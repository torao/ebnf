#[cfg(test)]
mod test;

use std::collections::HashMap;

use crate::{
  io::SyntaxReader,
  lex::{DefinitionList, SingleDefinition, SyntacticFactor, SyntacticPrimary, SyntacticTerm},
  Error, Location, Node, Result, Syntax,
};

pub struct ParserContext {
  rules: HashMap<String, DefinitionListParser>,
}

impl ParserContext {
  pub fn parser_for(&self, meta_identifier: &str) -> Option<&DefinitionListParser> {
    let id = Self::canonicalize(meta_identifier);
    self.rules.get(&id)
  }

  pub fn build_from(syntax: &Syntax, factory: &dyn SpecialSequenceHandler) -> Result<Self> {
    let mut rules = HashMap::new();
    for rule in &syntax.syntax_rules {
      let id = Self::canonicalize(&rule.meta_identifier);
      let parser = DefinitionListParser::new(&rule.definition_list, factory)?;
      if let Some(_) = rules.insert(id, parser) {
        panic!("Syntax contains a rule with a duplicate name: {}", rule.meta_identifier);
      }
    }
    Ok(ParserContext { rules })
  }

  fn canonicalize(meta_identifier: &str) -> String {
    meta_identifier.chars().filter(|ch| !ch.is_whitespace()).collect::<String>()
  }
}

pub trait SpecialSequenceHandler {
  fn build(&self, location: &Location, special_sequence: &str) -> Result<Box<dyn Parser>>;
}

pub trait Parser: std::fmt::Debug {
  fn symbol(&self, context: &ParserContext) -> String;
  fn accept(&self, context: &ParserContext, r: &mut SyntaxReader) -> Result<Acceptability>;
  fn parse(&self, context: &ParserContext, r: &mut SyntaxReader) -> Result<Option<Node>>;
}

#[derive(Debug, PartialEq, Eq)]
pub enum Acceptability {
  /// NOTE: The return value of [`SyntaxReader::reset_to_mark()`] cannot be used to determine the
  /// depth of the match, since mark/reset may not return the correct depth if it is multilayered.
  ///
  Accept(usize),
  Reject,
}

#[derive(Debug)]
pub struct DefinitionListParser(Vec<SingleDefinitionParser>);

impl DefinitionListParser {
  pub fn new(
    definition_list: &DefinitionList,
    factory: &dyn SpecialSequenceHandler,
  ) -> Result<Self> {
    let mut single_definitions = Vec::new();
    for i in 0..definition_list.0.len() {
      let single_definition = &definition_list.0[i];
      single_definitions.push(SingleDefinitionParser::new(&single_definition, factory)?);
    }
    assert!(
      !single_definitions.is_empty(),
      "The definition_list does not contain any definitions."
    );
    Ok(DefinitionListParser(single_definitions))
  }

  fn accept_index(
    &self,
    context: &ParserContext,
    r: &mut SyntaxReader,
  ) -> Result<(usize, Acceptability)> {
    let mut max_depth = 0;
    let mut max_depth_indices = Vec::new();
    for i in 0..self.0.len() {
      let mark = r.mark()?;
      let acceptability = self.0[i].accept(context, r)?;
      r.reset_to_mark(mark)?;
      if let Acceptability::Accept(depth) = acceptability {
        if (max_depth == 0 && max_depth_indices.is_empty()) || max_depth == depth {
          max_depth = depth;
          max_depth_indices.push(i);
        } else if max_depth < depth {
          max_depth = depth;
          max_depth_indices.truncate(0);
          max_depth_indices.push(i);
        }
      }
    }

    match max_depth_indices.len() {
      0 => Ok((0, Acceptability::Reject)),
      1 => Ok((max_depth_indices[0], Acceptability::Accept(max_depth))),
      _ => {
        let conflicts = max_depth_indices
          .iter()
          .map(|i| self.0[*i].symbol(context))
          .collect::<Vec<String>>()
          .join(" <=> ");
        Err(Error::new(
          r.location(),
          format!("It's a contradictory pattern that matches multiple definitions: {}", conflicts),
        ))
      }
    }
  }
}

impl Parser for DefinitionListParser {
  fn symbol(&self, context: &ParserContext) -> String {
    self.0.iter().map(|term| term.symbol(context)).collect::<Vec<String>>().join(" | ")
  }
  fn accept(&self, context: &ParserContext, r: &mut SyntaxReader) -> Result<Acceptability> {
    let (_, acceptability) = self.accept_index(context, r)?;
    Ok(acceptability)
  }
  fn parse(&self, context: &ParserContext, r: &mut SyntaxReader) -> Result<Option<Node>> {
    let (index, _) = self.accept_index(context, r)?;
    self.0[index].parse(context, r)
  }
}

#[derive(Debug)]
pub struct SingleDefinitionParser {
  syntactic_terms: Vec<SyntacticTermParser>,
}

impl SingleDefinitionParser {
  pub fn new(
    single_definition: &SingleDefinition,
    factory: &dyn SpecialSequenceHandler,
  ) -> Result<SingleDefinitionParser> {
    let mut syntactic_terms = Vec::new();
    for syntactic_term in &single_definition.syntactic_terms {
      syntactic_terms.push(SyntacticTermParser::new(&syntactic_term, factory)?);
    }
    Ok(SingleDefinitionParser { syntactic_terms })
  }
}

impl Parser for SingleDefinitionParser {
  fn symbol(&self, context: &ParserContext) -> String {
    self.syntactic_terms.iter().map(|term| term.symbol(context)).collect::<Vec<String>>().join(", ")
  }
  fn accept(&self, context: &ParserContext, r: &mut SyntaxReader) -> Result<Acceptability> {
    let mut total_depth = 0;
    for syntactic_term in &self.syntactic_terms {
      if let Acceptability::Accept(depth) = syntactic_term.accept(context, r)? {
        total_depth += depth;
      } else {
        return Ok(Acceptability::Reject);
      }
    }
    Ok(Acceptability::Accept(total_depth))
  }
  fn parse(&self, context: &ParserContext, r: &mut SyntaxReader) -> Result<Option<Node>> {
    let location = r.location().clone();
    let mut children = Vec::new();
    for syntactic_term in &self.syntactic_terms {
      merge_or_push(&mut children, syntactic_term.parse(context, r)?);
    }
    Ok(Some(Node::with_children(location, children)))
  }
}

#[derive(Debug)]
pub struct SyntacticTermParser {
  syntactic_factor: SyntacticFactorParser,
  syntactic_exception: Option<SyntacticFactorParser>,
}

impl SyntacticTermParser {
  pub fn new(syntactic_term: &SyntacticTerm, factory: &dyn SpecialSequenceHandler) -> Result<Self> {
    let syntactic_factor = SyntacticFactorParser::new(&syntactic_term.syntactic_factor, factory)?;
    let syntactic_exception = if let Some(ex) = &syntactic_term.syntactic_exception {
      Some(SyntacticFactorParser::new(ex, factory)?)
    } else {
      None
    };
    Ok(SyntacticTermParser { syntactic_factor, syntactic_exception })
  }
}

impl Parser for SyntacticTermParser {
  fn symbol(&self, context: &ParserContext) -> String {
    if let Some(ex) = &self.syntactic_exception {
      format!("{} - {}", self.syntactic_factor.symbol(context), ex.symbol(context))
    } else {
      self.syntactic_factor.symbol(context)
    }
  }
  fn accept(&self, context: &ParserContext, r: &mut SyntaxReader) -> Result<Acceptability> {
    if let Some(ex) = &self.syntactic_exception {
      if let Acceptability::Accept(..) = ex.accept(context, r)? {
        return Ok(Acceptability::Reject);
      }
    }
    self.syntactic_factor.accept(context, r)
  }
  fn parse(&self, context: &ParserContext, r: &mut SyntaxReader) -> Result<Option<Node>> {
    self.syntactic_factor.parse(context, r)
  }
}

#[derive(Debug)]
pub struct SyntacticFactorParser {
  repetition: u32,
  syntactic_primary: Box<dyn Parser>,
}

impl SyntacticFactorParser {
  pub fn new(
    syntactic_factor: &SyntacticFactor,
    factory: &dyn SpecialSequenceHandler,
  ) -> Result<Self> {
    let repetition = syntactic_factor.repetition;
    let syntactic_primary: Box<dyn Parser> = match &syntactic_factor.syntactic_primary {
      SyntacticPrimary::OptionalSequence(_, definition_list) => {
        let definition_list = DefinitionListParser::new(&definition_list, factory)?;
        Box::new(OptionalSequenceParser { definition_list })
      }
      SyntacticPrimary::RepeatedSequence(_, definition_list) => {
        let definition_list = DefinitionListParser::new(&definition_list, factory)?;
        Box::new(RepeatedSequenceParser { definition_list })
      }
      SyntacticPrimary::GroupedSequence(_, definition_list) => {
        let definition_list = DefinitionListParser::new(&definition_list, factory)?;
        Box::new(GroupSequenceParser { definition_list })
      }
      SyntacticPrimary::MetaIdentifier(_, meta_identifier) => {
        Box::new(MetaIdentifierParser { meta_identifier: meta_identifier.to_string() })
      }
      SyntacticPrimary::TerminalString(_, terminal_string) => {
        let terminal_string = terminal_string.chars().collect::<Vec<char>>();
        Box::new(TerminalStringParser { terminal_string })
      }
      SyntacticPrimary::SpecialSequence(location, special_sequence) => {
        let special_sequence = special_sequence.to_string();
        let parser = factory.build(&location, &special_sequence)?;
        Box::new(SpecialSequenceParser { special_sequence, parser })
      }
      SyntacticPrimary::EmptySequence(_) => Box::new(EmptySequenceParser {}),
    };
    Ok(SyntacticFactorParser { repetition, syntactic_primary })
  }
}

impl Parser for SyntacticFactorParser {
  fn symbol(&self, context: &ParserContext) -> String {
    if self.repetition == 1 {
      self.syntactic_primary.symbol(context)
    } else {
      format!("{} * {}", self.repetition, self.syntactic_primary.symbol(context))
    }
  }
  fn accept(&self, context: &ParserContext, r: &mut SyntaxReader) -> Result<Acceptability> {
    let mut total_depth = 0;
    for _ in 0..self.repetition {
      if let Acceptability::Accept(depth) = self.syntactic_primary.accept(context, r)? {
        total_depth += depth;
      } else {
        return Ok(Acceptability::Reject);
      }
    }
    Ok(Acceptability::Accept(total_depth))
  }
  fn parse(&self, context: &ParserContext, r: &mut SyntaxReader) -> Result<Option<Node>> {
    let location = r.location().clone();
    let mut children = Vec::new();
    for _ in 0..self.repetition {
      merge_or_push(&mut children, self.syntactic_primary.parse(context, r)?);
    }
    Ok(Some(Node::with_children(location, children)))
  }
}

#[derive(Debug)]
pub struct OptionalSequenceParser {
  definition_list: DefinitionListParser,
}

impl Parser for OptionalSequenceParser {
  fn symbol(&self, context: &ParserContext) -> String {
    format!("[{}]", self.definition_list.symbol(context))
  }
  fn accept(&self, context: &ParserContext, r: &mut SyntaxReader) -> Result<Acceptability> {
    let acceptability = self.definition_list.accept(context, r)?;
    Ok(if acceptability == Acceptability::Reject {
      Acceptability::Accept(0)
    } else {
      acceptability
    })
  }
  fn parse(&self, context: &ParserContext, r: &mut SyntaxReader) -> Result<Option<Node>> {
    match self.accept(context, r)? {
      Acceptability::Accept(depth) if depth != 0 => self.definition_list.parse(context, r),
      _ => Ok(None),
    }
  }
}

#[derive(Debug)]
pub struct RepeatedSequenceParser {
  definition_list: DefinitionListParser,
}

impl Parser for RepeatedSequenceParser {
  fn symbol(&self, context: &ParserContext) -> String {
    format!("{{{}}}", self.definition_list.symbol(context))
  }
  fn accept(&self, context: &ParserContext, r: &mut SyntaxReader) -> Result<Acceptability> {
    let mut total_depth = 0;
    loop {
      match self.definition_list.accept(context, r)? {
        Acceptability::Accept(depth) if depth == 0 => break,
        Acceptability::Accept(depth) => total_depth += depth,
        Acceptability::Reject => break,
      }
    }
    Ok(Acceptability::Accept(total_depth))
  }
  fn parse(&self, context: &ParserContext, r: &mut SyntaxReader) -> Result<Option<Node>> {
    let location = r.location().clone();
    let mut children = Vec::new();
    loop {
      let mark = r.mark()?;
      let accept = self.accept(context, r)?;
      r.reset_to_mark(mark)?;
      match accept {
        Acceptability::Accept(depth) if depth != 0 => {
          if !merge_or_push(&mut children, self.definition_list.parse(context, r)?) {
            break;
          }
        }
        _ => break,
      }
    }
    if children.is_empty() {
      Ok(None)
    } else {
      Ok(Some(Node::with_children(location, children)))
    }
  }
}

#[derive(Debug)]
pub struct GroupSequenceParser {
  definition_list: DefinitionListParser,
}

impl Parser for GroupSequenceParser {
  fn symbol(&self, context: &ParserContext) -> String {
    format!("({})", self.definition_list.symbol(context))
  }
  fn accept(&self, context: &ParserContext, r: &mut SyntaxReader) -> Result<Acceptability> {
    self.definition_list.accept(context, r)
  }
  fn parse(&self, context: &ParserContext, r: &mut SyntaxReader) -> Result<Option<Node>> {
    self.definition_list.parse(context, r)
  }
}

#[derive(Debug)]
pub struct MetaIdentifierParser {
  meta_identifier: String,
}

impl Parser for MetaIdentifierParser {
  fn symbol(&self, _context: &ParserContext) -> String {
    self.meta_identifier.to_string()
  }
  fn accept(&self, context: &ParserContext, r: &mut SyntaxReader) -> Result<Acceptability> {
    match context.parser_for(&self.meta_identifier) {
      Some(parser) => parser.accept(context, r),
      None => panic!(
        "The meta identifier {:?} contained in the rule is not defined in Syntax.",
        self.meta_identifier
      ),
    }
  }
  fn parse(&self, context: &ParserContext, r: &mut SyntaxReader) -> Result<Option<Node>> {
    let location = r.location().clone();
    if let Some(parser) = context.parser_for(&self.meta_identifier) {
      match parser.parse(context, r)? {
        Some(Node { location: _, name: _, token, children }) => {
          let name = ParserContext::canonicalize(&self.meta_identifier);
          Ok(Some(Node { location, name: Some(name), token, children }))
        }
        None => Ok(None),
      }
    } else {
      panic!(
        "The meta identifier {:?} contained in the rule is not defined in Syntax.",
        self.meta_identifier
      )
    }
  }
}

#[derive(Debug)]
pub struct TerminalStringParser {
  terminal_string: Vec<char>,
}

impl Parser for TerminalStringParser {
  fn symbol(&self, _context: &ParserContext) -> String {
    format!("\"{}\"", self.terminal_string.iter().collect::<String>())
  }
  fn accept(&self, _context: &ParserContext, r: &mut SyntaxReader) -> Result<Acceptability> {
    Ok(if r.prefix_matches(&self.terminal_string)? {
      Acceptability::Accept(self.terminal_string.len())
    } else {
      Acceptability::Reject
    })
  }
  fn parse(&self, _context: &ParserContext, r: &mut SyntaxReader) -> Result<Option<Node>> {
    let location = r.location().clone();
    if !r.prefix_matches(&self.terminal_string)? {
      panic!(
        "Parsing was performed on the unacceptable characters: {:?} != {:?}: on {:?}",
        r.peek(self.terminal_string.len())?,
        self.terminal_string.iter().collect::<String>(),
        self
      );
    }
    r.skip(self.terminal_string.len())?;
    let terminal_string = self.terminal_string.iter().collect::<String>();
    Ok(Some(Node::with_token(location, &terminal_string)))
  }
}

#[derive(Debug)]
pub struct SpecialSequenceParser {
  special_sequence: String,
  parser: Box<dyn Parser>,
}

impl<'a> Parser for SpecialSequenceParser {
  fn symbol(&self, _context: &ParserContext) -> String {
    format!("?{}?", self.special_sequence)
  }
  fn accept(&self, context: &ParserContext, r: &mut SyntaxReader) -> Result<Acceptability> {
    self.parser.accept(context, r)
  }
  fn parse(&self, context: &ParserContext, r: &mut SyntaxReader) -> Result<Option<Node>> {
    self.parser.parse(context, r)
  }
}

#[derive(Debug)]
pub struct EmptySequenceParser {}

impl Parser for EmptySequenceParser {
  fn symbol(&self, _context: &ParserContext) -> String {
    String::from("∅")
  }
  fn accept(&self, _context: &ParserContext, _r: &mut SyntaxReader) -> Result<Acceptability> {
    Ok(Acceptability::Accept(0))
  }
  fn parse(&self, _context: &ParserContext, _r: &mut SyntaxReader) -> Result<Option<Node>> {
    Ok(None)
  }
}

fn merge_or_push(children: &mut Vec<Node>, new_node: Option<Node>) -> bool {
  if let Some(new_node) = new_node {
    if let Some(last_node) = children.last_mut() {
      if last_node.name.is_none()
        && new_node.name.is_none()
        && last_node.children.is_empty()
        && new_node.children.is_empty()
      {
        last_node.token.push_str(&new_node.token);
        return true;
      }
    }
    children.push(new_node);
    return true;
  }
  false
}
