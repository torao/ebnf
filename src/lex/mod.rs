//! `lex` is a low-level module for parsing Extended BNF syntax and constructing [`SyntaxRule`]s.
//!
//! This is useful if you are interested in the syntactic structure of EBNF, for example rustdoc.
//!
use std::{
  fmt::{Display, Write},
  fs::File,
  io::Read,
};

use self::tokenizer::{Token, Tokenizer};
use crate::io::Decoder;
use crate::{Error, Location, Result};

mod tokenizer;

#[cfg(test)]
mod test;

/// `parse_str()` is a simple way for parsing EBNF syntax and build [`SyntaxRule`]s from a specified
/// string. See [`Lexer`] for more low-level and efficient usage.
///
/// ```
/// use std::io::Cursor;
/// use ebnf::lex;
///
/// let name = "/path/to/your/file.ebnf";
/// let syntax = "abc = 'A', ('B' | 'C'); xyz = 'X', 'Y', 'Z';";
/// let rules = lex::parse_str(name, syntax).unwrap();
/// assert_eq!(2, rules.len());
/// assert_eq!("abc", rules[0].meta_identifier);
/// assert_eq!("xyz", rules[1].meta_identifier);
/// ```
///
pub fn parse_str(name: &str, syntax: &str) -> Result<Vec<SyntaxRule>> {
  let mut lexer = Lexer::new(name);
  let mut rules = Vec::new();
  rules.append(&mut lexer.push_str(syntax)?);
  if let Some(rule) = lexer.flush()? {
    rules.push(rule);
  }
  Ok(rules)
}

pub fn parse_file(file_name: &str, encoding: &str, max_buffer_size: usize) -> Result<Vec<SyntaxRule>> {
  let mut file = File::open(file_name).map_err(|err| Error::new(&Location::new(file_name), err.to_string()))?;
  parse(file_name, &mut file, encoding, max_buffer_size)
}

/// `parse()` function parses the Extended BNF syntax read from the specified stream and restores
/// the [`SyntaxRule`]s.
///
pub fn parse(name: &str, r: &mut dyn Read, encoding: &str, max_buffer_size: usize) -> Result<Vec<SyntaxRule>> {
  let mut decoder = Decoder::new(name, encoding, false)?;
  let mut lexer = Lexer::with_capacity(name, tokenizer::DEFAULT_INIT_BUFFER_SIZE, max_buffer_size);
  let mut rules = Vec::new();
  let mut buffer = [0u8; 4 * 1024];
  loop {
    let length = match r.read(&mut buffer) {
      Ok(len) if len == 0 => break, // EOF reached
      Ok(len) => len,
      Err(err) => {
        return Err(Error::new(
          &lexer.tokenizer.location,
          format!("Failed to load data: {}", err),
        ));
      }
    };
    let input = decoder.push(&buffer[0..length])?;
    rules.append(&mut lexer.push_str(&input)?);
  }

  // Push and convert the remaining bytes.
  let input = decoder.flush()?;
  rules.append(&mut lexer.push_str(&input)?);
  if let Some(rule) = lexer.flush()? {
    rules.push(rule);
  }

  Ok(rules)
}

///
/// To support streamimg or pipelined operations, syntax-rules can be parsed by `push()` or
/// `push_str()` fragments of the input characters. In this case, you need to call `flush()` to
/// indicate that the end of stream has been reached and to restore the [`SyntaxRule`] with the
/// remaining text in the internal buffer. Each function will return zero or more SyntaxRules.
///
/// ```
/// use ebnf::lex::{Lexer, SyntaxRule};
///
/// let mut rules = Vec::new();
/// let mut lexer = Lexer::new("/path/to/your/file.ebnf");
/// rules.append(&mut lexer.push_str("abc = 'A', ('B' | 'C'); xyz = 'X', 'Y', 'Z';").unwrap());
/// if let Some(rule) = lexer.flush().unwrap() {
///   rules.push(rule);
/// }
/// assert_eq!(2, rules.len());
/// assert_eq!("abc", rules[0].meta_identifier);
/// assert_eq!("xyz", rules[1].meta_identifier);
/// ```
pub struct Lexer {
  tokenizer: Tokenizer,
  tokens: Vec<Token>,
}

impl Lexer {
  /// Construct a new EBNF Lexer.
  ///
  /// # Parameters
  ///
  /// * `name` - The location of an EBNF definition to be parsed by this Lexer (for example, a
  ///   local file path or URL). This information is only used to report the location of the syntax
  ///   error when it occurs.
  ///
  pub fn new(name: &str) -> Lexer {
    Lexer {
      tokenizer: Tokenizer::new(name),
      tokens: Vec::new(),
    }
  }

  /// Construct a new EBNF Lexer with a specified buffer size limit.
  /// By setting an upper limit on the buffer size, it's able to prevent attacks that consume memory
  /// by entering like huge meta-identifier or comment.
  ///
  /// # Paramters
  ///
  /// * `name` - The location of an EBNF definition to be parsed by this Lexer (for example, a
  ///   local file path or URL). This information is only used to report the location of the syntax
  ///   error when it occurs.
  /// * `max_buffer_size` - Maximum number of characters that can be buffered. If zero is specified,
  ///   buffering is performed without limit.
  ///
  pub fn with_capacity(name: &str, init_buffer_size: usize, max_buffer_size: usize) -> Lexer {
    Lexer {
      tokenizer: Tokenizer::with_capacity(name, init_buffer_size, max_buffer_size),
      tokens: Vec::new(),
    }
  }

  pub fn push(&mut self, ch: char) -> Result<Option<SyntaxRule>> {
    let tokens = self.tokenizer.push(ch)?;
    let mut r = self.append(tokens)?;
    Ok(if r.is_empty() { None } else { Some(r.remove(0)) })
  }

  ///
  /// NOTE: The internal state when an error is returned is undefined; it's not possible to parse
  /// the correct syntax with `push()`, `push_str()`, or `flash()` continuation characters unless
  /// `reset()` is called.
  ///
  pub fn push_str(&mut self, s: &str) -> Result<Vec<SyntaxRule>> {
    let tokens = self.tokenizer.push_str(s)?;
    self.append(tokens)
  }

  pub fn flush(&mut self) -> Result<Option<SyntaxRule>> {
    let tokens = self.tokenizer.flush()?;
    let mut r = self.append(tokens)?;
    Ok(if r.is_empty() { None } else { Some(r.remove(0)) })
  }

  pub fn reset(&mut self) {
    self.tokenizer.reset();
    self.tokens.truncate(0);
  }

  fn append(&mut self, mut new_tokens: Vec<Token>) -> Result<Vec<SyntaxRule>> {
    let mut rules = Vec::new();
    while !new_tokens.is_empty() {
      let token = new_tokens.remove(0);
      let is_terminator = token.is_terminator();
      self.tokens.push(token);
      if is_terminator {
        if let Some(syntax_rule) = build_syntax_rule(&self.tokens)? {
          rules.push(syntax_rule);
        }
        self.tokens.truncate(0);
      }
    }
    Ok(rules)
  }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SyntaxRule {
  pub location: Location,
  pub meta_identifier: String,
  pub definition_list: DefinitionList,
}

impl Display for SyntaxRule {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    f.write_str(&self.meta_identifier)?;
    f.write_char('=')?;
    self.definition_list.fmt(f)?;
    f.write_char(';')
  }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DefinitionList(pub Vec<SingleDefinition>);

impl Display for DefinitionList {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    for i in 0..self.0.len() {
      if i != 0 {
        f.write_char('|')?;
      }
      self.0[i].fmt(f)?;
    }
    Ok(())
  }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SingleDefinition {
  pub syntactic_terms: Vec<SyntacticTerm>,
}

impl Display for SingleDefinition {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    for i in 0..self.syntactic_terms.len() {
      if i != 0 {
        f.write_char(',')?;
      }
      self.syntactic_terms[i].fmt(f)?;
    }
    Ok(())
  }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SyntacticTerm {
  pub syntactic_factor: SyntacticFactor,
  pub syntactic_exception: Option<SyntacticFactor>,
}

impl Display for SyntacticTerm {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    self.syntactic_factor.fmt(f)?;
    if let Some(exception) = &self.syntactic_exception {
      f.write_char('-')?;
      exception.fmt(f)?;
    }
    Ok(())
  }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SyntacticFactor {
  pub repetition: u32,
  pub syntactic_primary: SyntacticPrimary,
}

impl Display for SyntacticFactor {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    if self.repetition != 1 {
      write!(f, "{}*", self.repetition)?;
    }
    self.syntactic_primary.fmt(f)
  }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SyntacticPrimary {
  OptionalSequence(Location, DefinitionList),
  RepeatedSequence(Location, DefinitionList),
  GroupedSequence(Location, DefinitionList),
  MetaIdentifier(Location, String),
  TerminalString(Location, String),
  SpecialSequence(Location, String),
  EmptySequence(Location),
}

impl SyntacticPrimary {
  pub fn location<'a>(&'a self) -> &'a Location {
    match self {
      SyntacticPrimary::OptionalSequence(location, ..) => location,
      SyntacticPrimary::RepeatedSequence(location, ..) => location,
      SyntacticPrimary::GroupedSequence(location, ..) => location,
      SyntacticPrimary::MetaIdentifier(location, ..) => location,
      SyntacticPrimary::TerminalString(location, ..) => location,
      SyntacticPrimary::SpecialSequence(location, ..) => location,
      SyntacticPrimary::EmptySequence(location, ..) => location,
    }
  }
}

impl Display for SyntacticPrimary {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      SyntacticPrimary::OptionalSequence(_, definition_list) => {
        f.write_char('[')?;
        definition_list.fmt(f)?;
        f.write_char(']')
      }
      SyntacticPrimary::RepeatedSequence(_, definition_list) => {
        f.write_char('{')?;
        definition_list.fmt(f)?;
        f.write_char('}')
      }
      SyntacticPrimary::GroupedSequence(_, definition_list) => {
        f.write_char('(')?;
        definition_list.fmt(f)?;
        f.write_char(')')
      }
      SyntacticPrimary::MetaIdentifier(_, meta_identifier) => f.write_str(meta_identifier),
      SyntacticPrimary::TerminalString(_, terminal_string) => {
        let single_quote = !terminal_string.contains('\'');
        f.write_char(if single_quote { '\'' } else { '\"' })?;
        f.write_str(terminal_string)?;
        f.write_char(if single_quote { '\'' } else { '\"' })
      }
      SyntacticPrimary::SpecialSequence(_, special_sequence) => {
        f.write_char('?')?;
        f.write_str(&special_sequence)?;
        f.write_char('?')
      }
      SyntacticPrimary::EmptySequence(_) => Ok(()),
    }
  }
}

fn build_syntax_rule(tokens: &[Token]) -> Result<Option<SyntaxRule>> {
  // NOTE: The `tokens` parameter in all of the following functions is implicitly terminated with
  // terminator token (';', '.', or EOF).
  debug_assert!(
    !tokens.is_empty()
      && tokens.last().unwrap().is_terminator()
      && tokens.iter().filter(|tk| tk.is_terminator()).count() == 1
  );

  // Read meta-identifier until defining-symbol appears.
  let (meta_identifier, location, next) = read_meta_identifier(tokens, 0);
  let next = skip_comment_or_gap_separator(tokens, next);
  if location.is_none() {
    if tokens[next].is_terminator() {
      Ok(None)
    } else {
      Err(Error::new(
        tokens[next].location(),
        format!("meta-identifier expected, but {} appeared.", tokens[next].name()),
      ))
    }
  } else if !tokens[next].is_defining_symbol() {
    Err(Error::new(
      tokens[next].location(),
      format!(
        "meta-identifier or defining-symbol '=' expected, but {} appeared.",
        tokens[next].name()
      ),
    ))
  } else {
    assert!(!meta_identifier.is_empty());
    let location = location.unwrap();
    let definition_list = read_definition_list(tokens, next + 1)?;
    Ok(Some(SyntaxRule {
      location,
      meta_identifier,
      definition_list,
    }))
  }
}

fn read_definition_list(tokens: &[Token], position: usize) -> Result<DefinitionList> {
  let mut definition_list = Vec::with_capacity(8);
  let mut position = position;
  loop {
    let (single_definition, next) = read_single_definition(tokens, position)?;
    definition_list.push(single_definition);
    position = skip_comment_or_gap_separator(tokens, next);
    if position >= tokens.len() || tokens[position].is_terminator() {
      break;
    }
    if let Token::DefinitionSeparatorSymbol(..) = &tokens[position] {
      position = position + 1;
    }
  }
  Ok(DefinitionList(definition_list))
}

fn read_single_definition(tokens: &[Token], position: usize) -> Result<(SingleDefinition, usize)> {
  let mut syntactic_terms = Vec::with_capacity(8);
  let mut position = position;
  loop {
    let (syntactic_term, next) = read_syntactic_term(tokens, position)?;
    syntactic_terms.push(syntactic_term);
    position = skip_comment_or_gap_separator(tokens, next);
    if position >= tokens.len() {
      break;
    }
    match &tokens[position] {
      Token::ConcatenateSymbol(..) => position = position + 1,
      Token::DefinitionSeparatorSymbol(..) => break,
      token if token.is_terminator() => break,
      token =>
        return Err(Error::new(
          token.location(),
          format!("concatenate-symbol ',', definition-separator-symbol '|', or terminator-symbol ';' expected, but {} appeared.", token.name()),
        )),
    }
  }
  Ok((SingleDefinition { syntactic_terms }, position))
}

fn read_syntactic_term(tokens: &[Token], position: usize) -> Result<(SyntacticTerm, usize)> {
  let (syntactic_factor, next) = read_syntactic_factor(tokens, position)?;
  let next = skip_comment_or_gap_separator(tokens, next);
  let (syntactic_exception, position) = if next < tokens.len() && tokens[next].is_except_symbol() {
    let (syntactic_exception, next) = read_syntactic_factor(tokens, next + 1)?;
    (Some(syntactic_exception), next)
  } else {
    (None, next)
  };
  Ok((
    SyntacticTerm {
      syntactic_factor,
      syntactic_exception,
    },
    position,
  ))
}

fn read_syntactic_factor(tokens: &[Token], position: usize) -> Result<(SyntacticFactor, usize)> {
  let position = skip_comment_or_gap_separator(tokens, position);
  let (repetition, next) = if position >= tokens.len() {
    (1, position)
  } else if let Token::Integer(_, repetition) = &tokens[position] {
    let repetition = match repetition.parse::<u32>() {
      Ok(repetition) => repetition,
      Err(error) => {
        return Err(Error::new(
          tokens[position].location(),
          format!(
            "cannot convert the number of repetitions {:?} to 32-bit integer: {}",
            repetition, error
          ),
        ))
      }
    };
    let i = skip_comment_or_gap_separator(tokens, position + 1);
    if !tokens[i].is_repetition_symbol() {
      return Err(Error::new(
        tokens[i].location(),
        format!("repetition-symbol '*' expected, but {} appeared.", tokens[i].name()),
      ));
    }
    (repetition, skip_comment_or_gap_separator(tokens, i + 1))
  } else {
    (1, position)
  };
  let (syntactic_primary, next) = read_syntactic_primary(tokens, next)?;
  Ok((
    SyntacticFactor {
      repetition,
      syntactic_primary,
    },
    next,
  ))
}

fn read_syntactic_primary(tokens: &[Token], position: usize) -> Result<(SyntacticPrimary, usize)> {
  let i = skip_comment_or_gap_separator(tokens, position);
  if i >= tokens.len() {
    let location = if let Some(last) = tokens.last() {
      last.location().clone()
    } else {
      Location::new("<unknown>")
    };
    return Ok((SyntacticPrimary::EmptySequence(location), i));
  }
  match &tokens[i] {
    Token::StartOptionSymbol(location, start_option_symbol) => {
      if *start_option_symbol == "(/" && i + 1 < tokens.len() && tokens[i + 1].is_end_group_symbol() {
        // Invalid character sequence: (/)
        return Err(Error::new(
          location,
          String::from("An ambiguous start/end-option-symbol: (/)"),
        ));
      }
      let (definition_list, next) = read_enclosed_definition_list(
        tokens,
        i,
        |tk| tk.is_start_option_symbol(),
        |tk| tk.is_end_option_symbol(),
      )?;
      Ok((
        SyntacticPrimary::OptionalSequence(location.clone(), definition_list),
        next,
      ))
    }
    Token::StartRepeatSymbol(location, start_repeat_symbol) => {
      if *start_repeat_symbol == "(:" && i + 1 < tokens.len() && tokens[i + 1].is_end_group_symbol() {
        // Invalid character sequence: (:)
        return Err(Error::new(
          location,
          String::from("An ambiguous start/end-repeat-symbol: (:)"),
        ));
      }
      let (definition_list, next) = read_enclosed_definition_list(
        tokens,
        i,
        |tk| tk.is_start_repeat_symbol(),
        |tk| tk.is_end_repeat_symbol(),
      )?;
      Ok((
        SyntacticPrimary::RepeatedSequence(location.clone(), definition_list),
        next,
      ))
    }
    Token::StartGroupSymbol(location) => {
      let (definition_list, next) = read_enclosed_definition_list(
        tokens,
        i,
        |tk| tk.is_start_group_symbol(),
        |tk| tk.is_end_group_symbol(),
      )?;
      Ok((
        SyntacticPrimary::GroupedSequence(location.clone(), definition_list),
        next,
      ))
    }
    Token::MetaIdentifier(location, _) => {
      let (meta_identifier, _, next) = read_meta_identifier(tokens, i);
      Ok((
        SyntacticPrimary::MetaIdentifier(location.clone(), meta_identifier),
        next,
      ))
    }
    Token::TerminalString(location, content, _) => Ok((
      SyntacticPrimary::TerminalString(location.clone(), content.clone()),
      i + 1,
    )),
    Token::SpecialSequence(location, content) => Ok((
      SyntacticPrimary::SpecialSequence(location.clone(), content.clone()),
      i + 1,
    )),
    token => Ok((SyntacticPrimary::EmptySequence(token.location().clone()), i)),
  }
}

/// Restores the definition-list closed by parentheses. This function recursively constructs
/// nexted parentheses.
///
fn read_enclosed_definition_list(
  tokens: &[Token],
  position: usize,
  is_open: fn(&Token) -> bool,
  is_close: fn(&Token) -> bool,
) -> Result<(DefinitionList, usize)> {
  debug_assert!(is_open(&tokens[position]));
  let mut depth = 0;
  for i in position + 1..tokens.len() {
    if is_open(&tokens[i]) {
      depth += 1;
    } else if is_close(&tokens[i]) {
      if depth == 0 {
        let subtokens = &tokens[position + 1..i];
        let definition_list = read_definition_list(subtokens, 0)?;
        return Ok((definition_list, i + 1));
      } else {
        depth -= 1;
      }
    }
  }
  Err(Error::new(
    tokens[position].location(),
    format!(
      "{} '{}' is not closed.",
      tokens[position].name(),
      tokens[position].debug()
    ),
  ))
}

/// Read from specified position until it founds a token that isn't a meta-identifier or gap
/// separator, or an EOF, and return a string of meta-identifier. All gap-separator-sequences are
/// replaced by a single space character.
///
/// # Returns
/// 1. meta-identifier string. Zero length if no valid meta-identifier could be detected.
/// 2. The location of the first token that makes up the meta-identifier.
/// 3. the position of next token to read. Greater than or equal to `tokens.len()` if EOF is reached.
///
fn read_meta_identifier(tokens: &[Token], position: usize) -> (String, Option<Location>, usize) {
  let mut meta_identifier = String::with_capacity(16);
  let start = skip_comment_or_gap_separator(tokens, position);
  let mut location: Option<Location> = None;
  let mut i = start;
  while i < tokens.len() {
    match &tokens[i] {
      Token::MetaIdentifier(_, identifier) => {
        meta_identifier.push_str(identifier);
        if location.is_none() {
          location = Some(tokens[i].location().clone());
        }
      }
      Token::GapSeparatorSequence(..) => {
        if !meta_identifier.ends_with(' ') {
          meta_identifier.push(' ')
        }
      }
      _ => break,
    }
    i += 1;
  }
  (meta_identifier.trim().to_string(), location, i)
}

fn skip_comment_or_gap_separator(tokens: &[Token], position: usize) -> usize {
  let mut i = position;
  while i < tokens.len() && (tokens[i].is_gap_separator_sequence() || tokens[i].is_comment()) {
    i += 1;
  }
  i
}

impl Token {
  pub fn location(&self) -> &Location {
    self.info().0
  }
  pub fn name(&self) -> &str {
    self.info().1
  }
  pub fn debug(&self) -> String {
    self.info().2
  }
  fn info(&self) -> (&Location, &str, String) {
    match self {
      Token::RepetitionSymbol(loc) => (loc, "repetition-symbol", "*".to_string()),
      Token::ExceptSymbol(loc) => (loc, "except-symbol", "-".to_string()),
      Token::ConcatenateSymbol(loc) => (loc, "concatenate-symbol", ",".to_string()),
      Token::DefinitionSeparatorSymbol(loc, sym) => (loc, "definition-separator-symbol", format!("{:?}", sym)),
      Token::DefiningSymbol(loc) => (loc, "defining-symbol", "=".to_string()),
      Token::TerminatorSymbol(loc, sym) => (loc, "terminator-symbol", format!("{}", sym)),
      Token::StartOptionSymbol(loc, sym) => (loc, "start-option-symbol", format!("{}", sym)),
      Token::EndOptionSymbol(loc, sym) => (loc, "end-option-symbol", format!("{}", sym)),
      Token::StartRepeatSymbol(loc, sym) => (loc, "start-repeat-symbol", format!("{}", sym)),
      Token::EndRepeatSymbol(loc, sym) => (loc, "end-repeat-symbol", format!("{}", sym)),
      Token::StartGroupSymbol(loc) => (loc, "start-group-symbol", "(".to_string()),
      Token::EndGroupSymbol(loc) => (loc, "end-group-symbol", ")".to_string()),
      Token::MetaIdentifier(loc, value) => (loc, "meta-identifier", value.to_string()),
      Token::TerminalString(loc, value, _) => (loc, "terminal-string", value.to_string()),
      Token::Integer(loc, value) => (loc, "integer", value.to_string()),
      Token::Comment(loc, content) => (loc, "comment", format!("(*{}*)", content.to_string())),
      Token::SpecialSequence(loc, content) => (loc, "special-sequence", content.to_string()),
      Token::GapSeparatorSequence(loc, gap) => (loc, "gap-separator-sequence", format!("{:?}", gap)),
      Token::EOF(loc) => (loc, "EOF", String::from("")),
    }
  }
  pub fn is_defining_symbol(&self) -> bool {
    match self {
      Token::DefiningSymbol(..) => true,
      _ => false,
    }
  }
  pub fn is_repetition_symbol(&self) -> bool {
    if let Token::RepetitionSymbol(..) = self {
      true
    } else {
      false
    }
  }
  pub fn is_except_symbol(&self) -> bool {
    if let Token::ExceptSymbol(..) = self {
      true
    } else {
      false
    }
  }
  pub fn is_start_option_symbol(&self) -> bool {
    if let Token::StartOptionSymbol(..) = self {
      true
    } else {
      false
    }
  }
  pub fn is_end_option_symbol(&self) -> bool {
    if let Token::EndOptionSymbol(..) = self {
      true
    } else {
      false
    }
  }
  pub fn is_start_repeat_symbol(&self) -> bool {
    if let Token::StartRepeatSymbol(..) = self {
      true
    } else {
      false
    }
  }
  pub fn is_end_repeat_symbol(&self) -> bool {
    if let Token::EndRepeatSymbol(..) = self {
      true
    } else {
      false
    }
  }
  pub fn is_start_group_symbol(&self) -> bool {
    if let Token::StartGroupSymbol(..) = self {
      true
    } else {
      false
    }
  }
  pub fn is_end_group_symbol(&self) -> bool {
    if let Token::EndGroupSymbol(..) = self {
      true
    } else {
      false
    }
  }
  pub fn is_gap_separator_sequence(&self) -> bool {
    match self {
      Token::GapSeparatorSequence(..) => true,
      _ => false,
    }
  }
  pub fn is_terminator(&self) -> bool {
    if let Token::TerminatorSymbol(..) | Token::EOF(..) = self {
      true
    } else {
      false
    }
  }
  pub fn is_comment(&self) -> bool {
    match self {
      Token::Comment(..) => true,
      _ => false,
    }
  }
}

#[inline]
pub fn is_gap_separator_char(ch: char) -> bool {
  ch == ' ' // space
    || ch == '\t' // horizontal-tabulation
    || ch == '\r' // new-line (carriage  return)
    || ch == '\n' // new-line (line feed)
    || ch == 0x0B as char // vertical-tabulation
    || ch == 0x0C as char // form-feed
}
