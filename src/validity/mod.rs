use std::collections::HashMap;

use crate::{
  keyed_meta_identifier,
  lex::{self, DefinitionList, SyntacticPrimary, SyntaxRule},
  normalized_meta_identifier, Error, Result, Syntax,
};

pub fn new_syntax(syntax_rules: Vec<SyntaxRule>) -> Result<Syntax> {
  let mut canonical_names = HashMap::with_capacity(syntax_rules.len());
  let mut rules: HashMap<String, usize> = HashMap::with_capacity(syntax_rules.len());
  for (i, syntax_rule) in syntax_rules.iter().enumerate() {
    let id = keyed_meta_identifier(&syntax_rule.meta_identifier);
    let canonical_name = normalized_meta_identifier(&syntax_rule.meta_identifier);
    assert_eq!(canonical_name, syntax_rule.meta_identifier);
    if let Some(_) = canonical_names.insert(id.clone(), canonical_name.clone()) {
      let duplicate = &syntax_rules[*rules.get(&id).unwrap()];
      return Err(Error::new(
        &syntax_rule.location,
        format!(
          "The meta-identifier {} is defined in ({},{}).",
          syntax_rule.meta_identifier, duplicate.location.lines, duplicate.location.columns
        ),
      ));
    }
    rules.insert(id, i);
  }
  make_sure_all_meta_identifiers_are_defined(&syntax_rules, &rules)?;
  Ok(Syntax {
    canonical_names,
    rules,
    syntax_rules,
  })
}

// すべての definition-list と single-definition の要素が 1 つ以上あること。

pub fn make_sure_all_meta_identifiers_are_defined<T>(
  syntax_rules: &Vec<lex::SyntaxRule>,
  rules: &HashMap<String, T>,
) -> Result<()> {
  fn is_def(syntactic_primary: &SyntacticPrimary, rules: impl Fn(&str) -> bool) -> Result<()> {
    if let SyntacticPrimary::MetaIdentifier(location, meta_identifier) = syntactic_primary {
      let id = keyed_meta_identifier(meta_identifier);
      if rules(&id) {
        Ok(())
      } else {
        Err(Error::new(
          location,
          format!("meta-identifier {:?} is not defined.", meta_identifier),
        ))
      }
    } else {
      Ok(())
    }
  }
  fn is_defined(definition_list: &DefinitionList, rules: impl Fn(&str) -> bool) -> Result<()> {
    for single_definition in &definition_list.0 {
      for syntactic_term in &single_definition.syntactic_terms {
        is_def(&syntactic_term.syntactic_factor.syntactic_primary, &rules)?;
        if let Some(exception) = &syntactic_term.syntactic_exception {
          is_def(&exception.syntactic_primary, &rules)?;
        }
      }
    }
    Ok(())
  }
  for rule in syntax_rules {
    is_defined(&rule.definition_list, |id| rules.contains_key(id))?;
  }
  Ok(())
}
