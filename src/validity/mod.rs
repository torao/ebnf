use crate::{Error, Result, Syntax};

/// Verify the syntactic structure and definition for [`Syntax`] at the time of construction.
///
pub fn verify_construct(syntax: &Syntax) -> Result<()> {
  verify_duplicate_definition(syntax)?;

  // TODO: Verify that all meta-identifiers in the definition-list are defined.

  Ok(())
}

/// Verify that there are no duplicate meta-dentifier definitions.
///
fn verify_duplicate_definition(syntax: &Syntax) -> Result<()> {
  for i in 0..syntax.syntax_rules.len() {
    for j in i + 1..syntax.syntax_rules.len() {
      if Syntax::same_meta_identifier(
        &syntax.syntax_rules[i].meta_identifier,
        &syntax.syntax_rules[j].meta_identifier,
      ) {
        return Err(Error::new(
          &syntax.syntax_rules[j].location,
          format!(
            "The meta-identifier {} is defined in ({},{}).",
            syntax.syntax_rules[j].meta_identifier,
            syntax.syntax_rules[i].location.lines,
            syntax.syntax_rules[i].location.columns
          ),
        ));
      }
    }
  }
  Ok(())
}
