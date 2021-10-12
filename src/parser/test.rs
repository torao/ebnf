use std::io::Cursor;

use crate::{io::SyntaxReader, lex::parse_str, Location, Result, Syntax};

use super::{Parser, ParserContext, SpecialSequenceHandler};

#[test]
fn parser_context_build() {
  let rules = parse_str("", "a = 'A'; b = 'B'; c = 'C'; ab = a, b;").unwrap();
  let syntax = Syntax::new(rules).unwrap();
  let context = ParserContext::build_from(&syntax, &NOOP {}).unwrap();
  let parser = context.parser_for("ab").unwrap();

  let cursor = Box::new(Cursor::new(b"AB"));
  let mut r = SyntaxReader::with_encoding("", cursor, "utf-8").unwrap();

  println!("{:?}", parser);
  println!("{:?}", parser.parse(&context, &mut r).unwrap());
}

struct NOOP {}

impl SpecialSequenceHandler for NOOP {
  fn build(&self, _location: &Location, _special_sequence: &str) -> Result<Box<dyn Parser>> {
    unreachable!()
  }
}
