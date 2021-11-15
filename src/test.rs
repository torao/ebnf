use std::{fmt::Debug, io::Cursor};

use crate::{
  parser::{
    graph::{GraphConfig, LexGraph},
    CharsScanner, Parser, SpecialSequenceParser, SpecialSequenceScanner,
  },
  Location, Result, Syntax,
};

pub const TEST_EBNF_NAME: &str = "definition.ebnf";
pub const TEST_TARGET_NAME: &str = "target.txt";

pub fn dl(lines: u64, columns: u64) -> Location {
  Location::with_location(TEST_EBNF_NAME, lines, columns)
}

pub fn sl(lines: u64, columns: u64) -> Location {
  Location::with_location(TEST_TARGET_NAME, lines, columns)
}

pub fn split_by(text: &str, chars: usize) -> Vec<String> {
  text
    .chars()
    .collect::<Vec<_>>()
    .chunks(chars)
    .map(|c| c.iter().collect::<String>())
    .collect::<Vec<_>>()
}

pub fn assert_err_match<T: Debug>(location: &Location, msg_pattern: impl Into<String>, actual: Result<T>) {
  let msg_pattern = msg_pattern.into();
  if let Err(error) = actual {
    assert_eq!(*location, error.location);
    let re = regex::Regex::new(&msg_pattern).unwrap();
    if !re.is_match(&error.message) {
      assert_eq!(&msg_pattern, &error.message);
    }
  } else {
    panic!("Error expected, but success: {:?}", actual);
  }
}

#[test]
fn test() {
  let source_name = "sample.ebnf";
  let syntax = r#"(* a simple program syntax in EBNF - Wikipedia *)
program = 'PROGRAM', white space, identifier, white space,
  'BEGIN', white space,
  { assignment, ";", white space },
  'END.' ;
identifier = alphabetic character, { alphabetic character | digit } ;
number = [ "-" ], digit, { digit } ;
string = '"' , { all characters - '"' }, '"' ;
assignment = identifier , ":=" , ( number | identifier | string ) ;
alphabetic character = "A" | "B" | "C" | "D" | "E" | "F" | "G"
            | "H" | "I" | "J" | "K" | "L" | "M" | "N"
            | "O" | "P" | "Q" | "R" | "S" | "T" | "U"
            | "V" | "W" | "X" | "Y" | "Z" ;
digit = "0" | "1" | "2" | "3" | "4" | "5" | "6" | "7" | "8" | "9" ;
white space = ? white space characters ? ;
all characters = ? all visible characters ? ;"#;
  let mut cursor = Cursor::new(syntax.as_bytes());
  let syntax = Syntax::read_from_utf8(source_name, &mut cursor, 1024).unwrap();
  let mut config = GraphConfig::new();
  config.special_sequence_parser(SpecialSequenceParser::new(Box::new(|_, label| {
    special_sequence_scanner(label)
  })));
  let graph = LexGraph::compile(&syntax, &config);
  let mut parser = Parser::new(&graph, "program", 1024, source_name).unwrap();

  let mut events = Vec::new();
  events.append(
    &mut parser
      .push_str(
        r#"PROGRAM DEMO1
BEGIN
  A:=3;
  B:=45;
  H:=-100023;
  C:=A;
  D123:=B34A;
  BABOON:=GIRAFFE;
  TEXT:="Hello world!";
END."#,
      )
      .unwrap(),
  );
  events.append(&mut parser.flush().unwrap());

  fn special_sequence_scanner(label: &str) -> Box<dyn SpecialSequenceScanner> {
    Box::new(match label.trim() {
      "white space characters" => {
        CharsScanner::with_one_or_more(Box::new(|c| c.is_whitespace() || c.is_ascii_control()))
      }
      "all visible characters" => {
        CharsScanner::with_one_of(Box::new(|c| !c.is_ascii_control()))
      }
      _ => panic!("unexpected special-sequence!: {:?}", label),
    })
  }
}
