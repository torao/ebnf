use std::{fmt::Debug, io::Cursor};

use crate::{
  io::MarkableReader,
  parser::{
    graph::{GraphConfig, LexGraph},
    test::assert_eq_events,
    CharsScanner, Event, Parser, SpecialSequenceParser, SpecialSequenceScanner,
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
  let syntax = Syntax::read_from_utf8(TEST_EBNF_NAME, &mut cursor, 1024).unwrap();
  let mut config = GraphConfig::new();
  config.special_sequence_parser(SpecialSequenceParser::new(Box::new(|_, label| {
    special_sequence_scanner(label)
  })));
  let graph = LexGraph::compile(&syntax, &config);
  let mut parser = Parser::new(&graph, "program").unwrap();
  let mut input = MarkableReader::new(
    TEST_TARGET_NAME,
    r#"PROGRAM DEMO1
BEGIN
  A:=3;
  B:=45;
  H:=-100023;
  C:=A;
  D123:=B34A;
  BABOON:=GIRAFFE;
  TEXT:="Hello world!";
END."#
      .into(),
  );
  let events = parser.parse(&mut input).unwrap();
  assert_eq_events(
    &vec![
      Event::begin(&dl(2, 1), &sl(1, 1), "program"),
      Event::token(&dl(2, 11), &sl(1, 1), "PROGRAM"),
      Event::begin(&dl(2, 22), &sl(1, 8), "white space"),
      Event::token(&dl(15, 15), &sl(1, 8), " "),
      Event::end(&dl(2, 22), &sl(1, 9), "white space"),
      Event::begin(&dl(2, 35), &sl(1, 9), "identifier"),
      Event::begin(&dl(6, 14), &sl(1, 9), "alphabetic character"),
      Event::token(&dl(10, 42), &sl(1, 9), "D"),
      Event::end(&dl(6, 14), &sl(1, 10), "alphabetic character"),
      Event::begin(&dl(6, 38), &sl(1, 10), "alphabetic character"),
      Event::token(&dl(10, 48), &sl(1, 10), "E"),
      Event::end(&dl(6, 38), &sl(1, 11), "alphabetic character"),
      Event::begin(&dl(6, 38), &sl(1, 11), "alphabetic character"),
      Event::token(&dl(11, 45), &sl(1, 11), "M"),
      Event::end(&dl(6, 38), &sl(1, 12), "alphabetic character"),
      Event::begin(&dl(6, 38), &sl(1, 12), "alphabetic character"),
      Event::token(&dl(12, 15), &sl(1, 12), "O"),
      Event::end(&dl(6, 38), &sl(1, 13), "alphabetic character"),
      Event::begin(&dl(6, 61), &sl(1, 13), "digit"),
      Event::token(&dl(14, 15), &sl(1, 13), "1"),
      Event::end(&dl(6, 61), &sl(1, 14), "digit"),
      Event::end(&dl(2, 35), &sl(1, 14), "identifier"),
      Event::begin(&dl(2, 47), &sl(1, 14), "white space"),
      Event::token(&dl(15, 15), &sl(1, 14), "\n"),
      Event::end(&dl(2, 47), &sl(2, 1), "white space"),
      Event::token(&dl(3, 3), &sl(2, 1), "BEGIN"),
      Event::begin(&dl(3, 12), &sl(2, 6), "white space"),
      Event::token(&dl(15, 15), &sl(2, 6), "\n  "),
      Event::end(&dl(3, 12), &sl(3, 3), "white space"),
      Event::begin(&dl(4, 5), &sl(3, 3), "assignment"),
      Event::begin(&dl(9, 14), &sl(3, 3), "identifier"),
      Event::begin(&dl(6, 14), &sl(3, 3), "alphabetic character"),
      Event::token(&dl(10, 24), &sl(3, 3), "A"),
      Event::end(&dl(6, 14), &sl(3, 4), "alphabetic character"),
      Event::end(&dl(9, 14), &sl(3, 4), "identifier"),
      Event::token(&dl(9, 27), &sl(3, 4), ":="),
      Event::begin(&dl(9, 36), &sl(3, 6), "number"),
      Event::begin(&dl(7, 19), &sl(3, 6), "digit"),
      Event::token(&dl(14, 27), &sl(3, 6), "3"),
      Event::end(&dl(7, 19), &sl(3, 7), "digit"),
      Event::end(&dl(9, 36), &sl(3, 7), "number"),
      Event::end(&dl(4, 5), &sl(3, 7), "assignment"),
      Event::token(&dl(4, 17), &sl(3, 7), ";"),
      Event::begin(&dl(4, 22), &sl(3, 8), "white space"),
      Event::token(&dl(15, 15), &sl(3, 8), "\n  "),
      Event::end(&dl(4, 22), &sl(4, 3), "white space"),
      Event::begin(&dl(4, 5), &sl(4, 3), "assignment"),
      Event::begin(&dl(9, 14), &sl(4, 3), "identifier"),
      Event::begin(&dl(6, 14), &sl(4, 3), "alphabetic character"),
      Event::token(&dl(10, 30), &sl(4, 3), "B"),
      Event::end(&dl(6, 14), &sl(4, 4), "alphabetic character"),
      Event::end(&dl(9, 14), &sl(4, 4), "identifier"),
      Event::token(&dl(9, 27), &sl(4, 4), ":="),
      Event::begin(&dl(9, 36), &sl(4, 6), "number"),
      Event::begin(&dl(7, 19), &sl(4, 6), "digit"),
      Event::token(&dl(14, 33), &sl(4, 6), "4"),
      Event::end(&dl(7, 19), &sl(4, 7), "digit"),
      Event::begin(&dl(7, 28), &sl(4, 7), "digit"),
      Event::token(&dl(14, 39), &sl(4, 7), "5"),
      Event::end(&dl(7, 28), &sl(4, 8), "digit"),
      Event::end(&dl(9, 36), &sl(4, 8), "number"),
      Event::end(&dl(4, 5), &sl(4, 8), "assignment"),
      Event::token(&dl(4, 17), &sl(4, 8), ";"),
      Event::begin(&dl(4, 22), &sl(4, 9), "white space"),
      Event::token(&dl(15, 15), &sl(4, 9), "\n  "),
      Event::end(&dl(4, 22), &sl(5, 3), "white space"),
      Event::begin(&dl(4, 5), &sl(5, 3), "assignment"),
      Event::begin(&dl(9, 14), &sl(5, 3), "identifier"),
      Event::begin(&dl(6, 14), &sl(5, 3), "alphabetic character"),
      Event::token(&dl(11, 15), &sl(5, 3), "H"),
      Event::end(&dl(6, 14), &sl(5, 4), "alphabetic character"),
      Event::end(&dl(9, 14), &sl(5, 4), "identifier"),
      Event::token(&dl(9, 27), &sl(5, 4), ":="),
      Event::begin(&dl(9, 36), &sl(5, 6), "number"),
      Event::token(&dl(7, 12), &sl(5, 6), "-"),
      Event::begin(&dl(7, 19), &sl(5, 7), "digit"),
      Event::token(&dl(14, 15), &sl(5, 7), "1"),
      Event::end(&dl(7, 19), &sl(5, 8), "digit"),
      Event::begin(&dl(7, 28), &sl(5, 8), "digit"),
      Event::token(&dl(14, 9), &sl(5, 8), "0"),
      Event::end(&dl(7, 28), &sl(5, 9), "digit"),
      Event::begin(&dl(7, 28), &sl(5, 9), "digit"),
      Event::token(&dl(14, 9), &sl(5, 9), "0"),
      Event::end(&dl(7, 28), &sl(5, 10), "digit"),
      Event::begin(&dl(7, 28), &sl(5, 10), "digit"),
      Event::token(&dl(14, 9), &sl(5, 10), "0"),
      Event::end(&dl(7, 28), &sl(5, 11), "digit"),
      Event::begin(&dl(7, 28), &sl(5, 11), "digit"),
      Event::token(&dl(14, 21), &sl(5, 11), "2"),
      Event::end(&dl(7, 28), &sl(5, 12), "digit"),
      Event::begin(&dl(7, 28), &sl(5, 12), "digit"),
      Event::token(&dl(14, 27), &sl(5, 12), "3"),
      Event::end(&dl(7, 28), &sl(5, 13), "digit"),
      Event::end(&dl(9, 36), &sl(5, 13), "number"),
      Event::end(&dl(4, 5), &sl(5, 13), "assignment"),
      Event::token(&dl(4, 17), &sl(5, 13), ";"),
      Event::begin(&dl(4, 22), &sl(5, 14), "white space"),
      Event::token(&dl(15, 15), &sl(5, 14), "\n  "),
      Event::end(&dl(4, 22), &sl(6, 3), "white space"),
      Event::begin(&dl(4, 5), &sl(6, 3), "assignment"),
      Event::begin(&dl(9, 14), &sl(6, 3), "identifier"),
      Event::begin(&dl(6, 14), &sl(6, 3), "alphabetic character"),
      Event::token(&dl(10, 36), &sl(6, 3), "C"),
      Event::end(&dl(6, 14), &sl(6, 4), "alphabetic character"),
      Event::end(&dl(9, 14), &sl(6, 4), "identifier"),
      Event::token(&dl(9, 27), &sl(6, 4), ":="),
      Event::begin(&dl(9, 45), &sl(6, 6), "identifier"),
      Event::begin(&dl(6, 14), &sl(6, 6), "alphabetic character"),
      Event::token(&dl(10, 24), &sl(6, 6), "A"),
      Event::end(&dl(6, 14), &sl(6, 7), "alphabetic character"),
      Event::end(&dl(9, 45), &sl(6, 7), "identifier"),
      Event::end(&dl(4, 5), &sl(6, 7), "assignment"),
      Event::token(&dl(4, 17), &sl(6, 7), ";"),
      Event::begin(&dl(4, 22), &sl(6, 8), "white space"),
      Event::token(&dl(15, 15), &sl(6, 8), "\n  "),
      Event::end(&dl(4, 22), &sl(7, 3), "white space"),
      Event::begin(&dl(4, 5), &sl(7, 3), "assignment"),
      Event::begin(&dl(9, 14), &sl(7, 3), "identifier"),
      Event::begin(&dl(6, 14), &sl(7, 3), "alphabetic character"),
      Event::token(&dl(10, 42), &sl(7, 3), "D"),
      Event::end(&dl(6, 14), &sl(7, 4), "alphabetic character"),
      Event::begin(&dl(6, 61), &sl(7, 4), "digit"),
      Event::token(&dl(14, 15), &sl(7, 4), "1"),
      Event::end(&dl(6, 61), &sl(7, 5), "digit"),
      Event::begin(&dl(6, 61), &sl(7, 5), "digit"),
      Event::token(&dl(14, 21), &sl(7, 5), "2"),
      Event::end(&dl(6, 61), &sl(7, 6), "digit"),
      Event::begin(&dl(6, 61), &sl(7, 6), "digit"),
      Event::token(&dl(14, 27), &sl(7, 6), "3"),
      Event::end(&dl(6, 61), &sl(7, 7), "digit"),
      Event::end(&dl(9, 14), &sl(7, 7), "identifier"),
      Event::token(&dl(9, 27), &sl(7, 7), ":="),
      Event::begin(&dl(9, 45), &sl(7, 9), "identifier"),
      Event::begin(&dl(6, 14), &sl(7, 9), "alphabetic character"),
      Event::token(&dl(10, 30), &sl(7, 9), "B"),
      Event::end(&dl(6, 14), &sl(7, 10), "alphabetic character"),
      Event::begin(&dl(6, 61), &sl(7, 10), "digit"),
      Event::token(&dl(14, 27), &sl(7, 10), "3"),
      Event::end(&dl(6, 61), &sl(7, 11), "digit"),
      Event::begin(&dl(6, 61), &sl(7, 11), "digit"),
      Event::token(&dl(14, 33), &sl(7, 11), "4"),
      Event::end(&dl(6, 61), &sl(7, 12), "digit"),
      Event::begin(&dl(6, 38), &sl(7, 12), "alphabetic character"),
      Event::token(&dl(10, 24), &sl(7, 12), "A"),
      Event::end(&dl(6, 38), &sl(7, 13), "alphabetic character"),
      Event::end(&dl(9, 45), &sl(7, 13), "identifier"),
      Event::end(&dl(4, 5), &sl(7, 13), "assignment"),
      Event::token(&dl(4, 17), &sl(7, 13), ";"),
      Event::begin(&dl(4, 22), &sl(7, 14), "white space"),
      Event::token(&dl(15, 15), &sl(7, 14), "\n  "),
      Event::end(&dl(4, 22), &sl(8, 3), "white space"),
      Event::begin(&dl(4, 5), &sl(8, 3), "assignment"),
      Event::begin(&dl(9, 14), &sl(8, 3), "identifier"),
      Event::begin(&dl(6, 14), &sl(8, 3), "alphabetic character"),
      Event::token(&dl(10, 30), &sl(8, 3), "B"),
      Event::end(&dl(6, 14), &sl(8, 4), "alphabetic character"),
      Event::begin(&dl(6, 38), &sl(8, 4), "alphabetic character"),
      Event::token(&dl(10, 24), &sl(8, 4), "A"),
      Event::end(&dl(6, 38), &sl(8, 5), "alphabetic character"),
      Event::begin(&dl(6, 38), &sl(8, 5), "alphabetic character"),
      Event::token(&dl(10, 30), &sl(8, 5), "B"),
      Event::end(&dl(6, 38), &sl(8, 6), "alphabetic character"),
      Event::begin(&dl(6, 38), &sl(8, 6), "alphabetic character"),
      Event::token(&dl(12, 15), &sl(8, 6), "O"),
      Event::end(&dl(6, 38), &sl(8, 7), "alphabetic character"),
      Event::begin(&dl(6, 38), &sl(8, 7), "alphabetic character"),
      Event::token(&dl(12, 15), &sl(8, 7), "O"),
      Event::end(&dl(6, 38), &sl(8, 8), "alphabetic character"),
      Event::begin(&dl(6, 38), &sl(8, 8), "alphabetic character"),
      Event::token(&dl(11, 51), &sl(8, 8), "N"),
      Event::end(&dl(6, 38), &sl(8, 9), "alphabetic character"),
      Event::end(&dl(9, 14), &sl(8, 9), "identifier"),
      Event::token(&dl(9, 27), &sl(8, 9), ":="),
      Event::begin(&dl(9, 45), &sl(8, 11), "identifier"),
      Event::begin(&dl(6, 14), &sl(8, 11), "alphabetic character"),
      Event::token(&dl(10, 60), &sl(8, 11), "G"),
      Event::end(&dl(6, 14), &sl(8, 12), "alphabetic character"),
      Event::begin(&dl(6, 38), &sl(8, 12), "alphabetic character"),
      Event::token(&dl(11, 21), &sl(8, 12), "I"),
      Event::end(&dl(6, 38), &sl(8, 13), "alphabetic character"),
      Event::begin(&dl(6, 38), &sl(8, 13), "alphabetic character"),
      Event::token(&dl(12, 33), &sl(8, 13), "R"),
      Event::end(&dl(6, 38), &sl(8, 14), "alphabetic character"),
      Event::begin(&dl(6, 38), &sl(8, 14), "alphabetic character"),
      Event::token(&dl(10, 24), &sl(8, 14), "A"),
      Event::end(&dl(6, 38), &sl(8, 15), "alphabetic character"),
      Event::begin(&dl(6, 38), &sl(8, 15), "alphabetic character"),
      Event::token(&dl(10, 54), &sl(8, 15), "F"),
      Event::end(&dl(6, 38), &sl(8, 16), "alphabetic character"),
      Event::begin(&dl(6, 38), &sl(8, 16), "alphabetic character"),
      Event::token(&dl(10, 54), &sl(8, 16), "F"),
      Event::end(&dl(6, 38), &sl(8, 17), "alphabetic character"),
      Event::begin(&dl(6, 38), &sl(8, 17), "alphabetic character"),
      Event::token(&dl(10, 48), &sl(8, 17), "E"),
      Event::end(&dl(6, 38), &sl(8, 18), "alphabetic character"),
      Event::end(&dl(9, 45), &sl(8, 18), "identifier"),
      Event::end(&dl(4, 5), &sl(8, 18), "assignment"),
      Event::token(&dl(4, 17), &sl(8, 18), ";"),
      Event::begin(&dl(4, 22), &sl(8, 19), "white space"),
      Event::token(&dl(15, 15), &sl(8, 19), "\n  "),
      Event::end(&dl(4, 22), &sl(9, 3), "white space"),
      Event::begin(&dl(4, 5), &sl(9, 3), "assignment"),
      Event::begin(&dl(9, 14), &sl(9, 3), "identifier"),
      Event::begin(&dl(6, 14), &sl(9, 3), "alphabetic character"),
      Event::token(&dl(12, 45), &sl(9, 3), "T"),
      Event::end(&dl(6, 14), &sl(9, 4), "alphabetic character"),
      Event::begin(&dl(6, 38), &sl(9, 4), "alphabetic character"),
      Event::token(&dl(10, 48), &sl(9, 4), "E"),
      Event::end(&dl(6, 38), &sl(9, 5), "alphabetic character"),
      Event::begin(&dl(6, 38), &sl(9, 5), "alphabetic character"),
      Event::token(&dl(13, 27), &sl(9, 5), "X"),
      Event::end(&dl(6, 38), &sl(9, 6), "alphabetic character"),
      Event::begin(&dl(6, 38), &sl(9, 6), "alphabetic character"),
      Event::token(&dl(12, 45), &sl(9, 6), "T"),
      Event::end(&dl(6, 38), &sl(9, 7), "alphabetic character"),
      Event::end(&dl(9, 14), &sl(9, 7), "identifier"),
      Event::token(&dl(9, 27), &sl(9, 7), ":="),
      Event::begin(&dl(9, 58), &sl(9, 9), "string"),
      Event::token(&dl(8, 10), &sl(9, 9), "\""),
      Event::begin(&dl(8, 18), &sl(9, 10), "all characters"),
      Event::token(&dl(16, 18), &sl(9, 10), "H"),
      Event::end(&dl(8, 18), &sl(9, 11), "all characters"),
      Event::begin(&dl(8, 18), &sl(9, 11), "all characters"),
      Event::token(&dl(16, 18), &sl(9, 11), "e"),
      Event::end(&dl(8, 18), &sl(9, 12), "all characters"),
      Event::begin(&dl(8, 18), &sl(9, 12), "all characters"),
      Event::token(&dl(16, 18), &sl(9, 12), "l"),
      Event::end(&dl(8, 18), &sl(9, 13), "all characters"),
      Event::begin(&dl(8, 18), &sl(9, 13), "all characters"),
      Event::token(&dl(16, 18), &sl(9, 13), "l"),
      Event::end(&dl(8, 18), &sl(9, 14), "all characters"),
      Event::begin(&dl(8, 18), &sl(9, 14), "all characters"),
      Event::token(&dl(16, 18), &sl(9, 14), "o"),
      Event::end(&dl(8, 18), &sl(9, 15), "all characters"),
      Event::begin(&dl(8, 18), &sl(9, 15), "all characters"),
      Event::token(&dl(16, 18), &sl(9, 15), " "),
      Event::end(&dl(8, 18), &sl(9, 16), "all characters"),
      Event::begin(&dl(8, 18), &sl(9, 16), "all characters"),
      Event::token(&dl(16, 18), &sl(9, 16), "w"),
      Event::end(&dl(8, 18), &sl(9, 17), "all characters"),
      Event::begin(&dl(8, 18), &sl(9, 17), "all characters"),
      Event::token(&dl(16, 18), &sl(9, 17), "o"),
      Event::end(&dl(8, 18), &sl(9, 18), "all characters"),
      Event::begin(&dl(8, 18), &sl(9, 18), "all characters"),
      Event::token(&dl(16, 18), &sl(9, 18), "r"),
      Event::end(&dl(8, 18), &sl(9, 19), "all characters"),
      Event::begin(&dl(8, 18), &sl(9, 19), "all characters"),
      Event::token(&dl(16, 18), &sl(9, 19), "l"),
      Event::end(&dl(8, 18), &sl(9, 20), "all characters"),
      Event::begin(&dl(8, 18), &sl(9, 20), "all characters"),
      Event::token(&dl(16, 18), &sl(9, 20), "d"),
      Event::end(&dl(8, 18), &sl(9, 21), "all characters"),
      Event::begin(&dl(8, 18), &sl(9, 21), "all characters"),
      Event::token(&dl(16, 18), &sl(9, 21), "!"),
      Event::end(&dl(8, 18), &sl(9, 22), "all characters"),
      Event::token(&dl(8, 42), &sl(9, 22), "\""),
      Event::end(&dl(9, 58), &sl(9, 23), "string"),
      Event::end(&dl(4, 5), &sl(9, 23), "assignment"),
      Event::token(&dl(4, 17), &sl(9, 23), ";"),
      Event::begin(&dl(4, 22), &sl(9, 24), "white space"),
      Event::token(&dl(15, 15), &sl(9, 24), "\n"),
      Event::end(&dl(4, 22), &sl(10, 1), "white space"),
      Event::token(&dl(5, 3), &sl(10, 1), "END."),
      Event::end(&dl(2, 1), &sl(10, 5), "program"),
    ],
    events,
  );

  fn special_sequence_scanner(label: &str) -> Box<dyn SpecialSequenceScanner> {
    Box::new(match label.trim() {
      "white space characters" => {
        CharsScanner::with_one_or_more(Box::new(|c| c.is_whitespace() || c.is_ascii_control()))
      }
      "all visible characters" => CharsScanner::with_one_of(Box::new(|c| !c.is_ascii_control())),
      _ => panic!("unexpected special-sequence!: {:?}", label),
    })
  }
}
