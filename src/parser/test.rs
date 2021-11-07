use regex::Regex;

use crate::{
  parser::graph::{GraphConfig, LexGraph},
  parser::Parser,
  parser::{machine::LexMachine, parallel_notation, Event},
  test::split_by,
  Location, Syntax,
};
use std::io::Cursor;

#[test]
fn test() {
  let ebnf = b"A = 'a'; B = 'b'; AB = A, B;";
  let mut cursor = Cursor::new(ebnf);
  let syntax = Syntax::read_from_utf8("definition.ebnf", &mut cursor, 1024).unwrap();

  let config = GraphConfig::new();
  let graph = LexGraph::compile(&syntax, &config);

  let mut parser = Parser::new(&graph, "A", 1024, "target.txt").unwrap();
  let mut tokens = Vec::new();
  assert_eq!("A", parser.name());
  tokens.append(&mut parser.push_str("a").unwrap());
  tokens.append(&mut parser.flush().unwrap());
  assert_eq!(
    vec![
      Event::begin(dl(1, 1), sl(1, 1), "A"),
      Event::token(dl(1, 5), sl(1, 1), "a"),
      Event::end(dl(1, 1), sl(1, 1), "A"),
    ],
    tokens
  );

  let mut parser = Parser::new(&graph, "AB", 1024, "target.txt").unwrap();
  let mut tokens = Vec::new();
  assert_eq!("AB", parser.name());
  tokens.append(&mut parser.push_str("ab").unwrap());
  tokens.append(&mut parser.flush().unwrap());
  assert_eq!(
    vec![
      Event::begin(dl(1, 19), sl(1, 1), "AB"),
      Event::begin(dl(1, 24), sl(1, 1), "A"),
      Event::token(dl(1, 5), sl(1, 1), "a"),
      Event::end(dl(1, 24), sl(1, 1), "A"),
      Event::begin(dl(1, 27), sl(1, 2), "B"),
      Event::token(dl(1, 14), sl(1, 2), "b"),
      Event::end(dl(1, 27), sl(1, 2), "B"),
      Event::end(dl(1, 19), sl(1, 1), "AB"),
    ],
    tokens
  );
}

#[test]
fn terminal_string() {
  let ebnf = "A = 'a'; B = 'b'; XYZ = 'xyz'; e = ;";

  assert_success(
    ebnf,
    "A",
    "a",
    vec![
      Event::begin(dl(1, 1), sl(1, 1), "A"),
      Event::token(dl(1, 5), sl(1, 1), "a"),
      Event::end(dl(1, 1), sl(1, 1), "A"),
    ],
  );
  assert_success(
    ebnf,
    "B",
    "b",
    vec![
      Event::begin(dl(1, 10), sl(1, 1), "B"),
      Event::token(dl(1, 14), sl(1, 1), "b"),
      Event::end(dl(1, 10), sl(1, 1), "B"),
    ],
  );
  assert_success(
    ebnf,
    "XYZ",
    "xyz",
    vec![
      Event::begin(dl(1, 19), sl(1, 1), "XYZ"),
      Event::token(dl(1, 25), sl(1, 1), "xyz"),
      Event::end(dl(1, 19), sl(1, 1), "XYZ"),
    ],
  );
  assert_success(
    ebnf,
    "e",
    "",
    vec![
      Event::begin(dl(1, 32), sl(1, 1), "e"),
      Event::end(dl(1, 32), sl(1, 1), "e"),
    ],
  );
  assert_expected_but_not(ebnf, "XYZ", "d", sl(1, 1), vec!["\"xyz\""], "d");
  assert_expected_but_not(ebnf, "XYZ", "", sl(1, 1), vec!["\"xyz\""], "");
}

#[test]
fn definition_list() {
  let ebnf = "A = 'a'; B = 'b'; C = 'c'; ABC = A | B | C;";

  assert_success(
    ebnf,
    "ABC",
    "a",
    vec![
      Event::begin(dl(1, 28), sl(1, 1), "ABC"),
      Event::begin(dl(1, 34), sl(1, 1), "A"),
      Event::token(dl(1, 5), sl(1, 1), "a"),
      Event::end(dl(1, 34), sl(1, 1), "A"),
      Event::end(dl(1, 28), sl(1, 1), "ABC"),
    ],
  );
  assert_success(
    ebnf,
    "ABC",
    "b",
    vec![
      Event::begin(dl(1, 28), sl(1, 1), "ABC"),
      Event::begin(dl(1, 38), sl(1, 1), "B"),
      Event::token(dl(1, 14), sl(1, 1), "b"),
      Event::end(dl(1, 38), sl(1, 1), "B"),
      Event::end(dl(1, 28), sl(1, 1), "ABC"),
    ],
  );
  assert_success(
    ebnf,
    "ABC",
    "c",
    vec![
      Event::begin(dl(1, 28), sl(1, 1), "ABC"),
      Event::begin(dl(1, 42), sl(1, 1), "C"),
      Event::token(dl(1, 23), sl(1, 1), "c"),
      Event::end(dl(1, 42), sl(1, 1), "C"),
      Event::end(dl(1, 28), sl(1, 1), "ABC"),
    ],
  );
  assert_expected_but_not(ebnf, "ABC", "d", sl(1, 1), vec!["A", "B", "C"], "d");
  assert_expected_but_not(ebnf, "ABC", "", sl(1, 1), vec!["A", "B", "C"], "");
}

#[test]
fn single_definition() {
  let ebnf = "A = 'a'; B = 'b'; ABC = A, B, 'c';";

  assert_success(
    ebnf,
    "ABC",
    "abc",
    vec![
      Event::begin(dl(1, 19), sl(1, 1), "ABC"),
      Event::begin(dl(1, 25), sl(1, 1), "A"),
      Event::token(dl(1, 5), sl(1, 1), "a"),
      Event::end(dl(1, 25), sl(1, 1), "A"),
      Event::begin(dl(1, 28), sl(1, 2), "B"),
      Event::token(dl(1, 14), sl(1, 2), "b"),
      Event::end(dl(1, 28), sl(1, 2), "B"),
      Event::token(dl(1, 31), sl(1, 3), "c"),
      Event::end(dl(1, 19), sl(1, 1), "ABC"),
    ],
  );
  assert_expected_but_not(ebnf, "ABC", "a", sl(1, 2), vec!["\"b\""], "");
  assert_expected_but_not(ebnf, "ABC", "ab", sl(1, 3), vec!["\"c\""], "");
  assert_expected_but_not(ebnf, "ABC", "abcd", sl(1, 4), vec!["EOF"], "d");
  assert_expected_but_not(ebnf, "ABC", "d", sl(1, 1), vec!["\"a\""], "d");
  assert_expected_but_not(ebnf, "ABC", "", sl(1, 1), vec!["\"a\""], "");
}

#[test]
fn syntactic_factor_with_repetition() {
  let ebnf = "A = 2 * ('a' | 'b', 'c');";

  assert_success(
    ebnf,
    "A",
    "aa",
    vec![
      Event::begin(dl(1, 1), sl(1, 1), "A"),
      Event::token(dl(1, 10), sl(1, 1), "a"),
      Event::token(dl(1, 10), sl(1, 2), "a"),
      Event::end(dl(1, 1), sl(1, 1), "A"),
    ],
  );
  assert_success(
    ebnf,
    "A",
    "abc",
    vec![
      Event::begin(dl(1, 1), sl(1, 1), "A"),
      Event::token(dl(1, 10), sl(1, 1), "a"),
      Event::token(dl(1, 16), sl(1, 2), "b"),
      Event::token(dl(1, 21), sl(1, 3), "c"),
      Event::end(dl(1, 1), sl(1, 1), "A"),
    ],
  );
  assert_success(
    ebnf,
    "A",
    "bcbc",
    vec![
      Event::begin(dl(1, 1), sl(1, 1), "A"),
      Event::token(dl(1, 16), sl(1, 1), "b"),
      Event::token(dl(1, 21), sl(1, 2), "c"),
      Event::token(dl(1, 16), sl(1, 3), "b"),
      Event::token(dl(1, 21), sl(1, 4), "c"),
      Event::end(dl(1, 1), sl(1, 1), "A"),
    ],
  );
  assert_success(
    ebnf,
    "A",
    "bca",
    vec![
      Event::begin(dl(1, 1), sl(1, 1), "A"),
      Event::token(dl(1, 16), sl(1, 1), "b"),
      Event::token(dl(1, 21), sl(1, 2), "c"),
      Event::token(dl(1, 10), sl(1, 3), "a"),
      Event::end(dl(1, 1), sl(1, 1), "A"),
    ],
  );
  assert_expected_but_not(ebnf, "A", "", sl(1, 1), vec!["\"a\"", "\"b\""], "");
  assert_expected_but_not(ebnf, "A", "x", sl(1, 1), vec!["\"a\"", "\"b\""], "x");
  assert_expected_but_not(ebnf, "A", "a", sl(1, 2), vec!["\"a\"", "\"b\""], "");
  assert_expected_but_not(ebnf, "A", "ax", sl(1, 2), vec!["\"a\"", "\"b\""], "x");
  assert_expected_but_not(ebnf, "A", "ab", sl(1, 3), vec!["\"c\""], "");
  assert_expected_but_not(ebnf, "A", "aaa", sl(1, 3), vec!["EOF"], "a");
  assert_expected_but_not(ebnf, "A", "aab", sl(1, 3), vec!["EOF"], "b");
  assert_expected_but_not(ebnf, "A", "aax", sl(1, 3), vec!["EOF"], "x");
  assert_expected_but_not(ebnf, "A", "b", sl(1, 2), vec!["\"c\""], "");
  assert_expected_but_not(ebnf, "A", "bx", sl(1, 2), vec!["\"c\""], "x");
  assert_expected_but_not(ebnf, "A", "bc", sl(1, 3), vec!["\"a\"", "\"b\""], "");
  assert_expected_but_not(ebnf, "A", "bcb", sl(1, 4), vec!["\"c\""], "");
  assert_expected_but_not(ebnf, "A", "bcbx", sl(1, 4), vec!["\"c\""], "x");
  assert_expected_but_not(ebnf, "A", "bcbca", sl(1, 5), vec!["EOF"], "a");
  assert_expected_but_not(ebnf, "A", "bcbcb", sl(1, 5), vec!["EOF"], "b");
  assert_expected_but_not(ebnf, "A", "bcbcx", sl(1, 5), vec!["EOF"], "x");
}

#[test]
fn syntactic_term_with_exception() {
  let ebnf = "A = ('a' | 'b' | 'c') - ('b' | 'c');";
  assert_success(
    ebnf,
    "A",
    "a",
    vec![
      Event::begin(dl(1, 1), sl(1, 1), "A"),
      Event::token(dl(1, 6), sl(1, 1), "a"),
      Event::end(dl(1, 1), sl(1, 1), "A"),
    ],
  );
  assert_expected_but_not(ebnf, "A", "b", sl(1, 1), vec!["('a'|'b'|'c')-('b'|'c')"], "b");
  assert_expected_but_not(ebnf, "A", "c", sl(1, 1), vec!["('a'|'b'|'c')-('b'|'c')"], "c");
  assert_expected_but_not(ebnf, "A", "d", sl(1, 1), vec!["\"a\"", "\"b\"", "\"c\""], "d");
  assert_expected_but_not(ebnf, "A", "", sl(1, 1), vec!["\"a\"", "\"b\"", "\"c\""], "");
}

#[test]
fn syntactic_term_excluding_empty_set() {
  let ebnf = "A = ['a'] - ;";
  assert_success(
    ebnf,
    "A",
    "a",
    vec![
      Event::begin(dl(1, 1), sl(1, 1), "A"),
      Event::token(dl(1, 6), sl(1, 1), "a"),
      Event::end(dl(1, 1), sl(1, 1), "A"),
    ],
  );
  assert_expected_but_not(ebnf, "A", "", sl(1, 1), vec!["['a']-"], "");

  let ebnf = "A = {'a'} - ;";
  assert_success(
    ebnf,
    "A",
    "a",
    vec![
      Event::begin(dl(1, 1), sl(1, 1), "A"),
      Event::token(dl(1, 6), sl(1, 1), "a"),
      Event::end(dl(1, 1), sl(1, 1), "A"),
    ],
  );
  assert_success(
    ebnf,
    "A",
    "aa",
    vec![
      Event::begin(dl(1, 1), sl(1, 1), "A"),
      Event::token(dl(1, 6), sl(1, 1), "a"),
      Event::token(dl(1, 6), sl(1, 2), "a"),
      Event::end(dl(1, 1), sl(1, 1), "A"),
    ],
  );
  assert_expected_but_not(ebnf, "A", "", sl(1, 1), vec!["{'a'}-"], "");

  let ebnf = "AB = ('a' | 'b' | ) - ;";
  assert_success(
    ebnf,
    "AB",
    "a",
    vec![
      Event::begin(dl(1, 1), sl(1, 1), "AB"),
      Event::token(dl(1, 7), sl(1, 1), "a"),
      Event::end(dl(1, 1), sl(1, 1), "AB"),
    ],
  );
  assert_success(
    ebnf,
    "AB",
    "b",
    vec![
      Event::begin(dl(1, 1), sl(1, 1), "AB"),
      Event::token(dl(1, 13), sl(1, 1), "b"),
      Event::end(dl(1, 1), sl(1, 1), "AB"),
    ],
  );
  assert_expected_but_not(ebnf, "AB", "", sl(1, 1), vec!["('a'|'b'|)-"], "");
}

const DEFAULT_EBNF_NAME: &str = "definition.ebnf";
const DEFAULT_SOURCE_NAME: &str = "target.txt";

fn dl(lines: u64, columns: u64) -> Location {
  Location::with_location(DEFAULT_EBNF_NAME, lines, columns)
}

fn sl(lines: u64, columns: u64) -> Location {
  Location::with_location(DEFAULT_SOURCE_NAME, lines, columns)
}

fn create_graph(ebnf: &str) -> LexGraph {
  let mut cursor = Cursor::new(ebnf.as_bytes());
  let syntax = Syntax::read_from_utf8(DEFAULT_EBNF_NAME, &mut cursor, 1024).unwrap();
  let config = GraphConfig::new();
  LexGraph::compile(&syntax, &config)
}

fn assert_success(ebnf: &str, id: &str, test: &str, expected: Vec<Event>) {
  let graph = create_graph(ebnf);

  for chars in 1..=ebnf.len() {
    let mut parser = Parser::new(&graph, id, 1024, DEFAULT_SOURCE_NAME).unwrap();
    assert_eq!(id, parser.name());

    let mut actual = Vec::new();
    for fragment in split_by(test, chars) {
      actual.append(&mut parser.push_str(&fragment).unwrap());
    }
    actual.append(&mut parser.flush().unwrap());

    for i in 0..std::cmp::min(actual.len(), expected.len()) {
      assert_eq!(
        expected[i],
        actual[i],
        "The {}-th event is different for the {}-width division.",
        i + 1,
        chars
      );
    }
    assert_eq!(
      expected.len(),
      actual.len(),
      "The length of the event is different. {}",
      if expected.len() > actual.len() {
        format!(
          "The actual events are less than expected: expected[{}] = {:?}",
          actual.len(),
          expected[actual.len()]
        )
      } else {
        format!(
          "The actual events are more than expected: actual[{}] = {:?}",
          expected.len(),
          actual[expected.len()]
        )
      }
    );
  }
}

fn assert_failure(ebnf: &str, id: &str, test: &str, location: Location, msg_match: &str) {
  let graph = create_graph(ebnf);

  let re = Regex::new(msg_match).unwrap();
  for chars in 1..=ebnf.len() {
    let mut parser = Parser::new(&graph, id, 1024, DEFAULT_SOURCE_NAME).unwrap();
    assert_eq!(id, parser.name());

    let mut error = None;
    for fragment in split_by(test, chars) {
      if let Err(err) = parser.push_str(&fragment) {
        error = Some(err);
        break;
      }
    }
    if error.is_none() {
      if let Err(err) = parser.flush() {
        error = Some(err);
      }
    }

    if let Some(err) = error {
      if !re.is_match(&err.message) {
        assert_eq!(msg_match, err.message, "Unexpected error message: {}", err.location);
      }
      assert_eq!(
        location, err.location,
        "The location of error did't match: {}",
        err.message
      );
    } else {
      panic!("The program terminated successfully without the expected error.");
    }
  }
}

fn assert_expected_but_not(ebnf: &str, id: &str, test: &str, location: Location, expected: Vec<&str>, actual: &str) {
  let expected = expected.iter().map(|s| s.to_string()).collect::<Vec<_>>();
  let message = LexMachine::error_expected_but_not::<()>(
    &location,
    &parallel_notation(expected, "or"),
    &actual.chars().collect::<Vec<_>>(),
  )
  .unwrap_err()
  .message;
  let message = regex::escape(&message);
  assert_failure(ebnf, id, test, location, &message)
}
