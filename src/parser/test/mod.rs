pub mod event_filter;
pub mod special_sequence;

use rand::{prelude::StdRng, RngCore, SeedableRng};
use regex::Regex;

use crate::{
  parser::graph::{GraphConfig, LexGraph},
  parser::Parser,
  parser::{machine::LexMachine, parallel_notation, Event},
  test::{assert_err_match, dl, sl, split_by, TEST_EBNF_NAME, TEST_TARGET_NAME},
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
fn push() {
  let ebnf = "X = 'abcdef';";
  let graph = create_graph(ebnf);
  let mut parser = Parser::new(&graph, "X", 1024, TEST_TARGET_NAME).unwrap();
  let mut events = Vec::new();
  events.append(&mut parser.push('a').unwrap());
  events.append(&mut parser.push_chars(&['b', 'c']).unwrap());
  events.append(&mut parser.push_str("def").unwrap());
  events.append(&mut parser.flush().unwrap());
  assert_eq_events(
    &vec![
      Event::begin(dl(1, 1), sl(1, 1), "X"),
      Event::token(dl(1, 5), sl(1, 1), "abcdef"),
      Event::end(dl(1, 1), sl(1, 1), "X"),
    ],
    events,
  );

  let mut parser = Parser::new(&graph, "X", 1, TEST_TARGET_NAME).unwrap();
  assert_err_match(
    &sl(1, 1),
    "The token could not be recognized after reaching the max buffer size of 1 chars\\.",
    parser.push_str("abcdef"),
  );
}

#[test]
fn terminal_string() {
  let ebnf = "A = 'a'; B = 'b'; XYZ = 'xyz'; e = ;";

  assert_success(
    ebnf,
    "A",
    "a",
    &vec![
      Event::begin(dl(1, 1), sl(1, 1), "A"),
      Event::token(dl(1, 5), sl(1, 1), "a"),
      Event::end(dl(1, 1), sl(1, 1), "A"),
    ],
  );
  assert_success(
    ebnf,
    "B",
    "b",
    &vec![
      Event::begin(dl(1, 10), sl(1, 1), "B"),
      Event::token(dl(1, 14), sl(1, 1), "b"),
      Event::end(dl(1, 10), sl(1, 1), "B"),
    ],
  );
  assert_success(
    ebnf,
    "XYZ",
    "xyz",
    &vec![
      Event::begin(dl(1, 19), sl(1, 1), "XYZ"),
      Event::token(dl(1, 25), sl(1, 1), "xyz"),
      Event::end(dl(1, 19), sl(1, 1), "XYZ"),
    ],
  );
  assert_success(
    ebnf,
    "e",
    "",
    &vec![
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
    &vec![
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
    &vec![
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
    &vec![
      Event::begin(dl(1, 28), sl(1, 1), "ABC"),
      Event::begin(dl(1, 42), sl(1, 1), "C"),
      Event::token(dl(1, 23), sl(1, 1), "c"),
      Event::end(dl(1, 42), sl(1, 1), "C"),
      Event::end(dl(1, 28), sl(1, 1), "ABC"),
    ],
  );
  assert_expected_but_not(ebnf, "ABC", "d", sl(1, 1), vec!["A", "B", "C"], "d");
  assert_expected_but_not(ebnf, "ABC", "", sl(1, 1), vec!["A", "B", "C"], "");

  // duplicate matches
  let ebnf = "A = 'a', 'a' | 'aa';";
  let graph = create_graph(ebnf);
  let mut parser = Parser::new(&graph, "A", 0, TEST_TARGET_NAME).unwrap();
  assert_err_match(
    &sl(1, 1),
    "The parsing process encountered an ambiguous match\\. .+",
    parser.push_str("aa"),
  );
}

#[test]
fn single_definition() {
  let ebnf = "A = 'a'; B = 'b'; ABC = A, B, 'c';";

  assert_success(
    ebnf,
    "ABC",
    "abc",
    &vec![
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
fn syntactic_term_with_exception() {
  let ebnf = "A = ('a' | 'b' | 'c') - ('b' | 'c');";
  assert_success(
    ebnf,
    "A",
    "a",
    &vec![
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

/// **Specification**: In a syntax that matches more than one in the definition-list, when a best
/// matching candidate is excluded by a syntactic-exception, the program will assume that there is
/// no match, instead of selecting the second candidate.
///
/// selecting the second candidate isn't supported in the current implementation because it would
/// require implementing a very complex and inefficient method that would research all matching
/// paths to their
///
// #[test]
#[allow(dead_code)]
fn syntactic_term_with_exception_when_there_is_a_other_item_to_select() {
  let ebnf = "A = ('/' | '/*') - '/*', '*';";
  assert_success(
    ebnf,
    "A",
    "/*",
    &vec![
      Event::begin(dl(1, 1), sl(1, 1), "A"),
      Event::token(dl(1, 6), sl(1, 1), "/"),
      Event::token(dl(1, 28), sl(1, 2), "*"),
      Event::end(dl(1, 1), sl(1, 1), "A"),
    ],
  );
}

#[test]
fn syntactic_term_excluding_empty_set() {
  let ebnf = "A = ['a'] - ;";
  assert_success(
    ebnf,
    "A",
    "a",
    &vec![
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
    &vec![
      Event::begin(dl(1, 1), sl(1, 1), "A"),
      Event::token(dl(1, 6), sl(1, 1), "a"),
      Event::end(dl(1, 1), sl(1, 1), "A"),
    ],
  );
  assert_success(
    ebnf,
    "A",
    "aa",
    &vec![
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
    &vec![
      Event::begin(dl(1, 1), sl(1, 1), "AB"),
      Event::token(dl(1, 7), sl(1, 1), "a"),
      Event::end(dl(1, 1), sl(1, 1), "AB"),
    ],
  );
  assert_success(
    ebnf,
    "AB",
    "b",
    &vec![
      Event::begin(dl(1, 1), sl(1, 1), "AB"),
      Event::token(dl(1, 13), sl(1, 1), "b"),
      Event::end(dl(1, 1), sl(1, 1), "AB"),
    ],
  );
  assert_expected_but_not(ebnf, "AB", "", sl(1, 1), vec!["('a'|'b'|)-"], "");
}

#[test]
fn syntactic_factor_with_repetition() {
  let ebnf = "A = 2 * ('a' | 'b', 'c');";

  assert_success(
    ebnf,
    "A",
    "aa",
    &vec![
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
    &vec![
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
    &vec![
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
    &vec![
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
fn syntactic_factor_zero_repetition() {
  let ebnf = "A = 0 * 'a';";

  assert_success(
    ebnf,
    "A",
    "",
    &vec![
      Event::begin(dl(1, 1), sl(1, 1), "A"),
      Event::end(dl(1, 1), sl(1, 1), "A"),
    ],
  );
  assert_expected_but_not(ebnf, "A", "a", sl(1, 1), vec!["EOF"], "a");
}

#[test]
fn syntactic_primary_optimal_sequence() {
  let ebnf = "A = ['a'];";

  assert_success(
    ebnf,
    "A",
    "",
    &vec![
      Event::begin(dl(1, 1), sl(1, 1), "A"),
      Event::end(dl(1, 1), sl(1, 1), "A"),
    ],
  );
  assert_success(
    ebnf,
    "A",
    "a",
    &vec![
      Event::begin(dl(1, 1), sl(1, 1), "A"),
      Event::token(dl(1, 6), sl(1, 1), "a"),
      Event::end(dl(1, 1), sl(1, 1), "A"),
    ],
  );
  assert_expected_but_not(ebnf, "A", "aa", sl(1, 2), vec!["EOF"], "a");
}

#[test]
fn syntactic_primary_optimal_sequence_nested() {
  let ebnf = "AB = ['a', ['b']];";

  assert_success(
    ebnf,
    "AB",
    "",
    &vec![
      Event::begin(dl(1, 1), sl(1, 1), "AB"),
      Event::end(dl(1, 1), sl(1, 1), "AB"),
    ],
  );
  assert_success(
    ebnf,
    "AB",
    "a",
    &vec![
      Event::begin(dl(1, 1), sl(1, 1), "AB"),
      Event::token(dl(1, 7), sl(1, 1), "a"),
      Event::end(dl(1, 1), sl(1, 1), "AB"),
    ],
  );
  assert_success(
    ebnf,
    "AB",
    "ab",
    &vec![
      Event::begin(dl(1, 1), sl(1, 1), "AB"),
      Event::token(dl(1, 7), sl(1, 1), "a"),
      Event::token(dl(1, 13), sl(1, 2), "b"),
      Event::end(dl(1, 1), sl(1, 1), "AB"),
    ],
  );
  assert_expected_but_not(ebnf, "AB", "b", sl(1, 1), vec!["EOF"], "b");
  assert_expected_but_not(ebnf, "AB", "ac", sl(1, 2), vec!["EOF"], "c");
}

#[test]
fn syntactic_primary_repeated_sequence() {
  let ebnf = "A = {'a'};";

  for i in 0..=100 {
    let test = (0..i).map(|_| "a").collect::<String>();
    let mut expected = Vec::new();
    expected.push(Event::begin(dl(1, 1), sl(1, 1), "A"));
    for j in 0..i {
      expected.push(Event::token(dl(1, 6), sl(1, j + 1), "a"));
    }
    expected.push(Event::end(dl(1, 1), sl(1, 1), "A"));

    assert_success(ebnf, "A", &test, &expected);

    let test = format!("{}b", test);
    assert_expected_but_not(ebnf, "A", &test, sl(1, i + 1), vec!["EOF"], "b");
  }
}

#[test]
fn syntactic_primary_repeated_sequence_nested() {
  let ebnf = "AB = {'a', {'b'}};";

  for i in 0..=100 {
    let mut rand = StdRng::seed_from_u64(i as u64);

    let mut test = Vec::new();
    let mut expected = Vec::new();
    expected.push(Event::begin(dl(1, 1), sl(1, 1), "AB"));
    if i > 0 {
      test.push('a');
      expected.push(Event::token(dl(1, 7), sl(1, 1), "a"));
    }
    for i in 1..i {
      let (ch, def) = if rand.next_u32() & 0x01 == 1 {
        ('a', 7)
      } else {
        ('b', 13)
      };
      test.push(ch);
      expected.push(Event::token(dl(1, def), sl(1, i + 1), ch.to_string()));
    }
    let test = test.iter().collect::<String>();
    expected.push(Event::end(dl(1, 1), sl(1, 1), "AB"));

    assert_success(ebnf, "AB", &test, &expected);

    let test = format!("{}c", test);
    assert_expected_but_not(ebnf, "AB", &test, sl(1, i + 1), vec!["EOF"], "c");
  }
}

#[test]
fn syntactic_primary_repeated_sequence_with_enclosures() {
  let ebnf = "A = '(', {'a'}, ')';";
  assert_success(
    ebnf,
    "A",
    "(a)",
    &vec![
      Event::begin(dl(1, 1), sl(1, 1), "A"),
      Event::token(dl(1, 5), sl(1, 1), "("),
      Event::token(dl(1, 11), sl(1, 2), "a"),
      Event::token(dl(1, 17), sl(1, 3), ")"),
      Event::end(dl(1, 1), sl(1, 1), "A"),
    ],
  );
  assert_success(
    ebnf,
    "A",
    "(aa)",
    &vec![
      Event::begin(dl(1, 1), sl(1, 1), "A"),
      Event::token(dl(1, 5), sl(1, 1), "("),
      Event::token(dl(1, 11), sl(1, 2), "a"),
      Event::token(dl(1, 11), sl(1, 3), "a"),
      Event::token(dl(1, 17), sl(1, 4), ")"),
      Event::end(dl(1, 1), sl(1, 1), "A"),
    ],
  );

  assert_success(
    ebnf,
    "A",
    "()",
    &vec![
      Event::begin(dl(1, 1), sl(1, 1), "A"),
      Event::token(dl(1, 5), sl(1, 1), "("),
      Event::token(dl(1, 17), sl(1, 2), ")"),
      Event::end(dl(1, 1), sl(1, 1), "A"),
    ],
  );
}

#[test]
fn syntactic_primary_grouped_sequence() {
  let ebnf = "ABC = ('a' | 'b', 'c');";

  assert_success(
    ebnf,
    "ABC",
    "a",
    &vec![
      Event::begin(dl(1, 1), sl(1, 1), "ABC"),
      Event::token(dl(1, 8), sl(1, 1), "a"),
      Event::end(dl(1, 1), sl(1, 1), "ABC"),
    ],
  );
  assert_success(
    ebnf,
    "ABC",
    "bc",
    &vec![
      Event::begin(dl(1, 1), sl(1, 1), "ABC"),
      Event::token(dl(1, 14), sl(1, 1), "b"),
      Event::token(dl(1, 19), sl(1, 2), "c"),
      Event::end(dl(1, 1), sl(1, 1), "ABC"),
    ],
  );
  assert_expected_but_not(ebnf, "ABC", "", sl(1, 1), vec!["\"a\"", "\"b\""], "");
}

#[test]
fn syntactic_primary_meta_identifier() {
  let ebnf = "A = 'a'; B = 'b'; C = 'c'; ABC = A, [B], {C};";
  assert_success(
    ebnf,
    "ABC",
    "a",
    &vec![
      Event::begin(dl(1, 28), sl(1, 1), "ABC"),
      Event::begin(dl(1, 34), sl(1, 1), "A"),
      Event::token(dl(1, 5), sl(1, 1), "a"),
      Event::end(dl(1, 34), sl(1, 1), "A"),
      Event::end(dl(1, 28), sl(1, 1), "ABC"),
    ],
  );
}

#[test]
fn syntactic_primary_terminal_string() {
  let ebnf = "AB = 'a', ['b'];";
  assert_success(
    ebnf,
    "AB",
    "a",
    &vec![
      Event::begin(dl(1, 1), sl(1, 1), "AB"),
      Event::token(dl(1, 6), sl(1, 1), "a"),
      Event::end(dl(1, 1), sl(1, 1), "AB"),
    ],
  );
}

#[test]
fn syntactic_primary_empty() {
  assert_success(
    "E = ;",
    "E",
    "",
    &vec![
      Event::begin(dl(1, 1), sl(1, 1), "E"),
      Event::end(dl(1, 1), sl(1, 1), "E"),
    ],
  );
  assert_success(
    "E = ; AB = (E | 'a' | 'b');",
    "AB",
    "",
    &vec![
      Event::begin(dl(1, 7), sl(1, 1), "AB"),
      Event::end(dl(1, 7), sl(1, 1), "AB"),
    ],
  );
  assert_success(
    "E = ; AB = ('a' | E | 'b');",
    "AB",
    "",
    &vec![
      Event::begin(dl(1, 7), sl(1, 1), "AB"),
      Event::end(dl(1, 7), sl(1, 1), "AB"),
    ],
  );
  assert_success(
    "E = ; AB = ('a' | 'b' | E);",
    "AB",
    "",
    &vec![
      Event::begin(dl(1, 7), sl(1, 1), "AB"),
      Event::end(dl(1, 7), sl(1, 1), "AB"),
    ],
  );
  assert_success(
    "E = ; AB = ('a' | E | 'b');",
    "AB",
    "",
    &vec![
      Event::begin(dl(1, 7), sl(1, 1), "AB"),
      Event::end(dl(1, 7), sl(1, 1), "AB"),
    ],
  );
  assert_success(
    "E = ; AB = ('a' | 'b' | E);",
    "AB",
    "",
    &vec![
      Event::begin(dl(1, 7), sl(1, 1), "AB"),
      Event::end(dl(1, 7), sl(1, 1), "AB"),
    ],
  );
}

#[test]
fn livelock() {
  let ebnf = "E = {}";
  let graph = create_graph(ebnf);
  let mut parser = Parser::new(&graph, "E", 0, TEST_TARGET_NAME).unwrap();
  assert_err_match(&sl(1, 1), "Livelock: .+", parser.push_str("abc"));
}

pub fn create_graph(ebnf: &str) -> LexGraph {
  create_graph_with_config(ebnf, &GraphConfig::new())
}

pub fn create_graph_with_config(ebnf: &str, config: &GraphConfig) -> LexGraph {
  let mut cursor = Cursor::new(ebnf.as_bytes());
  let syntax = Syntax::read_from_utf8(TEST_EBNF_NAME, &mut cursor, 1024).unwrap();
  LexGraph::compile(&syntax, &config)
}

pub fn assert_success(ebnf: &str, id: &str, test: &str, expected: &Vec<Event>) {
  let graph = create_graph(ebnf);
  for chars in 1..=ebnf.len() {
    let mut parser = Parser::new(&graph, id, 1024, TEST_TARGET_NAME).unwrap();
    assert_eq!(id, parser.name());

    let mut actual = Vec::new();
    for fragment in split_by(test, chars) {
      actual.append(&mut parser.push_str(&fragment).unwrap());
    }
    actual.append(&mut parser.flush().unwrap());

    assert_eq_events(expected, actual);
  }
}

pub fn assert_eq_events(expected: &Vec<Event>, actual: Vec<Event>) {
  for i in 0..std::cmp::min(actual.len(), expected.len()) {
    assert_eq!(expected[i], actual[i], "The {}-th event is different.", i + 1,);
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

pub fn assert_failure(ebnf: &str, id: &str, test: &str, location: Location, msg_match: &str) {
  let graph = create_graph(ebnf);

  let re = Regex::new(msg_match).unwrap();
  for chars in 1..=ebnf.len() {
    let mut parser = Parser::new(&graph, id, 1024, TEST_TARGET_NAME).unwrap();
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

pub fn assert_expected_but_not(
  ebnf: &str,
  id: &str,
  test: &str,
  location: Location,
  expected: Vec<&str>,
  actual: &str,
) {
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
