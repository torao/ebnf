use std::io::Cursor;

use crate::{
  io::{MarkableCharReader, MarkableReader},
  parser::{
    graph::{GraphConfig, LexGraph},
    test::{assert_eq_events, create_graph_with_config, dl, sl, TEST_EBNF_NAME, TEST_TARGET_NAME},
    CharsScanner, Event, Parser, Reaction, RegExScanner, SpecialSequenceParser, SpecialSequenceScanner,
  },
  Location, Syntax,
};

#[test]
fn default() {
  let default = SpecialSequenceParser::default();
  let scanner = default.0(&dl(1, 1), "default scanner");
  let mut input = MarkableReader::new(TEST_TARGET_NAME, "\u{0}".into());
  assert_eq!("?default scanner?", scanner.symbol());
  assert_eq!(
    Ok(Reaction::Match { events: vec![] }),
    scanner.scan(&sl(1, 1), &mut input)
  )
}

#[test]
fn non_ascii_unicode_characters() {
  fn is_non_ascii_unicode(ch: char) -> bool {
    ch as u32 >= 0x80
  }

  // parse and build a special-sequence syntax
  let ebnf = "SS = '[', ? non-ascii ?, ']'";
  let syntax = Syntax::read_from_str(TEST_EBNF_NAME, ebnf, 0).unwrap();

  // build instruction graph with non-ascii special-sequence scanner
  let mut config = GraphConfig::new();
  config.special_sequence_parser(SpecialSequenceParser::new(Box::new(
    |_, _| -> Box<dyn SpecialSequenceScanner> {
      Box::new(CharsScanner::with_zero_or_more(Box::new(is_non_ascii_unicode)))
    },
  )));
  let graph = LexGraph::compile(&syntax, &config);

  // parse a text with non-ascii characters
  let mut parser = Parser::new(&graph, "SS").unwrap();
  let mut input = MarkableReader::new(TEST_TARGET_NAME, "[あいうえお]".into());
  let actual = parser.parse(&mut input).unwrap();
  assert_eq_events(
    &vec![
      Event::begin(&dl(1, 1), &sl(1, 1), "SS"),
      Event::token(&dl(1, 6), &sl(1, 1), "["),
      Event::token(&dl(1, 11), &sl(1, 2), "あいうえお"),
      Event::token(&dl(1, 26), &sl(1, 7), "]"),
      Event::end(&dl(1, 1), &sl(1, 8), "SS"),
    ],
    actual,
  );
}

#[test]
fn regex_scanner() {
  let scanner = RegExScanner::from_str(&dl(1, 1), "[あ-お]+").unwrap();
  assert_eq!("?[あ-お]+?", scanner.symbol());

  let scan = move |test: &str| -> Reaction {
    scanner
      .scan(&dl(1, 1), &mut MarkableReader::new(TEST_TARGET_NAME, test.into()))
      .unwrap()
  };
  assert_eq!(
    Reaction::Match {
      events: vec![Event::token(&dl(1, 1), &sl(1, 1), "あいうえお")]
    },
    scan("あいうえお"),
  );
  assert_eq!(
    Reaction::Match {
      events: vec![Event::token(&dl(1, 1), &sl(1, 1), "あい")]
    },
    scan("あい卯"),
  );
  assert_eq!(Reaction::Unmatch, scan(""),);
  assert_eq!(Reaction::Unmatch, scan("亜いう"),);

  // matches more than 256 characters
  let scanner = RegExScanner::from_str(&dl(1, 1), "[あ-お]+").unwrap();
  let test = (0..1000).map(|_| 'あ').collect::<String>();
  let mut r = MarkableReader::new(TEST_TARGET_NAME, test.as_str().into());
  let err = scanner.scan(&dl(1, 1), &mut r).unwrap_err();
  assert!(err.message.contains("Detect a match with more than 256 characters"));

  // make sure that RegExScanner can be used as a terminal-symbol for parser.
  let ebnf = "SS = ? aiueo ?";
  let mut config = GraphConfig::new();
  config.special_sequence_parser(SpecialSequenceParser::new(Box::new(
    |_, _| -> Box<dyn SpecialSequenceScanner> { Box::new(RegExScanner::from_str(&dl(1, 1), "[あ-お]+").unwrap()) },
  )));
  let graph = create_graph_with_config(ebnf, &config);
  let mut parser = Parser::new(&graph, "SS").unwrap();
  let mut input = MarkableReader::new(TEST_TARGET_NAME, "あいうえお".into());
  let actual = parser.parse(&mut input).unwrap();
  assert_eq_events(
    &vec![
      Event::begin(&dl(1, 1), &sl(1, 1), "SS"),
      Event::token(&dl(1, 6), &sl(1, 1), "あいうえお"),
      Event::end(&dl(1, 1), &sl(1, 6), "SS"),
    ],
    actual,
  );

  let mut parser = Parser::new(&graph, "SS").unwrap();
  let mut input = MarkableReader::new(TEST_TARGET_NAME, "壱弐参".into());
  assert!(parser.parse(&mut input).is_err());

  assert!(RegExScanner::from_str(&dl(1, 1), "\\xxx").is_err());
}

#[test]
fn char_scanner() {
  fn hex(c: char) -> bool {
    (c >= '0' && c <= '9') || (c >= 'a' && c <= 'f') || (c >= 'A' && c <= 'F')
  }

  let scanner = CharsScanner::with_max(Box::new(hex), 2);
  assert_match(&scanner, "", vec![Event::token(&dl(1, 1), &sl(1, 1), "")], &sl(1, 1));
  assert_match(&scanner, "a", vec![Event::token(&dl(1, 1), &sl(1, 1), "a")], &sl(1, 2));
  assert_match(
    &scanner,
    "aa",
    vec![Event::token(&dl(1, 1), &sl(1, 1), "aa")],
    &sl(1, 3),
  );
  assert_match(
    &scanner,
    "aaa",
    vec![Event::token(&dl(1, 1), &sl(1, 1), "aa")],
    &sl(1, 3),
  );

  let scanner = CharsScanner::with_range(Box::new(hex), 1, 2);
  assert_unmatch(&scanner, "");
  assert_match(&scanner, "a", vec![Event::token(&dl(1, 1), &sl(1, 1), "a")], &sl(1, 2));
  assert_match(
    &scanner,
    "aa",
    vec![Event::token(&dl(1, 1), &sl(1, 1), "aa")],
    &sl(1, 3),
  );
  assert_match(
    &scanner,
    "aaa",
    vec![Event::token(&dl(1, 1), &sl(1, 1), "aa")],
    &sl(1, 3),
  );
}

#[test]
fn forward() {
  #[derive(Debug)]
  struct Forward {
    label: String,
  }

  impl SpecialSequenceScanner for Forward {
    fn symbol(&self) -> String {
      format!("?{}?", self.label)
    }

    fn scan(&self, _: &Location, _: &mut dyn MarkableCharReader) -> crate::Result<Reaction> {
      Ok(Reaction::Forward {
        meta_identifier: self.label.clone(),
      })
    }
  }

  let mut config = GraphConfig::new();
  config.special_sequence_parser(SpecialSequenceParser::new(Box::new(|_, label| {
    Box::new(Forward {
      label: label.to_string(),
    })
  })));

  let syntax = "A = 'a'; FA = ?A?; FB = ?B?;";
  let mut cursor = Cursor::new(syntax.as_bytes());
  let syntax = Syntax::read_from_utf8(TEST_EBNF_NAME, &mut cursor, 1024).unwrap();
  let graph = LexGraph::compile(&syntax, &config);

  // when forwarding to a meta-identifier that exists
  let target = "a";
  let mut parser = Parser::new(&graph, "FA").unwrap();
  let mut r = MarkableReader::for_bytes(TEST_TARGET_NAME, target.as_bytes().to_vec(), "UTF-8").unwrap();
  let events = parser.parse(&mut r).unwrap();
  assert_eq_events(
    &vec![
      Event::begin(&dl(1, 10), &sl(1, 1), "FA"),
      Event::token(&dl(1, 5), &sl(1, 1), "a"),
      Event::end(&dl(1, 10), &sl(1, 2), "FA"),
    ],
    events,
  );

  // when forwarding to a non-existent meta-identifier
  let mut parser = Parser::new(&graph, "FB").unwrap();
  let mut r = MarkableReader::for_bytes(TEST_TARGET_NAME, target.as_bytes().to_vec(), "UTF-8").unwrap();
  let err = parser.parse(&mut r).unwrap_err();
  assert!(err
    .message
    .contains("The non-existent meta-identifier \"B\" was directed"));
}

fn assert_match(scanner: &dyn SpecialSequenceScanner, target: &str, expected: Vec<Event>, end: &Location) {
  let definition = Location::new(TEST_EBNF_NAME);
  let mut r = MarkableReader::for_bytes(TEST_TARGET_NAME, target.as_bytes().to_vec(), "utf-8").unwrap();
  if let Reaction::Match { events } = scanner.scan(&definition, &mut r).unwrap() {
    assert_eq!(expected, events);
    assert_eq!(end, &r.location());
  } else {
    panic!();
  }
}

fn assert_unmatch(scanner: &dyn SpecialSequenceScanner, target: &str) {
  let definition = Location::new(TEST_EBNF_NAME);
  let mut r = MarkableReader::for_bytes(TEST_TARGET_NAME, target.as_bytes().to_vec(), "utf-8").unwrap();
  let location = r.location();
  if let Reaction::Unmatch = scanner.scan(&definition, &mut r).unwrap() {
    assert_eq!(location, r.location());
  } else {
    panic!();
  }
}
