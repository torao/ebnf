use crate::{
  parser::{
    graph::{GraphConfig, LexGraph},
    test::{assert_eq_events, create_graph_with_config, dl, sl, TEST_EBNF_NAME, TEST_TARGET_NAME},
    Event, Parser, Reaction, RegExScanner, SpecialSequenceParser, SpecialSequenceScanner,
  },
  Location, Result, Syntax,
};

#[test]
fn default() {
  let default = SpecialSequenceParser::default();
  let scanner = default.0(&dl(1, 1), "default scanner");
  assert_eq!("?default scanner?", scanner.symbol());
  assert_eq!(
    Ok(Reaction::Match { length: 0, token: None }),
    scanner.scan(&sl(1, 1), &['\0'; 0], true)
  )
}

#[test]
fn non_ascii_characters() {
  fn is_non_ascii(ch: char) -> bool {
    ch as u32 >= 0x80
  }
  #[derive(Debug)]
  struct NonAsciiCharacters {}
  impl SpecialSequenceScanner for NonAsciiCharacters {
    fn symbol(&self) -> String {
      String::from("? non-ascii characters ?")
    }
    fn scan(&self, _location: &Location, buffer: &[char], flush: bool) -> Result<Reaction> {
      if buffer.len() == 0 {
        Ok(if flush { Reaction::Unmatch } else { Reaction::NeedMore })
      } else if !is_non_ascii(buffer[0]) {
        Ok(Reaction::Unmatch)
      } else {
        for i in 1..buffer.len() {
          if !is_non_ascii(buffer[i]) {
            return Ok(Reaction::Match {
              length: i,
              token: Some(buffer[..i].iter().collect::<String>()),
            });
          }
        }
        Ok(if flush {
          Reaction::Match {
            length: buffer.len(),
            token: Some(buffer.iter().collect::<String>()),
          }
        } else {
          Reaction::NeedMore
        })
      }
    }
  }

  // parse and build a special-sequence syntax
  let ebnf = "SS = '[', ? non-ascii ?, ']'";
  let syntax = Syntax::read_from_str(TEST_EBNF_NAME, ebnf, 0).unwrap();

  // build instruction graph with non-ascii special-sequence scanner
  let mut config = GraphConfig::new();
  config.special_sequence_parser(SpecialSequenceParser::new(Box::new(
    |_, _| -> Box<dyn SpecialSequenceScanner> { Box::new(NonAsciiCharacters {}) },
  )));
  let graph = LexGraph::compile(&syntax, &config);

  // parse a text with non-ascii characters
  let mut parser = Parser::new(&graph, "SS", 0, TEST_TARGET_NAME).unwrap();
  let mut expected = Vec::new();
  expected.append(&mut parser.push_str("[あいうえお]").unwrap());
  expected.append(&mut parser.flush().unwrap());

  assert_eq_events(
    &vec![
      Event::begin(dl(1, 1), sl(1, 1), "SS"),
      Event::token(dl(1, 6), sl(1, 1), "["),
      Event::token(dl(1, 11), sl(1, 2), "あいうえお"),
      Event::token(dl(1, 26), sl(1, 7), "]"),
      Event::end(dl(1, 1), sl(1, 1), "SS"),
    ],
    expected,
  );
}

#[test]
fn regex_scanner() {
  let scanner = RegExScanner::from_str(&dl(1, 1), "[あ-お]+").unwrap();
  assert_eq!("?[あ-お]+?", scanner.symbol());
  assert_eq!(
    Reaction::Match {
      length: 5,
      token: Some(String::from("あいうえお"))
    },
    scanner
      .scan(&sl(1, 1), &"あいうえお".chars().collect::<Vec<_>>(), true)
      .unwrap(),
  );
  assert_eq!(
    Reaction::Match {
      length: 2,
      token: Some(String::from("あい"))
    },
    scanner
      .scan(&sl(1, 1), &"あい卯".chars().collect::<Vec<_>>(), true)
      .unwrap(),
  );
  assert_eq!(
    Reaction::Unmatch,
    scanner.scan(&sl(1, 1), &"".chars().collect::<Vec<_>>(), true).unwrap(),
  );
  assert_eq!(
    Reaction::Unmatch,
    scanner
      .scan(&sl(1, 1), &"亜いう".chars().collect::<Vec<_>>(), true)
      .unwrap(),
  );

  // make sure that RegExScanner can be used as a terminal-symbol for parser.
  let ebnf = "SS = ? aiueo ?";
  let mut config = GraphConfig::new();
  config.special_sequence_parser(SpecialSequenceParser::new(Box::new(
    |_, _| -> Box<dyn SpecialSequenceScanner> { Box::new(RegExScanner::from_str(&dl(1, 1), "[あ-お]+").unwrap()) },
  )));
  let graph = create_graph_with_config(ebnf, &config);
  let mut parser = Parser::new(&graph, "SS", 0, TEST_TARGET_NAME).unwrap();
  let mut expected = Vec::new();
  expected.append(&mut parser.push_str("あいうえお").unwrap());
  expected.append(&mut parser.flush().unwrap());
  assert_eq_events(
    &vec![
      Event::begin(dl(1, 1), sl(1, 1), "SS"),
      Event::token(dl(1, 6), sl(1, 1), "あいうえお"),
      Event::end(dl(1, 1), sl(1, 1), "SS"),
    ],
    expected,
  );

  let mut parser = Parser::new(&graph, "SS", 0, TEST_TARGET_NAME).unwrap();
  assert!(parser.push_str("壱弐参").is_err());

  let ebnf = "SS = '<<', ? aiueo ?, '>>'";
  let graph = create_graph_with_config(ebnf, &config);
  let text = "<<あいうえお>>".chars().collect::<Vec<_>>();
  for chunk_size in 1..text.len() {
    let mut parser = Parser::new(&graph, "SS", 0, TEST_TARGET_NAME).unwrap();
    let mut expected = Vec::new();
    for chunk in text.chunks(chunk_size) {
      expected.append(&mut parser.push_chars(chunk).unwrap());
    }
    expected.append(&mut parser.flush().unwrap());
    assert_eq_events(
      &vec![
        Event::begin(dl(1, 1), sl(1, 1), "SS"),
        Event::token(dl(1, 6), sl(1, 1), "<<"),
        Event::token(dl(1, 12), sl(1, 3), "あいうえお"),
        Event::token(dl(1, 23), sl(1, 8), ">>"),
        Event::end(dl(1, 1), sl(1, 1), "SS"),
      ],
      expected,
    );
  }

  let text = "<<あいう壱弐参>>".chars().collect::<Vec<_>>();
  for chunk_size in 1..text.len() {
    let mut parser = Parser::new(&graph, "SS", 0, TEST_TARGET_NAME).unwrap();
    let error = text
      .chunks(chunk_size)
      .map(|chunk| parser.push_chars(chunk))
      .find(|r| r.is_err())
      .or_else(|| {
        let r = parser.flush();
        if r.is_err() {
          Some(r)
        } else {
          None
        }
      })
      .map(|e| e.unwrap_err());
    assert!(error.is_some());
  }

  let mut parser = Parser::new(&graph, "SS", 0, TEST_TARGET_NAME).unwrap();
  parser.push_str("<<あいう").unwrap();
  assert!(parser.push_str("絵お").is_err());

  assert!(RegExScanner::from_str(&dl(1, 1), "\\xxx").is_err());
}
