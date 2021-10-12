use crate::{
  lex::tokenizer::{Token, Tokenizer},
  Location, Result,
};
use regex::Regex;

#[test]
fn simple_single_syntax_rule() {
  // Standard representation.
  assert_correct_syntax_rules(
    "ABC = 'xyz' * 123, [option] | {repeat} (*comment*), (group)-;",
    vec![
      Token::MetaIdentifier(location(1, 1), "ABC".to_string()),
      Token::GapSeparatorSequence(location(1, 4), " ".to_string()),
      Token::DefiningSymbol(location(1, 5)),
      Token::GapSeparatorSequence(location(1, 6), " ".to_string()),
      Token::TerminalString(location(1, 7), "xyz".to_string(), '\''),
      Token::GapSeparatorSequence(location(1, 12), " ".to_string()),
      Token::RepetitionSymbol(location(1, 13)),
      Token::GapSeparatorSequence(location(1, 14), " ".to_string()),
      Token::Integer(location(1, 15), "123".to_string()),
      Token::ConcatenateSymbol(location(1, 18)),
      Token::GapSeparatorSequence(location(1, 19), " ".to_string()),
      Token::StartOptionSymbol(location(1, 20), "["),
      Token::MetaIdentifier(location(1, 21), "option".to_string()),
      Token::EndOptionSymbol(location(1, 27), "]"),
      Token::GapSeparatorSequence(location(1, 28), " ".to_string()),
      Token::DefinitionSeparatorSymbol(location(1, 29), '|'),
      Token::GapSeparatorSequence(location(1, 30), " ".to_string()),
      Token::StartRepeatSymbol(location(1, 31), "{"),
      Token::MetaIdentifier(location(1, 32), "repeat".to_string()),
      Token::EndRepeatSymbol(location(1, 38), "}"),
      Token::GapSeparatorSequence(location(1, 39), " ".to_string()),
      Token::Comment(location(1, 40), "comment".to_string()),
      Token::ConcatenateSymbol(location(1, 51)),
      Token::GapSeparatorSequence(location(1, 52), " ".to_string()),
      Token::StartGroupSymbol(location(1, 53)),
      Token::MetaIdentifier(location(1, 54), "group".to_string()),
      Token::EndGroupSymbol(location(1, 59)),
      Token::ExceptSymbol(location(1, 60)),
      Token::TerminatorSymbol(location(1, 61), ';'),
      Token::EOF(location(1, 62)),
    ],
  );

  // Alternative representation.
  assert_correct_syntax_rules(
    "ABC='a'/'b'!'c',(/option/),(:repeat:).",
    vec![
      Token::MetaIdentifier(location(1, 1), "ABC".to_string()),
      Token::DefiningSymbol(location(1, 4)),
      Token::TerminalString(location(1, 5), "a".to_string(), '\''),
      Token::DefinitionSeparatorSymbol(location(1, 8), '/'),
      Token::TerminalString(location(1, 9), "b".to_string(), '\''),
      Token::DefinitionSeparatorSymbol(location(1, 12), '!'),
      Token::TerminalString(location(1, 13), "c".to_string(), '\''),
      Token::ConcatenateSymbol(location(1, 16)),
      Token::StartOptionSymbol(location(1, 17), "(/"),
      Token::MetaIdentifier(location(1, 19), "option".to_string()),
      Token::EndOptionSymbol(location(1, 25), "/)"),
      Token::ConcatenateSymbol(location(1, 27)),
      Token::StartRepeatSymbol(location(1, 28), "(:"),
      Token::MetaIdentifier(location(1, 30), "repeat".to_string()),
      Token::EndRepeatSymbol(location(1, 36), ":)"),
      Token::TerminatorSymbol(location(1, 38), '.'),
      Token::EOF(location(1, 39)),
    ],
  );
}

#[test]
fn terminal_string() {
  // Both double-quotes and single-quotes can be used.
  assert_correct_syntax_rules(
    "A=\"a\";B=\'b\';",
    vec![
      Token::MetaIdentifier(location(1, 1), "A".to_string()),
      Token::DefiningSymbol(location(1, 2)),
      Token::TerminalString(location(1, 3), "a".to_string(), '\"'),
      Token::TerminatorSymbol(location(1, 6), ';'),
      Token::MetaIdentifier(location(1, 7), "B".to_string()),
      Token::DefiningSymbol(location(1, 8)),
      Token::TerminalString(location(1, 9), "b".to_string(), '\''),
      Token::TerminatorSymbol(location(1, 12), ';'),
      Token::EOF(location(1, 13)),
    ],
  );

  for quote in "\"\'".chars() {
    // All characters available for terminal-string.
    let expected = (' '..0x7F as char).filter(|c| *c != quote).collect::<String>();
    assert_correct_syntax_rules(
      format!("{}{}{}", quote, expected, quote).as_str(),
      vec![Token::TerminalString(location(1, 1), expected, quote), Token::EOF(location(1, 97))],
    );

    // All characters unavailable for terminal-string.
    for ch in (0x00 as char..' ').chain(0x7F as char..=0xFF as char) {
      assert_incorrect_syntax_rules(
        format!("{}{}{}", quote, ch, quote).as_str(),
        1,
        1,
        "terminal-string contains a character '[^']+' that cannot be used\\.",
      );
    }

    // Some Unicode characters that cannot be used in terminal-string.
    for ch in "にほんご中文한국".chars() {
      assert_incorrect_syntax_rules(
        format!("{}{}{}", quote, ch, quote).as_str(),
        1,
        1,
        "terminal-string contains a character '[^']+' that cannot be used\\.",
      )
    }

    // Unclosed terminal-string.
    assert_incorrect_syntax_rules(
      format!("{}ABC", quote).as_str(),
      1,
      1,
      format!("terminal-string is not closed with {}\\.", regex::escape(&format!("{:?}", quote)))
        .as_str(),
    );
  }
}

#[test]
fn special_sequence() {
  // Simple special-sequence.
  assert_correct_syntax_rules(
    "SPECIAL=? Here is special sequence. ?",
    vec![
      Token::MetaIdentifier(location(1, 1), "SPECIAL".to_string()),
      Token::DefiningSymbol(location(1, 8)),
      Token::SpecialSequence(location(1, 9), " Here is special sequence. ".to_string()),
      Token::EOF(location(1, 38)),
    ],
  );

  // Empty special-sequence.
  assert_correct_syntax_rules(
    "??",
    vec![Token::SpecialSequence(location(1, 1), "".to_string()), Token::EOF(location(1, 3))],
  );

  // 7-bit chharacters between 0x20-0x7E are available.
  let sequence = (' '..0x7F as char).filter(|c| *c != '?').collect::<String>();
  let sequence_length = sequence.len();
  let special = format!("?{}?", sequence);
  assert_correct_syntax_rules(
    &special,
    vec![
      Token::SpecialSequence(location(1, 1), sequence),
      Token::EOF(location(1, sequence_length + 3)),
    ],
  );

  // Control codes smaller than 0x20 and 8-bit characters larger than or equal 0x7F cannot be used.
  for invalid_char in (0 as char..' ').chain(0x7F as char..0x80 as char).filter(|ch| {
    *ch != '\t' && *ch != '\n' && *ch != '\r' && *ch != 0x0B as char && *ch != 0x0C as char
  }) {
    let special = format!("?{}?", invalid_char);
    assert_incorrect_syntax_rules(&special, 1, 1, "special-sequence contains a character.*");
  }

  // In case the special-sequence hasn't been completed.
  assert_incorrect_syntax_rules(
    "? not completed",
    1,
    1,
    "special-sequence is not closed with '\\?'\\.",
  )
}

#[test]
fn comment() {
  // Simple comment.
  assert_correct_syntax_rules(
    "COMMENT=(* This is comment. *)",
    vec![
      Token::MetaIdentifier(location(1, 1), "COMMENT".to_string()),
      Token::DefiningSymbol(location(1, 8)),
      Token::Comment(location(1, 9), " This is comment. ".to_string()),
      Token::EOF(location(1, 31)),
    ],
  );

  // Nested comment.
  assert_correct_syntax_rules(
    "(* This (* is (* comment *). *) *)",
    vec![
      Token::Comment(location(1, 1), " This (* is (* comment *). *) ".to_string()),
      Token::EOF(location(1, 35)),
    ],
  );

  // In case the comment isn't closed.
  assert_incorrect_syntax_rules(
    "(* This (* isn't *) closed comment.",
    1,
    1,
    "start-comment-symbol '\\(\\*' is not closed\\.",
  );

  // In case the comment isn't opened.
  assert_incorrect_syntax_rules(
    "(* This (* isn't *) opened comment. *) *)",
    1,
    40,
    "end-comment-symbol '\\*\\)' is not opened\\.",
  );

  // An ambiguous start/end-comment-symbol.
  assert_incorrect_syntax_rules("(*)", 1, 1, "An ambiguous start/end-command-symbol: \\(\\*\\)")
}

fn assert_correct_syntax_rules(syntax_rules: &str, expected: Vec<Token>) {
  tokenize_in_various_split(syntax_rules, expected).unwrap();
}

fn assert_incorrect_syntax_rules(syntax_rules: &str, line: usize, column: usize, msg_regex: &str) {
  let err = tokenize_in_various_split(syntax_rules, vec![]).unwrap_err();
  let re = Regex::new(msg_regex).unwrap();
  assert_eq!(
    line as u64, err.location.lines,
    "line is not match: {} != {}",
    line, err.location.lines
  );
  assert_eq!(
    column as u64, err.location.columns,
    "column is not match: {} != {}",
    column, err.location.columns
  );
  assert!(re.is_match(&err.message), "message doesn't match: {} != {}", msg_regex, err.message);
}

fn tokenize_in_various_split(syntax_rules: &str, expected: Vec<Token>) -> Result<()> {
  let mut tk = Tokenizer::new(FILE_NAME);
  let syntax_rules = syntax_rules.chars().collect::<Vec<char>>();
  for step in 1..=syntax_rules.len() {
    let mut actual = Vec::new();
    let div = syntax_rules.len() / step + if syntax_rules.len() % step != 0 { 1 } else { 0 };
    for i in 0..div {
      let begin = i * step;
      let end = std::cmp::min((i + 1) * step, syntax_rules.len());
      let chunk = syntax_rules[begin..end].iter().collect::<String>();
      let mut tokens = tk.push_str(&chunk)?;
      actual.append(&mut tokens);
    }
    actual.append(&mut tk.flush()?);

    for (e, a) in expected.iter().zip(actual.iter()) {
      assert_eq!(e, a);
    }
    if expected.len() != actual.len() {
      panic!("length not match: {} != {}; {:?}", expected.len(), actual.len(), actual);
    }

    tk.reset();
  }
  Ok(())
}

const FILE_NAME: &str = "C:\\like Windows File System\\with space\\path.ebnf";

fn location(lines: usize, columns: usize) -> Location {
  Location { name: FILE_NAME.to_string(), lines: lines as u64, columns: columns as u64 }
}
