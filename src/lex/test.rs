use std::{
  fs::{remove_file, File},
  io::Cursor,
};

use regex::Regex;
use std::io::Write;

use crate::{io::test::ErrorRead, test::split_by};
use crate::{
  lex::{self, parse, parse_file, parse_str},
  Location,
};

use super::Lexer;

macro_rules! rule {
  ($id:expr, $($defs:expr), *) => {
    if let lex::SyntacticPrimary::MetaIdentifier(location, id) = $id.syntactic_primary {
      lex::SyntaxRule{
        location: location,
        meta_identifier: id.to_string(),
        definition_list: lex::DefinitionList(vec![$($defs), *]),
      }
    } else {
      panic!("Not a meta-identifier: {:?}", $id)
    }
  };
}

macro_rules! def {
  ($($terms:expr), *) => {
    lex::SingleDefinition{
      syntactic_terms: vec![$($terms), *]
    }
  };
}

macro_rules! term {
  ($factor:expr) => {
    lex::SyntacticTerm {
      syntactic_factor: $factor,
      syntactic_exception: None,
    }
  };
  ($factor:expr, $exception:expr) => {
    lex::SyntacticTerm {
      syntactic_factor: $factor,
      syntactic_exception: Some($exception),
    }
  };
}

macro_rules! factor {
  ($primary:expr) => {
    factor!($primary, 1)
  };
  ($primary:expr, $repetition:expr) => {
    lex::SyntacticFactor {
      repetition: $repetition,
      syntactic_primary: $primary,
    }
  };
}

macro_rules! sequence_primary {
  ($line:expr, $col:expr, $name:ident, $repetition:expr, $($defs:expr), +) => {
    factor!(lex::SyntacticPrimary::$name(
      location($line, $col),
      lex::DefinitionList(vec![$($defs), +]),
    ), $repetition)
  };
}

macro_rules! option {
  ($line:expr, $col:expr, $repetition:expr, $($defs:expr), *) => {
    sequence_primary!($line, $col, OptionalSequence, $repetition, $($defs), *)
  };
}

macro_rules! repeat {
  ($line:expr, $col:expr, $repetition:expr, $($defs:expr), *) => {
    sequence_primary!($line, $col, RepeatedSequence, $repetition, $($defs), *)
  };
}

macro_rules! grouped {
  ($line:expr, $col:expr, $repetition:expr, $($defs:expr), *) => {
    sequence_primary!($line, $col, GroupedSequence, $repetition, $($defs), *)
  };
}

macro_rules! id {
  ($line:expr, $col:expr, $id:expr) => {
    id!($line, $col, $id, 1)
  };
  ($line:expr, $col:expr, $id:expr, $repetition:expr) => {
    factor!(
      lex::SyntacticPrimary::MetaIdentifier(location($line, $col), $id.to_string()),
      $repetition
    )
  };
}

macro_rules! terminal {
  ($line:expr, $col:expr, $value:expr) => {
    terminal!($line, $col, $value, 1)
  };
  ($line:expr, $col:expr, $value:expr, $repetition:expr) => {
    factor!(
      lex::SyntacticPrimary::TerminalString(location($line, $col), $value.to_string()),
      $repetition
    )
  };
}

macro_rules! special {
  ($line:expr, $col:expr, $content:expr) => {
    special!($line, $col, $content, 1)
  };
  ($line:expr, $col:expr, $content:expr, $repetition:expr) => {
    factor!(
      lex::SyntacticPrimary::SpecialSequence(location($line, $col), $content.to_string()),
      $repetition
    )
  };
}

macro_rules! empty {
  ($line:expr, $col:expr) => {
    empty!($line, $col, 1)
  };
  ($line:expr, $col:expr, $repetition:expr) => {
    factor!(lex::SyntacticPrimary::EmptySequence(location($line, $col)), $repetition)
  };
}

#[test]
fn syntax_restored_from_file() {
  let mut temp_file = std::env::temp_dir();
  temp_file.push("ebnf_syntax_restored_from_file.tmp");
  let temp_file_name = temp_file.to_str().unwrap();

  let syntax = "a = 'A';";
  let expected = parse_str(temp_file_name, syntax).unwrap();

  let mut file = File::create(temp_file.clone()).unwrap();
  file.write_all(syntax.as_bytes()).unwrap();
  drop(file);
  let actual = parse_file(temp_file_name, "utf-8", 1024).unwrap();
  remove_file(temp_file).unwrap();

  assert_eq!(expected, actual);
}

#[test]
fn syntax_doesnt_ends_with_terminator() {
  assert_correct_syntax_rules(
    "a = 'A'",
    vec![rule!(id!(1, 1, "a"), def!(term!(terminal!(1, 5, "A"))))],
  );
  assert_correct_syntax_rules(
    "a = 'A'; b = 'B'",
    vec![
      rule!(id!(1, 1, "a"), def!(term!(terminal!(1, 5, "A")))),
      rule!(id!(1, 9, "b"), def!(term!(terminal!(1, 14, "B")))),
    ],
  );

  assert_eq!(parse_str("", "a = 'A';").unwrap(), parse_str("", "a = 'A'").unwrap(),);
  assert_eq!(
    parse_str("", "a = 'A';").unwrap(),
    parse("", &mut Cursor::new(b"a = 'A'"), "utf-8", 1024).unwrap(),
  );
}

#[test]
fn syntax_io_error_in_reading() {
  let mut r = ErrorRead::new(b"a = '", "something's wrong");
  let err = parse("path", &mut r, "us-ascii", 1024).unwrap_err();
  assert_eq!(Location::with_location("path", 1, 5), err.location);
  assert!(err.message.contains("something's wrong"));
}

/// In case any syntax-rules are not contained in definition.
#[test]
fn syntax_that_doesnt_contain_any_rules() {
  assert_correct_syntax_rules("", vec![]);
  assert_correct_syntax_rules(";", vec![]);
  assert_correct_syntax_rules(" ", vec![]);
  assert_correct_syntax_rules(" ; ; ", vec![]);
  assert_correct_syntax_rules(" (* *) \t\r\n; (* *)\t\r\n; (* *)\t\r\n(* *)", vec![]);
}

/// In case separator symbols are contained in comment or terminal-string.
#[test]
fn symbols_in_comments_and_terminal_string_dont_affect() {
  let symbols = ";|,!/:-=[]{}()\"*";
  assert_correct_syntax_rule(
    &format!("A(*{}*)='{}';(*{}*)", symbols, symbols, symbols),
    rule!(id!(1, 1, "A"), def!(term!(terminal!(1, 23, symbols)))),
  );
}

#[test]
fn single_rule_placed_on_multiple_lines() {
  assert_correct_syntax_rule(
    r#"
  multi line
  syntax rule =
    { abc } - xyz,
    [ xyz | abc ],
    100 * ("d", "e", "f")
  ;
"#,
    rule!(
      id!(2, 3, "multi line syntax rule"),
      def!(
        term!(repeat!(4, 5, 1, def!(term!(id!(4, 7, "abc")))), id!(4, 15, "xyz")),
        term!(option!(
          5,
          5,
          1,
          def!(term!(id!(5, 7, "xyz"))),
          def!(term!(id!(5, 13, "abc")))
        )),
        term!(grouped!(
          6,
          11,
          100,
          def!(
            term!(terminal!(6, 12, "d")),
            term!(terminal!(6, 17, "e")),
            term!(terminal!(6, 22, "f"))
          )
        ))
      )
    ),
  );
}

#[test]
fn meta_identifier() {
  // meta-identifier that has gap-separator-sequence.
  assert_correct_syntax_rule(
    "a b = 'ab';",
    rule!(id!(1, 1, "a b"), def!(term!(terminal!(1, 7, "ab")))),
  );
  assert_correct_syntax_rule(
    "  a \t\r\n  b = 'ab';",
    rule!(id!(1, 3, "a b"), def!(term!(terminal!(2, 7, "ab")))),
  );

  // All letters and digits can be used, nothing else.
  let valid = ('a'..='z').chain('A'..='Z').chain('0'..='9').collect::<String>();
  assert_correct_syntax_rule(
    &format!("{} = 'x';", valid),
    rule!(id!(1, 1, &valid), def!(term!(terminal!(1, valid.len() + 4, "x")))),
  );
  for invalid in ('\u{00}'..'\u{FF}').filter(|ch| !valid.contains(*ch) && !"\'\"= \t\r\n\u{b}\u{c}".contains(*ch)) {
    assert_incorrect_syntax_rules(&format!("a{}z = 'x';", invalid), 1, 2, ".*");
  }

  // meta-identifier cannot start with a digit.
  for digit in '0'..='9' {
    assert_incorrect_syntax_rules(
      &format!("{}abc = 'x';", digit),
      1,
      1,
      "meta-identifier expected, but integer appeared\\.",
    );
  }

  // meta-identifier doesn't exist.
  assert_incorrect_syntax_rules(
    "= 'ABC'",
    1,
    1,
    "meta-identifier expected, but defining-symbol appeared\\.",
  );

  // Not a meta-identifier.
  for token in vec!["'a'", "100", "[abc]", "{abc}", "(abc)", "|", ",", "?xxx?"].iter() {
    assert_incorrect_syntax_rules(
      &format!("{} = 'A'", token),
      1,
      1,
      "meta-identifier expected, but .+ appeared\\.",
    );
  }

  // Confirm that the specified buffer size limit is not exceeded.
  let mut lexer = Lexer::with_capacity("foo", 256, 1024);
  for i in 0..=u32::MAX {
    match lexer.push('a') {
      Ok(_) => (),
      Err(err) => {
        let re = Regex::new(".+ too long: 1024 \\+ 1 > 1024\\.").unwrap();
        assert_eq!(1024, i);
        assert!(re.is_match(&err.message));
        break;
      }
    }
  }
}

#[test]
fn terminal_string() {
  // It must contain at least one or more characters.
  assert_incorrect_syntax_rules(
    "a = ''",
    1,
    5,
    "The terminal-string must contain one or more terminal-characters\\.",
  );
}

#[test]
fn defining_symbol() {
  // defining-symbol dosn't exist.
  assert_incorrect_syntax_rules("abc", 1, 4, ".+ EOF appeared\\.");
  assert_incorrect_syntax_rules("abc;", 1, 4, ".+ terminator-symbol appeared\\.");
  assert_incorrect_syntax_rules("abc,", 1, 4, ".+ concatenate-symbol appeared\\.");

  // defining-symbol appears twice.
  assert_incorrect_syntax_rules("a = 'a' = 'A';", 1, 9, ".+, but defining-symbol appeared\\.");
}

#[test]
fn repetition_symbol() {
  // Representation for specifying the number of repetitions using repetition-symbol.
  assert_correct_syntax_rule(
    "a = 12 * 'A';",
    rule!(id!(1, 1, "a"), def!(term!(terminal!(1, 10, "A", 12)))),
  );

  // Group repetition.
  assert_correct_syntax_rule(
    "a = 12 * ('a' | 'A');",
    rule!(
      id!(1, 1, "a"),
      def!(term!(grouped!(
        1,
        10,
        12,
        def!(term!(terminal!(1, 11, "a"))),
        def!(term!(terminal!(1, 17, "A")))
      )))
    ),
  );

  // The absence of syntactic-primary is recognized as a addition of the empty-sequence.
  assert_correct_syntax_rule("a = 12 * ;", rule!(id!(1, 1, "a"), def!(term!(empty!(1, 10, 12)))));

  // Replacing integer and syntactic-primary.
  assert_incorrect_syntax_rules("a = 'A' * 12;", 1, 9, ".+, but repetition-symbol appeared\\.");

  // Specifying a numeric string that cannot be recognized as an integer.
  assert_incorrect_syntax_rules(
    "a = 3.14 * 'A';",
    1,
    6,
    "repetition-symbol '\\*' expected, but terminator-symbol appeared\\.",
  );
  assert_incorrect_syntax_rules(
    "a = 0x12 * 'A';",
    1,
    6,
    "repetition-symbol '\\*' expected, but meta-identifier appeared\\.",
  );
  assert_incorrect_syntax_rules(
    "a = 99999999999999999999999999999999999999999999999999999 * 'A';",
    1,
    5,
    "cannot convert the number of repetitions \"9+\" to 32-bit integer: .*",
  );
}

#[test]
fn except_symbol() {
  assert_correct_syntax_rule(
    "a = ('a' | 'b') - 'b';",
    rule!(
      id!(1, 1, "a"),
      def!(term!(
        grouped!(
          1,
          5,
          1,
          def!(term!(terminal!(1, 6, "a"))),
          def!(term!(terminal!(1, 12, "b")))
        ),
        terminal!(1, 19, "b")
      ))
    ),
  );

  // Representation with exceptions.
  assert_correct_syntax_rule(
    "ac = abc - 'b' | axc - 'x';",
    rule!(
      id!(1, 1, "ac"),
      def!(term!(id!(1, 6, "abc"), terminal!(1, 12, "b"))),
      def!(term!(id!(1, 18, "axc"), terminal!(1, 24, "x")))
    ),
  );

  // The absence of syntactic-exception is recognized as a addition of the empty-sequence.
  assert_correct_syntax_rule(
    "ac = abc - | axc - ;",
    rule!(
      id!(1, 1, "ac"),
      def!(term!(id!(1, 6, "abc"), empty!(1, 12))),
      def!(term!(id!(1, 14, "axc"), empty!(1, 20)))
    ),
  );
}

#[test]
fn concatenate_symbol() {
  // Representation of a sequence by concatenate-symbol.
  assert_correct_syntax_rule(
    "abc = 'a', 'b', 'c';",
    rule!(
      id!(1, 1, "abc"),
      def!(
        term!(terminal!(1, 7, "a")),
        term!(terminal!(1, 12, "b")),
        term!(terminal!(1, 17, "c"))
      )
    ),
  );

  // A sequence of concatenate-symbols is implicitly considered to have an empty-sequence.
  assert_correct_syntax_rule(
    "xxx = , , ;",
    rule!(
      id!(1, 1, "xxx"),
      def!(term!(empty!(1, 7)), term!(empty!(1, 9)), term!(empty!(1, 11)))
    ),
  );
}

#[test]
fn comment() {
  // Printable characters can be used.
  let valid = ('\u{20}'..'\u{7F}')
    .chain("\t\r\n\u{b}\u{c}".chars())
    .collect::<String>();
  assert_correct_syntax_rule(
    &format!("abc = 'a' (*{}*);", valid),
    rule!(id!(1, 1, "abc"), def!(term!(terminal!(1, 7, "a")))),
  );

  // Control-codes other than gap-symbol and 8-bit characters cannot be used.
  for invalid in ('\u{0}'..='\u{FF}').filter(|ch| !valid.contains(*ch)) {
    assert_incorrect_syntax_rules(
      &format!("abc = 'a' (*{}*);", invalid),
      1,
      13,
      "This comment contains a character '.+' \\(U\\+[0-9a-fA-F]{4}\\) that cannot be used as a comment\\.",
    );
  }
}

#[test]
fn special_sequence() {
  assert_correct_syntax_rule(
    "abc = ? control code ?;",
    rule!(id!(1, 1, "abc"), def!(term!(special!(1, 7, " control code ")))),
  );

  // Printable characters other than '?' can be used.
  let valid = ('\u{20}'..'\u{7F}').filter(|ch| *ch != '?').collect::<String>();
  assert_correct_syntax_rule(
    &format!("abc = ?{}?;", valid),
    rule!(id!(1, 1, "abc"), def!(term!(special!(1, 7, valid)))),
  );

  // Control-codes other than gap-symbol and 8-bit characters cannot be used.
  for invalid in ('\u{0}'..='\u{FF}').filter(|ch| !valid.contains(*ch) && !"?\t\r\n\u{b}\u{c}".contains(*ch)) {
    assert_incorrect_syntax_rules(
      &format!("abc = ?{}?;", invalid),
      1,
      7,
      "special-sequence contains a character '.+' that cannot be used\\.",
    );
  }
}

#[test]
fn parentheses_pair() {
  // Nested parentheses.
  assert_correct_syntax_rule(
    "a=('A'|'B'|('C','D'))",
    rule![
      id!(1, 1, "a"),
      def!(term!(grouped!(
        1,
        3,
        1,
        def!(term!(terminal!(1, 4, "A"))),
        def!(term!(terminal!(1, 8, "B"))),
        def!(term!(grouped!(
          1,
          12,
          1,
          def!(term!(terminal!(1, 13, "C")), term!(terminal!(1, 17, "D")))
        )))
      )))
    ],
  );

  // The end of the parentheses doesn't exist.
  assert_incorrect_syntax_rules("a=(*", 1, 3, "start-comment-symbol '\\(\\*' is not closed\\.");
  assert_incorrect_syntax_rules("a=[", 1, 3, "start-option-symbol '\\[' is not closed\\.");
  assert_incorrect_syntax_rules("a={", 1, 3, "start-repeat-symbol '\\{' is not closed\\.");
  assert_incorrect_syntax_rules("a=(/", 1, 3, "start-option-symbol '\\(/' is not closed\\.");
  assert_incorrect_syntax_rules("a=(:", 1, 3, "start-repeat-symbol '\\(:' is not closed\\.");
  assert_incorrect_syntax_rules("a=(", 1, 3, "start-group-symbol '\\(' is not closed\\.");

  // The start of the parentheses doesn't exist.
  assert_incorrect_syntax_rules("a=*)", 1, 3, "end-comment-symbol '\\*\\)' is not opened\\.");
  assert_incorrect_syntax_rules("a=]", 1, 3, ".+, but end-option-symbol appeared\\.");
  assert_incorrect_syntax_rules("a=}", 1, 3, ".+, but end-repeat-symbol appeared\\.");
  assert_incorrect_syntax_rules("a=/)", 1, 3, ".+, but end-option-symbol appeared\\.");
  assert_incorrect_syntax_rules("a=:)", 1, 3, ".+, but end-repeat-symbol appeared\\.");
  assert_incorrect_syntax_rules("a=)", 1, 3, ".+, but end-group-symbol appeared\\.");

  // Ambiguous parentheses correspondence.
  assert_incorrect_syntax_rules("a=(*);", 1, 3, "An ambiguous start/end-command-symbol: \\(\\*\\)");
  assert_incorrect_syntax_rules("a=(:);", 1, 3, "An ambiguous start/end-repeat-symbol: \\(:\\)");
  assert_incorrect_syntax_rules("a=(/);", 1, 3, "An ambiguous start/end-option-symbol: \\(/\\)");
}

#[test]
fn syntactic_term() {
  const REPEAT: u32 = 99;
  for (syntax, primary) in vec![
    (
      "['a','b'|'c']",
      option!(
        1,
        12,
        REPEAT,
        def!(term!(terminal!(1, 13, "a")), term!(terminal!(1, 17, "b"))),
        def!(term!(terminal!(1, 21, "c")))
      ),
    ),
    (
      "{'a','b'|'c'}",
      repeat!(
        1,
        12,
        REPEAT,
        def!(term!(terminal!(1, 13, "a")), term!(terminal!(1, 17, "b"))),
        def!(term!(terminal!(1, 21, "c")))
      ),
    ),
    (
      "['a','b'|'c']",
      option!(
        1,
        12,
        REPEAT,
        def!(term!(terminal!(1, 13, "a")), term!(terminal!(1, 17, "b"))),
        def!(term!(terminal!(1, 21, "c")))
      ),
    ),
    ("xyz", id!(1, 12, "xyz", REPEAT)),
    ("'xyz'", terminal!(1, 12, "xyz", REPEAT)),
    ("? control code ?", special!(1, 12, " control code ", REPEAT)),
    ("", empty!(1, 13, REPEAT)),
  ] {
    assert_correct_syntax_rule(
      &format!("abc = {} * {} - 'x';", REPEAT, syntax),
      rule!(
        id!(1, 1, "abc"),
        def!(term!(primary, terminal!(1, syntax.len() + 15, "x")))
      ),
    );
  }
}

#[test]
fn stringify() {
  // Format for display.
  let mut lexer = Lexer::new("foo");
  let rules = lexer
    .push_str("abc \td = abc | 'D'  (* XX *) | 3 * abc | xyz-, { abc - 'a' }, [ xyz | abc ], ('d', 'e', 'f'), ?XYZ?;")
    .unwrap();
  assert_eq!(1, rules.len());
  assert_eq!(
    "abc d=abc|'D'|3*abc|xyz-,{abc-'a'},[xyz|abc],('d','e','f'),?XYZ?;",
    format!("{}", rules.first().unwrap())
  );

  // Generate debug string for token
  assert_eq!(
    "(*ABC*)",
    lex::Token::Comment(location(1, 1), "ABC".to_string()).debug()
  );
  assert_eq!(
    "\" \\t\\r\\n\"",
    lex::Token::GapSeparatorSequence(location(1, 1), " \t\r\n".to_string()).debug()
  );
}

#[test]
fn syntax_rules() {
  assert_correct_syntax_rules(
    r#"abc = "A" | "B" | "C" ;
xyz = "X", "Y", "Z";
abc  d = abc | "D"  (* The meta-identifier contains gap separators *);
(* *) abcxyz (* *) = (* *) abc (* *) | (* *) xyz (* *) ;
repeat = { abc }, [ xyz | abc ], ("d", "e", "f") ;
"#,
    vec![
      rule!(
        id!(1, 1, "abc"),
        def![term!(terminal!(1, 7, "A"))],
        def![term!(terminal!(1, 13, "B"))],
        def![term!(terminal!(1, 19, "C"))]
      ),
      rule!(
        id!(2, 1, "xyz"),
        def![
          term!(terminal!(2, 7, "X")),
          term!(terminal!(2, 12, "Y")),
          term!(terminal!(2, 17, "Z"))
        ]
      ),
      rule!(
        id!(3, 1, "abc d"),
        def![term!(id!(3, 10, "abc"))],
        def![term!(terminal!(3, 16, "D"))]
      ),
      rule!(
        id!(4, 6, "abcxyz"),
        def!(term!(id!(4, 28, "abc"))),
        def!(term!(id!(4, 46, "xyz")))
      ),
      rule!(
        id!(5, 1, "repeat"),
        def!(
          term!(repeat!(5, 10, 1, def!(term!(id!(5, 12, "abc"))))),
          term!(option!(
            5,
            19,
            1,
            def!(term!(id!(5, 21, "xyz"))),
            def!(term!(id!(5, 27, "abc")))
          )),
          term!(grouped!(
            5,
            34,
            1,
            def!(
              term!(terminal!(5, 35, "d")),
              term!(terminal!(5, 40, "e")),
              term!(terminal!(5, 45, "f"))
            )
          ))
        )
      ),
    ],
  );

  assert_correct_syntax_rule(
    r#"abc = "A" | "B" | "C" ;"#,
    rule!(
      id!(1, 1, "abc"),
      def![term!(terminal!(1, 7, "A"))],
      def![term!(terminal!(1, 13, "B"))],
      def![term!(terminal!(1, 19, "C"))]
    ),
  );
}

fn assert_correct_syntax_rules(syntax_rules: &str, expected: Vec<lex::SyntaxRule>) {
  fn assert_eq_rules(expected: &Vec<lex::SyntaxRule>, rules: &Vec<lex::SyntaxRule>) {
    assert_eq!(expected.len(), rules.len(), "The number of rules is not match.");
    for (i, (expected, actual)) in expected.iter().zip(rules.iter()).enumerate() {
      assert_eq!(
        expected.meta_identifier, actual.meta_identifier,
        "[{}] meta-identifier is not match.",
        i
      );
      assert_eq_definition_list(i, &expected.definition_list, &actual.definition_list);
    }
  }

  let mut lexer = Lexer::new(FILE_NAME);
  for i in 1..=syntax_rules.len() {
    lexer.reset();
    let mut rules = Vec::<lex::SyntaxRule>::new();
    for chunk in split_by(syntax_rules, i).iter() {
      rules.append(&mut lexer.push_str(chunk).unwrap());
    }
    if let Some(rule) = lexer.flush().unwrap() {
      rules.push(rule);
    }
    assert_eq_rules(&expected, &rules);
  }

  // Checks for push operations, one character at a time.
  lexer.reset();
  let mut rules = Vec::<lex::SyntaxRule>::new();
  for ch in syntax_rules.chars() {
    if let Some(token) = lexer.push(ch).unwrap() {
      rules.push(token);
    }
  }
  if let Some(rule) = lexer.flush().unwrap() {
    rules.push(rule);
  }
  assert_eq_rules(&expected, &rules);
}

fn assert_correct_syntax_rule(syntax_rule: &str, expected: lex::SyntaxRule) {
  assert_correct_syntax_rules(syntax_rule, vec![expected]);
}

fn assert_eq_definition_list(i: usize, expected: &lex::DefinitionList, actual: &lex::DefinitionList) {
  if expected.0.len() != actual.0.len() {
    assert_eq!(
      expected.0, actual.0,
      "[{}] The length of definition-list are not match.",
      i
    );
  }
  for (j, (expected, actual)) in expected.0.iter().zip(actual.0.iter()).enumerate() {
    assert_eq!(
      expected.syntactic_terms.len(),
      actual.syntactic_terms.len(),
      "[{},{}] The length of syntactic-term is not match.",
      i,
      j
    );
    for (k, (expected, actual)) in expected
      .syntactic_terms
      .iter()
      .zip(actual.syntactic_terms.iter())
      .enumerate()
    {
      assert_eq!(
        expected.syntactic_exception, actual.syntactic_exception,
        "[{},{},{}] syntactic-exception is not match.",
        i, j, k
      );
      let expected = &expected.syntactic_factor;
      let actual = &actual.syntactic_factor;
      assert_eq!(
        expected.repetition, actual.repetition,
        "[{},{},{}] repetition is not match.",
        i, j, k
      );
      match (&expected.syntactic_primary, &actual.syntactic_primary) {
        (lex::SyntacticPrimary::OptionalSequence(l1, dl1), lex::SyntacticPrimary::OptionalSequence(l2, dl2)) => {
          assert_eq!(l1, l2, "[{},{},{}] location is not match.", i, j, k);
          assert_eq_definition_list(i, dl1, dl2);
        }
        (lex::SyntacticPrimary::RepeatedSequence(l1, dl1), lex::SyntacticPrimary::RepeatedSequence(l2, dl2)) => {
          assert_eq!(l1, l2, "[{},{},{}] location is not match.", i, j, k);
          assert_eq_definition_list(i, dl1, dl2);
        }
        (lex::SyntacticPrimary::GroupedSequence(l1, dl1), lex::SyntacticPrimary::GroupedSequence(l2, dl2)) => {
          assert_eq!(l1, l2, "[{},{},{}] location is not match.", i, j, k);
          assert_eq_definition_list(i, dl1, dl2);
        }
        _ => assert_eq!(expected, actual, "[{},{},{}] syntactic-term is not match.", i, j, k),
      }
    }
  }
}

fn assert_incorrect_syntax_rules(syntax_rules: &str, line: usize, col: usize, pattern: &str) {
  let re = Regex::new(pattern).unwrap();
  let assert_error = |err: crate::Error| {
    assert_eq!(
      line as u64, err.location.lines,
      "Line number doesn't match: {}",
      err.message
    );
    assert_eq!(
      col as u64, err.location.columns,
      "Column number doesn't match: {}",
      err.message
    );
    if !re.is_match(&err.message) {
      assert_eq!(pattern, err.message);
    }
  };
  let mut lexer = Lexer::new(FILE_NAME);
  for i in 1..=syntax_rules.len() {
    lexer.reset();
    for chunk in split_by(syntax_rules, i).iter() {
      match lexer.push_str(chunk) {
        Ok(_) => (),
        Err(error) => {
          assert_error(error);
          return;
        }
      }
    }
    assert_error(
      lexer
        .flush()
        .expect_err(&format!("No error was encountered: {:?}", syntax_rules)),
    );
  }
}

const FILE_NAME: &str = "C:\\like Windows File System\\with space\\path.ebnf";

fn location(lines: usize, columns: usize) -> Location {
  Location {
    name: FILE_NAME.to_string(),
    lines: lines as u64,
    columns: columns as u64,
  }
}
