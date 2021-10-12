//!
//! The `ebnf` library provides an application-specific programming language or DSL parser defined
//! in the **Extended BNF** syntax of the [ISO/IEC 14977:1996](https://www.cl.cam.ac.uk/~mgk25/iso-14977.pdf)
//! specification.
//!
//! # Examples
//!
//! If you just want to refer to the syntactic structure of EBNF, use the [`lex`] module.
//! You can use [`lex::parse()`] or [`lex::parse_str()`] to restore the syntax definition.
//!
//!
//! ```
//! use std::io::Cursor;
//! use ebnf::lex;
//!
//! let name = "";
//! let syntax = "abc = 'A', ('B' | 'C'); xyz = 'X', 'Y', 'Z';";
//! let rules = lex::parse_str(name, syntax).unwrap();
//! assert_eq!(2, rules.len());
//! assert_eq!("abc", rules[0].meta_identifier);
//! assert_eq!("xyz", rules[1].meta_identifier);
//! ```
//!
use std::fmt::{Display, Formatter};

pub mod io;
pub mod lex;
pub mod parser;
mod validity;

/// `Result` in the `ebnf` library represents processing result that it can be either a result with
/// arbitrary type `T` or an [`Error`].
///
pub type Result<T> = std::result::Result<T, Error>;

/// `Error` represents an error related to lexical analysis and syntax used by the `ebnf` library.
/// This contains the location information and message of the syntax in which the error occurred.
///
#[derive(Debug, PartialEq, Eq)]
pub struct Error {
  pub location: Location,
  pub message: String,
}

impl Error {
  /// Constructs `Error` with the location and the error message.
  ///
  fn new(location: &Location, message: String) -> Error {
    Error { location: location.clone(), message }
  }
}

/// The `Display` for [Error] generates a string in `"$name($lines,$columns) $message"` format.
///
impl Display for Error {
  fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
    write!(f, "{} {}", self.location, self.message)
  }
}

impl std::error::Error for Error {}

/// `Syntax` represents the syntactic structure of Extended BNF.
///
#[derive(Debug)]
pub struct Syntax {
  pub syntax_rules: Vec<lex::SyntaxRule>,
}

impl Syntax {
  /// Creates a syntax from a list of specified syntax rules.
  ///
  /// # Returns
  ///
  /// Syntax with the specified syntax-rule. Or Error if the prior validation fails.
  ///
  pub fn new(syntax_rules: Vec<lex::SyntaxRule>) -> Result<Self> {
    let syntax = Syntax { syntax_rules };
    validity::verify_construct(&syntax)?;
    Ok(syntax)
  }

  /// ```
  /// use std::io::Cursor;
  /// use ebnf::Syntax;
  ///
  /// let mut cursor = Cursor::new("abc = 'A', ('B' | 'C'); xyz = 'X', 'Y', 'Z';");
  /// let syntax = Syntax::from("/your/path/file.ebnf", &mut cursor, "utf-8").unwrap();
  /// assert_eq!(2, syntax.syntax_rules.len());
  /// assert_eq!("abc", syntax.syntax_rules[0].meta_identifier);
  /// assert_eq!("xyz", syntax.syntax_rules[1].meta_identifier);
  /// ```
  ///
  /// See [lex::Lexer] for a more low-level and efficient operation.
  ///
  pub fn from(name: &str, r: &mut dyn std::io::Read, _encoding: &str) -> Result<Self> {
    let mut buffer = String::with_capacity(4 * 1024);
    match r.read_to_string(&mut buffer) {
      Ok(_) => (),
      Err(err) => {
        let mut location = Location::new(name);
        location.push_str(&buffer);
        return Err(Error::new(
          &location,
          format!("An error occurred reading the syntax: {}", err),
        ));
      }
    }

    let mut rules = Vec::with_capacity(16);
    let mut lexer = lex::Lexer::new(name);
    rules.append(&mut lexer.push_str(&buffer)?);
    if let Some(remaining) = lexer.flush()? {
      rules.push(remaining);
    }
    Self::new(rules)
  }

  /// `get_syntax_rule()` returns the syntax-rule corresponding to the specified meta-identifier.
  /// Comparison of meta-identifiers doesn't take into account gap-separator-sequence.
  ///
  /// # Parameters
  ///
  /// * `meta_identifier` - meta-identifier of the syntax-rule to be referenced.
  ///
  /// # Return
  ///
  /// The syntax-rule corresponding to the meta-identifier. If the corresponding syntax-rule is not
  /// defined, `None` will be returned.
  ///
  pub fn get_syntax_rule(&self, meta_identifier: &str) -> Option<&lex::SyntaxRule> {
    for i in 0..self.syntax_rules.len() {
      if Self::same_meta_identifier(&self.syntax_rules[i].meta_identifier, meta_identifier) {
        return Some(&self.syntax_rules[i]);
      }
    }
    None
  }

  fn same_meta_identifier(mi1: &str, mi2: &str) -> bool {
    let mut it1 = mi1.chars().filter(|ch| !ch.is_whitespace());
    let mut it2 = mi2.chars().filter(|ch| !ch.is_whitespace());
    loop {
      let ch1 = it1.next();
      let ch2 = it2.next();
      if ch1 != ch2 {
        return false;
      }
      if ch1.is_none() && ch2.is_none() {
        break;
      }
    }
    true
  }
}

impl Display for Syntax {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    for rule in self.syntax_rules.iter() {
      rule.fmt(f)?;
    }
    Ok(())
  }
}

/// `Location` holds the current reding position and identifies the location where the error or
/// warning occurred.
///
#[derive(Eq, PartialEq, Debug, Clone)]
pub struct Location {
  /// The string indicating the location of the EBNF file being parsed by [Lexer](lex::Lexer). This
  /// value is specified by [Lexer::new()](lex::Lexer::new()), and is intended to be set as a local
  /// file name, URL, or else.
  pub name: String,
  /// The line number, with the first line being 1. If zero, the location is unknown.
  pub lines: u64,
  /// The column number, with the first column being 1. If zero, the location is unknown.
  pub columns: u64,
}

impl Location {
  /// Constructs a `Location` at initial position (1, 1) with the specified name.
  pub fn new(name: &str) -> Self {
    Self::with_location(name, 1, 1)
  }
  /// Constructs a `Location` with the specified name, lines, and columns.
  pub fn with_location(name: &str, lines: u64, columns: u64) -> Self {
    Location { name: name.to_string(), lines, columns }
  }
  fn reset(&mut self) {
    self.lines = 1;
    self.columns = 1;
  }
  fn push_str(&mut self, s: &str) {
    for ch in s.chars() {
      self.push(ch);
    }
  }
  fn push_chars(&mut self, s: &[char]) {
    for ch in s {
      self.push(*ch);
    }
  }
  fn push(&mut self, ch: char) {
    if ch == '\n' {
      self.lines += 1;
      self.columns = 1;
    } else {
      self.columns += 1;
    }
  }
}

/// The `Display` implementation for [Location] generates a string in `"$name($lines,$columns)"`
/// format.
///
/// ```
/// use ebnf::Location;
///
/// let location = Location::new("/your/path/to/foo.ebnf");
/// assert_eq!("/your/path/to/foo.ebnf(1,1)", format!("{}", location));
/// ```
///
impl Display for Location {
  fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
    write!(f, "{}({},{})", self.name, self.lines, self.columns)
  }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Node {
  location: Location,
  name: Option<String>,
  token: String,
  children: Vec<Node>,
}

impl Node {
  pub fn with_token(location: Location, token: &str) -> Node {
    Node { location, name: None, token: token.to_string(), children: Vec::new() }
  }
  pub fn with_name(location: Location, name: &str, token: &str) -> Node {
    Node { location, name: Some(name.to_string()), token: token.to_string(), children: Vec::new() }
  }
  pub fn with_children(location: Location, children: Vec<Node>) -> Node {
    Node { location, name: None, token: String::new(), children }
  }
}
