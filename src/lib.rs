//!
//! The `ebnf` library provides an application-specific programming language or DSL parser defined
//! in the **Extended BNF** syntax of the [ISO/IEC 14977:1996](https://www.cl.cam.ac.uk/~mgk25/iso-14977.pdf)
//! specification.
//!
//! # Examples
//!
//! If you just want to refer to the syntactic structure of EBNF, use the [`lex`] module. You can use [`lex::parse()`]
//! or [`lex::parse_str()`] to restore the syntax definition.
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
//! # Specification
//!
//! ## Meta Identififer Naming
//!
//! ## Definition Priority
//!
//! In a definition-list (i.e. OR match), if a stream matches more than one definition, the first definition is applied.
//!
//! ```ebnf
//! open parentheses = '#' | '#(' | '/';
//! ```
//!
use embed_doc_image::embed_doc_image;
use std::{
  collections::HashMap,
  fmt::{Display, Formatter},
};

// pub mod graph;
pub mod io;
pub mod lex;
pub mod parser;
mod validity;

#[cfg(test)]
pub mod test;

/// `Result` in the `ebnf` library represents processing result that it can be either a result with arbitrary type `T`
/// or an [`Error`].
///
pub type Result<T> = std::result::Result<T, Error>;

/// `Error` represents an error related to lexical analysis and syntax used by the `ebnf` library. This contains the
/// location information and message of the syntax in which the error occurred.
///
#[derive(Debug, PartialEq, Eq)]
pub struct Error {
  pub location: Location,
  pub message: String,
}

impl Error {
  /// Constructs `Error` with the location and the error message.
  ///
  fn new(location: &Location, message: impl Into<String>) -> Error {
    Error {
      location: location.clone(),
      message: message.into(),
    }
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
/// ![ebnf::Syntax][Syntax]
///
#[embed_doc_image("Syntax", "assets/Syntax.png")]
#[derive(Debug)]
pub struct Syntax {
  canonical_names: HashMap<String, String>,
  rules: HashMap<String, usize>,
  syntax_rules: Vec<lex::SyntaxRule>,
}

impl Syntax {
  /// Creates a syntax from a list of specified syntax rules.
  ///
  /// # Returns
  ///
  /// Syntax with the specified syntax-rule. Or Error if the prior validation fails.
  ///
  pub fn new(syntax_rules: Vec<lex::SyntaxRule>) -> Result<Self> {
    validity::new_syntax(syntax_rules)
  }

  pub fn canonical_name(&self, meta_identifier: &str) -> Option<&str> {
    let id = keyed_meta_identifier(meta_identifier);
    self.canonical_names.get(&id).map(|s| s as &str)
  }

  pub fn rules(&self) -> impl Iterator<Item = &lex::SyntaxRule> {
    self.syntax_rules.iter()
  }

  /// Reads EBNF syntax from the specified input stream and builds a [`Syntax`].
  ///
  /// ![ebnf::Syntax::read_from()][Syntax::read_from]
  ///
  /// ```rust
  /// use std::io::Cursor;
  /// use ebnf::Syntax;
  ///
  /// let mut cursor = Cursor::new("abc = 'A', ('B' | 'C'); xyz = 'X', 'Y', 'Z';");
  /// let syntax = Syntax::from("/your/path/to/file.ebnf", &mut cursor, "utf-8", 0).unwrap();
  /// assert_eq!(2, syntax.syntax_rules.len());
  /// assert_eq!("abc", syntax.syntax_rules[0].meta_identifier);
  /// assert_eq!("xyz", syntax.syntax_rules[1].meta_identifier);
  /// ```
  ///
  /// See [lex::Lexer] for a more low-level and efficient operation.
  ///
  /// Any EBNF syntax that needs to buffer more than `max_buffer_size` will result in an error. This
  /// limit is important so as not to cause a critical resource craving when reading streams of
  /// unknown length.
  ///
  /// # Parameters
  ///
  /// * `name` - The human-readable name of the stream (e.g., file name or URL). This string is
  ///   used to indicate its location in case of errors.
  /// * `r` - Input stream from which the EBNF syntax is read.
  /// * `encoding` - The encoding of characters to be read from the input stream `r`, such as
  ///   `"utf-8"` or `"Shift_JIS"`. For encoding name that can be specified, see
  ///   <https://encoding.spec.whatwg.org/>.
  /// * `max_buffer_size` - Maximum size of the internal buffer. If 0, the buffer size isn't limited.
  ///
  #[embed_doc_image("Syntax::read_from", "assets/Syntax-read_from.png")]
  pub fn read_from(name: &str, r: &mut dyn std::io::Read, encoding: &str, max_buffer_size: usize) -> Result<Self> {
    Self::new(lex::parse(name, r, encoding, max_buffer_size)?)
  }

  pub fn read_from_utf8(name: &str, r: &mut dyn std::io::Read, max_buffer_size: usize) -> Result<Self> {
    Self::read_from(name, r, "utf-8", max_buffer_size)
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
    let id = keyed_meta_identifier(meta_identifier);
    self.rules.get(&id).map(|p| *p).map(|i| &self.syntax_rules[i])
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

/// `Location` holds the current reading position and identifies the location where the error or
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
    Location {
      name: name.to_string(),
      lines,
      columns,
    }
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

/// The `Display` implementation for [`Location`] generates a string in `"$name($lines,$columns)"`
/// format.
///
/// ```rust
/// use ebnf::Location;
///
/// let location = Location::with_location("/your/path/to/foo.ebnf", 53, 8);
/// assert_eq!("/your/path/to/foo.ebnf(53,8)", format!("{}", location));
/// ```
///
impl Display for Location {
  fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
    write!(f, "{}({},{})", self.name, self.lines, self.columns)
  }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct AST {
  location: Location,
  name: Option<String>,
  node: Node,
}

impl AST {
  pub fn is_leaf(&self) -> bool {
    match self.node {
      Node::Atom { .. } => true,
      Node::Complex { .. } => false,
    }
  }
  pub fn is_node(&self) -> bool {
    !self.is_leaf()
  }
  pub fn location(&self) -> &Location {
    &self.location
  }
  pub fn name(&self) -> Option<&str> {
    match &self.name {
      Some(s) => Some(s),
      None => None,
    }
  }
  pub fn token(&self) -> String {
    match &self.node {
      Node::Atom { token } => token.clone(),
      Node::Complex { children } => {
        let mut buffer = String::with_capacity(64);
        for node in children.iter() {
          buffer.push_str(&node.token());
        }
        buffer
      }
    }
  }
}

impl AST {
  pub fn with_token(location: Location, token: &str) -> Self {
    Self {
      location,
      name: None,
      node: Node::Atom {
        token: token.to_string(),
      },
    }
  }
  pub fn with_name(location: Location, name: &str, token: &str) -> Self {
    Self {
      location,
      name: Some(name.to_string()),
      node: Node::Atom {
        token: token.to_string(),
      },
    }
  }
  pub fn with_children(location: Location, children: Vec<AST>) -> Self {
    Self {
      location,
      name: None,
      node: Node::Complex { children },
    }
  }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Node {
  Atom { token: String },
  Complex { children: Vec<AST> },
}

/// `canonical_meta_identifier()` converts the specified meta-identifier string to its formal
/// name in the definition.
/// This function removes leading and trailing whitespace in the string and converts one or more
/// whitespace into a single space.
///
/// ```
/// use ebnf::canonical_meta_identifier;
///
/// assert_eq!("quick brown fox", canonical_meta_identifier(" quick\tbrown\n\tfox"));
/// ```
///
pub fn normalized_meta_identifier(meta_identifier: &str) -> String {
  let mut buffer = Vec::with_capacity(meta_identifier.len());
  let mut whitespace_right_before = true;
  for ch in meta_identifier.chars() {
    if lex::is_gap_separator_char(ch) {
      if !whitespace_right_before {
        buffer.push(' ');
        whitespace_right_before = true;
      }
    } else {
      buffer.push(ch);
      whitespace_right_before = false;
    }
  }
  if whitespace_right_before && !buffer.is_empty() {
    buffer.truncate(buffer.len() - 1);
  }
  buffer.iter().collect::<String>()
}

/// `keyed_meta_identifier()` converts the specified meta-identifier string into a key for search.
/// This function removes *all* whitespace in the string.
///
/// The transformed meta-identifier can be used as a key for [`HashMap`].
///
/// ```
/// use ebnf::keyed_meta_identifier;
///
/// assert_eq!("quickbrownfox", keyed_meta_identifier(" quick\tbrown\n\tfox"));
/// ```
///
pub fn keyed_meta_identifier(meta_identifier: &str) -> String {
  meta_identifier
    .chars()
    .filter(|ch| !lex::is_gap_separator_char(*ch))
    .collect::<String>()
}
