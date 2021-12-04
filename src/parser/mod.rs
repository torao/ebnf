pub mod graph;
mod machine;

#[cfg(test)]
pub mod test;

use std::fmt::Debug;

use regex::Regex;

use crate::{
  io::MarkableCharReader,
  parser::{graph::LexGraph, machine::LexMachine},
  Error, Location, Result,
};

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Event {
  Token {
    definition: Location,
    location: Location,
    token: String,
  },
  Begin {
    definition: Location,
    location: Location,
    label: String,
  },
  End {
    definition: Location,
    location: Location,
    label: String,
  },
}

impl Event {
  pub fn token(definition: &Location, location: &Location, token: impl Into<String>) -> Self {
    Self::Token {
      definition: definition.clone(),
      location: location.clone(),
      token: token.into(),
    }
  }

  pub fn begin(definition: &Location, location: &Location, label: impl Into<String>) -> Self {
    Self::Begin {
      definition: definition.clone(),
      location: location.clone(),
      label: label.into(),
    }
  }

  pub fn end(definition: &Location, location: &Location, label: impl Into<String>) -> Self {
    Self::End {
      definition: definition.clone(),
      location: location.clone(),
      label: label.into(),
    }
  }
}

pub struct Parser<'a> {
  machine: LexMachine<'a>,
}

impl<'a> Parser<'a> {
  pub fn new(graph: &'a LexGraph, meta_identifier: &str) -> Option<Self> {
    LexMachine::new(graph, meta_identifier).map(|machine| Parser { machine })
  }

  pub fn name(&self) -> &str {
    self.machine.id()
  }

  pub fn parse(&mut self, r: &mut dyn MarkableCharReader) -> Result<Vec<Event>> {
    self.machine.parse(r)
  }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Reaction {
  /// `Match` indicates that the token was restored by matching the specified number of characters
  /// at the beginning of the `buffer`. If there is no token to be restored, the `token` will be
  /// `None`.
  Match { events: Vec<Event> },

  /// `Unmatch` indicates that the beginning of the specified buffer wasn't matched.
  Unmatch,

  /// `Forward` indicates that the matching process is forwarded to the specified meta-identifier.
  /// When the matching of the meta-identifier is completed, it returns and continues the
  /// processing of this special sequence.
  Forward { meta_identifier: String },
}

/// `SpecialSequenceParser` is a factory for generating a [`SpecialSequenceScanner`] when the
/// Parser encounters a special-sequence.
/// By using SS, applications can implement their own extensions for special-sequence.
///
pub struct SpecialSequenceParser(Box<dyn Fn(&Location, &str) -> Box<dyn SpecialSequenceScanner>>);

impl SpecialSequenceParser {
  pub fn new(f: Box<dyn Fn(&Location, &str) -> Box<dyn SpecialSequenceScanner>>) -> Self {
    Self(f)
  }
}

impl Default for SpecialSequenceParser {
  fn default() -> Self {
    Self::new(Box::new(
      |_: &Location, content: &str| -> Box<dyn SpecialSequenceScanner> {
        Box::new(DefaultScanner {
          content: content.to_string(),
        })
      },
    ))
  }
}

#[derive(Debug)]
struct DefaultScanner {
  content: String,
}

impl SpecialSequenceScanner for DefaultScanner {
  fn symbol(&self) -> String {
    format!("?{}?", self.content)
  }

  fn scan(&self, _definition: &Location, _r: &mut dyn MarkableCharReader) -> Result<Reaction> {
    Ok(Reaction::Match { events: Vec::new() })
  }
}

pub trait SpecialSequenceScanner {
  fn symbol(&self) -> String;
  fn scan(&self, definition: &Location, r: &mut dyn MarkableCharReader) -> Result<Reaction>;
}

/// A scanner that can specify predication and repetition in character units.
pub struct CharsScanner {
  predicator: Box<dyn Fn(char) -> bool>,
  min: Option<usize>,
  max: Option<usize>,
}

impl CharsScanner {
  pub fn new(predicator: Box<dyn Fn(char) -> bool>, min: Option<usize>, max: Option<usize>) -> Self {
    Self { predicator, min, max }
  }
  pub fn with_one_of(predicator: Box<dyn Fn(char) -> bool>) -> Self {
    Self::with_range(predicator, 1, 1)
  }
  pub fn with_one_or_more(predicator: Box<dyn Fn(char) -> bool>) -> Self {
    Self::with_min(predicator, 1)
  }
  pub fn with_zero_or_more(predicator: Box<dyn Fn(char) -> bool>) -> Self {
    Self::new(predicator, None, None)
  }
  pub fn with_min(predicator: Box<dyn Fn(char) -> bool>, min: usize) -> Self {
    Self::new(predicator, Some(min), None)
  }
  pub fn with_max(predicator: Box<dyn Fn(char) -> bool>, max: usize) -> Self {
    Self::new(predicator, None, Some(max))
  }
  pub fn with_range(predicator: Box<dyn Fn(char) -> bool>, min: usize, max: usize) -> Self {
    Self::new(predicator, Some(min), Some(max))
  }
}

impl SpecialSequenceScanner for CharsScanner {
  fn symbol(&self) -> String {
    String::from("?chars?")
  }
  fn scan(&self, definition: &Location, r: &mut dyn MarkableCharReader) -> Result<Reaction> {
    let mark = r.mark()?;
    let location = r.location().clone();
    let mut buffer = Vec::new();
    while self.max.map(|max| buffer.len() < max).unwrap_or(true) {
      let m2 = r.mark()?;
      if let Some(ch) = r.read()? {
        if !(self.predicator)(ch) {
          r.reset_to_mark(m2)?;
          break;
        }
        r.unmark(m2)?;
        buffer.push(ch);
      } else {
        break;
      }
    }

    if self.min.map(|min| buffer.len() < min).unwrap_or(false) {
      r.reset_to_mark(mark)?;
      Ok(Reaction::Unmatch)
    } else {
      let token = buffer.iter().collect::<String>();
      Ok(Reaction::Match {
        events: vec![Event::token(definition, &location, token)],
      })
    }
  }
}

/// based on [regex crate](https://docs.rs/regex/).
pub struct RegExScanner {
  regex: Regex,
}

impl RegExScanner {
  pub fn new(regex: Regex) -> Self {
    Self { regex }
  }
  pub fn from_str(definition: &Location, re: &str) -> Result<Self> {
    match Regex::new(re) {
      Ok(regex) => Ok(Self::new(regex)),
      Err(err) => Err(Error::new(definition, format!("Malformed regular expression: {}", err))),
    }
  }
}

impl SpecialSequenceScanner for RegExScanner {
  fn symbol(&self) -> String {
    format!("?{}?", self.regex.to_string())
  }
  fn scan(&self, definition: &Location, r: &mut dyn MarkableCharReader) -> Result<Reaction> {
    let max_length = 256;
    let location = r.location().clone();
    let token = r.peek(max_length + 1)?;
    match self.regex.find(&token) {
      Some(m) if m.start() == 0 => {
        let token = m.as_str().chars().collect::<Vec<_>>();
        if token.len() > max_length {
          Err(Error::new(
            &r.location(),
            format!(
              "Detect a match with more than {} characters. Regular Expression matches are limited to {} characters.",
              max_length, max_length,
            ),
          ))
        } else {
          r.skip(token.len())?;
          Ok(Reaction::Match {
            events: vec![Event::token(definition, &location, token.iter().collect::<String>())],
          })
        }
      }
      _ => Ok(Reaction::Unmatch),
    }
  }
}

fn parallel_notation(mut words: Vec<String>, conj: &str) -> String {
  match words.len() {
    0 => String::from(""),
    1 => words.remove(0),
    2 => format!("{} {} {}", words[0], conj, words[1]),
    _ => {
      let last = words.remove(words.len() - 1);
      format!("{}, {} {}", words.join(", "), conj, last)
    }
  }
}
