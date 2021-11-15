pub mod graph;
mod machine;

#[cfg(test)]
mod test;

use std::fmt::{Debug, Formatter};

use regex::Regex;

use crate::{
  parser::{
    graph::{LexGraph, Prospect},
    machine::LexMachine,
  },
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
  pub fn token(definition: Location, location: Location, token: impl Into<String>) -> Event {
    Event::Token {
      definition: definition.clone(),
      location: location.clone(),
      token: token.into(),
    }
  }

  pub fn begin(definition: Location, location: Location, label: impl Into<String>) -> Event {
    Event::Begin {
      definition: definition.clone(),
      location: location.clone(),
      label: label.into(),
    }
  }

  pub fn end(definition: Location, location: Location, label: impl Into<String>) -> Event {
    Event::End {
      definition: definition.clone(),
      location: location.clone(),
      label: label.into(),
    }
  }
}

pub trait ScanContext {
  fn graph<'a>(&'a self) -> &'a LexGraph;
  fn call_by_identifier(
    &mut self,
    meta_identifier: &str,
    location: &Location,
    buffer: &[char],
    flush: bool,
  ) -> Result<Prospect>;
  fn call_by_index(&mut self, index: usize, location: &Location, buffer: &[char], flush: bool) -> Result<Prospect>;
}

pub struct Parser<'a> {
  machine: LexMachine<'a>,

  buffer: Vec<char>,
  max_buffer_size: usize,

  /// Location of the `buffer` head.
  location: Location,

  filter: EventFilter,
}

impl<'a> Parser<'a> {
  pub fn new(graph: &'a LexGraph, meta_identifier: &str, max_buffer_size: usize, name: &str) -> Option<Self> {
    let max_buffer_size = if max_buffer_size == 0 { 1024 } else { max_buffer_size };
    LexMachine::new(graph, meta_identifier).map(|machine| Parser {
      machine,
      buffer: Vec::new(),
      max_buffer_size,
      location: Location::new(name),
      filter: EventFilter::new(),
    })
  }

  pub fn name(&self) -> &str {
    self.machine.id()
  }

  pub fn push(&mut self, ch: char) -> Result<Vec<Event>> {
    let mut buffer = ['\0'; 1];
    buffer[0] = ch;
    self.push_chars(&buffer)
  }

  pub fn push_str(&mut self, s: &str) -> Result<Vec<Event>> {
    self.push_chars(&s.chars().collect::<Vec<char>>())
  }

  pub fn push_chars(&mut self, chars: &[char]) -> Result<Vec<Event>> {
    if self.buffer.len() + chars.len() > self.max_buffer_size {
      return Err(Error::new(
        &self.location,
        format!(
          "The token could not be recognized after reaching the max buffer size of {} chars.",
          self.max_buffer_size
        ),
      ));
    }

    self.buffer.append(&mut chars.to_vec());
    self.proceed(false)
  }

  pub fn flush(&mut self) -> Result<Vec<Event>> {
    self.proceed(true)
  }

  fn proceed(&mut self, flush: bool) -> Result<Vec<Event>> {
    let (consumed, events) = self.machine.proceed(&self.location, &self.buffer, flush)?;
    let consumed = self.buffer.drain(0..consumed);
    self.location.push_chars(&consumed.collect::<Vec<_>>());
    Ok(self.filter.push(events, flush))
  }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Reaction {
  /// `NeedMore` indicates that more characters need to arrive to determine if it's a match or
  /// a unmatch, and shouldn't be returned when flushed.
  NeedMore,

  /// `Match` indicates that the token was restored by matching the specified number of characters
  /// at the beginning of the `buffer`. If there is no token to be restored, the `token` will be
  /// `None`.
  Match { length: usize, token: Option<String> },

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

  fn scan(&self, _: &Location, _: &[char], _: bool) -> Result<Reaction> {
    Ok(Reaction::Match { length: 0, token: None })
  }
}

pub trait SpecialSequenceScanner: std::fmt::Debug {
  fn symbol(&self) -> String;
  fn scan(&self, location: &Location, buffer: &[char], flush: bool) -> Result<Reaction>;
}

/// A scanner that can specify predication and repetition in character units.
pub struct CharsScanner {
  predicator: Box<dyn Fn(char) -> bool>,
  min: Option<usize>,
  max: Option<usize>,
}

impl CharsScanner {
  pub fn new(predicator: Box<dyn Fn(char) -> bool>, min: Option<usize>, max: Option<usize>) -> Self {
    CharsScanner { predicator, min, max }
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

impl Debug for CharsScanner {
  fn fmt(&self, f: &mut Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
    f.debug_struct("CharsScanner")
      .field("min", &self.min)
      .field("max", &self.max)
      .finish()
  }
}

impl SpecialSequenceScanner for CharsScanner {
  fn symbol(&self) -> String {
    String::from("?chars?")
  }
  fn scan(&self, _location: &Location, buffer: &[char], flush: bool) -> Result<Reaction> {
    let max = if let Some(max) = self.max {
      std::cmp::min(buffer.len(), max)
    } else {
      buffer.len()
    };
    let mut i = 0;
    while i < max {
      if !(self.predicator)(buffer[i]) {
        break;
      }
      i += 1;
    }

    let in_range = self.min.map(|min| i >= min).unwrap_or(true) && self.max.map(|max| i <= max).unwrap_or(true);
    if in_range && (i < buffer.len() || (i == buffer.len() && flush)) {
      Ok(Reaction::Match {
        length: i,
        token: Some(buffer[..i].iter().collect::<String>()),
      })
    } else if i == buffer.len() && !flush {
      Ok(Reaction::NeedMore)
    } else {
      Ok(Reaction::Unmatch)
    }
  }
}

/// based on [regex crate](https://docs.rs/regex/).
#[derive(Debug)]
pub struct RegExScanner {
  definition: Location,
  regex: Regex,
}

impl RegExScanner {
  pub fn new(definition: &Location, regex: Regex) -> Self {
    Self {
      definition: definition.clone(),
      regex,
    }
  }
  pub fn from_str(definition: &Location, re: &str) -> Result<Self> {
    match Regex::new(re) {
      Ok(regex) => Ok(Self::new(definition, regex)),
      Err(err) => Err(Error::new(definition, format!("Malformed regular expression: {}", err))),
    }
  }
}

impl SpecialSequenceScanner for RegExScanner {
  fn symbol(&self) -> String {
    format!("?{}?", self.regex.to_string())
  }
  fn scan(&self, _location: &Location, buffer: &[char], flush: bool) -> Result<Reaction> {
    let text = buffer.iter().collect::<String>();
    if let Some(matcher) = self.regex.find(&text) {
      if matcher.start() > 0 {
        Ok(Reaction::Unmatch)
      } else if matcher.end() == text.len() {
        Ok(if flush {
          Reaction::Match {
            length: buffer.len(),
            token: Some(text),
          }
        } else {
          Reaction::NeedMore
        })
      } else {
        let length = matcher.end();
        let token = &text[..length];
        Ok(Reaction::Match {
          length: token.chars().count(),
          token: Some(token.to_string()),
        })
      }
    } else {
      Ok(Reaction::Unmatch)
    }
  }
}

/// A filter function to remove non-terminal symbols from the event sequence that appear in the
/// parsing process. However, even if the entire syntax tree is empty, the non-terminal symbol
/// of the root is returned without deletion.
///
struct EventFilter {
  buffer: Vec<Event>,
  first_event_returned: bool,
}

impl EventFilter {
  pub fn new() -> Self {
    Self {
      buffer: Vec::new(),
      first_event_returned: false,
    }
  }

  pub fn push(&mut self, mut events: Vec<Event>, flush: bool) -> Vec<Event> {
    self.buffer.append(&mut events);

    // The first event of the parser, the start event of the meta-identifier, is passed through
    // without being removed. This preserves the top-level `Event::Begin` and `Event::End` even if
    // it's empty.
    if !self.first_event_returned && !self.buffer.is_empty() {
      events.push(self.buffer.remove(0));
      self.first_event_returned = true;
    }

    // If `Event::Begin` and `Event::End` pair are consecutive, remove them.
    let mut i = 0;
    while i + 1 < self.buffer.len() {
      if let Event::Begin {
        definition: def1,
        location: loc1,
        label: lab1,
      } = &self.buffer[i]
      {
        if let Event::End {
          definition: def2,
          location: loc2,
          label: lab2,
        } = &self.buffer[i + 1]
        {
          if def1 == def2 && loc1 == loc2 && lab1 == lab2 {
            self.buffer.drain(i..i + 2);
            if i != 0 {
              i -= 1;
            }
            continue;
          }
        }
      }
      i += 1;
    }

    if flush {
      events.append(&mut self.buffer);
    } else {
      let last_token = self.buffer.iter().enumerate().rfind(|(_, e)| match *e {
        Event::Token { .. } => true,
        _ => false,
      });
      if let Some((mut i, _)) = last_token {
        i += 1;
        while i < self.buffer.len() {
          if let Event::End { .. } = &self.buffer[i] {
            i += 1;
          } else {
            break;
          }
        }
        events.append(&mut self.buffer.drain(0..i).collect::<Vec<Event>>());
      }
    }

    events
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
