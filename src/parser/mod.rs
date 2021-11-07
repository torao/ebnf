mod graph;
mod machine;

#[cfg(test)]
mod test;

use crate::{Error, Location, Result};

use self::{
  graph::{LexGraph, Prospect},
  machine::LexMachine,
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
}

impl<'a> Parser<'a> {
  pub fn new(graph: &'a LexGraph, meta_identifier: &str, max_buffer_size: usize, name: &str) -> Option<Self> {
    LexMachine::new(graph, meta_identifier).map(|machine| Parser {
      machine,
      buffer: Vec::new(),
      max_buffer_size,
      location: Location::new(name),
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
    let (consumed, tokens) = self.machine.proceed(&self.location, &self.buffer, flush)?;
    let consumed = self.buffer.drain(0..consumed);
    self.location.push_chars(&consumed.collect::<Vec<_>>());
    Ok(tokens)
  }
}

pub enum Ack {
  NeedMore,
  Match { length: usize, event: Option<Event> },
  Unmatch,
}

pub trait ParseContext {}

pub struct SpecialSequenceParser(Box<dyn Fn(&Location, &str) -> Box<dyn SpecialSequenceScanner>>);

impl SpecialSequenceParser {
  pub fn new(f: Box<dyn Fn(&Location, &str) -> Box<dyn SpecialSequenceScanner>>) -> Self {
    Self(f)
  }
}

impl Default for SpecialSequenceParser {
  fn default() -> Self {
    Self::new(Box::new(|_: &Location, _: &str| -> Box<dyn SpecialSequenceScanner> {
      Box::new(Ignore::Continue)
    }))
  }
}

pub trait SpecialSequenceScanner: std::fmt::Debug {
  fn symbol(&self) -> String;
  fn scan(&self, context: &mut dyn ParseContext, buffer: &[char], flush: bool) -> Result<Ack>;
}

#[derive(Debug)]
pub enum Ignore {
  Continue,
  Reject,
}

impl SpecialSequenceScanner for Ignore {
  fn symbol(&self) -> String {
    match self {
      Ignore::Continue => "?continue?".to_string(),
      Ignore::Reject => "?reject?".to_string(),
    }
  }

  fn scan(&self, _context: &mut dyn ParseContext, _buffer: &[char], _flush: bool) -> Result<Ack> {
    Ok(match self {
      Ignore::Continue => Ack::Match { length: 0, event: None },
      Ignore::Reject => Ack::Unmatch {},
    })
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
