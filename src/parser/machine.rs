use crate::{
  io::{BufferedCharReader, MarkableCharReader, MarkableReader},
  parser::{
    graph::{LexGraph, Prospect, Scanner, Step},
    Event, Reaction,
  },
  Error, Location, Result,
};

/// Turing machine
pub struct LexMachine<'a> {
  graph: &'a LexGraph,
  meta_identifier: String,
  entry_address: usize,
}

impl<'a> LexMachine<'a> {
  pub fn new(graph: &'a LexGraph, meta_identifier: &str) -> Option<Self> {
    graph
      .index_of_label(&format!("${}", meta_identifier))
      .map(|entry_address| LexMachine {
        graph,
        meta_identifier: graph.canonical_name(meta_identifier).unwrap().to_string(),
        entry_address,
      })
  }

  pub fn id(&'a self) -> &'a str {
    &self.meta_identifier
  }

  pub fn parse(&mut self, r: &mut dyn MarkableCharReader) -> Result<Vec<Event>> {
    let mut events = Vec::new();
    match self.parse_to_subroutine_end(self.entry_address, r, &mut events)? {
      Prospect::Proceed if r.is_eof()? => {
        remove_empty_begin_end_pair(&mut events);
        Ok(events)
      }
      Prospect::Proceed => Err(self.err_expected_but_stream_not(None, r)),
      Prospect::NotThisWay(err) => Err(err),
    }
  }

  fn parse_to_subroutine_end(
    &mut self,
    addr: usize,
    r: &mut dyn MarkableCharReader,
    events: &mut Vec<Event>,
  ) -> Result<Prospect> {
    let mut next = Some(addr);
    while let Some(addr) = next {
      let instr = self.graph.instruction(addr).unwrap();
      match &instr.step {
        Step::Repetition { min, max, subroutine } => {
          let mut temp = Vec::new();
          let mut i = 0;
          while i < *max {
            let location = r.location();
            let mark = r.mark()?;
            match self.parse_to_subroutine_end(*subroutine, r, &mut temp)? {
              Prospect::Proceed => (),
              prospect @ Prospect::NotThisWay(..) => {
                if i < *min {
                  return Ok(prospect);
                }
                r.reset_to_mark(mark)?;
                break;
              }
            }
            if *max == u32::MAX && r.location() == location {
              return Err(Error::new(
                &location,
                format!("Livelock: reading didn't proceed in repetation"),
              ));
            }
            i += 1;
          }
          events.append(&mut temp);
        }
        Step::Or { subroutines } => {
          let mut errors = Vec::new();
          for i in 0..subroutines.len() {
            let mark = r.mark()?;
            let mut temp = Vec::new();
            match self.parse_to_subroutine_end(subroutines[i], r, &mut temp)? {
              Prospect::Proceed => {
                events.append(&mut temp);
                break;
              }
              Prospect::NotThisWay(err) => {
                r.reset_to_mark(mark)?;
                errors.push(err);
              }
            }
          }

          if errors.len() == subroutines.len() {
            // Priority is given to the error with the deepest match.
            let mut err = errors.pop().unwrap();
            while !errors.is_empty() {
              let other = errors.pop().unwrap();
              if err.location < other.location {
                err = other;
              }
            }
            return Ok(Prospect::NotThisWay(if err.location == r.location() {
              self.err_expected_but_stream_not(next, r)
            } else {
              err
            }));
          }
        }
        Step::Alias { meta_identifier } => {
          let address = self.graph.index_of_label(meta_identifier).expect(&format!(
            "meta-identifier {:?} is not defined (this must be checked during Syntax construction).",
            meta_identifier
          ));
          let meta_identifier = self.graph.canonical_name(meta_identifier).unwrap();
          let definition = &instr.definition.clone();
          let mut temp = Vec::new();
          temp.push(Event::begin(definition, &r.location(), meta_identifier));
          if let p @ Prospect::NotThisWay(..) = self.parse_to_subroutine_end(address, r, &mut temp)? {
            return Ok(p);
          }
          temp.push(Event::end(definition, &r.location(), meta_identifier));
          events.append(&mut temp);
        }
        Step::Scan { scanner, .. } => {
          if let p @ Prospect::NotThisWay(..) = scanner.scan(self, addr, r, events)? {
            return Ok(p);
          }
        }
      }
      next = instr.next;
    }
    Ok(Prospect::Proceed)
  }

  fn err_expected_but_stream_not(&self, current: Option<usize>, r: &mut dyn MarkableCharReader) -> Error {
    let location = r.location();
    let expected = current
      .map(|i| self.graph.instruction(i).map(|n| n.symbol.to_string()))
      .flatten()
      .unwrap_or(String::from("EOF"));
    match Self::stream_prefix_to_string(r) {
      Ok(actual) => Self::err_expected_but_not(&location, &expected, &actual),
      Err(error) => error,
    }
  }

  pub fn err_expected_but_not(location: &Location, expected: &str, actual: &str) -> Error {
    Self::err_syntax(location, &format!("{} expected, but {} appeared.", expected, actual))
  }

  fn err_syntax(location: &Location, message: &str) -> Error {
    Error::new(&location, format!("Syntactic Error: {}", message))
  }

  fn stream_prefix_to_string(r: &mut dyn MarkableCharReader) -> Result<String> {
    if r.is_eof()? {
      Ok(String::from("EOF"))
    } else {
      let prefix = r.peek(9)?.chars().collect::<Vec<_>>();
      let prefix = if prefix.len() < 9 {
        prefix.iter().collect::<String>()
      } else {
        format!("{}...", prefix[..8].iter().collect::<String>())
      };
      Ok(format!("{:?}", prefix))
    }
  }
}

pub struct TerminalStringScanner {
  terminal_string: Vec<char>,
}

impl TerminalStringScanner {
  pub fn new(terminal_string: Vec<char>) -> Self {
    Self { terminal_string }
  }
}

impl Scanner for TerminalStringScanner {
  fn scan(
    &self,
    context: &mut LexMachine,
    addr: usize,
    r: &mut dyn MarkableCharReader,
    events: &mut Vec<Event>,
  ) -> Result<Prospect> {
    let instr = context.graph.instruction(addr).unwrap();
    if r.prefix_matches(&self.terminal_string)? {
      let location = r.location();
      r.skip(self.terminal_string.len())?;
      events.push(Event::Token {
        definition: instr.definition.clone(),
        location,
        token: self.terminal_string.iter().collect::<String>(),
      });
      Ok(Prospect::Proceed)
    } else {
      Ok(Prospect::NotThisWay(context.err_expected_but_stream_not(Some(addr), r)))
    }
  }
}

pub struct SpecialSequenceScanner {
  scanner: Box<dyn crate::parser::SpecialSequenceScanner>,
}

impl SpecialSequenceScanner {
  pub fn new(scanner: Box<dyn crate::parser::SpecialSequenceScanner>) -> Self {
    Self { scanner }
  }
}

impl Scanner for SpecialSequenceScanner {
  fn scan(
    &self,
    context: &mut LexMachine,
    addr: usize,
    r: &mut dyn MarkableCharReader,
    events: &mut Vec<Event>,
  ) -> Result<Prospect> {
    let instr = context.graph.instruction(addr).unwrap();
    let mark = r.mark()?;
    Ok(match self.scanner.scan(&instr.definition, r)? {
      Reaction::Match { events: mut evts } => {
        r.unmark(mark)?;
        events.append(&mut evts);
        Prospect::Proceed
      }
      Reaction::Forward { meta_identifier } => {
        if let Some(next) = context.graph.index_of_label(&meta_identifier) {
          r.unmark(mark)?;
          context.parse_to_subroutine_end(next, r, events)?;
          Prospect::Proceed
        } else {
          r.reset_to_mark(mark)?;
          return Err(Error::new(
            &r.location(),
            format!(
              "The non-existent meta-identifier {:?} was directed by the special-sequence {} defined in {}",
              meta_identifier, instr.symbol, instr.definition
            ),
          ));
        }
      }
      Reaction::Unmatch => {
        r.reset_to_mark(mark)?;
        Prospect::NotThisWay(context.err_expected_but_stream_not(Some(addr), r))
      }
    })
  }
}

pub struct EmptyScanner {}

impl EmptyScanner {
  pub fn new() -> Self {
    Self {}
  }
}

impl Scanner for EmptyScanner {
  fn scan(
    &self,
    _context: &mut LexMachine,
    _addr: usize,
    _r: &mut dyn MarkableCharReader,
    _events: &mut Vec<Event>,
  ) -> Result<Prospect> {
    Ok(Prospect::Proceed)
  }
}

pub struct TermWithExceptionScanner {
  factor: usize,
  exception: usize,
}

impl TermWithExceptionScanner {
  pub fn new(factor: usize, exception: usize) -> Self {
    Self { factor, exception }
  }
}

impl Scanner for TermWithExceptionScanner {
  fn scan(
    &self,
    context: &mut LexMachine,
    addr: usize,
    r: &mut dyn MarkableCharReader,
    events: &mut Vec<Event>,
  ) -> Result<Prospect> {
    let begin = r.location();
    let mark = r.mark()?;
    let mut temp = Vec::new();
    let prospect = match context.parse_to_subroutine_end(self.factor, r, &mut temp)? {
      p @ Prospect::Proceed => {
        let end = r.location();

        // Capture the matched character sequence.
        r.reset_to_mark(mark)?;
        let mark = r.mark()?;
        let mut buffer = Vec::new();
        while r.location().lines < end.lines || r.location().columns < end.columns {
          if let Some(ch) = r.read()? {
            buffer.push(ch);
          }
        }
        debug_assert_eq!(end, r.location());

        // Test for matching exception.
        let mut test = MarkableReader::with_location(begin.clone(), Box::new(BufferedCharReader::new(buffer)));
        let mut ignore = Vec::new();
        match context.parse_to_subroutine_end(self.exception, &mut test, &mut ignore)? {
          Prospect::Proceed if test.is_eof()? => {
            r.reset_to_mark(mark)?;
            Prospect::NotThisWay(context.err_expected_but_stream_not(Some(addr), r))
          }
          _ => {
            events.append(&mut temp);
            p
          }
        }
      }
      p @ Prospect::NotThisWay(..) => {
        r.reset_to_mark(mark)?;
        p
      }
    };
    Ok(prospect)
  }
}

/// This filter function removes empty event start/end pairs generated during parsing. However,
/// even if the entire syntax tree is empty, the non-terminal symbol of the root is returned
/// without deletion.
///
fn remove_empty_begin_end_pair(events: &mut Vec<Event>) {
  let mut i = 1; // the first pair isn't removed even if it's empty
  while i + 1 < events.len() {
    match (&events[i], &events[i + 1]) {
      (Event::Begin { label: begin, .. }, Event::End { label: end, .. }) => {
        debug_assert_eq!(begin, end);
        events.drain(i..=i + 1);
      }
      _ => i += 1,
    }
  }
}
