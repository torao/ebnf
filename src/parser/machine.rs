use std::collections::HashSet;

use crate::{
  parser::parallel_notation,
  parser::{
    graph::{Instruction, LexGraph, Prospect, Scanner, Step},
    Event, Reaction,
  },
  Error, Location, Result,
};

#[derive(Debug)]
struct Subroutine {
  control: Control,
  return_address: Option<usize>,
}

#[derive(Debug)]
enum Control {
  Repetition {
    min: u32,
    max: u32,
    current: u32,
    continue_address: usize,
  },
  Block {
    exit_event: Event,
  },
}

enum PreEval {
  Accept(usize),
  Reject(usize),
  NotSure,
}

/// Turing machine
pub struct LexMachine<'a> {
  graph: &'a LexGraph,
  meta_identifier: String,
  /// The start position for the next [`proceed()`] execution.
  /// `None` if this parser has reached at the end of syntax definition.
  ///
  next_start_position: Option<usize>,
  /// storing return pointer
  stack: Vec<Subroutine>,
}

impl<'a> LexMachine<'a> {
  pub fn new(graph: &'a LexGraph, meta_identifier: &str) -> Option<Self> {
    graph
      .index_of_label(&format!("${}", meta_identifier))
      .map(|cursor| LexMachine {
        graph,
        meta_identifier: graph.canonical_name(meta_identifier).unwrap().to_string(),
        next_start_position: Some(cursor),
        stack: Vec::new(),
      })
  }

  pub fn id(&'a self) -> &'a str {
    &self.meta_identifier
  }

  pub fn proceed(&mut self, location: &Location, buffer: &[char], flush: bool) -> Result<(usize, Vec<Event>)> {
    let mut consumed = 0;
    let mut events = Vec::new();
    let mut location = location.clone();
    let mut livelock = HashSet::new();
    // while consumed < buffer.len() || (flush && !self.stack.is_empty()) {
    while flush || consumed < buffer.len() {
      let prev_stack_size = self.stack.len();
      let current_position = self.next_start_position;

      // Evaluate the execution results
      match self.step_forward(&location, &buffer[consumed..], flush)? {
        Prospect::NextStep { length, event, next } => {
          location.push_chars(&buffer[consumed..consumed + length]);
          consumed += length;
          if let Some(event) = event {
            events.push(event);
          }

          // Check for live lock.
          // This detects a live lock when the same step is executed despite a read length of 0.
          if length > 0 || (self.next_start_position.is_none() && self.stack.len() < prev_stack_size) {
            livelock.clear();
          } else if livelock.contains(&next) {
            let pos = Self::buffer_to_string(&buffer[consumed..]);
            let (symbol, definition) = self
              .next_start_position
              .map(|i| self.graph.instruction(i))
              .flatten()
              .map(|i| (i.symbol.to_string(), i.definition.clone()))
              .unwrap_or((String::from("EOF"), Location::with_location("<unknown>", 0, 0)));
            return Err(Error::new(
              &location,
              format!(
                "Livelock: The step {} defined in {} could not proceed on {}. {:?}",
                symbol, definition, pos, next
              ),
            ));
          } else {
            livelock.insert(current_position);
          }

          self.next_start_position = next;
        }
        Prospect::WaitingForMore => break,
        Prospect::NotThisWay => {
          let break_stack = self.stack.iter().enumerate().rfind(|(_, sr)| match &(*sr).control {
            Control::Repetition { min, current, .. } if *current >= *min => true,
            _ => false,
          });
          if let Some((i, _)) = break_stack {
            // Break the repetitions if at least the minimum number of repetitions condition is met.
            self.next_start_position = self.stack[i].return_address;
            let disposal = self.stack.drain(i..);
            for sb in disposal.rev() {
              if let Control::Block { exit_event } = sb.control {
                events.push(exit_event);
              }
            }
          } else {
            return self.error_expected_current_step_but_not(&location, &buffer[consumed..]);
          }
        }
      }
    }
    if flush {
      if self.next_start_position.is_some() {
        return self.error_expected_current_step_but_not(&location, &buffer[consumed..]);
      } else if consumed != buffer.len() {
        return Self::error_expected_but_not(&location, "EOF", &buffer[consumed..]);
      }
    }
    Ok((consumed, events))
  }

  fn step_forward(&mut self, location: &Location, buffer: &[char], flush: bool) -> Result<Prospect> {
    let cursor = if let Some(prospect) = self.move_to_next_start_position(location, buffer, flush)? {
      println!("step_forward({}, {:?}, {}) -> {:?}", location, buffer, flush, prospect);
      return Ok(prospect);
    } else {
      self.next_start_position.unwrap()
    };
    let instr = self.graph.instruction(cursor).unwrap();
    print!("step_forward({}, {:?}, {}):", location, buffer, flush);
    let prospect: Prospect = match &instr.step {
      Step::Repetition { min, max, subroutine } => {
        if *max == 0 {
          // Skip this step if the maximum number of repetition is zero.
          Prospect::NextStep {
            length: 0,
            event: None,
            next: instr.next,
          }
        } else {
          match self.pre_eval(*subroutine, location, buffer, flush)? {
            PreEval::Accept(..) => {
              let next = self.push_repetitions_onto_stack(*min, *max, *subroutine, instr.next);
              print!("Repetition({},{},{})", min, max, subroutine);
              next
            },
            PreEval::Reject(..) => {
              Prospect::NextStep {
                length: 0,
                event: None,
                next: instr.next,
              }
            },
            PreEval::NotSure => Prospect::WaitingForMore,
          }
        }
      }
      Step::Or { subroutines } => {
        print!("Or({})", subroutines.iter().map(|i| i.to_string()).collect::<Vec<_>>().join(","));
        match self.select_a_pathway(subroutines, &location, buffer, flush)? {
          (_, Some(next)) => Prospect::NextStep {
            length: 0,
            event: None,
            next: Some(next),
          },
          (PreEval::Reject(..), _) => Prospect::NotThisWay,
          (PreEval::NotSure, _) => Prospect::WaitingForMore,
          (PreEval::Accept(..), _) => unreachable!(),
        }
      },
      Step::Step { scanner, .. } => {
        print!("Step()");
        scanner.scan(self, &instr, &location, buffer, flush)?
      },
      Step::Alias { meta_identifier } => {
        print!("Alias({:?})", meta_identifier);
        let label = self.graph.canonical_name(meta_identifier).unwrap().to_string();
        let address = self.graph.index_of_label(&meta_identifier).expect(&format!(
          "meta-identifier {:?} is not defined (this must be checked during Syntax construction).",
          meta_identifier
        ));
        self.push_block_onto_stack(&instr.definition, location, &label, address, instr.next)
      }
    };

    println!(" -> {:?}", prospect);
    Ok(prospect)
  }

  ///
  fn select_a_pathway(
    &mut self,
    subroutine: &Vec<usize>,
    location: &Location,
    buffer: &[char],
    flush: bool,
  ) -> Result<(PreEval, Option<usize>)> {
    #[derive(Default)]
    struct MaxIndices {
      length: usize,
      indices: Vec<usize>,
    }
    impl MaxIndices {
      pub fn push(&mut self, i: usize, length: usize) {
        if length > self.length {
          self.length = length;
          self.indices.clear();
          self.indices.push(i);
        } else if length == self.length {
          self.indices.push(i);
        }
      }
      pub fn len(&self) -> usize {
        self.indices.len()
      }
    }

    let mut accepted = MaxIndices::default();
    let mut rejected = MaxIndices::default();
    let mut not_sure = Vec::new();
    for i in subroutine {
      match self.pre_eval(*i, &location, buffer, flush)? {
        PreEval::Accept(length) => accepted.push(*i, length),
        PreEval::Reject(length) => rejected.push(*i, length),
        PreEval::NotSure => not_sure.push(*i),
      }
    }
    match (accepted.len(), rejected.len(), not_sure.len()) {
      (1, _, 0) => Ok((PreEval::Accept(accepted.length), Some(accepted.indices.remove(0)))),
      (0, _, 1) => Ok((PreEval::NotSure, Some(not_sure.remove(0)))),
      (0, 1, 0) => Ok((PreEval::Reject(rejected.length), Some(rejected.indices.remove(0)))),
      (0, n, 0) if n > 1 => Ok((PreEval::Reject(rejected.length), None)),
      (n, _, 0) if n > 1 => self.error_duplicate_match(&location, buffer, &accepted.indices),
      _ => Ok((PreEval::NotSure, None)),
    }
  }

  fn pre_eval(&mut self, next: usize, location: &Location, buffer: &[char], flush: bool) -> Result<PreEval> {
    let instr = self.graph.instruction(next).unwrap();
    match &instr.step {
      Step::Repetition { min, max, subroutine } => {
        //println!("pre_eval({}, {}, {:?}, {}): Repetition({},{},{})", next, location, buffer, flush, min, max, subroutine);
        let mut offset = 0;
        let mut repetitions = 0;
        while repetitions <= *max {
          match self.pre_eval(*subroutine, location, &buffer[offset..], flush)? {
            PreEval::Accept(length) if length == 0 && repetitions >= *min => break,
            PreEval::Accept(length) => {
              offset += length;
              repetitions += 1;
            }
            PreEval::Reject(_length) if repetitions >= *min => break,
            PreEval::NotSure if flush => return Ok(PreEval::Reject(offset)),
            eval => return Ok(eval),
          }
        }
        Ok(PreEval::Accept(offset))
      }
      Step::Step { scanner, .. } => match scanner.scan(self, &instr, location, buffer, flush)? {
        Prospect::NextStep { length, .. } => {
          //println!("pre_eval({}, {}, {:?}, {}): Step() -> NextStep({})", next, location, buffer, flush, length);
          if let Some(next) = instr.next {
            match self.pre_eval(next, location, &buffer[length..], flush)? {
              PreEval::Accept(len) => Ok(PreEval::Accept(len + length)),
              PreEval::Reject(len) => Ok(PreEval::Reject(len + length)),
              PreEval::NotSure => Ok(PreEval::NotSure),
            }
          } else {
            Ok(PreEval::Accept(length))
          }
        }
        Prospect::NotThisWay => Ok(PreEval::Reject(0)),
        Prospect::WaitingForMore if flush => Ok(PreEval::Reject(0)),
        Prospect::WaitingForMore => Ok(PreEval::NotSure),
      },
      Step::Or { subroutines } => match self.select_a_pathway(subroutines, location, buffer, flush)? {
        (PreEval::Accept(..), Some(next)) => self.pre_eval(next, location, buffer, flush),
        (p @ _, _) => Ok(p),
      },
      Step::Alias { meta_identifier } => {
        //println!("pre_eval({}, {}, {:?}, {}): Alias({})", next, location, buffer, flush, meta_identifier);
        let index = self.graph.index_of_label(&meta_identifier).unwrap();
        self.pre_eval(index, location, buffer, flush)
      }
    }
  }

  /// When the specified cursor points to the end of a sub-sequence, this moves back one stack and
  /// refers to the cursor that follows.
  ///
  fn move_to_next_start_position(
    &mut self,
    location: &Location,
    buffer: &[char],
    _flush: bool,
  ) -> Result<Option<Prospect>> {
    // If the end of the sub-sequence has been reached, the stack is returned.
    while self.next_start_position.is_none() && !self.stack.is_empty() {
      let mut subroutine = self.stack.pop().unwrap();
      match &mut subroutine.control {
        Control::Repetition {
          max,
          current,
          continue_address,
          ..
        } if *current + 1 < *max => {
          *current += 1;
          self.next_start_position = Some(*continue_address);
          self.stack.push(subroutine);
        }
        Control::Repetition { .. } => {
          // If the maximum number of repetition has been reached.
          self.next_start_position = subroutine.return_address;
        }
        Control::Block { exit_event } => {
          self.next_start_position = subroutine.return_address;
          let event = exit_event.clone();
          return Ok(Some(Prospect::NextStep {
            length: 0,
            event: Some(event),
            next: subroutine.return_address,
          }));
        }
      }
    }
    if self.next_start_position.is_none() {
      if buffer.len() == 0 {
        return Ok(Some(Prospect::WaitingForMore));
      } else {
        return Self::error_expected_but_not(location, "EOF", buffer);
      }
    }
    assert!(self.next_start_position.is_some());
    Ok(None)
  }

  fn push_repetitions_onto_stack(
    &mut self,
    min: u32,
    max: u32,
    continue_address: usize,
    return_address: Option<usize>,
  ) -> Prospect {
    // TODO: Set the upper limit for the number of stackable items.
    self.stack.push(Subroutine {
      control: Control::Repetition {
        min,
        max,
        current: 0,
        continue_address,
      },
      return_address,
    });
    Prospect::NextStep {
      length: 0,
      event: None,
      next: Some(continue_address),
    }
  }

  fn push_block_onto_stack(
    &mut self,
    definition: &Location,
    location: &Location,
    label: &str,
    start_address: usize,
    return_address: Option<usize>,
  ) -> Prospect {
    // TODO: Set the upper limit for the number of stackable items.
    self.stack.push(Subroutine {
      control: Control::Block {
        exit_event: Event::end(definition.clone(), location.clone(), label),
      },
      return_address,
    });
    Prospect::NextStep {
      length: 0,
      event: Some(Event::begin(definition.clone(), location.clone(), label)),
      next: Some(start_address),
    }
  }

  fn error_duplicate_match<T>(&self, location: &Location, buffer: &[char], indices: &Vec<usize>) -> Result<T> {
    let actual = Self::buffer_to_string(buffer);
    let symbols = indices
      .iter()
      .map(|i| self.graph.instruction(*i).unwrap().symbol.to_string())
      .collect::<Vec<_>>();
    let symbols = parallel_notation(symbols, "or");
    Err(Error::new(
      &location,
      format!(
        "The parsing process encountered an ambiguous match. The pattern {} matches either {}.",
        actual, symbols
      ),
    ))
  }

  fn error_expected_current_step_but_not<T>(&self, location: &Location, buffer: &[char]) -> Result<T> {
    let expected = self
      .next_start_position
      .map(|i| self.graph.instruction(i).map(|n| n.symbol.to_string()))
      .flatten()
      .unwrap_or(String::from("EOF"));
    Self::error_expected_but_not(location, &expected, buffer)
  }

  pub fn error_expected_but_not<T>(location: &Location, expected: &str, actual: &[char]) -> Result<T> {
    let actual = Self::buffer_to_string(actual);
    Self::error_syntax(location, &format!("{} is expected, but {} appeared.", expected, actual))
  }

  fn error_syntax<T>(location: &Location, message: &str) -> Result<T> {
    Err(Error::new(&location, format!("Syntactic Error: {}", message)))
  }

  fn buffer_to_string(buffer: &[char]) -> String {
    let length = std::cmp::min(buffer.len(), 8);
    if length == 0 {
      String::from("EOF")
    } else {
      let sample = buffer[0..length].iter().collect::<String>();
      let sample = if buffer.len() > 8 { sample + "..." } else { sample };
      format!("{:?}", sample)
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
    _context: &mut LexMachine,
    inst: &Instruction,
    location: &Location,
    buffer: &[char],
    flush: bool,
  ) -> Result<Prospect> {
    let length = std::cmp::min(self.terminal_string.len(), buffer.len());
    for i in 0..length {
      if buffer[i] != self.terminal_string[i] {
        return Ok(Prospect::NotThisWay);
      }
    }
    Ok(if length >= self.terminal_string.len() {
      let token = Event::token(
        inst.definition.clone(),
        location.clone(),
        self.terminal_string.iter().collect::<String>(),
      );
      Prospect::NextStep {
        length,
        event: Some(token),
        next: inst.next,
      }
    } else if flush {
      Prospect::NotThisWay
    } else {
      Prospect::WaitingForMore
    })
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
    inst: &Instruction,
    location: &Location,
    buffer: &[char],
    flush: bool,
  ) -> Result<Prospect> {
    Ok(match self.scanner.scan(location, buffer, flush)? {
      Reaction::Match { length, token } => Prospect::NextStep {
        length,
        event: token.map(|tk| Event::Token {
          definition: inst.definition.clone(),
          location: location.clone(),
          token: tk,
        }),
        next: inst.next,
      },
      Reaction::Forward { meta_identifier } => {
        if let Some(next) = context.graph.index_of_label(&meta_identifier) {
          Prospect::NextStep {
            length: 0,
            event: None,
            next: Some(next),
          }
        } else {
          return Err(Error::new(
            &location,
            format!(
              "The non-existent meta-identifier {:?} was directed by the special-sequence {} defined in {}",
              meta_identifier, inst.symbol, inst.definition
            ),
          ));
        }
      }
      Reaction::NeedMore => Prospect::WaitingForMore,
      Reaction::Unmatch => Prospect::NotThisWay,
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
    inst: &Instruction,
    _location: &Location,
    _buffer: &[char],
    _flush: bool,
  ) -> Result<Prospect> {
    Ok(Prospect::NextStep {
      length: 0,
      event: None,
      next: inst.next,
    })
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
    _instr: &Instruction,
    location: &Location,
    buffer: &[char],
    flush: bool,
  ) -> Result<Prospect> {
    match context.pre_eval(self.factor, location, buffer, flush)? {
      PreEval::Accept(length) => match context.pre_eval(self.exception, location, &buffer[0..length], flush)? {
        PreEval::Accept(ex_length) => {
          if length == ex_length {
            return Ok(Prospect::NotThisWay);
          }
        }
        PreEval::Reject(..) => (),
        PreEval::NotSure => {
          return Ok(Prospect::WaitingForMore);
        }
      },
      PreEval::Reject(..) => (),
      PreEval::NotSure => {
        return Ok(Prospect::WaitingForMore);
      }
    }
    Ok(Prospect::NextStep {
      length: 0,
      event: None,
      next: Some(self.factor),
    })
  }
}
