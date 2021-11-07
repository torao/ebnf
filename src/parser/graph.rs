use std::collections::HashMap;

use crate::{
  keyed_meta_identifier,
  lex::{DefinitionList, SingleDefinition, SyntacticFactor, SyntacticPrimary, SyntacticTerm},
  parser::{machine::TerminalStringScanner, parallel_notation, Event, SpecialSequenceParser},
  Location, Result, Syntax,
};

use super::{
  machine::{EmptyScanner, SpecialSequenceScanner, TermWithExceptionScanner},
  LexMachine,
};

pub struct Instruction {
  pub next: Option<usize>,
  pub symbol: String,
  pub definition: Location,
  pub step: Step,
}

pub trait Scanner {
  fn scan(
    &self,
    context: &mut LexMachine,
    instr: &Instruction,
    location: &Location,
    buffer: &[char],
    flush: bool,
  ) -> Result<Prospect>;
}

#[derive(Debug)]
pub enum Prospect {
  WaitingForMore,
  NextStep {
    length: usize,
    event: Option<Event>,
    next: Option<usize>,
  },
  NotThisWay,
}

pub enum Step {
  Repetition { min: u32, max: u32, subroutine: usize },
  Or { subroutines: Vec<usize> },
  Step { scanner: Box<dyn Scanner> },
  Alias { meta_identifier: String },
}

pub struct LexGraph {
  interactions: Vec<Instruction>,
  labeled_indices: HashMap<String, usize>,
  canonical_names: HashMap<String, String>,
}

impl LexGraph {
  pub fn compile(syntax: &Syntax, config: &GraphConfig) -> LexGraph {
    let mut interactions = Vec::new();
    let mut labeled_indices = HashMap::new();
    let mut canonical_names = HashMap::new();
    for rule in syntax.rules() {
      let id = keyed_meta_identifier(&rule.meta_identifier);
      let canonical_name = syntax.canonical_name(&rule.meta_identifier).unwrap();
      let index = register_definition_list(&mut interactions, None, &rule.definition_list, config);
      canonical_names.insert(id.clone(), canonical_name.to_string());
      labeled_indices.insert(id.clone(), index);

      let index = interactions.len();
      interactions.push(Instruction {
        next: None,
        symbol: canonical_name.to_string(),
        definition: rule.location.clone(),
        step: Step::Alias {
          meta_identifier: canonical_name.to_string(),
        },
      });
      labeled_indices.insert(format!("${}", id), index);
    }
    LexGraph {
      interactions,
      labeled_indices,
      canonical_names,
    }
  }

  pub fn canonical_name(&self, meta_identifier: &str) -> Option<&str> {
    let id = keyed_meta_identifier(meta_identifier);
    self.canonical_names.get(&id).map(|s| s.as_str())
  }

  pub fn step(&self, i: usize) -> &Instruction {
    &self.interactions[i]
  }

  pub fn index_of_label(&self, meta_identifier: &str) -> Option<usize> {
    self
      .labeled_indices
      .get(&keyed_meta_identifier(meta_identifier))
      .map(|x| *x)
  }

  pub fn instruction(&self, i: usize) -> Option<&Instruction> {
    self.interactions.get(i)
  }
}

fn register_definition_list(
  steps: &mut Vec<Instruction>,
  next: Option<usize>,
  list: &DefinitionList,
  config: &GraphConfig,
) -> usize {
  if list.0.len() == 1 {
    return register_single_definition(steps, next, &list.0[0], config);
  }

  let mut subroutines = Vec::with_capacity(list.0.len());
  let mut symbols = Vec::with_capacity(list.0.len());
  for def in &list.0 {
    let index = register_single_definition(steps, next, def, config);
    subroutines.push(index);
    symbols.push(steps[index].symbol.to_string());
  }

  let index = steps.len();
  let node = Instruction {
    next,
    symbol: parallel_notation(symbols, "or"),
    definition: steps.last().unwrap().definition.clone(),
    step: Step::Or { subroutines },
  };
  steps.push(node);

  index
}

fn register_single_definition(
  steps: &mut Vec<Instruction>,
  next: Option<usize>,
  def: &SingleDefinition,
  config: &GraphConfig,
) -> usize {
  assert_ne!(0, def.syntactic_terms.len());
  let mut current_next = next;
  for i in 0..def.syntactic_terms.len() {
    let term = &def.syntactic_terms[def.syntactic_terms.len() - i - 1];
    current_next = Some(register_syntactic_term(steps, current_next, term, config));
  }
  current_next.unwrap()
}

fn register_syntactic_term(
  steps: &mut Vec<Instruction>,
  next: Option<usize>,
  term: &SyntacticTerm,
  config: &GraphConfig,
) -> usize {
  if let Some(exception) = &term.syntactic_exception {
    let factor = register_syntactic_factor(steps, None, &term.syntactic_factor, config);
    let exception = register_syntactic_factor(steps, None, exception, config);

    let index = steps.len();
    let node = Instruction {
      next,
      symbol: term.to_string(),
      definition: term.syntactic_factor.syntactic_primary.location().clone(),
      step: Step::Step {
        scanner: Box::new(TermWithExceptionScanner::new(factor, exception)),
      },
    };
    steps.push(node);
    index
  } else {
    register_syntactic_factor(steps, next, &term.syntactic_factor, config)
  }
}

fn register_syntactic_factor(
  steps: &mut Vec<Instruction>,
  next: Option<usize>,
  factor: &SyntacticFactor,
  config: &GraphConfig,
) -> usize {
  if factor.repetition == 1 {
    register_syntactic_primary(steps, next, &factor.syntactic_primary, config)
  } else {
    let subroutine = register_syntactic_primary(steps, None, &factor.syntactic_primary, config);

    let index = steps.len();
    let node = Instruction {
      next,
      symbol: factor.to_string(),
      definition: factor.syntactic_primary.location().clone(),
      step: Step::Repetition {
        min: factor.repetition,
        max: factor.repetition,
        subroutine,
      },
    };
    steps.push(node);
    index
  }
}

fn register_syntactic_primary(
  steps: &mut Vec<Instruction>,
  next: Option<usize>,
  primary: &SyntacticPrimary,
  config: &GraphConfig,
) -> usize {
  let mut symbol = primary.to_string();
  let (step, definition): (Step, Location) = match &primary {
    SyntacticPrimary::OptionalSequence(definition, list) => {
      let subroutine = register_definition_list(steps, next, list, config);
      (
        Step::Repetition {
          min: 0,
          max: 1,
          subroutine,
        },
        definition.clone(),
      )
    }
    SyntacticPrimary::RepeatedSequence(definition, list) => {
      let subroutine = register_definition_list(steps, next, list, config);
      (
        Step::Repetition {
          min: 0,
          max: u32::MAX,
          subroutine,
        },
        definition.clone(),
      )
    }
    SyntacticPrimary::GroupedSequence(_, list) => return register_definition_list(steps, next, list, config),
    SyntacticPrimary::MetaIdentifier(definition, meta_identifier) => {
      symbol = meta_identifier.to_string();
      let meta_identifier = meta_identifier.to_string();
      (Step::Alias { meta_identifier }, definition.clone())
    }
    SyntacticPrimary::TerminalString(definition, terminal_string) => {
      symbol = format!("{:?}", terminal_string);
      let terminal_string = terminal_string.chars().collect::<Vec<_>>();
      (
        Step::Step {
          scanner: Box::new(TerminalStringScanner::new(terminal_string)),
        },
        definition.clone(),
      )
    }
    SyntacticPrimary::SpecialSequence(definition, special_sequence) => {
      let scanner = (config.special_sequence_parser.0)(definition, special_sequence);
      symbol = scanner.symbol();
      (
        Step::Step {
          scanner: Box::new(SpecialSequenceScanner::new(scanner)),
        },
        definition.clone(),
      )
    }
    SyntacticPrimary::EmptySequence(definition) => {
      symbol = String::from("EMPTY");
      (
        Step::Step {
          scanner: Box::new(EmptyScanner::new()),
        },
        definition.clone(),
      )
    }
  };

  let index = steps.len();
  let step = Instruction {
    next,
    symbol,
    definition,
    step,
  };
  steps.push(step);
  index
}

pub struct GraphConfig {
  special_sequence_parser: SpecialSequenceParser,
}

impl GraphConfig {
  pub fn new() -> Self {
    Self {
      special_sequence_parser: SpecialSequenceParser::default(),
    }
  }

  pub fn special_sequence_parser(&mut self, p: SpecialSequenceParser) -> &mut Self {
    self.special_sequence_parser = p;
    self
  }
}
