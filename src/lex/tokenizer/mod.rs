use crate::{lex::is_gap_separator_char, Error, Location, Result};

#[cfg(test)]
mod test;

pub const DEFAULT_INIT_BUFFER_SIZE: usize = 254;

/// `Tokenizer` simply converts the character stream into a flat sequence of [Token]s and notify
/// the `handler`.
///
pub struct Tokenizer {
  /// The maximum length of characters in the token that can be buffered. If 0, no limit.
  max_buffer_size: usize,

  /// Buffer to store undetermined character sequence.
  buffer: Vec<char>,

  /// Current read position.
  pub location: Location,
}

impl Tokenizer {
  pub fn new(name: &str) -> Tokenizer {
    Self::with_capacity(name, DEFAULT_INIT_BUFFER_SIZE, 0)
  }

  pub fn with_capacity(name: &str, init_buffer_size: usize, max_buffer_size: usize) -> Tokenizer {
    let init_buffer_size = if max_buffer_size == 0 {
      init_buffer_size
    } else {
      std::cmp::max(init_buffer_size, max_buffer_size)
    };
    Tokenizer {
      max_buffer_size,
      buffer: Vec::with_capacity(init_buffer_size),
      location: Location::new(name),
    }
  }

  /// `reset()` function clear the internal buffer and initializes the read position.
  pub fn reset(&mut self) {
    self.buffer.truncate(0);
    self.location.reset();
  }

  pub fn push(&mut self, ch: char) -> Result<Vec<Token>> {
    self.ensure_capacity(1)?;
    self.buffer.push(ch);
    self.tokenize()
  }

  pub fn push_str(&mut self, s: &str) -> Result<Vec<Token>> {
    let mut chars = s.chars().collect::<Vec<char>>();
    self.ensure_capacity(chars.len())?;
    self.buffer.append(&mut chars);
    self.tokenize()
  }

  /// `flush()` function restores the token from the remaining characters in this internal buffer.
  /// It should be called at the endo of the EBNF definition stream. The [Token::EOF] that indicates
  /// the location of the end of stream will always be appended to the end of return tokens upon
  /// successful result.
  ///
  pub fn flush(&mut self) -> Result<Vec<Token>> {
    let mut tokens = Vec::with_capacity(2);
    if let Some((token, next_position)) = self.read_next_token(0, true)? {
      if next_position > 0 {
        self.buffer.drain(0..next_position);
      }
      tokens.push(token);
    }
    assert!(
      self.buffer.is_empty(),
      "Flush is complete, but there is still data in the buffer: {:?}",
      self.buffer.iter().collect::<String>()
    );
    tokens.push(Token::EOF(self.location.clone()));
    Ok(tokens)
  }

  fn tokenize(&mut self) -> Result<Vec<Token>> {
    let mut position = 0;
    let mut tokens = Vec::with_capacity(16);
    while position < self.buffer.len() {
      if let Some((token, next_position)) = self.read_next_token(position, false)? {
        tokens.push(token);
        debug_assert_ne!(
          position, next_position,
          "The read position hasn't changed in the round (potentially an infinite loop)."
        );
        position = next_position;
      } else {
        break;
      }
    }

    // Deletes bytes read from the buffer.
    if position > 0 {
      self.buffer.drain(0..position);
    }
    Ok(tokens)
  }

  fn read_next_token(&mut self, position: usize, flush: bool) -> Result<Option<(Token, usize)>> {
    let next = read_next(&self.location, &self.buffer, position, flush)?;
    match next {
      Some((token, offset)) => {
        debug_assert_ne!(
          0, offset,
          "The read position hasn't changed in the round (potentially an infinite loop)."
        );
        let position = self.move_location(position, offset);
        Ok(Some((token, position)))
      }
      None => Ok(None),
    }
  }

  /// Move the reading position.
  fn move_location(&mut self, start: usize, offset: usize) -> usize {
    for i in 0..offset {
      self.location.push(self.buffer[start + i]);
    }
    start + offset
  }

  fn ensure_capacity(&self, additive_amount: usize) -> Result<()> {
    if self.max_buffer_size > 0 && self.buffer.len() + additive_amount > self.max_buffer_size {
      let msg = format!(
        "Token such as identifier, comment, or special sequence are too long: {} + {} > {}.",
        self.buffer.len(),
        additive_amount,
        self.max_buffer_size
      );
      Err(Error::new(&self.location, msg))
    } else {
      Ok(())
    }
  }
}

/// The enum type `Symbol` defines definitions with `-symbol` suffix in ISO 2382, and predications
/// for single character.
///
/// Some symbols have alternative representations, and concrete representations as text are kept
/// as its member.
///
#[derive(Debug, Eq, PartialEq)]
pub enum Token {
  // === Symbold ===
  /// `*`
  RepetitionSymbol(Location),
  /// '-'
  ExceptSymbol(Location),
  /// `,`
  ConcatenateSymbol(Location),
  /// `|`, or `/` or `!`
  DefinitionSeparatorSymbol(Location, char),
  /// `=`
  DefiningSymbol(Location),
  /// `;`, or `.`
  TerminatorSymbol(Location, char),
  // === Grouping ===
  /// `[`, or `(/`
  StartOptionSymbol(Location, &'static str),
  /// `]`, or `/)`
  EndOptionSymbol(Location, &'static str),
  /// `{`, or `(:`
  StartRepeatSymbol(Location, &'static str),
  /// `}`, or `:)`
  EndRepeatSymbol(Location, &'static str),
  /// `(`
  StartGroupSymbol(Location),
  /// `)`
  EndGroupSymbol(Location),

  /// EOF is not defined in EBNF, but is used to represent as a virtual symbol in order to preserve
  /// its position.
  EOF(Location),

  // === Atom ===
  /// Represents a `meta-identifier`
  MetaIdentifier(Location, String),

  /// Represents a `terminal-string` enclosed in `'` or `"`.
  /// The first `&str` member represents `{character}` (i.e., the inside character sequence of the
  /// quoted string). The second `char` member represents the actual quote symbol used.
  TerminalString(Location, String, char),

  /// Represents an `integer`, which is a sequence of one or more `decimal-digit`.
  Integer(Location, String),

  /// Represents a `bracketed-textual-comment` enclosed in `(*` and `*)`.
  /// The member `&str` represents a `{comment-symbols}` (i.e., the inside character sequence of
  /// a comment).
  Comment(Location, String),

  /// Represents a `special-sequence` enclosed in `?`.
  /// The member `&str` represents the inside `{character - '?'}` of the `special-sequence`.
  SpecialSequence(Location, String),

  /// Represents a sequence of ignorable whitespace characters.
  GapSeparatorSequence(Location, String),
}

#[inline]
fn is_letter_char(ch: char) -> bool {
  (ch >= 'a' && ch <= 'z') || (ch >= 'A' && ch <= 'Z')
}

#[inline]
fn is_decimal_digit_char(ch: char) -> bool {
  ch >= '0' && ch <= '9'
}

#[inline]
fn is_terminal_char(ch: char) -> bool {
  // This implementation is a strict specification, but it could be relaxed to allow non-us-ascii
  // Unicode.
  ch >= ' ' && ch < 0x7F as char
}

#[inline]
fn is_other_char(ch: char) -> bool {
  const OTHER_CHAR: &str = " .:!+_%@&#$<>/\\^`~";
  OTHER_CHAR.find(ch).is_some()
}

#[inline]
fn is_meta_identifier_first_char(ch: char) -> bool {
  is_letter_char(ch)
}

#[inline]
fn is_meta_identifier_char(ch: char) -> bool {
  is_meta_identifier_first_char(ch) || is_decimal_digit_char(ch)
}

#[inline]
fn is_special_sequence_char(ch: char) -> bool {
  (is_terminal_char(ch) && ch != '?') || is_other_char(ch) || is_gap_separator_char(ch)
}

/// `read_next()` function reads the next token from the specified buffer position.
/// If a valid token can be read, this returns `Some((token, offset))` tuple, where `offset`
/// is the number of characters corresponding to the token. If more data is needed in the buffer
/// to make a decision, returns `None`.
///
/// # Parameters
///
/// * `loc` - [Location] in the file or stream corresponding to the current read position.
/// * `buffer` - Character buffer to read tokens.
/// * `position` - Start position for reading in the `buffer`.
/// * `flush` - `true` if no more input will be made and it is therefore flushing.
///
/// # Returns
///
/// * `Some(token,size)` - The token generated from the specified position and the number of
///   characters in the buffer that the token occupied.
/// * `None` - Characters in the buffer are not sufficient to determine the token (need to
///   wait for more characters to arrive).
///
fn read_next(loc: &Location, buffer: &[char], position: usize, flush: bool) -> Result<Option<(Token, usize)>> {
  fn ok(token: Token, offset: usize) -> Result<Option<(Token, usize)>> {
    Ok(Some((token, offset)))
  }
  fn cont<T>() -> Result<Option<T>> {
    Ok(None)
  }
  debug_assert!(position <= buffer.len());
  if position == buffer.len() {
    return Ok(None);
  }
  match buffer[position] {
    ',' => ok(Token::ConcatenateSymbol(loc.clone()), 1),
    '=' => ok(Token::DefiningSymbol(loc.clone()), 1),
    separator @ ('|' | '!') => {
      // '/' is caught in the case '/)'.
      ok(Token::DefinitionSeparatorSymbol(loc.clone(), separator), 1)
    }
    terminator @ (';' | '.') => ok(Token::TerminatorSymbol(loc.clone(), terminator), 1),
    '-' => ok(Token::ExceptSymbol(loc.clone()), 1),
    ')' => ok(Token::EndGroupSymbol(loc.clone()), 1),
    '[' => ok(Token::StartOptionSymbol(loc.clone(), "["), 1),
    ']' => ok(Token::EndOptionSymbol(loc.clone(), "]"), 1),
    '{' => ok(Token::StartRepeatSymbol(loc.clone(), "{"), 1),
    '}' => ok(Token::EndRepeatSymbol(loc.clone(), "}"), 1),

    _ if !flush && position + 1 >= buffer.len() => {
      // The following are symbols that must not have more than two characters to be determined.
      cont()
    }

    '\'' | '\"' => terminal_string(loc, buffer, position, flush),
    '(' => {
      if flush && position + 1 == buffer.len() {
        ok(Token::StartGroupSymbol(loc.clone()), 1)
      } else if buffer[position + 1] == '*' {
        if position + 2 < buffer.len() && buffer[position + 2] == ')' {
          // Invalid character sequence: (*)
          Err(Error::new(
            loc,
            format!(
              "An ambiguous start/end-command-symbol: {}",
              buffer[position..=position + 2].iter().collect::<String>()
            ),
          ))
        } else {
          comment(loc, buffer, position, flush)
        }
      } else {
        match buffer[position + 1] {
          '/' => {
            // alternative start-option-symbol
            ok(Token::StartOptionSymbol(loc.clone(), "(/"), 2)
          }
          ':' => {
            // alternative start-repeat-symbol
            ok(Token::StartRepeatSymbol(loc.clone(), "(:"), 2)
          }
          _ => ok(Token::StartGroupSymbol(loc.clone()), 1),
        }
      }
    }
    '/' => {
      if !flush && buffer[position + 1] == ')' {
        ok(Token::EndOptionSymbol(loc.clone(), "/)"), 2)
      } else {
        ok(Token::DefinitionSeparatorSymbol(loc.clone(), '/'), 1)
      }
    }
    ':' => {
      if !flush && buffer[position + 1] == ')' {
        ok(Token::EndRepeatSymbol(loc.clone(), ":)"), 2)
      } else {
        Err(Error::new(loc, format!("No colon ':' is allowed here.")))
      }
    }
    '*' => {
      if !flush && buffer[position + 1] == ')' {
        Err(Error::new(
          loc,
          format!("end-comment-symbol '{}' is not opened.", END_COMMENT_SYMBOL),
        ))
      } else {
        ok(Token::RepetitionSymbol(loc.clone()), 1)
      }
    }
    '?' => special_sequence(loc, buffer, position, flush),
    meta_identifier if is_meta_identifier_first_char(meta_identifier) => Ok(
      read_while(&buffer, position + 1, is_meta_identifier_char, flush).map(|end| {
        let meta_identifier = buffer[position..end].iter().collect::<String>();
        (Token::MetaIdentifier(loc.clone(), meta_identifier), end - position)
      }),
    ),
    digit if is_decimal_digit_char(digit) => Ok(read_while(&buffer, position + 1, is_decimal_digit_char, flush).map(
      |end| {
        let decimal_digit = buffer[position..end].iter().collect::<String>();
        (Token::Integer(loc.clone(), decimal_digit), end - position)
      },
    )),
    gap if is_gap_separator_char(gap) => Ok(read_while(&buffer, position + 1, is_gap_separator_char, flush).map(
      |end| {
        let gap = buffer[position..end].iter().collect::<String>();
        (Token::GapSeparatorSequence(loc.clone(), gap), end - position)
      },
    )),
    unknown => Err(Error::new(
      &loc,
      format!(
        "An undefined character was detected: {:?} (U+{:04X})",
        unknown, unknown as u32
      ),
    )),
  }
}

/// `terminal_string()` function reads and consumes a single terminal-string from the current position.
///
fn terminal_string(loc: &Location, buffer: &[char], position: usize, flush: bool) -> Result<Option<(Token, usize)>> {
  let quote = buffer[position];

  // Find location of the corresponding quote.
  let mut end = position + 1;
  while end < buffer.len() && buffer[end] != quote {
    if !is_terminal_char(buffer[end]) {
      return Err(Error::new(
        loc,
        format!(
          "terminal-string contains a character {:?} that cannot be used.",
          buffer[end]
        ),
      ));
    }
    end += 1;
  }

  if end == buffer.len() {
    if flush {
      Err(Error::new(
        loc,
        format!("terminal-string is not closed with {:?}.", quote),
      ))
    } else {
      Ok(None)
    }
  } else if end == position + 1 {
    Err(Error::new(
      loc,
      "The terminal-string must contain one or more terminal-characters.".to_string(),
    ))
  } else {
    let s = buffer[position + 1..end].iter().collect::<String>();
    Ok(Some((Token::TerminalString(loc.clone(), s, quote), end - position + 1)))
  }
}

/// `special_sequence()` function reads and consumes a single special-sequence from the current position.
///
fn special_sequence(loc: &Location, buffer: &[char], position: usize, flush: bool) -> Result<Option<(Token, usize)>> {
  const SPECIAL_SEQUENCE_SYMBOL: char = '?';

  // Find location of the corresponding question.
  let mut end = position + 1;
  while end < buffer.len() && buffer[end] != SPECIAL_SEQUENCE_SYMBOL {
    if !is_special_sequence_char(buffer[end]) {
      return Err(Error::new(
        loc,
        format!(
          "special-sequence contains a character {:?} that cannot be used.",
          buffer[end]
        ),
      ));
    }
    end += 1;
  }

  if end == buffer.len() {
    if flush {
      Err(Error::new(
        loc,
        format!("special-sequence is not closed with {:?}.", SPECIAL_SEQUENCE_SYMBOL),
      ))
    } else {
      Ok(None)
    }
  } else {
    let s = buffer[position + 1..end].iter().collect::<String>();
    Ok(Some((Token::SpecialSequence(loc.clone(), s), end - position + 1)))
  }
}

const START_COMMENT_SYMBOL: &str = "(*";
const END_COMMENT_SYMBOL: &str = "*)";

/// `comment()` function reads and consumes a single (may be nexted) comment-squence from the current position.
///
fn comment(loc: &Location, buffer: &[char], position: usize, flush: bool) -> Result<Option<(Token, usize)>> {
  let mut location = loc.clone();
  let mut nested_depth = 0;

  location.push_str(START_COMMENT_SYMBOL);
  let mut end = position + 2;
  loop {
    if end >= buffer.len() {
      return if flush {
        Err(Error::new(
          loc,
          format!("This start-comment-symbol '{}' is not closed.", START_COMMENT_SYMBOL),
        ))
      } else {
        Ok(None)
      };
    }
    if buffer[end - 1] == '*' && buffer[end] == ')' {
      if nested_depth == 0 {
        let comment = buffer[position + 2..end - 1].iter().collect::<String>();
        return Ok(Some((Token::Comment(loc.clone(), comment), end - position + 1)));
      }
      nested_depth -= 1;
    } else if buffer[end - 1] == '(' && buffer[end] == '*' {
      nested_depth += 1;
    } else if !is_gap_separator_char(buffer[end]) && !is_terminal_char(buffer[end]) {
      return Err(Error::new(
        &location,
        format!(
          "This comment contains a character {:?} (U+{:04X}) that cannot be used as a comment.",
          buffer[end], buffer[end] as u32
        ),
      ));
    }
    location.push(buffer[end]);
    end += 1;
  }
}

fn read_while(buffer: &[char], position: usize, eval: fn(char) -> bool, flush: bool) -> Option<usize> {
  let mut position = position;
  while position < buffer.len() && eval(buffer[position]) {
    position += 1;
  }
  if !flush && position == buffer.len() {
    None
  } else {
    Some(position)
  }
}
