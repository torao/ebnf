//! `io` module provides basic functions related to input and output.
//!
use crate::{Error, Location, Result};
use encoding_rs::{CoderResult, Encoding};
use std::{
  collections::HashSet,
  io::{Cursor, Read},
  str::Chars,
};

#[cfg(test)]
pub mod test;

/// `CharReader` is a trait that represents a stream of input characters.
///
pub trait CharReader {
  /// Reads a single character from the stream.
  ///
  /// # Returns
  /// Character to be read; `None` if EOF has been reached.
  ///
  fn read(&mut self) -> Result<Option<char>> {
    let mut buffer = ['\u{0}'; 1];
    let length = self.read_chars(&mut buffer)?;
    if length == 0 {
      Ok(None)
    } else {
      Ok(Some(buffer[0]))
    }
  }

  /// Reads characters from the stream into the specified buffer.
  ///
  /// # Returns
  /// The number of characters written to the buffer if read successfully; 0 if EOF has been
  /// reached (or buffer size is 0).
  ///
  fn read_chars(&mut self, buffer: &mut [char]) -> Result<usize>;

  /// Reads all characters from a stream and returns them as a string.
  ///
  /// # Returns
  /// String to be read.
  ///
  fn read_all(&mut self) -> Result<String> {
    let mut buffer = ['\u{0}'; 1024];
    let mut out = String::with_capacity(1024);
    loop {
      let len = self.read_chars(&mut buffer[..])?;
      if len == 0 {
        break;
      }
      out.push_str(&buffer[0..len].iter().collect::<String>());
    }
    Ok(out)
  }
}

struct BufferedCharReader {
  chars: Vec<char>,
}

impl CharReader for BufferedCharReader {
  fn read_chars(&mut self, buffer: &mut [char]) -> Result<usize> {
    let length = std::cmp::min(buffer.len(), self.chars.len());
    for (i, ch) in self.chars.drain(0..length).enumerate() {
      buffer[i] = ch;
    }
    Ok(length)
  }
}

impl<'a> From<&'a str> for Box<dyn CharReader> {
  fn from(s: &'a str) -> Self {
    From::from(s.chars())
  }
}

impl<'a> From<Chars<'a>> for Box<dyn CharReader> {
  fn from(iter: Chars<'a>) -> Self {
    Box::new(BufferedCharReader {
      chars: iter.collect::<Vec<char>>(),
    })
  }
}

/// A character stream that implements mark, reset, and skip of the read position.
///
pub struct SyntaxReader {
  r: Box<dyn CharReader>,
  lookahead_buffer: Vec<char>,
  // TODO: INtroduce the upper limit of the buffer size for marks.
  mark_stack: Vec<(usize, Location, Vec<char>)>,
  mark_index: Index,
  location: Location,
}

impl SyntaxReader {
  pub fn new(name: &str, r: Box<dyn CharReader>) -> Self {
    let lookahead_buffer = Vec::new();
    let mark_stack = Vec::new();
    let mark_index = Index::new();
    let location = Location::new(name);
    SyntaxReader {
      r,
      lookahead_buffer,
      mark_stack,
      mark_index,
      location,
    }
  }

  pub fn with_encoding(name: &str, r: Box<dyn Read>, encoding: &str) -> Result<Self> {
    Ok(Self::new(name, Box::new(CharDecodeReader::new(name, r, encoding)?)))
  }

  pub fn for_bytes(name: &str, bytes: Vec<u8>, encoding: &str) -> Result<Self> {
    Ok(Self::with_encoding(name, Box::new(Cursor::new(bytes)), encoding)?)
  }

  /// Returns the current read position of this stream.
  ///
  pub fn location(&self) -> &Location {
    &self.location
  }

  /// Determines whether the current read position of this stream is a forward match to the
  /// specified character sequence.
  ///
  /// ```
  /// use std::io::Cursor;
  /// use ebnf::io::{CharReader, CharDecodeReader, SyntaxReader};
  ///
  /// let mut r = SyntaxReader::for_bytes("", b"hello, world".to_vec(), "utf-8").unwrap();
  /// assert_eq!('h', r.read().unwrap().unwrap());
  /// assert!(r.prefix_matches(&['e', 'l', 'l']).unwrap());
  /// ```
  ///
  pub fn prefix_matches(&mut self, prefix: &[char]) -> Result<bool> {
    let mark = self.mark()?;
    for i in 0..prefix.len() {
      let ch = self.read()?;
      if ch.is_none() || ch.unwrap() != prefix[i] {
        self.reset_to_mark(mark)?;
        return Ok(false);
      }
    }
    self.reset_to_mark(mark)?;
    Ok(true)
  }

  /// Refers to the string of the specified `length` at the beginning of the stream without changing
  /// the current read position.
  /// If the number of characters remaining in the stream is less than `length`, it will return the
  /// number of characters shorter than `length` up to EOF.
  ///
  /// ```
  /// use std::io::Cursor;
  /// use ebnf::io::{CharReader, CharDecodeReader, SyntaxReader};
  ///
  /// let mut r = SyntaxReader::for_bytes("", b"hello, world".to_vec(), "utf-8").unwrap();
  /// assert_eq!('h', r.read().unwrap().unwrap());
  /// assert_eq!("ell", r.peek(3).unwrap());
  /// ```
  ///
  pub fn peek(&mut self, length: usize) -> Result<String> {
    let mark = self.mark()?;
    let mut chars = Vec::<char>::with_capacity(length);
    for _ in 0..length {
      match self.read()? {
        Some(ch) => chars.push(ch),
        None => break,
      }
    }
    self.reset_to_mark(mark)?;
    Ok(chars.iter().collect::<String>())
  }

  /// Skips a specified number of characters from the current read position.
  ///
  /// # Parameters
  /// * `length` - Number of characters to skip.
  ///
  /// # Returns
  /// The number of characters actually skipped; a value less than `length` may be returned if EOF
  /// is reached.
  ///
  pub fn skip(&mut self, length: usize) -> Result<usize> {
    let mut remainings = length;
    let mut buffer = ['\u{0}'; 1024];
    while remainings > 0 {
      let len = std::cmp::min(remainings, buffer.len());
      let len = self.read_chars(&mut buffer[0..len])?;
      if len == 0 {
        break;
      }
      remainings -= len;
    }
    Ok(length - remainings)
  }

  /// Marks the current read position. The return value can be used to reset to this read position.
  ///
  /// This mark operation internally buffers the characters read for reset. Note that reading large
  /// data while retaining the mark may cause memory strain.
  ///
  /// # Returns
  /// Identifier of the marked position.
  ///
  pub fn mark(&mut self) -> Result<usize> {
    let marker = self.mark_index.acquire(&self.location)?;
    self.mark_stack.push((marker, self.location.clone(), Vec::new()));
    Ok(marker)
  }

  /// Resets the read position to the read position of the specified mark.
  ///
  /// # Returns
  /// The number of characters that were undone by the reset operation.
  ///
  pub fn reset_to_mark(&mut self, marker: usize) -> Result<usize> {
    let i = self.find_mark_index(marker)?;
    let mut undo_length = 0;
    while self.mark_stack.len() > i {
      let (_, location, unread) = self.mark_stack.pop().unwrap();
      undo_length += unread.len();
      self.lookahead_buffer.splice(0..0, unread);
      self.location = location;
    }
    self.mark_index.release(marker);
    Ok(undo_length)
  }

  /// Clears the read position of the specified mark. However, as long as the other marks remain,
  /// the internal buffer for resetting will remain.
  ///
  /// # Returns
  /// The number of characters that were undone by the clear operation.
  ///
  pub fn clear_to_mark(&mut self, marker: usize) -> Result<usize> {
    let i = self.find_mark_index(marker)?;
    let mut clear_length = 0;
    if i == 0 {
      for j in 0..self.mark_stack.len() {
        clear_length += self.mark_stack[j].2.len();
      }
      self.mark_stack.clear();
      debug_assert_eq!(1, self.mark_index.len());
    } else {
      while self.mark_stack.len() > i {
        let mut removal = self.mark_stack.remove(i);
        clear_length += removal.2.len();
        self.mark_stack[i - 1].2.append(&mut removal.2);
      }
    }
    self.mark_index.release(marker);
    Ok(clear_length)
  }

  /// Save read characters only if markers are present.
  fn save_undo_for_mark(&mut self, buffer: &[char], len: usize) -> Result<()> {
    if !self.mark_stack.is_empty() {
      let stack_len = self.mark_stack.len();
      let last = &mut self.mark_stack[stack_len - 1];
      last.2.append(&mut buffer[0..len].to_vec());
    }
    Ok(())
  }

  fn find_mark_index(&self, marker: usize) -> Result<usize> {
    for i in 0..self.mark_stack.len() {
      if self.mark_stack[i].0 == marker {
        return Ok(i);
      }
    }
    Err(Error::new(
      &self.location,
      format!("The specified mark is invalid: {}", marker),
    ))
  }
}

impl CharReader for SyntaxReader {
  fn read_chars(&mut self, buffer: &mut [char]) -> Result<usize> {
    if !self.lookahead_buffer.is_empty() {
      let len = std::cmp::min(buffer.len(), self.lookahead_buffer.len());
      for i in 0..len {
        buffer[i] = self.lookahead_buffer[i];
        self.location.push(buffer[i]);
      }
      self.lookahead_buffer.drain(0..len);
      self.save_undo_for_mark(buffer, len)?;
      return Ok(len);
    }

    match self.r.read_chars(buffer) {
      Ok(len) if len == 0 => Ok(0),
      Ok(len) => {
        self.location.push_chars(&buffer[0..len]);
        self.save_undo_for_mark(buffer, len)?;
        Ok(len)
      }
      Err(err) => Err(Error::new(&self.location, format!("{}", err))),
    }
  }
}

/// `CharDecodeReader` is a character stream for reading byte sequences read from a byte stream
/// as characters according to a specific encoding.
///
/// ```
/// use ebnf::io::{CharReader, CharDecodeReader};
/// use std::io::Cursor;
///
/// let buffer = [0x8Cu8, 0xE1, 0x94, 0x79, 0x82, 0xCD, 0x94, 0x4C, 0x82, 0xC5, 0x82, 0xA0, 0x82, 0xE9];
/// let mut reader = CharDecodeReader::for_bytes("/your/path/to/decode-file.txt", buffer.to_vec(), "Shift_JIS").unwrap();
/// let output = reader.read_all().unwrap();
///
/// assert_eq!("吾輩は猫である", output);
/// ```
///
/// For available encodings, please refer to the [whatwg](https://encoding.spec.whatwg.org/) site.
///
pub struct CharDecodeReader {
  r: Box<dyn Read>,
  decoder: Decoder,
  read_buffer: Vec<u8>,
  remaining_buffer: Vec<char>,
  location: Location,
}

impl CharDecodeReader {
  /// Constructs a reader that decodes characters of a given encoding.
  ///
  /// # Paramters
  /// * `r` - Lower-level byte streams.
  /// * `name` - The string that indicates the input source (e.g., file name or URL).
  /// * `encoding` - The encoding of a character, such as `"utf-8"` or `"Shift_JIS"`, to be decoded
  ///   from a byte sequence.
  ///
  /// # Returns
  /// Reader, or error if the `encoding` is undefined.
  ///
  pub fn new(name: &str, r: Box<dyn Read>, encoding: &str) -> Result<Self> {
    let r = r.into();
    let decoder = Decoder::new(name, encoding, false)?;
    let read_buffer = [0u8; 1024].to_vec();
    let remaining_buffer = Vec::new();
    let location = Location::new(name);
    Ok(CharDecodeReader {
      r,
      decoder,
      read_buffer,
      remaining_buffer,
      location,
    })
  }

  pub fn for_bytes(name: &str, bytes: Vec<u8>, encoding: &str) -> Result<Self> {
    Self::new(name, Box::new(Cursor::new(bytes)), encoding)
  }
}

impl CharReader for CharDecodeReader {
  fn read_chars(&mut self, buffer: &mut [char]) -> Result<usize> {
    if !self.remaining_buffer.is_empty() {
      let len = std::cmp::min(buffer.len(), self.remaining_buffer.len());
      for i in 0..len {
        buffer[i] = self.remaining_buffer[i];
        self.location.push(buffer[i]);
      }
      self.remaining_buffer.drain(0..len);
      return Ok(len);
    }

    loop {
      let length = match self.r.read(&mut self.read_buffer) {
        Ok(len) if len == 0 => return Ok(0),
        Ok(len) => len,
        Err(err) => {
          return Err(Error::new(&self.location, format!("{}", err)));
        }
      };
      let output = self.decoder.push(&self.read_buffer[0..length])?;
      if !output.is_empty() {
        let chars = output.chars().collect::<Vec<char>>();
        let len = std::cmp::min(buffer.len(), chars.len());
        for i in 0..len {
          buffer[i] = chars[i];
          self.location.push(buffer[i]);
        }
        if len < chars.len() {
          self.remaining_buffer.append(&mut chars[len..].to_vec());
        }
        return Ok(len);
      }
    }
  }
}

/// `Decorder` decodes a byte sequence into a string according to the specified encoding. The
/// operation is designed to decode characters from fragmented byte sequences for streaming and
/// pipeline processing.
///
/// ```
/// use ebnf::io::Decoder;
///
/// let mut decoder = Decoder::new("/your/path/to/decode-file.txt", "Shift_JIS", true).unwrap();
/// let mut output = String::new();
/// for buffer in vec![vec![0x8C, 0xE1, 0x94], vec![0x79, 0x82, 0xCD, 0x94], vec![0x4C, 0x82, 0xC5, 0x82, 0xA0, 0x82], vec![0xE9]] {
///   output.push_str(&decoder.push(&buffer).unwrap());
/// }
/// output.push_str(&decoder.flush().unwrap());
/// assert_eq!("吾輩は猫である", output);
/// ```
///
/// For available encodings, please refer to the [whatwg](https://encoding.spec.whatwg.org/) site.
///
pub struct Decoder {
  encoding: String,
  decoder: encoding_rs::Decoder,
  location: Location,
  stop_with_garbled: bool,
  buffer: Vec<u8>,
}

impl Decoder {
  /// Constructs a decoder that decodes characters of a given encoding.
  ///
  /// # Paramters
  /// * `name` - The string that indicates the input source (e.g., file name or URL).
  /// * `encoding` - The encoding of a character, such as `"utf-8"` or `"Shift_JIS"`, to be decoded
  ///   from a byte sequence.
  /// * `stop_with_garbled` - True if the decoder immediately terminates with an error when it
  ///   encounters a character that cannot decode, otherwise the character is replaced with the
  ///   REPLACEMENT CHARACTER `'\u{FFFC}'` and the process will continue to the end.
  ///
  /// # Returns
  /// Decoder. Error if the `encoding` is undefined.
  ///
  pub fn new(name: &str, encoding: &str, stop_with_garbled: bool) -> Result<Decoder> {
    let location = Location::new(name);

    // Get the decoder for the specified character encoding.
    let decoder = if let Some(encoding) = Encoding::for_label(encoding.as_bytes()) {
      encoding.new_decoder()
    } else {
      return Err(Error::new(
        &location,
        format!("Unable to recognize the specified character encoding: {}", encoding),
      ));
    };

    let encoding = encoding.to_string();
    let buffer = Vec::new();
    Ok(Decoder {
      encoding,
      decoder,
      location,
      stop_with_garbled,
      buffer,
    })
  }

  /// Adds a fragment of a byte sequence and returns a string that can be decoded to that point.
  /// If there is insufficient byte sequence to restore a character, the byte sequence will be
  /// buffered internally until sufficient byte sequence arrives for restoration.
  ///
  /// Note that it is necessary to [`Decoder::flush()`] at the end of the stream to force the
  /// buffered byte sequence to be converted to characters.
  ///
  /// # Parameters
  /// * `buffer` - The flagment of a byte sequence to restore a string.
  ///
  /// # Returns
  /// Continuation of the string that can be recovered in the arriving byte sequence.
  ///
  pub fn push(&mut self, buffer: &[u8]) -> Result<String> {
    self.convert(buffer, false)
  }

  /// Forces the byte sequence remaining in the internal buffer to be converted to a string.
  /// This method must be called at the end of the stream.
  ///
  /// # Returns
  /// Restored string.
  ///
  pub fn flush(&mut self) -> Result<String> {
    self.convert(&[0u8; 0], true)
  }

  /// Convert the internal buffer to a string as much as possible; if `flush` is true, convert all
  /// characters in the buffer to a string.
  ///
  fn convert(&mut self, buffer: &[u8], flush: bool) -> Result<String> {
    self.buffer.append(&mut buffer.to_vec());
    let mut position = 0;
    let mut output_buffer = String::with_capacity(256);
    let mut output = String::with_capacity(self.buffer.len());
    loop {
      let (result, read, garbled) = self
        .decoder
        .decode_to_string(&self.buffer[position..], &mut output_buffer, flush);
      position += read;
      if !output_buffer.is_empty() {
        output.push_str(&output_buffer);
        output_buffer.truncate(0);
      }
      if garbled && self.stop_with_garbled {
        return self.garbled_detected(&output);
      }
      if result == CoderResult::InputEmpty || (read == 0 && output_buffer.is_empty()) {
        break;
      }
    }
    self.location.push_str(&output);
    self.buffer.drain(0..position);
    Ok(output)
  }

  /// Generate an error to be reported when a garbled character is detected.
  ///
  fn garbled_detected(&mut self, output: &str) -> Result<String> {
    let position = output.chars().position(|c| c == '\u{FFFD}').unwrap_or(0);
    let from = self.location.clone();
    let mut to = from.clone();
    self
      .location
      .push_str(&output.chars().take(position + 1).collect::<String>());
    to.push_str(output);
    return Err(Error::new(
      &self.location,
      format!(
        "Detected a byte sequence that cannot be changed to {}: between ({},{}) and ({},{}).",
        self.encoding, from.lines, from.columns, to.lines, to.columns
      ),
    ));
  }
}

struct Index {
  next: usize,
  in_use: HashSet<usize>,
}

impl Index {
  pub fn new() -> Self {
    Index {
      next: 0,
      in_use: HashSet::with_capacity(32),
    }
  }
  pub fn acquire(&mut self, location: &Location) -> Result<usize> {
    if self.in_use.len() == usize::MAX {
      return Err(Error::new(location, "Too many mark operations."));
    }
    let mut i = self.next;
    while self.in_use.contains(&i) {
      i = if i == usize::MAX { 0 } else { i + 1 };
    }
    self.next = i + 1;
    Ok(i)
  }
  pub fn release(&mut self, i: usize) {
    self.in_use.remove(&i);
  }
  pub fn len(&self) -> usize {
    self.in_use.len()
  }
}
