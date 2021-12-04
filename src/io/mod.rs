//! `io` module provides basic functions related to input and output.
//!
use crate::{Error, Location, Result};
use encoding_rs::{CoderResult, Encoding};
use std::{
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

pub struct BufferedCharReader {
  chars: Vec<char>,
}

impl BufferedCharReader {
  pub fn new(chars: Vec<char>) -> BufferedCharReader {
    BufferedCharReader { chars }
  }
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

pub trait MarkableCharReader: CharReader {
  /// Returns the current read position of this stream.
  ///
  fn location(&self) -> Location;

  fn is_eof(&mut self) -> Result<bool> {
    let mark = self.mark()?;
    let ch = self.read()?;
    self.reset_to_mark(mark)?;
    Ok(ch.is_none())
  }

  /// Determines whether the current read position of this stream is a forward match to the
  /// specified character sequence.
  ///
  /// ```rust
  /// use ebnf::io::{CharReader, MarkableCharReader, MarkableReader};
  ///
  /// let mut r = MarkableReader::for_bytes("", b"hello, world".to_vec(), "utf-8").unwrap();
  /// assert_eq!('h', r.read().unwrap().unwrap());
  /// assert!(r.prefix_matches(&['e', 'l', 'l']).unwrap());
  /// ```
  ///
  fn prefix_matches(&mut self, prefix: &[char]) -> Result<bool> {
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
  /// ```rust
  /// use ebnf::io::{CharReader, MarkableCharReader, MarkableReader};
  ///
  /// let mut r = MarkableReader::for_bytes("", b"hello, world".to_vec(), "utf-8").unwrap();
  /// assert_eq!('h', r.read().unwrap().unwrap());
  /// assert_eq!("ell", r.peek(3).unwrap());
  /// ```
  ///
  fn peek(&mut self, length: usize) -> Result<String> {
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
  fn skip(&mut self, length: usize) -> Result<usize> {
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
  fn mark(&mut self) -> Result<u64>;

  /// Resets the read position to the position of the specified mark.
  ///
  /// # Returns
  /// The number of characters that were undone by the reset operation.
  ///
  fn reset_to_mark(&mut self, marker: u64) -> Result<usize>;

  /// Clears the read position of the specified mark. However, as long as the other marks remain,
  /// the internal buffer for resetting will remain.
  ///
  /// # Returns
  /// The number of characters that were undone by the clear operation.
  ///
  fn unmark(&mut self, marker: u64) -> Result<()>;
}

// TODO テストして MarkableReader に追加し、また文字列版 MarkableCharReader を実装する。
#[allow(dead_code)]
struct UnreadBuffer {
  location: Location,
  buffer: Vec<char>,
  /// Next read position in the buffer.
  next_read_position_in_buffer: usize,
  /// Position of the head of the buffer in the stream.
  buffer_head_position_in_stream: u64,
  // TODO: Introduce the upper limit of the buffer size for marks.
  stack: Vec<(u64, Location)>,
}

#[allow(dead_code)]
impl UnreadBuffer {
  pub fn new(location: Location) -> Self {
    UnreadBuffer {
      location: location.clone(),
      buffer: Vec::with_capacity(1024),
      next_read_position_in_buffer: 0,
      buffer_head_position_in_stream: 0,
      stack: Vec::with_capacity(64),
    }
  }
  pub fn location(&self) -> Location {
    self.location.clone()
  }
  pub fn remains(&self) -> bool {
    self.buffer.len() > self.next_read_position_in_buffer
  }
  pub fn read(&mut self, buffer: &mut [char]) -> usize {
    let length = std::cmp::min(buffer.len(), self.buffer.len() - self.next_read_position_in_buffer);
    for i in 0..length {
      buffer[i] = self.buffer[self.next_read_position_in_buffer + i];
    }
    self.next_read_position_in_buffer += length;
    if !self.remains() {
      self.truncate_buffer_if_stack_empty();
    }
    self.location.push_chars(&buffer[..length]);
    length
  }
  pub fn append(&mut self, buf: &[char]) {
    if !self.stack.is_empty() {
      debug_assert!(!self.remains());
      self.buffer.append(&mut buf.to_vec());
      self.next_read_position_in_buffer += buf.len();
    } else {
      debug_assert!(self.buffer.is_empty());
      debug_assert_eq!(0, self.next_read_position_in_buffer);
      self.buffer_head_position_in_stream += buf.len() as u64;
    }
    self.location.push_chars(buf);
  }
  pub fn mark(&mut self) -> u64 {
    let position = self.buffer_head_position_in_stream + self.next_read_position_in_buffer as u64;
    debug_assert!(self.stack.last().map(|prev| prev.0 <= position).unwrap_or(true));
    self.stack.push((position, self.location()));
    position
  }
  pub fn revert(&mut self, mark: u64) -> Result<usize> {
    self.location = self.remove_mark(mark)?;
    let old_position = self.buffer_head_position_in_stream + self.next_read_position_in_buffer as u64;
    self.next_read_position_in_buffer = (mark - self.buffer_head_position_in_stream) as usize;
    Ok((old_position - mark) as usize)
  }
  pub fn unmark(&mut self, position: u64) -> Result<()> {
    self.remove_mark(position)?;
    self.truncate_buffer_if_stack_empty();
    Ok(())
  }
  fn remove_mark(&mut self, mark: u64) -> Result<Location> {
    if mark < self.buffer_head_position_in_stream
      || mark > self.buffer_head_position_in_stream + self.buffer.len() as u64
    {
      return self.err_invalid_mark(mark);
    }
    for i in (0..self.stack.len()).rev() {
      if self.stack[i].0 == mark {
        let location = self.stack[i].1.clone();
        self.stack.drain(i..);
        return Ok(location);
      } else if self.stack[i].0 < mark {
        return self.err_invalid_mark(mark);
      }
    }
    self.err_invalid_mark(mark)
  }
  fn truncate_buffer_if_stack_empty(&mut self) {
    if self.stack.is_empty() {
      self.buffer.truncate(0);
      self.next_read_position_in_buffer = 0;
    }
  }
  fn err_invalid_mark<T>(&self, mark: u64) -> Result<T> {
    Err(Error::new(
      &self.location,
      format!("The specified mark {} is invalid: {:?}", mark, self.stack),
    ))
  }
}

/// A character stream that implements mark, reset, and skip of the read position.
///
pub struct MarkableReader {
  r: Box<dyn CharReader>,
  buffer: UnreadBuffer,
}

impl MarkableReader {
  pub fn new(name: &str, r: Box<dyn CharReader>) -> Self {
    MarkableReader {
      r,
      buffer: UnreadBuffer::new(Location::new(name)),
    }
  }

  pub fn with_location(location: Location, r: Box<dyn CharReader>) -> Self {
    Self {
      r,
      buffer: UnreadBuffer::new(location),
    }
  }

  pub fn with_encoding(name: &str, r: Box<dyn Read>, encoding: &str) -> Result<Self> {
    Ok(Self::new(name, Box::new(CharDecodeReader::new(name, r, encoding)?)))
  }

  pub fn for_bytes(name: &str, bytes: Vec<u8>, encoding: &str) -> Result<Self> {
    Ok(Self::with_encoding(name, Box::new(Cursor::new(bytes)), encoding)?)
  }
}

impl CharReader for MarkableReader {
  fn read_chars(&mut self, buffer: &mut [char]) -> Result<usize> {
    if self.buffer.remains() {
      let length = self.buffer.read(buffer);
      return Ok(length);
    }

    match self.r.read_chars(buffer) {
      Ok(len) if len == 0 => Ok(0),
      Ok(len) => {
        self.buffer.append(&buffer[..len]);
        Ok(len)
      }
      Err(err) => Err(Error::new(&self.buffer.location(), format!("{}", err))),
    }
  }
}

impl MarkableCharReader for MarkableReader {
  fn location(&self) -> Location {
    self.buffer.location()
  }

  fn mark(&mut self) -> Result<u64> {
    Ok(self.buffer.mark())
  }

  fn reset_to_mark(&mut self, marker: u64) -> Result<usize> {
    self.buffer.revert(marker)
  }

  fn unmark(&mut self, marker: u64) -> Result<()> {
    self.buffer.remove_mark(marker).map(|_| ())
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
