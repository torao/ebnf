use std::io::{Read, Write};

use crate::{
  io::{CharDecodeReader, CharReader, Decoder, SyntaxReader},
  Location,
};

#[test]
fn syntax_reader_mark_reset() {
  let (encoded, _) = encode("Shift_JIS", "零壱弐参四五六七八九");
  let mut r = SyntaxReader::for_bytes("", encoded.to_vec(), "Shift_JIS").unwrap();

  assert_eq!('零', r.read().unwrap().unwrap());
  assert_eq!('壱', r.read().unwrap().unwrap());
  let marker1 = r.mark().unwrap();
  assert_eq!('弐', r.read().unwrap().unwrap());
  assert_eq!('参', r.read().unwrap().unwrap());
  let marker2 = r.mark().unwrap();
  assert_eq!('四', r.read().unwrap().unwrap());
  let marker3 = r.mark().unwrap();
  assert_eq!('五', r.read().unwrap().unwrap());
  assert_eq!(&Location::with_location("", 1, 7), r.location());
  assert_eq!(2, r.reset_to_mark(marker2).unwrap());
  assert_eq!(&Location::with_location("", 1, 5), r.location());
  assert_eq!('四', r.read().unwrap().unwrap());
  assert_eq!(&Location::with_location("", 1, 6), r.location());
  assert!(r.reset_to_mark(marker3).is_err());
  assert_eq!(&Location::with_location("", 1, 6), r.location());
  assert_eq!('五', r.read().unwrap().unwrap());
  assert_eq!('六', r.read().unwrap().unwrap());
  assert_eq!(&Location::with_location("", 1, 8), r.location());
  assert_eq!(5, r.reset_to_mark(marker1).unwrap());
  assert_eq!(&Location::with_location("", 1, 3), r.location());
  assert_eq!('弐', r.read().unwrap().unwrap());
  assert_eq!('参', r.read().unwrap().unwrap());
  let marker4 = r.mark().unwrap();
  assert_eq!('四', r.read().unwrap().unwrap());
  let marker5 = r.mark().unwrap();
  assert_eq!('五', r.read().unwrap().unwrap());
  assert_eq!(&Location::with_location("", 1, 7), r.location());
  assert_eq!(2, r.clear_to_mark(marker4).unwrap());
  assert_eq!(&Location::with_location("", 1, 7), r.location());
  assert!(r.reset_to_mark(marker4).is_err());
  assert!(r.reset_to_mark(marker5).is_err());
  assert_eq!('六', r.read().unwrap().unwrap());
  assert_eq!('七', r.read().unwrap().unwrap());
  assert!(r.reset_to_mark(marker1).is_err());
  assert!(r.reset_to_mark(marker2).is_err());
  let marker5 = r.mark().unwrap();
  assert_eq!('八', r.read().unwrap().unwrap());
  assert_eq!('九', r.read().unwrap().unwrap());
  assert!(r.read().unwrap().is_none());
  assert_eq!(2, r.reset_to_mark(marker5).unwrap());
  assert_eq!('八', r.read().unwrap().unwrap());
  assert_eq!('九', r.read().unwrap().unwrap());
  assert!(r.read().unwrap().is_none());

  // The first level can be restored after the second level is cleared.
  let (encoded, _) = encode("Shift_JIS", "零壱弐参四五六七八九");
  let mut r = SyntaxReader::for_bytes("", encoded.to_vec(), "Shift_JIS").unwrap();
  assert_eq!('零', r.read().unwrap().unwrap());
  assert_eq!('壱', r.read().unwrap().unwrap());
  let marker1 = r.mark().unwrap();
  assert_eq!('弐', r.read().unwrap().unwrap());
  assert_eq!('参', r.read().unwrap().unwrap());
  let marker2 = r.mark().unwrap();
  assert_eq!('四', r.read().unwrap().unwrap());
  assert_eq!('五', r.read().unwrap().unwrap());
  assert_eq!(2, r.clear_to_mark(marker2).unwrap());
  assert_eq!('六', r.read().unwrap().unwrap());
  assert_eq!('七', r.read().unwrap().unwrap());
  assert!(r.reset_to_mark(marker2).is_err());
  assert_eq!(6, r.reset_to_mark(marker1).unwrap());
  assert_eq!('弐', r.read().unwrap().unwrap());
  assert_eq!('参', r.read().unwrap().unwrap());
}

#[test]
fn syntax_reader_peek_skip() {
  let (encoded, _) = encode("Shift_JIS", "零壱弐参四五六七八九");
  let mut r = SyntaxReader::for_bytes("", encoded.to_vec(), "Shift_JIS").unwrap();
  assert_eq!('零', r.read().unwrap().unwrap());
  assert_eq!("壱弐参", r.peek(3).unwrap());
  assert_eq!('壱', r.read().unwrap().unwrap());
  assert_eq!(&Location::with_location("", 1, 3), r.location());
  assert_eq!(3, r.skip(3).unwrap());
  assert_eq!(&Location::with_location("", 1, 6), r.location());
  assert_eq!('五', r.read().unwrap().unwrap());
  assert_eq!("六七八九", r.peek(100).unwrap());
  assert_eq!('六', r.read().unwrap().unwrap());
  assert_eq!(3, r.skip(100).unwrap());
  assert!(r.read().unwrap().is_none());
  assert_eq!(&Location::with_location("", 1, 11), r.location());
}

#[test]
fn syntax_reader_prefix_match() {
  let mut r = SyntaxReader::new("", From::from("\nhello, world"));
  assert!(!r.prefix_matches(&"hello".chars().collect::<Vec<char>>()).unwrap());
}

#[test]
fn syntax_reader_read_error() {
  let (encoded, _) = encode("Shift_JIS", "零壱弐");
  let r = Box::new(ErrorRead::new(&encoded, "something's wrong"));
  let mut r = SyntaxReader::with_encoding("", r, "Shift_JIS").unwrap();
  assert_eq!('零', r.read().unwrap().unwrap());
  assert_eq!('壱', r.read().unwrap().unwrap());
  assert_eq!('弐', r.read().unwrap().unwrap());
  assert!(r.read().unwrap_err().message.contains("something's wrong"));
}

#[test]
fn char_decode_reader_decoding() {
  for encoding in vec!["utf-8", "iso-8859-1", "us-ascii", "Shift_JIS"].iter() {
    assert_encode_decode(encoding, "hello, world");
  }

  for encoding in vec!["utf-8", "Shift_JIS", "EUC-JP", "iso-2022-jp"] {
    assert_encode_decode(encoding, JAPANESE);
  }

  // Undefined character encoding.
  let (encoded, _) = encode("Shift_JIS", "零壱弐");
  if let Err(err) = CharDecodeReader::for_bytes("", encoded.to_vec(), "UNDEFINED_ENCODING") {
    assert!(err.message.contains("UNDEFINED_ENCODING"));
  } else {
    panic!("Successfully constructed for an undefined character encoding.");
  }
}

#[test]
fn decode_expected_encoding_bytes() {
  assert_restore("us-ascii", "hello, world", b"hello, world");
  assert_restore("iso-8859-1", "hello, world", b"hello, world");
  assert_restore("utf-8", "hello, world", b"hello, world");
  assert_restore("Shift_JIS", "hello, world", b"hello, world");

  assert_restore(
    "Shift_JIS",
    "あいうえお",
    &[0x82u8, 0xA0, 0x82, 0xA2, 0x82, 0xA4, 0x82, 0xA6, 0x82, 0xA8][..],
  );
  assert_restore(
    "utf-8",
    "あいうえお",
    &[
      0xE3u8, 0x81, 0x82, 0xE3, 0x81, 0x84, 0xE3, 0x81, 0x86, 0xE3, 0x81, 0x88, 0xE3, 0x81, 0x8A,
    ],
  );
}

#[test]
fn encoder_encounter_garbled_text() {
  let (mut encoded, _) = encode("Shift_JIS", "零壱弐");
  encoded[3] = 0xFF;

  let mut decoder = Decoder::new("", "Shift_JIS", true).unwrap();
  let err = decoder.push(&encoded).unwrap_err();
  assert_eq!(Location::with_location("", 1, 3), err.location);
  assert!(
    err
      .message
      .contains("Detected a byte sequence that cannot be changed to Shift_JIS"),
    "{}",
    err.message
  );
}

fn assert_restore(encoding: &str, expected: &str, test: &[u8]) {
  let (encoded, has_error) = encode(encoding, expected);
  assert!(
    !has_error,
    "The expected string contains a character that cannot be encoded in {}: {}",
    encoding, expected
  );
  assert_eq!(
    encoded, test,
    "The test string doesn't match the assumption in {}.",
    encoding
  );

  // Decode in chunks of various lengths.
  for i in 1..=test.len() {
    let mut decoder = Decoder::new("", encoding, true).unwrap();
    let mut actual = String::with_capacity(1024);
    for chunk in split_by(test, i).iter() {
      actual.push_str(&decoder.push(*chunk).unwrap());
    }
    actual.push_str(&decoder.flush().unwrap());
    assert_eq!(hex_str(expected), hex_str(&actual), "{:?} != {:?}", expected, actual);
  }
}

fn encode(encoding: &str, s: &str) -> (Vec<u8>, bool) {
  let encode = encoding_rs::Encoding::for_label(encoding.as_bytes()).unwrap();
  let (cow, _, has_error) = encode.encode(s);
  (cow.to_vec(), has_error)
}

fn hex_str(s: &str) -> String {
  s.as_bytes()
    .iter()
    .map(|c| format!("{:02X}", c))
    .collect::<Vec<String>>()
    .join(" ")
}

fn split_by<'a>(buffer: &'a [u8], bytes: usize) -> Vec<&'a [u8]> {
  let mut chunks = Vec::new();
  let div = buffer.len() / bytes + if buffer.len() % bytes != 0 { 1 } else { 0 };
  for i in 0..div {
    let begin = i * bytes;
    let end = std::cmp::min((i + 1) * bytes, buffer.len());
    chunks.push(&buffer[begin..end]);
  }
  chunks
}

/// Raises an error with the specified message after the specified byte value has been read.
///
pub struct ErrorRead {
  remaining: Vec<u8>,
  message: String,
}

impl ErrorRead {
  pub fn new(bytes: &[u8], message: &str) -> ErrorRead {
    ErrorRead {
      remaining: bytes.to_vec(),
      message: message.to_string(),
    }
  }
}

impl Read for ErrorRead {
  fn read(&mut self, mut buf: &mut [u8]) -> std::io::Result<usize> {
    if self.remaining.is_empty() {
      Err(std::io::Error::new(
        std::io::ErrorKind::InvalidInput,
        self.message.to_string(),
      ))
    } else {
      let len = std::cmp::min(self.remaining.len(), buf.len());
      buf.write_all(&self.remaining[0..len])?;
      self.remaining.drain(0..len);
      Ok(len)
    }
  }
}

const JAPANESE: &str = r#"「ではみなさんは、そういうふうに川だと云いわれたり、乳の流れたあとだと云われたりしていたこのぼんやりと白いものがほんとうは何かご承知ですか。」先生は、黒板に吊つるした大きな黒い星座の図の、上から下へ白くけぶった銀河帯のようなところを指さしながら、みんなに問といをかけました。
カムパネルラが手をあげました。それから四五人手をあげました。ジョバンニも手をあげようとして、急いでそのままやめました。たしかにあれがみんな星だと、いつか雑誌で読んだのでしたが、このごろはジョバンニはまるで毎日教室でもねむく、本を読むひまも読む本もないので、なんだかどんなこともよくわからないという気持ちがするのでした。"#;

fn assert_encode_decode(encoding: &str, expected: &str) {
  struct ChunkedRead {
    chunks: Vec<Vec<u8>>,
  }

  impl Read for ChunkedRead {
    fn read(&mut self, mut buf: &mut [u8]) -> std::io::Result<usize> {
      if self.chunks.is_empty() {
        Ok(0)
      } else {
        let chunk = if self.chunks[0].len() <= buf.len() {
          self.chunks.remove(0)
        } else {
          self.chunks[0].drain(0..buf.len()).collect::<Vec<u8>>()
        };
        buf.write_all(&chunk).unwrap();
        Ok(chunk.len())
      }
    }
  }

  // CharReader test
  let (encoded, garbled) = encode(encoding, expected);
  assert!(!garbled);
  for bytes in 1..encoded.len() {
    // CharReader::read_chars(), read_all()
    let chunks = split_by(&encoded, bytes)
      .iter()
      .map(|s| s.to_vec())
      .collect::<Vec<Vec<u8>>>();
    let r = Box::new(ChunkedRead { chunks });
    let mut r = CharDecodeReader::new("foo.ebnf", r, encoding).unwrap();
    let actual = r.read_all().unwrap();
    assert_eq!(
      expected, actual,
      "CharReader::read_chars() decode failed: {}, bytes={}",
      encoding, bytes
    );

    // CharReader::read()
    let chunks = split_by(&encoded, bytes)
      .iter()
      .map(|s| s.to_vec())
      .collect::<Vec<Vec<u8>>>();
    let r = Box::new(ChunkedRead { chunks });
    let mut r = CharDecodeReader::new("foo.ebnf", r, encoding).unwrap();
    let mut actual = String::new();
    while let Some(ch) = r.read().unwrap() {
      actual.push(ch);
    }
    assert_eq!(
      expected, actual,
      "CharReader::read() decode failed: {}, bytes={}",
      encoding, bytes
    );
  }

  // Decode test
  assert_restore(encoding, expected, &encoded);
}
