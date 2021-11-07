pub fn split_by(text: &str, chars: usize) -> Vec<String> {
  let text = text.chars().collect::<Vec<char>>();
  let mut chunks = Vec::new();
  let div = text.len() / chars + if text.len() % chars != 0 { 1 } else { 0 };
  for i in 0..div {
    let begin = i * chars;
    let end = std::cmp::min((i + 1) * chars, text.len());
    let chunk = text[begin..end].iter().collect::<String>();
    chunks.push(chunk);
  }
  chunks
}
