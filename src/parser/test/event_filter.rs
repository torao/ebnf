use crate::parser::{
  test::sl,
  test::{assert_eq_events, dl},
  Event, EventFilter,
};

#[test]
fn remove_empty_event_start_end_paris() {
  // The root begin/end pairs are not removed.
  assert_filtered_eq(
    vec![
      Event::begin(dl(1, 1), sl(1, 1), "root"),
      Event::end(dl(1, 1), sl(1, 1), "root"),
    ],
    vec![
      Event::begin(dl(1, 1), sl(1, 1), "root"),
      Event::end(dl(1, 1), sl(1, 1), "root"),
    ],
  );

  // The empty begin/end pairs without root are removed.
  assert_filtered_eq(
    vec![
      Event::begin(dl(1, 1), sl(1, 1), "root"),
      Event::begin(dl(1, 2), sl(1, 1), "NOTEMPTY"),
      Event::begin(dl(1, 3), sl(1, 1), "B"),
      Event::token(dl(1, 4), sl(1, 1), "b"),
      Event::end(dl(1, 3), sl(1, 1), "B"),
      Event::end(dl(1, 2), sl(1, 1), "NOTEMPTY"),
      Event::end(dl(1, 1), sl(1, 1), "root"),
    ],
    vec![
      Event::begin(dl(1, 1), sl(1, 1), "root"),
      Event::begin(dl(1, 2), sl(1, 1), "EMPTY"),
      Event::end(dl(1, 2), sl(1, 1), "EMPTY"),
      Event::begin(dl(1, 2), sl(1, 1), "NOTEMPTY"),
      Event::begin(dl(1, 3), sl(1, 1), "A"),
      Event::end(dl(1, 3), sl(1, 1), "A"),
      Event::begin(dl(1, 3), sl(1, 1), "B"),
      Event::token(dl(1, 4), sl(1, 1), "b"),
      Event::end(dl(1, 3), sl(1, 1), "B"),
      Event::begin(dl(1, 3), sl(1, 1), "C"),
      Event::end(dl(1, 3), sl(1, 1), "C"),
      Event::end(dl(1, 2), sl(1, 1), "NOTEMPTY"),
      Event::end(dl(1, 1), sl(1, 1), "root"),
    ],
  );

  fn assert_filtered_eq(expected: Vec<Event>, events: Vec<Event>) {
    for chunk_size in 1..events.len() {
      let mut f = EventFilter::new();
      let mut actual = Vec::new();
      for chunk in events.chunks(chunk_size) {
        let chunk = chunk.clone();
        actual.append(&mut f.push(chunk.to_vec(), false));
      }
      actual.append(&mut f.push(vec![], true));
      assert_eq_events(&expected, actual);
    }
  }
}
