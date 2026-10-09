use aiken/fuzz

/// The length of a list.
pub fn length(xs: List<Int>) -> Int {
  when xs is {
    [] -> 0
    [_, ..rest] -> 1 + length(rest)
  }
}

/// The property: a length is never negative.
test prop_length_non_negative(xs via fuzz.list(fuzz.int())) {
  length(xs) >= 0
}

// ---- The test body as a function of its inputs, for `aiken export` ----

pub fn prop_length_non_negative_body(xs: List<Int>) -> Bool {
  length(xs) >= 0
}
