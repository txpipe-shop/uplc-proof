use aiken/fuzz

/// n! for n >= 0 (and 1 for negative n).
pub fn factorial(n: Int) -> Int {
  if n <= 0 {
    1
  } else {
    n * factorial(n - 1)
  }
}

/// The property: n! is positive.
test prop_factorial_positive(n via fuzz.int()) {
  if n >= 0 {
    factorial(n) > 0
  } else {
    True
  }
}

/// A wrong property: n! > n fails at n = 1 and n = 2 (`aiken check` catches
/// it only when its 100 random integers hit one of them).
test prop_factorial_greater(n via fuzz.int()) {
  if n >= 0 {
    factorial(n) > n
  } else {
    True
  }
}

// ---- Each test body as a function of its inputs, for `aiken export` ----

pub fn prop_factorial_positive_body(n: Int) -> Bool {
  if n >= 0 {
    factorial(n) > 0
  } else {
    True
  }
}

pub fn prop_factorial_greater_body(n: Int) -> Bool {
  if n >= 0 {
    factorial(n) > n
  } else {
    True
  }
}
