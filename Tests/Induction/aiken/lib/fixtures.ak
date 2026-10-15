//// Functions exported as standalone UPLC programs
//// (`aiken export --module fixtures --name <fn>`), used as test fixtures
//// for UplcProof (`UplcProof.Induction`). Most exercise one recursion shape:
//// Int vs List recursion, list results, an extra unchanged argument, an
//// accumulator, a branch on data, recursion on `n - 2` and deeper; the last
//// ones take `Bool`, `ByteArray` and `Data` parameters, or compare with a
//// large literal.

pub fn factorial(n: Int) -> Int {
  when n is {
    0 -> 1
    _ -> n * factorial(n - 1)
  }
}

pub fn sum_to(n: Int) -> Int {
  when n is {
    0 -> 0
    _ -> n + sum_to(n - 1)
  }
}

pub fn sum(xs: List<Int>) -> Int {
  when xs is {
    [] -> 0
    [x, ..rest] -> x + sum(rest)
  }
}

pub fn product(xs: List<Int>) -> Int {
  when xs is {
    [] -> 1
    [x, ..rest] -> x * product(rest)
  }
}

pub fn alternating_sum(xs: List<Int>) -> Int {
  when xs is {
    [] -> 0
    [x, ..rest] -> x - alternating_sum(rest)
  }
}

pub fn length(xs: List<Int>) -> Int {
  when xs is {
    [] -> 0
    [_, ..rest] -> 1 + length(rest)
  }
}

pub fn sum_squares(xs: List<Int>) -> Int {
  when xs is {
    [] -> 0
    [x, ..rest] -> x * x + sum_squares(rest)
  }
}

pub fn double_all(xs: List<Int>) -> List<Int> {
  when xs is {
    [] -> []
    [x, ..rest] -> [2 * x, ..double_all(rest)]
  }
}

pub fn countdown(n: Int) -> List<Int> {
  when n is {
    0 -> []
    _ -> [n, ..countdown(n - 1)]
  }
}

pub fn power(b: Int, e: Int) -> Int {
  if e == 0 {
    1
  } else {
    b * power(b, e - 1)
  }
}

pub fn sum_acc(xs: List<Int>, acc: Int) -> Int {
  when xs is {
    [] -> acc
    [x, ..rest] -> sum_acc(rest, acc + x)
  }
}

pub fn factorial_acc(n: Int, acc: Int) -> Int {
  when n is {
    0 -> acc
    _ -> factorial_acc(n - 1, acc * n)
  }
}

pub fn count_positive_acc(xs: List<Int>, acc: Int) -> Int {
  when xs is {
    [] -> acc
    [x, ..rest] ->
      if x > 0 {
        count_positive_acc(rest, acc + 1)
      } else {
        count_positive_acc(rest, acc)
      }
  }
}

pub fn reverse_acc(xs: List<Int>, acc: List<Int>) -> List<Int> {
  when xs is {
    [] -> acc
    [x, ..rest] -> reverse_acc(rest, [x, ..acc])
  }
}

/// Two list parameters consumed together (simultaneous structural recursion).
pub fn sum_prod(xs: List<Int>, ys: List<Int>) -> Int {
  when xs is {
    [] -> 0
    [x, ..xs] ->
      when ys is {
        [] -> 0
        [y, ..ys] -> x * y + sum_prod(xs, ys)
      }
  }
}

/// The accumulator replaced by an element (`acc := x`).
pub fn last_or(xs: List<Int>, acc: Int) -> Int {
  when xs is {
    [] -> acc
    [x, ..rest] -> last_or(rest, x)
  }
}

/// The accumulator before the list (refused by `uplc_induction`).
pub fn sum_acc_first(acc: Int, xs: List<Int>) -> Int {
  when xs is {
    [] -> acc
    [x, ..rest] -> sum_acc_first(acc + x, rest)
  }
}

pub fn count_positive(xs: List<Int>) -> Int {
  when xs is {
    [] -> 0
    [x, ..rest] ->
      if x > 0 {
        1 + count_positive(rest)
      } else {
        count_positive(rest)
      }
  }
}

pub fn fib(n: Int) -> Int {
  if n <= 1 {
    n
  } else {
    fib(n - 1) + fib(n - 2)
  }
}

pub fn half(n: Int) -> Int {
  if n <= 1 {
    0
  } else {
    1 + half(n - 2)
  }
}

/// Recursion on `n - 3` (refused by `uplc_induction`).
pub fn tribonacci(n: Int) -> Int {
  if n <= 2 {
    n
  } else {
    tribonacci(n - 1) + tribonacci(n - 2) + tribonacci(n - 3)
  }
}

/// A loop that fails for some inputs (refused by `uplc_induction`).
pub fn even_or_fail(n: Int) -> Bool {
  if n == 0 {
    True
  } else if n == 1 {
    fail
  } else {
    even_or_fail(n - 2)
  }
}

/// Two elements at a time (refused by `uplc_induction`).
pub fn sum_pairs(xs: List<Int>) -> Int {
  when xs is {
    [a, b, ..rest] -> a * b + sum_pairs(rest)
    _ -> 0
  }
}

test factorial_5() {
  factorial(5) == 120
}

test sum_to_10() {
  sum_to(10) == 55
}

test sum_sample() {
  sum([4, 23, 56]) == 83
}

test product_sample() {
  product([2, 3, 4]) == 24
}

test length_sample() {
  length([7, 8, 9]) == 3
}

test sum_squares_sample() {
  sum_squares([1, 2, 3]) == 14
}

test double_all_sample() {
  double_all([1, 2, 3]) == [2, 4, 6]
}

test countdown_3() {
  countdown(3) == [3, 2, 1]
}

test power_2_10() {
  power(2, 10) == 1024
}

test sum_acc_sample() {
  sum_acc([1, 2, 3], 10) == 16
}

test factorial_acc_5() {
  factorial_acc(5, 2) == 240
}

test count_positive_acc_sample() {
  count_positive_acc([1, -2, 3], 10) == 12
}

test reverse_acc_sample() {
  reverse_acc([1, 2, 3], [9]) == [3, 2, 1, 9]
}

test last_or_sample() {
  last_or([1, 2, 3], 9) == 3 && last_or([], 9) == 9
}

test count_positive_sample() {
  count_positive([1, -2, 3]) == 2
}

test fib_10() {
  fib(10) == 55
}

test half_9() {
  half(9) == 4
}

test tribonacci_5() {
  tribonacci(5) == 11
}

test even_or_fail_6() {
  even_or_fail(6)
}

test sum_pairs_sample() {
  sum_pairs([1, 2, 3, 4, 5]) == 14
}

fn has(xs: List<Int>, x: Int) -> Bool {
  when xs is {
    [] -> False
    [y, ..ys] -> y == x || has(ys, x)
  }
}

/// Like a validator checking a signatory: `True` if `x` is in `xs`, else fails.
pub fn require_member(xs: List<Int>, x: Int) -> Bool {
  if has(xs, x) {
    True
  } else {
    fail
  }
}

/// A guard on the argument that is not the list.
pub fn sum_if_positive(xs: List<Int>, t: Int) -> Int {
  if t > 0 {
    sum(xs)
  } else {
    fail
  }
}

test sum_if_positive_sample() {
  sum_if_positive([1, 2], 1) == 3
}

// `Bool` and `ByteArray` parameters (added for UplcProof: encoders, `uplc_run`).
// Exported with aiken v1.1.24; the fixtures above with v1.1.21.

/// A validator-like check with no recursion, on `Bool` and `ByteArray`
/// parameters: `True` if open or signed by the owner, else fails.
pub fn check_signer(is_open: Bool, signer: ByteArray, owner: ByteArray) -> Bool {
  if is_open || signer == owner {
    True
  } else {
    fail
  }
}

/// `List<Bool>`: how many are `True`.
pub fn count_true(bs: List<Bool>) -> Int {
  when bs is {
    [] -> 0
    [b, ..rest] ->
      if b {
        1 + count_true(rest)
      } else {
        count_true(rest)
      }
  }
}

/// `List<ByteArray>`: whether `key` is one of `keys`.
pub fn signed_by(keys: List<ByteArray>, key: ByteArray) -> Bool {
  when keys is {
    [] -> False
    [k, ..rest] -> k == key || signed_by(rest, key)
  }
}

test check_signer_sample() {
  check_signer(False, #"01", #"01") && check_signer(True, #"01", #"02")
}

test count_true_sample() {
  count_true([True, False, True]) == 2
}

test signed_by_sample() {
  signed_by([#"01", #"02"], #"02") && !signed_by([#"01"], #"02")
}

// Equality on `Data` (the `equalsData` builtin), exported with aiken v1.1.24.

/// An output reference: a record, compared as `Data`.
pub type Ref {
  id: ByteArray,
  idx: Int,
}

/// A validator-like check: `True` if `r == expected` (`equalsData`), else fails.
pub fn require_ref(r: Ref, expected: Ref) -> Bool {
  if r == expected {
    True
  } else {
    fail
  }
}

/// `==` on `Data` as the result.
pub fn same_data(a: Data, b: Data) -> Bool {
  a == b
}

/// `==` on lists of records.
pub fn same_refs(xs: List<Ref>, ys: List<Ref>) -> Bool {
  xs == ys
}

test require_ref_sample() {
  require_ref(Ref { id: #"01", idx: 0 }, Ref { id: #"01", idx: 0 })
}

test same_data_sample() {
  let a: Data = Ref { id: #"01", idx: 0 }
  let b: Data = Ref { id: #"01", idx: 1 }
  same_data(a, a) && !same_data(a, b)
}

test same_refs_sample() {
  same_refs([Ref { id: #"01", idx: 0 }], [Ref { id: #"01", idx: 0 }]) && !same_refs(
    [Ref { id: #"01", idx: 0 }],
    [],
  )
}

// A bound written as a large literal, as a fuzzer's `int_between(0, 1_000_000)`
// puts it in a test (exported with aiken v1.1.24). After the split on `n`, the
// comparison of `n + 1` with 1_000_000 must stay a branch condition: reducing it
// unfolds `n + 1 - 1_000_000` one unit at a time.

pub fn sum_to_bounded(n: Int) -> Int {
  if n <= 1_000_000 {
    sum_to(n)
  } else {
    fail
  }
}

test sum_to_bounded_sample() {
  sum_to_bounded(10) == 55
}
