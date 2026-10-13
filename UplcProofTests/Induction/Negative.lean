import UplcProofTests.Induction.Positive

/-!
# Tests: what `uplc_induction` must refuse

Each test has the form

    example … : Halts … ∨ True := by
      fails_with "reason" (left; uplc_induction n)
      right; trivial

The build fails if `uplc_induction` proves the `Halts …` side, or fails with an
error that does not contain `reason`. (No arithmetic hypothesis such as
`h : 0 = 1` may be in scope: `omega` would use it.) `fails_unbounded` checks the
same, then again with no heartbeat limit.
-/

open PlutusCore.UPLC.Term PlutusCore.UPLC.CekValue
open UplcProof

namespace UplcProofTests.Induction

open Lean Elab Tactic in
/-- `fails_with "reason" tac`: `tac` fails, with an error that contains `reason`. -/
elab "fails_with " r:str t:tactic : tactic => do
  let some err ← try evalTactic t; pure none catch e => pure (some e.toMessageData)
    | throwError "expected a failure with \"{r.getString}\", but the tactic succeeded"
  let msg : String ← err.toString
  unless (msg.splitOn r.getString).length > 1 do
    throwError "expected a failure with \"{r.getString}\", got{indentD msg}"

open Lean Elab Tactic in
/-- `fails_unbounded "reason" tac`: `tac` fails with an error that contains `reason`,
    first within the default heartbeat budget (`maxHeartbeats` 200000, counted from
    here), then with no limit at all. The first run guards the second: a tactic that
    does not stop on its own fails the build there (a timeout) instead of hanging
    it. (Both runs count against the declaration's own budget: lift it with
    `set_option maxHeartbeats 0 in` when they need more than it.) -/
elab "fails_unbounded " r:str t:tactic : tactic => do
  withTheReader Core.Context ({ · with maxHeartbeats := maxHeartbeats.defValue * 1000 }) <|
    withCurrHeartbeats <| evalTactic (← `(tactic| fails_with $r $t))
  withTheReader Core.Context ({ · with maxHeartbeats := 0 }) do
    evalTactic (← `(tactic| fails_with $r $t))

/-! ## Wrong specifications are rejected -/

example (n : Nat) : Halts factorialHex.script [int n] (intV (2 ^ n)) ∨ True := by
  fails_with "cannot prove them equal" (left; uplc_induction n)
  right; trivial

example (n : Nat) : Halts sumToHex.script [int n] (intV (triangle n + 1)) ∨ True := by
  fails_with "cannot prove them equal" (left; uplc_induction n)
  right; trivial

example (n : Nat) :
    Halts countdownHex.script [int n] (listV (countdown n).reverse) ∨ True := by
  fails_with "cannot prove them equal" (left; uplc_induction n)
  right; trivial

example (b : Int) (e : Nat) :
    Halts powerHex.script [int b, int e] (intV (b * e)) ∨ True := by
  fails_with "cannot prove them equal" (left; uplc_induction e [Int.pow_succ, Int.mul_comm])
  right; trivial

example (xs : List Int) : Halts sumHex.script [list xs] (intV (prod xs)) ∨ True := by
  fails_with "cannot prove them equal" (left; uplc_induction xs)
  right; trivial

example (xs : List Int) :
    Halts lengthHex.script [list xs] (intV (xs.length + 1)) ∨ True := by
  fails_with "cannot prove them equal" (left; uplc_induction xs)
  right; trivial

example (xs : List Int) :
    Halts doubleAllHex.script [list xs] (listV (xs.map (3 * ·))) ∨ True := by
  fails_with "cannot prove them equal" (left; uplc_induction xs)
  right; trivial

-- a wrong branch: counts `0 ≤ x` where the script counts `0 < x`
example (xs : List Int) :
    Halts countPositiveHex.script [list xs] (intV (xs.filter (0 ≤ ·)).length) ∨ True := by
  fails_with "on the branch" (left; uplc_induction xs)
  right; trivial

/-! ## Wrong claims about a validator-like script -/

-- accepts without the membership hypothesis
example (xs : List Int) (x : Int) :
    Halts requireMemberHex.script [list xs, int x] (.VCon (.Bool true)) ∨ True := by
  fails_with "fails (reaches `Error`)"
    (left; uplc_induction xs (loop := fun k => .VCon (.Bool (k.contains x))))
  right; trivial

-- rejects although `x` is a member
example (xs : List Int) (x : Int) (_h : x ∈ xs) :
    Fails requireMemberHex.script [list xs, int x] ∨ True := by
  fails_with "halts" (left; uplc_induction xs (loop := fun k => .VCon (.Bool (k.contains x))))
  right; trivial

-- a wrong result for the loop
example (xs : List Int) (x : Int) (_h : x ∈ xs) :
    Halts requireMemberHex.script [list xs, int x] (.VCon (.Bool true)) ∨ True := by
  fails_with "cannot prove them equal"
    (left; uplc_induction xs (loop := fun k => .VCon (.Bool (k.head? == some x))))
  right; trivial

-- halts without `0 < t`: the error names the branch that fails
example (xs : List Int) (t : Int) :
    Halts sumIfPositiveHex.script [list xs, int t] (intV xs.sum) ∨ True := by
  fails_with "on the branch [¬0 < t]: the script fails" (left; uplc_induction xs)
  right; trivial

-- halts without `n ≤ 1000000`: the error names the branch that fails (and the
-- comparison with the large literal is a branch, not a recursion-depth error)
example (n : Nat) : Halts sumToBoundedHex.script [int n] (intV (triangle n)) ∨ True := by
  fails_with "1000000]: the script fails (reaches `Error`)" (left; uplc_induction n)
  right; trivial

-- induction on the wrong variable: the run waits on `xs`, not on `n`
example (xs : List Int) (n : Nat) :
    Halts requireMemberHex.script [list xs, int n] (.VCon (.Bool true)) ∨ True := by
  fails_with "entry: symbolic execution is stuck" (left; uplc_induction n)
  right; trivial

-- induction on a variable the script does not get
example (_m n : Nat) : Halts factorialHex.script [int n] (intV (fact n)) ∨ True := by
  fails_with "is not in the script's arguments" (left; uplc_induction _m)
  right; trivial

-- the result uses a hypothesis about `xs`, which the loop does not see
example (xs : List Int) (h : xs ≠ []) :
    Halts sumHex.script [list xs] (intV (xs.head h + xs.tail.sum)) ∨ True := by
  fails_with "mentions `h`" (left; uplc_induction xs)
  right; trivial

/-! ## Accumulators -/

-- a wrong result
example (xs : List Int) (acc : Int) :
    Halts sumAccHex.script [list xs, int acc] (intV (acc + xs.sum + 1)) ∨ True := by
  fails_with "cannot prove them equal" (left; uplc_induction xs generalizing acc)
  right; trivial

-- a wrong list accumulator (`acc` before the reversed list)
example (xs acc : List Int) :
    Halts reverseAccHex.script [list xs, list acc] (listV (acc ++ xs.reverse)) ∨ True := by
  fails_with "cannot prove them equal" (left; uplc_induction xs generalizing acc)
  right; trivial

-- without `generalizing acc`, the error says to add it
example (xs : List Int) (acc : Int) :
    Halts sumAccHex.script [list xs, int acc] (intV (acc + xs.sum)) ∨ True := by
  fails_with "generalizing acc" (left; uplc_induction xs)
  right; trivial

-- `b` is captured by the loop, not passed: not an accumulator
example (b : Int) (e : Nat) : Halts powerHex.script [int b, int e] (intV (b ^ e)) ∨ True := by
  fails_with "is not an accumulator" (left; uplc_induction e generalizing b)
  right; trivial

-- a `Nat` accumulator: the script computes it as an `Int`
example (xs : List Int) (acc : Nat) :
    Halts sumAccHex.script [list xs, int acc] (intV (acc + xs.sum)) ∨ True := by
  fails_with "state it as `(acc : Int)`" (left; uplc_induction xs generalizing acc)
  right; trivial

/-! ## Induction on pairs (`fib`) -/

-- a wrong result: both inductions are tried, and both errors are shown
example (n : Nat) : Halts fibHex.script [int n] (intV (fib (n + 1))) ∨ True := by
  fails_with "Induction on pairs (for recursion on `n - 1` and `n - 2`) fails too"
    (left; uplc_induction n)
  right; trivial

/-! ## Known limitations (true statements the tactic does not prove)

* the accumulator before the list (`sum_acc_first(acc, xs)`);
* recursion on `n - 3` (`tribonacci`);
* a loop that fails for some inputs (`even_or_fail`, for odd `n`);
* a list taken two elements at a time (`sum_pairs`). -/

example (xs : List Int) (acc : Int) :
    Halts sumAccFirstHex.script [int acc, list xs] (intV (acc + xs.sum)) ∨ True := by
  fails_with "the accumulator before `n`" (left; uplc_induction xs generalizing acc)
  right; trivial

def trib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | n + 3 => trib n + trib (n + 1) + trib (n + 2)

example (n : Nat) : Halts tribonacciHex.script [int n] (intV (trib n)) ∨ True := by
  fails_with "Only structural recursion" (left; uplc_induction n)
  right; trivial

-- the loop invariant says the loop returns, but for `1` it fails
example (n : Nat) (_h : n % 2 = 0) :
    Halts evenOrFailHex.script [int n] (.VCon (.Bool true)) ∨ True := by
  fails_with "base case 1: the script fails" (left; uplc_induction n)
  right; trivial

def sumPairs : List Int → Int
  | a :: b :: rest => a * b + sumPairs rest
  | _ => 0

example (xs : List Int) : Halts sumPairsHex.script [list xs] (intV (sumPairs xs)) ∨ True := by
  fails_with "symbolic execution is stuck" (left; uplc_induction xs)
  right; trivial

/-! ## Splits nest at most `uplc.maxSplits` deep -/

-- induction on `b`, but the loop is on `e`: every iteration splits on `e = 0`, and the
-- run stops past the limit, with or without a heartbeat limit
set_option uplc.maxSplits 8 in
example (b e : Nat) : Halts powerHex.script [int b, int e] (intV ((b : Int) ^ e)) ∨ True := by
  fails_unbounded "entry: more than 8 nested splits" (left; uplc_induction b)
  right; trivial

-- six `if`s and the split on `xs` (`guarded_sum_halts`): seven nested splits, not six
set_option uplc.maxSplits 6 in
example (xs : List Int) (t : Int) (_h : 5 < t) :
    Halts guardedSum [list xs, int t] (intV xs.sum) ∨ True := by
  fails_with "entry: more than 6 nested splits" (left; uplc_induction xs)
  right; trivial

/-! ## A typo in the lemma list is reported as such -/

/-- error: Unknown constant `Int.pow_succc` -/
#guard_msgs in
example (b : Int) (e : Nat) : Halts powerHex.script [int b, int e] (intV (b ^ e)) := by
  uplc_induction e [Int.pow_succc, Int.mul_comm]

end UplcProofTests.Induction
