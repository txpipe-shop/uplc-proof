import UplcProof.Induction
import UplcProof.Encode

/-!
# Tests: real Aiken functions, proved for every input

The scripts of `Tests/Induction/Scripts/` are compiled Aiken
(`Tests/Induction/aiken/lib/fixtures.ak`; `math_factorial.hex` is
aiken-blaster-examples' own build of `factorial`), applied to arguments built with
the encoders of `UplcProof.Encode` (`int`, `list`). For each one, except the four
limitations of `UplcProofTests.Induction.Negative` and the fixtures of
`UplcProofTests.Induction.Run`:
* a sample run of the real script agrees with the specification (`#guard`);
* `uplc_induction` proves the specification for every input;
* `#print axioms` shows only `propext` and `Quot.sound` (`#guard_msgs` fails
  the build otherwise).
-/

open PlutusCore.UPLC.Term PlutusCore.UPLC.CekValue PlutusCore.UPLC.CekMachine
open PlutusCore.Data (Data)
open UplcProof

namespace UplcProofTests.Induction

/-! ## Results and fixtures -/

def intV (x : Int) : CekValue := .VCon (.Integer x)
def listV (xs : List Int) : CekValue := .VCon (.ConstDataList (xs.map .I))

/-- The integer a run halted with, if any. -/
def haltInt : State → Option Int
  | .Halt (.VCon (.Integer i)) => some i
  | _ => none

/-- The integer list a run halted with, if any. -/
def haltList : State → Option (List Int)
  | .Halt (.VCon (.ConstDataList ds)) => ds.mapM fun | .I i => some i | _ => none
  | _ => none

def run (p : Program) (args : List Term) : State := cekExecuteProgram p args 100000

/-- Whether a run halted, with any value. -/
def halted : State → Bool
  | .Halt _ => true
  | _ => false

#import_uplc UplcProofTests.Induction.factorialHex PlutusV3 single_cbor_hex
  "Tests/Induction/Scripts/factorial.hex"
#import_uplc UplcProofTests.Induction.sumToHex PlutusV3 single_cbor_hex
  "Tests/Induction/Scripts/sum_to.hex"
#import_uplc UplcProofTests.Induction.sumToBoundedHex PlutusV3 single_cbor_hex
  "Tests/Induction/Scripts/sum_to_bounded.hex"
#import_uplc UplcProofTests.Induction.countdownHex PlutusV3 single_cbor_hex
  "Tests/Induction/Scripts/countdown.hex"
#import_uplc UplcProofTests.Induction.powerHex PlutusV3 single_cbor_hex
  "Tests/Induction/Scripts/power.hex"
#import_uplc UplcProofTests.Induction.sumHex PlutusV3 single_cbor_hex
  "Tests/Induction/Scripts/sum.hex"
#import_uplc UplcProofTests.Induction.sumProdHex PlutusV3 single_cbor_hex
  "Tests/Induction/Scripts/math_sum_prod.hex"
#import_uplc UplcProofTests.Induction.productHex PlutusV3 single_cbor_hex
  "Tests/Induction/Scripts/product.hex"
#import_uplc UplcProofTests.Induction.altSumHex PlutusV3 single_cbor_hex
  "Tests/Induction/Scripts/alternating_sum.hex"
#import_uplc UplcProofTests.Induction.lengthHex PlutusV3 single_cbor_hex
  "Tests/Induction/Scripts/length.hex"
#import_uplc UplcProofTests.Induction.sumSquaresHex PlutusV3 single_cbor_hex
  "Tests/Induction/Scripts/sum_squares.hex"
#import_uplc UplcProofTests.Induction.doubleAllHex PlutusV3 single_cbor_hex
  "Tests/Induction/Scripts/double_all.hex"
#import_uplc UplcProofTests.Induction.sumAccHex PlutusV3 single_cbor_hex
  "Tests/Induction/Scripts/sum_acc.hex"
#import_uplc UplcProofTests.Induction.factorialAccHex PlutusV3 single_cbor_hex
  "Tests/Induction/Scripts/factorial_acc.hex"
#import_uplc UplcProofTests.Induction.countPositiveAccHex PlutusV3 single_cbor_hex
  "Tests/Induction/Scripts/count_positive_acc.hex"
#import_uplc UplcProofTests.Induction.reverseAccHex PlutusV3 single_cbor_hex
  "Tests/Induction/Scripts/reverse_acc.hex"
#import_uplc UplcProofTests.Induction.lastOrHex PlutusV3 single_cbor_hex
  "Tests/Induction/Scripts/last_or.hex"
#import_uplc UplcProofTests.Induction.sumAccFirstHex PlutusV3 single_cbor_hex
  "Tests/Induction/Scripts/sum_acc_first.hex"
#import_uplc UplcProofTests.Induction.countPositiveHex PlutusV3 single_cbor_hex
  "Tests/Induction/Scripts/count_positive.hex"
#import_uplc UplcProofTests.Induction.fibHex PlutusV3 single_cbor_hex
  "Tests/Induction/Scripts/fib.hex"
#import_uplc UplcProofTests.Induction.halfHex PlutusV3 single_cbor_hex
  "Tests/Induction/Scripts/half.hex"
#import_uplc UplcProofTests.Induction.tribonacciHex PlutusV3 single_cbor_hex
  "Tests/Induction/Scripts/tribonacci.hex"
#import_uplc UplcProofTests.Induction.evenOrFailHex PlutusV3 single_cbor_hex
  "Tests/Induction/Scripts/even_or_fail.hex"
#import_uplc UplcProofTests.Induction.sumPairsHex PlutusV3 single_cbor_hex
  "Tests/Induction/Scripts/sum_pairs.hex"
#import_uplc UplcProofTests.Induction.requireMemberHex PlutusV3 single_cbor_hex
  "Tests/Induction/Scripts/require_member.hex"
#import_uplc UplcProofTests.Induction.sumIfPositiveHex PlutusV3 single_cbor_hex
  "Tests/Induction/Scripts/sum_if_positive.hex"
-- aiken-blaster-examples' own factorial (`verify/Scripts/math_factorial.hex`), compiled by
-- another aiken build: `(-1) + n` instead of `n + (-1)`
#import_uplc UplcProofTests.Induction.factorialOldHex PlutusV3 single_cbor_hex
  "Tests/Induction/Scripts/math_factorial.hex"

/-! ## Specifications -/

def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

def triangle : Nat → Nat
  | 0 => 0
  | n + 1 => (n + 1) + triangle n

def countdown : Nat → List Int
  | 0 => []
  | n + 1 => (n + 1 : Nat) :: countdown n

def prod : List Int → Int
  | [] => 1
  | x :: xs => x * prod xs

def altSum : List Int → Int
  | [] => 0
  | x :: xs => x - altSum xs

def sumSq : List Int → Int
  | [] => 0
  | x :: xs => x * x + sumSq xs

/-- Truncated dot product: `Σᵢ xs[i] * ys[i]` up to the shorter list. -/
def dot : List Int → List Int → Int
  | [], _            => 0
  | _ :: _, []       => 0
  | x :: xs, y :: ys => x * y + dot xs ys

def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

/-- The script's own `has`. -/
def has (x : Int) : List Int → Bool
  | [] => false
  | y :: ys => y == x || has x ys

/-! ## Sample runs agree with the specifications -/

#guard haltInt (run factorialHex.script [int 10]) == some (fact 10)
#guard haltInt (run factorialOldHex.script [int 10]) == some (fact 10)
#guard haltInt (run sumToHex.script [int 100]) == some (triangle 100)
#guard haltInt (run sumToBoundedHex.script [int 100]) == some (triangle 100)
#guard !halted (run sumToBoundedHex.script [int 1000001])
#guard haltList (run countdownHex.script [int 3]) == some (countdown 3)
#guard haltInt (run powerHex.script [int (-2), int 3]) == some ((-2) ^ 3)
#guard haltInt (run sumHex.script [list [4, 23, 56]]) == some [4, 23, 56].sum
#guard haltInt (run productHex.script [list [2, -3, 5]]) == some (prod [2, -3, 5])
#guard haltInt (run altSumHex.script [list [10, 3, 4]]) == some (altSum [10, 3, 4])
#guard haltInt (run lengthHex.script [list [7, 8, 9]]) == some 3
#guard haltInt (run sumSquaresHex.script [list [-3, 4]]) == some (sumSq [-3, 4])
#guard haltList (run doubleAllHex.script [list [1, 2, 3]]) == some [2, 4, 6]
#guard haltInt (run countPositiveHex.script [list [1, -2, 3]]) == some 2
#guard haltInt (run fibHex.script [int 10]) == some (fib 10)
#guard haltInt (run halfHex.script [int 9]) == some 4
#guard haltInt (run sumAccHex.script [list [1, 2, 3], int 10]) == some 16
#guard haltInt (run factorialAccHex.script [int 5, int 2]) == some (2 * fact 5)
#guard haltInt (run countPositiveAccHex.script [list [1, -2, 3], int 10]) == some 12
#guard haltList (run reverseAccHex.script [list [1, 2, 3], list [9]]) == some [3, 2, 1, 9]
#guard haltInt (run lastOrHex.script [list [1, 2, 3], int 9]) == some 3
#guard haltInt (run lastOrHex.script [list [], int 9]) == some 9
#guard haltInt (run sumAccFirstHex.script [int 10, list [1, 2, 3]]) == some 16
#guard halted (run evenOrFailHex.script [int 6])
#guard !halted (run evenOrFailHex.script [int 7])
#guard halted (run requireMemberHex.script [list [1, 2, 3], int 2])
#guard !halted (run requireMemberHex.script [list [1, 2, 3], int 5])
#guard haltInt (run sumIfPositiveHex.script [list [1, 2], int 1]) == some 3
#guard !halted (run sumIfPositiveHex.script [list [1, 2], int 0])
#guard haltInt (run sumProdHex.script [list [4, 23, 56], list [1, 2, 3]]) == some 218
#guard haltInt (run sumProdHex.script [list [4, 23, 56], list [1, 2]]) == some 50
#guard haltInt (run sumProdHex.script [list [], list [1, 2]]) == some 0

/-! ## Proofs for every input -/

theorem factorial_halts (n : Nat) : Halts factorialHex.script [int n] (intV (fact n)) := by
  uplc_induction n

theorem factorial_old_halts (n : Nat) : Halts factorialOldHex.script [int n] (intV (fact n)) := by
  uplc_induction n

theorem sum_to_halts (n : Nat) : Halts sumToHex.script [int n] (intV (triangle n)) := by
  uplc_induction n

/-- The script compares `n` with the literal 1000000 (`sum_to_bounded`). After the
    split on `n`, `↑(n + 1) ≤ 1000000` stays a branch condition (reducing it would
    unfold `n + 1 - 1000000 : Nat` one unit at a time, past the recursion limit);
    `h` closes the branch where the script fails. -/
theorem sum_to_bounded_halts (n : Nat) (h : n ≤ 1000000) :
    Halts sumToBoundedHex.script [int n] (intV (triangle n)) := by
  uplc_induction n

theorem countdown_halts (n : Nat) : Halts countdownHex.script [int n] (listV (countdown n)) := by
  uplc_induction n

/-- `b` is not an induction variable: the compiled loop captures it. -/
theorem power_halts (b : Int) (e : Nat) : Halts powerHex.script [int b, int e] (intV (b ^ e)) := by
  uplc_induction e [Int.pow_succ, Int.mul_comm]

theorem sum_halts (xs : List Int) : Halts sumHex.script [list xs] (intV xs.sum) := by
  uplc_induction xs

theorem product_halts (xs : List Int) : Halts productHex.script [list xs] (intV (prod xs)) := by
  uplc_induction xs

theorem alternating_sum_halts (xs : List Int) :
    Halts altSumHex.script [list xs] (intV (altSum xs)) := by
  uplc_induction xs

theorem length_halts (xs : List Int) : Halts lengthHex.script [list xs] (intV xs.length) := by
  uplc_induction xs

theorem sum_squares_halts (xs : List Int) :
    Halts sumSquaresHex.script [list xs] (intV (sumSq xs)) := by
  uplc_induction xs

theorem double_all_halts (xs : List Int) :
    Halts doubleAllHex.script [list xs] (listV (xs.map (2 * ·))) := by
  uplc_induction xs

/-! ## Recursion on `n - 2`: induction on pairs (`P k ∧ P (k + 1)`) -/

theorem fib_halts (n : Nat) : Halts fibHex.script [int n] (intV (fib n)) := by
  uplc_induction n

theorem half_halts (n : Nat) : Halts halfHex.script [int n] (intV (n / 2 : Nat)) := by
  uplc_induction n

/-! ## Accumulators: the invariant holds for every value of `acc` -/

theorem sum_acc_halts (xs : List Int) (acc : Int) :
    Halts sumAccHex.script [list xs, int acc] (intV (acc + xs.sum)) := by
  uplc_induction xs generalizing acc

theorem factorial_acc_halts (n : Nat) (acc : Int) :
    Halts factorialAccHex.script [int n, int acc] (intV (acc * fact n)) := by
  uplc_induction n generalizing acc [Int.mul_assoc, Int.natCast_mul]

/-- With a branch on the data in the loop. -/
theorem count_positive_acc_halts (xs : List Int) (acc : Int) :
    Halts countPositiveAccHex.script [list xs, int acc]
      (intV (acc + (xs.filter (0 < ·)).length)) := by
  uplc_induction xs generalizing acc

/-- A list accumulator. -/
theorem reverse_acc_halts (xs acc : List Int) :
    Halts reverseAccHex.script [list xs, list acc] (listV (xs.reverse ++ acc)) := by
  uplc_induction xs generalizing acc

/-- The first iteration replaces the accumulator by the head (`acc := x`). -/
theorem last_or_halts (xs : List Int) (acc : Int) :
    Halts lastOrHex.script [list xs, int acc] (intV (xs.getLast?.getD acc)) := by
  uplc_induction xs generalizing acc [List.getLast?_cons]

/-- Two lists consumed together: `xs` is the induction variable, `ys` the
    changing second argument. -/
theorem sum_prod_halts (xs ys : List Int) :
    Halts sumProdHex.script [list xs, list ys] (intV (dot xs ys)) := by
  uplc_induction xs generalizing ys

/-! ## Branches on the data -/

/-- The loop branches on `0 < x`: one branch per outcome. -/
theorem count_positive_halts (xs : List Int) :
    Halts countPositiveHex.script [list xs] (intV (xs.filter (0 < ·)).length) := by
  uplc_induction xs

/-- A validator-like script (`require_member`: `has(xs, x)`, else `fail`): the
    loop returns a `Bool`, not the script's result, so its result is given. -/
theorem require_member_halts (xs : List Int) (x : Int) (h : x ∈ xs) :
    Halts requireMemberHex.script [list xs, int x] (.VCon (.Bool true)) := by
  uplc_induction xs (loop := fun k => .VCon (.Bool (k.contains x)))

theorem require_member_fails (xs : List Int) (x : Int) (h : x ∉ xs) :
    Fails requireMemberHex.script [list xs, int x] := by
  uplc_induction xs (loop := fun k => .VCon (.Bool (k.contains x)))

/-- The hypothesis may use the spec's own definitions (here `has`). -/
theorem require_member_halts_has (xs : List Int) (x : Int) (h : has x xs = true) :
    Halts requireMemberHex.script [list xs, int x] (.VCon (.Bool true)) := by
  uplc_induction xs (loop := fun k => .VCon (.Bool (has x k)))

/-- A guard on the other argument (`t > 0`): the branch that contradicts `h`
    is closed, by `omega`. -/
theorem sum_if_positive_halts (xs : List Int) (t : Int) (h : 0 < t) :
    Halts sumIfPositiveHex.script [list xs, int t] (intV xs.sum) := by
  uplc_induction xs

theorem sum_if_positive_fails (xs : List Int) (t : Int) (h : t ≤ 0) :
    Fails sumIfPositiveHex.script [list xs, int t] := by
  uplc_induction xs

/-! ## A long run without a loop (about 730 steps) -/

/-- `unIData x + 1 + ⋯ + 1`, with `k` additions. -/
def addOnes : Nat → Term
  | 0 => .Apply (.Builtin .UnIData) (.Var "x")
  | k + 1 => .Apply (.Apply (.Builtin .AddInteger) (addOnes k)) (.Const (.Integer 1))

theorem add_ones_halts (n : Nat) :
    Halts (.Program (.Version 1 1 0) (.Lam "x" (addOnes 90))) [int n] (intV (n + 90)) := by
  uplc_induction n

/-! ## An `if` that is not delayed, as other compilers emit it: its value waits in a frame -/

/-- `(if 0 < x then 1 else 0) + 5`, the `if` being the builtin's first argument. -/
def ifInFrame : Term :=
  .Apply (.Apply (.Builtin .AddInteger)
    (.Apply (.Apply (.Apply (.Force (.Builtin .IfThenElse))
      (.Apply (.Apply (.Builtin .LessThanInteger) (.Const (.Integer 0)))
        (.Apply (.Builtin .UnIData) (.Var "x"))))
      (.Const (.Integer 1))) (.Const (.Integer 0))))
    (.Const (.Integer 5))

-- `n` is not used: the run only branches on `x`
theorem if_in_frame_halts (n : Nat) (x : Int) (h : 0 < x) :
    Halts (.Program (.Version 1 1 0) (.Lam "n" (.Lam "x" ifInFrame))) [int n, int x] (intV 6) := by
  uplc_induction n

/-! ## Six `if`s in a row, then a loop: seven nested splits (`uplc.maxSplits`) -/

/-- `if k < t then rest else error`, on the argument `t`. -/
def guardT (k : Int) (rest : Term) : Term :=
  .Force (.Apply (.Apply (.Apply (.Force (.Builtin .IfThenElse))
    (.Apply (.Apply (.Builtin .LessThanInteger) (.Const (.Integer k)))
      (.Apply (.Builtin .UnIData) (.Var "t"))))
    (.Delay rest)) (.Delay .Error))

/-- The body of the compiled `sum`. -/
def sumBody : Term := match sumHex.script with | .Program _ b => b

/-- `guarded_sum(xs, t)`: six guards `k < t` (`k = 0, …, 5`), then `sum(xs)`. -/
def guardedSum : Program :=
  .Program (.Version 1 1 0) (.Lam "xs" (.Lam "t"
    (guardT 0 (guardT 1 (guardT 2 (guardT 3 (guardT 4 (guardT 5
      (.Apply sumBody (.Var "xs"))))))))))

#guard haltInt (run guardedSum [list [4, 23, 56], int 6]) == some 83
#guard !halted (run guardedSum [list [4, 23, 56], int 5])

/-- The six `if`s split (the `¬ k < t` branches contradict `h`), then the run splits
    on `xs`: seven nested splits, under the default `uplc.maxSplits`. -/
theorem guarded_sum_halts (xs : List Int) (t : Int) (h : 5 < t) :
    Halts guardedSum [list xs, int t] (intV xs.sum) := by
  uplc_induction xs

-- the limit counts them exactly (with 6: `UplcProofTests.Induction.Negative`)
set_option uplc.maxSplits 7 in
example (xs : List Int) (t : Int) (h : 5 < t) :
    Halts guardedSum [list xs, int t] (intV xs.sum) := by
  uplc_induction xs

/-! ## Arithmetic of the builtins (a loop counter decremented by `subtractInteger`) -/

example (m : Nat) :
    PlutusCore.Integer.subtractInteger (PlutusCore.Integer.addInteger ↑m 5) 2 = ↑(m + 3) := by
  uplc_eq

/-! ## Axioms: only `propext` and `Quot.sound` -/

/-- info: 'UplcProofTests.Induction.factorial_halts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms factorial_halts
/-- info: 'UplcProofTests.Induction.factorial_old_halts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms factorial_old_halts
/-- info: 'UplcProofTests.Induction.sum_to_halts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sum_to_halts
/-- info: 'UplcProofTests.Induction.sum_to_bounded_halts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sum_to_bounded_halts
/-- info: 'UplcProofTests.Induction.countdown_halts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms countdown_halts
/-- info: 'UplcProofTests.Induction.fib_halts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms fib_halts
/-- info: 'UplcProofTests.Induction.half_halts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms half_halts
/-- info: 'UplcProofTests.Induction.power_halts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms power_halts
/-- info: 'UplcProofTests.Induction.sum_halts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sum_halts
/-- info: 'UplcProofTests.Induction.product_halts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms product_halts
/-- info: 'UplcProofTests.Induction.alternating_sum_halts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms alternating_sum_halts
/-- info: 'UplcProofTests.Induction.length_halts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms length_halts
/-- info: 'UplcProofTests.Induction.sum_squares_halts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sum_squares_halts
/-- info: 'UplcProofTests.Induction.double_all_halts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms double_all_halts
/-- info: 'UplcProofTests.Induction.count_positive_halts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms count_positive_halts
/-- info: 'UplcProofTests.Induction.sum_acc_halts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sum_acc_halts
/-- info: 'UplcProofTests.Induction.factorial_acc_halts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms factorial_acc_halts
/-- info: 'UplcProofTests.Induction.count_positive_acc_halts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms count_positive_acc_halts
/-- info: 'UplcProofTests.Induction.reverse_acc_halts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms reverse_acc_halts
/-- info: 'UplcProofTests.Induction.last_or_halts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms last_or_halts
/-- info: 'UplcProofTests.Induction.sum_prod_halts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sum_prod_halts
/-- info: 'UplcProofTests.Induction.require_member_halts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms require_member_halts
/-- info: 'UplcProofTests.Induction.require_member_fails' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms require_member_fails
/-- info: 'UplcProofTests.Induction.require_member_halts_has' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms require_member_halts_has
/-- info: 'UplcProofTests.Induction.sum_if_positive_halts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sum_if_positive_halts
/-- info: 'UplcProofTests.Induction.sum_if_positive_fails' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sum_if_positive_fails
/-- info: 'UplcProofTests.Induction.add_ones_halts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms add_ones_halts
/-- info: 'UplcProofTests.Induction.if_in_frame_halts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms if_in_frame_halts
/-- info: 'UplcProofTests.Induction.guarded_sum_halts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms guarded_sum_halts

/-! ## The engine's modes agree

`uplc.fastStep 2` compares every step the engine computes on the expression
(`Sym.Fast`) with `whnf` of `step`, and fails at the first difference;
`uplc.stepLemmas 0` proves every step by evaluation instead of by the lemmas of
`UplcProof.Induction.Steps`. The same claims, the same results. -/

set_option uplc.fastStep 2 in
example (n : Nat) : Halts factorialHex.script [int n] (intV (fact n)) := by
  uplc_induction n

set_option uplc.fastStep 2 in
example (xs : List Int) (acc : Int) :
    Halts countPositiveAccHex.script [list xs, int acc]
      (intV (acc + (xs.filter (0 < ·)).length)) := by
  uplc_induction xs generalizing acc

set_option uplc.fastStep 2 in
example (xs : List Int) (x : Int) (h : x ∈ xs) :
    Halts requireMemberHex.script [list xs, int x] (.VCon (.Bool true)) := by
  uplc_induction xs (loop := fun k => .VCon (.Bool (k.contains x)))

set_option uplc.stepLemmas 0 in
example (n : Nat) : Halts factorialHex.script [int n] (intV (fact n)) := by
  uplc_induction n

set_option uplc.stepLemmas 0 in
example (xs : List Int) (x : Int) (h : x ∈ xs) :
    Halts requireMemberHex.script [list xs, int x] (.VCon (.Bool true)) := by
  uplc_induction xs (loop := fun k => .VCon (.Bool (k.contains x)))

end UplcProofTests.Induction
