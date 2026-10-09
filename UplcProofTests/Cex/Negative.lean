import UplcProof.Cex
import UplcProof.Encode
import CardanoLedgerApi.V3

/-!
# Tests: what must be rejected, with the expected error

* ill-formed counterexample text (unbalanced parentheses, an unterminated string,
  an unknown constructor, an ill-typed value, a wrong or missing binder name);
* values that do not refute the statement (including a false statement with the
  wrong value: the statement itself is never available to the closers);
* `refuteWithValues` with a value of the wrong type, or the wrong number of values;
* a statement Blaster proves, given to `blaster_refute`;
* `blaster_pretty` on a valid goal: status `oracle`, and the axiom
  `Blaster.Tactic.blasterProven` shows; on a spurious model: status `falsified`,
  never `refuted`; on a goal Blaster cannot translate: status `unknown` (also
  `blaster_refute`);
* each checker on a case it must reject: the round trip (`roundTrips`,
  `renderLean`), the axiom check (`checkAxioms`), the kernel check (`kernelCheck`).
-/

set_option uplc.cex.timings false

open PlutusCore.Data (Data)
open PlutusCore.ByteString (ByteString)
open CardanoLedgerApi.V3.Tx (TxOutRef)
open UplcProof.Cex

namespace UplcProofTests.Cex.Negative

/-! ## Ill-formed z3 text -/

/-- info: Except.error "unbalanced parentheses: missing `)`" -/
#guard_msgs in #eval prettyFull "(PlutusCore.Data.PlutusCore.DataInternal.Data.I 5"

/-- info: Except.error "unbalanced parentheses: unexpected `)`" -/
#guard_msgs in #eval prettyFull "(PlutusCore.Data.PlutusCore.DataInternal.Data.I 5))"

/-- info: Except.error "unterminated string literal" -/
#guard_msgs in #eval prettyFull "(PlutusCore.ByteString.PlutusCore.ByteStringInternal.ByteString.mk \"ab)"

/-- info: Except.error "empty value" -/
#guard_msgs in #eval prettyFull "  "

/--
info: Except.error "counterexample entry \"(Data.I 5)\" is not of the form \"<binder>: <value>\""
-/
#guard_msgs in #eval splitEntry "(Data.I 5)"

/-! ## `refute_cex`: bad text, bad names -/

/--
error: value of d: ill-formed counterexample text (unbalanced parentheses: missing `)`):
  (PlutusCore.Data.PlutusCore.DataInternal.Data.I 5
-/
#guard_msgs in
example : ¬ ∀ (d : Data), d ≠ Data.I 5 := by
  refute_cex "d: (PlutusCore.Data.PlutusCore.DataInternal.Data.I 5"

/--
error: value of d: ill-formed counterexample text (unbalanced parentheses: unexpected `)`):
  (PlutusCore.Data.PlutusCore.DataInternal.Data.I 5))
-/
#guard_msgs in
example : ¬ ∀ (d : Data), d ≠ Data.I 5 := by
  refute_cex "d: (PlutusCore.Data.PlutusCore.DataInternal.Data.I 5))"

/--
error: value of d: the counterexample does not elaborate at type Data:
  PlutusCore.Data.PlutusCore.DataInternal.Data.Foo 5
Unknown constant `PlutusCore.Data.PlutusCore.DataInternal.Data.Foo`
-/
#guard_msgs in
example : ¬ ∀ (d : Data), d ≠ Data.I 5 := by
  refute_cex "d: (PlutusCore.Data.PlutusCore.DataInternal.Data.Foo 5)"

/--
error: value of d: the counterexample does not elaborate at type Data:
  PlutusCore.Data.PlutusCore.DataInternal.Data.I "x"
Application type mismatch: The argument
  "x"
has type
  String
but is expected to have type
  PlutusCore.Integer.Integer
in the application
  Data.I "x"
-/
#guard_msgs in
example : ¬ ∀ (d : Data), d ≠ Data.I 5 := by
  refute_cex "d: (PlutusCore.Data.PlutusCore.DataInternal.Data.I \"x\")"

-- an unknown name is an error
/-- error: unknown binder name(s): e. The statement's binders are: d -/
#guard_msgs in
example : ¬ ∀ (d : Data), d ≠ Data.I 5 := by
  refute_cex "e: (PlutusCore.Data.PlutusCore.DataInternal.Data.I 5)"

/-- error: unknown binder name(s): z. The statement's binders are: x, y -/
#guard_msgs in
example : ¬ ∀ (x y : Int), x < 3 := by
  refute_cex "x: 3", "z: 1"

-- a missing binder gets a default value (accepted: `UplcProofTests.Cex.Positive`), but
-- one whose type has none is an error naming it
/--
error: e is not in the counterexample, and its type
  Empty
has no default value (no `Inhabited` instance, no constructor with default arguments)
-/
#guard_msgs in
example : ¬ ∀ (x : Int) (e : Empty), x < 3 := by
  refute_cex "x: 3"

-- the same for z3's abstract value (`$0`: no concrete value)
/--
error: e has no concrete value in the counterexample ($0), and its type
  Empty
has no default value (no `Inhabited` instance, no constructor with default arguments)
-/
#guard_msgs in
example : ¬ ∀ (x : Int) (e : Empty), x < 3 := by
  refute_cex "x: 3", "e: $0"

-- a missing binder's default must still refute: here it breaks a hypothesis
/--
error: the hypothesis
  default < 0
does not hold at these values (no closer proves it; tried decide, rfl, trivial, cases, simp, uplc_cex_closer)
-/
#guard_msgs in
example : ¬ ∀ (x y : Int), x < 3 → y < x → y * 2 > -4 := by
  refute_cex "x: 0"

/--
error: refute_cex: counterexample entry "(- 2)" is not of the form "<binder>: <value>"
-/
#guard_msgs in
example : ¬ ∀ (x : Int), x > -1 := by
  refute_cex "(- 2)"

/-! ## `refute_with`: bad values -/

/--
error: Application type mismatch: The argument
  "x"
has type
  String
but is expected to have type
  PlutusCore.Integer.Integer
in the application
  Data.I "x"
-/
#guard_msgs in
example : ¬ ∀ (d : Data), d ≠ Data.I 5 := by
  refute_with Data.I "x"

/-- error: 1 value(s) given, but the statement has 2 binder(s): [x, y] -/
#guard_msgs in
example : ¬ ∀ (x y : Int), x < 3 → y < x → y * 2 > -4 := by
  refute_with 0

/-- error: 3 value(s) given, but the statement has 2 binder(s): [x, y] -/
#guard_msgs in
example : ¬ ∀ (x y : Int), x < 3 → y < x → y * 2 > -4 := by
  refute_with 0, -2, 1

/--
error: the goal is not a negation `¬ ∀ x̄, P`:
  ∀ (x : Int), x > 0
-/
#guard_msgs in
example : ∀ (x : Int), x > 0 := by
  refute_with 1

-- `refuteWithValues`: a value of the wrong type, the wrong number of values
open Lean Elab Tactic in
/--
error: the value of x has type
  String
but the binder has type
  Int
-/
#guard_msgs in
example : ¬ ∀ (x : Int), x > 0 := by
  run_tac do
    let _ ← refuteWithValues (← getMainGoal) #[toExpr "0"]
    replaceMainGoal []

open Lean Elab Tactic in
/-- error: 2 value(s) given, but the statement has 1 binder(s): [x] -/
#guard_msgs in
example : ¬ ∀ (x : Int), x > 0 := by
  run_tac do
    let _ ← refuteWithValues (← getMainGoal) #[toExpr (0 : Int), toExpr (1 : Int)]
    replaceMainGoal []

/-! ## Values that do not refute the statement -/

-- the statement is false (at `Data.I 5`), but not at `Data.I 4`: rejected, although
-- `simp_all` with the statement as a hypothesis would close the goal
/--
error: these values do not refute the statement: no closer proves
  ¬Data.I 4 ≠ Data.I 5
(tried decide, rfl, bool, cases, simp, simp_all, uplc_cex_closer)
-/
#guard_msgs in
example : ¬ ∀ (d : Data), d ≠ Data.I 5 := by
  refute_with Data.I 4

/--
error: the hypothesis
  5 < 3
does not hold at these values (no closer proves it; tried decide, rfl, trivial, cases, simp, uplc_cex_closer)
-/
#guard_msgs in
example : ¬ ∀ (x y : Int), x < 3 → y < x → y * 2 > -4 := by
  refute_with 5, -2

/--
error: these values do not refute the statement: no closer proves
  ¬(0 * 0 ≠ 9 ∨ 0 > 0)
(tried decide, rfl, bool, cases, simp, simp_all, uplc_cex_closer)
-/
#guard_msgs in
example : ¬ ∀ (x : Int), x * x ≠ 9 ∨ x > 0 := by
  refute_with 0

open PlutusCore.UPLC.Term PlutusCore.UPLC.CekValue PlutusCore.UPLC.CekMachine
open UplcProof

/-- info: Successfully decoded single CBOR hex 'Tests/Induction/Scripts/factorial.hex' -/
#guard_msgs in
#import_uplc UplcProofTests.Cex.Negative.factorialHex PlutusV3 single_cbor_hex
  "Tests/Induction/Scripts/factorial.hex"

def intV (x : Int) : CekValue := .VCon (.Integer x)

-- `factorial 2 = 2`: the claim holds at `n = 2`, the run cannot refute it
/--
error: these values do not refute the statement: no closer proves
  ¬Halts factorialHex.script [int 2] (intV 2)
(tried decide, rfl, bool, cases, simp, simp_all, uplc_cex_closer)
-/
#guard_msgs in
example : ¬ ∀ (n : Int), Halts factorialHex.script [int n] (intV n) := by
  refute_with 2

/-! ## `blaster_refute` on a statement Blaster proves -/

/--
error: UPLC-RESULT {"status":"oracle","kernel":false,"cex":{},"lean":{}}
blaster_refute: Blaster says it holds (z3: unsat): the statement cannot be refuted.
-/
#guard_msgs in
example : ¬ ∀ (r : TxOutRef), r.txOutRefIdx < 3 → r.txOutRefIdx < 4 := by
  blaster_refute

/--
error: blaster_refute: the goal is not a negation `¬ S`:
  ∀ (x : Int), x * x ≥ 0
-/
#guard_msgs in
example : ∀ (x : Int), x * x ≥ 0 := by
  blaster_refute

/-! ## `blaster_pretty`: `oracle`, `falsified`, `unknown` -/

-- valid: exactly `blaster` (the axiom, its warning), plus the `UPLC-RESULT` line.
-- An `example`, so that no theorem of the test suite depends on `blasterProven`:
-- the warning below is the evidence that the axiom is used.
/--
info: ✅ Valid
---
warning: declaration uses 'blasterProven' (SMT-verified, no proof term)
---
info: UPLC-RESULT {"status":"oracle","kernel":false,"cex":{},"lean":{}}
Blaster (z3) says the goal holds. There is no kernel proof: the goal is closed with the axiom Blaster.Tactic.blasterProven.
-/
#guard_msgs in
example : ∀ (r : TxOutRef), r.txOutRefIdx < 3 → r.txOutRefIdx < 4 := by
  blaster_pretty

-- A regression test for Blaster's translation of non-ASCII string literals: before
-- Blaster ee111d8, z3's model for this goal was `"\u{c3}\u{bf}"` (not a
-- counterexample, so status `falsified`); with the fix it is the literal itself,
-- and the refutation is checked by the kernel.
/--
error: UPLC-RESULT {"status":"refuted","kernel":true,"cex":{"b":"ff0061"},"lean":{"b":"⟨\"\\xff\\x00a\"⟩"},"closer":"decide"}
Counterexample (refutation checked by the kernel, closer decide):
  b := ⟨"\xff\x00a"⟩
Refutation:
example : ¬∀ (b : ByteString), b ≠ { data := "ÿ\x00a" } := by
  refute_with ⟨"\xff\x00a"⟩
-/
#guard_msgs in
example : ∀ (b : ByteString), b ≠ ⟨"\xff\x00a"⟩ := by
  blaster_pretty

-- z3 gives no concrete value for a function (`@@ArrowT2!val!0`): the default is
-- tried, does not refute, status `falsified`
/--
error: UPLC-RESULT {"status":"falsified","kernel":false,"cex":{"f":null},"lean":{"f":"default"},"defaults":["f"],"reason":"these values do not refute the statement: no closer proves\n  ¬default 0 = 0\n(tried decide, rfl, bool, cases, simp, simp_all, uplc_cex_closer)"}
Counterexample from Blaster, NOT confirmed: no kernel-checked refutation could be built from it.
  f := default  -- no concrete value in Blaster's model (@@ArrowT2!val!0): default
Why: these values do not refute the statement: no closer proves
  ¬default 0 = 0
(tried decide, rfl, bool, cases, simp, simp_all, uplc_cex_closer)
Attempted refutation:
example : ¬∀ (f : Int → Int), f 0 = 0 := by
  refute_with default
-/
#guard_msgs in
example : ∀ (f : Int → Int), f 0 = 0 := by
  blaster_pretty

-- z3 text that is neither Lean nor an abstract value: no Lean text (only a comment),
-- no snippet, status `falsified`
open Lean Elab Tactic Meta in
/--
info: UPLC-RESULT {"status":"falsified","kernel":false,"cex":{"x":null},"lean":{"x":null},"reason":"value of x: the counterexample text does not parse as Lean (not a Lean term: <input>:1:0: expected term):\n  #x0f"}
Counterexample from Blaster, NOT confirmed: no kernel-checked refutation could be built from it.
  -- x: no Lean term elaborates to this value; z3 gave: #x0f
Why: value of x: the counterexample text does not parse as Lean (not a Lean term: <input>:1:0: expected term):
  #x0f
-/
#guard_msgs in
example : True := by
  run_tac do
    let S ← Term.elabTerm (← `(∀ (x : Int), x < 3)) none
    let (r, _) ← analyse (← instantiateMVars S) #[("x", "#x0f")]
    logInfo (r.message (timings := false))
  trivial

-- Blaster cannot translate the CEK machine: status `unknown`, with Blaster's reason
/--
error: UPLC-RESULT {"status":"unknown","kernel":false,"cex":{},"lean":{},"reason":"Inductive datatype with instance parameters not supported: `BitVec"}
Blaster failed:
Inductive datatype with instance parameters not supported: `BitVec
-/
#guard_msgs in
example : ∀ (n : Int), Halts factorialHex.script [int n] (intV n) := by
  blaster_pretty

-- the same for `blaster_refute`
/--
error: UPLC-RESULT {"status":"unknown","kernel":false,"cex":{},"lean":{},"reason":"Inductive datatype with instance parameters not supported: `BitVec"}
Blaster failed:
Inductive datatype with instance parameters not supported: `BitVec
-/
#guard_msgs in
example : ¬ ∀ (n : Int), Halts factorialHex.script [int n] (intV n) := by
  blaster_refute

/-! ## Each checker rejects -/

open Lean Elab Meta in
/-- `#round_trip "text" : ty := value`: whether `text` elaborates back to `value`. -/
elab "#round_trip " text:str " : " ty:term " := " v:term : command =>
  Command.liftTermElabM do
    let ty ← Term.elabType ty
    let v ← instantiateMVars (← Term.elabTermEnsuringType v ty)
    logInfo m!"{← roundTrips text.getString ty v}"

/-- info: true -/
#guard_msgs in #round_trip "Data.I 5" : Data := Data.I 5
/-- info: false -/
#guard_msgs in #round_trip "Data.I 4" : Data := Data.I 5
/-- info: false -/
#guard_msgs in #round_trip "Data.I (5" : Data := Data.I 5
/-- info: false -/
#guard_msgs in #round_trip "Data.I \"5\"" : Data := Data.I 5
/-- info: false -/
#guard_msgs in #round_trip "Data.I _" : Data := Data.I 5

-- a plausible short name that does not resolve (an `export`ed type opened): rejected,
-- and the renderer picks a name that does
section
open CardanoLedgerApi.V3
/-- info: false -/
#guard_msgs in #round_trip "Vote.VoteYes" : CardanoLedgerApi.V3.Governance.Vote :=
  CardanoLedgerApi.V3.Governance.Vote.VoteYes

open Lean Elab Meta in
/-- info: some (Governance.Vote.VoteYes) -/
#guard_msgs in #eval show TermElabM Unit from do
  let v := mkConst ``CardanoLedgerApi.V3.Governance.Vote.VoteYes
  let ty := mkConst ``CardanoLedgerApi.V3.Governance.Vote
  logInfo m!"{(← renderLean v ty).map (·.line)}"
end

-- a value no Lean text elaborates back to: no text at all
open Lean Elab Meta in
/-- info: none -/
#guard_msgs in #eval show TermElabM Unit from do
  let ty := mkConst ``Int
  let v ← mkSorry ty (synthetic := false)
  logInfo m!"{(← renderLean v ty).map (·.line)}"

-- the axiom check
open Lean Meta in
/--
error: the proof uses axioms beyond propext, Quot.sound, Classical.choice: [sorryAx]
-/
#guard_msgs in #eval show MetaM Unit from do
  checkAxioms (← mkSorry (mkConst ``False) (synthetic := false))

open Lean Meta in
/--
error: the proof uses axioms beyond propext, Quot.sound, Classical.choice: [Lean.ofReduceBool]
-/
#guard_msgs in #eval show MetaM Unit from do
  checkAxioms (mkConst ``Lean.ofReduceBool)

open Lean Meta in
/--
error: the proof uses axioms beyond propext, Quot.sound, Classical.choice: [Blaster.Tactic.blasterProven]
-/
#guard_msgs in #eval show MetaM Unit from do
  checkAxioms (mkApp (mkConst ``Blaster.Tactic.blasterProven [levelZero]) (mkConst ``False))

open Lean Meta in
#guard_msgs in #eval show MetaM Unit from do
  checkAxioms (mkConst ``propext)

-- the kernel check: an ill-typed proof (`rfl : 1 = 2`) is rejected, a well-typed one accepted
-- (the message names a numbered auxiliary declaration: only its first words are shown)
open Lean Meta in
/--
info: rejected: the kernel rejects the refutation: (kernel) declaration type mismatch
---
info: accepted
-/
#guard_msgs in #eval show MetaM Unit from do
  for (lhs, rhs) in [(1, 2), (1, 1)] do
    try
      kernelCheck (← mkEq (mkNatLit lhs) (mkNatLit rhs)) (← mkEqRefl (mkNatLit 1))
      logInfo "accepted"
    catch ex =>
      let msg ← ex.toMessageData.toString
      logInfo m!"rejected: {(msg.splitOn ",").headD msg}"

end UplcProofTests.Cex.Negative
