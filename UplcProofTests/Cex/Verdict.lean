import UplcProofTests.ScriptContext
import UplcProofTests.Induction.Negative

/-!
# Tests: `refute_with` on claims about validator calls

Kreisel's Aiken prover states a property test that calls a validator with, per call,
the script context a script builds from the test's inputs, and the validator's
verdict on it as a hypothesis: `Halts ctx [enc x̄] (VCon (Data c)) → Verdict v c ok →
…`. Here the context builder is the identity (`idScript`, written as a UPLC term),
the validator is `time_lock` (`UplcProofTests.ScriptContext`: it rejects
`tlCtx 18456` and accepts `tlCtx 18457`), and the conclusion says what the test
says of the verdict.

* `uplc_cex_closer` discharges `Verdict v c true` (`false`) by running `v` on `c`;
* `refute_with … _ …` leaves the context `c` open: the hypothesis
  `Halts ctx … (VCon (Data c))` gives it, by running `ctx`;
* the newer form, one premise per call `(∀ c, Halts ctx … (VCon (Data c)) →
  Verdict v c ok)`, is discharged by the same run.
-/

open PlutusCore.Data (Data)
open PlutusCore.UPLC.Term (Term Program Version)
open CardanoLedgerApi.IsData.Class (IsData)
open UplcProof UplcProof.Cex
open UplcProofTests.ScriptContext

namespace UplcProofTests.Cex.Verdict

/-- A context builder that returns its argument. -/
def idScript : Program := .Program (.Version 1 1 0) (.Lam "x" (.Var "x"))

/-- The context of `time_lock` for a lower bound, as `Data`. -/
abbrev ctxData (lower : Int) : Data := IsData.toData (tlCtx lower)

/-! ## A `Verdict` hypothesis, and the context left open (`_`) -/

/-- "`time_lock` never accepts", with the context a binder: FALSE (it accepts at 18457). -/
abbrev NeverAccepts : Prop :=
  ∀ (lower : Int) (c : Data) (ok : Bool),
    Halts idScript [data (ctxData lower)] (.VCon (.Data c)) →
    Verdict timeLock.script c ok →
    ok = false

theorem neverAccepts_refuted : ¬ NeverAccepts := by
  refute_with 18457, _, true

/-- The context written out gives the same refutation. -/
theorem neverAccepts_refuted' : ¬ NeverAccepts := by
  refute_with 18457, ctxData 18457, true

/-- "`time_lock` always accepts": FALSE (it rejects at 18456): `Verdict … false`. -/
abbrev AlwaysAccepts : Prop :=
  ∀ (lower : Int) (c : Data) (ok : Bool),
    Halts idScript [data (ctxData lower)] (.VCon (.Data c)) →
    Verdict timeLock.script c ok →
    ok = true

theorem alwaysAccepts_refuted : ¬ AlwaysAccepts := by
  refute_with 18456, _, false

/-! ## One premise per call -/

/-- "`time_lock` never accepts", with one premise per call: FALSE. -/
abbrev NeverAcceptsPremise : Prop :=
  ∀ (lower : Int) (ok : Bool),
    (∀ c, Halts idScript [data (ctxData lower)] (.VCon (.Data c)) →
      Verdict timeLock.script c ok) →
    ok = false

theorem neverAcceptsPremise_refuted : ¬ NeverAcceptsPremise := by
  refute_with 18457, true

abbrev AlwaysAcceptsPremise : Prop :=
  ∀ (lower : Int) (ok : Bool),
    (∀ c, Halts idScript [data (ctxData lower)] (.VCon (.Data c)) →
      Verdict timeLock.script c ok) →
    ok = true

theorem alwaysAcceptsPremise_refuted : ¬ AlwaysAcceptsPremise := by
  refute_with 18456, false

/-! ## Must reject -/

/-- The wrong verdict: `time_lock` rejects at 18456, so `Verdict … true` does not hold. -/
example : ¬ NeverAccepts := by
  fails_with "does not hold at these values" (refute_with 18456, _, true)
  refute_with 18457, _, true

example : ¬ NeverAcceptsPremise := by
  fails_with "does not hold at these values" (refute_with 18456, true)
  refute_with 18457, true

/-- `_` where no hypothesis gives the value. -/
abbrev Unrelated : Prop := ∀ (c : Data) (ok : Bool), Verdict timeLock.script c ok → ok = false

example : ¬ Unrelated ∨ True := by
  fails_with "does not give the value left open" (left; refute_with _, true)
  right; trivial

/-- `_` for a context the hypothesis's run does not give (another value is claimed
    than the one the builder returns). -/
example : ¬ NeverAccepts := by
  fails_with "does not hold at these values" (refute_with 18457, ctxData 18456, true)
  refute_with 18457, _, true

/-- info: 'UplcProofTests.Cex.Verdict.neverAccepts_refuted' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms neverAccepts_refuted
/-- info: 'UplcProofTests.Cex.Verdict.neverAccepts_refuted'' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms neverAccepts_refuted'
/-- info: 'UplcProofTests.Cex.Verdict.alwaysAccepts_refuted' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms alwaysAccepts_refuted
/-- info: 'UplcProofTests.Cex.Verdict.neverAcceptsPremise_refuted' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms neverAcceptsPremise_refuted
/-- info: 'UplcProofTests.Cex.Verdict.alwaysAcceptsPremise_refuted' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms alwaysAcceptsPremise_refuted

end UplcProofTests.Cex.Verdict
