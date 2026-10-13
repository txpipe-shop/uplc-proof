import UplcProofTests.Induction.Positive
import UplcProofTests.Induction.Negative
import UplcProofTests.Induction.Run

/-!
# Tests of `UplcProof.Induction`

* `UplcProofTests.Induction.Positive`: `uplc_induction` on the fixtures of
  `Tests/Induction/Scripts/`, with axiom guards.
* `UplcProofTests.Induction.Negative`: what `uplc_induction` must refuse, with the
  expected error.
* `UplcProofTests.Induction.Run`: `uplc_run` and `evalRun` (runs without
  induction), and the lemmas about runs.
-/
