import UplcProofTests.Induction
import UplcProofTests.Cex
import UplcProofTests.ScriptContext
import UplcProofTests.Auto
import UplcProofTests.Readme

/-!
# Tests of UplcProof

`lake build` builds them: every theorem with a check of its axioms, and every case
that must be refused with its expected error.

* `UplcProofTests.Induction`: `uplc_induction`, `uplc_run`, `evalRun`.
* `UplcProofTests.Cex`: counterexamples and refutations.
* `UplcProofTests.ScriptContext`: two validators' scripts over a full `ScriptContext`.
* `UplcProofTests.Auto`: `uplc_auto` on Aiken property tests.
* `UplcProofTests.Readme`: the README's examples.
-/
