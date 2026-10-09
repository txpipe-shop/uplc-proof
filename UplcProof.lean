import UplcProof.Encode
import UplcProof.Induction
import UplcProof.Cex
import UplcProof.Auto
import UplcProof.Invariant

/-!
# UplcProof

Proofs about compiled Aiken (UPLC) scripts for every input, checked by Lean's
kernel, and counterexamples that are Lean terms when a claim is false.

* `UplcProof.Induction`: `Halts`, `Fails`; `uplc_induction` and `uplc_run`.
* `UplcProof.Encode`: arguments as `aiken export` passes them; `Accepts`, `Verdict`.
* `UplcProof.Cex`: Blaster counterexamples as JSON and Lean terms; `refute_with`,
  `refute_cex`, `blaster_refute`, `blaster_pretty`.
* `UplcProof.Auto`: `uplc_auto`, one tactic for an Aiken property test.
* `UplcProof.Invariant`: `Reachable.invariant`.
-/
