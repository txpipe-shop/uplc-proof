import UplcProofTests.Cex.Positive
import UplcProofTests.Cex.Negative

/-!
# Tests of `UplcProof.Cex`

* `UplcProofTests.Cex.Positive`: `Pretty` on raw z3 text, rendering round trips,
  `blaster_refute` / `refute_with` / `refute_cex` theorems with axiom guards,
  `blaster_pretty`'s exact messages, a `Halts` claim refuted by running a real
  Aiken script.
* `UplcProofTests.Cex.Negative`: what must be rejected, with the expected error.
-/
