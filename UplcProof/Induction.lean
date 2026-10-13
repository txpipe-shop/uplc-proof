import UplcProof.Induction.Exec
import UplcProof.Induction.EqData
import UplcProof.Induction.Steps
import UplcProof.Induction.Sym
import UplcProof.Induction.Tactic
import UplcProof.Induction.Run

/-!
# `UplcProof.Induction`: proofs about UPLC runs for every input

* `UplcProof.Induction.Exec`: the theory (`exec`, `Reaches`, `Halts`, `Fails`,
  `initState`, and the lemmas to run a claim forward or refute one); no
  meta-programming.
* `UplcProof.Induction.EqData`: `Data` equality (`equalsData`) by evaluation
  (`dataEqB`, `equalsData_eq_dataEqB`), and as a proposition
  (`equalsData_eq_true_iff`); no meta-programming.
* `UplcProof.Induction.Steps`: one lemma per structural rule of the CEK machine's
  `step`, and per saturated builtin the engine computes directly (lists, pairs,
  `Data`, `ifThenElse`): the kernel checks an instance instead of running `step`; no
  meta-programming.
* `UplcProof.Induction.Sym`: symbolic execution of the CEK machine (structural steps
  and common builtins computed on the expression, the rest by `whnf`), loop-head
  detection, closed `equalsData` decided by evaluation, runs remembered and stated
  once (`sharedRun`), the per-call session that holds every cache (`withSession`),
  and the engine's options (`uplc.*`).
* `UplcProof.Induction.Tactic`: `uplc_induction`, `uplc_eq`, `uplc_cond`, and the
  engine (`Tactic.drive`, `Tactic.refute`, `Tactic.Ctx`).
* `UplcProof.Induction.Run`: `uplc_run` (no induction), `Tactic.runOn` and
  `Tactic.evalRun`.
-/
