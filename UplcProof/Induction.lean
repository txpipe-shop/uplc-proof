import UplcProof.Induction.Exec
import UplcProof.Induction.EqData
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
* `UplcProof.Induction.Sym`: symbolic execution of the CEK machine, loop-head
  detection, closed `equalsData` decided by evaluation.
* `UplcProof.Induction.Tactic`: `uplc_induction`, `uplc_eq`, `uplc_cond`.
* `UplcProof.Induction.Run`: `uplc_run` (no induction), `Tactic.runOn` and
  `Tactic.evalRun`.
-/
