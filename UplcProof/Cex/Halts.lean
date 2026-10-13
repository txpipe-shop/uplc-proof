import Lean
import UplcProof.Induction.Exec
import UplcProof.Induction.Run
import UplcProof.Cex.Refute

/-!
# `UplcProof.Cex.Halts`: refuting a `Halts` claim by running the program

An extension of `uplc_cex_closer` (tried last by `refute_with`, `refute_cex`,
`blaster_refute`, `blaster_pretty`):

* on `¬ Halts p args v` (also through `abbrev`s such as `Accepts`), with `p` and
  `args` closed: `UplcProof.Tactic.evalRun p args` runs the CEK machine to its
  final state `T` with a kernel-checked proof of `Reaches (initState p args) T`;
  if `T` is `Error` the claim is refuted by `not_halts_of_reaches_error`
  (`Fails.not_halts`); if `T` is `Halt w`, by `not_halts_of_reaches_halt`
  (`Halts.ne`) once `v ≠ w` is proved (`decide`, `cases`, `simp`);
* on `¬ Fails p args`: the run halts with some `w` (`Halts.of_reaches`,
  `Fails.not_halts`);
* on a hypothesis `Halts p args v` (or `Fails p args`) to discharge at the
  values: the run halts with `v` (or ends in `Error`).
-/

open Lean Meta Elab Tactic
open PlutusCore.UPLC.CekMachine

namespace UplcProof.Cex

/-- Closers for `v ≠ w` between two `CekValue`s. -/
private def neClosers : Array Closer :=
  refuteClosers.filter (·.name != "uplc_cex_closer")

/-- `evalRun`, off the heartbeat budget: no limit during the run (it is bounded by
    its fuel, `Tactic.maxSteps` CEK steps), and its heartbeats do not count against
    the enclosing tactic afterwards (the count is restored). Under the default
    `maxHeartbeats` (200000) a run of more than about 48,000 steps would not fit
    (the costs are in `Tactic.evalRun`'s doc). -/
private def evalRunUnbounded (p args : Expr) : TacticM (Expr × Expr) := do
  let hb ← IO.getNumHeartbeats
  try
    withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := 0 }) (Tactic.evalRun p args)
  finally
    IO.setNumHeartbeats hb

/-- A proof of `v ≠ w`, by `neClosers` on `v ≠ w`, then on `whnfD v ≠ w` (the
    claimed value may be written with definitions, `intV 3`). -/
private def proveNe? (v w : Expr) : TacticM (Option Expr) := do
  for v' in [v, ← whnfD v] do
    let hne ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``Ne #[v', w])
    if let .ok _ ← closeWith neClosers hne.mvarId! then return some (← instantiateMVars hne)
  return none

@[tactic cexCloser] def evalCexCloserRun : Tactic := fun _ => withMainContext do
  let g ← getMainGoal
  let ty ← instantiateMVars (← g.getType)
  if let some q ← negated? ty then
    let some (p, args, v?) ← Tactic.runGoal? q
      | throwError "uplc_cex_closer (run): not a `Halts`/`Fails` claim"
    let (T, hT) ← evalRunUnbounded p args
    match v? with
    | some v =>
        if T.isConstOf ``State.Error then
          g.assign (mkAppN (mkConst ``not_halts_of_reaches_error) #[p, args, v, hT])
        else if T.isAppOfArity ``State.Halt 1 then
          let w := T.appArg!
          match ← proveNe? v w with
          | some hne => g.assign (mkAppN (mkConst ``not_halts_of_reaches_halt) #[p, args, v, w, hT, hne])
          | none =>
              throwError "uplc_cex_closer (run): the run halts with{indentExpr w}\nwhich is not \
                shown to differ from the claimed value{indentExpr v}"
        else throwError "uplc_cex_closer (run): unexpected final state{indentExpr T}"
    | none =>
        unless T.isAppOfArity ``State.Halt 1 do
          throwError "uplc_cex_closer (run): the run fails, so the claim `Fails` holds"
        let w := T.appArg!
        let fails := mkApp2 (mkConst ``Fails) p args
        let pf ← withLocalDeclD `hf fails fun hf => do
          mkLambdaFVars #[hf] (mkAppN (mkConst ``Fails.not_halts)
            #[p, args, w, hf, mkAppN (mkConst ``Halts.of_reaches) #[p, args, w, hT]])
        g.assign pf
  else
    let some (p, args, v?) ← Tactic.runGoal? ty
      | throwError "uplc_cex_closer (run): not a `Halts`/`Fails` claim"
    let (T, hT) ← evalRunUnbounded p args
    match v? with
    | some v =>
        unless T.isAppOfArity ``State.Halt 1 do
          throwError "uplc_cex_closer (run): the run does not halt with a value:{indentExpr T}"
        unless ← isDefEq T.appArg! v do
          throwError "uplc_cex_closer (run): the run halts with{indentExpr T.appArg!}\nnot with{indentExpr v}"
        g.assign (mkAppN (mkConst ``Halts.of_reaches) #[p, args, v, hT])
    | none =>
        unless T.isConstOf ``State.Error do
          throwError "uplc_cex_closer (run): the run does not fail:{indentExpr T}"
        g.assign (mkAppN (mkConst ``Fails.of_reaches) #[p, args, hT])
  replaceMainGoal []

end UplcProof.Cex
