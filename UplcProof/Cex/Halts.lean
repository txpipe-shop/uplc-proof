import Lean
import UplcProof.Induction.Exec
import UplcProof.Induction.Run
import UplcProof.Encode
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
  values: the run halts with `v` (or ends in `Error`). A metavariable in `v` (a
  `refute_with _`) is assigned from the run;
* on a hypothesis `Verdict s c true` (`false`): `Accepts s c` (`¬ Accepts s c`) by
  the run, then `Verdict.of_accepts` (`Verdict.of_not_accepts`);
* on a hypothesis `∀ c, Halts p args (VCon (Data c)) → P c` (a validator call's
  premise: `P c` is typically `Verdict s c ok`): the run of `p` on `args`; if it
  halts with `Data e`, every such `c` is `e` (`Halts.data_eq`) and `P e` is
  discharged like any hypothesis; if it ends in `Error`, the premise holds
  vacuously.
-/

open Lean Meta Elab Tactic
open PlutusCore.UPLC.CekMachine

namespace UplcProof.Cex

/-- Closers for `v ≠ w` between two `CekValue`s. -/
private def neClosers : Array Closer :=
  refuteClosers.filter (·.name != "uplc_cex_closer")

/-- `evalRun`, off the heartbeat budget: no limit during the run (it is bounded by
    its fuel, `Tactic.maxSteps` CEK steps), and its heartbeats do not count against
    the enclosing tactic afterwards (the count is restored): how long the program
    runs is not the closer's budget to judge (the costs are in `Tactic.evalRun`'s
    doc). -/
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

/-- `Verdict s c b` with `b` the literal `true` (`false`): `s`, `c`, the goal
    `Accepts s c` (`¬ Accepts s c`) and the lemma back to the verdict. -/
private def verdictGoal? (ty : Expr) : MetaM (Option (Expr × Expr × Expr × Name)) := do
  let ty ← instantiateMVars ty
  unless ty.isAppOfArity ``Verdict 3 do return none
  let s := ty.getArg! 0
  let c := ty.getArg! 1
  let b ← whnfR (ty.getArg! 2)
  let acc := mkApp2 (mkConst ``Accepts) s c
  if b.isConstOf ``Bool.true then return some (s, c, acc, ``Verdict.of_accepts)
  if b.isConstOf ``Bool.false then return some (s, c, mkNot acc, ``Verdict.of_not_accepts)
  return none

/-- `c = e` where `c` is a `Data` and `e` its value: the `Data` inside `VCon (Data e)`. -/
private def dataValue? (w : Expr) : Option Expr :=
  if w.isAppOfArity ``PlutusCore.UPLC.CekValue.CekValue.VCon 1 &&
      w.appArg!.isAppOfArity ``PlutusCore.UPLC.Term.Const.Data 1 then
    some w.appArg!.appArg!
  else none

/-- Closes `g` by running a program (see the module doc for the goals it takes). -/
private partial def closeByRun (g : MVarId) : TacticM Unit := g.withContext do
  let ty ← instantiateMVars (← g.getType)
  -- `Verdict s c b`: the run of `s` on `c`
  if let some (s, c, q, lem) ← verdictGoal? ty then
    let g' ← mkFreshExprSyntheticOpaqueMVar q
    closeByRun g'.mvarId!
    g.assign (mkApp3 (mkConst lem) s c g')
    return
  -- a validator call's premise, `∀ c, Halts p args (VCon (Data c)) → P c`
  if let .forallE _ _ (.forallE _ _ _ _) _ := ty then
    if ← closePremise g ty then return
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
        -- `isDefEq` also assigns a value left open (`refute_with _`) from the run
        unless ← isDefEq T.appArg! v do
          throwError "uplc_cex_closer (run): the run halts with{indentExpr T.appArg!}\nnot with{indentExpr v}"
        g.assign (mkAppN (mkConst ``Halts.of_reaches) #[p, args, v, hT])
    | none =>
        unless T.isConstOf ``State.Error do
          throwError "uplc_cex_closer (run): the run does not fail:{indentExpr T}"
        g.assign (mkAppN (mkConst ``Fails.of_reaches) #[p, args, hT])
where
  /-- `g : ∀ c, Halts p args (VCon (Data c)) → P c` with `p`, `args` closed and `P` not
      about the hypothesis: closed by the run of `p` (see the module doc); `false` if
      `g` does not have this shape. -/
  closePremise (g : MVarId) (ty : Expr) : TacticM Bool :=
    forallBoundedTelescope ty (some 2) fun xs body => do
      let #[c, h] := xs | return false
      let hTy ← inferType h
      let some (p, args, some v) ← Tactic.runGoal? hTy | return false
      if p.containsFVar c.fvarId! || args.containsFVar c.fvarId! || body.containsFVar h.fvarId! then
        return false
      unless (dataValue? v).any (· == c) do return false
      let (T, hT) ← evalRunUnbounded p args
      if T.isConstOf ``State.Error then
        -- no run halts: the premise holds for every `c`, vacuously
        let no := mkApp (mkAppN (mkConst ``not_halts_of_reaches_error) #[p, args, v, hT]) h
        g.assign (← mkLambdaFVars #[c, h] (← mkFalseElim body no))
        return true
      unless T.isAppOfArity ``State.Halt 1 do return false
      let some e := dataValue? T.appArg!
        | throwError "uplc_cex_closer (run): the run of the premise's program halts with{indentExpr T.appArg!}\n\
            which is not a `Data`"
      -- `P e`, discharged at the run's value
      let motive ← mkLambdaFVars #[c] body
      let ge ← mkFreshExprSyntheticOpaqueMVar (motive.beta #[e])
      match ← closeWith hypClosers ge.mvarId! with
      | .ok _ => pure ()
      | .error _ =>
          throwError "uplc_cex_closer (run): the premise's program halts with{indentExpr e}\n\
            and at that value{indentExpr (motive.beta #[e])}\ndoes not hold"
      -- every `c` the premise speaks of is `e`
      let hE := mkAppN (mkConst ``Halts.of_reaches) #[p, args, T.appArg!, hT]
      let hce ← mkAppM ``Halts.data_eq #[h, hE]
      let pf ← mkEqNDRec motive ge (← mkEqSymm hce)
      g.assign (← mkLambdaFVars #[c, h] pf)
      return true

@[tactic cexCloser] def evalCexCloserRun : Tactic := fun _ => withMainContext do
  closeByRun (← getMainGoal)
  replaceMainGoal []

end UplcProof.Cex
