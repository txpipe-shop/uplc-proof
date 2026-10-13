import Lean
import Blaster
import UplcProof.Cex.Pretty
import UplcProof.Cex.Bridge
import UplcProof.Cex.Render
import UplcProof.Cex.Json
import UplcProof.Cex.Refute
import UplcProof.Cex.Report

/-!
# `UplcProof.Cex.Tactic`: Blaster, then a kernel-checked refutation

* `blaster_pretty (opts)*`: a drop-in for `blaster`. Falsified: the counterexample
  is turned into a refutation of `∀ (free variables and hypotheses of the
  goal), goal` (a proof of its negation), checked by the kernel in a throwaway environment, and the tactic
  fails with the `UPLC-RESULT` message (status `refuted`, or `falsified` when no
  kernel-checked refutation could be built). Valid: exactly `blaster` (the goal
  is closed with the axiom `Blaster.Tactic.blasterProven`, with `blaster`'s
  warning) plus an info message `UPLC-RESULT` with status `oracle`.
  Undetermined: as `blaster` (the goal is replaced by Blaster's optimized form),
  plus an info message with status `unknown`.
* `blaster_refute (opts)*`: on a goal `¬ S`, runs Blaster on `S`; Falsified: the
  refutation closes the goal (the error is the `UPLC-RESULT` message if none can
  be built); Valid: an error, Blaster says `S` holds; Undetermined: an error.

If Blaster itself fails (an error, or a runtime exception such as deep recursion
on a large term), both tactics fail with an `UPLC-RESULT` line of status
`unknown` (Blaster's message in `"reason"`), and Blaster's log messages are
dropped.

Programmatic API (for `uplc_auto`):
* `runBlaster (stmt : Expr) (sOpts : BlasterOptions) : TacticM BlasterOutcome` —
  Blaster's messages are left in the log (callers restore it if they want); its
  heartbeats do not count against the caller;
* `collectValues (S : Expr) (entries : Array (String × String)) : TacticM (Array Candidate)` —
  the values of `S`'s binders from Blaster's entries (or defaults), as `analyse`
  reads them;
* `analyse (S : Expr) (entries : Array (String × String)) : TacticM (Report × Option Expr)` —
  the report on `S` from Blaster's entries, with the kernel-checked proof of
  `¬ S` when the status is `refuted`;
* `blasterReport (goal : MVarId) (sOpts : BlasterOptions) : TacticM (Report × BlasterOutcome × Option Expr)` —
  `blaster_pretty`'s analysis without closing or failing: the report on
  `¬ ∀ (context), goal`, and the proof of that negation if refuted.
-/

open Lean Elab Tactic Meta
open Blaster.Optimize Blaster.Smt Blaster.Options Blaster.Syntax

namespace UplcProof.Cex

/-- What Blaster said. -/
inductive BlasterOutcome where
  /-- Blaster says the proposition holds (no kernel proof). -/
  | valid
  /-- The model, as `(binder name, raw z3 value)` entries. -/
  | falsified (entries : Array (String × String))
  /-- Blaster's optimized goal. -/
  | undetermined (optExpr : Expr)
deriving Inhabited

/-- Runs Blaster (z3) on the proposition `stmt`, as `blaster` does: without a
    heartbeat limit, from a heartbeat count of 0. The caller's heartbeat count is
    restored afterwards (also when Blaster throws), so Blaster's work does not
    count against it. Blaster's own messages stay in the log. -/
def runBlaster (stmt : Expr) (sOpts : BlasterOptions) : TacticM BlasterOutcome := do
  let env := {(default : TranslateEnv) with optEnv.options.solverOptions := sOpts}
  let hb ← IO.getNumHeartbeats
  let ((result, optExpr), _) ← try
      withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := 0 }) do
        IO.setNumHeartbeats 0
        Translate.main stmt (logUndetermined := false) |>.run env
    finally
      IO.setNumHeartbeats hb
  match result with
  | .Valid => return .valid
  | .Falsified cex =>
      -- each entry is `"<binder>: <value>"` plus a trailing character Blaster drops
      let entries := cex.filterMap fun s => (splitEntry (s.dropRight 1)).toOption
      return .falsified entries.toArray
  | .Undetermined => return .undetermined optExpr

/-- A binder's value, before the refutation is attempted. -/
structure Candidate where
  /-- The binder's name, as in the statement. -/
  name : Name
  /-- The binder's type (earlier values substituted). -/
  type : Expr
  /-- The value, if one could be built. -/
  value? : Option Expr := none
  /-- The clean Lean text the value was elaborated from. -/
  source? : Option String := none
  /-- z3's text for it, cleaned for display. -/
  z3? : Option String := none
  /-- Why a default value was used. -/
  note? : Option String := none
  /-- No concrete value in Blaster's model: a default value was used. -/
  isDefault : Bool := false
  /-- Why there is no value. -/
  error? : Option String := none
deriving Inhabited

/-- The values of `S`'s binders from Blaster's entries, matched by name (the
    `k`-th entry named `x` to the `k`-th binder named `x`). A binder the model
    leaves out, or gives only an abstract value for (`$0`), gets a default value
    (`mkDefault?`). Never throws on a bad value: it is recorded. -/
partial def collectValues (S : Expr) (entries : Array (String × String)) : TacticM (Array Candidate) := do
  let seen ← IO.mkRef ({} : Std.HashMap String Nat)
  let rec go (ty : Expr) (acc : Array Candidate) : TacticM (Array Candidate) := do
    let ty' ← if ty.isForall || ty.isLet then pure ty else do
      let t ← whnfR ty
      pure (if t.isForall || t.isLet then t else ty)
    match ty' with
    | .letE _ _ v b _ => go (b.instantiate1 v) acc
    | .forallE n d b _ =>
        if ← isProp d then
          go (b.instantiate1 (← mkFreshExprMVar d)) acc
        else
          let key := n.eraseMacroScopes.toString
          let k := (← seen.get).getD key 0
          seen.modify (·.insert key (k + 1))
          let mut c : Candidate := { name := n, type := d }
          match (entries.filter (·.1 == key))[k]? with
          | some (_, raw) =>
            if isAbstractValue raw then
              -- z3's `$0` / `T!val!0`: no concrete value, the binder is unconstrained
              let z3 := raw.trim
              match ← mkDefault? d with
              | some v =>
                  let note := s!"no concrete value in Blaster's model ({z3}): default"
                  c := { c with value? := some v, isDefault := true, z3? := some z3, note? := some note }
              | none =>
                  let why := s!"{key} has no concrete value in Blaster's model ({z3}) and its type has no default value"
                  c := { c with z3? := some z3, error? := some why }
            else
              c := { c with z3? := (prettyCex raw).toOption <|> some raw }
              let r ← tryCatchRuntimeEx (Except.ok <$> elabCexValue raw d)
                fun ex => Except.error <$> ex.toMessageData.toString
              match r with
              | .ok (v, text) => c := { c with value? := some v, source? := some text }
              | .error why => c := { c with error? := some why }
          | none =>
              match ← mkDefault? d with
              | some v => c := { c with value? := some v, isDefault := true,
                                        note? := some "not in Blaster's model: default" }
              | none => c := { c with error? := some s!"{key} is not in Blaster's model and its type has no default value" }
          let v ← match c.value? with | some v => pure v | none => mkFreshExprMVar d
          go (b.instantiate1 v) (acc.push c)
    | _ => return acc
  go S #[]

private def ms (t0 : Nat) : IO Nat := return (← IO.monoMsNow) - t0

/-- The report on `S` from Blaster's entries; with the proof of `¬ S` (checked by
    the kernel) when the status is `refuted`. -/
def analyse (S : Expr) (entries : Array (String × String)) : TacticM (Report × Option Expr) := do
  let t0 ← IO.monoMsNow
  let cands ← collectValues S entries
  let mut proof? : Option Expr := none
  let mut closer? : Option String := none
  let mut reason? : Option String := none
  let mut kernel := false
  match cands.find? (·.error?.isSome) with
  | some c => reason? := some s!"value of {c.name.eraseMacroScopes}: {c.error?.getD ""}"
  | none =>
      let g ← mkFreshExprSyntheticOpaqueMVar (mkNot S)
      let s ← saveState
      -- runtime exceptions (heartbeats, recursion depth) are failures like any other
      let res ← tryCatchRuntimeEx
        (Except.ok <$> refuteCore g.mvarId! fun i _ _ => do
          let some c := cands[i]? | throwError "no value for binder {i}"
          let some v := c.value? | throwError "no value for {c.name}"
          return (v, c.source?, c.note?))
        fun ex => do
          s.restore
          return .error (← ex.toMessageData.toString)
      match res with
      | .error why => reason? := some why
      | .ok r =>
          closer? := some r.closer
          let kres ← tryCatchRuntimeEx (do kernelCheck (mkNot S) r.proof; return none)
            fun ex => some <$> ex.toMessageData.toString
          match kres with
          | none =>
              kernel := true
              proof? := some r.proof
          | some why => reason? := some why
  let tRefute ← ms t0
  let t1 ← IO.monoMsNow
  -- names in the JSON objects must be distinct
  let names := distinctNames (cands.map (·.name.eraseMacroScopes.toString))
  let mut es : Array Entry := #[]
  for (c, name) in cands.zip names do
    match c.value? with
    | some v =>
        let e ← tryCatchRuntimeEx (mkEntry name v c.type c.source? c.z3? c.note? c.isDefault)
          fun _ => pure { name, z3? := c.z3?, note? := c.note?, isDefault := c.isDefault }
        es := es.push e
    | none =>
        es := es.push { name, z3? := c.z3?, note? := c.error?, isDefault := c.isDefault }
  let negation? ← renderProp (mkNot S)
  let status := if kernel then Status.refuted else .falsified
  let tRender ← ms t1
  let report : Report := {
    status := status
    kernel := kernel
    entries := es
    negation? := negation?
    closer? := closer?
    reason? := reason?
    timings := #[("refute", tRefute), ("render", tRender)] }
  return (report, proof?)

/-- Reverts the propositional hypotheses into the goal (as `blaster` does). -/
private def revertProps (goal : MVarId) : MetaM MVarId :=
  goal.withContext do
    let mut hyps := #[]
    for decl in ← getLCtx do
      if decl.isImplementationDetail then continue
      if ← isProp decl.type then hyps := hyps.push decl.fvarId
    hyps.foldrM (fun h g => do let (_, g) ← g.revert #[h]; return g) goal

/-- `∀ (free variables of the context), type`. -/
private def closeOverContext (type : Expr) : MetaM Expr := do
  let mut fvars := #[]
  for decl in ← getLCtx do
    unless decl.isImplementationDetail do fvars := fvars.push decl.toExpr
  instantiateMVars (← mkForallFVars fvars type)

/-- `blaster_pretty`'s analysis of `goal` (the caller reverts the `Prop`
    hypotheses first, with `revertProps`, as `blaster_pretty` does), without
    closing it or failing: the outcome, the report (on `¬ ∀ (context), goal` when
    falsified) and the kernel-checked proof of that negation when refuted.
    Blaster's own messages are dropped, except `✅ Valid`. If Blaster throws (also
    a runtime exception), its messages are dropped and the exception rethrown. -/
def blasterReport (goal : MVarId) (sOpts : BlasterOptions) :
    TacticM (Report × BlasterOutcome × Option Expr) := goal.withContext do
  let msgs := (← getThe Core.State).messages
  let t0 ← IO.monoMsNow
  -- `tryCatchRuntimeEx`: also a runtime exception (deep recursion on a large term)
  let outcome ← tryCatchRuntimeEx (runBlaster (← goal.getType) sOpts) fun ex => do
    modifyThe Core.State fun s => { s with messages := msgs }
    throw ex
  let tBlaster ← ms t0
  match outcome with
  | .valid =>
      return ({ status := .oracle, timings := #[("blaster", tBlaster)] }, outcome, none)
  | .undetermined _ =>
      modifyThe Core.State fun s => { s with messages := msgs }
      return ({ status := .unknown, timings := #[("blaster", tBlaster)] }, outcome, none)
  | .falsified entries =>
      modifyThe Core.State fun s => { s with messages := msgs }
      let S ← closeOverContext (← goal.getType)
      let (r, proof?) ← analyse S entries
      return ({ r with timings := #[("blaster", tBlaster)] ++ r.timings }, outcome, proof?)

/-- `blaster_pretty (opts)*` is `blaster (opts)*`, with a counterexample that is
    Lean and a refutation checked by the kernel (see the module doc). -/
syntax (name := blasterPretty) "blaster_pretty" (solveOption)* : tactic

@[tactic blasterPretty] def evalBlasterPretty : Tactic := fun stx => withMainContext do
  let sOpts ← parseSolveOptions stx[1].getArgs default
  let timings := uplc.cex.timings.get (← getOptions)
  let goal ← revertProps (← getMainGoal)
  goal.withContext do
    let t0 ← IO.monoMsNow
    -- also a runtime exception: the failure is reported with its `UPLC-RESULT` line
    let (report, outcome, _) ← tryCatchRuntimeEx (blasterReport goal sOpts) fun ex => do
      let r : Report := { status := .unknown, reason? := some (← ex.toMessageData.toString),
                          timings := #[("blaster", ← ms t0)] }
      throwError "{r.resultLine timings}\nBlaster failed:\n{ex.toMessageData}"
    match outcome with
    | .valid =>
        -- exactly `blaster`: the axiom, and its warning
        let ty ← instantiateMVars (← goal.getType)
        goal.assign (mkApp (mkConst ``Blaster.Tactic.blasterProven [← getLevel ty]) ty)
        if (← getOptions).getBool `warn.sorry true then
          logWarningAt stx "declaration uses 'blasterProven' (SMT-verified, no proof term)"
        logInfoAt stx (report.message timings)
        replaceMainGoal []
    | .undetermined optExpr =>
        let newGoal ← goal.replaceTargetDefEq optExpr
        logInfoAt stx (report.message timings)
        replaceMainGoal [newGoal]
    | .falsified _ => throwError (report.message timings)

/-- `blaster_refute (opts)*` closes `¬ S` with a refutation built from Blaster's
    counterexample to `S` (see the module doc). -/
syntax (name := blasterRefute) "blaster_refute" (solveOption)* : tactic

@[tactic blasterRefute] def evalBlasterRefute : Tactic := fun stx => withMainContext do
  let sOpts ← parseSolveOptions stx[1].getArgs default
  let timings := uplc.cex.timings.get (← getOptions)
  let goal ← getMainGoal
  let some S ← negated? (← goal.getType)
    | throwError "blaster_refute: the goal is not a negation `¬ S`:{indentExpr (← goal.getType)}"
  let msgs := (← getThe Core.State).messages
  let t0 ← IO.monoMsNow
  -- also a runtime exception: the failure is reported with its `UPLC-RESULT` line
  let outcome ← tryCatchRuntimeEx (runBlaster S sOpts) fun ex => do
    modifyThe Core.State fun s => { s with messages := msgs }
    let r : Report := { status := .unknown, reason? := some (← ex.toMessageData.toString),
                        timings := #[("blaster", ← ms t0)] }
    throwError "{r.resultLine timings}\nBlaster failed:\n{ex.toMessageData}"
  modifyThe Core.State fun s => { s with messages := msgs }
  let tBlaster ← ms t0
  match outcome with
  | .valid =>
      let r : Report := { status := .oracle, timings := #[("blaster", tBlaster)] }
      throwError "{r.resultLine timings}\nblaster_refute: Blaster says it holds (z3: unsat): \
        the statement cannot be refuted."
  | .undetermined _ =>
      let r : Report := { status := .unknown, timings := #[("blaster", tBlaster)] }
      throwError "{r.resultLine timings}\nblaster_refute: Blaster could not decide the statement."
  | .falsified entries =>
      let (r, proof?) ← analyse S entries
      let r := { r with timings := #[("blaster", tBlaster)] ++ r.timings }
      match proof? with
      | some proof =>
          goal.assign proof
          replaceMainGoal []
      | none => throwError (r.message timings)

end UplcProof.Cex
