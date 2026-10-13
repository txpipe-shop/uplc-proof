import Lean
import UplcProof.Induction.Exec
import UplcProof.Induction.Sym
import UplcProof.Induction.Tactic

/-!
# `uplc_run` and `evalRun`: runs without induction

* `uplc_run` proves `Halts p args v` (or `Fails p args`) by symbolic execution
  alone: the machine runs from the initial state and, when the next step depends
  on symbolic data, splits on the condition `c` of the `if` it is at (one branch
  knows `c`, the other `¬c`). A branch whose hypotheses are contradictory
  (`omega`, `simp_all`) is closed there; every other branch must reach the claimed
  target. Loops on data of known shape just run; a loop on symbolic data is for
  `uplc_induction` (`uplc_run` stops on it: stuck, or past `uplc.maxSplits` nested
  splits). `uplc_run [t₁, t₂]` adds lemmas for the value equalities (the
  claim's own definitions are added automatically). A symbolic `Bool` argument
  (`bool b`) is not an `if` condition, it is matched on: `cases b <;> uplc_run`.
  It is `uplc_induction`'s engine (`Tactic.drive`) with no induction variable.
* `Tactic.runOn g closer? phase` is `uplc_run` on the goal `g`, for tactics built on
  it: `closer?` is tried last at each leaf that neither reaches the target nor
  has contradictory hypotheses (`Ctx.closer?`).
* `Tactic.evalRun p args` runs a closed program to its final state and proves that
  the run gets there: with `not_halts_of_reaches_error` and
  `not_halts_of_reaches_halt` (in `Exec`), what refuting a claim on a concrete input
  needs.

Nothing here is trusted: the tactics build terms the kernel checks.
-/

open Lean Meta Elab Tactic
open PlutusCore.UPLC.Term PlutusCore.UPLC.CekValue PlutusCore.UPLC.CekMachine
open UplcProof.Sym

namespace UplcProof.Tactic

/-- A context for `drive` with no induction variable: the run only splits on the
    conditions of `if`s. -/
def runCtx (phase : String) (closer? : Option (MVarId → TacticM Bool))
    (ts : SimpArgs := ⟨#[]⟩) : Ctx :=
  { τ := mkConst ``Nat, res? := none, gen? := none, ts, candidates := #[],
    split? := none, phase, closer? }

/-- `Halts p args v` or `Fails p args`, up to reducible definitions (`Accepts s c`):
    the program, its arguments and the claimed value (`none` for `Fails`). -/
def runGoal? (ty : Expr) : MetaM (Option (Expr × Expr × Option Expr)) := do
  let ty ← whnfR ty
  match_expr ty with
  | Halts p args v => return some (p, args, some v)
  | Fails p args => return some (p, args, none)
  | _ => return none

/-- Proves `g : Halts p args v` (or `Fails p args`) by symbolic execution, splitting
    on `if` conditions over symbolic data; no induction. `closer?`: tried last at a
    leaf that does not reach the target (its effects are undone if it fails).
    `phase` names the run in error messages; `simpArgs` are extra lemmas for the
    value equalities (`uplc_run [simpArgs]`), besides the claim's own definitions.
    Throws if a branch neither reaches the target nor is closed. -/
def runOn (g : MVarId) (closer? : Option (MVarId → TacticM Bool)) (phase : String := "run")
    (simpArgs : Array Syntax := #[]) : TacticM Unit := g.withContext do
  let ty ← instantiateMVars (← g.getType)
  let some (p, args, v?) ← runGoal? ty
    | throwError "{phase}: expected a goal `Halts p args v` or `Fails p args`, got{indentExpr ty}"
  let specs ← match v? with
    | some v => specDefs v
    | none => pure #[]
  let ts : SimpArgs := ⟨mkSepArray (simpArgs ++ specs) (mkAtom ",")⟩
  -- elaborate the user's lemmas now: `uplc_eq` failures are caught later, and would hide a typo
  unless simpArgs.isEmpty do
    discard <| Tactic.run (← mkFreshExprMVar (mkConst ``True)).mvarId!
      (withoutRecover (evalTactic (← `(tactic| simp only [$ts,*]))))
  let T := match v? with | some v => mkApp (mkConst ``State.Halt) v | none => mkConst ``State.Error
  let g' ← mkFreshExprSyntheticOpaqueMVar
    (mkApp2 (mkConst ``Reaches) (mkApp2 (mkConst ``initState) p args) T)
  g.assign <| match v? with
    | some v => mkApp4 (mkConst ``Halts.of_reaches) p args v g'
    | none => mkApp3 (mkConst ``Fails.of_reaches) p args g'
  drive (runCtx phase closer? ts) g'.mvarId!

/-- The types `evalLeaves` goes through (by their constructors). -/
private def valueTypes : List Name :=
  [``PlutusCore.UPLC.CekMachine.State, ``CekValue, ``PlutusCore.UPLC.Term.Const, ``PlutusCore.Data.Data, ``List, ``Prod]

/-- `e` with its closed `Bool` and `Int` leaves computed to literals (`lessThanInteger 3 4`
    to `true`, `addInteger 3 4` to `7`), through the constructors of the types of
    values (`valueTypes`; not into closures). A leaf that does not reduce to a
    literal is kept. The result is definitionally equal to `e`. -/
private partial def evalLeaves (e : Expr) : MetaM Expr := do
  if e.hasFVar || e.hasMVar then return e
  let ty ← whnfR (← inferType e)
  if ty.isConstOf ``Bool then
    let e' ← whnfD e
    return if e'.isConstOf ``Bool.true || e'.isConstOf ``Bool.false then e' else e
  if ty.isConstOf ``Int then
    let natLit? (n : Expr) : MetaM (Option Nat) := do
      let .lit (.natVal k) ← whnfD n | return none
      return some k
    let e' ← whnfD e
    match_expr e' with
    | Int.ofNat n => return (← natLit? n).map (fun k => toExpr (Int.ofNat k)) |>.getD e
    | Int.negSucc n => return (← natLit? n).map (fun k => toExpr (Int.negSucc k)) |>.getD e
    | _ => return e
  let some tn := ty.getAppFn.constName? | return e
  unless valueTypes.contains tn do return e
  let some c := e.getAppFn.constName? | return e
  let some (.ctorInfo ci) := (← getEnv).find? c | return e
  let args := e.getAppArgs
  let mut newArgs := args
  for i in [ci.numParams : args.size] do
    newArgs := newArgs.set! i (← evalLeaves args[i]!)
  return mkAppN e.getAppFn newArgs

/-- A piece of `evalRun`'s proof. -/
private inductive RunLink where
  /-- `count` CEK steps from `a` to `b`: `exec a count = b`, checked by the kernel. -/
  | exec (a b : Expr) (count : Nat)
  /-- `a = b` by `proof`: a closed `equalsData` replaced by its value. -/
  | eq (a b proof : Expr)

/-- Runs the closed program `p` on the closed arguments `args` (terms of types
    `Program` and `List Term`) to its final state `T`, `State.Halt v` or
    `State.Error`, and returns `T` with a proof of `Reaches (initState p args) T`:
    one `Reaches.of_exec c rfl` per stretch of at most 100 steps.

    A closed `equalsData x y` does not reduce (`eqData` is defined by well-founded
    recursion): where the run waits on one (an `if` on it), and where one is left in
    the final value, it is decided by evaluating `dataEqB x y`
    (`Sym.rewriteEqualsData`); the state is rewritten (`Reaches.of_eq_left`) and the
    run goes on. In `T`, closed `Bool` and `Int` leaves are then computed
    (`evalLeaves`); other leaves (`ByteString`, `String`) stay as the run left them.

    Throws if the run is stuck otherwise (the program or the arguments are not
    closed, or a builtin whose semantics does not reduce: `DecodeUtf8`, by
    well-founded recursion too), or takes more than `fuel` steps.

    The segments `exec a c = b` are checked by the kernel only (each step was
    computed by `whnf`; the kernel re-runs it). Cost: about 4.1 `maxHeartbeats`
    units per step, so runs of up to about 48,000 steps fit in the default 200,000
    (`fib 13`: 33,891 steps, 137,000 units, 3.6 s); longer runs need
    `set_option maxHeartbeats 0` (`fib 14`: 54,861 steps, 223,000 units, 6.0 s;
    `fib 15`: 88,791 steps), and the kernel's check then takes about as long again
    (timings: Apple M5, Lean 4.24). A full `ScriptContext` run of a real validator
    is far shorter (1,228 steps, two `equalsData`).

    To refute `Halts p args v`: if `T` is `Error`, `not_halts_of_reaches_error proof`;
    if `T` is `Halt w`, `not_halts_of_reaches_halt proof (hne : v ≠ w)`. -/
def evalRun (p args : Expr) (fuel : Nat := maxSteps) : TacticM (Expr × Expr) := do
  let cache ← IO.mkRef {}
  let st0 := mkApp2 (mkConst ``initState) p args
  let mut cur ← norm cache st0
  let mut links : Array RunLink := #[]
  let mut steps := 0
  repeat
    let stop ← runUntil cache cur (fun _ => pure false) (fuel - steps)
    let mut a := cur
    for (b, c) in stop.segments do
      links := links.push (.exec a b c)
      a := b
    steps := steps + stop.steps
    cur := stop.state
    -- a closed `equalsData` the run waits on (stuck), or left in the final value
    let focus := if ctorName? cur == some ``State.Return then cur.appArg! else cur
    let around := if stop.stuck then (branchCondition? focus <|> branchCondition? cur).getD focus
      else cur
    let some e := findOutsideEnv? isClosedEqualsData around <|>
        (if stop.stuck then findOutsideEnv? isClosedEqualsData cur else none)
      | if stop.stuck then
          throwShort m!"evalRun: the run is stuck after {steps} steps (are the program and its \
            arguments closed? a builtin whose semantics does not reduce, as `DecodeUtf8`?):\
            {indentExpr cur}"
        else break
    let (st', h) ← rewriteEqualsData cache cur e
    links := links.push (.eq cur st' h)
    cur := st'
  let Tl := cur
  let T ← evalLeaves Tl
  unless ← withNewMCtxDepth (isDefEq Tl T) do
    throwError "evalRun: internal error: the computed final state differs from the run's"
  let stateTy := mkConst ``PlutusCore.UPLC.CekMachine.State
  let mut proof := mkApp3 (mkConst ``Reaches.of_eq) Tl T (mkApp2 (mkConst ``Eq.refl [1]) stateTy Tl)
  for l in links.reverse do
    proof := match l with
      | .exec a b c => mkAppN (mkConst ``Reaches.of_exec)
          #[a, b, T, mkNatLit c, mkApp2 (mkConst ``Eq.refl [1]) stateTy b, proof]
      | .eq a b h => mkAppN (mkConst ``Reaches.of_eq_left) #[a, b, T, h, proof]
  return (T, ← mkExpectedTypeHint proof (mkApp2 (mkConst ``Reaches) st0 T))

end UplcProof.Tactic

namespace UplcProof

/-- `uplc_run` proves `Halts p args v` (or `Fails p args`) by symbolic execution, with
    no induction: it splits on the conditions of `if`s over symbolic data and closes
    the branches whose hypotheses are contradictory (`omega`, `simp_all`).
    `[t₁, t₂]` adds lemmas or definitions for the value equalities (the claim's
    definitions are added automatically). For loops on symbolic data, use
    `uplc_induction`; for a symbolic `Bool` argument, `cases b <;> uplc_run`. -/
syntax (name := uplcRunTac) "uplc_run" (" [" Lean.Parser.Tactic.simpArg,* "]")? : tactic

@[tactic uplcRunTac] def evalUplcRun : Tactic := fun stx => withMainContext do
  let simpArgs := if stx[1].getNumArgs > 0 then stx[1][1].getSepArgs else #[]
  Tactic.runOn (← getMainGoal) none "run" simpArgs
  replaceMainGoal []

end UplcProof
