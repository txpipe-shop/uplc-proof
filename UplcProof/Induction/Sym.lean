import Lean
import UplcProof.Induction.Exec
import UplcProof.Induction.EqData

/-!
# Symbolic execution of the CEK machine

Runs `step` on states that contain free variables (the symbolic inputs), using
Lean's own reduction (`whnf`). Branches are decided by reduction too: they are
decidable as long as the shape of the data is known (`m + 1`, `x :: xs`).

Nothing in this file is trusted: every run it computes ends up in a proof
`exec st c = st'` that is checked by `rfl`, i.e. by the kernel re-running the
same `c` steps.
-/

open Lean Meta
open PlutusCore.UPLC.Term PlutusCore.UPLC.CekValue PlutusCore.UPLC.CekMachine

namespace UplcProof.Sym

/-- Inductive types whose constructors are exposed when normalizing a state.
    Leaves of any other type (`Int`, `Nat`, `String`, `Bool`, …) are kept as
    written, so that `↑(m + 1)` stays `↑(m + 1)`. -/
private def structuralTypes : List Name :=
  [``PlutusCore.UPLC.CekMachine.State, ``PlutusCore.UPLC.CekMachine.Frame,
   ``PlutusCore.UPLC.CekValue.CekValue, ``PlutusCore.UPLC.CekValue.Environment,
   ``PlutusCore.UPLC.Term.Term, ``PlutusCore.UPLC.Term.Const, ``PlutusCore.Data.Data,
   ``List, ``Prod, ``PlutusCore.UPLC.Builtins.ExpectedBuiltinArgs,
   ``PlutusCore.UPLC.Builtins.ExpectedBuiltinArg, ``PlutusCore.UPLC.Term.BuiltinFun]

private def isStructuralType (ty : Expr) : MetaM Bool := do
  let ty ← whnfR ty
  match ty.getAppFn.constName? with
  | some n => return structuralTypes.contains n
  | none => return false

/-- Normal forms already computed in this run (normal forms map to themselves,
    so the unchanged parts of the next state are not traversed again). -/
abbrev Cache := IO.Ref (Std.HashMap Expr Expr)

/-- `whnf e`, or `none` when reduction runs out of recursion depth. A symbolic `Nat`
    under a literal can do that: `↑(n + 1) ≤ 1000000` unfolds to a match on
    `n + 1 - 1000000 : Nat`, and `Nat.sub` recurses on its second argument, the literal,
    one `Nat.pred` per unit. Such a term is left as it is (stuck): the run then branches
    on it, and `uplc_cond` decides it. -/
def whnfBounded? (e : Expr) : MetaM (Option Expr) := do
  let s ← saveState
  tryCatchRuntimeEx (some <$> whnf e) fun ex => do
    unless ex.isMaxRecDepth do throw ex
    s.restore
    return none

/-- Expose the constructors of `e` (recursively, through structural types only). -/
partial def norm (cache : Cache) (e : Expr) : MetaM Expr := do
  let rec go (e : Expr) : MetaM Expr := do
    if let some r := (← cache.get).get? e then return r
    let r ← do
      unless ← isStructuralType (← inferType e) do return e
      let some e' ← whnfBounded? e | return e
      let fn := e'.getAppFn
      -- a term that reduces to a variable is that variable (the stack `step.folding [] s` is `s`)
      let some c := fn.constName? | return if e'.isFVar then e' else e
      let some (.ctorInfo ci) := (← getEnv).find? c | return e
      let args := e'.getAppArgs
      let mut newArgs := args
      for i in [ci.numParams : args.size] do
        newArgs := newArgs.set! i (← go args[i]!)
      pure (mkAppN fn newArgs)
    cache.modify (·.insert e r |>.insert r r)
    return r
  go e

def ctorName? (e : Expr) : Option Name := e.getAppFn.constName?

def isHalt (st : Expr) : Bool := ctorName? st == some ``State.Halt
def isError (st : Expr) : Bool := ctorName? st == some ``State.Error

private def svDefault : MetaM Expr :=
  mkAppOptM ``Inhabited.default #[mkConst ``PlutusCore.Default.BuiltinSemanticsVariant, none]

/-- Throws `msg`, printing subterms deeper than a few levels as `⋯` (states are large). -/
def throwShort (msg : MessageData) : MetaM α :=
  withOptions (·.setBool `pp.deepTerms false |>.setNat `pp.deepTerms.threshold 8) (throwError msg)

/-- One symbolic CEK step, or `none` when reduction cannot decide what the
    machine does next (it depends on symbolic data). -/
private def stepE (cache : Cache) (st : Expr) : MetaM (Option Expr) := do
  let e := mkApp2 (mkConst ``PlutusCore.UPLC.CekMachine.step) (← svDefault) st
  let some e' ← whnfBounded? e | return none
  match ctorName? e' with
  | some ``State.Eval | some ``State.Return | some ``State.Error | some ``State.Halt =>
    return some (← norm cache e')
  | _ => return none

/-- Where a symbolic run stopped, after `steps` steps (`stuck`: the next step
    depends on symbolic data). `segments` are the states it went through, every
    `chunk` steps and at the end, each with its distance from the previous one:
    one `rfl` per segment keeps each check shallow. -/
structure Stop where
  state : Expr
  steps : Nat
  segments : Array (Expr × Nat)
  stuck : Bool

/-- Run from `st` (normalized) until `stop` holds or the machine halts, errors or
    gets stuck; an error after `maxSteps` steps without any of these. -/
partial def runUntil (cache : Cache) (st : Expr) (stop : Expr → MetaM Bool) (maxSteps : Nat)
    (chunk := 100) : MetaM Stop := do
  let rec loop (st : Expr) (n : Nat) (segs : Array (Expr × Nat)) : MetaM Stop := do
    let done (stuck : Bool) : Stop :=
      ⟨st, n, if n % chunk == 0 then segs else segs.push (st, n % chunk), stuck⟩
    if (← stop st) || isHalt st || isError st then return done false
    if n ≥ maxSteps then
      throwShort m!"symbolic execution reached its step limit ({maxSteps} more steps) without \
        stopping; the state is{indentExpr st}"
    let some st' ← stepE cache st | return done true
    loop st' (n + 1) (if (n + 1) % chunk == 0 then segs.push (st', chunk) else segs)
  loop st 0 #[]

/-- The first subterm of `e` satisfying `p`, skipping closure environments: they
    hold every variable in scope, not what the machine waits on. -/
partial def findOutsideEnv? (p : Expr → Bool) (e : Expr) : Option Expr :=
  if p e then some e
  else if ctorName? e == some ``Environment.NonEmptyEvironment then none
  else match e with
    | .app a b | .lam _ a b _ | .forallE _ a b _ => findOutsideEnv? p a <|> findOutsideEnv? p b
    | .letE _ t v b _ => findOutsideEnv? p t <|> findOutsideEnv? p v <|> findOutsideEnv? p b
    | .mdata _ b | .proj _ _ b => findOutsideEnv? p b
    | _ => none

/-- The condition `c` of the first `ifThenElse c _ _` in `v` that is not a literal:
    what a stuck run branches on. -/
def branchCondition? (v : Expr) : Option Expr :=
  let isIf (e : Expr) := e.isAppOfArity ``PlutusCore.Bool.ifThenElse 4 &&
    !(e.getArg! 1).isConstOf ``Bool.true && !(e.getArg! 1).isConstOf ``Bool.false
  (findOutsideEnv? isIf v).map (·.getArg! 1)

/-! ## Closed `Data` equalities

`equalsData x y` does not reduce, even on closed `x`, `y` (`eqData` is defined by
well-founded recursion): a run that branches on it is stuck. When `x` and `y` are
closed it is decided by evaluating `dataEqB x y` (`UplcProof.equalsData_eq_dataEqB`),
and the state is rewritten with the value. -/

/-- `e` is `equalsData x y` with `x` and `y` closed. -/
def isClosedEqualsData (e : Expr) : Bool :=
  e.isAppOfArity ``PlutusCore.Data.equalsData 2 && !e.hasFVar && !e.hasMVar

/-- For `c = equalsData x y` (closed): its value `b` and a proof of `c = b`, which
    the kernel checks by evaluating `dataEqB x y`. -/
private def decideEqualsData (c : Expr) : MetaM (Expr × Expr) := do
  let x := c.getArg! 0
  let y := c.getArg! 1
  let e := mkApp2 (mkConst ``UplcProof.dataEqB) x y
  let b ← withTransparency .default (whnf e)
  unless b.isConstOf ``Bool.true || b.isConstOf ``Bool.false do
    throwShort m!"cannot evaluate the `Data` equality{indentExpr c}"
  let hb ← mkExpectedTypeHint (← mkEqRefl b) (← mkEq e b)
  return (b, ← mkEqTrans (mkApp2 (mkConst ``UplcProof.equalsData_eq_dataEqB) x y) hb)

/-- `st` with the closed `c = equalsData x y` replaced by its value (then normalized),
    and a proof of `st = st'`. -/
def rewriteEqualsData (cache : Cache) (st c : Expr) : MetaM (Expr × Expr) := do
  let (b, hc) ← decideEqualsData c
  let body ← kabstract st c
  let st' ← norm cache (body.instantiate1 b)
  return (st', ← mkCongrArg (.lam `z (mkConst ``Bool) body .default) hc)

/-- A recursive function passed to itself: `self = VLam f (Lam x₁ … (Lam xₘ body)) cloEnv`.
    The machine is at its **loop head** when it is about to evaluate `body` in
    `cloEnv[f := self][x₁ := v₁]…[xₘ := vₘ]`. -/
structure Loop where
  cloEnv : Expr
  fName : Expr
  self : Expr
  xNames : Array Expr
  body : Expr

/-- The loop-head state on stack `s` with arguments `vs`. -/
def Loop.state (L : Loop) (s : Expr) (vs : Array Expr) : Expr :=
  let ρ := mkApp3 (mkConst ``Environment.NonEmptyEvironment) L.cloEnv L.fName L.self
  let ρ := (L.xNames.zip vs).foldl (fun ρ (x, v) =>
    mkApp3 (mkConst ``Environment.NonEmptyEvironment) ρ x v) ρ
  mkApp3 (mkConst ``State.Eval) s ρ L.body

/-- If `st` is the loop head of a function of `m` arguments, its loop, stack and arguments. -/
def loopHead? (m : Nat) (st : Expr) : MetaM (Option (Loop × Expr × Array Expr)) := do
  let_expr State.Eval s ρ t := st | return none
  let mut ρ := ρ
  let mut xs := #[]
  let mut vs := #[]
  for _ in [0:m] do
    let_expr Environment.NonEmptyEvironment ρ' x v := ρ | return none
    ρ := ρ'; xs := xs.push x; vs := vs.push v
  let_expr Environment.NonEmptyEvironment ρc f self := ρ | return none
  let_expr CekValue.VLam f' lam ρc' := self | return none
  let mut lam := lam
  for x in xs.reverse do
    let_expr PlutusCore.UPLC.Term.Term.Lam x' t' := lam | return none
    unless x == x' do return none
    lam := t'
  unless f == f' do return none
  unless ← isDefEq t lam do return none
  unless ← isDefEq ρc ρc' do return none
  return some ({ cloEnv := ρc, fName := f, self, xNames := xs.reverse, body := t }, s, vs.reverse)

/-- `Eq.refl st'`: a proof of `exec st c = st'` by defeq, checked here with
    `isDefEq`, then by the kernel. -/
def proveExec (st : Expr) (c : Nat) (st' : Expr) : MetaM Expr := do
  let lhs := mkApp2 (mkConst ``UplcProof.exec) st (mkNatLit c)
  unless ← withTransparency .default (isDefEq lhs st') do
    throwError "internal error: `exec` of {c} steps does not reduce to the computed state"
  mkEqRefl st'

end UplcProof.Sym
