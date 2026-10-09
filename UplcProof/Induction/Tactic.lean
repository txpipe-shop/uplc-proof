import Lean
import UplcProof.Induction.Exec
import UplcProof.Induction.Sym

/-!
# `uplc_induction`

Proves `Halts p args v` (or `Fails p args`) for a recursive UPLC program `p`, by
induction on a variable `n : Nat` or `n : List α` of `args`.

1. Run the machine symbolically from the initial state. Each stretch of steps
   becomes `Reaches.of_exec c rfl`. When the next step depends on symbolic data,
   split: on `n` (`cases n`) if that data mentions `n`, else on the condition `c`
   of the `ifThenElse` the machine is at (one branch with `c`, one with `¬c`).
2. At a **loop head** (the body of a function about to run with itself as an
   argument), state the loop invariant
   `∀ k s, Reaches (loop head with argument enc k on stack s) (Return s (res k))`
   and prove it by induction on `k`, by symbolic execution again. Inside the
   loop, the recursive call is closed by the induction hypothesis, which holds
   for *any* stack.
3. Use the invariant at the call, then run on to the target.

`enc` (how `k` is stored in the loop argument) is read off the first loop head.
`res` (what the loop returns) is `(loop := res)` if given, else the user's `v` as
a function of `n` (the loop computes what the program computes, as when Aiken
compiles a recursive function). A branch that ends elsewhere than the target is
accepted only if its hypotheses are contradictory (`omega`, `simp_all`), or if the
leaf closer `Ctx.closer?` closes it (none for `uplc_induction` and `uplc_run`; a
hook for tactics built on `Tactic.runOn`, see `closer_used` in
`UplcProofTests.Induction.Run`).

Splits nest at most `uplc.maxSplits` deep (default 16) on any branch: a loop whose
exit test is on symbolic data other than the induction variable would split at
every iteration, forever. `set_option uplc.maxSplits N` raises the limit for a
script that really branches deeper.

With `generalizing acc`, the loop is a function of two arguments, `n` and an
accumulator, and its head is where the body runs with both bound. The invariant
is `∀ k a s, Reaches (loop head with arguments enc k and w a on stack s) (Return s (res k a))`,
where `w a` is the accumulator's value at the first loop head with `a` in place of
the expression in `acc` it holds (e.g. `acc + x`), or of the value that replaced
`acc` (`acc := x`); `res` is `v` as a function of `n` and `acc`.

For `n : Nat`, when this fails (recursion on `n - 2`, as in `fib`), the tactic
tries induction on pairs: the entry splits `n` twice (`0`, `1`, `k + 2`), and the
invariant becomes `∀ k, P k ∧ P (k + 1)`, whose step proves `P (k + 2)` with
`P k` and `P (k + 1)` at hand.

The tactic only builds proof terms; the kernel checks them.
-/

open Lean Meta Elab Tactic
open PlutusCore.UPLC.Term PlutusCore.UPLC.CekValue PlutusCore.UPLC.CekMachine
open UplcProof.Sym

namespace UplcProof

theorem addInteger_eq (a b : Int) : PlutusCore.Integer.addInteger a b = a + b := rfl
theorem subtractInteger_eq (a b : Int) : PlutusCore.Integer.subtractInteger a b = a - b := rfl
theorem multiplyInteger_eq (a b : Int) : PlutusCore.Integer.multiplyInteger a b = a * b := rfl
theorem byteString_le_refl (a : PlutusCore.ByteString.ByteString) : a ≤ a := String.le_refl a.data
theorem byteString_lt_irrefl (a : PlutusCore.ByteString.ByteString) : ¬ a < a :=
  String.lt_irrefl a.data

/-- Closes equations between CEK values/states produced by symbolic execution:
    unfolds the PlutusCore arithmetic and the given definitions, then `omega`. -/
syntax (name := uplcEq) "uplc_eq" (" [" Lean.Parser.Tactic.simpArg,* "]")? : tactic

macro_rules
  | `(tactic| uplc_eq) => `(tactic| uplc_eq [])
  | `(tactic| uplc_eq [$ts,*]) => `(tactic|
      first
      | rfl
      | (simp only [State.Return.injEq, State.Halt.injEq, CekValue.VCon.injEq,
            Const.Integer.injEq, Const.Data.injEq, Const.ConstDataList.injEq, Const.Bool.injEq,
            addInteger_eq, subtractInteger_eq, multiplyInteger_eq, $ts,*]
          <;> first
            | ((try dsimp only [PlutusCore.Integer.Integer]) <;> omega)
            | (simp [$ts,*] <;> (try dsimp only [PlutusCore.Integer.Integer]) <;> omega)))

/-- Turns the branch condition `h : c = true` (or `= false`) on PlutusCore
    comparisons into a proposition (`0 < x`, `a ≠ b`, and then also `b ≠ a`);
    closes the goal if `h` is false. `equalsData x y` becomes `x = y` (`x ≠ y`) by
    `equalsData_eq_true_iff` (`_false_iff`), without `Classical.choice`. -/
macro "uplc_cond " h:ident : tactic => `(tactic|
  ((try simp only [PlutusCore.Integer.equalsInteger, PlutusCore.Integer.lessThanInteger,
      PlutusCore.Integer.lessThanEqualsInteger, PlutusCore.ByteString.equalsByteString,
      PlutusCore.ByteString.lessThanByteString, PlutusCore.ByteString.lessThanEqualsByteString,
      equalsData_eq_true_iff, equalsData_eq_false_iff,
      PlutusCore.Data.PlutusCore.DataInternal.Data.Constr.injEq,
      PlutusCore.Data.PlutusCore.DataInternal.Data.B.injEq,
      PlutusCore.Data.PlutusCore.DataInternal.Data.I.injEq, List.cons.injEq, and_true, true_and,
      ne_eq,
      byteString_le_refl, byteString_lt_irrefl, not_true_eq_false,
      beq_iff_eq, beq_eq_false_iff_ne, decide_eq_true_eq, decide_eq_false_iff_not,
      addInteger_eq, subtractInteger_eq, multiplyInteger_eq] at $h:ident);
    (try dsimp only [PlutusCore.Integer.Integer] at $h:ident);
    try have := Ne.symm $h))

namespace Tactic

/-- A loop invariant usable at a loop head: the full one (`∀ k s, …`, `arg = none`)
    or an induction hypothesis (`∀ s, …` at `arg = some j`); with an accumulator
    held as `w a`, `∀ k a s, …` (`∀ a s, …`). -/
structure LoopInvariant where
  proof : Expr
  arg : Option Expr
  enc : Expr
  loop : Sym.Loop
  w? : Option Expr

/-- Simp arguments (lemmas, `*`, `-erase`), as `uplc_eq [ts]` takes them. -/
abbrev SimpArgs := Syntax.TSepArray
  [``Lean.Parser.Tactic.simpStar, ``Lean.Parser.Tactic.simpErase, ``Lean.Parser.Tactic.simpLemma] ","

/-- The state of `drive` on one branch. `uplc_induction` builds it; a tactic built
    on the engine gets one from `runCtx` (no induction variable), and its
    extension point is `closer?`, the leaf closer. -/
structure Ctx where
  /-- The type of the induction variable. -/
  τ : Expr
  /-- `fun k => ` (or `fun k a => `) what the loop returns. -/
  res? : Option Expr
  /-- The accumulator (`generalizing acc`). -/
  gen? : Option Expr
  /-- Extra lemmas for `uplc_eq`. -/
  ts : SimpArgs
  /-- The loop invariants and induction hypotheses at hand. -/
  invariants : Array LoopInvariant := #[]
  /-- The values `k` the next recursive call may be on. -/
  candidates : Array Expr
  /-- The induction variable, until the run splits on it. -/
  split? : Option Expr
  /-- How many nested splits on it (2: on `n`, then on `n - 1`). -/
  splits : Nat := 1
  /-- Induction on pairs (`P k ∧ P (k + 1)`), for recursion on `n - 2`. -/
  pairs : Bool := false
  /-- The branch conditions taken. -/
  path : Array Expr := #[]
  /-- How many splits (on `n` or on a condition) led to this branch, at most
      `uplc.maxSplits`. -/
  depth : Nat := 0
  /-- Names the run in error messages. -/
  phase : String
  /-- Last resort at a leaf that does not reach the target (e.g. refute a
      hypothesis about another script's run, as the test closer
      `closeByRefutingHyp` does). It returns whether it closed the goal; if it
      did not, whatever it did is undone (`tryCloser`). An exception it throws
      propagates (it becomes the tactic's error). -/
  closer? : Option (MVarId → TacticM Bool) := none

/-- Where the run is, for error messages. -/
private def Ctx.at (ctx : Ctx) : MessageData :=
  if ctx.path.isEmpty then m!"{ctx.phase}" else m!"{ctx.phase}, on the branch {ctx.path}"

/-- `ctx.ts`, and the hypotheses (`*`) once the run has branched. -/
private def Ctx.simpArgs (ctx : Ctx) : SimpArgs :=
  if ctx.path.isEmpty then ctx.ts else
    ⟨mkSepArray (ctx.ts.getElems.map (·.raw) |>.push
      (mkNode ``Lean.Parser.Tactic.simpStar #[mkAtom "*"])) (mkAtom ",")⟩

/-- Step cap of one symbolic run (`runUntil`), and `evalRun`'s default fuel. -/
def maxSteps : Nat := 200000

/-- How deep splits may nest on one branch of `drive` (`Ctx.depth`). Each split on a
    loop with a symbolic exit test costs more than the one before (the branch
    conditions pile up), so the default is low enough to be reached within the
    default `maxHeartbeats` on such a loop. -/
register_option uplc.maxSplits : Nat := {
  defValue := 16
  descr := "uplc_induction, uplc_run: how deep splits (on the induction variable or on an \
    `if` condition) may nest on one branch; past it the tactic fails (a loop on symbolic \
    data other than the induction variable splits at every iteration)"
}

private def parseReaches (g : MVarId) : MetaM (Expr × Expr) := do
  let ty ← instantiateMVars (← g.getType)
  let_expr Reaches A B := ty | throwError "expected a goal `Reaches A B`, got{indentExpr ty}"
  return (A, B)

/-- `g` without the hypotheses about CEK runs (the loop invariants, and claims
    `Halts`/`Fails` about other runs): they hold whole states or programs, and
    `simp` has no use for them. -/
private def clean (g : MVarId) : MetaM MVarId := g.withContext do
  let runs ← (← getLCtx).getFVarIds.filterM fun x => do
    let ty ← instantiateMVars (← x.getType)
    return ty.getForallBody.isAppOf ``Reaches ||
      (ty.find? fun e => e.isConstOf ``Halts || e.isConstOf ``Fails).isSome
  g.tryClearMany runs

/-- Runs `tac` on `g` (cleaned); succeeds if it closes `g` without `sorry`. -/
private def closes (g : MVarId) (tac : Syntax) : TacticM Bool := do
  let r ← observing? do
    -- `withoutRecover`: a failing tactic must fail, not log an error and admit the goal
    let [] ← Tactic.run (← clean g) (withoutRecover (evalTactic tac)) | failure
    if (← instantiateMVars (mkMVar g)).hasSorry then failure
  return r.isSome

/-- A proof of `lhs = rhs`, by defeq or `uplc_eq`, if one is found. -/
private def proveEq (ctx : Ctx) (lhs rhs : Expr) : TacticM (Option Expr) := do
  if ← withNewMCtxDepth (isDefEq lhs rhs) then
    return some (← mkEqRefl lhs)
  let g ← mkFreshExprMVar (← mkEq lhs rhs)
  -- without the hypotheses first: rewriting with them can make a goal harder
  for ts in if ctx.path.isEmpty then #[ctx.ts] else #[ctx.ts, ctx.simpArgs] do
    if ← closes g.mvarId! (← `(tactic| uplc_eq [$ts,*])) then
      return some (← instantiateMVars g)
  return none

/-- Closes `g` if its hypotheses are contradictory: the branch cannot happen. -/
def refute (ctx : Ctx) (g : MVarId) : TacticM Bool := g.withContext do
  let f ← mkFreshExprMVar (mkConst ``False)
  let ts : Syntax.TSepArray [``Lean.Parser.Tactic.simpErase, ``Lean.Parser.Tactic.simpLemma] "," :=
    ⟨ctx.ts.elemsAndSeps⟩
  unless ← closes f.mvarId! (← `(tactic| first
      | omega
      | simp_all [$ts,*])) do
    return false
  g.assign (← mkFalseElim (← g.getType) f)
  return true

/-- The leaf closer of `ctx`, if any, on `g`; on failure, its effects are undone. -/
private def tryCloser (ctx : Ctx) (g : MVarId) : TacticM Bool := do
  let some c := ctx.closer? | return false
  let s ← saveState
  if ← c g then return true
  s.restore
  return false

/-- For `p : Nat`: `a` with its `Int` subterms that mention `p` replaced by `↑p`
    (e.g. `addInteger ↑(m + 1) (-1)` by `↑m`), if they are all provably `↑p`;
    `none` if `a` holds another value computed from `p` (e.g. `↑m - 2`). -/
private partial def canonicalize (ctx : Ctx) (a p : Expr) : TacticM (Option Expr) := do
  unless (← whnfR (← inferType p)).isConstOf ``Nat do return some a
  let cast ← mkAppOptM ``Nat.cast #[mkConst ``Int, none, p]
  let rec go (e : Expr) : OptionT TacticM Expr := do
    if !(e.hasAnyFVar p.containsFVar) || e == cast then return e
    if (← whnfR (← inferType e)).isConstOf ``Int then
      let isCast : Bool ← (return (← proveEq ctx e cast).isSome : TacticM Bool)
      if isCast then return cast else failure
    let .app f x := e | failure
    return .app (← go f) (← go x)
  go a

/-- `enc` with `arg = enc k` for one of the candidates `k`. -/
private def inferEnc (ctx : Ctx) (arg : Expr) : TacticM Expr := do
  -- a `Nat` is held as `↑k` (and `↑(k + 2) - 1` is read as `↑(k + 1)`)
  let held (k : Expr) : MetaM Expr :=
    if ctx.τ.isConstOf ``Nat then mkAppOptM ``Nat.cast #[mkConst ``Int, none, k] else pure k
  for p in ctx.candidates do
    let hp ← held p
    let some a ← canonicalize ctx arg p | continue
    return ← withLocalDeclD `k ctx.τ fun k => do
      let hk ← held k
      mkLambdaFVars #[k] (a.replace fun e => if e == hp then some hk else none)
  throwError "{ctx.at}: cannot read the loop argument{indentExpr arg}\nas a function of the \
    induction variable."

/-- The largest subterms of `e` of type `σ` that satisfy `p`. -/
private partial def heldTerms (p : Expr → Bool) (σ e : Expr) : MetaM (Array Expr) := do
  if !p e then return #[]
  if ← isDefEq (← inferType e) σ then return #[e]
  let .app f x := e | return #[]
  return (← heldTerms p σ f) ++ (← heldTerms p σ x)

/-- `f x :: List.map f l` back to `List.map f (x :: l)`: `norm` unfolds the
    encoding of a list (`List.map Data.I (x :: acc)`), which hides the list. -/
private partial def foldMaps (e : Expr) : MetaM Expr := do
  let e ← match e with
    | .app f a => pure (.app (← foldMaps f) (← foldMaps a))
    | _ => pure e
  let_expr List.cons _ hd tl := e | return e
  let_expr List.map _ _ f l := tl | return e
  unless hd.isApp && hd.appFn! == f do return e
  mkAppM ``List.map #[f, ← mkAppM ``List.cons #[hd.appArg!, l]]

/-- `w` with `v = w e` for the one expression `e` of `acc`'s type that the
    accumulator's value `v` holds: the one in `acc`, or, if the first iteration
    replaced `acc` (as `acc := x`), the one in `v`. -/
private def inferAcc (ctx : Ctx) (acc v : Expr) : MetaM Expr := do
  let v ← foldMaps v
  let σ ← inferType acc
  let held ← heldTerms (·.containsFVar acc.fvarId!) σ v
  let held ← if held.isEmpty then heldTerms (fun _ => true) σ v else pure held
  let [e] := held.toList.eraseDups
    | throwError "{ctx.at}: the loop's second argument should hold one expression of \
        type `{σ}` (the accumulator `{acc}`), but it is{indentExpr v}"
  withLocalDeclD `a σ fun a => mkLambdaFVars #[a] (v.replace fun x => if x == e then some a else none)

/-- What the loop returns (`res?`); throws if it was not given. -/
private def Ctx.res (ctx : Ctx) : MetaM Expr := do
  let some r := ctx.res? | throwError "{ctx.at}: the run enters a loop; give the loop's result \
    with `(loop := {if ctx.gen?.isSome then "fun k a" else "fun k"} => …)`."
  return r

/-- `ctx` one split deeper. Throws past `uplc.maxSplits`: on a loop whose exit
    test is on symbolic data that is not the induction variable, every iteration
    splits, and the run would go on forever. -/
private def Ctx.deeper (ctx : Ctx) : MetaM Ctx := do
  let limit := uplc.maxSplits.get (← getOptions)
  if ctx.depth ≥ limit then
    let last := ctx.path.extract (ctx.path.size - 2) ctx.path.size
    throwShort m!"{ctx.phase}: more than {limit} nested splits. A loop over symbolic data \
      other than the induction variable splits at every iteration: it needs `uplc_induction` \
      on that data. (If the script really branches this deep, raise \
      `set_option uplc.maxSplits`.)\
      {if last.isEmpty then m!"" else m!"\nThe last splits were on{indentD m!"{last}"}"}"
  return { ctx with depth := ctx.depth + 1 }

mutual

/-- Prove `Reaches st T` by symbolic execution, loop invariants and induction hypotheses. -/
partial def drive (ctx : Ctx) (g : MVarId) : TacticM Unit := g.withContext do
  let (st, T) ← parseReaches g
  let cache ← IO.mkRef {}
  let st ← norm cache st
  let isTarget (s : Expr) : Bool := match ctorName? T, ctorName? s with
    | some ``State.Halt, some ``State.Halt | some ``State.Error, some ``State.Error => true
    | some ``State.Return, some ``State.Return => s.appFn!.appArg! == T.appFn!.appArg!
    | _, _ => false
  -- loops on the induction data; the others (on data of known shape) just run.
  -- With an accumulator, the loop takes two arguments: `n`'s, then the accumulator.
  let inductionLoop? (s : Expr) : MetaM (Option (Sym.Loop × Expr × Array Expr)) := do
    let onData (v : Expr) := ctx.candidates.any fun k => k.isFVar && v.containsFVar k.fvarId!
    if let some (loop, stack, vs) ← loopHead? (if ctx.gen?.isSome then 2 else 1) s then
      if onData vs[0]! then return some (loop, stack, vs)
      if vs.size == 2 && onData vs[1]! then
        throwError "{ctx.at}: the loop takes the accumulator before `n`; `generalizing` \
          supports the order `(n, acc)`."
      return none
    let some acc := ctx.gen? | return none
    if let some (loop, _, vs) ← loopHead? 1 s then
      if onData vs[0]! && !loop.body.isAppOf ``PlutusCore.UPLC.Term.Term.Lam then
        throwError "{ctx.at}: the loop takes one argument, so `{acc}` is not an accumulator \
          (drop `generalizing {acc}`)."
    return none
  -- the starting state may be a loop head itself (the invariant starts there)
  let stop ← runUntil cache st
    (fun s => do
      if isTarget s then return true
      if s == st then return false
      return (← inductionLoop? s).isSome) maxSteps
  let st' := stop.state
  let mut g := g
  let mut a := st
  for (b, c) in stop.segments do
    let g' ← mkFreshExprSyntheticOpaqueMVar (mkApp2 (mkConst ``Reaches) b T)
    g.assign (mkAppN (mkConst ``Reaches.of_exec) #[a, b, T, mkNatLit c, ← proveExec a c b, g'])
    g := g'.mvarId!
    a := b
  -- `focus`: the value the machine waits on (in `Return s v`), else the whole state
  let focus := if ctorName? st' == some ``State.Return then st'.appArg! else st'
  let c? := if stop.stuck then branchCondition? focus <|> branchCondition? st' else none
  -- a closed `equalsData x y` (which does not reduce) that the run waits on, or left in
  -- the result: decided by evaluation, the state rewritten with its value, and on
  let closedEq? := if stop.stuck then findOutsideEnv? isClosedEqualsData (c?.getD focus)
    else if isTarget st' then findOutsideEnv? isClosedEqualsData st' else none
  if let some e := closedEq? then
    let (st'', h) ← rewriteEqualsData cache st' e
    let g' ← mkFreshExprSyntheticOpaqueMVar (mkApp2 (mkConst ``Reaches) st'' T)
    g.assign (mkAppN (mkConst ``Reaches.of_eq_left) #[st', st'', T, h, g'])
    return ← drive ctx g'.mvarId!
  if stop.stuck then
    -- split on `n` if the run waits on it, else on the condition it branches on
    let onN? := ctx.split?.filter fun n => (findOutsideEnv? (· == n) (c?.getD focus)).isSome
    if onN?.isNone && c?.isNone then
      throwShort m!"{ctx.at}: symbolic execution is stuck: reduction cannot decide the next \
        step, and it is not a branch on a condition. The machine is at{indentExpr st'}"
    let ctx ← ctx.deeper
    if let some n := onN? then
      for sg in ← g.cases n.fvarId! do
        sg.mvarId.withContext do
          let recFields ← sg.fields.filterM fun x => do isDefEq (← inferType x) ctx.τ
          drive { ctx with split? := if ctx.splits > 1 then recFields[0]? else none,
                           splits := ctx.splits - 1, invariants := #[],
                           path := ctx.path.map sg.subst.apply,
                           candidates := recFields.push (sg.subst.apply n),
                           phase := s!"{ctx.phase}, case {sg.ctorName}" } sg.mvarId
      return
    let some c := c? | throwError "internal error: no branch condition"
    let (fvars, gb) ← g.generalize #[{ expr := c, xName? := `b, hName? := `h }]
    for sg in ← gb.cases fvars[0]! do
      for gc in ← Tactic.run sg.mvarId (evalTactic (← `(tactic| uplc_cond $(mkIdent `h)))) do
        gc.withContext do
          let hTy := (← getLocalDeclFromUserName `h).type
          -- a branch that contradicts the hypotheses is closed at once
          unless ← refute ctx gc do
            drive { ctx with path := if hTy.isConstOf ``True then ctx.path else ctx.path.push hTy } gc
  else if isTarget st' then
    if let some h ← proveEq ctx st' T then
      g.assign (mkApp3 (mkConst ``Reaches.of_eq) st' T h)
    else unless ← (refute ctx g <||> tryCloser ctx g) do
      if ctorName? st'.appArg! == some ``CekValue.VLam then
        throwError "{ctx.at}: the run returns a function, but the claimed result is\
          {indentExpr T}\nIf the loop takes an accumulator: one passed to the script, after \
          `n`, is `uplc_induction n generalizing acc`; one that starts from a constant \
          (`go(xs, 0)`), or a second one, is not supported."
      throwError "{ctx.at}: the run ends with{indentExpr st'}\nbut the claimed result is\
        {indentExpr T}\nand `uplc_eq` cannot prove them equal (extra lemmas: \
        `uplc_induction n [lemmas]`, `uplc_run [lemmas]`)."
  else if let some (loop, s, vs) ← inductionLoop? st' then
    let known ← ctx.invariants.filterM fun I => do
      return (← isDefEq I.loop.body loop.body) && (← isDefEq I.loop.self loop.self)
    if known.isEmpty then
      let I ← prove ctx loop (← inferEnc ctx vs[0]!) (← ctx.gen?.mapM (inferAcc ctx · vs[1]!))
      call { ctx with invariants := ctx.invariants.push I } g #[I] s vs T
    else
      call ctx g known.reverse s vs T
  else if isHalt st' || isError st' then
    unless ← (refute ctx g <||> tryCloser ctx g) do
      throwError "{ctx.at}: the script {if isError st' then "fails (reaches `Error`)" else
        "halts"}, but the claim is that it reaches{indentExpr T}"
  else
    throwError "{ctx.at}: the run stopped at{indentExpr st'}\nwhich is neither the target\
      {indentExpr T}\nnor a loop head."

/-- A recursive call at loop head `(s, vs)`, closed by one of the invariants `Is` of its loop. -/
private partial def call (ctx : Ctx) (g : MVarId) (Is : Array LoopInvariant) (s : Expr)
    (vs : Array Expr) (T : Expr) : TacticM Unit := g.withContext do
  let arg := vs[0]!
  let ks (I : LoopInvariant) := I.arg.map (#[·]) |>.getD ctx.candidates
  for I in Is do
    -- the accumulator `vs[1]` is `w a` for some `a`
    let as ← match I.w? with
      | none => pure #[]
      | some w =>
        let a ← mkFreshExprMVar w.bindingDomain!
        unless ← isDefEq (mkApp w a).headBeta (← foldMaps vs[1]!) do
          throwError "{ctx.at}: recursive call with the accumulator{indentExpr vs[1]!}\nwhich \
            does not have the form it had at the first call{indentExpr w}"
        pure #[← instantiateMVars a]
    for k in ks I do
      let encK := (mkApp I.enc k).headBeta
      let some hArg ← proveEq ctx arg encK | continue
      let f ← withLocalDeclD `a (← inferType arg) fun a =>
        mkLambdaFVars #[a] (I.loop.state s (#[a] ++ vs.extract 1))
      let hA ← mkCongrArg f hArg
      let B := mkApp2 (mkConst ``State.Return) s (mkAppN (← ctx.res) (#[k] ++ as)).headBeta
      let hI := mkAppN I.proof ((if I.arg.isSome then #[] else #[k]) ++ as.push s)
      let g' ← mkFreshExprSyntheticOpaqueMVar (mkApp2 (mkConst ``Reaches) B T)
      g.assign (mkAppN (mkConst ``Reaches.call)
        #[I.loop.state s vs, I.loop.state s (#[encK] ++ vs.extract 1), B, T, hA, hI, g'])
      return ← drive ctx g'.mvarId!
  throwError "{ctx.at}: recursive call on{indentExpr arg}\nwhich is not `enc k` for k in \
    {Is.flatMap ks} (enc = {(Is.map (·.enc))[0]!}). Only structural recursion (on `n - 1`, also \
    `n - 2` for a `Nat`, on the tail of a list) is supported."

/-- State the invariant of `loop` and prove it by induction. -/
private partial def prove (ctx : Ctx) (loop : Sym.Loop) (enc : Expr) (w? : Option Expr) :
    TacticM LoopInvariant := do
  let res ← ctx.res
  let stackTy := mkApp (mkConst ``List [.zero]) (mkConst ``Frame)
  -- `P k`: from the loop head on `enc k` (and accumulator `a`) and any stack `s`,
  -- the machine returns `res k` (`res k a`) to `s`
  let P ← withLocalDeclD `k ctx.τ fun k => do
    let Pk ← withLocalDeclD `s stackTy fun s => do
      -- `as`: the accumulator `a` (if any), held as `vs`
      let mk (as vs : Array Expr) : MetaM Expr := do
        let A := loop.state s (#[(mkApp enc k).headBeta] ++ vs)
        let B := mkApp2 (mkConst ``State.Return) s (mkAppN res (#[k] ++ as)).headBeta
        mkForallFVars (as.push s) (mkApp2 (mkConst ``Reaches) A B)
      match w? with
      | some w => withLocalDeclD `a w.bindingDomain! fun a => mk #[a] #[(mkApp w a).headBeta]
      | none => mk #[] #[]
    mkLambdaFVars #[k] Pk
  -- prove the goal `P _` from the loop head, with the induction hypotheses `ihs` (`P j`, `j`)
  let run (g : MVarId) (ihs : Array (Expr × Expr)) (candidates : Array Expr) (case : String) := do
    let (_, g) ← g.introN (if w?.isSome then 2 else 1)
    drive { ctx with candidates, split? := none, phase := s!"loop invariant, {case}",
                     invariants := ctx.invariants ++ ihs.map fun (proof, j) =>
                       { proof, arg := some j, enc, loop, w? } } g
  let forallK (f : Expr → MetaM Expr) : MetaM Expr :=
    withLocalDeclD `k ctx.τ fun k => do mkForallFVars #[k] (← f k)
  unless ctx.pairs do
    let mI ← mkFreshExprSyntheticOpaqueMVar (← forallK fun k => pure (mkApp P k).headBeta)
    let (k, g) ← mI.mvarId!.intro `k
    for sg in ← g.induction k (ctx.τ.getAppFn.constName! ++ `rec) do
      sg.mvarId.withContext do
        let recFields ← sg.fields.filterM fun x => do isDefEq (← inferType x) ctx.τ
        let ihs ← sg.fields.filterMapM fun ih => do
          let ihTy ← inferType ih
          return if ihTy.isForall then (recFields.find? (ihTy.containsFVar ·.fvarId!)).map (ih, ·)
            else none
        run sg.mvarId ihs recFields (if recFields.isEmpty then "base case" else "step case")
    return { proof := mI, arg := none, enc, loop, w? }
  -- induction on pairs, `∀ k, P k ∧ P (k + 1)`: `P 0`, `P 1`, and `P (j + 2)` from `P j` and `P (j + 1)`
  let succ (j : Expr) := mkNatAdd j (mkNatLit 1)
  let mQ ← mkFreshExprSyntheticOpaqueMVar
    (← forallK fun k => pure (mkAnd (mkApp P k).headBeta (mkApp P (succ k)).headBeta))
  let (k, g) ← mQ.mvarId!.intro `k
  -- `A ∧ B`: its two goals
  let split (g : MVarId) : MetaM (MVarId × MVarId) := do
    let ty ← whnfR (← instantiateMVars (← g.getType))
    let_expr And A B := ty | throwError "internal error: pairs"
    let a ← mkFreshExprSyntheticOpaqueMVar A
    let b ← mkFreshExprSyntheticOpaqueMVar B
    g.assign (mkApp4 (mkConst ``And.intro) A B a b)
    return (a.mvarId!, b.mvarId!)
  let #[z, sc] ← g.induction k ``Nat.rec | throwError "internal error: pairs"
  -- `P 0` and `P 1` run on known values: no loop head to stop at
  z.mvarId.withContext do
    let (g0, g1) ← split z.mvarId
    run g0 #[] #[] "base case 0"
    run g1 #[] #[] "base case 1"
  sc.mvarId.withContext do
    let #[j, ih] := sc.fields | throwError "internal error: pairs"
    let (g1, g2) ← split sc.mvarId
    g1.assign (← mkAppM ``And.right #[ih])
    run g2 #[(← mkAppM ``And.left #[ih], j), (← mkAppM ``And.right #[ih], succ j)] #[j, succ j]
      "step case"
  let proof ← withLocalDeclD `k ctx.τ fun k => do mkLambdaFVars #[k] (← mkAppM ``And.left #[mkApp mQ k])
  return { proof, arg := none, enc, loop, w? }

end

/-- The user's definitions in `e` (the specification), as simp arguments:
    everything except instances, `match` auxiliaries (simp reduces those itself)
    and definitions from these libraries. -/
def specDefs (e : Expr) : MetaM (Array Syntax) := do
  let env ← getEnv
  let library := [`Init, `Lean, `Std, `Batteries, `Mathlib, `PlutusCore, `CardanoLedgerApi,
    `UplcProof]
  e.getUsedConstants.filterMapM fun c => do
    let some (.defnInfo _) := env.find? c | return none
    if (← isInstance c) || (← isMatcher c) then return none
    if let some idx := env.getModuleIdxFor? c then
      if library.any (·.isPrefixOf env.header.moduleNames[idx.toNat]!) then return none
    return some (mkNode ``Lean.Parser.Tactic.simpLemma #[mkNullNode, mkNullNode, mkIdent c])

def uplcInduction (n : Expr) (gen? : Option Expr) (simpArgs : Array Syntax) (loop? : Option Expr) :
    TacticM Unit := do
  let g ← getMainGoal
  g.withContext do
  -- `whnfR`: a claim written with a reducible wrapper (`Accepts s c`) is a `Halts` claim
  let ty ← whnfR (← instantiateMVars (← g.getType)).consumeMData
  let (p, args, v?) ← match_expr ty with
    | Halts p args v => pure (p, args, some v)
    | Fails p args => pure (p, args, none)
    | _ => throwError "uplc_induction: expected a goal `Halts p args v` or `Fails p args`, \
        got{indentExpr ty}"
  let τ ← whnfR (← inferType n)
  unless τ.isConstOf ``Nat || τ.isAppOfArity ``List 1 do
    throwError "uplc_induction: `{n}` must be a `Nat` or a `List`, not{indentExpr τ}"
  if let some acc := gen? then
    if acc == n then
      throwError "uplc_induction: `{n}` is the induction variable; `generalizing` takes the accumulator"
    if (← whnfR (← inferType acc)).isConstOf ``Nat then
      throwError "uplc_induction: the script computes the accumulator as an `Int`: \
        state it as `({acc} : Int)`"
  let vars := #[n] ++ gen?.toArray
  for x in vars do
    unless args.containsFVar x.fvarId! do
      throwError "uplc_induction: `{x}` is not in the script's arguments{indentExpr args}"
  let res? ← if loop?.isSome then pure loop? else v?.mapM (mkLambdaFVars vars ·)
  -- the loop's result is a function of `k` (and `a`) alone: nothing in it may be (or be
  -- about) `n` or `acc`, which the run replaces by other values
  if let some r := res? then
    for x in (collectFVars {} (← instantiateMVars r)).fvarIds do
      let ty ← x.getType
      if vars.any fun y => y.fvarId! == x || ty.containsFVar y.fvarId! then
        throwError "uplc_induction: the loop's result{indentExpr r}\nmentions `{mkFVar x}`, \
          which the loop does not see: write it with the loop's own arguments (`fun k => …` \
          with `k` for `{n}`; `xs.headD 0` rather than `xs.head h`)."
  let mut specs := #[]
  for e in v?.toList ++ loop?.toList do specs := specs ++ (← specDefs e)
  let ts : SimpArgs := ⟨mkSepArray (simpArgs ++ specs) (mkAtom ",")⟩
  -- elaborate the lemmas now: `uplc_eq` failures are caught later, and would hide a typo
  discard <| Tactic.run (← mkFreshExprMVar (mkConst ``True)).mvarId!
    (withoutRecover (evalTactic (← `(tactic| simp only [$ts,*]))))
  let T := match v? with | some v => mkApp (mkConst ``State.Halt) v | none => mkConst ``State.Error
  let g' ← mkFreshExprSyntheticOpaqueMVar
    (mkApp2 (mkConst ``Reaches) (mkApp2 (mkConst ``initState) p args) T)
  g.assign <| match v? with
    | some v => mkApp4 (mkConst ``Halts.of_reaches) p args v g'
    | none => mkApp3 (mkConst ``Fails.of_reaches) p args g'
  let run (pairs : Bool) : TacticM Unit :=
    drive { τ, res?, ts, gen?, pairs, splits := if pairs then 2 else 1, candidates := #[n],
            split? := some n, phase := "entry" } g'.mvarId!
  -- recursion on `n - 2` (`fib`) needs induction on pairs: tried when the plain one fails
  -- (`catch` restores the state: `TacticM`'s `try … catch` backtracks)
  try run false catch e =>
    unless τ.isConstOf ``Nat do throw e
    try run true catch e' =>
      throwError "{e.toMessageData}\n\nInduction on pairs (for recursion on `n - 1` and \
        `n - 2`) fails too:\n{e'.toMessageData}"
  replaceMainGoal []

end Tactic

/-- `uplc_induction n` proves `Halts p args v` (or `Fails p args`) for a recursive
    UPLC program `p`, by induction on `n : Nat` or `n : List α`. `generalizing acc`:
    the loop also carries `acc` (an accumulator), and the invariant holds for every
    value of it. `[t₁, t₂]` adds lemmas or definitions for the value equalities
    (the specification's definitions are added automatically). `(loop := fun k => r)`
    (`fun k a => r` with an accumulator): the loop returns `r` for argument `k`,
    when that is not the program's result. -/
syntax (name := uplcInductionTac) "uplc_induction " ident (" generalizing " ident)?
  (" [" Lean.Parser.Tactic.simpArg,* "]")? (" (" &"loop" " := " term ")")? : tactic

@[tactic uplcInductionTac] def evalUplcInduction : Tactic := fun stx => withMainContext do
  let n := Expr.fvar (← getFVarId stx[1])
  let gen? ← if stx[2].getNumArgs > 0 then some <$> Expr.fvar <$> getFVarId stx[2][1] else pure none
  let simpArgs := if stx[3].getNumArgs > 0 then stx[3][1].getSepArgs else #[]
  let mut loop? := none
  if stx[4].getNumArgs > 0 then
    let mut ty := mkConst ``CekValue
    if let some a := gen? then ty ← mkArrow (← inferType a) ty
    loop? := some (← elabTermEnsuringType stx[4][3] (← mkArrow (← inferType n) ty))
  Tactic.uplcInduction n gen? simpArgs loop?

end UplcProof
