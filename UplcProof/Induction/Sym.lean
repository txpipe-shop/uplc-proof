import Lean
import UplcProof.Induction.Exec
import UplcProof.Induction.EqData
import UplcProof.Induction.Steps

/-!
# Symbolic execution of the CEK machine

Runs `step` on states that contain free variables (the symbolic inputs), using
Lean's own reduction (`whnf`). Branches are decided by reduction too: they are
decidable as long as the shape of the data is known (`m + 1`, `x :: xs`).

The structural rules of `step` and the common saturated builtins are computed
directly on the expression (`Fast`), the rest by `whnf`. A run is proved by the
lemmas of `UplcProof.Induction.Steps`, one per rule (the kernel checks an instance,
it does not run `step`), and the steps without a lemma by evaluation (`rfl`).

Nothing in this file is trusted: every run it computes ends up in a proof
`exec st c = st'` that the kernel checks, so a step computed wrong here can only make
a proof fail.
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

/-! ### Options of the engine

Each optimization can be turned off, to measure it or to rule it out; the defaults are
what the tactics use. "Aux mode" is a run of `drive` with `Ctx.aux` on: `uplc_run`,
`Tactic.runOn` and the tactics built on them (`uplc_induction` runs without it). -/

register_option uplc.perf : Bool := {
  defValue := false
  descr := "print where the time of the engine went (counters by category), for the tactics \
    that report it"
}

register_option uplc.fastStep : Nat := {
  defValue := 1
  descr := "symbolic CEK steps: 0 = always `whnf`, 1 = structural rules computed directly \
    (`Sym.Fast.step?`), 2 = like 1 and compared with `whnf` at every step (testing)"
}

register_option uplc.quickRefute : Bool := {
  defValue := true
  descr := "aux mode: decide some branches by comparing hypotheses (`P` and `¬ P`; a \
    condition already in the context) before `omega`/`simp_all`"
}

register_option uplc.auxLemmas : Nat := {
  defValue := 1
  descr := "aux mode: auxiliary theorems (each checked by the kernel on its own): 0 = none, \
    1 = one per run of the test (after the contexts and the validators), 2 = also one per \
    branch of every run"
}

register_option uplc.nativeCond : Bool := {
  defValue := true
  descr := "aux mode: `uplc_cond` with its simp contexts built once (`Tactic.uplcCond`)"
}

register_option uplc.runCache : Bool := {
  defValue := true
  descr := "aux mode: remember each symbolic run by its start state (`Sym.runToEnd`)"
}

register_option uplc.splitBool : Bool := {
  defValue := true
  descr := "aux mode: split on a condition with `bool_split` and a motive built by \
    `Expr.replace` (instead of `generalize`; `cases`)"
}

register_option uplc.runLemmaMinSteps : Nat := {
  defValue := 1
  descr := "aux mode: a straight run of at least this many steps is an auxiliary theorem \
    shared by every branch that runs it (0 = never)"
}

register_option uplc.branchSimp : Bool := {
  defValue := false
  descr := "aux mode: at a branch on a comparison of numbers, try `simp_all` after `omega` \
    (off: `omega` alone there; the leaves keep the whole `refute`)"
}

register_option uplc.perfDump : Bool := {
  defValue := false
  descr := "with `uplc.perf`: print the hypotheses of every `simp_all` refutation attempt"
}

register_option uplc.chunk : Nat := {
  defValue := 100
  descr := "steps per `exec … = …` proof (`proveExec`) of a symbolic run"
}

register_option uplc.stepLemmas : Nat := {
  defValue := 3
  descr := "the proof of a run: 0 = every step by evaluation (`rfl`); 1 = the variable lookups \
    by the lemmas of `UplcProof.Induction.Steps`; 2 = also the other structural steps; 3 = also the \
    saturated builtins of `UplcProof.Induction.Steps` (`Sym.builtinProof?`)"
}

register_option uplc.omegaMemo : Bool := {
  defValue := true
  descr := "aux mode: remember the facts `omega` failed on (per session) and skip it on the \
    same facts (`Tactic.omegaFacts`)"
}

register_option uplc.simpMemo : Bool := {
  defValue := false
  descr := "aux mode: remember the cleaned contexts `simp_all` failed to refute (per \
    session) and skip it on the same context (`Tactic.hypTypes`)"
}

register_option uplc.fastBuiltins : Bool := {
  defValue := true
  descr := "with `uplc.fastStep`: the common saturated builtins computed on the expression \
    (`Sym.Fast.builtin?`) instead of by `whnf`"
}

register_option uplc.sessionState : Bool := {
  defValue := true
  descr := "the state behind the messages of a proof (the first open case's model, the paths \
    closed, the start time, the profile) in its session; false = global, shared by the \
    theorems of a file"
}

/-- Accumulated nanoseconds and calls, by category (without a session, or with
    `uplc.sessionState` off). -/
initialize perfCounters : IO.Ref (Std.HashMap String (Nat × Nat)) ← IO.mkRef {}

def perfEnabled {m : Type → Type} [Monad m] [MonadOptions m] : m Bool :=
  return uplc.perf.get (← getOptions)

private def isStructuralType (ty : Expr) : MetaM Bool := do
  let ty ← whnfR ty
  match ty.getAppFn.constName? with
  | some n => return structuralTypes.contains n
  | none => return false

/-- Normal forms already computed in this run (normal forms map to themselves,
    so the unchanged parts of the next state are not traversed again). -/
abbrev Cache := IO.Ref (Std.HashMap Expr Expr)

/-- Where a symbolic run stopped, after `steps` steps (`stuck`: the next step
    depends on symbolic data). `segments` are the states it went through, every
    `chunk` steps and at the end, each with its distance from the previous one:
    one `rfl` per segment keeps each check shallow. -/
structure Stop where
  state : Expr
  steps : Nat
  segments : Array (Expr × Nat)
  stuck : Bool
  /-- Every state of the run (`trace[i]`: after `i + 1` steps), for the proofs by lemmas
      (`Stop.proofs`); empty with `uplc.stepLemmas` off. -/
  trace : Array Expr := #[]

/-! ### Sessions: the caches of one proof

One call of `uplc_induction`, `uplc_run` or `uplc_auto` (or of a tactic built on the
engine) is a session (`withSession`): its caches live as long as it does and are seen by it
alone. `lean` elaborates the theorems of a file in parallel, and a cache shared between them
was measured to break proofs (a file with several theorems failed one run in three); the
free variables of two theorems can even have the same ids. The session is found through the
option `uplc.session`, which every function the proof calls inherits; with no session,
nothing is cached. -/

register_option uplc.session : Nat := {
  defValue := 0
  descr := "(internal) the session of the running tactic (`withSession`): its caches"
}

/-- The caches of a session. -/
structure Session where
  /-- Normal forms of closed terms (the scripts' code). -/
  closedNorm : IO.Ref (Std.HashMap Expr Expr)
  /-- Runs to a final or stuck state, by start state (`runToEnd`). -/
  stops : IO.Ref (Std.HashMap Expr Stop)
  /-- The auxiliary theorems of runs, by statement (`sharedRun`). -/
  runLemmas : IO.Ref (Std.HashMap Expr Expr)
  /-- The inequalities of names, by pair (`nameNe?`). -/
  names : IO.Ref (Std.HashMap (Expr × Expr) Expr)
  /-- The simp and dsimp contexts of `uplc_cond` (`Tactic.condCtxs`). -/
  cond : IO.Ref (Option (Simp.Context × Simp.SimprocsArray × Simp.Context × Simp.SimprocsArray))
  /-- The facts `omega` was given and failed on (`Tactic.refute`, `uplc.omegaMemo`). -/
  omegaFails : IO.Ref (Std.HashSet (Array Expr))
  /-- The cleaned contexts `simp_all` failed on (`Tactic.refute`, `uplc.simpMemo`). -/
  simpFails : IO.Ref (Std.HashSet (Array Expr))
  /-- The state behind the messages (`uplc.sessionState`): the first open case's model,
      the paths of the test closed so far, when the proof started, the profile. -/
  model : IO.Ref (Option String)
  paths : IO.Ref Nat
  since : IO.Ref Nat
  perf : IO.Ref (Std.HashMap String (Nat × Nat))

initialize sessions : IO.Ref (Std.HashMap Nat Session) ← IO.mkRef {}
initialize sessionCounter : IO.Ref Nat ← IO.mkRef 0

/-- A new session: its id (for `uplc.session`) and caches. -/
def Session.new : BaseIO Nat := do
  let id ← sessionCounter.modifyGet fun n => (n + 1, n + 1)
  let closedNorm ← IO.mkRef {}
  let stops ← IO.mkRef {}
  let runLemmas ← IO.mkRef {}
  let names ← IO.mkRef {}
  let cond ← IO.mkRef none
  let omegaFails ← IO.mkRef {}
  let simpFails ← IO.mkRef {}
  let model ← IO.mkRef none
  let paths ← IO.mkRef 0
  let since ← IO.mkRef 0
  let perf ← IO.mkRef {}
  let s : Session := ⟨closedNorm, stops, runLemmas, names, cond, omegaFails, simpFails, model, paths, since,
    perf⟩
  sessions.modify (·.insert id s)
  return id

/-- Drops the caches of session `id`. -/
def Session.close (id : Nat) : BaseIO Unit :=
  sessions.modify (·.erase id)

/-- The session of the running proof, if any. -/
def session? {m : Type → Type} [Monad m] [MonadOptions m] [MonadLiftT BaseIO m] :
    m (Option Session) := do
  let id := uplc.session.get (← getOptions)
  if id == 0 then return none
  return (← (sessions.get : BaseIO _)).get? id

/-- Runs `x` in a session of its own (fresh caches, dropped at the end): one per proof, so
    the theorems of a file, elaborated in parallel, never share a cache. -/
def withSession {m : Type → Type} {α : Type} [Monad m] [MonadWithOptions m] [MonadLiftT BaseIO m]
    [MonadFinally m] (x : m α) : m α := do
  let id ← (Session.new : BaseIO Nat)
  try withOptions (uplc.session.set · id) x
  finally (Session.close id : BaseIO Unit)

/-- The session whose message state is used (`uplc.sessionState`), if any. -/
def sessionState? {m : Type → Type} [Monad m] [MonadOptions m] [MonadLiftT BaseIO m] :
    m (Option Session) := do
  if uplc.sessionState.get (← getOptions) then session? else return none

/-! ### Profiling (only with `set_option uplc.perf true`; no effect on the proofs) -/

/-- The profile's counters: the session's, else the global ones. -/
def perfRef {m : Type → Type} [Monad m] [MonadOptions m] [MonadLiftT BaseIO m] :
    m (IO.Ref (Std.HashMap String (Nat × Nat))) := do
  return ((← sessionState?).map (·.perf)).getD perfCounters

def perfAdd {m : Type → Type} [Monad m] [MonadOptions m] [MonadLiftT BaseIO m]
    (k : String) (ns : Nat) : m Unit := do
  let r ← perfRef
  (r.modify fun m => let (a, b) := m.getD k (0, 0); m.insert k (a + ns, b + 1) : BaseIO Unit)

/-- Runs `x`, adding its time to category `k` when profiling. -/
@[inline] def timed {m : Type → Type} [Monad m] [MonadLiftT BaseIO m] [MonadOptions m]
    (k : String) (x : m α) : m α := do
  if !(← perfEnabled) then return ← x
  let t0 ← (IO.monoNanosNow : BaseIO Nat)
  let r ← x
  perfAdd k ((← (IO.monoNanosNow : BaseIO Nat)) - t0)
  return r

/-- The counters, one line per category (ms, calls), sorted by time. -/
def perfReport {m : Type → Type} [Monad m] [MonadOptions m] [MonadLiftT BaseIO m] :
    m String := do
  let m ← ((← perfRef).get : BaseIO _)
  let xs := m.toArray.qsort (fun a b => a.2.1 > b.2.1)
  return xs.foldl (fun s (k, (ns, n)) => s ++ s!"  {k}: {ns / 1000000} ms, {n} calls\n") ""

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
  let closedCache? := (← session?).map (·.closedNorm)
  let rec go (e : Expr) : MetaM Expr := do
    if let some r := (← cache.get).get? e then return r
    let closed := !e.hasFVar && !e.hasMVar
    if closed then
      if let some cc := closedCache? then
        if let some r := (← cc.get).get? e then return r
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
    if closed then
      if let some cc := closedCache? then cc.modify (·.insert e r |>.insert r r)
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

/-! ### The structural rules of `step`, computed on the expression

`whnf (step default st)` is general but slow: every rule goes through the
compiled `match`, and a variable lookup decides `x = x'` on `String`s by
reduction. `fastStep?` applies the rules of `PlutusCore.UPLC.CekMachine.step`
that only move pieces of a normalized state around (variables, `λ`, `delay`,
`force`, application, `constr`, `case`, partial builtin application) directly
on the expression, and returns `none` for everything else (a saturated builtin,
an error, an argument that is not a literal), which then goes through `whnf`.
Nothing here is trusted: the kernel re-runs every step (`proveExec`), so a rule
computed wrong here can only make a proof fail, never prove something false. -/

namespace Fast

def natLit? (e : Expr) : Option Nat :=
  match e with
  | .lit (.natVal n) => some n
  | _ => if e.isAppOfArity ``OfNat.ofNat 3 then
           match e.appFn!.appArg! with
           | .lit (.natVal n) => some n
           | _ => none
         else none

def strLit? (e : Expr) : Option String :=
  match e with
  | .lit (.strVal s) => some s
  | _ => none

/-- The elements of a list literal `[a₁, …, aₙ]` (`List.cons`/`List.nil`). -/
partial def listLit? (e : Expr) (acc : Array Expr := #[]) : Option (Array Expr) :=
  if e.isAppOfArity ``List.nil 1 then some acc
  else if e.isAppOfArity ``List.cons 3 then listLit? e.appArg! (acc.push e.appFn!.appArg!)
  else none

def frameTy : Expr := mkConst ``PlutusCore.UPLC.CekMachine.Frame
def valueTy : Expr := mkConst ``CekValue
def mkCons (α hd tl : Expr) : Expr := mkApp3 (mkConst ``List.cons [levelZero]) α hd tl
def mkNil (α : Expr) : Expr := mkApp (mkConst ``List.nil [levelZero]) α
def mkListLit (α : Expr) (xs : Array Expr) : Expr := xs.foldr (mkCons α) (mkNil α)

def eval (s ρ t : Expr) : Expr := mkApp3 (mkConst ``State.Eval) s ρ t
def ret (s v : Expr) : Expr := mkApp2 (mkConst ``State.Return) s v
def extend (ρ x v : Expr) : Expr := mkApp3 (mkConst ``Environment.NonEmptyEvironment) ρ x v

/-- `ifBoundOtherwiseError`'s lookup of `x` in a normalized environment
    (`none`: not a literal environment, or `x` unbound, i.e. an error). -/
partial def lookup? (ρ : Expr) (x : String) : Option Expr :=
  if ρ.isAppOfArity ``Environment.NonEmptyEvironment 3 then
    let y? := strLit? ρ.appFn!.appArg!
    match y? with
    | some y => if x == y then some ρ.appArg! else lookup? ρ.appFn!.appFn!.appArg! x
    | none => none
  else none

/-- For profiling: how many bindings a variable lookup at `st` walks past. -/
partial def lookupDepth (st : Expr) : Option Nat := do
  unless st.isAppOfArity ``State.Eval 3 do none
  let t := st.appArg!
  unless t.isAppOfArity ``Term.Var 1 do none
  let x ← strLit? t.appArg!
  let rec go (ρ : Expr) (d : Nat) : Option Nat :=
    if ρ.isAppOfArity ``Environment.NonEmptyEvironment 3 then
      if strLit? ρ.appFn!.appArg! == some x then some d else go ρ.appFn!.appFn!.appArg! (d + 1)
    else none
  go st.appFn!.appArg! 0

/-- For profiling: the kind of step the machine takes at `st` (`eval.Var`,
    `ret.RightApplicationOfValue.saturate:IfThenElse`, …). -/
def kind (st : Expr) : String :=
  let cname (x : Expr) : String := (x.getAppFn.constName?.map (·.getString!)).getD "?"
  if st.isAppOfArity ``State.Eval 3 then "eval." ++ cname st.appArg!
  else if st.isAppOfArity ``State.Return 2 then
    let s := st.appFn!.appArg!
    let v := st.appArg!
    if s.isAppOfArity ``List.cons 3 then
      let f := s.appFn!.appArg!
      let fk := cname f
      let vk (x : Expr) : String :=
        if x.isAppOfArity ``CekValue.VBuiltin 3 then
          let args := x.getAppArgs
          if args[2]!.isAppOfArity ``PlutusCore.UPLC.Builtins.ExpectedBuiltinArgs.One 1 then
            "saturate:" ++ cname args[0]!
          else "partial"
        else cname x
      if fk == "RightApplicationOfValue" then "ret." ++ fk ++ "." ++ vk f.appArg!
      else if fk == "LeftApplicationToValue" || fk == "ForceFrame" then "ret." ++ fk ++ "." ++ vk v
      else "ret." ++ fk
    else "ret.[]"
  else "other"

/-- `ExpectedBuiltinArgs.More ArgV η` (resp. `ArgQ`): `η`. -/
def moreArg? (args : Expr) (arg : Name) : Option Expr :=
  if args.isAppOfArity ``PlutusCore.UPLC.Builtins.ExpectedBuiltinArgs.More 2 &&
     args.appFn!.appArg!.isConstOf arg then some args.appArg! else none

/-- One step of `step default st` by its structural rules, or `none`. -/
def step? (st : Expr) : Option Expr := do
  if st.isAppOfArity ``State.Eval 3 then
    let s := st.appFn!.appFn!.appArg!
    let ρ := st.appFn!.appArg!
    let t := st.appArg!
    let .const c _ := t.getAppFn | none
    let n := t.getAppNumArgs
    if c == ``Term.Var && n == 1 then
      let x ← strLit? t.appArg!
      let v ← lookup? ρ x
      return ret s v
    if c == ``Term.Const && n == 1 then
      return ret s (mkApp (mkConst ``CekValue.VCon) t.appArg!)
    if c == ``Term.Lam && n == 2 then
      return ret s (mkApp3 (mkConst ``CekValue.VLam) t.appFn!.appArg! t.appArg! ρ)
    if c == ``Term.Delay && n == 1 then
      return ret s (mkApp2 (mkConst ``CekValue.VDelay) t.appArg! ρ)
    if c == ``Term.Force && n == 1 then
      return eval (mkCons frameTy (mkConst ``PlutusCore.UPLC.CekMachine.Frame.ForceFrame) s) ρ t.appArg!
    if c == ``Term.Apply && n == 2 then
      let f := mkApp2 (mkConst ``PlutusCore.UPLC.CekMachine.Frame.LeftApplicationToTerm) t.appArg! ρ
      return eval (mkCons frameTy f s) ρ t.appFn!.appArg!
    if c == ``Term.Constr && n == 2 then
      let i := t.appFn!.appArg!
      let ms := t.appArg!
      if ms.isAppOfArity ``List.cons 3 then
        let f := mkApp4 (mkConst ``PlutusCore.UPLC.CekMachine.Frame.ConstructorArgument) i
          (mkNil valueTy) ms.appArg! ρ
        return eval (mkCons frameTy f s) ρ ms.appFn!.appArg!
      if ms.isAppOfArity ``List.nil 1 then
        return ret s (mkApp2 (mkConst ``CekValue.VConstr) i (mkNil valueTy))
      none
    if c == ``Term.Case && n == 2 then
      let f := mkApp2 (mkConst ``PlutusCore.UPLC.CekMachine.Frame.CaseScrutinee) t.appArg! ρ
      return eval (mkCons frameTy f s) ρ t.appFn!.appArg!
    none
  else if st.isAppOfArity ``State.Return 2 then
    let s := st.appFn!.appArg!
    let v := st.appArg!
    if s.isAppOfArity ``List.nil 1 then
      return mkApp (mkConst ``State.Halt) v
    unless s.isAppOfArity ``List.cons 3 do none
    let f := s.appFn!.appArg!
    let s' := s.appArg!
    let .const fc _ := f.getAppFn | none
    let fn := f.getAppNumArgs
    if fc == ``PlutusCore.UPLC.CekMachine.Frame.LeftApplicationToTerm && fn == 2 then
      let g := mkApp (mkConst ``PlutusCore.UPLC.CekMachine.Frame.RightApplicationOfValue) v
      return eval (mkCons frameTy g s') f.appArg! f.appFn!.appArg!
    -- `fv` applied to `arg`
    let apply (fv arg : Expr) : Option Expr :=
      if fv.isAppOfArity ``CekValue.VLam 3 then
        let args := fv.getAppArgs
        some (eval s' (extend args[2]! args[0]! arg) args[1]!)
      else if fv.isAppOfArity ``CekValue.VBuiltin 3 then
        let args := fv.getAppArgs
        (moreArg? args[2]! ``PlutusCore.UPLC.Builtins.ExpectedBuiltinArg.ArgV).map fun η =>
          ret s' (mkApp3 (mkConst ``CekValue.VBuiltin) args[0]! (mkCons valueTy arg args[1]!) η)
      else none
    if fc == ``PlutusCore.UPLC.CekMachine.Frame.RightApplicationOfValue && fn == 1 then
      return ← apply f.appArg! v
    if fc == ``PlutusCore.UPLC.CekMachine.Frame.LeftApplicationToValue && fn == 1 then
      return ← apply v f.appArg!
    if fc == ``PlutusCore.UPLC.CekMachine.Frame.ForceFrame && fn == 0 then
      if v.isAppOfArity ``CekValue.VDelay 2 then
        return eval s' v.appArg! v.appFn!.appArg!
      if v.isAppOfArity ``CekValue.VBuiltin 3 then
        let args := v.getAppArgs
        let η ← moreArg? args[2]! ``PlutusCore.UPLC.Builtins.ExpectedBuiltinArg.ArgQ
        return ret s' (mkApp3 (mkConst ``CekValue.VBuiltin) args[0]! args[1]! η)
      none
    if fc == ``PlutusCore.UPLC.CekMachine.Frame.ConstructorArgument && fn == 4 then
      let args := f.getAppArgs
      let (i, vs, ms, ρ) := (args[0]!, args[1]!, args[2]!, args[3]!)
      if ms.isAppOfArity ``List.cons 3 then
        let g := mkApp4 (mkConst ``PlutusCore.UPLC.CekMachine.Frame.ConstructorArgument) i
          (mkCons valueTy v vs) ms.appArg! ρ
        return eval (mkCons frameTy g s') ρ ms.appFn!.appArg!
      if ms.isAppOfArity ``List.nil 1 then
        let xs ← listLit? vs
        return ret s' (mkApp2 (mkConst ``CekValue.VConstr) i (mkListLit valueTy (#[v] ++ xs).reverse))
      none
    if fc == ``PlutusCore.UPLC.CekMachine.Frame.CaseScrutinee && fn == 2 then
      unless v.isAppOfArity ``CekValue.VConstr 2 do none
      let i ← natLit? v.appFn!.appArg!
      let ms ← listLit? f.appFn!.appArg!
      let mi ← ms[i]?
      let vs ← listLit? v.appArg!
      let stack := vs.foldr (fun x acc =>
        mkCons frameTy (mkApp (mkConst ``PlutusCore.UPLC.CekMachine.Frame.LeftApplicationToValue) x) acc) s'
      return eval stack f.appArg! mi
    none
  else none

/-! #### Saturated builtins (`uplc.fastBuiltins`)

The common builtins of the scripts, on literal arguments, with the value `evalBuiltin`
gives (and `norm` writes): the shapes are those of `PlutusCore.UPLC.CekValue.mkCons` & co.
Anything else (a symbolic argument the result depends on, an empty list, another builtin)
is `none`, and goes through `whnf`. -/

def dataTy : Expr := mkConst ``PlutusCore.Data.PlutusCore.DataInternal.Data
def constTy : Expr := mkConst ``PlutusCore.UPLC.Term.Const
def dataC (c : String) : Name := Name.str ``PlutusCore.Data.PlutusCore.DataInternal.Data c
def constC (c : String) : Name := Name.str ``PlutusCore.UPLC.Term.Const c
def prodMk (α β a b : Expr) : Expr := mkApp4 (mkConst ``Prod.mk [levelZero, levelZero]) α β a b
def vcon (c : Expr) : Expr := mkApp (mkConst ``CekValue.VCon) c

/-- `VCon (Const.k x)`: `x`. -/
def vconArg? (v : Expr) (k : String) : Option Expr :=
  if v.isAppOfArity ``CekValue.VCon 1 && v.appArg!.isAppOfArity (constC k) 1 then
    some v.appArg!.appArg!
  else none

/-- The value of builtin `b` on `args` (the last argument first, as `step` passes them),
    with the lemma of `UplcProof.Induction.Steps` for that step (`sat<name>R`/`L`) and its pieces
    (in the lemma's order, after the stack). -/
def builtin? (b : Name) (args : Array Expr) : Option (String × Array Expr × Expr) := do
  let B (n : String) : Name := Name.str ``PlutusCore.UPLC.Term.BuiltinFun n
  let lists : List (String × String × (Expr → Expr)) :=
    [("Data", "ConstDataList", fun x => mkApp (mkConst (constC "Data")) x),
     ("Const", "ConstList", id),
     ("Pair", "ConstPairDataList", fun x => mkApp (mkConst (constC "PairData")) x)]
  if b == B "HeadList" && args.size == 1 then
    for (suf, k, wrap) in lists do
      if let some xs := vconArg? args[0]! k then
        if xs.isAppOfArity ``List.cons 3 then
          return (s!"HeadList{suf}", #[xs.appFn!.appArg!, xs.appArg!], vcon (wrap xs.appFn!.appArg!))
        none
    none
  if b == B "TailList" && args.size == 1 then
    for (suf, k, _) in lists do
      if let some xs := vconArg? args[0]! k then
        if xs.isAppOfArity ``List.cons 3 then
          return (s!"TailList{suf}", #[xs.appFn!.appArg!, xs.appArg!],
            vcon (mkApp (mkConst (constC k)) xs.appArg!))
        none
    none
  if b == B "NullList" && args.size == 1 then
    for (suf, k, _) in lists do
      if let some xs := vconArg? args[0]! k then
        if xs.isAppOfArity ``List.cons 3 then
          return (s!"NullList{suf}Cons", #[xs.appFn!.appArg!, xs.appArg!],
            vcon (mkApp (mkConst (constC "Bool")) (mkConst ``Bool.false)))
        if xs.isAppOfArity ``List.nil 1 then
          return (s!"NullList{suf}Nil", #[], vcon (mkApp (mkConst (constC "Bool")) (mkConst ``Bool.true)))
        none
    none
  if b == B "MkCons" && args.size == 2 then
    if let some xs := vconArg? args[0]! "ConstDataList" then
      let x ← vconArg? args[1]! "Data"
      return ("MkConsData", #[x, xs], vcon (mkApp (mkConst (constC "ConstDataList")) (mkCons dataTy x xs)))
    if let some xs := vconArg? args[0]! "ConstPairDataList" then
      let x ← vconArg? args[1]! "PairData"
      return ("MkConsPair", #[x, xs], vcon (mkApp (mkConst (constC "ConstPairDataList"))
        (mkCons (mkApp2 (mkConst ``Prod [levelZero, levelZero]) dataTy dataTy) x xs)))
    if let some xs := vconArg? args[0]! "ConstList" then
      unless args[1]!.isAppOfArity ``CekValue.VCon 1 do none
      let x := args[1]!.appArg!
      return ("MkConsConst", #[x, xs], vcon (mkApp (mkConst (constC "ConstList")) (mkCons constTy x xs)))
    none
  if b == B "IfThenElse" && args.size == 3 then
    let c ← vconArg? args[2]! "Bool"
    if c.isConstOf ``Bool.true then return ("IfThenElseTrue", #[args[1]!, args[0]!], args[1]!)
    if c.isConstOf ``Bool.false then return ("IfThenElseFalse", #[args[1]!, args[0]!], args[0]!)
    none
  if b == B "ChooseList" && args.size == 3 then
    for (suf, k, _) in lists do
      if let some xs := vconArg? args[2]! k then
        if xs.isAppOfArity ``List.cons 3 then
          return (s!"ChooseList{suf}Cons", #[args[0]!, args[1]!, xs.appFn!.appArg!, xs.appArg!], args[0]!)
        if xs.isAppOfArity ``List.nil 1 then
          return (s!"ChooseList{suf}Nil", #[args[0]!, args[1]!], args[1]!)
        none
    none
  if (b == B "FstPair" || b == B "SndPair") && args.size == 1 then
    let fst := b == B "FstPair"
    let n := if fst then "Fst" else "Snd"
    if let some p := vconArg? args[0]! "PairData" then
      unless p.isAppOfArity ``Prod.mk 4 do none
      let (x, y) := (p.appFn!.appArg!, p.appArg!)
      return (s!"{n}PairData", #[x, y], vcon (mkApp (mkConst (constC "Data")) (if fst then x else y)))
    if let some p := vconArg? args[0]! "Pair" then
      unless p.isAppOfArity ``Prod.mk 4 do none
      let (x, y) := (p.appFn!.appArg!, p.appArg!)
      return (s!"{n}PairConst", #[x, y], vcon (if fst then x else y))
    none
  if b == B "UnConstrData" && args.size == 1 then
    let d ← vconArg? args[0]! "Data"
    unless d.isAppOfArity (dataC "Constr") 2 do none
    return ("UnConstrData", #[d.appFn!.appArg!, d.appArg!], vcon (mkApp (mkConst (constC "Pair"))
      (prodMk constTy constTy (mkApp (mkConst (constC "Integer")) d.appFn!.appArg!)
        (mkApp (mkConst (constC "ConstDataList")) d.appArg!))))
  if b == B "UnIData" && args.size == 1 then
    let d ← vconArg? args[0]! "Data"
    unless d.isAppOfArity (dataC "I") 1 do none
    return ("UnIData", #[d.appArg!], vcon (mkApp (mkConst (constC "Integer")) d.appArg!))
  if b == B "UnBData" && args.size == 1 then
    let d ← vconArg? args[0]! "Data"
    unless d.isAppOfArity (dataC "B") 1 do none
    return ("UnBData", #[d.appArg!], vcon (mkApp (mkConst (constC "ByteString")) d.appArg!))
  if b == B "IData" && args.size == 1 then
    let i ← vconArg? args[0]! "Integer"
    return ("IData", #[i], vcon (mkApp (mkConst (constC "Data")) (mkApp (mkConst (dataC "I")) i)))
  if b == B "BData" && args.size == 1 then
    let x ← vconArg? args[0]! "ByteString"
    return ("BData", #[x], vcon (mkApp (mkConst (constC "Data")) (mkApp (mkConst (dataC "B")) x)))
  if b == B "ConstrData" && args.size == 2 then
    let xs ← vconArg? args[0]! "ConstDataList"
    let i ← vconArg? args[1]! "Integer"
    return ("ConstrData", #[i, xs],
      vcon (mkApp (mkConst (constC "Data")) (mkApp2 (mkConst (dataC "Constr")) i xs)))
  if b == B "MapData" && args.size == 1 then
    let xs ← vconArg? args[0]! "ConstPairDataList"
    return ("MapData", #[xs], vcon (mkApp (mkConst (constC "Data")) (mkApp (mkConst (dataC "Map")) xs)))
  if b == B "ListData" && args.size == 1 then
    let xs ← vconArg? args[0]! "ConstDataList"
    return ("ListData", #[xs], vcon (mkApp (mkConst (constC "Data")) (mkApp (mkConst (dataC "List")) xs)))
  if b == B "UnMapData" && args.size == 1 then
    let d ← vconArg? args[0]! "Data"
    unless d.isAppOfArity (dataC "Map") 1 do none
    return ("UnMapData", #[d.appArg!], vcon (mkApp (mkConst (constC "ConstPairDataList")) d.appArg!))
  if b == B "UnListData" && args.size == 1 then
    let d ← vconArg? args[0]! "Data"
    unless d.isAppOfArity (dataC "List") 1 do none
    return ("UnListData", #[d.appArg!], vcon (mkApp (mkConst (constC "ConstDataList")) d.appArg!))
  if b == B "MkPairData" && args.size == 2 then
    let y ← vconArg? args[0]! "Data"
    let x ← vconArg? args[1]! "Data"
    return ("MkPairData", #[x, y], vcon (mkApp (mkConst (constC "PairData")) (prodMk dataTy dataTy x y)))
  none

/-- A saturated builtin's step (the last argument, `One ArgV`), if `builtin?` knows it: the
    next state, and the lemma of `UplcProof.Induction.Steps` with its arguments before `k b h`. -/
def builtinStepFull? (st : Expr) : Option (Expr × Name × Array Expr) := do
  unless st.isAppOfArity ``State.Return 2 do none
  let s := st.appFn!.appArg!
  let v := st.appArg!
  unless s.isAppOfArity ``List.cons 3 do none
  let f := s.appFn!.appArg!
  let s' := s.appArg!
  let (fv, arg, side) ←
    if f.isAppOfArity ``PlutusCore.UPLC.CekMachine.Frame.RightApplicationOfValue 1 then
      some (f.appArg!, v, "R")
    else if f.isAppOfArity ``PlutusCore.UPLC.CekMachine.Frame.LeftApplicationToValue 1 then
      some (v, f.appArg!, "L")
    else none
  unless fv.isAppOfArity ``CekValue.VBuiltin 3 do none
  let bargs := fv.getAppArgs
  let η := bargs[2]!
  unless η.isAppOfArity ``PlutusCore.UPLC.Builtins.ExpectedBuiltinArgs.One 1 &&
    η.appArg!.isConstOf ``PlutusCore.UPLC.Builtins.ExpectedBuiltinArg.ArgV do none
  let .const b _ := bargs[0]! | none
  let vs ← listLit? bargs[1]!
  let (n, pieces, r) ← builtin? b (#[arg] ++ vs)
  return (ret s' r, Name.str (Name.mkStr2 "UplcProof" "Steps") s!"sat{n}{side}", #[s'] ++ pieces)

/-- A saturated builtin applied: the next state (`builtinStepFull?`). -/
def builtinStep? (st : Expr) : Option Expr := (builtinStepFull? st).map (·.1)

end Fast

/-- `Term.Builtin b` (its expected arguments, `expectedArgs b`, normalized once per
    session: a closed term) and the saturated builtins of `Fast.builtinStep?`. -/
def fastBuiltin? (cache : Cache) (st : Expr) : MetaM (Option Expr) := do
  if st.isAppOfArity ``State.Eval 3 then
    let t := st.appArg!
    unless t.isAppOfArity ``Term.Builtin 1 do return none
    let η ← norm cache (mkApp (mkConst ``PlutusCore.UPLC.Builtins.expectedArgs) t.appArg!)
    return some (Fast.ret st.appFn!.appFn!.appArg!
      (mkApp3 (mkConst ``CekValue.VBuiltin) t.appArg! (Fast.mkNil Fast.valueTy) η))
  return Fast.builtinStep? st

/-- One symbolic CEK step, or `none` when reduction cannot decide what the
    machine does next (it depends on symbolic data). The structural rules are
    computed directly (`Fast.step?`, option `uplc.fastStep`), the rest by `whnf`. -/
private def stepE (cache : Cache) (st : Expr) : MetaM (Option Expr) := do
  let mode := uplc.fastStep.get (← getOptions)
  if mode != 0 then
    let fast? ← if let some st' := Fast.step? st then pure (some st')
      else if uplc.fastBuiltins.get (← getOptions) then fastBuiltin? cache st
      else pure none
    if let some st' := fast? then
      if ← perfEnabled then
        perfAdd "step.fast" 0
        if let some d := Fast.lookupDepth st then perfAdd "lookup.depth(sum in 'ms' = x1e6)" (d * 1000000)
      if mode == 2 then
        let e' ← whnf (mkApp2 (mkConst ``PlutusCore.UPLC.CekMachine.step) (← svDefault) st)
        let slow ← norm cache e'
        unless slow == st' do
          unless ← withNewMCtxDepth (isDefEq slow st') do
            throwError "fast step differs from `step`:{indentExpr st}\nfast:{indentExpr st'}\nwhnf:{indentExpr slow}"
          perfAdd "step.fast.syntactic-mismatch" 0
      return some st'
  let e := mkApp2 (mkConst ``PlutusCore.UPLC.CekMachine.step) (← svDefault) st
  let t0 ← IO.monoNanosNow
  let some e' ← timed "step.whnf" (whnfBounded? e) | return none
  if ← perfEnabled then perfAdd ("step.whnf." ++ Fast.kind st) ((← IO.monoNanosNow) - t0)
  match ctorName? e' with
  | some ``State.Eval | some ``State.Return | some ``State.Error | some ``State.Halt =>
    return some (← timed "step.norm" (norm cache e'))
  | _ => return none

/-- Run from `st` (normalized) until `stop` holds or the machine halts, errors or
    gets stuck; an error after `maxSteps` steps without any of these. -/
partial def runUntil (cache : Cache) (st : Expr) (stop : Expr → MetaM Bool) (maxSteps : Nat)
    (chunk := 100) : MetaM Stop := do
  let record := uplc.stepLemmas.get (← getOptions) != 0
  let rec loop (st : Expr) (n : Nat) (segs : Array (Expr × Nat)) (tr : Array Expr) :
      MetaM Stop := do
    let done (stuck : Bool) : Stop :=
      { state := st, steps := n, stuck, trace := tr
        segments := if n % chunk == 0 then segs else segs.push (st, n % chunk) }
    if (← stop st) || isHalt st || isError st then return done false
    if n ≥ maxSteps then
      throwShort m!"symbolic execution reached its step limit ({maxSteps} more steps) without \
        stopping; the state is{indentExpr st}"
    let some st' ← stepE cache st | return done true
    loop st' (n + 1) (if (n + 1) % chunk == 0 then segs.push (st', chunk) else segs)
      (if record then tr.push st' else tr)
  loop st 0 #[] #[]

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

/-- The local variable a `match` (or `casesOn`) in `v` waits on: a discriminant that is a free
    variable (`match d with | Data.Constr i ds => …` on a symbolic `Data` leaf). The run goes on
    once it is split by its constructors. Closure environments are skipped, as in
    `branchCondition?`. -/
def stuckDiscr? (env : Lean.Environment) (v : Expr) : Option FVarId :=
  let discrs (e : Expr) : Array Expr :=
    match e.getAppFn with
    | .const n _ =>
      let args := e.getAppArgs
      match Lean.Meta.Match.Extension.getMatcherInfo? env n with
      | some info =>
        if args.size < info.arity then #[] else
          (Array.range info.numDiscrs).map fun i => args[info.numParams + 1 + i]!
      | none =>
        if isCasesOnRecursor env n then
          match env.find? n.getPrefix with
          | some (Lean.ConstantInfo.inductInfo iv) =>
            let i := iv.numParams + 1 + iv.numIndices
            if h : i < args.size then #[args[i]] else #[]
          | _ => #[]
        else #[]
    | _ => #[]
  (findOutsideEnv? (fun e => (discrs e).any (·.isFVar)) v).bind fun m =>
    (discrs m).findSome? fun a => if a.isFVar then some a.fvarId! else none

/-- A free variable of an inductive type (not `Int` or `Nat`) in the condition of a Lean `if` that
    `v` waits on: a builtin over lists is `if a.isEmpty = true then … else …` (`chooseList`), which
    `branchCondition?` does not take (it is not `ifThenElse`). Split by its constructors, the
    condition reduces. -/
def stuckIteVar? (v : Expr) : MetaM (Option FVarId) := do
  let isIte (e : Expr) := (e.isAppOfArity ``ite 5 || e.isAppOfArity ``dite 5) && (e.getArg! 1).hasFVar
  let some m := findOutsideEnv? isIte v | return none
  for x in (collectFVars {} (m.getArg! 1)).fvarIds do
    let ty ← whnfR (← x.getType)
    let .const n _ := ty.getAppFn | continue
    if n == ``Int || n == ``Nat then continue
    if let some (.inductInfo _) := (← getEnv).find? n then return some x
  return none

/-! ### Closed `Data` equalities

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

/-- A proof of `exec st c = st'`. Not re-checked here (the symbolic run already
    computed `st'` by reduction): the kernel re-runs the `c` steps when it checks
    the proof, which is the check that counts. Checking here too (`isDefEq`)
    doubled the time of a run. -/
def proveExec (st : Expr) (c : Nat) (st' : Expr) : MetaM Expr := do
  let lhs := mkApp2 (mkConst ``UplcProof.exec) st (mkNatLit c)
  mkExpectedTypeHint (← mkEqRefl st') (← mkEq lhs st')

/-! ### Runs proved by the lemmas of `UplcProof.Induction.Steps`

A step that a structural rule of `step` takes is proved by that rule's lemma (the kernel
compares the instance with the two states, it does not run `step`); a variable lookup by one
lemma per binding it walks past, each with the inequality of two names. The other steps
(builtins, `case` on a constructor, …) are proved by evaluation, in maximal blocks. -/

/-- The inequalities of names already built (closed terms), by pair: the session's. -/
abbrev NameCache := Option (IO.Ref (Std.HashMap (Expr × Expr) Expr))

private def decideProof (val : Bool) (p inst : Expr) : Expr :=
  mkApp3 (mkConst (if val then ``of_decide_eq_true else ``of_decide_eq_false)) p inst
    (mkApp2 (mkConst ``Eq.refl [levelOne]) (mkConst ``Bool) (mkConst (if val then ``Bool.true else ``Bool.false)))

/-- `x ≠ x'` for two different string literals: by their lengths, or by the first character
    where they differ (`Char.ofNat n ≠ Char.ofNat m` from `n ≠ m`, two numerals); `none` if
    they are equal or not literals. -/
def nameNe? (names : NameCache) (x x' : Expr) : MetaM (Option Expr) := do
  let (.lit (.strVal s₁)) := x | return none
  let (.lit (.strVal s₂)) := x' | return none
  if s₁ == s₂ then return none
  if let some c := names then
    if let some e := (← c.get).get? (x, x') then return some e
  let charT := mkConst ``Char
  let data (e : Expr) := mkApp (mkConst ``String.data) e
  let natEqDec (a b : Expr) : MetaM Expr := do
    return decideProof false (← mkEq a b) (mkApp2 (mkConst ``instDecidableEqNat) a b)
  let cs₁ := s₁.toList
  let cs₂ := s₂.toList
  let e ← if cs₁.length != cs₂.length then do
      let len (e : Expr) := mkApp2 (mkConst ``List.length [levelZero]) charT (data e)
      pure (mkApp3 (mkConst ``Steps.String.ne_of_length) x x' (← natEqDec (len x) (len x')))
    else do
      let some k := (List.range cs₁.length).find? (fun i => cs₁[i]! != cs₂[i]!) | return none
      let (n₁, n₂) := (cs₁[k]!.toNat, cs₂[k]!.toNat)
      unless n₁ < 55296 && n₂ < 55296 do return none
      let lit := mkRawNatLit
      let ch (n : Nat) := mkApp (mkConst ``Char.ofNat) (lit n)
      let rflSome (c : Expr) := mkApp2 (mkConst ``Eq.refl [levelOne]) (mkApp (mkConst ``Option [levelZero]) charT)
        (mkApp2 (mkConst ``Option.some [levelZero]) charT c)
      let lt (n : Nat) : MetaM Expr := do
        return decideProof true (← mkAppM ``LT.lt #[lit n, lit 55296])
          (mkApp2 (mkConst ``Nat.decLt) (lit n) (lit 55296))
      let hc := mkAppN (mkConst ``Steps.Char.ofNat_ne)
        #[lit n₁, lit n₂, ← lt n₁, ← lt n₂, ← natEqDec (lit n₁) (lit n₂)]
      pure (mkAppN (mkConst ``Steps.String.ne_of_drop)
        #[x, x', lit k, ch n₁, ch n₂, rflSome (ch n₁), rflSome (ch n₂), hc])
  if let some c := names then c.modify (·.insert (x, x') e)
  return some e

/-- The lookup of `x` in `ρ`, `ifBoundOtherwiseError s ρ x = r` (`r` the next state,
    `Return s V`): `ifBound_skip` past each binding, `ifBound_eq` at the one that binds `x`;
    with that binding's value `V`. -/
def lookupProof? (names : NameCache) (s ρ x r : Expr) : MetaM (Option (Expr × Expr)) := do
  let mut links : Array (Expr × Expr × Expr) := #[]
  let mut e := ρ
  let mut found := false
  repeat
    unless e.isAppOfArity ``Environment.NonEmptyEvironment 3 do break
    let p := e.appFn!.appFn!.appArg!
    let x' := e.appFn!.appArg!
    let V := e.appArg!
    links := links.push (p, x', V)
    if x' == x then found := true; break
    e := p
  unless found do return none
  let (p, _, V) := links.back!
  let mut pf := mkAppN (mkConst ``Steps.ifBound_eq) #[s, p, x, V]
  for i in (List.range (links.size - 1)).reverse do
    let (p, x', V') := links[i]!
    let some hne ← nameNe? names x x' | return none
    pf := mkAppN (mkConst ``Steps.ifBound_skip) #[s, p, x, x', V', r, hne, pf]
  return some (pf, V)

/-- The step `step` takes at `a` (to `next`), by its rule's lemma (`UplcProof.Induction.Steps`):
    `(k, rest) ↦` a proof of `exec a (k + 1) = b` from `rest : exec next k = b`; `none` when
    the step has no lemma (a builtin, `case` on a constructor, …). With `mode < 2`, only the
    variable lookups. -/
def stepProof? (names : NameCache) (a next b : Expr) (mode := 2) :
    MetaM (Option (Expr → Expr → Expr)) := do
  let some c := a.getAppFn.constName? | return none
  let rule (n : Name) (xs : Array Expr) : Option (Expr → Expr → Expr) :=
    some fun k rest => mkAppN (mkConst n) (xs ++ #[k, b, rest])
  if c == ``State.Eval && a.getAppNumArgs == 3 then
    let args := a.getAppArgs
    let (s, ρ, t) := (args[0]!, args[1]!, args[2]!)
    let some tc := t.getAppFn.constName? | return none
    let ta := t.getAppArgs
    if tc == ``Term.Var && ta.size == 1 then
      let some (h, V) ← lookupProof? names s ρ ta[0]! next | return none
      return some fun k rest => mkAppN (mkConst ``Steps.evalVar) #[s, ρ, ta[0]!, V, k, b, h, rest]
    if mode < 2 then return none
    if tc == ``Term.Builtin && ta.size == 1 then
      return if mode ≥ 3 then rule ``Steps.evalBuiltinTerm (#[s, ρ] ++ ta) else none
    if tc == ``Term.Const && ta.size == 1 then return rule ``Steps.evalConst (#[s, ρ] ++ ta)
    if tc == ``Term.Lam && ta.size == 2 then return rule ``Steps.evalLam (#[s, ρ] ++ ta)
    if tc == ``Term.Delay && ta.size == 1 then return rule ``Steps.evalDelay (#[s, ρ] ++ ta)
    if tc == ``Term.Force && ta.size == 1 then return rule ``Steps.evalForce (#[s, ρ] ++ ta)
    if tc == ``Term.Apply && ta.size == 2 then return rule ``Steps.evalApply (#[s, ρ] ++ ta)
    if tc == ``Term.Case && ta.size == 2 then return rule ``Steps.evalCase (#[s, ρ] ++ ta)
    if tc == ``Term.Constr && ta.size == 2 then
      let ms := ta[1]!
      if ms.isAppOfArity ``List.cons 3 then
        return rule ``Steps.evalConstrCons #[s, ρ, ta[0]!, ms.appFn!.appArg!, ms.appArg!]
      if ms.isAppOfArity ``List.nil 1 then return rule ``Steps.evalConstrNil #[s, ρ, ta[0]!]
    return none
  if mode < 2 then return none
  if mode ≥ 3 then
    if let some (_, n, xs) := Fast.builtinStepFull? a then return rule n xs
  if c == ``State.Return && a.getAppNumArgs == 2 then
    let stk := a.appFn!.appArg!
    let v := a.appArg!
    if stk.isAppOfArity ``List.nil 1 then return rule ``Steps.retHalt #[v]
    unless stk.isAppOfArity ``List.cons 3 do return none
    let f := stk.appFn!.appArg!
    let s := stk.appArg!
    let some fc := f.getAppFn.constName? | return none
    let fa := f.getAppArgs
    if fc == ``PlutusCore.UPLC.CekMachine.Frame.LeftApplicationToTerm && fa.size == 2 then
      return rule ``Steps.retLeftAppTerm #[s, fa[1]!, fa[0]!, v]
    -- `fv` applied to `arg`
    let app (fv arg : Expr) (lamL biL : Name) : Option (Expr → Expr → Expr) :=
      if fv.isAppOfArity ``CekValue.VLam 3 then
        let la := fv.getAppArgs
        rule lamL #[s, la[2]!, la[0]!, la[1]!, arg]
      else if fv.isAppOfArity ``CekValue.VBuiltin 3 then
        let ba := fv.getAppArgs
        match Fast.moreArg? ba[2]! ``PlutusCore.UPLC.Builtins.ExpectedBuiltinArg.ArgV with
        | some η => rule biL #[s, ba[0]!, ba[1]!, η, arg]
        | none => none
      else none
    if fc == ``PlutusCore.UPLC.CekMachine.Frame.RightApplicationOfValue && fa.size == 1 then
      return app fa[0]! v ``Steps.retRightAppLam ``Steps.retRightAppBuiltin
    if fc == ``PlutusCore.UPLC.CekMachine.Frame.LeftApplicationToValue && fa.size == 1 then
      return app v fa[0]! ``Steps.retLeftAppLam ``Steps.retLeftAppBuiltin
    if fc == ``PlutusCore.UPLC.CekMachine.Frame.ForceFrame && fa.size == 0 then
      if v.isAppOfArity ``CekValue.VDelay 2 then
        return rule ``Steps.retForceDelay #[s, v.appArg!, v.appFn!.appArg!]
      if v.isAppOfArity ``CekValue.VBuiltin 3 then
        let ba := v.getAppArgs
        if let some η := Fast.moreArg? ba[2]! ``PlutusCore.UPLC.Builtins.ExpectedBuiltinArg.ArgQ then
          return rule ``Steps.retForceBuiltin #[s, ba[0]!, ba[1]!, η]
      return none
    if fc == ``PlutusCore.UPLC.CekMachine.Frame.ConstructorArgument && fa.size == 4 then
      let ms := fa[2]!
      if ms.isAppOfArity ``List.cons 3 then
        return rule ``Steps.retConstrArg #[s, fa[3]!, fa[0]!, fa[1]!, ms.appFn!.appArg!, ms.appArg!, v]
    return none
  return none

/-- `exec states[i] (j - i) = states[j]` (`i < j`), built from the end: each step with a rule
    by its lemma, around the rest of the run (`stepProof?`); the steps without one in maximal
    blocks by evaluation (`proveExec`), joined by `Steps.exec_app`. -/
def proveSteps (states : Nat → Expr) (i j : Nat) (mode := 2) (names : NameCache := none) :
    MetaM Expr := do
  let b := states j
  let mut acc := mkApp (mkConst ``UplcProof.exec_zero) b
  let mut rem := 0
  -- the steps in `[k + 1, blockEnd)` have no rule: one block by evaluation
  let mut blockEnd := j
  let mut k := j
  let block (lo hi rem : Nat) (acc : Expr) : MetaM Expr := do
    return mkAppN (mkConst ``Steps.exec_app) #[states lo, states hi, b, mkNatLit (hi - lo),
      mkRawNatLit rem, ← proveExec (states lo) (hi - lo) (states hi), acc]
  while k > i do
    k := k - 1
    if let some r ← stepProof? names (states k) (states (k + 1)) b mode then
      if k + 1 < blockEnd then
        acc ← block (k + 1) blockEnd rem acc
        rem := rem + (blockEnd - (k + 1))
      acc := r (mkRawNatLit rem) acc
      rem := rem + 1
      blockEnd := k
  if i < blockEnd then
    acc ← block i blockEnd rem acc
  mkExpectedTypeHint acc (← mkEq (mkApp2 (mkConst ``UplcProof.exec) (states i) (mkNatLit (j - i))) b)

/-- The segments of a run from `st0`, each with its proof: `(b, c, exec a c = b)`, `a` the
    end of the previous segment. By the lemmas when the run recorded its states
    (`uplc.stepLemmas`), else by evaluation. -/
def Stop.proofs (stop : Stop) (st0 : Expr) : MetaM (Array (Expr × Nat × Expr)) := do
  let mode := uplc.stepLemmas.get (← getOptions)
  let lemmas := stop.trace.size == stop.steps && mode != 0
  let names := (← session?).map (·.names)
  let states (k : Nat) : Expr := if k == 0 then st0 else stop.trace[k - 1]!
  let mut out := #[]
  let mut a := st0
  let mut n := 0
  for (b, c) in stop.segments do
    let pf ← if lemmas then timed "prove.steps" (proveSteps states n (n + c) mode names) else proveExec a c b
    out := out.push (b, c, pf)
    a := b
    n := n + c
  return out

/-! ### Straight runs, computed once and proved once

The branches of a proof run the same code many times: the test's run, for
instance, is the same from its start in every case of the validators before
it. `runToEnd` remembers each run by its start state (the states hold the
symbolic inputs as free variables, so equal states are the same run), and
`sharedRun` states a long run as an auxiliary theorem, which the kernel checks
once, whatever the number of branches that use it. -/

/-- `runUntil` with no stop but the final (or stuck) states, remembered by start state (in
    the session's caches; with no session, not remembered). -/
def runToEnd (cache : Cache) (st : Expr) (maxSteps : Nat) : MetaM Stop := do
  let chunk := uplc.chunk.get (← getOptions)
  let ses? ← if uplc.runCache.get (← getOptions) then session? else pure none
  let some ses := ses? | return ← runUntil cache st (fun _ => pure false) maxSteps chunk
  if let some s := (← ses.stops.get).get? st then
    if ← perfEnabled then perfAdd "run.cache-hit" 0
    return s
  let s ← runUntil cache st (fun _ => pure false) maxSteps chunk
  ses.stops.modify (·.insert st s)
  return s

/-- A proof of `ty`, an implication between two runs (`Reaches A' T → Reaches A T`, or
    `Reaches A T → Reaches A' T`), built by `mkTerm`: for `steps` or more steps (option
    `uplc.runLemmaMinSteps`; shorter runs are proved in place, since an auxiliary
    theorem costs the kernel a check of its statement, two whole states), an auxiliary
    theorem applied to the free variables it is about, shared by statement. The cached proof
    is used only while its theorem is in the environment (a backtracked attempt removes it). -/
def sharedRun (ty : Expr) (steps : Nat) (mkTerm : MetaM Expr) : MetaM Expr := do
  let minSteps := uplc.runLemmaMinSteps.get (← getOptions)
  if minSteps == 0 || steps < minSteps then return ← mkTerm
  let cache? := (← session?).map (·.runLemmas)
  if let some c := cache? then
    if let some e := (← c.get).get? ty then
      if let some n := e.getAppFn.constName? then
        if (← getEnv).contains n then
          if ← perfEnabled then perfAdd "runlemma.hit" 0
          return e
  -- `zetaDelta := true`: no `Meta.check` of the proof (it would re-run every step in
  -- `isDefEq`); the kernel checks it
  let e ← timed "runlemma.add" do mkAuxTheorem ty (← mkTerm) (zetaDelta := true)
  if let some c := cache? then c.modify (·.insert ty e)
  return e

end UplcProof.Sym
