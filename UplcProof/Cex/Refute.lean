import Lean
import UplcProof.Cex.Pretty
import UplcProof.Cex.Bridge
import UplcProof.Cex.Render

/-!
# `UplcProof.Cex.Refute`: proving `¬ ∀ x̄, P` at concrete values

`refute_with t₁, …, tₙ` closes a goal `¬ ∀ (x₁ : α₁) … (xₙ : αₙ), P` (or
`(∀ …) → False`): it instantiates the binders with the values, discharges every
hypothesis `H → …` of the statement at those values, and closes `¬ P[t̄]` with
the first closer that works, in order:

1. `decide`;
2. rfl-based: `exact fun h => h rfl` (`P` is `a ≠ b`), `Bool` equalities by
   evaluation (`Bool.false_ne_true`), `intro h; cases h` (constructors clash);
3. `simp +decide`, then `intro h; simp_all +decide`;
4. `uplc_cex_closer`, an extensible tactic: `UplcProof.Cex.Halts` adds the
   concrete CEK run for a `Halts p args v` / `Fails p args` conclusion;
5. if all fail: `¬ (A ∨ B)` by refuting both sides, `¬ (A ∧ B)` by refuting one
   (each side with 1–5 again).

Hypotheses are discharged by `decide`, `rfl`, `trivial`, `intro h; cases h`,
`simp +decide`, `uplc_cex_closer`, in that order.

A closer counts only if its proof term uses no axiom beyond `propext`,
`Quot.sound` and `Classical.choice` (`checkAxioms`: `sorryAx`,
`Lean.ofReduceBool`, `Blaster.Tactic.blasterProven` are rejected); error
recovery is off, so a failing tactic cannot leave a `sorry` behind.
`kernelCheck` additionally type-checks a proof in the kernel, in a throwaway
environment.

`refute_cex "x: <raw z3>", …` does the same from Blaster's raw entries: each value
is cleaned (`Pretty`) and elaborated at its binder's type (`Bridge`), matched by
binder name. An unknown name is an error naming it; a binder the entries leave
out (Blaster omits unconstrained binders) gets `default`, as in `analyse`, and is
named in an info message (`mkDefault?`; an error if its type has none).

Every closer attempt catches runtime exceptions too (`tryCatchRuntimeEx`): a
closer that runs out of heartbeats or recursion depth fails like any other, its
state and heartbeat count are restored, and the next closer is tried, each with
the full `maxHeartbeats` budget. One part is deliberately not limited: the
concrete CEK run of `uplc_cex_closer` (`UplcProof.Cex.Halts`) has no heartbeat
limit (it is bounded by `Tactic.maxSteps` CEK steps) and its heartbeats are not
counted.

Programmatic API (for `blaster_pretty`, `blaster_refute` and `uplc_auto`):
* `refuteCore (goal : MVarId) (supply : Supply) (expected? : Option Nat) : TacticM RefuteResult`
  closes `goal : ¬ S`; `supply i n ty` gives the value of the `i`-th binder `n : ty`.
* `refuteWithValues (goal : MVarId) (vals : Array Expr) : TacticM RefuteResult`.
* `refuteWithEntries (goal : MVarId) (entries : Array (String × String)) : TacticM RefuteResult`
  (binder name, raw z3 value).
* `binderNames (S : Expr) : MetaM (Array Name)`, `negated? (ty : Expr) : MetaM (Option Expr)`.
* `checkAxioms (e : Expr) : MetaM Unit`, `axiomsOf (e : Expr) : CoreM (Array Name)`,
  `kernelCheck (type value : Expr) : MetaM Unit`.
-/

open Lean Meta Elab Tactic Term

namespace UplcProof.Cex

/-! ## Axioms and the kernel -/

/-- The axioms a refutation may use. -/
def allowedAxioms : List Name := [``propext, ``Quot.sound, ``Classical.choice]

/-- Every axiom `e` depends on, transitively. Constants are looked up in the
    elaborator's environment, so auxiliary lemmas that the kernel has not checked
    yet are traversed too. -/
def axiomsOf (e : Expr) : CoreM (Array Name) := do
  let env ← getEnv
  let mut visited : NameSet := {}
  let mut axioms : Array Name := #[]
  let mut todo : Array Name := e.getUsedConstants
  while h : todo.size > 0 do
    let c := todo[todo.size - 1]
    todo := todo.pop
    if visited.contains c then continue
    visited := visited.insert c
    match env.find? c with
    | some (.axiomInfo _) => axioms := axioms.push c
    | some (.defnInfo v) => todo := todo ++ v.type.getUsedConstants ++ v.value.getUsedConstants
    | some (.thmInfo v) => todo := todo ++ v.type.getUsedConstants ++ v.value.getUsedConstants
    | some (.opaqueInfo v) => todo := todo ++ v.type.getUsedConstants ++ v.value.getUsedConstants
    | some (.inductInfo v) => todo := todo ++ v.type.getUsedConstants ++ v.ctors.toArray
    | some (.ctorInfo v) => todo := todo ++ v.type.getUsedConstants
    | some (.recInfo v) => todo := todo ++ v.type.getUsedConstants
    | _ => pure ()
  return axioms

/-- Throws unless `e` is complete (no metavariable) and its axioms are among
    `allowedAxioms`. -/
def checkAxioms (e : Expr) : MetaM Unit := do
  let e ← instantiateMVars e
  if e.hasExprMVar then throwError "the proof is incomplete (it has holes)"
  let bad := (← axiomsOf e).filter (!allowedAxioms.contains ·)
  unless bad.isEmpty do
    throwError "the proof uses axioms beyond propext, Quot.sound, Classical.choice: {bad.toList}"

/-- Type-checks `value : type` in the kernel, as a theorem added to a throwaway
    copy of the environment (the current one is not modified). Local hypotheses
    the terms mention are abstracted first. -/
def kernelCheck (type value : Expr) : MetaM Unit := do
  let type ← instantiateMVars type
  let value ← instantiateMVars value
  if type.hasMVar || value.hasMVar then throwError "kernel check: the proof is incomplete"
  let r ← Closure.mkValueTypeClosure type value (zetaDelta := true)
  let name ← mkAuxDeclName `_uplc_cex_refutation
  let decl := Declaration.thmDecl
    { name, levelParams := r.levelParams.toList, type := r.type, value := r.value }
  let opts ← getOptions
  match (← getEnv).addDeclCore (Core.getMaxHeartbeats opts).toUSize decl (← readThe Core.Context).cancelTk? with
  | .ok _ => pure ()
  | .error ex => throwError "the kernel rejects the refutation: {ex.toMessageData opts}"

/-! ## Closers -/

/-- The extension point for closers: `uplc_cex_closer` is tried last, on the
    refutation goal `¬ P[t̄]` and on every hypothesis to discharge. Add
    alternatives with `@[tactic UplcProof.Cex.cexCloser]` (or `macro_rules`); each
    is tried in turn and its failure undone. -/
syntax (name := cexCloser) "uplc_cex_closer" : tactic

@[tactic cexCloser] def evalCexCloserBase : Tactic := fun _ =>
  throwError "uplc_cex_closer: no extension applies to this goal"

/-- A named tactic that may close a goal. -/
structure Closer where
  name : String
  tac : TacticM Unit

/-- Closers for the refutation goal `¬ P[t̄]`, in order. -/
def refuteClosers : Array Closer := #[
  ⟨"decide", do evalTactic (← `(tactic| decide))⟩,
  ⟨"rfl", do evalTactic (← `(tactic| exact fun h => h rfl))⟩,
  ⟨"bool", do evalTactic (← `(tactic| first
      | exact fun h => Bool.false_ne_true h
      | exact fun h => Bool.false_ne_true h.symm))⟩,
  ⟨"cases", do evalTactic (← `(tactic| intro h; cases h))⟩,
  ⟨"simp", do evalTactic (← `(tactic| simp +decide))⟩,
  ⟨"simp_all", do evalTactic (← `(tactic| intro h; simp_all +decide))⟩,
  ⟨"uplc_cex_closer", do evalTactic (← `(tactic| uplc_cex_closer))⟩]

/-- Closers for a hypothesis `H` of the statement, at the values. -/
private def hypClosers : Array Closer := #[
  ⟨"decide", do evalTactic (← `(tactic| decide))⟩,
  ⟨"rfl", do evalTactic (← `(tactic| rfl))⟩,
  ⟨"trivial", do evalTactic (← `(tactic| trivial))⟩,
  ⟨"cases", do evalTactic (← `(tactic| intro h; cases h))⟩,
  ⟨"simp", do evalTactic (← `(tactic| simp +decide))⟩,
  ⟨"uplc_cex_closer", do evalTactic (← `(tactic| uplc_cex_closer))⟩]

/-- Runs closer `c` on `g`: success only if it closes `g`, without error
    recovery, with a proof whose axioms pass `checkAxioms`. Each attempt has the
    full `maxHeartbeats` budget; any failure, including running out of heartbeats
    or recursion depth, restores the state (and the heartbeat count) and returns
    the reason, so the next closer is tried. -/
def runCloser (g : MVarId) (c : Closer) : TacticM (Option String) := do
  let s ← saveState
  let hb ← IO.getNumHeartbeats
  -- `tryCatchRuntimeEx`: a closer that runs out of heartbeats or recursion depth
  -- fails like any other (plain `try … catch` rethrows those), and the next is tried
  tryCatchRuntimeEx
    (do
      let gs ← withCurrHeartbeats <| Term.withoutErrToSorry <| Tactic.run g (withoutRecover c.tac)
      unless gs.isEmpty do throwError "goals remain"
      checkAxioms (mkMVar g)
      return none)
    fun ex => do
      let msg ← ex.toMessageData.toString
      s.restore
      -- the failed attempt's work does not count against the enclosing declaration
      IO.setNumHeartbeats hb
      return some msg

/-- Tries `closers` in order on `g`; returns the name of the one that closed it,
    or the list of failures. -/
def closeWith (closers : Array Closer) (g : MVarId) : TacticM (Except (Array (String × String)) String) := do
  let mut fails := #[]
  for c in closers do
    match ← runCloser g c with
    | none => return .ok c.name
    | some why => fails := fails.push (c.name, why)
  return .error fails

private def failSummary (fails : Array (String × String)) : String :=
  ", ".intercalate (fails.toList.map fun (n, _) => n)

/-- `S` if `ty` is syntactically `¬ S` or `S → False`. -/
private def notArg? (ty : Expr) : Option Expr :=
  match ty with
  | .app (.const ``Not _) s => some s
  | .forallE _ d (.const ``False _) _ => some d
  | _ => none

/-- Closes `g : ¬ Q` with `refuteClosers`; failing that, splits a connective:
    `¬ (A ∨ B)` by refuting both sides, `¬ (A ∧ B)` by refuting one. Returns the
    closer(s) used, or the failures of the closers on `g` itself. -/
private partial def refuteGoal (g : MVarId) : TacticM (Except (Array (String × String)) String) := do
  match ← closeWith refuteClosers g with
  | .ok c => return .ok c
  | .error fails =>
    let some q := notArg? (← instantiateMVars (← g.getType)) | return .error fails
    match_expr q with
    | Or a b =>
        let g₁ ← mkFreshExprSyntheticOpaqueMVar (mkNot a)
        let g₂ ← mkFreshExprSyntheticOpaqueMVar (mkNot b)
        let .ok c₁ ← refuteGoal g₁.mvarId! | return .error fails
        let .ok c₂ ← refuteGoal g₂.mvarId! | return .error fails
        let pf ← withLocalDeclD `h q fun h =>
          mkLambdaFVars #[h] (mkAppN (mkConst ``Or.elim) #[a, b, mkConst ``False, h, g₁, g₂])
        g.assign pf
        return .ok s!"or({c₁}, {c₂})"
    | And a b =>
        for (side, proj) in [(a, ``And.left), (b, ``And.right)] do
          let g₁ ← mkFreshExprSyntheticOpaqueMVar (mkNot side)
          if let .ok c ← refuteGoal g₁.mvarId! then
            let pf ← withLocalDeclD `h q fun h =>
              mkLambdaFVars #[h] (mkApp g₁ (mkApp3 (mkConst proj) a b h))
            g.assign pf
            return .ok s!"and({c})"
        return .error fails
    | _ => return .error fails

/-! ## The refutation -/

/-- `S` if `ty` is `¬ S` or `S → False` (up to reducible unfolding). -/
partial def negated? (ty : Expr) : MetaM (Option Expr) := do
  let ty ← instantiateMVars ty
  match_expr ty with
  | Not s => return some s
  | _ =>
    if let .forallE _ d b _ := ty then
      if !b.hasLooseBVars && b.isConstOf ``False then return some d
    let ty' ← whnfR ty
    if ty' != ty then negated? ty' else return none

/-- `ty` if it is a `∀`/`let`, else its reducible unfolding if that is one. -/
private def exposeBinder (ty : Expr) : MetaM Expr := do
  if ty.isForall || ty.isLet then return ty
  let ty' ← whnfR ty
  if ty'.isForall || ty'.isLet then return ty' else return ty

/-- The names of the value binders of `S` (its `∀`s whose type is not a `Prop`), in order. -/
partial def binderNames (S : Expr) : MetaM (Array Name) := go S #[]
where
  go (ty : Expr) (acc : Array Name) : MetaM (Array Name) := do
    match ← exposeBinder ty with
    | .forallE n d b bi => withLocalDecl n bi d fun x => do
        let acc := if ← isProp d then acc else acc.push n
        go (b.instantiate1 x) acc
    | .letE _ _ v b _ => go (b.instantiate1 v) acc
    | _ => return acc

/-- One instantiated binder. -/
structure Binder where
  name : Name
  type : Expr
  value : Expr
  /-- The text the value was elaborated from (the cleaned z3 text), the last
      resort when rendering it. -/
  source? : Option String := none
  /-- Why this value, when it is not the caller's (`default`, …). -/
  note? : Option String := none
deriving Inhabited

/-- The value of the `i`-th binder, named `n`, of type `ty` (earlier values
    substituted): the value, its source text, a note. -/
abbrev Supply := Nat → Name → Expr → TacticM (Expr × Option String × Option String)

/-- A successful refutation. -/
structure RefuteResult where
  binders : Array Binder
  /-- `P[t̄]`, the conclusion at the values. -/
  conclusion : Expr
  /-- The closer that refuted it. -/
  closer : String
  /-- The proof assigned to the goal. -/
  proof : Expr
deriving Inhabited

/-- Closes `goal : ¬ S` (or `S → False`), `S = ∀ x̄, P` with hypotheses among the
    binders, at the values given by `supply`. `expected?`: the number of values
    the caller has (an error unless `S` has exactly that many binders). Throws, naming what
    failed: the goal's shape, a value, a hypothesis that does not hold, or the
    conclusion that no closer refutes. -/
def refuteCore (goal : MVarId) (supply : Supply) (expected? : Option Nat := none) :
    TacticM RefuteResult := goal.withContext do
  let gty ← instantiateMVars (← goal.getType)
  let some S ← negated? gty
    | throwError "the goal is not a negation `¬ ∀ x̄, P`:{indentExpr gty}"
  if let some k := expected? then
    let names ← binderNames S
    unless k == names.size do
      throwError "{k} value(s) given, but the statement has {names.size} binder(s): {names.toList}"
  -- The closers run in the goal's context *without* the statement `S` as a
  -- hypothesis: only the values may refute it (with `S` at hand, `simp_all`
  -- refutes a false statement whatever the values).
  let mut ty := S
  let mut args : Array Expr := #[]
  let mut bs : Array Binder := #[]
  repeat
    match ← exposeBinder ty with
    | .forallE n d b _ =>
        if ← isProp d then
          let g ← mkFreshExprSyntheticOpaqueMVar d
          match ← closeWith hypClosers g.mvarId! with
          | .ok _ => pure ()
          | .error fails =>
              throwError "the hypothesis{indentExpr d}\ndoes not hold at these values \
                (no closer proves it; tried {failSummary fails})"
          args := args.push g
          ty := b.instantiate1 g
        else
          let (v, source?, note?) ← supply bs.size n d
          unless ← isDefEq (← inferType v) d do
            throwError "the value of {n} has type{indentExpr (← inferType v)}\nbut the binder has type{indentExpr d}"
          args := args.push v
          ty := b.instantiate1 v
          bs := bs.push { name := n, type := d, value := v, source?, note? }
    | .letE _ _ v b _ => ty := b.instantiate1 v
    | _ => break
  let Q ← instantiateMVars ty
  let g ← mkFreshExprSyntheticOpaqueMVar (mkNot Q)
  let closer ← match ← refuteGoal g.mvarId! with
    | .ok c => pure c
    | .error fails =>
        throwError "these values do not refute the statement: no closer proves{indentExpr (mkNot Q)}\n\
          (tried {failSummary fails})"
  let proof ← withLocalDeclD `h S fun h => do
    instantiateMVars (← mkLambdaFVars #[h] (mkApp g (mkAppN h args)))
  checkAxioms proof
  goal.assign proof
  return { binders := bs, conclusion := Q, closer, proof }

/-- Elaborates a user's term at `ty`: no error recovery, no holes. -/
private def elabUserValue (stx : Syntax) (ty : Expr) : TacticM Expr := withRef stx do
  let e ← Term.withoutErrToSorry <| Term.withSynthesize <| Term.elabTermEnsuringType stx ty
  let e ← instantiateMVars e
  if e.hasExprMVar then throwError "the value{indentExpr e}\nhas unsolved holes"
  return e

/-- `refuteCore` with already elaborated values (checked against the binder types). -/
def refuteWithValues (goal : MVarId) (vals : Array Expr) : TacticM RefuteResult :=
  refuteCore goal (expected? := vals.size) fun i n _ => do
    let some v := vals[i]? | throwError "no value for binder {n} ({vals.size} values given)"
    return (v, none, none)

/-- A default value of type `ty`: `default`, from its `Inhabited` instance; else,
    for an inductive type without indices, its first constructor whose arguments
    all have default values (recursively, depth `fuel`), as `deriving Inhabited`
    would build it (`Data` has no `Inhabited` instance: `Data.Constr 0 []`;
    `TxOutRef`: `{ txOutRefId := ⟨""⟩, txOutRefIdx := 0 }`). -/
partial def mkDefault? (ty : Expr) (fuel : Nat := 8) : MetaM (Option Expr) := do
  let viaInstance ← try
      let inst ← synthInstance (← mkAppM ``Inhabited #[ty])
      pure (some (← mkAppOptM ``Inhabited.default #[ty, inst]))
    catch _ => pure none
  if viaInstance.isSome || fuel == 0 then return viaInstance
  let ty ← whnfR (← instantiateMVars ty)
  let .const I us := ty.getAppFn | return none
  let some (.inductInfo iv) := (← getEnv).find? I | return none
  let params := ty.getAppArgs
  unless iv.numIndices == 0 && params.size == iv.numParams do return none
  for c in iv.ctors do
    let some (.ctorInfo ci) := (← getEnv).find? c | continue
    let mut t ← instantiateForall (ci.type.instantiateLevelParams ci.levelParams us) params
    let mut args : Array Expr := #[]
    let mut ok := true
    for _ in [:ci.numFields] do
      let .forallE _ d b _ := t | ok := false; break
      let some a ← mkDefault? d (fuel - 1) | ok := false; break
      args := args.push a
      t := b.instantiate1 a
    if ok then return some (mkAppN (mkAppN (mkConst c us) params) args)
  return none

/-- The note on a binder the entries leave out, or give only z3's abstract value
    for (`isAbstractValue`) (`refuteWithEntries`). -/
private def defaultNote : String := "no concrete value in the counterexample: default"

/-- `refuteCore` with raw Blaster entries `(binder name, raw z3 value)`, matched
    by name (the `k`-th entry named `x` goes to the `k`-th binder named `x`).
    An unknown name is an error naming it. A binder the entries leave out (Blaster
    omits unconstrained ones), or give only z3's abstract value for (`$0`), gets
    a default value (`mkDefault?`), like `analyse` does, and only such a binder has
    a `Binder.note?`; if its type has no default value, that is an error naming
    it. -/
def refuteWithEntries (goal : MVarId) (entries : Array (String × String)) : TacticM RefuteResult := do
  let S ← goal.withContext do
    let some S ← negated? (← goal.getType)
      | throwError "the goal is not a negation `¬ ∀ x̄, P`:{indentExpr (← goal.getType)}"
    return S
  let names ← goal.withContext (binderNames S)
  let names := names.map (·.eraseMacroScopes.toString)
  let unknown := entries.filter (!names.contains ·.1) |>.map (·.1)
  unless unknown.isEmpty do
    throwError "unknown binder name(s): {", ".intercalate unknown.toList}. \
      The statement's binders are: {", ".intercalate names.toList}"
  let seen ← IO.mkRef ({} : Std.HashMap String Nat)
  refuteCore goal fun _ n ty => do
    let key := n.eraseMacroScopes.toString
    let k := (← seen.get).getD key 0
    seen.modify (·.insert key (k + 1))
    match (entries.filter (·.1 == key))[k]? with
    | some (_, raw) =>
        if isAbstractValue raw then
          -- z3's `$0` / `T!val!0`: no concrete value, the binder is unconstrained
          let some v ← mkDefault? ty
            | throwError "{key} has no concrete value in the counterexample ({raw.trim}), and its \
                type{indentExpr ty}\nhas no default value (no `Inhabited` instance, no constructor \
                with default arguments)"
          return (v, none, some defaultNote)
        let (v, text) ← try elabCexValue raw ty catch ex =>
          throwError "value of {key}: {ex.toMessageData}"
        return (v, some text, none)
    | none =>
        let some v ← mkDefault? ty
          | throwError "{key} is not in the counterexample, and its type{indentExpr ty}\n\
              has no default value (no `Inhabited` instance, no constructor with default arguments)"
        return (v, none, some defaultNote)

/-! ## Tactics -/

/-- `refute_with t₁, …, tₙ` closes `¬ ∀ (x₁ : α₁) … (xₙ : αₙ), P` by instantiating
    the binders with `t₁ … tₙ`, discharging the hypotheses of the statement at
    those values, and refuting `P[t̄]` (see the module doc for the closers). The
    proof uses no axiom beyond `propext`, `Quot.sound`, `Classical.choice`. -/
syntax (name := refuteWithTac) "refute_with" (ppSpace colGt term),* : tactic

@[tactic refuteWithTac] def evalRefuteWith : Tactic := fun stx => withMainContext do
  let terms := stx[1].getSepArgs
  let goal ← getMainGoal
  let _ ← refuteCore goal (expected? := terms.size) fun i n ty => do
    let some t := terms[i]? | throwError "refute_with: no value for binder {n} ({terms.size} given)"
    return (← elabUserValue t ty, none, none)
  replaceMainGoal []

/-- `refute_cex "x: <raw z3 value>", …` is `refute_with` from Blaster's raw
    counterexample entries (as Blaster logs them, `- ` and trailing whitespace
    tolerated): each value is cleaned and elaborated at its binder's type,
    matched by binder name. An unknown name is an error. A binder the entries
    leave out (Blaster omits unconstrained binders) gets `default`, named in an
    info message; one whose type has no default value (`mkDefault?`) is an error. -/
syntax (name := refuteCexTac) "refute_cex" (ppSpace colGt str),* : tactic

@[tactic refuteCexTac] def evalRefuteCex : Tactic := fun stx => withMainContext do
  let strs := stx[1].getSepArgs
  let entries ← strs.mapM fun s => withRef s do
    let some e := s.isStrLit? | throwError "refute_cex: expected a string literal"
    match splitEntry e with
    | .ok p => pure p
    | .error msg => throwError "refute_cex: {msg}"
  let r ← refuteWithEntries (← getMainGoal) entries
  replaceMainGoal []
  let defaults := r.binders.filter (·.note? == some defaultNote)
  unless defaults.isEmpty do
    let shown ← defaults.mapM fun b => do
      let text := (← renderLean b.value b.type).map (·.line) |>.getD "default"
      return s!"{b.name.eraseMacroScopes} := {text}"
    logInfo m!"refute_cex: no concrete value in the counterexample, set to a default value: \
      {", ".intercalate shown.toList}"

end UplcProof.Cex
