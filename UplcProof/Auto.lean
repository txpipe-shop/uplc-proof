import Lean
import Blaster
import UplcProof.Induction
import UplcProof.Encode
import UplcProof.Cex

/-!
# `uplc_auto`: one tactic for an Aiken property test

The goal is the claim of a property test about its body function (the test body
as a function of the test's inputs, exported with `aiken export`): it returns
`True` on every input:

```
∀ (x₁ : τ₁) … (xₙ : τₙ), Halts body.script [enc x₁, …, enc xₙ] (.VCon (.Bool true))
```

Also accepted: `Fails p args`, any value in place of `True`, leaves already
introduced, `Prop` hypotheses among the binders, and a definition that unfolds to
such a claim. `uplc_auto` either proves the goal with a proof term the kernel
checks, or fails with a message whose first line is machine-readable
(`UPLC-RESULT {…}`, below).

## Pipeline

1. **Blaster** (z3), within `timeout` seconds, on the bounded claim
   `∀ x̄, SafeState (exec (initState p args) N) v` (`NoHaltState (exec …)` for a
   `Fails` claim): "within `N` CEK steps the run has not gone wrong" (it halted
   with `v`, or is still running; `Error` or another value is wrong). `N` grows as `fuel/8`, `fuel/4`, `fuel/2`, `fuel`
   while Blaster says valid and time remains. Small `N` come first because they
   give small formulas: with the buggy factorial property of the tests, z3 finds
   `n = 2` at `N = 250` in about 0.5 s, but at `N = 1000` it gives up after its
   10 s timeout (nonlinear arithmetic).
   A counterexample to this claim is a real one (the machine is deterministic;
   `Halts.safe`, `Fails.noHalt`). It is turned into a refutation of the claim
   *as stated* (a proof of `¬ ∀ x̄, Halts …`) by running the CEK machine on it
   (`UplcProof.Cex.analyse`), checked by the kernel in a throwaway environment,
   and the tactic fails with status `refuted`. Blaster's "valid" is never used as
   a proof: it is recorded (`"blaster":"valid"`; the status is `oracle` only if
   the kernel stage then fails) and the kernel stage runs.
   `(bound := halts)` states the bounded claim as
   `cekExecuteProgram p args N = State.Halt v` instead. Running out of fuel is
   then a counterexample too, and z3 mostly returns such inputs (for both
   factorial properties of the tests with `(fuel := 300)`: `n = 0` at `N = 37`,
   the first bound, which every run exceeds; for the buggy one, never the real
   bug `n = 1, 2`). Such a counterexample is run concretely, found to halt with
   `v`, recorded as `spurious`, and the kernel stage runs.
2. **Kernel**: `uplc_run` (symbolic execution, no induction), and `uplc_induction`
   on each `Nat` or `List` leaf and on each `Int` leaf `x` through `x < 0`
   (`uplc_run`) / `x = ↑k` (induction on `k : Nat`), that is
   `rcases Int.lt_or_le x 0 with h | h; · uplc_run; · obtain ⟨x, rfl⟩ := Int.eq_ofNat_of_zero_le h; uplc_induction x`.
   `Bool` leaves are split (`cases`) first. If the script loops (it contains a
   self-application `s s`, how Aiken compiles recursion), the inductions are
   tried first and `uplc_run` last, with a quarter of the heartbeat budget, or
   `loopRunHeartbeats` if `maxHeartbeats` is `0` (on a loop over symbolic data
   it unrolls until it runs out); otherwise `uplc_run` comes first. Each attempt
   starts from the same state (a failure is undone) with its own heartbeat
   budget (`maxHeartbeats`), and neither stage counts against the declaration's
   heartbeats. The first attempt that closes the goal with a proof that passes
   `Cex.checkAxioms` (nothing beyond `propext`, `Quot.sound`, `Classical.choice`)
   and `Cex.kernelCheck` wins.
3. If nothing closed the goal, the tactic fails with status `oracle` (Blaster
   found no counterexample in runs of up to `N` steps, but there is no kernel
   proof), `falsified` (Blaster's counterexample could not be confirmed) or
   `unknown`, followed by the most useful error of the kernel stage.

## Syntax

```
uplc_auto [t₁, t₂] (timeout := s) (fuel := N) (loop := fun k => r) (bound := safe|halts) generalizing acc
```

Each part is optional; the options after the lemmas come in any order.
* `[t₁, t₂]`: lemmas and definitions for the kernel stage, as for
  `uplc_induction`. `lessThanInteger`, `lessThanEqualsInteger`, `equalsInteger`,
  `equalsByteString` and `beq_self_eq_true` are always added.
* `(loop := fun k => r)`: what the script's loop returns for `k` (`fun k a => r`
  with an accumulator); `k : Nat` for an `Int` or `Nat` leaf, `k : List α` for a
  list leaf.
* `generalizing acc`: the loop's accumulator (`uplc_induction n generalizing acc`).
* `timeout`: seconds for the Blaster stage, `0` skips it (default 10).
* `fuel`: the largest `N` (default 1000).
* `bound`: `safe` (default) or `halts`, see above.

## Output (the first line of the message)

`UPLC-RESULT ` and one JSON object, each key once:

* proved (info):
  `UPLC-RESULT {"status":"proved","kernel":true,"method":"uplc_induction","leaf":"n","blaster":"valid","fuel":1000,"ms":{…}}`.
  `method` is `uplc_run` or `uplc_induction`; `leaf` is the induction leaf;
  `blaster` is `valid` (no counterexample up to `fuel` steps), `undetermined`,
  `spurious` (with `"spurious":{name: json}`), `falsified`, `error` or `skipped`
  (then no `fuel`).
* refuted (error): the `UplcProof.Cex` contract (`Cex.Report`): keys `status`,
  `kernel`, `cex`, `lean`, `closer`, `defaults` (if any), `ms`, then `"fuel"`
  (the bound at which Blaster found it); then `name := <lean>` lines and the
  ready-to-paste refutation (`refute_with`).
* oracle, unknown (error):
  `{"status":…,"kernel":false,"cex":{},"lean":{},"blaster":…,"fuel":…,"reason":…,"ms":…}`
  (`blaster`, `fuel`, `spurious` as for proved).
* falsified (error): `Cex.Report`'s keys (`status`, `kernel`, `cex`, `lean`,
  `closer` and `defaults` if any, `reason`), then `"blaster":"falsified"`,
  `"fuel"` and `"ms"`.
* a goal of the wrong shape, an unknown option, a lemma that does not elaborate
  (error): `{"status":"error","kernel":false,"reason":…}`.

`ms` (milliseconds: `blaster`, `kernel`, `total`; for refuted `blaster`, `refute`,
`render`, `total`; for falsified `blaster`, `refute`, `render`, `kernel`, `total`)
is omitted with `set_option uplc.cex.timings false`, which makes the line
deterministic. `set_option trace.uplc.auto true` logs each Blaster
call (and Blaster's own phase timings, on stdout).

Nothing here is trusted: a proof is a term the kernel checks; Blaster only
chooses what to try and which input to run. Tests: `UplcProofTests.Auto`.
-/

open PlutusCore.UPLC.Term PlutusCore.UPLC.CekValue PlutusCore.UPLC.CekMachine

namespace UplcProof

/-! ## The bounded claim -/

/-- The state `s`, reached after some steps, has not gone wrong: it halted with
    `v`, or it is still running. -/
def SafeState (s : State) (v : CekValue) : Prop :=
  match s with
  | .Halt w => w = v
  | .Error => False
  | _ => True

/-- The state `s` has not halted with a value. -/
def NoHaltState (s : State) : Prop :=
  match s with
  | .Halt _ => False
  | _ => True

/-- Why a counterexample to the bounded claim is a real one: if the claim holds,
    no prefix of the run goes wrong. -/
theorem Halts.safe {p : Program} {args : List Term} {v : CekValue} (h : Halts p args v)
    (N : Nat) : SafeState (exec (initState p args) N) v := by
  obtain ⟨n, hn⟩ := h.reaches
  rcases Nat.le_total n N with hle | hle
  · rw [exec_halt_mono hn hle]
    exact rfl
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
    rw [exec_add] at hn
    generalize exec (initState p args) N = s at hn ⊢
    cases s with
    | Halt w => rw [exec_halt] at hn; cases hn; exact rfl
    | Error => rw [exec_error] at hn; cases hn
    | Eval => exact True.intro
    | Return => exact True.intro

/-- The same for a `Fails` claim: if it holds, no prefix of the run has halted
    with a value. -/
theorem Fails.noHalt {p : Program} {args : List Term} (h : Fails p args) (N : Nat) :
    NoHaltState (exec (initState p args) N) := by
  have hne : ∀ w, exec (initState p args) N ≠ .Halt w := fun w hw =>
    h N w (by rw [cekExecuteProgram_eq, runSteps_iff_exec]; exact hw)
  generalize exec (initState p args) N = s at hne ⊢
  cases s with
  | Halt w => exact hne w rfl
  | Error => exact True.intro
  | Eval => exact True.intro
  | Return => exact True.intro

/-- An option of `uplc_auto`: `(timeout := s)`, `(fuel := N)`, `(loop := fun k => r)`,
    `(bound := safe|halts)`. -/
syntax uplcAutoOpt := " (" ident " := " term ")"
/-- `generalizing acc`: the loop's accumulator. -/
syntax uplcAutoGen := " generalizing " ident

/-- `uplc_auto [lemmas] (timeout := s) (fuel := N) (loop := fun k => r) (bound := safe|halts) generalizing acc`
    proves `∀ x̄, Halts p [enc x̄] v` (or `Fails p args`) with a kernel-checked
    proof, or fails with a counterexample whose refutation the kernel checked
    (`refuted`), or with what Blaster found (`oracle`, `falsified`, `unknown`).
    The first line of its message is `UPLC-RESULT {…}` (JSON). See
    `UplcProof.Auto`'s module doc. -/
syntax (name := uplcAutoTac) "uplc_auto" (" [" Lean.Parser.Tactic.simpArg,* "]")?
  (uplcAutoOpt <|> uplcAutoGen)* : tactic

open Lean Meta Elab Tactic

initialize registerTraceClass `uplc.auto

namespace Auto

/-! ## Options -/

/-- How the bounded claim for Blaster is stated. -/
inductive Bound where
  /-- `SafeState (exec (initState p args) N) v`: only a run that goes wrong
      within `N` steps is a counterexample. -/
  | safe
  /-- `cekExecuteProgram p args N = .Halt v`: a run longer than `N` steps is a
      counterexample too (spurious). -/
  | halts
deriving BEq, Inhabited

/-- The options of `uplc_auto` (see the module doc). -/
structure Opts where
  /-- Seconds for the Blaster stage; `0` skips it. -/
  timeout : Nat := 10
  /-- The largest bound `N` (CEK steps). -/
  fuel : Nat := 1000
  /-- How the bounded claim is stated (`(bound := safe|halts)`). -/
  bound : Bound := .safe
  /-- The lemmas `[t₁, t₂]`, for the kernel stage. -/
  simpArgs : Array Syntax := #[]
  /-- `(loop := fun k => r)`: what the script's loop returns. -/
  loop? : Option Syntax := none
  /-- `generalizing acc`: the loop's accumulator. -/
  gen? : Option Ident := none

/-! ## Output -/

/-- `UPLC-RESULT {k₁:v₁,…}` (values already JSON). -/
private def resultLine (kvs : List (String × String)) : String :=
  "UPLC-RESULT " ++ Cex.jsonObj kvs

/-- Appends keys to an `UPLC-RESULT {…}` line (keys it does not have yet). -/
private def appendKeys (line : String) (kvs : List (String × String)) : String :=
  if kvs.isEmpty then line else
  (line.dropRight 1) ++ "," ++ ((Cex.jsonObj kvs).drop 1)

/-- A usage error: the `UPLC-RESULT` line (status `error`), then `msg`. -/
private def usageError (reason : String) (msg : MessageData) : TacticM α :=
  throwError "{resultLine [("status", Cex.jsonStr "error"), ("kernel", "false"),
    ("reason", Cex.jsonStr reason)]}\n{msg}"

/-- Runs `x`; an error it throws becomes a usage error (`reason`, then the error). -/
private def asUsageError (reason : String) (x : TacticM α) : TacticM α := do
  try x catch ex => usageError reason ex.toMessageData

/-- The error for a goal `uplc_auto` does not handle. -/
private def shapeError (reason : String) (ty : Expr) : TacticM α := do
  usageError reason m!"uplc_auto: {reason}:{indentExpr ty}\nExpected a goal `∀ (x₁ : τ₁) … (xₙ : τₙ), Halts p [enc x₁, …] v` \
    (or `Fails p args`), e.g. `∀ n : Int, Halts body.script [int n] vTrue`."

/-! ## The goal -/

/-- `Halts p args v` (`some v`) or `Fails p args` (`none`), up to reducible
    definitions (`Accepts`). -/
def conclusion? (ty : Expr) : MetaM (Option (Expr × Expr × Option Expr)) :=
  Tactic.runGoal? ty

/-- Opens the binders of `ty` (unfolding reducible definitions, and other
    definitions when they are not a claim yet) down to a `Halts`/`Fails`
    conclusion; `k xs concl`. `concl` is whatever is left if there is no such
    claim. -/
partial def telescope (ty : Expr) (k : Array Expr → Expr → MetaM α) : MetaM α :=
  go ty #[]
where
  go (ty : Expr) (xs : Array Expr) : MetaM α := do
    let ty ← instantiateMVars ty
    match ty with
    | .forallE n d b bi => withLocalDecl n bi d fun x => go (b.instantiate1 x) (xs.push x)
    | .mdata _ e => go e xs
    | _ =>
      if (← conclusion? ty).isSome then return ← k xs ty
      let ty' ← whnfR ty
      if ty'.isForall then return ← go ty' xs
      match ← unfoldDefinition? ty' with
      | some t => go t xs
      | none => k xs ty

/-- `ty` itself if it is a `Halts`/`Fails` claim (up to reducible definitions),
    else the claim it unfolds to through other definitions, as `telescope`
    unfolds a conclusion (`myClaim cap amount` with `def myClaim … := Halts …`);
    `none` if there is none. -/
partial def claim? (ty : Expr) : MetaM (Option Expr) := do
  let ty ← instantiateMVars ty
  if (← conclusion? ty).isSome then return some ty
  match ← unfoldDefinition? (← whnfR ty) with
  | some t => claim? t
  | none => return none

/-- The local hypotheses the goal `ty` depends on, and every `Prop` hypothesis
    (with what it depends on), in context order. -/
def relevantContext (ty : Expr) : MetaM (Array Expr) := do
  let lctx ← getLCtx
  let mut keep : FVarIdSet := (collectFVars {} (← instantiateMVars ty)).fvarSet
  for d in lctx do
    if d.isImplementationDetail then continue
    if ← isProp d.type then keep := keep.insert d.fvarId
  -- close under the types (and values) of what is kept
  let mut changed := true
  while changed do
    changed := false
    for d in lctx do
      unless keep.contains d.fvarId do continue
      let deps := collectFVars {} (← instantiateMVars d.type)
      let deps := match d.value? with
        | some v => collectFVars deps v
        | none => deps
      for x in deps.fvarIds do
        unless keep.contains x do
          keep := keep.insert x
          changed := true
  return lctx.foldl (init := #[]) fun acc d =>
    if !d.isImplementationDetail && keep.contains d.fvarId then acc.push d.toExpr else acc

/-- The claim of goal `g`, closed over its context: `∀ (context) x̄, concl`, with
    the number of binders of the goal itself. Throws (status `error`) on a goal
    that is not a claim. -/
def statement (g : MVarId) : TacticM (Expr × Nat) := g.withContext do
  let ty ← instantiateMVars (← g.getType)
  let ctx ← relevantContext ty
  let r? ← telescope ty fun xs concl => do
    let some _ ← conclusion? concl | return none
    return some (← mkForallFVars (ctx ++ xs) concl, xs.size)
  let some r := r? | shapeError "the goal is not a claim about a run of a script" ty
  if r.1.hasMVar then shapeError "the goal has metavariables" ty
  return r

/-- The bounded claim at fuel `N`: the statement with its conclusion replaced. -/
def boundedClaim (stmt : Expr) (bound : Bound) (N : Nat) : MetaM Expr :=
  telescope stmt fun xs concl => do
    let some (p, args, v?) ← conclusion? concl | throwError "uplc_auto: internal error (claim)"
    let st := mkApp2 (mkConst ``exec) (mkApp2 (mkConst ``initState) p args) (mkNatLit N)
    let body ← match v?, bound with
      | some v, .safe => pure (mkApp2 (mkConst ``SafeState) st v)
      | some v, .halts =>
          mkEq (mkApp3 (mkConst ``cekExecuteProgram) p args (mkNatLit N))
            (mkApp (mkConst ``State.Halt) v)
      | none, _ => pure (mkApp (mkConst ``NoHaltState) st)
    mkForallFVars xs body

/-! ## Stage 1: Blaster -/

/-- What the Blaster stage found, when it does not refute the claim. -/
structure BlasterStage where
  /-- `valid`, `undetermined`, `spurious`, `falsified`, `error`, `skipped`. -/
  outcome : String := "skipped"
  /-- The bound of `outcome` (for `valid`: the largest `N` Blaster says valid at). -/
  fuel? : Option Nat := none
  /-- `spurious`: the counterexample, as `{name: json}`. -/
  spurious? : Option String := none
  /-- `falsified`: Blaster's counterexample, not confirmed (its timings include
      `blaster`, the time until Blaster's answer). -/
  report? : Option Cex.Report := none
  /-- `error`: why Blaster failed. -/
  reason? : Option String := none
  /-- Milliseconds the stage took. -/
  ms : Nat := 0

/-- The values of `stmt`'s binders given by Blaster's `entries` substituted, and
    its conclusion's program, arguments and claimed value; with the values as a
    JSON object (names made distinct as in `Cex.analyse`). `none` if a value is
    missing. -/
def atValues (stmt : Expr) (entries : Array (String × String)) :
    TacticM (Option (Expr × Expr × Option Expr × String)) := do
  let cands ← Cex.collectValues stmt entries
  if cands.any (·.value?.isNone) then return none
  let names := Cex.distinctNames (cands.map (·.name.eraseMacroScopes.toString))
  let mut json : Array (String × String) := #[]
  for (c, name) in cands.zip names do
    json := json.push (name, (← Cex.jsonOf c.value?.get! c.type).compress)
  let mut ty := stmt
  let mut i := 0
  repeat
    let ty' ← if ty.isForall then pure ty else whnfR ty
    match ty' with
    | .forallE _ d b _ =>
        if ← isProp d then
          ty := b.instantiate1 (← mkFreshExprMVar d)
        else
          ty := b.instantiate1 cands[i]!.value?.get!
          i := i + 1
    | _ => break
  let some (p, args, v?) ← conclusion? ty | return none
  let obj := Cex.jsonObj json.toList
  return some (← instantiateMVars p, ← instantiateMVars args, ← v?.mapM instantiateMVars, obj)

/-- Whether the run at Blaster's counterexample does what the claim says
    (halts with `v`; for `Fails`, fails): then the counterexample only says the
    bound ran out. Returns the counterexample's JSON if so. -/
def checkSpurious (stmt : Expr) (entries : Array (String × String)) (fuel : Nat) :
    TacticM (Option String) := do
  let s ← saveState
  let r ← tryCatchRuntimeEx
    (do
      let some (p, args, v?, obj) ← atValues stmt entries | return none
      let (T, _) ← withCurrHeartbeats (Tactic.evalRun p args fuel)
      let ok ← match v? with
        | some v => pure (T.isAppOfArity ``State.Halt 1 && (← withNewMCtxDepth (isDefEq T.appArg! v)))
        | none => pure (T.isConstOf ``State.Error)
      return if ok then some obj else none)
    (fun _ => return none)
  s.restore
  return r

/-- The bounds tried, smallest first. -/
def schedule (fuel : Nat) : List Nat :=
  [fuel / 8, fuel / 4, fuel / 2, fuel].filter (0 < ·) |>.eraseDups

/-- Stage 1. Returns `.error msg` when the claim is refuted (`msg`: the
    message to fail with), else what Blaster found. -/
def blasterStage (stmt : Expr) (opts : Opts) (timings : Bool) :
    TacticM (Except String BlasterStage) := do
  if opts.timeout == 0 then return .ok {}
  let t0 ← IO.monoMsNow
  let budget := opts.timeout * 1000
  let mut st : BlasterStage := {}
  for N in schedule opts.fuel do
    let elapsed := (← IO.monoMsNow) - t0
    if elapsed + 1000 > budget then break
    let claim ← boundedClaim stmt opts.bound N
    let msgs := (← getThe Core.State).messages
    let sOpts : Blaster.Options.BlasterOptions :=
      { timeout := some ((budget - elapsed) / 1000)
        -- Blaster's phase timings (on stdout) with the trace
        verbose := if ← isTracingEnabledFor `uplc.auto then 1 else 0 }
    let tN ← IO.monoMsNow
    -- also runtime exceptions (deep recursion on a large term): Blaster's failure is not ours
    let res ← tryCatchRuntimeEx (Except.ok <$> Cex.runBlaster claim sOpts) fun ex =>
      return .error (← ex.toMessageData.toString)
    let outcome ← match res with
      | .ok o => pure (some o)
      | .error why =>
          -- keep the last bound that was valid, if any
          st := if st.outcome == "valid" then { st with reason? := some why }
            else { st with outcome := "error", fuel? := some N, reason? := some why }
          pure none
    modifyThe Core.State fun s => { s with messages := msgs }
    let what := match outcome with
      | some .valid => "valid" | some (.falsified _) => "falsified"
      | some (.undetermined _) => "undetermined" | none => "error"
    trace[uplc.auto] "Blaster, N = {N} (z3 timeout {sOpts.timeout.getD 0} s): {what}, \
      {(← IO.monoMsNow) - tN} ms"
    let some outcome := outcome | break
    match outcome with
    | .valid =>
        st := { st with outcome := "valid", fuel? := some N }
    | .undetermined _ =>
        -- keep the last bound that was valid, if any
        if st.outcome != "valid" then st := { st with outcome := "undetermined", fuel? := some N }
        break
    | .falsified entries =>
        let tB := (← IO.monoMsNow) - t0
        let s ← saveState
        let r ← tryCatchRuntimeEx (Prod.fst <$> Cex.analyse stmt entries) fun ex => do
          let why ← ex.toMessageData.toString
          s.restore
          return { status := .falsified, reason? := some why : Cex.Report }
        if r.status == .refuted then
          let t := (← IO.monoMsNow) - t0
          let r := { r with timings := #[("blaster", tB)] ++ r.timings ++ #[("total", t)] }
          let msg := r.message timings
          let (first, rest) := match msg.splitOn "\n" with
            | l :: ls => (l, ls)
            | [] => ("", [])
          let line := appendKeys first [("fuel", toString N)]
          return .error ("\n".intercalate (line :: rest))
        match ← checkSpurious stmt entries (max 20000 (4 * N)) with
        | some obj =>
            st := { st with outcome := "spurious", fuel? := some N, spurious? := some obj }
        | none =>
            st := { st with outcome := "falsified", fuel? := some N,
                            report? := some { r with timings := #[("blaster", tB)] ++ r.timings } }
        break
  return .ok { st with ms := (← IO.monoMsNow) - t0 }

/-! ## Stage 2: the kernel -/

/-- Whether the program `p` (a constant or a literal) has a self-application
    `s s`: how Aiken compiles a recursive function. -/
def hasLoop (p : Expr) : MetaM Bool := do
  let mut p ← instantiateMVars p
  for _ in [0:16] do
    if p.isAppOf ``Program.Program then break
    let p' ← whnf p
    if p' == p then break
    p := p'
  return (p.find? fun e =>
    e.isAppOfArity ``Term.Apply 2 && (e.getArg! 0).isAppOfArity ``Term.Var 1 &&
      e.getArg! 0 == e.getArg! 1).isSome

/-- The local hypothesis named `n`. -/
def fvarNamed (n : Name) : MetaM Expr := return (← getLocalDeclFromUserName n).toExpr

/-- Runs `k` on each goal of `cases` on the `Bool` leaves `bs` (by name). -/
partial def withBoolCases (g : MVarId) (bs : List Name) (k : MVarId → TacticM Unit) :
    TacticM Unit := do
  match bs with
  | [] => k g
  | b :: rest => g.withContext do
    let x ← fvarNamed b
    for sg in ← g.cases x.fvarId! do
      try withBoolCases sg.mvarId rest k
      catch ex => throwError "case {b} := {sg.ctorName.componentsRev.head!}: {ex.toMessageData}"

/-- `(loop := …)` elaborated as a function of the induction variable (of type `τ`)
    and the accumulator. -/
def elabLoop (opts : Opts) (τ : Expr) (acc? : Option Expr) : TacticM (Option Expr) := do
  let some stx := opts.loop? | return none
  let mut ty := mkConst ``CekValue
  if let some a := acc? then ty ← mkArrow (← inferType a) ty
  ty ← mkArrow τ ty
  let e ← Term.withoutErrToSorry <| Term.withSynthesize <| Term.elabTermEnsuringType stx ty
  let e ← instantiateMVars e
  if e.hasExprMVar then throwError "uplc_auto: `(loop := …)` has unsolved holes:{indentExpr e}"
  return some e

/-- `generalizing acc`, in the current context. -/
def accFVar? (opts : Opts) : MetaM (Option Expr) :=
  opts.gen?.mapM fun x => fvarNamed x.getId

/-- `uplc_induction x` in goal `g` (on its own; `x` by name). -/
def inductionOn (opts : Opts) (simpArgs : Array Syntax) (g : MVarId) (x : Name) : TacticM Unit :=
  g.withContext do
    let n ← fvarNamed x
    let acc? ← accFVar? opts
    let loop? ← elabLoop opts (← whnfR (← inferType n)) acc?
    setGoals [g]
    Tactic.uplcInduction n acc? simpArgs loop?
    unless (← getGoals).isEmpty do throwError "uplc_induction left goals"

/-- For an `Int` leaf `x`: `x < 0` by `uplc_run`, and `x = ↑k` by `uplc_induction`
    on `k : Nat` (named `x` too). -/
def intInductionOn (opts : Opts) (simpArgs : Array Syntax) (g : MVarId) (x : Name) :
    TacticM Unit := g.withContext do
  setGoals [g]
  let xId := mkIdent x
  evalTactic (← `(tactic| rcases Int.lt_or_le $xId 0 with h | h))
  let [gNeg, gPos] ← getGoals | throwError "uplc_auto: internal error (Int split)"
  try Tactic.runOn gNeg none s!"run, case {x} < 0" simpArgs
  catch ex => throwError "case {x} < 0: {ex.toMessageData}"
  setGoals [gPos]
  -- `rfl` unhygienic: the `rcases` pattern, not a name
  let rflId := mkIdent `rfl
  evalTactic (← `(tactic| obtain ⟨$xId, $rflId:ident⟩ := Int.eq_ofNat_of_zero_le h))
  let g' ← getMainGoal
  try inductionOn opts simpArgs g' x
  catch ex => throwError "case {x} = ↑k (k : Nat): {ex.toMessageData}"

/-- One way to prove the goal. -/
structure Attempt where
  /-- `uplc_run` or `uplc_induction` (the `"method"` key). -/
  method : String
  /-- The induction leaf (the `"leaf"` key). -/
  leaf? : Option Name := none
  /-- Its heartbeat budget (in thousands, as `maxHeartbeats`), if not `maxHeartbeats`. -/
  heartbeats? : Option Nat := none
  /-- Runs it on the goal. -/
  run : MVarId → TacticM Unit

/-- Runs `a` on `g` with its own heartbeat budget; succeeds if it closes `g` with
    a proof the kernel accepts and that uses no axiom beyond `propext`,
    `Quot.sound`, `Classical.choice`. On failure the state is restored and the
    error returned (as text: it may mention undone metavariables). -/
def runAttempt (g : MVarId) (a : Attempt) : TacticM (Except String Unit) := do
  let s ← saveState
  -- the attempt's heartbeats do not count against the rest of the declaration
  let h ← IO.getNumHeartbeats
  let budget (x : TacticM (Except String Unit)) : TacticM (Except String Unit) :=
    match a.heartbeats? with
    | some n => withTheReader Core.Context (fun c => { c with maxHeartbeats := n * 1000 }) x
    | none => x
  let r ← tryCatchRuntimeEx
    (budget <| withCurrHeartbeats do
      Term.withoutErrToSorry <| a.run g
      let pf ← instantiateMVars (mkMVar g)
      if pf.hasExprMVar then throwError "the proof is incomplete"
      Cex.checkAxioms pf
      g.withContext do Cex.kernelCheck (← instantiateMVars (← g.getType)) pf
      return .ok ())
    (fun ex => do
      let msg ← g.withContext do (← addMessageContext ex.toMessageData).toString
      s.restore
      return .error msg)
  IO.setNumHeartbeats h
  return r

/-- The heartbeat budget (in thousands, as `maxHeartbeats`) of the `uplc_run`
    attempt on a script that loops, when `maxHeartbeats` is `0` (no limit): on a
    loop over symbolic data `uplc_run` would otherwise run forever. A quarter of
    Lean's default `maxHeartbeats`. -/
def loopRunHeartbeats : Nat := 50000

/-- The attempts for goal `g` (with its binders introduced), in order. -/
def attempts (g : MVarId) (opts : Opts) (simpArgs : Array Syntax) : TacticM (Array Attempt) :=
  g.withContext do
    let some (p, args, _) ← conclusion? (← instantiateMVars (← g.getType))
      | throwError "uplc_auto: internal error (goal)"
    let args ← instantiateMVars args
    let gen := opts.gen?.map (·.getId)
    let mut bools : Array Name := #[]
    let mut ind : Array (Name × Bool) := #[]  -- (leaf, isInt)
    for d in ← getLCtx do
      if d.isImplementationDetail || (← isProp d.type) then continue
      unless args.containsFVar d.fvarId do continue
      let ty ← whnfR (← instantiateMVars d.type)
      if ty.isConstOf ``Bool then bools := bools.push d.userName
      else if some d.userName == gen then continue
      else if ty.isConstOf ``Nat || ty.isAppOfArity ``List 1 then ind := ind.push (d.userName, false)
      else if ty.isConstOf ``Int then ind := ind.push (d.userName, true)
    let bs := bools.toList
    let loops ← hasLoop p
    let maxHb := maxHeartbeats.get (← getOptions)
    let run : Attempt := {
      method := "uplc_run"
      -- on a script that loops, symbolic execution alone unrolls the loop until it runs
      -- out of heartbeats: a quarter of the budget, after the inductions (never `0`,
      -- which would mean no limit)
      heartbeats? := if loops then
          some (if maxHb == 0 then loopRunHeartbeats else max 1 (maxHb / 4))
        else none
      run := fun g => withBoolCases g bs fun g => Tactic.runOn g none "run" simpArgs }
    let inds := ind.map fun (x, isInt) => ({
      method := "uplc_induction"
      leaf? := some x
      run := fun g => withBoolCases g bs fun g =>
        if isInt then intInductionOn opts simpArgs g x else inductionOn opts simpArgs g x } : Attempt)
    return if loops then inds.push run else #[run] ++ inds

/-- Comparisons on integers and byte strings, unfolded for `uplc_eq`
    (`lessThanInteger 0 x` to `decide (0 < x)`), and `beq_self_eq_true`. -/
def defaultLemmas : Array Name :=
  #[``PlutusCore.Integer.lessThanInteger, ``PlutusCore.Integer.lessThanEqualsInteger,
    ``PlutusCore.Integer.equalsInteger, ``PlutusCore.ByteString.equalsByteString,
    ``beq_self_eq_true]

/-! ## The tactic -/

/-- Parses the options of `uplc_auto`. -/
def parseOpts (stx : Syntax) : TacticM Opts := do
  let mut o : Opts := {}
  if stx[1].getNumArgs > 0 then o := { o with simpArgs := stx[1][1].getSepArgs }
  for item in stx[2].getArgs do
    if item.getKind == ``uplcAutoGen then
      o := { o with gen? := some ⟨item[1]⟩ }
      continue
    let name := item[1].getId
    let val := item[3]
    let nat (what : String) : TacticM Nat := do
      let some n := val.isNatLit? | throwErrorAt val "uplc_auto: `{what}` takes a number"
      return n
    match name with
    | `timeout => o := { o with timeout := ← nat "timeout" }
    | `fuel => o := { o with fuel := ← nat "fuel" }
    | `loop => o := { o with loop? := some val }
    | `bound =>
        match val.getId with
        | `safe => o := { o with bound := .safe }
        | `halts => o := { o with bound := .halts }
        | _ => throwErrorAt val "uplc_auto: `bound` is `safe` or `halts`"
    | _ => throwErrorAt item[1] "uplc_auto: unknown option `{name}` (timeout, fuel, loop, bound)"
  return o

/-- The `"ms"` key, if timings are on. -/
private def msKey (timings : Bool) (ms : List (String × Nat)) : List (String × String) :=
  if timings then [("ms", Cex.jsonObj (ms.map fun (k, v) => (k, toString v)))] else []

/-- The message when no attempt closed the goal; `kernelMs`, `totalMs`: the
    milliseconds of the kernel stage and of the whole tactic. -/
def failure (b : BlasterStage) (opts : Opts) (loops : Bool) (errors : Array (Attempt × String))
    (kernelMs totalMs : Nat) (timings : Bool) : String := Id.run do
  let blasterKeys := keysOf b
  let label (a : Attempt) : String := match a.leaf? with
    | some x => s!"{a.method} {x}"
    | none => a.method
  -- the most useful error: an induction's when the script loops, else the first attempt's
  let best? := if loops then errors.find? (·.1.leaf?.isSome) <|> errors[0]? else errors[0]?
  let summary := "\n".intercalate (errors.toList.map fun (a, m) =>
    s!"  - {label a}: {(m.splitOn "\n").headD ""}")
  let kernelPart := match best? with
    | some (a, m) => s!"Kernel stage (every attempt failed):\n{summary}\nThe error of `{label a}`:\n{m}"
    | none => "Kernel stage: nothing to try."
  if b.outcome == "falsified" then
    if let some r := b.report? then
      -- the report's keys (without its `"ms"`), then the stage's, then one `"ms"`
      -- with the report's phases and this tactic's
      let rest := ((r.message timings).splitOn "\n").drop 1
      let line := appendKeys (r.resultLine (timings := false))
        (blasterKeys ++ msKey timings (r.timings.toList ++ [("kernel", kernelMs), ("total", totalMs)]))
      return s!"{"\n".intercalate (line :: rest)}\n{kernelPart}"
  let oracle := b.outcome == "valid"
  let N := b.fuel?.getD opts.fuel
  let reason := match b.outcome with
    | "valid" => s!"Blaster found no counterexample in runs of up to {N} steps; no kernel proof"
    | "spurious" => s!"Blaster's only counterexample runs longer than {N} steps (it halts with \
        the claimed value); no kernel proof"
    | "undetermined" => s!"Blaster could not decide the claim on runs of up to {N} steps; no \
        kernel proof"
    | "falsified" => s!"Blaster's counterexample at {N} steps is not confirmed; no kernel proof"
    | "error" => s!"Blaster failed: {b.reason?.getD ""}; no kernel proof"
    | _ => "Blaster was skipped; no kernel proof"
  let line := resultLine ([("status", Cex.jsonStr (if oracle then "oracle" else "unknown")),
    ("kernel", "false"), ("cex", "{}"), ("lean", "{}")] ++ blasterKeys ++
    [("reason", Cex.jsonStr reason)] ++
    msKey timings [("blaster", b.ms), ("kernel", kernelMs), ("total", totalMs)])
  let holds := if oracle then
      s!"The claim holds according to Blaster (z3) for every run of up to {N} CEK steps, but \
        that is not a proof."
    else s!"{reason.capitalize}."
  let advice := if loops then
      s!"{holds} The script loops (a recursive function): give what the loop returns as \
        `(loop := fun k => …)` (e.g. `fun k => .VCon (.Integer (spec k))` with `spec` a Lean \
        function of `k : Nat`; an `Int` input `n` is split as `n < 0` / `n = ↑k`), and the \
        facts about `spec` the proof needs as `uplc_auto [spec_lemma]`; with an accumulator, \
        `generalizing acc`."
    else s!"{holds} The script does not loop: the kernel stage runs it symbolically; give the \
        facts its branches need as `uplc_auto [lemma]`."
  return s!"{line}\n{advice}\n{kernelPart}"
where
  /-- The keys `"blaster"`, `"fuel"` and `"spurious"` (those that apply). -/
  keysOf (b : BlasterStage) : List (String × String) :=
    [("blaster", Cex.jsonStr b.outcome)] ++ (b.fuel?.map fun N => ("fuel", toString N)).toList ++
      (b.spurious?.map fun o => ("spurious", o)).toList

/-- `uplc_auto` (see the module doc). -/
def run (stx : Syntax) : TacticM Unit := withMainContext do
  -- Blaster reads `env.constants`, which waits for the earlier declarations of the
  -- file (elaborated and kernel-checked in parallel): wait here, off the clock
  -- (`toKernelEnv` blocks on the kernel's task; the test keeps the compiler from dropping it)
  if (← getEnv).toKernelEnv.constants.map₂.isEmpty then
    trace[uplc.auto] "no local declaration"
  let t0 ← IO.monoMsNow
  let timings := Cex.uplc.cex.timings.get (← getOptions)
  let opts ← asUsageError "bad option" (parseOpts stx)
  let g ← getMainGoal
  let others := (← getGoals).drop 1
  let (stmt, arity) ← statement g
  -- the user's lemmas, elaborated now: a typo is an error, not a failed attempt
  unless opts.simpArgs.isEmpty do
    let ts : Tactic.SimpArgs := ⟨mkSepArray opts.simpArgs (mkAtom ",")⟩
    asUsageError "a lemma does not elaborate" do
      discard <| Lean.Elab.Tactic.run (← mkFreshExprMVar (mkConst ``True)).mvarId!
        (withoutRecover (evalTactic (← `(tactic| simp only [$ts,*]))))
  let simpArgs := opts.simpArgs ++ defaultLemmas.map fun c =>
    mkNode ``Lean.Parser.Tactic.simpLemma #[mkNullNode, mkNullNode, mkIdent c]
  -- stage 1, off the declaration's heartbeat budget, as stage 2 (`runAttempt`): Blaster
  -- (`Cex.runBlaster`) restores the count itself; this also drops the heartbeats of the
  -- analysis of its counterexample and of the spurious check's run
  let h0 ← IO.getNumHeartbeats
  let b ← match ← withCurrHeartbeats (blasterStage stmt opts timings) with
    | .error msg => throwError msg
    | .ok b => pure b
  IO.setNumHeartbeats h0
  -- stage 2
  let t1 ← IO.monoMsNow
  let (_, g') ← g.introNP arity
  -- the conclusion as `Halts`/`Fails` (unfolding the definition it may be stated with)
  let g' ← g'.withContext do
    let ty ← instantiateMVars (← g'.getType)
    let some c ← claim? ty
      | usageError "internal error (goal)" m!"uplc_auto: internal error: after introducing \
          {arity} binder(s), the goal is not a claim about a run of a script:{indentExpr ty}"
    if c == ty then pure g' else g'.replaceTargetDefEq c
  let mut errors : Array (Attempt × String) := #[]
  for a in ← attempts g' opts simpArgs do
    match ← runAttempt g' a with
    | .ok () =>
        let t ← IO.monoMsNow
        let kvs := [("status", Cex.jsonStr "proved"), ("kernel", "true"),
          ("method", Cex.jsonStr a.method)] ++
          (a.leaf?.map fun x => ("leaf", Cex.jsonStr x.toString)).toList ++ failure.keysOf b ++
          msKey timings [("blaster", b.ms), ("kernel", t - t1), ("total", t - t0)]
        logInfo (resultLine kvs)
        setGoals others
        return
    | .error msg => errors := errors.push (a, msg)
  let t ← IO.monoMsNow
  let loops ← g'.withContext do
    let some (p, _, _) ← conclusion? (← instantiateMVars (← g'.getType)) | pure false
    hasLoop p
  throwError (failure b opts loops errors (t - t1) (t - t0) timings)

end Auto

@[tactic uplcAutoTac] def evalUplcAuto : Tactic := Auto.run

end UplcProof
