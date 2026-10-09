import UplcProofTests.Induction.Negative

/-!
# Tests: encoders, `uplc_run`, `evalRun`, the leaf-closer hook, the `Exec` lemmas

* The encoders of `UplcProof.Encode` against real runs (`#guard`), on three
  fixtures with `Bool`, `ByteArray`, `List<Bool>` and `List<ByteArray>` parameters
  (`check_signer`, `count_true`, `signed_by` in `Tests/Induction/aiken/lib/fixtures.ak`).
* `uplc_run`: proofs with no induction (branches on symbolic data, loops on known
  data), goals written with the encoders and with `Accepts`; and what it must refuse
  (a loop on symbolic data: stuck, or past `uplc.maxSplits` nested splits).
* `evalRun`: refuting a claim on a concrete input (a run that fails, a run that
  halts with another value), and what it must refuse.
* `Ctx.closer?` (through `Tactic.runOn`): a leaf the run cannot close is closed by
  the closer, which is undone when it fails.
* `Data` equality (`equalsData`, which does not reduce): closed, decided by
  evaluation in `uplc_run` and `evalRun`, true and false, on records, lists and
  maps (`require_ref`, `same_data`, `same_refs`); symbolic, split on as a condition
  (`require_ref`), or left in the result (`same_data`, with `equalsData_of_ne`).
* The lemmas of `UplcProof.Induction.Exec` and `EqData` that no tactic here uses,
  for tactic authors: `Halts.eventually`, `Reaches.inv`, `Terminal`,
  `exec_terminal`, `Reaches.error_halt`, `Reaches.halt_halt`, `Halts.data_eq`,
  `equalsData_of_ne`.

Every theorem is checked with `#print axioms` (`#guard_msgs`).
-/

open PlutusCore.UPLC.Term PlutusCore.UPLC.CekValue PlutusCore.UPLC.CekMachine
open PlutusCore.Data (Data)
open UplcProof

namespace UplcProofTests.Induction

abbrev ByteString := PlutusCore.ByteString.ByteString

#import_uplc UplcProofTests.Induction.checkSignerHex PlutusV3 single_cbor_hex
  "Tests/Induction/Scripts/check_signer.hex"
#import_uplc UplcProofTests.Induction.countTrueHex PlutusV3 single_cbor_hex
  "Tests/Induction/Scripts/count_true.hex"
#import_uplc UplcProofTests.Induction.signedByHex PlutusV3 single_cbor_hex
  "Tests/Induction/Scripts/signed_by.hex"
#import_uplc UplcProofTests.Induction.requireRefHex PlutusV3 single_cbor_hex
  "Tests/Induction/Scripts/require_ref.hex"
#import_uplc UplcProofTests.Induction.sameDataHex PlutusV3 single_cbor_hex
  "Tests/Induction/Scripts/same_data.hex"
#import_uplc UplcProofTests.Induction.sameRefsHex PlutusV3 single_cbor_hex
  "Tests/Induction/Scripts/same_refs.hex"

/-- The `Bool` a run halted with, if any. -/
def haltBool : State → Option Bool
  | .Halt (.VCon (.Bool b)) => some b
  | _ => none

/-! ## Encoders: real runs -/

-- `check_signer(is_open, signer, owner)`: `True` if open or `signer == owner`, else fails
#guard halted (run checkSignerHex.script [bool true, bytes ⟨"a"⟩, bytes ⟨"b"⟩])
#guard halted (run checkSignerHex.script [bool false, bytes ⟨"a"⟩, bytes ⟨"a"⟩])
#guard !halted (run checkSignerHex.script [bool false, bytes ⟨"a"⟩, bytes ⟨"b"⟩])
#guard haltBool (run checkSignerHex.script [bool true, bytes ⟨"a"⟩, bytes ⟨"b"⟩]) == some true
-- `True` is `Constr 1 []`, `False` is `Constr 0 []`: `data` of them is `bool`
#guard halted (run checkSignerHex.script [data (.Constr 1 []), bytes ⟨"a"⟩, bytes ⟨"b"⟩])
#guard !halted (run checkSignerHex.script [data (.Constr 0 []), bytes ⟨"a"⟩, bytes ⟨"b"⟩])
-- `count_true(bs)`
#guard haltInt (run countTrueHex.script [boolList [true, false, true, true]]) == some 3
#guard haltInt (run countTrueHex.script [boolList []]) == some 0
-- `signed_by(keys, key)`
#guard haltBool (run signedByHex.script [bytesList [⟨"a"⟩, ⟨"b"⟩], bytes ⟨"b"⟩]) == some true
#guard haltBool (run signedByHex.script [bytesList [⟨"a"⟩], bytes ⟨"b"⟩]) == some false
#guard haltBool (run signedByHex.script [bytesList [], bytes ⟨"b"⟩]) == some false
-- `data`: the `Data` itself
#guard haltInt (run sumHex.script [data (.List [.I 4, .I 23, .I 56])]) == some 83
#guard haltInt (run factorialHex.script [data (.I 5)]) == some 120

example : bool true = data (.Constr 1 []) := rfl
example : bool false = data (.Constr 0 []) := rfl
example : int 3 = data (.I 3) := rfl
example : list [1, 2] = data (.List [.I 1, .I 2]) := rfl
example : bytesList [⟨"a"⟩] = data (.List [.B ⟨"a"⟩]) := rfl
example : boolList [true, false] = data (.List [.Constr 1 [], .Constr 0 []]) := rfl
example : vTrue = .VCon (.Bool true) := rfl
example : vFalse = .VCon (.Bool false) := rfl
example : vUnit = .VCon .Unit := rfl

/-! ## `uplc_run`: no induction -/

/-- A branch on symbolic `ByteArray`s: the `¬ s = o` branch fails, and contradicts `h`. -/
theorem check_signer_halts (s o : ByteString) (h : s = o) :
    Halts checkSignerHex.script [bool false, bytes s, bytes o] vTrue := by
  uplc_run

theorem check_signer_open (s o : ByteString) :
    Halts checkSignerHex.script [bool true, bytes s, bytes o] vTrue := by
  uplc_run

theorem check_signer_fails (s o : ByteString) (h : s ≠ o) :
    Fails checkSignerHex.script [bool false, bytes s, bytes o] := by
  uplc_run

/-- A symbolic `Bool` argument is matched on, not branched on: `cases` first. -/
theorem check_signer_self (b : Bool) (s : ByteString) :
    Halts checkSignerHex.script [bool b, bytes s, bytes s] vTrue := by
  cases b <;> uplc_run

/-- A guard on symbolic data, then a loop on a known list (it just runs). -/
theorem sum_if_positive_run (t : Int) (h : 0 < t) :
    Halts sumIfPositiveHex.script [list [1, 2, 3], int t] (intV 6) := by
  uplc_run

/-- A loop on a known list, branching on a symbolic `x` at each element. -/
theorem require_member_run (x : Int) (h : x = 2) :
    Halts requireMemberHex.script [list [1, 2, 3], int x] vTrue := by
  uplc_run

theorem require_member_run_fails (x : Int) (h : 3 < x) :
    Fails requireMemberHex.script [list [1, 2, 3], int x] := by
  uplc_run

/-- The encoders with `uplc_induction`: a loop on a `List<ByteArray>`. -/
theorem signed_by_halts (ks : List ByteString) (k : ByteString) :
    Halts signedByHex.script [bytesList ks, bytes k] (.VCon (.Bool (ks.contains k))) := by
  uplc_induction ks

/-! ## `Accepts` and `Verdict` (a hand-written validator) -/

/-- `λ ctx. if 0 < unIData ctx then () else error`. -/
def positiveCtx : Program :=
  .Program (.Version 1 1 0) (.Lam "ctx"
    (.Force (.Apply (.Apply (.Apply (.Force (.Builtin .IfThenElse))
      (.Apply (.Apply (.Builtin .LessThanInteger) (.Const (.Integer 0)))
        (.Apply (.Builtin .UnIData) (.Var "ctx"))))
      (.Delay (.Const .Unit))) (.Delay .Error))))

theorem accepts_positive (x : Int) (h : 0 < x) : Accepts positiveCtx (.I x) := by
  uplc_run

theorem rejects_nonpositive (x : Int) (h : x ≤ 0) : ¬ Accepts positiveCtx (.I x) :=
  Fails.not_halts (by uplc_run)

/-- `uplc_induction` on an `Accepts` goal. -/
theorem accepts_succ (n : Nat) : Accepts positiveCtx (.I (n + 1)) := by
  uplc_induction n

theorem verdict_positive (x : Int) (h : 0 < x) : Verdict positiveCtx (.I x) true :=
  ⟨fun _ => accepts_positive x h, fun _ => rfl⟩

theorem verdict_nonpositive (x : Int) (h : x ≤ 0) : Verdict positiveCtx (.I x) false :=
  ⟨fun h' => (Bool.false_ne_true h').elim, fun ha => (rejects_nonpositive x h ha).elim⟩

example (x : Int) (h : 0 < x) : Accepts positiveCtx (.I x) := (verdict_positive x h).accepts
example (x : Int) (h : x ≤ 0) : ¬ Accepts positiveCtx (.I x) := (verdict_nonpositive x h).rejects

/-! ## `evalRun`: refuting a claim on a concrete input -/

open Lean Meta Elab Tactic in
/-- `refute_run` proves `¬ Halts p args v` (`p`, `args`, `v` closed) by running
    `p` on `args` with `evalRun`: it fails, or halts with a value `simp` shows
    differs from `v`. -/
elab "refute_run" : tactic => do
  let g ← getMainGoal
  g.withContext do
  let ty ← instantiateMVars (← g.getType)
  let_expr Not h := ty | throwError "refute_run: expected `¬ Halts p args v`"
  let_expr Halts p args v := (← whnfR h) | throwError "refute_run: expected `¬ Halts p args v`"
  let (T, pf) ← Tactic.evalRun p args
  if Sym.isError T then
    g.assign (mkAppN (mkConst ``not_halts_of_reaches_error) #[p, args, v, pf])
  else
    let w := T.appArg!
    -- `whnfD`: the claimed value may be written with definitions (`intV 100`)
    let ne ← mkFreshExprMVar (← mkAppM ``Ne #[← whnfD v, w])
    let r ← observing? do
      let [] ← Tactic.run ne.mvarId! (withoutRecover (evalTactic (← `(tactic| simp)))) | failure
    if r.isNone then throwError "refute_run: the run halts with{indentExpr w}\nthe claimed value"
    g.assign (mkAppN (mkConst ``not_halts_of_reaches_halt) #[p, args, v, w, pf, ← instantiateMVars ne])
  replaceMainGoal []

open Lean Meta Elab Tactic in
/-- `#eval_run p args`: the final state `evalRun` computes, and the type of its proof. -/
elab "#eval_run " p:term:max args:term:max : command => Command.liftTermElabM do
  let p ← Term.elabTermEnsuringType p (mkConst ``Program)
  let args ← Term.elabTermEnsuringType args (← mkAppM ``List #[mkConst ``PlutusCore.UPLC.Term.Term])
  Term.synthesizeSyntheticMVarsNoPostponing
  let p ← instantiateMVars p
  let args ← instantiateMVars args
  let g ← mkFreshExprMVar (mkConst ``True)
  discard <| Tactic.run g.mvarId! do
    let (T, pf) ← Tactic.evalRun p args
    let pfTy ← inferType pf
    unless ← isDefEq pfTy (← mkAppM ``Reaches #[← mkAppM ``initState #[p, args], T]) do
      throwError "#eval_run: the proof has type{indentExpr pfTy}"
    logInfo m!"{T}"
    (← getMainGoal).assign (mkConst ``True.intro)

-- closed `Int` and `Bool` leaves are computed (`addInteger` and `equalsByteString` here)
/-- info: State.Halt (CekValue.VCon (Const.Integer 6)) -/
#guard_msgs in #eval_run sumHex.script [list [1, 2, 3]]
/-- info: State.Halt (CekValue.VCon (Const.Bool false)) -/
#guard_msgs in #eval_run signedByHex.script [bytesList [⟨"a"⟩], bytes ⟨"b"⟩]
/-- info: State.Error -/
#guard_msgs in #eval_run requireMemberHex.script [list [1, 2, 3], int 5]

/-- The run halts with `120`. -/
theorem factorial_not_100 : ¬ Halts factorialHex.script [int 5] (intV 100) := by
  refute_run

/-- The run fails. -/
theorem require_member_not_5 : ¬ Halts requireMemberHex.script [list [1, 2, 3], int 5] vTrue := by
  refute_run

theorem signed_by_not : ¬ Halts signedByHex.script [bytesList [⟨"a"⟩], bytes ⟨"b"⟩] vTrue := by
  refute_run

theorem check_signer_not : ¬ Halts checkSignerHex.script [bool false, bytes ⟨"a"⟩, bytes ⟨"b"⟩] vTrue := by
  refute_run

/-! ## The leaf closer (`Ctx.closer?`, through `Tactic.runOn`) -/

open Lean Meta Elab Tactic in
/-- A leaf closer: refutes a hypothesis `Halts p args v` about another run by running
    it (`evalRun`). (The run's own closers, `uplc_eq` and `refute`, never see that
    hypothesis: they work without the hypotheses about runs.) -/
def closeByRefutingHyp (g : MVarId) : TacticM Bool := g.withContext do
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let_expr Halts p args v := (← instantiateMVars d.type) | continue
    let (T, pf) ← Tactic.evalRun p args
    let notH ← if Sym.isError T then
        pure (mkAppN (mkConst ``not_halts_of_reaches_error) #[p, args, v, pf])
      else
        let ne ← mkFreshExprMVar (← mkAppM ``Ne #[← whnfD v, T.appArg!])
        let r ← observing? do
          let [] ← Tactic.run ne.mvarId! (withoutRecover (evalTactic (← `(tactic| simp)))) | failure
        if r.isNone then continue
        pure (mkAppN (mkConst ``not_halts_of_reaches_halt) #[p, args, v, T.appArg!, pf,
          ← instantiateMVars ne])
    g.assign (← mkFalseElim (← g.getType) (mkApp notH d.toExpr))
    return true
  return false

open Lean Elab Tactic in
/-- `uplc_run` with the closer `closeByRefutingHyp`. -/
elab "uplc_run_closing" : tactic => do
  Tactic.runOn (← getMainGoal) (some closeByRefutingHyp) "closer"
  replaceMainGoal []

/-- The `¬ s = o` branch fails, and only the closer closes it (`hsum` is false). -/
theorem closer_used (s o : ByteString) (hsum : Halts sumHex.script [list []] (intV 1)) :
    Halts checkSignerHex.script [bool false, bytes s, bytes o] vTrue := by
  uplc_run_closing

/-! ## `Data` equality (`equalsData`)

`require_ref(r, expected)`: `if r == expected { True } else { fail }` on a record
(`ifThenElse (equalsData r expected)`); `same_data(a, b)`: `a == b` as the result;
`same_refs(xs, ys)`: `==` on lists of records. `equalsData` does not reduce (`eqData`
is well-founded): closed, it is decided by evaluating `dataEqB`; symbolic, it is a
condition the run splits on (`r = expected` or not). -/

/-- An output reference `Ref { id, idx }` as `Data`. -/
def ref (id : String) (idx : Int) : Data := .Constr 0 [.B ⟨id⟩, .I idx]

#guard halted (run requireRefHex.script [data (ref "a" 0), data (ref "a" 0)])
#guard !halted (run requireRefHex.script [data (ref "a" 0), data (ref "a" 1)])
#guard haltBool (run sameDataHex.script [data (ref "a" 0), data (ref "b" 0)]) == some false
#guard haltBool (run sameRefsHex.script [data (.List [ref "a" 0]), data (.List [ref "a" 0])]) ==
  some true

-- the kernel decides a closed `equalsData` through `dataEqB`
example : PlutusCore.Data.equalsData (ref "a" 0) (ref "a" 1) = false :=
  (equalsData_eq_dataEqB _ _).trans rfl
example : PlutusCore.Data.equalsData (.Map [(.I 1, ref "a" 0)]) (.Map [(.I 1, ref "a" 0)]) = true :=
  (equalsData_eq_dataEqB _ _).trans rfl

/-- Closed and equal: the condition is decided, no split. -/
theorem require_ref_same : Halts requireRefHex.script [data (ref "a" 0), data (ref "a" 0)] vTrue := by
  uplc_run

/-- Closed and different (in the index). -/
theorem require_ref_other : Fails requireRefHex.script [data (ref "a" 0), data (ref "a" 1)] := by
  uplc_run

/-- A closed `equalsData` left in the result is decided too. -/
theorem same_data_other : Halts sameDataHex.script [data (ref "a" 0), data (ref "b" 0)] vFalse := by
  uplc_run

/-- `Data` inside lists, and inside maps. -/
theorem same_refs_same :
    Halts sameRefsHex.script [data (.List [ref "a" 0, ref "b" 1]), data (.List [ref "a" 0, ref "b" 1])]
      vTrue := by
  uplc_run

theorem same_data_maps :
    Halts sameDataHex.script [data (.Map [(.I 1, ref "a" 0)]), data (.Map [(.I 1, ref "a" 2)])]
      vFalse := by
  uplc_run

/-- Symbolic fields: the run splits on `equalsData`, as `Constr 0 [B s, I i] = …`. -/
theorem require_ref_fields (s t : ByteString) (i j : Int) (hs : s = t) (hi : i = j) :
    Halts requireRefHex.script [data (.Constr 0 [.B s, .I i]), data (.Constr 0 [.B t, .I j])]
      vTrue := by
  uplc_run

/-- Symbolic `Data`: the branches are `d = e` and `¬ d = e`. -/
theorem require_ref_eq (d e : Data) (h : d = e) :
    Halts requireRefHex.script [data d, data e] vTrue := by
  uplc_run

theorem require_ref_ne (d e : Data) (h : d ≠ e) : Fails requireRefHex.script [data d, data e] := by
  uplc_run

-- `evalRun` goes through a closed `equalsData`, and decides one in the result
/-- info: State.Error -/
#guard_msgs in #eval_run requireRefHex.script [data (ref "a" 0), data (ref "a" 1)]
/-- info: State.Halt (CekValue.VCon (Const.Bool true)) -/
#guard_msgs in #eval_run requireRefHex.script [data (ref "a" 0), data (ref "a" 0)]
/-- info: State.Halt (CekValue.VCon (Const.Bool false)) -/
#guard_msgs in #eval_run sameDataHex.script [data (ref "a" 0), data (ref "b" 0)]

/-- Through an `equalsData` that is false: the run fails. -/
theorem require_ref_not_other :
    ¬ Halts requireRefHex.script [data (ref "a" 0), data (ref "a" 1)] vTrue := by
  refute_run

/-- Through an `equalsData` that is true: the run halts with `True`, not `False`. -/
theorem require_ref_not_false :
    ¬ Halts requireRefHex.script [data (ref "a" 0), data (ref "a" 0)] vFalse := by
  refute_run

/-- An `equalsData` in the result. -/
theorem same_data_not_true : ¬ Halts sameDataHex.script [data (ref "a" 0), data (ref "b" 0)] vTrue := by
  refute_run

/-! ## The lemmas for tactic authors (`Exec`, `EqData`) -/

/-- `Halts.eventually`: from some fuel on, the run halts with the value. -/
theorem factorial_eventually (n : Nat) :
    ∃ N, ∀ fuel, N ≤ fuel →
      cekExecuteProgram factorialHex.script [int n] fuel = .Halt (intV (fact n)) :=
  (factorial_halts n).eventually

/-- `Reaches.inv` (`Terminal`): a run that halts halts from every state it goes through. -/
theorem factorial_halts_from (n c : Nat) :
    Reaches (exec (initState factorialHex.script [int n]) c) (.Halt (intV (fact n))) :=
  (factorial_halts n).reaches.inv c rfl trivial

/-- `Reaches.inv`, `Reaches.error_halt`: a state that reaches `Error` reaches no `Halt`. -/
theorem reaches_error_not_halt {A : State} {v : CekValue} (he : Reaches A .Error)
    (hv : Reaches A (.Halt v)) : False := by
  obtain ⟨c, hc⟩ := he
  exact (hv.inv c hc trivial).error_halt

/-- `Reaches.inv`, `Reaches.halt_halt`: a state reaches at most one `Halt`. -/
theorem reaches_halt_unique {A : State} {v w : CekValue} (hv : Reaches A (.Halt v))
    (hw : Reaches A (.Halt w)) : v = w := by
  obtain ⟨c, hc⟩ := hv
  exact (hw.inv c hc trivial).halt_halt

/-- `exec_terminal`: a final state stays put. -/
theorem error_stays (n : Nat) : exec .Error n = .Error := exec_terminal (B := .Error) trivial n

/-- `λ x. x`. -/
def idProg : Program := .Program (.Version 1 1 0) (.Lam "x" (.Var "x"))

theorem id_halts (d : Data) : Halts idProg [data d] (.VCon (.Data d)) := by
  uplc_run

/-- `Halts.data_eq`: a run halts with at most one `Data`. -/
theorem id_halts_only (d e : Data) (h : Halts idProg [data d] (.VCon (.Data e))) : e = d :=
  h.data_eq (id_halts d)

/-- `equalsData_of_ne` as a lemma for `uplc_run`: `same_data` returns `equalsData d e`
    itself, which `uplc_run` alone cannot show is `false`. -/
theorem same_data_ne (d e : Data) (h : d ≠ e) :
    Halts sameDataHex.script [data d, data e] vFalse := by
  uplc_run [equalsData_of_ne h]

/-! ## What `uplc_run`, `evalRun` and the closer must refuse -/

-- accepts without `s = o`: the error names the branch that fails
example (s o : ByteString) :
    Halts checkSignerHex.script [bool false, bytes s, bytes o] vTrue ∨ True := by
  fails_with "run, on the branch [¬s = o]: the script fails (reaches `Error`)" (left; uplc_run)
  right; trivial

-- rejects although open
example (s o : ByteString) : Fails checkSignerHex.script [bool true, bytes s, bytes o] ∨ True := by
  fails_with "run: the script halts" (left; uplc_run)
  right; trivial

-- a wrong value
example (t : Int) (_h : 0 < t) :
    Halts sumIfPositiveHex.script [list [1, 2, 3], int t] (intV 7) ∨ True := by
  fails_with "cannot prove them equal" (left; uplc_run)
  right; trivial

-- a wrong branch: `x = 5` is not in the list
example (x : Int) (_h : x = 5) :
    Halts requireMemberHex.script [list [1, 2, 3], int x] vTrue ∨ True := by
  fails_with "the script fails" (left; uplc_run)
  right; trivial

-- a loop on a symbolic list is for `uplc_induction`
example (xs : List Int) : Halts sumHex.script [list xs] (intV xs.sum) ∨ True := by
  fails_with "symbolic execution is stuck" (left; uplc_run)
  right; trivial

-- a loop on a symbolic `Int` whose exit test is an `if` (`n == 0`): every iteration
-- splits; the run stops past `uplc.maxSplits` (16), within the default heartbeat
-- budget and with no limit (the two runs together need more than one budget)
set_option maxHeartbeats 0 in
example (n : Nat) : Halts factorialHex.script [int n] (intV (fact n)) ∨ True := by
  fails_unbounded "run: more than 16 nested splits" (left; uplc_run)
  right; trivial

-- without `equalsData_of_ne h`
example (d e : Data) (_h : d ≠ e) :
    Halts sameDataHex.script [data d, data e] vFalse ∨ True := by
  fails_with "cannot prove them equal" (left; uplc_run)
  right; trivial

-- a symbolic `Bool` without `cases`
example (b : Bool) (s : ByteString) :
    Halts checkSignerHex.script [bool b, bytes s, bytes s] vTrue ∨ True := by
  fails_with "symbolic execution is stuck" (left; uplc_run)
  right; trivial

-- not a claim about a run
example : (1 : Nat) = 1 ∨ True := by
  fails_with "run: expected a goal `Halts p args v` or `Fails p args`" (left; uplc_run)
  right; trivial

-- a typo in the lemma list
/-- error: Unknown constant `Int.add_comm'` -/
#guard_msgs in
example (t : Int) (h : 0 < t) : Halts sumIfPositiveHex.script [list [1, 2, 3], int t] (intV 6) := by
  uplc_run [Int.add_comm']

-- `evalRun` refutes nothing true: the run halts with the claimed value
example : ¬ Halts factorialHex.script [int 5] (intV 120) ∨ True := by
  fails_with "refute_run: the run halts with" (left; refute_run)
  right; trivial

-- `evalRun` needs closed arguments
example (x : Int) : ¬ Halts factorialHex.script [int x] (intV 1) ∨ True := by
  fails_with "evalRun: the run is stuck" (left; refute_run)
  right; trivial

-- without the closer, the leaf is refused
example (s o : ByteString) (_hsum : Halts sumHex.script [list []] (intV 1)) :
    Halts checkSignerHex.script [bool false, bytes s, bytes o] vTrue ∨ True := by
  fails_with "on the branch [¬s = o]: the script fails" (left; uplc_run)
  right; trivial

-- a closer that fails is undone: `hsum` is true, the leaf is refused as without it
example (s o : ByteString) (_hsum : Halts sumHex.script [list []] (intV 0)) :
    Halts checkSignerHex.script [bool false, bytes s, bytes o] vTrue ∨ True := by
  fails_with "closer, on the branch [¬s = o]: the script fails" (left; uplc_run_closing)
  right; trivial

-- limitation: a loop on `List<Bool>` matches on each symbolic `Bool` (not an `if`)
example (bs : List Bool) :
    Halts countTrueHex.script [boolList bs] (intV (bs.count true)) ∨ True := by
  fails_with "symbolic execution is stuck" (left; uplc_induction bs)
  right; trivial

-- `Data` equality: a closed `equalsData` that is false, claimed to accept
example : Halts requireRefHex.script [data (ref "a" 0), data (ref "a" 1)] vTrue ∨ True := by
  fails_with "run: the script fails (reaches `Error`)" (left; uplc_run)
  right; trivial

-- ... that is true, claimed to reject
example : Fails requireRefHex.script [data (ref "a" 0), data (ref "a" 0)] ∨ True := by
  fails_with "run: the script halts" (left; uplc_run)
  right; trivial

-- ... a wrong result
example : Halts sameDataHex.script [data (ref "a" 0), data (ref "a" 0)] vFalse ∨ True := by
  fails_with "cannot prove them equal" (left; uplc_run)
  right; trivial

-- symbolic, without `d = e`: the branch `¬d = e` fails
example (d e : Data) : Halts requireRefHex.script [data d, data e] vTrue ∨ True := by
  fails_with "run, on the branch [¬d = e]: the script fails" (left; uplc_run)
  right; trivial

-- `evalRun` refutes nothing true through a closed `equalsData`
example : ¬ Halts requireRefHex.script [data (ref "a" 0), data (ref "a" 0)] vTrue ∨ True := by
  fails_with "refute_run: the run halts with" (left; refute_run)
  right; trivial

example : ¬ Halts sameDataHex.script [data (ref "a" 0), data (ref "b" 0)] vFalse ∨ True := by
  fails_with "refute_run: the run halts with" (left; refute_run)
  right; trivial

/-! ## Axioms: only `propext` and `Quot.sound` -/

/-- info: 'UplcProofTests.Induction.check_signer_halts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms check_signer_halts
/-- info: 'UplcProofTests.Induction.check_signer_open' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms check_signer_open
/-- info: 'UplcProofTests.Induction.check_signer_fails' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms check_signer_fails
/-- info: 'UplcProofTests.Induction.check_signer_self' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms check_signer_self
/-- info: 'UplcProofTests.Induction.sum_if_positive_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sum_if_positive_run
/-- info: 'UplcProofTests.Induction.require_member_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms require_member_run
/--
info: 'UplcProofTests.Induction.require_member_run_fails' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in #print axioms require_member_run_fails
/-- info: 'UplcProofTests.Induction.signed_by_halts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms signed_by_halts
/-- info: 'UplcProofTests.Induction.accepts_positive' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms accepts_positive
/-- info: 'UplcProofTests.Induction.rejects_nonpositive' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms rejects_nonpositive
/-- info: 'UplcProofTests.Induction.accepts_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms accepts_succ
/-- info: 'UplcProofTests.Induction.verdict_positive' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms verdict_positive
/-- info: 'UplcProofTests.Induction.verdict_nonpositive' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms verdict_nonpositive
/-- info: 'UplcProofTests.Induction.factorial_not_100' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms factorial_not_100
/-- info: 'UplcProofTests.Induction.require_member_not_5' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms require_member_not_5
/-- info: 'UplcProofTests.Induction.signed_by_not' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms signed_by_not
/-- info: 'UplcProofTests.Induction.check_signer_not' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms check_signer_not
/-- info: 'UplcProofTests.Induction.closer_used' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms closer_used
/-- info: 'UplcProofTests.Induction.require_ref_same' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms require_ref_same
/-- info: 'UplcProofTests.Induction.require_ref_other' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms require_ref_other
/-- info: 'UplcProofTests.Induction.same_data_other' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms same_data_other
/-- info: 'UplcProofTests.Induction.same_refs_same' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms same_refs_same
/-- info: 'UplcProofTests.Induction.same_data_maps' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms same_data_maps
/-- info: 'UplcProofTests.Induction.require_ref_fields' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms require_ref_fields
/-- info: 'UplcProofTests.Induction.require_ref_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms require_ref_eq
/-- info: 'UplcProofTests.Induction.require_ref_ne' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms require_ref_ne
/--
info: 'UplcProofTests.Induction.require_ref_not_other' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in #print axioms require_ref_not_other
/--
info: 'UplcProofTests.Induction.require_ref_not_false' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in #print axioms require_ref_not_false
/-- info: 'UplcProofTests.Induction.same_data_not_true' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms same_data_not_true
/-- info: 'UplcProofTests.Induction.factorial_eventually' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms factorial_eventually
/-- info: 'UplcProofTests.Induction.factorial_halts_from' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms factorial_halts_from
/--
info: 'UplcProofTests.Induction.reaches_error_not_halt' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in #print axioms reaches_error_not_halt
/-- info: 'UplcProofTests.Induction.reaches_halt_unique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms reaches_halt_unique
/-- info: 'UplcProofTests.Induction.error_stays' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms error_stays
/-- info: 'UplcProofTests.Induction.id_halts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms id_halts
/-- info: 'UplcProofTests.Induction.id_halts_only' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms id_halts_only
/-- info: 'UplcProofTests.Induction.same_data_ne' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms same_data_ne

end UplcProofTests.Induction
