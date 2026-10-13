import UplcProof.Induction

/-!
# Tests: what the kernel must reject

The engine assembles its proofs directly, without the elaborator's checks: the step
lemmas of `UplcProof.Induction.Steps` applied to the pieces of a state, the
inequality of two variable names (`Sym.nameNe?`), the saturated builtins
(`Sym.stepProof?`), each under an expected-type hint (as `Sym.proveSteps` puts it),
and runs stated as auxiliary theorems (`mkAuxTheorem`, as `Sym.sharedRun` and
`Tactic.withAuxLemma` make them). Only the kernel decides whether they are right.

Each `wrong*` theorem below is built the same way on a false fact, and must be
rejected by the kernel: `#guard_msgs` holds the `(kernel)` error, and the build
fails if it is missing. Each `good*` control is built the same way on a true fact,
and must be accepted, with clean axioms. (From the refusal suites of Kreisel's
Aiken workshop, 2026-10-09.)
-/

open Lean Meta Elab Tactic
open PlutusCore.UPLC.Term PlutusCore.UPLC.CekValue PlutusCore.UPLC.CekMachine
open PlutusCore.UPLC.Builtins
open UplcProof

namespace UplcProofTests.Kernel

/-- `decide (a = b) = false` for two `Nat` terms, as `Sym.nameNe?` builds it. -/
def natEqFalse (a b : Expr) : MetaM Expr := do
  return mkApp3 (mkConst ``of_decide_eq_false) (← mkEq a b)
    (mkApp2 (mkConst ``instDecidableEqNat) a b)
    (mkApp2 (mkConst ``Eq.refl [levelOne]) (mkConst ``Bool) (mkConst ``Bool.false))

/-- `n < 55296` by `decide`, as `Sym.nameNe?` builds it. -/
def ltTrue (n : Nat) : MetaM Expr := do
  let p ← mkAppM ``LT.lt #[mkRawNatLit n, mkRawNatLit 55296]
  return mkApp3 (mkConst ``of_decide_eq_true) p
    (mkApp2 (mkConst ``Nat.decLt) (mkRawNatLit n) (mkRawNatLit 55296))
    (mkApp2 (mkConst ``Eq.refl [levelOne]) (mkConst ``Bool) (mkConst ``Bool.true))

/-- Closes the goal with the term `mk` builds, under an expected-type hint, unchecked:
    only the kernel decides. -/
def closeUnchecked (mk : MetaM Expr) : TacticM Unit := do
  let g ← getMainGoal
  g.assign (← mkExpectedTypeHint (← mk) (← g.getType))
  replaceMainGoal []

/-- `"dbi_1" ≠ "dbi_2"` (or a false variant) by the fourth character, as
    `Sym.nameNe?` builds it: `String.ne_of_drop` with `Char.ofNat_ne`. -/
def neByDrop (x y : String) : MetaM Expr := do
  let ch (n : Nat) := mkApp (mkConst ``Char.ofNat) (mkRawNatLit n)
  let charT := mkConst ``Char
  let rflSome (c : Expr) := mkApp2 (mkConst ``Eq.refl [levelOne])
    (mkApp (mkConst ``Option [levelZero]) charT) (mkApp2 (mkConst ``Option.some [levelZero]) charT c)
  let hc := mkAppN (mkConst ``Steps.Char.ofNat_ne)
    #[mkRawNatLit 49, mkRawNatLit 50, ← ltTrue 49, ← ltTrue 50,
      ← natEqFalse (mkRawNatLit 49) (mkRawNatLit 50)]
  return mkAppN (mkConst ``Steps.String.ne_of_drop)
    #[mkStrLit x, mkStrLit y, mkRawNatLit 4, ch 49, ch 50, rflSome (ch 49), rflSome (ch 50), hc]

/-! ## The structural step lemmas and the inequality of names -/

/-- `Steps.evalConst` with a wrong next state (`Const 1` evaluates to `VCon 1`, not `VCon 2`). -/
elab "bad_step" : tactic => closeUnchecked do
  let s := mkApp (mkConst ``List.nil [levelZero]) (mkConst ``PlutusCore.UPLC.CekMachine.Frame)
  let ρ := mkConst ``PlutusCore.UPLC.CekValue.Environment.EmptyEnvironment
  let c2 := mkApp (mkConst ``PlutusCore.UPLC.Term.Const.Integer) (toExpr (2 : Int))
  let c1 := mkApp (mkConst ``PlutusCore.UPLC.Term.Const.Integer) (toExpr (1 : Int))
  let b := mkApp2 (mkConst ``PlutusCore.UPLC.CekMachine.State.Return) s
    (mkApp (mkConst ``PlutusCore.UPLC.CekValue.CekValue.VCon) c2)
  return mkAppN (mkConst ``Steps.evalConst) #[s, ρ, c1, mkRawNatLit 0, b, mkApp (mkConst ``exec_zero) b]

/-- Two equal names "shown" different by a character that is not there (`ne_of_drop`). -/
elab "bad_ne_drop" : tactic => closeUnchecked (neByDrop "dbi_1" "dbi_1")

/-- Two names of the same length "shown" different by their lengths (`ne_of_length`). -/
elab "bad_ne_length" : tactic => closeUnchecked do
  let len (e : Expr) := mkApp2 (mkConst ``List.length [levelZero]) (mkConst ``Char)
    (mkApp (mkConst ``String.data) e)
  let x := mkStrLit "dbi_1"
  let y := mkStrLit "dbi_2"
  return mkApp3 (mkConst ``Steps.String.ne_of_length) x y (← natEqFalse (len x) (len y))

elab "good_ne_drop" : tactic => closeUnchecked (neByDrop "dbi_1" "dbi_2")

/--
error: (kernel) application type mismatch
  Steps.evalConst [] Environment.EmptyEnvironment (Const.Integer 1) 0
    (State.Return [] (CekValue.VCon (Const.Integer 2))) (exec_zero (State.Return [] (CekValue.VCon (Const.Integer 2))))
argument has type
  exec (State.Return [] (CekValue.VCon (Const.Integer 2))) 0 = State.Return [] (CekValue.VCon (Const.Integer 2))
but function has type
  exec (State.Return [] (CekValue.VCon (Const.Integer 1))) 0 = State.Return [] (CekValue.VCon (Const.Integer 2)) →
    exec (State.Eval [] Environment.EmptyEnvironment (Term.Const (Const.Integer 1))) (Nat.succ 0) =
      State.Return [] (CekValue.VCon (Const.Integer 2))
-/
#guard_msgs in
example :
    exec (.Eval [] .EmptyEnvironment (.Const (.Integer 1))) 1 = .Return [] (.VCon (.Integer 2)) := by
  bad_step

/--
error: (kernel) application type mismatch
  Steps.String.ne_of_drop 4 (Eq.refl (some '1')) (Eq.refl (some '2'))
argument has type
  some '2' = some '2'
but function has type
  (List.drop 4 "dbi_1".data).head? = some '2' → '1' ≠ '2' → "dbi_1" ≠ "dbi_1"
-/
#guard_msgs in
example : ("dbi_1" : String) ≠ "dbi_1" := by bad_ne_drop

/--
error: (kernel) application type mismatch
  of_decide_eq_false (Eq.refl false)
argument has type
  false = false
but function has type
  decide ("dbi_1".data.length = "dbi_2".data.length) = false → ¬"dbi_1".data.length = "dbi_2".data.length
-/
#guard_msgs in
example : ("dbi_1" : String) ≠ "dbi_2" := by bad_ne_length

theorem goodNe : ("dbi_1" : String) ≠ "dbi_2" := by good_ne_drop

/-! ## An auxiliary theorem (as `Sym.sharedRun` and `Tactic.withAuxLemma` make them) -/

/-- `1 + 1 = 3` "proved" by `rfl : 3 = 3` under a type hint, as an auxiliary theorem
    (`mkAuxTheorem`, no `Meta.check`): only the kernel can tell, and it checks the
    auxiliary theorem on its own. The error must reach the output, and the theorem
    that uses it must not be added. -/
elab "bogus_aux" : tactic => do
  let g ← getMainGoal
  let ty ← g.getType
  let pf ← mkExpectedTypeHint (← mkEqRefl (mkNatLit 3)) ty
  let aux ← mkAuxTheorem ty pf (zetaDelta := true)
  g.assign aux
  replaceMainGoal []

/--
error: (kernel) application type mismatch
  id (Eq.refl 3)
argument has type
  3 = 3
but function has type
  1 + 1 = 3 → 1 + 1 = 3
-/
#guard_msgs in
example : 1 + 1 = 3 := by bogus_aux

/-! ## The saturated builtins (`Steps.sat*`, `Steps.evalBuiltinTerm`) -/

/-- Closes the goal `exec a 1 = b` with the lemma `n` applied to the elaborated `pieces`,
    `k := 0` and `exec_zero b` for the rest, under a type hint: unchecked, only the kernel
    decides. -/
def closeWith (n : Name) (pieces : Array Lean.Term) : TacticM Unit := do
  let g ← getMainGoal
  let ty ← g.getType
  let some (_, _, b) := ty.eq? | throwError "not an equation"
  let xs ← pieces.mapM fun p => Term.elabTerm p none
  Term.synthesizeSyntheticMVarsNoPostponing
  let xs ← xs.mapM instantiateMVars
  let pf := mkAppN (mkConst n) (xs ++ #[mkNatLit 0, b, mkApp (mkConst ``UplcProof.exec_zero) b])
  g.assign (← mkExpectedTypeHint pf ty)
  replaceMainGoal []

syntax "lemma_unchecked " ident " [" term,* "]" : tactic
elab_rules : tactic
  | `(tactic| lemma_unchecked $n:ident [$ps,*]) => closeWith n.getId ps.getElems

abbrev D := PlutusCore.Data.PlutusCore.DataInternal.Data

/--
error: (kernel) application type mismatch
  id
    (Steps.satHeadListDataR [] (PlutusCore.Data.PlutusCore.DataInternal.Data.I 2)
      [PlutusCore.Data.PlutusCore.DataInternal.Data.I 2] 0
      (State.Return [] (CekValue.VCon (Const.Data (PlutusCore.Data.PlutusCore.DataInternal.Data.I 2))))
      (exec_zero (State.Return [] (CekValue.VCon (Const.Data (PlutusCore.Data.PlutusCore.DataInternal.Data.I 2))))))
argument has type
  exec
      (State.Return
        [Frame.RightApplicationOfValue
            (CekValue.VBuiltin BuiltinFun.HeadList [] (ExpectedBuiltinArgs.One ExpectedBuiltinArg.ArgV))]
        (CekValue.VCon
          (Const.ConstDataList
            [PlutusCore.Data.PlutusCore.DataInternal.Data.I 2, PlutusCore.Data.PlutusCore.DataInternal.Data.I 2])))
      (Nat.succ 0) =
    State.Return [] (CekValue.VCon (Const.Data (PlutusCore.Data.PlutusCore.DataInternal.Data.I 2)))
but function has type
  exec
        (State.Return
          [Frame.RightApplicationOfValue
              (CekValue.VBuiltin BuiltinFun.HeadList [] (ExpectedBuiltinArgs.One ExpectedBuiltinArg.ArgV))]
          (CekValue.VCon
            (Const.ConstDataList
              [PlutusCore.Data.PlutusCore.DataInternal.Data.I 1, PlutusCore.Data.PlutusCore.DataInternal.Data.I 2])))
        1 =
      State.Return [] (CekValue.VCon (Const.Data (PlutusCore.Data.PlutusCore.DataInternal.Data.I 2))) →
    exec
        (State.Return
          [Frame.RightApplicationOfValue
              (CekValue.VBuiltin BuiltinFun.HeadList [] (ExpectedBuiltinArgs.One ExpectedBuiltinArg.ArgV))]
          (CekValue.VCon
            (Const.ConstDataList
              [PlutusCore.Data.PlutusCore.DataInternal.Data.I 1, PlutusCore.Data.PlutusCore.DataInternal.Data.I 2])))
        1 =
      State.Return [] (CekValue.VCon (Const.Data (PlutusCore.Data.PlutusCore.DataInternal.Data.I 2)))
-/
#guard_msgs in
/-- `headList [I 1, I 2]` is `I 1`; the wrong instance claims `I 2`. -/
example :
    exec (.Return [.RightApplicationOfValue (.VBuiltin .HeadList [] (.One .ArgV))]
      (.VCon (.ConstDataList [(.I 1 : D), (.I 2 : D)]))) 1 = .Return [] (.VCon (.Data ((.I 2 : D)))) := by
  lemma_unchecked UplcProof.Steps.satHeadListDataR [([] : Stack), (.I 2 : D), ([(.I 2 : D)] : List D)]

/--
error: (kernel) application type mismatch
  id
    (Steps.satIfThenElseTrueR [] (CekValue.VCon (Const.Integer 1)) (CekValue.VCon (Const.Integer 2)) 0
      (State.Return [] (CekValue.VCon (Const.Integer 1)))
      (exec_zero (State.Return [] (CekValue.VCon (Const.Integer 1)))))
argument has type
  exec
      (State.Return
        [Frame.RightApplicationOfValue
            (CekValue.VBuiltin BuiltinFun.IfThenElse [CekValue.VCon (Const.Integer 1), CekValue.VCon (Const.Bool true)]
              (ExpectedBuiltinArgs.One ExpectedBuiltinArg.ArgV))]
        (CekValue.VCon (Const.Integer 2)))
      (Nat.succ 0) =
    State.Return [] (CekValue.VCon (Const.Integer 1))
but function has type
  exec
        (State.Return
          [Frame.RightApplicationOfValue
              (CekValue.VBuiltin BuiltinFun.IfThenElse
                [CekValue.VCon (Const.Integer 1), CekValue.VCon (Const.Bool false)]
                (ExpectedBuiltinArgs.One ExpectedBuiltinArg.ArgV))]
          (CekValue.VCon (Const.Integer 2)))
        1 =
      State.Return [] (CekValue.VCon (Const.Integer 1)) →
    exec
        (State.Return
          [Frame.RightApplicationOfValue
              (CekValue.VBuiltin BuiltinFun.IfThenElse
                [CekValue.VCon (Const.Integer 1), CekValue.VCon (Const.Bool false)]
                (ExpectedBuiltinArgs.One ExpectedBuiltinArg.ArgV))]
          (CekValue.VCon (Const.Integer 2)))
        1 =
      State.Return [] (CekValue.VCon (Const.Integer 1))
-/
#guard_msgs in
/-- `ifThenElse false t e` is `e`; the wrong instance uses the `true` lemma. -/
example :
    exec (.Return [.RightApplicationOfValue (.VBuiltin .IfThenElse
        [.VCon (.Integer 1), .VCon (.Bool false)] (.One .ArgV))] (.VCon (.Integer 2))) 1 =
      .Return [] (.VCon (.Integer 1)) := by
  lemma_unchecked UplcProof.Steps.satIfThenElseTrueR
    [([] : Stack), (.VCon (.Integer 1) : CekValue), (.VCon (.Integer 2) : CekValue)]

/--
error: (kernel) application type mismatch
  id
    (Steps.satUnConstrDataR [] 1 [] 0
      (State.Return [] (CekValue.VCon (Const.Pair (Const.Integer 1, Const.ConstDataList []))))
      (exec_zero (State.Return [] (CekValue.VCon (Const.Pair (Const.Integer 1, Const.ConstDataList []))))))
argument has type
  exec
      (State.Return
        [Frame.RightApplicationOfValue
            (CekValue.VBuiltin BuiltinFun.UnConstrData [] (ExpectedBuiltinArgs.One ExpectedBuiltinArg.ArgV))]
        (CekValue.VCon (Const.Data (PlutusCore.Data.PlutusCore.DataInternal.Data.Constr 1 []))))
      (Nat.succ 0) =
    State.Return [] (CekValue.VCon (Const.Pair (Const.Integer 1, Const.ConstDataList [])))
but function has type
  exec
        (State.Return
          [Frame.RightApplicationOfValue
              (CekValue.VBuiltin BuiltinFun.UnConstrData [] (ExpectedBuiltinArgs.One ExpectedBuiltinArg.ArgV))]
          (CekValue.VCon (Const.Data (PlutusCore.Data.PlutusCore.DataInternal.Data.Constr 0 []))))
        1 =
      State.Return [] (CekValue.VCon (Const.Pair (Const.Integer 1, Const.ConstDataList []))) →
    exec
        (State.Return
          [Frame.RightApplicationOfValue
              (CekValue.VBuiltin BuiltinFun.UnConstrData [] (ExpectedBuiltinArgs.One ExpectedBuiltinArg.ArgV))]
          (CekValue.VCon (Const.Data (PlutusCore.Data.PlutusCore.DataInternal.Data.Constr 0 []))))
        1 =
      State.Return [] (CekValue.VCon (Const.Pair (Const.Integer 1, Const.ConstDataList [])))
-/
#guard_msgs in
/-- `unConstrData (Constr 0 [])` is `(0, [])`; the wrong instance claims `(1, [])`. -/
example :
    exec (.Return [.RightApplicationOfValue (.VBuiltin .UnConstrData [] (.One .ArgV))]
      (.VCon (.Data ((.Constr 0 [] : D))))) 1 =
      .Return [] (.VCon (.Pair (.Integer 1, .ConstDataList []))) := by
  lemma_unchecked UplcProof.Steps.satUnConstrDataR [([] : Stack), (1 : Int), ([] : List D)]

/--
error: (kernel) application type mismatch
  Steps.evalBuiltinTerm [] Environment.EmptyEnvironment BuiltinFun.HeadList 0
    (State.Return [] (CekValue.VBuiltin BuiltinFun.HeadList [] (ExpectedBuiltinArgs.One ExpectedBuiltinArg.ArgV)))
    (exec_zero
      (State.Return [] (CekValue.VBuiltin BuiltinFun.HeadList [] (ExpectedBuiltinArgs.One ExpectedBuiltinArg.ArgV))))
argument has type
  exec (State.Return [] (CekValue.VBuiltin BuiltinFun.HeadList [] (ExpectedBuiltinArgs.One ExpectedBuiltinArg.ArgV)))
      0 =
    State.Return [] (CekValue.VBuiltin BuiltinFun.HeadList [] (ExpectedBuiltinArgs.One ExpectedBuiltinArg.ArgV))
but function has type
  exec (State.Return [] (CekValue.VBuiltin BuiltinFun.HeadList [] (expectedArgs BuiltinFun.HeadList))) 0 =
      State.Return [] (CekValue.VBuiltin BuiltinFun.HeadList [] (ExpectedBuiltinArgs.One ExpectedBuiltinArg.ArgV)) →
    exec (State.Eval [] Environment.EmptyEnvironment (Term.Builtin BuiltinFun.HeadList)) (Nat.succ 0) =
      State.Return [] (CekValue.VBuiltin BuiltinFun.HeadList [] (ExpectedBuiltinArgs.One ExpectedBuiltinArg.ArgV))
-/
#guard_msgs in
/-- `Term.Builtin HeadList` expects a force first (`ArgQ`, then `One ArgV`); the wrong
    instance claims `One ArgV`. -/
example :
    exec (.Eval [] .EmptyEnvironment (.Builtin .HeadList)) 1 =
      .Return [] (.VBuiltin .HeadList [] (.One .ArgV)) := by
  lemma_unchecked UplcProof.Steps.evalBuiltinTerm
    [([] : Stack), (.EmptyEnvironment : PlutusCore.UPLC.CekValue.Environment), (.HeadList : BuiltinFun)]

theorem goodHead :
    exec (.Return [.RightApplicationOfValue (.VBuiltin .HeadList [] (.One .ArgV))]
      (.VCon (.ConstDataList [(.I 1 : D), (.I 2 : D)]))) 1 = .Return [] (.VCon (.Data ((.I 1 : D)))) := by
  lemma_unchecked UplcProof.Steps.satHeadListDataR [([] : Stack), (.I 1 : D), ([(.I 2 : D)] : List D)]

theorem goodBuiltinArgs :
    exec (.Eval [] .EmptyEnvironment (.Builtin .HeadList)) 1 =
      .Return [] (.VBuiltin .HeadList [] (.More .ArgQ (.One .ArgV))) := by
  lemma_unchecked UplcProof.Steps.evalBuiltinTerm
    [([] : Stack), (.EmptyEnvironment : PlutusCore.UPLC.CekValue.Environment), (.HeadList : BuiltinFun)]

/-! ## The controls are clean

(The wrong cases are `example`s on purpose: a `theorem` the kernel rejects is still
added, as an axiom, and a `#guard_msgs` that holds its error would let it reach the
`.olean`.) -/

/-- info: 'UplcProofTests.Kernel.goodNe' does not depend on any axioms -/
#guard_msgs in #print axioms goodNe
/-- info: 'UplcProofTests.Kernel.goodHead' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms goodHead
/-- info: 'UplcProofTests.Kernel.goodBuiltinArgs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms goodBuiltinArgs

end UplcProofTests.Kernel
