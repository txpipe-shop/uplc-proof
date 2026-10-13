import UplcProof.Induction.Exec

/-!
# One CEK step at a time, by lemmas

The proofs of a symbolic run are chains of `exec a c = b`. Checked by evaluation (`rfl`), the
kernel unfolds `step` (and its match over every rule) at each step, and a variable lookup
compares the name with every binding it walks past, character by character
(`String.decEq`). Here each structural rule of `step` is a lemma, proved once by `rfl`: an
instance costs the kernel the comparison of its two sides with the states, not a run of
`step`. A lookup is one lemma per binding walked past (`ifBound_ne`), with the inequality of
two names shown by their lengths or by one character (`String.ne_of_length`,
`String.ne_of_drop`). Nothing here is trusted beyond `step` itself: every lemma is checked by
the kernel when this file is built.
-/

open PlutusCore.UPLC.Term PlutusCore.UPLC.CekValue PlutusCore.UPLC.CekMachine
open PlutusCore.UPLC.Builtins

namespace UplcProof.Steps

/-- Two runs, one after the other. -/
theorem exec_app {a a' b : State} {m k : Nat} (h₁ : exec a m = a') (h₂ : exec a' k = b) :
    exec a (m + k) = b := by rw [exec_add, h₁, h₂]

/-! ## The lookup of a variable -/

theorem ifBound_ne {s : Stack} {p : Environment} {x x' : String} {V : CekValue} (h : x ≠ x') :
    ifBoundOtherwiseError s (.NonEmptyEvironment p x' V) x = ifBoundOtherwiseError s p x := by
  simp [ifBoundOtherwiseError, h]

theorem ifBound_eq {s : Stack} {p : Environment} {x : String} {V : CekValue} :
    ifBoundOtherwiseError s (.NonEmptyEvironment p x V) x = .Return s V := by
  simp [ifBoundOtherwiseError]

/-- `ifBound_ne`, then the rest of the lookup (one term per binding walked past). -/
theorem ifBound_skip {s : Stack} {p : Environment} {x x' : String} {V : CekValue} {r : State}
    (h : x ≠ x') (rest : ifBoundOtherwiseError s p x = r) :
    ifBoundOtherwiseError s (.NonEmptyEvironment p x' V) x = r :=
  (ifBound_ne h).trans rest

theorem evalVar {s : Stack} {ρ : Environment} {x : String} {V : CekValue} {k : Nat} {b : State}
    (h : ifBoundOtherwiseError s ρ x = .Return s V) (rest : exec (.Return s V) k = b) :
    exec (.Eval s ρ (.Var x)) (Nat.succ k) = b := by
  show exec (ifBoundOtherwiseError s ρ x) k = b
  rw [h]; exact rest

/-! ## Two names that differ -/

theorem String.ne_of_length {s t : String} (h : s.data.length ≠ t.data.length) : s ≠ t := by
  rintro rfl; exact h rfl

theorem String.ne_of_drop {s t : String} (k : Nat) {c d : Char}
    (hs : (s.data.drop k).head? = some c) (ht : (t.data.drop k).head? = some d) (h : c ≠ d) :
    s ≠ t := by
  rintro rfl; rw [hs] at ht; exact h (Option.some.inj ht)

theorem Char.ofNat_ne {n m : Nat} (hn : n < 55296) (hm : m < 55296) (h : n ≠ m) :
    Char.ofNat n ≠ Char.ofNat m := by
  intro e
  have h₁ : Char.ofNat n = Char.ofNatAux n (Or.inl hn) := by rw [Char.ofNat, dif_pos (Or.inl hn)]
  have h₂ : Char.ofNat m = Char.ofNatAux m (Or.inl hm) := by rw [Char.ofNat, dif_pos (Or.inl hm)]
  rw [h₁, h₂] at e
  exact h (congrArg (fun c => c.val.toNat) e)

/-! ## The structural rules of `step`

Each rule followed by the rest of the run, `exec next k = b → exec current (k + 1) = b`, true
by definition (`exec` takes one step: the rule's). The arguments are the pieces of the
current state, and the next state is never written out (the kernel builds it from the
rule), so a chain of these costs the kernel only the pieces each step adds. -/

theorem evalConst (s : Stack) (ρ : Environment) (c : PlutusCore.UPLC.Term.Const) (k : Nat) (b : State)
    (h : exec (.Return s (.VCon c)) k = b) : exec (.Eval s ρ (.Const c)) (Nat.succ k) = b := h
theorem evalLam (s : Stack) (ρ : Environment) (x : String) (M : Term) (k : Nat) (b : State)
    (h : exec (.Return s (.VLam x M ρ)) k = b) : exec (.Eval s ρ (.Lam x M)) (Nat.succ k) = b := h
theorem evalDelay (s : Stack) (ρ : Environment) (M : Term) (k : Nat) (b : State)
    (h : exec (.Return s (.VDelay M ρ)) k = b) : exec (.Eval s ρ (.Delay M)) (Nat.succ k) = b := h
theorem evalForce (s : Stack) (ρ : Environment) (M : Term) (k : Nat) (b : State)
    (h : exec (.Eval (.ForceFrame :: s) ρ M) k = b) : exec (.Eval s ρ (.Force M)) (Nat.succ k) = b := h
theorem evalApply (s : Stack) (ρ : Environment) (M N : Term) (k : Nat) (b : State)
    (h : exec (.Eval (.LeftApplicationToTerm N ρ :: s) ρ M) k = b) : exec (.Eval s ρ (.Apply M N)) (Nat.succ k) = b := h
theorem evalConstrCons (s : Stack) (ρ : Environment) (i : Nat) (M : Term) (Ms : List Term) (k : Nat) (b : State)
    (h : exec (.Eval (.ConstructorArgument i [] Ms ρ :: s) ρ M) k = b) : exec (.Eval s ρ (.Constr i (M :: Ms))) (Nat.succ k) = b := h
theorem evalConstrNil (s : Stack) (ρ : Environment) (i : Nat) (k : Nat) (b : State)
    (h : exec (.Return s (.VConstr i [])) k = b) : exec (.Eval s ρ (.Constr i [])) (Nat.succ k) = b := h
theorem evalCase (s : Stack) (ρ : Environment) (N : Term) (Ms : List Term) (k : Nat) (b : State)
    (h : exec (.Eval (.CaseScrutinee Ms ρ :: s) ρ N) k = b) : exec (.Eval s ρ (.Case N Ms)) (Nat.succ k) = b := h
theorem retHalt (V : CekValue) (k : Nat) (b : State)
    (h : exec (.Halt V) k = b) : exec (.Return [] V) (Nat.succ k) = b := h
theorem retLeftAppTerm (s : Stack) (ρ : Environment) (M : Term) (V : CekValue) (k : Nat) (b : State)
    (h : exec (.Eval (.RightApplicationOfValue V :: s) ρ M) k = b) : exec (.Return (.LeftApplicationToTerm M ρ :: s) V) (Nat.succ k) = b := h
theorem retRightAppLam (s : Stack) (ρ : Environment) (x : String) (M : Term) (V : CekValue) (k : Nat) (b : State)
    (h : exec (.Eval s (.NonEmptyEvironment ρ x V) M) k = b) : exec (.Return (.RightApplicationOfValue (.VLam x M ρ) :: s) V) (Nat.succ k) = b := h
theorem retLeftAppLam (s : Stack) (ρ : Environment) (x : String) (M : Term) (V : CekValue) (k : Nat) (b : State)
    (h : exec (.Eval s (.NonEmptyEvironment ρ x V) M) k = b) : exec (.Return (.LeftApplicationToValue V :: s) (.VLam x M ρ)) (Nat.succ k) = b := h
theorem retRightAppBuiltin (s : Stack) (f : BuiltinFun) (Vs : List CekValue) (η : ExpectedBuiltinArgs) (V : CekValue) (k : Nat) (b : State)
    (h : exec (.Return s (.VBuiltin f (V :: Vs) η)) k = b) : exec (.Return (.RightApplicationOfValue (.VBuiltin f Vs (.More .ArgV η)) :: s) V) (Nat.succ k) = b := h
theorem retLeftAppBuiltin (s : Stack) (f : BuiltinFun) (Vs : List CekValue) (η : ExpectedBuiltinArgs) (V : CekValue) (k : Nat) (b : State)
    (h : exec (.Return s (.VBuiltin f (V :: Vs) η)) k = b) : exec (.Return (.LeftApplicationToValue V :: s) (.VBuiltin f Vs (.More .ArgV η))) (Nat.succ k) = b := h
theorem retForceDelay (s : Stack) (ρ : Environment) (M : Term) (k : Nat) (b : State)
    (h : exec (.Eval s ρ M) k = b) : exec (.Return (.ForceFrame :: s) (.VDelay M ρ)) (Nat.succ k) = b := h
theorem retForceBuiltin (s : Stack) (f : BuiltinFun) (Vs : List CekValue) (η : ExpectedBuiltinArgs) (k : Nat) (b : State)
    (h : exec (.Return s (.VBuiltin f Vs η)) k = b) : exec (.Return (.ForceFrame :: s) (.VBuiltin f Vs (.More .ArgQ η))) (Nat.succ k) = b := h
theorem retConstrArg (s : Stack) (ρ : Environment) (i : Nat) (Vs : List CekValue) (M : Term) (Ms : List Term) (V : CekValue) (k : Nat) (b : State)
    (h : exec (.Eval (.ConstructorArgument i (V :: Vs) Ms ρ :: s) ρ M) k = b) : exec (.Return (.ConstructorArgument i Vs (M :: Ms) ρ :: s) V) (Nat.succ k) = b := h

/-! ## Saturated builtins

The last argument of a builtin whose value `evalBuiltin` computes from the arguments'
constructors, followed by the rest of the run: `sat<builtin><shape>R` (the argument came
after the function, `RightApplicationOfValue`) and `…L` (`LeftApplicationToValue`, from
`case`). True by definition: the kernel checked each one, `evalBuiltin` and all, when
this file was built; an instance costs it only the comparison of the pieces. One lemma
per shape `Sym.Fast.builtin?` knows; the pieces are those it returns. -/

theorem satHeadListDataR (s : Stack) (x) (xs) (k : Nat) (b : State)
    (h : exec (.Return s (.VCon (.Data x))) k = b) :
    exec (.Return (.RightApplicationOfValue (.VBuiltin .HeadList [] (.One .ArgV)) :: s) (.VCon (.ConstDataList (x :: xs)))) (Nat.succ k) = b := h
theorem satHeadListDataL (s : Stack) (x) (xs) (k : Nat) (b : State)
    (h : exec (.Return s (.VCon (.Data x))) k = b) :
    exec (.Return (.LeftApplicationToValue (.VCon (.ConstDataList (x :: xs))) :: s) (.VBuiltin .HeadList [] (.One .ArgV))) (Nat.succ k) = b := h
theorem satTailListDataR (s : Stack) (x) (xs) (k : Nat) (b : State)
    (h : exec (.Return s (.VCon (.ConstDataList xs))) k = b) :
    exec (.Return (.RightApplicationOfValue (.VBuiltin .TailList [] (.One .ArgV)) :: s) (.VCon (.ConstDataList (x :: xs)))) (Nat.succ k) = b := h
theorem satTailListDataL (s : Stack) (x) (xs) (k : Nat) (b : State)
    (h : exec (.Return s (.VCon (.ConstDataList xs))) k = b) :
    exec (.Return (.LeftApplicationToValue (.VCon (.ConstDataList (x :: xs))) :: s) (.VBuiltin .TailList [] (.One .ArgV))) (Nat.succ k) = b := h
theorem satNullListDataConsR (s : Stack) (x) (xs) (k : Nat) (b : State)
    (h : exec (.Return s (.VCon (.Bool false))) k = b) :
    exec (.Return (.RightApplicationOfValue (.VBuiltin .NullList [] (.One .ArgV)) :: s) (.VCon (.ConstDataList (x :: xs)))) (Nat.succ k) = b := h
theorem satNullListDataConsL (s : Stack) (x) (xs) (k : Nat) (b : State)
    (h : exec (.Return s (.VCon (.Bool false))) k = b) :
    exec (.Return (.LeftApplicationToValue (.VCon (.ConstDataList (x :: xs))) :: s) (.VBuiltin .NullList [] (.One .ArgV))) (Nat.succ k) = b := h
theorem satNullListDataNilR (s : Stack) (k : Nat) (b : State)
    (h : exec (.Return s (.VCon (.Bool true))) k = b) :
    exec (.Return (.RightApplicationOfValue (.VBuiltin .NullList [] (.One .ArgV)) :: s) (.VCon (.ConstDataList []))) (Nat.succ k) = b := h
theorem satNullListDataNilL (s : Stack) (k : Nat) (b : State)
    (h : exec (.Return s (.VCon (.Bool true))) k = b) :
    exec (.Return (.LeftApplicationToValue (.VCon (.ConstDataList [])) :: s) (.VBuiltin .NullList [] (.One .ArgV))) (Nat.succ k) = b := h
theorem satChooseListDataConsR (s : Stack) (lc nc : CekValue) (x) (xs) (k : Nat) (b : State)
    (h : exec (.Return s (lc)) k = b) :
    exec (.Return (.RightApplicationOfValue (.VBuiltin .ChooseList [nc, .VCon (.ConstDataList (x :: xs))] (.One .ArgV)) :: s) (lc)) (Nat.succ k) = b := h
theorem satChooseListDataConsL (s : Stack) (lc nc : CekValue) (x) (xs) (k : Nat) (b : State)
    (h : exec (.Return s (lc)) k = b) :
    exec (.Return (.LeftApplicationToValue (lc) :: s) (.VBuiltin .ChooseList [nc, .VCon (.ConstDataList (x :: xs))] (.One .ArgV))) (Nat.succ k) = b := h
theorem satChooseListDataNilR (s : Stack) (lc nc : CekValue) (k : Nat) (b : State)
    (h : exec (.Return s (nc)) k = b) :
    exec (.Return (.RightApplicationOfValue (.VBuiltin .ChooseList [nc, .VCon (.ConstDataList [])] (.One .ArgV)) :: s) (lc)) (Nat.succ k) = b := h
theorem satChooseListDataNilL (s : Stack) (lc nc : CekValue) (k : Nat) (b : State)
    (h : exec (.Return s (nc)) k = b) :
    exec (.Return (.LeftApplicationToValue (lc) :: s) (.VBuiltin .ChooseList [nc, .VCon (.ConstDataList [])] (.One .ArgV))) (Nat.succ k) = b := h
theorem satHeadListConstR (s : Stack) (x) (xs) (k : Nat) (b : State)
    (h : exec (.Return s (.VCon (x))) k = b) :
    exec (.Return (.RightApplicationOfValue (.VBuiltin .HeadList [] (.One .ArgV)) :: s) (.VCon (.ConstList (x :: xs)))) (Nat.succ k) = b := h
theorem satHeadListConstL (s : Stack) (x) (xs) (k : Nat) (b : State)
    (h : exec (.Return s (.VCon (x))) k = b) :
    exec (.Return (.LeftApplicationToValue (.VCon (.ConstList (x :: xs))) :: s) (.VBuiltin .HeadList [] (.One .ArgV))) (Nat.succ k) = b := h
theorem satTailListConstR (s : Stack) (x) (xs) (k : Nat) (b : State)
    (h : exec (.Return s (.VCon (.ConstList xs))) k = b) :
    exec (.Return (.RightApplicationOfValue (.VBuiltin .TailList [] (.One .ArgV)) :: s) (.VCon (.ConstList (x :: xs)))) (Nat.succ k) = b := h
theorem satTailListConstL (s : Stack) (x) (xs) (k : Nat) (b : State)
    (h : exec (.Return s (.VCon (.ConstList xs))) k = b) :
    exec (.Return (.LeftApplicationToValue (.VCon (.ConstList (x :: xs))) :: s) (.VBuiltin .TailList [] (.One .ArgV))) (Nat.succ k) = b := h
theorem satNullListConstConsR (s : Stack) (x) (xs) (k : Nat) (b : State)
    (h : exec (.Return s (.VCon (.Bool false))) k = b) :
    exec (.Return (.RightApplicationOfValue (.VBuiltin .NullList [] (.One .ArgV)) :: s) (.VCon (.ConstList (x :: xs)))) (Nat.succ k) = b := h
theorem satNullListConstConsL (s : Stack) (x) (xs) (k : Nat) (b : State)
    (h : exec (.Return s (.VCon (.Bool false))) k = b) :
    exec (.Return (.LeftApplicationToValue (.VCon (.ConstList (x :: xs))) :: s) (.VBuiltin .NullList [] (.One .ArgV))) (Nat.succ k) = b := h
theorem satNullListConstNilR (s : Stack) (k : Nat) (b : State)
    (h : exec (.Return s (.VCon (.Bool true))) k = b) :
    exec (.Return (.RightApplicationOfValue (.VBuiltin .NullList [] (.One .ArgV)) :: s) (.VCon (.ConstList []))) (Nat.succ k) = b := h
theorem satNullListConstNilL (s : Stack) (k : Nat) (b : State)
    (h : exec (.Return s (.VCon (.Bool true))) k = b) :
    exec (.Return (.LeftApplicationToValue (.VCon (.ConstList [])) :: s) (.VBuiltin .NullList [] (.One .ArgV))) (Nat.succ k) = b := h
theorem satChooseListConstConsR (s : Stack) (lc nc : CekValue) (x) (xs) (k : Nat) (b : State)
    (h : exec (.Return s (lc)) k = b) :
    exec (.Return (.RightApplicationOfValue (.VBuiltin .ChooseList [nc, .VCon (.ConstList (x :: xs))] (.One .ArgV)) :: s) (lc)) (Nat.succ k) = b := h
theorem satChooseListConstConsL (s : Stack) (lc nc : CekValue) (x) (xs) (k : Nat) (b : State)
    (h : exec (.Return s (lc)) k = b) :
    exec (.Return (.LeftApplicationToValue (lc) :: s) (.VBuiltin .ChooseList [nc, .VCon (.ConstList (x :: xs))] (.One .ArgV))) (Nat.succ k) = b := h
theorem satChooseListConstNilR (s : Stack) (lc nc : CekValue) (k : Nat) (b : State)
    (h : exec (.Return s (nc)) k = b) :
    exec (.Return (.RightApplicationOfValue (.VBuiltin .ChooseList [nc, .VCon (.ConstList [])] (.One .ArgV)) :: s) (lc)) (Nat.succ k) = b := h
theorem satChooseListConstNilL (s : Stack) (lc nc : CekValue) (k : Nat) (b : State)
    (h : exec (.Return s (nc)) k = b) :
    exec (.Return (.LeftApplicationToValue (lc) :: s) (.VBuiltin .ChooseList [nc, .VCon (.ConstList [])] (.One .ArgV))) (Nat.succ k) = b := h
theorem satHeadListPairR (s : Stack) (x) (xs) (k : Nat) (b : State)
    (h : exec (.Return s (.VCon (.PairData x))) k = b) :
    exec (.Return (.RightApplicationOfValue (.VBuiltin .HeadList [] (.One .ArgV)) :: s) (.VCon (.ConstPairDataList (x :: xs)))) (Nat.succ k) = b := h
theorem satHeadListPairL (s : Stack) (x) (xs) (k : Nat) (b : State)
    (h : exec (.Return s (.VCon (.PairData x))) k = b) :
    exec (.Return (.LeftApplicationToValue (.VCon (.ConstPairDataList (x :: xs))) :: s) (.VBuiltin .HeadList [] (.One .ArgV))) (Nat.succ k) = b := h
theorem satTailListPairR (s : Stack) (x) (xs) (k : Nat) (b : State)
    (h : exec (.Return s (.VCon (.ConstPairDataList xs))) k = b) :
    exec (.Return (.RightApplicationOfValue (.VBuiltin .TailList [] (.One .ArgV)) :: s) (.VCon (.ConstPairDataList (x :: xs)))) (Nat.succ k) = b := h
theorem satTailListPairL (s : Stack) (x) (xs) (k : Nat) (b : State)
    (h : exec (.Return s (.VCon (.ConstPairDataList xs))) k = b) :
    exec (.Return (.LeftApplicationToValue (.VCon (.ConstPairDataList (x :: xs))) :: s) (.VBuiltin .TailList [] (.One .ArgV))) (Nat.succ k) = b := h
theorem satNullListPairConsR (s : Stack) (x) (xs) (k : Nat) (b : State)
    (h : exec (.Return s (.VCon (.Bool false))) k = b) :
    exec (.Return (.RightApplicationOfValue (.VBuiltin .NullList [] (.One .ArgV)) :: s) (.VCon (.ConstPairDataList (x :: xs)))) (Nat.succ k) = b := h
theorem satNullListPairConsL (s : Stack) (x) (xs) (k : Nat) (b : State)
    (h : exec (.Return s (.VCon (.Bool false))) k = b) :
    exec (.Return (.LeftApplicationToValue (.VCon (.ConstPairDataList (x :: xs))) :: s) (.VBuiltin .NullList [] (.One .ArgV))) (Nat.succ k) = b := h
theorem satNullListPairNilR (s : Stack) (k : Nat) (b : State)
    (h : exec (.Return s (.VCon (.Bool true))) k = b) :
    exec (.Return (.RightApplicationOfValue (.VBuiltin .NullList [] (.One .ArgV)) :: s) (.VCon (.ConstPairDataList []))) (Nat.succ k) = b := h
theorem satNullListPairNilL (s : Stack) (k : Nat) (b : State)
    (h : exec (.Return s (.VCon (.Bool true))) k = b) :
    exec (.Return (.LeftApplicationToValue (.VCon (.ConstPairDataList [])) :: s) (.VBuiltin .NullList [] (.One .ArgV))) (Nat.succ k) = b := h
theorem satChooseListPairConsR (s : Stack) (lc nc : CekValue) (x) (xs) (k : Nat) (b : State)
    (h : exec (.Return s (lc)) k = b) :
    exec (.Return (.RightApplicationOfValue (.VBuiltin .ChooseList [nc, .VCon (.ConstPairDataList (x :: xs))] (.One .ArgV)) :: s) (lc)) (Nat.succ k) = b := h
theorem satChooseListPairConsL (s : Stack) (lc nc : CekValue) (x) (xs) (k : Nat) (b : State)
    (h : exec (.Return s (lc)) k = b) :
    exec (.Return (.LeftApplicationToValue (lc) :: s) (.VBuiltin .ChooseList [nc, .VCon (.ConstPairDataList (x :: xs))] (.One .ArgV))) (Nat.succ k) = b := h
theorem satChooseListPairNilR (s : Stack) (lc nc : CekValue) (k : Nat) (b : State)
    (h : exec (.Return s (nc)) k = b) :
    exec (.Return (.RightApplicationOfValue (.VBuiltin .ChooseList [nc, .VCon (.ConstPairDataList [])] (.One .ArgV)) :: s) (lc)) (Nat.succ k) = b := h
theorem satChooseListPairNilL (s : Stack) (lc nc : CekValue) (k : Nat) (b : State)
    (h : exec (.Return s (nc)) k = b) :
    exec (.Return (.LeftApplicationToValue (lc) :: s) (.VBuiltin .ChooseList [nc, .VCon (.ConstPairDataList [])] (.One .ArgV))) (Nat.succ k) = b := h
theorem satMkConsDataR (s : Stack) (x) (xs) (k : Nat) (b : State)
    (h : exec (.Return s (.VCon (.ConstDataList (x :: xs)))) k = b) :
    exec (.Return (.RightApplicationOfValue (.VBuiltin .MkCons [.VCon (.Data x)] (.One .ArgV)) :: s) (.VCon (.ConstDataList xs))) (Nat.succ k) = b := h
theorem satMkConsDataL (s : Stack) (x) (xs) (k : Nat) (b : State)
    (h : exec (.Return s (.VCon (.ConstDataList (x :: xs)))) k = b) :
    exec (.Return (.LeftApplicationToValue (.VCon (.ConstDataList xs)) :: s) (.VBuiltin .MkCons [.VCon (.Data x)] (.One .ArgV))) (Nat.succ k) = b := h
theorem satMkConsPairR (s : Stack) (x) (xs) (k : Nat) (b : State)
    (h : exec (.Return s (.VCon (.ConstPairDataList (x :: xs)))) k = b) :
    exec (.Return (.RightApplicationOfValue (.VBuiltin .MkCons [.VCon (.PairData x)] (.One .ArgV)) :: s) (.VCon (.ConstPairDataList xs))) (Nat.succ k) = b := h
theorem satMkConsPairL (s : Stack) (x) (xs) (k : Nat) (b : State)
    (h : exec (.Return s (.VCon (.ConstPairDataList (x :: xs)))) k = b) :
    exec (.Return (.LeftApplicationToValue (.VCon (.ConstPairDataList xs)) :: s) (.VBuiltin .MkCons [.VCon (.PairData x)] (.One .ArgV))) (Nat.succ k) = b := h
theorem satMkConsConstR (s : Stack) (x : Const) (xs) (k : Nat) (b : State)
    (h : exec (.Return s (.VCon (.ConstList (x :: xs)))) k = b) :
    exec (.Return (.RightApplicationOfValue (.VBuiltin .MkCons [.VCon x] (.One .ArgV)) :: s) (.VCon (.ConstList xs))) (Nat.succ k) = b := h
theorem satMkConsConstL (s : Stack) (x : Const) (xs) (k : Nat) (b : State)
    (h : exec (.Return s (.VCon (.ConstList (x :: xs)))) k = b) :
    exec (.Return (.LeftApplicationToValue (.VCon (.ConstList xs)) :: s) (.VBuiltin .MkCons [.VCon x] (.One .ArgV))) (Nat.succ k) = b := h
theorem satIfThenElseTrueR (s : Stack) (t e : CekValue) (k : Nat) (b : State)
    (h : exec (.Return s (t)) k = b) :
    exec (.Return (.RightApplicationOfValue (.VBuiltin .IfThenElse [t, .VCon (.Bool true)] (.One .ArgV)) :: s) (e)) (Nat.succ k) = b := h
theorem satIfThenElseTrueL (s : Stack) (t e : CekValue) (k : Nat) (b : State)
    (h : exec (.Return s (t)) k = b) :
    exec (.Return (.LeftApplicationToValue (e) :: s) (.VBuiltin .IfThenElse [t, .VCon (.Bool true)] (.One .ArgV))) (Nat.succ k) = b := h
theorem satIfThenElseFalseR (s : Stack) (t e : CekValue) (k : Nat) (b : State)
    (h : exec (.Return s (e)) k = b) :
    exec (.Return (.RightApplicationOfValue (.VBuiltin .IfThenElse [t, .VCon (.Bool false)] (.One .ArgV)) :: s) (e)) (Nat.succ k) = b := h
theorem satIfThenElseFalseL (s : Stack) (t e : CekValue) (k : Nat) (b : State)
    (h : exec (.Return s (e)) k = b) :
    exec (.Return (.LeftApplicationToValue (e) :: s) (.VBuiltin .IfThenElse [t, .VCon (.Bool false)] (.One .ArgV))) (Nat.succ k) = b := h
theorem satFstPairDataR (s : Stack) (x y) (k : Nat) (b : State)
    (h : exec (.Return s (.VCon (.Data x))) k = b) :
    exec (.Return (.RightApplicationOfValue (.VBuiltin .FstPair [] (.One .ArgV)) :: s) (.VCon (.PairData (x, y)))) (Nat.succ k) = b := h
theorem satFstPairDataL (s : Stack) (x y) (k : Nat) (b : State)
    (h : exec (.Return s (.VCon (.Data x))) k = b) :
    exec (.Return (.LeftApplicationToValue (.VCon (.PairData (x, y))) :: s) (.VBuiltin .FstPair [] (.One .ArgV))) (Nat.succ k) = b := h
theorem satSndPairDataR (s : Stack) (x y) (k : Nat) (b : State)
    (h : exec (.Return s (.VCon (.Data y))) k = b) :
    exec (.Return (.RightApplicationOfValue (.VBuiltin .SndPair [] (.One .ArgV)) :: s) (.VCon (.PairData (x, y)))) (Nat.succ k) = b := h
theorem satSndPairDataL (s : Stack) (x y) (k : Nat) (b : State)
    (h : exec (.Return s (.VCon (.Data y))) k = b) :
    exec (.Return (.LeftApplicationToValue (.VCon (.PairData (x, y))) :: s) (.VBuiltin .SndPair [] (.One .ArgV))) (Nat.succ k) = b := h
theorem satFstPairConstR (s : Stack) (x y : Const) (k : Nat) (b : State)
    (h : exec (.Return s (.VCon x)) k = b) :
    exec (.Return (.RightApplicationOfValue (.VBuiltin .FstPair [] (.One .ArgV)) :: s) (.VCon (.Pair (x, y)))) (Nat.succ k) = b := h
theorem satFstPairConstL (s : Stack) (x y : Const) (k : Nat) (b : State)
    (h : exec (.Return s (.VCon x)) k = b) :
    exec (.Return (.LeftApplicationToValue (.VCon (.Pair (x, y))) :: s) (.VBuiltin .FstPair [] (.One .ArgV))) (Nat.succ k) = b := h
theorem satSndPairConstR (s : Stack) (x y : Const) (k : Nat) (b : State)
    (h : exec (.Return s (.VCon y)) k = b) :
    exec (.Return (.RightApplicationOfValue (.VBuiltin .SndPair [] (.One .ArgV)) :: s) (.VCon (.Pair (x, y)))) (Nat.succ k) = b := h
theorem satSndPairConstL (s : Stack) (x y : Const) (k : Nat) (b : State)
    (h : exec (.Return s (.VCon y)) k = b) :
    exec (.Return (.LeftApplicationToValue (.VCon (.Pair (x, y))) :: s) (.VBuiltin .SndPair [] (.One .ArgV))) (Nat.succ k) = b := h
theorem satUnConstrDataR (s : Stack) (i) (xs) (k : Nat) (b : State)
    (h : exec (.Return s (.VCon (.Pair (.Integer i, .ConstDataList xs)))) k = b) :
    exec (.Return (.RightApplicationOfValue (.VBuiltin .UnConstrData [] (.One .ArgV)) :: s) (.VCon (.Data (.Constr i xs)))) (Nat.succ k) = b := h
theorem satUnConstrDataL (s : Stack) (i) (xs) (k : Nat) (b : State)
    (h : exec (.Return s (.VCon (.Pair (.Integer i, .ConstDataList xs)))) k = b) :
    exec (.Return (.LeftApplicationToValue (.VCon (.Data (.Constr i xs))) :: s) (.VBuiltin .UnConstrData [] (.One .ArgV))) (Nat.succ k) = b := h
theorem satUnIDataR (s : Stack) (i) (k : Nat) (b : State)
    (h : exec (.Return s (.VCon (.Integer i))) k = b) :
    exec (.Return (.RightApplicationOfValue (.VBuiltin .UnIData [] (.One .ArgV)) :: s) (.VCon (.Data (.I i)))) (Nat.succ k) = b := h
theorem satUnIDataL (s : Stack) (i) (k : Nat) (b : State)
    (h : exec (.Return s (.VCon (.Integer i))) k = b) :
    exec (.Return (.LeftApplicationToValue (.VCon (.Data (.I i))) :: s) (.VBuiltin .UnIData [] (.One .ArgV))) (Nat.succ k) = b := h
theorem satUnBDataR (s : Stack) (x) (k : Nat) (b : State)
    (h : exec (.Return s (.VCon (.ByteString x))) k = b) :
    exec (.Return (.RightApplicationOfValue (.VBuiltin .UnBData [] (.One .ArgV)) :: s) (.VCon (.Data (.B x)))) (Nat.succ k) = b := h
theorem satUnBDataL (s : Stack) (x) (k : Nat) (b : State)
    (h : exec (.Return s (.VCon (.ByteString x))) k = b) :
    exec (.Return (.LeftApplicationToValue (.VCon (.Data (.B x))) :: s) (.VBuiltin .UnBData [] (.One .ArgV))) (Nat.succ k) = b := h
theorem satIDataR (s : Stack) (i) (k : Nat) (b : State)
    (h : exec (.Return s (.VCon (.Data (.I i)))) k = b) :
    exec (.Return (.RightApplicationOfValue (.VBuiltin .IData [] (.One .ArgV)) :: s) (.VCon (.Integer i))) (Nat.succ k) = b := h
theorem satIDataL (s : Stack) (i) (k : Nat) (b : State)
    (h : exec (.Return s (.VCon (.Data (.I i)))) k = b) :
    exec (.Return (.LeftApplicationToValue (.VCon (.Integer i)) :: s) (.VBuiltin .IData [] (.One .ArgV))) (Nat.succ k) = b := h
theorem satBDataR (s : Stack) (x) (k : Nat) (b : State)
    (h : exec (.Return s (.VCon (.Data (.B x)))) k = b) :
    exec (.Return (.RightApplicationOfValue (.VBuiltin .BData [] (.One .ArgV)) :: s) (.VCon (.ByteString x))) (Nat.succ k) = b := h
theorem satBDataL (s : Stack) (x) (k : Nat) (b : State)
    (h : exec (.Return s (.VCon (.Data (.B x)))) k = b) :
    exec (.Return (.LeftApplicationToValue (.VCon (.ByteString x)) :: s) (.VBuiltin .BData [] (.One .ArgV))) (Nat.succ k) = b := h
theorem satConstrDataR (s : Stack) (i) (xs) (k : Nat) (b : State)
    (h : exec (.Return s (.VCon (.Data (.Constr i xs)))) k = b) :
    exec (.Return (.RightApplicationOfValue (.VBuiltin .ConstrData [.VCon (.Integer i)] (.One .ArgV)) :: s) (.VCon (.ConstDataList xs))) (Nat.succ k) = b := h
theorem satConstrDataL (s : Stack) (i) (xs) (k : Nat) (b : State)
    (h : exec (.Return s (.VCon (.Data (.Constr i xs)))) k = b) :
    exec (.Return (.LeftApplicationToValue (.VCon (.ConstDataList xs)) :: s) (.VBuiltin .ConstrData [.VCon (.Integer i)] (.One .ArgV))) (Nat.succ k) = b := h
theorem satMkPairDataR (s : Stack) (x y) (k : Nat) (b : State)
    (h : exec (.Return s (.VCon (.PairData (x, y)))) k = b) :
    exec (.Return (.RightApplicationOfValue (.VBuiltin .MkPairData [.VCon (.Data x)] (.One .ArgV)) :: s) (.VCon (.Data y))) (Nat.succ k) = b := h
theorem satMkPairDataL (s : Stack) (x y) (k : Nat) (b : State)
    (h : exec (.Return s (.VCon (.PairData (x, y)))) k = b) :
    exec (.Return (.LeftApplicationToValue (.VCon (.Data y)) :: s) (.VBuiltin .MkPairData [.VCon (.Data x)] (.One .ArgV))) (Nat.succ k) = b := h
theorem satMapDataR (s : Stack) (xs) (k : Nat) (b : State)
    (h : exec (.Return s (.VCon (.Data (.Map xs)))) k = b) :
    exec (.Return (.RightApplicationOfValue (.VBuiltin .MapData [] (.One .ArgV)) :: s) (.VCon (.ConstPairDataList xs))) (Nat.succ k) = b := h
theorem satMapDataL (s : Stack) (xs) (k : Nat) (b : State)
    (h : exec (.Return s (.VCon (.Data (.Map xs)))) k = b) :
    exec (.Return (.LeftApplicationToValue (.VCon (.ConstPairDataList xs)) :: s) (.VBuiltin .MapData [] (.One .ArgV))) (Nat.succ k) = b := h
theorem satListDataR (s : Stack) (xs) (k : Nat) (b : State)
    (h : exec (.Return s (.VCon (.Data (.List xs)))) k = b) :
    exec (.Return (.RightApplicationOfValue (.VBuiltin .ListData [] (.One .ArgV)) :: s) (.VCon (.ConstDataList xs))) (Nat.succ k) = b := h
theorem satListDataL (s : Stack) (xs) (k : Nat) (b : State)
    (h : exec (.Return s (.VCon (.Data (.List xs)))) k = b) :
    exec (.Return (.LeftApplicationToValue (.VCon (.ConstDataList xs)) :: s) (.VBuiltin .ListData [] (.One .ArgV))) (Nat.succ k) = b := h
theorem satUnMapDataR (s : Stack) (xs) (k : Nat) (b : State)
    (h : exec (.Return s (.VCon (.ConstPairDataList xs))) k = b) :
    exec (.Return (.RightApplicationOfValue (.VBuiltin .UnMapData [] (.One .ArgV)) :: s) (.VCon (.Data (.Map xs)))) (Nat.succ k) = b := h
theorem satUnMapDataL (s : Stack) (xs) (k : Nat) (b : State)
    (h : exec (.Return s (.VCon (.ConstPairDataList xs))) k = b) :
    exec (.Return (.LeftApplicationToValue (.VCon (.Data (.Map xs))) :: s) (.VBuiltin .UnMapData [] (.One .ArgV))) (Nat.succ k) = b := h
theorem satUnListDataR (s : Stack) (xs) (k : Nat) (b : State)
    (h : exec (.Return s (.VCon (.ConstDataList xs))) k = b) :
    exec (.Return (.RightApplicationOfValue (.VBuiltin .UnListData [] (.One .ArgV)) :: s) (.VCon (.Data (.List xs)))) (Nat.succ k) = b := h
theorem satUnListDataL (s : Stack) (xs) (k : Nat) (b : State)
    (h : exec (.Return s (.VCon (.ConstDataList xs))) k = b) :
    exec (.Return (.LeftApplicationToValue (.VCon (.Data (.List xs))) :: s) (.VBuiltin .UnListData [] (.One .ArgV))) (Nat.succ k) = b := h

/-- `Term.Builtin f`: its value, with the expected arguments `expectedArgs f` (the engine
    writes them computed; the kernel unfolds `expectedArgs f` to compare). -/
theorem evalBuiltinTerm (s : Stack) (ρ : Environment) (f : BuiltinFun) (k : Nat) (b : State)
    (h : exec (.Return s (.VBuiltin f [] (expectedArgs f))) k = b) :
    exec (.Eval s ρ (.Builtin f)) (Nat.succ k) = b := h

end UplcProof.Steps
