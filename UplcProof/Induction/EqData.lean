import PlutusCore.UPLC

/-!
# Equality on `Data`, by evaluation

PlutusCore's `Data` equality `eqData` (behind the `equalsData` builtin, `==` and
`DecidableEq` on `Data`, `Data` nested in lists and maps included) is defined by
well-founded recursion, hence `@[irreducible]`: neither `whnf` nor the kernel
evaluate it, not even `eqData d d` on a closed `d` (`decide`, `decide +kernel`,
`rfl` all fail). A run that branches on `equalsData x y` gets stuck there.

`dataEqB` is the same function by structural recursion, which both evaluate; and
`equalsData_eq_dataEqB` proves them equal once. So a closed `equalsData x y` is
decided by the kernel: `(equalsData_eq_dataEqB x y).trans (Eq.refl b)`.

`equalsData_eq_true_iff` / `equalsData_eq_false_iff` turn a symbolic condition into
`x = y` / `x ≠ y` without `Classical.choice` (PlutusCore's `LawfulBEq Data`, which
`beq_iff_eq` would use, depends on it).

The other definition behind a builtin that neither evaluates is `decodeUtf8.loop`
(the `DecodeUtf8` builtin, also by well-founded recursion): a run through
`DecodeUtf8` gets stuck, and nothing here resolves it.
-/

open PlutusCore.Data (Data)
open PlutusCore.Data.PlutusCore.DataInternal (eqData eqDataList eqDataMap eqDataConstr
  eqData_true_imp_eq)

namespace UplcProof

mutual
/-- `Data` equality by structural recursion: `eqData`, which the kernel can evaluate. -/
def dataEqB : Data → Data → Bool
  | .Constr i as, .Constr j bs => i == j && listEqB as bs
  | .Map m, .Map m' => pairsEqB m m'
  | .List l, .List l' => listEqB l l'
  | .I i, .I j => i == j
  | .B b, .B c => b == c
  | _, _ => false
termination_by structural x => x

/-- `dataEqB` on lists. -/
def listEqB : List Data → List Data → Bool
  | [], [] => true
  | x :: xs, y :: ys => dataEqB x y && listEqB xs ys
  | _, _ => false
termination_by structural xs => xs

/-- `dataEqB` on lists of pairs (`Data.Map`). -/
def pairsEqB : List (Data × Data) → List (Data × Data) → Bool
  | [], [] => true
  | (a, b) :: xs, (c, d) :: ys => dataEqB a c && dataEqB b d && pairsEqB xs ys
  | _, _ => false
termination_by structural xs => xs
end

mutual
theorem eqData_eq_dataEqB (x y : Data) : eqData x y = dataEqB x y := by
  rw [eqData.eq_def]
  cases x with
  | Constr i as =>
    cases y with
    | Constr j bs =>
      show eqDataConstr i as j bs = _
      rw [eqDataConstr.eq_def]
      show (i == j && eqDataList as bs) = _
      rw [eqDataList_eq_listEqB as bs]; rfl
    | _ => rfl
  | Map m =>
    cases y with
    | Map m' => show eqDataMap m m' = _; rw [eqDataMap_eq_pairsEqB m m']; rfl
    | _ => rfl
  | List l =>
    cases y with
    | List l' => show eqDataList l l' = _; rw [eqDataList_eq_listEqB l l']; rfl
    | _ => rfl
  | I i => cases y <;> rfl
  | B b => cases y <;> rfl
termination_by structural x

theorem eqDataList_eq_listEqB (xs ys : List Data) : eqDataList xs ys = listEqB xs ys := by
  rw [eqDataList.eq_def]
  cases xs with
  | nil => cases ys <;> rfl
  | cons x xs =>
    cases ys with
    | nil => rfl
    | cons y ys =>
      show (eqData x y && eqDataList xs ys) = _
      rw [eqData_eq_dataEqB x y, eqDataList_eq_listEqB xs ys]; rfl
termination_by structural xs

theorem eqDataMap_eq_pairsEqB (xs ys : List (Data × Data)) :
    eqDataMap xs ys = pairsEqB xs ys := by
  rw [eqDataMap.eq_def]
  cases xs with
  | nil => cases ys <;> rfl
  | cons p xs =>
    cases ys with
    | nil => rfl
    | cons q ys =>
      obtain ⟨a, b⟩ := p
      obtain ⟨c, d⟩ := q
      show (eqData a c && eqData b d && eqDataMap xs ys) = _
      rw [eqData_eq_dataEqB a c, eqData_eq_dataEqB b d, eqDataMap_eq_pairsEqB xs ys]; rfl
termination_by structural xs
end

/-- `i == i` on `Int` (`beq_self_eq_true` would use `Classical.choice` here). -/
theorem int_beq_self (i : PlutusCore.Integer.Integer) : (i == i) = true :=
  decide_eq_true rfl

mutual
theorem dataEqB_refl (x : Data) : dataEqB x x = true := by
  cases x with
  | Constr i as =>
    show (i == i && listEqB as as) = true
    rw [int_beq_self, listEqB_refl as]; rfl
  | Map m => show pairsEqB m m = true; exact pairsEqB_refl m
  | List l => show listEqB l l = true; exact listEqB_refl l
  | I i => show (i == i) = true; exact int_beq_self i
  | B b => show (b == b) = true; exact beq_self_eq_true b
termination_by structural x

theorem listEqB_refl (xs : List Data) : listEqB xs xs = true := by
  cases xs with
  | nil => rfl
  | cons x xs =>
    show (dataEqB x x && listEqB xs xs) = true
    rw [dataEqB_refl x, listEqB_refl xs]; rfl
termination_by structural xs

theorem pairsEqB_refl (xs : List (Data × Data)) : pairsEqB xs xs = true := by
  cases xs with
  | nil => rfl
  | cons p xs =>
    obtain ⟨a, b⟩ := p
    show (dataEqB a a && dataEqB b b && pairsEqB xs xs) = true
    rw [dataEqB_refl a, dataEqB_refl b, pairsEqB_refl xs]; rfl
termination_by structural xs
end

/-- The `equalsData` builtin's semantics is `dataEqB`: a closed `equalsData x y = b`
    is `(equalsData_eq_dataEqB x y).trans (Eq.refl b)`, checked by evaluation. -/
theorem equalsData_eq_dataEqB (x y : Data) : PlutusCore.Data.equalsData x y = dataEqB x y :=
  eqData_eq_dataEqB x y

theorem equalsData_self (x : Data) : PlutusCore.Data.equalsData x x = true :=
  (equalsData_eq_dataEqB x x).trans (dataEqB_refl x)

theorem equalsData_eq_true_iff (x y : Data) : PlutusCore.Data.equalsData x y = true ↔ x = y :=
  ⟨eqData_true_imp_eq x y, fun h => h ▸ equalsData_self x⟩

theorem equalsData_eq_false_iff (x y : Data) :
    PlutusCore.Data.equalsData x y = false ↔ x ≠ y := by
  constructor
  · intro h heq
    subst heq
    rw [equalsData_self] at h
    exact Bool.noConfusion h
  · intro hne
    cases h : PlutusCore.Data.equalsData x y
    · rfl
    · exact absurd (eqData_true_imp_eq x y h) hne

theorem equalsData_of_ne {x y : Data} (h : x ≠ y) : PlutusCore.Data.equalsData x y = false :=
  (equalsData_eq_false_iff x y).mpr h

end UplcProof
