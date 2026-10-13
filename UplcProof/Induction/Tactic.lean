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
accepted only if its hypotheses are contradictory (`omega`, `simp_all`, a cycle in the
order of byte strings), or if the leaf closer `Ctx.closer?` closes it (none for
`uplc_induction` and `uplc_run`; a hook for tactics built on `Tactic.runOn`, see
`closer_used` in `UplcProofTests.Induction.Run`).

Besides `n` and `if` conditions, a run splits a symbolic value by its constructors when a
`match` waits on it (a `Data` leaf), or when the condition of a Lean `if` does (`chooseList`
on a free list): at most `Tactic.maxCaseSplits` times on one branch.

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

In aux mode (`Ctx.aux`: `uplc_run`, `Tactic.runOn`), the engine also states runs as
auxiliary theorems (`Sym.sharedRun`, `withAuxLemma`), which the kernel checks one by one,
in the background; it tries cheap refutations first (two complementary hypotheses, a
condition already known) and skips `omega` on facts it already failed on. Every cache
lives in the session of one tactic call (`Sym.withSession`).

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

/-! The order of byte strings against the empty one (any `String`, bytes or not): what a branch
    on `lessThanEqualsByteString x ""` leaves, for `simp_all` in `refute`. -/

theorem byteString_cons_ne_empty (c : Char) (l : List Char) :
    (⟨⟨c :: l⟩⟩ : PlutusCore.ByteString.ByteString) ≠ ⟨""⟩ := by
  intro h
  have := congrArg (fun b : PlutusCore.ByteString.ByteString => b.data.data.length) h
  simp at this

@[simp] theorem byteString_le_empty (x : PlutusCore.ByteString.ByteString) : x ≤ ⟨""⟩ ↔ x = ⟨""⟩ := by
  rcases x with ⟨⟨l⟩⟩
  show ¬ ("" < String.mk l) ↔ _
  rw [String.lt_iff]
  cases l with
  | nil => exact iff_of_true (List.lt_irrefl _) rfl
  | cons c l => exact iff_of_false (fun h => h (List.nil_lt_cons c l)) (byteString_cons_ne_empty c l)

@[simp] theorem byteString_not_lt_empty (x : PlutusCore.ByteString.ByteString) : ¬ x < ⟨""⟩ := by
  rcases x with ⟨⟨l⟩⟩
  show ¬ (String.mk l < "")
  rw [String.lt_iff]
  exact List.not_lt_nil _

@[simp] theorem byteString_empty_le (x : PlutusCore.ByteString.ByteString) :
    (⟨""⟩ : PlutusCore.ByteString.ByteString) ≤ x := byteString_not_lt_empty x

@[simp] theorem byteString_empty_lt (x : PlutusCore.ByteString.ByteString) :
    (⟨""⟩ : PlutusCore.ByteString.ByteString) < x ↔ x ≠ ⟨""⟩ := by
  rcases x with ⟨⟨l⟩⟩
  show ("" < String.mk l) ↔ _
  rw [String.lt_iff]
  cases l with
  | nil => exact iff_of_false (List.lt_irrefl _) (fun h => h rfl)
  | cons c l => exact iff_of_true (List.nil_lt_cons c l) (byteString_cons_ne_empty c l)

@[simp] theorem lengthOfByteString_empty :
    PlutusCore.ByteString.lengthOfByteString ⟨""⟩ = 0 := rfl

/-! The order of byte strings is linear (`String`'s): the steps of a chain, for `byteOrderContra?`. -/

namespace ByteOrder
variable {a b c : PlutusCore.ByteString.ByteString}
theorem le_trans (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := String.le_trans h1 h2
theorem lt_trans (h1 : a < b) (h2 : b < c) : a < c := String.lt_trans h1 h2
theorem lt_of_le_of_lt (h1 : a ≤ b) (h2 : b < c) : a < c :=
  Decidable.byContradiction (p := a.data < c.data) fun h =>
    (String.le_trans (String.not_lt.mp h) h1) h2
theorem lt_of_lt_of_le (h1 : a < b) (h2 : b ≤ c) : a < c :=
  Decidable.byContradiction (p := a.data < c.data) fun h =>
    (String.le_trans h2 (String.not_lt.mp h)) h1
theorem lt_of_not_le (h : ¬ a ≤ b) : b < a := String.not_le.mp h
theorem le_of_not_lt (h : ¬ a < b) : b ≤ a := h
theorem le_of_eq (h : a = b) : a ≤ b := h ▸ String.le_refl a.data
theorem ge_of_eq (h : a = b) : b ≤ a := h ▸ String.le_refl a.data
theorem le_refl (a : PlutusCore.ByteString.ByteString) : a ≤ a := String.le_refl a.data
theorem false_of_lt_self (h : a < a) : False := String.lt_irrefl a.data h
end ByteOrder

/-- The two cases of a `Bool` inside a goal (what `generalize` and `cases` give, with
    the motive written directly). -/
theorem bool_split {c : Bool} {P : Bool → Prop} (hf : c = false → P false)
    (ht : c = true → P true) : P c := by
  cases c
  · exact hf rfl
  · exact ht rfl

/-- Closes equations between CEK values/states produced by symbolic execution:
    `uplc_eq_core`, then `uplc_eq_grind`. -/
syntax (name := uplcEq) "uplc_eq" (" [" Lean.Parser.Tactic.simpArg,* "]")? : tactic

/-- `uplc_eq` without `grind` (its proofs never use `Classical.choice`): unfolds the
    PlutusCore arithmetic and the given definitions, then `omega`; failing that, the same
    with the comparisons unfolded too, `Data` equalities by their constructors, and a
    value chosen by an `if` on a symbolic condition (split, each side by the branch's
    facts). -/
syntax (name := uplcEqCore) "uplc_eq_core" (" [" Lean.Parser.Tactic.simpArg,* "]")? : tactic

/-- `uplc_eq`'s last resort, `grind`: a product written in another order, a recursive
    definition unfolded by its equations. `grind` reads the hypotheses by itself, and
    its proofs use `Classical.choice`. -/
syntax (name := uplcEqGrind) "uplc_eq_grind" (" [" Lean.Parser.Tactic.simpArg,* "]")? : tactic

macro_rules
  | `(tactic| uplc_eq) => `(tactic| uplc_eq [])
  | `(tactic| uplc_eq [$ts,*]) => `(tactic| first | uplc_eq_core [$ts,*] | uplc_eq_grind [$ts,*])

macro_rules
  | `(tactic| uplc_eq_core) => `(tactic| uplc_eq_core [])
  | `(tactic| uplc_eq_core [$ts,*]) => `(tactic|
      first
      | rfl
      | (simp only [State.Return.injEq, State.Halt.injEq, CekValue.VCon.injEq,
            Const.Integer.injEq, Const.Data.injEq, Const.ConstDataList.injEq, Const.Bool.injEq,
            addInteger_eq, subtractInteger_eq, multiplyInteger_eq, $ts,*]
          <;> first
            | ((try dsimp only [PlutusCore.Integer.Integer]) <;> omega)
            | (simp [$ts,*] <;> (try dsimp only [PlutusCore.Integer.Integer]) <;> omega))
      | (simp only [State.Return.injEq, State.Halt.injEq, CekValue.VCon.injEq,
            Const.Integer.injEq, Const.Data.injEq, Const.ConstDataList.injEq, Const.Bool.injEq,
            addInteger_eq, subtractInteger_eq, multiplyInteger_eq,
            PlutusCore.Integer.equalsInteger, PlutusCore.Integer.lessThanInteger,
            PlutusCore.Integer.lessThanEqualsInteger, beq_iff_eq, beq_eq_false_iff_ne,
            decide_eq_true_eq, decide_eq_false_iff_not, $ts,*]
          -- Aiken's `/` and `%` (floor) by a positive literal: the Euclidean ones, which
          -- `omega` reads
          <;> (try simp (disch := decide) only [Int.fdiv_eq_ediv_of_nonneg,
                Int.fmod_eq_emod_of_nonneg])
          <;> first
            | ((try dsimp only [PlutusCore.Integer.Integer]) <;> omega)
            | (simp [$ts,*] <;> (try dsimp only [PlutusCore.Integer.Integer]) <;> omega))
      -- a value decided by `equalsData` of `Data` built from constructors (`eqData` is a
      -- well-founded recursion that `whnf` does not evaluate): `equalsData_eq_true_iff`
      -- (`_false_iff`) and the constructors
      | (simp only [State.Return.injEq, State.Halt.injEq, CekValue.VCon.injEq, Const.Bool.injEq,
            PlutusCore.Bool.ifThenElse, equalsData_eq_true_iff, equalsData_eq_false_iff,
            beq_iff_eq, PlutusCore.Data.PlutusCore.DataInternal.Data.Constr.injEq,
            PlutusCore.Data.PlutusCore.DataInternal.Data.B.injEq,
            PlutusCore.Data.PlutusCore.DataInternal.Data.I.injEq, List.cons.injEq,
            PlutusCore.Data.PlutusCore.DataInternal.Data.Map.injEq,
            PlutusCore.Data.PlutusCore.DataInternal.Data.List.injEq, Prod.mk.injEq,
            reduceCtorEq, Int.ofNat.injEq, Int.negSucc.injEq, and_true, true_and, and_false,
            false_and, ite_true, ite_false, Bool.false_eq_true, $ts,*]; done)
      -- a value chosen by `ifThenElse` on a symbolic condition (aiken's `!=` is the strict
      -- `ifThenElse (equalsInteger a b) False True`, and the run halts with it): split the `if`,
      -- each side closed by the branch's facts
      | (simp only [State.Return.injEq, State.Halt.injEq, PlutusCore.Bool.ifThenElse,
            PlutusCore.Integer.equalsInteger, PlutusCore.Integer.lessThanInteger,
            PlutusCore.Integer.lessThanEqualsInteger, addInteger_eq, subtractInteger_eq,
            multiplyInteger_eq, $ts,*]
         split <;> rename_i hc <;>
           (try simp only [beq_iff_eq, decide_eq_true_eq, decide_eq_false_iff_not, Bool.not_eq_true,
             beq_eq_false_iff_ne, ne_eq] at hc) <;>
           (try dsimp only [PlutusCore.Integer.Integer] at *) <;>
           first | rfl | omega | (simp_all; done)))

macro_rules
  | `(tactic| uplc_eq_grind) => `(tactic| uplc_eq_grind [])
  | `(tactic| uplc_eq_grind [$ts,*]) => `(tactic|
      first
      -- a product the compiler wrote in another order (`n * (1 + n)` for `n * (n + 1)`):
      -- `omega` is linear, `grind` normalizes the ring
      | (simp only [State.Return.injEq, State.Halt.injEq, CekValue.VCon.injEq,
            Const.Integer.injEq, Const.Data.injEq, Const.ConstDataList.injEq, Const.Bool.injEq,
            addInteger_eq, subtractInteger_eq, multiplyInteger_eq,
            PlutusCore.Integer.equalsInteger, PlutusCore.Integer.lessThanInteger,
            PlutusCore.Integer.lessThanEqualsInteger, beq_iff_eq, beq_eq_false_iff_ne,
            decide_eq_true_eq, decide_eq_false_iff_not, $ts,*]
          <;> (try simp (disch := decide) only [Int.fdiv_eq_ediv_of_nonneg,
                Int.fmod_eq_emod_of_nonneg])
          <;> simp only [Bool.beq_eq_decide_eq, decide_eq_decide] <;> grind)
      -- a recursive `def` unfolded by its equations per branch (the condition by `omega`), whose
      -- recursive argument equals the loop's by arithmetic (`↑(k + 2) - 2` and `↑k`, inside the
      -- function): `grind`'s congruence with linear arithmetic
      | (simp (disch := omega) only [State.Return.injEq, State.Halt.injEq, CekValue.VCon.injEq,
            Const.Integer.injEq, addInteger_eq, subtractInteger_eq, multiplyInteger_eq, $ts,*]
         <;> (try dsimp only [PlutusCore.Integer.Integer] at *)
         <;> grind))

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
      PlutusCore.Data.PlutusCore.DataInternal.Data.Map.injEq, PlutusCore.Data.PlutusCore.DataInternal.Data.List.injEq, Prod.mk.injEq, reduceCtorEq, Int.ofNat.injEq, Int.negSucc.injEq,
      ne_eq,
      byteString_le_refl, byteString_lt_irrefl, not_true_eq_false,
      beq_iff_eq, beq_eq_false_iff_ne, decide_eq_true_eq, decide_eq_false_iff_not,
      addInteger_eq, subtractInteger_eq, multiplyInteger_eq] at $h:ident);
    (try simp (disch := decide) only [Int.fdiv_eq_ediv_of_nonneg, Int.fmod_eq_emod_of_nonneg] at $h:ident);
    (try dsimp only [PlutusCore.Integer.Integer] at $h:ident);
    try have := Ne.symm $h))

namespace Tactic

/-- The simp and dsimp contexts of `uplc_cond`, built from the same syntax as the macro
    (`mkSimpContext`), once per session (`Sym.Session.cond`): elaborating the lemma list at
    every branch cost ~5 ms. Shared between the theorems of a file (elaborated in parallel),
    they broke proofs one run in three (measured), hence the session. -/
def condCtxs (g : MVarId) :
    TacticM (Simp.Context × Simp.SimprocsArray × Simp.Context × Simp.SimprocsArray) := do
  let cache? := (← session?).map (·.cond)
  if let some r := cache? then
    if let some c ← r.get then return c
  let h := mkIdent `h
  let s ← `(tactic| simp only [PlutusCore.Integer.equalsInteger, PlutusCore.Integer.lessThanInteger,
      PlutusCore.Integer.lessThanEqualsInteger, PlutusCore.ByteString.equalsByteString,
      PlutusCore.ByteString.lessThanByteString, PlutusCore.ByteString.lessThanEqualsByteString,
      equalsData_eq_true_iff, equalsData_eq_false_iff,
      PlutusCore.Data.PlutusCore.DataInternal.Data.Constr.injEq,
      PlutusCore.Data.PlutusCore.DataInternal.Data.B.injEq,
      PlutusCore.Data.PlutusCore.DataInternal.Data.I.injEq, List.cons.injEq, and_true, true_and,
      PlutusCore.Data.PlutusCore.DataInternal.Data.Map.injEq, PlutusCore.Data.PlutusCore.DataInternal.Data.List.injEq, Prod.mk.injEq, reduceCtorEq, Int.ofNat.injEq, Int.negSucc.injEq,
      ne_eq,
      byteString_le_refl, byteString_lt_irrefl, not_true_eq_false,
      beq_iff_eq, beq_eq_false_iff_ne, decide_eq_true_eq, decide_eq_false_iff_not,
      addInteger_eq, subtractInteger_eq, multiplyInteger_eq] at $h:ident)
  let d ← `(tactic| dsimp only [PlutusCore.Integer.Integer] at $h:ident)
  -- `mkSimpContext` works on the main goal (any goal does: the lemmas are constants)
  let gs ← getGoals
  setGoals [g]
  let (rs, rd) ← try
      pure (← mkSimpContext s (eraseLocal := false),
        ← mkSimpContext d (eraseLocal := false) (kind := .dsimp))
    finally setGoals gs
  let c := (rs.ctx, rs.simprocs, rd.ctx, rd.simprocs)
  if let some r := cache? then r.set (some c)
  return c

/-- `uplc_cond h` on `g`, without going through the tactic syntax: the same three steps
    (`try simp only […] at h`, `try dsimp only [Integer] at h`, `try have := Ne.symm h`) with
    the contexts of `condCtxs`. The goals left (none if `h` became `False`). -/
def uplcCond (g : MVarId) : TacticM (List MVarId) := do
  let (sctx, sprocs, dctx, dprocs) ← condCtxs g
  let hyp (g : MVarId) : MetaM FVarId := g.withContext do
    let some d := (← getLCtx).findFromUserName? `h | throwError "uplc_cond: no `h`"
    return d.fvarId
  let simpH (g : MVarId) : MetaM (Option MVarId) := do
    let h ← hyp g
    let (r, _) ← simpGoal g sctx sprocs none false #[h]
    return r.map (·.2)
  let dsimpH (g : MVarId) : MetaM (Option MVarId) := do
    let h ← hyp g
    let (r, _) ← dsimpGoal g dctx dprocs false #[h]
    return r
  let divModH (g : MVarId) : TacticM (Option MVarId) := do
    let h ← hyp g
    let ty ← g.withContext do instantiateMVars (← h.getType)
    unless (ty.find? fun e => e.isConstOf ``Int.fdiv || e.isConstOf ``Int.fmod).isSome do
      return some g
    let s ← `(tactic| simp (disch := decide) only [Int.fdiv_eq_ediv_of_nonneg, Int.fmod_eq_emod_of_nonneg] at $(mkIdent `h):ident)
    let gs ← getGoals
    setGoals [g]
    try
      let r ← mkSimpContext s (eraseLocal := false)
      let (res, _) ← r.dischargeWrapper.with fun d? => simpGoal g r.ctx r.simprocs d? false #[h]
      return res.map (·.2)
    finally setGoals gs
  let symmH (g : MVarId) : MetaM MVarId := g.withContext do
    let pf ← mkAppM ``Ne.symm #[mkFVar (← hyp g)]
    let g' ← g.assert `this (← inferType pf) pf
    return (← g'.intro1P).2
  let mut g := g
  match ← observing? (simpH g) with
  | some none => return []
  | some (some g') => g := g'
  | none => pure ()
  -- Aiken's `/` and `%` (floor) by a positive literal: the Euclidean ones, which `omega` reads
  match ← observing? (divModH g) with
  | some none => return []
  | some (some g') => g := g'
  | none => pure ()
  match ← observing? (dsimpH g) with
  | some none => return []
  | some (some g') => g := g'
  | none => pure ()
  if let some g' ← observing? (symmH g) then g := g'
  return [g]

/-- `uplc_cond h`: natively (`uplcCond`, option `uplc.nativeCond`) or by the macro. -/
def runCond (g : MVarId) : TacticM (List MVarId) := do
  if uplc.nativeCond.get (← getOptions) then uplcCond g
  else Tactic.run g (evalTactic (← `(tactic| uplc_cond $(mkIdent `h))))

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
  /-- Aux mode: runs shared by statement (`Sym.sharedRun`), the native `uplc_cond`
      (`runCond`), splits by `bool_split`, the cheap refutations first, and a branch
      as an auxiliary theorem (`withAuxLemma`, with `uplc.auxLemmas` 2). -/
  aux : Bool := false
  /-- Splits of symbolic values by their constructors on this path (`stuckDiscr?`): bounded,
      because a list of any length would split forever. -/
  caseSplits : Nat := 0

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

/-- How many times one path may split a symbolic value by its constructors (`Ctx.caseSplits`). -/
def maxCaseSplits : Nat := 24

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

/-- A hypothesis set aside for the end of a run: `clean` drops it, so the refutations and the
    equation checks at every branch never read it, and a leaf closer takes it back.
    `Deferred p` is `p`. Measured (Kreisel's Aiken workshop, 2026-10-09): a contract's
    statement in context cost two `simp_all` (~0.6 s) at each of ~120 branches. -/
def Deferred (p : Prop) : Prop := p

/-- `g` without the hypotheses about CEK runs (the loop invariants, and claims
    `Halts`/`Fails` about other runs): they hold whole states or programs, and
    `simp` has no use for them; and without the deferred ones (`Deferred`). -/
def clean (g : MVarId) : MetaM MVarId := g.withContext do
  let runs ← (← getLCtx).getFVarIds.filterM fun x => do
    let ty ← instantiateMVars (← x.getType)
    return ty.getForallBody.isAppOf ``Reaches || ty.isAppOf ``Deferred ||
      (ty.find? fun e => e.isConstOf ``Halts || e.isConstOf ``Fails).isSome
  g.tryClearMany runs

/-- Runs `tac` on `g` (cleaned); succeeds if it closes `g` without `sorry`. -/
def closes (g : MVarId) (tac : Syntax) : TacticM Bool := do
  let r ← observing? do
    -- `withoutRecover`: a failing tactic must fail, not log an error and admit the goal
    let [] ← Tactic.run (← clean g) (withoutRecover (evalTactic tac)) | failure
    if (← instantiateMVars (mkMVar g)).hasSorry then failure
  return r.isSome

/-- A proof of `lhs = rhs`, by defeq or `uplc_eq`, if one is found: `uplc_eq_core`
    without the hypotheses, then with them, and only then `uplc_eq_grind` (which reads the
    hypotheses by itself, and whose proofs use `Classical.choice`). -/
private def proveEq (ctx : Ctx) (lhs rhs : Expr) : TacticM (Option Expr) := do
  if ← withNewMCtxDepth (isDefEq lhs rhs) then
    return some (← mkEqRefl lhs)
  let g ← mkFreshExprMVar (← mkEq lhs rhs)
  -- without the hypotheses first: rewriting with them can make a goal harder
  let tss := if ctx.path.isEmpty then #[ctx.ts] else #[ctx.ts, ctx.simpArgs]
  for ts in tss do
    if ← closes g.mvarId! (← `(tactic| uplc_eq_core [$ts,*])) then
      return some (← instantiateMVars g)
  for ts in tss do
    if ← closes g.mvarId! (← `(tactic| uplc_eq_grind [$ts,*])) then
      return some (← instantiateMVars g)
  return none

/-- The cases `c = false` and `c = true` of the goal `g` (in this order, as `cases`
    gives them), with the hypothesis `h : c = b` introduced and `c` replaced by `b` in the
    target. The same as `generalize h : c = b; cases b`, without `kabstract` and the type
    check of the new target, which traverse the whole (large) state as a tree: here the
    motive is built by `Expr.replace` (shared subterms visited once), and the kernel checks
    it when it checks `bool_split`. -/
def splitBool (g : MVarId) (c : Expr) : MetaM (List MVarId) := g.withContext do
  let tgt ← instantiateMVars (← g.getType)
  let boolTy := mkConst ``Bool
  let P ← withLocalDeclD `b boolTy fun b => do
    mkLambdaFVars #[b] (tgt.replace fun e => if e == c then some b else none)
  let tag ← g.getTag
  let goal (v : Name) : MetaM Expr := do
    let bv := mkConst v
    mkFreshExprSyntheticOpaqueMVar
      (mkForall `h .default (mkApp3 (mkConst ``Eq [levelOne]) boolTy c bv) (P.beta #[bv])) tag
  let mf ← goal ``Bool.false
  let mt ← goal ``Bool.true
  g.assign (mkApp4 (mkConst ``bool_split) c P mf mt)
  let (_, gf) ← mf.mvarId!.intro `h
  let (_, gt) ← mt.mvarId!.intro `h
  return [gf, gt]

/-- `splitBool`, or `generalize h : c = b; cases b` (option `uplc.splitBool` off). -/
def splitCond (g : MVarId) (c : Expr) : MetaM (List MVarId) := do
  if uplc.splitBool.get (← getOptions) then return ← splitBool g c
  let (fvars, gb) ← g.generalize #[{ expr := c, xName? := `b, hName? := `h }]
  return (← gb.cases fvars[0]!).toList.map (·.mvarId)

/-- A hypothesis that is linear arithmetic over `Int`/`Nat` only (`omega`'s). -/
def isArith (ty : Expr) : MetaM Bool := do
  let ty := ty.consumeMData
  let ty := if ty.isAppOfArity ``Not 1 then ty.appArg! else ty
  let num (α : Expr) : MetaM Bool := do
    let α ← whnfR α
    return α.isConstOf ``Int || α.isConstOf ``Nat
  if ty.isAppOfArity ``Eq 3 || ty.isAppOfArity ``Ne 3 then return ← num (ty.getArg! 0)
  if ty.isAppOfArity ``LE.le 4 || ty.isAppOfArity ``LT.lt 4 then return ← num (ty.getArg! 0)
  return false

/-- Clears the arithmetic hypotheses of the main goal (see `isArith`). -/
elab "clear_arith" : tactic => do
  let g ← getMainGoal
  g.withContext do
    let hs ← (← getLCtx).getFVarIds.filterM fun x => do isArith (← instantiateMVars (← x.getType))
    replaceMainGoal [← g.tryClearMany hs]

/-- Two hypotheses `p : P` and `n : ¬ P` (or `n : a ≠ b` with `p : a = b`), found by
    comparing their types: the proof `n p` of `False`. -/
def complementary? (g : MVarId) : MetaM (Option Expr) := g.withContext do
  let mut pos : Std.HashMap Expr FVarId := {}
  let mut negs : Array (Expr × FVarId) := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty := (← instantiateMVars d.type).consumeMData
    if ty.isAppOfArity ``Not 1 then
      negs := negs.push (ty.appArg!.consumeMData, d.fvarId)
    else if ty.isAppOfArity ``Ne 3 then
      let eq := mkApp3 (mkConst ``Eq ty.getAppFn.constLevels!) (ty.getArg! 0) (ty.getArg! 1) (ty.getArg! 2)
      negs := negs.push (eq, d.fvarId)
    else
      pos := pos.insert ty d.fvarId
  for (p, n) in negs do
    if let some h := pos.get? p then return some (mkApp (mkFVar n) (mkFVar h))
  return none

/-- The hypothesis `h` (the last one of that name) says nothing new: another hypothesis
    has the same type. -/
def knownHyp (g : MVarId) (h : Name) : MetaM Bool := g.withContext do
  let some d := (← getLCtx).findFromUserName? h | return false
  let ty := (← instantiateMVars d.type).consumeMData
  if ty.isConstOf ``True then return true
  for d' in ← getLCtx do
    if d'.isImplementationDetail || d'.fvarId == d.fvarId then continue
    if (← instantiateMVars d'.type).consumeMData == ty then return true
  return false

/-- `complementary?`/`knownHyp` are on (option `uplc.quickRefute`). -/
def quickRefute {m : Type → Type} [Monad m] [MonadOptions m] : m Bool :=
  return uplc.quickRefute.get (← getOptions)

/-- A comparison of numbers (`Int`/`Nat`, through `abbrev`s), maybe negated: a branch condition
    that `omega` decides with the facts it reads, so `simp_all` adds nothing at the branch. -/
def numericFact (t : Expr) : MetaM Bool := do
  let t ← instantiateMVars t
  let t := if t.isAppOfArity ``Not 1 then t.appArg! else t
  let num (α : Expr) : MetaM Bool := do
    let α ← whnfR α
    return α.isConstOf ``Int || α.isConstOf ``Nat
  if t.isAppOfArity ``Eq 3 || t.isAppOfArity ``Ne 3 then num (t.getArg! 0)
  else if t.isAppOfArity ``LE.le 4 || t.isAppOfArity ``LT.lt 4 then num (t.getArg! 0)
  else return false

/-- Whether `omega` may read a hypothesis of type `t` (its `whnfR`, as `omega`'s `addFact`
    takes it). `false` only where `omega`'s frontend (Lean 4.24,
    `Lean.Elab.Tactic.Omega.Frontend`, `addFact`/`pushNot`) provably drops the fact: a
    non-arrow `∀`, an (in)equality over a type that is not `Int`/`Nat`/`Fin` (even after
    `whnf`), a negation `pushNot` gives up on, any other head. When in doubt, `true`. -/
partial def omegaReads (t : Expr) : MetaM Bool := do
  let num (α : Expr) (fin : Bool) : MetaM Bool := do
    let α ← whnf α
    return α.isConstOf ``Int || α.isConstOf ``Nat || (fin && α.isAppOf ``Fin)
  match t with
  | .forallE .. => return t.isArrow
  | .app .. =>
    let some c := t.getAppFn.constName? | return true
    let args := t.getAppArgs
    if c == ``Eq && args.size == 3 then return ← num args[0]! true
    if (c == ``LE.le || c == ``LT.lt || c == ``GT.gt || c == ``GE.ge) && args.size == 4 then
      return ← num args[0]! true
    if c == ``Ne && args.size == 3 then return ← num args[0]! false
    if c == ``Not && args.size == 1 then
      let p ← whnfR args[0]!
      match p with
      | .forallE .. => return true
      | .app .. =>
        let some c' := p.getAppFn.constName? | return true
        let pa := p.getAppArgs
        if (c' == ``LT.lt || c' == ``LE.le) && pa.size == 4 then return ← num pa[0]! true
        if c' == ``Eq && pa.size == 3 then return ← num pa[0]! true
        if c' == ``Dvd.dvd && pa.size == 4 then return ← num pa[0]! false
        return [``Prod.Lex, ``Not, ``And, ``Or, ``Iff].contains c'
      | _ => return false
    return [``Dvd.dvd, ``Prod.Lex, ``And, ``Exists, ``Subtype, ``Iff, ``Or].contains c
  | .mdata _ e => omegaReads e
  | _ => return false

/-- What `omega` reads in `g`'s context: the types of the hypotheses it may take, in order
    (`omegaReads`). The same facts give the same outcome: `omega` is deterministic. -/
def omegaFacts (g : MVarId) : MetaM (Array Expr) := g.withContext do
  let heads := [``Eq, ``LE.le, ``LT.lt, ``GT.gt, ``GE.ge, ``Ne, ``Not, ``Dvd.dvd, ``Prod.Lex,
    ``And, ``Exists, ``Subtype, ``Iff, ``Or]
  let env ← getEnv
  let mut out := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let t0 := d.type.consumeMData
    -- a head that is neither one `omega` reads nor reducible (so `whnfR` keeps it): dropped
    -- without computing `whnfR` (the hypotheses about runs hold whole states)
    if let some c := t0.getAppFn.constName? then
      unless heads.contains c || getReducibilityStatusCore env c == .reducible do continue
    -- the key holds the type as it is (equal types are read, and cleaned, alike)
    let ty ← instantiateMVars d.type
    if ← omegaReads (← whnfR ty) then out := out.push ty
  return out

/-- The types of `g`'s hypotheses, in order: what `simp_all` works on. -/
def hypTypes (g : MVarId) : MetaM (Array Expr) := g.withContext do
  let mut out := #[]
  for d in ← getLCtx do
    unless d.isImplementationDetail do out := out.push (← instantiateMVars d.type)
  return out

/-- The session's records of `omega` and `simp_all` failures, when `uplc.omegaMemo`
    (resp. `uplc.simpMemo`) is on; `none` with both off or no session. -/
def refuteMemo? : MetaM (Option (Option (IO.Ref (Std.HashSet (Array Expr))) ×
    Option (IO.Ref (Std.HashSet (Array Expr))))) := do
  let o := uplc.omegaMemo.get (← getOptions)
  let si := uplc.simpMemo.get (← getOptions)
  unless o || si do return none
  let some ses ← session? | return none
  return some (if o then some ses.omegaFails else none, if si then some ses.simpFails else none)

/-- Runs `tac` on `g0` (already cleaned); succeeds if it closes `g0` without `sorry`: the
    same as `closes` on the goal `g0` was cleaned from. -/
def closesOn (g0 : MVarId) (tac : Syntax) : TacticM Bool := do
  let r ← observing? do
    let [] ← Tactic.run g0 (withoutRecover (evalTactic tac)) | failure
    if (← instantiateMVars (mkMVar g0)).hasSorry then failure
  return r.isSome

/-- A proof of `False` from a cycle of `≤`/`<` between byte strings with a strict step, among
    `g`'s hypotheses (`a ≤ b`, `a < b`, their negations, `a = b`): the order is linear, so a
    sorted list's branches (`l8 < l11`, `l11 < l14`, `l14 ≤ l8`) close without `simp_all`. -/
def byteOrderContra? (g : MVarId) : MetaM (Option Expr) := g.withContext do
  let isBytes (t : Expr) : MetaM Bool := do
    let t ← whnfR t
    return t.isConstOf ``PlutusCore.ByteString.PlutusCore.ByteStringInternal.ByteString
  -- edges `u → v` (`u ≤ v`, or `u < v` when strict), with their proofs
  let mut edges : Array (Expr × Expr × Bool × Expr) := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let t ← instantiateMVars d.type
    let h := mkFVar d.fvarId
    let (neg, p) := if t.isAppOfArity ``Not 1 then (true, t.appArg!) else (false, t)
    if p.isAppOfArity ``LE.le 4 || p.isAppOfArity ``LT.lt 4 then
      unless ← isBytes (p.getArg! 0) do continue
      let u := p.getArg! 2
      let v := p.getArg! 3
      let le := p.isAppOfArity ``LE.le 4
      if !neg then edges := edges.push (u, v, !le, h)
      else if le then edges := edges.push (v, u, true, ← mkAppM ``ByteOrder.lt_of_not_le #[h])
      else edges := edges.push (v, u, false, ← mkAppM ``ByteOrder.le_of_not_lt #[h])
    else if !neg && p.isAppOfArity ``Eq 3 then
      unless ← isBytes (p.getArg! 0) do continue
      let u := p.getArg! 1
      let v := p.getArg! 2
      edges := edges.push (u, v, false, ← mkAppM ``ByteOrder.le_of_eq #[h])
      edges := edges.push (v, u, false, ← mkAppM ``ByteOrder.ge_of_eq #[h])
  unless edges.any (·.2.2.1) do return none
  -- for each strict edge `u < v`, a path `v →* u` (breadth first) closes the cycle
  for (u, v, strict, p) in edges do
    unless strict do continue
    let mut prev : Std.HashMap Expr (Option Nat) := {}
    prev := prev.insert v none
    let mut queue := #[v]
    let mut i := 0
    while i < queue.size && !prev.contains u do
      let w := queue[i]!
      i := i + 1
      for k in [0:edges.size] do
        let (a, b, _, _) := edges[k]!
        if a == w && !prev.contains b then
          prev := prev.insert b (some k)
          queue := queue.push b
    unless prev.contains u do continue
    -- the path, from `v` to `u`, edge by edge
    let mut path := #[]
    let mut x := u
    while x != v do
      let some (some k) := prev.get? x | break
      path := path.push k
      x := edges[k]!.1
    -- `v ≤ u` (or `<`), composed along the path
    let mut acc ← mkAppM ``ByteOrder.le_refl #[v]
    let mut accStrict := false
    for k in path.reverse do
      let (_, _, s, q) := edges[k]!
      acc ← match accStrict, s with
        | false, false => mkAppM ``ByteOrder.le_trans #[acc, q]
        | false, true => mkAppM ``ByteOrder.lt_of_le_of_lt #[acc, q]
        | true, false => mkAppM ``ByteOrder.lt_of_lt_of_le #[acc, q]
        | true, true => mkAppM ``ByteOrder.lt_trans #[acc, q]
      accStrict := accStrict || s
    let self ← if accStrict then mkAppM ``ByteOrder.lt_trans #[p, acc]
      else mkAppM ``ByteOrder.lt_of_lt_of_le #[p, acc]
    return some (← mkAppM ``ByteOrder.false_of_lt_self #[self])
  return none

/-- `omega` on `r` with the hypotheses `hidden` added back (those whose variables `r` still
    has); assigns `r` if it closes. Not tried when the facts `omega` would read are among
    `known` (it failed on those), nor on facts it already failed on in this session. -/
private def omegaWithBack (r : MVarId) (hidden : Array LocalDecl) (known : Std.HashSet Expr) :
    TacticM Bool := do
  let decl ← r.getDecl
  let mut lctx := decl.lctx
  let mut added := false
  for d in hidden do
    let ty ← instantiateMVars d.type
    if lctx.contains d.fvarId || ty.hasAnyFVar (!lctx.contains ·) then continue
    lctx := lctx.mkLocalDecl d.fvarId d.userName ty d.binderInfo
    added := true
  unless added do return false
  let r2 ← mkFreshExprMVarAt lctx decl.localInstances decl.type .syntheticOpaque decl.userName
  let facts ← omegaFacts r2.mvarId!
  if facts.all known.contains then return false
  let memo := (← refuteMemo?).bind (·.1)
  if let some fails := memo then
    if (← fails.get).contains facts then return false
  let ok ← timed "refute.arith-back" <| observing? do
    let [] ← Tactic.run r2.mvarId! (withoutRecover (evalTactic (← `(tactic| omega)))) | failure
  unless ok.isSome do
    if let some fails := memo then fails.modify (·.insert facts)
    return false
  r.assign r2
  return true

/-- For `refute`, after `omega` failed on the goal: `t` without the arithmetic hypotheses
    (`clear_arith`: `simp_all` can loop on `0 = x`), then `omega` with them back on each goal
    `t` leaves, where `t` brought a fact `omega` reads (`¬ i = j`, from `¬ (s = t ∧ i = j)` and
    `s = t`, against `i = j`). The goals `omega` does not close stay, as `t` left them. -/
elab "hiding_arith " t:tactic : tactic => do
  let g ← getMainGoal
  let (hidden, known, g1) ← g.withContext do
    let lctx ← getLCtx
    let hs ← lctx.getFVarIds.filterM fun x => do isArith (← instantiateMVars (← x.getType))
    let g1 ← g.tryClearMany hs
    let lctx1 := (← g1.getDecl).lctx
    let known := Std.HashSet.ofArray (← omegaFacts g)
    return (hs.filterMap fun x => if lctx1.contains x then none else lctx.find? x, known, g1)
  replaceMainGoal [g1]
  evalTactic t
  if hidden.isEmpty then return
  let rest ← (← getGoals).filterM fun r => do
    if ← r.isAssigned then return false
    return !(← omegaWithBack r hidden known)
  setGoals rest

/-- Closes `g` if its hypotheses are contradictory: the branch cannot happen. -/
def refute (ctx : Ctx) (g : MVarId) (full := true) (simp := true) : TacticM Bool := g.withContext do
  if ctx.aux && (← quickRefute) then
    if let some pf ← timed "refute.complementary" (complementary? g) then
      g.assign (← mkFalseElim (← g.getType) pf)
      return true
    unless full do return false
  -- a cycle in the order of byte strings (cheap: a search among the hypotheses)
  if let some pf ← timed "refute.order" (byteOrderContra? g) then
    g.assign (← mkFalseElim (← g.getType) pf)
    return true
  let f ← mkFreshExprMVar (mkConst ``False)
  let ts : Syntax.TSepArray [``Lean.Parser.Tactic.simpErase, ``Lean.Parser.Tactic.simpLemma] "," :=
    ⟨ctx.ts.elemsAndSeps⟩
  let ok ← if let some (oMemo, sMemo) ← refuteMemo? then do
    -- the same `first` as below, on the goal cleaned once; each alternative is skipped where
    -- it already failed on the same hypotheses (`omega` on the facts it reads, `simp_all` on
    -- the whole cleaned context): both are deterministic, so it would fail again
    let g0 ← clean f.mvarId!
    let omegaTac ← `(tactic| omega)
    let okO ← match oMemo with
      | none => timed "refute.omega" (closesOn g0 omegaTac)
      | some fails => do
        let key ← timed "refute.omega.facts" (omegaFacts g0)
        if (← fails.get).contains key then
          if ← perfEnabled then perfAdd "refute.omega.memo-hit" 0
          pure false
        else
          let r ← timed "refute.omega" (closesOn g0 omegaTac)
          unless r do fails.modify (·.insert key)
          pure r
    if okO then pure true
    else if !simp then pure false
    else
      -- without the arithmetic first (`omega` had them; `simp_all` can loop on `0 = x`), and
      -- `omega` with them on what is left (`hiding_arith`); with them only if that fails to
      -- run. A goal left open is a failure: a second `simp_all` with the arithmetic on it
      -- rarely closes one, and costs several times the first on large contexts
      let simpTac ← `(tactic| first
        | hiding_arith ((try simp [$ts,*] at *) <;> simp_all [$ts,*])
        | simp_all [$ts,*])
      match sMemo with
      | none => timed "refute.simp" (closesOn g0 simpTac)
      | some fails => do
        let key ← timed "refute.simp.hyps" (hypTypes g0)
        if (← fails.get).contains key then
          if ← perfEnabled then perfAdd "refute.simp.memo-hit" 0
          pure false
        else
          let r ← timed "refute.simp" (closesOn g0 simpTac)
          unless r do fails.modify (·.insert key)
          pure r
  else if ← perfEnabled then do
    -- the same as the `first` below, one alternative at a time, to see which one closes
    let alts := #[("refute.omega", ← `(tactic| omega)),
      ("refute.simp_all.1", ← `(tactic| hiding_arith ((try simp [$ts,*] at *) <;> simp_all [$ts,*]))),
      ("refute.simp_all.2", ← `(tactic| simp_all [$ts,*]))]
    let mut ok := false
    let g0 ← clean f.mvarId!
    let alts := if simp then alts else alts.take 1
    for (k, tac) in alts do
      let s ← saveState
      let t0 ← IO.monoNanosNow
      let r ← observing? (Tactic.run g0 (withoutRecover (evalTactic tac)))
      let closed := match r with | some [] => true | _ => false
      perfAdd (k ++ (if closed then ".closes" else if r.isSome then ".open" else ".fails"))
        ((← IO.monoNanosNow) - t0)
      if k == "refute.simp_all.1" && uplc.perfDump.get (← getOptions) then
        let hs ← g0.withContext do
          let lctx ← getLCtx
          let ps ← lctx.foldlM (init := #[]) fun acc d => do
            if d.isImplementationDetail then return acc
            if ← isProp d.type then return acc.push m!"{d.userName} : {d.type}" else return acc
          return ps
        IO.eprintln s!"[refute {if closed then "closes" else if r.isSome then "open" else "fails"} {((← IO.monoNanosNow) - t0) / 1000000} ms]"
        for m in hs do IO.eprintln s!"   {← m.toString}"
      if r.isNone then
        s.restore
        continue
      ok := closed && !(← instantiateMVars f).hasSorry
      unless ok do s.restore
      break
    pure ok
  else if !simp then
    timed "refute" (closes f.mvarId! (← `(tactic| omega)))
  else
    timed "refute" (closes f.mvarId! (← `(tactic| first
      | omega
      | hiding_arith ((try simp [$ts,*] at *) <;> simp_all [$ts,*])
      | simp_all [$ts,*])))
  unless ok do return false
  g.assign (← mkFalseElim (← g.getType) f)
  return true

/-- Proves `g` with `tac`, on a fresh goal of the same type, and states that proof as
    an auxiliary theorem (closed over the free variables it uses), which then closes `g`.
    The kernel checks each auxiliary theorem on its own (in the background when
    `Elab.async` is on, as with `lean` on the command line): the caches of one check are
    freed before the next, and the checks run while the tactic goes on. The metavariable
    assignments made by `tac` are dropped once its proof is a closed term. Only when the
    option `uplc.auxLemmas` is at least `level`. -/
def withAuxLemma (g : MVarId) (tac : MVarId → TacticM Bool) (level := 2) : TacticM Bool :=
    g.withContext do
  if uplc.auxLemmas.get (← getOptions) < level then return ← tac g
  let mctx0 ← getMCtx
  let ty ← instantiateMVars (← g.getType)
  let g2 ← mkFreshExprSyntheticOpaqueMVar ty (← g.getTag)
  unless ← tac g2.mvarId! do return false
  let pf ← timed "aux.instantiate" (instantiateMVars g2)
  if pf.hasExprMVar || pf.hasSorry || ty.hasExprMVar then
    g.assign pf
    return true
  -- `zetaDelta := true`: no `Meta.check` of the proof (it would re-run every step); the
  -- kernel checks it
  let aux ← timed "aux.add" (mkAuxTheorem ty pf (zetaDelta := true))
  setMCtx mctx0
  g.assign aux
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
  -- with no induction and a final target, the run stops only where `runUntil` does:
  -- it is the same run in every branch that gets here (shared, see `runToEnd`)
  let shared := ctx.aux && ctx.candidates.isEmpty && ctx.gen?.isNone &&
    (isHalt T || isError T)
  -- the starting state may be a loop head itself (the invariant starts there)
  let stop ← timed "drive.run" <| if shared then runToEnd cache st maxSteps else runUntil cache st
    (fun s => do
      if isTarget s then return true
      if s == st then return false
      return (← timed "drive.loophead" (inductionLoop? s)).isSome) maxSteps
  let st' := stop.state
  let mut g := g
  if shared && !stop.segments.isEmpty then
    -- `Reaches st' T → Reaches st T`, once for all the branches that run from `st`
    let reaches (x : Expr) := mkApp2 (mkConst ``Reaches) x T
    let imp ← sharedRun (mkForall `h .default (reaches st') (reaches st)) stop.steps
      (withLocalDeclD `h (reaches st') fun h => do
        let states := #[st] ++ stop.segments.map (·.1)
        let segs ← stop.proofs st
        let mut pf := h
        for i in (List.range segs.size).reverse do
          let (b, c, hb) := segs[i]!
          pf := mkAppN (mkConst ``Reaches.of_exec) #[states[i]!, b, T, mkNatLit c, hb, pf]
        mkLambdaFVars #[h] pf)
    let g' ← mkFreshExprSyntheticOpaqueMVar (reaches st')
    g.assign (mkApp imp g')
    g := g'.mvarId!
  else
    let mut a := st
    for (b, c, hb) in ← stop.proofs st do
      let g' ← mkFreshExprSyntheticOpaqueMVar (mkApp2 (mkConst ``Reaches) b T)
      g.assign (mkAppN (mkConst ``Reaches.of_exec) #[a, b, T, mkNatLit c, hb, g'])
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
    if let some n := ctx.split? then
      if (findOutsideEnv? (· == n) (c?.getD focus)).isSome then
        let ctx ← ctx.deeper
        for sg in ← g.cases n.fvarId! do
          sg.mvarId.withContext do
            let recFields ← sg.fields.filterM fun x => do isDefEq (← inferType x) ctx.τ
            -- the candidates of before go on, substituted: after two splits (`n = j + 2`), the loop
            -- argument can still be `↑n` itself, now `↑(j + 2)`
            let olds := ctx.candidates.map sg.subst.apply
            let olds := if olds.contains (sg.subst.apply n) then olds else olds.push (sg.subst.apply n)
            drive { ctx with split? := if ctx.splits > 1 then recFields[0]? else none,
                             splits := ctx.splits - 1, invariants := #[],
                             path := ctx.path.map sg.subst.apply,
                             candidates := recFields ++ olds,
                             phase := s!"{ctx.phase}, case {sg.ctorName}" } sg.mvarId
        return
    -- a `match` on a symbolic value (a `Data` leaf the fuzzer reader did not open): one case per
    -- constructor, the run goes on in each
    if c?.isNone then
      let x? ← match stuckDiscr? (← getEnv) focus <|> stuckDiscr? (← getEnv) st' with
        | some x => pure (some x)
        | none => do
          -- or a variable the condition of a Lean `if` waits on (`chooseList` on a free list)
          if let some x ← stuckIteVar? focus then pure (some x) else stuckIteVar? st'
      if let some x := x? then
        if ctx.caseSplits ≥ maxCaseSplits then
          throwShort m!"{ctx.at}: symbolic execution split a symbolic value {maxCaseSplits} times on \
            this path (a list of any length?); the machine is at{indentExpr st'}"
        let xName ← x.getUserName
        for sg in ← timed "drive.cases" (g.cases x) do
          let ctx' := { ctx with caseSplits := ctx.caseSplits + 1,
                                 path := ctx.path.map sg.subst.apply,
                                 phase := s!"{ctx.phase}, {xName.eraseMacroScopes} is {sg.ctorName.componentsRev.head!}" }
          -- a case the hypotheses contradict closes at once
          if ← refute ctx' sg.mvarId then continue
          if ctx.aux then
            discard <| withAuxLemma sg.mvarId fun g' => do drive ctx' g'; return true
          else
            drive ctx' sg.mvarId
        return
    let some c := c? | throwShort m!"{ctx.at}: symbolic execution is stuck: reduction cannot \
      decide the next step, and it is not a branch on a condition. The machine is at{indentExpr st'}"
    let ctx ← ctx.deeper
    let branches ← if ctx.aux then timed "drive.split" (splitCond g c) else do
      let (fvars, gb) ← timed "drive.generalize" (g.generalize #[{ expr := c, xName? := `b, hName? := `h }])
      pure ((← timed "drive.cases" (gb.cases fvars[0]!)).toList.map (·.mvarId))
    for sg in branches do
      let conds ← timed "drive.cond" do
        if ctx.aux then runCond sg
        else Tactic.run sg (evalTactic (← `(tactic| uplc_cond $(mkIdent `h))))
      for gc in conds do
        gc.withContext do
          let hTy := (← getLocalDeclFromUserName `h).type
          -- a branch that contradicts the hypotheses is closed at once (a branch whose
          -- condition is already a hypothesis only by `complementary?`: it adds nothing)
          let known ← if ctx.aux && (← quickRefute) then knownHyp gc `h else pure false
          let numeric ← if ctx.aux && !uplc.branchSimp.get (← getOptions) then numericFact hTy
            else pure false
          unless ← refute ctx gc (full := !known) (simp := !numeric) do
            let ctx' := { ctx with path := if hTy.isConstOf ``True then ctx.path else ctx.path.push hTy }
            if ctx.aux then
              discard <| withAuxLemma gc fun gc => do drive ctx' gc; return true
            else
              drive ctx' gc
  else if isTarget st' then
    if let some h ← timed "proveEq" (proveEq ctx st' T) then
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
    everything except instances, `match` auxiliaries (simp reduces those itself),
    definitions by well-founded recursion (their unfolding equation `f x = … f y …`
    loops in `simp`; pass the equations of each branch, `f_of_c (h : c) : f x = …`,
    as lemmas instead) and definitions from these libraries. -/
def specDefs (e : Expr) : MetaM (Array Syntax) := do
  let env ← getEnv
  let library := [`Init, `Lean, `Std, `Batteries, `Mathlib, `PlutusCore, `CardanoLedgerApi,
    `UplcProof]
  e.getUsedConstants.filterMapM fun c => do
    let some (.defnInfo _) := env.find? c | return none
    if (← isInstance c) || (← isMatcher c) then return none
    if (Lean.Elab.WF.eqnInfoExt.find? env c).isSome then return none
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

@[tactic uplcInductionTac] def evalUplcInduction : Tactic := fun stx => withSession <| withMainContext do
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
