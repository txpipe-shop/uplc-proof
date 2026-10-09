import PlutusCore.UPLC

/-!
# Composable CEK execution

The theory every proof produced by `uplc_induction` and `uplc_run` rests on.
Nothing here is specific to a script.

* `exec s n` runs at most `n` CEK steps and returns the state it reached.
  (`runSteps` turns fuel exhaustion into `Error`, so it cannot talk about the
  middle of a computation.)
* `Reaches A B`: the machine goes from `A` to `B` in finitely many steps.
  Proofs are chains of `Reaches.of_exec` (a fixed number of steps, checked by
  the kernel with `rfl`) and `Reaches.call` (a recursive call, by induction).
* `Halts p args v`: the user-facing statement. Trusting a theorem
  `Halts p args v` requires reading its one-line definition and trusting
  PlutusCore's `cekExecuteProgram`; nothing else in this file.
  `Fails p args`: no run halts with a value (a validator that rejects).
-/

open PlutusCore.UPLC.Term PlutusCore.UPLC.CekValue PlutusCore.UPLC.CekMachine

namespace UplcProof

/-! ## `exec`: run at most `n` steps -/

/-- Run at most `n` CEK steps. Unlike `runSteps`, running out of fuel returns
    the state reached instead of `Error`. -/
def exec : State → Nat → State
  | .Halt v, _ => .Halt v
  | .Error, _ => .Error
  | s, 0 => s
  | s, n + 1 => exec (step default s) n

theorem exec_halt (v : CekValue) (n : Nat) : exec (.Halt v) n = .Halt v := by cases n <;> rfl

theorem exec_error (n : Nat) : exec .Error n = .Error := by cases n <;> rfl

theorem exec_zero (s : State) : exec s 0 = s := by cases s <;> rfl

theorem exec_add (s : State) (m n : Nat) : exec s (m + n) = exec (exec s m) n := by
  induction m generalizing s with
  | zero => rw [Nat.zero_add, exec_zero]
  | succ m ih =>
    rw [Nat.add_right_comm]
    cases s with
    | Halt v => simp only [exec_halt]
    | Error => simp only [exec_error]
    | Eval st ρ t => exact ih _
    | Return st v => exact ih _

theorem runSteps_iff_exec (s : State) (n : Nat) (v : CekValue) :
    runSteps default s n = .Halt v ↔ exec s n = .Halt v := by
  induction n generalizing s with
  | zero => cases s <;> simp [runSteps, exec]
  | succ n ih => cases s <;> simp [runSteps, exec, ih]

theorem exec_halt_mono {s : State} {n m : Nat} {v : CekValue}
    (h : exec s n = .Halt v) (hle : n ≤ m) : exec s m = .Halt v := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
  rw [exec_add, h, exec_halt]

/-- The CEK machine is deterministic: two runs that halt give the same value. -/
theorem exec_halt_det {s : State} {n m : Nat} {v w : CekValue}
    (h₁ : exec s n = .Halt v) (h₂ : exec s m = .Halt w) : v = w := by
  rcases Nat.le_total n m with hle | hle
  · rw [exec_halt_mono h₁ hle] at h₂; cases h₂; rfl
  · rw [exec_halt_mono h₂ hle] at h₁; cases h₁; rfl

/-! ## `Reaches` -/

/-- The machine goes from `A` to `B` in finitely many steps. -/
def Reaches (A B : State) : Prop := ∃ n, exec A n = B

theorem Reaches.of_eq {A B : State} (h : A = B) : Reaches A B := ⟨0, (exec_zero A).trans h⟩

theorem Reaches.trans {A B C : State} (h₁ : Reaches A B) (h₂ : Reaches B C) : Reaches A C := by
  obtain ⟨n, hn⟩ := h₁
  obtain ⟨m, hm⟩ := h₂
  exact ⟨n + m, by rw [exec_add, hn, hm]⟩

/-- A fixed number of steps, then the rest of the run. -/
theorem Reaches.of_exec {A B C : State} (c : Nat) (h : exec A c = B) (h₂ : Reaches B C) :
    Reaches A C :=
  Reaches.trans ⟨c, h⟩ h₂

/-- A recursive call: the callee's run, provided its starting state is the
    current one up to an equation (typically on the argument). -/
theorem Reaches.call {A A' B C : State} (hA : A = A') (h₁ : Reaches A' B) (h₂ : Reaches B C) :
    Reaches A C :=
  Reaches.trans (hA ▸ h₁) h₂

/-- The current state rewritten (a closed `equalsData x y` replaced by its value),
    then the rest of the run. -/
theorem Reaches.of_eq_left {A A' C : State} (h : A = A') (r : Reaches A' C) : Reaches A C :=
  h ▸ r

/-! ## Programs -/

/-- The initial CEK state of `p` applied to `args`. -/
def initState (p : Program) (args : List Term) : State :=
  match p with
  | .Program _ body => initialState (applyParams body args)

theorem cekExecuteProgram_eq (p : Program) (args : List Term) (fuel : Nat) :
    cekExecuteProgram p args fuel = runSteps default (initState p args) fuel := by
  cases p; rfl

/-- `p` applied to `args` halts with value `v`, for some fuel. -/
def Halts (p : Program) (args : List Term) (v : CekValue) : Prop :=
  ∃ fuel, cekExecuteProgram p args fuel = .Halt v

theorem Halts.of_reaches {p : Program} {args : List Term} {v : CekValue}
    (h : Reaches (initState p args) (.Halt v)) : Halts p args v := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, by rw [cekExecuteProgram_eq, runSteps_iff_exec, hn]⟩

/-- Once halted, more fuel changes nothing: from some fuel on, the run halts with `v`. -/
theorem Halts.eventually {p : Program} {args : List Term} {v : CekValue} (h : Halts p args v) :
    ∃ N, ∀ fuel, N ≤ fuel → cekExecuteProgram p args fuel = .Halt v := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N, fun fuel hle => ?_⟩
  rw [cekExecuteProgram_eq, runSteps_iff_exec] at *
  exact exec_halt_mono hN hle

/-- Whatever the fuel, a run of `p` on `args` that halts, halts with `v`. -/
theorem Halts.unique {p : Program} {args : List Term} {v w : CekValue} {fuel : Nat}
    (h : Halts p args v) (hw : cekExecuteProgram p args fuel = .Halt w) : w = v := by
  obtain ⟨N, hN⟩ := h
  rw [cekExecuteProgram_eq, runSteps_iff_exec] at hN hw
  exact exec_halt_det hw hN

/-- `p` applied to `args` never halts with a value, whatever the fuel (a validator
    that rejects). -/
def Fails (p : Program) (args : List Term) : Prop :=
  ∀ fuel v, cekExecuteProgram p args fuel ≠ .Halt v

theorem Fails.of_reaches {p : Program} {args : List Term}
    (h : Reaches (initState p args) .Error) : Fails p args := by
  intro fuel v hv
  obtain ⟨n, hn⟩ := h
  rw [cekExecuteProgram_eq, runSteps_iff_exec] at hv
  rcases Nat.le_total n fuel with hle | hle
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
    rw [exec_add, hn, exec_error] at hv; cases hv
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
    rw [exec_add, hv, exec_halt] at hn; cases hn

/-! ## Running a claim forward, and refuting one

For leaf closers (`UplcProof.Tactic.Ctx.closer?`) that use hypotheses about other
runs (`Halts.reaches`, `Reaches.inv`), and for refuting a claim on a concrete
input: `UplcProof.Tactic.evalRun` gives the final state of the run, with a proof
of `Reaches (initState p args) final`. -/

/-- A `Halts` claim as a run from the initial state. -/
theorem Halts.reaches {p : Program} {args : List Term} {v : CekValue} (h : Halts p args v) :
    Reaches (initState p args) (.Halt v) := by
  obtain ⟨n, hn⟩ := h
  rw [cekExecuteProgram_eq, runSteps_iff_exec] at hn
  exact ⟨n, hn⟩

/-- A final state of the machine. -/
def Terminal : State → Prop
  | .Halt _ => True
  | .Error => True
  | _ => False

theorem exec_terminal {B : State} (hB : Terminal B) (n : Nat) : exec B n = B := by
  cases B with
  | Halt v => exact exec_halt v n
  | Error => exact exec_error n
  | Eval => exact hB.elim
  | Return => exact hB.elim

/-- If `A` reaches the final state `B`, so does any state `A` steps to. -/
theorem Reaches.inv {A A' B : State} (h : Reaches A B) (c : Nat) (hc : exec A c = A')
    (hB : Terminal B) : Reaches A' B := by
  obtain ⟨n, hn⟩ := h
  rcases Nat.le_total c n with hle | hle
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
    exact ⟨d, by rw [exec_add, hc] at hn; exact hn⟩
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
    rw [exec_add, hn, exec_terminal hB] at hc
    exact ⟨0, by rw [exec_zero]; exact hc.symm⟩

theorem Reaches.error_halt {v : CekValue} (h : Reaches .Error (.Halt v)) : False := by
  obtain ⟨n, hn⟩ := h
  rw [exec_error] at hn
  cases hn

theorem Reaches.halt_halt {v w : CekValue} (h : Reaches (.Halt v) (.Halt w)) : v = w := by
  obtain ⟨n, hn⟩ := h
  rw [exec_halt] at hn
  cases hn
  rfl

/-- Two runs of the same program that halt with `Data` agree. -/
theorem Halts.data_eq {p : Program} {args : List Term} {c c' : PlutusCore.Data.Data}
    (h : Halts p args (.VCon (.Data c))) (h' : Halts p args (.VCon (.Data c'))) : c = c' := by
  obtain ⟨n, hn⟩ := h
  have := h'.unique hn
  cases this
  rfl

/-- A run that halts with `w` does not halt with a different `v`. -/
theorem Halts.ne {p : Program} {args : List Term} {v w : CekValue}
    (h : Halts p args v) (h' : Halts p args w) (hne : v ≠ w) : False := by
  obtain ⟨n, hn⟩ := h
  exact hne (h'.unique hn)

/-- A run that fails does not halt. -/
theorem Fails.not_halts {p : Program} {args : List Term} {v : CekValue}
    (h : Fails p args) : ¬ Halts p args v := by
  rintro ⟨n, hn⟩
  exact h n v hn

/-- Refutation, when the run ends in `Error` (`evalRun` proves the premise). -/
theorem not_halts_of_reaches_error {p : Program} {args : List Term} {v : CekValue}
    (h : Reaches (initState p args) .Error) : ¬ Halts p args v :=
  (Fails.of_reaches h).not_halts

/-- Refutation, when the run halts with another value (`evalRun` proves the first premise). -/
theorem not_halts_of_reaches_halt {p : Program} {args : List Term} {v w : CekValue}
    (h : Reaches (initState p args) (.Halt w)) (hne : v ≠ w) : ¬ Halts p args v :=
  fun hv => (Halts.of_reaches h).ne hv (Ne.symm hne)

end UplcProof
