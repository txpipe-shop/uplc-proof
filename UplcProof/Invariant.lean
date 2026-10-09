/-!
# Invariants: from one transaction to every reachable state

A property test can only talk about one transaction: if the script's state
satisfies `Inv` and the validator accepts a transaction that moves it to `s'`,
then `s'` satisfies `Inv` (the step). `Reachable.invariant` lifts the step to
every state the script can reach from an initial one, through any number of
accepted transactions.
-/

namespace UplcProof

universe u

/-- The states reachable from one satisfying `init` by any number of `step`s. -/
inductive Reachable {σ : Type u} (init : σ → Prop) (step : σ → σ → Prop) : σ → Prop where
  | start {s : σ} : init s → Reachable init step s
  | next {s s' : σ} : Reachable init step s → step s s' → Reachable init step s'

/-- An invariant that holds initially and is preserved by every step holds in
    every reachable state. -/
theorem Reachable.invariant {σ : Type u} {init : σ → Prop} {step : σ → σ → Prop}
    {Inv : σ → Prop} (h₀ : ∀ s, init s → Inv s) (h₁ : ∀ s s', Inv s → step s s' → Inv s') :
    ∀ s, Reachable init step s → Inv s := by
  intro s h
  induction h with
  | start hs => exact h₀ _ hs
  | next _ hst ih => exact h₁ _ _ ih hst

end UplcProof
