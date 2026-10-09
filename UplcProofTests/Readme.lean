import UplcProof

/-!
# The README's examples, checked

Every Lean block of `README.md` is here verbatim. `#import_uplc` declares its name
at the root, whatever the namespace: the names here must differ from those of the
other test modules (`lake build UplcProofTests` fails otherwise).
-/

open UplcProof

namespace UplcProofTests.Readme

/-! ## 1. `uplc_induction`: factorial, for every input -/

#import_uplc factorialScript PlutusV3 single_cbor_hex "Tests/Induction/Scripts/factorial.hex"

def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

theorem factorial_halts (n : Nat) :
    Halts factorialScript.script [int n] (.VCon (.Integer (fact n))) := by
  uplc_induction n

/-- info: 'UplcProofTests.Readme.factorial_halts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms factorial_halts

/-! ## 2. `uplc_auto`: an Aiken property test about factorial -/

#import_uplc factorialProp PlutusV3 single_cbor_hex
  "Tests/Auto/Scripts/prop_factorial_positive.hex"

/-- What the script's loop computes, on the naturals. -/
def factorial : Nat → Int
  | 0 => 1
  | k + 1 => ((k + 1 : Nat) : Int) * factorial k

theorem factorial_pos (k : Nat) : 0 < factorial k := by
  induction k with
  | zero => decide
  | succ k ih => simp only [factorial]; exact Int.mul_pos (by omega) ih

theorem prop_factorial_positive : ∀ n : Int, Halts factorialProp.script [int n] vTrue := by
  uplc_auto [factorial_pos] (loop := fun k => .VCon (.Integer (factorial k))) (timeout := 30)

/-- info: 'UplcProofTests.Readme.prop_factorial_positive' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms prop_factorial_positive

/-! ## 3. `uplc_auto`: a validator, and its bug -/

set_option uplc.cex.timings false

#import_uplc vaultBugProp PlutusV3 single_cbor_hex
  "Tests/Auto/Scripts/prop_bug_accepts_only_up_to_cap.hex"

/--
error: UPLC-RESULT {"status":"refuted","kernel":true,"cex":{"cap":-1,"amount":0},"lean":{"cap":"-1","amount":"0"},"closer":"uplc_cex_closer","fuel":250}
Counterexample (refutation checked by the kernel, closer uplc_cex_closer):
  cap := -1
  amount := 0
Refutation:
example : ¬∀ (cap amount : Int), Halts vaultBugProp.script [int cap, int amount] vTrue := by
  refute_with -1, 0
-/
#guard_msgs in
example : ∀ (cap amount : Int), Halts vaultBugProp.script [int cap, int amount] vTrue := by
  uplc_auto

theorem vault_bug : ¬∀ (cap amount : Int), Halts vaultBugProp.script [int cap, int amount] vTrue := by
  refute_with -1, 0

/-- info: 'UplcProofTests.Readme.vault_bug' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms vault_bug

-- The same property of the vault without the bug is proved.
#import_uplc vaultProp PlutusV3 single_cbor_hex "Tests/Auto/Scripts/prop_accepts_only_up_to_cap.hex"

/-- info: UPLC-RESULT {"status":"proved","kernel":true,"method":"uplc_run","blaster":"valid","fuel":1000} -/
#guard_msgs in
theorem vault_accepts_only_up_to_cap :
    ∀ (cap amount : Int), Halts vaultProp.script [int cap, int amount] vTrue := by
  uplc_auto

/-- info: 'UplcProofTests.Readme.vault_accepts_only_up_to_cap' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms vault_accepts_only_up_to_cap

/-! ## 4. From one transaction to every reachable state -/

/-- A counter that starts at 1 and that every step increments stays positive. -/
theorem counter_stays_positive :
    ∀ s, Reachable (· = (1 : Int)) (fun s s' => s' = s + 1) s → 0 < s :=
  Reachable.invariant (fun _ h => by omega) (fun _ _ h h' => by omega)

/-- info: 'UplcProofTests.Readme.counter_stays_positive' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms counter_stays_positive

end UplcProofTests.Readme
