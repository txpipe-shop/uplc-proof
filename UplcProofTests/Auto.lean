import UplcProof.Auto

/-!
# Tests: `uplc_auto` on Aiken property tests

The fixtures (`Tests/Auto/Scripts/`) are the body functions of property tests
written in Aiken (`Tests/Auto/aiken/`: `lib/math.ak`, `lib/owner.ak`,
`lib/lists.ak`, `validators/vault.ak`, `validators/vault_bug.ak`), exported by
`Tests/Auto/aiken/export.sh` (aiken v1.1.24, traces off): each takes the test's
inputs (`Int`, `Bool`, `ByteArray`, `List<Int>`) and returns the test's `Bool`; a
validator is called inside the body function (`vault.spend(…)`), so each claim is
about one script: the validator's handler as compiled into the test, which is not
the same UPLC program as the validator's script in `plutus.json`.
`factorial_acc.hex` is not a property test: it is a copy of
`Tests/Induction/Scripts/factorial_acc.hex` (a fixture of `UplcProofTests.Induction`,
aiken v1.1.21).

* proved, with kernel-checked proofs and clean axioms: the factorial property (an
  `Int` leaf, a loop, given a loop spec), the vault (a validator call),
  the owner property (`Bool` and `ByteArray` leaves), a list property (a `List`
  leaf), an accumulator (`generalizing`), leaves already introduced, a claim
  stated with a definition;
* refuted, with a counterexample whose refutation the kernel checked (and the
  refutation printed, pasted below as a theorem): the buggy factorial property,
  the buggy vault, the stranger property (`ByteArray` values), a `Fails` claim;
* must reject: the factorial property without its loop spec is not proved
  (`oracle`; with `maxHeartbeats 0`, `uplc_run` on its loop still stops), a false
  claim is not proved even without Blaster (`unknown`), a spurious counterexample
  (a run longer than the bound) is not reported as refuted, nor one that cannot be
  confirmed (`falsified`), a proof that uses an axiom is not accepted, goals of the
  wrong shape and unknown options are errors;
* the `UPLC-RESULT` line of each status, with timings on, is one JSON object with
  each key once (`#uplc_json`), for `uplc_auto`, `blaster_pretty` and
  `blaster_refute`.

`set_option uplc.cex.timings false`: no `"ms"` key, so the result lines are
deterministic. `#uplc_result sev "line" ("text")? in cmd` checks the first line of
the one `UPLC-RESULT` message of `cmd` (and that the message contains `text`): a
failure message goes on with the kernel stage's errors, whose wording belongs to
`uplc_induction` and `uplc_run`.
-/

open PlutusCore.UPLC.Term PlutusCore.UPLC.CekValue PlutusCore.UPLC.CekMachine
open PlutusCore.ByteString (ByteString)
open UplcProof

namespace UplcProofTests.Auto

/-! ## `#uplc_result` -/

open Lean Elab Command in
/-- `#uplc_result info|error "UPLC-RESULT {…}" ("text")? in cmd`: `cmd` logs exactly
    one message whose first line starts with `UPLC-RESULT`, with that severity and
    that first line (and containing `text`). The messages of `cmd` are dropped. -/
syntax (name := uplcResultCmd) "#uplc_result " ident str (str)? " in" ppLine command : command

open Lean Elab Command in
@[command_elab uplcResultCmd] def elabUplcResult : CommandElab := fun stx => do
  let sev := stx[1].getId
  let some expected := stx[2].isStrLit? | throwErrorAt stx[2] "expected a string"
  let contains? := if stx[3].getNumArgs > 0 then stx[3][0].isStrLit? else none
  let initMsgs ← modifyGet fun st => (st.messages, { st with messages := {} })
  withReader ({ · with snap? := none }) do
    elabCommandTopLevel stx[5]
  let msgs := (← get).messages ++
    (← get).snapshotTasks.foldl (· ++ ·.get.getAll.foldl (· ++ ·.diagnostics.msgLog) {}) {}
  modify fun st => { st with messages := initMsgs, snapshotTasks := #[] }
  let mut found : Array (MessageSeverity × String) := #[]
  for m in msgs.toList do
    let txt ← m.data.toString
    if txt.startsWith "UPLC-RESULT" then found := found.push (m.severity, txt)
  let sevOk (s : MessageSeverity) : Bool := match sev, s with
    | `info, .information | `error, .error => true
    | _, _ => false
  match found with
  | #[(s, txt)] =>
      let line := (txt.splitOn "\n").headD ""
      unless sevOk s && line == expected do
        logErrorAt stx m!"#uplc_result: expected ({sev}){indentD expected}\ngot \
          ({if s == .error then "error" else "info"}){indentD line}"
      if let some c := contains? then
        unless (txt.splitOn c).length > 1 do
          logErrorAt stx m!"#uplc_result: the message does not contain{indentD c}\nit is{indentD txt}"
  | _ =>
      logErrorAt stx m!"#uplc_result: expected one UPLC-RESULT message, got {found.size}:\
        {indentD (toString (found.map (·.2)))}"

-- it must reject: the wrong first line, the wrong severity, no `UPLC-RESULT` at all
/--
error: #uplc_result: expected (info)
  UPLC-RESULT {"status":"proved"}
got (error)
  UPLC-RESULT {"status":"error","kernel":false,"reason":"the goal is not a claim about a run of a script"}
-/
#guard_msgs in
#uplc_result info "UPLC-RESULT {\"status\":\"proved\"}" in
example : 1 + 1 = 2 := by uplc_auto

/--
error: #uplc_result: expected one UPLC-RESULT message, got 0:
  #[]
-/
#guard_msgs in
#uplc_result info "UPLC-RESULT {\"status\":\"proved\"}" in
example : 1 + 1 = 2 := by decide

/-! ## Fixtures -/

#import_uplc factorialPositive PlutusV3 single_cbor_hex
  "Tests/Auto/Scripts/prop_factorial_positive.hex"
#import_uplc factorialGreater PlutusV3 single_cbor_hex
  "Tests/Auto/Scripts/prop_factorial_greater.hex"
#import_uplc vaultCap PlutusV3 single_cbor_hex
  "Tests/Auto/Scripts/prop_accepts_only_up_to_cap.hex"
#import_uplc vaultCapBug PlutusV3 single_cbor_hex
  "Tests/Auto/Scripts/prop_bug_accepts_only_up_to_cap.hex"
#import_uplc ownerCanAlwaysSpend PlutusV3 single_cbor_hex
  "Tests/Auto/Scripts/prop_owner_can_always_spend.hex"
#import_uplc strangerCanNeverSpend PlutusV3 single_cbor_hex
  "Tests/Auto/Scripts/prop_stranger_can_never_spend.hex"
#import_uplc lengthNonNegative PlutusV3 single_cbor_hex
  "Tests/Auto/Scripts/prop_length_non_negative.hex"
#import_uplc factorialAcc PlutusV3 single_cbor_hex
  "Tests/Auto/Scripts/factorial_acc.hex"

def run (p : Program) (args : List Term) : State := cekExecuteProgram p args 100000

/-- The `Bool` a run halted with, if any. -/
def haltBool : State → Option Bool
  | .Halt (.VCon (.Bool b)) => some b
  | _ => none

-- sample runs: each body function returns the test's verdict
#guard haltBool (run factorialPositive.script [int 5]) == some true
#guard haltBool (run factorialPositive.script [int (-3)]) == some true
#guard haltBool (run factorialGreater.script [int 3]) == some true
#guard haltBool (run factorialGreater.script [int 2]) == some false
#guard haltBool (run vaultCap.script [int 10, int 10]) == some true
#guard haltBool (run vaultCap.script [int 10, int 11]) == some true
#guard haltBool (run vaultCapBug.script [int 10, int 11]) == some false
#guard haltBool (run ownerCanAlwaysSpend.script [bool false, bytes ⟨"k"⟩]) == some true
#guard haltBool (run strangerCanNeverSpend.script [bool false, bytes ⟨"a"⟩, bytes ⟨"b"⟩]) == some true
#guard haltBool (run strangerCanNeverSpend.script [bool true, bytes ⟨"a"⟩, bytes ⟨"b"⟩]) == some false
#guard haltBool (run lengthNonNegative.script [list [4, -2, 7]]) == some true

/-- The factorial of `lib/math.ak`, on the naturals: what the script's loop returns. -/
def factorial : Nat → Int
  | 0 => 1
  | k + 1 => ((k + 1 : Nat) : Int) * factorial k

theorem factorial_pos (k : Nat) : 0 < factorial k := by
  induction k with
  | zero => decide
  | succ k ih => simp only [factorial]; exact Int.mul_pos (by omega) ih

def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

-- `hasLoop`: the factorial and the list length loop, the vault does not
open Lean Elab Term Meta in
#eval show TermElabM Unit from do
  for (s, expected) in [(← `(factorialPositive.script), true), (← `(lengthNonNegative.script), true),
      (← `(vaultCap.script), false), (← `(ownerCanAlwaysSpend.script), false)] do
    let p ← elabTerm s none
    unless (← Auto.hasLoop p) == expected do throwError "hasLoop {s}: expected {expected}"

set_option uplc.cex.timings false

/-! ## Proved -/

/- `prop_factorial_positive` (`lib/math.ak`): `n >= 0 → factorial(n) > 0`. An `Int`
    leaf (split as `n < 0` / `n = ↑k`), a loop: the loop spec is what the loop returns. -/
#uplc_result info "UPLC-RESULT {\"status\":\"proved\",\"kernel\":true,\"method\":\"uplc_induction\",\"leaf\":\"n\",\"blaster\":\"valid\",\"fuel\":1000}" in
theorem prop_factorial_positive : ∀ n : Int, Halts factorialPositive.script [int n] vTrue := by
  uplc_auto [factorial_pos] (loop := fun k => .VCon (.Integer (factorial k))) (timeout := 30)

/-- info: 'UplcProofTests.Auto.prop_factorial_positive' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms prop_factorial_positive

/- `prop_accepts_only_up_to_cap` (`validators/vault.ak`): the vault accepts only up to
    its cap. The validator is called inside the body function: one script. -/
/-- info: UPLC-RESULT {"status":"proved","kernel":true,"method":"uplc_run","blaster":"valid","fuel":1000} -/
#guard_msgs in
theorem prop_accepts_only_up_to_cap :
    ∀ (cap : Int) (amount : Int), Halts vaultCap.script [int cap, int amount] (.VCon (.Bool true)) := by
  uplc_auto

/-- info: 'UplcProofTests.Auto.prop_accepts_only_up_to_cap' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms prop_accepts_only_up_to_cap

/- `prop_owner_can_always_spend` (`lib/owner.ak`): a `Bool` leaf (split by `cases`) and a
    `ByteArray` leaf. -/
/-- info: UPLC-RESULT {"status":"proved","kernel":true,"method":"uplc_run","blaster":"valid","fuel":1000} -/
#guard_msgs in
theorem prop_owner_can_always_spend :
    ∀ (is_open : Bool) (owner : ByteString), Halts ownerCanAlwaysSpend.script [bool is_open, bytes owner] vTrue := by
  uplc_auto

/-- info: 'UplcProofTests.Auto.prop_owner_can_always_spend' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms prop_owner_can_always_spend

/- `prop_length_non_negative` (`lib/lists.ak`): a `List<Int>` leaf, induction on
    it. Blaster does not translate the list encoding (`"blaster":"error"`). -/
/-- info: UPLC-RESULT {"status":"proved","kernel":true,"method":"uplc_induction","leaf":"xs","blaster":"error","fuel":125} -/
#guard_msgs in
theorem prop_length_non_negative :
    ∀ xs : List Int, Halts lengthNonNegative.script [list xs] vTrue := by
  uplc_auto (loop := fun k => .VCon (.Integer k.length))

/-- info: 'UplcProofTests.Auto.prop_length_non_negative' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms prop_length_non_negative

/- An accumulator (`factorial_acc(n, acc)`), a `Nat` leaf, any result value:
    `generalizing acc` is passed to `uplc_induction`. Blaster skipped: it cannot
    decide this one (the spec is recursive) and would use its whole timeout. -/
/-- info: UPLC-RESULT {"status":"proved","kernel":true,"method":"uplc_induction","leaf":"n","blaster":"skipped"} -/
#guard_msgs in
theorem factorial_acc_halts :
    ∀ (n : Nat) (acc : Int), Halts factorialAcc.script [int n, int acc] (.VCon (.Integer (acc * fact n))) := by
  uplc_auto [Int.mul_assoc, Int.natCast_mul] generalizing acc (timeout := 0)

/-- info: 'UplcProofTests.Auto.factorial_acc_halts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms factorial_acc_halts

/- The leaves already introduced (a theorem with parameters). -/
/-- info: UPLC-RESULT {"status":"proved","kernel":true,"method":"uplc_run","blaster":"valid","fuel":1000} -/
#guard_msgs in
theorem vault_intro (cap amount : Int) : Halts vaultCap.script [int cap, int amount] vTrue := by
  uplc_auto

/-- info: 'UplcProofTests.Auto.vault_intro' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms vault_intro

/- A claim stated with a definition of the leaves (not reducible): unfolded. -/
/-- The vault's claim, as a definition. -/
def VaultClaim (cap amount : Int) : Prop := Halts vaultCap.script [int cap, int amount] vTrue

/-- info: UPLC-RESULT {"status":"proved","kernel":true,"method":"uplc_run","blaster":"valid","fuel":1000} -/
#guard_msgs in
theorem vault_def : ∀ cap amount, VaultClaim cap amount := by
  uplc_auto

/-- info: 'UplcProofTests.Auto.vault_def' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms vault_def

/-! ## Refuted: a counterexample, a refutation checked by the kernel -/

/- `prop_factorial_greater`: `n >= 0 → factorial(n) > n`, false at `n = 1, 2`. -/
/--
error: UPLC-RESULT {"status":"refuted","kernel":true,"cex":{"n":2},"lean":{"n":"2"},"closer":"uplc_cex_closer","fuel":250}
Counterexample (refutation checked by the kernel, closer uplc_cex_closer):
  n := 2
Refutation:
example : ¬∀ (n : Int), Halts factorialGreater.script [int n] vTrue := by
  refute_with 2
-/
#guard_msgs in
example : ∀ n : Int, Halts factorialGreater.script [int n] vTrue := by
  uplc_auto

-- the refutation it printed, pasted
theorem prop_factorial_greater_refuted : ¬∀ (n : Int), Halts factorialGreater.script [int n] vTrue := by
  refute_with 2

/-- info: 'UplcProofTests.Auto.prop_factorial_greater_refuted' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms prop_factorial_greater_refuted

/- `prop_bug_accepts_only_up_to_cap` (`validators/vault_bug.ak`): the vault with an
    off-by-one accepts `amount = cap + 1`. -/
/--
error: UPLC-RESULT {"status":"refuted","kernel":true,"cex":{"cap":-1,"amount":0},"lean":{"cap":"-1","amount":"0"},"closer":"uplc_cex_closer","fuel":250}
Counterexample (refutation checked by the kernel, closer uplc_cex_closer):
  cap := -1
  amount := 0
Refutation:
example : ¬∀ (cap amount : Int), Halts vaultCapBug.script [int cap, int amount] vTrue := by
  refute_with -1, 0
-/
#guard_msgs in
example : ∀ cap amount : Int, Halts vaultCapBug.script [int cap, int amount] vTrue := by
  uplc_auto

theorem prop_bug_accepts_only_up_to_cap_refuted :
    ¬∀ (cap amount : Int), Halts vaultCapBug.script [int cap, int amount] vTrue := by
  refute_with -1, 0

/-- info: 'UplcProofTests.Auto.prop_bug_accepts_only_up_to_cap_refuted' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms prop_bug_accepts_only_up_to_cap_refuted

/- `prop_stranger_can_never_spend` (`lib/owner.ak`): false when the vault is open. The
    `ByteArray` values as Lean (`⟨"…"⟩`) and as hex in the JSON. -/
/--
error: UPLC-RESULT {"status":"refuted","kernel":true,"cex":{"is_open":true,"signer":"","owner":"213021"},"lean":{"is_open":"true","signer":"⟨\"\"⟩","owner":"⟨\"!0!\"⟩"},"closer":"uplc_cex_closer","fuel":250}
Counterexample (refutation checked by the kernel, closer uplc_cex_closer):
  is_open := true
  signer := ⟨""⟩
  owner := ⟨"!0!"⟩
Refutation:
example : ¬∀ (is_open : Bool) (signer owner : ByteString),
        Halts strangerCanNeverSpend.script [UplcProof.bool is_open, bytes signer, bytes owner] vTrue := by
  refute_with true, ⟨""⟩, ⟨"!0!"⟩
-/
#guard_msgs in
example : ∀ (is_open : Bool) (signer owner : ByteString),
    Halts strangerCanNeverSpend.script [bool is_open, bytes signer, bytes owner] vTrue := by
  uplc_auto

theorem prop_stranger_can_never_spend_refuted :
    ¬∀ (is_open : Bool) (signer owner : ByteString),
      Halts strangerCanNeverSpend.script [UplcProof.bool is_open, bytes signer, bytes owner] vTrue := by
  refute_with true, ⟨""⟩, ⟨"!0!"⟩

/-- info: 'UplcProofTests.Auto.prop_stranger_can_never_spend_refuted' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms prop_stranger_can_never_spend_refuted

/- Leaves already introduced: the refuted statement closes over them. -/
#uplc_result error "UPLC-RESULT {\"status\":\"refuted\",\"kernel\":true,\"cex\":{\"n\":2},\"lean\":{\"n\":\"2\"},\"closer\":\"uplc_cex_closer\",\"fuel\":250}" "example : ¬∀ (n : Int), Halts factorialGreater.script [int n] vTrue := by" in
example (n : Int) : Halts factorialGreater.script [int n] vTrue := by
  uplc_auto

/- A `Fails` claim (the vault rejects everything) is refuted by a run that halts.
    Blaster's model has no value for the leaves: `default` (`0`). -/
#uplc_result error "UPLC-RESULT {\"status\":\"refuted\",\"kernel\":true,\"cex\":{\"cap\":0,\"amount\":0},\"lean\":{\"cap\":\"0\",\"amount\":\"0\"},\"closer\":\"uplc_cex_closer\",\"defaults\":[\"cap\",\"amount\"],\"fuel\":250}" in
example : ∀ cap amount : Int, Fails vaultCap.script [int cap, int amount] := by
  uplc_auto

/-! ## Must reject -/

/- The true factorial property without its loop spec: Blaster finds no
    counterexample, the kernel stage has no proof: `oracle`, never proved. -/
#uplc_result error "UPLC-RESULT {\"status\":\"oracle\",\"kernel\":false,\"cex\":{},\"lean\":{},\"blaster\":\"valid\",\"fuel\":1000,\"reason\":\"Blaster found no counterexample in runs of up to 1000 steps; no kernel proof\"}" "(loop := fun k => …)" in
example : ∀ n : Int, Halts factorialPositive.script [int n] vTrue := by
  uplc_auto (timeout := 30)

/- A false claim is not proved by the kernel stage, Blaster or not. -/
#uplc_result error "UPLC-RESULT {\"status\":\"unknown\",\"kernel\":false,\"cex\":{},\"lean\":{},\"blaster\":\"skipped\",\"reason\":\"Blaster was skipped; no kernel proof\"}" in
example : ∀ n : Int, Halts factorialGreater.script [int n] vTrue := by
  uplc_auto [factorial_pos] (loop := fun k => .VCon (.Integer (factorial k))) (timeout := 0)

#uplc_result error "UPLC-RESULT {\"status\":\"unknown\",\"kernel\":false,\"cex\":{},\"lean\":{},\"blaster\":\"skipped\",\"reason\":\"Blaster was skipped; no kernel proof\"}" in
example : ∀ cap amount : Int, Halts vaultCapBug.script [int cap, int amount] vTrue := by
  uplc_auto (timeout := 0)

/- A spurious counterexample: with `(bound := halts)` running out of fuel counts as
    a counterexample, and at `N = 37` every run does (`n = 0` takes 92 steps). The
    run at `n = 0` halts with `True`: recorded as `spurious`, never `refuted`; with
    the loop spec the kernel proves the claim. -/
#uplc_result info "UPLC-RESULT {\"status\":\"proved\",\"kernel\":true,\"method\":\"uplc_induction\",\"leaf\":\"n\",\"blaster\":\"spurious\",\"fuel\":37,\"spurious\":{\"n\":0}}" in
example : ∀ n : Int, Halts factorialPositive.script [int n] vTrue := by
  uplc_auto [factorial_pos] (loop := fun k => .VCon (.Integer (factorial k))) (bound := halts) (fuel := 300)

#uplc_result error "UPLC-RESULT {\"status\":\"unknown\",\"kernel\":false,\"cex\":{},\"lean\":{},\"blaster\":\"spurious\",\"fuel\":37,\"spurious\":{\"n\":0},\"reason\":\"Blaster's only counterexample runs longer than 37 steps (it halts with the claimed value); no kernel proof\"}" in
example : ∀ n : Int, Halts factorialPositive.script [int n] vTrue := by
  uplc_auto (bound := halts) (fuel := 300)

-- the keys of the `"spurious"` object are distinct, as those of `"cex"`: a repeated
-- binder name gets `_1`
open Lean Elab Tactic Meta in
/-- info: {"n":1,"n_1":2} -/
#guard_msgs in
example : True := by
  run_tac do
    let stmt ← Term.elabTerm
      (← `(∀ (n : Int), 0 ≤ n → ∀ (n : Int), Halts factorialPositive.script [int n] vTrue)) none
    let some (_, _, _, obj) ← Auto.atValues (← instantiateMVars stmt) #[("n", "1"), ("n", "2")]
      | throwError "no values"
    logInfo obj
  trivial

/- A claimed value Blaster may choose (an `opaque` function): its counterexample
    cannot be confirmed (no closer proves `flag 0 ≠ true`): `falsified`, never
    `refuted`. -/
/-- A function nothing is known about. -/
opaque flag : Int → Bool

#uplc_result error "UPLC-RESULT {\"status\":\"falsified\",\"kernel\":false,\"cex\":{\"cap\":0,\"amount\":0},\"lean\":{\"cap\":\"0\",\"amount\":\"0\"},\"reason\":\"these values do not refute the statement: no closer proves\\n  ¬UplcProof.Halts vaultCap.script [UplcProof.int 0, UplcProof.int 0]\\n      (PlutusCore.UPLC.CekValue.CekValue.VCon (PlutusCore.UPLC.Term.Const.Bool (UplcProofTests.Auto.flag 0)))\\n(tried decide, rfl, bool, cases, simp, simp_all, uplc_cex_closer)\",\"blaster\":\"falsified\",\"fuel\":250}" in
example : ∀ cap amount : Int, Halts vaultCap.script [int cap, int amount] (.VCon (.Bool (flag cap))) := by
  uplc_auto

/- With `maxHeartbeats 0` (no limit), `uplc_run` on a loop over symbolic data still
    stops: at the engine's nested-split limit (`uplc.maxSplits`), and failing that at
    its own budget (`Auto.loopRunHeartbeats`). The claim stays unproved. -/
#uplc_result error "UPLC-RESULT {\"status\":\"unknown\",\"kernel\":false,\"cex\":{},\"lean\":{},\"blaster\":\"skipped\",\"reason\":\"Blaster was skipped; no kernel proof\"}" "more than 16 nested splits" in
set_option maxHeartbeats 0 in
example : ∀ n : Int, Halts factorialPositive.script [int n] vTrue := by
  uplc_auto (timeout := 0)

/- Goals of the wrong shape. -/
/--
error: UPLC-RESULT {"status":"error","kernel":false,"reason":"the goal is not a claim about a run of a script"}
uplc_auto: the goal is not a claim about a run of a script:
  1 + 1 = 2
Expected a goal `∀ (x₁ : τ₁) … (xₙ : τₙ), Halts p [enc x₁, …] v` (or `Fails p args`), e.g. `∀ n : Int, Halts body.script [int n] vTrue`.
-/
#guard_msgs in
example : 1 + 1 = 2 := by
  uplc_auto

#uplc_result error "UPLC-RESULT {\"status\":\"error\",\"kernel\":false,\"reason\":\"the goal is not a claim about a run of a script\"}" in
example : ¬∀ n : Int, Halts factorialGreater.script [int n] vTrue := by
  uplc_auto

#uplc_result error "UPLC-RESULT {\"status\":\"error\",\"kernel\":false,\"reason\":\"the goal is not a claim about a run of a script\"}" in
example : ∀ n : Int, Halts factorialGreater.script [int n] vTrue ∧ True := by
  uplc_auto

/- Usage errors. -/
/--
error: UPLC-RESULT {"status":"error","kernel":false,"reason":"bad option"}
uplc_auto: unknown option `fuels` (timeout, fuel, loop, bound)
-/
#guard_msgs in
example : ∀ n : Int, Halts factorialGreater.script [int n] vTrue := by
  uplc_auto (fuels := 3)

/--
error: UPLC-RESULT {"status":"error","kernel":false,"reason":"bad option"}
uplc_auto: `bound` is `safe` or `halts`
-/
#guard_msgs in
example : ∀ n : Int, Halts factorialGreater.script [int n] vTrue := by
  uplc_auto (bound := exact)

#uplc_result error "UPLC-RESULT {\"status\":\"error\",\"kernel\":false,\"reason\":\"a lemma does not elaborate\"}" "no_such_lemma" in
example : ∀ n : Int, Halts factorialGreater.script [int n] vTrue := by
  uplc_auto [no_such_lemma]

/-! ## The `UPLC-RESULT` line is one JSON object, each key once

With timings on (the `"ms"` key), for each status `uplc_auto`, `blaster_pretty` and
`blaster_refute` can end with. -/

/-- The keys of the JSON text `s` at the top level, in order, and the keys that
    occur twice in one object (at any depth): a scan of the text, since
    `Json.parse` keeps only one of two equal keys. -/
def scanKeys (s : String) : List String × List String := Id.run do
  let cs := s.toList.toArray
  let mut stack : List (List String) := []
  let mut top : List String := []
  let mut dups : List String := []
  let mut i := 0
  while i < cs.size do
    let c := cs[i]!
    if c == '"' then
      -- a string: a key if a `:` follows
      let mut j := i + 1
      let mut str := ""
      while j < cs.size && cs[j]! != '"' do
        if cs[j]! == '\\' then
          str := str.push '\\'
          j := j + 1
        if j < cs.size then str := str.push cs[j]!
        j := j + 1
      let mut k := j + 1
      while k < cs.size && cs[k]!.isWhitespace do
        k := k + 1
      if k < cs.size && cs[k]! == ':' then
        match stack with
        | keys :: rest =>
            if keys.contains str then dups := dups ++ [str]
            if rest.isEmpty then top := top ++ [str]
            stack := (str :: keys) :: rest
        | [] => pure ()
      i := j + 1
    else
      if c == '{' then stack := [] :: stack
      else if c == '}' then stack := stack.drop 1
      i := i + 1
  return (top, dups)

#guard scanKeys "{\"a\":1,\"b\":{\"a\":[\"a\",{\"c\":\"x:\"}]},\"c\":2}" == (["a", "b", "c"], [])
#guard scanKeys "{\"a\":1,\"ms\":{},\"b\":\"\\\"ms\\\"\",\"ms\":{}}" == (["a", "ms", "b", "ms"], ["ms"])

open Lean Elab Command in
/-- `#uplc_json in cmd`: runs `cmd` with `uplc.cex.timings` on; for each message whose
    first line starts with `UPLC-RESULT `, checks that the rest of the line is one
    JSON object (`Json.parse`) with no key twice in an object, and logs its severity,
    status, top-level keys in order and the keys of its `"ms"` (sorted). The
    messages of `cmd` are dropped. -/
syntax (name := uplcJsonCmd) "#uplc_json" " in" ppLine command : command

open Lean Elab Command in
@[command_elab uplcJsonCmd] def elabUplcJson : CommandElab := fun stx => do
  let initMsgs ← modifyGet fun st => (st.messages, { st with messages := {} })
  withScope (fun sc => { sc with opts := UplcProof.Cex.uplc.cex.timings.set sc.opts true }) do
    withReader ({ · with snap? := none }) do
      elabCommandTopLevel stx[2]
  let msgs := (← get).messages ++
    (← get).snapshotTasks.foldl (· ++ ·.get.getAll.foldl (· ++ ·.diagnostics.msgLog) {}) {}
  modify fun st => { st with messages := initMsgs, snapshotTasks := #[] }
  let mut out : Array String := #[]
  for m in msgs.toList do
    let line := ((← m.data.toString).splitOn "\n").headD ""
    unless line.startsWith "UPLC-RESULT " do continue
    let body := line.drop "UPLC-RESULT ".length
    let sev := match m.severity with
      | .error => "error" | .warning => "warning" | .information => "info"
    match Json.parse body with
    | .error e => logErrorAt stx m!"#uplc_json: not JSON ({e}):{indentD body}"
    | .ok j =>
        let (top, dups) := scanKeys body
        unless dups.isEmpty do
          logErrorAt stx m!"#uplc_json: repeated keys {dups}:{indentD body}"
        let status := (j.getObjValAs? String "status").toOption.getD "?"
        let ms := match j.getObjVal? "ms" with
          | .ok (.obj kvs) => kvs.keys
          | _ => []
        let msPart := if ms.isEmpty then "" else s!"; ms: {", ".intercalate ms}"
        out := out.push s!"{sev} {status}: {", ".intercalate top}{msPart}"
  if out.isEmpty then logErrorAt stx "#uplc_json: no UPLC-RESULT line"
  else logInfoAt stx ("\n".intercalate out.toList)

-- `uplc_auto`: proved, refuted (also with `defaults`), oracle, unknown (skipped,
-- spurious), falsified, error
/-- info: info proved: status, kernel, method, blaster, fuel, ms; ms: blaster, kernel, total -/
#guard_msgs in
#uplc_json in
example : ∀ (cap amount : Int), Halts vaultCap.script [int cap, int amount] vTrue := by
  uplc_auto

/--
info: error refuted: status, kernel, cex, lean, closer, ms, fuel; ms: blaster, refute, render, total
-/
#guard_msgs in
#uplc_json in
example : ∀ cap amount : Int, Halts vaultCapBug.script [int cap, int amount] vTrue := by
  uplc_auto

/--
info: error refuted: status, kernel, cex, lean, closer, defaults, ms, fuel; ms: blaster, refute, render, total
-/
#guard_msgs in
#uplc_json in
example : ∀ cap amount : Int, Fails vaultCap.script [int cap, int amount] := by
  uplc_auto

/--
info: error oracle: status, kernel, cex, lean, blaster, fuel, reason, ms; ms: blaster, kernel, total
-/
#guard_msgs in
#uplc_json in
example : ∀ n : Int, Halts factorialPositive.script [int n] vTrue := by
  uplc_auto (fuel := 250)

/-- info: error unknown: status, kernel, cex, lean, blaster, reason, ms; ms: blaster, kernel, total -/
#guard_msgs in
#uplc_json in
example : ∀ cap amount : Int, Halts vaultCapBug.script [int cap, int amount] vTrue := by
  uplc_auto (timeout := 0)

/--
info: error unknown: status, kernel, cex, lean, blaster, fuel, spurious, reason, ms; ms: blaster, kernel, total
-/
#guard_msgs in
#uplc_json in
example : ∀ n : Int, Halts factorialPositive.script [int n] vTrue := by
  uplc_auto (bound := halts) (fuel := 300)

/--
info: error falsified: status, kernel, cex, lean, reason, blaster, fuel, ms; ms: blaster, kernel, refute, render, total
-/
#guard_msgs in
#uplc_json in
example : ∀ cap amount : Int, Halts vaultCap.script [int cap, int amount] (.VCon (.Bool (flag cap))) := by
  uplc_auto

/-- info: error error: status, kernel, reason -/
#guard_msgs in
#uplc_json in
example : 1 + 1 = 2 := by
  uplc_auto

-- `blaster_pretty`: refuted, falsified, oracle (an info message), unknown (Blaster fails)
/-- info: error refuted: status, kernel, cex, lean, closer, ms; ms: blaster, refute, render -/
#guard_msgs in
#uplc_json in
example : ∀ (x : Int), x * x ≠ 9 ∨ x > 0 := by blaster_pretty

/-- info: error falsified: status, kernel, cex, lean, defaults, reason, ms; ms: blaster, refute, render -/
#guard_msgs in
#uplc_json in
example : ∀ (f : Int → Int), f 0 = 0 := by blaster_pretty

/-- info: info oracle: status, kernel, cex, lean, ms; ms: blaster -/
#guard_msgs in
#uplc_json in
example : ∀ (x : Int), x * x ≥ 0 := by blaster_pretty

/-- info: error unknown: status, kernel, cex, lean, reason, ms; ms: blaster -/
#guard_msgs in
#uplc_json in
example : ∀ n : Int, Halts factorialGreater.script [int n] vTrue := by blaster_pretty

-- `blaster_refute`: oracle, falsified, unknown (Blaster fails); refuted closes the goal
/-- info: error oracle: status, kernel, cex, lean, ms; ms: blaster -/
#guard_msgs in
#uplc_json in
example : ¬ ∀ (x : Int), x * x ≥ 0 := by blaster_refute

/-- info: error falsified: status, kernel, cex, lean, defaults, reason, ms; ms: blaster, refute, render -/
#guard_msgs in
#uplc_json in
example : ¬ ∀ (f : Int → Int), f 0 = 0 := by blaster_refute

/-- info: error unknown: status, kernel, cex, lean, reason, ms; ms: blaster -/
#guard_msgs in
#uplc_json in
example : ¬ ∀ n : Int, Halts factorialGreater.script [int n] vTrue := by blaster_refute

/-! ## The theory: a counterexample to the bounded claim is a real one -/

/-- info: 'UplcProof.Halts.safe' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Halts.safe

/-- info: 'UplcProof.Fails.noHalt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Fails.noHalt

/-! ## A proof that uses an axiom is not accepted

Last in the file: Blaster reads the file's axioms as hypotheses. -/

/-- `factorial_pos`, stated as an axiom instead of proved. -/
axiom factorial_pos_axiom (k : Nat) : 0 < factorial k

/- The factorial property, whose only proof here goes through the axiom: the
    proof is built, then rejected (its axioms are checked), so the claim stays
    unproved. -/
#uplc_result error "UPLC-RESULT {\"status\":\"unknown\",\"kernel\":false,\"cex\":{},\"lean\":{},\"blaster\":\"skipped\",\"reason\":\"Blaster was skipped; no kernel proof\"}" "uses axioms beyond propext, Quot.sound, Classical.choice: [UplcProofTests.Auto.factorial_pos_axiom]" in
example : ∀ n : Int, Halts factorialPositive.script [int n] vTrue := by
  uplc_auto [factorial_pos_axiom] (loop := fun k => .VCon (.Integer (factorial k))) (timeout := 0)

end UplcProofTests.Auto
