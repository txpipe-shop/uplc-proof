import UplcProof.Cex
import UplcProof.Encode
import CardanoLedgerApi.V3

/-!
# Tests: refuting claims about real validators over a full `ScriptContext`

Two Plutus V3 validators of aiken-blaster-examples, as compiled in its `plutus.json`
(`Tests/Validators/`): `time_lock` (spend after the datum's deadline) and `vault`
(a parameterised two-party time lock). For each, a FALSE claim close to one the
examples prove with Blaster, stated on the ORIGINAL script with PlutusCore's CEK
machine (`Accepts` / `Halts`, the context passed as `Data`, `IsData.toData ctx`),
and refuted at Blaster's counterexample:

* (a) `refute_cex` fed with Blaster's raw counterexample entries, as Blaster
  printed them (raw z3 text → Lean values → kernel-checked refutation);
* (b) `refute_with` with the same values written as readable Lean terms;
* (c) `refute_from_blaster` (defined below): Blaster run here, on the claim in the
  form Blaster takes (time_lock: `#prep_uplc`'s `.prop`; vault: `cekExecuteProgram`
  at a fixed fuel), its model matched to the original claim's binders by name and
  refuted (`UplcProof.Cex.analyse`), so the raw text is regenerated, not pasted.

The conclusion `¬ Accepts …` is refuted by `uplc_cex_closer`: `evalRun` runs the
script on the concrete context to `Error`, in kernel-checked segments (vault's
run waits on two closed `equalsData`, decided by `dataEqB`). Then what must be
rejected: values that are not a counterexample (`t ≥ deadline`, the validator
accepts), refused by `refute_with` with its error.

## Measurements

Apple M5, 32 GB, Lean v4.24.0, 2026-10-08, with other jobs running (load average
about 7): an idle machine is faster. Per refutation, Lean's profiler
(`set_option profiler true`, `profiler.threshold 1`, `Elab.async false`), three
runs, ranges. "run" is `uplc_cex_closer` (`evalRun`: the symbolic CEK run, closed
`equalsData` decided by `dataEqB`), "other" the rest of the tactic (elaborating the
values, discharging the hypotheses), "kernel" the kernel's check of the theorem.
The script runs 418 CEK steps on time_lock's counterexample, 1,228 on vault's.

| refutation | total | run | other | kernel |
|---|---|---|---|---|
| time_lock (a) `refute_cex` | 0.34–0.37 s | 0.10–0.12 s | 0.11–0.12 s | 0.11–0.12 s |
| time_lock (b) `refute_with` | 0.30–0.38 s | 0.11–0.13 s | 0.07–0.08 s | 0.11–0.16 s |
| `#prep_uplc` (Blaster's form, for (c)) | 7.6–8.8 s | | | |
| time_lock (c) Blaster, then refutation | 0.68–0.75 s | 0.10–0.11 s | | 0.11–0.14 s |
| vault (a) `refute_cex` | 1.20–1.26 s | 0.58–0.62 s | 0.07 s | 0.46–0.55 s |
| vault (b) `refute_with` | 1.18–1.28 s | 0.61–0.69 s | 0.07–0.08 s | 0.45–0.48 s |
| vault (c) Blaster, then refutation | 3.54–3.99 s | 0.56–0.63 s | | 0.46–0.56 s |
| must reject (`refute_with` refused) | 0.14–0.18 s | 0.11–0.14 s | 0.01 s | |

(c) also includes Blaster (z3) and `analyse`'s own kernel check of the refutation
in a throwaway environment. Every refutation's axioms: `propext`, `Quot.sound`.

Whole file: `lake build UplcProofTests.ScriptContext`, its dependencies built,
8.2–8.5 s wall, 1.84–1.92 GB peak (max RSS from `/usr/bin/time -l`, three builds).
-/

set_option uplc.cex.timings false

open PlutusCore.Data (Data)
open PlutusCore.ByteString (ByteString)
open PlutusCore.UPLC.Term (Term Const)
open PlutusCore.UPLC.CekMachine (cekExecuteProgram)
open CardanoLedgerApi.IsData.Class (IsData toTerm)
open CardanoLedgerApi.V3 (ScriptContext TxOutRef TxOut Address Value Closure UpperBound
  POSIXTimeRange spendingInputs lovelaceValue singleton after)
open UplcProof UplcProof.Cex

namespace UplcProofTests.ScriptContext

open Lean Elab Tactic Meta in
/-- `refute_from_blaster S'` closes `¬ S` (`S` a claim on the original script) with
    Blaster's counterexample to `S'`, the same claim in the form Blaster takes:
    Blaster runs on `S'`, its model is matched to `S`'s binders by name (binders the
    model leaves out get `default`) and `S` is refuted at it (`analyse`, checked by
    the kernel). Blaster's own messages are dropped. -/
elab "refute_from_blaster " t:term : tactic => withMainContext do
  let goal ← getMainGoal
  let some S ← negated? (← goal.getType)
    | throwError "refute_from_blaster: the goal is not a negation `¬ S`"
  let S' ← Term.withSynthesize <| Term.elabTermEnsuringType t (mkSort .zero)
  let S' ← instantiateMVars S'
  let msgs := (← getThe Core.State).messages
  let outcome ← runBlaster S' default
  modifyThe Core.State fun s => { s with messages := msgs }
  let .falsified entries := outcome
    | throwError "refute_from_blaster: Blaster did not falsify{indentExpr S'}"
  let (r, proof?) ← analyse S entries
  let some proof := proof? | throwError (r.message false)
  goal.assign proof
  replaceMainGoal []

/-! ## `time_lock`

The datum is `Constr 0 [I deadline]`, the redeemer `Constr 0 []`; the validator
accepts iff the lower bound of the validity range is finite and `≥ deadline`. The
claim drops that last condition (`time_lock_complete` without `afterDeadline`). -/

/-- info: Successfully decoded single CBOR hex 'Tests/Validators/time_lock.hex' -/
#guard_msgs in
#import_uplc timeLock PlutusV3 single_cbor_hex "Tests/Validators/time_lock.hex"

def claimRedeemer : Data := .Constr 0 []
def deadlineDatum (d : Int) : Data := .Constr 0 [.I d]

/-- "`time_lock` accepts every claim with a deadline datum and a finite lower
    bound", on the original script: FALSE. -/
abbrev TimeLockClaim : Prop :=
  ∀ (ctx : ScriptContext) (deadline t : Int) (ref : TxOutRef)
    (closure : Closure) (upper : UpperBound),
    ctx.scriptContextRedeemer = claimRedeemer →
    ctx.scriptContextScriptInfo = .SpendingScript ref (some (deadlineDatum deadline)) →
    ctx.scriptContextTxInfo.txInfoValidRange =
      IsData.toData (POSIXTimeRange.mk (.FiniteLowerBound t closure) upper) →
    Accepts timeLock.script (IsData.toData ctx)

-- (a) Blaster's counterexample, as it printed it (`#blaster` on `TimeLockClaimPrep` below)
theorem timeLock_refute_cex : ¬ TimeLockClaim := by
  refute_cex
    "ctx: (let ((a!1 (List.cons (PlutusCore.Data.PlutusCore.DataInternal.Data.Constr
                        1
                        (List.cons (PlutusCore.Data.PlutusCore.DataInternal.Data.I
                                     18456)
                                   (as List.nil
                                       (@List @PlutusCore.Data.PlutusCore.DataInternal.Data))))
                      (List.cons (PlutusCore.Data.PlutusCore.DataInternal.Data.Constr
                                   1
                                   (as List.nil
                                       (@List @PlutusCore.Data.PlutusCore.DataInternal.Data)))
                                 (as List.nil
                                     (@List @PlutusCore.Data.PlutusCore.DataInternal.Data)))))
      (a!2 (List.cons (PlutusCore.Data.PlutusCore.DataInternal.Data.Constr
                        1
                        (List.cons (PlutusCore.Data.PlutusCore.DataInternal.Data.I
                                     3)
                                   (as List.nil
                                       (@List @PlutusCore.Data.PlutusCore.DataInternal.Data))))
                      (List.cons (PlutusCore.Data.PlutusCore.DataInternal.Data.Constr
                                   1
                                   (as List.nil
                                       (@List @PlutusCore.Data.PlutusCore.DataInternal.Data)))
                                 (as List.nil
                                     (@List @PlutusCore.Data.PlutusCore.DataInternal.Data)))))
      (a!4 (Option.some (PlutusCore.Data.PlutusCore.DataInternal.Data.Constr
                          0
                          (List.cons (PlutusCore.Data.PlutusCore.DataInternal.Data.I
                                       18457)
                                     (as List.nil
                                         (@List @PlutusCore.Data.PlutusCore.DataInternal.Data)))))))
(let ((a!3 (PlutusCore.Data.PlutusCore.DataInternal.Data.Constr
             0
             (List.cons (PlutusCore.Data.PlutusCore.DataInternal.Data.Constr
                          0
                          a!1)
                        (List.cons (PlutusCore.Data.PlutusCore.DataInternal.Data.Constr
                                     0
                                     a!2)
                                   (as List.nil
                                       (@List @PlutusCore.Data.PlutusCore.DataInternal.Data)))))))
  (CardanoLedgerApi.V3.Contexts.ScriptContext.mk
    (CardanoLedgerApi.V3.Contexts.TxInfo.mk
      (as List.nil (@List @CardanoLedgerApi.V3.Contexts.TxInInfo))
      (as List.nil (@List @CardanoLedgerApi.V3.Contexts.TxInInfo))
      (as List.nil (@List @CardanoLedgerApi.V2.Tx.TxOut))
      4
      (as List.nil
          (@List (@Prod @PlutusCore.Data.PlutusCore.DataInternal.Data
                        @PlutusCore.Data.PlutusCore.DataInternal.Data)))
      (as List.nil (@List @CardanoLedgerApi.V3.TxCert.TxCert))
      (as List.nil
          (@List (@Prod @CardanoLedgerApi.V1.Credential.Credential Int)))
      a!3
      (as List.nil
          (@List @PlutusCore.ByteString.PlutusCore.ByteStringInternal.ByteString))
      (as List.nil
          (@List (@Prod @CardanoLedgerApi.V3.Contexts.ScriptPurpose
                        @PlutusCore.Data.PlutusCore.DataInternal.Data)))
      (as List.nil
          (@List (@Prod @PlutusCore.ByteString.PlutusCore.ByteStringInternal.ByteString
                        @PlutusCore.Data.PlutusCore.DataInternal.Data)))
      (PlutusCore.ByteString.PlutusCore.ByteStringInternal.ByteString.mk \"!0!\")
      (as List.nil
          (@List (@Prod @CardanoLedgerApi.V3.Governance.Voter
                        (@List (@Prod @CardanoLedgerApi.V3.Governance.GovernanceActionId
                                      @CardanoLedgerApi.V3.Governance.Vote)))))
      (as List.nil (@List @CardanoLedgerApi.V3.Governance.ProposalProcedure))
      (PlutusCore.Data.PlutusCore.DataInternal.Data.I 15)
      (PlutusCore.Data.PlutusCore.DataInternal.Data.I 14))
    (PlutusCore.Data.PlutusCore.DataInternal.Data.Constr
      0
      (as List.nil (@List @PlutusCore.Data.PlutusCore.DataInternal.Data)))
    (CardanoLedgerApi.V3.Contexts.ScriptInfo.SpendingScript
      (CardanoLedgerApi.V3.Tx.TxOutRef.mk
        (PlutusCore.ByteString.PlutusCore.ByteStringInternal.ByteString.mk
          \"!1!\")
        5)
      a!4))))",
    "deadline: 18457",
    "t: 18456",
    "ref: (CardanoLedgerApi.V3.Tx.TxOutRef.mk
  (PlutusCore.ByteString.PlutusCore.ByteStringInternal.ByteString.mk \"!1!\")
  5)",
    "closure: true",
    "upper: (CardanoLedgerApi.V1.Time.UpperBound.FiniteUpperBound 3 true)"

/-- The counterexample context, readable: a claim (`Constr 0 []`) spending `ref`
    with deadline 18457, in a transaction whose validity range is `[18456, 3]`. -/
def tlRef : TxOutRef := ⟨⟨"!1!"⟩, 5⟩
def tlCtx (lower : Int) : ScriptContext where
  scriptContextTxInfo :=
    { txInfoInputs := [], txInfoReferenceInputs := [], txInfoOutputs := [],
      txInfoFee := 4, txInfoMint := [], txInfoTxCerts := [], txInfoWdrl := [],
      txInfoValidRange :=
        .Constr 0 [.Constr 0 [.Constr 1 [.I lower], .Constr 1 []],
                   .Constr 0 [.Constr 1 [.I 3], .Constr 1 []]],
      txInfoSignatories := [], txInfoRedeemers := [], txInfoData := [],
      txInfoId := ⟨"!0!"⟩, txInfoVotes := [], txInfoProposalProcedures := [],
      txInfoCurrentTreasuryAmount := .I 15, txInfoTreasuryDonation := .I 14 }
  scriptContextRedeemer := claimRedeemer
  scriptContextScriptInfo := .SpendingScript tlRef (some (deadlineDatum 18457))

-- (b) the same values, readable
theorem timeLock_refute_with : ¬ TimeLockClaim := by
  refute_with tlCtx 18456, 18457, 18456, tlRef, true, .FiniteUpperBound 3 true

-- (c) Blaster run here on the `#prep_uplc` form, its model refuting the original claim
#prep_uplc timeLockPrep timeLock spendingInputs 20000

/-- The same claim on `#prep_uplc`'s `.prop` (Blaster's optimised term, not proved
    equal to the script): what Blaster is given. -/
abbrev TimeLockClaimPrep : Prop :=
  ∀ (ctx : ScriptContext) (deadline t : Int) (ref : TxOutRef)
    (closure : Closure) (upper : UpperBound),
    ctx.scriptContextRedeemer = claimRedeemer →
    ctx.scriptContextScriptInfo = .SpendingScript ref (some (deadlineDatum deadline)) →
    ctx.scriptContextTxInfo.txInfoValidRange =
      IsData.toData (POSIXTimeRange.mk (.FiniteLowerBound t closure) upper) →
    PlutusCore.UPLC.Utils.isSuccessful (timeLockPrep.prop ctx)

theorem timeLock_refute_blaster : ¬ TimeLockClaim := by
  refute_from_blaster TimeLockClaimPrep

/-- info: 'UplcProofTests.ScriptContext.timeLock_refute_cex' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms timeLock_refute_cex
/-- info: 'UplcProofTests.ScriptContext.timeLock_refute_with' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms timeLock_refute_with
/-- info: 'UplcProofTests.ScriptContext.timeLock_refute_blaster' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms timeLock_refute_blaster

/-! ## `vault`

Parameterised by `seed_utxo`; a `Claim { amount, own_input_index,
continuing_output_index }` by the beneficiary must, among others, come after
`unlock_time`. The claim is aiken-blaster-examples' `claim_complete` with the
`unlockTime ≤ now` conjunct of `validClaim` dropped, over the parameters of
`claimCtx` (the validator still receives a full `ScriptContext`). Its run compares
`OutputReference`s and addresses with `equalsData`. -/

/-- info: Successfully decoded single CBOR hex 'Tests/Validators/vault.hex' -/
#guard_msgs in
#import_uplc vault PlutusV3 single_cbor_hex "Tests/Validators/vault.hex"

def vaultPolicyId : ByteString := "7c0c8d39ce0f6a4e3a1b2d8f5c9e"
def vaultSeedRefData : Data :=
  IsData.toData (⟨"1234567890abcdef1234567890abcdef1234567890abcdef1234567890abcdef", 0⟩ : TxOutRef)

def vaultClaimRedeemer (amount ownIdx contIdx : Int) : Data :=
  .Constr 0 [.I amount, .I ownIdx, .I contIdx]
def vaultDatum (beneficiary depositor : ByteString) (unlockTime cap : Int) : Data :=
  .Constr 0 [.B beneficiary, .B depositor, .I unlockTime, .I cap]
def vaultValue (lovelace nftQty : Int) : Value :=
  lovelaceValue lovelace ++ singleton vaultPolicyId PlutusCore.ByteString.emptyByteString nftQty
def vaultAddr : Address :=
  { addressCredential := .ScriptCredential vaultPolicyId, addressStakingCredential := none }
def vaultRef : TxOutRef := ⟨"e3b0c44298fc1c149afbf4c8996fb924", 0⟩
def vaultOutput (datum : Data) (lovelace nftQty : Int) : TxOut :=
  ⟨vaultAddr, vaultValue lovelace nftQty, .OutputDatum datum, none⟩

/-- A `Claim` transaction: one input (the spent script UTxO), one continuing
    output; the redeemer's index hints both 0 (as in aiken-blaster-examples). -/
def claimCtx (beneficiary depositor : ByteString)
    (unlockTime cap amount now inputValue continuingValue inputNftQty continuingNftQty : Int) :
    ScriptContext :=
  let d := vaultDatum beneficiary depositor unlockTime cap
  { scriptContextTxInfo :=
      { txInfoInputs := [⟨vaultRef, vaultOutput d inputValue inputNftQty⟩]
        txInfoReferenceInputs := []
        txInfoOutputs := [vaultOutput d continuingValue continuingNftQty]
        txInfoFee := 0, txInfoMint := [], txInfoTxCerts := [], txInfoWdrl := []
        txInfoValidRange := IsData.toData (after now)
        txInfoSignatories := [beneficiary]
        txInfoRedeemers := [], txInfoData := []
        txInfoId := "27ae41e4649b934ca495991b7852b855"
        txInfoVotes := [], txInfoProposalProcedures := []
        txInfoCurrentTreasuryAmount := IsData.toData (none : Option Int)
        txInfoTreasuryDonation := IsData.toData (none : Option Int) }
    scriptContextRedeemer := vaultClaimRedeemer amount 0 0
    scriptContextScriptInfo := .SpendingScript vaultRef (some d) }

/-- "`vault` accepts a bounded claim by the beneficiary, whatever the time", on the
    original script: FALSE. -/
abbrev VaultClaim : Prop :=
  ∀ (beneficiary depositor : ByteString)
    (unlockTime cap amount now inputValue continuingValue inputNftQty continuingNftQty : Int),
    0 < amount → amount ≤ cap → inputValue - amount ≤ continuingValue →
    inputNftQty = 1 → continuingNftQty = 1 →
    Halts vault.script
      [data vaultSeedRefData,
       data (IsData.toData (claimCtx beneficiary depositor unlockTime cap amount now
                              inputValue continuingValue inputNftQty continuingNftQty))]
      vUnit

-- (a) Blaster's counterexample, as it printed it (on `VaultClaimFuel` below); its model
-- leaves `beneficiary` and `depositor` out (unconstrained): given here as `""`
theorem vault_refute_cex : ¬ VaultClaim := by
  refute_cex
    "beneficiary: (PlutusCore.ByteString.PlutusCore.ByteStringInternal.ByteString.mk \"\")",
    "depositor: (PlutusCore.ByteString.PlutusCore.ByteStringInternal.ByteString.mk \"\")",
    "unlockTime: 1",
    "cap: 1",
    "amount: 1",
    "now: 0",
    "inputValue: 1",
    "continuingValue: 0",
    "inputNftQty: 1",
    "continuingNftQty: 1"

-- (b) the same values, readable
theorem vault_refute_with : ¬ VaultClaim := by
  refute_with "", "", 1, 1, 1, 0, 1, 0, 1, 1

/-- The same claim with `cekExecuteProgram` at a fixed fuel, as aiken-blaster-examples
    states vault claims: what Blaster is given. -/
abbrev VaultClaimFuel : Prop :=
  ∀ (beneficiary depositor : ByteString)
    (unlockTime cap amount now inputValue continuingValue inputNftQty continuingNftQty : Int),
    0 < amount → amount ≤ cap → inputValue - amount ≤ continuingValue →
    inputNftQty = 1 → continuingNftQty = 1 →
    cekExecuteProgram vault.script
      [toTerm vaultSeedRefData,
       toTerm (claimCtx beneficiary depositor unlockTime cap amount now
                 inputValue continuingValue inputNftQty continuingNftQty)] 5000000
      = .Halt (.VCon Const.Unit)

-- (c) Blaster run here, its model (`beneficiary`, `depositor` defaulted) refuting the claim
theorem vault_refute_blaster : ¬ VaultClaim := by
  refute_from_blaster VaultClaimFuel

/-- info: 'UplcProofTests.ScriptContext.vault_refute_cex' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms vault_refute_cex
/-- info: 'UplcProofTests.ScriptContext.vault_refute_with' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms vault_refute_with
/-- info: 'UplcProofTests.ScriptContext.vault_refute_blaster' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms vault_refute_blaster

/-! ## Must reject: values that are not a counterexample

The lower bound at the deadline (`t = deadline = 18457`): the hypotheses hold, the
validator accepts (`evalRun` halts with `()`), so nothing refutes the claim. -/

/--
error: these values do not refute the statement: no closer proves
  ¬Accepts timeLock.script (IsData.toData (tlCtx 18457))
(tried decide, rfl, bool, cases, simp, simp_all, uplc_cex_closer)
-/
#guard_msgs in
example : ¬ TimeLockClaim := by
  refute_with tlCtx 18457, 18457, 18457, tlRef, true, .FiniteUpperBound 3 true

end UplcProofTests.ScriptContext
