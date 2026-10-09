import UplcProof.Cex
import UplcProof.Encode
import CardanoLedgerApi.V3

/-!
# Tests: counterexamples that are Lean, refutations the kernel checks

* `Pretty` on raw z3 text (with `let`, `as`, qualified names, string escapes);
* no global unexpander: goals print as before;
* rendering: the Lean text of a value elaborates back to it (checked by
  `renderLean`, and again here by pasting the text into source and `rfl`);
* `blaster_refute`, `refute_with`, `refute_cex` (and `refuteWithValues`) on false
  statements over `Int`, `Data`, `TxOutRef`, `List Data`, `ByteString`, `Bool`,
  each with an axiom guard;
* `blaster_pretty` on false goals: the exact `UPLC-RESULT` message, and its
  snippet pasted back as a theorem;
* a `Halts` claim on a real Aiken script refuted by running it, also with a run
  that takes more heartbeats than the budget (`maxHeartbeats`) allows.
-/

set_option uplc.cex.timings false

open Lean Elab Meta UplcProof.Cex in
/-- `#cex_lean ty, "raw"`: the Lean text `renderLean` gives for the z3 value `raw`
    at type `ty` (which candidate won), and its JSON. -/
elab "#cex_lean " ty:term ", " raw:str : command => Command.liftTermElabM do
  let ty ← Term.elabType ty
  let (v, _) ← elabCexValue raw.getString ty
  match ← renderLean v ty with
  | some r => logInfo m!"{r.line}   [{r.mode}]   {(← jsonOf v ty).compress}"
  | none => logInfo "no Lean text"

-- before any `open`, names cannot be shortened: the leading-dot form wins
/-- info: .Constr 0 [.I 5]   [dot]   {"constructor":0,"fields":[{"int":5}]} -/
#guard_msgs in #cex_lean PlutusCore.Data.Data, "(PlutusCore.Data.PlutusCore.DataInternal.Data.Constr 0
  (List.cons (PlutusCore.Data.PlutusCore.DataInternal.Data.I 5) List.nil))"

example : (.Constr 0 [.I 5] : PlutusCore.Data.Data) =
    PlutusCore.Data.PlutusCore.DataInternal.Data.Constr 0
      [PlutusCore.Data.PlutusCore.DataInternal.Data.I 5] := rfl

open PlutusCore.Data (Data)
open PlutusCore.ByteString (ByteString)
open CardanoLedgerApi.V3.Tx (TxOutRef)
open UplcProof.Cex

namespace UplcProofTests.Cex

/-! ## `Pretty`: z3 text to clean text -/

/-- info: Except.ok "-3" -/
#guard_msgs in #eval prettyFull "(- 3)"

/-- info: Except.ok "PlutusCore.Data.PlutusCore.DataInternal.Data.I (-5)" -/
#guard_msgs in #eval prettyFull "(PlutusCore.Data.PlutusCore.DataInternal.Data.I (- 5))"

-- `as` dropped, `List.cons` chains as list literals, full names kept
/--
info: Except.ok "[PlutusCore.Data.PlutusCore.DataInternal.Data.I 6, PlutusCore.Data.PlutusCore.DataInternal.Data.I 7]"
-/
#guard_msgs in #eval prettyFull "(List.cons (PlutusCore.Data.PlutusCore.DataInternal.Data.I 6)
           (List.cons (PlutusCore.Data.PlutusCore.DataInternal.Data.I 7)
                      (as List.nil
                          (@List @PlutusCore.Data.PlutusCore.DataInternal.Data))))"

/-- The value z3 gives for `d ≠ Data.Map [(Data.I 1, Data.B ⟨"a"⟩)]`: a `let`, an `as`. -/
def z3Map : String := "(let ((a!1 (List.cons (Prod.mk (PlutusCore.Data.PlutusCore.DataInternal.Data.I
                                 1)
                               (PlutusCore.Data.PlutusCore.DataInternal.Data.B
                                 (PlutusCore.ByteString.PlutusCore.ByteStringInternal.ByteString.mk
                                   \"a\")))
                      (as List.nil
                          (@List (@Prod @PlutusCore.Data.PlutusCore.DataInternal.Data
                                        @PlutusCore.Data.PlutusCore.DataInternal.Data))))))
  (PlutusCore.Data.PlutusCore.DataInternal.Data.Map a!1))"

/--
info: Except.ok "PlutusCore.Data.PlutusCore.DataInternal.Data.Map [(PlutusCore.Data.PlutusCore.DataInternal.Data.I 1, PlutusCore.Data.PlutusCore.DataInternal.Data.B (PlutusCore.ByteString.PlutusCore.ByteStringInternal.ByteString.mk \"a\"))]"
-/
#guard_msgs in #eval prettyFull z3Map

-- the short display form (not guaranteed Lean: only ever shown as a comment)
/-- info: Except.ok "Data.Map [(Data.I 1, Data.B (ByteString.mk \"a\"))]" -/
#guard_msgs in #eval prettyCex z3Map

/-- info: Except.ok "TxOutRef.mk (ByteString.mk \"\") 3" -/
#guard_msgs in #eval prettyCex "(CardanoLedgerApi.V3.Tx.TxOutRef.mk
  (PlutusCore.ByteString.PlutusCore.ByteStringInternal.ByteString.mk \"\")
  3)"

/-- info: Except.ok "some (-3)" -/
#guard_msgs in #eval prettyCex "(Option.some (- 3))"

-- z3's string escapes (`\u{..}`, `""`) become Lean's (`\xhh`, `\"`)
/--
info: Except.ok "PlutusCore.ByteString.PlutusCore.ByteStringInternal.ByteString.mk \"\\xc3\\xbf\\\"\\\\\""
-/
#guard_msgs in #eval prettyFull "(PlutusCore.ByteString.PlutusCore.ByteStringInternal.ByteString.mk
  \"\\u{c3}\\u{bf}\"\"\\u{5c}\")"

-- z3's "no concrete value" (an eliminated variable, an abstract element), and not
#guard isAbstractValue "$0"
#guard isAbstractValue "@@ArrowT2!val!0"
#guard !isAbstractValue "(- 3)"
#guard !isAbstractValue "\"$0\""
#guard !isAbstractValue "(PlutusCore.Data.PlutusCore.DataInternal.Data.I 5)"

-- one Blaster entry: binder, value (trailing newline and `- ` tolerated)
/-- info: Except.ok ("y", "(- 2)") -/
#guard_msgs in #eval splitEntry "- y: (- 2)\n"

/-! ## No global unexpander: goals print as before -/

/-- info: Data.I 5 : Data -/
#guard_msgs in #check Data.I 5

/-- info: Data.Constr 0 [Data.I 5, Data.B { data := "AB" }] : Data -/
#guard_msgs in #check Data.Constr 0 [Data.I 5, Data.B ⟨"AB"⟩]

/-! ## Rendering: Lean text that elaborates back to the value -/

/-- info: -3   [short]   -3 -/
#guard_msgs in #cex_lean Int, "(- 3)"

/-- info: Data.I (-5)   [short]   {"int":-5} -/
#guard_msgs in #cex_lean Data, "(PlutusCore.Data.PlutusCore.DataInternal.Data.I (- 5))"

/-- info: Data.Map [(Data.I 1, Data.B ⟨"a"⟩)]   [short]   {"map":[{"k":{"int":1},"v":{"bytes":"61"}}]} -/
#guard_msgs in #cex_lean Data, "(let ((a!1 (List.cons (Prod.mk (PlutusCore.Data.PlutusCore.DataInternal.Data.I 1)
    (PlutusCore.Data.PlutusCore.DataInternal.Data.B
      (PlutusCore.ByteString.PlutusCore.ByteStringInternal.ByteString.mk \"a\")))
    (as List.nil (@List (@Prod @PlutusCore.Data.PlutusCore.DataInternal.Data
                               @PlutusCore.Data.PlutusCore.DataInternal.Data))))))
  (PlutusCore.Data.PlutusCore.DataInternal.Data.Map a!1))"

/--
info: { txOutRefId := ⟨"\xc3\xbf"⟩, txOutRefIdx := 3 }   [short]   {"constructor":0,"fields":[{"bytes":"c3bf"},{"int":3}]}
-/
#guard_msgs in #cex_lean TxOutRef, "(CardanoLedgerApi.V3.Tx.TxOutRef.mk
  (PlutusCore.ByteString.PlutusCore.ByteStringInternal.ByteString.mk \"\\u{c3}\\u{bf}\")
  3)"

/--
info: [Data.I 6, Data.Constr 0 [Data.I 7]]   [short]   [{"int":6},{"constructor":0,"fields":[{"int":7}]}]
-/
#guard_msgs in #cex_lean List Data, "(List.cons (PlutusCore.Data.PlutusCore.DataInternal.Data.I 6)
  (List.cons (PlutusCore.Data.PlutusCore.DataInternal.Data.Constr 0
    (List.cons (PlutusCore.Data.PlutusCore.DataInternal.Data.I 7) List.nil)) List.nil))"

/-- info: ⟨"AB"⟩   [short]   "4142" -/
#guard_msgs in #cex_lean ByteString,
  "(PlutusCore.ByteString.PlutusCore.ByteStringInternal.ByteString.mk \"AB\")"

/-- info: some (-3)   [short]   {"constructor":0,"fields":[{"int":-3}]} -/
#guard_msgs in #cex_lean Option Int, "(Option.some (- 3))"

/-- info: (7, false)   [short]   null -/
#guard_msgs in #cex_lean Int × Bool, "(Prod.mk 7 false)"

/-- info: [true, false]   [short]   [true,false] -/
#guard_msgs in #cex_lean List Bool, "(List.cons true (List.cons false List.nil))"

-- the texts above, pasted into source, elaborate to the values (the round trip by hand)
example : (Data.I (-5) : Data) = PlutusCore.Data.PlutusCore.DataInternal.Data.I (-5) := rfl
example : (Data.Map [(Data.I 1, Data.B ⟨"a"⟩)] : Data) =
    PlutusCore.Data.PlutusCore.DataInternal.Data.Map
      [(PlutusCore.Data.PlutusCore.DataInternal.Data.I 1,
        PlutusCore.Data.PlutusCore.DataInternal.Data.B
          (PlutusCore.ByteString.PlutusCore.ByteStringInternal.ByteString.mk "a"))] := rfl
example : ({ txOutRefId := ⟨"\xc3\xbf"⟩, txOutRefIdx := 3 } : TxOutRef) =
    CardanoLedgerApi.V3.Tx.TxOutRef.mk
      (PlutusCore.ByteString.PlutusCore.ByteStringInternal.ByteString.mk "\u00c3\u00bf") 3 := rfl
example : ([Data.I 6, Data.Constr 0 [Data.I 7]] : List Data) =
    [PlutusCore.Data.PlutusCore.DataInternal.Data.I 6,
     PlutusCore.Data.PlutusCore.DataInternal.Data.Constr 0
       [PlutusCore.Data.PlutusCore.DataInternal.Data.I 7]] := rfl
example : (⟨"AB"⟩ : ByteString) = PlutusCore.ByteString.PlutusCore.ByteStringInternal.ByteString.mk "AB" := rfl

/-! ## `blaster_refute`: Blaster's model, then a refutation the kernel checks -/

theorem br_int : ¬ ∀ (x : Int), x * x ≠ 9 ∨ x > 0 := by blaster_refute
theorem br_data : ¬ ∀ (d : Data), d ≠ Data.I 5 := by blaster_refute
theorem br_txoutref : ¬ ∀ (r : TxOutRef), r.txOutRefIdx < 3 := by blaster_refute
theorem br_list_data : ¬ ∀ (xs : List Data), xs.length < 2 := by blaster_refute
theorem br_bytestring : ¬ ∀ (b : ByteString), b.data.length < 2 := by blaster_refute
theorem br_bool : ¬ ∀ (b c : Bool), (b && c) = false := by blaster_refute
theorem br_hyps : ¬ ∀ (x y : Int), x < 3 → y < x → y * 2 > -4 := by blaster_refute

/-- info: 'UplcProofTests.Cex.br_int' does not depend on any axioms -/
#guard_msgs in #print axioms br_int
/-- info: 'UplcProofTests.Cex.br_data' does not depend on any axioms -/
#guard_msgs in #print axioms br_data
/-- info: 'UplcProofTests.Cex.br_txoutref' does not depend on any axioms -/
#guard_msgs in #print axioms br_txoutref
/-- info: 'UplcProofTests.Cex.br_list_data' does not depend on any axioms -/
#guard_msgs in #print axioms br_list_data
/-- info: 'UplcProofTests.Cex.br_bytestring' does not depend on any axioms -/
#guard_msgs in #print axioms br_bytestring
/-- info: 'UplcProofTests.Cex.br_bool' does not depend on any axioms -/
#guard_msgs in #print axioms br_bool
/-- info: 'UplcProofTests.Cex.br_hyps' does not depend on any axioms -/
#guard_msgs in #print axioms br_hyps

/-! ## `refute_with`, `refute_cex` -/

theorem rw_data_eq : ¬ ∀ (d : Data), d = Data.I 5 := by refute_with Data.I 4
theorem rw_txoutref : ¬ ∀ (r : TxOutRef), r.txOutRefIdx < 3 := by
  refute_with { txOutRefId := ⟨""⟩, txOutRefIdx := 3 }
theorem rw_or : ¬ ∀ (x : Int), x < 0 ∨ x > 10 := by refute_with 5
theorem rc_hyps : ¬ ∀ (x y : Int), x < 3 → y < x → y * 2 > -4 := by
  refute_cex "x: 0", "- y: (- 2)\n"
theorem rc_list_data : ¬ ∀ (xs : List Data), xs.length < 2 := by
  refute_cex "xs: (List.cons (PlutusCore.Data.PlutusCore.DataInternal.Data.I 6)
           (List.cons (PlutusCore.Data.PlutusCore.DataInternal.Data.I 7)
                      (as List.nil
                          (@List @PlutusCore.Data.PlutusCore.DataInternal.Data))))"
theorem rc_map : ¬ ∀ (d : Data), d ≠ Data.Map [(Data.I 1, Data.B ⟨"a"⟩)] := by
  refute_cex "d: (let ((a!1 (List.cons (Prod.mk (PlutusCore.Data.PlutusCore.DataInternal.Data.I 1)
    (PlutusCore.Data.PlutusCore.DataInternal.Data.B
      (PlutusCore.ByteString.PlutusCore.ByteStringInternal.ByteString.mk \"a\")))
    (as List.nil (@List (@Prod @PlutusCore.Data.PlutusCore.DataInternal.Data
                               @PlutusCore.Data.PlutusCore.DataInternal.Data))))))
  (PlutusCore.Data.PlutusCore.DataInternal.Data.Map a!1))"

/-- info: 'UplcProofTests.Cex.rw_data_eq' depends on axioms: [propext] -/
#guard_msgs in #print axioms rw_data_eq
/-- info: 'UplcProofTests.Cex.rw_txoutref' does not depend on any axioms -/
#guard_msgs in #print axioms rw_txoutref
/-- info: 'UplcProofTests.Cex.rw_or' does not depend on any axioms -/
#guard_msgs in #print axioms rw_or
/-- info: 'UplcProofTests.Cex.rc_hyps' does not depend on any axioms -/
#guard_msgs in #print axioms rc_hyps
/-- info: 'UplcProofTests.Cex.rc_list_data' does not depend on any axioms -/
#guard_msgs in #print axioms rc_list_data
/-- info: 'UplcProofTests.Cex.rc_map' does not depend on any axioms -/
#guard_msgs in #print axioms rc_map

-- `refuteWithValues`, the API behind them, with values already elaborated
open Lean Elab Tactic in
/-- info: closer decide, binders [x, y], conclusion -2 * 2 > -4 -/
#guard_msgs in
theorem rv_hyps : ¬ ∀ (x y : Int), x < 3 → y < x → y * 2 > -4 := by
  run_tac do
    let r ← refuteWithValues (← getMainGoal) #[toExpr (0 : Int), toExpr (-2 : Int)]
    logInfo m!"closer {r.closer}, binders {r.binders.toList.map (·.name)}, conclusion {r.conclusion}"
    replaceMainGoal []

/-- info: 'UplcProofTests.Cex.rv_hyps' does not depend on any axioms -/
#guard_msgs in #print axioms rv_hyps

-- binders the entries leave out (Blaster omits unconstrained ones) get a default value,
-- named in an info message: `default`, or the first constructor with default arguments
-- for types without an `Inhabited` instance (`Data`, `TxOutRef`)
/-- info: refute_cex: no concrete value in the counterexample, set to a default value: y := 0 -/
#guard_msgs in
theorem rc_default : ¬ ∀ (x y : Int), x < 3 ∨ y ≠ y := by
  refute_cex "x: 3"

/--
info: refute_cex: no concrete value in the counterexample, set to a default value: d := Data.Constr 0 [], b := false
-/
#guard_msgs in
theorem rc_default_data : ¬ ∀ (x : Int) (d : Data) (b : Bool), x < 3 ∨ d = Data.I 1 ∨ b := by
  refute_cex "x: 3"

/--
info: refute_cex: no concrete value in the counterexample, set to a default value: r := { txOutRefId := ⟨""⟩, txOutRefIdx := 0 }
-/
#guard_msgs in
theorem rc_default_txoutref : ¬ ∀ (r : TxOutRef) (x : Int), x < r.txOutRefIdx + 3 := by
  refute_cex "x: 3"

-- z3's abstract value (`$0`, an unconstrained binder) is treated the same way
/--
info: refute_cex: no concrete value in the counterexample, set to a default value: r := { txOutRefId := ⟨""⟩, txOutRefIdx := 0 }
-/
#guard_msgs in
theorem rc_default_abstract : ¬ ∀ (r : TxOutRef) (x : Int), x < r.txOutRefIdx + 3 := by
  refute_cex "r: $0", "x: 3"

/-- info: 'UplcProofTests.Cex.rc_default_abstract' does not depend on any axioms -/
#guard_msgs in #print axioms rc_default_abstract
/-- info: 'UplcProofTests.Cex.rc_default' does not depend on any axioms -/
#guard_msgs in #print axioms rc_default
/-- info: 'UplcProofTests.Cex.rc_default_data' depends on axioms: [propext] -/
#guard_msgs in #print axioms rc_default_data
/-- info: 'UplcProofTests.Cex.rc_default_txoutref' does not depend on any axioms -/
#guard_msgs in #print axioms rc_default_txoutref

/-! ## A closer that runs out of heartbeats does not stop the next ones

With `maxHeartbeats 100`, `decide` alone runs out on this conclusion; `refute_with`
tries it first (it fails, its work is undone and not counted), then `rfl` closes it. -/

/--
error: (deterministic) timeout at `whnf`, maximum number of heartbeats (100) has been reached

Note: Use `set_option maxHeartbeats <num>` to set the limit.

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
set_option maxHeartbeats 100 in
example : ¬ ((List.range 300).sum ≠ (List.range 300).sum) := by decide

set_option maxHeartbeats 100 in
theorem hb_refute_with : ¬ ∀ (n : Nat), (List.range n).sum ≠ (List.range n).sum := by
  refute_with 300

set_option maxHeartbeats 100 in
theorem hb_refute_cex : ¬ ∀ (n : Nat), (List.range n).sum ≠ (List.range n).sum := by
  refute_cex "n: 300"

/-- info: 'UplcProofTests.Cex.hb_refute_with' does not depend on any axioms -/
#guard_msgs in #print axioms hb_refute_with
/-- info: 'UplcProofTests.Cex.hb_refute_cex' does not depend on any axioms -/
#guard_msgs in #print axioms hb_refute_cex

-- the closers in order, under the same budget: what stopped `decide`, and which closed it
open Lean Elab Tactic Meta in
/--
info: decide: (deterministic) timeout at `whnf`, maximum number of heartbeats (100) has been reached
---
info: rfl: closed
-/
#guard_msgs in
example : True := by
  run_tac withTheReader Core.Context (fun c => { c with maxHeartbeats := 100 * 1000 }) <|
    withCurrHeartbeats do
      let g ← mkFreshExprSyntheticOpaqueMVar
        (← Term.elabTerm (← `(¬ ((List.range 300).sum ≠ (List.range 300).sum))) none)
      for c in refuteClosers do
        let r ← runCloser g.mvarId! c
        logInfo m!"{c.name}: {(r.map fun s => (s.splitOn "\n").headD s).getD "closed"}"
        if r.isNone then break
  trivial

/-! ## `blaster_pretty`: the message on a false goal -/

/--
error: UPLC-RESULT {"status":"refuted","kernel":true,"cex":{"x":-3},"lean":{"x":"-3"},"closer":"decide"}
Counterexample (refutation checked by the kernel, closer decide):
  x := -3
Refutation:
example : ¬∀ (x : Int), x * x ≠ 9 ∨ x > 0 := by
  refute_with -3
-/
#guard_msgs in
example : ∀ (x : Int), x * x ≠ 9 ∨ x > 0 := by blaster_pretty

-- free variables and hypotheses of the goal are quantified in the refuted statement
/--
error: UPLC-RESULT {"status":"refuted","kernel":true,"cex":{"x":4},"lean":{"x":"4"},"closer":"decide"}
Counterexample (refutation checked by the kernel, closer decide):
  x := 4
Refutation:
example : ¬∀ (x : Int), x > 3 → x > 4 := by
  refute_with 4
-/
#guard_msgs in
example (x : Int) (h : x > 3) : x > 4 := by blaster_pretty

/--
error: UPLC-RESULT {"status":"refuted","kernel":true,"cex":{"d":{"int":5}},"lean":{"d":"Data.I 5"},"closer":"rfl"}
Counterexample (refutation checked by the kernel, closer rfl):
  d := Data.I 5
Refutation:
example : ¬∀ (d : Data), d ≠ Data.I 5 := by
  refute_with Data.I 5
-/
#guard_msgs in
example : ∀ (d : Data), d ≠ Data.I 5 := by blaster_pretty

/--
error: UPLC-RESULT {"status":"refuted","kernel":true,"cex":{"r":{"constructor":0,"fields":[{"bytes":""},{"int":3}]}},"lean":{"r":"{ txOutRefId := ⟨\"\"⟩, txOutRefIdx := 3 }"},"closer":"decide"}
Counterexample (refutation checked by the kernel, closer decide):
  r := { txOutRefId := ⟨""⟩, txOutRefIdx := 3 }
Refutation:
example : ¬∀ (r : TxOutRef), r.txOutRefIdx < 3 := by
  refute_with { txOutRefId := ⟨""⟩, txOutRefIdx := 3 }
-/
#guard_msgs in
example : ∀ (r : TxOutRef), r.txOutRefIdx < 3 := by blaster_pretty

/--
error: UPLC-RESULT {"status":"refuted","kernel":true,"cex":{"xs":[{"int":6},{"int":7}]},"lean":{"xs":"[Data.I 6, Data.I 7]"},"closer":"decide"}
Counterexample (refutation checked by the kernel, closer decide):
  xs := [Data.I 6, Data.I 7]
Refutation:
example : ¬∀ (xs : List Data), xs.length < 2 := by
  refute_with [Data.I 6, Data.I 7]
-/
#guard_msgs in
example : ∀ (xs : List Data), xs.length < 2 := by blaster_pretty

/--
error: UPLC-RESULT {"status":"refuted","kernel":true,"cex":{"d":{"map":[{"k":{"int":1},"v":{"bytes":"61"}}]}},"lean":{"d":"Data.Map [(Data.I 1, Data.B ⟨\"a\"⟩)]"},"closer":"rfl"}
Counterexample (refutation checked by the kernel, closer rfl):
  d := Data.Map [(Data.I 1, Data.B ⟨"a"⟩)]
Refutation:
example : ¬∀ (d : Data), d ≠ Data.Map [(Data.I 1, Data.B { data := "a" })] := by
  refute_with Data.Map [(Data.I 1, Data.B ⟨"a"⟩)]
-/
#guard_msgs in
example : ∀ (d : Data), d ≠ Data.Map [(Data.I 1, Data.B ⟨"a"⟩)] := by blaster_pretty

/--
error: UPLC-RESULT {"status":"refuted","kernel":true,"cex":{"b":"4142"},"lean":{"b":"⟨\"AB\"⟩"},"closer":"decide"}
Counterexample (refutation checked by the kernel, closer decide):
  b := ⟨"AB"⟩
Refutation:
example : ¬∀ (b : ByteString), b.data.length < 2 := by
  refute_with ⟨"AB"⟩
-/
#guard_msgs in
example : ∀ (b : ByteString), b.data.length < 2 := by blaster_pretty

/--
error: UPLC-RESULT {"status":"refuted","kernel":true,"cex":{"b":true,"c":true},"lean":{"b":"true","c":"true"},"closer":"decide"}
Counterexample (refutation checked by the kernel, closer decide):
  b := true
  c := true
Refutation:
example : ¬∀ (b c : Bool), (b && c) = false := by
  refute_with true, true
-/
#guard_msgs in
example : ∀ (b c : Bool), (b && c) = false := by blaster_pretty

-- a binder Blaster's model leaves out gets `default` (key "defaults")
/--
error: UPLC-RESULT {"status":"refuted","kernel":true,"cex":{"x":3,"y":0},"lean":{"x":"3","y":"0"},"closer":"decide","defaults":["y"]}
Counterexample (refutation checked by the kernel, closer decide):
  x := 3
  y := 0  -- not in Blaster's model: default
Refutation:
example : ¬∀ (x y : Int), x < 3 := by
  refute_with 3, 0
-/
#guard_msgs in
example : ∀ (x y : Int), x < 3 := by blaster_pretty

-- z3 gives no concrete value (`$0`) for an unconstrained `TxOutRef` (no `Inhabited`
-- instance): the first constructor with default arguments is used
/--
error: UPLC-RESULT {"status":"refuted","kernel":true,"cex":{"r":{"constructor":0,"fields":[{"bytes":""},{"int":0}]},"x":3},"lean":{"r":"{ txOutRefId := ⟨\"\"⟩, txOutRefIdx := 0 }","x":"3"},"closer":"decide","defaults":["r"]}
Counterexample (refutation checked by the kernel, closer decide):
  r := { txOutRefId := ⟨""⟩, txOutRefIdx := 0 }  -- no concrete value in Blaster's model ($0): default
  x := 3
Refutation:
example : ¬∀ (r : TxOutRef) (x : Int), x < 3 ∨ r ≠ r := by
  refute_with { txOutRefId := ⟨""⟩, txOutRefIdx := 0 }, 3
-/
#guard_msgs in
example : ∀ (r : TxOutRef) (x : Int), x < 3 ∨ r ≠ r := by blaster_pretty

-- the snippets of these messages, pasted back
theorem bp_int : ¬∀ (x : Int), x * x ≠ 9 ∨ x > 0 := by
  refute_with -3
theorem bp_hyp : ¬∀ (x : Int), x > 3 → x > 4 := by
  refute_with 4
theorem bp_map : ¬∀ (d : Data), d ≠ Data.Map [(Data.I 1, Data.B { data := "a" })] := by
  refute_with Data.Map [(Data.I 1, Data.B ⟨"a"⟩)]
theorem bp_txoutref : ¬∀ (r : TxOutRef), r.txOutRefIdx < 3 := by
  refute_with { txOutRefId := ⟨""⟩, txOutRefIdx := 3 }

/-- info: 'UplcProofTests.Cex.bp_int' does not depend on any axioms -/
#guard_msgs in #print axioms bp_int
/-- info: 'UplcProofTests.Cex.bp_hyp' does not depend on any axioms -/
#guard_msgs in #print axioms bp_hyp
/-- info: 'UplcProofTests.Cex.bp_map' does not depend on any axioms -/
#guard_msgs in #print axioms bp_map
/-- info: 'UplcProofTests.Cex.bp_txoutref' does not depend on any axioms -/
#guard_msgs in #print axioms bp_txoutref

/-! ## A `Halts` claim on a real Aiken script, refuted by running it

`factorial` (`Tests/Induction/Scripts/factorial.hex`): the claim `factorial n = n`
holds only at `n = 1, 2`; it is refuted at `n = 3` (`3! = 6`). -/

open PlutusCore.UPLC.Term PlutusCore.UPLC.CekValue PlutusCore.UPLC.CekMachine
open UplcProof

/-- info: Successfully decoded single CBOR hex 'Tests/Induction/Scripts/factorial.hex' -/
#guard_msgs in
#import_uplc UplcProofTests.Cex.factorialHex PlutusV3 single_cbor_hex
  "Tests/Induction/Scripts/factorial.hex"

def intV (x : Int) : CekValue := .VCon (.Integer x)

theorem factorial_ne_id : ¬ ∀ (n : Int), Halts factorialHex.script [int n] (intV n) := by
  refute_with 3
theorem factorial_ne_id_cex : ¬ ∀ (n : Int), Halts factorialHex.script [int n] (intV n) := by
  refute_cex "n: 3"
-- a `Halts` hypothesis is discharged by running the script too
theorem factorial_hyp : ¬ ∀ (n : Int), Halts factorialHex.script [int n] (intV 6) → n = 4 := by
  refute_with 3
-- `Fails` refuted: the run halts
theorem factorial_not_fails : ¬ ∀ (n : Int), Fails factorialHex.script [int n] := by
  refute_with 3

/-- info: 'UplcProofTests.Cex.factorial_ne_id' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms factorial_ne_id
/-- info: 'UplcProofTests.Cex.factorial_ne_id_cex' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms factorial_ne_id_cex
/-- info: 'UplcProofTests.Cex.factorial_hyp' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms factorial_hyp
/-- info: 'UplcProofTests.Cex.factorial_not_fails' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms factorial_not_fails

/-! ## A run longer than the heartbeat budget

`fib` (`Tests/Induction/Scripts/fib.hex`) at `n = 10`: 7,971 CEK steps, about
32,000 heartbeats, more than the budget set here (20,000; the same holds at the
default 200,000 from `n = 14`, 54,861 steps, about 222,000 heartbeats, too costly
to check here). The run itself has no limit and does not count against the
closer, which goes on (`v ≠ w`) within its own budget. (Before that, the closer
failed with a heartbeat timeout after the run, and `refute_with` with "no closer
proves".) -/

/-- info: Successfully decoded single CBOR hex 'Tests/Induction/Scripts/fib.hex' -/
#guard_msgs in
#import_uplc UplcProofTests.Cex.fibHex PlutusV3 single_cbor_hex
  "Tests/Induction/Scripts/fib.hex"

set_option maxHeartbeats 20000 in
theorem fib_10_ne_zero : ¬ Halts fibHex.script [int 10] (intV 0) := by
  uplc_cex_closer

set_option maxHeartbeats 20000 in
theorem fib_10_refuted : ¬ ∀ (n : Int), Halts fibHex.script [int n] (intV 0) := by
  refute_with 10

/-- info: 'UplcProofTests.Cex.fib_10_ne_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms fib_10_ne_zero
/-- info: 'UplcProofTests.Cex.fib_10_refuted' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms fib_10_refuted

end UplcProofTests.Cex
