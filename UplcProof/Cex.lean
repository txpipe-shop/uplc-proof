import UplcProof.Cex.Pretty
import UplcProof.Cex.Bridge
import UplcProof.Cex.Value
import UplcProof.Cex.Render
import UplcProof.Cex.Json
import UplcProof.Cex.Refute
import UplcProof.Cex.Report
import UplcProof.Cex.Tactic
import UplcProof.Cex.Halts

/-!
# `UplcProof.Cex`: counterexamples that are Lean, refutations the kernel checks

When Blaster (an SMT tactic, z3) finds a counterexample to a goal, this module
turns it into (a) JSON for tools, (b) Lean source that elaborates, in the file
where the tactic ran, back to the same value, and (c) a refutation of the
statement checked by the kernel, with no axiom beyond `propext`, `Quot.sound`,
`Classical.choice`. A Blaster "valid" without a kernel proof is reported as
`oracle`, never as proved.

## Tactics

* `refute_with t₁, …, tₙ` — closes `¬ ∀ (x₁ : α₁) … (xₙ : αₙ), P` at the given
  values (hypotheses of the statement discharged at the values; `P[t̄]` refuted
  by `decide`, rfl-based closers, `simp`, the concrete CEK run for `Halts`/`Fails`).
* `refute_cex "x: <raw z3>", …` — the same from Blaster's raw entries, matched by
  binder name; an unknown name is an error, a binder the entries leave out gets
  `default` (named in an info message), as in `blaster_pretty`.
* `blaster_refute (opts)*` — on `¬ S`: Blaster on `S`, then the refutation.
* `blaster_pretty (opts)*` — a drop-in for `blaster` that reports (below).
* `uplc_cex_closer` — the extension point the refuting closers end with.

## Output contract (for tools; `uplc_auto` uses it too)

`blaster_pretty` fails (counterexample) or logs an info message (valid,
undetermined) whose **first line** is

```
UPLC-RESULT {"status":…,"kernel":…,"cex":{name: json},"lean":{name: "lean text"}}
```

one line of valid JSON, keys in this order:

* `"status"`: `"refuted"` (Blaster found a model and a refutation built from it
  was checked by the kernel) | `"falsified"` (Blaster found a model, but no
  kernel-checked refutation could be built: never call it refuted) | `"oracle"`
  (Blaster says the goal holds; there is no kernel proof. `blaster_pretty` then
  closes the goal with the axiom `Blaster.Tactic.blasterProven`, as `blaster`
  does; `blaster_refute` and `uplc_auto` fail) | `"unknown"` (Blaster could not
  decide, or failed);
* `"kernel"`: `true` iff the refutation was checked by the kernel (`refuted`);
* `"cex"`: binder name ↦ JSON value (`UplcProof.Cex.Json`: numbers, booleans,
  `ByteString` as a hex string, lists as arrays, `Data` in Cardano's detailed
  schema `{"int":n}` | `{"bytes":"hex"}` | `{"list":[…]}` |
  `{"map":[{"k":…,"v":…}]}` | `{"constructor":n,"fields":[…]}`, other types
  through `IsData.toData`, else `null`);
* `"lean"`: binder name ↦ Lean text of the value (one line; it elaborated back
  to the value at the binder's type in this file), or `null` if none does.

Optional keys, after these: `"closer"` (what refuted the conclusion),
`"defaults"` (binders with no concrete value in Blaster's model, set to a
default), `"reason"` (why there is no kernel-checked refutation, or why Blaster
failed), `"ms"` (milliseconds per phase: `blaster`, `refute`, `render`; off with
`set_option uplc.cex.timings false`). Each key appears once. Binder names are
the statement's, with `_1`, `_2` appended to repeated ones (`distinctNames`).
`uplc_auto` extends this contract: statuses `proved` (an info message) and
`error`, keys `method`, `leaf`, `blaster`, `fuel`, `spurious` (see
`UplcProof.Auto`).

The human-readable lines that follow: the counterexample as `  name := <lean>`
lines, then the refutation as a ready-to-paste snippet. With
`set_option uplc.cex.timings false`:

```
UPLC-RESULT {"status":"refuted","kernel":true,"cex":{"x":-3},"lean":{"x":"-3"},"closer":"decide"}
Counterexample (refutation checked by the kernel, closer decide):
  x := -3
Refutation:
example : ¬∀ (x : Int), x * x ≠ 9 ∨ x > 0 := by
  refute_with -3
```

The refuted statement is `∀ (free variables and hypotheses of the goal), goal`;
the kernel checks a proof of its negation.
Once Blaster has been called, `blaster_refute`'s errors also start with an
`UPLC-RESULT` line. When Blaster itself fails (an error, or a runtime exception
such as deep recursion on a large term), `blaster_pretty` and `blaster_refute`
fail with status `unknown` and Blaster's message in `"reason"`; Blaster's own
log messages are dropped.

## Lean API (for `uplc_auto`)

* `elabCexValue (raw : String) (expectedType : Expr) : TermElabM (Expr × String)` —
  z3 text to a closed value at the binder type (and the clean text).
* `prettyFull (raw : String) : Except String String`, `prettyCex`, `splitEntry`.
* `renderLean (value type : Expr) (source? : Option String := none) : TermElabM (Option Rendered)` —
  round-trip-checked Lean text (`Rendered.line`, `Rendered.pretty`).
* `jsonOf (value type : Expr) : MetaM Json`.
* `mkEntry (name : String) (value type : Expr) (source? z3? note? : Option String := none)
  (isDefault := false) : TermElabM Entry`; `Report`, `Report.resultLine`, `Report.message`;
  `distinctNames` (the `_1`, `_2` suffixes), `jsonStr`, `jsonObj` (`Report`).
* `refuteCore`, `refuteWithValues`, `refuteWithEntries` (`Refute`); `checkAxioms`,
  `kernelCheck`.
* `runBlaster`, `collectValues`, `analyse`, `blasterReport` (`Tactic`).
-/
