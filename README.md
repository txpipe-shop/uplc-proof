# UplcProof

Prove properties of compiled Aiken (UPLC) scripts in Lean 4 for all inputs, not
just random samples. When a property is false, `uplc_auto` looks for a
counterexample, and Lean's kernel checks it.

## Install

Requires Lean `v4.24.0`. In your `lakefile.toml`:

```toml
[[require]]
name = "UplcProof"
git = "https://github.com/txpipe-shop/uplc-proof"
rev = "main"
```

If your project also requires PlutusCore, CardanoLedgerApi or Blaster, use the
revisions in this package's `lakefile.toml`. `uplc_auto` and the `blaster_*`
tactics need Z3 on your `PATH` (see
[Lean-blaster's README](https://github.com/input-output-hk/Lean-blaster)). Then:

```lean
import UplcProof
open UplcProof
```

## Example: a loop, for every natural `n`

`#import_uplc name …` reads a hex file holding the `compiledCode` of the JSON that
`aiken export` prints (see [`export.sh`](Tests/Auto/aiken/export.sh); paths are
relative to your project's root) and defines `name.script`. `Halts s args v` says
that running `s` on `args` ends with the value `v` (`Fails s args`: it never ends
with a value); `int n` passes `n` the way `aiken export` does.

```lean
#import_uplc factorialScript PlutusV3 single_cbor_hex "Tests/Induction/Scripts/factorial.hex"

def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

theorem factorial_halts (n : Nat) :
    Halts factorialScript.script [int n] (.VCon (.Integer (fact n))) := by
  uplc_induction n
```

## Example: a bug in a validator

This vault should accept a withdrawal only up to the `cap` in its datum, but it
checks `redeemer - 1 <= d.cap`. Its property test usually passes `aiken check`,
because its 100 random pairs hit `amount = cap + 1` in only about one run in five.

To use the test in Lean, copy its body into a function of the test's inputs and
export that function with `aiken export`
([`vault_bug.ak`](Tests/Auto/aiken/validators/vault_bug.ak)):

```aiken
pub fn prop_bug_accepts_only_up_to_cap_body(cap: Int, amount: Int) -> Bool {
  let ok =
    vault_bug.spend(Some(Datum { cap }), amount, OutputReference(#"00", 0), transaction.placeholder)
  if ok {
    amount <= cap
  } else {
    True
  }
}
```

In Lean, `uplc_auto` finds the bug (the option drops timings from the output):

```lean
set_option uplc.cex.timings false

#import_uplc vaultBugProp PlutusV3 single_cbor_hex
  "Tests/Auto/Scripts/prop_bug_accepts_only_up_to_cap.hex"

example : ∀ (cap amount : Int), Halts vaultBugProp.script [int cap, int amount] vTrue := by
  uplc_auto
```

```
error: UPLC-RESULT {"status":"refuted","kernel":true,"cex":{"cap":-1,"amount":0},"lean":{"cap":"-1","amount":"0"},"closer":"uplc_cex_closer","fuel":250}
Counterexample (refutation checked by the kernel, closer uplc_cex_closer):
  cap := -1
  amount := 0
Refutation:
example : ¬∀ (cap amount : Int), Halts vaultBugProp.script [int cap, int amount] vTrue := by
  refute_with -1, 0
```

With `cap = -1` and `amount = 0`, the vault accepts a withdrawal above its cap.
The last two lines are a Lean proof that the property is false. With the bug
fixed, the same `uplc_auto` proves the property.

The property covers every `cap` and `amount`, in the one transaction the test
builds, for the validator as compiled into the test (not the script in
`plutus.json`). For the deployed script, over a whole `ScriptContext`, see
[`UplcProofTests/ScriptContext.lean`](UplcProofTests/ScriptContext.lean): there
the kernel checks Blaster's counterexamples against two validators of TxPipe's
aiken-blaster-examples (not public yet); each refutation takes about 0.35 s
(`time_lock`) or 1.2 s (`vault`).

## Tactics and theorems

| name | what it does |
|---|---|
| `uplc_induction n` | proves a loop correct for every `n : Nat` (passed as `int n`) or every list `n` |
| `uplc_run` | runs a script on symbolic inputs, splitting on each `if` |
| `uplc_auto` | proves or refutes an Aiken property test: looks for a counterexample with Blaster (an SMT tactic backed by Z3), then tries `uplc_run` and `uplc_induction` |
| `refute_with v₁, …` | proves a property false from given values; `blaster_refute` finds the values with Blaster. `_` leaves a script context open: the hypothesis `Halts ctx … (VCon (Data c))` gives it by running `ctx`; a hypothesis `Verdict v c ok` is checked by running the validator |
| `Reachable.invariant` (theorem) | a property that holds initially and that every step keeps holds in every reachable state |

## What a result means

The first line of the message of `uplc_auto` (and of the `blaster_*` tactics) is
`UPLC-RESULT` followed by JSON, for tools. Its `status` is one of:

- `proved`: a Lean proof, checked by the kernel.
- `refuted`: a counterexample, with a proof (checked by the kernel) that the
  property is false.
- `oracle`: Blaster found no counterexample (`uplc_auto` checks runs of up to
  `fuel` steps), but there is no Lean proof. This is not a proof.
- `falsified`, `unknown`, `error`: neither a proof nor a refutation. See the
  module docs of [`UplcProof/Auto.lean`](UplcProof/Auto.lean) and
  [`UplcProof/Cex.lean`](UplcProof/Cex.lean).

One exception: when Blaster says a goal holds, `blaster_pretty` closes it with an
axiom, as Blaster's own `blaster` does. `#print axioms` shows it: anything beyond
`propext`, `Quot.sound` and `Classical.choice` means a step was not proved.

What you still trust: the statement you wrote, the definitions of `Halts` and
`Fails`, PlutusCore's decoder and evaluator, Lean's kernel, that the exported
function is the test's body, and how [`UplcProof.Encode`](UplcProof/Encode.lean)
passes arguments (`int x` is `Data.I x`, as in `aiken export`). `Halts` means the
script halts after some number of steps; it says nothing about the ledger's
execution budget. Building PlutusCore prints a few `declaration uses 'sorry'`
warnings: UplcProof's theorems do not depend on those declarations, and
`#print axioms` would show it if yours did.

## Limits

- `uplc_induction` handles recursion on `n - 1` and/or `n - 2`, or on a list's
  tail, with at most one accumulator. It refuses other shapes, loops that fail for
  some inputs, and loops that branch on a symbolic `Bool`.
- `uplc_auto` does not guess what a loop computes: pass it with `(loop := …)`, or
  a true property ends as `oracle`.

## Tests

`lake build` builds the library and the tests in `UplcProofTests/`: every
theorem with a check of its axioms, the cases that must be refused, and wrong
proof steps that Lean's kernel must reject.
`UplcProofTests/Readme.lean` checks the examples above. Fixtures are in `Tests/`:
Aiken sources with their compiled scripts, and the two scripts from TxPipe's
aiken-blaster-examples.

## Credits and license

Built on IOG's [PlutusCoreBlaster](https://github.com/input-output-hk/PlutusCoreBlaster),
[CardanoLedgerApiBlaster](https://github.com/input-output-hk/CardanoLedgerApiBlaster)
and [Lean-blaster](https://github.com/input-output-hk/Lean-blaster) (Apache-2.0).

Licensed under the [Apache License 2.0](LICENSE).
