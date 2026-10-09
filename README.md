# UplcProof

Prove properties of compiled Aiken (UPLC) scripts in Lean 4 for all inputs, not
just random samples. When a property is false, you get a counterexample, and
Lean's kernel checks it too.

## Install

Lean `v4.24.0`. In your `lakefile.toml`:

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

## Example: a loop, for every input

`#import_uplc` loads a script compiled by `aiken export`. `Halts s args v` says
that running `s` on `args` ends with the value `v`; `int n` passes `n` the way
`aiken export` does.

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
because 100 random pairs rarely hit `amount = cap + 1`.

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

In Lean, `uplc_auto` finds the bug:

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

With `cap = -1` and `amount = 0` the vault accepts a withdrawal above its cap.
The last two lines are a Lean proof that the property is false. With the bug
fixed, the same `uplc_auto` proves the property.

The property covers every `cap` and `amount`, in the one transaction the test
builds. For claims about a validator's own script, over a whole `ScriptContext`,
see `UplcProofTests/ScriptContext.lean`: there the kernel checks Blaster's
counterexamples against two validators of
[aiken-blaster-examples](https://github.com/txpipe-shop/aiken-blaster-examples)
(`time_lock` in about 0.35 s, `vault` in about 1.2 s).

## Tactics

| name | what it does |
|---|---|
| `uplc_induction n` | a loop, for every `n` (an `Int` counting down, or a list) |
| `uplc_run` | runs a script on symbolic inputs, splitting on each `if` |
| `uplc_auto` | an Aiken property test: looks for a counterexample with Blaster (an SMT solver), then tries `uplc_run` and `uplc_induction` |
| `refute_with v₁, …` | proves a property false from given values; `blaster_refute` finds the values with Blaster |
| `Reachable.invariant` | a property that every step keeps holds in every reachable state |

## What a result means

The first line of the message of `uplc_auto` (and of the `blaster_*` tactics) is
JSON for tools. Its `status` is one of:

- `proved`: a Lean proof, checked by the kernel.
- `refuted`: a counterexample, with a proof (checked by the kernel) that the
  property is false.
- `oracle`: Blaster says the property holds, but there is no Lean proof. This
  is not a proof.
- `falsified`, `unknown`, `error`: neither a proof nor a refutation. See the
  module docs of `UplcProof/Auto.lean`.

`blaster_pretty` is the one exception: like Blaster's own `blaster`, it closes a
goal with an axiom when Blaster says it holds. `#print axioms` shows it: anything
beyond `propext`, `Quot.sound` and `Classical.choice` means a step was not proved.

What you still trust: the statement you wrote, the definitions of `Halts` and
`Fails`, PlutusCore's decoder and evaluator, Lean's kernel, that the exported
function is the test's body, and how [`UplcProof.Encode`](UplcProof/Encode.lean)
passes arguments (`int x` is `Data.I x`, as in `aiken export`). `Halts` counts
machine steps, not the ledger's execution budget.

## Limits

- `uplc_induction` handles one accumulator at most, recursion on `n - 1` and/or
  `n - 2` or on a list's tail. It refuses other shapes, loops that fail for some
  inputs, and loops that branch on a symbolic `Bool`.
- `uplc_auto` does not guess what a loop computes: pass it with `(loop := …)`, or
  a true property ends as `oracle`.

## Tests

`lake build` builds the library and the tests in `UplcProofTests/`: every
theorem with a check of its axioms, and the cases that must be refused.
`UplcProofTests/Readme.lean` checks the examples above. Fixtures are in `Tests/`:
Aiken sources with their compiled scripts, and the two scripts from
aiken-blaster-examples.

## Credits and license

Built on IOG's [PlutusCoreBlaster](https://github.com/input-output-hk/PlutusCoreBlaster),
[CardanoLedgerApiBlaster](https://github.com/input-output-hk/CardanoLedgerApiBlaster)
and [Lean-blaster](https://github.com/input-output-hk/Lean-blaster) (Apache-2.0).

Licensed under the [Apache License 2.0](LICENSE).
