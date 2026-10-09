# Validator fixtures

Two Plutus V3 validators, copied verbatim (the `compiledCode` field, single-CBOR
hex, no trailing newline) from the blueprint `plutus.json` of
[aiken-blaster-examples](https://github.com/txpipe-shop/aiken-blaster-examples) (compiled
with Aiken v1.1.22+39d6b04; the validators' sources are `validators/time_lock.ak`
and `validators/vault.ak` there).

| File | Blueprint title | Script hash | Parameters, then |
|---|---|---|---|
| `time_lock.hex` | `time_lock.time_lock.spend` | `94c1401b1e12f94f8128fc2f368555bd3e3def56708937594917431d` | the `ScriptContext` |
| `vault.hex` | `vault.vault.spend` | `596e80a69c51ebbe2843b05c03f973fd16035f045c77b0de6495d4b3` | `seed_utxo : OutputReference`, then the `ScriptContext` |

The same program serves every handler of a validator (`spend`, `mint`, `else`
share one hash): it dispatches on the `ScriptInfo` of the context.

`UplcProofTests/ScriptContext.lean` loads them with
`#import_uplc … PlutusV3 single_cbor_hex "Tests/Validators/<file>"` (paths relative
to the package root) and applies them, as the ledger does, to their parameters and
the context, each as a `Data` constant (`UplcProof.data`): `time_lock` to
`[data (IsData.toData ctx)]`, `vault` to `[data seed, data (IsData.toData ctx)]`.

To refresh: copy `compiledCode` of the two titles from a rebuilt `plutus.json`
(`aiken build` there); the counterexamples in the test are tied to these scripts.
