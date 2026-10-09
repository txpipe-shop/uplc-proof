import Lean
import CardanoLedgerApi.IsData.Class
import UplcProof.Cex.Value

/-!
# `UplcProof.Cex.Json`: a value as JSON, for tools

`jsonOf v ty` is directed by the binder's type `ty`:

| type | JSON |
|---|---|
| `Int`, `Nat` (`Integer`) | number |
| `Bool` | `true` / `false` |
| `String` | string |
| `ByteString` | hex string, as Aiken's `#"…"` (`null` if a character is not a byte) |
| `List α` | array |
| `Data` | Cardano's detailed schema: `{"int":n}`, `{"bytes":"hex"}`, `{"list":[…]}`, `{"map":[{"k":…,"v":…}]}`, `{"constructor":n,"fields":[…]}` |
| anything else with an `IsData` instance (`TxOutRef`, `ScriptContext`, …) | its `IsData.toData`, as `Data` |
| anything else | `null` |

The Lean text (`Render`) is always there; JSON is the machine-readable view of it.
-/

open Lean Meta

namespace UplcProof.Cex

private def hexDigit (n : Nat) : Char := "0123456789abcdef".get ⟨n % 16⟩

/-- The hex of a `ByteString`'s characters, or `none` if one is not a byte. -/
private def bytesHex? (s : String) : Option String :=
  s.toList.foldlM (init := "") fun acc c =>
    if c.toNat < 256 then some ((acc.push (hexDigit (c.toNat / 16))).push (hexDigit c.toNat))
    else none

/-- A `Data` value (as a `Val`) in Cardano's detailed JSON schema. -/
private partial def dataJson? : Val → Option Json
  | .ctor c _ fields _ =>
      if c == ``PlutusCore.Data.PlutusCore.DataInternal.Data.I then
        match fields with
        | #[(_, .int i)] => some (Json.mkObj [("int", toJson i)])
        | _ => none
      else if c == ``PlutusCore.Data.PlutusCore.DataInternal.Data.B then
        match fields with
        | #[(_, .bytes b)] => (bytesHex? b).map fun h => Json.mkObj [("bytes", Json.str h)]
        | _ => none
      else if c == ``PlutusCore.Data.PlutusCore.DataInternal.Data.List then
        match fields with
        | #[(_, .list xs)] => do
            let js ← xs.mapM dataJson?
            some (Json.mkObj [("list", Json.arr js)])
        | _ => none
      else if c == ``PlutusCore.Data.PlutusCore.DataInternal.Data.Map then
        match fields with
        | #[(_, .list ps)] => do
            let js ← ps.mapM fun
              | .pair k v => do
                  some (Json.mkObj [("k", ← dataJson? k), ("v", ← dataJson? v)])
              | _ => none
            some (Json.mkObj [("map", Json.arr js)])
        | _ => none
      else if c == ``PlutusCore.Data.PlutusCore.DataInternal.Data.Constr then
        match fields with
        | #[(_, .int i), (_, .list xs)] => do
            let js ← xs.mapM dataJson?
            some (Json.mkObj [("constructor", toJson i), ("fields", Json.arr js)])
        | _ => none
      else none
  | _ => none

/-- The JSON of `value : type` (see the module doc). -/
partial def jsonOf (value type : Expr) : MetaM Json := do
  let ty ← whnfR (← instantiateMVars type)
  let v ← toVal value
  if ty.isConstOf ``Int || ty.isConstOf ``Nat then
    return match v with | .int i => toJson i | _ => .null
  if ty.isConstOf ``Bool then
    return match v with | .bool b => toJson b | _ => .null
  if ty.isConstOf ``String then
    return match v with | .str s => toJson s | _ => .null
  if ty.isConstOf byteStringName then
    return match v with | .bytes s => (bytesHex? s).map Json.str |>.getD .null | _ => .null
  if ty.isConstOf dataName then
    return (dataJson? v).getD .null
  if ty.isAppOfArity ``List 1 then
    let elemTy := ty.appArg!
    -- element by element, on the `Expr`s, so each one is typed
    let mut out := #[]
    let mut e ← whnfCtor value
    repeat
      if e.isAppOfArity ``List.cons 3 then
        out := out.push (← jsonOf e.appFn!.appArg! elemTy)
        e ← whnfCtor e.appArg!
      else break
    return if e.isAppOfArity ``List.nil 1 then Json.arr out else .null
  -- through `IsData`, if the type has an instance
  try
    let inst ← synthInstance (← mkAppM ``CardanoLedgerApi.IsData.Class.IsData #[ty])
    let d ← mkAppOptM ``CardanoLedgerApi.IsData.Class.IsData.toData #[ty, inst, value]
    return (dataJson? (← toVal d)).getD .null
  catch _ => return .null

end UplcProof.Cex
