import Lean
import PlutusCore.Data

/-!
# `UplcProof.Cex.Value`: a counterexample value, read off its `Expr`

`toVal e` reads a closed value (as elaborated from z3's text, or `default`, or a
user's term) into `Val`, the shape both renderers work on (`Render` for Lean
text, `Json` for tools): literals (`Int`, `Nat`, `Bool`, `String`), a
`ByteString`, lists, pairs, options, other constructor applications (with field
names), and anything else kept as an opaque `Expr`. Subterms that are not
already literals or constructors are put in weak head normal form first
(`default`, `2 + 3`), so what is shown is the value, not how it was written.
-/

open Lean Meta

namespace UplcProof.Cex

/-- A value, as the renderers see it. -/
inductive Val where
  | int (i : Int)
  | bool (b : Bool)
  | str (s : String)
  /-- A `PlutusCore` `ByteString`: one character per byte. -/
  | bytes (s : String)
  | list (xs : Array Val)
  | pair (a b : Val)
  | some (v : Val)
  | none
  /-- A constructor application: the constructor, its inductive type, the
      explicit fields (name and value), and whether the type is a structure. -/
  | ctor (name : Name) (induct : Name) (fields : Array (Name × Val)) (struct : Bool)
  /-- Anything else, rendered by the delaborator. -/
  | opaque (e : Expr)
deriving Inhabited

/-- The constant name of `PlutusCore`'s `ByteString` type. -/
def byteStringName : Name := ``PlutusCore.ByteString.PlutusCore.ByteStringInternal.ByteString

/-- The constant name of `PlutusCore`'s `Data` type. -/
def dataName : Name := ``PlutusCore.Data.PlutusCore.DataInternal.Data

/-- A natural number literal, after weak head normalization if needed. -/
private def natVal? (e : Expr) : MetaM (Option Nat) := do
  if let some n ← getNatValue? e then return some n
  match (← whnfD e) with
  | .lit (.natVal n) => return some n
  | _ => return none

/-- An integer literal (`5`, `-3`, `Int.ofNat 5`, `Int.negSucc 2`), after weak
    head normalization if needed. -/
private def intVal? (e : Expr) : MetaM (Option Int) := do
  if let some i ← getIntValue? e then return some i
  let e' ← whnfD e
  match_expr e' with
  | Int.ofNat n => return (← natVal? n).map Int.ofNat
  | Int.negSucc n => return (← natVal? n).map Int.negSucc
  | _ => return none

/-- `e` itself if it is a constructor application with all its arguments,
    otherwise its weak head normal form. -/
def whnfCtor (e : Expr) : MetaM Expr := do
  if let .const c _ := e.getAppFn then
    if let some (.ctorInfo ci) := (← getEnv).find? c then
      if e.getAppNumArgs == ci.numParams + ci.numFields then return e
  whnfD e

/-- The explicit fields of constructor `c` (indices into its fields) with their names. -/
private def explicitFields (ci : ConstructorVal) : MetaM (Array (Nat × Name)) := do
  let env ← getEnv
  let structFields := if isStructure env ci.induct then getStructureFields env ci.induct else #[]
  forallTelescope ci.type fun xs _ => do
    let mut out := #[]
    for i in [ci.numParams : xs.size] do
      let d ← xs[i]!.fvarId!.getDecl
      if d.binderInfo.isExplicit then
        let j := i - ci.numParams
        let n := if h : j < structFields.size then structFields[j] else d.userName
        out := out.push (j, n)
    return out

/-- Reads a closed value into a `Val`. `fuel` bounds the depth. -/
partial def toVal (e : Expr) (fuel : Nat := 512) : MetaM Val := do
  let e ← instantiateMVars e
  if fuel == 0 then return .opaque e
  let ty ← whnfR (← inferType e)
  if ty.isConstOf ``Int then
    return match ← intVal? e with | .some i => .int i | .none => .opaque e
  if ty.isConstOf ``Nat then
    return match ← natVal? e with | .some n => .int n | .none => .opaque e
  if ty.isConstOf ``String then
    return match (← whnfD e) with | .lit (.strVal s) => .str s | _ => .opaque e
  let e' ← whnfCtor e
  let .const c _ := e'.getAppFn | return .opaque e
  let some (.ctorInfo ci) := (← getEnv).find? c | return .opaque e
  let args := e'.getAppArgs
  unless args.size == ci.numParams + ci.numFields do return .opaque e
  if c == ``Bool.true then return .bool true
  if c == ``Bool.false then return .bool false
  if c == ``List.nil then return .list #[]
  if c == ``List.cons then
    -- iterate along the spine, so long lists do not use depth
    let mut xs := #[← toVal args[1]! (fuel - 1)]
    let mut tl ← whnfCtor args[2]!
    repeat
      if tl.isAppOfArity ``List.cons 3 then
        xs := xs.push (← toVal tl.appFn!.appArg! (fuel - 1))
        tl ← whnfCtor tl.appArg!
      else break
    if tl.isAppOfArity ``List.nil 1 then return .list xs
    return .opaque e
  if c == ``Prod.mk then
    return .pair (← toVal args[2]! (fuel - 1)) (← toVal args[3]! (fuel - 1))
  if c == ``Option.some then return .some (← toVal args[1]! (fuel - 1))
  if c == ``Option.none then return .none
  if ci.induct == byteStringName then
    if let .lit (.strVal s) ← whnfD args[0]! then return .bytes s
    return .opaque e
  let fields ← explicitFields ci
  let mut out := #[]
  for (j, n) in fields do
    out := out.push (n, ← toVal args[ci.numParams + j]! (fuel - 1))
  return .ctor c ci.induct out (isStructure (← getEnv) ci.induct)

end UplcProof.Cex
