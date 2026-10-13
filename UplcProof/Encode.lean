import PlutusCore.UPLC
import UplcProof.Induction.Exec

/-!
# Arguments and results of exported Aiken functions

`aiken export --module m --name f` compiles `f` to a standalone program that takes
every parameter as `Data`, in the order of the Aiken parameters. The encoders here
build those arguments:

| Aiken parameter | argument | `Data` |
|---|---|---|
| `Int` | `int x` | `I x` |
| `ByteArray` | `bytes b` | `B b` |
| `Bool` | `bool b` | `Constr 0 []` (`False`), `Constr 1 []` (`True`) |
| `List<Int>` | `list xs` | `List [I x, …]` |
| `List<ByteArray>` | `bytesList bs` | `List [B b, …]` |
| `List<Bool>` | `boolList bs` | `List [Constr _ [], …]` |
| `Data`, anything else | `data d` | `d` |

The result is not wrapped in `Data`: a `Bool` result halts as `VCon (Bool b)`
(`vTrue`, `vFalse`), an `Int` as `VCon (Integer i)`, a `List<Int>` as
`VCon (ConstDataList [I i, …])`; a Plutus V3 validator accepts by halting with
`()` (`vUnit`, `Accepts`).

The encoders, the results and `Accepts` are `abbrev`s (except `boolData`, a `def`
by cases), so a claim written with them is a `Halts`/`Fails` claim for
`uplc_induction` and `uplc_run`, and `simp` sees through them. `Verdict` is a
`def`: `Verdict.accepts` and `Verdict.rejects` turn it into `Accepts s c` or
`¬ Accepts s c`.
-/

open PlutusCore.UPLC.Term PlutusCore.UPLC.CekValue PlutusCore.UPLC.CekMachine
open PlutusCore.Data (Data)

namespace UplcProof

/-! ## Arguments: every parameter of an exported Aiken function is `Data` -/

/-- An Aiken `Int` argument. -/
abbrev int (x : Int) : Term := .Const (.Data (.I x))

/-- An Aiken `ByteArray` argument. -/
abbrev bytes (b : PlutusCore.ByteString.ByteString) : Term := .Const (.Data (.B b))

/-- Aiken's `Bool` as `Data`: `False = Constr 0 []`, `True = Constr 1 []`. -/
def boolData : Bool → Data
  | false => .Constr 0 []
  | true => .Constr 1 []

/-- An Aiken `Bool` argument. -/
abbrev bool (b : Bool) : Term := .Const (.Data (boolData b))

/-- An argument already in `Data` form (`fuzz.data()`, records, opaque types). -/
abbrev data (d : Data) : Term := .Const (.Data d)

/-- An Aiken `List<Int>` argument. -/
abbrev list (xs : List Int) : Term := .Const (.Data (.List (xs.map .I)))

/-- An Aiken `List<ByteArray>` argument. -/
abbrev bytesList (bs : List PlutusCore.ByteString.ByteString) : Term :=
  .Const (.Data (.List (bs.map .B)))

/-- An Aiken `List<Bool>` argument. -/
abbrev boolList (bs : List Bool) : Term := .Const (.Data (.List (bs.map boolData)))

/-! ## Results -/

/-- What an exported Aiken function returning `Bool` halts with when it says `True`. -/
abbrev vTrue : CekValue := .VCon (.Bool true)

/-- What an exported Aiken function returning `Bool` halts with when it says `False`. -/
abbrev vFalse : CekValue := .VCon (.Bool false)

/-- The unit value: what a Plutus V3 validator halts with when it accepts. -/
abbrev vUnit : CekValue := .VCon .Unit

/-! ## On-chain judgment -/

/-- The ledger's judgment for Plutus V3: the script, applied to the script
    context, halts with `()`. Anything else (an `error`, a failed `expect`, a
    `False` turned into `error` by Aiken) is a rejection. An `abbrev`: a goal
    `Accepts s c` is a `Halts` claim for `uplc_run` and `uplc_induction`. -/
abbrev Accepts (script : Program) (ctx : Data) : Prop :=
  Halts script [.Const (.Data ctx)] (.VCon .Unit)

/-- `b` is the on-chain verdict of `script` on `ctx`. -/
def Verdict (script : Program) (ctx : Data) (b : Bool) : Prop :=
  (b = true ↔ Accepts script ctx)

theorem Verdict.accepts {s : Program} {c : Data} (h : Verdict s c true) : Accepts s c :=
  h.mp rfl

theorem Verdict.rejects {s : Program} {c : Data} (h : Verdict s c false) : ¬ Accepts s c :=
  fun ha => Bool.false_ne_true (h.mpr ha)

/-- The verdict `true`, from a run that accepts (`uplc_cex_closer` proves it by running
    the script). -/
theorem Verdict.of_accepts {s : Program} {c : Data} (h : Accepts s c) : Verdict s c true :=
  ⟨fun _ => h, fun _ => rfl⟩

/-- The verdict `false`, from a run that does not accept. -/
theorem Verdict.of_not_accepts {s : Program} {c : Data} (h : ¬ Accepts s c) :
    Verdict s c false :=
  ⟨fun e => absurd e Bool.false_ne_true, fun ha => absurd ha h⟩

end UplcProof
