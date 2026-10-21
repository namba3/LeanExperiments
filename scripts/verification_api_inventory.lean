import Lean
import LeanExperiments.Verification

/-!
Emit a machine-readable snapshot of public verification declarations. Types and
transitive axiom dependencies come from Lean's elaborated Environment. Type
pretty-printing is a review trigger, not a proof of semantic inequivalence.
-/

open Lean Elab Command

def verificationKind (info : ConstantInfo) : String :=
  match info with
  | .thmInfo _ => "theorem"
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "def"
  | .opaqueInfo _ => "opaque"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"
  | .quotInfo _ => "quot"

elab "#inventory_verification_api" : command => do
  let environment ← getEnv
  for (name, info) in environment.constants.toList do
    if name.toString.startsWith "LeanExperiments.Verification." && !name.isInternalDetail then
      let typeText ← liftTermElabM do
        return (← Meta.ppExpr info.type).pretty
      let axioms ← collectAxioms name
      let moduleName := match environment.getModuleIdxFor? name with
        | some index => environment.header.moduleNames[index.toNat]!.toString
        | none => "unknown"
      let record := Json.mkObj [
        ("name", toJson name.toString),
        ("kind", toJson (verificationKind info)),
        ("module", toJson moduleName),
        ("type", toJson typeText),
        ("axioms", toJson (axioms.toList.map Name.toString))
      ]
      logInfo m!"VERIFICATION_API|{record.compress}"

#inventory_verification_api
