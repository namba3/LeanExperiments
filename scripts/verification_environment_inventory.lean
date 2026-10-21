import Lean
import LeanExperiments.Verification

/-!
# Lean Environment inventory for verification propositions

Emit every non-generated public constant under the verification namespaces
whose type is a proposition. The Python audit compares this inventory with
the public manifest groups. This catches proposition-valued `def`s, explicit
axioms, instances with proposition types, and generated theorem declarations
that are not visible to the source-level theorem/lemma scanner.

Private declarations are excluded by Lean's internal-name marker and remain
covered by the direct-source private audit.
-/

open Lean Elab Command

elab "#inventory_verification_props" : command => do
  let environment ← getEnv
  for (name, info) in environment.constants.toList do
    if name.toString.startsWith "LeanExperiments.Verification." && !name.isInternalDetail then
      let proposition ← liftTermElabM <| Meta.isProp info.type
      if proposition then
        let kind := match info with
          | .thmInfo _ => "theorem"
          | .axiomInfo _ => "axiom"
          | .defnInfo _ => "def"
          | .opaqueInfo _ => "opaque"
          | .inductInfo _ => "inductive"
          | .ctorInfo _ => "constructor"
          | .recInfo _ => "recursor"
          | .quotInfo _ => "quot"
        logInfo m!"VERIFICATION_ENV_PROP|{kind}|{name}"

#inventory_verification_props
