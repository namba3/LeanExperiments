import Lean
import LeanExperiments.Verification

/-!
# Inventory of private proposition-valued definitions

Private theorem and lemma declarations are audited from their source files.
This inventory covers proposition-valued private `def` and `opaque` declarations,
which are outside that scanner. It also includes Lean-generated helper definitions;
the companion baseline makes those explicit and causes new entries to require review.
-/

open Lean Elab Command

elab "#inventory_private_prop_definitions" : command => do
  let environment ← getEnv
  for (name, info) in environment.constants.toList do
    let text := name.toString
    if text.startsWith "_private." && text.contains "LeanExperiments.Verification." then
      let isDefinition := match info with
        | .defnInfo _ | .opaqueInfo _ => true
        | _ => false
      if isDefinition then
        let proposition ← liftTermElabM <| Meta.isProp info.type
        if proposition then
          let normalized :=
            match text.splitOn ".0." with
            | privatePrefix :: declaration :: _ =>
              (privatePrefix.drop 9).toString ++ "::" ++ declaration
            | _ => text
          logInfo m!"VERIFICATION_PRIVATE_PROP_DEF|{normalized}"
          let axioms ← liftCoreM <| collectAxioms name
          let axiomNames := String.intercalate "," (axioms.toList.map Name.toString)
          logInfo m!"VERIFICATION_PRIVATE_PROP_AXIOMS|{normalized}|{axiomNames}"

#inventory_private_prop_definitions
