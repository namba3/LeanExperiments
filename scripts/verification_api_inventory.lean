import Lean
import LeanExperiments.Verification

/-!
Emit a machine-readable snapshot of public verification declarations. Types and
transitive axiom dependencies come from Lean's elaborated Environment. Type
pretty-printing is a review trigger, not a proof of semantic inequivalence.
-/

open Lean Elab Command

/-!
The ordinary API snapshot detects type and axiom changes, but a definition can
keep its type while its meaning changes. This curated list names the
specifications and invariants whose elaborated bodies receive a separate
structural review fingerprint. The Python checker requires this list to match
`verification_spec_manifest.json` exactly.
-/

partial def normalizeSpecExpr : Expr → Expr
  | .bvar index => .bvar index
  | .fvar id => .fvar id
  | .mvar id => .mvar id
  | .sort level => .sort level
  | .const name levels => .const name levels
  | .app fn argument => .app (normalizeSpecExpr fn) (normalizeSpecExpr argument)
  | .lam _ type body binderInfo =>
      .lam Name.anonymous (normalizeSpecExpr type) (normalizeSpecExpr body) binderInfo
  | .forallE _ type body binderInfo =>
      .forallE Name.anonymous (normalizeSpecExpr type) (normalizeSpecExpr body) binderInfo
  | .letE _ type value body nondep =>
      .letE Name.anonymous (normalizeSpecExpr type) (normalizeSpecExpr value)
        (normalizeSpecExpr body) nondep
  | .lit literal => .lit literal
  | .mdata _ expression => normalizeSpecExpr expression
  | .proj typeName index expression =>
      .proj typeName index (normalizeSpecExpr expression)

def criticalSpecNames : List Name := [
  `LeanExperiments.Verification.Factorial.factorialSpec,
  `LeanExperiments.Verification.Fibonacci.fibonacciSpecAux,
  `LeanExperiments.Verification.Fibonacci.fibonacciSpec,
  `LeanExperiments.Verification.HeapSort.Spec.MaxHeap,
  `LeanExperiments.Verification.HeapSort.Spec.siftDownLoopInvariant,
  `LeanExperiments.Verification.HeapSort.Spec.HeapBuildCorrect,
  `LeanExperiments.Verification.HeapSort.Spec.PopMaxRestCorrectFor,
  `LeanExperiments.Verification.HeapSort.Spec.PopMaxOrderCorrectFor,
  `LeanExperiments.Verification.QuickSort.quickSortIterativeInvariant,
  `LeanExperiments.Verification.MergeSort.MergeLoopPrefixInvariant,
  `LeanExperiments.Verification.MergeSort.MergeLoopInvariant,
  `LeanExperiments.Verification.PrimeFactors.isPrimeCheck,
  `LeanExperiments.Verification.PrimeFactors.FactorsCorrect,
  `LeanExperiments.Verification.RunningMedian.HeapOrdered,
  `LeanExperiments.Verification.RunningMedian.StateInvariant,
  `LeanExperiments.Verification.RunningMedian.stateInvariantCheck,
  `LeanExperiments.Verification.RunningMedian.medianSpec,
  `LeanExperiments.Verification.Sorting.Spec.Ascending,
  `LeanExperiments.Verification.Sorting.Spec.Correct,
  `LeanExperiments.Verification.Sorting.Spec.ascendingCheck,
  `LeanExperiments.Verification.Sorting.Spec.correctCheck
]

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
  for name in criticalSpecNames do
    let some (.defnInfo definition) := environment.find? name
      | throwError "critical specification is missing or is not a definition: {name}"
    if definition.value.hasFVar || definition.value.hasExprMVar || definition.value.hasLevelMVar then
      throwError "critical specification body is not closed: {name}"
    let body := normalizeSpecExpr definition.value
    let typeText ← liftTermElabM do
      return (← Meta.ppExpr definition.type).pretty
    let axioms ← collectAxioms name
    let moduleName := match environment.getModuleIdxFor? name with
      | some index => environment.header.moduleNames[index.toNat]!.toString
      | none => "unknown"
    let record := Json.mkObj [
      ("name", toJson name.toString),
      ("kind", toJson "def"),
      ("module", toJson moduleName),
      ("type", toJson typeText),
      ("body", toJson (reprStr body)),
      ("expr_hash_hint", toJson (reprStr body.hash)),
      ("reducibility", toJson (match definition.hints with
        | .opaque => "opaque"
        | .abbrev => "abbrev"
        | .regular height => s!"regular:{height}")),
      ("safety", toJson (reprStr definition.safety)),
      ("level_params", toJson (definition.levelParams.map Name.toString)),
      ("axioms", toJson (axioms.toList.map Name.toString)),
      ("lean_version", toJson Lean.versionString)
    ]
    logInfo m!"VERIFICATION_SPEC|{record.compress}"

#inventory_verification_api
