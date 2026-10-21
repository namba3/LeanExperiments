import Lean
import LeanExperiments.Verification.Sorting.Spec
import LeanExperiments.Verification.Sorting.Comparisons
import LeanExperiments.Verification.MergeSort.Spec
import LeanExperiments.Verification.QuickSort.Spec
import LeanExperiments.Verification.HeapSort.Spec
import LeanExperiments.Verification.RunningMedian.Spec
import LeanExperiments.Verification.CLI.Spec
import LeanExperiments.Verification.CLI.HeapSort

/-!
# Verification内のprivate定理の公理依存監査

ソースに宣言されたprivate theoremを環境から特定し、Leanカーネルの推移的な公理依存を個別に出力する。
-/

open Lean Elab Command
syntax (name := printPrivateAxioms) "#print_private_axioms " str : command
elab_rules : command
  | `(#print_private_axioms $target:str) => do
      let suffix := target.getString
      let env ← getEnv
      let candidates := env.constants.toList.filter fun (name, info) =>
        name.toString.startsWith "_private." && name.toString.endsWith suffix &&
          match info with
          | .thmInfo _ => true
          | _ => false
      if candidates.length != 1 then
        throwError "expected one private theorem ending in {suffix}, found {candidates.length}"
      let (name, _) := candidates[0]!
      let axioms ← liftCoreM <| collectAxioms name
      if axioms.isEmpty then
        logInfo m!"'{suffix}' does not depend on any axioms"
      else
        logInfo m!"'{suffix}' depends on axioms: {axioms.toList}"

#print_private_axioms "LeanExperiments.Verification.HeapSort.Spec.siftDownSwap_getElem!_eq_of_ne"
#print_private_axioms "LeanExperiments.Verification.HeapSort.Spec.siftDownSwap_descendant_bound"
#print_private_axioms "LeanExperiments.Verification.HeapSort.Spec.maxHeap_of_three"
#print_private_axioms "LeanExperiments.Verification.HeapSort.Spec.maxHeap_of_four"
#print_private_axioms "LeanExperiments.Verification.HeapSort.Spec.maxHeap_of_five"
#print_private_axioms "LeanExperiments.Verification.HeapSort.Spec.siftDownRecursive_quint_root_maxHeap"
#print_private_axioms "LeanExperiments.Verification.HeapSort.Spec.maxHeap_of_six"
#print_private_axioms "LeanExperiments.Verification.HeapSort.Spec.maxHeap_of_seven"
#print_private_axioms "LeanExperiments.Verification.HeapSort.Spec.maxHeap_of_eight"
#print_private_axioms "LeanExperiments.Verification.HeapSort.Spec.siftDownRecursive_sext_root_maxHeap"
#print_private_axioms "LeanExperiments.Verification.HeapSort.Spec.siftDownRecursive_sept_root_maxHeap"
#print_private_axioms "LeanExperiments.Verification.HeapSort.Spec.siftDownRecursive_oct_root_maxHeap"
#print_private_axioms "LeanExperiments.Verification.HeapSort.Spec.siftDownRecursive_quad_root_maxHeap"
#print_private_axioms "LeanExperiments.Verification.HeapSort.Spec.siftDownRecursive_sept_right_child_bounds"
#print_private_axioms "LeanExperiments.Verification.HeapSort.Spec.siftDownRecursive_sept_left_child_bounds"
#print_private_axioms "LeanExperiments.Verification.HeapSort.Spec.siftDownRecursive_oct_right_preserves_left_subtree"
#print_private_axioms "LeanExperiments.Verification.HeapSort.Spec.siftDownRecursive_oct_left_preserves_right_subtree"
#print_private_axioms "LeanExperiments.Verification.HeapSort.Spec.array_eq_index_values_of_size_eq_eight"
#print_private_axioms "LeanExperiments.Verification.HeapSort.Spec.array_eq_index_values_of_size_eq_nine"
#print_private_axioms "LeanExperiments.Verification.HeapSort.Spec.siftDownRecursive_nine_right_preserves_left_subtree"
#print_private_axioms "LeanExperiments.Verification.HeapSort.Spec.siftDownRecursive_nine_left_preserves_right_subtree"
#print_private_axioms "LeanExperiments.Verification.HeapSort.Spec.buildMaxHeapRecursive_oct_child_subheaps"
#print_private_axioms "LeanExperiments.Verification.HeapSort.Spec.buildMaxHeapRecursive_eq_siftDown_of_size_eq_two"
#print_private_axioms "LeanExperiments.Verification.HeapSort.Spec.buildMaxHeapRecursive_eq_siftDown_of_size_le_three"
#print_private_axioms "LeanExperiments.Verification.HeapSort.Spec.extractMaxima_eq_nil_of_extract_none"
#print_private_axioms "LeanExperiments.Verification.HeapSort.Spec.extractRemainder_eq_self_of_extract_none"
#print_private_axioms "LeanExperiments.Verification.HeapSort.Spec.maxHeap_of_size_le_one"
#print_private_axioms "LeanExperiments.Verification.HeapSort.Spec.popMaxRecursive_rest_maxHeap_of_size_eq_three"
#print_private_axioms "LeanExperiments.Verification.HeapSort.Spec.popMaxRecursive_rest_maxHeap_of_size_le_four"
#print_private_axioms "LeanExperiments.Verification.HeapSort.Spec.array_eq_index_values_of_size_eq_five"
#print_private_axioms "LeanExperiments.Verification.HeapSort.Spec.array_eq_index_values_of_size_eq_six"
#print_private_axioms "LeanExperiments.Verification.HeapSort.Spec.array_eq_index_values_of_size_eq_seven"
#print_private_axioms "LeanExperiments.Verification.HeapSort.Spec.popMaxRecursive_rest_maxHeap_of_maxHeap_size_eq_five"
#print_private_axioms "LeanExperiments.Verification.HeapSort.Spec.popMaxRecursive_rest_maxHeap_of_maxHeap_size_eq_six"
#print_private_axioms "LeanExperiments.Verification.HeapSort.Spec.popMaxRecursive_rest_maxHeap_of_maxHeap_size_eq_seven"
#print_private_axioms "LeanExperiments.Verification.HeapSort.Spec.popMaxRecursive_rest_maxHeap_of_maxHeap_size_eq_eight"
#print_private_axioms "LeanExperiments.Verification.HeapSort.Spec.popMaxRecursive_rest_maxHeap_of_maxHeap_size_eq_nine"
#print_private_axioms "LeanExperiments.Verification.HeapSort.Spec.heapSortAsList_correct"
#print_private_axioms "LeanExperiments.Verification.HeapSort.Spec.heapSortRecursiveAsList_correct"
#print_private_axioms "LeanExperiments.Verification.MergeSort.mergePasses_preserves_length_le_one"
#print_private_axioms "LeanExperiments.Verification.MergeSort.mergePasses_headD_eq_of_length_le_one"
#print_private_axioms "LeanExperiments.Verification.QuickSort.quickSortTaskPotential_pos"
#print_private_axioms "LeanExperiments.Verification.QuickSort.quickSortTaskListPotential_ge_initial"
#print_private_axioms "LeanExperiments.Verification.QuickSort.quickSortTaskListPotential_pos_iff"
#print_private_axioms "LeanExperiments.Verification.QuickSort.quickSortTaskStackOutput_push"
#print_private_axioms "LeanExperiments.Verification.RunningMedian.sortedHeapParts_correct"
#print_private_axioms "LeanExperiments.Verification.RunningMedian.sizeBalanced_of_bounds"
#print_private_axioms "LeanExperiments.Verification.RunningMedian.sortedLower_last_eq_root"
#print_private_axioms "LeanExperiments.Verification.RunningMedian.sortedUpper_first_eq_root"
#print_private_axioms "LeanExperiments.Verification.Sorting.Spec.pairwise_lt_nodup"
#print_private_axioms "LeanExperiments.Verification.Sorting.Spec.ascending_nodup_pairwise_lt"
#print_private_axioms "LeanExperiments.Verification.Sorting.Spec.countP_le_of_implies"