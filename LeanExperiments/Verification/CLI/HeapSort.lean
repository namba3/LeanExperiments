import LeanExperiments.CLI
import LeanExperiments.Verification.HeapSort.Spec

/-!
# HeapSort CLI の出力内容

HeapSort の純粋な結果整形を独立な MergeSort の結果と照合する。
標準入出力や改行の書き込みはこの仕様の対象外とする。
-/

namespace LeanExperiments.Verification.CLI.HeapSort

/-- ループ版 HeapSort CLI の出力文字列は、独立な MergeSort の出力文字列と一致する。 -/
theorem format_heapSort_eq_mergeSort (input : Array Nat) :
    LeanExperiments.CLI.formatNatList (LeanExperiments.HeapSort.heapSort input) =
      LeanExperiments.CLI.formatNatList
        (LeanExperiments.MergeSort.mergeSort input.toList).toArray := by
  rw [LeanExperiments.Verification.HeapSort.Spec.heapSort_eq_mergeSort]

/-- 再帰版 HeapSort の結果を整形した文字列も、独立な MergeSort と一致する。 -/
theorem format_heapSortRecursive_eq_mergeSort (input : Array Nat) :
    LeanExperiments.CLI.formatNatList
        (LeanExperiments.HeapSort.heapSortRecursive input) =
      LeanExperiments.CLI.formatNatList
        (LeanExperiments.MergeSort.mergeSort input.toList).toArray := by
  rw [LeanExperiments.Verification.HeapSort.Spec.heapSortRecursive_eq_mergeSort]

end LeanExperiments.Verification.CLI.HeapSort
