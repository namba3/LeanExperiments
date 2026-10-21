import LeanExperiments.Verification.CLI.HeapSort
import LeanExperiments.Verification.MergeSort.Spec
import LeanExperiments.Verification.QuickSort.Spec

/-!
# ソート CLI の純粋な出力整形

各 CLI が使う数列の文字列化を共通関数へ接続し、異なるソート実装が同じ入力に
同じ文字列を返すことを任意入力で示す。標準入出力の実行自体は対象外とする。
-/

namespace LeanExperiments.Verification.CLI.Sorting

open LeanExperiments.Verification.Sorting.Spec

/-- ループ版 MergeSort と再帰版 MergeSort の CLI 出力は任意入力で一致する。 -/
theorem format_mergeSortIterative_eq_mergeSort (input : List Nat) :
    LeanExperiments.CLI.formatNatList
        (LeanExperiments.MergeSort.mergeSortIterative input).toArray =
      LeanExperiments.CLI.formatNatList
        (LeanExperiments.MergeSort.mergeSort input).toArray := by
  have hOutput := Correct.eq_of_same_input
    (LeanExperiments.Verification.MergeSort.mergeSortIterative_correct input)
    (LeanExperiments.Verification.MergeSort.mergeSort_correct input)
  simpa using congrArg (fun output => LeanExperiments.CLI.formatNatList output.toArray) hOutput

/-- 再帰版 QuickSort と独立な再帰版 MergeSort の CLI 出力は任意入力で一致する。 -/
theorem format_quickSort_eq_mergeSort (input : List Nat) :
    LeanExperiments.CLI.formatNatList
        (LeanExperiments.QuickSort.quickSort input).toArray =
      LeanExperiments.CLI.formatNatList
        (LeanExperiments.MergeSort.mergeSort input).toArray := by
  have hOutput := Correct.eq_of_same_input
    (LeanExperiments.Verification.QuickSort.quickSort_correct input)
    (LeanExperiments.Verification.MergeSort.mergeSort_correct input)
  simpa using congrArg (fun output => LeanExperiments.CLI.formatNatList output.toArray) hOutput

/-- ループ版 QuickSort と独立な再帰版 MergeSort の CLI 出力は任意入力で一致する。 -/
theorem format_quickSortIterative_eq_mergeSort (input : List Nat) :
    LeanExperiments.CLI.formatNatList
        (LeanExperiments.QuickSort.quickSortIterative input).toArray =
      LeanExperiments.CLI.formatNatList
        (LeanExperiments.MergeSort.mergeSort input).toArray := by
  have hOutput := Correct.eq_of_same_input
    (LeanExperiments.Verification.QuickSort.quickSortIterative_correct input)
    (LeanExperiments.Verification.MergeSort.mergeSort_correct input)
  simpa using congrArg (fun output => LeanExperiments.CLI.formatNatList output.toArray) hOutput

/-- 再帰版 HeapSort CLI と独立な MergeSort の出力文字列は任意配列で一致する。 -/
theorem format_heapSortRecursive_eq_mergeSort (input : Array Nat) :
    LeanExperiments.CLI.formatNatList
        (LeanExperiments.HeapSort.heapSortRecursive input) =
      LeanExperiments.CLI.formatNatList
        (LeanExperiments.MergeSort.mergeSort input.toList).toArray := by
  exact LeanExperiments.Verification.CLI.HeapSort.format_heapSortRecursive_eq_mergeSort input

/-- ループ版 HeapSort CLI と独立な MergeSort の出力文字列は任意配列で一致する。 -/
theorem format_heapSort_eq_mergeSort (input : Array Nat) :
    LeanExperiments.CLI.formatNatList
        (LeanExperiments.HeapSort.heapSort input) =
      LeanExperiments.CLI.formatNatList
        (LeanExperiments.MergeSort.mergeSort input.toList).toArray := by
  exact LeanExperiments.Verification.CLI.HeapSort.format_heapSort_eq_mergeSort input

end LeanExperiments.Verification.CLI.Sorting
