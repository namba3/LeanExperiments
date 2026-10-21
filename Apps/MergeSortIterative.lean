import LeanExperiments.CLI
import LeanExperiments.MergeSort

/-- 標準入力の整数列をループ版マージソートで並べ替えて表示する。 -/
def main : IO Unit := do
  let numbers ← LeanExperiments.CLI.readNatList "mergesort-loop"
  let sorted := LeanExperiments.MergeSort.mergeSortIterative numbers.toList
  IO.println (LeanExperiments.CLI.formatNatList sorted.toArray)
