import LeanExperiments.CLI
import LeanExperiments.QuickSort

/-- 標準入力の整数列をループ版クイックソートで並べ替えて表示する。 -/
def main : IO Unit := do
  let numbers ← LeanExperiments.CLI.readNatList "quicksort-loop"
  let sorted := LeanExperiments.QuickSort.quickSortIterative numbers.toList
  IO.println (LeanExperiments.CLI.formatNatList sorted.toArray)
