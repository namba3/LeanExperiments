import LeanExperiments.CLI
import LeanExperiments.QuickSort

/-- 標準入力の整数列をクイックソートし、昇順で 1 行に表示する。 -/
def main : IO Unit := do
  let numbers ← LeanExperiments.CLI.readNatList "quicksort"
  let sorted := LeanExperiments.QuickSort.quickSort numbers.toList
  IO.println (LeanExperiments.CLI.formatNatList sorted.toArray)
