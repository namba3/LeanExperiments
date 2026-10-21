import LeanExperiments.CLI
import LeanExperiments.MergeSort

/-- 標準入力の整数列をマージソートし、昇順で 1 行に表示する。 -/
def main : IO Unit := do
  let numbers ← LeanExperiments.CLI.readNatList "mergesort"
  let sorted := LeanExperiments.MergeSort.mergeSort numbers.toList
  IO.println (LeanExperiments.CLI.formatNatList sorted.toArray)
