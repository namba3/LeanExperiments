import LeanExperiments.CLI
import LeanExperiments.HeapSort

/-- 標準入力の整数列を再帰版 heap sort で並べ替えて表示する。 -/
def main : IO Unit := do
  let numbers ← LeanExperiments.CLI.readNatList "heapsort-rec"
  let sorted := LeanExperiments.HeapSort.heapSortRecursive numbers
  IO.println (LeanExperiments.CLI.formatNatList sorted)
