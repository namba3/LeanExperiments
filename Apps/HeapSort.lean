import LeanExperiments.CLI
import LeanExperiments.HeapSort

/-- 標準入力の整数列を読み、heap sort の結果を 1 行で表示する。 -/
def main : IO Unit := do
  let numbers ← LeanExperiments.CLI.readNatList "heapsort"
  let sorted := LeanExperiments.HeapSort.heapSort numbers
  -- 空配列の場合も、出力形式を一定にするため改行を 1 つ出力する。
  IO.println (LeanExperiments.CLI.formatNatList sorted)
