import LeanExperiments.CLI
import LeanExperiments.RunningMedian

/-- 標準入力の整数列の中央値を、空なら `none` として1行で表示する。 -/
def main : IO Unit := do
  let numbers ← LeanExperiments.CLI.readNatList "median"
  IO.println (LeanExperiments.CLI.formatMedian (LeanExperiments.RunningMedian.medianOf numbers))
