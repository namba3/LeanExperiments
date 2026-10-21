import LeanExperiments.CLI
import LeanExperiments.Factorial

/-- 標準入力から自然数を 1 つ読み、その階乗を表示する。 -/
def main : IO Unit := do
  let n ← LeanExperiments.CLI.readNat "factorial"
  IO.println (LeanExperiments.factorial n)
