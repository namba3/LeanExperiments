import LeanExperiments.CLI
import LeanExperiments.Fibonacci

/-- 標準入力から添字を 1 つ読み、高速倍加法で Fibonacci 数を求める。 -/
def main : IO Unit := do
  let n ← LeanExperiments.CLI.readNat "fibonacci"
  IO.println (LeanExperiments.fibonacci n)
