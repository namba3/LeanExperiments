import LeanExperiments.CLI
import LeanExperiments.PrimeFactors

/-- 標準入力から自然数を 1 つ読み、素因数を重複込みで表示する。 -/
def main : IO Unit := do
  let n ← LeanExperiments.CLI.readNat "prime-factors"
  let factors := LeanExperiments.primeFactors n
  if factors.isEmpty then
    -- 0 と 1 はこの実装では素因数を持たないため、そのことを明示する。
    IO.println "(none)"
  else
    IO.println (String.intercalate " " (factors.toList.map toString))
