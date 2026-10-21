module

public import Std.WP

@[expose] public section

set_option experimental.intrinsic true

/-!
# 素因数分解

試し割りで自然数を素因数へ分解する。
小さな約数から順番に割るため、返す素因数は昇順になり、同じ素因数は
指数表記ではなく重複した値として出力される。
-/

namespace LeanExperiments

/-- 試し割りを最後まで実行し、残余・次の候補・見つかった因子を返す。

この関数は因子の積と残余の積を保つループ契約を独立に検証するために分けている。
候補を割り切れた場合は同じ候補で再試行し、割り切れない場合だけ候補を進める。
-/
def trialDivisionLoop (n : Nat) : Nat × Nat × Array Nat := Id.run do
  let mut remaining := n
  let mut divisor := 2
  let mut factors := #[]
  -- `remaining - divisor` は割り算時も候補更新時も減少する。
  while divisor * divisor ≤ remaining decreasing remaining - divisor do
    if remaining % divisor == 0 then
      factors := factors.push divisor
      remaining := remaining / divisor
    else
      divisor := divisor + 1
  return (remaining, divisor, factors)

/-- `n` の素因数を昇順の配列で返す。重複する素因数もすべて含める。

割る候補 `divisor` が `remaining` の平方根を超えた時点でループを終える。
その時点で `remaining > 1` なら、残った数自身が素数なので最後に追加する。
0 と 1 は素因数を持たないものとして空配列を返す。
-/
def primeFactors (n : Nat) : Array Nat :=
  if n ≤ 1 then #[] else
    let (remaining, _, factors) := trialDivisionLoop n
    if remaining > 1 then factors.push remaining else factors

end LeanExperiments
