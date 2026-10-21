module

@[expose] public section

/-!
# 階乗

`factorial` コマンドから利用する階乗の実装。
`factorialLoop n result` は、残りの `n` 個の因子を `result` に掛けていく
末尾再帰関数である。
Lean の `Nat` を使うため、入力は 0 以上で、結果は任意精度の自然数になる。
-/

namespace LeanExperiments

/-- 残りの因子 `n, n-1, ..., 1` を蓄積値 `result` に掛けていく。

`n = 0` になった時点で、これまでに蓄積した積を返す。
-/
def factorialLoop : Nat → Nat → Nat
  | 0, result => result
  -- n が n+1 の場合、因子 n+1 を積へ取り込んで残りを n にする。
  | n + 1, result => factorialLoop n (result * (n + 1))

/-- 自然数 `n` の階乗 `n!` を計算する。`0! = 1` も基底ケースで得られる。 -/
def factorial (n : Nat) : Nat := factorialLoop n 1

end LeanExperiments
