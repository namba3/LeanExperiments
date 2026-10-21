module

@[expose] public section

/-!
# Fibonacci 数列

高速倍加法を使って Fibonacci 数を求める。
通常の再帰は同じ値を何度も計算するが、この実装は添字を半分にして
必要な 2 項をまとめて求めるため、再帰の深さは `n` に対して対数的になる。
-/

namespace LeanExperiments

/-- `(F n, F (n + 1))` を返す高速倍加法の中核。

`a = F k`, `b = F (k+1)` が分かれば、次の恒等式で 2 倍先までを計算できる。

* `F (2k) = a * (2b - a)`
* `F (2k+1) = a*a + b*b`

添字が偶数ならこの 2 値をそのまま返し、奇数なら 1 項進めて返す。
-/
def fibonacciPair : Nat → Nat × Nat
  | 0 => (0, 1)
  | n + 1 =>
    let (a, b) := fibonacciPair ((n + 1) / 2)
    -- 自然数の減算を使う。Fibonacci の隣接項では 2*b ≥ a が成り立つ。
    let even := a * (2 * b - a)
    let odd := a * a + b * b
    if (n + 1) % 2 == 0 then (even, odd) else (odd, even + odd)
termination_by n => n
decreasing_by omega

/-- `F 0 = 0`, `F 1 = 1` とする Fibonacci 数列の `n` 番目を返す。 -/
def fibonacci (n : Nat) : Nat := (fibonacciPair n).1

end LeanExperiments
