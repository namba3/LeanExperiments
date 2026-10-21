module

public import LeanExperiments.Fibonacci
public meta import LeanExperiments.Fibonacci
public import Mathlib.Data.Nat.GCD.Basic
public import Mathlib.Data.Nat.Fib.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public meta import Mathlib.Algebra.Group.Nat.Defs

@[expose] public section

/-!
# Fibonacci 数の検証

高速倍加法の実装が、通常の Fibonacci 漸化式を反復する独立仕様と
任意の添字で一致することを証明する。加えて、有限範囲や二進分岐境界の網羅確認と、
大きな具体値のカーネル計算も行い、一般証明を異なる形の検査で補強する。
-/

namespace LeanExperiments.Verification.Fibonacci

/-- 通常の漸化式を線形回数だけ反復する Fibonacci の比較仕様。 -/
def fibonacciSpecAux : Nat → Nat → Nat → Nat
  | 0, current, _ => current
  | steps + 1, current, next => fibonacciSpecAux steps next (current + next)

/-- 高速倍加法とは別の、線形時間で計算する通常漸化式の仕様。 -/
def fibonacciSpec (n : Nat) : Nat := fibonacciSpecAux n 0 1

/-- `n = 0` から `n = 512` までを連続して確認する。 -/
def boundedInputs : List Nat := List.range 513

/-- 高速倍加法と通常の漸化式が一致するかを各添字で判定する。 -/
def boundedRecurrenceCheck : Bool :=
  boundedInputs.all fun n =>
    decide (LeanExperiments.fibonacci n = fibonacciSpec n)

/-- `n = 0` から `n = 512` まで、両定義の値が全て一致する。 -/
theorem boundedRecurrenceCheck_passes : boundedRecurrenceCheck = true := by
  native_decide

/-- 確認範囲内の添字では、高速倍加法が通常の漸化式と同じ値を返す。 -/
theorem fibonacci_correct_for_boundedInput (n : Nat) (hInput : n ∈ boundedInputs) :
    LeanExperiments.fibonacci n = fibonacciSpec n := by
  have hAll : ∀ candidate ∈ boundedInputs,
      decide (LeanExperiments.fibonacci candidate = fibonacciSpec candidate) = true :=
    List.all_eq_true.mp boundedRecurrenceCheck_passes
  exact of_decide_eq_true (hAll n hInput)

/-- 二進分岐の境界となる2の累乗と、その直前・直後の添字。 -/
def powerOfTwoBoundaryInputs : List Nat :=
  (List.range 16).flatMap fun exponent =>
    let power := 2 ^ (exponent + 1)
    [power - 1, power, power + 1]

/-- 2 から 65536 までの各2の累乗と、その前後の添字を比較対象にする。 -/
def powerOfTwoBoundaryCheck : Bool :=
  powerOfTwoBoundaryInputs.all fun n =>
    decide (LeanExperiments.fibonacci n = fibonacciSpec n)

/-- 2の累乗をまたぐ48個の添字すべてで、高速倍加法と通常漸化式が一致する。 -/
theorem powerOfTwoBoundaryCheck_passes : powerOfTwoBoundaryCheck = true := by
  native_decide

/-- 2の累乗の直前・累乗上・直後として列挙した添字では仕様一致を取り出せる。 -/
theorem fibonacci_correct_for_powerOfTwoBoundaryInput (n : Nat)
    (hInput : n ∈ powerOfTwoBoundaryInputs) :
    LeanExperiments.fibonacci n = fibonacciSpec n := by
  have hAll : ∀ candidate ∈ powerOfTwoBoundaryInputs,
      decide (LeanExperiments.fibonacci candidate = fibonacciSpec candidate) = true :=
    List.all_eq_true.mp powerOfTwoBoundaryCheck_passes
  exact of_decide_eq_true (hAll n hInput)

/-- `fibonacciPair n` の第 2 成分、すなわち `F (n+1)` は常に正である。

高速倍加法は添字を半分にして呼び出すので、その小さい添字に関する強い帰納法を
使う。倍加公式に現れる `a*a + b*b` は、帰納法の仮定 `b > 0` により正となる。
-/
theorem fibonacciPair_next_positive (n : Nat) :
    0 < (LeanExperiments.fibonacciPair n).2 := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    cases n with
    | zero =>
        simp [LeanExperiments.fibonacciPair]
    | succ n =>
        have hHalf : (n + 1) / 2 < n + 1 := by omega
        cases hPair : LeanExperiments.fibonacciPair ((n + 1) / 2) with
        | mk a b =>
            have hB : 0 < b := by
              have h := ih ((n + 1) / 2) hHalf
              simpa [hPair] using h
            have hBB : 0 < b * b := Nat.mul_pos hB hB
            have hOdd : 0 < a * a + b * b := by omega
            simp only [LeanExperiments.fibonacciPair, hPair]
            by_cases hEven : (n + 1) % 2 == 0
            · simp [hEven, hOdd]
            · simp [hEven]
              omega

/-- 高速倍加法が返す二項は、常に左から右へ非減少である。

帰納法では半分の添字における二項の大小を使う。偶数分岐では
`d = b-a` と置くと `b = a+d` かつ `2*b-a = a+2*d` となる。
両辺を展開した差は `a*a + d*d` なので、自然数の非負性から順序が従う。
-/
theorem fibonacciPair_first_le_second (n : Nat) :
    (LeanExperiments.fibonacciPair n).1 ≤ (LeanExperiments.fibonacciPair n).2 := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    cases n with
    | zero => simp [LeanExperiments.fibonacciPair]
    | succ n =>
      let half := (n + 1) / 2
      have hHalf : half < n + 1 := by dsimp [half]; omega
      cases hPair : LeanExperiments.fibonacciPair half with
      | mk a b =>
        have hAB : a ≤ b := by
          have h := ih half hHalf
          simpa [hPair] using h
        let d := b - a
        have hBD : b = a + d := by dsimp [d]; omega
        have hFactor : 2 * b - a = a + 2 * d := by dsimp [d]; omega
        have hEvenBound : a * (2 * b - a) ≤ a * a + b * b := by
          rw [hFactor, hBD]
          simp [Nat.mul_two, Nat.mul_add, Nat.mul_comm]
          omega
        by_cases hEven : (n + 1) % 2 == 0
        · simpa [LeanExperiments.fibonacciPair, half, hPair, hEven] using hEvenBound
        · simp [LeanExperiments.fibonacciPair, half, hPair, hEven]

private theorem fibonacciPair_even (k : Nat) :
    LeanExperiments.fibonacciPair (2 * k) =
      ((LeanExperiments.fibonacciPair k).1 *
          (2 * (LeanExperiments.fibonacciPair k).2 - (LeanExperiments.fibonacciPair k).1),
       (LeanExperiments.fibonacciPair k).1 * (LeanExperiments.fibonacciPair k).1 +
          (LeanExperiments.fibonacciPair k).2 * (LeanExperiments.fibonacciPair k).2) := by
  cases k with
  | zero => simp [LeanExperiments.fibonacciPair]
  | succ k =>
    change LeanExperiments.fibonacciPair ((2 * k + 1) + 1) = _
    have hDiv : (2 * k + 2) / 2 = k + 1 := by omega
    have hMod : (2 * k + 2) % 2 = 0 := by omega
    simp [LeanExperiments.fibonacciPair, hDiv, hMod]

private theorem fibonacciPair_odd (k : Nat) :
    LeanExperiments.fibonacciPair (2 * k + 1) =
      ((LeanExperiments.fibonacciPair k).1 * (LeanExperiments.fibonacciPair k).1 +
          (LeanExperiments.fibonacciPair k).2 * (LeanExperiments.fibonacciPair k).2,
       (LeanExperiments.fibonacciPair k).1 *
          (2 * (LeanExperiments.fibonacciPair k).2 - (LeanExperiments.fibonacciPair k).1) +
          (LeanExperiments.fibonacciPair k).1 * (LeanExperiments.fibonacciPair k).1 +
          (LeanExperiments.fibonacciPair k).2 * (LeanExperiments.fibonacciPair k).2) := by
  have hDiv : (2 * k + 1) / 2 = k := by omega
  have hMod : (2 * k + 1) % 2 = 1 := by omega
  simp [LeanExperiments.fibonacciPair, hDiv, hMod]
  ac_rfl

/-- 倍加法の返す組は、隣接する Fibonacci 項の組として一歩ずつ進む。 -/
theorem fibonacciPair_succ (n : Nat) :
    LeanExperiments.fibonacciPair (n + 1) =
      ((LeanExperiments.fibonacciPair n).2,
       (LeanExperiments.fibonacciPair n).1 + (LeanExperiments.fibonacciPair n).2) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hEven : n % 2 = 0
    · let k := n / 2
      have hIndex : n = 2 * k := by dsimp [k]; omega
      rw [hIndex, fibonacciPair_even, fibonacciPair_odd]
      simp [Nat.add_assoc]
    · let k := n / 2
      have hIndex : n = 2 * k + 1 := by dsimp [k]; omega
      have hSmaller : k < n := by dsimp [k]; omega
      have hStep := ih k hSmaller
      have hStepFirst : (LeanExperiments.fibonacciPair (k + 1)).1 =
          (LeanExperiments.fibonacciPair k).2 := congrArg Prod.fst hStep
      have hStepSecond : (LeanExperiments.fibonacciPair (k + 1)).2 =
          (LeanExperiments.fibonacciPair k).1 + (LeanExperiments.fibonacciPair k).2 :=
        congrArg Prod.snd hStep
      have hNextIndex : 2 * k + 1 + 1 = 2 * (k + 1) := by omega
      rw [hIndex, hNextIndex, fibonacciPair_odd, fibonacciPair_even,
        hStepFirst, hStepSecond]
      cases hPair : LeanExperiments.fibonacciPair k with
      | mk a b =>
        have hAB : a ≤ b := by
          have h := fibonacciPair_first_le_second k
          simpa [hPair] using h
        have hSub : 2 * b - a = b + (b - a) := by omega
        have hEvenIdentity : a * (2 * b - a) + a * a = a * b + a * b := by
          calc
            a * (2 * b - a) + a * a = a * (b + (b - a)) + a * a := by rw [hSub]
            _ = a * b + (a * (b - a) + a * a) := by rw [Nat.mul_add]; ac_rfl
            _ = a * b + a * ((b - a) + a) := by
              congr 1
              exact (Nat.mul_add a (b - a) a).symm
            _ = a * b + a * b := by rw [Nat.sub_add_cancel hAB]
        have hFactor : 2 * (a + b) - b = 2 * a + b := by omega
        have hNextEvenIdentity : b * (2 * (a + b) - b) = a * b + a * b + b * b := by
          rw [hFactor, Nat.mul_add, Nat.two_mul, Nat.mul_add]
          ac_rfl
        have hNextOddIdentity : b * b + (a + b) * (a + b) =
            a * a + a * b + a * b + b * b + b * b := by
          simp only [Nat.add_mul, Nat.mul_add]
          ac_rfl
        dsimp only [Prod.fst, Prod.snd]
        apply Prod.ext
        · rw [hNextEvenIdentity, hEvenIdentity]
        · rw [hNextOddIdentity]
          omega

/-- 参照仕様の線形反復は、初期値の加算に関して線形である。 -/
private theorem fibonacciSpecAux_add (steps first₁ first₂ next₁ next₂ : Nat) :
    fibonacciSpecAux steps (first₁ + first₂) (next₁ + next₂) =
      fibonacciSpecAux steps first₁ next₁ + fibonacciSpecAux steps first₂ next₂ := by
  induction steps generalizing first₁ first₂ next₁ next₂ with
  | zero => simp [fibonacciSpecAux]
  | succ steps ih =>
    simp only [fibonacciSpecAux]
    have hSecond : (first₁ + first₂) + (next₁ + next₂) =
        (first₁ + next₁) + (first₂ + next₂) := by omega
    rw [hSecond, ih]

/-- 独立仕様も通常の Fibonacci 漸化式を満たす。 -/
theorem fibonacciSpec_succ_succ (n : Nat) :
    fibonacciSpec (n + 2) = fibonacciSpec n + fibonacciSpec (n + 1) := by
  simp only [fibonacciSpec, fibonacciSpecAux]
  simpa [Nat.add_comm] using fibonacciSpecAux_add n 1 0 1 1

/-- 参照仕様を隣接する Fibonacci 項から開始すると、添字分だけ進んだ項になる。 -/
private theorem fibonacciSpecAux_shift (offset steps : Nat) :
    fibonacciSpecAux steps (fibonacciSpec offset) (fibonacciSpec (offset + 1)) =
      fibonacciSpec (offset + steps) := by
  induction steps generalizing offset with
  | zero => simp [fibonacciSpecAux]
  | succ steps ih =>
      rw [fibonacciSpecAux]
      rw [← fibonacciSpec_succ_succ offset]
      rw [ih (offset + 1)]
      congr 1; omega

/-- 線形参照仕様を二つの初期値から反復した結果の閉じた形。 -/
private theorem fibonacciSpecAux_succ_closed_form (steps first next : Nat) :
    fibonacciSpecAux (steps + 1) first next =
      first * fibonacciSpec steps + next * fibonacciSpec (steps + 1) := by
  induction steps generalizing first next with
  | zero => simp [fibonacciSpecAux, fibonacciSpec]
  | succ steps ih =>
      change fibonacciSpecAux (steps + 1) next (first + next) = _
      rw [ih, fibonacciSpec_succ_succ]
      simp only [Nat.mul_add, Nat.add_mul]
      ac_rfl

/-- Fibonacci の加法公式を、通常漸化式の独立参照仕様について証明する。

この形は `F (m+n+1) = F(m)F(n) + F(m+1)F(n+1)` で、添字0も含めて扱える。
-/
theorem fibonacciSpec_add (m n : Nat) :
    fibonacciSpec (m + n + 1) =
      fibonacciSpec m * fibonacciSpec n +
        fibonacciSpec (m + 1) * fibonacciSpec (n + 1) := by
  calc
    fibonacciSpec (m + n + 1) = fibonacciSpec (m + (n + 1)) := by
      congr 1
    _ = fibonacciSpecAux (n + 1) (fibonacciSpec m) (fibonacciSpec (m + 1)) :=
      (fibonacciSpecAux_shift m (n + 1)).symm
    _ = fibonacciSpec m * fibonacciSpec n +
        fibonacciSpec (m + 1) * fibonacciSpec (n + 1) :=
      fibonacciSpecAux_succ_closed_form n _ _

/-- 高速倍加法が返す二項は、任意の添字で参照仕様の隣接二項に一致する。 -/
theorem fibonacciPair_eq_spec_pair (n : Nat) :
    LeanExperiments.fibonacciPair n = (fibonacciSpec n, fibonacciSpec (n + 1)) := by
  induction n with
  | zero => simp [LeanExperiments.fibonacciPair, fibonacciSpec, fibonacciSpecAux]
  | succ n ih =>
    rw [fibonacciPair_succ, ih, fibonacciSpec_succ_succ]

/-- 高速倍加法の実装は、通常漸化式の参照仕様と任意の添字で一致する。 -/
theorem fibonacci_correct (n : Nat) :
    LeanExperiments.fibonacci n = fibonacciSpec n := by
  unfold LeanExperiments.fibonacci
  rw [fibonacciPair_eq_spec_pair]

/-- 偶数添字の Fibonacci 数は倍加公式 `F(2n) = F(n)(2F(n+1)-F(n))` に従う。 -/
theorem fibonacci_double_even (n : Nat) :
    LeanExperiments.fibonacci (2 * n) =
      LeanExperiments.fibonacci n *
        (2 * LeanExperiments.fibonacci (n + 1) - LeanExperiments.fibonacci n) := by
  have hPair := fibonacciPair_even n
  have hFirst := congrArg Prod.fst hPair
  have hSpec : fibonacciSpec (2 * n) =
      fibonacciSpec n * (2 * fibonacciSpec (n + 1) - fibonacciSpec n) := by
    simpa only [fibonacciPair_eq_spec_pair, Prod.fst, Prod.snd] using hFirst
  simpa only [fibonacci_correct] using hSpec

/-- 奇数添字の Fibonacci 数は倍加公式 `F(2n+1) = F(n)^2+F(n+1)^2` に従う。 -/
theorem fibonacci_double_odd (n : Nat) :
    LeanExperiments.fibonacci (2 * n + 1) =
      LeanExperiments.fibonacci n * LeanExperiments.fibonacci n +
        LeanExperiments.fibonacci (n + 1) * LeanExperiments.fibonacci (n + 1) := by
  have hPair := fibonacciPair_odd n
  have hFirst := congrArg Prod.fst hPair
  have hSpec : fibonacciSpec (2 * n + 1) =
      fibonacciSpec n * fibonacciSpec n +
        fibonacciSpec (n + 1) * fibonacciSpec (n + 1) := by
    simpa only [fibonacciPair_eq_spec_pair, Prod.fst, Prod.snd] using hFirst
  simpa only [fibonacci_correct] using hSpec

/-- 高速倍加法の公開関数も、任意の二添字で Fibonacci 加法公式を満たす。 -/
theorem fibonacci_add (m n : Nat) :
    LeanExperiments.fibonacci (m + n + 1) =
      LeanExperiments.fibonacci m * LeanExperiments.fibonacci n +
        LeanExperiments.fibonacci (m + 1) * LeanExperiments.fibonacci (n + 1) := by
  rw [fibonacci_correct (m + n + 1), fibonacci_correct m, fibonacci_correct n,
    fibonacci_correct (m + 1), fibonacci_correct (n + 1), fibonacciSpec_add]

/-- 正の添字 `m` に対し、`F m` は `m` の任意の倍数位置の Fibonacci 数を割り切る。

乗数に関する帰納法を行う。加法公式で `F (m*k+m)` を分解すると、第一項は
帰納法の仮定から `F m` の倍数であり、第二項には `F m` が因子として現れる。
有限個の添字の確認ではなく、全ての `m > 0` と乗数に対して成立する。
-/
theorem fibonacci_dvd_at_multiples {m k : Nat} (hm : 0 < m) :
    LeanExperiments.fibonacci m ∣ LeanExperiments.fibonacci (m * k) := by
  induction k with
  | zero => simp [fibonacci_correct, fibonacciSpec, fibonacciSpecAux]
  | succ k ih =>
      have hStep : m * (k + 1) = m * k + m := by simp [Nat.mul_succ]
      have hPrevious : m - 1 + 1 = m := Nat.sub_add_cancel (by omega)
      have hAddition := fibonacci_add (m * k) (m - 1)
      rw [hPrevious] at hAddition
      have hIndex : m * k + (m - 1) + 1 = m * k + m := by
        simp [Nat.add_assoc, hPrevious]
      rw [hIndex] at hAddition
      rw [hStep, hAddition]
      rcases ih with ⟨quotient, hQuotient⟩
      refine ⟨quotient * LeanExperiments.fibonacci (m - 1) +
        LeanExperiments.fibonacci (m * k + 1), ?_⟩
      rw [hQuotient]
      ring

/-- 正の添字 `m` が `n` を割り切るなら、`F m` は `F n` を割り切る。

添字の整除性を倍数表示に直し、倍数位置の一般定理を適用する。Fibonacci 数の
整除性を、値の計算なしに添字間の関係だけから導ける。
-/
theorem fibonacci_dvd_of_dvd_index {m n : Nat} (hm : 0 < m) (hIndex : m ∣ n) :
    LeanExperiments.fibonacci m ∣ LeanExperiments.fibonacci n := by
  obtain ⟨multiplier, rfl⟩ := hIndex
  exact fibonacci_dvd_at_multiples hm

/-- 高速倍加法の公開関数も、通常の Fibonacci 漸化式を任意の添字で満たす。 -/
theorem fibonacci_succ_succ (n : Nat) :
    LeanExperiments.fibonacci (n + 2) =
      LeanExperiments.fibonacci n + LeanExperiments.fibonacci (n + 1) := by
  simpa only [fibonacci_correct] using fibonacciSpec_succ_succ n

/-- 参照仕様を Mathlib の Fibonacci 列 `Nat.fib` と一致させる。

両者は先頭2項と2段階漸化式を共有するため、二段階帰納法で一致する。
これにより Mathlib が証明した一般性の高い Fibonacci の性質を、実装に移せる。
-/
theorem fibonacci_eq_natFib (n : Nat) :
    LeanExperiments.fibonacci n = Nat.fib n := by
  rw [fibonacci_correct]
  induction n using Nat.twoStepInduction with
  | zero => rfl
  | one => rfl
  | more n ih₀ ih₁ =>
      rw [fibonacciSpec_succ_succ, Nat.fib_add_two, ih₀, ih₁]

/-- 高速倍加法の結果は、二つの添字の最大公約数に対応する Fibonacci 数である。

Mathlib の `Nat.fib_gcd` を実装関数へ移した一般定理であり、有限個の Fibonacci 値の
列挙を用いず、任意の二添字の出力間の最大公約数を特徴付ける。
-/
theorem fibonacci_gcd (m n : Nat) :
    LeanExperiments.fibonacci (Nat.gcd m n) =
      Nat.gcd (LeanExperiments.fibonacci m) (LeanExperiments.fibonacci n) := by
  rw [fibonacci_eq_natFib, fibonacci_eq_natFib, fibonacci_eq_natFib]
  exact Nat.fib_gcd m n

/-- Cassini の恒等式を自然数の等式として表したもの。

添字が偶数なら `F (n+1)^2 = F n * F (n+2) + 1`、奇数なら積の側が 1 大きい。
符号付き差を使わず、隣接項の漸化式と偶奇の交代から任意の添字について証明する。
-/
theorem fibonacci_cassini_even_odd (n : Nat) :
    (if n % 2 = 0 then
      LeanExperiments.fibonacci (n + 1) * LeanExperiments.fibonacci (n + 1) =
        LeanExperiments.fibonacci n * LeanExperiments.fibonacci (n + 2) + 1
    else
      LeanExperiments.fibonacci n * LeanExperiments.fibonacci (n + 2) =
        LeanExperiments.fibonacci (n + 1) * LeanExperiments.fibonacci (n + 1) + 1) := by
  induction n with
  | zero => simp [fibonacci_correct, fibonacciSpec, fibonacciSpecAux]
  | succ n ih =>
      have hFirst := fibonacci_succ_succ n
      have hSecond : LeanExperiments.fibonacci (n + 3) =
          LeanExperiments.fibonacci (n + 1) + LeanExperiments.fibonacci (n + 2) := by
        simpa only [show n + 1 + 2 = n + 3 by omega] using
          fibonacci_succ_succ (n + 1)
      by_cases hEven : n % 2 = 0
      · have hOddNext : (n + 1) % 2 ≠ 0 := by omega
        simp only [ite_eq_right hOddNext]
        rw [hFirst, hSecond]
        have hIH : LeanExperiments.fibonacci (n + 1) * LeanExperiments.fibonacci (n + 1) =
            LeanExperiments.fibonacci n * LeanExperiments.fibonacci (n + 2) + 1 := by
          simpa [hEven] using ih
        nlinarith
      · have hEvenNext : (n + 1) % 2 = 0 := by omega
        simp only [ite_eq_left hEvenNext]
        rw [hFirst, hSecond]
        have hIH : LeanExperiments.fibonacci n * LeanExperiments.fibonacci (n + 2) =
            LeanExperiments.fibonacci (n + 1) * LeanExperiments.fibonacci (n + 1) + 1 := by
          simpa [hEven] using ih
        nlinarith

/-- 連続する2つの Fibonacci 数は任意の添字で互いに素である。 -/
theorem fibonacci_adjacent_coprime (n : Nat) :
    Nat.Coprime (LeanExperiments.fibonacci n)
      (LeanExperiments.fibonacci (n + 1)) := by
  induction n with
  | zero =>
      rw [fibonacci_correct 0, fibonacci_correct 1]
      decide
  | succ n ih =>
      rw [show (n + 1) + 1 = n + 2 by omega, fibonacci_succ_succ n]
      rw [Nat.coprime_comm, Nat.coprime_add_self_left]
      exact ih

/-- 添字0から `n` までの Fibonacci 数を順に足した値。 -/
def fibonacciPrefixSum : Nat → Nat
  | 0 => LeanExperiments.fibonacci 0
  | n + 1 => fibonacciPrefixSum n + LeanExperiments.fibonacci (n + 1)

/-- 先頭からの累積和に1を足すと、2つ先の Fibonacci 数になる。 -/
theorem fibonacci_prefix_sum_identity (n : Nat) :
    fibonacciPrefixSum n + 1 = LeanExperiments.fibonacci (n + 2) := by
  induction n with
  | zero => native_decide
  | succ n ih =>
      calc
        fibonacciPrefixSum (n + 1) + 1 =
            (fibonacciPrefixSum n + 1) + LeanExperiments.fibonacci (n + 1) := by
          simp only [fibonacciPrefixSum]
          omega
        _ = LeanExperiments.fibonacci (n + 2) + LeanExperiments.fibonacci (n + 1) := by
          rw [ih]
        _ = LeanExperiments.fibonacci (n + 3) := by
          rw [show n + 3 = (n + 1) + 2 by omega]
          rw [fibonacci_succ_succ (n + 1)]
          ac_rfl

/-- 添字0から `n` までの Fibonacci 数の平方を順に足した値。 -/
def fibonacciSquarePrefixSum : Nat → Nat
  | 0 => LeanExperiments.fibonacci 0 * LeanExperiments.fibonacci 0
  | n + 1 =>
      fibonacciSquarePrefixSum n +
        LeanExperiments.fibonacci (n + 1) * LeanExperiments.fibonacci (n + 1)

/-- Fibonacci 数の平方和は、末尾2項の積に一致する。 -/
theorem fibonacci_square_prefix_sum_identity (n : Nat) :
    fibonacciSquarePrefixSum n =
      LeanExperiments.fibonacci n * LeanExperiments.fibonacci (n + 1) := by
  induction n with
  | zero => native_decide
  | succ n ih =>
      calc
        fibonacciSquarePrefixSum (n + 1) =
            LeanExperiments.fibonacci n * LeanExperiments.fibonacci (n + 1) +
              LeanExperiments.fibonacci (n + 1) * LeanExperiments.fibonacci (n + 1) := by
          simp only [fibonacciSquarePrefixSum]
          rw [ih]
        _ = LeanExperiments.fibonacci (n + 1) *
              (LeanExperiments.fibonacci n + LeanExperiments.fibonacci (n + 1)) := by
          rw [Nat.mul_add]
          ac_rfl
        _ = LeanExperiments.fibonacci (n + 1) * LeanExperiments.fibonacci (n + 2) := by
          rw [← fibonacci_succ_succ n]

/-- Fibonacci の実装値は隣接する添字について単調非減少である。 -/
theorem fibonacci_monotone (n : Nat) :
    LeanExperiments.fibonacci n ≤ LeanExperiments.fibonacci (n + 1) := by
  simpa [LeanExperiments.fibonacci, fibonacciPair_eq_spec_pair] using
    fibonacciPair_first_le_second n

/-- 添字が前後する任意の二項についても、Fibonacci 数は単調非減少である。 -/
theorem fibonacci_mono_of_le {m n : Nat} (hmn : m ≤ n) :
    LeanExperiments.fibonacci m ≤ LeanExperiments.fibonacci n := by
  induction n with
  | zero =>
      have hZero : m = 0 := by omega
      subst m
      exact Nat.le_refl _
  | succ n ih =>
      by_cases hEqual : m = n + 1
      · subst m
        exact Nat.le_refl _
      · have hPrevious : m ≤ n := by omega
        exact Nat.le_trans (ih hPrevious) (fibonacci_monotone n)

/-- 添字を2つ進めると Fibonacci 数は少なくとも2倍になる。 -/
theorem fibonacci_double_step_lower_bound (n : Nat) :
    2 * LeanExperiments.fibonacci n ≤ LeanExperiments.fibonacci (n + 2) := by
  rw [fibonacci_succ_succ]
  have hMonotone := fibonacci_monotone n
  omega

/-- 奇数添字の Fibonacci 数は、添字の半分に応じた2の累乗以上である。 -/
theorem fibonacci_exponential_lower_bound (n : Nat) :
    2 ^ n ≤ LeanExperiments.fibonacci (2 * n + 1) := by
  induction n with
  | zero => native_decide
  | succ n ih =>
      have hGrowth := fibonacci_double_step_lower_bound (2 * n + 1)
      calc
        2 ^ (n + 1) = 2 * 2 ^ n := by rw [Nat.pow_succ]; omega
        _ ≤ 2 * LeanExperiments.fibonacci (2 * n + 1) :=
          Nat.mul_le_mul_left 2 ih
        _ ≤ LeanExperiments.fibonacci (2 * n + 3) := by
          simpa only [show (2 * n + 1) + 2 = 2 * n + 3 by omega] using hGrowth
        _ = LeanExperiments.fibonacci (2 * (n + 1) + 1) := by
          congr 1

/-- 任意の添字では、`F(n+1)` が `2^(n/2)` 以上になる。 -/
theorem fibonacci_exponential_lower_bound_all (n : Nat) :
    2 ^ (n / 2) ≤ LeanExperiments.fibonacci (n + 1) := by
  let half := n / 2
  have hOddIndex : 2 * half + 1 ≤ n + 1 := by
    dsimp [half]
    omega
  exact Nat.le_trans (fibonacci_exponential_lower_bound half)
    (fibonacci_mono_of_le hOddIndex)

/-- すべての自然数について、Fibonacci 数は添字の2の累乗以下である。 -/
theorem fibonacci_upper_bound_pow_two (n : Nat) :
    LeanExperiments.fibonacci n ≤ 2 ^ n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
      cases n with
      | zero => native_decide
      | succ n =>
          cases n with
          | zero => native_decide
          | succ n =>
              have hPrevious := ih n (by omega)
              have hCurrent := ih (n + 1) (by omega)
              have hPowSucc : 2 ^ (n + 1) = 2 ^ n * 2 := by
                rw [Nat.pow_succ]
              have hPowTwoSucc : 2 ^ (n + 2) = 2 ^ n * 4 := by
                calc
                  2 ^ (n + 2) = 2 ^ (n + 1) * 2 := by rw [Nat.pow_succ]
                  _ = (2 ^ n * 2) * 2 := by rw [Nat.pow_succ]
                  _ = 2 ^ n * 4 := by omega
              rw [fibonacci_succ_succ n]
              calc
                LeanExperiments.fibonacci n + LeanExperiments.fibonacci (n + 1) ≤
                    2 ^ n + 2 ^ (n + 1) := Nat.add_le_add hPrevious hCurrent
                _ = 2 ^ n + 2 ^ n * 2 := by rw [hPowSucc]
                _ ≤ 2 ^ n * 4 := by omega
                _ = 2 ^ (n + 2) := hPowTwoSucc.symm

/-- 添字を1つ進めた Fibonacci 数は、より強い上界 `2^n` を満たす。 -/
theorem fibonacci_upper_bound_pow_two_shifted (n : Nat) :
    LeanExperiments.fibonacci (n + 1) ≤ 2 ^ n := by
  induction n with
  | zero => native_decide
  | succ n ih =>
      have hPrevious : LeanExperiments.fibonacci n ≤ 2 ^ n :=
        Nat.le_trans (fibonacci_monotone n) ih
      have hRecurrence := fibonacci_succ_succ n
      calc
        LeanExperiments.fibonacci (n + 1 + 1) = LeanExperiments.fibonacci (n + 2) := by
          congr 1
        _ = LeanExperiments.fibonacci n + LeanExperiments.fibonacci (n + 1) := hRecurrence
        _ ≤ 2 ^ n + 2 ^ n := Nat.add_le_add hPrevious ih
        _ = 2 ^ (n + 1) := by rw [Nat.pow_succ]; omega

/-- Fibonacci 数の `n+1` 項は `2^(n/2)` 以上 `2^n` 以下に収まる。 -/
theorem fibonacci_growth_bounds (n : Nat) :
    2 ^ (n / 2) ≤ LeanExperiments.fibonacci (n + 1) ∧
      LeanExperiments.fibonacci (n + 1) ≤ 2 ^ n := by
  exact ⟨fibonacci_exponential_lower_bound_all n,
    fibonacci_upper_bound_pow_two_shifted n⟩

/-- 正の添字では高速倍加法が返す Fibonacci 数も正である。

偶数分岐では半分の添字が正になり、帰納法から `a > 0` を得る。さらに
`a ≤ b` より `2*b-a > 0` なので積が正になる。奇数分岐は `b > 0` から
`a*a+b*b > 0` が従う。
-/
theorem fibonacciPair_first_positive (n : Nat) (hn : 0 < n) :
    0 < (LeanExperiments.fibonacciPair n).1 := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    cases n with
    | zero => omega
    | succ n =>
      let half := (n + 1) / 2
      have hHalfLt : half < n + 1 := by dsimp [half]; omega
      cases hPair : LeanExperiments.fibonacciPair half with
      | mk a b =>
        have hB : 0 < b := by
          have h := fibonacciPair_next_positive half
          simpa [hPair] using h
        have hAB : a ≤ b := by
          have h := fibonacciPair_first_le_second half
          simpa [hPair] using h
        by_cases hEven : (n + 1) % 2 == 0
        · have hEvenMod : (n + 1) % 2 = 0 := beq_iff_eq.mp hEven
          have hHalfPos : 0 < half := by dsimp [half]; omega
          have hA : 0 < a := by
            have h := ih half hHalfLt hHalfPos
            simpa [hPair] using h
          have hFactorBound : a < 2 * b := by omega
          have hFactor : 0 < 2 * b - a := Nat.sub_pos_of_lt hFactorBound
          have hProduct : 0 < a * (2 * b - a) := Nat.mul_pos hA hFactor
          simpa [LeanExperiments.fibonacciPair, half, hPair, hEven] using hProduct
        · have hSquare : 0 < b * b := Nat.mul_pos hB hB
          have hOdd : 0 < a * a + b * b := by omega
          simpa [LeanExperiments.fibonacciPair, half, hPair, hEven] using hOdd

/-- Fibonacci 実装の値は、0以外の添字で必ず正になる。 -/
theorem fibonacci_positive_of_pos (n : Nat) (hn : 0 < n) :
    0 < LeanExperiments.fibonacci n := by
  exact fibonacciPair_first_positive n hn

/-- 添字2以降では Fibonacci の実装値が狭義に増加する。 -/
theorem fibonacci_strict_mono_from_two (n : Nat) (hn : 2 ≤ n) :
    LeanExperiments.fibonacci n < LeanExperiments.fibonacci (n + 1) := by
  have hRecurrence := fibonacci_succ_succ (n - 1)
  have hPreviousIndex : n - 1 + 1 = n := by omega
  have hNextIndex : n - 1 + 2 = n + 1 := by omega
  rw [hPreviousIndex, hNextIndex] at hRecurrence
  have hPreviousPositive :=
    fibonacci_positive_of_pos (n - 1) (by omega)
  omega

/-- Fibonacci 実装の値が0になるのは、添字が0の場合に限る。 -/
theorem fibonacci_eq_zero_iff (n : Nat) :
    LeanExperiments.fibonacci n = 0 ↔ n = 0 := by
  constructor
  · intro hValue
    by_cases hZero : n = 0
    · exact hZero
    · have hPositive := fibonacci_positive_of_pos n (Nat.pos_of_ne_zero hZero)
      omega
  · rintro rfl
    native_decide

/-- 最初の項では、`F 0 = 0` となる。 -/
theorem fibonacci_zero_boundary : LeanExperiments.fibonacci 0 = 0 := by
  native_decide

/-- 2 番目の項では、`F 1 = 1` となる。 -/
theorem fibonacci_one_boundary : LeanExperiments.fibonacci 1 = 1 := by
  native_decide

/-- `F 2 = 1` を確認する。 -/
theorem fibonacci_two_boundary : LeanExperiments.fibonacci 2 = 1 := by
  native_decide

/-- Fibonacci 数が1になる添字は1と2に限られる。

3以上の添字では、2からの狭義単調性により `F n > F 2 = 1` となる。
この特徴付けを、最大公約数を介した互いに素性の判定に使う。
-/
theorem fibonacci_eq_one_iff (n : Nat) :
    LeanExperiments.fibonacci n = 1 ↔ n = 1 ∨ n = 2 := by
  constructor
  · intro hValue
    by_cases hOne : n = 1
    · exact Or.inl hOne
    · by_cases hTwo : n = 2
      · exact Or.inr hTwo
      · have hZero : n ≠ 0 := by
          intro hZero
          subst n
          simp [fibonacci_zero_boundary] at hValue
        have hThree : 3 ≤ n := by omega
        have hStrict := fibonacci_strict_mono_from_two 2 (by omega)
        rw [fibonacci_two_boundary] at hStrict
        have hMonotone := fibonacci_mono_of_le (m := 3) (n := n) hThree
        have hGreater : 1 < LeanExperiments.fibonacci n := Nat.lt_of_lt_of_le hStrict hMonotone
        omega
  · rintro (rfl | rfl) <;> simp [fibonacci_one_boundary, fibonacci_two_boundary]

/-- 二つの Fibonacci 数が互いに素である条件は、添字の最大公約数が1または2であること。

`fibonacci_gcd` と値1の添字の特徴付けを合成し、連続添字以外の互いに素条件も
任意の添字対について判定する。
-/
theorem fibonacci_coprime_iff_index_gcd_eq_one_or_two (m n : Nat) :
    Nat.Coprime (LeanExperiments.fibonacci m) (LeanExperiments.fibonacci n) ↔
      Nat.gcd m n = 1 ∨ Nat.gcd m n = 2 := by
  rw [Nat.coprime_iff_gcd_eq_one, ← fibonacci_gcd, fibonacci_eq_one_iff]

/-- 周期の直前の項が1、周期位置の項が0なら、任意の法で剰余が周期化する。 -/
theorem fibonacci_mod_periodic_of_predecessor_one_and_period_zero
    (modulus period n : Nat) (hPeriod : 0 < period)
    (hPredecessor : LeanExperiments.fibonacci (period - 1) % modulus = 1)
    (hAtPeriod : LeanExperiments.fibonacci period % modulus = 0) :
    LeanExperiments.fibonacci (n + period) % modulus =
      LeanExperiments.fibonacci n % modulus := by
  have hIndex : n + period = n + (period - 1) + 1 := by omega
  have hFirstProduct :
      (LeanExperiments.fibonacci n * LeanExperiments.fibonacci (period - 1)) % modulus =
        LeanExperiments.fibonacci n % modulus := by
    rw [Nat.mul_mod, hPredecessor]
    simp
  have hSecondProduct :
      (LeanExperiments.fibonacci (n + 1) * LeanExperiments.fibonacci period) % modulus = 0 := by
    rw [Nat.mul_mod, hAtPeriod]
    simp
  calc
    LeanExperiments.fibonacci (n + period) % modulus =
        (LeanExperiments.fibonacci n * LeanExperiments.fibonacci (period - 1) +
          LeanExperiments.fibonacci (n + 1) * LeanExperiments.fibonacci period) % modulus := by
      rw [hIndex, fibonacci_add, Nat.sub_add_cancel hPeriod]
    _ = LeanExperiments.fibonacci n % modulus := by
      rw [Nat.add_mod, hFirstProduct, hSecondProduct]
      simp

/-- 上の仮定の下では、周期の倍数だけ進めても剰余が保たれる。 -/
theorem fibonacci_mod_periodic_mul_of_predecessor_one_and_period_zero
    (modulus period n k : Nat) (hPeriod : 0 < period)
    (hPredecessor : LeanExperiments.fibonacci (period - 1) % modulus = 1)
    (hAtPeriod : LeanExperiments.fibonacci period % modulus = 0) :
    LeanExperiments.fibonacci (n + period * k) % modulus =
      LeanExperiments.fibonacci n % modulus := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hIndex : n + period * (k + 1) = (n + period * k) + period := by
      rw [Nat.mul_succ]
      omega
    rw [hIndex,
      fibonacci_mod_periodic_of_predecessor_one_and_period_zero
        modulus period (n + period * k) hPeriod hPredecessor hAtPeriod,
      ih]

/-- 周期内の有限条件から、全添字における割り切り条件を導く。 -/
theorem fibonacci_divisible_iff_index_multiple_of_period
    (modulus period divisor n : Nat) (hPeriod : 0 < period)
    (hPredecessor : LeanExperiments.fibonacci (period - 1) % modulus = 1)
    (hAtPeriod : LeanExperiments.fibonacci period % modulus = 0)
    (hDivisorDvdPeriod : divisor ∣ period)
    (hResidues : ∀ residue, residue < period →
      (LeanExperiments.fibonacci residue % modulus = 0 ↔ residue % divisor = 0)) :
    LeanExperiments.fibonacci n % modulus = 0 ↔ n % divisor = 0 := by
  let block := n / period
  let residue := n % period
  have hIndex : n = residue + period * block := by
    dsimp [block, residue]
    exact (Nat.mod_add_div n period).symm
  have hDecomposition : n = period * block + residue := by
    rw [hIndex, Nat.add_comm]
  have hResidue : residue < period := by
    dsimp [residue]
    exact Nat.mod_lt n hPeriod
  have hFibonacciResidue :
      LeanExperiments.fibonacci n % modulus = LeanExperiments.fibonacci residue % modulus := by
    rw [hIndex]
    exact fibonacci_mod_periodic_mul_of_predecessor_one_and_period_zero
      modulus period residue block hPeriod hPredecessor hAtPeriod
  have hPeriodModDivisor : period % divisor = 0 :=
    Nat.dvd_iff_mod_eq_zero.mp hDivisorDvdPeriod
  have hIndexResidue : n % divisor = residue % divisor := by
    calc
      n % divisor = (period * block + residue) % divisor := by rw [hDecomposition]
      _ = residue % divisor := by
        rw [Nat.add_mod, Nat.mul_mod, hPeriodModDivisor]
        simp
  rw [hFibonacciResidue, hIndexResidue]
  exact hResidues residue hResidue

/-- 添字を3で割った余りに応じて、Fibonacci 数の偶奇は `0, 1, 1` と循環する。 -/
theorem fibonacci_mod_two_cycle (k : Nat) :
    (LeanExperiments.fibonacci (3 * k) % 2 = 0) ∧
    (LeanExperiments.fibonacci (3 * k + 1) % 2 = 1) ∧
    (LeanExperiments.fibonacci (3 * k + 2) % 2 = 1) := by
  induction k with
  | zero => native_decide
  | succ k ih =>
    rcases ih with ⟨h0, h1, h2⟩
    have recurrence0 : LeanExperiments.fibonacci (3 * (k + 1)) =
        LeanExperiments.fibonacci (3 * k + 1) + LeanExperiments.fibonacci (3 * k + 2) := by
      simpa only [show (3 * k + 1) + 2 = 3 * (k + 1) by omega,
        show (3 * k + 1) + 1 = 3 * k + 2 by omega] using
        fibonacci_succ_succ (3 * k + 1)
    have recurrence1 : LeanExperiments.fibonacci (3 * (k + 1) + 1) =
        LeanExperiments.fibonacci (3 * k + 2) + LeanExperiments.fibonacci (3 * (k + 1)) := by
      simpa only [show (3 * k + 2) + 2 = 3 * (k + 1) + 1 by omega,
        show (3 * k + 2) + 1 = 3 * (k + 1) by omega] using
        fibonacci_succ_succ (3 * k + 2)
    have recurrence2 : LeanExperiments.fibonacci (3 * (k + 1) + 2) =
        LeanExperiments.fibonacci (3 * (k + 1)) +
          LeanExperiments.fibonacci (3 * (k + 1) + 1) := by
      simpa only [show (3 * k + 3) + 2 = 3 * (k + 1) + 2 by omega,
        show (3 * k + 3) + 1 = 3 * (k + 1) + 1 by omega,
        show 3 * k + 3 = 3 * (k + 1) by omega] using
        fibonacci_succ_succ (3 * k + 3)
    have h0Next : LeanExperiments.fibonacci (3 * (k + 1)) % 2 = 0 := by
      rw [recurrence0, Nat.add_mod, h1, h2]
    have h1Next : LeanExperiments.fibonacci (3 * (k + 1) + 1) % 2 = 1 := by
      rw [recurrence1, Nat.add_mod, h2, h0Next]
    have h2Next : LeanExperiments.fibonacci (3 * (k + 1) + 2) % 2 = 1 := by
      rw [recurrence2, Nat.add_mod, h0Next, h1Next]
    exact ⟨h0Next, h1Next, h2Next⟩

/-- Fibonacci 数が偶数であることと、その添字が3の倍数であることは同値。 -/
def fibonacci_mod_two_residueCheck : Bool :=
  (List.range 3).all fun residue =>
    decide (LeanExperiments.fibonacci residue % 2 = 0 ↔ residue % 3 = 0)

/-- 2を法とする剰余代表3個全てで、偶数性と添字条件が一致する。 -/
theorem fibonacci_mod_two_residueCheck_passes :
    fibonacci_mod_two_residueCheck = true := by
  native_decide

/-- Fibonacci 数が偶数であることと、その添字が3の倍数であることは同値。 -/
theorem fibonacci_even_iff_index_multiple_of_three (n : Nat) :
    LeanExperiments.fibonacci n % 2 = 0 ↔ n % 3 = 0 := by
  have hPredecessor : LeanExperiments.fibonacci 2 % 2 = 1 := by native_decide
  have hAtPeriod : LeanExperiments.fibonacci 3 % 2 = 0 := by native_decide
  exact fibonacci_divisible_iff_index_multiple_of_period
    2 3 3 n (by omega) hPredecessor hAtPeriod
    (⟨1, by omega⟩) (by
      intro residue hResidue
      have hAll : ∀ candidate ∈ List.range 3,
          decide (LeanExperiments.fibonacci candidate % 2 = 0 ↔ candidate % 3 = 0) = true :=
        List.all_eq_true.mp fibonacci_mod_two_residueCheck_passes
      exact of_decide_eq_true (hAll residue (List.mem_range.mpr hResidue)))

/-- Fibonacci 数の5を法とする剰余は、添字を20増やしても変わらない。 -/
theorem fibonacci_mod_five_periodic (n : Nat) :
    LeanExperiments.fibonacci (n + 20) % 5 =
      LeanExperiments.fibonacci n % 5 := by
  have hPredecessor : LeanExperiments.fibonacci 19 % 5 = 1 := by
    native_decide
  have hAtPeriod : LeanExperiments.fibonacci 20 % 5 = 0 := by
    native_decide
  exact fibonacci_mod_periodic_of_predecessor_one_and_period_zero
    5 20 n (by omega) hPredecessor hAtPeriod

/-- 添字を20の倍数だけ進めても、Fibonacci 数の5を法とする剰余は保たれる。 -/
theorem fibonacci_mod_five_periodic_mul (n k : Nat) :
    LeanExperiments.fibonacci (n + 20 * k) % 5 =
      LeanExperiments.fibonacci n % 5 := by
  have hPredecessor : LeanExperiments.fibonacci 19 % 5 = 1 := by
    native_decide
  have hAtPeriod : LeanExperiments.fibonacci 20 % 5 = 0 := by
    native_decide
  exact fibonacci_mod_periodic_mul_of_predecessor_one_and_period_zero
    5 20 n k (by omega) hPredecessor hAtPeriod

/-- 20個の剰余代表について、5で割り切れる添字は5の倍数に限られるかを確認する。 -/
def fibonacci_mod_five_residueCheck : Bool :=
  (List.range 20).all fun residue =>
    decide (LeanExperiments.fibonacci residue % 5 = 0 ↔ residue % 5 = 0)

/-- 20個全ての剰余代表で、5による割り切り条件が添字の条件と一致する。 -/
theorem fibonacci_mod_five_residueCheck_passes :
    fibonacci_mod_five_residueCheck = true := by
  native_decide

/-- 20個の剰余代表について、5で割り切れる添字は5の倍数に限られる。 -/
private theorem fibonacci_mod_five_zero_iff_residue_zero (residue : Nat)
    (hResidue : residue < 20) :
    LeanExperiments.fibonacci residue % 5 = 0 ↔ residue % 5 = 0 := by
  have hAll : ∀ candidate ∈ List.range 20,
      decide (LeanExperiments.fibonacci candidate % 5 = 0 ↔ candidate % 5 = 0) = true :=
    List.all_eq_true.mp fibonacci_mod_five_residueCheck_passes
  exact of_decide_eq_true (hAll residue (List.mem_range.mpr hResidue))

/-- Fibonacci 数が5で割り切れることと、添字が5の倍数であることは同値。 -/
theorem fibonacci_divisible_by_five_iff_index_multiple_of_five (n : Nat) :
    LeanExperiments.fibonacci n % 5 = 0 ↔ n % 5 = 0 := by
  have hPredecessor : LeanExperiments.fibonacci 19 % 5 = 1 := by
    native_decide
  have hAtPeriod : LeanExperiments.fibonacci 20 % 5 = 0 := by
    native_decide
  exact fibonacci_divisible_iff_index_multiple_of_period
    5 20 5 n (by omega) hPredecessor hAtPeriod
    (⟨4, by omega⟩) (by
      intro residue hResidue
      exact fibonacci_mod_five_zero_iff_residue_zero residue hResidue)

/-- Fibonacci 数の7を法とする剰余は、添字を16増やしても変わらない。 -/
theorem fibonacci_mod_seven_periodic (n : Nat) :
    LeanExperiments.fibonacci (n + 16) % 7 =
      LeanExperiments.fibonacci n % 7 := by
  have hPredecessor : LeanExperiments.fibonacci 15 % 7 = 1 := by
    native_decide
  have hAtPeriod : LeanExperiments.fibonacci 16 % 7 = 0 := by
    native_decide
  exact fibonacci_mod_periodic_of_predecessor_one_and_period_zero
    7 16 n (by omega) hPredecessor hAtPeriod

/-- 添字を16の倍数だけ進めても、Fibonacci 数の7を法とする剰余は保たれる。 -/
theorem fibonacci_mod_seven_periodic_mul (n k : Nat) :
    LeanExperiments.fibonacci (n + 16 * k) % 7 =
      LeanExperiments.fibonacci n % 7 := by
  have hPredecessor : LeanExperiments.fibonacci 15 % 7 = 1 := by
    native_decide
  have hAtPeriod : LeanExperiments.fibonacci 16 % 7 = 0 := by
    native_decide
  exact fibonacci_mod_periodic_mul_of_predecessor_one_and_period_zero
    7 16 n k (by omega) hPredecessor hAtPeriod

/-- 16個の剰余代表における、7での割り切り条件を有限確認する。 -/
def fibonacci_mod_seven_residueCheck : Bool :=
  (List.range 16).all fun residue =>
    decide (LeanExperiments.fibonacci residue % 7 = 0 ↔ residue % 8 = 0)

/-- 16個全ての剰余代表で、7による割り切り条件が添字の条件と一致する。 -/
theorem fibonacci_mod_seven_residueCheck_passes :
    fibonacci_mod_seven_residueCheck = true := by
  native_decide

/-- 16個の剰余代表では、Fibonacci 数が7で割り切れるのは添字が8の倍数の場合。 -/
private theorem fibonacci_mod_seven_zero_iff_residue_multiple_of_eight
    (residue : Nat) (hResidue : residue < 16) :
    LeanExperiments.fibonacci residue % 7 = 0 ↔ residue % 8 = 0 := by
  have hAll : ∀ candidate ∈ List.range 16,
      decide (LeanExperiments.fibonacci candidate % 7 = 0 ↔ candidate % 8 = 0) = true :=
    List.all_eq_true.mp fibonacci_mod_seven_residueCheck_passes
  exact of_decide_eq_true (hAll residue (List.mem_range.mpr hResidue))

/-- Fibonacci 数が7で割り切れることと、添字が8の倍数であることは同値。 -/
theorem fibonacci_divisible_by_seven_iff_index_multiple_of_eight (n : Nat) :
    LeanExperiments.fibonacci n % 7 = 0 ↔ n % 8 = 0 := by
  have hPredecessor : LeanExperiments.fibonacci 15 % 7 = 1 := by
    native_decide
  have hAtPeriod : LeanExperiments.fibonacci 16 % 7 = 0 := by
    native_decide
  exact fibonacci_divisible_iff_index_multiple_of_period
    7 16 8 n (by omega) hPredecessor hAtPeriod
    (⟨2, by omega⟩) (by
      intro residue hResidue
      exact fibonacci_mod_seven_zero_iff_residue_multiple_of_eight residue hResidue)

/-- Fibonacci 数の8を法とする剰余は、添字を12増やしても変わらない。 -/
theorem fibonacci_mod_eight_periodic (n : Nat) :
    LeanExperiments.fibonacci (n + 12) % 8 =
      LeanExperiments.fibonacci n % 8 := by
  have hPredecessor : LeanExperiments.fibonacci 11 % 8 = 1 := by
    native_decide
  have hAtPeriod : LeanExperiments.fibonacci 12 % 8 = 0 := by
    native_decide
  exact fibonacci_mod_periodic_of_predecessor_one_and_period_zero
    8 12 n (by omega) hPredecessor hAtPeriod

/-- 添字を12の倍数だけ進めても、Fibonacci 数の8を法とする剰余は保たれる。 -/
theorem fibonacci_mod_eight_periodic_mul (n k : Nat) :
    LeanExperiments.fibonacci (n + 12 * k) % 8 =
      LeanExperiments.fibonacci n % 8 := by
  have hPredecessor : LeanExperiments.fibonacci 11 % 8 = 1 := by
    native_decide
  have hAtPeriod : LeanExperiments.fibonacci 12 % 8 = 0 := by
    native_decide
  exact fibonacci_mod_periodic_mul_of_predecessor_one_and_period_zero
    8 12 n k (by omega) hPredecessor hAtPeriod

/-- 12個の剰余代表における、8での割り切り条件を有限確認する。 -/
def fibonacci_mod_eight_residueCheck : Bool :=
  (List.range 12).all fun residue =>
    decide (LeanExperiments.fibonacci residue % 8 = 0 ↔ residue % 6 = 0)

/-- 12個全ての剰余代表で、8による割り切り条件が添字の条件と一致する。 -/
theorem fibonacci_mod_eight_residueCheck_passes :
    fibonacci_mod_eight_residueCheck = true := by
  native_decide

/-- 12個の剰余代表では、Fibonacci 数が8で割り切れるのは添字が6の倍数の場合。 -/
private theorem fibonacci_mod_eight_zero_iff_residue_multiple_of_six
    (residue : Nat) (hResidue : residue < 12) :
    LeanExperiments.fibonacci residue % 8 = 0 ↔ residue % 6 = 0 := by
  have hAll : ∀ candidate ∈ List.range 12,
      decide (LeanExperiments.fibonacci candidate % 8 = 0 ↔ candidate % 6 = 0) = true :=
    List.all_eq_true.mp fibonacci_mod_eight_residueCheck_passes
  exact of_decide_eq_true (hAll residue (List.mem_range.mpr hResidue))

/-- Fibonacci 数が8で割り切れることと、添字が6の倍数であることは同値。 -/
theorem fibonacci_divisible_by_eight_iff_index_multiple_of_six (n : Nat) :
    LeanExperiments.fibonacci n % 8 = 0 ↔ n % 6 = 0 := by
  have hPredecessor : LeanExperiments.fibonacci 11 % 8 = 1 := by
    native_decide
  have hAtPeriod : LeanExperiments.fibonacci 12 % 8 = 0 := by
    native_decide
  exact fibonacci_divisible_iff_index_multiple_of_period
    8 12 6 n (by omega) hPredecessor hAtPeriod
    (⟨2, by omega⟩) (by
      intro residue hResidue
      exact fibonacci_mod_eight_zero_iff_residue_multiple_of_six residue hResidue)

/-- Fibonacci 数の16を法とする剰余は、添字を24増やしても変わらない。 -/
theorem fibonacci_mod_sixteen_periodic (n : Nat) :
    LeanExperiments.fibonacci (n + 24) % 16 =
      LeanExperiments.fibonacci n % 16 := by
  have hPredecessor : LeanExperiments.fibonacci 23 % 16 = 1 := by
    native_decide
  have hAtPeriod : LeanExperiments.fibonacci 24 % 16 = 0 := by
    native_decide
  exact fibonacci_mod_periodic_of_predecessor_one_and_period_zero
    16 24 n (by omega) hPredecessor hAtPeriod

/-- 添字を24の倍数だけ進めても、Fibonacci 数の16を法とする剰余は保たれる。 -/
theorem fibonacci_mod_sixteen_periodic_mul (n k : Nat) :
    LeanExperiments.fibonacci (n + 24 * k) % 16 =
      LeanExperiments.fibonacci n % 16 := by
  have hPredecessor : LeanExperiments.fibonacci 23 % 16 = 1 := by
    native_decide
  have hAtPeriod : LeanExperiments.fibonacci 24 % 16 = 0 := by
    native_decide
  exact fibonacci_mod_periodic_mul_of_predecessor_one_and_period_zero
    16 24 n k (by omega) hPredecessor hAtPeriod

/-- 24個の剰余代表における、16での割り切り条件を有限確認する。 -/
def fibonacci_mod_sixteen_residueCheck : Bool :=
  (List.range 24).all fun residue =>
    decide (LeanExperiments.fibonacci residue % 16 = 0 ↔ residue % 12 = 0)

/-- 24個全ての剰余代表で、16による割り切り条件が添字の条件と一致する。 -/
theorem fibonacci_mod_sixteen_residueCheck_passes :
    fibonacci_mod_sixteen_residueCheck = true := by
  native_decide

/-- 24個の剰余代表では、Fibonacci 数が16で割り切れるのは添字が12の倍数の場合。 -/
private theorem fibonacci_mod_sixteen_zero_iff_residue_multiple_of_twelve
    (residue : Nat) (hResidue : residue < 24) :
    LeanExperiments.fibonacci residue % 16 = 0 ↔ residue % 12 = 0 := by
  have hAll : ∀ candidate ∈ List.range 24,
      decide (LeanExperiments.fibonacci candidate % 16 = 0 ↔ candidate % 12 = 0) = true :=
    List.all_eq_true.mp fibonacci_mod_sixteen_residueCheck_passes
  exact of_decide_eq_true (hAll residue (List.mem_range.mpr hResidue))

/-- Fibonacci 数が16で割り切れることと、添字が12の倍数であることは同値。 -/
theorem fibonacci_divisible_by_sixteen_iff_index_multiple_of_twelve (n : Nat) :
    LeanExperiments.fibonacci n % 16 = 0 ↔ n % 12 = 0 := by
  have hPredecessor : LeanExperiments.fibonacci 23 % 16 = 1 := by
    native_decide
  have hAtPeriod : LeanExperiments.fibonacci 24 % 16 = 0 := by
    native_decide
  exact fibonacci_divisible_iff_index_multiple_of_period
    16 24 12 n (by omega) hPredecessor hAtPeriod
    (⟨2, by omega⟩) (by
      intro residue hResidue
      exact fibonacci_mod_sixteen_zero_iff_residue_multiple_of_twelve residue hResidue)

/-- Fibonacci 数の11を法とする剰余は、添字を10増やしても変わらない。 -/
theorem fibonacci_mod_eleven_periodic (n : Nat) :
    LeanExperiments.fibonacci (n + 10) % 11 =
      LeanExperiments.fibonacci n % 11 := by
  have hPredecessor : LeanExperiments.fibonacci 9 % 11 = 1 := by
    native_decide
  have hAtPeriod : LeanExperiments.fibonacci 10 % 11 = 0 := by
    native_decide
  exact fibonacci_mod_periodic_of_predecessor_one_and_period_zero
    11 10 n (by omega) hPredecessor hAtPeriod

/-- 添字を10の倍数だけ進めても、Fibonacci 数の11を法とする剰余は保たれる。 -/
theorem fibonacci_mod_eleven_periodic_mul (n k : Nat) :
    LeanExperiments.fibonacci (n + 10 * k) % 11 =
      LeanExperiments.fibonacci n % 11 := by
  have hPredecessor : LeanExperiments.fibonacci 9 % 11 = 1 := by
    native_decide
  have hAtPeriod : LeanExperiments.fibonacci 10 % 11 = 0 := by
    native_decide
  exact fibonacci_mod_periodic_mul_of_predecessor_one_and_period_zero
    11 10 n k (by omega) hPredecessor hAtPeriod

/-- 10個の剰余代表における、11での割り切り条件を有限確認する。 -/
def fibonacci_mod_eleven_residueCheck : Bool :=
  (List.range 10).all fun residue =>
    decide (LeanExperiments.fibonacci residue % 11 = 0 ↔ residue % 10 = 0)

/-- 10個全ての剰余代表で、11による割り切り条件が添字の条件と一致する。 -/
theorem fibonacci_mod_eleven_residueCheck_passes :
    fibonacci_mod_eleven_residueCheck = true := by
  native_decide

/-- 10個の剰余代表では、Fibonacci 数が11で割り切れるのは添字が10の倍数の場合。 -/
private theorem fibonacci_mod_eleven_zero_iff_residue_multiple_of_ten
    (residue : Nat) (hResidue : residue < 10) :
    LeanExperiments.fibonacci residue % 11 = 0 ↔ residue % 10 = 0 := by
  have hAll : ∀ candidate ∈ List.range 10,
      decide (LeanExperiments.fibonacci candidate % 11 = 0 ↔ candidate % 10 = 0) = true :=
    List.all_eq_true.mp fibonacci_mod_eleven_residueCheck_passes
  exact of_decide_eq_true (hAll residue (List.mem_range.mpr hResidue))

/-- Fibonacci 数が11で割り切れることと、添字が10の倍数であることは同値。 -/
theorem fibonacci_divisible_by_eleven_iff_index_multiple_of_ten (n : Nat) :
    LeanExperiments.fibonacci n % 11 = 0 ↔ n % 10 = 0 := by
  have hPredecessor : LeanExperiments.fibonacci 9 % 11 = 1 := by
    native_decide
  have hAtPeriod : LeanExperiments.fibonacci 10 % 11 = 0 := by
    native_decide
  exact fibonacci_divisible_iff_index_multiple_of_period
    11 10 10 n (by omega) hPredecessor hAtPeriod
    (⟨1, by omega⟩) (by
      intro residue hResidue
      exact fibonacci_mod_eleven_zero_iff_residue_multiple_of_ten residue hResidue)

/-- Fibonacci 数の13を法とする剰余は、添字を28増やしても変わらない。 -/
theorem fibonacci_mod_thirteen_periodic (n : Nat) :
    LeanExperiments.fibonacci (n + 28) % 13 =
      LeanExperiments.fibonacci n % 13 := by
  have hPredecessor : LeanExperiments.fibonacci 27 % 13 = 1 := by
    native_decide
  have hAtPeriod : LeanExperiments.fibonacci 28 % 13 = 0 := by
    native_decide
  exact fibonacci_mod_periodic_of_predecessor_one_and_period_zero
    13 28 n (by omega) hPredecessor hAtPeriod

/-- 添字を28の倍数だけ進めても、Fibonacci 数の13を法とする剰余は保たれる。 -/
theorem fibonacci_mod_thirteen_periodic_mul (n k : Nat) :
    LeanExperiments.fibonacci (n + 28 * k) % 13 =
      LeanExperiments.fibonacci n % 13 := by
  have hPredecessor : LeanExperiments.fibonacci 27 % 13 = 1 := by
    native_decide
  have hAtPeriod : LeanExperiments.fibonacci 28 % 13 = 0 := by
    native_decide
  exact fibonacci_mod_periodic_mul_of_predecessor_one_and_period_zero
    13 28 n k (by omega) hPredecessor hAtPeriod

/-- 28個の剰余代表における、13での割り切り条件を有限確認する。 -/
def fibonacci_mod_thirteen_residueCheck : Bool :=
  (List.range 28).all fun residue =>
    decide (LeanExperiments.fibonacci residue % 13 = 0 ↔ residue % 7 = 0)

/-- 28個全ての剰余代表で、13による割り切り条件が添字の条件と一致する。 -/
theorem fibonacci_mod_thirteen_residueCheck_passes :
    fibonacci_mod_thirteen_residueCheck = true := by
  native_decide

/-- 28個の剰余代表では、Fibonacci 数が13で割り切れるのは添字が7の倍数の場合。 -/
private theorem fibonacci_mod_thirteen_zero_iff_residue_multiple_of_seven
    (residue : Nat) (hResidue : residue < 28) :
    LeanExperiments.fibonacci residue % 13 = 0 ↔ residue % 7 = 0 := by
  have hAll : ∀ candidate ∈ List.range 28,
      decide (LeanExperiments.fibonacci candidate % 13 = 0 ↔ candidate % 7 = 0) = true :=
    List.all_eq_true.mp fibonacci_mod_thirteen_residueCheck_passes
  exact of_decide_eq_true (hAll residue (List.mem_range.mpr hResidue))

/-- Fibonacci 数が13で割り切れることと、添字が7の倍数であることは同値。 -/
theorem fibonacci_divisible_by_thirteen_iff_index_multiple_of_seven (n : Nat) :
    LeanExperiments.fibonacci n % 13 = 0 ↔ n % 7 = 0 := by
  have hPredecessor : LeanExperiments.fibonacci 27 % 13 = 1 := by
    native_decide
  have hAtPeriod : LeanExperiments.fibonacci 28 % 13 = 0 := by
    native_decide
  exact fibonacci_divisible_iff_index_multiple_of_period
    13 28 7 n (by omega) hPredecessor hAtPeriod
    (⟨4, by omega⟩) (by
      intro residue hResidue
      exact fibonacci_mod_thirteen_zero_iff_residue_multiple_of_seven residue hResidue)

/-- Fibonacci 数の17を法とする剰余は、添字を36増やしても変わらない。 -/
theorem fibonacci_mod_seventeen_periodic (n : Nat) :
    LeanExperiments.fibonacci (n + 36) % 17 =
      LeanExperiments.fibonacci n % 17 := by
  have hPredecessor : LeanExperiments.fibonacci 35 % 17 = 1 := by
    native_decide
  have hAtPeriod : LeanExperiments.fibonacci 36 % 17 = 0 := by
    native_decide
  exact fibonacci_mod_periodic_of_predecessor_one_and_period_zero
    17 36 n (by omega) hPredecessor hAtPeriod

/-- 添字を36の倍数だけ進めても、Fibonacci 数の17を法とする剰余は保たれる。 -/
theorem fibonacci_mod_seventeen_periodic_mul (n k : Nat) :
    LeanExperiments.fibonacci (n + 36 * k) % 17 =
      LeanExperiments.fibonacci n % 17 := by
  have hPredecessor : LeanExperiments.fibonacci 35 % 17 = 1 := by
    native_decide
  have hAtPeriod : LeanExperiments.fibonacci 36 % 17 = 0 := by
    native_decide
  exact fibonacci_mod_periodic_mul_of_predecessor_one_and_period_zero
    17 36 n k (by omega) hPredecessor hAtPeriod

/-- 36個の剰余代表における、17での割り切り条件を有限確認する。 -/
def fibonacci_mod_seventeen_residueCheck : Bool :=
  (List.range 36).all fun residue =>
    decide (LeanExperiments.fibonacci residue % 17 = 0 ↔ residue % 9 = 0)

/-- 36個全ての剰余代表で、17による割り切り条件が添字の条件と一致する。 -/
theorem fibonacci_mod_seventeen_residueCheck_passes :
    fibonacci_mod_seventeen_residueCheck = true := by
  native_decide

/-- 36個の剰余代表では、Fibonacci 数が17で割り切れるのは添字が9の倍数の場合。 -/
private theorem fibonacci_mod_seventeen_zero_iff_residue_multiple_of_nine
    (residue : Nat) (hResidue : residue < 36) :
    LeanExperiments.fibonacci residue % 17 = 0 ↔ residue % 9 = 0 := by
  have hAll : ∀ candidate ∈ List.range 36,
      decide (LeanExperiments.fibonacci candidate % 17 = 0 ↔ candidate % 9 = 0) = true :=
    List.all_eq_true.mp fibonacci_mod_seventeen_residueCheck_passes
  exact of_decide_eq_true (hAll residue (List.mem_range.mpr hResidue))

/-- Fibonacci 数が17で割り切れることと、添字が9の倍数であることは同値。 -/
theorem fibonacci_divisible_by_seventeen_iff_index_multiple_of_nine (n : Nat) :
    LeanExperiments.fibonacci n % 17 = 0 ↔ n % 9 = 0 := by
  have hPredecessor : LeanExperiments.fibonacci 35 % 17 = 1 := by
    native_decide
  have hAtPeriod : LeanExperiments.fibonacci 36 % 17 = 0 := by
    native_decide
  exact fibonacci_divisible_iff_index_multiple_of_period
    17 36 9 n (by omega) hPredecessor hAtPeriod
    (⟨4, by omega⟩) (by
      intro residue hResidue
      exact fibonacci_mod_seventeen_zero_iff_residue_multiple_of_nine residue hResidue)

/-- Fibonacci 数の19を法とする剰余は、添字を18増やしても変わらない。 -/
theorem fibonacci_mod_nineteen_periodic (n : Nat) :
    LeanExperiments.fibonacci (n + 18) % 19 =
      LeanExperiments.fibonacci n % 19 := by
  have hPredecessor : LeanExperiments.fibonacci 17 % 19 = 1 := by
    native_decide
  have hAtPeriod : LeanExperiments.fibonacci 18 % 19 = 0 := by
    native_decide
  exact fibonacci_mod_periodic_of_predecessor_one_and_period_zero
    19 18 n (by omega) hPredecessor hAtPeriod

/-- 添字を18の倍数だけ進めても、Fibonacci 数の19を法とする剰余は保たれる。 -/
theorem fibonacci_mod_nineteen_periodic_mul (n k : Nat) :
    LeanExperiments.fibonacci (n + 18 * k) % 19 =
      LeanExperiments.fibonacci n % 19 := by
  have hPredecessor : LeanExperiments.fibonacci 17 % 19 = 1 := by
    native_decide
  have hAtPeriod : LeanExperiments.fibonacci 18 % 19 = 0 := by
    native_decide
  exact fibonacci_mod_periodic_mul_of_predecessor_one_and_period_zero
    19 18 n k (by omega) hPredecessor hAtPeriod

/-- 18個の剰余代表における、19での割り切り条件を有限確認する。 -/
def fibonacci_mod_nineteen_residueCheck : Bool :=
  (List.range 18).all fun residue =>
    decide (LeanExperiments.fibonacci residue % 19 = 0 ↔ residue % 18 = 0)

/-- 18個全ての剰余代表で、19による割り切り条件が添字の条件と一致する。 -/
theorem fibonacci_mod_nineteen_residueCheck_passes :
    fibonacci_mod_nineteen_residueCheck = true := by
  native_decide

/-- 18個の剰余代表では、Fibonacci 数が19で割り切れるのは添字が18の倍数の場合。 -/
private theorem fibonacci_mod_nineteen_zero_iff_residue_multiple_of_eighteen
    (residue : Nat) (hResidue : residue < 18) :
    LeanExperiments.fibonacci residue % 19 = 0 ↔ residue % 18 = 0 := by
  have hAll : ∀ candidate ∈ List.range 18,
      decide (LeanExperiments.fibonacci candidate % 19 = 0 ↔ candidate % 18 = 0) = true :=
    List.all_eq_true.mp fibonacci_mod_nineteen_residueCheck_passes
  exact of_decide_eq_true (hAll residue (List.mem_range.mpr hResidue))

/-- Fibonacci 数が19で割り切れることと、添字が18の倍数であることは同値。 -/
theorem fibonacci_divisible_by_nineteen_iff_index_multiple_of_eighteen (n : Nat) :
    LeanExperiments.fibonacci n % 19 = 0 ↔ n % 18 = 0 := by
  have hPredecessor : LeanExperiments.fibonacci 17 % 19 = 1 := by
    native_decide
  have hAtPeriod : LeanExperiments.fibonacci 18 % 19 = 0 := by
    native_decide
  exact fibonacci_divisible_iff_index_multiple_of_period
    19 18 18 n (by omega) hPredecessor hAtPeriod
    (⟨1, by omega⟩) (by
      intro residue hResidue
      exact fibonacci_mod_nineteen_zero_iff_residue_multiple_of_eighteen residue hResidue)

/-- Fibonacci 数の23を法とする剰余は、添字を48増やしても変わらない。 -/
theorem fibonacci_mod_twentyThree_periodic (n : Nat) :
    LeanExperiments.fibonacci (n + 48) % 23 =
      LeanExperiments.fibonacci n % 23 := by
  have hPredecessor : LeanExperiments.fibonacci 47 % 23 = 1 := by
    native_decide
  have hAtPeriod : LeanExperiments.fibonacci 48 % 23 = 0 := by
    native_decide
  exact fibonacci_mod_periodic_of_predecessor_one_and_period_zero
    23 48 n (by omega) hPredecessor hAtPeriod

/-- 添字を48の倍数だけ進めても、Fibonacci 数の23を法とする剰余は保たれる。 -/
theorem fibonacci_mod_twentyThree_periodic_mul (n k : Nat) :
    LeanExperiments.fibonacci (n + 48 * k) % 23 =
      LeanExperiments.fibonacci n % 23 := by
  have hPredecessor : LeanExperiments.fibonacci 47 % 23 = 1 := by
    native_decide
  have hAtPeriod : LeanExperiments.fibonacci 48 % 23 = 0 := by
    native_decide
  exact fibonacci_mod_periodic_mul_of_predecessor_one_and_period_zero
    23 48 n k (by omega) hPredecessor hAtPeriod

/-- 48個の剰余代表における、23での割り切り条件を有限確認する。 -/
def fibonacci_mod_twentyThree_residueCheck : Bool :=
  (List.range 48).all fun residue =>
    decide (LeanExperiments.fibonacci residue % 23 = 0 ↔ residue % 24 = 0)

/-- 48個全ての剰余代表で、23による割り切り条件が添字の条件と一致する。 -/
theorem fibonacci_mod_twentyThree_residueCheck_passes :
    fibonacci_mod_twentyThree_residueCheck = true := by
  native_decide

/-- 48個の剰余代表では、Fibonacci 数が23で割り切れるのは添字が24の倍数の場合。 -/
private theorem fibonacci_mod_twentyThree_zero_iff_residue_multiple_of_twentyFour
    (residue : Nat) (hResidue : residue < 48) :
    LeanExperiments.fibonacci residue % 23 = 0 ↔ residue % 24 = 0 := by
  have hAll : ∀ candidate ∈ List.range 48,
      decide (LeanExperiments.fibonacci candidate % 23 = 0 ↔ candidate % 24 = 0) = true :=
    List.all_eq_true.mp fibonacci_mod_twentyThree_residueCheck_passes
  exact of_decide_eq_true (hAll residue (List.mem_range.mpr hResidue))

/-- Fibonacci 数が23で割り切れることと、添字が24の倍数であることは同値。 -/
theorem fibonacci_divisible_by_twentyThree_iff_index_multiple_of_twentyFour (n : Nat) :
    LeanExperiments.fibonacci n % 23 = 0 ↔ n % 24 = 0 := by
  have hPredecessor : LeanExperiments.fibonacci 47 % 23 = 1 := by
    native_decide
  have hAtPeriod : LeanExperiments.fibonacci 48 % 23 = 0 := by
    native_decide
  exact fibonacci_divisible_iff_index_multiple_of_period
    23 48 24 n (by omega) hPredecessor hAtPeriod
    (⟨2, by omega⟩) (by
      intro residue hResidue
      exact fibonacci_mod_twentyThree_zero_iff_residue_multiple_of_twentyFour residue hResidue)

/-- Fibonacci 数の29を法とする剰余は、添字を14増やしても変わらない。 -/
theorem fibonacci_mod_twentyNine_periodic (n : Nat) :
    LeanExperiments.fibonacci (n + 14) % 29 =
      LeanExperiments.fibonacci n % 29 := by
  have hPredecessor : LeanExperiments.fibonacci 13 % 29 = 1 := by
    native_decide
  have hAtPeriod : LeanExperiments.fibonacci 14 % 29 = 0 := by
    native_decide
  exact fibonacci_mod_periodic_of_predecessor_one_and_period_zero
    29 14 n (by omega) hPredecessor hAtPeriod

/-- 添字を14の倍数だけ進めても、Fibonacci 数の29を法とする剰余は保たれる。 -/
theorem fibonacci_mod_twentyNine_periodic_mul (n k : Nat) :
    LeanExperiments.fibonacci (n + 14 * k) % 29 =
      LeanExperiments.fibonacci n % 29 := by
  have hPredecessor : LeanExperiments.fibonacci 13 % 29 = 1 := by
    native_decide
  have hAtPeriod : LeanExperiments.fibonacci 14 % 29 = 0 := by
    native_decide
  exact fibonacci_mod_periodic_mul_of_predecessor_one_and_period_zero
    29 14 n k (by omega) hPredecessor hAtPeriod

/-- 14個の剰余代表における、29での割り切り条件を有限確認する。 -/
def fibonacci_mod_twentyNine_residueCheck : Bool :=
  (List.range 14).all fun residue =>
    decide (LeanExperiments.fibonacci residue % 29 = 0 ↔ residue % 14 = 0)

/-- 14個全ての剰余代表で、29による割り切り条件が添字の条件と一致する。 -/
theorem fibonacci_mod_twentyNine_residueCheck_passes :
    fibonacci_mod_twentyNine_residueCheck = true := by
  native_decide

/-- 14個の剰余代表では、Fibonacci 数が29で割り切れるのは添字が14の倍数の場合。 -/
private theorem fibonacci_mod_twentyNine_zero_iff_residue_multiple_of_fourteen
    (residue : Nat) (hResidue : residue < 14) :
    LeanExperiments.fibonacci residue % 29 = 0 ↔ residue % 14 = 0 := by
  have hAll : ∀ candidate ∈ List.range 14,
      decide (LeanExperiments.fibonacci candidate % 29 = 0 ↔ candidate % 14 = 0) = true :=
    List.all_eq_true.mp fibonacci_mod_twentyNine_residueCheck_passes
  exact of_decide_eq_true (hAll residue (List.mem_range.mpr hResidue))

/-- Fibonacci 数が29で割り切れることと、添字が14の倍数であることは同値。 -/
theorem fibonacci_divisible_by_twentyNine_iff_index_multiple_of_fourteen (n : Nat) :
    LeanExperiments.fibonacci n % 29 = 0 ↔ n % 14 = 0 := by
  have hPredecessor : LeanExperiments.fibonacci 13 % 29 = 1 := by
    native_decide
  have hAtPeriod : LeanExperiments.fibonacci 14 % 29 = 0 := by
    native_decide
  exact fibonacci_divisible_iff_index_multiple_of_period
    29 14 14 n (by omega) hPredecessor hAtPeriod
    (⟨1, by omega⟩) (by
      intro residue hResidue
      exact fibonacci_mod_twentyNine_zero_iff_residue_multiple_of_fourteen residue hResidue)

/-- Fibonacci 数の31を法とする剰余は、添字を30増やしても変わらない。 -/
theorem fibonacci_mod_thirtyOne_periodic (n : Nat) :
    LeanExperiments.fibonacci (n + 30) % 31 =
      LeanExperiments.fibonacci n % 31 := by
  have hPredecessor : LeanExperiments.fibonacci 29 % 31 = 1 := by
    native_decide
  have hAtPeriod : LeanExperiments.fibonacci 30 % 31 = 0 := by
    native_decide
  exact fibonacci_mod_periodic_of_predecessor_one_and_period_zero
    31 30 n (by omega) hPredecessor hAtPeriod

/-- 添字を30の倍数だけ進めても、Fibonacci 数の31を法とする剰余は保たれる。 -/
theorem fibonacci_mod_thirtyOne_periodic_mul (n k : Nat) :
    LeanExperiments.fibonacci (n + 30 * k) % 31 =
      LeanExperiments.fibonacci n % 31 := by
  have hPredecessor : LeanExperiments.fibonacci 29 % 31 = 1 := by
    native_decide
  have hAtPeriod : LeanExperiments.fibonacci 30 % 31 = 0 := by
    native_decide
  exact fibonacci_mod_periodic_mul_of_predecessor_one_and_period_zero
    31 30 n k (by omega) hPredecessor hAtPeriod

/-- 30個の剰余代表における、31での割り切り条件を有限確認する。 -/
def fibonacci_mod_thirtyOne_residueCheck : Bool :=
  (List.range 30).all fun residue =>
    decide (LeanExperiments.fibonacci residue % 31 = 0 ↔ residue % 30 = 0)

/-- 30個全ての剰余代表で、31による割り切り条件が添字の条件と一致する。 -/
theorem fibonacci_mod_thirtyOne_residueCheck_passes :
    fibonacci_mod_thirtyOne_residueCheck = true := by
  native_decide

/-- 30個の剰余代表では、Fibonacci 数が31で割り切れるのは添字が30の倍数の場合。 -/
private theorem fibonacci_mod_thirtyOne_zero_iff_residue_multiple_of_thirty
    (residue : Nat) (hResidue : residue < 30) :
    LeanExperiments.fibonacci residue % 31 = 0 ↔ residue % 30 = 0 := by
  have hAll : ∀ candidate ∈ List.range 30,
      decide (LeanExperiments.fibonacci candidate % 31 = 0 ↔ candidate % 30 = 0) = true :=
    List.all_eq_true.mp fibonacci_mod_thirtyOne_residueCheck_passes
  exact of_decide_eq_true (hAll residue (List.mem_range.mpr hResidue))

/-- Fibonacci 数が31で割り切れることと、添字が30の倍数であることは同値。 -/
theorem fibonacci_divisible_by_thirtyOne_iff_index_multiple_of_thirty (n : Nat) :
    LeanExperiments.fibonacci n % 31 = 0 ↔ n % 30 = 0 := by
  have hPredecessor : LeanExperiments.fibonacci 29 % 31 = 1 := by
    native_decide
  have hAtPeriod : LeanExperiments.fibonacci 30 % 31 = 0 := by
    native_decide
  exact fibonacci_divisible_iff_index_multiple_of_period
    31 30 30 n (by omega) hPredecessor hAtPeriod
    (⟨1, by omega⟩) (by
      intro residue hResidue
      exact fibonacci_mod_thirtyOne_zero_iff_residue_multiple_of_thirty residue hResidue)

/-- Fibonacci 数の37を法とする剰余は、添字を76増やしても変わらない。 -/
theorem fibonacci_mod_thirtySeven_periodic (n : Nat) :
    LeanExperiments.fibonacci (n + 76) % 37 =
      LeanExperiments.fibonacci n % 37 := by
  have hPredecessor : LeanExperiments.fibonacci 75 % 37 = 1 := by
    native_decide
  have hAtPeriod : LeanExperiments.fibonacci 76 % 37 = 0 := by
    native_decide
  exact fibonacci_mod_periodic_of_predecessor_one_and_period_zero
    37 76 n (by omega) hPredecessor hAtPeriod

/-- 添字を76の倍数だけ進めても、Fibonacci 数の37を法とする剰余は保たれる。 -/
theorem fibonacci_mod_thirtySeven_periodic_mul (n k : Nat) :
    LeanExperiments.fibonacci (n + 76 * k) % 37 =
      LeanExperiments.fibonacci n % 37 := by
  have hPredecessor : LeanExperiments.fibonacci 75 % 37 = 1 := by
    native_decide
  have hAtPeriod : LeanExperiments.fibonacci 76 % 37 = 0 := by
    native_decide
  exact fibonacci_mod_periodic_mul_of_predecessor_one_and_period_zero
    37 76 n k (by omega) hPredecessor hAtPeriod

/-- 76個の剰余代表における、37での割り切り条件を有限確認する。 -/
def fibonacci_mod_thirtySeven_residueCheck : Bool :=
  (List.range 76).all fun residue =>
    decide (LeanExperiments.fibonacci residue % 37 = 0 ↔ residue % 19 = 0)

/-- 76個全ての剰余代表で、37による割り切り条件が添字の条件と一致する。 -/
theorem fibonacci_mod_thirtySeven_residueCheck_passes :
    fibonacci_mod_thirtySeven_residueCheck = true := by
  native_decide

/-- 76個の剰余代表では、Fibonacci 数が37で割り切れるのは添字が19の倍数の場合。 -/
private theorem fibonacci_mod_thirtySeven_zero_iff_residue_multiple_of_nineteen
    (residue : Nat) (hResidue : residue < 76) :
    LeanExperiments.fibonacci residue % 37 = 0 ↔ residue % 19 = 0 := by
  have hAll : ∀ candidate ∈ List.range 76,
      decide (LeanExperiments.fibonacci candidate % 37 = 0 ↔ candidate % 19 = 0) = true :=
    List.all_eq_true.mp fibonacci_mod_thirtySeven_residueCheck_passes
  exact of_decide_eq_true (hAll residue (List.mem_range.mpr hResidue))

/-- Fibonacci 数が37で割り切れることと、添字が19の倍数であることは同値。 -/
theorem fibonacci_divisible_by_thirtySeven_iff_index_multiple_of_nineteen (n : Nat) :
    LeanExperiments.fibonacci n % 37 = 0 ↔ n % 19 = 0 := by
  have hPredecessor : LeanExperiments.fibonacci 75 % 37 = 1 := by
    native_decide
  have hAtPeriod : LeanExperiments.fibonacci 76 % 37 = 0 := by
    native_decide
  exact fibonacci_divisible_iff_index_multiple_of_period
    37 76 19 n (by omega) hPredecessor hAtPeriod
    (⟨4, by omega⟩) (by
      intro residue hResidue
      exact fibonacci_mod_thirtySeven_zero_iff_residue_multiple_of_nineteen residue hResidue)

/-- Fibonacci 数の41を法とする剰余は、添字を40増やしても変わらない。 -/
theorem fibonacci_mod_fortyOne_periodic (n : Nat) :
    LeanExperiments.fibonacci (n + 40) % 41 =
      LeanExperiments.fibonacci n % 41 := by
  have hPredecessor : LeanExperiments.fibonacci 39 % 41 = 1 := by
    native_decide
  have hAtPeriod : LeanExperiments.fibonacci 40 % 41 = 0 := by
    native_decide
  exact fibonacci_mod_periodic_of_predecessor_one_and_period_zero
    41 40 n (by omega) hPredecessor hAtPeriod

/-- 添字を40の倍数だけ進めても、Fibonacci 数の41を法とする剰余は保たれる。 -/
theorem fibonacci_mod_fortyOne_periodic_mul (n k : Nat) :
    LeanExperiments.fibonacci (n + 40 * k) % 41 =
      LeanExperiments.fibonacci n % 41 := by
  have hPredecessor : LeanExperiments.fibonacci 39 % 41 = 1 := by
    native_decide
  have hAtPeriod : LeanExperiments.fibonacci 40 % 41 = 0 := by
    native_decide
  exact fibonacci_mod_periodic_mul_of_predecessor_one_and_period_zero
    41 40 n k (by omega) hPredecessor hAtPeriod

/-- 40個の剰余代表における、41での割り切り条件を有限確認する。 -/
def fibonacci_mod_fortyOne_residueCheck : Bool :=
  (List.range 40).all fun residue =>
    decide (LeanExperiments.fibonacci residue % 41 = 0 ↔ residue % 20 = 0)

/-- 40個全ての剰余代表で、41による割り切り条件が添字の条件と一致する。 -/
theorem fibonacci_mod_fortyOne_residueCheck_passes :
    fibonacci_mod_fortyOne_residueCheck = true := by
  native_decide

/-- 40個の剰余代表では、Fibonacci 数が41で割り切れるのは添字が20の倍数の場合。 -/
private theorem fibonacci_mod_fortyOne_zero_iff_residue_multiple_of_twenty
    (residue : Nat) (hResidue : residue < 40) :
    LeanExperiments.fibonacci residue % 41 = 0 ↔ residue % 20 = 0 := by
  have hAll : ∀ candidate ∈ List.range 40,
      decide (LeanExperiments.fibonacci candidate % 41 = 0 ↔ candidate % 20 = 0) = true :=
    List.all_eq_true.mp fibonacci_mod_fortyOne_residueCheck_passes
  exact of_decide_eq_true (hAll residue (List.mem_range.mpr hResidue))

/-- Fibonacci 数が41で割り切れることと、添字が20の倍数であることは同値。 -/
theorem fibonacci_divisible_by_fortyOne_iff_index_multiple_of_twenty (n : Nat) :
    LeanExperiments.fibonacci n % 41 = 0 ↔ n % 20 = 0 := by
  have hPredecessor : LeanExperiments.fibonacci 39 % 41 = 1 := by
    native_decide
  have hAtPeriod : LeanExperiments.fibonacci 40 % 41 = 0 := by
    native_decide
  exact fibonacci_divisible_iff_index_multiple_of_period
    41 40 20 n (by omega) hPredecessor hAtPeriod
    (⟨2, by omega⟩) (by
      intro residue hResidue
      exact fibonacci_mod_fortyOne_zero_iff_residue_multiple_of_twenty residue hResidue)

/-- Fibonacci 数の47を法とする剰余は、添字を32増やしても変わらない。 -/
theorem fibonacci_mod_fortySeven_periodic (n : Nat) :
    LeanExperiments.fibonacci (n + 32) % 47 =
      LeanExperiments.fibonacci n % 47 := by
  have hPredecessor : LeanExperiments.fibonacci 31 % 47 = 1 := by
    native_decide
  have hAtPeriod : LeanExperiments.fibonacci 32 % 47 = 0 := by
    native_decide
  exact fibonacci_mod_periodic_of_predecessor_one_and_period_zero
    47 32 n (by omega) hPredecessor hAtPeriod

/-- 添字を32の倍数だけ進めても、Fibonacci 数の47を法とする剰余は保たれる。 -/
theorem fibonacci_mod_fortySeven_periodic_mul (n k : Nat) :
    LeanExperiments.fibonacci (n + 32 * k) % 47 =
      LeanExperiments.fibonacci n % 47 := by
  have hPredecessor : LeanExperiments.fibonacci 31 % 47 = 1 := by
    native_decide
  have hAtPeriod : LeanExperiments.fibonacci 32 % 47 = 0 := by
    native_decide
  exact fibonacci_mod_periodic_mul_of_predecessor_one_and_period_zero
    47 32 n k (by omega) hPredecessor hAtPeriod

/-- 32個の剰余代表における、47での割り切り条件を有限確認する。 -/
def fibonacci_mod_fortySeven_residueCheck : Bool :=
  (List.range 32).all fun residue =>
    decide (LeanExperiments.fibonacci residue % 47 = 0 ↔ residue % 16 = 0)

/-- 32個全ての剰余代表で、47による割り切り条件が添字の条件と一致する。 -/
theorem fibonacci_mod_fortySeven_residueCheck_passes :
    fibonacci_mod_fortySeven_residueCheck = true := by
  native_decide

/-- 32個の剰余代表では、Fibonacci 数が47で割り切れるのは添字が16の倍数の場合。 -/
private theorem fibonacci_mod_fortySeven_zero_iff_residue_multiple_of_sixteen
    (residue : Nat) (hResidue : residue < 32) :
    LeanExperiments.fibonacci residue % 47 = 0 ↔ residue % 16 = 0 := by
  have hAll : ∀ candidate ∈ List.range 32,
      decide (LeanExperiments.fibonacci candidate % 47 = 0 ↔ candidate % 16 = 0) = true :=
    List.all_eq_true.mp fibonacci_mod_fortySeven_residueCheck_passes
  exact of_decide_eq_true (hAll residue (List.mem_range.mpr hResidue))

/-- Fibonacci 数が47で割り切れることと、添字が16の倍数であることは同値。 -/
theorem fibonacci_divisible_by_fortySeven_iff_index_multiple_of_sixteen (n : Nat) :
    LeanExperiments.fibonacci n % 47 = 0 ↔ n % 16 = 0 := by
  have hPredecessor : LeanExperiments.fibonacci 31 % 47 = 1 := by
    native_decide
  have hAtPeriod : LeanExperiments.fibonacci 32 % 47 = 0 := by
    native_decide
  exact fibonacci_divisible_iff_index_multiple_of_period
    47 32 16 n (by omega) hPredecessor hAtPeriod
    (⟨2, by omega⟩) (by
      intro residue hResidue
      exact fibonacci_mod_fortySeven_zero_iff_residue_multiple_of_sixteen residue hResidue)

/-- 小さな再帰範囲を越えた `F 10 = 55` を確認する。 -/
theorem fibonacci_ten_example : LeanExperiments.fibonacci 10 = 55 := by
  native_decide

/-- 高速倍加法で計算した `F 100` の正確な値を確認する。 -/
theorem fibonacci_hundred_example :
    LeanExperiments.fibonacci 100 = 354224848179261915075 := by
  native_decide

/-- 1000番目の Fibonacci 数も、大きな自然数として正確に計算される。 -/
theorem fibonacci_thousand_example :
    LeanExperiments.fibonacci 1000 =
      43466557686937456435688527675040625802564660517371780402481729089536555417949051890403879840079255169295922593080322634775209689623239873322471161642996440906533187938298969649928516003704476137795166849228875 := by
  native_decide

end LeanExperiments.Verification.Fibonacci
