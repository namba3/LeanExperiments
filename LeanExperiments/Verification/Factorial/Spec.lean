module

public import LeanExperiments.Factorial
public import Mathlib.Data.Nat.Factorial.BigOperators

@[expose] public section

/-!
# 階乗の仕様と正当性

実装側の末尾再帰関数を、単純な数学的再帰で定義した階乗と比較する。
蓄積値を使うループが仕様と一致することを示し、その結果から
`factorial` 全体の正しさを導く。
-/

namespace LeanExperiments.Verification.Factorial

/-- 数学的な定義に沿った階乗。証明で実装の意味を表す基準として使う。 -/
def factorialSpec : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorialSpec n

/-- 末尾再帰ループは、これまでの積と残りの階乗の積を返す。

`result` はすでに処理した因子の積、`n` はまだ掛けていない因子の数である。
帰納法では `result` を任意の値として扱う必要があるため、`generalizing acc`
を使っている。
-/
theorem factorialLoop_correct (n acc : Nat) :
    LeanExperiments.factorialLoop n acc = acc * factorialSpec n := by
  induction n generalizing acc with
  | zero =>
      simp [LeanExperiments.factorialLoop, factorialSpec]
  | succ n ih =>
      simp [LeanExperiments.factorialLoop, factorialSpec, ih, Nat.mul_assoc]

/-- 実用関数 `factorial` は数学的仕様 `factorialSpec` と一致する。 -/
theorem factorial_correct (n : Nat) :
    LeanExperiments.factorial n = factorialSpec n := by
  simp [LeanExperiments.factorial, factorialLoop_correct]

/-- 再帰仕様は Mathlib の標準的な階乗関数と一致する。

両者は同じ基底値と後者の漸化式を満たすため、添字に関する帰納法で一致する。
-/
theorem factorialSpec_eq_natFactorial (n : Nat) : factorialSpec n = n.factorial := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [factorialSpec, Nat.factorial_succ, ih]

/-- 実装関数は Mathlib の標準階乗と任意の入力で一致する。 -/
theorem factorial_eq_natFactorial (n : Nat) :
    LeanExperiments.factorial n = n.factorial := by
  rw [factorial_correct, factorialSpec_eq_natFactorial]

/-- 末尾再帰実装は、Mathlib の二分分割階乗実装とも全入力で一致する。

Mathlib の標準階乗を経由して比較するため、実装同士の有限個の値の照合には依存しない。
-/
theorem factorial_eq_binarySplitting (n : Nat) :
    LeanExperiments.factorial n = Nat.factorialBinarySplitting n := by
  rw [factorial_eq_natFactorial]
  exact congrFun Nat.factorial_eq_factorialBinarySplitting n

/-- 任意の有限添字集合について、各引数の階乗の積は引数の合計の階乗を割り切る。

これは多項係数が自然数になることを支える整除性であり、個々の実装値を列挙せず、
末尾再帰実装の一般正当性と Mathlib の有限積定理から導く。
-/
theorem factorial_product_dvd_factorial_sum {α : Type} (indices : Finset α)
    (argument : α → Nat) :
    (∏ index ∈ indices, LeanExperiments.factorial (argument index)) ∣
      LeanExperiments.factorial (∑ index ∈ indices, argument index) := by
  simpa only [factorial_eq_natFactorial] using
    Nat.prod_factorial_dvd_factorial_sum indices argument

/-- 階乗の加法は、前半の階乗と後半の上昇階乗の積に分解できる。

`m+n` 個の積を、最初の `m` 個と続く `n` 個へ分割する一般恒等式である。
末尾再帰実装の結果にも成立し、階乗の分割・合成に利用できる。
-/
theorem factorial_add_eq_factorial_mul_ascFactorial (m n : Nat) :
    LeanExperiments.factorial (m + n) =
      LeanExperiments.factorial m * Nat.ascFactorial (m + 1) n := by
  rw [factorial_eq_natFactorial, factorial_eq_natFactorial]
  exact (Nat.factorial_mul_ascFactorial m n).symm

/-- 仕様に従って、階乗の次項は直前の階乗に `n+1` を掛けた値になる。 -/
theorem factorialSpec_succ (n : Nat) :
    factorialSpec (n + 1) = (n + 1) * factorialSpec n := by
  rfl

/-- 階乗の次項は、実装関数上でも `factorial (n+1) = (n+1) * factorial n` を満たす。 -/
theorem factorial_succ (n : Nat) :
    LeanExperiments.factorial (n + 1) = (n + 1) * LeanExperiments.factorial n := by
  rw [factorial_correct, factorial_correct, factorialSpec_succ]

/-- すべての自然数の階乗は正である。 -/
theorem factorialSpec_positive (n : Nat) : 0 < factorialSpec n := by
  induction n with
  | zero => simp [factorialSpec]
  | succ n ih =>
      rw [factorialSpec]
      exact Nat.mul_pos (by omega) ih

/-- `(n+1)!` は常に `2^n` 以上である。

階乗の各新しい因子が2以上であることを使い、仕様の漸化式に関する帰納法で示す。
-/
theorem factorialSpec_pow_two_lower_bound (n : Nat) :
    2 ^ n ≤ factorialSpec (n + 1) := by
  induction n with
  | zero => simp [factorialSpec]
  | succ n ih =>
      change 2 ^ (n + 1) ≤ factorialSpec (n + 2)
      rw [factorialSpec_succ]
      have hFactor : 2 ≤ n + 2 := by omega
      have hProduct : 2 ^ n * 2 ≤ factorialSpec (n + 1) * (n + 2) :=
        Nat.mul_le_mul ih hFactor
      calc
        2 ^ (n + 1) = 2 ^ n * 2 := by rw [Nat.pow_succ]
        _ ≤ factorialSpec (n + 1) * (n + 2) := hProduct
        _ = (n + 2) * factorialSpec (n + 1) := Nat.mul_comm _ _
        _ = factorialSpec (n + 2) := (factorialSpec_succ (n + 1)).symm

/-- 底が大きくなると、同じ自然数指数の累乗も大きくなる。 -/
private theorem pow_mono_base {small large exponent : Nat}
    (hBase : small ≤ large) : small ^ exponent ≤ large ^ exponent := by
  induction exponent with
  | zero => simp
  | succ exponent ih =>
      rw [Nat.pow_succ, Nat.pow_succ]
      exact Nat.mul_le_mul ih hBase

/-- `n!` は `n^n` 以下である。`n=0` では `0^0=1` とする。 -/
theorem factorialSpec_upper_bound (n : Nat) :
    factorialSpec n ≤ n ^ n := by
  induction n with
  | zero => simp [factorialSpec]
  | succ n ih =>
      rw [factorialSpec_succ]
      have hBase : n ≤ n + 1 := by omega
      have hPower := pow_mono_base (exponent := n) hBase
      calc
        (n + 1) * factorialSpec n ≤ (n + 1) * (n + 1) ^ n :=
          Nat.mul_le_mul_left (n + 1) (Nat.le_trans ih hPower)
        _ = (n + 1) ^ (n + 1) := by rw [Nat.pow_succ]; ac_rfl

/-- 実装関数も任意の自然数で `n! ≤ n^n` を満たす。 -/
theorem factorial_upper_bound (n : Nat) :
    LeanExperiments.factorial n ≤ n ^ n := by
  rw [factorial_correct]
  exact factorialSpec_upper_bound n

/-- 実装関数も任意の `n` で `2^n ≤ (n+1)!` を満たす。 -/
theorem factorial_pow_two_lower_bound (n : Nat) :
    2 ^ n ≤ LeanExperiments.factorial (n + 1) := by
  rw [factorial_correct]
  exact factorialSpec_pow_two_lower_bound n

/-- 実装関数が返す階乗も、入力にかかわらず正である。 -/
theorem factorial_positive (n : Nat) : 0 < LeanExperiments.factorial n := by
  rw [factorial_correct]
  exact factorialSpec_positive n

/-- 添字が1以上なら、階乗は次の添字で厳密に大きくなる。

`n+1 > 1` と階乗の正値性を使い、漸化式の両辺で正の階乗を掛ける。
`n = 0` では `0! = 1!` なので、この補題には `0 < n` が必要である。
-/
theorem factorialSpec_succ_strict (n : Nat) (hn : 0 < n) :
    factorialSpec n < factorialSpec (n + 1) := by
  rw [factorialSpec_succ]
  have hFactor : 1 < n + 1 := by omega
  have hPositive := factorialSpec_positive n
  have hProduct := Nat.mul_lt_mul_of_pos_right hFactor hPositive
  simpa using hProduct

/-- `1 ≤ m < n` なら `m! < n!`。

添字が `n` と等しい場合は直後の項との厳密な増加を使い、それ以外は帰納法で
途中の階乗まで進んでから最後の一段の厳密な増加を適用する。
-/
theorem factorialSpec_strict_mono_of_pos {m n : Nat}
    (hm : 0 < m) (hmn : m < n) : factorialSpec m < factorialSpec n := by
  induction n generalizing m with
  | zero => omega
  | succ n ih =>
      by_cases hEq : m = n
      · subst m
        exact factorialSpec_succ_strict n hm
      · have hmn' : m < n := by omega
        exact Nat.lt_trans (ih hm hmn') (factorialSpec_succ_strict n (by omega))

/-- 階乗は自然数の添字について単調非減少である。

最初の二項 `0!` と `1!` は等しく、それ以降は前補題の狭義単調性が成り立つ。
-/
theorem factorialSpec_mono {m n : Nat} (hmn : m ≤ n) :
    factorialSpec m ≤ factorialSpec n := by
  induction n with
  | zero =>
      have hm : m = 0 := by omega
      subst m
      exact Nat.le_refl _
  | succ n ih =>
      by_cases hEq : m = n + 1
      · subst m
        exact Nat.le_refl _
      · have hmn' : m ≤ n := by omega
        have hStep : factorialSpec n ≤ factorialSpec (n + 1) := by
          by_cases hn : n = 0
          · subst n
            simp [factorialSpec]
          · exact Nat.le_of_lt (factorialSpec_succ_strict n (by omega))
        exact Nat.le_trans (ih hmn') hStep

/-- 実装が返す階乗も添字について単調非減少である。 -/
theorem factorial_mono {m n : Nat} (hmn : m ≤ n) :
    LeanExperiments.factorial m ≤ LeanExperiments.factorial n := by
  rw [factorial_correct m, factorial_correct n]
  exact factorialSpec_mono hmn

/-- 実装が返す階乗は、正の添字の範囲では狭義単調に増加する。 -/
theorem factorial_strict_mono_of_pos {m n : Nat}
    (hm : 0 < m) (hmn : m < n) :
    LeanExperiments.factorial m < LeanExperiments.factorial n := by
  rw [factorial_correct m, factorial_correct n]
  exact factorialSpec_strict_mono_of_pos hm hmn

/-- `1 ≤ k ≤ n` を満たす任意の `k` は `n!` を割り切る。

`n+1` が `k` 自身なら新しい因子から直ちに従う。それ以外は `k ≤ n` なので
帰納法の仮定を使い、階乗の漸化式で新たに掛ける因子を商へまとめる。
-/
theorem factorialSpec_dvd_of_le (n k : Nat) (hk : 0 < k) (hkn : k ≤ n) :
    k ∣ factorialSpec n := by
  induction n with
  | zero => omega
  | succ n ih =>
      rw [factorialSpec]
      by_cases hEq : k = n + 1
      · subst k
        exact ⟨factorialSpec n, rfl⟩
      · have hkn' : k ≤ n := by omega
        obtain ⟨quotient, hQuotient⟩ := ih hkn'
        refine ⟨(n + 1) * quotient, ?_⟩
        calc
          (n + 1) * factorialSpec n = (n + 1) * (k * quotient) := by rw [hQuotient]
          _ = k * ((n + 1) * quotient) := by ac_rfl

/-- 実装が返す階乗も、`1 ≤ k ≤ n` なら `k` で割り切れる。 -/
theorem factorial_dvd_of_le (n k : Nat) (hk : 0 < k) (hkn : k ≤ n) :
    k ∣ LeanExperiments.factorial n := by
  rw [factorial_correct]
  exact factorialSpec_dvd_of_le n k hk hkn

/-- 階乗が2で割り切れるのは、入力が2以上の場合に限る。 -/
theorem factorial_even_iff_two_le (n : Nat) :
    2 ∣ LeanExperiments.factorial n ↔ 2 ≤ n := by
  constructor
  · intro hDiv
    by_cases hTwoLe : 2 ≤ n
    · exact hTwoLe
    · have hSmall : n < 2 := by omega
      cases n with
      | zero =>
          simp [LeanExperiments.factorial, LeanExperiments.factorialLoop] at hDiv
      | succ n =>
          cases n with
          | zero =>
              simp [LeanExperiments.factorial, LeanExperiments.factorialLoop] at hDiv
          | succ n => omega
  · intro hTwoLe
    exact factorial_dvd_of_le n 2 (by omega) hTwoLe

/-- 階乗を2で割った余りが1になるのは、入力が0または1の場合に限る。 -/
theorem factorial_mod_two_eq_one_iff_le_one (n : Nat) :
    LeanExperiments.factorial n % 2 = 1 ↔ n ≤ 1 := by
  constructor
  · intro hOdd
    have hCases : n ≤ 1 ∨ 2 ≤ n := by omega
    rcases hCases with hSmall | hTwoLe
    · exact hSmall
    · have hEven : 2 ∣ LeanExperiments.factorial n :=
        factorial_even_iff_two_le n |>.mpr hTwoLe
      have hModZero := (Nat.dvd_iff_mod_eq_zero).mp hEven
      rw [hModZero] at hOdd
      omega
  · intro hSmall
    have hCases : n = 0 ∨ n = 1 := by omega
    rcases hCases with hZero | hOne
    · subst n
      simp [LeanExperiments.factorial, LeanExperiments.factorialLoop]
    · subst n
      simp [LeanExperiments.factorial, LeanExperiments.factorialLoop]

/-- 添字が小さい階乗は、添字が大きい階乗を割り切る。

`n+1` の場合は階乗の漸化式で新しい因子を商へ掛ければよく、帰納法で
`m! ∣ n!` なら `(n+1)!` にも同じ関係が保たれる。
-/
theorem factorialSpec_dvd_of_le_index {m n : Nat} (hmn : m ≤ n) :
    factorialSpec m ∣ factorialSpec n := by
  induction n with
  | zero =>
      have hm : m = 0 := by omega
      subst m
      exact Nat.dvd_refl _
  | succ n ih =>
      by_cases hEq : m = n + 1
      · subst m
        exact Nat.dvd_refl _
      · have hmn' : m ≤ n := by omega
        obtain ⟨quotient, hQuotient⟩ := ih hmn'
        refine ⟨(n + 1) * quotient, ?_⟩
        rw [factorialSpec, hQuotient]
        ac_rfl

/-- 実装が返す階乗も、添字が小さい階乗で割り切れる。 -/
theorem factorial_dvd_of_le_index {m n : Nat} (hmn : m ≤ n) :
    LeanExperiments.factorial m ∣ LeanExperiments.factorial n := by
  rw [factorial_correct m, factorial_correct n]
  exact factorialSpec_dvd_of_le_index hmn

/-- 二つの階乗の整除関係は、添字順か `1! ∣ 0!` の例外に限られる。 -/
theorem factorial_dvd_iff_index_le_or_base_exception (m n : Nat) :
    LeanExperiments.factorial m ∣ LeanExperiments.factorial n ↔
      m ≤ n ∨ (m = 1 ∧ n = 0) := by
  constructor
  · intro hDivides
    have hValue : LeanExperiments.factorial m ≤ LeanExperiments.factorial n :=
      Nat.le_of_dvd (factorial_positive n) hDivides
    by_cases hIndex : m ≤ n
    · exact Or.inl hIndex
    · have hReverse : n < m := by omega
      by_cases hZero : n = 0
      · subst n
        by_cases hOne : m = 1
        · exact Or.inr ⟨hOne, rfl⟩
        · have hAtLeastTwo : 2 ≤ m := by omega
          have hEven := (factorial_even_iff_two_le m).mpr hAtLeastTwo
          have hFactorialAtLeastTwo : 2 ≤ LeanExperiments.factorial m :=
            Nat.le_of_dvd (factorial_positive m) hEven
          simp only [LeanExperiments.factorial, factorialLoop] at hValue hFactorialAtLeastTwo
          exact False.elim (by omega)
      · have hStrict := factorial_strict_mono_of_pos (by omega) hReverse
        exact False.elim (by omega)
  · rintro (hIndex | ⟨rfl, rfl⟩)
    · exact factorial_dvd_of_le_index hIndex
    · simp [LeanExperiments.factorial, LeanExperiments.factorialLoop]

end LeanExperiments.Verification.Factorial
