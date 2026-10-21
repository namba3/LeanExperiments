module

public import LeanExperiments.PrimeFactors
public meta import LeanExperiments.PrimeFactors
public import Std.WP
public import Mathlib.Data.Nat.Factors
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.Nat.Factorization.Root
public import Mathlib.Data.List.Sort
public import Mathlib.Data.Nat.Squarefree
public meta import Mathlib.Algebra.Group.Nat.Defs

@[expose] public section

/-!
# 素因数分解の計算例

試し割りの境界と因数の並び方を、代表値についてカーネル内で確認する。
0 と 1、素数、重複する因子を持つ合成数、複数種類の因子を持つ数を含める。
これらは有限個の具体例であり、任意の自然数に対する素因数分解の一般定理ではない。
-/

namespace LeanExperiments.Verification.PrimeFactors

open Std.WP

set_option experimental.vcgen true

/-- 因子候補 `n` が素数であることを、`n` 未満の約数候補で表す。

`List.range n` は `0` から `n-1` までを列挙するため、2 未満の候補を除き、
それ以外で `n` を割り切るものがないことを要求すれば素数の仕様になる。
-/
def isPrimeCheck (n : Nat) : Bool :=
  decide (2 ≤ n) && (List.range n).all (fun divisor =>
    decide (divisor < 2 ∨ n % divisor ≠ 0))

/-- 約数候補の有限確認が成功することを、このファイルで使う素数性とする。 -/
def IsPrime (n : Nat) : Prop := isPrimeCheck n = true

/-- 有限の判定器は、全ての真の約数候補を排除する素数条件と同値である。

`divisor < n` から `List.range n` への所属を得るため、判定器が調べる範囲に
抜けがないこともこの同値性に含まれる。
-/
theorem isPrime_iff_no_proper_divisor (n : Nat) :
    IsPrime n ↔
      2 ≤ n ∧ ∀ divisor, 2 ≤ divisor → divisor < n → n % divisor ≠ 0 := by
  unfold IsPrime isPrimeCheck
  simp only [Bool.and_eq_true]
  constructor
  · rintro ⟨hLower, hDivisors⟩
    refine ⟨of_decide_eq_true hLower, ?_⟩
    intro divisor hDivisorLower hDivisorUpper
    have hCheck := (List.all_eq_true.mp hDivisors) divisor
      (List.mem_range.mpr hDivisorUpper)
    rcases of_decide_eq_true hCheck with hSmall | hNotDivisor
    · omega
    · exact hNotDivisor
  · rintro ⟨hLower, hNoDivisor⟩
    refine ⟨decide_eq_true hLower, ?_⟩
    apply List.all_eq_true.mpr
    intro divisor hMember
    have hUpper := List.mem_range.mp hMember
    by_cases hSmall : divisor < 2
    · exact decide_eq_true (Or.inl hSmall)
    · have hDivisorLower : 2 ≤ divisor := by omega
      exact decide_eq_true (Or.inr (hNoDivisor divisor hDivisorLower hUpper))

/-- 素数の乗法的な特徴付け：2以上で、積に分解すれば片方の因子が1。 -/
def PrimeByMultiplication (n : Nat) : Prop :=
  2 ≤ n ∧ ∀ left right, n = left * right → left = 1 ∨ right = 1

/-- 真の約数がない条件は、非自明な積に分解できない条件と同値である。

一方向では非自明な積の左因子が真の約数になることを使う。逆方向では真の約数を
商との積に書き、商も1ではないことから非自明な積を得る。
-/
theorem noProperDivisor_iff_primeByMultiplication (n : Nat) :
    2 ≤ n ∧ (∀ divisor, 2 ≤ divisor → divisor < n → n % divisor ≠ 0) ↔
      PrimeByMultiplication n := by
  constructor
  · rintro ⟨hLower, hNoDivisor⟩
    refine ⟨hLower, ?_⟩
    intro left right hProduct
    by_cases hLeft : left = 1
    · exact Or.inl hLeft
    · by_cases hRight : right = 1
      · exact Or.inr hRight
      · have hLeftNeZero : left ≠ 0 := by
          intro hZero
          subst left
          simp at hProduct
          omega
        have hRightNeZero : right ≠ 0 := by
          intro hZero
          subst right
          simp at hProduct
          omega
        have hLeftLower : 2 ≤ left := by omega
        have hRightLower : 2 ≤ right := by omega
        have hLeftUpper : left < n := by
          calc
            left < left * 2 := by omega
            _ ≤ left * right := Nat.mul_le_mul_left left hRightLower
            _ = n := hProduct.symm
        have hDivides : left ∣ n := ⟨right, hProduct⟩
        have hMod := (Nat.dvd_iff_mod_eq_zero).mp hDivides
        exact False.elim (hNoDivisor left hLeftLower hLeftUpper hMod)
  · rintro ⟨hLower, hProductPrime⟩
    refine ⟨hLower, ?_⟩
    intro divisor hDivisorLower hDivisorUpper hMod
    have hDivides : divisor ∣ n := (Nat.dvd_iff_mod_eq_zero).mpr hMod
    obtain ⟨quotient, hProduct⟩ := hDivides
    have hQuotientNeZero : quotient ≠ 0 := by
      intro hZero
      subst quotient
      simp at hProduct
      omega
    have hQuotientNeOne : quotient ≠ 1 := by
      intro hOne
      subst quotient
      simp at hProduct
      omega
    have hQuotientLower : 2 ≤ quotient := by omega
    rcases hProductPrime divisor quotient hProduct with hDivisorOne | hQuotientOne
    · omega
    · exact hQuotientNeOne hQuotientOne

/-- 有限判定器が表す素数条件を乗法的な特徴付けとしても利用できる。 -/
theorem isPrime_iff_primeByMultiplication (n : Nat) :
    IsPrime n ↔ PrimeByMultiplication n := by
  rw [isPrime_iff_no_proper_divisor]
  exact noProperDivisor_iff_primeByMultiplication n

/-- 乗法的な素数条件から、Mathlibの自然数素数条件へ変換する。 -/
private theorem primeByMultiplication_to_natPrime {n : Nat}
    (hPrime : PrimeByMultiplication n) : Nat.Prime n := by
  rw [Nat.prime_iff_not_exists_mul_eq]
  refine ⟨hPrime.1, ?_⟩
  rintro ⟨left, right, hLeft, hRight, hProduct⟩
  rcases hPrime.2 left right hProduct.symm with hLeftOne | hRightOne
  · subst left
    simp at hProduct
    omega
  · subst right
    simp at hProduct
    omega

/-- 因子列の隣接要素が非減少かを判定する。 -/
def ascendingCheck : List Nat → Bool
  | [] => true
  | [_] => true
  | first :: second :: rest =>
      decide (first ≤ second) && ascendingCheck (second :: rest)

/-- 隣接要素の昇順検査から、全ての前後要素間の順序を導く。 -/
private theorem ascendingCheck_pairwise_aux : ∀ values,
    ascendingCheck values = true → values.Pairwise (fun a b : Nat => a ≤ b)
  | [], _ => .nil
  | [_], _ => .cons (by intro other h; simp at h) .nil
  | first :: second :: rest, h => by
      simp only [ascendingCheck, Bool.and_eq_true] at h
      apply List.Pairwise.cons
      · intro later hLater
        simp only [List.mem_cons] at hLater
        rcases hLater with hSecond | hRest
        · subst later
          exact of_decide_eq_true h.1
        · exact Nat.le_trans (of_decide_eq_true h.1)
            (List.rel_of_pairwise_cons (ascendingCheck_pairwise_aux (second :: rest) h.2)
              (by simp [hRest]))
      · exact ascendingCheck_pairwise_aux (second :: rest) h.2

/-- 全要素間の順序が Pairwise で分かれば、隣接要素の検査器は成功する。 -/
private theorem ascendingCheck_eq_true_of_pairwise : ∀ {values},
    values.Pairwise (fun a b : Nat => a ≤ b) → ascendingCheck values = true
  | [], _ => rfl
  | [_], _ => rfl
  | first :: second :: rest, h => by
      simp only [ascendingCheck, Bool.and_eq_true]
      refine ⟨decide_eq_true (List.rel_of_pairwise_cons h (by simp)), ?_⟩
      exact ascendingCheck_eq_true_of_pairwise h.tail

/-- Mathlibの自然数素数条件から、このファイルのBoolean素数検査へ戻す。 -/
private theorem natPrime_to_isPrime {n : Nat} (hPrime : Nat.Prime n) : IsPrime n := by
  apply (isPrime_iff_no_proper_divisor n).2
  obtain ⟨hLower, hNoDivisor⟩ := Nat.prime_def_lt'.mp hPrime
  refine ⟨hLower, ?_⟩
  intro divisor hLowerDivisor hUpperDivisor hMod
  have hDivides : divisor ∣ n := Nat.dvd_iff_mod_eq_zero.mpr hMod
  exact (hNoDivisor divisor hLowerDivisor hUpperDivisor hDivides).elim

/-- 素因数分解結果の仕様。

0 と 1 は空配列を返す約束とし、2 以上では因子の積が入力に戻り、因子が昇順で、
各因子が素数であることを要求する。
-/
def FactorsCorrect (n : Nat) (factors : List Nat) : Prop :=
  if n ≤ 1 then factors = [] else
    factors.foldl Nat.mul 1 = n ∧
    ascendingCheck factors = true ∧
    factors.all isPrimeCheck = true

instance (n : Nat) (factors : List Nat) : Decidable (FactorsCorrect n factors) := by
  unfold FactorsCorrect
  infer_instance

/-- 正しい素因数列は入力だけから一意に決まる。

積と各因子の素数性から、素因数列の一意性を表す Mathlib の定理で両列が順列と
分かる。さらに、昇順性を Pairwise 条件へ変換し、昇順な順列どうしは一致することを
使ってリストそのものの等しさを導く。
-/
theorem FactorsCorrect.eq_of_same_input {n : Nat} {factors₁ factors₂ : List Nat}
    (hCorrect₁ : FactorsCorrect n factors₁)
    (hCorrect₂ : FactorsCorrect n factors₂) : factors₁ = factors₂ := by
  by_cases hSmall : n ≤ 1
  · have h₁ : factors₁ = [] := by
      simpa [FactorsCorrect, hSmall] using hCorrect₁
    have h₂ : factors₂ = [] := by
      simpa [FactorsCorrect, hSmall] using hCorrect₂
    rw [h₁, h₂]
  · have hLower : 2 ≤ n := by omega
    have hParts₁ : factors₁.foldl Nat.mul 1 = n ∧
        ascendingCheck factors₁ = true ∧ factors₁.all isPrimeCheck = true := by
      simpa [FactorsCorrect, hSmall] using hCorrect₁
    have hParts₂ : factors₂.foldl Nat.mul 1 = n ∧
        ascendingCheck factors₂ = true ∧ factors₂.all isPrimeCheck = true := by
      simpa [FactorsCorrect, hSmall] using hCorrect₂
    have hProduct₁ : factors₁.prod = n := by
      rw [List.prod_eq_foldl]
      exact hParts₁.1
    have hProduct₂ : factors₂.prod = n := by
      rw [List.prod_eq_foldl]
      exact hParts₂.1
    have hPrime₁ : ∀ factor ∈ factors₁, Nat.Prime factor := by
      intro factor hFactor
      have hIsPrime : IsPrime factor :=
        (List.all_eq_true.mp hParts₁.2.2) factor hFactor
      exact primeByMultiplication_to_natPrime
        ((isPrime_iff_primeByMultiplication factor).mp hIsPrime)
    have hPrime₂ : ∀ factor ∈ factors₂, Nat.Prime factor := by
      intro factor hFactor
      have hIsPrime : IsPrime factor :=
        (List.all_eq_true.mp hParts₂.2.2) factor hFactor
      exact primeByMultiplication_to_natPrime
        ((isPrime_iff_primeByMultiplication factor).mp hIsPrime)
    have hPerm₁ : factors₁.Perm n.primeFactorsList :=
      Nat.primeFactorsList_unique hProduct₁ hPrime₁
    have hPerm₂ : factors₂.Perm n.primeFactorsList :=
      Nat.primeFactorsList_unique hProduct₂ hPrime₂
    have hPerm : factors₁.Perm factors₂ := hPerm₁.trans hPerm₂.symm
    have hSorted₁ := ascendingCheck_pairwise_aux factors₁ hParts₁.2.1
    have hSorted₂ := ascendingCheck_pairwise_aux factors₂ hParts₂.2.1
    exact List.Perm.eq_of_pairwise' hSorted₁ hSorted₂ hPerm

/-- Mathlibの標準素因数列は、このファイルの完全な因数分解仕様を満たす。 -/
theorem FactorsCorrect.primeFactorsList_correct (n : Nat) :
    FactorsCorrect n n.primeFactorsList := by
  by_cases hSmall : n ≤ 1
  · have hEmpty : n.primeFactorsList = [] := by
      rw [Nat.primeFactorsList_eq_nil]
      omega
    simp [FactorsCorrect, hSmall, hEmpty]
  · have hNonzero : n ≠ 0 := by omega
    have hParts : n.primeFactorsList.foldl Nat.mul 1 = n ∧
        ascendingCheck n.primeFactorsList = true ∧
        n.primeFactorsList.all isPrimeCheck = true := by
      refine ⟨?_, ?_, ?_⟩
      · change n.primeFactorsList.foldl (fun left right => left * right) 1 = n
        rw [← List.prod_eq_foldl]
        exact Nat.prod_primeFactorsList hNonzero
      · exact ascendingCheck_eq_true_of_pairwise
          (Nat.primeFactorsList_sorted n).pairwise
      · apply List.all_eq_true.mpr
        intro factor hFactor
        exact natPrime_to_isPrime (Nat.prime_of_mem_primeFactorsList hFactor)
    simpa [FactorsCorrect, hSmall] using hParts

/-- 正しい因数列は、Mathlibの標準素因数列と一致する。 -/
theorem FactorsCorrect.eq_primeFactorsList {n : Nat} {factors : List Nat}
    (hCorrect : FactorsCorrect n factors) : factors = n.primeFactorsList :=
  FactorsCorrect.eq_of_same_input hCorrect (FactorsCorrect.primeFactorsList_correct n)

/-- 正しい因数列での各値の重複度は、入力の素因数分解における指数と一致する。

因子列全体の積だけでなく、任意の自然数 `factor` が何回現れるかを
`Nat.factorization` の指数として取り出せる。`factor` が素数でない場合も指数は 0 となる。
-/
theorem FactorsCorrect.count_eq_factorization {n : Nat} {factors : List Nat}
    (hCorrect : FactorsCorrect n factors) (factor : Nat) :
    factors.count factor = n.factorization factor := by
  rw [hCorrect.eq_primeFactorsList, Nat.primeFactorsList_count_eq]

/-- 数が平方数であることは、各素数の因数列中の出現回数が偶数であることと同値。

平方判定を具体的な値の計算へ還元せず、因数列の重複度だけで特徴付ける。素数でない値は
条件の対象外であり、0 の因数列も空なのでこの同値性に含まれる。
-/
theorem FactorsCorrect.isSquare_iff_even_count {n : Nat} {factors : List Nat}
    (hCorrect : FactorsCorrect n factors) :
    IsSquare n ↔ ∀ prime, Nat.Prime prime → Even (factors.count prime) := by
  rw [Nat.isSquare_iff_even_factorization]
  constructor
  · intro hSquareFactors prime hPrime
    simpa [← hCorrect.count_eq_factorization prime] using hSquareFactors prime hPrime
  · intro hEvenCounts prime hPrime
    simpa [hCorrect.count_eq_factorization prime] using hEvenCounts prime hPrime

/-- `n` が正の指数 `k` のべきであることは、各素数の重複度が `k` で割り切れることと同値。

平方数の場合の偶数性を任意の正の指数へ一般化する。逆方向では `Nat.floorRoot` を候補の
底にし、その素因数指数が元の指数を割り切る仮定から元の数との素因数分解の一致を示す。
指数を正に限定することで、`k = 0` のべきが常に 1 になる例外を除いている。
-/
theorem FactorsCorrect.isPower_iff_count_dvd {n : Nat} {factors : List Nat}
    (hCorrect : FactorsCorrect n factors) {exponent : Nat} (hExponent : 0 < exponent) :
    (∃ base, n = base ^ exponent) ↔
      ∀ prime, Nat.Prime prime → exponent ∣ factors.count prime := by
  constructor
  · rintro ⟨base, rfl⟩ prime hPrime
    by_cases hBase : base = 0
    · subst base
      have hEmpty : factors = [] := by
        have hCorrectZero : FactorsCorrect 0 factors := by
          simpa [Nat.zero_pow hExponent] using hCorrect
        simpa [FactorsCorrect] using hCorrectZero
      simp [hEmpty]
    · have hCount : factors.count prime = exponent * base.factorization prime := by
        rw [hCorrect.count_eq_factorization, Nat.factorization_pow]
        simp [Finsupp.smul_apply]
      exact ⟨base.factorization prime, by simp [hCount]⟩
  · intro hCounts
    by_cases hZero : n = 0
    · exact ⟨0, by simp [hZero, Nat.zero_pow hExponent]⟩
    · let base := Nat.floorRoot exponent n
      have hBaseNonzero : base ≠ 0 := by
        dsimp [base]
        exact (Nat.floorRoot_ne_zero).2 ⟨by omega, hZero⟩
      have hFactorization : base.factorization = n.factorization ⌊/⌋ exponent := by
        dsimp [base]
        exact Nat.factorization_floorRoot exponent n
      have hFactorizationPow : (base ^ exponent).factorization = n.factorization := by
        ext prime
        by_cases hPrime : Nat.Prime prime
        · have hCountDivides : exponent ∣ n.factorization prime := by
            simpa [hCorrect.count_eq_factorization prime] using hCounts prime hPrime
          rw [Nat.factorization_pow, Finsupp.smul_apply, hFactorization,
            Finsupp.floorDiv_apply, Nat.floorDiv_eq_div]
          change exponent * (n.factorization prime / exponent) = n.factorization prime
          exact Nat.mul_div_cancel' hCountDivides
        · simp [Nat.factorization_pow, Finsupp.smul_apply, hPrime,
            Nat.factorization_eq_zero_of_not_prime]
      have hPowerNonzero : base ^ exponent ≠ 0 := pow_ne_zero _ hBaseNonzero
      have hPowerEq : base ^ exponent = n :=
        Nat.eq_of_factorization_eq' hPowerNonzero hZero hFactorizationPow
      exact ⟨base, hPowerEq.symm⟩

/-- `floorRoot` を指数乗して元の数に戻る条件を素因数の重複度で特徴付ける。

指数が正なら、`n` がその指数のべきであることは `floorRoot` が完全な根を返すことと同値。
前定理と合わせると、完全な根が得られる条件は、正しい因数列における各素数の個数が
指数で割り切れることに等しい。
-/
theorem FactorsCorrect.floorRoot_pow_eq_iff_count_dvd {n : Nat} {factors : List Nat}
    (hCorrect : FactorsCorrect n factors) {exponent : Nat} (hExponent : 0 < exponent) :
    Nat.floorRoot exponent n ^ exponent = n ↔
      ∀ prime, Nat.Prime prime → exponent ∣ factors.count prime := by
  have hPower := FactorsCorrect.isPower_iff_count_dvd hCorrect hExponent
  constructor
  · intro hRoot
    apply hPower.mp
    exact ⟨Nat.floorRoot exponent n, hRoot.symm⟩
  · intro hCounts
    obtain ⟨base, hBase⟩ := hPower.mpr hCounts
    calc
      Nat.floorRoot exponent n ^ exponent =
          Nat.floorRoot exponent (base ^ exponent) ^ exponent := by rw [hBase]
      _ = base ^ exponent := by rw [Nat.floorRoot_pow_self (by omega : exponent ≠ 0)]
      _ = n := hBase.symm

/-- `floorRoot` の素因数重複度は、入力列の重複度を指数で割った商になる。

`Nat.floorRoot` は各素数の指数を切り捨て除算する。標準素因数列の個数と
`FactorsCorrect` が与える任意の正しい因数列の個数を結び、根の構成を列の仕様上でも
読み取れる形にする。
-/
theorem FactorsCorrect.floorRoot_count_eq_div {n : Nat} {factors : List Nat}
    (hCorrect : FactorsCorrect n factors) (exponent factor : Nat) :
    (Nat.floorRoot exponent n).primeFactorsList.count factor =
      factors.count factor / exponent := by
  rw [Nat.primeFactorsList_count_eq, Nat.factorization_floorRoot,
    Finsupp.floorDiv_apply, Nat.floorDiv_eq_div,
    hCorrect.count_eq_factorization factor]

/-- `n` から指数 `exponent` の完全べき部分を取り除いた残差。

`Nat.floorRoot` が各素因数の指数を `exponent` で割った商を集めるため、この残差には
指数の余りに対応する素因数だけが残る。
-/
def powerRemainder (exponent n : Nat) : Nat :=
  n / (Nat.floorRoot exponent n ^ exponent)

/-- 完全べき部分と残差の積は、元の入力に一致する。

`floorRoot_pow_dvd` が与える除法可能性を用い、自然数の除算の商を戻す。
-/
theorem powerRemainder_decomposition (n exponent : Nat) :
    Nat.floorRoot exponent n ^ exponent * powerRemainder exponent n = n := by
  unfold powerRemainder
  exact Nat.mul_div_cancel' (Nat.floorRoot_pow_dvd (n := exponent) (a := n))

/-- 完全べき部分を除いた残差は、元の入力を割り切る。

`powerRemainder_decomposition` の積を交換し、残差を積の第一因子として表す。
-/
theorem powerRemainder_dvd (n exponent : Nat) : powerRemainder exponent n ∣ n := by
  refine ⟨Nat.floorRoot exponent n ^ exponent, ?_⟩
  calc
    n = Nat.floorRoot exponent n ^ exponent * powerRemainder exponent n :=
      (powerRemainder_decomposition n exponent).symm
    _ = powerRemainder exponent n * (Nat.floorRoot exponent n ^ exponent) :=
      Nat.mul_comm _ _

/-- 指数1の完全べき分解では、非零入力の残差は1になる。

`floorRoot 1 n = n` なので、入力全体を完全べき部分として取り出した後には因子が残らない。
-/
theorem powerRemainder_one_eq_one {n : Nat} (hNonzero : n ≠ 0) :
    powerRemainder 1 n = 1 := by
  unfold powerRemainder
  rw [Nat.floorRoot_one_left, Nat.pow_one, Nat.div_self (Nat.pos_of_ne_zero hNonzero)]

/-- 非零入力で残差が1になることは、入力が指数乗であることと同値。

残差が1なら完全べき分解式から入力自体が `floorRoot` の指数乗になる。逆に入力が
指数乗なら `floorRoot_pow_self` で完全べき部分を特定でき、商は1になる。
-/
theorem powerRemainder_eq_one_iff_exists_pow {n exponent : Nat}
    (hExponent : 0 < exponent) (hNonzero : n ≠ 0) :
    powerRemainder exponent n = 1 ↔ ∃ root, n = root ^ exponent := by
  constructor
  · intro hRemainder
    refine ⟨Nat.floorRoot exponent n, ?_⟩
    have hDecomposition := powerRemainder_decomposition n exponent
    rw [hRemainder] at hDecomposition
    simpa using hDecomposition.symm
  · rintro ⟨root, hRoot⟩
    have hRootNonzero : root ≠ 0 := by
      intro hRootZero
      subst root
      rw [hRoot] at hNonzero
      simp at hNonzero
      omega
    unfold powerRemainder
    rw [hRoot, Nat.floorRoot_pow_self (by omega) root]
    exact Nat.div_self (Nat.pow_pos (Nat.pos_of_ne_zero hRootNonzero))

/-- 残差における各素数の重複度は、入力の重複度を指数で割った余り。

従って完全べき部分を除いた後に残る情報も、素因数列の個数から正確に復元できる。
入力を `FactorsCorrect` で表すことで、標準因数列への置き換えによらず利用できる。
-/
theorem FactorsCorrect.powerRemainder_factorization {n : Nat} {factors : List Nat}
    (hCorrect : FactorsCorrect n factors) (exponent factor : Nat) :
    (powerRemainder exponent n).factorization factor = factors.count factor % exponent := by
  have hDivides : Nat.floorRoot exponent n ^ exponent ∣ n :=
    Nat.floorRoot_pow_dvd (n := exponent) (a := n)
  rw [powerRemainder, Nat.factorization_div hDivides,
    Nat.factorization_pow, Nat.factorization_floorRoot]
  change n.factorization factor -
    exponent * (n.factorization factor / exponent) = factors.count factor % exponent
  rw [← hCorrect.count_eq_factorization factor]
  have hMod := Nat.mod_add_div (factors.count factor) exponent
  omega

/-- 正の指数 `k` に対し、残差に含まれる各素数の重複度は `k` 未満。

従って残差は、どの素数についても `k` 個以上の同じ因子を含まない。これは入力を完全な
`k` 乗部分と指数 `k` 未満の部分へ分けたことを、因数列の重複度で表す系である。
-/
theorem FactorsCorrect.powerRemainder_factorization_lt {n : Nat} {factors : List Nat}
    (hCorrect : FactorsCorrect n factors) {exponent : Nat}
    (hExponent : 0 < exponent) (factor : Nat) :
    (powerRemainder exponent n).factorization factor < exponent := by
  rw [FactorsCorrect.powerRemainder_factorization hCorrect exponent factor]
  exact Nat.mod_lt _ hExponent

/-- 非零入力から平方部分を除いた残差は squarefree である。

指数 2 の残差では、各素数の重複度が 2 未満になる。残差が非零であることは
完全べき部分との積が元の入力に戻る分解定理から従うため、Mathlib の一般判定に
重複度の上界を渡して平方因子の不在を示す。
-/
theorem FactorsCorrect.powerRemainder_two_squarefree {n : Nat} {factors : List Nat}
    (hCorrect : FactorsCorrect n factors) (hNonzero : n ≠ 0) :
    Squarefree (powerRemainder 2 n) := by
  have hRemainderNonzero : powerRemainder 2 n ≠ 0 := by
    intro hRemainderZero
    have hDecomposition := powerRemainder_decomposition n 2
    rw [hRemainderZero] at hDecomposition
    simp at hDecomposition
    exact hNonzero hDecomposition.symm
  apply Nat.squarefree_of_factorization_le_one hRemainderNonzero
  intro prime
  have hMultiplicity := FactorsCorrect.powerRemainder_factorization_lt
    hCorrect (exponent := 2) (by omega) prime
  omega

/-- 非零な数が squarefree であることは、正しい素因数列に重複がないことと同値。

因数列では重複を指数の代わりに表すため、`Nodup` が平方因子の不在を直接表現する。
0 は `FactorsCorrect` の約束で空列だが squarefree ではないため、非零条件を明示する。
-/
theorem FactorsCorrect.squarefree_iff_nodup {n : Nat} {factors : List Nat}
    (hCorrect : FactorsCorrect n factors) (hNonzero : n ≠ 0) :
    Squarefree n ↔ factors.Nodup := by
  rw [Nat.squarefree_iff_nodup_primeFactorsList hNonzero,
    hCorrect.eq_primeFactorsList]

/-- 非零入力では、素数 `prime` が正しい因数列に現れることと、入力を割り切ることは同値。

因数列の積や昇順性を個別に使わず、完全な因数分解仕様が標準素因数列と一致することから
素数因子の所属を特徴付ける。
-/
theorem FactorsCorrect.mem_iff_prime_dvd {n : Nat} {factors : List Nat}
    (hCorrect : FactorsCorrect n factors) (hNonzero : n ≠ 0)
    {prime : Nat} (hPrime : Nat.Prime prime) :
    prime ∈ factors ↔ prime ∣ n := by
  rw [hCorrect.eq_primeFactorsList]
  exact Nat.mem_primeFactorsList_iff_dvd hNonzero hPrime

/-- 素数の `k` 乗が入力を割り切ることは、因数列中にその素数が `k` 回以上現れることと同値。

素因数の重複度を、素数べきの約数条件として直接利用できる。
-/
theorem FactorsCorrect.prime_pow_dvd_iff_count_ge {n : Nat} {factors : List Nat}
    (hCorrect : FactorsCorrect n factors) (hNonzero : n ≠ 0)
    {prime exponent : Nat} (hPrime : Nat.Prime prime) :
    prime ^ exponent ∣ n ↔ exponent ≤ factors.count prime := by
  rw [hPrime.pow_dvd_iff_le_factorization hNonzero,
    ← hCorrect.count_eq_factorization prime]

/-- 非零な `d` が入力を割り切ることは、全ての素因子の指数が列内の個数以下であることと同値。

素数べきごとの判定をまとめ、任意の約数を因数列の重複度から特徴付ける。比較対象を
全ての自然数 `prime` に取っても、素数でない値の指数と列内個数はともに 0 となる。
-/
theorem FactorsCorrect.dvd_iff_factorization_le_counts {n : Nat} {factors : List Nat}
    (hCorrect : FactorsCorrect n factors) (hNonzero : n ≠ 0)
    {d : Nat} (hDNonzero : d ≠ 0) :
    d ∣ n ↔ ∀ prime, d.factorization prime ≤ factors.count prime := by
  rw [← Nat.factorization_le_iff_dvd hDNonzero hNonzero]
  constructor
  · intro hFactorization prime
    calc
      d.factorization prime ≤ n.factorization prime := hFactorization prime
      _ = factors.count prime := (hCorrect.count_eq_factorization prime).symm
  · intro hCounts prime
    calc
      d.factorization prime ≤ factors.count prime := hCounts prime
      _ = n.factorization prime := hCorrect.count_eq_factorization prime

/-- 積の正しい因数列は、各因数列を連結したものと順列になる。

各入力と積の因数列がそれぞれ `FactorsCorrect` を満たすなら、積では各素因数の重複度が
加算される。従って積の結果は、二つの入力の結果を並べ替えた列と同じ要素を持つ。
連結自体の昇順性は要求せず、ここでは重複込みの要素保存だけを述べる。
-/
theorem FactorsCorrect.mul_perm_append {n m : Nat}
    {factorsN factorsM factorsProduct : List Nat}
    (hN : FactorsCorrect n factorsN) (hM : FactorsCorrect m factorsM)
    (hProduct : FactorsCorrect (n * m) factorsProduct)
    (hNNonzero : n ≠ 0) (hMNonzero : m ≠ 0) :
    factorsProduct.Perm (factorsN ++ factorsM) := by
  apply List.perm_iff_count.mpr
  intro factor
  calc
    factorsProduct.count factor = (n * m).factorization factor :=
      hProduct.count_eq_factorization factor
    _ = n.factorization factor + m.factorization factor := by
      rw [Nat.factorization_mul hNNonzero hMNonzero]
      simp
    _ = factorsN.count factor + factorsM.count factor := by
      rw [← hN.count_eq_factorization factor, ← hM.count_eq_factorization factor]
    _ = (factorsN ++ factorsM).count factor := by simp [List.count_append]

/-- 二つの正しい因数列を併合ソートすると、積の正しい因数列が得られる。

非零な二入力の標準素因数列は、積の標準素因数列と連結順列の関係にある。
入力列を併合ソートした結果も同じ多重集合を持ち、両方とも昇順なので一致する。
これにより、因数分解仕様が乗算に対して閉じていることを示す。
-/
theorem FactorsCorrect.mul_mergeSort {n m : Nat}
    {factorsN factorsM : List Nat}
    (hN : FactorsCorrect n factorsN) (hM : FactorsCorrect m factorsM)
    (hNNonzero : n ≠ 0) (hMNonzero : m ≠ 0) :
    FactorsCorrect (n * m)
      ((factorsN ++ factorsM).mergeSort (· ≤ ·)) := by
  let output := (factorsN ++ factorsM).mergeSort (· ≤ ·)
  have hInputsEq : factorsN ++ factorsM = n.primeFactorsList ++ m.primeFactorsList := by
    rw [hN.eq_primeFactorsList, hM.eq_primeFactorsList]
  have hSortPerm : output.Perm (factorsN ++ factorsM) := by
    simpa [output] using List.mergeSort_perm (factorsN ++ factorsM) (· ≤ ·)
  have hOutputPerm : output.Perm (n * m).primeFactorsList := by
    exact hSortPerm.trans ((List.Perm.of_eq hInputsEq).trans
      (Nat.perm_primeFactorsList_mul hNNonzero hMNonzero).symm)
  have hOutputSorted : output.Pairwise (fun a b : Nat => a ≤ b) := by
    simpa [output] using List.pairwise_mergeSort' (r := (· ≤ ·))
      (factorsN ++ factorsM)
  have hCanonicalSorted : ((n * m).primeFactorsList).Pairwise (fun a b : Nat => a ≤ b) :=
    (Nat.primeFactorsList_sorted (n * m)).pairwise
  have hOutputEq : output = (n * m).primeFactorsList :=
    List.Perm.eq_of_pairwise' hOutputSorted hCanonicalSorted hOutputPerm
  change FactorsCorrect (n * m) output
  rw [hOutputEq]
  exact FactorsCorrect.primeFactorsList_correct (n * m)

/-- 因数列から、その列を指数回分含む昇順リストを作る検証用構成。 -/
def factorsPower (factors : List Nat) : Nat → List Nat
  | 0 => []
  | exponent + 1 =>
      (factorsPower factors exponent ++ factors).mergeSort (· ≤ ·)

/-- 正しい因数列から任意の自然数べきの正しい因数列を構成できる。

指数 0 では 1 の空因数列を返す。指数を 1 つ増やす段階では、直前の列と元の列を連結して
整列し、積に対する閉包定理を適用する。従って、任意の指数で積・昇順性・素数性が保たれる。
-/
theorem FactorsCorrect.pow_mergeSort {n : Nat} {factors : List Nat}
    (hCorrect : FactorsCorrect n factors) (hNonzero : n ≠ 0) (exponent : Nat) :
    FactorsCorrect (n ^ exponent) (factorsPower factors exponent) := by
  induction exponent with
  | zero => simp [factorsPower, FactorsCorrect]
  | succ exponent ih =>
    simpa [factorsPower, Nat.pow_succ] using
      FactorsCorrect.mul_mergeSort ih hCorrect (pow_ne_zero _ hNonzero) hNonzero

/-- べき乗用に構成した因数列では、各因子の重複度が指数倍になる。

`pow_mergeSort` は積・整列・素数性を保証するが、この系ではそれを素因数指数の仕様へ
接続し、実際に構成した列の各値の個数まで特定する。
-/
theorem FactorsCorrect.pow_count_eq_mul {n : Nat} {factors : List Nat}
    (hCorrect : FactorsCorrect n factors) (hNonzero : n ≠ 0)
    (exponent factor : Nat) :
    (factorsPower factors exponent).count factor = exponent * factors.count factor := by
  have hPowerCorrect := FactorsCorrect.pow_mergeSort hCorrect hNonzero exponent
  calc
    (factorsPower factors exponent).count factor = (n ^ exponent).factorization factor :=
      hPowerCorrect.count_eq_factorization factor
    _ = exponent * n.factorization factor := by
      rw [Nat.factorization_pow]
      simp [Finsupp.smul_apply]
    _ = exponent * factors.count factor := by
      rw [hCorrect.count_eq_factorization factor]

/-- 最大公約数の因数重複度は、二つの入力の重複度の小さい方になる。 -/
theorem FactorsCorrect.gcd_count_eq_min {n m : Nat}
    {factorsN factorsM factorsGcd : List Nat}
    (hN : FactorsCorrect n factorsN) (hM : FactorsCorrect m factorsM)
    (hGcd : FactorsCorrect (Nat.gcd n m) factorsGcd)
    (hNNonzero : n ≠ 0) (hMNonzero : m ≠ 0) (factor : Nat) :
    factorsGcd.count factor = min (factorsN.count factor) (factorsM.count factor) := by
  calc
    factorsGcd.count factor = (Nat.gcd n m).factorization factor :=
      hGcd.count_eq_factorization factor
    _ = min (n.factorization factor) (m.factorization factor) := by
      rw [Nat.factorization_gcd hNNonzero hMNonzero]
      rfl
    _ = min (factorsN.count factor) (factorsM.count factor) := by
      rw [← hN.count_eq_factorization factor, ← hM.count_eq_factorization factor]

/-- 最小公倍数の因数重複度は、二つの入力の重複度の大きい方になる。 -/
theorem FactorsCorrect.lcm_count_eq_max {n m : Nat}
    {factorsN factorsM factorsLcm : List Nat}
    (hN : FactorsCorrect n factorsN) (hM : FactorsCorrect m factorsM)
    (hLcm : FactorsCorrect (Nat.lcm n m) factorsLcm)
    (hNNonzero : n ≠ 0) (hMNonzero : m ≠ 0) (factor : Nat) :
    factorsLcm.count factor = max (factorsN.count factor) (factorsM.count factor) := by
  calc
    factorsLcm.count factor = (Nat.lcm n m).factorization factor :=
      hLcm.count_eq_factorization factor
    _ = max (n.factorization factor) (m.factorization factor) := by
      rw [Nat.factorization_lcm hNNonzero hMNonzero]
      rfl
    _ = max (factorsN.count factor) (factorsM.count factor) := by
      rw [← hN.count_eq_factorization factor, ← hM.count_eq_factorization factor]

/-- 2以上の入力について、正しい因数列の積は必ず元の入力に戻る。 -/
theorem FactorsCorrect.product_eq {n : Nat} {factors : List Nat}
    (hCorrect : FactorsCorrect n factors) (hLower : 2 ≤ n) :
    factors.foldl Nat.mul 1 = n := by
  have hNotSmall : ¬ n ≤ 1 := by omega
  have hParts :
      factors.foldl Nat.mul 1 = n ∧ ascendingCheck factors = true ∧
        factors.all isPrimeCheck = true := by
    simpa [FactorsCorrect, hNotSmall] using hCorrect
  exact hParts.1

/-- 正しい因数列に含まれる各要素は、乗法的特徴付けで見ても素数である。 -/
theorem FactorsCorrect.factor_isPrimeByMultiplication {n : Nat}
    {factors : List Nat} (hCorrect : FactorsCorrect n factors)
    {factor : Nat} (hFactor : factor ∈ factors) : PrimeByMultiplication factor := by
  by_cases hSmall : n ≤ 1
  · have hEmpty : factors = [] := by
      simpa [FactorsCorrect, hSmall] using hCorrect
    rw [hEmpty] at hFactor
    simp at hFactor
  · have hParts :
        factors.foldl Nat.mul 1 = n ∧ ascendingCheck factors = true ∧
          factors.all isPrimeCheck = true := by
      simpa [FactorsCorrect, hSmall] using hCorrect
    have hIsPrime : IsPrime factor :=
      (List.all_eq_true.mp hParts.2.2) factor hFactor
    exact (isPrime_iff_primeByMultiplication factor).mp hIsPrime

/-- 正しい因数列の各因子は2以上である。 -/
theorem FactorsCorrect.factor_ge_two {n : Nat} {factors : List Nat}
    (hCorrect : FactorsCorrect n factors) {factor : Nat}
    (hFactor : factor ∈ factors) : 2 ≤ factor :=
  (FactorsCorrect.factor_isPrimeByMultiplication hCorrect hFactor).1

/-- 2以上の数を正しく分解した因数列は空にならない。 -/
theorem FactorsCorrect.nonempty_of_two_le {n : Nat} {factors : List Nat}
    (hCorrect : FactorsCorrect n factors) (hLower : 2 ≤ n) : factors ≠ [] := by
  intro hEmpty
  have hProduct := FactorsCorrect.product_eq hCorrect hLower
  rw [hEmpty] at hProduct
  simp at hProduct
  omega

/-- 正しい因数列が空であることと、入力が0または1であることは同値である。 -/
theorem FactorsCorrect.isEmpty_iff_le_one {n : Nat} {factors : List Nat}
    (hCorrect : FactorsCorrect n factors) : factors = [] ↔ n ≤ 1 := by
  constructor
  · intro hEmpty
    by_cases hSmall : n ≤ 1
    · exact hSmall
    · have hLarge : 2 ≤ n := by omega
      exact False.elim (hCorrect.nonempty_of_two_le hLarge hEmpty)
  · intro hSmall
    simpa [FactorsCorrect, hSmall] using hCorrect

/-- 二つの正しい因数列が一致する条件を入力値まで含めて特徴付ける。

2以上では積から入力を復元できる。一方、0と1はどちらも空列へ写るため、その場合だけ
入力値の違いが出力から区別できない。 -/
theorem FactorsCorrect.eq_iff_input_eq_or_both_le_one
    {n m : Nat} {factors₁ factors₂ : List Nat}
    (hCorrect₁ : FactorsCorrect n factors₁)
    (hCorrect₂ : FactorsCorrect m factors₂) :
    factors₁ = factors₂ ↔ n = m ∨ (n ≤ 1 ∧ m ≤ 1) := by
  constructor
  · intro hFactors
    by_cases hSmall₁ : n ≤ 1
    · by_cases hSmall₂ : m ≤ 1
      · exact Or.inr ⟨hSmall₁, hSmall₂⟩
      · have hEmpty₁ := (FactorsCorrect.isEmpty_iff_le_one hCorrect₁).mpr hSmall₁
        have hEmpty₂ : factors₂ = [] := by rw [← hFactors, hEmpty₁]
        have hSmall₂' := (FactorsCorrect.isEmpty_iff_le_one hCorrect₂).mp hEmpty₂
        omega
    · by_cases hSmall₂ : m ≤ 1
      · have hEmpty₂ := (FactorsCorrect.isEmpty_iff_le_one hCorrect₂).mpr hSmall₂
        have hEmpty₁ : factors₁ = [] := by rw [hFactors, hEmpty₂]
        have hSmall₁' := (FactorsCorrect.isEmpty_iff_le_one hCorrect₁).mp hEmpty₁
        omega
      · have hLower₁ : 2 ≤ n := by omega
        have hLower₂ : 2 ≤ m := by omega
        have hProduct₁ := FactorsCorrect.product_eq hCorrect₁ hLower₁
        have hProduct₂ := FactorsCorrect.product_eq hCorrect₂ hLower₂
        have hProduct₁' : factors₁.prod = n := by
          rw [List.prod_eq_foldl]
          exact hProduct₁
        have hProduct₂' : factors₂.prod = m := by
          rw [List.prod_eq_foldl]
          exact hProduct₂
        rw [← hFactors] at hProduct₂'
        exact Or.inl (hProduct₁'.symm.trans hProduct₂')
  · rintro (rfl | ⟨hSmall₁, hSmall₂⟩)
    · exact FactorsCorrect.eq_of_same_input hCorrect₁ hCorrect₂
    · have hEmpty₁ := (FactorsCorrect.isEmpty_iff_le_one hCorrect₁).mpr hSmall₁
      have hEmpty₂ := (FactorsCorrect.isEmpty_iff_le_one hCorrect₂).mpr hSmall₂
      rw [hEmpty₁, hEmpty₂]

/-- `foldl` で積を取るとき、初期値は入力列の積全体の先頭因子になる。 -/
private theorem foldl_mul_eq_mul_foldl (values : List Nat) (initial : Nat) :
    values.foldl Nat.mul initial = initial * values.foldl Nat.mul 1 := by
  induction values generalizing initial with
  | nil => simp
  | cons value rest ih =>
      change rest.foldl Nat.mul (initial * value) =
        initial * rest.foldl Nat.mul (1 * value)
      calc
        rest.foldl Nat.mul (initial * value) =
            (initial * value) * rest.foldl Nat.mul 1 := ih _
        _ = initial * (value * rest.foldl Nat.mul 1) := by ac_rfl
        _ = initial * rest.foldl Nat.mul value := by rw [← ih value]
        _ = initial * rest.foldl Nat.mul (1 * value) := by rw [Nat.one_mul]

/-- リストに含まれる値は、そのリストの積を割り切る。 -/
private theorem mem_dvd_foldl_mul : ∀ {values : List Nat} {value : Nat},
    value ∈ values → value ∣ values.foldl Nat.mul 1 := by
  intro values
  induction values with
  | nil => simp
  | cons head tail ih =>
      intro value hMember
      have hProduct : (head :: tail).foldl Nat.mul 1 =
          head * tail.foldl Nat.mul 1 := by
        change tail.foldl Nat.mul (1 * head) = _
        rw [Nat.one_mul, foldl_mul_eq_mul_foldl]
      simp only [List.mem_cons] at hMember
      rw [hProduct]
      rcases hMember with hHead | hTail
      · subst value
        exact ⟨tail.foldl Nat.mul 1, rfl⟩
      · obtain ⟨quotient, hQuotient⟩ := ih hTail
        refine ⟨head * quotient, ?_⟩
        rw [hQuotient]
        ac_rfl

/-- 正しい因数列に含まれる各因子は、元の入力を割り切る。 -/
theorem FactorsCorrect.factor_dvd_input {n : Nat} {factors : List Nat}
    (hCorrect : FactorsCorrect n factors) {factor : Nat}
    (hFactor : factor ∈ factors) : factor ∣ n := by
  by_cases hSmall : n ≤ 1
  · have hEmpty : factors = [] := by
      simpa [FactorsCorrect, hSmall] using hCorrect
    rw [hEmpty] at hFactor
    simp at hFactor
  · have hProduct := FactorsCorrect.product_eq hCorrect (by omega)
    rw [← hProduct]
    exact mem_dvd_foldl_mul hFactor

/-- 正しい因数列に含まれる各因子は、入力値を超えない。 -/
theorem FactorsCorrect.factor_le_input {n : Nat} {factors : List Nat}
    (hCorrect : FactorsCorrect n factors) {factor : Nat}
    (hFactor : factor ∈ factors) : factor ≤ n := by
  have hPrime := FactorsCorrect.factor_isPrimeByMultiplication hCorrect hFactor
  have hDivides := FactorsCorrect.factor_dvd_input hCorrect hFactor
  have hNotSmall : ¬ n ≤ 1 := by
    intro hSmall
    have hEmpty : factors = [] := by
      simpa [FactorsCorrect, hSmall] using hCorrect
    rw [hEmpty] at hFactor
    simp at hFactor
  exact Nat.le_of_dvd (by omega) hDivides

/-- 因子が全て正なら、その列の積も正である。 -/
private theorem foldl_mul_one_pos (values : List Nat)
    (hPositive : ∀ value ∈ values, 0 < value) :
    0 < values.foldl Nat.mul 1 := by
  induction values with
  | nil => simp
  | cons value rest ih =>
      have hValue : 0 < value := hPositive value (by simp)
      have hRest : ∀ item ∈ rest, 0 < item := by
        intro item hItem
        exact hPositive item (by simp [hItem])
      change 0 < rest.foldl Nat.mul (1 * value)
      rw [Nat.one_mul, foldl_mul_eq_mul_foldl]
      exact Nat.mul_pos hValue (ih hRest)

/-- 因子が全て2以上で列が空でなければ、その積は2以上である。 -/
private theorem foldl_mul_one_ge_two (values : List Nat)
    (hLower : ∀ value ∈ values, 2 ≤ value) (hNonempty : values ≠ []) :
    2 ≤ values.foldl Nat.mul 1 := by
  cases values with
  | nil => contradiction
  | cons value rest =>
      have hValue : 2 ≤ value := hLower value (by simp)
      have hRestPositive : 0 < rest.foldl Nat.mul 1 :=
        foldl_mul_one_pos rest (by
          intro item hItem
          have hItemLower := hLower item (by simp [hItem])
          omega)
      have hProduct :
          (value :: rest).foldl Nat.mul 1 = value * rest.foldl Nat.mul 1 := by
        calc
          (value :: rest).foldl Nat.mul 1 = rest.foldl Nat.mul value := by
            change rest.foldl Nat.mul (1 * value) = _
            rw [Nat.one_mul]
          _ = value * rest.foldl Nat.mul 1 := foldl_mul_eq_mul_foldl rest value
      rw [hProduct]
      calc
        2 ≤ value := hValue
        _ = value * 1 := by simp
        _ ≤ value * rest.foldl Nat.mul 1 :=
          Nat.mul_le_mul_left value (by omega)

/-- 各因子が2以上なら、k個の因子の積は `2^k` 以上になる。 -/
private theorem foldl_mul_one_ge_pow_two (values : List Nat)
    (hLower : ∀ value ∈ values, 2 ≤ value) :
    2 ^ values.length ≤ values.foldl Nat.mul 1 := by
  induction values with
  | nil => simp
  | cons value rest ih =>
      have hValue : 2 ≤ value := hLower value (by simp)
      have hRestLower : ∀ item ∈ rest, 2 ≤ item := by
        intro item hItem
        exact hLower item (by simp [hItem])
      have hProduct :
          (value :: rest).foldl Nat.mul 1 = value * rest.foldl Nat.mul 1 := by
        calc
          (value :: rest).foldl Nat.mul 1 = rest.foldl Nat.mul value := by
            change rest.foldl Nat.mul (1 * value) = _
            rw [Nat.one_mul]
          _ = value * rest.foldl Nat.mul 1 := foldl_mul_eq_mul_foldl rest value
      have hMul : 2 ^ rest.length * 2 ≤ rest.foldl Nat.mul 1 * value :=
        Nat.mul_le_mul (ih hRestLower) hValue
      change 2 ^ (rest.length + 1) ≤ (value :: rest).foldl Nat.mul 1
      rw [hProduct]
      calc
        2 ^ (rest.length + 1) = 2 ^ rest.length * 2 := by rw [Nat.pow_succ]
        _ ≤ rest.foldl Nat.mul 1 * value := hMul
        _ = value * rest.foldl Nat.mul 1 := Nat.mul_comm _ _

/-- 正しい素因数分解では、因子数 `k` に対して `2^k ≤ n` が成立する。 -/
theorem FactorsCorrect.product_ge_pow_two {n : Nat} {factors : List Nat}
    (hCorrect : FactorsCorrect n factors) (hLower : 2 ≤ n) :
    2 ^ factors.length ≤ n := by
  have hFactorsLower : ∀ factor ∈ factors, 2 ≤ factor := by
    intro factor hFactor
    exact FactorsCorrect.factor_ge_two hCorrect hFactor
  calc
    2 ^ factors.length ≤ factors.foldl Nat.mul 1 :=
      foldl_mul_one_ge_pow_two factors hFactorsLower
    _ = n := FactorsCorrect.product_eq hCorrect hLower

/-- 素数を正しく因数分解した列は、その素数だけからなる singleton である。

列中の因子が全て2以上であることと、入力が非自明な積に分解できないことを使う。
従って、素数入力に余分な因子や重複因子が入らないことが仕様だけから従う。
-/
theorem FactorsCorrect.eq_singleton_of_prime {n : Nat} {factors : List Nat}
    (hCorrect : FactorsCorrect n factors)
    (hPrime : PrimeByMultiplication n) : factors = [n] := by
  have hProduct := FactorsCorrect.product_eq hCorrect hPrime.1
  cases factors with
  | nil =>
      simp at hProduct
      have hLower := hPrime.1
      omega
  | cons first rest =>
      have hFirstPrime := FactorsCorrect.factor_isPrimeByMultiplication
        (factor := first) hCorrect (by simp)
      have hFirstLower : 2 ≤ first := hFirstPrime.1
      have hSplit : n = first * rest.foldl Nat.mul 1 := by
        have hProductForm :
            (first :: rest).foldl Nat.mul 1 = first * rest.foldl Nat.mul 1 := by
          calc
            (first :: rest).foldl Nat.mul 1 = rest.foldl Nat.mul first := by
              change rest.foldl Nat.mul (1 * first) = _
              rw [Nat.one_mul]
            _ = first * rest.foldl Nat.mul 1 := foldl_mul_eq_mul_foldl rest first
        rw [hProductForm] at hProduct
        exact hProduct.symm
      rcases hPrime.2 first (rest.foldl Nat.mul 1) hSplit with hFirstOne | hRestOne
      · omega
      · have hRestProduct : rest.foldl Nat.mul 1 = 1 := hRestOne
        have hRestLower : ∀ value ∈ rest, 2 ≤ value := by
          intro value hValue
          exact FactorsCorrect.factor_ge_two hCorrect
            (List.mem_cons_of_mem first hValue)
        have hRestEmpty : rest = [] := by
          by_cases hEmpty : rest = []
          · exact hEmpty
          · have hAtLeastTwo := foldl_mul_one_ge_two rest hRestLower hEmpty
            rw [hRestProduct] at hAtLeastTwo
            omega
        subst rest
        simp [List.foldl] at hProduct
        simp [hProduct]

/-- 正しい因数列が singleton であることと、入力が素数であることは同値。 -/
theorem FactorsCorrect.length_eq_one_iff_prime {n : Nat} {factors : List Nat}
    (hCorrect : FactorsCorrect n factors) :
    factors.length = 1 ↔ PrimeByMultiplication n := by
  constructor
  · intro hLength
    cases factors with
    | nil => simp at hLength
    | cons factor rest =>
      cases rest with
      | nil =>
        have hInputLower : 2 ≤ n := by
          by_cases hLower : 2 ≤ n
          · exact hLower
          · have hSmall : n ≤ 1 := by omega
            simp [FactorsCorrect, hSmall] at hCorrect
        have hFactorPrime := FactorsCorrect.factor_isPrimeByMultiplication
          (factor := factor) hCorrect (by simp)
        have hProduct := FactorsCorrect.product_eq hCorrect hInputLower
        simp [List.foldl] at hProduct
        rw [← hProduct]
        exact hFactorPrime
      | cons second tail => simp at hLength
  · intro hPrime
    rw [FactorsCorrect.eq_singleton_of_prime hCorrect hPrime]
    rfl

/-- 0 から 20000 までの全整数を有限確認領域とする。 -/
def boundedInputs : List Nat := List.range 20001

/-- 各入力に対して、実装の結果が素因数分解仕様を満たすかを判定する。 -/
def boundedInputsCheck : Bool :=
  boundedInputs.all fun n =>
    decide (FactorsCorrect n (LeanExperiments.primeFactors n).toList)

/-- 0〜20000 の全入力について、積・順序・素数性の仕様を確認する。 -/
theorem boundedInputsCheck_passes : boundedInputsCheck = true := by
  native_decide

/-- 網羅確認した入力に対して素因数分解の仕様を取り出す。 -/
theorem primeFactors_correct_for_boundedInput (n : Nat)
    (hInput : n ∈ boundedInputs) :
    FactorsCorrect n (LeanExperiments.primeFactors n).toList := by
  have hAll : ∀ candidate ∈ boundedInputs,
      decide (FactorsCorrect candidate (LeanExperiments.primeFactors candidate).toList) = true :=
    List.all_eq_true.mp boundedInputsCheck_passes
  exact of_decide_eq_true (hAll n hInput)

/-! ## 平方根付近と大きな因子を持つ入力

小さな連続領域に加え、試し割りループが平方根境界に近づく入力や、残余が大きな
素数になる入力を個別に確認する。
-/

/-- 平方境界、大きな素数・半素数、重複因子、および64 bit境界前後を含む入力群。 -/
def boundaryInputs : List Nat :=
  [48, 49, 50, 120, 121, 122, 960, 961, 962,
    997, 1009, 1018080, 1018081, 1018082, 1022117, 1048576,
    100140048, 100140049, 100140050, 100160063,
    18446744073709551615, 18446744073709551616]

/-- 境界入力全てで積・順序・素数性の仕様を満たす。 -/
def boundaryInputsCheck : Bool :=
  boundaryInputs.all fun n =>
    decide (FactorsCorrect n (LeanExperiments.primeFactors n).toList)

/-- 平方根境界など22個の入力について素因数分解仕様を確認する。 -/
theorem boundaryInputsCheck_passes : boundaryInputsCheck = true := by
  native_decide

/-- 境界入力群に含まれる数について素因数分解仕様を取り出す。 -/
theorem primeFactors_correct_for_boundaryInput (n : Nat)
    (hInput : n ∈ boundaryInputs) :
    FactorsCorrect n (LeanExperiments.primeFactors n).toList := by
  have hAll : ∀ candidate ∈ boundaryInputs,
      decide (FactorsCorrect candidate (LeanExperiments.primeFactors candidate).toList) = true :=
    List.all_eq_true.mp boundaryInputsCheck_passes
  exact of_decide_eq_true (hAll n hInput)

/-- 1 以下の入力では試し割りループに入らず、空配列を返す。 -/
theorem primeFactors_eq_empty_of_le_one (n : Nat) (h : n ≤ 1) :
    LeanExperiments.primeFactors n = #[] := by
  unfold LeanExperiments.primeFactors
  simp [h]

/-- 1 以下の任意入力で、実装結果は因数分解仕様を満たす。 -/
theorem primeFactors_correct_of_le_one (n : Nat) (h : n ≤ 1) :
    FactorsCorrect n (LeanExperiments.primeFactors n).toList := by
  rw [primeFactors_eq_empty_of_le_one n h]
  simp [FactorsCorrect, h]

/-- 試し割り候補で割ったとき、残余から候補を引いた停止測度は減少する。 -/
theorem trialDivision_measure_decreases_of_division
    (remaining divisor : Nat)
    (hLower : 2 ≤ divisor)
    (hCandidate : divisor * divisor ≤ remaining) :
    remaining / divisor - divisor < remaining - divisor := by
  have hDivisorPositive : 0 < divisor := by omega
  have hQuotientLower : divisor ≤ remaining / divisor :=
    (Nat.le_div_iff_mul_le hDivisorPositive).2 hCandidate
  have hDivisorLtRemaining : divisor < remaining := by nlinarith
  have hRemainingPositive : 0 < remaining := by nlinarith
  have hQuotientLt : remaining / divisor < remaining :=
    Nat.div_lt_self hRemainingPositive (by omega)
  exact Nat.sub_lt_sub_right hQuotientLower hQuotientLt

/-- 割り切れない候補を1増やすときも、試し割りループの停止測度は減少する。 -/
theorem trialDivision_measure_decreases_of_increment
    (remaining divisor : Nat)
    (hLower : 2 ≤ divisor)
    (hCandidate : divisor * divisor ≤ remaining) :
    remaining - (divisor + 1) < remaining - divisor := by
  have hDivisorLtRemaining : divisor < remaining := by nlinarith
  exact Nat.sub_lt_sub_left hDivisorLtRemaining (by omega)

/-- 候補で割り切れるとき、除算後に候補を掛け戻すと残余に戻る。 -/
theorem trialDivision_mul_div_eq_of_mod_eq_zero {remaining divisor : Nat}
    (hMod : remaining % divisor = 0) :
    divisor * (remaining / divisor) = remaining := by
  have h := Nat.mod_add_div remaining divisor
  rw [hMod] at h
  omega

/-- 割り切れる候補で除した商の約数は、除算前の残余も割り切る。 -/
private theorem dvd_of_dvd_division_of_mod_eq_zero {remaining divisor candidate : Nat}
    (hMod : remaining % divisor = 0)
    (hDvd : candidate ∣ remaining / divisor) : candidate ∣ remaining := by
  have hProduct : candidate ∣ (remaining / divisor) * divisor :=
    dvd_mul_of_dvd_left hDvd divisor
  have hProductEq : (remaining / divisor) * divisor = remaining := by
    calc
      (remaining / divisor) * divisor = divisor * (remaining / divisor) :=
        Nat.mul_comm _ _
      _ = remaining := trialDivision_mul_div_eq_of_mod_eq_zero hMod
  rw [hProductEq] at hProduct
  exact hProduct

/-- 候補が残余を割り、より小さい約数がないなら、その候補は素数である。 -/
private theorem trialDivision_candidate_prime {remaining divisor : Nat}
    (hLower : 2 ≤ divisor)
    (hNoSmaller : ∀ candidate, 2 ≤ candidate → candidate < divisor →
      ¬ candidate ∣ remaining)
    (hMod : remaining % divisor = 0) : Nat.Prime divisor := by
  apply Nat.prime_def_lt'.2
  refine ⟨hLower, ?_⟩
  intro candidate hCandidateLower hCandidateUpper hCandidateDvd
  have hDivisorDvd : divisor ∣ remaining := Nat.dvd_iff_mod_eq_zero.mpr hMod
  exact hNoSmaller candidate hCandidateLower hCandidateUpper
    (hCandidateDvd.trans hDivisorDvd)

/-- 配列内の因子の積を、ループ契約で使う形に定める。 -/
def factorProduct (factors : Array Nat) : Nat :=
  factors.toList.foldl Nat.mul 1

/-- 因子を末尾に追加すると、因子積にその値が掛けられる。 -/
theorem factorProduct_push (factors : Array Nat) (factor : Nat) :
    factorProduct (factors.push factor) = factorProduct factors * factor := by
  simp [factorProduct, Array.toList_push, List.foldl_append]

/-- 因子配列に含まれる値は、配列全体の積を割り切る。 -/
theorem factor_dvd_factorProduct_of_mem (factors : Array Nat) (factor : Nat)
    (hFactor : factor ∈ factors.toList) :
    factor ∣ factorProduct factors := by
  change factor ∣ factors.toList.foldl Nat.mul 1
  have hDvdProduct : factor ∣ factors.toList.prod := List.dvd_prod hFactor
  rw [List.prod_eq_foldl_nat] at hDvdProduct
  exact hDvdProduct

set_option maxHeartbeats 1000000

/-- 試し割りループは因子積と残余の積、候補の下限を任意の入力で保つ。 -/
theorem trialDivisionLoop_product_invariant (n : Nat) :
    let (remaining, divisor, factors) := LeanExperiments.trialDivisionLoop n
    factorProduct factors * remaining = n ∧ 2 ≤ divisor ∧
      ∀ factor, factor ∈ factors.toList → 2 ≤ factor := by
  generalize hRun : LeanExperiments.trialDivisionLoop n = result
  apply Id.of_run_eq_wp hRun
  vcgen [LeanExperiments.trialDivisionLoop] invariants
  case inv1 => exact fun _ state =>
    factorProduct state.2.2 * state.1 = n ∧ 2 ≤ state.2.1 ∧
      ∀ factor, factor ∈ state.2.2.toList → 2 ≤ factor
  case vc1 => simp [factorProduct, factors]
  case vc2 => simp_all
  case vc3 =>
    simp_all [Variant.evalsBelow_ofMeasure_nat, Variant.evalsTo_ofMeasure,
      Assertion.NondetFun.evalsTo_pure]
    rcases ‹_ ∧ _› with ⟨hMeasure, hInvariant⟩
    constructor
    · rw [← hMeasure]
      simpa [remaining] using
        trialDivision_measure_decreases_of_division _ _ hInvariant.2.1 ‹_›
    · constructor
      · have hDivision := trialDivision_mul_div_eq_of_mod_eq_zero (by assumption)
        change factorProduct factors * remaining = n
        rw [factorProduct_push]
        rw [Nat.mul_assoc, hDivision]
        exact hInvariant.1
      · intro factor hFactor
        rcases Array.mem_push.mp (by simpa [factors] using hFactor) with hOld | hNew
        · exact hInvariant.2.2 factor hOld
        · omega
  case vc4 =>
    simp_all [Variant.evalsBelow_ofMeasure_nat, Variant.evalsTo_ofMeasure,
      Assertion.NondetFun.evalsTo_pure]
    rcases ‹_ ∧ _› with ⟨hMeasure, hInvariant⟩
    rw [← hMeasure]
    constructor
    · exact trialDivision_measure_decreases_of_increment _ _ hInvariant.2.1 ‹_›
    · dsimp [divisor]
      omega
  case vc5 => simp_all

/-- 試し割りループは出力因子の順序と、候補・残余の大小関係を保つ。 -/
theorem trialDivisionLoop_order_invariant (n : Nat) :
    let (remaining, divisor, factors) := LeanExperiments.trialDivisionLoop n
    factors.toList.Pairwise (· ≤ ·) ∧
      (∀ factor, factor ∈ factors → factor ≤ divisor) ∧
      (2 ≤ n → divisor ≤ remaining) := by
  generalize hRun : LeanExperiments.trialDivisionLoop n = result
  apply Id.of_run_eq_wp hRun
  vcgen [LeanExperiments.trialDivisionLoop] invariants
  case inv1 => exact fun _ state =>
    state.2.2.toList.Pairwise (· ≤ ·) ∧ 2 ≤ state.2.1 ∧
      (∀ factor, factor ∈ state.2.2 → factor ≤ state.2.1) ∧
      (2 ≤ n → state.2.1 ≤ state.1)
  case vc1 => simp [factors]
  case vc2 => simp_all
  case vc3 =>
    simp_all [Variant.evalsBelow_ofMeasure_nat, Variant.evalsTo_ofMeasure,
      Assertion.NondetFun.evalsTo_pure]
    rcases ‹_ ∧ _› with ⟨hMeasure, hInvariant⟩
    constructor
    · rw [← hMeasure]
      simpa [remaining] using
        trialDivision_measure_decreases_of_division _ _ hInvariant.2.1 ‹_›
    · constructor
      · rw [Array.toList_push, List.pairwise_append]
        refine ⟨hInvariant.1, by simp, ?_⟩
        intro earlier hEarlier later hLater
        simp at hLater
        subst later
        exact hInvariant.2.2.1 earlier (Array.mem_toList_iff.mp hEarlier)
      · constructor
        · intro factor hFactor
          rcases Array.mem_push.mp hFactor with hOld | hNew
          · exact hInvariant.2.2.1 factor hOld
          · omega
        · intro hN
          exact (Nat.le_div_iff_mul_le (by omega)).2 ‹_›
  case vc4 =>
    simp_all [Variant.evalsBelow_ofMeasure_nat, Variant.evalsTo_ofMeasure,
      Assertion.NondetFun.evalsTo_pure]
    rcases ‹_ ∧ _› with ⟨hMeasure, hInvariant⟩
    rw [← hMeasure]
    constructor
    · exact trialDivision_measure_decreases_of_increment _ _ hInvariant.2.1 ‹_›
    · constructor
      · dsimp [divisor]
        omega
      · constructor
        · intro factor hFactor
          have hOld := hInvariant.2.2.1 factor hFactor
          dsimp [divisor]
          omega
        · intro hN
          dsimp [divisor]
          nlinarith [hInvariant.2.1]
  case vc5 => simp_all

/-- 試し割りで候補を進める間、それ未満の2以上の数は残余を割らない。 -/
theorem trialDivisionLoop_no_smaller_divisor (n : Nat) :
    let (remaining, divisor, factors) := LeanExperiments.trialDivisionLoop n
    (∀ candidate, 2 ≤ candidate → candidate < divisor → ¬ candidate ∣ remaining) ∧
      (∀ factor, factor ∈ factors → Nat.Prime factor) ∧
      divisor * divisor > remaining := by
  generalize hRun : LeanExperiments.trialDivisionLoop n = result
  apply Id.of_run_eq_wp hRun
  vcgen [LeanExperiments.trialDivisionLoop] invariants
  case inv1 => exact fun exit state =>
    (2 ≤ state.2.1 ∧
      (∀ candidate, 2 ≤ candidate → candidate < state.2.1 → ¬ candidate ∣ state.1) ∧
      (∀ factor, factor ∈ state.2.2 → Nat.Prime factor)) ∧
      (exit = true → state.2.1 * state.2.1 > state.1)
  case vc1 =>
    change (2 ≤ 2 ∧ (∀ candidate, 2 ≤ candidate → candidate < 2 → ¬ candidate ∣ n) ∧
      (∀ factor, factor ∈ (#[] : Array Nat) → Nat.Prime factor)) ∧
      (false = true → 2 * 2 > n)
    exact ⟨⟨by omega, ⟨by intro candidate hLower hUpper; omega, by simp⟩⟩, by simp⟩
  case vc2 => simp_all
  case vc3 =>
    simp_all [Variant.evalsBelow_ofMeasure_nat, Variant.evalsTo_ofMeasure,
      Assertion.NondetFun.evalsTo_pure]
    rcases ‹_ ∧ _› with ⟨hMeasure, hInvariant⟩
    constructor
    · rw [← hMeasure]
      simpa [remaining] using
        trialDivision_measure_decreases_of_division _ _ hInvariant.1 ‹_›
    · constructor
      · intro candidate hCandidateLower hCandidateUpper hCandidateDvd
        exact (hInvariant.2.1 candidate hCandidateLower hCandidateUpper)
          (dvd_of_dvd_division_of_mod_eq_zero ‹_› hCandidateDvd)
      · intro factor hFactor
        rcases Array.mem_push.mp hFactor with hOld | hNew
        · exact hInvariant.2.2 factor hOld
        · subst factor
          exact trialDivision_candidate_prime hInvariant.1 hInvariant.2.1 ‹_›
  case vc4 =>
    simp_all [Variant.evalsBelow_ofMeasure_nat, Variant.evalsTo_ofMeasure,
      Assertion.NondetFun.evalsTo_pure]
    rcases ‹_ ∧ _› with ⟨hMeasure, hInvariant⟩
    constructor
    · rw [← hMeasure]
      exact trialDivision_measure_decreases_of_increment _ _ hInvariant.1 ‹_›
    · constructor
      · dsimp [divisor]
        omega
      · intro candidate hCandidateLower hCandidateUpper hCandidateDvd
        dsimp [divisor] at hCandidateUpper
        by_cases hOldUpper : candidate < divisor - 1
        · exact hInvariant.2.1 candidate hCandidateLower (by omega) hCandidateDvd
        · have hCandidateEq : candidate = divisor - 1 := by omega
          subst candidate
          apply ‹¬_ % _ = 0›
          exact Nat.dvd_iff_mod_eq_zero.mp (by simpa [divisor] using hCandidateDvd)
  case vc5 => simp_all

/-- 試し割りループが配列へ追加した全ての因子は素数である。 -/
theorem trialDivisionLoop_emitted_factors_prime (n : Nat) :
    let (_, _, factors) := LeanExperiments.trialDivisionLoop n
    ∀ factor, factor ∈ factors → Nat.Prime factor := by
  exact (trialDivisionLoop_no_smaller_divisor n).2.1

/-- 試し割りループの停止時は、候補の平方が残余を超えている。 -/
theorem trialDivisionLoop_stops_when_candidate_square_exceeds_remainder (n : Nat) :
    let (remaining, divisor, _) := LeanExperiments.trialDivisionLoop n
    divisor * divisor > remaining := by
  exact (trialDivisionLoop_no_smaller_divisor n).2.2

/-- 1より大きい入力に対し、ループ終了後に残る値は素数である。 -/
theorem trialDivisionLoop_remainder_prime_of_gt_one (n : Nat) :
    (LeanExperiments.trialDivisionLoop n).1 > 1 →
      Nat.Prime (LeanExperiments.trialDivisionLoop n).1 := by
  generalize hRun : LeanExperiments.trialDivisionLoop n = result
  rcases result with ⟨remaining, divisor, factors⟩
  have hNoSmaller := (trialDivisionLoop_no_smaller_divisor n).1
  change (∀ candidate, 2 ≤ candidate → candidate <
    (LeanExperiments.trialDivisionLoop n).2.1 →
    ¬ candidate ∣ (LeanExperiments.trialDivisionLoop n).1) at hNoSmaller
  rw [hRun] at hNoSmaller
  have hStop := trialDivisionLoop_stops_when_candidate_square_exceeds_remainder n
  change (LeanExperiments.trialDivisionLoop n).2.1 *
    (LeanExperiments.trialDivisionLoop n).2.1 >
    (LeanExperiments.trialDivisionLoop n).1 at hStop
  rw [hRun] at hStop
  intro hRemaining
  by_contra hNotPrime
  have hPositive : 0 < remaining := by omega
  have hMinFacSquare := Nat.minFac_sq_le_self hPositive hNotPrime
  have hMinFacPrime := Nat.minFac_prime (by omega : remaining ≠ 1)
  have hMinFacLower : 2 ≤ Nat.minFac remaining := hMinFacPrime.two_le
  have hMinFacDvd : Nat.minFac remaining ∣ remaining := Nat.minFac_dvd _
  have hMinFacLt : Nat.minFac remaining < divisor := by
    by_contra hNotLt
    have hDivisorLeMinFac : divisor ≤ Nat.minFac remaining := by omega
    have hSquareLe : divisor * divisor ≤ Nat.minFac remaining * Nat.minFac remaining :=
      Nat.mul_le_mul hDivisorLeMinFac hDivisorLeMinFac
    nlinarith [hStop, hMinFacSquare, hSquareLe]
  exact hNoSmaller _ hMinFacLower hMinFacLt hMinFacDvd

/-- ループ後の残余が1以下か素数なら、返却配列の全因子が素数である。 -/
theorem primeFactors_all_prime_of_remainder_prime (n : Nat) (hN : 2 ≤ n)
    (hR : (LeanExperiments.trialDivisionLoop n).1 ≤ 1 ∨
      Nat.Prime (LeanExperiments.trialDivisionLoop n).1) :
    ∀ factor, factor ∈ LeanExperiments.primeFactors n → Nat.Prime factor := by
  generalize hRun : LeanExperiments.trialDivisionLoop n = result
  rcases result with ⟨remaining, divisor, factors⟩
  have hLoopPrime : ∀ factor, factor ∈ factors → Nat.Prime factor := by
    have h := trialDivisionLoop_emitted_factors_prime n
    rw [hRun] at h
    exact h
  have hRemainderPrime : remaining ≤ 1 ∨ Nat.Prime remaining := by
    simpa [hRun] using hR
  have hNotSmall : ¬ n ≤ 1 := by omega
  unfold LeanExperiments.primeFactors
  simp only [ite_eq_right hNotSmall, hRun]
  intro factor hFactor
  by_cases hRemaining : remaining > 1
  · have hPrime : Nat.Prime remaining := hRemainderPrime.resolve_left (by omega)
    rcases Array.mem_push.mp (by simpa [hRemaining] using hFactor) with hOld | hNew
    · exact hLoopPrime factor hOld
    · subst factor
      exact hPrime
  · exact hLoopPrime factor (by simpa [hRemaining] using hFactor)

/-- 2以上の入力では、実装が返す因子配列の積は元の入力に等しい。 -/
theorem primeFactors_product_of_two_le (n : Nat) (hN : 2 ≤ n) :
    factorProduct (LeanExperiments.primeFactors n) = n := by
  generalize hRun : LeanExperiments.trialDivisionLoop n = result
  rcases result with ⟨remaining, divisor, factors⟩
  have hInvariant : factorProduct factors * remaining = n := by
    have h := trialDivisionLoop_product_invariant n
    rw [hRun] at h
    exact h.1
  have hNotSmall : ¬ n ≤ 1 := by omega
  unfold LeanExperiments.primeFactors
  simp only [ite_eq_right hNotSmall, hRun]
  by_cases hRemaining : remaining > 1
  · simp [hRemaining, factorProduct_push]
    omega
  · have hRemainingEq : remaining = 1 := by
      have hRemainingPositive : 0 < remaining := by
        by_contra hNotPositive
        have hZero : remaining = 0 := by omega
        rw [hZero] at hInvariant
        simp at hInvariant
        omega
      omega
    simpa [hRemaining, hRemainingEq] using hInvariant

/-- 2以上の入力では、実装が返す全ての因子は2以上である。 -/
theorem primeFactors_factors_ge_two_of_two_le (n : Nat) (hN : 2 ≤ n) :
    ∀ factor, factor ∈ LeanExperiments.primeFactors n → 2 ≤ factor := by
  generalize hRun : LeanExperiments.trialDivisionLoop n = result
  rcases result with ⟨remaining, divisor, factors⟩
  have hLoop := trialDivisionLoop_product_invariant n
  rw [hRun] at hLoop
  have hFactors : ∀ factor, factor ∈ factors → 2 ≤ factor := by
    intro factor hFactor
    exact hLoop.2.2 factor (Array.mem_toList_iff.mpr hFactor)
  have hNotSmall : ¬ n ≤ 1 := by omega
  unfold LeanExperiments.primeFactors
  simp only [ite_eq_right hNotSmall, hRun]
  by_cases hRemaining : remaining > 1
  · intro factor hFactor
    rcases Array.mem_push.mp (by simpa [hRemaining] using hFactor) with hOld | hNew
    · exact hFactors factor hOld
    · omega
  · intro factor hFactor
    exact hFactors factor (by simpa [hRemaining] using hFactor)

/-- 2以上の入力では、返却された各因子が入力を割り切る。 -/
theorem primeFactors_dvd_of_mem_of_two_le (n factor : Nat) (hN : 2 ≤ n)
    (hFactor : factor ∈ LeanExperiments.primeFactors n) :
    factor ∣ n := by
  have hProduct := primeFactors_product_of_two_le n hN
  have hFactorProduct : factor ∣ factorProduct (LeanExperiments.primeFactors n) :=
    factor_dvd_factorProduct_of_mem _ factor (Array.mem_toList_iff.mpr hFactor)
  rw [hProduct] at hFactorProduct
  exact hFactorProduct

/-- 2以上の入力では、各返却因子は2以上で、入力を割り切り、入力以下である。 -/
theorem primeFactors_factor_bounds_and_dvd_of_two_le (n : Nat) (hN : 2 ≤ n) :
    ∀ factor, factor ∈ LeanExperiments.primeFactors n →
      2 ≤ factor ∧ factor ∣ n ∧ factor ≤ n := by
  intro factor hFactor
  have hLower := primeFactors_factors_ge_two_of_two_le n hN factor hFactor
  have hDvd := primeFactors_dvd_of_mem_of_two_le n factor hN hFactor
  exact ⟨hLower, hDvd, Nat.le_of_dvd (by omega) hDvd⟩

/-- 2以上の入力では、実装が返す因子列は昇順である。 -/
theorem primeFactors_ascending_of_two_le (n : Nat) (hN : 2 ≤ n) :
    ascendingCheck (LeanExperiments.primeFactors n).toList = true := by
  generalize hRun : LeanExperiments.trialDivisionLoop n = result
  rcases result with ⟨remaining, divisor, factors⟩
  have hOrder := trialDivisionLoop_order_invariant n
  rw [hRun] at hOrder
  have hNotSmall : ¬ n ≤ 1 := by omega
  unfold LeanExperiments.primeFactors
  simp only [ite_eq_right hNotSmall, hRun]
  have hOutputPairwise :
      (if remaining > 1 then factors.push remaining else factors).toList.Pairwise
        (· ≤ ·) := by
    by_cases hRemaining : remaining > 1
    · simp only [hRemaining, ite_true]
      rw [Array.toList_push, List.pairwise_append]
      refine ⟨hOrder.1, by simp, ?_⟩
      intro earlier hEarlier later hLater
      simp at hLater
      subst later
      exact Nat.le_trans
        (hOrder.2.1 earlier (Array.mem_toList_iff.mp hEarlier))
        (hOrder.2.2 hN)
    · simpa [hRemaining] using hOrder.1
  exact ascendingCheck_eq_true_of_pairwise hOutputPairwise

/-- 残余が1以下か素数なら、実装結果は独立した因数分解仕様を満たす。 -/
theorem primeFactors_correct_of_remainder_prime (n : Nat) (hN : 2 ≤ n)
    (hR : (LeanExperiments.trialDivisionLoop n).1 ≤ 1 ∨
      Nat.Prime (LeanExperiments.trialDivisionLoop n).1) :
    FactorsCorrect n (LeanExperiments.primeFactors n).toList := by
  have hNotSmall : ¬ n ≤ 1 := by omega
  simp only [FactorsCorrect, ite_eq_right hNotSmall]
  refine ⟨?_, primeFactors_ascending_of_two_le n hN, ?_⟩
  · change factorProduct (LeanExperiments.primeFactors n) = n
    exact primeFactors_product_of_two_le n hN
  · apply List.all_eq_true.mpr
    intro factor hFactor
    have hPrime := primeFactors_all_prime_of_remainder_prime n hN hR factor
      (Array.mem_toList_iff.mp hFactor)
    exact natPrime_to_isPrime hPrime

/-- 2以上の任意の入力で、試し割りの結果は完全な因数分解仕様を満たす。 -/
theorem primeFactors_correct_of_two_le (n : Nat) (hN : 2 ≤ n) :
    FactorsCorrect n (LeanExperiments.primeFactors n).toList := by
  apply primeFactors_correct_of_remainder_prime n hN
  by_cases hSmallRemainder : (LeanExperiments.trialDivisionLoop n).1 ≤ 1
  · exact Or.inl hSmallRemainder
  · right
    have hGreater : 1 < (LeanExperiments.trialDivisionLoop n).1 :=
      Nat.lt_of_not_ge hSmallRemainder
    exact trialDivisionLoop_remainder_prime_of_gt_one n hGreater

/-- 任意の自然数で、試し割りの結果は独立した因数分解仕様を満たす。 -/
theorem primeFactors_correct (n : Nat) :
    FactorsCorrect n (LeanExperiments.primeFactors n).toList := by
  by_cases hSmall : n ≤ 1
  · exact primeFactors_correct_of_le_one n hSmall
  · exact primeFactors_correct_of_two_le n (by omega)

/-- 実装の因数列は、Mathlib の標準素因数列と任意の入力で一致する。

独立仕様 `FactorsCorrect` の一意性と、Mathlib の `primeFactorsList` が同仕様を満たす
ことを組み合わせる。0 と 1 も含め、空因数列の規約まで一致する。 -/
theorem primeFactors_toList_eq_primeFactorsList (n : Nat) :
    (LeanExperiments.primeFactors n).toList = n.primeFactorsList := by
  exact FactorsCorrect.eq_primeFactorsList (primeFactors_correct n)

/-- 非零二入力の積を分解すると、両入力の因数列を併合ソートした列になる。

各実装出力が独立仕様を満たすことを、仕様の乗算閉包と一意性で合成する。0を除外するのは
0の因数列が空であり、通常の素因数重複度の加法則が成り立たないため。 -/
theorem primeFactors_mul_toList_eq_mergeSort (n m : Nat)
    (hN : n ≠ 0) (hM : m ≠ 0) :
    (LeanExperiments.primeFactors (n * m)).toList =
      ((LeanExperiments.primeFactors n).toList ++
        (LeanExperiments.primeFactors m).toList).mergeSort (· ≤ ·) := by
  exact FactorsCorrect.eq_of_same_input
    (primeFactors_correct (n * m))
    (FactorsCorrect.mul_mergeSort (primeFactors_correct n)
      (primeFactors_correct m) hN hM)

/-- 非零二入力の積では、任意の値の因数重複度が二つの出力での個数の和になる。

素数以外の値も含めた `count` の加法則であり、因数列の並び替えに依存しない。
-/
theorem primeFactors_mul_count_eq_add (n m factor : Nat)
    (hN : n ≠ 0) (hM : m ≠ 0) :
    (LeanExperiments.primeFactors (n * m)).toList.count factor =
      (LeanExperiments.primeFactors n).toList.count factor +
        (LeanExperiments.primeFactors m).toList.count factor := by
  calc
    (LeanExperiments.primeFactors (n * m)).toList.count factor =
        (n * m).factorization factor :=
      FactorsCorrect.count_eq_factorization (primeFactors_correct (n * m)) factor
    _ = n.factorization factor + m.factorization factor := by
      rw [Nat.factorization_mul hN hM]
      simp
    _ = (LeanExperiments.primeFactors n).toList.count factor +
        (LeanExperiments.primeFactors m).toList.count factor := by
      rw [← FactorsCorrect.count_eq_factorization (primeFactors_correct n) factor,
        ← FactorsCorrect.count_eq_factorization (primeFactors_correct m) factor]

/-- 全入力について、最大公約数の因数重複度を0の規約を含めて特徴付ける。

両入力が非零なら重複度の小さい方をとる。片方が0なら最大公約数はもう片方であり、
両方が0ならこの仕様の空因数列に従って重複度は0となる。
-/
theorem primeFactors_gcd_count_eq (n m factor : Nat) :
    (LeanExperiments.primeFactors (Nat.gcd n m)).toList.count factor =
      if n = 0 then
        if m = 0 then 0 else (LeanExperiments.primeFactors m).toList.count factor
      else if m = 0 then (LeanExperiments.primeFactors n).toList.count factor
      else min ((LeanExperiments.primeFactors n).toList.count factor)
        ((LeanExperiments.primeFactors m).toList.count factor) := by
  by_cases hN : n = 0
  · subst n
    by_cases hM : m = 0
    · subst m
      simp [primeFactors_eq_empty_of_le_one]
    · simp [hM]
  · by_cases hM : m = 0
    · subst m
      simp [hN]
    · simpa [hN, hM] using FactorsCorrect.gcd_count_eq_min
        (primeFactors_correct n) (primeFactors_correct m)
        (primeFactors_correct (Nat.gcd n m)) hN hM factor

/-- 非零二入力の最大公約数では、任意の値の因数重複度が二入力の小さい方になる。

重複度の最小値をとることで、実装が返す最大公約数の素因数列を各入力の列から特徴付ける。
0 は空因数列を持つこの仕様では通常の指数最小則に含められないため、両入力を非零とする。
-/
theorem primeFactors_gcd_count_eq_min (n m factor : Nat)
    (hN : n ≠ 0) (hM : m ≠ 0) :
    (LeanExperiments.primeFactors (Nat.gcd n m)).toList.count factor =
      min ((LeanExperiments.primeFactors n).toList.count factor)
        ((LeanExperiments.primeFactors m).toList.count factor) := by
  exact FactorsCorrect.gcd_count_eq_min
    (primeFactors_correct n) (primeFactors_correct m)
    (primeFactors_correct (Nat.gcd n m)) hN hM factor

/-- 全入力について、最小公倍数の因数重複度を0の規約を含めて特徴付ける。

両入力が非零なら重複度の大きい方をとる。一方でも0なら最小公倍数は0で、仕様上の
空因数列に従って重複度は0となる。
-/
theorem primeFactors_lcm_count_eq (n m factor : Nat) :
    (LeanExperiments.primeFactors (Nat.lcm n m)).toList.count factor =
      if n = 0 ∨ m = 0 then 0 else
        max ((LeanExperiments.primeFactors n).toList.count factor)
          ((LeanExperiments.primeFactors m).toList.count factor) := by
  by_cases hN : n = 0
  · subst n
    simp [primeFactors_eq_empty_of_le_one]
  · by_cases hM : m = 0
    · subst m
      simp [hN, primeFactors_eq_empty_of_le_one]
    · simpa [hN, hM] using FactorsCorrect.lcm_count_eq_max
        (primeFactors_correct n) (primeFactors_correct m)
        (primeFactors_correct (Nat.lcm n m)) hN hM factor

/-- 非零二入力の最小公倍数では、任意の値の因数重複度が二入力の大きい方になる。

重複度の最大値をとることで、実装が返す最小公倍数の素因数列を各入力の列から特徴付ける。
0 は空因数列を持つこの仕様では通常の指数最大則に含められないため、両入力を非零とする。
-/
theorem primeFactors_lcm_count_eq_max (n m factor : Nat)
    (hN : n ≠ 0) (hM : m ≠ 0) :
    (LeanExperiments.primeFactors (Nat.lcm n m)).toList.count factor =
      max ((LeanExperiments.primeFactors n).toList.count factor)
        ((LeanExperiments.primeFactors m).toList.count factor) := by
  exact FactorsCorrect.lcm_count_eq_max
    (primeFactors_correct n) (primeFactors_correct m)
    (primeFactors_correct (Nat.lcm n m)) hN hM factor

/-- 任意入力のべきの因数列は、入力の因数列を指数回併合した列になる。

非零入力では抽象仕様のべき乗閉包と一意性を使う。0では任意のべきの結果が0または1で、
どちらも仕様上の空因数列となるため、別に境界ケースを閉じる。
-/
theorem primeFactors_pow_toList_eq_factorsPower (n exponent : Nat) :
    (LeanExperiments.primeFactors (n ^ exponent)).toList =
      factorsPower (LeanExperiments.primeFactors n).toList exponent := by
  by_cases hN : n = 0
  · subst n
    have hEmptyZero : (LeanExperiments.primeFactors 0).toList = [] := by
      simp [primeFactors_eq_empty_of_le_one 0 (by omega)]
    have hEmptyPower : ∀ k, factorsPower [] k = [] := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih => simp [factorsPower, ih]
    cases exponent with
    | zero => simpa [hEmptyZero, primeFactors_eq_empty_of_le_one 1 (by omega)] using
        (hEmptyPower 0)
    | succ exponent => simpa [hEmptyZero,
        primeFactors_eq_empty_of_le_one 0 (by omega)] using
        (hEmptyPower (exponent + 1))
  · exact FactorsCorrect.eq_of_same_input
      (primeFactors_correct (n ^ exponent))
      (FactorsCorrect.pow_mergeSort (primeFactors_correct n) hN exponent)

/-- 任意入力のべきでは、各値の素因数重複度が指数倍になる。

素数かどうかを別途仮定せず、因数列中の任意の自然数の個数について成り立つ。
-/
theorem primeFactors_pow_count_eq_mul (n exponent factor : Nat) :
    (LeanExperiments.primeFactors (n ^ exponent)).toList.count factor =
      exponent * (LeanExperiments.primeFactors n).toList.count factor := by
  by_cases hN : n = 0
  · subst n
    cases exponent with
    | zero => simp [primeFactors_eq_empty_of_le_one]
    | succ exponent => simp [primeFactors_eq_empty_of_le_one]
  · rw [primeFactors_pow_toList_eq_factorsPower n exponent]
    exact FactorsCorrect.pow_count_eq_mul (primeFactors_correct n) hN exponent factor

/-- 因数分解実装の出力は、入力が等しいか両方1以下のときに限り一致する。

0と1の出力はいずれも空配列であり、それ以外では正しい因数列の積から入力が復元できる。
-/
theorem primeFactors_eq_iff_input_eq_or_both_le_one (n m : Nat) :
    LeanExperiments.primeFactors n = LeanExperiments.primeFactors m ↔
      n = m ∨ (n ≤ 1 ∧ m ≤ 1) := by
  constructor
  · intro hOutput
    have hFactors := congrArg Array.toList hOutput
    exact (FactorsCorrect.eq_iff_input_eq_or_both_le_one
      (primeFactors_correct n) (primeFactors_correct m)).mp hFactors
  · intro hInput
    apply Array.toList_inj.mp
    exact (FactorsCorrect.eq_iff_input_eq_or_both_le_one
      (primeFactors_correct n) (primeFactors_correct m)).mpr hInput

/-- 任意の入力で、返却された各因子は素数で、入力を割り切り、入力以下である。
1以下では返却列が空なので、各因子についての条件は空虚に成立する。 -/
theorem primeFactors_factor_prime_dvd_le (n : Nat) :
    ∀ factor, factor ∈ LeanExperiments.primeFactors n →
      Nat.Prime factor ∧ factor ∣ n ∧ factor ≤ n := by
  intro factor hFactor
  have hCorrect := primeFactors_correct n
  have hMember : factor ∈ (LeanExperiments.primeFactors n).toList :=
    Array.mem_toList_iff.mpr hFactor
  have hPrimeByMul :=
    FactorsCorrect.factor_isPrimeByMultiplication hCorrect hMember
  have hPrime : Nat.Prime factor := primeByMultiplication_to_natPrime hPrimeByMul
  have hDvd := FactorsCorrect.factor_dvd_input hCorrect hMember
  have hLe := FactorsCorrect.factor_le_input hCorrect hMember
  exact ⟨hPrime, hDvd, hLe⟩

/-- 実装が返す各値の重複数は、その値の `Nat.factorization` 指数に一致する。
素数でない値についても両辺が0となるため、任意の自然数 `factor` に適用できる。 -/
theorem primeFactors_count_eq_factorization (n factor : Nat) :
    (LeanExperiments.primeFactors n).toList.count factor = n.factorization factor := by
  exact FactorsCorrect.count_eq_factorization (primeFactors_correct n) factor

/-- 任意の入力で、実装結果が空配列であることと入力が1以下であることは同値である。 -/
theorem primeFactors_eq_empty_iff_le_one (n : Nat) :
    LeanExperiments.primeFactors n = #[] ↔ n ≤ 1 := by
  constructor
  · intro hEmpty
    have hCorrect := primeFactors_correct n
    rw [hEmpty] at hCorrect
    exact (FactorsCorrect.isEmpty_iff_le_one hCorrect).mp rfl
  · exact primeFactors_eq_empty_of_le_one n

/-- 非零入力では、素数の `exponent` 乗が入力を割ることと、実装結果にその素数が
`exponent` 回以上含まれることは同値である。 -/
theorem primeFactors_prime_pow_dvd_iff_count_ge {n prime exponent : Nat}
    (hNonzero : n ≠ 0) (hPrime : Nat.Prime prime) :
    prime ^ exponent ∣ n ↔
      exponent ≤ (LeanExperiments.primeFactors n).toList.count prime := by
  exact FactorsCorrect.prime_pow_dvd_iff_count_ge
    (primeFactors_correct n) hNonzero hPrime

/-- 非零入力では、任意の非零約数が入力を割ることと、その素因数指数が実装結果中の
各素数の個数以下であることは同値である。 -/
theorem primeFactors_dvd_iff_factorization_le_counts {n divisor : Nat}
    (hNonzero : n ≠ 0) (hDivisorNonzero : divisor ≠ 0) :
    divisor ∣ n ↔ ∀ prime,
      divisor.factorization prime ≤ (LeanExperiments.primeFactors n).toList.count prime := by
  exact FactorsCorrect.dvd_iff_factorization_le_counts
    (primeFactors_correct n) hNonzero hDivisorNonzero

/-- 非零入力が平方因子を持たないことと、実装結果に重複因子がないことは同値である。 -/
theorem primeFactors_squarefree_iff_nodup (n : Nat) (hNonzero : n ≠ 0) :
    Squarefree n ↔ (LeanExperiments.primeFactors n).toList.Nodup := by
  exact FactorsCorrect.squarefree_iff_nodup (primeFactors_correct n) hNonzero

/-- 入力が正の指数のべきであることと、返却された各素数の重複数が指数で割り切れることは
同値である。 -/
theorem primeFactors_isPower_iff_count_dvd (n exponent : Nat)
    (hExponent : 0 < exponent) :
    (∃ base, n = base ^ exponent) ↔ ∀ prime, Nat.Prime prime →
      exponent ∣ (LeanExperiments.primeFactors n).toList.count prime := by
  exact FactorsCorrect.isPower_iff_count_dvd (primeFactors_correct n) hExponent

/-- 0 はこのプロジェクトの仕様では素因数を持たない。一般境界定理の系。 -/
theorem primeFactors_zero_boundary : LeanExperiments.primeFactors 0 = #[] :=
  primeFactors_eq_empty_of_le_one 0 (by omega)

/-- 1 はこのプロジェクトの仕様では素因数を持たない。一般境界定理の系。 -/
theorem primeFactors_one_boundary : LeanExperiments.primeFactors 1 = #[] :=
  primeFactors_eq_empty_of_le_one 1 (by omega)

/-- 最小の素数 2 は、自分自身だけを因数として返す。 -/
theorem primeFactors_two_example : LeanExperiments.primeFactors 2 = #[2] := by
  native_decide

/-- 12 を重複込みで `2 * 2 * 3` と分解する。 -/
theorem primeFactors_twelve_example :
    LeanExperiments.primeFactors 12 = #[2, 2, 3] := by
  native_decide

/-- 複数の重複因子を持つ 360 を昇順に分解する。 -/
theorem primeFactors_threeHundredSixty_example :
    LeanExperiments.primeFactors 360 = #[2, 2, 2, 3, 3, 5] := by
  native_decide

/-- 試し割りの探索で素数 97 自身が残る場合を確認する。 -/
theorem primeFactors_ninetySeven_example :
    LeanExperiments.primeFactors 97 = #[97] := by
  native_decide

/-- 大きな素数平方では、平方根の境界で同じ因子を2回返す。 -/
theorem primeFactors_largePrimeSquare_example :
    LeanExperiments.primeFactors 1000006000009 = #[1000003, 1000003] := by
  native_decide

/-- 約10^12の大きな素数平方も、積・順序・素数性の仕様を満たす。 -/
theorem primeFactors_largePrimeSquare_correct_example :
    FactorsCorrect 1000006000009
      (LeanExperiments.primeFactors 1000006000009).toList := by
  native_decide

/-- 約100万の素数は、試し割りの終了後に残余素数として返す。 -/
theorem primeFactors_largePrime_example :
    LeanExperiments.primeFactors 1000003 = #[1000003] := by
  native_decide

/-- 約100万の残余素数も、素因数分解の完全な仕様を満たす。 -/
theorem primeFactors_largePrime_correct_example :
    FactorsCorrect 1000003 (LeanExperiments.primeFactors 1000003).toList := by
  native_decide

/-- 最大64 bit値を7つの素因数へ分解する。 -/
theorem primeFactors_uint64Max_example :
    LeanExperiments.primeFactors 18446744073709551615 =
      #[3, 5, 17, 257, 641, 65537, 6700417] := by
  native_decide

/-- 最大64 bit値の具体例も積・昇順性・素数性の仕様を満たす。 -/
theorem primeFactors_uint64Max_correct_example :
    FactorsCorrect 18446744073709551615
      (LeanExperiments.primeFactors 18446744073709551615).toList := by
  native_decide

/-- 64 bit最大値の直後 `2^64` は、素因数2を64個返す。 -/
theorem primeFactors_twoPowSixtyFour_example :
    LeanExperiments.primeFactors 18446744073709551616 = Array.replicate 64 2 := by
  native_decide

/-- `2^64` の64個の重複因子も完全な素因数分解仕様を満たす。 -/
theorem primeFactors_twoPowSixtyFour_correct_example :
    FactorsCorrect 18446744073709551616
      (LeanExperiments.primeFactors 18446744073709551616).toList := by
  native_decide

/-- 64 bitを超える `2^128` も、素因数2を128個返す。 -/
theorem primeFactors_twoPowOneTwentyEight_example :
    LeanExperiments.primeFactors (2 ^ 128) = Array.replicate 128 2 := by
  native_decide

/-- `2^128` の128個の重複因子も完全な素因数分解仕様を満たす。 -/
theorem primeFactors_twoPowOneTwentyEight_correct_example :
    FactorsCorrect (2 ^ 128)
      (LeanExperiments.primeFactors (2 ^ 128)).toList := by
  native_decide

/-- さらに大きな `2^256` も、素因数2を256個返す。 -/
theorem primeFactors_twoPowTwoFiftySix_example :
    LeanExperiments.primeFactors (2 ^ 256) = Array.replicate 256 2 := by
  native_decide

/-- `2^256` の256個の重複因子も完全な素因数分解仕様を満たす。 -/
theorem primeFactors_twoPowTwoFiftySix_correct_example :
    FactorsCorrect (2 ^ 256)
      (LeanExperiments.primeFactors (2 ^ 256)).toList := by
  native_decide

end LeanExperiments.Verification.PrimeFactors
