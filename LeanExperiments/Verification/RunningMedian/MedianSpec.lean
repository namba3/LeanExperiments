import LeanExperiments.Verification.MergeSort.Spec
import LeanExperiments.Verification.Sorting.Spec

/-! # 逐次中央値の独立したソート基準仕様

入力をソートした列から中央値の分子・分母を定める参照仕様と、その順列不変性・
値変換則などを置く。逐次処理の実装状態には依存しない。 -/

namespace LeanExperiments.Verification.RunningMedian

/-- ソートした入力の中央値を、分子・分母の組で定義した参照仕様。 -/
def medianSpec (values : Array Nat) : Option (Nat × Nat) :=
  let sorted := (LeanExperiments.MergeSort.mergeSort values.toList).toArray
  match sorted.size with
  | 0 => none
  | n + 1 =>
      if n % 2 == 0 then
        some (sorted[n / 2]!, 1)
      else
        some (sorted[n / 2]! + sorted[n / 2 + 1]!, 2)

/-- ソート基準の中央値仕様が未定義となるのは、入力が空の場合に限る。 -/
theorem medianSpec_none_iff_empty (values : Array Nat) :
    medianSpec values = none ↔ values = #[] := by
  have hSortedSize :
      (LeanExperiments.MergeSort.mergeSort values.toList).toArray.size = values.size := by
    simpa using
      (LeanExperiments.Verification.MergeSort.mergeSort_correct values.toList).2.length_eq
  constructor
  · intro hNone
    dsimp only [medianSpec] at hNone
    rw [hSortedSize] at hNone
    cases hSize : values.size with
    | zero => exact Array.size_eq_zero_iff.mp hSize
    | succ n =>
      simp only [hSize] at hNone
      split at hNone <;> simp at hNone
  · intro hEmpty
    have hSize : values.size = 0 := by rw [hEmpty]; rfl
    dsimp only [medianSpec]
    rw [hSortedSize, hSize]

/-- 1要素入力の参照中央値は、その唯一の値を分母1で返す。 -/
theorem medianSpec_singleton (value : Nat) :
    medianSpec #[value] = some (value, 1) := by
  have hSorted : LeanExperiments.MergeSort.mergeSort [value] = [value] :=
    LeanExperiments.Verification.Sorting.Spec.Correct.eq_of_same_input
      (LeanExperiments.Verification.MergeSort.mergeSort_correct [value])
      ⟨by simp [LeanExperiments.Verification.Sorting.Spec.Ascending],
        List.Perm.refl _⟩
  simp [medianSpec, hSorted]

/-- 任意の二値入力の参照中央値は、その二値の和を分母2で表す。

値の大小と重複を場合分けし、中央値仕様がソート結果の一意性から導かれることを示す。
-/
theorem medianSpec_pair (left right : Nat) :
    medianSpec #[left, right] = some (left + right, 2) := by
  by_cases h : left ≤ right
  · have hSorted : LeanExperiments.MergeSort.mergeSort [left, right] = [left, right] :=
      LeanExperiments.Verification.Sorting.Spec.Correct.eq_of_same_input
        (LeanExperiments.Verification.MergeSort.mergeSort_correct [left, right])
        ⟨by simp [LeanExperiments.Verification.Sorting.Spec.Ascending, h],
          List.Perm.refl _⟩
    simp [medianSpec, hSorted]
  · have hRightLeft : right ≤ left := by omega
    have hSorted : LeanExperiments.MergeSort.mergeSort [left, right] = [right, left] :=
      LeanExperiments.Verification.Sorting.Spec.Correct.eq_of_same_input
        (LeanExperiments.Verification.MergeSort.mergeSort_correct [left, right])
        ⟨by simp [LeanExperiments.Verification.Sorting.Spec.Ascending, hRightLeft],
          (List.Perm.swap _ _ _).symm⟩
    simp [medianSpec, hSorted, Nat.add_comm]

/-- 中央値仕様の分母は、奇数長なら1、偶数長なら2になる。

任意の値・長さについて、結果が存在すると仮定すれば入力長の偶奇と分母が一致する。
-/
theorem medianSpec_denominator_parity {values : Array Nat} {numerator denominator : Nat}
    (hResult : medianSpec values = some (numerator, denominator)) :
    (values.size % 2 = 1 ∧ denominator = 1) ∨
      (values.size % 2 = 0 ∧ denominator = 2) := by
  have hSortedSize :
      (LeanExperiments.MergeSort.mergeSort values.toList).toArray.size = values.size := by
    simpa using
      (LeanExperiments.Verification.MergeSort.mergeSort_correct values.toList).2.length_eq
  dsimp [medianSpec] at hResult
  rw [hSortedSize] at hResult
  cases hSize : values.size with
  | zero => simp [hSize] at hResult
  | succ n =>
      by_cases hParity : n % 2 = 0
      · simp [hSize, hParity] at hResult
        rcases hResult with ⟨_, rfl⟩
        left
        constructor <;> omega
      · simp [hSize, hParity] at hResult
        rcases hResult with ⟨_, rfl⟩
        right
        constructor <;> omega

/-- 入力全体を定数だけ平行移動すると、参照中央値も同じだけ移動する。

ソート結果への加算写像の可換性を共通 `Correct` 仕様から導き、奇数時の単一値と
偶数時の二値の和をそれぞれ計算する。 -/
theorem medianSpec_add_const (values : Array Nat) (offset : Nat) :
    medianSpec (values.map fun value => value + offset) =
      (medianSpec values).map fun result =>
        (result.1 + offset * result.2, result.2) := by
  let addOffset := fun value : Nat => value + offset
  have hSortedMap :
      LeanExperiments.MergeSort.mergeSort (values.toList.map addOffset) =
        (LeanExperiments.MergeSort.mergeSort values.toList).map addOffset :=
    LeanExperiments.Verification.Sorting.Spec.Correct.sort_map
      LeanExperiments.MergeSort.mergeSort
      LeanExperiments.Verification.MergeSort.mergeSort_correct
      values.toList addOffset (by
        intro left right h
        dsimp [addOffset]
        omega)
  have hSortedSize : (LeanExperiments.MergeSort.mergeSort values.toList).toArray.size =
      values.size := by
    simpa using
      (LeanExperiments.Verification.MergeSort.mergeSort_correct values.toList).2.length_eq
  have hSortedLength : (LeanExperiments.MergeSort.mergeSort values.toList).length =
      values.size := by simpa using hSortedSize
  cases hSize : values.size with
  | zero => simp [medianSpec, hSortedSize, hSortedMap, hSortedLength, hSize, addOffset]
  | succ n =>
      have hSortedLength' : (LeanExperiments.MergeSort.mergeSort values.toList).length = n + 1 := by
        rw [hSortedLength, hSize]
      have hMapOptionAt (index : Nat)
          (hIndex : index < (LeanExperiments.MergeSort.mergeSort values.toList).length) :
          (((LeanExperiments.MergeSort.mergeSort values.toList)[index]?).map addOffset).getD 0 =
            ((LeanExperiments.MergeSort.mergeSort values.toList)[index]?).getD 0 + offset := by
        rw [List.getElem?_eq_getElem hIndex]
        simp [addOffset]
      by_cases hParity : n % 2 = 0
      · have hIndex : n / 2 < (LeanExperiments.MergeSort.mergeSort values.toList).length := by
          rw [hSortedLength']
          omega
        simp [medianSpec, hSortedSize, hSortedMap, hSize, hParity,
          hSortedLength', addOffset]
        rw [hMapOptionAt (n / 2) hIndex]
      · have hIndex : n / 2 < (LeanExperiments.MergeSort.mergeSort values.toList).length := by
          rw [hSortedLength']
          omega
        have hNextIndex : n / 2 + 1 <
            (LeanExperiments.MergeSort.mergeSort values.toList).length := by
          rw [hSortedLength']
          omega
        simp [medianSpec, hSortedSize, hSortedMap, hSize, hParity,
          hSortedLength', addOffset]
        rw [hMapOptionAt (n / 2) hIndex, hMapOptionAt (n / 2 + 1) hNextIndex]
        omega

/-- 全入力値を同じ自然数倍すると、参照中央値の分子も同じ倍数になる。

係数0も含め、値域に制限を置かない。ソート結果への乗算写像の可換性を共通仕様から
導き、中央値を構成する添字で写像後の値を計算する。
-/
theorem medianSpec_mul_const (values : Array Nat) (factor : Nat) :
    medianSpec (values.map fun value => factor * value) =
      (medianSpec values).map fun result => (result.1 * factor, result.2) := by
  let scale := fun value : Nat => factor * value
  have hSortedMap :
      LeanExperiments.MergeSort.mergeSort (values.toList.map scale) =
        (LeanExperiments.MergeSort.mergeSort values.toList).map scale :=
    LeanExperiments.Verification.Sorting.Spec.Correct.sort_map
      LeanExperiments.MergeSort.mergeSort
      LeanExperiments.Verification.MergeSort.mergeSort_correct
      values.toList scale (by
        intro left right h
        exact Nat.mul_le_mul_left factor h)
  have hSortedSize : (LeanExperiments.MergeSort.mergeSort values.toList).toArray.size =
      values.size := by
    simpa using
      (LeanExperiments.Verification.MergeSort.mergeSort_correct values.toList).2.length_eq
  have hSortedLength : (LeanExperiments.MergeSort.mergeSort values.toList).length =
      values.size := by simpa using hSortedSize
  cases hSize : values.size with
  | zero => simp [medianSpec, hSortedSize, hSortedMap, hSortedLength, hSize, scale]
  | succ n =>
      have hSortedLength' : (LeanExperiments.MergeSort.mergeSort values.toList).length = n + 1 := by
        rw [hSortedLength, hSize]
      have hMapOptionAt (index : Nat)
          (hIndex : index < (LeanExperiments.MergeSort.mergeSort values.toList).length) :
          (((LeanExperiments.MergeSort.mergeSort values.toList)[index]?).map scale).getD 0 =
            ((LeanExperiments.MergeSort.mergeSort values.toList)[index]?).getD 0 * factor := by
        rw [List.getElem?_eq_getElem hIndex]
        simp [scale, Nat.mul_comm]
      by_cases hParity : n % 2 = 0
      · have hIndex : n / 2 < (LeanExperiments.MergeSort.mergeSort values.toList).length := by
          rw [hSortedLength']
          omega
        simp [medianSpec, hSortedSize, hSortedMap, hSize, hParity,
          hSortedLength', scale]
        rw [hMapOptionAt (n / 2) hIndex]
      · have hIndex : n / 2 < (LeanExperiments.MergeSort.mergeSort values.toList).length := by
          rw [hSortedLength']
          omega
        have hNextIndex : n / 2 + 1 <
            (LeanExperiments.MergeSort.mergeSort values.toList).length := by
          rw [hSortedLength']
          omega
        simp [medianSpec, hSortedSize, hSortedMap, hSize, hParity,
          hSortedLength', scale]
        rw [hMapOptionAt (n / 2) hIndex, hMapOptionAt (n / 2 + 1) hNextIndex]
        simp [Nat.mul_add, Nat.mul_comm]

/-- 参照仕様の中央値は入力の順列に依存しない。 -/
theorem medianSpec_eq_of_perm {values₁ values₂ : Array Nat}
    (hPerm : values₁.toList.Perm values₂.toList) :
    medianSpec values₁ = medianSpec values₂ := by
  have hSorted := LeanExperiments.Verification.Sorting.Spec.Correct.eq_of_perm_inputs
    (LeanExperiments.Verification.MergeSort.mergeSort_correct values₁.toList)
    (LeanExperiments.Verification.MergeSort.mergeSort_correct values₂.toList)
    hPerm
  unfold medianSpec
  rw [hSorted]


end LeanExperiments.Verification.RunningMedian
