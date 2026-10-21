import LeanExperiments.Verification.MergeSort.Spec
import LeanExperiments.Verification.QuickSort.Spec

/-!
# ソート実装間の一般的な比較

共通仕様を満たす昇順結果は一意であることを使い、再帰版 merge sort と
再帰版 quick sort の一致、および整列済み入力に対する不変性を示す。
-/

namespace LeanExperiments.Verification.Sorting.Comparisons

open LeanExperiments.Verification.Sorting.Spec

/-- 同じ入力に対する二つのBoolean検査が成功すれば、その出力は一致する。

ソート実装ごとの比較を個別に再証明せず、共通の検査器の成功だけから
実装間の出力一致を導ける。
-/
theorem correctCheck_outputs_eq (input output₁ output₂ : List Nat)
    (h₁ : correctCheck input output₁ = true)
    (h₂ : correctCheck input output₂ = true) :
    output₁ = output₂ := by
  exact Correct.eq_of_same_input
    (correctCheck_sound input output₁ h₁)
    (correctCheck_sound input output₂ h₂)

/-- 検査に通った二つの出力は、入力が順列であることと同値に一致する。

共通検査器が昇順性と要素保存を確認するため、出力の一致から入力の多重集合の一致も
逆向きに取り出せる。
-/
theorem correctCheck_outputs_eq_iff_inputs_perm
    (input₁ output₁ input₂ output₂ : List Nat)
    (h₁ : correctCheck input₁ output₁ = true)
    (h₂ : correctCheck input₂ output₂ = true) :
    input₁.Perm input₂ ↔ output₁ = output₂ := by
  exact Correct.perm_iff_eq_output
    (correctCheck_sound input₁ output₁ h₁)
    (correctCheck_sound input₂ output₂ h₂)

/-- 任意入力で共通のソート仕様を満たす関数は、入力が昇順のときに限り入力を変えない。

ソート結果は同じ入力に対して一意であるため、すでに昇順の入力自身も唯一の正しい結果に
なる。逆に、ソート結果が入力そのものなら、その結果の昇順性から入力も昇順と分かる。
-/
theorem correctSort_eq_self_iff_ascending
    (sort : List Nat → List Nat)
    (hCorrect : ∀ input, Correct input (sort input))
    (input : List Nat) :
    sort input = input ↔ Ascending input := by
  constructor
  · intro hSame
    simpa [hSame] using (hCorrect input).1
  · intro hAscending
    exact Correct.eq_of_same_input (hCorrect input)
      ⟨hAscending, List.Perm.refl input⟩

/-- 共通ソート仕様を満たす関数を二度適用しても、二度目の結果は変わらない。

一度目の結果は昇順であり、入力の要素を保つ。したがって一度目の結果自身が、
その値を再びソートする際の正しい候補となり、正しい結果の一意性から冪等性が従う。
-/
theorem correctSort_idempotent
    (sort : List Nat → List Nat)
    (hCorrect : ∀ input, Correct input (sort input))
    (input : List Nat) :
    sort (sort input) = sort input := by
  exact Correct.eq_of_same_input (hCorrect (sort input))
    ⟨(hCorrect input).1, List.Perm.refl _⟩

/-- 再帰版 merge sort は、入力が昇順であることと入力をそのまま返すことが同値。 -/
theorem mergeSort_eq_self_iff_ascending (input : List Nat) :
    LeanExperiments.MergeSort.mergeSort input = input ↔ Ascending input :=
  correctSort_eq_self_iff_ascending LeanExperiments.MergeSort.mergeSort
    LeanExperiments.Verification.MergeSort.mergeSort_correct input

/-- 再帰版 quick sort も、入力が昇順であることと入力をそのまま返すことが同値。 -/
theorem quickSort_eq_self_iff_ascending (input : List Nat) :
    LeanExperiments.QuickSort.quickSort input = input ↔ Ascending input :=
  correctSort_eq_self_iff_ascending LeanExperiments.QuickSort.quickSort
    LeanExperiments.Verification.QuickSort.quickSort_correct input

/-- ループ版 quick sort と merge sort の検査が成功すれば、出力は必ず一致する。 -/
theorem quickSortIterative_eq_mergeSortIterative_of_checks (input : List Nat)
    (hQuick : correctCheck input (LeanExperiments.QuickSort.quickSortIterative input) = true)
    (hMerge : correctCheck input (LeanExperiments.MergeSort.mergeSortIterative input) = true) :
    LeanExperiments.QuickSort.quickSortIterative input =
      LeanExperiments.MergeSort.mergeSortIterative input :=
  correctCheck_outputs_eq input _ _ hQuick hMerge

/-- 再帰版 merge sort と再帰版 quick sort は任意の入力で同じ列を返す。 -/
theorem recursiveMergeAndQuickSort_agree (input : List Nat) :
    LeanExperiments.MergeSort.mergeSort input =
      LeanExperiments.QuickSort.quickSort input := by
  exact Correct.eq_of_same_input
    (LeanExperiments.Verification.MergeSort.mergeSort_correct input)
    (LeanExperiments.Verification.QuickSort.quickSort_correct input)

/-- 同じ要素を同じ個数だけ含む入力なら、merge sort の結果は入力順によらない。 -/
theorem mergeSort_eq_of_perm {input₁ input₂ : List Nat}
    (hInputs : input₁.Perm input₂) :
    LeanExperiments.MergeSort.mergeSort input₁ =
      LeanExperiments.MergeSort.mergeSort input₂ := by
  exact Correct.eq_of_perm_inputs
    (LeanExperiments.Verification.MergeSort.mergeSort_correct input₁)
    (LeanExperiments.Verification.MergeSort.mergeSort_correct input₂)
    hInputs

/-- 同じ要素を同じ個数だけ含む入力なら、quick sort の結果は入力順によらない。 -/
theorem quickSort_eq_of_perm {input₁ input₂ : List Nat}
    (hInputs : input₁.Perm input₂) :
    LeanExperiments.QuickSort.quickSort input₁ =
      LeanExperiments.QuickSort.quickSort input₂ := by
  exact Correct.eq_of_perm_inputs
    (LeanExperiments.Verification.QuickSort.quickSort_correct input₁)
    (LeanExperiments.Verification.QuickSort.quickSort_correct input₂)
    hInputs

/-- merge sort の結果が一致するのは、入力が同じ多重集合を表すときに限る。 -/
theorem mergeSort_eq_iff_perm_inputs {input₁ input₂ : List Nat} :
    LeanExperiments.MergeSort.mergeSort input₁ =
      LeanExperiments.MergeSort.mergeSort input₂ ↔ input₁.Perm input₂ := by
  exact (Correct.perm_iff_eq_output
    (LeanExperiments.Verification.MergeSort.mergeSort_correct input₁)
    (LeanExperiments.Verification.MergeSort.mergeSort_correct input₂)).symm

/-- quick sort の結果が一致するのは、入力が同じ多重集合を表すときに限る。 -/
theorem quickSort_eq_iff_perm_inputs {input₁ input₂ : List Nat} :
    LeanExperiments.QuickSort.quickSort input₁ =
      LeanExperiments.QuickSort.quickSort input₂ ↔ input₁.Perm input₂ := by
  exact (Correct.perm_iff_eq_output
    (LeanExperiments.Verification.QuickSort.quickSort_correct input₁)
    (LeanExperiments.Verification.QuickSort.quickSort_correct input₂)).symm

/-- 再帰版 merge sort は、任意の非空入力の最小値を先頭へ移す。 -/
theorem mergeSort_has_minimum (input : List Nat) (hInput : input ≠ []) :
    ∃ minimum, minimum ∈ input ∧ ∀ value ∈ input, minimum ≤ value := by
  exact Correct.exists_minimum
    (LeanExperiments.Verification.MergeSort.mergeSort_correct input) hInput

/-- 再帰版 quick sort も、任意の非空入力の最小値を先頭へ移す。 -/
theorem quickSort_has_minimum (input : List Nat) (hInput : input ≠ []) :
    ∃ minimum, minimum ∈ input ∧ ∀ value ∈ input, minimum ≤ value := by
  exact Correct.exists_minimum
    (LeanExperiments.Verification.QuickSort.quickSort_correct input) hInput

/-- 再帰版 merge sort は、任意の非空入力の最大値も保持する。 -/
theorem mergeSort_has_maximum (input : List Nat) (hInput : input ≠ []) :
    ∃ maximum, maximum ∈ input ∧ ∀ value ∈ input, value ≤ maximum := by
  exact Correct.exists_maximum
    (LeanExperiments.Verification.MergeSort.mergeSort_correct input) hInput

/-- 再帰版 quick sort も、任意の非空入力の最大値を保持する。 -/
theorem quickSort_has_maximum (input : List Nat) (hInput : input ≠ []) :
    ∃ maximum, maximum ∈ input ∧ ∀ value ∈ input, value ≤ maximum := by
  exact Correct.exists_maximum
    (LeanExperiments.Verification.QuickSort.quickSort_correct input) hInput

/-- 再帰版 merge sort は入力の最大値を出力末尾に置く。 -/
theorem mergeSort_last_is_maximum (input : List Nat) (hInput : input ≠ []) :
    ∃ initSegment maximum,
      LeanExperiments.MergeSort.mergeSort input = initSegment ++ [maximum] ∧
      maximum ∈ input ∧ ∀ value ∈ input, value ≤ maximum := by
  exact Correct.last_is_maximum
    (LeanExperiments.Verification.MergeSort.mergeSort_correct input) hInput

/-- 再帰版 quick sort も入力の最大値を出力末尾に置く。 -/
theorem quickSort_last_is_maximum (input : List Nat) (hInput : input ≠ []) :
    ∃ initSegment maximum,
      LeanExperiments.QuickSort.quickSort input = initSegment ++ [maximum] ∧
      maximum ∈ input ∧ ∀ value ∈ input, value ≤ maximum := by
  exact Correct.last_is_maximum
    (LeanExperiments.Verification.QuickSort.quickSort_correct input) hInput

/-- 再帰版 merge sort は要素数を保つ。 -/
theorem mergeSort_preserves_length (input : List Nat) :
    (LeanExperiments.MergeSort.mergeSort input).length = input.length := by
  exact Correct.length_eq (LeanExperiments.Verification.MergeSort.mergeSort_correct input)

/-- 再帰版 merge sort は要素総和を保つ。 -/
theorem mergeSort_preserves_sum (input : List Nat) :
    (LeanExperiments.MergeSort.mergeSort input).sum = input.sum := by
  exact Correct.sum_eq (LeanExperiments.Verification.MergeSort.mergeSort_correct input)

/-- 再帰版 quick sort は要素数を保つ。 -/
theorem quickSort_preserves_length (input : List Nat) :
    (LeanExperiments.QuickSort.quickSort input).length = input.length := by
  exact Correct.length_eq (LeanExperiments.Verification.QuickSort.quickSort_correct input)

/-- 再帰版 quick sort は要素総和を保つ。 -/
theorem quickSort_preserves_sum (input : List Nat) :
    (LeanExperiments.QuickSort.quickSort input).sum = input.sum := by
  exact Correct.sum_eq (LeanExperiments.Verification.QuickSort.quickSort_correct input)

/-- 再帰版 merge sort は、任意の値の出現回数を保つ。 -/
theorem mergeSort_preserves_count (input : List Nat) (value : Nat) :
    (LeanExperiments.MergeSort.mergeSort input).count value = input.count value := by
  exact Correct.count_eq
    (LeanExperiments.Verification.MergeSort.mergeSort_correct input) value

/-- 再帰版 quick sort は、任意の値の出現回数を保つ。 -/
theorem quickSort_preserves_count (input : List Nat) (value : Nat) :
    (LeanExperiments.QuickSort.quickSort input).count value = input.count value := by
  exact Correct.count_eq
    (LeanExperiments.Verification.QuickSort.quickSort_correct input) value

/-- 再帰版 merge sort は冪等であり、結果を再度ソートしても変化しない。 -/
theorem mergeSort_idempotent (input : List Nat) :
    LeanExperiments.MergeSort.mergeSort (LeanExperiments.MergeSort.mergeSort input) =
      LeanExperiments.MergeSort.mergeSort input := by
  exact correctSort_idempotent LeanExperiments.MergeSort.mergeSort
    LeanExperiments.Verification.MergeSort.mergeSort_correct input

/-- 再帰版 quick sort も冪等であり、結果を再度ソートしても変化しない。 -/
theorem quickSort_idempotent (input : List Nat) :
    LeanExperiments.QuickSort.quickSort (LeanExperiments.QuickSort.quickSort input) =
      LeanExperiments.QuickSort.quickSort input := by
  exact correctSort_idempotent LeanExperiments.QuickSort.quickSort
    LeanExperiments.Verification.QuickSort.quickSort_correct input

/-- 再帰版 merge sort は、すでに昇順の入力を変更しない。 -/
theorem mergeSort_of_ascending (input : List Nat) (hSorted : Ascending input) :
    LeanExperiments.MergeSort.mergeSort input = input := by
  exact Correct.eq_of_same_input
    (LeanExperiments.Verification.MergeSort.mergeSort_correct input)
    ⟨hSorted, List.Perm.refl input⟩

/-- 再帰版 quick sort は、すでに昇順の入力を変更しない。 -/
theorem quickSort_of_ascending (input : List Nat) (hSorted : Ascending input) :
    LeanExperiments.QuickSort.quickSort input = input := by
  exact Correct.eq_of_same_input
    (LeanExperiments.Verification.QuickSort.quickSort_correct input)
    ⟨hSorted, List.Perm.refl input⟩

/-- ループ版 merge sort が入力をそのまま返すことと、入力の昇順性は同値。 -/
theorem mergeSortIterative_eq_self_iff_ascending (input : List Nat) :
    LeanExperiments.MergeSort.mergeSortIterative input = input ↔ Ascending input :=
  correctSort_eq_self_iff_ascending LeanExperiments.MergeSort.mergeSortIterative
    LeanExperiments.Verification.MergeSort.mergeSortIterative_correct input

/-- ループ版 merge sort の出力は、入力の順列だけで決まる。 -/
theorem mergeSortIterative_eq_iff_perm_inputs {input₁ input₂ : List Nat} :
    LeanExperiments.MergeSort.mergeSortIterative input₁ =
      LeanExperiments.MergeSort.mergeSortIterative input₂ ↔ input₁.Perm input₂ := by
  exact (Correct.perm_iff_eq_output
    (LeanExperiments.Verification.MergeSort.mergeSortIterative_correct input₁)
    (LeanExperiments.Verification.MergeSort.mergeSortIterative_correct input₂)).symm

/-- ループ版 merge sort は、任意の非空入力の最小値を先頭へ移す。 -/
theorem mergeSortIterative_has_minimum (input : List Nat) (hInput : input ≠ []) :
    ∃ minimum, minimum ∈ input ∧ ∀ value ∈ input, minimum ≤ value := by
  exact Correct.exists_minimum
    (LeanExperiments.Verification.MergeSort.mergeSortIterative_correct input) hInput

/-- ループ版 merge sort は、任意の非空入力の最大値も保持する。 -/
theorem mergeSortIterative_has_maximum (input : List Nat) (hInput : input ≠ []) :
    ∃ maximum, maximum ∈ input ∧ ∀ value ∈ input, value ≤ maximum := by
  exact Correct.exists_maximum
    (LeanExperiments.Verification.MergeSort.mergeSortIterative_correct input) hInput

/-- ループ版 merge sort は入力の最大値を出力末尾に置く。 -/
theorem mergeSortIterative_last_is_maximum (input : List Nat) (hInput : input ≠ []) :
    ∃ initSegment maximum,
      LeanExperiments.MergeSort.mergeSortIterative input = initSegment ++ [maximum] ∧
      maximum ∈ input ∧ ∀ value ∈ input, value ≤ maximum := by
  exact Correct.last_is_maximum
    (LeanExperiments.Verification.MergeSort.mergeSortIterative_correct input) hInput

/-- ループ版 merge sort は要素数を保つ。 -/
theorem mergeSortIterative_preserves_length (input : List Nat) :
    (LeanExperiments.MergeSort.mergeSortIterative input).length = input.length := by
  exact Correct.length_eq
    (LeanExperiments.Verification.MergeSort.mergeSortIterative_correct input)

/-- ループ版 merge sort は要素総和を保つ。 -/
theorem mergeSortIterative_preserves_sum (input : List Nat) :
    (LeanExperiments.MergeSort.mergeSortIterative input).sum = input.sum := by
  exact Correct.sum_eq
    (LeanExperiments.Verification.MergeSort.mergeSortIterative_correct input)

/-- ループ版 merge sort は、任意の値の出現回数を保つ。 -/
theorem mergeSortIterative_preserves_count (input : List Nat) (value : Nat) :
    (LeanExperiments.MergeSort.mergeSortIterative input).count value = input.count value := by
  exact Correct.count_eq
    (LeanExperiments.Verification.MergeSort.mergeSortIterative_correct input) value

/-- ループ版 merge sort は、任意の Boolean 条件を満たす要素数を保つ。 -/
theorem mergeSortIterative_preserves_countP (input : List Nat) (predicate : Nat → Bool) :
    (LeanExperiments.MergeSort.mergeSortIterative input).countP predicate =
      input.countP predicate := by
  exact Correct.countP_eq
    (LeanExperiments.Verification.MergeSort.mergeSortIterative_correct input) predicate

/-- ループ版 merge sort の各位置の値は、入力における同じ順位の順序統計量である。 -/
theorem mergeSortIterative_rank_bounds (input : List Nat) {index : Nat}
    (hIndex : index < (LeanExperiments.MergeSort.mergeSortIterative input).length) :
    input.countP (fun value => decide
      (value < (LeanExperiments.MergeSort.mergeSortIterative input)[index])) ≤ index ∧
      index < input.countP (fun value => decide
        (value ≤ (LeanExperiments.MergeSort.mergeSortIterative input)[index])) := by
  exact Correct.getElem_rank_bounds
    (LeanExperiments.Verification.MergeSort.mergeSortIterative_correct input) hIndex

end LeanExperiments.Verification.Sorting.Comparisons
