import LeanExperiments.RunningMedian
import LeanExperiments.HeapSort
import LeanExperiments.Verification.MergeSort.Spec
import LeanExperiments.Verification.HeapSort.Spec
import Std.WP
import Std.Tactic.Do
import LeanExperiments.Verification.RunningMedian.Operations
import LeanExperiments.Verification.RunningMedian.MedianSpec
import LeanExperiments.Verification.RunningMedian.HeapInvariant
import LeanExperiments.Verification.RunningMedian.HeapOperations
import LeanExperiments.Verification.RunningMedian.StateInvariant

/-!
# 逐次中央値の仕様と有限領域検証

二つのヒープが保つ分割・順序・要素保存の条件を判定し、各入力の全ての接頭辞で
中央値を独立なソート基準と照合する。ここでの網羅確認は明示した有限領域に限られ、
任意の入力列に対する一般的な正しさ証明とは区別する。
-/

namespace LeanExperiments.Verification.RunningMedian

open Std.WP Lean.Order
set_option experimental.vcgen true

/-- 不変条件を満たす二つのヒープを個別にソートして連結すると、入力の正しいソート結果になる。 -/
private theorem sortedHeapParts_correct {input : Array Nat}
    {state : LeanExperiments.RunningMedian.State}
    (hInvariant : StateInvariant input state) :
    LeanExperiments.Verification.Sorting.Spec.Correct input.toList
      (LeanExperiments.MergeSort.mergeSort state.lower.toList ++
        LeanExperiments.MergeSort.mergeSort state.upper.toList) := by
  let lowerSorted := LeanExperiments.MergeSort.mergeSort state.lower.toList
  let upperSorted := LeanExperiments.MergeSort.mergeSort state.upper.toList
  have hLower := LeanExperiments.Verification.MergeSort.mergeSort_correct state.lower.toList
  have hUpper := LeanExperiments.Verification.MergeSort.mergeSort_correct state.upper.toList
  have hCross : ∀ lowerValue, lowerValue ∈ lowerSorted →
      ∀ upperValue, upperValue ∈ upperSorted → lowerValue ≤ upperValue := by
    intro lowerValue hLowerValue upperValue hUpperValue
    have hLowerValue : lowerValue ∈ state.lower.toList := hLower.2.mem_iff.mp hLowerValue
    have hUpperValue : upperValue ∈ state.upper.toList := hUpper.2.mem_iff.mp hUpperValue
    have hLowerArray : lowerValue ∈ state.lower := by simpa using hLowerValue
    have hUpperArray : upperValue ∈ state.upper := by simpa using hUpperValue
    obtain ⟨lowerIndex, hLowerIndex, hLowerAt⟩ := Array.mem_iff_getElem.mp hLowerArray
    obtain ⟨upperIndex, hUpperIndex, hUpperAt⟩ := Array.mem_iff_getElem.mp hUpperArray
    have hBoundary := hInvariant.2.2.2.1 lowerIndex hLowerIndex upperIndex hUpperIndex
    simpa [hLowerAt, hUpperAt] using hBoundary
  have hPairwise : (lowerSorted ++ upperSorted).Pairwise (fun a b : Nat => a ≤ b) := by
    apply List.pairwise_append.mpr
    exact ⟨LeanExperiments.Verification.Sorting.Spec.ascending_pairwise _ hLower.1,
      LeanExperiments.Verification.Sorting.Spec.ascending_pairwise _ hUpper.1,
      hCross⟩
  have hPerm : (lowerSorted ++ upperSorted).Perm input.toList := by
    dsimp [lowerSorted, upperSorted]
    exact (hLower.2.append hUpper.2).trans hInvariant.1
  exact ⟨LeanExperiments.Verification.Sorting.Spec.pairwise_ascending _ hPairwise, hPerm⟩

/-- 不変条件下で二つのヒープを個別に整列・連結した列は、入力のマージソート結果そのものである。 -/
theorem StateInvariant.sorted_parts_eq_mergeSort {input : Array Nat}
    {state : LeanExperiments.RunningMedian.State}
    (hInvariant : StateInvariant input state) :
    LeanExperiments.MergeSort.mergeSort state.lower.toList ++
      LeanExperiments.MergeSort.mergeSort state.upper.toList =
        LeanExperiments.MergeSort.mergeSort input.toList := by
  exact LeanExperiments.Verification.Sorting.Spec.Correct.eq_of_same_input
    (sortedHeapParts_correct hInvariant)
    (LeanExperiments.Verification.MergeSort.mergeSort_correct input.toList)

/-- 不変条件下で整列済みヒープを配列化した結果は、入力のマージソート配列と一致する。 -/
theorem StateInvariant.sorted_parts_toArray_eq_mergeSort {input : Array Nat}
    {state : LeanExperiments.RunningMedian.State}
    (hInvariant : StateInvariant input state) :
    (LeanExperiments.MergeSort.mergeSort state.lower.toList ++
      LeanExperiments.MergeSort.mergeSort state.upper.toList).toArray =
        (LeanExperiments.MergeSort.mergeSort input.toList).toArray := by
  exact congrArg List.toArray (StateInvariant.sorted_parts_eq_mergeSort hInvariant)

/-- 不変条件下では、下側ヒープの要素数は入力長の切り上げ半分に等しい。 -/
theorem lower_size_eq_ceil_half {input : Array Nat}
    {state : LeanExperiments.RunningMedian.State}
    (hInvariant : StateInvariant input state) :
    state.lower.size = (input.size + 1) / 2 := by
  exact (StateInvariant.heap_sizes hInvariant).1

/-- 不変条件下では、上側ヒープの要素数は入力長の切り捨て半分に等しい。 -/
theorem upper_size_eq_floor_half {input : Array Nat}
    {state : LeanExperiments.RunningMedian.State}
    (hInvariant : StateInvariant input state) :
    state.upper.size = input.size / 2 := by
  exact (StateInvariant.heap_sizes hInvariant).2

/-- 下側ヒープの根は、要素分割の条件により入力にも含まれる。 -/
theorem lower_root_mem_input {input : Array Nat}
    {state : LeanExperiments.RunningMedian.State}
    (hInvariant : StateInvariant input state) (hLower : 0 < state.lower.size) :
    state.lower[0]'(by omega) ∈ input.toList := by
  have hMem : state.lower[0]'(by omega) ∈ state.lower.toList :=
    Array.getElem_mem_toList (by omega)
  have hConcat : state.lower[0]'(by omega) ∈
      state.lower.toList ++ state.upper.toList := List.mem_append_left _ hMem
  exact hInvariant.1.mem_iff.mp hConcat

/-- 上側ヒープの根は、要素分割の条件により入力にも含まれる。 -/
theorem upper_root_mem_input {input : Array Nat}
    {state : LeanExperiments.RunningMedian.State}
    (hInvariant : StateInvariant input state) (hUpper : 0 < state.upper.size) :
    state.upper[0]'(by omega) ∈ input.toList := by
  have hMem : state.upper[0]'(by omega) ∈ state.upper.toList :=
    Array.getElem_mem_toList (by omega)
  have hConcat : state.upper[0]'(by omega) ∈
      state.lower.toList ++ state.upper.toList := List.mem_append_right _ hMem
  exact hInvariant.1.mem_iff.mp hConcat

/-- 不変条件を満たす0要素または1要素の状態に任意値を挿入すると、
更新後も要素保存・ヒープ順序・分割境界・サイズ均衡が保たれる。

サイズ1の場合は要素保存から状態中の唯一の値を特定し、長さ2までの一般契約へ
順列で接続する。これは任意長 `insert` 証明の基底遷移を、状態の表現形式に依存せず示す。
-/
theorem StateInvariant.insert_of_size_le_one {input : Array Nat}
    {state : LeanExperiments.RunningMedian.State}
    (hInvariant : StateInvariant input state) (hSize : input.size ≤ 1)
    (value : Nat) :
    StateInvariant (input.push value)
      (LeanExperiments.RunningMedian.insert state value) := by
  have hTotal := StateInvariant.size_partition hInvariant
  have hLowerFormula : state.lower.size = (input.size + 1) / 2 := by
    rcases hInvariant.2.2.2.2 with hBalanced | hLowerExtra <;> omega
  have hUpperFormula : state.upper.size = input.size / 2 := by
    rcases hInvariant.2.2.2.2 with hBalanced | hLowerExtra <;> omega
  by_cases hEmpty : input.size = 0
  · have hInput : input = #[] := Array.size_eq_zero_iff.mp hEmpty
    have hLowerEmpty : state.lower = #[] := by
      apply Array.size_eq_zero_iff.mp
      rw [hLowerFormula, hInput]
      decide
    have hUpperEmpty : state.upper = #[] := by
      apply Array.size_eq_zero_iff.mp
      rw [hUpperFormula, hInput]
      decide
    have hState : state = LeanExperiments.RunningMedian.empty := by
      cases state with
      | mk lower upper =>
        change lower = #[] at hLowerEmpty
        change upper = #[] at hUpperEmpty
        simp [LeanExperiments.RunningMedian.empty, hLowerEmpty, hUpperEmpty]
    subst input
    rw [hState]
    simpa using StateInvariant.insert_empty value
  · have hOne : input.size = 1 := by omega
    let root := state.lower[0]'(by rw [hLowerFormula, hOne]; decide)
    have hLowerSize : state.lower.size = 1 := by
      rw [hLowerFormula, hOne]
    have hUpperSize : state.upper.size = 0 := by
      rw [hUpperFormula, hOne]
    have hLower : state.lower = #[root] := by
      apply Array.ext
      · exact hLowerSize
      · intro index hLeft hRight
        have hIndex : index = 0 := by omega
        subst index
        simp [root]
    have hUpper : state.upper = #[] := Array.size_eq_zero_iff.mp hUpperSize
    have hState : state = { lower := #[root], upper := #[] } := by
      cases state with
      | mk lower upper =>
        change lower = #[root] at hLower
        change upper = #[] at hUpper
        simp [hLower, hUpper]
    have hPerm : (#[root]).toList.Perm input.toList := by
      simpa [hLower, hUpper] using hInvariant.1
    have hAppendPerm := hPerm.append_right [value]
    have hInputPushPerm : (#[root, value]).toList.Perm (input.push value).toList := by
      simpa using hAppendPerm
    rw [hState]
    exact StateInvariant.of_perm_input (StateInvariant.insert_singleton root value)
      hInputPushPerm

/-- 2つの単一要素ヒープを持つ不変状態で、下側の根以下の値を挿入しても
不変条件が保たれる。

この分岐では新しい値が下側の最大値を超えないため、最大ヒープへの挿入は末尾追加で
止まる。結果のサイズは2対1なので、再平衡ループはどちらも状態を変えない。
入力長2の逐次挿入証明で、値が下側へ振り分けられるケースを切り出した一般補題である。
-/
theorem StateInvariant.insert_from_two_singletons_of_le
    {input : Array Nat} {state : LeanExperiments.RunningMedian.State}
    (hInvariant : StateInvariant input state)
    {lowerRoot upperRoot value : Nat}
    (hState : state = { lower := #[lowerRoot], upper := #[upperRoot] })
    (hValue : value ≤ lowerRoot) :
    StateInvariant (input.push value)
      (LeanExperiments.RunningMedian.insert state value) := by
  rw [hState] at hInvariant ⊢
  have hHeapInsert :
      LeanExperiments.RunningMedian.insertHeap
          LeanExperiments.RunningMedian.maxPrefer #[lowerRoot] value =
        #[lowerRoot, value] := by
    apply insertHeap_eq_push_of_stops LeanExperiments.RunningMedian.maxPrefer
    right
    simp [LeanExperiments.RunningMedian.maxPrefer, hValue]
  have hResult :
      LeanExperiments.RunningMedian.insert
          { lower := #[lowerRoot], upper := #[upperRoot] } value =
        { lower := #[lowerRoot, value], upper := #[upperRoot] } := by
    simp [LeanExperiments.RunningMedian.insert, hValue]
    have hLowerBalanced :=
      rebalanceLower_eq_self_of_size_le #[lowerRoot, value] #[upperRoot] (by simp)
    have hUpperBalanced :=
      rebalanceUpper_eq_self_of_size_le #[lowerRoot, value] #[upperRoot] (by simp)
    simp [hHeapInsert, hLowerBalanced, hUpperBalanced]
  rw [hResult]
  have hRootBoundary := hInvariant.2.2.2.1 0 (by simp) 0 (by simp)
  have hPartition : ([lowerRoot, value, upperRoot]).Perm (input.push value).toList := by
    have hOriginal : ([lowerRoot, upperRoot]).Perm input.toList := by
      simpa using hInvariant.1
    have hAppend := hOriginal.append_right [value]
    have hReorder : ([lowerRoot, value, upperRoot]).Perm
        ([lowerRoot, upperRoot, value]) := by
      simpa using (List.Perm.refl [lowerRoot]).append
        (List.Perm.swap value upperRoot []).symm
    simpa using hReorder.trans hAppend
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa using hPartition
  · intro parent hParent
    have hParentBound : parent < 2 := by simpa using hParent
    have hParentCases : parent = 0 ∨ parent = 1 := by omega
    rcases hParentCases with hParentZero | hParentLeaf
    · subst parent
      constructor
      · intro hChild
        simpa [maxPrefer] using hValue
      · intro hChild
        simp at hChild
    · subst parent
      constructor <;> intro hChild <;> simp at hChild
  · intro parent hParent
    have hParentBound : parent < 1 := by simpa using hParent
    have hParentZero : parent = 0 := by omega
    subst parent
    constructor <;> intro hChild <;> simp at hChild
  · intro lowerIndex hLowerIndex upperIndex hUpperIndex
    have hLowerIndexCases : lowerIndex = 0 ∨ lowerIndex = 1 := by
      have hBound : lowerIndex < 2 := by simpa using hLowerIndex
      omega
    rcases hLowerIndexCases with hLowerIndexEq | hLowerIndexEq
    · subst lowerIndex
      have hUpperIndexEq : upperIndex = 0 := by simpa using hUpperIndex
      subst upperIndex
      simpa using hRootBoundary
    · subst lowerIndex
      have hUpperIndexEq : upperIndex = 0 := by simpa using hUpperIndex
      subst upperIndex
      exact Nat.le_trans hValue hRootBoundary
  · simp

/-- 下側の根より大きい値を二つの単一要素ヒープへ挿入しても不変条件を保つ。

新しい値と上側根の大小に応じて、再平衡で下側へ移る値が新値か既存根かに分かれる。
どちらの場合も任意のNat値に対する要素保存・ヒープ順序・分割境界・サイズ均衡を示す。
-/
theorem StateInvariant.insert_from_two_singletons_of_gt
    {input : Array Nat} {state : LeanExperiments.RunningMedian.State}
    (hInvariant : StateInvariant input state)
    {lowerRoot upperRoot value : Nat}
    (hState : state = { lower := #[lowerRoot], upper := #[upperRoot] })
    (hValue : lowerRoot < value) :
    StateInvariant (input.push value)
      (LeanExperiments.RunningMedian.insert state value) := by
  rw [hState] at hInvariant ⊢
  have hRootBoundary : lowerRoot ≤ upperRoot := by
    simpa using hInvariant.2.2.2.1 0 (by simp) 0 (by simp)
  have hOriginal : ([lowerRoot, upperRoot]).Perm input.toList := by
    simpa using hInvariant.1
  have hAppend := hOriginal.append_right [value]
  have hOutputInvariant (larger smaller upper : Nat)
      (hSmall : smaller ≤ larger) (hUpper : larger ≤ upper)
      (hPartition : ([larger, smaller, upper]).Perm (input.push value).toList) :
      StateInvariant (input.push value)
        { lower := #[larger, smaller], upper := #[upper] } := by
    refine ⟨hPartition, ?_, ?_, ?_, by simp⟩
    · intro parent hParent
      have hParentBound : parent < 2 := by simpa using hParent
      have hCases : parent = 0 ∨ parent = 1 := by omega
      rcases hCases with hZero | hLeaf
      · subst parent
        constructor
        · intro hChild
          change decide (larger < smaller) = false
          simp [Nat.not_lt.mpr hSmall]
        · intro hChild
          simp at hChild
      · subst parent
        constructor <;> intro hChild <;> simp at hChild
    · intro parent hParent
      have hParentBound : parent < 1 := by simpa using hParent
      have hZero : parent = 0 := by omega
      subst parent
      constructor <;> intro hChild <;> simp at hChild
    · intro lowerIndex hLowerIndex upperIndex hUpperIndex
      have hLowerBound : lowerIndex < 2 := by simpa using hLowerIndex
      have hUpperBound : upperIndex < 1 := by simpa using hUpperIndex
      have hLowerCases : lowerIndex = 0 ∨ lowerIndex = 1 := by omega
      have hUpperZero : upperIndex = 0 := by omega
      subst upperIndex
      rcases hLowerCases with hFirst | hSecond
      · subst lowerIndex
        simpa using hUpper
      · subst lowerIndex
        exact Nat.le_trans hSmall hUpper
  by_cases hValueUpper : value < upperRoot
  · have hResult := insert_from_two_singletons_upper_eq lowerRoot upperRoot value hValue
    have hOutput : LeanExperiments.RunningMedian.insert
        { lower := #[lowerRoot], upper := #[upperRoot] } value =
        { lower := #[value, lowerRoot], upper := #[upperRoot] } := by
      rw [hResult]
      simp [hValueUpper, insertHeap_maxPrefer_singleton_of_lt hValue]
    rw [hOutput]
    have hRotate : ([value, lowerRoot, upperRoot]).Perm
        ([lowerRoot, upperRoot, value]) := by
      exact (List.Perm.swap value lowerRoot [upperRoot]).symm.trans
        ((List.Perm.refl [lowerRoot]).append (List.Perm.swap value upperRoot []).symm)
    apply hOutputInvariant value lowerRoot upperRoot (Nat.le_of_lt hValue) (by omega)
    simpa using hRotate.trans hAppend
  · have hUpperLe : upperRoot ≤ value := by omega
    have hOutput : LeanExperiments.RunningMedian.insert
        { lower := #[lowerRoot], upper := #[upperRoot] } value =
        { lower := #[upperRoot, lowerRoot], upper := #[value] } := by
      rw [insert_from_two_singletons_upper_eq lowerRoot upperRoot value hValue]
      rw [ite_eq_right (by omega)]
      by_cases hEqual : upperRoot = lowerRoot
      · subst upperRoot
        have hInsert := insertHeap_eq_push_of_stops LeanExperiments.RunningMedian.maxPrefer
          #[lowerRoot] lowerRoot
          (Or.inr (by simp [LeanExperiments.RunningMedian.maxPrefer]))
        simpa using hInsert
      · have hLowerLt : lowerRoot < upperRoot := by omega
        simp [insertHeap_maxPrefer_singleton_of_lt hLowerLt]
    rw [hOutput]
    have hSwapRoots : ([upperRoot, lowerRoot, value]).Perm
        ([lowerRoot, upperRoot, value]) :=
      (List.Perm.swap upperRoot lowerRoot [value]).symm
    apply hOutputInvariant upperRoot lowerRoot value hRootBoundary hUpperLe
    simpa using hSwapRoots.trans hAppend

/-- 入力長が2以下の任意の不変状態へ値を挿入すると、不変条件が保たれる。

長さ0・1は基底契約へ、長さ2はサイズ式から各ヒープが単一要素であることを導き、
下側根との比較に応じた2つの一般挿入契約へ帰着する。したがって、値の大小や重複に
制限を置かず、全ての長さ3までの逐次状態遷移を一つの定理で扱える。
-/
private theorem sizeBalanced_of_bounds {lower upper : Nat}
    (hLower : lower ≤ upper + 1) (hUpper : upper ≤ lower) :
    lower = upper ∨ lower = upper + 1 := by omega

/-- 不変状態への任意の1回挿入は、要素数に関係なく不変条件を保つ。

空状態では初回挿入の契約を使う。非空状態は下側根との比較で振り分け、
ヒープ順序・全要素境界・分割性を保つ挿入補題と、再平衡の一般契約を合成する。
-/
theorem StateInvariant.insert_arbitrary {input : Array Nat}
    {state : LeanExperiments.RunningMedian.State}
    (hInvariant : StateInvariant input state) (value : Nat) :
    StateInvariant (input.push value)
      (LeanExperiments.RunningMedian.insert state value) := by
  by_cases hEmpty : state.lower.isEmpty = true
  · have hLowerSize : state.lower.size = 0 := by simpa [Array.isEmpty] using hEmpty
    have hUpperSize : state.upper.size = 0 := by
      rcases hInvariant.2.2.2.2 with hBalanced | hLowerExtra <;> omega
    have hLowerArray : state.lower = #[] := Array.size_eq_zero_iff.mp hLowerSize
    have hUpperArray : state.upper = #[] := Array.size_eq_zero_iff.mp hUpperSize
    have hInputSize : input.size = 0 := by
      have hLen := hInvariant.1.length_eq
      simpa [hLowerArray, hUpperArray] using hLen.symm
    have hInput : input = #[] := Array.size_eq_zero_iff.mp hInputSize
    have hState : state = LeanExperiments.RunningMedian.empty := by
      cases state with
      | mk lower upper =>
        have hl : lower = #[] := by simpa using hLowerArray
        have hu : upper = #[] := by simpa using hUpperArray
        simp [LeanExperiments.RunningMedian.empty, hl, hu]
    subst input
    rw [hState]
    exact StateInvariant.insert_empty value
  · have hNonempty : state.lower ≠ #[] := by
      intro hArray
      apply hEmpty
      simp [hArray]
    have hLowerPos : 0 < state.lower.size := Array.size_pos_iff.mpr hNonempty
    have hRoot : state.lower[0]? = some (state.lower[0]'hLowerPos) := by
      simp [getElem?_pos state.lower 0 hLowerPos]
    have hRootBang : state.lower[0]! = state.lower[0]'hLowerPos :=
      getElem!_pos state.lower 0 hLowerPos
    have hMaxPreferEq : maxPrefer = LeanExperiments.RunningMedian.maxPrefer := by
      funext candidate current
      rfl
    have hMinPreferEq : minPrefer = LeanExperiments.RunningMedian.minPrefer := by
      funext candidate current
      rfl
    by_cases hRoute : value ≤ state.lower[0]'hLowerPos
    · let lowerInserted := LeanExperiments.RunningMedian.insertHeap
        LeanExperiments.RunningMedian.maxPrefer state.lower value
      have hLowerHeapLocal : HeapOrdered maxPrefer lowerInserted := by
        simpa [lowerInserted] using
          insertHeap_maxPrefer_preserves state.lower hInvariant.2.1 value
      have hLowerHeap : HeapOrdered LeanExperiments.RunningMedian.maxPrefer lowerInserted := by
        simpa only [hMaxPreferEq] using hLowerHeapLocal
      have hBoundary := crossBoundary_insertLower_of_le_lowerRoot state value hLowerPos
        hInvariant.2.2.2.1 (by simpa [hRootBang] using hRoute)
      have hInsertSize : lowerInserted.size = state.lower.size + 1 := by
        exact insertHeap_size LeanExperiments.RunningMedian.maxPrefer state.lower value
      have hLowerClose : lowerInserted.size ≤ state.upper.size + 2 := by
        rcases hInvariant.2.2.2.2 with hEq | hExtra <;> omega
      have hUpperClose : state.upper.size ≤ lowerInserted.size + 1 := by
        rcases hInvariant.2.2.2.2 with hEq | hExtra <;> omega
      have hRebalanced := rebalanceBoth_preserves_heapOrders_and_crossBoundary
        lowerInserted state.upper hLowerHeap
        (by simpa only [hMinPreferEq] using hInvariant.2.2.1)
        hBoundary hLowerClose hUpperClose
      have hPartitionPre := insertLower_partition_size state value hInvariant.1
      have hPartition := (rebalanceBoth_perm lowerInserted state.upper).trans hPartitionPre.1
      have hInsertEq : LeanExperiments.RunningMedian.insert state value =
          { lower := (LeanExperiments.RunningMedian.rebalanceUpper
              (LeanExperiments.RunningMedian.rebalanceLower lowerInserted state.upper).1
              (LeanExperiments.RunningMedian.rebalanceLower lowerInserted state.upper).2).1,
            upper := (LeanExperiments.RunningMedian.rebalanceUpper
              (LeanExperiments.RunningMedian.rebalanceLower lowerInserted state.upper).1
              (LeanExperiments.RunningMedian.rebalanceLower lowerInserted state.upper).2).2 } := by
        simp [LeanExperiments.RunningMedian.insert, hEmpty, hRoot, hRoute, lowerInserted]
      rw [hInsertEq]
      refine ⟨?_, ?_, ?_, hRebalanced.2.2, ?_⟩
      · simpa [Array.toList_push] using hPartition
      · simpa only [hMaxPreferEq] using hRebalanced.1
      · simpa only [hMinPreferEq] using hRebalanced.2.1
      · have hFinal :
            (LeanExperiments.RunningMedian.rebalanceUpper
              (LeanExperiments.RunningMedian.rebalanceLower lowerInserted state.upper).1
              (LeanExperiments.RunningMedian.rebalanceLower lowerInserted state.upper).2).1.size =
                (LeanExperiments.RunningMedian.rebalanceUpper
                  (LeanExperiments.RunningMedian.rebalanceLower lowerInserted state.upper).1
                  (LeanExperiments.RunningMedian.rebalanceLower lowerInserted state.upper).2).2.size ∨
              (LeanExperiments.RunningMedian.rebalanceUpper
                (LeanExperiments.RunningMedian.rebalanceLower lowerInserted state.upper).1
                (LeanExperiments.RunningMedian.rebalanceLower lowerInserted state.upper).2).1.size =
                  (LeanExperiments.RunningMedian.rebalanceUpper
                    (LeanExperiments.RunningMedian.rebalanceLower lowerInserted state.upper).1
                    (LeanExperiments.RunningMedian.rebalanceLower lowerInserted state.upper).2).2.size + 1 := by
          apply sizeBalanced_of_bounds
          · exact (rebalanceBoth_size_balanced lowerInserted state.upper).1
          · exact (rebalanceBoth_size_balanced lowerInserted state.upper).2
        simpa only using hFinal
    · let upperInserted := LeanExperiments.RunningMedian.insertHeap
        LeanExperiments.RunningMedian.minPrefer state.upper value
      have hGreater : state.lower[0]'hLowerPos < value := by
        have hRouteBang : ¬ value ≤ state.lower[0]! := by simpa [hRootBang] using hRoute
        omega
      have hUpperHeapLocal : HeapOrdered minPrefer upperInserted := by
        simpa [upperInserted] using
          insertHeap_minPrefer_preserves state.upper hInvariant.2.2.1 value
      have hUpperHeap : HeapOrdered LeanExperiments.RunningMedian.minPrefer upperInserted := by
        simpa only [hMinPreferEq] using hUpperHeapLocal
      have hBoundary := crossBoundary_insertUpper_of_gt_lowerRoot state value hLowerPos
        hInvariant.2.1 hInvariant.2.2.2.1
        (by simpa [hRootBang] using hGreater)
      have hInsertSize : upperInserted.size = state.upper.size + 1 := by
        exact insertHeap_size LeanExperiments.RunningMedian.minPrefer state.upper value
      have hLowerClose : state.lower.size ≤ upperInserted.size + 2 := by
        rcases hInvariant.2.2.2.2 with hEq | hExtra <;> omega
      have hUpperClose : upperInserted.size ≤ state.lower.size + 1 := by
        rcases hInvariant.2.2.2.2 with hEq | hExtra <;> omega
      have hRebalanced := rebalanceBoth_preserves_heapOrders_and_crossBoundary
        state.lower upperInserted hInvariant.2.1 hUpperHeap hBoundary hLowerClose hUpperClose
      have hPartitionPre := insertUpper_partition_size state value hInvariant.1
      have hPartition := (rebalanceBoth_perm state.lower upperInserted).trans hPartitionPre.1
      have hInsertEq : LeanExperiments.RunningMedian.insert state value =
          { lower := (LeanExperiments.RunningMedian.rebalanceUpper
              (LeanExperiments.RunningMedian.rebalanceLower state.lower upperInserted).1
              (LeanExperiments.RunningMedian.rebalanceLower state.lower upperInserted).2).1,
            upper := (LeanExperiments.RunningMedian.rebalanceUpper
              (LeanExperiments.RunningMedian.rebalanceLower state.lower upperInserted).1
              (LeanExperiments.RunningMedian.rebalanceLower state.lower upperInserted).2).2 } := by
        simp [LeanExperiments.RunningMedian.insert, hEmpty, hRoot, hRoute, upperInserted]
      rw [hInsertEq]
      refine ⟨?_, ?_, ?_, hRebalanced.2.2, ?_⟩
      · simpa [Array.toList_push] using hPartition
      · simpa only [hMaxPreferEq] using hRebalanced.1
      · simpa only [hMinPreferEq] using hRebalanced.2.1
      · have hFinal :
            (LeanExperiments.RunningMedian.rebalanceUpper
              (LeanExperiments.RunningMedian.rebalanceLower state.lower upperInserted).1
              (LeanExperiments.RunningMedian.rebalanceLower state.lower upperInserted).2).1.size =
                (LeanExperiments.RunningMedian.rebalanceUpper
                  (LeanExperiments.RunningMedian.rebalanceLower state.lower upperInserted).1
                  (LeanExperiments.RunningMedian.rebalanceLower state.lower upperInserted).2).2.size ∨
              (LeanExperiments.RunningMedian.rebalanceUpper
                (LeanExperiments.RunningMedian.rebalanceLower state.lower upperInserted).1
                (LeanExperiments.RunningMedian.rebalanceLower state.lower upperInserted).2).1.size =
                  (LeanExperiments.RunningMedian.rebalanceUpper
                    (LeanExperiments.RunningMedian.rebalanceLower state.lower upperInserted).1
                    (LeanExperiments.RunningMedian.rebalanceLower state.lower upperInserted).2).2.size + 1 := by
          apply sizeBalanced_of_bounds
          · exact (rebalanceBoth_size_balanced state.lower upperInserted).1
          · exact (rebalanceBoth_size_balanced state.lower upperInserted).2
        simpa only using hFinal

/-- 不変状態から任意の値列を順に挿入すると、入力接頭部と値列を連結した配列上で
状態不変条件が保たれる。1値ごとの一般挿入定理を `List.foldl` に沿って合成する。
-/
theorem fold_insert_stateInvariant (items : List Nat) :
    ∀ {input : Array Nat} {state : LeanExperiments.RunningMedian.State},
      StateInvariant input state →
      StateInvariant (input ++ items.toArray)
        (items.foldl LeanExperiments.RunningMedian.insert state) := by
  induction items with
  | nil =>
      intro input state h
      simpa using h
  | cons value items ih =>
      intro input state h
      rw [List.foldl_cons]
      have hNext := StateInvariant.insert_arbitrary h value
      have hRest := ih hNext
      simpa [Array.append_assoc] using hRest

/-- 任意の入力配列を処理した `ofArray` の状態は論理的不変条件を満たす。

値の範囲や入力長に制限を置かず、空状態からの一般的な挿入保存を帰納的に合成する。
-/
theorem StateInvariant.ofArray_arbitrary (values : Array Nat) :
    StateInvariant values (LeanExperiments.RunningMedian.ofArray values) := by
  have h := fold_insert_stateInvariant values.toList StateInvariant.empty
  simpa [LeanExperiments.RunningMedian.ofArray, ← Array.foldl_toList] using h

/-- 入力長が2以下の任意の不変状態へ値を挿入すると、不変条件が保たれる。
長さ0・1は基底契約へ、長さ2はサイズ式から各ヒープが単一要素であることを導き、
下側根との比較に応じた2つの一般挿入契約へ帰着する。したがって、値の大小や重複に
制限を置かず、全ての長さ3までの逐次状態遷移を一つの定理で扱える。
-/
theorem StateInvariant.insert_of_size_le_two {input : Array Nat}
    {state : LeanExperiments.RunningMedian.State}
    (hInvariant : StateInvariant input state) (hSize : input.size ≤ 2)
    (value : Nat) :
    StateInvariant (input.push value)
      (LeanExperiments.RunningMedian.insert state value) := by
  by_cases hSmall : input.size ≤ 1
  · exact StateInvariant.insert_of_size_le_one hInvariant hSmall value
  · have hInputSize : input.size = 2 := by omega
    have hTotal := StateInvariant.size_partition hInvariant
    have hLowerSize : state.lower.size = 1 := by
      rcases hInvariant.2.2.2.2 with hBalanced | hLowerExtra <;> omega
    have hUpperSize : state.upper.size = 1 := by
      rcases hInvariant.2.2.2.2 with hBalanced | hLowerExtra <;> omega
    let lowerRoot := state.lower[0]'(by omega)
    let upperRoot := state.upper[0]'(by omega)
    have hLower : state.lower = #[lowerRoot] := by
      apply Array.ext
      · exact hLowerSize
      · intro index hLeft hRight
        have hIndex : index = 0 := by omega
        subst index
        simp [lowerRoot]
    have hUpper : state.upper = #[upperRoot] := by
      apply Array.ext
      · exact hUpperSize
      · intro index hLeft hRight
        have hIndex : index = 0 := by omega
        subst index
        simp [upperRoot]
    have hState : state = { lower := #[lowerRoot], upper := #[upperRoot] } := by
      cases state with
      | mk lower upper =>
          simp only [LeanExperiments.RunningMedian.State.mk.injEq]
          exact ⟨hLower, hUpper⟩
    by_cases hRoute : value ≤ lowerRoot
    · exact StateInvariant.insert_from_two_singletons_of_le
        hInvariant hState hRoute
    · exact StateInvariant.insert_from_two_singletons_of_gt
        hInvariant hState (by omega)

/-- 2+1要素の不変状態で下側根より大きい値を挿入すると不変条件が保たれる。

値は上側の単一要素ヒープへ入り、上側根との比較で2要素の順序が決まる。
挿入後は両ヒープが2要素となるため、再平衡は状態を変えない。この枝では
値域を有限化せず、既存の下側ヒープと境界条件から全要素間の境界を導く。
-/
theorem StateInvariant.insert_from_two_one_of_gt_root
    {input : Array Nat} {state : LeanExperiments.RunningMedian.State}
    (hInvariant : StateInvariant input state)
    {lowerRoot lowerOther upperRoot value : Nat}
    (hState : state = { lower := #[lowerRoot, lowerOther], upper := #[upperRoot] })
    (hValue : lowerRoot < value) :
    StateInvariant (input.push value)
      (LeanExperiments.RunningMedian.insert state value) := by
  rw [hState] at hInvariant ⊢
  have hLowerOther : lowerOther ≤ lowerRoot := by
    have hEdge := (hInvariant.2.1 0 (by simp)).1 (by simp)
    simpa [maxPrefer] using hEdge
  have hLowerUpperRoot := hInvariant.2.2.2.1
  have hRootLeUpper : lowerRoot ≤ upperRoot :=
    hLowerUpperRoot 0 (by simp) 0 (by simp)
  have hOtherLeUpper : lowerOther ≤ upperRoot :=
    Nat.le_trans hLowerOther hRootLeUpper
  have hUpperPerm : ([lowerRoot, lowerOther, upperRoot]).Perm input.toList := by
    simpa using hInvariant.1
  have hAppend := hUpperPerm.append_right [value]
  have hUpperInsert :
      LeanExperiments.RunningMedian.insertHeap
          LeanExperiments.RunningMedian.minPrefer #[upperRoot] value =
        (if value < upperRoot then #[value, upperRoot] else #[upperRoot, value]) := by
    by_cases hLess : value < upperRoot
    · simp [hLess, insertHeap_minPrefer_singleton_of_gt hLess]
    · have hLe : upperRoot ≤ value := by omega
      have hPush := insertHeap_eq_push_of_stops
        LeanExperiments.RunningMedian.minPrefer #[upperRoot] value
        (Or.inr (by simpa [LeanExperiments.RunningMedian.minPrefer] using hLe))
      simp [hLess, hPush]
  have hRebalanceLower (upper : Array Nat) (hSize : upper.size = 2) :
      LeanExperiments.RunningMedian.rebalanceLower #[lowerRoot, lowerOther] upper =
        (#[lowerRoot, lowerOther], upper) :=
    rebalanceLower_eq_self_of_size_le _ _ (by rw [hSize]; simp)
  have hRebalanceUpper (upper : Array Nat) (hSize : upper.size = 2) :
      LeanExperiments.RunningMedian.rebalanceUpper #[lowerRoot, lowerOther] upper =
        (#[lowerRoot, lowerOther], upper) :=
    rebalanceUpper_eq_self_of_size_le _ _ (by rw [hSize]; simp)
  have hOutput (first second : Nat) (hOrder : first ≤ second)
      (hFirstBoundary : lowerRoot ≤ first ∧ lowerOther ≤ first)
      (hSecondBoundary : lowerRoot ≤ second ∧ lowerOther ≤ second)
      (hPerm : ([lowerRoot, lowerOther, first, second]).Perm
        (input.push value).toList) :
      StateInvariant (input.push value)
        { lower := #[lowerRoot, lowerOther], upper := #[first, second] } := by
    refine ⟨hPerm, hInvariant.2.1, ?_, ?_, by simp⟩
    · intro parent hParent
      have hBound : parent < 2 := by simpa using hParent
      have hParentCases : parent = 0 ∨ parent = 1 := by omega
      rcases hParentCases with hZero | hLeaf
      · subst parent
        constructor
        · intro _
          simpa [minPrefer] using hOrder
        · intro hChild
          simp at hChild
      · subst parent
        constructor <;> intro hChild <;> simp at hChild
    · intro lowerIndex hLowerIndex upperIndex hUpperIndex
      have hLowerCases : lowerIndex = 0 ∨ lowerIndex = 1 := by
        have hBound : lowerIndex < 2 := by simpa using hLowerIndex
        omega
      have hUpperCases : upperIndex = 0 ∨ upperIndex = 1 := by
        have hBound : upperIndex < 2 := by simpa using hUpperIndex
        omega
      rcases hLowerCases with hLowerZero | hLowerOne <;>
        rcases hUpperCases with hUpperZero | hUpperOne <;>
        subst lowerIndex <;> subst upperIndex
      · exact hFirstBoundary.1
      · exact hSecondBoundary.1
      · exact hFirstBoundary.2
      · exact hSecondBoundary.2
  by_cases hLess : value < upperRoot
  · have hResult :
        LeanExperiments.RunningMedian.insert
            { lower := #[lowerRoot, lowerOther], upper := #[upperRoot] } value =
          { lower := #[lowerRoot, lowerOther], upper := #[value, upperRoot] } := by
      have hRoute : ¬ value ≤ lowerRoot := by omega
      have hBalLower := rebalanceLower_eq_self_of_size_le
        #[lowerRoot, lowerOther] #[value, upperRoot] (by simp)
      have hBalUpper := rebalanceUpper_eq_self_of_size_le
        #[lowerRoot, lowerOther] #[value, upperRoot] (by simp)
      simp [LeanExperiments.RunningMedian.insert, hRoute, hUpperInsert, hLess,
        hBalLower, hBalUpper]
    rw [hResult]
    have hRotate : ([lowerRoot, lowerOther, value, upperRoot]).Perm
        ([lowerRoot, lowerOther, upperRoot, value]) := by
      simpa using (List.Perm.refl [lowerRoot, lowerOther]).append
        (List.Perm.swap value upperRoot []).symm
    apply hOutput value upperRoot (Nat.le_of_lt hLess)
      ⟨by omega, by omega⟩ ⟨hRootLeUpper, hOtherLeUpper⟩
    simpa [Array.toList_push] using hRotate.trans hAppend
  · have hLe : upperRoot ≤ value := by omega
    have hResult :
        LeanExperiments.RunningMedian.insert
            { lower := #[lowerRoot, lowerOther], upper := #[upperRoot] } value =
          { lower := #[lowerRoot, lowerOther], upper := #[upperRoot, value] } := by
      have hRoute : ¬ value ≤ lowerRoot := by omega
      have hBalLower := rebalanceLower_eq_self_of_size_le
        #[lowerRoot, lowerOther] #[upperRoot, value] (by simp)
      have hBalUpper := rebalanceUpper_eq_self_of_size_le
        #[lowerRoot, lowerOther] #[upperRoot, value] (by simp)
      simp [LeanExperiments.RunningMedian.insert, hRoute, hUpperInsert, hLess,
        hBalLower, hBalUpper]
    rw [hResult]
    apply hOutput upperRoot value hLe
      ⟨hRootLeUpper, hOtherLeUpper⟩ ⟨by omega, by omega⟩
    simpa [Array.toList_push] using hAppend

/-- 2+1要素の不変状態で下側根以下の値を挿入すると不変条件を保つ。

新値は最大ヒープの末尾へ入り、最大根を一つ上側へ移す。取り出し契約から残る
下側ヒープと根以下の境界を得て、1回の再平衡補題で一般の2+2状態へ接続する。
-/
theorem StateInvariant.insert_from_two_one_of_le_root
    {input : Array Nat} {state : LeanExperiments.RunningMedian.State}
    (hInvariant : StateInvariant input state)
    {lowerRoot lowerOther upperRoot value : Nat}
    (hState : state = { lower := #[lowerRoot, lowerOther], upper := #[upperRoot] })
    (hValue : value ≤ lowerRoot) :
    StateInvariant (input.push value)
      (LeanExperiments.RunningMedian.insert state value) := by
  rw [hState] at hInvariant ⊢
  have hLowerOther : lowerOther ≤ lowerRoot := by
    have hEdge := (hInvariant.2.1 0 (by simp)).1 (by simp)
    simpa [maxPrefer] using hEdge
  have hRootBoundary := hInvariant.2.2.2.1
  have hRootUpper : lowerRoot ≤ upperRoot :=
    hRootBoundary 0 (by simp) 0 (by simp)
  have hLowerInsert :
      LeanExperiments.RunningMedian.insertHeap
          LeanExperiments.RunningMedian.maxPrefer #[lowerRoot, lowerOther] value =
        #[lowerRoot, lowerOther, value] := by
    apply insertHeap_eq_push_of_stops
      LeanExperiments.RunningMedian.maxPrefer #[lowerRoot, lowerOther] value
    right
    simp [LeanExperiments.RunningMedian.maxPrefer, hValue]
  have hInsertedHeap : HeapOrdered maxPrefer #[lowerRoot, lowerOther, value] := by
    rw [← hLowerInsert]
    exact insertHeap_HeapOrdered_maxPrefer_of_parent_le #[lowerRoot, lowerOther]
      value hInvariant.2.1 (Or.inr (by simp [hValue]))
  have hPopExists : ∃ rest,
      LeanExperiments.RunningMedian.popHeap maxPrefer #[lowerRoot, lowerOther, value] =
        some (lowerRoot, rest) := by
    cases hPop : LeanExperiments.RunningMedian.popHeap maxPrefer
        #[lowerRoot, lowerOther, value] with
    | none =>
        have hEmpty := (popHeap_eq_none_iff_empty maxPrefer _).mp hPop
        simp at hEmpty
    | some pair =>
        rcases pair with ⟨root, rest⟩
        have hRoot := popHeap_value_eq_root hPop
        simp at hRoot
        subst root
        exact ⟨rest, rfl⟩
  obtain ⟨rest, hPop⟩ := hPopExists
  have hPopCorrect := popHeap_maxPrefer_restCorrect_of_heapOrdered
    #[lowerRoot, lowerOther, value] hInsertedHeap
  have hPopSpec :
      0 < #[lowerRoot, lowerOther, value].size ∧
      #[lowerRoot, lowerOther, value][0]? = some lowerRoot ∧
      LeanExperiments.Verification.HeapSort.Spec.MaxHeap rest ∧
      rest.toList.Perm (#[lowerRoot, lowerOther, value].toList.drop 1) := by
    simpa [LeanExperiments.Verification.HeapSort.Spec.PopMaxRestCorrectFor, hPop]
      using hPopCorrect
  have hRestHeap : HeapOrdered maxPrefer rest :=
    (heapSortMaxHeap_iff_HeapOrdered_maxPrefer rest).mp hPopSpec.2.2.1
  have hRestBound : ∀ item, item ∈ rest.toList → item ≤ lowerRoot := by
    simpa [hPop] using
      LeanExperiments.Verification.HeapSort.Spec.PopMaxRestCorrectFor.rest_le_maximum
        hPopCorrect
        ((heapSortMaxHeap_iff_HeapOrdered_maxPrefer _).mpr hInsertedHeap)
  have hRestLe : ∀ index (hIndex : index < rest.size),
      rest[index]'hIndex ≤ lowerRoot := by
    intro index hIndex
    have hMem : rest[index]'hIndex ∈ rest.toList :=
      by simp
    exact hRestBound _ hMem
  have hRestSize : rest.size = 2 := by
    have hSize := popHeap_size hPop
    simp at hSize
    omega
  have hUpperInsert :
      LeanExperiments.RunningMedian.insertHeap minPrefer #[upperRoot] lowerRoot =
        #[lowerRoot, upperRoot] := by
    by_cases hStrict : lowerRoot < upperRoot
    · have hInsert := insertHeap_minPrefer_singleton_of_gt hStrict
      change LeanExperiments.RunningMedian.insertHeap minPrefer #[upperRoot] lowerRoot = _
      exact hInsert
    · have hEqual : lowerRoot = upperRoot := by omega
      subst upperRoot
      simpa using (insertHeap_eq_push_of_stops minPrefer #[lowerRoot] lowerRoot
        (Or.inr (by simp [minPrefer])))
  have hUpperHeap : HeapOrdered minPrefer #[lowerRoot, upperRoot] := by
    intro parent hParent
    have hParentCases : parent = 0 ∨ parent = 1 := by
      have hBound : parent < 2 := by simpa using hParent
      omega
    rcases hParentCases with hParentZero | hParentOne
    · subst parent
      constructor
      · intro _
        simpa [minPrefer] using hRootUpper
      · intro hChild
        simp at hChild
    · subst parent
      constructor <;> intro hChild <;> simp at hChild
  have hTransfer : LeanExperiments.RunningMedian.transferLowerRoot maxPrefer minPrefer
      #[lowerRoot, lowerOther, value] #[upperRoot] =
        some (rest, #[lowerRoot, upperRoot]) := by
    simp [LeanExperiments.RunningMedian.transferLowerRoot, hPop, hUpperInsert]
  have hLowerBalanced := rebalanceLower_one_transfer
    #[lowerRoot, lowerOther, value] #[upperRoot] rest #[lowerRoot, upperRoot]
    (by simp) hTransfer (by simp [hRestSize])
  have hUpperBalanced := rebalanceUpper_eq_self_of_size_le rest #[lowerRoot, upperRoot]
    (by simp [hRestSize])
  have hResult : LeanExperiments.RunningMedian.insert
      { lower := #[lowerRoot, lowerOther], upper := #[upperRoot] } value =
        { lower := rest, upper := #[lowerRoot, upperRoot] } := by
    simp [LeanExperiments.RunningMedian.insert, hValue, hLowerInsert,
      hLowerBalanced, hUpperBalanced]
  rw [hResult]
  have hPartition := insert_partition
    ({ lower := #[lowerRoot, lowerOther], upper := #[upperRoot] } :
      LeanExperiments.RunningMedian.State) value hInvariant.1
  refine ⟨?_, hRestHeap, hUpperHeap, ?_, ?_⟩
  · rw [hResult] at hPartition
    exact hPartition
  · intro lowerIndex hLowerIndex upperIndex hUpperIndex
    change rest[lowerIndex] ≤ #[lowerRoot, upperRoot][upperIndex]
    have hLowerCases : lowerIndex = 0 ∨ lowerIndex = 1 := by
      have hBound : lowerIndex < 2 := by simpa [hRestSize] using hLowerIndex
      omega
    have hUpperCases : upperIndex = 0 ∨ upperIndex = 1 := by
      have hBound : upperIndex < 2 := by simpa using hUpperIndex
      omega
    rcases hLowerCases with hFirst | hSecond <;>
      rcases hUpperCases with hUpperFirst | hUpperSecond <;>
      subst lowerIndex <;> subst upperIndex
    · simpa using hRestLe 0 (by omega)
    · exact Nat.le_trans (hRestLe 0 (by omega)) hRootUpper
    · simpa using hRestLe 1 (by omega)
    · exact Nat.le_trans (hRestLe 1 (by omega)) hRootUpper
  · simp [hRestSize]

/-- 2+2要素の不変状態で下側根以下の値を挿入すると不変条件を保つ。

新しい値は下側へ入り、サイズは3+2となるため再平衡ループは状態を変えない。
挿入ヒープの一般契約とヒープ間境界の契約を合成し、値の列挙を使わずに示す。
-/
theorem StateInvariant.insert_from_two_two_of_le_root
    {input : Array Nat} {state : LeanExperiments.RunningMedian.State}
    (hInvariant : StateInvariant input state)
    {lowerRoot lowerOther upperRoot upperOther value : Nat}
    (hState : state =
      { lower := #[lowerRoot, lowerOther], upper := #[upperRoot, upperOther] })
    (hValue : value ≤ lowerRoot) :
    StateInvariant (input.push value)
      (LeanExperiments.RunningMedian.insert state value) := by
  rw [hState] at hInvariant ⊢
  have hRootUpper : lowerRoot ≤ upperRoot :=
    hInvariant.2.2.2.1 0 (by simp) 0 (by simp)
  have hLowerInsertedHeap :=
    insertHeap_maxPrefer_twoElements_preserves (value := value) hInvariant.2.1
  have hLowerInsertedSize :
      (LeanExperiments.RunningMedian.insertHeap LeanExperiments.RunningMedian.maxPrefer
        #[lowerRoot, lowerOther] value).size = 3 := by
    simp [insertHeap_size]
  have hLowerNoRebalanceImpl := rebalanceLower_eq_self_of_size_le
    (LeanExperiments.RunningMedian.insertHeap
      LeanExperiments.RunningMedian.maxPrefer #[lowerRoot, lowerOther] value)
    #[upperRoot, upperOther] (by simp [insertHeap_size])
  have hUpperNoRebalanceImpl := rebalanceUpper_eq_self_of_size_le
    (LeanExperiments.RunningMedian.insertHeap
      LeanExperiments.RunningMedian.maxPrefer #[lowerRoot, lowerOther] value)
    #[upperRoot, upperOther] (by simp [insertHeap_size])
  have hResult : LeanExperiments.RunningMedian.insert
      { lower := #[lowerRoot, lowerOther], upper := #[upperRoot, upperOther] } value =
        { lower := LeanExperiments.RunningMedian.insertHeap LeanExperiments.RunningMedian.maxPrefer
            #[lowerRoot, lowerOther] value,
          upper := #[upperRoot, upperOther] } := by
    simp [LeanExperiments.RunningMedian.insert, hValue,
      hLowerNoRebalanceImpl, hUpperNoRebalanceImpl]
  rw [hResult]
  have hPartition := insert_partition
    ({ lower := #[lowerRoot, lowerOther], upper := #[upperRoot, upperOther] } :
      LeanExperiments.RunningMedian.State) value hInvariant.1
  refine ⟨?_, hLowerInsertedHeap, hInvariant.2.2.1, ?_, ?_⟩
  · rw [hResult] at hPartition
    exact hPartition
  · change ∀ lowerIndex (hLowerIndex : lowerIndex <
        (LeanExperiments.RunningMedian.insertHeap maxPrefer
          #[lowerRoot, lowerOther] value).size),
      ∀ upperIndex (hUpperIndex : upperIndex < #[upperRoot, upperOther].size),
        (LeanExperiments.RunningMedian.insertHeap maxPrefer
          #[lowerRoot, lowerOther] value)[lowerIndex]'hLowerIndex ≤
          #[upperRoot, upperOther][upperIndex]'hUpperIndex
    have hBoundaryAfterInsert := crossBoundary_insertLower
      ({ lower := #[lowerRoot, lowerOther], upper := #[upperRoot, upperOther] } :
        LeanExperiments.RunningMedian.State)
      value hInvariant.2.2.2.1 (by
        intro upperIndex hUpperIndex
        exact Nat.le_trans hValue
          (hInvariant.2.2.2.1 0 (by simp) upperIndex hUpperIndex))
    simpa [maxPrefer, LeanExperiments.RunningMedian.maxPrefer] using hBoundaryAfterInsert
  · simp [hLowerInsertedSize]

/-- 2+2要素の不変状態で下側根より大きい値を挿入すると不変条件を保つ。

上側最小ヒープへの挿入後、最小根を下側へ一度移す。最小値取り出し契約から残余の
順序と下界を得て、挿入後も全ての要素間境界が成り立つことを示す。
-/
theorem StateInvariant.insert_from_two_two_of_gt_root
    {input : Array Nat} {state : LeanExperiments.RunningMedian.State}
    (hInvariant : StateInvariant input state)
    {lowerRoot lowerOther upperRoot upperOther value : Nat}
    (hState : state =
      { lower := #[lowerRoot, lowerOther], upper := #[upperRoot, upperOther] })
    (hValue : lowerRoot < value) :
    StateInvariant (input.push value)
      (LeanExperiments.RunningMedian.insert state value) := by
  rw [hState] at hInvariant ⊢
  have hLowerOther : lowerOther ≤ lowerRoot := by
    have hEdge := (hInvariant.2.1 0 (by simp)).1 (by simp)
    simpa [maxPrefer] using hEdge
  have hUpperOrder : upperRoot ≤ upperOther := by
    have hEdge := (hInvariant.2.2.1 0 (by simp)).1 (by simp)
    simpa [minPrefer] using hEdge
  have hBoundary := hInvariant.2.2.2.1
  have hRootUpper : lowerRoot ≤ upperRoot :=
    hBoundary 0 (by simp) 0 (by simp)
  have hOtherUpper : lowerOther ≤ upperRoot :=
    hBoundary 1 (by simp) 0 (by simp)
  have hLowerHeap : HeapOrdered LeanExperiments.RunningMedian.maxPrefer
      #[lowerRoot, lowerOther] := by
    intro parent hParent
    rcases hInvariant.2.1 parent (by simpa using hParent) with ⟨hLeft, hRight⟩
    constructor
    · intro hChild
      have hEdge := hLeft (by simpa using hChild)
      exact hEdge
    · intro hChild
      have hEdge := hRight (by simpa using hChild)
      exact hEdge
  have hUpperHeap : MinHeap #[upperRoot, upperOther] := by
    apply (minHeap_iff_HeapOrdered_minPrefer _).mpr
    simpa [minPrefer, LeanExperiments.RunningMedian.minPrefer] using hInvariant.2.2.1
  have hUpperInsertedHeap : MinHeap
      (LeanExperiments.RunningMedian.insertHeap LeanExperiments.RunningMedian.minPrefer
        #[upperRoot, upperOther] value) :=
    insertHeap_minPrefer_twoElements_preserves (value := value) hUpperHeap
  have hUpperLowerBound : ∀ item,
      item ∈ #[upperRoot, upperOther].toList → lowerRoot ≤ item := by
    intro item hItem
    change item ∈ [upperRoot, upperOther] at hItem
    simp at hItem
    rcases hItem with hRoot | hOther
    · subst item
      exact hRootUpper
    · subst item
      exact Nat.le_trans hRootUpper hUpperOrder
  have hInsertedUpperLowerBound : ∀ item,
      item ∈ (LeanExperiments.RunningMedian.insertHeap
        LeanExperiments.RunningMedian.minPrefer #[upperRoot, upperOther] value).toList →
        lowerRoot ≤ item :=
    insertHeap_ge_of_forall_ge LeanExperiments.RunningMedian.minPrefer
      #[upperRoot, upperOther] value lowerRoot hUpperLowerBound (by omega)
  have hPopExists : ∃ rest,
      LeanExperiments.RunningMedian.popHeap LeanExperiments.RunningMedian.minPrefer
        (LeanExperiments.RunningMedian.insertHeap
          LeanExperiments.RunningMedian.minPrefer #[upperRoot, upperOther] value) =
        some ((LeanExperiments.RunningMedian.insertHeap
          LeanExperiments.RunningMedian.minPrefer #[upperRoot, upperOther] value)[0]!, rest) := by
    cases hPop : LeanExperiments.RunningMedian.popHeap
        LeanExperiments.RunningMedian.minPrefer
        (LeanExperiments.RunningMedian.insertHeap
          LeanExperiments.RunningMedian.minPrefer #[upperRoot, upperOther] value) with
    | none =>
        have hEmpty := (popHeap_eq_none_iff_empty
          LeanExperiments.RunningMedian.minPrefer
          (LeanExperiments.RunningMedian.insertHeap
            LeanExperiments.RunningMedian.minPrefer #[upperRoot, upperOther] value)).mp hPop
        have hSize := insertHeap_size LeanExperiments.RunningMedian.minPrefer
          #[upperRoot, upperOther] value
        omega
    | some pair =>
        rcases pair with ⟨root, rest⟩
        have hRoot := popHeap_value_eq_root hPop
        have hPos : 0 < (LeanExperiments.RunningMedian.insertHeap
            LeanExperiments.RunningMedian.minPrefer #[upperRoot, upperOther] value).size := by
          rw [insertHeap_size]
          omega
        have hRootValue : root =
            (LeanExperiments.RunningMedian.insertHeap LeanExperiments.RunningMedian.minPrefer
              #[upperRoot, upperOther] value)[0]! := by
          rw [getElem?_pos _ 0 hPos] at hRoot
          have hEq := Option.some.inj hRoot
          calc
            root = (LeanExperiments.RunningMedian.insertHeap
                LeanExperiments.RunningMedian.minPrefer #[upperRoot, upperOther] value)[0] := hEq.symm
            _ = (LeanExperiments.RunningMedian.insertHeap
                LeanExperiments.RunningMedian.minPrefer #[upperRoot, upperOther] value)[0]! :=
              (getElem!_pos _ 0 hPos).symm
        subst root
        exact ⟨rest, rfl⟩
  obtain ⟨rest, hPopUpper⟩ := hPopExists
  let moved := (LeanExperiments.RunningMedian.insertHeap
    LeanExperiments.RunningMedian.minPrefer #[upperRoot, upperOther] value)[0]!
  have hMovedLower : lowerRoot ≤ moved := by
    let upperInserted := LeanExperiments.RunningMedian.insertHeap
      LeanExperiments.RunningMedian.minPrefer #[upperRoot, upperOther] value
    have hPos : 0 < upperInserted.size := by
      change 0 < (LeanExperiments.RunningMedian.insertHeap
        LeanExperiments.RunningMedian.minPrefer #[upperRoot, upperOther] value).size
      rw [insertHeap_size]
      omega
    have hMem : upperInserted[0]'hPos ∈ upperInserted.toList :=
      Array.getElem_mem_toList hPos
    have hMovedEq : moved = upperInserted[0]'hPos := by
      change (LeanExperiments.RunningMedian.insertHeap
        LeanExperiments.RunningMedian.minPrefer #[upperRoot, upperOther] value)[0]! = _
      exact getElem!_pos _ 0 hPos
    have hMovedMem : moved ∈ upperInserted.toList := by
      rw [hMovedEq]
      exact hMem
    simpa [upperInserted] using hInsertedUpperLowerBound moved hMovedMem
  have hRestMinHeap : MinHeap rest :=
    popHeap_minPrefer_restMinHeap_of_MinHeap hUpperInsertedHeap hPopUpper
  have hMovedMinimum := popHeap_minPrefer_returns_minimum_of_MinHeap
    hUpperInsertedHeap hPopUpper
  have hRestGe : ∀ index (hIndex : index < rest.size), moved ≤ rest[index]'hIndex := by
    intro index hIndex
    have hPerm := popHeap_perm_dropRoot hPopUpper
    have hMem : rest[index]'hIndex ∈ rest.toList := by simp
    have hInTail : rest[index]'hIndex ∈
        (LeanExperiments.RunningMedian.insertHeap LeanExperiments.RunningMedian.minPrefer
          #[upperRoot, upperOther] value).toList.drop 1 := hPerm.mem_iff.mp hMem
    have hInHeap := List.mem_of_mem_drop hInTail
    have hInArray : rest[index]'hIndex ∈
        LeanExperiments.RunningMedian.insertHeap LeanExperiments.RunningMedian.minPrefer
          #[upperRoot, upperOther] value := by simpa using hInHeap
    obtain ⟨heapIndex, hIndexArray, hAt⟩ := Array.mem_iff_getElem.mp hInArray
    have hMinimum := hMovedMinimum heapIndex hIndexArray
    have hAtBang :
        (LeanExperiments.RunningMedian.insertHeap LeanExperiments.RunningMedian.minPrefer
          #[upperRoot, upperOther] value)[heapIndex]! = rest[index]'hIndex := by
      rw [getElem!_pos _ heapIndex hIndexArray]
      exact hAt
    calc
      moved = (LeanExperiments.RunningMedian.insertHeap LeanExperiments.RunningMedian.minPrefer
        #[upperRoot, upperOther] value)[0]! := rfl
      _ ≤ (LeanExperiments.RunningMedian.insertHeap LeanExperiments.RunningMedian.minPrefer
        #[upperRoot, upperOther] value)[heapIndex]! := hMovedMinimum heapIndex hIndexArray
      _ = rest[index]'hIndex := hAtBang
  have hPopSize : rest.size = 2 := by
    have hSize := popHeap_size hPopUpper
    simp [insertHeap_size] at hSize
    omega
  have hLowerInsertedHeap : HeapOrdered LeanExperiments.RunningMedian.maxPrefer
      (LeanExperiments.RunningMedian.insertHeap LeanExperiments.RunningMedian.maxPrefer
        #[lowerRoot, lowerOther] moved) :=
    insertHeap_maxPrefer_twoElements_preserves (value := moved) hLowerHeap
  have hLowerNoRebalance := rebalanceLower_eq_self_of_size_le
    #[lowerRoot, lowerOther]
    (LeanExperiments.RunningMedian.insertHeap LeanExperiments.RunningMedian.minPrefer
      #[upperRoot, upperOther] value) (by simp [insertHeap_size])
  have hUpperTransfer : LeanExperiments.RunningMedian.transferUpperRoot
      LeanExperiments.RunningMedian.minPrefer LeanExperiments.RunningMedian.maxPrefer
      #[lowerRoot, lowerOther]
      (LeanExperiments.RunningMedian.insertHeap LeanExperiments.RunningMedian.minPrefer
        #[upperRoot, upperOther] value) =
      some (LeanExperiments.RunningMedian.insertHeap LeanExperiments.RunningMedian.maxPrefer
        #[lowerRoot, lowerOther] moved, rest) := by
    simp [LeanExperiments.RunningMedian.transferUpperRoot, hPopUpper, moved]
  have hAfterUpper := rebalanceUpper_one_transfer
    #[lowerRoot, lowerOther]
    (LeanExperiments.RunningMedian.insertHeap LeanExperiments.RunningMedian.minPrefer
      #[upperRoot, upperOther] value)
    (LeanExperiments.RunningMedian.insertHeap LeanExperiments.RunningMedian.maxPrefer
      #[lowerRoot, lowerOther] moved)
    rest (by simp [insertHeap_size]) hUpperTransfer (by
      calc
        rest.size ≤ #[lowerRoot, lowerOther].size + 1 := by simp [hPopSize]
        _ = (LeanExperiments.RunningMedian.insertHeap LeanExperiments.RunningMedian.maxPrefer
          #[lowerRoot, lowerOther] moved).size := (insertHeap_size _ _ _).symm)
  have hResult : LeanExperiments.RunningMedian.insert
      { lower := #[lowerRoot, lowerOther], upper := #[upperRoot, upperOther] } value =
        { lower := LeanExperiments.RunningMedian.insertHeap LeanExperiments.RunningMedian.maxPrefer
            #[lowerRoot, lowerOther] moved,
          upper := rest } := by
    have hNotRoute : ¬ value ≤ lowerRoot := by omega
    simp [LeanExperiments.RunningMedian.insert, hNotRoute,
      hLowerNoRebalance, hAfterUpper]
  rw [hResult]
  have hPartition := insert_partition
    ({ lower := #[lowerRoot, lowerOther], upper := #[upperRoot, upperOther] } :
      LeanExperiments.RunningMedian.State) value hInvariant.1
  have hFinalLowerBound : ∀ item,
      item ∈ (LeanExperiments.RunningMedian.insertHeap
        LeanExperiments.RunningMedian.maxPrefer #[lowerRoot, lowerOther] moved).toList →
        item ≤ moved := by
    apply insertHeap_le_of_forall_le LeanExperiments.RunningMedian.maxPrefer
      #[lowerRoot, lowerOther] moved moved
    · intro item hItem
      change item ∈ [lowerRoot, lowerOther] at hItem
      simp at hItem
      rcases hItem with hRoot | hOther
      · subst item
        exact hMovedLower
      · subst item
        exact Nat.le_trans hLowerOther hMovedLower
    · exact Nat.le_refl moved
  have hRestHeapOrdered : HeapOrdered minPrefer rest := by
    simpa [minPrefer, LeanExperiments.RunningMedian.minPrefer] using
      (minHeap_iff_HeapOrdered_minPrefer rest).mp hRestMinHeap
  refine ⟨?_, hLowerInsertedHeap, hRestHeapOrdered, ?_, ?_⟩
  · rw [hResult] at hPartition
    exact hPartition
  · intro lowerIndex hLowerIndex upperIndex hUpperIndex
    have hLowerMem :
        (LeanExperiments.RunningMedian.insertHeap LeanExperiments.RunningMedian.maxPrefer
          #[lowerRoot, lowerOther] moved)[lowerIndex]'hLowerIndex ∈
          (LeanExperiments.RunningMedian.insertHeap LeanExperiments.RunningMedian.maxPrefer
            #[lowerRoot, lowerOther] moved).toList :=
      Array.getElem_mem_toList hLowerIndex
    have hUpperBound := hRestGe upperIndex hUpperIndex
    exact Nat.le_trans (hFinalLowerBound _ hLowerMem) hUpperBound
  · simp [hPopSize, insertHeap_size]

/-- 長さ4の任意の不変状態で下側根以下の値を挿入する分岐は不変条件を保つ。

要素数と均衡条件から状態を2+2要素に特定し、値を列挙しない2+2挿入契約へ帰着する。
-/
theorem StateInvariant.insert_from_size_four_of_le_root {input : Array Nat}
    {state : LeanExperiments.RunningMedian.State}
    (hInvariant : StateInvariant input state) (hSize : input.size = 4)
    (value : Nat) (hValue : value ≤ state.lower[0]!) :
    StateInvariant (input.push value)
      (LeanExperiments.RunningMedian.insert state value) := by
  have hTotal := StateInvariant.size_partition hInvariant
  have hLowerSize : state.lower.size = 2 := by
    rcases hInvariant.2.2.2.2 with hBalanced | hLowerExtra <;> omega
  have hUpperSize : state.upper.size = 2 := by
    rcases hInvariant.2.2.2.2 with hBalanced | hLowerExtra <;> omega
  let lowerRoot := state.lower[0]'(by omega)
  let lowerOther := state.lower[1]'(by omega)
  let upperRoot := state.upper[0]'(by omega)
  let upperOther := state.upper[1]'(by omega)
  have hLowerEq : state.lower = #[lowerRoot, lowerOther] := by
    apply Array.ext
    · exact hLowerSize
    · intro index hIndex hBound
      have hCases : index = 0 ∨ index = 1 := by omega
      rcases hCases with hZero | hOne
      · subst index
        simp [lowerRoot]
      · subst index
        simp [lowerOther]
  have hUpperEq : state.upper = #[upperRoot, upperOther] := by
    apply Array.ext
    · exact hUpperSize
    · intro index hIndex hBound
      have hCases : index = 0 ∨ index = 1 := by omega
      rcases hCases with hZero | hOne
      · subst index
        simp [upperRoot]
      · subst index
        simp [upperOther]
  have hState : state =
      { lower := #[lowerRoot, lowerOther], upper := #[upperRoot, upperOther] } := by
    cases state with
    | mk lower upper =>
        simp only [LeanExperiments.RunningMedian.State.mk.injEq]
        exact ⟨hLowerEq, hUpperEq⟩
  have hRootValue : value ≤ lowerRoot := by
    have hBang : state.lower[0]! = state.lower[0]'(by omega) :=
      getElem!_pos state.lower 0 (by omega)
    simpa [lowerRoot, hBang] using hValue
  exact StateInvariant.insert_from_two_two_of_le_root
    hInvariant hState hRootValue

/-- 長さ4の任意の不変状態で下側根より大きい値を挿入する分岐は不変条件を保つ。 -/
theorem StateInvariant.insert_from_size_four_of_gt_root {input : Array Nat}
    {state : LeanExperiments.RunningMedian.State}
    (hInvariant : StateInvariant input state) (hSize : input.size = 4)
    (value : Nat) (hValue : state.lower[0]! < value) :
    StateInvariant (input.push value)
      (LeanExperiments.RunningMedian.insert state value) := by
  have hTotal := StateInvariant.size_partition hInvariant
  have hLowerSize : state.lower.size = 2 := by
    rcases hInvariant.2.2.2.2 with hBalanced | hLowerExtra <;> omega
  have hUpperSize : state.upper.size = 2 := by
    rcases hInvariant.2.2.2.2 with hBalanced | hLowerExtra <;> omega
  let lowerRoot := state.lower[0]'(by omega)
  let lowerOther := state.lower[1]'(by omega)
  let upperRoot := state.upper[0]'(by omega)
  let upperOther := state.upper[1]'(by omega)
  have hLowerEq : state.lower = #[lowerRoot, lowerOther] := by
    apply Array.ext
    · exact hLowerSize
    · intro index hIndex hBound
      have hCases : index = 0 ∨ index = 1 := by omega
      rcases hCases with hZero | hOne
      · subst index
        simp [lowerRoot]
      · subst index
        simp [lowerOther]
  have hUpperEq : state.upper = #[upperRoot, upperOther] := by
    apply Array.ext
    · exact hUpperSize
    · intro index hIndex hBound
      have hCases : index = 0 ∨ index = 1 := by omega
      rcases hCases with hZero | hOne
      · subst index
        simp [upperRoot]
      · subst index
        simp [upperOther]
  have hState : state =
      { lower := #[lowerRoot, lowerOther], upper := #[upperRoot, upperOther] } := by
    cases state with
    | mk lower upper =>
        simp only [LeanExperiments.RunningMedian.State.mk.injEq]
        exact ⟨hLowerEq, hUpperEq⟩
  have hRootValue : lowerRoot < value := by
    have hBang : state.lower[0]! = state.lower[0]'(by omega) :=
      getElem!_pos state.lower 0 (by omega)
    simpa [lowerRoot, hBang] using hValue
  exact StateInvariant.insert_from_two_two_of_gt_root
    hInvariant hState hRootValue

/-- 3+2要素の不変状態で下側根より大きい値を挿入すると不変条件を保つ。

値は上側へ入り、両ヒープが3要素になるため再平衡は停止する。 -/
theorem StateInvariant.insert_from_three_two_of_gt_root
    {input : Array Nat} {state : LeanExperiments.RunningMedian.State}
    (hInvariant : StateInvariant input state)
    {lowerRoot lowerLeft lowerRight upperRoot upperOther value : Nat}
    (hState : state = {
      lower := #[lowerRoot, lowerLeft, lowerRight],
      upper := #[upperRoot, upperOther] })
    (hValue : lowerRoot < value) :
    StateInvariant (input.push value)
      (LeanExperiments.RunningMedian.insert state value) := by
  rw [hState] at hInvariant ⊢
  have hUpperHeap := insertHeap_minPrefer_twoElements_preserves
    (value := value)
    ((minHeap_iff_HeapOrdered_minPrefer _).mpr hInvariant.2.2.1)
  have hUpperOrdered : HeapOrdered minPrefer
      (LeanExperiments.RunningMedian.insertHeap minPrefer
        #[upperRoot, upperOther] value) :=
    (minHeap_iff_HeapOrdered_minPrefer _).mp hUpperHeap
  have hBalanced : #[lowerRoot, lowerLeft, lowerRight].size =
      (LeanExperiments.RunningMedian.insertHeap minPrefer
        #[upperRoot, upperOther] value).size := by simp [insertHeap_size]
  have hRebalance := rebalanceLoops_eq_self_of_balanced_size
    #[lowerRoot, lowerLeft, lowerRight]
    (LeanExperiments.RunningMedian.insertHeap minPrefer
      #[upperRoot, upperOther] value) (Or.inl hBalanced)
  dsimp at hRebalance
  have hResult : LeanExperiments.RunningMedian.insert
      { lower := #[lowerRoot, lowerLeft, lowerRight],
        upper := #[upperRoot, upperOther] } value =
      { lower := #[lowerRoot, lowerLeft, lowerRight],
        upper := LeanExperiments.RunningMedian.insertHeap minPrefer
          #[upperRoot, upperOther] value } := by
    by_cases hRoute : value ≤ lowerRoot
    · omega
    · have hLowerResult := congrArg Prod.fst hRebalance
      have hUpperResult := congrArg Prod.snd hRebalance
      simp [LeanExperiments.RunningMedian.insert, hRoute]
      exact ⟨hLowerResult, hUpperResult⟩
  rw [hResult]
  let routedState : LeanExperiments.RunningMedian.State :=
    ⟨#[lowerRoot, lowerLeft, lowerRight], #[upperRoot, upperOther]⟩
  have hPartition := insert_partition
    routedState value (by simpa [routedState] using hInvariant.1)
  refine ⟨?_, hInvariant.2.1, hUpperOrdered, ?_, ?_⟩
  · rw [hResult] at hPartition
    exact hPartition
  · exact crossBoundary_insertUpper_of_gt_lowerRoot
      routedState value (by simp [routedState])
      (by simpa [routedState] using hInvariant.2.1)
      (by simpa [routedState] using hInvariant.2.2.2.1) hValue
  · simp [insertHeap_size]

/-- 3+2要素の不変状態で下側根以下の値を挿入しても不変条件を保つ。

下側最大ヒープへの挿入後、最大値を一度上側へ移す。最大値取り出し契約と残余要素の
上界、および上側への挿入後も維持される下界を合成して、ヒープ間境界を示す。
-/
theorem StateInvariant.insert_from_three_two_of_le_root
    {input : Array Nat} {state : LeanExperiments.RunningMedian.State}
    (hInvariant : StateInvariant input state)
    {lowerRoot lowerLeft lowerRight upperRoot upperOther value : Nat}
    (hState : state = {
      lower := #[lowerRoot, lowerLeft, lowerRight],
      upper := #[upperRoot, upperOther] })
    (hValue : value ≤ lowerRoot) :
    StateInvariant (input.push value)
      (LeanExperiments.RunningMedian.insert state value) := by
  rw [hState] at hInvariant ⊢
  let hLowerInserted := LeanExperiments.RunningMedian.insertHeap
    LeanExperiments.RunningMedian.maxPrefer #[lowerRoot, lowerLeft, lowerRight] value
  have hLowerInsertedSize : hLowerInserted.size = 4 := by
    simp [hLowerInserted, insertHeap_size]
  have hLowerInsertedHeap : HeapOrdered LeanExperiments.RunningMedian.maxPrefer hLowerInserted := by
    simpa [hLowerInserted] using
      insertHeap_maxPrefer_threeElements_preserves hInvariant.2.1
  have hMovedEq : hLowerInserted[0]! = lowerRoot := by
    simpa [hLowerInserted] using
      insertHeap_maxPrefer_root_eq_of_le #[lowerRoot, lowerLeft, lowerRight]
        value (by simp) hValue
  have hPopExists : ∃ rest,
      LeanExperiments.RunningMedian.popHeap maxPrefer hLowerInserted =
        some (lowerRoot, rest) := by
    cases hPop : LeanExperiments.RunningMedian.popHeap maxPrefer hLowerInserted with
    | none =>
        have hEmpty := (popHeap_eq_none_iff_empty maxPrefer hLowerInserted).mp hPop
        rw [hLowerInsertedSize] at hEmpty
        simp at hEmpty
    | some pair =>
        rcases pair with ⟨root, rest⟩
        have hRoot := popHeap_value_eq_root hPop
        have hRootValue : root = lowerRoot := by
          have hRoot' : hLowerInserted[0]? = some root := hRoot
          rw [getElem?_pos _ 0 (by omega)] at hRoot'
          have hEq := Option.some.inj hRoot'
          have hRootBang : hLowerInserted[0]! = root := by
            calc
              hLowerInserted[0]! = hLowerInserted[0]'(by omega) :=
                getElem!_pos hLowerInserted 0 (by omega)
              _ = root := hEq
          calc
            root = hLowerInserted[0]! := hRootBang.symm
            _ = lowerRoot := hMovedEq
        subst root
        exact ⟨rest, rfl⟩
  obtain ⟨rest, hPop⟩ := hPopExists
  have hPopCorrect := popHeap_maxPrefer_restCorrect_of_heapOrdered
    hLowerInserted hLowerInsertedHeap
  have hPopSpec :
      0 < hLowerInserted.size ∧
      hLowerInserted[0]? = some lowerRoot ∧
      LeanExperiments.Verification.HeapSort.Spec.MaxHeap rest ∧
      rest.toList.Perm (hLowerInserted.toList.drop 1) := by
    simpa [LeanExperiments.Verification.HeapSort.Spec.PopMaxRestCorrectFor, hPop]
      using hPopCorrect
  have hRestHeap : HeapOrdered LeanExperiments.RunningMedian.maxPrefer rest :=
    (heapSortMaxHeap_iff_HeapOrdered_maxPrefer rest).mp hPopSpec.2.2.1
  have hRestBound : ∀ item, item ∈ rest.toList → item ≤ lowerRoot := by
    simpa [hPop] using
      LeanExperiments.Verification.HeapSort.Spec.PopMaxRestCorrectFor.rest_le_maximum
        hPopCorrect
        ((heapSortMaxHeap_iff_HeapOrdered_maxPrefer _).mpr hLowerInsertedHeap)
  have hRestLe : ∀ index (hIndex : index < rest.size),
      rest[index]'hIndex ≤ lowerRoot := by
    intro index hIndex
    exact hRestBound _ (by simp)
  have hRestSize : rest.size = 3 := by
    have hSize := popHeap_size hPop
    omega
  have hUpperHeap : MinHeap #[upperRoot, upperOther] := by
    apply (minHeap_iff_HeapOrdered_minPrefer _).mpr
    simpa [minPrefer, LeanExperiments.RunningMedian.minPrefer] using hInvariant.2.2.1
  have hUpperBound : ∀ item, item ∈ #[upperRoot, upperOther].toList → lowerRoot ≤ item := by
    intro item hItem
    have hCases : item = upperRoot ∨ item = upperOther := by
      simpa using hItem
    rcases hCases with h | h
    · subst item
      exact hInvariant.2.2.2.1 0 (by simp) 0 (by simp)
    · subst item
      have hRootOther := (hUpperHeap 0 (by simp)).1 (by simp)
      exact Nat.le_trans (hInvariant.2.2.2.1 0 (by simp) 0 (by simp)) hRootOther
  let hUpperInserted := LeanExperiments.RunningMedian.insertHeap minPrefer
    #[upperRoot, upperOther] lowerRoot
  have hUpperInsertedHeap : MinHeap hUpperInserted :=
    insertHeap_minPrefer_twoElements_preserves hUpperHeap
  have hUpperInsertedOrdered : HeapOrdered minPrefer hUpperInserted := by
    apply (minHeap_iff_HeapOrdered_minPrefer _).mp
    simpa [hUpperInserted]
      using hUpperInsertedHeap
  have hUpperInsertedBound : ∀ item, item ∈ hUpperInserted.toList → lowerRoot ≤ item := by
    simpa [hUpperInserted] using
      (insertHeap_ge_of_forall_ge minPrefer #[upperRoot, upperOther] lowerRoot lowerRoot
        hUpperBound (Nat.le_refl lowerRoot))
  have hTransfer : LeanExperiments.RunningMedian.transferLowerRoot maxPrefer minPrefer
      hLowerInserted #[upperRoot, upperOther] = some (rest, hUpperInserted) := by
    simp [LeanExperiments.RunningMedian.transferLowerRoot, hPop, hUpperInserted]
  have hAfterLower := rebalanceLower_one_transfer hLowerInserted
    #[upperRoot, upperOther] rest hUpperInserted (by simp [hLowerInsertedSize])
    hTransfer (by simp [hRestSize, hUpperInserted, insertHeap_size])
  have hAfterUpper := rebalanceUpper_eq_self_of_size_le rest hUpperInserted
    (by simp [hRestSize, hUpperInserted, insertHeap_size])
  have hResult : LeanExperiments.RunningMedian.insert
      { lower := #[lowerRoot, lowerLeft, lowerRight],
        upper := #[upperRoot, upperOther] } value =
      { lower := rest, upper := hUpperInserted } := by
    simp [LeanExperiments.RunningMedian.insert, hValue]
    rw [hAfterLower, hAfterUpper]
    simp
  rw [hResult]
  let inputState : LeanExperiments.RunningMedian.State :=
    ⟨#[lowerRoot, lowerLeft, lowerRight], #[upperRoot, upperOther]⟩
  have hPartition := insert_partition inputState value
    (by simpa [inputState] using hInvariant.1)
  refine ⟨?_, hRestHeap, hUpperInsertedOrdered, ?_, ?_⟩
  · rw [hResult] at hPartition
    exact hPartition
  · intro lowerIndex hLowerIndex upperIndex hUpperIndex
    exact Nat.le_trans (hRestLe lowerIndex hLowerIndex)
      (hUpperInsertedBound _ (Array.getElem_mem_toList hUpperIndex))
  · simp [hRestSize, hUpperInserted, insertHeap_size]

/-- 長さ5の不変状態で下側根より大きい値を挿入する分岐は不変条件を保つ。 -/
theorem StateInvariant.insert_from_size_five_of_gt_root {input : Array Nat}
    {state : LeanExperiments.RunningMedian.State}
    (hInvariant : StateInvariant input state) (hSize : input.size = 5)
    (value : Nat) (hValue : state.lower[0]! < value) :
    StateInvariant (input.push value)
      (LeanExperiments.RunningMedian.insert state value) := by
  have hTotal := StateInvariant.size_partition hInvariant
  have hLowerSize : state.lower.size = 3 := by
    rcases hInvariant.2.2.2.2 with hBalanced | hLowerExtra <;> omega
  have hUpperSize : state.upper.size = 2 := by
    rcases hInvariant.2.2.2.2 with hBalanced | hLowerExtra <;> omega
  let lowerRoot := state.lower[0]'(by omega)
  let lowerLeft := state.lower[1]'(by omega)
  let lowerRight := state.lower[2]'(by omega)
  let upperRoot := state.upper[0]'(by omega)
  let upperOther := state.upper[1]'(by omega)
  have hLowerEq : state.lower = #[lowerRoot, lowerLeft, lowerRight] := by
    apply Array.ext
    · exact hLowerSize
    · intro index hIndex hBound
      have hCases : index = 0 ∨ index = 1 ∨ index = 2 := by omega
      rcases hCases with h | h | h <;> subst index
      · simp [lowerRoot]
      · simp [lowerLeft]
      · simp [lowerRight]
  have hUpperEq : state.upper = #[upperRoot, upperOther] := by
    apply Array.ext
    · exact hUpperSize
    · intro index hIndex hBound
      have hCases : index = 0 ∨ index = 1 := by omega
      rcases hCases with h | h <;> subst index
      · simp [upperRoot]
      · simp [upperOther]
  have hState : state = {
      lower := #[lowerRoot, lowerLeft, lowerRight],
      upper := #[upperRoot, upperOther] } := by
    cases state with
    | mk lower upper =>
        simp only [LeanExperiments.RunningMedian.State.mk.injEq]
        exact ⟨hLowerEq, hUpperEq⟩
  have hRootValue : lowerRoot < value := by
    have hBang : state.lower[0]! = state.lower[0]'(by omega) :=
      getElem!_pos state.lower 0 (by omega)
    simpa [lowerRoot, hBang] using hValue
  exact StateInvariant.insert_from_three_two_of_gt_root
    hInvariant hState hRootValue

/-- 長さ5の不変状態で下側根以下の値を挿入する分岐は不変条件を保つ。 -/
theorem StateInvariant.insert_from_size_five_of_le_root {input : Array Nat}
    {state : LeanExperiments.RunningMedian.State}
    (hInvariant : StateInvariant input state) (hSize : input.size = 5)
    (value : Nat) (hValue : value ≤ state.lower[0]!) :
    StateInvariant (input.push value)
      (LeanExperiments.RunningMedian.insert state value) := by
  have hTotal := StateInvariant.size_partition hInvariant
  have hLowerSize : state.lower.size = 3 := by
    rcases hInvariant.2.2.2.2 with hBalanced | hLowerExtra <;> omega
  have hUpperSize : state.upper.size = 2 := by
    rcases hInvariant.2.2.2.2 with hBalanced | hLowerExtra <;> omega
  let lowerRoot := state.lower[0]'(by omega)
  let lowerLeft := state.lower[1]'(by omega)
  let lowerRight := state.lower[2]'(by omega)
  let upperRoot := state.upper[0]'(by omega)
  let upperOther := state.upper[1]'(by omega)
  have hLowerEq : state.lower = #[lowerRoot, lowerLeft, lowerRight] := by
    apply Array.ext
    · exact hLowerSize
    · intro index hIndex hBound
      have hCases : index = 0 ∨ index = 1 ∨ index = 2 := by omega
      rcases hCases with h | h | h <;> subst index
      · simp [lowerRoot]
      · simp [lowerLeft]
      · simp [lowerRight]
  have hUpperEq : state.upper = #[upperRoot, upperOther] := by
    apply Array.ext
    · exact hUpperSize
    · intro index hIndex hBound
      have hCases : index = 0 ∨ index = 1 := by omega
      rcases hCases with h | h <;> subst index
      · simp [upperRoot]
      · simp [upperOther]
  have hState : state = {
      lower := #[lowerRoot, lowerLeft, lowerRight],
      upper := #[upperRoot, upperOther] } := by
    cases state with
    | mk lower upper =>
        simp only [LeanExperiments.RunningMedian.State.mk.injEq]
        exact ⟨hLowerEq, hUpperEq⟩
  have hRootValue : value ≤ lowerRoot := by
    have hBang : state.lower[0]! = state.lower[0]'(by omega) :=
      getElem!_pos state.lower 0 (by omega)
    simpa [lowerRoot, hBang] using hValue
  exact StateInvariant.insert_from_three_two_of_le_root
    hInvariant hState hRootValue

/-- 長さ5の任意の不変状態への挿入は不変条件を保つ。 -/
theorem StateInvariant.insert_of_size_five {input : Array Nat}
    {state : LeanExperiments.RunningMedian.State}
    (hInvariant : StateInvariant input state) (hSize : input.size = 5)
    (value : Nat) :
    StateInvariant (input.push value)
      (LeanExperiments.RunningMedian.insert state value) := by
  by_cases hRoot : state.lower[0]! < value
  · exact StateInvariant.insert_from_size_five_of_gt_root
      hInvariant hSize value hRoot
  · exact StateInvariant.insert_from_size_five_of_le_root
      hInvariant hSize value (by omega)

/-- 3+3要素の不変状態に下側根以下の値を挿入しても不変条件を保つ。

下側最大ヒープへの挿入後のサイズは4対3となり、再平衡は停止する。
挿入値が元の下側根以下であることから、ヒープ間境界も維持される。
-/
theorem StateInvariant.insert_from_three_three_of_le_root
    {input : Array Nat} {state : LeanExperiments.RunningMedian.State}
    (hInvariant : StateInvariant input state)
    {lowerRoot lowerLeft lowerRight upperRoot upperLeft upperRight value : Nat}
    (hState : state = {
      lower := #[lowerRoot, lowerLeft, lowerRight],
      upper := #[upperRoot, upperLeft, upperRight] })
    (hValue : value ≤ lowerRoot) :
    StateInvariant (input.push value)
      (LeanExperiments.RunningMedian.insert state value) := by
  rw [hState] at hInvariant ⊢
  let lowerInserted := LeanExperiments.RunningMedian.insertHeap
    LeanExperiments.RunningMedian.maxPrefer
    #[lowerRoot, lowerLeft, lowerRight] value
  have hLowerInsertedHeap : HeapOrdered LeanExperiments.RunningMedian.maxPrefer lowerInserted := by
    simpa [lowerInserted] using
      insertHeap_maxPrefer_threeElements_preserves hInvariant.2.1
  have hSize : lowerInserted.size = #[upperRoot, upperLeft, upperRight].size + 1 := by
    simp [lowerInserted, insertHeap_size]
  have hRebalance := rebalanceLoops_eq_self_of_balanced_size
    lowerInserted #[upperRoot, upperLeft, upperRight] (Or.inr hSize)
  dsimp at hRebalance
  have hResult : LeanExperiments.RunningMedian.insert
      { lower := #[lowerRoot, lowerLeft, lowerRight],
        upper := #[upperRoot, upperLeft, upperRight] } value =
      { lower := lowerInserted, upper := #[upperRoot, upperLeft, upperRight] } := by
    simp [LeanExperiments.RunningMedian.insert, hValue, lowerInserted]
    exact Prod.mk.inj hRebalance
  rw [hResult]
  let inputState : LeanExperiments.RunningMedian.State :=
    ⟨#[lowerRoot, lowerLeft, lowerRight], #[upperRoot, upperLeft, upperRight]⟩
  have hPartition := insert_partition inputState value
    (by simpa [inputState] using hInvariant.1)
  refine ⟨?_, hLowerInsertedHeap, hInvariant.2.2.1, ?_, ?_⟩
  · rw [hResult] at hPartition
    exact hPartition
  · exact crossBoundary_insertLower_of_le_lowerRoot
      inputState value (by simp [inputState])
      (by simpa [inputState] using hInvariant.2.2.2.1)
      hValue
  · simp [lowerInserted, insertHeap_size]

/-- 長さ6の任意の不変状態で下側根以下の値を挿入する分岐は不変条件を保つ。 -/
theorem StateInvariant.insert_from_size_six_of_le_root {input : Array Nat}
    {state : LeanExperiments.RunningMedian.State}
    (hInvariant : StateInvariant input state) (hSize : input.size = 6)
    (value : Nat) (hValue : value ≤ state.lower[0]!) :
    StateInvariant (input.push value)
      (LeanExperiments.RunningMedian.insert state value) := by
  have hTotal := StateInvariant.size_partition hInvariant
  have hLowerSize : state.lower.size = 3 := by
    rcases hInvariant.2.2.2.2 with hBalanced | hLowerExtra <;> omega
  have hUpperSize : state.upper.size = 3 := by
    rcases hInvariant.2.2.2.2 with hBalanced | hLowerExtra <;> omega
  let lowerRoot := state.lower[0]'(by omega)
  let lowerLeft := state.lower[1]'(by omega)
  let lowerRight := state.lower[2]'(by omega)
  let upperRoot := state.upper[0]'(by omega)
  let upperLeft := state.upper[1]'(by omega)
  let upperRight := state.upper[2]'(by omega)
  have hLowerEq : state.lower = #[lowerRoot, lowerLeft, lowerRight] := by
    apply Array.ext
    · exact hLowerSize
    · intro index hIndex hBound
      have hCases : index = 0 ∨ index = 1 ∨ index = 2 := by omega
      rcases hCases with h | h | h <;> subst index
      · simp [lowerRoot]
      · simp [lowerLeft]
      · simp [lowerRight]
  have hUpperEq : state.upper = #[upperRoot, upperLeft, upperRight] := by
    apply Array.ext
    · exact hUpperSize
    · intro index hIndex hBound
      have hCases : index = 0 ∨ index = 1 ∨ index = 2 := by omega
      rcases hCases with h | h | h <;> subst index
      · simp [upperRoot]
      · simp [upperLeft]
      · simp [upperRight]
  have hState : state = {
      lower := #[lowerRoot, lowerLeft, lowerRight],
      upper := #[upperRoot, upperLeft, upperRight] } := by
    cases state with
    | mk lower upper =>
        simp only [LeanExperiments.RunningMedian.State.mk.injEq]
        exact ⟨hLowerEq, hUpperEq⟩
  have hRootValue : value ≤ lowerRoot := by
    have hBang : state.lower[0]! = state.lower[0]'(by omega) :=
      getElem!_pos state.lower 0 (by omega)
    simpa [lowerRoot, hBang] using hValue
  exact StateInvariant.insert_from_three_three_of_le_root
    hInvariant hState hRootValue

/-- 3+3要素の不変状態で下側根より大きい値を挿入しても不変条件を保つ。

上側最小ヒープから最小値を一度下側へ移す。最小値取り出し契約により、移動値は
残余上側ヒープ以下となり、既存の下側要素も移動値以下であることから境界を示す。
-/
theorem StateInvariant.insert_from_three_three_of_gt_root
    {input : Array Nat} {state : LeanExperiments.RunningMedian.State}
    (hInvariant : StateInvariant input state)
    {lowerRoot lowerLeft lowerRight upperRoot upperLeft upperRight value : Nat}
    (hState : state = {
      lower := #[lowerRoot, lowerLeft, lowerRight],
      upper := #[upperRoot, upperLeft, upperRight] })
    (hValue : lowerRoot < value) :
    StateInvariant (input.push value)
      (LeanExperiments.RunningMedian.insert state value) := by
  rw [hState] at hInvariant ⊢
  let upperInserted := LeanExperiments.RunningMedian.insertHeap
    LeanExperiments.RunningMedian.minPrefer
    #[upperRoot, upperLeft, upperRight] value
  let upperInsertedLocal := LeanExperiments.RunningMedian.insertHeap
    minPrefer #[upperRoot, upperLeft, upperRight] value
  have hUpperInsertedEq : upperInsertedLocal = upperInserted := by rfl
  have hUpperHeap : MinHeap #[upperRoot, upperLeft, upperRight] := by
    apply (minHeap_iff_HeapOrdered_minPrefer _).mpr
    exact hInvariant.2.2.1
  have hUpperInsertedHeap : MinHeap upperInserted := by
    simpa [upperInserted] using insertHeap_minPrefer_threeElements_preserves hUpperHeap
  have hUpperInsertedSize : upperInserted.size = 4 := by
    simp [upperInserted, insertHeap_size]
  have hUpperInsertedPositive : 0 < upperInserted.size := by omega
  have hMovedLower : lowerRoot ≤ upperInserted[0]! := by
    have hBoundary := crossBoundary_insertUpper_of_gt_lowerRoot
      ({ lower := #[lowerRoot, lowerLeft, lowerRight],
         upper := #[upperRoot, upperLeft, upperRight] } : LeanExperiments.RunningMedian.State)
      value (by simp) hInvariant.2.1 hInvariant.2.2.2.1 hValue
    have hRoot := hBoundary 0 (by simp) 0 (by simp [insertHeap_size])
    have hRootLocal : lowerRoot ≤ upperInsertedLocal[0]'(by
        simp [upperInsertedLocal, insertHeap_size]) := by
      simpa [upperInsertedLocal] using hRoot
    have hRootLocalBang : lowerRoot ≤ upperInsertedLocal[0]! := by
      calc
        lowerRoot ≤ upperInsertedLocal[0]'(by simp [upperInsertedLocal, insertHeap_size]) := hRootLocal
        _ = upperInsertedLocal[0]! :=
          (getElem!_pos upperInsertedLocal 0 (by simp [upperInsertedLocal, insertHeap_size])).symm
    have hRootEq : upperInsertedLocal[0]! = upperInserted[0]! := by
      exact congrArg (fun heap : Array Nat => heap[0]!) hUpperInsertedEq
    exact Nat.le_trans hRootLocalBang (by rw [← hRootEq]; exact Nat.le_refl _)
  let moved := upperInserted[0]!
  have hPopExists : ∃ rest,
      LeanExperiments.RunningMedian.popHeap LeanExperiments.RunningMedian.minPrefer
        upperInserted = some (moved, rest) := by
    cases hPop : LeanExperiments.RunningMedian.popHeap
        LeanExperiments.RunningMedian.minPrefer upperInserted with
    | none =>
        have hEmpty := (popHeap_eq_none_iff_empty
          LeanExperiments.RunningMedian.minPrefer upperInserted).mp hPop
        have hSize : upperInserted.size = 4 := by simp [upperInserted, insertHeap_size]
        rw [hSize] at hEmpty
        simp at hEmpty
    | some pair =>
        rcases pair with ⟨root, rest⟩
        have hRoot := popHeap_value_eq_root hPop
        have hRootValue : root = moved := by
          have hRoot' : upperInserted[0]? = some root := hRoot
          have hPositive : 0 < upperInserted.size := by
            simp [upperInserted, insertHeap_size]
          rw [getElem?_pos _ 0 hPositive] at hRoot'
          have hEq := Option.some.inj hRoot'
          have hRootBang : upperInserted[0]! = root := by
            calc
              upperInserted[0]! = upperInserted[0]'hPositive :=
                getElem!_pos upperInserted 0 hPositive
              _ = root := hEq
          exact hRootBang.symm
        subst root
        exact ⟨rest, rfl⟩
  obtain ⟨rest, hPop⟩ := hPopExists
  have hRestMinHeap : MinHeap rest :=
    popHeap_minPrefer_restMinHeap_of_MinHeap hUpperInsertedHeap hPop
  have hMovedMinimum := popHeap_minPrefer_returns_minimum_of_MinHeap
    hUpperInsertedHeap hPop
  have hRestSize : rest.size = 3 := by
    have hSize := popHeap_size hPop
    simp [upperInserted, insertHeap_size] at hSize
    omega
  have hRestGe : ∀ index (hIndex : index < rest.size),
      moved ≤ rest[index]'hIndex := by
    intro index hIndex
    have hPerm := popHeap_perm_dropRoot hPop
    have hMem : rest[index]'hIndex ∈ rest.toList := by simp
    have hInTail : rest[index]'hIndex ∈ upperInserted.toList.drop 1 :=
      hPerm.mem_iff.mp hMem
    have hInHeap := List.mem_of_mem_drop hInTail
    have hInArray : rest[index]'hIndex ∈ upperInserted := by simpa using hInHeap
    obtain ⟨heapIndex, hIndexArray, hAt⟩ := Array.mem_iff_getElem.mp hInArray
    have hAtBang : upperInserted[heapIndex]! = rest[index]'hIndex := by
      rw [getElem!_pos _ heapIndex hIndexArray]
      exact hAt
    calc
      moved = upperInserted[0]! := rfl
      _ ≤ upperInserted[heapIndex]! := hMovedMinimum heapIndex hIndexArray
      _ = rest[index]'hIndex := hAtBang
  have hLowerBound : ∀ item, item ∈ #[lowerRoot, lowerLeft, lowerRight].toList →
      item ≤ moved := by
    intro item hItem
    have hInArray : item ∈ #[lowerRoot, lowerLeft, lowerRight] := by simpa using hItem
    obtain ⟨index, hIndex, hAt⟩ := Array.mem_iff_getElem.mp hInArray
    have hRootMax := maxHeap_root_is_maximum
      #[lowerRoot, lowerLeft, lowerRight] hInvariant.2.1 index hIndex
    have hAtRoot : #[lowerRoot, lowerLeft, lowerRight][0]! = lowerRoot := by simp
    have hAtValue : #[lowerRoot, lowerLeft, lowerRight][index]! = item := by
      rw [getElem!_pos _ index hIndex]
      exact hAt
    rw [hAtValue, hAtRoot] at hRootMax
    exact Nat.le_trans hRootMax hMovedLower
  let lowerInserted := LeanExperiments.RunningMedian.insertHeap
    LeanExperiments.RunningMedian.maxPrefer
    #[lowerRoot, lowerLeft, lowerRight] moved
  have hLowerInsertedHeap : HeapOrdered LeanExperiments.RunningMedian.maxPrefer lowerInserted := by
    simpa [lowerInserted] using
      insertHeap_maxPrefer_threeElements_preserves (value := moved) hInvariant.2.1
  have hLowerInsertedBound : ∀ item, item ∈ lowerInserted.toList → item ≤ moved := by
    simpa [lowerInserted] using
      (insertHeap_le_of_forall_le LeanExperiments.RunningMedian.maxPrefer
        #[lowerRoot, lowerLeft, lowerRight] moved moved hLowerBound (Nat.le_refl moved))
  have hTransfer : LeanExperiments.RunningMedian.transferUpperRoot
      LeanExperiments.RunningMedian.minPrefer LeanExperiments.RunningMedian.maxPrefer
      #[lowerRoot, lowerLeft, lowerRight] upperInserted = some (lowerInserted, rest) := by
    simp [LeanExperiments.RunningMedian.transferUpperRoot, hPop, lowerInserted, moved]
  have hAfterLower := rebalanceLower_eq_self_of_size_le
    #[lowerRoot, lowerLeft, lowerRight] upperInserted (by simp [upperInserted, insertHeap_size])
  have hAfterUpper := rebalanceUpper_one_transfer
    #[lowerRoot, lowerLeft, lowerRight] upperInserted lowerInserted rest
    (by simp [upperInserted, insertHeap_size]) hTransfer (by
      calc
        rest.size ≤ 3 := by omega
        _ ≤ lowerInserted.size := by simp [lowerInserted, insertHeap_size])
  have hResult : LeanExperiments.RunningMedian.insert
      { lower := #[lowerRoot, lowerLeft, lowerRight],
        upper := #[upperRoot, upperLeft, upperRight] } value =
      { lower := lowerInserted, upper := rest } := by
    have hNotRoute : ¬ value ≤ lowerRoot := by omega
    simp [LeanExperiments.RunningMedian.insert, hNotRoute,
      upperInserted, hAfterLower, hAfterUpper]
  rw [hResult]
  have hPartition := insert_partition
    ({ lower := #[lowerRoot, lowerLeft, lowerRight],
       upper := #[upperRoot, upperLeft, upperRight] } : LeanExperiments.RunningMedian.State)
    value hInvariant.1
  refine ⟨?_, hLowerInsertedHeap, ?_, ?_, ?_⟩
  · rw [hResult] at hPartition
    exact hPartition
  · exact (minHeap_iff_HeapOrdered_minPrefer rest).mp hRestMinHeap
  · intro lowerIndex hLowerIndex upperIndex hUpperIndex
    have hLowerLeMoved := hLowerInsertedBound _
      (Array.getElem_mem_toList hLowerIndex)
    exact Nat.le_trans hLowerLeMoved (hRestGe upperIndex hUpperIndex)
  · simp [lowerInserted, hRestSize, insertHeap_size]

/-- 4+3要素の不変状態に下側根以下の値を挿入しても不変条件を保つ。 -/
theorem StateInvariant.insert_from_four_three_of_le_root
    {input : Array Nat} {state : LeanExperiments.RunningMedian.State}
    (hInvariant : StateInvariant input state)
    {lowerRoot lowerLeft lowerMiddle lowerRight upperRoot upperLeft upperRight value : Nat}
    (hState : state = {
      lower := #[lowerRoot, lowerLeft, lowerMiddle, lowerRight],
      upper := #[upperRoot, upperLeft, upperRight] })
    (hValue : value ≤ lowerRoot) :
    StateInvariant (input.push value)
      (LeanExperiments.RunningMedian.insert state value) := by
  rw [hState] at hInvariant ⊢
  let lowerInserted := LeanExperiments.RunningMedian.insertHeap
    LeanExperiments.RunningMedian.maxPrefer
    #[lowerRoot, lowerLeft, lowerMiddle, lowerRight] value
  have hLowerInsertedSize : lowerInserted.size = 5 := by
    simp [lowerInserted, insertHeap_size]
  have hLowerInsertedHeap : HeapOrdered LeanExperiments.RunningMedian.maxPrefer lowerInserted := by
    simpa [lowerInserted] using
      insertHeap_maxPrefer_fourElements_preserves hInvariant.2.1
  have hMovedEq : lowerInserted[0]! = lowerRoot := by
    simpa [lowerInserted] using
      insertHeap_maxPrefer_root_eq_of_le #[lowerRoot, lowerLeft, lowerMiddle, lowerRight]
        value (by simp) hValue
  have hPopExists : ∃ rest,
      LeanExperiments.RunningMedian.popHeap maxPrefer lowerInserted =
        some (lowerRoot, rest) := by
    cases hPop : LeanExperiments.RunningMedian.popHeap maxPrefer lowerInserted with
    | none =>
        have hEmpty := (popHeap_eq_none_iff_empty maxPrefer lowerInserted).mp hPop
        rw [hLowerInsertedSize] at hEmpty
        simp at hEmpty
    | some pair =>
        rcases pair with ⟨root, rest⟩
        have hRoot := popHeap_value_eq_root hPop
        have hRootValue : root = lowerRoot := by
          have hRoot' : lowerInserted[0]? = some root := hRoot
          rw [getElem?_pos _ 0 (by omega)] at hRoot'
          have hEq := Option.some.inj hRoot'
          have hRootBang : lowerInserted[0]! = root := by
            calc
              lowerInserted[0]! = lowerInserted[0]'(by omega) :=
                getElem!_pos lowerInserted 0 (by omega)
              _ = root := hEq
          calc
            root = lowerInserted[0]! := hRootBang.symm
            _ = lowerRoot := hMovedEq
        subst root
        exact ⟨rest, rfl⟩
  obtain ⟨rest, hPop⟩ := hPopExists
  have hPopCorrect := popHeap_maxPrefer_restCorrect_of_heapOrdered
    lowerInserted hLowerInsertedHeap
  have hPopSpec :
      0 < lowerInserted.size ∧
      lowerInserted[0]? = some lowerRoot ∧
      LeanExperiments.Verification.HeapSort.Spec.MaxHeap rest ∧
      rest.toList.Perm (lowerInserted.toList.drop 1) := by
    simpa [LeanExperiments.Verification.HeapSort.Spec.PopMaxRestCorrectFor, hPop]
      using hPopCorrect
  have hRestHeap : HeapOrdered LeanExperiments.RunningMedian.maxPrefer rest :=
    (heapSortMaxHeap_iff_HeapOrdered_maxPrefer rest).mp hPopSpec.2.2.1
  have hRestBound : ∀ item, item ∈ rest.toList → item ≤ lowerRoot := by
    simpa [hPop] using
      LeanExperiments.Verification.HeapSort.Spec.PopMaxRestCorrectFor.rest_le_maximum
        hPopCorrect
        ((heapSortMaxHeap_iff_HeapOrdered_maxPrefer _).mpr hLowerInsertedHeap)
  have hRestLe : ∀ index (hIndex : index < rest.size),
      rest[index]'hIndex ≤ lowerRoot := by
    intro index hIndex
    exact hRestBound _ (by simp)
  have hRestSize : rest.size = 4 := by
    have hSize := popHeap_size hPop
    omega
  have hUpperHeap : MinHeap #[upperRoot, upperLeft, upperRight] := by
    apply (minHeap_iff_HeapOrdered_minPrefer _).mpr
    simpa [minPrefer, LeanExperiments.RunningMedian.minPrefer] using hInvariant.2.2.1
  let upperInserted := LeanExperiments.RunningMedian.insertHeap
    LeanExperiments.RunningMedian.minPrefer
    #[upperRoot, upperLeft, upperRight] lowerRoot
  let upperInsertedLocal := LeanExperiments.RunningMedian.insertHeap minPrefer
    #[upperRoot, upperLeft, upperRight] lowerRoot
  have hUpperInsertedEq : upperInsertedLocal = upperInserted := by rfl
  have hUpperInsertedSize : upperInserted.size = 4 := by
    simp [upperInserted, insertHeap_size]
  have hUpperInsertedHeap : MinHeap upperInserted := by
    simpa [upperInserted] using insertHeap_minPrefer_threeElements_preserves hUpperHeap
  have hUpperInsertedOrdered : HeapOrdered minPrefer upperInserted := by
    apply (minHeap_iff_HeapOrdered_minPrefer _).mp
    simpa [upperInserted, minPrefer, LeanExperiments.RunningMedian.minPrefer] using hUpperInsertedHeap
  have hUpperInsertedBound : ∀ item, item ∈ upperInserted.toList → lowerRoot ≤ item := by
    intro item hItem
    have hInArray : item ∈ upperInserted := by simpa using hItem
    obtain ⟨index, hIndex, hAt⟩ := Array.mem_iff_getElem.mp hInArray
    have hCross := crossBoundary_insertUpper
      ({ lower := #[lowerRoot, lowerLeft, lowerMiddle, lowerRight],
         upper := #[upperRoot, upperLeft, upperRight] } : LeanExperiments.RunningMedian.State)
      lowerRoot hInvariant.2.2.2.1 (by
        intro lowerIndex hLowerIndex
        have hMaximum := maxHeap_root_is_maximum
          #[lowerRoot, lowerLeft, lowerMiddle, lowerRight]
          hInvariant.2.1 lowerIndex hLowerIndex
        have hMaximumBang :
            #[lowerRoot, lowerLeft, lowerMiddle, lowerRight][lowerIndex]! ≤ lowerRoot := by
          simpa using hMaximum
        rw [← getElem!_pos _ lowerIndex hLowerIndex]
        exact hMaximumBang)
    have hLocalIndex : index < upperInsertedLocal.size := by
      have hIndexFour : index < 4 := by simpa [upperInserted, insertHeap_size] using hIndex
      simpa [upperInsertedLocal, insertHeap_size] using hIndexFour
    have hRootCross := hCross 0 (by simp) index hLocalIndex
    have hRootCrossBang : lowerRoot ≤ upperInsertedLocal[index]! := by
      calc
        lowerRoot ≤ upperInsertedLocal[index]'hLocalIndex := hRootCross
        _ = upperInsertedLocal[index]! :=
          (getElem!_pos upperInsertedLocal index hLocalIndex).symm
    have hArrayIndex : upperInsertedLocal[index]! = upperInserted[index]! :=
      congrArg (fun heap : Array Nat => heap[index]!) hUpperInsertedEq
    have hAtBang : upperInserted[index]! = item := by
      rw [getElem!_pos upperInserted index hIndex]
      exact hAt
    calc
      lowerRoot ≤ upperInsertedLocal[index]! := hRootCrossBang
      _ = upperInserted[index]! := hArrayIndex
      _ = item := hAtBang
  have hTransfer : LeanExperiments.RunningMedian.transferLowerRoot maxPrefer minPrefer
      lowerInserted #[upperRoot, upperLeft, upperRight] = some (rest, upperInserted) := by
    rw [← hUpperInsertedEq]
    simp [LeanExperiments.RunningMedian.transferLowerRoot, hPop]
    rfl
  have hAfterLower := rebalanceLower_one_transfer lowerInserted
    #[upperRoot, upperLeft, upperRight] rest upperInserted
    (by simp [hLowerInsertedSize]) hTransfer
    (by simp [hRestSize, upperInserted, insertHeap_size])
  have hAfterUpper := rebalanceUpper_eq_self_of_size_le rest upperInserted
    (by simp [hRestSize, upperInserted, insertHeap_size])
  have hResult : LeanExperiments.RunningMedian.insert
      { lower := #[lowerRoot, lowerLeft, lowerMiddle, lowerRight],
        upper := #[upperRoot, upperLeft, upperRight] } value =
      { lower := rest, upper := upperInserted } := by
    simp [LeanExperiments.RunningMedian.insert, hValue]
    rw [hAfterLower, hAfterUpper]
    simp
  rw [hResult]
  let inputState : LeanExperiments.RunningMedian.State :=
    ⟨#[lowerRoot, lowerLeft, lowerMiddle, lowerRight], #[upperRoot, upperLeft, upperRight]⟩
  have hPartition := insert_partition inputState value
    (by simpa [inputState] using hInvariant.1)
  refine ⟨?_, hRestHeap, hUpperInsertedOrdered, ?_, ?_⟩
  · rw [hResult] at hPartition
    exact hPartition
  · intro lowerIndex hLowerIndex upperIndex hUpperIndex
    exact Nat.le_trans (hRestLe lowerIndex hLowerIndex)
      (hUpperInsertedBound _ (Array.getElem_mem_toList hUpperIndex))
  · simp [hRestSize, upperInserted, insertHeap_size]

/-- 4+4要素の不変状態で下側根以下の値を挿入しても不変条件を保つ。

挿入後はサイズ5対4となるため再平衡は停止する。根以下という挿入条件から、
下側への追加後もヒープ間境界が成り立つ。
-/
theorem StateInvariant.insert_from_four_four_of_le_root
    {input : Array Nat} {state : LeanExperiments.RunningMedian.State}
    (hInvariant : StateInvariant input state)
    {lowerRoot lowerLeft lowerMiddle lowerRight upperRoot upperLeft upperMiddle upperRight value : Nat}
    (hState : state = {
      lower := #[lowerRoot, lowerLeft, lowerMiddle, lowerRight],
      upper := #[upperRoot, upperLeft, upperMiddle, upperRight] })
    (hValue : value ≤ lowerRoot) :
    StateInvariant (input.push value)
      (LeanExperiments.RunningMedian.insert state value) := by
  rw [hState] at hInvariant ⊢
  let lowerInserted := LeanExperiments.RunningMedian.insertHeap
    LeanExperiments.RunningMedian.maxPrefer
    #[lowerRoot, lowerLeft, lowerMiddle, lowerRight] value
  have hLowerHeap : HeapOrdered LeanExperiments.RunningMedian.maxPrefer lowerInserted := by
    simpa [lowerInserted] using
      insertHeap_maxPrefer_fourElements_preserves hInvariant.2.1
  have hBalanced : lowerInserted.size =
      #[upperRoot, upperLeft, upperMiddle, upperRight].size + 1 := by
    simp [lowerInserted, insertHeap_size]
  have hRebalance := rebalanceLoops_eq_self_of_balanced_size lowerInserted
    #[upperRoot, upperLeft, upperMiddle, upperRight] (Or.inr hBalanced)
  dsimp at hRebalance
  have hResult : LeanExperiments.RunningMedian.insert
      { lower := #[lowerRoot, lowerLeft, lowerMiddle, lowerRight],
        upper := #[upperRoot, upperLeft, upperMiddle, upperRight] } value =
      { lower := lowerInserted, upper := #[upperRoot, upperLeft, upperMiddle, upperRight] } := by
    simp [LeanExperiments.RunningMedian.insert, hValue, lowerInserted]
    exact Prod.mk.inj hRebalance
  rw [hResult]
  let inputState : LeanExperiments.RunningMedian.State :=
    ⟨#[lowerRoot, lowerLeft, lowerMiddle, lowerRight],
      #[upperRoot, upperLeft, upperMiddle, upperRight]⟩
  have hPartition := insert_partition inputState value
    (by simpa [inputState] using hInvariant.1)
  refine ⟨?_, hLowerHeap, hInvariant.2.2.1, ?_, ?_⟩
  · rw [hResult] at hPartition
    exact hPartition
  · exact crossBoundary_insertLower_of_le_lowerRoot inputState value (by simp [inputState])
      (by simpa [inputState] using hInvariant.2.2.2.1) hValue
  · simp [lowerInserted, insertHeap_size]

/-- 4+4要素の不変状態で下側根より大きい値を挿入しても不変条件を保つ。

上側最小ヒープへの挿入後、その根を一度下側へ移す。取り出された最小値と下側根の
大小関係、残余上側ヒープの下界を使ってヒープ間境界を保つ。
-/
theorem StateInvariant.insert_from_four_four_of_gt_root
    {input : Array Nat} {state : LeanExperiments.RunningMedian.State}
    (hInvariant : StateInvariant input state)
    {lowerRoot lowerLeft lowerMiddle lowerRight upperRoot upperLeft upperMiddle upperRight value : Nat}
    (hState : state = {
      lower := #[lowerRoot, lowerLeft, lowerMiddle, lowerRight],
      upper := #[upperRoot, upperLeft, upperMiddle, upperRight] })
    (hValue : lowerRoot < value) :
    StateInvariant (input.push value)
      (LeanExperiments.RunningMedian.insert state value) := by
  rw [hState] at hInvariant ⊢
  let upperInserted := LeanExperiments.RunningMedian.insertHeap
    LeanExperiments.RunningMedian.minPrefer
    #[upperRoot, upperLeft, upperMiddle, upperRight] value
  let upperInsertedLocal := LeanExperiments.RunningMedian.insertHeap minPrefer
    #[upperRoot, upperLeft, upperMiddle, upperRight] value
  have hUpperInsertedEq : upperInsertedLocal = upperInserted := by rfl
  have hUpperHeap : MinHeap #[upperRoot, upperLeft, upperMiddle, upperRight] := by
    apply (minHeap_iff_HeapOrdered_minPrefer _).mpr
    exact hInvariant.2.2.1
  have hUpperInsertedHeap : MinHeap upperInserted := by
    simpa [upperInserted] using insertHeap_minPrefer_fourElements_preserves hUpperHeap
  have hUpperInsertedOrdered : HeapOrdered minPrefer upperInserted :=
    (minHeap_iff_HeapOrdered_minPrefer _).mp hUpperInsertedHeap
  have hUpperInsertedSize : upperInserted.size = 5 := by
    simp [upperInserted, insertHeap_size]
  have hMovedLower : lowerRoot ≤ upperInserted[0]! := by
    have hBoundary := crossBoundary_insertUpper_of_gt_lowerRoot
      ({ lower := #[lowerRoot, lowerLeft, lowerMiddle, lowerRight],
         upper := #[upperRoot, upperLeft, upperMiddle, upperRight] } : LeanExperiments.RunningMedian.State)
      value (by simp) hInvariant.2.1 hInvariant.2.2.2.1 hValue
    have hRoot := hBoundary 0 (by simp) 0 (by simp [insertHeap_size])
    have hRootLocal : lowerRoot ≤ upperInsertedLocal[0]'(by
        simp [upperInsertedLocal, insertHeap_size]) := by
      simpa [upperInsertedLocal] using hRoot
    have hRootBang : lowerRoot ≤ upperInsertedLocal[0]! := by
      calc
        lowerRoot ≤ upperInsertedLocal[0]'(by simp [upperInsertedLocal, insertHeap_size]) := hRootLocal
        _ = upperInsertedLocal[0]! :=
          (getElem!_pos upperInsertedLocal 0 (by simp [upperInsertedLocal, insertHeap_size])).symm
    have hRootEq : upperInsertedLocal[0]! = upperInserted[0]! :=
      congrArg (fun heap : Array Nat => heap[0]!) hUpperInsertedEq
    exact Nat.le_trans hRootBang (Nat.le_of_eq hRootEq)
  let moved := upperInserted[0]!
  have hPopExists : ∃ rest,
      LeanExperiments.RunningMedian.popHeap LeanExperiments.RunningMedian.minPrefer
        upperInserted = some (moved, rest) := by
    cases hPop : LeanExperiments.RunningMedian.popHeap
        LeanExperiments.RunningMedian.minPrefer upperInserted with
    | none =>
        have hEmpty := (popHeap_eq_none_iff_empty
          LeanExperiments.RunningMedian.minPrefer upperInserted).mp hPop
        rw [hUpperInsertedSize] at hEmpty
        simp at hEmpty
    | some pair =>
        rcases pair with ⟨root, rest⟩
        have hRoot := popHeap_value_eq_root hPop
        have hRootValue : root = moved := by
          have hRoot' : upperInserted[0]? = some root := hRoot
          rw [getElem?_pos _ 0 (by omega)] at hRoot'
          have hEq := Option.some.inj hRoot'
          have hRootBang : upperInserted[0]! = root := by
            calc
              upperInserted[0]! = upperInserted[0]'(by omega) :=
                getElem!_pos upperInserted 0 (by omega)
              _ = root := hEq
          exact hRootBang.symm
        subst root
        exact ⟨rest, rfl⟩
  obtain ⟨rest, hPop⟩ := hPopExists
  have hRestHeap : MinHeap rest :=
    popHeap_minPrefer_restMinHeap_of_MinHeap hUpperInsertedHeap hPop
  have hMovedMinimum := popHeap_minPrefer_returns_minimum_of_MinHeap
    hUpperInsertedHeap hPop
  have hRestSize : rest.size = 4 := by
    have hSize := popHeap_size hPop
    simp [upperInserted, insertHeap_size] at hSize
    omega
  have hRestGe : ∀ index (hIndex : index < rest.size),
      moved ≤ rest[index]'hIndex := by
    intro index hIndex
    have hPerm := popHeap_perm_dropRoot hPop
    have hMem : rest[index]'hIndex ∈ rest.toList := by simp
    have hInTail : rest[index]'hIndex ∈ upperInserted.toList.drop 1 :=
      hPerm.mem_iff.mp hMem
    have hInHeap := List.mem_of_mem_drop hInTail
    have hInArray : rest[index]'hIndex ∈ upperInserted := by simpa using hInHeap
    obtain ⟨heapIndex, hIndexArray, hAt⟩ := Array.mem_iff_getElem.mp hInArray
    have hAtBang : upperInserted[heapIndex]! = rest[index]'hIndex := by
      rw [getElem!_pos _ heapIndex hIndexArray]
      exact hAt
    calc
      moved = upperInserted[0]! := rfl
      _ ≤ upperInserted[heapIndex]! := hMovedMinimum heapIndex hIndexArray
      _ = rest[index]'hIndex := hAtBang
  have hLowerBound : ∀ item,
      item ∈ #[lowerRoot, lowerLeft, lowerMiddle, lowerRight].toList → item ≤ moved := by
    intro item hItem
    have hInArray : item ∈ #[lowerRoot, lowerLeft, lowerMiddle, lowerRight] := by
      simpa using hItem
    obtain ⟨index, hIndex, hAt⟩ := Array.mem_iff_getElem.mp hInArray
    have hMaximum := maxHeap_root_is_maximum
      #[lowerRoot, lowerLeft, lowerMiddle, lowerRight] hInvariant.2.1 index hIndex
    have hAtBang : #[lowerRoot, lowerLeft, lowerMiddle, lowerRight][index]! = item := by
      rw [getElem!_pos _ index hIndex]
      exact hAt
    have hMaximumBang :
        #[lowerRoot, lowerLeft, lowerMiddle, lowerRight][index]! ≤ lowerRoot := by
      simpa using hMaximum
    rw [hAtBang] at hMaximumBang
    exact Nat.le_trans hMaximumBang hMovedLower
  let lowerInserted := LeanExperiments.RunningMedian.insertHeap
    LeanExperiments.RunningMedian.maxPrefer
    #[lowerRoot, lowerLeft, lowerMiddle, lowerRight] moved
  have hLowerInsertedHeap : HeapOrdered LeanExperiments.RunningMedian.maxPrefer lowerInserted := by
    simpa [lowerInserted] using
      insertHeap_maxPrefer_fourElements_preserves (value := moved) hInvariant.2.1
  have hLowerInsertedBound : ∀ item, item ∈ lowerInserted.toList → item ≤ moved := by
    simpa [lowerInserted] using
      (insertHeap_le_of_forall_le LeanExperiments.RunningMedian.maxPrefer
        #[lowerRoot, lowerLeft, lowerMiddle, lowerRight] moved moved
        hLowerBound (Nat.le_refl moved))
  have hTransfer : LeanExperiments.RunningMedian.transferUpperRoot
      LeanExperiments.RunningMedian.minPrefer LeanExperiments.RunningMedian.maxPrefer
      #[lowerRoot, lowerLeft, lowerMiddle, lowerRight] upperInserted =
        some (lowerInserted, rest) := by
    simp [LeanExperiments.RunningMedian.transferUpperRoot, hPop, lowerInserted, moved]
  have hAfterLower := rebalanceLower_eq_self_of_size_le
    #[lowerRoot, lowerLeft, lowerMiddle, lowerRight] upperInserted
    (by simp [upperInserted, insertHeap_size])
  have hAfterUpper := rebalanceUpper_one_transfer
    #[lowerRoot, lowerLeft, lowerMiddle, lowerRight] upperInserted lowerInserted rest
    (by simp [upperInserted, insertHeap_size]) hTransfer (by
      calc
        rest.size ≤ 4 := by omega
        _ ≤ lowerInserted.size := by simp [lowerInserted, insertHeap_size])
  have hResult : LeanExperiments.RunningMedian.insert
      { lower := #[lowerRoot, lowerLeft, lowerMiddle, lowerRight],
        upper := #[upperRoot, upperLeft, upperMiddle, upperRight] } value =
      { lower := lowerInserted, upper := rest } := by
    have hNotRoute : ¬ value ≤ lowerRoot := by omega
    simp [LeanExperiments.RunningMedian.insert, hNotRoute,
      upperInserted, hAfterLower, hAfterUpper]
  rw [hResult]
  let inputState : LeanExperiments.RunningMedian.State :=
    ⟨#[lowerRoot, lowerLeft, lowerMiddle, lowerRight],
      #[upperRoot, upperLeft, upperMiddle, upperRight]⟩
  have hPartition := insert_partition inputState value
    (by simpa [inputState] using hInvariant.1)
  refine ⟨?_, hLowerInsertedHeap, (minHeap_iff_HeapOrdered_minPrefer _).mp hRestHeap,
    ?_, ?_⟩
  · rw [hResult] at hPartition
    exact hPartition
  · intro lowerIndex hLowerIndex upperIndex hUpperIndex
    exact Nat.le_trans
      (hLowerInsertedBound _ (Array.getElem_mem_toList hLowerIndex))
      (hRestGe upperIndex hUpperIndex)
  · simp [lowerInserted, hRestSize, insertHeap_size]

/-- 4+3要素の不変状態で下側根より大きい値を挿入しても不変条件を保つ。

上側に1要素を加えると4+4となり、再平衡ループは状態を変えない。
-/
theorem StateInvariant.insert_from_four_three_of_gt_root
    {input : Array Nat} {state : LeanExperiments.RunningMedian.State}
    (hInvariant : StateInvariant input state)
    {lowerRoot lowerLeft lowerMiddle lowerRight upperRoot upperLeft upperRight value : Nat}
    (hState : state = {
      lower := #[lowerRoot, lowerLeft, lowerMiddle, lowerRight],
      upper := #[upperRoot, upperLeft, upperRight] })
    (hValue : lowerRoot < value) :
    StateInvariant (input.push value)
      (LeanExperiments.RunningMedian.insert state value) := by
  rw [hState] at hInvariant ⊢
  let upperInserted := LeanExperiments.RunningMedian.insertHeap
    LeanExperiments.RunningMedian.minPrefer
    #[upperRoot, upperLeft, upperRight] value
  have hUpperHeap : MinHeap #[upperRoot, upperLeft, upperRight] :=
    (minHeap_iff_HeapOrdered_minPrefer _).mpr hInvariant.2.2.1
  have hUpperInsertedHeap : MinHeap upperInserted := by
    simpa [upperInserted] using
      insertHeap_minPrefer_threeElements_preserves hUpperHeap
  have hUpperOrdered : HeapOrdered minPrefer upperInserted :=
    (minHeap_iff_HeapOrdered_minPrefer _).mp hUpperInsertedHeap
  have hBalanced : #[lowerRoot, lowerLeft, lowerMiddle, lowerRight].size =
      upperInserted.size := by simp [upperInserted, insertHeap_size]
  have hRebalance := rebalanceLoops_eq_self_of_balanced_size
    #[lowerRoot, lowerLeft, lowerMiddle, lowerRight] upperInserted (Or.inl hBalanced)
  dsimp at hRebalance
  have hResult : LeanExperiments.RunningMedian.insert
      { lower := #[lowerRoot, lowerLeft, lowerMiddle, lowerRight],
        upper := #[upperRoot, upperLeft, upperRight] } value =
      { lower := #[lowerRoot, lowerLeft, lowerMiddle, lowerRight],
        upper := upperInserted } := by
    by_cases hRoute : value ≤ lowerRoot
    · omega
    · have hLowerResult := congrArg Prod.fst hRebalance
      have hUpperResult := congrArg Prod.snd hRebalance
      simp [LeanExperiments.RunningMedian.insert, hRoute]
      exact ⟨hLowerResult, hUpperResult⟩
  rw [hResult]
  let routedState : LeanExperiments.RunningMedian.State :=
    ⟨#[lowerRoot, lowerLeft, lowerMiddle, lowerRight], #[upperRoot, upperLeft, upperRight]⟩
  have hPartition := insert_partition routedState value
    (by simpa [routedState] using hInvariant.1)
  refine ⟨?_, hInvariant.2.1, hUpperOrdered, ?_, ?_⟩
  · rw [hResult] at hPartition
    exact hPartition
  · exact crossBoundary_insertUpper_of_gt_lowerRoot
      routedState value (by simp [routedState])
      (by simpa [routedState] using hInvariant.2.1)
      (by simpa [routedState] using hInvariant.2.2.2.1) hValue
  · simp [upperInserted, insertHeap_size]

/-- 長さ7の任意の不変状態で下側根以下の値を挿入する分岐は不変条件を保つ。 -/
theorem StateInvariant.insert_from_size_seven_of_le_root {input : Array Nat}
    {state : LeanExperiments.RunningMedian.State}
    (hInvariant : StateInvariant input state) (hSize : input.size = 7)
    (value : Nat) (hValue : value ≤ state.lower[0]!) :
    StateInvariant (input.push value)
      (LeanExperiments.RunningMedian.insert state value) := by
  have hTotal := StateInvariant.size_partition hInvariant
  have hLowerSize : state.lower.size = 4 := by
    rcases hInvariant.2.2.2.2 with hBalanced | hLowerExtra <;> omega
  have hUpperSize : state.upper.size = 3 := by
    rcases hInvariant.2.2.2.2 with hBalanced | hLowerExtra <;> omega
  let lowerRoot := state.lower[0]'(by omega)
  let lowerLeft := state.lower[1]'(by omega)
  let lowerMiddle := state.lower[2]'(by omega)
  let lowerRight := state.lower[3]'(by omega)
  let upperRoot := state.upper[0]'(by omega)
  let upperLeft := state.upper[1]'(by omega)
  let upperRight := state.upper[2]'(by omega)
  have hLowerEq : state.lower = #[lowerRoot, lowerLeft, lowerMiddle, lowerRight] := by
    apply Array.ext
    · exact hLowerSize
    · intro index hIndex hBound
      have hCases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 := by omega
      rcases hCases with h | h | h | h <;> subst index
      · simp [lowerRoot]
      · simp [lowerLeft]
      · simp [lowerMiddle]
      · simp [lowerRight]
  have hUpperEq : state.upper = #[upperRoot, upperLeft, upperRight] := by
    apply Array.ext
    · exact hUpperSize
    · intro index hIndex hBound
      have hCases : index = 0 ∨ index = 1 ∨ index = 2 := by omega
      rcases hCases with h | h | h <;> subst index
      · simp [upperRoot]
      · simp [upperLeft]
      · simp [upperRight]
  have hState : state = {
      lower := #[lowerRoot, lowerLeft, lowerMiddle, lowerRight],
      upper := #[upperRoot, upperLeft, upperRight] } := by
    cases state with
    | mk lower upper =>
        simp only [LeanExperiments.RunningMedian.State.mk.injEq]
        exact ⟨hLowerEq, hUpperEq⟩
  have hRootValue : value ≤ lowerRoot := by
    have hBang : state.lower[0]! = state.lower[0]'(by omega) :=
      getElem!_pos state.lower 0 (by omega)
    simpa [lowerRoot, hBang] using hValue
  exact StateInvariant.insert_from_four_three_of_le_root
    hInvariant hState hRootValue

/-- 長さ7の任意の不変状態で下側根より大きい値を挿入する分岐は不変条件を保つ。 -/
theorem StateInvariant.insert_from_size_seven_of_gt_root {input : Array Nat}
    {state : LeanExperiments.RunningMedian.State}
    (hInvariant : StateInvariant input state) (hSize : input.size = 7)
    (value : Nat) (hValue : state.lower[0]! < value) :
    StateInvariant (input.push value)
      (LeanExperiments.RunningMedian.insert state value) := by
  have hTotal := StateInvariant.size_partition hInvariant
  have hLowerSize : state.lower.size = 4 := by
    rcases hInvariant.2.2.2.2 with hBalanced | hLowerExtra <;> omega
  have hUpperSize : state.upper.size = 3 := by
    rcases hInvariant.2.2.2.2 with hBalanced | hLowerExtra <;> omega
  let lowerRoot := state.lower[0]'(by omega)
  let lowerLeft := state.lower[1]'(by omega)
  let lowerMiddle := state.lower[2]'(by omega)
  let lowerRight := state.lower[3]'(by omega)
  let upperRoot := state.upper[0]'(by omega)
  let upperLeft := state.upper[1]'(by omega)
  let upperRight := state.upper[2]'(by omega)
  have hLowerEq : state.lower = #[lowerRoot, lowerLeft, lowerMiddle, lowerRight] := by
    apply Array.ext
    · exact hLowerSize
    · intro index hIndex hBound
      have hCases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 := by omega
      rcases hCases with h | h | h | h <;> subst index
      · simp [lowerRoot]
      · simp [lowerLeft]
      · simp [lowerMiddle]
      · simp [lowerRight]
  have hUpperEq : state.upper = #[upperRoot, upperLeft, upperRight] := by
    apply Array.ext
    · exact hUpperSize
    · intro index hIndex hBound
      have hCases : index = 0 ∨ index = 1 ∨ index = 2 := by omega
      rcases hCases with h | h | h <;> subst index
      · simp [upperRoot]
      · simp [upperLeft]
      · simp [upperRight]
  have hState : state = {
      lower := #[lowerRoot, lowerLeft, lowerMiddle, lowerRight],
      upper := #[upperRoot, upperLeft, upperRight] } := by
    cases state with
    | mk lower upper =>
        simp only [LeanExperiments.RunningMedian.State.mk.injEq]
        exact ⟨hLowerEq, hUpperEq⟩
  have hRootValue : lowerRoot < value := by
    have hBang : state.lower[0]! = state.lower[0]'(by omega) :=
      getElem!_pos state.lower 0 (by omega)
    simpa [lowerRoot, hBang] using hValue
  exact StateInvariant.insert_from_four_three_of_gt_root
    hInvariant hState hRootValue

/-- 長さ7の任意の不変状態への挿入は不変条件を保つ。 -/
theorem StateInvariant.insert_of_size_seven {input : Array Nat}
    {state : LeanExperiments.RunningMedian.State}
    (hInvariant : StateInvariant input state) (hSize : input.size = 7)
    (value : Nat) :
    StateInvariant (input.push value)
      (LeanExperiments.RunningMedian.insert state value) := by
  by_cases hRoot : state.lower[0]! < value
  · exact StateInvariant.insert_from_size_seven_of_gt_root
      hInvariant hSize value hRoot
  · exact StateInvariant.insert_from_size_seven_of_le_root
      hInvariant hSize value (by omega)

/-- 長さ8の任意の不変状態で下側根以下の値を挿入する分岐は不変条件を保つ。 -/
theorem StateInvariant.insert_from_size_eight_of_le_root {input : Array Nat}
    {state : LeanExperiments.RunningMedian.State}
    (hInvariant : StateInvariant input state) (hSize : input.size = 8)
    (value : Nat) (hValue : value ≤ state.lower[0]!) :
    StateInvariant (input.push value)
      (LeanExperiments.RunningMedian.insert state value) := by
  have hTotal := StateInvariant.size_partition hInvariant
  have hLowerSize : state.lower.size = 4 := by
    rcases hInvariant.2.2.2.2 with hBalanced | hLowerExtra <;> omega
  have hUpperSize : state.upper.size = 4 := by
    rcases hInvariant.2.2.2.2 with hBalanced | hLowerExtra <;> omega
  let lowerRoot := state.lower[0]'(by omega)
  let lowerLeft := state.lower[1]'(by omega)
  let lowerMiddle := state.lower[2]'(by omega)
  let lowerRight := state.lower[3]'(by omega)
  let upperRoot := state.upper[0]'(by omega)
  let upperLeft := state.upper[1]'(by omega)
  let upperMiddle := state.upper[2]'(by omega)
  let upperRight := state.upper[3]'(by omega)
  have hLowerEq : state.lower = #[lowerRoot, lowerLeft, lowerMiddle, lowerRight] := by
    apply Array.ext
    · exact hLowerSize
    · intro index hIndex hBound
      have hCases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 := by omega
      rcases hCases with h | h | h | h <;> subst index
      · simp [lowerRoot]
      · simp [lowerLeft]
      · simp [lowerMiddle]
      · simp [lowerRight]
  have hUpperEq : state.upper = #[upperRoot, upperLeft, upperMiddle, upperRight] := by
    apply Array.ext
    · exact hUpperSize
    · intro index hIndex hBound
      have hCases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 := by omega
      rcases hCases with h | h | h | h <;> subst index
      · simp [upperRoot]
      · simp [upperLeft]
      · simp [upperMiddle]
      · simp [upperRight]
  have hState : state = {
      lower := #[lowerRoot, lowerLeft, lowerMiddle, lowerRight],
      upper := #[upperRoot, upperLeft, upperMiddle, upperRight] } := by
    cases state with
    | mk lower upper =>
        simp only [LeanExperiments.RunningMedian.State.mk.injEq]
        exact ⟨hLowerEq, hUpperEq⟩
  have hRootValue : value ≤ lowerRoot := by
    have hBang : state.lower[0]! = state.lower[0]'(by omega) :=
      getElem!_pos state.lower 0 (by omega)
    simpa [lowerRoot, hBang] using hValue
  exact StateInvariant.insert_from_four_four_of_le_root
    hInvariant hState hRootValue

/-- 長さ8の任意の不変状態で下側根より大きい値を挿入する分岐は不変条件を保つ。 -/
theorem StateInvariant.insert_from_size_eight_of_gt_root {input : Array Nat}
    {state : LeanExperiments.RunningMedian.State}
    (hInvariant : StateInvariant input state) (hSize : input.size = 8)
    (value : Nat) (hValue : state.lower[0]! < value) :
    StateInvariant (input.push value)
      (LeanExperiments.RunningMedian.insert state value) := by
  have hTotal := StateInvariant.size_partition hInvariant
  have hLowerSize : state.lower.size = 4 := by
    rcases hInvariant.2.2.2.2 with hBalanced | hLowerExtra <;> omega
  have hUpperSize : state.upper.size = 4 := by
    rcases hInvariant.2.2.2.2 with hBalanced | hLowerExtra <;> omega
  let lowerRoot := state.lower[0]'(by omega)
  let lowerLeft := state.lower[1]'(by omega)
  let lowerMiddle := state.lower[2]'(by omega)
  let lowerRight := state.lower[3]'(by omega)
  let upperRoot := state.upper[0]'(by omega)
  let upperLeft := state.upper[1]'(by omega)
  let upperMiddle := state.upper[2]'(by omega)
  let upperRight := state.upper[3]'(by omega)
  have hLowerEq : state.lower = #[lowerRoot, lowerLeft, lowerMiddle, lowerRight] := by
    apply Array.ext
    · exact hLowerSize
    · intro index hIndex hBound
      have hCases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 := by omega
      rcases hCases with h | h | h | h <;> subst index
      · simp [lowerRoot]
      · simp [lowerLeft]
      · simp [lowerMiddle]
      · simp [lowerRight]
  have hUpperEq : state.upper = #[upperRoot, upperLeft, upperMiddle, upperRight] := by
    apply Array.ext
    · exact hUpperSize
    · intro index hIndex hBound
      have hCases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 := by omega
      rcases hCases with h | h | h | h <;> subst index
      · simp [upperRoot]
      · simp [upperLeft]
      · simp [upperMiddle]
      · simp [upperRight]
  have hState : state = {
      lower := #[lowerRoot, lowerLeft, lowerMiddle, lowerRight],
      upper := #[upperRoot, upperLeft, upperMiddle, upperRight] } := by
    cases state with
    | mk lower upper =>
        simp only [LeanExperiments.RunningMedian.State.mk.injEq]
        exact ⟨hLowerEq, hUpperEq⟩
  have hRootValue : lowerRoot < value := by
    have hBang : state.lower[0]! = state.lower[0]'(by omega) :=
      getElem!_pos state.lower 0 (by omega)
    simpa [lowerRoot, hBang] using hValue
  exact StateInvariant.insert_from_four_four_of_gt_root
    hInvariant hState hRootValue

/-- 長さ8の任意の不変状態への挿入は不変条件を保つ。 -/
theorem StateInvariant.insert_of_size_eight {input : Array Nat}
    {state : LeanExperiments.RunningMedian.State}
    (hInvariant : StateInvariant input state) (hSize : input.size = 8)
    (value : Nat) :
    StateInvariant (input.push value)
      (LeanExperiments.RunningMedian.insert state value) := by
  by_cases hRoot : state.lower[0]! < value
  · exact StateInvariant.insert_from_size_eight_of_gt_root
      hInvariant hSize value hRoot
  · exact StateInvariant.insert_from_size_eight_of_le_root
      hInvariant hSize value (by omega)

/-- 長さ9の任意不変状態で下側根より大きい値を挿入する分岐は不変条件を保つ。

サイズ分割からヒープ長は5と4に定まり、値は上側へ挿入される。サイズ4の
最小ヒープ挿入契約と再平衡の同数停止契約を合成して示す。
-/
theorem StateInvariant.insert_from_size_nine_of_gt_root {input : Array Nat}
    {state : LeanExperiments.RunningMedian.State}
    (hInvariant : StateInvariant input state) (hSize : input.size = 9)
    (value : Nat) (hValue : state.lower[0]! < value) :
    StateInvariant (input.push value)
      (LeanExperiments.RunningMedian.insert state value) := by
  have hTotal := StateInvariant.size_partition hInvariant
  have hLowerSize : state.lower.size = 5 := by
    rcases hInvariant.2.2.2.2 with hEqual | hLowerExtra <;> omega
  have hUpperSize : state.upper.size = 4 := by
    rcases hInvariant.2.2.2.2 with hEqual | hLowerExtra <;> omega
  let upperInserted := LeanExperiments.RunningMedian.insertHeap minPrefer state.upper value
  have hUpperInsertedHeap : MinHeap upperInserted := by
    simpa [upperInserted] using
      insertHeap_minPrefer_preserves_of_size_four state.upper hUpperSize value
        ((minHeap_iff_HeapOrdered_minPrefer state.upper).mpr hInvariant.2.2.1)
  have hUpperHeap : HeapOrdered minPrefer upperInserted :=
    (minHeap_iff_HeapOrdered_minPrefer upperInserted).mp hUpperInsertedHeap
  have hCross := crossBoundary_insertUpper_of_gt_lowerRoot state value
    (by omega) hInvariant.2.1 hInvariant.2.2.2.1 hValue
  have hBalanced : state.lower.size = upperInserted.size := by
    simp [upperInserted, insertHeap_size, hLowerSize, hUpperSize]
  have hLowerNotEmpty : state.lower.isEmpty = false := by
    simp [Array.isEmpty, hLowerSize]
  have hLowerRoot : state.lower[0]? = some state.lower[0]! := by
    rw [getElem?_pos state.lower 0 (by omega),
      getElem!_pos state.lower 0 (by omega)]
  have hRebalance := rebalanceLoops_eq_self_of_balanced_size
    state.lower upperInserted (Or.inl hBalanced)
  dsimp at hRebalance
  have hResult : LeanExperiments.RunningMedian.insert state value =
      { lower := state.lower, upper := upperInserted } := by
    by_cases hRoute : value ≤ state.lower[0]!
    · omega
    · have hLowerResult := congrArg Prod.fst hRebalance
      have hUpperResult := congrArg Prod.snd hRebalance
      simp [LeanExperiments.RunningMedian.insert, hLowerNotEmpty, hLowerRoot, hRoute]
      exact ⟨hLowerResult, hUpperResult⟩
  have hPartition := insert_partition state value hInvariant.1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [hResult] using hPartition
  · simpa [hResult] using hInvariant.2.1
  · simpa [hResult] using hUpperHeap
  · simpa [hResult] using hCross
  · simp [hResult, upperInserted, insertHeap_size, hLowerSize, hUpperSize]

/-- 長さ9の任意不変状態で下側根以下の値を挿入する分岐は不変条件を保つ。

下側の5要素ヒープへ挿入した後、根を一度上側へ移す。挿入後の最大ヒープ性、
取り出し後の残余上界、上側への挿入契約をつなぎ、分割境界とサイズ均衡を示す。
-/
theorem StateInvariant.insert_from_size_nine_of_le_root {input : Array Nat}
    {state : LeanExperiments.RunningMedian.State}
    (hInvariant : StateInvariant input state) (hSize : input.size = 9)
    (value : Nat) (hValue : value ≤ state.lower[0]!) :
    StateInvariant (input.push value)
      (LeanExperiments.RunningMedian.insert state value) := by
  have hTotal := StateInvariant.size_partition hInvariant
  have hLowerSize : state.lower.size = 5 := by
    rcases hInvariant.2.2.2.2 with hEqual | hLowerExtra <;> omega
  have hUpperSize : state.upper.size = 4 := by
    rcases hInvariant.2.2.2.2 with hEqual | hLowerExtra <;> omega
  let lowerInserted := LeanExperiments.RunningMedian.insertHeap
    LeanExperiments.RunningMedian.maxPrefer state.lower value
  have hLowerInsertedSize : lowerInserted.size = 6 := by
    simp [lowerInserted, insertHeap_size, hLowerSize]
  have hLowerInsertedHeap : HeapOrdered LeanExperiments.RunningMedian.maxPrefer
      lowerInserted := by
    have hPreferEq : maxPrefer = LeanExperiments.RunningMedian.maxPrefer := by
      funext candidate current
      rfl
    have hPrivateHeap : HeapOrdered maxPrefer
        (LeanExperiments.RunningMedian.insertHeap maxPrefer state.lower value) :=
      insertHeap_maxPrefer_preserves_of_size_five state.lower hLowerSize value hInvariant.2.1
    have hPrivateHeap' : HeapOrdered maxPrefer lowerInserted := by
      simpa [lowerInserted, hPreferEq] using hPrivateHeap
    simpa [hPreferEq] using hPrivateHeap'
  have hMovedEq : lowerInserted[0]! = state.lower[0]! := by
    simpa [lowerInserted] using
      insertHeap_maxPrefer_root_eq_of_le state.lower value (by omega) hValue
  have hPopExists : ∃ rest,
      LeanExperiments.RunningMedian.popHeap maxPrefer lowerInserted =
        some (state.lower[0]!, rest) := by
    cases hPop : LeanExperiments.RunningMedian.popHeap maxPrefer lowerInserted with
    | none =>
        have hEmpty := (popHeap_eq_none_iff_empty maxPrefer lowerInserted).mp hPop
        rw [hLowerInsertedSize] at hEmpty
        simp at hEmpty
    | some pair =>
        rcases pair with ⟨root, rest⟩
        have hRoot := popHeap_value_eq_root hPop
        have hRoot' : lowerInserted[0]? = some root := hRoot
        rw [getElem?_pos lowerInserted 0 (by omega)] at hRoot'
        have hRootValue : root = state.lower[0]! := by
          calc
            root = lowerInserted[0]'(by omega) := (Option.some.inj hRoot').symm
            _ = lowerInserted[0]! := (getElem!_pos lowerInserted 0 (by omega)).symm
            _ = state.lower[0]! := hMovedEq
        refine ⟨rest, ?_⟩
        simp [hRootValue]
  obtain ⟨rest, hPop⟩ := hPopExists
  have hPopCorrect := popHeap_maxPrefer_restCorrect_of_heapOrdered
    lowerInserted hLowerInsertedHeap
  have hPopSpec :
      0 < lowerInserted.size ∧
      lowerInserted[0]? = some state.lower[0]! ∧
      LeanExperiments.Verification.HeapSort.Spec.MaxHeap rest ∧
      rest.toList.Perm (lowerInserted.toList.drop 1) := by
    simpa [LeanExperiments.Verification.HeapSort.Spec.PopMaxRestCorrectFor, hPop]
      using hPopCorrect
  have hRestHeap : HeapOrdered maxPrefer rest :=
    (heapSortMaxHeap_iff_HeapOrdered_maxPrefer rest).mp hPopSpec.2.2.1
  have hRestBound : ∀ item, item ∈ rest.toList → item ≤ state.lower[0]! := by
    simpa [hPop] using
      LeanExperiments.Verification.HeapSort.Spec.PopMaxRestCorrectFor.rest_le_maximum
        hPopCorrect
        ((heapSortMaxHeap_iff_HeapOrdered_maxPrefer _).mpr hLowerInsertedHeap)
  have hRestLe : ∀ index (hIndex : index < rest.size),
      rest[index]'hIndex ≤ state.lower[0]! := by
    intro index hIndex
    exact hRestBound _ (by simp)
  have hRestSize : rest.size = 5 := by
    have hSize := popHeap_size hPop
    omega
  let upperInserted := LeanExperiments.RunningMedian.insertHeap minPrefer state.upper
    state.lower[0]!
  have hUpperInsertedHeap : MinHeap upperInserted := by
    simpa [upperInserted] using
      insertHeap_minPrefer_preserves_of_size_four state.upper hUpperSize state.lower[0]!
        ((minHeap_iff_HeapOrdered_minPrefer state.upper).mpr hInvariant.2.2.1)
  have hUpperInsertedOrdered : HeapOrdered minPrefer upperInserted :=
    (minHeap_iff_HeapOrdered_minPrefer upperInserted).mp hUpperInsertedHeap
  have hUpperBound : ∀ item, item ∈ upperInserted.toList → state.lower[0]! ≤ item := by
    refine insertHeap_ge_of_forall_ge minPrefer state.upper state.lower[0]!
      state.lower[0]! ?_ (Nat.le_refl _)
    intro item hItem
    have hArray : item ∈ state.upper := by simpa using hItem
    obtain ⟨index, hIndex, hAt⟩ := Array.mem_iff_getElem.mp hArray
    have hBoundary := hInvariant.2.2.2.1 0 (by omega) index hIndex
    have hRootValue : state.lower[0]'(by omega) = state.lower[0]! :=
      (getElem!_pos state.lower 0 (by omega)).symm
    have hAt' : state.upper[index]'hIndex = item := hAt
    rw [hAt'] at hBoundary
    simpa [hRootValue] using hBoundary
  have hTransfer : LeanExperiments.RunningMedian.transferLowerRoot maxPrefer minPrefer
      lowerInserted state.upper = some (rest, upperInserted) := by
    simp [LeanExperiments.RunningMedian.transferLowerRoot, hPop, upperInserted]
  have hAfterLower := rebalanceLower_one_transfer lowerInserted state.upper rest upperInserted
    (by simp [hLowerInsertedSize, hUpperSize]) hTransfer
    (by simp [hRestSize, upperInserted, insertHeap_size, hUpperSize])
  have hAfterUpper := rebalanceUpper_eq_self_of_size_le rest upperInserted
    (by simp [hRestSize, upperInserted, insertHeap_size, hUpperSize])
  have hLowerNotEmpty : state.lower.isEmpty = false := by
    simp [Array.isEmpty, hLowerSize]
  have hLowerRoot : state.lower[0]? = some state.lower[0]! := by
    rw [getElem?_pos state.lower 0 (by omega), getElem!_pos state.lower 0 (by omega)]
  have hResult : LeanExperiments.RunningMedian.insert state value =
      { lower := rest, upper := upperInserted } := by
    have hRoute : value ≤ state.lower[0]! := hValue
    simp [LeanExperiments.RunningMedian.insert, hLowerNotEmpty, hLowerRoot, hRoute]
    rw [hAfterLower]
    exact Prod.mk.inj hAfterUpper
  have hPartition := insert_partition state value hInvariant.1
  rw [hResult] at hPartition
  rw [hResult]
  refine ⟨?_, ?_, hUpperInsertedOrdered, ?_, ?_⟩
  · exact hPartition
  · exact hRestHeap
  · intro lowerIndex hLowerIndex upperIndex hUpperIndex
    exact Nat.le_trans (hRestLe lowerIndex hLowerIndex)
      (hUpperBound _ (Array.getElem_mem_toList hUpperIndex))
  · simp [hRestSize, upperInserted, insertHeap_size, hUpperSize]

/-- 長さ9の任意不変状態への挿入は、どちらの根比較分岐でも不変条件を保つ。 -/
theorem StateInvariant.insert_of_size_nine {input : Array Nat}
    {state : LeanExperiments.RunningMedian.State}
    (hInvariant : StateInvariant input state) (hSize : input.size = 9)
    (value : Nat) :
    StateInvariant (input.push value)
      (LeanExperiments.RunningMedian.insert state value) := by
  by_cases hRoot : state.lower[0]! < value
  · exact StateInvariant.insert_from_size_nine_of_gt_root
      hInvariant hSize value hRoot
  · exact StateInvariant.insert_from_size_nine_of_le_root
      hInvariant hSize value (by omega)

/-- 長さ10の任意不変状態で下側根以下の値を挿入する分岐は不変条件を保つ。

ヒープ長が5対5と定まるため、下側への挿入後はサイズ6対5で均衡する。
一般サイズ5の最大ヒープ挿入契約と根以下挿入の境界契約から従う。
-/
theorem StateInvariant.insert_from_size_ten_of_le_root {input : Array Nat}
    {state : LeanExperiments.RunningMedian.State}
    (hInvariant : StateInvariant input state) (hSize : input.size = 10)
    (value : Nat) (hValue : value ≤ state.lower[0]!) :
    StateInvariant (input.push value)
      (LeanExperiments.RunningMedian.insert state value) := by
  have hTotal := StateInvariant.size_partition hInvariant
  have hLowerSize : state.lower.size = 5 := by
    rcases hInvariant.2.2.2.2 with hEqual | hLowerExtra <;> omega
  have hUpperSize : state.upper.size = 5 := by
    rcases hInvariant.2.2.2.2 with hEqual | hLowerExtra <;> omega
  let lowerInserted := LeanExperiments.RunningMedian.insertHeap
    LeanExperiments.RunningMedian.maxPrefer state.lower value
  have hPreferEq : maxPrefer = LeanExperiments.RunningMedian.maxPrefer := by
    funext candidate current
    rfl
  have hPrivateInserted : HeapOrdered maxPrefer
      (LeanExperiments.RunningMedian.insertHeap maxPrefer state.lower value) :=
    insertHeap_maxPrefer_preserves_of_size_five state.lower hLowerSize value hInvariant.2.1
  have hLowerInsertedHeap : HeapOrdered LeanExperiments.RunningMedian.maxPrefer
      lowerInserted := by
    have hPrivateHeap : HeapOrdered maxPrefer lowerInserted := by
      simpa [lowerInserted, hPreferEq] using hPrivateInserted
    simpa [hPreferEq] using hPrivateHeap
  have hCross := crossBoundary_insertLower_of_le_lowerRoot state value
    (by omega) hInvariant.2.2.2.1 hValue
  have hBalanced : lowerInserted.size = state.upper.size + 1 := by
    simp [lowerInserted, insertHeap_size, hLowerSize, hUpperSize]
  have hLowerNotEmpty : state.lower.isEmpty = false := by
    simp [Array.isEmpty, hLowerSize]
  have hLowerRoot : state.lower[0]? = some state.lower[0]! := by
    rw [getElem?_pos state.lower 0 (by omega), getElem!_pos state.lower 0 (by omega)]
  have hRebalance := rebalanceLoops_eq_self_of_balanced_size lowerInserted state.upper
    (Or.inr hBalanced)
  dsimp at hRebalance
  have hResult : LeanExperiments.RunningMedian.insert state value =
      { lower := lowerInserted, upper := state.upper } := by
    have hRoute : value ≤ state.lower[0]! := hValue
    simp [LeanExperiments.RunningMedian.insert, hLowerNotEmpty, hLowerRoot, hRoute]
    exact Prod.mk.inj hRebalance
  have hPartition := insert_partition state value hInvariant.1
  rw [hResult] at hPartition
  rw [hResult]
  refine ⟨hPartition, hLowerInsertedHeap, hInvariant.2.2.1, ?_, ?_⟩
  · exact hCross
  · simp [lowerInserted, insertHeap_size, hLowerSize, hUpperSize]

/-- 長さ10の任意不変状態で下側根より大きい値を挿入する分岐は不変条件を保つ。

上側最小ヒープへ値を挿入して最小根を下側へ移す。popHeap の残余最小ヒープ契約と
残余要素の下界を使い、挿入後もヒープ間境界が保たれることを示す。
-/
theorem StateInvariant.insert_from_size_ten_of_gt_root {input : Array Nat}
    {state : LeanExperiments.RunningMedian.State}
    (hInvariant : StateInvariant input state) (hSize : input.size = 10)
    (value : Nat) (hValue : state.lower[0]! < value) :
    StateInvariant (input.push value)
      (LeanExperiments.RunningMedian.insert state value) := by
  have hTotal := StateInvariant.size_partition hInvariant
  have hLowerSize : state.lower.size = 5 := by
    rcases hInvariant.2.2.2.2 with hEqual | hLowerExtra <;> omega
  have hUpperSize : state.upper.size = 5 := by
    rcases hInvariant.2.2.2.2 with hEqual | hLowerExtra <;> omega
  have hUpperMinHeap : MinHeap state.upper :=
    (minHeap_iff_HeapOrdered_minPrefer state.upper).mpr hInvariant.2.2.1
  have hMinPreferEq : minPrefer = LeanExperiments.RunningMedian.minPrefer := by
    funext candidate current
    rfl
  let upperInserted := LeanExperiments.RunningMedian.insertHeap
    LeanExperiments.RunningMedian.minPrefer state.upper value
  have hUpperInsertedHeap : MinHeap upperInserted := by
    have hPrivateInserted : MinHeap
        (LeanExperiments.RunningMedian.insertHeap minPrefer state.upper value) :=
      insertHeap_minPrefer_preserves_of_size_five state.upper hUpperSize value hUpperMinHeap
    simpa [upperInserted, hMinPreferEq] using hPrivateInserted
  have hUpperInsertedSize : upperInserted.size = 6 := by
    simp [upperInserted, insertHeap_size, hUpperSize]
  have hUpperHeap : HeapOrdered LeanExperiments.RunningMedian.minPrefer upperInserted :=
    (minHeap_iff_HeapOrdered_minPrefer upperInserted).mp hUpperInsertedHeap
  have hCross := crossBoundary_insertUpper_of_gt_lowerRoot state value
    (by omega) hInvariant.2.1 hInvariant.2.2.2.1 hValue
  have hCrossRuntime : ∀ lowerIndex (hLowerIndex : lowerIndex < state.lower.size),
      ∀ upperIndex (hUpperIndex : upperIndex < upperInserted.size),
        state.lower[lowerIndex]'hLowerIndex ≤ upperInserted[upperIndex]'hUpperIndex := by
    simpa [upperInserted, hMinPreferEq] using hCross
  let moved := upperInserted[0]!
  have hMovedLower : state.lower[0]! ≤ moved := by
    have hAt := hCrossRuntime 0 (by omega) 0 (by omega)
    calc
      state.lower[0]! = state.lower[0]'(by omega) := getElem!_pos state.lower 0 (by omega)
      _ ≤ upperInserted[0]'(by omega) := hAt
      _ = upperInserted[0]! := (getElem!_pos upperInserted 0 (by omega)).symm
      _ = moved := rfl
  have hPopExists : ∃ rest,
      LeanExperiments.RunningMedian.popHeap LeanExperiments.RunningMedian.minPrefer
        upperInserted = some (moved, rest) := by
    cases hPop : LeanExperiments.RunningMedian.popHeap
        LeanExperiments.RunningMedian.minPrefer upperInserted with
    | none =>
        have hEmpty := (popHeap_eq_none_iff_empty
          LeanExperiments.RunningMedian.minPrefer upperInserted).mp hPop
        rw [hUpperInsertedSize] at hEmpty
        simp at hEmpty
    | some pair =>
        rcases pair with ⟨root, rest⟩
        have hRoot := popHeap_value_eq_root hPop
        have hRootValue : root = moved := by
          have hRoot' : upperInserted[0]? = some root := hRoot
          rw [getElem?_pos _ 0 (by omega)] at hRoot'
          have hEq := Option.some.inj hRoot'
          calc
            root = upperInserted[0]'(by omega) := hEq.symm
            _ = upperInserted[0]! := (getElem!_pos upperInserted 0 (by omega)).symm
            _ = moved := rfl
        subst root
        exact ⟨rest, rfl⟩
  obtain ⟨rest, hPop⟩ := hPopExists
  have hRestHeap : MinHeap rest :=
    popHeap_minPrefer_restMinHeap_of_MinHeap hUpperInsertedHeap hPop
  have hMovedMinimum := popHeap_minPrefer_returns_minimum_of_MinHeap
    hUpperInsertedHeap hPop
  have hRestSize : rest.size = 5 := by
    have hSize := popHeap_size hPop
    simp [upperInserted, insertHeap_size, hUpperSize] at hSize
    omega
  have hRestGe : ∀ index (hIndex : index < rest.size),
      moved ≤ rest[index]'hIndex := by
    intro index hIndex
    have hPerm := popHeap_perm_dropRoot hPop
    have hMem : rest[index]'hIndex ∈ rest.toList := by simp
    have hInTail : rest[index]'hIndex ∈ upperInserted.toList.drop 1 :=
      hPerm.mem_iff.mp hMem
    have hInHeap := List.mem_of_mem_drop hInTail
    have hInArray : rest[index]'hIndex ∈ upperInserted := by simpa using hInHeap
    obtain ⟨heapIndex, hIndexArray, hAt⟩ := Array.mem_iff_getElem.mp hInArray
    have hAtBang : upperInserted[heapIndex]! = rest[index]'hIndex := by
      rw [getElem!_pos _ heapIndex hIndexArray]
      exact hAt
    calc
      moved = upperInserted[0]! := rfl
      _ ≤ upperInserted[heapIndex]! := hMovedMinimum heapIndex hIndexArray
      _ = rest[index]'hIndex := hAtBang
  have hLowerBound : ∀ item, item ∈ state.lower.toList → item ≤ moved := by
    intro item hItem
    have hInArray : item ∈ state.lower := by simpa using hItem
    obtain ⟨index, hIndex, hAt⟩ := Array.mem_iff_getElem.mp hInArray
    have hMaximum := maxHeap_root_is_maximum state.lower hInvariant.2.1 index hIndex
    have hAtBang : state.lower[index]! = item := by
      rw [getElem!_pos _ index hIndex]
      exact hAt
    have hMaximumBang : state.lower[index]! ≤ state.lower[0]! := by
      simpa using hMaximum
    calc
      item = state.lower[index]! := hAtBang.symm
      _ ≤ state.lower[0]! := hMaximumBang
      _ ≤ moved := hMovedLower
  let lowerInserted := LeanExperiments.RunningMedian.insertHeap
    LeanExperiments.RunningMedian.maxPrefer state.lower moved
  have hLowerInsertedHeap : HeapOrdered LeanExperiments.RunningMedian.maxPrefer
      lowerInserted := by
    have hPreferEq : maxPrefer = LeanExperiments.RunningMedian.maxPrefer := by
      funext candidate current
      rfl
    have hPrivateInserted : HeapOrdered maxPrefer
        (LeanExperiments.RunningMedian.insertHeap maxPrefer state.lower moved) :=
      insertHeap_maxPrefer_preserves_of_size_five state.lower hLowerSize moved hInvariant.2.1
    have hPrivateHeap : HeapOrdered maxPrefer lowerInserted := by
      simpa [lowerInserted, hPreferEq] using hPrivateInserted
    simpa [hPreferEq] using hPrivateHeap
  have hLowerInsertedSize : lowerInserted.size = 6 := by
    simp [lowerInserted, insertHeap_size, hLowerSize]
  have hLowerInsertedBound : ∀ item, item ∈ lowerInserted.toList → item ≤ moved := by
    simpa [lowerInserted] using
      (insertHeap_le_of_forall_le LeanExperiments.RunningMedian.maxPrefer
        state.lower moved moved hLowerBound (Nat.le_refl moved))
  have hTransfer : LeanExperiments.RunningMedian.transferUpperRoot
      LeanExperiments.RunningMedian.minPrefer LeanExperiments.RunningMedian.maxPrefer
      state.lower upperInserted = some (lowerInserted, rest) := by
    simp [LeanExperiments.RunningMedian.transferUpperRoot, hPop, lowerInserted, moved]
  have hAfterLower := rebalanceLower_eq_self_of_size_le state.lower upperInserted
    (by simp [upperInserted, insertHeap_size, hLowerSize, hUpperSize])
  have hAfterUpper := rebalanceUpper_one_transfer
    state.lower upperInserted lowerInserted rest
    (by simp [upperInserted, insertHeap_size, hLowerSize, hUpperSize])
    hTransfer (by omega)
  have hLowerNotEmpty : state.lower.isEmpty = false := by
    simp [Array.isEmpty, hLowerSize]
  have hLowerRoot : state.lower[0]? = some state.lower[0]! := by
    rw [getElem?_pos state.lower 0 (by omega), getElem!_pos state.lower 0 (by omega)]
  have hResult : LeanExperiments.RunningMedian.insert state value =
      { lower := lowerInserted, upper := rest } := by
    have hRoute : ¬ value ≤ state.lower[0]! := by omega
    simp [LeanExperiments.RunningMedian.insert, hLowerNotEmpty, hLowerRoot, hRoute,
      upperInserted, hAfterLower, hAfterUpper]
  have hPartition := insert_partition state value hInvariant.1
  rw [hResult] at hPartition
  rw [hResult]
  refine ⟨hPartition, hLowerInsertedHeap,
    (minHeap_iff_HeapOrdered_minPrefer rest).mp hRestHeap, ?_, ?_⟩
  · intro lowerIndex hLowerIndex upperIndex hUpperIndex
    exact Nat.le_trans
      (hLowerInsertedBound _ (Array.getElem_mem_toList hLowerIndex))
      (hRestGe upperIndex hUpperIndex)
  · simp [lowerInserted, hRestSize, insertHeap_size, hLowerSize]

/-- 長さ10の任意不変状態への挿入は、どちらの根比較分岐でも不変条件を保つ。 -/
theorem StateInvariant.insert_of_size_ten {input : Array Nat}
    {state : LeanExperiments.RunningMedian.State}
    (hInvariant : StateInvariant input state) (hSize : input.size = 10)
    (value : Nat) :
    StateInvariant (input.push value)
      (LeanExperiments.RunningMedian.insert state value) := by
  by_cases hRoot : state.lower[0]! < value
  · exact StateInvariant.insert_from_size_ten_of_gt_root
      hInvariant hSize value hRoot
  · exact StateInvariant.insert_from_size_ten_of_le_root
      hInvariant hSize value (by omega)

/-- 長さ11で下側根より大きい値を挿入する分岐は状態不変条件を保つ。

サイズ分割により両ヒープは6要素と5要素になる。上側の6要素最小ヒープ挿入契約と、
挿入後に両ヒープが同じ長さになる場合の再平衡停止契約を合成する。
-/
theorem StateInvariant.insert_from_size_eleven_of_gt_root {input : Array Nat}
    {state : LeanExperiments.RunningMedian.State}
    (hInvariant : StateInvariant input state) (hSize : input.size = 11)
    (value : Nat) (hValue : state.lower[0]! < value) :
    StateInvariant (input.push value)
      (LeanExperiments.RunningMedian.insert state value) := by
  have hTotal := StateInvariant.size_partition hInvariant
  have hLowerSize : state.lower.size = 6 := by
    rcases hInvariant.2.2.2.2 with hEqual | hLowerExtra <;> omega
  have hUpperSize : state.upper.size = 5 := by
    rcases hInvariant.2.2.2.2 with hEqual | hLowerExtra <;> omega
  let upperInserted := LeanExperiments.RunningMedian.insertHeap minPrefer state.upper value
  have hUpperMinHeap : MinHeap state.upper :=
    (minHeap_iff_HeapOrdered_minPrefer state.upper).mpr hInvariant.2.2.1
  have hUpperInsertedHeap : MinHeap upperInserted := by
    simpa [upperInserted] using
      insertHeap_minPrefer_preserves_of_size_five state.upper hUpperSize value hUpperMinHeap
  have hUpperHeap : HeapOrdered minPrefer upperInserted :=
    (minHeap_iff_HeapOrdered_minPrefer upperInserted).mp hUpperInsertedHeap
  have hCross := crossBoundary_insertUpper_of_gt_lowerRoot state value
    (by omega) hInvariant.2.1 hInvariant.2.2.2.1 hValue
  have hBalanced : state.lower.size = upperInserted.size := by
    simp [upperInserted, insertHeap_size, hLowerSize, hUpperSize]
  have hLowerNotEmpty : state.lower.isEmpty = false := by
    simp [Array.isEmpty, hLowerSize]
  have hLowerRoot : state.lower[0]? = some state.lower[0]! := by
    rw [getElem?_pos state.lower 0 (by omega), getElem!_pos state.lower 0 (by omega)]
  have hRebalance := rebalanceLoops_eq_self_of_balanced_size
    state.lower upperInserted (Or.inl hBalanced)
  dsimp at hRebalance
  have hResult : LeanExperiments.RunningMedian.insert state value =
      { lower := state.lower, upper := upperInserted } := by
    by_cases hRoute : value ≤ state.lower[0]!
    · omega
    · have hLowerResult := congrArg Prod.fst hRebalance
      have hUpperResult := congrArg Prod.snd hRebalance
      simp [LeanExperiments.RunningMedian.insert, hLowerNotEmpty, hLowerRoot, hRoute]
      exact ⟨hLowerResult, hUpperResult⟩
  have hPartition := insert_partition state value hInvariant.1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [hResult] using hPartition
  · simpa [hResult] using hInvariant.2.1
  · simpa [hResult] using hUpperHeap
  · simpa [hResult] using hCross
  · simp [hResult, upperInserted, insertHeap_size, hLowerSize, hUpperSize]

/-- 長さ11の任意不変状態で下側根以下の値を挿入する分岐は不変条件を保つ。

下側の6要素ヒープへ挿入した後、根を一度上側へ移す。挿入後の最大ヒープ性、
取り出し後の残余上界、上側への挿入契約をつなぎ、分割境界とサイズ均衡を示す。
-/
theorem StateInvariant.insert_from_size_eleven_of_le_root {input : Array Nat}
    {state : LeanExperiments.RunningMedian.State}
    (hInvariant : StateInvariant input state) (hSize : input.size = 11)
    (value : Nat) (hValue : value ≤ state.lower[0]!) :
    StateInvariant (input.push value)
      (LeanExperiments.RunningMedian.insert state value) := by
  have hTotal := StateInvariant.size_partition hInvariant
  have hLowerSize : state.lower.size = 6 := by
    rcases hInvariant.2.2.2.2 with hEqual | hLowerExtra <;> omega
  have hUpperSize : state.upper.size = 5 := by
    rcases hInvariant.2.2.2.2 with hEqual | hLowerExtra <;> omega
  let lowerInserted := LeanExperiments.RunningMedian.insertHeap
    LeanExperiments.RunningMedian.maxPrefer state.lower value
  have hLowerInsertedSize : lowerInserted.size = 7 := by
    simp [lowerInserted, insertHeap_size, hLowerSize]
  have hLowerInsertedHeap : HeapOrdered LeanExperiments.RunningMedian.maxPrefer
      lowerInserted := by
    have hPreferEq : maxPrefer = LeanExperiments.RunningMedian.maxPrefer := by
      funext candidate current
      rfl
    have hPrivateHeap : HeapOrdered maxPrefer
        (LeanExperiments.RunningMedian.insertHeap maxPrefer state.lower value) :=
      insertHeap_maxPrefer_preserves_of_size_six state.lower hLowerSize value hInvariant.2.1
    have hPrivateHeap' : HeapOrdered maxPrefer lowerInserted := by
      simpa [lowerInserted, hPreferEq] using hPrivateHeap
    simpa [hPreferEq] using hPrivateHeap'
  have hMovedEq : lowerInserted[0]! = state.lower[0]! := by
    simpa [lowerInserted] using
      insertHeap_maxPrefer_root_eq_of_le state.lower value (by omega) hValue
  have hPopExists : ∃ rest,
      LeanExperiments.RunningMedian.popHeap maxPrefer lowerInserted =
        some (state.lower[0]!, rest) := by
    cases hPop : LeanExperiments.RunningMedian.popHeap maxPrefer lowerInserted with
    | none =>
        have hEmpty := (popHeap_eq_none_iff_empty maxPrefer lowerInserted).mp hPop
        rw [hLowerInsertedSize] at hEmpty
        simp at hEmpty
    | some pair =>
        rcases pair with ⟨root, rest⟩
        have hRoot := popHeap_value_eq_root hPop
        have hRoot' : lowerInserted[0]? = some root := hRoot
        rw [getElem?_pos lowerInserted 0 (by omega)] at hRoot'
        have hRootValue : root = state.lower[0]! := by
          calc
            root = lowerInserted[0]'(by omega) := (Option.some.inj hRoot').symm
            _ = lowerInserted[0]! := (getElem!_pos lowerInserted 0 (by omega)).symm
            _ = state.lower[0]! := hMovedEq
        refine ⟨rest, ?_⟩
        simp [hRootValue]
  obtain ⟨rest, hPop⟩ := hPopExists
  have hPopCorrect := popHeap_maxPrefer_restCorrect_of_heapOrdered
    lowerInserted hLowerInsertedHeap
  have hPopSpec :
      0 < lowerInserted.size ∧
      lowerInserted[0]? = some state.lower[0]! ∧
      LeanExperiments.Verification.HeapSort.Spec.MaxHeap rest ∧
      rest.toList.Perm (lowerInserted.toList.drop 1) := by
    simpa [LeanExperiments.Verification.HeapSort.Spec.PopMaxRestCorrectFor, hPop]
      using hPopCorrect
  have hRestHeap : HeapOrdered maxPrefer rest :=
    (heapSortMaxHeap_iff_HeapOrdered_maxPrefer rest).mp hPopSpec.2.2.1
  have hRestBound : ∀ item, item ∈ rest.toList → item ≤ state.lower[0]! := by
    simpa [hPop] using
      LeanExperiments.Verification.HeapSort.Spec.PopMaxRestCorrectFor.rest_le_maximum
        hPopCorrect
        ((heapSortMaxHeap_iff_HeapOrdered_maxPrefer _).mpr hLowerInsertedHeap)
  have hRestLe : ∀ index (hIndex : index < rest.size),
      rest[index]'hIndex ≤ state.lower[0]! := by
    intro index hIndex
    exact hRestBound _ (by simp)
  have hRestSize : rest.size = 6 := by
    have hSize := popHeap_size hPop
    omega
  let upperInserted := LeanExperiments.RunningMedian.insertHeap minPrefer state.upper
    state.lower[0]!
  have hUpperInsertedHeap : MinHeap upperInserted := by
    simpa [upperInserted] using
      insertHeap_minPrefer_preserves_of_size_five state.upper hUpperSize state.lower[0]!
        ((minHeap_iff_HeapOrdered_minPrefer state.upper).mpr hInvariant.2.2.1)
  have hUpperInsertedOrdered : HeapOrdered minPrefer upperInserted :=
    (minHeap_iff_HeapOrdered_minPrefer upperInserted).mp hUpperInsertedHeap
  have hUpperBound : ∀ item, item ∈ upperInserted.toList → state.lower[0]! ≤ item := by
    refine insertHeap_ge_of_forall_ge minPrefer state.upper state.lower[0]!
      state.lower[0]! ?_ (Nat.le_refl _)
    intro item hItem
    have hArray : item ∈ state.upper := by simpa using hItem
    obtain ⟨index, hIndex, hAt⟩ := Array.mem_iff_getElem.mp hArray
    have hBoundary := hInvariant.2.2.2.1 0 (by omega) index hIndex
    have hRootValue : state.lower[0]'(by omega) = state.lower[0]! :=
      (getElem!_pos state.lower 0 (by omega)).symm
    have hAt' : state.upper[index]'hIndex = item := hAt
    rw [hAt'] at hBoundary
    simpa [hRootValue] using hBoundary
  have hTransfer : LeanExperiments.RunningMedian.transferLowerRoot maxPrefer minPrefer
      lowerInserted state.upper = some (rest, upperInserted) := by
    simp [LeanExperiments.RunningMedian.transferLowerRoot, hPop, upperInserted]
  have hAfterLower := rebalanceLower_one_transfer lowerInserted state.upper rest upperInserted
    (by simp [hLowerInsertedSize, hUpperSize]) hTransfer
    (by simp [hRestSize, upperInserted, insertHeap_size, hUpperSize])
  have hAfterUpper := rebalanceUpper_eq_self_of_size_le rest upperInserted
    (by simp [hRestSize, upperInserted, insertHeap_size, hUpperSize])
  have hLowerNotEmpty : state.lower.isEmpty = false := by
    simp [Array.isEmpty, hLowerSize]
  have hLowerRoot : state.lower[0]? = some state.lower[0]! := by
    rw [getElem?_pos state.lower 0 (by omega), getElem!_pos state.lower 0 (by omega)]
  have hResult : LeanExperiments.RunningMedian.insert state value =
      { lower := rest, upper := upperInserted } := by
    have hRoute : value ≤ state.lower[0]! := hValue
    simp [LeanExperiments.RunningMedian.insert, hLowerNotEmpty, hLowerRoot, hRoute]
    rw [hAfterLower]
    exact Prod.mk.inj hAfterUpper
  have hPartition := insert_partition state value hInvariant.1
  rw [hResult] at hPartition
  rw [hResult]
  refine ⟨?_, ?_, hUpperInsertedOrdered, ?_, ?_⟩
  · exact hPartition
  · exact hRestHeap
  · intro lowerIndex hLowerIndex upperIndex hUpperIndex
    exact Nat.le_trans (hRestLe lowerIndex hLowerIndex)
      (hUpperBound _ (Array.getElem_mem_toList hUpperIndex))
  · simp [hRestSize, upperInserted, insertHeap_size, hUpperSize]

/-- 長さ11の任意不変状態への挿入は、どちらの根比較分岐でも不変条件を保つ。 -/
theorem StateInvariant.insert_of_size_eleven {input : Array Nat}
    {state : LeanExperiments.RunningMedian.State}
    (hInvariant : StateInvariant input state) (hSize : input.size = 11)
    (value : Nat) :
    StateInvariant (input.push value)
      (LeanExperiments.RunningMedian.insert state value) := by
  by_cases hRoot : state.lower[0]! < value
  · exact StateInvariant.insert_from_size_eleven_of_gt_root
      hInvariant hSize value hRoot
  · exact StateInvariant.insert_from_size_eleven_of_le_root
      hInvariant hSize value (by omega)

/-- 長さ13で下側根より大きい値を挿入する分岐は状態不変条件を保つ。

サイズ分割により下側は7要素、上側は6要素になる。上側の6要素最小ヒープ挿入契約と、
挿入後に両ヒープが同じ長さになる場合の再平衡停止契約を合成する。
-/
theorem StateInvariant.insert_from_size_thirteen_of_gt_root {input : Array Nat}
    {state : LeanExperiments.RunningMedian.State}
    (hInvariant : StateInvariant input state) (hSize : input.size = 13)
    (value : Nat) (hValue : state.lower[0]! < value) :
    StateInvariant (input.push value)
      (LeanExperiments.RunningMedian.insert state value) := by
  have hTotal := StateInvariant.size_partition hInvariant
  have hLowerSize : state.lower.size = 7 := by
    rcases hInvariant.2.2.2.2 with hEqual | hLowerExtra <;> omega
  have hUpperSize : state.upper.size = 6 := by
    rcases hInvariant.2.2.2.2 with hEqual | hLowerExtra <;> omega
  let upperInserted := LeanExperiments.RunningMedian.insertHeap minPrefer state.upper value
  have hUpperMinHeap : MinHeap state.upper :=
    (minHeap_iff_HeapOrdered_minPrefer state.upper).mpr hInvariant.2.2.1
  have hUpperInsertedHeap : MinHeap upperInserted := by
    simpa [upperInserted] using
      insertHeap_minPrefer_preserves_of_size_six state.upper hUpperSize value hUpperMinHeap
  have hUpperHeap : HeapOrdered minPrefer upperInserted :=
    (minHeap_iff_HeapOrdered_minPrefer upperInserted).mp hUpperInsertedHeap
  have hCross := crossBoundary_insertUpper_of_gt_lowerRoot state value
    (by omega) hInvariant.2.1 hInvariant.2.2.2.1 hValue
  have hBalanced : state.lower.size = upperInserted.size := by
    simp [upperInserted, insertHeap_size, hLowerSize, hUpperSize]
  have hLowerNotEmpty : state.lower.isEmpty = false := by
    simp [Array.isEmpty, hLowerSize]
  have hLowerRoot : state.lower[0]? = some state.lower[0]! := by
    rw [getElem?_pos state.lower 0 (by omega), getElem!_pos state.lower 0 (by omega)]
  have hRebalance := rebalanceLoops_eq_self_of_balanced_size
    state.lower upperInserted (Or.inl hBalanced)
  dsimp at hRebalance
  have hResult : LeanExperiments.RunningMedian.insert state value =
      { lower := state.lower, upper := upperInserted } := by
    by_cases hRoute : value ≤ state.lower[0]!
    · omega
    · have hLowerResult := congrArg Prod.fst hRebalance
      have hUpperResult := congrArg Prod.snd hRebalance
      simp [LeanExperiments.RunningMedian.insert, hLowerNotEmpty, hLowerRoot, hRoute]
      exact ⟨hLowerResult, hUpperResult⟩
  have hPartition := insert_partition state value hInvariant.1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [hResult] using hPartition
  · simpa [hResult] using hInvariant.2.1
  · simpa [hResult] using hUpperHeap
  · simpa [hResult] using hCross
  · simp [hResult, upperInserted, insertHeap_size, hLowerSize, hUpperSize]

/-- 長さ13の任意不変状態で下側根以下の値を挿入する分岐は不変条件を保つ。

下側7要素ヒープへの根以下挿入契約で順序を保ち、挿入後に根を一度上側へ移す。
取り出し後の残余上界と上側への6要素挿入契約をつなぎ、分割境界とサイズ均衡を示す。
-/
theorem StateInvariant.insert_from_size_thirteen_of_le_root {input : Array Nat}
    {state : LeanExperiments.RunningMedian.State}
    (hInvariant : StateInvariant input state) (hSize : input.size = 13)
    (value : Nat) (hValue : value ≤ state.lower[0]!) :
    StateInvariant (input.push value)
      (LeanExperiments.RunningMedian.insert state value) := by
  have hTotal := StateInvariant.size_partition hInvariant
  have hLowerSize : state.lower.size = 7 := by
    rcases hInvariant.2.2.2.2 with hEqual | hLowerExtra <;> omega
  have hUpperSize : state.upper.size = 6 := by
    rcases hInvariant.2.2.2.2 with hEqual | hLowerExtra <;> omega
  let lowerInserted := LeanExperiments.RunningMedian.insertHeap
    LeanExperiments.RunningMedian.maxPrefer state.lower value
  have hLowerInsertedSize : lowerInserted.size = 8 := by
    simp [lowerInserted, insertHeap_size, hLowerSize]
  have hLowerInsertedHeap : HeapOrdered LeanExperiments.RunningMedian.maxPrefer
      lowerInserted := by
    have hPreferEq : maxPrefer = LeanExperiments.RunningMedian.maxPrefer := by
      funext candidate current
      rfl
    have hPrivateHeap : HeapOrdered maxPrefer
        (LeanExperiments.RunningMedian.insertHeap maxPrefer state.lower value) :=
      insertHeap_maxPrefer_preserves_of_size_seven_of_le_root state.lower hLowerSize value
        (by simpa [LeanExperiments.RunningMedian.maxPrefer] using hValue) hInvariant.2.1
    have hPrivateHeap' : HeapOrdered maxPrefer lowerInserted := by
      simpa [lowerInserted, hPreferEq] using hPrivateHeap
    simpa [hPreferEq] using hPrivateHeap'
  have hMovedEq : lowerInserted[0]! = state.lower[0]! := by
    simpa [lowerInserted] using
      insertHeap_maxPrefer_root_eq_of_le state.lower value (by omega) hValue
  have hPopExists : ∃ rest,
      LeanExperiments.RunningMedian.popHeap maxPrefer lowerInserted =
        some (state.lower[0]!, rest) := by
    cases hPop : LeanExperiments.RunningMedian.popHeap maxPrefer lowerInserted with
    | none =>
        have hEmpty := (popHeap_eq_none_iff_empty maxPrefer lowerInserted).mp hPop
        rw [hLowerInsertedSize] at hEmpty
        simp at hEmpty
    | some pair =>
        rcases pair with ⟨root, rest⟩
        have hRoot := popHeap_value_eq_root hPop
        have hRoot' : lowerInserted[0]? = some root := hRoot
        rw [getElem?_pos lowerInserted 0 (by omega)] at hRoot'
        have hRootValue : root = state.lower[0]! := by
          calc
            root = lowerInserted[0]'(by omega) := (Option.some.inj hRoot').symm
            _ = lowerInserted[0]! := (getElem!_pos lowerInserted 0 (by omega)).symm
            _ = state.lower[0]! := hMovedEq
        refine ⟨rest, ?_⟩
        simp [hRootValue]
  obtain ⟨rest, hPop⟩ := hPopExists
  have hPopCorrect := popHeap_maxPrefer_restCorrect_of_heapOrdered
    lowerInserted hLowerInsertedHeap
  have hPopSpec :
      0 < lowerInserted.size ∧
      lowerInserted[0]? = some state.lower[0]! ∧
      LeanExperiments.Verification.HeapSort.Spec.MaxHeap rest ∧
      rest.toList.Perm (lowerInserted.toList.drop 1) := by
    simpa [LeanExperiments.Verification.HeapSort.Spec.PopMaxRestCorrectFor, hPop]
      using hPopCorrect
  have hRestHeap : HeapOrdered maxPrefer rest :=
    (heapSortMaxHeap_iff_HeapOrdered_maxPrefer rest).mp hPopSpec.2.2.1
  have hRestBound : ∀ item, item ∈ rest.toList → item ≤ state.lower[0]! := by
    simpa [hPop] using
      LeanExperiments.Verification.HeapSort.Spec.PopMaxRestCorrectFor.rest_le_maximum
        hPopCorrect
        ((heapSortMaxHeap_iff_HeapOrdered_maxPrefer _).mpr hLowerInsertedHeap)
  have hRestLe : ∀ index (hIndex : index < rest.size),
      rest[index]'hIndex ≤ state.lower[0]! := by
    intro index hIndex
    exact hRestBound _ (by simp)
  have hRestSize : rest.size = 7 := by
    have hSize := popHeap_size hPop
    omega
  let upperInserted := LeanExperiments.RunningMedian.insertHeap minPrefer state.upper
    state.lower[0]!
  have hUpperInsertedHeap : MinHeap upperInserted := by
    simpa [upperInserted] using
      insertHeap_minPrefer_preserves_of_size_six state.upper hUpperSize state.lower[0]!
        ((minHeap_iff_HeapOrdered_minPrefer state.upper).mpr hInvariant.2.2.1)
  have hUpperInsertedOrdered : HeapOrdered minPrefer upperInserted :=
    (minHeap_iff_HeapOrdered_minPrefer upperInserted).mp hUpperInsertedHeap
  have hUpperBound : ∀ item, item ∈ upperInserted.toList → state.lower[0]! ≤ item := by
    refine insertHeap_ge_of_forall_ge minPrefer state.upper state.lower[0]!
      state.lower[0]! ?_ (Nat.le_refl _)
    intro item hItem
    have hArray : item ∈ state.upper := by simpa using hItem
    obtain ⟨index, hIndex, hAt⟩ := Array.mem_iff_getElem.mp hArray
    have hBoundary := hInvariant.2.2.2.1 0 (by omega) index hIndex
    have hRootValue : state.lower[0]'(by omega) = state.lower[0]! :=
      (getElem!_pos state.lower 0 (by omega)).symm
    have hAt' : state.upper[index]'hIndex = item := hAt
    rw [hAt'] at hBoundary
    simpa [hRootValue] using hBoundary
  have hTransfer : LeanExperiments.RunningMedian.transferLowerRoot maxPrefer minPrefer
      lowerInserted state.upper = some (rest, upperInserted) := by
    simp [LeanExperiments.RunningMedian.transferLowerRoot, hPop, upperInserted]
  have hAfterLower := rebalanceLower_one_transfer lowerInserted state.upper rest upperInserted
    (by simp [hLowerInsertedSize, hUpperSize]) hTransfer
    (by simp [hRestSize, upperInserted, insertHeap_size, hUpperSize])
  have hAfterUpper := rebalanceUpper_eq_self_of_size_le rest upperInserted
    (by simp [hRestSize, upperInserted, insertHeap_size, hUpperSize])
  have hLowerNotEmpty : state.lower.isEmpty = false := by
    simp [Array.isEmpty, hLowerSize]
  have hLowerRoot : state.lower[0]? = some state.lower[0]! := by
    rw [getElem?_pos state.lower 0 (by omega), getElem!_pos state.lower 0 (by omega)]
  have hResult : LeanExperiments.RunningMedian.insert state value =
      { lower := rest, upper := upperInserted } := by
    have hRoute : value ≤ state.lower[0]! := hValue
    simp [LeanExperiments.RunningMedian.insert, hLowerNotEmpty, hLowerRoot, hRoute]
    rw [hAfterLower]
    exact Prod.mk.inj hAfterUpper
  have hPartition := insert_partition state value hInvariant.1
  rw [hResult] at hPartition
  rw [hResult]
  refine ⟨?_, ?_, hUpperInsertedOrdered, ?_, ?_⟩
  · exact hPartition
  · exact hRestHeap
  · intro lowerIndex hLowerIndex upperIndex hUpperIndex
    exact Nat.le_trans (hRestLe lowerIndex hLowerIndex)
      (hUpperBound _ (Array.getElem_mem_toList hUpperIndex))
  · simp [hRestSize, upperInserted, insertHeap_size, hUpperSize]

/-- 長さ15の任意不変状態で下側根以下の値を挿入する分岐は不変条件を保つ。

8要素最大ヒープへの任意値挿入契約で順序を保ち、挿入後に根を一度上側へ移す。
取り出し後の残余上界と上側への7要素最小ヒープ挿入契約をつなぎ、分割境界と均衡を示す。
-/
theorem StateInvariant.insert_from_size_fifteen_of_le_root {input : Array Nat}
    {state : LeanExperiments.RunningMedian.State}
    (hInvariant : StateInvariant input state) (hSize : input.size = 15)
    (value : Nat) (hValue : value ≤ state.lower[0]!) :
    StateInvariant (input.push value)
      (LeanExperiments.RunningMedian.insert state value) := by
  have hTotal := StateInvariant.size_partition hInvariant
  have hLowerSize : state.lower.size = 8 := by
    rcases hInvariant.2.2.2.2 with hEqual | hLowerExtra <;> omega
  have hUpperSize : state.upper.size = 7 := by
    rcases hInvariant.2.2.2.2 with hEqual | hLowerExtra <;> omega
  let lowerInserted := LeanExperiments.RunningMedian.insertHeap
    LeanExperiments.RunningMedian.maxPrefer state.lower value
  have hLowerInsertedSize : lowerInserted.size = 9 := by
    simp [lowerInserted, insertHeap_size, hLowerSize]
  have hLowerInsertedHeap : HeapOrdered LeanExperiments.RunningMedian.maxPrefer
      lowerInserted := by
    have hPreferEq : maxPrefer = LeanExperiments.RunningMedian.maxPrefer := by
      funext candidate current
      rfl
    have hPrivateHeap : HeapOrdered maxPrefer
        (LeanExperiments.RunningMedian.insertHeap maxPrefer state.lower value) :=
      insertHeap_maxPrefer_preserves_of_size_eight state.lower hLowerSize value hInvariant.2.1
    have hPrivateHeap' : HeapOrdered maxPrefer lowerInserted := by
      simpa [lowerInserted, hPreferEq] using hPrivateHeap
    simpa [hPreferEq] using hPrivateHeap'
  have hMovedEq : lowerInserted[0]! = state.lower[0]! := by
    simpa [lowerInserted] using
      insertHeap_maxPrefer_root_eq_of_le state.lower value (by omega) hValue
  have hPopExists : ∃ rest,
      LeanExperiments.RunningMedian.popHeap maxPrefer lowerInserted =
        some (state.lower[0]!, rest) := by
    cases hPop : LeanExperiments.RunningMedian.popHeap maxPrefer lowerInserted with
    | none =>
        have hEmpty := (popHeap_eq_none_iff_empty maxPrefer lowerInserted).mp hPop
        rw [hLowerInsertedSize] at hEmpty
        simp at hEmpty
    | some pair =>
        rcases pair with ⟨root, rest⟩
        have hRoot := popHeap_value_eq_root hPop
        have hRoot' : lowerInserted[0]? = some root := hRoot
        rw [getElem?_pos lowerInserted 0 (by omega)] at hRoot'
        have hRootValue : root = state.lower[0]! := by
          calc
            root = lowerInserted[0]'(by omega) := (Option.some.inj hRoot').symm
            _ = lowerInserted[0]! := (getElem!_pos lowerInserted 0 (by omega)).symm
            _ = state.lower[0]! := hMovedEq
        refine ⟨rest, ?_⟩
        simp [hRootValue]
  obtain ⟨rest, hPop⟩ := hPopExists
  have hPopCorrect := popHeap_maxPrefer_restCorrect_of_heapOrdered
    lowerInserted hLowerInsertedHeap
  have hPopSpec :
      0 < lowerInserted.size ∧
      lowerInserted[0]? = some state.lower[0]! ∧
      LeanExperiments.Verification.HeapSort.Spec.MaxHeap rest ∧
      rest.toList.Perm (lowerInserted.toList.drop 1) := by
    simpa [LeanExperiments.Verification.HeapSort.Spec.PopMaxRestCorrectFor, hPop]
      using hPopCorrect
  have hRestHeap : HeapOrdered maxPrefer rest :=
    (heapSortMaxHeap_iff_HeapOrdered_maxPrefer rest).mp hPopSpec.2.2.1
  have hRestBound : ∀ item, item ∈ rest.toList → item ≤ state.lower[0]! := by
    simpa [hPop] using
      LeanExperiments.Verification.HeapSort.Spec.PopMaxRestCorrectFor.rest_le_maximum
        hPopCorrect
        ((heapSortMaxHeap_iff_HeapOrdered_maxPrefer _).mpr hLowerInsertedHeap)
  have hRestLe : ∀ index (hIndex : index < rest.size),
      rest[index]'hIndex ≤ state.lower[0]! := by
    intro index hIndex
    exact hRestBound _ (by simp)
  have hRestSize : rest.size = 8 := by
    have hSize := popHeap_size hPop
    omega
  let upperInserted := LeanExperiments.RunningMedian.insertHeap minPrefer state.upper
    state.lower[0]!
  have hUpperInsertedHeap : MinHeap upperInserted := by
    simpa [upperInserted] using
      insertHeap_minPrefer_preserves_of_size_seven state.upper hUpperSize state.lower[0]!
        ((minHeap_iff_HeapOrdered_minPrefer state.upper).mpr hInvariant.2.2.1)
  have hUpperInsertedOrdered : HeapOrdered minPrefer upperInserted :=
    (minHeap_iff_HeapOrdered_minPrefer upperInserted).mp hUpperInsertedHeap
  have hUpperBound : ∀ item, item ∈ upperInserted.toList → state.lower[0]! ≤ item := by
    refine insertHeap_ge_of_forall_ge minPrefer state.upper state.lower[0]!
      state.lower[0]! ?_ (Nat.le_refl _)
    intro item hItem
    have hArray : item ∈ state.upper := by simpa using hItem
    obtain ⟨index, hIndex, hAt⟩ := Array.mem_iff_getElem.mp hArray
    have hBoundary := hInvariant.2.2.2.1 0 (by omega) index hIndex
    have hRootValue : state.lower[0]'(by omega) = state.lower[0]! :=
      (getElem!_pos state.lower 0 (by omega)).symm
    have hAt' : state.upper[index]'hIndex = item := hAt
    rw [hAt'] at hBoundary
    simpa [hRootValue] using hBoundary
  have hTransfer : LeanExperiments.RunningMedian.transferLowerRoot maxPrefer minPrefer
      lowerInserted state.upper = some (rest, upperInserted) := by
    simp [LeanExperiments.RunningMedian.transferLowerRoot, hPop, upperInserted]
  have hAfterLower := rebalanceLower_one_transfer lowerInserted state.upper rest upperInserted
    (by simp [hLowerInsertedSize, hUpperSize]) hTransfer
    (by simp [hRestSize, upperInserted, insertHeap_size, hUpperSize])
  have hAfterUpper := rebalanceUpper_eq_self_of_size_le rest upperInserted
    (by simp [hRestSize, upperInserted, insertHeap_size, hUpperSize])
  have hLowerNotEmpty : state.lower.isEmpty = false := by
    simp [Array.isEmpty, hLowerSize]
  have hLowerRoot : state.lower[0]? = some state.lower[0]! := by
    rw [getElem?_pos state.lower 0 (by omega), getElem!_pos state.lower 0 (by omega)]
  have hResult : LeanExperiments.RunningMedian.insert state value =
      { lower := rest, upper := upperInserted } := by
    have hRoute : value ≤ state.lower[0]! := hValue
    simp [LeanExperiments.RunningMedian.insert, hLowerNotEmpty, hLowerRoot, hRoute]
    rw [hAfterLower]
    exact Prod.mk.inj hAfterUpper
  have hPartition := insert_partition state value hInvariant.1
  rw [hResult] at hPartition
  rw [hResult]
  refine ⟨?_, ?_, hUpperInsertedOrdered, ?_, ?_⟩
  · exact hPartition
  · exact hRestHeap
  · intro lowerIndex hLowerIndex upperIndex hUpperIndex
    exact Nat.le_trans (hRestLe lowerIndex hLowerIndex)
      (hUpperBound _ (Array.getElem_mem_toList hUpperIndex))
  · simp [hRestSize, upperInserted, insertHeap_size, hUpperSize]

/-- 長さ13の任意不変状態への挿入は、根比較の両分岐で不変条件を保つ。 -/
theorem StateInvariant.insert_of_size_thirteen {input : Array Nat}
    {state : LeanExperiments.RunningMedian.State}
    (hInvariant : StateInvariant input state) (hSize : input.size = 13)
    (value : Nat) :
    StateInvariant (input.push value)
      (LeanExperiments.RunningMedian.insert state value) := by
  by_cases hRoot : state.lower[0]! < value
  · exact StateInvariant.insert_from_size_thirteen_of_gt_root
      hInvariant hSize value hRoot
  · exact StateInvariant.insert_from_size_thirteen_of_le_root
      hInvariant hSize value (by omega)


/-- 長さ12の任意不変状態で下側根以下の値を挿入する分岐は不変条件を保つ。

ヒープ長が6対6と定まるため、下側への挿入後はサイズ7対6で均衡する。
一般サイズ6の最大ヒープ挿入契約と根以下挿入の境界契約から従う。
-/
theorem StateInvariant.insert_from_size_twelve_of_le_root {input : Array Nat}
    {state : LeanExperiments.RunningMedian.State}
    (hInvariant : StateInvariant input state) (hSize : input.size = 12)
    (value : Nat) (hValue : value ≤ state.lower[0]!) :
    StateInvariant (input.push value)
      (LeanExperiments.RunningMedian.insert state value) := by
  have hTotal := StateInvariant.size_partition hInvariant
  have hLowerSize : state.lower.size = 6 := by
    rcases hInvariant.2.2.2.2 with hEqual | hLowerExtra <;> omega
  have hUpperSize : state.upper.size = 6 := by
    rcases hInvariant.2.2.2.2 with hEqual | hLowerExtra <;> omega
  let lowerInserted := LeanExperiments.RunningMedian.insertHeap
    LeanExperiments.RunningMedian.maxPrefer state.lower value
  have hPreferEq : maxPrefer = LeanExperiments.RunningMedian.maxPrefer := by
    funext candidate current
    rfl
  have hPrivateInserted : HeapOrdered maxPrefer
      (LeanExperiments.RunningMedian.insertHeap maxPrefer state.lower value) :=
    insertHeap_maxPrefer_preserves_of_size_six state.lower hLowerSize value hInvariant.2.1
  have hLowerInsertedHeap : HeapOrdered LeanExperiments.RunningMedian.maxPrefer
      lowerInserted := by
    have hPrivateHeap : HeapOrdered maxPrefer lowerInserted := by
      simpa [lowerInserted, hPreferEq] using hPrivateInserted
    simpa [hPreferEq] using hPrivateHeap
  have hCross := crossBoundary_insertLower_of_le_lowerRoot state value
    (by omega) hInvariant.2.2.2.1 hValue
  have hBalanced : lowerInserted.size = state.upper.size + 1 := by
    simp [lowerInserted, insertHeap_size, hLowerSize, hUpperSize]
  have hLowerNotEmpty : state.lower.isEmpty = false := by
    simp [Array.isEmpty, hLowerSize]
  have hLowerRoot : state.lower[0]? = some state.lower[0]! := by
    rw [getElem?_pos state.lower 0 (by omega), getElem!_pos state.lower 0 (by omega)]
  have hRebalance := rebalanceLoops_eq_self_of_balanced_size lowerInserted state.upper
    (Or.inr hBalanced)
  dsimp at hRebalance
  have hResult : LeanExperiments.RunningMedian.insert state value =
      { lower := lowerInserted, upper := state.upper } := by
    have hRoute : value ≤ state.lower[0]! := hValue
    simp [LeanExperiments.RunningMedian.insert, hLowerNotEmpty, hLowerRoot, hRoute]
    exact Prod.mk.inj hRebalance
  have hPartition := insert_partition state value hInvariant.1
  rw [hResult] at hPartition
  rw [hResult]
  refine ⟨hPartition, hLowerInsertedHeap, hInvariant.2.2.1, ?_, ?_⟩
  · exact hCross
  · simp [lowerInserted, insertHeap_size, hLowerSize, hUpperSize]


/-- 長さ12の任意不変状態で下側根より大きい値を挿入する分岐は不変条件を保つ。

上側最小ヒープへ値を挿入して最小根を下側へ移す。popHeap の残余最小ヒープ契約と
残余要素の下界を使い、挿入後もヒープ間境界が保たれることを示す。
-/
theorem StateInvariant.insert_from_size_twelve_of_gt_root {input : Array Nat}
    {state : LeanExperiments.RunningMedian.State}
    (hInvariant : StateInvariant input state) (hSize : input.size = 12)
    (value : Nat) (hValue : state.lower[0]! < value) :
    StateInvariant (input.push value)
      (LeanExperiments.RunningMedian.insert state value) := by
  have hTotal := StateInvariant.size_partition hInvariant
  have hLowerSize : state.lower.size = 6 := by
    rcases hInvariant.2.2.2.2 with hEqual | hLowerExtra <;> omega
  have hUpperSize : state.upper.size = 6 := by
    rcases hInvariant.2.2.2.2 with hEqual | hLowerExtra <;> omega
  have hUpperMinHeap : MinHeap state.upper :=
    (minHeap_iff_HeapOrdered_minPrefer state.upper).mpr hInvariant.2.2.1
  have hMinPreferEq : minPrefer = LeanExperiments.RunningMedian.minPrefer := by
    funext candidate current
    rfl
  let upperInserted := LeanExperiments.RunningMedian.insertHeap
    LeanExperiments.RunningMedian.minPrefer state.upper value
  have hUpperInsertedHeap : MinHeap upperInserted := by
    have hPrivateInserted : MinHeap
        (LeanExperiments.RunningMedian.insertHeap minPrefer state.upper value) :=
      insertHeap_minPrefer_preserves_of_size_six state.upper hUpperSize value hUpperMinHeap
    simpa [upperInserted, hMinPreferEq] using hPrivateInserted
  have hUpperInsertedSize : upperInserted.size = 7 := by
    simp [upperInserted, insertHeap_size, hUpperSize]
  have hUpperHeap : HeapOrdered LeanExperiments.RunningMedian.minPrefer upperInserted :=
    (minHeap_iff_HeapOrdered_minPrefer upperInserted).mp hUpperInsertedHeap
  have hCross := crossBoundary_insertUpper_of_gt_lowerRoot state value
    (by omega) hInvariant.2.1 hInvariant.2.2.2.1 hValue
  have hCrossRuntime : ∀ lowerIndex (hLowerIndex : lowerIndex < state.lower.size),
      ∀ upperIndex (hUpperIndex : upperIndex < upperInserted.size),
        state.lower[lowerIndex]'hLowerIndex ≤ upperInserted[upperIndex]'hUpperIndex := by
    simpa [upperInserted, hMinPreferEq] using hCross
  let moved := upperInserted[0]!
  have hMovedLower : state.lower[0]! ≤ moved := by
    have hAt := hCrossRuntime 0 (by omega) 0 (by omega)
    calc
      state.lower[0]! = state.lower[0]'(by omega) := getElem!_pos state.lower 0 (by omega)
      _ ≤ upperInserted[0]'(by omega) := hAt
      _ = upperInserted[0]! := (getElem!_pos upperInserted 0 (by omega)).symm
      _ = moved := rfl
  have hPopExists : ∃ rest,
      LeanExperiments.RunningMedian.popHeap LeanExperiments.RunningMedian.minPrefer
        upperInserted = some (moved, rest) := by
    cases hPop : LeanExperiments.RunningMedian.popHeap
        LeanExperiments.RunningMedian.minPrefer upperInserted with
    | none =>
        have hEmpty := (popHeap_eq_none_iff_empty
          LeanExperiments.RunningMedian.minPrefer upperInserted).mp hPop
        rw [hUpperInsertedSize] at hEmpty
        simp at hEmpty
    | some pair =>
        rcases pair with ⟨root, rest⟩
        have hRoot := popHeap_value_eq_root hPop
        have hRootValue : root = moved := by
          have hRoot' : upperInserted[0]? = some root := hRoot
          rw [getElem?_pos _ 0 (by omega)] at hRoot'
          have hEq := Option.some.inj hRoot'
          calc
            root = upperInserted[0]'(by omega) := hEq.symm
            _ = upperInserted[0]! := (getElem!_pos upperInserted 0 (by omega)).symm
            _ = moved := rfl
        subst root
        exact ⟨rest, rfl⟩
  obtain ⟨rest, hPop⟩ := hPopExists
  have hRestHeap : MinHeap rest :=
    popHeap_minPrefer_restMinHeap_of_MinHeap hUpperInsertedHeap hPop
  have hMovedMinimum := popHeap_minPrefer_returns_minimum_of_MinHeap
    hUpperInsertedHeap hPop
  have hRestSize : rest.size = 6 := by
    have hSize := popHeap_size hPop
    simp [upperInserted, insertHeap_size, hUpperSize] at hSize
    omega
  have hRestGe : ∀ index (hIndex : index < rest.size),
      moved ≤ rest[index]'hIndex := by
    intro index hIndex
    have hPerm := popHeap_perm_dropRoot hPop
    have hMem : rest[index]'hIndex ∈ rest.toList := by simp
    have hInTail : rest[index]'hIndex ∈ upperInserted.toList.drop 1 :=
      hPerm.mem_iff.mp hMem
    have hInHeap := List.mem_of_mem_drop hInTail
    have hInArray : rest[index]'hIndex ∈ upperInserted := by simpa using hInHeap
    obtain ⟨heapIndex, hIndexArray, hAt⟩ := Array.mem_iff_getElem.mp hInArray
    have hAtBang : upperInserted[heapIndex]! = rest[index]'hIndex := by
      rw [getElem!_pos _ heapIndex hIndexArray]
      exact hAt
    calc
      moved = upperInserted[0]! := rfl
      _ ≤ upperInserted[heapIndex]! := hMovedMinimum heapIndex hIndexArray
      _ = rest[index]'hIndex := hAtBang
  have hLowerBound : ∀ item, item ∈ state.lower.toList → item ≤ moved := by
    intro item hItem
    have hInArray : item ∈ state.lower := by simpa using hItem
    obtain ⟨index, hIndex, hAt⟩ := Array.mem_iff_getElem.mp hInArray
    have hMaximum := maxHeap_root_is_maximum state.lower hInvariant.2.1 index hIndex
    have hAtBang : state.lower[index]! = item := by
      rw [getElem!_pos _ index hIndex]
      exact hAt
    have hMaximumBang : state.lower[index]! ≤ state.lower[0]! := by
      simpa using hMaximum
    calc
      item = state.lower[index]! := hAtBang.symm
      _ ≤ state.lower[0]! := hMaximumBang
      _ ≤ moved := hMovedLower
  let lowerInserted := LeanExperiments.RunningMedian.insertHeap
    LeanExperiments.RunningMedian.maxPrefer state.lower moved
  have hLowerInsertedHeap : HeapOrdered LeanExperiments.RunningMedian.maxPrefer
      lowerInserted := by
    have hPreferEq : maxPrefer = LeanExperiments.RunningMedian.maxPrefer := by
      funext candidate current
      rfl
    have hPrivateInserted : HeapOrdered maxPrefer
        (LeanExperiments.RunningMedian.insertHeap maxPrefer state.lower moved) :=
      insertHeap_maxPrefer_preserves_of_size_six state.lower hLowerSize moved hInvariant.2.1
    have hPrivateHeap : HeapOrdered maxPrefer lowerInserted := by
      simpa [lowerInserted, hPreferEq] using hPrivateInserted
    simpa [hPreferEq] using hPrivateHeap
  have hLowerInsertedSize : lowerInserted.size = 7 := by
    simp [lowerInserted, insertHeap_size, hLowerSize]
  have hLowerInsertedBound : ∀ item, item ∈ lowerInserted.toList → item ≤ moved := by
    simpa [lowerInserted] using
      (insertHeap_le_of_forall_le LeanExperiments.RunningMedian.maxPrefer
        state.lower moved moved hLowerBound (Nat.le_refl moved))
  have hTransfer : LeanExperiments.RunningMedian.transferUpperRoot
      LeanExperiments.RunningMedian.minPrefer LeanExperiments.RunningMedian.maxPrefer
      state.lower upperInserted = some (lowerInserted, rest) := by
    simp [LeanExperiments.RunningMedian.transferUpperRoot, hPop, lowerInserted, moved]
  have hAfterLower := rebalanceLower_eq_self_of_size_le state.lower upperInserted
    (by simp [upperInserted, insertHeap_size, hLowerSize, hUpperSize])
  have hAfterUpper := rebalanceUpper_one_transfer
    state.lower upperInserted lowerInserted rest
    (by simp [upperInserted, insertHeap_size, hLowerSize, hUpperSize])
    hTransfer (by omega)
  have hLowerNotEmpty : state.lower.isEmpty = false := by
    simp [Array.isEmpty, hLowerSize]
  have hLowerRoot : state.lower[0]? = some state.lower[0]! := by
    rw [getElem?_pos state.lower 0 (by omega), getElem!_pos state.lower 0 (by omega)]
  have hResult : LeanExperiments.RunningMedian.insert state value =
      { lower := lowerInserted, upper := rest } := by
    have hRoute : ¬ value ≤ state.lower[0]! := by omega
    simp [LeanExperiments.RunningMedian.insert, hLowerNotEmpty, hLowerRoot, hRoute,
      upperInserted, hAfterLower, hAfterUpper]
  have hPartition := insert_partition state value hInvariant.1
  rw [hResult] at hPartition
  rw [hResult]
  refine ⟨hPartition, hLowerInsertedHeap,
    (minHeap_iff_HeapOrdered_minPrefer rest).mp hRestHeap, ?_, ?_⟩
  · intro lowerIndex hLowerIndex upperIndex hUpperIndex
    exact Nat.le_trans
      (hLowerInsertedBound _ (Array.getElem_mem_toList hLowerIndex))
      (hRestGe upperIndex hUpperIndex)
  · simp [lowerInserted, hRestSize, insertHeap_size, hLowerSize]


/-- 長さ12の任意不変状態への挿入は、どちらの根比較分岐でも不変条件を保つ。 -/
theorem StateInvariant.insert_of_size_twelve {input : Array Nat}
    {state : LeanExperiments.RunningMedian.State}
    (hInvariant : StateInvariant input state) (hSize : input.size = 12)
    (value : Nat) :
    StateInvariant (input.push value)
      (LeanExperiments.RunningMedian.insert state value) := by
  by_cases hRoot : state.lower[0]! < value
  · exact StateInvariant.insert_from_size_twelve_of_gt_root
      hInvariant hSize value hRoot
  · exact StateInvariant.insert_from_size_twelve_of_le_root
      hInvariant hSize value (by omega)

/-- 長さ15で下側根より大きい値を上側へ挿入しても、状態不変条件を保つ。

上側は7要素なので、任意値挿入後の8要素最小ヒープ契約を使う。下側は8要素のまま
で挿入後の上側と同じ大きさになり、根比較からヒープ間境界も保たれる。
-/
theorem StateInvariant.insert_from_size_fifteen_of_gt_root {input : Array Nat}
    {state : LeanExperiments.RunningMedian.State}
    (hInvariant : StateInvariant input state) (hSize : input.size = 15)
    (value : Nat) (hValue : state.lower[0]! < value) :
    StateInvariant (input.push value)
      (LeanExperiments.RunningMedian.insert state value) := by
  have hTotal := StateInvariant.size_partition hInvariant
  have hLowerSize : state.lower.size = 8 := by
    rcases hInvariant.2.2.2.2 with hEqual | hLowerExtra <;> omega
  have hUpperSize : state.upper.size = 7 := by
    rcases hInvariant.2.2.2.2 with hEqual | hLowerExtra <;> omega
  let upperInserted := LeanExperiments.RunningMedian.insertHeap
    LeanExperiments.RunningMedian.minPrefer state.upper value
  have hMinPreferEq : minPrefer = LeanExperiments.RunningMedian.minPrefer := by
    funext candidate current
    rfl
  have hUpperHeap : MinHeap state.upper :=
    (minHeap_iff_HeapOrdered_minPrefer state.upper).mpr hInvariant.2.2.1
  have hUpperInsertedHeap : MinHeap upperInserted := by
    have hPrivateInserted : MinHeap
        (LeanExperiments.RunningMedian.insertHeap minPrefer state.upper value) :=
      insertHeap_minPrefer_preserves_of_size_seven state.upper hUpperSize value hUpperHeap
    simpa [upperInserted, hMinPreferEq] using hPrivateInserted
  have hUpperOrdered : HeapOrdered LeanExperiments.RunningMedian.minPrefer upperInserted :=
    (minHeap_iff_HeapOrdered_minPrefer upperInserted).mp hUpperInsertedHeap
  have hCross := crossBoundary_insertUpper_of_gt_lowerRoot state value
    (by omega) hInvariant.2.1 hInvariant.2.2.2.1 hValue
  have hBalanced : state.lower.size = upperInserted.size := by
    simp [upperInserted, insertHeap_size, hLowerSize, hUpperSize]
  have hLowerNotEmpty : state.lower.isEmpty = false := by
    simp [Array.isEmpty, hLowerSize]
  have hLowerRoot : state.lower[0]? = some state.lower[0]! := by
    rw [getElem?_pos state.lower 0 (by omega), getElem!_pos state.lower 0 (by omega)]
  have hRebalance := rebalanceLoops_eq_self_of_balanced_size
    state.lower upperInserted (Or.inl hBalanced)
  dsimp at hRebalance
  have hResult : LeanExperiments.RunningMedian.insert state value =
      { lower := state.lower, upper := upperInserted } := by
    have hRoute : ¬ value ≤ state.lower[0]! := by omega
    simp [LeanExperiments.RunningMedian.insert, hLowerNotEmpty, hLowerRoot, hRoute]
    exact ⟨congrArg Prod.fst hRebalance, congrArg Prod.snd hRebalance⟩
  have hPartition := insert_partition state value hInvariant.1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [hResult] using hPartition
  · simpa [hResult] using hInvariant.2.1
  · simpa [hResult, hMinPreferEq] using hUpperOrdered
  · simpa [hResult, upperInserted, hMinPreferEq] using hCross
  · simp [hResult, upperInserted, insertHeap_size, hLowerSize, hUpperSize]

/-- 長さ15の任意不変状態への挿入は、根比較の両分岐で不変条件を保つ。 -/
theorem StateInvariant.insert_of_size_fifteen {input : Array Nat}
    {state : LeanExperiments.RunningMedian.State}
    (hInvariant : StateInvariant input state) (hSize : input.size = 15)
    (value : Nat) :
    StateInvariant (input.push value)
      (LeanExperiments.RunningMedian.insert state value) := by
  by_cases hRoot : state.lower[0]! < value
  · exact StateInvariant.insert_from_size_fifteen_of_gt_root
      hInvariant hSize value hRoot
  · exact StateInvariant.insert_from_size_fifteen_of_le_root
      hInvariant hSize value (by omega)

/-- 長さ14で下側根以下の値を下側へ挿入しても、状態不変条件を保つ。 -/
theorem StateInvariant.insert_from_size_fourteen_of_le_root {input : Array Nat}
    {state : LeanExperiments.RunningMedian.State}
    (hInvariant : StateInvariant input state) (hSize : input.size = 14)
    (value : Nat) (hValue : value ≤ state.lower[0]!) :
    StateInvariant (input.push value)
      (LeanExperiments.RunningMedian.insert state value) := by
  have hTotal := StateInvariant.size_partition hInvariant
  have hLowerSize : state.lower.size = 7 := by
    rcases hInvariant.2.2.2.2 with hEqual | hLowerExtra <;> omega
  have hUpperSize : state.upper.size = 7 := by
    rcases hInvariant.2.2.2.2 with hEqual | hLowerExtra <;> omega
  let lowerInserted := LeanExperiments.RunningMedian.insertHeap maxPrefer state.lower value
  have hPreferEq : maxPrefer = LeanExperiments.RunningMedian.maxPrefer := by
    funext candidate current
    rfl
  have hLowerInsertedPrivate : HeapOrdered maxPrefer lowerInserted := by
    simpa [lowerInserted, hPreferEq] using
      insertHeap_maxPrefer_preserves_of_size_seven state.lower hLowerSize value hInvariant.2.1
  have hLowerInsertedHeap : HeapOrdered LeanExperiments.RunningMedian.maxPrefer lowerInserted := by
    simpa [hPreferEq] using hLowerInsertedPrivate
  have hCross := crossBoundary_insertLower_of_le_lowerRoot state value
    (by omega) hInvariant.2.2.2.1 hValue
  have hLowerInsertedSize : lowerInserted.size = 8 := by
    simp [lowerInserted, insertHeap_size, hLowerSize]
  have hBalanced : lowerInserted.size = state.upper.size + 1 := by
    omega
  have hLowerNotEmpty : state.lower.isEmpty = false := by
    simp [Array.isEmpty, hLowerSize]
  have hLowerRoot : state.lower[0]? = some state.lower[0]! := by
    rw [getElem?_pos state.lower 0 (by omega), getElem!_pos state.lower 0 (by omega)]
  have hRebalance := rebalanceLoops_eq_self_of_balanced_size lowerInserted state.upper
    (Or.inr hBalanced)
  dsimp at hRebalance
  have hResult : LeanExperiments.RunningMedian.insert state value =
      { lower := lowerInserted, upper := state.upper } := by
    have hRoute : value ≤ state.lower[0]! := hValue
    simp [LeanExperiments.RunningMedian.insert, hLowerNotEmpty, hLowerRoot, hRoute]
    exact Prod.mk.inj hRebalance
  have hPartition := insert_partition state value hInvariant.1
  rw [hResult] at hPartition
  rw [hResult]
  refine ⟨hPartition, hLowerInsertedHeap, hInvariant.2.2.1, ?_, ?_⟩
  · exact hCross
  · simp [lowerInserted, insertHeap_size, hLowerSize, hUpperSize]

/-- 長さ14の任意不変状態で下側根より大きい値を挿入する分岐は不変条件を保つ。

上側最小ヒープへ値を挿入して最小根を下側へ移す。popHeap の残余最小ヒープ契約と
残余要素の下界を使い、挿入後もヒープ間境界が保たれることを示す。
-/
theorem StateInvariant.insert_from_size_fourteen_of_gt_root {input : Array Nat}
    {state : LeanExperiments.RunningMedian.State}
    (hInvariant : StateInvariant input state) (hSize : input.size = 14)
    (value : Nat) (hValue : state.lower[0]! < value) :
    StateInvariant (input.push value)
      (LeanExperiments.RunningMedian.insert state value) := by
  have hTotal := StateInvariant.size_partition hInvariant
  have hLowerSize : state.lower.size = 7 := by
    rcases hInvariant.2.2.2.2 with hEqual | hLowerExtra <;> omega
  have hUpperSize : state.upper.size = 7 := by
    rcases hInvariant.2.2.2.2 with hEqual | hLowerExtra <;> omega
  have hUpperMinHeap : MinHeap state.upper :=
    (minHeap_iff_HeapOrdered_minPrefer state.upper).mpr hInvariant.2.2.1
  have hMinPreferEq : minPrefer = LeanExperiments.RunningMedian.minPrefer := by
    funext candidate current
    rfl
  let upperInserted := LeanExperiments.RunningMedian.insertHeap
    LeanExperiments.RunningMedian.minPrefer state.upper value
  have hUpperInsertedHeap : MinHeap upperInserted := by
    have hPrivateInserted : MinHeap
        (LeanExperiments.RunningMedian.insertHeap minPrefer state.upper value) :=
      insertHeap_minPrefer_preserves_of_size_seven state.upper hUpperSize value hUpperMinHeap
    simpa [upperInserted, hMinPreferEq] using hPrivateInserted
  have hUpperInsertedSize : upperInserted.size = 8 := by
    simp [upperInserted, insertHeap_size, hUpperSize]
  have hUpperHeap : HeapOrdered LeanExperiments.RunningMedian.minPrefer upperInserted :=
    (minHeap_iff_HeapOrdered_minPrefer upperInserted).mp hUpperInsertedHeap
  have hCross := crossBoundary_insertUpper_of_gt_lowerRoot state value
    (by omega) hInvariant.2.1 hInvariant.2.2.2.1 hValue
  have hCrossRuntime : ∀ lowerIndex (hLowerIndex : lowerIndex < state.lower.size),
      ∀ upperIndex (hUpperIndex : upperIndex < upperInserted.size),
        state.lower[lowerIndex]'hLowerIndex ≤ upperInserted[upperIndex]'hUpperIndex := by
    simpa [upperInserted, hMinPreferEq] using hCross
  let moved := upperInserted[0]!
  have hMovedLower : state.lower[0]! ≤ moved := by
    have hAt := hCrossRuntime 0 (by omega) 0 (by omega)
    calc
      state.lower[0]! = state.lower[0]'(by omega) := getElem!_pos state.lower 0 (by omega)
      _ ≤ upperInserted[0]'(by omega) := hAt
      _ = upperInserted[0]! := (getElem!_pos upperInserted 0 (by omega)).symm
      _ = moved := rfl
  have hPopExists : ∃ rest,
      LeanExperiments.RunningMedian.popHeap LeanExperiments.RunningMedian.minPrefer
        upperInserted = some (moved, rest) := by
    cases hPop : LeanExperiments.RunningMedian.popHeap
        LeanExperiments.RunningMedian.minPrefer upperInserted with
    | none =>
        have hEmpty := (popHeap_eq_none_iff_empty
          LeanExperiments.RunningMedian.minPrefer upperInserted).mp hPop
        rw [hUpperInsertedSize] at hEmpty
        simp at hEmpty
    | some pair =>
        rcases pair with ⟨root, rest⟩
        have hRoot := popHeap_value_eq_root hPop
        have hRootValue : root = moved := by
          have hRoot' : upperInserted[0]? = some root := hRoot
          rw [getElem?_pos _ 0 (by omega)] at hRoot'
          have hEq := Option.some.inj hRoot'
          calc
            root = upperInserted[0]'(by omega) := hEq.symm
            _ = upperInserted[0]! := (getElem!_pos upperInserted 0 (by omega)).symm
            _ = moved := rfl
        subst root
        exact ⟨rest, rfl⟩
  obtain ⟨rest, hPop⟩ := hPopExists
  have hRestHeap : MinHeap rest :=
    popHeap_minPrefer_restMinHeap_of_MinHeap hUpperInsertedHeap hPop
  have hMovedMinimum := popHeap_minPrefer_returns_minimum_of_MinHeap
    hUpperInsertedHeap hPop
  have hRestSize : rest.size = 7 := by
    have hSize := popHeap_size hPop
    simp [upperInserted, insertHeap_size, hUpperSize] at hSize
    omega
  have hRestGe : ∀ index (hIndex : index < rest.size),
      moved ≤ rest[index]'hIndex := by
    intro index hIndex
    have hPerm := popHeap_perm_dropRoot hPop
    have hMem : rest[index]'hIndex ∈ rest.toList := by simp
    have hInTail : rest[index]'hIndex ∈ upperInserted.toList.drop 1 :=
      hPerm.mem_iff.mp hMem
    have hInHeap := List.mem_of_mem_drop hInTail
    have hInArray : rest[index]'hIndex ∈ upperInserted := by simpa using hInHeap
    obtain ⟨heapIndex, hIndexArray, hAt⟩ := Array.mem_iff_getElem.mp hInArray
    have hAtBang : upperInserted[heapIndex]! = rest[index]'hIndex := by
      rw [getElem!_pos _ heapIndex hIndexArray]
      exact hAt
    calc
      moved = upperInserted[0]! := rfl
      _ ≤ upperInserted[heapIndex]! := hMovedMinimum heapIndex hIndexArray
      _ = rest[index]'hIndex := hAtBang
  have hLowerBound : ∀ item, item ∈ state.lower.toList → item ≤ moved := by
    intro item hItem
    have hInArray : item ∈ state.lower := by simpa using hItem
    obtain ⟨index, hIndex, hAt⟩ := Array.mem_iff_getElem.mp hInArray
    have hMaximum := maxHeap_root_is_maximum state.lower hInvariant.2.1 index hIndex
    have hAtBang : state.lower[index]! = item := by
      rw [getElem!_pos _ index hIndex]
      exact hAt
    have hMaximumBang : state.lower[index]! ≤ state.lower[0]! := by
      simpa using hMaximum
    calc
      item = state.lower[index]! := hAtBang.symm
      _ ≤ state.lower[0]! := hMaximumBang
      _ ≤ moved := hMovedLower
  let lowerInserted := LeanExperiments.RunningMedian.insertHeap
    LeanExperiments.RunningMedian.maxPrefer state.lower moved
  have hLowerInsertedHeap : HeapOrdered LeanExperiments.RunningMedian.maxPrefer
      lowerInserted := by
    have hPreferEq : maxPrefer = LeanExperiments.RunningMedian.maxPrefer := by
      funext candidate current
      rfl
    have hPrivateInserted : HeapOrdered maxPrefer
        (LeanExperiments.RunningMedian.insertHeap maxPrefer state.lower moved) :=
      insertHeap_maxPrefer_preserves_of_size_seven state.lower hLowerSize moved hInvariant.2.1
    have hPrivateHeap : HeapOrdered maxPrefer lowerInserted := by
      simpa [lowerInserted, hPreferEq] using hPrivateInserted
    simpa [hPreferEq] using hPrivateHeap
  have hLowerInsertedSize : lowerInserted.size = 8 := by
    simp [lowerInserted, insertHeap_size, hLowerSize]
  have hLowerInsertedBound : ∀ item, item ∈ lowerInserted.toList → item ≤ moved := by
    simpa [lowerInserted] using
      (insertHeap_le_of_forall_le LeanExperiments.RunningMedian.maxPrefer
        state.lower moved moved hLowerBound (Nat.le_refl moved))
  have hTransfer : LeanExperiments.RunningMedian.transferUpperRoot
      LeanExperiments.RunningMedian.minPrefer LeanExperiments.RunningMedian.maxPrefer
      state.lower upperInserted = some (lowerInserted, rest) := by
    simp [LeanExperiments.RunningMedian.transferUpperRoot, hPop, lowerInserted, moved]
  have hAfterLower := rebalanceLower_eq_self_of_size_le state.lower upperInserted
    (by simp [upperInserted, insertHeap_size, hLowerSize, hUpperSize])
  have hAfterUpper := rebalanceUpper_one_transfer
    state.lower upperInserted lowerInserted rest
    (by simp [upperInserted, insertHeap_size, hLowerSize, hUpperSize])
    hTransfer (by omega)
  have hLowerNotEmpty : state.lower.isEmpty = false := by
    simp [Array.isEmpty, hLowerSize]
  have hLowerRoot : state.lower[0]? = some state.lower[0]! := by
    rw [getElem?_pos state.lower 0 (by omega), getElem!_pos state.lower 0 (by omega)]
  have hResult : LeanExperiments.RunningMedian.insert state value =
      { lower := lowerInserted, upper := rest } := by
    have hRoute : ¬ value ≤ state.lower[0]! := by omega
    simp [LeanExperiments.RunningMedian.insert, hLowerNotEmpty, hLowerRoot, hRoute,
      upperInserted, hAfterLower, hAfterUpper]
  have hPartition := insert_partition state value hInvariant.1
  rw [hResult] at hPartition
  rw [hResult]
  refine ⟨hPartition, hLowerInsertedHeap,
    (minHeap_iff_HeapOrdered_minPrefer rest).mp hRestHeap, ?_, ?_⟩
  · intro lowerIndex hLowerIndex upperIndex hUpperIndex
    exact Nat.le_trans
      (hLowerInsertedBound _ (Array.getElem_mem_toList hLowerIndex))
      (hRestGe upperIndex hUpperIndex)
  · simp [lowerInserted, hRestSize, insertHeap_size, hLowerSize]


/-- 長さ16で下側根以下の値を下側へ挿入しても、状態不変条件を保つ。 -/
theorem StateInvariant.insert_from_size_sixteen_of_le_root {input : Array Nat}
    {state : LeanExperiments.RunningMedian.State}
    (hInvariant : StateInvariant input state) (hSize : input.size = 16)
    (value : Nat) (hValue : value ≤ state.lower[0]!) :
    StateInvariant (input.push value)
      (LeanExperiments.RunningMedian.insert state value) := by
  have hTotal := StateInvariant.size_partition hInvariant
  have hLowerSize : state.lower.size = 8 := by
    rcases hInvariant.2.2.2.2 with hEqual | hLowerExtra <;> omega
  have hUpperSize : state.upper.size = 8 := by
    rcases hInvariant.2.2.2.2 with hEqual | hLowerExtra <;> omega
  let lowerInserted := LeanExperiments.RunningMedian.insertHeap maxPrefer state.lower value
  have hPreferEq : maxPrefer = LeanExperiments.RunningMedian.maxPrefer := by
    funext candidate current
    rfl
  have hLowerInsertedPrivate : HeapOrdered maxPrefer lowerInserted := by
    simpa [lowerInserted, hPreferEq] using
      insertHeap_maxPrefer_preserves_of_size_eight state.lower hLowerSize value hInvariant.2.1
  have hLowerInsertedHeap : HeapOrdered LeanExperiments.RunningMedian.maxPrefer lowerInserted := by
    simpa [hPreferEq] using hLowerInsertedPrivate
  have hCross := crossBoundary_insertLower_of_le_lowerRoot state value
    (by omega) hInvariant.2.2.2.1 hValue
  have hLowerInsertedSize : lowerInserted.size = 9 := by
    simp [lowerInserted, insertHeap_size, hLowerSize]
  have hBalanced : lowerInserted.size = state.upper.size + 1 := by
    omega
  have hLowerNotEmpty : state.lower.isEmpty = false := by
    simp [Array.isEmpty, hLowerSize]
  have hLowerRoot : state.lower[0]? = some state.lower[0]! := by
    rw [getElem?_pos state.lower 0 (by omega), getElem!_pos state.lower 0 (by omega)]
  have hRebalance := rebalanceLoops_eq_self_of_balanced_size lowerInserted state.upper
    (Or.inr hBalanced)
  dsimp at hRebalance
  have hResult : LeanExperiments.RunningMedian.insert state value =
      { lower := lowerInserted, upper := state.upper } := by
    have hRoute : value ≤ state.lower[0]! := hValue
    simp [LeanExperiments.RunningMedian.insert, hLowerNotEmpty, hLowerRoot, hRoute]
    exact Prod.mk.inj hRebalance
  have hPartition := insert_partition state value hInvariant.1
  rw [hResult] at hPartition
  rw [hResult]
  refine ⟨hPartition, hLowerInsertedHeap, hInvariant.2.2.1, ?_, ?_⟩
  · exact hCross
  · simp [lowerInserted, insertHeap_size, hLowerSize, hUpperSize]

/-- 長さ16の任意不変状態で下側根より大きい値を挿入する分岐は不変条件を保つ。

上側最小ヒープへ値を挿入して最小根を下側へ移す。popHeap の残余最小ヒープ契約と
残余要素の下界を使い、挿入後もヒープ間境界が保たれることを示す。
-/
theorem StateInvariant.insert_from_size_sixteen_of_gt_root {input : Array Nat}
    {state : LeanExperiments.RunningMedian.State}
    (hInvariant : StateInvariant input state) (hSize : input.size = 16)
    (value : Nat) (hValue : state.lower[0]! < value) :
    StateInvariant (input.push value)
      (LeanExperiments.RunningMedian.insert state value) := by
  have hTotal := StateInvariant.size_partition hInvariant
  have hLowerSize : state.lower.size = 8 := by
    rcases hInvariant.2.2.2.2 with hEqual | hLowerExtra <;> omega
  have hUpperSize : state.upper.size = 8 := by
    rcases hInvariant.2.2.2.2 with hEqual | hLowerExtra <;> omega
  have hUpperMinHeap : MinHeap state.upper :=
    (minHeap_iff_HeapOrdered_minPrefer state.upper).mpr hInvariant.2.2.1
  have hMinPreferEq : minPrefer = LeanExperiments.RunningMedian.minPrefer := by
    funext candidate current
    rfl
  let upperInserted := LeanExperiments.RunningMedian.insertHeap
    LeanExperiments.RunningMedian.minPrefer state.upper value
  have hUpperInsertedHeap : MinHeap upperInserted := by
    have hPrivateInserted : MinHeap
        (LeanExperiments.RunningMedian.insertHeap minPrefer state.upper value) :=
      insertHeap_minPrefer_preserves_of_size_eight state.upper hUpperSize value hUpperMinHeap
    simpa [upperInserted, hMinPreferEq] using hPrivateInserted
  have hUpperInsertedSize : upperInserted.size = 9 := by
    simp [upperInserted, insertHeap_size, hUpperSize]
  have hUpperHeap : HeapOrdered LeanExperiments.RunningMedian.minPrefer upperInserted :=
    (minHeap_iff_HeapOrdered_minPrefer upperInserted).mp hUpperInsertedHeap
  have hCross := crossBoundary_insertUpper_of_gt_lowerRoot state value
    (by omega) hInvariant.2.1 hInvariant.2.2.2.1 hValue
  have hCrossRuntime : ∀ lowerIndex (hLowerIndex : lowerIndex < state.lower.size),
      ∀ upperIndex (hUpperIndex : upperIndex < upperInserted.size),
        state.lower[lowerIndex]'hLowerIndex ≤ upperInserted[upperIndex]'hUpperIndex := by
    simpa [upperInserted, hMinPreferEq] using hCross
  let moved := upperInserted[0]!
  have hMovedLower : state.lower[0]! ≤ moved := by
    have hAt := hCrossRuntime 0 (by omega) 0 (by omega)
    calc
      state.lower[0]! = state.lower[0]'(by omega) := getElem!_pos state.lower 0 (by omega)
      _ ≤ upperInserted[0]'(by omega) := hAt
      _ = upperInserted[0]! := (getElem!_pos upperInserted 0 (by omega)).symm
      _ = moved := rfl
  have hPopExists : ∃ rest,
      LeanExperiments.RunningMedian.popHeap LeanExperiments.RunningMedian.minPrefer
        upperInserted = some (moved, rest) := by
    cases hPop : LeanExperiments.RunningMedian.popHeap
        LeanExperiments.RunningMedian.minPrefer upperInserted with
    | none =>
        have hEmpty := (popHeap_eq_none_iff_empty
          LeanExperiments.RunningMedian.minPrefer upperInserted).mp hPop
        rw [hUpperInsertedSize] at hEmpty
        simp at hEmpty
    | some pair =>
        rcases pair with ⟨root, rest⟩
        have hRoot := popHeap_value_eq_root hPop
        have hRootValue : root = moved := by
          have hRoot' : upperInserted[0]? = some root := hRoot
          rw [getElem?_pos _ 0 (by omega)] at hRoot'
          have hEq := Option.some.inj hRoot'
          calc
            root = upperInserted[0]'(by omega) := hEq.symm
            _ = upperInserted[0]! := (getElem!_pos upperInserted 0 (by omega)).symm
            _ = moved := rfl
        subst root
        exact ⟨rest, rfl⟩
  obtain ⟨rest, hPop⟩ := hPopExists
  have hRestHeap : MinHeap rest :=
    popHeap_minPrefer_restMinHeap_of_MinHeap hUpperInsertedHeap hPop
  have hMovedMinimum := popHeap_minPrefer_returns_minimum_of_MinHeap
    hUpperInsertedHeap hPop
  have hRestSize : rest.size = 8 := by
    have hSize := popHeap_size hPop
    simp [upperInserted, insertHeap_size, hUpperSize] at hSize
    omega
  have hRestGe : ∀ index (hIndex : index < rest.size),
      moved ≤ rest[index]'hIndex := by
    intro index hIndex
    have hPerm := popHeap_perm_dropRoot hPop
    have hMem : rest[index]'hIndex ∈ rest.toList := by simp
    have hInTail : rest[index]'hIndex ∈ upperInserted.toList.drop 1 :=
      hPerm.mem_iff.mp hMem
    have hInHeap := List.mem_of_mem_drop hInTail
    have hInArray : rest[index]'hIndex ∈ upperInserted := by simpa using hInHeap
    obtain ⟨heapIndex, hIndexArray, hAt⟩ := Array.mem_iff_getElem.mp hInArray
    have hAtBang : upperInserted[heapIndex]! = rest[index]'hIndex := by
      rw [getElem!_pos _ heapIndex hIndexArray]
      exact hAt
    calc
      moved = upperInserted[0]! := rfl
      _ ≤ upperInserted[heapIndex]! := hMovedMinimum heapIndex hIndexArray
      _ = rest[index]'hIndex := hAtBang
  have hLowerBound : ∀ item, item ∈ state.lower.toList → item ≤ moved := by
    intro item hItem
    have hInArray : item ∈ state.lower := by simpa using hItem
    obtain ⟨index, hIndex, hAt⟩ := Array.mem_iff_getElem.mp hInArray
    have hMaximum := maxHeap_root_is_maximum state.lower hInvariant.2.1 index hIndex
    have hAtBang : state.lower[index]! = item := by
      rw [getElem!_pos _ index hIndex]
      exact hAt
    have hMaximumBang : state.lower[index]! ≤ state.lower[0]! := by
      simpa using hMaximum
    calc
      item = state.lower[index]! := hAtBang.symm
      _ ≤ state.lower[0]! := hMaximumBang
      _ ≤ moved := hMovedLower
  let lowerInserted := LeanExperiments.RunningMedian.insertHeap
    LeanExperiments.RunningMedian.maxPrefer state.lower moved
  have hLowerInsertedHeap : HeapOrdered LeanExperiments.RunningMedian.maxPrefer
      lowerInserted := by
    have hPreferEq : maxPrefer = LeanExperiments.RunningMedian.maxPrefer := by
      funext candidate current
      rfl
    have hPrivateInserted : HeapOrdered maxPrefer
        (LeanExperiments.RunningMedian.insertHeap maxPrefer state.lower moved) :=
      insertHeap_maxPrefer_preserves_of_size_eight state.lower hLowerSize moved hInvariant.2.1
    have hPrivateHeap : HeapOrdered maxPrefer lowerInserted := by
      simpa [lowerInserted, hPreferEq] using hPrivateInserted
    simpa [hPreferEq] using hPrivateHeap
  have hLowerInsertedSize : lowerInserted.size = 9 := by
    simp [lowerInserted, insertHeap_size, hLowerSize]
  have hLowerInsertedBound : ∀ item, item ∈ lowerInserted.toList → item ≤ moved := by
    simpa [lowerInserted] using
      (insertHeap_le_of_forall_le LeanExperiments.RunningMedian.maxPrefer
        state.lower moved moved hLowerBound (Nat.le_refl moved))
  have hTransfer : LeanExperiments.RunningMedian.transferUpperRoot
      LeanExperiments.RunningMedian.minPrefer LeanExperiments.RunningMedian.maxPrefer
      state.lower upperInserted = some (lowerInserted, rest) := by
    simp [LeanExperiments.RunningMedian.transferUpperRoot, hPop, lowerInserted, moved]
  have hAfterLower := rebalanceLower_eq_self_of_size_le state.lower upperInserted
    (by simp [upperInserted, insertHeap_size, hLowerSize, hUpperSize])
  have hAfterUpper := rebalanceUpper_one_transfer
    state.lower upperInserted lowerInserted rest
    (by simp [upperInserted, insertHeap_size, hLowerSize, hUpperSize])
    hTransfer (by omega)
  have hLowerNotEmpty : state.lower.isEmpty = false := by
    simp [Array.isEmpty, hLowerSize]
  have hLowerRoot : state.lower[0]? = some state.lower[0]! := by
    rw [getElem?_pos state.lower 0 (by omega), getElem!_pos state.lower 0 (by omega)]
  have hResult : LeanExperiments.RunningMedian.insert state value =
      { lower := lowerInserted, upper := rest } := by
    have hRoute : ¬ value ≤ state.lower[0]! := by omega
    simp [LeanExperiments.RunningMedian.insert, hLowerNotEmpty, hLowerRoot, hRoute,
      upperInserted, hAfterLower, hAfterUpper]
  have hPartition := insert_partition state value hInvariant.1
  rw [hResult] at hPartition
  rw [hResult]
  refine ⟨hPartition, hLowerInsertedHeap,
    (minHeap_iff_HeapOrdered_minPrefer rest).mp hRestHeap, ?_, ?_⟩
  · intro lowerIndex hLowerIndex upperIndex hUpperIndex
    exact Nat.le_trans
      (hLowerInsertedBound _ (Array.getElem_mem_toList hLowerIndex))
      (hRestGe upperIndex hUpperIndex)
  · simp [lowerInserted, hRestSize, insertHeap_size, hLowerSize]


/-- 長さ16の任意不変状態への挿入は、根比較の両分岐で不変条件を保つ。 -/
theorem StateInvariant.insert_of_size_sixteen {input : Array Nat}
    {state : LeanExperiments.RunningMedian.State}
    (hInvariant : StateInvariant input state) (hSize : input.size = 16)
    (value : Nat) :
    StateInvariant (input.push value)
      (LeanExperiments.RunningMedian.insert state value) := by
  by_cases hRoot : state.lower[0]! < value
  · exact StateInvariant.insert_from_size_sixteen_of_gt_root
      hInvariant hSize value hRoot
  · exact StateInvariant.insert_from_size_sixteen_of_le_root
      hInvariant hSize value (by omega)

/-- 長さ14の任意不変状態への挿入は、両方の根比較分岐で不変条件を保つ。 -/
theorem StateInvariant.insert_of_size_fourteen {input : Array Nat}
    {state : LeanExperiments.RunningMedian.State}
    (hInvariant : StateInvariant input state) (hSize : input.size = 14)
    (value : Nat) :
    StateInvariant (input.push value)
      (LeanExperiments.RunningMedian.insert state value) := by
  by_cases hRoot : state.lower[0]! < value
  · exact StateInvariant.insert_from_size_fourteen_of_gt_root
      hInvariant hSize value hRoot
  · exact StateInvariant.insert_from_size_fourteen_of_le_root
      hInvariant hSize value (by omega)

/-- 長さ6の任意の不変状態で下側根より大きい値を挿入する分岐は不変条件を保つ。 -/
theorem StateInvariant.insert_from_size_six_of_gt_root {input : Array Nat}
    {state : LeanExperiments.RunningMedian.State}
    (hInvariant : StateInvariant input state) (hSize : input.size = 6)
    (value : Nat) (hValue : state.lower[0]! < value) :
    StateInvariant (input.push value)
      (LeanExperiments.RunningMedian.insert state value) := by
  have hTotal := StateInvariant.size_partition hInvariant
  have hLowerSize : state.lower.size = 3 := by
    rcases hInvariant.2.2.2.2 with hBalanced | hLowerExtra <;> omega
  have hUpperSize : state.upper.size = 3 := by
    rcases hInvariant.2.2.2.2 with hBalanced | hLowerExtra <;> omega
  let lowerRoot := state.lower[0]'(by omega)
  let lowerLeft := state.lower[1]'(by omega)
  let lowerRight := state.lower[2]'(by omega)
  let upperRoot := state.upper[0]'(by omega)
  let upperLeft := state.upper[1]'(by omega)
  let upperRight := state.upper[2]'(by omega)
  have hLowerEq : state.lower = #[lowerRoot, lowerLeft, lowerRight] := by
    apply Array.ext
    · exact hLowerSize
    · intro index hIndex hBound
      have hCases : index = 0 ∨ index = 1 ∨ index = 2 := by omega
      rcases hCases with h | h | h <;> subst index
      · simp [lowerRoot]
      · simp [lowerLeft]
      · simp [lowerRight]
  have hUpperEq : state.upper = #[upperRoot, upperLeft, upperRight] := by
    apply Array.ext
    · exact hUpperSize
    · intro index hIndex hBound
      have hCases : index = 0 ∨ index = 1 ∨ index = 2 := by omega
      rcases hCases with h | h | h <;> subst index
      · simp [upperRoot]
      · simp [upperLeft]
      · simp [upperRight]
  have hState : state = {
      lower := #[lowerRoot, lowerLeft, lowerRight],
      upper := #[upperRoot, upperLeft, upperRight] } := by
    cases state with
    | mk lower upper =>
        simp only [LeanExperiments.RunningMedian.State.mk.injEq]
        exact ⟨hLowerEq, hUpperEq⟩
  have hRootValue : lowerRoot < value := by
    have hBang : state.lower[0]! = state.lower[0]'(by omega) :=
      getElem!_pos state.lower 0 (by omega)
    simpa [lowerRoot, hBang] using hValue
  exact StateInvariant.insert_from_three_three_of_gt_root
    hInvariant hState hRootValue

/-- 長さ6の任意の不変状態への挿入は不変条件を保つ。 -/
theorem StateInvariant.insert_of_size_six {input : Array Nat}
    {state : LeanExperiments.RunningMedian.State}
    (hInvariant : StateInvariant input state) (hSize : input.size = 6)
    (value : Nat) :
    StateInvariant (input.push value)
      (LeanExperiments.RunningMedian.insert state value) := by
  by_cases hRoot : state.lower[0]! < value
  · exact StateInvariant.insert_from_size_six_of_gt_root
      hInvariant hSize value hRoot
  · exact StateInvariant.insert_from_size_six_of_le_root
      hInvariant hSize value (by omega)

/-- 長さ3の任意の不変状態で下側根より大きい値を挿入する分岐は不変条件を保つ。

サイズ式から状態を2+1要素と特定し、明示したヒープ形に対する挿入契約へ帰着する。
仮定する状態は `ofArray` の出力に限らず、論理的不変条件を満たす任意の状態でよい。
-/
theorem StateInvariant.insert_from_size_three_of_gt_root {input : Array Nat}
    {state : LeanExperiments.RunningMedian.State}
    (hInvariant : StateInvariant input state) (hSize : input.size = 3)
    (value : Nat) (hValue : state.lower[0]! < value) :
    StateInvariant (input.push value)
      (LeanExperiments.RunningMedian.insert state value) := by
  have hTotal := StateInvariant.size_partition hInvariant
  have hLowerSize : state.lower.size = 2 := by
    rcases hInvariant.2.2.2.2 with hBalanced | hLowerExtra <;> omega
  have hUpperSize : state.upper.size = 1 := by
    rcases hInvariant.2.2.2.2 with hBalanced | hLowerExtra <;> omega
  let lowerRoot := state.lower[0]'(by omega)
  let lowerOther := state.lower[1]'(by omega)
  let upperRoot := state.upper[0]'(by omega)
  have hLowerEq : state.lower = #[lowerRoot, lowerOther] := by
    apply Array.ext
    · exact hLowerSize
    · intro index hIndex hBound
      have hCases : index = 0 ∨ index = 1 := by omega
      rcases hCases with hZero | hOne
      · subst index
        simp [lowerRoot]
      · subst index
        simp [lowerOther]
  have hUpperEq : state.upper = #[upperRoot] := by
    apply Array.ext
    · exact hUpperSize
    · intro index hIndex hBound
      have hZero : index = 0 := by omega
      subst index
      simp [upperRoot]
  have hState : state =
      { lower := #[lowerRoot, lowerOther], upper := #[upperRoot] } := by
    cases state with
    | mk lower upper =>
        simp only [LeanExperiments.RunningMedian.State.mk.injEq]
        exact ⟨hLowerEq, hUpperEq⟩
  have hRootValue : lowerRoot < value := by
    have hBang : state.lower[0]! = state.lower[0]'(by omega) :=
      getElem!_pos state.lower 0 (by omega)
    simpa [lowerRoot, hBang] using hValue
  exact StateInvariant.insert_from_two_one_of_gt_root hInvariant hState hRootValue

/-- 長さ3の任意の不変状態で下側根以下の値を挿入する分岐は不変条件を保つ。

サイズ式から2+1要素の状態形を特定し、根の取り出しと一回の再平衡を使った
下側挿入契約へ帰着する。
-/
theorem StateInvariant.insert_from_size_three_of_le_root {input : Array Nat}
    {state : LeanExperiments.RunningMedian.State}
    (hInvariant : StateInvariant input state) (hSize : input.size = 3)
    (value : Nat) (hValue : value ≤ state.lower[0]!) :
    StateInvariant (input.push value)
      (LeanExperiments.RunningMedian.insert state value) := by
  have hTotal := StateInvariant.size_partition hInvariant
  have hLowerSize : state.lower.size = 2 := by
    rcases hInvariant.2.2.2.2 with hBalanced | hLowerExtra <;> omega
  have hUpperSize : state.upper.size = 1 := by
    rcases hInvariant.2.2.2.2 with hBalanced | hLowerExtra <;> omega
  let lowerRoot := state.lower[0]'(by omega)
  let lowerOther := state.lower[1]'(by omega)
  let upperRoot := state.upper[0]'(by omega)
  have hLowerEq : state.lower = #[lowerRoot, lowerOther] := by
    apply Array.ext
    · exact hLowerSize
    · intro index hIndex hBound
      have hCases : index = 0 ∨ index = 1 := by omega
      rcases hCases with hZero | hOne
      · subst index
        simp [lowerRoot]
      · subst index
        simp [lowerOther]
  have hUpperEq : state.upper = #[upperRoot] := by
    apply Array.ext
    · exact hUpperSize
    · intro index hIndex hBound
      have hZero : index = 0 := by omega
      subst index
      simp [upperRoot]
  have hState : state =
      { lower := #[lowerRoot, lowerOther], upper := #[upperRoot] } := by
    cases state with
    | mk lower upper =>
        simp only [LeanExperiments.RunningMedian.State.mk.injEq]
        exact ⟨hLowerEq, hUpperEq⟩
  have hRootValue : value ≤ lowerRoot := by
    have hBang : state.lower[0]! = state.lower[0]'(by omega) :=
      getElem!_pos state.lower 0 (by omega)
    simpa [lowerRoot, hBang] using hValue
  exact StateInvariant.insert_from_two_one_of_le_root hInvariant hState hRootValue

/-- 入力長3以下の任意の不変状態への挿入は、値の大小を問わず不変条件を保つ。 -/
theorem StateInvariant.insert_of_size_le_three {input : Array Nat}
    {state : LeanExperiments.RunningMedian.State}
    (hInvariant : StateInvariant input state) (hSize : input.size ≤ 3)
    (value : Nat) :
    StateInvariant (input.push value)
      (LeanExperiments.RunningMedian.insert state value) := by
  by_cases hSmall : input.size ≤ 2
  · exact StateInvariant.insert_of_size_le_two hInvariant hSmall value
  · have hInputSize : input.size = 3 := by omega
    have hTotal := StateInvariant.size_partition hInvariant
    have hLowerSize : state.lower.size = 2 := by
      rcases hInvariant.2.2.2.2 with hBalanced | hLowerExtra <;> omega
    have hUpperSize : state.upper.size = 1 := by
      rcases hInvariant.2.2.2.2 with hBalanced | hLowerExtra <;> omega
    have hLowerRoot : 0 < state.lower.size := by omega
    by_cases hRoute : value ≤ state.lower[0]!
    · exact StateInvariant.insert_from_size_three_of_le_root
        hInvariant hInputSize value hRoute
    · exact StateInvariant.insert_from_size_three_of_gt_root
        hInvariant hInputSize value (by omega)

/-- 入力長4以下の任意の不変状態への挿入は、値の大小を問わず不変条件を保つ。 -/
theorem StateInvariant.insert_of_size_le_four {input : Array Nat}
    {state : LeanExperiments.RunningMedian.State}
    (hInvariant : StateInvariant input state) (hSize : input.size ≤ 4)
    (value : Nat) :
    StateInvariant (input.push value)
      (LeanExperiments.RunningMedian.insert state value) := by
  by_cases hSmall : input.size ≤ 3
  · exact StateInvariant.insert_of_size_le_three hInvariant hSmall value
  · have hInputSize : input.size = 4 := by omega
    by_cases hRoute : value ≤ state.lower[0]!
    · exact StateInvariant.insert_from_size_four_of_le_root
        hInvariant hInputSize value hRoute
    · exact StateInvariant.insert_from_size_four_of_gt_root
        hInvariant hInputSize value (by omega)

/-- 任意の3値を逐次挿入した `ofArray` 状態は、不変条件を保つ。

最初の2値について既存の一般契約で単一要素ヒープ形を特定し、今回証明した両方の
挿入分岐を使って、値の順序や重複に依存しない長さ3の状態不変条件を得る。
-/
theorem StateInvariant.ofArray_triple (first second third : Nat) :
    StateInvariant #[first, second, third]
      (LeanExperiments.RunningMedian.ofArray #[first, second, third]) := by
  have hInput : #[first, second, third] = (#[first, second]).push third := by simp
  rw [hInput, ofArray_push]
  have hPair := StateInvariant.ofArray_pair first second
  by_cases hOrder : first < second
  · have hState := ofArray_pair_eq_of_lt hOrder
    rw [hState] at hPair
    rw [hState]
    by_cases hRoute : third ≤ first
    · exact StateInvariant.insert_from_two_singletons_of_le hPair rfl hRoute
    · exact StateInvariant.insert_from_two_singletons_of_gt hPair rfl (by omega)
  · have hState := ofArray_pair_eq_of_ge (by omega : second ≤ first)
    rw [hState] at hPair
    rw [hState]
    by_cases hRoute : third ≤ second
    · exact StateInvariant.insert_from_two_singletons_of_le hPair rfl hRoute
    · exact StateInvariant.insert_from_two_singletons_of_gt hPair rfl (by omega)

/-- 任意の4値を逐次挿入した `ofArray` 状態も不変条件を保つ。 -/
theorem StateInvariant.ofArray_quadruple
    (first second third fourth : Nat) :
    StateInvariant #[first, second, third, fourth]
      (LeanExperiments.RunningMedian.ofArray #[first, second, third, fourth]) := by
  have hInput : #[first, second, third, fourth] =
      (#[first, second, third] : Array Nat).push fourth := by simp
  rw [hInput, ofArray_push]
  exact StateInvariant.insert_of_size_le_three
    (StateInvariant.ofArray_triple first second third) (by simp) fourth

/-- サイズ3の任意配列を逐次挿入した `ofArray` 状態は不変条件を満たす。 -/
theorem StateInvariant.ofArray_size_eq_three (values : Array Nat)
    (hSize : values.size = 3) :
    StateInvariant values (LeanExperiments.RunningMedian.ofArray values) := by
  let first := values[0]!
  let second := values[1]!
  let third := values[2]!
  have hValues : values = #[first, second, third] := by
    apply Array.ext
    · simpa using hSize
    · intro index hIndex hBound
      have hCases : index = 0 ∨ index = 1 ∨ index = 2 := by omega
      rcases hCases with h | h | h <;> subst index
      · simpa [first] using (getElem!_pos values 0 (by omega)).symm
      · simpa [second] using (getElem!_pos values 1 (by omega)).symm
      · simpa [third] using (getElem!_pos values 2 (by omega)).symm
  rw [hValues]
  exact StateInvariant.ofArray_triple first second third

/-- サイズ4の任意配列を逐次挿入した `ofArray` 状態は不変条件を満たす。 -/
theorem StateInvariant.ofArray_size_eq_four (values : Array Nat)
    (hSize : values.size = 4) :
    StateInvariant values (LeanExperiments.RunningMedian.ofArray values) := by
  let first := values[0]!
  let second := values[1]!
  let third := values[2]!
  let fourth := values[3]!
  have hValues : values = #[first, second, third, fourth] := by
    apply Array.ext
    · simpa using hSize
    · intro index hIndex hBound
      have hCases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 := by omega
      rcases hCases with h | h | h | h <;> subst index
      · simpa [first] using (getElem!_pos values 0 (by omega)).symm
      · simpa [second] using (getElem!_pos values 1 (by omega)).symm
      · simpa [third] using (getElem!_pos values 2 (by omega)).symm
      · simpa [fourth] using (getElem!_pos values 3 (by omega)).symm
  rw [hValues]
  exact StateInvariant.ofArray_quadruple first second third fourth

/-- サイズ5の配列を逐次挿入した `ofArray` 状態も一般不変条件を満たす。

先頭4値の不変状態に5番目を追加し、長さ4以下の任意不変状態への挿入保存を適用する。
-/
theorem StateInvariant.ofArray_size_eq_five (values : Array Nat)
    (hSize : values.size = 5) :
    StateInvariant values (LeanExperiments.RunningMedian.ofArray values) := by
  let first := values[0]!
  let second := values[1]!
  let third := values[2]!
  let fourth := values[3]!
  let fifth := values[4]!
  have hPrefix : StateInvariant #[first, second, third, fourth]
      (LeanExperiments.RunningMedian.ofArray #[first, second, third, fourth]) :=
    StateInvariant.ofArray_quadruple first second third fourth
  have hValues : values = (#[first, second, third, fourth] : Array Nat).push fifth := by
    apply Array.ext
    · simp [hSize]
    · intro index hIndex hBound
      have hCases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 := by omega
      rcases hCases with h | h | h | h | h <;> subst index
      · simpa [first] using (getElem!_pos values 0 (by omega)).symm
      · simpa [second] using (getElem!_pos values 1 (by omega)).symm
      · simpa [third] using (getElem!_pos values 2 (by omega)).symm
      · simpa [fourth] using (getElem!_pos values 3 (by omega)).symm
      · simpa [fifth] using (getElem!_pos values 4 (by omega)).symm
  rw [hValues, ofArray_push]
  exact StateInvariant.insert_of_size_le_four hPrefix (by simp) fifth

/-- サイズ6の配列を逐次挿入した `ofArray` 状態は不変条件を満たす。 -/
theorem StateInvariant.ofArray_size_eq_six (values : Array Nat)
    (hSize : values.size = 6) :
    StateInvariant values (LeanExperiments.RunningMedian.ofArray values) := by
  let first := values[0]!
  let second := values[1]!
  let third := values[2]!
  let fourth := values[3]!
  let fifth := values[4]!
  let sixth := values[5]!
  have hPrefix : StateInvariant #[first, second, third, fourth, fifth]
      (LeanExperiments.RunningMedian.ofArray #[first, second, third, fourth, fifth]) :=
    StateInvariant.ofArray_size_eq_five #[first, second, third, fourth, fifth] (by simp)
  have hValues : values = (#[first, second, third, fourth, fifth] : Array Nat).push sixth := by
    apply Array.ext
    · simp [hSize]
    · intro index hIndex hBound
      have hCases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨
          index = 4 ∨ index = 5 := by omega
      rcases hCases with h | h | h | h | h | h <;> subst index
      · simpa [first] using (getElem!_pos values 0 (by omega)).symm
      · simpa [second] using (getElem!_pos values 1 (by omega)).symm
      · simpa [third] using (getElem!_pos values 2 (by omega)).symm
      · simpa [fourth] using (getElem!_pos values 3 (by omega)).symm
      · simpa [fifth] using (getElem!_pos values 4 (by omega)).symm
      · simpa [sixth] using (getElem!_pos values 5 (by omega)).symm
  rw [hValues, ofArray_push]
  exact StateInvariant.insert_of_size_five hPrefix (by simp) sixth

/-- サイズ7の配列を逐次挿入した `ofArray` 状態は不変条件を満たす。 -/
theorem StateInvariant.ofArray_size_eq_seven (values : Array Nat)
    (hSize : values.size = 7) :
    StateInvariant values (LeanExperiments.RunningMedian.ofArray values) := by
  let first := values[0]!
  let second := values[1]!
  let third := values[2]!
  let fourth := values[3]!
  let fifth := values[4]!
  let sixth := values[5]!
  let seventh := values[6]!
  have hPrefix : StateInvariant #[first, second, third, fourth, fifth, sixth]
      (LeanExperiments.RunningMedian.ofArray #[first, second, third, fourth, fifth, sixth]) :=
    StateInvariant.ofArray_size_eq_six #[first, second, third, fourth, fifth, sixth] (by simp)
  have hValues : values = (#[first, second, third, fourth, fifth, sixth] : Array Nat).push seventh := by
    apply Array.ext
    · simp [hSize]
    · intro index hIndex hBound
      have hCases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨
          index = 4 ∨ index = 5 ∨ index = 6 := by omega
      rcases hCases with h | h | h | h | h | h | h <;> subst index
      · simpa [first] using (getElem!_pos values 0 (by omega)).symm
      · simpa [second] using (getElem!_pos values 1 (by omega)).symm
      · simpa [third] using (getElem!_pos values 2 (by omega)).symm
      · simpa [fourth] using (getElem!_pos values 3 (by omega)).symm
      · simpa [fifth] using (getElem!_pos values 4 (by omega)).symm
      · simpa [sixth] using (getElem!_pos values 5 (by omega)).symm
      · simpa [seventh] using (getElem!_pos values 6 (by omega)).symm
  rw [hValues, ofArray_push]
  exact StateInvariant.insert_of_size_six hPrefix (by simp) seventh

/-- サイズ8の配列を逐次挿入した `ofArray` 状態は不変条件を満たす。 -/
theorem StateInvariant.ofArray_size_eq_eight (values : Array Nat)
    (hSize : values.size = 8) :
    StateInvariant values (LeanExperiments.RunningMedian.ofArray values) := by
  let first := values[0]!
  let second := values[1]!
  let third := values[2]!
  let fourth := values[3]!
  let fifth := values[4]!
  let sixth := values[5]!
  let seventh := values[6]!
  let eighth := values[7]!
  have hPrefix : StateInvariant #[first, second, third, fourth, fifth, sixth, seventh]
      (LeanExperiments.RunningMedian.ofArray
        #[first, second, third, fourth, fifth, sixth, seventh]) :=
    StateInvariant.ofArray_size_eq_seven
      #[first, second, third, fourth, fifth, sixth, seventh] (by simp)
  have hValues : values =
      (#[first, second, third, fourth, fifth, sixth, seventh] : Array Nat).push eighth := by
    apply Array.ext
    · simp [hSize]
    · intro index hIndex hBound
      have hCases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨
          index = 4 ∨ index = 5 ∨ index = 6 ∨ index = 7 := by omega
      rcases hCases with h | h | h | h | h | h | h | h <;> subst index
      · simpa [first] using (getElem!_pos values 0 (by omega)).symm
      · simpa [second] using (getElem!_pos values 1 (by omega)).symm
      · simpa [third] using (getElem!_pos values 2 (by omega)).symm
      · simpa [fourth] using (getElem!_pos values 3 (by omega)).symm
      · simpa [fifth] using (getElem!_pos values 4 (by omega)).symm
      · simpa [sixth] using (getElem!_pos values 5 (by omega)).symm
      · simpa [seventh] using (getElem!_pos values 6 (by omega)).symm
      · simpa [eighth] using (getElem!_pos values 7 (by omega)).symm
  rw [hValues, ofArray_push]
  exact StateInvariant.insert_of_size_seven hPrefix (by simp) eighth

/-- サイズ9の配列を逐次挿入した `ofArray` 状態は不変条件を満たす。 -/
theorem StateInvariant.ofArray_size_eq_nine (values : Array Nat)
    (hSize : values.size = 9) :
    StateInvariant values (LeanExperiments.RunningMedian.ofArray values) := by
  let first := values[0]!
  let second := values[1]!
  let third := values[2]!
  let fourth := values[3]!
  let fifth := values[4]!
  let sixth := values[5]!
  let seventh := values[6]!
  let eighth := values[7]!
  let ninth := values[8]!
  have hPrefix : StateInvariant
      #[first, second, third, fourth, fifth, sixth, seventh, eighth]
      (LeanExperiments.RunningMedian.ofArray
        #[first, second, third, fourth, fifth, sixth, seventh, eighth]) :=
    StateInvariant.ofArray_size_eq_eight
      #[first, second, third, fourth, fifth, sixth, seventh, eighth] (by simp)
  have hValues : values =
      (#[first, second, third, fourth, fifth, sixth, seventh, eighth] : Array Nat).push ninth := by
    apply Array.ext
    · simp [hSize]
    · intro index hIndex hBound
      have hCases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 ∨
          index = 5 ∨ index = 6 ∨ index = 7 ∨ index = 8 := by omega
      rcases hCases with h | h | h | h | h | h | h | h | h <;> subst index
      · simpa [first] using (getElem!_pos values 0 (by omega)).symm
      · simpa [second] using (getElem!_pos values 1 (by omega)).symm
      · simpa [third] using (getElem!_pos values 2 (by omega)).symm
      · simpa [fourth] using (getElem!_pos values 3 (by omega)).symm
      · simpa [fifth] using (getElem!_pos values 4 (by omega)).symm
      · simpa [sixth] using (getElem!_pos values 5 (by omega)).symm
      · simpa [seventh] using (getElem!_pos values 6 (by omega)).symm
      · simpa [eighth] using (getElem!_pos values 7 (by omega)).symm
      · simpa [ninth] using (getElem!_pos values 8 (by omega)).symm
  rw [hValues, ofArray_push]
  exact StateInvariant.insert_of_size_eight hPrefix (by simp) ninth

/-- サイズ10の配列を逐次挿入した `ofArray` 状態は不変条件を満たす。 -/
theorem StateInvariant.ofArray_size_eq_ten (values : Array Nat)
    (hSize : values.size = 10) :
    StateInvariant values (LeanExperiments.RunningMedian.ofArray values) := by
  let first := values[0]!
  let second := values[1]!
  let third := values[2]!
  let fourth := values[3]!
  let fifth := values[4]!
  let sixth := values[5]!
  let seventh := values[6]!
  let eighth := values[7]!
  let ninth := values[8]!
  let tenth := values[9]!
  have hPrefix : StateInvariant
      #[first, second, third, fourth, fifth, sixth, seventh, eighth, ninth]
      (LeanExperiments.RunningMedian.ofArray
        #[first, second, third, fourth, fifth, sixth, seventh, eighth, ninth]) :=
    StateInvariant.ofArray_size_eq_nine
      #[first, second, third, fourth, fifth, sixth, seventh, eighth, ninth] (by simp)
  have hValues : values =
      (#[first, second, third, fourth, fifth, sixth, seventh, eighth, ninth] : Array Nat).push tenth := by
    apply Array.ext
    · simp [hSize]
    · intro index hIndex hBound
      have hCases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 ∨
          index = 5 ∨ index = 6 ∨ index = 7 ∨ index = 8 ∨ index = 9 := by omega
      rcases hCases with h | h | h | h | h | h | h | h | h | h <;> subst index
      · simpa [first] using (getElem!_pos values 0 (by omega)).symm
      · simpa [second] using (getElem!_pos values 1 (by omega)).symm
      · simpa [third] using (getElem!_pos values 2 (by omega)).symm
      · simpa [fourth] using (getElem!_pos values 3 (by omega)).symm
      · simpa [fifth] using (getElem!_pos values 4 (by omega)).symm
      · simpa [sixth] using (getElem!_pos values 5 (by omega)).symm
      · simpa [seventh] using (getElem!_pos values 6 (by omega)).symm
      · simpa [eighth] using (getElem!_pos values 7 (by omega)).symm
      · simpa [ninth] using (getElem!_pos values 8 (by omega)).symm
      · simpa [tenth] using (getElem!_pos values 9 (by omega)).symm
  rw [hValues, ofArray_push]
  exact StateInvariant.insert_of_size_nine hPrefix (by simp) tenth

/-- サイズ11の配列を逐次挿入した `ofArray` 状態は不変条件を満たす。 -/
theorem StateInvariant.ofArray_size_eq_eleven (values : Array Nat)
    (hSize : values.size = 11) :
    StateInvariant values (LeanExperiments.RunningMedian.ofArray values) := by
  let first := values[0]!
  let second := values[1]!
  let third := values[2]!
  let fourth := values[3]!
  let fifth := values[4]!
  let sixth := values[5]!
  let seventh := values[6]!
  let eighth := values[7]!
  let ninth := values[8]!
  let tenth := values[9]!
  let eleventh := values[10]!
  have hPrefix : StateInvariant
      #[first, second, third, fourth, fifth, sixth, seventh, eighth, ninth, tenth]
      (LeanExperiments.RunningMedian.ofArray
        #[first, second, third, fourth, fifth, sixth, seventh, eighth, ninth, tenth]) :=
    StateInvariant.ofArray_size_eq_ten
      #[first, second, third, fourth, fifth, sixth, seventh, eighth, ninth, tenth] (by simp)
  have hValues : values =
      (#[first, second, third, fourth, fifth, sixth, seventh, eighth, ninth, tenth] : Array Nat).push eleventh := by
    apply Array.ext
    · simp [hSize]
    · intro index hIndex hBound
      have hCases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 ∨
          index = 5 ∨ index = 6 ∨ index = 7 ∨ index = 8 ∨ index = 9 ∨ index = 10 := by omega
      rcases hCases with h | h | h | h | h | h | h | h | h | h | h <;> subst index
      · simpa [first] using (getElem!_pos values 0 (by omega)).symm
      · simpa [second] using (getElem!_pos values 1 (by omega)).symm
      · simpa [third] using (getElem!_pos values 2 (by omega)).symm
      · simpa [fourth] using (getElem!_pos values 3 (by omega)).symm
      · simpa [fifth] using (getElem!_pos values 4 (by omega)).symm
      · simpa [sixth] using (getElem!_pos values 5 (by omega)).symm
      · simpa [seventh] using (getElem!_pos values 6 (by omega)).symm
      · simpa [eighth] using (getElem!_pos values 7 (by omega)).symm
      · simpa [ninth] using (getElem!_pos values 8 (by omega)).symm
      · simpa [tenth] using (getElem!_pos values 9 (by omega)).symm
      · simpa [eleventh] using (getElem!_pos values 10 (by omega)).symm
  rw [hValues, ofArray_push]
  exact StateInvariant.insert_of_size_ten hPrefix (by simp) eleventh

/-- サイズ12の配列を逐次挿入した `ofArray` 状態は不変条件を満たす。 -/
theorem StateInvariant.ofArray_size_eq_twelve (values : Array Nat)
    (hSize : values.size = 12) :
    StateInvariant values (LeanExperiments.RunningMedian.ofArray values) := by
  let first := values[0]!
  let second := values[1]!
  let third := values[2]!
  let fourth := values[3]!
  let fifth := values[4]!
  let sixth := values[5]!
  let seventh := values[6]!
  let eighth := values[7]!
  let ninth := values[8]!
  let tenth := values[9]!
  let eleventh := values[10]!
  let twelfth := values[11]!
  have hPrefix : StateInvariant
      #[first, second, third, fourth, fifth, sixth, seventh, eighth, ninth, tenth, eleventh]
      (LeanExperiments.RunningMedian.ofArray
        #[first, second, third, fourth, fifth, sixth, seventh, eighth, ninth, tenth, eleventh]) :=
    StateInvariant.ofArray_size_eq_eleven
      #[first, second, third, fourth, fifth, sixth, seventh, eighth, ninth, tenth, eleventh] (by simp)
  have hValues : values =
      (#[first, second, third, fourth, fifth, sixth, seventh, eighth, ninth, tenth, eleventh] : Array Nat).push twelfth := by
    apply Array.ext
    · simp [hSize]
    · intro index hIndex hBound
      have hCases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 ∨
          index = 5 ∨ index = 6 ∨ index = 7 ∨ index = 8 ∨ index = 9 ∨ index = 10 ∨ index = 11 := by omega
      rcases hCases with h | h | h | h | h | h | h | h | h | h | h | h <;> subst index
      · simpa [first] using (getElem!_pos values 0 (by omega)).symm
      · simpa [second] using (getElem!_pos values 1 (by omega)).symm
      · simpa [third] using (getElem!_pos values 2 (by omega)).symm
      · simpa [fourth] using (getElem!_pos values 3 (by omega)).symm
      · simpa [fifth] using (getElem!_pos values 4 (by omega)).symm
      · simpa [sixth] using (getElem!_pos values 5 (by omega)).symm
      · simpa [seventh] using (getElem!_pos values 6 (by omega)).symm
      · simpa [eighth] using (getElem!_pos values 7 (by omega)).symm
      · simpa [ninth] using (getElem!_pos values 8 (by omega)).symm
      · simpa [tenth] using (getElem!_pos values 9 (by omega)).symm
      · simpa [eleventh] using (getElem!_pos values 10 (by omega)).symm
      · simpa [twelfth] using (getElem!_pos values 11 (by omega)).symm
  rw [hValues, ofArray_push]
  exact StateInvariant.insert_of_size_eleven hPrefix (by simp) twelfth

/-- サイズ13の配列を逐次挿入した `ofArray` 状態は不変条件を満たす。 -/
theorem StateInvariant.ofArray_size_eq_thirteen (values : Array Nat)
    (hSize : values.size = 13) :
    StateInvariant values (LeanExperiments.RunningMedian.ofArray values) := by
  let first := values[0]!
  let second := values[1]!
  let third := values[2]!
  let fourth := values[3]!
  let fifth := values[4]!
  let sixth := values[5]!
  let seventh := values[6]!
  let eighth := values[7]!
  let ninth := values[8]!
  let tenth := values[9]!
  let eleventh := values[10]!
  let twelfth := values[11]!
  let thirteenth := values[12]!
  have hPrefix : StateInvariant
      #[first, second, third, fourth, fifth, sixth, seventh, eighth, ninth, tenth, eleventh, twelfth]
      (LeanExperiments.RunningMedian.ofArray
        #[first, second, third, fourth, fifth, sixth, seventh, eighth, ninth, tenth, eleventh, twelfth]) :=
    StateInvariant.ofArray_size_eq_twelve
      #[first, second, third, fourth, fifth, sixth, seventh, eighth, ninth, tenth, eleventh, twelfth] (by simp)
  have hValues : values =
      (#[first, second, third, fourth, fifth, sixth, seventh, eighth, ninth, tenth, eleventh, twelfth] : Array Nat).push thirteenth := by
    apply Array.ext
    · simp [hSize]
    · intro index hIndex hBound
      have hCases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 ∨
          index = 5 ∨ index = 6 ∨ index = 7 ∨ index = 8 ∨ index = 9 ∨ index = 10 ∨
          index = 11 ∨ index = 12 := by omega
      rcases hCases with h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst index
      · simpa [first] using (getElem!_pos values 0 (by omega)).symm
      · simpa [second] using (getElem!_pos values 1 (by omega)).symm
      · simpa [third] using (getElem!_pos values 2 (by omega)).symm
      · simpa [fourth] using (getElem!_pos values 3 (by omega)).symm
      · simpa [fifth] using (getElem!_pos values 4 (by omega)).symm
      · simpa [sixth] using (getElem!_pos values 5 (by omega)).symm
      · simpa [seventh] using (getElem!_pos values 6 (by omega)).symm
      · simpa [eighth] using (getElem!_pos values 7 (by omega)).symm
      · simpa [ninth] using (getElem!_pos values 8 (by omega)).symm
      · simpa [tenth] using (getElem!_pos values 9 (by omega)).symm
      · simpa [eleventh] using (getElem!_pos values 10 (by omega)).symm
      · simpa [twelfth] using (getElem!_pos values 11 (by omega)).symm
      · simpa [thirteenth] using (getElem!_pos values 12 (by omega)).symm
  rw [hValues, ofArray_push]
  exact StateInvariant.insert_of_size_twelve hPrefix (by simp) thirteenth

/-- サイズ14の配列を逐次挿入した `ofArray` 状態は不変条件を満たす。 -/
theorem StateInvariant.ofArray_size_eq_fourteen (values : Array Nat)
    (hSize : values.size = 14) :
    StateInvariant values (LeanExperiments.RunningMedian.ofArray values) := by
  let first := values[0]!
  let second := values[1]!
  let third := values[2]!
  let fourth := values[3]!
  let fifth := values[4]!
  let sixth := values[5]!
  let seventh := values[6]!
  let eighth := values[7]!
  let ninth := values[8]!
  let tenth := values[9]!
  let eleventh := values[10]!
  let twelfth := values[11]!
  let thirteenth := values[12]!
  let fourteenth := values[13]!
  have hPrefix : StateInvariant
      #[first, second, third, fourth, fifth, sixth, seventh, eighth, ninth, tenth, eleventh, twelfth, thirteenth]
      (LeanExperiments.RunningMedian.ofArray
        #[first, second, third, fourth, fifth, sixth, seventh, eighth, ninth, tenth, eleventh, twelfth, thirteenth]) :=
    StateInvariant.ofArray_size_eq_thirteen
      #[first, second, third, fourth, fifth, sixth, seventh, eighth, ninth, tenth, eleventh, twelfth, thirteenth] (by simp)
  have hValues : values =
      (#[first, second, third, fourth, fifth, sixth, seventh, eighth, ninth, tenth, eleventh, twelfth, thirteenth] : Array Nat).push fourteenth := by
    apply Array.ext
    · simp [hSize]
    · intro index hIndex hBound
      have hCases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 ∨
          index = 5 ∨ index = 6 ∨ index = 7 ∨ index = 8 ∨ index = 9 ∨ index = 10 ∨
          index = 11 ∨ index = 12 ∨ index = 13 := by omega
      rcases hCases with h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst index
      · simpa [first] using (getElem!_pos values 0 (by omega)).symm
      · simpa [second] using (getElem!_pos values 1 (by omega)).symm
      · simpa [third] using (getElem!_pos values 2 (by omega)).symm
      · simpa [fourth] using (getElem!_pos values 3 (by omega)).symm
      · simpa [fifth] using (getElem!_pos values 4 (by omega)).symm
      · simpa [sixth] using (getElem!_pos values 5 (by omega)).symm
      · simpa [seventh] using (getElem!_pos values 6 (by omega)).symm
      · simpa [eighth] using (getElem!_pos values 7 (by omega)).symm
      · simpa [ninth] using (getElem!_pos values 8 (by omega)).symm
      · simpa [tenth] using (getElem!_pos values 9 (by omega)).symm
      · simpa [eleventh] using (getElem!_pos values 10 (by omega)).symm
      · simpa [twelfth] using (getElem!_pos values 11 (by omega)).symm
      · simpa [thirteenth] using (getElem!_pos values 12 (by omega)).symm
      · simpa [fourteenth] using (getElem!_pos values 13 (by omega)).symm
  rw [hValues, ofArray_push]
  exact StateInvariant.insert_of_size_thirteen hPrefix (by simp) fourteenth

/-- サイズ15の配列を逐次挿入した `ofArray` 状態は不変条件を満たす。 -/
theorem StateInvariant.ofArray_size_eq_fifteen (values : Array Nat)
    (hSize : values.size = 15) :
    StateInvariant values (LeanExperiments.RunningMedian.ofArray values) := by
  let first := values[0]!
  let second := values[1]!
  let third := values[2]!
  let fourth := values[3]!
  let fifth := values[4]!
  let sixth := values[5]!
  let seventh := values[6]!
  let eighth := values[7]!
  let ninth := values[8]!
  let tenth := values[9]!
  let eleventh := values[10]!
  let twelfth := values[11]!
  let thirteenth := values[12]!
  let fourteenth := values[13]!
  let fifteenth := values[14]!
  have hPrefix : StateInvariant
      #[first, second, third, fourth, fifth, sixth, seventh, eighth, ninth, tenth,
        eleventh, twelfth, thirteenth, fourteenth]
      (LeanExperiments.RunningMedian.ofArray
        #[first, second, third, fourth, fifth, sixth, seventh, eighth, ninth, tenth,
          eleventh, twelfth, thirteenth, fourteenth]) :=
    StateInvariant.ofArray_size_eq_fourteen
      #[first, second, third, fourth, fifth, sixth, seventh, eighth, ninth, tenth,
        eleventh, twelfth, thirteenth, fourteenth] (by simp)
  have hValues : values =
      (#[first, second, third, fourth, fifth, sixth, seventh, eighth, ninth, tenth,
        eleventh, twelfth, thirteenth, fourteenth] : Array Nat).push fifteenth := by
    apply Array.ext
    · simp [hSize]
    · intro index hIndex hBound
      have hCases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 ∨
          index = 5 ∨ index = 6 ∨ index = 7 ∨ index = 8 ∨ index = 9 ∨ index = 10 ∨
          index = 11 ∨ index = 12 ∨ index = 13 ∨ index = 14 := by omega
      rcases hCases with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
        subst index
      · simpa [first] using (getElem!_pos values 0 (by omega)).symm
      · simpa [second] using (getElem!_pos values 1 (by omega)).symm
      · simpa [third] using (getElem!_pos values 2 (by omega)).symm
      · simpa [fourth] using (getElem!_pos values 3 (by omega)).symm
      · simpa [fifth] using (getElem!_pos values 4 (by omega)).symm
      · simpa [sixth] using (getElem!_pos values 5 (by omega)).symm
      · simpa [seventh] using (getElem!_pos values 6 (by omega)).symm
      · simpa [eighth] using (getElem!_pos values 7 (by omega)).symm
      · simpa [ninth] using (getElem!_pos values 8 (by omega)).symm
      · simpa [tenth] using (getElem!_pos values 9 (by omega)).symm
      · simpa [eleventh] using (getElem!_pos values 10 (by omega)).symm
      · simpa [twelfth] using (getElem!_pos values 11 (by omega)).symm
      · simpa [thirteenth] using (getElem!_pos values 12 (by omega)).symm
      · simpa [fourteenth] using (getElem!_pos values 13 (by omega)).symm
      · simpa [fifteenth] using (getElem!_pos values 14 (by omega)).symm
  rw [hValues, ofArray_push]
  exact StateInvariant.insert_of_size_fourteen hPrefix (by simp) fifteenth

/-- サイズ16の配列を逐次挿入した `ofArray` 状態は不変条件を満たす。 -/
theorem StateInvariant.ofArray_size_eq_sixteen (values : Array Nat)
    (hSize : values.size = 16) :
    StateInvariant values (LeanExperiments.RunningMedian.ofArray values) := by
  let first := values[0]!
  let second := values[1]!
  let third := values[2]!
  let fourth := values[3]!
  let fifth := values[4]!
  let sixth := values[5]!
  let seventh := values[6]!
  let eighth := values[7]!
  let ninth := values[8]!
  let tenth := values[9]!
  let eleventh := values[10]!
  let twelfth := values[11]!
  let thirteenth := values[12]!
  let fourteenth := values[13]!
  let fifteenth := values[14]!
  let sixteenth := values[15]!
  have hPrefix : StateInvariant
      #[first, second, third, fourth, fifth, sixth, seventh, eighth, ninth, tenth,
        eleventh, twelfth, thirteenth, fourteenth, fifteenth]
      (LeanExperiments.RunningMedian.ofArray
        #[first, second, third, fourth, fifth, sixth, seventh, eighth, ninth, tenth,
          eleventh, twelfth, thirteenth, fourteenth, fifteenth]) :=
    StateInvariant.ofArray_size_eq_fifteen
      #[first, second, third, fourth, fifth, sixth, seventh, eighth, ninth, tenth,
        eleventh, twelfth, thirteenth, fourteenth, fifteenth] (by simp)
  have hValues : values =
      (#[first, second, third, fourth, fifth, sixth, seventh, eighth, ninth, tenth,
        eleventh, twelfth, thirteenth, fourteenth, fifteenth] : Array Nat).push sixteenth := by
    apply Array.ext
    · simp [hSize]
    · intro index hIndex hBound
      have hCases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 ∨ index = 5 ∨ index = 6 ∨ index = 7 ∨ index = 8 ∨ index = 9 ∨ index = 10 ∨ index = 11 ∨ index = 12 ∨ index = 13 ∨ index = 14 ∨ index = 15 := by omega
      rcases hCases with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst index
      · simpa [first] using (getElem!_pos values 0 (by omega)).symm
      · simpa [second] using (getElem!_pos values 1 (by omega)).symm
      · simpa [third] using (getElem!_pos values 2 (by omega)).symm
      · simpa [fourth] using (getElem!_pos values 3 (by omega)).symm
      · simpa [fifth] using (getElem!_pos values 4 (by omega)).symm
      · simpa [sixth] using (getElem!_pos values 5 (by omega)).symm
      · simpa [seventh] using (getElem!_pos values 6 (by omega)).symm
      · simpa [eighth] using (getElem!_pos values 7 (by omega)).symm
      · simpa [ninth] using (getElem!_pos values 8 (by omega)).symm
      · simpa [tenth] using (getElem!_pos values 9 (by omega)).symm
      · simpa [eleventh] using (getElem!_pos values 10 (by omega)).symm
      · simpa [twelfth] using (getElem!_pos values 11 (by omega)).symm
      · simpa [thirteenth] using (getElem!_pos values 12 (by omega)).symm
      · simpa [fourteenth] using (getElem!_pos values 13 (by omega)).symm
      · simpa [fifteenth] using (getElem!_pos values 14 (by omega)).symm
      · simpa [sixteenth] using (getElem!_pos values 15 (by omega)).symm
  rw [hValues, ofArray_push]
  exact StateInvariant.insert_of_size_fifteen hPrefix (by simp) sixteenth

/-- サイズ17の配列を逐次挿入した `ofArray` 状態は不変条件を満たす。 -/
theorem StateInvariant.ofArray_size_eq_seventeen (values : Array Nat)
    (hSize : values.size = 17) :
    StateInvariant values (LeanExperiments.RunningMedian.ofArray values) := by
  let first := values[0]!
  let second := values[1]!
  let third := values[2]!
  let fourth := values[3]!
  let fifth := values[4]!
  let sixth := values[5]!
  let seventh := values[6]!
  let eighth := values[7]!
  let ninth := values[8]!
  let tenth := values[9]!
  let eleventh := values[10]!
  let twelfth := values[11]!
  let thirteenth := values[12]!
  let fourteenth := values[13]!
  let fifteenth := values[14]!
  let sixteenth := values[15]!
  let seventeenth := values[16]!
  have hPrefix : StateInvariant
      #[first, second, third, fourth, fifth, sixth, seventh, eighth, ninth, tenth,
        eleventh, twelfth, thirteenth, fourteenth, fifteenth, sixteenth]
      (LeanExperiments.RunningMedian.ofArray
        #[first, second, third, fourth, fifth, sixth, seventh, eighth, ninth, tenth,
          eleventh, twelfth, thirteenth, fourteenth, fifteenth, sixteenth]) :=
    StateInvariant.ofArray_size_eq_sixteen
      #[first, second, third, fourth, fifth, sixth, seventh, eighth, ninth, tenth,
        eleventh, twelfth, thirteenth, fourteenth, fifteenth, sixteenth] (by simp)
  have hValues : values =
      (#[first, second, third, fourth, fifth, sixth, seventh, eighth, ninth, tenth,
        eleventh, twelfth, thirteenth, fourteenth, fifteenth, sixteenth] : Array Nat).push seventeenth := by
    apply Array.ext
    · simp [hSize]
    · intro index hIndex hBound
      have hCases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 ∨ index = 5 ∨ index = 6 ∨ index = 7 ∨ index = 8 ∨ index = 9 ∨ index = 10 ∨ index = 11 ∨ index = 12 ∨ index = 13 ∨ index = 14 ∨ index = 15 ∨ index = 16 := by omega
      rcases hCases with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst index
      · simpa [first] using (getElem!_pos values 0 (by omega)).symm
      · simpa [second] using (getElem!_pos values 1 (by omega)).symm
      · simpa [third] using (getElem!_pos values 2 (by omega)).symm
      · simpa [fourth] using (getElem!_pos values 3 (by omega)).symm
      · simpa [fifth] using (getElem!_pos values 4 (by omega)).symm
      · simpa [sixth] using (getElem!_pos values 5 (by omega)).symm
      · simpa [seventh] using (getElem!_pos values 6 (by omega)).symm
      · simpa [eighth] using (getElem!_pos values 7 (by omega)).symm
      · simpa [ninth] using (getElem!_pos values 8 (by omega)).symm
      · simpa [tenth] using (getElem!_pos values 9 (by omega)).symm
      · simpa [eleventh] using (getElem!_pos values 10 (by omega)).symm
      · simpa [twelfth] using (getElem!_pos values 11 (by omega)).symm
      · simpa [thirteenth] using (getElem!_pos values 12 (by omega)).symm
      · simpa [fourteenth] using (getElem!_pos values 13 (by omega)).symm
      · simpa [fifteenth] using (getElem!_pos values 14 (by omega)).symm
      · simpa [sixteenth] using (getElem!_pos values 15 (by omega)).symm
      · simpa [seventeenth] using (getElem!_pos values 16 (by omega)).symm
  rw [hValues, ofArray_push]
  exact StateInvariant.insert_of_size_sixteen hPrefix (by simp) seventeenth

/-- サイズ4以下の任意配列について、`ofArray` の状態不変条件を満たす。 -/
theorem StateInvariant.ofArray_size_le_four (values : Array Nat)
    (hSize : values.size ≤ 4) :
    StateInvariant values (LeanExperiments.RunningMedian.ofArray values) := by
  by_cases hSmall : values.size ≤ 2
  · exact StateInvariant.ofArray_size_le_two values hSmall
  · by_cases hThree : values.size = 3
    · exact StateInvariant.ofArray_size_eq_three values hThree
    · have hFour : values.size = 4 := by omega
      exact StateInvariant.ofArray_size_eq_four values hFour

/-- サイズ5以下の任意配列について、`ofArray` の状態不変条件を満たす。 -/
theorem StateInvariant.ofArray_size_le_five (values : Array Nat)
    (hSize : values.size ≤ 5) :
    StateInvariant values (LeanExperiments.RunningMedian.ofArray values) := by
  by_cases hSmall : values.size ≤ 4
  · exact StateInvariant.ofArray_size_le_four values hSmall
  · have hFive : values.size = 5 := by omega
    exact StateInvariant.ofArray_size_eq_five values hFive

/-- サイズ6以下の任意配列について、`ofArray` の状態不変条件を満たす。 -/
theorem StateInvariant.ofArray_size_le_six (values : Array Nat)
    (hSize : values.size ≤ 6) :
    StateInvariant values (LeanExperiments.RunningMedian.ofArray values) := by
  by_cases hSmall : values.size ≤ 5
  · exact StateInvariant.ofArray_size_le_five values hSmall
  · have hSix : values.size = 6 := by omega
    exact StateInvariant.ofArray_size_eq_six values hSix

/-- サイズ7以下の任意配列について、`ofArray` の状態不変条件を満たす。 -/
theorem StateInvariant.ofArray_size_le_seven (values : Array Nat)
    (hSize : values.size ≤ 7) :
    StateInvariant values (LeanExperiments.RunningMedian.ofArray values) := by
  by_cases hSmall : values.size ≤ 6
  · exact StateInvariant.ofArray_size_le_six values hSmall
  · have hSeven : values.size = 7 := by omega
    exact StateInvariant.ofArray_size_eq_seven values hSeven

/-- サイズ8以下の任意配列について、`ofArray` の状態不変条件を満たす。 -/
theorem StateInvariant.ofArray_size_le_eight (values : Array Nat)
    (hSize : values.size ≤ 8) :
    StateInvariant values (LeanExperiments.RunningMedian.ofArray values) := by
  by_cases hSmall : values.size ≤ 7
  · exact StateInvariant.ofArray_size_le_seven values hSmall
  · have hEight : values.size = 8 := by omega
    exact StateInvariant.ofArray_size_eq_eight values hEight

/-- サイズ9以下の任意配列について、`ofArray` の状態不変条件を満たす。 -/
theorem StateInvariant.ofArray_size_le_nine (values : Array Nat)
    (hSize : values.size ≤ 9) :
    StateInvariant values (LeanExperiments.RunningMedian.ofArray values) := by
  by_cases hSmall : values.size ≤ 8
  · exact StateInvariant.ofArray_size_le_eight values hSmall
  · have hNine : values.size = 9 := by omega
    exact StateInvariant.ofArray_size_eq_nine values hNine

/-- サイズ10以下の任意配列について、`ofArray` の状態不変条件を満たす。 -/
theorem StateInvariant.ofArray_size_le_ten (values : Array Nat)
    (hSize : values.size ≤ 10) :
    StateInvariant values (LeanExperiments.RunningMedian.ofArray values) := by
  by_cases hSmall : values.size ≤ 9
  · exact StateInvariant.ofArray_size_le_nine values hSmall
  · have hTen : values.size = 10 := by omega
    exact StateInvariant.ofArray_size_eq_ten values hTen

/-- サイズ11以下の任意配列について、`ofArray` の状態不変条件を満たす。 -/
theorem StateInvariant.ofArray_size_le_eleven (values : Array Nat)
    (hSize : values.size ≤ 11) :
    StateInvariant values (LeanExperiments.RunningMedian.ofArray values) := by
  by_cases hSmall : values.size ≤ 10
  · exact StateInvariant.ofArray_size_le_ten values hSmall
  · have hEleven : values.size = 11 := by omega
    exact StateInvariant.ofArray_size_eq_eleven values hEleven

/-- サイズ12以下の任意配列について、`ofArray` の状態不変条件を満たす。 -/
theorem StateInvariant.ofArray_size_le_twelve (values : Array Nat)
    (hSize : values.size ≤ 12) :
    StateInvariant values (LeanExperiments.RunningMedian.ofArray values) := by
  by_cases hSmall : values.size ≤ 11
  · exact StateInvariant.ofArray_size_le_eleven values hSmall
  · have hTwelve : values.size = 12 := by omega
    exact StateInvariant.ofArray_size_eq_twelve values hTwelve

/-- サイズ13以下の任意配列について、`ofArray` の状態不変条件を満たす。 -/
theorem StateInvariant.ofArray_size_le_thirteen (values : Array Nat)
    (hSize : values.size ≤ 13) :
    StateInvariant values (LeanExperiments.RunningMedian.ofArray values) := by
  by_cases hSmall : values.size ≤ 12
  · exact StateInvariant.ofArray_size_le_twelve values hSmall
  · have hThirteen : values.size = 13 := by omega
    exact StateInvariant.ofArray_size_eq_thirteen values hThirteen

/-- サイズ14以下の任意配列について、`ofArray` の状態不変条件を満たす。 -/
theorem StateInvariant.ofArray_size_le_fourteen (values : Array Nat)
    (hSize : values.size ≤ 14) :
    StateInvariant values (LeanExperiments.RunningMedian.ofArray values) := by
  by_cases hSmall : values.size ≤ 13
  · exact StateInvariant.ofArray_size_le_thirteen values hSmall
  · have hFourteen : values.size = 14 := by omega
    exact StateInvariant.ofArray_size_eq_fourteen values hFourteen

/-- サイズ15以下の任意配列について、`ofArray` の状態不変条件を満たす。 -/
theorem StateInvariant.ofArray_size_le_fifteen (values : Array Nat)
    (hSize : values.size ≤ 15) :
    StateInvariant values (LeanExperiments.RunningMedian.ofArray values) := by
  by_cases hSmall : values.size ≤ 14
  · exact StateInvariant.ofArray_size_le_fourteen values hSmall
  · have hFifteen : values.size = 15 := by omega
    exact StateInvariant.ofArray_size_eq_fifteen values hFifteen

/-- サイズ16以下の任意配列について、`ofArray` の状態不変条件を満たす。 -/
theorem StateInvariant.ofArray_size_le_sixteen (values : Array Nat)
    (hSize : values.size ≤ 16) :
    StateInvariant values (LeanExperiments.RunningMedian.ofArray values) := by
  by_cases hSmall : values.size ≤ 15
  · exact StateInvariant.ofArray_size_le_fifteen values hSmall
  · have hSixteen : values.size = 16 := by omega
    exact StateInvariant.ofArray_size_eq_sixteen values hSixteen

/-- サイズ17以下の任意配列について、`ofArray` の状態不変条件を満たす。 -/
theorem StateInvariant.ofArray_size_le_seventeen (values : Array Nat)
    (hSize : values.size ≤ 17) :
    StateInvariant values (LeanExperiments.RunningMedian.ofArray values) := by
  by_cases hSmall : values.size ≤ 16
  · exact StateInvariant.ofArray_size_le_sixteen values hSmall
  · have hSeventeen : values.size = 17 := by omega
    exact StateInvariant.ofArray_size_eq_seventeen values hSeventeen

/-- 両ヒープが非空なら、下側の最大値は上側の最小値以下である。 -/
theorem lower_root_le_upper_root {input : Array Nat}
    {state : LeanExperiments.RunningMedian.State}
    (hInvariant : StateInvariant input state)
    (hLower : 0 < state.lower.size) (hUpper : 0 < state.upper.size) :
    state.lower[0]'(by omega) ≤ state.upper[0]'hUpper :=
  hInvariant.2.2.2.1 0 (by omega) 0 hUpper

/-- 最大ヒープの順序条件により、下側の各値は根以下である。 -/
theorem lower_value_le_root {input : Array Nat}
    {state : LeanExperiments.RunningMedian.State}
    (hInvariant : StateInvariant input state) {index : Nat}
    (hIndex : index < state.lower.size) :
    state.lower[index]! ≤ state.lower[0]! :=
  maxHeap_root_is_maximum state.lower hInvariant.2.1 index hIndex

/-- 最小ヒープの順序条件により、上側の根は各値以下である。 -/
theorem upper_root_le_value {input : Array Nat}
    {state : LeanExperiments.RunningMedian.State}
    (hInvariant : StateInvariant input state) {index : Nat}
    (hIndex : index < state.upper.size) :
    state.upper[0]! ≤ state.upper[index]! :=
  minHeap_root_is_minimum state.upper hInvariant.2.2.1 index hIndex

private theorem sortedLower_last_eq_root {input : Array Nat}
    {state : LeanExperiments.RunningMedian.State}
    (hInvariant : StateInvariant input state) (hLower : 0 < state.lower.size) :
    let sorted := LeanExperiments.MergeSort.mergeSort state.lower.toList
    sorted[sorted.length - 1]! = state.lower[0]! := by
  dsimp
  let sorted := LeanExperiments.MergeSort.mergeSort state.lower.toList
  have hCorrect := LeanExperiments.Verification.MergeSort.mergeSort_correct state.lower.toList
  have hPairwise := LeanExperiments.Verification.Sorting.Spec.ascending_pairwise sorted hCorrect.1
  have hSortedLength : sorted.length = state.lower.size := by
    simpa [sorted] using hCorrect.2.length_eq
  have hLength : 0 < sorted.length := by
    omega
  have hLastIndex : sorted.length - 1 < sorted.length := by omega
  have hAllLe : ∀ value, value ∈ sorted → value ≤ state.lower[0]'(by omega) := by
    intro value hValue
    have hValueList : value ∈ state.lower.toList := hCorrect.2.mem_iff.mp hValue
    have hValueArray : value ∈ state.lower := by simpa using hValueList
    obtain ⟨index, hIndex, hAt⟩ := Array.mem_iff_getElem.mp hValueArray
    have hRootLe := lower_value_le_root hInvariant hIndex
    have hRootLe' : state.lower[index] ≤ state.lower[0] := by
      simpa only [← getElem!_pos] using hRootLe
    simpa [hAt] using hRootLe'
  have hLastLeRoot := hAllLe _ (List.getElem_mem hLastIndex)
  have hRootMemArray : state.lower[0]'(by omega) ∈ state.lower.toList :=
    Array.getElem_mem_toList (by omega)
  have hRootMem : state.lower[0]'(by omega) ∈ sorted := hCorrect.2.mem_iff.mpr hRootMemArray
  obtain ⟨rootIndex, hRootIndex, hRootAt⟩ := List.mem_iff_getElem.mp hRootMem
  have hRootIndexLe : rootIndex ≤ sorted.length - 1 := by omega
  have hRootLeLast : state.lower[0]'(by omega) ≤ sorted[sorted.length - 1] := by
    by_cases hEq : rootIndex = sorted.length - 1
    · have hAtLast : sorted[sorted.length - 1] = state.lower[0] := by
        simpa only [hEq] using hRootAt
      exact Nat.le_of_eq hAtLast.symm
    · have hLt : rootIndex < sorted.length - 1 := by omega
      have hPair := hPairwise.rel_getElem_of_lt hRootIndex hLastIndex hLt
      exact Nat.le_trans (Nat.le_of_eq hRootAt.symm) hPair
  have hLastLeRoot' : sorted[sorted.length - 1] ≤ state.lower[0]'(by omega) := by
    simpa only [← getElem!_pos] using hLastLeRoot
  have hResult := Nat.le_antisymm hLastLeRoot' hRootLeLast
  change sorted[sorted.length - 1]! = state.lower[0]!
  rw [getElem!_pos sorted (sorted.length - 1) hLastIndex,
    getElem!_pos state.lower 0 hLower]
  exact hResult

private theorem sortedUpper_first_eq_root {input : Array Nat}
    {state : LeanExperiments.RunningMedian.State}
    (hInvariant : StateInvariant input state) (hUpper : 0 < state.upper.size) :
    let sorted := LeanExperiments.MergeSort.mergeSort state.upper.toList
    sorted[0]! = state.upper[0]! := by
  dsimp
  let sorted := LeanExperiments.MergeSort.mergeSort state.upper.toList
  have hCorrect := LeanExperiments.Verification.MergeSort.mergeSort_correct state.upper.toList
  have hPairwise := LeanExperiments.Verification.Sorting.Spec.ascending_pairwise sorted hCorrect.1
  have hSortedLength : sorted.length = state.upper.size := by
    simpa [sorted] using hCorrect.2.length_eq
  have hLength : 0 < sorted.length := by
    omega
  have hFirstIndex : 0 < sorted.length := hLength
  have hAllGe : ∀ value, value ∈ sorted → state.upper[0]'(by omega) ≤ value := by
    intro value hValue
    have hValueList : value ∈ state.upper.toList := hCorrect.2.mem_iff.mp hValue
    have hValueArray : value ∈ state.upper := by simpa using hValueList
    obtain ⟨index, hIndex, hAt⟩ := Array.mem_iff_getElem.mp hValueArray
    have hRootLe := upper_root_le_value hInvariant hIndex
    have hRootLe' : state.upper[0] ≤ state.upper[index] := by
      simpa only [← getElem!_pos] using hRootLe
    simpa [hAt] using hRootLe'
  have hFirstLeRoot : sorted[0] ≤ state.upper[0]'(by omega) := by
    have hRootMemArray : state.upper[0]'(by omega) ∈ state.upper.toList :=
      Array.getElem_mem_toList (by omega)
    have hRootMem : state.upper[0]'(by omega) ∈ sorted := hCorrect.2.mem_iff.mpr hRootMemArray
    obtain ⟨rootIndex, hRootIndex, hRootAt⟩ := List.mem_iff_getElem.mp hRootMem
    by_cases hEq : rootIndex = 0
    · have hAtFirst : sorted[0] = state.upper[0] := by
        simpa only [hEq] using hRootAt
      exact Nat.le_of_eq hAtFirst
    · have hLt : 0 < rootIndex := by omega
      have hPair := hPairwise.rel_getElem_of_lt hFirstIndex hRootIndex hLt
      exact Nat.le_trans hPair (Nat.le_of_eq hRootAt)
  have hFirstGeRoot := hAllGe _ (List.getElem_mem hFirstIndex)
  have hFirstGeRoot' : state.upper[0]'(by omega) ≤ sorted[0] := by
    simpa only [← getElem!_pos] using hFirstGeRoot
  have hResult := (Nat.le_antisymm hFirstGeRoot' hFirstLeRoot).symm
  change sorted[0]! = state.upper[0]!
  rw [getElem!_pos sorted 0 hFirstIndex,
    getElem!_pos state.upper 0 hUpper]
  exact hResult

/-- 状態が論理的不変条件を満たせば、その中央値はソート基準の中央値と一致する。 -/
theorem median_eq_medianSpec_of_invariant {input : Array Nat}
    {state : LeanExperiments.RunningMedian.State}
    (hInvariant : StateInvariant input state) :
    LeanExperiments.RunningMedian.median state = medianSpec input := by
  let lowerSorted := LeanExperiments.MergeSort.mergeSort state.lower.toList
  let upperSorted := LeanExperiments.MergeSort.mergeSort state.upper.toList
  have hSortedArrayEq : (lowerSorted ++ upperSorted).toArray =
      (LeanExperiments.MergeSort.mergeSort input.toList).toArray :=
    StateInvariant.sorted_parts_toArray_eq_mergeSort hInvariant
  have hLowerLength : lowerSorted.length = state.lower.size := by
    simpa [lowerSorted] using
      (LeanExperiments.Verification.MergeSort.mergeSort_correct state.lower.toList).2.length_eq
  have hUpperLength : upperSorted.length = state.upper.size := by
    simpa [upperSorted] using
      (LeanExperiments.Verification.MergeSort.mergeSort_correct state.upper.toList).2.length_eq
  have hTotal : state.lower.size + state.upper.size = input.size := by
    simpa using hInvariant.1.length_eq
  by_cases hInput : 0 < input.size
  · rcases hInvariant.2.2.2.2 with hEven | hOdd
    · cases hUpperSize : state.upper.size with
      | zero => omega
      | succ k =>
        have hUpper : 0 < state.upper.size := by omega
        have hLowerSize : state.lower.size = k + 1 := by omega
        have hLowMedian :
            (lowerSorted ++ upperSorted)[k]?.getD 0 = state.lower[0]! := by
          rw [List.getElem?_append_left (by rw [hLowerLength, hLowerSize]; omega)]
          rw [List.getElem?_eq_getElem (by rw [hLowerLength, hLowerSize]; omega)]
          simp only [Option.getD_some]
          simpa [lowerSorted, hLowerLength, hLowerSize] using
            sortedLower_last_eq_root hInvariant (by omega)
        have hUpperRoot : upperSorted[0] = state.upper[0] := by
          simpa [upperSorted, hUpperLength, hUpperSize] using
            sortedUpper_first_eq_root hInvariant hUpper
        have hMiddle : (k + 1 + k) / 2 = k := by omega
        have hParity : (k + 1 + k) % 2 = 1 := by omega
        rw [median_of_even_size state hEven hUpper]
        unfold medianSpec
        rw [← hSortedArrayEq]
        simp [List.size_toArray, hLowerLength, hUpperLength, hLowerSize,
          hUpperSize, hMiddle, hParity, hLowMedian] <;>
          exact hUpperRoot.symm
    · cases hUpperSize : state.upper.size with
      | zero =>
        have hLowerSize : state.lower.size = 1 := by omega
        have hLowMedian :
            (lowerSorted ++ upperSorted)[0]?.getD 0 = state.lower[0]! := by
          rw [List.getElem?_append_left (by rw [hLowerLength, hLowerSize]; omega)]
          rw [List.getElem?_eq_getElem (by rw [hLowerLength, hLowerSize]; omega)]
          simp only [Option.getD_some]
          simpa [lowerSorted, hLowerLength, hLowerSize] using
            sortedLower_last_eq_root hInvariant (by omega)
        have hRoot : lowerSorted[0] = state.lower[0] := by
          simpa [lowerSorted, hLowerLength, hLowerSize] using
            sortedLower_last_eq_root hInvariant (by omega)
        rw [median_of_odd_size state hOdd]
        unfold medianSpec
        rw [← hSortedArrayEq]
        simp [List.size_toArray, hLowerLength, hUpperLength, hLowerSize,
          hUpperSize, hRoot]
      | succ k =>
        have hLowerSize : state.lower.size = k + 2 := by omega
        have hLowerRoot : lowerSorted[k + 1] = state.lower[0] := by
          simpa [lowerSorted, hLowerLength, hLowerSize] using
            sortedLower_last_eq_root hInvariant (by omega)
        have hMiddle : (k + 2 + k) / 2 = k + 1 := by omega
        have hParity : (k + 2 + k) % 2 = 0 := by omega
        rw [median_of_odd_size state hOdd]
        unfold medianSpec
        rw [← hSortedArrayEq]
        simp [List.size_toArray, hLowerLength, hUpperLength, hLowerSize,
          hUpperSize, hMiddle, hParity] <;>
          exact hLowerRoot.symm
  · have hInputZero : input.size = 0 := by omega
    have hStateSizes : state.lower.size = 0 ∧ state.upper.size = 0 := by omega
    rcases hStateSizes with ⟨hLowerZero, hUpperZero⟩
    have hInputEmpty : input = #[] := Array.size_eq_zero_iff.mp hInputZero
    have hLowerEmpty : state.lower = #[] := Array.size_eq_zero_iff.mp hLowerZero
    have hUpperEmpty : state.upper = #[] := Array.size_eq_zero_iff.mp hUpperZero
    simp [medianSpec, LeanExperiments.RunningMedian.median,
      hInputEmpty, hLowerEmpty, hUpperEmpty,
      LeanExperiments.Verification.MergeSort.mergeSort_empty]

/-- 下側2要素・上側1要素の状態で下側根より大きい値を挿入した後、
公開中央値はソート仕様と一致する。 -/
theorem median_insert_eq_medianSpec_of_two_one_of_gt_root {input : Array Nat}
    {state : LeanExperiments.RunningMedian.State}
    (hInvariant : StateInvariant input state)
    {lowerRoot lowerOther upperRoot value : Nat}
    (hState : state = { lower := #[lowerRoot, lowerOther], upper := #[upperRoot] })
    (hValue : lowerRoot < value) :
    LeanExperiments.RunningMedian.median
        (LeanExperiments.RunningMedian.insert state value) =
      medianSpec (input.push value) :=
  median_eq_medianSpec_of_invariant
    (StateInvariant.insert_from_two_one_of_gt_root hInvariant hState hValue)

/-- 最終状態が不変条件を満たすなら、公開関数 `medianOf` はソート仕様と一致する。

この定理は状態不変条件と出力正当性の境界を示す。後続する任意入力向け定理で、実装が
不変条件を保つことを合成している。
-/
theorem medianOf_eq_medianSpec_of_invariant {input : Array Nat}
    (hInvariant : StateInvariant input
      (LeanExperiments.RunningMedian.ofArray input)) :
    LeanExperiments.RunningMedian.medianOf input = medianSpec input := by
  unfold LeanExperiments.RunningMedian.medianOf
  exact median_eq_medianSpec_of_invariant hInvariant

/-- 長さ2以下では、逐次中央値の出力は独立なソート仕様と一致する。

これは値を列挙した有限計算ではなく、任意の自然数値について長さだけを制限した
一般証明である。任意長の場合は、後続の `medianOf_eq_medianSpec_arbitrary` が同じ
出力正当性をサイズ制約なしで示す。
-/
theorem medianOf_eq_medianSpec_of_size_le_two (values : Array Nat)
    (hSize : values.size ≤ 2) :
    LeanExperiments.RunningMedian.medianOf values = medianSpec values := by
  exact medianOf_eq_medianSpec_of_invariant
    (StateInvariant.ofArray_size_le_two values hSize)

/-- 二値入力の実装状態が不変条件を満たすなら、その中央値は二値の平均である。

不変条件を明示的に受け取る中間契約であり、任意入力での成立は後述の一般定理から従う。
-/
theorem medianOf_pair_of_invariant (left right : Nat)
    (hInvariant : StateInvariant #[left, right]
      (LeanExperiments.RunningMedian.ofArray #[left, right])) :
    LeanExperiments.RunningMedian.medianOf #[left, right] =
      some (left + right, 2) := by
  rw [medianOf_eq_medianSpec_of_invariant hInvariant]
  exact medianSpec_pair left right

/-- 2つ目の値が1つ目より大きい入力では、公開中央値関数が二値の平均を返す。 -/
theorem medianOf_pair_of_lt {left right : Nat} (hLeft : left < right) :
    LeanExperiments.RunningMedian.medianOf #[left, right] =
      some (left + right, 2) := by
  rw [medianOf_eq_medianSpec_of_invariant (StateInvariant.ofArray_pair_of_lt hLeft)]
  exact medianSpec_pair left right

/-- 任意の二値入力で、公開中央値関数は二値の平均を返す。 -/
theorem medianOf_pair (left right : Nat) :
    LeanExperiments.RunningMedian.medianOf #[left, right] =
      some (left + right, 2) := by
  exact medianOf_pair_of_invariant left right (StateInvariant.ofArray_pair left right)

/-- 実装状態が不変条件を満たすなら、公開関数が `none` を返すのは空入力の場合に限る。 -/
theorem medianOf_none_iff_empty_of_invariant {input : Array Nat}
    (hInvariant : StateInvariant input
      (LeanExperiments.RunningMedian.ofArray input)) :
    LeanExperiments.RunningMedian.medianOf input = none ↔ input = #[] := by
  rw [medianOf_eq_medianSpec_of_invariant hInvariant]
  exact medianSpec_none_iff_empty input

/-- 公開中央値が `none` になるのは入力が空の場合に限る。 -/
theorem medianOf_none_iff_empty (input : Array Nat) :
    LeanExperiments.RunningMedian.medianOf input = none ↔ input = #[] :=
  medianOf_none_iff_empty_of_invariant (StateInvariant.ofArray_arbitrary input)

/-- 最終状態の不変条件があれば、順列である二入力の中央値結果は一致する。 -/
theorem medianOf_eq_of_stateInvariants_of_perm {values₁ values₂ : Array Nat}
    (hInvariant₁ : StateInvariant values₁
      (LeanExperiments.RunningMedian.ofArray values₁))
    (hInvariant₂ : StateInvariant values₂
      (LeanExperiments.RunningMedian.ofArray values₂))
    (hPerm : values₁.toList.Perm values₂.toList) :
    LeanExperiments.RunningMedian.medianOf values₁ =
      LeanExperiments.RunningMedian.medianOf values₂ := by
  calc
    LeanExperiments.RunningMedian.medianOf values₁ = medianSpec values₁ := by
      unfold LeanExperiments.RunningMedian.medianOf
      exact median_eq_medianSpec_of_invariant hInvariant₁
    _ = medianSpec values₂ := medianSpec_eq_of_perm hPerm
    _ = LeanExperiments.RunningMedian.medianOf values₂ := by
      symm
      unfold LeanExperiments.RunningMedian.medianOf
      exact median_eq_medianSpec_of_invariant hInvariant₂

/-- 奇数個の中央値である下側の根は、上下の分割をまたぐ境界値になる。 -/
theorem odd_median_partition_bounds {input : Array Nat}
    {state : LeanExperiments.RunningMedian.State}
    (hInvariant : StateInvariant input state)
    (hSize : state.lower.size = state.upper.size + 1)
    {lowerIndex upperIndex : Nat}
    (hLowerIndex : lowerIndex < state.lower.size)
    (hUpperIndex : upperIndex < state.upper.size) :
    state.lower[lowerIndex]! ≤ state.lower[0]! ∧
      state.lower[0]! ≤ state.upper[upperIndex]! := by
  refine ⟨lower_value_le_root hInvariant hLowerIndex, ?_⟩
  have hCross := hInvariant.2.2.2.1 0 (by omega) upperIndex hUpperIndex
  open Array in
    simpa only [← getElem!_pos] using hCross

/-- 奇数個の不変状態で返す値は、入力の中央順位を占める。

順位は重複値を考慮し、中央値より小さい要素数が中央順位以下、中央値以下の要素数が
中央順位より大きいこととして表す。ソート仕様の順位特徴付けをヒープ分割へ移している。
-/
theorem odd_median_rank_bounds {input : Array Nat}
    {state : LeanExperiments.RunningMedian.State}
    (hInvariant : StateInvariant input state)
    (hSize : state.lower.size = state.upper.size + 1) :
    input.toList.countP (fun value => decide (value < state.lower[0]!)) ≤ state.upper.size ∧
      state.upper.size <
        input.toList.countP (fun value => decide (value ≤ state.lower[0]!)) := by
  let lowerSorted := LeanExperiments.MergeSort.mergeSort state.lower.toList
  let upperSorted := LeanExperiments.MergeSort.mergeSort state.upper.toList
  let output := lowerSorted ++ upperSorted
  have hCorrect := sortedHeapParts_correct hInvariant
  have hLowerCorrect := LeanExperiments.Verification.MergeSort.mergeSort_correct
    state.lower.toList
  have hUpperCorrect := LeanExperiments.Verification.MergeSort.mergeSort_correct
    state.upper.toList
  have hLowerLength : lowerSorted.length = state.lower.size := by
    simpa [lowerSorted] using hLowerCorrect.2.length_eq
  have hUpperLength : upperSorted.length = state.upper.size := by
    simpa [upperSorted] using hUpperCorrect.2.length_eq
  have hOutputLength : output.length = input.size := by
    dsimp [output]
    rw [List.length_append, hLowerLength, hUpperLength]
    have hLengths := hInvariant.1.length_eq
    simpa using hLengths
  have hIndexLower : state.upper.size < lowerSorted.length := by
    rw [hLowerLength]
    omega
  have hIndexOutput : state.upper.size < output.length := by
    rw [hOutputLength]
    have hLengths := hInvariant.1.length_eq
    have hTotal : state.lower.size + state.upper.size = input.size := by simpa using hLengths
    omega
  have hLowerRoot : lowerSorted[state.upper.size]! = state.lower[0]! := by
    simpa [lowerSorted, hLowerLength, hSize] using
      sortedLower_last_eq_root hInvariant (by omega)
  have hOutputRoot : output[state.upper.size] = state.lower[0]'(by omega) := by
    dsimp [output]
    rw [List.getElem_append_left hIndexLower]
    have hLowerRootSafe : lowerSorted[state.upper.size] = state.lower[0]'(by omega) := by
      simpa only [getElem!_pos lowerSorted state.upper.size hIndexLower,
        getElem!_pos state.lower 0 (by omega)] using hLowerRoot
    exact hLowerRootSafe
  have hRank := hCorrect.getElem_eq_iff_rank_bounds hIndexOutput
    (state.lower[0]'(by omega))
  rw [hOutputRoot] at hRank
  simpa only [getElem!_pos state.lower 0 (by omega)] using hRank.mp rfl

/-- 偶数個の不変状態では、二つの根がソート結果の隣り合う中央順位を占める。

下側最大値は順位 `lower.size - 1`、上側最小値は順位 `lower.size` に現れる。このため、
二つの根の平均が偶数個の中央値になることを、重複値を含む順位条件でも確認できる。
-/
theorem even_median_roots_rank_bounds {input : Array Nat}
    {state : LeanExperiments.RunningMedian.State}
    (hInvariant : StateInvariant input state)
    (hEqual : state.lower.size = state.upper.size)
    (hUpper : 0 < state.upper.size) :
    (input.toList.countP (fun value => decide (value < state.lower[0]!)) ≤
        state.lower.size - 1 ∧
      state.lower.size - 1 <
        input.toList.countP (fun value => decide (value ≤ state.lower[0]!))) ∧
    (input.toList.countP (fun value => decide (value < state.upper[0]!)) ≤
        state.lower.size ∧
      state.lower.size <
        input.toList.countP (fun value => decide (value ≤ state.upper[0]!))) := by
  let lowerSorted := LeanExperiments.MergeSort.mergeSort state.lower.toList
  let upperSorted := LeanExperiments.MergeSort.mergeSort state.upper.toList
  let output := lowerSorted ++ upperSorted
  have hCorrect := sortedHeapParts_correct hInvariant
  have hLowerCorrect := LeanExperiments.Verification.MergeSort.mergeSort_correct
    state.lower.toList
  have hUpperCorrect := LeanExperiments.Verification.MergeSort.mergeSort_correct
    state.upper.toList
  have hLowerLength : lowerSorted.length = state.lower.size := by
    simpa [lowerSorted] using hLowerCorrect.2.length_eq
  have hUpperLength : upperSorted.length = state.upper.size := by
    simpa [upperSorted] using hUpperCorrect.2.length_eq
  have hOutputLength : output.length = input.size := by
    dsimp [output]
    rw [List.length_append, hLowerLength, hUpperLength]
    have hLengths := hInvariant.1.length_eq
    simpa using hLengths
  have hLowerIndex : state.lower.size - 1 < output.length := by
    rw [hOutputLength]
    have hLengths := hInvariant.1.length_eq
    have hTotal : state.lower.size + state.upper.size = input.size := by simpa using hLengths
    omega
  have hUpperIndex : state.lower.size < output.length := by
    rw [hOutputLength]
    have hLengths := hInvariant.1.length_eq
    have hTotal : state.lower.size + state.upper.size = input.size := by simpa using hLengths
    omega
  have hLowerPartIndex : state.lower.size - 1 < lowerSorted.length := by
    rw [hLowerLength]
    omega
  have hLowerRoot : lowerSorted[state.lower.size - 1]! = state.lower[0]! := by
    simpa [lowerSorted, hLowerLength] using
      sortedLower_last_eq_root hInvariant (by omega)
  have hLowerOutput : output[state.lower.size - 1] = state.lower[0]'(by omega) := by
    dsimp [output]
    rw [List.getElem_append_left hLowerPartIndex]
    have hLowerRootSafe :
        lowerSorted[state.lower.size - 1] = state.lower[0]'(by omega) := by
      simpa only [getElem!_pos lowerSorted (state.lower.size - 1) hLowerPartIndex,
        getElem!_pos state.lower 0 (by omega)] using hLowerRoot
    exact hLowerRootSafe
  have hUpperRoot : upperSorted[0]! = state.upper[0]! := by
    simpa [upperSorted] using sortedUpper_first_eq_root hInvariant hUpper
  have hUpperOutput : output[state.lower.size] = state.upper[0]'hUpper := by
    dsimp [output]
    rw [List.getElem_append_right (by omega)]
    have hUpperRootSafe : upperSorted[0] = state.upper[0]'hUpper := by
      simpa only [getElem!_pos upperSorted 0 (by omega),
        getElem!_pos state.upper 0 hUpper] using hUpperRoot
    simpa [hLowerLength] using hUpperRootSafe
  have hLowerRank := hCorrect.getElem_eq_iff_rank_bounds hLowerIndex
    (state.lower[0]'(by omega))
  have hUpperRank := hCorrect.getElem_eq_iff_rank_bounds hUpperIndex
    (state.upper[0]'hUpper)
  rw [hLowerOutput] at hLowerRank
  rw [hUpperOutput] at hUpperRank
  constructor
  · simpa only [getElem!_pos state.lower 0 (by omega)] using hLowerRank.mp rfl
  · simpa only [getElem!_pos state.upper 0 hUpper] using hUpperRank.mp rfl

/-- 偶数個の中央値の分子は、下側・上側の根の間の平均として挟まれる。 -/
theorem even_median_numerator_bounds {input : Array Nat}
    {state : LeanExperiments.RunningMedian.State}
    (hInvariant : StateInvariant input state)
    (hSize : state.lower.size = state.upper.size)
    (hUpper : 0 < state.upper.size) :
    2 * state.lower[0]! ≤ state.lower[0]! + state.upper[0]! ∧
      state.lower[0]! + state.upper[0]! ≤ 2 * state.upper[0]! := by
  have hBoundary := lower_root_le_upper_root hInvariant (by omega) hUpper
  open Array in
    have hBoundaryBang : state.lower[0]! ≤ state.upper[0]! := by
      simpa only [← getElem!_pos] using hBoundary
    omega

/-- 奇数個の不変状態で返す中央値は、入力に実際に含まれる要素である。 -/
theorem odd_median_mem_input {input : Array Nat}
    {state : LeanExperiments.RunningMedian.State}
    (hInvariant : StateInvariant input state)
    (hSize : state.lower.size = state.upper.size + 1) :
    state.lower[0]'(by omega) ∈ input.toList :=
  lower_root_mem_input hInvariant (by omega)

/-- 偶数個の不変状態で平均に使う二つの根は、どちらも入力要素である。 -/
theorem even_median_roots_mem_input {input : Array Nat}
    {state : LeanExperiments.RunningMedian.State}
    (hInvariant : StateInvariant input state)
    (hSize : state.lower.size = state.upper.size)
    (hUpper : 0 < state.upper.size) :
    state.lower[0]'(by omega) ∈ input.toList ∧
      state.upper[0]'hUpper ∈ input.toList := by
  exact ⟨lower_root_mem_input hInvariant (by omega),
    upper_root_mem_input hInvariant hUpper⟩

/-- 不変条件を満たす非空入力には、必ず中央値の結果が存在する。 -/
theorem median_exists_of_nonempty_invariant {input : Array Nat}
    {state : LeanExperiments.RunningMedian.State}
    (hInvariant : StateInvariant input state) (hInput : 0 < input.size) :
    ∃ numerator denominator,
      LeanExperiments.RunningMedian.median state = some (numerator, denominator) := by
  have hParity := StateInvariant.heap_size_parity_iff hInvariant
  by_cases hEven : input.size % 2 = 0
  · have hEqual : state.lower.size = state.upper.size := hParity.1.mp hEven
    have hUpperPositive : 0 < state.upper.size := by
      rw [(StateInvariant.heap_sizes hInvariant).2]
      omega
    exact ⟨state.lower[0]'(by omega) + state.upper[0]'hUpperPositive, 2,
      median_of_even_size state hEqual hUpperPositive⟩
  · have hOdd : input.size % 2 = 1 := by omega
    have hLowerOneMore : state.lower.size = state.upper.size + 1 := hParity.2.mp hOdd
    exact ⟨state.lower[0]'(by omega), 1, median_of_odd_size state hLowerOneMore⟩

/-- 非空入力の不変な最終状態では、公開中央値が存在し、分母が入力長の偶奇に合う。

実装が不変条件を保つことは仮定として明示し、中央値の全域性と分母の契約を合成する。
-/
theorem medianOf_result_and_denominator_parity_of_invariant {input : Array Nat}
    (hInvariant : StateInvariant input (LeanExperiments.RunningMedian.ofArray input))
    (hInput : 0 < input.size) :
    ∃ numerator denominator,
      LeanExperiments.RunningMedian.medianOf input = some (numerator, denominator) ∧
        ((input.size % 2 = 1 ∧ denominator = 1) ∨
          (input.size % 2 = 0 ∧ denominator = 2)) := by
  obtain ⟨numerator, denominator, hResult⟩ :=
    median_exists_of_nonempty_invariant hInvariant hInput
  refine ⟨numerator, denominator, ?_, ?_⟩
  · exact hResult
  · apply medianSpec_denominator_parity
    rw [← medianOf_eq_medianSpec_of_invariant hInvariant]
    exact hResult

/-- 任意の非空入力では公開中央値が定義され、分母は入力長の偶奇に一致する。 -/
theorem medianOf_result_and_denominator_parity {input : Array Nat}
    (hInput : 0 < input.size) :
    ∃ numerator denominator,
      LeanExperiments.RunningMedian.medianOf input = some (numerator, denominator) ∧
        ((input.size % 2 = 1 ∧ denominator = 1) ∨
          (input.size % 2 = 0 ∧ denominator = 2)) :=
  medianOf_result_and_denominator_parity_of_invariant
    (StateInvariant.ofArray_arbitrary input) hInput

/-- 入力全体が既知の範囲内なら、不変状態の中央値も同じ範囲内に収まる。

偶数個の場合は中央値を分子・分母で表すため、範囲条件も分母倍した整数不等式で示す。
-/
theorem median_within_input_bounds {input : Array Nat}
    {state : LeanExperiments.RunningMedian.State}
    (hInvariant : StateInvariant input state)
    (hInput : 0 < input.size)
    (hLowerBound : ∀ value, value ∈ input.toList → lowerBound ≤ value)
    (hUpperBound : ∀ value, value ∈ input.toList → value ≤ upperBound) :
    ∃ numerator denominator,
      LeanExperiments.RunningMedian.median state = some (numerator, denominator) ∧
        ((denominator = 1 ∧ lowerBound ≤ numerator ∧ numerator ≤ upperBound) ∨
          (denominator = 2 ∧ 2 * lowerBound ≤ numerator ∧
            numerator ≤ 2 * upperBound)) := by
  have hParity := StateInvariant.heap_size_parity_iff hInvariant
  by_cases hEven : input.size % 2 = 0
  · have hEqual := hParity.1.mp hEven
    have hUpperPositive : 0 < state.upper.size := by
      rw [(StateInvariant.heap_sizes hInvariant).2]
      omega
    have hMedian := median_of_even_size state hEqual hUpperPositive
    obtain ⟨hLowerMem, hUpperMem⟩ :=
      even_median_roots_mem_input hInvariant hEqual hUpperPositive
    let lowerRoot : Nat := state.lower[0]'(by omega)
    let upperRoot : Nat := state.upper[0]'hUpperPositive
    have hLower := hLowerBound lowerRoot hLowerMem
    have hLowerUpper := hLowerBound upperRoot hUpperMem
    have hUpperLower := hUpperBound lowerRoot hLowerMem
    have hUpper := hUpperBound upperRoot hUpperMem
    refine ⟨lowerRoot + upperRoot, 2, ?_, ?_⟩
    · simpa [lowerRoot, upperRoot] using hMedian
    · right
      refine ⟨rfl, ?_, ?_⟩ <;> omega
  · have hOdd : input.size % 2 = 1 := by omega
    have hLowerOneMore := hParity.2.mp hOdd
    have hMedian := median_of_odd_size state hLowerOneMore
    have hRootMem := odd_median_mem_input hInvariant hLowerOneMore
    let lowerRoot : Nat := state.lower[0]'(by omega)
    have hLower := hLowerBound lowerRoot hRootMem
    have hUpper := hUpperBound lowerRoot hRootMem
    refine ⟨lowerRoot, 1, ?_, ?_⟩
    · simpa [lowerRoot] using hMedian
    · left
      exact ⟨rfl, hLower, hUpper⟩

/-- 入力値が上下限の間にあれば、公開中央値も同じ値域に収まる。

偶数長では中央値を分子・分母で返すため、分子に対する上下限を分母倍して表す。
入力長や値の大きさには上限を置かない。
-/
theorem medianOf_within_input_bounds {input : Array Nat}
    (hInput : 0 < input.size)
    (hLowerBound : ∀ value, value ∈ input.toList → lowerBound ≤ value)
    (hUpperBound : ∀ value, value ∈ input.toList → value ≤ upperBound) :
    ∃ numerator denominator,
      LeanExperiments.RunningMedian.medianOf input = some (numerator, denominator) ∧
        ((denominator = 1 ∧ lowerBound ≤ numerator ∧ numerator ≤ upperBound) ∨
          (denominator = 2 ∧ 2 * lowerBound ≤ numerator ∧
            numerator ≤ 2 * upperBound)) := by
  obtain ⟨numerator, denominator, hMedian, hBounds⟩ :=
    median_within_input_bounds (StateInvariant.ofArray_arbitrary input)
      hInput hLowerBound hUpperBound
  exact ⟨numerator, denominator, by
    simpa [LeanExperiments.RunningMedian.medianOf] using hMedian, hBounds⟩

/-- 奇数長の公開中央値は、入力に含まれる要素を分母1で返す。 -/
theorem medianOf_odd_numerator_mem_input {input : Array Nat}
    (hOdd : input.size % 2 = 1) :
    ∃ value, value ∈ input.toList ∧
      LeanExperiments.RunningMedian.medianOf input = some (value, 1) := by
  let state := LeanExperiments.RunningMedian.ofArray input
  have hInvariant : StateInvariant input state := StateInvariant.ofArray_arbitrary input
  have hSizes := (StateInvariant.heap_size_parity_iff hInvariant).2.mp hOdd
  have hMedian := median_of_odd_size state hSizes
  have hMem := odd_median_mem_input hInvariant hSizes
  refine ⟨state.lower[0]'(by omega), hMem, ?_⟩
  simpa [state, LeanExperiments.RunningMedian.medianOf] using hMedian

/-- 偶数長の公開中央値は、入力中の順序付いた二値の平均である。 -/
theorem medianOf_even_roots_mem_input {input : Array Nat}
    (hEven : input.size % 2 = 0) (hNonempty : 0 < input.size) :
    ∃ lowerRoot upperRoot,
      lowerRoot ∈ input.toList ∧ upperRoot ∈ input.toList ∧
        lowerRoot ≤ upperRoot ∧
        LeanExperiments.RunningMedian.medianOf input =
          some (lowerRoot + upperRoot, 2) := by
  let state := LeanExperiments.RunningMedian.ofArray input
  have hInvariant : StateInvariant input state := StateInvariant.ofArray_arbitrary input
  have hSizes := (StateInvariant.heap_size_parity_iff hInvariant).1.mp hEven
  have hUpperPositive : 0 < state.upper.size := by
    rw [(StateInvariant.heap_sizes hInvariant).2]
    omega
  let lowerRoot := state.lower[0]'(by omega)
  let upperRoot := state.upper[0]'hUpperPositive
  obtain ⟨hLowerMem, hUpperMem⟩ :=
    even_median_roots_mem_input hInvariant hSizes hUpperPositive
  have hOrder := lower_root_le_upper_root hInvariant (by omega) hUpperPositive
  have hMedian := median_of_even_size state hSizes hUpperPositive
  refine ⟨lowerRoot, upperRoot, hLowerMem, hUpperMem, ?_, ?_⟩
  · simpa [lowerRoot, upperRoot] using hOrder
  · simpa [state, lowerRoot, upperRoot, LeanExperiments.RunningMedian.medianOf] using hMedian

/-- 奇数長では、公開中央値の値が中央順位を占めることを重複込みの個数で特徴付ける。

中央値より小さい入力要素数は中央添字以下で、中央値以下の要素数は中央添字より多い。
この契約は入力長・値域に上限を置かず、公開関数が返す値と独立した順位仕様を結ぶ。
-/
theorem medianOf_odd_rank_bounds {input : Array Nat}
    (hOdd : input.size % 2 = 1) :
    ∃ value,
      input.toList.countP (fun item => decide (item < value)) ≤ input.size / 2 ∧
        input.size / 2 <
          input.toList.countP (fun item => decide (item ≤ value)) ∧
        LeanExperiments.RunningMedian.medianOf input = some (value, 1) := by
  let state := LeanExperiments.RunningMedian.ofArray input
  have hInvariant : StateInvariant input state := StateInvariant.ofArray_arbitrary input
  have hSize := (StateInvariant.heap_size_parity_iff hInvariant).2.mp hOdd
  have hUpperSize := (StateInvariant.heap_sizes hInvariant).2
  let value := state.lower[0]'(by omega)
  have hValueBang : state.lower[0]! = value := by
    exact getElem!_pos state.lower 0 (by omega)
  have hRank := odd_median_rank_bounds hInvariant hSize
  have hMedian := median_of_odd_size state hSize
  refine ⟨value, ?_, ?_, ?_⟩
  · simpa [value, hValueBang, hUpperSize] using hRank.1
  · simpa [value, hValueBang, hUpperSize] using hRank.2
  · simpa [state, value, LeanExperiments.RunningMedian.medianOf] using hMedian

/-- 偶数長では、公開中央値の二つの根が隣接する中央順位を占める。

下側根は順位 `input.size / 2 - 1`、上側根は順位 `input.size / 2` の値であり、
中央値は両者の和を分子、2を分母として返す。重複値と任意の入力長を含む一般定理である。
-/
theorem medianOf_even_roots_rank_bounds {input : Array Nat}
    (hEven : input.size % 2 = 0) (hNonempty : 0 < input.size) :
    ∃ lowerRoot upperRoot,
      input.toList.countP (fun item => decide (item < lowerRoot)) ≤ input.size / 2 - 1 ∧
        input.size / 2 - 1 <
          input.toList.countP (fun item => decide (item ≤ lowerRoot)) ∧
        input.toList.countP (fun item => decide (item < upperRoot)) ≤ input.size / 2 ∧
        input.size / 2 <
          input.toList.countP (fun item => decide (item ≤ upperRoot)) ∧
        lowerRoot ≤ upperRoot ∧
        LeanExperiments.RunningMedian.medianOf input =
          some (lowerRoot + upperRoot, 2) := by
  let state := LeanExperiments.RunningMedian.ofArray input
  have hInvariant : StateInvariant input state := StateInvariant.ofArray_arbitrary input
  have hEqual := (StateInvariant.heap_size_parity_iff hInvariant).1.mp hEven
  have hSizes := StateInvariant.heap_sizes hInvariant
  have hUpperPositive : 0 < state.upper.size := by
    rw [hSizes.2]
    omega
  let lowerRoot := state.lower[0]'(by omega)
  let upperRoot := state.upper[0]'hUpperPositive
  have hLowerRootBang : state.lower[0]! = lowerRoot :=
    getElem!_pos state.lower 0 (by omega)
  have hUpperRootBang : state.upper[0]! = upperRoot :=
    getElem!_pos state.upper 0 hUpperPositive
  have hRanks := even_median_roots_rank_bounds hInvariant hEqual hUpperPositive
  rcases hRanks with ⟨⟨hLowerLt, hLowerLe⟩, ⟨hUpperLt, hUpperLe⟩⟩
  have hOrder := lower_root_le_upper_root hInvariant (by omega) hUpperPositive
  have hMedian := median_of_even_size state hEqual hUpperPositive
  refine ⟨lowerRoot, upperRoot, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change _ ≤ state.lower.size - 1 at hLowerLt
    change _ ≤ input.size / 2 - 1
    rw [hLowerRootBang] at hLowerLt
    omega
  · change state.lower.size - 1 < _ at hLowerLe
    change input.size / 2 - 1 < _
    rw [hLowerRootBang] at hLowerLe
    omega
  · change _ ≤ state.lower.size at hUpperLt
    change _ ≤ input.size / 2
    rw [hUpperRootBang] at hUpperLt
    omega
  · change state.lower.size < _ at hUpperLe
    change input.size / 2 < _
    rw [hUpperRootBang] at hUpperLe
    omega
  · simpa [lowerRoot, upperRoot] using hOrder
  · simpa [state, lowerRoot, upperRoot, LeanExperiments.RunningMedian.medianOf] using hMedian

/-- 0要素または1要素を表す任意の不変状態へ値を挿入した後、
実装の中央値は更新後入力のソート仕様と一致する。

状態遷移の基底契約と一般の中央値仕様定理を合成し、有限値列挙なしに
最初の2回までの挿入後の出力正当性を導く。
-/
theorem median_insert_eq_medianSpec_of_size_le_one {input : Array Nat}
    {state : LeanExperiments.RunningMedian.State}
    (hInvariant : StateInvariant input state) (hSize : input.size ≤ 1)
    (value : Nat) :
    LeanExperiments.RunningMedian.median
        (LeanExperiments.RunningMedian.insert state value) =
      medianSpec (input.push value) := by
  exact median_eq_medianSpec_of_invariant
    (StateInvariant.insert_of_size_le_one hInvariant hSize value)

/-- 入力長2以下の不変状態へ1件挿入した後も、公開中央値はソート仕様と一致する。 -/
theorem median_insert_eq_medianSpec_of_size_le_two {input : Array Nat}
    {state : LeanExperiments.RunningMedian.State}
    (hInvariant : StateInvariant input state) (hSize : input.size ≤ 2)
    (value : Nat) :
    LeanExperiments.RunningMedian.median
        (LeanExperiments.RunningMedian.insert state value) =
      medianSpec (input.push value) := by
  exact median_eq_medianSpec_of_invariant
    (StateInvariant.insert_of_size_le_two hInvariant hSize value)

/-- 状態検査器の成功から、要素分割・ヒープ順序・境界・サイズ条件を導く。 -/
theorem stateInvariantCheck_sound (input : Array Nat)
    (state : LeanExperiments.RunningMedian.State)
    (hCheck : stateInvariantCheck input state = true) :
    StateInvariant input state := by
  have hParts :
      (((decide ((state.lower.toList ++ state.upper.toList).Perm input.toList) = true ∧
        heapCheck maxPrefer state.lower = true) ∧
        heapCheck minPrefer state.upper = true) ∧
        state.lower.all (fun lowerValue =>
          state.upper.all (fun upperValue => decide (lowerValue ≤ upperValue))) = true) ∧
      (state.lower.size == state.upper.size ||
        state.lower.size == state.upper.size + 1) = true := by
    unfold stateInvariantCheck at hCheck
    simpa only [Bool.and_eq_true] using hCheck
  rcases hParts with ⟨⟨⟨⟨hPerm, hLowerHeap⟩, hUpperHeap⟩, hCross⟩, hSize⟩
  refine ⟨of_decide_eq_true hPerm,
    (heapCheck_correct maxPrefer state.lower).mp hLowerHeap,
    (heapCheck_correct minPrefer state.upper).mp hUpperHeap, ?_, ?_⟩
  · intro lowerIndex hLowerIndex upperIndex hUpperIndex
    have hForLower := (Array.all_eq_true.mp hCross) lowerIndex hLowerIndex
    have hForUpper := (Array.all_eq_true.mp hForLower) upperIndex hUpperIndex
    exact of_decide_eq_true (by simpa using hForUpper)
  · have hSizeOr :
        (state.lower.size == state.upper.size) = true ∨
          (state.lower.size == state.upper.size + 1) = true := by
      simpa only [Bool.or_eq_true] using hSize
    rcases hSizeOr with hEqual | hOneMore
    · left
      exact beq_iff_eq.mp hEqual
    · right
      exact beq_iff_eq.mp hOneMore

/-- 論理的不変条件が成り立てば、状態検査器は成功する。 -/
theorem stateInvariantCheck_complete (input : Array Nat)
    (state : LeanExperiments.RunningMedian.State)
    (hInvariant : StateInvariant input state) :
    stateInvariantCheck input state = true := by
  have hCross : state.lower.all (fun lowerValue =>
      state.upper.all (fun upperValue => decide (lowerValue ≤ upperValue))) = true := by
    apply Array.all_eq_true.mpr
    intro lowerIndex hLowerIndex
    apply Array.all_eq_true.mpr
    intro upperIndex hUpperIndex
    exact decide_eq_true (hInvariant.2.2.2.1 lowerIndex hLowerIndex upperIndex hUpperIndex)
  have hSize : (state.lower.size == state.upper.size ||
      state.lower.size == state.upper.size + 1) = true := by
    rcases hInvariant.2.2.2.2 with hEqual | hOneMore
    · simp [hEqual]
    · simp [hOneMore]
  have hParts :
      (((decide ((state.lower.toList ++ state.upper.toList).Perm input.toList) = true ∧
        heapCheck maxPrefer state.lower = true) ∧
        heapCheck minPrefer state.upper = true) ∧
        state.lower.all (fun lowerValue =>
          state.upper.all (fun upperValue => decide (lowerValue ≤ upperValue))) = true) ∧
      (state.lower.size == state.upper.size ||
        state.lower.size == state.upper.size + 1) = true := by
    refine ⟨⟨⟨⟨decide_eq_true hInvariant.1,
      (heapCheck_correct maxPrefer state.lower).mpr hInvariant.2.1⟩,
      (heapCheck_correct minPrefer state.upper).mpr hInvariant.2.2.1⟩,
      hCross⟩, hSize⟩
  unfold stateInvariantCheck
  simpa only [Bool.and_eq_true] using hParts

/-- 状態検査器の成功と論理的不変条件は同値である。 -/
theorem stateInvariantCheck_correct (input : Array Nat)
    (state : LeanExperiments.RunningMedian.State) :
    stateInvariantCheck input state = true ↔ StateInvariant input state := by
  constructor
  · exact stateInvariantCheck_sound input state
  · exact stateInvariantCheck_complete input state

/-- 二つの単一要素ヒープから下側の根以下を挿入する場合、更新後の状態検査器も成功する。 -/
theorem stateInvariantCheck_insert_from_two_singletons_of_le
    {input : Array Nat} {state : LeanExperiments.RunningMedian.State}
    (hInvariant : StateInvariant input state)
    {lowerRoot upperRoot value : Nat}
    (hState : state = { lower := #[lowerRoot], upper := #[upperRoot] })
    (hValue : value ≤ lowerRoot) :
    stateInvariantCheck (input.push value)
        (LeanExperiments.RunningMedian.insert state value) = true :=
  (stateInvariantCheck_correct _ _).2
    (StateInvariant.insert_from_two_singletons_of_le hInvariant hState hValue)

/-- 二つの単一要素ヒープから下側根より大きい値を挿入する場合も、更新後の状態検査器は成功する。-/
theorem stateInvariantCheck_insert_from_two_singletons_of_gt
    {input : Array Nat} {state : LeanExperiments.RunningMedian.State}
    (hInvariant : StateInvariant input state)
    {lowerRoot upperRoot value : Nat}
    (hState : state = { lower := #[lowerRoot], upper := #[upperRoot] })
    (hValue : lowerRoot < value) :
    stateInvariantCheck (input.push value)
        (LeanExperiments.RunningMedian.insert state value) = true :=
  (stateInvariantCheck_correct _ _).2
    (StateInvariant.insert_from_two_singletons_of_gt hInvariant hState hValue)

/-- 2+1要素状態の上側挿入分岐でも、更新後の状態検査器が成功する。 -/
theorem stateInvariantCheck_insert_from_two_one_of_gt_root
    {input : Array Nat} {state : LeanExperiments.RunningMedian.State}
    (hInvariant : StateInvariant input state)
    {lowerRoot lowerOther upperRoot value : Nat}
    (hState : state = { lower := #[lowerRoot, lowerOther], upper := #[upperRoot] })
    (hValue : lowerRoot < value) :
    stateInvariantCheck (input.push value)
        (LeanExperiments.RunningMedian.insert state value) = true :=
  (stateInvariantCheck_correct _ _).2
    (StateInvariant.insert_from_two_one_of_gt_root hInvariant hState hValue)

/-- 2+1要素状態の下側挿入分岐でも、更新後の状態検査器は成功する。 -/
theorem stateInvariantCheck_insert_from_two_one_of_le_root
    {input : Array Nat} {state : LeanExperiments.RunningMedian.State}
    (hInvariant : StateInvariant input state)
    {lowerRoot lowerOther upperRoot value : Nat}
    (hState : state = { lower := #[lowerRoot, lowerOther], upper := #[upperRoot] })
    (hValue : value ≤ lowerRoot) :
    stateInvariantCheck (input.push value)
        (LeanExperiments.RunningMedian.insert state value) = true :=
  (stateInvariantCheck_correct _ _).2
    (StateInvariant.insert_from_two_one_of_le_root hInvariant hState hValue)

/-- 長さ2以下の不変状態への挿入後、状態検査器が成功する一般定理。 -/
theorem stateInvariantCheck_insert_of_size_le_two {input : Array Nat}
    {state : LeanExperiments.RunningMedian.State}
    (hInvariant : StateInvariant input state) (hSize : input.size ≤ 2)
    (value : Nat) :
    stateInvariantCheck (input.push value)
        (LeanExperiments.RunningMedian.insert state value) = true :=
  (stateInvariantCheck_correct _ _).2
    (StateInvariant.insert_of_size_le_two hInvariant hSize value)

/-- 長さ3以下の不変状態への挿入後、状態検査器が成功する一般定理。 -/
theorem stateInvariantCheck_insert_of_size_le_three {input : Array Nat}
    {state : LeanExperiments.RunningMedian.State}
    (hInvariant : StateInvariant input state) (hSize : input.size ≤ 3)
    (value : Nat) :
    stateInvariantCheck (input.push value)
        (LeanExperiments.RunningMedian.insert state value) = true :=
  (stateInvariantCheck_correct _ _).2
    (StateInvariant.insert_of_size_le_three hInvariant hSize value)

/-- 長さ4以下の不変状態への挿入後、状態検査器が成功する一般定理。 -/
theorem stateInvariantCheck_insert_of_size_le_four {input : Array Nat}
    {state : LeanExperiments.RunningMedian.State}
    (hInvariant : StateInvariant input state) (hSize : input.size ≤ 4)
    (value : Nat) :
    stateInvariantCheck (input.push value)
        (LeanExperiments.RunningMedian.insert state value) = true :=
  (stateInvariantCheck_correct _ _).2
    (StateInvariant.insert_of_size_le_four hInvariant hSize value)

/-- 長さ5の不変状態で値が下側根より大きい分岐では、挿入後の状態検査が成功する。 -/
theorem stateInvariantCheck_insert_from_size_five_of_gt_root {input : Array Nat}
    {state : LeanExperiments.RunningMedian.State}
    (hInvariant : StateInvariant input state) (hSize : input.size = 5)
    (value : Nat) (hValue : state.lower[0]! < value) :
    stateInvariantCheck (input.push value)
        (LeanExperiments.RunningMedian.insert state value) = true :=
  (stateInvariantCheck_correct _ _).2
    (StateInvariant.insert_from_size_five_of_gt_root hInvariant hSize value hValue)

/-- 長さ5で下側根以下の値を挿入した後も、独立した状態検査器が成功する。 -/
theorem stateInvariantCheck_insert_from_size_five_of_le_root {input : Array Nat}
    {state : LeanExperiments.RunningMedian.State}
    (hInvariant : StateInvariant input state) (hSize : input.size = 5)
    (value : Nat) (hValue : value ≤ state.lower[0]!) :
    stateInvariantCheck (input.push value)
        (LeanExperiments.RunningMedian.insert state value) = true :=
  (stateInvariantCheck_correct _ _).2
    (StateInvariant.insert_from_size_five_of_le_root hInvariant hSize value hValue)

/-- 長さ5の任意の不変状態への挿入後、独立した状態検査器が成功する。 -/
theorem stateInvariantCheck_insert_of_size_five {input : Array Nat}
    {state : LeanExperiments.RunningMedian.State}
    (hInvariant : StateInvariant input state) (hSize : input.size = 5)
    (value : Nat) :
    stateInvariantCheck (input.push value)
        (LeanExperiments.RunningMedian.insert state value) = true :=
  (stateInvariantCheck_correct _ _).2
    (StateInvariant.insert_of_size_five hInvariant hSize value)

/-- 長さ6の任意の不変状態への挿入後、独立した状態検査器が成功する。 -/
theorem stateInvariantCheck_insert_of_size_six {input : Array Nat}
    {state : LeanExperiments.RunningMedian.State}
    (hInvariant : StateInvariant input state) (hSize : input.size = 6)
    (value : Nat) :
    stateInvariantCheck (input.push value)
        (LeanExperiments.RunningMedian.insert state value) = true :=
  (stateInvariantCheck_correct _ _).2
    (StateInvariant.insert_of_size_six hInvariant hSize value)

/-- 長さ7の任意の不変状態への挿入後、独立した状態検査器が成功する。 -/
theorem stateInvariantCheck_insert_of_size_seven {input : Array Nat}
    {state : LeanExperiments.RunningMedian.State}
    (hInvariant : StateInvariant input state) (hSize : input.size = 7)
    (value : Nat) :
    stateInvariantCheck (input.push value)
        (LeanExperiments.RunningMedian.insert state value) = true :=
  (stateInvariantCheck_correct _ _).2
    (StateInvariant.insert_of_size_seven hInvariant hSize value)

/-- 長さ8の任意の不変状態への挿入後、独立した状態検査器が成功する。 -/
theorem stateInvariantCheck_insert_of_size_eight {input : Array Nat}
    {state : LeanExperiments.RunningMedian.State}
    (hInvariant : StateInvariant input state) (hSize : input.size = 8)
    (value : Nat) :
    stateInvariantCheck (input.push value)
        (LeanExperiments.RunningMedian.insert state value) = true :=
  (stateInvariantCheck_correct _ _).2
    (StateInvariant.insert_of_size_eight hInvariant hSize value)

/-- 長さ10の任意の不変状態への挿入後、独立した状態検査器が成功する。 -/
theorem stateInvariantCheck_insert_of_size_ten {input : Array Nat}
    {state : LeanExperiments.RunningMedian.State}
    (hInvariant : StateInvariant input state) (hSize : input.size = 10)
    (value : Nat) :
    stateInvariantCheck (input.push value)
        (LeanExperiments.RunningMedian.insert state value) = true :=
  (stateInvariantCheck_correct _ _).2
    (StateInvariant.insert_of_size_ten hInvariant hSize value)

/-- 状態検査器は、独立した最大・最小ヒープ数値仕様を含む論理条件と同値である。 -/
theorem stateInvariantCheck_iff_numericHeapSpecs (input : Array Nat)
    (state : LeanExperiments.RunningMedian.State) :
    stateInvariantCheck input state = true ↔
      (state.lower.toList ++ state.upper.toList).Perm input.toList ∧
        LeanExperiments.Verification.HeapSort.Spec.MaxHeap state.lower ∧
        MinHeap state.upper ∧
        (∀ lowerIndex (hLowerIndex : lowerIndex < state.lower.size),
          ∀ upperIndex (hUpperIndex : upperIndex < state.upper.size),
            state.lower[lowerIndex]'hLowerIndex ≤ state.upper[upperIndex]'hUpperIndex) ∧
        (state.lower.size = state.upper.size ∨
          state.lower.size = state.upper.size + 1) := by
  rw [stateInvariantCheck_correct, StateInvariant.iff_numericHeapSpecs]

/-- 状態検査器の成功は、ヒープ根だけで表した分割条件を含む独立仕様と同値である。 -/
theorem stateInvariantCheck_iff_numericHeapRootBoundary (input : Array Nat)
    (state : LeanExperiments.RunningMedian.State) :
    stateInvariantCheck input state = true ↔
      (state.lower.toList ++ state.upper.toList).Perm input.toList ∧
        LeanExperiments.Verification.HeapSort.Spec.MaxHeap state.lower ∧
        MinHeap state.upper ∧
        (state.lower.size = 0 ∨ state.upper.size = 0 ∨
          state.lower[0]! ≤ state.upper[0]!) ∧
        (state.lower.size = state.upper.size ∨
          state.lower.size = state.upper.size + 1) := by
  rw [stateInvariantCheck_correct, StateInvariant.iff_numericHeapRootBoundary]

/-- 検査済み状態の両ヒープから取り出す値はそれぞれ最大値・最小値で、残余契約も満たす。 -/
theorem stateInvariantCheck_popContracts (input : Array Nat)
    (state : LeanExperiments.RunningMedian.State)
    (hCheck : stateInvariantCheck input state = true) :
    LeanExperiments.Verification.HeapSort.Spec.PopMaxRestCorrectFor
      (LeanExperiments.RunningMedian.popHeap maxPrefer) state.lower ∧
    (∀ root rest,
      LeanExperiments.RunningMedian.popHeap minPrefer state.upper = some (root, rest) →
        (∀ index, index < state.upper.size → root ≤ state.upper[index]!) ∧
          rest.toList.Perm (state.upper.toList.drop 1) ∧
          rest.size + 1 = state.upper.size) := by
  have hInvariant := stateInvariantCheck_sound input state hCheck
  refine ⟨popHeap_maxPrefer_restCorrect_of_heapOrdered state.lower hInvariant.2.1, ?_⟩
  intro root rest hPop
  exact popHeap_minPrefer_contract_of_MinHeap
    ((minHeap_iff_HeapOrdered_minPrefer state.upper).2 hInvariant.2.2.1) hPop

/-- 状態検査器の成功から、非空な両ヒープの根の境界を直接導く。 -/
theorem stateInvariantCheck_lowerRoot_le_upperRoot (input : Array Nat)
    (state : LeanExperiments.RunningMedian.State)
    (hCheck : stateInvariantCheck input state = true)
    (hLower : 0 < state.lower.size) (hUpper : 0 < state.upper.size) :
    state.lower[0]! ≤ state.upper[0]! := by
  exact StateInvariant.lowerRoot_le_upperRoot input state
    (stateInvariantCheck_sound input state hCheck) hLower hUpper

/-- 状態検査器の結果は、検査対象の入力を順列に置き換えても変わらない。 -/
theorem stateInvariantCheck_eq_of_perm_input {input other : Array Nat}
    (state : LeanExperiments.RunningMedian.State)
    (hPerm : input.toList.Perm other.toList) :
    stateInvariantCheck input state = stateInvariantCheck other state := by
  cases hCheck : stateInvariantCheck input state with
  | false =>
      have hNotInvariant : ¬ StateInvariant input state := by
        intro hInvariant
        simp [stateInvariantCheck_complete _ _ hInvariant] at hCheck
      have hOtherNotInvariant : ¬ StateInvariant other state := by
        intro hInvariant
        apply hNotInvariant
        exact hInvariant.of_perm_input hPerm.symm
      have hOtherFalse : stateInvariantCheck other state ≠ true := by
        intro hTrue
        exact hOtherNotInvariant (stateInvariantCheck_sound _ _ hTrue)
      have hOther : stateInvariantCheck other state = false := by
        cases hResult : stateInvariantCheck other state <;> simp_all
      exact hOther.symm
  | true =>
      have hInvariant := stateInvariantCheck_sound _ _ hCheck
      have hOtherInvariant := hInvariant.of_perm_input hPerm
      have hOther := stateInvariantCheck_complete _ _ hOtherInvariant
      exact hOther.symm

/-- 長さ 0 から各入力長までの接頭辞を列挙する。 -/
def prefixes (values : Array Nat) : List (Array Nat) :=
  (List.range (values.size + 1)).map fun length => values.extract 0 length

/-- 一つの入力列について、全接頭辞の状態不変条件を確認する。 -/
def inputCheck (values : Array Nat) : Bool :=
  (prefixes values).all fun partialInput =>
    let state := LeanExperiments.RunningMedian.ofArray partialInput
    stateInvariantCheck partialInput state

/-- 入力検査が成功すれば、各接頭辞の状態不変条件と中央値一致を命題として得る。 -/
theorem inputCheck_sound (values : Array Nat) (hCheck : inputCheck values = true) :
    ∀ partialInput ∈ prefixes values,
      StateInvariant partialInput (LeanExperiments.RunningMedian.ofArray partialInput) ∧
        LeanExperiments.RunningMedian.median
            (LeanExperiments.RunningMedian.ofArray partialInput) = medianSpec partialInput := by
  intro partialInput hPartial
  have hEach := (List.all_eq_true.mp hCheck) partialInput hPartial
  have hInvariant := stateInvariantCheck_sound _ _ hEach
  exact ⟨hInvariant,
    median_eq_medianSpec_of_invariant hInvariant⟩

/-- `inputCheck` の成否は、全接頭辞で状態不変条件が成り立つことと同値である。

この定理は Boolean 検査器が直接検査する条件だけを切り出し、中央値仕様との一致は
不変条件から導く別の正当性定理に委ねる。
-/
theorem inputCheck_invariants_iff (values : Array Nat) :
    inputCheck values = true ↔
      ∀ partialInput ∈ prefixes values,
        StateInvariant partialInput (LeanExperiments.RunningMedian.ofArray partialInput) := by
  constructor
  · intro hCheck partialInput hPartial
    exact (inputCheck_sound values hCheck partialInput hPartial).1
  · intro hEveryPrefix
    unfold inputCheck
    apply List.all_eq_true.mpr
    intro partialInput hPartial
    exact stateInvariantCheck_complete _ _ (hEveryPrefix partialInput hPartial)

/-- 2つ目が1つ目より大きい二要素入力では、全接頭辞の実装状態検査が成功する。 -/
theorem inputCheck_pair_of_lt {left right : Nat} (hLeft : left < right) :
    inputCheck #[left, right] = true := by
  apply (inputCheck_invariants_iff #[left, right]).mpr
  intro partialInput hPartial
  have hPrefixes : prefixes #[left, right] = [#[], #[left], #[left, right]] := by
    simp [prefixes, List.range, List.range.loop]
  rw [hPrefixes] at hPartial
  simp at hPartial
  rcases hPartial with rfl | rfl | rfl
  · rw [ofArray_empty]
    exact StateInvariant.empty
  · exact StateInvariant.ofArray_singleton left
  · exact StateInvariant.ofArray_pair_of_lt hLeft

/-- 任意の二値入力では、空・1要素・2要素の全接頭辞で状態検査が成功する。 -/
theorem inputCheck_pair (left right : Nat) : inputCheck #[left, right] = true := by
  apply (inputCheck_invariants_iff #[left, right]).mpr
  intro partialInput hPartial
  have hPrefixes : prefixes #[left, right] = [#[], #[left], #[left, right]] := by
    simp [prefixes, List.range, List.range.loop]
  rw [hPrefixes] at hPartial
  simp at hPartial
  rcases hPartial with rfl | rfl | rfl
  · rw [ofArray_empty]
    exact StateInvariant.empty
  · exact StateInvariant.ofArray_singleton left
  · exact StateInvariant.ofArray_pair left right

/-- 任意の3値入力では、全4接頭辞の状態不変条件とBoolean検査が成功する。-/
theorem inputCheck_triple (first second third : Nat) :
    inputCheck #[first, second, third] = true := by
  apply (inputCheck_invariants_iff #[first, second, third]).mpr
  intro partialInput hPartial
  have hPrefixes : prefixes #[first, second, third] =
      [#[], #[first], #[first, second], #[first, second, third]] := by
    simp [prefixes, List.range, List.range.loop]
  rw [hPrefixes] at hPartial
  simp at hPartial
  rcases hPartial with rfl | rfl | rfl | rfl
  · rw [ofArray_empty]
    exact StateInvariant.empty
  · exact StateInvariant.ofArray_singleton first
  · exact StateInvariant.ofArray_pair first second
  · exact StateInvariant.ofArray_triple first second third

/-- 任意の4値入力では、全5接頭辞の状態不変条件とBoolean検査が成功する。 -/
theorem inputCheck_quadruple (first second third fourth : Nat) :
    inputCheck #[first, second, third, fourth] = true := by
  apply (inputCheck_invariants_iff #[first, second, third, fourth]).mpr
  intro partialInput hPartial
  have hPrefixes : prefixes #[first, second, third, fourth] =
      [#[], #[first], #[first, second], #[first, second, third],
        #[first, second, third, fourth]] := by
    simp [prefixes, List.range, List.range.loop]
  rw [hPrefixes] at hPartial
  simp at hPartial
  rcases hPartial with rfl | rfl | rfl | rfl | rfl
  · rw [ofArray_empty]
    exact StateInvariant.empty
  · exact StateInvariant.ofArray_singleton first
  · exact StateInvariant.ofArray_pair first second
  · exact StateInvariant.ofArray_triple first second third
  · exact StateInvariant.ofArray_quadruple first second third fourth

/-- サイズ4の任意配列では、全5接頭辞の状態不変条件検査が成功する。 -/
theorem inputCheck_size_eq_four (values : Array Nat) (hSize : values.size = 4) :
    inputCheck values = true := by
  let first := values[0]!
  let second := values[1]!
  let third := values[2]!
  let fourth := values[3]!
  have hValues : values = #[first, second, third, fourth] := by
    apply Array.ext
    · simpa using hSize
    · intro index hIndex hBound
      have hCases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 := by omega
      rcases hCases with h | h | h | h <;> subst index
      · simpa [first] using (getElem!_pos values 0 (by omega)).symm
      · simpa [second] using (getElem!_pos values 1 (by omega)).symm
      · simpa [third] using (getElem!_pos values 2 (by omega)).symm
      · simpa [fourth] using (getElem!_pos values 3 (by omega)).symm
  rw [hValues]
  exact inputCheck_quadruple first second third fourth

/-- サイズ4以下の任意入力では、各接頭辞の状態検査が成功する。 -/
theorem inputCheck_size_le_four (values : Array Nat) (hSize : values.size ≤ 4) :
    inputCheck values = true := by
  apply (inputCheck_invariants_iff values).2
  intro partialInput hPartial
  have hPartialSize : partialInput.size ≤ values.size := by
    unfold prefixes at hPartial
    rcases List.mem_map.mp hPartial with ⟨length, hLength, hExtract⟩
    subst partialInput
    simp
    omega
  exact StateInvariant.ofArray_size_le_four partialInput (by omega)

/-- サイズ5以下の任意入力では、各接頭辞の状態検査が成功する。 -/
theorem inputCheck_size_le_five (values : Array Nat) (hSize : values.size ≤ 5) :
    inputCheck values = true := by
  apply (inputCheck_invariants_iff values).2
  intro partialInput hPartial
  have hPartialSize : partialInput.size ≤ values.size := by
    unfold prefixes at hPartial
    rcases List.mem_map.mp hPartial with ⟨length, hLength, hExtract⟩
    subst partialInput
    simp
    omega
  exact StateInvariant.ofArray_size_le_five partialInput (by omega)

/-- サイズ6以下の任意入力では、各接頭辞の状態検査が成功する。 -/
theorem inputCheck_size_le_six (values : Array Nat) (hSize : values.size ≤ 6) :
    inputCheck values = true := by
  apply (inputCheck_invariants_iff values).2
  intro partialInput hPartial
  have hPartialSize : partialInput.size ≤ values.size := by
    unfold prefixes at hPartial
    rcases List.mem_map.mp hPartial with ⟨length, hLength, hExtract⟩
    subst partialInput
    simp
    omega
  exact StateInvariant.ofArray_size_le_six partialInput (by omega)

/-- サイズ7以下の任意入力では、各接頭辞の状態検査が成功する。 -/
theorem inputCheck_size_le_seven (values : Array Nat) (hSize : values.size ≤ 7) :
    inputCheck values = true := by
  apply (inputCheck_invariants_iff values).2
  intro partialInput hPartial
  have hPartialSize : partialInput.size ≤ values.size := by
    unfold prefixes at hPartial
    rcases List.mem_map.mp hPartial with ⟨length, hLength, hExtract⟩
    subst partialInput
    simp
    omega
  exact StateInvariant.ofArray_size_le_seven partialInput (by omega)

/-- サイズ8以下の任意入力では、各接頭辞の状態検査が成功する。 -/
theorem inputCheck_size_le_eight (values : Array Nat) (hSize : values.size ≤ 8) :
    inputCheck values = true := by
  apply (inputCheck_invariants_iff values).2
  intro partialInput hPartial
  have hPartialSize : partialInput.size ≤ values.size := by
    unfold prefixes at hPartial
    rcases List.mem_map.mp hPartial with ⟨length, hLength, hExtract⟩
    subst partialInput
    simp
    omega
  exact StateInvariant.ofArray_size_le_eight partialInput (by omega)

/-- サイズ9以下の任意入力では、各接頭辞の状態検査が成功する。 -/
theorem inputCheck_size_le_nine (values : Array Nat) (hSize : values.size ≤ 9) :
    inputCheck values = true := by
  apply (inputCheck_invariants_iff values).2
  intro partialInput hPartial
  have hPartialSize : partialInput.size ≤ values.size := by
    unfold prefixes at hPartial
    rcases List.mem_map.mp hPartial with ⟨length, hLength, hExtract⟩
    subst partialInput
    simp
    omega
  exact StateInvariant.ofArray_size_le_nine partialInput (by omega)

/-- サイズ10以下の任意入力では、各接頭辞の状態検査が成功する。 -/
theorem inputCheck_size_le_ten (values : Array Nat) (hSize : values.size ≤ 10) :
    inputCheck values = true := by
  apply (inputCheck_invariants_iff values).2
  intro partialInput hPartial
  have hPartialSize : partialInput.size ≤ values.size := by
    unfold prefixes at hPartial
    rcases List.mem_map.mp hPartial with ⟨length, hLength, hExtract⟩
    subst partialInput
    simp
    omega
  exact StateInvariant.ofArray_size_le_ten partialInput (by omega)

/-- サイズ11以下の任意入力では、各接頭辞の状態検査が成功する。 -/
theorem inputCheck_size_le_eleven (values : Array Nat) (hSize : values.size ≤ 11) :
    inputCheck values = true := by
  apply (inputCheck_invariants_iff values).2
  intro partialInput hPartial
  have hPartialSize : partialInput.size ≤ values.size := by
    unfold prefixes at hPartial
    rcases List.mem_map.mp hPartial with ⟨length, hLength, hExtract⟩
    subst partialInput
    simp
    omega
  exact StateInvariant.ofArray_size_le_eleven partialInput (by omega)

/-- サイズ12以下の任意入力では、各接頭辞の状態検査が成功する。 -/
theorem inputCheck_size_le_twelve (values : Array Nat) (hSize : values.size ≤ 12) :
    inputCheck values = true := by
  apply (inputCheck_invariants_iff values).2
  intro partialInput hPartial
  have hPartialSize : partialInput.size ≤ values.size := by
    unfold prefixes at hPartial
    rcases List.mem_map.mp hPartial with ⟨length, hLength, hExtract⟩
    subst partialInput
    simp
    omega
  exact StateInvariant.ofArray_size_le_twelve partialInput (by omega)

/-- サイズ13以下の任意入力では、各接頭辞の状態検査が成功する。 -/
theorem inputCheck_size_le_thirteen (values : Array Nat) (hSize : values.size ≤ 13) :
    inputCheck values = true := by
  apply (inputCheck_invariants_iff values).2
  intro partialInput hPartial
  have hPartialSize : partialInput.size ≤ values.size := by
    unfold prefixes at hPartial
    rcases List.mem_map.mp hPartial with ⟨length, hLength, hExtract⟩
    subst partialInput
    simp
    omega
  exact StateInvariant.ofArray_size_le_thirteen partialInput (by omega)

/-- サイズ14以下の任意入力では、各接頭辞の状態検査が成功する。 -/
theorem inputCheck_size_le_fourteen (values : Array Nat) (hSize : values.size ≤ 14) :
    inputCheck values = true := by
  apply (inputCheck_invariants_iff values).2
  intro partialInput hPartial
  have hPartialSize : partialInput.size ≤ values.size := by
    unfold prefixes at hPartial
    rcases List.mem_map.mp hPartial with ⟨length, hLength, hExtract⟩
    subst partialInput
    simp
    omega
  exact StateInvariant.ofArray_size_le_fourteen partialInput (by omega)

/-- サイズ15以下の任意入力では、各接頭辞の状態検査が成功する。 -/
theorem inputCheck_size_le_fifteen (values : Array Nat) (hSize : values.size ≤ 15) :
    inputCheck values = true := by
  apply (inputCheck_invariants_iff values).2
  intro partialInput hPartial
  have hPartialSize : partialInput.size ≤ values.size := by
    unfold prefixes at hPartial
    rcases List.mem_map.mp hPartial with ⟨length, hLength, hExtract⟩
    subst partialInput
    simp
    omega
  exact StateInvariant.ofArray_size_le_fifteen partialInput (by omega)

/-- サイズ16以下の任意入力では、各接頭辞の状態検査が成功する。 -/
theorem inputCheck_size_le_sixteen (values : Array Nat) (hSize : values.size ≤ 16) :
    inputCheck values = true := by
  apply (inputCheck_invariants_iff values).2
  intro partialInput hPartial
  have hPartialSize : partialInput.size ≤ values.size := by
    unfold prefixes at hPartial
    rcases List.mem_map.mp hPartial with ⟨length, hLength, hExtract⟩
    subst partialInput
    simp
    omega
  exact StateInvariant.ofArray_size_le_sixteen partialInput (by omega)

/-- サイズ17以下の任意入力では、各接頭辞の状態検査が成功する。 -/
theorem inputCheck_size_le_seventeen (values : Array Nat) (hSize : values.size ≤ 17) :
    inputCheck values = true := by
  apply (inputCheck_invariants_iff values).2
  intro partialInput hPartial
  have hPartialSize : partialInput.size ≤ values.size := by
    unfold prefixes at hPartial
    rcases List.mem_map.mp hPartial with ⟨length, hLength, hExtract⟩
    subst partialInput
    simp
    omega
  exact StateInvariant.ofArray_size_le_seventeen partialInput (by omega)

/-- 任意の4値入力に対する公開中央値は、独立したソート仕様と一致する。 -/
theorem medianOf_quadruple (first second third fourth : Nat) :
    LeanExperiments.RunningMedian.medianOf #[first, second, third, fourth] =
      medianSpec #[first, second, third, fourth] :=
  medianOf_eq_medianSpec_of_invariant
    (StateInvariant.ofArray_quadruple first second third fourth)

/-- サイズ4の任意配列で、公開中央値は独立したソート仕様と一致する。 -/
theorem medianOf_eq_medianSpec_of_size_eq_four (values : Array Nat)
    (hSize : values.size = 4) :
    LeanExperiments.RunningMedian.medianOf values = medianSpec values :=
  medianOf_eq_medianSpec_of_invariant
    (StateInvariant.ofArray_size_eq_four values hSize)

/-- サイズ4以下の任意配列で、公開中央値は独立したソート仕様と一致する。 -/
theorem medianOf_eq_medianSpec_of_size_le_four (values : Array Nat)
    (hSize : values.size ≤ 4) :
    LeanExperiments.RunningMedian.medianOf values = medianSpec values :=
  medianOf_eq_medianSpec_of_invariant
    (StateInvariant.ofArray_size_le_four values hSize)

/-- サイズ5以下の任意配列で、公開中央値は独立したソート仕様と一致する。 -/
theorem medianOf_eq_medianSpec_of_size_le_five (values : Array Nat)
    (hSize : values.size ≤ 5) :
    LeanExperiments.RunningMedian.medianOf values = medianSpec values :=
  medianOf_eq_medianSpec_of_invariant
    (StateInvariant.ofArray_size_le_five values hSize)

/-- サイズ6以下の任意配列で、公開中央値は独立したソート仕様と一致する。 -/
theorem medianOf_eq_medianSpec_of_size_le_six (values : Array Nat)
    (hSize : values.size ≤ 6) :
    LeanExperiments.RunningMedian.medianOf values = medianSpec values :=
  medianOf_eq_medianSpec_of_invariant
    (StateInvariant.ofArray_size_le_six values hSize)

/-- サイズ7以下の任意配列で、公開中央値は独立したソート仕様と一致する。 -/
theorem medianOf_eq_medianSpec_of_size_le_seven (values : Array Nat)
    (hSize : values.size ≤ 7) :
    LeanExperiments.RunningMedian.medianOf values = medianSpec values :=
  medianOf_eq_medianSpec_of_invariant
    (StateInvariant.ofArray_size_le_seven values hSize)

/-- サイズ8以下の任意配列で、公開中央値は独立したソート仕様と一致する。 -/
theorem medianOf_eq_medianSpec_of_size_le_eight (values : Array Nat)
    (hSize : values.size ≤ 8) :
    LeanExperiments.RunningMedian.medianOf values = medianSpec values :=
  medianOf_eq_medianSpec_of_invariant
    (StateInvariant.ofArray_size_le_eight values hSize)

/-- サイズ9以下の任意配列で、公開中央値は独立したソート仕様と一致する。 -/
theorem medianOf_eq_medianSpec_of_size_le_nine (values : Array Nat)
    (hSize : values.size ≤ 9) :
    LeanExperiments.RunningMedian.medianOf values = medianSpec values :=
  medianOf_eq_medianSpec_of_invariant
    (StateInvariant.ofArray_size_le_nine values hSize)

/-- サイズ10以下の任意配列で、公開中央値は独立したソート仕様と一致する。 -/
theorem medianOf_eq_medianSpec_of_size_le_ten (values : Array Nat)
    (hSize : values.size ≤ 10) :
    LeanExperiments.RunningMedian.medianOf values = medianSpec values :=
  medianOf_eq_medianSpec_of_invariant
    (StateInvariant.ofArray_size_le_ten values hSize)

/-- サイズ11以下の任意配列で、公開中央値は独立したソート仕様と一致する。 -/
theorem medianOf_eq_medianSpec_of_size_le_eleven (values : Array Nat)
    (hSize : values.size ≤ 11) :
    LeanExperiments.RunningMedian.medianOf values = medianSpec values :=
  medianOf_eq_medianSpec_of_invariant
    (StateInvariant.ofArray_size_le_eleven values hSize)

/-- サイズ12以下の任意配列で、公開中央値は独立したソート仕様と一致する。 -/
theorem medianOf_eq_medianSpec_of_size_le_twelve (values : Array Nat)
    (hSize : values.size ≤ 12) :
    LeanExperiments.RunningMedian.medianOf values = medianSpec values :=
  medianOf_eq_medianSpec_of_invariant
    (StateInvariant.ofArray_size_le_twelve values hSize)

/-- サイズ13以下の任意配列で、公開中央値は独立したソート仕様と一致する。 -/
theorem medianOf_eq_medianSpec_of_size_le_thirteen (values : Array Nat)
    (hSize : values.size ≤ 13) :
    LeanExperiments.RunningMedian.medianOf values = medianSpec values :=
  medianOf_eq_medianSpec_of_invariant
    (StateInvariant.ofArray_size_le_thirteen values hSize)

/-- サイズ14以下の任意配列で、公開中央値は独立したソート仕様と一致する。 -/
theorem medianOf_eq_medianSpec_of_size_le_fourteen (values : Array Nat)
    (hSize : values.size ≤ 14) :
    LeanExperiments.RunningMedian.medianOf values = medianSpec values :=
  medianOf_eq_medianSpec_of_invariant
    (StateInvariant.ofArray_size_le_fourteen values hSize)

/-- サイズ15以下の任意配列で、公開中央値は独立したソート仕様と一致する。 -/
theorem medianOf_eq_medianSpec_of_size_le_fifteen (values : Array Nat)
    (hSize : values.size ≤ 15) :
    LeanExperiments.RunningMedian.medianOf values = medianSpec values :=
  medianOf_eq_medianSpec_of_invariant
    (StateInvariant.ofArray_size_le_fifteen values hSize)

/-- サイズ16以下の任意配列で、公開中央値は独立したソート仕様と一致する。 -/
theorem medianOf_eq_medianSpec_of_size_le_sixteen (values : Array Nat)
    (hSize : values.size ≤ 16) :
    LeanExperiments.RunningMedian.medianOf values = medianSpec values :=
  medianOf_eq_medianSpec_of_invariant
    (StateInvariant.ofArray_size_le_sixteen values hSize)

/-- サイズ17以下の任意配列で、公開中央値は独立したソート仕様と一致する。 -/
theorem medianOf_eq_medianSpec_of_size_le_seventeen (values : Array Nat)
    (hSize : values.size ≤ 17) :
    LeanExperiments.RunningMedian.medianOf values = medianSpec values :=
  medianOf_eq_medianSpec_of_invariant
    (StateInvariant.ofArray_size_le_seventeen values hSize)

/-- 任意長・任意値の入力について、公開中央値は独立したソート仕様と一致する。 -/
theorem medianOf_eq_medianSpec_arbitrary (values : Array Nat) :
    LeanExperiments.RunningMedian.medianOf values = medianSpec values :=
  medianOf_eq_medianSpec_of_invariant (StateInvariant.ofArray_arbitrary values)

/-- 入力全体に定数を足すと、公開中央値も分母に応じた量だけ移動する。 -/
theorem medianOf_add_const (values : Array Nat) (offset : Nat) :
    LeanExperiments.RunningMedian.medianOf (values.map fun value => value + offset) =
      (LeanExperiments.RunningMedian.medianOf values).map fun result =>
        (result.1 + offset * result.2, result.2) := by
  rw [medianOf_eq_medianSpec_arbitrary (values.map fun value => value + offset),
    medianOf_eq_medianSpec_arbitrary values]
  exact medianSpec_add_const values offset

/-- 全入力値を同じ自然数倍すると、公開中央値の分子も同じ倍数になる。 -/
theorem medianOf_mul_const (values : Array Nat) (factor : Nat) :
    LeanExperiments.RunningMedian.medianOf (values.map fun value => factor * value) =
      (LeanExperiments.RunningMedian.medianOf values).map fun result =>
        (result.1 * factor, result.2) := by
  rw [medianOf_eq_medianSpec_arbitrary (values.map fun value => factor * value),
    medianOf_eq_medianSpec_arbitrary values]
  exact medianSpec_mul_const values factor

/-- 全入力値へ同じ自然数の一次変換を適用したときの公開中央値を特徴付ける。

`x ↦ factor * x + offset` は順序を保ち、分母 `d` の中央値 `(n, d)` を
`(factor * n + offset * d, d)` へ移す。係数0・空入力を含む任意入力に適用できる。
-/
theorem medianOf_affine (values : Array Nat) (factor offset : Nat) :
    LeanExperiments.RunningMedian.medianOf
        (values.map fun value => factor * value + offset) =
      (LeanExperiments.RunningMedian.medianOf values).map fun result =>
        (result.1 * factor + offset * result.2, result.2) := by
  have hMap :
      ((values.map (fun value => factor * value)).map (fun value => value + offset)) =
        values.map (fun value => factor * value + offset) := by
    rw [Array.map_map]
    rfl
  calc
    LeanExperiments.RunningMedian.medianOf
        (values.map fun value => factor * value + offset) =
      LeanExperiments.RunningMedian.medianOf
        ((values.map fun value => factor * value).map fun value => value + offset) := by
          rw [hMap]
    _ = (LeanExperiments.RunningMedian.medianOf (values.map fun value => factor * value)).map
          fun result => (result.1 + offset * result.2, result.2) :=
        medianOf_add_const (values.map fun value => factor * value) offset
    _ = ((LeanExperiments.RunningMedian.medianOf values).map
          fun result => (result.1 * factor, result.2)).map
          fun result => (result.1 + offset * result.2, result.2) := by
        rw [medianOf_mul_const]
    _ = (LeanExperiments.RunningMedian.medianOf values).map fun result =>
          (result.1 * factor + offset * result.2, result.2) := by
        cases LeanExperiments.RunningMedian.medianOf values <;> simp

/-- 入力検査が成功すれば、公開中央値は独立したソート基準の仕様と一致する。 -/
theorem medianOf_eq_medianSpec_of_inputCheck (values : Array Nat)
    (hCheck : inputCheck values = true) :
    LeanExperiments.RunningMedian.medianOf values = medianSpec values := by
  have hFull : values ∈ prefixes values := by
    unfold prefixes
    apply List.mem_map.mpr
    refine ⟨values.size, List.mem_range.mpr (by omega), ?_⟩
    simp
  obtain ⟨_, hMedian⟩ := inputCheck_sound values hCheck values hFull
  simpa [LeanExperiments.RunningMedian.medianOf] using hMedian

/-- 検査に成功した二入力が同じ値の順列なら、逐次中央値の結果も等しい。

個々の入力で実装結果がソート基準の中央値と一致することと、基準中央値が順列に
依存しないことを組み合わせる。有限網羅領域の外でも、入力検査が成功した列に適用できる。
-/
theorem medianOf_eq_of_inputCheck {values₁ values₂ : Array Nat}
    (hCheck₁ : inputCheck values₁ = true)
    (hCheck₂ : inputCheck values₂ = true)
    (hPerm : values₁.toList.Perm values₂.toList) :
    LeanExperiments.RunningMedian.medianOf values₁ =
      LeanExperiments.RunningMedian.medianOf values₂ := by
  rw [medianOf_eq_medianSpec_of_inputCheck values₁ hCheck₁,
    medianOf_eq_medianSpec_of_inputCheck values₂ hCheck₂,
    medianSpec_eq_of_perm hPerm]

/-- 全接頭辞の不変条件と中央値一致が、入力全体のBoolean検査と同値である。 -/
theorem inputCheck_correct (values : Array Nat) :
    inputCheck values = true ↔
      ∀ partialInput ∈ prefixes values,
        StateInvariant partialInput (LeanExperiments.RunningMedian.ofArray partialInput) ∧
          LeanExperiments.RunningMedian.medianOf partialInput = medianSpec partialInput := by
  constructor
  · intro hCheck partialInput hPartial
    have hInvariant := (inputCheck_invariants_iff values).mp hCheck partialInput hPartial
    exact ⟨hInvariant, medianOf_eq_medianSpec_of_invariant hInvariant⟩
  · intro hEveryPrefix
    apply (inputCheck_invariants_iff values).mpr
    intro partialInput hPartial
    exact (hEveryPrefix partialInput hPartial).1

/-- 任意入力の全接頭辞で不変条件が成立するため、独立検査器は必ず成功する。 -/
theorem inputCheck_arbitrary (values : Array Nat) : inputCheck values = true := by
  apply (inputCheck_correct values).2
  intro partialInput hPartial
  exact ⟨StateInvariant.ofArray_arbitrary partialInput,
    medianOf_eq_medianSpec_arbitrary partialInput⟩

/-- 公開中央値は、任意の入力順列に対して同じ結果を返す。 -/
theorem medianOf_eq_of_perm {values₁ values₂ : Array Nat}
    (hPerm : values₁.toList.Perm values₂.toList) :
    LeanExperiments.RunningMedian.medianOf values₁ =
      LeanExperiments.RunningMedian.medianOf values₂ := by
  exact medianOf_eq_of_inputCheck (inputCheck_arbitrary values₁)
    (inputCheck_arbitrary values₂) hPerm

/-- 指定値集合から長さ `length` の全配列を作る。 -/
def arraysOfLengthOver (alphabet : List Nat) : Nat → List (Array Nat)
  | 0 => [#[]]
  | length + 1 =>
      (arraysOfLengthOver alphabet length).flatMap fun partialInput =>
        alphabet.map fun value => partialInput.push value

/-- 値0〜3から長さ `length` の全配列を作る。 -/
def arraysOfLength : Nat → List (Array Nat) :=
  arraysOfLengthOver [0, 1, 2, 3]

/-- 値0〜3、長さ0〜8の全87381入力を確認する。 -/
def boundedInputs : List (Array Nat) :=
  (List.range 9).flatMap arraysOfLength

/-- 各入力の全接頭辞について、ヒープ条件と中央値仕様が成立する。 -/
def boundedInputsCheck : Bool := boundedInputs.all inputCheck

/-- 値0〜3、長さ0〜8の全87,381配列で逐次中央値検証が通る。 -/
theorem boundedInputsCheck_passes : boundedInputsCheck = true := by
  native_decide

/-- 87381件の有限領域にある任意の入力について、全接頭辞の論理的不変条件と
中央値仕様との一致を取り出せる。 -/
theorem boundedInput_invariants (values : Array Nat)
    (hValues : values ∈ boundedInputs) :
    ∀ partialInput ∈ prefixes values,
      StateInvariant partialInput (LeanExperiments.RunningMedian.ofArray partialInput) ∧
        LeanExperiments.RunningMedian.median
            (LeanExperiments.RunningMedian.ofArray partialInput) = medianSpec partialInput := by
  have hAll : ∀ candidate ∈ boundedInputs, inputCheck candidate = true :=
    List.all_eq_true.mp boundedInputsCheck_passes
  exact inputCheck_sound values (hAll values hValues)

/-! ## 大きな値を含む全列挙確認

比較対象の桁が大きく異なる場合や最大64 bit値の重複も含め、全入力の全接頭辞で
二つのヒープの不変条件と中央値仕様を確認する。 -/

/-- 5種類の値から作る長さ0〜7の全97656配列。 -/
def wideValueInputs : List (Array Nat) :=
  (List.range 8).flatMap fun length =>
    arraysOfLengthOver [0, 1, 2, 4294967296, 18446744073709551615] length

/-- 大きな値を含む97656入力の全接頭辞で、ヒープ条件と中央値仕様を確認する。 -/
def wideValueInputsCheck : Bool := wideValueInputs.all inputCheck

/-- 大きな値を含む97656入力の全接頭辞で逐次中央値の検証が通る。 -/
theorem wideValueInputsCheck_passes : wideValueInputsCheck = true := by
  native_decide

/-- 97656件の大きな値領域にある任意の入力について、全接頭辞の論理的不変条件と
中央値仕様との一致を取り出せる。 -/
theorem wideValueInput_invariants (values : Array Nat)
    (hValues : values ∈ wideValueInputs) :
    ∀ partialInput ∈ prefixes values,
      StateInvariant partialInput (LeanExperiments.RunningMedian.ofArray partialInput) ∧
        LeanExperiments.RunningMedian.median
            (LeanExperiments.RunningMedian.ofArray partialInput) = medianSpec partialInput := by
  have hAll : ∀ candidate ∈ wideValueInputs, inputCheck candidate = true :=
    List.all_eq_true.mp wideValueInputsCheck_passes
  exact inputCheck_sound values (hAll values hValues)

/-- 空入力には中央値がない。 -/
theorem medianOf_empty : LeanExperiments.RunningMedian.medianOf #[] = none := by
  rw [medianOf_eq_medianSpec_of_invariant (by
    rw [ofArray_empty]
    exact StateInvariant.empty)]
  simp [medianSpec, LeanExperiments.Verification.MergeSort.mergeSort_empty]

/-- 任意の1要素入力では、公開関数 `medianOf` はその唯一の値を分母1で返す。 -/
theorem medianOf_singleton (value : Nat) :
    LeanExperiments.RunningMedian.medianOf #[value] = some (value, 1) := by
  rw [medianOf_eq_medianSpec_of_invariant (StateInvariant.ofArray_singleton value)]
  exact medianSpec_singleton value

/-- 長さ0または1の配列では、公開関数は空結果か唯一の要素を返す。

長さの上限を明示した定理であり、配列の値自体には上限を置かない。
-/
theorem bounded_medianOf_size_le_one (values : Array Nat)
    (hSize : values.size ≤ 1) :
    LeanExperiments.RunningMedian.medianOf values =
      if values.size = 0 then none else some (values[0]!, 1) := by
  have hListLength : values.toList.length ≤ 1 := by simpa using hSize
  cases hList : values.toList with
  | nil =>
      have hValues : values = #[] := Array.toList_inj.mp hList
      simp [hValues, medianOf_empty]
  | cons value rest =>
      have hRest : rest = [] := by
        have hLength : (value :: rest).length ≤ 1 := by simpa [hList] using hListLength
        simp at hLength
        omega
      have hValues : values = #[value] := by
        apply Array.toList_inj.mp
        simp [hList, hRest]
      subst values
      simp [medianOf_singleton]

/-- 奇数個の入力では中央の値をそのまま返す。 -/
theorem medianOf_odd_example :
    LeanExperiments.RunningMedian.medianOf #[9, 1, 4, 2, 7] = some (4, 1) := by
  native_decide

/-- 偶数個の入力では中央二値の平均を分母2の有理値として返す。 -/
theorem medianOf_even_example :
    LeanExperiments.RunningMedian.medianOf #[9, 1, 4, 2] = some (6, 2) := by
  native_decide

/-- 重複を含む偶数長入力でも、同じ値を正しく数えて中央値を求める。 -/
theorem medianOf_duplicates_example :
    LeanExperiments.RunningMedian.medianOf #[5, 2, 2, 9, 2, 5] = some (7, 2) := by
  native_decide

/-- 長い単調列、同値列、交互列、および大きな境界値の列。 -/
def adversarialInputs : List (Array Nat) :=
  [Array.range 64, (Array.range 64).reverse, Array.replicate 64 7,
    (Array.range 64).map fun index => index % 2,
    Array.replicate 64 18446744073709551615,
    (Array.range 64).map fun index =>
      if index % 2 == 0 then 18446744073709551615 else 0]

/-- 代表的な長さ64の入力パターン全てで逐次検証が通る。 -/
theorem adversarialInputsCheck_passes :
    adversarialInputs.all inputCheck = true := by
  native_decide

/-- 二分ヒープの階層数が変化する境目の長さで使う入力。 -/
def heapBoundaryInputs : List (Array Nat) :=
  [63, 64, 65, 127, 128, 129, 255, 256, 257, 511, 512, 513].flatMap fun length =>
    [Array.range length,
      (Array.range length).reverse,
      (Array.range length).map fun index =>
        if index % 2 == 0 then 18446744073709551615 else 0]

/-- 長さ63/64/65、127/128/129、255/256/257、511/512/513の各列について全接頭辞の検証が通る。 -/
theorem heapBoundaryInputsCheck_passes :
    heapBoundaryInputs.all inputCheck = true := by
  native_decide

/-- 境界長の有限領域に属する入力について、全接頭辞の不変条件と中央値一致を取り出す。 -/
theorem heapBoundaryInput_invariants (values : Array Nat)
    (hValues : values ∈ heapBoundaryInputs) :
    ∀ partialInput ∈ prefixes values,
      StateInvariant partialInput (LeanExperiments.RunningMedian.ofArray partialInput) ∧
        LeanExperiments.RunningMedian.median
            (LeanExperiments.RunningMedian.ofArray partialInput) = medianSpec partialInput := by
  have hAll : ∀ candidate ∈ heapBoundaryInputs, inputCheck candidate = true :=
    List.all_eq_true.mp heapBoundaryInputsCheck_passes
  exact inputCheck_sound values (hAll values hValues)

end LeanExperiments.Verification.RunningMedian
