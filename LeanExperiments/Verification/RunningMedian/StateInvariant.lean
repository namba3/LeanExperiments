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

/-!
# 逐次中央値の状態不変条件

状態判定器と論理的不変条件、その構造・分割・サイズに関する基礎補題をまとめる。
-/

namespace LeanExperiments.Verification.RunningMedian

open Std.WP Lean.Order
set_option experimental.vcgen true

/-- 状態が二つのヒープの構造・境界・サイズ・要素保存条件を満たすか判定する。 -/
def stateInvariantCheck (input : Array Nat)
    (state : LeanExperiments.RunningMedian.State) : Bool :=
  decide ((state.lower.toList ++ state.upper.toList).Perm input.toList) &&
    heapCheck maxPrefer state.lower &&
    heapCheck minPrefer state.upper &&
    state.lower.all (fun lowerValue =>
      state.upper.all (fun upperValue => decide (lowerValue ≤ upperValue))) &&
    (state.lower.size == state.upper.size ||
      state.lower.size == state.upper.size + 1)

/-- 逐次中央値状態の論理的不変条件。二つのヒープが入力を分割し、全ての値の
境界が保たれ、下側の要素数が同じか一つ多いことを表す。 -/
def StateInvariant (input : Array Nat)
    (state : LeanExperiments.RunningMedian.State) : Prop :=
  (state.lower.toList ++ state.upper.toList).Perm input.toList ∧
    HeapOrdered maxPrefer state.lower ∧
    HeapOrdered minPrefer state.upper ∧
    (∀ lowerIndex (hLowerIndex : lowerIndex < state.lower.size),
      ∀ upperIndex (hUpperIndex : upperIndex < state.upper.size),
        state.lower[lowerIndex]'hLowerIndex ≤ state.upper[upperIndex]'hUpperIndex) ∧
    (state.lower.size = state.upper.size ∨
      state.lower.size = state.upper.size + 1)

/-- 状態不変条件を満たす状態には、サイズ再平衡を適用しても変化しない。 -/
theorem StateInvariant.rebalanceLoops_eq_self {input : Array Nat}
    (state : LeanExperiments.RunningMedian.State)
    (hInvariant : StateInvariant input state) :
    let balanced := LeanExperiments.RunningMedian.rebalanceLower state.lower state.upper
    LeanExperiments.RunningMedian.rebalanceUpper balanced.1 balanced.2 =
      (state.lower, state.upper) := by
  exact rebalanceLoops_eq_self_of_balanced_size state.lower state.upper
    hInvariant.2.2.2.2

/-- 新しい値が全ての下側要素以上なら、上側へのヒープ挿入後も分割境界を保つ。 -/
theorem crossBoundary_insertUpper (state : LeanExperiments.RunningMedian.State)
    (value : Nat)
    (hBoundary : ∀ lowerIndex (hLowerIndex : lowerIndex < state.lower.size),
      ∀ upperIndex (hUpperIndex : upperIndex < state.upper.size),
        state.lower[lowerIndex]'hLowerIndex ≤ state.upper[upperIndex]'hUpperIndex)
    (hValue : ∀ lowerIndex (hLowerIndex : lowerIndex < state.lower.size),
      state.lower[lowerIndex]'hLowerIndex ≤ value) :
    ∀ lowerIndex (hLowerIndex : lowerIndex < state.lower.size),
      ∀ upperIndex (hUpperIndex : upperIndex <
        (LeanExperiments.RunningMedian.insertHeap minPrefer state.upper value).size),
        state.lower[lowerIndex]'hLowerIndex ≤
          (LeanExperiments.RunningMedian.insertHeap minPrefer state.upper value)[upperIndex]'hUpperIndex := by
  intro lowerIndex hLowerIndex upperIndex hUpperIndex
  apply insertHeap_ge_of_forall_ge minPrefer state.upper value
  · intro item hItem
    have hItemArray : item ∈ state.upper := by simpa using hItem
    obtain ⟨index, hIndex, hAt⟩ := Array.mem_iff_getElem.mp hItemArray
    have hPair := hBoundary lowerIndex hLowerIndex index hIndex
    simpa [hAt] using hPair
  · exact hValue lowerIndex hLowerIndex
  · exact Array.getElem_mem_toList hUpperIndex

/-- 新しい値が全ての上側要素以下なら、下側へのヒープ挿入後も分割境界を保つ。 -/
theorem crossBoundary_insertLower (state : LeanExperiments.RunningMedian.State)
    (value : Nat)
    (hBoundary : ∀ lowerIndex (hLowerIndex : lowerIndex < state.lower.size),
      ∀ upperIndex (hUpperIndex : upperIndex < state.upper.size),
        state.lower[lowerIndex]'hLowerIndex ≤ state.upper[upperIndex]'hUpperIndex)
    (hValue : ∀ upperIndex (hUpperIndex : upperIndex < state.upper.size),
      value ≤ state.upper[upperIndex]'hUpperIndex) :
    ∀ lowerIndex (hLowerIndex : lowerIndex <
      (LeanExperiments.RunningMedian.insertHeap maxPrefer state.lower value).size),
      ∀ upperIndex (hUpperIndex : upperIndex < state.upper.size),
        (LeanExperiments.RunningMedian.insertHeap maxPrefer state.lower value)[lowerIndex]'hLowerIndex ≤
          state.upper[upperIndex]'hUpperIndex := by
  intro lowerIndex hLowerIndex upperIndex hUpperIndex
  apply insertHeap_le_of_forall_le maxPrefer state.lower value
  · intro item hItem
    have hItemArray : item ∈ state.lower := by simpa using hItem
    obtain ⟨index, hIndex, hAt⟩ := Array.mem_iff_getElem.mp hItemArray
    have hPair := hBoundary index hIndex upperIndex hUpperIndex
    simpa [hAt] using hPair
  · exact hValue upperIndex hUpperIndex
  · exact Array.getElem_mem_toList hLowerIndex

/-- 下側最大値より大きい値を上側へ送る分岐では、挿入後も分割境界を保つ。 -/
theorem crossBoundary_insertUpper_of_gt_lowerRoot
    (state : LeanExperiments.RunningMedian.State) (value : Nat)
    (hLower : 0 < state.lower.size)
    (hLowerHeap : HeapOrdered maxPrefer state.lower)
    (hBoundary : ∀ lowerIndex (hLowerIndex : lowerIndex < state.lower.size),
      ∀ upperIndex (hUpperIndex : upperIndex < state.upper.size),
        state.lower[lowerIndex]'hLowerIndex ≤ state.upper[upperIndex]'hUpperIndex)
    (hValue : state.lower[0]! < value) :
    ∀ lowerIndex (hLowerIndex : lowerIndex < state.lower.size),
      ∀ upperIndex (hUpperIndex : upperIndex <
        (LeanExperiments.RunningMedian.insertHeap minPrefer state.upper value).size),
        state.lower[lowerIndex]'hLowerIndex ≤
          (LeanExperiments.RunningMedian.insertHeap minPrefer state.upper value)[upperIndex]'hUpperIndex := by
  apply crossBoundary_insertUpper state value hBoundary
  intro lowerIndex hLowerIndex
  have hMax := maxHeap_root_is_maximum state.lower hLowerHeap lowerIndex hLowerIndex
  have hMax' : state.lower[lowerIndex]'hLowerIndex ≤ state.lower[0]! := by
    simpa only [getElem!_pos state.lower lowerIndex hLowerIndex,
      getElem!_pos state.lower 0 hLower] using hMax
  omega

/-- 下側最大値以下の値を下側へ送る分岐では、挿入後も分割境界を保つ。 -/
theorem crossBoundary_insertLower_of_le_lowerRoot
    (state : LeanExperiments.RunningMedian.State) (value : Nat)
    (hLower : 0 < state.lower.size)
    (hBoundary : ∀ lowerIndex (hLowerIndex : lowerIndex < state.lower.size),
      ∀ upperIndex (hUpperIndex : upperIndex < state.upper.size),
        state.lower[lowerIndex]'hLowerIndex ≤ state.upper[upperIndex]'hUpperIndex)
    (hValue : value ≤ state.lower[0]!) :
    ∀ lowerIndex (hLowerIndex : lowerIndex <
      (LeanExperiments.RunningMedian.insertHeap maxPrefer state.lower value).size),
      ∀ upperIndex (hUpperIndex : upperIndex < state.upper.size),
        (LeanExperiments.RunningMedian.insertHeap maxPrefer state.lower value)[lowerIndex]'hLowerIndex ≤
          state.upper[upperIndex]'hUpperIndex := by
  apply crossBoundary_insertLower state value hBoundary
  intro upperIndex hUpperIndex
  have hRootBoundary := hBoundary 0 hLower upperIndex hUpperIndex
  calc
    value ≤ state.lower[0]! := hValue
    _ ≤ state.upper[upperIndex]'hUpperIndex := by
      simpa only [getElem!_pos state.lower 0 hLower] using hRootBoundary

/-- 実装の根比較で振り分けた挿入は、再平衡前のヒープ間境界を保つ。 -/
theorem crossBoundary_insertRouted
    (state : LeanExperiments.RunningMedian.State) (value : Nat)
    (hLower : 0 < state.lower.size)
    (hLowerHeap : HeapOrdered maxPrefer state.lower)
    (hBoundary : ∀ lowerIndex (hLowerIndex : lowerIndex < state.lower.size),
      ∀ upperIndex (hUpperIndex : upperIndex < state.upper.size),
        state.lower[lowerIndex]'hLowerIndex ≤ state.upper[upperIndex]'hUpperIndex) :
    (value ≤ state.lower[0]! →
      ∀ lowerIndex (hLowerIndex : lowerIndex <
        (LeanExperiments.RunningMedian.insertHeap maxPrefer state.lower value).size),
        ∀ upperIndex (hUpperIndex : upperIndex < state.upper.size),
          (LeanExperiments.RunningMedian.insertHeap maxPrefer state.lower value)[lowerIndex]'hLowerIndex ≤
            state.upper[upperIndex]'hUpperIndex) ∧
    (state.lower[0]! < value →
      ∀ lowerIndex (hLowerIndex : lowerIndex < state.lower.size),
        ∀ upperIndex (hUpperIndex : upperIndex <
          (LeanExperiments.RunningMedian.insertHeap minPrefer state.upper value).size),
          state.lower[lowerIndex]'hLowerIndex ≤
            (LeanExperiments.RunningMedian.insertHeap minPrefer state.upper value)[upperIndex]'hUpperIndex) := by
  constructor
  · intro hRoute
    exact crossBoundary_insertLower_of_le_lowerRoot state value hLower hBoundary hRoute
  · intro hGreater
    exact crossBoundary_insertUpper_of_gt_lowerRoot state value hLower hLowerHeap
      hBoundary hGreater

/-- 不変条件を満たす状態では、空の場合も含めて実装の値振り分け後に境界が保たれる。

下側ヒープが空ならサイズ均衡条件から上側も空なので、値を下側へ入れた後の境界は
空虚に成立する。非空なら、実装と同じ根比較に応じて既存の2つの分岐契約を適用する。
-/
theorem crossBoundary_after_routed_insert {input : Array Nat}
    (state : LeanExperiments.RunningMedian.State)
    (hInvariant : StateInvariant input state) (value : Nat) :
    (if state.lower.isEmpty then
      ∀ lowerIndex (hLowerIndex : lowerIndex <
        (LeanExperiments.RunningMedian.insertHeap maxPrefer state.lower value).size),
        ∀ upperIndex (hUpperIndex : upperIndex < state.upper.size),
          (LeanExperiments.RunningMedian.insertHeap maxPrefer state.lower value)[lowerIndex]'hLowerIndex ≤
            state.upper[upperIndex]'hUpperIndex
    else if value ≤ state.lower[0]! then
      ∀ lowerIndex (hLowerIndex : lowerIndex <
        (LeanExperiments.RunningMedian.insertHeap maxPrefer state.lower value).size),
        ∀ upperIndex (hUpperIndex : upperIndex < state.upper.size),
          (LeanExperiments.RunningMedian.insertHeap maxPrefer state.lower value)[lowerIndex]'hLowerIndex ≤
            state.upper[upperIndex]'hUpperIndex
    else
      ∀ lowerIndex (hLowerIndex : lowerIndex < state.lower.size),
        ∀ upperIndex (hUpperIndex : upperIndex <
          (LeanExperiments.RunningMedian.insertHeap minPrefer state.upper value).size),
          state.lower[lowerIndex]'hLowerIndex ≤
            (LeanExperiments.RunningMedian.insertHeap minPrefer state.upper value)[upperIndex]'hUpperIndex) := by
  by_cases hEmpty : state.lower.isEmpty = true
  · have hLowerSize : state.lower.size = 0 := by
      simpa [Array.isEmpty] using hEmpty
    have hUpperSize : state.upper.size = 0 := by
      rcases hInvariant.2.2.2.2 with hBalanced | hLowerExtra <;> omega
    have hUpperEmpty : state.upper = #[] := Array.size_eq_zero_iff.mp hUpperSize
    simp [hEmpty, hUpperEmpty]
  · have hNonempty : ¬ state.lower.isEmpty := by simpa using hEmpty
    have hLowerArrayNe : state.lower ≠ #[] := by
      intro hArray
      apply hNonempty
      simp [hArray]
    have hLower : 0 < state.lower.size := Array.size_pos_iff.mpr hLowerArrayNe
    have hRootEq : state.lower[0]! = state.lower[0]'hLower :=
      getElem!_pos state.lower 0 hLower
    have hBoundary := hInvariant.2.2.2.1
    by_cases hRoute : value ≤ state.lower[0]'hLower
    · have hRouteBang : value ≤ state.lower[0]! := by
        simpa [hRootEq] using hRoute
      simpa [hEmpty, hRootEq, hRoute] using
        (crossBoundary_insertLower_of_le_lowerRoot state value hLower hBoundary hRouteBang)
    · have hGreater : state.lower[0]! < value := by omega
      simpa [hEmpty, hRootEq, hRoute] using
        (crossBoundary_insertUpper_of_gt_lowerRoot state value hLower hInvariant.2.1
          hBoundary hGreater)

/-- 下側最大根を上側へ移す操作は、任意長の順序付きヒープ間境界を保つ。

取り出し後の下側要素は移動根以下であり、移動根は新しい上側ヒープへ追加される。
残った上側要素との境界は元の境界から従う。
-/
theorem transferLowerRoot_preserves_crossBoundary
    {lower upper nextLower nextUpper : Array Nat}
    (hLower : HeapOrdered LeanExperiments.RunningMedian.maxPrefer lower)
    (_hUpper : HeapOrdered LeanExperiments.RunningMedian.minPrefer upper)
    (hBoundary : ∀ i (hi : i < lower.size) j (hj : j < upper.size),
      lower[i]'hi ≤ upper[j]'hj)
    (hMove : LeanExperiments.RunningMedian.transferLowerRoot
      LeanExperiments.RunningMedian.maxPrefer LeanExperiments.RunningMedian.minPrefer
      lower upper = some (nextLower, nextUpper)) :
    ∀ i (hi : i < nextLower.size) j (hj : j < nextUpper.size),
      nextLower[i]'hi ≤ nextUpper[j]'hj := by
  unfold LeanExperiments.RunningMedian.transferLowerRoot at hMove
  cases hPop : LeanExperiments.RunningMedian.popHeap
      LeanExperiments.RunningMedian.maxPrefer lower with
  | none => simp [hPop] at hMove
  | some pair =>
    rcases pair with ⟨root, rest⟩
    have hResult : rest = nextLower ∧
        LeanExperiments.RunningMedian.insertHeap
          LeanExperiments.RunningMedian.minPrefer upper root = nextUpper := by
      simpa [hPop] using hMove
    rcases hResult with ⟨hRestEq, hInsertedEq⟩
    subst nextLower
    subst nextUpper
    have hRoot := popHeap_value_eq_root hPop
    have hPositive : 0 < lower.size := (Array.getElem?_eq_some_iff.mp hRoot).1
    have hRootValue : lower[0]'hPositive = root := by
      rw [getElem?_pos lower 0 hPositive] at hRoot
      have hEq := Option.some.inj hRoot
      exact hEq
    have hRestBound : ∀ x, x ∈ rest.toList → x ≤ root := by
      intro x hx
      have hInLower := List.mem_of_mem_drop
        ((popHeap_perm_dropRoot hPop).mem_iff.mp hx)
      obtain ⟨k, hk, hAt⟩ := List.mem_iff_getElem.mp hInLower
      have hMax := maxHeap_root_is_maximum lower hLower k hk
      have hMaxArray : lower[k]'hk ≤ lower[0]'hPositive := by
        simpa only [getElem!_pos lower k hk, getElem!_pos lower 0 hPositive] using hMax
      have hAtArray : lower[k]'hk = x := by simpa using hAt
      have hRootArray : lower[0]'hPositive = root := by
        simpa only [getElem!_pos lower 0 hPositive] using hRootValue
      omega
    intro i hi j hj
    have hRestMem : rest[i]'hi ∈ rest.toList := by simp
    have hLowerMem : rest[i]'hi ∈ lower.toList :=
      List.mem_of_mem_drop ((popHeap_perm_dropRoot hPop).mem_iff.mp hRestMem)
    have hInsertedPerm := insertHeap_perm LeanExperiments.RunningMedian.minPrefer upper root
    have hUpperMem := hInsertedPerm.mem_iff.mp (Array.getElem_mem_toList hj)
    simp only [List.mem_append, List.mem_singleton] at hUpperMem
    rcases hUpperMem with hOldUpper | hMovedRoot
    · obtain ⟨k, hk, hAt⟩ := List.mem_iff_getElem.mp hLowerMem
      obtain ⟨l, hl, hUpperAt⟩ := List.mem_iff_getElem.mp hOldUpper
      have hPair := hBoundary k hk l hl
      have hAtArray : lower[k]'hk = rest[i]'hi := by simpa using hAt
      have hUpperArray : upper[l]'hl =
          (LeanExperiments.RunningMedian.insertHeap
            LeanExperiments.RunningMedian.minPrefer upper root)[j]'hj := by simpa using hUpperAt
      simpa [hAtArray, hUpperArray] using hPair
    · have hLeRoot := hRestBound _ (Array.getElem_mem_toList hi)
      have hItemEq :
          (LeanExperiments.RunningMedian.insertHeap
            LeanExperiments.RunningMedian.minPrefer upper root)[j]'hj = root := by
        simpa using hMovedRoot
      simpa [hItemEq] using hLeRoot

/-- 上側最小根を下側へ移す操作も、任意長の順序付きヒープ間境界を保つ。 -/
theorem transferUpperRoot_preserves_crossBoundary
    {lower upper nextLower nextUpper : Array Nat}
    (_hLower : HeapOrdered LeanExperiments.RunningMedian.maxPrefer lower)
    (hUpper : HeapOrdered LeanExperiments.RunningMedian.minPrefer upper)
    (hBoundary : ∀ i (hi : i < lower.size) j (hj : j < upper.size),
      lower[i]'hi ≤ upper[j]'hj)
    (hMove : LeanExperiments.RunningMedian.transferUpperRoot
      LeanExperiments.RunningMedian.minPrefer LeanExperiments.RunningMedian.maxPrefer
      lower upper = some (nextLower, nextUpper)) :
    ∀ i (hi : i < nextLower.size) j (hj : j < nextUpper.size),
      nextLower[i]'hi ≤ nextUpper[j]'hj := by
  unfold LeanExperiments.RunningMedian.transferUpperRoot at hMove
  cases hPop : LeanExperiments.RunningMedian.popHeap
      LeanExperiments.RunningMedian.minPrefer upper with
  | none => simp [hPop] at hMove
  | some pair =>
    rcases pair with ⟨root, rest⟩
    have hResult : LeanExperiments.RunningMedian.insertHeap
          LeanExperiments.RunningMedian.maxPrefer lower root = nextLower ∧
        rest = nextUpper := by
      simpa [hPop] using hMove
    rcases hResult with ⟨hInsertedEq, hRestEq⟩
    subst nextLower
    subst nextUpper
    intro i hi j hj
    have hInsertedPerm := insertHeap_perm LeanExperiments.RunningMedian.maxPrefer lower root
    have hLowerMem := hInsertedPerm.mem_iff.mp (Array.getElem_mem_toList hi)
    simp only [List.mem_append, List.mem_singleton] at hLowerMem
    have hRestMem : rest[j]'hj ∈ rest.toList := by simp
    have hUpperMem : rest[j]'hj ∈ upper.toList :=
      List.mem_of_mem_drop ((popHeap_perm_dropRoot hPop).mem_iff.mp hRestMem)
    rcases hLowerMem with hOldLower | hMovedRoot
    · obtain ⟨k, hk, hAt⟩ := List.mem_iff_getElem.mp hOldLower
      obtain ⟨l, hl, hUpperAt⟩ := List.mem_iff_getElem.mp hUpperMem
      have hPair := hBoundary k hk l hl
      have hAtArray : lower[k]'hk =
          (LeanExperiments.RunningMedian.insertHeap
            LeanExperiments.RunningMedian.maxPrefer lower root)[i]'hi := by simpa using hAt
      have hUpperArray : upper[l]'hl = rest[j]'hj := by simpa using hUpperAt
      simpa [hAtArray, hUpperArray] using hPair
    · have hMinimum : ∀ k (hk : k < upper.size), root ≤ upper[k]'hk := by
        intro k hk
        have hMinimumBang := popHeap_minPrefer_returns_minimum hUpper hPop k hk
        simpa only [getElem!_pos upper k hk] using hMinimumBang
      have hRestMinimum : ∀ x, x ∈ rest.toList → root ≤ x := by
        intro x hx
        have hInOriginal := List.mem_of_mem_drop
          ((popHeap_perm_dropRoot hPop).mem_iff.mp hx)
        obtain ⟨k, hk, hAt⟩ := List.mem_iff_getElem.mp hInOriginal
        have hLe := hMinimum k hk
        have hAtArray : upper[k]'hk = x := by simpa using hAt
        simpa [hAtArray] using hLe
      have hItemEq :
          (LeanExperiments.RunningMedian.insertHeap
            LeanExperiments.RunningMedian.maxPrefer lower root)[i]'hi = root := by
        simpa using hMovedRoot
      have hRootRest : root ≤ rest[j]'hj :=
        hRestMinimum _ (Array.getElem_mem_toList hj)
      simpa [hItemEq] using hRootRest

/-- 最大根を上側へ移しても、両ヒープの順序は任意長で保たれる。 -/
theorem transferLowerRoot_preserves_heapOrders
    {lower upper nextLower nextUpper : Array Nat}
    (hLower : HeapOrdered LeanExperiments.RunningMedian.maxPrefer lower)
    (hUpper : HeapOrdered LeanExperiments.RunningMedian.minPrefer upper)
    (hMove : LeanExperiments.RunningMedian.transferLowerRoot
      LeanExperiments.RunningMedian.maxPrefer LeanExperiments.RunningMedian.minPrefer
      lower upper = some (nextLower, nextUpper)) :
    HeapOrdered LeanExperiments.RunningMedian.maxPrefer nextLower ∧
      HeapOrdered LeanExperiments.RunningMedian.minPrefer nextUpper := by
  unfold LeanExperiments.RunningMedian.transferLowerRoot at hMove
  cases hPop : LeanExperiments.RunningMedian.popHeap
      LeanExperiments.RunningMedian.maxPrefer lower with
  | none => simp [hPop] at hMove
  | some pair =>
    rcases pair with ⟨root, rest⟩
    have hResult : rest = nextLower ∧
        LeanExperiments.RunningMedian.insertHeap
          LeanExperiments.RunningMedian.minPrefer upper root = nextUpper := by
      simpa [hPop] using hMove
    rcases hResult with ⟨hRestEq, hInsertedEq⟩
    subst nextLower
    subst nextUpper
    have hPreferEq : maxPrefer = LeanExperiments.RunningMedian.maxPrefer := by
      funext candidate current
      rfl
    have hPopLocal : LeanExperiments.RunningMedian.popHeap maxPrefer lower =
        some (root, rest) := by
      simpa only [hPreferEq] using hPop
    have hPopCorrect := popHeap_maxPrefer_restCorrect_of_heapOrdered lower hLower
    have hPopSpec :
        0 < lower.size ∧ lower[0]? = some root ∧
          LeanExperiments.Verification.HeapSort.Spec.MaxHeap rest ∧
          rest.toList.Perm (lower.toList.drop 1) := by
      simpa [LeanExperiments.Verification.HeapSort.Spec.PopMaxRestCorrectFor, hPopLocal]
        using hPopCorrect
    have hRestOrdered :=
      (heapSortMaxHeap_iff_HeapOrdered_maxPrefer rest).mp hPopSpec.2.2.1
    exact ⟨hRestOrdered, insertHeap_minPrefer_preserves upper hUpper root⟩

/-- 最小根を下側へ移しても、両ヒープの順序は任意長で保たれる。 -/
theorem transferUpperRoot_preserves_heapOrders
    {lower upper nextLower nextUpper : Array Nat}
    (hLower : HeapOrdered LeanExperiments.RunningMedian.maxPrefer lower)
    (hUpper : HeapOrdered LeanExperiments.RunningMedian.minPrefer upper)
    (hMove : LeanExperiments.RunningMedian.transferUpperRoot
      LeanExperiments.RunningMedian.minPrefer LeanExperiments.RunningMedian.maxPrefer
      lower upper = some (nextLower, nextUpper)) :
    HeapOrdered LeanExperiments.RunningMedian.maxPrefer nextLower ∧
      HeapOrdered LeanExperiments.RunningMedian.minPrefer nextUpper := by
  unfold LeanExperiments.RunningMedian.transferUpperRoot at hMove
  cases hPop : LeanExperiments.RunningMedian.popHeap
      LeanExperiments.RunningMedian.minPrefer upper with
  | none => simp [hPop] at hMove
  | some pair =>
    rcases pair with ⟨root, rest⟩
    have hResult : LeanExperiments.RunningMedian.insertHeap
          LeanExperiments.RunningMedian.maxPrefer lower root = nextLower ∧
        rest = nextUpper := by
      simpa [hPop] using hMove
    rcases hResult with ⟨hInsertedEq, hRestEq⟩
    subst nextLower
    subst nextUpper
    have hPreferEq : minPrefer = LeanExperiments.RunningMedian.minPrefer := by
      funext candidate current
      rfl
    have hPopLocal : LeanExperiments.RunningMedian.popHeap minPrefer upper =
        some (root, rest) := by
      simpa only [hPreferEq] using hPop
    have hRestHeap : MinHeap rest :=
      popHeap_minPrefer_restMinHeap_of_MinHeap
        ((minHeap_iff_HeapOrdered_minPrefer upper).mpr hUpper) hPopLocal
    exact ⟨insertHeap_maxPrefer_preserves lower hLower root,
      (minHeap_iff_HeapOrdered_minPrefer _).mp hRestHeap⟩

/-- 振り分け後のサイズ差が最大2なら、再平衡後も両ヒープ順序と境界を保つ。

このサイズ範囲では下側または上側の根を高々一度移せばよい。各遷移の順序保存と
境界保存を接続し、両ループの停止後の契約を得る。
-/
theorem rebalanceBoth_preserves_heapOrders_and_crossBoundary
    (lower upper : Array Nat)
    (hLower : HeapOrdered LeanExperiments.RunningMedian.maxPrefer lower)
    (hUpper : HeapOrdered LeanExperiments.RunningMedian.minPrefer upper)
    (hBoundary : ∀ i (hi : i < lower.size) j (hj : j < upper.size),
      lower[i]'hi ≤ upper[j]'hj)
    (hLowerClose : lower.size ≤ upper.size + 2)
    (hUpperClose : upper.size ≤ lower.size + 1) :
    let lowerResult := LeanExperiments.RunningMedian.rebalanceLower lower upper
    let result := LeanExperiments.RunningMedian.rebalanceUpper lowerResult.1 lowerResult.2
    HeapOrdered LeanExperiments.RunningMedian.maxPrefer result.1 ∧
      HeapOrdered LeanExperiments.RunningMedian.minPrefer result.2 ∧
      (∀ i (hi : i < result.1.size) j (hj : j < result.2.size),
        result.1[i]'hi ≤ result.2[j]'hj) := by
  by_cases hLowerTooLarge : upper.size + 1 < lower.size
  · have hLowerDiff : lower.size = upper.size + 2 := by omega
    have hLowerNonempty : 0 < lower.size := by omega
    have hTransferSome := (transferLowerRoot_isSome_iff_source_nonempty
      LeanExperiments.RunningMedian.maxPrefer LeanExperiments.RunningMedian.minPrefer
      lower upper).2 hLowerNonempty
    cases hMove : LeanExperiments.RunningMedian.transferLowerRoot
        LeanExperiments.RunningMedian.maxPrefer LeanExperiments.RunningMedian.minPrefer
        lower upper with
    | none => simp [hMove] at hTransferSome
    | some pair =>
      rcases pair with ⟨nextLower, nextUpper⟩
      have hNextSize := transferLowerRoot_size hMove
      have hNextBalanced : nextLower.size ≤ nextUpper.size + 1 := by omega
      have hAfterLower := rebalanceLower_one_transfer lower upper
        nextLower nextUpper hLowerTooLarge hMove hNextBalanced
      have hAfterUpper := rebalanceUpper_eq_self_of_size_le nextLower nextUpper (by omega)
      have hOrders := transferLowerRoot_preserves_heapOrders hLower hUpper hMove
      have hCross := transferLowerRoot_preserves_crossBoundary hLower hUpper hBoundary hMove
      dsimp only
      rw [hAfterLower, hAfterUpper]
      exact ⟨hOrders.1, hOrders.2, hCross⟩
  · have hLowerNoop := rebalanceLower_eq_self_of_size_le lower upper (by omega)
    by_cases hUpperTooLarge : lower.size < upper.size
    · have hUpperDiff : upper.size = lower.size + 1 := by omega
      have hUpperNonempty : 0 < upper.size := by omega
      have hTransferSome := (transferUpperRoot_isSome_iff_source_nonempty
        LeanExperiments.RunningMedian.minPrefer LeanExperiments.RunningMedian.maxPrefer
        lower upper).2 hUpperNonempty
      cases hMove : LeanExperiments.RunningMedian.transferUpperRoot
          LeanExperiments.RunningMedian.minPrefer LeanExperiments.RunningMedian.maxPrefer
          lower upper with
      | none => simp [hMove] at hTransferSome
      | some pair =>
        rcases pair with ⟨nextLower, nextUpper⟩
        have hNextSize := transferUpperRoot_size hMove
        have hNextBalanced : nextUpper.size ≤ nextLower.size := by omega
        have hAfterUpper := rebalanceUpper_one_transfer lower upper
          nextLower nextUpper hUpperTooLarge hMove hNextBalanced
        have hOrders := transferUpperRoot_preserves_heapOrders hLower hUpper hMove
        have hCross := transferUpperRoot_preserves_crossBoundary hLower hUpper hBoundary hMove
        dsimp only
        rw [hLowerNoop, hAfterUpper]
        exact ⟨hOrders.1, hOrders.2, hCross⟩
    · have hUpperNoop := rebalanceUpper_eq_self_of_size_le lower upper (by omega)
      have hCrossFinal := hBoundary
      dsimp only
      rw [hLowerNoop, hUpperNoop]
      exact ⟨hLower, hUpper, hCrossFinal⟩

/-- ヒープへの値振り分けは、選んだヒープの長さを1つ増やして入力要素の分割を保つ。 -/
theorem insertLower_partition_size {input : Array Nat}
    (state : LeanExperiments.RunningMedian.State) (value : Nat)
    (hPartition : (state.lower.toList ++ state.upper.toList).Perm input.toList) :
    ((LeanExperiments.RunningMedian.insertHeap maxPrefer state.lower value).toList ++
      state.upper.toList).Perm (input.push value).toList ∧
    (LeanExperiments.RunningMedian.insertHeap maxPrefer state.lower value).size =
      state.lower.size + 1 := by
  have hInsert := (insertHeap_perm maxPrefer state.lower value).append
    (List.Perm.refl state.upper.toList)
  have hReorder :
      (state.lower.toList ++ [value] ++ state.upper.toList).Perm
        (state.lower.toList ++ state.upper.toList ++ [value]) := by
    have hSwap : ([value] ++ state.upper.toList).Perm
        (state.upper.toList ++ [value]) := List.perm_append_comm
    simpa only [List.append_assoc] using
      (List.Perm.refl state.lower.toList).append hSwap
  have hPush := hPartition.append_right [value]
  constructor
  · have hFinal := hInsert.trans (hReorder.trans hPush)
    simpa only [Array.toList_push] using hFinal
  · exact insertHeap_size maxPrefer state.lower value

/-- 上側ヒープへの値振り分けも、長さ増加と入力要素の分割を保つ。 -/
theorem insertUpper_partition_size {input : Array Nat}
    (state : LeanExperiments.RunningMedian.State) (value : Nat)
    (hPartition : (state.lower.toList ++ state.upper.toList).Perm input.toList) :
    (state.lower.toList ++
      (LeanExperiments.RunningMedian.insertHeap minPrefer state.upper value).toList).Perm
        (input.push value).toList ∧
    (LeanExperiments.RunningMedian.insertHeap minPrefer state.upper value).size =
      state.upper.size + 1 := by
  have hInsert := (List.Perm.refl state.lower.toList).append
    (insertHeap_perm minPrefer state.upper value)
  have hPush := hPartition.append_right [value]
  have hReassoc :
      (state.lower.toList ++ (state.upper.toList ++ [value])).Perm
        ((state.lower.toList ++ state.upper.toList) ++ [value]) :=
    List.Perm.of_eq (by simp [List.append_assoc])
  constructor
  · have hFinal := hInsert.trans (hReassoc.trans hPush)
    simpa only [Array.toList_push] using hFinal
  · exact insertHeap_size minPrefer state.upper value

/-- 実装の根取得分岐に従う振り分けは、全ての状態で分割とサイズ契約を満たす。 -/
theorem insertRouted_partition_size {input : Array Nat}
    (state : LeanExperiments.RunningMedian.State) (value : Nat)
    (hPartition : (state.lower.toList ++ state.upper.toList).Perm input.toList) :
    (if state.lower.isEmpty then
      ((LeanExperiments.RunningMedian.insertHeap maxPrefer state.lower value).toList ++
        state.upper.toList).Perm (input.push value).toList ∧
        (LeanExperiments.RunningMedian.insertHeap maxPrefer state.lower value).size =
          state.lower.size + 1
    else
      if value ≤ state.lower[0]! then
        ((LeanExperiments.RunningMedian.insertHeap maxPrefer state.lower value).toList ++
          state.upper.toList).Perm (input.push value).toList ∧
          (LeanExperiments.RunningMedian.insertHeap maxPrefer state.lower value).size =
            state.lower.size + 1
      else
        (state.lower.toList ++
          (LeanExperiments.RunningMedian.insertHeap minPrefer state.upper value).toList).Perm
            (input.push value).toList ∧
          (LeanExperiments.RunningMedian.insertHeap minPrefer state.upper value).size =
            state.upper.size + 1) := by
  by_cases hEmpty : state.lower.isEmpty = true
  · simpa [hEmpty, Array.toList_push] using
      (insertLower_partition_size state value hPartition)
  · have hNonempty : ¬ state.lower.isEmpty := by simpa using hEmpty
    have hArrayNe : state.lower ≠ #[] := by
      intro hArray
      have hIsEmpty : state.lower.isEmpty = true := by simp [hArray]
      exact hEmpty hIsEmpty
    have hLower : 0 < state.lower.size := Array.size_pos_iff.mpr hArrayNe
    have hRootEq : state.lower[0]! = state.lower[0]'hLower :=
      getElem!_pos state.lower 0 hLower
    by_cases hRoute : value ≤ state.lower[0]'hLower
    · simpa [hEmpty, hRootEq, hRoute, Array.toList_push] using
        (insertLower_partition_size state value hPartition)
    · simpa [hEmpty, hRootEq, hRoute, Array.toList_push] using
        (insertUpper_partition_size state value hPartition)

/-- 逐次中央値への挿入は、空状態の特別分岐を含めて要素数を1つ増やす。 -/
theorem insert_total_size (state : LeanExperiments.RunningMedian.State) (value : Nat) :
    (LeanExperiments.RunningMedian.insert state value).lower.size +
      (LeanExperiments.RunningMedian.insert state value).upper.size =
        state.lower.size + state.upper.size + 1 := by
  by_cases hEmpty : state.lower = #[] ∧ state.upper = #[]
  · simp [LeanExperiments.RunningMedian.insert, hEmpty.1, hEmpty.2]
  · cases hRoot : state.lower[0]? with
    | none =>
        simp [LeanExperiments.RunningMedian.insert, hEmpty, hRoot,
          rebalanceBoth_total_size, insertHeap_size]
        omega
    | some root =>
        by_cases hRoute : value ≤ root
        · simp [LeanExperiments.RunningMedian.insert, hEmpty, hRoot, hRoute,
            rebalanceBoth_total_size, insertHeap_size]
          omega
        · simp [LeanExperiments.RunningMedian.insert, hEmpty, hRoot, hRoute,
            rebalanceBoth_total_size, insertHeap_size]
          omega

/-- 任意の状態への挿入後、下側は上側と同数か1つ多くなる。 -/
theorem insert_size_balanced (state : LeanExperiments.RunningMedian.State) (value : Nat) :
    (LeanExperiments.RunningMedian.insert state value).lower.size =
        (LeanExperiments.RunningMedian.insert state value).upper.size ∨
      (LeanExperiments.RunningMedian.insert state value).lower.size =
        (LeanExperiments.RunningMedian.insert state value).upper.size + 1 := by
  by_cases hEmpty : state.lower = #[] ∧ state.upper = #[]
  · simp [LeanExperiments.RunningMedian.insert, hEmpty.1, hEmpty.2]
  · have hNotEmpty : ¬(state.lower.isEmpty && state.upper.isEmpty) := by
      simp only [Bool.and_eq_true]
      intro h
      exact hEmpty ⟨Array.isEmpty_iff.mp h.1, Array.isEmpty_iff.mp h.2⟩
    cases hRoot : state.lower[0]? with
    | none =>
        have hBal := rebalanceBoth_size_balanced
          (LeanExperiments.RunningMedian.insertHeap
            LeanExperiments.RunningMedian.maxPrefer state.lower value) state.upper
        dsimp at hBal
        simp [LeanExperiments.RunningMedian.insert, hNotEmpty, hRoot]
        rcases hBal with ⟨hLower, hUpper⟩
        omega
    | some root =>
        by_cases hRoute : value ≤ root
        · have hBal := rebalanceBoth_size_balanced
            (LeanExperiments.RunningMedian.insertHeap
              LeanExperiments.RunningMedian.maxPrefer state.lower value) state.upper
          dsimp at hBal
          simp [LeanExperiments.RunningMedian.insert, hNotEmpty, hRoot, hRoute]
          rcases hBal with ⟨hLower, hUpper⟩
          omega
        · have hBal := rebalanceBoth_size_balanced state.lower
            (LeanExperiments.RunningMedian.insertHeap
              LeanExperiments.RunningMedian.minPrefer state.upper value)
          dsimp at hBal
          simp [LeanExperiments.RunningMedian.insert, hNotEmpty, hRoot, hRoute]
          rcases hBal with ⟨hLower, hUpper⟩
          omega

/-- 挿入後の上下ヒープ長は、挿入前の総要素数から切り上げ・切り捨て半分に定まる。 -/
theorem insert_heap_sizes (state : LeanExperiments.RunningMedian.State) (value : Nat) :
    (LeanExperiments.RunningMedian.insert state value).lower.size =
        (state.lower.size + state.upper.size + 2) / 2 ∧
      (LeanExperiments.RunningMedian.insert state value).upper.size =
        (state.lower.size + state.upper.size + 1) / 2 := by
  have hTotal := insert_total_size state value
  have hBalanced := insert_size_balanced state value
  omega

/-- 要素分割を保つ状態への挿入後、2ヒープの合計サイズは入力長より1大きい。 -/
theorem insert_size_partition {input : Array Nat}
    (state : LeanExperiments.RunningMedian.State) (value : Nat)
    (hPartition : (state.lower.toList ++ state.upper.toList).Perm input.toList) :
    (LeanExperiments.RunningMedian.insert state value).lower.size +
      (LeanExperiments.RunningMedian.insert state value).upper.size = input.size + 1 := by
  have hSize : state.lower.size + state.upper.size = input.size := by
    simpa [List.length_append] using hPartition.length_eq
  rw [insert_total_size, hSize]

/-- 根を一方のヒープから取り出して他方へ挿入しても、全要素と合計サイズを保存する。 -/
theorem popHeap_insert_partition_size {sourcePrefer destinationPrefer : Nat → Nat → Bool}
    {source destination : Array Nat} {root : Nat} {rest : Array Nat}
    (hPop : LeanExperiments.RunningMedian.popHeap sourcePrefer source = some (root, rest)) :
    (rest.toList ++
      (LeanExperiments.RunningMedian.insertHeap destinationPrefer destination root).toList).Perm
        (source.toList ++ destination.toList) ∧
    rest.size +
      (LeanExperiments.RunningMedian.insertHeap destinationPrefer destination root).size =
        source.size + destination.size := by
  have hRestPerm := popHeap_perm_dropRoot hPop
  have hRoot := popHeap_value_eq_root hPop
  have hListRoot : source.toList[0]? = some root := by
    rw [Array.getElem?_toList]
    exact hRoot
  have hHeadLt : 0 < source.toList.length :=
    (List.getElem?_eq_some_iff.mp hListRoot).1
  have hHeadValue : source.toList[0] = root :=
    (List.getElem?_eq_some_iff.mp hListRoot).2
  have hDecomp : root :: source.toList.drop 1 = source.toList := by
    have hListDecomp := List.getElem_cons_drop (as := source.toList) (i := 0) hHeadLt
    simpa [hHeadValue] using hListDecomp
  have hRestFull : (root :: rest.toList).Perm source.toList := by
    calc
      (root :: rest.toList).Perm (root :: source.toList.drop 1) :=
        List.Perm.cons root hRestPerm
      _ = source.toList := hDecomp
  have hInsert := insertHeap_perm destinationPrefer destination root
  have hInsertList :
      (LeanExperiments.RunningMedian.insertHeap destinationPrefer destination root).toList.Perm
        (destination.toList ++ [root]) := by
    simpa only [Array.toList_push] using hInsert
  have hSwapDestination : (destination.toList ++ [root]).Perm ([root] ++ destination.toList) :=
    List.perm_append_comm
  have hMoveRoot :
      (rest.toList ++ (destination.toList ++ [root])).Perm
        ((root :: rest.toList) ++ destination.toList) := by
    have hMoveToFront := (List.Perm.refl rest.toList).append hSwapDestination
    have hAssoc : (rest.toList ++ ([root] ++ destination.toList)) =
        ((rest.toList ++ [root]) ++ destination.toList) := by
      simp [List.append_assoc]
    have hSwapRest :
        ((rest.toList ++ [root]) ++ destination.toList).Perm
          (([root] ++ rest.toList) ++ destination.toList) :=
      (List.perm_append_comm).append (List.Perm.refl destination.toList)
    simpa [List.append_assoc] using
      (hMoveToFront.trans ((List.Perm.of_eq hAssoc).trans hSwapRest))
  have hPartition :=
    (List.Perm.refl rest.toList).append hInsertList |>.trans hMoveRoot
  have hPartition := hPartition.trans
    (hRestFull.append (List.Perm.refl destination.toList))
  have hRestSize := popHeap_size hPop
  have hInsertSize := insertHeap_size destinationPrefer destination root
  constructor
  · exact hPartition
  · omega

/-- 反対側の根を移す向きでも、移動後の要素分割と合計サイズが保存される。 -/
theorem insertHeap_pop_partition_size {sourcePrefer destinationPrefer : Nat → Nat → Bool}
    {source destination : Array Nat} {root : Nat} {rest : Array Nat}
    (hPop : LeanExperiments.RunningMedian.popHeap sourcePrefer source = some (root, rest)) :
    ((LeanExperiments.RunningMedian.insertHeap destinationPrefer destination root).toList ++
      rest.toList).Perm (destination.toList ++ source.toList) ∧
    (LeanExperiments.RunningMedian.insertHeap destinationPrefer destination root).size +
      rest.size = destination.size + source.size := by
  have hTransfer := popHeap_insert_partition_size
    (sourcePrefer := sourcePrefer) (destinationPrefer := destinationPrefer)
    (source := source) (destination := destination) hPop
  constructor
  · exact List.perm_append_comm.trans
      (hTransfer.1.trans List.perm_append_comm)
  · omega

/-- 下側の根を上側へ移す成功遷移は、要素分割と合計サイズを保つ。 -/
theorem transferLowerRoot_partition_size {sourcePrefer destinationPrefer : Nat → Nat → Bool}
    {lower upper nextLower nextUpper : Array Nat}
    (hMove : LeanExperiments.RunningMedian.transferLowerRoot sourcePrefer destinationPrefer
      lower upper =
      some (nextLower, nextUpper)) :
    (nextLower.toList ++ nextUpper.toList).Perm (lower.toList ++ upper.toList) ∧
      nextLower.size + nextUpper.size = lower.size + upper.size ∧
      nextLower.size + 1 = lower.size ∧ nextUpper.size = upper.size + 1 := by
  unfold LeanExperiments.RunningMedian.transferLowerRoot at hMove
  cases hPop : LeanExperiments.RunningMedian.popHeap sourcePrefer lower with
  | none => simp [hPop] at hMove
  | some pair =>
      rcases pair with ⟨value, rest⟩
      have hResult : rest = nextLower ∧
          LeanExperiments.RunningMedian.insertHeap destinationPrefer upper value = nextUpper := by
        simpa [hPop] using hMove
      rcases hResult with ⟨hLower, hUpper⟩
      subst nextLower
      subst nextUpper
      have hTransfer := popHeap_insert_partition_size
        (sourcePrefer := sourcePrefer) (destinationPrefer := destinationPrefer)
        (source := lower) (destination := upper) hPop
      have hPopSize := popHeap_size hPop
      have hInsertSize := insertHeap_size destinationPrefer upper value
      exact ⟨hTransfer.1, by omega, hPopSize, by omega⟩

/-- 上側の根を下側へ移す成功遷移も、要素分割と合計サイズを保つ。 -/
theorem transferUpperRoot_partition_size {sourcePrefer destinationPrefer : Nat → Nat → Bool}
    {lower upper nextLower nextUpper : Array Nat}
    (hMove : LeanExperiments.RunningMedian.transferUpperRoot sourcePrefer destinationPrefer
      lower upper =
      some (nextLower, nextUpper)) :
    (nextLower.toList ++ nextUpper.toList).Perm (lower.toList ++ upper.toList) ∧
      nextLower.size + nextUpper.size = lower.size + upper.size ∧
      nextLower.size = lower.size + 1 ∧ nextUpper.size + 1 = upper.size := by
  unfold LeanExperiments.RunningMedian.transferUpperRoot at hMove
  cases hPop : LeanExperiments.RunningMedian.popHeap sourcePrefer upper with
  | none => simp [hPop] at hMove
  | some pair =>
      rcases pair with ⟨value, rest⟩
      have hResult : LeanExperiments.RunningMedian.insertHeap destinationPrefer lower value =
          nextLower ∧ rest = nextUpper := by
        simpa [hPop] using hMove
      rcases hResult with ⟨hLower, hUpper⟩
      subst nextLower
      subst nextUpper
      have hTransfer := insertHeap_pop_partition_size
        (sourcePrefer := sourcePrefer) (destinationPrefer := destinationPrefer)
        (source := upper) (destination := lower) hPop
      have hPopSize := popHeap_size hPop
      have hInsertSize := insertHeap_size destinationPrefer lower value
      exact ⟨hTransfer.1, by omega, by omega, hPopSize⟩

/-- 下側からの再平衡ループは、反復全体で二つのヒープの要素分割を保つ。 -/
theorem rebalanceLower_perm (lower upper : Array Nat) :
    let result := LeanExperiments.RunningMedian.rebalanceLower lower upper
    (result.1.toList ++ result.2.toList).Perm (lower.toList ++ upper.toList) := by
  change ((LeanExperiments.RunningMedian.rebalanceLower lower upper).1.toList ++
      (LeanExperiments.RunningMedian.rebalanceLower lower upper).2.toList).Perm
    (lower.toList ++ upper.toList)
  generalize hRun : LeanExperiments.RunningMedian.rebalanceLower lower upper = result
  unfold LeanExperiments.RunningMedian.rebalanceLower at hRun
  apply Id.of_run_eq_wp hRun
  vcgen [LeanExperiments.RunningMedian.rebalanceLower] invariants
  case inv1 => exact fun _ heaps =>
    (heaps.1.toList ++ heaps.2.toList).Perm (lower.toList ++ upper.toList)
  case vc1 => exact List.Perm.refl _
  case vc2 => simp_all
  case vc3 =>
    simp_all [LeanExperiments.RunningMedian.transferLowerRoot,
      Variant.evalsBelow_ofMeasure_nat, Variant.evalsTo_ofMeasure,
      Assertion.NondetFun.evalsTo_pure]
    rcases ‹_ ∧ _› with ⟨hMeasure, hPartition⟩
    have hMove := transferLowerRoot_partition_size (by assumption)
    rcases hMove with ⟨hPerm, hTotal, hLowerSize, hUpperSize⟩
    constructor
    · omega
    · exact hPerm.trans hPartition
  case vc4 =>
    simp_all [Variant.evalsTo_ofMeasure, Assertion.NondetFun.evalsTo_pure]
  case vc5 => simp_all

/-- 上側からの再平衡ループも、反復全体で二つのヒープの要素分割を保つ。 -/
theorem rebalanceUpper_perm (lower upper : Array Nat) :
    let result := LeanExperiments.RunningMedian.rebalanceUpper lower upper
    (result.1.toList ++ result.2.toList).Perm (lower.toList ++ upper.toList) := by
  change ((LeanExperiments.RunningMedian.rebalanceUpper lower upper).1.toList ++
      (LeanExperiments.RunningMedian.rebalanceUpper lower upper).2.toList).Perm
    (lower.toList ++ upper.toList)
  generalize hRun : LeanExperiments.RunningMedian.rebalanceUpper lower upper = result
  unfold LeanExperiments.RunningMedian.rebalanceUpper at hRun
  apply Id.of_run_eq_wp hRun
  vcgen [LeanExperiments.RunningMedian.rebalanceUpper] invariants
  case inv1 => exact fun _ heaps =>
    (heaps.1.toList ++ heaps.2.toList).Perm (lower.toList ++ upper.toList)
  case vc1 => exact List.Perm.refl _
  case vc2 => simp_all
  case vc3 =>
    simp_all [LeanExperiments.RunningMedian.transferUpperRoot,
      Variant.evalsBelow_ofMeasure_nat, Variant.evalsTo_ofMeasure,
      Assertion.NondetFun.evalsTo_pure]
    rcases ‹_ ∧ _› with ⟨hMeasure, hPartition⟩
    have hMove := transferUpperRoot_partition_size (by assumption)
    rcases hMove with ⟨hPerm, hTotal, hLowerSize, hUpperSize⟩
    constructor
    · omega
    · exact hPerm.trans hPartition
  case vc4 =>
    simp_all [Variant.evalsTo_ofMeasure, Assertion.NondetFun.evalsTo_pure]
  case vc5 => simp_all

/-- 上下の再平衡を続けて適用しても、二つのヒープの要素分割を保つ。 -/
theorem rebalanceBoth_perm (lower upper : Array Nat) :
    let lowerResult := LeanExperiments.RunningMedian.rebalanceLower lower upper
    let result := LeanExperiments.RunningMedian.rebalanceUpper
      lowerResult.1 lowerResult.2
    (result.1.toList ++ result.2.toList).Perm (lower.toList ++ upper.toList) := by
  change (((LeanExperiments.RunningMedian.rebalanceUpper
      (LeanExperiments.RunningMedian.rebalanceLower lower upper).1
      (LeanExperiments.RunningMedian.rebalanceLower lower upper).2).1.toList ++
      (LeanExperiments.RunningMedian.rebalanceUpper
        (LeanExperiments.RunningMedian.rebalanceLower lower upper).1
        (LeanExperiments.RunningMedian.rebalanceLower lower upper).2).2.toList)).Perm
    (lower.toList ++ upper.toList)
  exact (rebalanceUpper_perm
    (LeanExperiments.RunningMedian.rebalanceLower lower upper).1
    (LeanExperiments.RunningMedian.rebalanceLower lower upper).2).trans
      (rebalanceLower_perm lower upper)

/-- 再平衡の前後で、任意の Boolean 分類に属する要素数が保たれる。 -/
theorem rebalanceBoth_countP (lower upper : Array Nat) (predicate : Nat → Bool) :
    let lowerResult := LeanExperiments.RunningMedian.rebalanceLower lower upper
    let result := LeanExperiments.RunningMedian.rebalanceUpper lowerResult.1 lowerResult.2
    result.1.toList.countP predicate + result.2.toList.countP predicate =
      lower.toList.countP predicate + upper.toList.countP predicate := by
  have hCount := (rebalanceBoth_perm lower upper).countP_eq predicate
  simpa [List.countP_append] using hCount

/-- 任意の状態での1件挿入は、再平衡後も入力と新しい値の要素分割を保つ。 -/
theorem insert_partition {input : Array Nat} (state : LeanExperiments.RunningMedian.State)
    (value : Nat)
    (hPartition : (state.lower.toList ++ state.upper.toList).Perm input.toList) :
    ((LeanExperiments.RunningMedian.insert state value).lower.toList ++
      (LeanExperiments.RunningMedian.insert state value).upper.toList).Perm
        (input.push value).toList := by
  by_cases hEmpty : state.lower = #[] ∧ state.upper = #[]
  · have hInputSize : input.size = 0 := by
      have hLength := hPartition.length_eq
      simpa [hEmpty.1, hEmpty.2] using hLength.symm
    have hInput : input = #[] := Array.size_eq_zero_iff.mp hInputSize
    simp [LeanExperiments.RunningMedian.insert, hEmpty.1, hEmpty.2, hInput]
  · cases hRoot : state.lower[0]? with
    | none =>
        have hPre := insertLower_partition_size state value hPartition
        have hHeapEq : LeanExperiments.RunningMedian.insertHeap maxPrefer state.lower value =
            LeanExperiments.RunningMedian.insertHeap
              LeanExperiments.RunningMedian.maxPrefer state.lower value := by
          rfl
        rw [hHeapEq] at hPre
        simpa [LeanExperiments.RunningMedian.insert, hEmpty, hRoot] using
          (rebalanceBoth_perm
            (LeanExperiments.RunningMedian.insertHeap
              LeanExperiments.RunningMedian.maxPrefer state.lower value)
            state.upper).trans hPre.1
    | some root =>
        by_cases hRoute : value ≤ root
        · have hPre := insertLower_partition_size state value hPartition
          have hHeapEq : LeanExperiments.RunningMedian.insertHeap maxPrefer state.lower value =
              LeanExperiments.RunningMedian.insertHeap
                LeanExperiments.RunningMedian.maxPrefer state.lower value := by
            rfl
          rw [hHeapEq] at hPre
          simpa [LeanExperiments.RunningMedian.insert, hEmpty, hRoot, hRoute] using
            (rebalanceBoth_perm
              (LeanExperiments.RunningMedian.insertHeap
                LeanExperiments.RunningMedian.maxPrefer state.lower value)
              state.upper).trans hPre.1
        · have hPre := insertUpper_partition_size state value hPartition
          have hHeapEq : LeanExperiments.RunningMedian.insertHeap minPrefer state.upper value =
              LeanExperiments.RunningMedian.insertHeap
                LeanExperiments.RunningMedian.minPrefer state.upper value := by
            rfl
          rw [hHeapEq] at hPre
          simpa [LeanExperiments.RunningMedian.insert, hEmpty, hRoot, hRoute] using
            (rebalanceBoth_perm state.lower
              (LeanExperiments.RunningMedian.insertHeap
                LeanExperiments.RunningMedian.minPrefer state.upper value)).trans hPre.1

/-- 挿入後の2ヒープに含まれる任意分類の件数は、入力件数と追加値で決まる。

要素順列契約を任意の Boolean 述語へ写した結果であり、重複値を含む入力でも
分類ごとの件数が正確に保たれることを表す。
-/
theorem insert_countP_partition {input : Array Nat}
    (state : LeanExperiments.RunningMedian.State) (value : Nat)
    (hPartition : (state.lower.toList ++ state.upper.toList).Perm input.toList)
    (predicate : Nat → Bool) :
    (LeanExperiments.RunningMedian.insert state value).lower.toList.countP predicate +
        (LeanExperiments.RunningMedian.insert state value).upper.toList.countP predicate =
      input.toList.countP predicate + (if predicate value then 1 else 0) := by
  have hPerm := insert_partition state value hPartition
  have hCount := hPerm.countP_eq predicate
  rw [Array.toList_push, List.countP_append] at hCount
  simpa [List.countP_cons] using hCount

/-- 任意長の入力全体が、`ofArray` の二つのヒープへ順列として分配される。 -/
theorem ofArray_partition (values : Array Nat) :
    ((LeanExperiments.RunningMedian.ofArray values).lower.toList ++
      (LeanExperiments.RunningMedian.ofArray values).upper.toList).Perm values.toList := by
  have foldPartition (items : List Nat) (initial : LeanExperiments.RunningMedian.State)
      (input : Array Nat)
      (hPartition : (initial.lower.toList ++ initial.upper.toList).Perm input.toList) :
      (((items.foldl LeanExperiments.RunningMedian.insert initial).lower.toList ++
        (items.foldl LeanExperiments.RunningMedian.insert initial).upper.toList).Perm
          (input.toList ++ items)) := by
    induction items generalizing initial input with
    | nil => simpa using hPartition
    | cons value items ih =>
        simp only [List.foldl_cons]
        have hStep := insert_partition initial value hPartition
        have hRest := ih (LeanExperiments.RunningMedian.insert initial value)
          (input.push value) hStep
        simpa [Array.toList_push, List.append_assoc] using hRest
  simpa [LeanExperiments.RunningMedian.ofArray, LeanExperiments.RunningMedian.empty,
    ← Array.foldl_toList] using
      foldPartition values.toList LeanExperiments.RunningMedian.empty #[]
        (by simp [LeanExperiments.RunningMedian.empty])

/-- `ofArray` の最終状態は、任意の Boolean 分類ごとに入力要素数を正確に分配する。

逐次挿入を通した要素順列保存から従うため、重複値や値域に制限を置かない。
-/
theorem ofArray_countP_partition (values : Array Nat) (predicate : Nat → Bool) :
    (LeanExperiments.RunningMedian.ofArray values).lower.toList.countP predicate +
        (LeanExperiments.RunningMedian.ofArray values).upper.toList.countP predicate =
      values.toList.countP predicate := by
  rw [← List.countP_append]
  exact (ofArray_partition values).countP_eq predicate

/-- 状態不変条件のヒープ部分を、最大・最小ヒープの数値仕様で表した同値定理。 -/
theorem StateInvariant.iff_numericHeapSpecs (input : Array Nat)
    (state : LeanExperiments.RunningMedian.State) :
    StateInvariant input state ↔
      (state.lower.toList ++ state.upper.toList).Perm input.toList ∧
        LeanExperiments.Verification.HeapSort.Spec.MaxHeap state.lower ∧
        MinHeap state.upper ∧
        (∀ lowerIndex (hLowerIndex : lowerIndex < state.lower.size),
          ∀ upperIndex (hUpperIndex : upperIndex < state.upper.size),
            state.lower[lowerIndex]'hLowerIndex ≤ state.upper[upperIndex]'hUpperIndex) ∧
        (state.lower.size = state.upper.size ∨
          state.lower.size = state.upper.size + 1) := by
  constructor
  · rintro ⟨hPerm, hLower, hUpper, hBoundary, hSize⟩
    exact ⟨hPerm,
      (heapSortMaxHeap_iff_HeapOrdered_maxPrefer state.lower).mpr hLower,
      (minHeap_iff_HeapOrdered_minPrefer state.upper).2 hUpper,
      hBoundary, hSize⟩

  · rintro ⟨hPerm, hLower, hUpper, hBoundary, hSize⟩
    exact ⟨hPerm,
      (heapSortMaxHeap_iff_HeapOrdered_maxPrefer state.lower).mp hLower,
      (minHeap_iff_HeapOrdered_minPrefer state.upper).1 hUpper,
      hBoundary, hSize⟩

/-- 数値ヒープ仕様の下では、全要素間の分割条件を根の比較で置き換えられる。 -/
theorem StateInvariant.iff_numericHeapRootBoundary (input : Array Nat)
    (state : LeanExperiments.RunningMedian.State) :
    StateInvariant input state ↔
      (state.lower.toList ++ state.upper.toList).Perm input.toList ∧
        LeanExperiments.Verification.HeapSort.Spec.MaxHeap state.lower ∧
        MinHeap state.upper ∧
        (state.lower.size = 0 ∨ state.upper.size = 0 ∨
          state.lower[0]! ≤ state.upper[0]!) ∧
        (state.lower.size = state.upper.size ∨
          state.lower.size = state.upper.size + 1) := by
  rw [StateInvariant.iff_numericHeapSpecs]
  constructor
  · rintro ⟨hPerm, hLower, hUpper, hCross, hSize⟩
    have hRoot := (crossBoundary_iff_rootBoundary state
      ((heapSortMaxHeap_iff_HeapOrdered_maxPrefer state.lower).mp hLower)
      ((minHeap_iff_HeapOrdered_minPrefer state.upper).1 hUpper)).mp hCross
    exact ⟨hPerm, hLower, hUpper, hRoot, hSize⟩
  · rintro ⟨hPerm, hLower, hUpper, hRoot, hSize⟩
    have hCross := (crossBoundary_iff_rootBoundary state
      ((heapSortMaxHeap_iff_HeapOrdered_maxPrefer state.lower).mp hLower)
      ((minHeap_iff_HeapOrdered_minPrefer state.upper).1 hUpper)).mpr hRoot
    exact ⟨hPerm, hLower, hUpper, hCross, hSize⟩

/-- 状態不変条件が成り立ち、両ヒープが非空なら、下側の最大値は上側の最小値以下である。 -/
theorem StateInvariant.lowerRoot_le_upperRoot (input : Array Nat)
    (state : LeanExperiments.RunningMedian.State)
    (hInvariant : StateInvariant input state)
    (hLower : 0 < state.lower.size) (hUpper : 0 < state.upper.size) :
    state.lower[0]! ≤ state.upper[0]! := by
  rcases hInvariant with ⟨_, _, _, hBoundary, _⟩
  simpa only [getElem!_pos state.lower 0 hLower,
    getElem!_pos state.upper 0 hUpper] using
      (hBoundary 0 hLower 0 hUpper)

/-- 空入力の処理結果は、空状態のままである。 -/
theorem ofArray_empty :
    LeanExperiments.RunningMedian.ofArray #[] = LeanExperiments.RunningMedian.empty := by
  simp [LeanExperiments.RunningMedian.ofArray, LeanExperiments.RunningMedian.empty]

/-- 入力末尾へ値を追加した状態は、前の状態へその値を1回挿入した結果である。 -/
theorem ofArray_push (values : Array Nat) (value : Nat) :
    LeanExperiments.RunningMedian.ofArray (values.push value) =
      LeanExperiments.RunningMedian.insert
        (LeanExperiments.RunningMedian.ofArray values) value := by
  simp [LeanExperiments.RunningMedian.ofArray]

/-- 任意の入力に対し、二つのヒープに保持する要素数の合計は入力長に一致する。 -/
theorem ofArray_total_size (values : Array Nat) :
    (LeanExperiments.RunningMedian.ofArray values).lower.size +
      (LeanExperiments.RunningMedian.ofArray values).upper.size = values.size := by
  have foldTotal (items : List Nat) (initial : LeanExperiments.RunningMedian.State) :
      (items.foldl LeanExperiments.RunningMedian.insert initial).lower.size +
        (items.foldl LeanExperiments.RunningMedian.insert initial).upper.size =
          initial.lower.size + initial.upper.size + items.length := by
    induction items generalizing initial with
    | nil => simp
    | cons value items ih =>
        simp only [List.foldl_cons]
        rw [ih, insert_total_size]
        simp only [List.length_cons]
        omega
  simpa [LeanExperiments.RunningMedian.ofArray, LeanExperiments.RunningMedian.empty,
    ← Array.foldl_toList] using
    foldTotal values.toList LeanExperiments.RunningMedian.empty

/-- 空状態は、空入力に対する一般不変条件を満たす。 -/
theorem StateInvariant.empty :
    StateInvariant #[] LeanExperiments.RunningMedian.empty := by
  simp [StateInvariant, HeapOrdered, LeanExperiments.RunningMedian.empty,
    maxPrefer, minPrefer]

/-- 空状態への最初の挿入は、値を下側ヒープにだけ置く。 -/
theorem insert_empty_state (value : Nat) :
    LeanExperiments.RunningMedian.insert LeanExperiments.RunningMedian.empty value =
      { lower := #[value], upper := #[] } := by
  simp [LeanExperiments.RunningMedian.insert, LeanExperiments.RunningMedian.empty]

/-- 実装の空状態への1回挿入は、任意の値で更新後の状態不変条件を満たす。 -/
theorem StateInvariant.insert_empty (value : Nat) :
    StateInvariant #[value]
      (LeanExperiments.RunningMedian.insert LeanExperiments.RunningMedian.empty value) := by
  rw [insert_empty_state]
  simp [StateInvariant, HeapOrdered, maxPrefer, minPrefer]

/-- 任意の値を一つだけ処理した実装状態は、1要素入力の不変条件を満たす。

これは有限値の列挙ではなく、値に仮定を置かない長さ1の一般証明であり、
`ofArray_push` による帰納証明の最初の非空ケースを固定する。
-/
theorem StateInvariant.ofArray_singleton (value : Nat) :
    StateInvariant #[value] (LeanExperiments.RunningMedian.ofArray #[value]) := by
  simp [LeanExperiments.RunningMedian.ofArray, insert_empty_state, StateInvariant,
    HeapOrdered, maxPrefer, minPrefer]

/-- 1要素状態に、それより大きな値を挿入した場合の2ヒープ配置を特定する。 -/
theorem ofArray_pair_eq_of_lt {left right : Nat} (hLeft : left < right) :
    LeanExperiments.RunningMedian.ofArray #[left, right] =
      { lower := #[left], upper := #[right] } := by
  change LeanExperiments.RunningMedian.ofArray (#[left].push right) = _
  rw [ofArray_push]
  rw [show LeanExperiments.RunningMedian.ofArray #[left] =
      LeanExperiments.RunningMedian.insert LeanExperiments.RunningMedian.empty left by
    simp [LeanExperiments.RunningMedian.ofArray]]
  rw [insert_empty_state]
  have hRoute : ¬ right ≤ left := by omega
  simp [LeanExperiments.RunningMedian.insert, hRoute, insertHeap_empty,
    rebalanceLoops_eq_self_of_balanced_size]

/-- 昇順の2値を処理した実装状態は、各値を対応するヒープに保持する。 -/
theorem StateInvariant.ofArray_pair_of_lt {left right : Nat} (hLeft : left < right) :
    StateInvariant #[left, right]
      (LeanExperiments.RunningMedian.ofArray #[left, right]) := by
  rw [ofArray_pair_eq_of_lt hLeft]
  simp [StateInvariant, HeapOrdered, maxPrefer, minPrefer]
  omega

/-- 1要素状態に、それ以下の値を挿入した場合は下側の根を上側へ移す。 -/
theorem ofArray_pair_eq_of_ge {left right : Nat} (hRight : right ≤ left) :
    LeanExperiments.RunningMedian.ofArray #[left, right] =
      { lower := #[right], upper := #[left] } := by
  change LeanExperiments.RunningMedian.ofArray (#[left].push right) = _
  rw [ofArray_push]
  rw [show LeanExperiments.RunningMedian.ofArray #[left] =
      LeanExperiments.RunningMedian.insert LeanExperiments.RunningMedian.empty left by
    simp [LeanExperiments.RunningMedian.ofArray]]
  rw [insert_empty_state]
  have hInsert : LeanExperiments.RunningMedian.insertHeap
      LeanExperiments.RunningMedian.maxPrefer #[left] right =
      #[left, right] := by
    have hParent : right ≤ #[left][(#[left].size - 1) / 2]! := by simpa using hRight
    have hPush := insertHeap_eq_push_maxPrefer_of_parent_le #[left] right (Or.inr hParent)
    change LeanExperiments.RunningMedian.insertHeap LeanExperiments.RunningMedian.maxPrefer
      #[left] right = #[left, right] at hPush
    exact hPush
  simp [LeanExperiments.RunningMedian.insert, hRight, hInsert, rebalanceLower_pair,
    rebalanceUpper_eq_self_of_size_le]

/-- 逆順または同値の2値を処理した実装状態は、状態不変条件を満たす。 -/
theorem StateInvariant.ofArray_pair_of_ge {left right : Nat} (hRight : right ≤ left) :
    StateInvariant #[left, right]
      (LeanExperiments.RunningMedian.ofArray #[left, right]) := by
  rw [ofArray_pair_eq_of_ge hRight]
  refine ⟨List.Perm.swap left right [], ?_, ?_, ?_, ?_⟩
  · simp [HeapOrdered]
  · simp [HeapOrdered]
  · intro lowerIndex hLowerIndex upperIndex hUpperIndex
    simp at hLowerIndex hUpperIndex
    subst lowerIndex
    subst upperIndex
    exact hRight
  · simp

/-- 任意の二値入力を処理した状態は、値の順序や重複に関係なく不変条件を満たす。 -/
theorem StateInvariant.ofArray_pair (left right : Nat) :
    StateInvariant #[left, right]
      (LeanExperiments.RunningMedian.ofArray #[left, right]) := by
  by_cases hLeft : left < right
  · exact StateInvariant.ofArray_pair_of_lt hLeft
  · apply StateInvariant.ofArray_pair_of_ge
    omega

/-- 任意の長さ2以下の入力では、`ofArray` の状態が一般不変条件を満たす。

値域や重複に制約を置かず、空・単一要素・二要素の全てを長さで場合分けする。
二要素の場合は値の大小を `StateInvariant.ofArray_pair` が一般に扱う。
-/
theorem StateInvariant.ofArray_size_le_two (values : Array Nat)
    (hSize : values.size ≤ 2) :
    StateInvariant values (LeanExperiments.RunningMedian.ofArray values) := by
  by_cases hZero : values.size = 0
  · have hValues : values = #[] := Array.size_eq_zero_iff.mp hZero
    rw [hValues, ofArray_empty]
    exact StateInvariant.empty
  · by_cases hOne : values.size = 1
    · let value := values[0]!
      have hValues : values = #[value] := by
        apply Array.ext
        · exact hOne
        · intro index hLeft hRight
          have hIndex : index = 0 := by omega
          subst index
          simp [value, hOne]
      rw [hValues]
      exact StateInvariant.ofArray_singleton value
    · have hTwo : values.size = 2 := by omega
      let first := values[0]!
      let second := values[1]!
      have hValues : values = #[first, second] := by
        apply Array.ext
        · exact hTwo
        · intro index hLeft hRight
          have hIndex : index = 0 ∨ index = 1 := by omega
          rcases hIndex with hIndex | hIndex
          · subst index
            simp [first, hTwo]
          · subst index
            simp [second, hTwo]
      rw [hValues]
      exact StateInvariant.ofArray_pair first second

/-- 任意値を挿入した1要素状態から、2要素後の状態不変条件が成り立つ。

空状態からの挿入契約と `ofArray_push` をつなぎ、値の順序にかかわらず
逐次 `insert` による長さ2までの遷移を確認する。
-/
theorem StateInvariant.insert_singleton (root value : Nat) :
    StateInvariant #[root, value]
      (LeanExperiments.RunningMedian.insert
        { lower := #[root], upper := #[] } value) := by
  have hSingleton : LeanExperiments.RunningMedian.ofArray #[root] =
      { lower := #[root], upper := #[] } := by
    simp [LeanExperiments.RunningMedian.ofArray, insert_empty_state]
  rw [← hSingleton]
  rw [← ofArray_push #[root] value]
  simpa using StateInvariant.ofArray_pair root value

/-- 入力の順列を取っても、同じ状態の論理的不変条件は保たれる。

不変条件が入力に依存するのは、二つのヒープを連結した値列が入力の順列であるという
要素保存条件だけである。そのため、逐次処理の順序と状態を固定したまま入力側の
順列を変更しても、この関係は推移性から引き継がれる。
-/
theorem StateInvariant.of_perm_input {input other : Array Nat}
    {state : LeanExperiments.RunningMedian.State}
    (hInvariant : StateInvariant input state)
    (hPerm : input.toList.Perm other.toList) :
    StateInvariant other state := by
  exact ⟨hInvariant.1.trans hPerm, hInvariant.2.1, hInvariant.2.2.1,
    hInvariant.2.2.2.1, hInvariant.2.2.2.2⟩

/-- 状態不変条件下では、任意の Boolean 分類に属する入力要素数が二つのヒープへ分配される。 -/
theorem StateInvariant.countP_partition {input : Array Nat}
    {state : LeanExperiments.RunningMedian.State}
    (hInvariant : StateInvariant input state) (predicate : Nat → Bool) :
    input.toList.countP predicate =
      state.lower.toList.countP predicate + state.upper.toList.countP predicate := by
  rw [← hInvariant.1.countP_eq predicate, List.countP_append]

/-- 状態不変条件下では、二つのヒープの要素数の合計が入力長に一致する。

要素順列保存から従う一般定理であり、再平衡後の総要素数保存を状態単位で扱える。
-/
theorem StateInvariant.size_partition {input : Array Nat}
    {state : LeanExperiments.RunningMedian.State}
    (hInvariant : StateInvariant input state) :
    state.lower.size + state.upper.size = input.size := by
  have hLength := hInvariant.1.length_eq
  simpa [List.length_append] using hLength

/-- 空状態が不変条件を満たすのは、入力も空の場合に限る。

要素保存条件とサイズ分割により、空状態が非空入力を表す可能性を排除する。
-/
theorem StateInvariant.empty_iff_input_empty (input : Array Nat) :
    StateInvariant input LeanExperiments.RunningMedian.empty ↔ input = #[] := by
  constructor
  · intro hInvariant
    have hTotal := StateInvariant.size_partition hInvariant
    simp [LeanExperiments.RunningMedian.empty] at hTotal
    exact Array.size_eq_zero_iff.mp hTotal.symm
  · intro hInput
    subst input
    exact StateInvariant.empty

/-- 不変条件下では、下側ヒープが入力長の切り上げ半分、上側が切り捨て半分を持つ。

合計要素数と下側が同数または1つ多いという均衡条件から、中央値の分割位置を厳密に
求める。
-/
theorem StateInvariant.heap_sizes {input : Array Nat}
    {state : LeanExperiments.RunningMedian.State}
    (hInvariant : StateInvariant input state) :
    state.lower.size = (input.size + 1) / 2 ∧
      state.upper.size = input.size / 2 := by
  have hTotal := StateInvariant.size_partition hInvariant
  rcases hInvariant.2.2.2.2 with hBalanced | hLowerExtra
  · rw [hBalanced] at hTotal
    constructor <;> omega
  · rw [hLowerExtra] at hTotal
    constructor <;> omega

/-- 不変条件下では、入力長の偶奇とヒープ間のサイズ均衡が同値になる。

偶数長なら両ヒープは同数、奇数長なら下側がちょうど1つ多い。この同値は入力長から
状態の分割を判定するときにも、状態の均衡から入力長の偶奇を求めるときにも使える。
-/
theorem StateInvariant.heap_size_parity_iff {input : Array Nat}
    {state : LeanExperiments.RunningMedian.State}
    (hInvariant : StateInvariant input state) :
    (input.size % 2 = 0 ↔ state.lower.size = state.upper.size) ∧
      (input.size % 2 = 1 ↔ state.lower.size = state.upper.size + 1) := by
  have hSizes := StateInvariant.heap_sizes hInvariant
  constructor
  · constructor
    · intro hEven
      rw [hSizes.1, hSizes.2]
      omega
    · intro hEqual
      rw [hSizes.1, hSizes.2] at hEqual
      omega
  · constructor
    · intro hOdd
      rw [hSizes.1, hSizes.2]
      omega
    · intro hLowerExtra
      rw [hSizes.1, hSizes.2] at hLowerExtra
      omega

/-- 不変条件下で各値が入力に現れる回数は、二つのヒープでの出現回数の和である。 -/
theorem StateInvariant.value_count_partition {input : Array Nat}
    {state : LeanExperiments.RunningMedian.State}
    (hInvariant : StateInvariant input state) (value : Nat) :
    input.toList.countP (fun item => decide (item = value)) =
      state.lower.toList.countP (fun item => decide (item = value)) +
        state.upper.toList.countP (fun item => decide (item = value)) := by
  exact StateInvariant.countP_partition hInvariant (fun item => decide (item = value))


end LeanExperiments.Verification.RunningMedian
