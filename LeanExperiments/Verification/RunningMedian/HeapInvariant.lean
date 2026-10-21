import LeanExperiments.Verification.RunningMedian.Operations
import LeanExperiments.Verification.HeapSort.Spec
import Std.WP
import Std.Tactic.Do

/-! # ヒープ順序仕様と挿入時の不変条件

任意の優先関数に対するヒープ順序、例外辺を用いた上昇調整の不変条件、
Boolean 検査器との対応、および挿入後の順序回復をまとめる。 -/

namespace LeanExperiments.Verification.RunningMedian

open Std.WP Lean.Order
set_option experimental.vcgen true

/-- 各親が左右の子より優先されるかを配列全体について確認する。 -/
def heapCheck (prefer : Nat → Nat → Bool) (heap : Array Nat) : Bool :=
  (List.range heap.size).all fun index =>
    let left := 2 * index + 1
    let right := left + 1
    (left ≥ heap.size || decide (prefer heap[left]! heap[index]! = false)) &&
      (right ≥ heap.size || decide (prefer heap[right]! heap[index]! = false))

/-- ヒープ配列で、全ての子が親より優先されないことを表す論理仕様。 -/
def HeapOrdered (prefer : Nat → Nat → Bool) (heap : Array Nat) : Prop :=
  ∀ index, index < heap.size →
    (2 * index + 1 < heap.size →
      prefer heap[2 * index + 1]! heap[index]! = false) ∧
    (2 * index + 2 < heap.size →
      prefer heap[2 * index + 2]! heap[index]! = false)

/-- 指定した子添字から親へ向かう辺だけを除いて、配列がヒープ順序にあること。 -/
def HeapOrderedExceptChild (prefer : Nat → Nat → Bool)
    (heap : Array Nat) (exception : Nat) : Prop :=
  ∀ index, index < heap.size →
    (2 * index + 1 < heap.size →
      2 * index + 1 = exception ∨
        prefer heap[2 * index + 1]! heap[index]! = false) ∧
    (2 * index + 2 < heap.size →
      2 * index + 2 = exception ∨
        prefer heap[2 * index + 2]! heap[index]! = false)

/-- `siftUp` の例外辺と、移動中の値の下にある部分木の上限をまとめる。 -/
def HeapOrderedExceptChildWithSubtreeBound (prefer : Nat → Nat → Bool)
    (heap : Array Nat) (exception : Nat) : Prop :=
  HeapOrderedExceptChild prefer heap exception ∧
    ∀ index, LeanExperiments.Verification.HeapSort.Spec.HeapDescendant exception index →
      index ≠ exception → index < heap.size →
        prefer heap[index]! heap[(exception - 1) / 2]! = false

/-- 例外辺を通らない親子経路では、端点間の非優先関係が推移する。 -/
theorem HeapOrderedExceptChild.prefer_false_of_descendant_avoiding_exception
    {prefer : Nat → Nat → Bool} {heap : Array Nat}
    {exception root index : Nat}
    (hExcept : HeapOrderedExceptChild prefer heap exception)
    (hIrrefl : ∀ value, prefer value value = false)
    (hNotTrans : ∀ first second third,
      prefer first second = false → prefer second third = false →
        prefer first third = false)
    (hPath : LeanExperiments.Verification.HeapSort.Spec.HeapDescendant root index)
    (hAvoid : ¬ LeanExperiments.Verification.HeapSort.Spec.HeapDescendant
      root exception)
    (hIndex : index < heap.size) :
    prefer heap[index]! heap[root]! = false := by
  induction hPath with
  | root => exact hIrrefl heap[root]!
  | left hPath ih =>
      rename_i parent
      have hParent : parent < heap.size := by omega
      have hEdge := (hExcept parent hParent).1 (by omega)
      rcases hEdge with hException | hOrdered
      · have hForbidden :
            LeanExperiments.Verification.HeapSort.Spec.HeapDescendant root exception := by
          simpa [hException] using
            (LeanExperiments.Verification.HeapSort.Spec.HeapDescendant.left hPath)
        exact (hAvoid hForbidden).elim
      · exact hNotTrans _ _ _ hOrdered (ih hParent)
  | right hPath ih =>
      rename_i parent
      have hParent : parent < heap.size := by omega
      have hEdge := (hExcept parent hParent).2 (by omega)
      rcases hEdge with hException | hOrdered
      · have hForbidden :
            LeanExperiments.Verification.HeapSort.Spec.HeapDescendant root exception := by
          simpa [hException] using
            (LeanExperiments.Verification.HeapSort.Spec.HeapDescendant.right hPath)
        exact (hAvoid hForbidden).elim
      · exact hNotTrans _ _ _ hOrdered (ih hParent)

/-- 例外位置を根とする部分木では、全ての子孫が根の値を優先しない。 -/
theorem HeapOrderedExceptChild.prefer_false_of_descendant
    {prefer : Nat → Nat → Bool} {heap : Array Nat}
    {exception index : Nat}
    (hExcept : HeapOrderedExceptChild prefer heap exception)
    (hIrrefl : ∀ value, prefer value value = false)
    (hNotTrans : ∀ first second third,
      prefer first second = false → prefer second third = false →
        prefer first third = false)
    (hPath : LeanExperiments.Verification.HeapSort.Spec.HeapDescendant exception index)
    (hIndex : index < heap.size) :
    prefer heap[index]! heap[exception]! = false := by
  induction hPath with
  | root => exact hIrrefl heap[exception]!
  | left hPath ih =>
      rename_i parent
      have hParent : parent < heap.size := by omega
      have hChildNotException : 2 * parent + 1 ≠ exception := by
        have hLower :=
          LeanExperiments.Verification.HeapSort.Spec.HeapDescendant.root_le hPath
        omega
      have hEdge := (hExcept parent hParent).1 (by omega)
      rcases hEdge with hEdgeException | hOrdered
      · exact (hChildNotException hEdgeException).elim
      · exact hNotTrans _ _ _ hOrdered (ih hParent)
  | right hPath ih =>
      rename_i parent
      have hParent : parent < heap.size := by omega
      have hChildNotException : 2 * parent + 2 ≠ exception := by
        have hLower :=
          LeanExperiments.Verification.HeapSort.Spec.HeapDescendant.root_le hPath
        omega
      have hEdge := (hExcept parent hParent).2 (by omega)
      rcases hEdge with hEdgeException | hOrdered
      · exact (hChildNotException hEdgeException).elim
      · exact hNotTrans _ _ _ hOrdered (ih hParent)

/-- すでにヒープ順序を満たす配列では、有効な添字からの親方向調整は何も変えない。 -/
theorem siftUp_eq_self_of_heapOrdered (prefer : Nat → Nat → Bool)
    (heap : Array Nat) (start : Nat) (hStart : start < heap.size)
    (hOrdered : HeapOrdered prefer heap) :
    LeanExperiments.RunningMedian.siftUp prefer heap start = heap := by
  by_cases hZero : start = 0
  · subst start
    exact siftUp_zero_eq_self prefer heap
  · let parent := (start - 1) / 2
    have hParent : parent < heap.size := by dsimp [parent]; omega
    have hChildren : start = 2 * parent + 1 ∨ start = 2 * parent + 2 := by
      have hDivMod := Nat.mod_add_div (start - 1) 2
      have hMod := Nat.mod_lt (start - 1) (by omega : 0 < 2)
      dsimp [parent]
      omega
    have hStops : prefer heap[start]! heap[parent]! = false := by
      rcases hChildren with hLeft | hRight
      · have hEdge := (hOrdered parent hParent).1 (by omega)
        simpa [hLeft] using hEdge
      · have hEdge := (hOrdered parent hParent).2 (by omega)
        simpa [hRight] using hEdge
    apply siftUp_eq_self_of_stops
    right
    simpa [parent] using hStops

/-- 子が現在位置より優先されないなら、下降候補は現在位置になる。 -/
theorem siftDownBest_eq_index_of_children_stopping (prefer : Nat → Nat → Bool)
    (heap : Array Nat) (index : Nat)
    (hLeftStop : 2 * index + 1 < heap.size →
      prefer heap[2 * index + 1]! heap[index]! = false)
    (hRightStop : 2 * index + 2 < heap.size →
      prefer heap[2 * index + 2]! heap[index]! = false) :
    LeanExperiments.RunningMedian.siftDownBest prefer heap index = index := by
  let left := 2 * index + 1
  let right := 2 * index + 2
  have hLeftNo : left < heap.size → prefer heap[left]! heap[index]! = false := by
    intro hLeft
    simpa [left] using hLeftStop hLeft
  have hRightNo : right < heap.size → prefer heap[right]! heap[index]! = false := by
    intro hRight
    simpa [right] using hRightStop hRight
  have hLeftCheck : (left < heap.size && prefer heap[left]! heap[index]!) = false := by
    by_cases hLeft : left < heap.size
    · have hNo := hLeftNo hLeft
      rw [getElem!_pos heap left hLeft] at hNo
      simp [hLeft, hNo]
    · simp [hLeft]
  have hRightCheck : (right < heap.size && prefer heap[right]! heap[index]!) = false := by
    by_cases hRight : right < heap.size
    · have hNo := hRightNo hRight
      rw [getElem!_pos heap right hRight] at hNo
      simp [hRight, hNo]
    · simp [hRight]
  simp [LeanExperiments.RunningMedian.siftDownBest, left, right, hLeftCheck, hRightCheck]

/-- 下降候補は、現在位置か左右いずれかの子添字である。 -/
theorem siftDownBest_eq_index_or_child (prefer : Nat → Nat → Bool)
    (heap : Array Nat) (index : Nat) :
    LeanExperiments.RunningMedian.siftDownBest prefer heap index = index ∨
      LeanExperiments.RunningMedian.siftDownBest prefer heap index = 2 * index + 1 ∨
      LeanExperiments.RunningMedian.siftDownBest prefer heap index = 2 * index + 2 := by
  let left := 2 * index + 1
  let right := 2 * index + 2
  let takeLeft := left < heap.size && prefer heap[left]! heap[index]!
  let bestLeft := if takeLeft then left else index
  let takeRight := right < heap.size && prefer heap[right]! heap[bestLeft]!
  change (if takeRight then right else bestLeft) = index ∨
    (if takeRight then right else bestLeft) = left ∨
    (if takeRight then right else bestLeft) = right
  by_cases hRight : takeRight = true
  · simp [hRight, left, right]
  · by_cases hLeft : takeLeft = true
    · simp [hRight, bestLeft, hLeft, left, right]
    · simp [hRight, bestLeft, hLeft, left, right]

/-- 子が存在しない添字での下降1反復は、配列・添字を保って停止する。 -/
theorem siftDownStep_eq_identity_of_no_children (prefer : Nat → Nat → Bool)
    (heap : Array Nat) (index : Nat) (hNoChildren : heap.size ≤ 2 * index + 1) :
    LeanExperiments.RunningMedian.siftDownStep prefer heap index =
      (heap, index, false) := by
  have hBest : LeanExperiments.RunningMedian.siftDownBest prefer heap index = index := by
    apply siftDownBest_eq_index_of_children_stopping prefer heap index
    · intro hLeft
      omega
    · intro hRight
      omega
  simp [LeanExperiments.RunningMedian.siftDownStep, hBest]

/-- 既にヒープ順序を満たす位置では、子方向調整の候補は現在位置になる。 -/
theorem siftDownBest_eq_index_of_heapOrdered (prefer : Nat → Nat → Bool)
    (heap : Array Nat) (index : Nat) (hIndex : index < heap.size)
    (hOrdered : HeapOrdered prefer heap) :
    LeanExperiments.RunningMedian.siftDownBest prefer heap index = index := by
  apply siftDownBest_eq_index_of_children_stopping prefer heap index
  · exact fun hLeft => (hOrdered index hIndex).1 hLeft
  · exact fun hRight => (hOrdered index hIndex).2 hRight

/-- 順序済みヒープ上の有効な位置からの子方向調整は配列を変更しない。 -/
theorem siftDown_eq_self_of_heapOrdered (prefer : Nat → Nat → Bool)
    (heap : Array Nat) (start : Nat) (hStart : start < heap.size)
    (hOrdered : HeapOrdered prefer heap) :
    LeanExperiments.RunningMedian.siftDown prefer heap start = heap := by
  generalize hRun : LeanExperiments.RunningMedian.siftDown prefer heap start = result
  apply Id.of_run_eq_wp hRun
  vcgen [LeanExperiments.RunningMedian.siftDown] invariants
  · fun _ state => state.1 = heap ∧ state.2.1 = start
  case vc1 => simp_all
  case vc2 =>
    simp_all [Variant.evalsBelow_ofMeasure_nat, Variant.evalsTo_ofMeasure,
      Assertion.NondetFun.evalsTo_pure]
    rename_i currentHeap currentIndex currentFlag currentMeasure pair hInvariant hFlag
    have hMeasure := siftDownStep_variant_decreases prefer currentHeap currentIndex
    have hBest :
        LeanExperiments.RunningMedian.siftDownBest prefer currentHeap currentIndex = currentIndex := by
      rw [hInvariant.2.1, hInvariant.2.2]
      exact siftDownBest_eq_index_of_heapOrdered prefer heap start hStart hOrdered
    have hStopped :
        (LeanExperiments.RunningMedian.siftDownStep prefer currentHeap currentIndex).2.2 = false := by
      simp [LeanExperiments.RunningMedian.siftDownStep, hBest]
    have hStep := siftDownStep_stopped prefer currentHeap currentIndex hStopped
    constructor
    · simpa [values, index, running, hInvariant.1, hFlag] using hMeasure
    · constructor
      · simpa [values, hInvariant.2.1] using hStep.1
      · simpa [index, hInvariant.2.2] using hStep.2
  case vc3 => simp_all [Variant.evalsTo_ofMeasure, Assertion.NondetFun.evalsTo_pure]

/-- 最小ヒープでは、配列に存在する各子の値が親以上である。 -/
def MinHeap (heap : Array Nat) : Prop :=
  ∀ index, index < heap.size →
    (2 * index + 1 < heap.size → heap[index]! ≤ heap[2 * index + 1]!) ∧
    (2 * index + 2 < heap.size → heap[index]! ≤ heap[2 * index + 2]!)

/-- 指定位置から出る辺だけを例外として許す最小ヒープ条件。 -/
def MinHeapExcept (heap : Array Nat) (exception : Nat) : Prop :=
  ∀ parent, parent < heap.size → parent ≠ exception →
    (2 * parent + 1 < heap.size → heap[parent]! ≤ heap[2 * parent + 1]!) ∧
    (2 * parent + 2 < heap.size → heap[parent]! ≤ heap[2 * parent + 2]!)

/-- 例外位置の子辺も整っていれば、例外付き条件から通常の最小ヒープ順序が従う。 -/
theorem MinHeapExcept.of_ordered_exception_row (heap : Array Nat) (exception : Nat)
    (hExcept : MinHeapExcept heap exception)
    (hRow : exception < heap.size →
      (2 * exception + 1 < heap.size → heap[exception]! ≤ heap[2 * exception + 1]!) ∧
      (2 * exception + 2 < heap.size → heap[exception]! ≤ heap[2 * exception + 2]!)) :
    MinHeap heap := by
  intro parent hParent
  by_cases hException : parent = exception
  · subst parent
    exact hRow hParent
  · exact hExcept parent hParent hException

/-- Booleanのヒープ検査は、論理的な親子優先度条件と同値である。 -/
theorem heapCheck_correct (prefer : Nat → Nat → Bool) (heap : Array Nat) :
    heapCheck prefer heap = true ↔ HeapOrdered prefer heap := by
  unfold heapCheck HeapOrdered
  constructor
  · intro hOrdered index hIndex
    have hAtIndex := (List.all_eq_true.mp hOrdered) index
      (List.mem_range.mpr hIndex)
    have hParts :
        (2 * index + 1 ≥ heap.size ||
          decide (prefer heap[2 * index + 1]! heap[index]! = false)) = true ∧
        (2 * index + 2 ≥ heap.size ||
          decide (prefer heap[2 * index + 2]! heap[index]! = false)) = true := by
      simpa only [Bool.and_eq_true] using hAtIndex
    have hLeftOr :
        decide (2 * index + 1 ≥ heap.size) = true ∨
          decide (prefer heap[2 * index + 1]! heap[index]! = false) = true := by
      simpa only [Bool.or_eq_true] using hParts.1
    have hRightOr :
        decide (2 * index + 2 ≥ heap.size) = true ∨
          decide (prefer heap[2 * index + 2]! heap[index]! = false) = true := by
      simpa only [Bool.or_eq_true] using hParts.2
    constructor
    · intro hChild
      have hAbsent : ¬ 2 * index + 1 ≥ heap.size := by omega
      rcases hLeftOr with hAbsentBool | hNotPreferred
      · exact False.elim (hAbsent (of_decide_eq_true hAbsentBool))
      · exact of_decide_eq_true hNotPreferred
    · intro hChild
      have hAbsent : ¬ 2 * index + 2 ≥ heap.size := by omega
      rcases hRightOr with hAbsentBool | hNotPreferred
      · exact False.elim (hAbsent (of_decide_eq_true hAbsentBool))
      · exact of_decide_eq_true hNotPreferred
  · intro hOrdered
    apply List.all_eq_true.mpr
    intro index hIndex
    have hIndexBound : index < heap.size := List.mem_range.mp hIndex
    obtain ⟨hLeft, hRight⟩ := hOrdered index hIndexBound
    have hLeftCheck :
        (decide (2 * index + 1 ≥ heap.size) ||
          decide (prefer heap[2 * index + 1]! heap[index]! = false)) = true := by
      have hLeftOr : decide (2 * index + 1 ≥ heap.size) = true ∨
          decide (prefer heap[2 * index + 1]! heap[index]! = false) = true := by
        by_cases hChild : 2 * index + 1 < heap.size
        · exact Or.inr (decide_eq_true (hLeft hChild))
        · left
          exact decide_eq_true (by omega)
      simpa only [Bool.or_eq_true] using hLeftOr
    have hRightCheck :
        (decide (2 * index + 2 ≥ heap.size) ||
          decide (prefer heap[2 * index + 2]! heap[index]! = false)) = true := by
      have hRightOr : decide (2 * index + 2 ≥ heap.size) = true ∨
          decide (prefer heap[2 * index + 2]! heap[index]! = false) = true := by
        by_cases hChild : 2 * index + 2 < heap.size
        · exact Or.inr (decide_eq_true (hRight hChild))
        · left
          exact decide_eq_true (by omega)
      simpa only [Bool.or_eq_true] using hRightOr
    rw [Bool.and_eq_true]
    exact ⟨hLeftCheck, hRightCheck⟩

/-- 順序済みヒープへの末尾追加では、新しい葉につながる辺以外は順序を保つ。

追加前の全ての親子辺は値も添字も変わらない。新しい末尾要素との辺だけを例外として
明示するため、後続の `siftUp` 反復で例外辺が親方向へ移動する不変条件に使える。
-/
theorem HeapOrdered.push_except_last (prefer : Nat → Nat → Bool)
    (heap : Array Nat) (value : Nat) (hOrdered : HeapOrdered prefer heap) :
    HeapOrderedExceptChild prefer (heap.push value) heap.size := by
  intro index hIndex
  have hPushSize : (heap.push value).size = heap.size + 1 := by simp
  have hGetOld (position : Nat) (hPosition : position < heap.size) :
      (heap.push value)[position]! = heap[position]! := by
    rw [getElem!_pos (heap.push value) position (by simp; omega),
      getElem!_pos heap position hPosition]
    simp [Array.getElem_push, hPosition]
  constructor
  · intro hLeft
    by_cases hNewChild : 2 * index + 1 = heap.size
    · exact Or.inl hNewChild
    · right
      have hOldChild : 2 * index + 1 < heap.size := by
        have hChildBound : 2 * index + 1 < heap.size + 1 := by
          simpa [hPushSize] using hLeft
        omega
      have hIndexOld : index < heap.size := by omega
      have hOld := hOrdered index hIndexOld
      rw [hGetOld (2 * index + 1) hOldChild, hGetOld index hIndexOld]
      exact hOld.1 hOldChild
  · intro hRight
    by_cases hNewChild : 2 * index + 2 = heap.size
    · exact Or.inl hNewChild
    · right
      have hOldChild : 2 * index + 2 < heap.size := by
        have hChildBound : 2 * index + 2 < heap.size + 1 := by
          simpa [hPushSize] using hRight
        omega
      have hIndexOld : index < heap.size := by omega
      have hOld := hOrdered index hIndexOld
      rw [hGetOld (2 * index + 2) hOldChild, hGetOld index hIndexOld]
      exact hOld.2 hOldChild

/-- 末尾追加は、例外辺と空の子孫部分木をもつ `siftUp` 初期不変条件を作る。 -/
theorem HeapOrdered.push_siftUp_initial_invariant (prefer : Nat → Nat → Bool)
    (heap : Array Nat) (value : Nat) (hOrdered : HeapOrdered prefer heap) :
    HeapOrderedExceptChildWithSubtreeBound prefer (heap.push value) heap.size := by
  constructor
  · exact HeapOrdered.push_except_last prefer heap value hOrdered
  · intro index hPath hNotRoot hIndex
    have hPathLower :=
      LeanExperiments.Verification.HeapSort.Spec.HeapDescendant.root_le hPath
    have hPushSize : (heap.push value).size = heap.size + 1 := by simp
    omega

/-- siftUp 交換後も、例外位置の下の値は移動してきた旧親の値を優先しない。 -/
theorem HeapOrderedExceptChildWithSubtreeBound.subtree_bound_after_swap
    {prefer : Nat → Nat → Bool} {heap : Array Nat} {exception index : Nat}
    (hInvariant : HeapOrderedExceptChildWithSubtreeBound prefer heap exception)
    (hExceptionPositive : 0 < exception) (hExceptionBound : exception < heap.size)
    (hPath : LeanExperiments.Verification.HeapSort.Spec.HeapDescendant exception index)
    (hStrict : index ≠ exception) (hIndex : index < heap.size) :
    prefer
      (LeanExperiments.RunningMedian.swap heap exception ((exception - 1) / 2))[index]!
      (LeanExperiments.RunningMedian.swap heap exception ((exception - 1) / 2))[exception]! =
        false := by
  have hIndexAfterException : exception < index := by
    have hRootLe :=
      LeanExperiments.Verification.HeapSort.Spec.HeapDescendant.root_le hPath
    omega
  have hParentBound : (exception - 1) / 2 < heap.size := by omega
  have hIndexNotParent : index ≠ (exception - 1) / 2 := by omega
  have hOutside := swap_getElem!_eq_of_outside heap exception ((exception - 1) / 2)
    index hExceptionBound hParentBound hIndex hStrict hIndexNotParent
  have hAt := swap_getElem!_at_positions heap exception ((exception - 1) / 2)
    hExceptionBound hParentBound
  rw [hOutside, hAt.1]
  exact hInvariant.2 index hPath hStrict hIndex

/-- 例外辺を避ける部分木は、親との交換後も移動した旧親の値との順序を保つ。 -/
theorem HeapOrderedExceptChild.prefer_false_of_unaffected_descendant_after_swap
    {prefer : Nat → Nat → Bool} {heap : Array Nat}
    {exception parent root index : Nat}
    (hExcept : HeapOrderedExceptChild prefer heap exception)
    (hIrrefl : ∀ value, prefer value value = false)
    (hNotTrans : ∀ first second third,
      prefer first second = false → prefer second third = false →
        prefer first third = false)
    (hExceptionPositive : 0 < exception) (hExceptionBound : exception < heap.size)
    (hParent : parent = (exception - 1) / 2)
    (hPath : LeanExperiments.Verification.HeapSort.Spec.HeapDescendant root index)
    (hAvoid : ¬ LeanExperiments.Verification.HeapSort.Spec.HeapDescendant root exception)
    (hRootNotPreferParent : prefer heap[root]! heap[parent]! = false)
    (hIndexNotParent : index ≠ parent) (hIndex : index < heap.size) :
    prefer
      (LeanExperiments.RunningMedian.swap heap exception parent)[index]!
      (LeanExperiments.RunningMedian.swap heap exception parent)[exception]! = false := by
  have hIndexNotException : index ≠ exception := by
    intro hSame
    apply hAvoid
    simpa [hSame] using hPath
  have hNotPreferred :=
    prefer_false_of_descendant_avoiding_exception hExcept hIrrefl hNotTrans
      hPath hAvoid hIndex
  have hNotPreferredParent := hNotTrans _ _ _ hNotPreferred hRootNotPreferParent
  have hParentBound : parent < heap.size := by rw [hParent]; omega
  have hOutside := swap_getElem!_eq_of_outside heap exception parent index
    hExceptionBound hParentBound hIndex hIndexNotException hIndexNotParent
  have hAt := swap_getElem!_at_positions heap exception parent hExceptionBound hParentBound
  rw [hOutside, hAt.1]
  exact hNotPreferredParent

/-- 例外辺の兄弟側にある任意深さの子孫は、交換後も旧親値を優先しない。 -/
theorem HeapOrderedExceptChild.prefer_false_of_sibling_descendant_after_swap
    {prefer : Nat → Nat → Bool} {heap : Array Nat}
    {exception parent sibling index : Nat}
    (hExcept : HeapOrderedExceptChild prefer heap exception)
    (hIrrefl : ∀ value, prefer value value = false)
    (hNotTrans : ∀ first second third,
      prefer first second = false → prefer second third = false →
        prefer first third = false)
    (hExceptionChild : exception = 2 * parent + 1 ∨ exception = 2 * parent + 2)
    (hSiblingChild : sibling = 2 * parent + 1 ∨ sibling = 2 * parent + 2)
    (hSiblingNotException : sibling ≠ exception)
    (hExceptionBound : exception < heap.size)
    (hSiblingPath :
      LeanExperiments.Verification.HeapSort.Spec.HeapDescendant sibling index)
    (hParent : parent = (exception - 1) / 2)
    (hIndex : index < heap.size) :
    prefer
      (LeanExperiments.RunningMedian.swap heap exception parent)[index]!
      (LeanExperiments.RunningMedian.swap heap exception parent)[exception]! = false := by
  have hAvoid :=
    LeanExperiments.Verification.HeapSort.Spec.HeapDescendant.not_descendant_of_sibling_child
      hSiblingChild hExceptionChild hSiblingNotException
      (LeanExperiments.Verification.HeapSort.Spec.HeapDescendant.root exception)
  have hSiblingBound : sibling < heap.size := by
    have hSiblingLeIndex := hSiblingPath.root_le
    omega
  have hParentBound : parent < heap.size := by
    rcases hSiblingChild with hLeft | hRight <;> omega
  have hSiblingNotPreferParent : prefer heap[sibling]! heap[parent]! = false := by
    have hParentEdges := hExcept parent hParentBound
    rcases hSiblingChild with hLeft | hRight
    · have hEdge := hParentEdges.1 (by omega)
      rcases hEdge with hExceptionEdge | hOrdered
      · exact (hSiblingNotException (by simpa [hLeft] using hExceptionEdge)).elim
      · simpa [hLeft] using hOrdered
    · have hEdge := hParentEdges.2 (by omega)
      rcases hEdge with hExceptionEdge | hOrdered
      · exact (hSiblingNotException (by simpa [hRight] using hExceptionEdge)).elim
      · simpa [hRight] using hOrdered
  have hIndexNotParent : index ≠ parent := by
    intro hSame
    have hSiblingLeIndex := hSiblingPath.root_le
    rcases hSiblingChild with hLeft | hRight <;> omega
  exact prefer_false_of_unaffected_descendant_after_swap hExcept hIrrefl hNotTrans
    (by rcases hExceptionChild with hLeft | hRight <;> omega)
    hExceptionBound hParent hSiblingPath hAvoid hSiblingNotPreferParent
    hIndexNotParent hIndex

/-- 子が親を優先して交換した辺は、優先関係の非対称性により交換後は正しい向きになる。 -/
theorem prefer_false_of_swap_reverses_preferred_edge
    {prefer : Nat → Nat → Bool} {heap : Array Nat} {exception : Nat}
    (hExceptionPositive : 0 < exception) (hExceptionBound : exception < heap.size)
    (hPrefer : prefer heap[exception]! heap[(exception - 1) / 2]! = true)
    (hAsymm : ∀ child parent, prefer child parent = true →
      prefer parent child = false) :
    prefer
      (LeanExperiments.RunningMedian.swap heap exception ((exception - 1) / 2))[exception]!
      (LeanExperiments.RunningMedian.swap heap exception ((exception - 1) / 2))[(exception - 1) / 2]! =
        false := by
  have hParentBound : (exception - 1) / 2 < heap.size := by omega
  have hAt := swap_getElem!_at_positions heap exception ((exception - 1) / 2)
    hExceptionBound hParentBound
  rw [hAt.1, hAt.2]
  exact hAsymm _ _ hPrefer

/-- 交換で親へ上がった値は、旧親のもう一方の子よりも優先される。 -/
theorem prefer_false_of_other_child_after_swap
    {prefer : Nat → Nat → Bool} {heap : Array Nat}
    {exception parent sibling : Nat}
    (hExcept : HeapOrderedExceptChild prefer heap exception)
    (hExceptionBound : exception < heap.size) (hParentBound : parent < heap.size)
    (hParent : parent = (exception - 1) / 2)
    (hSibling : sibling = 2 * parent + 1 ∨ sibling = 2 * parent + 2)
    (hSiblingNotException : sibling ≠ exception) (hSiblingBound : sibling < heap.size)
    (hPrefer : prefer heap[exception]! heap[parent]! = true)
    (hPreferTrans : ∀ first second third,
      prefer first second = true → prefer second third = true →
        prefer first third = true) :
    prefer (LeanExperiments.RunningMedian.swap heap exception parent)[sibling]!
      (LeanExperiments.RunningMedian.swap heap exception parent)[parent]! = false := by
  have hEdges := hExcept parent hParentBound
  have hOldEdge : prefer heap[sibling]! heap[parent]! = false := by
    rcases hSibling with hLeft | hRight
    · have hEdge := hEdges.1 (by omega)
      rcases hEdge with hExceptionEdge | hOrdered
      · exact (hSiblingNotException (by simpa [hLeft] using hExceptionEdge)).elim
      · simpa [hLeft] using hOrdered
    · have hEdge := hEdges.2 (by omega)
      rcases hEdge with hExceptionEdge | hOrdered
      · exact (hSiblingNotException (by simpa [hRight] using hExceptionEdge)).elim
      · simpa [hRight] using hOrdered
  have hSiblingNotParent : sibling ≠ parent := by
    rcases hSibling with hLeft | hRight <;> omega
  have hSiblingNotPreferred : prefer heap[sibling]! heap[exception]! = false := by
    cases hCompare : prefer heap[sibling]! heap[exception]! with
    | false => rfl
    | true =>
        have hContradiction := hPreferTrans _ _ _ hCompare hPrefer
        rw [hOldEdge] at hContradiction
        exact hContradiction.symm
  have hOutside := swap_getElem!_eq_of_outside heap exception parent sibling
    hExceptionBound hParentBound hSiblingBound hSiblingNotException hSiblingNotParent
  have hAt := swap_getElem!_at_positions heap exception parent
    hExceptionBound hParentBound
  rw [hOutside, hAt.2]
  exact hSiblingNotPreferred

/-- 交換後、新しく例外位置になった親から出る左右の辺は順序を保つ。 -/
theorem HeapOrderedExceptChild.parent_row_after_swap
    {prefer : Nat → Nat → Bool} {heap : Array Nat} {exception parent : Nat}
    (hInvariant : HeapOrderedExceptChildWithSubtreeBound prefer heap exception)
    (hExceptionPositive : 0 < exception) (hExceptionBound : exception < heap.size)
    (hParentBound : parent < heap.size)
    (hParent : parent = (exception - 1) / 2)
    (hPrefer : prefer heap[exception]! heap[parent]! = true)
    (hAsymm : ∀ child parent, prefer child parent = true →
      prefer parent child = false)
    (hPreferTrans : ∀ first second third,
      prefer first second = true → prefer second third = true →
        prefer first third = true) :
    let swapped := LeanExperiments.RunningMedian.swap heap exception parent
    (2 * parent + 1 < swapped.size →
      prefer swapped[2 * parent + 1]! swapped[parent]! = false) ∧
    (2 * parent + 2 < swapped.size →
      prefer swapped[2 * parent + 2]! swapped[parent]! = false) := by
  let swapped := LeanExperiments.RunningMedian.swap heap exception parent
  have hSwapSize :
      (LeanExperiments.RunningMedian.swap heap exception parent).size = heap.size := by
    simp [LeanExperiments.RunningMedian.swap]
  have hSwappedSize : swapped.size = heap.size := by simpa [swapped] using hSwapSize
  have hChildren : exception = 2 * parent + 1 ∨ exception = 2 * parent + 2 := by
    have hDivMod := Nat.mod_add_div (exception - 1) 2
    have hMod := Nat.mod_lt (exception - 1) (by omega : 0 < 2)
    rw [hParent]
    omega
  have hAt := swap_getElem!_at_positions heap exception parent hExceptionBound hParentBound
  have hSwappedEdge : prefer swapped[exception]! swapped[parent]! = false := by
    change prefer
      (LeanExperiments.RunningMedian.swap heap exception parent)[exception]!
      (LeanExperiments.RunningMedian.swap heap exception parent)[parent]! = false
    rw [hAt.1, hAt.2]
    exact hAsymm _ _ hPrefer
  have hSwappedSizeEq : swapped.size = heap.size := hSwappedSize
  constructor
  · intro hLeft
    have hLeftBound : 2 * parent + 1 < heap.size := by
      change 2 * parent + 1 < swapped.size at hLeft
      rw [hSwappedSizeEq] at hLeft
      exact hLeft
    rcases hChildren with hExceptionLeft | hExceptionRight
    · rw [← hExceptionLeft]
      exact hSwappedEdge
    · have hSibling := prefer_false_of_other_child_after_swap
        hInvariant.1 hExceptionBound hParentBound hParent (Or.inl rfl)
        (by omega) hLeftBound hPrefer hPreferTrans
      change prefer swapped[2 * parent + 1]! swapped[parent]! = false
      exact hSibling
  · intro hRight
    have hRightBound : 2 * parent + 2 < heap.size := by
      change 2 * parent + 2 < swapped.size at hRight
      rw [hSwappedSizeEq] at hRight
      exact hRight
    rcases hChildren with hExceptionLeft | hExceptionRight
    · have hSibling := prefer_false_of_other_child_after_swap
        hInvariant.1 hExceptionBound hParentBound hParent (Or.inr rfl)
        (by omega) hRightBound hPrefer hPreferTrans
      change prefer swapped[2 * parent + 2]! swapped[parent]! = false
      exact hSibling
    · rw [← hExceptionRight]
      exact hSwappedEdge

/-- siftUp の交換後、値が下がった旧例外位置から出る左右の辺も順序を保つ。 -/
theorem HeapOrderedExceptChild.old_exception_row_after_swap
    {prefer : Nat → Nat → Bool} {heap : Array Nat} {exception : Nat}
    (hInvariant : HeapOrderedExceptChildWithSubtreeBound prefer heap exception)
    (hExceptionPositive : 0 < exception) (hExceptionBound : exception < heap.size) :
    let swapped :=
      LeanExperiments.RunningMedian.swap heap exception ((exception - 1) / 2)
    (2 * exception + 1 < heap.size →
      prefer swapped[2 * exception + 1]! swapped[exception]! = false) ∧
    (2 * exception + 2 < heap.size →
      prefer swapped[2 * exception + 2]! swapped[exception]! = false) := by
  constructor
  · intro hLeft
    exact hInvariant.subtree_bound_after_swap hExceptionPositive hExceptionBound
      (LeanExperiments.Verification.HeapSort.Spec.HeapDescendant.left
        (LeanExperiments.Verification.HeapSort.Spec.HeapDescendant.root exception))
      (by omega) hLeft
  · intro hRight
    exact hInvariant.subtree_bound_after_swap hExceptionPositive hExceptionBound
      (LeanExperiments.Verification.HeapSort.Spec.HeapDescendant.right
        (LeanExperiments.Verification.HeapSort.Spec.HeapDescendant.root exception))
      (by omega) hRight

/-- 交換で上がった値の祖父は、旧親値を優先しない。 -/
theorem HeapOrderedExceptChild.prefer_false_parent_of_parent_after_swap
    {prefer : Nat → Nat → Bool} {heap : Array Nat} {exception parent : Nat}
    (hExcept : HeapOrderedExceptChild prefer heap exception)
    (hExceptionPositive : 0 < exception) (hExceptionBound : exception < heap.size)
    (hParent : parent = (exception - 1) / 2)
    (hPrefer : prefer heap[exception]! heap[parent]! = true)
    (hAsymm : ∀ child parent, prefer child parent = true →
      prefer parent child = false) :
    prefer heap[parent]!
      (LeanExperiments.RunningMedian.swap heap exception parent)[(parent - 1) / 2]! = false := by
  by_cases hParentZero : parent = 0
  · have hParentExprZero : (exception - 1) / 2 = 0 := by
      rw [← hParent]
      exact hParentZero
    rw [hParent, hParentExprZero]
    have hAt := swap_getElem!_at_positions heap exception 0 hExceptionBound (by omega)
    rw [hAt.2]
    have hPreferZero : prefer heap[exception]! heap[0]! = true := by
      simpa [hParentZero] using hPrefer
    exact hAsymm _ _ hPreferZero
  · let grandparent := (parent - 1) / 2
    have hParentChild : parent = 2 * grandparent + 1 ∨
        parent = 2 * grandparent + 2 := by
      have hDivMod := Nat.mod_add_div (parent - 1) 2
      have hMod := Nat.mod_lt (parent - 1) (by omega : 0 < 2)
      dsimp [grandparent]
      omega
    have hGrandparentBound : grandparent < heap.size := by
      have hParentBound : parent < heap.size := by rw [hParent]; omega
      rcases hParentChild with hLeft | hRight <;> omega
    have hParentNotException : parent ≠ exception := by
      rw [hParent]
      omega
    have hGrandparentEdges := hExcept grandparent hGrandparentBound
    have hOrderedEdge : prefer heap[parent]! heap[grandparent]! = false := by
      rcases hParentChild with hLeft | hRight
      · have hEdge := hGrandparentEdges.1 (by omega)
        rcases hEdge with hExceptionEdge | hOrdered
        · exact (hParentNotException (by simpa [hLeft] using hExceptionEdge)).elim
        · simpa [hLeft] using hOrdered
      · have hEdge := hGrandparentEdges.2 (by omega)
        rcases hEdge with hExceptionEdge | hOrdered
        · exact (hParentNotException (by simpa [hRight] using hExceptionEdge)).elim
        · simpa [hRight] using hOrdered
    have hGrandparentOutside := swap_getElem!_eq_of_outside heap exception parent
      grandparent hExceptionBound (by rw [hParent]; omega) hGrandparentBound
      (by omega) (by omega)
    change prefer heap[parent]!
      (LeanExperiments.RunningMedian.swap heap exception parent)[grandparent]! = false
    rw [hGrandparentOutside]
    exact hOrderedEdge

/-- siftUp の交換で、親子辺の例外位置を一段上へ移し、全ての辺条件を保つ。 -/
theorem HeapOrderedExceptChild.swap_up_preserves_exceptChild
    {prefer : Nat → Nat → Bool} {heap : Array Nat} {exception parent : Nat}
    (hInvariant : HeapOrderedExceptChildWithSubtreeBound prefer heap exception)
    (hExceptionPositive : 0 < exception) (hExceptionBound : exception < heap.size)
    (hParentBound : parent < heap.size)
    (hParent : parent = (exception - 1) / 2)
    (hPrefer : prefer heap[exception]! heap[parent]! = true)
    (hAsymm : ∀ child parent, prefer child parent = true →
      prefer parent child = false)
    (hPreferTrans : ∀ first second third,
      prefer first second = true → prefer second third = true →
        prefer first third = true) :
    HeapOrderedExceptChild prefer
      (LeanExperiments.RunningMedian.swap heap exception parent) parent := by
  have hParentRow := parent_row_after_swap hInvariant hExceptionPositive
    hExceptionBound hParentBound hParent hPrefer hAsymm hPreferTrans
  have hExceptionRow := old_exception_row_after_swap hInvariant
    hExceptionPositive hExceptionBound
  have hChildren : exception = 2 * parent + 1 ∨ exception = 2 * parent + 2 := by
    have hDivMod := Nat.mod_add_div (exception - 1) 2
    have hMod := Nat.mod_lt (exception - 1) (by omega : 0 < 2)
    rw [hParent]
    omega
  intro index hIndex
  by_cases hAtParent : index = parent
  · subst index
    constructor
    · intro hLeft
      right
      exact hParentRow.1 hLeft
    · intro hRight
      right
      exact hParentRow.2 hRight
  · by_cases hAtException : index = exception
    · subst index
      constructor
      · intro hLeft
        right
        have hLeftBound : 2 * exception + 1 < heap.size := by
          simpa [LeanExperiments.RunningMedian.swap] using hLeft
        simpa [hParent] using hExceptionRow.1 hLeftBound
      · intro hRight
        right
        have hRightBound : 2 * exception + 2 < heap.size := by
          simpa [LeanExperiments.RunningMedian.swap] using hRight
        simpa [hParent] using hExceptionRow.2 hRightBound
    · have hIndexBound : index < heap.size := by
        simpa [LeanExperiments.RunningMedian.swap] using hIndex
      have hIndexNotException : index ≠ exception := hAtException
      have hIndexNotParent : index ≠ parent := hAtParent
      have hOldEdges := hInvariant.1 index hIndexBound
      constructor
      · intro hLeft
        have hLeftBound : 2 * index + 1 < heap.size := by
          simpa [LeanExperiments.RunningMedian.swap] using hLeft
        by_cases hChildIsNewException : 2 * index + 1 = parent
        · exact Or.inl hChildIsNewException
        · have hChildNotOldException : 2 * index + 1 ≠ exception := by
            intro hSame
            rcases hChildren with hExceptionLeft | hExceptionRight <;> omega
          rcases hOldEdges.1 hLeftBound with hOldExceptionEdge | hOldOrdered
          · exact (hChildNotOldException hOldExceptionEdge).elim
          · right
            have hChildOutside := swap_getElem!_eq_of_outside heap exception parent
              (2 * index + 1) hExceptionBound hParentBound hLeftBound
              hChildNotOldException hChildIsNewException
            have hParentOutside := swap_getElem!_eq_of_outside heap exception parent
              index hExceptionBound hParentBound hIndexBound
              hIndexNotException hIndexNotParent
            rw [hChildOutside, hParentOutside]
            exact hOldOrdered
      · intro hRight
        have hRightBound : 2 * index + 2 < heap.size := by
          simpa [LeanExperiments.RunningMedian.swap] using hRight
        by_cases hChildIsNewException : 2 * index + 2 = parent
        · exact Or.inl hChildIsNewException
        · have hChildNotOldException : 2 * index + 2 ≠ exception := by
            intro hSame
            rcases hChildren with hExceptionLeft | hExceptionRight <;> omega
          rcases hOldEdges.2 hRightBound with hOldExceptionEdge | hOldOrdered
          · exact (hChildNotOldException hOldExceptionEdge).elim
          · right
            have hChildOutside := swap_getElem!_eq_of_outside heap exception parent
              (2 * index + 2) hExceptionBound hParentBound hRightBound
              hChildNotOldException hChildIsNewException
            have hParentOutside := swap_getElem!_eq_of_outside heap exception parent
              index hExceptionBound hParentBound hIndexBound
              hIndexNotException hIndexNotParent
            rw [hChildOutside, hParentOutside]
            exact hOldOrdered

/-- 一段の siftUp 交換は、例外辺とその下の部分木上限を親位置へ移す。 -/
theorem HeapOrderedExceptChild.swap_up_preserves_invariant
    {prefer : Nat → Nat → Bool} {heap : Array Nat} {exception parent : Nat}
    (hInvariant : HeapOrderedExceptChildWithSubtreeBound prefer heap exception)
    (hExceptionPositive : 0 < exception) (hExceptionBound : exception < heap.size)
    (hParentBound : parent < heap.size)
    (hParent : parent = (exception - 1) / 2)
    (hPrefer : prefer heap[exception]! heap[parent]! = true)
    (hAsymm : ∀ child parent, prefer child parent = true →
      prefer parent child = false)
    (hPreferTrans : ∀ first second third,
      prefer first second = true → prefer second third = true →
        prefer first third = true)
    (hIrrefl : ∀ value, prefer value value = false)
    (hNotTrans : ∀ first second third,
      prefer first second = false → prefer second third = false →
        prefer first third = false) :
    HeapOrderedExceptChildWithSubtreeBound prefer
      (LeanExperiments.RunningMedian.swap heap exception parent) parent := by
  constructor
  · exact swap_up_preserves_exceptChild hInvariant hExceptionPositive
      hExceptionBound hParentBound hParent hPrefer hAsymm hPreferTrans
  · intro index hPath hNotRoot hIndex
    have hSwapSize :
        (LeanExperiments.RunningMedian.swap heap exception parent).size = heap.size := by
      simp [LeanExperiments.RunningMedian.swap]
    have hIndexBound : index < heap.size := by
      simpa [hSwapSize] using hIndex
    have hParentLtIndex : parent < index := by
      have hParentLeIndex := hPath.root_le
      omega
    obtain ⟨child, hChild, hChildPath⟩ := hPath.exists_first_child hParentLtIndex
    have hParentNotGrandparent := prefer_false_parent_of_parent_after_swap
      hInvariant.1 hExceptionPositive hExceptionBound hParent hPrefer hAsymm
    by_cases hChildIsException : child = exception
    · subst child
      by_cases hIndexIsException : index = exception
      · subst index
        have hAt := swap_getElem!_at_positions heap exception parent
          hExceptionBound hParentBound
        rw [hAt.1]
        exact hParentNotGrandparent
      · have hIndexNotParent : index ≠ parent := by
          intro hSame
          have hExceptionLeIndex := hChildPath.root_le
          omega
        have hIndexNotException := hIndexIsException
        have hOldSubtreeBound := hInvariant.2 index hChildPath hIndexNotException hIndexBound
        rw [← hParent] at hOldSubtreeBound
        have hOutside := swap_getElem!_eq_of_outside heap exception parent index
          hExceptionBound hParentBound hIndexBound hIndexNotException hIndexNotParent
        rw [hOutside]
        exact hNotTrans _ _ _ hOldSubtreeBound hParentNotGrandparent
    · have hSiblingBound := prefer_false_of_sibling_descendant_after_swap
        hInvariant.1 hIrrefl hNotTrans hChildren hChild hChildIsException
        hExceptionBound hChildPath hParent hIndexBound
      have hAt := swap_getElem!_at_positions heap exception parent
        hExceptionBound hParentBound
      rw [hAt.1] at hSiblingBound
      exact hNotTrans _ _ _ hSiblingBound hParentNotGrandparent
where
  hChildren : exception = 2 * parent + 1 ∨ exception = 2 * parent + 2 := by
    have hDivMod := Nat.mod_add_div (exception - 1) 2
    have hMod := Nat.mod_lt (exception - 1) (by omega : 0 < 2)
    rw [hParent]
    omega

/-- `siftUp` の1回の交換は、配列長と要素順列を保ちながら例外辺を親へ移す。 -/
theorem HeapOrderedExceptChild.swap_up_contract
    {prefer : Nat → Nat → Bool} {heap : Array Nat} {exception parent : Nat}
    (hInvariant : HeapOrderedExceptChildWithSubtreeBound prefer heap exception)
    (hExceptionPositive : 0 < exception) (hExceptionBound : exception < heap.size)
    (hParentBound : parent < heap.size)
    (hParent : parent = (exception - 1) / 2)
    (hPrefer : prefer heap[exception]! heap[parent]! = true)
    (hAsymm : ∀ child parent, prefer child parent = true →
      prefer parent child = false)
    (hPreferTrans : ∀ first second third,
      prefer first second = true → prefer second third = true →
        prefer first third = true) :
    let swapped := LeanExperiments.RunningMedian.swap heap exception parent
    swapped.size = heap.size ∧
      swapped.toList.Perm heap.toList ∧
      HeapOrderedExceptChild prefer swapped parent := by
  dsimp
  constructor
  · simp [LeanExperiments.RunningMedian.swap]
  constructor
  · exact swap_perm heap exception parent hExceptionBound hParentBound
  · exact HeapOrderedExceptChild.swap_up_preserves_exceptChild hInvariant
      hExceptionPositive hExceptionBound hParentBound hParent hPrefer hAsymm
      hPreferTrans

/-- 例外辺の比較が停止条件を満たせば、例外辺仕様から全体のヒープ順序が従う。 -/
theorem HeapOrdered.of_exceptChild_of_stops (prefer : Nat → Nat → Bool)
    {heap : Array Nat} {exception : Nat}
    (hExcept : HeapOrderedExceptChild prefer heap exception)
    (hStops : ∀ parent, parent < heap.size →
      (2 * parent + 1 = exception →
        prefer heap[2 * parent + 1]! heap[parent]! = false) ∧
      (2 * parent + 2 = exception →
        prefer heap[2 * parent + 2]! heap[parent]! = false)) :
    HeapOrdered prefer heap := by
  intro parent hParent
  have hEdges := hExcept parent hParent
  have hStopEdges := hStops parent hParent
  constructor
  · intro hLeft
    rcases hEdges.1 hLeft with hException | hOrdered
    · exact hStopEdges.1 hException
    · exact hOrdered
  · intro hRight
    rcases hEdges.2 hRight with hException | hOrdered
    · exact hStopEdges.2 hException
    · exact hOrdered

/-- 例外辺の親との比較が偽なら、その辺を含めて全体の順序が成立する。 -/
theorem HeapOrdered.of_exceptChild_of_parent_stop (prefer : Nat → Nat → Bool)
    {heap : Array Nat} {exception : Nat}
    (hExcept : HeapOrderedExceptChild prefer heap exception)
    (hStopped : exception = 0 ∨
      prefer heap[exception]! heap[(exception - 1) / 2]! = false) :
    HeapOrdered prefer heap := by
  apply HeapOrdered.of_exceptChild_of_stops prefer hExcept
  intro parent hParent
  constructor
  · intro hLeft
    rcases hStopped with hRoot | hCompare
    · omega
    · have hParentEq : parent = (exception - 1) / 2 := by omega
      rw [hLeft, hParentEq]
      exact hCompare
  · intro hRight
    rcases hStopped with hRoot | hCompare
    · omega
    · have hParentEq : parent = (exception - 1) / 2 := by omega
      rw [hRight, hParentEq]
      exact hCompare

/-- 拡張例外辺不変条件のもとで停止する `siftUp` は、全ヒープ順序を満たす。 -/
theorem siftUp_heapOrdered_of_stops (prefer : Nat → Nat → Bool)
    (heap : Array Nat) (start : Nat)
    (hInvariant : HeapOrderedExceptChildWithSubtreeBound prefer heap start)
    (hStopped : start = 0 ∨
      prefer heap[start]! heap[(start - 1) / 2]! = false) :
    HeapOrdered prefer (LeanExperiments.RunningMedian.siftUp prefer heap start) := by
  rw [LeanExperiments.Verification.RunningMedian.siftUp_eq_self_of_stops
    prefer heap start hStopped]
  exact HeapOrdered.of_exceptChild_of_parent_stop prefer hInvariant.1 hStopped

/-- 例外辺不変条件と優先関係の性質から、任意回の `siftUp` 後に全順序を回復する。 -/
theorem siftUp_heapOrdered_of_initial_invariant
    (prefer : Nat → Nat → Bool) (heap : Array Nat) (start : Nat)
    (hStart : start < heap.size)
    (hInvariant : HeapOrderedExceptChildWithSubtreeBound prefer heap start)
    (hAsymm : ∀ child parent, prefer child parent = true → prefer parent child = false)
    (hPreferTrans : ∀ first second third,
      prefer first second = true → prefer second third = true → prefer first third = true)
    (hIrrefl : ∀ value, prefer value value = false)
    (hNotTrans : ∀ first second third,
      prefer first second = false → prefer second third = false → prefer first third = false) :
    HeapOrdered prefer (LeanExperiments.RunningMedian.siftUp prefer heap start) := by
  generalize hRun : LeanExperiments.RunningMedian.siftUp prefer heap start = result
  apply Id.of_run_eq_wp hRun
  vcgen [LeanExperiments.RunningMedian.siftUp] invariants
  case inv1 =>
    exact fun exit state =>
      state.1.size = heap.size ∧
      if exit then HeapOrdered prefer state.1 else
        HeapOrderedExceptChildWithSubtreeBound prefer state.1 state.2 ∧
        state.2 ≤ start ∧
        LeanExperiments.Verification.HeapSort.Spec.HeapDescendant state.2 start ∧
        (state.2 = 0 → HeapOrdered prefer state.1)
  case vc1 =>
    constructor
    · rfl
    · refine ⟨hInvariant, Nat.le_refl _,
        LeanExperiments.Verification.HeapSort.Spec.HeapDescendant.root start, ?_⟩
      intro hZero
      have hStartZero : start = 0 := by simpa using hZero
      rw [hStartZero] at hInvariant ⊢
      exact HeapOrdered.of_exceptChild_of_parent_stop prefer hInvariant.1 (Or.inl rfl)
  case vc2 => simp_all
  case vc3 =>
    simp_all [Variant.evalsBelow_ofMeasure_nat, Variant.evalsTo_ofMeasure,
      Assertion.NondetFun.evalsTo_pure]
    rename_i arr idx measure invariant hPositive hCompare
    rcases invariant with ⟨hMeasureEq, hSize, hExcept, hBound, hPath, hRootOrdered⟩
    have hIndexBound : idx < arr.size := by omega
    have hIndexPositive : 0 < idx := by omega
    have hCompareIdx : prefer arr[idx]! arr[(idx - 1) / 2]! = true := by
      simpa [hMeasureEq, parent] using hCompare
    have hParentBound : (idx - 1) / 2 < arr.size := by omega
    have hStep := HeapOrderedExceptChild.swap_up_preserves_invariant
      hExcept hIndexPositive hIndexBound hParentBound rfl hCompareIdx hAsymm hPreferTrans
      hIrrefl hNotTrans
    constructor
    · dsimp [parent]
      omega
    constructor
    · simpa [values, LeanExperiments.RunningMedian.swap] using hSize
    · refine ⟨hStep, ?_, ?_, ?_⟩
      · dsimp [parent]
        omega
      · have hParentCurrent :
            LeanExperiments.Verification.HeapSort.Spec.HeapDescendant ((idx - 1) / 2) idx := by
          let p := (idx - 1) / 2
          have hMod := Nat.mod_add_div (idx - 1) 2
          have hModBound := Nat.mod_lt (idx - 1) (by omega : 0 < 2)
          by_cases hEven : (idx - 1) % 2 = 0
          · have hIndex : idx = 2 * p + 1 := by dsimp [p]; omega
            change LeanExperiments.Verification.HeapSort.Spec.HeapDescendant p idx
            rw [hIndex]
            exact LeanExperiments.Verification.HeapSort.Spec.HeapDescendant.left
              (LeanExperiments.Verification.HeapSort.Spec.HeapDescendant.root p)
          · have hIndex : idx = 2 * p + 2 := by dsimp [p]; omega
            change LeanExperiments.Verification.HeapSort.Spec.HeapDescendant p idx
            rw [hIndex]
            exact LeanExperiments.Verification.HeapSort.Spec.HeapDescendant.right
              (LeanExperiments.Verification.HeapSort.Spec.HeapDescendant.root p)
        have hNewPath := hParentCurrent.trans hPath
        simpa [parent] using hNewPath
      · intro hParentZero
        exact HeapOrdered.of_exceptChild_of_parent_stop prefer hStep.1
          (Or.inl (by simpa [parent] using hParentZero))
  case vc4 =>
    simp_all [Variant.evalsTo_ofMeasure, Assertion.NondetFun.evalsTo_pure]
    rename_i arr idx measure invariant hPositive hNoCompare
    rcases invariant with ⟨hMeasureEq, hSize, hExcept, hBound, hPath, hRootOrdered⟩
    have hNoCompareIdx : prefer arr[idx]! arr[(idx - 1) / 2]! = false := by
      simpa [hMeasureEq, parent] using hNoCompare
    exact HeapOrdered.of_exceptChild_of_parent_stop prefer hExcept.1 (Or.inr hNoCompareIdx)
  case vc5 => simp_all

/-- 親との比較で停止する末尾追加は、例外辺仕様から全体の順序を保つ。 -/
theorem HeapOrdered.push_of_stops (prefer : Nat → Nat → Bool) (heap : Array Nat)
    (value : Nat) (hOrdered : HeapOrdered prefer heap)
    (hStops : heap.size = 0 ∨ prefer value heap[(heap.size - 1) / 2]! = false) :
    HeapOrdered prefer (heap.push value) := by
  apply HeapOrdered.of_exceptChild_of_stops prefer
    (HeapOrdered.push_except_last prefer heap value hOrdered)
  intro parent hParent
  constructor
  · intro hLeft
    have hChildBound : 2 * parent + 1 < (heap.push value).size := by
      rw [hLeft]
      simp
    have hParentOld : parent < heap.size := by omega
    have hParentEq : parent = (heap.size - 1) / 2 := by omega
    have hNoSwap : prefer value heap[parent]! = false := by
      rcases hStops with hEmpty | hNoSwap
      · omega
      · simpa [hParentEq] using hNoSwap
    have hValueAtEnd : (heap.push value)[heap.size]! = value := by simp
    have hParentValue : (heap.push value)[parent]! = heap[parent]! := by
      rw [getElem!_pos (heap.push value) parent hParent,
        getElem!_pos heap parent hParentOld]
      simp [Array.getElem_push, hParentOld]
    rw [hLeft, hValueAtEnd, hParentValue]
    exact hNoSwap
  · intro hRight
    have hChildBound : 2 * parent + 2 < (heap.push value).size := by
      rw [hRight]
      simp
    have hParentOld : parent < heap.size := by omega
    have hParentEq : parent = (heap.size - 1) / 2 := by omega
    have hNoSwap : prefer value heap[parent]! = false := by
      rcases hStops with hEmpty | hNoSwap
      · omega
      · simpa [hParentEq] using hNoSwap
    have hValueAtEnd : (heap.push value)[heap.size]! = value := by simp
    have hParentValue : (heap.push value)[parent]! = heap[parent]! := by
      rw [getElem!_pos (heap.push value) parent hParent,
        getElem!_pos heap parent hParentOld]
      simp [Array.getElem_push, hParentOld]
    rw [hRight, hValueAtEnd, hParentValue]
    exact hNoSwap

/-- 既存ヒープへの末尾追加が順序を保つための条件は、新しい親子辺の停止条件と同値である。 -/
theorem HeapOrdered.push_iff_stops (prefer : Nat → Nat → Bool) (heap : Array Nat)
    (value : Nat) (hOrdered : HeapOrdered prefer heap) :
    HeapOrdered prefer (heap.push value) ↔
      (heap.size = 0 ∨ prefer value heap[(heap.size - 1) / 2]! = false) := by
  constructor
  · intro hPushed
    by_cases hEmpty : heap.size = 0
    · exact Or.inl hEmpty
    · right
      let parent := (heap.size - 1) / 2
      have hParent : parent < heap.size := by dsimp [parent]; omega
      have hParentPush : parent < (heap.push value).size := by simp; omega
      have hChildIndex : heap.size = 2 * parent + 1 ∨ heap.size = 2 * parent + 2 := by
        have hDivMod := Nat.mod_add_div (heap.size - 1) 2
        have hMod := Nat.mod_lt (heap.size - 1) (by omega : 0 < 2)
        dsimp [parent]
        omega
      have hParentSame : (heap.push value)[parent]! = heap[parent]! := by
        rw [getElem!_pos (heap.push value) parent (by simp; omega),
          getElem!_pos heap parent hParent]
        simp [Array.getElem_push, hParent]
      have hValueAtEnd : (heap.push value)[heap.size]! = value := by simp
      rcases hChildIndex with hLeft | hRight
      · have hChildBound : 2 * parent + 1 < (heap.push value).size := by
          simp only [Array.size_push]
          omega
        have hNoSwap := (hPushed parent hParentPush).1 hChildBound
        rw [show 2 * parent + 1 = heap.size by omega, hValueAtEnd,
          hParentSame] at hNoSwap
        simpa [parent] using hNoSwap
      · have hChildBound : 2 * parent + 2 < (heap.push value).size := by
          simp only [Array.size_push]
          omega
        have hNoSwap := (hPushed parent hParentPush).2 hChildBound
        rw [show 2 * parent + 2 = heap.size by omega, hValueAtEnd,
          hParentSame] at hNoSwap
        simpa [parent] using hNoSwap
  · intro hStops
    exact HeapOrdered.push_of_stops prefer heap value hOrdered hStops

/-- 既存ヒープが順序済みなら、末尾追加後の Boolean 検査成功は親での停止条件と同値である。

一般的な `siftUp` の正当性とは区別し、交換を行わない単純な `push` の境界だけを
実行可能な検査器へ接続する。
-/
theorem heapCheck_push_iff_stops (prefer : Nat → Nat → Bool) (heap : Array Nat)
    (value : Nat) (hOrdered : HeapOrdered prefer heap) :
    heapCheck prefer (heap.push value) = true ↔
      (heap.size = 0 ∨ prefer value heap[(heap.size - 1) / 2]! = false) := by
  rw [heapCheck_correct]
  exact HeapOrdered.push_iff_stops prefer heap value hOrdered

/-- 停止条件を満たす挿入は、元のヒープ順序をそのまま保つ。 -/
theorem insertHeap_HeapOrdered_of_stops (prefer : Nat → Nat → Bool)
    (heap : Array Nat) (value : Nat) (hOrdered : HeapOrdered prefer heap)
    (hStops : heap.size = 0 ∨ prefer value heap[(heap.size - 1) / 2]! = false) :
    HeapOrdered prefer (LeanExperiments.RunningMedian.insertHeap prefer heap value) := by
  rw [insertHeap_eq_push_of_stops prefer heap value hStops]
  exact HeapOrdered.push_of_stops prefer heap value hOrdered hStops


end LeanExperiments.Verification.RunningMedian
