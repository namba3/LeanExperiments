import LeanExperiments.HeapSort
import LeanExperiments.Verification.MergeSort.Spec
import LeanExperiments.Verification.Sorting.Spec
import Std.WP
import Std.Tactic.Do

/-!
# ヒープ仕様と基本操作の契約

共通のソート仕様、配列ヒープの数学的モデル、sift-down と最大値取り出しの一般補題を置く。
ヒープ構築・抽出反復・ソート全体の正当性は `Core.lean` でこの契約を合成する。
-/

namespace LeanExperiments.Verification.HeapSort.Spec

open Std.WP Lean.Order
set_option experimental.vcgen true

/-- ヒープソートでも共通のリスト昇順仕様を使う。 -/
abbrev Ascending (values : List Nat) : Prop :=
  LeanExperiments.Verification.Sorting.Spec.Ascending values

/-- 有限検査でも共通ソート仕様の昇順 Boolean 判定器を再利用する。 -/
abbrev ascendingCheck (values : List Nat) : Bool :=
  LeanExperiments.Verification.Sorting.Spec.ascendingCheck values

/-- 共通昇順判定器の健全性・完全性をヒープソート仕様にも公開する。 -/
theorem ascendingCheck_correct (values : List Nat) :
    ascendingCheck values = true ↔ Ascending values := by
  exact LeanExperiments.Verification.Sorting.Spec.ascendingCheck_correct values

/-- 共通ソート仕様を配列の入出力へ適用する。

配列をリストへ変換し、共通の昇順性・順列保存仕様をそのまま再利用する。
-/
abbrev Correct (input output : Array Nat) : Prop :=
  LeanExperiments.Verification.Sorting.Spec.Correct input.toList output.toList

/-- `Correct` の判定可能な Boolean 版。

昇順性は上の再帰的な判定器で、要素保存は Lean 標準の `List.isPerm` で
確認し、後の補題でこの計算結果を論理的な `Correct` へ戻す。
-/
def correctCheck (input output : Array Nat) : Bool :=
  ascendingCheck output.toList && output.toList.isPerm input.toList

/-- Boolean 版の確認結果から `Correct` の証明を取り出す。 -/
theorem correctCheck_sound (input output : Array Nat)
    (h : correctCheck input output = true) : Correct input output := by
  unfold correctCheck at h
  rw [Bool.and_eq_true] at h
  constructor
  · exact ascendingCheck_correct output.toList |>.mp h.1
  · exact List.isPerm_iff.mp h.2

/-- 論理仕様を満たす出力は、Boolean 正当性検査にも必ず合格する。 -/
theorem correctCheck_complete (input output : Array Nat)
    (h : Correct input output) : correctCheck input output = true := by
  unfold correctCheck
  rw [Bool.and_eq_true]
  exact ⟨ascendingCheck_correct output.toList |>.mpr h.1,
    List.isPerm_iff.mpr h.2⟩

/-- ヒープソートの Boolean 検査器は、昇順性と要素保存の論理仕様と同値である。 -/
theorem correctCheck_iff (input output : Array Nat) :
    correctCheck input output = true ↔ Correct input output := by
  constructor
  · exact correctCheck_sound input output
  · exact correctCheck_complete input output

/-- 最大ヒープでは、配列に存在する各子の値が親を超えない。 -/
def MaxHeap (heap : Array Nat) : Prop :=
  ∀ index, index < heap.size →
    (2 * index + 1 < heap.size → heap[2 * index + 1]! ≤ heap[index]!) ∧
    (2 * index + 2 < heap.size → heap[2 * index + 2]! ≤ heap[index]!)

/-- 二分ヒープ配列上で、ある位置の部分木に属する添字を表す。 -/
inductive HeapDescendant : Nat → Nat → Prop where
  | root (root : Nat) : HeapDescendant root root
  | left {root parent : Nat} :
      HeapDescendant root parent → HeapDescendant root (2 * parent + 1)
  | right {root parent : Nat} :
      HeapDescendant root parent → HeapDescendant root (2 * parent + 2)

/-- 部分木に属する添字は、その根より後ろか根そのものである。 -/
theorem HeapDescendant.root_le {root index : Nat}
    (hDescendant : HeapDescendant root index) : root ≤ index := by
  induction hDescendant with
  | root => omega
  | left _ ih => omega
  | right _ ih => omega

/-- 子孫経路を連結すると、合成した根からの子孫経路になる。 -/
theorem HeapDescendant.trans {root middle index : Nat}
    (hRootMiddle : HeapDescendant root middle)
    (hMiddleIndex : HeapDescendant middle index) :
    HeapDescendant root index := by
  induction hMiddleIndex with
  | root => exact hRootMiddle
  | left _ ih => exact HeapDescendant.left ih
  | right _ ih => exact HeapDescendant.right ih

/-- 根より後ろの子孫の親添字も、同じ部分木に属する。 -/
theorem HeapDescendant.parent_of_lt {root index : Nat}
    (hDescendant : HeapDescendant root index) (hRootLt : root < index) :
    HeapDescendant root ((index - 1) / 2) := by
  induction hDescendant with
  | root => omega
  | left hParent ih =>
      rename_i parent
      have hParentIndex : ((2 * parent + 1 - 1) / 2) = parent := by omega
      change HeapDescendant root ((2 * parent + 1 - 1) / 2)
      rw [hParentIndex]
      exact hParent
  | right hParent ih =>
      rename_i parent
      have hParentIndex : ((2 * parent + 2 - 1) / 2) = parent := by omega
      change HeapDescendant root ((2 * parent + 2 - 1) / 2)
      rw [hParentIndex]
      exact hParent

/-- 選択した子の部分木外にある親から、その部分木へ子辺は入らない。 -/
theorem HeapDescendant.child_not_descendant_of_selected_child
    (root largest parent child : Nat)
    (hLargest : largest = 2 * root + 1 ∨ largest = 2 * root + 2)
    (hParentRoot : root < parent)
    (hParentOutside : ¬ HeapDescendant largest parent)
    (hChild : child = 2 * parent + 1 ∨ child = 2 * parent + 2) :
    ¬ HeapDescendant largest child := by
  intro hChildInside
  rcases hChild with hLeft | hRight
  · by_cases hChildEq : child = largest
    · rcases hLargest with hLargestLeft | hLargestRight <;> omega
    · have hLargestLtChild : largest < child := by
        have hLe := hChildInside.root_le
        omega
      have hParentInside := hChildInside.parent_of_lt hLargestLtChild
      have hParentEq : (child - 1) / 2 = parent := by omega
      rw [hParentEq] at hParentInside
      exact hParentOutside hParentInside
  · by_cases hChildEq : child = largest
    · rcases hLargest with hLargestLeft | hLargestRight <;> omega
    · have hLargestLtChild : largest < child := by
        have hLe := hChildInside.root_le
        omega
      have hParentInside := hChildInside.parent_of_lt hLargestLtChild
      have hParentEq : (child - 1) / 2 = parent := by omega
      rw [hParentEq] at hParentInside
      exact hParentOutside hParentInside

/-- 根より後ろの子孫は、根の左右どちらかの子を通る。 -/
theorem HeapDescendant.exists_first_child {root index : Nat}
    (hDescendant : HeapDescendant root index) (hRootLt : root < index) :
    ∃ child, (child = 2 * root + 1 ∨ child = 2 * root + 2) ∧
      HeapDescendant child index := by
  induction hDescendant with
  | root => omega
  | left hPath ih =>
      rename_i parent
      have hRootLeParent := hPath.root_le
      by_cases hSame : parent = root
      · subst parent
        exact ⟨2 * root + 1, Or.inl rfl, HeapDescendant.root _⟩
      · have hRootLtParent : root < parent := by omega
        obtain ⟨child, hChild, hPathFromChild⟩ := ih hRootLtParent
        exact ⟨child, hChild, HeapDescendant.left hPathFromChild⟩
  | right hPath ih =>
      rename_i parent
      have hRootLeParent := hPath.root_le
      by_cases hSame : parent = root
      · subst parent
        exact ⟨2 * root + 2, Or.inr rfl, HeapDescendant.root _⟩
      · have hRootLtParent : root < parent := by omega
        obtain ⟨child, hChild, hPathFromChild⟩ := ih hRootLtParent
        exact ⟨child, hChild, HeapDescendant.right hPathFromChild⟩

/-- 一方の子の部分木に属する添字は、もう一方の子の部分木には属さない。 -/
theorem HeapDescendant.not_descendant_of_sibling_child
    {root selected sibling index : Nat}
    (hSelected : selected = 2 * root + 1 ∨ selected = 2 * root + 2)
    (hSibling : sibling = 2 * root + 1 ∨ sibling = 2 * root + 2)
    (hDifferent : selected ≠ sibling)
    (hPath : HeapDescendant sibling index) :
    ¬ HeapDescendant selected index := by
  have hSelectedOutside : ¬ HeapDescendant selected sibling := by
    intro hInside
    have hSelectedLeSibling := hInside.root_le
    have hSelectedLtSibling : selected < sibling := by
      rcases hSelected with hLeft | hRight <;>
        rcases hSibling with hSiblingLeft | hSiblingRight <;> omega
    have hParentInside := hInside.parent_of_lt hSelectedLtSibling
    have hSiblingParent : (sibling - 1) / 2 = root := by
      rcases hSibling with hLeft | hRight <;> omega
    rw [hSiblingParent] at hParentInside
    have hSelectedLeRoot := hParentInside.root_le
    rcases hSelected with hLeft | hRight <;> omega
  induction hPath with
  | root => exact hSelectedOutside
  | left hPrevious ih =>
      rename_i parent
      have hRootLtSibling : root < sibling := by
        rcases hSibling with hLeft | hRight <;> omega
      have hParentRoot : root < parent := by
        have hSiblingLeParent := hPrevious.root_le
        omega
      exact child_not_descendant_of_selected_child root selected parent
        (2 * parent + 1) hSelected hParentRoot ih (Or.inl rfl)
  | right hPrevious ih =>
      rename_i parent
      have hRootLtSibling : root < sibling := by
        rcases hSibling with hLeft | hRight <;> omega
      have hParentRoot : root < parent := by
        have hSiblingLeParent := hPrevious.root_le
        omega
      exact child_not_descendant_of_selected_child root selected parent
        (2 * parent + 2) hSelected hParentRoot ih (Or.inr rfl)

/-- 配列木の根 `0` からは、全ての自然数添字へ子孫経路が存在する。 -/
theorem HeapDescendant.zero_ancestor (index : Nat) : HeapDescendant 0 index := by
  induction index using Nat.strongRecOn with
  | ind index ih =>
      by_cases hZero : index = 0
      · subst index
        exact HeapDescendant.root 0
      · let parent := (index - 1) / 2
        have hParentLt : parent < index := by
          dsimp [parent]
          omega
        have hParentPath := ih parent hParentLt
        have hChild : index = 2 * parent + 1 ∨ index = 2 * parent + 2 := by
          dsimp [parent]
          omega
        rcases hChild with hLeft | hRight
        · rw [hLeft]
          exact HeapDescendant.left hParentPath
        · rw [hRight]
          exact HeapDescendant.right hParentPath

/-- 最大ヒープでは、根が配列中の全ての要素以上になる。 -/
theorem MaxHeap.le_root {heap : Array Nat} (hHeap : MaxHeap heap) :
    ∀ index, index < heap.size → heap[index]! ≤ heap[0]! := by
  intro index
  induction index using Nat.strongRecOn with
  | ind index ih =>
      intro hIndex
      by_cases hRoot : index = 0
      · simp [hRoot]
      · let parent := (index - 1) / 2
        have hParentLt : parent < index := by
          dsimp [parent]
          omega
        have hParentSize : parent < heap.size := Nat.lt_trans hParentLt hIndex
        have hParentBound := hHeap parent hParentSize
        have hChildIndex :
            index = 2 * parent + 1 ∨ index = 2 * parent + 2 := by
          dsimp [parent]
          omega
        have hChildLeParent : heap[index]! ≤ heap[parent]! := by
          rcases hChildIndex with hLeft | hRight
          · rw [hLeft]
            exact hParentBound.1 (by omega)
          · rw [hRight]
            exact hParentBound.2 (by omega)
        exact Nat.le_trans hChildLeParent (ih parent hParentLt hParentSize)

/-- 最大ヒープが空でなければ、根はリストに含まれる最大要素である。 -/
theorem MaxHeap.root_is_greatest {heap : Array Nat} (hHeap : MaxHeap heap)
    (hNonempty : 0 < heap.size) :
    heap[0]! ∈ heap.toList ∧
      ∀ value, value ∈ heap.toList → value ≤ heap[0]! := by
  have hRootMem : heap[0]! ∈ heap.toList := by simp [hNonempty]
  refine ⟨hRootMem, ?_⟩
  intro value hValue
  have hArrayMem := Array.mem_toList_iff.mp hValue
  obtain ⟨index, hIndex, hIndexValue⟩ := Array.mem_iff_getElem.mp hArrayMem
  have hBound := hHeap.le_root index hIndex
  have hValueAtIndex : heap[index]! = value := by
    rw [getElem!_pos heap index hIndex, hIndexValue]
  rw [hValueAtIndex] at hBound
  exact hBound

/-- 最大ヒープでは、各根が自身の部分木の全要素以上である。 -/
theorem MaxHeap.ancestor_dominates_descendants {heap : Array Nat}
    (hHeap : MaxHeap heap) {root index : Nat}
    (hDescendant : HeapDescendant root index) (hIndex : index < heap.size) :
    heap[index]! ≤ heap[root]! := by
  induction hDescendant with
  | root => simp
  | left hParent ih =>
      rename_i parent
      have hParentIndex : parent < heap.size := by omega
      have hEdge := hHeap parent hParentIndex
      have hChildLeParent : heap[2 * parent + 1]! ≤ heap[parent]! :=
        hEdge.1 (by omega)
      exact Nat.le_trans hChildLeParent (ih hParentIndex)
  | right hParent ih =>
      rename_i parent
      have hParentIndex : parent < heap.size := by omega
      have hEdge := hHeap parent hParentIndex
      have hChildLeParent : heap[2 * parent + 2]! ≤ heap[parent]! :=
        hEdge.2 (by omega)
      exact Nat.le_trans hChildLeParent (ih hParentIndex)

/-- 局所的な親子条件は、全ての根と子孫の値の大小関係と同値である。

前向きは親子条件を部分木の経路に沿って合成し、逆向きは左右の子を直接選ぶ。
checker の局所仕様を、木全体に対する意味で読み替えるために使える。
-/
theorem maxHeap_iff_ancestor_dominates_descendants (heap : Array Nat) :
    MaxHeap heap ↔
      ∀ root index, HeapDescendant root index → index < heap.size →
        heap[index]! ≤ heap[root]! := by
  constructor
  · intro hHeap root index hDescendant hIndex
    exact hHeap.ancestor_dominates_descendants hDescendant hIndex
  · intro hDescendant root hRoot
    constructor
    · intro hLeft
      exact hDescendant root (2 * root + 1)
        (HeapDescendant.left (HeapDescendant.root root)) hLeft
    · intro hRight
      exact hDescendant root (2 * root + 2)
        (HeapDescendant.right (HeapDescendant.root root)) hRight

/-- 最大ヒープの末尾要素を削除しても、残った親子条件は保たれる。 -/
theorem MaxHeap.pop {heap : Array Nat} (hHeap : MaxHeap heap) :
    MaxHeap heap.pop := by
  intro parent hParent
  have hPopSize : heap.pop.size = heap.size - 1 := by simp
  have hParentInput : parent < heap.size := by omega
  have hEdges := hHeap parent hParentInput
  constructor
  · intro hLeft
    have hLeftInput : 2 * parent + 1 < heap.size := by omega
    have hChildLeParent := hEdges.1 hLeftInput
    have hParentPop : heap.pop[parent]! = heap[parent]! := by
      rw [getElem!_pos heap.pop parent hParent,
        getElem!_pos heap parent hParentInput, Array.getElem_pop hParent]
    have hLeftPop : heap.pop[2 * parent + 1]! = heap[2 * parent + 1]! := by
      rw [getElem!_pos heap.pop (2 * parent + 1) hLeft,
        getElem!_pos heap (2 * parent + 1) hLeftInput,
        Array.getElem_pop hLeft]
    rw [hParentPop, hLeftPop]
    exact hChildLeParent
  · intro hRight
    have hRightInput : 2 * parent + 2 < heap.size := by omega
    have hChildLeParent := hEdges.2 hRightInput
    have hParentPop : heap.pop[parent]! = heap[parent]! := by
      rw [getElem!_pos heap.pop parent hParent,
        getElem!_pos heap parent hParentInput, Array.getElem_pop hParent]
    have hRightPop : heap.pop[2 * parent + 2]! = heap[2 * parent + 2]! := by
      rw [getElem!_pos heap.pop (2 * parent + 2) hRight,
        getElem!_pos heap (2 * parent + 2) hRightInput,
        Array.getElem_pop hRight]
    rw [hParentPop, hRightPop]
    exact hChildLeParent

/-- 最大ヒープの末尾を根へ移しても、根より下の親子条件は保たれる。

`popMax` が根を取り除いた直後の配列に対する性質であり、残る修復義務が根の部分木だけで
あることを明示する。
-/
theorem MaxHeap.pop_set_root_preserves_below_root {heap : Array Nat}
    (hHeap : MaxHeap heap) (last : Nat) :
    ∀ parent, 0 < parent → parent < (heap.pop.set! 0 last).size →
      (2 * parent + 1 < (heap.pop.set! 0 last).size →
        (heap.pop.set! 0 last)[2 * parent + 1]! ≤ (heap.pop.set! 0 last)[parent]!) ∧
      (2 * parent + 2 < (heap.pop.set! 0 last).size →
        (heap.pop.set! 0 last)[2 * parent + 2]! ≤ (heap.pop.set! 0 last)[parent]!) := by
  intro parent hParentPositive hParent
  have hPopHeap := hHeap.pop
  have hPopSize : heap.pop.size = heap.size - 1 := by simp
  have hParentPop : parent < heap.pop.size := by
    simp only [Array.size_pop, Array.size_set!] at hParent
    omega
  have hPopEdges := hPopHeap parent hParentPop
  constructor
  · intro hLeft
    have hLeftPop : 2 * parent + 1 < heap.pop.size := by
      simpa only [Array.size_set!] using hLeft
    have hLeftEdge := hPopEdges.1 hLeftPop
    rw [Array.getElem!_set!_ne _ 0 (2 * parent + 1) last (by omega),
      Array.getElem!_set!_ne _ 0 parent last (by omega)]
    exact hLeftEdge
  · intro hRight
    have hRightPop : 2 * parent + 2 < heap.pop.size := by
      simpa only [Array.size_set!] using hRight
    have hRightEdge := hPopEdges.2 hRightPop
    rw [Array.getElem!_set!_ne _ 0 (2 * parent + 2) last (by omega),
      Array.getElem!_set!_ne _ 0 parent last (by omega)]
    exact hRightEdge

/-- 下降処理が選ぶ候補位置は、現在の位置より前へ戻らない。 -/
theorem siftDownLargest_ge (values : Array Nat) (index : Nat) :
    index ≤ LeanExperiments.HeapSort.siftDownLargest values index :=
  LeanExperiments.HeapSort.siftDownLargest_ge values index

/-- 下降候補は、現在位置か二つの子添字のいずれかである。 -/
theorem siftDownLargest_eq_root_or_child (values : Array Nat) (index : Nat) :
    LeanExperiments.HeapSort.siftDownLargest values index = index ∨
      LeanExperiments.HeapSort.siftDownLargest values index = 2 * index + 1 ∨
      LeanExperiments.HeapSort.siftDownLargest values index = 2 * index + 2 :=
  LeanExperiments.HeapSort.siftDownLargest_eq_root_or_child values index

/-- 候補が現在位置と異なるとき、下降先は左右いずれかの子である。 -/
theorem siftDownLargest_moves_to_child (values : Array Nat) (index : Nat)
    (hMoves : LeanExperiments.HeapSort.siftDownLargest values index ≠ index) :
    LeanExperiments.HeapSort.siftDownLargest values index = 2 * index + 1 ∨
      LeanExperiments.HeapSort.siftDownLargest values index = 2 * index + 2 := by
  rcases siftDownLargest_eq_root_or_child values index with hRoot | hLeft | hRight
  · exact False.elim (hMoves hRoot)
  · exact Or.inl hLeft
  · exact Or.inr hRight

/-- 実際に下降するとき、移動先は現在位置より深く、右子の添字を越えない。 -/
theorem siftDownLargest_moves_strictly_down (values : Array Nat) (index : Nat)
    (hMoves : LeanExperiments.HeapSort.siftDownLargest values index ≠ index) :
    index < LeanExperiments.HeapSort.siftDownLargest values index ∧
      LeanExperiments.HeapSort.siftDownLargest values index ≤ 2 * index + 2 := by
  rcases siftDownLargest_moves_to_child values index hMoves with hLeft | hRight
  · constructor <;> omega
  · constructor <;> omega

/-- 選択された位置の値は、配列内にある根と左右の子の値以上である。 -/
theorem siftDownLargest_value_ge_valid_candidates (values : Array Nat) (index : Nat) :
    values[index]! ≤ values[LeanExperiments.HeapSort.siftDownLargest values index]! ∧
      (2 * index + 1 < values.size →
        values[2 * index + 1]! ≤
          values[LeanExperiments.HeapSort.siftDownLargest values index]!) ∧
      (2 * index + 2 < values.size →
        values[2 * index + 2]! ≤
          values[LeanExperiments.HeapSort.siftDownLargest values index]!) := by
  have hRightIndex : 2 * index + 1 + 1 = 2 * index + 2 := by omega
  simp only [LeanExperiments.HeapSort.siftDownLargest,
    Bool.and_eq_true, decide_eq_true_eq, hRightIndex]
  split <;> split <;> omega

/-- 左の子が根より大きく、右の子が左の子を越えなければ左の子を選ぶ。 -/
theorem siftDownLargest_eq_left_of_left_dominates
    (values : Array Nat) (index : Nat)
    (hLeft : 2 * index + 1 < values.size ∧
      values[index]! < values[2 * index + 1]!)
    (hRight : 2 * index + 2 < values.size →
      values[2 * index + 2]! ≤ values[2 * index + 1]!) :
    LeanExperiments.HeapSort.siftDownLargest values index = 2 * index + 1 := by
  have hLeftRaw : values[index]! < values[2 * index + 1] := by
    simpa only [getElem!_pos values (2 * index + 1) hLeft.1] using hLeft.2
  have hLeftCondition :
      (decide (2 * index + 1 < values.size) &&
        decide (values[index]! < values[2 * index + 1]!)) = true := by
    simp [hLeft.1, hLeftRaw]
  have hRightCondition :
      (decide (2 * index + 2 < values.size) &&
        decide (values[2 * index + 1]! < values[2 * index + 2]!)) = false := by
    by_cases hRightIndex : 2 * index + 2 < values.size
    · have hRightBound := hRight hRightIndex
      have hNoCompare : ¬ values[2 * index + 1]! < values[2 * index + 2]! := by
        omega
      have hCompare :
          decide (values[2 * index + 1]! < values[2 * index + 2]!) = false :=
        decide_eq_false hNoCompare
      simp only [hRightIndex, decide_true, Bool.true_and]
      exact hCompare
    · simp [hRightIndex]
  unfold LeanExperiments.HeapSort.siftDownLargest
  simp [hLeftCondition, hRightCondition, Nat.add_assoc]

/-- 左の子が根を越えず、右の子が根より大きければ右の子を選ぶ。 -/
theorem siftDownLargest_eq_right_of_right_dominates
    (values : Array Nat) (index : Nat)
    (hLeft : 2 * index + 1 < values.size →
      values[2 * index + 1]! ≤ values[index]!)
    (hRight : 2 * index + 2 < values.size ∧
      values[index]! < values[2 * index + 2]!) :
    LeanExperiments.HeapSort.siftDownLargest values index = 2 * index + 2 := by
  have hLeftCondition :
      (decide (2 * index + 1 < values.size) &&
        decide (values[index]! < values[2 * index + 1]!)) = false := by
    by_cases hLeftIndex : 2 * index + 1 < values.size
    · have hLeftBound := hLeft hLeftIndex
      have hNoCompare : ¬ values[index]! < values[2 * index + 1]! := by
        omega
      have hCompare :
          decide (values[index]! < values[2 * index + 1]!) = false :=
        decide_eq_false hNoCompare
      simp only [hLeftIndex, decide_true, Bool.true_and]
      exact hCompare
    · simp [hLeftIndex]
  have hRightRaw : values[index]! < values[2 * index + 2] := by
    simpa only [getElem!_pos values (2 * index + 2) hRight.1] using hRight.2
  have hRightCondition :
      (decide (2 * index + 2 < values.size) &&
        decide (values[index]! < values[2 * index + 2]!)) = true := by
    simp [hRight.1, hRightRaw]
  unfold LeanExperiments.HeapSort.siftDownLargest
  simp [hLeftCondition, hRightCondition, Nat.add_assoc]

/-- 左が根より大きく、右が左をさらに越えるときは右の子を選ぶ。 -/
theorem siftDownLargest_eq_right_of_right_greater_than_left
    (values : Array Nat) (index : Nat)
    (hLeft : 2 * index + 1 < values.size ∧
      values[index]! < values[2 * index + 1]!)
    (hRight : 2 * index + 2 < values.size ∧
      values[2 * index + 1]! < values[2 * index + 2]!) :
    LeanExperiments.HeapSort.siftDownLargest values index = 2 * index + 2 := by
  have hLeftRaw : values[index]! < values[2 * index + 1] := by
    simpa only [getElem!_pos values (2 * index + 1) hLeft.1] using hLeft.2
  have hLeftCondition :
      (decide (2 * index + 1 < values.size) &&
        decide (values[index]! < values[2 * index + 1]!)) = true := by
    simp [hLeft.1, hLeftRaw]
  have hRightRaw : values[2 * index + 1]! < values[2 * index + 2] := by
    simpa only [getElem!_pos values (2 * index + 2) hRight.1] using hRight.2
  have hRightCondition :
      (decide (2 * index + 2 < values.size) &&
        decide (values[2 * index + 1]! < values[2 * index + 2]!)) = true := by
    simp [hRight.1, hRightRaw]
  unfold LeanExperiments.HeapSort.siftDownLargest
  simp [hLeftCondition, hRightCondition, Nat.add_assoc]

/-- 根が配列内にあれば、選ばれた下降候補も配列内にある。 -/
theorem siftDownLargest_lt_size (values : Array Nat) (index : Nat)
    (hIndex : index < values.size) :
    LeanExperiments.HeapSort.siftDownLargest values index < values.size := by
  have hRightIndex : 2 * index + 1 + 1 = 2 * index + 2 := by omega
  simp only [LeanExperiments.HeapSort.siftDownLargest,
    Bool.and_eq_true, decide_eq_true_eq, hRightIndex]
  split <;> split <;> omega

/-- 配列内の根から選ばれる候補は、根か、配列内にある左右の子である。 -/
theorem siftDownLargest_eq_root_or_valid_child (values : Array Nat) (index : Nat)
    (hIndex : index < values.size) :
    LeanExperiments.HeapSort.siftDownLargest values index = index ∨
      (LeanExperiments.HeapSort.siftDownLargest values index = 2 * index + 1 ∧
        2 * index + 1 < values.size) ∨
      (LeanExperiments.HeapSort.siftDownLargest values index = 2 * index + 2 ∧
        2 * index + 2 < values.size) := by
  have hCandidate := siftDownLargest_lt_size values index hIndex
  rcases siftDownLargest_eq_root_or_child values index with hRoot | hLeft | hRight
  · exact Or.inl hRoot
  · exact Or.inr (Or.inl ⟨hLeft, by omega⟩)
  · exact Or.inr (Or.inr ⟨hRight, by omega⟩)

/-- 根が左右の存在する子以上であることと、下降候補が根に留まることは同値である。 -/
theorem siftDownLargest_eq_index_iff_dominatesChildren
    (values : Array Nat) (index : Nat) :
    LeanExperiments.HeapSort.siftDownLargest values index = index ↔
      (2 * index + 1 < values.size →
        values[2 * index + 1]! ≤ values[index]!) ∧
      (2 * index + 2 < values.size →
        values[2 * index + 2]! ≤ values[index]!) := by
  constructor
  · intro hCandidate
    have hSelected := siftDownLargest_value_ge_valid_candidates values index
    constructor
    · intro hLeft
      simpa [hCandidate] using hSelected.2.1 hLeft
    · intro hRight
      simpa [hCandidate] using hSelected.2.2 hRight
  · intro hDominates
    have hLeftCondition :
        (decide (2 * index + 1 < values.size) &&
          decide (values[index]! < values[2 * index + 1]!)) = false := by
      by_cases hLeft : 2 * index + 1 < values.size
      · have hBound := hDominates.1 hLeft
        have hBound' : values[2 * index + 1] ≤ values[index]! := by
          simpa only [getElem!_pos values (2 * index + 1) hLeft] using hBound
        simp [hLeft, hBound']
      · simp [hLeft]
    have hRightCondition :
        (decide (2 * index + 2 < values.size) &&
          decide (values[index]! < values[2 * index + 2]!)) = false := by
      by_cases hRight : 2 * index + 2 < values.size
      · have hBound := hDominates.2 hRight
        have hBound' : values[2 * index + 2] ≤ values[index]! := by
          simpa only [getElem!_pos values (2 * index + 2) hRight] using hBound
        simp [hRight, hBound']
      · simp [hRight]
    unfold LeanExperiments.HeapSort.siftDownLargest
    simp [hLeftCondition, hRightCondition]

/-- 根から別の候補へ下降するとき、その候補の値は根より厳密に大きい。 -/
theorem siftDownLargest_value_gt_of_moves (values : Array Nat) (index : Nat)
    (hMoves : LeanExperiments.HeapSort.siftDownLargest values index ≠ index) :
    values[index]! < values[LeanExperiments.HeapSort.siftDownLargest values index]! := by
  have hNotDominates :
      ¬ ((2 * index + 1 < values.size →
          values[2 * index + 1]! ≤ values[index]!) ∧
        (2 * index + 2 < values.size →
          values[2 * index + 2]! ≤ values[index]!)) := by
    intro hDominates
    exact hMoves ((siftDownLargest_eq_index_iff_dominatesChildren values index).2
      hDominates)
  by_cases hLeftDominates :
      (2 * index + 1 < values.size → values[2 * index + 1]! ≤ values[index]!)
  · have hRightFail :
        ¬ (2 * index + 2 < values.size → values[2 * index + 2]! ≤ values[index]!) := by
      intro hRightDominates
      exact hNotDominates ⟨hLeftDominates, hRightDominates⟩
    rcases not_imp.mp hRightFail with ⟨hRight, hNotLe⟩
    have hRightLeCandidate :=
      (siftDownLargest_value_ge_valid_candidates values index).2.2 hRight
    omega
  · rcases not_imp.mp hLeftDominates with ⟨hLeft, hNotLe⟩
    have hLeftLeCandidate :=
      (siftDownLargest_value_ge_valid_candidates values index).2.1 hLeft
    omega

/-- 再帰版の下降処理は、どの入力・根位置でも配列長を保つ。 -/
theorem siftDownRecursive_size (values : Array Nat) (root : Nat) :
    (LeanExperiments.HeapSort.siftDownRecursive values root).size = values.size :=
  LeanExperiments.HeapSort.siftDownRecursive_size values root

/-- 再帰版下降の一段目は、停止するか、fuelを一つ減らして選択位置から続ける。

有限fuelの実装を展開した一般式で、子の選択と再帰後の不変条件を別々に証明するときに使う。
-/
theorem siftDownRecursive_unfold (values : Array Nat) (root : Nat) :
    LeanExperiments.HeapSort.siftDownRecursive values root =
      let largest := LeanExperiments.HeapSort.siftDownLargest values root
      if largest == root then values
      else LeanExperiments.HeapSort.siftDownFuel (values.size - 1)
        (LeanExperiments.HeapSort.swap values root largest) largest := by
  cases hSize : values.size <;>
    simp [LeanExperiments.HeapSort.siftDownRecursive,
      LeanExperiments.HeapSort.siftDownFuel, LeanExperiments.HeapSort.siftDownLargest,
      hSize]

/-- 最大候補へ交換して下降を続けても、再帰下降全体の結果は変わらない。

一段展開の停止しない場合を、残りの計算に関する等式として切り出す。下降経路に沿った
不変条件を帰納的に合成するときに使える。
-/
theorem siftDownRecursive_eq_after_selected_swap
    (values : Array Nat) (root largest : Nat)
    (hLargest : LeanExperiments.HeapSort.siftDownLargest values root = largest)
    (hMovesDown : largest ≠ root) :
    LeanExperiments.HeapSort.siftDownRecursive values root =
      LeanExperiments.HeapSort.siftDownRecursive
        (LeanExperiments.HeapSort.swap values root largest) largest :=
  LeanExperiments.HeapSort.siftDownRecursive_eq_siftDownRecursive_after_swap
    values root largest hLargest hMovesDown

/-- 命令的な下降ループの状態が表す、初期の再帰結果との一致条件。

`current` と `index` をループ状態とし、そこから再帰的に下降した結果が初期状態の
下降結果に等しいことを表す。交換ごとの保存と停止時の帰結を以下で一般に証明する。
-/
def siftDownLoopInvariant (initial : Array Nat) (root : Nat)
    (current : Array Nat) (index : Nat) : Prop :=
  LeanExperiments.HeapSort.siftDownRecursive current index =
    LeanExperiments.HeapSort.siftDownRecursive initial root

/-- 下降ループ不変条件は、初期状態で成立する。 -/
theorem siftDownLoopInvariant_initial (initial : Array Nat) (root : Nat) :
    siftDownLoopInvariant initial root initial root := rfl

/-- 子へ下降すると、配列長から現在位置を引いたループ変種が厳密に減る。

候補位置が根以上で、根とは異なることから添字が厳密に増える。配列長は交換で保たれるため、
`size - index` は交換後に小さくなり、ループの停止性を支える。
-/
theorem siftDownLoopVariant_decreases (values : Array Nat) (index largest : Nat)
    (hLargest : LeanExperiments.HeapSort.siftDownLargest values index = largest)
    (hMovesDown : largest ≠ index) :
    values.size - largest < values.size - index := by
  by_cases hRoot : index < values.size
  · have hLargestBound := siftDownLargest_lt_size values index hRoot
    have hIndexLeLargest : index ≤ largest := by
      rw [← hLargest]
      exact LeanExperiments.HeapSort.siftDownLargest_ge values index
    omega
  · have hNotRoot : ¬ index < values.size := hRoot
    have hNoLeft : ¬ 2 * index + 1 < values.size := by omega
    have hNoRight : ¬ 2 * index + 2 < values.size := by omega
    have hDominates :
        (2 * index + 1 < values.size → values[2 * index + 1]! ≤ values[index]!) ∧
        (2 * index + 2 < values.size → values[2 * index + 2]! ≤ values[index]!) := by
      constructor <;> intro hChild <;> omega
    have hLargestEq := (siftDownLargest_eq_index_iff_dominatesChildren values index).2
      hDominates
    exact (hMovesDown (hLargest.symm.trans hLargestEq)).elim

/-- 最大候補との交換で、下降ループ不変条件は保存される。 -/
theorem siftDownLoopInvariant_swap (initial : Array Nat) (root : Nat)
    (current : Array Nat) (index largest : Nat)
    (hInvariant : siftDownLoopInvariant initial root current index)
    (hLargest : LeanExperiments.HeapSort.siftDownLargest current index = largest)
    (hMovesDown : largest ≠ index) :
    siftDownLoopInvariant initial root
      (LeanExperiments.HeapSort.swap current index largest) largest := by
  change LeanExperiments.HeapSort.siftDownRecursive
      (LeanExperiments.HeapSort.swap current index largest) largest = _
  calc
    _ = LeanExperiments.HeapSort.siftDownRecursive current index :=
      (siftDownRecursive_eq_after_selected_swap current index largest
        hLargest hMovesDown).symm
    _ = LeanExperiments.HeapSort.siftDownRecursive initial root := hInvariant

/-- 根が子以上になって停止した状態では、現在配列が初期下降結果そのものである。

ループ不変条件と停止時の固定点性を合成し、命令的ループの返却値を特定する際に使う。
-/
theorem siftDownLoopInvariant_exit (initial : Array Nat) (root : Nat)
    (current : Array Nat) (index : Nat)
    (hInvariant : siftDownLoopInvariant initial root current index)
    (hLeft : 2 * index + 1 < current.size →
      current[2 * index + 1]! ≤ current[index]!)
    (hRight : 2 * index + 2 < current.size →
      current[2 * index + 2]! ≤ current[index]!) :
    current = LeanExperiments.HeapSort.siftDownRecursive initial root := by
  have hFixed := LeanExperiments.HeapSort.siftDownRecursive_eq_self_of_dominatesChildren
    current index hLeft hRight
  exact hFixed.symm.trans hInvariant

set_option maxHeartbeats 1000000

/-- 命令的な下降ループは、任意の入力と根で再帰版 `siftDown` と一致する。

1反復の配列・添字更新は `siftDownStep` にまとめ、不変条件の保存と停止測度を
個別に確認してループ全体の結果へ結びつける。
-/
theorem siftDown_eq_siftDownRecursive (values : Array Nat) (root : Nat) :
    LeanExperiments.HeapSort.siftDown values root =
      LeanExperiments.HeapSort.siftDownRecursive values root := by
  generalize hRun : LeanExperiments.HeapSort.siftDown values root = result
  apply Id.of_run_eq_wp hRun
  vcgen [LeanExperiments.HeapSort.siftDown] invariants
  · fun finished state =>
      if finished then
        state.1 = LeanExperiments.HeapSort.siftDownRecursive values root
      else if state.2.2 then
        siftDownLoopInvariant values root state.1 state.2.1
      else state.1 = LeanExperiments.HeapSort.siftDownRecursive values root
  case vc1 => simp [siftDownLoopInvariant]
  case vc2 => simp_all
  case vc3 =>
    simp_all [LeanExperiments.HeapSort.siftDownStep,
      Variant.evalsBelow_ofMeasure_nat, Variant.evalsTo_ofMeasure,
      Assertion.NondetFun.evalsTo_pure]
    constructor
    · omega
    · have hDominates :=
        (siftDownLargest_eq_index_iff_dominatesChildren _ _).mp (by assumption)
      rcases ‹_ ∧ siftDownLoopInvariant values root _ _› with ⟨_, hInvariant⟩
      exact siftDownLoopInvariant_exit values root _ _ hInvariant hDominates.1 hDominates.2
  case vc4 =>
    simp_all [LeanExperiments.HeapSort.siftDownStep,
      Variant.evalsBelow_ofMeasure_nat, Variant.evalsTo_ofMeasure,
      Assertion.NondetFun.evalsTo_pure]
    constructor
    · have hDecrease := siftDownLoopVariant_decreases _ _ _ (by rfl) (by assumption)
      simp [current, index, LeanExperiments.HeapSort.siftDownStep,
        LeanExperiments.HeapSort.swap_size]
      omega
    · apply siftDownLoopInvariant_swap values root
      · exact (‹_ ∧ siftDownLoopInvariant values root _ _›).2
      · rfl
      · assumption
  case vc5 => simp_all

set_option maxHeartbeats 200000

set_option maxHeartbeats 1000000

/-- ループ版ヒープ構築は、任意入力で再帰版ヒープ構築と一致する。

未処理の親添字 `next` まで再帰版の構築を残すことをループ不変条件にする。
各反復で `siftDown` と `siftDownRecursive` の一般一致定理を使い、
処理済み範囲を1つ根側へ広げる。
-/
theorem buildMaxHeap_eq_buildMaxHeapRecursive (input : Array Nat) :
    LeanExperiments.HeapSort.buildMaxHeap input =
      LeanExperiments.HeapSort.buildMaxHeapRecursive input := by
  generalize hRun : LeanExperiments.HeapSort.buildMaxHeap input = result
  apply Id.of_run_eq_wp hRun
  vcgen [LeanExperiments.HeapSort.buildMaxHeap] invariants
  · fun finished state =>
      if finished then
        state.1 = LeanExperiments.HeapSort.buildMaxHeapRecursive input
      else
        LeanExperiments.HeapSort.buildMaxHeapRecursive.go state.2 state.1 =
          LeanExperiments.HeapSort.buildMaxHeapRecursive input
  case vc1 =>
    change LeanExperiments.HeapSort.buildMaxHeapRecursive.go
      (input.size / 2) input = _
    rfl
  case vc2 => simp_all
  case vc3 =>
    rename_i values current measure invariant hPositive
    simp_all [Variant.evalsTo_ofMeasure,
      Assertion.NondetFun.evalsTo_pure]
    rcases invariant with ⟨hMeasure, hInvariant⟩
    constructor
    · omega
    · have hSucc : current = next + 1 := by omega
      rw [hSucc, LeanExperiments.HeapSort.buildMaxHeapRecursive.go] at hInvariant
      change LeanExperiments.HeapSort.buildMaxHeapRecursive.go next
        (LeanExperiments.HeapSort.siftDown values next) = _
      rw [siftDown_eq_siftDownRecursive]
      exact hInvariant
  case vc4 =>
    rename_i values current measure invariant hNotPositive
    simp at invariant
    rcases invariant with ⟨_, hInvariant⟩
    have hZero : current = 0 := by omega
    rw [hZero, LeanExperiments.HeapSort.buildMaxHeapRecursive.go] at hInvariant
    exact hInvariant

set_option maxHeartbeats 200000

/-- 再帰版の下降処理は、どの入力・根位置でも要素を順列として保つ。 -/
theorem siftDownRecursive_perm (values : Array Nat) (root : Nat) :
    (LeanExperiments.HeapSort.siftDownRecursive values root).toList.Perm values.toList :=
  LeanExperiments.HeapSort.siftDownRecursive_perm values root

/-- 再帰版下降処理は、任意の配列と根位置で要素の総和を保つ。 -/
theorem siftDownRecursive_sum (values : Array Nat) (root : Nat) :
    (LeanExperiments.HeapSort.siftDownRecursive values root).toList.sum =
      values.toList.sum :=
  (siftDownRecursive_perm values root).sum_nat

/-- 任意 fuel の下降でも配列長が保存されることを、仕様モジュールから参照できる。 -/
theorem siftDownFuel_size (fuel : Nat) (values : Array Nat) (root : Nat) :
    (LeanExperiments.HeapSort.siftDownFuel fuel values root).size = values.size :=
  LeanExperiments.HeapSort.siftDownFuel_size fuel values root

/-- 任意 fuel の下降でも要素の重複を含む順列関係が保存される。 -/
theorem siftDownFuel_perm (fuel : Nat) (values : Array Nat) (root : Nat) :
    (LeanExperiments.HeapSort.siftDownFuel fuel values root).toList.Perm values.toList :=
  LeanExperiments.HeapSort.siftDownFuel_perm fuel values root

/-- 根から配列末尾までの距離が fuel 以上なら、一段短い fuel でも結果は変わらない。 -/
theorem siftDownFuel_succ_eq_of_size_le_fuel_add_root
    (fuel : Nat) (values : Array Nat) (root : Nat)
    (hSize : values.size ≤ fuel + root) :
    LeanExperiments.HeapSort.siftDownFuel (fuel + 1) values root =
      LeanExperiments.HeapSort.siftDownFuel fuel values root :=
  LeanExperiments.HeapSort.siftDownFuel_succ_eq_of_size_le_fuel_add_root
    fuel values root hSize

/-- 十分な fuel は、根から葉までの必要段数まで短縮できる。 -/
theorem siftDownFuel_eq_of_size_le_fuel_add_root (fuel : Nat) (values : Array Nat)
    (root : Nat) (hSize : values.size ≤ fuel + root) :
    LeanExperiments.HeapSort.siftDownFuel fuel values root =
      LeanExperiments.HeapSort.siftDownFuel (values.size - root) values root :=
  LeanExperiments.HeapSort.siftDownFuel_eq_of_size_le_fuel_add_root
    fuel values root hSize

/-- 再帰版下降の初期 fuel は、根から葉までの必要段数へ短縮できる。 -/
theorem siftDownRecursive_eq_siftDownFuel_sub_root (values : Array Nat) (root : Nat) :
    LeanExperiments.HeapSort.siftDownRecursive values root =
      LeanExperiments.HeapSort.siftDownFuel (values.size - root) values root :=
  LeanExperiments.HeapSort.siftDownRecursive_eq_siftDownFuel_sub_root values root

/-- 下降処理は再帰先より上の配列位置を変えない。 -/
theorem siftDownFuel_getElem!_eq_of_lt_root (fuel : Nat) (values : Array Nat)
    (root index : Nat) (hIndex : index < values.size) (hBefore : index < root) :
    (LeanExperiments.HeapSort.siftDownFuel fuel values root)[index]! = values[index]! :=
  LeanExperiments.HeapSort.siftDownFuel_getElem!_eq_of_lt_root
    fuel values root index hIndex hBefore

/-- 交換する2位置以外では、交換前後の配列要素が一致する。 -/
private theorem siftDownSwap_getElem!_eq_of_ne (values : Array Nat) (i j k : Nat)
    (hIndex : k < values.size) (hNeI : k ≠ i) (hNeJ : k ≠ j) :
    (LeanExperiments.HeapSort.swap values i j)[k]! = values[k]! := by
  unfold LeanExperiments.HeapSort.swap
  by_cases hi : i < values.size
  · by_cases hj : j < values.size
    · rw [Array.swapIfInBounds_def, dite_eq_left hi, dite_eq_left hj]
      rw [getElem!_pos _ k (by simpa using hIndex), getElem!_pos values k hIndex]
      exact Array.getElem_swap_of_ne hNeI hNeJ
    · simp [Array.swapIfInBounds, hi, hj]
  · simp [Array.swapIfInBounds, hi]

/-- 部分木内の2位置を交換しても、その部分木の一様な値上界は保たれる。 -/
private theorem siftDownSwap_descendant_bound
    (values : Array Nat) (root i j bound : Nat)
    (hI : HeapDescendant root i) (hJ : HeapDescendant root j)
    (hIIn : i < values.size) (hJIn : j < values.size)
    (hBound : ∀ index, HeapDescendant root index → index < values.size →
      values[index]! ≤ bound) :
    ∀ index, HeapDescendant root index → index < values.size →
      (LeanExperiments.HeapSort.swap values i j)[index]! ≤ bound := by
  intro index hIndexPath hIndex
  by_cases hIndexI : index = i
  · subst index
    unfold LeanExperiments.HeapSort.swap
    rw [getElem!_pos _ i (by simpa using hIIn)]
    rw [Array.getElem_swapIfInBounds_left (xs := values) hJIn (by
      simpa [LeanExperiments.HeapSort.swap] using hIIn)]
    simpa [getElem!_pos values j hJIn] using hBound j hJ hJIn
  · by_cases hIndexJ : index = j
    · subst index
      unfold LeanExperiments.HeapSort.swap
      rw [getElem!_pos _ j (by simpa using hJIn)]
      rw [Array.getElem_swapIfInBounds_right (xs := values) hIIn (by
        simpa [LeanExperiments.HeapSort.swap] using hJIn)]
      simpa [getElem!_pos values i hIIn] using hBound i hI hIIn
    · rw [siftDownSwap_getElem!_eq_of_ne values i j index hIndex hIndexI hIndexJ]
      exact hBound index hIndexPath hIndex

/-- sift-down は開始位置の部分木に属さない要素を変更しない。 -/
theorem siftDownFuel_getElem!_eq_of_not_descendant
    (fuel : Nat) (values : Array Nat) (root index : Nat)
    (hIndex : index < values.size) (hNotDescendant : ¬ HeapDescendant root index) :
    (LeanExperiments.HeapSort.siftDownFuel fuel values root)[index]! = values[index]! := by
  induction fuel generalizing values root index with
  | zero => simp [LeanExperiments.HeapSort.siftDownFuel]
  | succ fuel ih =>
      let largest := LeanExperiments.HeapSort.siftDownLargest values root
      by_cases hDone : largest = root
      · simp [LeanExperiments.HeapSort.siftDownFuel, largest, hDone]
      · have hChildPath :
            HeapDescendant root largest := by
          rcases LeanExperiments.HeapSort.siftDownLargest_eq_root_or_child values root with
            hRoot | hLeft | hRight
          · exact (hDone hRoot).elim
          · simpa [largest, hLeft] using
              HeapDescendant.left (HeapDescendant.root root)
          · simpa [largest, hRight] using
              HeapDescendant.right (HeapDescendant.root root)
        have hNotLargestDescendant : ¬ HeapDescendant largest index := by
          intro hDescendant
          exact hNotDescendant (HeapDescendant.trans hChildPath hDescendant)
        have hIndexNeRoot : index ≠ root := by
          intro hEq
          apply hNotDescendant
          rw [hEq]
          exact HeapDescendant.root root
        have hIndexNeLargest : index ≠ largest := by
          intro hEq
          apply hNotDescendant
          rw [hEq]
          exact hChildPath
        have hSwapSize :
            (LeanExperiments.HeapSort.swap values root largest).size = values.size :=
          LeanExperiments.HeapSort.swap_size values root largest
        have hIndexSwap : index <
            (LeanExperiments.HeapSort.swap values root largest).size := by
          rw [hSwapSize]
          exact hIndex
        have hRecursive := ih (LeanExperiments.HeapSort.swap values root largest)
          largest index hIndexSwap hNotLargestDescendant
        have hFrame := siftDownSwap_getElem!_eq_of_ne
          values root largest index hIndex hIndexNeRoot hIndexNeLargest
        change (if largest == root then values else
          LeanExperiments.HeapSort.siftDownFuel fuel
            (LeanExperiments.HeapSort.swap values root largest) largest)[index]! = _
        have hNotStopped : (largest == root) = false := by simp [hDone]
        simp [hNotStopped, hRecursive, hFrame]

/-- sift-down は開始部分木の値域上界を、下降後も保つ。

各交換の両端は開始部分木内にあり、次の再帰呼び出しが触れる範囲は選択した子の
部分木に限られる。帰納法ではその部分木内と外側の位置を分けて上界を引き継ぐ。
-/
theorem siftDownFuel_descendant_bound
    (fuel : Nat) (values : Array Nat) (root bound : Nat)
    (hBound : ∀ index, HeapDescendant root index → index < values.size →
      values[index]! ≤ bound) :
    ∀ index, HeapDescendant root index → index < values.size →
      (LeanExperiments.HeapSort.siftDownFuel fuel values root)[index]! ≤ bound := by
  induction fuel generalizing values root with
  | zero =>
      intro index hPath hIndex
      simpa [LeanExperiments.HeapSort.siftDownFuel] using hBound index hPath hIndex
  | succ fuel ih =>
      intro index hPath hIndex
      let largest := LeanExperiments.HeapSort.siftDownLargest values root
      by_cases hDone : largest = root
      · simpa [LeanExperiments.HeapSort.siftDownFuel, largest, hDone] using
          hBound index hPath hIndex
      · have hRootIn : root < values.size := by
          by_cases hRootIn : root < values.size
          · exact hRootIn
          · have hRootLe : values.size ≤ root := by omega
            have hNoLeft : ¬ 2 * root + 1 < values.size := by omega
            have hNoRight : ¬ 2 * root + 2 < values.size := by omega
            have hLargestEq : largest = root := by
              simp [largest, LeanExperiments.HeapSort.siftDownLargest, hNoLeft, hNoRight]
            exact (hDone hLargestEq).elim
        have hLargestIn : largest < values.size :=
          siftDownLargest_lt_size values root hRootIn
        have hChildPath : HeapDescendant root largest := by
          rcases LeanExperiments.HeapSort.siftDownLargest_eq_root_or_child values root with
            hRoot | hLeft | hRight
          · exact (hDone hRoot).elim
          · simpa [largest, hLeft] using HeapDescendant.left (HeapDescendant.root root)
          · simpa [largest, hRight] using HeapDescendant.right (HeapDescendant.root root)
        have hSwapSize := LeanExperiments.HeapSort.swap_size values root largest
        have hSwapBound := siftDownSwap_descendant_bound values root root largest bound
          (HeapDescendant.root root) hChildPath hRootIn hLargestIn hBound
        have hIndexSwap : index <
            (LeanExperiments.HeapSort.swap values root largest).size := by
          rw [hSwapSize]
          exact hIndex
        have hNotStopped : (largest == root) = false := by simp [hDone]
        change (if largest == root then values else
          LeanExperiments.HeapSort.siftDownFuel fuel
            (LeanExperiments.HeapSort.swap values root largest) largest)[index]! ≤ bound
        simp only [hNotStopped, Bool.false_eq_true, ite_false]
        by_cases hInChild : HeapDescendant largest index
        · have hChildBound :
              ∀ childIndex, HeapDescendant largest childIndex →
                childIndex < (LeanExperiments.HeapSort.swap values root largest).size →
                (LeanExperiments.HeapSort.swap values root largest)[childIndex]! ≤ bound := by
            intro childIndex hChildPath' hChildIndex
            have hInRoot := HeapDescendant.trans hChildPath hChildPath'
            have hChildIndexBefore : childIndex < values.size := by
              rw [← hSwapSize]
              exact hChildIndex
            exact hSwapBound childIndex hInRoot hChildIndexBefore
          exact ih (LeanExperiments.HeapSort.swap values root largest) largest
            hChildBound index hInChild hIndexSwap
        · have hFrame := siftDownFuel_getElem!_eq_of_not_descendant
            fuel (LeanExperiments.HeapSort.swap values root largest) largest index
            hIndexSwap hInChild
          rw [hFrame]
          exact hSwapBound index hPath hIndex

/-- 根が配列内にあるとき、任意 fuel の下降後も開始位置の値は下がらない。 -/
theorem siftDownFuel_root_value_ge_of_root_in_bounds
    (fuel : Nat) (values : Array Nat) (root : Nat)
    (hRoot : root < values.size) :
    values[root]! ≤ (LeanExperiments.HeapSort.siftDownFuel fuel values root)[root]! := by
  induction fuel generalizing values root with
  | zero => exact Nat.le_refl _
  | succ fuel _ =>
      let largest := LeanExperiments.HeapSort.siftDownLargest values root
      change values[root]! ≤
        (if largest == root then values else
          LeanExperiments.HeapSort.siftDownFuel fuel
            (LeanExperiments.HeapSort.swap values root largest) largest)[root]!
      by_cases hStop : largest = root
      · simp [hStop]
      · have hRootLtLargest : root < largest := by
          have hGe := LeanExperiments.HeapSort.siftDownLargest_ge values root
          omega
        have hLargestBound := siftDownLargest_lt_size values root hRoot
        have hSwapRootBound :
            root < (LeanExperiments.HeapSort.swap values root largest).size := by
          simpa [LeanExperiments.HeapSort.swap] using hRoot
        have hSwapRoot :
            (LeanExperiments.HeapSort.swap values root largest)[root]! = values[largest]! := by
          unfold LeanExperiments.HeapSort.swap
          rw [getElem!_pos _ root hSwapRootBound]
          rw [Array.getElem_swapIfInBounds_left (xs := values)
            hLargestBound hSwapRootBound]
          exact (getElem!_pos values largest hLargestBound).symm
        have hRootPromoted : values[root]! ≤
            (LeanExperiments.HeapSort.swap values root largest)[root]! := by
          rw [hSwapRoot]
          exact Nat.le_of_lt (siftDownLargest_value_gt_of_moves values root (by
            simpa [largest] using hStop))
        have hFrame := siftDownFuel_getElem!_eq_of_lt_root fuel
          (LeanExperiments.HeapSort.swap values root largest) largest root
          (by simpa [LeanExperiments.HeapSort.swap] using hRoot)
          hRootLtLargest
        have hNotStopped : (largest == root) = false := by simp [hStop]
        simp [hNotStopped]
        rw [hFrame]
        exact hRootPromoted

/-- 任意の添字で、fuel 付き下降後の同位置の値は元の値以上である。

根が範囲外なら子も存在せず配列を変更しないため、`getElem!` の既定値も保たれる。
-/
theorem siftDownFuel_root_value_ge (fuel : Nat) (values : Array Nat) (root : Nat) :
    values[root]! ≤ (LeanExperiments.HeapSort.siftDownFuel fuel values root)[root]! := by
  by_cases hRoot : root < values.size
  · exact siftDownFuel_root_value_ge_of_root_in_bounds fuel values root hRoot
  · have hNoLeftChild : values.size ≤ 2 * root + 1 := by omega
    rw [LeanExperiments.HeapSort.siftDownFuel_eq_self_of_noLeftChild
      fuel values root hNoLeftChild]
    exact Nat.le_refl _

/-- 正の fuel の下降後、根の値は開始時に選ばれた最大候補の値と一致する。

最初の段で選んだ値を根へ移し、再帰先が根より後ろであることとフレーム定理から、
その後の下降でも根の値が保たれる。
-/
theorem siftDownFuel_root_eq_initial_largest
    (fuel : Nat) (values : Array Nat) (root : Nat)
    (hFuel : 0 < fuel) (hRoot : root < values.size) :
    (LeanExperiments.HeapSort.siftDownFuel fuel values root)[root]! =
      values[LeanExperiments.HeapSort.siftDownLargest values root]! := by
  cases fuel with
  | zero => omega
  | succ fuel =>
      let largest := LeanExperiments.HeapSort.siftDownLargest values root
      have hLargestBound := siftDownLargest_lt_size values root hRoot
      have hSwapRootBound :
          root < (LeanExperiments.HeapSort.swap values root largest).size := by
        simpa [LeanExperiments.HeapSort.swap] using hRoot
      have hSwapRoot :
          (LeanExperiments.HeapSort.swap values root largest)[root]! = values[largest]! := by
        unfold LeanExperiments.HeapSort.swap
        rw [getElem!_pos _ root hSwapRootBound]
        rw [Array.getElem_swapIfInBounds_left (xs := values)
          hLargestBound hSwapRootBound]
        exact (getElem!_pos values largest hLargestBound).symm
      by_cases hStop : largest = root
      · have hStopProp : largest == root := by simp [hStop]
        change (if largest == root then values else
          LeanExperiments.HeapSort.siftDownFuel fuel
            (LeanExperiments.HeapSort.swap values root largest) largest)[root]! = _
        simp only [ite_eq_left hStopProp]
        change values[root]! = values[largest]!
        rw [hStop]
      · have hRootLtLargest : root < largest := by
          have hGe := LeanExperiments.HeapSort.siftDownLargest_ge values root
          omega
        have hFrame := siftDownFuel_getElem!_eq_of_lt_root fuel
          (LeanExperiments.HeapSort.swap values root largest) largest root
          hSwapRootBound hRootLtLargest
        have hNotStopProp : ¬ (largest == root) := by simp [hStop]
        have hOutputRoot :
            (LeanExperiments.HeapSort.siftDownFuel (fuel + 1) values root)[root]! =
              values[largest]! := by
          change (if largest == root then values else
            LeanExperiments.HeapSort.siftDownFuel fuel
              (LeanExperiments.HeapSort.swap values root largest) largest)[root]! = _
          simp only [ite_eq_right hNotStopProp]
          rw [hFrame, hSwapRoot]
        exact hOutputRoot

/-- 正の fuel の下降後、開始位置の値は開始時の左右の子以上になる。

最初に根・左右の子から最大候補を選び、その値を根へ移すことから従う。
-/
theorem siftDownFuel_root_dominates_initial_children
    (fuel : Nat) (values : Array Nat) (root : Nat)
    (hFuel : 0 < fuel) (hRoot : root < values.size) :
    (2 * root + 1 < values.size →
      values[2 * root + 1]! ≤ (LeanExperiments.HeapSort.siftDownFuel fuel values root)[root]!) ∧
    (2 * root + 2 < values.size →
      values[2 * root + 2]! ≤ (LeanExperiments.HeapSort.siftDownFuel fuel values root)[root]!) := by
  rw [siftDownFuel_root_eq_initial_largest fuel values root hFuel hRoot]
  exact ⟨(siftDownLargest_value_ge_valid_candidates values root).2.1,
    (siftDownLargest_value_ge_valid_candidates values root).2.2⟩

/-- 再帰版下降後の根は、開始時点の根と左右の子をすべて支配する。

根が配列外なら子も存在しないため、条件は自動的に満たされる。
-/
theorem siftDownRecursive_root_dominates_initial_children (values : Array Nat) (root : Nat) :
    (2 * root + 1 < values.size →
      values[2 * root + 1]! ≤
        (LeanExperiments.HeapSort.siftDownRecursive values root)[root]!) ∧
    (2 * root + 2 < values.size →
      values[2 * root + 2]! ≤
        (LeanExperiments.HeapSort.siftDownRecursive values root)[root]!) := by
  by_cases hRoot : root < values.size
  · unfold LeanExperiments.HeapSort.siftDownRecursive
    exact siftDownFuel_root_dominates_initial_children values.size values root
      (by omega) hRoot
  · constructor <;> intro hChild <;> omega

/-- 配列内の根では、下降後の根の値が最初に選んだ最大候補の値と一致する。

再帰下降は初手で選んだ値を根へ移し、その後の呼び出しは根より後ろだけを変更する。
この等式により、実装の比較選択を値の最大性へ結び付けられる。
-/
theorem siftDownRecursive_root_eq_initial_largest (values : Array Nat) (root : Nat)
    (hRoot : root < values.size) :
    (LeanExperiments.HeapSort.siftDownRecursive values root)[root]! =
      values[LeanExperiments.HeapSort.siftDownLargest values root]! := by
  unfold LeanExperiments.HeapSort.siftDownRecursive
  exact siftDownFuel_root_eq_initial_largest values.size values root (by omega) hRoot

/-- 下降後の根は、下降開始時の根と左右の子を全て支配する。

再帰下降が根へ持ち上げる値は初期候補の最大値であり、以後の再帰は根より深い添字だけを
変更する。この局所契約は、下降先の部分木が整っていることを示す証明で利用できる。
-/
theorem siftDownRecursive_root_dominates_initial_root_and_children
    (values : Array Nat) (root : Nat) :
    values[root]! ≤ (LeanExperiments.HeapSort.siftDownRecursive values root)[root]! ∧
      (2 * root + 1 < values.size →
        values[2 * root + 1]! ≤
          (LeanExperiments.HeapSort.siftDownRecursive values root)[root]!) ∧
      (2 * root + 2 < values.size →
        values[2 * root + 2]! ≤
          (LeanExperiments.HeapSort.siftDownRecursive values root)[root]!) := by
  by_cases hRoot : root < values.size
  · rw [siftDownRecursive_root_eq_initial_largest values root hRoot]
    exact siftDownLargest_value_ge_valid_candidates values root
  · have hNoLeftChild : values.size ≤ 2 * root + 1 := by omega
    rw [LeanExperiments.HeapSort.siftDownRecursive_eq_self_of_noLeftChild
      values root hNoLeftChild]
    refine ⟨Nat.le_refl _, ?_, ?_⟩ <;> intro hChild <;> omega

/-- 根以外の親子条件から、根より下の各要素を根の子の最大値で抑える。

`hBelow` は親添字が0より大きい位置のヒープ条件を表す。根の子に達した場合を
帰納法の基底とし、それ以外では親子条件を一段適用して親へ戻る。
-/
theorem value_le_root_children_max_of_heap_below_root (values : Array Nat)
    (hBelow : ∀ parent, 0 < parent → parent < values.size →
      (2 * parent + 1 < values.size → values[2 * parent + 1]! ≤ values[parent]!) ∧
      (2 * parent + 2 < values.size → values[2 * parent + 2]! ≤ values[parent]!)) :
    ∀ index, 0 < index → index < values.size →
      values[index]! ≤ max values[1]! values[2]! := by
  intro index
  induction index using Nat.strongRecOn with
  | ind index ih =>
      intro hPositive hIndex
      let parent := (index - 1) / 2
      have hParentLt : parent < index := by
        dsimp [parent]
        omega
      have hParentBound : parent < values.size := Nat.lt_trans hParentLt hIndex
      have hChild : index = 2 * parent + 1 ∨ index = 2 * parent + 2 := by
        dsimp [parent]
        omega
      by_cases hParentZero : parent = 0
      · rcases hChild with hLeft | hRight
        · rw [hLeft, hParentZero]
          exact Nat.le_max_left _ _
        · rw [hRight, hParentZero]
          exact Nat.le_max_right _ _
      · have hParentPositive : 0 < parent := by omega
        have hParentChild := hBelow parent hParentPositive hParentBound
        have hIndexLeParent : values[index]! ≤ values[parent]! := by
          rcases hChild with hLeft | hRight
          · rw [hLeft]
            exact hParentChild.1 (by omega)
          · rw [hRight]
            exact hParentChild.2 (by omega)
        exact Nat.le_trans hIndexLeParent
          (ih parent hParentLt hParentPositive hParentBound)

/-- 根以外の親子条件が成立する部分木では、全要素が根とその二つの子の最大値以下。

部分木の根だけは任意の値でよく、それより下の親子辺に `hBelow` を要求する。
この形は、根からの sift-down が部分木内の条件を回復する証明の帰納不変条件に使える。
-/
theorem value_le_root_or_children_max_of_heap_below_root (values : Array Nat)
    (root : Nat)
    (hBelow : ∀ parent, root < parent → parent < values.size →
      (2 * parent + 1 < values.size → values[2 * parent + 1]! ≤ values[parent]!) ∧
      (2 * parent + 2 < values.size → values[2 * parent + 2]! ≤ values[parent]!)) :
    ∀ index, HeapDescendant root index → index < values.size →
      values[index]! ≤ max values[root]! (max values[2 * root + 1]! values[2 * root + 2]!) := by
  intro index hDescendant
  induction hDescendant with
  | root =>
      intro hIndex
      exact Nat.le_max_left _ _
  | left hParent ih =>
      rename_i subroot
      intro hIndex
      by_cases hParentRoot : subroot = root
      · subst subroot
        exact Nat.le_trans (Nat.le_max_left _ _)
          (Nat.le_max_right _ _)
      · have hRootLtParent : root < subroot := by
          have hRootLeParent := hParent.root_le
          omega
        have hParentLt : subroot < values.size := by omega
        have hEdges := hBelow subroot hRootLtParent hParentLt
        have hChildLeParent : values[2 * subroot + 1]! ≤ values[subroot]! :=
          hEdges.1 (by omega)
        exact Nat.le_trans hChildLeParent (ih (by omega))
  | right hParent ih =>
      rename_i subroot
      intro hIndex
      by_cases hParentRoot : subroot = root
      · subst subroot
        exact Nat.le_trans (Nat.le_max_right _ _)
          (Nat.le_max_right _ _)
      · have hRootLtParent : root < subroot := by
          have hRootLeParent := hParent.root_le
          omega
        have hParentLt : subroot < values.size := by omega
        have hEdges := hBelow subroot hRootLtParent hParentLt
        have hChildLeParent : values[2 * subroot + 2]! ≤ values[subroot]! :=
          hEdges.2 (by omega)
        exact Nat.le_trans hChildLeParent (ih (by omega))

/-- 任意の部分木で、下位のヒープ条件を保った sift-down 後の根は全要素を支配する。

子孫の入力値を元の根と左右の子の最大値で抑え、下降処理後の根がその3値以上である
ことを合成する。部分木根が添字0であることは要求しない。
-/
theorem siftDownRecursive_root_bounds_descendants_of_heap_below_root
    (values : Array Nat) (root : Nat)
    (hBelow : ∀ parent, root < parent → parent < values.size →
      (2 * parent + 1 < values.size → values[2 * parent + 1]! ≤ values[parent]!) ∧
      (2 * parent + 2 < values.size → values[2 * parent + 2]! ≤ values[parent]!)) :
    ∀ index, HeapDescendant root index → index < values.size →
      values[index]! ≤
        (LeanExperiments.HeapSort.siftDownRecursive values root)[root]! := by
  intro index hDescendant hIndex
  have hSubtreeBound := value_le_root_or_children_max_of_heap_below_root
    values root hBelow index hDescendant hIndex
  have hRootAndChildren :=
    siftDownRecursive_root_dominates_initial_root_and_children values root
  have hRootBound : values[root]! ≤
      (LeanExperiments.HeapSort.siftDownRecursive values root)[root]! :=
    hRootAndChildren.1
  have hLeftBound : values[2 * root + 1]! ≤
      (LeanExperiments.HeapSort.siftDownRecursive values root)[root]! := by
    by_cases hLeft : 2 * root + 1 < values.size
    · exact hRootAndChildren.2.1 hLeft
    · rw [getElem!_neg values (2 * root + 1) hLeft]
      exact Nat.zero_le _
  have hRightBound : values[2 * root + 2]! ≤
      (LeanExperiments.HeapSort.siftDownRecursive values root)[root]! := by
    by_cases hRight : 2 * root + 2 < values.size
    · exact hRootAndChildren.2.2 hRight
    · rw [getElem!_neg values (2 * root + 2) hRight]
      exact Nat.zero_le _
  have hMaximumBound :
      max values[root]! (max values[2 * root + 1]! values[2 * root + 2]!) ≤
        (LeanExperiments.HeapSort.siftDownRecursive values root)[root]! :=
    (Nat.max_le).2 ⟨hRootBound, (Nat.max_le).2 ⟨hLeftBound, hRightBound⟩⟩
  exact Nat.le_trans hSubtreeBound hMaximumBound

/-- 下位のヒープ条件が成立する部分木では、下降後の根が出力部分木全体を支配する。

入力部分木の値は元の根と左右の子の最大値以下であり、この値域上界は一般補題により
下降後も保たれる。一方、出力根はその3値以上なので、部分木の全出力値を支配する。
-/
theorem siftDownRecursive_root_dominates_output_descendants_of_heap_below_root
    (values : Array Nat) (root : Nat)
    (hBelow : ∀ parent, root < parent → parent < values.size →
      (2 * parent + 1 < values.size → values[2 * parent + 1]! ≤ values[parent]!) ∧
      (2 * parent + 2 < values.size → values[2 * parent + 2]! ≤ values[parent]!)) :
    ∀ index, HeapDescendant root index → index < values.size →
      (LeanExperiments.HeapSort.siftDownRecursive values root)[index]! ≤
        (LeanExperiments.HeapSort.siftDownRecursive values root)[root]! := by
  let bound := max values[root]! (max values[2 * root + 1]! values[2 * root + 2]!)
  have hInputBound := value_le_root_or_children_max_of_heap_below_root values root hBelow
  have hOutputBound : ∀ index, HeapDescendant root index → index < values.size →
      (LeanExperiments.HeapSort.siftDownRecursive values root)[index]! ≤ bound := by
    intro index hPath hIndex
    unfold LeanExperiments.HeapSort.siftDownRecursive
    exact siftDownFuel_descendant_bound values.size values root bound
      hInputBound index hPath hIndex
  have hRootAndChildren :=
    siftDownRecursive_root_dominates_initial_root_and_children values root
  have hRootBound : values[root]! ≤
      (LeanExperiments.HeapSort.siftDownRecursive values root)[root]! :=
    hRootAndChildren.1
  have hLeftBound : values[2 * root + 1]! ≤
      (LeanExperiments.HeapSort.siftDownRecursive values root)[root]! := by
    by_cases hLeft : 2 * root + 1 < values.size
    · exact hRootAndChildren.2.1 hLeft
    · rw [getElem!_neg values (2 * root + 1) hLeft]
      exact Nat.zero_le _
  have hRightBound : values[2 * root + 2]! ≤
      (LeanExperiments.HeapSort.siftDownRecursive values root)[root]! := by
    by_cases hRight : 2 * root + 2 < values.size
    · exact hRootAndChildren.2.2 hRight
    · rw [getElem!_neg values (2 * root + 2) hRight]
      exact Nat.zero_le _
  have hBound : bound ≤
      (LeanExperiments.HeapSort.siftDownRecursive values root)[root]! := by
    dsimp [bound]
    exact (Nat.max_le).2 ⟨hRootBound, (Nat.max_le).2 ⟨hLeftBound, hRightBound⟩⟩
  intro index hPath hIndex
  exact Nat.le_trans (hOutputBound index hPath hIndex) hBound

/-- 下位部分木がヒープなら、再帰版下降後に開始位置の左右のヒープ辺が成立する。

部分木全体で根が最大になる定理から、存在する左右の子に限定した局所ヒープ条件を
取り出す。ヒープ構築を下から合成するときの根ケースで使える形にしている。
-/
theorem siftDownRecursive_root_edges_of_heap_below_root
    (values : Array Nat) (root : Nat)
    (hBelow : ∀ parent, root < parent → parent < values.size →
      (2 * parent + 1 < values.size → values[2 * parent + 1]! ≤ values[parent]!) ∧
      (2 * parent + 2 < values.size → values[2 * parent + 2]! ≤ values[parent]!)) :
    (2 * root + 1 < values.size →
      (LeanExperiments.HeapSort.siftDownRecursive values root)[2 * root + 1]! ≤
        (LeanExperiments.HeapSort.siftDownRecursive values root)[root]!) ∧
    (2 * root + 2 < values.size →
      (LeanExperiments.HeapSort.siftDownRecursive values root)[2 * root + 2]! ≤
        (LeanExperiments.HeapSort.siftDownRecursive values root)[root]!) := by
  have hDominates :=
    siftDownRecursive_root_dominates_output_descendants_of_heap_below_root
      values root hBelow
  constructor
  · intro hLeft
    exact hDominates (2 * root + 1) (HeapDescendant.left (HeapDescendant.root root)) hLeft
  · intro hRight
    exact hDominates (2 * root + 2) (HeapDescendant.right (HeapDescendant.root root)) hRight

/-- 選択した子の部分木外にある親子辺は、再帰版 sift-down 前後で保存される。

下降先以外にある辺の両端は、最初の根と選択子の交換にも再帰呼び出しにも触れない。
このフレーム補題を各段で合成し、部分木全体のヒープ保存を証明する。
-/
theorem siftDownRecursive_heapEdge_iff_of_outside_selected_subtree
    (values : Array Nat) (root parent child : Nat)
    (hRootLtParent : root < parent)
    (hParentIn : parent < values.size) (hChildIn : child < values.size)
    (hChild : child = 2 * parent + 1 ∨ child = 2 * parent + 2)
    (hParentOutside :
      ¬ HeapDescendant (LeanExperiments.HeapSort.siftDownLargest values root) parent) :
    (LeanExperiments.HeapSort.siftDownRecursive values root)[child]! ≤
        (LeanExperiments.HeapSort.siftDownRecursive values root)[parent]! ↔
      values[child]! ≤ values[parent]! := by
  let largest := LeanExperiments.HeapSort.siftDownLargest values root
  by_cases hDone : largest = root
  · have hChildren := (siftDownLargest_eq_index_iff_dominatesChildren values root).mp (by
      simpa [largest] using hDone)
    have hSame := LeanExperiments.HeapSort.siftDownRecursive_eq_self_of_dominatesChildren
      values root hChildren.1 hChildren.2
    rw [hSame]
  · have hLargestShape : largest = 2 * root + 1 ∨ largest = 2 * root + 2 := by
      rcases LeanExperiments.HeapSort.siftDownLargest_eq_root_or_child values root with
        hRoot | hLeft | hRight
      · exact (hDone (by simpa [largest] using hRoot)).elim
      · exact Or.inl (by simpa [largest] using hLeft)
      · exact Or.inr (by simpa [largest] using hRight)
    have hChildOutside := HeapDescendant.child_not_descendant_of_selected_child
      root largest parent child hLargestShape hRootLtParent hParentOutside hChild
    have hParentNeRoot : parent ≠ root := by omega
    have hChildGtParent : parent < child := by
      rcases hChild with hLeft | hRight <;> omega
    have hChildNeRoot : child ≠ root := by omega
    change ¬ HeapDescendant largest parent at hParentOutside
    have hParentNeLargest : parent ≠ largest := by
      intro hEq
      apply hParentOutside
      rw [hEq]
      exact HeapDescendant.root largest
    have hChildNeLargest : child ≠ largest := by
      intro hEq
      subst child
      exact hChildOutside (HeapDescendant.root largest)
    let candidate := LeanExperiments.HeapSort.swap values root largest
    have hCandidateSize : candidate.size = values.size := by
      dsimp [candidate]
      exact LeanExperiments.HeapSort.swap_size values root largest
    have hCandidateParent :
        (LeanExperiments.HeapSort.siftDownRecursive candidate largest)[parent]! =
          candidate[parent]! := by
      unfold LeanExperiments.HeapSort.siftDownRecursive
      exact siftDownFuel_getElem!_eq_of_not_descendant candidate.size candidate largest
        parent (by rw [hCandidateSize]; exact hParentIn) hParentOutside
    have hCandidateChild :
        (LeanExperiments.HeapSort.siftDownRecursive candidate largest)[child]! =
          candidate[child]! := by
      unfold LeanExperiments.HeapSort.siftDownRecursive
      exact siftDownFuel_getElem!_eq_of_not_descendant candidate.size candidate largest
        child (by rw [hCandidateSize]; exact hChildIn) hChildOutside
    have hSwapParent : candidate[parent]! = values[parent]! := by
      dsimp [candidate]
      exact siftDownSwap_getElem!_eq_of_ne values root largest parent hParentIn
        hParentNeRoot hParentNeLargest
    have hSwapChild : candidate[child]! = values[child]! := by
      dsimp [candidate]
      exact siftDownSwap_getElem!_eq_of_ne values root largest child hChildIn
        hChildNeRoot hChildNeLargest
    have hRecursive := siftDownRecursive_eq_after_selected_swap values root largest
      (by simp [largest]) hDone
    rw [hRecursive, hCandidateChild, hCandidateParent, hSwapChild, hSwapParent]

/-- 十分な fuel の sift-down は、開始部分木の親子条件を全て最大ヒープにする。

開始根より大きい親添字の辺が入力時点で成立していることを仮定する。選択した子の
部分木では fuel 帰納法を適用し、その外の辺は交換・再帰処理のフレーム性で保存する。
-/
theorem siftDownFuel_subtree_maxHeap_of_heap_below_root
    (fuel : Nat) (values : Array Nat) (root : Nat)
    (hEnough : values.size ≤ fuel + root)
    (hBelow : ∀ parent, root < parent → parent < values.size →
      (2 * parent + 1 < values.size → values[2 * parent + 1]! ≤ values[parent]!) ∧
      (2 * parent + 2 < values.size → values[2 * parent + 2]! ≤ values[parent]!)) :
    ∀ parent, HeapDescendant root parent → parent < values.size →
      (2 * parent + 1 < values.size →
        (LeanExperiments.HeapSort.siftDownFuel fuel values root)[2 * parent + 1]! ≤
          (LeanExperiments.HeapSort.siftDownFuel fuel values root)[parent]!) ∧
      (2 * parent + 2 < values.size →
        (LeanExperiments.HeapSort.siftDownFuel fuel values root)[2 * parent + 2]! ≤
          (LeanExperiments.HeapSort.siftDownFuel fuel values root)[parent]!) := by
  induction fuel generalizing values root with
  | zero =>
      intro parent hPath hParentIn
      have hRootLeParent := hPath.root_le
      omega
  | succ fuel ih =>
      intro parent hPath hParentIn
      have hRootIn : root < values.size := by
        have hRootLeParent := hPath.root_le
        omega
      have hCurrentEq :
          LeanExperiments.HeapSort.siftDownFuel (fuel + 1) values root =
            LeanExperiments.HeapSort.siftDownRecursive values root := by
        calc
          LeanExperiments.HeapSort.siftDownFuel (fuel + 1) values root =
              LeanExperiments.HeapSort.siftDownFuel (values.size - root) values root :=
            siftDownFuel_eq_of_size_le_fuel_add_root (fuel + 1) values root (by omega)
          _ = LeanExperiments.HeapSort.siftDownRecursive values root :=
            (siftDownRecursive_eq_siftDownFuel_sub_root values root).symm
      by_cases hParentRoot : parent = root
      · subst parent
        rw [hCurrentEq]
        exact siftDownRecursive_root_edges_of_heap_below_root values root hBelow
      · have hParentAfterRoot : root < parent := by
          have hRootLeParent := hPath.root_le
          omega
        let largest := LeanExperiments.HeapSort.siftDownLargest values root
        by_cases hDone : largest = root
        · simpa [LeanExperiments.HeapSort.siftDownFuel, largest, hDone] using
            hBelow parent hParentAfterRoot hParentIn
        · have hRootLtLargest : root < largest := by
            have hLargestGe := LeanExperiments.HeapSort.siftDownLargest_ge values root
            omega
          have hLargestIn := siftDownLargest_lt_size values root hRootIn
          have hLargestShape : largest = 2 * root + 1 ∨ largest = 2 * root + 2 := by
            rcases LeanExperiments.HeapSort.siftDownLargest_eq_root_or_child values root with
              hRoot | hLeft | hRight
            · exact (hDone hRoot).elim
            · exact Or.inl hLeft
            · exact Or.inr hRight
          let candidate := LeanExperiments.HeapSort.swap values root largest
          have hSwapSize : candidate.size = values.size := by
            dsimp [candidate]
            exact LeanExperiments.HeapSort.swap_size values root largest
          have hEnoughNext : candidate.size ≤ fuel + largest := by
            rw [hSwapSize]
            omega
          have hBelowNext : ∀ nextParent, largest < nextParent →
              nextParent < candidate.size →
              (2 * nextParent + 1 < candidate.size →
                candidate[2 * nextParent + 1]! ≤ candidate[nextParent]!) ∧
              (2 * nextParent + 2 < candidate.size →
                candidate[2 * nextParent + 2]! ≤ candidate[nextParent]!) := by
            intro nextParent hLargestLtParent hNextParentIn
            have hParentAfterRoot : root < nextParent := by omega
            have hNextParentInValues : nextParent < values.size := by
              rw [← hSwapSize]
              exact hNextParentIn
            have hInputEdge := hBelow nextParent hParentAfterRoot hNextParentInValues
            constructor
            · intro hLeft
              have hChildIn : 2 * nextParent + 1 < values.size := by
                rw [← hSwapSize]
                exact hLeft
              have hChildFrame := siftDownSwap_getElem!_eq_of_ne
                values root largest (2 * nextParent + 1) hChildIn (by omega) (by omega)
              have hParentFrame := siftDownSwap_getElem!_eq_of_ne
                values root largest nextParent hNextParentInValues (by omega) (by omega)
              rw [hChildFrame, hParentFrame]
              exact hInputEdge.1 hChildIn
            · intro hRight
              have hChildIn : 2 * nextParent + 2 < values.size := by
                rw [← hSwapSize]
                exact hRight
              have hChildFrame := siftDownSwap_getElem!_eq_of_ne
                values root largest (2 * nextParent + 2) hChildIn (by omega) (by omega)
              have hParentFrame := siftDownSwap_getElem!_eq_of_ne
                values root largest nextParent hNextParentInValues (by omega) (by omega)
              rw [hChildFrame, hParentFrame]
              exact hInputEdge.2 hChildIn
          have hNotStopped : (largest == root) = false := by simp [hDone]
          change (2 * parent + 1 < values.size →
              (if largest == root then values else
                LeanExperiments.HeapSort.siftDownFuel fuel candidate largest)[2 * parent + 1]! ≤
              (if largest == root then values else
                LeanExperiments.HeapSort.siftDownFuel fuel candidate largest)[parent]!) ∧
            (2 * parent + 2 < values.size →
              (if largest == root then values else
                LeanExperiments.HeapSort.siftDownFuel fuel candidate largest)[2 * parent + 2]! ≤
              (if largest == root then values else
                LeanExperiments.HeapSort.siftDownFuel fuel candidate largest)[parent]!)
          simp only [hNotStopped, Bool.false_eq_true, ite_false]
          by_cases hParentInChild : HeapDescendant largest parent
          · have hParentCandidateIn : parent < candidate.size := by
              rw [hSwapSize]
              exact hParentIn
            simpa [hSwapSize] using ih candidate largest hEnoughNext hBelowNext parent
              hParentInChild hParentCandidateIn
          · have hLeftOutside := HeapDescendant.child_not_descendant_of_selected_child
              root largest parent (2 * parent + 1) hLargestShape hParentAfterRoot
              hParentInChild (Or.inl rfl)
            have hRightOutside := HeapDescendant.child_not_descendant_of_selected_child
              root largest parent (2 * parent + 2) hLargestShape hParentAfterRoot
              hParentInChild (Or.inr rfl)
            have hParentFrame := siftDownFuel_getElem!_eq_of_not_descendant
              fuel candidate largest parent (by rw [hSwapSize]; exact hParentIn)
              hParentInChild
            have hParentNeRoot : parent ≠ root := by omega
            have hParentNeLargest : parent ≠ largest := by
              intro hEq
              apply hParentInChild
              rw [hEq]
              exact HeapDescendant.root largest
            have hInputEdge := hBelow parent hParentAfterRoot hParentIn
            constructor
            · intro hLeft
              have hChildIn : 2 * parent + 1 < values.size := hLeft
              have hChildCandidateIn : 2 * parent + 1 < candidate.size := by
                rw [hSwapSize]
                exact hLeft
              have hLeftFrame := siftDownFuel_getElem!_eq_of_not_descendant
                fuel candidate largest (2 * parent + 1) hChildCandidateIn
                hLeftOutside
              have hSwapChild := siftDownSwap_getElem!_eq_of_ne
                values root largest (2 * parent + 1) hChildIn (by omega)
                (by intro hEq; apply hLeftOutside; simpa [hEq] using HeapDescendant.root largest)
              have hSwapParent := siftDownSwap_getElem!_eq_of_ne
                values root largest parent hParentIn hParentNeRoot hParentNeLargest
              rw [hLeftFrame, hParentFrame, hSwapChild, hSwapParent]
              exact hInputEdge.1 hChildIn
            · intro hRight
              have hChildIn : 2 * parent + 2 < values.size := hRight
              have hChildCandidateIn : 2 * parent + 2 < candidate.size := by
                rw [hSwapSize]
                exact hRight
              have hRightFrame := siftDownFuel_getElem!_eq_of_not_descendant
                fuel candidate largest (2 * parent + 2) hChildCandidateIn
                hRightOutside
              have hSwapChild := siftDownSwap_getElem!_eq_of_ne
                values root largest (2 * parent + 2) hChildIn (by omega)
                (by intro hEq; apply hRightOutside; simpa [hEq] using HeapDescendant.root largest)
              have hSwapParent := siftDownSwap_getElem!_eq_of_ne
                values root largest parent hParentIn hParentNeRoot hParentNeLargest
              rw [hRightFrame, hParentFrame, hSwapChild, hSwapParent]
              exact hInputEdge.2 hChildIn

/-- 根以降の親子辺は、根の下降後すべて最大ヒープ条件を満たす。

根の辺は下降の支配性で回復し、根の子孫内の辺は部分木定理で整える。
部分木外の辺は両端が下降の影響を受けないため保存される。
-/
theorem siftDownRecursive_heapEdges_from_root
    (values : Array Nat) (root : Nat)
    (hBelow : ∀ parent, root < parent → parent < values.size →
      (2 * parent + 1 < values.size → values[2 * parent + 1]! ≤ values[parent]!) ∧
      (2 * parent + 2 < values.size → values[2 * parent + 2]! ≤ values[parent]!)) :
    ∀ parent, root ≤ parent → parent < values.size →
      (2 * parent + 1 < values.size →
        (LeanExperiments.HeapSort.siftDownRecursive values root)[2 * parent + 1]! ≤
          (LeanExperiments.HeapSort.siftDownRecursive values root)[parent]!) ∧
      (2 * parent + 2 < values.size →
        (LeanExperiments.HeapSort.siftDownRecursive values root)[2 * parent + 2]! ≤
          (LeanExperiments.HeapSort.siftDownRecursive values root)[parent]!) := by
  unfold LeanExperiments.HeapSort.siftDownRecursive
  intro parent hRootLeParent hParentIn
  by_cases hParentRoot : parent = root
  · subst parent
    exact siftDownRecursive_root_edges_of_heap_below_root values root hBelow
  · have hRootLtParent : root < parent := by omega
    by_cases hParentDescendant : HeapDescendant root parent
    · have hSubtree := siftDownFuel_subtree_maxHeap_of_heap_below_root
        values.size values root (by omega) hBelow parent hParentDescendant hParentIn
      simpa [LeanExperiments.HeapSort.siftDownRecursive] using hSubtree
    · have hEdge := hBelow parent hRootLtParent hParentIn
      constructor
      · intro hChildIn
        have hChildOutside : ¬ HeapDescendant root (2 * parent + 1) := by
          intro hChildDescendant
          have hParentPath := hChildDescendant.parent_of_lt (by omega)
          have hParentEq : ((2 * parent + 1 - 1) / 2) = parent := by omega
          rw [hParentEq] at hParentPath
          exact hParentDescendant hParentPath
        have hParentFrame := siftDownFuel_getElem!_eq_of_not_descendant
          values.size values root parent hParentIn hParentDescendant
        have hChildFrame := siftDownFuel_getElem!_eq_of_not_descendant
          values.size values root (2 * parent + 1) hChildIn hChildOutside
        rw [hChildFrame, hParentFrame]
        exact hEdge.1 hChildIn
      · intro hChildIn
        have hChildOutside : ¬ HeapDescendant root (2 * parent + 2) := by
          intro hChildDescendant
          have hParentPath := hChildDescendant.parent_of_lt (by omega)
          have hParentEq : ((2 * parent + 2 - 1) / 2) = parent := by omega
          rw [hParentEq] at hParentPath
          exact hParentDescendant hParentPath
        have hParentFrame := siftDownFuel_getElem!_eq_of_not_descendant
          values.size values root parent hParentIn hParentDescendant
        have hChildFrame := siftDownFuel_getElem!_eq_of_not_descendant
          values.size values root (2 * parent + 2) hChildIn hChildOutside
        rw [hChildFrame, hParentFrame]
        exact hEdge.2 hChildIn

/-- 配列の根以外がすでにヒープなら、再帰版 sift-down 後の配列全体が最大ヒープになる。 -/
theorem siftDownRecursive_maxHeap_of_heap_below_root
    (values : Array Nat)
    (hBelow : ∀ parent, 0 < parent → parent < values.size →
      (2 * parent + 1 < values.size → values[2 * parent + 1]! ≤ values[parent]!) ∧
      (2 * parent + 2 < values.size → values[2 * parent + 2]! ≤ values[parent]!)) :
    MaxHeap (LeanExperiments.HeapSort.siftDownRecursive values 0) := by
  unfold MaxHeap
  have hResultSize :
      (LeanExperiments.HeapSort.siftDownRecursive values 0).size = values.size := by
    change (LeanExperiments.HeapSort.siftDownFuel values.size values 0).size = values.size
    exact siftDownFuel_size values.size values 0
  rw [hResultSize]
  intro parent hParent
  exact siftDownRecursive_heapEdges_from_root values 0
    (by
      intro index hPositive hIndex
      exact hBelow index hPositive hIndex)
    parent (Nat.zero_le parent) hParent

/-- `buildMaxHeapRecursive.go` は、未処理の親添字以上にある辺を整えた状態を不変条件にする。

各段では最大の未処理添字を下降させる。下降後はその添字以降の全辺がヒープ条件を満たすため、帰納法で処理範囲を根へ広げられる。
-/
theorem buildMaxHeapRecursive_go_maxHeap
    (fuel : Nat) (values : Array Nat)
    (hFuel : fuel ≤ values.size / 2)
    (hEdges : ∀ parent, fuel ≤ parent → parent < values.size →
      (2 * parent + 1 < values.size → values[2 * parent + 1]! ≤ values[parent]!) ∧
      (2 * parent + 2 < values.size → values[2 * parent + 2]! ≤ values[parent]!)) :
    MaxHeap (LeanExperiments.HeapSort.buildMaxHeapRecursive.go fuel values) := by
  induction fuel generalizing values with
  | zero =>
      unfold MaxHeap
      intro parent hParent
      exact hEdges parent (Nat.zero_le parent) hParent
  | succ fuel ih =>
      rw [LeanExperiments.HeapSort.buildMaxHeapRecursive.go]
      apply ih
      · have hSize :
            (LeanExperiments.HeapSort.siftDownRecursive values fuel).size = values.size := by
          change (LeanExperiments.HeapSort.siftDownFuel values.size values fuel).size = values.size
          exact siftDownFuel_size values.size values fuel
        rw [hSize]
        omega
      · intro parent hParent hParentIn
        have hParentInput : parent < values.size := by
          have hSize :
              (LeanExperiments.HeapSort.siftDownRecursive values fuel).size = values.size := by
            change (LeanExperiments.HeapSort.siftDownFuel values.size values fuel).size = values.size
            exact siftDownFuel_size values.size values fuel
          rw [← hSize]
          exact hParentIn
        have hBelow : ∀ index, fuel < index → index < values.size →
            (2 * index + 1 < values.size → values[2 * index + 1]! ≤ values[index]!) ∧
            (2 * index + 2 < values.size → values[2 * index + 2]! ≤ values[index]!) := by
          intro index hIndex hIndexIn
          exact hEdges index (by omega) hIndexIn
        have hResult := siftDownRecursive_heapEdges_from_root values fuel hBelow
          parent (by omega) hParentInput
        have hResultSize :
            (LeanExperiments.HeapSort.siftDownFuel values.size values fuel).size =
              values.size := siftDownFuel_size values.size values fuel
        rw [← hResultSize] at hResult
        exact hResult

/-- 再帰版ヒープ構築は任意入力から最大ヒープを作る。 -/
theorem buildMaxHeapRecursive_maxHeap (values : Array Nat) :
    MaxHeap (LeanExperiments.HeapSort.buildMaxHeapRecursive values) := by
  unfold LeanExperiments.HeapSort.buildMaxHeapRecursive
  apply buildMaxHeapRecursive_go_maxHeap (values.size / 2) values
  · omega
  · intro parent hParent hParentIn
    have hNoChildren : values.size ≤ 2 * parent + 1 := by omega
    constructor <;> intro hChild <;> omega

/-- 最大ヒープから再帰版 `popMax` を行うと、残余配列も最大ヒープになる。 -/
theorem popMaxRecursive_rest_maxHeap_of_maxHeap
    {heap : Array Nat} {maximum : Nat} {rest : Array Nat}
    (hHeap : MaxHeap heap)
    (hPop : LeanExperiments.HeapSort.popMaxRecursive heap = some (maximum, rest)) :
    MaxHeap rest := by
  cases hRoot : heap[0]? with
  | none => simp [LeanExperiments.HeapSort.popMaxRecursive, hRoot] at hPop
  | some root =>
      cases hBack : heap.back? with
      | none => simp [LeanExperiments.HeapSort.popMaxRecursive, hRoot, hBack] at hPop
      | some last =>
          by_cases hEmpty : heap.pop = #[]
          · have hRest : rest = #[] := by
              simp [LeanExperiments.HeapSort.popMaxRecursive, hRoot, hBack, hEmpty] at hPop
              exact hPop.2
            simp [hRest, MaxHeap]
          · have hRest :
                rest = LeanExperiments.HeapSort.siftDownRecursive (heap.pop.set! 0 last) 0 := by
              simp [LeanExperiments.HeapSort.popMaxRecursive, hRoot, hBack, hEmpty] at hPop
              exact hPop.2.symm
            have hBelow : ∀ parent, 0 < parent →
                parent < (heap.pop.set! 0 last).size →
                (2 * parent + 1 < (heap.pop.set! 0 last).size →
                  (heap.pop.set! 0 last)[2 * parent + 1]! ≤ (heap.pop.set! 0 last)[parent]!) ∧
                (2 * parent + 2 < (heap.pop.set! 0 last).size →
                  (heap.pop.set! 0 last)[2 * parent + 2]! ≤ (heap.pop.set! 0 last)[parent]!) := by
              intro parent hParent hParentSize
              exact hHeap.pop_set_root_preserves_below_root last parent hParent hParentSize
            rw [hRest]
            exact siftDownRecursive_maxHeap_of_heap_below_root
              (heap.pop.set! 0 last) hBelow

/-- 根以外の親子条件が最大ヒープなら、下降後の根は入力中の各要素以上である。

配列長が0でも成立するよう、最大値の存在ではなく範囲内添字に対する上界として述べる。
-/
theorem siftDownRecursive_root_bounds_all_elements_of_heap_children
    (values : Array Nat)
    (hBelow : ∀ parent, 0 < parent → parent < values.size →
      (2 * parent + 1 < values.size → values[2 * parent + 1]! ≤ values[parent]!) ∧
      (2 * parent + 2 < values.size → values[2 * parent + 2]! ≤ values[parent]!)) :
    ∀ index, index < values.size →
      values[index]! ≤
        (LeanExperiments.HeapSort.siftDownRecursive values 0)[0]! := by
  intro index hIndex
  have hRootAndChildren :=
    siftDownRecursive_root_dominates_initial_root_and_children values 0
  have hSubtreeBound :=
    value_le_root_or_children_max_of_heap_below_root values 0
      (by
        intro parent hParent hParentIndex
        exact hBelow parent (by omega) hParentIndex)
      index (HeapDescendant.zero_ancestor index) hIndex
  have hRootBound : values[0]! ≤
      (LeanExperiments.HeapSort.siftDownRecursive values 0)[0]! := hRootAndChildren.1
  have hLeftBound : values[1]! ≤
      (LeanExperiments.HeapSort.siftDownRecursive values 0)[0]! := by
    by_cases hLeftIndex : 1 < values.size
    · simpa using hRootAndChildren.2.1 hLeftIndex
    · rw [getElem!_neg values 1 hLeftIndex]
      exact Nat.zero_le _
  have hRightBound : values[2]! ≤
      (LeanExperiments.HeapSort.siftDownRecursive values 0)[0]! := by
    by_cases hRightIndex : 2 < values.size
    · simpa using hRootAndChildren.2.2 hRightIndex
    · rw [getElem!_neg values 2 hRightIndex]
      exact Nat.zero_le _
  have hInitialMaximumBound :
      max values[0]! (max values[1]! values[2]!) ≤
        (LeanExperiments.HeapSort.siftDownRecursive values 0)[0]! :=
    (Nat.max_le).2 ⟨hRootBound, (Nat.max_le).2 ⟨hLeftBound, hRightBound⟩⟩
  exact Nat.le_trans hSubtreeBound hInitialMaximumBound

/-- 根の部分木が最大ヒープなら、再帰下降後の根は配列全体の最大値になる。

前提 `hBelow` は根 `0` の子以外にある全ての親子関係が成立することを表す。
下降処理後の根は、初期根と左右の子を支配し、他の要素は根の子以下である。
さらに下降処理が順列を保つため、結果配列中の全要素も結果の根以下となる。
-/
theorem siftDownRecursive_root_is_maximum_of_heap_children (values : Array Nat)
    (hBelow : ∀ parent, 0 < parent → parent < values.size →
      (2 * parent + 1 < values.size → values[2 * parent + 1]! ≤ values[parent]!) ∧
      (2 * parent + 2 < values.size → values[2 * parent + 2]! ≤ values[parent]!))
    (hNonempty : 0 < values.size) :
    (LeanExperiments.HeapSort.siftDownRecursive values 0)[0]! ∈
        (LeanExperiments.HeapSort.siftDownRecursive values 0).toList ∧
      ∀ value,
        value ∈ (LeanExperiments.HeapSort.siftDownRecursive values 0).toList →
          value ≤ (LeanExperiments.HeapSort.siftDownRecursive values 0)[0]! := by
  let output := LeanExperiments.HeapSort.siftDownRecursive values 0
  have hRootBound : ∀ index, index < values.size → values[index]! ≤ output[0]! := by
    simpa [output] using
      siftDownRecursive_root_bounds_all_elements_of_heap_children values hBelow
  have hOutputNonempty : 0 < output.size := by
    rw [siftDownRecursive_size]
    exact hNonempty
  have hPerm : output.toList.Perm values.toList :=
    siftDownRecursive_perm values 0
  refine ⟨by simp [output, hOutputNonempty], ?_⟩
  intro value hValue
  have hInputValue : value ∈ values.toList :=
    (List.Perm.mem_iff hPerm).mp (by simpa [output] using hValue)
  have hArrayMem := Array.mem_toList_iff.mp hInputValue
  obtain ⟨index, hIndex, hIndexValue⟩ := Array.mem_iff_getElem.mp hArrayMem
  have hValueAtIndex : values[index]! = value := by
    rw [getElem!_pos values index hIndex, hIndexValue]
  rw [← hValueAtIndex]
  exact hRootBound index hIndex

/-- 根より大きい子が存在すれば、正の fuel の下降後には根の値が厳密に増える。 -/
theorem siftDownFuel_root_value_gt_of_not_dominatesChildren
    (fuel : Nat) (values : Array Nat) (root : Nat)
    (hFuel : 0 < fuel) (hRoot : root < values.size)
    (hNotDominates :
      ¬ ((2 * root + 1 < values.size → values[2 * root + 1]! ≤ values[root]!) ∧
        (2 * root + 2 < values.size → values[2 * root + 2]! ≤ values[root]!))) :
    values[root]! <
      (LeanExperiments.HeapSort.siftDownFuel fuel values root)[root]! := by
  cases fuel with
  | zero => omega
  | succ fuel =>
      let largest := LeanExperiments.HeapSort.siftDownLargest values root
      have hMoves :
          LeanExperiments.HeapSort.siftDownLargest values root ≠ root := by
        intro hStop
        exact hNotDominates
          ((siftDownLargest_eq_index_iff_dominatesChildren values root).mp hStop)
      have hRootLtLargest : root < largest := by
        have hGe := LeanExperiments.HeapSort.siftDownLargest_ge values root
        omega
      have hLargestBound := siftDownLargest_lt_size values root hRoot
      have hSwapRootBound :
          root < (LeanExperiments.HeapSort.swap values root largest).size := by
        simpa [LeanExperiments.HeapSort.swap] using hRoot
      have hSwapRoot :
          (LeanExperiments.HeapSort.swap values root largest)[root]! = values[largest]! := by
        unfold LeanExperiments.HeapSort.swap
        rw [getElem!_pos _ root hSwapRootBound]
        rw [Array.getElem_swapIfInBounds_left (xs := values)
          hLargestBound hSwapRootBound]
        exact (getElem!_pos values largest hLargestBound).symm
      have hRootPromoted : values[root]! <
          (LeanExperiments.HeapSort.swap values root largest)[root]! := by
        rw [hSwapRoot]
        exact siftDownLargest_value_gt_of_moves values root hMoves
      have hFrame := siftDownFuel_getElem!_eq_of_lt_root fuel
        (LeanExperiments.HeapSort.swap values root largest) largest root
        (by simpa [LeanExperiments.HeapSort.swap] using hRoot)
        hRootLtLargest
      have hNotStopped : (largest == root) = false := by simp [hMoves, largest]
      change values[root]! <
        (if largest == root then values else
          LeanExperiments.HeapSort.siftDownFuel fuel
            (LeanExperiments.HeapSort.swap values root largest) largest)[root]!
      simp [hNotStopped]
      rw [hFrame]
      exact hRootPromoted

/-- 根が存在する子以上なら、任意 fuel の下降処理は配列を変更しない。 -/
theorem siftDownFuel_eq_self_of_dominatesChildren (fuel : Nat) (values : Array Nat)
    (root : Nat)
    (hLeft : 2 * root + 1 < values.size → values[2 * root + 1]! ≤ values[root]!)
    (hRight : 2 * root + 2 < values.size → values[2 * root + 2]! ≤ values[root]!) :
    LeanExperiments.HeapSort.siftDownFuel fuel values root = values :=
  LeanExperiments.HeapSort.siftDownFuel_eq_self_of_dominatesChildren
    fuel values root hLeft hRight

/-- 正の fuel では、下降処理が配列を保つことと根が子以上であることは同値である。 -/
theorem siftDownFuel_eq_self_iff_dominatesChildren_of_pos
    (fuel : Nat) (values : Array Nat) (root : Nat)
    (hFuel : 0 < fuel) (hRoot : root < values.size) :
    LeanExperiments.HeapSort.siftDownFuel fuel values root = values ↔
      (2 * root + 1 < values.size → values[2 * root + 1]! ≤ values[root]!) ∧
      (2 * root + 2 < values.size → values[2 * root + 2]! ≤ values[root]!) := by
  constructor
  · intro hUnchanged
    by_cases hDominates :
        (2 * root + 1 < values.size → values[2 * root + 1]! ≤ values[root]!) ∧
        (2 * root + 2 < values.size → values[2 * root + 2]! ≤ values[root]!)
    · exact hDominates
    · have hRootIncreased := siftDownFuel_root_value_gt_of_not_dominatesChildren
        fuel values root hFuel hRoot hDominates
      have hRootEq :
          (LeanExperiments.HeapSort.siftDownFuel fuel values root)[root]! = values[root]! :=
        congrArg (fun result : Array Nat => result[root]!) hUnchanged
      rw [hRootEq] at hRootIncreased
      omega
  · intro hDominates
    exact LeanExperiments.HeapSort.siftDownFuel_eq_self_of_dominatesChildren
      fuel values root hDominates.1 hDominates.2

/-- 任意fuelで下降結果が入力と等しい条件は、fuelが0か根が子以上であること。

fuelが0なら処理を始めず、正のfuelで根が配列内なら直下の子だけを調べれば固定点か判定できる。
根が配列外の場合は有効な子も存在しないため、結果は常に入力と等しい。
-/
theorem siftDownFuel_eq_self_iff_zero_or_dominatesChildren
    (fuel : Nat) (values : Array Nat) (root : Nat) :
    LeanExperiments.HeapSort.siftDownFuel fuel values root = values ↔
      fuel = 0 ∨
        ((2 * root + 1 < values.size → values[2 * root + 1]! ≤ values[root]!) ∧
          (2 * root + 2 < values.size → values[2 * root + 2]! ≤ values[root]!)) := by
  by_cases hFuel : fuel = 0
  · simp [hFuel, LeanExperiments.HeapSort.siftDownFuel]
  · have hPositive : 0 < fuel := Nat.pos_of_ne_zero hFuel
    by_cases hRoot : root < values.size
    · simpa [hFuel] using
        (siftDownFuel_eq_self_iff_dominatesChildren_of_pos
          fuel values root hPositive hRoot)
    · have hNoLeftChild : values.size ≤ 2 * root + 1 := by omega
      rw [LeanExperiments.HeapSort.siftDownFuel_eq_self_of_noLeftChild
        fuel values root hNoLeftChild]
      constructor
      · intro _
        right
        constructor <;> intro hChild <;> omega
      · intro _
        rfl

/-- 正のfuelで根の値が増えることと、開始時に根が子を支配しないことは同値。

停止判定が固定点であることと、下降先へ進む場合に選択値が根より大きいことを合わせる。
-/
theorem siftDownFuel_root_value_gt_iff_not_dominatesChildren
    (fuel : Nat) (values : Array Nat) (root : Nat)
    (hFuel : 0 < fuel) :
    values[root]! < (LeanExperiments.HeapSort.siftDownFuel fuel values root)[root]! ↔
      ¬ ((2 * root + 1 < values.size → values[2 * root + 1]! ≤ values[root]!) ∧
        (2 * root + 2 < values.size → values[2 * root + 2]! ≤ values[root]!)) := by
  by_cases hRoot : root < values.size
  · constructor
    · intro hIncreases hDominates
      have hUnchanged :=
        (siftDownFuel_eq_self_iff_dominatesChildren_of_pos fuel values root
          hFuel hRoot).2 hDominates
      rw [hUnchanged] at hIncreases
      omega
    · exact siftDownFuel_root_value_gt_of_not_dominatesChildren
        fuel values root hFuel hRoot
  · have hNoLeftChild : values.size ≤ 2 * root + 1 := by omega
    rw [LeanExperiments.HeapSort.siftDownFuel_eq_self_of_noLeftChild
      fuel values root hNoLeftChild]
    constructor <;> intro _ <;> omega

/-- 配列内の根からの再帰下降が入力を保つのは、根が存在する子以上の場合に限る。 -/
theorem siftDownRecursive_eq_self_iff_dominatesChildren
    (values : Array Nat) (root : Nat) :
    LeanExperiments.HeapSort.siftDownRecursive values root = values ↔
      (2 * root + 1 < values.size → values[2 * root + 1]! ≤ values[root]!) ∧
      (2 * root + 2 < values.size → values[2 * root + 2]! ≤ values[root]!) := by
  by_cases hRoot : root < values.size
  · unfold LeanExperiments.HeapSort.siftDownRecursive
    exact siftDownFuel_eq_self_iff_dominatesChildren_of_pos
      values.size values root (by omega) hRoot
  · constructor
    · intro _
      constructor <;> intro hChild <;> omega
    · intro _
      unfold LeanExperiments.HeapSort.siftDownRecursive
      exact LeanExperiments.HeapSort.siftDownFuel_eq_self_of_noLeftChild
        values.size values root (by omega)

/-- 再帰版下降後に根の値が増えることは、開始時に根が子を支配しないことと同値。

範囲内の根では正のfuelに対する一般定理を使う。範囲外の根には子が存在せず、値も
変化しないので、両辺とも偽になる。
-/
theorem siftDownRecursive_root_value_gt_iff_not_dominatesChildren
    (values : Array Nat) (root : Nat) :
    values[root]! < (LeanExperiments.HeapSort.siftDownRecursive values root)[root]! ↔
      ¬ ((2 * root + 1 < values.size → values[2 * root + 1]! ≤ values[root]!) ∧
        (2 * root + 2 < values.size → values[2 * root + 2]! ≤ values[root]!)) := by
  by_cases hRoot : root < values.size
  · unfold LeanExperiments.HeapSort.siftDownRecursive
    exact siftDownFuel_root_value_gt_iff_not_dominatesChildren
      values.size values root (by omega)
  · have hNoLeftChild : values.size ≤ 2 * root + 1 := by omega
    rw [LeanExperiments.HeapSort.siftDownRecursive_eq_self_of_noLeftChild
      values root hNoLeftChild]
    have hDominates :
        (2 * root + 1 < values.size → values[2 * root + 1]! ≤ values[root]!) ∧
        (2 * root + 2 < values.size → values[2 * root + 2]! ≤ values[root]!) := by
      constructor <;> intro hChild <;> omega
    constructor
    · intro hIncrease
      omega
    · intro hNotDominates
      exact (hNotDominates hDominates).elim

/-- 左の子も存在しない位置では、任意 fuel の下降処理が入力を保つ。 -/
theorem siftDownFuel_eq_self_of_noLeftChild (fuel : Nat) (values : Array Nat)
    (root : Nat) (hNoLeftChild : values.size ≤ 2 * root + 1) :
    LeanExperiments.HeapSort.siftDownFuel fuel values root = values :=
  LeanExperiments.HeapSort.siftDownFuel_eq_self_of_noLeftChild
    fuel values root hNoLeftChild

/-- 再帰版下降処理も、開始位置より前の配列要素を保存する。 -/
theorem siftDownRecursive_getElem!_eq_of_lt_root (values : Array Nat)
    (root index : Nat) (hIndex : index < values.size) (hBefore : index < root) :
    (LeanExperiments.HeapSort.siftDownRecursive values root)[index]! = values[index]! := by
  unfold LeanExperiments.HeapSort.siftDownRecursive
  exact siftDownFuel_getElem!_eq_of_lt_root values.size values root index hIndex hBefore

/-- 再帰版 sift-down は開始位置の部分木外にある要素を変更しない。 -/
theorem siftDownRecursive_getElem!_eq_of_not_descendant
    (values : Array Nat) (root index : Nat)
    (hIndex : index < values.size) (hNotDescendant : ¬ HeapDescendant root index) :
    (LeanExperiments.HeapSort.siftDownRecursive values root)[index]! = values[index]! := by
  unfold LeanExperiments.HeapSort.siftDownRecursive
  exact siftDownFuel_getElem!_eq_of_not_descendant
    values.size values root index hIndex hNotDescendant

/-- 下降対象の部分木外にある親子辺の大小条件は sift-down の前後で同値になる。 -/
theorem siftDownRecursive_heapEdge_iff_of_outside_subtree
    (values : Array Nat) (root parent child : Nat)
    (hParent : parent < values.size) (hChild : child < values.size)
    (hParentOutside : ¬ HeapDescendant root parent)
    (hChildOutside : ¬ HeapDescendant root child) :
    (LeanExperiments.HeapSort.siftDownRecursive values root)[child]! ≤
        (LeanExperiments.HeapSort.siftDownRecursive values root)[parent]! ↔
      values[child]! ≤ values[parent]! := by
  rw [siftDownRecursive_getElem!_eq_of_not_descendant
      values root child hChild hChildOutside,
    siftDownRecursive_getElem!_eq_of_not_descendant
      values root parent hParent hParentOutside]

/-- 任意 fuel の下降処理は、開始位置より前のリスト prefix を保つ。 -/
theorem siftDownFuel_toList_take_eq (fuel : Nat) (values : Array Nat) (root : Nat) :
    (LeanExperiments.HeapSort.siftDownFuel fuel values root).toList.take root =
      values.toList.take root := by
  apply List.ext_getElem
  · simp [siftDownFuel_size]
  · intro index hOutput hInput
    have hSize := siftDownFuel_size fuel values root
    have hBefore : index < root := by
      simp only [List.length_take] at hOutput hInput
      omega
    have hIndex : index < values.size := by
      have hOutputLength :
          (LeanExperiments.HeapSort.siftDownFuel fuel values root).toList.length = values.size := by
        simpa only [Array.length_toList] using hSize
      simp only [List.length_take] at hOutput
      rw [hOutputLength] at hOutput
      omega
    have hFrame := siftDownFuel_getElem!_eq_of_lt_root
      fuel values root index hIndex hBefore
    have hOutputIndex : index <
        (LeanExperiments.HeapSort.siftDownFuel fuel values root).size := by
      rw [siftDownFuel_size]
      exact hIndex
    have hFrameBounded :
        (LeanExperiments.HeapSort.siftDownFuel fuel values root)[index] = values[index] := by
      rw [← getElem!_pos (LeanExperiments.HeapSort.siftDownFuel fuel values root)
        index hOutputIndex, ← getElem!_pos values index hIndex]
      exact hFrame
    simpa only [List.getElem_take, Array.getElem_toList] using hFrameBounded

/-- 下降処理が触れる範囲の要素は、開始位置以降の suffix 内で順列として保存される。

開始位置より前の prefix が要素ごとに不変であることと、配列全体の順列保存を合わせる。
したがって、suffix の要素も重複数を含めて保存される。
-/
theorem siftDownFuel_drop_perm (fuel : Nat) (values : Array Nat) (root : Nat) :
    ((LeanExperiments.HeapSort.siftDownFuel fuel values root).toList.drop root).Perm
      (values.toList.drop root) := by
  have hPrefix := siftDownFuel_toList_take_eq fuel values root
  have hPerm := siftDownFuel_perm fuel values root
  have hSplitOutput :
      (LeanExperiments.HeapSort.siftDownFuel fuel values root).toList =
        (LeanExperiments.HeapSort.siftDownFuel fuel values root).toList.take root ++
          (LeanExperiments.HeapSort.siftDownFuel fuel values root).toList.drop root :=
    (List.take_append_drop root
      (LeanExperiments.HeapSort.siftDownFuel fuel values root).toList).symm
  have hSplitInput : values.toList = values.toList.take root ++ values.toList.drop root :=
    (List.take_append_drop root values.toList).symm
  rw [hSplitOutput, hSplitInput, hPrefix] at hPerm
  rw [List.perm_iff_count] at hPerm
  rw [List.perm_iff_count]
  intro value
  have hCount := hPerm value
  simp only [List.count_append] at hCount
  omega

/-- 再帰版下降処理は開始添字以降の要素を順列として保存する。 -/
theorem siftDownRecursive_drop_perm (values : Array Nat) (root : Nat) :
    ((LeanExperiments.HeapSort.siftDownRecursive values root).toList.drop root).Perm
      (values.toList.drop root) := by
  unfold LeanExperiments.HeapSort.siftDownRecursive
  exact siftDownFuel_drop_perm values.size values root

/-- 下降対象 suffix の長さと自然数値の総和は、処理後も保存される。

suffix の順列保存から導くことで、変更範囲だけに対する要素保存の帰結を明示する。
-/
theorem siftDownFuel_drop_length_and_sum (fuel : Nat) (values : Array Nat) (root : Nat) :
    ((LeanExperiments.HeapSort.siftDownFuel fuel values root).toList.drop root).length =
        (values.toList.drop root).length ∧
      ((LeanExperiments.HeapSort.siftDownFuel fuel values root).toList.drop root).sum =
        (values.toList.drop root).sum := by
  have hPerm := siftDownFuel_drop_perm fuel values root
  exact ⟨hPerm.length_eq, hPerm.sum_nat⟩

/-- 下降対象 suffix は、任意の Boolean 条件を満たす要素数も処理後に保つ。

値ごとの出現回数に限らず、しきい値・分類などで定義した部分集合の個数を比較できる。
-/
theorem siftDownFuel_drop_countP (fuel : Nat) (values : Array Nat) (root : Nat)
    (predicate : Nat → Bool) :
    ((LeanExperiments.HeapSort.siftDownFuel fuel values root).toList.drop root).countP
        predicate =
      (values.toList.drop root).countP predicate := by
  exact (siftDownFuel_drop_perm fuel values root).countP_eq predicate

/-- 再帰版下降処理も、suffix 内の任意の Boolean 条件を満たす要素数を保つ。 -/
theorem siftDownRecursive_drop_countP (values : Array Nat) (root : Nat)
    (predicate : Nat → Bool) :
    ((LeanExperiments.HeapSort.siftDownRecursive values root).toList.drop root).countP
        predicate =
      (values.toList.drop root).countP predicate := by
  exact siftDownRecursive_drop_perm values root |>.countP_eq predicate

/-- 再帰版下降処理は、開始位置より前のリスト prefix を保つ。 -/
theorem siftDownRecursive_toList_take_eq (values : Array Nat) (root : Nat) :
    (LeanExperiments.HeapSort.siftDownRecursive values root).toList.take root =
      values.toList.take root := by
  unfold LeanExperiments.HeapSort.siftDownRecursive
  exact siftDownFuel_toList_take_eq values.size values root

/-- 左の子が配列外なら、再帰版下降処理は配列を変更しない。 -/
theorem siftDownRecursive_eq_self_of_noLeftChild (values : Array Nat) (root : Nat)
    (hNoLeftChild : values.size ≤ 2 * root + 1) :
    LeanExperiments.HeapSort.siftDownRecursive values root = values :=
  LeanExperiments.HeapSort.siftDownRecursive_eq_self_of_noLeftChild
    values root hNoLeftChild

/-- 最大ヒープの親子条件を満たす根では、再帰版下降処理は配列を変えない。

`root` が配列外でも、そこから子が存在すれば `root` 自身も配列内にあるため、
`MaxHeap` の親子条件を適用できる。
-/
theorem siftDownRecursive_eq_self_of_maxHeap (heap : Array Nat) (root : Nat)
    (hHeap : MaxHeap heap) :
    LeanExperiments.HeapSort.siftDownRecursive heap root = heap := by
  apply LeanExperiments.HeapSort.siftDownRecursive_eq_self_of_dominatesChildren
  · intro hLeft
    have hRoot : root < heap.size := by omega
    exact hHeap root hRoot |>.1 hLeft
  · intro hRight
    have hRoot : root < heap.size := by omega
    exact hHeap root hRoot |>.2 hRight

/-- 再帰版ヒープ構築は、入力がすでに最大ヒープなら入力をそのまま返す。

構築順で呼ばれる各下降処理の根は、既存の最大ヒープ条件からすでに子以上である。
そのため各段階が配列を変えないことを、fuel に関する帰納法で示す。
-/
theorem buildMaxHeapRecursive_eq_self_of_maxHeap (heap : Array Nat)
    (hHeap : MaxHeap heap) :
    LeanExperiments.HeapSort.buildMaxHeapRecursive heap = heap := by
  unfold LeanExperiments.HeapSort.buildMaxHeapRecursive
  have hGo : ∀ fuel candidate, MaxHeap candidate →
      LeanExperiments.HeapSort.buildMaxHeapRecursive.go fuel candidate = candidate := by
    intro fuel
    induction fuel with
    | zero =>
        intro candidate _
        rfl
    | succ fuel ih =>
        intro candidate hCandidate
        rw [LeanExperiments.HeapSort.buildMaxHeapRecursive.go]
        rw [siftDownRecursive_eq_self_of_maxHeap candidate fuel hCandidate]
        exact ih candidate hCandidate
  exact hGo (heap.size / 2) heap hHeap

/-- 長さ1以下では再帰版ヒープ構築の処理回数が0なので、入力配列を保つ。 -/
theorem buildMaxHeapRecursive_eq_self_of_size_le_one (values : Array Nat)
    (hSize : values.size ≤ 1) :
    LeanExperiments.HeapSort.buildMaxHeapRecursive values = values := by
  unfold LeanExperiments.HeapSort.buildMaxHeapRecursive
  have hFuel : values.size / 2 = 0 := by omega
  rw [hFuel]
  rfl

/-- 再帰版のヒープ構築は、任意の入力要素を順列として保存する。 -/
theorem buildMaxHeapRecursive_perm (values : Array Nat) :
    (LeanExperiments.HeapSort.buildMaxHeapRecursive values).toList.Perm values.toList := by
  unfold LeanExperiments.HeapSort.buildMaxHeapRecursive
  have hFuelPerm (fuel : Nat) : ∀ heap,
      (LeanExperiments.HeapSort.buildMaxHeapRecursive.go fuel heap).toList.Perm heap.toList := by
    induction fuel with
    | zero => intro heap; rfl
    | succ fuel ih =>
        intro heap
        rw [LeanExperiments.HeapSort.buildMaxHeapRecursive.go]
        exact (ih (LeanExperiments.HeapSort.siftDownRecursive heap fuel)).trans
          (siftDownRecursive_perm heap fuel)
  exact hFuelPerm (values.size / 2) values

/-- 再帰版ヒープ構築は任意入力の配列長を保つ。 -/
theorem buildMaxHeapRecursive_size (values : Array Nat) :
    (LeanExperiments.HeapSort.buildMaxHeapRecursive values).size = values.size := by
  have hPerm := buildMaxHeapRecursive_perm values
  have hLength := hPerm.length_eq
  simpa only [Array.length_toList] using hLength

/-- 再帰版ヒープ構築は任意入力の自然数値の総和を保つ。 -/
theorem buildMaxHeapRecursive_sum (values : Array Nat) :
    (LeanExperiments.HeapSort.buildMaxHeapRecursive values).toList.sum =
      values.toList.sum := by
  unfold LeanExperiments.HeapSort.buildMaxHeapRecursive
  have hFuelSum (fuel : Nat) : ∀ heap,
      (LeanExperiments.HeapSort.buildMaxHeapRecursive.go fuel heap).toList.sum =
        heap.toList.sum := by
    induction fuel with
    | zero => intro heap; rfl
    | succ fuel ih =>
        intro heap
        rw [LeanExperiments.HeapSort.buildMaxHeapRecursive.go]
        rw [ih]
        exact siftDownRecursive_sum heap fuel
  exact hFuelSum (values.size / 2) values

/-- 末尾を根へ移す操作は、根を除いた入力列と順列関係になる。 -/
theorem popSetBack_toList_perm_dropRoot (heap : Array Nat)
    (hSize : 1 < heap.size) (maximum last : Nat)
    (hRoot : heap[0]? = some maximum) (hBack : heap.back? = some last) :
    (heap.pop.set! 0 last).toList.Perm (heap.toList.drop 1) := by
  have hPopIndex : 0 < heap.size - 1 := by omega
  have hPopRoot : heap.pop[0]? = some maximum := by
    rw [Array.getElem?_pop]
    simp only [hPopIndex, ↓reduceIte]
    exact hRoot
  have hRootValue : heap[0] = maximum := by
    rw [getElem?_pos heap 0 (by omega)] at hRoot
    injection hRoot
  have hBackValue : heap.back! = last := by
    rw [Array.back!_eq_back?]
    simp [hBack]
  have hPopList : heap.pop.toList = maximum :: heap.pop.toList.drop 1 := by
    have hHead : heap.pop.toList[0]? = some maximum := by
      rw [Array.getElem?_toList]
      exact hPopRoot
    have hHeadLt : 0 < heap.pop.toList.length :=
      (List.getElem?_eq_some_iff.mp hHead).1
    have hDecomp := List.getElem_cons_drop (as := heap.pop.toList) (i := 0) hHeadLt
    simpa [hRootValue, Array.getElem_toList, Array.getElem_pop] using hDecomp.symm
  have hHeapList : heap.toList = heap.pop.toList ++ [last] := by
    rw [Array.eq_push_pop_back!_of_size_ne_zero (by omega : heap.size ≠ 0)]
    simp [hBackValue]
  have hDrop : heap.toList.drop 1 = heap.pop.toList.drop 1 ++ [last] := by
    rw [hHeapList, hPopList]
    simp
  have hSetList : (heap.pop.set! 0 last).toList = last :: heap.pop.toList.drop 1 := by
    rw [Array.toList_set!]
    rw [hPopList]
    simp
  have hTailPerm :
      (last :: heap.pop.toList.drop 1).Perm
        (heap.pop.toList.drop 1 ++ [last]) :=
    (List.perm_append_singleton last (heap.pop.toList.drop 1)).symm
  rw [hSetList, hDrop]
  exact hTailPerm

/-- ループ版 `popMax` は、任意の配列で再帰版 `popMaxRecursive` と一致する。

制御分岐と末尾の根置換は同じであり、非空の残余に対する下降処理の一般一致定理で
実装全体の一致を得る。
-/
theorem popMax_eq_popMaxRecursive (heap : Array Nat) :
    LeanExperiments.HeapSort.popMax heap =
      LeanExperiments.HeapSort.popMaxRecursive heap := by
  simp [LeanExperiments.HeapSort.popMax,
    LeanExperiments.HeapSort.popMaxRecursive,
    siftDown_eq_siftDownRecursive]

/-- `popMax` が成功するとき、返す値は入力ヒープの根に一致する。 -/
theorem popMax_value_eq_root {heap : Array Nat} {maximum : Nat}
    {rest : Array Nat}
    (hPop : LeanExperiments.HeapSort.popMax heap = some (maximum, rest)) :
    heap[0]? = some maximum := by
  unfold LeanExperiments.HeapSort.popMax at hPop
  cases hRoot : heap[0]? with
  | none => simp [hRoot] at hPop
  | some root =>
      cases hLast : heap.back? with
      | none => simp [hRoot, hLast] at hPop
      | some last =>
          simp [hRoot, hLast] at hPop
          by_cases hEmpty : heap.pop = #[]
          · simp [hEmpty] at hPop
            simp [hPop.1]
          · simp [hEmpty] at hPop
            simp [hPop.1]

/-- 再帰版 `popMax` が成功するとき、返す値は入力ヒープの根に一致する。 -/
theorem popMaxRecursive_value_eq_root {heap : Array Nat} {maximum : Nat}
    {rest : Array Nat}
    (hPop : LeanExperiments.HeapSort.popMaxRecursive heap = some (maximum, rest)) :
    heap[0]? = some maximum := by
  unfold LeanExperiments.HeapSort.popMaxRecursive at hPop
  cases hRoot : heap[0]? with
  | none => simp [hRoot] at hPop
  | some root =>
      cases hLast : heap.back? with
      | none => simp [hRoot, hLast] at hPop
      | some last =>
          simp [hRoot, hLast] at hPop
          by_cases hEmpty : heap.pop = #[]
          · simp [hEmpty] at hPop
            simp [hPop.1]
          · simp [hEmpty] at hPop
            simp [hPop.1]

/-- 再帰版 `popMax` が成功すると、残余配列の長さはちょうど1減る。 -/
theorem popMaxRecursive_size {heap : Array Nat} {maximum : Nat}
    {rest : Array Nat}
    (hPop : LeanExperiments.HeapSort.popMaxRecursive heap = some (maximum, rest)) :
    rest.size + 1 = heap.size := by
  cases hRoot : heap[0]? with
  | none => simp [LeanExperiments.HeapSort.popMaxRecursive, hRoot] at hPop
  | some root =>
      cases hBack : heap.back? with
      | none => simp [LeanExperiments.HeapSort.popMaxRecursive, hRoot, hBack] at hPop
      | some last =>
          have hRest : rest =
              (if heap.pop = #[] then heap.pop else
                LeanExperiments.HeapSort.siftDownRecursive (heap.pop.set! 0 last) 0) := by
            simp [LeanExperiments.HeapSort.popMaxRecursive, hRoot, hBack] at hPop
            by_cases hEmpty : heap.pop = #[]
            · simp [hEmpty] at hPop
              simpa [hEmpty] using hPop.2
            · simp [hEmpty] at hPop
              simpa [hEmpty] using hPop.2.symm
          have hConditionalSize :
              (if heap.pop = #[] then heap.pop else
                LeanExperiments.HeapSort.siftDownRecursive (heap.pop.set! 0 last) 0).size =
                  heap.pop.size := by
            by_cases hEmpty : heap.pop = #[]
            · simp [hEmpty]
            · simp [hEmpty, siftDownRecursive_size]
          have hRootIndex : 0 < heap.size :=
            (Array.getElem?_eq_some_iff.mp hRoot).1
          calc
            rest.size + 1 =
                (if heap.pop = #[] then heap.pop else
                  LeanExperiments.HeapSort.siftDownRecursive (heap.pop.set! 0 last) 0).size + 1 := by
                    rw [hRest]
            _ = heap.pop.size + 1 := by rw [hConditionalSize]
            _ = heap.size := by rw [Array.size_pop]; omega

/-- 再帰版 `popMax` の残余配列は、入力から根を除いた要素を順列として保つ。 -/
theorem popMaxRecursive_rest_perm_dropRoot {heap : Array Nat} {maximum : Nat}
    {rest : Array Nat}
    (hPop : LeanExperiments.HeapSort.popMaxRecursive heap = some (maximum, rest)) :
    rest.toList.Perm (heap.toList.drop 1) := by
  cases hRoot : heap[0]? with
  | none => simp [LeanExperiments.HeapSort.popMaxRecursive, hRoot] at hPop
  | some root =>
      cases hBack : heap.back? with
      | none => simp [LeanExperiments.HeapSort.popMaxRecursive, hRoot, hBack] at hPop
      | some last =>
          have hRootMaximum : heap[0]? = some maximum :=
            popMaxRecursive_value_eq_root hPop
          by_cases hEmpty : heap.pop = #[]
          · have hRest : rest = #[] := by
              simp [LeanExperiments.HeapSort.popMaxRecursive, hRoot, hBack, hEmpty] at hPop
              exact hPop.2
            have hSize : heap.size = 1 := by
              have hPopSize : heap.pop.size = 0 := congrArg Array.size hEmpty
              have hSizePop : heap.pop.size = heap.size - 1 := by simp [Array.size_pop]
              rw [hPopSize] at hSizePop
              have hPositive : 0 < heap.size := (Array.getElem?_eq_some_iff.mp hRoot).1
              omega
            have hListSize : heap.toList.length = 1 := by
              simpa only [Array.length_toList] using hSize
            have hTailSize : heap.toList.tail.length = 0 := by
              simp [List.length_tail, hListSize]
            have hTailEmpty : heap.toList.tail = [] :=
              List.eq_nil_of_length_eq_zero hTailSize
            rw [hRest]
            simp [hTailEmpty]
          · have hRest : rest =
                LeanExperiments.HeapSort.siftDownRecursive (heap.pop.set! 0 last) 0 := by
              simp [LeanExperiments.HeapSort.popMaxRecursive, hRoot, hBack, hEmpty] at hPop
              exact hPop.2.symm
            have hPopSize : 0 < heap.pop.size := Array.size_pos_iff.mpr hEmpty
            have hSize : 1 < heap.size := by
              rw [Array.size_pop] at hPopSize
              omega
            rw [hRest]
            exact (siftDownRecursive_perm (heap.pop.set! 0 last) 0).trans
              (popSetBack_toList_perm_dropRoot heap hSize maximum last
                hRootMaximum hBack)

/-- ループ版 `popMax` の残余も、最大ヒープ入力なら最大ヒープである。 -/
theorem popMax_rest_maxHeap_of_maxHeap
    {heap : Array Nat} {maximum : Nat} {rest : Array Nat}
    (hHeap : MaxHeap heap)
    (hPop : LeanExperiments.HeapSort.popMax heap = some (maximum, rest)) :
    MaxHeap rest := by
  rw [popMax_eq_popMaxRecursive] at hPop
  exact popMaxRecursive_rest_maxHeap_of_maxHeap hHeap hPop

/-- ループ版 `popMax` の残余は、入力ヒープから根を除いた要素の順列である。 -/
theorem popMax_rest_perm_dropRoot {heap : Array Nat} {maximum : Nat}
    {rest : Array Nat}
    (hPop : LeanExperiments.HeapSort.popMax heap = some (maximum, rest)) :
    rest.toList.Perm (heap.toList.drop 1) := by
  rw [popMax_eq_popMaxRecursive] at hPop
  exact popMaxRecursive_rest_perm_dropRoot hPop

/-- 最大ヒープから最大値を取り除いた残余配列では、根が残余中の全要素以上である。

これは残余全体が最大ヒープであることまでは示さないが、下降処理が復旧する根の
最大性を、任意長のヒープについて保証する。
-/
theorem popMaxRecursive_rest_root_is_greatest_of_maxHeap
    {heap : Array Nat} {maximum : Nat} {rest : Array Nat}
    (hHeap : MaxHeap heap)
    (hPop : LeanExperiments.HeapSort.popMaxRecursive heap = some (maximum, rest)) :
    ∀ value, value ∈ rest.toList → value ≤ rest[0]! := by
  cases hRoot : heap[0]? with
  | none => simp [LeanExperiments.HeapSort.popMaxRecursive, hRoot] at hPop
  | some root =>
      cases hBack : heap.back? with
      | none => simp [LeanExperiments.HeapSort.popMaxRecursive, hRoot, hBack] at hPop
      | some last =>
          by_cases hEmpty : heap.pop = #[]
          · have hRest : rest = #[] := by
              simp [LeanExperiments.HeapSort.popMaxRecursive, hRoot, hBack, hEmpty] at hPop
              exact hPop.2
            intro value hValue
            rw [hRest] at hValue
            simp at hValue
          · have hRest : rest =
                LeanExperiments.HeapSort.siftDownRecursive (heap.pop.set! 0 last) 0 := by
              simp [LeanExperiments.HeapSort.popMaxRecursive, hRoot, hBack, hEmpty] at hPop
              exact hPop.2.symm
            have hCandidateNonempty : 0 < (heap.pop.set! 0 last).size := by
              have hPopNonempty : 0 < heap.pop.size := Array.size_pos_iff.mpr hEmpty
              simpa using hPopNonempty
            have hBelow :
                ∀ parent, 0 < parent → parent < (heap.pop.set! 0 last).size →
                  (2 * parent + 1 < (heap.pop.set! 0 last).size →
                    (heap.pop.set! 0 last)[2 * parent + 1]! ≤
                      (heap.pop.set! 0 last)[parent]!) ∧
                  (2 * parent + 2 < (heap.pop.set! 0 last).size →
                    (heap.pop.set! 0 last)[2 * parent + 2]! ≤
                      (heap.pop.set! 0 last)[parent]!) := by
              intro parent hParent hParentSize
              exact hHeap.pop_set_root_preserves_below_root last parent hParent hParentSize
            have hSift := siftDownRecursive_root_is_maximum_of_heap_children
              (heap.pop.set! 0 last) hBelow hCandidateNonempty
            rw [hRest]
            exact hSift.2

/-- 最大ヒープの根の値は、そのヒープ中の全ての要素以上である。 -/
theorem root_value_is_maximum {heap : Array Nat} {maximum : Nat}
    (hHeap : MaxHeap heap) (hRootOption : heap[0]? = some maximum) :
    ∀ index, index < heap.size → heap[index]! ≤ maximum := by
  have hSize : 0 < heap.size := by
    by_cases hPositive : 0 < heap.size
    · exact hPositive
    · have hNone : heap[0]? = none := getElem?_neg heap 0 (by omega)
      rw [hNone] at hRootOption
      cases hRootOption
  have hIndex : 0 < heap.size := hSize
  have hRootSome := hRootOption
  rw [getElem?_pos heap 0 hIndex] at hRootSome
  injection hRootSome with hRootValue
  have hRoot : heap[0]! = maximum := by
    rw [getElem!_pos heap 0 hIndex, hRootValue]
  intro index hIndex
  rw [← hRoot]
  exact hHeap.le_root index hIndex

/-- 最大ヒープからループ版 `popMax` が返す値は、その入力の最大値である。 -/
theorem popMax_value_is_maximum {heap : Array Nat} {maximum : Nat}
    {rest : Array Nat} (hHeap : MaxHeap heap)
    (hPop : LeanExperiments.HeapSort.popMax heap = some (maximum, rest)) :
    ∀ index, index < heap.size → heap[index]! ≤ maximum := by
  exact root_value_is_maximum hHeap (popMax_value_eq_root hPop)

/-- 最大ヒープから再帰版 `popMax` が返す値も、その入力の最大値である。 -/
theorem popMaxRecursive_value_is_maximum {heap : Array Nat} {maximum : Nat}
    {rest : Array Nat} (hHeap : MaxHeap heap)
    (hPop : LeanExperiments.HeapSort.popMaxRecursive heap = some (maximum, rest)) :
    ∀ index, index < heap.size → heap[index]! ≤ maximum := by
  exact root_value_is_maximum hHeap (popMaxRecursive_value_eq_root hPop)

/-- 最大ヒープから再帰版 `popMax` が返す値は、入力リストの最大要素である。

添字を使う配列上の上界を、抽象仕様で使いやすいリストの所属・上界へ移す。
-/
theorem popMaxRecursive_returns_greatest_of_maxHeap
    {heap : Array Nat} {maximum : Nat} {rest : Array Nat}
    (hHeap : MaxHeap heap)
    (hPop : LeanExperiments.HeapSort.popMaxRecursive heap = some (maximum, rest)) :
    maximum ∈ heap.toList ∧ ∀ value, value ∈ heap.toList → value ≤ maximum := by
  have hRoot := popMaxRecursive_value_eq_root hPop
  have hPositive : 0 < heap.size := (Array.getElem?_eq_some_iff.mp hRoot).1
  have hRootValue : heap[0]! = maximum := by
    rw [getElem?_pos heap 0 hPositive] at hRoot
    injection hRoot with hValue
    simpa only [getElem!_pos heap 0 hPositive] using hValue
  have hGreatest := hHeap.root_is_greatest hPositive
  constructor
  · simpa [hRootValue] using hGreatest.1
  · intro value hValue
    rw [← hRootValue]
    exact hGreatest.2 value hValue

/-- 最大ヒープから1回抽出すると、返却値は残余配列の全要素以上になる。

返却値が入力の最大値であることと、残余配列が入力から根を除いた順列であることを
組み合わせ、抽出順序の次段に渡せる一般契約を得る。
-/
theorem popMaxRecursive_dominates_rest_of_maxHeap
    {heap : Array Nat} {maximum : Nat} {rest : Array Nat}
    (hHeap : MaxHeap heap)
    (hPop : LeanExperiments.HeapSort.popMaxRecursive heap = some (maximum, rest)) :
    ∀ value, value ∈ rest.toList → value ≤ maximum := by
  have hInputGreatest := popMaxRecursive_returns_greatest_of_maxHeap hHeap hPop
  have hRestPerm := popMaxRecursive_rest_perm_dropRoot hPop
  intro value hValue
  have hInTail : value ∈ heap.toList.drop 1 :=
    (List.Perm.mem_iff hRestPerm).mp hValue
  exact hInputGreatest.2 value (List.mem_of_mem_drop hInTail)

/-- ループ版 `popMax` が `none` を返すことと、入力サイズが0であることは同値。 -/
theorem popMax_eq_none_iff_empty (heap : Array Nat) :
    LeanExperiments.HeapSort.popMax heap = none ↔ heap.size = 0 := by
  cases hRoot : heap[0]? with
  | none =>
      have hSize : heap.size = 0 := by
        have hBound := Array.getElem?_eq_none_iff.mp hRoot
        omega
      simp [LeanExperiments.HeapSort.popMax, hSize]
  | some root =>
      have hPositive : 0 < heap.size :=
        (Array.getElem?_eq_some_iff.mp hRoot).1
      cases hBack : heap.back? with
      | none =>
          have hEmpty := Array.back?_eq_none_iff.mp hBack
          have hSize : heap.size = 0 := by simp [hEmpty]
          omega
      | some last =>
          have hNonempty : heap ≠ #[] := by
            intro hEmpty
            have hSize : heap.size = 0 := by simp [hEmpty]
            omega
          by_cases hPopEmpty : heap.pop = #[]
          · simp [LeanExperiments.HeapSort.popMax, hRoot, hBack, hNonempty,
              hPopEmpty]
          · simp [LeanExperiments.HeapSort.popMax, hRoot, hBack, hNonempty,
              hPopEmpty]

/-- 再帰版 `popMax` も、ちょうどサイズ0のときに `none` を返す。 -/
theorem popMaxRecursive_eq_none_iff_empty (heap : Array Nat) :
    LeanExperiments.HeapSort.popMaxRecursive heap = none ↔ heap.size = 0 := by
  cases hRoot : heap[0]? with
  | none =>
      have hSize : heap.size = 0 := by
        have hBound := Array.getElem?_eq_none_iff.mp hRoot
        omega
      simp [LeanExperiments.HeapSort.popMaxRecursive, hSize]
  | some root =>
      have hPositive : 0 < heap.size :=
        (Array.getElem?_eq_some_iff.mp hRoot).1
      cases hBack : heap.back? with
      | none =>
          have hEmpty := Array.back?_eq_none_iff.mp hBack
          have hSize : heap.size = 0 := by simp [hEmpty]
          omega
      | some last =>
          have hNonempty : heap ≠ #[] := by
            intro hEmpty
            have hSize : heap.size = 0 := by simp [hEmpty]
            omega
          by_cases hPopEmpty : heap.pop = #[]
          · simp [LeanExperiments.HeapSort.popMaxRecursive, hRoot, hBack,
              hNonempty, hPopEmpty]
          · simp [LeanExperiments.HeapSort.popMaxRecursive, hRoot, hBack,
              hNonempty, hPopEmpty]

/-- 全ての親子位置について最大ヒープ条件を計算で検査する。 -/
def maxHeapCheck (heap : Array Nat) : Bool :=
  (List.range heap.size).all fun index =>
    let left := 2 * index + 1
    let right := left + 1
    (left ≥ heap.size || decide (heap[left]! ≤ heap[index]!)) &&
      (right ≥ heap.size || decide (heap[right]! ≤ heap[index]!))

/-- 最大ヒープ検査器の成功条件は、論理的な全親子条件と同値である。 -/
theorem maxHeapCheck_correct (heap : Array Nat) :
    maxHeapCheck heap = true ↔ MaxHeap heap := by
  unfold maxHeapCheck MaxHeap
  constructor
  · intro hCheck index hIndex
    have hAtIndex := (List.all_eq_true.mp hCheck) index
      (List.mem_range.mpr hIndex)
    have hParts :
        (2 * index + 1 ≥ heap.size ||
          decide (heap[2 * index + 1]! ≤ heap[index]!)) = true ∧
        (2 * index + 2 ≥ heap.size ||
          decide (heap[2 * index + 2]! ≤ heap[index]!)) = true := by
      simpa only [Bool.and_eq_true] using hAtIndex
    constructor
    · intro hLeft
      have hLeftOr :
          decide (2 * index + 1 ≥ heap.size) = true ∨
            decide (heap[2 * index + 1]! ≤ heap[index]!) = true := by
        simpa only [Bool.or_eq_true] using hParts.1
      rcases hLeftOr with hOutOfBounds | hOrdered
      · exact False.elim (Nat.not_lt_of_ge (of_decide_eq_true hOutOfBounds) hLeft)
      · exact of_decide_eq_true hOrdered
    · intro hRight
      have hRightOr :
          decide (2 * index + 2 ≥ heap.size) = true ∨
            decide (heap[2 * index + 2]! ≤ heap[index]!) = true := by
        simpa only [Bool.or_eq_true] using hParts.2
      rcases hRightOr with hOutOfBounds | hOrdered
      · exact False.elim (Nat.not_lt_of_ge (of_decide_eq_true hOutOfBounds) hRight)
      · exact of_decide_eq_true hOrdered
  · intro hHeap
    apply List.all_eq_true.mpr
    intro index hIndex
    have hChildren := hHeap index (List.mem_range.mp hIndex)
    rw [Bool.and_eq_true]
    constructor
    · rw [Bool.or_eq_true]
      by_cases hLeft : 2 * index + 1 < heap.size
      · exact Or.inr (decide_eq_true (hChildren.1 hLeft))
      · exact Or.inl (decide_eq_true (Nat.le_of_not_gt hLeft))
    · rw [Bool.or_eq_true]
      by_cases hRight : 2 * index + 2 < heap.size
      · exact Or.inr (decide_eq_true (hChildren.2 hRight))
      · exact Or.inl (decide_eq_true (Nat.le_of_not_gt hRight))

/-- Boolean ヒープ検査器の成功は、全ての根と子孫の順序条件と同値である。

局所的な親子比較を、木の経路全体に沿った祖先・子孫の仕様へ接続する。
-/
theorem maxHeapCheck_iff_ancestor_dominates_descendants (heap : Array Nat) :
    maxHeapCheck heap = true ↔
      ∀ root index, HeapDescendant root index → index < heap.size →
        heap[index]! ≤ heap[root]! := by
  rw [maxHeapCheck_correct, maxHeap_iff_ancestor_dominates_descendants]

end LeanExperiments.Verification.HeapSort.Spec
