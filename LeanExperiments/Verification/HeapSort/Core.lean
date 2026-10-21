import LeanExperiments.HeapSort
import LeanExperiments.Verification.MergeSort.Spec
import LeanExperiments.Verification.Sorting.Spec
import Std.WP
import Std.Tactic.Do

/-!
# ヒープソートの仕様と一般証明

実装本体から独立させた、ヒープソートの仕様と例題を置くモジュール。
アルゴリズムの実装は `LeanExperiments.HeapSort` にあり、このファイルでは
結果が昇順であることと入力要素を保つことを正しさの条件として定義する。

このモジュールには仕様、不変条件、および再帰版・ループ版の任意長・任意値の入力に
対する一般証明を置く。有限入力の具体例と回帰確認は `FiniteChecks` に分離し、
CLI 入出力層は個別の対象として扱う。 -/

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

/-- ヒープ構築後には、最大ヒープ条件と入力要素の重複込み保存を要求する。 -/
def HeapBuildCorrect (input heap : Array Nat) : Prop :=
  MaxHeap heap ∧ heap.toList.Perm input.toList

/-- 再帰版ヒープ構築は任意入力について最大ヒープ条件と要素保存を満たす。 -/
theorem buildMaxHeapRecursive_correct (input : Array Nat) :
    HeapBuildCorrect input (LeanExperiments.HeapSort.buildMaxHeapRecursive input) := by
  exact ⟨buildMaxHeapRecursive_maxHeap input, buildMaxHeapRecursive_perm input⟩

/-- ループ版ヒープ構築は任意入力で最大ヒープ条件と要素保存を満たす。 -/
theorem buildMaxHeap_correct (input : Array Nat) :
    HeapBuildCorrect input (LeanExperiments.HeapSort.buildMaxHeap input) := by
  rw [buildMaxHeap_eq_buildMaxHeapRecursive]
  exact buildMaxHeapRecursive_correct input

/-- 任意の2要素列では、再帰版ヒープ構築後に最大ヒープ条件と要素保存が成り立つ。 -/
theorem buildMaxHeapRecursive_correct_pair (left right : Nat) :
    HeapBuildCorrect #[left, right]
      (LeanExperiments.HeapSort.buildMaxHeapRecursive #[left, right]) := by
  refine ⟨?_, buildMaxHeapRecursive_perm #[left, right]⟩
  unfold LeanExperiments.HeapSort.buildMaxHeapRecursive
  change MaxHeap (LeanExperiments.HeapSort.buildMaxHeapRecursive.go
    (#[left, right].size / 2) #[left, right])
  have hFuel : #[left, right].size / 2 = 1 := by simp
  rw [hFuel]
  rw [LeanExperiments.HeapSort.buildMaxHeapRecursive.go]
  change MaxHeap (LeanExperiments.HeapSort.siftDownRecursive #[left, right] 0)
  rw [LeanExperiments.HeapSort.siftDownRecursive_pair]
  by_cases h : left < right
  · simp only [ite_eq_left h]
    unfold MaxHeap
    intro index hIndex
    have hIndexTwo : index < 2 := by simpa using hIndex
    by_cases hZero : index = 0
    · subst index
      constructor
      · intro _
        simpa using Nat.le_of_lt h
      · intro hRightChild
        simp at hRightChild
    · have hOne : index = 1 := by omega
      subst index
      constructor <;> intro hChild <;> simp at hChild
  · have hRight : right ≤ left := by omega
    simp only [ite_eq_right h]
    unfold MaxHeap
    intro index hIndex
    have hIndexTwo : index < 2 := by simpa using hIndex
    by_cases hZero : index = 0
    · subst index
      constructor
      · intro _
        simpa using hRight
      · intro hRightChild
        simp at hRightChild
    · have hOne : index = 1 := by omega
      subst index
      constructor <;> intro hChild <;> simp at hChild

/-- 根が2つの子以上なら、その3要素配列は最大ヒープである。 -/
private theorem maxHeap_of_three (root left right : Nat)
    (hLeft : left ≤ root) (hRight : right ≤ root) :
    MaxHeap #[root, left, right] := by
  unfold MaxHeap
  intro index hIndex
  have hIndexThree : index < 3 := by simpa using hIndex
  by_cases hZero : index = 0
  · subst index
    constructor
    · intro _
      simpa using hLeft
    · intro _
      simpa using hRight
  · by_cases hOne : index = 1
    · subst index
      constructor <;> intro hChild <;> simp at hChild
    · have hTwo : index = 2 := by omega
      subst index
      constructor <;> intro hChild <;> simp at hChild

/-- 根と各子、および左の子とその子の順序から4要素ヒープを得る。 -/
private theorem maxHeap_of_four (root left right leaf : Nat)
    (hLeft : left ≤ root) (hRight : right ≤ root) (hLeaf : leaf ≤ left) :
    MaxHeap #[root, left, right, leaf] := by
  unfold MaxHeap
  intro index hIndex
  have hIndexFour : index < 4 := by simpa using hIndex
  by_cases hZero : index = 0
  · subst index
    constructor
    · intro _
      simpa using hLeft
    · intro _
      simpa using hRight
  · by_cases hOne : index = 1
    · subst index
      constructor
      · intro _
        simpa using hLeaf
      · intro hChild
        simp at hChild
    · by_cases hTwo : index = 2
      · subst index
        constructor <;> intro hChild <;> simp at hChild
      · have hThree : index = 3 := by omega
        subst index
        constructor <;> intro hChild <;> simp at hChild

/-- 根と左右の子、および左の子とその2つの子の順序から5要素ヒープを得る。 -/
private theorem maxHeap_of_five (root left right leftLeaf rightLeaf : Nat)
    (hLeft : left ≤ root) (hRight : right ≤ root)
    (hLeftLeaf : leftLeaf ≤ left) (hRightLeaf : rightLeaf ≤ left) :
    MaxHeap #[root, left, right, leftLeaf, rightLeaf] := by
  unfold MaxHeap
  intro index hIndex
  have hIndexFive : index < 5 := by simpa using hIndex
  by_cases hZero : index = 0
  · subst index
    constructor
    · intro _
      simpa using hLeft
    · intro _
      simpa using hRight
  · by_cases hOne : index = 1
    · subst index
      constructor
      · intro _
        simpa using hLeftLeaf
      · intro _
        simpa using hRightLeaf
    · by_cases hTwo : index = 2
      · subst index
        constructor <;> intro hChild <;> simp at hChild
      · by_cases hThree : index = 3
        · subst index
          constructor <;> intro hChild <;> simp at hChild
        · have hFour : index = 4 := by omega
          subst index
          constructor <;> intro hChild <;> simp at hChild

/-- 左の子部分木が最大ヒープなら、5要素配列の根からの下降で最大ヒープになる。 -/
private theorem siftDownRecursive_quint_root_maxHeap
    (root left right leftLeaf rightLeaf : Nat)
    (hLeftLeaf : leftLeaf ≤ left) (hRightLeaf : rightLeaf ≤ left) :
    MaxHeap (LeanExperiments.HeapSort.siftDownRecursive
      #[root, left, right, leftLeaf, rightLeaf] 0) := by
  rw [LeanExperiments.HeapSort.siftDownRecursive_quint_root]
  by_cases hRootLeft : root < left
  · by_cases hLeftRight : left < right
    · simp only [ite_eq_left hRootLeft, ite_eq_left hLeftRight]
      apply maxHeap_of_five <;> omega
    · have hRightLeft : right ≤ left := by omega
      by_cases hRootLeftLeaf : root < leftLeaf
      · by_cases hLeftLeafRightLeaf : leftLeaf < rightLeaf
        · simp only [ite_eq_left hRootLeft, ite_eq_right hLeftRight,
            ite_eq_left hRootLeftLeaf, ite_eq_left hLeftLeafRightLeaf]
          apply maxHeap_of_five <;> omega
        · simp only [ite_eq_left hRootLeft, ite_eq_right hLeftRight,
            ite_eq_left hRootLeftLeaf, ite_eq_right hLeftLeafRightLeaf]
          apply maxHeap_of_five <;> omega
      · by_cases hRootRightLeaf : root < rightLeaf
        · simp only [ite_eq_left hRootLeft, ite_eq_right hLeftRight,
            ite_eq_right hRootLeftLeaf, ite_eq_left hRootRightLeaf]
          apply maxHeap_of_five <;> omega
        · simp only [ite_eq_left hRootLeft, ite_eq_right hLeftRight,
            ite_eq_right hRootLeftLeaf, ite_eq_right hRootRightLeaf]
          apply maxHeap_of_five <;> omega
  · by_cases hRootRight : root < right
    · simp only [ite_eq_right hRootLeft, ite_eq_left hRootRight]
      apply maxHeap_of_five <;> omega
    · simp only [ite_eq_right hRootLeft, ite_eq_right hRootRight]
      apply maxHeap_of_five <;> omega

/-- 根と左右の子、その子部分木の条件から6要素ヒープを得る。 -/
private theorem maxHeap_of_six
    (root left right leftLeaf rightLeaf rightChild : Nat)
    (hLeft : left ≤ root) (hRight : right ≤ root)
    (hLeftLeaf : leftLeaf ≤ left) (hRightLeaf : rightLeaf ≤ left)
    (hRightChild : rightChild ≤ right) :
    MaxHeap #[root, left, right, leftLeaf, rightLeaf, rightChild] := by
  unfold MaxHeap
  intro index hIndex
  have hIndexSix : index < 6 := by simpa using hIndex
  by_cases hZero : index = 0
  · subst index
    constructor
    · intro _
      simpa using hLeft
    · intro _
      simpa using hRight
  · by_cases hOne : index = 1
    · subst index
      constructor
      · intro _
        simpa using hLeftLeaf
      · intro _
        simpa using hRightLeaf
    · by_cases hTwo : index = 2
      · subst index
        constructor
        · intro _
          simpa using hRightChild
        · intro hChild
          simp at hChild
      · by_cases hThree : index = 3
        · subst index
          constructor <;> intro hChild <;> simp at hChild
        · by_cases hFour : index = 4
          · subst index
            constructor <;> intro hChild <;> simp at hChild
          · have hFive : index = 5 := by omega
            subst index
            constructor <;> intro hChild <;> simp at hChild

/-- 各親子の大小条件から7要素配列の最大ヒープ条件を得る。 -/
private theorem maxHeap_of_seven
    (root left right leftLeft leftRight rightLeft rightRight : Nat)
    (hLeft : left ≤ root) (hRight : right ≤ root)
    (hLeftLeft : leftLeft ≤ left) (hLeftRight : leftRight ≤ left)
    (hRightLeft : rightLeft ≤ right) (hRightRight : rightRight ≤ right) :
    MaxHeap #[root, left, right, leftLeft, leftRight, rightLeft, rightRight] := by
  unfold MaxHeap
  intro index hIndex
  have hIndexSeven : index < 7 := by simpa using hIndex
  by_cases hZero : index = 0
  · subst index
    constructor
    · intro _
      simpa using hLeft
    · intro _
      simpa using hRight
  · by_cases hOne : index = 1
    · subst index
      constructor
      · intro _
        simpa using hLeftLeft
      · intro _
        simpa using hLeftRight
    · by_cases hTwo : index = 2
      · subst index
        constructor
        · intro _
          simpa using hRightLeft
        · intro _
          simpa using hRightRight
      · by_cases hThree : index = 3
        · subst index
          constructor <;> intro hChild <;> simp at hChild
        · by_cases hFour : index = 4
          · subst index
            constructor <;> intro hChild <;> simp at hChild
          · by_cases hFive : index = 5
            · subst index
              constructor <;> intro hChild <;> simp at hChild
            · have hSix : index = 6 := by omega
              subst index
              constructor <;> intro hChild <;> simp at hChild

/-- 各親子の大小条件から8要素配列の最大ヒープ条件を得る。 -/
private theorem maxHeap_of_eight
    (root left right leftLeft leftRight rightLeft rightRight leftLeftLeft : Nat)
    (hLeft : left ≤ root) (hRight : right ≤ root)
    (hLeftLeft : leftLeft ≤ left) (hLeftRight : leftRight ≤ left)
    (hRightLeft : rightLeft ≤ right) (hRightRight : rightRight ≤ right)
    (hLeftLeftLeft : leftLeftLeft ≤ leftLeft) :
    MaxHeap #[root, left, right, leftLeft, leftRight, rightLeft, rightRight,
      leftLeftLeft] := by
  unfold MaxHeap
  intro index hIndex
  have hIndexEight : index < 8 := by simpa using hIndex
  by_cases hZero : index = 0
  · subst index
    constructor
    · intro _
      simpa using hLeft
    · intro _
      simpa using hRight
  · by_cases hOne : index = 1
    · subst index
      constructor
      · intro _
        simpa using hLeftLeft
      · intro _
        simpa using hLeftRight
    · by_cases hTwo : index = 2
      · subst index
        constructor
        · intro _
          simpa using hRightLeft
        · intro _
          simpa using hRightRight
      · by_cases hThree : index = 3
        · subst index
          constructor
          · intro _
            simpa using hLeftLeftLeft
          · intro hChild
            simp at hChild
        · by_cases hFour : index = 4
          · subst index
            constructor <;> intro hChild <;> simp at hChild
          · by_cases hFive : index = 5
            · subst index
              constructor <;> intro hChild <;> simp at hChild
            · by_cases hSix : index = 6
              · subst index
                constructor <;> intro hChild <;> simp at hChild
              · have hSeven : index = 7 := by omega
                subst index
                constructor <;> intro hChild <;> simp at hChild

/-- 左右の子部分木が最大ヒープなら、6要素配列の根下降後も最大ヒープになる。 -/
private theorem siftDownRecursive_sext_root_maxHeap
    (root left right leftLeaf rightLeaf rightChild : Nat)
    (hLeftLeaf : leftLeaf ≤ left) (hRightLeaf : rightLeaf ≤ left)
    (hRightChild : rightChild ≤ right) :
    MaxHeap (LeanExperiments.HeapSort.siftDownRecursive
      #[root, left, right, leftLeaf, rightLeaf, rightChild] 0) := by
  rw [LeanExperiments.HeapSort.siftDownRecursive_sext_root]
  by_cases hRootLeft : root < left
  · by_cases hLeftRight : left < right
    · by_cases hRootRightChild : root < rightChild
      · simp only [ite_eq_left hRootLeft, ite_eq_left hLeftRight,
          ite_eq_left hRootRightChild]
        apply maxHeap_of_six <;> omega
      · simp only [ite_eq_left hRootLeft, ite_eq_left hLeftRight,
          ite_eq_right hRootRightChild]
        apply maxHeap_of_six <;> omega
    · have hRightLeft : right ≤ left := by omega
      by_cases hRootLeftLeaf : root < leftLeaf
      · by_cases hLeftLeafRightLeaf : leftLeaf < rightLeaf
        · simp only [ite_eq_left hRootLeft, ite_eq_right hLeftRight,
            ite_eq_left hRootLeftLeaf, ite_eq_left hLeftLeafRightLeaf]
          apply maxHeap_of_six <;> omega
        · simp only [ite_eq_left hRootLeft, ite_eq_right hLeftRight,
            ite_eq_left hRootLeftLeaf, ite_eq_right hLeftLeafRightLeaf]
          apply maxHeap_of_six <;> omega
      · by_cases hRootRightLeaf : root < rightLeaf
        · simp only [ite_eq_left hRootLeft, ite_eq_right hLeftRight,
            ite_eq_right hRootLeftLeaf, ite_eq_left hRootRightLeaf]
          apply maxHeap_of_six <;> omega
        · simp only [ite_eq_left hRootLeft, ite_eq_right hLeftRight,
            ite_eq_right hRootLeftLeaf, ite_eq_right hRootRightLeaf]
          apply maxHeap_of_six <;> omega
  · by_cases hRootRight : root < right
    · by_cases hRootRightChild : root < rightChild
      · simp only [ite_eq_right hRootLeft, ite_eq_left hRootRight,
          ite_eq_left hRootRightChild]
        apply maxHeap_of_six <;> omega
      · simp only [ite_eq_right hRootLeft, ite_eq_left hRootRight,
          ite_eq_right hRootRightChild]
        apply maxHeap_of_six <;> omega
    · simp only [ite_eq_right hRootLeft, ite_eq_right hRootRight]
      apply maxHeap_of_six <;> omega

/-- 子部分木がヒープなら、7要素配列の根下降後も全ての親子条件を満たす。 -/
private theorem siftDownRecursive_sept_root_maxHeap
    (root left right leftLeft leftRight rightLeft rightRight : Nat)
    (hLeftLeft : leftLeft ≤ left) (hLeftRight : leftRight ≤ left)
    (hRightLeft : rightLeft ≤ right) (hRightRight : rightRight ≤ right) :
    MaxHeap (LeanExperiments.HeapSort.siftDownRecursive
      #[root, left, right, leftLeft, leftRight, rightLeft, rightRight] 0) := by
  rw [LeanExperiments.HeapSort.siftDownRecursive_sept_root]
  by_cases hRootLeft : root < left
  · by_cases hLeftRight : left < right
    · by_cases hRootRightLeft : root < rightLeft
      · by_cases hRightLeftRight : rightLeft < rightRight
        · simp only [ite_eq_left hRootLeft, ite_eq_left hLeftRight,
            ite_eq_left hRootRightLeft, ite_eq_left hRightLeftRight]
          apply maxHeap_of_seven <;> omega
        · simp only [ite_eq_left hRootLeft, ite_eq_left hLeftRight,
            ite_eq_left hRootRightLeft, ite_eq_right hRightLeftRight]
          apply maxHeap_of_seven <;> omega
      · by_cases hRootRightRight : root < rightRight
        · simp only [ite_eq_left hRootLeft, ite_eq_left hLeftRight,
            ite_eq_right hRootRightLeft, ite_eq_left hRootRightRight]
          apply maxHeap_of_seven <;> omega
        · simp only [ite_eq_left hRootLeft, ite_eq_left hLeftRight,
            ite_eq_right hRootRightLeft, ite_eq_right hRootRightRight]
          apply maxHeap_of_seven <;> omega
    · have hRightLeftRoot : right ≤ left := by omega
      by_cases hRootLeftLeft : root < leftLeft
      · by_cases hLeftLeftRight : leftLeft < leftRight
        · simp only [ite_eq_left hRootLeft, ite_eq_right hLeftRight,
            ite_eq_left hRootLeftLeft, ite_eq_left hLeftLeftRight]
          apply maxHeap_of_seven <;> omega
        · simp only [ite_eq_left hRootLeft, ite_eq_right hLeftRight,
            ite_eq_left hRootLeftLeft, ite_eq_right hLeftLeftRight]
          apply maxHeap_of_seven <;> omega
      · by_cases hRootLeftRight : root < leftRight
        · simp only [ite_eq_left hRootLeft, ite_eq_right hLeftRight,
            ite_eq_right hRootLeftLeft, ite_eq_left hRootLeftRight]
          apply maxHeap_of_seven <;> omega
        · simp only [ite_eq_left hRootLeft, ite_eq_right hLeftRight,
            ite_eq_right hRootLeftLeft, ite_eq_right hRootLeftRight]
          apply maxHeap_of_seven <;> omega
  · by_cases hRootRight : root < right
    · by_cases hRootRightLeft : root < rightLeft
      · by_cases hRightLeftRight : rightLeft < rightRight
        · simp only [ite_eq_right hRootLeft, ite_eq_left hRootRight,
            ite_eq_left hRootRightLeft, ite_eq_left hRightLeftRight]
          apply maxHeap_of_seven <;> omega
        · simp only [ite_eq_right hRootLeft, ite_eq_left hRootRight,
            ite_eq_left hRootRightLeft, ite_eq_right hRightLeftRight]
          apply maxHeap_of_seven <;> omega
      · by_cases hRootRightRight : root < rightRight
        · simp only [ite_eq_right hRootLeft, ite_eq_left hRootRight,
            ite_eq_right hRootRightLeft, ite_eq_left hRootRightRight]
          apply maxHeap_of_seven <;> omega
        · simp only [ite_eq_right hRootLeft, ite_eq_left hRootRight,
            ite_eq_right hRootRightLeft, ite_eq_right hRootRightRight]
          apply maxHeap_of_seven <;> omega
    · simp only [ite_eq_right hRootLeft, ite_eq_right hRootRight]
      apply maxHeap_of_seven <;> omega

/-- 子部分木がヒープなら、8要素配列の根下降後も全ての親子条件を満たす。 -/
private theorem siftDownRecursive_oct_root_maxHeap
    (root left right leftLeft leftRight rightLeft rightRight leftLeftLeft : Nat)
    (hLeftLeft : leftLeft ≤ left) (hLeftRight : leftRight ≤ left)
    (hRightLeft : rightLeft ≤ right) (hRightRight : rightRight ≤ right)
    (hLeftLeftLeft : leftLeftLeft ≤ leftLeft) :
    MaxHeap (LeanExperiments.HeapSort.siftDownRecursive
      #[root, left, right, leftLeft, leftRight, rightLeft, rightRight,
        leftLeftLeft] 0) := by
  rw [LeanExperiments.HeapSort.siftDownRecursive_oct_root]
  by_cases hRootLeft : root < left
  · by_cases hLeftRight : left < right
    · by_cases hRootRightLeft : root < rightLeft
      · by_cases hRightLeftRight : rightLeft < rightRight
        · simp only [ite_eq_left hRootLeft, ite_eq_left hLeftRight,
            ite_eq_left hRootRightLeft, ite_eq_left hRightLeftRight]
          apply maxHeap_of_eight <;> omega
        · simp only [ite_eq_left hRootLeft, ite_eq_left hLeftRight,
            ite_eq_left hRootRightLeft, ite_eq_right hRightLeftRight]
          apply maxHeap_of_eight <;> omega
      · by_cases hRootRightRight : root < rightRight
        · simp only [ite_eq_left hRootLeft, ite_eq_left hLeftRight,
            ite_eq_right hRootRightLeft, ite_eq_left hRootRightRight]
          apply maxHeap_of_eight <;> omega
        · simp only [ite_eq_left hRootLeft, ite_eq_left hLeftRight,
            ite_eq_right hRootRightLeft, ite_eq_right hRootRightRight]
          apply maxHeap_of_eight <;> omega
    · have hRightLeftRoot : right ≤ left := by omega
      by_cases hRootLeftLeft : root < leftLeft
      · by_cases hLeftLeftRight : leftLeft < leftRight
        · simp only [ite_eq_left hRootLeft, ite_eq_right hLeftRight,
            ite_eq_left hRootLeftLeft, ite_eq_left hLeftLeftRight]
          apply maxHeap_of_eight <;> omega
        · have hLeftRightLeft : leftRight ≤ leftLeft := by omega
          by_cases hRootLeftLeftLeft : root < leftLeftLeft
          · simp only [ite_eq_left hRootLeft, ite_eq_right hLeftRight,
              ite_eq_left hRootLeftLeft, ite_eq_right hLeftLeftRight,
              ite_eq_left hRootLeftLeftLeft]
            apply maxHeap_of_eight <;> omega
          · simp only [ite_eq_left hRootLeft, ite_eq_right hLeftRight,
              ite_eq_left hRootLeftLeft, ite_eq_right hLeftLeftRight,
              ite_eq_right hRootLeftLeftLeft]
            apply maxHeap_of_eight <;> omega
      · by_cases hRootLeftRight : root < leftRight
        · simp only [ite_eq_left hRootLeft, ite_eq_right hLeftRight,
            ite_eq_right hRootLeftLeft, ite_eq_left hRootLeftRight]
          apply maxHeap_of_eight <;> omega
        · simp only [ite_eq_left hRootLeft, ite_eq_right hLeftRight,
            ite_eq_right hRootLeftLeft, ite_eq_right hRootLeftRight]
          apply maxHeap_of_eight <;> omega
  · by_cases hRootRight : root < right
    · by_cases hRootRightLeft : root < rightLeft
      · by_cases hRightLeftRight : rightLeft < rightRight
        · simp only [ite_eq_right hRootLeft, ite_eq_left hRootRight,
            ite_eq_left hRootRightLeft, ite_eq_left hRightLeftRight]
          apply maxHeap_of_eight <;> omega
        · simp only [ite_eq_right hRootLeft, ite_eq_left hRootRight,
            ite_eq_left hRootRightLeft, ite_eq_right hRightLeftRight]
          apply maxHeap_of_eight <;> omega
      · by_cases hRootRightRight : root < rightRight
        · simp only [ite_eq_right hRootLeft, ite_eq_left hRootRight,
            ite_eq_right hRootRightLeft, ite_eq_left hRootRightRight]
          apply maxHeap_of_eight <;> omega
        · simp only [ite_eq_right hRootLeft, ite_eq_left hRootRight,
            ite_eq_right hRootRightLeft, ite_eq_right hRootRightRight]
          apply maxHeap_of_eight <;> omega
    · simp only [ite_eq_right hRootLeft, ite_eq_right hRootRight]
      apply maxHeap_of_eight <;> omega

/-- 左部分木が最大ヒープなら、再帰下降は4要素配列を最大ヒープにする。 -/
private theorem siftDownRecursive_quad_root_maxHeap (root left right leaf : Nat)
    (hSubheap : leaf ≤ left) :
    MaxHeap (LeanExperiments.HeapSort.siftDownRecursive #[root, left, right, leaf] 0) := by
  rw [LeanExperiments.HeapSort.siftDownRecursive_quad_root]
  by_cases hRootLeft : root < left
  · by_cases hLeftRight : left < right
    · simp only [ite_eq_left hRootLeft, ite_eq_left hLeftRight]
      apply maxHeap_of_four
      · omega
      · omega
      · exact hSubheap
    · have hRightLeft : right ≤ left := by omega
      by_cases hRootLeaf : root < leaf
      · simp only [ite_eq_left hRootLeft, ite_eq_right hLeftRight,
          ite_eq_left hRootLeaf]
        apply maxHeap_of_four
        · omega
        · exact hRightLeft
        · omega
      · have hLeafRoot : leaf ≤ root := by omega
        simp only [ite_eq_left hRootLeft, ite_eq_right hLeftRight,
          ite_eq_right hRootLeaf]
        apply maxHeap_of_four
        · omega
        · exact hRightLeft
        · exact hLeafRoot
  · by_cases hRootRight : root < right
    · simp only [ite_eq_right hRootLeft, ite_eq_left hRootRight]
      apply maxHeap_of_four
      · omega
      · omega
      · exact hSubheap
    · have hLeftRoot : left ≤ root := by omega
      have hRightRoot : right ≤ root := by omega
      simp only [ite_eq_right hRootLeft, ite_eq_right hRootRight]
      exact maxHeap_of_four root left right leaf hLeftRoot hRightRoot hSubheap

/-- 任意の3要素列では、再帰版ヒープ構築後に最大ヒープ条件を満たす。 -/
theorem buildMaxHeapRecursive_correct_triple (root left right : Nat) :
    HeapBuildCorrect #[root, left, right]
      (LeanExperiments.HeapSort.buildMaxHeapRecursive #[root, left, right]) := by
  refine ⟨?_, buildMaxHeapRecursive_perm #[root, left, right]⟩
  unfold LeanExperiments.HeapSort.buildMaxHeapRecursive
  change MaxHeap (LeanExperiments.HeapSort.buildMaxHeapRecursive.go
    (#[root, left, right].size / 2) #[root, left, right])
  have hFuel : #[root, left, right].size / 2 = 1 := by simp
  rw [hFuel]
  rw [LeanExperiments.HeapSort.buildMaxHeapRecursive.go]
  change MaxHeap (LeanExperiments.HeapSort.siftDownRecursive #[root, left, right] 0)
  rw [LeanExperiments.HeapSort.siftDownRecursive_triple]
  by_cases hRootLeft : root < left
  · by_cases hLeftRight : left < right
    · simp only [ite_eq_left hRootLeft, ite_eq_left hLeftRight]
      apply maxHeap_of_three
      · omega
      · omega
    · have hRightLeft : right ≤ left := by omega
      simp only [ite_eq_left hRootLeft, ite_eq_right hLeftRight]
      apply maxHeap_of_three
      · omega
      · exact hRightLeft
  · by_cases hRootRight : root < right
    · have hLeftRoot : left ≤ root := by omega
      simp only [ite_eq_right hRootLeft, ite_eq_left hRootRight]
      apply maxHeap_of_three
      · omega
      · omega
    · have hLeftRoot : left ≤ root := by omega
      have hRightRoot : right ≤ root := by omega
      simp only [ite_eq_right hRootLeft, ite_eq_right hRootRight]
      exact maxHeap_of_three root left right hLeftRoot hRightRoot

/-- 任意の4要素列では、再帰版ヒープ構築後に最大ヒープ条件を満たす。 -/
theorem buildMaxHeapRecursive_correct_quad (root left right leaf : Nat) :
    HeapBuildCorrect #[root, left, right, leaf]
      (LeanExperiments.HeapSort.buildMaxHeapRecursive #[root, left, right, leaf]) := by
  refine ⟨?_, buildMaxHeapRecursive_perm #[root, left, right, leaf]⟩
  unfold LeanExperiments.HeapSort.buildMaxHeapRecursive
  change MaxHeap (LeanExperiments.HeapSort.buildMaxHeapRecursive.go
    (#[root, left, right, leaf].size / 2) #[root, left, right, leaf])
  have hFuel : #[root, left, right, leaf].size / 2 = 2 := by simp
  rw [hFuel]
  rw [LeanExperiments.HeapSort.buildMaxHeapRecursive.go]
  rw [LeanExperiments.HeapSort.siftDownRecursive_quad_leftChild]
  by_cases hLeftLeaf : left < leaf
  · simp only [ite_eq_left hLeftLeaf]
    rw [LeanExperiments.HeapSort.buildMaxHeapRecursive.go]
    change MaxHeap (LeanExperiments.HeapSort.siftDownRecursive #[root, leaf, right, left] 0)
    exact siftDownRecursive_quad_root_maxHeap root leaf right left (Nat.le_of_lt hLeftLeaf)
  · have hLeafLeft : leaf ≤ left := by omega
    simp only [ite_eq_right hLeftLeaf]
    rw [LeanExperiments.HeapSort.buildMaxHeapRecursive.go]
    change MaxHeap (LeanExperiments.HeapSort.siftDownRecursive #[root, left, right, leaf] 0)
    exact siftDownRecursive_quad_root_maxHeap root left right leaf hLeafLeft

/-- 任意の5要素列では、再帰版ヒープ構築後に最大ヒープ条件を満たす。 -/
theorem buildMaxHeapRecursive_correct_quint
    (root left right leftLeaf rightLeaf : Nat) :
    HeapBuildCorrect #[root, left, right, leftLeaf, rightLeaf]
      (LeanExperiments.HeapSort.buildMaxHeapRecursive
        #[root, left, right, leftLeaf, rightLeaf]) := by
  refine ⟨?_, buildMaxHeapRecursive_perm #[root, left, right, leftLeaf, rightLeaf]⟩
  unfold LeanExperiments.HeapSort.buildMaxHeapRecursive
  change MaxHeap (LeanExperiments.HeapSort.buildMaxHeapRecursive.go
    (#[root, left, right, leftLeaf, rightLeaf].size / 2)
    #[root, left, right, leftLeaf, rightLeaf])
  have hFuel : #[root, left, right, leftLeaf, rightLeaf].size / 2 = 2 := by simp
  rw [hFuel]
  rw [LeanExperiments.HeapSort.buildMaxHeapRecursive.go]
  rw [LeanExperiments.HeapSort.buildMaxHeapRecursive.go]
  change MaxHeap (LeanExperiments.HeapSort.siftDownRecursive
    (LeanExperiments.HeapSort.siftDownRecursive
      #[root, left, right, leftLeaf, rightLeaf] 1) 0)
  rw [LeanExperiments.HeapSort.siftDownRecursive_quint_left]
  by_cases hLeftLeaf : left < leftLeaf
  · by_cases hLeafRight : leftLeaf < rightLeaf
    · simp only [ite_eq_left hLeftLeaf, ite_eq_left hLeafRight]
      exact siftDownRecursive_quint_root_maxHeap root rightLeaf right leftLeaf left
        (Nat.le_of_lt hLeafRight) (by omega)
    · simp only [ite_eq_left hLeftLeaf, ite_eq_right hLeafRight]
      exact siftDownRecursive_quint_root_maxHeap root leftLeaf right left rightLeaf
        (by omega) (by omega)
  · by_cases hRightLeaf : left < rightLeaf
    · simp only [ite_eq_right hLeftLeaf, ite_eq_left hRightLeaf]
      exact siftDownRecursive_quint_root_maxHeap root rightLeaf right leftLeaf left
        (by omega) (by omega)
    · simp only [ite_eq_right hLeftLeaf, ite_eq_right hRightLeaf]
      exact siftDownRecursive_quint_root_maxHeap root left right leftLeaf rightLeaf
        (by omega) (by omega)

/-- 任意の6要素列では、再帰版ヒープ構築後に最大ヒープ条件を満たす。 -/
theorem buildMaxHeapRecursive_correct_sext
    (root left right leftLeaf rightLeaf rightChild : Nat) :
    HeapBuildCorrect #[root, left, right, leftLeaf, rightLeaf, rightChild]
      (LeanExperiments.HeapSort.buildMaxHeapRecursive
        #[root, left, right, leftLeaf, rightLeaf, rightChild]) := by
  refine ⟨?_, buildMaxHeapRecursive_perm
    #[root, left, right, leftLeaf, rightLeaf, rightChild]⟩
  unfold LeanExperiments.HeapSort.buildMaxHeapRecursive
  change MaxHeap (LeanExperiments.HeapSort.buildMaxHeapRecursive.go
    (#[root, left, right, leftLeaf, rightLeaf, rightChild].size / 2)
    #[root, left, right, leftLeaf, rightLeaf, rightChild])
  have hFuel : #[root, left, right, leftLeaf, rightLeaf, rightChild].size / 2 = 3 := by simp
  rw [hFuel]
  rw [LeanExperiments.HeapSort.buildMaxHeapRecursive.go]
  rw [LeanExperiments.HeapSort.buildMaxHeapRecursive.go]
  rw [LeanExperiments.HeapSort.buildMaxHeapRecursive.go]
  change MaxHeap (LeanExperiments.HeapSort.siftDownRecursive
    (LeanExperiments.HeapSort.siftDownRecursive
      (LeanExperiments.HeapSort.siftDownRecursive
        #[root, left, right, leftLeaf, rightLeaf, rightChild] 2) 1) 0)
  rw [LeanExperiments.HeapSort.siftDownRecursive_sext_right]
  by_cases hRightChild : right < rightChild
  · simp only [ite_eq_left hRightChild]
    rw [LeanExperiments.HeapSort.siftDownRecursive_sext_left]
    by_cases hLeftLeaf : left < leftLeaf
    · by_cases hLeafRight : leftLeaf < rightLeaf
      · simp only [ite_eq_left hLeftLeaf, ite_eq_left hLeafRight]
        exact siftDownRecursive_sext_root_maxHeap root rightLeaf rightChild leftLeaf left right
          (Nat.le_of_lt hLeafRight) (by omega) (Nat.le_of_lt hRightChild)
      · simp only [ite_eq_left hLeftLeaf, ite_eq_right hLeafRight]
        exact siftDownRecursive_sext_root_maxHeap root leftLeaf rightChild left rightLeaf right
          (by omega) (by omega) (Nat.le_of_lt hRightChild)
    · by_cases hRightLeaf : left < rightLeaf
      · simp only [ite_eq_right hLeftLeaf, ite_eq_left hRightLeaf]
        exact siftDownRecursive_sext_root_maxHeap root rightLeaf rightChild leftLeaf left right
          (by omega) (by omega) (Nat.le_of_lt hRightChild)
      · simp only [ite_eq_right hLeftLeaf, ite_eq_right hRightLeaf]
        exact siftDownRecursive_sext_root_maxHeap root left rightChild leftLeaf rightLeaf right
          (by omega) (by omega) (Nat.le_of_lt hRightChild)
  · have hChildRight : rightChild ≤ right := by omega
    simp only [ite_eq_right hRightChild]
    rw [LeanExperiments.HeapSort.siftDownRecursive_sext_left]
    by_cases hLeftLeaf : left < leftLeaf
    · by_cases hLeafRight : leftLeaf < rightLeaf
      · simp only [ite_eq_left hLeftLeaf, ite_eq_left hLeafRight]
        exact siftDownRecursive_sext_root_maxHeap root rightLeaf right leftLeaf left rightChild
          (Nat.le_of_lt hLeafRight) (by omega) hChildRight
      · simp only [ite_eq_left hLeftLeaf, ite_eq_right hLeafRight]
        exact siftDownRecursive_sext_root_maxHeap root leftLeaf right left rightLeaf rightChild
          (by omega) (by omega) hChildRight
    · by_cases hRightLeaf : left < rightLeaf
      · simp only [ite_eq_right hLeftLeaf, ite_eq_left hRightLeaf]
        exact siftDownRecursive_sext_root_maxHeap root rightLeaf right leftLeaf left rightChild
          (by omega) (by omega) hChildRight
      · simp only [ite_eq_right hLeftLeaf, ite_eq_right hRightLeaf]
        exact siftDownRecursive_sext_root_maxHeap root left right leftLeaf rightLeaf rightChild
          (by omega) (by omega) hChildRight

/-- 7要素配列で添字2を下降させると、その節点と2つの葉が最大ヒープになる。 -/
private theorem siftDownRecursive_sept_right_child_bounds
    (root left parent leftLeaf rightLeaf leftChild rightChild : Nat) :
    let result := LeanExperiments.HeapSort.siftDownRecursive
      #[root, left, parent, leftLeaf, rightLeaf, leftChild, rightChild] 2
    result[5]! ≤ result[2]! ∧ result[6]! ≤ result[2]! := by
  rw [LeanExperiments.HeapSort.siftDownRecursive_sept_right]
  by_cases hParentLeft : parent < leftChild
  · by_cases hLeftRight : leftChild < rightChild
    · simp only [ite_eq_left hParentLeft, ite_eq_left hLeftRight]
      simp <;> omega
    · simp only [ite_eq_left hParentLeft, ite_eq_right hLeftRight]
      simp <;> omega
  · by_cases hParentRight : parent < rightChild
    · simp only [ite_eq_right hParentLeft, ite_eq_left hParentRight]
      simp <;> omega
    · simp only [ite_eq_right hParentLeft, ite_eq_right hParentRight]
      simp <;> omega

/-- 7要素配列で添字1を下降させると、その節点と2つの葉が最大ヒープになる。 -/
private theorem siftDownRecursive_sept_left_child_bounds
    (root parent sibling leftLeaf rightLeaf tailLeft tailRight : Nat) :
    let result := LeanExperiments.HeapSort.siftDownRecursive
      #[root, parent, sibling, leftLeaf, rightLeaf, tailLeft, tailRight] 1
    result[3]! ≤ result[1]! ∧ result[4]! ≤ result[1]! := by
  rw [LeanExperiments.HeapSort.siftDownRecursive_sept_left]
  by_cases hParentLeftLeaf : parent < leftLeaf
  · by_cases hLeftLeafRightLeaf : leftLeaf < rightLeaf
    · simp only [ite_eq_left hParentLeftLeaf, ite_eq_left hLeftLeafRightLeaf]
      simp <;> omega
    · simp only [ite_eq_left hParentLeftLeaf, ite_eq_right hLeftLeafRightLeaf]
      simp <;> omega
  · by_cases hParentRightLeaf : parent < rightLeaf
    · simp only [ite_eq_right hParentLeftLeaf, ite_eq_left hParentRightLeaf]
      simp <;> omega
    · simp only [ite_eq_right hParentLeftLeaf, ite_eq_right hParentRightLeaf]
      simp <;> omega

/-- 長さ8配列の添字3を下降させると、添字3・7の親子条件を満たす。 -/
theorem siftDownRecursive_oct_leftmost_child_bounds
    (root left right leftLeft leftRight rightLeft rightRight leftLeftLeft : Nat) :
    let result := LeanExperiments.HeapSort.siftDownRecursive
      #[root, left, right, leftLeft, leftRight, rightLeft, rightRight, leftLeftLeft] 3
    result[7]! ≤ result[3]! := by
  rw [LeanExperiments.HeapSort.siftDownRecursive_oct_leftmost]
  by_cases h : leftLeft < leftLeftLeft
  · simp only [ite_eq_left h]
    simp <;> omega
  · simp only [ite_eq_right h]
    simp <;> omega

/-- 長さ8配列の添字2を下降させると、その節点と左右の葉が最大ヒープになる。 -/
theorem siftDownRecursive_oct_right_child_bounds
    (root left parent leftLeaf rightLeaf leftChild rightChild tail : Nat) :
    let result := LeanExperiments.HeapSort.siftDownRecursive
      #[root, left, parent, leftLeaf, rightLeaf, leftChild, rightChild, tail] 2
    result[5]! ≤ result[2]! ∧ result[6]! ≤ result[2]! := by
  rw [LeanExperiments.HeapSort.siftDownRecursive_oct_right]
  by_cases hParentLeft : parent < leftChild
  · by_cases hLeftRight : leftChild < rightChild
    · simp only [ite_eq_left hParentLeft, ite_eq_left hLeftRight]
      simp <;> omega
    · simp only [ite_eq_left hParentLeft, ite_eq_right hLeftRight]
      simp <;> omega
  · by_cases hParentRight : parent < rightChild
    · simp only [ite_eq_right hParentLeft, ite_eq_left hParentRight]
      simp <;> omega
    · simp only [ite_eq_right hParentLeft, ite_eq_right hParentRight]
      simp <;> omega

/-- 添字3部分木がヒープなら、添字1の下降後に左部分木全体もヒープになる。 -/
theorem siftDownRecursive_oct_left_subtree_bounds
    (root parent sibling leftChild rightLeaf tailLeft tailRight leftGrandchild : Nat)
    (hGrandchild : leftGrandchild ≤ leftChild) :
    let result := LeanExperiments.HeapSort.siftDownRecursive
      #[root, parent, sibling, leftChild, rightLeaf, tailLeft, tailRight,
        leftGrandchild] 1
    result[3]! ≤ result[1]! ∧ result[4]! ≤ result[1]! ∧
      result[7]! ≤ result[3]! := by
  rw [LeanExperiments.HeapSort.siftDownRecursive_oct_left]
  by_cases hParentLeft : parent < leftChild
  · by_cases hLeftRight : leftChild < rightLeaf
    · simp only [ite_eq_left hParentLeft, ite_eq_left hLeftRight]
      simp <;> omega
    · by_cases hParentGrandchild : parent < leftGrandchild
      · simp only [ite_eq_left hParentLeft, ite_eq_right hLeftRight,
          ite_eq_left hParentGrandchild]
        simp <;> omega
      · simp only [ite_eq_left hParentLeft, ite_eq_right hLeftRight,
          ite_eq_right hParentGrandchild]
        simp <;> omega
  · by_cases hParentRight : parent < rightLeaf
    · simp only [ite_eq_right hParentLeft, ite_eq_left hParentRight]
      simp <;> omega
    · simp only [ite_eq_right hParentLeft, ite_eq_right hParentRight]
      simp <;> omega

/-- 添字2の下降は、別の部分木にある添字3・7を変更しない。 -/
private theorem siftDownRecursive_oct_right_preserves_left_subtree
    (root left parent leftLeaf rightLeaf leftChild rightChild tail : Nat) :
    let result := LeanExperiments.HeapSort.siftDownRecursive
      #[root, left, parent, leftLeaf, rightLeaf, leftChild, rightChild, tail] 2
    result[3]! = leftLeaf ∧ result[7]! = tail := by
  rw [LeanExperiments.HeapSort.siftDownRecursive_oct_right]
  by_cases hParentLeft : parent < leftChild
  · by_cases hLeftRight : leftChild < rightChild
    · simp only [ite_eq_left hParentLeft, ite_eq_left hLeftRight]
      simp
    · simp only [ite_eq_left hParentLeft, ite_eq_right hLeftRight]
      simp
  · by_cases hParentRight : parent < rightChild
    · simp only [ite_eq_right hParentLeft, ite_eq_left hParentRight]
      simp
    · simp only [ite_eq_right hParentLeft, ite_eq_right hParentRight]
      simp

/-- 添字1の下降は、別の部分木にある添字2・5・6を変更しない。 -/
private theorem siftDownRecursive_oct_left_preserves_right_subtree
    (root parent sibling leftChild rightLeaf tailLeft tailRight leftGrandchild : Nat) :
    let result := LeanExperiments.HeapSort.siftDownRecursive
      #[root, parent, sibling, leftChild, rightLeaf, tailLeft, tailRight,
        leftGrandchild] 1
    result[2]! = sibling ∧ result[5]! = tailLeft ∧ result[6]! = tailRight := by
  rw [LeanExperiments.HeapSort.siftDownRecursive_oct_left]
  by_cases hParentLeft : parent < leftChild
  · by_cases hLeftRight : leftChild < rightLeaf
    · simp only [ite_eq_left hParentLeft, ite_eq_left hLeftRight]
      simp
    · by_cases hParentGrandchild : parent < leftGrandchild
      · simp only [ite_eq_left hParentLeft, ite_eq_right hLeftRight,
          ite_eq_left hParentGrandchild]
        simp
      · simp only [ite_eq_left hParentLeft, ite_eq_right hLeftRight,
          ite_eq_right hParentGrandchild]
        simp
  · by_cases hParentRight : parent < rightLeaf
    · simp only [ite_eq_right hParentLeft, ite_eq_left hParentRight]
      simp
    · simp only [ite_eq_right hParentLeft, ite_eq_right hParentRight]
      simp

/-- 長さ8の配列を添字値で明示した列へ書き換える。 -/
private theorem array_eq_index_values_of_size_eq_eight (heap : Array Nat)
    (hSize : heap.size = 8) :
    heap = #[heap[0]!, heap[1]!, heap[2]!, heap[3]!, heap[4]!, heap[5]!,
      heap[6]!, heap[7]!] := by
  apply Array.ext_getElem?
  intro index
  by_cases h0 : index = 0
  · subst index; simp [hSize]
  · by_cases h1 : index = 1
    · subst index; simp [hSize]
    · by_cases h2 : index = 2
      · subst index; simp [hSize]
      · by_cases h3 : index = 3
        · subst index; simp [hSize]
        · by_cases h4 : index = 4
          · subst index; simp [hSize]
          · by_cases h5 : index = 5
            · subst index; simp [hSize]
            · by_cases h6 : index = 6
              · subst index; simp [hSize]
              · by_cases h7 : index = 7
                · subst index; simp [hSize]
                · have hOutside : 8 ≤ index := by omega
                  have hNone : heap[index]? = none :=
                    Array.getElem?_eq_none_iff.mpr (by omega)
                  simp [hOutside, hNone]

/-- 長さ9の配列を添字値で明示した列へ書き換える。 -/
private theorem array_eq_index_values_of_size_eq_nine (heap : Array Nat)
    (hSize : heap.size = 9) :
    heap = #[heap[0]!, heap[1]!, heap[2]!, heap[3]!, heap[4]!, heap[5]!,
      heap[6]!, heap[7]!, heap[8]!] := by
  apply Array.ext_getElem?
  intro index
  by_cases h0 : index = 0
  · subst index; simp [hSize]
  · by_cases h1 : index = 1
    · subst index; simp [hSize]
    · by_cases h2 : index = 2
      · subst index; simp [hSize]
      · by_cases h3 : index = 3
        · subst index; simp [hSize]
        · by_cases h4 : index = 4
          · subst index; simp [hSize]
          · by_cases h5 : index = 5
            · subst index; simp [hSize]
            · by_cases h6 : index = 6
              · subst index; simp [hSize]
              · by_cases h7 : index = 7
                · subst index; simp [hSize]
                · by_cases h8 : index = 8
                  · subst index; simp [hSize]
                  · have hOutside : 9 ≤ index := by omega
                    have hNone : heap[index]? = none :=
                      Array.getElem?_eq_none_iff.mpr (by omega)
                    simp [hOutside, hNone]

/-- 添字3下降後、葉7・8の両方が添字3以下になる。 -/
theorem siftDownRecursive_nine_leftmost_child_bounds
    (root left right parent child4 child5 child6 leftLeaf rightLeaf : Nat) :
    let result := LeanExperiments.HeapSort.siftDownRecursive
      #[root, left, right, parent, child4, child5, child6, leftLeaf, rightLeaf] 3
    result[7]! ≤ result[3]! ∧ result[8]! ≤ result[3]! := by
  rw [LeanExperiments.HeapSort.siftDownRecursive_nine_leftmost]
  by_cases hParentLeft : parent < leftLeaf
  · by_cases hLeftRight : leftLeaf < rightLeaf
    · simp only [ite_eq_left hParentLeft, ite_eq_left hLeftRight]
      simp <;> omega
    · simp only [ite_eq_left hParentLeft, ite_eq_right hLeftRight]
      simp <;> omega
  · by_cases hParentRight : parent < rightLeaf
    · simp only [ite_eq_right hParentLeft, ite_eq_left hParentRight]
      simp <;> omega
    · simp only [ite_eq_right hParentLeft, ite_eq_right hParentRight]
      simp <;> omega

/-- 添字2下降後、その左右の葉5・6は添字2以下になる。 -/
theorem siftDownRecursive_nine_right_child_bounds
    (root left parent leftLeaf rightLeaf leftChild rightChild tailLeft tailRight : Nat) :
    let result := LeanExperiments.HeapSort.siftDownRecursive
      #[root, left, parent, leftLeaf, rightLeaf, leftChild, rightChild, tailLeft,
        tailRight] 2
    result[5]! ≤ result[2]! ∧ result[6]! ≤ result[2]! := by
  rw [LeanExperiments.HeapSort.siftDownRecursive_nine_right]
  by_cases hParentLeft : parent < leftChild
  · by_cases hLeftRight : leftChild < rightChild
    · simp only [ite_eq_left hParentLeft, ite_eq_left hLeftRight]
      simp <;> omega
    · simp only [ite_eq_left hParentLeft, ite_eq_right hLeftRight]
      simp <;> omega
  · by_cases hParentRight : parent < rightChild
    · simp only [ite_eq_right hParentLeft, ite_eq_left hParentRight]
      simp <;> omega
    · simp only [ite_eq_right hParentLeft, ite_eq_right hParentRight]
      simp <;> omega

/-- 子孫部分木がヒープなら、添字1下降後に左側の部分木全体がヒープになる。 -/
theorem siftDownRecursive_nine_left_subtree_bounds
    (root parent sibling leftChild rightLeaf tailLeft tailRight leftGrandchild
      rightGrandchild : Nat)
    (hLeftGrandchild : leftGrandchild ≤ leftChild)
    (hRightGrandchild : rightGrandchild ≤ leftChild) :
    let result := LeanExperiments.HeapSort.siftDownRecursive
      #[root, parent, sibling, leftChild, rightLeaf, tailLeft, tailRight,
        leftGrandchild, rightGrandchild] 1
    result[3]! ≤ result[1]! ∧ result[4]! ≤ result[1]! ∧
      result[7]! ≤ result[3]! ∧ result[8]! ≤ result[3]! := by
  rw [LeanExperiments.HeapSort.siftDownRecursive_nine_left]
  by_cases hParentLeft : parent < leftChild
  · by_cases hLeftRight : leftChild < rightLeaf
    · simp only [ite_eq_left hParentLeft, ite_eq_left hLeftRight]
      simp <;> omega
    · by_cases hParentLeftGrandchild : parent < leftGrandchild
      · by_cases hLeftRightGrandchild : leftGrandchild < rightGrandchild
        · simp only [ite_eq_left hParentLeft, ite_eq_right hLeftRight,
            ite_eq_left hParentLeftGrandchild, ite_eq_left hLeftRightGrandchild]
          simp <;> omega
        · simp only [ite_eq_left hParentLeft, ite_eq_right hLeftRight,
            ite_eq_left hParentLeftGrandchild, ite_eq_right hLeftRightGrandchild]
          simp <;> omega
      · by_cases hParentRightGrandchild : parent < rightGrandchild
        · simp only [ite_eq_left hParentLeft, ite_eq_right hLeftRight,
            ite_eq_right hParentLeftGrandchild, ite_eq_left hParentRightGrandchild]
          simp <;> omega
        · simp only [ite_eq_left hParentLeft, ite_eq_right hLeftRight,
            ite_eq_right hParentLeftGrandchild, ite_eq_right hParentRightGrandchild]
          simp <;> omega
  · by_cases hParentRight : parent < rightLeaf
    · simp only [ite_eq_right hParentLeft, ite_eq_left hParentRight]
      simp <;> omega
    · simp only [ite_eq_right hParentLeft, ite_eq_right hParentRight]
      simp <;> omega

/-- 添字2下降は別の部分木の添字3・7・8を変えない。 -/
private theorem siftDownRecursive_nine_right_preserves_left_subtree
    (root left parent leftLeaf rightLeaf leftChild rightChild leftGrandchild
      rightGrandchild : Nat) :
    let result := LeanExperiments.HeapSort.siftDownRecursive
      #[root, left, parent, leftLeaf, rightLeaf, leftChild, rightChild,
        leftGrandchild, rightGrandchild] 2
    result[3]! = leftLeaf ∧ result[7]! = leftGrandchild ∧
      result[8]! = rightGrandchild := by
  rw [LeanExperiments.HeapSort.siftDownRecursive_nine_right]
  by_cases hParentLeft : parent < leftChild
  · by_cases hLeftRight : leftChild < rightChild
    · simp only [ite_eq_left hParentLeft, ite_eq_left hLeftRight]
      simp
    · simp only [ite_eq_left hParentLeft, ite_eq_right hLeftRight]
      simp
  · by_cases hParentRight : parent < rightChild
    · simp only [ite_eq_right hParentLeft, ite_eq_left hParentRight]
      simp
    · simp only [ite_eq_right hParentLeft, ite_eq_right hParentRight]
      simp

/-- 添字1下降は右部分木の添字2・5・6を変えない。 -/
private theorem siftDownRecursive_nine_left_preserves_right_subtree
    (root parent sibling leftChild rightLeaf tailLeft tailRight leftGrandchild
      rightGrandchild : Nat) :
    let result := LeanExperiments.HeapSort.siftDownRecursive
      #[root, parent, sibling, leftChild, rightLeaf, tailLeft, tailRight,
        leftGrandchild, rightGrandchild] 1
    result[2]! = sibling ∧ result[5]! = tailLeft ∧ result[6]! = tailRight := by
  rw [LeanExperiments.HeapSort.siftDownRecursive_nine_left]
  by_cases hParentLeft : parent < leftChild
  · by_cases hLeftRight : leftChild < rightLeaf
    · simp only [ite_eq_left hParentLeft, ite_eq_left hLeftRight]
      simp
    · by_cases hParentLeftGrandchild : parent < leftGrandchild
      · by_cases hLeftRightGrandchild : leftGrandchild < rightGrandchild
        · simp only [ite_eq_left hParentLeft, ite_eq_right hLeftRight,
            ite_eq_left hParentLeftGrandchild, ite_eq_left hLeftRightGrandchild]
          simp
        · simp only [ite_eq_left hParentLeft, ite_eq_right hLeftRight,
            ite_eq_left hParentLeftGrandchild, ite_eq_right hLeftRightGrandchild]
          simp
      · by_cases hParentRightGrandchild : parent < rightGrandchild
        · simp only [ite_eq_left hParentLeft, ite_eq_right hLeftRight,
            ite_eq_right hParentLeftGrandchild, ite_eq_left hParentRightGrandchild]
          simp
        · simp only [ite_eq_left hParentLeft, ite_eq_right hLeftRight,
            ite_eq_right hParentLeftGrandchild, ite_eq_right hParentRightGrandchild]
          simp
  · by_cases hParentRight : parent < rightLeaf
    · simp only [ite_eq_right hParentLeft, ite_eq_left hParentRight]
      simp
    · simp only [ite_eq_right hParentLeft, ite_eq_right hParentRight]
      simp

private theorem buildMaxHeapRecursive_oct_child_subheaps
    (root left right leftLeft leftRight rightLeft rightRight leftLeftLeft : Nat) :
    let values := #[root, left, right, leftLeft, leftRight, rightLeft, rightRight,
      leftLeftLeft]
    let stage3 := LeanExperiments.HeapSort.siftDownRecursive values 3
    let stage2 := LeanExperiments.HeapSort.siftDownRecursive stage3 2
    let stage1 := LeanExperiments.HeapSort.siftDownRecursive stage2 1
    stage1[3]! ≤ stage1[1]! ∧ stage1[4]! ≤ stage1[1]! ∧
      stage1[7]! ≤ stage1[3]! ∧ stage1[5]! ≤ stage1[2]! ∧
      stage1[6]! ≤ stage1[2]! := by
  let values := #[root, left, right, leftLeft, leftRight, rightLeft, rightRight,
    leftLeftLeft]
  let stage3 := LeanExperiments.HeapSort.siftDownRecursive values 3
  let stage2 := LeanExperiments.HeapSort.siftDownRecursive stage3 2
  let stage1 := LeanExperiments.HeapSort.siftDownRecursive stage2 1
  have hStage3Left := siftDownRecursive_oct_leftmost_child_bounds
    root left right leftLeft leftRight rightLeft rightRight leftLeftLeft
  have hStage3LeftBounds : stage3[7]! ≤ stage3[3]! := by
    simpa [stage3, values] using hStage3Left
  have hStage3Size : stage3.size = 8 := by
    change (LeanExperiments.HeapSort.siftDownRecursive values 3).size = 8
    rw [LeanExperiments.HeapSort.siftDownRecursive_size]
    rfl
  have hStage3Values := array_eq_index_values_of_size_eq_eight stage3 hStage3Size
  have hStage2Right := siftDownRecursive_oct_right_child_bounds
    stage3[0]! stage3[1]! stage3[2]! stage3[3]! stage3[4]! stage3[5]! stage3[6]!
      stage3[7]!
  have hStage2Frame := siftDownRecursive_oct_right_preserves_left_subtree
    stage3[0]! stage3[1]! stage3[2]! stage3[3]! stage3[4]! stage3[5]! stage3[6]!
      stage3[7]!
  have hStage2Left : stage2[7]! ≤ stage2[3]! := by
    have hFrame : stage2[3]! = stage3[3]! ∧ stage2[7]! = stage3[7]! := by
      have hFrame' := hStage2Frame
      rw [← hStage3Values] at hFrame'
      change stage2[3]! = stage3[3]! ∧ stage2[7]! = stage3[7]!
      exact hFrame'
    calc
      stage2[7]! = stage3[7]! := hFrame.2
      _ ≤ stage3[3]! := hStage3LeftBounds
      _ = stage2[3]! := hFrame.1.symm
  have hStage2Size : stage2.size = 8 := by
    change (LeanExperiments.HeapSort.siftDownRecursive stage3 2).size = 8
    rw [LeanExperiments.HeapSort.siftDownRecursive_size, hStage3Size]
  have hStage2Values := array_eq_index_values_of_size_eq_eight stage2 hStage2Size
  have hStage2RightBounds :
      stage2[5]! ≤ stage2[2]! ∧ stage2[6]! ≤ stage2[2]! := by
    have hRight' := hStage2Right
    rw [← hStage3Values] at hRight'
    change stage2[5]! ≤ stage2[2]! ∧ stage2[6]! ≤ stage2[2]!
    exact hRight'
  have hStage1Left := siftDownRecursive_oct_left_subtree_bounds
    stage2[0]! stage2[1]! stage2[2]! stage2[3]! stage2[4]! stage2[5]!
      stage2[6]! stage2[7]! hStage2Left
  have hStage1RightFrame := siftDownRecursive_oct_left_preserves_right_subtree
    stage2[0]! stage2[1]! stage2[2]! stage2[3]! stage2[4]! stage2[5]!
      stage2[6]! stage2[7]!
  have hStage1LeftBounds : stage1[3]! ≤ stage1[1]! ∧
      stage1[4]! ≤ stage1[1]! ∧ stage1[7]! ≤ stage1[3]! := by
    have hLeft' := hStage1Left
    rw [← hStage2Values] at hLeft'
    change stage1[3]! ≤ stage1[1]! ∧ stage1[4]! ≤ stage1[1]! ∧
      stage1[7]! ≤ stage1[3]!
    exact hLeft'
  have hStage1RightFrame : stage1[2]! = stage2[2]! ∧
      stage1[5]! = stage2[5]! ∧ stage1[6]! = stage2[6]! := by
    have hRight' := hStage1RightFrame
    rw [← hStage2Values] at hRight'
    change stage1[2]! = stage2[2]! ∧ stage1[5]! = stage2[5]! ∧
      stage1[6]! = stage2[6]!
    exact hRight'
  refine ⟨hStage1LeftBounds.1, hStage1LeftBounds.2.1,
    hStage1LeftBounds.2.2, ?_, ?_⟩
  · calc
      stage1[5]! = stage2[5]! := hStage1RightFrame.2.1
      _ ≤ stage2[2]! := hStage2RightBounds.1
      _ = stage1[2]! := hStage1RightFrame.1.symm
  · calc
      stage1[6]! = stage2[6]! := hStage1RightFrame.2.2
      _ ≤ stage2[2]! := hStage2RightBounds.2
      _ = stage1[2]! := hStage1RightFrame.1.symm

/-- 9要素の構築で添字3・2・1を処理すると、根の左右部分木が最大ヒープになる。 -/
theorem buildMaxHeapRecursive_nine_child_subheaps
    (root left right leftLeft leftRight rightLeft rightRight leftLeftLeft
      leftLeftRight : Nat) :
    let values := #[root, left, right, leftLeft, leftRight, rightLeft, rightRight,
      leftLeftLeft, leftLeftRight]
    let stage3 := LeanExperiments.HeapSort.siftDownRecursive values 3
    let stage2 := LeanExperiments.HeapSort.siftDownRecursive stage3 2
    let stage1 := LeanExperiments.HeapSort.siftDownRecursive stage2 1
    stage1[3]! ≤ stage1[1]! ∧ stage1[4]! ≤ stage1[1]! ∧
      stage1[7]! ≤ stage1[3]! ∧ stage1[8]! ≤ stage1[3]! ∧
      stage1[5]! ≤ stage1[2]! ∧ stage1[6]! ≤ stage1[2]! := by
  let values := #[root, left, right, leftLeft, leftRight, rightLeft, rightRight,
    leftLeftLeft, leftLeftRight]
  let stage3 := LeanExperiments.HeapSort.siftDownRecursive values 3
  let stage2 := LeanExperiments.HeapSort.siftDownRecursive stage3 2
  let stage1 := LeanExperiments.HeapSort.siftDownRecursive stage2 1
  have hStage3Left := siftDownRecursive_nine_leftmost_child_bounds
    root left right leftLeft leftRight rightLeft rightRight leftLeftLeft leftLeftRight
  have hStage3Bounds : stage3[7]! ≤ stage3[3]! ∧ stage3[8]! ≤ stage3[3]! := by
    simpa [stage3, values] using hStage3Left
  have hStage3Size : stage3.size = 9 := by
    change (LeanExperiments.HeapSort.siftDownRecursive values 3).size = 9
    rw [LeanExperiments.HeapSort.siftDownRecursive_size]
    rfl
  have hStage3Values := array_eq_index_values_of_size_eq_nine stage3 hStage3Size
  have hStage2Right := siftDownRecursive_nine_right_child_bounds
    stage3[0]! stage3[1]! stage3[2]! stage3[3]! stage3[4]! stage3[5]!
      stage3[6]! stage3[7]! stage3[8]!
  have hStage2Frame := siftDownRecursive_nine_right_preserves_left_subtree
    stage3[0]! stage3[1]! stage3[2]! stage3[3]! stage3[4]! stage3[5]!
      stage3[6]! stage3[7]! stage3[8]!
  have hStage2Left : stage2[7]! ≤ stage2[3]! ∧ stage2[8]! ≤ stage2[3]! := by
    have hFrame : stage2[3]! = stage3[3]! ∧ stage2[7]! = stage3[7]! ∧
        stage2[8]! = stage3[8]! := by
      have hFrame' := hStage2Frame
      rw [← hStage3Values] at hFrame'
      change stage2[3]! = stage3[3]! ∧ stage2[7]! = stage3[7]! ∧
        stage2[8]! = stage3[8]!
      exact hFrame'
    constructor
    · calc
        stage2[7]! = stage3[7]! := hFrame.2.1
        _ ≤ stage3[3]! := hStage3Bounds.1
        _ = stage2[3]! := hFrame.1.symm
    · calc
        stage2[8]! = stage3[8]! := hFrame.2.2
        _ ≤ stage3[3]! := hStage3Bounds.2
        _ = stage2[3]! := hFrame.1.symm
  have hStage2Size : stage2.size = 9 := by
    change (LeanExperiments.HeapSort.siftDownRecursive stage3 2).size = 9
    rw [LeanExperiments.HeapSort.siftDownRecursive_size, hStage3Size]
  have hStage2Values := array_eq_index_values_of_size_eq_nine stage2 hStage2Size
  have hStage2RightBounds :
      stage2[5]! ≤ stage2[2]! ∧ stage2[6]! ≤ stage2[2]! := by
    have hRight' := hStage2Right
    rw [← hStage3Values] at hRight'
    change stage2[5]! ≤ stage2[2]! ∧ stage2[6]! ≤ stage2[2]!
    exact hRight'
  have hStage1Left := siftDownRecursive_nine_left_subtree_bounds
    stage2[0]! stage2[1]! stage2[2]! stage2[3]! stage2[4]! stage2[5]!
      stage2[6]! stage2[7]! stage2[8]! hStage2Left.1 hStage2Left.2
  have hStage1RightFrame := siftDownRecursive_nine_left_preserves_right_subtree
    stage2[0]! stage2[1]! stage2[2]! stage2[3]! stage2[4]! stage2[5]!
      stage2[6]! stage2[7]! stage2[8]!
  have hStage1LeftBounds : stage1[3]! ≤ stage1[1]! ∧
      stage1[4]! ≤ stage1[1]! ∧ stage1[7]! ≤ stage1[3]! ∧
      stage1[8]! ≤ stage1[3]! := by
    have hLeft' := hStage1Left
    rw [← hStage2Values] at hLeft'
    change stage1[3]! ≤ stage1[1]! ∧ stage1[4]! ≤ stage1[1]! ∧
      stage1[7]! ≤ stage1[3]! ∧ stage1[8]! ≤ stage1[3]!
    exact hLeft'
  have hStage1RightFrame : stage1[2]! = stage2[2]! ∧
      stage1[5]! = stage2[5]! ∧ stage1[6]! = stage2[6]! := by
    have hRight' := hStage1RightFrame
    rw [← hStage2Values] at hRight'
    change stage1[2]! = stage2[2]! ∧ stage1[5]! = stage2[5]! ∧
      stage1[6]! = stage2[6]!
    exact hRight'
  refine ⟨hStage1LeftBounds.1, hStage1LeftBounds.2.1,
    hStage1LeftBounds.2.2.1, hStage1LeftBounds.2.2.2,
    ?_, ?_⟩
  · calc
      stage1[5]! = stage2[5]! := hStage1RightFrame.2.1
      _ ≤ stage2[2]! := hStage2RightBounds.1
      _ = stage1[2]! := hStage1RightFrame.1.symm
  · calc
      stage1[6]! = stage2[6]! := hStage1RightFrame.2.2
      _ ≤ stage2[2]! := hStage2RightBounds.2
      _ = stage1[2]! := hStage1RightFrame.1.symm

/-- 長さ9で下位の親を処理した後、根が左右の子以上なら再帰版構築は最大ヒープを返す。

添字3・2・1の処理後に左右の部分木がヒープになる一般補題を使い、最後の根下降が
恒等処理であることを示す。長さ9の構築証明に必要な根段階の条件を明示する。
-/
theorem buildMaxHeapRecursive_correct_of_size_eq_nine_of_root_step
    (input : Array Nat) (hSize : input.size = 9)
    (hRootStep :
      let stage3 := LeanExperiments.HeapSort.siftDownRecursive input 3
      let stage2 := LeanExperiments.HeapSort.siftDownRecursive stage3 2
      let stage1 := LeanExperiments.HeapSort.siftDownRecursive stage2 1
      stage1[1]! ≤ stage1[0]! ∧ stage1[2]! ≤ stage1[0]!) :
    HeapBuildCorrect input (LeanExperiments.HeapSort.buildMaxHeapRecursive input) := by
  let stage3 := LeanExperiments.HeapSort.siftDownRecursive input 3
  let stage2 := LeanExperiments.HeapSort.siftDownRecursive stage3 2
  let stage1 := LeanExperiments.HeapSort.siftDownRecursive stage2 1
  have hStage3Size : stage3.size = 9 := by
    simp [stage3, siftDownRecursive_size, hSize]
  have hStage2Size : stage2.size = 9 := by
    simp [stage2, siftDownRecursive_size, hStage3Size]
  have hStage1Size : stage1.size = 9 := by
    simp [stage1, siftDownRecursive_size, hStage2Size]
  have hChildren := buildMaxHeapRecursive_nine_child_subheaps
    input[0]! input[1]! input[2]! input[3]! input[4]! input[5]! input[6]!
      input[7]! input[8]!
  have hChildBounds :
      stage1[3]! ≤ stage1[1]! ∧ stage1[4]! ≤ stage1[1]! ∧
      stage1[7]! ≤ stage1[3]! ∧ stage1[8]! ≤ stage1[3]! ∧
      stage1[5]! ≤ stage1[2]! ∧ stage1[6]! ≤ stage1[2]! := by
    simpa [stage1, stage2, stage3,
      ← array_eq_index_values_of_size_eq_nine input hSize] using hChildren
  have hRootBounds : stage1[1]! ≤ stage1[0]! ∧ stage1[2]! ≤ stage1[0]! := by
    simpa [stage1, stage2, stage3] using hRootStep
  have hRootNoop : LeanExperiments.HeapSort.siftDownRecursive stage1 0 = stage1 := by
    apply LeanExperiments.HeapSort.siftDownRecursive_eq_self_of_dominatesChildren
    · intro _
      exact hRootBounds.1
    · intro _
      exact hRootBounds.2
  have hStageHeap : MaxHeap stage1 := by
    unfold MaxHeap
    intro index hIndex
    have hIndexSmall : index < 9 := by simpa [hStage1Size] using hIndex
    have hCases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨
        index = 4 ∨ index = 5 ∨ index = 6 ∨ index = 7 ∨ index = 8 := by omega
    rcases hCases with h | h | h | h | h | h | h | h | h
    · subst index
      exact ⟨fun _ => hRootBounds.1, fun _ => hRootBounds.2⟩
    · subst index
      exact ⟨fun _ => hChildBounds.1, fun _ => hChildBounds.2.1⟩
    · subst index
      exact ⟨fun _ => hChildBounds.2.2.2.2.1,
        fun _ => hChildBounds.2.2.2.2.2⟩
    · subst index
      exact ⟨fun _ => hChildBounds.2.2.1, fun _ => hChildBounds.2.2.2.1⟩
    · subst index
      constructor <;> intro hChild <;> have := hChild <;> simp [hStage1Size] at this
    · subst index
      constructor <;> intro hChild <;> have := hChild <;> simp [hStage1Size] at this
    · subst index
      constructor <;> intro hChild <;> have := hChild <;> simp [hStage1Size] at this
    · subst index
      constructor <;> intro hChild <;> have := hChild <;> simp [hStage1Size] at this
    · subst index
      constructor <;> intro hChild <;> have := hChild <;> simp [hStage1Size] at this
  refine ⟨?_, buildMaxHeapRecursive_perm input⟩
  have hBuild : LeanExperiments.HeapSort.buildMaxHeapRecursive input =
      LeanExperiments.HeapSort.siftDownRecursive stage1 0 := by
    unfold LeanExperiments.HeapSort.buildMaxHeapRecursive
    change LeanExperiments.HeapSort.buildMaxHeapRecursive.go (input.size / 2) input = _
    have hFuel : input.size / 2 = 4 := by omega
    rw [hFuel]
    rw [LeanExperiments.HeapSort.buildMaxHeapRecursive.go]
    rw [LeanExperiments.HeapSort.buildMaxHeapRecursive.go]
    rw [LeanExperiments.HeapSort.buildMaxHeapRecursive.go]
    rw [LeanExperiments.HeapSort.buildMaxHeapRecursive.go]
    rfl
  rw [hBuild, hRootNoop]
  exact hStageHeap

/-- 長さ9で根が入力中の最大値なら、再帰版ヒープ構築は最大ヒープを返す。

添字3・2・1の下降が左右の部分木を整える。これらの呼び出しは添字0を変えず、
根は全ての入力値以上なので最後の根下降は配列を変更しない。
-/
theorem buildMaxHeapRecursive_correct_of_size_eq_nine_of_root_maximum
    (input : Array Nat) (hSize : input.size = 9)
    (hRootMaximum : ∀ value, value ∈ input.toList → value ≤ input[0]!) :
    HeapBuildCorrect input (LeanExperiments.HeapSort.buildMaxHeapRecursive input) := by
  let stage3 := LeanExperiments.HeapSort.siftDownRecursive input 3
  let stage2 := LeanExperiments.HeapSort.siftDownRecursive stage3 2
  let stage1 := LeanExperiments.HeapSort.siftDownRecursive stage2 1
  have hStage3Size : stage3.size = 9 := by
    simp [stage3, siftDownRecursive_size, hSize]
  have hStage2Size : stage2.size = 9 := by
    simp [stage2, siftDownRecursive_size, hStage3Size]
  have hStage1Size : stage1.size = 9 := by
    simp [stage1, siftDownRecursive_size, hStage2Size]
  have hChildren := buildMaxHeapRecursive_nine_child_subheaps
    input[0]! input[1]! input[2]! input[3]! input[4]! input[5]! input[6]!
      input[7]! input[8]!
  have hChildBounds :
      stage1[3]! ≤ stage1[1]! ∧ stage1[4]! ≤ stage1[1]! ∧
      stage1[7]! ≤ stage1[3]! ∧ stage1[8]! ≤ stage1[3]! ∧
      stage1[5]! ≤ stage1[2]! ∧ stage1[6]! ≤ stage1[2]! := by
    simpa [stage1, stage2, stage3,
      ← array_eq_index_values_of_size_eq_nine input hSize] using hChildren
  have hRootStable : stage1[0]! = input[0]! := by
    calc
      stage1[0]! = stage2[0]! := by
        exact siftDownRecursive_getElem!_eq_of_lt_root stage2 1 0
          (by simp [hStage2Size]) (by omega)
      _ = stage3[0]! := by
        exact siftDownRecursive_getElem!_eq_of_lt_root stage3 2 0
          (by simp [hStage3Size]) (by omega)
      _ = input[0]! := by
        exact siftDownRecursive_getElem!_eq_of_lt_root input 3 0
          (by omega) (by omega)
  have hStagePerm : stage1.toList.Perm input.toList := by
    exact (siftDownRecursive_perm stage2 1).trans
      ((siftDownRecursive_perm stage3 2).trans (siftDownRecursive_perm input 3))
  have hOneMem : stage1[1]! ∈ input.toList := by
    apply hStagePerm.mem_iff.mp
    apply Array.mem_toList_iff.mpr
    apply Array.mem_iff_getElem.mpr
    exact ⟨1, by omega, (getElem!_pos stage1 1 (by omega)).symm⟩
  have hTwoMem : stage1[2]! ∈ input.toList := by
    apply hStagePerm.mem_iff.mp
    apply Array.mem_toList_iff.mpr
    apply Array.mem_iff_getElem.mpr
    exact ⟨2, by omega, (getElem!_pos stage1 2 (by omega)).symm⟩
  have hRootOne : stage1[1]! ≤ stage1[0]! := by
    rw [hRootStable]
    exact hRootMaximum stage1[1]! hOneMem
  have hRootTwo : stage1[2]! ≤ stage1[0]! := by
    rw [hRootStable]
    exact hRootMaximum stage1[2]! hTwoMem
  have hRootNoop : LeanExperiments.HeapSort.siftDownRecursive stage1 0 = stage1 := by
    apply LeanExperiments.HeapSort.siftDownRecursive_eq_self_of_dominatesChildren
    · intro _
      exact hRootOne
    · intro _
      exact hRootTwo
  have hStageHeap : MaxHeap stage1 := by
    unfold MaxHeap
    intro index hIndex
    have hIndexSmall : index < 9 := by simpa [hStage1Size] using hIndex
    have hCases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨
        index = 4 ∨ index = 5 ∨ index = 6 ∨ index = 7 ∨ index = 8 := by omega
    rcases hCases with h | h | h | h | h | h | h | h | h
    · subst index
      exact ⟨fun _ => hRootOne, fun _ => hRootTwo⟩
    · subst index
      exact ⟨fun _ => hChildBounds.1, fun _ => hChildBounds.2.1⟩
    · subst index
      exact ⟨fun _ => hChildBounds.2.2.2.2.1,
        fun _ => hChildBounds.2.2.2.2.2⟩
    · subst index
      exact ⟨fun _ => hChildBounds.2.2.1, fun _ => hChildBounds.2.2.2.1⟩
    · subst index
      constructor <;> intro hChild <;> have := hChild <;> simp [hStage1Size] at this
    · subst index
      constructor <;> intro hChild <;> have := hChild <;> simp [hStage1Size] at this
    · subst index
      constructor <;> intro hChild <;> have := hChild <;> simp [hStage1Size] at this
    · subst index
      constructor <;> intro hChild <;> have := hChild <;> simp [hStage1Size] at this
    · subst index
      constructor <;> intro hChild <;> have := hChild <;> simp [hStage1Size] at this
  refine ⟨?_, buildMaxHeapRecursive_perm input⟩
  have hBuild : LeanExperiments.HeapSort.buildMaxHeapRecursive input =
      LeanExperiments.HeapSort.siftDownRecursive stage1 0 := by
    unfold LeanExperiments.HeapSort.buildMaxHeapRecursive
    change LeanExperiments.HeapSort.buildMaxHeapRecursive.go (input.size / 2) input = _
    have hFuel : input.size / 2 = 4 := by omega
    rw [hFuel]
    rw [LeanExperiments.HeapSort.buildMaxHeapRecursive.go]
    rw [LeanExperiments.HeapSort.buildMaxHeapRecursive.go]
    rw [LeanExperiments.HeapSort.buildMaxHeapRecursive.go]
    rw [LeanExperiments.HeapSort.buildMaxHeapRecursive.go]
    rfl
  rw [hBuild, hRootNoop]
  exact hStageHeap

set_option maxHeartbeats 1000000
/-- 任意の8要素列では、再帰版ヒープ構築後に最大ヒープ条件を満たす。 -/
theorem buildMaxHeapRecursive_correct_oct
    (root left right leftLeft leftRight rightLeft rightRight leftLeftLeft : Nat) :
    HeapBuildCorrect
      #[root, left, right, leftLeft, leftRight, rightLeft, rightRight, leftLeftLeft]
      (LeanExperiments.HeapSort.buildMaxHeapRecursive
        #[root, left, right, leftLeft, leftRight, rightLeft, rightRight, leftLeftLeft]) := by
  let values := #[root, left, right, leftLeft, leftRight, rightLeft, rightRight,
    leftLeftLeft]
  let stage3 := LeanExperiments.HeapSort.siftDownRecursive values 3
  let stage2 := LeanExperiments.HeapSort.siftDownRecursive stage3 2
  let stage1 := LeanExperiments.HeapSort.siftDownRecursive stage2 1
  refine ⟨?_, buildMaxHeapRecursive_perm values⟩
  unfold LeanExperiments.HeapSort.buildMaxHeapRecursive
  change MaxHeap (LeanExperiments.HeapSort.buildMaxHeapRecursive.go (values.size / 2) values)
  have hFuel : values.size / 2 = 4 := by simp [values]
  rw [hFuel]
  rw [LeanExperiments.HeapSort.buildMaxHeapRecursive.go]
  rw [LeanExperiments.HeapSort.buildMaxHeapRecursive.go]
  rw [LeanExperiments.HeapSort.buildMaxHeapRecursive.go]
  rw [LeanExperiments.HeapSort.buildMaxHeapRecursive.go]
  change MaxHeap (LeanExperiments.HeapSort.siftDownRecursive stage1 0)
  have hChildBounds := buildMaxHeapRecursive_oct_child_subheaps
    root left right leftLeft leftRight rightLeft rightRight leftLeftLeft
  change stage1[3]! ≤ stage1[1]! ∧ stage1[4]! ≤ stage1[1]! ∧
    stage1[7]! ≤ stage1[3]! ∧ stage1[5]! ≤ stage1[2]! ∧
    stage1[6]! ≤ stage1[2]! at hChildBounds
  have hStage1Size : stage1.size = 8 := by
    change (LeanExperiments.HeapSort.siftDownRecursive stage2 1).size = 8
    rw [LeanExperiments.HeapSort.siftDownRecursive_size,
      LeanExperiments.HeapSort.siftDownRecursive_size,
      LeanExperiments.HeapSort.siftDownRecursive_size]
    simp [values]
  have hStage1Values := array_eq_index_values_of_size_eq_eight stage1 hStage1Size
  have hRootHeap := siftDownRecursive_oct_root_maxHeap
    stage1[0]! stage1[1]! stage1[2]! stage1[3]! stage1[4]! stage1[5]!
      stage1[6]! stage1[7]!
      hChildBounds.1 hChildBounds.2.1 hChildBounds.2.2.2.1
      hChildBounds.2.2.2.2 hChildBounds.2.2.1
  rw [hStage1Values]
  exact hRootHeap
set_option maxHeartbeats 200000

/-- 任意の7要素列では、再帰版ヒープ構築後に最大ヒープ条件を満たす。 -/
theorem buildMaxHeapRecursive_correct_sept
    (root left right leftLeft leftRight rightLeft rightRight : Nat) :
    HeapBuildCorrect #[root, left, right, leftLeft, leftRight, rightLeft, rightRight]
      (LeanExperiments.HeapSort.buildMaxHeapRecursive
        #[root, left, right, leftLeft, leftRight, rightLeft, rightRight]) := by
  refine ⟨?_, buildMaxHeapRecursive_perm
    #[root, left, right, leftLeft, leftRight, rightLeft, rightRight]⟩
  unfold LeanExperiments.HeapSort.buildMaxHeapRecursive
  change MaxHeap (LeanExperiments.HeapSort.buildMaxHeapRecursive.go
    (#[root, left, right, leftLeft, leftRight, rightLeft, rightRight].size / 2)
    #[root, left, right, leftLeft, leftRight, rightLeft, rightRight])
  have hFuel :
      #[root, left, right, leftLeft, leftRight, rightLeft, rightRight].size / 2 = 3 := by
    simp
  rw [hFuel]
  rw [LeanExperiments.HeapSort.buildMaxHeapRecursive.go]
  rw [LeanExperiments.HeapSort.buildMaxHeapRecursive.go]
  rw [LeanExperiments.HeapSort.buildMaxHeapRecursive.go]
  change MaxHeap (LeanExperiments.HeapSort.siftDownRecursive
    (LeanExperiments.HeapSort.siftDownRecursive
      (LeanExperiments.HeapSort.siftDownRecursive
        #[root, left, right, leftLeft, leftRight, rightLeft, rightRight] 2) 1) 0)
  rw [LeanExperiments.HeapSort.siftDownRecursive_sept_right]
  by_cases hRightLeft : right < rightLeft
  · by_cases hLeftRight : rightLeft < rightRight
    · simp only [ite_eq_left hRightLeft, ite_eq_left hLeftRight]
      rw [LeanExperiments.HeapSort.siftDownRecursive_sept_left]
      by_cases hLeftLeft : left < leftLeft
      · by_cases hLeftLeftRight : leftLeft < leftRight
        · simp only [ite_eq_left hLeftLeft, ite_eq_left hLeftLeftRight]
          apply siftDownRecursive_sept_root_maxHeap <;> omega
        · simp only [ite_eq_left hLeftLeft, ite_eq_right hLeftLeftRight]
          apply siftDownRecursive_sept_root_maxHeap <;> omega
      · by_cases hLeftRightLeaf : left < leftRight
        · simp only [ite_eq_right hLeftLeft, ite_eq_left hLeftRightLeaf]
          apply siftDownRecursive_sept_root_maxHeap <;> omega
        · simp only [ite_eq_right hLeftLeft, ite_eq_right hLeftRightLeaf]
          apply siftDownRecursive_sept_root_maxHeap <;> omega
    · simp only [ite_eq_left hRightLeft, ite_eq_right hLeftRight]
      rw [LeanExperiments.HeapSort.siftDownRecursive_sept_left]
      by_cases hLeftLeft : left < leftLeft
      · by_cases hLeftLeftRight : leftLeft < leftRight
        · simp only [ite_eq_left hLeftLeft, ite_eq_left hLeftLeftRight]
          apply siftDownRecursive_sept_root_maxHeap <;> omega
        · simp only [ite_eq_left hLeftLeft, ite_eq_right hLeftLeftRight]
          apply siftDownRecursive_sept_root_maxHeap <;> omega
      · by_cases hLeftRightLeaf : left < leftRight
        · simp only [ite_eq_right hLeftLeft, ite_eq_left hLeftRightLeaf]
          apply siftDownRecursive_sept_root_maxHeap <;> omega
        · simp only [ite_eq_right hLeftLeft, ite_eq_right hLeftRightLeaf]
          apply siftDownRecursive_sept_root_maxHeap <;> omega
  · by_cases hRightRight : right < rightRight
    · simp only [ite_eq_right hRightLeft, ite_eq_left hRightRight]
      rw [LeanExperiments.HeapSort.siftDownRecursive_sept_left]
      by_cases hLeftLeft : left < leftLeft
      · by_cases hLeftLeftRight : leftLeft < leftRight
        · simp only [ite_eq_left hLeftLeft, ite_eq_left hLeftLeftRight]
          apply siftDownRecursive_sept_root_maxHeap <;> omega
        · simp only [ite_eq_left hLeftLeft, ite_eq_right hLeftLeftRight]
          apply siftDownRecursive_sept_root_maxHeap <;> omega
      · by_cases hLeftRightLeaf : left < leftRight
        · simp only [ite_eq_right hLeftLeft, ite_eq_left hLeftRightLeaf]
          apply siftDownRecursive_sept_root_maxHeap <;> omega
        · simp only [ite_eq_right hLeftLeft, ite_eq_right hLeftRightLeaf]
          apply siftDownRecursive_sept_root_maxHeap <;> omega
    · simp only [ite_eq_right hRightLeft, ite_eq_right hRightRight]
      rw [LeanExperiments.HeapSort.siftDownRecursive_sept_left]
      by_cases hLeftLeft : left < leftLeft
      · by_cases hLeftLeftRight : leftLeft < leftRight
        · simp only [ite_eq_left hLeftLeft, ite_eq_left hLeftLeftRight]
          apply siftDownRecursive_sept_root_maxHeap <;> omega
        · simp only [ite_eq_left hLeftLeft, ite_eq_right hLeftLeftRight]
          apply siftDownRecursive_sept_root_maxHeap <;> omega
      · by_cases hLeftRightLeaf : left < leftRight
        · simp only [ite_eq_right hLeftLeft, ite_eq_left hLeftRightLeaf]
          apply siftDownRecursive_sept_root_maxHeap <;> omega
        · simp only [ite_eq_right hLeftLeft, ite_eq_right hLeftRightLeaf]
          apply siftDownRecursive_sept_root_maxHeap <;> omega

/-- 長さ2以下の任意配列は、再帰版ヒープ構築後に最大ヒープ条件を満たす。

2要素の場合は根と唯一の子を比較し、大きい方を根へ置く下降補題を使う。
-/
theorem buildMaxHeapRecursive_correct_of_size_le_two (values : Array Nat)
    (hSize : values.size ≤ 2) :
    HeapBuildCorrect values (LeanExperiments.HeapSort.buildMaxHeapRecursive values) := by
  by_cases hSmall : values.size ≤ 1
  · rw [buildMaxHeapRecursive_eq_self_of_size_le_one values hSmall]
    constructor
    · unfold MaxHeap
      intro index hIndex
      constructor <;> intro hChild <;> omega
    · exact List.Perm.refl _
  · have hSizeEq : values.size = 2 := by omega
    have hValues : values = #[values[0]!, values[1]!] := by
      apply Array.ext_getElem?
      intro index
      by_cases hZero : index = 0
      · subst index
        simp [hSizeEq]
      · by_cases hOne : index = 1
        · subst index
          simp [hSizeEq]
        · have hOutside : 2 ≤ index := by omega
          have hNone : values[index]? = none :=
            Array.getElem?_eq_none_iff.mpr (by omega)
          simp [hOutside, hNone]
    rw [hValues]
    exact buildMaxHeapRecursive_correct_pair values[0]! values[1]!

/-- 長さ2の配列では、再帰版ヒープ構築は根からの下降と一致する。 -/
private theorem buildMaxHeapRecursive_eq_siftDown_of_size_eq_two
    (values : Array Nat) (hSize : values.size = 2) :
    LeanExperiments.HeapSort.buildMaxHeapRecursive values =
      LeanExperiments.HeapSort.siftDownRecursive values 0 := by
  unfold LeanExperiments.HeapSort.buildMaxHeapRecursive
  have hFuel : values.size / 2 = 1 := by omega
  rw [hFuel]
  rw [LeanExperiments.HeapSort.buildMaxHeapRecursive.go]
  rfl

/-- 長さ3以下では、再帰版ヒープ構築は根からの下降だけで完了する。 -/
private theorem buildMaxHeapRecursive_eq_siftDown_of_size_le_three
    (values : Array Nat) (hSize : values.size ≤ 3) :
    LeanExperiments.HeapSort.buildMaxHeapRecursive values =
      LeanExperiments.HeapSort.siftDownRecursive values 0 := by
  by_cases hSmall : values.size ≤ 1
  · rw [buildMaxHeapRecursive_eq_self_of_size_le_one values hSmall]
    exact (LeanExperiments.HeapSort.siftDownRecursive_eq_self_of_noLeftChild
      values 0 (by omega)).symm
  · have hSizeCases : values.size = 2 ∨ values.size = 3 := by omega
    rcases hSizeCases with hTwo | hThree
    · exact buildMaxHeapRecursive_eq_siftDown_of_size_eq_two values hTwo
    · unfold LeanExperiments.HeapSort.buildMaxHeapRecursive
      have hFuel : values.size / 2 = 1 := by omega
      rw [hFuel]
      rw [LeanExperiments.HeapSort.buildMaxHeapRecursive.go]
      rfl

/-- 長さ3以下の任意配列は、再帰版ヒープ構築後に最大ヒープ条件を満たす。 -/
theorem buildMaxHeapRecursive_correct_of_size_le_three (values : Array Nat)
    (hSize : values.size ≤ 3) :
    HeapBuildCorrect values (LeanExperiments.HeapSort.buildMaxHeapRecursive values) := by
  by_cases hSmall : values.size ≤ 2
  · exact buildMaxHeapRecursive_correct_of_size_le_two values hSmall
  · have hSizeEq : values.size = 3 := by omega
    have hValues : values = #[values[0]!, values[1]!, values[2]!] := by
      apply Array.ext_getElem?
      intro index
      by_cases hZero : index = 0
      · subst index
        simp [hSizeEq]
      · by_cases hOne : index = 1
        · subst index
          simp [hSizeEq]
        · by_cases hTwo : index = 2
          · subst index
            simp [hSizeEq]
          · have hOutside : 3 ≤ index := by omega
            have hNone : values[index]? = none :=
              Array.getElem?_eq_none_iff.mpr (by omega)
            simp [hOutside, hNone]
    rw [hValues]
    exact buildMaxHeapRecursive_correct_triple values[0]! values[1]! values[2]!

/-- 長さ4以下の任意配列は、再帰版ヒープ構築後に最大ヒープ条件を満たす。 -/
theorem buildMaxHeapRecursive_correct_of_size_le_four (values : Array Nat)
    (hSize : values.size ≤ 4) :
    HeapBuildCorrect values (LeanExperiments.HeapSort.buildMaxHeapRecursive values) := by
  by_cases hSmall : values.size ≤ 3
  · exact buildMaxHeapRecursive_correct_of_size_le_three values hSmall
  · have hSizeEq : values.size = 4 := by omega
    have hValues : values = #[values[0]!, values[1]!, values[2]!, values[3]!] := by
      apply Array.ext_getElem?
      intro index
      by_cases hZero : index = 0
      · subst index
        simp [hSizeEq]
      · by_cases hOne : index = 1
        · subst index
          simp [hSizeEq]
        · by_cases hTwo : index = 2
          · subst index
            simp [hSizeEq]
          · by_cases hThree : index = 3
            · subst index
              simp [hSizeEq]
            · have hOutside : 4 ≤ index := by omega
              have hNone : values[index]? = none :=
                Array.getElem?_eq_none_iff.mpr (by omega)
              simp [hOutside, hNone]
    rw [hValues]
    exact buildMaxHeapRecursive_correct_quad
      values[0]! values[1]! values[2]! values[3]!

/-- 長さ5以下の任意配列は、再帰版ヒープ構築後に最大ヒープ条件を満たす。 -/
theorem buildMaxHeapRecursive_correct_of_size_le_five (values : Array Nat)
    (hSize : values.size ≤ 5) :
    HeapBuildCorrect values (LeanExperiments.HeapSort.buildMaxHeapRecursive values) := by
  by_cases hSmall : values.size ≤ 4
  · exact buildMaxHeapRecursive_correct_of_size_le_four values hSmall
  · have hSizeEq : values.size = 5 := by omega
    have hValues : values =
        #[values[0]!, values[1]!, values[2]!, values[3]!, values[4]!] := by
      apply Array.ext_getElem?
      intro index
      by_cases hZero : index = 0
      · subst index
        simp [hSizeEq]
      · by_cases hOne : index = 1
        · subst index
          simp [hSizeEq]
        · by_cases hTwo : index = 2
          · subst index
            simp [hSizeEq]
          · by_cases hThree : index = 3
            · subst index
              simp [hSizeEq]
            · by_cases hFour : index = 4
              · subst index
                simp [hSizeEq]
              · have hOutside : 5 ≤ index := by omega
                have hNone : values[index]? = none :=
                  Array.getElem?_eq_none_iff.mpr (by omega)
                simp [hOutside, hNone]
    rw [hValues]
    exact buildMaxHeapRecursive_correct_quint
      values[0]! values[1]! values[2]! values[3]! values[4]!

/-- 長さ6以下の任意配列は、再帰版ヒープ構築後に最大ヒープ条件を満たす。 -/
theorem buildMaxHeapRecursive_correct_of_size_le_six (values : Array Nat)
    (hSize : values.size ≤ 6) :
    HeapBuildCorrect values (LeanExperiments.HeapSort.buildMaxHeapRecursive values) := by
  by_cases hSmall : values.size ≤ 5
  · exact buildMaxHeapRecursive_correct_of_size_le_five values hSmall
  · have hSizeEq : values.size = 6 := by omega
    have hValues : values =
        #[values[0]!, values[1]!, values[2]!, values[3]!, values[4]!, values[5]!] := by
      apply Array.ext_getElem?
      intro index
      by_cases hZero : index = 0
      · subst index
        simp [hSizeEq]
      · by_cases hOne : index = 1
        · subst index
          simp [hSizeEq]
        · by_cases hTwo : index = 2
          · subst index
            simp [hSizeEq]
          · by_cases hThree : index = 3
            · subst index
              simp [hSizeEq]
            · by_cases hFour : index = 4
              · subst index
                simp [hSizeEq]
              · by_cases hFive : index = 5
                · subst index
                  simp [hSizeEq]
                · have hOutside : 6 ≤ index := by omega
                  have hNone : values[index]? = none :=
                    Array.getElem?_eq_none_iff.mpr (by omega)
                  simp [hOutside, hNone]
    rw [hValues]
    exact buildMaxHeapRecursive_correct_sext
      values[0]! values[1]! values[2]! values[3]! values[4]! values[5]!

/-- 長さ7以下の任意配列は、再帰版ヒープ構築後に最大ヒープ条件を満たす。 -/
theorem buildMaxHeapRecursive_correct_of_size_le_seven (values : Array Nat)
    (hSize : values.size ≤ 7) :
    HeapBuildCorrect values (LeanExperiments.HeapSort.buildMaxHeapRecursive values) := by
  by_cases hSmall : values.size ≤ 6
  · exact buildMaxHeapRecursive_correct_of_size_le_six values hSmall
  · have hSizeEq : values.size = 7 := by omega
    have hValues : values =
        #[values[0]!, values[1]!, values[2]!, values[3]!, values[4]!, values[5]!,
          values[6]!] := by
      apply Array.ext_getElem?
      intro index
      by_cases hZero : index = 0
      · subst index
        simp [hSizeEq]
      · by_cases hOne : index = 1
        · subst index
          simp [hSizeEq]
        · by_cases hTwo : index = 2
          · subst index
            simp [hSizeEq]
          · by_cases hThree : index = 3
            · subst index
              simp [hSizeEq]
            · by_cases hFour : index = 4
              · subst index
                simp [hSizeEq]
              · by_cases hFive : index = 5
                · subst index
                  simp [hSizeEq]
                · by_cases hSix : index = 6
                  · subst index
                    simp [hSizeEq]
                  · have hOutside : 7 ≤ index := by omega
                    have hNone : values[index]? = none :=
                      Array.getElem?_eq_none_iff.mpr (by omega)
                    simp [hOutside, hNone]
    rw [hValues]
    exact buildMaxHeapRecursive_correct_sept
      values[0]! values[1]! values[2]! values[3]! values[4]! values[5]! values[6]!

/-- 長さ8以下の任意配列は、再帰版ヒープ構築後に最大ヒープ条件を満たす。 -/
theorem buildMaxHeapRecursive_correct_of_size_le_eight (values : Array Nat)
    (hSize : values.size ≤ 8) :
    HeapBuildCorrect values (LeanExperiments.HeapSort.buildMaxHeapRecursive values) := by
  by_cases hSmall : values.size ≤ 7
  · exact buildMaxHeapRecursive_correct_of_size_le_seven values hSmall
  · have hSizeEq : values.size = 8 := by omega
    have hValues := array_eq_index_values_of_size_eq_eight values hSizeEq
    rw [hValues]
    exact buildMaxHeapRecursive_correct_oct
      values[0]! values[1]! values[2]! values[3]! values[4]! values[5]!
      values[6]! values[7]!

/-- 長さ9以下で根が入力最大値なら、再帰版ヒープ構築は最大ヒープを返す。

長さ8以下では根の条件は不要であり、長さ9の場合にだけ追加の根最大条件を使う。
-/
theorem buildMaxHeapRecursive_correct_of_size_le_nine_of_root_maximum
    (input : Array Nat) (hSize : input.size ≤ 9)
    (hRootMaximum : ∀ value, value ∈ input.toList → value ≤ input[0]!) :
    HeapBuildCorrect input (LeanExperiments.HeapSort.buildMaxHeapRecursive input) := by
  by_cases hSmall : input.size ≤ 8
  · exact buildMaxHeapRecursive_correct_of_size_le_eight input hSmall
  · have hSizeEq : input.size = 9 := by omega
    exact buildMaxHeapRecursive_correct_of_size_eq_nine_of_root_maximum
      input hSizeEq hRootMaximum

/-- 長さ9以下で最後の根下降が固定点なら、再帰版ヒープ構築は最大ヒープを返す。

長さ8以下では無条件の構築定理を使い、長さ9の場合だけ根段階の比較条件を用いる。
-/
theorem buildMaxHeapRecursive_correct_of_size_le_nine_of_root_step
    (input : Array Nat) (hSize : input.size ≤ 9)
    (hRootStep :
      let stage3 := LeanExperiments.HeapSort.siftDownRecursive input 3
      let stage2 := LeanExperiments.HeapSort.siftDownRecursive stage3 2
      let stage1 := LeanExperiments.HeapSort.siftDownRecursive stage2 1
      stage1[1]! ≤ stage1[0]! ∧ stage1[2]! ≤ stage1[0]!) :
    HeapBuildCorrect input (LeanExperiments.HeapSort.buildMaxHeapRecursive input) := by
  by_cases hSmall : input.size ≤ 8
  · exact buildMaxHeapRecursive_correct_of_size_le_eight input hSmall
  · have hSizeEq : input.size = 9 := by omega
    exact buildMaxHeapRecursive_correct_of_size_eq_nine_of_root_step
      input hSizeEq hRootStep

/-- すでに最大ヒープである入力に対し、再帰版構築は `HeapBuildCorrect` を満たす。

固定点性によりヒープ条件を保ち、任意入力の順列保存定理により要素を保存する。
-/
theorem buildMaxHeapRecursive_correct_of_maxHeapInput (input : Array Nat)
    (hHeap : MaxHeap input) :
    HeapBuildCorrect input (LeanExperiments.HeapSort.buildMaxHeapRecursive input) := by
  rw [buildMaxHeapRecursive_eq_self_of_maxHeap input hHeap]
  exact ⟨hHeap, List.Perm.refl _⟩

/-- 構築後仕様を最大ヒープ検査と要素保存検査で計算する。 -/
def heapBuildCheck (input heap : Array Nat) : Bool :=
  maxHeapCheck heap && heap.toList.isPerm input.toList

/-- 構築後の Boolean 検査は論理仕様と同値である。 -/
theorem heapBuildCheck_correct (input heap : Array Nat) :
    heapBuildCheck input heap = true ↔ HeapBuildCorrect input heap := by
  unfold heapBuildCheck HeapBuildCorrect
  rw [Bool.and_eq_true, maxHeapCheck_correct, List.isPerm_iff]

/-- 再帰版ヒープ構築の出力は、独立した Boolean 検査器に必ず合格する。 -/
theorem heapBuildCheck_buildMaxHeapRecursive (input : Array Nat) :
    heapBuildCheck input (LeanExperiments.HeapSort.buildMaxHeapRecursive input) = true :=
  (heapBuildCheck_correct input _).2 (buildMaxHeapRecursive_correct input)

/-- ループ版ヒープ構築の出力も、任意入力で独立した Boolean 検査器に合格する。 -/
theorem heapBuildCheck_buildMaxHeap (input : Array Nat) :
    heapBuildCheck input (LeanExperiments.HeapSort.buildMaxHeap input) = true :=
  (heapBuildCheck_correct input _).2 (buildMaxHeap_correct input)

/-- ヒープ構築仕様から、配列の長さが変わらないことを導く。 -/
theorem HeapBuildCorrect.size_eq {input heap : Array Nat}
    (hCorrect : HeapBuildCorrect input heap) : heap.size = input.size := by
  have hLength := hCorrect.2.length_eq
  simpa only [Array.length_toList] using hLength

/-- ヒープ構築仕様から、配列内の値の合計が保存されることを導く。 -/
theorem HeapBuildCorrect.sum_eq {input heap : Array Nat}
    (hCorrect : HeapBuildCorrect input heap) :
    heap.toList.sum = input.toList.sum := hCorrect.2.sum_nat

/-- 正しいヒープ構築結果では、根が配列内の全ての値以上である。 -/
theorem HeapBuildCorrect.root_is_maximum {input heap : Array Nat}
    (hCorrect : HeapBuildCorrect input heap) :
    ∀ index, index < heap.size → heap[index]! ≤ heap[0]! := by
  exact hCorrect.1.le_root

/-- 正しいヒープ構築結果の根の値は、重複を含む形で入力にも現れる。 -/
theorem HeapBuildCorrect.root_mem_input {input heap : Array Nat}
    (hCorrect : HeapBuildCorrect input heap) (hNonempty : 0 < heap.size) :
    heap[0]! ∈ input.toList := by
  have hRootMem : heap[0]! ∈ heap.toList := by
    simp [hNonempty]
  exact hCorrect.2.mem_iff.mp hRootMem

/-- 正しいヒープ構築結果の根は入力の全要素以上である。 -/
theorem HeapBuildCorrect.root_is_maximum_of_input {input heap : Array Nat}
    (hCorrect : HeapBuildCorrect input heap) :
    ∀ value, value ∈ input.toList → value ≤ heap[0]! := by
  intro value hValue
  have hValueHeapList : value ∈ heap.toList := hCorrect.2.mem_iff.mpr hValue
  have hValueHeap : value ∈ heap := Array.mem_toList_iff.mp hValueHeapList
  obtain ⟨index, hIndex, hIndexValue⟩ := Array.mem_iff_getElem.mp hValueHeap
  have hRootMaximum := hCorrect.root_is_maximum index hIndex
  have hIndexBang : heap[index]! = value := by
    rw [getElem!_pos heap index hIndex]
    exact hIndexValue
  rw [← hIndexBang]
  exact hRootMaximum

/-- Boolean のヒープ構築検査に合格すれば、配列の長さが保存される。 -/
theorem heapBuildCheck_size_eq (input heap : Array Nat)
    (hCheck : heapBuildCheck input heap = true) : heap.size = input.size :=
  HeapBuildCorrect.size_eq ((heapBuildCheck_correct input heap).mp hCheck)

/-- Boolean のヒープ構築検査に合格すれば、値の合計が保存される。 -/
theorem heapBuildCheck_sum_eq (input heap : Array Nat)
    (hCheck : heapBuildCheck input heap = true) :
    heap.toList.sum = input.toList.sum :=
  HeapBuildCorrect.sum_eq ((heapBuildCheck_correct input heap).mp hCheck)

/-- 最大値取り出し関数 `extract` の残余ヒープと保存要素を表す仕様。 -/
def PopMaxRestCorrectFor
    (extract : Array Nat → Option (Nat × Array Nat)) (heap : Array Nat) : Prop :=
  match extract heap with
  | none => heap.isEmpty = true
  | some (maximum, rest) =>
      0 < heap.size ∧ heap[0]? = some maximum ∧ MaxHeap rest ∧
        rest.toList.Perm (heap.toList.drop 1)

/-- 最大値抽出の順序仕様。残余がヒープであることを要求せず、抽出値と残余の順序を表す。 -/
def PopMaxOrderCorrectFor
    (extract : Array Nat → Option (Nat × Array Nat)) (heap : Array Nat) : Prop :=
  match extract heap with
  | none => heap.isEmpty = true
  | some (maximum, rest) =>
      0 < heap.size ∧ heap[0]? = some maximum ∧
        (∀ value, value ∈ rest.toList → value ≤ maximum) ∧
        rest.toList.Perm (heap.toList.drop 1)

/-- 抽出の要素保存とサイズ減少だけを切り出した仕様。 -/
def PopMaxElementsCorrectFor
    (extract : Array Nat → Option (Nat × Array Nat)) (heap : Array Nat) : Prop :=
  match extract heap with
  | none => heap.size = 0
  | some (maximum, rest) =>
      rest.size + 1 = heap.size ∧ (maximum :: rest.toList).Perm heap.toList

/-- 抽出の要素保存契約から、任意述語に対する要素数保存を取り出す。

失敗時は入力が空であり、成功時は取り出した値と残余配列を合わせた要素数が入力と一致する。
-/
theorem PopMaxElementsCorrectFor.countP
    (extract : Array Nat → Option (Nat × Array Nat)) (heap : Array Nat)
    (hCorrect : PopMaxElementsCorrectFor extract heap) (predicate : Nat → Bool) :
    match extract heap with
    | none => heap.toList.countP predicate = 0
    | some (maximum, rest) =>
        (maximum :: rest.toList).countP predicate = heap.toList.countP predicate := by
  cases hExtract : extract heap with
  | none =>
      simp only [PopMaxElementsCorrectFor, hExtract] at hCorrect
      have hEmpty : heap.size = 0 := hCorrect
      have hListEmpty : heap.toList = [] := List.eq_nil_of_length_eq_zero (by
        simpa [Array.length_toList] using hEmpty)
      simp [hListEmpty]
  | some result =>
      cases result with
      | mk maximum rest =>
          simp only [PopMaxElementsCorrectFor, hExtract] at hCorrect
          have hPerm : (maximum :: rest.toList).Perm heap.toList := by
            exact hCorrect.2
          exact hPerm.countP_eq predicate

/-- 抽出のサイズ減少と要素保存だけを計算で確認する Boolean 検査器。 -/
def popMaxElementsCheckFor
    (extract : Array Nat → Option (Nat × Array Nat)) (heap : Array Nat) : Bool :=
  match extract heap with
  | none => decide (heap.size = 0)
  | some (maximum, rest) =>
      decide (rest.size + 1 = heap.size) &&
        (maximum :: rest.toList).isPerm heap.toList

/-- 要素保存の Boolean 検査器は、その論理契約と同値である。 -/
theorem popMaxElementsCheckFor_correct
    (extract : Array Nat → Option (Nat × Array Nat)) (heap : Array Nat) :
    popMaxElementsCheckFor extract heap = true ↔
      PopMaxElementsCorrectFor extract heap := by
  cases hExtract : extract heap with
  | none =>
      simp [popMaxElementsCheckFor, PopMaxElementsCorrectFor, hExtract]
  | some result =>
      cases result with
      | mk maximum rest =>
          simp [popMaxElementsCheckFor, PopMaxElementsCorrectFor, hExtract,
            Bool.and_eq_true, List.isPerm_iff]

/-- 再帰版 `popMax` は、ヒープ性に関係なくサイズと要素保存の契約を満たす。 -/
theorem popMaxRecursive_elements_correct_for_all (heap : Array Nat) :
    PopMaxElementsCorrectFor LeanExperiments.HeapSort.popMaxRecursive heap := by
  cases hExtract : LeanExperiments.HeapSort.popMaxRecursive heap with
  | none =>
      have hEmpty := (popMaxRecursive_eq_none_iff_empty heap).mp hExtract
      simpa [PopMaxElementsCorrectFor, hExtract] using hEmpty
  | some result =>
      cases result with
      | mk maximum rest =>
          have hPop : LeanExperiments.HeapSort.popMaxRecursive heap =
              some (maximum, rest) := hExtract
          have hSize := popMaxRecursive_size hPop
          have hRoot := popMaxRecursive_value_eq_root hPop
          have hDropPerm := popMaxRecursive_rest_perm_dropRoot hPop
          have hPositive : 0 < heap.size := by omega
          have hRootValue : heap[0] = maximum := by
            rw [getElem?_pos heap 0 hPositive] at hRoot
            injection hRoot with hEq
          have hHead : heap.toList[0]'(by simp [Array.length_toList]; omega) = maximum := by
            simpa only [Array.getElem_toList] using hRootValue
          have hDecompose : maximum :: heap.toList.drop 1 = heap.toList := by
            have hListDecompose := List.getElem_cons_drop
              (as := heap.toList) (i := 0) (by simp [Array.length_toList]; omega)
            simpa [hHead] using hListDecompose
          have hConsPerm : (maximum :: rest.toList).Perm heap.toList := by
            have hPerm := hDropPerm.cons maximum
            rw [hDecompose] at hPerm
            exact hPerm
          simpa [PopMaxElementsCorrectFor, hExtract] using
            (And.intro hSize hConsPerm)

/-- ループ版 `popMax` も全ての配列でサイズと要素保存の契約を満たす。 -/
theorem popMax_elements_correct_for_all (heap : Array Nat) :
    PopMaxElementsCorrectFor LeanExperiments.HeapSort.popMax heap := by
  unfold PopMaxElementsCorrectFor
  rw [popMax_eq_popMaxRecursive]
  exact popMaxRecursive_elements_correct_for_all heap

/-- 再帰版 `popMax` は、抽出値と残余を合わせた任意分類の個数を保存する。

空配列では結果が `none` で入力の個数も0、非空配列では返却値を残余の先頭に加えた列が
入力と同じ個数を持つ。ヒープ順序を仮定せず、任意の配列に適用できる。
-/
theorem popMaxRecursive_countP (heap : Array Nat) (predicate : Nat → Bool) :
    match LeanExperiments.HeapSort.popMaxRecursive heap with
    | none => heap.toList.countP predicate = 0
    | some (maximum, rest) =>
        (maximum :: rest.toList).countP predicate = heap.toList.countP predicate := by
  exact PopMaxElementsCorrectFor.countP LeanExperiments.HeapSort.popMaxRecursive heap
    (popMaxRecursive_elements_correct_for_all heap) predicate

/-- ループ版 `popMax` は、抽出値と残余を合わせた任意分類の個数を保存する。 -/
theorem popMax_countP (heap : Array Nat) (predicate : Nat → Bool) :
    match LeanExperiments.HeapSort.popMax heap with
    | none => heap.toList.countP predicate = 0
    | some (maximum, rest) =>
        (maximum :: rest.toList).countP predicate = heap.toList.countP predicate := by
  exact PopMaxElementsCorrectFor.countP LeanExperiments.HeapSort.popMax heap
    (popMax_elements_correct_for_all heap) predicate

/-- ループ版 `popMax` の要素保存検査器は、任意の配列で合格する。 -/
theorem popMaxElementsCheck_all (heap : Array Nat) :
    popMaxElementsCheckFor LeanExperiments.HeapSort.popMax heap = true :=
  (popMaxElementsCheckFor_correct LeanExperiments.HeapSort.popMax heap).2
    (popMax_elements_correct_for_all heap)

/-- 再帰版 `popMax` のサイズ減少・要素保存を確認する Boolean 検査器。 -/
def popMaxRecursiveElementsCheck (heap : Array Nat) : Bool :=
  popMaxElementsCheckFor LeanExperiments.HeapSort.popMaxRecursive heap

/-- 再帰版の要素保存検査器は、その一般論理契約と同値である。 -/
theorem popMaxRecursiveElementsCheck_correct (heap : Array Nat) :
    popMaxRecursiveElementsCheck heap = true ↔
      PopMaxElementsCorrectFor LeanExperiments.HeapSort.popMaxRecursive heap :=
  popMaxElementsCheckFor_correct LeanExperiments.HeapSort.popMaxRecursive heap

/-- 再帰版 `popMax` の要素保存検査器は、任意の配列で合格する。 -/
theorem popMaxRecursiveElementsCheck_all (heap : Array Nat) :
    popMaxRecursiveElementsCheck heap = true :=
  popMaxRecursiveElementsCheck_correct heap |>.2
    (popMaxRecursive_elements_correct_for_all heap)

/-- 再帰版 `popMax` は、取り出した値と残余配列の総和を保存する。

空ヒープでは取り出しが失敗し、非空ヒープでは要素保存の一般契約から従う。
-/
theorem popMaxRecursive_sum (heap : Array Nat) :
    match LeanExperiments.HeapSort.popMaxRecursive heap with
    | none => heap.toList.sum = 0
    | some (maximum, rest) => maximum + rest.toList.sum = heap.toList.sum := by
  cases hExtract : LeanExperiments.HeapSort.popMaxRecursive heap with
  | none =>
      have hEmpty := (popMaxRecursive_eq_none_iff_empty heap).mp hExtract
      have hArray : heap = #[] := Array.size_eq_zero_iff.mp hEmpty
      simp [hArray]
  | some result =>
      cases result with
      | mk maximum rest =>
          have hElements := popMaxRecursive_elements_correct_for_all heap
          simp [PopMaxElementsCorrectFor, hExtract] at hElements
          have hSum := hElements.2.sum_nat
          simpa using hSum

/-- 残余仕様を満たす取り出し値は、入力ヒープの根に一致する。 -/
theorem PopMaxRestCorrectFor.value_eq_root
    {extract : Array Nat → Option (Nat × Array Nat)} {heap : Array Nat}
    (hCorrect : PopMaxRestCorrectFor extract heap) :
    match extract heap with
    | none => True
    | some (maximum, _) => heap[0]? = some maximum := by
  cases hExtract : extract heap with
  | none => trivial
  | some result =>
      cases result with
      | mk maximum rest =>
          have hSuccess :
              0 < heap.size ∧ heap[0]? = some maximum ∧ MaxHeap rest ∧
                rest.toList.Perm (heap.toList.drop 1) := by
            simpa [PopMaxRestCorrectFor, hExtract] using hCorrect
          exact hSuccess.2.1

/-- 最大ヒープから残余仕様どおりに取り出す値は、入力中の全要素以上となる。 -/
theorem PopMaxRestCorrectFor.value_is_maximum
    {extract : Array Nat → Option (Nat × Array Nat)} {heap : Array Nat}
    (hCorrect : PopMaxRestCorrectFor extract heap) (hHeap : MaxHeap heap) :
    match extract heap with
    | none => True
    | some (maximum, _) =>
        ∀ index, index < heap.size → heap[index]! ≤ maximum := by
  cases hExtract : extract heap with
  | none => trivial
  | some result =>
      cases result with
      | mk maximum rest =>
          have hRoot : heap[0]? = some maximum := by
            simpa [hExtract] using PopMaxRestCorrectFor.value_eq_root hCorrect
          simpa [hExtract] using root_value_is_maximum hHeap hRoot

/-- 正しい最大値取り出しでは、残った全要素が取り出した値以下である。 -/
theorem PopMaxRestCorrectFor.rest_le_maximum
    {extract : Array Nat → Option (Nat × Array Nat)} {heap : Array Nat}
    (hCorrect : PopMaxRestCorrectFor extract heap) (hHeap : MaxHeap heap) :
    match extract heap with
    | none => True
    | some (maximum, rest) => ∀ value ∈ rest.toList, value ≤ maximum := by
  cases hExtract : extract heap with
  | none => trivial
  | some result =>
      cases result with
      | mk maximum rest =>
          have hSuccess :
              0 < heap.size ∧ heap[0]? = some maximum ∧ MaxHeap rest ∧
                rest.toList.Perm (heap.toList.drop 1) := by
            simpa [PopMaxRestCorrectFor, hExtract] using hCorrect
          have hMaximum : ∀ index, index < heap.size → heap[index]! ≤ maximum := by
            simpa [hExtract] using
              PopMaxRestCorrectFor.value_is_maximum hCorrect hHeap
          intro value hValueRest
          have hValueTail := hSuccess.2.2.2.mem_iff.mp hValueRest
          have hValueHeap := List.mem_of_mem_drop hValueTail
          obtain ⟨index, hIndex, hValue⟩ := List.mem_iff_getElem.mp hValueHeap
          have hIndexArray : index < heap.size := by
            simpa [Array.length_toList] using hIndex
          have hBound := hMaximum index hIndexArray
          have hValueArray : heap[index] = value := by
            simpa only [Array.getElem_toList] using hValue
          rw [getElem!_pos heap index hIndexArray, hValueArray] at hBound
          exact hBound

/-- 残余ヒープまで正しい抽出契約は、入力ヒープ上で順序仕様を含意する。 -/
theorem PopMaxRestCorrectFor.orderCorrect
    {extract : Array Nat → Option (Nat × Array Nat)} {heap : Array Nat}
    (hCorrect : PopMaxRestCorrectFor extract heap) (hHeap : MaxHeap heap) :
    PopMaxOrderCorrectFor extract heap := by
  cases hExtract : extract heap with
  | none =>
      have hEmpty : heap.isEmpty = true := by
        simpa [PopMaxRestCorrectFor, hExtract] using hCorrect
      simpa [PopMaxOrderCorrectFor, hExtract] using hEmpty
  | some result =>
      cases result with
      | mk maximum rest =>
          have hSuccess :
              0 < heap.size ∧ heap[0]? = some maximum ∧ MaxHeap rest ∧
                rest.toList.Perm (heap.toList.drop 1) := by
            simpa [PopMaxRestCorrectFor, hExtract] using hCorrect
          have hOrder : ∀ value, value ∈ rest.toList → value ≤ maximum := by
            simpa [hExtract] using
              PopMaxRestCorrectFor.rest_le_maximum hCorrect hHeap
          simpa [PopMaxOrderCorrectFor, hExtract] using
            (And.intro hSuccess.1
              (And.intro hSuccess.2.1
                (And.intro hOrder hSuccess.2.2.2)))

/-- 続けてもう一度最大値を取り出すと、その値は直前の取り出し値以下である。 -/
theorem PopMaxRestCorrectFor.next_value_le
    {extract : Array Nat → Option (Nat × Array Nat)} {heap : Array Nat}
    (hCorrect : PopMaxRestCorrectFor extract heap) (hHeap : MaxHeap heap)
    (hCorrectForRest : ∀ rest, PopMaxRestCorrectFor extract rest) :
    match extract heap with
    | none => True
    | some (maximum, rest) =>
        match extract rest with
        | none => True
        | some (next, _) => next ≤ maximum := by
  cases hExtract : extract heap with
  | none => simp
  | some result =>
      cases result with
      | mk maximum rest =>
          change match extract rest with
            | none => True
            | some (next, _) => next ≤ maximum
          cases hNextExtract : extract rest with
          | none => simp
          | some nextResult =>
              cases nextResult with
              | mk next nextRest =>
                  change next ≤ maximum
                  have hRestBound : ∀ value ∈ rest.toList, value ≤ maximum := by
                    simpa [hExtract] using
                      PopMaxRestCorrectFor.rest_le_maximum hCorrect hHeap
                  have hNextRoot : rest[0]? = some next := by
                    simpa [hNextExtract] using
                      PopMaxRestCorrectFor.value_eq_root
                        (hCorrectForRest rest)
                  obtain ⟨hRootIndex, hRootValue⟩ :=
                    Array.getElem?_eq_some_iff.mp hNextRoot
                  have hRootMem : next ∈ rest.toList :=
                    Array.mem_toList_iff.mpr
                      (Array.mem_iff_getElem.mpr ⟨0, hRootIndex, hRootValue⟩)
                  exact hRestBound next hRootMem

/-- 残余仕様から、失敗時の空性と成功時の要素数減少を一般に導く。 -/
theorem PopMaxRestCorrectFor.size
    {extract : Array Nat → Option (Nat × Array Nat)} {heap : Array Nat}
    (hCorrect : PopMaxRestCorrectFor extract heap) :
    match extract heap with
    | none => heap.size = 0
    | some (_, rest) => rest.size + 1 = heap.size := by
  cases hExtract : extract heap with
  | none =>
      simp [PopMaxRestCorrectFor, hExtract] at hCorrect
      have hEmpty : heap = #[] := by
        simpa [Array.isEmpty_iff] using hCorrect
      simp [hEmpty]
  | some result =>
      cases result with
      | mk maximum rest =>
          simp [PopMaxRestCorrectFor, hExtract] at hCorrect
          have hLength := hCorrect.2.2.2.length_eq
          rw [List.length_tail] at hLength
          simp only [Array.length_toList] at hLength
          omega

/-- 同じ入力で残余仕様を満たす抽出関数は、成否と返却最大値が一致する。 -/
theorem PopMaxRestCorrectFor.maximum_eq
    {extract₁ extract₂ : Array Nat → Option (Nat × Array Nat)} {heap : Array Nat}
    (hCorrect₁ : PopMaxRestCorrectFor extract₁ heap)
    (hCorrect₂ : PopMaxRestCorrectFor extract₂ heap) :
    (extract₁ heap).map Prod.fst = (extract₂ heap).map Prod.fst := by
  cases hExtract₁ : extract₁ heap with
  | none =>
      cases hExtract₂ : extract₂ heap with
      | none => rfl
      | some result =>
          cases result with
          | mk maximum rest =>
              have hSize₁ : heap.size = 0 := by
                simpa [hExtract₁] using PopMaxRestCorrectFor.size hCorrect₁
              have hSize₂ : rest.size + 1 = heap.size := by
                simpa [hExtract₂] using PopMaxRestCorrectFor.size hCorrect₂
              have hFalse : False := by omega
              exact hFalse.elim
  | some result₁ =>
      cases result₁ with
      | mk maximum₁ rest₁ =>
          cases hExtract₂ : extract₂ heap with
          | none =>
              have hSize₁ : rest₁.size + 1 = heap.size := by
                simpa [hExtract₁] using PopMaxRestCorrectFor.size hCorrect₁
              have hSize₂ : heap.size = 0 := by
                simpa [hExtract₂] using PopMaxRestCorrectFor.size hCorrect₂
              have hFalse : False := by omega
              exact hFalse.elim
          | some result₂ =>
              cases result₂ with
              | mk maximum₂ rest₂ =>
                  have hRoot₁ : heap[0]? = some maximum₁ := by
                    simpa [hExtract₁] using
                      PopMaxRestCorrectFor.value_eq_root hCorrect₁
                  have hRoot₂ : heap[0]? = some maximum₂ := by
                    simpa [hExtract₂] using
                      PopMaxRestCorrectFor.value_eq_root hCorrect₂
                  have hMaximum : maximum₁ = maximum₂ := by
                    rw [hRoot₁] at hRoot₂
                    injection hRoot₂
                  simp [hMaximum]

/-- 同じ入力ヒープで残余仕様を満たす抽出結果は、残余の要素を順列として保つ。

失敗する場合はヒープが空であり、成功する場合は両方の残余が元のヒープから
根を除いた同じ列と順列になる。従って、抽出実装による残余配列の並び方が異なっても、
取り出し後に残る要素の重複度は一致する。
-/
theorem PopMaxRestCorrectFor.rest_perm
    {extract₁ extract₂ : Array Nat → Option (Nat × Array Nat)} {heap : Array Nat}
    (hCorrect₁ : PopMaxRestCorrectFor extract₁ heap)
    (hCorrect₂ : PopMaxRestCorrectFor extract₂ heap) :
    match extract₁ heap, extract₂ heap with
    | none, none => True
    | some (_, rest₁), some (_, rest₂) => rest₁.toList.Perm rest₂.toList
    | _, _ => False := by
  cases hExtract₁ : extract₁ heap with
  | none =>
      cases hExtract₂ : extract₂ heap with
      | none => simp
      | some result₂ =>
          cases result₂ with
          | mk maximum₂ rest₂ =>
              have hEmpty : heap.size = 0 := by
                simpa [hExtract₁] using PopMaxRestCorrectFor.size hCorrect₁
              have hRestSize : rest₂.size + 1 = heap.size := by
                simpa [hExtract₂] using PopMaxRestCorrectFor.size hCorrect₂
              have hFalse : False := by omega
              exact hFalse.elim
  | some result₁ =>
      cases result₁ with
      | mk maximum₁ rest₁ =>
          cases hExtract₂ : extract₂ heap with
          | none =>
              have hRestSize : rest₁.size + 1 = heap.size := by
                simpa [hExtract₁] using PopMaxRestCorrectFor.size hCorrect₁
              have hEmpty : heap.size = 0 := by
                simpa [hExtract₂] using PopMaxRestCorrectFor.size hCorrect₂
              have hFalse : False := by omega
              exact hFalse.elim
          | some result₂ =>
              cases result₂ with
              | mk maximum₂ rest₂ =>
                  have hSuccess₁ :
                      0 < heap.size ∧ heap[0]? = some maximum₁ ∧ MaxHeap rest₁ ∧
                        rest₁.toList.Perm (heap.toList.drop 1) := by
                    simpa [PopMaxRestCorrectFor, hExtract₁] using hCorrect₁
                  have hSuccess₂ :
                      0 < heap.size ∧ heap[0]? = some maximum₂ ∧ MaxHeap rest₂ ∧
                        rest₂.toList.Perm (heap.toList.drop 1) := by
                    simpa [PopMaxRestCorrectFor, hExtract₂] using hCorrect₂
                  exact hSuccess₁.2.2.2.trans hSuccess₂.2.2.2.symm

/-- 残余仕様があれば、取り出した値と残余配列を合わせて入力要素を重複込みで保存する。 -/
theorem PopMaxRestCorrectFor.perm_cons
    {extract : Array Nat → Option (Nat × Array Nat)} {heap : Array Nat}
    (hCorrect : PopMaxRestCorrectFor extract heap) :
    match extract heap with
    | none => True
    | some (maximum, rest) => (maximum :: rest.toList).Perm heap.toList := by
  cases hExtract : extract heap with
  | none => trivial
  | some result =>
      cases result with
      | mk maximum rest =>
          have hSuccess :
              0 < heap.size ∧ heap[0]? = some maximum ∧ MaxHeap rest ∧
                rest.toList.Perm (heap.toList.drop 1) := by
            simpa [PopMaxRestCorrectFor, hExtract] using hCorrect
          have hHead : heap.toList[0]'(by simp [Array.length_toList]; omega) = maximum := by
            have hRoot := hSuccess.2.1
            rw [getElem?_pos heap 0 (by omega)] at hRoot
            have hValue : heap[0] = maximum := by injection hRoot
            simpa only [Array.getElem_toList] using hValue
          have hDecompose : maximum :: heap.toList.drop 1 = heap.toList := by
            have hListDecompose := List.getElem_cons_drop
              (as := heap.toList) (i := 0) (by simp [Array.length_toList]; omega)
            simpa [hHead] using hListDecompose
          have hPerm := List.Perm.cons maximum hSuccess.2.2.2
          rw [hDecompose] at hPerm
          exact hPerm

/-- 仕様を満たす抽出関数を最大ヒープへ繰り返し適用し、値を取り出す。 -/
def extractMaxima (extract : Array Nat → Option (Nat × Array Nat)) :
    Nat → Array Nat → List Nat
  | 0, _ => []
  | fuel + 1, heap =>
      match extract heap with
      | none => []
      | some (maximum, rest) => maximum :: extractMaxima extract fuel rest

/-- 1段階の抽出が入力最大値を返し、残りの要素を順列として保つ仕様。 -/
def PopMaxOrderedCorrectFor
    (extract : Array Nat → Option (Nat × Array Nat)) (heap : Array Nat) : Prop :=
  match extract heap with
  | none => heap.size = 0
  | some (maximum, rest) =>
      (maximum :: rest.toList).Perm heap.toList ∧
        (∀ value, value ∈ heap.toList → value ≤ maximum)

/-- 最大値順序抽出仕様を、要素保存と最大値境界で独立に検査する。 -/
def popMaxOrderedCheckFor
    (extract : Array Nat → Option (Nat × Array Nat)) (heap : Array Nat) : Bool :=
  match extract heap with
  | none => decide (heap.size = 0)
  | some (maximum, rest) =>
      (maximum :: rest.toList).isPerm heap.toList &&
        decide (∀ value, value ∈ heap.toList → value ≤ maximum)

/-- 順序抽出検査器が成功することと、1段階の論理契約は同値である。 -/
theorem popMaxOrderedCheckFor_correct
    (extract : Array Nat → Option (Nat × Array Nat)) (heap : Array Nat) :
    popMaxOrderedCheckFor extract heap = true ↔
      PopMaxOrderedCorrectFor extract heap := by
  cases hExtract : extract heap with
  | none => simp [popMaxOrderedCheckFor, PopMaxOrderedCorrectFor, hExtract]
  | some result =>
      cases result with
      | mk maximum rest =>
          simp [popMaxOrderedCheckFor, PopMaxOrderedCorrectFor, hExtract,
            Bool.and_eq_true, List.isPerm_iff]

/-- 最大値抽出の順序仕様は、サイズ減少と要素保存も含意する。 -/
theorem PopMaxOrderedCorrectFor.elementsCorrect
    {extract : Array Nat → Option (Nat × Array Nat)} {heap : Array Nat}
    (hCorrect : PopMaxOrderedCorrectFor extract heap) :
    PopMaxElementsCorrectFor extract heap := by
  cases hExtract : extract heap with
  | none =>
      simpa [PopMaxOrderedCorrectFor, PopMaxElementsCorrectFor, hExtract] using hCorrect
  | some result =>
      cases result with
      | mk maximum rest =>
          have hSuccess :
              (maximum :: rest.toList).Perm heap.toList ∧
                (∀ value, value ∈ heap.toList → value ≤ maximum) := by
            simpa [PopMaxOrderedCorrectFor, hExtract] using hCorrect
          have hPerm : (maximum :: rest.toList).Perm heap.toList := hSuccess.1
          have hListLength := hPerm.length_eq
          have hSize : rest.size + 1 = heap.size := by
            simpa [List.length_cons, Array.length_toList] using hListLength
          simpa [PopMaxElementsCorrectFor, hExtract] using
            (And.intro hSize hPerm)

/-- 最大ヒープ上の再帰版 `popMax` は、残余ヒープ条件なしの1段階順序仕様を満たす。 -/
theorem popMaxRecursive_orderedCorrect_of_maxHeap (heap : Array Nat)
    (hHeap : MaxHeap heap) :
    PopMaxOrderedCorrectFor LeanExperiments.HeapSort.popMaxRecursive heap := by
  cases hPop : LeanExperiments.HeapSort.popMaxRecursive heap with
  | none =>
      have hEmpty := (popMaxRecursive_eq_none_iff_empty heap).mp hPop
      simpa [PopMaxOrderedCorrectFor, hPop] using hEmpty
  | some result =>
      cases result with
      | mk maximum rest =>
          have hElements := popMaxRecursive_elements_correct_for_all heap
          have hElementsSuccess :
              rest.size + 1 = heap.size ∧
                (maximum :: rest.toList).Perm heap.toList := by
            simpa [PopMaxElementsCorrectFor, hPop] using hElements
          have hPerm : (maximum :: rest.toList).Perm heap.toList := by
            exact hElementsSuccess.2
          have hGreatest := popMaxRecursive_returns_greatest_of_maxHeap hHeap hPop
          simpa [PopMaxOrderedCorrectFor, hPop] using
            (And.intro hPerm hGreatest.2)

/-- 再帰版 `popMax` の最大値順序検査器。 -/
def popMaxRecursiveOrderedCheck (heap : Array Nat) : Bool :=
  popMaxOrderedCheckFor LeanExperiments.HeapSort.popMaxRecursive heap

/-- 最大ヒープ入力に対する再帰版抽出は、最大値順序検査に合格する。 -/
theorem popMaxRecursiveOrderedCheck_of_maxHeap (heap : Array Nat)
    (hHeap : MaxHeap heap) :
    popMaxRecursiveOrderedCheck heap = true := by
  exact (popMaxOrderedCheckFor_correct
    LeanExperiments.HeapSort.popMaxRecursive heap).2
      (popMaxRecursive_orderedCorrect_of_maxHeap heap hHeap)

/-- 1段階最大抽出仕様を満たす関数では、反復抽出値は入力要素である。 -/
theorem extractMaxima_mem_of_orderedCorrect
    {extract : Array Nat → Option (Nat × Array Nat)}
    (hCorrectForAll : ∀ heap, PopMaxOrderedCorrectFor extract heap) :
    ∀ fuel heap value, value ∈ extractMaxima extract fuel heap → value ∈ heap.toList := by
  intro fuel
  induction fuel with
  | zero => simp [extractMaxima]
  | succ fuel ih =>
      intro heap value hValue
      cases hExtract : extract heap with
      | none => simp [extractMaxima, hExtract] at hValue
      | some result =>
          cases result with
          | mk maximum rest =>
              simp only [extractMaxima, hExtract, List.mem_cons] at hValue
              rcases hValue with hMaximum | hRestValue
              · subst value
                have hStep :
                    (maximum :: rest.toList).Perm heap.toList ∧
                      (∀ value, value ∈ heap.toList → value ≤ maximum) := by
                  simpa [PopMaxOrderedCorrectFor, hExtract] using hCorrectForAll heap
                exact hStep.1.mem_iff.mp (by simp)
              · have hRestMem := ih rest value hRestValue
                have hStep :
                    (maximum :: rest.toList).Perm heap.toList ∧
                      (∀ value, value ∈ heap.toList → value ≤ maximum) := by
                  simpa [PopMaxOrderedCorrectFor, hExtract] using hCorrectForAll heap
                exact hStep.1.mem_iff.mp (by simp [hRestMem])

/-- 1段階最大抽出仕様を満たす関数の反復抽出列は降順である。

この合成定理は、残余状態がヒープであることを仮定せず、各状態で最大値抽出仕様が
成立することだけを使う。
-/
theorem extractMaxima_pairwise_of_orderedCorrect
    {extract : Array Nat → Option (Nat × Array Nat)}
    (hCorrectForAll : ∀ heap, PopMaxOrderedCorrectFor extract heap) :
    ∀ fuel heap,
      (extractMaxima extract fuel heap).Pairwise (fun earlier later => later ≤ earlier) := by
  intro fuel
  induction fuel with
  | zero => intro heap; simp [extractMaxima]
  | succ fuel ih =>
      intro heap
      cases hExtract : extract heap with
      | none => simp [extractMaxima, hExtract]
      | some result =>
          cases result with
          | mk maximum rest =>
              have hStep :
                  (maximum :: rest.toList).Perm heap.toList ∧
                    (∀ value, value ∈ heap.toList → value ≤ maximum) := by
                simpa [PopMaxOrderedCorrectFor, hExtract] using hCorrectForAll heap
              have hTailSorted := ih rest
              simp only [extractMaxima, hExtract]
              change (maximum :: extractMaxima extract fuel rest).Pairwise
                (fun earlier later => later ≤ earlier)
              constructor
              · intro value hValue
                have hRestMem :=
                  extractMaxima_mem_of_orderedCorrect hCorrectForAll fuel rest value hValue
                have hInCons : value ∈ maximum :: rest.toList := by
                  simp [hRestMem]
                exact hStep.2 value (hStep.1.mem_iff.mp hInCons)
              · exact hTailSorted

/-- 繰り返し取り出した値は、最初のヒープに含まれる値である。 -/
theorem extractMaxima_mem
    {extract : Array Nat → Option (Nat × Array Nat)}
    (hCorrectForAll : ∀ heap, PopMaxRestCorrectFor extract heap) :
    ∀ fuel heap value, value ∈ extractMaxima extract fuel heap → value ∈ heap.toList := by
  intro fuel
  induction fuel with
  | zero => simp [extractMaxima]
  | succ fuel ih =>
      intro heap value hValue
      cases hExtract : extract heap with
      | none => simp [extractMaxima, hExtract] at hValue
      | some result =>
          cases result with
          | mk maximum rest =>
              simp only [extractMaxima, hExtract, List.mem_cons] at hValue
              rcases hValue with hIsMaximum | hInRest
              · subst value
                have hRoot : heap[0]? = some maximum := by
                  simpa [hExtract] using
                    PopMaxRestCorrectFor.value_eq_root (hCorrectForAll heap)
                exact Array.mem_toList_iff.mpr
                  (Array.mem_iff_getElem?.mpr ⟨0, hRoot⟩)
              · have hInRestList := ih rest value hInRest
                have hPerm : (maximum :: rest.toList).Perm heap.toList := by
                  simpa [hExtract] using
                    PopMaxRestCorrectFor.perm_cons (hCorrectForAll heap)
                have hInCons : value ∈ maximum :: rest.toList := by
                  simp [hInRestList]
                exact hPerm.mem_iff.mp hInCons

/-- 正しい抽出を繰り返すと、取り出し値は大きい順に並ぶ。 -/
theorem extractMaxima_pairwise
    {extract : Array Nat → Option (Nat × Array Nat)}
    (hCorrectForAll : ∀ heap, PopMaxRestCorrectFor extract heap) :
    ∀ fuel heap, MaxHeap heap →
      (extractMaxima extract fuel heap).Pairwise (fun earlier later => later ≤ earlier) := by
  intro fuel
  induction fuel with
  | zero => intro heap _; simp [extractMaxima]
  | succ fuel ih =>
      intro heap hHeap
      cases hExtract : extract heap with
      | none => simp [extractMaxima, hExtract]
      | some result =>
          cases result with
          | mk maximum rest =>
              have hSpec := hCorrectForAll heap
              have hSuccess :
                  0 < heap.size ∧ heap[0]? = some maximum ∧ MaxHeap rest ∧
                    rest.toList.Perm (heap.toList.drop 1) := by
                simpa [PopMaxRestCorrectFor, hExtract] using hSpec
              have hRestSorted := ih rest hSuccess.2.2.1
              have hMaximum := PopMaxRestCorrectFor.value_is_maximum hSpec hHeap
              have hMaximumBound : ∀ index, index < heap.size →
                  heap[index]! ≤ maximum := by
                simpa [hExtract] using hMaximum
              simp only [extractMaxima, hExtract]
              change (maximum :: extractMaxima extract fuel rest).Pairwise
                (fun earlier later => later ≤ earlier)
              apply List.Pairwise.cons
              · intro value hValue
                have hValueRest := extractMaxima_mem hCorrectForAll fuel rest value hValue
                have hValueTail := hSuccess.2.2.2.mem_iff.mp hValueRest
                have hValueHeap := List.mem_of_mem_drop hValueTail
                obtain ⟨index, hIndex, hValueAtIndex⟩ :=
                  Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp hValueHeap)
                have hBound := hMaximumBound index hIndex
                have hValueBang : heap[index]! = value := by
                  rw [getElem!_pos heap index hIndex, hValueAtIndex]
                rw [hValueBang] at hBound
                exact hBound
              · exact hRestSorted

/-- 取り出し列の長さは、指定 fuel にかかわらず元ヒープの要素数を超えない。 -/
theorem extractMaxima_length_le
    {extract : Array Nat → Option (Nat × Array Nat)}
    (hCorrectForAll : ∀ heap, PopMaxRestCorrectFor extract heap) :
    ∀ fuel heap, (extractMaxima extract fuel heap).length ≤ heap.size := by
  intro fuel
  induction fuel with
  | zero => intro heap; simp [extractMaxima]
  | succ fuel ih =>
      intro heap
      cases hExtract : extract heap with
      | none => simp [extractMaxima, hExtract]
      | some result =>
          cases result with
          | mk maximum rest =>
              have hSize : rest.size + 1 = heap.size := by
                simpa [hExtract] using
                  PopMaxRestCorrectFor.size (hCorrectForAll heap)
              have hTailBound := ih rest
              simp only [extractMaxima, hExtract, List.length_cons]
              omega

/-- 指定 fuel で取り出し終えた後に残る配列を返す。 -/
def extractRemainder (extract : Array Nat → Option (Nat × Array Nat)) :
    Nat → Array Nat → Array Nat
  | 0, heap => heap
  | fuel + 1, heap =>
      match extract heap with
      | none => heap
      | some (_, rest) => extractRemainder extract fuel rest

/-- 抽出に失敗した状態からは、追加 fuel を与えても列が増えない。 -/
private theorem extractMaxima_eq_nil_of_extract_none
    (extract : Array Nat → Option (Nat × Array Nat)) {heap : Array Nat}
    (hNone : extract heap = none) :
    ∀ fuel, extractMaxima extract fuel heap = [] := by
  intro fuel
  cases fuel with
  | zero => rfl
  | succ fuel => simp [extractMaxima, hNone]

/-- 抽出に失敗した状態は、追加 fuel 後も残余としてそのまま残る。 -/
private theorem extractRemainder_eq_self_of_extract_none
    (extract : Array Nat → Option (Nat × Array Nat)) {heap : Array Nat}
    (hNone : extract heap = none) :
    ∀ fuel, extractRemainder extract fuel heap = heap := by
  intro fuel
  cases fuel with
  | zero => rfl
  | succ fuel => simp [extractRemainder, hNone]

/-- 二段に分けた抽出列は、一度に合計 fuel を使った抽出列と一致する。

第一段の残余配列から第二段を実行すると、列は第一段・第二段の順に連結される。
抽出契約を仮定しないため、早期に `none` を返す関数にも適用できる。
-/
theorem extractMaxima_add_fuel
    (extract : Array Nat → Option (Nat × Array Nat))
    (firstFuel secondFuel : Nat) (heap : Array Nat) :
    extractMaxima extract (firstFuel + secondFuel) heap =
      extractMaxima extract firstFuel heap ++
        extractMaxima extract secondFuel (extractRemainder extract firstFuel heap) := by
  induction firstFuel generalizing heap with
  | zero => simp [extractMaxima, extractRemainder]
  | succ firstFuel ih =>
      cases hExtract : extract heap with
      | none =>
          simp [extractMaxima, extractRemainder, hExtract,
            extractMaxima_eq_nil_of_extract_none extract hExtract]
      | some result =>
          cases result with
          | mk maximum rest =>
              simp only [Nat.succ_add, extractMaxima, hExtract, extractRemainder]
              rw [ih (heap := rest)]
              simp

/-- 二段実行の最終残余は、合計 fuel を使った実行の残余と一致する。 -/
theorem extractRemainder_add_fuel
    (extract : Array Nat → Option (Nat × Array Nat))
    (firstFuel secondFuel : Nat) (heap : Array Nat) :
    extractRemainder extract (firstFuel + secondFuel) heap =
      extractRemainder extract secondFuel
        (extractRemainder extract firstFuel heap) := by
  induction firstFuel generalizing heap with
  | zero => simp [extractRemainder]
  | succ firstFuel ih =>
      cases hExtract : extract heap with
      | none =>
          simp [extractRemainder, hExtract,
            extractRemainder_eq_self_of_extract_none extract hExtract]
      | some result =>
          cases result with
          | mk maximum rest =>
              simp only [Nat.succ_add, extractRemainder, hExtract]
              exact ih (heap := rest)

/-- 十分な fuel の有無にかかわらず、残余配列の長さは入力長から fuel を引いた値。

各成功抽出で長さがちょうど1減り、入力が空になれば抽出は失敗するため、
fuel が入力長を超える場合も自然数の切り捨て減算で正確に表せる。
-/
theorem extractRemainder_size_eq_sub
    {extract : Array Nat → Option (Nat × Array Nat)}
    (hCorrectForAll : ∀ heap, PopMaxRestCorrectFor extract heap) :
    ∀ fuel heap,
      (extractRemainder extract fuel heap).size = heap.size - fuel := by
  intro fuel
  induction fuel with
  | zero => intro heap; simp [extractRemainder]
  | succ fuel ih =>
      intro heap
      cases hExtract : extract heap with
      | none =>
          have hEmpty : heap.size = 0 := by
            simpa [hExtract] using PopMaxRestCorrectFor.size (hCorrectForAll heap)
          simp [extractRemainder, hExtract, hEmpty]
      | some result =>
          cases result with
          | mk maximum rest =>
              have hStepSize : rest.size + 1 = heap.size := by
                simpa [hExtract] using PopMaxRestCorrectFor.size (hCorrectForAll heap)
              have hTail := ih rest
              simp only [extractRemainder, hExtract]
              rw [hTail]
              omega

/-- 抽出値列と最終残余を合わせると、元のヒープの順列になる。 -/
theorem extractMaxima_append_remainder_perm
    {extract : Array Nat → Option (Nat × Array Nat)}
    (hCorrectForAll : ∀ heap, PopMaxRestCorrectFor extract heap) :
    ∀ fuel heap,
      (extractMaxima extract fuel heap ++
        (extractRemainder extract fuel heap).toList).Perm heap.toList := by
  intro fuel
  induction fuel with
  | zero => intro heap; simp [extractMaxima, extractRemainder]
  | succ fuel ih =>
      intro heap
      cases hExtract : extract heap with
      | none => simp [extractMaxima, extractRemainder, hExtract]
      | some result =>
          cases result with
          | mk maximum rest =>
              have hStep : (maximum :: rest.toList).Perm heap.toList := by
                simpa [hExtract] using
                  PopMaxRestCorrectFor.perm_cons (hCorrectForAll heap)
              have hTail := ih rest
              simpa [extractMaxima, extractRemainder, hExtract] using
                hTail.cons maximum |>.trans hStep

/-- 抽出数と残余サイズの合計は、元のヒープサイズに等しい。 -/
theorem extractMaxima_length_add_remainder_size
    {extract : Array Nat → Option (Nat × Array Nat)}
    (hCorrectForAll : ∀ heap, PopMaxRestCorrectFor extract heap)
    (fuel : Nat) (heap : Array Nat) :
    (extractMaxima extract fuel heap).length +
        (extractRemainder extract fuel heap).size = heap.size := by
  have hPerm := extractMaxima_append_remainder_perm hCorrectForAll fuel heap
  have hLength := hPerm.length_eq
  simpa only [List.length_append, Array.length_toList] using hLength

/-- 指定 fuel で取り出される要素数は、fuel と入力長の小さい方に等しい。

各成功抽出が要素を1つ減らし、空配列で停止するため、処理済み要素数を
入力長や fuel の大小関係に応じた場合分けなしで表せる。
-/
theorem extractMaxima_length_eq_min_fuel_size
    {extract : Array Nat → Option (Nat × Array Nat)}
    (hCorrectForAll : ∀ heap, PopMaxRestCorrectFor extract heap)
    (fuel : Nat) (heap : Array Nat) :
    (extractMaxima extract fuel heap).length = min fuel heap.size := by
  have hLength := extractMaxima_length_add_remainder_size
    hCorrectForAll fuel heap
  have hRemainder := extractRemainder_size_eq_sub
    hCorrectForAll fuel heap
  by_cases hEnough : heap.size ≤ fuel
  · have hRemainderZero : (extractRemainder extract fuel heap).size = 0 := by
      rw [hRemainder]
      omega
    rw [hRemainderZero] at hLength
    simp only [Nat.min_eq_right hEnough]
    omega
  · have hFuelLtSize : fuel < heap.size := by omega
    rw [hRemainder] at hLength
    simp only [Nat.min_eq_left (Nat.le_of_lt hFuelLtSize)]
    omega

/-- 抽出値と残余配列の要素総和を合わせると、元のヒープの総和になる。 -/
theorem extractMaxima_sum_add_remainder_sum
    {extract : Array Nat → Option (Nat × Array Nat)}
    (hCorrectForAll : ∀ heap, PopMaxRestCorrectFor extract heap)
    (fuel : Nat) (heap : Array Nat) :
    (extractMaxima extract fuel heap).sum +
        (extractRemainder extract fuel heap).toList.sum = heap.toList.sum := by
  have hPerm := extractMaxima_append_remainder_perm hCorrectForAll fuel heap
  have hSum := hPerm.sum_nat
  simpa only [List.sum_append] using hSum

/-- 要素保存の一回抽出契約だけで、繰り返し抽出後も総和が保存される。

残余ヒープの最大ヒープ条件を仮定せず、各段階の値と要素保存だけを使う。
-/
theorem extractMaxima_sum_add_remainder_sum_of_elements
    {extract : Array Nat → Option (Nat × Array Nat)}
    (hElements : ∀ heap, PopMaxElementsCorrectFor extract heap) :
    ∀ fuel heap,
      (extractMaxima extract fuel heap).sum +
        (extractRemainder extract fuel heap).toList.sum = heap.toList.sum := by
  intro fuel
  induction fuel with
  | zero => intro heap; simp [extractMaxima, extractRemainder]
  | succ fuel ih =>
      intro heap
      cases hExtract : extract heap with
      | none =>
          have hSize : heap.size = 0 := by
            simpa [PopMaxElementsCorrectFor, hExtract] using hElements heap
          have hEmpty : heap = #[] := Array.size_eq_zero_iff.mp hSize
          have hExtractEmpty : extract #[] = none := by
            simpa [hEmpty] using hExtract
          simp [extractMaxima, extractRemainder, hEmpty, hExtractEmpty]
      | some result =>
          cases result with
          | mk maximum rest =>
              have hSpec : rest.size + 1 = heap.size ∧
                  (maximum :: rest.toList).Perm heap.toList := by
                simpa [PopMaxElementsCorrectFor, hExtract] using hElements heap
              have hStepSum : maximum + rest.toList.sum = heap.toList.sum := by
                have hSum := hSpec.2.sum_nat
                simpa using hSum
              have hTail := ih rest
              simp only [extractMaxima, extractRemainder, hExtract,
                List.sum_cons]
              omega

/-- fuel が残り要素数以上なら、抽出処理後の残余配列は空になる。 -/
theorem extractRemainder_eq_empty_of_enough_fuel
    {extract : Array Nat → Option (Nat × Array Nat)}
    (hCorrectForAll : ∀ heap, PopMaxRestCorrectFor extract heap) :
    ∀ fuel heap, heap.size ≤ fuel → extractRemainder extract fuel heap = #[] := by
  intro fuel
  induction fuel with
  | zero =>
      intro heap hSize
      have hHeapEmpty : heap = #[] := by
        apply Array.size_eq_zero_iff.mp
        omega
      simp [hHeapEmpty, extractRemainder]
  | succ fuel ih =>
      intro heap hFuel
      cases hExtract : extract heap with
      | none =>
          have hHeapSize : heap.size = 0 := by
            simpa [hExtract] using PopMaxRestCorrectFor.size (hCorrectForAll heap)
          have hHeapEmpty : heap = #[] := Array.size_eq_zero_iff.mp hHeapSize
          have hExtractEmpty : extract #[] = none := by
            simpa [hHeapEmpty] using hExtract
          simp [extractRemainder, hHeapEmpty, hExtractEmpty]
      | some result =>
          cases result with
          | mk maximum rest =>
              have hStepSize : rest.size + 1 = heap.size := by
                simpa [hExtract] using PopMaxRestCorrectFor.size (hCorrectForAll heap)
              have hRestFuel : rest.size ≤ fuel := by omega
              have hRestEmpty := ih rest hRestFuel
              simp [extractRemainder, hExtract, hRestEmpty]

/-- 十分な fuel で抽出を完了すると、抽出値列は元ヒープの順列になる。 -/
theorem extractMaxima_perm_of_enough_fuel
    {extract : Array Nat → Option (Nat × Array Nat)}
    (hCorrectForAll : ∀ heap, PopMaxRestCorrectFor extract heap)
    (fuel : Nat) (heap : Array Nat) (hFuel : heap.size ≤ fuel) :
    (extractMaxima extract fuel heap).Perm heap.toList := by
  have hPerm := extractMaxima_append_remainder_perm hCorrectForAll fuel heap
  rw [extractRemainder_eq_empty_of_enough_fuel hCorrectForAll fuel heap hFuel] at hPerm
  simpa using hPerm

/-- 要素保存の1回抽出契約だけから、抽出列と最終残余の併合が入力順列だと示す。 -/
theorem extractMaxima_append_remainder_perm_of_elements
    {extract : Array Nat → Option (Nat × Array Nat)}
    (hElements : ∀ heap, PopMaxElementsCorrectFor extract heap) :
    ∀ fuel heap,
      (extractMaxima extract fuel heap ++
        (extractRemainder extract fuel heap).toList).Perm heap.toList := by
  intro fuel
  induction fuel with
  | zero => intro heap; simp [extractMaxima, extractRemainder]
  | succ fuel ih =>
      intro heap
      cases hExtract : extract heap with
      | none =>
          have hSpec := hElements heap
          have hEmptySize : heap.size = 0 := by
            simpa [PopMaxElementsCorrectFor, hExtract] using hSpec
          have hEmpty : heap = #[] := Array.size_eq_zero_iff.mp hEmptySize
          have hExtractEmpty : extract #[] = none := by
            simpa [hEmpty] using hExtract
          simp [extractMaxima, extractRemainder, hEmpty, hExtractEmpty]
      | some result =>
          cases result with
          | mk maximum rest =>
              have hSpec : rest.size + 1 = heap.size ∧
                  (maximum :: rest.toList).Perm heap.toList := by
                simpa [PopMaxElementsCorrectFor, hExtract] using hElements heap
              have hStep : (maximum :: rest.toList).Perm heap.toList := by
                exact hSpec.2
              have hTail := ih rest
              simpa [extractMaxima, extractRemainder, hExtract] using
                hTail.cons maximum |>.trans hStep

/-- 部分抽出後も、抽出済み列と残余を合わせた任意条件の要素数が保存される。

ヒープ条件や抽出順序を仮定せず、各段階の要素保存契約だけから従う。
したがって、途中で処理を止めた場合にも、Boolean 条件で分類した要素の個数を
抽出済み側と残余側へ分解できる。
-/
theorem extractMaxima_countP_add_remainder_countP_of_elements
    {extract : Array Nat → Option (Nat × Array Nat)}
    (hElements : ∀ heap, PopMaxElementsCorrectFor extract heap)
    (fuel : Nat) (heap : Array Nat) (predicate : Nat → Bool) :
    (extractMaxima extract fuel heap).countP predicate +
        (extractRemainder extract fuel heap).toList.countP predicate =
      heap.toList.countP predicate := by
  have hPerm := extractMaxima_append_remainder_perm_of_elements
    hElements fuel heap
  have hCounts := hPerm.countP_eq predicate
  simpa [List.countP_append] using hCounts

/-- 要素保存契約だけから、抽出数と残余サイズの合計は入力サイズに等しい。 -/
theorem extractMaxima_length_add_remainder_size_of_elements
    {extract : Array Nat → Option (Nat × Array Nat)}
    (hElements : ∀ heap, PopMaxElementsCorrectFor extract heap)
    (fuel : Nat) (heap : Array Nat) :
    (extractMaxima extract fuel heap).length +
        (extractRemainder extract fuel heap).size = heap.size := by
  have hPerm := extractMaxima_append_remainder_perm_of_elements hElements fuel heap
  have hLength := hPerm.length_eq
  simpa only [List.length_append, Array.length_toList] using hLength

/-- 要素保存の1回抽出契約では、十分な fuel で残余配列が空になる。 -/
theorem extractRemainder_eq_empty_of_enough_fuel_of_elements
    {extract : Array Nat → Option (Nat × Array Nat)}
    (hElements : ∀ heap, PopMaxElementsCorrectFor extract heap) :
    ∀ fuel heap, heap.size ≤ fuel → extractRemainder extract fuel heap = #[] := by
  intro fuel
  induction fuel with
  | zero =>
      intro heap hSize
      have hHeapEmpty : heap = #[] := by
        apply Array.size_eq_zero_iff.mp
        omega
      simp [hHeapEmpty, extractRemainder]
  | succ fuel ih =>
      intro heap hFuel
      cases hExtract : extract heap with
      | none =>
          have hHeapSize : heap.size = 0 := by
            simpa [PopMaxElementsCorrectFor, hExtract] using hElements heap
          have hHeapEmpty : heap = #[] := Array.size_eq_zero_iff.mp hHeapSize
          have hExtractEmpty : extract #[] = none := by
            simpa [hHeapEmpty] using hExtract
          simp [extractRemainder, hHeapEmpty, hExtractEmpty]
      | some result =>
          cases result with
          | mk maximum rest =>
              have hSpec : rest.size + 1 = heap.size ∧
                  (maximum :: rest.toList).Perm heap.toList := by
                simpa [PopMaxElementsCorrectFor, hExtract] using hElements heap
              have hStepSize : rest.size + 1 = heap.size := by
                exact hSpec.1
              have hRestFuel : rest.size ≤ fuel := by omega
              have hRestEmpty := ih rest hRestFuel
              simp [extractRemainder, hExtract, hRestEmpty]

/-- サイズ減少と空配列での停止だけから、任意 fuel 後の残余長を正確に求める。

要素の順序やヒープ条件は使わず、成功時のサイズ減少と失敗時の空配列条件だけを使う。
-/
theorem extractRemainder_size_eq_sub_of_elements
    {extract : Array Nat → Option (Nat × Array Nat)}
    (hElements : ∀ heap, PopMaxElementsCorrectFor extract heap) :
    ∀ fuel heap,
      (extractRemainder extract fuel heap).size = heap.size - fuel := by
  intro fuel
  induction fuel with
  | zero => intro heap; simp [extractRemainder]
  | succ fuel ih =>
      intro heap
      cases hExtract : extract heap with
      | none =>
          have hEmpty : heap.size = 0 := by
            simpa [PopMaxElementsCorrectFor, hExtract] using hElements heap
          simp [extractRemainder, hExtract, hEmpty]
      | some result =>
          cases result with
          | mk maximum rest =>
              have hSpec : rest.size + 1 = heap.size ∧
                  (maximum :: rest.toList).Perm heap.toList := by
                simpa [PopMaxElementsCorrectFor, hExtract] using hElements heap
              have hStepSize : rest.size + 1 = heap.size := hSpec.1
              have hTail := ih rest
              simp only [extractRemainder, hExtract]
              rw [hTail]
              omega

/-- 要素保存契約だけから、抽出済み要素数は fuel と入力長の小さい方に等しい。

ヒープ条件や抽出順序を必要とせず、各成功段階でサイズが1減ることだけで処理数が決まる。
-/
theorem extractMaxima_length_eq_min_fuel_size_of_elements
    {extract : Array Nat → Option (Nat × Array Nat)}
    (hElements : ∀ heap, PopMaxElementsCorrectFor extract heap)
    (fuel : Nat) (heap : Array Nat) :
    (extractMaxima extract fuel heap).length = min fuel heap.size := by
  have hLength := extractMaxima_length_add_remainder_size_of_elements
    hElements fuel heap
  have hRemainder := extractRemainder_size_eq_sub_of_elements
    hElements fuel heap
  by_cases hEnough : heap.size ≤ fuel
  · have hRemainderZero : (extractRemainder extract fuel heap).size = 0 := by
      rw [hRemainder]
      omega
    rw [hRemainderZero] at hLength
    simp only [Nat.min_eq_right hEnough]
    omega
  · have hFuelLtSize : fuel < heap.size := by omega
    rw [hRemainder] at hLength
    simp only [Nat.min_eq_left (Nat.le_of_lt hFuelLtSize)]
    omega

/-- 要素保存契約を満たす抽出器は、十分な fuel で元配列の全要素を取り出す。 -/
theorem extractMaxima_perm_of_enough_fuel_of_elements
    {extract : Array Nat → Option (Nat × Array Nat)}
    (hElements : ∀ heap, PopMaxElementsCorrectFor extract heap)
    (fuel : Nat) (heap : Array Nat) (hFuel : heap.size ≤ fuel) :
    (extractMaxima extract fuel heap).Perm heap.toList := by
  have hPerm := extractMaxima_append_remainder_perm_of_elements hElements fuel heap
  rw [extractRemainder_eq_empty_of_enough_fuel_of_elements
    hElements fuel heap hFuel] at hPerm
  simpa using hPerm

/-- 最大値を正しく抽出する関数は、十分な fuel で降順列と要素保存を同時に満たす。 -/
theorem extractMaxima_descending_and_perm_of_orderedCorrect
    {extract : Array Nat → Option (Nat × Array Nat)}
    (hOrdered : ∀ candidate, PopMaxOrderedCorrectFor extract candidate)
    (fuel : Nat) (heap : Array Nat) (hFuel : heap.size ≤ fuel) :
    (extractMaxima extract fuel heap).Pairwise (fun earlier later => later ≤ earlier) ∧
      (extractMaxima extract fuel heap).Perm heap.toList := by
  have hElements : ∀ candidate, PopMaxElementsCorrectFor extract candidate := by
    intro candidate
    exact PopMaxOrderedCorrectFor.elementsCorrect (hOrdered candidate)
  exact ⟨extractMaxima_pairwise_of_orderedCorrect hOrdered fuel heap,
    extractMaxima_perm_of_enough_fuel_of_elements hElements fuel heap hFuel⟩

/-- 最大抽出契約だけから、十分な fuel で昇順ソート仕様を得る。 -/
theorem extractMaxima_reverse_correct_of_orderedCorrect
    {extract : Array Nat → Option (Nat × Array Nat)}
    (hOrdered : ∀ candidate, PopMaxOrderedCorrectFor extract candidate)
    (fuel : Nat) (heap : Array Nat) (hFuel : heap.size ≤ fuel) :
    LeanExperiments.Verification.Sorting.Spec.Correct heap.toList
      (extractMaxima extract fuel heap).reverse := by
  obtain ⟨hDescending, hPerm⟩ :=
    extractMaxima_descending_and_perm_of_orderedCorrect hOrdered fuel heap hFuel
  constructor
  · apply LeanExperiments.Verification.Sorting.Spec.pairwise_ascending
    exact (List.pairwise_reverse).mpr hDescending
  · exact (List.reverse_perm _).trans hPerm

/-- 十分な fuel で完了する抽出列は、降順性と要素保存を同時に満たす。 -/
theorem extractMaxima_descending_and_perm_of_enough_fuel
    {extract : Array Nat → Option (Nat × Array Nat)}
    (hCorrectForAll : ∀ heap, PopMaxRestCorrectFor extract heap)
    (fuel : Nat) (heap : Array Nat) (hHeap : MaxHeap heap)
    (hFuel : heap.size ≤ fuel) :
    (extractMaxima extract fuel heap).Pairwise (fun earlier later => later ≤ earlier) ∧
      (extractMaxima extract fuel heap).Perm heap.toList := by
  exact ⟨extractMaxima_pairwise hCorrectForAll fuel heap hHeap,
    extractMaxima_perm_of_enough_fuel hCorrectForAll fuel heap hFuel⟩

/-- 十分な fuel で最大値を順に取り出し、列を反転すれば昇順ソート仕様を満たす。

最大値抽出で得られる列は降順で、元ヒープと同じ要素を持つ。反転によって
順序を昇順にし、順列関係は反転しても保たれるため、抽象的な抽出仕様から
ソート結果の正しさまで一度に導ける。
-/
theorem extractMaxima_reverse_correct_of_enough_fuel
    {extract : Array Nat → Option (Nat × Array Nat)}
    (hCorrectForAll : ∀ heap, PopMaxRestCorrectFor extract heap)
    (fuel : Nat) (heap : Array Nat) (hHeap : MaxHeap heap)
    (hFuel : heap.size ≤ fuel) :
    LeanExperiments.Verification.Sorting.Spec.Correct heap.toList
      (extractMaxima extract fuel heap).reverse := by
  obtain ⟨hDescending, hPerm⟩ :=
    extractMaxima_descending_and_perm_of_enough_fuel
      hCorrectForAll fuel heap hHeap hFuel
  constructor
  · apply LeanExperiments.Verification.Sorting.Spec.pairwise_ascending
    have hReversed := (List.pairwise_reverse).mpr hDescending
    simpa using hReversed
  · exact (List.reverse_perm _).trans hPerm

/-- 十分な fuel を与えた抽出列は、fuel の値によらず一致する。

fuel がヒープサイズ以上なら、反転した抽出列は同じ入力に対する正しいソート結果である。
仕様の一意性から反転後の一致を得て、反転の対合性で抽出列自体の一致に戻す。
-/
theorem extractMaxima_eq_of_enough_fuel
    {extract : Array Nat → Option (Nat × Array Nat)}
    (hCorrectForAll : ∀ heap, PopMaxRestCorrectFor extract heap)
    (fuel₁ fuel₂ : Nat) (heap : Array Nat) (hHeap : MaxHeap heap)
    (hFuel₁ : heap.size ≤ fuel₁) (hFuel₂ : heap.size ≤ fuel₂) :
    extractMaxima extract fuel₁ heap = extractMaxima extract fuel₂ heap := by
  have hSorted₁ := extractMaxima_reverse_correct_of_enough_fuel
    hCorrectForAll fuel₁ heap hHeap hFuel₁
  have hSorted₂ := extractMaxima_reverse_correct_of_enough_fuel
    hCorrectForAll fuel₂ heap hHeap hFuel₂
  have hReverseEq :=
    LeanExperiments.Verification.Sorting.Spec.Correct.eq_of_same_input hSorted₁ hSorted₂
  have hEq := congrArg List.reverse hReverseEq
  simpa using hEq

/-- fuel が入力サイズ以下なら、途中までの抽出列は完了時の抽出列の prefix になる。

各成功段階で同じ最大値を取り出し、残余配列に帰納法の仮定を適用する。
抽出順序の大小関係は使わず、残余契約とサイズ減少だけで示す。
-/
theorem extractMaxima_eq_take_of_fuel_le_size
    {extract : Array Nat → Option (Nat × Array Nat)}
    (hCorrectForAll : ∀ heap, PopMaxRestCorrectFor extract heap) :
    ∀ fuel heap, fuel ≤ heap.size →
      extractMaxima extract fuel heap =
        (extractMaxima extract heap.size heap).take fuel := by
  intro fuel
  induction fuel with
  | zero => intro heap _; simp [extractMaxima]
  | succ fuel ih =>
      intro heap hFuel
      cases hExtract : extract heap with
      | none =>
          have hEmptySize : heap.size = 0 := by
            simpa [PopMaxRestCorrectFor, hExtract] using hCorrectForAll heap
          have hEmpty : heap = #[] := Array.size_eq_zero_iff.mp hEmptySize
          have hExtractEmpty : extract #[] = none := by
            simpa [hEmpty] using hExtract
          simp [extractMaxima, hEmpty, hExtractEmpty]
      | some result =>
          cases result with
          | mk maximum rest =>
              have hSpec := hCorrectForAll heap
              have hStepSize : rest.size + 1 = heap.size := by
                simpa [hExtract] using PopMaxRestCorrectFor.size hSpec
              have hRestFuel : fuel ≤ rest.size := by omega
              have hTail := ih rest hRestFuel
              have hFull : extractMaxima extract heap.size heap =
                  maximum :: extractMaxima extract rest.size rest := by
                rw [← hStepSize]
                simp [extractMaxima, hExtract]
              calc
                extractMaxima extract (fuel + 1) heap =
                    maximum :: extractMaxima extract fuel rest := by
                  simp [extractMaxima, hExtract]
                _ = maximum :: (extractMaxima extract rest.size rest).take fuel := by
                  rw [hTail]
                _ = (extractMaxima extract heap.size heap).take (fuel + 1) := by
                  rw [hFull]
                  simp

/-- サイズ上限内の残余契約でも、部分抽出列は完了列の prefix になる。

各残余が最大ヒープでサイズも減るため、開始時のサイズ上限を再帰段階にも適用できる。
-/
theorem extractMaxima_eq_take_of_bounded_contract
    {extract : Array Nat → Option (Nat × Array Nat)}
    (bound : Nat)
    (hContract : ∀ candidate, MaxHeap candidate → candidate.size ≤ bound →
      PopMaxRestCorrectFor extract candidate) :
    ∀ fuel heap, MaxHeap heap → heap.size ≤ bound → fuel ≤ heap.size →
      extractMaxima extract fuel heap =
        (extractMaxima extract heap.size heap).take fuel := by
  intro fuel
  induction fuel with
  | zero => intro heap _ _ _; simp [extractMaxima]
  | succ fuel ih =>
      intro heap hHeap hBound hFuel
      cases hExtract : extract heap with
      | none =>
          have hEmptySize : heap.size = 0 := by
            simpa [PopMaxRestCorrectFor, hExtract] using
              hContract heap hHeap hBound
          have hEmpty : heap = #[] := Array.size_eq_zero_iff.mp hEmptySize
          have hExtractEmpty : extract #[] = none := by
            simpa [hEmpty] using hExtract
          simp [extractMaxima, hEmpty, hExtractEmpty]
      | some result =>
          cases result with
          | mk maximum rest =>
              have hSpec := hContract heap hHeap hBound
              have hSuccess :
                  0 < heap.size ∧ heap[0]? = some maximum ∧ MaxHeap rest ∧
                    rest.toList.Perm (heap.toList.drop 1) := by
                simpa [PopMaxRestCorrectFor, hExtract] using hSpec
              have hStepSize : rest.size + 1 = heap.size := by
                simpa [hExtract] using PopMaxRestCorrectFor.size hSpec
              have hRestBound : rest.size ≤ bound := by omega
              have hRestFuel : fuel ≤ rest.size := by omega
              have hTail := ih rest hSuccess.2.2.1 hRestBound hRestFuel
              have hFull : extractMaxima extract heap.size heap =
                  maximum :: extractMaxima extract rest.size rest := by
                rw [← hStepSize]
                simp [extractMaxima, hExtract]
              calc
                extractMaxima extract (fuel + 1) heap =
                    maximum :: extractMaxima extract fuel rest := by
                  simp [extractMaxima, hExtract]
                _ = maximum :: (extractMaxima extract rest.size rest).take fuel := by
                  rw [hTail]
                _ = (extractMaxima extract heap.size heap).take (fuel + 1) := by
                  rw [hFull]
                  simp

/-- 最大ヒープ上で抽出の残余契約が成立すれば、サイズ上限なしに抽出列を証明できる。

各成功ステップの残余も最大ヒープであり、サイズが1つ減るため、抽出契約は
最大ヒープ状態に対してだけ仮定すればよい。
-/
theorem extractMaxima_correct_of_heap_contract
    {extract : Array Nat → Option (Nat × Array Nat)}
    (fuel : Nat) (heap : Array Nat)
    (hContract : ∀ candidate, MaxHeap candidate →
      PopMaxRestCorrectFor extract candidate)
    (hHeap : MaxHeap heap) (hFuel : heap.size ≤ fuel) :
    (extractMaxima extract fuel heap).Pairwise (fun earlier later => later ≤ earlier) ∧
      (extractMaxima extract fuel heap).Perm heap.toList := by
  induction fuel generalizing heap with
  | zero =>
      have hEmpty : heap = #[] := by
        apply Array.size_eq_zero_iff.mp
        omega
      simp [extractMaxima, hEmpty]
  | succ fuel ih =>
      cases hExtract : extract heap with
      | none =>
          have hSpec := hContract heap hHeap
          have hEmptySize : heap.size = 0 := by
            simpa [PopMaxRestCorrectFor, hExtract] using hSpec
          have hEmpty : heap = #[] := Array.size_eq_zero_iff.mp hEmptySize
          have hExtractEmpty : extract #[] = none := by simpa [hEmpty] using hExtract
          rw [hEmpty]
          simp [extractMaxima, hExtractEmpty]
      | some result =>
          cases result with
          | mk maximum rest =>
              have hSpec := hContract heap hHeap
              have hStep :
                  0 < heap.size ∧ heap[0]? = some maximum ∧ MaxHeap rest ∧
                    rest.toList.Perm (heap.toList.drop 1) := by
                simpa [PopMaxRestCorrectFor, hExtract] using hSpec
              have hRestSize : rest.size + 1 = heap.size := by
                simpa [hExtract] using PopMaxRestCorrectFor.size hSpec
              have hTail := ih rest hStep.2.2.1 (by omega)
              have hStepPerm : (maximum :: rest.toList).Perm heap.toList := by
                simpa [hExtract] using PopMaxRestCorrectFor.perm_cons hSpec
              constructor
              · simp only [extractMaxima, hExtract]
                apply List.Pairwise.cons
                · intro value hValue
                  have hInRestExtracted := hTail.2.mem_iff.mp hValue
                  have hInRest := hStep.2.2.2.mem_iff.mp hInRestExtracted
                  have hInHeapTail := List.mem_of_mem_drop hInRest
                  have hInHeap := Array.mem_toList_iff.mp hInHeapTail
                  obtain ⟨index, hIndex, hValueAtIndex⟩ :=
                    Array.mem_iff_getElem.mp hInHeap
                  have hRootMax := MaxHeap.le_root hHeap index hIndex
                  have hRoot : heap[0]! = maximum := by
                    have hRootSome := hStep.2.1
                    rw [getElem?_pos heap 0 (by omega)] at hRootSome
                    injection hRootSome with hEq
                    simpa only [getElem!_pos heap 0 (by omega)] using hEq
                  have hValueBang : heap[index]! = value := by
                    rw [getElem!_pos heap index hIndex, hValueAtIndex]
                  rw [hRoot, hValueBang] at hRootMax
                  exact hRootMax
                · exact hTail.1
              · simp only [extractMaxima, hExtract]
                exact hTail.2.cons maximum |>.trans hStepPerm

/-- 最大ヒープ上の抽出契約が成立し、fuel が十分なら全要素をちょうど一度ずつ取り出す。

順列保存から抽出列の長さが初期ヒープの要素数に一致することを導く。
-/
theorem extractMaxima_length_eq_of_heap_contract
    {extract : Array Nat → Option (Nat × Array Nat)}
    (fuel : Nat) (heap : Array Nat)
    (hContract : ∀ candidate, MaxHeap candidate →
      PopMaxRestCorrectFor extract candidate)
    (hHeap : MaxHeap heap) (hFuel : heap.size ≤ fuel) :
    (extractMaxima extract fuel heap).length = heap.size := by
  have hPerm := (extractMaxima_correct_of_heap_contract
    fuel heap hContract hHeap hFuel).2
  calc
    (extractMaxima extract fuel heap).length = heap.toList.length := hPerm.length_eq
    _ = heap.size := by simp

/-- サイズ上限内で抽出の残余契約が成立すれば、その範囲の抽出列を証明できる。

各成功ステップで残余も最大ヒープとなり、サイズが1つ減るため、開始ヒープ以下の
サイズに限った契約で十分である。
-/
theorem extractMaxima_bounded_correct
    {extract : Array Nat → Option (Nat × Array Nat)}
    (bound fuel : Nat) (heap : Array Nat)
    (hContract : ∀ candidate, MaxHeap candidate → candidate.size ≤ bound →
      PopMaxRestCorrectFor extract candidate)
    (hHeap : MaxHeap heap) (hBound : heap.size ≤ bound)
    (hFuel : heap.size ≤ fuel) :
    (extractMaxima extract fuel heap).Pairwise (fun earlier later => later ≤ earlier) ∧
      (extractMaxima extract fuel heap).Perm heap.toList := by
  induction fuel generalizing heap with
  | zero =>
      have hEmpty : heap = #[] := by
        apply Array.size_eq_zero_iff.mp
        omega
      simp [extractMaxima, hEmpty]
  | succ fuel ih =>
      cases hExtract : extract heap with
      | none =>
          have hSpec := hContract heap hHeap hBound
          have hEmptySize : heap.size = 0 := by
            simpa [PopMaxRestCorrectFor, hExtract] using hSpec
          have hEmpty : heap = #[] := Array.size_eq_zero_iff.mp hEmptySize
          have hExtractEmpty : extract #[] = none := by simpa [hEmpty] using hExtract
          rw [hEmpty]
          simp [extractMaxima, hExtractEmpty]
      | some result =>
          cases result with
          | mk maximum rest =>
              have hSpec := hContract heap hHeap hBound
              have hStep :
                  0 < heap.size ∧ heap[0]? = some maximum ∧ MaxHeap rest ∧
                    rest.toList.Perm (heap.toList.drop 1) := by
                simpa [PopMaxRestCorrectFor, hExtract] using hSpec
              have hRestSize : rest.size + 1 = heap.size := by
                simpa [hExtract] using PopMaxRestCorrectFor.size hSpec
              have hTail := ih rest hStep.2.2.1
                (by omega) (by omega)
              have hStepPerm : (maximum :: rest.toList).Perm heap.toList := by
                simpa [hExtract] using PopMaxRestCorrectFor.perm_cons hSpec
              constructor
              · simp only [extractMaxima, hExtract]
                apply List.Pairwise.cons
                · intro value hValue
                  have hInRestExtracted := hTail.2.mem_iff.mp hValue
                  have hInRest := hStep.2.2.2.mem_iff.mp hInRestExtracted
                  have hInHeapTail := List.mem_of_mem_drop hInRest
                  have hInHeap := Array.mem_toList_iff.mp hInHeapTail
                  obtain ⟨index, hIndex, hValueAtIndex⟩ :=
                    Array.mem_iff_getElem.mp hInHeap
                  have hRootMax := MaxHeap.le_root hHeap index hIndex
                  have hRoot : heap[0]! = maximum := by
                    have hRootSome := hStep.2.1
                    rw [getElem?_pos heap 0 (by omega)] at hRootSome
                    injection hRootSome with hEq
                    simpa only [getElem!_pos heap 0 (by omega)] using hEq
                  have hValueBang : heap[index]! = value := by
                    rw [getElem!_pos heap index hIndex, hValueAtIndex]
                  rw [hRoot, hValueBang] at hRootMax
                  exact hRootMax
                · exact hTail.1
              · simp only [extractMaxima, hExtract]
                exact hTail.2.cons maximum |>.trans hStepPerm

/-- 有界契約の部分実行では、抽出済み列と残余ヒープが入力要素を分割する。

抽出が失敗した場合は契約からヒープが空と分かる。成功時は一段の順列仕様と、残余にも
適用できるサイズ上限付きの帰納仮定を合成する。
-/
theorem extractMaxima_append_remainder_perm_of_bounded_contract
    {extract : Array Nat → Option (Nat × Array Nat)}
    (bound fuel : Nat) (heap : Array Nat)
    (hContract : ∀ candidate, MaxHeap candidate → candidate.size ≤ bound →
      PopMaxRestCorrectFor extract candidate)
    (hHeap : MaxHeap heap) (hBound : heap.size ≤ bound) :
    (extractMaxima extract fuel heap ++
      (extractRemainder extract fuel heap).toList).Perm heap.toList := by
  induction fuel generalizing heap with
  | zero => simp [extractMaxima, extractRemainder]
  | succ fuel ih =>
      cases hExtract : extract heap with
      | none =>
          have hEmptySize : heap.size = 0 := by
            simpa [PopMaxRestCorrectFor, hExtract] using
              hContract heap hHeap hBound
          have hEmpty : heap = #[] := Array.size_eq_zero_iff.mp hEmptySize
          have hExtractEmpty : extract #[] = none := by
            simpa [hEmpty] using hExtract
          simp [extractMaxima, extractRemainder, hEmpty, hExtractEmpty]
      | some result =>
          cases result with
          | mk maximum rest =>
              have hSpec := hContract heap hHeap hBound
              have hStep :
                  0 < heap.size ∧ heap[0]? = some maximum ∧ MaxHeap rest ∧
                    rest.toList.Perm (heap.toList.drop 1) := by
                simpa [PopMaxRestCorrectFor, hExtract] using hSpec
              have hRestSize : rest.size + 1 = heap.size := by
                simpa [hExtract] using PopMaxRestCorrectFor.size hSpec
              have hTail := ih rest hStep.2.2.1 (by omega)
              have hStepPerm : (maximum :: rest.toList).Perm heap.toList := by
                simpa [hExtract] using PopMaxRestCorrectFor.perm_cons hSpec
              simp only [extractMaxima, extractRemainder, hExtract]
              exact hTail.cons maximum |>.trans hStepPerm

/-- サイズ上限付き契約でも、部分抽出後の任意条件の要素数を保存する。 -/
theorem extractMaxima_countP_add_remainder_countP_of_bounded_contract
    {extract : Array Nat → Option (Nat × Array Nat)}
    (bound fuel : Nat) (heap : Array Nat)
    (hContract : ∀ candidate, MaxHeap candidate → candidate.size ≤ bound →
      PopMaxRestCorrectFor extract candidate)
    (hHeap : MaxHeap heap) (hBound : heap.size ≤ bound)
    (predicate : Nat → Bool) :
    (extractMaxima extract fuel heap).countP predicate +
        (extractRemainder extract fuel heap).toList.countP predicate =
      heap.toList.countP predicate := by
  have hPerm := extractMaxima_append_remainder_perm_of_bounded_contract
    bound fuel heap hContract hHeap hBound
  have hCounts := hPerm.countP_eq predicate
  simpa [List.countP_append] using hCounts

/-- サイズ上限付きの抽出契約でも、部分抽出列は降順になる。

完了抽出列の降順性を上限付き契約から示し、部分列をその prefix として得る。
-/
theorem extractMaxima_pairwise_of_bounded_contract
    {extract : Array Nat → Option (Nat × Array Nat)}
    (bound fuel : Nat) (heap : Array Nat)
    (hContract : ∀ candidate, MaxHeap candidate → candidate.size ≤ bound →
      PopMaxRestCorrectFor extract candidate)
    (hHeap : MaxHeap heap) (hBound : heap.size ≤ bound)
    (hFuel : fuel ≤ heap.size) :
    (extractMaxima extract fuel heap).Pairwise (fun earlier later => later ≤ earlier) := by
  rw [extractMaxima_eq_take_of_bounded_contract bound hContract
    fuel heap hHeap hBound hFuel]
  have hFull := extractMaxima_bounded_correct
    bound heap.size heap hContract hHeap hBound (Nat.le_refl _)
  exact hFull.1.take

/-- ヒープ長以下の fuel なら、有界契約の抽出処理は毎回1要素を取り出す。

完了列の長さがヒープ長であることと、途中列が完了列の prefix であることから従う。
-/
theorem extractMaxima_length_eq_fuel_of_bounded_contract
    {extract : Array Nat → Option (Nat × Array Nat)}
    (bound fuel : Nat) (heap : Array Nat)
    (hContract : ∀ candidate, MaxHeap candidate → candidate.size ≤ bound →
      PopMaxRestCorrectFor extract candidate)
    (hHeap : MaxHeap heap) (hBound : heap.size ≤ bound)
    (hFuel : fuel ≤ heap.size) :
    (extractMaxima extract fuel heap).length = fuel := by
  rw [extractMaxima_eq_take_of_bounded_contract bound hContract
    fuel heap hHeap hBound hFuel]
  have hFull := extractMaxima_bounded_correct
    bound heap.size heap hContract hHeap hBound (Nat.le_refl _)
  have hFullLength : (extractMaxima extract heap.size heap).length = heap.size :=
    hFull.2.length_eq
  simp [List.length_take, hFullLength, Nat.min_eq_left hFuel]

/-- 有界な抽出契約の途中結果は、完了列でまだ抽出していない要素以上になる。

部分抽出列を完了列の prefix とみなし、降順な完了列の prefix と suffix の関係を使う。
従って `fuel` 回で得られた要素は、完了列で後に現れる要素より小さくない。
-/
theorem extractMaxima_top_prefix_of_bounded_contract
    {extract : Array Nat → Option (Nat × Array Nat)}
    (bound fuel : Nat) (heap : Array Nat)
    (hContract : ∀ candidate, MaxHeap candidate → candidate.size ≤ bound →
      PopMaxRestCorrectFor extract candidate)
    (hHeap : MaxHeap heap) (hBound : heap.size ≤ bound)
    (hFuel : fuel ≤ heap.size) :
    ∀ selected, selected ∈ extractMaxima extract fuel heap →
      ∀ omitted, omitted ∈ (extractMaxima extract heap.size heap).drop fuel →
        omitted ≤ selected := by
  rw [extractMaxima_eq_take_of_bounded_contract bound hContract
    fuel heap hHeap hBound hFuel]
  have hFull := extractMaxima_bounded_correct
    bound heap.size heap hContract hHeap hBound (Nat.le_refl _)
  intro selected hSelected omitted hOmitted
  exact hFull.1.rel_of_mem_take_of_mem_drop hSelected hOmitted

/-- 有界な抽出契約で得た部分列を反転すると昇順になる。

最大値から順に得た降順の prefix を反転し、共通ソート仕様の `Ascending` へ接続する。
-/
theorem extractMaxima_reverse_ascending_of_bounded_contract
    {extract : Array Nat → Option (Nat × Array Nat)}
    (bound fuel : Nat) (heap : Array Nat)
    (hContract : ∀ candidate, MaxHeap candidate → candidate.size ≤ bound →
      PopMaxRestCorrectFor extract candidate)
    (hHeap : MaxHeap heap) (hBound : heap.size ≤ bound)
    (hFuel : fuel ≤ heap.size) :
    LeanExperiments.Verification.Sorting.Spec.Ascending
      (extractMaxima extract fuel heap).reverse := by
  have hDescending := extractMaxima_pairwise_of_bounded_contract
    bound fuel heap hContract hHeap hBound hFuel
  have hAscendingPairwise :=
    (List.pairwise_reverse).2 hDescending
  exact LeanExperiments.Verification.Sorting.Spec.pairwise_ascending _ hAscendingPairwise


/-- 正しいヒープ構築と残余仕様を持つ最大値抽出を合成すれば、入力を正しくソートする。

この定理は実装関数の有限例に依存しない。構築後のヒープ条件と要素保存、抽出関数の
残余仕様、ヒープサイズ以上の fuel があれば、抽出列を反転した結果が共通仕様を満たす。
従って、ヒープ構築・最大値抽出それぞれの一般的な実装証明を用意できれば、個々の
ソート入力を列挙せずに全入力の正当性を得られる。
-/
theorem sort_correct_of_heapBuild_and_extract
    {extract : Array Nat → Option (Nat × Array Nat)}
    {input heap : Array Nat}
    (hBuild : HeapBuildCorrect input heap)
    (hExtract : ∀ candidate, PopMaxRestCorrectFor extract candidate)
    (fuel : Nat) (hFuel : heap.size ≤ fuel) :
    LeanExperiments.Verification.Sorting.Spec.Correct input.toList
      (extractMaxima extract fuel heap).reverse := by
  have hSorted := extractMaxima_reverse_correct_of_enough_fuel
    hExtract fuel heap hBuild.1 hFuel
  exact ⟨hSorted.1, hSorted.2.trans hBuild.2⟩

/-- 最大ヒープ状態に限った抽出契約と正しい構築結果から、任意長のソートを導く。

抽出契約は実際に到達する最大ヒープ状態に対してのみ必要となる。構築後の最大ヒープ性、
抽出列の降順性と順列保存を合成し、列を反転した結果が入力の正しい昇順順列であると示す。
-/
theorem sort_correct_of_heapBuild_and_heap_extract
    {extract : Array Nat → Option (Nat × Array Nat)}
    {input heap : Array Nat}
    (hBuild : HeapBuildCorrect input heap)
    (hExtract : ∀ candidate, MaxHeap candidate →
      PopMaxRestCorrectFor extract candidate)
    (fuel : Nat) (hFuel : heap.size ≤ fuel) :
    LeanExperiments.Verification.Sorting.Spec.Correct input.toList
      (extractMaxima extract fuel heap).reverse := by
  obtain ⟨hDescending, hPerm⟩ := extractMaxima_correct_of_heap_contract
    fuel heap hExtract hBuild.1 hFuel
  constructor
  · apply LeanExperiments.Verification.Sorting.Spec.pairwise_ascending
    exact (List.pairwise_reverse).mpr hDescending
  · exact (List.reverse_perm _).trans hPerm |>.trans hBuild.2

/-- サイズ上限付きの抽出契約と正しいヒープ構築から、その範囲のソートを導く。

構築結果のサイズが契約上限内であれば、抽出中の残余サイズも上限を超えない。
そのため、有限範囲で証明した抽出契約を使っても、入力の正しいソート結果まで合成できる。
-/
theorem sort_correct_of_heapBuild_and_bounded_heap_extract
    {extract : Array Nat → Option (Nat × Array Nat)}
    {input heap : Array Nat}
    (hBuild : HeapBuildCorrect input heap)
    (bound fuel : Nat)
    (hExtract : ∀ candidate, MaxHeap candidate → candidate.size ≤ bound →
      PopMaxRestCorrectFor extract candidate)
    (hBound : heap.size ≤ bound) (hFuel : heap.size ≤ fuel) :
    LeanExperiments.Verification.Sorting.Spec.Correct input.toList
      (extractMaxima extract fuel heap).reverse := by
  obtain ⟨hDescending, hPerm⟩ := extractMaxima_bounded_correct
    bound fuel heap hExtract hBuild.1 hBound hFuel
  constructor
  · apply LeanExperiments.Verification.Sorting.Spec.pairwise_ascending
    exact (List.pairwise_reverse).mpr hDescending
  · exact (List.reverse_perm _).trans hPerm |>.trans hBuild.2

/-- 最大ヒープ入力に対する再帰版構築を、抽象的な最大値抽出と合成してソート仕様を得る。

入力が最大ヒープであるという前提の下では、再帰版構築の `HeapBuildCorrect` と
要素数に十分な fuel を満たせる。抽出実装が残余仕様を満たすことを別途証明すれば、
この定理から具体的なソート結果の正当性を導ける。
-/
theorem sort_correct_of_recursiveHeapBuild_and_extract_of_maxHeapInput
    {extract : Array Nat → Option (Nat × Array Nat)} (input : Array Nat)
    (hInput : MaxHeap input)
    (hExtract : ∀ candidate, PopMaxRestCorrectFor extract candidate) :
    LeanExperiments.Verification.Sorting.Spec.Correct input.toList
      (extractMaxima extract input.size
        (LeanExperiments.HeapSort.buildMaxHeapRecursive input)).reverse := by
  apply sort_correct_of_heapBuild_and_extract
    (buildMaxHeapRecursive_correct_of_maxHeapInput input hInput)
    hExtract input.size
  rw [buildMaxHeapRecursive_size]
  exact Nat.le_refl _

/-- 長さ4以下の入力では、抽象抽出契約から再帰版構築後のソート仕様を得る。

この範囲では構築後の最大ヒープ条件を無条件で証明できる。抽出関数自体が残余仕様を
満たすことは引き続き別の前提としている。
-/
theorem sort_correct_of_recursiveHeapBuild_and_extract_of_size_le_four
    {extract : Array Nat → Option (Nat × Array Nat)} (input : Array Nat)
    (hInputSize : input.size ≤ 4)
    (hExtract : ∀ candidate, PopMaxRestCorrectFor extract candidate) :
    LeanExperiments.Verification.Sorting.Spec.Correct input.toList
      (extractMaxima extract input.size
        (LeanExperiments.HeapSort.buildMaxHeapRecursive input)).reverse := by
  apply sort_correct_of_heapBuild_and_extract
    (buildMaxHeapRecursive_correct_of_size_le_four input hInputSize)
    hExtract input.size
  rw [buildMaxHeapRecursive_size]
  exact Nat.le_refl _

/-- 長さ5以下の入力では、抽象抽出契約から再帰版構築後のソート仕様を得る。

この範囲では構築後の最大ヒープ条件を無条件で証明できる。抽出関数自体が残余仕様を
満たすことは引き続き別の前提としている。
-/
theorem sort_correct_of_recursiveHeapBuild_and_extract_of_size_le_five
    {extract : Array Nat → Option (Nat × Array Nat)} (input : Array Nat)
    (hInputSize : input.size ≤ 5)
    (hExtract : ∀ candidate, PopMaxRestCorrectFor extract candidate) :
    LeanExperiments.Verification.Sorting.Spec.Correct input.toList
      (extractMaxima extract input.size
        (LeanExperiments.HeapSort.buildMaxHeapRecursive input)).reverse := by
  apply sort_correct_of_heapBuild_and_extract
    (buildMaxHeapRecursive_correct_of_size_le_five input hInputSize)
    hExtract input.size
  rw [buildMaxHeapRecursive_size]
  exact Nat.le_refl _

/-- 長さ6以下の入力では、抽象抽出契約から再帰版構築後のソート仕様を得る。

この範囲では構築後の最大ヒープ条件を無条件で証明できる。抽出関数自体が残余仕様を
満たすことは引き続き別の前提としている。
-/
theorem sort_correct_of_recursiveHeapBuild_and_extract_of_size_le_six
    {extract : Array Nat → Option (Nat × Array Nat)} (input : Array Nat)
    (hInputSize : input.size ≤ 6)
    (hExtract : ∀ candidate, PopMaxRestCorrectFor extract candidate) :
    LeanExperiments.Verification.Sorting.Spec.Correct input.toList
      (extractMaxima extract input.size
        (LeanExperiments.HeapSort.buildMaxHeapRecursive input)).reverse := by
  apply sort_correct_of_heapBuild_and_extract
    (buildMaxHeapRecursive_correct_of_size_le_six input hInputSize)
    hExtract input.size
  rw [buildMaxHeapRecursive_size]
  exact Nat.le_refl _

/-- 同じヒープから契約を満たす二つの抽出実装は、十分な fuel なら同じソート結果を返す。

各抽出列を反転した結果は、どちらも同じヒープの正しい昇順ソートである。
共通ソート仕様の一意性により、残余ヒープの内部配置や抽出手順が違っても出力リストは一致する。
-/
theorem extractMaxima_reverse_eq_of_contracts
    {extract₁ extract₂ : Array Nat → Option (Nat × Array Nat)}
    (hCorrect₁ : ∀ candidate, PopMaxRestCorrectFor extract₁ candidate)
    (hCorrect₂ : ∀ candidate, PopMaxRestCorrectFor extract₂ candidate)
    (fuel : Nat) (heap : Array Nat) (hHeap : MaxHeap heap)
    (hFuel : heap.size ≤ fuel) :
    (extractMaxima extract₁ fuel heap).reverse =
      (extractMaxima extract₂ fuel heap).reverse := by
  exact LeanExperiments.Verification.Sorting.Spec.Correct.eq_of_same_input
    (extractMaxima_reverse_correct_of_enough_fuel hCorrect₁ fuel heap hHeap hFuel)
    (extractMaxima_reverse_correct_of_enough_fuel hCorrect₂ fuel heap hHeap hFuel)

/-- サイズ上限内の残余契約だけで、二つの抽出実装の完了結果が一致する。

抽出中の残余は入力ヒープ以下のサイズになるため、開始時の上限内に契約を限定しても
両方の反転出力が同じソート仕様を満たし、その一意性から一致を得られる。
-/
theorem extractMaxima_reverse_eq_of_bounded_contracts
    {extract₁ extract₂ : Array Nat → Option (Nat × Array Nat)}
    (bound fuel : Nat) (heap : Array Nat)
    (hCorrect₁ : ∀ candidate, MaxHeap candidate → candidate.size ≤ bound →
      PopMaxRestCorrectFor extract₁ candidate)
    (hCorrect₂ : ∀ candidate, MaxHeap candidate → candidate.size ≤ bound →
      PopMaxRestCorrectFor extract₂ candidate)
    (hHeap : MaxHeap heap) (hBound : heap.size ≤ bound)
    (hFuel : heap.size ≤ fuel) :
    (extractMaxima extract₁ fuel heap).reverse =
      (extractMaxima extract₂ fuel heap).reverse := by
  have hExtract₁ := extractMaxima_bounded_correct bound fuel heap
    hCorrect₁ hHeap hBound hFuel
  have hExtract₂ := extractMaxima_bounded_correct bound fuel heap
    hCorrect₂ hHeap hBound hFuel
  have hSorted₁ : LeanExperiments.Verification.Sorting.Spec.Correct heap.toList
      (extractMaxima extract₁ fuel heap).reverse := by
    constructor
    · apply LeanExperiments.Verification.Sorting.Spec.pairwise_ascending
      exact (List.pairwise_reverse).mpr hExtract₁.1
    · exact (List.reverse_perm _).trans hExtract₁.2
  have hSorted₂ : LeanExperiments.Verification.Sorting.Spec.Correct heap.toList
      (extractMaxima extract₂ fuel heap).reverse := by
    constructor
    · apply LeanExperiments.Verification.Sorting.Spec.pairwise_ascending
      exact (List.pairwise_reverse).mpr hExtract₂.1
    · exact (List.reverse_perm _).trans hExtract₂.2
  exact LeanExperiments.Verification.Sorting.Spec.Correct.eq_of_same_input
    hSorted₁ hSorted₂

/-- 契約を満たす二つの抽出実装は、部分 fuel でも同じ値列を返す。

両実装の部分列は、それぞれ十分な fuel で得られる完了列の prefix である。
完了列の一致と prefix 定理を合わせ、途中結果の一致を導く。
-/
theorem extractMaxima_eq_of_contracts_of_fuel_le_size
    {extract₁ extract₂ : Array Nat → Option (Nat × Array Nat)}
    (hCorrect₁ : ∀ candidate, PopMaxRestCorrectFor extract₁ candidate)
    (hCorrect₂ : ∀ candidate, PopMaxRestCorrectFor extract₂ candidate)
    (fuel : Nat) (heap : Array Nat) (hHeap : MaxHeap heap)
    (hFuel : fuel ≤ heap.size) :
    extractMaxima extract₁ fuel heap = extractMaxima extract₂ fuel heap := by
  rw [extractMaxima_eq_take_of_fuel_le_size hCorrect₁ fuel heap hFuel,
    extractMaxima_eq_take_of_fuel_le_size hCorrect₂ fuel heap hFuel]
  have hFullReverse := extractMaxima_reverse_eq_of_contracts
    hCorrect₁ hCorrect₂ heap.size heap hHeap (Nat.le_refl _)
  have hFull := congrArg List.reverse hFullReverse
  exact congrArg (List.take fuel) (by simpa using hFull)

/-- サイズ上限付き契約を満たす二実装は、部分 fuel でも同じ抽出列を返す。

部分列を各実装の完了列の prefix として表し、完了結果の一意性を使って比較する。
-/
theorem extractMaxima_eq_of_bounded_contracts_of_fuel_le_size
    {extract₁ extract₂ : Array Nat → Option (Nat × Array Nat)}
    (bound fuel : Nat) (heap : Array Nat)
    (hCorrect₁ : ∀ candidate, MaxHeap candidate → candidate.size ≤ bound →
      PopMaxRestCorrectFor extract₁ candidate)
    (hCorrect₂ : ∀ candidate, MaxHeap candidate → candidate.size ≤ bound →
      PopMaxRestCorrectFor extract₂ candidate)
    (hHeap : MaxHeap heap) (hBound : heap.size ≤ bound)
    (hFuel : fuel ≤ heap.size) :
    extractMaxima extract₁ fuel heap = extractMaxima extract₂ fuel heap := by
  rw [extractMaxima_eq_take_of_bounded_contract bound hCorrect₁
      fuel heap hHeap hBound hFuel,
    extractMaxima_eq_take_of_bounded_contract bound hCorrect₂
      fuel heap hHeap hBound hFuel]
  have hFullReverse := extractMaxima_reverse_eq_of_bounded_contracts
    bound heap.size heap hCorrect₁ hCorrect₂ hHeap hBound (Nat.le_refl _)
  have hFull := congrArg List.reverse hFullReverse
  exact congrArg (List.take fuel) (by simpa using hFull)

/-- 取り出し後は、返却値と残余配列の和が入力ヒープの全要素の和に等しい。 -/
theorem PopMaxRestCorrectFor.sum_eq
    {extract : Array Nat → Option (Nat × Array Nat)} {heap : Array Nat}
    (hCorrect : PopMaxRestCorrectFor extract heap) :
    match extract heap with
    | none => True
    | some (maximum, rest) => maximum + rest.toList.sum = heap.toList.sum := by
  cases hExtract : extract heap with
  | none => trivial
  | some result =>
      cases result with
      | mk maximum rest =>
          have hPerm : (maximum :: rest.toList).Perm heap.toList := by
            simpa [hExtract] using PopMaxRestCorrectFor.perm_cons hCorrect
          have hSum := hPerm.sum_nat
          simpa [hExtract] using hSum

/-- 取り出し関数の残余仕様をヒープ条件と順列の Boolean 検査で判定する。 -/
def popMaxRestCheckFor
    (extract : Array Nat → Option (Nat × Array Nat)) (heap : Array Nat) : Bool :=
  match extract heap with
  | none => decide (heap.isEmpty = true)
  | some (maximum, rest) =>
      decide (0 < heap.size) &&
        (decide (heap[0]? = some maximum) &&
          (maxHeapCheck rest && rest.toList.isPerm (heap.toList.drop 1)))

/-- 最大値抽出の順序仕様を Boolean で判定する。 -/
def popMaxOrderCheckFor
    (extract : Array Nat → Option (Nat × Array Nat)) (heap : Array Nat) : Bool :=
  match extract heap with
  | none => decide (heap.isEmpty = true)
  | some (maximum, rest) =>
      decide (0 < heap.size) &&
        (decide (heap[0]? = some maximum) &&
          (decide (∀ value, value ∈ rest.toList → value ≤ maximum) &&
            rest.toList.isPerm (heap.toList.drop 1)))

/-- 順序検査器が成功することと、その論理仕様は同値である。 -/
theorem popMaxOrderCheckFor_correct
    (extract : Array Nat → Option (Nat × Array Nat)) (heap : Array Nat) :
    popMaxOrderCheckFor extract heap = true ↔ PopMaxOrderCorrectFor extract heap := by
  cases hPop : extract heap with
  | none => simp [popMaxOrderCheckFor, PopMaxOrderCorrectFor, hPop]
  | some result =>
      cases result with
      | mk maximum rest =>
          simp [popMaxOrderCheckFor, PopMaxOrderCorrectFor, hPop,
            Bool.and_eq_true, List.isPerm_iff]

/-- 汎用の残余検査器が成功することと、論理仕様が成り立つことは同値である。 -/
theorem popMaxRestCheckFor_correct
    (extract : Array Nat → Option (Nat × Array Nat)) (heap : Array Nat) :
    popMaxRestCheckFor extract heap = true ↔ PopMaxRestCorrectFor extract heap := by
  cases hPop : extract heap with
  | none =>
      simp [popMaxRestCheckFor, PopMaxRestCorrectFor, hPop]
  | some result =>
      cases result with
      | mk maximum rest =>
          simp [popMaxRestCheckFor, PopMaxRestCorrectFor, hPop, Bool.and_eq_true,
            maxHeapCheck_correct, List.isPerm_iff]

/-- 入力が最大ヒープなら、強い残余検査の合格から順序検査も導ける。 -/
theorem popMaxOrderCheckFor_of_popMaxRestCheckFor
    (extract : Array Nat → Option (Nat × Array Nat)) (heap : Array Nat)
    (hHeap : MaxHeap heap) (hCheck : popMaxRestCheckFor extract heap = true) :
    popMaxOrderCheckFor extract heap = true := by
  apply (popMaxOrderCheckFor_correct extract heap).2
  exact PopMaxRestCorrectFor.orderCorrect
    ((popMaxRestCheckFor_correct extract heap).mp hCheck) hHeap

/-- 再帰版 `popMax` の順序仕様検査器。 -/
def popMaxRecursiveOrderCheck (heap : Array Nat) : Bool :=
  popMaxOrderCheckFor LeanExperiments.HeapSort.popMaxRecursive heap

/-- 最大ヒープからの再帰版抽出は、順序検査器に合格する。 -/
theorem popMaxRecursiveOrderCheck_of_maxHeap (heap : Array Nat)
    (hHeap : MaxHeap heap) :
    popMaxRecursiveOrderCheck heap = true := by
  cases hPop : LeanExperiments.HeapSort.popMaxRecursive heap with
  | none =>
      have hEmpty := (popMaxRecursive_eq_none_iff_empty heap).mp hPop
      have hIsEmpty : heap.isEmpty = true :=
        Array.isEmpty_iff_size_eq_zero.mpr hEmpty
      have hArrayEmpty : heap = #[] := by
        simpa [Array.isEmpty_iff] using hIsEmpty
      apply (popMaxOrderCheckFor_correct
        LeanExperiments.HeapSort.popMaxRecursive heap).2
      simp [PopMaxOrderCorrectFor, hArrayEmpty,
        LeanExperiments.HeapSort.popMaxRecursive]
  | some result =>
      cases result with
      | mk maximum rest =>
          apply (popMaxOrderCheckFor_correct
            LeanExperiments.HeapSort.popMaxRecursive heap).2
          simp only [PopMaxOrderCorrectFor, hPop]
          exact ⟨(Array.getElem?_eq_some_iff.mp
              (popMaxRecursive_value_eq_root hPop)).1,
            popMaxRecursive_value_eq_root hPop,
            popMaxRecursive_dominates_rest_of_maxHeap hHeap hPop,
            popMaxRecursive_rest_perm_dropRoot hPop⟩

/-- Boolean 残余検査に合格した取り出し結果は、成功時に要素数を1つ減らす。 -/
theorem popMaxRestCheckFor_size
    (extract : Array Nat → Option (Nat × Array Nat)) (heap : Array Nat)
    (hCheck : popMaxRestCheckFor extract heap = true) :
    match extract heap with
    | none => heap.size = 0
    | some (_, rest) => rest.size + 1 = heap.size :=
  PopMaxRestCorrectFor.size ((popMaxRestCheckFor_correct extract heap).mp hCheck)

/-- ループ版 `popMax` 後の残余は最大ヒープで、元の根以外の要素を保存する。 -/
def PopMaxRestCorrect (heap : Array Nat) : Prop :=
  PopMaxRestCorrectFor LeanExperiments.HeapSort.popMax heap

/-- ループ版 `popMax` の残余仕様を Boolean で検査する。 -/
def popMaxRestCheck (heap : Array Nat) : Bool :=
  popMaxRestCheckFor LeanExperiments.HeapSort.popMax heap

/-- ループ版の残余検査器は、その論理仕様と同値である。 -/
theorem popMaxRestCheck_correct (heap : Array Nat) :
    popMaxRestCheck heap = true ↔ PopMaxRestCorrect heap := by
  exact popMaxRestCheckFor_correct LeanExperiments.HeapSort.popMax heap

/-- 再帰版 `popMax` 後の残余ヒープについての仕様。 -/
def PopMaxRecursiveRestCorrect (heap : Array Nat) : Prop :=
  PopMaxRestCorrectFor LeanExperiments.HeapSort.popMaxRecursive heap

/-- 再帰版 `popMax` 後の残余仕様を Boolean で検査する。 -/
def popMaxRecursiveRestCheck (heap : Array Nat) : Bool :=
  popMaxRestCheckFor LeanExperiments.HeapSort.popMaxRecursive heap

/-- 再帰版の残余検査器も、その論理仕様と同値である。 -/
theorem popMaxRecursiveRestCheck_correct (heap : Array Nat) :
    popMaxRecursiveRestCheck heap = true ↔ PopMaxRecursiveRestCorrect heap := by
  exact popMaxRestCheckFor_correct LeanExperiments.HeapSort.popMaxRecursive heap

/-- 最大ヒープからの再帰版抽出は、残余ヒープ検査器にも合格する。 -/
theorem popMaxRecursiveRestCheck_of_maxHeap (heap : Array Nat)
    (hHeap : MaxHeap heap) :
    popMaxRecursiveRestCheck heap = true := by
  apply (popMaxRecursiveRestCheck_correct heap).2
  cases hPop : LeanExperiments.HeapSort.popMaxRecursive heap with
  | none =>
      have hEmpty := (popMaxRecursive_eq_none_iff_empty heap).mp hPop
      have hArrayEmpty : heap = #[] := by
        have hIsEmpty : heap.isEmpty = true :=
          Array.isEmpty_iff_size_eq_zero.mpr hEmpty
        simpa [Array.isEmpty_iff] using hIsEmpty
      simp [PopMaxRecursiveRestCorrect, PopMaxRestCorrectFor, hArrayEmpty,
        LeanExperiments.HeapSort.popMaxRecursive]
  | some result =>
      cases result with
      | mk maximum rest =>
          have hRoot := popMaxRecursive_value_eq_root hPop
          have hRestHeap := popMaxRecursive_rest_maxHeap_of_maxHeap hHeap hPop
          have hPerm := popMaxRecursive_rest_perm_dropRoot hPop
          simp only [PopMaxRecursiveRestCorrect, PopMaxRestCorrectFor, hPop]
          exact ⟨(Array.getElem?_eq_some_iff.mp hRoot).1, hRoot,
            hRestHeap, hPerm⟩

/-- 最大ヒープからのループ版抽出も、任意サイズで残余ヒープ仕様を満たす。 -/
theorem popMaxRestCorrectFor_of_maxHeap (heap : Array Nat)
    (hHeap : MaxHeap heap) :
    PopMaxRestCorrectFor LeanExperiments.HeapSort.popMax heap := by
  unfold PopMaxRestCorrectFor
  rw [popMax_eq_popMaxRecursive]
  apply (popMaxRestCheckFor_correct LeanExperiments.HeapSort.popMaxRecursive heap).mp
  simpa [popMaxRecursiveRestCheck] using
    popMaxRecursiveRestCheck_of_maxHeap heap hHeap

/-- 最大ヒープ上で再帰版 `popMax` は最大値順序仕様を満たす。 -/
theorem popMaxRecursive_orderCorrect_of_maxHeap (heap : Array Nat)
    (hHeap : MaxHeap heap) :
    PopMaxOrderCorrectFor LeanExperiments.HeapSort.popMaxRecursive heap := by
  exact PopMaxRestCorrectFor.orderCorrect
    ((popMaxRecursiveRestCheck_correct heap).mp
      (popMaxRecursiveRestCheck_of_maxHeap heap hHeap)) hHeap

/-- 最大ヒープ上でループ版 `popMax` は最大値順序仕様を満たす。 -/
theorem popMax_orderCorrect_of_maxHeap (heap : Array Nat)
    (hHeap : MaxHeap heap) :
    PopMaxOrderCorrectFor LeanExperiments.HeapSort.popMax heap := by
  exact PopMaxRestCorrectFor.orderCorrect
    (popMaxRestCorrectFor_of_maxHeap heap hHeap) hHeap

/-- 最大ヒープからのループ版抽出は、残余仕様の Boolean 検査器に合格する。 -/
theorem popMaxRestCheck_of_maxHeap (heap : Array Nat)
    (hHeap : MaxHeap heap) :
    popMaxRestCheck heap = true := by
  unfold popMaxRestCheck popMaxRestCheckFor
  rw [popMax_eq_popMaxRecursive]
  simpa [popMaxRecursiveRestCheck, popMaxRestCheckFor] using
    popMaxRecursiveRestCheck_of_maxHeap heap hHeap

/-- 最大ヒープからのループ版抽出は、最大値順序の Boolean 検査にも合格する。 -/
theorem popMaxOrderCheckFor_of_maxHeap (heap : Array Nat)
    (hHeap : MaxHeap heap) :
    popMaxOrderCheckFor LeanExperiments.HeapSort.popMax heap = true := by
  apply popMaxOrderCheckFor_of_popMaxRestCheckFor
    LeanExperiments.HeapSort.popMax heap hHeap
  exact popMaxRestCheck_of_maxHeap heap hHeap

/-- 長さ1以下の配列なら、その配列は必ず最大ヒープである。 -/
private theorem maxHeap_of_size_le_one (heap : Array Nat) (hSize : heap.size ≤ 1) :
    MaxHeap heap := by
  unfold MaxHeap
  intro index hIndex
  have hIndexLt : index < heap.size := by simpa using hIndex
  have hZero : index = 0 := by omega
  subst index
  constructor <;> intro hChild <;> omega

/-- 3要素入力の再帰版 `popMax` は、長さ2の下降で最大ヒープ残余を作る。 -/
private theorem popMaxRecursive_rest_maxHeap_of_size_eq_three
    (heap : Array Nat) (maximum : Nat) (rest : Array Nat)
    (hSize : heap.size = 3)
    (hPop : LeanExperiments.HeapSort.popMaxRecursive heap = some (maximum, rest)) :
    MaxHeap rest := by
  cases hRoot : heap[0]? with
  | none => simp [LeanExperiments.HeapSort.popMaxRecursive, hRoot] at hPop
  | some root =>
      cases hBack : heap.back? with
      | none => simp [LeanExperiments.HeapSort.popMaxRecursive, hRoot, hBack] at hPop
      | some last =>
          have hPopSize : heap.pop.size = 2 := by simp [Array.size_pop, hSize]
          have hPopNonempty : heap.pop ≠ #[] := by
            intro hEmpty
            have hEmptySize : heap.pop.size = 0 := by simp [hEmpty]
            rw [hPopSize] at hEmptySize
            omega
          have hRest : rest = LeanExperiments.HeapSort.siftDownRecursive
              (heap.pop.set! 0 last) 0 := by
            simp [LeanExperiments.HeapSort.popMaxRecursive, hRoot, hBack,
              hPopNonempty] at hPop
            exact hPop.2.symm
          have hCandidateSize : (heap.pop.set! 0 last).size = 2 := by
            simp [Array.size_pop, hSize]
          have hBuiltHeap :=
            (buildMaxHeapRecursive_correct_of_size_le_two
              (heap.pop.set! 0 last) (by omega)).1
          rw [buildMaxHeapRecursive_eq_siftDown_of_size_eq_two
            (heap.pop.set! 0 last) hCandidateSize] at hBuiltHeap
          rw [hRest]
          exact hBuiltHeap

/-- 長さ4入力の再帰版 `popMax` は、長さ3の下降で最大ヒープ残余を作る。 -/
private theorem popMaxRecursive_rest_maxHeap_of_size_le_four
    (heap : Array Nat) (maximum : Nat) (rest : Array Nat)
    (hSize : heap.size ≤ 4)
    (hPop : LeanExperiments.HeapSort.popMaxRecursive heap = some (maximum, rest)) :
    MaxHeap rest := by
  cases hRoot : heap[0]? with
  | none => simp [LeanExperiments.HeapSort.popMaxRecursive, hRoot] at hPop
  | some root =>
      cases hBack : heap.back? with
      | none => simp [LeanExperiments.HeapSort.popMaxRecursive, hRoot, hBack] at hPop
      | some last =>
          have hRestExpr : rest =
              (if heap.pop = #[] then heap.pop else
                LeanExperiments.HeapSort.siftDownRecursive (heap.pop.set! 0 last) 0) := by
            simp [LeanExperiments.HeapSort.popMaxRecursive, hRoot, hBack] at hPop
            by_cases hEmpty : heap.pop = #[]
            · simp [hEmpty] at hPop
              simpa [hEmpty] using hPop.2
            · simp [hEmpty] at hPop
              simpa [hEmpty] using hPop.2.symm
          by_cases hEmpty : heap.pop = #[]
          · rw [hRestExpr]
            simp [hEmpty, MaxHeap]
          · have hCandidateSize : (heap.pop.set! 0 last).size ≤ 3 := by
              have hSizePop : heap.pop.size = heap.size - 1 := by
                simp [Array.size_pop]
              have hSizeSet : (heap.pop.set! 0 last).size = heap.pop.size := by simp
              rw [hSizeSet, hSizePop]
              omega
            have hBuiltHeap :=
              (buildMaxHeapRecursive_correct_of_size_le_three
                (heap.pop.set! 0 last) hCandidateSize).1
            rw [buildMaxHeapRecursive_eq_siftDown_of_size_le_three
              (heap.pop.set! 0 last) hCandidateSize] at hBuiltHeap
            rw [hRestExpr]
            simp only [ite_eq_right hEmpty]
            exact hBuiltHeap

/-- 長さ4以下の任意配列では、再帰版 `popMax` が残余仕様を満たす。 -/
theorem popMaxRecursiveRestCorrect_of_size_le_four (heap : Array Nat)
    (hSize : heap.size ≤ 4) :
    PopMaxRecursiveRestCorrect heap := by
  cases hExtract : LeanExperiments.HeapSort.popMaxRecursive heap with
  | none =>
      have hEmptyInput := (popMaxRecursive_eq_none_iff_empty heap).mp hExtract
      have hEmptyHeap : heap = #[] := Array.size_eq_zero_iff.mp hEmptyInput
      simp [PopMaxRecursiveRestCorrect, PopMaxRestCorrectFor, hEmptyHeap,
        LeanExperiments.HeapSort.popMaxRecursive]
  | some result =>
      cases result with
      | mk maximum rest =>
          have hPop : LeanExperiments.HeapSort.popMaxRecursive heap =
              some (maximum, rest) := hExtract
          have hRestSize := popMaxRecursive_size hPop
          have hRestHeap := popMaxRecursive_rest_maxHeap_of_size_le_four
            heap maximum rest hSize hPop
          have hRoot := popMaxRecursive_value_eq_root hPop
          have hPerm := popMaxRecursive_rest_perm_dropRoot hPop
          have hPermTail : rest.toList.Perm heap.toList.tail := by simpa using hPerm
          simp [PopMaxRecursiveRestCorrect, PopMaxRestCorrectFor, hPop]
          exact ⟨by omega, hRoot, hRestHeap, hPermTail⟩

/-- 長さ5の配列を添字値で明示した列へ書き換える。 -/
private theorem array_eq_index_values_of_size_eq_five (heap : Array Nat)
    (hSize : heap.size = 5) :
    heap = #[heap[0]!, heap[1]!, heap[2]!, heap[3]!, heap[4]!] := by
  apply Array.ext_getElem?
  intro index
  by_cases h0 : index = 0
  · subst index; simp [hSize]
  · by_cases h1 : index = 1
    · subst index; simp [hSize]
    · by_cases h2 : index = 2
      · subst index; simp [hSize]
      · by_cases h3 : index = 3
        · subst index; simp [hSize]
        · by_cases h4 : index = 4
          · subst index; simp [hSize]
          · have hOutside : 5 ≤ index := by omega
            have hNone : heap[index]? = none :=
              Array.getElem?_eq_none_iff.mpr (by omega)
            simp [hOutside, hNone]

/-- 長さ6の配列を添字値で明示した列へ書き換える。 -/
private theorem array_eq_index_values_of_size_eq_six (heap : Array Nat)
    (hSize : heap.size = 6) :
    heap = #[heap[0]!, heap[1]!, heap[2]!, heap[3]!, heap[4]!, heap[5]!] := by
  apply Array.ext_getElem?
  intro index
  by_cases h0 : index = 0
  · subst index; simp [hSize]
  · by_cases h1 : index = 1
    · subst index; simp [hSize]
    · by_cases h2 : index = 2
      · subst index; simp [hSize]
      · by_cases h3 : index = 3
        · subst index; simp [hSize]
        · by_cases h4 : index = 4
          · subst index; simp [hSize]
          · by_cases h5 : index = 5
            · subst index; simp [hSize]
            · have hOutside : 6 ≤ index := by omega
              have hNone : heap[index]? = none :=
                Array.getElem?_eq_none_iff.mpr (by omega)
              simp [hOutside, hNone]

/-- 長さ7の配列を添字値で明示した列へ書き換える。 -/
private theorem array_eq_index_values_of_size_eq_seven (heap : Array Nat)
    (hSize : heap.size = 7) :
    heap = #[heap[0]!, heap[1]!, heap[2]!, heap[3]!, heap[4]!, heap[5]!, heap[6]!] := by
  apply Array.ext_getElem?
  intro index
  by_cases h0 : index = 0
  · subst index; simp [hSize]
  · by_cases h1 : index = 1
    · subst index; simp [hSize]
    · by_cases h2 : index = 2
      · subst index; simp [hSize]
      · by_cases h3 : index = 3
        · subst index; simp [hSize]
        · by_cases h4 : index = 4
          · subst index; simp [hSize]
          · by_cases h5 : index = 5
            · subst index; simp [hSize]
            · by_cases h6 : index = 6
              · subst index; simp [hSize]
              · have hOutside : 7 ≤ index := by omega
                have hNone : heap[index]? = none :=
                  Array.getElem?_eq_none_iff.mpr (by omega)
                simp [hOutside, hNone]

/-- 最大ヒープの5要素再帰版 `popMax` は最大ヒープ残余を返す。 -/
private theorem popMaxRecursive_rest_maxHeap_of_maxHeap_size_eq_five
    (heap : Array Nat) (maximum : Nat) (rest : Array Nat)
    (hSize : heap.size = 5) (hHeap : MaxHeap heap)
    (hPop : LeanExperiments.HeapSort.popMaxRecursive heap = some (maximum, rest)) :
    MaxHeap rest := by
  have hValues := array_eq_index_values_of_size_eq_five heap hSize
  let root := heap[0]!
  let left := heap[1]!
  let right := heap[2]!
  let leaf := heap[3]!
  let last := heap[4]!
  have hSubheap : leaf ≤ left := by
    have h := hHeap 1 (by simp [hSize])
    have h := h.1 (by simp [hSize])
    simpa [left, leaf] using h
  have hRest : rest =
      LeanExperiments.HeapSort.siftDownRecursive #[last, left, right, leaf] 0 := by
    rw [hValues] at hPop
    simp [LeanExperiments.HeapSort.popMaxRecursive] at hPop
    simpa [root, left, right, leaf, last] using hPop.2.symm
  rw [hRest]
  exact siftDownRecursive_quad_root_maxHeap last left right leaf hSubheap

/-- 最大ヒープの6要素再帰版 `popMax` は最大ヒープ残余を返す。 -/
private theorem popMaxRecursive_rest_maxHeap_of_maxHeap_size_eq_six
    (heap : Array Nat) (maximum : Nat) (rest : Array Nat)
    (hSize : heap.size = 6) (hHeap : MaxHeap heap)
    (hPop : LeanExperiments.HeapSort.popMaxRecursive heap = some (maximum, rest)) :
    MaxHeap rest := by
  have hValues := array_eq_index_values_of_size_eq_six heap hSize
  let root := heap[0]!
  let left := heap[1]!
  let right := heap[2]!
  let leftLeaf := heap[3]!
  let rightLeaf := heap[4]!
  let last := heap[5]!
  have hSubheapLeft : leftLeaf ≤ left := by
    have h := hHeap 1 (by simp [hSize])
    have h := h.1 (by simp [hSize])
    simpa [left, leftLeaf] using h
  have hSubheapRight : rightLeaf ≤ left := by
    have h := hHeap 1 (by simp [hSize])
    have h := h.2 (by simp [hSize])
    simpa [left, rightLeaf] using h
  have hRest : rest =
      LeanExperiments.HeapSort.siftDownRecursive
        #[last, left, right, leftLeaf, rightLeaf] 0 := by
    rw [hValues] at hPop
    simp [LeanExperiments.HeapSort.popMaxRecursive] at hPop
    simpa [root, left, right, leftLeaf, rightLeaf, last] using hPop.2.symm
  rw [hRest]
  exact siftDownRecursive_quint_root_maxHeap last left right leftLeaf rightLeaf
    hSubheapLeft hSubheapRight

/-- 最大ヒープの7要素再帰版 `popMax` は最大ヒープ残余を返す。 -/
private theorem popMaxRecursive_rest_maxHeap_of_maxHeap_size_eq_seven
    (heap : Array Nat) (maximum : Nat) (rest : Array Nat)
    (hSize : heap.size = 7) (hHeap : MaxHeap heap)
    (hPop : LeanExperiments.HeapSort.popMaxRecursive heap = some (maximum, rest)) :
    MaxHeap rest := by
  have hValues := array_eq_index_values_of_size_eq_seven heap hSize
  let left := heap[1]!
  let right := heap[2]!
  let leftLeaf := heap[3]!
  let rightLeaf := heap[4]!
  let rightChild := heap[5]!
  let last := heap[6]!
  have hSubheapLeft : leftLeaf ≤ left := by
    have h := hHeap 1 (by simp [hSize])
    have h := h.1 (by simp [hSize])
    simpa [left, leftLeaf] using h
  have hSubheapRight : rightLeaf ≤ left := by
    have h := hHeap 1 (by simp [hSize])
    have h := h.2 (by simp [hSize])
    simpa [left, rightLeaf] using h
  have hSubheapRightChild : rightChild ≤ right := by
    have h := hHeap 2 (by simp [hSize])
    have h := h.1 (by simp [hSize])
    simpa [right, rightChild] using h
  have hRest : rest =
      LeanExperiments.HeapSort.siftDownRecursive
        #[last, left, right, leftLeaf, rightLeaf, rightChild] 0 := by
    rw [hValues] at hPop
    simp [LeanExperiments.HeapSort.popMaxRecursive] at hPop
    simpa [left, right, leftLeaf, rightLeaf, rightChild, last] using hPop.2.symm
  rw [hRest]
  exact siftDownRecursive_sext_root_maxHeap last left right leftLeaf rightLeaf rightChild
    hSubheapLeft hSubheapRight hSubheapRightChild

/-- 最大ヒープの8要素再帰版 `popMax` は最大ヒープ残余を返す。 -/
private theorem popMaxRecursive_rest_maxHeap_of_maxHeap_size_eq_eight
    (heap : Array Nat) (maximum : Nat) (rest : Array Nat)
    (hSize : heap.size = 8) (hHeap : MaxHeap heap)
    (hPop : LeanExperiments.HeapSort.popMaxRecursive heap = some (maximum, rest)) :
    MaxHeap rest := by
  have hValues := array_eq_index_values_of_size_eq_eight heap hSize
  let left := heap[1]!
  let right := heap[2]!
  let leftLeft := heap[3]!
  let leftRight := heap[4]!
  let rightLeft := heap[5]!
  let rightRight := heap[6]!
  let last := heap[7]!
  have hSubheapLeftLeft : leftLeft ≤ left := by
    have h := hHeap 1 (by simp [hSize])
    have h := h.1 (by simp [hSize])
    simpa [left, leftLeft] using h
  have hSubheapLeftRight : leftRight ≤ left := by
    have h := hHeap 1 (by simp [hSize])
    have h := h.2 (by simp [hSize])
    simpa [left, leftRight] using h
  have hSubheapRightLeft : rightLeft ≤ right := by
    have h := hHeap 2 (by simp [hSize])
    have h := h.1 (by simp [hSize])
    simpa [right, rightLeft] using h
  have hSubheapRightRight : rightRight ≤ right := by
    have h := hHeap 2 (by simp [hSize])
    have h := h.2 (by simp [hSize])
    simpa [right, rightRight] using h
  have hRest : rest =
      LeanExperiments.HeapSort.siftDownRecursive
        #[last, left, right, leftLeft, leftRight, rightLeft, rightRight] 0 := by
    rw [hValues] at hPop
    simp [LeanExperiments.HeapSort.popMaxRecursive] at hPop
    simpa [left, right, leftLeft, leftRight, rightLeft, rightRight, last] using
      hPop.2.symm
  rw [hRest]
  exact siftDownRecursive_sept_root_maxHeap last left right leftLeft leftRight
    rightLeft rightRight hSubheapLeftLeft hSubheapLeftRight
    hSubheapRightLeft hSubheapRightRight

/-- 最大ヒープの9要素再帰版 `popMax` は最大ヒープ残余を返す。 -/
private theorem popMaxRecursive_rest_maxHeap_of_maxHeap_size_eq_nine
    (heap : Array Nat) (maximum : Nat) (rest : Array Nat)
    (hSize : heap.size = 9) (hHeap : MaxHeap heap)
    (hPop : LeanExperiments.HeapSort.popMaxRecursive heap = some (maximum, rest)) :
    MaxHeap rest := by
  have hValues := array_eq_index_values_of_size_eq_nine heap hSize
  let left := heap[1]!
  let right := heap[2]!
  let leftLeft := heap[3]!
  let leftRight := heap[4]!
  let rightLeft := heap[5]!
  let rightRight := heap[6]!
  let leftLeftLeft := heap[7]!
  let last := heap[8]!
  have hSubheapLeftLeft : leftLeft ≤ left := by
    have h := hHeap 1 (by simp [hSize])
    have h := h.1 (by simp [hSize])
    simpa [left, leftLeft] using h
  have hSubheapLeftRight : leftRight ≤ left := by
    have h := hHeap 1 (by simp [hSize])
    have h := h.2 (by simp [hSize])
    simpa [left, leftRight] using h
  have hSubheapRightLeft : rightLeft ≤ right := by
    have h := hHeap 2 (by simp [hSize])
    have h := h.1 (by simp [hSize])
    simpa [right, rightLeft] using h
  have hSubheapRightRight : rightRight ≤ right := by
    have h := hHeap 2 (by simp [hSize])
    have h := h.2 (by simp [hSize])
    simpa [right, rightRight] using h
  have hSubheapLeftLeftLeft : leftLeftLeft ≤ leftLeft := by
    have h := hHeap 3 (by simp [hSize])
    have h := h.1 (by simp [hSize])
    simpa [leftLeft, leftLeftLeft] using h
  have hRest : rest = LeanExperiments.HeapSort.siftDownRecursive
      #[last, left, right, leftLeft, leftRight, rightLeft, rightRight, leftLeftLeft] 0 := by
    rw [hValues] at hPop
    simp [LeanExperiments.HeapSort.popMaxRecursive] at hPop
    simpa [left, right, leftLeft, leftRight, rightLeft, rightRight, leftLeftLeft, last]
      using hPop.2.symm
  rw [hRest]
  exact siftDownRecursive_oct_root_maxHeap last left right leftLeft leftRight
    rightLeft rightRight leftLeftLeft hSubheapLeftLeft hSubheapLeftRight
    hSubheapRightLeft hSubheapRightRight hSubheapLeftLeftLeft

/-- サイズ9以下の最大ヒープでは、再帰版 `popMax` が残余契約を満たす。 -/
theorem popMaxRecursiveRestCorrect_of_maxHeap_and_size_le_nine (heap : Array Nat)
    (hHeap : MaxHeap heap) (hSize : heap.size ≤ 9) :
    PopMaxRecursiveRestCorrect heap := by
  cases hExtract : LeanExperiments.HeapSort.popMaxRecursive heap with
  | none =>
      have hEmpty := (popMaxRecursive_eq_none_iff_empty heap).mp hExtract
      have hHeapEmpty : heap = #[] := Array.size_eq_zero_iff.mp hEmpty
      simp [PopMaxRecursiveRestCorrect, PopMaxRestCorrectFor, hHeapEmpty,
        LeanExperiments.HeapSort.popMaxRecursive]
  | some result =>
      cases result with
      | mk maximum rest =>
          have hPop : LeanExperiments.HeapSort.popMaxRecursive heap =
              some (maximum, rest) := hExtract
          have hRestHeap : MaxHeap rest := by
            by_cases hSmall : heap.size ≤ 4
            · exact popMaxRecursive_rest_maxHeap_of_size_le_four
                heap maximum rest hSmall hPop
            · by_cases hFive : heap.size = 5
              · exact popMaxRecursive_rest_maxHeap_of_maxHeap_size_eq_five
                  heap maximum rest hFive hHeap hPop
              · by_cases hSix : heap.size = 6
                · exact popMaxRecursive_rest_maxHeap_of_maxHeap_size_eq_six
                    heap maximum rest hSix hHeap hPop
                · by_cases hSeven : heap.size = 7
                  · exact popMaxRecursive_rest_maxHeap_of_maxHeap_size_eq_seven
                      heap maximum rest hSeven hHeap hPop
                  · by_cases hEight : heap.size = 8
                    · exact popMaxRecursive_rest_maxHeap_of_maxHeap_size_eq_eight
                        heap maximum rest hEight hHeap hPop
                    · have hNine : heap.size = 9 := by omega
                      exact popMaxRecursive_rest_maxHeap_of_maxHeap_size_eq_nine
                        heap maximum rest hNine hHeap hPop
          have hRoot := popMaxRecursive_value_eq_root hPop
          have hPerm := popMaxRecursive_rest_perm_dropRoot hPop
          have hPermTail : rest.toList.Perm heap.toList.tail := by simpa using hPerm
          have hRestSize := popMaxRecursive_size hPop
          simp [PopMaxRecursiveRestCorrect, PopMaxRestCorrectFor, hPop]
          exact ⟨by omega, hRoot, hRestHeap, hPermTail⟩

/-- サイズ8以下の最大ヒープに対する再帰版 `popMax` 残余契約。 -/
theorem popMaxRecursiveRestCorrect_of_maxHeap_and_size_le_eight (heap : Array Nat)
    (hHeap : MaxHeap heap) (hSize : heap.size ≤ 8) :
    PopMaxRecursiveRestCorrect heap :=
  popMaxRecursiveRestCorrect_of_maxHeap_and_size_le_nine heap hHeap (by omega)

/-- サイズ7以下の最大ヒープに対する再帰版 `popMax` 残余契約。 -/
theorem popMaxRecursiveRestCorrect_of_maxHeap_and_size_le_seven (heap : Array Nat)
    (hHeap : MaxHeap heap) (hSize : heap.size ≤ 7) :
    PopMaxRecursiveRestCorrect heap :=
  popMaxRecursiveRestCorrect_of_maxHeap_and_size_le_eight heap hHeap (by omega)

/-- サイズ6以下の最大ヒープでの再帰版 `popMax` 残余契約。 -/
theorem popMaxRecursiveRestCorrect_of_maxHeap_and_size_le_six (heap : Array Nat)
    (hHeap : MaxHeap heap) (hSize : heap.size ≤ 6) :
    PopMaxRecursiveRestCorrect heap :=
  popMaxRecursiveRestCorrect_of_maxHeap_and_size_le_seven heap hHeap (by omega)

/-- 長さ3以下の任意配列では、再帰版 `popMax` が残余仕様を満たす。 -/
theorem popMaxRecursiveRestCorrect_of_size_le_three (heap : Array Nat)
    (hSize : heap.size ≤ 3) :
    PopMaxRecursiveRestCorrect heap :=
  popMaxRecursiveRestCorrect_of_size_le_four heap (by omega)

/-- 2要素以下の任意配列では、再帰版 `popMax` が残余仕様を満たす。 -/
theorem popMaxRecursiveRestCorrect_of_size_le_two (heap : Array Nat)
    (hSize : heap.size ≤ 2) :
    PopMaxRecursiveRestCorrect heap :=
  popMaxRecursiveRestCorrect_of_size_le_three heap (by omega)

/-- 空配列・単一要素配列では、再帰版 `popMax` が残余仕様を満たす。 -/
theorem popMaxRecursiveRestCorrect_of_size_le_one (heap : Array Nat)
    (hSize : heap.size ≤ 1) :
    PopMaxRecursiveRestCorrect heap :=
  popMaxRecursiveRestCorrect_of_size_le_two heap (by omega)

/-- 再帰版排出は、抽出列と既存出力を連結して反転した結果になる。

任意の fuel・ヒープ・既存出力で実装と抽象的な抽出列が一致するため、
抽出列に関する一般定理を実際の再帰版ソートへ移す際の接続点として使える。
-/
theorem drainRecursive_eq_reverse_extractMaxima (fuel : Nat)
    (heap output : Array Nat) :
    LeanExperiments.HeapSort.drainRecursive fuel heap output =
      ((output.toList ++ extractMaxima LeanExperiments.HeapSort.popMaxRecursive
        fuel heap).reverse).toArray := by
  induction fuel generalizing heap output with
  | zero =>
      apply Array.toList_inj.mp
      simp [LeanExperiments.HeapSort.drainRecursive, extractMaxima]
  | succ fuel ih =>
      cases hPop : LeanExperiments.HeapSort.popMaxRecursive heap with
      | none =>
          apply Array.toList_inj.mp
          simp [LeanExperiments.HeapSort.drainRecursive, extractMaxima, hPop]
      | some result =>
          cases result with
          | mk maximum rest =>
              have hDrain : LeanExperiments.HeapSort.drainRecursive
                  (fuel + 1) heap output =
                    LeanExperiments.HeapSort.drainRecursive fuel rest
                      (output.push maximum) := by
                simp [LeanExperiments.HeapSort.drainRecursive, hPop]
              rw [hDrain, ih rest (output.push maximum)]
              apply Array.toList_inj.mp
              simp [extractMaxima, hPop, Array.toList_push,
                List.append_assoc, List.reverse_append]

/-- 再帰版排出を二段に分けて再開しても、一括実行と同じ結果になる。

第一段で得た抽出列を降順の蓄積出力へ戻し、第一段の残余ヒープから第二段を続ける。
fuel 分割の合成則により、結果配列は分割しない実行と一致する。
-/
theorem drainRecursive_add_fuel (firstFuel secondFuel : Nat)
    (heap output : Array Nat) :
    LeanExperiments.HeapSort.drainRecursive (firstFuel + secondFuel) heap output =
      LeanExperiments.HeapSort.drainRecursive secondFuel
        (extractRemainder LeanExperiments.HeapSort.popMaxRecursive firstFuel heap)
        ((output.toList ++ extractMaxima LeanExperiments.HeapSort.popMaxRecursive
          firstFuel heap).toArray) := by
  rw [drainRecursive_eq_reverse_extractMaxima, drainRecursive_eq_reverse_extractMaxima]
  simp
  rw [extractMaxima_add_fuel]
  simp [List.append_assoc]

/-- 有界な抽出契約のもとで、再帰版排出の途中結果は昇順で fuel 個になる。

空の出力から始めた実行を抽象的な部分抽出列へ書き換え、昇順性と正確な処理数を得る。
-/
theorem drainRecursive_partial_correct_of_bounded_contract (bound fuel : Nat)
    (heap : Array Nat)
    (hContract : ∀ candidate, MaxHeap candidate → candidate.size ≤ bound →
      PopMaxRestCorrectFor LeanExperiments.HeapSort.popMaxRecursive candidate)
    (hHeap : MaxHeap heap) (hBound : heap.size ≤ bound)
    (hFuel : fuel ≤ heap.size) :
    LeanExperiments.Verification.Sorting.Spec.Ascending
        (LeanExperiments.HeapSort.drainRecursive fuel heap #[]).toList ∧
      (LeanExperiments.HeapSort.drainRecursive fuel heap #[]).size = fuel := by
  have hDrain := drainRecursive_eq_reverse_extractMaxima fuel heap #[]
  have hAscending := extractMaxima_reverse_ascending_of_bounded_contract
    bound fuel heap hContract hHeap hBound hFuel
  have hLength := extractMaxima_length_eq_fuel_of_bounded_contract
    bound fuel heap hContract hHeap hBound hFuel
  constructor
  · rw [hDrain]
    simpa using hAscending
  · rw [hDrain]
    simpa using hLength

/-- 降順の既存出力から部分排出を再開した結果も昇順になり、追加分はちょうど fuel 個となる。

既存出力が残余ヒープの全要素以上なら、今回抽出する値も既存出力の後ろに降順で続く。
全てを排出しきる必要はなく、fuel がヒープサイズ以下なら部分結果に適用できる。
-/
theorem drainRecursive_resume_partial_correct_of_bounded_contract
    (bound fuel : Nat) (heap output : Array Nat)
    (hContract : ∀ candidate, MaxHeap candidate → candidate.size ≤ bound →
      PopMaxRestCorrectFor LeanExperiments.HeapSort.popMaxRecursive candidate)
    (hHeap : MaxHeap heap) (hBound : heap.size ≤ bound) (hFuel : fuel ≤ heap.size)
    (hOutputDescending : output.toList.Pairwise (fun earlier later => later ≤ earlier))
    (hOutputAboveHeap : ∀ emitted, emitted ∈ output.toList →
      ∀ value, value ∈ heap.toList → value ≤ emitted) :
    LeanExperiments.Verification.Sorting.Spec.Ascending
        (LeanExperiments.HeapSort.drainRecursive fuel heap output).toList ∧
      (LeanExperiments.HeapSort.drainRecursive fuel heap output).size = output.size + fuel := by
  let extracted := extractMaxima LeanExperiments.HeapSort.popMaxRecursive fuel heap
  have hDescending := extractMaxima_pairwise_of_bounded_contract
    bound fuel heap hContract hHeap hBound hFuel
  have hPartition := extractMaxima_append_remainder_perm_of_bounded_contract
    bound fuel heap hContract hHeap hBound
  have hCross : ∀ emitted, emitted ∈ output.toList →
      ∀ value, value ∈ extracted → value ≤ emitted := by
    intro emitted hEmitted value hValue
    have hValueAppend : value ∈ extracted ++
        (extractRemainder LeanExperiments.HeapSort.popMaxRecursive fuel heap).toList :=
      List.mem_append.mpr (Or.inl hValue)
    have hValueHeap := hPartition.mem_iff.mp hValueAppend
    exact hOutputAboveHeap emitted hEmitted value hValueHeap
  have hCombinedDescending :
      (output.toList ++ extracted).Pairwise (fun earlier later => later ≤ earlier) := by
    rw [List.pairwise_append]
    exact ⟨hOutputDescending, hDescending, hCross⟩
  have hSorted :
      LeanExperiments.Verification.Sorting.Spec.Ascending
        (output.toList ++ extracted).reverse := by
    apply LeanExperiments.Verification.Sorting.Spec.pairwise_ascending
    exact (List.pairwise_reverse).mpr hCombinedDescending
  have hLength := extractMaxima_length_eq_fuel_of_bounded_contract
    bound fuel heap hContract hHeap hBound hFuel
  have hDrain := drainRecursive_eq_reverse_extractMaxima fuel heap output
  constructor
  · rw [hDrain]
    simpa [extracted] using hSorted
  · rw [hDrain]
    simp [List.length_append, hLength]
    omega

/-- 再帰版排出の途中出力と残余ヒープで、任意の Boolean 条件を満たす要素数が保存される。

出力は抽出列を反転した配列だが、反転しても条件に合う要素数は変わらない。
従って、途中で停止した時点でも、出力済み部分と未処理ヒープの個数を合計すると
入力での個数に一致する。
-/
theorem drainRecursive_countP_add_remainder_countP_of_bounded_contract
    (bound fuel : Nat) (heap : Array Nat)
    (hContract : ∀ candidate, MaxHeap candidate → candidate.size ≤ bound →
      PopMaxRestCorrectFor LeanExperiments.HeapSort.popMaxRecursive candidate)
    (hHeap : MaxHeap heap) (hBound : heap.size ≤ bound)
    (predicate : Nat → Bool) :
    (LeanExperiments.HeapSort.drainRecursive fuel heap #[]).toList.countP predicate +
        (extractRemainder LeanExperiments.HeapSort.popMaxRecursive fuel heap).toList.countP
          predicate =
      heap.toList.countP predicate := by
  have hCounts := extractMaxima_countP_add_remainder_countP_of_bounded_contract
    bound fuel heap hContract hHeap hBound predicate
  have hDrain := drainRecursive_eq_reverse_extractMaxima fuel heap #[]
  rw [hDrain]
  simpa using hCounts

/-- 既存の蓄積出力から再帰版排出を再開しても、出力と残余の分類個数が保存される。

再開前の出力とヒープを合わせた個数は、再開後の出力と残余ヒープに分配される。
既存出力の順序は問わず、要素の分類だけを追跡する。
-/
theorem drainRecursive_resume_countP_add_remainder_countP_of_bounded_contract
    (bound fuel : Nat) (heap output : Array Nat)
    (hContract : ∀ candidate, MaxHeap candidate → candidate.size ≤ bound →
      PopMaxRestCorrectFor LeanExperiments.HeapSort.popMaxRecursive candidate)
    (hHeap : MaxHeap heap) (hBound : heap.size ≤ bound)
    (predicate : Nat → Bool) :
    (LeanExperiments.HeapSort.drainRecursive fuel heap output).toList.countP predicate +
        (extractRemainder LeanExperiments.HeapSort.popMaxRecursive fuel heap).toList.countP
          predicate =
      output.toList.countP predicate + heap.toList.countP predicate := by
  have hCounts := extractMaxima_countP_add_remainder_countP_of_bounded_contract
    bound fuel heap hContract hHeap hBound predicate
  have hDrain := drainRecursive_eq_reverse_extractMaxima fuel heap output
  have hReverseCount :
      ((output.toList ++ extractMaxima LeanExperiments.HeapSort.popMaxRecursive
          fuel heap).reverse).countP predicate =
        (output.toList ++ extractMaxima LeanExperiments.HeapSort.popMaxRecursive
          fuel heap).countP predicate :=
    (List.reverse_perm _).countP_eq predicate
  rw [hDrain]
  rw [hReverseCount]
  simp only [List.countP_append]
  omega

/-- サイズ上限付き抽出契約での部分再開が、順序・長さ・要素分類数を同時に保つ。

再開前の出力が降順で、残余ヒープの全要素がその出力以下なら、途中再開後の配列は
昇順になり、追加分の長さは `fuel` と一致する。同時に、任意の Boolean 条件に合う値の
個数は、再開前の出力とヒープを合わせた個数から変化しない。
-/
theorem drainRecursive_resume_partial_contract_of_bounded_contract
    (bound fuel : Nat) (heap output : Array Nat)
    (hContract : ∀ candidate, MaxHeap candidate → candidate.size ≤ bound →
      PopMaxRestCorrectFor LeanExperiments.HeapSort.popMaxRecursive candidate)
    (hHeap : MaxHeap heap) (hBound : heap.size ≤ bound) (hFuel : fuel ≤ heap.size)
    (hOutputDescending : output.toList.Pairwise (fun earlier later => later ≤ earlier))
    (hOutputAboveHeap : ∀ emitted, emitted ∈ output.toList →
      ∀ value, value ∈ heap.toList → value ≤ emitted)
    (predicate : Nat → Bool) :
    LeanExperiments.Verification.Sorting.Spec.Ascending
        (LeanExperiments.HeapSort.drainRecursive fuel heap output).toList ∧
      (LeanExperiments.HeapSort.drainRecursive fuel heap output).size = output.size + fuel ∧
      (LeanExperiments.HeapSort.drainRecursive fuel heap output).toList.countP predicate +
          (extractRemainder LeanExperiments.HeapSort.popMaxRecursive fuel heap).toList.countP
            predicate =
        output.toList.countP predicate + heap.toList.countP predicate := by
  have hSortedLength := drainRecursive_resume_partial_correct_of_bounded_contract
    bound fuel heap output hContract hHeap hBound hFuel hOutputDescending hOutputAboveHeap
  have hCounts := drainRecursive_resume_countP_add_remainder_countP_of_bounded_contract
    bound fuel heap output hContract hHeap hBound predicate
  exact ⟨hSortedLength.1, hSortedLength.2, hCounts⟩

/-- 実際の再帰版排出は、途中で出力した値を未出力の値より小さくしない。

未出力値は、完了抽出列で部分実行の後に現れる値に対応する。従って途中出力は
有界契約の範囲で、最大値から `fuel` 個を選んだ top-k 結果である。
-/
theorem drainRecursive_top_prefix_of_bounded_contract (bound fuel : Nat)
    (heap : Array Nat)
    (hContract : ∀ candidate, MaxHeap candidate → candidate.size ≤ bound →
      PopMaxRestCorrectFor LeanExperiments.HeapSort.popMaxRecursive candidate)
    (hHeap : MaxHeap heap) (hBound : heap.size ≤ bound)
    (hFuel : fuel ≤ heap.size) :
    ∀ selected, selected ∈
        (LeanExperiments.HeapSort.drainRecursive fuel heap #[]).toList →
      ∀ omitted, omitted ∈
        (extractMaxima LeanExperiments.HeapSort.popMaxRecursive heap.size heap).drop fuel →
        omitted ≤ selected := by
  have hDrain := drainRecursive_eq_reverse_extractMaxima fuel heap #[]
  have hTop := extractMaxima_top_prefix_of_bounded_contract
    bound fuel heap hContract hHeap hBound hFuel
  intro selected hSelected omitted hOmitted
  have hSelectedExtracted : selected ∈
      extractMaxima LeanExperiments.HeapSort.popMaxRecursive fuel heap := by
    simpa [hDrain] using hSelected
  exact hTop selected hSelectedExtracted omitted hOmitted

/-- 有界な抽出契約のもとで、再帰版排出はヒープを正しくソートする。

完了抽出列の降順性と順列保存を反転によって昇順の出力仕様へ移し、排出実装との
一致定理で `drainRecursive` 自体の正しさを得る。
-/
theorem drainRecursive_correct_of_bounded_contract (bound fuel : Nat)
    (heap : Array Nat)
    (hContract : ∀ candidate, MaxHeap candidate → candidate.size ≤ bound →
      PopMaxRestCorrectFor LeanExperiments.HeapSort.popMaxRecursive candidate)
    (hHeap : MaxHeap heap) (hBound : heap.size ≤ bound)
    (hFuel : heap.size ≤ fuel) :
    LeanExperiments.Verification.Sorting.Spec.Correct heap.toList
      (LeanExperiments.HeapSort.drainRecursive fuel heap #[]).toList := by
  have hExtract := extractMaxima_bounded_correct
    bound fuel heap hContract hHeap hBound hFuel
  have hSorted : LeanExperiments.Verification.Sorting.Spec.Ascending
      (extractMaxima LeanExperiments.HeapSort.popMaxRecursive fuel heap).reverse := by
    apply LeanExperiments.Verification.Sorting.Spec.pairwise_ascending
    exact (List.pairwise_reverse).mpr hExtract.1
  have hPerm :
      (extractMaxima LeanExperiments.HeapSort.popMaxRecursive fuel heap).reverse.Perm
        heap.toList :=
    (List.reverse_perm _).trans hExtract.2
  have hDrain := drainRecursive_eq_reverse_extractMaxima fuel heap #[]
  have hDrainList :
      (LeanExperiments.HeapSort.drainRecursive fuel heap #[]).toList =
        (extractMaxima LeanExperiments.HeapSort.popMaxRecursive fuel heap).reverse := by
    rw [hDrain]
    simp
  constructor
  · simpa [hDrainList] using hSorted
  · exact hDrainList ▸ hPerm

/-- 既存の降順出力を続きから排出すると、連結した全結果が正しくソートされる。

既存出力の値が残余ヒープの全要素以上なら、既存列と今回の降順抽出列を連結しても
降順である。反転した `drainRecursive` の結果は、両方の入力要素を保存した昇順列になる。
-/
theorem drainRecursive_resume_correct_of_bounded_contract (bound fuel : Nat)
    (heap output : Array Nat)
    (hContract : ∀ candidate, MaxHeap candidate → candidate.size ≤ bound →
      PopMaxRestCorrectFor LeanExperiments.HeapSort.popMaxRecursive candidate)
    (hHeap : MaxHeap heap) (hBound : heap.size ≤ bound)
    (hFuel : heap.size ≤ fuel)
    (hOutputDescending : output.toList.Pairwise (fun earlier later => later ≤ earlier))
    (hOutputAboveHeap : ∀ emitted, emitted ∈ output.toList →
      ∀ value, value ∈ heap.toList → value ≤ emitted) :
    LeanExperiments.Verification.Sorting.Spec.Correct
      (output.toList ++ heap.toList)
      (LeanExperiments.HeapSort.drainRecursive fuel heap output).toList := by
  let extracted := extractMaxima LeanExperiments.HeapSort.popMaxRecursive fuel heap
  have hExtract := extractMaxima_bounded_correct
    bound fuel heap hContract hHeap hBound hFuel
  have hCross : ∀ emitted, emitted ∈ output.toList →
      ∀ value, value ∈ extracted → value ≤ emitted := by
    intro emitted hEmitted value hValue
    exact hOutputAboveHeap emitted hEmitted value (hExtract.2.mem_iff.mp hValue)
  have hCombinedDescending :
      (output.toList ++ extracted).Pairwise (fun earlier later => later ≤ earlier) := by
    rw [List.pairwise_append]
    exact ⟨hOutputDescending, hExtract.1, hCross⟩
  have hSorted :
      LeanExperiments.Verification.Sorting.Spec.Ascending
        (output.toList ++ extracted).reverse := by
    apply LeanExperiments.Verification.Sorting.Spec.pairwise_ascending
    exact (List.pairwise_reverse).mpr hCombinedDescending
  have hCombinedPerm :
      (output.toList ++ extracted).Perm (output.toList ++ heap.toList) :=
    (List.Perm.refl output.toList).append hExtract.2
  have hSortedPerm :
      (output.toList ++ extracted).reverse.Perm (output.toList ++ heap.toList) :=
    (List.reverse_perm _).trans hCombinedPerm
  have hDrain := drainRecursive_eq_reverse_extractMaxima fuel heap output
  have hDrainList :
      (LeanExperiments.HeapSort.drainRecursive fuel heap output).toList =
        (output.toList ++ extracted).reverse := by
    rw [hDrain]
  constructor
  · simpa [hDrainList] using hSorted
  · exact hDrainList ▸ hSortedPerm

/-- 抽出不能なら、fuel に関係なく再帰排出は現在の出力を反転して返す。 -/
theorem drainRecursive_eq_reverse_of_popMax_none (fuel : Nat)
    (heap output : Array Nat)
    (hNone : LeanExperiments.HeapSort.popMaxRecursive heap = none) :
    LeanExperiments.HeapSort.drainRecursive fuel heap output = output.reverse := by
  induction fuel with
  | zero => simp [LeanExperiments.HeapSort.drainRecursive]
  | succ fuel ih => simp [LeanExperiments.HeapSort.drainRecursive, hNone]

set_option maxHeartbeats 1000000

/-- ループ版heap sortは、任意入力で再帰版heap sortと一致する。

残りfuel・ヒープ・降順の出力から再帰排出した結果を保つ不変条件を使う。
各反復を再帰版 `popMax` の場合分けに接続し、停止時のfuel 0から最終一致を得る。
-/
theorem heapSort_eq_heapSortRecursive (input : Array Nat) :
    LeanExperiments.HeapSort.heapSort input =
      LeanExperiments.HeapSort.heapSortRecursive input := by
  generalize hRun : LeanExperiments.HeapSort.heapSort input = result
  apply Id.of_run_eq_wp hRun
  vcgen [LeanExperiments.HeapSort.heapSort] invariants
  · fun finished state =>
      if finished then
        state.2.1.reverse = LeanExperiments.HeapSort.heapSortRecursive input
      else
        LeanExperiments.HeapSort.drainRecursive state.2.2 state.1 state.2.1 =
          LeanExperiments.HeapSort.heapSortRecursive input
  case vc1 =>
    dsimp [LeanExperiments.HeapSort.heapSortRecursive, heap, output, remaining]
    rw [buildMaxHeap_eq_buildMaxHeapRecursive]
  case vc2 =>
    simp_all
  case vc3 =>
    simp_all [Variant.evalsBelow_ofMeasure_nat, Variant.evalsTo_ofMeasure,
      Assertion.NondetFun.evalsTo_pure,
      popMax_eq_popMaxRecursive]
    rename_i currentHeap currentOutput fuel bound maximum rest invariant positive popEq
    rcases ‹_ ∧ _› with ⟨hMeasure, hInvariant⟩
    have hFuel : currentOutput = remaining + 1 := by
      dsimp [remaining]
      omega
    constructor
    · omega
    · simpa [hFuel, LeanExperiments.HeapSort.drainRecursive, popEq] using hInvariant
  case vc4 =>
    simp_all [Variant.evalsBelow_ofMeasure_nat, Variant.evalsTo_ofMeasure,
      Assertion.NondetFun.evalsTo_pure,
      popMax_eq_popMaxRecursive]
    rename_i currentHeap currentOutput fuel bound popResult invariant positive impossiblePop popEq
    rcases ‹_ ∧ _› with ⟨hMeasure, hInvariant⟩
    have hResult : popResult = none := by
      cases popResult with
      | none => rfl
      | some pair =>
          rcases pair with ⟨maximum, rest⟩
          exact False.elim (impossiblePop maximum rest rfl)
    have hFuel : currentOutput = remaining + 1 := by
      dsimp [remaining]
      omega
    constructor
    · omega
    · have hNoPop := popEq.trans hResult
      have hCurrent := drainRecursive_eq_reverse_of_popMax_none currentOutput _ currentHeap hNoPop
      rw [hCurrent] at hInvariant
      rw [drainRecursive_eq_reverse_of_popMax_none remaining _ currentHeap hNoPop]
      exact hInvariant
  case vc5 =>
    simp_all [Variant.evalsTo_ofMeasure, Assertion.NondetFun.evalsTo_pure,
      LeanExperiments.HeapSort.drainRecursive]

set_option maxHeartbeats 200000

/-- 再帰版ヒープソートの2つの実装契約から、任意長での正当性を導く。

ヒープ構築が入力を保存して最大ヒープを返し、最大ヒープ上の `popMaxRecursive` が
残余契約を満たせば、有限入力例やサイズ上限を使わずに実装結果の昇順性と順列保存が従う。
-/
theorem heapSortRecursive_correct_of_contracts (input : Array Nat)
    (hBuild : HeapBuildCorrect input
      (LeanExperiments.HeapSort.buildMaxHeapRecursive input))
    (hPop : ∀ candidate, MaxHeap candidate →
      PopMaxRestCorrectFor LeanExperiments.HeapSort.popMaxRecursive candidate) :
    LeanExperiments.Verification.Sorting.Spec.Correct input.toList
      (LeanExperiments.HeapSort.heapSortRecursive input).toList := by
  have hSort := sort_correct_of_heapBuild_and_heap_extract hBuild hPop input.size (by
    rw [buildMaxHeapRecursive_size]
    exact Nat.le_refl _)
  have hDrain := drainRecursive_eq_reverse_extractMaxima input.size
    (LeanExperiments.HeapSort.buildMaxHeapRecursive input) #[]
  simpa [LeanExperiments.HeapSort.heapSortRecursive, hDrain] using hSort

/-- 再帰版ヒープソートは任意長・任意値の入力を正しく昇順に並べ替える。 -/
theorem heapSortRecursive_correct (input : Array Nat) :
    LeanExperiments.Verification.Sorting.Spec.Correct input.toList
      (LeanExperiments.HeapSort.heapSortRecursive input).toList := by
  apply heapSortRecursive_correct_of_contracts input
  · exact buildMaxHeapRecursive_correct input
  · intro candidate hHeap
    exact (popMaxRecursiveRestCheck_correct candidate).mp
      (popMaxRecursiveRestCheck_of_maxHeap candidate hHeap)

/-- 再帰版ヒープソートの先頭 `k` 個は、任意のしきい値未満の入力要素を
`k` 個またはそのしきい値未満の入力要素数の小さい方だけ含む。重複値を含む入力でも
「最小側から `k` 個取る」という top-k の性質を正確に表す。
-/
theorem heapSortRecursive_take_countP_lt (input : Array Nat) (k threshold : Nat) :
    ((LeanExperiments.HeapSort.heapSortRecursive input).toList.take k).countP
        (fun value => decide (value < threshold)) =
      min k (input.toList.countP (fun value => decide (value < threshold))) := by
  exact LeanExperiments.Verification.Sorting.Spec.Correct.countP_take_lt
    (heapSortRecursive_correct input) k threshold

/-- 再帰版の先頭 `k` 個に含まれる、しきい値以下の値の個数を入力全体から決める。 -/
theorem heapSortRecursive_take_countP_le (input : Array Nat) (k threshold : Nat) :
    ((LeanExperiments.HeapSort.heapSortRecursive input).toList.take k).countP
        (fun value => decide (value ≤ threshold)) =
      min k (input.toList.countP (fun value => decide (value ≤ threshold))) := by
  exact LeanExperiments.Verification.Sorting.Spec.Correct.countP_take_le
    (heapSortRecursive_correct input) k threshold

/-- 再帰版の先頭 `k` 個に含まれる、しきい値より大きい値の個数を特徴付ける。 -/
theorem heapSortRecursive_take_countP_gt (input : Array Nat) (k threshold : Nat) :
    ((LeanExperiments.HeapSort.heapSortRecursive input).toList.take k).countP
        (fun value => decide (threshold < value)) =
      min (input.toList.countP (fun value => decide (threshold < value)))
        (k - input.toList.countP (fun value => decide (value ≤ threshold))) := by
  exact LeanExperiments.Verification.Sorting.Spec.Correct.countP_take_gt
    (heapSortRecursive_correct input) k threshold

/-- 再帰版の先頭 `k` 個に含まれる、しきい値以上の値の個数を特徴付ける。 -/
theorem heapSortRecursive_take_countP_ge (input : Array Nat) (k threshold : Nat) :
    ((LeanExperiments.HeapSort.heapSortRecursive input).toList.take k).countP
        (fun value => decide (threshold ≤ value)) =
      min (input.toList.countP (fun value => decide (threshold ≤ value)))
        (k - input.toList.countP (fun value => decide (value < threshold))) := by
  exact LeanExperiments.Verification.Sorting.Spec.Correct.countP_take_ge
    (heapSortRecursive_correct input) k threshold

/-- 再帰版の出力が狭義昇順であることは、入力に重複値がないことと同値である。 -/
theorem heapSortRecursive_pairwise_lt_iff_input_nodup (input : Array Nat) :
    (LeanExperiments.HeapSort.heapSortRecursive input).toList.Pairwise
        (fun left right : Nat => left < right) ↔ input.toList.Nodup := by
  exact LeanExperiments.Verification.Sorting.Spec.Correct.pairwise_lt_iff_input_nodup
    (heapSortRecursive_correct input)

/-- 任意の候補配列が再帰版ヒープソートの出力であることは、正当性と同値である。 -/
theorem heapSortRecursive_eq_iff_correct (input output : Array Nat) :
    LeanExperiments.HeapSort.heapSortRecursive input = output ↔ Correct input output := by
  constructor
  · intro hOutput
    rw [← hOutput]
    exact heapSortRecursive_correct input
  · intro hCorrect
    apply Array.toList_inj.mp
    exact LeanExperiments.Verification.Sorting.Spec.Correct.eq_of_same_input
      (heapSortRecursive_correct input) hCorrect

/-- 独立 Boolean 検査器は、再帰版ヒープソートの実出力だけを受理する。 -/
theorem correctCheck_iff_heapSortRecursive_output (input output : Array Nat) :
    correctCheck input output = true ↔
      output = LeanExperiments.HeapSort.heapSortRecursive input := by
  constructor
  · intro hCheck
    exact (heapSortRecursive_eq_iff_correct input output).2
      (correctCheck_sound input output hCheck) |>.symm
  · intro hOutput
    apply correctCheck_complete
    rw [hOutput]
    exact heapSortRecursive_correct input

/-- 任意入力に対する再帰版ヒープソート出力は、独立 Boolean 検査器に合格する。 -/
theorem heapSortRecursive_correctCheck (input : Array Nat) :
    correctCheck input (LeanExperiments.HeapSort.heapSortRecursive input) = true :=
  correctCheck_complete input _ (heapSortRecursive_correct input)

/-- 再帰版の各出力位置は、入力中の順位条件で正確に特徴付けられる。

重複値がある場合も、値より小さい入力要素数と値以下の入力要素数がその順位を決める。
-/
theorem heapSortRecursive_getElem_eq_iff_rank_bounds (input : Array Nat)
    (index : Nat) (hIndex : index <
      (LeanExperiments.HeapSort.heapSortRecursive input).toList.length) (value : Nat) :
    (LeanExperiments.HeapSort.heapSortRecursive input).toList[index] = value ↔
      input.toList.countP (fun item => decide (item < value)) ≤ index ∧
        index < input.toList.countP (fun item => decide (item ≤ value)) := by
  exact LeanExperiments.Verification.Sorting.Spec.Correct.getElem_eq_iff_rank_bounds
    (heapSortRecursive_correct input) hIndex value

/-- ループ版ヒープソートは任意長・任意値の入力を正しく昇順に並べ替える。 -/
theorem heapSort_correct (input : Array Nat) :
    LeanExperiments.Verification.Sorting.Spec.Correct input.toList
      (LeanExperiments.HeapSort.heapSort input).toList := by
  rw [heapSort_eq_heapSortRecursive]
  exact heapSortRecursive_correct input

/-- ループ版ヒープソートの先頭 `k` 個も、任意のしきい値未満の入力要素を
`k` 個またはそのしきい値未満の入力要素数の小さい方だけ含む。再帰版との一致に頼らず、
ループ版の正当性仕様から top-k の個数特性を得る。
-/
theorem heapSort_take_countP_lt (input : Array Nat) (k threshold : Nat) :
    ((LeanExperiments.HeapSort.heapSort input).toList.take k).countP
        (fun value => decide (value < threshold)) =
      min k (input.toList.countP (fun value => decide (value < threshold))) := by
  exact LeanExperiments.Verification.Sorting.Spec.Correct.countP_take_lt
    (heapSort_correct input) k threshold

/-- ループ版の先頭 `k` 個に含まれる、しきい値以下の値の個数を入力全体から決める。 -/
theorem heapSort_take_countP_le (input : Array Nat) (k threshold : Nat) :
    ((LeanExperiments.HeapSort.heapSort input).toList.take k).countP
        (fun value => decide (value ≤ threshold)) =
      min k (input.toList.countP (fun value => decide (value ≤ threshold))) := by
  exact LeanExperiments.Verification.Sorting.Spec.Correct.countP_take_le
    (heapSort_correct input) k threshold

/-- ループ版の先頭 `k` 個に含まれる、しきい値より大きい値の個数を特徴付ける。 -/
theorem heapSort_take_countP_gt (input : Array Nat) (k threshold : Nat) :
    ((LeanExperiments.HeapSort.heapSort input).toList.take k).countP
        (fun value => decide (threshold < value)) =
      min (input.toList.countP (fun value => decide (threshold < value)))
        (k - input.toList.countP (fun value => decide (value ≤ threshold))) := by
  exact LeanExperiments.Verification.Sorting.Spec.Correct.countP_take_gt
    (heapSort_correct input) k threshold

/-- ループ版の先頭 `k` 個に含まれる、しきい値以上の値の個数を特徴付ける。 -/
theorem heapSort_take_countP_ge (input : Array Nat) (k threshold : Nat) :
    ((LeanExperiments.HeapSort.heapSort input).toList.take k).countP
        (fun value => decide (threshold ≤ value)) =
      min (input.toList.countP (fun value => decide (threshold ≤ value)))
        (k - input.toList.countP (fun value => decide (value < threshold))) := by
  exact LeanExperiments.Verification.Sorting.Spec.Correct.countP_take_ge
    (heapSort_correct input) k threshold

/-- ループ版の出力が狭義昇順であることは、入力に重複値がないことと同値である。 -/
theorem heapSort_pairwise_lt_iff_input_nodup (input : Array Nat) :
    (LeanExperiments.HeapSort.heapSort input).toList.Pairwise
        (fun left right : Nat => left < right) ↔ input.toList.Nodup := by
  exact LeanExperiments.Verification.Sorting.Spec.Correct.pairwise_lt_iff_input_nodup
    (heapSort_correct input)

/-- 任意の候補配列がループ版ヒープソートの出力であることは、正当性と同値である。 -/
theorem heapSort_eq_iff_correct (input output : Array Nat) :
    LeanExperiments.HeapSort.heapSort input = output ↔ Correct input output := by
  constructor
  · intro hOutput
    rw [← hOutput]
    exact heapSort_correct input
  · intro hCorrect
    apply Array.toList_inj.mp
    exact LeanExperiments.Verification.Sorting.Spec.Correct.eq_of_same_input
      (heapSort_correct input) hCorrect

/-- 独立 Boolean 検査器は、ループ版ヒープソートの実出力だけを受理する。 -/
theorem correctCheck_iff_heapSort_output (input output : Array Nat) :
    correctCheck input output = true ↔
      output = LeanExperiments.HeapSort.heapSort input := by
  constructor
  · intro hCheck
    exact (heapSort_eq_iff_correct input output).2
      (correctCheck_sound input output hCheck) |>.symm
  · intro hOutput
    apply correctCheck_complete
    rw [hOutput]
    exact heapSort_correct input

/-- 非空入力に対するループ版の先頭要素は、入力の最小値である。 -/
theorem heapSort_head_is_minimum (input : Array Nat) (hInput : input.toList ≠ []) :
    ∃ minimum,
      (LeanExperiments.HeapSort.heapSort input).toList.head? = some minimum ∧
        minimum ∈ input.toList ∧ ∀ value ∈ input.toList, minimum ≤ value := by
  have hCorrect := heapSort_correct input
  have hOutput : (LeanExperiments.HeapSort.heapSort input).toList ≠ [] := by
    intro hEmpty
    have hLength := hCorrect.2.length_eq
    rw [hEmpty] at hLength
    cases hInputCase : input.toList with
    | nil => exact hInput hInputCase
    | cons first rest => simp [hInputCase] at hLength
  obtain ⟨minimum, rest, hRepresentation, hMem, hBound⟩ :=
    LeanExperiments.Verification.Sorting.Spec.Correct.head_is_minimum hCorrect hOutput
  refine ⟨minimum, ?_, hMem, hBound⟩
  simp [hRepresentation]

/-- 非空入力に対するループ版の末尾要素は、入力の最大値である。 -/
theorem heapSort_last_is_maximum (input : Array Nat) (hInput : input.toList ≠ []) :
    ∃ maximum,
      (LeanExperiments.HeapSort.heapSort input).toList.getLast? = some maximum ∧
        maximum ∈ input.toList ∧ ∀ value ∈ input.toList, value ≤ maximum := by
  have hCorrect := heapSort_correct input
  obtain ⟨initial, maximum, hRepresentation, hMem, hBound⟩ :=
    LeanExperiments.Verification.Sorting.Spec.Correct.last_is_maximum hCorrect hInput
  refine ⟨maximum, ?_, hMem, hBound⟩
  simp [hRepresentation]

/-- 再帰版の先頭要素も、非空入力の最小値である。 -/
theorem heapSortRecursive_head_is_minimum (input : Array Nat)
    (hInput : input.toList ≠ []) :
    ∃ minimum,
      (LeanExperiments.HeapSort.heapSortRecursive input).toList.head? = some minimum ∧
        minimum ∈ input.toList ∧ ∀ value ∈ input.toList, minimum ≤ value := by
  obtain ⟨minimum, hHead, hMem, hBound⟩ := heapSort_head_is_minimum input hInput
  refine ⟨minimum, ?_, hMem, hBound⟩
  rw [← heapSort_eq_heapSortRecursive input]
  exact hHead

/-- 再帰版の末尾要素も、非空入力の最大値である。 -/
theorem heapSortRecursive_last_is_maximum (input : Array Nat)
    (hInput : input.toList ≠ []) :
    ∃ maximum,
      (LeanExperiments.HeapSort.heapSortRecursive input).toList.getLast? = some maximum ∧
        maximum ∈ input.toList ∧ ∀ value ∈ input.toList, value ≤ maximum := by
  obtain ⟨maximum, hLast, hMem, hBound⟩ := heapSort_last_is_maximum input hInput
  refine ⟨maximum, ?_, hMem, hBound⟩
  rw [← heapSort_eq_heapSortRecursive input]
  exact hLast

/-- 配列版HeapSortをリスト共通仕様へ接続する。 -/
private def heapSortAsList (values : List Nat) : List Nat :=
  (LeanExperiments.HeapSort.heapSort values.toArray).toList

/-- ループ版HeapSortのリスト化した関数も任意入力で共通仕様を満たす。 -/
private theorem heapSortAsList_correct (values : List Nat) :
    LeanExperiments.Verification.Sorting.Spec.Correct values (heapSortAsList values) := by
  simpa [heapSortAsList] using heapSort_correct values.toArray

/-- 再帰版HeapSortをリスト共通仕様へ接続する。 -/
private def heapSortRecursiveAsList (values : List Nat) : List Nat :=
  (LeanExperiments.HeapSort.heapSortRecursive values.toArray).toList

/-- 再帰版HeapSortのリスト化した関数も任意入力で共通仕様を満たす。 -/
private theorem heapSortRecursiveAsList_correct (values : List Nat) :
    LeanExperiments.Verification.Sorting.Spec.Correct values
      (heapSortRecursiveAsList values) := by
  simpa [heapSortRecursiveAsList] using heapSortRecursive_correct values.toArray

/-- 非減少関数で各要素を写す操作は、ヒープソートと可換である。

ソートの一般正当性と出力一意性から従い、個別の変換関数や入力値に依存しない。
-/
theorem heapSort_map_of_monotone (input : Array Nat) (f : Nat → Nat)
    (hMonotone : ∀ ⦃a b⦄, a ≤ b → f a ≤ f b) :
    LeanExperiments.HeapSort.heapSort (input.map f) =
      (LeanExperiments.HeapSort.heapSort input).map f := by
  apply Array.toList_inj.mp
  have hMap : (input.toList.map f).toArray = input.map f := by
    apply Array.toList_inj.mp
    simp
  rw [← hMap]
  simpa [heapSortAsList] using
    (LeanExperiments.Verification.Sorting.Spec.Correct.sort_map
      heapSortAsList heapSortAsList_correct input.toList f hMonotone)

/-- 再帰版でも、非減少関数による写像はヒープソートと可換である。 -/
theorem heapSortRecursive_map_of_monotone (input : Array Nat) (f : Nat → Nat)
    (hMonotone : ∀ ⦃a b⦄, a ≤ b → f a ≤ f b) :
    LeanExperiments.HeapSort.heapSortRecursive (input.map f) =
      (LeanExperiments.HeapSort.heapSortRecursive input).map f := by
  apply Array.toList_inj.mp
  have hMap : (input.toList.map f).toArray = input.map f := by
    apply Array.toList_inj.mp
    simp
  rw [← hMap]
  simpa [heapSortRecursiveAsList] using
    (LeanExperiments.Verification.Sorting.Spec.Correct.sort_map
      heapSortRecursiveAsList heapSortRecursiveAsList_correct input.toList f hMonotone)

/-- 要素を条件で絞り込んでからループ版をソートする結果は、先にソートしてから絞る結果に一致する。 -/
theorem heapSort_filter (input : Array Nat) (predicate : Nat → Bool) :
    LeanExperiments.HeapSort.heapSort (input.filter predicate) =
      (LeanExperiments.HeapSort.heapSort input).filter predicate := by
  apply Array.toList_inj.mp
  have hFilter : (input.toList.filter predicate).toArray = input.filter predicate := by
    apply Array.toList_inj.mp
    simp
  rw [← hFilter]
  simpa [heapSortAsList] using
    (LeanExperiments.Verification.Sorting.Spec.Correct.sort_filter
      heapSortAsList heapSortAsList_correct input.toList predicate)

/-- 条件による絞り込みは再帰版ヒープソートとも可換である。 -/
theorem heapSortRecursive_filter (input : Array Nat) (predicate : Nat → Bool) :
    LeanExperiments.HeapSort.heapSortRecursive (input.filter predicate) =
      (LeanExperiments.HeapSort.heapSortRecursive input).filter predicate := by
  apply Array.toList_inj.mp
  have hFilter : (input.toList.filter predicate).toArray = input.filter predicate := by
    apply Array.toList_inj.mp
    simp
  rw [← hFilter]
  simpa [heapSortRecursiveAsList] using
    (LeanExperiments.Verification.Sorting.Spec.Correct.sort_filter
      heapSortRecursiveAsList heapSortRecursiveAsList_correct input.toList predicate)

/-- 連結した入力のソート結果は、各部分のソート結果を併合したものに一致する。

要素保存により部分入力のソート結果を元の連結入力と順列比較し、併合の共通正当性と
昇順出力の一意性を用いる。実装内部のヒープ状態には依存しない合成則である。
-/
theorem heapSort_append_eq_merge (left right : Array Nat) :
    LeanExperiments.HeapSort.heapSort (left ++ right) =
      (LeanExperiments.MergeSort.merge
        (LeanExperiments.HeapSort.heapSort left).toList
        (LeanExperiments.HeapSort.heapSort right).toList).toArray := by
  apply Array.toList_inj.mp
  have hAppend : (left.toList ++ right.toList).toArray = left ++ right := by
    apply Array.toList_inj.mp
    simp
  rw [← hAppend]
  simpa [heapSortAsList] using
    (LeanExperiments.Verification.MergeSort.correct_sort_append_eq_merge
      heapSortAsList heapSortAsList_correct left.toList right.toList)

/-- 再帰版でも、連結入力のソートは部分ごとのソート結果の併合と一致する。 -/
theorem heapSortRecursive_append_eq_merge (left right : Array Nat) :
    LeanExperiments.HeapSort.heapSortRecursive (left ++ right) =
      (LeanExperiments.MergeSort.merge
        (LeanExperiments.HeapSort.heapSortRecursive left).toList
        (LeanExperiments.HeapSort.heapSortRecursive right).toList).toArray := by
  apply Array.toList_inj.mp
  have hAppend : (left.toList ++ right.toList).toArray = left ++ right := by
    apply Array.toList_inj.mp
    simp
  rw [← hAppend]
  simpa [heapSortRecursiveAsList] using
    (LeanExperiments.Verification.MergeSort.correct_sort_append_eq_merge
      heapSortRecursiveAsList heapSortRecursiveAsList_correct left.toList right.toList)

/-- 再帰版ヒープソートの出力は、独立なマージソート仕様の結果と一致する。

両者が同じ昇順・順列仕様を満たすことから、有限例によらず出力そのものを比較できる。
-/
theorem heapSortRecursive_eq_mergeSort (input : Array Nat) :
    LeanExperiments.HeapSort.heapSortRecursive input =
      (LeanExperiments.MergeSort.mergeSort input.toList).toArray := by
  apply Array.toList_inj.mp
  exact LeanExperiments.Verification.Sorting.Spec.Correct.eq_of_same_input
    (heapSortRecursive_correct input)
    (LeanExperiments.Verification.MergeSort.mergeSort_correct input.toList)

/-- ループ版ヒープソートも、独立なマージソート仕様の結果と一致する。 -/
theorem heapSort_eq_mergeSort (input : Array Nat) :
    LeanExperiments.HeapSort.heapSort input =
      (LeanExperiments.MergeSort.mergeSort input.toList).toArray := by
  apply Array.toList_inj.mp
  exact LeanExperiments.Verification.Sorting.Spec.Correct.eq_of_same_input
    (heapSort_correct input)
    (LeanExperiments.Verification.MergeSort.mergeSort_correct input.toList)

/-- 任意入力に対するループ版ヒープソート出力は独立 Boolean 検査器に合格する。 -/
theorem heapSort_correctCheck (input : Array Nat) :
    correctCheck input (LeanExperiments.HeapSort.heapSort input) = true :=
  correctCheck_complete input _ (heapSort_correct input)

/-- ループ版の各出力位置は、入力中の順位条件で正確に特徴付けられる。 -/
theorem heapSort_getElem_eq_iff_rank_bounds (input : Array Nat)
    (index : Nat) (hIndex : index <
      (LeanExperiments.HeapSort.heapSort input).toList.length) (value : Nat) :
    (LeanExperiments.HeapSort.heapSort input).toList[index] = value ↔
      input.toList.countP (fun item => decide (item < value)) ≤ index ∧
        index < input.toList.countP (fun item => decide (item ≤ value)) := by
  exact LeanExperiments.Verification.Sorting.Spec.Correct.getElem_eq_iff_rank_bounds
    (heapSort_correct input) hIndex value

/-- ループ版ヒープソートの出力は、同じ要素の入力順序に依存しない。 -/
theorem heapSort_eq_of_perm_inputs {input₁ input₂ : Array Nat}
    (hPerm : input₁.toList.Perm input₂.toList) :
    LeanExperiments.HeapSort.heapSort input₁ = LeanExperiments.HeapSort.heapSort input₂ := by
  apply Array.toList_inj.mp
  simpa [heapSortAsList] using
    (LeanExperiments.Verification.Sorting.Spec.Correct.sort_eq_of_perm_inputs
      heapSortAsList heapSortAsList_correct hPerm)

/-- 再帰版ヒープソートの出力は、同じ要素の入力順序に依存しない。 -/
theorem heapSortRecursive_eq_of_perm_inputs {input₁ input₂ : Array Nat}
    (hPerm : input₁.toList.Perm input₂.toList) :
    LeanExperiments.HeapSort.heapSortRecursive input₁ =
      LeanExperiments.HeapSort.heapSortRecursive input₂ := by
  apply Array.toList_inj.mp
  simpa [heapSortRecursiveAsList] using
    (LeanExperiments.Verification.Sorting.Spec.Correct.sort_eq_of_perm_inputs
      heapSortRecursiveAsList heapSortRecursiveAsList_correct hPerm)

/-- ループ版ヒープソートを再度適用しても、整列済みの出力は変わらない。 -/
theorem heapSort_idempotent (input : Array Nat) :
    LeanExperiments.HeapSort.heapSort (LeanExperiments.HeapSort.heapSort input) =
      LeanExperiments.HeapSort.heapSort input := by
  apply Array.toList_inj.mp
  simpa [heapSortAsList] using
    (LeanExperiments.Verification.Sorting.Spec.Correct.sort_idempotent
      heapSortAsList heapSortAsList_correct input.toList)

/-- ループ版HeapSortが入力を変更しないことと、入力が昇順であることは同値。

出力の昇順性と入力要素の保存から導くため、値の重複を含む任意の配列に適用できる。
-/
theorem heapSort_eq_self_iff_ascending (input : Array Nat) :
    LeanExperiments.HeapSort.heapSort input = input ↔
      LeanExperiments.Verification.Sorting.Spec.Ascending input.toList := by
  constructor
  · intro hOutput
    simpa [hOutput] using (heapSort_correct input).1
  · intro hAscending
    apply Array.toList_inj.mp
    exact LeanExperiments.Verification.Sorting.Spec.Correct.eq_of_same_input
      (heapSort_correct input) ⟨hAscending, List.Perm.refl _⟩

/-- 再帰版ヒープソートを再度適用しても、整列済みの出力は変わらない。 -/
theorem heapSortRecursive_idempotent (input : Array Nat) :
    LeanExperiments.HeapSort.heapSortRecursive
        (LeanExperiments.HeapSort.heapSortRecursive input) =
      LeanExperiments.HeapSort.heapSortRecursive input := by
  apply Array.toList_inj.mp
  simpa [heapSortRecursiveAsList] using
    (LeanExperiments.Verification.Sorting.Spec.Correct.sort_idempotent
      heapSortRecursiveAsList heapSortRecursiveAsList_correct input.toList)

/-- 再帰版HeapSortが入力を変更しないことと、入力が昇順であることは同値。

ループ版と同じ共通仕様を使い、任意長・任意値の配列に対して特徴付ける。
-/
theorem heapSortRecursive_eq_self_iff_ascending (input : Array Nat) :
    LeanExperiments.HeapSort.heapSortRecursive input = input ↔
      LeanExperiments.Verification.Sorting.Spec.Ascending input.toList := by
  constructor
  · intro hOutput
    simpa [hOutput] using (heapSortRecursive_correct input).1
  · intro hAscending
    apply Array.toList_inj.mp
    exact LeanExperiments.Verification.Sorting.Spec.Correct.eq_of_same_input
      (heapSortRecursive_correct input) ⟨hAscending, List.Perm.refl _⟩

/-- 入力以下のサイズの最大ヒープに対する抽出契約から、再帰版ソートを証明する。

実際の排出処理では、残余ヒープのサイズは初期ヒープ以下である。この定理では
`popMaxRecursive` の契約をその到達可能なサイズ範囲に限定し、入力長に上限を設けずに
再帰版ソートの正当性を導く。
-/
theorem heapSortRecursive_correct_of_bounded_contracts (input : Array Nat)
    (hBuild : HeapBuildCorrect input
      (LeanExperiments.HeapSort.buildMaxHeapRecursive input))
    (hPop : ∀ candidate, MaxHeap candidate → candidate.size ≤ input.size →
      PopMaxRestCorrectFor LeanExperiments.HeapSort.popMaxRecursive candidate) :
    LeanExperiments.Verification.Sorting.Spec.Correct input.toList
      (LeanExperiments.HeapSort.heapSortRecursive input).toList := by
  let heap := LeanExperiments.HeapSort.buildMaxHeapRecursive input
  have hHeapSize : heap.size = input.size := HeapBuildCorrect.size_eq hBuild
  have hExtract := extractMaxima_bounded_correct input.size input.size heap
    hPop hBuild.1 (by omega) (by omega)
  have hOutput : LeanExperiments.Verification.Sorting.Spec.Correct input.toList
      (extractMaxima LeanExperiments.HeapSort.popMaxRecursive input.size heap).reverse := by
    constructor
    · apply LeanExperiments.Verification.Sorting.Spec.pairwise_ascending
      exact (List.pairwise_reverse).mpr hExtract.1
    · exact (List.reverse_perm _).trans hExtract.2 |>.trans hBuild.2
  have hDrain := drainRecursive_eq_reverse_extractMaxima input.size heap #[]
  simpa [LeanExperiments.HeapSort.heapSortRecursive, heap, hDrain] using hOutput

/-- 最大ヒープ入力では、入力サイズ以下の残余契約だけで再帰版ソートが正しい。

入力がすでに最大ヒープなので構築は恒等関数となる。従って抽出契約は、初期入力より
大きなヒープ状態について仮定する必要がない。
-/
theorem heapSortRecursive_correct_of_maxHeap_input_and_bounded_pop
    (input : Array Nat) (hInputHeap : MaxHeap input)
    (hPop : ∀ candidate, MaxHeap candidate → candidate.size ≤ input.size →
      PopMaxRestCorrectFor LeanExperiments.HeapSort.popMaxRecursive candidate) :
    LeanExperiments.Verification.Sorting.Spec.Correct input.toList
      (LeanExperiments.HeapSort.heapSortRecursive input).toList := by
  apply heapSortRecursive_correct_of_bounded_contracts input
  · exact buildMaxHeapRecursive_correct_of_maxHeapInput input hInputHeap
  · exact hPop

/-- 再帰版ヒープソートは、整列性の前提なしに任意入力の全要素を保存する。 -/
theorem heapSortRecursive_perm (input : Array Nat) :
    (LeanExperiments.HeapSort.heapSortRecursive input).toList.Perm input.toList := by
  let heap := LeanExperiments.HeapSort.buildMaxHeapRecursive input
  have hExtractPerm := extractMaxima_perm_of_enough_fuel_of_elements
    (fun candidate => popMaxRecursive_elements_correct_for_all candidate)
    input.size heap (by simp [heap, buildMaxHeapRecursive_size])
  have hPerm :
      (extractMaxima LeanExperiments.HeapSort.popMaxRecursive input.size heap).reverse.Perm
        input.toList := by
    exact (List.reverse_perm _).trans hExtractPerm |>.trans
      (buildMaxHeapRecursive_perm input)
  have hDrain := drainRecursive_eq_reverse_extractMaxima input.size heap #[]
  change (LeanExperiments.HeapSort.drainRecursive input.size heap #[]).toList.Perm _
  rw [hDrain]
  simpa [heap] using hPerm

/-- 再帰版ヒープソートの任意長での正当性は、出力昇順性だけを示せばよい。

任意入力の順列保存は既に一般定理として成立しているため、共通ソート仕様の残る条件は
昇順性である。この同値は、任意長の正当性証明を検討するときに、順列保存と昇順性の
どちらの契約が必要かを切り分ける再利用可能な形で表す。
-/
theorem heapSortRecursive_correct_iff_ascending (input : Array Nat) :
    Correct input (LeanExperiments.HeapSort.heapSortRecursive input) ↔
      LeanExperiments.Verification.Sorting.Spec.Ascending
        (LeanExperiments.HeapSort.heapSortRecursive input).toList := by
  constructor
  · exact And.left
  · intro hAscending
    exact ⟨hAscending, heapSortRecursive_perm input⟩

/-- 独立した Boolean 検査器は、任意入力で再帰版出力の昇順性を正確に判定する。

検査器の一般的な soundness/completeness と、再帰版の要素保存定理を合わせると、
検査成功と出力昇順性が同値になる。検査器は再帰版の内部処理を参照しない。
-/
theorem heapSortRecursive_check_iff_ascending (input : Array Nat) :
    correctCheck input (LeanExperiments.HeapSort.heapSortRecursive input) = true ↔
      LeanExperiments.Verification.Sorting.Spec.Ascending
        (LeanExperiments.HeapSort.heapSortRecursive input).toList := by
  rw [correctCheck_iff, heapSortRecursive_correct_iff_ascending]

/-- 再帰版ヒープソートは任意入力の配列長を保つ。 -/
theorem heapSortRecursive_size (input : Array Nat) :
    (LeanExperiments.HeapSort.heapSortRecursive input).size = input.size := by
  let heap := LeanExperiments.HeapSort.buildMaxHeapRecursive input
  have hElements : ∀ candidate,
      PopMaxElementsCorrectFor LeanExperiments.HeapSort.popMaxRecursive candidate :=
    fun candidate => popMaxRecursive_elements_correct_for_all candidate
  have hCount := extractMaxima_length_add_remainder_size_of_elements
    hElements input.size heap
  have hRemainder := extractRemainder_eq_empty_of_enough_fuel_of_elements
    hElements input.size heap (by simp [heap, buildMaxHeapRecursive_size])
  rw [hRemainder] at hCount
  have hExtractLength :
      (extractMaxima LeanExperiments.HeapSort.popMaxRecursive input.size heap).length =
        heap.size := by
    simpa using hCount
  have hDrain := drainRecursive_eq_reverse_extractMaxima input.size heap #[]
  calc
    (LeanExperiments.HeapSort.heapSortRecursive input).size =
        (extractMaxima LeanExperiments.HeapSort.popMaxRecursive input.size heap).length := by
          change (LeanExperiments.HeapSort.drainRecursive input.size heap #[]).size = _
          rw [hDrain]
          simp
    _ = heap.size := hExtractLength
    _ = input.size := by simp [heap, buildMaxHeapRecursive_size]

/-- 再帰版ヒープソートは任意入力の自然数値の総和を保つ。 -/
theorem heapSortRecursive_sum (input : Array Nat) :
    (LeanExperiments.HeapSort.heapSortRecursive input).toList.sum = input.toList.sum := by
  let heap := LeanExperiments.HeapSort.buildMaxHeapRecursive input
  have hElements : ∀ candidate,
      PopMaxElementsCorrectFor LeanExperiments.HeapSort.popMaxRecursive candidate :=
    fun candidate => popMaxRecursive_elements_correct_for_all candidate
  have hAccumulated := extractMaxima_sum_add_remainder_sum_of_elements
    hElements input.size heap
  have hRemainder := extractRemainder_eq_empty_of_enough_fuel_of_elements
    hElements input.size heap (by simp [heap, buildMaxHeapRecursive_size])
  rw [hRemainder] at hAccumulated
  have hExtractSum :
      (extractMaxima LeanExperiments.HeapSort.popMaxRecursive input.size heap).sum =
        heap.toList.sum := by
    simpa using hAccumulated
  have hDrain := drainRecursive_eq_reverse_extractMaxima input.size heap #[]
  calc
    (LeanExperiments.HeapSort.heapSortRecursive input).toList.sum =
        (extractMaxima LeanExperiments.HeapSort.popMaxRecursive input.size heap).sum := by
          simp [LeanExperiments.HeapSort.heapSortRecursive, heap, hDrain]
    _ = heap.toList.sum := hExtractSum
    _ = input.toList.sum := buildMaxHeapRecursive_sum input

/-- 再帰版ヒープソートは、任意の Boolean 条件を満たす要素数を任意長で保つ。

値ごとの重複数だけでなく、しきい値や分類条件に該当する要素数も要素順列保存から従う。
昇順性を主張する定理とは独立に、順列保存だけから任意の分類条件について導ける。
この定理自体にも入力長の制限はない。
-/
theorem heapSortRecursive_countP (input : Array Nat) (predicate : Nat → Bool) :
    (LeanExperiments.HeapSort.heapSortRecursive input).toList.countP predicate =
      input.toList.countP predicate := by
  exact heapSortRecursive_perm input |>.countP_eq predicate

/-- ループ版ヒープソートは、任意の Boolean 条件を満たす要素数を任意長で保つ。

昇順性や有限領域の仮定を必要とせず、重複数や値の分類ごとの個数を直接比較できる。
-/
theorem heapSort_countP (input : Array Nat) (predicate : Nat → Bool) :
    (LeanExperiments.HeapSort.heapSort input).toList.countP predicate =
      input.toList.countP predicate := by
  rw [heapSort_eq_heapSortRecursive]
  exact heapSortRecursive_countP input predicate

/-- ループ版ヒープソートは任意入力の配列長を保つ。 -/
theorem heapSort_size (input : Array Nat) :
    (LeanExperiments.HeapSort.heapSort input).size = input.size := by
  rw [heapSort_eq_heapSortRecursive]
  exact heapSortRecursive_size input

/-- ループ版ヒープソートは任意入力の自然数値の総和を保つ。 -/
theorem heapSort_sum (input : Array Nat) :
    (LeanExperiments.HeapSort.heapSort input).toList.sum = input.toList.sum := by
  rw [heapSort_eq_heapSortRecursive]
  exact heapSortRecursive_sum input

/-- 長さ6以下では、再帰版ヒープソートが任意の自然数配列を正しくソートする。

値を有限列挙した検査ではなく、入力長だけを6以下に制限した一般定理である。
-/
theorem heapSortRecursive_correct_of_size_le_six (input : Array Nat)
    (hSize : input.size ≤ 6) :
    LeanExperiments.Verification.Sorting.Spec.Correct input.toList
      (LeanExperiments.HeapSort.heapSortRecursive input).toList := by
  let heap := LeanExperiments.HeapSort.buildMaxHeapRecursive input
  have hBuild := buildMaxHeapRecursive_correct_of_size_le_six input hSize
  have hHeapSize : heap.size = input.size := by
    simp [heap, buildMaxHeapRecursive_size]
  have hExtract := extractMaxima_bounded_correct input.size input.size heap
    (fun candidate hCandidateHeap hCandidateSize =>
      popMaxRecursiveRestCorrect_of_maxHeap_and_size_le_six candidate
        hCandidateHeap (by omega))
    hBuild.1 (by omega) (by omega)
  have hOutput : LeanExperiments.Verification.Sorting.Spec.Correct input.toList
      (extractMaxima LeanExperiments.HeapSort.popMaxRecursive input.size heap).reverse := by
    constructor
    · apply LeanExperiments.Verification.Sorting.Spec.pairwise_ascending
      exact (List.pairwise_reverse).mpr hExtract.1
    · exact (List.reverse_perm _).trans hExtract.2 |>.trans hBuild.2
  have hDrain := drainRecursive_eq_reverse_extractMaxima input.size heap #[]
  simpa [LeanExperiments.HeapSort.heapSortRecursive, heap, hDrain] using hOutput

/-- 長さ7以下では、再帰版ヒープソートが任意の自然数配列を正しくソートする。

長さ7以下のヒープ構築定理と、最大ヒープかつサイズ7以下での抽出残余契約を合成する。
値の範囲を有限列挙せず、自然数値全体について成立する。
-/
theorem heapSortRecursive_correct_of_size_le_seven (input : Array Nat)
    (hSize : input.size ≤ 7) :
    LeanExperiments.Verification.Sorting.Spec.Correct input.toList
      (LeanExperiments.HeapSort.heapSortRecursive input).toList := by
  let heap := LeanExperiments.HeapSort.buildMaxHeapRecursive input
  have hBuild := buildMaxHeapRecursive_correct_of_size_le_seven input hSize
  have hHeapSize : heap.size = input.size := by
    simp [heap, buildMaxHeapRecursive_size]
  have hExtract := extractMaxima_bounded_correct input.size input.size heap
    (fun candidate hCandidateHeap hCandidateSize =>
      popMaxRecursiveRestCorrect_of_maxHeap_and_size_le_seven candidate
        hCandidateHeap (by omega))
    hBuild.1 (by omega) (by omega)
  have hOutput : LeanExperiments.Verification.Sorting.Spec.Correct input.toList
      (extractMaxima LeanExperiments.HeapSort.popMaxRecursive input.size heap).reverse := by
    constructor
    · apply LeanExperiments.Verification.Sorting.Spec.pairwise_ascending
      exact (List.pairwise_reverse).mpr hExtract.1
    · exact (List.reverse_perm _).trans hExtract.2 |>.trans hBuild.2
  have hDrain := drainRecursive_eq_reverse_extractMaxima input.size heap #[]
  simpa [LeanExperiments.HeapSort.heapSortRecursive, heap, hDrain] using hOutput

/-- 長さ8以下では、再帰版ヒープソートが任意の自然数配列を正しくソートする。

長さ8以下のヒープ構築定理と、最大ヒープかつサイズ9以下での抽出残余契約を合成する。
値の範囲を有限列挙せず、自然数値全体について成立する。
-/
theorem heapSortRecursive_correct_of_size_le_eight (input : Array Nat)
    (hSize : input.size ≤ 8) :
    LeanExperiments.Verification.Sorting.Spec.Correct input.toList
      (LeanExperiments.HeapSort.heapSortRecursive input).toList := by
  let heap := LeanExperiments.HeapSort.buildMaxHeapRecursive input
  have hBuild := buildMaxHeapRecursive_correct_of_size_le_eight input hSize
  have hHeapSize : heap.size = input.size := by
    simp [heap, buildMaxHeapRecursive_size]
  have hExtract := extractMaxima_bounded_correct input.size input.size heap
    (fun candidate hCandidateHeap hCandidateSize =>
      popMaxRecursiveRestCorrect_of_maxHeap_and_size_le_nine candidate
        hCandidateHeap (by omega))
    hBuild.1 (by omega) (by omega)
  have hOutput : LeanExperiments.Verification.Sorting.Spec.Correct input.toList
      (extractMaxima LeanExperiments.HeapSort.popMaxRecursive input.size heap).reverse := by
    constructor
    · apply LeanExperiments.Verification.Sorting.Spec.pairwise_ascending
      exact (List.pairwise_reverse).mpr hExtract.1
    · exact (List.reverse_perm _).trans hExtract.2 |>.trans hBuild.2
  have hDrain := drainRecursive_eq_reverse_extractMaxima input.size heap #[]
  simpa [LeanExperiments.HeapSort.heapSortRecursive, heap, hDrain] using hOutput

/-- 長さ9以下では、構築結果が最大ヒープなら再帰版ソートが正しい。

値の範囲を制限しない。任意長の要素保存、構築の順列保存、最大ヒープ上でサイズ9以下の
抽出残余契約を合成する分解定理である。後続の任意長正当性定理では、構築後の最大ヒープ性も
含めて実装契約を合成する。
-/
theorem heapSortRecursive_correct_of_size_le_nine_and_builder_maxHeap
    (input : Array Nat) (hSize : input.size ≤ 9)
    (hBuildHeap : MaxHeap (LeanExperiments.HeapSort.buildMaxHeapRecursive input)) :
    LeanExperiments.Verification.Sorting.Spec.Correct input.toList
      (LeanExperiments.HeapSort.heapSortRecursive input).toList := by
  apply heapSortRecursive_correct_of_bounded_contracts input
  · exact ⟨hBuildHeap, buildMaxHeapRecursive_perm input⟩
  · intro candidate hCandidateHeap hCandidateSize
    exact popMaxRecursiveRestCorrect_of_maxHeap_and_size_le_nine
      candidate hCandidateHeap (by omega)

/-- 根が入力最大値である長さ9の任意配列は、再帰版ヒープソートで正しく並ぶ。

根より下を先にヒープ化すると左右の部分木が最大ヒープになり、根は入力最大値のまま
なので最後の下降処理は不要となる。その構築結果と長さ9以下の抽出契約を合成する。
-/
theorem heapSortRecursive_correct_of_size_eq_nine_of_root_maximum
    (input : Array Nat) (hSize : input.size = 9)
    (hRootMaximum : ∀ value, value ∈ input.toList → value ≤ input[0]!) :
    LeanExperiments.Verification.Sorting.Spec.Correct input.toList
      (LeanExperiments.HeapSort.heapSortRecursive input).toList := by
  apply heapSortRecursive_correct_of_size_le_nine_and_builder_maxHeap
    input (by omega)
  exact (buildMaxHeapRecursive_correct_of_size_eq_nine_of_root_maximum
    input hSize hRootMaximum).1

/-- 長さ9以下で根が入力最大値なら、再帰版ヒープソートは正しい。

長さ8以下では任意入力の既存証明を使い、長さ9の場合だけ根最大条件から構築後の
最大ヒープ条件を導いて抽出契約と合成する。
-/
theorem heapSortRecursive_correct_of_size_le_nine_of_root_maximum
    (input : Array Nat) (hSize : input.size ≤ 9)
    (hRootMaximum : ∀ value, value ∈ input.toList → value ≤ input[0]!) :
    LeanExperiments.Verification.Sorting.Spec.Correct input.toList
      (LeanExperiments.HeapSort.heapSortRecursive input).toList := by
  apply heapSortRecursive_correct_of_size_le_nine_and_builder_maxHeap input hSize
  exact (buildMaxHeapRecursive_correct_of_size_le_nine_of_root_maximum
    input hSize hRootMaximum).1

/-- 長さ9で最後の根下降が固定点になるなら、再帰版ヒープソートは正しい。

根の直下以外の部分木条件は構築処理から証明し、根が子以上という残りの条件を仮定する。
入力全体の根最大性より弱い、構築段階に直接対応した合成契約である。
-/
theorem heapSortRecursive_correct_of_size_eq_nine_of_root_step
    (input : Array Nat) (hSize : input.size = 9)
    (hRootStep :
      let stage3 := LeanExperiments.HeapSort.siftDownRecursive input 3
      let stage2 := LeanExperiments.HeapSort.siftDownRecursive stage3 2
      let stage1 := LeanExperiments.HeapSort.siftDownRecursive stage2 1
      stage1[1]! ≤ stage1[0]! ∧ stage1[2]! ≤ stage1[0]!) :
    LeanExperiments.Verification.Sorting.Spec.Correct input.toList
      (LeanExperiments.HeapSort.heapSortRecursive input).toList := by
  apply heapSortRecursive_correct_of_size_le_nine_and_builder_maxHeap input (by omega)
  exact (buildMaxHeapRecursive_correct_of_size_eq_nine_of_root_step
    input hSize hRootStep).1

/-- 長さ9以下で最後の根下降が固定点なら、再帰版ヒープソートは正しい。

長さ8以下では無条件の正当性定理を使い、長さ9の場合にだけ、下位段階を処理した後の
根がその左右の子以上という条件を要求する。
-/
theorem heapSortRecursive_correct_of_size_le_nine_of_root_step
    (input : Array Nat) (hSize : input.size ≤ 9)
    (hRootStep :
      let stage3 := LeanExperiments.HeapSort.siftDownRecursive input 3
      let stage2 := LeanExperiments.HeapSort.siftDownRecursive stage3 2
      let stage1 := LeanExperiments.HeapSort.siftDownRecursive stage2 1
      stage1[1]! ≤ stage1[0]! ∧ stage1[2]! ≤ stage1[0]!) :
    LeanExperiments.Verification.Sorting.Spec.Correct input.toList
      (LeanExperiments.HeapSort.heapSortRecursive input).toList := by
  by_cases hSmall : input.size ≤ 8
  · exact heapSortRecursive_correct_of_size_le_eight input hSmall
  · have hSizeEq : input.size = 9 := by omega
    exact heapSortRecursive_correct_of_size_eq_nine_of_root_step
      input hSizeEq hRootStep

/-- 長さ4以下では、再帰版ヒープソートが任意の自然数配列を正しくソートする。 -/
theorem heapSortRecursive_correct_of_size_le_four (input : Array Nat)
    (hSize : input.size ≤ 4) :
    LeanExperiments.Verification.Sorting.Spec.Correct input.toList
      (LeanExperiments.HeapSort.heapSortRecursive input).toList :=
  heapSortRecursive_correct_of_size_le_six input (by omega)

/-- 長さ7以下の最大ヒープ入力は、再帰版ヒープソートで正しく並ぶ。

構築処理は最大ヒープを変更しない。以後の抽出は、各残余が最大ヒープである不変条件と
サイズ上限7の残余契約を使って完了する。
-/
theorem heapSortRecursive_correct_of_maxHeap_input_size_le_seven
    (input : Array Nat) (hInputHeap : MaxHeap input) (hSize : input.size ≤ 7) :
    LeanExperiments.Verification.Sorting.Spec.Correct input.toList
      (LeanExperiments.HeapSort.heapSortRecursive input).toList := by
  let heap := LeanExperiments.HeapSort.buildMaxHeapRecursive input
  have hBuild := buildMaxHeapRecursive_correct_of_maxHeapInput input hInputHeap
  have hHeapEq : heap = input := by
    simp [heap, buildMaxHeapRecursive_eq_self_of_maxHeap input hInputHeap]
  have hExtract := extractMaxima_bounded_correct input.size input.size heap
    (fun candidate hCandidateHeap hCandidateSize =>
      popMaxRecursiveRestCorrect_of_maxHeap_and_size_le_seven candidate
        hCandidateHeap (by omega))
    hBuild.1 (by simp [hHeapEq]) (by simp [hHeapEq])
  have hOutput : LeanExperiments.Verification.Sorting.Spec.Correct input.toList
      (extractMaxima LeanExperiments.HeapSort.popMaxRecursive input.size heap).reverse := by
    constructor
    · apply LeanExperiments.Verification.Sorting.Spec.pairwise_ascending
      exact (List.pairwise_reverse).mpr hExtract.1
    · exact (List.reverse_perm _).trans hExtract.2 |>.trans hBuild.2
  have hDrain := drainRecursive_eq_reverse_extractMaxima input.size heap #[]
  simpa [LeanExperiments.HeapSort.heapSortRecursive, heap, hDrain] using hOutput

/-- 長さ8以下の最大ヒープ入力は、再帰版ヒープソートで正しく並ぶ。

最大ヒープ上の再帰版抽出残余契約を、最大ヒープを変更しない構築処理と合成する。
-/
theorem heapSortRecursive_correct_of_maxHeap_input_size_le_eight
    (input : Array Nat) (hInputHeap : MaxHeap input) (hSize : input.size ≤ 8) :
    LeanExperiments.Verification.Sorting.Spec.Correct input.toList
      (LeanExperiments.HeapSort.heapSortRecursive input).toList := by
  let heap := LeanExperiments.HeapSort.buildMaxHeapRecursive input
  have hBuild := buildMaxHeapRecursive_correct_of_maxHeapInput input hInputHeap
  have hHeapEq : heap = input := by
    simp [heap, buildMaxHeapRecursive_eq_self_of_maxHeap input hInputHeap]
  have hExtract := extractMaxima_bounded_correct input.size input.size heap
    (fun candidate hCandidateHeap hCandidateSize =>
      popMaxRecursiveRestCorrect_of_maxHeap_and_size_le_eight candidate
        hCandidateHeap (by omega))
    hBuild.1 (by simp [hHeapEq]) (by simp [hHeapEq])
  have hOutput : LeanExperiments.Verification.Sorting.Spec.Correct input.toList
      (extractMaxima LeanExperiments.HeapSort.popMaxRecursive input.size heap).reverse := by
    constructor
    · apply LeanExperiments.Verification.Sorting.Spec.pairwise_ascending
      exact (List.pairwise_reverse).mpr hExtract.1
    · exact (List.reverse_perm _).trans hExtract.2 |>.trans hBuild.2
  have hDrain := drainRecursive_eq_reverse_extractMaxima input.size heap #[]
  simpa [LeanExperiments.HeapSort.heapSortRecursive, heap, hDrain] using hOutput

/-- 長さ9以下の最大ヒープ入力は、再帰版ヒープソートで正しく並ぶ。 -/
theorem heapSortRecursive_correct_of_maxHeap_input_size_le_nine
    (input : Array Nat) (hInputHeap : MaxHeap input) (hSize : input.size ≤ 9) :
    LeanExperiments.Verification.Sorting.Spec.Correct input.toList
      (LeanExperiments.HeapSort.heapSortRecursive input).toList := by
  let heap := LeanExperiments.HeapSort.buildMaxHeapRecursive input
  have hBuild := buildMaxHeapRecursive_correct_of_maxHeapInput input hInputHeap
  have hHeapEq : heap = input := by
    simp [heap, buildMaxHeapRecursive_eq_self_of_maxHeap input hInputHeap]
  have hExtract := extractMaxima_bounded_correct input.size input.size heap
    (fun candidate hCandidateHeap hCandidateSize =>
      popMaxRecursiveRestCorrect_of_maxHeap_and_size_le_nine candidate
        hCandidateHeap (by omega))
    hBuild.1 (by simp [hHeapEq]) (by simp [hHeapEq])
  have hOutput : LeanExperiments.Verification.Sorting.Spec.Correct input.toList
      (extractMaxima LeanExperiments.HeapSort.popMaxRecursive input.size heap).reverse := by
    constructor
    · apply LeanExperiments.Verification.Sorting.Spec.pairwise_ascending
      exact (List.pairwise_reverse).mpr hExtract.1
    · exact (List.reverse_perm _).trans hExtract.2 |>.trans hBuild.2
  have hDrain := drainRecursive_eq_reverse_extractMaxima input.size heap #[]
  simpa [LeanExperiments.HeapSort.heapSortRecursive, heap, hDrain] using hOutput

/-- 同じ入力を正しくソートした二つの出力配列は一致する。 -/
theorem Correct.eq_of_same_input {input output₁ output₂ : Array Nat}
    (h₁ : Correct input output₁) (h₂ : Correct input output₂) :
    output₁ = output₂ := by
  apply Array.toList_inj.mp
  exact LeanExperiments.Verification.Sorting.Spec.Correct.eq_of_same_input
    h₁ h₂

/-- 正しい配列ソート結果が一致することと、入力配列が同じ多重集合を持つことは同値。

配列仕様を共通リスト仕様へ移し、異なる入力・異なる実装の結果比較にも使える形で
特徴付ける。 -/
theorem Correct.perm_iff_eq_output {input₁ input₂ output₁ output₂ : Array Nat}
    (h₁ : Correct input₁ output₁) (h₂ : Correct input₂ output₂) :
    input₁.toList.Perm input₂.toList ↔ output₁ = output₂ := by
  constructor
  · intro hInputs
    apply Array.toList_inj.mp
    exact (LeanExperiments.Verification.Sorting.Spec.Correct.perm_iff_eq_output
      h₁ h₂).mp hInputs
  · intro hOutputs
    exact (LeanExperiments.Verification.Sorting.Spec.Correct.perm_iff_eq_output
      h₁ h₂).mpr (congrArg Array.toList hOutputs)

/-- ループ版 HeapSort の二つの出力が一致するのは、入力配列が順列のときに限る。 -/
theorem heapSort_eq_iff_input_perm {input₁ input₂ : Array Nat} :
    LeanExperiments.HeapSort.heapSort input₁ = LeanExperiments.HeapSort.heapSort input₂ ↔
      input₁.toList.Perm input₂.toList := by
  exact (Correct.perm_iff_eq_output
    (heapSort_correct input₁) (heapSort_correct input₂)).symm

/-- 再帰版 HeapSort にも、出力一致と入力順列の同値性が成り立つ。 -/
theorem heapSortRecursive_eq_iff_input_perm {input₁ input₂ : Array Nat} :
    LeanExperiments.HeapSort.heapSortRecursive input₁ =
      LeanExperiments.HeapSort.heapSortRecursive input₂ ↔
        input₁.toList.Perm input₂.toList := by
  exact (Correct.perm_iff_eq_output
    (heapSortRecursive_correct input₁) (heapSortRecursive_correct input₂)).symm

/-- ループ版と再帰版をまたいでも、出力一致は入力順列と同値。 -/
theorem heapSort_eq_heapSortRecursive_iff_input_perm {input₁ input₂ : Array Nat} :
    LeanExperiments.HeapSort.heapSort input₁ =
      LeanExperiments.HeapSort.heapSortRecursive input₂ ↔
        input₁.toList.Perm input₂.toList := by
  exact (Correct.perm_iff_eq_output
    (heapSort_correct input₁) (heapSortRecursive_correct input₂)).symm

/-- 同じ入力に対して二つの出力が Boolean 検査を通れば、出力配列は一致する。 -/
theorem outputs_eq_of_correctCheck {input output₁ output₂ : Array Nat}
    (h₁ : correctCheck input output₁ = true)
    (h₂ : correctCheck input output₂ = true) : output₁ = output₂ :=
  Correct.eq_of_same_input (correctCheck_sound input output₁ h₁)
    (correctCheck_sound input output₂ h₂)

end LeanExperiments.Verification.HeapSort.Spec
