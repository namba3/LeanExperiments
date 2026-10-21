import LeanExperiments.HeapSort
import LeanExperiments.Verification.MergeSort.Spec
import LeanExperiments.Verification.Sorting.Spec
import Std.WP
import Std.Tactic.Do
import LeanExperiments.Verification.HeapSort.HeapOperations

/-!
# ヒープソートの構築・抽出・一般正当性証明

`HeapOperations.lean` のヒープ仕様と操作契約を使い、ヒープ構築、最大値抽出、
再帰版・ループ版の任意入力正当性を合成する。有限確認は `FiniteChecks.lean` に置く。 -/

namespace LeanExperiments.Verification.HeapSort.Spec

open Std.WP Lean.Order
set_option experimental.vcgen true

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
