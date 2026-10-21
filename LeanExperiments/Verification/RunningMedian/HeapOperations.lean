import LeanExperiments.RunningMedian
import LeanExperiments.HeapSort
import LeanExperiments.Verification.MergeSort.Spec
import LeanExperiments.Verification.HeapSort.Spec
import Std.WP
import Std.Tactic.Do
import LeanExperiments.Verification.RunningMedian.Operations
import LeanExperiments.Verification.RunningMedian.MedianSpec
import LeanExperiments.Verification.RunningMedian.HeapInvariant


/-! # 最大・最小ヒープ操作と再平衡契約

最大・最小優先関数、挿入と下降調整の順序保存、根の抽出、二つのヒープ間の
移送および再平衡についての契約をまとめる。 -/

namespace LeanExperiments.Verification.RunningMedian

open Std.WP Lean.Order
set_option experimental.vcgen true

/-- 最大ヒープ用の優先関数。候補値が現在値より大きいときに `true` を返す。 -/
def maxPrefer (candidate current : Nat) : Bool := current < candidate

/-- 最小ヒープ用の優先関数。候補値が現在値より小さいときに `true` を返す。 -/
def minPrefer (candidate current : Nat) : Bool := candidate < current


/-- 最大優先関係の「優先されない」は推移的である。 -/
theorem maxPrefer_not_transitive {first second third : Nat}
    (hFirst : maxPrefer first second = false)
    (hSecond : maxPrefer second third = false) :
    maxPrefer first third = false := by
  simp [maxPrefer] at *
  omega

/-- 最小優先関係の「優先されない」は推移的である。 -/
theorem minPrefer_not_transitive {first second third : Nat}
    (hFirst : minPrefer first second = false)
    (hSecond : minPrefer second third = false) :
    minPrefer first third = false := by
  simp [minPrefer] at *
  omega

/-- 最大優先関係は反射的に自分自身を優先しない。 -/
theorem maxPrefer_irrefl (value : Nat) : maxPrefer value value = false := by
  simp [maxPrefer]

/-- 最小優先関係は反射的に自分自身を優先しない。 -/
theorem minPrefer_irrefl (value : Nat) : minPrefer value value = false := by
  simp [minPrefer]

/-- 最大優先関係は、優先方向を反転させた比較を同時には満たさない。 -/
theorem maxPrefer_asymmetric {child parent : Nat}
    (hPrefer : maxPrefer child parent = true) : maxPrefer parent child = false := by
  simp [maxPrefer] at *
  omega

/-- 最大優先関係の真の比較は推移する。 -/
theorem maxPrefer_transitive {first second third : Nat}
    (hFirst : maxPrefer first second = true)
    (hSecond : maxPrefer second third = true) : maxPrefer first third = true := by
  simp [maxPrefer] at *
  omega

/-- 最小優先関係は、優先方向を反転させた比較を同時には満たさない。 -/
theorem minPrefer_asymmetric {child parent : Nat}
    (hPrefer : minPrefer child parent = true) : minPrefer parent child = false := by
  simp [minPrefer] at *
  omega

/-- 最小優先関係の真の比較は推移する。 -/
theorem minPrefer_transitive {first second third : Nat}
    (hFirst : minPrefer first second = true)
    (hSecond : minPrefer second third = true) : minPrefer first third = true := by
  simp [minPrefer] at *
  omega

/-- 任意の最大ヒープへの挿入は、要素数に依存せず最大ヒープ順序を保つ。 -/
theorem insertHeap_maxPrefer_preserves (heap : Array Nat)
    (hHeap : HeapOrdered maxPrefer heap) (value : Nat) :
    HeapOrdered maxPrefer
      (LeanExperiments.RunningMedian.insertHeap LeanExperiments.RunningMedian.maxPrefer
        heap value) := by
  have hInitial := HeapOrdered.push_siftUp_initial_invariant maxPrefer heap value hHeap
  have hSift := siftUp_heapOrdered_of_initial_invariant maxPrefer (heap.push value)
    heap.size (by simp) hInitial
    (fun child parent h => maxPrefer_asymmetric h)
    (fun first second third hFirst hSecond => maxPrefer_transitive hFirst hSecond)
    (fun element => maxPrefer_irrefl element)
    (fun first second third hFirst hSecond => maxPrefer_not_transitive hFirst hSecond)
  change HeapOrdered maxPrefer
    (LeanExperiments.RunningMedian.siftUp maxPrefer (heap.push value)
      ((heap.push value).size - 1))
  rw [show (heap.push value).size - 1 = heap.size by simp]
  exact hSift

/-- 任意の最小ヒープへの挿入は、要素数に依存せず最小ヒープ順序を保つ。 -/
theorem insertHeap_minPrefer_preserves (heap : Array Nat)
    (hHeap : HeapOrdered minPrefer heap) (value : Nat) :
    HeapOrdered minPrefer
      (LeanExperiments.RunningMedian.insertHeap LeanExperiments.RunningMedian.minPrefer
        heap value) := by
  have hInitial := HeapOrdered.push_siftUp_initial_invariant minPrefer heap value hHeap
  have hSift := siftUp_heapOrdered_of_initial_invariant minPrefer (heap.push value)
    heap.size (by simp) hInitial
    (fun child parent h => minPrefer_asymmetric h)
    (fun first second third hFirst hSecond => minPrefer_transitive hFirst hSecond)
    (fun element => minPrefer_irrefl element)
    (fun first second third hFirst hSecond => minPrefer_not_transitive hFirst hSecond)
  change HeapOrdered minPrefer
    (LeanExperiments.RunningMedian.siftUp minPrefer (heap.push value)
      ((heap.push value).size - 1))
  rw [show (heap.push value).size - 1 = heap.size by simp]
  exact hSift

/-- 深さ1の子が親より優先される場合、`siftUp` はその1辺を交換して根で止まる。 -/
theorem siftUp_one_step {prefer : Nat → Nat → Bool} (heap : Array Nat)
    (hSize : 1 < heap.size) (hPrefer : prefer heap[1]! heap[0]! = true) :
    LeanExperiments.RunningMedian.siftUp prefer heap 1 =
      LeanExperiments.RunningMedian.swap heap 1 0 := by
  generalize hRun : LeanExperiments.RunningMedian.siftUp prefer heap 1 = result
  apply Id.of_run_eq_wp hRun
  vcgen [LeanExperiments.RunningMedian.siftUp] invariants
  case inv1 => exact fun exit state =>
    if exit then state = (LeanExperiments.RunningMedian.swap heap 1 0, 0)
    else state = (heap, 1) ∨ state = (LeanExperiments.RunningMedian.swap heap 1 0, 0)
  case vc1 => simp
  case vc2 => simp_all <;> omega
  case vc3 =>
    simp_all [Variant.evalsBelow_ofMeasure_nat, Variant.evalsTo_ofMeasure,
      Assertion.NondetFun.evalsTo_pure]
    rename_i current index measure invariant hPositive hCompare
    rcases invariant with ⟨rfl, hInvariant⟩
    rcases hInvariant with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp [values, parent]
    · omega
  case vc4 =>
    simp_all [Variant.evalsTo_ofMeasure, Assertion.NondetFun.evalsTo_pure]
    rename_i current index measure invariant hPositive hNoCompare
    rcases invariant with ⟨rfl, hInvariant⟩
    rcases hInvariant with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp_all [parent]
    · simp_all
  case vc5 => simp_all

/-- 深さ1の右子が根より優先される場合も、その1辺を交換して根で止まる。 -/
theorem siftUp_rightChild_one_step {prefer : Nat → Nat → Bool} (heap : Array Nat)
    (hSize : 2 < heap.size) (hPrefer : prefer heap[2]! heap[0]! = true) :
    LeanExperiments.RunningMedian.siftUp prefer heap 2 =
      LeanExperiments.RunningMedian.swap heap 2 0 := by
  generalize hRun : LeanExperiments.RunningMedian.siftUp prefer heap 2 = result
  apply Id.of_run_eq_wp hRun
  vcgen [LeanExperiments.RunningMedian.siftUp] invariants
  case inv1 => exact fun exit state =>
    if exit then state = (LeanExperiments.RunningMedian.swap heap 2 0, 0)
    else state = (heap, 2) ∨ state = (LeanExperiments.RunningMedian.swap heap 2 0, 0)
  case vc1 => simp
  case vc2 => simp_all <;> omega
  case vc3 =>
    simp_all [Variant.evalsBelow_ofMeasure_nat, Variant.evalsTo_ofMeasure,
      Assertion.NondetFun.evalsTo_pure]
    rename_i current index measure invariant hPositive hCompare
    rcases invariant with ⟨rfl, hInvariant⟩
    rcases hInvariant with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp [values, parent]
    · omega
  case vc4 =>
    simp_all [Variant.evalsTo_ofMeasure, Assertion.NondetFun.evalsTo_pure]
    rename_i current index measure invariant hPositive hNoCompare
    rcases invariant with ⟨rfl, hInvariant⟩
    rcases hInvariant with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp_all [parent]
    · simp_all
  case vc5 => simp_all

/-- 添字3の値が親と根の両方より優先されると、`siftUp` は2回交換して根で止まる。 -/
theorem siftUp_leftGrandchild_two_steps {prefer : Nat → Nat → Bool} (heap : Array Nat)
    (hSize : 3 < heap.size)
    (hParent : prefer heap[3]! heap[1]! = true)
    (hRoot : prefer heap[3]! heap[0]! = true) :
    LeanExperiments.RunningMedian.siftUp prefer heap 3 =
      LeanExperiments.RunningMedian.swap
        (LeanExperiments.RunningMedian.swap heap 3 1) 1 0 := by
  generalize hRun : LeanExperiments.RunningMedian.siftUp prefer heap 3 = result
  apply Id.of_run_eq_wp hRun
  vcgen [LeanExperiments.RunningMedian.siftUp] invariants
  case inv1 => exact fun exit state =>
    if exit then
      state = (LeanExperiments.RunningMedian.swap
        (LeanExperiments.RunningMedian.swap heap 3 1) 1 0, 0)
    else
      state = (heap, 3) ∨
        state = (LeanExperiments.RunningMedian.swap heap 3 1, 1) ∨
        state = (LeanExperiments.RunningMedian.swap
          (LeanExperiments.RunningMedian.swap heap 3 1) 1 0, 0)
  case vc1 => simp
  case vc2 => simp_all <;> omega
  case vc3 =>
    simp_all [Variant.evalsBelow_ofMeasure_nat, Variant.evalsTo_ofMeasure,
      Assertion.NondetFun.evalsTo_pure]
    rename_i current index measure invariant hPositive hCompare
    rcases invariant with ⟨rfl, hInvariant⟩
    rcases hInvariant with hStart | hMore
    · rcases hStart with ⟨rfl, rfl⟩
      simp [values, parent]
    · rcases hMore with hMiddle | hEnd
      · rcases hMiddle with ⟨rfl, rfl⟩
        simp_all [values, parent]
      · omega
  case vc4 =>
    simp_all [Variant.evalsTo_ofMeasure, Assertion.NondetFun.evalsTo_pure]
    rename_i current index measure invariant hPositive hNoCompare
    rcases invariant with ⟨rfl, hInvariant⟩
    rcases hInvariant with hStart | hMore
    · rcases hStart with ⟨rfl, rfl⟩
      simp_all [parent]
    · rcases hMore with hMiddle | hEnd
      · rcases hMiddle with ⟨rfl, rfl⟩
        have hShouldContinue :
            prefer (LeanExperiments.RunningMedian.swap heap 3 1)[1]!
              (LeanExperiments.RunningMedian.swap heap 3 1)[0]! = true := by
          change prefer ((heap.set! 3 heap[1]!).set! 1 heap[3]!)[1]!
            ((heap.set! 3 heap[1]!).set! 1 heap[3]!)[0]! = true
          have hOneBound : 1 < (heap.set! 3 heap[1]!).size := by
            simpa using (show 1 < heap.size by omega)
          rw [Array.getElem!_set!_self (heap.set! 3 heap[1]!) 1 _ hOneBound]
          rw [Array.getElem!_set!_ne (heap.set! 3 heap[1]!) 1 0 _ (by omega)]
          rw [Array.getElem!_set!_ne heap 3 0 _ (by omega)]
          simpa only [getElem!_pos heap 3 (by omega : 3 < heap.size)] using hRoot
        rw [hShouldContinue] at hNoCompare
        contradiction
      · simp_all
  case vc5 => simp_all

/-- 添字7の値が親より優先され、祖父母位置よりは優先されない場合、親だけと交換して停止する。 -/

theorem siftUp_leftGreatGrandchild_one_step {prefer : Nat → Nat → Bool} (heap : Array Nat)
    (hSize : 7 < heap.size)
    (hParent : prefer heap[7]! heap[3]! = true)
    (hRoot : prefer heap[7]! heap[1]! = false) :
    LeanExperiments.RunningMedian.siftUp prefer heap 7 =
      LeanExperiments.RunningMedian.swap heap 7 3 := by
  generalize hRun : LeanExperiments.RunningMedian.siftUp prefer heap 7 = result
  apply Id.of_run_eq_wp hRun
  vcgen [LeanExperiments.RunningMedian.siftUp] invariants
  case inv1 => exact fun exit state =>
    if exit then state = (LeanExperiments.RunningMedian.swap heap 7 3, 3)
    else state = (heap, 7) ∨ state = (LeanExperiments.RunningMedian.swap heap 7 3, 3)
  case vc1 => simp
  case vc2 => simp_all <;> omega
  case vc3 =>
    simp_all [Variant.evalsBelow_ofMeasure_nat, Variant.evalsTo_ofMeasure,
      Assertion.NondetFun.evalsTo_pure]
    rename_i current index measure invariant hPositive hCompare
    rcases invariant with ⟨rfl, hInvariant⟩
    rcases hInvariant with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp [values, parent]
    · exfalso
      have hCompareAtRoot : prefer (LeanExperiments.RunningMedian.swap heap 7 3)[3]!
          (LeanExperiments.RunningMedian.swap heap 7 3)[1]! = false := by
        change prefer ((heap.set! 7 heap[3]!).set! 3 heap[7]!)[3]!
          ((heap.set! 7 heap[3]!).set! 3 heap[7]!)[1]! = false
        have hOneBound : 3 < (heap.set! 7 heap[3]!).size := by
          simpa using (show 3 < heap.size by omega)
        rw [Array.getElem!_set!_self (heap.set! 7 heap[3]!) 3 _ hOneBound]
        rw [Array.getElem!_set!_ne (heap.set! 7 heap[3]!) 3 1 _ (by omega)]
        rw [Array.getElem!_set!_ne heap 7 1 _ (by omega)]
        simpa only [getElem!_pos heap 7 (by omega : 7 < heap.size)] using hRoot
      rw [hCompareAtRoot] at hCompare
      contradiction
  case vc4 =>
    simp_all [Variant.evalsTo_ofMeasure, Assertion.NondetFun.evalsTo_pure]
    rename_i current index measure invariant hPositive hNoCompare
    rcases invariant with ⟨rfl, hInvariant⟩
    rcases hInvariant with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp_all [parent]
    · simp_all
  case vc5 => simp_all


/-- 添字7の値が親と祖父母位置の両方より優先されると、2回交換して停止する。 -/

theorem siftUp_leftGreatGrandchild_two_steps {prefer : Nat → Nat → Bool} (heap : Array Nat)
    (hSize : 7 < heap.size)
    (hParent : prefer heap[7]! heap[3]! = true)
    (hAncestor : prefer heap[7]! heap[1]! = true)
    (hRootStop : prefer heap[7]! heap[0]! = false) :
    LeanExperiments.RunningMedian.siftUp prefer heap 7 =
      LeanExperiments.RunningMedian.swap
        (LeanExperiments.RunningMedian.swap heap 7 3) 3 1 := by
  generalize hRun : LeanExperiments.RunningMedian.siftUp prefer heap 7 = result
  apply Id.of_run_eq_wp hRun
  vcgen [LeanExperiments.RunningMedian.siftUp] invariants
  case inv1 => exact fun exit state =>
    if exit then
      state = (LeanExperiments.RunningMedian.swap
        (LeanExperiments.RunningMedian.swap heap 7 3) 3 1, 1)
    else
      state = (heap, 7) ∨
        state = (LeanExperiments.RunningMedian.swap heap 7 3, 3) ∨
        state = (LeanExperiments.RunningMedian.swap
          (LeanExperiments.RunningMedian.swap heap 7 3) 3 1, 1)
  case vc1 => simp
  case vc2 => simp_all <;> omega
  case vc3 =>
    simp_all [Variant.evalsBelow_ofMeasure_nat, Variant.evalsTo_ofMeasure,
      Assertion.NondetFun.evalsTo_pure]
    rename_i current index measure invariant hPositive hCompare
    rcases invariant with ⟨rfl, hInvariant⟩
    rcases hInvariant with hStart | hMore
    · rcases hStart with ⟨rfl, rfl⟩
      simp [values, parent]
    · rcases hMore with hMiddle | hEnd
      · rcases hMiddle with ⟨rfl, rfl⟩
        simp_all [values, parent]
      · have hShouldStop :
            prefer (LeanExperiments.RunningMedian.swap
              (LeanExperiments.RunningMedian.swap heap 7 3) 3 1)[1]!
              (LeanExperiments.RunningMedian.swap
                (LeanExperiments.RunningMedian.swap heap 7 3) 3 1)[0]! = false := by
          have hFirstSize :
              (LeanExperiments.RunningMedian.swap heap 7 3).size = heap.size := by
            exact size_eq_of_perm
              (swap_perm heap 7 3 (by omega) (by omega))
          have hFirst := swap_getElem!_at_positions heap 7 3 (by omega) (by omega)
          have hFinal := swap_getElem!_at_positions
            (LeanExperiments.RunningMedian.swap heap 7 3) 3 1
            (by rw [hFirstSize]; omega) (by rw [hFirstSize]; omega)
          have hRootFirst := swap_getElem!_eq_of_outside
            (LeanExperiments.RunningMedian.swap heap 7 3) 3 1 0
            (by rw [hFirstSize]; omega) (by rw [hFirstSize]; omega)
            (by rw [hFirstSize]; omega) (by omega) (by omega)
          calc
            prefer (LeanExperiments.RunningMedian.swap
                (LeanExperiments.RunningMedian.swap heap 7 3) 3 1)[1]!
                (LeanExperiments.RunningMedian.swap
                  (LeanExperiments.RunningMedian.swap heap 7 3) 3 1)[0]!
                = prefer (LeanExperiments.RunningMedian.swap heap 7 3)[3]!
                    (LeanExperiments.RunningMedian.swap heap 7 3)[0]! := by
                      rw [hFinal.2, hRootFirst]
            _ = prefer heap[7]! heap[0]! := by rw [hFirst.2, swap_getElem!_eq_of_outside
                  heap 7 3 0 (by omega) (by omega) (by omega) (by omega) (by omega)]
            _ = false := by
              simpa only [← getElem!_pos heap 7 (by omega)] using hRootStop
        rcases hEnd with ⟨rfl, rfl⟩
        simp only [parent] at hCompare
        rw [hShouldStop] at hCompare
        contradiction
  case vc4 =>
    simp_all [Variant.evalsTo_ofMeasure, Assertion.NondetFun.evalsTo_pure]
    rename_i current index measure invariant hPositive hNoCompare
    rcases invariant with ⟨rfl, hInvariant⟩
    rcases hInvariant with hStart | hMore
    · rcases hStart with ⟨rfl, rfl⟩
      simp_all [parent]
    · rcases hMore with hMiddle | hEnd
      · rcases hMiddle with ⟨rfl, rfl⟩
        have hShouldContinue :
            prefer (LeanExperiments.RunningMedian.swap heap 7 3)[3]!
              (LeanExperiments.RunningMedian.swap heap 7 3)[1]! = true := by
          change prefer ((heap.set! 7 heap[3]!).set! 3 heap[7]!)[3]!
            ((heap.set! 7 heap[3]!).set! 3 heap[7]!)[1]! = true
          have hOneBound : 3 < (heap.set! 7 heap[3]!).size := by
            simpa using (show 3 < heap.size by omega)
          rw [Array.getElem!_set!_self (heap.set! 7 heap[3]!) 3 _ hOneBound]
          rw [Array.getElem!_set!_ne (heap.set! 7 heap[3]!) 3 1 _ (by omega)]
          rw [Array.getElem!_set!_ne heap 7 1 _ (by omega)]
          simpa only [getElem!_pos heap 7 (by omega : 7 < heap.size)] using hAncestor
        rw [hShouldContinue] at hNoCompare
        contradiction
      · simp_all
  case vc5 => simp_all


/-- 添字7の値が親・祖父母・根の全てより優先されると、3回交換して根へ移る。 -/
theorem siftUp_leftGreatGrandchild_three_steps {prefer : Nat → Nat → Bool} (heap : Array Nat)
    (hSize : 7 < heap.size)
    (hParent : prefer heap[7]! heap[3]! = true)
    (hAncestor : prefer heap[7]! heap[1]! = true)
    (hRoot : prefer heap[7]! heap[0]! = true) :
    LeanExperiments.RunningMedian.siftUp prefer heap 7 =
      LeanExperiments.RunningMedian.swap
        (LeanExperiments.RunningMedian.swap
          (LeanExperiments.RunningMedian.swap heap 7 3) 3 1) 1 0 := by
  generalize hRun : LeanExperiments.RunningMedian.siftUp prefer heap 7 = result
  apply Id.of_run_eq_wp hRun
  vcgen [LeanExperiments.RunningMedian.siftUp] invariants
  case inv1 => exact fun exit state =>
    if exit then
      state = (LeanExperiments.RunningMedian.swap
        (LeanExperiments.RunningMedian.swap
          (LeanExperiments.RunningMedian.swap heap 7 3) 3 1) 1 0, 0)
    else
      state = (heap, 7) ∨
        state = (LeanExperiments.RunningMedian.swap heap 7 3, 3) ∨
        state = (LeanExperiments.RunningMedian.swap
          (LeanExperiments.RunningMedian.swap heap 7 3) 3 1, 1) ∨
        state = (LeanExperiments.RunningMedian.swap
          (LeanExperiments.RunningMedian.swap
            (LeanExperiments.RunningMedian.swap heap 7 3) 3 1) 1 0, 0)
  case vc1 => simp
  case vc2 => simp_all [LeanExperiments.RunningMedian.swap] <;> omega
  case vc3 =>
    simp_all [Variant.evalsBelow_ofMeasure_nat, Variant.evalsTo_ofMeasure,
      Assertion.NondetFun.evalsTo_pure]
    rename_i current index measure invariant hPositive hCompare
    rcases invariant with ⟨rfl, hInvariant⟩
    rcases hInvariant with hStart | hMore
    · rcases hStart with ⟨rfl, rfl⟩
      simp [values, parent]
    · rcases hMore with hMiddle | hMore
      · rcases hMiddle with ⟨rfl, rfl⟩
        simp_all [values, parent]
      · rcases hMore with hEnd | hFinal
        · rcases hEnd with ⟨rfl, rfl⟩
          simp_all [values, parent, LeanExperiments.RunningMedian.swap]
        · rcases hFinal with ⟨rfl, rfl⟩
          omega
  case vc4 =>
    simp_all [Variant.evalsTo_ofMeasure, Assertion.NondetFun.evalsTo_pure]
    rename_i current index measure invariant hPositive hNoCompare
    rcases invariant with ⟨rfl, hInvariant⟩
    rcases hInvariant with hStart | hMore
    · rcases hStart with ⟨rfl, rfl⟩
      simp_all [parent]
    · rcases hMore with hMiddle | hMore
      · rcases hMiddle with ⟨rfl, rfl⟩
        have hShouldContinue :
            prefer (LeanExperiments.RunningMedian.swap heap 7 3)[3]!
              (LeanExperiments.RunningMedian.swap heap 7 3)[1]! = true := by
          change prefer ((heap.set! 7 heap[3]!).set! 3 heap[7]!)[3]!
            ((heap.set! 7 heap[3]!).set! 3 heap[7]!)[1]! = true
          have hOneBound : 3 < (heap.set! 7 heap[3]!).size := by
            simpa using (show 3 < heap.size by omega)
          rw [Array.getElem!_set!_self (heap.set! 7 heap[3]!) 3 _ hOneBound]
          rw [Array.getElem!_set!_ne (heap.set! 7 heap[3]!) 3 1 _ (by omega)]
          rw [Array.getElem!_set!_ne heap 7 1 _ (by omega)]
          simpa only [getElem!_pos heap 7 (by omega : 7 < heap.size)] using hAncestor
        rw [hShouldContinue] at hNoCompare
        contradiction
      · rcases hMore with hEnd | hFinal
        · rcases hEnd with ⟨rfl, rfl⟩
          have hShouldContinue :
              prefer (LeanExperiments.RunningMedian.swap
                (LeanExperiments.RunningMedian.swap heap 7 3) 3 1)[1]!
                (LeanExperiments.RunningMedian.swap
                  (LeanExperiments.RunningMedian.swap heap 7 3) 3 1)[0]! = true := by
            have hFirstSize :
                (LeanExperiments.RunningMedian.swap heap 7 3).size = heap.size := by
              exact size_eq_of_perm
                (swap_perm heap 7 3 (by omega) (by omega))
            have hFirst := swap_getElem!_at_positions heap 7 3 (by omega) (by omega)
            have hFinal := swap_getElem!_at_positions
              (LeanExperiments.RunningMedian.swap heap 7 3) 3 1
              (by rw [hFirstSize]; omega) (by rw [hFirstSize]; omega)
            have hRootFirst := swap_getElem!_eq_of_outside
              (LeanExperiments.RunningMedian.swap heap 7 3) 3 1 0
              (by rw [hFirstSize]; omega) (by rw [hFirstSize]; omega)
              (by rw [hFirstSize]; omega) (by omega) (by omega)
            calc
              prefer (LeanExperiments.RunningMedian.swap
                  (LeanExperiments.RunningMedian.swap heap 7 3) 3 1)[1]!
                  (LeanExperiments.RunningMedian.swap
                    (LeanExperiments.RunningMedian.swap heap 7 3) 3 1)[0]!
                  = prefer (LeanExperiments.RunningMedian.swap heap 7 3)[3]!
                      (LeanExperiments.RunningMedian.swap heap 7 3)[0]! := by
                        rw [hFinal.2, hRootFirst]
              _ = prefer heap[7]! heap[0]! := by rw [hFirst.2,
                    swap_getElem!_eq_of_outside heap 7 3 0 (by omega) (by omega)
                      (by omega) (by omega) (by omega)]
              _ = true := by
                simpa only [← getElem!_pos heap 7 (by omega)] using hRoot
          simp only [parent] at hNoCompare
          rw [hShouldContinue] at hNoCompare
          contradiction
        · rcases hFinal with ⟨rfl, rfl⟩
          omega
  case vc5 => simp_all


/-- 添字8の値が親より優先され、祖父母位置よりは優先されない場合、親だけと交換して停止する。 -/
theorem siftUp_rightGreatGrandchild_one_step {prefer : Nat → Nat → Bool} (heap : Array Nat)
    (hSize : 8 < heap.size)
    (hParent : prefer heap[8]! heap[3]! = true)
    (hRoot : prefer heap[8]! heap[1]! = false) :
    LeanExperiments.RunningMedian.siftUp prefer heap 8 =
      LeanExperiments.RunningMedian.swap heap 8 3 := by
  generalize hRun : LeanExperiments.RunningMedian.siftUp prefer heap 8 = result
  apply Id.of_run_eq_wp hRun
  vcgen [LeanExperiments.RunningMedian.siftUp] invariants
  case inv1 => exact fun exit state =>
    if exit then state = (LeanExperiments.RunningMedian.swap heap 8 3, 3)
    else state = (heap, 8) ∨ state = (LeanExperiments.RunningMedian.swap heap 8 3, 3)
  case vc1 => simp
  case vc2 => simp_all <;> omega
  case vc3 =>
    simp_all [Variant.evalsBelow_ofMeasure_nat, Variant.evalsTo_ofMeasure,
      Assertion.NondetFun.evalsTo_pure]
    rename_i current index measure invariant hPositive hCompare
    rcases invariant with ⟨rfl, hInvariant⟩
    rcases hInvariant with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp [values, parent]
    · exfalso
      have hCompareAtRoot : prefer (LeanExperiments.RunningMedian.swap heap 8 3)[3]!
          (LeanExperiments.RunningMedian.swap heap 8 3)[1]! = false := by
        change prefer ((heap.set! 8 heap[3]!).set! 3 heap[8]!)[3]!
          ((heap.set! 8 heap[3]!).set! 3 heap[8]!)[1]! = false
        have hOneBound : 3 < (heap.set! 8 heap[3]!).size := by
          simpa using (show 3 < heap.size by omega)
        rw [Array.getElem!_set!_self (heap.set! 8 heap[3]!) 3 _ hOneBound]
        rw [Array.getElem!_set!_ne (heap.set! 8 heap[3]!) 3 1 _ (by omega)]
        rw [Array.getElem!_set!_ne heap 8 1 _ (by omega)]
        simpa only [getElem!_pos heap 8 (by omega : 8 < heap.size)] using hRoot
      rw [hCompareAtRoot] at hCompare
      contradiction
  case vc4 =>
    simp_all [Variant.evalsTo_ofMeasure, Assertion.NondetFun.evalsTo_pure]
    rename_i current index measure invariant hPositive hNoCompare
    rcases invariant with ⟨rfl, hInvariant⟩
    rcases hInvariant with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp_all [parent]
    · simp_all
  case vc5 => simp_all


/-- 添字8の値が親と祖父母位置より優先され、根よりは優先されない場合、2回交換して停止する。 -/
theorem siftUp_rightGreatGrandchild_two_steps {prefer : Nat → Nat → Bool} (heap : Array Nat)
    (hSize : 8 < heap.size)
    (hParent : prefer heap[8]! heap[3]! = true)
    (hAncestor : prefer heap[8]! heap[1]! = true)
    (hRootStop : prefer heap[8]! heap[0]! = false) :
    LeanExperiments.RunningMedian.siftUp prefer heap 8 =
      LeanExperiments.RunningMedian.swap
        (LeanExperiments.RunningMedian.swap heap 8 3) 3 1 := by
  generalize hRun : LeanExperiments.RunningMedian.siftUp prefer heap 8 = result
  apply Id.of_run_eq_wp hRun
  vcgen [LeanExperiments.RunningMedian.siftUp] invariants
  case inv1 => exact fun exit state =>
    if exit then
      state = (LeanExperiments.RunningMedian.swap
        (LeanExperiments.RunningMedian.swap heap 8 3) 3 1, 1)
    else
      state = (heap, 8) ∨
        state = (LeanExperiments.RunningMedian.swap heap 8 3, 3) ∨
        state = (LeanExperiments.RunningMedian.swap
          (LeanExperiments.RunningMedian.swap heap 8 3) 3 1, 1)
  case vc1 => simp
  case vc2 => simp_all <;> omega
  case vc3 =>
    simp_all [Variant.evalsBelow_ofMeasure_nat, Variant.evalsTo_ofMeasure,
      Assertion.NondetFun.evalsTo_pure]
    rename_i current index measure invariant hPositive hCompare
    rcases invariant with ⟨rfl, hInvariant⟩
    rcases hInvariant with hStart | hMore
    · rcases hStart with ⟨rfl, rfl⟩
      simp [values, parent]
    · rcases hMore with hMiddle | hEnd
      · rcases hMiddle with ⟨rfl, rfl⟩
        simp_all [values, parent]
      · have hShouldStop :
            prefer (LeanExperiments.RunningMedian.swap
              (LeanExperiments.RunningMedian.swap heap 8 3) 3 1)[1]!
              (LeanExperiments.RunningMedian.swap
                (LeanExperiments.RunningMedian.swap heap 8 3) 3 1)[0]! = false := by
          have hFirstSize :
              (LeanExperiments.RunningMedian.swap heap 8 3).size = heap.size := by
            exact size_eq_of_perm
              (swap_perm heap 8 3 (by omega) (by omega))
          have hFirst := swap_getElem!_at_positions heap 8 3 (by omega) (by omega)
          have hFinal := swap_getElem!_at_positions
            (LeanExperiments.RunningMedian.swap heap 8 3) 3 1
            (by rw [hFirstSize]; omega) (by rw [hFirstSize]; omega)
          have hRootFirst := swap_getElem!_eq_of_outside
            (LeanExperiments.RunningMedian.swap heap 8 3) 3 1 0
            (by rw [hFirstSize]; omega) (by rw [hFirstSize]; omega)
            (by rw [hFirstSize]; omega) (by omega) (by omega)
          calc
            prefer (LeanExperiments.RunningMedian.swap
                (LeanExperiments.RunningMedian.swap heap 8 3) 3 1)[1]!
                (LeanExperiments.RunningMedian.swap
                  (LeanExperiments.RunningMedian.swap heap 8 3) 3 1)[0]!
                = prefer (LeanExperiments.RunningMedian.swap heap 8 3)[3]!
                    (LeanExperiments.RunningMedian.swap heap 8 3)[0]! := by
                      rw [hFinal.2, hRootFirst]
            _ = prefer heap[8]! heap[0]! := by rw [hFirst.2, swap_getElem!_eq_of_outside
                  heap 8 3 0 (by omega) (by omega) (by omega) (by omega) (by omega)]
            _ = false := by
              simpa only [← getElem!_pos heap 8 (by omega)] using hRootStop
        rcases hEnd with ⟨rfl, rfl⟩
        simp only [parent] at hCompare
        rw [hShouldStop] at hCompare
        contradiction
  case vc4 =>
    simp_all [Variant.evalsTo_ofMeasure, Assertion.NondetFun.evalsTo_pure]
    rename_i current index measure invariant hPositive hNoCompare
    rcases invariant with ⟨rfl, hInvariant⟩
    rcases hInvariant with hStart | hMore
    · rcases hStart with ⟨rfl, rfl⟩
      simp_all [parent]
    · rcases hMore with hMiddle | hEnd
      · rcases hMiddle with ⟨rfl, rfl⟩
        have hShouldContinue :
            prefer (LeanExperiments.RunningMedian.swap heap 8 3)[3]!
              (LeanExperiments.RunningMedian.swap heap 8 3)[1]! = true := by
          change prefer ((heap.set! 8 heap[3]!).set! 3 heap[8]!)[3]!
            ((heap.set! 8 heap[3]!).set! 3 heap[8]!)[1]! = true
          have hOneBound : 3 < (heap.set! 8 heap[3]!).size := by
            simpa using (show 3 < heap.size by omega)
          rw [Array.getElem!_set!_self (heap.set! 8 heap[3]!) 3 _ hOneBound]
          rw [Array.getElem!_set!_ne (heap.set! 8 heap[3]!) 3 1 _ (by omega)]
          rw [Array.getElem!_set!_ne heap 8 1 _ (by omega)]
          simpa only [getElem!_pos heap 8 (by omega : 8 < heap.size)] using hAncestor
        rw [hShouldContinue] at hNoCompare
        contradiction
      · simp_all
  case vc5 => simp_all


/-- 添字9の値が親と祖父母位置の両方より優先されると、2回交換して停止する。 -/

theorem siftUp_index_nine_two_steps {prefer : Nat → Nat → Bool} (heap : Array Nat)
    (hSize : 9 < heap.size)
    (hParent : prefer heap[9]! heap[4]! = true)
    (hAncestor : prefer heap[9]! heap[1]! = true)
    (hRootStop : prefer heap[9]! heap[0]! = false) :
    LeanExperiments.RunningMedian.siftUp prefer heap 9 =
      LeanExperiments.RunningMedian.swap
        (LeanExperiments.RunningMedian.swap heap 9 4) 4 1 := by
  generalize hRun : LeanExperiments.RunningMedian.siftUp prefer heap 9 = result
  apply Id.of_run_eq_wp hRun
  vcgen [LeanExperiments.RunningMedian.siftUp] invariants
  case inv1 => exact fun exit state =>
    if exit then
      state = (LeanExperiments.RunningMedian.swap
        (LeanExperiments.RunningMedian.swap heap 9 4) 4 1, 1)
    else
      state = (heap, 9) ∨
        state = (LeanExperiments.RunningMedian.swap heap 9 4, 4) ∨
        state = (LeanExperiments.RunningMedian.swap
          (LeanExperiments.RunningMedian.swap heap 9 4) 4 1, 1)
  case vc1 => simp
  case vc2 => simp_all <;> omega
  case vc3 =>
    simp_all [Variant.evalsBelow_ofMeasure_nat, Variant.evalsTo_ofMeasure,
      Assertion.NondetFun.evalsTo_pure]
    rename_i current index measure invariant hPositive hCompare
    rcases invariant with ⟨rfl, hInvariant⟩
    rcases hInvariant with hStart | hMore
    · rcases hStart with ⟨rfl, rfl⟩
      simp [values, parent]
    · rcases hMore with hMiddle | hEnd
      · rcases hMiddle with ⟨rfl, rfl⟩
        simp_all [values, parent]
      · have hShouldStop :
            prefer (LeanExperiments.RunningMedian.swap
              (LeanExperiments.RunningMedian.swap heap 9 4) 4 1)[1]!
              (LeanExperiments.RunningMedian.swap
                (LeanExperiments.RunningMedian.swap heap 9 4) 4 1)[0]! = false := by
          have hFirstSize :
              (LeanExperiments.RunningMedian.swap heap 9 4).size = heap.size := by
            exact size_eq_of_perm
              (swap_perm heap 9 4 (by omega) (by omega))
          have hFirst := swap_getElem!_at_positions heap 9 4 (by omega) (by omega)
          have hFinal := swap_getElem!_at_positions
            (LeanExperiments.RunningMedian.swap heap 9 4) 4 1
            (by rw [hFirstSize]; omega) (by rw [hFirstSize]; omega)
          have hRootFirst := swap_getElem!_eq_of_outside
            (LeanExperiments.RunningMedian.swap heap 9 4) 4 1 0
            (by rw [hFirstSize]; omega) (by rw [hFirstSize]; omega)
            (by rw [hFirstSize]; omega) (by omega) (by omega)
          calc
            prefer (LeanExperiments.RunningMedian.swap
                (LeanExperiments.RunningMedian.swap heap 9 4) 4 1)[1]!
                (LeanExperiments.RunningMedian.swap
                  (LeanExperiments.RunningMedian.swap heap 9 4) 4 1)[0]!
                = prefer (LeanExperiments.RunningMedian.swap heap 9 4)[4]!
                    (LeanExperiments.RunningMedian.swap heap 9 4)[0]! := by
                      rw [hFinal.2, hRootFirst]
            _ = prefer heap[9]! heap[0]! := by rw [hFirst.2, swap_getElem!_eq_of_outside
                  heap 9 4 0 (by omega) (by omega) (by omega) (by omega) (by omega)]
            _ = false := by
              simpa only [← getElem!_pos heap 9 (by omega)] using hRootStop
        rcases hEnd with ⟨rfl, rfl⟩
        simp only [parent] at hCompare
        rw [hShouldStop] at hCompare
        contradiction
  case vc4 =>
    simp_all [Variant.evalsTo_ofMeasure, Assertion.NondetFun.evalsTo_pure]
    rename_i current index measure invariant hPositive hNoCompare
    rcases invariant with ⟨rfl, hInvariant⟩
    rcases hInvariant with hStart | hMore
    · rcases hStart with ⟨rfl, rfl⟩
      simp_all [parent]
    · rcases hMore with hMiddle | hEnd
      · rcases hMiddle with ⟨rfl, rfl⟩
        have hShouldContinue :
            prefer (LeanExperiments.RunningMedian.swap heap 9 4)[4]!
              (LeanExperiments.RunningMedian.swap heap 9 4)[1]! = true := by
          change prefer ((heap.set! 9 heap[4]!).set! 4 heap[9]!)[4]!
            ((heap.set! 9 heap[4]!).set! 4 heap[9]!)[1]! = true
          have hOneBound : 4 < (heap.set! 9 heap[4]!).size := by
            simpa using (show 4 < heap.size by omega)
          rw [Array.getElem!_set!_self (heap.set! 9 heap[4]!) 4 _ hOneBound]
          rw [Array.getElem!_set!_ne (heap.set! 9 heap[4]!) 4 1 _ (by omega)]
          rw [Array.getElem!_set!_ne heap 9 1 _ (by omega)]
          simpa only [getElem!_pos heap 9 (by omega : 9 < heap.size)] using hAncestor
        rw [hShouldContinue] at hNoCompare
        contradiction
      · simp_all
  case vc5 => simp_all


/-- 添字8の値が親・祖父母・根の全てより優先されると、3回交換して根へ移る。 -/
theorem siftUp_rightGreatGrandchild_three_steps {prefer : Nat → Nat → Bool} (heap : Array Nat)
    (hSize : 8 < heap.size)
    (hParent : prefer heap[8]! heap[3]! = true)
    (hAncestor : prefer heap[8]! heap[1]! = true)
    (hRoot : prefer heap[8]! heap[0]! = true) :
    LeanExperiments.RunningMedian.siftUp prefer heap 8 =
      LeanExperiments.RunningMedian.swap
        (LeanExperiments.RunningMedian.swap
          (LeanExperiments.RunningMedian.swap heap 8 3) 3 1) 1 0 := by
  generalize hRun : LeanExperiments.RunningMedian.siftUp prefer heap 8 = result
  apply Id.of_run_eq_wp hRun
  vcgen [LeanExperiments.RunningMedian.siftUp] invariants
  case inv1 => exact fun exit state =>
    if exit then
      state = (LeanExperiments.RunningMedian.swap
        (LeanExperiments.RunningMedian.swap
          (LeanExperiments.RunningMedian.swap heap 8 3) 3 1) 1 0, 0)
    else
      state = (heap, 8) ∨
        state = (LeanExperiments.RunningMedian.swap heap 8 3, 3) ∨
        state = (LeanExperiments.RunningMedian.swap
          (LeanExperiments.RunningMedian.swap heap 8 3) 3 1, 1) ∨
        state = (LeanExperiments.RunningMedian.swap
          (LeanExperiments.RunningMedian.swap
            (LeanExperiments.RunningMedian.swap heap 8 3) 3 1) 1 0, 0)
  case vc1 => simp
  case vc2 => simp_all [LeanExperiments.RunningMedian.swap] <;> omega
  case vc3 =>
    simp_all [Variant.evalsBelow_ofMeasure_nat, Variant.evalsTo_ofMeasure,
      Assertion.NondetFun.evalsTo_pure]
    rename_i current index measure invariant hPositive hCompare
    rcases invariant with ⟨rfl, hInvariant⟩
    rcases hInvariant with hStart | hMore
    · rcases hStart with ⟨rfl, rfl⟩
      simp [values, parent]
    · rcases hMore with hMiddle | hMore
      · rcases hMiddle with ⟨rfl, rfl⟩
        simp_all [values, parent]
      · rcases hMore with hEnd | hFinal
        · rcases hEnd with ⟨rfl, rfl⟩
          simp_all [values, parent, LeanExperiments.RunningMedian.swap]
        · rcases hFinal with ⟨rfl, rfl⟩
          omega
  case vc4 =>
    simp_all [Variant.evalsTo_ofMeasure, Assertion.NondetFun.evalsTo_pure]
    rename_i current index measure invariant hPositive hNoCompare
    rcases invariant with ⟨rfl, hInvariant⟩
    rcases hInvariant with hStart | hMore
    · rcases hStart with ⟨rfl, rfl⟩
      simp_all [parent]
    · rcases hMore with hMiddle | hMore
      · rcases hMiddle with ⟨rfl, rfl⟩
        have hShouldContinue :
            prefer (LeanExperiments.RunningMedian.swap heap 8 3)[3]!
              (LeanExperiments.RunningMedian.swap heap 8 3)[1]! = true := by
          change prefer ((heap.set! 8 heap[3]!).set! 3 heap[8]!)[3]!
            ((heap.set! 8 heap[3]!).set! 3 heap[8]!)[1]! = true
          have hOneBound : 3 < (heap.set! 8 heap[3]!).size := by
            simpa using (show 3 < heap.size by omega)
          rw [Array.getElem!_set!_self (heap.set! 8 heap[3]!) 3 _ hOneBound]
          rw [Array.getElem!_set!_ne (heap.set! 8 heap[3]!) 3 1 _ (by omega)]
          rw [Array.getElem!_set!_ne heap 8 1 _ (by omega)]
          simpa only [getElem!_pos heap 8 (by omega : 8 < heap.size)] using hAncestor
        rw [hShouldContinue] at hNoCompare
        contradiction
      · rcases hMore with hEnd | hFinal
        · rcases hEnd with ⟨rfl, rfl⟩
          have hShouldContinue :
              prefer (LeanExperiments.RunningMedian.swap
                (LeanExperiments.RunningMedian.swap heap 8 3) 3 1)[1]!
                (LeanExperiments.RunningMedian.swap
                  (LeanExperiments.RunningMedian.swap heap 8 3) 3 1)[0]! = true := by
            have hFirstSize :
                (LeanExperiments.RunningMedian.swap heap 8 3).size = heap.size := by
              exact size_eq_of_perm
                (swap_perm heap 8 3 (by omega) (by omega))
            have hFirst := swap_getElem!_at_positions heap 8 3 (by omega) (by omega)
            have hFinal := swap_getElem!_at_positions
              (LeanExperiments.RunningMedian.swap heap 8 3) 3 1
              (by rw [hFirstSize]; omega) (by rw [hFirstSize]; omega)
            have hRootFirst := swap_getElem!_eq_of_outside
              (LeanExperiments.RunningMedian.swap heap 8 3) 3 1 0
              (by rw [hFirstSize]; omega) (by rw [hFirstSize]; omega)
              (by rw [hFirstSize]; omega) (by omega) (by omega)
            calc
              prefer (LeanExperiments.RunningMedian.swap
                  (LeanExperiments.RunningMedian.swap heap 8 3) 3 1)[1]!
                  (LeanExperiments.RunningMedian.swap
                    (LeanExperiments.RunningMedian.swap heap 8 3) 3 1)[0]!
                  = prefer (LeanExperiments.RunningMedian.swap heap 8 3)[3]!
                      (LeanExperiments.RunningMedian.swap heap 8 3)[0]! := by
                        rw [hFinal.2, hRootFirst]
              _ = prefer heap[8]! heap[0]! := by rw [hFirst.2,
                    swap_getElem!_eq_of_outside heap 8 3 0 (by omega) (by omega)
                      (by omega) (by omega) (by omega)]
              _ = true := by
                simpa only [← getElem!_pos heap 8 (by omega)] using hRoot
          simp only [parent] at hNoCompare
          rw [hShouldContinue] at hNoCompare
          contradiction
        · rcases hFinal with ⟨rfl, rfl⟩
          omega
  case vc5 => simp_all


/-- 添字4の値が親と根の両方より優先されると、`siftUp` は2回交換して根で止まる。 -/
theorem siftUp_rightGrandchild_two_steps {prefer : Nat → Nat → Bool} (heap : Array Nat)
    (hSize : 4 < heap.size)
    (hParent : prefer heap[4]! heap[1]! = true)
    (hRoot : prefer heap[4]! heap[0]! = true) :
    LeanExperiments.RunningMedian.siftUp prefer heap 4 =
      LeanExperiments.RunningMedian.swap
        (LeanExperiments.RunningMedian.swap heap 4 1) 1 0 := by
  generalize hRun : LeanExperiments.RunningMedian.siftUp prefer heap 4 = result
  apply Id.of_run_eq_wp hRun
  vcgen [LeanExperiments.RunningMedian.siftUp] invariants
  case inv1 => exact fun exit state =>
    if exit then
      state = (LeanExperiments.RunningMedian.swap
        (LeanExperiments.RunningMedian.swap heap 4 1) 1 0, 0)
    else
      state = (heap, 4) ∨
        state = (LeanExperiments.RunningMedian.swap heap 4 1, 1) ∨
        state = (LeanExperiments.RunningMedian.swap
          (LeanExperiments.RunningMedian.swap heap 4 1) 1 0, 0)
  case vc1 => simp
  case vc2 => simp_all <;> omega
  case vc3 =>
    simp_all [Variant.evalsBelow_ofMeasure_nat, Variant.evalsTo_ofMeasure,
      Assertion.NondetFun.evalsTo_pure]
    rename_i current index measure invariant hPositive hCompare
    rcases invariant with ⟨rfl, hInvariant⟩
    rcases hInvariant with hStart | hMore
    · rcases hStart with ⟨rfl, rfl⟩
      simp [values, parent]
    · rcases hMore with hMiddle | hEnd
      · rcases hMiddle with ⟨rfl, rfl⟩
        simp_all [values, parent]
      · omega
  case vc4 =>
    simp_all [Variant.evalsTo_ofMeasure, Assertion.NondetFun.evalsTo_pure]
    rename_i current index measure invariant hPositive hNoCompare
    rcases invariant with ⟨rfl, hInvariant⟩
    rcases hInvariant with hStart | hMore
    · rcases hStart with ⟨rfl, rfl⟩
      simp_all [parent]
    · rcases hMore with hMiddle | hEnd
      · rcases hMiddle with ⟨rfl, rfl⟩
        have hShouldContinue :
            prefer (LeanExperiments.RunningMedian.swap heap 4 1)[1]!
              (LeanExperiments.RunningMedian.swap heap 4 1)[0]! = true := by
          change prefer ((heap.set! 4 heap[1]!).set! 1 heap[4]!)[1]!
            ((heap.set! 4 heap[1]!).set! 1 heap[4]!)[0]! = true
          have hOneBound : 1 < (heap.set! 4 heap[1]!).size := by
            simpa using (show 1 < heap.size by omega)
          rw [Array.getElem!_set!_self (heap.set! 4 heap[1]!) 1 _ hOneBound]
          rw [Array.getElem!_set!_ne (heap.set! 4 heap[1]!) 1 0 _ (by omega)]
          rw [Array.getElem!_set!_ne heap 4 0 _ (by omega)]
          simpa only [getElem!_pos heap 4 (by omega : 4 < heap.size)] using hRoot
        rw [hShouldContinue] at hNoCompare
        contradiction
      · simp_all
  case vc5 => simp_all

/-- 添字5の値が親と根の両方より優先されると、`siftUp` は2回交換して根で止まる。 -/
theorem siftUp_leftGrandchildOfRight_two_steps {prefer : Nat → Nat → Bool} (heap : Array Nat)
    (hSize : 5 < heap.size)
    (hParent : prefer heap[5]! heap[2]! = true)
    (hRoot : prefer heap[5]! heap[0]! = true) :
    LeanExperiments.RunningMedian.siftUp prefer heap 5 =
      LeanExperiments.RunningMedian.swap
        (LeanExperiments.RunningMedian.swap heap 5 2) 2 0 := by
  generalize hRun : LeanExperiments.RunningMedian.siftUp prefer heap 5 = result
  apply Id.of_run_eq_wp hRun
  vcgen [LeanExperiments.RunningMedian.siftUp] invariants
  case inv1 => exact fun exit state =>
    if exit then
      state = (LeanExperiments.RunningMedian.swap
        (LeanExperiments.RunningMedian.swap heap 5 2) 2 0, 0)
    else
      state = (heap, 5) ∨
        state = (LeanExperiments.RunningMedian.swap heap 5 2, 2) ∨
        state = (LeanExperiments.RunningMedian.swap
          (LeanExperiments.RunningMedian.swap heap 5 2) 2 0, 0)
  case vc1 => simp
  case vc2 => simp_all <;> omega
  case vc3 =>
    simp_all [Variant.evalsBelow_ofMeasure_nat, Variant.evalsTo_ofMeasure,
      Assertion.NondetFun.evalsTo_pure]
    rename_i current index measure invariant hPositive hCompare
    rcases invariant with ⟨rfl, hInvariant⟩
    rcases hInvariant with hStart | hMore
    · rcases hStart with ⟨rfl, rfl⟩
      simp [values, parent]
    · rcases hMore with hMiddle | hEnd
      · rcases hMiddle with ⟨rfl, rfl⟩
        simp_all [values, parent]
      · omega
  case vc4 =>
    simp_all [Variant.evalsTo_ofMeasure, Assertion.NondetFun.evalsTo_pure]
    rename_i current index measure invariant hPositive hNoCompare
    rcases invariant with ⟨rfl, hInvariant⟩
    rcases hInvariant with hStart | hMore
    · rcases hStart with ⟨rfl, rfl⟩
      simp_all [parent]
    · rcases hMore with hMiddle | hEnd
      · rcases hMiddle with ⟨rfl, rfl⟩
        have hShouldContinue :
            prefer (LeanExperiments.RunningMedian.swap heap 5 2)[2]!
              (LeanExperiments.RunningMedian.swap heap 5 2)[0]! = true := by
          change prefer ((heap.set! 5 heap[2]!).set! 2 heap[5]!)[2]!
            ((heap.set! 5 heap[2]!).set! 2 heap[5]!)[0]! = true
          have hOneBound : 2 < (heap.set! 5 heap[2]!).size := by
            simpa using (show 2 < heap.size by omega)
          rw [Array.getElem!_set!_self (heap.set! 5 heap[2]!) 2 _ hOneBound]
          rw [Array.getElem!_set!_ne (heap.set! 5 heap[2]!) 2 0 _ (by omega)]
          rw [Array.getElem!_set!_ne heap 5 0 _ (by omega)]
          simpa only [getElem!_pos heap 5 (by omega : 5 < heap.size)] using hRoot
        rw [hShouldContinue] at hNoCompare
        contradiction
      · simp_all
  case vc5 => simp_all

/-- 添字6の値が親より優先され根よりは優先されない場合、親とだけ交換して止まる。 -/
theorem siftUp_rightGrandchildOfRight_one_step {prefer : Nat → Nat → Bool}
    (heap : Array Nat) (hSize : 6 < heap.size)
    (hParent : prefer heap[6]! heap[2]! = true)
    (hRoot : prefer heap[6]! heap[0]! = false) :
    LeanExperiments.RunningMedian.siftUp prefer heap 6 =
      LeanExperiments.RunningMedian.swap heap 6 2 := by
  generalize hRun : LeanExperiments.RunningMedian.siftUp prefer heap 6 = result
  apply Id.of_run_eq_wp hRun
  vcgen [LeanExperiments.RunningMedian.siftUp] invariants
  case inv1 => exact fun exit state =>
    if exit then state = (LeanExperiments.RunningMedian.swap heap 6 2, 2)
    else state = (heap, 6) ∨ state = (LeanExperiments.RunningMedian.swap heap 6 2, 2)
  case vc1 => simp
  case vc2 => simp_all <;> omega
  case vc3 =>
    simp_all [Variant.evalsBelow_ofMeasure_nat, Variant.evalsTo_ofMeasure,
      Assertion.NondetFun.evalsTo_pure]
    rename_i current index measure invariant hPositive hCompare
    rcases invariant with ⟨rfl, hInvariant⟩
    rcases hInvariant with hStart | hEnd
    · rcases hStart with ⟨rfl, rfl⟩
      simp [values, parent]
    · rcases hEnd with ⟨rfl, rfl⟩
      have hShouldStop :
          prefer (LeanExperiments.RunningMedian.swap heap 6 2)[2]!
            (LeanExperiments.RunningMedian.swap heap 6 2)[0]! = false := by
        change prefer ((heap.set! 6 heap[2]!).set! 2 heap[6]!)[2]!
          ((heap.set! 6 heap[2]!).set! 2 heap[6]!)[0]! = false
        have hOneBound : 2 < (heap.set! 6 heap[2]!).size := by
          simpa using (show 2 < heap.size by omega)
        rw [Array.getElem!_set!_self (heap.set! 6 heap[2]!) 2 _ hOneBound]
        rw [Array.getElem!_set!_ne (heap.set! 6 heap[2]!) 2 0 _ (by omega)]
        rw [Array.getElem!_set!_ne heap 6 0 _ (by omega)]
        simpa only [getElem!_pos heap 6 (by omega : 6 < heap.size)] using hRoot
      rw [hShouldStop] at hCompare
      simp_all
  case vc4 =>
    simp_all [Variant.evalsTo_ofMeasure, Assertion.NondetFun.evalsTo_pure]
    rename_i current index measure invariant hPositive hNoCompare
    rcases invariant with ⟨rfl, hInvariant⟩
    rcases hInvariant with hStart | hEnd
    · rcases hStart with ⟨rfl, rfl⟩
      simp_all [parent]
    · rcases hEnd with ⟨rfl, rfl⟩
      have hShouldStop :
          prefer (LeanExperiments.RunningMedian.swap heap 6 2)[2]!
            (LeanExperiments.RunningMedian.swap heap 6 2)[0]! = false := by
        change prefer ((heap.set! 6 heap[2]!).set! 2 heap[6]!)[2]!
          ((heap.set! 6 heap[2]!).set! 2 heap[6]!)[0]! = false
        have hOneBound : 2 < (heap.set! 6 heap[2]!).size := by
          simpa using (show 2 < heap.size by omega)
        rw [Array.getElem!_set!_self (heap.set! 6 heap[2]!) 2 _ hOneBound]
        rw [Array.getElem!_set!_ne (heap.set! 6 heap[2]!) 2 0 _ (by omega)]
        rw [Array.getElem!_set!_ne heap 6 0 _ (by omega)]
        simpa only [getElem!_pos heap 6 (by omega : 6 < heap.size)] using hRoot
      rw [hShouldStop] at hNoCompare
      simp_all
  case vc5 => simp_all

/-- 添字6の値が親と根の両方より優先されると、右部分木を2回上昇して根で止まる。
-/
theorem siftUp_rightGrandchildOfRight_two_steps {prefer : Nat → Nat → Bool}
    (heap : Array Nat) (hSize : 6 < heap.size)
    (hParent : prefer heap[6]! heap[2]! = true)
    (hRoot : prefer heap[6]! heap[0]! = true) :
    LeanExperiments.RunningMedian.siftUp prefer heap 6 =
      LeanExperiments.RunningMedian.swap
        (LeanExperiments.RunningMedian.swap heap 6 2) 2 0 := by
  generalize hRun : LeanExperiments.RunningMedian.siftUp prefer heap 6 = result
  apply Id.of_run_eq_wp hRun
  vcgen [LeanExperiments.RunningMedian.siftUp] invariants
  case inv1 => exact fun exit state =>
    if exit then
      state = (LeanExperiments.RunningMedian.swap
        (LeanExperiments.RunningMedian.swap heap 6 2) 2 0, 0)
    else
      state = (heap, 6) ∨
        state = (LeanExperiments.RunningMedian.swap heap 6 2, 2) ∨
        state = (LeanExperiments.RunningMedian.swap
          (LeanExperiments.RunningMedian.swap heap 6 2) 2 0, 0)
  case vc1 => simp
  case vc2 => simp_all <;> omega
  case vc3 =>
    simp_all [Variant.evalsBelow_ofMeasure_nat, Variant.evalsTo_ofMeasure,
      Assertion.NondetFun.evalsTo_pure]
    rename_i current index measure invariant hPositive hCompare
    rcases invariant with ⟨rfl, hInvariant⟩
    rcases hInvariant with hStart | hMore
    · rcases hStart with ⟨rfl, rfl⟩
      simp [values, parent]
    · rcases hMore with hMiddle | hEnd
      · rcases hMiddle with ⟨rfl, rfl⟩
        simp_all [values, parent]
      · omega
  case vc4 =>
    simp_all [Variant.evalsTo_ofMeasure, Assertion.NondetFun.evalsTo_pure]
    rename_i current index measure invariant hPositive hNoCompare
    rcases invariant with ⟨rfl, hInvariant⟩
    rcases hInvariant with hStart | hMore
    · rcases hStart with ⟨rfl, rfl⟩
      simp_all [parent]
    · rcases hMore with hMiddle | hEnd
      · rcases hMiddle with ⟨rfl, rfl⟩
        have hShouldContinue :
            prefer (LeanExperiments.RunningMedian.swap heap 6 2)[2]!
              (LeanExperiments.RunningMedian.swap heap 6 2)[0]! = true := by
          change prefer ((heap.set! 6 heap[2]!).set! 2 heap[6]!)[2]!
            ((heap.set! 6 heap[2]!).set! 2 heap[6]!)[0]! = true
          have hOneBound : 2 < (heap.set! 6 heap[2]!).size := by
            simpa using (show 2 < heap.size by omega)
          rw [Array.getElem!_set!_self (heap.set! 6 heap[2]!) 2 _ hOneBound]
          rw [Array.getElem!_set!_ne (heap.set! 6 heap[2]!) 2 0 _ (by omega)]
          rw [Array.getElem!_set!_ne heap 6 0 _ (by omega)]
          simpa only [getElem!_pos heap 6 (by omega : 6 < heap.size)] using hRoot
        rw [hShouldContinue] at hNoCompare
        contradiction
      · simp_all
  case vc5 => simp_all

/-- 添字4の値が親より優先され、根よりは優先されない場合、親だけと交換して停止する。 -/
theorem siftUp_rightGrandchild_one_step {prefer : Nat → Nat → Bool} (heap : Array Nat)
    (hSize : 4 < heap.size)
    (hParent : prefer heap[4]! heap[1]! = true)
    (hRoot : prefer heap[4]! heap[0]! = false) :
    LeanExperiments.RunningMedian.siftUp prefer heap 4 =
      LeanExperiments.RunningMedian.swap heap 4 1 := by
  generalize hRun : LeanExperiments.RunningMedian.siftUp prefer heap 4 = result
  apply Id.of_run_eq_wp hRun
  vcgen [LeanExperiments.RunningMedian.siftUp] invariants
  case inv1 => exact fun exit state =>
    if exit then state = (LeanExperiments.RunningMedian.swap heap 4 1, 1)
    else state = (heap, 4) ∨ state = (LeanExperiments.RunningMedian.swap heap 4 1, 1)
  case vc1 => simp
  case vc2 => simp_all <;> omega
  case vc3 =>
    simp_all [Variant.evalsBelow_ofMeasure_nat, Variant.evalsTo_ofMeasure,
      Assertion.NondetFun.evalsTo_pure]
    rename_i current index measure invariant hPositive hCompare
    rcases invariant with ⟨rfl, hInvariant⟩
    rcases hInvariant with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp [values, parent]
    · exfalso
      have hCompareAtRoot : prefer (LeanExperiments.RunningMedian.swap heap 4 1)[1]!
          (LeanExperiments.RunningMedian.swap heap 4 1)[0]! = false := by
        change prefer ((heap.set! 4 heap[1]!).set! 1 heap[4]!)[1]!
          ((heap.set! 4 heap[1]!).set! 1 heap[4]!)[0]! = false
        have hOneBound : 1 < (heap.set! 4 heap[1]!).size := by
          simpa using (show 1 < heap.size by omega)
        rw [Array.getElem!_set!_self (heap.set! 4 heap[1]!) 1 _ hOneBound]
        rw [Array.getElem!_set!_ne (heap.set! 4 heap[1]!) 1 0 _ (by omega)]
        rw [Array.getElem!_set!_ne heap 4 0 _ (by omega)]
        simpa only [getElem!_pos heap 4 (by omega : 4 < heap.size)] using hRoot
      rw [hCompareAtRoot] at hCompare
      contradiction
  case vc4 =>
    simp_all [Variant.evalsTo_ofMeasure, Assertion.NondetFun.evalsTo_pure]
    rename_i current index measure invariant hPositive hNoCompare
    rcases invariant with ⟨rfl, hInvariant⟩
    rcases hInvariant with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp_all [parent]
    · simp_all
  case vc5 => simp_all

/-- 添字3の値が親より優先され、根よりは優先されない場合、親だけと交換して停止する。 -/
theorem siftUp_leftGrandchild_one_step {prefer : Nat → Nat → Bool} (heap : Array Nat)
    (hSize : 3 < heap.size)
    (hParent : prefer heap[3]! heap[1]! = true)
    (hRoot : prefer heap[3]! heap[0]! = false) :
    LeanExperiments.RunningMedian.siftUp prefer heap 3 =
      LeanExperiments.RunningMedian.swap heap 3 1 := by
  generalize hRun : LeanExperiments.RunningMedian.siftUp prefer heap 3 = result
  apply Id.of_run_eq_wp hRun
  vcgen [LeanExperiments.RunningMedian.siftUp] invariants
  case inv1 => exact fun exit state =>
    if exit then state = (LeanExperiments.RunningMedian.swap heap 3 1, 1)
    else state = (heap, 3) ∨ state = (LeanExperiments.RunningMedian.swap heap 3 1, 1)
  case vc1 => simp
  case vc2 => simp_all <;> omega
  case vc3 =>
    simp_all [Variant.evalsBelow_ofMeasure_nat, Variant.evalsTo_ofMeasure,
      Assertion.NondetFun.evalsTo_pure]
    rename_i current index measure invariant hPositive hCompare
    rcases invariant with ⟨rfl, hInvariant⟩
    rcases hInvariant with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp [values, parent]
    · exfalso
      have hCompareAtRoot : prefer (LeanExperiments.RunningMedian.swap heap 3 1)[1]!
          (LeanExperiments.RunningMedian.swap heap 3 1)[0]! = false := by
        change prefer ((heap.set! 3 heap[1]!).set! 1 heap[3]!)[1]!
          ((heap.set! 3 heap[1]!).set! 1 heap[3]!)[0]! = false
        have hOneBound : 1 < (heap.set! 3 heap[1]!).size := by
          simpa using (show 1 < heap.size by omega)
        rw [Array.getElem!_set!_self (heap.set! 3 heap[1]!) 1 _ hOneBound]
        rw [Array.getElem!_set!_ne (heap.set! 3 heap[1]!) 1 0 _ (by omega)]
        rw [Array.getElem!_set!_ne heap 3 0 _ (by omega)]
        simpa only [getElem!_pos heap 3 (by omega : 3 < heap.size)] using hRoot
      rw [hCompareAtRoot] at hCompare
      contradiction
  case vc4 =>
    simp_all [Variant.evalsTo_ofMeasure, Assertion.NondetFun.evalsTo_pure]
    rename_i current index measure invariant hPositive hNoCompare
    rcases invariant with ⟨rfl, hInvariant⟩
    rcases hInvariant with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp_all [parent]
    · simp_all
  case vc5 => simp_all

/-- 添字5の値が親より優先され、根よりは優先されない場合、親だけと交換して停止する。 -/
theorem siftUp_leftGrandchildOfRight_one_step {prefer : Nat → Nat → Bool} (heap : Array Nat)
    (hSize : 5 < heap.size)
    (hParent : prefer heap[5]! heap[2]! = true)
    (hRoot : prefer heap[5]! heap[0]! = false) :
    LeanExperiments.RunningMedian.siftUp prefer heap 5 =
      LeanExperiments.RunningMedian.swap heap 5 2 := by
  generalize hRun : LeanExperiments.RunningMedian.siftUp prefer heap 5 = result
  apply Id.of_run_eq_wp hRun
  vcgen [LeanExperiments.RunningMedian.siftUp] invariants
  case inv1 => exact fun exit state =>
    if exit then state = (LeanExperiments.RunningMedian.swap heap 5 2, 2)
    else state = (heap, 5) ∨ state = (LeanExperiments.RunningMedian.swap heap 5 2, 2)
  case vc1 => simp
  case vc2 => simp_all <;> omega
  case vc3 =>
    simp_all [Variant.evalsBelow_ofMeasure_nat, Variant.evalsTo_ofMeasure,
      Assertion.NondetFun.evalsTo_pure]
    rename_i current index measure invariant hPositive hCompare
    rcases invariant with ⟨rfl, hInvariant⟩
    rcases hInvariant with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp [values, parent]
    · exfalso
      have hCompareAtRoot : prefer (LeanExperiments.RunningMedian.swap heap 5 2)[2]!
          (LeanExperiments.RunningMedian.swap heap 5 2)[0]! = false := by
        change prefer ((heap.set! 5 heap[2]!).set! 2 heap[5]!)[2]!
          ((heap.set! 5 heap[2]!).set! 2 heap[5]!)[0]! = false
        have hOneBound : 2 < (heap.set! 5 heap[2]!).size := by
          simpa using (show 2 < heap.size by omega)
        rw [Array.getElem!_set!_self (heap.set! 5 heap[2]!) 2 _ hOneBound]
        rw [Array.getElem!_set!_ne (heap.set! 5 heap[2]!) 2 0 _ (by omega)]
        rw [Array.getElem!_set!_ne heap 5 0 _ (by omega)]
        simpa only [getElem!_pos heap 5 (by omega : 5 < heap.size)] using hRoot
      rw [hCompareAtRoot] at hCompare
      contradiction
  case vc4 =>
    simp_all [Variant.evalsTo_ofMeasure, Assertion.NondetFun.evalsTo_pure]
    rename_i current index measure invariant hPositive hNoCompare
    rcases invariant with ⟨rfl, hInvariant⟩
    rcases hInvariant with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp_all [parent]
    · simp_all
  case vc5 => simp_all

/-- 2要素の親方向調整では、優先される子が親位置へ移り、旧親が子位置へ移る。 -/
theorem siftUp_pair_of_prefer_true {prefer : Nat → Nat → Bool}
    {left right : Nat} (hPrefer : prefer right left = true) :
    LeanExperiments.RunningMedian.siftUp prefer #[left, right] 1 = #[right, left] := by
  rw [siftUp_one_step #[left, right] (by simp) (by simpa using hPrefer)]
  simp [LeanExperiments.RunningMedian.swap]

/-- 2要素ヒープへの挿入では、新しい値が根より優先されると根と末尾を交換する。 -/
theorem insertHeap_twoElements_of_prefer_true {prefer : Nat → Nat → Bool}
    {root other value : Nat} (hPrefer : prefer value root = true) :
    LeanExperiments.RunningMedian.insertHeap prefer #[root, other] value =
      #[value, other, root] := by
  unfold LeanExperiments.RunningMedian.insertHeap
  change LeanExperiments.RunningMedian.siftUp prefer #[root, other, value] 2 =
    #[value, other, root]
  rw [siftUp_rightChild_one_step #[root, other, value] (by simp) (by simpa using hPrefer)]
  simp [LeanExperiments.RunningMedian.swap]

/-- 2要素の最大ヒープへ根より大きい値を挿入すると、その値が新しい根になる。 -/
theorem insertHeap_maxPrefer_twoElements_of_gt {root other value : Nat}
    (hRoot : root < value) :
    LeanExperiments.RunningMedian.insertHeap LeanExperiments.RunningMedian.maxPrefer
      #[root, other] value = #[value, other, root] := by
  apply insertHeap_twoElements_of_prefer_true
  simp [LeanExperiments.RunningMedian.maxPrefer, hRoot]

/-- 2要素の最小ヒープへ根より小さい値を挿入すると、その値が新しい根になる。 -/
theorem insertHeap_minPrefer_twoElements_of_lt {root other value : Nat}
    (hRoot : value < root) :
    LeanExperiments.RunningMedian.insertHeap LeanExperiments.RunningMedian.minPrefer
      #[root, other] value = #[value, other, root] := by
  apply insertHeap_twoElements_of_prefer_true
  simp [LeanExperiments.RunningMedian.minPrefer, hRoot]

/-- 任意の二要素最大ヒープに任意値を挿入しても、最大ヒープ順序を保つ。 -/
theorem insertHeap_maxPrefer_twoElements_preserves
    {root other value : Nat}
    (hHeap : HeapOrdered LeanExperiments.RunningMedian.maxPrefer #[root, other]) :
    HeapOrdered LeanExperiments.RunningMedian.maxPrefer
      (LeanExperiments.RunningMedian.insertHeap
        LeanExperiments.RunningMedian.maxPrefer #[root, other] value) := by
  have hOther : other ≤ root := by
    have h := (hHeap 0 (by simp)).1 (by simp)
    simpa [LeanExperiments.RunningMedian.maxPrefer] using h
  by_cases hStops : value ≤ root
  · have hPush :
        LeanExperiments.RunningMedian.insertHeap LeanExperiments.RunningMedian.maxPrefer
            #[root, other] value = #[root, other, value] := by
      apply insertHeap_eq_push_of_stops
      right
      simpa [LeanExperiments.RunningMedian.maxPrefer]
    rw [hPush]
    intro index hIndex
    have hCases : index = 0 ∨ index = 1 ∨ index = 2 := by
      have hBound : index < 3 := by simpa using hIndex
      omega
    rcases hCases with h | h | h <;> subst index <;>
      simp_all [HeapOrdered, LeanExperiments.RunningMedian.maxPrefer] <;> omega
  · have hRoot : root < value := by omega
    rw [insertHeap_maxPrefer_twoElements_of_gt hRoot]
    intro index hIndex
    have hCases : index = 0 ∨ index = 1 ∨ index = 2 := by
      have hBound : index < 3 := by simpa using hIndex
      omega
    rcases hCases with h | h | h <;> subst index <;>
      simp_all [HeapOrdered, LeanExperiments.RunningMedian.maxPrefer] <;> omega

/-- 任意の二要素最小ヒープに任意値を挿入しても、最小ヒープ順序を保つ。 -/
theorem insertHeap_minPrefer_twoElements_preserves
    {root other value : Nat} (hHeap : MinHeap #[root, other]) :
    MinHeap (LeanExperiments.RunningMedian.insertHeap
      LeanExperiments.RunningMedian.minPrefer #[root, other] value) := by
  have hRoot : root ≤ other := (hHeap 0 (by simp)).1 (by simp)
  have hOrdered : HeapOrdered LeanExperiments.RunningMedian.minPrefer #[root, other] := by
    intro index hIndex
    have hCases : index = 0 ∨ index = 1 := by
      have hBound : index < 2 := by simpa using hIndex
      omega
    rcases hCases with h | h <;> subst index
    · constructor
      · intro _
        simpa [LeanExperiments.RunningMedian.minPrefer] using hRoot
      · intro hChild
        simp at hChild
    · simp
  by_cases hStops : root ≤ value
  · have hPush :
        LeanExperiments.RunningMedian.insertHeap LeanExperiments.RunningMedian.minPrefer
            #[root, other] value = #[root, other, value] := by
      apply insertHeap_eq_push_of_stops
      right
      simpa [LeanExperiments.RunningMedian.minPrefer]
    rw [hPush]
    intro index hIndex
    have hCases : index = 0 ∨ index = 1 ∨ index = 2 := by
      have hBound : index < 3 := by simpa using hIndex
      omega
    rcases hCases with h | h | h <;> subst index <;>
      simp_all [MinHeap] <;> omega
  · have hValue : value < root := by omega
    rw [insertHeap_minPrefer_twoElements_of_lt hValue]
    intro index hIndex
    have hCases : index = 0 ∨ index = 1 ∨ index = 2 := by
      have hBound : index < 3 := by simpa using hIndex
      omega
    rcases hCases with h | h | h <;> subst index <;>
      simp_all [MinHeap] <;> omega

/-- 3要素の最大ヒープでは、根を超える追加値を挿入した結果も最大ヒープになる。 -/
theorem insertHeap_maxPrefer_threeElements_of_gt_root
    {root left right value : Nat}
    (hHeap : HeapOrdered LeanExperiments.RunningMedian.maxPrefer #[root, left, right])
    (hValue : root < value) :
    HeapOrdered LeanExperiments.RunningMedian.maxPrefer
      (LeanExperiments.RunningMedian.insertHeap
        LeanExperiments.RunningMedian.maxPrefer #[root, left, right] value) := by
  have hLeft : left ≤ root := by
    have hEdge := (hHeap 0 (by simp)).1 (by simp)
    simpa [LeanExperiments.RunningMedian.maxPrefer] using hEdge
  have hRight : right ≤ root := by
    have hEdge := (hHeap 0 (by simp)).2 (by simp)
    simpa [LeanExperiments.RunningMedian.maxPrefer] using hEdge
  have hValueLeft : left < value := by omega
  have hSift :
      LeanExperiments.RunningMedian.insertHeap
          LeanExperiments.RunningMedian.maxPrefer #[root, left, right] value =
        #[value, root, right, left] := by
    unfold LeanExperiments.RunningMedian.insertHeap
    change LeanExperiments.RunningMedian.siftUp
      LeanExperiments.RunningMedian.maxPrefer #[root, left, right, value] 3 =
        #[value, root, right, left]
    rw [siftUp_leftGrandchild_two_steps #[root, left, right, value] (by simp)
      (by simp [LeanExperiments.RunningMedian.maxPrefer, hValueLeft])
      (by simp [LeanExperiments.RunningMedian.maxPrefer, hValue])]
    simp [LeanExperiments.RunningMedian.swap]
  rw [hSift]
  intro index hIndex
  have hIndexBound : index < 4 := by simpa using hIndex
  have hCases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 := by omega
  rcases hCases with h | h | h | h <;> subst index <;>
    simp_all [HeapOrdered, LeanExperiments.RunningMedian.maxPrefer] <;> omega

/-- 3要素の最小ヒープでは、根を下回る追加値を挿入した結果も最小ヒープになる。 -/
theorem insertHeap_minPrefer_threeElements_of_lt_root
    {root left right value : Nat}
    (hHeap : MinHeap #[root, left, right])
    (hValue : value < root) :
    MinHeap
      (LeanExperiments.RunningMedian.insertHeap
        LeanExperiments.RunningMedian.minPrefer #[root, left, right] value) := by
  have hLeft : root ≤ left := by
    have hEdge := (hHeap 0 (by simp)).1 (by simp)
    exact hEdge
  have hRight : root ≤ right := by
    have hEdge := (hHeap 0 (by simp)).2 (by simp)
    exact hEdge
  have hSift :
      LeanExperiments.RunningMedian.insertHeap
          LeanExperiments.RunningMedian.minPrefer #[root, left, right] value =
        #[value, root, right, left] := by
    have hValueLeft : value < left := by omega
    unfold LeanExperiments.RunningMedian.insertHeap
    change LeanExperiments.RunningMedian.siftUp
      LeanExperiments.RunningMedian.minPrefer #[root, left, right, value] 3 =
        #[value, root, right, left]
    rw [siftUp_leftGrandchild_two_steps #[root, left, right, value] (by simp)
      (by simp [LeanExperiments.RunningMedian.minPrefer, hValueLeft])
      (by simp [LeanExperiments.RunningMedian.minPrefer, hValue])]
    simp [LeanExperiments.RunningMedian.swap]
  rw [hSift]
  intro index hIndex
  have hIndexBound : index < 4 := by simpa using hIndex
  have hCases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 := by omega
  rcases hCases with h | h | h | h <;> subst index <;> simp_all [MinHeap] <;> omega

/-- 任意の3要素最大ヒープへの挿入は、停止・1回交換・2回交換の各場合で順序を保つ。 -/
theorem insertHeap_maxPrefer_threeElements_preserves
    {root left right value : Nat}
    (hHeap : HeapOrdered LeanExperiments.RunningMedian.maxPrefer #[root, left, right]) :
    HeapOrdered LeanExperiments.RunningMedian.maxPrefer
      (LeanExperiments.RunningMedian.insertHeap
        LeanExperiments.RunningMedian.maxPrefer #[root, left, right] value) := by
  by_cases hStops : value ≤ left
  · apply insertHeap_HeapOrdered_of_stops LeanExperiments.RunningMedian.maxPrefer
      #[root, left, right] value hHeap
    right
    simpa [LeanExperiments.RunningMedian.maxPrefer] using hStops
  · have hParent : left < value := by omega
    by_cases hStopsAtRoot : value ≤ root
    · have hSift :
        LeanExperiments.RunningMedian.insertHeap
            LeanExperiments.RunningMedian.maxPrefer #[root, left, right] value =
          #[root, value, right, left] := by
        unfold LeanExperiments.RunningMedian.insertHeap
        change LeanExperiments.RunningMedian.siftUp
          LeanExperiments.RunningMedian.maxPrefer #[root, left, right, value] 3 =
            #[root, value, right, left]
        rw [siftUp_leftGrandchild_one_step #[root, left, right, value] (by simp)
          (by simp [LeanExperiments.RunningMedian.maxPrefer, hParent])
          (by simp [LeanExperiments.RunningMedian.maxPrefer, hStopsAtRoot])]
        simp [LeanExperiments.RunningMedian.swap]
      have hRootLeft : left ≤ root := by
        have hEdge := (hHeap 0 (by simp)).1 (by simp)
        simpa [LeanExperiments.RunningMedian.maxPrefer] using hEdge
      have hRootRight : right ≤ root := by
        have hEdge := (hHeap 0 (by simp)).2 (by simp)
        simpa [LeanExperiments.RunningMedian.maxPrefer] using hEdge
      rw [hSift]
      intro index hIndex
      have hIndexBound : index < 4 := by simpa using hIndex
      have hCases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 := by omega
      rcases hCases with h | h | h | h <;> subst index <;>
        simp_all [HeapOrdered, LeanExperiments.RunningMedian.maxPrefer] <;> omega
    · have hRoot : root < value := by omega
      exact insertHeap_maxPrefer_threeElements_of_gt_root hHeap hRoot

/-- 任意の3要素最小ヒープへの挿入は、停止・1回交換・2回交換の各場合で順序を保つ。 -/
theorem insertHeap_minPrefer_threeElements_preserves
    {root left right value : Nat}
    (hHeap : MinHeap #[root, left, right]) :
    MinHeap
      (LeanExperiments.RunningMedian.insertHeap
        LeanExperiments.RunningMedian.minPrefer #[root, left, right] value) := by
  by_cases hStops : left ≤ value
  · have hOrdered : HeapOrdered LeanExperiments.RunningMedian.minPrefer
        #[root, left, right] := by
      intro index hIndex
      have hIndexBound : index < 3 := by simpa using hIndex
      have hCases : index = 0 ∨ index = 1 ∨ index = 2 := by omega
      rcases hCases with h | h | h <;> subst index
      · obtain ⟨hLeft, hRight⟩ := hHeap 0 (by simp)
        constructor
        · intro hChild
          have hEdge := hLeft (by simp)
          simp [LeanExperiments.RunningMedian.minPrefer]
          simp at hEdge
          omega
        · intro hChild
          have hEdge := hRight (by simp)
          simp [LeanExperiments.RunningMedian.minPrefer]
          simp at hEdge
          omega
      · simp
      · simp
    have hStoppedOrdered : HeapOrdered LeanExperiments.RunningMedian.minPrefer
        (LeanExperiments.RunningMedian.insertHeap
          LeanExperiments.RunningMedian.minPrefer #[root, left, right] value) :=
      insertHeap_HeapOrdered_of_stops LeanExperiments.RunningMedian.minPrefer
        #[root, left, right] value hOrdered (by
          right
          simpa [LeanExperiments.RunningMedian.minPrefer] using hStops)
    intro index hIndex
    obtain ⟨hLeft, hRight⟩ := hStoppedOrdered index hIndex
    constructor
    · intro hChild
      have hEdge := hLeft hChild
      simp [LeanExperiments.RunningMedian.minPrefer] at hEdge
      omega
    · intro hChild
      have hEdge := hRight hChild
      simp [LeanExperiments.RunningMedian.minPrefer] at hEdge
      omega
  · have hParent : value < left := by omega
    by_cases hStopsAtRoot : root ≤ value
    · have hSift :
        LeanExperiments.RunningMedian.insertHeap
            LeanExperiments.RunningMedian.minPrefer #[root, left, right] value =
          #[root, value, right, left] := by
        unfold LeanExperiments.RunningMedian.insertHeap
        change LeanExperiments.RunningMedian.siftUp
          LeanExperiments.RunningMedian.minPrefer #[root, left, right, value] 3 =
            #[root, value, right, left]
        rw [siftUp_leftGrandchild_one_step #[root, left, right, value] (by simp)
          (by simp [LeanExperiments.RunningMedian.minPrefer, hParent])
          (by simp [LeanExperiments.RunningMedian.minPrefer, hStopsAtRoot])]
        simp [LeanExperiments.RunningMedian.swap]
      have hRootLeft : root ≤ left := (hHeap 0 (by simp)).1 (by simp)
      have hRootRight : root ≤ right := (hHeap 0 (by simp)).2 (by simp)
      rw [hSift]
      intro index hIndex
      have hIndexBound : index < 4 := by simpa using hIndex
      have hCases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 := by omega
      rcases hCases with h | h | h | h <;> subst index <;> simp_all [MinHeap] <;> omega
    · have hRoot : value < root := by omega
      exact insertHeap_minPrefer_threeElements_of_lt_root hHeap hRoot

/-- 4要素の最大ヒープでは、根を超える追加値を挿入した結果も最大ヒープになる。 -/
theorem insertHeap_maxPrefer_fourElements_of_gt_root
    {root left right leaf value : Nat}
    (hHeap : HeapOrdered LeanExperiments.RunningMedian.maxPrefer
      #[root, left, right, leaf])
    (hValue : root < value) :
    HeapOrdered LeanExperiments.RunningMedian.maxPrefer
      (LeanExperiments.RunningMedian.insertHeap
        LeanExperiments.RunningMedian.maxPrefer #[root, left, right, leaf] value) := by
  have hLeft : left ≤ root := by
    have hEdge := (hHeap 0 (by simp)).1 (by simp)
    simpa [LeanExperiments.RunningMedian.maxPrefer] using hEdge
  have hRight : right ≤ root := by
    have hEdge := (hHeap 0 (by simp)).2 (by simp)
    simpa [LeanExperiments.RunningMedian.maxPrefer] using hEdge
  have hLeaf : leaf ≤ left := by
    have hEdge := (hHeap 1 (by simp)).1 (by simp)
    simpa [LeanExperiments.RunningMedian.maxPrefer] using hEdge
  have hValueLeft : left < value := by omega
  have hSift :
      LeanExperiments.RunningMedian.insertHeap
          LeanExperiments.RunningMedian.maxPrefer #[root, left, right, leaf] value =
        #[value, root, right, leaf, left] := by
    unfold LeanExperiments.RunningMedian.insertHeap
    change LeanExperiments.RunningMedian.siftUp
      LeanExperiments.RunningMedian.maxPrefer #[root, left, right, leaf, value] 4 =
        #[value, root, right, leaf, left]
    rw [siftUp_rightGrandchild_two_steps #[root, left, right, leaf, value] (by simp)
      (by simp [LeanExperiments.RunningMedian.maxPrefer, hValueLeft])
      (by simp [LeanExperiments.RunningMedian.maxPrefer, hValue])]
    simp [LeanExperiments.RunningMedian.swap]
  rw [hSift]
  intro index hIndex
  have hIndexBound : index < 5 := by simpa using hIndex
  have hCases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 := by omega
  rcases hCases with h | h | h | h | h <;> subst index <;>
    simp_all [HeapOrdered, LeanExperiments.RunningMedian.maxPrefer] <;> omega

/-- 4要素の最小ヒープでは、根を下回る追加値を挿入した結果も最小ヒープになる。 -/
theorem insertHeap_minPrefer_fourElements_of_lt_root
    {root left right leaf value : Nat}
    (hHeap : MinHeap #[root, left, right, leaf])
    (hValue : value < root) :
    MinHeap
      (LeanExperiments.RunningMedian.insertHeap
        LeanExperiments.RunningMedian.minPrefer #[root, left, right, leaf] value) := by
  have hLeft : root ≤ left := by
    have hEdge := (hHeap 0 (by simp)).1 (by simp)
    exact hEdge
  have hRight : root ≤ right := by
    have hEdge := (hHeap 0 (by simp)).2 (by simp)
    exact hEdge
  have hLeaf : left ≤ leaf := by
    have hEdge := (hHeap 1 (by simp)).1 (by simp)
    exact hEdge
  have hValueLeft : value < left := by omega
  have hSift :
      LeanExperiments.RunningMedian.insertHeap
          LeanExperiments.RunningMedian.minPrefer #[root, left, right, leaf] value =
        #[value, root, right, leaf, left] := by
    unfold LeanExperiments.RunningMedian.insertHeap
    change LeanExperiments.RunningMedian.siftUp
      LeanExperiments.RunningMedian.minPrefer #[root, left, right, leaf, value] 4 =
        #[value, root, right, leaf, left]
    rw [siftUp_rightGrandchild_two_steps #[root, left, right, leaf, value] (by simp)
      (by simp [LeanExperiments.RunningMedian.minPrefer, hValueLeft])
      (by simp [LeanExperiments.RunningMedian.minPrefer, hValue])]
    simp [LeanExperiments.RunningMedian.swap]
  rw [hSift]
  intro index hIndex
  have hIndexBound : index < 5 := by simpa using hIndex
  have hCases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 := by omega
  rcases hCases with h | h | h | h | h <;> subst index <;> simp_all [MinHeap] <;> omega

/-- 任意の4要素最大ヒープへの挿入は、停止・1回交換・2回交換の全場合で順序を保つ。 -/
theorem insertHeap_maxPrefer_fourElements_preserves
    {root left right leaf value : Nat}
    (hHeap : HeapOrdered LeanExperiments.RunningMedian.maxPrefer
      #[root, left, right, leaf]) :
    HeapOrdered LeanExperiments.RunningMedian.maxPrefer
      (LeanExperiments.RunningMedian.insertHeap
        LeanExperiments.RunningMedian.maxPrefer #[root, left, right, leaf] value) := by
  by_cases hStops : value ≤ left
  · apply insertHeap_HeapOrdered_of_stops LeanExperiments.RunningMedian.maxPrefer
      #[root, left, right, leaf] value hHeap
    right
    simpa [LeanExperiments.RunningMedian.maxPrefer] using hStops
  · have hParent : left < value := by omega
    by_cases hStopsAtRoot : value ≤ root
    · have hSift :
        LeanExperiments.RunningMedian.insertHeap
            LeanExperiments.RunningMedian.maxPrefer #[root, left, right, leaf] value =
          #[root, value, right, leaf, left] := by
        unfold LeanExperiments.RunningMedian.insertHeap
        change LeanExperiments.RunningMedian.siftUp
          LeanExperiments.RunningMedian.maxPrefer #[root, left, right, leaf, value] 4 =
            #[root, value, right, leaf, left]
        rw [siftUp_rightGrandchild_one_step #[root, left, right, leaf, value] (by simp)
          (by simp [LeanExperiments.RunningMedian.maxPrefer, hParent])
          (by simp [LeanExperiments.RunningMedian.maxPrefer, hStopsAtRoot])]
        simp [LeanExperiments.RunningMedian.swap]
      have hRootLeft : left ≤ root := by
        have hEdge := (hHeap 0 (by simp)).1 (by simp)
        simpa [LeanExperiments.RunningMedian.maxPrefer] using hEdge
      have hRootRight : right ≤ root := by
        have hEdge := (hHeap 0 (by simp)).2 (by simp)
        simpa [LeanExperiments.RunningMedian.maxPrefer] using hEdge
      have hLeftLeaf : leaf ≤ left := by
        have hEdge := (hHeap 1 (by simp)).1 (by simp)
        simpa [LeanExperiments.RunningMedian.maxPrefer] using hEdge
      rw [hSift]
      intro index hIndex
      have hIndexBound : index < 5 := by simpa using hIndex
      have hCases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 := by omega
      rcases hCases with h | h | h | h | h <;> subst index <;>
        simp_all [HeapOrdered, LeanExperiments.RunningMedian.maxPrefer] <;> omega
    · have hRoot : root < value := by omega
      exact insertHeap_maxPrefer_fourElements_of_gt_root hHeap hRoot

/-- 任意の4要素最小ヒープへの挿入は、停止・1回交換・2回交換の全場合で順序を保つ。 -/
theorem insertHeap_minPrefer_fourElements_preserves
    {root left right leaf value : Nat}
    (hHeap : MinHeap #[root, left, right, leaf]) :
    MinHeap
      (LeanExperiments.RunningMedian.insertHeap
        LeanExperiments.RunningMedian.minPrefer #[root, left, right, leaf] value) := by
  by_cases hStops : left ≤ value
  · have hOrdered : HeapOrdered LeanExperiments.RunningMedian.minPrefer
        #[root, left, right, leaf] := by
      intro index hIndex
      have hIndexBound : index < 4 := by simpa using hIndex
      have hCases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 := by omega
      rcases hCases with h | h | h | h <;> subst index
      · obtain ⟨hLeft, hRight⟩ := hHeap 0 (by simp)
        constructor
        · intro hChild
          have hEdge := hLeft (by simp)
          simp [LeanExperiments.RunningMedian.minPrefer]
          simp at hEdge
          omega
        · intro hChild
          have hEdge := hRight (by simp)
          simp [LeanExperiments.RunningMedian.minPrefer]
          simp at hEdge
          omega
      · obtain ⟨hChild, _⟩ := hHeap 1 (by simp)
        constructor
        · intro hIsChild
          have hEdge := hChild (by simp)
          simp [LeanExperiments.RunningMedian.minPrefer]
          simp at hEdge
          omega
        · simp
      · simp
      · simp
    have hStoppedOrdered : HeapOrdered LeanExperiments.RunningMedian.minPrefer
        (LeanExperiments.RunningMedian.insertHeap
          LeanExperiments.RunningMedian.minPrefer #[root, left, right, leaf] value) :=
      insertHeap_HeapOrdered_of_stops LeanExperiments.RunningMedian.minPrefer
        #[root, left, right, leaf] value hOrdered (by
          right
          simpa [LeanExperiments.RunningMedian.minPrefer] using hStops)
    intro index hIndex
    obtain ⟨hLeft, hRight⟩ := hStoppedOrdered index hIndex
    constructor
    · intro hChild
      have hEdge := hLeft hChild
      simp [LeanExperiments.RunningMedian.minPrefer] at hEdge
      omega
    · intro hChild
      have hEdge := hRight hChild
      simp [LeanExperiments.RunningMedian.minPrefer] at hEdge
      omega
  · have hParent : value < left := by omega
    by_cases hStopsAtRoot : root ≤ value
    · have hSift :
        LeanExperiments.RunningMedian.insertHeap
            LeanExperiments.RunningMedian.minPrefer #[root, left, right, leaf] value =
          #[root, value, right, leaf, left] := by
        unfold LeanExperiments.RunningMedian.insertHeap
        change LeanExperiments.RunningMedian.siftUp
          LeanExperiments.RunningMedian.minPrefer #[root, left, right, leaf, value] 4 =
            #[root, value, right, leaf, left]
        rw [siftUp_rightGrandchild_one_step #[root, left, right, leaf, value] (by simp)
          (by simp [LeanExperiments.RunningMedian.minPrefer, hParent])
          (by simp [LeanExperiments.RunningMedian.minPrefer, hStopsAtRoot])]
        simp [LeanExperiments.RunningMedian.swap]
      have hRootLeft : root ≤ left := (hHeap 0 (by simp)).1 (by simp)
      have hRootRight : root ≤ right := (hHeap 0 (by simp)).2 (by simp)
      have hLeftLeaf : left ≤ leaf := (hHeap 1 (by simp)).1 (by simp)
      rw [hSift]
      intro index hIndex
      have hIndexBound : index < 5 := by simpa using hIndex
      have hCases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 := by omega
      rcases hCases with h | h | h | h | h <;> subst index <;> simp_all [MinHeap] <;> omega
    · have hRoot : value < root := by omega
      exact insertHeap_minPrefer_fourElements_of_lt_root hHeap hRoot

/-- 任意の5要素最大ヒープへの挿入は、停止・1回交換・2回交換の全場合で順序を保つ。 -/
theorem insertHeap_maxPrefer_fiveElements_preserves
    {root left right leftLeaf rightLeaf value : Nat}
    (hHeap : HeapOrdered LeanExperiments.RunningMedian.maxPrefer
      #[root, left, right, leftLeaf, rightLeaf]) :
    HeapOrdered LeanExperiments.RunningMedian.maxPrefer
      (LeanExperiments.RunningMedian.insertHeap
        LeanExperiments.RunningMedian.maxPrefer
        #[root, left, right, leftLeaf, rightLeaf] value) := by
  by_cases hStops : value ≤ right
  · apply insertHeap_HeapOrdered_of_stops LeanExperiments.RunningMedian.maxPrefer
      #[root, left, right, leftLeaf, rightLeaf] value hHeap
    right
    simpa [LeanExperiments.RunningMedian.maxPrefer] using hStops
  · have hParent : right < value := by omega
    by_cases hStopsAtRoot : value ≤ root
    · have hSift :
        LeanExperiments.RunningMedian.insertHeap
            LeanExperiments.RunningMedian.maxPrefer
            #[root, left, right, leftLeaf, rightLeaf] value =
          #[root, left, value, leftLeaf, rightLeaf, right] := by
        unfold LeanExperiments.RunningMedian.insertHeap
        change LeanExperiments.RunningMedian.siftUp
          LeanExperiments.RunningMedian.maxPrefer
          #[root, left, right, leftLeaf, rightLeaf, value] 5 =
            #[root, left, value, leftLeaf, rightLeaf, right]
        rw [siftUp_leftGrandchildOfRight_one_step
          #[root, left, right, leftLeaf, rightLeaf, value] (by simp)
          (by simp [LeanExperiments.RunningMedian.maxPrefer, hParent])
          (by simp [LeanExperiments.RunningMedian.maxPrefer, hStopsAtRoot])]
        simp [LeanExperiments.RunningMedian.swap]
      have hRootLeft : left ≤ root := by
        have hEdge := (hHeap 0 (by simp)).1 (by simp)
        simpa [LeanExperiments.RunningMedian.maxPrefer] using hEdge
      have hLeftLeaf : leftLeaf ≤ left := by
        have hEdge := (hHeap 1 (by simp)).1 (by simp)
        simpa [LeanExperiments.RunningMedian.maxPrefer] using hEdge
      have hLeftRightLeaf : rightLeaf ≤ left := by
        have hEdge := (hHeap 1 (by simp)).2 (by simp)
        simpa [LeanExperiments.RunningMedian.maxPrefer] using hEdge
      rw [hSift]
      intro index hIndex
      have hIndexBound : index < 6 := by simpa using hIndex
      have hCases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨
          index = 4 ∨ index = 5 := by omega
      rcases hCases with h | h | h | h | h | h <;> subst index <;>
        simp_all [HeapOrdered, LeanExperiments.RunningMedian.maxPrefer] <;> omega
    · have hRoot : root < value := by omega
      have hSift :
          LeanExperiments.RunningMedian.insertHeap
              LeanExperiments.RunningMedian.maxPrefer
              #[root, left, right, leftLeaf, rightLeaf] value =
            #[value, left, root, leftLeaf, rightLeaf, right] := by
        unfold LeanExperiments.RunningMedian.insertHeap
        change LeanExperiments.RunningMedian.siftUp
          LeanExperiments.RunningMedian.maxPrefer
          #[root, left, right, leftLeaf, rightLeaf, value] 5 =
            #[value, left, root, leftLeaf, rightLeaf, right]
        rw [siftUp_leftGrandchildOfRight_two_steps
          #[root, left, right, leftLeaf, rightLeaf, value] (by simp)
          (by simp [LeanExperiments.RunningMedian.maxPrefer, hParent])
          (by simp [LeanExperiments.RunningMedian.maxPrefer, hRoot])]
        simp [LeanExperiments.RunningMedian.swap]
      have hRootLeft : left ≤ root := by
        have hEdge := (hHeap 0 (by simp)).1 (by simp)
        simpa [LeanExperiments.RunningMedian.maxPrefer] using hEdge
      have hRootRight : right ≤ root := by
        have hEdge := (hHeap 0 (by simp)).2 (by simp)
        simpa [LeanExperiments.RunningMedian.maxPrefer] using hEdge
      have hLeftLeaf : leftLeaf ≤ left := by
        have hEdge := (hHeap 1 (by simp)).1 (by simp)
        simpa [LeanExperiments.RunningMedian.maxPrefer] using hEdge
      have hLeftRightLeaf : rightLeaf ≤ left := by
        have hEdge := (hHeap 1 (by simp)).2 (by simp)
        simpa [LeanExperiments.RunningMedian.maxPrefer] using hEdge
      rw [hSift]
      intro index hIndex
      have hIndexBound : index < 6 := by simpa using hIndex
      have hCases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨
          index = 4 ∨ index = 5 := by omega
      rcases hCases with h | h | h | h | h | h <;> subst index <;>
        simp_all [HeapOrdered, LeanExperiments.RunningMedian.maxPrefer] <;> omega

/-- 任意の5要素最小ヒープへの挿入は、停止・1回交換・2回交換の全場合で順序を保つ。 -/
theorem insertHeap_minPrefer_fiveElements_preserves
    {root left right leftLeaf rightLeaf value : Nat}
    (hHeap : MinHeap #[root, left, right, leftLeaf, rightLeaf]) :
    MinHeap
      (LeanExperiments.RunningMedian.insertHeap
        LeanExperiments.RunningMedian.minPrefer
        #[root, left, right, leftLeaf, rightLeaf] value) := by
  have hOrdered : HeapOrdered LeanExperiments.RunningMedian.minPrefer
      #[root, left, right, leftLeaf, rightLeaf] := by
    intro index hIndex
    have hCases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 := by
      have hIndexBound : index < 5 := by simpa using hIndex
      omega
    rcases hCases with h | h | h | h | h <;> subst index
    · obtain ⟨hLeft, hRight⟩ := hHeap 0 (by simp)
      constructor
      · intro hChild
        have hEdge := hLeft (by simp)
        simp [LeanExperiments.RunningMedian.minPrefer]
        simp at hEdge
        omega
      · intro hChild
        have hEdge := hRight (by simp)
        simp [LeanExperiments.RunningMedian.minPrefer]
        simp at hEdge
        omega
    · obtain ⟨hLeft, hRight⟩ := hHeap 1 (by simp)
      constructor
      · intro hChild
        have hEdge := hLeft (by simp)
        simp [LeanExperiments.RunningMedian.minPrefer]
        simp at hEdge
        omega
      · intro hChild
        have hEdge := hRight (by simp)
        simp [LeanExperiments.RunningMedian.minPrefer]
        simp at hEdge
        omega
    · simp
    · simp
    · simp
  by_cases hStops : right ≤ value
  · have hStoppedOrdered : HeapOrdered LeanExperiments.RunningMedian.minPrefer
        (LeanExperiments.RunningMedian.insertHeap
          LeanExperiments.RunningMedian.minPrefer
          #[root, left, right, leftLeaf, rightLeaf] value) :=
      insertHeap_HeapOrdered_of_stops LeanExperiments.RunningMedian.minPrefer
        #[root, left, right, leftLeaf, rightLeaf] value hOrdered (by
          right
          simpa [LeanExperiments.RunningMedian.minPrefer] using hStops)
    intro index hIndex
    obtain ⟨hLeft, hRight⟩ := hStoppedOrdered index hIndex
    constructor
    · intro hChild
      have hEdge := hLeft hChild
      simp [LeanExperiments.RunningMedian.minPrefer] at hEdge
      omega
    · intro hChild
      have hEdge := hRight hChild
      simp [LeanExperiments.RunningMedian.minPrefer] at hEdge
      omega
  · have hParent : value < right := by omega
    by_cases hStopsAtRoot : root ≤ value
    · have hSift :
        LeanExperiments.RunningMedian.insertHeap
            LeanExperiments.RunningMedian.minPrefer
            #[root, left, right, leftLeaf, rightLeaf] value =
          #[root, left, value, leftLeaf, rightLeaf, right] := by
        unfold LeanExperiments.RunningMedian.insertHeap
        change LeanExperiments.RunningMedian.siftUp
          LeanExperiments.RunningMedian.minPrefer
          #[root, left, right, leftLeaf, rightLeaf, value] 5 =
            #[root, left, value, leftLeaf, rightLeaf, right]
        rw [siftUp_leftGrandchildOfRight_one_step
          #[root, left, right, leftLeaf, rightLeaf, value] (by simp)
          (by simp [LeanExperiments.RunningMedian.minPrefer, hParent])
          (by simp [LeanExperiments.RunningMedian.minPrefer, hStopsAtRoot])]
        simp [LeanExperiments.RunningMedian.swap]
      have hRootLeft : root ≤ left := (hHeap 0 (by simp)).1 (by simp)
      have hLeftLeaf : left ≤ leftLeaf := (hHeap 1 (by simp)).1 (by simp)
      have hLeftRightLeaf : left ≤ rightLeaf := (hHeap 1 (by simp)).2 (by simp)
      rw [hSift]
      intro index hIndex
      have hIndexBound : index < 6 := by simpa using hIndex
      have hCases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨
          index = 4 ∨ index = 5 := by omega
      rcases hCases with h | h | h | h | h | h <;> subst index <;>
        simp_all [MinHeap] <;> omega
    · have hRoot : value < root := by omega
      have hSift :
          LeanExperiments.RunningMedian.insertHeap
              LeanExperiments.RunningMedian.minPrefer
              #[root, left, right, leftLeaf, rightLeaf] value =
            #[value, left, root, leftLeaf, rightLeaf, right] := by
        unfold LeanExperiments.RunningMedian.insertHeap
        change LeanExperiments.RunningMedian.siftUp
          LeanExperiments.RunningMedian.minPrefer
          #[root, left, right, leftLeaf, rightLeaf, value] 5 =
            #[value, left, root, leftLeaf, rightLeaf, right]
        rw [siftUp_leftGrandchildOfRight_two_steps
          #[root, left, right, leftLeaf, rightLeaf, value] (by simp)
          (by simp [LeanExperiments.RunningMedian.minPrefer, hParent])
          (by simp [LeanExperiments.RunningMedian.minPrefer, hRoot])]
        simp [LeanExperiments.RunningMedian.swap]
      have hRootLeft : root ≤ left := (hHeap 0 (by simp)).1 (by simp)
      have hRootRight : root ≤ right := (hHeap 0 (by simp)).2 (by simp)
      have hLeftLeaf : left ≤ leftLeaf := (hHeap 1 (by simp)).1 (by simp)
      have hLeftRightLeaf : left ≤ rightLeaf := (hHeap 1 (by simp)).2 (by simp)
      rw [hSift]
      intro index hIndex
      have hIndexBound : index < 6 := by simpa using hIndex
      have hCases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨
          index = 4 ∨ index = 5 := by omega
      rcases hCases with h | h | h | h | h | h <;> subst index <;>
        simp_all [MinHeap] <;> omega

/-- 任意の6要素最大ヒープへの挿入は順序を保つ。

新しい葉の位置は添字6であり、停止・親までの1回交換・根までの2回交換を場合分けする。
-/
theorem insertHeap_maxPrefer_sixElements_preserves
    {root left right leftLeaf rightLeaf middleLeaf value : Nat}
    (hHeap : HeapOrdered LeanExperiments.RunningMedian.maxPrefer
      #[root, left, right, leftLeaf, rightLeaf, middleLeaf]) :
    HeapOrdered LeanExperiments.RunningMedian.maxPrefer
      (LeanExperiments.RunningMedian.insertHeap
        LeanExperiments.RunningMedian.maxPrefer
        #[root, left, right, leftLeaf, rightLeaf, middleLeaf] value) := by
  by_cases hStops : value ≤ right
  · apply insertHeap_HeapOrdered_of_stops LeanExperiments.RunningMedian.maxPrefer
      #[root, left, right, leftLeaf, rightLeaf, middleLeaf] value hHeap
    right
    simpa [LeanExperiments.RunningMedian.maxPrefer] using hStops
  · have hParent : right < value := by omega
    by_cases hStopsAtRoot : value ≤ root
    · have hSift :
        LeanExperiments.RunningMedian.insertHeap LeanExperiments.RunningMedian.maxPrefer
            #[root, left, right, leftLeaf, rightLeaf, middleLeaf] value =
          #[root, left, value, leftLeaf, rightLeaf, middleLeaf, right] := by
        unfold LeanExperiments.RunningMedian.insertHeap
        change LeanExperiments.RunningMedian.siftUp LeanExperiments.RunningMedian.maxPrefer
          #[root, left, right, leftLeaf, rightLeaf, middleLeaf, value] 6 = _
        rw [siftUp_rightGrandchildOfRight_one_step
          #[root, left, right, leftLeaf, rightLeaf, middleLeaf, value] (by simp)
          (by simp [LeanExperiments.RunningMedian.maxPrefer, hParent])
          (by simp [LeanExperiments.RunningMedian.maxPrefer, hStopsAtRoot])]
        simp [LeanExperiments.RunningMedian.swap]
      have hEdges0 := hHeap 0 (by simp)
      have hEdges1 := hHeap 1 (by simp)
      have hEdges2 := hHeap 2 (by simp)
      have hRootLeft : left ≤ root := by
        simpa [LeanExperiments.RunningMedian.maxPrefer] using hEdges0.1 (by simp)
      have hLeftLeaf : leftLeaf ≤ left := by
        simpa [LeanExperiments.RunningMedian.maxPrefer] using hEdges1.1 (by simp)
      have hLeftRightLeaf : rightLeaf ≤ left := by
        simpa [LeanExperiments.RunningMedian.maxPrefer] using hEdges1.2 (by simp)
      have hMiddleLeaf : middleLeaf ≤ right := by
        simpa [LeanExperiments.RunningMedian.maxPrefer] using hEdges2.1 (by simp)
      rw [hSift]
      intro index hIndex
      have hCases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨
          index = 4 ∨ index = 5 ∨ index = 6 := by
        have hBound : index < 7 := by simpa using hIndex
        omega
      rcases hCases with h | h | h | h | h | h | h <;> subst index <;>
        simp_all [HeapOrdered, LeanExperiments.RunningMedian.maxPrefer] <;> omega
    · have hRoot : root < value := by omega
      have hSift :
          LeanExperiments.RunningMedian.insertHeap LeanExperiments.RunningMedian.maxPrefer
              #[root, left, right, leftLeaf, rightLeaf, middleLeaf] value =
            #[value, left, root, leftLeaf, rightLeaf, middleLeaf, right] := by
        unfold LeanExperiments.RunningMedian.insertHeap
        change LeanExperiments.RunningMedian.siftUp LeanExperiments.RunningMedian.maxPrefer
          #[root, left, right, leftLeaf, rightLeaf, middleLeaf, value] 6 = _
        rw [siftUp_rightGrandchildOfRight_two_steps
          #[root, left, right, leftLeaf, rightLeaf, middleLeaf, value] (by simp)
          (by simp [LeanExperiments.RunningMedian.maxPrefer, hParent])
          (by simp [LeanExperiments.RunningMedian.maxPrefer, hRoot])]
        simp [LeanExperiments.RunningMedian.swap]
      have hEdges0 := hHeap 0 (by simp)
      have hEdges1 := hHeap 1 (by simp)
      have hEdges2 := hHeap 2 (by simp)
      have hRootLeft : left ≤ root := by
        simpa [LeanExperiments.RunningMedian.maxPrefer] using hEdges0.1 (by simp)
      have hRootRight : right ≤ root := by
        simpa [LeanExperiments.RunningMedian.maxPrefer] using hEdges0.2 (by simp)
      have hLeftLeaf : leftLeaf ≤ left := by
        simpa [LeanExperiments.RunningMedian.maxPrefer] using hEdges1.1 (by simp)
      have hLeftRightLeaf : rightLeaf ≤ left := by
        simpa [LeanExperiments.RunningMedian.maxPrefer] using hEdges1.2 (by simp)
      have hMiddleLeaf : middleLeaf ≤ right := by
        simpa [LeanExperiments.RunningMedian.maxPrefer] using hEdges2.1 (by simp)
      rw [hSift]
      intro index hIndex
      have hCases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨
          index = 4 ∨ index = 5 ∨ index = 6 := by
        have hBound : index < 7 := by simpa using hIndex
        omega
      rcases hCases with h | h | h | h | h | h | h <;> subst index <;>
        simp_all [HeapOrdered, LeanExperiments.RunningMedian.maxPrefer] <;> omega

/-- サイズ6の任意の最大ヒープへの挿入が最大ヒープ順序を保つ。 -/
theorem insertHeap_maxPrefer_preserves_of_size_six (heap : Array Nat)
    (hSize : heap.size = 6) (value : Nat)
    (hHeap : HeapOrdered maxPrefer heap) :
    HeapOrdered maxPrefer (LeanExperiments.RunningMedian.insertHeap maxPrefer heap value) := by
  let root := heap[0]!
  let left := heap[1]!
  let right := heap[2]!
  let leftLeaf := heap[3]!
  let rightLeaf := heap[4]!
  let middleLeaf := heap[5]!
  have hHeapEq : heap = #[root, left, right, leftLeaf, rightLeaf, middleLeaf] := by
    apply Array.ext
    · simpa using hSize
    · intro index hIndex hBound
      have hCases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨
          index = 4 ∨ index = 5 := by omega
      rcases hCases with h | h | h | h | h | h <;> subst index
      · simpa [root] using (getElem!_pos heap 0 (by omega)).symm
      · simpa [left] using (getElem!_pos heap 1 (by omega)).symm
      · simpa [right] using (getElem!_pos heap 2 (by omega)).symm
      · simpa [leftLeaf] using (getElem!_pos heap 3 (by omega)).symm
      · simpa [rightLeaf] using (getElem!_pos heap 4 (by omega)).symm
      · simpa [middleLeaf] using (getElem!_pos heap 5 (by omega)).symm
  have hTupleHeap : HeapOrdered maxPrefer #[root, left, right, leftLeaf, rightLeaf, middleLeaf] := by
    simpa [hHeapEq] using hHeap
  rw [hHeapEq]
  exact insertHeap_maxPrefer_sixElements_preserves hTupleHeap

/-- 任意の6要素最小ヒープへの挿入は、停止・1回交換・2回交換の全分岐で順序を保つ。 -/
theorem insertHeap_minPrefer_sixElements_preserves
    {root left right leftLeaf rightLeaf middleLeaf value : Nat}
    (hHeap : MinHeap #[root, left, right, leftLeaf, rightLeaf, middleLeaf]) :
    MinHeap
      (LeanExperiments.RunningMedian.insertHeap
        LeanExperiments.RunningMedian.minPrefer
        #[root, left, right, leftLeaf, rightLeaf, middleLeaf] value) := by
  have hOrdered : HeapOrdered LeanExperiments.RunningMedian.minPrefer
      #[root, left, right, leftLeaf, rightLeaf, middleLeaf] := by
    simpa [HeapOrdered, MinHeap, LeanExperiments.RunningMedian.minPrefer] using hHeap
  by_cases hStops : right ≤ value
  · have hStoppedOrdered : HeapOrdered LeanExperiments.RunningMedian.minPrefer
        (LeanExperiments.RunningMedian.insertHeap LeanExperiments.RunningMedian.minPrefer
          #[root, left, right, leftLeaf, rightLeaf, middleLeaf] value) :=
      insertHeap_HeapOrdered_of_stops LeanExperiments.RunningMedian.minPrefer
        #[root, left, right, leftLeaf, rightLeaf, middleLeaf] value hOrdered
        (Or.inr (by
          simp [LeanExperiments.RunningMedian.minPrefer]
          omega))
    intro index hIndex
    obtain ⟨hLeft, hRight⟩ := hStoppedOrdered index hIndex
    constructor
    · intro hChild
      have hEdge := hLeft hChild
      simp [LeanExperiments.RunningMedian.minPrefer] at hEdge
      omega
    · intro hChild
      have hEdge := hRight hChild
      simp [LeanExperiments.RunningMedian.minPrefer] at hEdge
      omega
  · have hParent : value < right := by omega
    by_cases hStopsAtRoot : root ≤ value
    · have hSift :
        LeanExperiments.RunningMedian.insertHeap LeanExperiments.RunningMedian.minPrefer
            #[root, left, right, leftLeaf, rightLeaf, middleLeaf] value =
          #[root, left, value, leftLeaf, rightLeaf, middleLeaf, right] := by
        unfold LeanExperiments.RunningMedian.insertHeap
        change LeanExperiments.RunningMedian.siftUp LeanExperiments.RunningMedian.minPrefer
          #[root, left, right, leftLeaf, rightLeaf, middleLeaf, value] 6 = _
        rw [siftUp_rightGrandchildOfRight_one_step
          #[root, left, right, leftLeaf, rightLeaf, middleLeaf, value] (by simp)
          (by simp [LeanExperiments.RunningMedian.minPrefer, hParent])
          (by simp [LeanExperiments.RunningMedian.minPrefer, hStopsAtRoot])]
        simp [LeanExperiments.RunningMedian.swap]
      have hRootLeft : root ≤ left := (hHeap 0 (by simp)).1 (by simp)
      have hRootRight : root ≤ right := (hHeap 0 (by simp)).2 (by simp)
      have hLeftLeaf : left ≤ leftLeaf := (hHeap 1 (by simp)).1 (by simp)
      have hLeftRightLeaf : left ≤ rightLeaf := (hHeap 1 (by simp)).2 (by simp)
      have hRightMiddleLeaf : right ≤ middleLeaf := (hHeap 2 (by simp)).1 (by simp)
      rw [hSift]
      intro index hIndex
      have hCases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨
          index = 4 ∨ index = 5 ∨ index = 6 := by
        have hBound : index < 7 := by simpa using hIndex
        omega
      rcases hCases with h | h | h | h | h | h | h <;> subst index <;>
        simp_all [MinHeap] <;> omega
    · have hRoot : value < root := by omega
      have hSift :
          LeanExperiments.RunningMedian.insertHeap LeanExperiments.RunningMedian.minPrefer
              #[root, left, right, leftLeaf, rightLeaf, middleLeaf] value =
            #[value, left, root, leftLeaf, rightLeaf, middleLeaf, right] := by
        unfold LeanExperiments.RunningMedian.insertHeap
        change LeanExperiments.RunningMedian.siftUp LeanExperiments.RunningMedian.minPrefer
          #[root, left, right, leftLeaf, rightLeaf, middleLeaf, value] 6 = _
        rw [siftUp_rightGrandchildOfRight_two_steps
          #[root, left, right, leftLeaf, rightLeaf, middleLeaf, value] (by simp)
          (by simp [LeanExperiments.RunningMedian.minPrefer, hParent])
          (by simp [LeanExperiments.RunningMedian.minPrefer, hRoot])]
        simp [LeanExperiments.RunningMedian.swap]
      have hRootLeft : root ≤ left := (hHeap 0 (by simp)).1 (by simp)
      have hRootRight : root ≤ right := (hHeap 0 (by simp)).2 (by simp)
      have hLeftLeaf : left ≤ leftLeaf := (hHeap 1 (by simp)).1 (by simp)
      have hLeftRightLeaf : left ≤ rightLeaf := (hHeap 1 (by simp)).2 (by simp)
      have hRightMiddleLeaf : right ≤ middleLeaf := (hHeap 2 (by simp)).1 (by simp)
      rw [hSift]
      intro index hIndex
      have hCases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨
          index = 4 ∨ index = 5 ∨ index = 6 := by
        have hBound : index < 7 := by simpa using hIndex
        omega
      rcases hCases with h | h | h | h | h | h | h <;> subst index <;>
        simp_all [MinHeap] <;> omega

/-- サイズ6の任意の最小ヒープへの挿入が最小ヒープ順序を保つ。 -/
theorem insertHeap_minPrefer_preserves_of_size_six (heap : Array Nat)
    (hSize : heap.size = 6) (value : Nat) (hHeap : MinHeap heap) :
    MinHeap (LeanExperiments.RunningMedian.insertHeap minPrefer heap value) := by
  let root := heap[0]!
  let left := heap[1]!
  let right := heap[2]!
  let leftLeaf := heap[3]!
  let rightLeaf := heap[4]!
  let middleLeaf := heap[5]!
  have hHeapEq : heap = #[root, left, right, leftLeaf, rightLeaf, middleLeaf] := by
    apply Array.ext
    · simpa using hSize
    · intro index hIndex hBound
      have hCases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨
          index = 4 ∨ index = 5 := by omega
      rcases hCases with h | h | h | h | h | h <;> subst index
      · simpa [root] using (getElem!_pos heap 0 (by omega)).symm
      · simpa [left] using (getElem!_pos heap 1 (by omega)).symm
      · simpa [right] using (getElem!_pos heap 2 (by omega)).symm
      · simpa [leftLeaf] using (getElem!_pos heap 3 (by omega)).symm
      · simpa [rightLeaf] using (getElem!_pos heap 4 (by omega)).symm
      · simpa [middleLeaf] using (getElem!_pos heap 5 (by omega)).symm
  have hTupleHeap : MinHeap #[root, left, right, leftLeaf, rightLeaf, middleLeaf] := by
    simpa [hHeapEq] using hHeap
  rw [hHeapEq]
  exact insertHeap_minPrefer_sixElements_preserves hTupleHeap

/-- 7要素最大ヒープに根以下の値を挿入しても、停止・1回交換・2回交換の全場合で順序を保つ。 -/
theorem insertHeap_maxPrefer_sevenElements_of_le_root
    {root left right leftLeaf rightLeaf rightLeft rightRight value : Nat}
    (hHeap : HeapOrdered LeanExperiments.RunningMedian.maxPrefer
      #[root, left, right, leftLeaf, rightLeaf, rightLeft, rightRight])
    (hValue : value ≤ root) :
    HeapOrdered LeanExperiments.RunningMedian.maxPrefer
      (LeanExperiments.RunningMedian.insertHeap LeanExperiments.RunningMedian.maxPrefer
        #[root, left, right, leftLeaf, rightLeaf, rightLeft, rightRight] value) := by
  have hRootLeft : left ≤ root := by
    have hEdge := (hHeap 0 (by simp)).1 (by simp)
    simpa [LeanExperiments.RunningMedian.maxPrefer] using hEdge
  have hRootRight : right ≤ root := by
    have hEdge := (hHeap 0 (by simp)).2 (by simp)
    simpa [LeanExperiments.RunningMedian.maxPrefer] using hEdge
  have hLeftLeaf : leftLeaf ≤ left := by
    have hEdge := (hHeap 1 (by simp)).1 (by simp)
    simpa [LeanExperiments.RunningMedian.maxPrefer] using hEdge
  have hLeftRightLeaf : rightLeaf ≤ left := by
    have hEdge := (hHeap 1 (by simp)).2 (by simp)
    simpa [LeanExperiments.RunningMedian.maxPrefer] using hEdge
  have hRightLeft : rightLeft ≤ right := by
    have hEdge := (hHeap 2 (by simp)).1 (by simp)
    simpa [LeanExperiments.RunningMedian.maxPrefer] using hEdge
  have hRightRight : rightRight ≤ right := by
    have hEdge := (hHeap 2 (by simp)).2 (by simp)
    simpa [LeanExperiments.RunningMedian.maxPrefer] using hEdge
  by_cases hStops : value ≤ leftLeaf
  · exact insertHeap_HeapOrdered_of_stops LeanExperiments.RunningMedian.maxPrefer
      #[root, left, right, leftLeaf, rightLeaf, rightLeft, rightRight] value hHeap
      (Or.inr (by simpa [LeanExperiments.RunningMedian.maxPrefer] using hStops))
  · have hParent : leftLeaf < value := by omega
    by_cases hStopsAtAncestor : value ≤ left
    · have hSift :
        LeanExperiments.RunningMedian.insertHeap LeanExperiments.RunningMedian.maxPrefer
            #[root, left, right, leftLeaf, rightLeaf, rightLeft, rightRight] value =
          #[root, left, right, value, rightLeaf, rightLeft, rightRight, leftLeaf] := by
        unfold LeanExperiments.RunningMedian.insertHeap
        change LeanExperiments.RunningMedian.siftUp LeanExperiments.RunningMedian.maxPrefer
          #[root, left, right, leftLeaf, rightLeaf, rightLeft, rightRight, value] 7 = _
        rw [siftUp_leftGreatGrandchild_one_step _ (by simp)
          (by simp [LeanExperiments.RunningMedian.maxPrefer, hParent])
          (by simp [LeanExperiments.RunningMedian.maxPrefer, hStopsAtAncestor])]
        simp [LeanExperiments.RunningMedian.swap]
      rw [hSift]
      intro index hIndex
      have hCases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 ∨
          index = 5 ∨ index = 6 ∨ index = 7 := by
        have hBound : index < 8 := by simpa using hIndex
        omega
      rcases hCases with h | h | h | h | h | h | h | h <;> subst index <;>
        simp_all [HeapOrdered, LeanExperiments.RunningMedian.maxPrefer] <;> omega
    · have hAncestor : left < value := by omega
      have hSift :
        LeanExperiments.RunningMedian.insertHeap LeanExperiments.RunningMedian.maxPrefer
            #[root, left, right, leftLeaf, rightLeaf, rightLeft, rightRight] value =
          #[root, value, right, left, rightLeaf, rightLeft, rightRight, leftLeaf] := by
        unfold LeanExperiments.RunningMedian.insertHeap
        change LeanExperiments.RunningMedian.siftUp LeanExperiments.RunningMedian.maxPrefer
          #[root, left, right, leftLeaf, rightLeaf, rightLeft, rightRight, value] 7 = _
        rw [siftUp_leftGreatGrandchild_two_steps _ (by simp)
          (by simp [LeanExperiments.RunningMedian.maxPrefer, hParent])
          (by simp [LeanExperiments.RunningMedian.maxPrefer, hAncestor])
          (by simp [LeanExperiments.RunningMedian.maxPrefer, hValue])]
        simp [LeanExperiments.RunningMedian.swap]
      rw [hSift]
      intro index hIndex
      have hCases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 ∨
          index = 5 ∨ index = 6 ∨ index = 7 := by
        have hBound : index < 8 := by simpa using hIndex
        omega
      rcases hCases with h | h | h | h | h | h | h | h <;> subst index <;>
        simp_all [HeapOrdered, LeanExperiments.RunningMedian.maxPrefer] <;> omega

/-- 根より大きい値を7要素最大ヒープへ挿入しても、3段の経路で順序を保つ。 -/
theorem insertHeap_maxPrefer_sevenElements_of_gt_root
    {root left right leftLeaf rightLeaf rightLeft rightRight value : Nat}
    (hHeap : HeapOrdered LeanExperiments.RunningMedian.maxPrefer
      #[root, left, right, leftLeaf, rightLeaf, rightLeft, rightRight])
    (hValue : root < value) :
    HeapOrdered LeanExperiments.RunningMedian.maxPrefer
      (LeanExperiments.RunningMedian.insertHeap LeanExperiments.RunningMedian.maxPrefer
        #[root, left, right, leftLeaf, rightLeaf, rightLeft, rightRight] value) := by
  have hRootLeft : left ≤ root := by
    have hEdge := (hHeap 0 (by simp)).1 (by simp)
    simpa [LeanExperiments.RunningMedian.maxPrefer] using hEdge
  have hRootRight : right ≤ root := by
    have hEdge := (hHeap 0 (by simp)).2 (by simp)
    simpa [LeanExperiments.RunningMedian.maxPrefer] using hEdge
  have hLeftLeaf : leftLeaf ≤ left := by
    have hEdge := (hHeap 1 (by simp)).1 (by simp)
    simpa [LeanExperiments.RunningMedian.maxPrefer] using hEdge
  have hLeftRightLeaf : rightLeaf ≤ left := by
    have hEdge := (hHeap 1 (by simp)).2 (by simp)
    simpa [LeanExperiments.RunningMedian.maxPrefer] using hEdge
  have hRightLeft : rightLeft ≤ right := by
    have hEdge := (hHeap 2 (by simp)).1 (by simp)
    simpa [LeanExperiments.RunningMedian.maxPrefer] using hEdge
  have hRightRight : rightRight ≤ right := by
    have hEdge := (hHeap 2 (by simp)).2 (by simp)
    simpa [LeanExperiments.RunningMedian.maxPrefer] using hEdge
  by_cases hStops : value ≤ leftLeaf
  · exact insertHeap_HeapOrdered_of_stops LeanExperiments.RunningMedian.maxPrefer
      #[root, left, right, leftLeaf, rightLeaf, rightLeft, rightRight] value hHeap
      (Or.inr (by simpa [LeanExperiments.RunningMedian.maxPrefer] using hStops))
  · have hParent : leftLeaf < value := by omega
    by_cases hStopsAtAncestor : value ≤ left
    · have hSift :
        LeanExperiments.RunningMedian.insertHeap LeanExperiments.RunningMedian.maxPrefer
            #[root, left, right, leftLeaf, rightLeaf, rightLeft, rightRight] value =
          #[root, left, right, value, rightLeaf, rightLeft, rightRight, leftLeaf] := by
        unfold LeanExperiments.RunningMedian.insertHeap
        change LeanExperiments.RunningMedian.siftUp LeanExperiments.RunningMedian.maxPrefer
          #[root, left, right, leftLeaf, rightLeaf, rightLeft, rightRight, value] 7 = _
        rw [siftUp_leftGreatGrandchild_one_step _ (by simp)
          (by simp [LeanExperiments.RunningMedian.maxPrefer, hParent])
          (by simp [LeanExperiments.RunningMedian.maxPrefer, hStopsAtAncestor])]
        simp [LeanExperiments.RunningMedian.swap]
      rw [hSift]
      intro index hIndex
      have hCases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 ∨
          index = 5 ∨ index = 6 ∨ index = 7 := by
        have hBound : index < 8 := by simpa using hIndex
        omega
      rcases hCases with h | h | h | h | h | h | h | h <;> subst index <;>
        simp_all [HeapOrdered, LeanExperiments.RunningMedian.maxPrefer] <;> omega
    · have hAncestor : left < value := by omega
      by_cases hStopsAtRoot : value ≤ root
      · have hSift :
          LeanExperiments.RunningMedian.insertHeap LeanExperiments.RunningMedian.maxPrefer
              #[root, left, right, leftLeaf, rightLeaf, rightLeft, rightRight] value =
            #[root, value, right, left, rightLeaf, rightLeft, rightRight, leftLeaf] := by
          unfold LeanExperiments.RunningMedian.insertHeap
          change LeanExperiments.RunningMedian.siftUp LeanExperiments.RunningMedian.maxPrefer
            #[root, left, right, leftLeaf, rightLeaf, rightLeft, rightRight, value] 7 = _
          rw [siftUp_leftGreatGrandchild_two_steps _ (by simp)
            (by simp [LeanExperiments.RunningMedian.maxPrefer, hParent])
            (by simp [LeanExperiments.RunningMedian.maxPrefer, hAncestor])
            (by simp [LeanExperiments.RunningMedian.maxPrefer, hStopsAtRoot])]
          simp [LeanExperiments.RunningMedian.swap]
        rw [hSift]
        intro index hIndex
        have hCases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 ∨
            index = 5 ∨ index = 6 ∨ index = 7 := by
          have hBound : index < 8 := by simpa using hIndex
          omega
        rcases hCases with h | h | h | h | h | h | h | h <;> subst index <;>
          simp_all [HeapOrdered, LeanExperiments.RunningMedian.maxPrefer] <;> omega
      · have hRoot : root < value := by omega
        have hSift :
          LeanExperiments.RunningMedian.insertHeap LeanExperiments.RunningMedian.maxPrefer
              #[root, left, right, leftLeaf, rightLeaf, rightLeft, rightRight] value =
            #[value, root, right, left, rightLeaf, rightLeft, rightRight, leftLeaf] := by
          unfold LeanExperiments.RunningMedian.insertHeap
          change LeanExperiments.RunningMedian.siftUp LeanExperiments.RunningMedian.maxPrefer
            #[root, left, right, leftLeaf, rightLeaf, rightLeft, rightRight, value] 7 = _
          rw [siftUp_leftGreatGrandchild_three_steps _ (by simp)
            (by simp [LeanExperiments.RunningMedian.maxPrefer, hParent])
            (by simp [LeanExperiments.RunningMedian.maxPrefer, hAncestor])
            (by simp [LeanExperiments.RunningMedian.maxPrefer, hRoot])]
          simp [LeanExperiments.RunningMedian.swap]
        rw [hSift]
        intro index hIndex
        have hCases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 ∨
            index = 5 ∨ index = 6 ∨ index = 7 := by
          have hBound : index < 8 := by simpa using hIndex
          omega
        rcases hCases with h | h | h | h | h | h | h | h <;> subst index <;>
          simp_all [HeapOrdered, LeanExperiments.RunningMedian.maxPrefer] <;> omega

/-- 7要素の任意の最大ヒープへの挿入は、移動段数にかかわらず順序を保つ。 -/
theorem insertHeap_maxPrefer_sevenElements_preserves
    {root left right leftLeaf rightLeaf rightLeft rightRight value : Nat}
    (hHeap : HeapOrdered LeanExperiments.RunningMedian.maxPrefer
      #[root, left, right, leftLeaf, rightLeaf, rightLeft, rightRight]) :
    HeapOrdered LeanExperiments.RunningMedian.maxPrefer
      (LeanExperiments.RunningMedian.insertHeap LeanExperiments.RunningMedian.maxPrefer
        #[root, left, right, leftLeaf, rightLeaf, rightLeft, rightRight] value) := by
  by_cases hValue : value ≤ root
  · exact insertHeap_maxPrefer_sevenElements_of_le_root hHeap hValue
  · exact insertHeap_maxPrefer_sevenElements_of_gt_root hHeap (by omega)

/-- 8要素の任意の最大ヒープへの挿入は、添字8から根までの順序を保つ。 -/
theorem insertHeap_maxPrefer_eightElements_preserves
    {root left right leftLeft leftRight rightLeft rightRight leftLeftLeaf value : Nat}
    (hHeap : HeapOrdered LeanExperiments.RunningMedian.maxPrefer
      #[root, left, right, leftLeft, leftRight, rightLeft, rightRight, leftLeftLeaf]) :
    HeapOrdered LeanExperiments.RunningMedian.maxPrefer
      (LeanExperiments.RunningMedian.insertHeap LeanExperiments.RunningMedian.maxPrefer
        #[root, left, right, leftLeft, leftRight, rightLeft, rightRight, leftLeftLeaf] value) := by
  have hRootLeft : left ≤ root := by
    have hEdge := (hHeap 0 (by simp)).1 (by simp)
    simpa [LeanExperiments.RunningMedian.maxPrefer] using hEdge
  have hRootRight : right ≤ root := by
    have hEdge := (hHeap 0 (by simp)).2 (by simp)
    simpa [LeanExperiments.RunningMedian.maxPrefer] using hEdge
  have hLeftLeft : leftLeft ≤ left := by
    have hEdge := (hHeap 1 (by simp)).1 (by simp)
    simpa [LeanExperiments.RunningMedian.maxPrefer] using hEdge
  have hLeftRight : leftRight ≤ left := by
    have hEdge := (hHeap 1 (by simp)).2 (by simp)
    simpa [LeanExperiments.RunningMedian.maxPrefer] using hEdge
  have hRightLeft : rightLeft ≤ right := by
    have hEdge := (hHeap 2 (by simp)).1 (by simp)
    simpa [LeanExperiments.RunningMedian.maxPrefer] using hEdge
  have hRightRight : rightRight ≤ right := by
    have hEdge := (hHeap 2 (by simp)).2 (by simp)
    simpa [LeanExperiments.RunningMedian.maxPrefer] using hEdge
  have hLeftLeftLeaf : leftLeftLeaf ≤ leftLeft := by
    have hEdge := (hHeap 3 (by simp)).1 (by simp)
    simpa [LeanExperiments.RunningMedian.maxPrefer] using hEdge
  by_cases hStops : value ≤ leftLeft
  · exact insertHeap_HeapOrdered_of_stops LeanExperiments.RunningMedian.maxPrefer
      #[root, left, right, leftLeft, leftRight, rightLeft, rightRight, leftLeftLeaf]
      value hHeap (Or.inr (by simpa [LeanExperiments.RunningMedian.maxPrefer] using hStops))
  · have hParent : leftLeft < value := by omega
    by_cases hStopsAtAncestor : value ≤ left
    · have hSift :
        LeanExperiments.RunningMedian.insertHeap LeanExperiments.RunningMedian.maxPrefer
            #[root, left, right, leftLeft, leftRight, rightLeft, rightRight, leftLeftLeaf] value =
          #[root, left, right, value, leftRight, rightLeft, rightRight, leftLeftLeaf, leftLeft] := by
        unfold LeanExperiments.RunningMedian.insertHeap
        change LeanExperiments.RunningMedian.siftUp LeanExperiments.RunningMedian.maxPrefer
          #[root, left, right, leftLeft, leftRight, rightLeft, rightRight, leftLeftLeaf, value] 8 = _
        rw [siftUp_rightGreatGrandchild_one_step _ (by simp)
          (by simp [LeanExperiments.RunningMedian.maxPrefer, hParent])
          (by simp [LeanExperiments.RunningMedian.maxPrefer, hStopsAtAncestor])]
        simp [LeanExperiments.RunningMedian.swap]
      rw [hSift]
      intro index hIndex
      have hBound : index < 9 := by simpa using hIndex
      have hCases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 ∨
          index = 5 ∨ index = 6 ∨ index = 7 ∨ index = 8 := by omega
      rcases hCases with h | h | h | h | h | h | h | h | h <;> subst index <;>
        simp_all [HeapOrdered, LeanExperiments.RunningMedian.maxPrefer] <;> omega
    · have hAncestor : left < value := by omega
      by_cases hStopsAtRoot : value ≤ root
      · have hSift :
          LeanExperiments.RunningMedian.insertHeap LeanExperiments.RunningMedian.maxPrefer
              #[root, left, right, leftLeft, leftRight, rightLeft, rightRight, leftLeftLeaf] value =
            #[root, value, right, left, leftRight, rightLeft, rightRight, leftLeftLeaf, leftLeft] := by
          unfold LeanExperiments.RunningMedian.insertHeap
          change LeanExperiments.RunningMedian.siftUp LeanExperiments.RunningMedian.maxPrefer
            #[root, left, right, leftLeft, leftRight, rightLeft, rightRight, leftLeftLeaf, value] 8 = _
          rw [siftUp_rightGreatGrandchild_two_steps _ (by simp)
            (by simp [LeanExperiments.RunningMedian.maxPrefer, hParent])
            (by simp [LeanExperiments.RunningMedian.maxPrefer, hAncestor])
            (by simp [LeanExperiments.RunningMedian.maxPrefer, hStopsAtRoot])]
          simp [LeanExperiments.RunningMedian.swap]
        rw [hSift]
        intro index hIndex
        have hBound : index < 9 := by simpa using hIndex
        have hCases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 ∨
            index = 5 ∨ index = 6 ∨ index = 7 ∨ index = 8 := by omega
        rcases hCases with h | h | h | h | h | h | h | h | h <;> subst index <;>
          simp_all [HeapOrdered, LeanExperiments.RunningMedian.maxPrefer] <;> omega
      · have hRoot : root < value := by omega
        have hSift :
          LeanExperiments.RunningMedian.insertHeap LeanExperiments.RunningMedian.maxPrefer
              #[root, left, right, leftLeft, leftRight, rightLeft, rightRight, leftLeftLeaf] value =
            #[value, root, right, left, leftRight, rightLeft, rightRight, leftLeftLeaf, leftLeft] := by
          unfold LeanExperiments.RunningMedian.insertHeap
          change LeanExperiments.RunningMedian.siftUp LeanExperiments.RunningMedian.maxPrefer
            #[root, left, right, leftLeft, leftRight, rightLeft, rightRight, leftLeftLeaf, value] 8 = _
          rw [siftUp_rightGreatGrandchild_three_steps _ (by simp)
            (by simp [LeanExperiments.RunningMedian.maxPrefer, hParent])
            (by simp [LeanExperiments.RunningMedian.maxPrefer, hAncestor])
            (by simp [LeanExperiments.RunningMedian.maxPrefer, hRoot])]
          simp [LeanExperiments.RunningMedian.swap]
        rw [hSift]
        intro index hIndex
        have hBound : index < 9 := by simpa using hIndex
        have hCases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 ∨
            index = 5 ∨ index = 6 ∨ index = 7 ∨ index = 8 := by omega
        rcases hCases with h | h | h | h | h | h | h | h | h <;> subst index <;>
          simp_all [HeapOrdered, LeanExperiments.RunningMedian.maxPrefer] <;> omega

/-- 7要素最小ヒープへの挿入は、添字7から根までの全交換段数で順序を保つ。 -/
theorem insertHeap_minPrefer_sevenElements_preserves
    {root left right leftLeaf rightLeaf rightLeft rightRight value : Nat}
    (hHeap : MinHeap #[root, left, right, leftLeaf, rightLeaf, rightLeft, rightRight]) :
    MinHeap (LeanExperiments.RunningMedian.insertHeap minPrefer
      #[root, left, right, leftLeaf, rightLeaf, rightLeft, rightRight] value) := by
  by_cases hStops : leftLeaf ≤ value
  · have hOrdered : HeapOrdered minPrefer
        #[root, left, right, leftLeaf, rightLeaf, rightLeft, rightRight] := by
      simpa [HeapOrdered, MinHeap, minPrefer] using hHeap
    have hStopped : HeapOrdered minPrefer
        (LeanExperiments.RunningMedian.insertHeap minPrefer
          #[root, left, right, leftLeaf, rightLeaf, rightLeft, rightRight] value) :=
      insertHeap_HeapOrdered_of_stops minPrefer
        #[root, left, right, leftLeaf, rightLeaf, rightLeft, rightRight] value hOrdered
        (Or.inr (by simpa [minPrefer] using hStops))
    intro index hIndex
    obtain ⟨hLeft, hRight⟩ := hStopped index hIndex
    constructor
    · intro hChild
      have hEdge := hLeft hChild
      simp [minPrefer] at hEdge
      omega
    · intro hChild
      have hEdge := hRight hChild
      simp [minPrefer] at hEdge
      omega
  · have hParent : value < leftLeaf := by omega
    by_cases hStopsAtParent : left ≤ value
    · have hSift :
        LeanExperiments.RunningMedian.insertHeap minPrefer
            #[root, left, right, leftLeaf, rightLeaf, rightLeft, rightRight] value =
          #[root, left, right, value, rightLeaf, rightLeft, rightRight, leftLeaf] := by
        unfold LeanExperiments.RunningMedian.insertHeap
        change LeanExperiments.RunningMedian.siftUp minPrefer
          #[root, left, right, leftLeaf, rightLeaf, rightLeft, rightRight, value] 7 = _
        rw [siftUp_leftGreatGrandchild_one_step
          #[root, left, right, leftLeaf, rightLeaf, rightLeft, rightRight, value] (by simp)
          (by simp [minPrefer, hParent]) (by simp [minPrefer, hStopsAtParent])]
        simp [LeanExperiments.RunningMedian.swap]
      rw [hSift]
      intro index hIndex
      have hRootLeft : root ≤ left := (hHeap 0 (by simp)).1 (by simp)
      have hRootRight : root ≤ right := (hHeap 0 (by simp)).2 (by simp)
      have hLeftLeaf : left ≤ leftLeaf := (hHeap 1 (by simp)).1 (by simp)
      have hLeftRightLeaf : left ≤ rightLeaf := (hHeap 1 (by simp)).2 (by simp)
      have hRightLeftLeaf : right ≤ rightLeft := (hHeap 2 (by simp)).1 (by simp)
      have hRightRightLeaf : right ≤ rightRight := (hHeap 2 (by simp)).2 (by simp)
      have hCases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨
          index = 4 ∨ index = 5 ∨ index = 6 ∨ index = 7 := by
        have hBound : index < 8 := by simpa using hIndex
        omega
      rcases hCases with h | h | h | h | h | h | h | h <;> subst index <;>
        simp_all [MinHeap] <;> omega
    · have hAncestor : value < left := by omega
      by_cases hStopsAtRoot : root ≤ value
      · have hSift :
          LeanExperiments.RunningMedian.insertHeap minPrefer
              #[root, left, right, leftLeaf, rightLeaf, rightLeft, rightRight] value =
            #[root, value, right, left, rightLeaf, rightLeft, rightRight, leftLeaf] := by
          unfold LeanExperiments.RunningMedian.insertHeap
          change LeanExperiments.RunningMedian.siftUp minPrefer
            #[root, left, right, leftLeaf, rightLeaf, rightLeft, rightRight, value] 7 = _
          rw [siftUp_leftGreatGrandchild_two_steps
            #[root, left, right, leftLeaf, rightLeaf, rightLeft, rightRight, value] (by simp)
            (by simp [minPrefer, hParent]) (by simp [minPrefer, hAncestor])
            (by simp [minPrefer, hStopsAtRoot])]
          simp [LeanExperiments.RunningMedian.swap]
        rw [hSift]
        intro index hIndex
        have hRootLeft : root ≤ left := (hHeap 0 (by simp)).1 (by simp)
        have hRootRight : root ≤ right := (hHeap 0 (by simp)).2 (by simp)
        have hLeftLeaf : left ≤ leftLeaf := (hHeap 1 (by simp)).1 (by simp)
        have hLeftRightLeaf : left ≤ rightLeaf := (hHeap 1 (by simp)).2 (by simp)
        have hRightLeftLeaf : right ≤ rightLeft := (hHeap 2 (by simp)).1 (by simp)
        have hRightRightLeaf : right ≤ rightRight := (hHeap 2 (by simp)).2 (by simp)
        have hCases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨
            index = 4 ∨ index = 5 ∨ index = 6 ∨ index = 7 := by
          have hBound : index < 8 := by simpa using hIndex
          omega
        rcases hCases with h | h | h | h | h | h | h | h <;> subst index <;>
          simp_all [MinHeap] <;> omega
      · have hRoot : value < root := by omega
        have hSift :
            LeanExperiments.RunningMedian.insertHeap minPrefer
                #[root, left, right, leftLeaf, rightLeaf, rightLeft, rightRight] value =
              #[value, root, right, left, rightLeaf, rightLeft, rightRight, leftLeaf] := by
          unfold LeanExperiments.RunningMedian.insertHeap
          change LeanExperiments.RunningMedian.siftUp minPrefer
            #[root, left, right, leftLeaf, rightLeaf, rightLeft, rightRight, value] 7 = _
          rw [siftUp_leftGreatGrandchild_three_steps
            #[root, left, right, leftLeaf, rightLeaf, rightLeft, rightRight, value] (by simp)
            (by simp [minPrefer, hParent]) (by simp [minPrefer, hAncestor])
            (by simp [minPrefer, hRoot])]
          simp [LeanExperiments.RunningMedian.swap]
        rw [hSift]
        intro index hIndex
        have hRootLeft : root ≤ left := (hHeap 0 (by simp)).1 (by simp)
        have hRootRight : root ≤ right := (hHeap 0 (by simp)).2 (by simp)
        have hLeftLeaf : left ≤ leftLeaf := (hHeap 1 (by simp)).1 (by simp)
        have hLeftRightLeaf : left ≤ rightLeaf := (hHeap 1 (by simp)).2 (by simp)
        have hRightLeftLeaf : right ≤ rightLeft := (hHeap 2 (by simp)).1 (by simp)
        have hRightRightLeaf : right ≤ rightRight := (hHeap 2 (by simp)).2 (by simp)
        have hCases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨
            index = 4 ∨ index = 5 ∨ index = 6 ∨ index = 7 := by
          have hBound : index < 8 := by simpa using hIndex
          omega
        rcases hCases with h | h | h | h | h | h | h | h <;> subst index <;>
          simp_all [MinHeap] <;> omega

/-- 8要素の任意の最小ヒープへの挿入は、添字8から根までの順序を保つ。 -/
theorem insertHeap_minPrefer_eightElements_preserves
    {root left right leftLeft leftRight rightLeft rightRight leftLeftLeaf value : Nat}
    (hHeap : MinHeap
      #[root, left, right, leftLeft, leftRight, rightLeft, rightRight, leftLeftLeaf]) :
    MinHeap (LeanExperiments.RunningMedian.insertHeap minPrefer
      #[root, left, right, leftLeft, leftRight, rightLeft, rightRight, leftLeftLeaf] value) := by
  have hOrdered : HeapOrdered minPrefer
      #[root, left, right, leftLeft, leftRight, rightLeft, rightRight, leftLeftLeaf] := by
    simpa [HeapOrdered, MinHeap, minPrefer] using hHeap
  have hRootLeft : root ≤ left := (hHeap 0 (by simp)).1 (by simp)
  have hRootRight : root ≤ right := (hHeap 0 (by simp)).2 (by simp)
  have hLeftLeft : left ≤ leftLeft := (hHeap 1 (by simp)).1 (by simp)
  have hLeftRight : left ≤ leftRight := (hHeap 1 (by simp)).2 (by simp)
  have hRightLeft : right ≤ rightLeft := (hHeap 2 (by simp)).1 (by simp)
  have hRightRight : right ≤ rightRight := (hHeap 2 (by simp)).2 (by simp)
  have hLeftLeftLeaf : leftLeft ≤ leftLeftLeaf := (hHeap 3 (by simp)).1 (by simp)
  by_cases hStops : leftLeft ≤ value
  · have hStopped : HeapOrdered minPrefer
        (LeanExperiments.RunningMedian.insertHeap minPrefer
          #[root, left, right, leftLeft, leftRight, rightLeft, rightRight, leftLeftLeaf] value) :=
      insertHeap_HeapOrdered_of_stops minPrefer
        #[root, left, right, leftLeft, leftRight, rightLeft, rightRight, leftLeftLeaf]
        value hOrdered (Or.inr (by simpa [minPrefer] using hStops))
    intro index hIndex
    obtain ⟨hLeft, hRight⟩ := hStopped index hIndex
    constructor
    · intro hChild
      have hEdge := hLeft hChild
      simpa [MinHeap, minPrefer] using hEdge
    · intro hChild
      have hEdge := hRight hChild
      simpa [MinHeap, minPrefer] using hEdge
  · have hParent : value < leftLeft := by omega
    by_cases hStopsAtAncestor : left ≤ value
    · have hSift :
        LeanExperiments.RunningMedian.insertHeap minPrefer
            #[root, left, right, leftLeft, leftRight, rightLeft, rightRight, leftLeftLeaf] value =
          #[root, left, right, value, leftRight, rightLeft, rightRight, leftLeftLeaf, leftLeft] := by
        unfold LeanExperiments.RunningMedian.insertHeap
        change LeanExperiments.RunningMedian.siftUp minPrefer
          #[root, left, right, leftLeft, leftRight, rightLeft, rightRight, leftLeftLeaf, value] 8 = _
        rw [siftUp_rightGreatGrandchild_one_step _ (by simp)
          (by simp [minPrefer, hParent]) (by simp [minPrefer, hStopsAtAncestor])]
        simp [LeanExperiments.RunningMedian.swap]
      rw [hSift]
      intro index hIndex
      have hCases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 ∨
          index = 5 ∨ index = 6 ∨ index = 7 ∨ index = 8 := by
        have hBound : index < 9 := by simpa using hIndex
        omega
      rcases hCases with h | h | h | h | h | h | h | h | h <;> subst index <;>
        simp_all [MinHeap] <;> omega
    · have hAncestor : value < left := by omega
      by_cases hStopsAtRoot : root ≤ value
      · have hSift :
          LeanExperiments.RunningMedian.insertHeap minPrefer
              #[root, left, right, leftLeft, leftRight, rightLeft, rightRight, leftLeftLeaf] value =
            #[root, value, right, left, leftRight, rightLeft, rightRight, leftLeftLeaf, leftLeft] := by
          unfold LeanExperiments.RunningMedian.insertHeap
          change LeanExperiments.RunningMedian.siftUp minPrefer
            #[root, left, right, leftLeft, leftRight, rightLeft, rightRight, leftLeftLeaf, value] 8 = _
          rw [siftUp_rightGreatGrandchild_two_steps _ (by simp)
            (by simp [minPrefer, hParent]) (by simp [minPrefer, hAncestor])
            (by simp [minPrefer, hStopsAtRoot])]
          simp [LeanExperiments.RunningMedian.swap]
        rw [hSift]
        intro index hIndex
        have hCases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 ∨
            index = 5 ∨ index = 6 ∨ index = 7 ∨ index = 8 := by
          have hBound : index < 9 := by simpa using hIndex
          omega
        rcases hCases with h | h | h | h | h | h | h | h | h <;> subst index <;>
          simp_all [MinHeap] <;> omega
      · have hRoot : value < root := by omega
        have hSift :
          LeanExperiments.RunningMedian.insertHeap minPrefer
              #[root, left, right, leftLeft, leftRight, rightLeft, rightRight, leftLeftLeaf] value =
            #[value, root, right, left, leftRight, rightLeft, rightRight, leftLeftLeaf, leftLeft] := by
          unfold LeanExperiments.RunningMedian.insertHeap
          change LeanExperiments.RunningMedian.siftUp minPrefer
            #[root, left, right, leftLeft, leftRight, rightLeft, rightRight, leftLeftLeaf, value] 8 = _
          rw [siftUp_rightGreatGrandchild_three_steps _ (by simp)
            (by simp [minPrefer, hParent]) (by simp [minPrefer, hAncestor])
            (by simp [minPrefer, hRoot])]
          simp [LeanExperiments.RunningMedian.swap]
        rw [hSift]
        intro index hIndex
        have hCases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 ∨
            index = 5 ∨ index = 6 ∨ index = 7 ∨ index = 8 := by
          have hBound : index < 9 := by simpa using hIndex
          omega
        rcases hCases with h | h | h | h | h | h | h | h | h <;> subst index <;>
          simp_all [MinHeap] <;> omega

/-- サイズ7の任意の最小ヒープへの挿入が最小ヒープ順序を保つ。 -/
theorem insertHeap_minPrefer_preserves_of_size_seven (heap : Array Nat)
    (hSize : heap.size = 7) (value : Nat) (hHeap : MinHeap heap) :
    MinHeap (LeanExperiments.RunningMedian.insertHeap minPrefer heap value) := by
  let root := heap[0]!
  let left := heap[1]!
  let right := heap[2]!
  let leftLeaf := heap[3]!
  let rightLeaf := heap[4]!
  let rightLeft := heap[5]!
  let rightRight := heap[6]!
  have hHeapEq : heap = #[root, left, right, leftLeaf, rightLeaf, rightLeft, rightRight] := by
    apply Array.ext
    · simpa using hSize
    · intro index hIndex hBound
      have hCases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨
          index = 4 ∨ index = 5 ∨ index = 6 := by omega
      rcases hCases with h | h | h | h | h | h | h <;> subst index
      · simpa [root] using (getElem!_pos heap 0 (by omega)).symm
      · simpa [left] using (getElem!_pos heap 1 (by omega)).symm
      · simpa [right] using (getElem!_pos heap 2 (by omega)).symm
      · simpa [leftLeaf] using (getElem!_pos heap 3 (by omega)).symm
      · simpa [rightLeaf] using (getElem!_pos heap 4 (by omega)).symm
      · simpa [rightLeft] using (getElem!_pos heap 5 (by omega)).symm
      · simpa [rightRight] using (getElem!_pos heap 6 (by omega)).symm
  have hTupleHeap : MinHeap #[root, left, right, leftLeaf, rightLeaf, rightLeft, rightRight] := by
    simpa [hHeapEq] using hHeap
  rw [hHeapEq]
  exact insertHeap_minPrefer_sevenElements_preserves hTupleHeap

/-- サイズ7の任意の最大ヒープへの挿入が最大ヒープ順序を保つ。 -/
theorem insertHeap_maxPrefer_preserves_of_size_seven (heap : Array Nat)
    (hSize : heap.size = 7) (value : Nat) (hHeap : HeapOrdered maxPrefer heap) :
    HeapOrdered maxPrefer (LeanExperiments.RunningMedian.insertHeap maxPrefer heap value) := by
  let root := heap[0]!
  let left := heap[1]!
  let right := heap[2]!
  let leftLeaf := heap[3]!
  let rightLeaf := heap[4]!
  let rightLeft := heap[5]!
  let rightRight := heap[6]!
  have hHeapEq : heap = #[root, left, right, leftLeaf, rightLeaf, rightLeft, rightRight] := by
    apply Array.ext
    · simpa using hSize
    · intro index hIndex hBound
      have hCases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨
          index = 4 ∨ index = 5 ∨ index = 6 := by omega
      rcases hCases with h | h | h | h | h | h | h <;> subst index
      · simpa [root] using (getElem!_pos heap 0 (by omega)).symm
      · simpa [left] using (getElem!_pos heap 1 (by omega)).symm
      · simpa [right] using (getElem!_pos heap 2 (by omega)).symm
      · simpa [leftLeaf] using (getElem!_pos heap 3 (by omega)).symm
      · simpa [rightLeaf] using (getElem!_pos heap 4 (by omega)).symm
      · simpa [rightLeft] using (getElem!_pos heap 5 (by omega)).symm
      · simpa [rightRight] using (getElem!_pos heap 6 (by omega)).symm
  have hTupleHeap : HeapOrdered maxPrefer
      #[root, left, right, leftLeaf, rightLeaf, rightLeft, rightRight] := by
    simpa [hHeapEq] using hHeap
  rw [hHeapEq]
  exact insertHeap_maxPrefer_sevenElements_preserves hTupleHeap

/-- サイズ8の任意の最小ヒープ配列への挿入が最小ヒープ順序を保つ。 -/
theorem insertHeap_minPrefer_preserves_of_size_eight (heap : Array Nat)
    (hSize : heap.size = 8) (value : Nat) (hHeap : MinHeap heap) :
    MinHeap (LeanExperiments.RunningMedian.insertHeap minPrefer heap value) := by
  let root := heap[0]!
  let left := heap[1]!
  let right := heap[2]!
  let leftLeft := heap[3]!
  let leftRight := heap[4]!
  let rightLeft := heap[5]!
  let rightRight := heap[6]!
  let leftLeftLeaf := heap[7]!
  have hHeapEq : heap = #[root, left, right, leftLeft, leftRight, rightLeft,
      rightRight, leftLeftLeaf] := by
    apply Array.ext
    · simpa using hSize
    · intro index hIndex hBound
      have hCases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 ∨
          index = 5 ∨ index = 6 ∨ index = 7 := by omega
      rcases hCases with h | h | h | h | h | h | h | h <;> subst index
      · simpa [root] using (getElem!_pos heap 0 (by omega)).symm
      · simpa [left] using (getElem!_pos heap 1 (by omega)).symm
      · simpa [right] using (getElem!_pos heap 2 (by omega)).symm
      · simpa [leftLeft] using (getElem!_pos heap 3 (by omega)).symm
      · simpa [leftRight] using (getElem!_pos heap 4 (by omega)).symm
      · simpa [rightLeft] using (getElem!_pos heap 5 (by omega)).symm
      · simpa [rightRight] using (getElem!_pos heap 6 (by omega)).symm
      · simpa [leftLeftLeaf] using (getElem!_pos heap 7 (by omega)).symm
  have hTupleHeap : MinHeap
      #[root, left, right, leftLeft, leftRight, rightLeft, rightRight, leftLeftLeaf] := by
    simpa [hHeapEq] using hHeap
  rw [hHeapEq]
  exact insertHeap_minPrefer_eightElements_preserves hTupleHeap

/-- サイズ8の任意の最大ヒープ配列への挿入が最大ヒープ順序を保つ。 -/
theorem insertHeap_maxPrefer_preserves_of_size_eight (heap : Array Nat)
    (hSize : heap.size = 8) (value : Nat) (hHeap : HeapOrdered maxPrefer heap) :
    HeapOrdered maxPrefer (LeanExperiments.RunningMedian.insertHeap maxPrefer heap value) := by
  let root := heap[0]!
  let left := heap[1]!
  let right := heap[2]!
  let leftLeft := heap[3]!
  let leftRight := heap[4]!
  let rightLeft := heap[5]!
  let rightRight := heap[6]!
  let leftLeftLeaf := heap[7]!
  have hHeapEq : heap = #[root, left, right, leftLeft, leftRight, rightLeft,
      rightRight, leftLeftLeaf] := by
    apply Array.ext
    · simpa using hSize
    · intro index hIndex hBound
      have hCases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 ∨
          index = 5 ∨ index = 6 ∨ index = 7 := by omega
      rcases hCases with h | h | h | h | h | h | h | h <;> subst index
      · simpa [root] using (getElem!_pos heap 0 (by omega)).symm
      · simpa [left] using (getElem!_pos heap 1 (by omega)).symm
      · simpa [right] using (getElem!_pos heap 2 (by omega)).symm
      · simpa [leftLeft] using (getElem!_pos heap 3 (by omega)).symm
      · simpa [leftRight] using (getElem!_pos heap 4 (by omega)).symm
      · simpa [rightLeft] using (getElem!_pos heap 5 (by omega)).symm
      · simpa [rightRight] using (getElem!_pos heap 6 (by omega)).symm
      · simpa [leftLeftLeaf] using (getElem!_pos heap 7 (by omega)).symm
  have hTupleHeap : HeapOrdered maxPrefer
      #[root, left, right, leftLeft, leftRight, rightLeft, rightRight, leftLeftLeaf] := by
    simpa [hHeapEq] using hHeap
  rw [hHeapEq]
  exact insertHeap_maxPrefer_eightElements_preserves hTupleHeap

/-- 任意7要素最大ヒープへ根以下の値を挿入しても、最大ヒープ順序を保つ。 -/
theorem insertHeap_maxPrefer_preserves_of_size_seven_of_le_root (heap : Array Nat)
    (hSize : heap.size = 7) (value : Nat) (hValue : value ≤ heap[0]!)
    (hHeap : HeapOrdered maxPrefer heap) :
    HeapOrdered maxPrefer (LeanExperiments.RunningMedian.insertHeap maxPrefer heap value) := by
  let root := heap[0]!
  let left := heap[1]!
  let right := heap[2]!
  let leftLeaf := heap[3]!
  let rightLeaf := heap[4]!
  let rightLeft := heap[5]!
  let rightRight := heap[6]!
  have hHeapEq : heap = #[root, left, right, leftLeaf, rightLeaf, rightLeft, rightRight] := by
    apply Array.ext
    · simpa using hSize
    · intro index hIndex hBound
      have hCases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨
          index = 4 ∨ index = 5 ∨ index = 6 := by omega
      rcases hCases with h | h | h | h | h | h | h <;> subst index
      · simpa [root] using (getElem!_pos heap 0 (by omega)).symm
      · simpa [left] using (getElem!_pos heap 1 (by omega)).symm
      · simpa [right] using (getElem!_pos heap 2 (by omega)).symm
      · simpa [leftLeaf] using (getElem!_pos heap 3 (by omega)).symm
      · simpa [rightLeaf] using (getElem!_pos heap 4 (by omega)).symm
      · simpa [rightLeft] using (getElem!_pos heap 5 (by omega)).symm
      · simpa [rightRight] using (getElem!_pos heap 6 (by omega)).symm
  have hTupleHeap : HeapOrdered maxPrefer
      #[root, left, right, leftLeaf, rightLeaf, rightLeft, rightRight] := by
    simpa [hHeapEq] using hHeap
  have hValueTuple : value ≤ root := by simpa [root] using hValue
  rw [hHeapEq]
  exact insertHeap_maxPrefer_sevenElements_of_le_root hTupleHeap hValueTuple

/-- サイズ5の任意の最大ヒープへ値を挿入しても、最大ヒープ順序を保つ。 -/
theorem insertHeap_maxPrefer_preserves_of_size_five (heap : Array Nat)
    (hSize : heap.size = 5) (value : Nat)
    (hHeap : HeapOrdered maxPrefer heap) :
    HeapOrdered maxPrefer (LeanExperiments.RunningMedian.insertHeap maxPrefer heap value) := by
  let root := heap[0]!
  let left := heap[1]!
  let right := heap[2]!
  let leftLeaf := heap[3]!
  let rightLeaf := heap[4]!
  have hHeapEq : heap = #[root, left, right, leftLeaf, rightLeaf] := by
    apply Array.ext
    · simpa using hSize
    · intro index hIndex hBound
      have hCases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 := by
        omega
      rcases hCases with h | h | h | h | h <;> subst index
      · simpa [root] using (getElem!_pos heap 0 (by omega)).symm
      · simpa [left] using (getElem!_pos heap 1 (by omega)).symm
      · simpa [right] using (getElem!_pos heap 2 (by omega)).symm
      · simpa [leftLeaf] using (getElem!_pos heap 3 (by omega)).symm
      · simpa [rightLeaf] using (getElem!_pos heap 4 (by omega)).symm
  have hTupleHeap : HeapOrdered maxPrefer #[root, left, right, leftLeaf, rightLeaf] := by
    simpa [hHeapEq] using hHeap
  rw [hHeapEq]
  exact insertHeap_maxPrefer_fiveElements_preserves hTupleHeap

/-- サイズ5の任意の最小ヒープへ値を挿入しても、最小ヒープ順序を保つ。 -/
theorem insertHeap_minPrefer_preserves_of_size_five (heap : Array Nat)
    (hSize : heap.size = 5) (value : Nat) (hHeap : MinHeap heap) :
    MinHeap (LeanExperiments.RunningMedian.insertHeap minPrefer heap value) := by
  let root := heap[0]!
  let left := heap[1]!
  let right := heap[2]!
  let leftLeaf := heap[3]!
  let rightLeaf := heap[4]!
  have hHeapEq : heap = #[root, left, right, leftLeaf, rightLeaf] := by
    apply Array.ext
    · simpa using hSize
    · intro index hIndex hBound
      have hCases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 := by
        omega
      rcases hCases with h | h | h | h | h <;> subst index
      · simpa [root] using (getElem!_pos heap 0 (by omega)).symm
      · simpa [left] using (getElem!_pos heap 1 (by omega)).symm
      · simpa [right] using (getElem!_pos heap 2 (by omega)).symm
      · simpa [leftLeaf] using (getElem!_pos heap 3 (by omega)).symm
      · simpa [rightLeaf] using (getElem!_pos heap 4 (by omega)).symm
  have hTupleHeap : MinHeap #[root, left, right, leftLeaf, rightLeaf] := by
    simpa [hHeapEq] using hHeap
  rw [hHeapEq]
  exact insertHeap_minPrefer_fiveElements_preserves hTupleHeap

/-- サイズ4の任意の最大ヒープへ値を挿入しても、最大ヒープ順序を保つ。 -/
theorem insertHeap_maxPrefer_preserves_of_size_four (heap : Array Nat)
    (hSize : heap.size = 4) (value : Nat)
    (hHeap : HeapOrdered maxPrefer heap) :
    HeapOrdered maxPrefer (LeanExperiments.RunningMedian.insertHeap maxPrefer heap value) := by
  let root := heap[0]!
  let left := heap[1]!
  let right := heap[2]!
  let leaf := heap[3]!
  have hHeapEq : heap = #[root, left, right, leaf] := by
    apply Array.ext
    · simpa using hSize
    · intro index hIndex hBound
      have hCases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 := by omega
      rcases hCases with h | h | h | h <;> subst index
      · simpa [root] using (getElem!_pos heap 0 (by omega)).symm
      · simpa [left] using (getElem!_pos heap 1 (by omega)).symm
      · simpa [right] using (getElem!_pos heap 2 (by omega)).symm
      · simpa [leaf] using (getElem!_pos heap 3 (by omega)).symm
  have hTupleHeap : HeapOrdered maxPrefer #[root, left, right, leaf] := by
    simpa [hHeapEq] using hHeap
  rw [hHeapEq]
  exact insertHeap_maxPrefer_fourElements_preserves hTupleHeap

/-- サイズ4の任意の最小ヒープへ値を挿入しても、最小ヒープ順序を保つ。 -/
theorem insertHeap_minPrefer_preserves_of_size_four (heap : Array Nat)
    (hSize : heap.size = 4) (value : Nat) (hHeap : MinHeap heap) :
    MinHeap (LeanExperiments.RunningMedian.insertHeap minPrefer heap value) := by
  let root := heap[0]!
  let left := heap[1]!
  let right := heap[2]!
  let leaf := heap[3]!
  have hHeapEq : heap = #[root, left, right, leaf] := by
    apply Array.ext
    · simpa using hSize
    · intro index hIndex hBound
      have hCases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 := by omega
      rcases hCases with h | h | h | h <;> subst index
      · simpa [root] using (getElem!_pos heap 0 (by omega)).symm
      · simpa [left] using (getElem!_pos heap 1 (by omega)).symm
      · simpa [right] using (getElem!_pos heap 2 (by omega)).symm
      · simpa [leaf] using (getElem!_pos heap 3 (by omega)).symm
  have hTupleHeap : MinHeap #[root, left, right, leaf] := by
    simpa [hHeapEq] using hHeap
  rw [hHeapEq]
  exact insertHeap_minPrefer_fourElements_preserves hTupleHeap

/-- 最大ヒープの2要素で子が親より大きければ、親方向調整が両者を交換する。 -/
theorem siftUp_maxPrefer_pair_of_lt {left right : Nat} (hLeft : left < right) :
    LeanExperiments.RunningMedian.siftUp LeanExperiments.RunningMedian.maxPrefer
      #[left, right] 1 = #[right, left] := by
  apply siftUp_pair_of_prefer_true
  simp [LeanExperiments.RunningMedian.maxPrefer, hLeft]

/-- 最小ヒープの2要素で子が親より小さければ、親方向調整が両者を交換する。 -/
theorem siftUp_minPrefer_pair_of_gt {left right : Nat} (hRight : right < left) :
    LeanExperiments.RunningMedian.siftUp LeanExperiments.RunningMedian.minPrefer
      #[left, right] 1 = #[right, left] := by
  apply siftUp_pair_of_prefer_true
  simp [LeanExperiments.RunningMedian.minPrefer, hRight]

/-- 1要素の最大ヒープへより大きな値を挿入すると、新しい値が根になる。 -/
theorem insertHeap_maxPrefer_singleton_of_lt {left right : Nat}
    (hLeft : left < right) :
    LeanExperiments.RunningMedian.insertHeap LeanExperiments.RunningMedian.maxPrefer
      #[left] right = #[right, left] := by
  unfold LeanExperiments.RunningMedian.insertHeap
  change LeanExperiments.RunningMedian.siftUp LeanExperiments.RunningMedian.maxPrefer
    #[left, right] 1 = #[right, left]
  exact siftUp_maxPrefer_pair_of_lt hLeft

/-- 1要素の最小ヒープへより小さな値を挿入すると、新しい値が根になる。 -/
theorem insertHeap_minPrefer_singleton_of_gt {left right : Nat}
    (hRight : right < left) :
    LeanExperiments.RunningMedian.insertHeap LeanExperiments.RunningMedian.minPrefer
      #[left] right = #[right, left] := by
  unfold LeanExperiments.RunningMedian.insertHeap
  change LeanExperiments.RunningMedian.siftUp LeanExperiments.RunningMedian.minPrefer
    #[left, right] 1 = #[right, left]
  exact siftUp_minPrefer_pair_of_gt hRight

/-- 最小優先度の候補選択は、現在位置と存在する子のうち最小値を持つ添字を返す。 -/
theorem siftDownBest_minPrefer_selects_minimum (heap : Array Nat) (index : Nat)
    (hIndex : index < heap.size) :
    let best := LeanExperiments.RunningMedian.siftDownBest minPrefer heap index
    best < heap.size ∧ heap[best]! ≤ heap[index]! ∧
      (2 * index + 1 < heap.size → heap[best]! ≤ heap[2 * index + 1]!) ∧
      (2 * index + 2 < heap.size → heap[best]! ≤ heap[2 * index + 2]!) := by
  dsimp
  let left := 2 * index + 1
  let right := 2 * index + 2
  let takeLeft := left < heap.size && minPrefer heap[left]! heap[index]!
  let bestLeft := if takeLeft then left else index
  let takeRight := right < heap.size && minPrefer heap[right]! heap[bestLeft]!
  let best := if takeRight then right else bestLeft
  change best < heap.size ∧ heap[best]! ≤ heap[index]! ∧
    (left < heap.size → heap[best]! ≤ heap[left]!) ∧
    (right < heap.size → heap[best]! ≤ heap[right]!)
  by_cases hTakeLeft : takeLeft = true
  · have hLeftSpec : left < heap.size ∧ heap[left]! < heap[index]! := by
      simpa [takeLeft, minPrefer] using hTakeLeft
    by_cases hTakeRight : takeRight = true
    · have hRightSpec : right < heap.size ∧ heap[right]! < heap[left]! := by
        simpa [takeRight, bestLeft, hTakeLeft, minPrefer] using hTakeRight
      simp [best, bestLeft, hTakeRight]
      omega
    · have hRightNot : ¬ (right < heap.size ∧ heap[right]! < heap[left]!) := by
        intro h
        have hCompare : minPrefer heap[right]! heap[left]! = true := by
          simp [minPrefer, h.2]
        have hInBounds : decide (right < heap.size) = true := by simp [h.1]
        have hChosen : takeRight = true := by
          simp [takeRight, bestLeft, hTakeLeft, hInBounds, hCompare]
        exact hTakeRight hChosen
      simp [best, bestLeft, hTakeLeft, hTakeRight]
      omega
  · have hLeftNot : ¬ (left < heap.size ∧ heap[left]! < heap[index]!) := by
      intro h
      have hCompare : minPrefer heap[left]! heap[index]! = true := by
        simp [minPrefer, h.2]
      have hInBounds : decide (left < heap.size) = true := by simp [h.1]
      have hChosen : takeLeft = true := by
        simp [takeLeft, hInBounds, hCompare]
      exact hTakeLeft hChosen
    by_cases hTakeRight : takeRight = true
    · have hRightSpec : right < heap.size ∧ heap[right]! < heap[index]! := by
        simpa [takeRight, bestLeft, hTakeLeft, minPrefer] using hTakeRight
      simp [best, bestLeft, hTakeRight]
      omega
    · have hRightNot : ¬ (right < heap.size ∧ heap[right]! < heap[index]!) := by
        intro h
        have hCompare : minPrefer heap[right]! heap[index]! = true := by
          simp [minPrefer, h.2]
        have hInBounds : decide (right < heap.size) = true := by simp [h.1]
        have hChosen : takeRight = true := by
          simp [takeRight, bestLeft, hTakeLeft, hInBounds, hCompare]
        exact hTakeRight hChosen
      simp [best, bestLeft, hTakeLeft, hTakeRight]
      omega

/-- 最小優先度の下降1ステップ後、処理した位置の親子辺は最小ヒープ順序になる。 -/
theorem siftDownStep_minPrefer_orders_current_position (heap : Array Nat) (index : Nat)
    (hIndex : index < heap.size) :
    let nextHeap :=
      (LeanExperiments.RunningMedian.siftDownStep minPrefer heap index).1
    (2 * index + 1 < heap.size → nextHeap[index]! ≤ nextHeap[2 * index + 1]!) ∧
      (2 * index + 2 < heap.size → nextHeap[index]! ≤ nextHeap[2 * index + 2]!) := by
  let best := LeanExperiments.RunningMedian.siftDownBest minPrefer heap index
  have hSelection := siftDownBest_minPrefer_selects_minimum heap index hIndex
  dsimp [best] at hSelection
  rcases hSelection with ⟨hBestBound, hBestParent, hBestLeft, hBestRight⟩
  by_cases hBestEq : best = index
  · have hStopped :
        (LeanExperiments.RunningMedian.siftDownStep minPrefer heap index).2.2 = false := by
      simp [LeanExperiments.RunningMedian.siftDownStep, best, hBestEq]
    have hIdentity := siftDownStep_stopped minPrefer heap index hStopped
    simpa [best, hBestEq, hIdentity.1] using And.intro hBestLeft hBestRight
  · have hRunning :
        (LeanExperiments.RunningMedian.siftDownStep minPrefer heap index).2.2 = true := by
      simp [LeanExperiments.RunningMedian.siftDownStep, best, hBestEq]
    have hStep := siftDownStep_running minPrefer heap index hRunning
    have hIndexBound : index < heap.size := hIndex
    have hBestBoundLocal : best < heap.size := by simpa [best] using hBestBound
    have hSwap : LeanExperiments.RunningMedian.swap heap index best =
        heap.swap index best := by
      simp [LeanExperiments.RunningMedian.swap, Array.swap, Array.setIfInBounds,
        hIndexBound, hBestBoundLocal]
    have hNextHeap :
        (LeanExperiments.RunningMedian.siftDownStep minPrefer heap index).1 =
          heap.swap index best := by
      rw [hStep.1]
      simpa [best] using hSwap
    change
      (2 * index + 1 < heap.size →
          (LeanExperiments.RunningMedian.siftDownStep minPrefer heap index).1[index]! ≤
            (LeanExperiments.RunningMedian.siftDownStep minPrefer heap index).1[2 * index + 1]!) ∧
        (2 * index + 2 < heap.size →
          (LeanExperiments.RunningMedian.siftDownStep minPrefer heap index).1[index]! ≤
            (LeanExperiments.RunningMedian.siftDownStep minPrefer heap index).1[2 * index + 2]!)
    rw [hNextHeap]
    constructor
    · intro hLeft
      have hLeftNeIndex : 2 * index + 1 ≠ index := by omega
      have hSwapSize : (heap.swap index best).size = heap.size := by simp
      have hRootValue : (heap.swap index best)[index]! = heap[best]! := by
        rw [getElem!_pos _ _ (by simpa [hSwapSize] using hIndex)]
        simp [Array.getElem_swap_left]
        rw [getElem!_pos heap best hBestBoundLocal]
      have hChildValue :
          (heap.swap index best)[2 * index + 1]! =
            if 2 * index + 1 = best then heap[index]! else heap[2 * index + 1]! := by
        rw [getElem!_pos _ _ (by simpa [hSwapSize] using hLeft)]
        simp [Array.getElem_swap, hLeft, hIndexBound, hLeftNeIndex]
      rw [hRootValue, hChildValue]
      by_cases hChosen : 2 * index + 1 = best
      · simpa [best, hChosen] using hBestParent
      · simpa [best, hChosen] using hBestLeft hLeft
    · intro hRight
      have hRightNeIndex : 2 * index + 2 ≠ index := by omega
      have hSwapSize : (heap.swap index best).size = heap.size := by simp
      have hRootValue : (heap.swap index best)[index]! = heap[best]! := by
        rw [getElem!_pos _ _ (by simpa [hSwapSize] using hIndex)]
        simp [Array.getElem_swap_left]
        rw [getElem!_pos heap best hBestBoundLocal]
      have hChildValue :
          (heap.swap index best)[2 * index + 2]! =
            if 2 * index + 2 = best then heap[index]! else heap[2 * index + 2]! := by
        rw [getElem!_pos _ _ (by simpa [hSwapSize] using hRight)]
        simp [Array.getElem_swap, hRight, hIndexBound, hRightNeIndex]
      rw [hRootValue, hChildValue]
      by_cases hChosen : 2 * index + 2 = best
      · simpa [best, hChosen] using hBestParent
      · simpa [best, hChosen] using hBestRight hRight

/-- 下降を続ける最小優先度の反復では、交換後の経路辺も最小ヒープ順序になる。 -/
theorem siftDownStep_minPrefer_running_orders_transition (heap : Array Nat) (index : Nat)
    (hRunning :
      (LeanExperiments.RunningMedian.siftDownStep minPrefer heap index).2.2 = true) :
    let nextHeap :=
      (LeanExperiments.RunningMedian.siftDownStep minPrefer heap index).1
    let nextIndex :=
      (LeanExperiments.RunningMedian.siftDownStep minPrefer heap index).2.1
    nextHeap[index]! ≤ nextHeap[nextIndex]! := by
  let nextHeap :=
    (LeanExperiments.RunningMedian.siftDownStep minPrefer heap index).1
  let nextIndex :=
    (LeanExperiments.RunningMedian.siftDownStep minPrefer heap index).2.1
  have hProgress := siftDownStep_progress minPrefer heap index hRunning
  have hIndex : index < heap.size := by omega
  have hEdges := siftDownStep_minPrefer_orders_current_position heap index hIndex
  have hBestNe :
      LeanExperiments.RunningMedian.siftDownBest minPrefer heap index ≠ index := by
    intro hEq
    have hNextEq : nextIndex = index := by
      have hStep := siftDownStep_running minPrefer heap index hRunning
      simpa [nextIndex] using hStep.2.trans hEq
    omega
  have hBestCases := siftDownBest_eq_index_or_child minPrefer heap index
  have hChild : nextIndex = 2 * index + 1 ∨ nextIndex = 2 * index + 2 := by
    have hStep := siftDownStep_running minPrefer heap index hRunning
    rcases hBestCases with hIndexCase | hLeftCase | hRightCase
    · exact (hBestNe hIndexCase).elim
    · exact Or.inl (hStep.2.trans hLeftCase)
    · exact Or.inr (hStep.2.trans hRightCase)
  rcases hChild with h | h
  · have hLeftEdge := hEdges.1 (by omega)
    simpa [nextHeap, nextIndex, h] using hLeftEdge
  · have hRightEdge := hEdges.2 (by omega)
    simpa [nextHeap, nextIndex, h] using hRightEdge

/-- 継続時、処理済み位置から現在位置への順序は、候補全てへの上界で保たれる。 -/
theorem siftDownStep_minPrefer_preserves_incoming_edge
    (heap : Array Nat) (index parent : Nat) (hIndex : index < heap.size)
    (hParent : parent < index)
    (hParentLeft : 2 * index + 1 < heap.size →
      heap[parent]! ≤ heap[2 * index + 1]!)
    (hParentRight : 2 * index + 2 < heap.size →
      heap[parent]! ≤ heap[2 * index + 2]!)
    (hRunning :
      (LeanExperiments.RunningMedian.siftDownStep minPrefer heap index).2.2 = true) :
    let nextHeap :=
      (LeanExperiments.RunningMedian.siftDownStep minPrefer heap index).1
    nextHeap[parent]! ≤ nextHeap[index]! := by
  let nextHeap :=
    (LeanExperiments.RunningMedian.siftDownStep minPrefer heap index).1
  let best := LeanExperiments.RunningMedian.siftDownBest minPrefer heap index
  have hStep := siftDownStep_running minPrefer heap index hRunning
  have hProgress := siftDownStep_progress minPrefer heap index hRunning
  have hBestBound : best < heap.size := by
    change LeanExperiments.RunningMedian.siftDownBest minPrefer heap index < heap.size
    rw [← hStep.2]
    exact hProgress.2
  have hBestNe : best ≠ index := by
    change best ≠ index
    intro hEq
    have hNextIndexEq :
        (LeanExperiments.RunningMedian.siftDownStep minPrefer heap index).2.1 = index := by
      rw [hStep.2]
      simpa [best] using hEq
    omega
  have hBestCases := siftDownBest_eq_index_or_child minPrefer heap index
  have hParentBest : heap[parent]! ≤ heap[best]! := by
    rcases hBestCases with hCurrent | hLeft | hRight
    · change best = index at hCurrent
      exact (hBestNe hCurrent).elim
    · have hLeftBound : 2 * index + 1 < heap.size := by omega
      change best = 2 * index + 1 at hLeft
      rw [hLeft]
      exact hParentLeft hLeftBound
    · have hRightBound : 2 * index + 2 < heap.size := by omega
      change best = 2 * index + 2 at hRight
      rw [hRight]
      exact hParentRight hRightBound
  have hIndexBound : index < heap.size := hIndex
  have hSwap : LeanExperiments.RunningMedian.swap heap index best =
      heap.swap index best := by
    simp [LeanExperiments.RunningMedian.swap, Array.swap, Array.setIfInBounds,
      hIndexBound, hBestBound]
  have hNextHeap :
      (LeanExperiments.RunningMedian.siftDownStep minPrefer heap index).1 =
        heap.swap index best := by
    rw [hStep.1]
    simpa [best] using hSwap
  have hSwapSize : (heap.swap index best).size = heap.size := by simp
  have hParentValue : nextHeap[parent]! = heap[parent]! := by
    dsimp [nextHeap]
    exact siftDownStep_getElem!_eq_of_lt_index minPrefer heap index parent hParent
  have hIndexValue : nextHeap[index]! = heap[best]! := by
    change (LeanExperiments.RunningMedian.siftDownStep minPrefer heap index).1[index]! =
      heap[best]!
    rw [hNextHeap]
    rw [getElem!_pos _ _ (by simpa [hSwapSize] using hIndex)]
    simp [Array.getElem_swap_left]
    rw [getElem!_pos heap best hBestBound]
  change nextHeap[parent]! ≤ nextHeap[index]!
  rw [hParentValue, hIndexValue]
  exact hParentBest

/-- 根置換後の初回下降では、交換先の値がその部分木の子候補以下になる。 -/
theorem siftDownStep_minPrefer_root_initializes_path
    (heap : Array Nat)
    (hBelowRoot : ∀ parent, 0 < parent → parent < heap.size →
      (2 * parent + 1 < heap.size → heap[parent]! ≤ heap[2 * parent + 1]!) ∧
      (2 * parent + 2 < heap.size → heap[parent]! ≤ heap[2 * parent + 2]!))
    (hRunning :
      (LeanExperiments.RunningMedian.siftDownStep minPrefer heap 0).2.2 = true) :
    let best := LeanExperiments.RunningMedian.siftDownBest minPrefer heap 0
    let nextHeap := (LeanExperiments.RunningMedian.siftDownStep minPrefer heap 0).1
    MinHeapExcept nextHeap best ∧
      nextHeap[0]! ≤ nextHeap[best]! ∧
      (2 * best + 1 < nextHeap.size → nextHeap[0]! ≤ nextHeap[2 * best + 1]!) ∧
      (2 * best + 2 < nextHeap.size → nextHeap[0]! ≤ nextHeap[2 * best + 2]!) := by
  let best := LeanExperiments.RunningMedian.siftDownBest minPrefer heap 0
  let nextHeap := (LeanExperiments.RunningMedian.siftDownStep minPrefer heap 0).1
  have hStep := siftDownStep_running minPrefer heap 0 hRunning
  have hProgress := siftDownStep_progress minPrefer heap 0 hRunning
  have hBestBound : best < heap.size := by
    change LeanExperiments.RunningMedian.siftDownBest minPrefer heap 0 < heap.size
    rw [← hStep.2]
    exact hProgress.2
  have hBestPositive : 0 < best := by
    change 0 < LeanExperiments.RunningMedian.siftDownBest minPrefer heap 0
    rw [← hStep.2]
    exact hProgress.1
  have hBestShapeCases := siftDownBest_eq_index_or_child minPrefer heap 0
  have hBestShape : best = 1 ∨ best = 2 := by
    rcases hBestShapeCases with hRoot | hLeft | hRight
    · change best = 0 at hRoot
      omega
    · change best = 1 at hLeft
      exact Or.inl hLeft
    · change best = 2 at hRight
      exact Or.inr hRight
  have hIndexBound : 0 < heap.size := by omega
  have hSwap : LeanExperiments.RunningMedian.swap heap 0 best = heap.swap 0 best := by
    simp [LeanExperiments.RunningMedian.swap, Array.swap, Array.setIfInBounds,
      hIndexBound, hBestBound]
  have hNextHeap :
      (LeanExperiments.RunningMedian.siftDownStep minPrefer heap 0).1 =
        heap.swap 0 best := by
    rw [hStep.1]
    simpa [best] using hSwap
  have hNextSize : nextHeap.size = heap.size := by
    dsimp [nextHeap]
    exact siftDownStep_size minPrefer heap 0
  have hRootValue : nextHeap[0]! = heap[best]! := by
    change (LeanExperiments.RunningMedian.siftDownStep minPrefer heap 0).1[0]! =
      heap[best]!
    rw [hNextHeap]
    rw [getElem!_pos _ _ (by simpa [Array.size_swap] using hIndexBound)]
    simp [Array.getElem_swap_left]
    rw [getElem!_pos heap best hBestBound]
  have hRootEdges := siftDownStep_minPrefer_orders_current_position heap 0 hIndexBound
  have hRootToBest : nextHeap[0]! ≤ nextHeap[best]! := by
    rcases hBestShape with hLeft | hRight
    · have hEdge := hRootEdges.1 (by omega : 1 < heap.size)
      simpa [nextHeap, hLeft] using hEdge
    · have hEdge := hRootEdges.2 (by omega : 2 < heap.size)
      simpa [nextHeap, hRight] using hEdge
  have hBestEdges := hBelowRoot best hBestPositive hBestBound
  have hOutputExcept : MinHeapExcept nextHeap best := by
    intro parent hParent hParentNeBest
    by_cases hParentZero : parent = 0
    · subst parent
      simpa [nextHeap, hNextSize] using hRootEdges
    · have hParentPositive : 0 < parent := by omega
      have hParentInput : parent < heap.size := by simpa [hNextSize] using hParent
      have hParentValue : nextHeap[parent]! = heap[parent]! := by
        dsimp [nextHeap]
        exact siftDownStep_getElem!_eq_of_outside_swap minPrefer heap 0 parent hParentInput
          (by omega) hParentNeBest
      constructor
      · intro hLeft
        have hLeftInput : 2 * parent + 1 < heap.size := by simpa [hNextSize] using hLeft
        have hLeftNeRoot : 2 * parent + 1 ≠ 0 := by omega
        have hLeftNeBest : 2 * parent + 1 ≠ best := by
          intro hEq
          rcases hBestShape with hBestLeft | hBestRight <;> omega
        have hLeftValue : nextHeap[2 * parent + 1]! = heap[2 * parent + 1]! := by
          dsimp [nextHeap]
          exact siftDownStep_getElem!_eq_of_outside_swap minPrefer heap 0
            (2 * parent + 1) hLeftInput hLeftNeRoot hLeftNeBest
        rw [hParentValue, hLeftValue]
        exact (hBelowRoot parent hParentPositive hParentInput).1 hLeftInput
      · intro hRight
        have hRightInput : 2 * parent + 2 < heap.size := by simpa [hNextSize] using hRight
        have hRightNeRoot : 2 * parent + 2 ≠ 0 := by omega
        have hRightNeBest : 2 * parent + 2 ≠ best := by
          intro hEq
          rcases hBestShape with hBestLeft | hBestRight <;> omega
        have hRightValue : nextHeap[2 * parent + 2]! = heap[2 * parent + 2]! := by
          dsimp [nextHeap]
          exact siftDownStep_getElem!_eq_of_outside_swap minPrefer heap 0
            (2 * parent + 2) hRightInput hRightNeRoot hRightNeBest
        rw [hParentValue, hRightValue]
        exact (hBelowRoot parent hParentPositive hParentInput).2 hRightInput
  constructor
  · exact hOutputExcept
  constructor
  · exact hRootToBest
  constructor
  · intro hLeft
    change 2 * best + 1 < nextHeap.size at hLeft
    have hLeftInput : 2 * best + 1 < heap.size := by simpa [hNextSize] using hLeft
    have hChildNotRoot : 2 * best + 1 ≠ 0 := by omega
    have hChildNotBest : 2 * best + 1 ≠ best := by omega
    have hChildValue : nextHeap[2 * best + 1]! = heap[2 * best + 1]! := by
      dsimp [nextHeap]
      exact siftDownStep_getElem!_eq_of_outside_swap minPrefer heap 0
        (2 * best + 1) hLeftInput hChildNotRoot hChildNotBest
    change nextHeap[0]! ≤ nextHeap[2 * best + 1]!
    rw [hRootValue, hChildValue]
    exact hBestEdges.1 hLeftInput
  · intro hRight
    change 2 * best + 2 < nextHeap.size at hRight
    have hRightInput : 2 * best + 2 < heap.size := by simpa [hNextSize] using hRight
    have hChildNotRoot : 2 * best + 2 ≠ 0 := by omega
    have hChildNotBest : 2 * best + 2 ≠ best := by omega
    have hChildValue : nextHeap[2 * best + 2]! = heap[2 * best + 2]! := by
      dsimp [nextHeap]
      exact siftDownStep_getElem!_eq_of_outside_swap minPrefer heap 0
        (2 * best + 2) hRightInput hChildNotRoot hChildNotBest
    change nextHeap[0]! ≤ nextHeap[2 * best + 2]!
    rw [hRootValue, hChildValue]
    exact hBestEdges.2 hRightInput

/-- 継続する交換では、順序違反の行が現在位置から選択した子へ移る。 -/
theorem siftDownStep_minPrefer_moves_minHeap_exception
    (heap : Array Nat) (index parent : Nat)
    (hIndex : index < heap.size)
    (hParentShape : index = 2 * parent + 1 ∨ index = 2 * parent + 2)
    (hExcept : MinHeapExcept heap index)
    (hIncomingLeft : 2 * index + 1 < heap.size →
      heap[parent]! ≤ heap[2 * index + 1]!)
    (hIncomingRight : 2 * index + 2 < heap.size →
      heap[parent]! ≤ heap[2 * index + 2]!)
    (hRunning :
      (LeanExperiments.RunningMedian.siftDownStep minPrefer heap index).2.2 = true) :
    let best := LeanExperiments.RunningMedian.siftDownBest minPrefer heap index
    let nextHeap := (LeanExperiments.RunningMedian.siftDownStep minPrefer heap index).1
    MinHeapExcept nextHeap best ∧
      nextHeap[index]! ≤ nextHeap[best]! ∧
      (2 * best + 1 < nextHeap.size → nextHeap[index]! ≤ nextHeap[2 * best + 1]!) ∧
      (2 * best + 2 < nextHeap.size → nextHeap[index]! ≤ nextHeap[2 * best + 2]!) := by
  let best := LeanExperiments.RunningMedian.siftDownBest minPrefer heap index
  let nextHeap := (LeanExperiments.RunningMedian.siftDownStep minPrefer heap index).1
  have hStep := siftDownStep_running minPrefer heap index hRunning
  have hProgress := siftDownStep_progress minPrefer heap index hRunning
  have hBestBound : best < heap.size := by
    change LeanExperiments.RunningMedian.siftDownBest minPrefer heap index < heap.size
    rw [← hStep.2]
    exact hProgress.2
  have hBestNe : best ≠ index := by
    change best ≠ index
    intro hEq
    have hNextIndexEq :
        (LeanExperiments.RunningMedian.siftDownStep minPrefer heap index).2.1 = index := by
      rw [hStep.2]
      simpa [best] using hEq
    omega
  have hBestShape : best = 2 * index + 1 ∨ best = 2 * index + 2 := by
    rcases siftDownBest_eq_index_or_child minPrefer heap index with hCurrent | hLeft | hRight
    · change best = index at hCurrent
      exact (hBestNe hCurrent).elim
    · change best = 2 * index + 1 at hLeft
      exact Or.inl hLeft
    · change best = 2 * index + 2 at hRight
      exact Or.inr hRight
  have hBestSelection := siftDownBest_minPrefer_selects_minimum heap index hIndex
  dsimp [best] at hBestSelection
  rcases hBestSelection with ⟨_, hBestCurrent, _, _⟩
  have hIndexBound : index < heap.size := hIndex
  have hSwap : LeanExperiments.RunningMedian.swap heap index best =
      heap.swap index best := by
    simp [LeanExperiments.RunningMedian.swap, Array.swap, Array.setIfInBounds,
      hIndexBound, hBestBound]
  have hNextHeap :
      (LeanExperiments.RunningMedian.siftDownStep minPrefer heap index).1 =
        heap.swap index best := by
    rw [hStep.1]
    simpa [best] using hSwap
  have hNextSize : nextHeap.size = heap.size := by
    dsimp [nextHeap]
    exact siftDownStep_size minPrefer heap index
  have hIndexValue : nextHeap[index]! = heap[best]! := by
    change (LeanExperiments.RunningMedian.siftDownStep minPrefer heap index).1[index]! =
      heap[best]!
    rw [hNextHeap]
    rw [getElem!_pos _ _ (by simpa [Array.size_swap] using hIndex)]
    simp [Array.getElem_swap_left]
    rw [getElem!_pos heap best hBestBound]
  have hBestValue : nextHeap[best]! = heap[index]! := by
    change (LeanExperiments.RunningMedian.siftDownStep minPrefer heap index).1[best]! =
      heap[index]!
    rw [hNextHeap]
    rw [getElem!_pos _ _ (by simpa [Array.size_swap] using hBestBound)]
    simp
    rw [getElem!_pos heap index hIndex]
  have hBestIncomingLeft : 2 * best + 1 < heap.size →
      heap[best]! ≤ heap[2 * best + 1]! := by
    intro hLeft
    exact (hExcept best hBestBound (by omega)).1 hLeft
  have hBestIncomingRight : 2 * best + 2 < heap.size →
      heap[best]! ≤ heap[2 * best + 2]! := by
    intro hRight
    exact (hExcept best hBestBound (by omega)).2 hRight
  have hCurrentEdges := siftDownStep_minPrefer_orders_current_position heap index hIndex
  have hOutputExcept : MinHeapExcept nextHeap best := by
    intro row hRow hRowNeBest
    by_cases hRowCurrent : row = index
    · subst row
      simpa [nextHeap, hNextSize] using hCurrentEdges
    · have hRowNeIndex : row ≠ index := hRowCurrent
      have hRowInput : row < heap.size := by simpa [hNextSize] using hRow
      have hRowValue : nextHeap[row]! = heap[row]! := by
        dsimp [nextHeap]
        exact siftDownStep_getElem!_eq_of_outside_swap minPrefer heap index row hRowInput
          hRowNeIndex hRowNeBest
      constructor
      · intro hLeft
        have hLeftInput : 2 * row + 1 < heap.size := by simpa [hNextSize] using hLeft
        by_cases hLeftIsIndex : 2 * row + 1 = index
        · have hRowParent : row = parent := by omega
          have hIndexOutput : nextHeap[index]! = heap[best]! := hIndexValue
          rw [hRowValue, hLeftIsIndex, hIndexOutput, hRowParent]
          rcases hBestShape with hBestLeft | hBestRight
          · rw [hBestLeft]
            exact hIncomingLeft (by omega)
          · rw [hBestRight]
            exact hIncomingRight (by omega)
        · by_cases hLeftIsBest : 2 * row + 1 = best
          · have hRowEqIndex : row = index := by
              rcases hBestShape with hBestLeft | hBestRight <;> omega
            exact (hRowNeIndex hRowEqIndex).elim
          · have hLeftValue : nextHeap[2 * row + 1]! = heap[2 * row + 1]! := by
              dsimp [nextHeap]
              exact siftDownStep_getElem!_eq_of_outside_swap minPrefer heap index
                (2 * row + 1) hLeftInput hLeftIsIndex hLeftIsBest
            rw [hRowValue, hLeftValue]
            exact (hExcept row (by simpa [hNextSize] using hRow) hRowNeIndex).1 hLeftInput
      · intro hRight
        have hRightInput : 2 * row + 2 < heap.size := by simpa [hNextSize] using hRight
        by_cases hRightIsIndex : 2 * row + 2 = index
        · have hRowParent : row = parent := by omega
          have hIndexOutput : nextHeap[index]! = heap[best]! := hIndexValue
          rw [hRowValue, hRightIsIndex, hIndexOutput, hRowParent]
          rcases hBestShape with hBestLeft | hBestRight
          · rw [hBestLeft]
            exact hIncomingLeft (by omega)
          · rw [hBestRight]
            exact hIncomingRight (by omega)
        · by_cases hRightIsBest : 2 * row + 2 = best
          · have hRowEqIndex : row = index := by
              rcases hBestShape with hBestLeft | hBestRight <;> omega
            exact (hRowNeIndex hRowEqIndex).elim
          · have hRightValue : nextHeap[2 * row + 2]! = heap[2 * row + 2]! := by
              dsimp [nextHeap]
              exact siftDownStep_getElem!_eq_of_outside_swap minPrefer heap index
                (2 * row + 2) hRightInput hRightIsIndex hRightIsBest
            rw [hRowValue, hRightValue]
            exact (hExcept row (by simpa [hNextSize] using hRow) hRowNeIndex).2 hRightInput
  have hNewIndexToBest : nextHeap[index]! ≤ nextHeap[best]! := by
    rw [hIndexValue, hBestValue]
    exact hBestCurrent
  have hNewIndexToLeft : 2 * best + 1 < nextHeap.size →
      nextHeap[index]! ≤ nextHeap[2 * best + 1]! := by
    intro hLeft
    have hLeftInput : 2 * best + 1 < heap.size := by simpa [hNextSize] using hLeft
    have hLeftValue : nextHeap[2 * best + 1]! = heap[2 * best + 1]! := by
      dsimp [nextHeap]
      exact siftDownStep_getElem!_eq_of_outside_swap minPrefer heap index
        (2 * best + 1) hLeftInput (by omega) (by omega)
    rw [hIndexValue, hLeftValue]
    exact hBestIncomingLeft hLeftInput
  have hNewIndexToRight : 2 * best + 2 < nextHeap.size →
      nextHeap[index]! ≤ nextHeap[2 * best + 2]! := by
    intro hRight
    have hRightInput : 2 * best + 2 < heap.size := by simpa [hNextSize] using hRight
    have hRightValue : nextHeap[2 * best + 2]! = heap[2 * best + 2]! := by
      dsimp [nextHeap]
      exact siftDownStep_getElem!_eq_of_outside_swap minPrefer heap index
        (2 * best + 2) hRightInput (by omega) (by omega)
    rw [hIndexValue, hRightValue]
    exact hBestIncomingRight hRightInput
  exact ⟨hOutputExcept, hNewIndexToBest, hNewIndexToLeft, hNewIndexToRight⟩

/-- 最小優先度で下降を続ける1反復は、経路順序・接頭部・停止測度を保つ。 -/
theorem siftDownStep_minPrefer_running_contract (heap : Array Nat) (index : Nat)
    (hRunning :
      (LeanExperiments.RunningMedian.siftDownStep minPrefer heap index).2.2 = true) :
    let nextHeap :=
      (LeanExperiments.RunningMedian.siftDownStep minPrefer heap index).1
    let nextIndex :=
      (LeanExperiments.RunningMedian.siftDownStep minPrefer heap index).2.1
    index < nextIndex ∧ nextIndex < heap.size ∧
      heap.size - nextIndex < heap.size - index ∧
      nextHeap[index]! ≤ nextHeap[nextIndex]! ∧
      (∀ position, position < index → nextHeap[position]! = heap[position]!) := by
  let nextHeap :=
    (LeanExperiments.RunningMedian.siftDownStep minPrefer heap index).1
  let nextIndex :=
    (LeanExperiments.RunningMedian.siftDownStep minPrefer heap index).2.1
  have hProgress := siftDownStep_progress minPrefer heap index hRunning
  have hMeasure := siftDownStep_measure_decreases minPrefer heap index hRunning
  have hEdge := siftDownStep_minPrefer_running_orders_transition heap index hRunning
  have hPrefix : ∀ position, position < index → nextHeap[position]! = heap[position]! := by
    intro position hPosition
    exact siftDownStep_getElem!_eq_of_lt_index minPrefer heap index position hPosition
  exact ⟨hProgress.1, hProgress.2, hMeasure, hEdge, hPrefix⟩

/-- 最小優先度の下降1ステップは、長さ・要素順列・処理位置の親子順序を保つ。 -/
theorem siftDownStep_minPrefer_local_contract (heap : Array Nat) (index : Nat)
    (hIndex : index < heap.size) :
    let nextHeap :=
      (LeanExperiments.RunningMedian.siftDownStep minPrefer heap index).1
    nextHeap.size = heap.size ∧ nextHeap.toList.Perm heap.toList ∧
      (2 * index + 1 < heap.size → nextHeap[index]! ≤ nextHeap[2 * index + 1]!) ∧
      (2 * index + 2 < heap.size → nextHeap[index]! ≤ nextHeap[2 * index + 2]!) := by
  let nextHeap :=
    (LeanExperiments.RunningMedian.siftDownStep minPrefer heap index).1
  have hSize : nextHeap.size = heap.size := by
    dsimp [nextHeap]
    exact siftDownStep_size minPrefer heap index
  have hPerm : nextHeap.toList.Perm heap.toList := by
    dsimp [nextHeap]
    exact siftDownStep_perm minPrefer heap index
  have hEdges := siftDownStep_minPrefer_orders_current_position heap index hIndex
  exact ⟨hSize, hPerm, hEdges.1, hEdges.2⟩

/-- 停止ステップでは例外位置の行も順序付けられ、配列全体が最小ヒープになる。 -/
theorem siftDownStep_minPrefer_stopped_repairs_exception
    (heap : Array Nat) (index : Nat) (hIndex : index < heap.size)
    (hExcept : MinHeapExcept heap index)
    (hStopped :
      (LeanExperiments.RunningMedian.siftDownStep minPrefer heap index).2.2 = false) :
    MinHeap (LeanExperiments.RunningMedian.siftDownStep minPrefer heap index).1 := by
  have hBest : LeanExperiments.RunningMedian.siftDownBest minPrefer heap index = index := by
    unfold LeanExperiments.RunningMedian.siftDownStep at hStopped
    dsimp at hStopped
    by_cases hEq : LeanExperiments.RunningMedian.siftDownBest minPrefer heap index == index
    · exact of_decide_eq_true hEq
    · simp [hEq] at hStopped
  have hStep := siftDownStep_stopped minPrefer heap index hStopped
  have hSelection := siftDownBest_minPrefer_selects_minimum heap index hIndex
  have hRow : index < heap.size →
      (2 * index + 1 < heap.size → heap[index]! ≤ heap[2 * index + 1]!) ∧
      (2 * index + 2 < heap.size → heap[index]! ≤ heap[2 * index + 2]!) := by
    intro hIndexBound
    simpa [hBest] using hSelection.2.2
  rw [hStep.1]
  exact MinHeapExcept.of_ordered_exception_row heap index hExcept hRow

/-- 下降経路上の現在位置は、根からの処理済み親行と値の上下関係を保つ。 -/
def MinHeapSiftPath (heap : Array Nat) (index : Nat) : Prop :=
  index = 0 ∨
    ∃ parent,
      (index = 2 * parent + 1 ∨ index = 2 * parent + 2) ∧
        heap[parent]! ≤ heap[index]! ∧
        (2 * index + 1 < heap.size → heap[parent]! ≤ heap[2 * index + 1]!) ∧
        (2 * index + 2 < heap.size → heap[parent]! ≤ heap[2 * index + 2]!)

/-- `MinHeapExcept` と経路条件は、根からの各 siftDown 反復で保たれる。 -/
theorem siftDownStep_minPrefer_preserves_path
    (heap : Array Nat) (index : Nat)
    (hExcept : MinHeapExcept heap index) (hPath : MinHeapSiftPath heap index)
    (hIndex : index < heap.size)
    (hRunning :
      (LeanExperiments.RunningMedian.siftDownStep minPrefer heap index).2.2 = true) :
    let nextHeap := (LeanExperiments.RunningMedian.siftDownStep minPrefer heap index).1
    let nextIndex := (LeanExperiments.RunningMedian.siftDownStep minPrefer heap index).2.1
    MinHeapExcept nextHeap nextIndex ∧ MinHeapSiftPath nextHeap nextIndex := by
  let nextHeap := (LeanExperiments.RunningMedian.siftDownStep minPrefer heap index).1
  let nextIndex := (LeanExperiments.RunningMedian.siftDownStep minPrefer heap index).2.1
  have hProgress := siftDownStep_progress minPrefer heap index hRunning
  have hStep := siftDownStep_running minPrefer heap index hRunning
  have hBestBound : LeanExperiments.RunningMedian.siftDownBest minPrefer heap index < heap.size := by
    rw [← hStep.2]
    exact hProgress.2
  have hNextIndex : nextIndex = LeanExperiments.RunningMedian.siftDownBest minPrefer heap index := by
    simpa [nextIndex] using hStep.2
  have hNextHeap : nextHeap =
      (LeanExperiments.RunningMedian.siftDownStep minPrefer heap index).1 := rfl
  by_cases hRoot : index = 0
  · subst index
    have hBelowRoot : ∀ row, 0 < row → row < heap.size →
        (2 * row + 1 < heap.size → heap[row]! ≤ heap[2 * row + 1]!) ∧
        (2 * row + 2 < heap.size → heap[row]! ≤ heap[2 * row + 2]!) := by
      intro row hPositive hRow
      exact hExcept row hRow (by omega)
    have hInitialized := siftDownStep_minPrefer_root_initializes_path heap hBelowRoot hRunning
    have hBestShape :
        LeanExperiments.RunningMedian.siftDownBest minPrefer heap 0 = 1 ∨
          LeanExperiments.RunningMedian.siftDownBest minPrefer heap 0 = 2 := by
      rcases siftDownBest_eq_index_or_child minPrefer heap 0 with hCurrent | hLeft | hRight
      · have := hProgress.1
        rw [hStep.2] at this
        omega
      · exact Or.inl hLeft
      · exact Or.inr hRight
    rcases hInitialized with ⟨hNextExcept, hRootBest, hRootLeft, hRootRight⟩
    refine ⟨?_, ?_⟩
    · simpa [nextHeap, nextIndex, hStep.2] using hNextExcept
    · rcases hBestShape with hLeft | hRight
      · refine Or.inr ⟨0, Or.inl ?_, ?_, ?_, ?_⟩
        · simpa [nextIndex, hStep.2] using hLeft
        · simpa [nextHeap, nextIndex, hStep.2] using hRootBest
        · simpa [nextHeap, nextIndex, hStep.2] using hRootLeft
        · simpa [nextHeap, nextIndex, hStep.2] using hRootRight
      · refine Or.inr ⟨0, Or.inr ?_, ?_, ?_, ?_⟩
        · simpa [nextIndex, hStep.2] using hRight
        · simpa [nextHeap, nextIndex, hStep.2] using hRootBest
        · simpa [nextHeap, nextIndex, hStep.2] using hRootLeft
        · simpa [nextHeap, nextIndex, hStep.2] using hRootRight
  · rcases hPath with hAtRoot | ⟨parent, hShape, hParentCurrent, hParentLeft, hParentRight⟩
    · omega
    have hMoved := siftDownStep_minPrefer_moves_minHeap_exception heap index parent hIndex
      hShape hExcept hParentLeft hParentRight hRunning
    rcases hMoved with ⟨hNextExcept, hNewParentCurrent, hNewParentLeft, hNewParentRight⟩
    have hNewShape :
        nextIndex = 2 * index + 1 ∨ nextIndex = 2 * index + 2 := by
      rcases siftDownBest_eq_index_or_child minPrefer heap index with hCurrent | hLeft | hRight
      · have hProgressIndex : index < nextIndex := by
          simpa [nextIndex] using hProgress.1
        rw [hNextIndex, hCurrent] at hProgressIndex
        omega
      · exact Or.inl (hNextIndex.trans hLeft)
      · exact Or.inr (hNextIndex.trans hRight)
    refine ⟨?_, ?_⟩
    · simpa [nextHeap, nextIndex, hStep.2] using hNextExcept
    · refine Or.inr ⟨index, hNewShape, ?_, ?_, ?_⟩
      · simpa [nextHeap, nextIndex, hStep.2] using hNewParentCurrent
      · simpa [nextHeap, nextIndex, hStep.2] using hNewParentLeft
      · simpa [nextHeap, nextIndex, hStep.2] using hNewParentRight

/-- 下降ループでは例外行・経路・実行中の範囲・停止時の正しさを保つ。 -/
def MinHeapSiftInvariant (heap : Array Nat) (index : Nat) (running : Bool) : Prop :=
  MinHeapExcept heap index ∧ MinHeapSiftPath heap index ∧
    (running = true → index < heap.size) ∧ (running = false → MinHeap heap)

/-- siftDown の1ステップは例外行と経路の不変条件を維持し、停止時に最小ヒープを返す。 -/
theorem siftDownStep_minPrefer_preserves_invariant (heap : Array Nat) (index : Nat)
    (hInvariant : MinHeapSiftInvariant heap index true) :
    MinHeapSiftInvariant
      (LeanExperiments.RunningMedian.siftDownStep minPrefer heap index).1
      (LeanExperiments.RunningMedian.siftDownStep minPrefer heap index).2.1
      (LeanExperiments.RunningMedian.siftDownStep minPrefer heap index).2.2 := by
  rcases hInvariant with ⟨hExcept, hPath, hIndex, _⟩
  by_cases hContinues :
      (LeanExperiments.RunningMedian.siftDownStep minPrefer heap index).2.2 = true
  · have hProgress := siftDownStep_progress minPrefer heap index hContinues
    have hTransition := siftDownStep_minPrefer_preserves_path heap index hExcept hPath
      (hIndex rfl) hContinues
    rcases hTransition with ⟨hExceptNext, hPathNext⟩
    refine ⟨hExceptNext, hPathNext, ?_, ?_⟩
    · intro _
      have hNextSize := siftDownStep_size minPrefer heap index
      calc
        (LeanExperiments.RunningMedian.siftDownStep minPrefer heap index).2.1 < heap.size :=
          hProgress.2
        _ = (LeanExperiments.RunningMedian.siftDownStep minPrefer heap index).1.size :=
          hNextSize.symm
    · intro hStopped
      simp [hContinues] at hStopped
  · have hStopped :
        (LeanExperiments.RunningMedian.siftDownStep minPrefer heap index).2.2 = false := by
      cases hFlag :
          (LeanExperiments.RunningMedian.siftDownStep minPrefer heap index).2.2 <;>
        simp_all
    have hIdentity := siftDownStep_stopped minPrefer heap index hStopped
    have hRepaired := siftDownStep_minPrefer_stopped_repairs_exception
      heap index (hIndex rfl) hExcept hStopped
    have hRepairedHeap : MinHeap heap := by simpa [hIdentity.1] using hRepaired
    rw [hIdentity.1, hIdentity.2, hStopped]
    exact ⟨hExcept, hPath, by simp, by intro _; exact hRepairedHeap⟩

/-- 根以外の行が初めから整った配列では、最小優先度の下降後に全体が最小ヒープになる。 -/
theorem siftDown_minPrefer_MinHeap_of_belowRoot (heap : Array Nat)
    (hBelowRoot : ∀ parent, 0 < parent → parent < heap.size →
      (2 * parent + 1 < heap.size → heap[parent]! ≤ heap[2 * parent + 1]!) ∧
      (2 * parent + 2 < heap.size → heap[parent]! ≤ heap[2 * parent + 2]!)) :
    MinHeap (LeanExperiments.RunningMedian.siftDown minPrefer heap 0) := by
  by_cases hNonempty : 0 < heap.size
  · generalize hRun : LeanExperiments.RunningMedian.siftDown minPrefer heap 0 = result
    apply Id.of_run_eq_wp hRun
    vcgen [LeanExperiments.RunningMedian.siftDown] invariants
    · fun finished state =>
        if finished then MinHeap state.1
        else MinHeapSiftInvariant state.1 state.2.1 state.2.2
    case vc1 =>
      simp
      unfold MinHeapSiftInvariant MinHeapSiftPath
      refine ⟨?_, Or.inl rfl, ?_, ?_⟩
      · intro parent hParent hParentNe
        have hParentNeZero : parent ≠ 0 := by simpa using hParentNe
        exact hBelowRoot parent (by omega) hParent
      · intro _
        exact hNonempty
      · intro hStopped
        cases hStopped
    case vc2 =>
      rename_i finalHeap finalIndex finalRunning hFinished
      simpa using hFinished
    case vc3 =>
      simp_all [Variant.evalsBelow_ofMeasure_nat, Variant.evalsTo_ofMeasure,
        Assertion.NondetFun.evalsTo_pure]
      rename_i currentHeap currentIndex currentFlag currentMeasure pair hInvariant hFlag
      constructor
      · have hMeasure := siftDownStep_variant_decreases minPrefer currentHeap currentIndex
        simpa [values, index, running, hFlag, hInvariant.1] using hMeasure
      · have hCurrentInvariant : MinHeapSiftInvariant currentHeap currentIndex true := by
          simpa [values, index, running, hFlag] using hInvariant.2
        have hStepInvariant := siftDownStep_minPrefer_preserves_invariant
          currentHeap currentIndex hCurrentInvariant
        simpa [values, index, running, hFlag] using hStepInvariant
    case vc4 =>
      simp_all [Variant.evalsTo_ofMeasure, Assertion.NondetFun.evalsTo_pure]
      rename_i currentHeap currentIndex currentFlag currentMeasure pair hInvariant hFlag
      exact hInvariant.2.2.2.2 rfl
  · have hEmpty : heap.size = 0 := by omega
    have hResultSize := siftDown_size minPrefer heap 0
    simp [hEmpty] at hResultSize
    intro index hIndex
    simp [hResultSize] at hIndex

/-- 最小優先度の下降1ステップ後、同じ位置を再評価すると停止する。 -/
theorem siftDownStep_minPrefer_stops_when_rechecked (heap : Array Nat) (index : Nat)
    (hIndex : index < heap.size) :
    let nextHeap :=
      (LeanExperiments.RunningMedian.siftDownStep minPrefer heap index).1
    (LeanExperiments.RunningMedian.siftDownStep minPrefer nextHeap index).2.2 = false := by
  let nextHeap :=
    (LeanExperiments.RunningMedian.siftDownStep minPrefer heap index).1
  change (LeanExperiments.RunningMedian.siftDownStep minPrefer nextHeap index).2.2 = false
  have hEdges := siftDownStep_minPrefer_orders_current_position heap index hIndex
  have hNextSize : nextHeap.size = heap.size := by
    dsimp [nextHeap]
    exact siftDownStep_size minPrefer heap index
  have hLeftStop : 2 * index + 1 < nextHeap.size →
      minPrefer nextHeap[2 * index + 1]! nextHeap[index]! = false := by
    intro hLeft
    have hLeftOriginal : 2 * index + 1 < heap.size := by
      simpa [hNextSize] using hLeft
    have hEdge := hEdges.1 hLeftOriginal
    have hEdgeLocal : nextHeap[index]! ≤ nextHeap[2 * index + 1]! := by
      simpa [nextHeap] using hEdge
    simp [minPrefer, Nat.not_lt.mpr hEdgeLocal]
  have hRightStop : 2 * index + 2 < nextHeap.size →
      minPrefer nextHeap[2 * index + 2]! nextHeap[index]! = false := by
    intro hRight
    have hRightOriginal : 2 * index + 2 < heap.size := by
      simpa [hNextSize] using hRight
    have hEdge := hEdges.2 hRightOriginal
    have hEdgeLocal : nextHeap[index]! ≤ nextHeap[2 * index + 2]! := by
      simpa [nextHeap] using hEdge
    simp [minPrefer, Nat.not_lt.mpr hEdgeLocal]
  have hBest := siftDownBest_eq_index_of_children_stopping minPrefer nextHeap index
    hLeftStop hRightStop
  simp [LeanExperiments.RunningMedian.siftDownStep, hBest]

/-- 最小優先度の下降1ステップ後に同じ位置を再評価すると、配列・添字を保って停止する。 -/
theorem siftDownStep_minPrefer_recheck_contract (heap : Array Nat) (index : Nat)
    (hIndex : index < heap.size) :
    let nextHeap :=
      (LeanExperiments.RunningMedian.siftDownStep minPrefer heap index).1
    (LeanExperiments.RunningMedian.siftDownStep minPrefer nextHeap index).1 = nextHeap ∧
      (LeanExperiments.RunningMedian.siftDownStep minPrefer nextHeap index).2.1 = index ∧
      (LeanExperiments.RunningMedian.siftDownStep minPrefer nextHeap index).2.2 = false := by
  let nextHeap :=
    (LeanExperiments.RunningMedian.siftDownStep minPrefer heap index).1
  have hStopped := siftDownStep_minPrefer_stops_when_rechecked heap index hIndex
  have hIdentity := siftDownStep_stopped minPrefer nextHeap index hStopped
  exact ⟨hIdentity.1, hIdentity.2, hStopped⟩

/-- 最小ヒープの数値仕様は、汎用の親子優先度仕様と同値である。 -/
theorem minHeap_iff_HeapOrdered_minPrefer (heap : Array Nat) :
    MinHeap heap ↔ HeapOrdered minPrefer heap := by
  simp [MinHeap, HeapOrdered, minPrefer]

/-- 推移的な優先関係では、ヒープの祖先は部分木の全子孫より優先されない。 -/
theorem HeapOrdered.ancestor_preferred_to_descendant {prefer : Nat → Nat → Bool}
    {heap : Array Nat}
    (hReflexive : ∀ value, prefer value value = false)
    (hTransitive : ∀ first second third,
      prefer first second = false → prefer second third = false →
        prefer first third = false)
    (hHeap : HeapOrdered prefer heap) {root index : Nat}
    (hDescendant : LeanExperiments.Verification.HeapSort.Spec.HeapDescendant root index)
    (hIndex : index < heap.size) :
    prefer heap[index]! heap[root]! = false := by
  induction hDescendant with
  | root => exact hReflexive heap[root]!
  | left hPath ih =>
      rename_i parent
      have hParentIndex : parent < heap.size := by omega
      have hLeftEdge := (hHeap parent hParentIndex).1 (by omega)
      exact hTransitive _ _ _ hLeftEdge (ih hParentIndex)
  | right hPath ih =>
      rename_i parent
      have hParentIndex : parent < heap.size := by omega
      have hRightEdge := (hHeap parent hParentIndex).2 (by omega)
      exact hTransitive _ _ _ hRightEdge (ih hParentIndex)

/-- 最小ヒープでは、任意の祖先の値が部分木の全子孫以下である。 -/
theorem MinHeap.ancestor_le_descendant {heap : Array Nat}
    (hHeap : MinHeap heap) {root index : Nat}
    (hDescendant : LeanExperiments.Verification.HeapSort.Spec.HeapDescendant root index)
    (hIndex : index < heap.size) :
    heap[root]! ≤ heap[index]! := by
  have hReflexive : ∀ value, minPrefer value value = false := minPrefer_irrefl
  have hTransitive : ∀ first second third,
      minPrefer first second = false → minPrefer second third = false →
        minPrefer first third = false := by
    intro first second third hFirst hSecond
    exact minPrefer_not_transitive hFirst hSecond
  have hPreferred := HeapOrdered.ancestor_preferred_to_descendant
    hReflexive hTransitive (minHeap_iff_HeapOrdered_minPrefer heap |>.mp hHeap)
    hDescendant hIndex
  simp [minPrefer] at hPreferred
  omega

/-- 最大ヒープでは、任意の祖先の値が部分木の全子孫以上である。 -/
theorem maxHeap.ancestor_ge_descendant {heap : Array Nat}
    (hHeap : HeapOrdered maxPrefer heap) {root index : Nat}
    (hDescendant : LeanExperiments.Verification.HeapSort.Spec.HeapDescendant root index)
    (hIndex : index < heap.size) :
    heap[index]! ≤ heap[root]! := by
  have hReflexive : ∀ value, maxPrefer value value = false := maxPrefer_irrefl
  have hTransitive : ∀ first second third,
      maxPrefer first second = false → maxPrefer second third = false →
        maxPrefer first third = false := by
    intro first second third hFirst hSecond
    exact maxPrefer_not_transitive hFirst hSecond
  have hPreferred := HeapOrdered.ancestor_preferred_to_descendant
    hReflexive hTransitive hHeap hDescendant hIndex
  simp [maxPrefer] at hPreferred
  omega

/-- 最小ヒープの根を任意の値で置き換えても、根より下の親子条件は保たれる。 -/
theorem minHeap_set_root_preserves_below_root {heap : Array Nat}
    (hHeap : MinHeap heap) (root : Nat) :
    ∀ parent, 0 < parent → parent < (heap.set! 0 root).size →
      (2 * parent + 1 < (heap.set! 0 root).size →
        (heap.set! 0 root)[parent]! ≤ (heap.set! 0 root)[2 * parent + 1]!) ∧
      (2 * parent + 2 < (heap.set! 0 root).size →
        (heap.set! 0 root)[parent]! ≤ (heap.set! 0 root)[2 * parent + 2]!) := by
  intro parent hParentPositive hParent
  have hParentSet : parent < heap.size := by simpa using hParent
  have hParentEdge := hHeap parent hParentSet
  constructor
  · intro hLeft
    have hLeftSet : 2 * parent + 1 < heap.size := by simpa using hLeft
    have hEdge := (hParentEdge.1 hLeftSet)
    rw [Array.getElem!_set!_ne _ 0 parent root (by omega),
      Array.getElem!_set!_ne _ 0 (2 * parent + 1) root (by omega)]
    exact hEdge
  · intro hRight
    have hRightSet : 2 * parent + 2 < heap.size := by simpa using hRight
    have hEdge := (hParentEdge.2 hRightSet)
    rw [Array.getElem!_set!_ne _ 0 parent root (by omega),
      Array.getElem!_set!_ne _ 0 (2 * parent + 2) root (by omega)]
    exact hEdge

/-- 根を除いた末尾配列も、元の最小ヒープの親子順序を保つ。 -/
theorem minHeap_pop_preserves_order {heap : Array Nat} (hHeap : MinHeap heap) :
    MinHeap heap.pop := by
  intro parent hParent
  have hParentInput : parent < heap.size := by
    simp only [Array.size_pop] at hParent
    omega
  have hParentPop : parent < heap.pop.size := by simpa using hParent
  have hParentValue : heap.pop[parent]! = heap[parent]! := by
    rw [getElem!_pos heap.pop parent hParentPop,
      getElem!_pos heap parent hParentInput, Array.getElem_pop hParentPop]
  constructor
  · intro hLeft
    have hLeftInput : 2 * parent + 1 < heap.size := by
      simp only [Array.size_pop] at hLeft
      omega
    have hLeftPop : 2 * parent + 1 < heap.pop.size := by simpa using hLeft
    have hLeftValue : heap.pop[2 * parent + 1]! = heap[2 * parent + 1]! := by
      rw [getElem!_pos heap.pop (2 * parent + 1) hLeftPop,
        getElem!_pos heap (2 * parent + 1) hLeftInput, Array.getElem_pop hLeftPop]
    rw [hParentValue, hLeftValue]
    exact (hHeap parent hParentInput).1 hLeftInput
  · intro hRight
    have hRightInput : 2 * parent + 2 < heap.size := by
      simp only [Array.size_pop] at hRight
      omega
    have hRightPop : 2 * parent + 2 < heap.pop.size := by simpa using hRight
    have hRightValue : heap.pop[2 * parent + 2]! = heap[2 * parent + 2]! := by
      rw [getElem!_pos heap.pop (2 * parent + 2) hRightPop,
        getElem!_pos heap (2 * parent + 2) hRightInput, Array.getElem_pop hRightPop]
    rw [hParentValue, hRightValue]
    exact (hHeap parent hParentInput).2 hRightInput

/-- 最小ヒープの根を末尾値で置き換えても、根より下の親子条件は保たれる。 -/
theorem minHeap_pop_set_root_preserves_below_root {heap : Array Nat}
    (hHeap : MinHeap heap) (last : Nat) :
    ∀ parent, 0 < parent → parent < (heap.pop.set! 0 last).size →
      (2 * parent + 1 < (heap.pop.set! 0 last).size →
        (heap.pop.set! 0 last)[parent]! ≤ (heap.pop.set! 0 last)[2 * parent + 1]!) ∧
      (2 * parent + 2 < (heap.pop.set! 0 last).size →
        (heap.pop.set! 0 last)[parent]! ≤ (heap.pop.set! 0 last)[2 * parent + 2]!) := by
  intro parent hParentPositive hParent
  exact minHeap_set_root_preserves_below_root (minHeap_pop_preserves_order hHeap) last
    parent hParentPositive hParent

/-- 汎用ヒープ検査を最小優先関数に適用すると、最小ヒープ仕様を正確に判定する。 -/
theorem heapCheck_minPrefer_correct (heap : Array Nat) :
    heapCheck minPrefer heap = true ↔ MinHeap heap := by
  calc
    heapCheck minPrefer heap = true ↔ HeapOrdered minPrefer heap :=
      heapCheck_correct minPrefer heap
    _ ↔ MinHeap heap := (minHeap_iff_HeapOrdered_minPrefer heap).symm

/-- 最大ヒープの数値仕様は、HeapSortの共通 `MaxHeap` 仕様と同値である。 -/
theorem heapSortMaxHeap_iff_HeapOrdered_maxPrefer (heap : Array Nat) :
    LeanExperiments.Verification.HeapSort.Spec.MaxHeap heap ↔
      HeapOrdered maxPrefer heap := by
  simp [LeanExperiments.Verification.HeapSort.Spec.MaxHeap, HeapOrdered, maxPrefer]

/-- 最大ヒープでは、追加値が親以下なら挿入は末尾追加と一致する。 -/
theorem insertHeap_eq_push_maxPrefer_of_parent_le (heap : Array Nat)
    (value : Nat)
    (hStops : heap.size = 0 ∨ value ≤ heap[(heap.size - 1) / 2]!) :
    LeanExperiments.RunningMedian.insertHeap maxPrefer heap value = heap.push value := by
  apply insertHeap_eq_push_of_stops
  rcases hStops with hEmpty | hParent
  · exact Or.inl hEmpty
  · right
    simp [maxPrefer]
    omega

/-- 最小ヒープでは、親が追加値以下なら挿入は末尾追加と一致する。 -/
theorem insertHeap_eq_push_minPrefer_of_parent_le (heap : Array Nat)
    (value : Nat)
    (hStops : heap.size = 0 ∨ heap[(heap.size - 1) / 2]! ≤ value) :
    LeanExperiments.RunningMedian.insertHeap minPrefer heap value = heap.push value := by
  apply insertHeap_eq_push_of_stops
  rcases hStops with hEmpty | hParent
  · exact Or.inl hEmpty
  · right
    simp [minPrefer]
    omega

/-- 最大ヒープでは、空ヒープまたは追加値が親以上なら挿入後も順序を保つ。 -/
theorem insertHeap_HeapOrdered_maxPrefer_of_parent_le (heap : Array Nat)
    (value : Nat) (hOrdered : HeapOrdered maxPrefer heap)
    (hStops : heap.size = 0 ∨ value ≤ heap[(heap.size - 1) / 2]!) :
    HeapOrdered maxPrefer (LeanExperiments.RunningMedian.insertHeap maxPrefer heap value) := by
  apply insertHeap_HeapOrdered_of_stops maxPrefer heap value hOrdered
  rcases hStops with hEmpty | hParent
  · exact Or.inl hEmpty
  · right
    simp [maxPrefer]
    omega

/-- 最小ヒープでは、空ヒープまたは追加値が親以下なら挿入後も順序を保つ。 -/
theorem insertHeap_HeapOrdered_minPrefer_of_parent_le (heap : Array Nat)
    (value : Nat) (hOrdered : HeapOrdered minPrefer heap)
    (hStops : heap.size = 0 ∨ heap[(heap.size - 1) / 2]! ≤ value) :
    HeapOrdered minPrefer (LeanExperiments.RunningMedian.insertHeap minPrefer heap value) := by
  apply insertHeap_HeapOrdered_of_stops minPrefer heap value hOrdered
  rcases hStops with hEmpty | hParent
  · exact Or.inl hEmpty
  · right
    simp [minPrefer]
    omega

/-- 追加値が最大ヒープの全要素以下なら、挿入後も最大ヒープ順序を保つ。 -/
theorem insertHeap_HeapOrdered_maxPrefer_of_le_all (heap : Array Nat)
    (value : Nat) (hOrdered : HeapOrdered maxPrefer heap)
    (hValue : ∀ index, index < heap.size → value ≤ heap[index]!) :
    HeapOrdered maxPrefer (LeanExperiments.RunningMedian.insertHeap maxPrefer heap value) := by
  apply insertHeap_HeapOrdered_maxPrefer_of_parent_le heap value hOrdered
  by_cases hEmpty : heap.size = 0
  · exact Or.inl hEmpty
  · right
    have hParent : (heap.size - 1) / 2 < heap.size := by omega
    have hAtParent := hValue ((heap.size - 1) / 2) hParent
    simpa only [getElem!_pos heap ((heap.size - 1) / 2) hParent] using hAtParent

/-- 最小ヒープの全要素が追加値以下なら、挿入後も最小ヒープ順序を保つ。 -/
theorem insertHeap_HeapOrdered_minPrefer_of_all_le (heap : Array Nat)
    (value : Nat) (hOrdered : HeapOrdered minPrefer heap)
    (hValue : ∀ index, index < heap.size → heap[index]! ≤ value) :
    HeapOrdered minPrefer (LeanExperiments.RunningMedian.insertHeap minPrefer heap value) := by
  apply insertHeap_HeapOrdered_minPrefer_of_parent_le heap value hOrdered
  by_cases hEmpty : heap.size = 0
  · exact Or.inl hEmpty
  · right
    have hParent : (heap.size - 1) / 2 < heap.size := by omega
    have hAtParent := hValue ((heap.size - 1) / 2) hParent
    simpa only [getElem!_pos heap ((heap.size - 1) / 2) hParent] using hAtParent

/-- 最大ヒープへの停止条件付き挿入は、共有 `MaxHeap` 仕様を保つ。 -/
theorem insertHeap_MaxHeap_of_parent_le (heap : Array Nat)
    (value : Nat) (hHeap : LeanExperiments.Verification.HeapSort.Spec.MaxHeap heap)
    (hStops : heap.size = 0 ∨ value ≤ heap[(heap.size - 1) / 2]!) :
    LeanExperiments.Verification.HeapSort.Spec.MaxHeap
      (LeanExperiments.RunningMedian.insertHeap maxPrefer heap value) := by
  apply (heapSortMaxHeap_iff_HeapOrdered_maxPrefer _).mpr
  exact insertHeap_HeapOrdered_maxPrefer_of_parent_le heap value
    ((heapSortMaxHeap_iff_HeapOrdered_maxPrefer heap).mp hHeap) hStops

/-- 最小ヒープへの停止条件付き挿入は、数値 `MinHeap` 仕様を保つ。 -/
theorem insertHeap_MinHeap_of_parent_le (heap : Array Nat)
    (value : Nat) (hHeap : MinHeap heap)
    (hStops : heap.size = 0 ∨ heap[(heap.size - 1) / 2]! ≤ value) :
    MinHeap (LeanExperiments.RunningMedian.insertHeap minPrefer heap value) := by
  apply (minHeap_iff_HeapOrdered_minPrefer _).mpr
  exact insertHeap_HeapOrdered_minPrefer_of_parent_le heap value
    ((minHeap_iff_HeapOrdered_minPrefer heap).mp hHeap) hStops

/-- 逐次中央値の最大ヒープ候補選択は、ヒープソートの下降処理と同じ位置を選ぶ。 -/
theorem maxSiftDownBest_eq_heapSortLargest (heap : Array Nat) (index : Nat) :
    LeanExperiments.RunningMedian.siftDownBest maxPrefer heap index =
      LeanExperiments.HeapSort.siftDownLargest heap index := by
  rfl

/-- 継続する最大ヒープ下降の交換結果は、ヒープソートの1段下降と一致する。 -/
theorem maxSiftDownStep_running_eq_heapSort_swap (heap : Array Nat) (index : Nat)
    (hRunning :
      (LeanExperiments.RunningMedian.siftDownStep maxPrefer heap index).2.2 = true) :
    (LeanExperiments.RunningMedian.siftDownStep maxPrefer heap index).1 =
      LeanExperiments.HeapSort.swap heap index
        (LeanExperiments.HeapSort.siftDownLargest heap index) := by
  have hProgress := siftDownStep_progress maxPrefer heap index hRunning
  have hStep := siftDownStep_running maxPrefer heap index hRunning
  rw [hStep.2, maxSiftDownBest_eq_heapSortLargest] at hProgress
  rw [hStep.1, maxSiftDownBest_eq_heapSortLargest]
  have hIndexBound : index < heap.size := Nat.lt_trans hProgress.1 hProgress.2
  have hRunningSwap :
      LeanExperiments.RunningMedian.swap heap index
          (LeanExperiments.HeapSort.siftDownLargest heap index) =
        heap.swap index (LeanExperiments.HeapSort.siftDownLargest heap index) := by
    simp [LeanExperiments.RunningMedian.swap, Array.swap, Array.setIfInBounds,
      hIndexBound, hProgress.2]
  have hHeapSortSwap :
      LeanExperiments.HeapSort.swap heap index
          (LeanExperiments.HeapSort.siftDownLargest heap index) =
        heap.swap index (LeanExperiments.HeapSort.siftDownLargest heap index) := by
    simp [LeanExperiments.HeapSort.swap, Array.swapIfInBounds,
      hIndexBound, hProgress.2]
  exact hRunningSwap.trans hHeapSortSwap.symm

/-- ヒープソートの下降不変条件は、最大ヒープの1段遷移でも継続・停止の両方で保たれる。 -/
theorem maxSiftDownStep_preserves_heapSortInvariant
    {initial : Array Nat} {root : Nat} {heap : Array Nat} {index : Nat}
    (hInvariant :
      LeanExperiments.Verification.HeapSort.Spec.siftDownLoopInvariant
        initial root heap index) :
    ((hRunning :
        (LeanExperiments.RunningMedian.siftDownStep maxPrefer heap index).2.2 = true) →
      LeanExperiments.Verification.HeapSort.Spec.siftDownLoopInvariant initial root
        (LeanExperiments.RunningMedian.siftDownStep maxPrefer heap index).1
        (LeanExperiments.RunningMedian.siftDownStep maxPrefer heap index).2.1) ∧
    ((hStopped :
        (LeanExperiments.RunningMedian.siftDownStep maxPrefer heap index).2.2 = false) →
      (LeanExperiments.RunningMedian.siftDownStep maxPrefer heap index).1 =
        LeanExperiments.HeapSort.siftDownRecursive initial root) := by
  constructor
  · intro hRunning
    have hProgress := siftDownStep_progress maxPrefer heap index hRunning
    have hStep := siftDownStep_running maxPrefer heap index hRunning
    have hIndexEq :
        (LeanExperiments.RunningMedian.siftDownStep maxPrefer heap index).2.1 =
          LeanExperiments.HeapSort.siftDownLargest heap index := by
      rw [hStep.2, maxSiftDownBest_eq_heapSortLargest]
    have hMoves : LeanExperiments.HeapSort.siftDownLargest heap index ≠ index := by
      intro hEq
      have hLt : index < LeanExperiments.HeapSort.siftDownLargest heap index := by
        simpa [hIndexEq] using hProgress.1
      omega
    have hArrayEq := maxSiftDownStep_running_eq_heapSort_swap heap index hRunning
    simpa [LeanExperiments.Verification.HeapSort.Spec.siftDownLoopInvariant,
      hArrayEq, hIndexEq] using
      (LeanExperiments.Verification.HeapSort.Spec.siftDownLoopInvariant_swap
        initial root heap index (LeanExperiments.HeapSort.siftDownLargest heap index)
        hInvariant rfl hMoves)
  · intro hStopped
    have hIdentity := siftDownStep_stopped maxPrefer heap index hStopped
    have hCandidateBool :
        (LeanExperiments.RunningMedian.siftDownBest maxPrefer heap index == index) = true := by
      cases hCandidate :
          (LeanExperiments.RunningMedian.siftDownBest maxPrefer heap index == index) <;>
        simp [LeanExperiments.RunningMedian.siftDownStep, hCandidate] at hStopped ⊢
    have hLargest : LeanExperiments.HeapSort.siftDownLargest heap index = index := by
      have hCandidate := beq_iff_eq.mp hCandidateBool
      simpa [maxSiftDownBest_eq_heapSortLargest] using hCandidate
    have hDominates :=
      (LeanExperiments.Verification.HeapSort.Spec.siftDownLargest_eq_index_iff_dominatesChildren
        heap index).mp hLargest
    rw [hIdentity.1]
    exact LeanExperiments.Verification.HeapSort.Spec.siftDownLoopInvariant_exit
      initial root heap index hInvariant hDominates.1 hDominates.2

/-- 逐次中央値の最大ヒープ下降ループは、任意配列でヒープソートの再帰下降と一致する。 -/
theorem maxSiftDown_eq_heapSortRecursive (heap : Array Nat) (start : Nat) :
    LeanExperiments.RunningMedian.siftDown maxPrefer heap start =
      LeanExperiments.HeapSort.siftDownRecursive heap start := by
  generalize hRun : LeanExperiments.RunningMedian.siftDown maxPrefer heap start = result
  apply Id.of_run_eq_wp hRun
  vcgen [LeanExperiments.RunningMedian.siftDown] invariants
  · fun finished state =>
      if finished then
        state.1 = LeanExperiments.HeapSort.siftDownRecursive heap start
      else if state.2.2 then
        LeanExperiments.Verification.HeapSort.Spec.siftDownLoopInvariant
          heap start state.1 state.2.1
      else state.1 = LeanExperiments.HeapSort.siftDownRecursive heap start
  case vc1 => simp [LeanExperiments.Verification.HeapSort.Spec.siftDownLoopInvariant]
  case vc2 => simp_all
  case vc3 =>
    simp_all [
      Variant.evalsBelow_ofMeasure_nat, Variant.evalsTo_ofMeasure,
      Assertion.NondetFun.evalsTo_pure]
    rename_i currentHeap currentIndex currentRunning currentMeasure pair hInvariant hFlag
    rcases hInvariant with ⟨hMeasureInvariant, hLoopInvariant⟩
    constructor
    · have hMeasure := siftDownStep_variant_decreases maxPrefer currentHeap currentIndex
      simpa [values, index, running, hMeasureInvariant] using hMeasure
    · by_cases hNextRunning : running = true
      · have hStepRunning :
            (LeanExperiments.RunningMedian.siftDownStep maxPrefer currentHeap currentIndex).2.2 = true := by
          simpa [running] using hNextRunning
        have hPreserved := maxSiftDownStep_preserves_heapSortInvariant hLoopInvariant
        have hNextInvariant := hPreserved.1 hStepRunning
        simpa [values, index, running, hNextRunning] using hNextInvariant
      · have hStepStopped :
            (LeanExperiments.RunningMedian.siftDownStep maxPrefer currentHeap currentIndex).2.2 = false := by
          cases hResult :
              (LeanExperiments.RunningMedian.siftDownStep maxPrefer currentHeap currentIndex).2.2 <;>
            simp_all [running]
        have hPreserved := maxSiftDownStep_preserves_heapSortInvariant hLoopInvariant
        have hFinal := hPreserved.2 hStepStopped
        simpa [values, index, running, hStepStopped] using hFinal
  case vc4 =>
    simp_all [Variant.evalsTo_ofMeasure,
      Assertion.NondetFun.evalsTo_pure]

/-- 根以外が最大ヒープなら、逐次中央値の最大ヒープ下降後は配列全体が最大ヒープになる。 -/
theorem maxSiftDown_heapOrdered_of_heapOrdered_below_root (heap : Array Nat)
    (hBelow : ∀ parent, 0 < parent → parent < heap.size →
      (2 * parent + 1 < heap.size → heap[2 * parent + 1]! ≤ heap[parent]!) ∧
      (2 * parent + 2 < heap.size → heap[2 * parent + 2]! ≤ heap[parent]!)) :
    HeapOrdered maxPrefer (LeanExperiments.RunningMedian.siftDown maxPrefer heap 0) := by
  rw [maxSiftDown_eq_heapSortRecursive]
  exact (heapSortMaxHeap_iff_HeapOrdered_maxPrefer _).mp
    (LeanExperiments.Verification.HeapSort.Spec.siftDownRecursive_maxHeap_of_heap_below_root
      heap hBelow)

/-- 最大ヒープ用 `popHeap` は、ヒープソートの検証済み最大値取り出しと一致する。 -/
theorem popHeap_maxPrefer_eq_heapSort_popMax (heap : Array Nat) :
    LeanExperiments.RunningMedian.popHeap maxPrefer heap =
      LeanExperiments.HeapSort.popMax heap := by
  simp [LeanExperiments.RunningMedian.popHeap, LeanExperiments.HeapSort.popMax,
    maxSiftDown_eq_heapSortRecursive,
    LeanExperiments.Verification.HeapSort.Spec.siftDown_eq_siftDownRecursive]

/-- 最大ヒープからの取り出しは根を返し、残余のヒープ条件と要素保存を保つ。 -/
theorem popHeap_maxPrefer_restCorrect_of_heapOrdered (heap : Array Nat)
    (hHeap : HeapOrdered maxPrefer heap) :
    LeanExperiments.Verification.HeapSort.Spec.PopMaxRestCorrectFor
      (LeanExperiments.RunningMedian.popHeap maxPrefer) heap := by
  unfold LeanExperiments.Verification.HeapSort.Spec.PopMaxRestCorrectFor
  rw [popHeap_maxPrefer_eq_heapSort_popMax]
  apply LeanExperiments.Verification.HeapSort.Spec.popMaxRestCorrectFor_of_maxHeap
  exact (heapSortMaxHeap_iff_HeapOrdered_maxPrefer _).mpr hHeap

/-- `popHeap` が成功すると、比較関数によらず残余配列の長さは1つ減る。 -/
theorem popHeap_size {prefer : Nat → Nat → Bool} {heap : Array Nat}
    {root : Nat} {rest : Array Nat}
    (hPop : LeanExperiments.RunningMedian.popHeap prefer heap = some (root, rest)) :
    rest.size + 1 = heap.size := by
  unfold LeanExperiments.RunningMedian.popHeap at hPop
  cases hRoot : heap[0]? with
  | none => simp [hRoot] at hPop
  | some actualRoot =>
      cases hBack : heap.back? with
      | none => simp [hRoot, hBack] at hPop
      | some last =>
          by_cases hEmpty : heap.pop.isEmpty
          · simp [hRoot, hBack, hEmpty] at hPop
            rw [← hPop.2]
            have hPopEmpty : heap.pop = #[] := by simpa using hEmpty
            have hPopSize : heap.pop.size = 0 := by simp [hPopEmpty]
            have hSizePop : heap.pop.size = heap.size - 1 := by
              simp [Array.size_pop]
            have hPositive : 0 < heap.size :=
              (Array.getElem?_eq_some_iff.mp hRoot).1
            omega
          · simp [hRoot, hBack, hEmpty] at hPop
            have hRestSize : rest.size = heap.pop.size := by
              rw [← hPop.2]
              simpa using siftDown_size prefer (heap.pop.set! 0 last) 0
            rw [hRestSize, Array.size_pop]
            have hPositive : 0 < heap.size :=
              (Array.getElem?_eq_some_iff.mp hRoot).1
            omega

/-- `popHeap` は、比較関数によらず根以外の要素を順列として残す。 -/
theorem popHeap_perm_dropRoot {prefer : Nat → Nat → Bool} {heap : Array Nat}
    {root : Nat} {rest : Array Nat}
    (hPop : LeanExperiments.RunningMedian.popHeap prefer heap = some (root, rest)) :
    rest.toList.Perm (heap.toList.drop 1) := by
  unfold LeanExperiments.RunningMedian.popHeap at hPop
  cases hRoot : heap[0]? with
  | none => simp [hRoot] at hPop
  | some actualRoot =>
      cases hBack : heap.back? with
      | none => simp [hRoot, hBack] at hPop
      | some last =>
          by_cases hEmpty : heap.pop.isEmpty
          · simp [hRoot, hBack, hEmpty] at hPop
            have hPopEmpty : heap.pop = #[] := by simpa using hEmpty
            have hRest : rest = #[] := by
              simpa [hPopEmpty] using hPop.2.symm
            have hPopSize : heap.pop.size = 0 := by simp [hPopEmpty]
            have hSizePop : heap.pop.size = heap.size - 1 := by
              simp [Array.size_pop]
            have hPositive : 0 < heap.size :=
              (Array.getElem?_eq_some_iff.mp hRoot).1
            have hHeapSize : heap.size = 1 := by omega
            have hListSize : heap.toList.length = 1 := by
              simpa only [Array.length_toList] using hHeapSize
            have hDropSize : (heap.toList.drop 1).length = 0 := by
              simp [hListSize]
            have hDropEmpty : heap.toList.drop 1 = [] :=
              List.eq_nil_of_length_eq_zero hDropSize
            rw [hRest, hDropEmpty]
          · simp [hRoot, hBack, hEmpty] at hPop
            have hPopPositive : 0 < heap.pop.size :=
              Array.size_pos_iff.mpr (by simpa using hEmpty)
            have hSize : 1 < heap.size := by
              rw [Array.size_pop] at hPopPositive
              omega
            rw [← hPop.2]
            exact
              (siftDown_perm prefer (heap.pop.set! 0 last) 0).trans
                (LeanExperiments.Verification.HeapSort.Spec.popSetBack_toList_perm_dropRoot
                  heap hSize actualRoot last hRoot hBack)

/-- `popHeap` が `none` を返すのは、入力ヒープが空の場合に限る。 -/
theorem popHeap_eq_none_iff_empty (prefer : Nat → Nat → Bool) (heap : Array Nat) :
    LeanExperiments.RunningMedian.popHeap prefer heap = none ↔ heap.size = 0 := by
  cases hRoot : heap[0]? with
  | none =>
      have hSize : heap.size = 0 := by
        have hBound := Array.getElem?_eq_none_iff.mp hRoot
        omega
      simp [LeanExperiments.RunningMedian.popHeap, hSize]
  | some actualRoot =>
      have hPositive : 0 < heap.size :=
        (Array.getElem?_eq_some_iff.mp hRoot).1
      cases hBack : heap.back? with
      | none =>
          have hEmpty := Array.back?_eq_none_iff.mp hBack
          have hSize : heap.size = 0 := by simp [hEmpty]
          omega
      | some last =>
          constructor
          · intro hNone
            by_cases hPopEmpty : heap.pop = #[]
            · simp [LeanExperiments.RunningMedian.popHeap, hRoot, hBack,
                hPopEmpty] at hNone
            · simp [LeanExperiments.RunningMedian.popHeap, hRoot, hBack,
                hPopEmpty] at hNone
          · intro hSize
            omega

/-- 下側の根移動が失敗するのは、移動元の下側ヒープが空の場合に限る。 -/
theorem transferLowerRoot_eq_none_iff_empty
    (sourcePrefer destinationPrefer : Nat → Nat → Bool)
    (lower upper : Array Nat) :
    LeanExperiments.RunningMedian.transferLowerRoot sourcePrefer destinationPrefer
        lower upper = none ↔ lower.size = 0 := by
  unfold LeanExperiments.RunningMedian.transferLowerRoot
  cases hPop : LeanExperiments.RunningMedian.popHeap sourcePrefer lower with
  | none =>
      constructor
      · intro _
        exact (popHeap_eq_none_iff_empty sourcePrefer lower).mp hPop
      · intro _
        simp
  | some pair =>
      rcases pair with ⟨value, rest⟩
      have hPositive : 0 < lower.size := by
        have hSize := popHeap_size hPop
        omega
      constructor
      · intro hNone
        simp at hNone
      · intro hEmpty
        omega

/-- 上側の根移動が失敗するのは、移動元の上側ヒープが空の場合に限る。 -/
theorem transferUpperRoot_eq_none_iff_empty
    (sourcePrefer destinationPrefer : Nat → Nat → Bool)
    (lower upper : Array Nat) :
    LeanExperiments.RunningMedian.transferUpperRoot sourcePrefer destinationPrefer
        lower upper = none ↔ upper.size = 0 := by
  unfold LeanExperiments.RunningMedian.transferUpperRoot
  cases hPop : LeanExperiments.RunningMedian.popHeap sourcePrefer upper with
  | none =>
      constructor
      · intro _
        exact (popHeap_eq_none_iff_empty sourcePrefer upper).mp hPop
      · intro _
        simp
  | some pair =>
      rcases pair with ⟨value, rest⟩
      have hPositive : 0 < upper.size := by
        have hSize := popHeap_size hPop
        omega
      constructor
      · intro hNone
        simp at hNone
      · intro hEmpty
        omega

/-- 根の移動遷移では、下側が1つ減り上側が1つ増える。 -/
theorem transferLowerRoot_size {sourcePrefer destinationPrefer : Nat → Nat → Bool}
    {lower upper nextLower nextUpper : Array Nat}
    (hMove : LeanExperiments.RunningMedian.transferLowerRoot sourcePrefer destinationPrefer
      lower upper = some (nextLower, nextUpper)) :
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
      exact ⟨popHeap_size hPop, by simp [insertHeap_size]⟩

/-- 反対向きの根の移動遷移では、下側が1つ増え上側が1つ減る。 -/
theorem transferUpperRoot_size {sourcePrefer destinationPrefer : Nat → Nat → Bool}
    {lower upper nextLower nextUpper : Array Nat}
    (hMove : LeanExperiments.RunningMedian.transferUpperRoot sourcePrefer destinationPrefer
      lower upper = some (nextLower, nextUpper)) :
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
      exact ⟨by simp [insertHeap_size], popHeap_size hPop⟩

/-- 下側の根移動が成功するのは、移動元の下側ヒープが空でない場合に限る。 -/
theorem transferLowerRoot_isSome_iff_source_nonempty
    (sourcePrefer destinationPrefer : Nat → Nat → Bool)
    (lower upper : Array Nat) :
    (LeanExperiments.RunningMedian.transferLowerRoot sourcePrefer destinationPrefer
      lower upper).isSome = true ↔ 0 < lower.size := by
  cases hMove : LeanExperiments.RunningMedian.transferLowerRoot
      sourcePrefer destinationPrefer lower upper with
  | none =>
      have hEmpty := (transferLowerRoot_eq_none_iff_empty
        sourcePrefer destinationPrefer lower upper).mp hMove
      simp [hEmpty]
  | some result =>
      rcases result with ⟨nextLower, nextUpper⟩
      have hSize := transferLowerRoot_size hMove
      simp
      omega

/-- 上側の根移動が成功するのは、移動元の上側ヒープが空でない場合に限る。 -/
theorem transferUpperRoot_isSome_iff_source_nonempty
    (sourcePrefer destinationPrefer : Nat → Nat → Bool)
    (lower upper : Array Nat) :
    (LeanExperiments.RunningMedian.transferUpperRoot sourcePrefer destinationPrefer
      lower upper).isSome = true ↔ 0 < upper.size := by
  cases hMove : LeanExperiments.RunningMedian.transferUpperRoot
      sourcePrefer destinationPrefer lower upper with
  | none =>
      have hEmpty := (transferUpperRoot_eq_none_iff_empty
        sourcePrefer destinationPrefer lower upper).mp hMove
      simp [hEmpty]
  | some result =>
      rcases result with ⟨nextLower, nextUpper⟩
      have hSize := transferUpperRoot_size hMove
      simp
      omega

/-- 下側のサイズが上側以下なら、下側からの再平衡ループは状態を変えない。 -/
theorem rebalanceLower_eq_self_of_size_le (lower upper : Array Nat)
    (hSize : lower.size ≤ upper.size + 1) :
    LeanExperiments.RunningMedian.rebalanceLower lower upper = (lower, upper) := by
  generalize hRun : LeanExperiments.RunningMedian.rebalanceLower lower upper = result
  unfold LeanExperiments.RunningMedian.rebalanceLower at hRun
  apply Id.of_run_eq_wp hRun
  vcgen [LeanExperiments.RunningMedian.rebalanceLower] invariants
  · fun _ heaps => heaps = (lower, upper)
  case vc1 => simp_all <;> omega
  case vc2 => simp_all <;> omega
  case vc3 => simp_all <;> omega

/-- 下側サイズが2超過し、1回の根移動で均衡するなら再平衡結果はその移動先である。

ループ不変条件は初期状態と移動後状態だけを許す。移動後のサイズ条件で次の反復が
停止し、成功した遷移をループ全体の契約へ接続する。
-/
theorem rebalanceLower_one_transfer
    (lower upper nextLower nextUpper : Array Nat)
    (hStart : upper.size + 1 < lower.size)
    (hTransfer : LeanExperiments.RunningMedian.transferLowerRoot maxPrefer minPrefer
      lower upper = some (nextLower, nextUpper))
    (hBalanced : nextLower.size ≤ nextUpper.size + 1) :
    LeanExperiments.RunningMedian.rebalanceLower lower upper = (nextLower, nextUpper) := by
  generalize hRun : LeanExperiments.RunningMedian.rebalanceLower lower upper = result
  unfold LeanExperiments.RunningMedian.rebalanceLower at hRun
  apply Id.of_run_eq_wp hRun
  vcgen [LeanExperiments.RunningMedian.rebalanceLower] invariants
  case inv1 =>
    exact fun exit heaps =>
      if exit then heaps = (nextLower, nextUpper)
      else heaps = (lower, upper) ∨ heaps = (nextLower, nextUpper)
  case vc1 => simp_all
  case vc2 => assumption
  case vc3 =>
    simp_all
    rcases ‹_ ∧ _› with ⟨hMeasure, hInvariant⟩
    rcases hInvariant with hInitial | hFinal
    · rcases hInitial with ⟨hLower, hUpper⟩
      cases hLower
      cases hUpper
      simp_all
      rename_i transition
      have hTransferImpl := hTransfer
      change LeanExperiments.RunningMedian.transferLowerRoot
          LeanExperiments.RunningMedian.maxPrefer LeanExperiments.RunningMedian.minPrefer
          lower upper = some (nextLower, nextUpper) at hTransferImpl
      rw [hTransferImpl] at transition
      injection transition with hPair
      cases hPair
      have hMoveSize := transferLowerRoot_size hTransfer
      constructor
      · omega
      · right
        exact ⟨rfl, rfl⟩
    · rcases hFinal with ⟨hLower, hUpper⟩
      cases hLower
      cases hUpper
      simp_all
      omega
  case vc4 =>
    simp_all
    rcases ‹_ ∧ _› with ⟨hMeasure, hInvariant⟩
    rcases hInvariant with hInitial | hFinal
    · rcases hInitial with ⟨hLower, hUpper⟩
      cases hLower
      cases hUpper
      simp_all [LeanExperiments.RunningMedian.transferLowerRoot]
      rename_i measure opt noSome guard invariant transition
      exfalso
      exact noSome nextLower nextUpper (by
        simpa [LeanExperiments.RunningMedian.transferLowerRoot] using
          transition.symm.trans hTransfer)
    · rcases hFinal with ⟨hLower, hUpper⟩
      cases hLower
      cases hUpper
      simp_all
  case vc5 =>
    simp_all
    rcases ‹_ ∧ _› with ⟨hMeasure, hInvariant⟩
    rcases hInvariant with hInitial | hFinal
    · rcases hInitial with ⟨hLower, hUpper⟩
      cases hLower
      cases hUpper
      simp_all
      omega
    · exact hFinal

/-- 上側のサイズが下側以下なら、上側からの再平衡ループは状態を変えない。 -/
theorem rebalanceUpper_eq_self_of_size_le (lower upper : Array Nat)
    (hSize : upper.size ≤ lower.size) :
    LeanExperiments.RunningMedian.rebalanceUpper lower upper = (lower, upper) := by
  generalize hRun : LeanExperiments.RunningMedian.rebalanceUpper lower upper = result
  unfold LeanExperiments.RunningMedian.rebalanceUpper at hRun
  apply Id.of_run_eq_wp hRun
  vcgen [LeanExperiments.RunningMedian.rebalanceUpper] invariants
  · fun _ heaps => heaps = (lower, upper)
  case vc1 => simp_all <;> omega
  case vc2 => simp_all <;> omega
  case vc3 => simp_all <;> omega

/-- 上側が下側より大きく、1回の根移動で上側が下側以下になるなら、
上側からの再平衡ループはその移動先で停止する。

初期状態と移動後状態だけをループ不変条件に使い、サイズ条件から次の反復が
停止することを示す。
-/
theorem rebalanceUpper_one_transfer
    (lower upper nextLower nextUpper : Array Nat)
    (hStart : lower.size < upper.size)
    (hTransfer : LeanExperiments.RunningMedian.transferUpperRoot minPrefer maxPrefer
      lower upper = some (nextLower, nextUpper))
    (hBalanced : nextUpper.size ≤ nextLower.size) :
    LeanExperiments.RunningMedian.rebalanceUpper lower upper = (nextLower, nextUpper) := by
  generalize hRun : LeanExperiments.RunningMedian.rebalanceUpper lower upper = result
  unfold LeanExperiments.RunningMedian.rebalanceUpper at hRun
  apply Id.of_run_eq_wp hRun
  vcgen [LeanExperiments.RunningMedian.rebalanceUpper] invariants
  case inv1 =>
    exact fun exit heaps =>
      if exit then heaps = (nextLower, nextUpper)
      else heaps = (lower, upper) ∨ heaps = (nextLower, nextUpper)
  case vc1 => simp_all
  case vc2 => assumption
  case vc3 =>
    simp_all
    rcases ‹_ ∧ _› with ⟨hMeasure, hInvariant⟩
    rcases hInvariant with hInitial | hFinal
    · rcases hInitial with ⟨hLower, hUpper⟩
      cases hLower
      cases hUpper
      simp_all
      rename_i transition
      have hTransferImpl := hTransfer
      change LeanExperiments.RunningMedian.transferUpperRoot
          LeanExperiments.RunningMedian.minPrefer LeanExperiments.RunningMedian.maxPrefer
          lower upper = some (nextLower, nextUpper) at hTransferImpl
      rw [hTransferImpl] at transition
      injection transition with hPair
      cases hPair
      have hMoveSize := transferUpperRoot_size hTransfer
      constructor
      · omega
      · right
        exact ⟨rfl, rfl⟩
    · rcases hFinal with ⟨hLower, hUpper⟩
      cases hLower
      cases hUpper
      simp_all
      omega
  case vc4 =>
    simp_all
    rcases ‹_ ∧ _› with ⟨hMeasure, hInvariant⟩
    rcases hInvariant with hInitial | hFinal
    · rcases hInitial with ⟨hLower, hUpper⟩
      cases hLower
      cases hUpper
      simp_all [LeanExperiments.RunningMedian.transferUpperRoot]
      rename_i measure opt noSome guard invariant transition
      exfalso
      exact noSome nextLower nextUpper (by
        simpa [LeanExperiments.RunningMedian.transferUpperRoot] using
          transition.symm.trans hTransfer)
    · rcases hFinal with ⟨hLower, hUpper⟩
      cases hLower
      cases hUpper
      simp_all
  case vc5 =>
    simp_all
    rcases ‹_ ∧ _› with ⟨hMeasure, hInvariant⟩
    rcases hInvariant with hInitial | hFinal
    · rcases hInitial with ⟨hLower, hUpper⟩
      cases hLower
      cases hUpper
      simp_all
      omega
    · exact hFinal

/-- 2つのヒープが同じサイズなら、再平衡ループの合成は状態を変えない。 -/
theorem rebalanceLoops_eq_self_of_size_eq (lower upper : Array Nat)
    (hSize : lower.size = upper.size) :
    let balanced := LeanExperiments.RunningMedian.rebalanceLower lower upper
    LeanExperiments.RunningMedian.rebalanceUpper balanced.1 balanced.2 = (lower, upper) := by
  change LeanExperiments.RunningMedian.rebalanceUpper
    (LeanExperiments.RunningMedian.rebalanceLower lower upper).1
    (LeanExperiments.RunningMedian.rebalanceLower lower upper).2 = (lower, upper)
  rw [rebalanceLower_eq_self_of_size_le lower upper (by omega)]
  exact rebalanceUpper_eq_self_of_size_le lower upper (by omega)

/-- 下側が同数または1つ多い状態では、再平衡の合成は状態を変えない。 -/
theorem rebalanceLoops_eq_self_of_balanced_size (lower upper : Array Nat)
    (hSize : lower.size = upper.size ∨ lower.size = upper.size + 1) :
    let balanced := LeanExperiments.RunningMedian.rebalanceLower lower upper
    LeanExperiments.RunningMedian.rebalanceUpper balanced.1 balanced.2 = (lower, upper) := by
  change LeanExperiments.RunningMedian.rebalanceUpper
    (LeanExperiments.RunningMedian.rebalanceLower lower upper).1
    (LeanExperiments.RunningMedian.rebalanceLower lower upper).2 = (lower, upper)
  rcases hSize with hEqual | hLowerExtra
  · rw [rebalanceLower_eq_self_of_size_le lower upper (by omega)]
    exact rebalanceUpper_eq_self_of_size_le lower upper (by omega)
  · rw [rebalanceLower_eq_self_of_size_le lower upper (by omega)]
    exact rebalanceUpper_eq_self_of_size_le lower upper (by omega)

/-- 最大ヒープ用 `popHeap` は、任意の2要素配列から根と末尾だけの配列を返す。 -/
theorem popHeap_maxPrefer_pair (left right : Nat) :
    LeanExperiments.RunningMedian.popHeap maxPrefer #[left, right] =
      some (left, #[right]) := by
  have hSift : LeanExperiments.HeapSort.siftDown #[right] 0 = #[right] := by
    rw [LeanExperiments.Verification.HeapSort.Spec.siftDown_eq_siftDownRecursive]
    exact LeanExperiments.Verification.HeapSort.Spec.siftDownRecursive_eq_self_of_noLeftChild
      #[right] 0 (by simp)
  rw [popHeap_maxPrefer_eq_heapSort_popMax]
  simp [LeanExperiments.HeapSort.popMax, hSift]

/-- 最大ヒープの2要素からの根移動は、根を上側の空ヒープへ移す。 -/
theorem transferLowerRoot_pair (left right : Nat) :
    LeanExperiments.RunningMedian.transferLowerRoot maxPrefer minPrefer
      #[left, right] #[] = some (#[right], #[left]) := by
  simp [LeanExperiments.RunningMedian.transferLowerRoot, popHeap_maxPrefer_pair,
    insertHeap_empty]

/-- 2要素の下側ヒープと空の上側ヒープは、根を移して再平衡を終える。 -/
theorem rebalanceLower_pair (left right : Nat) :
    LeanExperiments.RunningMedian.rebalanceLower #[left, right] #[] =
      (#[right], #[left]) := by
  have hPopImpl : LeanExperiments.RunningMedian.popHeap LeanExperiments.RunningMedian.maxPrefer
      #[left, right] = some (left, #[right]) := by
    change LeanExperiments.RunningMedian.popHeap
      (fun candidate current => current < candidate) #[left, right] = some (left, #[right])
    exact popHeap_maxPrefer_pair left right
  have hTransfer : LeanExperiments.RunningMedian.transferLowerRoot
      LeanExperiments.RunningMedian.maxPrefer LeanExperiments.RunningMedian.minPrefer
      #[left, right] #[] = some (#[right], #[left]) := by
    simp [LeanExperiments.RunningMedian.transferLowerRoot, hPopImpl, insertHeap_empty]
  generalize hRun : LeanExperiments.RunningMedian.rebalanceLower #[left, right] #[] = result
  unfold LeanExperiments.RunningMedian.rebalanceLower at hRun
  apply Id.of_run_eq_wp hRun
  vcgen [LeanExperiments.RunningMedian.rebalanceLower] invariants
  case inv1 =>
    exact fun exit heaps =>
      if exit then heaps = (#[right], #[left])
      else heaps = (#[left, right], #[]) ∨ heaps = (#[right], #[left])
  case vc1 => simp [lower, upper]
  case vc2 => assumption
  case vc3 =>
    simp_all
    rcases ‹_ ∧ _› with ⟨hMeasure, hInvariant⟩
    rcases hInvariant with hInitial | hFinal
    · rcases hInitial with ⟨hA, hB⟩
      cases hA
      cases hB
      simp_all
    · rcases hFinal with ⟨hA, hB⟩
      cases hA
      cases hB
      simp_all
      omega
  case vc4 =>
    simp_all
    rcases ‹_ ∧ _› with ⟨hMeasure, hInvariant⟩
    rcases hInvariant with hInitial | hFinal
    · rcases hInitial with ⟨hA, hB⟩
      cases hA
      cases hB
      simp_all [LeanExperiments.RunningMedian.transferLowerRoot]
      rename_i measure opt noSome guard inv transition
      exact noSome #[right] #[left] (by simpa [hTransfer] using transition.symm)
    · rcases hFinal with ⟨hA, hB⟩
      cases hA
      cases hB
      simp_all
  case vc5 =>
    simp_all
    rcases ‹_ ∧ _› with ⟨hMeasure, hInvariant⟩
    rcases hInvariant with hInitial | hFinal
    · rcases hInitial with ⟨hA, hB⟩
      cases hA
      cases hB
      simp_all
      omega
    · exact hFinal

/-- 最小ヒープ用 `popHeap` も、任意の2要素配列から根と末尾だけの配列を返す。 -/
theorem popHeap_minPrefer_pair (left right : Nat) :
    LeanExperiments.RunningMedian.popHeap minPrefer #[left, right] =
      some (left, #[right]) := by
  have hSift : LeanExperiments.RunningMedian.siftDown minPrefer #[right] 0 = #[right] :=
    siftDown_eq_self_of_heapOrdered minPrefer #[right] 0 (by simp)
      (by simp [HeapOrdered, minPrefer])
  simp [LeanExperiments.RunningMedian.popHeap, hSift]

/-- 空の下側ヒープへ、上側2要素の根を移す具体的な遷移。 -/
theorem transferUpperRoot_pair (left right : Nat) :
    LeanExperiments.RunningMedian.transferUpperRoot minPrefer maxPrefer
      #[] #[left, right] = some (#[left], #[right]) := by
  simp [LeanExperiments.RunningMedian.transferUpperRoot, popHeap_minPrefer_pair,
    insertHeap_empty]

/-- 1要素の下側へ上側2要素の根を移すと、上側は残りの1要素になる。

大小関係を仮定せず、1回の根移動を正確に表す。再平衡ループの長さ2ケースを
検証するときに、ヒープへの再挿入と上側の残余を分離して扱える。
-/
theorem transferUpperRoot_singleton_pair (lowerRoot upperRoot upperOther : Nat) :
    LeanExperiments.RunningMedian.transferUpperRoot
      LeanExperiments.RunningMedian.minPrefer LeanExperiments.RunningMedian.maxPrefer
      #[lowerRoot] #[upperRoot, upperOther] =
        some (LeanExperiments.RunningMedian.insertHeap
          LeanExperiments.RunningMedian.maxPrefer #[lowerRoot] upperRoot,
          #[upperOther]) := by
  have hPop : LeanExperiments.RunningMedian.popHeap
      LeanExperiments.RunningMedian.minPrefer #[upperRoot, upperOther] =
        some (upperRoot, #[upperOther]) := by
    change LeanExperiments.RunningMedian.popHeap minPrefer
      #[upperRoot, upperOther] = some (upperRoot, #[upperOther])
    exact popHeap_minPrefer_pair upperRoot upperOther
  simp [LeanExperiments.RunningMedian.transferUpperRoot, hPop]

/-- 下側1要素・上側2要素の再平衡は、上側の根を1回移して停止する。

値の大小関係を仮定せず、任意のNat配列値について再平衡ループの状態遷移を
確定する。逐次挿入の上側振り分け分岐を不変条件へ接続するための一般補題である。
-/
theorem rebalanceUpper_singleton_pair (lowerRoot upperRoot upperOther : Nat) :
    LeanExperiments.RunningMedian.rebalanceUpper #[lowerRoot] #[upperRoot, upperOther] =
      (LeanExperiments.RunningMedian.insertHeap LeanExperiments.RunningMedian.maxPrefer
        #[lowerRoot] upperRoot, #[upperOther]) := by
  have hTransfer : LeanExperiments.RunningMedian.transferUpperRoot
      LeanExperiments.RunningMedian.minPrefer LeanExperiments.RunningMedian.maxPrefer
      #[lowerRoot] #[upperRoot, upperOther] = some
        (LeanExperiments.RunningMedian.insertHeap LeanExperiments.RunningMedian.maxPrefer
          #[lowerRoot] upperRoot, #[upperOther]) := by
    exact transferUpperRoot_singleton_pair lowerRoot upperRoot upperOther
  generalize hRun : LeanExperiments.RunningMedian.rebalanceUpper
    #[lowerRoot] #[upperRoot, upperOther] = result
  unfold LeanExperiments.RunningMedian.rebalanceUpper at hRun
  apply Id.of_run_eq_wp hRun
  vcgen [LeanExperiments.RunningMedian.rebalanceUpper] invariants
  case inv1 =>
    exact fun exit heaps =>
      if exit then heaps =
        (LeanExperiments.RunningMedian.insertHeap LeanExperiments.RunningMedian.maxPrefer
          #[lowerRoot] upperRoot, #[upperOther])
      else heaps = (#[lowerRoot], #[upperRoot, upperOther]) ∨ heaps =
        (LeanExperiments.RunningMedian.insertHeap LeanExperiments.RunningMedian.maxPrefer
          #[lowerRoot] upperRoot, #[upperOther])
  case vc1 => simp [lower, upper]
  case vc2 => assumption
  case vc3 =>
    simp_all
    rcases ‹_ ∧ _› with ⟨hMeasure, hInvariant⟩
    rcases hInvariant with hInitial | hFinal
    · rcases hInitial with ⟨hA, hB⟩
      cases hA
      cases hB
      simp_all
    · rcases hFinal with ⟨hA, hB⟩
      cases hA
      cases hB
      simp_all [insertHeap_size]
      omega
  case vc4 =>
    simp_all
    rcases ‹_ ∧ _› with ⟨hMeasure, hInvariant⟩
    rcases hInvariant with hInitial | hFinal
    · rcases hInitial with ⟨hA, hB⟩
      cases hA
      cases hB
      simp_all [LeanExperiments.RunningMedian.transferUpperRoot]
      rename_i measure opt noSome guard inv transition
      exact noSome
        (LeanExperiments.RunningMedian.insertHeap LeanExperiments.RunningMedian.maxPrefer
          #[lowerRoot] upperRoot) #[upperOther]
        transition.symm
    · rcases hFinal with ⟨hA, hB⟩
      cases hA
      cases hB
      simp_all
  case vc5 =>
    simp_all
    rcases ‹_ ∧ _› with ⟨hMeasure, hInvariant⟩
    rcases hInvariant with hInitial | hFinal
    · rcases hInitial with ⟨hA, hB⟩
      cases hA
      cases hB
      simp_all
      omega
    · exact hFinal

/-- 下側根より大きい値を単一要素状態へ挿入したときの実装結果。

新しい値が上側根より小さければその値を下側へ移し、そうでなければ既存の上側根を
下側へ移す。分岐ごとの最終配列を、値に上限を置かずに特定する。
-/
theorem insert_from_two_singletons_upper_eq (lowerRoot upperRoot value : Nat)
    (hRoute : lowerRoot < value) :
    LeanExperiments.RunningMedian.insert
        { lower := #[lowerRoot], upper := #[upperRoot] } value =
      if value < upperRoot then
        { lower := LeanExperiments.RunningMedian.insertHeap
            LeanExperiments.RunningMedian.maxPrefer #[lowerRoot] value,
          upper := #[upperRoot] }
      else
        { lower := LeanExperiments.RunningMedian.insertHeap
            LeanExperiments.RunningMedian.maxPrefer #[lowerRoot] upperRoot,
          upper := #[value] } := by
  have hNotRoute : ¬ value ≤ lowerRoot := by omega
  by_cases hValueUpper : value < upperRoot
  · have hUpperInsert : LeanExperiments.RunningMedian.insertHeap
        LeanExperiments.RunningMedian.minPrefer #[upperRoot] value = #[value, upperRoot] :=
      insertHeap_minPrefer_singleton_of_gt hValueUpper
    have hLowerBalanced := rebalanceLower_eq_self_of_size_le
      #[lowerRoot] #[value, upperRoot] (by simp)
    simp [LeanExperiments.RunningMedian.insert, hNotRoute, hValueUpper,
      hUpperInsert, hLowerBalanced, rebalanceUpper_singleton_pair]
  · have hUpperValue : upperRoot ≤ value := by omega
    have hUpperInsert : LeanExperiments.RunningMedian.insertHeap
        LeanExperiments.RunningMedian.minPrefer #[upperRoot] value = #[upperRoot, value] := by
      apply insertHeap_eq_push_of_stops
      right
      simp [LeanExperiments.RunningMedian.minPrefer, hUpperValue]
    have hLowerBalanced := rebalanceLower_eq_self_of_size_le
      #[lowerRoot] #[upperRoot, value] (by simp)
    simp [LeanExperiments.RunningMedian.insert, hNotRoute, hValueUpper,
      hUpperInsert, hLowerBalanced, rebalanceUpper_singleton_pair]

/-- 下側からの再平衡は、取り出しと反対側への挿入を通して合計サイズを保つ。 -/
theorem rebalanceLower_total_size (lower upper : Array Nat) :
    let result := LeanExperiments.RunningMedian.rebalanceLower lower upper
    result.1.size + result.2.size = lower.size + upper.size := by
  change (LeanExperiments.RunningMedian.rebalanceLower lower upper).1.size +
      (LeanExperiments.RunningMedian.rebalanceLower lower upper).2.size =
    lower.size + upper.size
  generalize hRun : LeanExperiments.RunningMedian.rebalanceLower lower upper = result
  unfold LeanExperiments.RunningMedian.rebalanceLower at hRun
  apply Id.of_run_eq_wp hRun
  vcgen [LeanExperiments.RunningMedian.rebalanceLower] invariants
  case inv1 => exact fun _ heaps =>
    heaps.1.size + heaps.2.size = lower.size + upper.size
  case vc1 => simp
  case vc2 => simp_all
  case vc3 =>
    simp_all [LeanExperiments.RunningMedian.transferLowerRoot,
      Variant.evalsBelow_ofMeasure_nat, Variant.evalsTo_ofMeasure,
      Assertion.NondetFun.evalsTo_pure]
    rcases ‹_ ∧ _› with ⟨hMeasure, hTotalSize⟩
    have hMoveSize := transferLowerRoot_size (by assumption)
    rcases hMoveSize with ⟨hLowerSize, hUpperSize⟩
    constructor
    · omega
    · omega
  case vc4 =>
    simp_all [Variant.evalsTo_ofMeasure, Assertion.NondetFun.evalsTo_pure]
    rcases ‹_ ∧ _› with ⟨hMeasure, hTotalSize⟩
    omega
  case vc5 =>
    simp_all
    rcases ‹_ ∧ _› with ⟨hMeasure, hTotalSize⟩
    omega

/-- 下側からの再平衡後は、下側の要素数が上側を2つ以上上回らない。 -/
theorem rebalanceLower_size_bound (lower upper : Array Nat) :
    let result := LeanExperiments.RunningMedian.rebalanceLower lower upper
    result.1.size ≤ result.2.size + 1 := by
  change (LeanExperiments.RunningMedian.rebalanceLower lower upper).1.size ≤
    (LeanExperiments.RunningMedian.rebalanceLower lower upper).2.size + 1
  generalize hRun : LeanExperiments.RunningMedian.rebalanceLower lower upper = result
  unfold LeanExperiments.RunningMedian.rebalanceLower at hRun
  apply Id.of_run_eq_wp hRun
  vcgen [LeanExperiments.RunningMedian.rebalanceLower] invariants
  case inv1 => exact fun exit heaps =>
    if exit then heaps.1.size ≤ heaps.2.size + 1
    else heaps.1.size + heaps.2.size = lower.size + upper.size
  case vc1 => simp
  case vc2 => simp_all
  case vc3 =>
    simp_all [LeanExperiments.RunningMedian.transferLowerRoot,
      Variant.evalsBelow_ofMeasure_nat, Variant.evalsTo_ofMeasure,
      Assertion.NondetFun.evalsTo_pure]
    rcases ‹_ ∧ _› with ⟨hMeasure, hTotalSize⟩
    have hMoveSize := transferLowerRoot_size (by assumption)
    rcases hMoveSize with ⟨hLowerSize, hUpperSize⟩
    constructor
    · omega
    · omega
  case vc4 =>
    simp_all [Variant.evalsTo_ofMeasure, Assertion.NondetFun.evalsTo_pure]
    rename_i currentLower currentUpper measure opt noSome guard inv transition
    have hOptNone : opt = none := by
      cases hOption : opt with
      | none => rfl
      | some pair =>
          rcases pair with ⟨nextLower, nextUpper⟩
          exact False.elim (inv nextLower nextUpper hOption)
    have hEmpty := (transferLowerRoot_eq_none_iff_empty
      LeanExperiments.RunningMedian.maxPrefer LeanExperiments.RunningMedian.minPrefer
      currentLower currentUpper).mp (by rw [transition, hOptNone])
    have hMeasured : currentLower.size = measure := noSome.1
    omega
  case vc5 => simp_all

/-- 上側からの再平衡も、取り出しと反対側への挿入を通して合計サイズを保つ。 -/
theorem rebalanceUpper_total_size (lower upper : Array Nat) :
    let result := LeanExperiments.RunningMedian.rebalanceUpper lower upper
    result.1.size + result.2.size = lower.size + upper.size := by
  change (LeanExperiments.RunningMedian.rebalanceUpper lower upper).1.size +
      (LeanExperiments.RunningMedian.rebalanceUpper lower upper).2.size =
    lower.size + upper.size
  generalize hRun : LeanExperiments.RunningMedian.rebalanceUpper lower upper = result
  unfold LeanExperiments.RunningMedian.rebalanceUpper at hRun
  apply Id.of_run_eq_wp hRun
  vcgen [LeanExperiments.RunningMedian.rebalanceUpper] invariants
  case inv1 => exact fun _ heaps =>
    heaps.1.size + heaps.2.size = lower.size + upper.size
  case vc1 => simp
  case vc2 => simp_all
  case vc3 =>
    simp_all [LeanExperiments.RunningMedian.transferUpperRoot,
      Variant.evalsBelow_ofMeasure_nat, Variant.evalsTo_ofMeasure,
      Assertion.NondetFun.evalsTo_pure]
    rcases ‹_ ∧ _› with ⟨hMeasure, hTotalSize⟩
    have hMoveSize := transferUpperRoot_size (by assumption)
    rcases hMoveSize with ⟨hLowerSize, hUpperSize⟩
    constructor
    · omega
    · omega
  case vc4 =>
    simp_all [Variant.evalsTo_ofMeasure, Assertion.NondetFun.evalsTo_pure]
    rcases ‹_ ∧ _› with ⟨hMeasure, hTotalSize⟩
    omega
  case vc5 =>
    simp_all
    rcases ‹_ ∧ _› with ⟨hMeasure, hTotalSize⟩
    omega

/-- 上側からの再平衡後は、上側の要素数が下側を2つ以上上回らない。 -/
theorem rebalanceUpper_size_bound (lower upper : Array Nat) :
    let result := LeanExperiments.RunningMedian.rebalanceUpper lower upper
    result.2.size ≤ result.1.size + 1 := by
  change (LeanExperiments.RunningMedian.rebalanceUpper lower upper).2.size ≤
    (LeanExperiments.RunningMedian.rebalanceUpper lower upper).1.size + 1
  generalize hRun : LeanExperiments.RunningMedian.rebalanceUpper lower upper = result
  unfold LeanExperiments.RunningMedian.rebalanceUpper at hRun
  apply Id.of_run_eq_wp hRun
  vcgen [LeanExperiments.RunningMedian.rebalanceUpper] invariants
  case inv1 => exact fun exit heaps =>
    if exit then heaps.2.size ≤ heaps.1.size + 1
    else heaps.1.size + heaps.2.size = lower.size + upper.size
  case vc1 => simp
  case vc2 => simp_all
  case vc3 =>
    simp_all [LeanExperiments.RunningMedian.transferUpperRoot,
      Variant.evalsBelow_ofMeasure_nat, Variant.evalsTo_ofMeasure,
      Assertion.NondetFun.evalsTo_pure]
    rcases ‹_ ∧ _› with ⟨hMeasure, hTotalSize⟩
    have hMoveSize := transferUpperRoot_size (by assumption)
    rcases hMoveSize with ⟨hLowerSize, hUpperSize⟩
    constructor
    · omega
    · omega
  case vc4 =>
    simp_all [Variant.evalsTo_ofMeasure, Assertion.NondetFun.evalsTo_pure]
    rename_i currentLower currentUpper measure opt noSome guard inv transition
    have hOptNone : opt = none := by
      cases hOption : opt with
      | none => rfl
      | some pair =>
          rcases pair with ⟨nextLower, nextUpper⟩
          exact False.elim (inv nextLower nextUpper hOption)
    have hEmpty := (transferUpperRoot_eq_none_iff_empty
      LeanExperiments.RunningMedian.minPrefer LeanExperiments.RunningMedian.maxPrefer
      currentLower currentUpper).mp (by rw [transition, hOptNone])
    have hMeasured : currentUpper.size = measure := noSome.1
    omega
  case vc5 =>
    simp_all
    omega

/-- 上下の再平衡を続けて適用しても、入力全体の要素数を保つ。 -/
theorem rebalanceBoth_total_size (lower upper : Array Nat) :
    let lowerResult := LeanExperiments.RunningMedian.rebalanceLower lower upper
    let result := LeanExperiments.RunningMedian.rebalanceUpper
      lowerResult.1 lowerResult.2
    result.1.size + result.2.size = lower.size + upper.size := by
  have hLower := rebalanceLower_total_size lower upper
  have hUpper := rebalanceUpper_total_size
    (LeanExperiments.RunningMedian.rebalanceLower lower upper).1
    (LeanExperiments.RunningMedian.rebalanceLower lower upper).2
  simpa only [hLower] using hUpper

/-- 下側・上側の再平衡を続けると、2つのヒープのサイズ差は1以内になる。 -/
theorem rebalanceBoth_size_balanced (lower upper : Array Nat) :
    let lowerResult := LeanExperiments.RunningMedian.rebalanceLower lower upper
    let result := LeanExperiments.RunningMedian.rebalanceUpper lowerResult.1 lowerResult.2
    result.1.size ≤ result.2.size + 1 ∧ result.2.size ≤ result.1.size := by
  change
    (LeanExperiments.RunningMedian.rebalanceUpper
      (LeanExperiments.RunningMedian.rebalanceLower lower upper).1
      (LeanExperiments.RunningMedian.rebalanceLower lower upper).2).1.size ≤
        (LeanExperiments.RunningMedian.rebalanceUpper
          (LeanExperiments.RunningMedian.rebalanceLower lower upper).1
          (LeanExperiments.RunningMedian.rebalanceLower lower upper).2).2.size + 1 ∧
    (LeanExperiments.RunningMedian.rebalanceUpper
      (LeanExperiments.RunningMedian.rebalanceLower lower upper).1
      (LeanExperiments.RunningMedian.rebalanceLower lower upper).2).2.size ≤
        (LeanExperiments.RunningMedian.rebalanceUpper
          (LeanExperiments.RunningMedian.rebalanceLower lower upper).1
          (LeanExperiments.RunningMedian.rebalanceLower lower upper).2).1.size
  let initialLower := (LeanExperiments.RunningMedian.rebalanceLower lower upper).1
  let initialUpper := (LeanExperiments.RunningMedian.rebalanceLower lower upper).2
  have hLowerBound : initialLower.size ≤ initialUpper.size + 1 := by
    exact rebalanceLower_size_bound lower upper
  generalize hRun : LeanExperiments.RunningMedian.rebalanceUpper initialLower initialUpper = result
  unfold LeanExperiments.RunningMedian.rebalanceUpper at hRun
  apply Id.of_run_eq_wp hRun
  vcgen [LeanExperiments.RunningMedian.rebalanceUpper] invariants
  case inv1 => exact fun exit heaps =>
    if exit then heaps.1.size ≤ heaps.2.size + 1 ∧ heaps.2.size ≤ heaps.1.size
    else heaps.1.size + heaps.2.size = initialLower.size + initialUpper.size ∧
      heaps.1.size ≤ heaps.2.size + 1
  case vc1 => simp [initialLower, initialUpper, hLowerBound]
  case vc2 => simp_all
  case vc3 =>
    simp_all [LeanExperiments.RunningMedian.transferUpperRoot,
      Variant.evalsBelow_ofMeasure_nat, Variant.evalsTo_ofMeasure,
      Assertion.NondetFun.evalsTo_pure]
    rcases ‹_ ∧ _› with ⟨hMeasure, hInvariant⟩
    rcases hInvariant with ⟨hTotal, hLowerBound⟩
    have hMoveSize := transferUpperRoot_size (by assumption)
    rcases hMoveSize with ⟨hLowerSize, hUpperSize⟩
    all_goals omega
  case vc4 =>
    simp_all [Variant.evalsTo_ofMeasure, Assertion.NondetFun.evalsTo_pure]
    rename_i currentLower currentUpper measure opt noSome guard inv transition
    have hOptNone : opt = none := by
      cases hOption : opt with
      | none => rfl
      | some pair =>
          rcases pair with ⟨nextLower, nextUpper⟩
          exact False.elim (inv nextLower nextUpper hOption)
    have hEmpty := (transferUpperRoot_eq_none_iff_empty
      LeanExperiments.RunningMedian.minPrefer LeanExperiments.RunningMedian.maxPrefer
      currentLower currentUpper).mp (by rw [transition, hOptNone])
    have hMeasured : currentUpper.size = measure := noSome.1
    omega
  case vc5 => simp_all <;> omega

/-- 上下の再平衡後、下側は全要素数の切り上げ半分、上側は切り捨て半分を持つ。 -/
theorem rebalanceBoth_heap_sizes (lower upper : Array Nat) :
    let lowerResult := LeanExperiments.RunningMedian.rebalanceLower lower upper
    let result := LeanExperiments.RunningMedian.rebalanceUpper lowerResult.1 lowerResult.2
    result.1.size = (lower.size + upper.size + 1) / 2 ∧
      result.2.size = (lower.size + upper.size) / 2 := by
  have hTotal := rebalanceBoth_total_size lower upper
  have hBalanced := rebalanceBoth_size_balanced lower upper
  dsimp at hTotal hBalanced ⊢
  omega

/-- `popHeap` が返す値は、入力配列の根である。 -/
theorem popHeap_value_eq_root {prefer : Nat → Nat → Bool} {heap : Array Nat}
    {root : Nat} {rest : Array Nat}
    (hPop : LeanExperiments.RunningMedian.popHeap prefer heap = some (root, rest)) :
    heap[0]? = some root := by
  unfold LeanExperiments.RunningMedian.popHeap at hPop
  cases hRoot : heap[0]? with
  | none => simp [hRoot] at hPop
  | some actualRoot =>
      cases hBack : heap.back? with
      | none => simp [hRoot, hBack] at hPop
      | some last =>
          by_cases hEmpty : heap.pop.isEmpty
          · simp [hRoot, hBack, hEmpty] at hPop
            rw [← hPop.1]
          · simp [hRoot, hBack, hEmpty] at hPop
            rw [← hPop.1]

/-- 取り出した根と残余を合わせると、任意の Boolean 分類の個数が保存される。 -/
theorem popHeap_countP {prefer : Nat → Nat → Bool} {heap : Array Nat}
    {root : Nat} {rest : Array Nat}
    (hPop : LeanExperiments.RunningMedian.popHeap prefer heap = some (root, rest))
    (predicate : Nat → Bool) :
    (root :: rest.toList).countP predicate = heap.toList.countP predicate := by
  have hRestPerm := popHeap_perm_dropRoot hPop
  have hRoot := popHeap_value_eq_root hPop
  have hListRoot : heap.toList[0]? = some root := by
    rw [Array.getElem?_toList]
    exact hRoot
  have hHeadLt : 0 < heap.toList.length :=
    (List.getElem?_eq_some_iff.mp hListRoot).1
  have hHeadValue : heap.toList[0] = root :=
    (List.getElem?_eq_some_iff.mp hListRoot).2
  have hDecomp : root :: heap.toList.drop 1 = heap.toList := by
    have hListDecomp := List.getElem_cons_drop (as := heap.toList) (i := 0) hHeadLt
    simpa [hHeadValue] using hListDecomp
  have hElementsPerm : (root :: rest.toList).Perm heap.toList := by
    have hPerm := List.Perm.cons root hRestPerm
    rw [hDecomp] at hPerm
    exact hPerm
  exact hElementsPerm.countP_eq predicate

/-- 推移的なヒープ優先関係では、根は全ての要素に対して優先されない。 -/
theorem HeapOrdered.preferred_to_root (prefer : Nat → Nat → Bool)
    (heap : Array Nat)
    (hReflexive : ∀ value, prefer value value = false)
    (hTransitive : ∀ first second third,
      prefer first second = false → prefer second third = false →
        prefer first third = false)
    (hOrdered : HeapOrdered prefer heap) :
    ∀ index, index < heap.size → prefer heap[index]! heap[0]! = false := by
  intro index
  induction index using Nat.strongRecOn with
  | ind index ih =>
    intro hIndex
    by_cases hRoot : index = 0
    · subst index
      exact hReflexive heap[0]!
    · let parent := (index - 1) / 2
      have hParentLt : parent < index := by dsimp [parent]; omega
      have hParentBound : parent < heap.size := Nat.lt_trans hParentLt hIndex
      have hChildIndex : index = 2 * parent + 1 ∨ index = 2 * parent + 2 := by
        dsimp [parent]
        omega
      have hParentToRoot := ih parent hParentLt hParentBound
      rcases hChildIndex with hLeftIndex | hRightIndex
      · have hChildBound : 2 * parent + 1 < heap.size := by omega
        have hEdge := (hOrdered parent hParentBound).1 hChildBound
        have hEdgeAtIndex : prefer heap[index]! heap[parent]! = false := by
          simpa [hLeftIndex] using hEdge
        exact hTransitive heap[index]! heap[parent]! heap[0]!
          hEdgeAtIndex hParentToRoot
      · have hChildBound : 2 * parent + 2 < heap.size := by omega
        have hEdge := (hOrdered parent hParentBound).2 hChildBound
        have hEdgeAtIndex : prefer heap[index]! heap[parent]! = false := by
          simpa [hRightIndex] using hEdge
        exact hTransitive heap[index]! heap[parent]! heap[0]!
          hEdgeAtIndex hParentToRoot

/-- 推移的優先関係のヒープから取り出す値は、入力の全要素以上に優先される。 -/
theorem popHeap_returns_preferred_to_all {prefer : Nat → Nat → Bool}
    {heap : Array Nat} {root : Nat} {rest : Array Nat}
    (hReflexive : ∀ value, prefer value value = false)
    (hTransitive : ∀ first second third,
      prefer first second = false → prefer second third = false →
        prefer first third = false)
    (hHeap : HeapOrdered prefer heap)
    (hPop : LeanExperiments.RunningMedian.popHeap prefer heap = some (root, rest)) :
    ∀ index, index < heap.size → prefer heap[index]! root = false := by
  have hRoot := popHeap_value_eq_root hPop
  have hPositive : 0 < heap.size := (Array.getElem?_eq_some_iff.mp hRoot).1
  have hRootValue : heap[0]! = root := by
    rw [getElem?_pos heap 0 hPositive] at hRoot
    have hValue := Option.some.inj hRoot
    rw [getElem!_pos heap 0 hPositive]
    exact hValue
  intro index hIndex
  rw [← hRootValue]
  exact HeapOrdered.preferred_to_root prefer heap hReflexive hTransitive
    hHeap index hIndex

/-- 最大ヒープの根は、配列内の全ての値以上である。 -/
theorem maxHeap_root_is_maximum (heap : Array Nat)
    (hOrdered : HeapOrdered maxPrefer heap) (index : Nat)
    (hIndex : index < heap.size) : heap[index]! ≤ heap[0]! := by
  have hReflexive : ∀ value, maxPrefer value value = false := by
    intro value
    exact maxPrefer_irrefl value
  have hTransitive : ∀ first second third,
      maxPrefer first second = false → maxPrefer second third = false →
        maxPrefer first third = false := by
    intro first second third hFirst hSecond
    exact maxPrefer_not_transitive hFirst hSecond
  have hRoot := HeapOrdered.preferred_to_root
    maxPrefer heap hReflexive hTransitive hOrdered index hIndex
  simp [maxPrefer] at hRoot
  omega

/-- 最小ヒープの根は、配列内の全ての値以下である。 -/
theorem minHeap_root_is_minimum (heap : Array Nat)
    (hOrdered : HeapOrdered minPrefer heap) (index : Nat)
    (hIndex : index < heap.size) : heap[0]! ≤ heap[index]! := by
  have hReflexive : ∀ value, minPrefer value value = false := by
    intro value
    exact minPrefer_irrefl value
  have hTransitive : ∀ first second third,
      minPrefer first second = false → minPrefer second third = false →
        minPrefer first third = false := by
    intro first second third hFirst hSecond
    exact minPrefer_not_transitive hFirst hSecond
  have hRoot := HeapOrdered.preferred_to_root
    minPrefer heap hReflexive hTransitive hOrdered index hIndex
  simp [minPrefer] at hRoot
  omega

/-- ヒープ順序があれば、全要素間の境界条件は根同士の比較で特徴付けられる。 -/
theorem crossBoundary_iff_rootBoundary
    (state : LeanExperiments.RunningMedian.State)
    (hLower : HeapOrdered maxPrefer state.lower)
    (hUpper : HeapOrdered minPrefer state.upper) :
    (∀ lowerIndex (hLowerIndex : lowerIndex < state.lower.size),
      ∀ upperIndex (hUpperIndex : upperIndex < state.upper.size),
        state.lower[lowerIndex]'hLowerIndex ≤ state.upper[upperIndex]'hUpperIndex) ↔
      (state.lower.size = 0 ∨ state.upper.size = 0 ∨
        state.lower[0]! ≤ state.upper[0]!) := by
  constructor
  · intro hCross
    by_cases hLowerNonempty : 0 < state.lower.size
    · by_cases hUpperNonempty : 0 < state.upper.size
      · right
        right
        simpa only [getElem!_pos state.lower 0 hLowerNonempty,
          getElem!_pos state.upper 0 hUpperNonempty] using
          (hCross 0 hLowerNonempty 0 hUpperNonempty)
      · right
        left
        omega
    · left
      omega
  · intro hBoundary lowerIndex hLowerIndex upperIndex hUpperIndex
    rcases hBoundary with hLowerEmpty | hUpperEmpty | hRoots
    · omega
    · omega
    · have hLowerRoot := maxHeap_root_is_maximum
        state.lower hLower lowerIndex hLowerIndex
      have hUpperRoot := minHeap_root_is_minimum
        state.upper hUpper upperIndex hUpperIndex
      simpa only [getElem!_pos state.lower lowerIndex hLowerIndex,
        getElem!_pos state.upper upperIndex hUpperIndex] using
        (show state.lower[lowerIndex]! ≤ state.upper[upperIndex]! by omega)

/-- 数値的な最小ヒープ仕様から、根が全要素以下であることを導く。 -/
theorem MinHeap.root_is_minimum (heap : Array Nat)
    (hMinHeap : MinHeap heap) (index : Nat)
    (hIndex : index < heap.size) : heap[0]! ≤ heap[index]! := by
  exact hMinHeap.ancestor_le_descendant
    (LeanExperiments.Verification.HeapSort.Spec.HeapDescendant.zero_ancestor index) hIndex

/-- 最小ヒープからの取り出し値は、入力ヒープの全要素以下である。 -/
theorem popHeap_minPrefer_returns_minimum {heap : Array Nat}
    (hHeap : HeapOrdered minPrefer heap) {root : Nat} {rest : Array Nat}
    (hPop : LeanExperiments.RunningMedian.popHeap minPrefer heap = some (root, rest)) :
    ∀ index, index < heap.size → root ≤ heap[index]! := by
  have hRoot := popHeap_value_eq_root hPop
  have hPositive : 0 < heap.size := (Array.getElem?_eq_some_iff.mp hRoot).1
  have hRootValue : heap[0]! = root := by
    rw [getElem?_pos heap 0 hPositive] at hRoot
    have hValue := Option.some.inj hRoot
    rw [getElem!_pos heap 0 hPositive]
    exact hValue
  intro index hIndex
  rw [← hRootValue]
  exact minHeap_root_is_minimum heap hHeap index hIndex

/-- 数値的な最小ヒープ仕様の下では、取り出した根が入力の最小値である。 -/
theorem popHeap_minPrefer_returns_minimum_of_MinHeap {heap : Array Nat}
    (hHeap : MinHeap heap) {root : Nat} {rest : Array Nat}
    (hPop : LeanExperiments.RunningMedian.popHeap minPrefer heap = some (root, rest)) :
    ∀ index, index < heap.size → root ≤ heap[index]! := by
  exact popHeap_minPrefer_returns_minimum
    ((minHeap_iff_HeapOrdered_minPrefer heap).mp hHeap) hPop

/-- 最小ヒープからの取り出しは、最小値・残余要素・長さの契約を満たす。 -/
theorem popHeap_minPrefer_contract_of_MinHeap {heap : Array Nat}
    (hHeap : MinHeap heap) {root : Nat} {rest : Array Nat}
    (hPop : LeanExperiments.RunningMedian.popHeap minPrefer heap = some (root, rest)) :
    (∀ index, index < heap.size → root ≤ heap[index]!) ∧
      rest.toList.Perm (heap.toList.drop 1) ∧ rest.size + 1 = heap.size := by
  exact ⟨popHeap_minPrefer_returns_minimum_of_MinHeap hHeap hPop,
    popHeap_perm_dropRoot hPop, popHeap_size hPop⟩

/-- 根を末尾要素で置換した配列が既に最小ヒープなら、取り出し後の残余も最小ヒープである。
これは置換配列に対する `siftDown` の一般的なヒープ順序保存を必要条件付きで切り出す。 -/
theorem popHeap_minPrefer_restMinHeap_of_replacementMinHeap
    {heap rest : Array Nat} {root : Nat}
    (hPop : LeanExperiments.RunningMedian.popHeap minPrefer heap = some (root, rest))
    (hReplacement : MinHeap (heap.pop.set! 0 heap.back!)) : MinHeap rest := by
  unfold LeanExperiments.RunningMedian.popHeap at hPop
  cases hRoot : heap[0]? with
  | none => simp [hRoot] at hPop
  | some actualRoot =>
      cases hBack : heap.back? with
      | none => simp [hRoot, hBack] at hPop
      | some last =>
          by_cases hEmpty : heap.pop.isEmpty
          · simp [hRoot, hBack, hEmpty] at hPop
            have hRest : rest = heap.pop := by simpa using hPop.2.symm
            rw [hRest]
            have hPopEmpty : heap.pop = #[] := by simpa using hEmpty
            simp [MinHeap, hPopEmpty]
          · simp [hRoot, hBack, hEmpty] at hPop
            have hPopNonempty : 0 < heap.pop.size :=
              Array.size_pos_iff.mpr (by simpa using hEmpty)
            have hLast : heap.back! = last := by
              rw [Array.back!_eq_back?]
              simp [hBack]
            have hReplacementOrdered :
                HeapOrdered minPrefer (heap.pop.setIfInBounds 0 last) := by
              have hOrdered :=
                (minHeap_iff_HeapOrdered_minPrefer _).mp hReplacement
              simpa [hLast] using hOrdered
            have hSift :
                LeanExperiments.RunningMedian.siftDown minPrefer
                  (heap.pop.setIfInBounds 0 last) 0 = heap.pop.setIfInBounds 0 last :=
              siftDown_eq_self_of_heapOrdered minPrefer
                (heap.pop.setIfInBounds 0 last) 0
                (by simpa using hPopNonempty) hReplacementOrdered
            rw [← hPop.2, hSift]
            simpa [hLast] using hReplacement

/-- 最小ヒープからの取り出し後も、残余配列は最小ヒープである。 -/
theorem popHeap_minPrefer_restMinHeap_of_MinHeap
    {heap rest : Array Nat} {root : Nat}
    (hHeap : MinHeap heap)
    (hPop : LeanExperiments.RunningMedian.popHeap minPrefer heap = some (root, rest)) :
    MinHeap rest := by
  unfold LeanExperiments.RunningMedian.popHeap at hPop
  cases hRoot : heap[0]? with
  | none => simp [hRoot] at hPop
  | some actualRoot =>
      cases hBack : heap.back? with
      | none => simp [hRoot, hBack] at hPop
      | some last =>
          by_cases hEmpty : heap.pop.isEmpty
          · simp [hRoot, hBack, hEmpty] at hPop
            have hRest : rest = heap.pop := by simpa using hPop.2.symm
            rw [hRest]
            have hPopEmpty : heap.pop = #[] := by simpa using hEmpty
            simp [MinHeap, hPopEmpty]
          · simp [hRoot, hBack, hEmpty] at hPop
            have hLast : heap.back! = last := by
              rw [Array.back!_eq_back?]
              simp [hBack]
            have hBelowRoot := minHeap_pop_set_root_preserves_below_root hHeap last
            have hSiftMinHeap :
                MinHeap (LeanExperiments.RunningMedian.siftDown minPrefer
                  (heap.pop.setIfInBounds 0 last) 0) := by
              apply siftDown_minPrefer_MinHeap_of_belowRoot
              intro parent hParentPositive hParent
              have hParent' : parent < (heap.pop.set! 0 last).size := by
                simpa [Array.set!_eq_setIfInBounds] using hParent
              have hRows := hBelowRoot parent hParentPositive hParent'
              simpa [Array.set!_eq_setIfInBounds] using hRows
            rw [← hPop.2]
            simpa [hLast, Array.set!_eq_setIfInBounds] using hSiftMinHeap

/-- 置換後配列が最小ヒープである条件の下で、最小値・残余ヒープ・要素保存・長さをまとめた取り出し契約。 -/
theorem popHeap_minPrefer_fullContract_of_replacementMinHeap
    {heap rest : Array Nat} {root : Nat}
    (hHeap : MinHeap heap)
    (hPop : LeanExperiments.RunningMedian.popHeap minPrefer heap = some (root, rest))
    (hReplacement : MinHeap (heap.pop.set! 0 heap.back!)) :
    (∀ index, index < heap.size → root ≤ heap[index]!) ∧
      MinHeap rest ∧ rest.toList.Perm (heap.toList.drop 1) ∧
      rest.size + 1 = heap.size := by
  rcases popHeap_minPrefer_contract_of_MinHeap hHeap hPop with
    ⟨hMinimum, hPermutation, hSize⟩
  exact ⟨hMinimum,
    popHeap_minPrefer_restMinHeap_of_replacementMinHeap hPop hReplacement,
    hPermutation, hSize⟩

/-- 最小ヒープからの取り出しは、最小値・残余ヒープ・要素保存・長さの契約を満たす。 -/
theorem popHeap_minPrefer_fullContract_of_MinHeap
    {heap rest : Array Nat} {root : Nat}
    (hHeap : MinHeap heap)
    (hPop : LeanExperiments.RunningMedian.popHeap minPrefer heap = some (root, rest)) :
    (∀ index, index < heap.size → root ≤ heap[index]!) ∧
      MinHeap rest ∧ rest.toList.Perm (heap.toList.drop 1) ∧
      rest.size + 1 = heap.size := by
  rcases popHeap_minPrefer_contract_of_MinHeap hHeap hPop with
    ⟨hMinimum, hPermutation, hSize⟩
  exact ⟨hMinimum, popHeap_minPrefer_restMinHeap_of_MinHeap hHeap hPop,
    hPermutation, hSize⟩

/-- 下側が一つ多い状態では、中央値は最大ヒープの根を分母1で返す。 -/
theorem median_of_odd_size (state : LeanExperiments.RunningMedian.State)
    (hSize : state.lower.size = state.upper.size + 1) :
    LeanExperiments.RunningMedian.median state =
      some (state.lower[0]'(by omega), 1) := by
  unfold LeanExperiments.RunningMedian.median
  rw [ite_eq_left (by omega)]
  rw [Array.getElem?_eq_getElem (by omega)]
  rfl

/-- 同じ要素数で上側も空でなければ、中央値は両ヒープの根の平均を返す。 -/
theorem median_of_even_size (state : LeanExperiments.RunningMedian.State)
    (hSize : state.lower.size = state.upper.size)
    (hUpper : 0 < state.upper.size) :
    LeanExperiments.RunningMedian.median state =
      some (state.lower[0]'(by omega) + state.upper[0]'hUpper, 2) := by
  unfold LeanExperiments.RunningMedian.median
  rw [ite_eq_right (by omega)]
  rw [Array.getElem?_eq_getElem (by omega), Array.getElem?_eq_getElem hUpper]


end LeanExperiments.Verification.RunningMedian
