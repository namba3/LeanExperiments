import LeanExperiments.RunningMedian
import LeanExperiments.HeapSort
import LeanExperiments.Verification.MergeSort.Spec
import LeanExperiments.Verification.HeapSort.Spec
import Std.WP
import Std.Tactic.Do

/-!
# 逐次中央値の仕様と有限領域検証

二つのヒープが保つ分割・順序・要素保存の条件を判定し、各入力の全ての接頭辞で
中央値を独立なソート基準と照合する。ここでの網羅確認は明示した有限領域に限られ、
任意の入力列に対する一般的な正しさ証明とは区別する。
-/

namespace LeanExperiments.Verification.RunningMedian

open Std.WP Lean.Order
set_option experimental.vcgen true

/-- 有効範囲内の2添字の交換は、配列の要素を順列として保つ。 -/
theorem swap_perm (heap : Array Nat) (left right : Nat)
    (hLeft : left < heap.size) (hRight : right < heap.size) :
    (LeanExperiments.RunningMedian.swap heap left right).toList.Perm heap.toList := by
  have hSwap : LeanExperiments.RunningMedian.swap heap left right = heap.swap left right := by
    simp [LeanExperiments.RunningMedian.swap, Array.swap, Array.setIfInBounds,
      hLeft, hRight]
  rw [hSwap]
  exact Array.perm_iff_toList_perm.mp (Array.swap_perm hLeft hRight)

/-- 有効範囲内の交換は、交換位置以外の要素を変えない。 -/
theorem swap_getElem!_eq_of_outside (heap : Array Nat) (left right position : Nat)
    (hLeft : left < heap.size) (hRight : right < heap.size)
    (hPosition : position < heap.size)
    (hNotLeft : position ≠ left) (hNotRight : position ≠ right) :
    (LeanExperiments.RunningMedian.swap heap left right)[position]! = heap[position]! := by
  have hSwap : LeanExperiments.RunningMedian.swap heap left right =
      heap.swap left right := by
    simp [LeanExperiments.RunningMedian.swap, Array.swap, Array.setIfInBounds,
      hLeft, hRight]
  rw [hSwap]
  rw [getElem!_pos _ position (by simpa using hPosition), getElem!_pos heap position hPosition]
  exact Array.getElem_swap_of_ne hNotLeft hNotRight

/-- 有効範囲内の交換後、左位置と右位置には互いの旧値が入る。 -/
theorem swap_getElem!_at_positions (heap : Array Nat) (left right : Nat)
    (hLeft : left < heap.size) (hRight : right < heap.size) :
    (LeanExperiments.RunningMedian.swap heap left right)[left]! = heap[right]! ∧
      (LeanExperiments.RunningMedian.swap heap left right)[right]! = heap[left]! := by
  have hSwap : LeanExperiments.RunningMedian.swap heap left right =
      heap.swap left right := by
    simp [LeanExperiments.RunningMedian.swap, Array.swap, Array.setIfInBounds,
      hLeft, hRight]
  constructor
  · rw [hSwap]
    rw [getElem!_pos (heap.swap left right) left (by simpa using hLeft)]
    rw [Array.getElem_swap hLeft hRight (by simpa using hLeft)]
    simp [getElem!_pos heap right hRight]
  · by_cases hEq : left = right
    · subst right
      rw [hSwap]
      rw [getElem!_pos (heap.swap left left) left (by simpa using hLeft)]
      rw [Array.getElem_swap hLeft hLeft (by simpa using hLeft)]
      simp [getElem!_pos heap left hLeft]
    · rw [hSwap]
      rw [getElem!_pos (heap.swap left right) right (by simpa using hRight)]
      rw [Array.getElem_swap hLeft hRight (by simpa using hRight)]
      simp [getElem!_pos heap left hLeft]
      intro hSame
      subst right
      rfl

/-- 有効な交換後の各位置は、左右端点の置換か非端点の保存で完全に記述できる。 -/
theorem swap_getElem!_eq_ite (heap : Array Nat) (left right position : Nat)
    (hLeft : left < heap.size) (hRight : right < heap.size)
    (hPosition : position < heap.size) :
    (LeanExperiments.RunningMedian.swap heap left right)[position]! =
      if position = left then heap[right]!
      else if position = right then heap[left]!
      else heap[position]! := by
  by_cases hAtLeft : position = left
  · subst position
    simp [swap_getElem!_at_positions heap left right hLeft hRight]
  · by_cases hAtRight : position = right
    · subst position
      simp [hAtLeft, swap_getElem!_at_positions heap left right hLeft hRight]
    · simp [hAtLeft, hAtRight,
        swap_getElem!_eq_of_outside heap left right position hLeft hRight
          hPosition hAtLeft hAtRight]

/-- 配列をリストにした要素順列は、元の配列長も等しくする。 -/
theorem size_eq_of_perm {left right : Array Nat}
    (hPerm : left.toList.Perm right.toList) : left.size = right.size := by
  simpa using hPerm.length_eq

/-- siftDown の1反復は配列の要素数を変えない。 -/
theorem siftDownStep_size (prefer : Nat → Nat → Bool) (heap : Array Nat)
    (index : Nat) :
    (LeanExperiments.RunningMedian.siftDownStep prefer heap index).1.size = heap.size := by
  dsimp [LeanExperiments.RunningMedian.siftDownStep]
  split <;> simp [LeanExperiments.RunningMedian.swap]

/-- 子への移動を終了した反復は、配列と現在位置をそのまま返す。 -/
theorem siftDownStep_stopped (prefer : Nat → Nat → Bool) (heap : Array Nat)
    (index : Nat)
    (hStopped : (LeanExperiments.RunningMedian.siftDownStep prefer heap index).2.2 = false) :
    (LeanExperiments.RunningMedian.siftDownStep prefer heap index).1 = heap ∧
      (LeanExperiments.RunningMedian.siftDownStep prefer heap index).2.1 = index := by
  dsimp [LeanExperiments.RunningMedian.siftDownStep] at hStopped ⊢
  by_cases hBest : LeanExperiments.RunningMedian.siftDownBest prefer heap index == index
  · simp [hBest] at hStopped ⊢
  · simp [hBest] at hStopped

/-- 子への移動を続ける反復は、選んだ子へ交換して現在位置を移す。 -/
theorem siftDownStep_running (prefer : Nat → Nat → Bool) (heap : Array Nat)
    (index : Nat)
    (hRunning : (LeanExperiments.RunningMedian.siftDownStep prefer heap index).2.2 = true) :
    (LeanExperiments.RunningMedian.siftDownStep prefer heap index).1 =
        LeanExperiments.RunningMedian.swap heap index
          (LeanExperiments.RunningMedian.siftDownBest prefer heap index) ∧
      (LeanExperiments.RunningMedian.siftDownStep prefer heap index).2.1 =
        LeanExperiments.RunningMedian.siftDownBest prefer heap index := by
  dsimp [LeanExperiments.RunningMedian.siftDownStep] at hRunning ⊢
  by_cases hBest : LeanExperiments.RunningMedian.siftDownBest prefer heap index == index
  · simp [hBest] at hRunning
  · simp [hBest] at hRunning ⊢

/-- 継続する子方向調整は、添字を増やし配列の範囲内へ移動する。 -/
theorem siftDownStep_progress (prefer : Nat → Nat → Bool) (heap : Array Nat)
    (index : Nat)
    (hRunning : (LeanExperiments.RunningMedian.siftDownStep prefer heap index).2.2 = true) :
    index < (LeanExperiments.RunningMedian.siftDownStep prefer heap index).2.1 ∧
      (LeanExperiments.RunningMedian.siftDownStep prefer heap index).2.1 < heap.size := by
  grind [LeanExperiments.RunningMedian.siftDownStep,
    LeanExperiments.RunningMedian.siftDownBest]

/-- 子方向調整の1反復は、停止時も継続時も配列要素を保存する。 -/
theorem siftDownStep_perm (prefer : Nat → Nat → Bool) (heap : Array Nat)
    (index : Nat) :
    (LeanExperiments.RunningMedian.siftDownStep prefer heap index).1.toList.Perm
      heap.toList := by
  by_cases hRunning :
      (LeanExperiments.RunningMedian.siftDownStep prefer heap index).2.2 = true
  · have hProgress := siftDownStep_progress prefer heap index hRunning
    have hStep := siftDownStep_running prefer heap index hRunning
    rw [hStep.1]
    have hBest :
        (LeanExperiments.RunningMedian.siftDownBest prefer heap index == index) = false := by
      cases hEq : (LeanExperiments.RunningMedian.siftDownBest prefer heap index == index) <;>
        simp [LeanExperiments.RunningMedian.siftDownStep, hEq] at hRunning ⊢
    have hBestBound : LeanExperiments.RunningMedian.siftDownBest prefer heap index < heap.size := by
      simpa [LeanExperiments.RunningMedian.siftDownStep, hBest] using hProgress.2
    exact swap_perm heap index (LeanExperiments.RunningMedian.siftDownBest prefer heap index)
      (by omega) hBestBound
  · have hStopped :
        (LeanExperiments.RunningMedian.siftDownStep prefer heap index).2.2 = false := by
      cases hResult : (LeanExperiments.RunningMedian.siftDownStep prefer heap index).2.2 <;>
        simp_all
    have hIdentity := siftDownStep_stopped prefer heap index hStopped
    simp [hIdentity.1]

/-- 下降1反復で交換位置以外の配列要素は変わらない。 -/
theorem siftDownStep_getElem!_eq_of_outside_swap (prefer : Nat → Nat → Bool)
    (heap : Array Nat) (index position : Nat) (hPosition : position < heap.size)
    (hNotIndex : position ≠ index)
    (hNotBest : position ≠
      LeanExperiments.RunningMedian.siftDownBest prefer heap index) :
    (LeanExperiments.RunningMedian.siftDownStep prefer heap index).1[position]! =
      heap[position]! := by
  by_cases hRunning :
      (LeanExperiments.RunningMedian.siftDownStep prefer heap index).2.2 = true
  · have hStep := siftDownStep_running prefer heap index hRunning
    have hProgress := siftDownStep_progress prefer heap index hRunning
    have hIndexBound : index < heap.size := by omega
    have hBestBound :
        LeanExperiments.RunningMedian.siftDownBest prefer heap index < heap.size := by
      rw [← hStep.2]
      exact hProgress.2
    have hSwap : LeanExperiments.RunningMedian.swap heap index
        (LeanExperiments.RunningMedian.siftDownBest prefer heap index) =
          heap.swap index (LeanExperiments.RunningMedian.siftDownBest prefer heap index) := by
      simp [LeanExperiments.RunningMedian.swap, Array.swap, Array.setIfInBounds,
        hIndexBound, hBestBound]
    rw [hStep.1, hSwap]
    have hSwapSize :
        (heap.swap index
          (LeanExperiments.RunningMedian.siftDownBest prefer heap index)).size = heap.size := by
      simp
    rw [getElem!_pos _ position (by simpa [hSwapSize] using hPosition),
      getElem!_pos heap position hPosition]
    exact Array.getElem_swap_of_ne hNotIndex hNotBest
  · have hStopped :
        (LeanExperiments.RunningMedian.siftDownStep prefer heap index).2.2 = false := by
      cases hFlag :
          (LeanExperiments.RunningMedian.siftDownStep prefer heap index).2.2 <;>
        simp_all
    have hIdentity := siftDownStep_stopped prefer heap index hStopped
    rw [hIdentity.1]

/-- 下降1反復は、現在添字より前にある処理済み配列部分を変えない。 -/
theorem siftDownStep_getElem!_eq_of_lt_index (prefer : Nat → Nat → Bool)
    (heap : Array Nat) (index position : Nat) (hPosition : position < index) :
    (LeanExperiments.RunningMedian.siftDownStep prefer heap index).1[position]! =
      heap[position]! := by
  by_cases hRunning :
      (LeanExperiments.RunningMedian.siftDownStep prefer heap index).2.2 = true
  · have hStep := siftDownStep_running prefer heap index hRunning
    have hProgress := siftDownStep_progress prefer heap index hRunning
    have hPositionBound : position < heap.size := by omega
    have hNotIndex : position ≠ index := by omega
    have hNotBest :
        position ≠ LeanExperiments.RunningMedian.siftDownBest prefer heap index := by
      intro hEq
      have hPositionEq : position =
          (LeanExperiments.RunningMedian.siftDownStep prefer heap index).2.1 := by
        rw [hStep.2]
        exact hEq
      omega
    exact siftDownStep_getElem!_eq_of_outside_swap prefer heap index position
      hPositionBound hNotIndex hNotBest
  · have hStopped :
        (LeanExperiments.RunningMedian.siftDownStep prefer heap index).2.2 = false := by
      cases hFlag :
          (LeanExperiments.RunningMedian.siftDownStep prefer heap index).2.2 <;>
        simp_all
    have hIdentity := siftDownStep_stopped prefer heap index hStopped
    rw [hIdentity.1]

/-- 継続時には `heap.size - index` が真に減少し、子方向ループの停止測度になる。 -/
theorem siftDownStep_measure_decreases (prefer : Nat → Nat → Bool) (heap : Array Nat)
    (index : Nat)
    (hRunning : (LeanExperiments.RunningMedian.siftDownStep prefer heap index).2.2 = true) :
    heap.size - (LeanExperiments.RunningMedian.siftDownStep prefer heap index).2.1 <
      heap.size - index := by
  have hProgress := siftDownStep_progress prefer heap index hRunning
  omega

/-- 最後の停止反復も含め、子方向調整の1反復で停止測度が減少する。 -/
theorem siftDownStep_variant_decreases (prefer : Nat → Nat → Bool)
    (heap : Array Nat) (index : Nat) :
    (LeanExperiments.RunningMedian.siftDownStep prefer heap index).1.size -
        (LeanExperiments.RunningMedian.siftDownStep prefer heap index).2.1 +
        (if (LeanExperiments.RunningMedian.siftDownStep prefer heap index).2.2 then 1 else 0) <
      heap.size - index + 1 := by
  by_cases hRunning :
      (LeanExperiments.RunningMedian.siftDownStep prefer heap index).2.2 = true
  · have hProgress := siftDownStep_progress prefer heap index hRunning
    have hSize := siftDownStep_size prefer heap index
    simp [hRunning] at *
    omega
  · have hStopped :
        (LeanExperiments.RunningMedian.siftDownStep prefer heap index).2.2 = false := by
      cases hResult : (LeanExperiments.RunningMedian.siftDownStep prefer heap index).2.2 <;>
        simp_all
    have hIdentity := siftDownStep_stopped prefer heap index hStopped
    rcases hIdentity with ⟨hHeap, hIndex⟩
    simp [hStopped, hHeap, hIndex]

/-- 子方向へのヒープ調整全体は、任意の初期添字でも配列長を保つ。 -/
theorem siftDown_size (prefer : Nat → Nat → Bool) (heap : Array Nat) (start : Nat) :
    (LeanExperiments.RunningMedian.siftDown prefer heap start).size = heap.size := by
  generalize hRun : LeanExperiments.RunningMedian.siftDown prefer heap start = result
  apply Id.of_run_eq_wp hRun
  vcgen [LeanExperiments.RunningMedian.siftDown] invariants
  · fun finished state => state.1.size = heap.size
  case vc1 => rfl
  case vc2 => simp_all
  case vc3 =>
    simp_all [Variant.evalsBelow_ofMeasure_nat, Variant.evalsTo_ofMeasure,
      Assertion.NondetFun.evalsTo_pure]
    rename_i currentHeap currentIndex currentFlag currentMeasure pair hInvariant hFlag
    constructor
    · have hMeasure := siftDownStep_variant_decreases prefer currentHeap currentIndex
      simpa [values, index, running, hInvariant.1] using hMeasure
    · simp [values, siftDownStep_size, hInvariant.2]
  case vc4 => simp_all [Variant.evalsTo_ofMeasure,
    Assertion.NondetFun.evalsTo_pure]

/-- 子方向へのヒープ調整全体は、任意の初期添字でも要素を保存する。 -/
theorem siftDown_perm (prefer : Nat → Nat → Bool) (heap : Array Nat) (start : Nat) :
    (LeanExperiments.RunningMedian.siftDown prefer heap start).toList.Perm heap.toList := by
  generalize hRun : LeanExperiments.RunningMedian.siftDown prefer heap start = result
  apply Id.of_run_eq_wp hRun
  vcgen [LeanExperiments.RunningMedian.siftDown] invariants
  · fun finished state => state.1.toList.Perm heap.toList
  case vc1 => exact List.Perm.refl _
  case vc2 => simp_all
  case vc3 =>
    simp_all [Variant.evalsBelow_ofMeasure_nat, Variant.evalsTo_ofMeasure,
      Assertion.NondetFun.evalsTo_pure]
    rename_i currentHeap currentIndex currentFlag currentMeasure pair hInvariant hFlag
    constructor
    · have hMeasure := siftDownStep_variant_decreases prefer currentHeap currentIndex
      simpa [values, index, running, hInvariant.1] using hMeasure
    · exact (siftDownStep_perm prefer currentHeap currentIndex).trans hInvariant.2
  case vc4 => simp_all [Variant.evalsTo_ofMeasure,
    Assertion.NondetFun.evalsTo_pure]

/-- 親方向へのヒープ調整は配列の要素数を変えない。

ループ不変条件として配列長を保ち、添字 `index` が正なら親添字が小さいことを停止測度に
使う。交換が起きても配列長は変化しない。
-/
theorem siftUp_size (prefer : Nat → Nat → Bool) (heap : Array Nat) (start : Nat) :
    (LeanExperiments.RunningMedian.siftUp prefer heap start).size = heap.size := by
  generalize hRun : LeanExperiments.RunningMedian.siftUp prefer heap start = result
  apply Id.of_run_eq_wp hRun
  vcgen [LeanExperiments.RunningMedian.siftUp] invariants
  · fun finished state => state.1.size = heap.size
  case vc1 => rfl
  case vc2 => simp_all
  case vc3 =>
    simp_all [Variant.evalsBelow_ofMeasure_nat, Variant.evalsTo_ofMeasure,
      Assertion.NondetFun.evalsTo_pure]
    constructor
    · dsimp [parent]
      omega
    · simp_all [values, LeanExperiments.RunningMedian.swap]
  case vc4 => simp_all [Variant.evalsTo_ofMeasure,
    Assertion.NondetFun.evalsTo_pure]
  case vc5 => simp_all

/-- 配列内の添字から始める親方向調整は、要素を順列として保存する。

ループ不変条件に現在添字の範囲と配列要素の順列関係を持たせる。親への交換では、
有効範囲内の交換が順列を保つことを使う。
-/
theorem siftUp_perm (prefer : Nat → Nat → Bool) (heap : Array Nat) (start : Nat)
    (hStart : start < heap.size) :
    (LeanExperiments.RunningMedian.siftUp prefer heap start).toList.Perm heap.toList := by
  generalize hRun : LeanExperiments.RunningMedian.siftUp prefer heap start = result
  apply Id.of_run_eq_wp hRun
  vcgen [LeanExperiments.RunningMedian.siftUp] invariants
  · fun finished state => state.1.toList.Perm heap.toList ∧ state.2 < heap.size
  case vc1 => exact ⟨List.Perm.refl _, hStart⟩
  case vc2 => simp_all
  case vc3 =>
    simp_all [Variant.evalsBelow_ofMeasure_nat, Variant.evalsTo_ofMeasure,
      Assertion.NondetFun.evalsTo_pure]
    constructor
    · dsimp [parent]
      omega
    · simp_all [values]
      all_goals
        rcases ‹_ ∧ _ ∧ _› with ⟨hEq, hOldPerm, hOldBound⟩
        have hSizes := size_eq_of_perm hOldPerm
        first
        | omega
        | constructor
          · exact (swap_perm _ _ _ (by omega) (by omega)).trans hOldPerm
          · dsimp [parent]
            omega
  case vc4 =>
    simp_all [Variant.evalsTo_ofMeasure, Assertion.NondetFun.evalsTo_pure]
    rcases ‹_ ∧ _ ∧ _› with ⟨hEq, hPerm, hBound⟩
    omega
  case vc5 => simp_all

/-- `siftUp` が開始添字より後ろの値を保存する一般的な局所性契約。 -/
theorem siftUp_getElem!_eq_of_gt_start (prefer : Nat → Nat → Bool)
    (heap : Array Nat) (start position : Nat)
    (hPosition : start < position) (hPositionBound : position < heap.size) :
    (LeanExperiments.RunningMedian.siftUp prefer heap start)[position]! = heap[position]! := by
  generalize hRun : LeanExperiments.RunningMedian.siftUp prefer heap start = result
  apply Id.of_run_eq_wp hRun
  vcgen [LeanExperiments.RunningMedian.siftUp] invariants
  · fun _ state => state.1.size = heap.size ∧ state.2 ≤ start ∧
      (∀ index, start < index → index < heap.size → state.1[index]! = heap[index]!)
  case vc1 => simp_all
  case vc2 =>
    simp_all
    rename_i arr curr hOuter hInv
    rcases hInv with ⟨hSize, hBound, hOutside⟩
    have h := hOutside position hPosition hPositionBound
    have hArrayBound : position < arr.size := by omega
    rw [getElem!_pos arr position hArrayBound] at h
    exact h
  case vc3 =>
    simp_all [Variant.evalsBelow_ofMeasure_nat, Variant.evalsTo_ofMeasure,
      Assertion.NondetFun.evalsTo_pure]
    rename_i arr curr idx hInv hPos hComp
    rcases hInv with ⟨hCurrentEq, hSize, hBound, hOutside⟩
    subst curr
    constructor
    · dsimp [parent]
      omega
    constructor
    · simpa [values, LeanExperiments.RunningMedian.swap] using hSize
    constructor
    · dsimp [parent]
      omega
    · intro position hAfter hPosition
      have hPositionArray : position < arr.size := by omega
      have hCurrentArray : idx < arr.size := by omega
      have hParentArray : parent < arr.size := by
        dsimp [parent]
        omega
      have hNotCurrent : position ≠ idx := by omega
      have hNotParent : position ≠ parent := by omega
      have hSwap := swap_getElem!_eq_of_outside arr idx parent position
        hCurrentArray hParentArray hPositionArray hNotCurrent hNotParent
      have hOld := hOutside position hAfter hPosition
      have hSwapped : (LeanExperiments.RunningMedian.swap arr idx parent)[position]! =
          heap[position] := hSwap.trans hOld
      dsimp [values]
      exact hSwapped
  case vc4 =>
    simp_all [Variant.evalsTo_ofMeasure, Assertion.NondetFun.evalsTo_pure]
    rename_i arr curr measure invariant hPos hNoCompare
    rcases invariant with ⟨hCurrentEq, hSize, hBound, hOutside⟩
    subst curr
    constructor
    · exact hBound
    · intro position hAfter hPosition
      have h := hOutside position hAfter hPosition
      rw [← hSize] at hPosition
      rw [getElem!_pos _ position hPosition] at h
      exact h
  case vc5 => simp_all

/-- `siftUp` は開始添字の祖先経路外にある有効位置を変更しない。 -/
theorem siftUp_getElem!_eq_of_not_ancestor (prefer : Nat → Nat → Bool)
    (heap : Array Nat) (start position : Nat)
    (hStart : start < heap.size)
    (hPosition : position < heap.size)
    (hNotAncestor : ¬
      LeanExperiments.Verification.HeapSort.Spec.HeapDescendant position start) :
    (LeanExperiments.RunningMedian.siftUp prefer heap start)[position]! = heap[position]! := by
  generalize hRun : LeanExperiments.RunningMedian.siftUp prefer heap start = result
  apply Id.of_run_eq_wp hRun
  vcgen [LeanExperiments.RunningMedian.siftUp] invariants
  · fun _ state => state.1.size = heap.size ∧ state.2 ≤ start ∧
      LeanExperiments.Verification.HeapSort.Spec.HeapDescendant state.2 start ∧
      (∀ index,
        ¬ LeanExperiments.Verification.HeapSort.Spec.HeapDescendant index start →
        index < heap.size → state.1[index]! = heap[index]!)
  case vc1 => exact ⟨rfl, Nat.le_refl _,
    LeanExperiments.Verification.HeapSort.Spec.HeapDescendant.root start, by simp⟩
  case vc2 =>
    simp_all
    rename_i arr curr hOuter hInvariant
    rcases hInvariant with ⟨hSize, hBound, hPath, hOutside⟩
    have hValue := hOutside position hNotAncestor hPosition
    have hArrayBound : position < arr.size := by omega
    rw [getElem!_pos arr position hArrayBound] at hValue
    exact hValue
  case vc3 =>
    simp_all [Variant.evalsBelow_ofMeasure_nat, Variant.evalsTo_ofMeasure,
      Assertion.NondetFun.evalsTo_pure]
    rename_i arr curr idx hInvariant hPositive hCompare
    rcases hInvariant with ⟨hCurrentEq, hSize, hBound, hPath, hOutside⟩
    subst curr
    have hParentCurrent :
        LeanExperiments.Verification.HeapSort.Spec.HeapDescendant parent idx := by
      dsimp [parent]
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
    have hParentPath :
        LeanExperiments.Verification.HeapSort.Spec.HeapDescendant parent start := by
      exact hParentCurrent.trans hPath
    constructor
    · dsimp [parent]
      omega
    constructor
    · simpa [values, LeanExperiments.RunningMedian.swap] using hSize
    constructor
    · dsimp [parent]
      omega
    constructor
    · exact hParentPath
    · intro position hNotAncestor hPosition
      have hPositionArray : position < arr.size := by omega
      have hCurrentArray : idx < arr.size := by omega
      have hParentArray : parent < arr.size := by
        dsimp [parent]
        omega
      have hNotCurrent : position ≠ idx := by
        intro hEq
        subst position
        exact hNotAncestor hPath
      have hNotParent : position ≠ parent := by
        intro hEq
        subst position
        exact hNotAncestor hParentPath
      have hSwap := swap_getElem!_eq_of_outside arr idx parent position
        hCurrentArray hParentArray hPositionArray hNotCurrent hNotParent
      have hOld := hOutside position hNotAncestor (by omega)
      dsimp [values]
      exact hSwap.trans hOld
  case vc4 =>
    simp_all [Variant.evalsTo_ofMeasure, Assertion.NondetFun.evalsTo_pure]
    rename_i arr curr measure invariant hPositive hNoCompare
    rcases invariant with ⟨hCurrentEq, hSize, hBound, hPath, hOutside⟩
    subst curr
    rw [← hSize] at hPosition
    constructor
    · exact hBound
    constructor
    · exact hPath
    · intro index hNotAncestor hIndex
      have hIndexValue := hOutside index hNotAncestor (by omega)
      rw [← hSize] at hIndex
      rw [getElem!_pos _ index hIndex] at hIndexValue
      exact hIndexValue
  case vc5 => simp_all

/-- 根を優先しない開始値を親方向へ調整しても、根の値は変わらない。

調整中に動く値をループ不変条件で追跡する。値と根の優先関係は変わらないため、
調整が根の位置まで進むことはなく、各交換では根以外の位置だけが更新される。
-/
theorem siftUp_root_eq_of_start_not_preferred (prefer : Nat → Nat → Bool)
    (heap : Array Nat) (start : Nat)
    (hStart : 0 < start) (hBound : start < heap.size)
    (hNotPreferred : prefer heap[start]! heap[0]! = false) :
    (LeanExperiments.RunningMedian.siftUp prefer heap start)[0]! = heap[0]! := by
  generalize hRun : LeanExperiments.RunningMedian.siftUp
    prefer heap start = result
  apply Id.of_run_eq_wp hRun
  vcgen [LeanExperiments.RunningMedian.siftUp] invariants
  · fun _ state => state.1.size = heap.size ∧ 0 < state.2 ∧
      state.2 < heap.size ∧ state.1[state.2]! = heap[start]! ∧
      state.1[0]! = heap[0]! ∧ prefer heap[start]! heap[0]! = false
  case vc1 => exact ⟨rfl, hStart, hBound, rfl, rfl, hNotPreferred⟩
  case vc2 => simp_all
  case vc3 =>
    simp_all [Variant.evalsBelow_ofMeasure_nat, Variant.evalsTo_ofMeasure,
      Assertion.NondetFun.evalsTo_pure]
    rename_i arr idx measure invariant hPositive hCompare
    have hIdxEq := invariant.1
    have hSize := invariant.2.1
    have hIdxBound := invariant.2.2.1
    have hCurrent := invariant.2.2.2.1
    have hRoot := invariant.2.2.2.2
    have hCurrentValue : arr[measure]! = heap[start] := by
      simpa [hIdxEq] using hCurrent
    have hCandidateNotPreferred : prefer arr[measure]! arr[0]! = false := by
      rw [hCurrentValue, hRoot]
      exact hNotPreferred
    have hParentPositive : 0 < (idx - 1) / 2 := by
      by_cases hParentZero : (idx - 1) / 2 = 0
      · have hCompare' := hCompare
        rw [show parent = 0 from hParentZero] at hCompare'
        rw [hCurrentValue, hRoot] at hCompare'
        rw [hNotPreferred] at hCompare'
        cases hCompare'
      · omega
    constructor
    · dsimp [parent]
      omega
    constructor
    · simpa [values, LeanExperiments.RunningMedian.swap] using hSize
    constructor
    · exact hParentPositive
    constructor
    · dsimp [parent]
      omega
    constructor
    · have hAt := swap_getElem!_at_positions arr idx ((idx - 1) / 2)
        (by omega) (by omega)
      calc
        (LeanExperiments.RunningMedian.swap arr idx ((idx - 1) / 2))[(idx - 1) / 2]! =
            arr[idx]! := hAt.2
        _ = heap[start] := hCurrent
    · have hAtZero := swap_getElem!_eq_of_outside arr idx ((idx - 1) / 2) 0
        (by omega) (by omega) (by omega) (by omega) (by omega)
      simpa [values] using hAtZero.trans hRoot
  case vc4 =>
    simp_all [Variant.evalsTo_ofMeasure, Assertion.NondetFun.evalsTo_pure]
    rename_i arr idx measure invariant hPositive hNoCompare
    have hIdxEq := invariant.1
    have hIdxBound := invariant.2.2.1
    have hCurrent := invariant.2.2.2.1
    constructor
    · omega
    · simpa [hIdxEq] using hCurrent
  case vc5 => simp_all

/-- 最大優先ヒープでは、根以下の値を挿入しても既存の根は変わらない。 -/
theorem insertHeap_root_eq_of_not_preferred (prefer : Nat → Nat → Bool)
    (heap : Array Nat) (value : Nat) (hNonempty : 0 < heap.size)
    (hNotPreferred : prefer value heap[0]! = false) :
    (LeanExperiments.RunningMedian.insertHeap prefer heap value)[0]! = heap[0]! := by
  have hBound : heap.size < (heap.push value).size := by simp
  have hInsertedNotPreferred :
      prefer (heap.push value)[heap.size]! (heap.push value)[0]! = false := by
    simpa [Array.getElem_push, hNonempty] using hNotPreferred
  have hRoot := siftUp_root_eq_of_start_not_preferred prefer
    (heap.push value) heap.size hNonempty hBound hInsertedNotPreferred
  simpa [LeanExperiments.RunningMedian.insertHeap, Array.getElem_push, hNonempty] using hRoot

/-- 最大優先ヒープでは、根以下の値を挿入しても既存の根は変わらない。 -/
theorem insertHeap_maxPrefer_root_eq_of_le (heap : Array Nat) (value : Nat)
    (hNonempty : 0 < heap.size) (hValue : value ≤ heap[0]!) :
    (LeanExperiments.RunningMedian.insertHeap LeanExperiments.RunningMedian.maxPrefer
      heap value)[0]! = heap[0]! := by
  apply insertHeap_root_eq_of_not_preferred
  · exact hNonempty
  · simp [LeanExperiments.RunningMedian.maxPrefer, hValue]

/-- 最小優先ヒープでは、根以上の値を挿入しても既存の根は変わらない。 -/
theorem insertHeap_minPrefer_root_eq_of_ge (heap : Array Nat) (value : Nat)
    (hNonempty : 0 < heap.size) (hValue : heap[0]! ≤ value) :
    (LeanExperiments.RunningMedian.insertHeap LeanExperiments.RunningMedian.minPrefer
      heap value)[0]! = heap[0]! := by
  apply insertHeap_root_eq_of_not_preferred
  · exact hNonempty
  · simp [LeanExperiments.RunningMedian.minPrefer, hValue]

/-- 根の位置から始める親方向調整は、交換相手がないため配列を変更しない。 -/
theorem siftUp_zero_eq_self (prefer : Nat → Nat → Bool) (heap : Array Nat) :
    LeanExperiments.RunningMedian.siftUp prefer heap 0 = heap := by
  generalize hRun : LeanExperiments.RunningMedian.siftUp prefer heap 0 = result
  apply Id.of_run_eq_wp hRun
  vcgen [LeanExperiments.RunningMedian.siftUp] invariants
  · fun finished state => state.1 = heap ∧ state.2 = 0
  case vc1 => simp_all
  case vc2 => simp_all [parent] <;> omega
  case vc3 =>
    simp_all [Variant.evalsTo_ofMeasure, Assertion.NondetFun.evalsTo_pure,
      parent] <;> omega
  case vc4 => simp_all [Variant.evalsTo_ofMeasure, Assertion.NondetFun.evalsTo_pure]

/-- 開始位置が根、または親との交換条件が偽なら、親方向調整は配列を変更しない。 -/
theorem siftUp_eq_self_of_stops (prefer : Nat → Nat → Bool)
    (heap : Array Nat) (start : Nat)
    (hStops : start = 0 ∨ prefer heap[start]! heap[(start - 1) / 2]! = false) :
    LeanExperiments.RunningMedian.siftUp prefer heap start = heap := by
  by_cases hZero : start = 0
  · subst start
    exact siftUp_zero_eq_self prefer heap
  · have hNoSwap := hStops.resolve_left hZero
    generalize hRun : LeanExperiments.RunningMedian.siftUp prefer heap start = result
    apply Id.of_run_eq_wp hRun
    vcgen [LeanExperiments.RunningMedian.siftUp] invariants
    · fun finished state => state.1 = heap ∧ state.2 = start
    case vc1 => simp_all
    case vc2 =>
      simp_all [Variant.evalsBelow_ofMeasure_nat, Variant.evalsTo_ofMeasure,
        Assertion.NondetFun.evalsTo_pure, parent]
      rcases ‹_ ∧ _ ∧ _› with ⟨hIndexEq, hArray, hStartEq⟩
      simp_all
    case vc3 =>
      simp_all [Variant.evalsTo_ofMeasure, Assertion.NondetFun.evalsTo_pure,
        parent] <;> omega
    case vc4 =>
      simp_all [Variant.evalsTo_ofMeasure, Assertion.NondetFun.evalsTo_pure]

/-- ヒープへの挿入は要素数をちょうど1つ増やす。 -/
theorem insertHeap_size (prefer : Nat → Nat → Bool) (heap : Array Nat) (value : Nat) :
    (LeanExperiments.RunningMedian.insertHeap prefer heap value).size = heap.size + 1 := by
  unfold LeanExperiments.RunningMedian.insertHeap
  rw [siftUp_size]
  simp

/-- ヒープ挿入は、元の要素に新しい値を1つ加えた順列を返す。 -/
theorem insertHeap_perm (prefer : Nat → Nat → Bool) (heap : Array Nat) (value : Nat) :
    (LeanExperiments.RunningMedian.insertHeap prefer heap value).toList.Perm
      (heap.toList ++ [value]) := by
  unfold LeanExperiments.RunningMedian.insertHeap
  have h := siftUp_perm prefer (heap.push value) ((heap.push value).size - 1) (by simp)
  simpa using h

/-- 空ヒープ、または追加値と末尾葉の親の比較で停止する場合、挿入は末尾追加だけで終わる。 -/
theorem insertHeap_eq_push_of_stops (prefer : Nat → Nat → Bool)
    (heap : Array Nat) (value : Nat)
    (hStops : heap.size = 0 ∨ prefer value heap[(heap.size - 1) / 2]! = false) :
    LeanExperiments.RunningMedian.insertHeap prefer heap value = heap.push value := by
  unfold LeanExperiments.RunningMedian.insertHeap
  change LeanExperiments.RunningMedian.siftUp prefer (heap.push value)
    ((heap.push value).size - 1) = heap.push value
  have hStart : (heap.push value).size - 1 = heap.size := by simp
  rw [hStart]
  apply siftUp_eq_self_of_stops
  by_cases hEmpty : heap.size = 0
  · left
    exact hEmpty
  · right
    have hNoSwap : prefer value heap[(heap.size - 1) / 2]! = false := by
      rcases hStops with hStop | hStop
      · contradiction
      · exact hStop
    let parent := (heap.size - 1) / 2
    have hParent : parent < heap.size := by dsimp [parent]; omega
    have hParentPush : parent < (heap.push value).size := by simp; omega
    have hSameParent : (heap.push value)[parent]! = heap[parent]! := by
      rw [getElem!_pos (heap.push value) parent hParentPush,
        getElem!_pos heap parent hParent]
      simp [Array.getElem_push, hParent]
    simpa [parent, hSameParent] using hNoSwap

/-- 挿入後の根は、元のヒープの要素か新たに挿入した値のいずれかである。 -/
theorem insertHeap_root_mem_input_or_value (prefer : Nat → Nat → Bool)
    (heap : Array Nat) (value : Nat) :
    (LeanExperiments.RunningMedian.insertHeap prefer heap value)[0]! ∈ heap.toList ∨
      (LeanExperiments.RunningMedian.insertHeap prefer heap value)[0]! = value := by
  have hNonempty : 0 <
      (LeanExperiments.RunningMedian.insertHeap prefer heap value).size := by
    rw [insertHeap_size]
    omega
  have hRootMem :
      (LeanExperiments.RunningMedian.insertHeap prefer heap value)[0]! ∈
        (LeanExperiments.RunningMedian.insertHeap prefer heap value).toList := by
    have hRootMem' :
        (LeanExperiments.RunningMedian.insertHeap prefer heap value)[0]'(by omega) ∈
          (LeanExperiments.RunningMedian.insertHeap prefer heap value).toList :=
      Array.getElem_mem_toList hNonempty
    simpa only [← getElem!_pos] using hRootMem'
  have hPerm := insertHeap_perm prefer heap value
  have hCandidate :
      (LeanExperiments.RunningMedian.insertHeap prefer heap value)[0]! ∈
        heap.toList ++ [value] := hPerm.mem_iff.mp hRootMem
  simpa only [List.mem_append, List.mem_singleton] using hCandidate

/-- 元ヒープと追加値が上界以下なら、挿入後の全要素もその上界以下である。 -/
theorem insertHeap_le_of_forall_le (prefer : Nat → Nat → Bool)
    (heap : Array Nat) (value bound : Nat)
    (hHeap : ∀ item, item ∈ heap.toList → item ≤ bound)
    (hValue : value ≤ bound) :
    ∀ item, item ∈ (LeanExperiments.RunningMedian.insertHeap prefer heap value).toList →
      item ≤ bound := by
  intro item hItem
  have hCandidate := (insertHeap_perm prefer heap value).mem_iff.mp hItem
  simp only [List.mem_append, List.mem_singleton] at hCandidate
  rcases hCandidate with hOld | hNew
  · exact hHeap item hOld
  · simpa [hNew] using hValue

/-- 元ヒープと追加値が下界以上なら、挿入後の全要素もその下界以上である。 -/
theorem insertHeap_ge_of_forall_ge (prefer : Nat → Nat → Bool)
    (heap : Array Nat) (value bound : Nat)
    (hHeap : ∀ item, item ∈ heap.toList → bound ≤ item)
    (hValue : bound ≤ value) :
    ∀ item, item ∈ (LeanExperiments.RunningMedian.insertHeap prefer heap value).toList →
      bound ≤ item := by
  intro item hItem
  have hCandidate := (insertHeap_perm prefer heap value).mem_iff.mp hItem
  simp only [List.mem_append, List.mem_singleton] at hCandidate
  rcases hCandidate with hOld | hNew
  · exact hHeap item hOld
  · simpa [hNew] using hValue

/-- 元ヒープと追加値が属する閉区間は、挿入後の全要素について保たれる。 -/
theorem insertHeap_mem_between_of_forall_between (prefer : Nat → Nat → Bool)
    (heap : Array Nat) (value lower upper : Nat)
    (hHeap : ∀ item, item ∈ heap.toList → lower ≤ item ∧ item ≤ upper)
    (hValue : lower ≤ value ∧ value ≤ upper) :
    ∀ item, item ∈ (LeanExperiments.RunningMedian.insertHeap prefer heap value).toList →
      lower ≤ item ∧ item ≤ upper := by
  intro item hItem
  have hCandidate := (insertHeap_perm prefer heap value).mem_iff.mp hItem
  simp only [List.mem_append, List.mem_singleton] at hCandidate
  rcases hCandidate with hOld | hNew
  · exact hHeap item hOld
  · simpa [hNew] using hValue

/-- 空ヒープへ1要素を挿入すると、その値を根に持つ1要素ヒープになる。

一般の要素順列保存とサイズ増加を組み合わせ、長さ1の出力を一意に定める。
-/
theorem insertHeap_empty (prefer : Nat → Nat → Bool) (value : Nat) :
    LeanExperiments.RunningMedian.insertHeap prefer #[] value = #[value] := by
  simp [LeanExperiments.RunningMedian.insertHeap, siftUp_zero_eq_self]

/-- 挿入後の任意の Boolean 分類の個数は、新しい値の所属分だけ増える。 -/
theorem insertHeap_countP (prefer : Nat → Nat → Bool) (heap : Array Nat)
    (value : Nat) (predicate : Nat → Bool) :
    (LeanExperiments.RunningMedian.insertHeap prefer heap value).toList.countP predicate =
      heap.toList.countP predicate + if predicate value then 1 else 0 := by
  have hCounts := (insertHeap_perm prefer heap value).countP_eq predicate
  simpa [List.countP_append] using hCounts

/-- 入力を連結して一度に処理する結果は、前半の後に後半を挿入した状態と一致する。

この定理は値の範囲や要素数に制限がなく、配列を分割して逐次処理する際の状態合成則に
なる。中央値の計算結果だけでなく、二つのヒープを含む状態全体が一致する。
-/
theorem ofArray_append (left right : Array Nat) :
    LeanExperiments.RunningMedian.ofArray (left ++ right) =
      right.foldl LeanExperiments.RunningMedian.insert
        (LeanExperiments.RunningMedian.ofArray left) := by
  simp [LeanExperiments.RunningMedian.ofArray]

/-- 連結入力の中央値は、前半の状態に後半を順次挿入した状態から得られる。 -/
theorem medianOf_append (left right : Array Nat) :
    LeanExperiments.RunningMedian.medianOf (left ++ right) =
      LeanExperiments.RunningMedian.median
        (right.foldl LeanExperiments.RunningMedian.insert
          (LeanExperiments.RunningMedian.ofArray left)) := by
  exact congrArg LeanExperiments.RunningMedian.median (ofArray_append left right)

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

private def maxPrefer (candidate current : Nat) : Bool := current < candidate
private def minPrefer (candidate current : Nat) : Bool := candidate < current

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
