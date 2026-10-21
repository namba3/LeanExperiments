import LeanExperiments.RunningMedian
import LeanExperiments.HeapSort
import LeanExperiments.Verification.MergeSort.Spec
import LeanExperiments.Verification.HeapSort.Spec
import Std.WP
import Std.Tactic.Do

/-! # 逐次中央値の配列・ヒープ操作契約

交換、下降・上昇調整、挿入、および配列からの構築について、任意入力に対する
サイズ・要素保存・局所性などの一般契約をまとめる。 -/

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


end LeanExperiments.Verification.RunningMedian
