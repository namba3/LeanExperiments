import LeanExperiments.MergeSort
import LeanExperiments.Verification.Sorting.Spec
import Std.WP
import Std.Tactic.Do

/-!
# マージソートの計算例

空入力、重複値、逆順の入力を使って、分割と併合の実装結果をカーネル内で確認する。
再帰版、命令的な `while` 併合ループ、反復版ソート全体について、任意入力の一般正当性を証明する。
明示した有限領域の計算検査は、境界回帰確認として一般証明を補う。
-/

namespace LeanExperiments.Verification.MergeSort

open List
open Std.WP Lean.Order
set_option experimental.vcgen true

/-- `merge` は左右の要素をちょうど保ち、連結リストと順列になる。 -/
theorem merge_perm_append (left right : List Nat) :
    List.Perm (LeanExperiments.MergeSort.merge left right) (left ++ right) := by
  cases left with
  | nil => simp [LeanExperiments.MergeSort.merge]
  | cons leftHead leftTail =>
    cases right with
    | nil => simp [LeanExperiments.MergeSort.merge]
    | cons rightHead rightTail =>
      by_cases h : leftHead ≤ rightHead
      · have hTail := merge_perm_append leftTail (rightHead :: rightTail)
        simpa [LeanExperiments.MergeSort.merge, h] using hTail.cons leftHead
      · simp only [LeanExperiments.MergeSort.merge, ite_eq_right h]
        have hTail := merge_perm_append (leftHead :: leftTail) rightTail
        calc
          rightHead :: LeanExperiments.MergeSort.merge (leftHead :: leftTail) rightTail ~
              rightHead :: ((leftHead :: leftTail) ++ rightTail) := hTail.cons rightHead
          _ ~ (leftHead :: leftTail) ++ rightHead :: rightTail :=
            (List.perm_middle (a := rightHead)).symm
termination_by left.length + right.length
decreasing_by all_goals simp_wf <;> omega

/-- 右側が空のとき、`merge` は左側をそのまま返す。 -/
theorem merge_empty_right (left : List Nat) :
    LeanExperiments.MergeSort.merge left [] = left := by
  induction left with
  | nil => simp [LeanExperiments.MergeSort.merge]
  | cons head tail ih => simp [LeanExperiments.MergeSort.merge]

/-- 二つの昇順リストを併合すると、結果も昇順になる。 -/
theorem merge_pairwise : ∀ left right,
    left.Pairwise (fun a b : Nat => a ≤ b) →
    right.Pairwise (fun a b : Nat => a ≤ b) →
    (LeanExperiments.MergeSort.merge left right).Pairwise (fun a b : Nat => a ≤ b)
  | [], right, _, hRight => by simpa [LeanExperiments.MergeSort.merge] using hRight
  | left, [], hLeft, _ => by
    rw [merge_empty_right]
    exact hLeft
  | leftHead :: leftTail, rightHead :: rightTail, hLeft, hRight => by
    by_cases hHeads : leftHead ≤ rightHead
    · simp only [LeanExperiments.MergeSort.merge, ite_eq_left hHeads]
      apply List.Pairwise.cons
      · intro value hValue
        have hPerm := merge_perm_append leftTail (rightHead :: rightTail)
        have hInAppend := hPerm.mem_iff.mp hValue
        simp only [List.mem_append] at hInAppend
        rcases hInAppend with hInLeft | hInRight
        · exact List.rel_of_pairwise_cons hLeft hInLeft
        · simp only [List.mem_cons] at hInRight
          rcases hInRight with rfl | hInRight
          · exact hHeads
          · exact Nat.le_trans hHeads (List.rel_of_pairwise_cons hRight hInRight)
      · exact merge_pairwise leftTail (rightHead :: rightTail) hLeft.tail hRight
    · simp only [LeanExperiments.MergeSort.merge, ite_eq_right hHeads]
      apply List.Pairwise.cons
      · intro value hValue
        have hPerm := merge_perm_append (leftHead :: leftTail) rightTail
        have hInAppend := hPerm.mem_iff.mp hValue
        simp only [List.mem_append] at hInAppend
        rcases hInAppend with hInLeft | hInRight
        · simp only [List.mem_cons] at hInLeft
          rcases hInLeft with rfl | hInLeft
          · omega
          · exact Nat.le_trans (by omega) (List.rel_of_pairwise_cons hLeft hInLeft)
        · exact List.rel_of_pairwise_cons hRight hInRight
      · exact merge_pairwise (leftHead :: leftTail) rightTail hLeft hRight.tail
termination_by left right => left.length + right.length
decreasing_by all_goals simp_wf <;> omega

/-- 二つの昇順リストの併合は、連結した入力に対する共通ソート仕様を満たす。

昇順性と要素保存を別々に証明した併合補題を共通仕様 `Correct` にまとめる。
左右の部分列を先に整列する実装を検証するとき、最後の併合段階をこの契約で置き換えられる。
-/
theorem merge_correct (left right : List Nat)
    (hLeft : LeanExperiments.Verification.Sorting.Spec.Ascending left)
    (hRight : LeanExperiments.Verification.Sorting.Spec.Ascending right) :
    LeanExperiments.Verification.Sorting.Spec.Correct (left ++ right)
      (LeanExperiments.MergeSort.merge left right) := by
  refine ⟨LeanExperiments.Verification.Sorting.Spec.pairwise_ascending _
    (merge_pairwise left right
      (LeanExperiments.Verification.Sorting.Spec.ascending_pairwise left hLeft)
      (LeanExperiments.Verification.Sorting.Spec.ascending_pairwise right hRight)), ?_⟩
  exact merge_perm_append left right

/-- 命令型 merge の主ループを表すリスト状態。

左右の未処理 suffix と、すでに出力した prefix を保持する。
-/
structure MergeLoopState where
  leftRemaining : List Nat
  rightRemaining : List Nat
  emitted : List Nat
  deriving Repr

/-- 両方に未処理要素があるとき、小さい先頭要素を出力へ移す一回の状態遷移。 -/
def mergeLoopStep (state : MergeLoopState) : MergeLoopState :=
  match state.leftRemaining, state.rightRemaining with
  | leftHead :: leftTail, rightHead :: rightTail =>
      if leftHead ≤ rightHead then
        ⟨leftTail, rightHead :: rightTail, state.emitted ++ [leftHead]⟩
      else
        ⟨leftHead :: leftTail, rightTail, state.emitted ++ [rightHead]⟩
  | _, _ => state

/-- 一回の主ループ反復で選ばれて出力へ移る値。 -/
def mergeLoopSelected (state : MergeLoopState) : Option Nat :=
  match state.leftRemaining, state.rightRemaining with
  | leftHead :: _, rightHead :: _ =>
      some (if leftHead ≤ rightHead then leftHead else rightHead)
  | _, _ => none

/-- ループ状態の出力済み部分と未処理部分を元の要素列に戻す。 -/
def mergeLoopContents (state : MergeLoopState) : List Nat :=
  state.emitted ++ state.leftRemaining ++ state.rightRemaining

/-- 両 suffix が昇順なら、選択した先頭値は反復後に残る全要素以下である。

マージ済み prefix を伸ばす際に、新しい末尾が後続値より大きくならないことを表す。
-/
theorem mergeLoopSelected_le_remaining (state : MergeLoopState)
    (hLeft : state.leftRemaining.Pairwise (fun a b : Nat => a ≤ b))
    (hRight : state.rightRemaining.Pairwise (fun a b : Nat => a ≤ b)) :
    ∀ value ∈ (mergeLoopStep state).leftRemaining ++
        (mergeLoopStep state).rightRemaining,
      ∀ selected ∈ (mergeLoopSelected state).toList, selected ≤ value := by
  cases state with
  | mk left right emitted =>
    cases left with
    | nil => simp [mergeLoopStep, mergeLoopSelected]
    | cons leftHead leftTail =>
      cases right with
      | nil => simp [mergeLoopStep, mergeLoopSelected]
      | cons rightHead rightTail =>
        by_cases hHeads : leftHead ≤ rightHead
        · simp only [mergeLoopSelected, mergeLoopStep, ite_eq_left hHeads,
            List.mem_cons, List.mem_append]
          intro value hValue selected hSelected
          simp only [Option.toList_some, List.mem_singleton] at hSelected
          subst selected
          rcases hValue with hValue | hValue
          · exact List.rel_of_pairwise_cons hLeft hValue
          · rcases hValue with rfl | hValue
            · exact hHeads
            · exact Nat.le_trans hHeads (List.rel_of_pairwise_cons hRight hValue)
        · have hRightHeadLeft : rightHead ≤ leftHead := by omega
          simp only [mergeLoopSelected, mergeLoopStep, ite_eq_right hHeads,
            List.mem_cons, List.mem_append]
          intro value hValue selected hSelected
          simp only [Option.toList_some, List.mem_singleton] at hSelected
          subst selected
          rcases hValue with hValue | hValue
          · rcases hValue with rfl | hValue
            · exact hRightHeadLeft
            · exact Nat.le_trans hRightHeadLeft
                (List.rel_of_pairwise_cons hLeft hValue)
          · exact List.rel_of_pairwise_cons hRight hValue

/-- 一反復後に未処理 suffix に残る値は、反復前にも未処理だった。 -/
theorem mergeLoopStep_remaining_mem (state : MergeLoopState) {value : Nat}
    (hValue : value ∈ (mergeLoopStep state).leftRemaining ++
      (mergeLoopStep state).rightRemaining) :
    value ∈ state.leftRemaining ++ state.rightRemaining := by
  cases state with
  | mk left right emitted =>
    cases left with
    | nil => simpa [mergeLoopStep] using hValue
    | cons leftHead leftTail =>
      cases right with
      | nil => simpa [mergeLoopStep] using hValue
      | cons rightHead rightTail =>
        by_cases hHeads : leftHead ≤ rightHead
        · simp only [mergeLoopStep, ite_eq_left hHeads, List.mem_append,
            List.mem_cons] at hValue ⊢
          rcases hValue with hLeft | hRight
          · exact Or.inl (Or.inr hLeft)
          · exact Or.inr hRight
        · simp only [mergeLoopStep, ite_eq_right hHeads, List.mem_append,
            List.mem_cons] at hValue ⊢
          rcases hValue with hLeft | hRight
          · exact Or.inl hLeft
          · exact Or.inr (Or.inr hRight)

/-- 昇順 suffix 上で、遷移後も出力済み prefix は未処理値以下のままである。 -/
theorem mergeLoopStep_preserves_boundary (state : MergeLoopState)
    (hLeft : state.leftRemaining.Pairwise (fun a b : Nat => a ≤ b))
    (hRight : state.rightRemaining.Pairwise (fun a b : Nat => a ≤ b))
    (hBoundary : ∀ x ∈ state.emitted, ∀ y ∈ state.leftRemaining ++ state.rightRemaining,
      x ≤ y) :
    ∀ x ∈ (mergeLoopStep state).emitted,
      ∀ y ∈ (mergeLoopStep state).leftRemaining ++ (mergeLoopStep state).rightRemaining,
        x ≤ y := by
  cases state with
  | mk left right emitted =>
    cases left with
    | nil => simpa [mergeLoopStep] using hBoundary
    | cons leftHead leftTail =>
      cases right with
      | nil => simpa [mergeLoopStep] using hBoundary
      | cons rightHead rightTail =>
        by_cases hHeads : leftHead ≤ rightHead
        · simp only [mergeLoopStep, ite_eq_left hHeads]
          intro x hx y hy
          have hyStep : y ∈ (mergeLoopStep ⟨leftHead :: leftTail,
              rightHead :: rightTail, emitted⟩).leftRemaining ++
              (mergeLoopStep ⟨leftHead :: leftTail, rightHead :: rightTail,
                emitted⟩).rightRemaining := by
            simpa [mergeLoopStep, hHeads] using hy
          rcases List.mem_append.mp hx with hx | hx
          · exact hBoundary x hx y (mergeLoopStep_remaining_mem _ hyStep)
          · have hxEq : x = leftHead := by simpa using hx
            subst x
            exact mergeLoopSelected_le_remaining _ hLeft hRight y hyStep leftHead (by
              simp [mergeLoopSelected, hHeads])
        · simp only [mergeLoopStep, ite_eq_right hHeads]
          intro x hx y hy
          have hyStep : y ∈ (mergeLoopStep ⟨leftHead :: leftTail,
              rightHead :: rightTail, emitted⟩).leftRemaining ++
              (mergeLoopStep ⟨leftHead :: leftTail, rightHead :: rightTail,
                emitted⟩).rightRemaining := by
            simpa [mergeLoopStep, hHeads] using hy
          rcases List.mem_append.mp hx with hx | hx
          · exact hBoundary x hx y (mergeLoopStep_remaining_mem _ hyStep)
          · have hxEq : x = rightHead := by simpa using hx
            subst x
            exact mergeLoopSelected_le_remaining _ hLeft hRight y hyStep rightHead (by
              simp [mergeLoopSelected, hHeads])

/-- 出力 prefix が未処理 suffix 以下なら、遷移後の出力 prefix も pairwise 昇順である。 -/
theorem mergeLoopStep_preserves_emitted_pairwise (state : MergeLoopState)
    (hEmitted : state.emitted.Pairwise (fun a b : Nat => a ≤ b))
    (hBoundary : ∀ x ∈ state.emitted, ∀ y ∈ state.leftRemaining ++ state.rightRemaining,
      x ≤ y) :
    (mergeLoopStep state).emitted.Pairwise (fun a b : Nat => a ≤ b) := by
  cases state with
  | mk left right emitted =>
    cases left with
    | nil => simpa [mergeLoopStep] using hEmitted
    | cons leftHead leftTail =>
      cases right with
      | nil => simpa [mergeLoopStep] using hEmitted
      | cons rightHead rightTail =>
        by_cases hHeads : leftHead ≤ rightHead
        · simp only [mergeLoopStep, ite_eq_left hHeads]
          rw [List.pairwise_append]
          refine ⟨hEmitted, by simp, ?_⟩
          intro x hx y hy
          have hyEq : y = leftHead := by simpa using hy
          subst y
          exact hBoundary x hx leftHead (by simp)
        · simp only [mergeLoopStep, ite_eq_right hHeads]
          rw [List.pairwise_append]
          refine ⟨hEmitted, by simp, ?_⟩
          intro x hx y hy
          have hyEq : y = rightHead := by simpa using hy
          subst y
          exact hBoundary x hx rightHead (by simp)

/-- 出力 prefix が昇順で、すべての未処理値以下であるという主ループ不変条件。 -/
def MergeLoopPrefixInvariant (state : MergeLoopState) : Prop :=
  state.emitted.Pairwise (fun a b : Nat => a ≤ b) ∧
    (∀ x ∈ state.emitted, ∀ y ∈ state.leftRemaining ++ state.rightRemaining, x ≤ y)

/-- 空の出力から始めた状態は prefix 不変条件を満たす。 -/
theorem mergeLoopPrefixInvariant_init (left right : List Nat) :
    MergeLoopPrefixInvariant ⟨left, right, []⟩ := by
  simp [MergeLoopPrefixInvariant]

/-- 左右の suffix が昇順なら、一反復後も prefix 不変条件が保たれる。 -/
theorem mergeLoopStep_preserves_prefixInvariant (state : MergeLoopState)
    (hLeft : state.leftRemaining.Pairwise (fun a b : Nat => a ≤ b))
    (hRight : state.rightRemaining.Pairwise (fun a b : Nat => a ≤ b))
    (hInvariant : MergeLoopPrefixInvariant state) :
    MergeLoopPrefixInvariant (mergeLoopStep state) := by
  exact ⟨mergeLoopStep_preserves_emitted_pairwise state hInvariant.1 hInvariant.2,
    mergeLoopStep_preserves_boundary state hLeft hRight hInvariant.2⟩

/-- 各 suffix が昇順なら、一反復後の左右 suffix も昇順である。 -/
theorem mergeLoopStep_preserves_remaining_sorted (state : MergeLoopState)
    (hLeft : state.leftRemaining.Pairwise (fun a b : Nat => a ≤ b))
    (hRight : state.rightRemaining.Pairwise (fun a b : Nat => a ≤ b)) :
    (mergeLoopStep state).leftRemaining.Pairwise (fun a b : Nat => a ≤ b) ∧
      (mergeLoopStep state).rightRemaining.Pairwise (fun a b : Nat => a ≤ b) := by
  cases state with
  | mk left right emitted =>
    cases left with
    | nil => exact ⟨hLeft, hRight⟩
    | cons leftHead leftTail =>
      cases right with
      | nil => exact ⟨hLeft, hRight⟩
      | cons rightHead rightTail =>
        by_cases hHeads : leftHead ≤ rightHead
        · simp only [mergeLoopStep, ite_eq_left hHeads]
          exact ⟨hLeft.tail, hRight⟩
        · simp only [mergeLoopStep, ite_eq_right hHeads]
          exact ⟨hLeft, hRight.tail⟩

/-- 出力 prefix と二つの未処理 suffix に対する主ループ不変条件。 -/
def MergeLoopInvariant (state : MergeLoopState) : Prop :=
  MergeLoopPrefixInvariant state ∧
    state.leftRemaining.Pairwise (fun a b : Nat => a ≤ b) ∧
    state.rightRemaining.Pairwise (fun a b : Nat => a ≤ b)

/-- 空 prefix と昇順な入力 suffix から主ループ不変条件を初期化する。 -/
theorem mergeLoopInvariant_init (left right : List Nat)
    (hLeft : left.Pairwise (fun a b : Nat => a ≤ b))
    (hRight : right.Pairwise (fun a b : Nat => a ≤ b)) :
    MergeLoopInvariant ⟨left, right, []⟩ :=
  ⟨mergeLoopPrefixInvariant_init left right, hLeft, hRight⟩

/-- 主ループの一反復は prefix と左右 suffix の不変条件をまとめて保つ。 -/
theorem mergeLoopStep_preserves_invariant (state : MergeLoopState)
    (hInvariant : MergeLoopInvariant state) :
    MergeLoopInvariant (mergeLoopStep state) := by
  rcases hInvariant with ⟨hPrefix, hLeft, hRight⟩
  exact ⟨mergeLoopStep_preserves_prefixInvariant state hLeft hRight hPrefix,
    (mergeLoopStep_preserves_remaining_sorted state hLeft hRight).1,
    (mergeLoopStep_preserves_remaining_sorted state hLeft hRight).2⟩

/-- 一回の主ループ遷移は、重複を含めて要素を保存する。 -/
theorem mergeLoopStep_preserves_contents_perm (state : MergeLoopState) :
    List.Perm (mergeLoopContents (mergeLoopStep state)) (mergeLoopContents state) := by
  cases state with
  | mk left right emitted =>
    cases left with
    | nil => simp [mergeLoopStep, mergeLoopContents]
    | cons leftHead leftTail =>
      cases right with
      | nil => simp [mergeLoopStep, mergeLoopContents]
      | cons rightHead rightTail =>
        simp only [mergeLoopStep]
        by_cases hHeads : leftHead ≤ rightHead
        · simp [hHeads, mergeLoopContents, List.append_assoc]
        · simp only [ite_eq_right hHeads, mergeLoopContents, List.append_assoc]
          have hMiddle : List.Perm
              (rightHead :: ((leftHead :: leftTail) ++ rightTail))
              ((leftHead :: leftTail) ++ rightHead :: rightTail) :=
            (List.perm_middle (a := rightHead)).symm
          exact (List.Perm.refl emitted).append hMiddle

/-- 両方の suffix が残るとき、各ループ反復で未処理総数が一つ減る。 -/
theorem mergeLoopStep_decreases_remaining (state : MergeLoopState)
    (hLeft : state.leftRemaining ≠ []) (hRight : state.rightRemaining ≠ []) :
    (mergeLoopStep state).leftRemaining.length +
        (mergeLoopStep state).rightRemaining.length <
      state.leftRemaining.length + state.rightRemaining.length := by
  cases state with
  | mk left right emitted =>
    cases left with
    | nil => contradiction
    | cons leftHead leftTail =>
      cases right with
      | nil => contradiction
      | cons rightHead rightTail =>
        simp only [mergeLoopStep]
        split <;> simp_all <;> omega

/-- 左右の先頭から一つずつ出力へ移す状態モデルの主ループ。

再帰呼び出しを左右のリスト引数で直接表し、残り要素数を停止性の測度にする。
-/
def mergeLoopRun (left right emitted : List Nat) : MergeLoopState :=
  match left, right with
  | [], _ => ⟨left, right, emitted⟩
  | _, [] => ⟨left, right, emitted⟩
  | leftHead :: leftTail, rightHead :: rightTail =>
    if leftHead ≤ rightHead then
      mergeLoopRun leftTail (rightHead :: rightTail) (emitted ++ [leftHead])
    else
      mergeLoopRun (leftHead :: leftTail) rightTail (emitted ++ [rightHead])
termination_by left.length + right.length
decreasing_by
  all_goals simp_wf <;> simp_all <;> omega

/-- 停止まで主ループを実行しても、prefix と suffix の不変条件が保たれる。 -/
theorem mergeLoopRun_preserves_invariant (left right emitted : List Nat)
    (hInvariant : MergeLoopInvariant ⟨left, right, emitted⟩) :
    MergeLoopInvariant (mergeLoopRun left right emitted) := by
  have hGeneral : ∀ n left right emitted,
      left.length + right.length = n →
      MergeLoopInvariant ⟨left, right, emitted⟩ →
      MergeLoopInvariant (mergeLoopRun left right emitted) := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro left right emitted hMeasure hState
      cases left with
      | nil => simpa [mergeLoopRun] using hState
      | cons leftHead leftTail =>
        cases right with
        | nil => simpa [mergeLoopRun] using hState
        | cons rightHead rightTail =>
          simp only [mergeLoopRun]
          by_cases hHeads : leftHead ≤ rightHead
          · simp only [ite_eq_left hHeads]
            apply ih (leftTail.length + (rightHead :: rightTail).length)
            · simp at hMeasure ⊢
              omega
            · rfl
            · simpa [ite_eq_left hHeads, mergeLoopStep, hHeads] using
                mergeLoopStep_preserves_invariant
                ⟨leftHead :: leftTail, rightHead :: rightTail, emitted⟩ hState
          · simp only [ite_eq_right hHeads]
            apply ih ((leftHead :: leftTail).length + rightTail.length)
            · simp at hMeasure ⊢
              omega
            · rfl
            · simpa [ite_eq_right hHeads, mergeLoopStep, hHeads] using
                mergeLoopStep_preserves_invariant
                ⟨leftHead :: leftTail, rightHead :: rightTail, emitted⟩ hState
  exact hGeneral (left.length + right.length) left right emitted rfl hInvariant

/-- 停止まで主ループを実行しても、重複を含む要素の内容が保存される。 -/
theorem mergeLoopRun_preserves_contents_perm (left right emitted : List Nat) :
    List.Perm (mergeLoopContents (mergeLoopRun left right emitted))
      (mergeLoopContents ⟨left, right, emitted⟩) := by
  have hGeneral : ∀ n left right emitted,
      left.length + right.length = n →
      List.Perm (mergeLoopContents (mergeLoopRun left right emitted))
        (mergeLoopContents ⟨left, right, emitted⟩) := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro left right emitted hMeasure
      cases left with
      | nil => simp [mergeLoopRun, mergeLoopContents]
      | cons leftHead leftTail =>
        cases right with
        | nil => simp [mergeLoopRun, mergeLoopContents]
        | cons rightHead rightTail =>
          simp only [mergeLoopRun]
          by_cases hHeads : leftHead ≤ rightHead
          · simp only [ite_eq_left hHeads]
            have hRun := ih (leftTail.length + (rightHead :: rightTail).length)
              (by simp at hMeasure ⊢; omega) leftTail (rightHead :: rightTail)
              (emitted ++ [leftHead]) rfl
            exact hRun.trans (by
              simp [mergeLoopContents, List.append_assoc])
          · simp only [ite_eq_right hHeads]
            have hRun := ih ((leftHead :: leftTail).length + rightTail.length)
              (by simp at hMeasure ⊢; omega) (leftHead :: leftTail) rightTail
              (emitted ++ [rightHead]) rfl
            have hStep := mergeLoopStep_preserves_contents_perm
              ⟨leftHead :: leftTail, rightHead :: rightTail, emitted⟩
            exact hRun.trans (by
              simpa [mergeLoopStep, hHeads, mergeLoopContents, List.append_assoc] using hStep)
  exact hGeneral (left.length + right.length) left right emitted rfl

/-- 有限回帰確認で使う値。小値の重複と桁の大きい値を含める。 -/
def mergeIterativeBoundaryValues : List Nat := [0, 1, 1000000]

/-- 有限回帰確認用の入力領域。上記 3 値からなる長さ 2 以下の全 13 リスト。 -/
def mergeIterativeBoundaryInputs : List (List Nat) :=
  let values := mergeIterativeBoundaryValues
  let singletons := values.map (fun value => [value])
  let pairs := values.flatMap (fun left => values.map (fun right => [left, right]))
  [] :: (singletons ++ pairs)

/-- 有限回帰確認: 上記 13 リストの全 169 組で、命令的 `while` 実装と状態モデルが一致する。

任意入力での一致は `mergeIterative_eq_loop_model` が証明し、この有限領域は実行回帰を確認する。
-/
theorem mergeIterative_bounded_agrees_with_loop_model :
    ∀ left ∈ mergeIterativeBoundaryInputs,
      ∀ right ∈ mergeIterativeBoundaryInputs,
        LeanExperiments.MergeSort.mergeIterative left right =
          mergeLoopContents (mergeLoopRun left right []) := by
  native_decide

/-- 実際の `while` 併合実装は、任意の入力で再帰版 `merge` と一致する。

ループ中は「逆順に蓄積した prefix と残り二列の再帰的併合」が初期仕様と等しい、という
不変条件を使う。ループ変種は残り要素数で、各反復が一要素を消費することを証明する。
-/
theorem mergeIterative_eq_merge (inputLeft inputRight : List Nat) :
    LeanExperiments.MergeSort.mergeIterative inputLeft inputRight =
      LeanExperiments.MergeSort.merge inputLeft inputRight := by
  generalize hRun : LeanExperiments.MergeSort.mergeIterative inputLeft inputRight = result
  apply Id.of_run_eq_wp hRun
  vcgen [LeanExperiments.MergeSort.mergeIterative] invariants
  · fun _ state =>
      state.2.2.reverse ++ LeanExperiments.MergeSort.merge state.1 state.2.1 =
        LeanExperiments.MergeSort.merge inputLeft inputRight
  all_goals
    simp_all [LeanExperiments.MergeSort.merge, Variant.evalsTo_ofMeasure,
      Assertion.NondetFun.evalsTo_pure, Variant.evalsBelow_ofMeasure_nat,
      outputReversed, List.append_assoc] <;> omega

/-- 有限回帰確認用のソート入力。上記 3 値からなる長さ 3 以下の全 40 リスト。 -/
def mergeSortIterativeBoundaryInputs : List (List Nat) :=
  let values := mergeIterativeBoundaryValues
  let singletons := values.map (fun value => [value])
  let pairs := values.flatMap (fun first => values.map (fun second => [first, second]))
  let triples := values.flatMap (fun first =>
    values.flatMap (fun second => values.map (fun third => [first, second, third])))
  [] :: (singletons ++ pairs ++ triples)

/-- 有限領域の確認: 境界値 3 種・長さ 3 以下の全 40 入力で反復版と再帰版が一致する。

任意の入力に対する一般証明ではなく、空列・重複値・端数 run の回帰確認である。
-/
theorem mergeSortIterative_bounded_agrees_with_recursive :
    ∀ values ∈ mergeSortIterativeBoundaryInputs,
      LeanExperiments.MergeSort.mergeSortIterative values =
        LeanExperiments.MergeSort.mergeSort values := by
  native_decide

/-- 主ループ終了時には、左右の未処理 suffix の少なくとも一方が空である。 -/
theorem mergeLoopRun_stops (left right emitted : List Nat) :
    (mergeLoopRun left right emitted).leftRemaining = [] ∨
      (mergeLoopRun left right emitted).rightRemaining = [] := by
  have hGeneral : ∀ n left right emitted,
      left.length + right.length = n →
      (mergeLoopRun left right emitted).leftRemaining = [] ∨
        (mergeLoopRun left right emitted).rightRemaining = [] := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro left right emitted hMeasure
      cases left with
      | nil => simp [mergeLoopRun]
      | cons leftHead leftTail =>
        cases right with
        | nil => simp [mergeLoopRun]
        | cons rightHead rightTail =>
          simp only [mergeLoopRun]
          by_cases hHeads : leftHead ≤ rightHead
          · simp only [ite_eq_left hHeads]
            apply ih (leftTail.length + (rightHead :: rightTail).length)
            · simp at hMeasure ⊢
              omega
            · rfl
          · simp only [ite_eq_right hHeads]
            apply ih ((leftHead :: leftTail).length + rightTail.length)
            · simp at hMeasure ⊢
              omega
            · rfl
  exact hGeneral (left.length + right.length) left right emitted rfl

/-- 昇順な二列を主ループで併合した出力は、一般に昇順である。 -/
theorem mergeLoopRun_output_pairwise (left right : List Nat)
    (hLeft : left.Pairwise (fun a b : Nat => a ≤ b))
    (hRight : right.Pairwise (fun a b : Nat => a ≤ b)) :
    (mergeLoopContents (mergeLoopRun left right [])).Pairwise
      (fun a b : Nat => a ≤ b) := by
  let initial : MergeLoopState := ⟨left, right, []⟩
  have hFinal := mergeLoopRun_preserves_invariant left right []
    (mergeLoopInvariant_init left right hLeft hRight)
  rcases mergeLoopRun_stops left right [] with hLeftEmpty | hRightEmpty
  · have hSorted :
        ((mergeLoopRun left right []).emitted ++
          (mergeLoopRun left right []).rightRemaining).Pairwise
            (fun a b : Nat => a ≤ b) := by
      rw [List.pairwise_append]
      refine ⟨hFinal.1.1, hFinal.2.2, ?_⟩
      intro x hx y hy
      apply hFinal.1.2 x hx y
      simp [hLeftEmpty, hy]
    simpa [mergeLoopContents, hLeftEmpty] using hSorted
  · have hSorted :
        ((mergeLoopRun left right []).emitted ++
          (mergeLoopRun left right []).leftRemaining).Pairwise
            (fun a b : Nat => a ≤ b) := by
      rw [List.pairwise_append]
      refine ⟨hFinal.1.1, hFinal.2.1, ?_⟩
      intro x hx y hy
      apply hFinal.1.2 x hx y
      simp [hRightEmpty, hy]
    simpa [mergeLoopContents, hRightEmpty, List.append_assoc] using hSorted

/-- 昇順な二列を主ループで併合した結果は、連結した入力に対する共通仕様を満たす。 -/
theorem mergeLoopRun_correct (left right : List Nat)
    (hLeft : LeanExperiments.Verification.Sorting.Spec.Ascending left)
    (hRight : LeanExperiments.Verification.Sorting.Spec.Ascending right) :
    LeanExperiments.Verification.Sorting.Spec.Correct (left ++ right)
      (mergeLoopContents (mergeLoopRun left right [])) := by
  refine ⟨LeanExperiments.Verification.Sorting.Spec.pairwise_ascending _
    (mergeLoopRun_output_pairwise left right
      (LeanExperiments.Verification.Sorting.Spec.ascending_pairwise left hLeft)
      (LeanExperiments.Verification.Sorting.Spec.ascending_pairwise right hRight)), ?_⟩
  simpa [mergeLoopContents, List.append_assoc] using
    mergeLoopRun_preserves_contents_perm left right []

/-- 状態モデルの併合結果は、再帰版 `merge` の一般仕様から定まる結果と一致する。 -/
theorem mergeLoopRun_eq_merge (left right : List Nat)
    (hLeft : LeanExperiments.Verification.Sorting.Spec.Ascending left)
    (hRight : LeanExperiments.Verification.Sorting.Spec.Ascending right) :
    mergeLoopContents (mergeLoopRun left right []) =
      LeanExperiments.MergeSort.merge left right := by
  exact (LeanExperiments.Verification.Sorting.Spec.Correct.eq_of_same_input
    (mergeLoopRun_correct left right hLeft hRight)
    (merge_correct left right hLeft hRight))

/-- 主ループモデルは、昇順性の仮定なしでも再帰版 `merge` と同じ残り列を作る。 -/
theorem mergeLoopRun_contents_eq_merge (left right emitted : List Nat) :
    mergeLoopContents (mergeLoopRun left right emitted) =
      emitted ++ LeanExperiments.MergeSort.merge left right := by
  have hGeneral : ∀ n left right emitted,
      left.length + right.length = n →
      mergeLoopContents (mergeLoopRun left right emitted) =
        emitted ++ LeanExperiments.MergeSort.merge left right := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro left right emitted hMeasure
      cases left with
      | nil => simp [mergeLoopRun, mergeLoopContents, LeanExperiments.MergeSort.merge]
      | cons leftHead leftTail =>
        cases right with
        | nil => simp [mergeLoopRun, mergeLoopContents, LeanExperiments.MergeSort.merge]
        | cons rightHead rightTail =>
          simp only [mergeLoopRun, LeanExperiments.MergeSort.merge]
          by_cases hHeads : leftHead ≤ rightHead
          · simp only [ite_eq_left hHeads]
            have hTail := ih (leftTail.length + (rightHead :: rightTail).length)
              (by simp at hMeasure ⊢; omega) leftTail (rightHead :: rightTail)
              (emitted ++ [leftHead]) rfl
            simpa [mergeLoopContents, List.append_assoc] using hTail
          · simp only [ite_eq_right hHeads]
            have hTail := ih ((leftHead :: leftTail).length + rightTail.length)
              (by simp at hMeasure ⊢; omega) (leftHead :: leftTail) rightTail
              (emitted ++ [rightHead]) rfl
            simpa [mergeLoopContents, List.append_assoc] using hTail
  exact hGeneral (left.length + right.length) left right emitted rfl

/-- 実際の併合ループは、任意の入力で状態モデルの停止結果と一致する。 -/
theorem mergeIterative_eq_loop_model (left right : List Nat) :
    LeanExperiments.MergeSort.mergeIterative left right =
      mergeLoopContents (mergeLoopRun left right []) := by
  rw [mergeIterative_eq_merge]
  simpa using (mergeLoopRun_contents_eq_merge left right []).symm

/-- 昇順な左右リストを実際の併合ループで併合した結果は、共通仕様を満たす。 -/
theorem mergeIterative_correct (left right : List Nat)
    (hLeft : LeanExperiments.Verification.Sorting.Spec.Ascending left)
    (hRight : LeanExperiments.Verification.Sorting.Spec.Ascending right) :
    LeanExperiments.Verification.Sorting.Spec.Correct (left ++ right)
      (LeanExperiments.MergeSort.mergeIterative left right) := by
  rw [mergeIterative_eq_loop_model]
  exact mergeLoopRun_correct left right hLeft hRight


/-- 昇順な二列の併合結果は、左右の列の順を入れ替えても変わらない。

両方の結果が同じ連結入力を正しくソートするため、共通仕様の一意性から従う。
-/
theorem merge_comm_of_ascending (left right : List Nat)
    (hLeft : LeanExperiments.Verification.Sorting.Spec.Ascending left)
    (hRight : LeanExperiments.Verification.Sorting.Spec.Ascending right) :
    LeanExperiments.MergeSort.merge left right =
      LeanExperiments.MergeSort.merge right left := by
  apply LeanExperiments.Verification.Sorting.Spec.Correct.eq_of_perm_inputs
    (merge_correct left right hLeft hRight)
    (merge_correct right left hRight hLeft)
  exact List.perm_append_comm

/-- 三つの昇順 run は、併合の括り方によらず同じ結果になる。

各段階の `merge_correct` を合成し、両方の結果が同じ連結列を正しくソートすることを示す。
隣接 run を異なる組み合わせで併合する反復 pass の結果比較に利用できる。
-/
theorem merge_assoc_of_ascending (left middle right : List Nat)
    (hLeft : LeanExperiments.Verification.Sorting.Spec.Ascending left)
    (hMiddle : LeanExperiments.Verification.Sorting.Spec.Ascending middle)
    (hRight : LeanExperiments.Verification.Sorting.Spec.Ascending right) :
    LeanExperiments.MergeSort.merge
        (LeanExperiments.MergeSort.merge left middle) right =
      LeanExperiments.MergeSort.merge left
        (LeanExperiments.MergeSort.merge middle right) := by
  have hLeftMiddle := merge_correct left middle hLeft hMiddle
  have hMiddleRight := merge_correct middle right hMiddle hRight
  have hLeftGrouped := merge_correct
    (LeanExperiments.MergeSort.merge left middle) right hLeftMiddle.1 hRight
  have hRightGrouped := merge_correct
    left (LeanExperiments.MergeSort.merge middle right) hLeft hMiddleRight.1
  have hLeftInput :
      (LeanExperiments.MergeSort.merge left middle) ++ right ~ left ++ (middle ++ right) := by
    exact (hLeftMiddle.2.append (List.Perm.refl right)).trans
      (List.Perm.of_eq (List.append_assoc left middle right))
  have hRightInput :
      left ++ LeanExperiments.MergeSort.merge middle right ~ left ++ (middle ++ right) := by
    exact ((List.Perm.refl left).append hMiddleRight.2)
  apply LeanExperiments.Verification.Sorting.Spec.Correct.eq_of_same_input
    ⟨hLeftGrouped.1, hLeftGrouped.2.trans hLeftInput⟩
    ⟨hRightGrouped.1, hRightGrouped.2.trans hRightInput⟩

/-- すでに昇順な run を葉に持つ、二分併合木。

反復処理で隣接 run を併合する順序を抽象化し、併合の括り方に依存しない性質を調べる。
-/
inductive MergeTree where
  | leaf : List Nat → MergeTree
  | node : MergeTree → MergeTree → MergeTree
  deriving Repr

/-- 併合木が表す入力列。葉の run を左から順に連結する。 -/
def MergeTree.input : MergeTree → List Nat
  | .leaf values => values
  | .node left right => left.input ++ right.input

/-- 併合木を評価し、各内部節点で二つの結果を `merge` する。 -/
def MergeTree.eval : MergeTree → List Nat
  | .leaf values => values
  | .node left right =>
      LeanExperiments.MergeSort.merge left.eval right.eval

/-- 併合木の全ての葉が昇順 run であること。 -/
def MergeTree.RunsAscending : MergeTree → Prop
  | .leaf values => LeanExperiments.Verification.Sorting.Spec.Ascending values
  | .node left right => left.RunsAscending ∧ right.RunsAscending

/-- 昇順 run を葉に持つ任意の併合木は、その全入力に対して正しいソート結果を返す。

木の形や内部節点の併合順序を固定せず、各節点の `merge_correct` を帰納的に合成する。
-/
theorem MergeTree.correct (tree : MergeTree) (hRuns : tree.RunsAscending) :
    LeanExperiments.Verification.Sorting.Spec.Correct tree.input tree.eval := by
  induction tree with
  | leaf values =>
      change LeanExperiments.Verification.Sorting.Spec.Correct values values
      exact ⟨hRuns, List.Perm.refl values⟩
  | node left right ihLeft ihRight =>
      obtain ⟨hLeftRuns, hRightRuns⟩ := hRuns
      have hLeft := ihLeft hLeftRuns
      have hRight := ihRight hRightRuns
      have hMerge := merge_correct left.eval right.eval hLeft.1 hRight.1
      change LeanExperiments.Verification.Sorting.Spec.Correct
        (left.input ++ right.input) (LeanExperiments.MergeSort.merge left.eval right.eval)
      exact ⟨hMerge.1, hMerge.2.trans (hLeft.2.append hRight.2)⟩

/-- 任意の昇順run併合木は、同じ入力を `Correct` にソートする任意の実装と一致する。 -/
theorem MergeTree.eval_eq_of_correct_sorter (tree : MergeTree)
    (hRuns : tree.RunsAscending) (sorter : List Nat → List Nat)
    (hSorter : ∀ values,
      LeanExperiments.Verification.Sorting.Spec.Correct values (sorter values)) :
    tree.eval = sorter tree.input :=
  LeanExperiments.Verification.Sorting.Spec.Correct.eq_of_same_input
    (tree.correct hRuns) (hSorter tree.input)

/-- run併合木の入力が任意の正しいソート入力と順列関係なら、そのソート結果とも一致する。 -/
theorem MergeTree.eval_eq_of_correct_sorter_of_input_perm (tree : MergeTree)
    (hRuns : tree.RunsAscending) (sorter : List Nat → List Nat)
    (hSorter : ∀ values,
      LeanExperiments.Verification.Sorting.Spec.Correct values (sorter values))
    (input : List Nat) (hInputs : tree.input.Perm input) :
    tree.eval = sorter input :=
  LeanExperiments.Verification.Sorting.Spec.Correct.eq_of_perm_inputs
    (tree.correct hRuns) (hSorter input) hInputs

/-- 同じ多重集合を表す昇順 run 併合木は、どの木構造でも同じ列を返す。 -/
theorem MergeTree.eval_eq_of_input_perm (left right : MergeTree)
    (hLeft : left.RunsAscending) (hRight : right.RunsAscending)
    (hInputs : left.input.Perm right.input) :
    left.eval = right.eval :=
  LeanExperiments.Verification.Sorting.Spec.Correct.eq_of_perm_inputs
    (left.correct hLeft) (right.correct hRight) hInputs

/-- run の列を右から順に併合する二分木を作る。空の run 列は空 run として表す。 -/
def MergeTree.ofRuns : List (List Nat) → MergeTree
  | [] => .leaf []
  | [run] => .leaf run
  | run :: next :: rest => .node (.leaf run) (ofRuns (next :: rest))

/-- `ofRuns` が表す入力は、run 列を連結したものと一致する。 -/
theorem MergeTree.ofRuns_input (runs : List (List Nat)) :
    (MergeTree.ofRuns runs).input = runs.flatten := by
  induction runs with
  | nil => rfl
  | cons run rest ih =>
      cases rest with
      | nil => simp [MergeTree.ofRuns, MergeTree.input]
      | cons next tail =>
          simp [MergeTree.ofRuns, MergeTree.input, List.flatten_cons, ih]

/-- 全 run が昇順なら、`ofRuns` の全ての葉も昇順である。 -/
theorem MergeTree.ofRuns_runsAscending (runs : List (List Nat))
    (hRuns : ∀ run ∈ runs,
      LeanExperiments.Verification.Sorting.Spec.Ascending run) :
    (MergeTree.ofRuns runs).RunsAscending := by
  induction runs with
  | nil => simp [MergeTree.ofRuns, MergeTree.RunsAscending,
      LeanExperiments.Verification.Sorting.Spec.Ascending]
  | cons run rest ih =>
      cases rest with
      | nil =>
          simpa [MergeTree.ofRuns, MergeTree.RunsAscending] using hRuns run (by simp)
      | cons next tail =>
          simp only [MergeTree.ofRuns, MergeTree.RunsAscending]
          refine ⟨hRuns run (by simp), ?_⟩
          apply ih
          intro item hItem
          exact hRuns item (by simp [hItem])

/-- `ofRuns` の評価は、各 run を右から畳み込んで併合した結果である。 -/
theorem MergeTree.ofRuns_eval (runs : List (List Nat)) :
    (MergeTree.ofRuns runs).eval =
      runs.foldr
        (fun run merged => LeanExperiments.MergeSort.merge run merged) [] := by
  induction runs with
  | nil => rfl
  | cons run rest ih =>
      cases rest with
      | nil =>
          simp only [MergeTree.ofRuns, MergeTree.eval, List.foldr_cons, List.foldr_nil]
          cases run <;> simp [LeanExperiments.MergeSort.merge]
      | cons next tail =>
          simp only [MergeTree.ofRuns, MergeTree.eval, List.foldr_cons, ih]

/-- 任意の併合木は、同じ run 列の右畳み込みと同じ結果を返す。

木の葉が昇順で、入力が run 列の連結と順列関係にあれば、全ての二分併合順序が
共通のソート仕様を満たすため結果が一意になる。
-/
theorem MergeTree.eval_eq_foldMerge_of_input_perm (tree : MergeTree)
    (runs : List (List Nat)) (hTree : tree.RunsAscending)
    (hRuns : ∀ run ∈ runs,
      LeanExperiments.Verification.Sorting.Spec.Ascending run)
    (hInputs : tree.input.Perm runs.flatten) :
    tree.eval =
      runs.foldr
        (fun run merged => LeanExperiments.MergeSort.merge run merged) [] := by
  rw [← MergeTree.ofRuns_eval runs]
  apply MergeTree.eval_eq_of_input_perm tree (MergeTree.ofRuns runs)
    hTree (MergeTree.ofRuns_runsAscending runs hRuns)
  rw [MergeTree.ofRuns_input]
  exact hInputs

/-- 同じ半分割を使う再帰版 merge sort の併合木を構成する。 -/
def MergeTree.ofList (values : List Nat) : MergeTree :=
  if values.length ≤ 1 then
    .leaf values
  else
    .node (ofList (values.take (values.length / 2)))
      (ofList (values.drop (values.length / 2)))
termination_by values.length
decreasing_by
  all_goals simp_wf
  all_goals omega

/-- `ofList` が作る木の入力は、元のリストそのものである。 -/
theorem MergeTree.ofList_input (values : List Nat) :
    (MergeTree.ofList values).input = values := by
  by_cases hSmall : values.length ≤ 1
  · rw [MergeTree.ofList, ite_eq_left hSmall]
    rfl
  · rw [MergeTree.ofList, ite_eq_right hSmall]
    simp only [MergeTree.input]
    rw [MergeTree.ofList_input, MergeTree.ofList_input]
    exact List.take_append_drop _ _
termination_by values.length
decreasing_by
  all_goals simp_wf
  all_goals omega

/-- `ofList` が作る木の葉は全て昇順 run である。 -/
theorem MergeTree.ofList_runsAscending (values : List Nat) :
    (MergeTree.ofList values).RunsAscending := by
  by_cases hSmall : values.length ≤ 1
  · cases values with
    | nil => simp [MergeTree.ofList, MergeTree.RunsAscending,
        LeanExperiments.Verification.Sorting.Spec.Ascending]
    | cons first rest =>
      cases rest with
      | nil => simp [MergeTree.ofList, MergeTree.RunsAscending,
          LeanExperiments.Verification.Sorting.Spec.Ascending]
      | cons second rest => simp at hSmall
  · rw [MergeTree.ofList, ite_eq_right hSmall]
    simp only [MergeTree.RunsAscending]
    exact ⟨MergeTree.ofList_runsAscending _, MergeTree.ofList_runsAscending _⟩
termination_by values.length
decreasing_by
  all_goals simp_wf
  all_goals omega

/-- `ofList` の木評価は、公開されている再帰版 `mergeSort` と一致する。 -/
theorem MergeTree.ofList_eval (values : List Nat) :
    (MergeTree.ofList values).eval = LeanExperiments.MergeSort.mergeSort values := by
  by_cases hSmall : values.length ≤ 1
  · rw [MergeTree.ofList, ite_eq_left hSmall]
    simp [MergeTree.eval, LeanExperiments.MergeSort.mergeSort, hSmall]
  · rw [MergeTree.ofList, ite_eq_right hSmall]
    rw [MergeTree.eval, LeanExperiments.MergeSort.mergeSort, ite_eq_right hSmall]
    rw [MergeTree.ofList_eval, MergeTree.ofList_eval]
termination_by values.length
decreasing_by
  all_goals simp_wf
  all_goals omega

/-- 隣り合う run を一組ずつ併合する一回分の pass。 -/
def mergePass : List (List Nat) → List (List Nat)
  | [] => []
  | [run] => [run]
  | left :: right :: rest =>
      LeanExperiments.MergeSort.merge left right :: mergePass rest

/-- 実装側の一 pass は、仕様側の再帰版 pass と任意の run 列で一致する。 -/
theorem mergePassIterative_eq_mergePass : ∀ runs : List (List Nat),
    LeanExperiments.MergeSort.mergePassIterative runs = mergePass runs
  | [] => by simp [LeanExperiments.MergeSort.mergePassIterative, mergePass]
  | [run] => by simp [LeanExperiments.MergeSort.mergePassIterative, mergePass]
  | left :: right :: rest => by
      simp only [LeanExperiments.MergeSort.mergePassIterative, mergePass]
      rw [mergeIterative_eq_merge, mergePassIterative_eq_mergePass rest]
termination_by runs => runs.length
decreasing_by all_goals simp_wf <;> omega

/-- run の列を元の入力順に連結する。 -/
def flattenRuns : List (List Nat) → List Nat
  | [] => []
  | run :: rest => run ++ flattenRuns rest

/-- run の各要素が昇順であることを表す。 -/
def RunsAscending : List (List Nat) → Prop
  | [] => True
  | run :: rest =>
      LeanExperiments.Verification.Sorting.Spec.Ascending run ∧ RunsAscending rest

/-- 一回の隣接併合 pass は、各出力 run の昇順性を保つ。 -/
theorem mergePass_preserves_sorted_runs : ∀ runs : List (List Nat),
    RunsAscending runs → RunsAscending (mergePass runs)
  | [], _ => trivial
  | [run], hRuns => by simpa [mergePass, RunsAscending] using hRuns
  | left :: right :: rest, hRuns => by
      simp only [mergePass, RunsAscending]
      exact ⟨(merge_correct left right hRuns.1 hRuns.2.1).1,
        mergePass_preserves_sorted_runs rest hRuns.2.2⟩
termination_by runs => runs.length
decreasing_by all_goals simp_wf <;> omega

/-- 一回の隣接併合 pass は、全 run を合わせた要素を重複込みで保存する。 -/
theorem mergePass_preserves_flattened_perm : ∀ runs : List (List Nat),
    List.Perm (flattenRuns (mergePass runs)) (flattenRuns runs)
  | [] => by simp [mergePass, flattenRuns]
  | [run] => by simp [mergePass, flattenRuns]
  | left :: right :: rest => by
      simp only [mergePass, flattenRuns]
      exact ((merge_perm_append left right).append
        (mergePass_preserves_flattened_perm rest)).trans
          (List.Perm.of_eq (List.append_assoc left right (flattenRuns rest)))
termination_by runs => runs.length
decreasing_by all_goals simp_wf <;> omega

/-- 任意回数の隣接併合 pass でも、各 run の昇順性は保たれる。 -/
def mergePasses : Nat → List (List Nat) → List (List Nat)
  | 0, runs => runs
  | rounds + 1, runs => mergePasses rounds (mergePass runs)

/-- 繰り返し pass を行っても、全 run を合わせた要素は保存される。 -/
theorem mergePasses_preserves_flattened_perm (rounds : Nat) (runs : List (List Nat)) :
    List.Perm (flattenRuns (mergePasses rounds runs)) (flattenRuns runs) := by
  induction rounds generalizing runs with
  | zero => exact List.Perm.refl _
  | succ rounds ih =>
    simp only [mergePasses]
    exact (ih (mergePass runs)).trans (mergePass_preserves_flattened_perm runs)

/-- 任意回数の隣接併合 pass でも、各 run の昇順性は保たれる。 -/
theorem mergePasses_preserves_sorted_runs (rounds : Nat) (runs : List (List Nat))
    (hRuns : RunsAscending runs) : RunsAscending (mergePasses rounds runs) := by
  induction rounds generalizing runs with
  | zero => exact hRuns
  | succ rounds ih =>
    simp only [mergePasses]
    exact ih (mergePass runs) (mergePass_preserves_sorted_runs runs hRuns)

/-- 一回の隣接併合 pass 後の run 数は、元の run 数の切り上げ半分になる。 -/
theorem mergePass_length : ∀ runs : List (List Nat),
    (mergePass runs).length = (runs.length + 1) / 2
  | [] => rfl
  | [_] => by simp [mergePass]
  | _ :: _ :: rest => by
      simp only [mergePass, List.length_cons]
      rw [mergePass_length]
      omega

/-- 実装側の pass も、run 数を切り上げ半分にする。 -/
theorem mergePassIterative_length (runs : List (List Nat)) :
    (LeanExperiments.MergeSort.mergePassIterative runs).length = (runs.length + 1) / 2 := by
  rw [mergePassIterative_eq_mergePass]
  exact mergePass_length runs

/-- 実装側の一 pass は、各 run の昇順性を保つ。 -/
theorem mergePassIterative_preserves_sorted_runs (runs : List (List Nat))
    (hRuns : RunsAscending runs) :
    RunsAscending (LeanExperiments.MergeSort.mergePassIterative runs) := by
  rw [mergePassIterative_eq_mergePass]
  exact mergePass_preserves_sorted_runs runs hRuns

/-- 実装側の一 pass は、全 run を合わせた要素を重複込みで保存する。 -/
theorem mergePassIterative_preserves_flattened_perm (runs : List (List Nat)) :
    List.Perm (flattenRuns (LeanExperiments.MergeSort.mergePassIterative runs))
      (flattenRuns runs) := by
  rw [mergePassIterative_eq_mergePass]
  exact mergePass_preserves_flattened_perm runs

/-- 二つ以上の run がある場合、実装側の一 pass は run 数を狭義に減らす。 -/
theorem mergePassIterative_length_lt (runs : List (List Nat))
    (hRuns : 1 < runs.length) :
    (LeanExperiments.MergeSort.mergePassIterative runs).length < runs.length := by
  rw [mergePassIterative_length]
  omega

/-- 二つ以上の run がある場合、一回の pass で run 数が狭義に減る。 -/
theorem mergePass_length_lt (runs : List (List Nat)) (hRuns : 1 < runs.length) :
    (mergePass runs).length < runs.length := by
  rw [mergePass_length]
  omega

/-- run が高々一つなら、追加 pass を行っても高々一つのままである。 -/
private theorem mergePasses_preserves_length_le_one (rounds : Nat)
    (runs : List (List Nat)) (hRuns : runs.length ≤ 1) :
    (mergePasses rounds runs).length ≤ 1 := by
  induction rounds generalizing runs with
  | zero => exact hRuns
  | succ rounds ih =>
    simp only [mergePasses]
    apply ih
    rw [mergePass_length]
    omega

/-- 初期 run 数以上の pass を行えば、残る run は高々一つになる。

各 pass は run 数が二つ以上なら少なくとも一つ減らすため、初期個数を上界にできる。
-/
theorem mergePasses_length_le_one_of_rounds_ge_length :
    ∀ rounds (runs : List (List Nat)), runs.length ≤ rounds →
      (mergePasses rounds runs).length ≤ 1
  | 0, runs, hRuns => by
      have : runs = [] := List.length_eq_zero_iff.mp (by omega)
      simp [this, mergePasses]
  | rounds + 1, runs, hRuns => by
      by_cases hSmall : runs.length ≤ 1
      · exact mergePasses_preserves_length_le_one (rounds + 1) runs hSmall
      · have hNext : (mergePass runs).length ≤ rounds := by
          have hDecrease := mergePass_length_lt runs (by omega)
          omega
        simpa only [mergePasses] using
          mergePasses_length_le_one_of_rounds_ge_length rounds (mergePass runs) hNext

/-- run 数が `2^rounds` 以下なら、その pass 数で一 run 以下になる。

各 pass が run 数を切り上げ半分にすることを用いた幾何的な上界であり、入力長回の
pass を使うより強い停止回数評価を与える。
-/
theorem mergePasses_length_le_one_of_length_le_pow :
    ∀ rounds (runs : List (List Nat)), runs.length ≤ 2 ^ rounds →
      (mergePasses rounds runs).length ≤ 1
  | 0, runs, hLength => by
      have hSmall : runs.length ≤ 1 := by simpa using hLength
      simpa [mergePasses] using hSmall
  | rounds + 1, runs, hLength => by
      by_cases hSmall : runs.length ≤ 1
      · exact mergePasses_preserves_length_le_one (rounds + 1) runs hSmall
      · have hNext : (mergePass runs).length ≤ 2 ^ rounds := by
          rw [mergePass_length]
          have hPow : 2 ^ (rounds + 1) = 2 ^ rounds * 2 := by simp [Nat.pow_succ]
          omega
        simpa only [mergePasses] using
          mergePasses_length_le_one_of_length_le_pow rounds (mergePass runs) hNext

/-- 入力の各値を、初期 run として一要素リストにする。 -/
def singletonRuns (values : List Nat) : List (List Nat) :=
  values.map fun value => [value]

/-- 各入力要素から一要素 run を作った場合、入力長 pass 以内に停止状態へ達する。 -/
theorem mergePasses_singletonRuns_length_le_one (values : List Nat) :
    (mergePasses values.length (singletonRuns values)).length ≤ 1 := by
  apply mergePasses_length_le_one_of_rounds_ge_length
  simp [singletonRuns]

/-- 隣接する run を一組ずつ併合し、run が一つになるまで pass を繰り返す。 -/
def mergeUntilOne : List (List Nat) → List Nat
  | [] => []
  | [run] => run
  | left :: right :: rest => mergeUntilOne (mergePass (left :: right :: rest))
termination_by runs => runs.length
decreasing_by
  apply mergePass_length_lt
  simp

/-- run が高々一つなら、再帰モデルは先頭 run を返す。 -/
theorem mergeUntilOne_eq_headD_of_length_le_one (runs : List (List Nat))
    (hLength : runs.length ≤ 1) :
    mergeUntilOne runs = runs.headD [] := by
  cases runs with
  | nil => simp [mergeUntilOne]
  | cons run rest =>
    have hRest : rest = [] := by
      have hRestLength : rest.length = 0 := by
        simp only [List.length_cons] at hLength
        omega
      exact List.length_eq_zero_iff.mp hRestLength
    subst rest
    simp [mergeUntilOne]

/-- run が高々一つなら、何 pass 重ねても先頭 run は変わらない。 -/
private theorem mergePasses_headD_eq_of_length_le_one (rounds : Nat)
    (runs : List (List Nat)) (hLength : runs.length ≤ 1) :
    (mergePasses rounds runs).headD [] = runs.headD [] := by
  have hPass : mergePass runs = runs := by
    cases runs with
    | nil => rfl
    | cons run rest =>
      have hRest : rest = [] := by
        simp only [List.length_cons] at hLength
        have : rest.length = 0 := by omega
        exact List.length_eq_zero_iff.mp this
      subst rest
      rfl
  induction rounds with
  | zero => rfl
  | succ rounds ih =>
    simp only [mergePasses, hPass]
    exact ih

/-- `2^rounds` 以下の run は、再帰モデルと固定 rounds pass が同じ結果になる。 -/
theorem mergeUntilOne_eq_mergePasses_headD_of_length_le_pow :
    ∀ rounds (runs : List (List Nat)), runs.length ≤ 2 ^ rounds →
      mergeUntilOne runs = (mergePasses rounds runs).headD []
  | 0, runs, hLength => by
      have hSmall : runs.length ≤ 1 := by simpa using hLength
      rw [mergeUntilOne_eq_headD_of_length_le_one runs hSmall]
      simp [mergePasses]
  | rounds + 1, runs, hLength => by
      by_cases hSmall : runs.length ≤ 1
      · rw [mergeUntilOne_eq_headD_of_length_le_one runs hSmall]
        exact (mergePasses_headD_eq_of_length_le_one (rounds + 1) runs hSmall).symm
      · have hNext : (mergePass runs).length ≤ 2 ^ rounds := by
          rw [mergePass_length]
          have hPow : 2 ^ (rounds + 1) = 2 ^ rounds * 2 := by simp [Nat.pow_succ]
          omega
        cases runs with
        | nil => simp at hSmall
        | cons left rest =>
          cases rest with
          | nil => simp at hSmall
          | cons right tail =>
            simpa only [mergeUntilOne, mergePasses] using
              mergeUntilOne_eq_mergePasses_headD_of_length_le_pow rounds
                (mergePass (left :: right :: tail)) hNext

/-- 任意 run 列に一 pass を適用しても、最終的な併合結果は変わらない。 -/
theorem mergeUntilOne_mergePassIterative (runs : List (List Nat)) :
    mergeUntilOne (LeanExperiments.MergeSort.mergePassIterative runs) =
      mergeUntilOne runs := by
  rw [mergePassIterative_eq_mergePass]
  cases runs with
  | nil => simp [mergePass, mergeUntilOne]
  | cons left rest =>
    cases rest with
    | nil => simp [mergePass, mergeUntilOne]
    | cons right tail => simp [mergeUntilOne]

/-- 任意の昇順 run 列を pass で一つにまとめると、元の全要素の正しいソート結果になる。

各 pass が run 数を減らし、昇順性と要素保存を保つことから、最終 run の仕様を導く。
-/
theorem mergeUntilOne_correct : ∀ runs : List (List Nat),
    RunsAscending runs →
      LeanExperiments.Verification.Sorting.Spec.Correct
        (flattenRuns runs) (mergeUntilOne runs)
  | [], _ => by simp [flattenRuns, mergeUntilOne,
      LeanExperiments.Verification.Sorting.Spec.Correct,
      LeanExperiments.Verification.Sorting.Spec.Ascending]
  | [run], hRuns => by
      simp only [mergeUntilOne, flattenRuns, List.append_nil]
      exact ⟨hRuns.1, List.Perm.refl run⟩
  | left :: right :: rest, hRuns => by
      have hPassRuns := mergePass_preserves_sorted_runs _ hRuns
      have hPassCorrect := mergeUntilOne_correct (mergePass (left :: right :: rest)) hPassRuns
      have hPassPerm := mergePass_preserves_flattened_perm (left :: right :: rest)
      simp only [mergeUntilOne, flattenRuns] at hPassCorrect ⊢
      exact ⟨hPassCorrect.1, hPassCorrect.2.trans hPassPerm⟩
termination_by runs => runs.length
decreasing_by
  apply mergePass_length_lt
  simp

/-- 一要素 run を連結すると初期入力に戻る。 -/
theorem flatten_singletonRuns (values : List Nat) :
    flattenRuns (singletonRuns values) = values := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
      change flattenRuns (rest.map fun item => [item]) = rest at ih
      simp [singletonRuns, flattenRuns, ih]

/-- run が高々一つなら、その先頭を取り出した値は run 全体と等しい。 -/
theorem headD_correct_of_length_le_one (runs : List (List Nat))
    (hLength : runs.length ≤ 1) (hRuns : RunsAscending runs) :
    LeanExperiments.Verification.Sorting.Spec.Correct (flattenRuns runs) (runs.headD []) := by
  cases runs with
  | nil => simp [flattenRuns, LeanExperiments.Verification.Sorting.Spec.Correct,
      LeanExperiments.Verification.Sorting.Spec.Ascending]
  | cons run rest =>
      have hRest : rest = [] := by
        have hRestLength : rest.length = 0 := by
          change rest.length + 1 ≤ 1 at hLength
          omega
        exact List.length_eq_zero_iff.mp hRestLength
      subst rest
      simp only [List.headD_cons]
      simp only [RunsAscending] at hRuns
      refine ⟨hRuns.1, ?_⟩
      simp [flattenRuns]

/-- 十分な回数 pass を行った後に先頭 run を返すモデルの正当性。 -/
theorem mergePasses_headD_correct (rounds : Nat) (runs : List (List Nat))
    (hRounds : runs.length ≤ rounds) (hRuns : RunsAscending runs) :
    LeanExperiments.Verification.Sorting.Spec.Correct (flattenRuns runs)
      ((mergePasses rounds runs).headD []) := by
  have hStop := mergePasses_length_le_one_of_rounds_ge_length rounds runs hRounds
  have hSorted := mergePasses_preserves_sorted_runs rounds runs hRuns
  have hOutput := headD_correct_of_length_le_one (mergePasses rounds runs) hStop hSorted
  have hPerm := mergePasses_preserves_flattened_perm rounds runs
  exact ⟨hOutput.1, hOutput.2.trans hPerm⟩

/-- 初期 run 数が `2^rounds` 以下なら、幾何的上界の pass 数で正しく併合できる。 -/
theorem mergePasses_headD_correct_of_length_le_pow (rounds : Nat)
    (runs : List (List Nat)) (hLength : runs.length ≤ 2 ^ rounds)
    (hRuns : RunsAscending runs) :
    LeanExperiments.Verification.Sorting.Spec.Correct (flattenRuns runs)
      ((mergePasses rounds runs).headD []) := by
  have hStop := mergePasses_length_le_one_of_length_le_pow rounds runs hLength
  have hSorted := mergePasses_preserves_sorted_runs rounds runs hRuns
  have hOutput := headD_correct_of_length_le_one (mergePasses rounds runs) hStop hSorted
  have hPerm := mergePasses_preserves_flattened_perm rounds runs
  exact ⟨hOutput.1, hOutput.2.trans hPerm⟩

/-- 一要素ずつ作った初期 run はすべて昇順である。 -/
theorem singletonRuns_sorted (values : List Nat) :
    RunsAscending (singletonRuns values) := by
  induction values with
  | nil => trivial
  | cons value rest ih => exact ⟨by trivial, ih⟩

/-- 入力長が `2^rounds` 以下なら、一要素 run の反復併合はその pass 数で正しく完了する。 -/
theorem singletonRuns_mergePasses_headD_correct_of_length_le_pow (rounds : Nat)
    (values : List Nat) (hLength : values.length ≤ 2 ^ rounds) :
    LeanExperiments.Verification.Sorting.Spec.Correct values
      ((mergePasses rounds (singletonRuns values)).headD []) := by
  have h := mergePasses_headD_correct_of_length_le_pow rounds (singletonRuns values)
    (by simpa [singletonRuns] using hLength) (singletonRuns_sorted values)
  simpa [flatten_singletonRuns] using h

/-- 隣接併合による反復ソートの関数型モデル。

これは `mergeSortIterative` と同じ pass を使う仕様モデルである。各 pass の一致に加え、
外側 `while` 全体とのシミュレーションも一般に証明する。
-/
def adjacentMergeSortModel (values : List Nat) : List Nat :=
  mergeUntilOne (singletonRuns values)

/-- 命令的な外側 `while` は、隣接併合モデルと任意入力で一致する。

ループ継続中は現在の run 列を最後まで併合した値を保ち、終了時は先頭 run がその値に
一致することを不変条件に含める。run 数を測度として pass の停止性も確認する。
-/
theorem mergeSortIterative_eq_adjacentMergeSortModel (values : List Nat) :
    LeanExperiments.MergeSort.mergeSortIterative values = adjacentMergeSortModel values := by
  generalize hRun : LeanExperiments.MergeSort.mergeSortIterative values = result
  apply Id.of_run_eq_wp hRun
  vcgen [LeanExperiments.MergeSort.mergeSortIterative] invariants
  · fun finished runs =>
      if finished then runs.headD [] = adjacentMergeSortModel values
      else mergeUntilOne runs = adjacentMergeSortModel values
  case vc1 => rfl
  case vc2 => simp_all
  case vc3 =>
    dsimp [runs] at *
    simp_all [Variant.evalsBelow_ofMeasure_nat, mergePassIterative_length,
      mergeUntilOne_mergePassIterative] <;> omega
  case vc4 =>
    simp_all [Variant.evalsTo_ofMeasure, Assertion.NondetFun.evalsTo_pure]
    have hRuns : runs.length ≤ 1 := by omega
    have hInvariant : mergeUntilOne runs = adjacentMergeSortModel values :=
      (show runs.length = _ ∧ mergeUntilOne runs = adjacentMergeSortModel values from
        by assumption).2
    simpa only [List.headD_eq_head?_getD] using
      (mergeUntilOne_eq_headD_of_length_le_one runs hRuns).symm.trans hInvariant

/-- 入力長が `2^rounds` 以下なら、実装結果はその固定 rounds pass モデルと一致する。 -/
theorem mergeSortIterative_eq_fixedRounds_of_length_le_pow (rounds : Nat)
    (values : List Nat) (hLength : values.length ≤ 2 ^ rounds) :
    LeanExperiments.MergeSort.mergeSortIterative values =
      (mergePasses rounds (singletonRuns values)).headD [] := by
  have hRuns : (singletonRuns values).length ≤ 2 ^ rounds := by
    simpa [singletonRuns] using hLength
  calc
    LeanExperiments.MergeSort.mergeSortIterative values = adjacentMergeSortModel values :=
      mergeSortIterative_eq_adjacentMergeSortModel values
    _ = (mergePasses rounds (singletonRuns values)).headD [] := by
      simpa [adjacentMergeSortModel] using
        mergeUntilOne_eq_mergePasses_headD_of_length_le_pow rounds
          (singletonRuns values) hRuns

/-- 固定回数の pass 後に先頭 run を返す関数型ソートモデル。 -/
def adjacentMergeSortPassModel (values : List Nat) : List Nat :=
  (mergePasses values.length (singletonRuns values)).headD []

/-- 隣接併合モデルは任意の入力について昇順性と要素保存を満たす。 -/
theorem adjacentMergeSortModel_correct (values : List Nat) :
    LeanExperiments.Verification.Sorting.Spec.Correct values
      (adjacentMergeSortModel values) := by
  have h := mergeUntilOne_correct (singletonRuns values) (singletonRuns_sorted values)
  rw [flatten_singletonRuns] at h
  exact h

/-- 外側 while の一般一致とモデルの正当性から、反復版ソート全体が任意入力で正しい。 -/
theorem mergeSortIterative_correct (values : List Nat) :
    LeanExperiments.Verification.Sorting.Spec.Correct values
      (LeanExperiments.MergeSort.mergeSortIterative values) := by
  rw [mergeSortIterative_eq_adjacentMergeSortModel]
  exact adjacentMergeSortModel_correct values

/-- 反復版の順列保存から、検査器の成功と出力昇順性が同値になる。 -/
theorem mergeSortIterative_check_iff_ascending (values : List Nat) :
    LeanExperiments.Verification.Sorting.Spec.correctCheck values
      (LeanExperiments.MergeSort.mergeSortIterative values) = true ↔
    LeanExperiments.Verification.Sorting.Spec.Ascending
      (LeanExperiments.MergeSort.mergeSortIterative values) :=
  LeanExperiments.Verification.Sorting.Spec.correctCheck_iff_ascending_of_perm
    values _ (mergeSortIterative_correct values).2

/-- 同じ重複数を持つ入力は、順序が違っても反復版ソートで同じ列になる。 -/
theorem mergeSortIterative_eq_of_perm {left right : List Nat}
    (hPerm : List.Perm left right) :
    LeanExperiments.MergeSort.mergeSortIterative left =
      LeanExperiments.MergeSort.mergeSortIterative right :=
  LeanExperiments.Verification.Sorting.Spec.Correct.sort_eq_of_perm_inputs
    LeanExperiments.MergeSort.mergeSortIterative mergeSortIterative_correct hPerm

/-- 反復版ソートは、すでに昇順の入力を変更しない。 -/
theorem mergeSortIterative_eq_self_of_ascending (values : List Nat)
    (hAscending : LeanExperiments.Verification.Sorting.Spec.Ascending values) :
    LeanExperiments.MergeSort.mergeSortIterative values = values :=
  LeanExperiments.Verification.Sorting.Spec.Correct.sort_eq_self_of_ascending
    LeanExperiments.MergeSort.mergeSortIterative mergeSortIterative_correct values hAscending

/-- 反復版ソートを二度適用しても結果は変わらない。 -/
theorem mergeSortIterative_idempotent (values : List Nat) :
    LeanExperiments.MergeSort.mergeSortIterative
      (LeanExperiments.MergeSort.mergeSortIterative values) =
        LeanExperiments.MergeSort.mergeSortIterative values :=
  LeanExperiments.Verification.Sorting.Spec.Correct.sort_idempotent
    LeanExperiments.MergeSort.mergeSortIterative mergeSortIterative_correct values

/-- 固定回数 pass モデルも任意入力を正しくソートする。 -/
theorem adjacentMergeSortPassModel_correct (values : List Nat) :
    LeanExperiments.Verification.Sorting.Spec.Correct values
      (adjacentMergeSortPassModel values) := by
  have h := mergePasses_headD_correct values.length (singletonRuns values)
    (by simp [singletonRuns]) (singletonRuns_sorted values)
  rw [flatten_singletonRuns] at h
  exact h

/-- 再帰版マージソートは、入力と同じ要素を重複込みで保持する。 -/
theorem mergeSort_perm (values : List Nat) :
    List.Perm (LeanExperiments.MergeSort.mergeSort values) values := by
  by_cases hSmall : values.length ≤ 1
  · simp [LeanExperiments.MergeSort.mergeSort, hSmall]
  · rw [LeanExperiments.MergeSort.mergeSort, ite_eq_right hSmall]
    have hLeftLength : (values.take (values.length / 2)).length < values.length := by
      simp [List.length_take]
      omega
    have hRightLength : (values.drop (values.length / 2)).length < values.length := by
      simp [List.length_drop]
      omega
    have hLeft := mergeSort_perm (values.take (values.length / 2))
    have hRight := mergeSort_perm (values.drop (values.length / 2))
    calc
      LeanExperiments.MergeSort.merge
          (LeanExperiments.MergeSort.mergeSort (values.take (values.length / 2)))
          (LeanExperiments.MergeSort.mergeSort (values.drop (values.length / 2))) ~
          LeanExperiments.MergeSort.mergeSort (values.take (values.length / 2)) ++
            LeanExperiments.MergeSort.mergeSort (values.drop (values.length / 2)) :=
        merge_perm_append _ _
      _ ~ values.take (values.length / 2) ++ values.drop (values.length / 2) :=
        hLeft.append hRight
      _ ~ values := List.Perm.of_eq (List.take_append_drop _ _)
termination_by values.length
decreasing_by
  all_goals simp_wf
  all_goals omega

/-- 再帰版マージソートの結果は、任意の入力について昇順である。 -/
theorem mergeSort_pairwise (values : List Nat) :
    (LeanExperiments.MergeSort.mergeSort values).Pairwise (fun a b : Nat => a ≤ b) := by
  by_cases hSmall : values.length ≤ 1
  · cases values with
    | nil => simp [LeanExperiments.MergeSort.mergeSort]
    | cons first rest =>
      cases rest with
      | nil => simp [LeanExperiments.MergeSort.mergeSort]
      | cons second rest => simp at hSmall
  · rw [LeanExperiments.MergeSort.mergeSort, ite_eq_right hSmall]
    exact merge_pairwise _ _ (mergeSort_pairwise _) (mergeSort_pairwise _)
termination_by values.length
decreasing_by
  all_goals simp_wf
  all_goals omega

/-- 再帰版マージソートは任意の入力について共通の正しさ仕様を満たす。 -/
theorem mergeSort_correct (values : List Nat) :
    LeanExperiments.Verification.Sorting.Spec.Correct values
      (LeanExperiments.MergeSort.mergeSort values) := by
  simpa only [MergeTree.ofList_input, MergeTree.ofList_eval] using
    (MergeTree.ofList values).correct (MergeTree.ofList_runsAscending values)

/-- 再帰版ソートは、順列関係にある入力へ同じ結果を返す。 -/
theorem mergeSort_eq_of_perm {left right : List Nat}
    (hPerm : List.Perm left right) :
    LeanExperiments.MergeSort.mergeSort left =
      LeanExperiments.MergeSort.mergeSort right :=
  LeanExperiments.Verification.Sorting.Spec.Correct.sort_eq_of_perm_inputs
    LeanExperiments.MergeSort.mergeSort mergeSort_correct hPerm

/-- 再帰版ソートは、昇順入力を変更しない。 -/
theorem mergeSort_eq_self_of_ascending (values : List Nat)
    (hAscending : LeanExperiments.Verification.Sorting.Spec.Ascending values) :
    LeanExperiments.MergeSort.mergeSort values = values :=
  LeanExperiments.Verification.Sorting.Spec.Correct.sort_eq_self_of_ascending
    LeanExperiments.MergeSort.mergeSort mergeSort_correct values hAscending

/-- 再帰版ソートを二度適用しても結果は変わらない。 -/
theorem mergeSort_idempotent (values : List Nat) :
    LeanExperiments.MergeSort.mergeSort (LeanExperiments.MergeSort.mergeSort values) =
      LeanExperiments.MergeSort.mergeSort values :=
  LeanExperiments.Verification.Sorting.Spec.Correct.sort_idempotent
    LeanExperiments.MergeSort.mergeSort mergeSort_correct values

/-- `Correct` を満たす任意のソート関数では、連結入力のソートは部分結果の `merge` に一致する。 -/
theorem correct_sort_append_eq_merge
    (sorter : List Nat → List Nat)
    (hSorter : ∀ values,
      LeanExperiments.Verification.Sorting.Spec.Correct values (sorter values))
    (left right : List Nat) :
    sorter (left ++ right) =
      LeanExperiments.MergeSort.merge (sorter left) (sorter right) := by
  have hLeft := hSorter left
  have hRight := hSorter right
  have hWhole := hSorter (left ++ right)
  have hParts := LeanExperiments.Verification.MergeSort.merge_correct
    (sorter left) (sorter right) hLeft.1 hRight.1
  have hInputs : (left ++ right).Perm (sorter left ++ sorter right) := by
    exact hLeft.2.symm.append hRight.2.symm
  exact LeanExperiments.Verification.Sorting.Spec.Correct.eq_of_perm_inputs
    hWhole hParts hInputs

/-- 連結した入力の再帰版ソートは、各部分のソート結果を `merge` した結果に一致する。 -/
theorem mergeSort_append_eq_merge (left right : List Nat) :
    LeanExperiments.MergeSort.mergeSort (left ++ right) =
      LeanExperiments.MergeSort.merge
        (LeanExperiments.MergeSort.mergeSort left)
        (LeanExperiments.MergeSort.mergeSort right) :=
  correct_sort_append_eq_merge
    LeanExperiments.MergeSort.mergeSort mergeSort_correct left right

/-- 連結した入力の命令版ソートも、部分ソート結果の `merge` と一致する。 -/
theorem mergeSortIterative_append_eq_merge (left right : List Nat) :
    LeanExperiments.MergeSort.mergeSortIterative (left ++ right) =
      LeanExperiments.MergeSort.merge
        (LeanExperiments.MergeSort.mergeSortIterative left)
        (LeanExperiments.MergeSort.mergeSortIterative right) :=
  correct_sort_append_eq_merge
    LeanExperiments.MergeSort.mergeSortIterative mergeSortIterative_correct left right

/-- 再帰版マージソートは任意の条件による絞り込みと可換である。 -/
theorem mergeSort_filter (values : List Nat) (predicate : Nat → Bool) :
    LeanExperiments.MergeSort.mergeSort (values.filter predicate) =
      (LeanExperiments.MergeSort.mergeSort values).filter predicate :=
  LeanExperiments.Verification.Sorting.Spec.Correct.sort_filter
    LeanExperiments.MergeSort.mergeSort mergeSort_correct values predicate

/-- 命令版マージソートも任意の条件による絞り込みと可換である。 -/
theorem mergeSortIterative_filter (values : List Nat) (predicate : Nat → Bool) :
    LeanExperiments.MergeSort.mergeSortIterative (values.filter predicate) =
      (LeanExperiments.MergeSort.mergeSortIterative values).filter predicate :=
  LeanExperiments.Verification.Sorting.Spec.Correct.sort_filter
    LeanExperiments.MergeSort.mergeSortIterative mergeSortIterative_correct values predicate

/-- 再帰版マージソートは非減少関数による写像と可換である。 -/
theorem mergeSort_map (values : List Nat) (f : Nat → Nat)
    (hMonotone : ∀ ⦃a b⦄, a ≤ b → f a ≤ f b) :
    LeanExperiments.MergeSort.mergeSort (values.map f) =
      (LeanExperiments.MergeSort.mergeSort values).map f :=
  LeanExperiments.Verification.Sorting.Spec.Correct.sort_map
    LeanExperiments.MergeSort.mergeSort mergeSort_correct values f hMonotone

/-- 命令版マージソートも非減少関数による写像と可換である。 -/
theorem mergeSortIterative_map (values : List Nat) (f : Nat → Nat)
    (hMonotone : ∀ ⦃a b⦄, a ≤ b → f a ≤ f b) :
    LeanExperiments.MergeSort.mergeSortIterative (values.map f) =
      (LeanExperiments.MergeSort.mergeSortIterative values).map f :=
  LeanExperiments.Verification.Sorting.Spec.Correct.sort_map
    LeanExperiments.MergeSort.mergeSortIterative mergeSortIterative_correct values f hMonotone

/-- 再帰版の順列保存から、検査器の成功と出力昇順性が同値になる。 -/
theorem mergeSort_check_iff_ascending (values : List Nat) :
    LeanExperiments.Verification.Sorting.Spec.correctCheck values
      (LeanExperiments.MergeSort.mergeSort values) = true ↔
    LeanExperiments.Verification.Sorting.Spec.Ascending
      (LeanExperiments.MergeSort.mergeSort values) :=
  LeanExperiments.Verification.Sorting.Spec.correctCheck_iff_ascending_of_perm
    values _ (mergeSort_correct values).2

/-- 反復版と再帰版ソートは、任意入力について同じ結果を返す。 -/
theorem mergeSortIterative_agrees_with_mergeSort (values : List Nat) :
    LeanExperiments.MergeSort.mergeSortIterative values =
      LeanExperiments.MergeSort.mergeSort values :=
  LeanExperiments.Verification.Sorting.Spec.Correct.eq_of_same_input
    (mergeSortIterative_correct values) (mergeSort_correct values)

/-- 再帰版マージソートの各出力位置は、入力中の順位条件で特徴付けられる。

重複値も含め、値より小さい入力要素数と値以下の入力要素数がその順位を正確に定める。
-/
theorem mergeSort_getElem_eq_iff_rank_bounds (values : List Nat)
    (index : Nat) (hIndex : index <
      (LeanExperiments.MergeSort.mergeSort values).length) (value : Nat) :
    (LeanExperiments.MergeSort.mergeSort values)[index] = value ↔
      values.countP (fun item => decide (item < value)) ≤ index ∧
        index < values.countP (fun item => decide (item ≤ value)) :=
  LeanExperiments.Verification.Sorting.Spec.Correct.getElem_eq_iff_rank_bounds
    (mergeSort_correct values) hIndex value

/-- 反復版マージソートの各出力位置にも、同じ一般順位特徴付けが成り立つ。 -/
theorem mergeSortIterative_getElem_eq_iff_rank_bounds (values : List Nat)
    (index : Nat) (hIndex : index <
      (LeanExperiments.MergeSort.mergeSortIterative values).length) (value : Nat) :
    (LeanExperiments.MergeSort.mergeSortIterative values)[index] = value ↔
      values.countP (fun item => decide (item < value)) ≤ index ∧
        index < values.countP (fun item => decide (item ≤ value)) :=
  LeanExperiments.Verification.Sorting.Spec.Correct.getElem_eq_iff_rank_bounds
    (mergeSortIterative_correct values) hIndex value

/-- 再帰版の先頭 `k` 個に含まれる、しきい値以下の値の個数を入力から決める。 -/
theorem mergeSort_take_countP_le (values : List Nat) (k threshold : Nat) :
    ((LeanExperiments.MergeSort.mergeSort values).take k).countP
        (fun value => decide (value ≤ threshold)) =
      min k (values.countP (fun value => decide (value ≤ threshold))) :=
  LeanExperiments.Verification.Sorting.Spec.Correct.countP_take_le
    (mergeSort_correct values) k threshold

/-- 再帰版の先頭 `k` 個に含まれる、しきい値より大きい値の個数を特徴付ける。 -/
theorem mergeSort_take_countP_gt (values : List Nat) (k threshold : Nat) :
    ((LeanExperiments.MergeSort.mergeSort values).take k).countP
        (fun value => decide (threshold < value)) =
      min (values.countP (fun value => decide (threshold < value)))
        (k - values.countP (fun value => decide (value ≤ threshold))) :=
  LeanExperiments.Verification.Sorting.Spec.Correct.countP_take_gt
    (mergeSort_correct values) k threshold

/-- 再帰版の先頭 `k` 個に含まれる、しきい値以上の値の個数を特徴付ける。 -/
theorem mergeSort_take_countP_ge (values : List Nat) (k threshold : Nat) :
    ((LeanExperiments.MergeSort.mergeSort values).take k).countP
        (fun value => decide (threshold ≤ value)) =
      min (values.countP (fun value => decide (threshold ≤ value)))
        (k - values.countP (fun value => decide (value < threshold))) :=
  LeanExperiments.Verification.Sorting.Spec.Correct.countP_take_ge
    (mergeSort_correct values) k threshold

/-- 反復版の先頭 `k` 個に含まれる、しきい値以下の値の個数を入力から決める。 -/
theorem mergeSortIterative_take_countP_le (values : List Nat) (k threshold : Nat) :
    ((LeanExperiments.MergeSort.mergeSortIterative values).take k).countP
        (fun value => decide (value ≤ threshold)) =
      min k (values.countP (fun value => decide (value ≤ threshold))) :=
  LeanExperiments.Verification.Sorting.Spec.Correct.countP_take_le
    (mergeSortIterative_correct values) k threshold

/-- 反復版の先頭 `k` 個に含まれる、しきい値より大きい値の個数を特徴付ける。 -/
theorem mergeSortIterative_take_countP_gt (values : List Nat) (k threshold : Nat) :
    ((LeanExperiments.MergeSort.mergeSortIterative values).take k).countP
        (fun value => decide (threshold < value)) =
      min (values.countP (fun value => decide (threshold < value)))
        (k - values.countP (fun value => decide (value ≤ threshold))) :=
  LeanExperiments.Verification.Sorting.Spec.Correct.countP_take_gt
    (mergeSortIterative_correct values) k threshold

/-- 反復版の先頭 `k` 個に含まれる、しきい値以上の値の個数を特徴付ける。 -/
theorem mergeSortIterative_take_countP_ge (values : List Nat) (k threshold : Nat) :
    ((LeanExperiments.MergeSort.mergeSortIterative values).take k).countP
        (fun value => decide (threshold ≤ value)) =
      min (values.countP (fun value => decide (threshold ≤ value)))
        (k - values.countP (fun value => decide (value < threshold))) :=
  LeanExperiments.Verification.Sorting.Spec.Correct.countP_take_ge
    (mergeSortIterative_correct values) k threshold

/-- チャンクの順序を入れ替えても、連結したリストの要素は順列として保存される。 -/
theorem flatten_perm_of_chunk_perm {chunks other : List (List Nat)}
    (hChunks : chunks.Perm other) : chunks.flatten.Perm other.flatten := by
  induction hChunks with
  | nil => exact List.Perm.nil
  | cons chunk _ ih =>
      simpa only [List.flatten_cons] using ih.append_left chunk
  | swap first second rest =>
      simp only [List.flatten_cons]
      calc
        second ++ (first ++ rest.flatten) ~
            (second ++ first) ++ rest.flatten :=
              List.Perm.of_eq (by simp [List.append_assoc])
        _ ~ (first ++ second) ++ rest.flatten :=
              List.perm_append_comm.append_right rest.flatten
        _ ~ first ++ (second ++ rest.flatten) :=
              List.Perm.of_eq (by simp [List.append_assoc])
  | trans _ _ ihFirst ihSecond => exact ihFirst.trans ihSecond

/-- `Correct` を満たすソート関数の結果は、チャンクの順序変更に影響されない。 -/
theorem correct_sort_flatten_perm
    (sorter : List Nat → List Nat)
    (hSorter : ∀ values,
      LeanExperiments.Verification.Sorting.Spec.Correct values (sorter values))
    {chunks other : List (List Nat)} (hChunks : chunks.Perm other) :
    sorter chunks.flatten = sorter other.flatten := by
  exact LeanExperiments.Verification.Sorting.Spec.Correct.eq_of_perm_inputs
    (hSorter chunks.flatten) (hSorter other.flatten)
    (flatten_perm_of_chunk_perm hChunks)

/-- `Correct` な任意のソート関数は、連結入力をソートした結果とチャンクごとの右併合が一致する。 -/
theorem correct_sort_flatten_eq_foldMerge
    (sorter : List Nat → List Nat)
    (hSorter : ∀ values,
      LeanExperiments.Verification.Sorting.Spec.Correct values (sorter values))
    (chunks : List (List Nat)) :
    sorter chunks.flatten =
      chunks.foldr
        (fun chunk merged =>
          LeanExperiments.MergeSort.merge
            (sorter chunk) merged) [] := by
  induction chunks with
  | nil =>
      cases hOutput : sorter [] with
      | nil =>
          change sorter [] = []
          exact hOutput
      | cons first rest =>
          have hLength := (hSorter []).length_eq
          simp [hOutput] at hLength
  | cons chunk rest ih =>
      change sorter (chunk ++ List.flatten rest) = _
      calc
        sorter (chunk ++ List.flatten rest) =
            LeanExperiments.MergeSort.merge
              (sorter chunk) (sorter (List.flatten rest)) :=
                correct_sort_append_eq_merge sorter hSorter chunk _
        _ = LeanExperiments.MergeSort.merge
              (sorter chunk)
              (rest.foldr
                (fun next merged =>
                  LeanExperiments.MergeSort.merge
                    (sorter next) merged) []) := by
                rw [ih]
        _ = (chunk :: rest).foldr
              (fun next merged =>
                LeanExperiments.MergeSort.merge
                  (sorter next) merged) [] := rfl

/-- 共通仕様を満たすソート関数では、チャンク列の順列変更で右畳み込みの併合結果も変わらない。 -/
theorem correct_sort_foldMerge_eq_of_chunk_perm
    (sorter : List Nat → List Nat)
    (hSorter : ∀ values,
      LeanExperiments.Verification.Sorting.Spec.Correct values (sorter values))
    {chunks other : List (List Nat)} (hChunks : chunks.Perm other) :
    chunks.foldr
        (fun chunk merged =>
          LeanExperiments.MergeSort.merge (sorter chunk) merged) [] =
      other.foldr
        (fun chunk merged =>
          LeanExperiments.MergeSort.merge (sorter chunk) merged) [] := by
  rw [← correct_sort_flatten_eq_foldMerge sorter hSorter chunks,
    ← correct_sort_flatten_eq_foldMerge sorter hSorter other]
  exact correct_sort_flatten_perm sorter hSorter hChunks

/-- 再帰版マージソートは任意個のチャンク分割に対する一般併合則を満たす。 -/
theorem mergeSort_flatten_eq_foldMerge (chunks : List (List Nat)) :
    LeanExperiments.MergeSort.mergeSort chunks.flatten =
      chunks.foldr
        (fun chunk merged =>
          LeanExperiments.MergeSort.merge
            (LeanExperiments.MergeSort.mergeSort chunk) merged) [] :=
  correct_sort_flatten_eq_foldMerge
    LeanExperiments.MergeSort.mergeSort mergeSort_correct chunks

/-- 任意個のチャンクに対する命令版ソートも、再帰版の順次併合結果と一致する。 -/
theorem mergeSortIterative_flatten_eq_foldMerge (chunks : List (List Nat)) :
    LeanExperiments.MergeSort.mergeSortIterative chunks.flatten =
      chunks.foldr
        (fun chunk merged =>
          LeanExperiments.MergeSort.merge
            (LeanExperiments.MergeSort.mergeSortIterative chunk) merged) [] := by
  exact correct_sort_flatten_eq_foldMerge
    LeanExperiments.MergeSort.mergeSortIterative mergeSortIterative_correct chunks

/-- 隣接併合モデルは共通仕様を満たすため、再帰版ソートと同じ結果になる。 -/
theorem adjacentMergeSortModel_agrees_with_mergeSort (values : List Nat) :
    adjacentMergeSortModel values = LeanExperiments.MergeSort.mergeSort values :=
  LeanExperiments.Verification.Sorting.Spec.Correct.eq_of_same_input
    (adjacentMergeSortModel_correct values) (mergeSort_correct values)

/-- 固定 pass 数モデルも、共通仕様の一意性により再帰版と一致する。 -/
theorem adjacentMergeSortPassModel_agrees_with_mergeSort (values : List Nat) :
    adjacentMergeSortPassModel values = LeanExperiments.MergeSort.mergeSort values :=
  LeanExperiments.Verification.Sorting.Spec.Correct.eq_of_same_input
    (adjacentMergeSortPassModel_correct values) (mergeSort_correct values)

/-- ループ版が共通検査に通ることと、再帰版の結果と一致することは同値。 -/
theorem mergeSortIterative_correct_iff_agrees (values : List Nat) :
    LeanExperiments.Verification.Sorting.Spec.correctCheck values
      (LeanExperiments.MergeSort.mergeSortIterative values) = true ↔
    LeanExperiments.MergeSort.mergeSortIterative values =
      LeanExperiments.MergeSort.mergeSort values := by
  constructor
  · intro hCheck
    exact LeanExperiments.Verification.Sorting.Spec.Correct.eq_of_same_input
      (LeanExperiments.Verification.Sorting.Spec.correctCheck_sound values _ hCheck)
      (mergeSort_correct values)
  · intro hAgree
    rw [hAgree]
    exact LeanExperiments.Verification.Sorting.Spec.correctCheck_complete values
      (LeanExperiments.MergeSort.mergeSort values) (mergeSort_correct values)

/-- 空リストはそのまま空リストになる。 -/
theorem mergeSort_empty : LeanExperiments.MergeSort.mergeSort [] = [] := by
  simp [LeanExperiments.MergeSort.mergeSort]

/-- 重複値を保持しながら昇順に並ぶ。 -/
theorem mergeSort_duplicates_example :
    LeanExperiments.MergeSort.mergeSort [7, 2, 5, 2, 0, 9] = [0, 2, 2, 5, 7, 9] := by
  native_decide

/-- 逆順の値も昇順へ並べ替える。 -/
theorem mergeSort_reverseInput_example :
    LeanExperiments.MergeSort.mergeSort [9, 8, 7, 6, 5, 4, 3, 2, 1, 0] =
      [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] := by
  native_decide

/-- ループ版は空入力を空のまま返す。 -/
theorem mergeSortIterative_empty_boundary :
    LeanExperiments.MergeSort.mergeSortIterative [] = [] := by
  native_decide

/-- ループ版も重複値を保持して昇順に並べ替える。 -/
theorem mergeSortIterative_duplicates_example :
    LeanExperiments.MergeSort.mergeSortIterative [7, 2, 5, 2, 0, 9] =
      [0, 2, 2, 5, 7, 9] := by
  native_decide

/-- 再帰版とループ版が代表的な重複値入力で一致する。 -/
theorem mergeSort_implementations_agree_example :
    LeanExperiments.MergeSort.mergeSort [7, 2, 5, 2, 0, 9] =
      LeanExperiments.MergeSort.mergeSortIterative [7, 2, 5, 2, 0, 9] := by
  native_decide

/-! ## 有限領域の網羅確認

長さ 0〜5、値 0〜2 の全 364 入力に対し、昇順性と要素保存を別々に含む共通仕様を
両実装が満たすこと、さらに両者が同じ結果を返すことを確認する。
これは有限領域の計算確認であり、任意の自然数列についての一般証明ではない。 -/

/-- 再帰版が有限領域の全入力で共通のソート仕様を満たす。 -/
def mergeSortBoundedCheck : Bool :=
  LeanExperiments.Verification.Sorting.Spec.boundedInputs.all fun input =>
    LeanExperiments.Verification.Sorting.Spec.correctCheck input
      (LeanExperiments.MergeSort.mergeSort input)

/-- ループ版が有限領域の全入力で共通のソート仕様を満たす。 -/
def mergeSortIterativeBoundedCheck : Bool :=
  LeanExperiments.Verification.Sorting.Spec.boundedInputs.all fun input =>
    LeanExperiments.Verification.Sorting.Spec.correctCheck input
      (LeanExperiments.MergeSort.mergeSortIterative input)

/-- 有限領域の全入力で再帰版とループ版の出力が一致する。 -/
def mergeSortAgreementBoundedCheck : Bool :=
  LeanExperiments.Verification.Sorting.Spec.boundedInputs.all fun input =>
    decide (LeanExperiments.MergeSort.mergeSort input =
      LeanExperiments.MergeSort.mergeSortIterative input)

/-- 364 入力全てで再帰版の昇順性と要素保存を確認する。 -/
theorem mergeSortBoundedCheck_passes : mergeSortBoundedCheck = true := by
  native_decide

/-- 364 入力全てでループ版の昇順性と要素保存を確認する。 -/
theorem mergeSortIterativeBoundedCheck_passes : mergeSortIterativeBoundedCheck = true := by
  native_decide

/-- 364 入力全てで両実装の結果が一致する。 -/
theorem mergeSortAgreementBoundedCheck_passes : mergeSortAgreementBoundedCheck = true := by
  native_decide

/-- より広い有限領域でループ版の昇順性と要素保存を確認する。 -/
def mergeSortIterativeStressCheck : Bool :=
  LeanExperiments.Verification.Sorting.Spec.stressInputs.all fun input =>
    LeanExperiments.Verification.Sorting.Spec.correctCheck input
      (LeanExperiments.MergeSort.mergeSortIterative input)

/-- 長さ 0〜8、値 0〜3 の全 87,381 入力でループ版の仕様が成立する。 -/
theorem mergeSortIterativeStressCheck_passes : mergeSortIterativeStressCheck = true := by
  native_decide

/-- より広い有限領域で再帰版とループ版の一致を確認する。 -/
def mergeSortAgreementStressCheck : Bool :=
  LeanExperiments.Verification.Sorting.Spec.stressInputs.all fun input =>
    decide (LeanExperiments.MergeSort.mergeSort input =
      LeanExperiments.MergeSort.mergeSortIterative input)

/-- 長さ 0〜8、値 0〜3 の全 87,381 入力で両実装が一致する。 -/
theorem mergeSortAgreementStressCheck_passes : mergeSortAgreementStressCheck = true := by
  native_decide

/-! ## 大きな値を含む全列挙確認

値の桁が大きく異なる入力や最大64 bit値の重複を含め、長さ0〜7の97,656入力について
再帰版・ループ版の仕様と両者の一致を確認する。 -/

/-- 大きな値を含む全入力で再帰版が共通仕様を満たす。 -/
def mergeSortWideValueCheck : Bool :=
  LeanExperiments.Verification.Sorting.Spec.wideValueInputs.all fun input =>
    LeanExperiments.Verification.Sorting.Spec.correctCheck input
      (LeanExperiments.MergeSort.mergeSort input)

/-- 大きな値を含む全入力でループ版が共通仕様を満たす。 -/
def mergeSortIterativeWideValueCheck : Bool :=
  LeanExperiments.Verification.Sorting.Spec.wideValueInputs.all fun input =>
    LeanExperiments.Verification.Sorting.Spec.correctCheck input
      (LeanExperiments.MergeSort.mergeSortIterative input)

/-- 大きな値を含む全入力で再帰版とループ版の結果が一致する。 -/
def mergeSortAgreementWideValueCheck : Bool :=
  LeanExperiments.Verification.Sorting.Spec.wideValueInputs.all fun input =>
    decide (LeanExperiments.MergeSort.mergeSort input =
      LeanExperiments.MergeSort.mergeSortIterative input)

/-- 97,656入力全てで再帰版の仕様が成立する。 -/
theorem mergeSortWideValueCheck_passes : mergeSortWideValueCheck = true := by
  native_decide

/-- 97,656入力全てでループ版の仕様が成立する。 -/
theorem mergeSortIterativeWideValueCheck_passes :
    mergeSortIterativeWideValueCheck = true := by
  native_decide

/-- 97,656入力全てで両実装の結果が一致する。 -/
theorem mergeSortAgreementWideValueCheck_passes :
    mergeSortAgreementWideValueCheck = true := by
  native_decide

/-! ## 偏りのある長い入力

小さい値域の網羅確認とは別に、長さ64および63・65・127・128・129・255・256・257・511・512・513の整列済み・逆順・同値・周期列を確認する。
quick sort の分割偏りや、ループ版の複数回併合を含む入力形状を狙った確認である。
-/

/-- 偏り入力全てで再帰版が共通仕様を満たす。 -/
def mergeSortAdversarialCheck : Bool :=
  LeanExperiments.Verification.Sorting.Spec.adversarialInputs.all fun input =>
    LeanExperiments.Verification.Sorting.Spec.correctCheck input
      (LeanExperiments.MergeSort.mergeSort input)

/-- 偏り入力全てでループ版が共通仕様を満たす。 -/
def mergeSortIterativeAdversarialCheck : Bool :=
  LeanExperiments.Verification.Sorting.Spec.adversarialInputs.all fun input =>
    LeanExperiments.Verification.Sorting.Spec.correctCheck input
      (LeanExperiments.MergeSort.mergeSortIterative input)

/-- 偏り入力全てで再帰版とループ版の結果が一致する。 -/
def mergeSortAgreementAdversarialCheck : Bool :=
  LeanExperiments.Verification.Sorting.Spec.adversarialInputs.all fun input =>
    decide (LeanExperiments.MergeSort.mergeSort input =
      LeanExperiments.MergeSort.mergeSortIterative input)

/-- 全ての偏り入力で再帰版の昇順性と要素保存を確認する。 -/
theorem mergeSortAdversarialCheck_passes : mergeSortAdversarialCheck = true := by
  native_decide

/-- 全ての偏り入力でループ版の昇順性と要素保存を確認する。 -/
theorem mergeSortIterativeAdversarialCheck_passes :
    mergeSortIterativeAdversarialCheck = true := by
  native_decide

/-- 全ての偏り入力で再帰版とループ版の一致を確認する。 -/
theorem mergeSortAgreementAdversarialCheck_passes :
    mergeSortAgreementAdversarialCheck = true := by
  native_decide

/-! ## 長さと64ビット値幅を組み合わせた確認 -/

/-- 共通の48境界値入力で再帰版が仕様を満たす。 -/
def mergeSortWideAdversarialCheck : Bool :=
  LeanExperiments.Verification.Sorting.Spec.wideAdversarialInputs.all fun input =>
    LeanExperiments.Verification.Sorting.Spec.correctCheck input
      (LeanExperiments.MergeSort.mergeSort input)

/-- 共通の48境界値入力でループ版が仕様を満たす。 -/
def mergeSortIterativeWideAdversarialCheck : Bool :=
  LeanExperiments.Verification.Sorting.Spec.wideAdversarialInputs.all fun input =>
    LeanExperiments.Verification.Sorting.Spec.correctCheck input
      (LeanExperiments.MergeSort.mergeSortIterative input)

/-- 共通の48境界値入力で二つの実装結果が一致する。 -/
def mergeSortAgreementWideAdversarialCheck : Bool :=
  LeanExperiments.Verification.Sorting.Spec.wideAdversarialInputs.all fun input =>
    decide (LeanExperiments.MergeSort.mergeSort input =
      LeanExperiments.MergeSort.mergeSortIterative input)

/-- 48入力全てで再帰版が仕様を満たす。 -/
theorem mergeSortWideAdversarialCheck_passes :
    mergeSortWideAdversarialCheck = true := by
  native_decide

/-- 48入力全てでループ版が仕様を満たす。 -/
theorem mergeSortIterativeWideAdversarialCheck_passes :
    mergeSortIterativeWideAdversarialCheck = true := by
  native_decide

/-- 48入力全てで再帰版とループ版の結果が一致する。 -/
theorem mergeSortAgreementWideAdversarialCheck_passes :
    mergeSortAgreementWideAdversarialCheck = true := by
  native_decide

/-! ## 1024 要素付近の大規模境界確認 -/

/-- 1023・1024・1025要素の入力全てでループ版の仕様を確認する。 -/
def mergeSortIterativeLargeAdversarialCheck : Bool :=
  LeanExperiments.Verification.Sorting.Spec.largeAdversarialInputs.all fun input =>
    LeanExperiments.Verification.Sorting.Spec.correctCheck input
      (LeanExperiments.MergeSort.mergeSortIterative input)

/-- 1023・1024・1025要素の入力全てで再帰版との一致を確認する。 -/
def mergeSortAgreementLargeAdversarialCheck : Bool :=
  LeanExperiments.Verification.Sorting.Spec.largeAdversarialInputs.all fun input =>
    decide (LeanExperiments.MergeSort.mergeSort input =
      LeanExperiments.MergeSort.mergeSortIterative input)

/-- 12種類の大規模入力全てでループ版の昇順性と要素保存が成り立つ。 -/
theorem mergeSortIterativeLargeAdversarialCheck_passes :
    mergeSortIterativeLargeAdversarialCheck = true := by
  native_decide

/-- 12種類の大規模入力全てで再帰版とループ版が一致する。 -/
theorem mergeSortAgreementLargeAdversarialCheck_passes :
    mergeSortAgreementLargeAdversarialCheck = true := by
  native_decide

/-- 64ビット境界値を含む大規模入力で、ループ版の仕様適合を調べる。 -/
def mergeSortIterativeLargeWideAdversarialCheck : Bool :=
  LeanExperiments.Verification.Sorting.Spec.largeWideAdversarialInputs.all fun input =>
    LeanExperiments.Verification.Sorting.Spec.correctCheck input
      (LeanExperiments.MergeSort.mergeSortIterative input)

/-- 64ビット境界値を含む大規模入力で、再帰版との出力一致を調べる。 -/
def mergeSortAgreementLargeWideAdversarialCheck : Bool :=
  LeanExperiments.Verification.Sorting.Spec.largeWideAdversarialInputs.all fun input =>
    decide (LeanExperiments.MergeSort.mergeSort input =
      LeanExperiments.MergeSort.mergeSortIterative input)

/-- 1023〜1025要素の64ビット境界値入力12件全てでループ版の仕様が成立する。 -/
theorem mergeSortIterativeLargeWideAdversarialCheck_passes :
    mergeSortIterativeLargeWideAdversarialCheck = true := by
  native_decide

/-- 1023〜1025要素の64ビット境界値入力12件全てで両版の結果が一致する。 -/
theorem mergeSortAgreementLargeWideAdversarialCheck_passes :
    mergeSortAgreementLargeWideAdversarialCheck = true := by
  native_decide

/-- 大きな64ビット境界値入力ごとに、ループ版の `Correct` を取り出す。 -/
theorem mergeSortIterative_correct_for_largeWideAdversarialInput (input : List Nat)
    (hInput : input ∈ LeanExperiments.Verification.Sorting.Spec.largeWideAdversarialInputs) :
    LeanExperiments.Verification.Sorting.Spec.Correct input
      (LeanExperiments.MergeSort.mergeSortIterative input) := by
  have hAll := List.all_eq_true.mp mergeSortIterativeLargeWideAdversarialCheck_passes
  exact LeanExperiments.Verification.Sorting.Spec.correctCheck_sound input _ (hAll input hInput)

/-- 境界値入力に含まれる任意の列で、再帰版の `Correct` を取り出せる。 -/
theorem mergeSort_correct_for_wideAdversarialInput (input : List Nat)
    (hInput : input ∈ LeanExperiments.Verification.Sorting.Spec.wideAdversarialInputs) :
    LeanExperiments.Verification.Sorting.Spec.Correct input
      (LeanExperiments.MergeSort.mergeSort input) := by
  have hAll : ∀ candidate ∈ LeanExperiments.Verification.Sorting.Spec.wideAdversarialInputs,
      LeanExperiments.Verification.Sorting.Spec.correctCheck candidate
        (LeanExperiments.MergeSort.mergeSort candidate) = true :=
    List.all_eq_true.mp mergeSortWideAdversarialCheck_passes
  exact LeanExperiments.Verification.Sorting.Spec.correctCheck_sound input _ (hAll input hInput)

/-- 境界値入力に含まれる任意の列で、ループ版の `Correct` を取り出せる。 -/
theorem mergeSortIterative_correct_for_wideAdversarialInput (input : List Nat)
    (hInput : input ∈ LeanExperiments.Verification.Sorting.Spec.wideAdversarialInputs) :
    LeanExperiments.Verification.Sorting.Spec.Correct input
      (LeanExperiments.MergeSort.mergeSortIterative input) := by
  have hAll : ∀ candidate ∈ LeanExperiments.Verification.Sorting.Spec.wideAdversarialInputs,
      LeanExperiments.Verification.Sorting.Spec.correctCheck candidate
        (LeanExperiments.MergeSort.mergeSortIterative candidate) = true :=
    List.all_eq_true.mp mergeSortIterativeWideAdversarialCheck_passes
  exact LeanExperiments.Verification.Sorting.Spec.correctCheck_sound input _ (hAll input hInput)

/-- 偏り入力の有限領域に含まれる入力について、ループ版の `Correct` を取り出せる。 -/
theorem mergeSortIterative_correct_for_adversarialInput (input : List Nat)
    (hInput : input ∈ LeanExperiments.Verification.Sorting.Spec.adversarialInputs) :
    LeanExperiments.Verification.Sorting.Spec.Correct input
      (LeanExperiments.MergeSort.mergeSortIterative input) := by
  have hAll : ∀ candidate ∈ LeanExperiments.Verification.Sorting.Spec.adversarialInputs,
      LeanExperiments.Verification.Sorting.Spec.correctCheck candidate
        (LeanExperiments.MergeSort.mergeSortIterative candidate) = true :=
    List.all_eq_true.mp mergeSortIterativeAdversarialCheck_passes
  exact LeanExperiments.Verification.Sorting.Spec.correctCheck_sound input _ (hAll input hInput)

/-- 有限領域に含まれる入力について、再帰版の `Correct` を得る。 -/
theorem mergeSort_correct_for_boundedInput (input : List Nat)
    (hInput : input ∈ LeanExperiments.Verification.Sorting.Spec.boundedInputs) :
    LeanExperiments.Verification.Sorting.Spec.Correct input
      (LeanExperiments.MergeSort.mergeSort input) := by
  have hAll : ∀ candidate ∈ LeanExperiments.Verification.Sorting.Spec.boundedInputs,
      LeanExperiments.Verification.Sorting.Spec.correctCheck candidate
        (LeanExperiments.MergeSort.mergeSort candidate) = true :=
    List.all_eq_true.mp mergeSortBoundedCheck_passes
  exact LeanExperiments.Verification.Sorting.Spec.correctCheck_sound input _ (hAll input hInput)

/-- 有限領域に含まれる入力について、ループ版の `Correct` を得る。 -/
theorem mergeSortIterative_correct_for_boundedInput (input : List Nat)
    (hInput : input ∈ LeanExperiments.Verification.Sorting.Spec.boundedInputs) :
    LeanExperiments.Verification.Sorting.Spec.Correct input
      (LeanExperiments.MergeSort.mergeSortIterative input) := by
  have hAll : ∀ candidate ∈ LeanExperiments.Verification.Sorting.Spec.boundedInputs,
      LeanExperiments.Verification.Sorting.Spec.correctCheck candidate
        (LeanExperiments.MergeSort.mergeSortIterative candidate) = true :=
    List.all_eq_true.mp mergeSortIterativeBoundedCheck_passes
  exact LeanExperiments.Verification.Sorting.Spec.correctCheck_sound input _ (hAll input hInput)

/-- 有限領域に含まれる入力について、両実装の結果が等しい。 -/
theorem mergeSort_implementations_agree_for_boundedInput (input : List Nat)
    (hInput : input ∈ LeanExperiments.Verification.Sorting.Spec.boundedInputs) :
    LeanExperiments.MergeSort.mergeSort input =
      LeanExperiments.MergeSort.mergeSortIterative input := by
  have hAll : ∀ candidate ∈ LeanExperiments.Verification.Sorting.Spec.boundedInputs,
      decide (LeanExperiments.MergeSort.mergeSort candidate =
        LeanExperiments.MergeSort.mergeSortIterative candidate) = true :=
    List.all_eq_true.mp mergeSortAgreementBoundedCheck_passes
  exact of_decide_eq_true (hAll input hInput)

end LeanExperiments.Verification.MergeSort
