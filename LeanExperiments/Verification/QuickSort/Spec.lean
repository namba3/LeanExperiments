import LeanExperiments.QuickSort
import LeanExperiments.Verification.Sorting.Spec
import LeanExperiments.Verification.MergeSort.Spec
import Std.WP
import Std.Tactic.Do

/-!
# クイックソートの計算例

境界値、重複値、逆順の入力で pivot 分割の結果をカーネル内で確認する。
再帰版とループ版は任意の入力について共通の正当性仕様を満たすことを証明し、
有限領域の検査は境界回帰確認として補助的に使う。
-/

namespace LeanExperiments.Verification.QuickSort

open List
open Std.WP Lean.Order
set_option experimental.vcgen true

private def quickSortTaskOutput : LeanExperiments.QuickSort.QuickSortTask → List Nat
  | .sort values => LeanExperiments.QuickSort.quickSort values
  | .emit value => [value]

/-- スタックを次に実行する順に並べたとき、各タスクが生成する出力を連結する。 -/
private def quickSortTaskStackOutput
    (tasks : Array LeanExperiments.QuickSort.QuickSortTask) : List Nat :=
  tasks.toList.reverse.flatMap quickSortTaskOutput

/-- 出力済み列とタスクスタックが表す列を連結した、ループ版の意味的不変条件。 -/
def quickSortIterativeInvariant (values : List Nat)
    (state : Array LeanExperiments.QuickSort.QuickSortTask × Array Nat) : Prop :=
  state.2.toList ++ quickSortTaskStackOutput state.1 =
    LeanExperiments.QuickSort.quickSort values

/-- どのタスクも停止測度が正である。 -/
private theorem quickSortTaskPotential_pos
    (task : LeanExperiments.QuickSort.QuickSortTask) :
    0 < LeanExperiments.QuickSort.quickSortTaskPotential task := by
  cases task with
  | sort values => simp [LeanExperiments.QuickSort.quickSortTaskPotential]
  | emit value => simp [LeanExperiments.QuickSort.quickSortTaskPotential]

/-- リストを畳み込むとき、加算測度は初期値より小さくならない。 -/
private theorem quickSortTaskListPotential_ge_initial
    (tasks : List LeanExperiments.QuickSort.QuickSortTask) (initial : Nat) :
    initial ≤ tasks.foldl
      (fun total task => total + LeanExperiments.QuickSort.quickSortTaskPotential task)
      initial := by
  induction tasks generalizing initial with
  | nil => simp
  | cons task tasks ih =>
    simp only [List.foldl_cons]
    calc
      initial ≤ initial + LeanExperiments.QuickSort.quickSortTaskPotential task := by omega
      _ ≤ tasks.foldl
          (fun total task => total + LeanExperiments.QuickSort.quickSortTaskPotential task)
          (initial + LeanExperiments.QuickSort.quickSortTaskPotential task) :=
        ih (initial + LeanExperiments.QuickSort.quickSortTaskPotential task)

/-- タスクリストの測度が正であることは、空でないことと同値である。 -/
private theorem quickSortTaskListPotential_pos_iff
    (tasks : List LeanExperiments.QuickSort.QuickSortTask) :
    0 < tasks.foldl
        (fun total task => total + LeanExperiments.QuickSort.quickSortTaskPotential task) 0 ↔
      tasks ≠ [] := by
  induction tasks with
  | nil => simp
  | cons task tasks ih =>
    constructor
    · intro _
      simp
    · intro _
      rw [List.foldl_cons]
      have hInitial := quickSortTaskListPotential_ge_initial tasks
        (LeanExperiments.QuickSort.quickSortTaskPotential task)
      have hTask := quickSortTaskPotential_pos task
      exact Nat.lt_of_lt_of_le (by simpa using hTask) (by simpa using hInitial)

/-- スタック測度は、スタックが空でない場合に限り正である。 -/
theorem quickSortTaskStackPotential_pos_iff
    (tasks : Array LeanExperiments.QuickSort.QuickSortTask) :
    0 < LeanExperiments.QuickSort.quickSortTaskStackPotential tasks ↔
      !tasks.isEmpty := by
  rw [LeanExperiments.QuickSort.quickSortTaskStackPotential,
    quickSortTaskListPotential_pos_iff]
  simp

/-- pivot 以下の列と pivot より大きい列に分けても、要素は重複込みで保存される。 -/
theorem partition_perm (pivot : Nat) (values : List Nat) :
    List.Perm (values.filter (· ≤ pivot) ++ values.filter (pivot < ·)) values := by
  have hUpper : values.filter (pivot < ·) =
      values.filter (fun value => !(decide (value ≤ pivot))) := by
    apply List.filter_congr
    intro value hValue
    by_cases h : value ≤ pivot
    · simp [h]
    · simp [h]
      omega
  rw [hUpper]
  exact List.filter_append_perm (fun value => decide (value ≤ pivot)) values

/-- タスクを一つ積むと、実行順のタスク出力の先頭にその結果が加わる。 -/
private theorem quickSortTaskStackOutput_push
    (tasks : Array LeanExperiments.QuickSort.QuickSortTask)
    (task : LeanExperiments.QuickSort.QuickSortTask) :
    quickSortTaskStackOutput (tasks.push task) =
      quickSortTaskOutput task ++ quickSortTaskStackOutput tasks := by
  simp [quickSortTaskStackOutput, quickSortTaskOutput]

/-- 分割時に積む三タスクは、再帰版が分割結果へ出す順序と同じ意味を持つ。 -/
theorem quickSortTaskStackOutput_pushQuickSortTasks
    (tasks : Array LeanExperiments.QuickSort.QuickSortTask)
    (lower upper : List Nat) (pivot : Nat) :
    quickSortTaskStackOutput
        (LeanExperiments.QuickSort.pushQuickSortTasks tasks lower upper pivot) =
      LeanExperiments.QuickSort.quickSort lower ++ pivot ::
        LeanExperiments.QuickSort.quickSort upper ++ quickSortTaskStackOutput tasks := by
  simp [LeanExperiments.QuickSort.pushQuickSortTasks,
    quickSortTaskStackOutput_push, quickSortTaskOutput, List.append_assoc]

/-- 非空スタックの意味は、次に実行する末尾タスクと残りの意味へ分解できる。 -/
theorem quickSortTaskStackOutput_pop_back
    (tasks : Array LeanExperiments.QuickSort.QuickSortTask)
    (h : tasks.size ≠ 0) :
    quickSortTaskStackOutput tasks =
      quickSortTaskOutput tasks.back! ++ quickSortTaskStackOutput tasks.pop := by
  rw [Array.eq_push_pop_back!_of_size_ne_zero h]
  simp [quickSortTaskStackOutput_push]

/-- 各タスクの処理は、出力済み列と残りスタックを合わせた意味を保つ。 -/
theorem quickSortTaskStackOutput_taskStep
    (tasks : Array LeanExperiments.QuickSort.QuickSortTask)
    (task : LeanExperiments.QuickSort.QuickSortTask) :
    quickSortTaskOutput task ++ quickSortTaskStackOutput tasks =
      match task with
      | .sort [] => quickSortTaskStackOutput tasks
      | .sort (pivot :: rest) =>
          quickSortTaskStackOutput
            (LeanExperiments.QuickSort.pushQuickSortTasks tasks
              (rest.filter (· ≤ pivot)) (rest.filter (pivot < ·)) pivot)
      | .emit value => [value] ++ quickSortTaskStackOutput tasks := by
  cases task with
  | sort values =>
    cases values with
    | nil => simp [quickSortTaskOutput, LeanExperiments.QuickSort.quickSort]
    | cons pivot rest =>
      simpa [quickSortTaskOutput, LeanExperiments.QuickSort.quickSort] using
        (quickSortTaskStackOutput_pushQuickSortTasks tasks
          (rest.filter (· ≤ pivot)) (rest.filter (pivot < ·)) pivot).symm
  | emit value => simp [quickSortTaskOutput]

/-- 非空スタックの末尾タスクを処理しても、スタックが表す出力全体は保たれる。 -/
theorem quickSortTaskStackOutput_backStep
    (tasks : Array LeanExperiments.QuickSort.QuickSortTask)
    (h : tasks.size ≠ 0) :
    quickSortTaskStackOutput tasks =
      match tasks.back! with
      | .sort [] => quickSortTaskStackOutput tasks.pop
      | .sort (pivot :: rest) =>
          quickSortTaskStackOutput
            (LeanExperiments.QuickSort.pushQuickSortTasks tasks.pop
              (rest.filter (· ≤ pivot)) (rest.filter (pivot < ·)) pivot)
      | .emit value => [value] ++ quickSortTaskStackOutput tasks.pop := by
  rw [quickSortTaskStackOutput_pop_back tasks h]
  exact quickSortTaskStackOutput_taskStep tasks.pop tasks.back!

/-- 出力済み prefix と残りスタックを合わせた意味は、一反復後も変わらない。 -/
theorem quickSortTaskStackOutput_output_prefix_backStep
    (outputPrefix : List Nat)
    (tasks : Array LeanExperiments.QuickSort.QuickSortTask)
    (h : tasks.size ≠ 0) :
    outputPrefix ++ quickSortTaskStackOutput tasks =
      match tasks.back! with
      | .sort [] => outputPrefix ++ quickSortTaskStackOutput tasks.pop
      | .sort (pivot :: rest) =>
          outputPrefix ++ quickSortTaskStackOutput
            (LeanExperiments.QuickSort.pushQuickSortTasks tasks.pop
              (rest.filter (· ≤ pivot)) (rest.filter (pivot < ·)) pivot)
      | .emit value => (outputPrefix ++ [value]) ++ quickSortTaskStackOutput tasks.pop := by
  rw [quickSortTaskStackOutput_backStep tasks h]
  cases hTask : tasks.back! with
  | sort values => cases values <;> simp
  | emit value => simp [List.append_assoc]

/-- 実装の出力配列とタスクスタックを合わせた意味は、実際の末尾処理で保たれる。 -/
theorem quickSortTaskStackOutput_array_backStep
    (output : Array Nat)
    (tasks : Array LeanExperiments.QuickSort.QuickSortTask)
    (h : tasks.size ≠ 0) :
    output.toList ++ quickSortTaskStackOutput tasks =
      match tasks.back! with
      | .sort [] => output.toList ++ quickSortTaskStackOutput tasks.pop
      | .sort (pivot :: rest) =>
          output.toList ++ quickSortTaskStackOutput
            (LeanExperiments.QuickSort.pushQuickSortTasks tasks.pop
              (rest.filter (· ≤ pivot)) (rest.filter (pivot < ·)) pivot)
      | .emit value => (output.push value).toList ++ quickSortTaskStackOutput tasks.pop := by
  rw [quickSortTaskStackOutput_output_prefix_backStep output.toList tasks h]
  cases hTask : tasks.back! with
  | sort values => cases values <;> simp
  | emit value => simp [Array.toList_push, List.append_assoc]

/-- 初期状態では、入力全体が未処理タスクの意味として不変条件を満たす。 -/
theorem quickSortIterativeInvariant_initial (values : List Nat) :
    quickSortIterativeInvariant values
      (#[LeanExperiments.QuickSort.QuickSortTask.sort values], #[]) := by
  simp [quickSortIterativeInvariant, quickSortTaskStackOutput,
    quickSortTaskOutput]

/-- 実装と同じ一反復遷移は、非空スタック上で不変条件を保つ。 -/
theorem quickSortIterativeInvariant_step
    (values : List Nat)
    (state : Array LeanExperiments.QuickSort.QuickSortTask × Array Nat)
    (hTasks : state.1.size ≠ 0)
    (hInvariant : quickSortIterativeInvariant values state) :
    quickSortIterativeInvariant values
      (LeanExperiments.QuickSort.quickSortTaskStackStep state) := by
  rcases state with ⟨tasks, output⟩
  change output.toList ++ quickSortTaskStackOutput tasks =
    LeanExperiments.QuickSort.quickSort values at hInvariant
  have hStep := quickSortTaskStackOutput_array_backStep output tasks hTasks
  rw [hStep] at hInvariant
  cases hTask : tasks.back! with
  | sort taskValues =>
    cases taskValues <;>
      simpa [quickSortIterativeInvariant,
        LeanExperiments.QuickSort.quickSortTaskStackStep, hTask,
        Array.toList_push, List.append_assoc] using hInvariant
  | emit value =>
    simpa [quickSortIterativeInvariant,
      LeanExperiments.QuickSort.quickSortTaskStackStep, hTask,
      Array.toList_push, List.append_assoc] using hInvariant

/-- 不変条件と空スタックから、ループが返す配列は再帰版の結果だと分かる。 -/
theorem quickSortIterativeInvariant_terminal
    (values : List Nat)
    (state : Array LeanExperiments.QuickSort.QuickSortTask × Array Nat)
    (hEmpty : state.1.isEmpty)
    (hInvariant : quickSortIterativeInvariant values state) :
    state.2.toList = LeanExperiments.QuickSort.quickSort values := by
  unfold quickSortIterativeInvariant at hInvariant
  have hSize : state.1.size = 0 := Array.isEmpty_iff_size_eq_zero.mp hEmpty
  have hArray : state.1 = #[] := Array.size_eq_zero_iff.mp hSize
  have hStack : quickSortTaskStackOutput state.1 = [] := by
    simp [quickSortTaskStackOutput, hArray]
  rw [hStack, List.append_nil] at hInvariant
  exact hInvariant

/-- pivot 分割は入力要素数を保存する。 -/
theorem partition_length (pivot : Nat) (values : List Nat) :
    (values.filter (· ≤ pivot)).length + (values.filter (pivot < ·)).length =
      values.length := by
  have hPerm := partition_perm pivot values
  simpa [List.length_append] using hPerm.length_eq

/-- pivot 分割後の三タスク追加は、処理前の一タスクより停止測度を下げる。 -/
theorem quickSortTaskStackPotential_split_decreases
    (tasks : Array LeanExperiments.QuickSort.QuickSortTask)
    (pivot : Nat) (rest : List Nat) :
    LeanExperiments.QuickSort.quickSortTaskStackPotential
        (LeanExperiments.QuickSort.pushQuickSortTasks tasks
          (rest.filter (· ≤ pivot)) (rest.filter (pivot < ·)) pivot) <
      LeanExperiments.QuickSort.quickSortTaskStackPotential
        (tasks.push (.sort (pivot :: rest))) := by
  have hLength := partition_length pivot rest
  rw [LeanExperiments.QuickSort.quickSortTaskStackPotential_pushQuickSortTasks,
    LeanExperiments.QuickSort.quickSortTaskStackPotential_push]
  simp only [LeanExperiments.QuickSort.quickSortTaskPotential]
  have hCons : (pivot :: rest).length = rest.length + 1 := by simp
  rw [hCons]
  omega

/-- スタック末尾のタスクを一つ処理すると、全タスク種別で測度が厳密に減る。 -/
theorem quickSortTaskStackPotential_taskStep_decreases
    (tasks : Array LeanExperiments.QuickSort.QuickSortTask)
    (task : LeanExperiments.QuickSort.QuickSortTask) :
    (match task with
      | .sort [] => LeanExperiments.QuickSort.quickSortTaskStackPotential tasks
      | .sort (pivot :: rest) =>
          LeanExperiments.QuickSort.quickSortTaskStackPotential
            (LeanExperiments.QuickSort.pushQuickSortTasks tasks
              (rest.filter (· ≤ pivot)) (rest.filter (pivot < ·)) pivot)
      | .emit _ => LeanExperiments.QuickSort.quickSortTaskStackPotential tasks) <
      LeanExperiments.QuickSort.quickSortTaskStackPotential (tasks.push task) := by
  cases task with
  | sort values =>
    cases values with
    | nil =>
      rw [LeanExperiments.QuickSort.quickSortTaskStackPotential_push]
      simp [LeanExperiments.QuickSort.quickSortTaskPotential]
    | cons pivot rest =>
      exact quickSortTaskStackPotential_split_decreases tasks pivot rest
  | emit value =>
    rw [LeanExperiments.QuickSort.quickSortTaskStackPotential_push]
    simp [LeanExperiments.QuickSort.quickSortTaskPotential]

/-- 非空スタックの末尾タスクを実装どおりに処理すると、スタック測度が厳密に減る。 -/
theorem quickSortTaskStackPotential_backStep_decreases
    (tasks : Array LeanExperiments.QuickSort.QuickSortTask)
    (h : tasks.size ≠ 0) :
    (match tasks.back! with
      | .sort [] => LeanExperiments.QuickSort.quickSortTaskStackPotential tasks.pop
      | .sort (pivot :: rest) =>
          LeanExperiments.QuickSort.quickSortTaskStackPotential
            (LeanExperiments.QuickSort.pushQuickSortTasks tasks.pop
              (rest.filter (· ≤ pivot)) (rest.filter (pivot < ·)) pivot)
      | .emit _ => LeanExperiments.QuickSort.quickSortTaskStackPotential tasks.pop) <
      LeanExperiments.QuickSort.quickSortTaskStackPotential tasks := by
  rw [Array.eq_push_pop_back!_of_size_ne_zero h]
  simp only [Array.back!_push, Array.pop_push]
  exact quickSortTaskStackPotential_taskStep_decreases tasks.pop tasks.back!

/-- 実装が使う一反復遷移では、非空スタックの停止測度が厳密に減る。 -/
theorem quickSortTaskStackStep_potential_decreases
    (state : Array LeanExperiments.QuickSort.QuickSortTask × Array Nat)
    (hTasks : state.1.size ≠ 0) :
    LeanExperiments.QuickSort.quickSortTaskStackPotential
        (LeanExperiments.QuickSort.quickSortTaskStackStep state).1 <
      LeanExperiments.QuickSort.quickSortTaskStackPotential state.1 := by
  rcases state with ⟨tasks, output⟩
  cases hTask : tasks.back! with
  | sort values =>
    cases values <;>
      simpa [LeanExperiments.QuickSort.quickSortTaskStackStep, hTask] using
        quickSortTaskStackPotential_backStep_decreases tasks hTasks
  | emit value =>
    simpa [LeanExperiments.QuickSort.quickSortTaskStackStep, hTask] using
      quickSortTaskStackPotential_backStep_decreases tasks hTasks

/-- 反復版 quick sort は任意の入力で再帰版と同じ結果を返す。 -/
theorem quickSortIterative_eq_recursive (values : List Nat) :
    LeanExperiments.QuickSort.quickSortIterative values =
      LeanExperiments.QuickSort.quickSort values := by
  generalize hRun : LeanExperiments.QuickSort.quickSortIterative values = result
  apply Id.of_run_eq_wp hRun
  vcgen [LeanExperiments.QuickSort.quickSortIterative] invariants
  · fun finished state =>
      if finished then state.2.toList = LeanExperiments.QuickSort.quickSort values
      else quickSortIterativeInvariant values state
  case vc1 =>
    simp_all [state, quickSortIterativeInvariant, quickSortTaskStackOutput,
      quickSortTaskOutput]
  case vc2 => simp_all [state]
  case vc3 =>
    simp_all [state, Variant.evalsBelow_ofMeasure_nat,
      Variant.evalsTo_ofMeasure, Assertion.NondetFun.evalsTo_pure]
    rename_i q1 q2 q3 q4 q5 q6
    rcases q5 with ⟨hMeasure, hInvariant⟩
    have hTasks : q4.1.size ≠ 0 := by
      intro hZero
      apply q6
      exact Array.size_eq_zero_iff.mp hZero
    constructor
    · rw [← hMeasure]
      exact quickSortTaskStackStep_potential_decreases q4 hTasks
    · exact quickSortIterativeInvariant_step values q4 hTasks hInvariant
  case vc4 =>
    simp_all [state, quickSortIterativeInvariant, quickSortTaskStackOutput,
      Variant.evalsTo_ofMeasure, Assertion.NondetFun.evalsTo_pure]

/-- 分割後の左側への所属は、入力への所属と pivot 以下であることに同値。 -/
theorem partition_lower_mem_iff {pivot value : Nat} {values : List Nat} :
    value ∈ values.filter (· ≤ pivot) ↔ value ∈ values ∧ value ≤ pivot := by
  simp [List.mem_filter]

/-- 分割後の右側への所属は、入力への所属と pivot より大きいことに同値。 -/
theorem partition_upper_mem_iff {pivot value : Nat} {values : List Nat} :
    value ∈ values.filter (pivot < ·) ↔ value ∈ values ∧ pivot < value := by
  simp [List.mem_filter]

/-- pivot 分割は、任意の Boolean 分類に属する値の個数を左右へ正確に振り分ける。 -/
theorem partition_countP_decomposition (pivot : Nat) (values : List Nat)
    (predicate : Nat → Bool) :
    (values.filter (· ≤ pivot)).countP predicate +
        (values.filter (pivot < ·)).countP predicate = values.countP predicate := by
  have hPerm := partition_perm pivot values
  simpa [List.countP_append] using hPerm.countP_eq predicate

/-- pivot 以下の分割に入る要素は、全て pivot 以下である。 -/
theorem partition_lower_bound {pivot value : Nat} {values : List Nat}
    (h : value ∈ values.filter (· ≤ pivot)) : value ≤ pivot :=
  of_decide_eq_true (List.mem_filter.mp h).2

/-- pivot より大きい分割に入る要素は、全て pivot より大きい。 -/
theorem partition_upper_bound {pivot value : Nat} {values : List Nat}
    (h : value ∈ values.filter (pivot < ·)) : pivot < value :=
  of_decide_eq_true (List.mem_filter.mp h).2

/-- pivot 以下の分割と pivot より大きい分割に同じ値は入らない。 -/
theorem partition_disjoint (pivot : Nat) (values : List Nat) :
    ∀ value, value ∈ values.filter (· ≤ pivot) →
      value ∈ values.filter (pivot < ·) → False := by
  intro value hLower hUpper
  have hLowerBound := partition_lower_bound hLower
  have hUpperBound := partition_upper_bound hUpper
  omega

/-- 再帰版クイックソートは、任意の入力で要素を重複込みで保存する。 -/
theorem quickSort_perm : ∀ values : List Nat,
    List.Perm (LeanExperiments.QuickSort.quickSort values) values
  | [] => by simp [LeanExperiments.QuickSort.quickSort]
  | pivot :: rest => by
    let lower := rest.filter (· ≤ pivot)
    let upper := rest.filter (pivot < ·)
    have hPartition : List.Perm (lower ++ upper) rest := by
      exact partition_perm pivot rest
    simp only [LeanExperiments.QuickSort.quickSort]
    calc
      LeanExperiments.QuickSort.quickSort lower ++ pivot ::
          LeanExperiments.QuickSort.quickSort upper ~ lower ++ pivot :: upper :=
        (quickSort_perm lower).append ((quickSort_perm upper).cons pivot)
      _ ~ pivot :: (lower ++ upper) := List.perm_middle
      _ ~ pivot :: rest := hPartition.cons pivot
termination_by values => values.length
decreasing_by
  all_goals simp_wf
  · exact Nat.lt_succ_of_le (List.length_filter_le _ _)
  · exact Nat.lt_succ_of_le (List.length_filter_le _ _)

/-- pivot 以下の分割を再帰ソートした結果も、全て pivot 以下に保たれる。 -/
theorem quickSort_lower_output_bound (pivot : Nat) (values : List Nat) :
    ∀ value ∈ LeanExperiments.QuickSort.quickSort (values.filter (· ≤ pivot)),
      value ≤ pivot := by
  intro value hValue
  have hPerm := quickSort_perm (values.filter (· ≤ pivot))
  have hInput : value ∈ values.filter (· ≤ pivot) := hPerm.mem_iff.mp hValue
  exact partition_lower_bound hInput

/-- pivot より大きい分割を再帰ソートした結果も、全て pivot より大きい。 -/
theorem quickSort_upper_output_bound (pivot : Nat) (values : List Nat) :
    ∀ value ∈ LeanExperiments.QuickSort.quickSort (values.filter (pivot < ·)),
      pivot < value := by
  intro value hValue
  have hPerm := quickSort_perm (values.filter (pivot < ·))
  have hInput : value ∈ values.filter (pivot < ·) := hPerm.mem_iff.mp hValue
  exact partition_upper_bound hInput

/-- 左右の再帰ソート結果を連結しても、左側の値は右側の値以下である。 -/
theorem quickSort_partition_output_order (pivot : Nat) (values : List Nat) :
    ∀ leftValue ∈ LeanExperiments.QuickSort.quickSort (values.filter (· ≤ pivot)),
      ∀ rightValue ∈ LeanExperiments.QuickSort.quickSort (values.filter (pivot < ·)),
        leftValue ≤ rightValue := by
  intro leftValue hLeft rightValue hRight
  exact Nat.le_trans
    (quickSort_lower_output_bound pivot values leftValue hLeft)
    (Nat.le_of_lt (quickSort_upper_output_bound pivot values rightValue hRight))

/-- 再帰版クイックソートの結果は、任意の入力で昇順になる。 -/
theorem quickSort_pairwise : ∀ values : List Nat,
    (LeanExperiments.QuickSort.quickSort values).Pairwise (fun a b : Nat => a ≤ b)
  | [] => by simp [LeanExperiments.QuickSort.quickSort]
  | pivot :: rest => by
    let lower := rest.filter (· ≤ pivot)
    let upper := rest.filter (pivot < ·)
    have hLowerSorted := quickSort_pairwise lower
    have hUpperSorted := quickSort_pairwise upper
    have hUpperBounds : ∀ value ∈ LeanExperiments.QuickSort.quickSort upper, pivot ≤ value := by
      intro value hValue
      exact Nat.le_of_lt (quickSort_upper_output_bound pivot rest value hValue)
    have hLowerBounds : ∀ value ∈ LeanExperiments.QuickSort.quickSort lower, value ≤ pivot := by
      intro value hValue
      exact quickSort_lower_output_bound pivot rest value hValue
    simp only [LeanExperiments.QuickSort.quickSort]
    rw [List.pairwise_append]
    refine ⟨hLowerSorted, ?_, ?_⟩
    · apply List.Pairwise.cons
      · intro value hValue
        exact hUpperBounds value hValue
      · exact hUpperSorted
    · intro leftValue hLeft rightValue hRight
      simp only [List.mem_cons] at hRight
      rcases hRight with rfl | hRight
      · exact hLowerBounds leftValue hLeft
      · exact Nat.le_trans (hLowerBounds leftValue hLeft) (hUpperBounds rightValue hRight)
termination_by values => values.length
decreasing_by
  all_goals simp_wf
  · exact Nat.lt_succ_of_le (List.length_filter_le _ _)
  · exact Nat.lt_succ_of_le (List.length_filter_le _ _)

/-- 再帰版クイックソートは任意の入力について共通の正しさ仕様を満たす。 -/
theorem quickSort_correct (values : List Nat) :
    LeanExperiments.Verification.Sorting.Spec.Correct values
      (LeanExperiments.QuickSort.quickSort values) := by
  exact ⟨LeanExperiments.Verification.Sorting.Spec.pairwise_ascending _
    (quickSort_pairwise values), quickSort_perm values⟩

/-- ループ版 quick sort は任意の入力で昇順性と要素保存を満たす。 -/
theorem quickSortIterative_correct (values : List Nat) :
    LeanExperiments.Verification.Sorting.Spec.Correct values
      (LeanExperiments.QuickSort.quickSortIterative values) := by
  rw [quickSortIterative_eq_recursive]
  exact quickSort_correct values

/-- 再帰版QuickSortは、左右を独立にソートしてMergeSortの併合関数で結合する操作と一致する。 -/
theorem quickSort_append_eq_merge (left right : List Nat) :
    LeanExperiments.QuickSort.quickSort (left ++ right) =
      LeanExperiments.MergeSort.merge
        (LeanExperiments.QuickSort.quickSort left)
        (LeanExperiments.QuickSort.quickSort right) :=
  LeanExperiments.Verification.MergeSort.correct_sort_append_eq_merge
    LeanExperiments.QuickSort.quickSort quickSort_correct left right

/-- ループ版QuickSortも連結入力を個別ソート後の併合へ分解できる。 -/
theorem quickSortIterative_append_eq_merge (left right : List Nat) :
    LeanExperiments.QuickSort.quickSortIterative (left ++ right) =
      LeanExperiments.MergeSort.merge
        (LeanExperiments.QuickSort.quickSortIterative left)
        (LeanExperiments.QuickSort.quickSortIterative right) :=
  LeanExperiments.Verification.MergeSort.correct_sort_append_eq_merge
    LeanExperiments.QuickSort.quickSortIterative quickSortIterative_correct left right

/-- 再帰版は順列関係にある入力へ同じ結果を返す。 -/
theorem quickSort_eq_of_perm {left right : List Nat} (hPerm : List.Perm left right) :
    LeanExperiments.QuickSort.quickSort left = LeanExperiments.QuickSort.quickSort right :=
  LeanExperiments.Verification.Sorting.Spec.Correct.sort_eq_of_perm_inputs
    LeanExperiments.QuickSort.quickSort quickSort_correct hPerm

/-- ループ版は順列関係にある入力へ同じ結果を返す。 -/
theorem quickSortIterative_eq_of_perm {left right : List Nat}
    (hPerm : List.Perm left right) :
    LeanExperiments.QuickSort.quickSortIterative left =
      LeanExperiments.QuickSort.quickSortIterative right :=
  LeanExperiments.Verification.Sorting.Spec.Correct.sort_eq_of_perm_inputs
    LeanExperiments.QuickSort.quickSortIterative quickSortIterative_correct hPerm

/-- 再帰版は既に昇順の入力を変更しない。 -/
theorem quickSort_eq_self_of_ascending (values : List Nat)
    (hAscending : LeanExperiments.Verification.Sorting.Spec.Ascending values) :
    LeanExperiments.QuickSort.quickSort values = values :=
  LeanExperiments.Verification.Sorting.Spec.Correct.sort_eq_self_of_ascending
    LeanExperiments.QuickSort.quickSort quickSort_correct values hAscending

/-- ループ版は既に昇順の入力を変更しない。 -/
theorem quickSortIterative_eq_self_of_ascending (values : List Nat)
    (hAscending : LeanExperiments.Verification.Sorting.Spec.Ascending values) :
    LeanExperiments.QuickSort.quickSortIterative values = values :=
  LeanExperiments.Verification.Sorting.Spec.Correct.sort_eq_self_of_ascending
    LeanExperiments.QuickSort.quickSortIterative quickSortIterative_correct values hAscending

/-- 再帰版クイックソートは冪等である。 -/
theorem quickSort_idempotent (values : List Nat) :
    LeanExperiments.QuickSort.quickSort (LeanExperiments.QuickSort.quickSort values) =
      LeanExperiments.QuickSort.quickSort values :=
  LeanExperiments.Verification.Sorting.Spec.Correct.sort_idempotent
    LeanExperiments.QuickSort.quickSort quickSort_correct values

/-- ループ版クイックソートは冪等である。 -/
theorem quickSortIterative_idempotent (values : List Nat) :
    LeanExperiments.QuickSort.quickSortIterative
        (LeanExperiments.QuickSort.quickSortIterative values) =
      LeanExperiments.QuickSort.quickSortIterative values :=
  LeanExperiments.Verification.Sorting.Spec.Correct.sort_idempotent
    LeanExperiments.QuickSort.quickSortIterative quickSortIterative_correct values

/-- 再帰版は非減少写像とソートの順序を交換できる。 -/
theorem quickSort_map_of_monotone (values : List Nat) (f : Nat → Nat)
    (hMonotone : ∀ ⦃a b⦄, a ≤ b → f a ≤ f b) :
    LeanExperiments.QuickSort.quickSort (values.map f) =
      (LeanExperiments.QuickSort.quickSort values).map f :=
  LeanExperiments.Verification.Sorting.Spec.Correct.sort_map
    LeanExperiments.QuickSort.quickSort quickSort_correct values f hMonotone

/-- ループ版も非減少写像とソートの順序を交換できる。 -/
theorem quickSortIterative_map_of_monotone (values : List Nat) (f : Nat → Nat)
    (hMonotone : ∀ ⦃a b⦄, a ≤ b → f a ≤ f b) :
    LeanExperiments.QuickSort.quickSortIterative (values.map f) =
      (LeanExperiments.QuickSort.quickSortIterative values).map f :=
  LeanExperiments.Verification.Sorting.Spec.Correct.sort_map
    LeanExperiments.QuickSort.quickSortIterative quickSortIterative_correct values f hMonotone

/-- 再帰版は任意のBoolean条件による絞り込みと可換である。 -/
theorem quickSort_filter (values : List Nat) (predicate : Nat → Bool) :
    LeanExperiments.QuickSort.quickSort (values.filter predicate) =
      (LeanExperiments.QuickSort.quickSort values).filter predicate :=
  LeanExperiments.Verification.Sorting.Spec.Correct.sort_filter
    LeanExperiments.QuickSort.quickSort quickSort_correct values predicate

/-- ループ版も任意のBoolean条件による絞り込みと可換である。 -/
theorem quickSortIterative_filter (values : List Nat) (predicate : Nat → Bool) :
    LeanExperiments.QuickSort.quickSortIterative (values.filter predicate) =
      (LeanExperiments.QuickSort.quickSortIterative values).filter predicate :=
  LeanExperiments.Verification.Sorting.Spec.Correct.sort_filter
    LeanExperiments.QuickSort.quickSortIterative quickSortIterative_correct values predicate

/-- 再帰版クイックソートの各出力位置は、入力中の順位条件で特徴付けられる。

重複値も含め、値より小さい入力要素数と値以下の入力要素数がその順位を正確に定める。
-/
theorem quickSort_getElem_eq_iff_rank_bounds (values : List Nat)
    (index : Nat) (hIndex : index <
      (LeanExperiments.QuickSort.quickSort values).length) (value : Nat) :
    (LeanExperiments.QuickSort.quickSort values)[index] = value ↔
      values.countP (fun item => decide (item < value)) ≤ index ∧
        index < values.countP (fun item => decide (item ≤ value)) :=
  LeanExperiments.Verification.Sorting.Spec.Correct.getElem_eq_iff_rank_bounds
    (quickSort_correct values) hIndex value

/-- 反復版クイックソートの各出力位置にも、同じ一般順位特徴付けが成り立つ。 -/
theorem quickSortIterative_getElem_eq_iff_rank_bounds (values : List Nat)
    (index : Nat) (hIndex : index <
      (LeanExperiments.QuickSort.quickSortIterative values).length) (value : Nat) :
    (LeanExperiments.QuickSort.quickSortIterative values)[index] = value ↔
      values.countP (fun item => decide (item < value)) ≤ index ∧
        index < values.countP (fun item => decide (item ≤ value)) :=
  LeanExperiments.Verification.Sorting.Spec.Correct.getElem_eq_iff_rank_bounds
    (quickSortIterative_correct values) hIndex value

/-- 再帰版の先頭 `k` 個に含まれる、しきい値以下の値の個数を入力から決める。 -/
theorem quickSort_take_countP_le (values : List Nat) (k threshold : Nat) :
    ((LeanExperiments.QuickSort.quickSort values).take k).countP
        (fun value => decide (value ≤ threshold)) =
      min k (values.countP (fun value => decide (value ≤ threshold))) :=
  LeanExperiments.Verification.Sorting.Spec.Correct.countP_take_le
    (quickSort_correct values) k threshold

/-- 再帰版の先頭 `k` 個に含まれる、しきい値より大きい値の個数を特徴付ける。 -/
theorem quickSort_take_countP_gt (values : List Nat) (k threshold : Nat) :
    ((LeanExperiments.QuickSort.quickSort values).take k).countP
        (fun value => decide (threshold < value)) =
      min (values.countP (fun value => decide (threshold < value)))
        (k - values.countP (fun value => decide (value ≤ threshold))) :=
  LeanExperiments.Verification.Sorting.Spec.Correct.countP_take_gt
    (quickSort_correct values) k threshold

/-- 再帰版の先頭 `k` 個に含まれる、しきい値以上の値の個数を特徴付ける。 -/
theorem quickSort_take_countP_ge (values : List Nat) (k threshold : Nat) :
    ((LeanExperiments.QuickSort.quickSort values).take k).countP
        (fun value => decide (threshold ≤ value)) =
      min (values.countP (fun value => decide (threshold ≤ value)))
        (k - values.countP (fun value => decide (value < threshold))) :=
  LeanExperiments.Verification.Sorting.Spec.Correct.countP_take_ge
    (quickSort_correct values) k threshold

/-- 反復版の先頭 `k` 個に含まれる、しきい値以下の値の個数を入力から決める。 -/
theorem quickSortIterative_take_countP_le (values : List Nat) (k threshold : Nat) :
    ((LeanExperiments.QuickSort.quickSortIterative values).take k).countP
        (fun value => decide (value ≤ threshold)) =
      min k (values.countP (fun value => decide (value ≤ threshold))) :=
  LeanExperiments.Verification.Sorting.Spec.Correct.countP_take_le
    (quickSortIterative_correct values) k threshold

/-- 反復版の先頭 `k` 個に含まれる、しきい値より大きい値の個数を特徴付ける。 -/
theorem quickSortIterative_take_countP_gt (values : List Nat) (k threshold : Nat) :
    ((LeanExperiments.QuickSort.quickSortIterative values).take k).countP
        (fun value => decide (threshold < value)) =
      min (values.countP (fun value => decide (threshold < value)))
        (k - values.countP (fun value => decide (value ≤ threshold))) :=
  LeanExperiments.Verification.Sorting.Spec.Correct.countP_take_gt
    (quickSortIterative_correct values) k threshold

/-- 反復版の先頭 `k` 個に含まれる、しきい値以上の値の個数を特徴付ける。 -/
theorem quickSortIterative_take_countP_ge (values : List Nat) (k threshold : Nat) :
    ((LeanExperiments.QuickSort.quickSortIterative values).take k).countP
        (fun value => decide (threshold ≤ value)) =
      min (values.countP (fun value => decide (threshold ≤ value)))
        (k - values.countP (fun value => decide (value < threshold))) :=
  LeanExperiments.Verification.Sorting.Spec.Correct.countP_take_ge
    (quickSortIterative_correct values) k threshold

/-- 再帰版の順列保存を使うと、共通 Boolean 検査器の成功は出力の昇順性と同値になる。 -/
theorem quickSort_check_iff_ascending (values : List Nat) :
    LeanExperiments.Verification.Sorting.Spec.correctCheck values
      (LeanExperiments.QuickSort.quickSort values) = true ↔
    LeanExperiments.Verification.Sorting.Spec.Ascending
      (LeanExperiments.QuickSort.quickSort values) :=
  LeanExperiments.Verification.Sorting.Spec.correctCheck_iff_ascending_of_perm
    values _ (quickSort_perm values)

/-- ループ版も、一般の順列保存により検査器の成功と出力昇順性が同値になる。 -/
theorem quickSortIterative_check_iff_ascending (values : List Nat) :
    LeanExperiments.Verification.Sorting.Spec.correctCheck values
      (LeanExperiments.QuickSort.quickSortIterative values) = true ↔
    LeanExperiments.Verification.Sorting.Spec.Ascending
      (LeanExperiments.QuickSort.quickSortIterative values) :=
  LeanExperiments.Verification.Sorting.Spec.correctCheck_iff_ascending_of_perm
    values _ (quickSortIterative_correct values).2

/-- ループ版が共通検査に通ることと、再帰版の結果と一致することは同値。 -/
theorem quickSortIterative_correct_iff_agrees (values : List Nat) :
    LeanExperiments.Verification.Sorting.Spec.correctCheck values
      (LeanExperiments.QuickSort.quickSortIterative values) = true ↔
    LeanExperiments.QuickSort.quickSortIterative values =
      LeanExperiments.QuickSort.quickSort values := by
  constructor
  · intro hCheck
    exact LeanExperiments.Verification.Sorting.Spec.Correct.eq_of_same_input
      (LeanExperiments.Verification.Sorting.Spec.correctCheck_sound values _ hCheck)
      (quickSort_correct values)
  · intro hAgree
    rw [hAgree]
    exact LeanExperiments.Verification.Sorting.Spec.correctCheck_complete values
      (LeanExperiments.QuickSort.quickSort values) (quickSort_correct values)

/-- 空リストはそのまま空リストになる。 -/
theorem quickSort_empty_boundary : LeanExperiments.QuickSort.quickSort [] = [] := by
  native_decide

/-- 重複値を失わず、昇順に並べ替える。 -/
theorem quickSort_duplicates_example :
    LeanExperiments.QuickSort.quickSort [7, 2, 5, 2, 0, 9] = [0, 2, 2, 5, 7, 9] := by
  native_decide

/-- 逆順の値を昇順へ並べ替える。 -/
theorem quickSort_reverseInput_example :
    LeanExperiments.QuickSort.quickSort [9, 8, 7, 6, 5, 4, 3, 2, 1, 0] =
      [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] := by
  native_decide

/-- ループ版は空入力を空のまま返す。 -/
theorem quickSortIterative_empty_boundary :
    LeanExperiments.QuickSort.quickSortIterative [] = [] := by
  native_decide

/-- ループ版も重複値を保持して昇順に並べ替える。 -/
theorem quickSortIterative_duplicates_example :
    LeanExperiments.QuickSort.quickSortIterative [7, 2, 5, 2, 0, 9] =
      [0, 2, 2, 5, 7, 9] := by
  native_decide

/-- 再帰版とループ版が代表的な重複値入力で一致する。 -/
theorem quickSort_implementations_agree_example :
    LeanExperiments.QuickSort.quickSort [7, 2, 5, 2, 0, 9] =
      LeanExperiments.QuickSort.quickSortIterative [7, 2, 5, 2, 0, 9] := by
  native_decide

/-! ## 有限領域の網羅確認

長さ 0〜5、値 0〜2 の全 364 入力に対し、昇順性と要素保存を別々に含む共通仕様を
両実装が満たすこと、さらに両者が同じ結果を返すことを確認する。
これは有限領域の計算確認であり、任意の自然数列についての一般証明ではない。 -/

/-- 再帰版が有限領域の全入力で共通のソート仕様を満たす。 -/
def quickSortBoundedCheck : Bool :=
  LeanExperiments.Verification.Sorting.Spec.boundedInputs.all fun input =>
    LeanExperiments.Verification.Sorting.Spec.correctCheck input
      (LeanExperiments.QuickSort.quickSort input)

/-- ループ版が有限領域の全入力で共通のソート仕様を満たす。 -/
def quickSortIterativeBoundedCheck : Bool :=
  LeanExperiments.Verification.Sorting.Spec.boundedInputs.all fun input =>
    LeanExperiments.Verification.Sorting.Spec.correctCheck input
      (LeanExperiments.QuickSort.quickSortIterative input)

/-- 有限領域の全入力で再帰版とループ版の出力が一致する。 -/
def quickSortAgreementBoundedCheck : Bool :=
  LeanExperiments.Verification.Sorting.Spec.boundedInputs.all fun input =>
    decide (LeanExperiments.QuickSort.quickSort input =
      LeanExperiments.QuickSort.quickSortIterative input)

/-- 364 入力全てで再帰版の昇順性と要素保存を確認する。 -/
theorem quickSortBoundedCheck_passes : quickSortBoundedCheck = true := by
  native_decide

/-- 364 入力全てでループ版の昇順性と要素保存を確認する。 -/
theorem quickSortIterativeBoundedCheck_passes : quickSortIterativeBoundedCheck = true := by
  native_decide

/-- 364 入力全てで両実装の結果が一致する。 -/
theorem quickSortAgreementBoundedCheck_passes : quickSortAgreementBoundedCheck = true := by
  native_decide

/-- より広い有限領域でループ版の昇順性と要素保存を確認する。 -/
def quickSortIterativeStressCheck : Bool :=
  LeanExperiments.Verification.Sorting.Spec.stressInputs.all fun input =>
    LeanExperiments.Verification.Sorting.Spec.correctCheck input
      (LeanExperiments.QuickSort.quickSortIterative input)

/-- 長さ 0〜8、値 0〜3 の全 87,381 入力でループ版の仕様が成立する。 -/
theorem quickSortIterativeStressCheck_passes : quickSortIterativeStressCheck = true := by
  native_decide

/-- より広い有限領域で再帰版とループ版の一致を確認する。 -/
def quickSortAgreementStressCheck : Bool :=
  LeanExperiments.Verification.Sorting.Spec.stressInputs.all fun input =>
    decide (LeanExperiments.QuickSort.quickSort input =
      LeanExperiments.QuickSort.quickSortIterative input)

/-- 長さ 0〜8、値 0〜3 の全 87,381 入力で両実装が一致する。 -/
theorem quickSortAgreementStressCheck_passes : quickSortAgreementStressCheck = true := by
  native_decide

/-! ## 大きな値を含む全列挙確認

値の桁が大きく異なる入力や最大64 bit値の重複を含め、長さ0〜7の97,656入力について
再帰版・ループ版の仕様と両者の一致を確認する。 -/

/-- 大きな値を含む全入力で再帰版が共通仕様を満たす。 -/
def quickSortWideValueCheck : Bool :=
  LeanExperiments.Verification.Sorting.Spec.wideValueInputs.all fun input =>
    LeanExperiments.Verification.Sorting.Spec.correctCheck input
      (LeanExperiments.QuickSort.quickSort input)

/-- 大きな値を含む全入力でループ版が共通仕様を満たす。 -/
def quickSortIterativeWideValueCheck : Bool :=
  LeanExperiments.Verification.Sorting.Spec.wideValueInputs.all fun input =>
    LeanExperiments.Verification.Sorting.Spec.correctCheck input
      (LeanExperiments.QuickSort.quickSortIterative input)

/-- 大きな値を含む全入力で再帰版とループ版の結果が一致する。 -/
def quickSortAgreementWideValueCheck : Bool :=
  LeanExperiments.Verification.Sorting.Spec.wideValueInputs.all fun input =>
    decide (LeanExperiments.QuickSort.quickSort input =
      LeanExperiments.QuickSort.quickSortIterative input)

/-- 97,656入力全てで再帰版の仕様が成立する。 -/
theorem quickSortWideValueCheck_passes : quickSortWideValueCheck = true := by
  native_decide

/-- 97,656入力全てでループ版の仕様が成立する。 -/
theorem quickSortIterativeWideValueCheck_passes :
    quickSortIterativeWideValueCheck = true := by
  native_decide

/-- 97,656入力全てで両実装の結果が一致する。 -/
theorem quickSortAgreementWideValueCheck_passes :
    quickSortAgreementWideValueCheck = true := by
  native_decide

/-! ## 偏りのある長い入力

小さい値域の網羅確認とは別に、長さ64および63・65・127・128・129・255・256・257・511・512・513の整列済み・逆順・同値・周期列を確認する。
先頭要素を基準にする実装で分割が偏る形や、重複値が多い形を含める。
-/

/-- 偏り入力全てで再帰版が共通仕様を満たす。 -/
def quickSortAdversarialCheck : Bool :=
  LeanExperiments.Verification.Sorting.Spec.adversarialInputs.all fun input =>
    LeanExperiments.Verification.Sorting.Spec.correctCheck input
      (LeanExperiments.QuickSort.quickSort input)

/-- 偏り入力全てでループ版が共通仕様を満たす。 -/
def quickSortIterativeAdversarialCheck : Bool :=
  LeanExperiments.Verification.Sorting.Spec.adversarialInputs.all fun input =>
    LeanExperiments.Verification.Sorting.Spec.correctCheck input
      (LeanExperiments.QuickSort.quickSortIterative input)

/-- 偏り入力全てで再帰版とループ版の結果が一致する。 -/
def quickSortAgreementAdversarialCheck : Bool :=
  LeanExperiments.Verification.Sorting.Spec.adversarialInputs.all fun input =>
    decide (LeanExperiments.QuickSort.quickSort input =
      LeanExperiments.QuickSort.quickSortIterative input)

/-- 全ての偏り入力で再帰版の昇順性と要素保存を確認する。 -/
theorem quickSortAdversarialCheck_passes : quickSortAdversarialCheck = true := by
  native_decide

/-- 全ての偏り入力でループ版の昇順性と要素保存を確認する。 -/
theorem quickSortIterativeAdversarialCheck_passes :
    quickSortIterativeAdversarialCheck = true := by
  native_decide

/-- 全ての偏り入力で再帰版とループ版の一致を確認する。 -/
theorem quickSortAgreementAdversarialCheck_passes :
    quickSortAgreementAdversarialCheck = true := by
  native_decide

/-! ## 長さと64ビット値幅を組み合わせた確認 -/

/-- 共通の48境界値入力で再帰版が仕様を満たす。 -/
def quickSortWideAdversarialCheck : Bool :=
  LeanExperiments.Verification.Sorting.Spec.wideAdversarialInputs.all fun input =>
    LeanExperiments.Verification.Sorting.Spec.correctCheck input
      (LeanExperiments.QuickSort.quickSort input)

/-- 共通の48境界値入力でループ版が仕様を満たす。 -/
def quickSortIterativeWideAdversarialCheck : Bool :=
  LeanExperiments.Verification.Sorting.Spec.wideAdversarialInputs.all fun input =>
    LeanExperiments.Verification.Sorting.Spec.correctCheck input
      (LeanExperiments.QuickSort.quickSortIterative input)

/-- 共通の48境界値入力で二つの実装結果が一致する。 -/
def quickSortAgreementWideAdversarialCheck : Bool :=
  LeanExperiments.Verification.Sorting.Spec.wideAdversarialInputs.all fun input =>
    decide (LeanExperiments.QuickSort.quickSort input =
      LeanExperiments.QuickSort.quickSortIterative input)

/-- 48入力全てで再帰版が仕様を満たす。 -/
theorem quickSortWideAdversarialCheck_passes :
    quickSortWideAdversarialCheck = true := by
  native_decide

/-- 48入力全てでループ版が仕様を満たす。 -/
theorem quickSortIterativeWideAdversarialCheck_passes :
    quickSortIterativeWideAdversarialCheck = true := by
  native_decide

/-- 48入力全てで再帰版とループ版の結果が一致する。 -/
theorem quickSortAgreementWideAdversarialCheck_passes :
    quickSortAgreementWideAdversarialCheck = true := by
  native_decide

/-! ## 1024 要素付近の大規模境界確認 -/

/-- 1023・1024・1025要素の入力全てでループ版の仕様を確認する。 -/
def quickSortIterativeLargeAdversarialCheck : Bool :=
  LeanExperiments.Verification.Sorting.Spec.largeAdversarialInputs.all fun input =>
    LeanExperiments.Verification.Sorting.Spec.correctCheck input
      (LeanExperiments.QuickSort.quickSortIterative input)

/-- 1023・1024・1025要素の入力全てで再帰版との一致を確認する。 -/
def quickSortAgreementLargeAdversarialCheck : Bool :=
  LeanExperiments.Verification.Sorting.Spec.largeAdversarialInputs.all fun input =>
    decide (LeanExperiments.QuickSort.quickSort input =
      LeanExperiments.QuickSort.quickSortIterative input)

/-- 12種類の大規模入力全てでループ版の昇順性と要素保存が成り立つ。 -/
theorem quickSortIterativeLargeAdversarialCheck_passes :
    quickSortIterativeLargeAdversarialCheck = true := by
  native_decide

/-- 12種類の大規模入力全てで再帰版とループ版が一致する。 -/
theorem quickSortAgreementLargeAdversarialCheck_passes :
    quickSortAgreementLargeAdversarialCheck = true := by
  native_decide

/-- 64ビット境界値を含む大規模入力で、反復版の仕様適合を調べる。 -/
def quickSortIterativeLargeWideAdversarialCheck : Bool :=
  LeanExperiments.Verification.Sorting.Spec.largeWideAdversarialInputs.all fun input =>
    LeanExperiments.Verification.Sorting.Spec.correctCheck input
      (LeanExperiments.QuickSort.quickSortIterative input)

/-- 64ビット境界値を含む大規模入力で、再帰版との出力一致を調べる。 -/
def quickSortAgreementLargeWideAdversarialCheck : Bool :=
  LeanExperiments.Verification.Sorting.Spec.largeWideAdversarialInputs.all fun input =>
    decide (LeanExperiments.QuickSort.quickSort input =
      LeanExperiments.QuickSort.quickSortIterative input)

/-- 1023〜1025要素の64ビット境界値入力12件全てで反復版の仕様が成立する。 -/
theorem quickSortIterativeLargeWideAdversarialCheck_passes :
    quickSortIterativeLargeWideAdversarialCheck = true := by
  native_decide

/-- 1023〜1025要素の64ビット境界値入力12件全てで両版の結果が一致する。 -/
theorem quickSortAgreementLargeWideAdversarialCheck_passes :
    quickSortAgreementLargeWideAdversarialCheck = true := by
  native_decide

/-- 大きな64ビット境界値入力ごとに、反復版の `Correct` を取り出す。 -/
theorem quickSortIterative_correct_for_largeWideAdversarialInput (input : List Nat)
    (hInput : input ∈ LeanExperiments.Verification.Sorting.Spec.largeWideAdversarialInputs) :
    LeanExperiments.Verification.Sorting.Spec.Correct input
      (LeanExperiments.QuickSort.quickSortIterative input) := by
  have hAll := List.all_eq_true.mp quickSortIterativeLargeWideAdversarialCheck_passes
  exact LeanExperiments.Verification.Sorting.Spec.correctCheck_sound input _ (hAll input hInput)

/-- 境界値入力に含まれる任意の列で、再帰版の `Correct` を取り出せる。 -/
theorem quickSort_correct_for_wideAdversarialInput (input : List Nat)
    (hInput : input ∈ LeanExperiments.Verification.Sorting.Spec.wideAdversarialInputs) :
    LeanExperiments.Verification.Sorting.Spec.Correct input
      (LeanExperiments.QuickSort.quickSort input) := by
  have hAll : ∀ candidate ∈ LeanExperiments.Verification.Sorting.Spec.wideAdversarialInputs,
      LeanExperiments.Verification.Sorting.Spec.correctCheck candidate
        (LeanExperiments.QuickSort.quickSort candidate) = true :=
    List.all_eq_true.mp quickSortWideAdversarialCheck_passes
  exact LeanExperiments.Verification.Sorting.Spec.correctCheck_sound input _ (hAll input hInput)

/-- 境界値入力に含まれる任意の列で、ループ版の `Correct` を取り出せる。 -/
theorem quickSortIterative_correct_for_wideAdversarialInput (input : List Nat)
    (hInput : input ∈ LeanExperiments.Verification.Sorting.Spec.wideAdversarialInputs) :
    LeanExperiments.Verification.Sorting.Spec.Correct input
      (LeanExperiments.QuickSort.quickSortIterative input) := by
  have hAll : ∀ candidate ∈ LeanExperiments.Verification.Sorting.Spec.wideAdversarialInputs,
      LeanExperiments.Verification.Sorting.Spec.correctCheck candidate
        (LeanExperiments.QuickSort.quickSortIterative candidate) = true :=
    List.all_eq_true.mp quickSortIterativeWideAdversarialCheck_passes
  exact LeanExperiments.Verification.Sorting.Spec.correctCheck_sound input _ (hAll input hInput)

/-- 有限領域に含まれる入力について、再帰版の `Correct` を得る。 -/
theorem quickSort_correct_for_boundedInput (input : List Nat)
    (hInput : input ∈ LeanExperiments.Verification.Sorting.Spec.boundedInputs) :
    LeanExperiments.Verification.Sorting.Spec.Correct input
      (LeanExperiments.QuickSort.quickSort input) := by
  have hAll : ∀ candidate ∈ LeanExperiments.Verification.Sorting.Spec.boundedInputs,
      LeanExperiments.Verification.Sorting.Spec.correctCheck candidate
        (LeanExperiments.QuickSort.quickSort candidate) = true :=
    List.all_eq_true.mp quickSortBoundedCheck_passes
  exact LeanExperiments.Verification.Sorting.Spec.correctCheck_sound input _ (hAll input hInput)

/-- 有限領域に含まれる入力について、ループ版の `Correct` を得る。 -/
theorem quickSortIterative_correct_for_boundedInput (input : List Nat)
    (hInput : input ∈ LeanExperiments.Verification.Sorting.Spec.boundedInputs) :
    LeanExperiments.Verification.Sorting.Spec.Correct input
      (LeanExperiments.QuickSort.quickSortIterative input) := by
  have hAll : ∀ candidate ∈ LeanExperiments.Verification.Sorting.Spec.boundedInputs,
      LeanExperiments.Verification.Sorting.Spec.correctCheck candidate
        (LeanExperiments.QuickSort.quickSortIterative candidate) = true :=
    List.all_eq_true.mp quickSortIterativeBoundedCheck_passes
  exact LeanExperiments.Verification.Sorting.Spec.correctCheck_sound input _ (hAll input hInput)

/-- 有限領域に含まれる入力について、両実装の結果が等しい。 -/
theorem quickSort_implementations_agree_for_boundedInput (input : List Nat)
    (hInput : input ∈ LeanExperiments.Verification.Sorting.Spec.boundedInputs) :
    LeanExperiments.QuickSort.quickSort input =
      LeanExperiments.QuickSort.quickSortIterative input := by
  have hAll : ∀ candidate ∈ LeanExperiments.Verification.Sorting.Spec.boundedInputs,
      decide (LeanExperiments.QuickSort.quickSort candidate =
        LeanExperiments.QuickSort.quickSortIterative candidate) = true :=
    List.all_eq_true.mp quickSortAgreementBoundedCheck_passes
  exact of_decide_eq_true (hAll input hInput)

/-- 拡張有限領域に含まれる入力では、ループ版も共通ソート仕様を満たす。 -/
theorem quickSortIterative_correct_for_stressInput (input : List Nat)
    (hInput : input ∈ LeanExperiments.Verification.Sorting.Spec.stressInputs) :
    LeanExperiments.Verification.Sorting.Spec.Correct input
      (LeanExperiments.QuickSort.quickSortIterative input) := by
  have hAll : ∀ candidate ∈ LeanExperiments.Verification.Sorting.Spec.stressInputs,
      LeanExperiments.Verification.Sorting.Spec.correctCheck candidate
        (LeanExperiments.QuickSort.quickSortIterative candidate) = true :=
    List.all_eq_true.mp quickSortIterativeStressCheck_passes
  exact LeanExperiments.Verification.Sorting.Spec.correctCheck_sound input _ (hAll input hInput)

/-- 拡張有限領域に含まれる入力では、両実装の結果が一致する。 -/
theorem quickSort_implementations_agree_for_stressInput (input : List Nat)
    (hInput : input ∈ LeanExperiments.Verification.Sorting.Spec.stressInputs) :
    LeanExperiments.QuickSort.quickSort input =
      LeanExperiments.QuickSort.quickSortIterative input := by
  have hAll : ∀ candidate ∈ LeanExperiments.Verification.Sorting.Spec.stressInputs,
      decide (LeanExperiments.QuickSort.quickSort candidate =
        LeanExperiments.QuickSort.quickSortIterative candidate) = true :=
    List.all_eq_true.mp quickSortAgreementStressCheck_passes
  exact of_decide_eq_true (hAll input hInput)

/-- 大きな値を含む有限領域では、ループ版も共通ソート仕様を満たす。 -/
theorem quickSortIterative_correct_for_wideValueInput (input : List Nat)
    (hInput : input ∈ LeanExperiments.Verification.Sorting.Spec.wideValueInputs) :
    LeanExperiments.Verification.Sorting.Spec.Correct input
      (LeanExperiments.QuickSort.quickSortIterative input) := by
  have hAll : ∀ candidate ∈ LeanExperiments.Verification.Sorting.Spec.wideValueInputs,
      LeanExperiments.Verification.Sorting.Spec.correctCheck candidate
        (LeanExperiments.QuickSort.quickSortIterative candidate) = true :=
    List.all_eq_true.mp quickSortIterativeWideValueCheck_passes
  exact LeanExperiments.Verification.Sorting.Spec.correctCheck_sound input _ (hAll input hInput)

/-- 大きな値を含む有限領域では、両実装の結果が一致する。 -/
theorem quickSort_implementations_agree_for_wideValueInput (input : List Nat)
    (hInput : input ∈ LeanExperiments.Verification.Sorting.Spec.wideValueInputs) :
    LeanExperiments.QuickSort.quickSort input =
      LeanExperiments.QuickSort.quickSortIterative input := by
  have hAll : ∀ candidate ∈ LeanExperiments.Verification.Sorting.Spec.wideValueInputs,
      decide (LeanExperiments.QuickSort.quickSort candidate =
        LeanExperiments.QuickSort.quickSortIterative candidate) = true :=
    List.all_eq_true.mp quickSortAgreementWideValueCheck_passes
  exact of_decide_eq_true (hAll input hInput)

/-- 長さ境界の偏り入力では、ループ版も共通ソート仕様を満たす。 -/
theorem quickSortIterative_correct_for_adversarialInput (input : List Nat)
    (hInput : input ∈ LeanExperiments.Verification.Sorting.Spec.adversarialInputs) :
    LeanExperiments.Verification.Sorting.Spec.Correct input
      (LeanExperiments.QuickSort.quickSortIterative input) := by
  have hAll : ∀ candidate ∈ LeanExperiments.Verification.Sorting.Spec.adversarialInputs,
      LeanExperiments.Verification.Sorting.Spec.correctCheck candidate
        (LeanExperiments.QuickSort.quickSortIterative candidate) = true :=
    List.all_eq_true.mp quickSortIterativeAdversarialCheck_passes
  exact LeanExperiments.Verification.Sorting.Spec.correctCheck_sound input _ (hAll input hInput)

/-- 長さ境界の偏り入力では、両実装の結果が一致する。 -/
theorem quickSort_implementations_agree_for_adversarialInput (input : List Nat)
    (hInput : input ∈ LeanExperiments.Verification.Sorting.Spec.adversarialInputs) :
    LeanExperiments.QuickSort.quickSort input =
      LeanExperiments.QuickSort.quickSortIterative input := by
  have hAll : ∀ candidate ∈ LeanExperiments.Verification.Sorting.Spec.adversarialInputs,
      decide (LeanExperiments.QuickSort.quickSort candidate =
        LeanExperiments.QuickSort.quickSortIterative candidate) = true :=
    List.all_eq_true.mp quickSortAgreementAdversarialCheck_passes
  exact of_decide_eq_true (hAll input hInput)

end LeanExperiments.Verification.QuickSort
