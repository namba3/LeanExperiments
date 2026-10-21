import Std.WP
import Std.Tactic.Do
set_option experimental.intrinsic true

/-!
# クイックソート

先頭の値を pivot として残りのリストを 2 つに分け、それぞれを再帰的に整列する。
pivot 以下の値を左側、pivot より大きい値を右側へ分け、最後に 3 つを連結する。
-/

namespace LeanExperiments.QuickSort

/-- pivot を基準に分割し、再帰的に整列するクイックソート。

同じ値は pivot と一緒に左側へ送る。左右どちらの部分リストも残りの入力から
要素を選び出したものなので、入力全体より短く、再帰は停止する。

pivot の選び方により、すでに整列した入力などでは分割が偏り、再帰の深さが
線形になることがある。この素朴な実装は学習用で、最悪時の高速化は扱わない。
-/
def quickSort : List Nat → List Nat
  | [] => []
  | pivot :: rest =>
    let lower := rest.filter (· ≤ pivot)
    let upper := rest.filter (pivot < ·)
    quickSort lower ++ pivot :: quickSort upper
termination_by values => values.length
decreasing_by
  all_goals simp_wf
  · have hFilter : (rest.attach.filter (fun x => decide (x.val ≤ pivot))).length ≤ rest.length := by
      calc
        _ ≤ rest.attach.length := List.length_filter_le _ _
        _ = rest.length := by simp
    simpa using Nat.lt_succ_of_le hFilter
  · have hFilter : (rest.attach.filter (fun x => decide (pivot < x.val))).length ≤ rest.length := by
      calc
        _ ≤ rest.attach.length := List.length_filter_le _ _
        _ = rest.length := by simp
    simpa using Nat.lt_succ_of_le hFilter

/-- ループ版で使う、処理対象リストと出力値を表すスタック項目。 -/
inductive QuickSortTask where
  | sort (values : List Nat)
  | emit (value : Nat)
  deriving Inhabited

/-- 各スタック項目に割り当てる停止測度。分割で増える子タスクも含め、各反復で減少する。 -/
def quickSortTaskPotential : QuickSortTask → Nat
  | .sort values => 3 * values.length + 1
  | .emit _ => 1

/-- スタック全体の停止測度。 -/
def quickSortTaskStackPotential (tasks : Array QuickSortTask) : Nat :=
  tasks.toList.foldl (fun total task => total + quickSortTaskPotential task) 0

/-- タスクを一つ積むとき、停止測度はそのタスクの測度分だけ増える。 -/
theorem quickSortTaskStackPotential_push (tasks : Array QuickSortTask)
    (task : QuickSortTask) :
    quickSortTaskStackPotential (tasks.push task) =
      quickSortTaskStackPotential tasks + quickSortTaskPotential task := by
  simp [quickSortTaskStackPotential, Array.toList_push, List.foldl_append]

/-- 非空スタックの測度は、末尾タスクと残りの測度の和に分解できる。 -/
theorem quickSortTaskStackPotential_pop_back (tasks : Array QuickSortTask)
    (h : tasks.size ≠ 0) :
    quickSortTaskStackPotential tasks =
      quickSortTaskStackPotential tasks.pop + quickSortTaskPotential tasks.back! := by
  rw [Array.eq_push_pop_back!_of_size_ne_zero h,
    quickSortTaskStackPotential_push]
  simp only [Array.pop_push, Array.back!_push]

/-- 分割した右部分、pivot 出力、左部分をこの順に積み、左側を次に処理させる。 -/
def pushQuickSortTasks (tasks : Array QuickSortTask) (lower upper : List Nat) (pivot : Nat) :
    Array QuickSortTask :=
  ((tasks.push (.sort upper)).push (.emit pivot)).push (.sort lower)

/-- ループ版 quick sort の一反復を表す状態遷移。呼び出し時はタスクスタックが非空である。 -/
def quickSortTaskStackStep (state : Array QuickSortTask × Array Nat) :
    Array QuickSortTask × Array Nat :=
  let (tasks, output) := state
  let task := tasks.back!
  let tasks := tasks.pop
  match task with
  | .sort [] => (tasks, output)
  | .sort (pivot :: rest) =>
    let lower := rest.filter (· ≤ pivot)
    let upper := rest.filter (pivot < ·)
    (pushQuickSortTasks tasks lower upper pivot, output)
  | .emit value => (tasks, output.push value)

/-- 分割後の三タスクを積んだときの測度を、各タスクの測度へ展開する。 -/
theorem quickSortTaskStackPotential_pushQuickSortTasks
    (tasks : Array QuickSortTask) (lower upper : List Nat) (pivot : Nat) :
    quickSortTaskStackPotential (pushQuickSortTasks tasks lower upper pivot) =
      quickSortTaskStackPotential tasks +
        quickSortTaskPotential (.sort upper) + quickSortTaskPotential (.emit pivot) +
        quickSortTaskPotential (.sort lower) := by
  simp [pushQuickSortTasks, quickSortTaskStackPotential_push, Nat.add_assoc]

/-- 再帰呼び出しを明示的なスタックで置き換えたクイックソート。

`sort` 項目を処理すると、スタックへ右側、基準値、左側の順で追加する。スタックは
後入れ先出しなので、実際には左側、基準値、右側の順に処理され、再帰版と同じ出力順になる。
-/
def quickSortIterative (values : List Nat) : List Nat := Id.run do
  let mut state := (#[QuickSortTask.sort values], #[])
  while !state.1.isEmpty decreasing quickSortTaskStackPotential state.1 do
    state := quickSortTaskStackStep state
  return state.2.toList

end LeanExperiments.QuickSort
