import Std.WP
import Std.Tactic.Do
set_option experimental.intrinsic true

/-!
# マージソート

リストを前半と後半に分けて再帰的に整列し、2 つの整列済みリストを併合する。
入力を変更せず、新しいリストを作る関数型の実装である。
-/

namespace LeanExperiments.MergeSort

/-- 2 つの昇順リストを、昇順を保ったまま 1 つに併合する。

先頭要素を比較し、小さい方を結果の先頭へ移す。同じ値なら左側を先に選ぶため、
左側の要素を先に並べる安定な併合になる。片方が空になったら、もう片方の残りを
そのまま付け足せばよい。
-/
def merge : List Nat → List Nat → List Nat
  | [], right => right
  | left, [] => left
  | leftHead :: leftTail, rightHead :: rightTail =>
    if leftHead ≤ rightHead then
      leftHead :: merge leftTail (rightHead :: rightTail)
    else
      rightHead :: merge (leftHead :: leftTail) rightTail
termination_by left right => left.length + right.length
decreasing_by all_goals simp_wf <;> omega

/-- リストを半分に分けて整列し、最後に併合する。

長さが 0 または 1 のリストはすでに整列済みなので、そのまま返す。
それより長い場合は中央の位置で `take` と `drop` に分ける。各部分リストは
元のリストより短くなるため、再帰呼び出しは必ず停止する。
-/
def mergeSort (values : List Nat) : List Nat :=
  if values.length ≤ 1 then
    values
  else
    let middle := values.length / 2
    merge (mergeSort (values.take middle)) (mergeSort (values.drop middle))
termination_by values.length
decreasing_by
  all_goals simp_wf
  all_goals
    have hHalf : values.length / 2 < values.length := by omega
    omega

/-- 2 つの整列済みリストをループで併合する。

再帰版 `merge` と同じ比較順で先頭を選び、逆順の出力へ追加する。片側が尽きたら
空側に対する `merge` の基底節で残りを受け取り、出力を反転して先頭へ連結する。
-/
def mergeIterative (left right : List Nat) : List Nat := Id.run do
  let mut leftRemaining := left
  let mut rightRemaining := right
  let mut outputReversed := []
  while !leftRemaining.isEmpty && !rightRemaining.isEmpty
    decreasing leftRemaining.length + rightRemaining.length
  do
    match leftRemaining with
    | [] => pure ()
    | leftHead :: leftTail =>
      match rightRemaining with
      | [] => pure ()
      | rightHead :: rightTail =>
        if leftHead ≤ rightHead then
          outputReversed := leftHead :: outputReversed
          leftRemaining := leftTail
        else
          outputReversed := rightHead :: outputReversed
          rightRemaining := rightTail
  return outputReversed.reverse ++ merge leftRemaining rightRemaining

/-- 隣り合う run を一組ずつ反復版 `merge` で併合する一 pass。 -/
def mergePassIterative : List (List Nat) → List (List Nat)
  | [] => []
  | [run] => [run]
  | left :: right :: rest => mergeIterative left right :: mergePassIterative rest
termination_by runs => runs.length
decreasing_by all_goals simp_wf <;> omega

/-- 各要素を 1 個の run として始め、隣り合う run を反復的に併合する。

run が 1 個以下になった時点で全体が整列済みである。各 pass で隣り合う run を
まとめるため、分割位置を計算せずに反復版のマージソートを構成できる。
-/
def mergeSortIterative (values : List Nat) : List Nat := Id.run do
  let mut runs := values.map (fun value => [value])
  while runs.length > 1
    decreasing runs.length
  do
    runs := mergePassIterative runs
  return runs.headD []

end LeanExperiments.MergeSort
