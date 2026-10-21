import Std.WP

set_option experimental.intrinsic true

/-!
# 二つのヒープによる逐次中央値

下側の値を最大ヒープ、上側の値を最小ヒープで保持する。両ヒープの大きさを
揃えることで、値を一つ受け取るたびに中央値を定数時間で参照できる。
各ヒープの挿入・取り出しは配列で表した二分ヒープ上で行う。
-/

namespace LeanExperiments.RunningMedian

/-- 値 `candidate` が `current` よりヒープの根に近い優先度を持つか判定する。 -/
def swap (values : Array Nat) (left right : Nat) : Array Nat :=
  let leftValue := values[left]!
  let rightValue := values[right]!
  (values.set! left rightValue).set! right leftValue

/-- 優先度関数に従って、追加した末尾要素を親方向へ移動する。 -/
def siftUp (prefer : Nat → Nat → Bool) (heap : Array Nat)
    (start : Nat) : Array Nat := Id.run do
  let mut values := heap
  let mut index := start
  while index > 0 decreasing index do
    let parent := (index - 1) / 2
    if prefer values[index]! values[parent]! then
      values := swap values index parent
      index := parent
    else
      break
  return values

/-- siftDown の現在位置と左右の子から、次に交換する候補を選ぶ。 -/
def siftDownBest (prefer : Nat → Nat → Bool) (heap : Array Nat)
    (index : Nat) : Nat :=
  let left := 2 * index + 1
  let right := left + 1
  let best := if left < heap.size && prefer heap[left]! heap[index]! then left else index
  if right < heap.size && prefer heap[right]! heap[best]! then right else best

/-- siftDown の1反復を、更新後の配列・添字・継続フラグとして表す。 -/
def siftDownStep (prefer : Nat → Nat → Bool) (heap : Array Nat)
    (index : Nat) : Array Nat × Nat × Bool :=
  let best := siftDownBest prefer heap index
  if best == index then (heap, index, false)
  else (swap heap index best, best, true)

/-- 優先度関数に従って、根要素を子方向へ移動する。 -/
def siftDown (prefer : Nat → Nat → Bool) (heap : Array Nat)
    (start : Nat) : Array Nat := Id.run do
  let mut values := heap
  let mut index := start
  let mut running := true
  while running decreasing values.size - index + (if running then 1 else 0) do
    let (nextValues, nextIndex, nextRunning) := siftDownStep prefer values index
    values := nextValues
    index := nextIndex
    running := nextRunning
  return values

/-- 二分ヒープへ値を一つ追加する。 -/
def insertHeap (prefer : Nat → Nat → Bool) (heap : Array Nat)
    (value : Nat) : Array Nat :=
  let withValue := heap.push value
  siftUp prefer withValue (withValue.size - 1)

/-- 二分ヒープの根を取り出し、残りのヒープとともに返す。 -/
def popHeap (prefer : Nat → Nat → Bool)
    (heap : Array Nat) : Option (Nat × Array Nat) := do
  let root ← heap[0]?
  let last ← heap.back?
  let rest := heap.pop
  if rest.isEmpty then
    some (root, rest)
  else
    some (root, siftDown prefer (rest.set! 0 last) 0)

/-- 最大ヒープで、候補が現在値より優先される条件。 -/
def maxPrefer (candidate current : Nat) : Bool := current < candidate
/-- 最小ヒープで、候補が現在値より優先される条件。 -/
def minPrefer (candidate current : Nat) : Bool := candidate < current

/-- 下側の根を上側へ移す1回の状態遷移。根を取り出せない場合は何も返さない。 -/
def transferLowerRoot (sourcePrefer destinationPrefer : Nat → Nat → Bool)
    (lower upper : Array Nat) : Option (Array Nat × Array Nat) := do
  let (value, rest) ← popHeap sourcePrefer lower
  pure (rest, insertHeap destinationPrefer upper value)

/-- 上側の根を下側へ移す1回の状態遷移。根を取り出せない場合は何も返さない。 -/
def transferUpperRoot (sourcePrefer destinationPrefer : Nat → Nat → Bool)
    (lower upper : Array Nat) : Option (Array Nat × Array Nat) := do
  let (value, rest) ← popHeap sourcePrefer upper
  pure (insertHeap destinationPrefer lower value, rest)

/-- 下側ヒープが2つ多い間、最大値を上側へ移してサイズ差を修正する。 -/
def rebalanceLower (lower upper : Array Nat) : Array Nat × Array Nat := Id.run do
  let mut lower := lower
  let mut upper := upper
  while lower.size > upper.size + 1 decreasing lower.size do
    if let some (nextLower, nextUpper) := transferLowerRoot maxPrefer minPrefer lower upper then
      lower := nextLower
      upper := nextUpper
    else
      break
  return (lower, upper)

/-- 上側ヒープが大きい間、最小値を下側へ移してサイズ差を修正する。 -/
def rebalanceUpper (lower upper : Array Nat) : Array Nat × Array Nat := Id.run do
  let mut lower := lower
  let mut upper := upper
  while upper.size > lower.size decreasing upper.size do
    if let some (nextLower, nextUpper) := transferUpperRoot minPrefer maxPrefer lower upper then
      lower := nextLower
      upper := nextUpper
    else
      break
  return (lower, upper)

/-- 中央値計算器の状態。`lower` は最大ヒープ、`upper` は最小ヒープ。 -/
structure State where
  lower : Array Nat := #[]
  upper : Array Nat := #[]
  deriving Repr, DecidableEq

/-- 値を一つも受け取っていない初期状態。 -/
def empty : State := {}

/-- 新しい値を二つのヒープへ挿入し、要素数の差を高々一つに保つ。 -/
def insert (state : State) (value : Nat) : State := Id.run do
  -- 最初の値は再平衡を必要としないため、空状態からの遷移を直接返す。
  if state.lower.isEmpty && state.upper.isEmpty then
    return { lower := #[value], upper := #[] }
  let mut lower := state.lower
  let mut upper := state.upper
  if let some lowerMaximum := lower[0]? then
    if value ≤ lowerMaximum then
      lower := insertHeap maxPrefer lower value
    else
      upper := insertHeap minPrefer upper value
  else
    lower := insertHeap maxPrefer lower value

  -- 下側が2つ多い場合と上側が多い場合を別々のループ契約に分けて修正する。
  let (balancedLower, balancedUpper) := rebalanceLower lower upper
  let (finalLower, finalUpper) := rebalanceUpper balancedLower balancedUpper
  return { lower := finalLower, upper := finalUpper }

/-- 入力配列の全要素を順に挿入して状態を作る。 -/
def ofArray (values : Array Nat) : State :=
  values.foldl insert empty

/-- 現時点の中央値を既約化前の分子・分母で返す。

要素数が奇数なら分母は 1、偶数なら中央二値の平均として分母は 2。
空の入力には中央値がないため `none` を返す。
-/
def median (state : State) : Option (Nat × Nat) :=
  if state.lower.size > state.upper.size then
    (state.lower[0]?).map fun value => (value, 1)
  else
    match state.lower[0]?, state.upper[0]? with
    | some lowerMaximum, some upperMinimum =>
        some (lowerMaximum + upperMinimum, 2)
    | _, _ => none

/-- 配列を読み込み、その全要素に対する中央値を返す。 -/
def medianOf (values : Array Nat) : Option (Nat × Nat) :=
  median (ofArray values)

end LeanExperiments.RunningMedian
