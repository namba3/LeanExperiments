import Std.WP
import Std.Tactic.Do
set_option experimental.intrinsic true

/-!
# ヒープソート

最大ヒープを配列で表し、自然数列を昇順に並べ替える。
配列は二分木を幅優先順に格納する。添字 `i` の左の子は `2*i+1`、
右の子は `2*i+2` で、親の値が子の値以上になることをヒープ条件とする。

このモジュールは実行可能なアルゴリズム本体を置く場所であり、仕様や
正しさの証明は `LeanExperiments.Verification.HeapSort.Spec` に分けている。
-/

namespace LeanExperiments.HeapSort

/-- 配列の `i` 番目と `j` 番目を交換する。添字が範囲外なら配列を変えない。 -/
def swap (values : Array Nat) (i j : Nat) : Array Nat :=
  values.swapIfInBounds i j

/-- 添字交換は配列の長さを保つ。下降処理の配列状態を確認する補題として使える。 -/
theorem swap_size (values : Array Nat) (i j : Nat) :
    (swap values i j).size = values.size := by
  unfold swap
  exact Array.size_swapIfInBounds

/-- 範囲外の添字を許す交換処理も、配列の要素を順列として保つ。 -/
theorem swap_toList_perm (values : Array Nat) (i j : Nat) :
    (swap values i j).toList.Perm values.toList := by
  unfold swap
  by_cases hi : i < values.size
  · by_cases hj : j < values.size
    · have hSwap : values.swapIfInBounds i j = values.swap i j := by
        simp [Array.swapIfInBounds, hi, hj]
      rw [hSwap]
      exact Array.perm_iff_toList_perm.mp (Array.swap_perm hi hj)
    · simp [Array.swapIfInBounds, hi, hj]
  · simp [Array.swapIfInBounds, hi]

/-- 根と左右の子のうち、値が最大の位置を返す。

下降版のループと再帰版で同じ選択規則を使う。子が存在しない場合はその候補を
無視し、比較が同値なら現在の位置を保つ。実装間の一致を検証するため公開する。
-/
def siftDownLargest (values : Array Nat) (index : Nat) : Nat :=
  let left := 2 * index + 1
  let right := left + 1
  let afterLeft :=
    if left < values.size && values[index]! < values[left]! then left else index
  if right < values.size && values[afterLeft]! < values[right]! then right else afterLeft

/-- 下降ループの一段を表す状態遷移。

現在位置とその子の最大候補を交換し、次に調べる添字と配列を返す。候補が現在位置なら
交換は恒等になり、呼び出し側は添字が変わらないことからループを終了できる。
-/
def siftDownStep (values : Array Nat) (index : Nat) : Array Nat × Nat :=
  let largest := siftDownLargest values index
  (swap values index largest, largest)

/-- 子の部分木がすでにヒープであるとき、`root` 以下のヒープ条件を回復する。

根と左右の子を比べて最大の値を選ぶ。子が最大ならその子と交換して下へ進み、
根が最大なら条件を満たしたので終了する。
-/
def siftDown (values : Array Nat) (root : Nat) : Array Nat := Id.run do
  let mut current := values
  let mut index := root
  let mut running := true
  while running decreasing current.size - index + (if running then 1 else 0) do
    let (nextValues, nextIndex) := siftDownStep current index
    if nextIndex == index then
      running := false
    else
      current := nextValues
      index := nextIndex
  return current

/-- 選ばれる最大候補は、現在位置より後ろか同じ位置にある。 -/
theorem siftDownLargest_ge (values : Array Nat) (index : Nat) :
    index ≤ siftDownLargest values index := by
  dsimp [siftDownLargest]
  split <;> split <;> omega

/-- 下降処理が選ぶ添字は、現在位置か、その左右いずれかの子である。 -/
theorem siftDownLargest_eq_root_or_child (values : Array Nat) (index : Nat) :
    siftDownLargest values index = index ∨
      siftDownLargest values index = 2 * index + 1 ∨
      siftDownLargest values index = 2 * index + 2 := by
  dsimp [siftDownLargest]
  split <;> split <;> simp_all

/-- 交換する二位置より前の添字の値は変化しない。 -/
private theorem swap_getElem!_eq_of_lt_left (values : Array Nat) (i j k : Nat)
    (hk : k < values.size) (hki : k < i) (hij : i ≤ j) :
    (swap values i j)[k]! = values[k]! := by
  unfold swap
  by_cases hi : i < values.size
  · by_cases hj : j < values.size
    · rw [Array.swapIfInBounds_def, dite_eq_left hi, dite_eq_left hj]
      rw [getElem!_pos _ k (by simpa using hk), getElem!_pos _ k hk]
      exact Array.getElem_swap_of_ne (by omega) (by omega)
    · simp [Array.swapIfInBounds_def, hi, hj]
  · simp [Array.swapIfInBounds_def, hi]

/-- `siftDown` の再帰版を、段数 `fuel` を明示して定義する。

ヒープの下降先は配列内の子の添字なので、1 回進むたびに少なくとも 1 つ深くなる。
初期 fuel に配列長を使えば葉に達するまでの段数を十分に覆える。fuel が 0 に
なる場合も現在の配列を返すため、この関数自体は全ての引数で停止する。
-/
def siftDownFuel : Nat → Array Nat → Nat → Array Nat
  | 0, values, _ => values
  | fuel + 1, values, index =>
    let largest := siftDownLargest values index
    if largest == index then
      values
    else
      siftDownFuel fuel (swap values index largest) largest

/-- 再帰によって根から葉へ進み、最大ヒープ条件を回復する。 -/
def siftDownRecursive (values : Array Nat) (root : Nat) : Array Nat :=
  siftDownFuel values.size values root

/-- `root + fuel` が配列長以上なら、下降のfuelを一つ減らしても結果は変わらない。 -/
theorem siftDownFuel_succ_eq_of_size_le_fuel_add_root
    (fuel : Nat) (values : Array Nat) (root : Nat)
    (hSize : values.size ≤ fuel + root) :
    siftDownFuel (fuel + 1) values root = siftDownFuel fuel values root := by
  induction fuel generalizing values root with
  | zero =>
      have hRoot : values.size ≤ root := by omega
      have hLeft : ¬ 2 * root + 1 < values.size := by omega
      have hRight : ¬ 2 * root + 2 < values.size := by omega
      simp [siftDownFuel, siftDownLargest, hRoot, hLeft, hRight]
  | succ fuel ih =>
      let largest := siftDownLargest values root
      have hRootLeLargest : root ≤ largest := by
        dsimp [largest, siftDownLargest]
        split <;> split <;> omega
      by_cases hDone : largest = root
      · simp [siftDownFuel, largest, hDone]
      · have hSwapSize : (swap values root largest).size = values.size := by
          by_cases hRoot : root < values.size
          · by_cases hLargest : largest < values.size
            · simp [swap, Array.swapIfInBounds, hRoot, hLargest]
            · simp [swap, Array.swapIfInBounds, hRoot, hLargest]
          · simp [swap, Array.swapIfInBounds, hRoot]
        have hNextSize : (swap values root largest).size ≤ fuel + largest := by
          rw [hSwapSize]
          omega
        have hNext := ih (swap values root largest) largest hNextSize
        have hNotStopped : (largest == root) = false := by simp [hDone]
        change (if largest == root then values else
            siftDownFuel (fuel + 1) (swap values root largest) largest) =
          if largest == root then values else
            siftDownFuel fuel (swap values root largest) largest
        rw [hNotStopped]
        exact hNext

/-- fuel が根から葉までの必要段数以上なら、それより大きな fuel は結果を変えない。 -/
theorem siftDownFuel_eq_of_size_le_fuel_add_root (fuel : Nat) (values : Array Nat)
    (root : Nat) (hSize : values.size ≤ fuel + root) :
    siftDownFuel fuel values root = siftDownFuel (values.size - root) values root := by
  induction fuel generalizing values root with
  | zero =>
      have hRoot : values.size ≤ root := by omega
      simp [Nat.sub_eq_zero_of_le hRoot]
  | succ fuel ih =>
      by_cases hEnough : values.size - root ≤ fuel
      · have hSmallerBound : values.size ≤ fuel + root := by omega
        rw [siftDownFuel_succ_eq_of_size_le_fuel_add_root fuel values root hSmallerBound]
        exact ih values root hSmallerBound
      · have hExact : fuel + 1 = values.size - root := by omega
        rw [hExact]

/-- 再帰版下降は、根から葉までの必要段数だけ fuel を与えた結果と一致する。 -/
theorem siftDownRecursive_eq_siftDownFuel_sub_root (values : Array Nat) (root : Nat) :
    siftDownRecursive values root = siftDownFuel (values.size - root) values root := by
  unfold siftDownRecursive
  exact siftDownFuel_eq_of_size_le_fuel_add_root values.size values root (by omega)

/-- 選択した子と交換して再帰する一段は、下降全体の結果を変えない。 -/
theorem siftDownRecursive_eq_siftDownRecursive_after_swap
    (values : Array Nat) (root largest : Nat)
    (hLargest : siftDownLargest values root = largest)
    (hMovesDown : largest ≠ root) :
    siftDownRecursive values root =
      siftDownRecursive (swap values root largest) largest := by
  have hRootLt : root < values.size := by
    by_cases hRoot : root < values.size
    · exact hRoot
    · have hNoLeft : ¬ 2 * root + 1 < values.size := by omega
      have hNoRight : ¬ 2 * root + 2 < values.size := by omega
      have hLargestEq : siftDownLargest values root = root := by
        simp [siftDownLargest, hNoLeft, hNoRight]
      have hLargestRoot : largest = root := hLargest.symm.trans hLargestEq
      exact False.elim (hMovesDown hLargestRoot)
  have hRootLeLargest := siftDownLargest_ge values root
  have hRootLtLargest : root < largest := by omega
  have hFuelPositive : 0 < values.size - root := by omega
  have hFuelStep : values.size - root = (values.size - root - 1) + 1 := by omega
  have hSwapSize : (swap values root largest).size = values.size := swap_size values root largest
  rw [siftDownRecursive_eq_siftDownFuel_sub_root,
    siftDownRecursive_eq_siftDownFuel_sub_root]
  rw [hFuelStep]
  simp only [siftDownFuel]
  simp [hLargest, hMovesDown]
  have hEnough : (swap values root largest).size ≤
      (values.size - root - 1) + largest := by rw [hSwapSize]; omega
  have hStable := siftDownFuel_eq_of_size_le_fuel_add_root
    (values.size - root - 1) (swap values root largest) largest hEnough
  rw [hSwapSize] at hStable
  rw [hSwapSize]
  exact hStable

/-- 任意の fuel 付き下降は、配列長を保存する。 -/
theorem siftDownFuel_size (fuel : Nat) (values : Array Nat) (root : Nat) :
    (siftDownFuel fuel values root).size = values.size := by
  have hSwapSize (array : Array Nat) (i j : Nat) :
      (swap array i j).size = array.size := by
    by_cases hi : i < array.size
    · by_cases hj : j < array.size
      · simp [swap, Array.swapIfInBounds, hi, hj]
      · simp [swap, Array.swapIfInBounds, hi, hj]
    · simp [swap, Array.swapIfInBounds, hi]
  induction fuel generalizing values root with
  | zero => rfl
  | succ fuel ih =>
      simp only [siftDownFuel]
      by_cases hStop : siftDownLargest values root = root
      · simp [hStop]
      · simp [hStop, ih, hSwapSize]

/-- 任意の fuel 付き下降は、要素を順列として保存する。 -/
theorem siftDownFuel_perm (fuel : Nat) (values : Array Nat) (root : Nat) :
    (siftDownFuel fuel values root).toList.Perm values.toList := by
  induction fuel generalizing values root with
  | zero => rfl
  | succ fuel ih =>
      simp only [siftDownFuel]
      by_cases hStop : siftDownLargest values root = root
      · simp [hStop]
      · simp [hStop]
        exact (ih (swap values root (siftDownLargest values root))
          (siftDownLargest values root)).trans
          (swap_toList_perm values root (siftDownLargest values root))

/-- 下降処理は、再帰先より前の添字にある値を変更しない。 -/
theorem siftDownFuel_getElem!_eq_of_lt_root (fuel : Nat) (values : Array Nat)
    (root index : Nat) (hIndex : index < values.size) (hBefore : index < root) :
    (siftDownFuel fuel values root)[index]! = values[index]! := by
  induction fuel generalizing values root with
  | zero => rfl
  | succ fuel ih =>
      simp only [siftDownFuel]
      by_cases hStop : siftDownLargest values root = root
      · simp [hStop]
      · have hRootLeLargest := siftDownLargest_ge values root
        have hIndexLargest : index < siftDownLargest values root := by omega
        have hSwapSize : (swap values root (siftDownLargest values root)).size =
            values.size := by simp [swap]
        have hRecursive := ih (swap values root (siftDownLargest values root))
          (siftDownLargest values root) (by omega) hIndexLargest
        have hFrame := swap_getElem!_eq_of_lt_left values root
          (siftDownLargest values root) index hIndex hBefore hRootLeLargest
        simp [hStop, hRecursive, hFrame]

/-- 2要素配列の根からの下降は、根と子を比較して大きい値を根に置く。 -/
theorem siftDownRecursive_pair (left right : Nat) :
    siftDownRecursive #[left, right] 0 =
      if left < right then #[right, left] else #[left, right] := by
  unfold siftDownRecursive
  change siftDownFuel 2 #[left, right] 0 = _
  by_cases h : left < right
  · simp [siftDownFuel, siftDownLargest, swap, h, Array.swapIfInBounds_def]
  · simp [siftDownFuel, siftDownLargest, h]

/-- 3要素配列の下降結果は、根と2つの葉の比較で決まる。 -/
theorem siftDownRecursive_triple (root left right : Nat) :
    siftDownRecursive #[root, left, right] 0 =
      if root < left then
        if left < right then #[right, left, root] else #[left, root, right]
      else if root < right then #[right, left, root] else #[root, left, right] := by
  unfold siftDownRecursive
  change siftDownFuel 3 #[root, left, right] 0 = _
  by_cases hRootLeft : root < left
  · by_cases hLeftRight : left < right
    · simp [siftDownFuel, siftDownLargest, swap, hRootLeft, hLeftRight,
        Array.swapIfInBounds_def]
    · simp [siftDownFuel, siftDownLargest, swap, hRootLeft, hLeftRight,
        Array.swapIfInBounds_def]
  · by_cases hRootRight : root < right
    · simp [siftDownFuel, siftDownLargest, swap, hRootLeft, hRootRight,
        Array.swapIfInBounds_def]
    · simp [siftDownFuel, siftDownLargest, hRootLeft, hRootRight]

/-- 4要素配列の添字1からの下降は、その節点と唯一の子を比較する。 -/
theorem siftDownRecursive_quad_leftChild (root parent sibling child : Nat) :
    siftDownRecursive #[root, parent, sibling, child] 1 =
      if parent < child then #[root, child, sibling, parent]
      else #[root, parent, sibling, child] := by
  unfold siftDownRecursive
  change siftDownFuel 4 #[root, parent, sibling, child] 1 = _
  by_cases h : parent < child
  · simp [siftDownFuel, siftDownLargest, swap, h, Array.swapIfInBounds_def]
  · simp [siftDownFuel, siftDownLargest, h]

/-- 長さ4の根からの下降結果を、根・子・孫の比較で表す。 -/
theorem siftDownRecursive_quad_root (root left right leaf : Nat) :
    siftDownRecursive #[root, left, right, leaf] 0 =
      if root < left then
        if left < right then #[right, left, root, leaf]
        else if root < leaf then #[left, leaf, right, root]
        else #[left, root, right, leaf]
      else if root < right then #[right, left, root, leaf]
      else #[root, left, right, leaf] := by
  unfold siftDownRecursive
  change siftDownFuel 4 #[root, left, right, leaf] 0 = _
  by_cases hRootLeft : root < left
  · by_cases hLeftRight : left < right
    · simp [siftDownFuel, siftDownLargest, swap, hRootLeft, hLeftRight,
        Array.swapIfInBounds_def]
    · by_cases hRootLeaf : root < leaf
      · simp [siftDownFuel, siftDownLargest, swap, hRootLeft, hLeftRight,
          hRootLeaf, Array.swapIfInBounds_def]
      · simp [siftDownFuel, siftDownLargest, swap, hRootLeft, hLeftRight,
          hRootLeaf, Array.swapIfInBounds_def]
  · by_cases hRootRight : root < right
    · simp [siftDownFuel, siftDownLargest, swap, hRootLeft, hRootRight,
        Array.swapIfInBounds_def]
    · simp [siftDownFuel, siftDownLargest, hRootLeft, hRootRight]

/-- 5要素配列の根からの下降結果を、根・子・孫の比較で表す。 -/
theorem siftDownRecursive_quint_left (root parent sibling leftLeaf rightLeaf : Nat) :
    siftDownRecursive #[root, parent, sibling, leftLeaf, rightLeaf] 1 =
      if parent < leftLeaf then
        if leftLeaf < rightLeaf then #[root, rightLeaf, sibling, leftLeaf, parent]
        else #[root, leftLeaf, sibling, parent, rightLeaf]
      else if parent < rightLeaf then #[root, rightLeaf, sibling, leftLeaf, parent]
      else #[root, parent, sibling, leftLeaf, rightLeaf] := by
  unfold siftDownRecursive
  change siftDownFuel 5 #[root, parent, sibling, leftLeaf, rightLeaf] 1 = _
  by_cases hParentLeftLeaf : parent < leftLeaf
  · by_cases hLeftLeafRightLeaf : leftLeaf < rightLeaf
    · simp [siftDownFuel, siftDownLargest, swap, hParentLeftLeaf,
        hLeftLeafRightLeaf, Array.swapIfInBounds_def]
    · simp [siftDownFuel, siftDownLargest, swap, hParentLeftLeaf,
        hLeftLeafRightLeaf, Array.swapIfInBounds_def]
  · by_cases hParentRightLeaf : parent < rightLeaf
    · simp [siftDownFuel, siftDownLargest, swap, hParentLeftLeaf,
        hParentRightLeaf, Array.swapIfInBounds_def]
    · simp [siftDownFuel, siftDownLargest, hParentLeftLeaf, hParentRightLeaf]

/-- 5要素配列の根からの下降結果を、根・子・孫の比較で表す。 -/
theorem siftDownRecursive_quint_root (root left right leftLeaf rightLeaf : Nat) :
    siftDownRecursive #[root, left, right, leftLeaf, rightLeaf] 0 =
      if root < left then
        if left < right then #[right, left, root, leftLeaf, rightLeaf]
        else if root < leftLeaf then
          if leftLeaf < rightLeaf then #[left, rightLeaf, right, leftLeaf, root]
          else #[left, leftLeaf, right, root, rightLeaf]
        else if root < rightLeaf then #[left, rightLeaf, right, leftLeaf, root]
        else #[left, root, right, leftLeaf, rightLeaf]
      else if root < right then #[right, left, root, leftLeaf, rightLeaf]
      else #[root, left, right, leftLeaf, rightLeaf] := by
  unfold siftDownRecursive
  change siftDownFuel 5 #[root, left, right, leftLeaf, rightLeaf] 0 = _
  by_cases hRootLeft : root < left
  · by_cases hLeftRight : left < right
    · simp [siftDownFuel, siftDownLargest, swap, hRootLeft, hLeftRight,
        Array.swapIfInBounds_def]
    · by_cases hRootLeftLeaf : root < leftLeaf
      · by_cases hLeftLeafRightLeaf : leftLeaf < rightLeaf
        · simp [siftDownFuel, siftDownLargest, swap, hRootLeft, hLeftRight,
            hRootLeftLeaf, hLeftLeafRightLeaf, Array.swapIfInBounds_def]
        · simp [siftDownFuel, siftDownLargest, swap, hRootLeft, hLeftRight,
            hRootLeftLeaf, hLeftLeafRightLeaf, Array.swapIfInBounds_def]
      · by_cases hRootRightLeaf : root < rightLeaf
        · simp [siftDownFuel, siftDownLargest, swap, hRootLeft, hLeftRight,
            hRootLeftLeaf, hRootRightLeaf, Array.swapIfInBounds_def]
        · simp [siftDownFuel, siftDownLargest, swap, hRootLeft, hLeftRight,
            hRootLeftLeaf, hRootRightLeaf, Array.swapIfInBounds_def]
  · by_cases hRootRight : root < right
    · simp [siftDownFuel, siftDownLargest, swap, hRootLeft, hRootRight,
        Array.swapIfInBounds_def]
    · simp [siftDownFuel, siftDownLargest, hRootLeft, hRootRight]

/-- 6要素配列の根からの下降結果を、根・子・孫の比較で表す。 -/
theorem siftDownRecursive_sext_root
    (root left right leftLeaf rightLeaf rightChild : Nat) :
    siftDownRecursive #[root, left, right, leftLeaf, rightLeaf, rightChild] 0 =
      if root < left then
        if left < right then
          if root < rightChild then #[right, left, rightChild, leftLeaf, rightLeaf, root]
          else #[right, left, root, leftLeaf, rightLeaf, rightChild]
        else if root < leftLeaf then
          if leftLeaf < rightLeaf then #[left, rightLeaf, right, leftLeaf, root, rightChild]
          else #[left, leftLeaf, right, root, rightLeaf, rightChild]
        else if root < rightLeaf then #[left, rightLeaf, right, leftLeaf, root, rightChild]
        else #[left, root, right, leftLeaf, rightLeaf, rightChild]
      else if root < right then
        if root < rightChild then #[right, left, rightChild, leftLeaf, rightLeaf, root]
        else #[right, left, root, leftLeaf, rightLeaf, rightChild]
      else #[root, left, right, leftLeaf, rightLeaf, rightChild] := by
  unfold siftDownRecursive
  change siftDownFuel 6 #[root, left, right, leftLeaf, rightLeaf, rightChild] 0 = _
  by_cases hRootLeft : root < left
  · by_cases hLeftRight : left < right
    · by_cases hRootRightChild : root < rightChild
      · simp [siftDownFuel, siftDownLargest, swap, hRootLeft, hLeftRight,
          hRootRightChild, Array.swapIfInBounds_def]
      · simp [siftDownFuel, siftDownLargest, swap, hRootLeft, hLeftRight,
          hRootRightChild, Array.swapIfInBounds_def]
    · by_cases hRootLeftLeaf : root < leftLeaf
      · by_cases hLeftLeafRightLeaf : leftLeaf < rightLeaf
        · simp [siftDownFuel, siftDownLargest, swap, hRootLeft, hLeftRight,
            hRootLeftLeaf, hLeftLeafRightLeaf, Array.swapIfInBounds_def]
        · simp [siftDownFuel, siftDownLargest, swap, hRootLeft, hLeftRight,
            hRootLeftLeaf, hLeftLeafRightLeaf, Array.swapIfInBounds_def]
      · by_cases hRootRightLeaf : root < rightLeaf
        · simp [siftDownFuel, siftDownLargest, swap, hRootLeft, hLeftRight,
            hRootLeftLeaf, hRootRightLeaf, Array.swapIfInBounds_def]
        · simp [siftDownFuel, siftDownLargest, swap, hRootLeft, hLeftRight,
            hRootLeftLeaf, hRootRightLeaf, Array.swapIfInBounds_def]
  · by_cases hRootRight : root < right
    · by_cases hRootRightChild : root < rightChild
      · simp [siftDownFuel, siftDownLargest, swap, hRootLeft, hRootRight,
          hRootRightChild, Array.swapIfInBounds_def]
      · simp [siftDownFuel, siftDownLargest, swap, hRootLeft, hRootRight,
          hRootRightChild, Array.swapIfInBounds_def]
    · simp [siftDownFuel, siftDownLargest, hRootLeft, hRootRight]

/-- 6要素配列の添字1からの下降は、左右の葉を比較して値を移す。 -/
theorem siftDownRecursive_sext_left
    (root parent sibling leftLeaf rightLeaf tail : Nat) :
    siftDownRecursive #[root, parent, sibling, leftLeaf, rightLeaf, tail] 1 =
      if parent < leftLeaf then
        if leftLeaf < rightLeaf then #[root, rightLeaf, sibling, leftLeaf, parent, tail]
        else #[root, leftLeaf, sibling, parent, rightLeaf, tail]
      else if parent < rightLeaf then #[root, rightLeaf, sibling, leftLeaf, parent, tail]
      else #[root, parent, sibling, leftLeaf, rightLeaf, tail] := by
  unfold siftDownRecursive
  change siftDownFuel 6 #[root, parent, sibling, leftLeaf, rightLeaf, tail] 1 = _
  by_cases hParentLeftLeaf : parent < leftLeaf
  · by_cases hLeftLeafRightLeaf : leftLeaf < rightLeaf
    · simp [siftDownFuel, siftDownLargest, swap, hParentLeftLeaf,
        hLeftLeafRightLeaf, Array.swapIfInBounds_def]
    · simp [siftDownFuel, siftDownLargest, swap, hParentLeftLeaf,
        hLeftLeafRightLeaf, Array.swapIfInBounds_def]
  · by_cases hParentRightLeaf : parent < rightLeaf
    · simp [siftDownFuel, siftDownLargest, swap, hParentLeftLeaf,
        hParentRightLeaf, Array.swapIfInBounds_def]
    · simp [siftDownFuel, siftDownLargest, hParentLeftLeaf, hParentRightLeaf]

/-- 6要素配列の添字2からの下降は、その節点と唯一の子を比較する。 -/
theorem siftDownRecursive_sext_right
    (root left parent leftLeaf rightLeaf child : Nat) :
    siftDownRecursive #[root, left, parent, leftLeaf, rightLeaf, child] 2 =
      if parent < child then #[root, left, child, leftLeaf, rightLeaf, parent]
      else #[root, left, parent, leftLeaf, rightLeaf, child] := by
  unfold siftDownRecursive
  change siftDownFuel 6 #[root, left, parent, leftLeaf, rightLeaf, child] 2 = _
  by_cases h : parent < child
  · simp [siftDownFuel, siftDownLargest, swap, h, Array.swapIfInBounds_def]
  · simp [siftDownFuel, siftDownLargest, h]

/-- 7要素配列の添字2からの下降は、左右の葉の最大値をその位置へ移す。 -/
theorem siftDownRecursive_sept_right
    (root left parent leftLeaf rightLeaf leftChild rightChild : Nat) :
    siftDownRecursive
        #[root, left, parent, leftLeaf, rightLeaf, leftChild, rightChild] 2 =
      if parent < leftChild then
        if leftChild < rightChild then
          #[root, left, rightChild, leftLeaf, rightLeaf, leftChild, parent]
        else #[root, left, leftChild, leftLeaf, rightLeaf, parent, rightChild]
      else if parent < rightChild then
        #[root, left, rightChild, leftLeaf, rightLeaf, leftChild, parent]
      else #[root, left, parent, leftLeaf, rightLeaf, leftChild, rightChild] := by
  unfold siftDownRecursive
  change siftDownFuel 7
    #[root, left, parent, leftLeaf, rightLeaf, leftChild, rightChild] 2 = _
  by_cases hParentLeft : parent < leftChild
  · by_cases hLeftRight : leftChild < rightChild
    · simp [siftDownFuel, siftDownLargest, swap, hParentLeft, hLeftRight,
        Array.swapIfInBounds_def]
    · simp [siftDownFuel, siftDownLargest, swap, hParentLeft, hLeftRight,
        Array.swapIfInBounds_def]
  · by_cases hParentRight : parent < rightChild
    · simp [siftDownFuel, siftDownLargest, swap, hParentLeft, hParentRight,
        Array.swapIfInBounds_def]
    · simp [siftDownFuel, siftDownLargest, hParentLeft, hParentRight]

/-- 7要素配列の添字1からの下降は、左右の葉を比較して値を移す。 -/
theorem siftDownRecursive_sept_left
    (root parent sibling leftLeaf rightLeaf tailLeft tailRight : Nat) :
    siftDownRecursive
        #[root, parent, sibling, leftLeaf, rightLeaf, tailLeft, tailRight] 1 =
      if parent < leftLeaf then
        if leftLeaf < rightLeaf then
          #[root, rightLeaf, sibling, leftLeaf, parent, tailLeft, tailRight]
        else #[root, leftLeaf, sibling, parent, rightLeaf, tailLeft, tailRight]
      else if parent < rightLeaf then
        #[root, rightLeaf, sibling, leftLeaf, parent, tailLeft, tailRight]
      else #[root, parent, sibling, leftLeaf, rightLeaf, tailLeft, tailRight] := by
  unfold siftDownRecursive
  change siftDownFuel 7
    #[root, parent, sibling, leftLeaf, rightLeaf, tailLeft, tailRight] 1 = _
  by_cases hParentLeftLeaf : parent < leftLeaf
  · by_cases hLeftLeafRightLeaf : leftLeaf < rightLeaf
    · simp [siftDownFuel, siftDownLargest, swap, hParentLeftLeaf,
        hLeftLeafRightLeaf, Array.swapIfInBounds_def]
    · simp [siftDownFuel, siftDownLargest, swap, hParentLeftLeaf,
        hLeftLeafRightLeaf, Array.swapIfInBounds_def]
  · by_cases hParentRightLeaf : parent < rightLeaf
    · simp [siftDownFuel, siftDownLargest, swap, hParentLeftLeaf,
        hParentRightLeaf, Array.swapIfInBounds_def]
    · simp [siftDownFuel, siftDownLargest, hParentLeftLeaf, hParentRightLeaf]

/-- 7要素配列の根からの下降結果は、最大の子と孫を選ぶ比較で決まる。 -/
theorem siftDownRecursive_sept_root
    (root left right leftLeft leftRight rightLeft rightRight : Nat) :
    siftDownRecursive
        #[root, left, right, leftLeft, leftRight, rightLeft, rightRight] 0 =
      if root < left then
        if left < right then
          if root < rightLeft then
            if rightLeft < rightRight then
              #[right, left, rightRight, leftLeft, leftRight, rightLeft, root]
            else #[right, left, rightLeft, leftLeft, leftRight, root, rightRight]
          else if root < rightRight then
            #[right, left, rightRight, leftLeft, leftRight, rightLeft, root]
          else #[right, left, root, leftLeft, leftRight, rightLeft, rightRight]
        else if root < leftLeft then
          if leftLeft < leftRight then
            #[left, leftRight, right, leftLeft, root, rightLeft, rightRight]
          else #[left, leftLeft, right, root, leftRight, rightLeft, rightRight]
        else if root < leftRight then
          #[left, leftRight, right, leftLeft, root, rightLeft, rightRight]
        else #[left, root, right, leftLeft, leftRight, rightLeft, rightRight]
      else if root < right then
        if root < rightLeft then
          if rightLeft < rightRight then
            #[right, left, rightRight, leftLeft, leftRight, rightLeft, root]
          else #[right, left, rightLeft, leftLeft, leftRight, root, rightRight]
        else if root < rightRight then
          #[right, left, rightRight, leftLeft, leftRight, rightLeft, root]
        else #[right, left, root, leftLeft, leftRight, rightLeft, rightRight]
      else #[root, left, right, leftLeft, leftRight, rightLeft, rightRight] := by
  unfold siftDownRecursive
  change siftDownFuel 7
    #[root, left, right, leftLeft, leftRight, rightLeft, rightRight] 0 = _
  by_cases hRootLeft : root < left
  · by_cases hLeftRight : left < right
    · by_cases hRootRightLeft : root < rightLeft
      · by_cases hRightLeftRight : rightLeft < rightRight
        · simp [siftDownFuel, siftDownLargest, swap, hRootLeft, hLeftRight,
            hRootRightLeft, hRightLeftRight, Array.swapIfInBounds_def]
        · simp [siftDownFuel, siftDownLargest, swap, hRootLeft, hLeftRight,
            hRootRightLeft, hRightLeftRight, Array.swapIfInBounds_def]
      · by_cases hRootRightRight : root < rightRight
        · simp [siftDownFuel, siftDownLargest, swap, hRootLeft, hLeftRight,
            hRootRightLeft, hRootRightRight, Array.swapIfInBounds_def]
        · simp [siftDownFuel, siftDownLargest, swap, hRootLeft, hLeftRight,
            hRootRightLeft, hRootRightRight, Array.swapIfInBounds_def]
    · by_cases hRootLeftLeft : root < leftLeft
      · by_cases hLeftLeftRight : leftLeft < leftRight
        · simp [siftDownFuel, siftDownLargest, swap, hRootLeft, hLeftRight,
            hRootLeftLeft, hLeftLeftRight, Array.swapIfInBounds_def]
        · simp [siftDownFuel, siftDownLargest, swap, hRootLeft, hLeftRight,
            hRootLeftLeft, hLeftLeftRight, Array.swapIfInBounds_def]
      · by_cases hRootLeftRight : root < leftRight
        · simp [siftDownFuel, siftDownLargest, swap, hRootLeft, hLeftRight,
            hRootLeftLeft, hRootLeftRight, Array.swapIfInBounds_def]
        · simp [siftDownFuel, siftDownLargest, swap, hRootLeft, hLeftRight,
            hRootLeftLeft, hRootLeftRight, Array.swapIfInBounds_def]
  · by_cases hRootRight : root < right
    · by_cases hRootRightLeft : root < rightLeft
      · by_cases hRightLeftRight : rightLeft < rightRight
        · simp [siftDownFuel, siftDownLargest, swap, hRootLeft, hRootRight,
            hRootRightLeft, hRightLeftRight, Array.swapIfInBounds_def]
        · simp [siftDownFuel, siftDownLargest, swap, hRootLeft, hRootRight,
            hRootRightLeft, hRightLeftRight, Array.swapIfInBounds_def]
      · by_cases hRootRightRight : root < rightRight
        · simp [siftDownFuel, siftDownLargest, swap, hRootLeft, hRootRight,
            hRootRightLeft, hRootRightRight, Array.swapIfInBounds_def]
        · simp [siftDownFuel, siftDownLargest, swap, hRootLeft, hRootRight,
            hRootRightLeft, hRootRightRight, Array.swapIfInBounds_def]
    · simp [siftDownFuel, siftDownLargest, hRootLeft, hRootRight]

/-- 8要素配列の根からの下降では、左側の深い部分木にも再帰的に進む。 -/
theorem siftDownRecursive_oct_root
    (root left right leftLeft leftRight rightLeft rightRight leftLeftLeft : Nat) :
    siftDownRecursive
        #[root, left, right, leftLeft, leftRight, rightLeft, rightRight,
          leftLeftLeft] 0 =
      if root < left then
        if left < right then
          if root < rightLeft then
            if rightLeft < rightRight then
              #[right, left, rightRight, leftLeft, leftRight, rightLeft, root,
                leftLeftLeft]
            else #[right, left, rightLeft, leftLeft, leftRight, root, rightRight,
              leftLeftLeft]
          else if root < rightRight then
            #[right, left, rightRight, leftLeft, leftRight, rightLeft, root,
              leftLeftLeft]
          else #[right, left, root, leftLeft, leftRight, rightLeft, rightRight,
            leftLeftLeft]
        else if root < leftLeft then
          if leftLeft < leftRight then
            #[left, leftRight, right, leftLeft, root, rightLeft, rightRight,
              leftLeftLeft]
          else if root < leftLeftLeft then
            #[left, leftLeft, right, leftLeftLeft, leftRight, rightLeft, rightRight,
              root]
          else #[left, leftLeft, right, root, leftRight, rightLeft, rightRight,
            leftLeftLeft]
        else if root < leftRight then
          #[left, leftRight, right, leftLeft, root, rightLeft, rightRight,
            leftLeftLeft]
        else #[left, root, right, leftLeft, leftRight, rightLeft, rightRight,
          leftLeftLeft]
      else if root < right then
        if root < rightLeft then
          if rightLeft < rightRight then
            #[right, left, rightRight, leftLeft, leftRight, rightLeft, root,
              leftLeftLeft]
          else #[right, left, rightLeft, leftLeft, leftRight, root, rightRight,
            leftLeftLeft]
        else if root < rightRight then
          #[right, left, rightRight, leftLeft, leftRight, rightLeft, root,
            leftLeftLeft]
        else #[right, left, root, leftLeft, leftRight, rightLeft, rightRight,
          leftLeftLeft]
      else #[root, left, right, leftLeft, leftRight, rightLeft, rightRight,
        leftLeftLeft] := by
  unfold siftDownRecursive
  change siftDownFuel 8
    #[root, left, right, leftLeft, leftRight, rightLeft, rightRight, leftLeftLeft] 0 = _
  by_cases hRootLeft : root < left
  · by_cases hLeftRight : left < right
    · by_cases hRootRightLeft : root < rightLeft
      · by_cases hRightLeftRight : rightLeft < rightRight
        · simp [siftDownFuel, siftDownLargest, swap, hRootLeft, hLeftRight,
            hRootRightLeft, hRightLeftRight, Array.swapIfInBounds_def]
        · simp [siftDownFuel, siftDownLargest, swap, hRootLeft, hLeftRight,
            hRootRightLeft, hRightLeftRight, Array.swapIfInBounds_def]
      · by_cases hRootRightRight : root < rightRight
        · simp [siftDownFuel, siftDownLargest, swap, hRootLeft, hLeftRight,
            hRootRightLeft, hRootRightRight, Array.swapIfInBounds_def]
        · simp [siftDownFuel, siftDownLargest, swap, hRootLeft, hLeftRight,
            hRootRightLeft, hRootRightRight, Array.swapIfInBounds_def]
    · by_cases hRootLeftLeft : root < leftLeft
      · by_cases hLeftLeftRight : leftLeft < leftRight
        · simp [siftDownFuel, siftDownLargest, swap, hRootLeft, hLeftRight,
            hRootLeftLeft, hLeftLeftRight, Array.swapIfInBounds_def]
        · by_cases hRootLeftLeftLeft : root < leftLeftLeft
          · simp [siftDownFuel, siftDownLargest, swap, hRootLeft, hLeftRight,
              hRootLeftLeft, hLeftLeftRight, hRootLeftLeftLeft,
              Array.swapIfInBounds_def]
          · simp [siftDownFuel, siftDownLargest, swap, hRootLeft, hLeftRight,
              hRootLeftLeft, hLeftLeftRight, hRootLeftLeftLeft,
              Array.swapIfInBounds_def]
      · by_cases hRootLeftRight : root < leftRight
        · simp [siftDownFuel, siftDownLargest, swap, hRootLeft, hLeftRight,
            hRootLeftLeft, hRootLeftRight, Array.swapIfInBounds_def]
        · simp [siftDownFuel, siftDownLargest, swap, hRootLeft, hLeftRight,
            hRootLeftLeft, hRootLeftRight, Array.swapIfInBounds_def]
  · by_cases hRootRight : root < right
    · by_cases hRootRightLeft : root < rightLeft
      · by_cases hRightLeftRight : rightLeft < rightRight
        · simp [siftDownFuel, siftDownLargest, swap, hRootLeft, hRootRight,
            hRootRightLeft, hRightLeftRight, Array.swapIfInBounds_def]
        · simp [siftDownFuel, siftDownLargest, swap, hRootLeft, hRootRight,
            hRootRightLeft, hRightLeftRight, Array.swapIfInBounds_def]
      · by_cases hRootRightRight : root < rightRight
        · simp [siftDownFuel, siftDownLargest, swap, hRootLeft, hRootRight,
            hRootRightLeft, hRootRightRight, Array.swapIfInBounds_def]
        · simp [siftDownFuel, siftDownLargest, swap, hRootLeft, hRootRight,
            hRootRightLeft, hRootRightRight, Array.swapIfInBounds_def]
    · simp [siftDownFuel, siftDownLargest, hRootLeft, hRootRight]

/-- 8要素配列の添字3からの下降は、唯一の子である添字7と比較する。 -/
theorem siftDownRecursive_oct_leftmost
    (root left right leftLeft leftRight rightLeft rightRight leftLeftLeft : Nat) :
    siftDownRecursive
        #[root, left, right, leftLeft, leftRight, rightLeft, rightRight,
          leftLeftLeft] 3 =
      if leftLeft < leftLeftLeft then
        #[root, left, right, leftLeftLeft, leftRight, rightLeft, rightRight,
          leftLeft]
      else #[root, left, right, leftLeft, leftRight, rightLeft, rightRight,
        leftLeftLeft] := by
  unfold siftDownRecursive
  change siftDownFuel 8
    #[root, left, right, leftLeft, leftRight, rightLeft, rightRight, leftLeftLeft] 3 = _
  by_cases h : leftLeft < leftLeftLeft
  · simp [siftDownFuel, siftDownLargest, swap, h, Array.swapIfInBounds_def]
  · simp [siftDownFuel, siftDownLargest, h]

/-- 8要素配列の添字2からの下降は、左右の葉の最大値をその位置へ移す。 -/
theorem siftDownRecursive_oct_right
    (root left parent leftLeaf rightLeaf leftChild rightChild tail : Nat) :
    siftDownRecursive
        #[root, left, parent, leftLeaf, rightLeaf, leftChild, rightChild, tail] 2 =
      if parent < leftChild then
        if leftChild < rightChild then
          #[root, left, rightChild, leftLeaf, rightLeaf, leftChild, parent, tail]
        else #[root, left, leftChild, leftLeaf, rightLeaf, parent, rightChild, tail]
      else if parent < rightChild then
        #[root, left, rightChild, leftLeaf, rightLeaf, leftChild, parent, tail]
      else #[root, left, parent, leftLeaf, rightLeaf, leftChild, rightChild, tail] := by
  unfold siftDownRecursive
  change siftDownFuel 8
    #[root, left, parent, leftLeaf, rightLeaf, leftChild, rightChild, tail] 2 = _
  by_cases hParentLeft : parent < leftChild
  · by_cases hLeftRight : leftChild < rightChild
    · simp [siftDownFuel, siftDownLargest, swap, hParentLeft, hLeftRight,
        Array.swapIfInBounds_def]
    · simp [siftDownFuel, siftDownLargest, swap, hParentLeft, hLeftRight,
        Array.swapIfInBounds_def]
  · by_cases hParentRight : parent < rightChild
    · simp [siftDownFuel, siftDownLargest, swap, hParentLeft, hParentRight,
        Array.swapIfInBounds_def]
    · simp [siftDownFuel, siftDownLargest, hParentLeft, hParentRight]

/-- 8要素配列の添字1下降は、左の孫にも必要なら進んでヒープ条件を回復する。 -/
theorem siftDownRecursive_oct_left
    (root parent sibling leftChild rightLeaf tailLeft tailRight leftGrandchild : Nat) :
    siftDownRecursive
        #[root, parent, sibling, leftChild, rightLeaf, tailLeft, tailRight,
          leftGrandchild] 1 =
      if parent < leftChild then
        if leftChild < rightLeaf then
          #[root, rightLeaf, sibling, leftChild, parent, tailLeft, tailRight,
            leftGrandchild]
        else if parent < leftGrandchild then
          #[root, leftChild, sibling, leftGrandchild, rightLeaf, tailLeft, tailRight,
            parent]
        else #[root, leftChild, sibling, parent, rightLeaf, tailLeft, tailRight,
          leftGrandchild]
      else if parent < rightLeaf then
        #[root, rightLeaf, sibling, leftChild, parent, tailLeft, tailRight,
          leftGrandchild]
      else #[root, parent, sibling, leftChild, rightLeaf, tailLeft, tailRight,
        leftGrandchild] := by
  unfold siftDownRecursive
  change siftDownFuel 8
    #[root, parent, sibling, leftChild, rightLeaf, tailLeft, tailRight,
      leftGrandchild] 1 = _
  by_cases hParentLeft : parent < leftChild
  · by_cases hLeftRight : leftChild < rightLeaf
    · simp [siftDownFuel, siftDownLargest, swap, hParentLeft, hLeftRight,
        Array.swapIfInBounds_def]
    · by_cases hParentGrandchild : parent < leftGrandchild
      · simp [siftDownFuel, siftDownLargest, swap, hParentLeft, hLeftRight,
          hParentGrandchild, Array.swapIfInBounds_def]
      · simp [siftDownFuel, siftDownLargest, swap, hParentLeft, hLeftRight,
          hParentGrandchild, Array.swapIfInBounds_def]
  · by_cases hParentRight : parent < rightLeaf
    · simp [siftDownFuel, siftDownLargest, swap, hParentLeft, hParentRight,
        Array.swapIfInBounds_def]
    · simp [siftDownFuel, siftDownLargest, hParentLeft, hParentRight]

/-- 9要素配列の添字3からの下降は、左右の葉7・8の大きい方を選ぶ。 -/
theorem siftDownRecursive_nine_leftmost
    (root left right parent child4 child5 child6 leftLeaf rightLeaf : Nat) :
    siftDownRecursive #[root, left, right, parent, child4, child5, child6,
      leftLeaf, rightLeaf] 3 =
      if parent < leftLeaf then
        if leftLeaf < rightLeaf then
          #[root, left, right, rightLeaf, child4, child5, child6, leftLeaf, parent]
        else #[root, left, right, leftLeaf, child4, child5, child6, parent, rightLeaf]
      else if parent < rightLeaf then
        #[root, left, right, rightLeaf, child4, child5, child6, leftLeaf, parent]
      else #[root, left, right, parent, child4, child5, child6, leftLeaf, rightLeaf] := by
  unfold siftDownRecursive
  change siftDownFuel 9
    #[root, left, right, parent, child4, child5, child6, leftLeaf, rightLeaf] 3 = _
  by_cases hParentLeft : parent < leftLeaf
  · by_cases hLeftRight : leftLeaf < rightLeaf
    · simp [siftDownFuel, siftDownLargest, swap, hParentLeft, hLeftRight,
        Array.swapIfInBounds_def]
    · simp [siftDownFuel, siftDownLargest, swap, hParentLeft, hLeftRight,
        Array.swapIfInBounds_def]
  · by_cases hParentRight : parent < rightLeaf
    · simp [siftDownFuel, siftDownLargest, swap, hParentLeft, hParentRight,
        Array.swapIfInBounds_def]
    · simp [siftDownFuel, siftDownLargest, hParentLeft, hParentRight]

/-- 9要素配列の添字2からの下降は、左右の子5・6から大きい値を選ぶ。 -/
theorem siftDownRecursive_nine_right
    (root left parent leftLeaf rightLeaf leftChild rightChild tailLeft tailRight : Nat) :
    siftDownRecursive #[root, left, parent, leftLeaf, rightLeaf, leftChild, rightChild,
      tailLeft, tailRight] 2 =
      if parent < leftChild then
        if leftChild < rightChild then
          #[root, left, rightChild, leftLeaf, rightLeaf, leftChild, parent,
            tailLeft, tailRight]
        else #[root, left, leftChild, leftLeaf, rightLeaf, parent, rightChild,
          tailLeft, tailRight]
      else if parent < rightChild then
        #[root, left, rightChild, leftLeaf, rightLeaf, leftChild, parent,
          tailLeft, tailRight]
      else #[root, left, parent, leftLeaf, rightLeaf, leftChild, rightChild,
        tailLeft, tailRight] := by
  unfold siftDownRecursive
  change siftDownFuel 9
    #[root, left, parent, leftLeaf, rightLeaf, leftChild, rightChild, tailLeft,
      tailRight] 2 = _
  by_cases hParentLeft : parent < leftChild
  · by_cases hLeftRight : leftChild < rightChild
    · simp [siftDownFuel, siftDownLargest, swap, hParentLeft, hLeftRight,
        Array.swapIfInBounds_def]
    · simp [siftDownFuel, siftDownLargest, swap, hParentLeft, hLeftRight,
        Array.swapIfInBounds_def]
  · by_cases hParentRight : parent < rightChild
    · simp [siftDownFuel, siftDownLargest, swap, hParentLeft, hParentRight,
        Array.swapIfInBounds_def]
    · simp [siftDownFuel, siftDownLargest, hParentLeft, hParentRight]

/-- 9要素配列の添字1下降は、添字3まで進み、その左右の葉も調べる。 -/
theorem siftDownRecursive_nine_left
    (root parent sibling leftChild rightLeaf tailLeft tailRight leftGrandchild
      rightGrandchild : Nat) :
    siftDownRecursive #[root, parent, sibling, leftChild, rightLeaf, tailLeft,
      tailRight, leftGrandchild, rightGrandchild] 1 =
      if parent < leftChild then
        if leftChild < rightLeaf then
          #[root, rightLeaf, sibling, leftChild, parent, tailLeft, tailRight,
            leftGrandchild, rightGrandchild]
        else if parent < leftGrandchild then
          if leftGrandchild < rightGrandchild then
            #[root, leftChild, sibling, rightGrandchild, rightLeaf, tailLeft,
              tailRight, leftGrandchild, parent]
          else #[root, leftChild, sibling, leftGrandchild, rightLeaf, tailLeft,
            tailRight, parent, rightGrandchild]
        else if parent < rightGrandchild then
          #[root, leftChild, sibling, rightGrandchild, rightLeaf, tailLeft,
            tailRight, leftGrandchild, parent]
        else #[root, leftChild, sibling, parent, rightLeaf, tailLeft, tailRight,
          leftGrandchild, rightGrandchild]
      else if parent < rightLeaf then
        #[root, rightLeaf, sibling, leftChild, parent, tailLeft, tailRight,
          leftGrandchild, rightGrandchild]
      else #[root, parent, sibling, leftChild, rightLeaf, tailLeft, tailRight,
        leftGrandchild, rightGrandchild] := by
  unfold siftDownRecursive
  change siftDownFuel 9
    #[root, parent, sibling, leftChild, rightLeaf, tailLeft, tailRight,
      leftGrandchild, rightGrandchild] 1 = _
  by_cases hParentLeft : parent < leftChild
  · by_cases hLeftRight : leftChild < rightLeaf
    · simp [siftDownFuel, siftDownLargest, swap, hParentLeft, hLeftRight,
        Array.swapIfInBounds_def]
    · by_cases hParentLeftGrandchild : parent < leftGrandchild
      · by_cases hLeftRightGrandchild : leftGrandchild < rightGrandchild
        · simp [siftDownFuel, siftDownLargest, swap, hParentLeft, hLeftRight,
            hParentLeftGrandchild, hLeftRightGrandchild, Array.swapIfInBounds_def]
        · simp [siftDownFuel, siftDownLargest, swap, hParentLeft, hLeftRight,
            hParentLeftGrandchild, hLeftRightGrandchild, Array.swapIfInBounds_def]
      · by_cases hParentRightGrandchild : parent < rightGrandchild
        · simp [siftDownFuel, siftDownLargest, swap, hParentLeft, hLeftRight,
            hParentLeftGrandchild, hParentRightGrandchild, Array.swapIfInBounds_def]
        · simp [siftDownFuel, siftDownLargest, swap, hParentLeft, hLeftRight,
            hParentLeftGrandchild, hParentRightGrandchild, Array.swapIfInBounds_def]
  · by_cases hParentRight : parent < rightLeaf
    · simp [siftDownFuel, siftDownLargest, swap, hParentLeft, hParentRight,
        Array.swapIfInBounds_def]
    · simp [siftDownFuel, siftDownLargest, hParentLeft, hParentRight]


/-- すでに根がその子以上なら、fuel 付き下降処理は配列を変更しない。

子が存在する場合の比較だけで `siftDownLargest` が根を選ぶことを示す。
任意の fuel について最初の段階で停止するため、配列全体が同じままになる。
-/
theorem siftDownFuel_eq_self_of_dominatesChildren (fuel : Nat) (values : Array Nat)
    (root : Nat)
    (hLeft : 2 * root + 1 < values.size → values[2 * root + 1]! ≤ values[root]!)
    (hRight : 2 * root + 2 < values.size → values[2 * root + 2]! ≤ values[root]!) :
    siftDownFuel fuel values root = values := by
  have hLeftCondition :
      (decide (2 * root + 1 < values.size) &&
        decide (values[root]! < values[2 * root + 1]!)) = false := by
    by_cases hChild : 2 * root + 1 < values.size
    · have hRoot : root < values.size := by omega
      have hBound : values[2 * root + 1] ≤ values[root] := by
        simpa only [getElem!_pos values (2 * root + 1) hChild,
          getElem!_pos values root hRoot] using hLeft hChild
      simp [hChild, hRoot, hBound]
    · simp [hChild]
  have hRightCondition :
      (decide (2 * root + 2 < values.size) &&
        decide (values[root]! < values[2 * root + 2]!)) = false := by
    by_cases hChild : 2 * root + 2 < values.size
    · have hRoot : root < values.size := by omega
      have hBound : values[2 * root + 2] ≤ values[root] := by
        simpa only [getElem!_pos values (2 * root + 2) hChild,
          getElem!_pos values root hRoot] using hRight hChild
      simp [hChild, hRoot, hBound]
    · simp [hChild]
  have hLargest : siftDownLargest values root = root := by
    unfold siftDownLargest
    simp [hLeftCondition, hRightCondition]
  induction fuel with
  | zero => rfl
  | succ fuel ih => simp [siftDownFuel, hLargest]

/-- 左の子が配列外にある位置では、任意 fuel の下降処理は入力を保つ。 -/
theorem siftDownFuel_eq_self_of_noLeftChild (fuel : Nat) (values : Array Nat)
    (root : Nat) (hNoLeftChild : values.size ≤ 2 * root + 1) :
    siftDownFuel fuel values root = values := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
      have hNoRightChild : values.size ≤ 2 * root + 2 := by omega
      have hLargest : siftDownLargest values root = root := by
        simp [siftDownLargest, hNoLeftChild, hNoRightChild]
      simp [siftDownFuel, hLargest]

/-- すでに根がその子以上なら、再帰版下降処理は配列を変更しない。 -/
theorem siftDownRecursive_eq_self_of_dominatesChildren (values : Array Nat) (root : Nat)
    (hLeft : 2 * root + 1 < values.size → values[2 * root + 1]! ≤ values[root]!)
    (hRight : 2 * root + 2 < values.size → values[2 * root + 2]! ≤ values[root]!) :
    siftDownRecursive values root = values := by
  unfold siftDownRecursive
  exact siftDownFuel_eq_self_of_dominatesChildren values.size values root hLeft hRight

/-- 左の子が配列外にある位置からの再帰下降は、入力配列をそのまま返す。 -/
theorem siftDownRecursive_eq_self_of_noLeftChild (values : Array Nat) (root : Nat)
    (hNoLeftChild : values.size ≤ 2 * root + 1) :
    siftDownRecursive values root = values := by
  unfold siftDownRecursive
  exact siftDownFuel_eq_self_of_noLeftChild values.size values root hNoLeftChild

/-- 再帰版の下降処理は、どの入力・根位置でも配列長を保つ。 -/
theorem siftDownRecursive_size (values : Array Nat) (root : Nat) :
    (siftDownRecursive values root).size = values.size := by
  exact siftDownFuel_size values.size values root

/-- 再帰版の下降処理は、どの入力・根位置でも要素を順列として保つ。 -/
theorem siftDownRecursive_perm (values : Array Nat) (root : Nat) :
    (siftDownRecursive values root).toList.Perm values.toList := by
  exact siftDownFuel_perm values.size values root

/-- 任意の配列を最大ヒープにする。

葉はそれだけでヒープなので、最後の親から根へ向かって `siftDown` を適用する。
子の部分木を先に整えてから親を処理することで、全体のヒープ条件を構成する。
-/
def buildMaxHeap (values : Array Nat) : Array Nat := Id.run do
  let mut heap := values
  let mut next := values.size / 2
  while next > 0 decreasing next do
    -- `next` を先に 1 減らすので、最初に処理する親は size/2 - 1 になる。
    next := next - 1
    heap := siftDown heap next
  return heap

/-- 最後の親から根へ、再帰版の `siftDown` を適用して最大ヒープを作る。

ループ版と同じ順序で添字を処理するが、残りの添字を再帰呼び出しで表す。
-/
def buildMaxHeapRecursive (values : Array Nat) : Array Nat :=
  go (values.size / 2) values
where
  go : Nat → Array Nat → Array Nat
    | 0, heap => heap
    | next + 1, heap => go next (siftDownRecursive heap next)

/-- 最大ヒープの根から最大値を取り出し、残りのヒープと組にして返す。

空配列なら `none` を返す。空でなければ末尾を根へ移し、根から下へ整え直す。
-/
def popMax (heap : Array Nat) : Option (Nat × Array Nat) := do
  let maximum ← heap[0]?
  let last ← heap.back?
  let rest := heap.pop
  if rest.isEmpty then
    some (maximum, rest)
  else
    some (maximum, siftDown (rest.set! 0 last) 0)

/-- `popMax` の再帰版。末尾の値を根へ移し、再帰版 `siftDown` で整える。 -/
def popMaxRecursive (heap : Array Nat) : Option (Nat × Array Nat) := do
  let maximum ← heap[0]?
  let last ← heap.back?
  let rest := heap.pop
  if rest.isEmpty then
    some (maximum, rest)
  else
    some (maximum, siftDownRecursive (rest.set! 0 last) 0)

/-- 最大値を繰り返し取り出す再帰ループ。

取り出し回数を fuel にし、各値を配列へ追加する。最大値は降順に取り出されるので、
全ての値を集めた後に反転して昇順にする。
-/
def drainRecursive : Nat → Array Nat → Array Nat → Array Nat
  | 0, _, output => output.reverse
  | fuel + 1, heap, output =>
    match popMaxRecursive heap with
    | none => output.reverse
    | some (maximum, rest) => drainRecursive fuel rest (output.push maximum)

/-- 配列を再帰的なヒープ構築・下降処理で昇順に並べ替える。 -/
def heapSortRecursive (values : Array Nat) : Array Nat :=
  drainRecursive values.size (buildMaxHeapRecursive values) #[]

/-- 最大ヒープを使って自然数の配列を昇順に並べ替える。

最大値を繰り返し取り出すと降順の列が得られるため、最後に配列を反転する。
-/
def heapSort (values : Array Nat) : Array Nat := Id.run do
  let mut heap := buildMaxHeap values
  let mut output := #[]
  let mut remaining := values.size
  while remaining > 0 decreasing remaining do
    remaining := remaining - 1
    if let some (maximum, rest) := popMax heap then
      -- 取り出した値は大きい順に並ぶ。最後の reverse で昇順にする。
      output := output.push maximum
      heap := rest
  return output.reverse

end LeanExperiments.HeapSort
