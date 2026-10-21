/-!
# ソート共通の仕様

リストを使うソート実装に共通する「昇順」と「要素の保存」を定義する。
この仕様から有限領域の網羅確認や、正しいソート結果の一意性を導く。
-/

namespace LeanExperiments.Verification.Sorting.Spec

/-- リストが昇順であるとは、隣り合う要素が左から右へ非減少であること。 -/
def Ascending : List Nat → Prop
  | [] => True
  | [_] => True
  | first :: second :: rest => first ≤ second ∧ Ascending (second :: rest)

/-- `Ascending` の判定可能な証拠を、リストの構造に沿って構成する。 -/
private def decideAscending : (values : List Nat) → Decidable (Ascending values)
  | [] => isTrue trivial
  | [_] => isTrue trivial
  | first :: second :: rest =>
    if h : first ≤ second then
      match decideAscending (second :: rest) with
      | isTrue hRest => isTrue ⟨h, hRest⟩
      | isFalse hRest => isFalse (fun hAscending => hRest hAscending.2)
    else
      isFalse (fun hAscending => h hAscending.1)

/-- 昇順性を計算可能な真偽値として判定する。 -/
def ascendingCheck (values : List Nat) : Bool :=
  match decideAscending values with
  | isTrue _ => true
  | isFalse _ => false

/-- Boolean 判定が成功することと、論理仕様の昇順性は同値である。 -/
theorem ascendingCheck_correct (values : List Nat) :
    ascendingCheck values = true ↔ Ascending values := by
  unfold ascendingCheck
  cases h : decideAscending values with
  | isTrue hAscending => simp [hAscending]
  | isFalse hNotAscending => simp [hNotAscending]

/-- ソート結果に求める性質。昇順であり、入力との順列関係を保つ。 -/
def Correct (input output : List Nat) : Prop :=
  Ascending output ∧ output.Perm input

/-- 非減少関数による写像は、昇順性を保つ。 -/
theorem Ascending.map {values : List Nat} (f : Nat → Nat)
    (hMonotone : ∀ ⦃a b⦄, a ≤ b → f a ≤ f b)
    (hAscending : Ascending values) : Ascending (values.map f) := by
  induction values with
  | nil => trivial
  | cons first tail ih =>
    cases tail with
    | nil => trivial
    | cons second rest =>
      change f first ≤ f second ∧ Ascending ((second :: rest).map f)
      exact ⟨hMonotone hAscending.1, ih hAscending.2⟩

/-- 非減少関数で入力と結果を写しても、ソート正当性が保たれる。 -/
theorem Correct.map {input output : List Nat} (f : Nat → Nat)
    (hMonotone : ∀ ⦃a b⦄, a ≤ b → f a ≤ f b)
    (hCorrect : Correct input output) : Correct (input.map f) (output.map f) := by
  constructor
  · exact Ascending.map f hMonotone hCorrect.1
  · exact hCorrect.2.map f

/-- 正しいソート結果は入力と同じ要素数を持つ。 -/
theorem Correct.length_eq {input output : List Nat} (hCorrect : Correct input output) :
    output.length = input.length := hCorrect.2.length_eq

/-- 正しいソート結果の要素総和は入力と等しい。 -/
theorem Correct.sum_eq {input output : List Nat} (hCorrect : Correct input output) :
    output.sum = input.sum := hCorrect.2.sum_nat

/-- 正しいソート結果は、任意の判定条件を満たす要素数も入力と同じに保つ。

特定の値の出現回数だけでなく、区間条件や分類条件など、Boolean述語で定まる任意の
部分集合について個数を比較できる。ソートが順列関係を保つことから従う。
-/
theorem Correct.countP_eq {input output : List Nat} (hCorrect : Correct input output)
    (predicate : Nat → Bool) :
    output.countP predicate = input.countP predicate := hCorrect.2.countP_eq predicate

/-- 正しいソート結果では、任意の値の出現回数が入力と一致する。 -/
theorem Correct.count_eq {input output : List Nat} (hCorrect : Correct input output)
    (value : Nat) : output.count value = input.count value :=
  hCorrect.2.count_eq value

/-- `Correct` を実行可能な Boolean 判定にしたもの。 -/
def correctCheck (input output : List Nat) : Bool :=
  ascendingCheck output && output.isPerm input

/-- Boolean 判定の成功からソート正当性を取り出す。 -/
theorem correctCheck_sound (input output : List Nat)
    (h : correctCheck input output = true) : Correct input output := by
  unfold correctCheck at h
  rw [Bool.and_eq_true] at h
  constructor
  · exact ascendingCheck_correct output |>.mp h.1
  · exact List.isPerm_iff.mp h.2

/-- 昇順性と要素保存が成り立てば、Boolean 正当性検査も成功する。 -/
theorem correctCheck_complete (input output : List Nat)
    (hCorrect : Correct input output) : correctCheck input output = true := by
  unfold correctCheck
  rw [Bool.and_eq_true]
  exact ⟨ascendingCheck_correct output |>.mpr hCorrect.1,
    List.isPerm_iff.mpr hCorrect.2⟩

/-- 共通のBooleanソート検査器は論理仕様と同値である。 -/
theorem correctCheck_iff (input output : List Nat) :
    correctCheck input output = true ↔ Correct input output := by
  constructor
  · exact correctCheck_sound input output
  · exact correctCheck_complete input output

/-- 出力要素の保存が別途分かるとき、Boolean 検査器は昇順性だけを判定すればよい。

実装ごとに順列保存を一般証明した後、独立した検査器との残る照合義務を昇順性へ
切り分けるために使う。ソート実装の内部状態や処理手順には依存しない。
-/
theorem correctCheck_iff_ascending_of_perm (input output : List Nat)
    (hPerm : output.Perm input) :
    correctCheck input output = true ↔ Ascending output := by
  constructor
  · intro hCheck
    exact (correctCheck_sound input output hCheck).1
  · intro hAscending
    exact correctCheck_complete input output ⟨hAscending, hPerm⟩

/-- `Pairwise` で全要素間の順序が分かれば、隣接要素の昇順性も得られる。 -/
theorem pairwise_ascending : ∀ values,
    values.Pairwise (fun a b : Nat => a ≤ b) → Ascending values
  | [], _ => trivial
  | [_], _ => trivial
  | first :: second :: rest, hSorted => by
    refine ⟨List.rel_of_pairwise_cons hSorted (by simp), ?_⟩
    exact pairwise_ascending (second :: rest) hSorted.tail

/-- 隣接昇順性と自然数の推移律から、全要素間の `Pairwise` 順序を得る。 -/
theorem ascending_pairwise : ∀ values,
    Ascending values → values.Pairwise (fun a b : Nat => a ≤ b)
  | [], _ => .nil
  | [value], _ => .cons (by intro other h; simp at h) .nil
  | first :: second :: rest, hAscending => by
    apply List.Pairwise.cons
    · intro later hLater
      have hTail := ascending_pairwise (second :: rest) hAscending.2
      simp only [List.mem_cons] at hLater
      rcases hLater with rfl | hLater
      · exact hAscending.1
      · exact Nat.le_trans hAscending.1 (List.rel_of_pairwise_cons hTail hLater)
    · exact ascending_pairwise (second :: rest) hAscending.2

/-- 狭義の全順序関係が成り立つ列には重複がない。 -/
private theorem pairwise_lt_nodup : ∀ values : List Nat,
    values.Pairwise (fun left right => left < right) → values.Nodup
  | [], _ => by simp
  | head :: tail, hPairwise => by
      apply List.nodup_cons.mpr
      refine ⟨?_, pairwise_lt_nodup tail hPairwise.tail⟩
      intro hMem
      have hLt := List.rel_of_pairwise_cons hPairwise hMem
      exact Nat.lt_irrefl head hLt

/-- 昇順かつ重複のない自然数列は全ての前後要素間で狭義昇順である。 -/
private theorem ascending_nodup_pairwise_lt : ∀ values : List Nat,
    Ascending values → values.Nodup →
      values.Pairwise (fun left right => left < right)
  | [], _, _ => .nil
  | [head], _, _ => .cons (by intro other h; simp at h) .nil
  | head :: next :: tail, hAscending, hNodup => by
      have hWeak := ascending_pairwise (head :: next :: tail) hAscending
      have hNodupParts : head ∉ next :: tail ∧ (next :: tail).Nodup :=
        List.nodup_cons.mp hNodup
      apply List.Pairwise.cons
      · intro value hValue
        have hLe := List.rel_of_pairwise_cons hWeak hValue
        have hNe : head ≠ value := by
          intro hEqual
          subst value
          exact hNodupParts.1 hValue
        omega
      · exact ascending_nodup_pairwise_lt (next :: tail) hAscending.2
          hNodupParts.2

/-- 昇順列の先頭 `k` 個には、しきい値未満の要素が全体の個数を超えない範囲で
ちょうど `k` 個まで含まれる。しきい値未満の値は昇順列の先頭側に集まるためである。
-/
theorem Ascending.countP_take_lt {values : List Nat} (hAscending : Ascending values)
    (k threshold : Nat) :
    (values.take k).countP (fun value => decide (value < threshold)) =
      min k (values.countP (fun value => decide (value < threshold))) := by
  induction k generalizing values with
  | zero => simp
  | succ k ih =>
      cases values with
      | nil => simp
      | cons head tail =>
          have hTail : Ascending tail := by
            cases tail with
            | nil => trivial
            | cons next rest =>
                change head ≤ next ∧ Ascending (next :: rest) at hAscending
                exact hAscending.2
          by_cases hHead : head < threshold
          · have hInd := ih hTail
            simp only [List.take_succ_cons, List.countP_cons,
              decide_eq_true hHead, hInd]
            by_cases hCount : k ≤ tail.countP (fun value => decide (value < threshold))
            · simp [hCount]
            · simp
          · have hTailCount :
                tail.countP (fun value => decide (value < threshold)) = 0 := by
              apply List.countP_eq_zero.mpr
              intro value hValue
              have hPairwise := ascending_pairwise (head :: tail) hAscending
              have hHeadLeValue : head ≤ value :=
                List.rel_of_pairwise_cons hPairwise (by simp [hValue])
              have hNotBelow : ¬ value < threshold := by omega
              simp [hNotBelow]
            have hAppendCount := congrArg
              (List.countP (fun value => decide (value < threshold)))
              (List.take_append_drop k tail)
            rw [List.countP_append, hTailCount] at hAppendCount
            have hPrefixCount :
                (tail.take k).countP (fun value => decide (value < threshold)) = 0 := by
              omega
            simp [List.take, hHead, hPrefixCount, hTailCount]

/-- ソート済み出力の先頭 `k` 個にあるしきい値未満の要素数は、入力中の個数と
`k` の小さい方に一致する。従って先頭 `k` 個は、重複値も含めて入力の最小側を正確に
選んだ部分列である。
-/
theorem Correct.countP_take_lt {input output : List Nat} (hCorrect : Correct input output)
    (k threshold : Nat) :
    (output.take k).countP (fun value => decide (value < threshold)) =
      min k (input.countP (fun value => decide (value < threshold))) := by
  rw [hCorrect.1.countP_take_lt, hCorrect.countP_eq]

/-- 昇順出力の先頭 `k` 個にあるしきい値以下の要素数は、全体の個数と `k` の小さい方。

狭義不等号の定理をしきい値 `threshold + 1` に適用し、自然数上で同値な境界条件へ
書き換える。重複値がしきい値と等しい場合も個数に含む。
-/
theorem Correct.countP_take_le {input output : List Nat} (hCorrect : Correct input output)
    (k threshold : Nat) :
    (output.take k).countP (fun value => decide (value ≤ threshold)) =
      min k (input.countP (fun value => decide (value ≤ threshold))) := by
  simpa [Nat.lt_succ_iff] using hCorrect.countP_take_lt k (threshold + 1)

/-- 先頭 `k` 個にあるしきい値より大きい値の個数は、未充足の `k` 枠と入力個数の小さい方。

昇順列では、しきい値以下の値が先に並ぶ。従って先頭 `k` 個に現れるしきい値超過値は、
しきい値以下の入力要素を数えた後に残る枠だけであり、重複値も正確に数える。
-/
theorem Correct.countP_take_gt {input output : List Nat} (hCorrect : Correct input output)
    (k threshold : Nat) :
    (output.take k).countP (fun value => decide (threshold < value)) =
      min (input.countP (fun value => decide (threshold < value)))
        (k - input.countP (fun value => decide (value ≤ threshold))) := by
  let atMost : Nat → Bool := fun value => decide (value ≤ threshold)
  let greater : Nat → Bool := fun value => decide (threshold < value)
  have hLength := hCorrect.length_eq
  have hPrefixLength : (output.take k).length = min k input.length := by
    simp [hLength]
  have hPrefixAtMost : (output.take k).countP atMost =
      min k (input.countP atMost) := by
    simpa [atMost] using hCorrect.countP_take_le k threshold
  have hPrefixPartition : (output.take k).length =
      (output.take k).countP atMost + (output.take k).countP greater := by
    simpa [atMost, greater, Nat.not_le] using
      (output.take k).length_eq_countP_add_countP atMost
  have hInputPartition : input.length = input.countP atMost + input.countP greater := by
    simpa [atMost, greater, Nat.not_le] using input.length_eq_countP_add_countP atMost
  have hPrefixGreater : (output.take k).countP greater =
      min k input.length - min k (input.countP atMost) := by
    omega
  change (output.take k).countP greater = min (input.countP greater) (k - input.countP atMost)
  omega

/-- 先頭 `k` 個にあるしきい値以上の値の個数も、残る枠と入力個数で正確に決まる。

しきい値が正なら一つ小さいしきい値に対する `countP_take_gt` を使う。しきい値0では
全ての自然数が条件を満たすため、単に先頭部分の長さとなる。
-/
theorem Correct.countP_take_ge {input output : List Nat} (hCorrect : Correct input output)
    (k threshold : Nat) :
    (output.take k).countP (fun value => decide (threshold ≤ value)) =
      min (input.countP (fun value => decide (threshold ≤ value)))
        (k - input.countP (fun value => decide (value < threshold))) := by
  by_cases hZero : threshold = 0
  · subst threshold
    have hLength := hCorrect.length_eq
    simpa [hLength] using (Nat.min_comm k input.length)
  · obtain ⟨previous, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hZero
    simpa [Nat.succ_le_iff, Nat.lt_succ_iff] using
      hCorrect.countP_take_gt k previous

/-- 任意のBoolean分類について、prefixとsuffixの個数の和は入力全体の個数に等しい。

ソートの順序性は使わず、要素保存と `take`・`drop` の分割だけから導く。
任意の分類条件で、prefix と suffix の間にまたがる重複数も正確に保存される。
-/
theorem Correct.countP_take_add_drop_eq {input output : List Nat}
    (hCorrect : Correct input output) (k : Nat) (predicate : Nat → Bool) :
    (output.take k).countP predicate + (output.drop k).countP predicate =
      input.countP predicate := by
  calc
    (output.take k).countP predicate + (output.drop k).countP predicate =
        (output.take k ++ output.drop k).countP predicate := by
          rw [List.countP_append]
    _ = output.countP predicate := by
      exact congrArg (List.countP predicate) (List.take_append_drop k output)
    _ = input.countP predicate := hCorrect.countP_eq predicate

/-- 任意のBoolean分類について、suffixの個数は入力全体からprefixの個数を引いた値。

加法形の分割定理から、自然数上の正確な残数を取り出す。
-/
theorem Correct.countP_drop_eq_sub_take {input output : List Nat}
    (hCorrect : Correct input output) (k : Nat) (predicate : Nat → Bool) :
    (output.drop k).countP predicate =
      input.countP predicate - (output.take k).countP predicate := by
  have hSplit := hCorrect.countP_take_add_drop_eq k predicate
  omega

/-- 正しいソート結果の suffix に残るしきい値以下の値数を、入力全体から求める。

一般のprefix/suffix分割則と、prefix内の個数定理を合成する。
-/
theorem Correct.countP_drop_le {input output : List Nat} (hCorrect : Correct input output)
    (k threshold : Nat) :
    (output.drop k).countP (fun value => decide (value ≤ threshold)) =
      input.countP (fun value => decide (value ≤ threshold)) -
        min k (input.countP (fun value => decide (value ≤ threshold))) := by
  rw [hCorrect.countP_drop_eq_sub_take k (fun value => decide (value ≤ threshold)),
    hCorrect.countP_take_le k threshold]

/-- 正しいソート結果の suffix に残るしきい値未満の値数を、入力全体から求める。

`take` と `drop` による個数分割と、prefix に含まれる値数の一般公式を使う。
これにより `<` の条件も suffix 側で正確に追跡できる。
-/
theorem Correct.countP_drop_lt {input output : List Nat} (hCorrect : Correct input output)
    (k threshold : Nat) :
    (output.drop k).countP (fun value => decide (value < threshold)) =
    input.countP (fun value => decide (value < threshold)) -
        min k (input.countP (fun value => decide (value < threshold))) := by
  rw [hCorrect.countP_drop_eq_sub_take k (fun value => decide (value < threshold)),
    hCorrect.countP_take_lt k threshold]

/-- suffix に残るしきい値超過値数は、入力中の個数から prefix で選ばれた分を引いた値。

先頭部分の超過値数は `countP_take_gt` で決まり、`take` と `drop` の個数分割により
残余部分の超過値数も任意の `k` について定まる。
-/
theorem Correct.countP_drop_gt {input output : List Nat} (hCorrect : Correct input output)
    (k threshold : Nat) :
    (output.drop k).countP (fun value => decide (threshold < value)) =
      input.countP (fun value => decide (threshold < value)) -
        min (input.countP (fun value => decide (threshold < value)))
          (k - input.countP (fun value => decide (value ≤ threshold))) := by
  rw [hCorrect.countP_drop_eq_sub_take k (fun value => decide (threshold < value)),
    hCorrect.countP_take_gt k threshold]

/-- suffix に残るしきい値以上の値数も、入力全体と prefix の個数から一意に決まる。

正のしきい値では一つ小さい値に対する `countP_drop_gt` に帰着する。しきい値0では
全入力値が該当するため、suffix の長さを入力長から prefix 長を引いて求める。
-/
theorem Correct.countP_drop_ge {input output : List Nat} (hCorrect : Correct input output)
    (k threshold : Nat) :
    (output.drop k).countP (fun value => decide (threshold ≤ value)) =
      input.countP (fun value => decide (threshold ≤ value)) -
        min (input.countP (fun value => decide (threshold ≤ value)))
          (k - input.countP (fun value => decide (value < threshold))) := by
  rw [hCorrect.countP_drop_eq_sub_take k (fun value => decide (threshold ≤ value)),
    hCorrect.countP_take_ge k threshold]

/-- 正しいソート結果が狭義昇順であることと、入力に重複がないことは同値である。
順列保存で重複の有無を出力へ移し、昇順性と組み合わせて隣接値を狭義順序へ強める。
-/
theorem Correct.pairwise_lt_iff_input_nodup {input output : List Nat}
    (hCorrect : Correct input output) :
    output.Pairwise (fun left right : Nat => left < right) ↔ input.Nodup := by
  constructor
  · intro hStrict
    exact hCorrect.2.nodup_iff.mp (pairwise_lt_nodup output hStrict)
  · intro hInputNodup
    have hOutputNodup : output.Nodup := hCorrect.2.nodup_iff.mpr hInputNodup
    exact ascending_nodup_pairwise_lt output hCorrect.1 hOutputNodup

/-- 条件で要素を除いても、残ったリストの昇順性は保たれる。 -/
theorem Ascending.filter {values : List Nat} (predicate : Nat → Bool)
    (hAscending : Ascending values) : Ascending (values.filter predicate) :=
  pairwise_ascending _ ((ascending_pairwise values hAscending).filter predicate)

/-- 同じ条件で入力と昇順出力を絞り込んでも、ソート正当性が保たれる。 -/
theorem Correct.filter {input output : List Nat} (predicate : Nat → Bool)
    (hCorrect : Correct input output) :
    Correct (input.filter predicate) (output.filter predicate) := by
  constructor
  · exact Ascending.filter predicate hCorrect.1
  · exact hCorrect.2.filter predicate

/-- 正しいソート結果では、前の添字の値は後の添字の値以下である。

仕様が隣接要素だけに課す昇順性から、推移律を介して任意の二つの位置の順序を得る。
添字が等しい場合も含め、配列やリストを直接走査せずに位置間の大小を利用できる。
-/
theorem Correct.getElem_le {input output : List Nat}
    (hCorrect : Correct input output) {i j : Nat}
    (hi : i < output.length) (hj : j < output.length) (hij : i ≤ j) :
    output[i] ≤ output[j] := by
  rcases Nat.lt_or_eq_of_le hij with hlt | rfl
  · exact List.Pairwise.rel_getElem_of_lt hi hj
      (ascending_pairwise output hCorrect.1) hlt
  · exact Nat.le_refl _

/-- `i` 番目より前にある値は、正しいソート結果の `i` 番目以下である。 -/
theorem Correct.le_getElem_of_mem_take {input output : List Nat}
    (hCorrect : Correct input output) {i : Nat} (hi : i < output.length)
    {value : Nat} (hValue : value ∈ output.take i) :
    value ≤ output[i] := by
  rw [List.mem_take_iff_getElem] at hValue
  obtain ⟨j, hj, hAtJ⟩ := hValue
  have hJltI : j < i := by omega
  have hOrder : output[j] ≤ output[i] :=
    hCorrect.getElem_le (i := j) (j := i) (by omega) hi (by omega)
  simpa [hAtJ] using hOrder

/-- `i` 番目より後にある値は、正しいソート結果の `i` 番目以上である。 -/
theorem Correct.getElem_le_of_mem_drop {input output : List Nat}
    (hCorrect : Correct input output) {i : Nat} (hi : i < output.length)
    {value : Nat} (hValue : value ∈ output.drop (i + 1)) :
    output[i] ≤ value := by
  rw [List.mem_drop_iff_getElem] at hValue
  obtain ⟨j, hj, hAtJ⟩ := hValue
  have hIndex : i + 1 + j < output.length := by omega
  have hOrder : output[i] ≤ output[i + 1 + j] :=
    hCorrect.getElem_le (i := i) (j := i + 1 + j) hi hIndex (by omega)
  simpa [hAtJ] using hOrder

/-- 正しいソート結果の `i` 番目は、入力の `i` 番目の順序統計量である。

その値より小さい入力要素は高々 `i` 個であり、その値以下の入力要素は少なくとも
`i + 1` 個ある。重複値があってもこの上下界は保たれ、値の順位を曖昧なく表す。
-/
theorem Correct.getElem_rank_bounds {input output : List Nat}
    (hCorrect : Correct input output) {i : Nat} (hi : i < output.length) :
    input.countP (fun value => decide (value < output[i])) ≤ i ∧
      i < input.countP (fun value => decide (value ≤ output[i])) := by
  let pivot := output[i]
  change input.countP (fun value => decide (value < pivot)) ≤ i ∧
    i < input.countP (fun value => decide (value ≤ pivot))
  let below : Nat → Bool := fun value => decide (value < pivot)
  let atMost : Nat → Bool := fun value => decide (value ≤ pivot)
  have hPrefixAtMost : ∀ value ∈ output.take i, atMost value = true := by
    intro value hValue
    exact decide_eq_true (hCorrect.le_getElem_of_mem_take hi hValue)
  have hSuffixNotBelow : ∀ value ∈ output.drop (i + 1), below value = false := by
    intro value hValue
    have hBound := hCorrect.getElem_le_of_mem_drop hi hValue
    have hPivotBound : pivot ≤ value := by simpa [pivot] using hBound
    have hNot : ¬ value < pivot := by omega
    simp [below, hNot]
  have hBelowSuffix : (output.drop (i + 1)).countP below = 0 := by
    apply List.countP_eq_zero.mpr
    intro value hValue
    rw [hSuffixNotBelow value hValue]
    decide
  have hPrefixLength : (output.take i).length = i := by
    simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hi)]
  have hDecomp : output = output.take i ++ output[i] :: output.drop (i + 1) := by
    calc
      output = output.take i ++ output.drop i := (List.take_append_drop i output).symm
      _ = output.take i ++ output[i] :: output.drop (i + 1) := by
        rw [List.drop_eq_getElem_cons hi]
  have hBelowPerm := hCorrect.countP_eq below
  have hAtMostPerm := hCorrect.countP_eq atMost
  constructor
  · have hBelowCenter : below output[i] = false := by simp [below, pivot]
    have hBelowOutput : output.countP below = (output.take i).countP below := by
      calc
        output.countP below =
            (output.take i ++ output[i] :: output.drop (i + 1)).countP below :=
          congrArg (List.countP below) hDecomp
        _ = (output.take i).countP below := by
          rw [List.countP_append, List.countP_cons, hBelowCenter, hBelowSuffix]
          simp
    calc
      input.countP below = output.countP below := hBelowPerm.symm
      _ = (output.take i).countP below := hBelowOutput
      _ ≤ i := Nat.le_trans (List.countP_le_length (p := below) (l := output.take i))
        (by omega)
  · have hAtMostCenter : atMost output[i] = true := by simp [atMost, pivot]
    have hPrefixCount : (output.take i).countP atMost = i := by
      rw [List.countP_eq_length.mpr hPrefixAtMost, hPrefixLength]
    have hAtMostOutput : output.countP atMost =
        i + ((output.drop (i + 1)).countP atMost + 1) := by
      calc
        output.countP atMost =
            (output.take i ++ output[i] :: output.drop (i + 1)).countP atMost :=
          congrArg (List.countP atMost) hDecomp
        _ = (output.take i).countP atMost +
            ((output.drop (i + 1)).countP atMost + 1) := by
          rw [List.countP_append, List.countP_cons, hAtMostCenter]
          simp
        _ = i + ((output.drop (i + 1)).countP atMost + 1) := by
          rw [hPrefixCount]
    calc
      i < input.countP atMost := by
        rw [← hAtMostPerm, hAtMostOutput]
        omega

/-- 各要素の真偽値条件が含意で結ばれるとき、前者を満たす要素数は後者以下。 -/
private theorem countP_le_of_implies {α : Type} (values : List α)
    (p q : α → Bool) (hImplies : ∀ value, p value = true → q value = true) :
    values.countP p ≤ values.countP q := by
  induction values with
  | nil => simp
  | cons head tail ih =>
    cases hp : p head with
    | false =>
      rw [List.countP_cons, hp]
      cases hq : q head with
      | false =>
        rw [List.countP_cons, hq]
        exact ih
      | true =>
        rw [List.countP_cons, hq]
        simp
        omega
    | true =>
      have hq : q head = true := hImplies head (by rw [hp])
      rw [List.countP_cons, hp, List.countP_cons, hq]
      omega

/-- 正しいソート結果の `i` 番目の値は、入力の順位条件で特徴付けられる。

値 `v` がその位置に現れることと、入力中で `v` より小さい値が高々 `i` 個あり、
`v` 以下の値が少なくとも `i + 1` 個あることは同値である。重複値がある場合も、
この条件はその値が占める順位の範囲を正確に表す。
-/
theorem Correct.getElem_eq_iff_rank_bounds {input output : List Nat}
    (hCorrect : Correct input output) {i : Nat} (hi : i < output.length) (value : Nat) :
    output[i] = value ↔
      input.countP (fun item => decide (item < value)) ≤ i ∧
        i < input.countP (fun item => decide (item ≤ value)) := by
  constructor
  · intro hValue
    subst value
    exact hCorrect.getElem_rank_bounds hi
  · intro hRanks
    by_cases hEqual : output[i] = value
    · exact hEqual
    · rcases Nat.lt_or_gt_of_ne hEqual with hOutputLt | hValueLt
      · have hCountLe :
          input.countP (fun item => decide (item ≤ output[i])) ≤
            input.countP (fun item => decide (item < value)) := by
          apply countP_le_of_implies
          intro item hAtMost
          have hItem := of_decide_eq_true hAtMost
          exact decide_eq_true (Nat.lt_of_le_of_lt hItem hOutputLt)
        have hActualRank := hCorrect.getElem_rank_bounds hi
        omega
      · have hCountLe :
          input.countP (fun item => decide (item ≤ value)) ≤
            input.countP (fun item => decide (item < output[i])) := by
          apply countP_le_of_implies
          intro item hAtMost
          have hItem := of_decide_eq_true hAtMost
          exact decide_eq_true (Nat.lt_of_le_of_lt hItem hValueLt)
        have hActualRank := hCorrect.getElem_rank_bounds hi
        omega

/-- 同じ入力に対して `Correct` を満たす二つの結果は必ず一致する。 -/
theorem Correct.eq_of_same_input {input output₁ output₂ : List Nat}
    (h₁ : Correct input output₁) (h₂ : Correct input output₂) : output₁ = output₂ := by
  apply List.Perm.eq_of_pairwise (le := fun a b : Nat => a ≤ b)
  · intro a b _ _ hab hba
    exact Nat.le_antisymm hab hba
  · exact ascending_pairwise output₁ h₁.1
  · exact ascending_pairwise output₂ h₂.1
  · exact h₁.2.trans h₂.2.symm

/-- 共通仕様を満たす任意のソート関数は、Boolean 条件による絞り込みと可換である。

入力を絞ってソートした結果と、ソート後の出力を同じ条件で絞った結果は、どちらも
絞り込み後の入力に対する `Correct` を満たす。一意性から両者が一致する。
-/
theorem Correct.sort_filter (sort : List Nat → List Nat)
    (hSort : ∀ values, Correct values (sort values))
    (values : List Nat) (predicate : Nat → Bool) :
    sort (values.filter predicate) = (sort values).filter predicate := by
  exact Correct.eq_of_same_input (hSort (values.filter predicate))
    (Correct.filter predicate (hSort values))

/-- 共通仕様を満たす任意のソート関数は、非減少関数による写像と可換である。

写像後の入力に対するソートと、ソート結果を写像した列は、ともに同じ入力に対する
`Correct` を満たす。写像が非減少なので昇順性を保ち、順列写像で要素保存も従う。
-/
theorem Correct.sort_map (sort : List Nat → List Nat)
    (hSort : ∀ values, Correct values (sort values))
    (values : List Nat) (f : Nat → Nat)
    (hMonotone : ∀ ⦃a b⦄, a ≤ b → f a ≤ f b) :
    sort (values.map f) = (sort values).map f := by
  exact Correct.eq_of_same_input (hSort (values.map f))
    (Correct.map f hMonotone (hSort values))

/-- 順列関係にある入力を正しくソートした結果は、入力順によらず一致する。 -/
theorem Correct.eq_of_perm_inputs {input₁ input₂ output₁ output₂ : List Nat}
    (h₁ : Correct input₁ output₁) (h₂ : Correct input₂ output₂)
    (hInputs : input₁.Perm input₂) : output₁ = output₂ := by
  apply List.Perm.eq_of_pairwise (le := fun a b : Nat => a ≤ b)
  · intro a b _ _ hab hba
    exact Nat.le_antisymm hab hba
  · exact ascending_pairwise output₁ h₁.1
  · exact ascending_pairwise output₂ h₂.1
  · exact h₁.2.trans (hInputs.trans h₂.2.symm)

/-- 共通仕様を満たすソート関数の結果は、順列関係にある入力上で一致する。 -/
theorem Correct.sort_eq_of_perm_inputs (sort : List Nat → List Nat)
    (hSort : ∀ values, Correct values (sort values))
    {input₁ input₂ : List Nat} (hInputs : input₁.Perm input₂) :
    sort input₁ = sort input₂ :=
  Correct.eq_of_perm_inputs (hSort input₁) (hSort input₂) hInputs

/-- 共通仕様を満たすソート関数は、既に昇順の入力を変更しない。 -/
theorem Correct.sort_eq_self_of_ascending (sort : List Nat → List Nat)
    (hSort : ∀ values, Correct values (sort values))
    (values : List Nat) (hAscending : Ascending values) :
    sort values = values :=
  Correct.eq_of_same_input (hSort values) ⟨hAscending, List.Perm.refl values⟩

/-- 共通仕様を満たすソート関数を二度適用しても結果は変わらない。 -/
theorem Correct.sort_idempotent (sort : List Nat → List Nat)
    (hSort : ∀ values, Correct values (sort values)) (values : List Nat) :
    sort (sort values) = sort values := by
  have hSorted := hSort values
  exact Correct.sort_eq_self_of_ascending sort hSort (sort values) hSorted.1

/-- 正しいソート結果が一致することと、入力が順列関係にあることは同値である。 -/
theorem Correct.perm_iff_eq_output {input₁ input₂ output₁ output₂ : List Nat}
    (h₁ : Correct input₁ output₁) (h₂ : Correct input₂ output₂) :
    input₁.Perm input₂ ↔ output₁ = output₂ := by
  constructor
  · exact Correct.eq_of_perm_inputs h₁ h₂
  · intro hOutputs
    exact h₁.2.symm.trans ((List.Perm.of_eq hOutputs).trans h₂.2)

/-- 正しい非空なソート結果の先頭は、入力に含まれる最小値である。 -/
theorem Correct.head_is_minimum {input output : List Nat}
    (hCorrect : Correct input output) (hOutput : output ≠ []) :
    ∃ minimum rest, output = minimum :: rest ∧ minimum ∈ input ∧
      ∀ value ∈ input, minimum ≤ value := by
  cases output with
  | nil => contradiction
  | cons minimum rest =>
      refine ⟨minimum, rest, rfl, ?_, ?_⟩
      · exact hCorrect.2.mem_iff.mp (by simp)
      · intro value hValue
        have hInOutput : value ∈ minimum :: rest := hCorrect.2.mem_iff.mpr hValue
        simp only [List.mem_cons] at hInOutput
        rcases hInOutput with rfl | hInRest
        · exact Nat.le_refl _
        · exact List.rel_of_pairwise_cons (ascending_pairwise _ hCorrect.1) hInRest

/-- 非空入力を正しくソートした結果は、入力の最小値を含む。 -/
theorem Correct.exists_minimum {input output : List Nat}
    (hCorrect : Correct input output) (hInput : input ≠ []) :
    ∃ minimum, minimum ∈ input ∧ ∀ value ∈ input, minimum ≤ value := by
  have hOutput : output ≠ [] := by
    intro hEmpty
    have hLength := hCorrect.2.length_eq
    rw [hEmpty] at hLength
    cases input with
    | nil => exact hInput rfl
    | cons first rest => simp at hLength
  obtain ⟨minimum, _, _, hMinimumMem, hLowerBound⟩ :=
    Correct.head_is_minimum hCorrect hOutput
  exact ⟨minimum, hMinimumMem, hLowerBound⟩

/-- Pairwise 昇順な非空リストの最後の要素は、全要素以上である。 -/
theorem pairwise_last_is_maximum : ∀ values : List Nat,
    values.Pairwise (fun a b : Nat => a ≤ b) → values ≠ [] →
    ∃ initSegment maximum, values = initSegment ++ [maximum] ∧ maximum ∈ values ∧
      ∀ value ∈ values, value ≤ maximum := by
  intro values
  induction values with
  | nil =>
      intro _ hNonempty
      contradiction
  | cons first rest ih =>
      cases rest with
      | nil =>
          intro _ _
          exact ⟨[], first, by simp, by simp,
            by intro value hValue; simp at hValue; omega⟩
      | cons second tail =>
          intro hSorted _
          obtain ⟨initSegment, maximum, hTailEq, hMaximumMem, hMaximumBound⟩ :=
            ih hSorted.tail (by simp)
          have hFirstSecond : first ≤ second :=
            List.rel_of_pairwise_cons hSorted (by simp)
          have hSecondMaximum : second ≤ maximum := hMaximumBound second (by simp)
          refine ⟨first :: initSegment, maximum, ?_, by simp [hTailEq], ?_⟩
          · calc
              first :: (second :: tail) = first :: (initSegment ++ [maximum]) := by rw [hTailEq]
              _ = (first :: initSegment) ++ [maximum] := by simp
          intro value hValue
          simp only [List.mem_cons] at hValue
          rcases hValue with rfl | hValue
          · exact Nat.le_trans hFirstSecond hSecondMaximum
          · have hValue' : value = second ∨ value ∈ tail := by simpa using hValue
            rcases hValue' with rfl | hValueTail
            · exact hSecondMaximum
            · exact hMaximumBound value (by simp [hValueTail])

/-- 正しくソートした非空入力では、出力の最後の要素が入力の最大値である。 -/
theorem Correct.last_is_maximum {input output : List Nat}
    (hCorrect : Correct input output) (hInput : input ≠ []) :
    ∃ initSegment maximum, output = initSegment ++ [maximum] ∧ maximum ∈ input ∧
      ∀ value ∈ input, value ≤ maximum := by
  have hOutput : output ≠ [] := by
    intro hEmpty
    have hLength := hCorrect.2.length_eq
    rw [hEmpty] at hLength
    cases input with
    | nil => exact hInput rfl
    | cons first rest => simp at hLength
  obtain ⟨initSegment, maximum, hLast, hMaximumMem, hMaximumBound⟩ :=
    pairwise_last_is_maximum output (ascending_pairwise output hCorrect.1) hOutput
  refine ⟨initSegment, maximum, hLast, hCorrect.2.mem_iff.mp hMaximumMem, ?_⟩
  intro value hValue
  exact hMaximumBound value (hCorrect.2.mem_iff.mpr hValue)

/-- 正しくソートした非空入力には、入力の最大値が含まれる。 -/
theorem Correct.exists_maximum {input output : List Nat}
    (hCorrect : Correct input output) (hInput : input ≠ []) :
    ∃ maximum, maximum ∈ input ∧ ∀ value ∈ input, value ≤ maximum := by
  obtain ⟨_, maximum, _, hMaximumMem, hMaximumBound⟩ :=
    Correct.last_is_maximum hCorrect hInput
  exact ⟨maximum, hMaximumMem, hMaximumBound⟩

/-- 指定した値集合から、長さ `n` のリストを全て列挙する。 -/
def listsOfLengthOver (alphabet : List Nat) : Nat → List (List Nat)
  | 0 => [[]]
  | size + 1 =>
    (listsOfLengthOver alphabet size).flatMap fun prior =>
      alphabet.map fun value => prior ++ [value]

/-- 長さ `n` のリストを、各要素 `0`, `1`, `2` から選んで全て列挙する。 -/
def listsOfLength : Nat → List (List Nat) := listsOfLengthOver [0, 1, 2]

/-- 長さ 0〜5、各要素 0〜2 の全 364 リスト。 -/
def boundedInputs : List (List Nat) :=
  (List.range 6).flatMap listsOfLength

/-- 長さ 0〜8、各要素 0〜3 の全 87,381 リスト。 -/
def stressInputs : List (List Nat) :=
  (List.range 9).flatMap (listsOfLengthOver [0, 1, 2, 3])

/-- 小さい値と大きな境界値を混ぜた、長さ0〜7の全97,656入力。 -/
def wideValueInputs : List (List Nat) :=
  (List.range 8).flatMap
    (listsOfLengthOver [0, 1, 2, 4294967296, 18446744073709551615])

/-- 長さ64およびヒープ階層境界付近の整列済み・逆順・同値・周期的な偏り入力。 -/
def adversarialInputs : List (List Nat) :=
  [ List.range 64
  , (List.range 64).reverse
  , List.replicate 64 7
  , (List.range 64).map fun value => value % 5
  ] ++ [63, 65, 127, 128, 129, 255, 256, 257, 511, 512, 513].flatMap fun length =>
    [ List.range length
    , (List.range length).reverse
    , List.replicate length 7
    , (List.range length).map fun value => value % 5
    ]

/-- 12種類の境界長に4種類の64ビット値パターンを適用した全48入力。 -/
def wideAdversarialInputs : List (List Nat) :=
  let max64 := 18446744073709551615
  [63, 64, 65, 127, 128, 129, 255, 256, 257, 511, 512, 513].flatMap fun length =>
    [ (List.range length).map (fun index => if index % 2 = 0 then max64 else 0)
    , (List.range length).map (fun index =>
        match index % 4 with
        | 0 => max64
        | 1 => 4294967296
        | 2 => 1
        | _ => 0)
    , (List.range length).map (fun index => max64 - index)
    , List.replicate length max64
    ]

/-- 1024 要素付近で、順序・同値・周期性に偏りのある長い入力を作る。 -/
def largeAdversarialInputs : List (List Nat) :=
  [1023, 1024, 1025].flatMap fun length =>
    [ List.range length
    , (List.range length).reverse
    , List.replicate length 7
    , (List.range length).map fun index => index % 11
    ]

/-- 1023〜1025要素で64ビット境界値を混ぜた12種類の大きな入力を作る。 -/
def largeWideAdversarialInputs : List (List Nat) :=
  let max64 := 18446744073709551615
  [1023, 1024, 1025].flatMap fun length =>
    [ (List.range length).map (fun index => if index % 2 = 0 then max64 else 0)
    , (List.range length).map (fun index =>
        match index % 4 with
        | 0 => max64
        | 1 => 4294967296
        | 2 => 1
        | _ => 0)
    , (List.range length).map (fun index => max64 - index)
    , List.replicate length max64
    ]

end LeanExperiments.Verification.Sorting.Spec
