import LeanExperiments.Verification.HeapSort.Core

/-! Finite regression checks and concrete examples for heap sort. -/

open Std.WP Lean.Order
set_option maxHeartbeats 200000

namespace LeanExperiments.Verification.HeapSort.Spec

/-! 以下はカーネルが計算結果を確認する具体例である。
任意の配列に対する `Correct input (heapSort input)` の証明とは区別する。 -/

/-- 空配列をソートすると、空配列のままで仕様を満たす。 -/
theorem heapSort_empty_boundary_correct :
    Correct (#[] : Array Nat) (LeanExperiments.HeapSort.heapSort #[]) := by
  have hSort : LeanExperiments.HeapSort.heapSort (#[] : Array Nat) = #[] := by
    native_decide
  rw [hSort]
  constructor
  · simp [LeanExperiments.Verification.Sorting.Spec.Ascending]
  · exact List.Perm.refl []

/-- 重複値を含む例で、出力の順序と要素保存をまとめて確認する。 -/
theorem heapSort_example_correct :
    Correct #[7, 2, 5, 2, 0, 9]
      (LeanExperiments.HeapSort.heapSort #[7, 2, 5, 2, 0, 9]) := by
  have hSort :
      LeanExperiments.HeapSort.heapSort #[7, 2, 5, 2, 0, 9] = #[0, 2, 2, 5, 7, 9] := by
    native_decide
  rw [hSort]
  constructor
  · simp [LeanExperiments.Verification.Sorting.Spec.Ascending]
  · apply List.isPerm_iff.mp
    native_decide

/-- 再帰版も重複値を保って昇順に並べ替える。 -/
theorem heapSortRecursive_example_correct :
    Correct #[7, 2, 5, 2, 0, 9]
      (LeanExperiments.HeapSort.heapSortRecursive #[7, 2, 5, 2, 0, 9]) := by
  have hSort :
      LeanExperiments.HeapSort.heapSortRecursive #[7, 2, 5, 2, 0, 9] = #[0, 2, 2, 5, 7, 9] := by
    native_decide
  rw [hSort]
  constructor
  · simp [LeanExperiments.Verification.Sorting.Spec.Ascending]
  · apply List.isPerm_iff.mp
    native_decide

/-! ## 有限領域の網羅確認

以下では値を `0, 1, 2` に限り、長さ 0 から 4 までの配列をすべて列挙する。
合計 1 + 3 + 9 + 27 + 81 = 121 配列について、実装結果が `Correct` を満たす
ことを計算で確認する。これはこの有限領域に対する網羅確認であり、値や長さを
制限しない一般的な正しさの証明ではない。 -/

/-- 指定した値集合から、長さ `size` の配列を全て列挙する。 -/
def arraysOfLengthOver (alphabet : List Nat) : Nat → List (Array Nat)
  | 0 => [#[]]
  | size + 1 =>
    (arraysOfLengthOver alphabet size).flatMap fun prior =>
      alphabet.map fun value => prior.push value

/-- 各長さについて、要素を `0`, `1`, `2` から選んだ全配列を生成する。 -/
def arraysOfLength : Nat → List (Array Nat) := arraysOfLengthOver [0, 1, 2]

/-- 長さ 0〜4、各要素 0〜2 の全配列（121 個）。 -/
def boundedInputs : List (Array Nat) :=
  (List.range 5).flatMap arraysOfLength

/-- 列挙した全配列に対する `Correct` 判定が成功する。 -/
def boundedInputsCheck : Bool :=
  boundedInputs.all fun input =>
    correctCheck input (LeanExperiments.HeapSort.heapSort input)

/-- 同じ有限領域を再帰版 heap sort に対しても調べる。 -/
def boundedInputsRecursiveCheck : Bool :=
  boundedInputs.all fun input =>
    correctCheck input (LeanExperiments.HeapSort.heapSortRecursive input)

/-- 121 通りの入力をすべて実行し、昇順性と要素保存の両方を確認する。 -/
theorem boundedInputsCheck_passes : boundedInputsCheck = true := by
  native_decide

/-- 再帰版についても 121 通りすべてで昇順性と要素保存を確認する。 -/
theorem boundedInputsRecursiveCheck_passes : boundedInputsRecursiveCheck = true := by
  native_decide

/-- ヒープ構築段階が、有限基本領域の全入力で最大ヒープ条件を満たす。 -/
def boundedBuildMaxHeapCheck : Bool :=
  boundedInputs.all fun input =>
    maxHeapCheck (LeanExperiments.HeapSort.buildMaxHeap input)

/-- 再帰版のヒープ構築段階についても最大ヒープ条件を検査する。 -/
def boundedBuildMaxHeapRecursiveCheck : Bool :=
  boundedInputs.all fun input =>
    maxHeapCheck (LeanExperiments.HeapSort.buildMaxHeapRecursive input)

/-- 121入力全てでループ版のヒープ構築結果が最大ヒープになる。 -/
theorem boundedBuildMaxHeapCheck_passes : boundedBuildMaxHeapCheck = true := by
  native_decide

/-- 121入力全てで再帰版のヒープ構築結果も最大ヒープになる。 -/
theorem boundedBuildMaxHeapRecursiveCheck_passes :
    boundedBuildMaxHeapRecursiveCheck = true := by
  native_decide

/-- 有限基本領域の入力ごとに、ループ版が作るヒープ不変条件を取り出せる。 -/
theorem buildMaxHeap_maxHeap_for_boundedInput (input : Array Nat)
    (hInput : input ∈ boundedInputs) :
    MaxHeap (LeanExperiments.HeapSort.buildMaxHeap input) := by
  have hAll : ∀ candidate ∈ boundedInputs,
      maxHeapCheck (LeanExperiments.HeapSort.buildMaxHeap candidate) = true :=
    List.all_eq_true.mp boundedBuildMaxHeapCheck_passes
  exact (maxHeapCheck_correct _).mp (hAll input hInput)

/-- 有限基本領域の入力ごとに、再帰版のヒープ不変条件も取り出せる。 -/
theorem buildMaxHeapRecursive_maxHeap_for_boundedInput (input : Array Nat)
    (hInput : input ∈ boundedInputs) :
    MaxHeap (LeanExperiments.HeapSort.buildMaxHeapRecursive input) := by
  have hAll : ∀ candidate ∈ boundedInputs,
      maxHeapCheck (LeanExperiments.HeapSort.buildMaxHeapRecursive candidate) = true :=
    List.all_eq_true.mp boundedBuildMaxHeapRecursiveCheck_passes
  exact (maxHeapCheck_correct _).mp (hAll input hInput)

/-- 有限領域に列挙した入力それぞれについて `Correct` を取り出せる。 -/
theorem heapSort_correct_for_boundedInput (input : Array Nat)
    (hInput : input ∈ boundedInputs) :
    Correct input (LeanExperiments.HeapSort.heapSort input) := by
  have hAll : ∀ candidate ∈ boundedInputs,
      correctCheck candidate (LeanExperiments.HeapSort.heapSort candidate) = true :=
    List.all_eq_true.mp boundedInputsCheck_passes
  exact correctCheck_sound input _ (hAll input hInput)

/-- 有限領域に列挙した入力それぞれについて再帰版の `Correct` を取り出せる。 -/
theorem heapSortRecursive_correct_for_boundedInput (input : Array Nat)
    (hInput : input ∈ boundedInputs) :
    Correct input (LeanExperiments.HeapSort.heapSortRecursive input) := by
  have hAll : ∀ candidate ∈ boundedInputs,
      correctCheck candidate (LeanExperiments.HeapSort.heapSortRecursive candidate) = true :=
    List.all_eq_true.mp boundedInputsRecursiveCheck_passes
  exact correctCheck_sound input _ (hAll input hInput)

/-! ## 拡張有限領域の確認

値を 0〜3、長さを 0〜8 に広げた全 87,381 配列について両実装を調べる。
それぞれ仕様を満たすことに加えて、再帰版とループ版の結果が一致することも確認する。
-/

/-- 長さ 0〜8、各要素 0〜3 の全 87,381 配列。 -/
def stressInputs : List (Array Nat) :=
  (List.range 9).flatMap (arraysOfLengthOver [0, 1, 2, 3])

/-- 全入力配列について、配列内と直後の全根位置で両 `siftDown` の一致を検査する。 -/
def siftDownAgreementAtAllRootsCheck (input : Array Nat) : Bool :=
  (List.range (input.size + 1)).all fun root =>
    decide (LeanExperiments.HeapSort.siftDown input root =
      LeanExperiments.HeapSort.siftDownRecursive input root)

/-- 拡張有限領域の全配列と全根位置で、二つの下降処理を直接比較する。 -/
def siftDownAgreementStressCheck : Bool :=
  stressInputs.all siftDownAgreementAtAllRootsCheck

/-- 各入力・根位置で両 `siftDown` 出力が入力の順列であることを調べる。 -/
def siftDownPreservesAtAllRootsCheck (input : Array Nat) : Bool :=
  (List.range (input.size + 1)).all fun root =>
    let loopResult := LeanExperiments.HeapSort.siftDown input root
    let recursiveResult := LeanExperiments.HeapSort.siftDownRecursive input root
    loopResult.toList.isPerm input.toList &&
      recursiveResult.toList.isPerm input.toList

/-- 拡張有限領域の全配列・根位置で、両下降処理の要素保存を検査する。 -/
def siftDownPreservesStressCheck : Bool :=
  stressInputs.all siftDownPreservesAtAllRootsCheck

/-- 拡張有限領域の全配列で、両ヒープ構築版が最大ヒープを生成するか確認する。 -/
def heapBuildersStressCheck : Bool :=
  stressInputs.all fun input =>
    heapBuildCheck input (LeanExperiments.HeapSort.buildMaxHeap input) &&
      heapBuildCheck input (LeanExperiments.HeapSort.buildMaxHeapRecursive input)

/-- 両ヒープ構築版と、両構築結果に対する二つの `popMax` の戻り値を比較する。 -/
def heapPrimitiveAgreementStressCheck : Bool :=
  stressInputs.all fun input =>
    let loopHeap := LeanExperiments.HeapSort.buildMaxHeap input
    let recursiveHeap := LeanExperiments.HeapSort.buildMaxHeapRecursive input
    decide (loopHeap = recursiveHeap) &&
      (decide (LeanExperiments.HeapSort.popMax input =
          LeanExperiments.HeapSort.popMaxRecursive input) &&
        (decide (LeanExperiments.HeapSort.popMax loopHeap =
            LeanExperiments.HeapSort.popMaxRecursive loopHeap) &&
          decide (LeanExperiments.HeapSort.popMax recursiveHeap =
            LeanExperiments.HeapSort.popMaxRecursive recursiveHeap)))

/-- 取り出し後の残余仕様を、両ヒープ構築版と拡張有限領域で調べる。 -/
def popMaxRestBuildersStressCheck : Bool :=
  stressInputs.all fun input =>
    (popMaxRestCheck (LeanExperiments.HeapSort.buildMaxHeap input) &&
      popMaxRecursiveRestCheck (LeanExperiments.HeapSort.buildMaxHeap input)) &&
      (popMaxRestCheck (LeanExperiments.HeapSort.buildMaxHeapRecursive input) &&
        popMaxRecursiveRestCheck (LeanExperiments.HeapSort.buildMaxHeapRecursive input))

/-- 拡張有限領域でループ版の昇順性と要素保存を確認する。 -/
def heapSortStressCheck : Bool :=
  stressInputs.all fun input =>
    correctCheck input (LeanExperiments.HeapSort.heapSort input)

/-- 拡張有限領域で再帰版の昇順性と要素保存を確認する。 -/
def heapSortRecursiveStressCheck : Bool :=
  stressInputs.all fun input =>
    correctCheck input (LeanExperiments.HeapSort.heapSortRecursive input)

/-- 拡張有限領域で再帰版とループ版の結果が一致することを確認する。 -/
def heapSortAgreementStressCheck : Bool :=
  stressInputs.all fun input =>
    decide (LeanExperiments.HeapSort.heapSort input =
      LeanExperiments.HeapSort.heapSortRecursive input)

/-- 87,381 配列全てでループ版が仕様を満たす。 -/
theorem heapSortStressCheck_passes : heapSortStressCheck = true := by
  native_decide

/-- 87,381 配列全てでループ版・再帰版のヒープ構築結果が最大ヒープになる。 -/
theorem heapBuildersStressCheck_passes : heapBuildersStressCheck = true := by
  native_decide

/-- 87,381入力全てでヒープ構築結果と両抽出版の戻り値が一致する。 -/
theorem heapPrimitiveAgreementStressCheck_passes :
    heapPrimitiveAgreementStressCheck = true := by
  native_decide

/-- 87,381 入力の各配列で、全ての根位置において両 `siftDown` の結果が一致する。 -/
theorem siftDownAgreementStressCheck_passes :
    siftDownAgreementStressCheck = true := by
  native_decide

/-- 87,381 入力の全根位置で、両 `siftDown` が入力要素を重複込みで保存する。 -/
theorem siftDownPreservesStressCheck_passes :
    siftDownPreservesStressCheck = true := by
  native_decide

/-- 87,381 入力全てで、両構築版と両 `popMax` 版の残余仕様が成り立つ。 -/
theorem popMaxRestBuildersStressCheck_passes :
    popMaxRestBuildersStressCheck = true := by
  native_decide

/-- 拡張有限領域に含まれる入力ごとに、ループ版のヒープ不変条件を取り出せる。 -/
theorem buildMaxHeap_maxHeap_for_stressInput (input : Array Nat)
    (hInput : input ∈ stressInputs) :
    MaxHeap (LeanExperiments.HeapSort.buildMaxHeap input) := by
  have hAll := List.all_eq_true.mp heapBuildersStressCheck_passes input hInput
  rw [Bool.and_eq_true] at hAll
  exact (heapBuildCheck_correct _ _).mp hAll.1 |>.1

/-- 拡張有限領域に含まれる入力ごとに、再帰版のヒープ不変条件も取り出せる。 -/
theorem buildMaxHeapRecursive_maxHeap_for_stressInput (input : Array Nat)
    (hInput : input ∈ stressInputs) :
    MaxHeap (LeanExperiments.HeapSort.buildMaxHeapRecursive input) := by
  have hAll := List.all_eq_true.mp heapBuildersStressCheck_passes input hInput
  rw [Bool.and_eq_true] at hAll
  exact (heapBuildCheck_correct _ _).mp hAll.2 |>.1

/-- 拡張有限領域でループ版のヒープ構築が入力要素を重複込みで保存する。 -/
theorem buildMaxHeap_perm_for_stressInput (input : Array Nat)
    (hInput : input ∈ stressInputs) :
    (LeanExperiments.HeapSort.buildMaxHeap input).toList.Perm input.toList := by
  have hAll := List.all_eq_true.mp heapBuildersStressCheck_passes input hInput
  rw [Bool.and_eq_true] at hAll
  exact (heapBuildCheck_correct _ _).mp hAll.1 |>.2

/-- 拡張有限領域で再帰版のヒープ構築も入力要素を重複込みで保存する。 -/
theorem buildMaxHeapRecursive_perm_for_stressInput (input : Array Nat)
    (hInput : input ∈ stressInputs) :
    (LeanExperiments.HeapSort.buildMaxHeapRecursive input).toList.Perm input.toList := by
  have hAll := List.all_eq_true.mp heapBuildersStressCheck_passes input hInput
  rw [Bool.and_eq_true] at hAll
  exact (heapBuildCheck_correct _ _).mp hAll.2 |>.2

/-- 有限領域の各入力でヒープ構築版と両 `popMax` の結果一致を取り出す。 -/
theorem heapPrimitiveAgreement_for_stressInput (input : Array Nat)
    (hInput : input ∈ stressInputs) :
    LeanExperiments.HeapSort.buildMaxHeap input =
        LeanExperiments.HeapSort.buildMaxHeapRecursive input ∧
      LeanExperiments.HeapSort.popMax input =
        LeanExperiments.HeapSort.popMaxRecursive input ∧
      LeanExperiments.HeapSort.popMax (LeanExperiments.HeapSort.buildMaxHeap input) =
        LeanExperiments.HeapSort.popMaxRecursive
          (LeanExperiments.HeapSort.buildMaxHeap input) ∧
      LeanExperiments.HeapSort.popMax
          (LeanExperiments.HeapSort.buildMaxHeapRecursive input) =
        LeanExperiments.HeapSort.popMaxRecursive
          (LeanExperiments.HeapSort.buildMaxHeapRecursive input) := by
  have hAllInputs := List.all_eq_true.mp heapPrimitiveAgreementStressCheck_passes
  have hChecks := hAllInputs input hInput
  rw [Bool.and_eq_true] at hChecks
  have hFurtherChecks := hChecks.2
  rw [Bool.and_eq_true] at hFurtherChecks
  have hHeapPopChecks := hFurtherChecks.2
  rw [Bool.and_eq_true] at hHeapPopChecks
  exact ⟨of_decide_eq_true hChecks.1, of_decide_eq_true hFurtherChecks.1,
    of_decide_eq_true hHeapPopChecks.1, of_decide_eq_true hHeapPopChecks.2⟩

/-- 有限領域の各配列で、配列内と末尾直後の根位置全てについて下降結果が一致する。 -/
theorem siftDown_eq_siftDownRecursive_for_stressInput (input : Array Nat)
    (hInput : input ∈ stressInputs) :
    ∀ root, root ≤ input.size →
      LeanExperiments.HeapSort.siftDown input root =
        LeanExperiments.HeapSort.siftDownRecursive input root := by
  have hAllInputs := List.all_eq_true.mp siftDownAgreementStressCheck_passes
  have hAllRoots := hAllInputs input hInput
  intro root hRoot
  apply of_decide_eq_true
  exact (List.all_eq_true.mp hAllRoots) root
    (List.mem_range.mpr (by omega))

/-- 有限領域の各配列・根位置で、ループ版と再帰版の下降処理が要素を保存する。 -/
theorem siftDown_perm_for_stressInput (input : Array Nat)
    (hInput : input ∈ stressInputs) :
    ∀ root, root ≤ input.size →
      (LeanExperiments.HeapSort.siftDown input root).toList.Perm input.toList ∧
        (LeanExperiments.HeapSort.siftDownRecursive input root).toList.Perm
          input.toList := by
  have hAllInputs := List.all_eq_true.mp siftDownPreservesStressCheck_passes
  have hAllRoots := hAllInputs input hInput
  intro root hRoot
  have hChecks := (List.all_eq_true.mp hAllRoots) root
    (List.mem_range.mpr (by omega))
  rw [Bool.and_eq_true] at hChecks
  exact ⟨List.isPerm_iff.mp hChecks.1, List.isPerm_iff.mp hChecks.2⟩

/-- 有限領域の各入力から、ループ版の最大値取り出し後の残余仕様を導く。 -/
theorem popMaxRest_buildMaxHeap_for_stressInput (input : Array Nat)
    (hInput : input ∈ stressInputs) :
    PopMaxRestCorrect (LeanExperiments.HeapSort.buildMaxHeap input) := by
  have hAll := List.all_eq_true.mp popMaxRestBuildersStressCheck_passes input hInput
  rw [Bool.and_eq_true] at hAll
  have hLoopBuilder := hAll.1
  rw [Bool.and_eq_true] at hLoopBuilder
  exact (popMaxRestCheck_correct _).mp hLoopBuilder.1

/-- 有限領域の各入力から、再帰版の最大値取り出し後の残余仕様を導く。 -/
theorem popMaxRest_buildMaxHeapRecursive_for_stressInput (input : Array Nat)
    (hInput : input ∈ stressInputs) :
    PopMaxRestCorrect (LeanExperiments.HeapSort.buildMaxHeapRecursive input) := by
  have hAll := List.all_eq_true.mp popMaxRestBuildersStressCheck_passes input hInput
  rw [Bool.and_eq_true] at hAll
  have hRecursiveBuilder := hAll.2
  rw [Bool.and_eq_true] at hRecursiveBuilder
  exact (popMaxRestCheck_correct _).mp hRecursiveBuilder.1

/-- 有限領域の各入力から、再帰版 `popMax` の残余仕様を導く。 -/
theorem popMaxRecursiveRest_buildMaxHeap_for_stressInput (input : Array Nat)
    (hInput : input ∈ stressInputs) :
    PopMaxRecursiveRestCorrect (LeanExperiments.HeapSort.buildMaxHeap input) := by
  have hAll := List.all_eq_true.mp popMaxRestBuildersStressCheck_passes input hInput
  rw [Bool.and_eq_true] at hAll
  have hLoopBuilder := hAll.1
  rw [Bool.and_eq_true] at hLoopBuilder
  exact (popMaxRecursiveRestCheck_correct _).mp hLoopBuilder.2

/-- 有限領域の各入力から、再帰版構築・再帰版取り出し後の残余仕様を導く。 -/
theorem popMaxRecursiveRest_buildMaxHeapRecursive_for_stressInput
    (input : Array Nat) (hInput : input ∈ stressInputs) :
    PopMaxRecursiveRestCorrect
      (LeanExperiments.HeapSort.buildMaxHeapRecursive input) := by
  have hAll := List.all_eq_true.mp popMaxRestBuildersStressCheck_passes input hInput
  rw [Bool.and_eq_true] at hAll
  have hRecursiveBuilder := hAll.2
  rw [Bool.and_eq_true] at hRecursiveBuilder
  exact (popMaxRecursiveRestCheck_correct _).mp hRecursiveBuilder.2

/-- 87,381 配列全てで再帰版が仕様を満たす。 -/
theorem heapSortRecursiveStressCheck_passes : heapSortRecursiveStressCheck = true := by
  native_decide

/-- 87,381 配列全てで両実装の結果が一致する。 -/
theorem heapSortAgreementStressCheck_passes : heapSortAgreementStressCheck = true := by
  native_decide

/-! ## 大きな値を含む全列挙確認

小さい値だけでは見つけにくい、比較対象の桁が大きく異なる場合や最大64 bit値の
重複を含め、長さ0〜7の97,656配列を両実装で確認する。 -/

/-- 5種類の値から作る長さ0〜7の全97,656配列。 -/
def wideValueInputs : List (Array Nat) :=
  (LeanExperiments.Verification.Sorting.Spec.wideValueInputs).map List.toArray

/-- 大きな値を含む全入力で、両ヒープ構築版のヒープ条件と要素保存を調べる。 -/
def heapBuildersWideValueCheck : Bool :=
  wideValueInputs.all fun input =>
    heapBuildCheck input (LeanExperiments.HeapSort.buildMaxHeap input) &&
      heapBuildCheck input (LeanExperiments.HeapSort.buildMaxHeapRecursive input)

/-- 97,656入力全てで両ヒープ構築版が仕様を満たす。 -/
theorem heapBuildersWideValueCheck_passes : heapBuildersWideValueCheck = true := by
  native_decide

/-- 広値有限領域の各入力で、両ヒープ構築版の論理仕様を取り出せる。 -/
theorem heapBuildCorrect_for_wideValueInput (input : Array Nat)
    (hInput : input ∈ wideValueInputs) :
    HeapBuildCorrect input (LeanExperiments.HeapSort.buildMaxHeap input) ∧
      HeapBuildCorrect input (LeanExperiments.HeapSort.buildMaxHeapRecursive input) := by
  have hChecks := (List.all_eq_true.mp heapBuildersWideValueCheck_passes) input hInput
  rw [Bool.and_eq_true] at hChecks
  exact ⟨(heapBuildCheck_correct _ _).mp hChecks.1,
    (heapBuildCheck_correct _ _).mp hChecks.2⟩

/-- 大きな値を含む入力でも、両ヒープ構築版と両 `popMax` 版の残余仕様を調べる。 -/
def popMaxRestBuildersWideValueCheck : Bool :=
  wideValueInputs.all fun input =>
    (popMaxRestCheck (LeanExperiments.HeapSort.buildMaxHeap input) &&
      popMaxRecursiveRestCheck (LeanExperiments.HeapSort.buildMaxHeap input)) &&
      (popMaxRestCheck (LeanExperiments.HeapSort.buildMaxHeapRecursive input) &&
        popMaxRecursiveRestCheck
          (LeanExperiments.HeapSort.buildMaxHeapRecursive input))

/-- 97,656入力全てで、構築版と抽出版の4通りが残余仕様を満たす。 -/
theorem popMaxRestBuildersWideValueCheck_passes :
    popMaxRestBuildersWideValueCheck = true := by
  native_decide

/-- 大きな値を含む各入力について、ループ構築・ループ抽出の残余仕様を得る。 -/
theorem popMaxRest_buildMaxHeap_for_wideValueInput (input : Array Nat)
    (hInput : input ∈ wideValueInputs) :
    PopMaxRestCorrect (LeanExperiments.HeapSort.buildMaxHeap input) := by
  have hAll := List.all_eq_true.mp popMaxRestBuildersWideValueCheck_passes input hInput
  rw [Bool.and_eq_true] at hAll
  have hLoopBuilder := hAll.1
  rw [Bool.and_eq_true] at hLoopBuilder
  exact (popMaxRestCheck_correct _).mp hLoopBuilder.1

/-- 大きな値を含む各入力について、ループ構築・再帰抽出の残余仕様を得る。 -/
theorem popMaxRecursiveRest_buildMaxHeap_for_wideValueInput (input : Array Nat)
    (hInput : input ∈ wideValueInputs) :
    PopMaxRecursiveRestCorrect (LeanExperiments.HeapSort.buildMaxHeap input) := by
  have hAll := List.all_eq_true.mp popMaxRestBuildersWideValueCheck_passes input hInput
  rw [Bool.and_eq_true] at hAll
  have hLoopBuilder := hAll.1
  rw [Bool.and_eq_true] at hLoopBuilder
  exact (popMaxRecursiveRestCheck_correct _).mp hLoopBuilder.2

/-- 大きな値を含む各入力について、再帰構築・ループ抽出の残余仕様を得る。 -/
theorem popMaxRest_buildMaxHeapRecursive_for_wideValueInput (input : Array Nat)
    (hInput : input ∈ wideValueInputs) :
    PopMaxRestCorrect (LeanExperiments.HeapSort.buildMaxHeapRecursive input) := by
  have hAll := List.all_eq_true.mp popMaxRestBuildersWideValueCheck_passes input hInput
  rw [Bool.and_eq_true] at hAll
  have hRecursiveBuilder := hAll.2
  rw [Bool.and_eq_true] at hRecursiveBuilder
  exact (popMaxRestCheck_correct _).mp hRecursiveBuilder.1

/-- 大きな値を含む各入力について、再帰構築・再帰抽出の残余仕様を得る。 -/
theorem popMaxRecursiveRest_buildMaxHeapRecursive_for_wideValueInput
    (input : Array Nat) (hInput : input ∈ wideValueInputs) :
    PopMaxRecursiveRestCorrect
      (LeanExperiments.HeapSort.buildMaxHeapRecursive input) := by
  have hAll := List.all_eq_true.mp popMaxRestBuildersWideValueCheck_passes input hInput
  rw [Bool.and_eq_true] at hAll
  have hRecursiveBuilder := hAll.2
  rw [Bool.and_eq_true] at hRecursiveBuilder
  exact (popMaxRecursiveRestCheck_correct _).mp hRecursiveBuilder.2

/-- 大きな値を含む各入力・根位置で下降処理の一致と両出力の要素保存を調べる。 -/
def siftDownWideAtAllRootsCheck (input : Array Nat) : Bool :=
  (List.range (input.size + 1)).all fun root =>
    let loopResult := LeanExperiments.HeapSort.siftDown input root
    let recursiveResult := LeanExperiments.HeapSort.siftDownRecursive input root
    decide (loopResult = recursiveResult) &&
      (loopResult.toList.isPerm input.toList &&
        recursiveResult.toList.isPerm input.toList)

/-- 97,656個の大きな値を含む入力で、全根位置の下降処理を検査する。 -/
def siftDownWideValueCheck : Bool :=
  wideValueInputs.all siftDownWideAtAllRootsCheck

/-- 97,656入力の全根位置で両 `siftDown` の一致と要素保存が成立する。 -/
theorem siftDownWideValueCheck_passes : siftDownWideValueCheck = true := by
  native_decide

/-- 大きな値の有限領域でも、各入力・根位置で下降結果の一致と要素保存を取り出せる。 -/
theorem siftDown_properties_for_wideValueInput (input : Array Nat)
    (hInput : input ∈ wideValueInputs) :
    ∀ root, root ≤ input.size →
      LeanExperiments.HeapSort.siftDown input root =
        LeanExperiments.HeapSort.siftDownRecursive input root ∧
      (LeanExperiments.HeapSort.siftDown input root).toList.Perm input.toList ∧
      (LeanExperiments.HeapSort.siftDownRecursive input root).toList.Perm
        input.toList := by
  have hAllInputs := List.all_eq_true.mp siftDownWideValueCheck_passes
  have hAllRoots := hAllInputs input hInput
  intro root hRoot
  have hChecks := (List.all_eq_true.mp hAllRoots) root
    (List.mem_range.mpr (by omega))
  rw [Bool.and_eq_true] at hChecks
  have hPreservation := hChecks.2
  rw [Bool.and_eq_true] at hPreservation
  exact ⟨of_decide_eq_true hChecks.1, List.isPerm_iff.mp hPreservation.1,
    List.isPerm_iff.mp hPreservation.2⟩

/-- 大きな値を含む入力で構築版と両 `popMax` 版の結果一致を直接検査する。 -/
def heapPrimitiveAgreementWideValueCheck : Bool :=
  wideValueInputs.all fun input =>
    let loopHeap := LeanExperiments.HeapSort.buildMaxHeap input
    let recursiveHeap := LeanExperiments.HeapSort.buildMaxHeapRecursive input
    decide (loopHeap = recursiveHeap) &&
      (decide (LeanExperiments.HeapSort.popMax input =
          LeanExperiments.HeapSort.popMaxRecursive input) &&
        (decide (LeanExperiments.HeapSort.popMax loopHeap =
            LeanExperiments.HeapSort.popMaxRecursive loopHeap) &&
          decide (LeanExperiments.HeapSort.popMax recursiveHeap =
            LeanExperiments.HeapSort.popMaxRecursive recursiveHeap)))

/-- 97,656入力全てで構築結果と両最大値取り出し結果が一致する。 -/
theorem heapPrimitiveAgreementWideValueCheck_passes :
    heapPrimitiveAgreementWideValueCheck = true := by
  native_decide

/-- 大きな値の有限領域に含まれる各入力から、構築・抽出結果の一致を取り出す。 -/
theorem heapPrimitiveAgreement_for_wideValueInput (input : Array Nat)
    (hInput : input ∈ wideValueInputs) :
    LeanExperiments.HeapSort.buildMaxHeap input =
        LeanExperiments.HeapSort.buildMaxHeapRecursive input ∧
      LeanExperiments.HeapSort.popMax input =
        LeanExperiments.HeapSort.popMaxRecursive input ∧
      LeanExperiments.HeapSort.popMax (LeanExperiments.HeapSort.buildMaxHeap input) =
        LeanExperiments.HeapSort.popMaxRecursive
          (LeanExperiments.HeapSort.buildMaxHeap input) ∧
      LeanExperiments.HeapSort.popMax
          (LeanExperiments.HeapSort.buildMaxHeapRecursive input) =
        LeanExperiments.HeapSort.popMaxRecursive
          (LeanExperiments.HeapSort.buildMaxHeapRecursive input) := by
  have hAllInputs := List.all_eq_true.mp heapPrimitiveAgreementWideValueCheck_passes
  have hChecks := hAllInputs input hInput
  rw [Bool.and_eq_true] at hChecks
  have hFurtherChecks := hChecks.2
  rw [Bool.and_eq_true] at hFurtherChecks
  have hHeapPopChecks := hFurtherChecks.2
  rw [Bool.and_eq_true] at hHeapPopChecks
  exact ⟨of_decide_eq_true hChecks.1, of_decide_eq_true hFurtherChecks.1,
    of_decide_eq_true hHeapPopChecks.1, of_decide_eq_true hHeapPopChecks.2⟩

/-- 大きな値を含む全入力でループ版が仕様を満たす。 -/
def heapSortWideValueCheck : Bool :=
  wideValueInputs.all fun input =>
    correctCheck input (LeanExperiments.HeapSort.heapSort input)

/-- 大きな値を含む全入力で再帰版が仕様を満たす。 -/
def heapSortRecursiveWideValueCheck : Bool :=
  wideValueInputs.all fun input =>
    correctCheck input (LeanExperiments.HeapSort.heapSortRecursive input)

/-- 大きな値を含む全入力で両実装の結果が一致する。 -/
def heapSortAgreementWideValueCheck : Bool :=
  wideValueInputs.all fun input =>
    decide (LeanExperiments.HeapSort.heapSort input =
      LeanExperiments.HeapSort.heapSortRecursive input)

/-- 97,656配列全てでループ版の仕様が成立する。 -/
theorem heapSortWideValueCheck_passes : heapSortWideValueCheck = true := by
  native_decide

/-- 97,656配列全てで再帰版の仕様が成立する。 -/
theorem heapSortRecursiveWideValueCheck_passes :
    heapSortRecursiveWideValueCheck = true := by
  native_decide

/-- 97,656配列全てで両実装の結果が一致する。 -/
theorem heapSortAgreementWideValueCheck_passes :
    heapSortAgreementWideValueCheck = true := by
  native_decide

/-! ## 偏りのある長い入力

長さ64およびヒープ階層境界付近の整列済み・逆順・同値・周期列を使い、
小さい全列挙領域では現れない長さと値の偏りを両実装で確認する。
-/

/-- 共通の偏り入力を配列に変換して再利用する。 -/
def adversarialInputs : List (Array Nat) :=
  LeanExperiments.Verification.Sorting.Spec.adversarialInputs.map List.toArray

/-- 偏り入力全てでループ版が仕様を満たす。 -/
def heapSortAdversarialCheck : Bool :=
  adversarialInputs.all fun input =>
    correctCheck input (LeanExperiments.HeapSort.heapSort input)

/-- 偏り入力全てで再帰版が仕様を満たす。 -/
def heapSortRecursiveAdversarialCheck : Bool :=
  adversarialInputs.all fun input =>
    correctCheck input (LeanExperiments.HeapSort.heapSortRecursive input)

/-- 偏り入力全てで再帰版とループ版の結果が一致する。 -/
def heapSortAgreementAdversarialCheck : Bool :=
  adversarialInputs.all fun input =>
    decide (LeanExperiments.HeapSort.heapSort input =
      LeanExperiments.HeapSort.heapSortRecursive input)

/-- 全ての偏り入力でループ版の昇順性と要素保存を確認する。 -/
theorem heapSortAdversarialCheck_passes : heapSortAdversarialCheck = true := by
  native_decide

/-- 全ての偏り入力で再帰版の昇順性と要素保存を確認する。 -/
theorem heapSortRecursiveAdversarialCheck_passes :
    heapSortRecursiveAdversarialCheck = true := by
  native_decide

/-- 全ての偏り入力で再帰版とループ版の一致を確認する。 -/
theorem heapSortAgreementAdversarialCheck_passes :
    heapSortAgreementAdversarialCheck = true := by
  native_decide

/-- 偏り入力の有限領域に含まれる入力について、ループ版の `Correct` を取り出せる。 -/
theorem heapSort_correct_for_adversarialInput (input : Array Nat)
    (hInput : input ∈ adversarialInputs) :
    Correct input (LeanExperiments.HeapSort.heapSort input) := by
  have hAll : ∀ candidate ∈ adversarialInputs,
      correctCheck candidate (LeanExperiments.HeapSort.heapSort candidate) = true :=
    List.all_eq_true.mp heapSortAdversarialCheck_passes
  exact correctCheck_sound input _ (hAll input hInput)

/-- 偏り入力の有限領域に含まれる入力について、再帰版の `Correct` を取り出せる。 -/
theorem heapSortRecursive_correct_for_adversarialInput (input : Array Nat)
    (hInput : input ∈ adversarialInputs) :
    Correct input (LeanExperiments.HeapSort.heapSortRecursive input) := by
  have hAll : ∀ candidate ∈ adversarialInputs,
      correctCheck candidate (LeanExperiments.HeapSort.heapSortRecursive candidate) = true :=
    List.all_eq_true.mp heapSortRecursiveAdversarialCheck_passes
  exact correctCheck_sound input _ (hAll input hInput)

/-! ## 長さと64ビット幅を組み合わせた境界値入力

ヒープ階層の境界となる各長さで、0 と最大値の交互列、0・1・`2^32`・最大値の
周期列、最大値付近の連続値、および最大値の同値列を検査する。 -/

/-- 12種類の境界長それぞれに4種類の64ビット値パターンを作る。 -/
def wideAdversarialInputs : List (Array Nat) :=
  LeanExperiments.Verification.Sorting.Spec.wideAdversarialInputs.map List.toArray

/-- 長さ境界を含む48入力で、両ヒープ構築版のヒープ条件と要素保存を調べる。 -/
def heapBuildersWideAdversarialCheck : Bool :=
  wideAdversarialInputs.all fun input =>
    heapBuildCheck input (LeanExperiments.HeapSort.buildMaxHeap input) &&
      heapBuildCheck input (LeanExperiments.HeapSort.buildMaxHeapRecursive input)

/-- 48個の64ビット境界値入力全てで両ヒープ構築版が仕様を満たす。 -/
theorem heapBuildersWideAdversarialCheck_passes :
    heapBuildersWideAdversarialCheck = true := by
  native_decide

/-- 長い境界入力ごとに、両ヒープ構築版の論理仕様を取り出せる。 -/
theorem heapBuildCorrect_for_wideAdversarialInput (input : Array Nat)
    (hInput : input ∈ wideAdversarialInputs) :
    HeapBuildCorrect input (LeanExperiments.HeapSort.buildMaxHeap input) ∧
      HeapBuildCorrect input (LeanExperiments.HeapSort.buildMaxHeapRecursive input) := by
  have hChecks := (List.all_eq_true.mp heapBuildersWideAdversarialCheck_passes)
    input hInput
  rw [Bool.and_eq_true] at hChecks
  exact ⟨(heapBuildCheck_correct _ _).mp hChecks.1,
    (heapBuildCheck_correct _ _).mp hChecks.2⟩

/-- 48個の長い境界値入力で、両構築版と両抽出版の残余仕様を調べる。 -/
def popMaxRestWideAdversarialCheck : Bool :=
  wideAdversarialInputs.all fun input =>
    (popMaxRestCheck (LeanExperiments.HeapSort.buildMaxHeap input) &&
      popMaxRecursiveRestCheck (LeanExperiments.HeapSort.buildMaxHeap input)) &&
      (popMaxRestCheck (LeanExperiments.HeapSort.buildMaxHeapRecursive input) &&
        popMaxRecursiveRestCheck
          (LeanExperiments.HeapSort.buildMaxHeapRecursive input))

/-- 長さ63〜513の48境界値入力で、4通り全ての `popMax` 残余仕様が成立する。 -/
theorem popMaxRestWideAdversarialCheck_passes :
    popMaxRestWideAdversarialCheck = true := by
  native_decide

/-- 各長い境界値入力で、両構築版と両抽出版の残余仕様を取り出せる。 -/
theorem popMaxRest_properties_for_wideAdversarialInput
    (input : Array Nat) (hInput : input ∈ wideAdversarialInputs) :
    PopMaxRestCorrect (LeanExperiments.HeapSort.buildMaxHeap input) ∧
      PopMaxRecursiveRestCorrect (LeanExperiments.HeapSort.buildMaxHeap input) ∧
      PopMaxRestCorrect (LeanExperiments.HeapSort.buildMaxHeapRecursive input) ∧
      PopMaxRecursiveRestCorrect
        (LeanExperiments.HeapSort.buildMaxHeapRecursive input) := by
  have hAll := List.all_eq_true.mp popMaxRestWideAdversarialCheck_passes input hInput
  rw [Bool.and_eq_true] at hAll
  have hLoopBuilder := hAll.1
  rw [Bool.and_eq_true] at hLoopBuilder
  have hRecursiveBuilder := hAll.2
  rw [Bool.and_eq_true] at hRecursiveBuilder
  exact ⟨(popMaxRestCheck_correct _).mp hLoopBuilder.1,
    (popMaxRecursiveRestCheck_correct _).mp hLoopBuilder.2,
    (popMaxRestCheck_correct _).mp hRecursiveBuilder.1,
    (popMaxRecursiveRestCheck_correct _).mp hRecursiveBuilder.2⟩

/-- ヒープ階層境界の各長さで全根位置の下降一致と両出力の要素保存を調べる。 -/
def siftDownWideAdversarialAtAllRootsCheck (input : Array Nat) : Bool :=
  (List.range (input.size + 1)).all fun root =>
    let loopResult := LeanExperiments.HeapSort.siftDown input root
    let recursiveResult := LeanExperiments.HeapSort.siftDownRecursive input root
    decide (loopResult = recursiveResult) &&
      (loopResult.toList.isPerm input.toList &&
        recursiveResult.toList.isPerm input.toList)

/-- 長さ63〜513の48境界値入力で、全ての根位置の `siftDown` を検査する。 -/
def siftDownWideAdversarialCheck : Bool :=
  wideAdversarialInputs.all siftDownWideAdversarialAtAllRootsCheck

/-- 48境界値入力の全根位置で両下降処理の一致と要素保存が成立する。 -/
theorem siftDownWideAdversarialCheck_passes :
    siftDownWideAdversarialCheck = true := by
  native_decide

/-- 境界長の各入力・根位置で下降処理の一致と要素保存を取り出せる。 -/
theorem siftDown_properties_for_wideAdversarialInput (input : Array Nat)
    (hInput : input ∈ wideAdversarialInputs) :
    ∀ root, root ≤ input.size →
      LeanExperiments.HeapSort.siftDown input root =
        LeanExperiments.HeapSort.siftDownRecursive input root ∧
      (LeanExperiments.HeapSort.siftDown input root).toList.Perm input.toList ∧
      (LeanExperiments.HeapSort.siftDownRecursive input root).toList.Perm
        input.toList := by
  have hAllInputs := List.all_eq_true.mp siftDownWideAdversarialCheck_passes
  have hAllRoots := hAllInputs input hInput
  intro root hRoot
  have hChecks := (List.all_eq_true.mp hAllRoots) root
    (List.mem_range.mpr (by omega))
  rw [Bool.and_eq_true] at hChecks
  have hPreservation := hChecks.2
  rw [Bool.and_eq_true] at hPreservation
  exact ⟨of_decide_eq_true hChecks.1, List.isPerm_iff.mp hPreservation.1,
    List.isPerm_iff.mp hPreservation.2⟩

/-- 境界値を含む長い入力でループ版の仕様適合を確認する。 -/
def heapSortWideAdversarialCheck : Bool :=
  wideAdversarialInputs.all fun input =>
    correctCheck input (LeanExperiments.HeapSort.heapSort input)

/-- 境界値を含む長い入力で再帰版の仕様適合を確認する。 -/
def heapSortRecursiveWideAdversarialCheck : Bool :=
  wideAdversarialInputs.all fun input =>
    correctCheck input (LeanExperiments.HeapSort.heapSortRecursive input)

/-- 境界値を含む長い入力で両実装の出力一致を確認する。 -/
def heapSortAgreementWideAdversarialCheck : Bool :=
  wideAdversarialInputs.all fun input =>
    decide (LeanExperiments.HeapSort.heapSort input =
      LeanExperiments.HeapSort.heapSortRecursive input)

/-- 12境界長×4種類の48入力全てでループ版の仕様適合を確認する。 -/
theorem heapSortWideAdversarialCheck_passes :
    heapSortWideAdversarialCheck = true := by
  native_decide

/-- 48入力全てで再帰版の仕様適合を確認する。 -/
theorem heapSortRecursiveWideAdversarialCheck_passes :
    heapSortRecursiveWideAdversarialCheck = true := by
  native_decide

/-- 48入力全てで両実装の出力一致を確認する。 -/
theorem heapSortAgreementWideAdversarialCheck_passes :
    heapSortAgreementWideAdversarialCheck = true := by
  native_decide

/-- 列挙した長い境界値入力それぞれについてループ版の正しさを取り出す。 -/
theorem heapSort_correct_for_wideAdversarialInput (input : Array Nat)
    (hInput : input ∈ wideAdversarialInputs) :
    Correct input (LeanExperiments.HeapSort.heapSort input) := by
  have hAll : ∀ candidate ∈ wideAdversarialInputs,
      correctCheck candidate (LeanExperiments.HeapSort.heapSort candidate) = true :=
    List.all_eq_true.mp heapSortWideAdversarialCheck_passes
  exact correctCheck_sound input _ (hAll input hInput)

/-- 列挙した長い境界値入力それぞれについて再帰版の正しさを取り出す。 -/
theorem heapSortRecursive_correct_for_wideAdversarialInput (input : Array Nat)
    (hInput : input ∈ wideAdversarialInputs) :
    Correct input (LeanExperiments.HeapSort.heapSortRecursive input) := by
  have hAll : ∀ candidate ∈ wideAdversarialInputs,
      correctCheck candidate (LeanExperiments.HeapSort.heapSortRecursive candidate) = true :=
    List.all_eq_true.mp heapSortRecursiveWideAdversarialCheck_passes
  exact correctCheck_sound input _ (hAll input hInput)

/-! ## 1024要素付近の大きな偏り入力

ヒープ階層がさらに深くなる境界で、全ソート共通の大きな偏り入力を使い、
両ヒープソート実装の仕様適合と出力一致を個別に確認する。
-/

/-- 共通仕様で定義した長さ1023・1024・1025の12入力を配列に変換する。 -/
def largeAdversarialInputs : List (Array Nat) :=
  LeanExperiments.Verification.Sorting.Spec.largeAdversarialInputs.map List.toArray

/-- 1023〜1025要素の全12入力でループ版ヒープソートの仕様適合を調べる。 -/
def heapSortLargeAdversarialCheck : Bool :=
  largeAdversarialInputs.all fun input =>
    correctCheck input (LeanExperiments.HeapSort.heapSort input)

/-- 1023〜1025要素の全12入力で再帰版ヒープソートの仕様適合を調べる。 -/
def heapSortRecursiveLargeAdversarialCheck : Bool :=
  largeAdversarialInputs.all fun input =>
    correctCheck input (LeanExperiments.HeapSort.heapSortRecursive input)

/-- 1023〜1025要素の全12入力で両ヒープソートの結果一致を調べる。 -/
def heapSortAgreementLargeAdversarialCheck : Bool :=
  largeAdversarialInputs.all fun input =>
    decide (LeanExperiments.HeapSort.heapSort input =
      LeanExperiments.HeapSort.heapSortRecursive input)

/-- 全12個の大きな偏り入力で、ループ版ヒープソートが仕様を満たす。 -/
theorem heapSortLargeAdversarialCheck_passes :
    heapSortLargeAdversarialCheck = true := by
  native_decide

/-- 全12個の大きな偏り入力で、再帰版ヒープソートが仕様を満たす。 -/
theorem heapSortRecursiveLargeAdversarialCheck_passes :
    heapSortRecursiveLargeAdversarialCheck = true := by
  native_decide

/-- 全12個の大きな偏り入力で、両ヒープソートの結果が一致する。 -/
theorem heapSortAgreementLargeAdversarialCheck_passes :
    heapSortAgreementLargeAdversarialCheck = true := by
  native_decide

/-- 大きな偏り入力ごとに、ループ版ヒープソートの論理的正しさを取り出す。 -/
theorem heapSort_correct_for_largeAdversarialInput (input : Array Nat)
    (hInput : input ∈ largeAdversarialInputs) :
    Correct input (LeanExperiments.HeapSort.heapSort input) := by
  have hAll : ∀ candidate ∈ largeAdversarialInputs,
      correctCheck candidate (LeanExperiments.HeapSort.heapSort candidate) = true :=
    List.all_eq_true.mp heapSortLargeAdversarialCheck_passes
  exact correctCheck_sound input _ (hAll input hInput)

/-- 大きな偏り入力ごとに、再帰版ヒープソートの論理的正しさを取り出す。 -/
theorem heapSortRecursive_correct_for_largeAdversarialInput (input : Array Nat)
    (hInput : input ∈ largeAdversarialInputs) :
    Correct input (LeanExperiments.HeapSort.heapSortRecursive input) := by
  have hAll : ∀ candidate ∈ largeAdversarialInputs,
      correctCheck candidate (LeanExperiments.HeapSort.heapSortRecursive candidate) = true :=
    List.all_eq_true.mp heapSortRecursiveLargeAdversarialCheck_passes
  exact correctCheck_sound input _ (hAll input hInput)

/-- 共通仕様の大きな64ビット境界値入力を配列として再利用する。 -/
def largeWideAdversarialInputs : List (Array Nat) :=
  LeanExperiments.Verification.Sorting.Spec.largeWideAdversarialInputs.map List.toArray

/-- 1023〜1025要素の64ビット境界値12入力で、ループ版の仕様を調べる。 -/
def heapSortLargeWideAdversarialCheck : Bool :=
  largeWideAdversarialInputs.all fun input =>
    correctCheck input (LeanExperiments.HeapSort.heapSort input)

/-- 1023〜1025要素の64ビット境界値12入力で、再帰版の仕様を調べる。 -/
def heapSortRecursiveLargeWideAdversarialCheck : Bool :=
  largeWideAdversarialInputs.all fun input =>
    correctCheck input (LeanExperiments.HeapSort.heapSortRecursive input)

/-- 1023〜1025要素の64ビット境界値12入力で、両ヒープソートの一致を調べる。 -/
def heapSortAgreementLargeWideAdversarialCheck : Bool :=
  largeWideAdversarialInputs.all fun input =>
    decide (LeanExperiments.HeapSort.heapSort input =
      LeanExperiments.HeapSort.heapSortRecursive input)

/-- 全ての大きな64ビット境界値入力で、ループ版の仕様が成り立つ。 -/
theorem heapSortLargeWideAdversarialCheck_passes :
    heapSortLargeWideAdversarialCheck = true := by
  native_decide

/-- 全ての大きな64ビット境界値入力で、再帰版の仕様が成り立つ。 -/
theorem heapSortRecursiveLargeWideAdversarialCheck_passes :
    heapSortRecursiveLargeWideAdversarialCheck = true := by
  native_decide

/-- 全ての大きな64ビット境界値入力で、両ヒープソートの結果が一致する。 -/
theorem heapSortAgreementLargeWideAdversarialCheck_passes :
    heapSortAgreementLargeWideAdversarialCheck = true := by
  native_decide

/-- 大きな64ビット境界値入力ごとに、ループ版の `Correct` を取り出す。 -/
theorem heapSort_correct_for_largeWideAdversarialInput (input : Array Nat)
    (hInput : input ∈ largeWideAdversarialInputs) :
    Correct input (LeanExperiments.HeapSort.heapSort input) := by
  have hAll := List.all_eq_true.mp heapSortLargeWideAdversarialCheck_passes
  exact correctCheck_sound input _ (hAll input hInput)

/-- 大きな64ビット境界値入力ごとに、再帰版の `Correct` を取り出す。 -/
theorem heapSortRecursive_correct_for_largeWideAdversarialInput (input : Array Nat)
    (hInput : input ∈ largeWideAdversarialInputs) :
    Correct input (LeanExperiments.HeapSort.heapSortRecursive input) := by
  have hAll := List.all_eq_true.mp heapSortRecursiveLargeWideAdversarialCheck_passes
  exact correctCheck_sound input _ (hAll input hInput)

end LeanExperiments.Verification.HeapSort.Spec
