import LeanExperiments.CLI
import LeanExperiments.Verification.RunningMedian.Spec

/-!
# CLI 入力パーサーの検証

標準入力の読み取りから純粋な文字列パーサーを分離し、空白の扱い、自然数の境界値、
不正トークン、単一値入力の個数制約をカーネル内の計算で確認する。
-/

namespace LeanExperiments.Verification.CLI

/-- 複数値出力へ末尾の値を追加すると、必要な場合だけ区切り空白が1つ入る。 -/
theorem formatNatList_push (numbers : Array Nat) (value : Nat) :
    LeanExperiments.CLI.formatNatList (numbers.push value) =
      if numbers.isEmpty then toString value
      else LeanExperiments.CLI.formatNatList numbers ++ " " ++ toString value := by
  by_cases hEmpty : numbers.toList = []
  · have hArray : numbers = #[] :=
      Array.toList_inj.mp (by simpa using hEmpty)
    simp [LeanExperiments.CLI.formatNatList, hArray]
  · have hArray : numbers ≠ #[] := by
      intro h
      simp [h] at hEmpty
    have hMap : numbers.toList.map toString ≠ [] := by
      simpa using hEmpty
    simp only [LeanExperiments.CLI.formatNatList, Array.toList_push,
      List.map_append, List.map_singleton]
    rw [String.intercalate_append_of_ne_nil hMap (by simp)]
    simp [Array.isEmpty_iff, hArray]

/-- 二つの非空配列を連結して整形すると、個別の整形結果を空白1つで結べる。 -/
theorem formatNatList_append_of_ne_nil (left right : Array Nat)
    (hLeft : left ≠ #[]) (hRight : right ≠ #[]) :
    LeanExperiments.CLI.formatNatList (left ++ right) =
      LeanExperiments.CLI.formatNatList left ++ " " ++
        LeanExperiments.CLI.formatNatList right := by
  have hLeftTokens : left.toList.map toString ≠ [] := by
    intro h
    apply hLeft
    have hList : left.toList = [] := by simpa using h
    exact Array.toList_inj.mp hList
  have hRightTokens : right.toList.map toString ≠ [] := by
    intro h
    apply hRight
    have hList : right.toList = [] := by simpa using h
    exact Array.toList_inj.mp hList
  simpa [LeanExperiments.CLI.formatNatList, Array.toList_append, List.map_append] using
    (String.intercalate_append_of_ne_nil hLeftTokens hRightTokens
      (s := " ") (l := left.toList.map toString) (m := right.toList.map toString))

/-- 配列パーサーが指定値を返すかを、エラー文字列に依存せず判定する。 -/
private def parsesNatListAs (input : String) (expected : Array Nat) : Bool :=
  match LeanExperiments.CLI.parseNatList input with
  | .ok numbers => numbers == expected
  | .error _ => false

/-- 単一値パーサーが指定値を返すかを判定する。 -/
private def parsesNatAs (input : String) (expected : Nat) : Bool :=
  match LeanExperiments.CLI.parseNat input with
  | .ok number => number == expected
  | .error _ => false

/-- 指定入力が、指定されたエラーメッセージで失敗するかを確認する。 -/
private def parseNatErrorIs (input message : String) : Bool :=
  match LeanExperiments.CLI.parseNat input with
  | .ok _ => false
  | .error actualMessage => actualMessage == message

/-- トークン列を `Option` の全件変換で解釈する独立仕様。 -/
def parseNatTokensSpec (tokens : List String) : Option (List Nat) :=
  tokens.mapM String.toNat?

/-- トークン変換仕様が失敗するのは、変換できないトークンが含まれる場合に限る。 -/
theorem parseNatTokensSpec_none_iff_invalid (tokens : List String) :
    parseNatTokensSpec tokens = none ↔
      ∃ token, token ∈ tokens ∧ token.toNat? = none := by
  induction tokens with
  | nil => simp [parseNatTokensSpec]
  | cons token tokens ih =>
      cases hToken : token.toNat? with
      | none => simp [parseNatTokensSpec, List.mapM_cons, hToken]
      | some value =>
          cases hTail : tokens.mapM String.toNat? with
          | none =>
              constructor
              · intro _
                obtain ⟨invalid, hInvalidMem, hInvalid⟩ := ih.mp hTail
                exact ⟨invalid, List.mem_cons_of_mem _ hInvalidMem, hInvalid⟩
              · intro _
                simp [parseNatTokensSpec, List.mapM_cons, hToken, hTail]
          | some numbers =>
              constructor
              · intro hNone
                simp [parseNatTokensSpec, List.mapM_cons, hToken, hTail] at hNone
              · intro hInvalid
                obtain ⟨invalid, hInvalidMem, hInvalid⟩ := hInvalid
                simp only [List.mem_cons] at hInvalidMem
                rcases hInvalidMem with hHead | hInvalidMem
                · subst invalid
                  simp [hToken] at hInvalid
                · have hTailNone : tokens.mapM String.toNat? = none :=
                    ih.mpr ⟨invalid, hInvalidMem, hInvalid⟩
                  rw [hTail] at hTailNone
                  contradiction

/-- 文字列を文字列リスト上で空白文字ごとに分割し、空部分列を除く独立モデル。 -/
def splitNatTokensSpec (input : String) : List String :=
  (input.toList.splitOnP Char.isWhitespace).map String.ofList
    |>.filter (!·.isEmpty)

/-- CLI の空白分割実装は、文字リスト上の分割モデルと任意の入力で一致する。

実装側は部分文字列スライスを使い、仕様側は入力を文字リストへ変換して分割する。
Lean の `String.toList_split_bool` により、両者の分割結果を照合する。
-/
theorem splitNatTokens_spec (input : String) :
    LeanExperiments.CLI.splitNatTokens input = splitNatTokensSpec input := by
  simp [LeanExperiments.CLI.splitNatTokens, splitNatTokensSpec,
    String.toList_split_bool]

/-- 再帰実装は、任意トークン列の全件変換仕様と一致する。

不正トークンがあれば列全体が失敗し、すべて有効なら順序を保った自然数列を返す。
-/
theorem parseNatTokens_spec (tokens : List String) :
    LeanExperiments.CLI.parseNatTokens tokens =
      match parseNatTokensSpec tokens with
      | some numbers => .ok numbers
      | none => .error "expected non-negative integers" := by
  exact LeanExperiments.CLI.parseNatTokens_spec tokens

/-- 文字列パーサーは、空白分割後のトークン列を独立仕様どおりに変換する。 -/
theorem parseNatList_spec (input : String) :
    LeanExperiments.CLI.parseNatList input =
      match parseNatTokensSpec (splitNatTokensSpec input) with
      | some numbers => .ok numbers.toArray
      | none => .error "expected non-negative integers" := by
  rw [LeanExperiments.CLI.parseNatList]
  rw [splitNatTokens_spec]
  rw [parseNatTokens_spec]
  cases parseNatTokensSpec (splitNatTokensSpec input) <;> rfl

/-- 複数値パーサーの変換エラーは、空白分割モデル中の不正トークンと同値である。 -/
theorem parseNatList_error_iff_invalid (input : String) :
    LeanExperiments.CLI.parseNatList input =
        .error "expected non-negative integers" ↔
      ∃ token, token ∈ splitNatTokensSpec input ∧ token.toNat? = none := by
  rw [parseNatList_spec]
  cases hSpec : parseNatTokensSpec (splitNatTokensSpec input) with
  | none =>
      constructor
      · intro _
        exact (parseNatTokensSpec_none_iff_invalid _).mp hSpec
      · intro _
        simp
  | some numbers =>
      have hNoInvalid :
          ¬ ∃ token, token ∈ splitNatTokensSpec input ∧ token.toNat? = none := by
        intro hInvalid
        have hNone := (parseNatTokensSpec_none_iff_invalid _).2 hInvalid
        rw [hSpec] at hNone
        contradiction
      constructor
      · intro hError
        simp at hError
      · intro hInvalid
        exact False.elim (hNoInvalid hInvalid)

/-- 複数値パーサーが成功することと、空白分割で得た全トークンが自然数へ変換できることは
同値である。成功時は独立仕様の変換結果を順序どおり配列で返す。
-/
theorem parseNatList_success_iff_all_tokens_convertible (input : String) :
    (∃ numbers, LeanExperiments.CLI.parseNatList input = .ok numbers) ↔
      ∀ token, token ∈ splitNatTokensSpec input → token.toNat? ≠ none := by
  constructor
  · rintro ⟨numbers, hParsed⟩ token hMember hInvalid
    have hNone : parseNatTokensSpec (splitNatTokensSpec input) = none :=
      (parseNatTokensSpec_none_iff_invalid _).2 ⟨token, hMember, hInvalid⟩
    rw [parseNatList_spec, hNone] at hParsed
    cases hParsed
  · intro hValid
    have hTokens : ∃ values,
        parseNatTokensSpec (splitNatTokensSpec input) = some values := by
      cases hParsed : parseNatTokensSpec (splitNatTokensSpec input) with
      | none =>
          obtain ⟨token, hMember, hInvalid⟩ :=
            (parseNatTokensSpec_none_iff_invalid _).mp hParsed
          exact False.elim (hValid token hMember hInvalid)
      | some values => exact ⟨values, rfl⟩
    obtain ⟨values, hParsed⟩ := hTokens
    refine ⟨values.toArray, ?_⟩
    rw [parseNatList_spec, hParsed]

/-- 単一値パーサーは、独立した文字列・数値仕様の結果を個数制約で分類する。

トークン変換の失敗はそのまま伝播し、成功した数値列がちょうど1要素の場合だけ値を返す。
-/
theorem parseNat_spec (input : String) :
    LeanExperiments.CLI.parseNat input =
      match parseNatTokensSpec (splitNatTokensSpec input) with
      | none => .error "expected non-negative integers"
      | some [value] => .ok value
      | some _ => .error "expected exactly one integer on standard input" := by
  rw [LeanExperiments.CLI.parseNat, parseNatList_spec]
  cases hSpec : parseNatTokensSpec (splitNatTokensSpec input) with
  | none => rfl
  | some numbers =>
      cases numbers with
      | nil => rfl
      | cons value rest =>
          cases rest with
          | nil => rfl
          | cons _ _ => rfl

/-- 単一値パーサーの成功条件は、独立仕様がその値だけを返すことと同値である。 -/
theorem parseNat_success_iff_spec (input : String) (value : Nat) :
    LeanExperiments.CLI.parseNat input = .ok value ↔
      parseNatTokensSpec (splitNatTokensSpec input) = some [value] := by
  rw [parseNat_spec]
  cases hSpec : parseNatTokensSpec (splitNatTokensSpec input) with
  | none => simp
  | some numbers =>
      cases numbers with
      | nil => simp
      | cons first rest =>
          cases rest with
          | nil => simp
          | cons _ _ => simp

/-- 単一値パーサーが成功するのは、リストパーサーの結果がその1値だけの場合に限る。 -/
theorem parseNat_success_iff (input : String) (value : Nat) :
    LeanExperiments.CLI.parseNat input = .ok value ↔
      ∃ numbers, LeanExperiments.CLI.parseNatList input = .ok numbers ∧
        numbers.toList = [value] := by
  cases hParsed : LeanExperiments.CLI.parseNatList input with
  | error message => simp [LeanExperiments.CLI.parseNat, hParsed]
  | ok numbers =>
    cases hNumbers : numbers.toList with
    | nil => simp [LeanExperiments.CLI.parseNat, hParsed, hNumbers]
    | cons first rest =>
      cases rest with
      | nil => simp [LeanExperiments.CLI.parseNat, hParsed, hNumbers]
      | cons second tail =>
        simp [LeanExperiments.CLI.parseNat, hParsed, hNumbers]

/-- 単一値パーサーの失敗理由は、配列パース失敗か個数不一致に限られる。

前者のエラー文字列はそのまま伝播し、配列パースに成功した場合は要素数が1でないときだけ
個数エラーになることを、任意の入力文字列について分類する。
-/
theorem parseNat_error_iff (input : String) (message : String) :
    LeanExperiments.CLI.parseNat input = .error message ↔
      (∃ listMessage,
        LeanExperiments.CLI.parseNatList input = .error listMessage ∧
          message = listMessage) ∨
      (∃ numbers,
        LeanExperiments.CLI.parseNatList input = .ok numbers ∧
          numbers.toList.length ≠ 1 ∧
          message = "expected exactly one integer on standard input") := by
  cases hParsed : LeanExperiments.CLI.parseNatList input with
  | error listMessage =>
      simp [LeanExperiments.CLI.parseNat, hParsed, eq_comm]
  | ok numbers =>
      have hSize : numbers.size = numbers.toList.length := by simp
      cases hNumbers : numbers.toList with
      | nil => simp [LeanExperiments.CLI.parseNat, hParsed, hNumbers, hSize, eq_comm]
      | cons first rest =>
          cases rest with
          | nil => simp [LeanExperiments.CLI.parseNat, hParsed, hNumbers, hSize, eq_comm]
          | cons second tail =>
              simp [LeanExperiments.CLI.parseNat, hParsed, hNumbers, hSize, eq_comm]

/-- 空白だけの入力は、値を持たないリストとして受理する。 -/
theorem parseNatList_emptyWhitespace_example :
    parsesNatListAs " \t\n\r " #[] = true := by
  native_decide

/-- 標準入力が EOF まで完全に空の場合も、複数値パーサーは空配列を返す。 -/
theorem parseNatList_emptyInput_example :
    parsesNatListAs "" #[] = true := by
  native_decide

/-- 空白の連続・行頭・行末にかかわらず、各非負整数を順番どおりに読む。 -/
theorem parseNatList_mixedWhitespace_example :
    parsesNatListAs "  12\t0\n34\r\n " #[12, 0, 34] = true := by
  native_decide

/-- 64 bit の最大値を超える自然数も、桁落ちせずに読み取る。 -/
theorem parseNatList_largeInteger_example :
    parsesNatListAs "18446744073709551616" #[18446744073709551616] = true := by
  native_decide

/-- 不正トークンより前に数値があっても、部分的な結果を成功として返さない。 -/
theorem parseNatList_rejectsInvalidToken_example :
    parseNatErrorIs "12 3x 45" "expected non-negative integers" = true := by
  native_decide

/-- 自然数専用のため、負数表記は受理しない。 -/
theorem parseNatList_rejectsNegativeNumber_example :
    parseNatErrorIs "-1" "expected non-negative integers" = true := by
  native_decide

/-- 単一値パーサーは、前後の空白を許しつつ一つの値を返す。 -/
theorem parseNat_singleValue_example :
    parsesNatAs " \n 42 \t" 42 = true := by
  native_decide

/-- 空入力では、単一値パーサーは「ちょうど1個」という制約違反を返す。 -/
theorem parseNat_rejectsEmpty_example :
    parseNatErrorIs "" "expected exactly one integer on standard input" = true := by
  native_decide

/-- 空白だけの入力も、単一値パーサーでは「ちょうど1個」という制約違反になる。 -/
theorem parseNat_rejectsWhitespaceOnly_example :
    parseNatErrorIs " \t\n" "expected exactly one integer on standard input" = true := by
  native_decide

/-- 複数値入力も単一値パーサーでは拒否する。 -/
theorem parseNat_rejectsMultipleValues_example :
    parseNatErrorIs "1 2" "expected exactly one integer on standard input" = true := by
  native_decide

/-- 単一値パーサーも、不正トークンを個数エラーに置き換えず伝播する。 -/
theorem parseNat_propagatesInvalidToken_example :
    parseNatErrorIs "1 nope" "expected non-negative integers" = true := by
  native_decide

/-- 中央値CLIの表示対象は、任意入力で独立なソート基準中央値と一致する。

共通の純粋フォーマッターへ渡す分子・分母が一致するため、CLIが表示する文字列も
実装のヒープ状態ではなく独立仕様で定まる。
-/
theorem formatMedian_medianOf_eq_medianSpec (values : Array Nat) :
    LeanExperiments.CLI.formatMedian (LeanExperiments.RunningMedian.medianOf values) =
      LeanExperiments.CLI.formatMedian
        (LeanExperiments.Verification.RunningMedian.medianSpec values) := by
  rw [LeanExperiments.Verification.RunningMedian.medianOf_eq_medianSpec_arbitrary]

end LeanExperiments.Verification.CLI
