/-!
# CLI 共通処理

各コマンドで同じ入力規則を使えるようにする補助関数をまとめる。
入力は標準入力を EOF まで読み、空白文字で分割してから自然数として解釈する。
-/

namespace LeanExperiments.CLI

/-- エラーを標準エラーへ表示し、失敗を表す終了コードでプロセスを終える。 -/
private def inputError {α : Type} (application message : String) : IO α := do
  IO.eprintln s!"{application}: {message}"
  IO.Process.exit 1

/-- トークンを末尾再帰で解析し、順序を保った自然数列を返す。 -/
private def parseNatTokensAux : List String → List Nat → Except String (List Nat)
  | [], reversed => .ok reversed.reverse
  | token :: tokens, reversed =>
      match token.toNat? with
      | none => .error "expected non-negative integers"
      | some number => parseNatTokensAux tokens (number :: reversed)

/-- 空白分割後のトークン列を左から自然数列へ変換する。 -/
def parseNatTokens (tokens : List String) : Except String (List Nat) :=
  parseNatTokensAux tokens []

/-- 末尾再帰パーサーは、任意トークン列の `mapM` 仕様と一致する。 -/
private theorem parseNatTokensAux_spec (tokens : List String) (reversed : List Nat) :
    parseNatTokensAux tokens reversed =
      match tokens.mapM String.toNat? with
      | some numbers => .ok (reversed.reverse ++ numbers)
      | none => .error "expected non-negative integers" := by
  induction tokens generalizing reversed with
  | nil => simp [parseNatTokensAux]
  | cons token tokens ih =>
      cases hToken : token.toNat? with
      | none => simp [parseNatTokensAux, hToken]
      | some number =>
          simp only [parseNatTokensAux, hToken, List.mapM_cons]
          cases hTail : tokens.mapM String.toNat? with
          | none => simp [ih, hTail]
          | some numbers => simp [ih, hTail, List.reverse_cons, List.append_assoc]

/-- 成功・失敗と成功時の順序を、任意トークン列の独立 `mapM` 仕様と照合する。 -/
theorem parseNatTokens_spec (tokens : List String) :
    parseNatTokens tokens =
      match tokens.mapM String.toNat? with
      | some numbers => .ok numbers
      | none => .error "expected non-negative integers" := by
  rw [parseNatTokens]
  simpa using parseNatTokensAux_spec tokens []

/-- 空白入力から、空トークンを除いたトークン列を得る。 -/
def splitNatTokens (input : String) : List String :=
  (input.split Char.isWhitespace).map String.Slice.toString
    |>.filter (!·.isEmpty)
    |>.toList

/-- 空白区切りの入力を、0個以上の自然数の配列へ変換する純粋関数。

空白文字だけの入力は空配列になる。各トークンは `String.toNat?` で解釈するため、
負数や数字以外を含むトークンはエラーとなり、先行する値だけを返すことはない。
-/
def parseNatList (input : String) : Except String (Array Nat) := do
  match parseNatTokens (splitNatTokens input) with
  | .error message => .error message
  | .ok numbers => .ok numbers.toArray

/-- 入力全体が非負整数ちょうど1個である場合に、その値を返す純粋関数。 -/
def parseNat (input : String) : Except String Nat :=
  match parseNatList input with
  | .error message => .error message
  | .ok numbers =>
    match numbers.toList with
    | [number] => .ok number
    | _ => .error "expected exactly one integer on standard input"

/-- 自然数配列を、値の間にASCII空白を1つ置いた十進表記へ変換する。 -/
def formatNatList (numbers : Array Nat) : String :=
  String.intercalate " " (numbers.toList.map toString)

/-- 中央値の分子・分母を、自然数または `.5` を使った十進表記へ整える。 -/
def formatMedian : Option (Nat × Nat) → String
  | none => "none"
  | some (numerator, 1) => toString numerator
  | some (numerator, 2) =>
      if numerator % 2 == 0 then
        toString (numerator / 2)
      else
        s!"{numerator / 2}.5"
  | some (numerator, denominator) => s!"{numerator}/{denominator}"

/-- 標準入力から、空白区切りの 0 個以上の非負整数を読み取る。

ヒープソートのように複数の値を受け取るコマンドで使う。
空入力は空の配列として扱い、数字に変換できない語があればエラーにする。
-/
def readNatList (application : String) : IO (Array Nat) := do
  let stdin ← IO.getStdin
  let input ← stdin.readToEnd
  match parseNatList input with
  | .ok numbers => pure numbers
  | .error message => inputError application message

/-- 標準入力から非負整数をちょうど 1 個読み取る。

階乗、素因数分解、Fibonacci のように単一の値を処理するコマンドで使う。
読み取った個数が 0 個または 2 個以上の場合も入力エラーとして終了する。
-/
def readNat (application : String) : IO Nat := do
  let stdin ← IO.getStdin
  let input ← stdin.readToEnd
  match parseNat input with
  | .ok number => pure number
  | .error message => inputError application message

end LeanExperiments.CLI
