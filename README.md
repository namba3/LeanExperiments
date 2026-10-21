# LeanExperiments

[日本語](README.md) | [English](README.en.md)

Lean 4 でアルゴリズムを実装し、動作や性質を確かめながら練習するためのプロジェクトです。アルゴリズム本体、標準入力から動く CLI、検証用の仕様や証明を分けて管理します。

## 必要な環境

- Lean 4.35.0（`elan` で管理。バージョンは `lean-toolchain` で固定）
- Lake（Lean に同梱）

## ビルド

プロジェクトのルートで次を実行します。

```sh
lake build
```

このコマンドはライブラリと CLI をまとめてビルドします。個別の CLI は `lake exe <名前>` で実行できます。

## CLI の使い方

階乗、素因数分解、Fibonacci は標準入力から非負整数を 1 個受け取ります。全てのソート CLI と中央値 CLI は空白区切りの非負整数を 0 個以上受け取ります。数字に変換できない入力や、単一の数を要求するコマンドへ複数の値を渡した場合は、エラーを標準エラーに表示して終了コード 1 で終了します。

```sh
printf '10\n' | lake exe factorial
# 3628800

printf '360\n' | lake exe prime-factors
# 2 2 2 3 3 5

printf '100\n' | lake exe fibonacci
# 354224848179261915075

printf '9 1 4 2 7 3\n' | lake exe median
# 3.5

printf '9 1 4 2 7\n' | lake exe median
# 4

printf '7 2 5 2 0 9\n' | lake exe heapsort
# 0 2 2 5 7 9

printf '7 2 5 2 0 9\n' | lake exe heapsort-rec
# 0 2 2 5 7 9

printf '7 2 5 2 0 9\n' | lake exe mergesort
# 0 2 2 5 7 9

printf '7 2 5 2 0 9\n' | lake exe mergesort-loop
# 0 2 2 5 7 9

printf '7 2 5 2 0 9\n' | lake exe quicksort
# 0 2 2 5 7 9

printf '7 2 5 2 0 9\n' | lake exe quicksort-loop
# 0 2 2 5 7 9
```

ソート CLI はそれぞれ再帰版とループ版を用意しています。`heapsort`、`mergesort-loop`、`quicksort-loop` がループ版で、`heapsort-rec`、`mergesort`、`quicksort` が再帰版です。heap sort の再帰版は下降処理とヒープ構築・取り出しを再帰で行います。merge sort のループ版は隣り合う整列済み区間を反復的に併合します。quick sort のループ版は再帰呼び出しの代わりに明示的なタスクスタックを使います。

再帰版 quick sort とループ版 quick sort は、どちらも先頭要素を基準値にします。このため、すでに整列した入力などでは処理が偏り、再帰版の呼び出しが深くなったり、ループ版のスタックが大きくなったりすることがあります。

中央値は `lake exe median` で計算できます。標準入力の値を順に、下半分を保持する最大ヒープと上半分を保持する最小ヒープへ振り分けます。追加は `O(log n)`、追加後の中央値参照は `O(1)` です。要素数が偶数なら中央二値の平均を出力し、空入力では `none` を返します。

Fibonacci は高速倍加法を用い、添字を半分にして再帰するため再帰の深さは対数的です。素因数分解は試し割りを使い、因数を昇順かつ重複込みで返します。

## ソースの構成

- `Apps/`：各 CLI の入口。入力の読み取り、アルゴリズム呼び出し、結果の表示を担当します。
- `LeanExperiments/`：再利用できるアルゴリズムと共通処理を置きます。
- `LeanExperiments/Verification/`：仕様、補題、正しさの証明をアルゴリズムごとに置きます。

## 検証

`LeanExperiments/Verification/` に仕様、補題、証明、有限領域の回帰確認を置いています。quick sort・merge sort・heap sort は再帰版とループ版の両方について任意入力での一般正当性を証明済みです。ループ版 quick sort は状態不変条件と停止測度を用いて再帰版との一致を証明し、共通仕様 `Correct` に接続しています。各アルゴリズムの証明範囲、有限領域、未完了事項は[検証カタログ](docs/verification.md)を参照してください。

`LeanExperiments/Verification/` 以下のコードのほぼ全ては AI によって生成されています。証明が Lean に受理されることと、仕様や検証対象の選び方が適切であることは別なので、各証明の範囲と未完了事項は検証カタログで確認してください。GitHub Actions では Lean の全ターゲットをビルドし、公理依存を監査したうえで、CLI の入出力例も実行確認します。

## ライセンス

このリポジトリの内容は、[MIT License](LICENSE-MIT) または [Apache License 2.0](LICENSE-APACHE) のいずれかの条件で利用できます。依存ライブラリには、それぞれのライセンスが適用されます。
