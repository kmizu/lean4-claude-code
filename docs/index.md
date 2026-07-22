# Shallot + Lens 解説

[English](en/index.html) | **日本語**

**「このパーサは正しい」と言い切るとはどういうことか** — それを Lean 4 という
定理証明支援系で実際にやってみたプロジェクトの解説です。

対象読者は **PEG（Parsing Expression Grammar）はわかるが、Lean や定理証明には
詳しくない人**。パーサジェネレータを書いたことがある、Ford の論文を読んだことが
ある、くらいの人がいちばん楽しめるように書いています。

## 読み物（順番に読むのがおすすめ）

1. [イントロ — パーサが「正しい」とは何か](guide/01-intro.html)
2. [Lean 4 最小入門 — BNF 使いのための定理証明](guide/02-lean-primer.html)
3. [PEG の形式意味論 — Ford の意味論を Lean に写す](guide/03-peg-semantics.html)
4. [Shallot 言語 — 型検査器・インタプリタ・コンパイラの証明スタック](guide/04-shallot.html)
5. [Lens 抽出器 — 証明された Lean コードを Scala 3 にする](guide/05-lens.html)
6. [読みどころガイド — ソースコードの歩き方](guide/06-reading-guide.html)
7. [応用編 — 検証済み JSON パーサを作る](guide/07-json.html)
8. [応用編 — macro_peg の call-by-name 意味論を形式化する](guide/08-macro-peg.html)

## リファレンス

- [定理一覧（機械監査済み）](theorems.html)
- [抽出可能サブセットの仕様](extractable-subset.html)
- [開発ロードマップ（全マイルストーンの記録）](roadmap.html)
- [リポジトリ本体](https://github.com/kmizu/lean4-peg)

## 3行でいうと

- Shallot という小さな関数型言語の **パーサ・型検査器・インタプリタ・コンパイラを
  Lean 4 で書き、その正しさを `sorry`（証明の穴）ゼロで機械検証した**
- パーサは「検証済みの汎用 PEG インタプリタ + 文法データ」なので、PEG の
  健全性・完全性・決定性の定理が Shallot のパーサにそのまま適用される
- 検証した Lean コードを **自作の抽出器 Lens で Scala 3 に変換**し、
  Lean 側と Scala 側で同じ 60 ケースを実行して一致することを機械的に確認している
