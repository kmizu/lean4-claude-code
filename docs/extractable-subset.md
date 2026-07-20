# 抽出可能サブセット（凍結: M9）

Lens が Scala 3 へ抽出できる Lean 4 コードの契約。違反は**必ず fail-loud**
（宣言名・フェーズ・対象項つきエラーで抽出全体が中断、ファイルは一切書かれない）。

## 使えるもの

- **inductive / structure**: 添字なし、Prop フィールドなし。mutual ブロック可。
  型パラメータ可（Scala ジェネリクスへ）。
- **def**: 構造的再帰・燃料再帰・整礎再帰（等式補題ルート経由で直接再帰に戻る）、
  相互再帰、prefix 位置の型多相。`match`（ネスト可、Nat の succ 連鎖は
  ガード付き case へ平坦化）。`if`（whitelisted な Decidable インスタンスのみ）。
- **プリミティブ型**: `Nat`/`Int` → `BigInt`（Nat 減算は 0 切り詰め、
  div/mod-by-zero は 0 / 恒等、**Int の `/` `%` はユークリッド除算**）、
  `Bool` → `Boolean`、`String` → `String`（コードポイント正確なブリッジ）、
  `Char` → `BigInt`（Unicode スカラー値。Scala `Char` は UTF-16 単位なので不使用）、
  `List`/`Option`/`Prod`/`Except` → `List`/`Option`/`Tuple2`/`Either`。
- **演算**: 四則・比較・`++`（String/List）・`==`（プリミティブ）・`Nat.repr`/
  `Int.repr`・`String.toList`・`Char.toNat`。すべて**正準 core インスタンス限定**
  （カスタムインスタンスは fail-loud）。

## 使えないもの（fail-loud）

- `partial def` / `unsafe` / 公理 / `opaque`
- 添字付き inductive、Prop を運ぶコンストラクタ（`Subtype`/`Fin`/`Decidable` 内包データ）
- whitelisted 以外の typeclass 経由コード（自作型の等価性は手書き `beq` を使う）
- non-prefix の型多相、部分適用されたコンストラクタ（v5 以降の課題）
- `do` 記法（明示 `match` で書く。`Except` の連鎖はネスト match ✓）

## TCB（信頼ベース）と検証の分担

抽出器・手書きランタイム（`shallot.rt`）・Scala コンパイラ・JVM は**信頼**。
Lean 内の定理が保証するのは Lean レベルの意味論。両者の橋渡しは
`corpus/golden/all.jsonl` の差分ハーネス（Lean ネイティブ実行 ≡ 抽出 Scala 実行）
が経験的に検査する。ケーステーブル自体が抽出されるため、レンダラや評価器の
ドリフトは即座に差分として現れる。

## LCNF フォールバックについて（設計判断）

当初計画にあった `Lean.Compiler.LCNF` ベースのフォールバック抽出は**実装していない**。
理由: 等式補題ルートが本プロジェクトの全宣言（PEG インタプリタ・型検査器・
インタプリタ・VM・RBMap を含む 27 ルートの推移閉包）を 100% カバーし、
フォールバックの主目的だった `partial def` はサブセットから排除済みのため。
将来、等式ルートで扱えない宣言が現れた時点で再検討する。
