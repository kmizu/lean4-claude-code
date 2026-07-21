# 6. 読みどころガイド — ソースコードの歩き方

[English](../en/06-reading-guide.html) | **日本語** ｜ [← 5章](05-lens.html) ｜ [目次](../index.html)

最後に、[リポジトリ](https://github.com/kmizu/lean4-claude-code)を自分で
歩きたい人のための地図を置いておきます。

## 6.1 地図

```
lean/
├── Shallot/
│   ├── Peg/        # 汎用PEG: Syntax → Semantics → Interp → 定理4ファイル
│   ├── Syntax/     # Shallot具象構文: Grammar(文法値) / Printer / TreeToAst
│   │               #   / Lexemes / RoundtripExpr / Roundtrip(roundtrip証明3層)
│   ├── Lang/       # AST / Typing / TypeCheck(+Verify) / Eval / TypeSound
│   ├── Opt/        # 定数畳み込み + 保存定理
│   ├── Vm/         # スタックVM: Machine / Compile / Correct(正しさ証明)
│   └── Data/       # 赤黒木: RBMap / RBVerify / RBBalance
├── Lens/           # 抽出器: Translate / Equations / Matcher分解 / Printer …
└── Audit.lean      # 全フラッグシップ定理の公理監査（#guard_msgs）
scala/
├── runtime/        # 手書きプレリュード（TCB）
├── generated/      # Lens の出力（コミット済み・ドリフト検査つき）
└── shallot-cli/    # CLI + ScalaCheck プロパティ
corpus/             # 差分ハーネスの golden（60ケース）
docs/theorems.md    # 定理一覧（この解説の索引としても使える）
```

規模感：Lean 約 11,800 行（うち証明 約 8,000 行）、抽出器 約 4,000 行、
生成 Scala 約 1,300 行。

## 6.2 3 つの読書コース

**(i) PEG だけ 30 分コース。** `Peg/Syntax.lean` → `Peg/Semantics.lean` →
`Peg/Interp.lean` の順で読む（3 章の内容の原典）。定理 4 ファイル
（`Fuel` / `Soundness` / `Determinism` / `Completeness`）は**ヘッダの
docstring と theorem の主張行だけ**読めば十分です。

**(ii) 定理踏破コース。** [docs/theorems.md](../theorems.html) を索引に、
`lean/Audit.lean` を開く。そこに並ぶ `#print axioms` の対象が全フラッグ
シップ定理なので、名前で各ファイルに跳んで主張を読む。証明本体は
読まなくてよい——**主張と docstring が本文、証明は機械のための脚注**です。
（RoundtripExpr.lean は 1,700 行ありますが、読むべきは最後の定理主張だけです。）

**(iii) 手を動かすコース。** リポジトリの README の手順で環境を作り、
`make verify` を走らせる。fail-fast の順に：

```make
verify: audit lean lake-test check-drift scala diff
```

`audit`（ソースに sorry 等がないか）→ `lean`（`lake build` = **全証明の
再検査＋公理監査**）→ `lake-test`（抽出器のゴールデン）→ `check-drift`
（コミット済み生成コードが再抽出と一致するか）→ `scala`（sbt テスト）→
`diff`（60 ケースの Lean ≡ Scala 突き合わせ）。何が「検証されている」のかを、
検証のパイプラインそのものが説明してくれます。

その後は `sbt "shallotCli/run run ../examples/collatz.shl"` あたりで、
証明済みスタックが実際に動くのを眺めてください。

## 6.3 ヘッダ docstring は設計メモである

この連載の引用の多くが、実はソースファイルの**ヘッダコメント**でした。
このリポジトリでは、各ファイルの冒頭 docstring に「なぜこの設計にしたか」
「何を主張し、何を主張しないか」が書いてあります。`Peg/Interp.lean` の
燃料規約、`Syntax/Roundtrip.lean` の境界条件の顛末、`Lens/Builtins.lean` の
手監査宣言——**ヘッダだけ拾い読みする**のが、このコードベースのいちばん
効率的な歩き方です。

## 6.4 さらに先へ

- **Ford, "Parsing Expression Grammars" (POPL 2004)** — 本プロジェクトの
  `Derives` の原典。読み直すと、規則が 1 本ずつ Lean に写っているのが
  わかるはずです
- **Theorem Proving in Lean 4**（Lean 公式チュートリアル）— 2 章の続きを
  ちゃんとやりたくなったら
- **[docs/roadmap.md](../roadmap.html)** — 本プロジェクトの全マイルストーンの
  記録。抽出器のバグを敵対的レビューで 17 件洗い出した話や、コンパイラ
  正しさ証明の設計変更など、開発の航海日誌として
- 左再帰 PEG（Warth らのパッカラット拡張）の形式化、優先順位を保った
  pretty-printer の roundtrip など、**この土台の上でやれる未踏の題材**は
  たくさん残っています。`Derives` はそのための出発点として設計されています

## 最後に

このリポジトリでは、`lake build` が通ること自体が査読です。どこから信じて
読み始めればいいか迷ったら、答えは 1 ファイル——`lean/Audit.lean`——に
集約されています。楽しんでください。

---

[← 5章 Lens 抽出器](05-lens.html) ｜ [目次](../index.html) ｜ [7章 応用編: JSON →](07-json.html)
