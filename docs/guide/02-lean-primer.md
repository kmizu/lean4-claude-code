# 2. Lean 4 最小入門 — BNF 使いのための定理証明

[English](../en/02-lean-primer.html) | **日本語** ｜ [← 1章](01-intro.html) ｜ [目次](../index.html) ｜ [3章 →](03-peg-semantics.html)

この章では、本プロジェクトのコードを「読める」ようになるための最小限の Lean 4 を
紹介します。Lean を書けるようになる必要はありません。**BNF が読めるなら、この
プロジェクトの型定義は読めます。推論規則が読めるなら、意味論も読めます**——
それを確かめるのがこの章のゴールです。

## 2.1 `inductive` は BNF である

Lean の `inductive`（帰納型）はデータ型の定義です。パーサ屋の目にはこう映るはず：

```
PExp ::= eps | any | chr Char | range Char Char | lit String
       | nt Nat | seq PExp PExp | alt PExp PExp | star PExp | notP PExp
```

これを Lean で書くとこうなります（`lean/Shallot/Peg/Syntax.lean` から抜粋）：

```lean
inductive PExp where
  | eps
  | any
  | chr (c : Char)
  | range (lo hi : Char)
  | lit (s : List Char)
  | nt (i : Nat)
  | seq (e₁ e₂ : PExp)
  | alt (e₁ e₂ : PExp)
  | star (e : PExp)
  | notP (e : PExp)
```

`|` で選択肢を並べ、各選択肢（**コンストラクタ**と呼びます）が引数を持てる。
まさに BNF です。`seq` の引数に `PExp` 自身が現れる＝再帰的な文法定義、も
そのまま書けます。AST を定義する道具としては、ML 系言語の代数的データ型と
同じものだと思って差し支えありません。

## 2.2 `def` + `match` は再帰下降の関数

関数定義は `def`、場合分けは `match`（またはトップレベルのパターン節）。
誰でも一度は書いたことがある「先頭一致」関数を見てください：

```lean
/-- `stripPrefix? s input = some rest` iff `input = s ++ rest`. -/
def stripPrefix? : List Char → List Char → Option (List Char)
  | [], rest => some rest
  | _ :: _, [] => none
  | c :: cs, d :: ds => if beqChar c d then stripPrefix? cs ds else none
```

`Option` は「失敗するかもしれない計算」の型で、`some x` が成功、`none` が失敗。
Haskell の `Maybe`、Rust の `Option` と同じです。3 つの節はそれぞれ
「パターンが空なら残り全部を返す／入力が尽きたら失敗／先頭が一致したら再帰」。
再帰下降パーサの部品そのものですね。

1 点だけ Lean 特有の事情：**Lean の関数はすべて停止しなければなりません**。
`stripPrefix?` は再帰のたびに引数のリストが構造的に小さくなるので、Lean は
自動で停止を認めます。これが問題になるケースは 2.4 節で。

## 2.3 `inductive ... Prop` は推論規則である

ここが本章の山場です。Lean では**命題**（Prop）も帰納的に定義できます。
これが操作的意味論の推論規則を書く道具になります。3 章で主役になる `Derives` の
冒頭を先取りして見てみましょう：

```lean
inductive Derives (g : Grammar) : PExp → List Char → Outcome → Prop where
  | eps (input : List Char) :
      Derives g .eps input (.ok (.leaf []) input)
  | anyOk (c : Char) (rest : List Char) :
      Derives g .any (c :: rest) (.ok (.leaf [c]) rest)
  | anyFail :
      Derives g .any [] .fail
```

読み替え表はこうです：

| 論文の推論規則 | Lean の帰納的述語 |
|---|---|
| 規則の名前 | コンストラクタ名（`eps`, `anyOk`, …） |
| 横線の**上**（前提） | コンストラクタの引数（`h : ...` の形のもの） |
| 横線の**下**（結論） | コンストラクタの返り型 |
| 「導出木がある」 | この型の値が構成できる |

`anyOk` を論文風に書けば「（前提なし）───── any は c::rest から c を消費して成功」。
前提付きの規則は 3 章でたくさん出てきますが、読み方は同じです。

**文法を書くのと同じ道具（inductive）で、意味論が書ける**——ここが Lean の
気持ちよさです。しかも書いた規則は飾りではなく、「導出木」はプログラム中の
値として構成・分解でき、機械がその場合分けの網羅性を検査してくれます。

## 2.4 燃料付き再帰 — ハックではなく意味論の 3 値化

PEG のインタプリタは、左再帰する文法を与えられると停止しません。ところが Lean の
関数は停止必須。この緊張をどう解くか。答えは**燃料（fuel）**です：

```lean
def pegRun (g : Grammar) : Nat → PExp → List Char → Option Outcome
  | 0, _, _ => none
  | fuel + 1, e, input => ...  -- 再帰呼び出しはすべて fuel を使う
```

自然数の引数を 1 つ足し、再帰のたびに必ず 1 減らす。これで全ての再帰は構造的に
停止します。「実行ステップ数の上限付き実行」だと思ってください。

これを「停止性をごまかすハック」と感じた方にこそ強調したいのですが、
本プロジェクトでは fuel は**意味論上の三値化**として真面目に運用されています。
`pegRun` のファイルヘッダにある規約：

> `none` means "out of fuel" and NOTHING else; `some .fail` is a legitimate
> semantic outcome.

つまり返り値は「成功 `some (.ok ...)` ／意味論的失敗 `some .fail` ／燃料切れ
`none`」の 3 値で、**失敗と燃料切れを型レベルで区別**します。この区別のおかげで
定理の主張が濁りません：健全性は「`some` を返したなら正しい」、完全性は
「導出が存在するなら**十分な燃料で** `some` になる」。燃料は定理の中で
存在量化（∃ fuel）され、「単調性定理」（燃料を増やしても結果は変わらない）が
それを支えます。3 章で実物を見ます。

## 2.5 `theorem`・`sorry`・公理監査

**定理**は「型が命題で、値がその証明」という特別な定義です：

```lean
theorem pegRun_sound (h : pegRun g f e x = some o) : Derives g e x o := by
  ...
```

「`pegRun` が `some o` を返した」という仮定 `h` から「`Derives g e x o` の導出が
存在する」を作る関数、と読めます（証明 = プログラム）。`by` 以下に書くのは
タクティクと呼ばれる証明スクリプトですが、**読者は証明本体を読む必要はありません**。
主張（型）が読めれば、その定理が何を保証するかは全部わかります。Lean が
受理した時点で証明は正しい——それが定理証明支援系を使う意味です。

ただし 2 つ、「ズル」の可能性を知っておく必要があります。

**`sorry`**：Lean には「この証明はあとで書く」というプレースホルダがあります。
`sorry` と書けばどんな命題も「証明済み」としてコンパイルが通る——TODO コメントが
型検査を通ってしまう恐ろしい代物です。だから「sorry ゼロ」が検証プロジェクトの
最低ラインで、本リポジトリでは CI 相当のスクリプトがソース中の `sorry` を拒否します。

**公理**：`sorry` を消しても、勝手な公理を仮定していたら意味がありません。
Lean では任意の定理について「依存している公理の一覧」を機械的に問い合わせられます。
本リポジトリの `lean/Audit.lean` はそれを**スナップショットテスト**にしています：

```lean
/-- info: 'Shallot.derives_det' does not depend on any axioms -/
#guard_msgs in
#print axioms Shallot.derives_det
```

`#print axioms` が定理の公理依存を出力し、`#guard_msgs` が「その出力はこの
コメントと一字一句一致するはず」を検査します。一致しなければ**ビルドが落ちる**。
つまり `lake build`（Lean のビルドコマンド）が通った＝全定理の公理依存が
宣言通り、です。CI のスナップショットテストの発想がそのまま証明の世界に
持ち込まれている、と言えばエンジニアには通じるでしょうか。

なお Lean の標準的な公理は `propext`・`Classical.choice`・`Quot.sound` の 3 つで、
これは数学で普通に使う「標準装備」です（追加の信頼を要求するものではありません）。
本プロジェクトの定理はすべてこの 3 つ以下、上の `derives_det`（PEG の決定性）に
至っては**公理ゼロ**で証明されています。

## 2.6 これだけ知っていれば読める

まとめると、本プロジェクトのコードを読むのに必要な語彙は：

- `inductive` = BNF／代数的データ型
- `inductive ... Prop` = 推論規則の束。コンストラクタ引数が前提、返り型が結論
- `def` + パターン節 = 普通の関数。全域必須、危ういときは燃料
- `Option`/`Except` = 失敗しうる計算（`none` は本プロジェクトでは常に燃料切れ）
- `theorem` = 主張（型）だけ読めばよい。証明本体は機械のための脚注
- `sorry` ゼロ + 公理監査 = 「ズルをしていない」ことの機械的な保証

次章から、この語彙だけで PEG の形式意味論を読んでいきます。

---

[← 1章 イントロ](01-intro.html) ｜ [目次](../index.html) ｜ [3章 PEG の形式意味論 →](03-peg-semantics.html)
