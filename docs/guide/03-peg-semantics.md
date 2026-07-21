# 3. PEG の形式意味論 — Ford の意味論を Lean に写す

[English](../en/03-peg-semantics.html) | **日本語** ｜ [← 2章](02-lean-primer.html) ｜ [目次](../index.html) ｜ [4章 →](04-shallot.html)

この章が本連載の中核です。Ford (POPL 2004) の PEG 形式意味論を Lean の帰納的述語として
定式化し、燃料付きインタプリタがその意味論に対して**健全**・**完全**・**決定的**である
ことを証明します。PEG を知っている読者なら、この章のコードはほぼ全部読めるはずです。

## 3.1 復習：Ford の ⇒ 関係

Ford の論文では、解析式 e と入力に対して「e は入力の接頭辞を消費して成功する」か
「失敗する」かを、推論規則の集まりとして定義します。たとえば優先選択 e₁/e₂ なら：

- e₁ が成功すれば e₁/e₂ は e₁ の結果で成功する
- e₁ が**失敗し**、e₂ が成功すれば、e₂ の結果で成功する
- 両方失敗すれば失敗する

CFG の選択と違い、2 番目の規則には「e₁ が失敗した」という**前提が明示的に要る**——
これが PEG の曖昧性のなさの源泉でした。本プロジェクトの定式化はこの意味論に
**1 点だけ拡張**を加えています：成功の結果（outcome）に**構文木を積む**ことです。
これが後で決定性定理を「木の一意性込み」にしてくれます（3.5 節）。

## 3.2 データ型：PExp・PTree・Outcome

解析式はこう定義されています（`lean/Shallot/Peg/Syntax.lean`）。2 章で見た通り、
`inductive` は BNF だと思って読んでください：

```lean
inductive PExp where
  | eps                       -- ε
  | any                       -- 任意の1文字
  | chr (c : Char)            -- 文字リテラル
  | range (lo hi : Char)      -- 文字クラス [lo-hi]
  | lit (s : List Char)       -- 文字列リテラル（プリミティブ！）
  | nt (i : Nat)              -- 非終端記号（規則表への添字）
  | seq (e₁ e₂ : PExp)        -- 連接
  | alt (e₁ e₂ : PExp)        -- 優先選択 e₁ / e₂
  | star (e : PExp)           -- e*（Ford 忠実にプリミティブ）
  | notP (e : PExp)           -- 否定先読み !e
```

設計判断が 3 つ埋まっています。

**文字列リテラルはプリミティブ。** `lit "if"` を `chr 'i' ; chr 'f'` の連接に脱糖する
定式化も可能ですが、そうするとキーワード 1 個につき導出木のノードが文字数ぶん増えます。
後の roundtrip 証明（4 章）では「印字したテキストの導出を手で組み立てる」作業が
大量に発生するので、キーワード 1 個 = 導出 1 ノードにしておくことが証明コストに直結します。

**star はプリミティブ。** `e* = e e* / ε` と脱糖する手もありますが、Ford の原意味論に
star の規則があるので忠実に採りました。ε を消費する本体の star が停止しない問題は
「そういう導出は存在しない」という形で意味論側が自然に処理します（3.6 節）。

**非終端記号は Nat の添字。** 文法は規則の単なるリストで、範囲外の添字には
「明示的に失敗する」規則を与えます。これにより**文法の整形式性の仮定が定理から
一切消えます**——「well-formed な文法に対して…」という但し書きなしで、
すべての定理がすべての文法値について成り立ちます。

構文木と結果はこうです：

```lean
inductive PTree where
  | leaf (cs : List Char)       -- eps/any/chr/range/lit が消費した文字たち
  | nodeNT (i : Nat) (t : PTree)
  | seq (l r : PTree)
  | choiceL (t : PTree)         -- alt の左で成功
  | choiceR (t : PTree)         -- alt の右で成功
  | starNil
  | starCons (hd tl : PTree)    -- tl は star の残り全体の木
  | notT                        -- 否定先読みの成功

inductive Outcome where
  | fail
  | ok (t : PTree) (rest : List Char)
```

`PTree` は `PExp` の形をそのまま鏡写しにしています。「子のリストを持つノード」
（`List PTree`）を**あえて使っていない**のがポイントで、Lean ではリストを内包する
帰納型（入れ子帰納型）は帰納法の道具立てが急に扱いにくくなります。ミラー構造なら
すべての帰納法が素直に回ります。

また、入力位置は「残りの入力」（`List Char` の接尾辞）で表します。添字（何文字目か）を
使わないので、意味論にも証明にも添字演算が一切出てきません。

## 3.3 Derives：26 本の推論規則

意味論の本体は 3 引数の帰納的述語です。`Derives g e input o` は
「文法 g のもとで、式 e は入力 input に対して結果 o を導出する」と読みます。
代表的な規則を実コードから見てみましょう（`lean/Shallot/Peg/Semantics.lean`）：

```lean
  | chrOk (c d : Char) (rest : List Char) (h : beqChar c d = true) :
      Derives g (.chr c) (d :: rest) (.ok (.leaf [d]) rest)
  | chrFail (c d : Char) (rest : List Char) (h : beqChar c d = false) :
      Derives g (.chr c) (d :: rest) .fail
```

2 章の読み替え表そのままです：コンストラクタ名が規則名、引数の `h : ...` が前提
（横線の上）、返り型が結論（横線の下）。`beqChar c d = true` という **Bool の等式**を
前提にしているのは証明工学上の選択で、後で場合分けするときに「真のとき／偽のとき」が
機械的に反転できます。

優先選択の 3 規則が PEG らしさの核心です：

```lean
  | altL (e₁ e₂ : PExp) (input rest : List Char) (t : PTree)
      (h : Derives g e₁ input (.ok t rest)) :
      Derives g (.alt e₁ e₂) input (.ok (.choiceL t) rest)
  | altR (e₁ e₂ : PExp) (input rest : List Char) (t : PTree)
      (h₁ : Derives g e₁ input .fail)
      (h₂ : Derives g e₂ input (.ok t rest)) :
      Derives g (.alt e₁ e₂) input (.ok (.choiceR t) rest)
  | altFail (e₁ e₂ : PExp) (input : List Char)
      (h₁ : Derives g e₁ input .fail)
      (h₂ : Derives g e₂ input .fail) :
      Derives g (.alt e₁ e₂) input .fail
```

`altR` に注目してください。右側で成功するには **`h₁ : e₁ が失敗する導出`** を
差し出さなければいけません。CFG の選択なら「どちらかで成功すればよい」ところ、
PEG では失敗の証明が成功の前提になる——教科書で言葉として知っていた性質が、
規則の**引数**という物理的な形で現れています。

star と否定先読み：

```lean
  | starNil (e : PExp) (input : List Char)
      (h : Derives g e input .fail) :
      Derives g (.star e) input (.ok .starNil input)
  | starCons (e : PExp) (input rest rest' : List Char) (t ts : PTree)
      (h₁ : Derives g e input (.ok t rest))
      (h₂ : Derives g (.star e) rest (.ok ts rest')) :
      Derives g (.star e) input (.ok (.starCons t ts) rest')
  | notOk (e : PExp) (input rest : List Char) (t : PTree)
      (h : Derives g e input (.ok t rest)) :
      Derives g (.notP e) input .fail
  | notFail (e : PExp) (input : List Char)
      (h : Derives g e input .fail) :
      Derives g (.notP e) input (.ok .notT input)
```

star が止まるのは本体が**失敗した**とき（`starNil` の前提）だけ——greedy かつ
バックトラックしない、PEG の star の定義通りです。`notP` は結果を反転し、
入力を消費せず（結論の input がそのまま）、木は中身を持たない `notT` になります。
否定先読みの中で作られた木は外に漏れない、という直感の形式化です。

## 3.4 インタプリタ：燃料付き pegRun

意味論（Prop）は実行できないので、実行可能な関数を別に書きます
（`lean/Shallot/Peg/Interp.lean`）。優先選択と star の節を引用します：

```lean
    | .alt e₁ e₂ =>
      match pegRun g fuel e₁ input with
      | some (.ok t rest) => some (.ok (.choiceL t) rest)
      | some .fail =>
        match pegRun g fuel e₂ input with
        | some (.ok t rest) => some (.ok (.choiceR t) rest)
        | some .fail => some .fail
        | none => none
      | none => none
    | .star e =>
      match pegRun g fuel e input with
      | some (.ok t rest) =>
        match pegRun g fuel (.star e) rest with
        | some (.ok ts rest') => some (.ok (.starCons t ts) rest')
        | some .fail => some .fail -- 意味論上は到達不能（totality のために残す）
        | none => none
      | some .fail => some (.ok .starNil input)
      | none => none
```

規則と 1:1 に対応しているのが見て取れると思います。返り型は
`Option Outcome` で、規約は厳格に**「`none` は燃料切れ、それ以外の意味を持たない」**。
`some .fail` は正規の意味論的失敗です。この 3 値の区別が定理の主張を綺麗に保ちます
（「`some` を返したら正しい。`none` については何も言わない」）。

star の節に 1 箇所、「意味論上は到達不能」というコメント付きの分岐があります。
star は意味論上失敗しない（3.5 節の `starNeverFails`）ので、内側の star が
`some .fail` を返す分岐は実際には通りません。しかし Lean の関数は全域でなければ
ならないため、分岐自体は書いておき、証明側で「この枝には来ない」ことを示します。

## 3.5 4 つの定理

主張だけを実コードから引用します（証明はファイルにありますが、読む必要は
ありません——主張が読めれば定理は「使えます」）。

```lean
-- T0: 燃料単調性
theorem pegRun_mono (h : pegRun g f e x = some o) :
    pegRun g (f + 1) e x = some o

-- T1: 健全性 — インタプリタが返した結果（ok も fail も）は導出可能
theorem pegRun_sound (h : pegRun g f e x = some o) : Derives g e x o

-- T2: 決定性 — 導出結果は一意（構文木も込みで！）
theorem derives_det (h₁ : Derives g e x o₁) (h₂ : Derives g e x o₂) : o₁ = o₂

-- T3: 完全性 — 導出が存在するなら、ある燃料で計算できる
theorem pegRun_complete (h : Derives g e x o) : ∃ f, pegRun g f e x = some o
```

（付番はプロジェクトの定理一覧 [theorems.md](../theorems.html) に合わせています。
ソースファイルのヘッダコメントの一部に古い付番が残っていますが、内容は同一です。）

3 つ合わせると「`pegRun` は `Derives` の完全な実装である」——
`pegRun g f e x = some o` ↔ `Derives g e x o`（→ が T1、← が T3、
結果が食い違わないことが T2）。インタプリタと意味論のあいだに隙間はありません。

**T2 が木の一意性を含む**ことに注目してください。`Outcome.ok` が構文木を
運んでいるので、「結果が等しい」＝「消費量も木も等しい」です。PEG は曖昧でない、
とよく言われますが、この定式化ではそれが `o₁ = o₂` という 1 本の等式に
畳み込まれています。設計（outcome に木を積む）が定理を安くした例です。
ちなみに T2 は**公理を一切使わずに**証明されています（`#print axioms` の
出力が「does not depend on any axioms」になります——2 章参照）。

証明の雰囲気だけ、プロジェクトでいちばん短い定理でお見せします：

```lean
/-- A star never fails: the only `Derives` rules concluding at a `.star`
expression are `starNil` and `starCons`, and both produce `.ok`. -/
theorem starNeverFails {g : Grammar} {e : PExp} {input : List Char} {o : Outcome}
    (h : Derives g (.star e) input o) : o ≠ .fail := by
  intro hf
  subst hf
  cases h
```

「star の導出だと仮定して（h）、結果が fail だと仮定すると（intro hf, subst hf）、
star を結論とする規則は starNil と starCons しかなく、どちらも ok を作るので、
fail を作る場合分けは**空**（cases h が全ケースを閉じる）」。3 行です。
帰納的述語のケース分析は、規則の一覧表を機械が照合してくれる作業なのです。

## 3.6 正直なスコープ：左再帰と全域性

T3 は「**導出が存在するなら**計算できる」であって、「すべての文法が停止する」
ではありません。ここは正直に書いておくべきポイントです。

左再帰する文法（規則 0 が `nt 0` 自身を先頭に参照する等）を考えると、
`Derives` の規則をどう組み合わせても有限の導出木が作れません——`ntOk` の前提が
また同じ `nt 0` の導出を要求し、無限後退するからです。つまり**導出が存在しない**。
このときインタプリタは燃料を使い果たして `none` を返しますが、それは T1〜T3 の
どの主張にも反しません（3 定理はすべて `some` の場合について語っている）。

TRX（Coq による PEG の先行形式化）は整形式性解析を定式化して全域性まで証明する
道を取りましたが、本プロジェクトは「燃料 + 導出存在に相対的な完全性」という
軽量な定式化を選びました。文法の整形式性仮定なしで全定理が成り立つ、という
3.2 節の性質はこの選択の恩恵です。左再帰サポート（Warth らのパッカラット拡張など）を
形式化したい人には、この `Derives` がちょうどよい出発点になるはずです。

## この章の持ち帰り

**outcome に構文木を積むという設計の一手が、決定性定理を「木の一意性込み」に
してくれた。** 仕様の書き方（データ型の設計）が、後の定理の強さと証明の安さを
決めます。形式化とは、証明を書く前の設計勝負でもあるのです。

---

[← 2章 Lean 最小入門](02-lean-primer.html) ｜ [目次](../index.html) ｜ [4章 Shallot 言語 →](04-shallot.html)
