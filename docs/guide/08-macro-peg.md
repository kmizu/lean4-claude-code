# 8. 応用編 — macro_peg の評価戦略を形式化する

[English](../en/08-macro-peg.html) | **日本語** ｜ [← 7章](07-json.html) ｜ [目次](../index.html)

7 章は「検証済みの汎用 `pegRun` に文法値を渡すだけで定理が付いてくる」という 1 章の構図を、
JSON という実用フォーマットで再確認する話でした。この章は逆に、**その構図が壊れる場所**を
扱います。[kmizu/macro_peg](https://github.com/kmizu/macro_peg) は PEG を
「パラメータ付き規則」で拡張したライブラリで、パラメータという新しい構文要素が入る以上、
既存の `PExp`/`Derives`/`pegRun` をそのまま使い回すことはできません。何が変わり、何が
変わらないかを追うのがこの章の主題です。

## 8.1 参照実装を読む：3 つの評価戦略と `extract()`

macro_peg の `Evaluator.scala` を読むと、マクロ呼び出しの実引数の扱いに 3 つの戦略が
あることが分かります（`EvaluationStrategy.scala`）。デフォルトの `CallByName` は実引数を
**評価せず構文のまま**渡す真の call-by-name。`CallByValueSeq`/`CallByValuePar` は入力を
消費しながら実引数を先に評価し、消費した部分文字列を値として渡す——2 つの間でも「逐次消費」
と「同一位置での先読み抽出」という違いがあります。README の見出しの主張（回文やコピー言語
`{ww}` を認識できる、というPEGを超える表現力の話）を裏付けるテストは全て `CallByName` の
例です。この章はまず `CallByName` から形式化を始め（8.1〜8.4）、その後 `Strategy`
パラメータで `MDerives`/`mpegRun` を一般化して残り 2 戦略を追加します（8.5）——
最終的に 3 戦略すべてを形式化しています。

`CallByName` の実装は環境スレッディング方式で、`bindings : Map[Symbol, Expression]` に
規則名とパラメータ名を同居させています。ここで目を引くのが `extract()` という関数です。
マクロ呼び出し `P(w "a")` を評価するとき、実引数 `w "a"` の中の自由変数 `w` を、**呼び出し
時点の bindings で先に閉じてから**新しい束縛として渡す——これをやらないと、再帰呼び出しの
たびに `w` という同じ名前が指す意味がずれてしまいます（名前衝突／変数捕獲）。手製の衛生化
コードが要るのは、パラメータを**名前**で表現し、グローバルな規則名と同じ名前空間に同居させて
いるからです。

## 8.2 de Bruijn 化——`extract()` がまるごと不要になる

Lean 側は、既存 `PExp.nt` が非終端記号を `Nat` インデックスで指すのと同じ流儀を、パラメータ
参照にも適用しました。`.param k` は「現在アクティブな規則の第 k 実引数」を指す 1 段だけの
de Bruijn インデックスです（`lean/MacroPeg/Syntax.lean:56`）。macro_peg の核（高階関数レイヤーを
除いた範囲）では規則本体がネストしない——ラムダがない——ため、de Bruijn の段数はこの 1 段で
足ります。

```lean
inductive MExp where
  ...
  | param (k : Nat)
  | call (i : Nat) (args : List MExp)
  ...
```

すると置換 `MExp.subst` は、名前も環境も要らない、ただの構造的な書き換えになります
（`lean/MacroPeg/Syntax.lean:110-133`）。範囲外の `.param k` 参照（アリティと矛盾する
不正な規則——`call` 側でアリティ検査済みなので実際には起こらない）は、新しい AST
コンストラクタを増やすことなく、既存コンストラクタから作れる恒偽式 `.notP .eps` に落とします
（`lean/MacroPeg/Syntax.lean:82`）——これは 3 章で確立した「整形式性仮定ゼロ」（欠番非終端
記号は明示の失敗規則を持つ）の自然な延長です。**この 1 段の de Bruijn 化だけで、`extract()`
相当の手製衛生化コードが一切不要になり、単純な置換だけで capture-free になります。** 参照実装
との比較で見えてくる、地味だけれど本質的な差分です。

## 8.3 新しい `Derives` を作る——JSON との対比

7 章の JSON は、既存の `PExp`/`Derives`/`pegRun` を**そのまま**再利用できる例でした。
macro_peg はそうはいきません。`.param`/`.call`（引数付き）という `PExp` にない構文が要る
以上、**新しい AST・新しい `Derives`・新しいインタプリタ**を持つ独立モジュール
`lean/MacroPeg/` が必要になります（Lean の inductive に部分型付き拡張という概念はないので、
これは型としての「拡張」ではなく、同じ設計原則を踏襲した並行実装です）。

`MDerives`（`lean/MacroPeg/Semantics.lean:35`）は `eps`/`any`/`chr`/`range`/`lit`/`seq`/
`alt`/`star`/`notP` の 9 規則を `Derives` から一字一句写し取り、新規に 6 規則を足します：

- `dbg`（:60）: `Debug(e)` は `e` を評価せず無条件成功——参照実装の no-op をそのまま反映
- `paramFail`（:62）: 生の `.param k` は無条件失敗。`call` の置換で必ず消えているはずなので
  実際には到達しませんが、健全性がすべての `MExp` について言える必要がある以上、総称
  インタプリタの死んだ分岐（`star` の内側 `some .fail` と同じ流儀）と対称的に、`MDerives`
  側にもこの規則が要ります
- `callOk`/`callFail`（:64, :69）: 規則 `i` を引き、宣言アリティと実引数の個数が一致する
  ことを前提に、`MExp.subst args r.body`（置換**済み**の本体）から導出する。**実引数はここでは
  評価されません**——これが call-by-name の核心です
- `callMissing`/`callArity`（:74, :77）: 欠番規則・アリティ不一致は前提なしの明示失敗規則

`mpegRun`（`lean/MacroPeg/Interp.lean:21`）は `pegRun` と同じ燃料付き構造的再帰。`.call`
ケースは `.nt` ケースと同型（規則を引き、燃料を 1 消費して置換後の本体へ再帰）で、`.param`
ケース（:43）は上で触れた「到達しないが総称性のために要る」死んだ分岐です。

証明の型は転用できました。T0-T3（燃料単調性・接尾辞不変・健全性・決定性・完全性）の
証明手法そのものは「燃料についての強い帰納法、各段で任意の式に対する帰納法の仮定」という
形——`.nt` ケースが参照先の式にも同じ仮定を要求する時点で、既に `pegRun`/`Derives` の
証明はこの形をしていました。`call` ケースはただ `subst args r.body` という「別の式」に
同じ仮定を当てはめるだけで済み、新規性はゼロでした。

## 8.4 headline 定理：コピー言語を全称量化で証明する

`NonTrivialLanguagesSpec.scala` にある、非文脈自由言語の教科書的 witness——コピー言語
`{ww | w ∈ {a,b}*}`——を認識する文法がこちらです：

```
Copy(w) = "a" Copy(w "a") / "b" Copy(w "b") / w
```

Scala のテストスイートはこの文法が `"aa"`・`"bb"`・`"abab"` 等の有限個の文字列を正しく
受理し、`"ab"`・`"aba"` 等を正しく拒否することを確認しています。証明で書けるのはその先
——**すべての** `u ∈ {a,b}*` について成り立つことです：

```lean
theorem copy_language_ww (u : List Char) (hu : ∀ c ∈ u, c = 'a' ∨ c = 'b') :
    ∃ t, MDerives copyGrammar (.call copyIdx [.lit []]) (u ++ u) (.ok t [])
```

（`lean/MacroPeg/Examples.lean:326`）。有限個のテストケースではなく、`{a,b}*` 上のすべての
`u` について。

### 蓄積引数はけっして平坦にならない

自然な証明戦略は `u` についての帰納法です。ところが `Copy` の再帰呼び出しの実引数
`w "a"` は call-by-name のため**評価されず構文のまま**渡ります——Lean の項で言えば
`.seq (.param 0) (.chr 'a')`。1 段再帰するたびに、次のアクティブ化の `.param 0` は
平坦な `.lit` ではなく `.seq` ノードに束縛され、2 段目、3 段目と左に伸びるネストした
`.seq` の連鎖になっていきます。つまり「アキュムレータは `.lit w` である」という形の
帰納法は成立しません。

そこで挟んだのが `ExactMatch`——「`wexp` は `.lit w` と挙動的に同一」という不変条件です
（`lean/MacroPeg/Examples.lean:108`）：

```lean
structure ExactMatch (wexp : MExp) (w : List Char) : Prop where
  succ : ∀ rest, ∃ t, MDerives copyGrammar wexp (w ++ rest) (.ok t rest)
  fail : ∀ z, (∀ p, z ≠ w ++ p) → MDerives copyGrammar wexp z .fail
```

`exactMatch_step`（:120）が「`wexp` が `w` に厳密一致するなら `.seq wexp (.chr c)` は
`w ++ [c]` に厳密一致する」という保存則を示し、これで `Copy` の再帰呼び出しを跨いでも
帰納法が回るようになります。参照実装が `extract()` で解いていた「呼び出しごとに実引数の
構文が変わる」という同じ現象に、証明の側でも向き合う必要があった、というのがこの節の
オチです。

### 書いてみて気づいた 2 つの穴

最初のドラフトには本物の論理的な穴が 2 つありました。

1つ目は**アルファベット制限の欠落**。`Copy` の文法は `'a'`/`'b'` の分岐しか持たないので、
`u` に他の文字が混ざっていたら `copy_language_ww` は成り立ちません。定理の主張に
`(hu : ∀ c ∈ u, c = 'a' ∨ c = 'b')` を足す必要がありました——証明を書く前は当たり前に
見えた「すべての `u`」が、実際に書いてみると暗黙の前提を要求してきた例です。

2つ目は、それを埋めるために必要になった補題 `copy_fail_short`
（`lean/MacroPeg/Examples.lean:154`）：

```lean
theorem copy_fail_short {wexp : MExp} {w : List Char} (hm : ExactMatch wexp w) :
    ∀ z : List Char, z.length < w.length →
      MDerives copyGrammar (.call copyIdx [wexp]) z .fail
```

`copy_gen`（帰納法の本体、:225）の基底ケースでは、`Copy(w)` を長さちょうど `|w|` の入力に
当てたとき、2 つの「伸びる」分岐（`'a'`/`'b'` を読んで再帰する側）が両方とも失敗し、
3 番目の分岐（`wexp` 自身にマッチ）だけが残ることを示す必要があります。1 文字消費した後の
残り入力は長さ `|w|-1`、しかし再帰先の `Copy` は `|w|+1` の文字列に対する呼び出しなので、
**入力が短すぎて原理的に成功しえない**——この「短すぎたら失敗する」という事実は、文字の
中身に関する議論を一切必要としない、純粋に長さだけの議論です。この補題が抜けていることに
気づいたのも、証明を実際に最後まで書こうとして初めてでした。

このプロジェクトでは sepOkB（4 章）や大文字 `E`（7 章）のように、証明を書く過程で仕様の
穴が見つかる場面が何度もありました。今回はその変奏で、**穴が見つかったのが実装の欠陥では
なく、定理の主張そのものの甘さ**だった点が少し違います。全称量化の定理を書くという行為
自体が、「本当にすべての `u` について成り立つか」を突き詰めて考えさせた、という言い方も
できます。

## 8.5 `Strategy` を通す — `CallByValuePar` と `CallByValueSeq`

ここまでは `CallByName` 専用の `MDerives`/`mpegRun` でした。残り 2 戦略を足すには、
署名そのものを変更する破壊的な retrofit が要ります——Lean の `inductive`/`mutual` は
「1 箇所で全コンストラクタを宣言」を要求するので、新しい `call` 規則を後から生やす
という選択肢がありません。`MDerives (g : MGrammar) : ...` は
`MDerives (g : MGrammar) (s : Strategy) : ...` になり、T0-T3 の証明済み定理も含め
`MacroPeg/` 以下のほぼ全ファイルを書き直すことになります。

```lean
inductive Strategy where
  | callByName
  | callByValuePar
  | callByValueSeq
  deriving DecidableEq
```

既存 15 規則は `s` を素通しするだけ（戦略が効くのは `.call` だけ）。`callOk`/`callFail`
は `hs : s = .callByName` を前提に足した `callNameOk`/`callNameFail` に改名し、
2 つの戦略それぞれに新しい補助関係と 3 本ずつのコンストラクタ（正常終了・本体失敗・
実引数失敗）を追加します。

`CallByValuePar`（実引数を**同一の入力位置**に対して独立に評価する、バックリファレンス
風の戦略）には `DerivesArgsPar` を追加：

```lean
inductive DerivesArgsPar (g : MGrammar) (s : Strategy) (input : List Char) :
    List MExp → List MExp → Prop where
  | nil : DerivesArgsPar g s input [] []
  | cons (a : MExp) (as : List MExp) (p rest : List Char) (t : MTree) (vs : List MExp)
      (h1 : MDerives g s a input (.ok t rest))
      (hp : input = p ++ rest)
      (h2 : DerivesArgsPar g s input as vs) :
      DerivesArgsPar g s input (a :: as) (.lit p :: vs)
```

`input` が全実引数を通じて固定されている——各実引数は独立に、同じ開始位置から評価
されます。対して `CallByValueSeq`（実引数を**左から順に**評価し、消費した入力位置を
次の実引数へスレッディングする戦略）の `DerivesArgsSeq` は `input` の代わりに
`final`（全実引数を評価し終えた最終位置）を運びます：

```lean
inductive DerivesArgsSeq (g : MGrammar) (s : Strategy) :
    List Char → List MExp → List MExp → List Char → Prop where
  | nil (input : List Char) : DerivesArgsSeq g s input [] [] input
  | cons (a : MExp) (as : List MExp) (input p rest final : List Char) (t : MTree) (vs : List MExp)
      (h1 : MDerives g s a input (.ok t rest))
      (hp : input = p ++ rest)
      (h2 : DerivesArgsSeq g s rest as vs final) :
      DerivesArgsSeq g s input (a :: as) (.lit p :: vs) final
```

`cons` の再帰が次の実引数を `rest`（今の実引数が消費した残り）に対して評価している点が
`DerivesArgsPar` との唯一だが本質的な違いです。`CallByValueSeq` 側の呼び出し規則
`callSeqOk` は、規則本体をこの `final`（`DerivesArgsSeq` の呼び出し記法では `mid`）
から導出します——`CallByValuePar` の `callParOk` が本体を常に**元の** `input` から
導出するのとは対照的です。

### 「実引数のどれかが失敗したら呼び出し全体が失敗する」を正しく書く

`callParArgFail`（実引数のどれかが失敗したときに呼び出し全体を失敗させる規則）の
最初のドラフトは、`badArg ∈ args`（リストのどこかに失敗する実引数がある）としか
要求しておらず、`badArg` より前の実引数の成否を一切制約していませんでした。完全性
（T3）を証明しようとしたエージェントが、この規則が**参照実装の左から右への短絡評価と
矛盾する**ことを機械的に発見しました——`badArg` より前に非停止な実引数があると、
導出は存在するのに `mpegRun` はどの燃料でも決してその `.fail` を実現できない（`none`
を返し続ける）反例が構築できてしまうのです。`sorry` で誤魔化す代わりに、証明可能な
disproof を添えて報告され、修正されました：

```lean
| callParArgFail (i : Nat) (pre : List MExp) (badArg : MExp) (post : List MExp) (r : MRule)
    (input : List Char) (preVals : List MExp)
    (hs : s = .callByValuePar)
    (hr : ruleAtM g.rules i = some r)
    (ha : r.arity = (pre ++ badArg :: post).length)
    (hpre : DerivesArgsPar g s input pre preVals)
    (hfail : MDerives g s badArg input .fail) :
    MDerives g s (.call i (pre ++ badArg :: post)) input .fail
```

`args = pre ++ badArg :: post` という明示的な分割と、`hpre : DerivesArgsPar g s input
pre preVals`（`badArg` より前がすべて成功している証拠）を要求することで、
`evalArgsPar` の左から右への短絡評価と正確に対応するようになりました。

このバグを踏んだあとに書いた `CallByValueSeq` 側の `callSeqArgFail` は、同じ罠を
先回りで回避しています——最初から `pre ++ badArg :: post` ＋
`hpre : DerivesArgsSeq g s input pre preVals mid`（`badArg` より前がすべて成功し、
かつ `mid` までスレッディング済みである証拠）という正しい形で書かれ、完全性の証明で
作り直す手戻りは発生しませんでした。sepOkB（4 章）・大文字 `E`（7 章）・`{a,b}*`
制限（8.4）に続き、このプロジェクトで何度も見てきた「証明を書いて初めて仕様の穴が
見つかる」パターンの一例であると同時に、**一度見つけた穴を次の設計に明文化して
再発を防げた**という珍しい例でもあります。

### P1 が `CallByValueSeq` で非自明になる

P1（`mderives_suffix`：成功した導出は入力の接頭辞を消費する）の証明はミューチュアル
帰納法 `MDerives.rec` で `motive_2`（`DerivesArgsPar` 用）・`motive_3`
（`DerivesArgsSeq` 用）を要求します。`CallByValuePar` の全コンストラクタは
「本体の副次導出が入力を消費する」という `CallByName` と同じ議論に還元できるので、
`motive_2` は自明な `True` で済みました。ところが `callSeqOk` は本体を実引数評価の
**最終スレッディング位置** `mid` から導出するため、その副次導出からは
`mid = p ++ rest` しか得られません。`input = _ ++ rest` を回復するには、
「実引数の逐次評価自体が `input` から `mid` までの接頭辞を消費した」という事実が
別途必要で、これは `DerivesArgsSeq` の各 `cons` ステップが持つ `hp : input = p ++
rest` から組み立てられます。そこで `motive_3` を `∃ q, input = q ++ final` という
非自明な述語にし、帰納法の仮定として運びました。同じ「実引数の補助関係」でも、
位置をスレッディングするかどうかで証明に要求される情報量が変わる、という例です。

T0-T3 の証明手法そのもの（燃料についての強い帰納法／導出構造についてのミューチュアル
帰納法）は `CallByName` の段階で確立したものがそのまま転用できました。新規性が
あったのは、ここで見た 2 点——「実引数が 1 つでも失敗したら呼び出し全体が失敗する」
規則の正しい形と、位置のスレッディングが証明に要求する情報の違い——に集約されます。

## 8.6 高階関数レイヤーの一部を形式化する——そして旧スコープ判断の誤りに気づく

ここまでの節（と、この章の以前の版・`docs/roadmap.md`）は、macro_peg の高階関数
レイヤー（ラムダ・名前付きルールを値として渡す機能）を丸ごとスコープ外にしていました。
理由として書いていたのは「参照実装の `Evaluator` でもネイティブ機能ではなく、別
ユーティリティ `MacroExpander`（呼び出し前にグラマ全体を展開する、非停止性リスクの
ある構文的インライン化パス）経由でしか動かない」——**この理解は不正確でした。**

### 参照実装を読み直して分かったこと

高階関数レイヤーに実際に着手する段になって、`Evaluator.scala`/`MacroExpander.scala`/
`Parser.scala` を改めて精読し、`sbt console` で実機検証しました。分かったのは：

- `Evaluator.scala` は `FUNS`（各ルール名を `Function` 値に変換したマップ）と
  `bindings` を素通しする形で、「パラメータに束縛された callable（名前付きルール
  参照でもラムダリテラルでも）を、その場で呼び出す」を**ネイティブに**サポートして
  いました。`MacroExpander.expandGrammar` を一切経由せず `Evaluator` だけを直接
  呼んでも、出荷テストスイートの高階関数テスト 6 件全てが同一の結果を返すことを
  確認しました
- `MacroExpander` が本当に必須なのは、「あるルール呼び出しがクロージャを**戻り値**
  として返し、それを**別の**呼び出し元で改めて適用する」という、真の環境捕獲を
  伴うパターンだけでした。このパターンは AST 上は書けますが、出荷テストスイートに
  1 件も存在しません。自作したテスト（`MakeAdder(x: ?) = (y -> x y); UseCurried(f:
  ?, y: ?) = f(y);` のような、クロージャを返して別の場所で使う形）で確認したところ、
  `MacroExpander` なしでは `ClassCastException` で確実にクラッシュします
- 「カリー化」を謳うテスト（`Curry(f: ?) = (x -> (y -> f(x, y)))` を
  `Curry((x,y->x y))("a")("b")` として呼ぶもの）は、実は名前負けしていました。
  `Call` の構文が `識別子(引数)` の形しか持たない（`Parser.scala`）ため、呼び出し
  結果への連続適用という構文自体が存在せず、`Curry(...)` はラムダ値のゼロ幅
  マッチとして即座に成功し、残りの `("a")("b")` はただの文字列リテラルの並びとして
  シーケンスされているだけでした——実際にはカリー化も適用も一切起きていません

つまり「渡された callable を、同じ呼び出しツリーの中で即座に呼ぶ」というパターン
だけなら、非停止性リスクなしにネイティブに形式化できる——これが今回の M-PEG-4
マイルストーンの出発点です。

### `.lam` / `.callParam` / `.invoke`

このプロジェクトには `.peg` 構文解析器がなく、`Examples.lean` で `MExp` を直接
Lean の項として組み立てます。そのため「名前付きルールを値として渡す」と「ラムダ
リテラルを渡す」は、区別する必要すらありません——どちらも同じ `.lam arity body`
という形に帰着します：

```lean
| lam (arity : Nat) (body : MExp)
| callParam (k : Nat) (args : List MExp)
| invoke (arity : Nat) (body : MExp) (args : List MExp)
```

`.lam` は callable な値で、`.dbg` と同じ「無条件ゼロ幅成功」として評価されます
（値は入力を消費しない）。`body` の中の `.param` はラムダ自身のスコープを指し、
外側のルールの `.param` とは無関係——出荷テストのラムダリテラルは全て自己完結
（自由変数によるキャプチャなし）だったので、`subst` は `.lam` を `.lit` と同じ
「葉」として扱い、中へは再帰しません。これがキャプチャなしを構造的に保証します。

`.callParam k args` は「現在のルールの第 k 実引数に束縛された callable を、
この `args` で呼ぶ」という構文で、`Examples.lean` が直接書く形です。`subst` が
必ずこれを解決します：`.param k` の位置に `.lam ar bod` があれば
`.invoke ar bod (substした args)` に書き換え、それ以外（型が合わない・範囲外）
なら既存の `.param` アウトオブレンジと同じ `MExp.failAlways` に潰します。

`.invoke` は `.call` とほぼ同型ですが、グローバルなルール表から `body`/`arity`
を引くのではなく、既に手元にある値をそのまま使います。**実装しながら気づいた
設計の訂正**があります：当初のプランは「`.invoke` はどの `Strategy` でも同じ
1 規則で済む」でしたが、これは「1 つの導出は 1 つの `Strategy` にコミットする」
という既存の不変条件（`s` は導出全体を通じて固定）と矛盾します。渡された
callable 経由の呼び出しも、名前付きルール経由の呼び出しと同じ規約で実引数を
扱うべきです。`.call` と同じ 3-way（`invokeNameOk`/`Fail`、`invokeParOk`/
`Fail`/`ArgFail`、`invokeSeqOk`/`Fail`/`ArgFail`、`invokeArity`）に設計し直し、
既存の `DerivesArgsPar`/`DerivesArgsSeq`/`evalArgsPar`/`evalArgsSeq` をそのまま
再利用しました——新しい補助関係は不要でした。

### `CallByValuePar`/`CallByValueSeq` 下のラムダ引数は、退化挙動を忠実に再現する

参照実装ではラムダ値は「入力を消費しないゼロ幅マッチ」として評価されるため、
`CallByValuePar`/`CallByValueSeq` 下でラムダを実引数に渡すと、実引数評価が
ゼロ幅マッチして消費文字列（空）が値として束縛され、**ラムダの中身が丸ごと
消えて空文字列と区別つかなくなります**。この組み合わせは出荷テストに 1 つも
存在しない、事実上未定義の退化挙動です。

今回は、参照実装と食い違う「賢い」新仕様を作らず、この退化を忠実に再現する
判断にしました。`.lam` を `.dbg` と同じ「無条件ゼロ幅成功」規則 1 本だけにし、
`evalArgsPar`/`evalArgsSeq` には一切手を入れていません。退化した値
（`.lit []`）を後から `.callParam`/`.invoke` で「呼ぼう」とすると、既存の
「整形式性仮定ゼロ」哲学（`.param` アウトオブレンジと同じ扱い）に従って自動的に
失敗します——特別なケース分けは一切不要でした。

### T0-T3 の拡張とスモークテスト

証明ファイル（`Fuel`/`Props`/`Soundness`/`Determinism`/`Completeness`）への
拡張は、`.invoke` の各ケースが `.call` の対応ケースとほぼ同型だったため、
機械的に進みました。`invokeParArgFail`/`invokeSeqArgFail` は、M-PEG-2 の
`callParArgFail` が完全性証明の途中で発見した不健全性（`args = pre ++ badArg
:: post` ＋ `pre` 成功の明示証拠が必要という教訓）を最初から設計に組み込んで
おいたため、今回は手戻りが発生しませんでした。

`Examples.lean` には 2 種類のスモークテストを追加しました——名前付きルール
参照のパターン（`Double(Plus1, "aa")` 相当：`Double(f,s) = f(f(s))` で
`"aa"` を 2 回倍化して `"aaaaaaaa"` に一致）と、多引数ラムダリテラルの
パターン（`Map2((x,y -> x y x), "a", "b")` 相当：`"a" ++ "b" ++ "a"` =
`"aba"` に一致）です。どちらも `#guard` が一発で通り、手で追った導出が
正しかったことを裏付けました。

## 8.7 Lens 抽出と差分ハーネス

`mpegRun` は `pegRun` と同型の燃料付き構造的再帰なので、抽出器 Lens の等式補題ルートは
新規の対応なしにそのまま通りました——ただし 1 点だけ既存のホワイトリストに引っかかりました。
アリティ検査を Prop の `≠`（`Decidable` 経由）で書くと、Lens のビルトイン表に
`instDecidableNot` が登録されておらず抽出が失敗します。`beqChar`/`leChar` と同じ流儀で
Bool の `==` を使うよう書き換えると通りました——`.chr`/`.range` が既にそうしているのと
同じパターンです（`.invoke` のアリティ検査にも同じパターンをそのまま適用しています）。

差分ハーネスも既存の設計をそのまま踏襲しています。`shallot-cli macro-dump` サブコマンドが
抽出済み `MacroPeg_mpegRun` を、単一の `MacroPeg_mCases` テーブル（全戦略・全機能ぶんの
witness をまとめて持つ）に対して実行し、`corpus/golden/macro_peg.jsonl`
（`CallByName` 8 件・`CallByValuePar` 3 件・`CallByValueSeq` 3 件・高階関数 6 件、
計 20 件）に対して Lean ネイティブ実行 ≡ golden ≡ Scala 抽出実行の 3 方一致を
`make verify` の中で常時検査します。新しい機能を足すたびに、この 3 方一致の仕組み
自体には手を入れていません——コンストラクタが増えても `MacroPeg_mCases` に行を
足すだけです。

## 8.8 今回の範囲外にしたもの

- **クロージャの戻り値適用**（真の環境捕獲）: あるルール呼び出しがクロージャを
  戻り値として返し、それを**別の**呼び出し元で改めて適用するパターン。AST 上は
  書けますが、参照実装でもこれを動かすには `MacroExpander`（呼び出し前に全展開
  する、非停止性リスクのある構文的インライン化パス、自己再帰する規則には使えない）
  が必須で、出荷テストスイートに 1 件もこのパターンのテストが存在しません
  （8.6 で実機確認済み。ただし「クラッシュする」という当時の結論は 8.9 で訂正して
  います）。それ以外の高階関数の使い方——渡された callable を同じ呼び出しツリー
  の中で即座に呼ぶパターン——はこの章ですべて形式化しました

## 8.9 もう一つの訂正——クロージャ戻り値パターンは実は形式化済みだった

次のマイルストーン（M-PEG-5）を検討する過程で、8.6/8.8 に書いた「クロージャの
戻り値適用は `MacroExpander` なしでは `ClassCastException` でクラッシュする」
という記述を、参照実装の再検証で覆すことになりました。

`Baz(f: ?) = f; Apply(f: ?, s: ?) = f(s); S = Apply(Baz((x -> x)), "a")` を
`sbt console` で `Evaluator` だけを使って直接評価したところ、クラッシュせず、
決定的に `Failure` を返しました。そもそも `Interpreter` クラスは `MacroExpander`
を一度も呼んでいません（「`MacroExpander` を `Interpreter` の内部に隠す」という
コミット名の実装が、実は `MacroExpander` を呼んでいなかった、というのも今回
分かったことの一つです）。

これは実は `.callParam` の `subst`（`MacroPeg/Syntax.lean`）が最初から正しく
持っていた挙動でした。`CallByName` の下で `Apply` の `f` に束縛されるのは
`Baz(...)` という未評価の `.call` 式であって `.lam` ではないので、`.callParam`
は既存のフォールバックで `MExp.failAlways` に落ちます。新しいコンストラクタも
新しい証明ルールも要らず、`Examples.lean`/`Corpus.lean` にこの事実を確認する
スモークテスト（corpus ID `335-mpeg-hof-return-reject-a`）を 1 件追加しただけです。

つまり M-PEG-4 は、当初考えていたよりも広い範囲を最初から正しく形式化できて
いました。本当に未形式化のまま残っているのは、`MacroExpander` の全展開が実際に
**成功させる**ケース——マクロ呼び出しのグラフが非循環なら安全に停止する——であり、
これが M-PEG-5 の対象です。

## 8.10 M-PEG-5——非循環グラフの上を歩く

`MacroExpander.expandGrammar` は、マクロ呼び出しを構文的に片っ端からインライン
展開していくだけの、素朴なパスです。`Baz`/`Apply` のような非再帰的なマクロなら
これで問題なく `Success` に変わりますが、`Rec(n: ?) = "a" Rec(n)` のような、
普通に評価すれば何の問題もなく止まるごく平凡な（左再帰ですらない）規則に対しては、
自分自身を無限にインライン展開し続けて絶対に止まりません。実機で 60 秒以上
ハングすることも確認済みです。M-PEG-5 はこの`expandGrammar`を、「パラメータ付き
ルールの呼び出しグラフが非循環である」という整形式性条件のもとで形式化し、
この条件下では必ず停止することを証明するマイルストーンです。

### `rank` を停止性の尺度に直接使う

このプロジェクトの他の関数はすべて「fuel が尽きたら諦める」という単純な戦略で
停止性を確保してきました。M-PEG-5 ではあえてそれを選ばず、非循環グラフから
導かれる「順位（rank）」——各ルールについて「自分が呼ぶ先の中で一番順位が高い
ものより 1 大きい」という、DFS で計算する自然数——を`termination_by`の停止性尺度
そのものとして使うことにしました。狙いは、フォールバック（fuel で単に打ち切る
だけの安全策）に頼らず、「非循環性が本当に停止を保証する」という主張を字義通り
証明することです。

核心の定理は`rank_lt_of_acyclic`：非循環なグラフでは、ルール`i`がルール`j`を
呼んでいれば`rank j < rank i`が必ず成り立つ、というものです。この証明は
2 つの単調性補題に分解できました。1 つは「fuel を増やしても既に成功した結果は
変わらない」という補題（`Fuel.lean`の`mpegRun_mono`がそのままテンプレートになる、
低リスクな部分）。もう 1 つは「`visiting`集合を小さくしても成功しやすくなる
だけで、値も大きくならない」という補題——これがこのプロジェクト初のグラフ理論で、
前例が一切ない、設計時点で「一番転びやすい」と名指しされていた箇所でした。

実際にはこの直感は正しく、証明も通りました。ただし一発では通らず、2 回の設計
転換を経ています。1 回目は`foldl`を`foldr`に変えたこと——`cons`の展開が
`max x (xs.foldr max 0)`という形に直接効くようにするためで、`foldl`のままだと
「初期値をどちらに積むか」の順序の違いに証明が振り回されました。2 回目は
`List.contains`まわりの補題名で行き詰まった末に、`argAt`と同じ流儀の自前
`natElem`関数に切り替えたことです——`if`分岐の形にしておくと`simp`/`split`との
相性が段違いに良くなりました。

ちょっとした副産物として、ダイヤモンド型の依存関係（`A`が`B`と`C`を呼び、
`B`と`C`が両方`D`を呼ぶ）でも、`visiting`ベースの循環検知が誤検知を起こさない
ことを`#eval`で確認できました。`D`は 2 つの経路から独立に（再計算はされますが）
同じ順位に到達し、これは「共有された子孫」と「本物のサイクル」を正しく
区別できている証拠です。

### T-fix——代入は「呼び出しなし」を保存する

`expand`が本当に`MacroExpander`の謳う不動点（「呼び出しが一切残らない」）に
到達することも証明しました（`expand_hasCall_eq_false`）。証明のほとんどは
機械的でしたが、`.call i (a::as)`のケース——展開済みの本体と展開済みの実引数を
`MExp.subst`で合流させる箇所——だけは、新しい補題を要求してきました。「両方とも
呼び出しなしなら、代入した結果も呼び出しなし」という事実（`subst_hasCall_eq_false`）
です。これは`MExp.subst`/`substArgs`自体の構造に沿った、独立のmutual帰納法で
証明しました。既存の構造をなぞるだけなので機械的ではありますが、証明義務として
は本物で、省略できませんでした。

### `decide`が詰まる、という Lean 4 のあるある

具体的な文法（`closureReturnGrammar`）が非循環であることを、`MExp.expand`に
実際に渡す証明項として構成する必要がある箇所で、`by decide`や`by rfl`が
kernel簡約で行き詰まる、という現象に遭遇しました。`rankGo`/`rankSuccs`が
well-founded再帰として実装されている以上、kernelの`whnf`簡約では最後まで
簡約しきれないことがある——という、Lean 4ではそこそこ知られた現象です。
面白いのは、`#eval`や`#guard`（コンパイル評価を使う）は何の問題もなく動く
ことで、実際にヘッドラインの`#guard`はこれで無事に通っています。証明項が
どうしても必要な箇所（`Examples.lean`の`closureReturnAcyclic`）だけ、
関連する等式補題を全部並べた`by simp [...]`で計算を書き換えベースで駆動する
ことで解決しました。

### ヘッドライン：`"fail"`が`"ok+0"`に変わる

`Examples.lean`にこの一行が加わりました：

```lean
#guard renderMPeg
  (mpegRun closureReturnGrammar .callByName 200
    (MExp.expand closureReturnGrammar closureReturnAcyclic
      (.call closureReturnApplyIdx
        [.call closureReturnBazIdx [.lam 1 (.param 0)], .lit ['a']]))
    "a".toList) == "ok+0"
```

M-PEG-4/8.9 節でずっと`"fail"`だった同じ式が、`expand`を一段挟むだけで
`"ok+0"`に変わります。閉包が呼び出し境界を越えて本当に動くようになった、
これが今回の実質的な成果です。

### 抽出器のもう一つの発見

`expand`/`expandGrammar`自体は等式補題ルート経由で無事に抽出できましたが、
`Corpus.lean`のような呼び出し側から`acyclicB g = true`の具体的な証明項を
実引数として渡そうとすると、抽出器が「theorem leaked into executable code」
とfail-loudに拒否することが分かりました。`Lens/Translate.lean`の`sigParams`
は関数の**定義**側でProp引数を消去する仕組みは持っていますが、その関数を
**呼び出す側**でProp引数を消去する仕組みはまだ実装されていなかったのです。
関数定義自体の抽出可能性と、その呼び出し箇所の抽出可能性は別問題だった、
という発見でした。このため Scala 側の実参照との突き合わせは、自動化された
corpus diff ではなく、このプロジェクトを通して何度も使ってきた`sbt console`
による実機の一回限りの検証——`Baz`/`Apply`は実際に`Success`になること、
`Rec(n)`は実際に 60 秒以上ハングすることの両方を、`MacroExpander.expandGrammar`
自体に対して直接確認する——で代替しました。

---

[← 7章 応用編: JSON](07-json.html) ｜ [目次](../index.html)
