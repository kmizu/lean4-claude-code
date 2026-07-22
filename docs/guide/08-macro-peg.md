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

## 8.6 Lens 抽出と差分ハーネス

`mpegRun` は `pegRun` と同型の燃料付き構造的再帰なので、抽出器 Lens の等式補題ルートは
新規の対応なしにそのまま通りました——ただし 1 点だけ既存のホワイトリストに引っかかりました。
アリティ検査を Prop の `≠`（`Decidable` 経由）で書くと、Lens のビルトイン表に
`instDecidableNot` が登録されておらず抽出が失敗します。`beqChar`/`leChar` と同じ流儀で
Bool の `==` を使うよう書き換えると通りました——`.chr`/`.range` が既にそうしているのと
同じパターンです。

差分ハーネスも既存の設計をそのまま踏襲しています。`shallot-cli macro-dump` サブコマンドが
抽出済み `MacroPeg_mpegRun` を、単一の `MacroPeg_mCases` テーブル（3 戦略ぶんの
witness をまとめて持つ）に対して実行し、`corpus/golden/macro_peg.jsonl`
（`CallByName` 8 件・`CallByValuePar` 3 件・`CallByValueSeq` 3 件、計 14 件）に
対して Lean ネイティブ実行 ≡ golden ≡ Scala 抽出実行の 3 方一致を `make verify` の
中で常時検査します。新しい戦略を足すたびに、この 3 方一致の仕組み自体には手を
入れていません——`Strategy` が増えても `MacroPeg_mCases` に行を足すだけです。

## 8.7 今回の範囲外にしたもの

- **高階関数レイヤー**（ラムダ `(x -> e)`・カリー化・第一級関数値）: 参照実装でも
  `Evaluator` のネイティブ機能ではなく、別ユーティリティ `MacroExpander` による
  「呼び出し前に全展開する」非停止性リスクのある構文的インライン化パス経由でしか
  動作しません（再帰マクロには使えない）。今回は「データ値としての式パラメータを
  取る再帰マクロ」という、macro_peg の見出しの表現力主張を支えている核——
  3 つの評価戦略すべて——を対象にしました

---

[← 7章 応用編: JSON](07-json.html) ｜ [目次](../index.html)
