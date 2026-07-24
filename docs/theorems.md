# 定理一覧（機械監査済み）

すべて `lean/Audit.lean` の `#guard_msgs in #print axioms` でビルド時に公理集合が
検証される。許容公理は Lean 標準の `propext` / `Classical.choice` / `Quot.sound` のみ
（多くはそれ以下）。`sorry` はリポジトリに存在しない（`scripts/audit-source.sh` が
ソースレベルでも拒否する）。

## PEG フレームワーク（M4）

| 定理 | 内容 | 公理 |
|------|------|------|
| `pegRun_mono` / `_le` (T0) | 燃料単調性 | propext |
| `derives_suffix` (P1) | 成功導出は接頭辞を消費する | propext |
| `pegRun_sound` (T1) | インタプリタの ok / fail 結果はすべて導出可能 | propext |
| `derives_det` (T2) | 導出結果は一意（**構文木込み**） | **公理ゼロ** |
| `pegRun_complete` (T3) | すべての導出は有限燃料で計算される | propext |

正直なスコープ: 完全性は「導出の存在」に相対的（左再帰・ε本体 star には導出が
存在せず、インタプリタは `none` を返す。文法整形式性の仮定は一切なし——欠番
非終端記号は明示の失敗規則を持つ）。

## 赤黒木マップ（M6）

| 定理 | 内容 |
|------|------|
| `cmpStr_*`（29補題, R5） | cmpStr は狭義全順序（String/Char の外延性なしで証明） |
| `RBNode.ordered_insert` (R1) | 挿入は BST 不変条件を保存 |
| `RBNode.find_insert` (R3) | find/insert のモデル定理 |
| `RBNode.find_fromList` (R6) | テーブル検索 ≡ 連想リスト検索（L5/V2 の橋） |
| `RBBalance.rb_insert` (R2) | 挿入は赤黒平衡を保存（Okasaki、フル強度） |

## 型検査器（M6）

| 定理 | 内容 |
|------|------|
| `typecheck_sound` (L1) | 検査器 ok ⇒ 型付け関係が成立 |
| `typecheck_complete` (L2) | 型付け関係 ⇒ 検査器 ok |
| `checkProgram_sound` / `_complete` (L3) | プログラムレベル ⇔ `WTProg` |

## インタプリタ・最適化器（M8）

| 定理 | 内容 |
|------|------|
| `eval_mono` / `_le` (L4) | インタプリタ燃料単調性 |
| `optExpr_hasType` (O1) | 定数畳み込みは型を保存 |
| `optExpr_eval` (O2) | 定数畳み込みは評価結果を保存（同一燃料） |
| `eval_sound` / `runProgram_sound` (L5) | **well-typed ⇒ stuck しない**（divByZero のみ許容、stuck系エラーは証明済み不在） |
| `optProgram_run` (O3) | プログラム全体の畳み込みが結果を保存（最適化テーブル対応の再帰納） |

## コンパイラ・VM（M10）

| 定理 | 内容 |
|------|------|
| `vmRun_mono` / append 合成 / テーブル橋 (V0) | VM 基盤（naive な append 成功形は**偽**——bind/unbind が locals を動かす。反例発見の上、誤差なしの形で証明） |
| `compile_sim_cont` / `compile_sim` (V1) | **継続渡し形式の前進シミュレーション**（コンパイル済みコードの bind/unbind 平衡性を利用、call ケース込みフルスコープ） |
| `compile_correct` (V2) | **`runProgram` が値 v で成功 ⇒ `vmRunProgram` も同じ v で成功** |

## パーサ roundtrip（M11）

| 定理 | 内容 |
|------|------|
| RT-L1（`digitsVal_natDigits`・`keyword_guard_fails`・`derives_ident`・`derives_number` ほか） | 字句層の導出構築キット＋復元 |
| RT-L2 `derives_printExpr`（1705行） | 式層: 正準印字はパーズされ AST が復元される（tier登り＋fail-cascade） |
| RT-L3 `derives_printProgram`（1471行） | プログラム層 roundtrip: `treeToAst t = .ok p` |
| `parse_print` | **`parseShallot`（検証済み PEG パーサ）が正準印字から p を復元**（十分燃料すべてで） |
| `pipeline_correct` | **合成定理**: 正準印字はパーズで p に戻り、p は well-typed、評価値は型正しく、コンパイル済み VM も同値を計算 |

既知の正準形制約（`printableProgB` 仮定に集約）:
- `eqB` は `eqI` と同一の `"=="` に印字されるため正準印字不能
- 負リテラルは `( - digits )` に印字され、`treeToAst` が正規化して戻す
- **分離ガード `sepOkB`**: 最後の関数本体が裸の変数かつ main が `'('` 始まりの
  組み合わせは除外——この形では PEG の優先選択 `Call / Ident` が関数境界を越えて
  `x ( 1 + 2 )` を関数呼び出しとして貪り、パーズが壊れる。**roundtrip 証明の過程で
  発見された本物の文法境界条件**（実パーサへの反例で検証済み。テストコーパスでは
  未検出やった——形式検証が仕様の穴を見つけた実例）。

## 検証済み JSON パーサ（J シリーズ、RFC 8259）

| 定理 | 内容 |
|------|------|
| T1-T3 の継承 | パーサ＝検証済み `pegRun` ＋ `jsonGrammar`（ABNF 1:1 対応表つき）なので健全性・木込み決定性・完全性が自動適用 |
| J3 字句キット | `hexListVal_hex4`（\uXXXX の逆関数）、`combineUnits_map_toNat`（サロゲート合成）、`escapeCp_cases`（エスケープ4分岐 ⇔ 解析形の1:1対応） |
| `derives_printJson` / `parse_print_json` (J-RT) | **正準印字の完全 roundtrip**: `wfValue v → parseJson (printJson v) = .ok v`（十分な燃料すべてで）。仮定は数値の桁形状のみ——**文字列は無条件** |

経験的裏付け: nst/JSONTestSuite で y\_（必須受理）違反 0・n\_（必須拒否）違反 0、
i\_（実装定義）は lone surrogate 拒否方針どおり。抽出 Scala 版は 318 ファイル
全件で Lean 側と判定同一（不正 UTF-8 の扱い込み）。`make verify` に常設。

## Macro PEG（M-PEG / M-PEG-2 / M-PEG-3 / M-PEG-4 / M-PEG-5）: kmizu/macro_peg の意味論

`MExp`（`.param k` = 現在の規則活性化の第 k 実引数、`.call i args` = 規則 i 呼び出し）
と、それに対する新しい導出関係 `MDerives` / インタプリタ `mpegRun` を独立モジュール
`MacroPeg/` として形式化。既存 `PExp`/`Derives`/`pegRun` の型としての拡張ではなく
（Lean の inductive に部分型付き拡張はない）、同じ設計原則（Nat インデックス、
整形式性仮定ゼロ、fuel 総称インタプリタ）を踏襲する並行実装。M-PEG（`CallByName`
のみ）の後続として、M-PEG-2 で `Strategy`（`.callByName` / `.callByValuePar`）
パラメータを `MDerives`/`mpegRun` に通し、`CallByValuePar`（実引数を同一位置で
独立評価するバックリファレンス風の戦略）を追加。M-PEG-3 で `Strategy` に
`.callByValueSeq` を加え、`CallByValueSeq`（実引数を左から順に評価し、消費した
入力位置を次の引数へスレッディングし、規則本体はその最終位置から始まる戦略）を
形式化。さらに M-PEG-4 で高階関数レイヤーの一部——`.lam`（callable な値、名前付き
ルール参照とラムダリテラルを統一表現）・`.callParam`（束縛された callable の呼び出し）・
`.invoke`（`subst` が `.callParam` を解決した後の形）——を追加した。いずれも既存
ファイルへの retrofit であり、既存の定理・headline定理も含めすべて再検証済み。

| 定理 | 内容 | 公理 |
|------|------|------|
| `mpegRun_mono` / `_le` (T0) | 燃料単調性 | propext, Quot.sound |
| `mderives_suffix` (P1) | 成功導出は接頭辞を消費する | propext |
| `mpegRun_sound` (T1) | インタプリタの ok / fail 結果はすべて導出可能 | propext, Classical.choice, Quot.sound |
| `mderives_det` (T2) | 導出結果は一意（構文木込み） | propext, Quot.sound |
| `mpegRun_complete` (T3) | すべての導出は有限燃料で計算される | propext, Quot.sound |
| `copy_language_ww` | **headline**（`CallByName`）: コピー言語 `{ww \| w ∈ {a,b}*}`（非文脈自由の教科書的 witness）を `Copy(w) = "a" Copy(w "a") / "b" Copy(w "b") / w` が `{a,b}*` 上の**すべての** `u` について認識することを証明（Scala テストスイートは有限個の witness しか確認できないが、証明は全称量化） | propext, Classical.choice, Quot.sound |

設計判断（`MacroPeg/Syntax.lean`/`Semantics.lean` のヘッダに詳細）:
- **de Bruijn 化で `extract()` が不要になる**: 参照実装（Scala `Evaluator`）は
  パラメータを名前で表現し、`extract()` という手製の変数捕獲回避関数を必要とする。
  Lean 側はパラメータを「現在の規則活性化の第 k 引数」という 1 段の de Bruijn
  インデックスで表現し、単純な構造的置換 `MExp.subst` だけで capture-free になる
- **スコープ**: `CallByName`＋`CallByValuePar`＋`CallByValueSeq`（macro_peg の
  三戦略すべて）と、高階関数レイヤーの「渡された callable を同じ呼び出しツリーの
  中で即座に呼ぶ」部分（名前付きルール参照・ラムダリテラルの両方）を形式化。
  **この境界線は当初の理解が不正確だった**——`docs/roadmap.md` に旧版が残る通り、
  以前は「高階関数は参照実装の `Evaluator` でもネイティブ機能ではなく、別ユーティリティ
  `MacroExpander`（非停止性リスクのある構文的インライン化パス）経由でしか動かない」
  としてまるごとスコープ外にしていた。M-PEG-4着手時に参照実装（`Evaluator.scala`/
  `MacroExpander.scala`/`Parser.scala`）を実機検証（`sbt console` で `MacroExpander`
  を経由せず`Evaluator`だけを実行）した結果、これは誤りで、`Evaluator` は
  `FUNS`/`bindings` を素通しする形で「渡された callable をその場で呼ぶ」を
  **ネイティブに**サポートしていると判明した。`MacroExpander` が必須なのは
  「クロージャを戻り値として返し、別の呼び出し元で改めて適用する」（真の環境捕獲）
  の場合のみで、これは出荷テストに1件も存在しない。今回形式化したのはネイティブに
  サポートされている前者のみ——後者（クロージャの戻り値適用）は非停止性リスクを
  抱えたまま今回もスコープ外
- **`callParArgFail` は証明が見つけた本物の設計バグだった**:
  `CallByValuePar` の「実引数のどれかが失敗したら呼び出し全体が失敗する」という
  規則の最初のドラフトは、`badArg ∈ args`（リストのどこかに失敗する引数がある）
  としか要求しておらず、`callParArgFail` より前の引数の成否を一切制約していなかった。
  完全性（T3）を証明しようとしたエージェントが、この規則が**参照実装の左から右への
  短絡評価と矛盾する**ことを機械的に発見した——`badArg` より前に非停止な引数が
  あると、導出は存在するのに `mpegRun` はどの燃料でも決してその `.fail` を実現
  できない（`none` を返し続ける）反例を構築し、`sorry` の代わりに証明可能な
  disproof を残して報告した。修正: `callParArgFail` に `args = pre ++ badArg :: post`
  という明示的な分割と `hpre : DerivesArgsPar g s input pre preVals`（`badArg` より
  前がすべて成功している証拠）を追加。これで `evalArgsPar` の左から右への
  短絡評価と正確に対応するようになり、T3 は sorry ゼロで通った
- **`callSeqArgFail` は同じ罠を先回りで回避した**: M-PEG-3 の設計時点で
  `callParArgFail` の教訓（前の実引数の成否を制約しないと不健全になる）を
  プロンプトに明示したため、`callSeqArgFail` は最初から `args = pre ++ badArg :: post`
  ＋ `hpre : DerivesArgsSeq g s input pre preVals mid`（`badArg` より前がすべて
  成功し、かつ `mid` までスレッディング済みである証拠）という正しい形で書かれ、
  T3 で作り直す手戻りは発生しなかった
- **P1（`mderives_suffix`）は `CallByValueSeq` で `motive_3` が非自明になった**:
  `CallByValuePar` の Par 系ケースは全て「本体の副次導出 `hd` が入力を消費する」
  という `CallByName` と同じ議論に還元でき、`DerivesArgsPar` についての帰納法の
  仮定（`motive_2`）は使われないので `True` で済んだ。ところが `callSeqOk` は本体
  を「実引数評価が消費し終えた最終位置 `mid`」から導出するため、`hd` からは
  `mid = p ++ rest` しか出ず、`input = _ ++ rest` を得るには「実引数の逐次評価
  自体が `input` から `mid` までの接頭辞を消費した」という事実が別途要る。これは
  `DerivesArgsSeq` の各 `cons` ステップが持つ `hp : input = p ++ rest` から直接
  組み立てられるので、`motive_3` を `∃ q, input = q ++ final` という非自明な述語
  にして帰納法の仮定として運ぶ形にした——同じ「引数の補助関係」でも、位置を
  スレッディングするかどうかで証明に要求される情報量が変わる好例
- **`.invoke` は当初「strategy 非依存」で設計したが、実装しながら誤りに気づいた**:
  最初のプラン（コウタ承認済み）は「`.invoke` はどの `Strategy` でも同じ1規則で
  済む」だったが、実際に `Semantics.lean` を書く段になって、これは「1つの導出は
  1つの `Strategy` にコミットする」という既存の不変条件（`s` は導出全体で固定）
  と矛盾すると気づいた——渡された callable 経由の呼び出しも、名前付きルール
  経由の呼び出しと同じ規約で実引数を扱うべきである。`.call` と同じ3-way
  （`invokeName*`/`invokePar*`/`invokeSeq*`）に設計し直し、既存の
  `DerivesArgsPar`/`DerivesArgsSeq`/`evalArgsPar`/`evalArgsSeq` をそのまま
  再利用した（新しい補助関係は不要——「どの `MExp` リストを評価するか」しか
  気にしない設計だったので、呼び出し元が `.call` か `.invoke` かは無関係だった）
- **`CallByValuePar`/`CallByValueSeq` 下のラムダ引数は、参照実装の退化挙動を
  忠実に再現する設計にした**: 参照実装ではラムダ値は「入力を消費しないゼロ幅
  マッチ」として評価されるため、Par/Seq 下でラムダを実引数に渡すと、実引数評価が
  ゼロ幅マッチして消費文字列（空）が `.lit []` として束縛され、ラムダの中身が
  丸ごと消えてしまう——この組み合わせは出荷テストに1つも存在しない、事実上
  未定義の退化挙動である。今回は参照実装と食い違う「賢い」新仕様を作らず、この
  退化を忠実に再現した：`.lam` は `.dbg` と同じ「無条件ゼロ幅成功」規則1本のみで、
  `evalArgsPar`/`evalArgsSeq` には一切手を入れていない。結果として、退化した
  `.lit []` を `.callParam`/`.invoke` で「呼ぼう」とすると、既存の
  「整形式性仮定ゼロ」哲学（`.param` アウトオブレンジと同じ扱い）に従って
  自動的に失敗する——特別なケース分けが一切不要だった
- **`copy_gen` の一般化**: 帰納法は `u` に対して行うが、`Copy` の再帰呼び出しの実引数
  `w "a"` は call-by-name のため評価されず構文木のまま渡る（`.lit` に平坦化されない）。
  よって「アキュムレータは `.lit w` である」という形の帰納法は成立せず、`ExactMatch`
  （「`.lit w` と挙動的に同一」という不変条件）を経由した一般化が必要だった
- **`{a,b}*` への制限は書いてみて気づいた**: 文法が `'a'`/`'b'` の分岐しか持たない以上
  `copy_language_ww` は無条件の `∀ u` では偽——最初のドラフトはこの仮定を欠いていて、
  補う過程で「`Copy(v)` は `|z| < |v|` な入力には失敗する」（`copy_fail_short`）という
  補題が要ることも判明した。証明を書く前は自明に見えた命題が、実際に書いてみると
  暗黙の前提（アルファベット制限・長さ下界）を要求してくる——このプロジェクトで
  何度も見た形の発見がここでも起きた
- **「クロージャの戻り値適用」は実は M-PEG-4 の範囲内だった（M-PEG-5 検討時に判明）**:
  上のスコープ記述は「参照実装でも `MacroExpander` なしでは `ClassCastException` で
  クラッシュする」としていたが、`Evaluator.scala`/`Interpreter.scala` を実機再検証
  （`sbt console`）したところ、これは不正確だった——`Interpreter` はそもそも
  `MacroExpander` を一切呼ばず、この構成（`Baz(f: ?) = f; Apply(f: ?, s: ?) = f(s);
  S = Apply(Baz((x -> x)), "a")`）はクラッシュせず、決定的に `Failure` を返す。
  これは `.callParam` の `subst` が既に持っている「解決先が `.lam` でなければ
  `MExp.failAlways`」というフォールバック（`MacroPeg/Syntax.lean`）とそのまま一致する
  ——`CallByName` の下で `Apply` の `f` に束縛されるのは `Baz(...)` という未評価の
  `.call` 式であって `.lam` ではないため。新しい `MExp` コンストラクタも新しい証明も
  不要で、`Examples.lean`/`Corpus.lean` の `closureReturnGrammar`（corpus ID
  `335-mpeg-hof-return-reject-a`）が計算による確認として追加されている。真に
  未形式化のまま残るのは、`MacroExpander` の全展開が実際に成功させるケース（後述）
  だけ

## M-PEG-5: 非循環マクロ展開（`CallGraph.lean` / `Expand.lean`）

`MacroExpander.expandGrammar`（構文的インライン展開）を、パラメータ付きルールの
呼び出しグラフが非循環という整形式性条件のもとで形式化し、この条件下で必ず停止
することを証明した。全体で新しい `MExp` コンストラクタは追加していない
（`expand`/`expandGrammar` は既存 `MExp`/`MGrammar` に対する外部の変換関数）。

| 定理 | 内容 | 公理 |
|------|------|------|
| `rank_lt_of_acyclic` | `acyclicB g = true` かつ `j ∈ g.calls i` なら `rank g j < rank g i`（非循環グラフ上の辺越しの厳密な順位低下） | propext |
| `expand_hasCall_eq_false` (T-fix) | `MExp.expand g h e` の出力には非空引数の `.call` が一切残らない（`MacroExpander`が謳う「呼び出しが残らない」不動点に実際に到達する） | propext |
| `expandGrammar_hasCall_eq_false` | 文法全体レベルでの T-fix（`MGrammar.expandGrammar` の全ルールの本体に呼び出しが残らない） | propext |
| `subst_hasCall_eq_false` / `substArgs_hasCall_eq_false` | **代入は呼び出しなし性を保存する**——`MExp.subst`/`substArgs` の構造に沿った独立の mutual 帰納法。T-fix の `.call i (a::as)` ケース（展開済み本体と展開済み実引数を `subst` で合流させる箇所）が必要とする補題 | propext |

設計判断（`MacroPeg/CallGraph.lean`/`Expand.lean` のヘッダに詳細）:
- **停止性の尺度に `rank` を直接使う**（フォールバック版の「fuel で単に打ち切る」は
  採用しなかった）: `rankGo`/`rankSuccs`（fuel と `visiting` 集合ガード付きの DFS、
  サイクル検知は「現在のスタックに乗っているノードを再訪したら `none`」）で `rank`
  を計算し、`rank_lt_of_acyclic` を `MExp.expand`/`expandArgs`/`expandRule` の
  `termination_by` の測度（`(rankExpr g e, MExp.size e)` の辞書式順序）としてそのまま
  使う。証明の核は2つの単調性補題——**L1**（fuel 単調性、`Fuel.lean` の
  `mpegRun_mono` が直接のテンプレート、低リスク）と **L2**（`visiting` 縮小の単調性、
  このプロジェクト初のグラフ理論で前例ゼロ、最大のリスク項目として設計時に
  名指しされていた）。L2 は「`visiting` は成功を妨げる方向にしか働かない
  （縮小すれば成功しやすくなり、値も大きくならない）」という直感を形式化したもので、
  `foldl` を `foldr` に変更（`cons` 展開を直接効かせるため）し、`List.contains` 系の
  補題名で行き詰まった末に自前の `natElem`（`argAt` と同じ流儀の自前 membership
  チェック）に切り替える、という2回の設計転換を経て証明を完遂した。事前承認済みの
  フォールバック（利用者が rank の候補を直接与え、機械的にチェックするだけに留める案）
  は結局不要だった
- **0 引数呼び出しは対象外**: `.call i (a :: as)`（実引数が非空）だけをグラフの辺／
  展開対象とし、参照実装の `Identifier` と `Call(name, params)` の区別を、この
  プロジェクトの一様な `.call i args` 表現の上に復元している。この設計の帰結として
  `copyGrammar`（M-PEG のフラッグシップ）が正しく非循環判定に落ちる
  （`Copy(w "a")` は非空引数の自己再帰）——これは参照実装の `MacroExpander` も
  `copyGrammar` に対して実際にハングすることの独立した確認でもある（意図した設計の
  帰結であり、バグではない）
- **`.lam`/`.invoke` の本体は `expand` が再帰する**（`subst` とは対照的）:
  `subst` は `.lam` を捕獲回避のため不透明な葉として扱うが、`expand` は本体全体を
  書き換えるパスなので「呼び出し元の環境を守る」動機が最初からなく、`.lam` リテラル
  の内側に埋め込まれた呼び出し（`closureReturnGrammar` の形そのもの）を展開せず
  残すと「呼び出しが残らない」という目標が達成できない
- **`decide`/`rfl` は `rankGo`/`acyclicB` で kernel 簡約に詰まる**（Lean 4 の既知の
  現象——well-founded 再帰は kernel `whnf` では簡約されないことがある一方、
  `#eval`/`#guard`（コンパイル評価）は問題なく動く）: 具体的な文法に対して
  `acyclicB g = true` を実引数として構成する必要がある箇所（`Examples.lean` の
  `closureReturnAcyclic` 等）では、`by decide`/`by rfl` ではなく、関連する等式補題
  （`rankGo`、`rankSuccs`、`natElem`、`MGrammar.calls`、文法自体の `def` など）を
  全部並べた `by simp [...]` で計算を書き換えベースで駆動する
- **`.call i margs` の順序**: Scala 参照実装は「実引数を展開してから callee の生の
  本体に代入し、代入結果を再度展開する」が、この形式化は「callee の本体と実引数を
  独立に展開してから代入する」（各々が単独で測度を厳密に下げるため）。両者は
  「呼び出しが残らない」という最終的な不動点では一致する——`expand` は呼び出しを
  作り出さず消すだけなので、すでに呼び出しなしの2つの断片を `subst` で合流させても
  呼び出しは復活しない（これが `subst_hasCall_eq_false` の内容）——が、この違いは
  参照実装の逐語的アルゴリズムからの意図的な乖離であり見落としではない、として
  `Expand.lean` のヘッダに明記した
- **Lens 抽出器の呼び出し箇所 Prop 引数消去（発見してその場で修復）**: `expand`/
  `expandGrammar` 自体（等式補題ルート）は抽出できたが、当初は呼び出し側
  （`Corpus.lean` の差分ケース）から `acyclicB g = true` の具体的な証明項を実引数
  として渡すと「theorem leaked into executable code」で fail-loud に拒否されて
  いた——`sigParams`（`Lens/Translate.lean`）は関数**定義**側の Prop 引数消去は
  サポートするが、**呼び出し箇所**での消去は未対応と判明（`docs/extractable-
  subset.md` に追記）。同じセッション内でこれを修復：`sigParams`（定義側、Prop
  引数を `Unit` 型のパラメータとして温存——位置を潰さないことで既存の
  `transDefViaEqns` のパターン位置インデックスに一切影響しない）、`transApp`
  （呼び出し箇所、Prop 型の実引数を `()` リテラルへ差し替え）、`transMatcher`
  （名前付き match `match h : e with ...` が各 alt に注入する等式証明の引数も
  同じ経路で消去）の 3 箇所を変更。proof irrelevance により、どんな証明項が渡され
  ていても安全に消去できる。既存 27 ルートはいずれも Prop 引数を持たないため退行
  リスクなし——`make verify` で 60+318+20 ケース全件無退行を確認した上で
  `mExpandCase`（corpus ID `340`/`341`）を追加し、Lens で自動抽出した Scala
  経由の 3 方一致（Lean ≡ golden ≡ Scala、計 22 ケース）を達成した

## CFG 研究: `CFL ⊊ MPEL^CBN_1`（`Cfg/` / `MacroPeg/PegEmbed.lean` / `Shallot/Peg/Examples.lean`）

kmizu/macro_peg（2016年 SWoPP 原稿）が発見的に示唆していた「Macro PEL は CFL を
真に含む」という主張を、T1（プレーン PEG の埋め込み）・T2（GNF 化した CFG の
埋め込み）・T3（両者を組み合わせた言語階層定理）として機械証明した。

| 定理 | 内容 | 公理 |
|------|------|------|
| `MacroPeg.peg_embed_complete` (T1, 完全性) | プレーン PEG の導出 `Derives g e x o` は、0引数 Macro PEG への埋め込み `embedExp e` 上の `MDerives`（call-by-name）に忠実に写る | propext |
| `MacroPeg.peg_embed_sound` (T1, 健全性) | その逆——埋め込みの導出は、元のプレーン PEG の導出を正確に反映する（両方向が揃って初めて「埋め込みは言語を保存する」が言える） | propext |
| `Cfg.cfg_cps_complete` / `cfg_cps_sound` (T2) | GNF（Greibach標準形）の CFG に対する CPS 埋め込み `cfgToMacroPeg`——1引数の継続渡しで、優先順位付き選択の「ローカル成功・継続失敗」バックトラックに対応 | propext(+Classical.choice/Quot.sound の一部) |
| `Shallot.S_char` | aⁿbⁿcⁿ（非文脈自由）の完全な文字特徴づけ——2016年原稿 Fig.6 のプレーン PEG 文法 `S ← &(A !"b") "a"+ B !.` が厳密にこの言語を認識することの証明 | propext, Quot.sound |
| `Cfg.cfl_proper_subset_mpel1` (T3) | `MPEL^CBN_1`（0/1引数ルートの Macro PEG が認識する言語のクラス）は CFL を真に含む——GNF 化できる CFG は T2 で埋め込め、かつ aⁿbⁿcⁿ が T1+`S_char` で `MPEL^CBN_1` に属しながら CFL でない（非文脈自由性は明示的仮説として受け取る、下記参照） | propext, Classical.choice, Quot.sound |

正直なスコープ（誠実に開示すべき2点、モジュールヘッダにも明記）:
- **GNF 仮説**: 一般 CFG→GNF 正規化（ε・単位規則・左再帰の除去）は classical
  （Greibach 1965 / Hopcroft–Ullman）であり、このプロジェクトでは形式化していない
  ——引用に留め、`axiom`/未証明プレースホルダとして忍び込ませることはしていない。
  `Cfg.gnf_cfl_subset_mpel1` の仮説は `isGnfB cg = true` であり、「任意の CFG」
  ではない
- **非文脈自由性の仮説化**: aⁿbⁿcⁿ が CFL でないという事実（pumping lemma、古典的）
  も明示的な仮説として `cfl_proper_subset_mpel1` に渡す——呼び出し側がこの古典的
  証明を供給する設計
- **`CFL ⊆ PEL`（マクロなしのプレーン PEG）は未解決のまま**: T2 の CPS 構成は
  継続を実引数として渡すマクロ層の力に本質的に依存しており、マクロ拡張のない
  プレーン PEG には転用できない。偶数長回文が CFL⊆PEL の反例候補として有力だが
  証明の構成法は見つかっていない（2020年以降も進展なし、確認済み）——この論点は
  T3 の対象ではなく、別の未解決問題（回文予想）である。T7（下記）でこの問題を
  正式に文書化した

## T7: `CFL ⊆ PEL`（マクロなしのプレーン PEG）——未解決問題の文書化（`Cfg/OpenProblems.lean`）

T3 が解決したのは Macro 拡張版（`CFL ⊊ MPEL^CBN_1`）であり、より古い「プレーン
PEG は CFL を全部含むか」という問題（Ford, POPL 2004 が最初に予想）とは別物——
両者を混同しないことが誠実さの要点。この節では**解決済みの半分**を機械証明し、
**未解決の半分**を`Prop`として明示的に文書化した（`axiom`/未証明プレースホルダとして
忍び込ませることはしていない）。

| 定理 | 内容 | 公理 |
|------|------|------|
| `Cfg.abc_isPEL` | aⁿbⁿcⁿ はプレーン PEG（`abcGrammar`、マクロ機構は一切不要）で認識される——`S_char`からほぼ無料で得られる | propext, Quot.sound |
| `Cfg.pel_not_subset_cfl` | **解決済み**: `PEL ⊄ CFL`——`abc_isPEL`と非文脈自由性の仮説（T3と同じ pumping lemma 仮説）を組み合わせるだけ | propext, Quot.sound |
| `Cfg.CFLSubsetPELConjecture` | **未解決**（証明も反証もしていない）：任意の CFL がプレーン PEG で認識可能か。`theorem`ではなく`Prop`の`def`として、答えを主張せずに問題の内容だけを正確に固定する | （定理ではないため公理監査の対象外） |
| `Cfg.EvenPalindromes` | 反例候補の最有力語族——`{a,b}`上の偶数長回文（教科書的CFG`S → aSa \| bSb \| ε`で文脈自由なのは自明、PEG非表現性は未証明）を`Language`として厳密に定義（CFGは構築していない） |  |

なぜ T2 の構成が転用できないか: T2 の CPS 埋め込みは`buildCallSeq`が「次に何を
試すか」という継続を**パラメータ付きルールへの実引数として渡す**ことに本質的に
依存している。プレーンPEGのルールは引数を一切持てないため、この機構がそもそも
存在しない——マクロ層の余分な表現力が「パラメータ付きルールが制御フローをデータ
として運べること」に由来するという非対称性そのものが興味深い考察点。本気で
取り組むなら scaffolding automata 流の pumping 的議論、または全く新しい手法が
必要（Loff/Moreira/Reisはこの問題を解決していない）。今後進展があっても
「Conjecture」（または「Bounded-survived: サイズNまで全数探索で確認済み」）
ラベルを外さないこと——未証明のまま`axiom`/プレースホルダとして忍び込ませない。

設計上の勘所（Lean 特有の罠、次回以降のための備忘）:
- **`conv_lhs`/`conv_rhs` は Mathlib 専用のマクロで、Mathlib 非依存のこのプロジェクト
  には存在しない**——`conv => lhs; rw [...]`（core Lean の `conv` ブロック内ナビゲー
  ション）が正しい書き方
- **ネストした `cases` で複数の枝が共有する新規変数の名前は、後続の `cases` に
  握りつぶされることがある**（`cases`が共有依存変数を revert・再導入する際、ユーザー
  指定名を保持しない）。対策は (a) 握りつぶした直後に `rename_i` で名前を回復する、
  (b) 反転をフラットな存在量化子で返す独立補題（`seq_inv` 等）を先に証明し、本体では
  `obtain` で取り出す——後者の方が深いネストで信頼できる
- **`MDerives` は `DerivesArgsPar`/`DerivesArgsSeq` と相互帰納**なので、`induction h with`
  は使えず（"does not support mutually inductive types" エラー）、`induction h using
  MDerives.rec (motive_2 := ...) (motive_3 := ...)` の後に `case NAME args => tac` を
  並べる必要がある（`MacroPeg/Determinism.lean` の `mderives_det` が同型の先例）
- **コンストラクタの不一致を閉じるには `simp only [...] at h` だけでは不十分**な場合が
  多い（`h : C1 = C2` が単純化されずに残る）——`cases h`/`injection h` を使うのが
  確実（一致する場合は成分を取り出し、不一致なら自動的にゴールを閉じる）
