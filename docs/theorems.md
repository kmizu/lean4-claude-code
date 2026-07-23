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

## Macro PEG（M-PEG / M-PEG-2 / M-PEG-3 / M-PEG-4）: kmizu/macro_peg の意味論

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
