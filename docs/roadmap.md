# Roadmap

詳細プラン: `~/.claude/plans/lean-4-scala-dapper-tarjan.md`

| M | 内容 | DoD | 状態 |
|---|------|-----|------|
| M0 | スケルトン・elan/Lean v4.32.0・lake/sbt骨格・Makefile・APIスパイク | make verify 全段green | ✅ 完了 |
| M1 | 抽出器v0＋ランタイムv0＋差分テスト1本（Int div/mod #evalピン留め） | 端到端1本green | ✅ 完了（Int `/`・`%`は**ユークリッド除算**と判明→RT.intDiv/intMod実装） |
| M2 | Shallot AST＋Render＋抽出器v1（構造的再帰）＋corpus 00x | Render抽出roundtrip | ✅ 完了（等式ルート動作。fib/fact/gcd/ADTパターン/@tailrec。ケーステーブル自体を抽出する単一ソース差分設計。**重要**: v4.32のimportModulesは`loadExts := true`＋`enableInitializersExecution`＋`importAll := true`必須——ないとMatcherInfo/EqnInfo拡張が空で等式生成が失敗する） | |
| M3 | PEG実装＋抽出器v2（ネストmatchスパイク）＋corpus 01x | parseフェーズgreen | ✅ 完了（matcher分解＝最重リスク項目突破。pegRun全体が抽出されLeanと一致。TCBレビューで捕獲バグ17件発見→全修正→Torture回帰化も同時に実施） |
| M4 | PEG証明 T0-T3・決定性＋Audit開始 | 公理監査green | ✅ 完了（5定理sorryゼロ：T0/P1/T1/T2/T3。公理はpropextのみ、決定性は公理ゼロ。#guard_msgs監査ビルトイン化） |
| M5 | RBMap＋型検査器＋抽出器v3＋corpus 02x-04x | typeフェーズgreen | ✅ 完了（mutual Expr/Args・相互再帰typecheck・多相RBMap抽出。abbrev展開・Prod射影→._1/._2対応。35ケース一致） |
| M6 | RBMap R1-R6＋型検査器 L1-L3 | 監査green | ✅ 完了（RBVerify 618行：cmpStr全順序29補題・R1/R3/R6。R2は296行フル強度。L1-L3は250行） |
| M7 | インタプリタ＋最適化器＋corpus 05x/07x＋ScalaCheck | evalフェーズgreen | ✅ 完了（ScalaCheck 3プロパティ×100ケース込み） |
| M8 | 型健全性 L5＋最適化器 O1-O3 | 監査green | ✅ 完了（TypeSound 791行：eval_sound=stuck不在証明、O3は最適化テーブル対応再帰納） |
| M9 | VM＋コンパイラ＋corpus 06x＋抽出器v4（LCNF・サブセット凍結） | vmフェーズgreen | ✅ 完了（構造化制御VM＝R1設計採用でM10をL難度に。LCNFは根拠付きデスコープ→extractable-subset.md） |
| M10 | コンパイラ正しさ V0-V2（最大の山） | フラッグシップ監査green | ✅ 完了（986行。CPS形式のV1でcallケース込みフルスコープ。エージェントが申し送りの合成補題の偽を反例で発見→再設計） |
| M11 | 具象構文＋roundtrip RT-L1〜L3＋合成定理＋docs | フルコーパス・docs完 | ✅ 完了（RT-L1 594行＋RT-L2 1705行＋RT-L3 1471行。pipeline_correct=全部の合成。sepOkB境界条件をroundtrip証明が発見） |
| M-PEG | kmizu/macro_peg の call-by-name 意味論を独立モジュール `MacroPeg/` として形式化（T0-T3＋headline定理）＋Lens抽出＋差分ハーネス | 監査green・`copy_language_ww` 全称量化・Lens抽出＋差分ハーネスgreen | ✅ 完了（T0-T3の5定理＋headline `copy_language_ww`、sorryゼロ。Lens抽出＋差分ハーネスもgreen、8ケース） |
| M-PEG-2 | `MacroPeg/` に `Strategy`（`.callByName`/`.callByValuePar`）を追加し `MDerives`/`mpegRun` を retrofit。`CallByValuePar`（実引数を同一位置で独立評価）を形式化 | 既存8ケース無退行・T0-T3再証明green・Lens抽出＋差分ハーネス拡張green | ✅ 完了（`DerivesArgsPar`/`evalArgsPar` の mutual 拡張、T0-T3 retrofit、`callParArgFail` の設計バグを完全性証明の過程で発見・修正——`args = pre ++ badArg :: post` ＋ `pre` 成功の明示証拠が必要だった。Par版スモークテスト3ケース追加、既存8ケース無退行、`make verify` フルグリーン） |
| M-PEG-3 | `MacroPeg/` に `Strategy.callByValueSeq` を追加し `MDerives`/`mpegRun` を retrofit。`CallByValueSeq`（実引数を左から逐次評価し入力位置をスレッディング、規則本体は最終位置から）を形式化 | 既存11ケース無退行・T0-T3再証明green・Lens抽出＋差分ハーネス拡張green | ✅ 完了（`DerivesArgsSeq`/`evalArgsSeq` の mutual 拡張、T0-T3 retrofit。`callSeqArgFail` は M-PEG-2 の `callParArgFail` バグの教訓を先回りで反映し設計段階から健全。P1 (`mderives_suffix`) は `callSeqOk` が最終スレッディング位置 `mid` から本体を導出するため `motive_3` を `∃ q, input = q ++ final` という非自明な述語にする必要があった。Seq版スモークテスト3ケース追加、既存11ケース無退行、`make verify` フルグリーン——三戦略すべて形式化完了） |
| M-PEG-4 | `MacroPeg/` に高階関数レイヤーの一部（`.lam`/`.callParam`/`.invoke`）を追加。「渡された callable を同じ呼び出しツリーの中で即座に呼ぶ」パターン（名前付きルール参照・ラムダリテラルの両方）を形式化 | 既存14ケース無退行・T0-T3再証明green・Lens抽出＋差分ハーネス拡張green | ✅ 完了（参照実装の実機検証で「高階関数はEvaluatorのネイティブ機能ではない」という旧来の理解が誤りだったと判明——`MacroExpander`なしで`Evaluator`だけで出荷テスト全件が動くことを確認。`.lam`が名前付きルール参照とラムダリテラルを統一表現し、`.invoke`は`.call`と同じ3-way strategy分岐が必要と実装中に設計訂正（当初「strategy非依存」としていたプランが誤りだった）。Par/Seq下のラムダ引数は参照実装の退化挙動（ゼロ幅マッチ→空文字列）を忠実に再現。HOFスモークテスト5ケース追加（計19ケース）、既存14ケース無退行、`make verify`フルグリーン。真のクロージャ捕獲・戻り値適用（`MacroExpander`必須・非停止性リスクあり・出荷テスト0件）は引き続きスコープ外）。**訂正パッチ（M-PEG-5検討時）**: 「クロージャ戻り値適用は`MacroExpander`なしでは`ClassCastException`でクラッシュする」という記述が不正確と判明——実際は決定的`Failure`で、既存`.callParam`フォールバックだけで既に正しく形式化済み。確認スモークテスト1件追加（計20ケース）、新規証明・新規コンストラクタなし |
| M-PEG-5 | `MacroExpander`相当（マクロ呼び出しの構文的インライン展開）を、パラメータ付きルールの呼び出しグラフが非循環という整形式性条件のもとで形式化し、この条件下で必ず停止することを証明する。これにより「クロージャを戻り値として返し、別の呼び出し元で改めて適用する」パターンが実際に**成功**するケースを扱えるようになる（M-PEG-4までの`.callParam`フォールバックは「常に失敗する」ケースしか説明しない） | 非循環条件の決定可能な検査＋その条件下での停止証明＋既存20ケース無退行 | ✅ 完了（`CallGraph.lean`：DFS＋visiting集合ガードの`rankGo`/`rankSuccs`、自前`natElem`（`List.contains`系補題名で詰まったため）、`acyclicB`（決定可能チェック）、そして本丸`rank_lt_of_acyclic`——非循環グラフ上で辺 `j ∈ g.calls i` なら `rank g j < rank g i`。証明の核心は2つの単調性補題：L1（fuel単調性、`Fuel.lean`の`mpegRun_mono`が直接テンプレート）とL2（visiting縮小の単調性、このプロジェクト初のグラフ理論、前例ゼロ——`foldl`を`foldr`に変えてcons展開を効かせ、`List.contains`の補題名で詰まった末に自前`natElem`に切替、という2回の設計転換を経て証明完了。ダイヤモンド型DAGでの偽陽性循環検知なしも`#eval`で確認済み）。`Expand.lean`：`rank`を`termination_by`の停止性尺度に直接使う`mutual`well-founded再帰で`MExp.expand`/`expandArgs`/`expandRule`＋`MGrammar.expandGrammar`を実装（`Prod.Lex.right'`と`decreasing_by`の試行錯誤を経て確立）。**T-fix**（`expand`の出力に非空引数`.call`が残らないこと）も証明——`.call i (a::as)`ケースで「展開済み本体」と「展開済み実引数」を`MExp.subst`で合流させる箇所が新たに「代入は呼び出しなし性を保存する」という補題（`subst_hasCall_eq_false`、`MExp.subst`/`substArgs`の構造に沿った独立のmutual帰納法）を要求し、これも完遂。ヘッドラインの`Baz`/`Apply`例は`Examples.lean`で`"fail"`→`"ok+0"`への反転を`#guard`で確認（`acyclicB`の証明は`decide`/`rfl`がkernel簡約で詰まる既知のLean 4現象——well-founded再帰がkernel `whnf`では簡約されない——にぶつかったため、等式補題を並べた`simp`でproof項を構成）。Lens抽出は`expand`自体（等式ルート経由）はできても、証明項（`acyclicB g = true`の具体的witness）を実引数として渡す呼び出し箇所で「theorem leaked into executable code」エラー——`sigParams`は関数**定義**のProp引数消去はサポートするが、**呼び出し箇所**でのProp引数消去は未対応という、抽出器の新しい既知の制約と判明（`docs/extractable-subset.md`に追記）。Scala側の実参照との3方一致は、この制約のためLens経由の自動corpus diffではなく、このセッション内で既に実施済みの`sbt console`による一回限りの実機検証（Baz/Apply成功・`Rec(n)`60秒ハング）で代替——設計時に明記した事前承認済みのスコープカット） |

## 未証明TODO（sorryの代わりにここに置く）

（なし — 定理はここから「証明済み」へしか動かない）

## Macro PEG（M-PEG 〜 M-PEG-5）: 今回スコープ外にしたもの

kmizu/macro_peg の README/Scala実装を精読・実機検証した上での意図的な絞り込み
（詳細は `docs/theorems.md` の Macro PEG 節）。macro_peg の三戦略
（`CallByName`/`CallByValuePar`/`CallByValueSeq`）、高階関数レイヤーのうち
「渡された callable を同じ呼び出しツリーの中で即座に呼ぶ」パターン、そして
「クロージャを戻り値として返し、別の呼び出し元で改めて適用する」パターンの
**非循環な場合**（M-PEG-5の`acyclicB`／`MExp.expand`）は形式化済み。

残るスコープ外は：

- **自己再帰するパラメータ付きマクロルールに対する`MacroExpander`相当の展開**:
  `Rec(n: ?) = "a" Rec(n)` のような、通常の評価では何の問題もなく停止する
  ごく普通の（左再帰ですらない）規則でも、`MacroExpander`のナイーブな構文的
  インライン化は無限に自分自身を展開し続け停止しない（M-PEG-5検討時に実機で
  60秒以上のハングを確認済み）。これは参照実装自身が持つ本物の限界であり、
  このプロジェクトの形式化のギャップではない——`acyclicB`はこのケースを正しく
  拒否し（`recGrammar`／`copyGrammar`のスモークテストで確認）、`MExp.expand`は
  この整形式性条件のもとでのみ呼び出し可能な設計にした
- **Lens抽出器の新しい既知の制約**: `MExp.expand`/`MGrammar.expandGrammar`自体
  （well-founded再帰、等式補題ルート経由）は抽出できるが、この関数を呼び出す側
  （例：`Corpus.lean`の差分ハーネス）で`acyclicB g = true`の具体的な証明項を
  実引数として渡すと、抽出器が「theorem leaked into executable code」で
  fail-loudに拒否する。`Lens/Translate.lean`の`sigParams`は関数**定義**の
  Prop引数消去はサポートするが、**呼び出し箇所**でのProp引数消去は未対応と
  判明した（詳細は`docs/extractable-subset.md`）。このため`expand`の
  Scala側3方一致は自動corpus diffではなく、実機（`sbt console`）による
  一回限りの検証（Baz/Apply成功・`Rec(n)`ハング、いずれもM-PEG-5検討時に実施済み）
  で代替した
- **解説ガイド新章**は不要になった——`docs/guide/08-macro-peg.md`/`docs/en/08-macro-peg.md`
  に M-PEG-4（8.6節）・M-PEG-5訂正（8.9節）を追記済みで、macro_pegシリーズの
  ガイド追記はこれで完了
