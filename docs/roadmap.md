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
| M-PEG-4 | `MacroPeg/` に高階関数レイヤーの一部（`.lam`/`.callParam`/`.invoke`）を追加。「渡された callable を同じ呼び出しツリーの中で即座に呼ぶ」パターン（名前付きルール参照・ラムダリテラルの両方）を形式化 | 既存14ケース無退行・T0-T3再証明green・Lens抽出＋差分ハーネス拡張green | ✅ 完了（参照実装の実機検証で「高階関数はEvaluatorのネイティブ機能ではない」という旧来の理解が誤りだったと判明——`MacroExpander`なしで`Evaluator`だけで出荷テスト全件が動くことを確認。`.lam`が名前付きルール参照とラムダリテラルを統一表現し、`.invoke`は`.call`と同じ3-way strategy分岐が必要と実装中に設計訂正（当初「strategy非依存」としていたプランが誤りだった）。Par/Seq下のラムダ引数は参照実装の退化挙動（ゼロ幅マッチ→空文字列）を忠実に再現。HOFスモークテスト5ケース追加（計19ケース）、既存14ケース無退行、`make verify`フルグリーン。真のクロージャ捕獲・戻り値適用（`MacroExpander`必須・非停止性リスクあり・出荷テスト0件）は引き続きスコープ外） |

## 未証明TODO（sorryの代わりにここに置く）

（なし — 定理はここから「証明済み」へしか動かない）

## Macro PEG（M-PEG 〜 M-PEG-4）: 今回スコープ外にしたもの

kmizu/macro_peg の README/Scala実装を精読・実機検証した上での意図的な絞り込み
（詳細は `docs/theorems.md` の Macro PEG 節）。macro_peg の三戦略
（`CallByName`/`CallByValuePar`/`CallByValueSeq`）と、高階関数レイヤーのうち
「渡された callable を同じ呼び出しツリーの中で即座に呼ぶ」パターンは形式化済み。
残るスコープ外は：

- **クロージャの戻り値適用**（真の環境捕獲）: あるルール呼び出しがクロージャを
  「戻り値」として返し、それを**別の**呼び出し元で改めて適用するパターン。
  AST上は書けるが、参照実装でもこれを動かすには別ユーティリティ `MacroExpander`
  （呼び出し前にグラマ全体を展開する、非停止性リスクのある構文的インライン化パス、
  自己再帰する規則には使えない）が必須で、出荷テストスイートに1件もこのパターンの
  テストが存在しない（M-PEG-4着手時に`sbt console`で実機確認済み）。旧版のこの
  節は「高階関数レイヤーは丸ごとEvaluatorのネイティブ機能ではない」としていたが、
  これは不正確だった——正しくは「クロージャの戻り値適用だけがネイティブ機能ではなく
  `MacroExpander`必須」であり、それ以外の高階関数の使い方（M-PEG-4が形式化した
  部分）はネイティブにサポートされている
- **解説ガイド新章**（`docs/guide/08-macro-peg.md` への M-PEG-4 追記は独立の作業
  として提案する。Par/Seq分の追記は既に反映済み）
