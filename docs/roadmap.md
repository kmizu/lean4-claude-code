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
| M6 | RBMap R1-R6＋型検査器 L1-L3 | 監査green | 🔄 L1-L3✅（健全性＋完全性250行）、R2✅（Okasaki平衡296行・弱化ゼロ）、R1/R3/R5/R6証明中 |
| M7 | インタプリタ＋最適化器＋corpus 05x/07x＋ScalaCheck | evalフェーズgreen | ✅ 完了（ScalaCheck 3プロパティ×100ケース込み） |
| M8 | 型健全性 L5＋最適化器 O1-O3 | 監査green | 🔄 L4/O1/O2証明中。L5/O3はR6着地後に発射 |
| M9 | VM＋コンパイラ＋corpus 06x＋抽出器v4（LCNF・サブセット凍結） | vmフェーズgreen | ✅ 完了（構造化制御VM＝R1設計採用でM10をL難度に。LCNFは根拠付きデスコープ→extractable-subset.md） |
| M10 | コンパイラ正しさ V0-V2（最大の山） | フラッグシップ監査green | ✅ 完了（986行。CPS形式のV1でcallケース込みフルスコープ。エージェントが申し送りの合成補題の偽を反例で発見→再設計） |
| M11 | 具象構文＋roundtrip RT-L1〜L3＋合成定理＋docs | フルコーパス・docs完 | ✅ 完了（RT-L1 594行＋RT-L2 1705行＋RT-L3 1471行。pipeline_correct=全部の合成。sepOkB境界条件をroundtrip証明が発見） |

## 未証明TODO（sorryの代わりにここに置く）

（なし — 定理はここから「証明済み」へしか動かない）
