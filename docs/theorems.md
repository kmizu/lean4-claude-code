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
| L5 型健全性 | well-typed ⇒ stuck しない（divByZero のみ許容）— 証明中 |
| O3 | プログラムレベル最適化保存 — 証明中 |

## コンパイラ・VM（M10）

| 定理 | 内容 |
|------|------|
| V0 | VM 燃料単調性・コード連接合成・テーブル橋 — 証明中 |
| V1 | 式レベル前進シミュレーション — 証明中 |
| V2 | `runProgram` 成功値 ⇒ `vmRunProgram` 同値 — 証明中 |

## パーサ roundtrip（M11）

| 定理 | 内容 |
|------|------|
| RT-L1（`digitsVal_natDigits`・`keyword_guard_fails`・`derives_ident`・`derives_number` ほか） | 字句層の導出構築キット＋復元 ✅ |
| RT-L2 `derives_printExpr` | 式層: 正準印字はパーズされ AST が復元される — 証明中 |
| RT-L3 | プログラム層 roundtrip — RT-L2 後 |
| パイプライン合成 | print → parse → check → eval の合成定理 — 最終 |

既知の正準形制約: `eqB` は `eqI` と同一の `"=="` に印字されるため正準印字不能
（roundtrip は `printableB` 仮定下）。負リテラルは `( - digits )` に印字され、
`treeToAst` が正規化して戻す（`Canon` 仮定）。
