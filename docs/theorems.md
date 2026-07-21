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
