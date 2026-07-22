# `E1EmbeddingGrind.lean` split plan — `GoodsteinPA/Zef2TC/`

Fable の立案（`model: fable`）による計画．対象は `GoodsteinPA/E1EmbeddingGrind.lean`（`Gexp` 移動後 4496 行）．
方針: **証明の内容は一切変更しない機械的分割**．`Zinfty/`・`OperatorZef2/` と同粒度（1ファイル1テーマ，150〜700行）で14ファイルに分ける．分割後 `E1EmbeddingGrind.lean` は削除する．

## 0. 事前に確認した依存関係の要点

- `BudgetedEmbedsTC` ラダー（TC版 master predicate）は V3 ラダー・最終パイプラインから一切使われていない（`budgetedEmbedsTC_*` の出現は自セクションと歴史的コメントのみ）．独立の葉ファイルにできる．
- EM エンジン（`em_Zef2TC'`・`em_cong1_Zef2TC`）は TC ラダー・V3 ラダー・帰納法キットの3箇所から使われる → 独立ファイルに切り出し，3ファイルが import する．
- `envSup`／term domination は V3 ラダー・SuccInd・Embedding・最終部から使われる → V3 より前に置く．
- `allω_inversion` は `embedding_Zef2TC_V3` と `stepAllωTC_bnd` の両方から使われる → Embedding でも Pass でもなく Inversion ファイルに置く．
- `rankToZeroAuxTC` は `passAuxTC` を使う → Rank0 は Pass に依存．
- `readoffVTC_core` は `sound0_TC` を使い，`readoff_value_goodstein` は `embedding_Zef2TC_V3` を使う → Readoff は Rank0 と Embedding の両方に依存．
- 残存 `sorry` は0個（grep ヒットは全て歴史的コメント中の文字列）．

## 1. ファイル一覧

| # | ファイル | 想定行数 | テーマ（一言） |
|---|---|---|---|
| 1 | `Zef2TC/Basic.lean` | ~270 | `Zef2TC` の定義・単調性・slot 算術 |
| 2 | `Zef2TC/Em.lean` | ~360 | budgeted 排中律エンジン（EM＋値合同 EM） |
| 3 | `Zef2TC/EmbedTC.lean` | ~350 | TC 版 master predicate のケースラダー（歴史的・下流未使用） |
| 4 | `Zef2TC/TermBound.lean` | ~140 | `envSup` と項値の `Gexp` 支配 |
| 5 | `Zef2TC/EmbedV3.lean` | ~420 | V3（構造的予算）master predicate のケースラダー |
| 6 | `Zef2TC/Axm.lean` | ~395 | ∃-free 有界真理キット＋PA⁻ 公理の一括処理 |
| 7 | `Zef2TC/SuccInd.lean` | ~365 | 帰納法スキーマ（succInd）のケース |
| 8 | `Zef2TC/Inversion.lean` | ~455 | 反転補題（allω・⋏・⋎）＋⊥-erase |
| 9 | `Zef2TC/Embedding.lean` | ~150 | V3 埋め込みの組み立てと rung-E 実現 |
| 10 | `Zef2TC/CutStep.lean` | ~240 | principal cut 簡約（⋏／atom／⊤） |
| 11 | `Zef2TC/Pass.lean` | ~640 | `Zef2TCProv` とカット除去 pass |
| 12 | `Zef2TC/Rank0.lean` | ~125 | rank 降下と rank-0 真理核 |
| 13 | `Zef2TC/Readoff.lean` | ~350 | 値予算 read-off パイプライン |
| 14 | `Zef2TC/Wainer.lean` | ~240 | 線形段数化と `wainer_bound_witness` |

### 各ファイルの内容（宣言名の割り当て）

**1. `Basic.lean`**（元 L35–119, 292–446, 460, 903–910）
- `inductive Zef2TC`，`Zef2TC.gate`，`Zef2TC.ofZef2`
- `Zef2TC.mono_f`，`Zef2TC.mono_c`，`Zef2TC.change_H`，`Zef2TC.change_e`
- `clT`（`Cl (fun _ => True)` の自明事実．汎用なのでここ）
- slot 算術: `relSlot_le`，`relSlot_mono`，`relSlot_succ_gap`，`le_relSlot_zero`，`index_le_relSlot_zero`（元位置は L903 だが純粋な slot 算術なのでここへ移す）
- import: 現ヘッダの外部 import 群（`ToMathlib.Goodstein.CichonCaicedo`・`ToMathlib.Hardy.Gexp`・`Encoding`・`ToFoundation.Numeral`・`ToFoundation.Subst`・`ReadoffValueGate`）をここに引き継ぐ．コメントアウト済みの `-- public import GoodsteinPA.Zinfty.Embedding` は削除．`import Std.Tactic.BVDecide.Normalize.Prop` は本当に必要か分割時に確認し，必要なファイルだけに残す．

**2. `Em.lean`**（元 L121–255, 689–902）
- `em_Zef2TC`，`em_Zef2TC'`
- `private em_cong_atomic_rel`，`private em_cong_atomic_nrel`，`em_cong_Zef2TC`，`em_cong1_Zef2TC`

**3. `EmbedTC.lean`**（元 L447–687（`clT` を除く），913–1030）
- `BudgetedEmbedsTC`，`budgetedEmbedsTC_closed`／`_verum`／`_wk`／`_shift`／`_or`／`_and`／`_cut`／`_exs`
- 注意: このラダーは V3 に置き換えられており下流に消費者がいない．分割時はそのまま保持するが，「削除するか」はユーザー判断事項として PR で明示すること．

**4. `TermBound.lean`**（元 L1041–1180）
- `envSup`，`envSup_mono_N`，`le_envSup`，`envSup_cons_le`
- `term_val_le_Gexp_iter`，`stdClosedVal_asg`，`stdClosedVal_asg_le_Gexp_iter`

**5. `EmbedV3.lean`**（元 L1181–1600）
- `BudgetedEmbedsV3`，`ewRootSlot_mono_B`，`envSup_shift_le`
- `budgetedEmbedsV3_closed`／`_verum`／`_wk`／`_or`／`_shift`／`_all`／`_and`／`_cut`／`_exs`

**6. `Axm.lean`**（元 L1601–1996）
- `ExFree`，`ExFree.rew`，`truth_exFree_Zef2TC`，`asg_emb_fix`，`atomTrue_asg_emb`
- `budgetedEmbedsV3_of_exFree_true`，`budgetedEmbedsV3_addEqOfLt`，`budgetedEmbedsV3_axm_PAminus`

**7. `SuccInd.lean`**（元 L1997–2360）
- `Cl_osuccs`，`allClosure_peel`，`clog_tower_gate`，`Cl_omega`
- `subst1_comp_bShift'`，`rew_subst1_comm_q'`，`rew_succInd'`，`succInd_nnf'`
- `metaInduction_Zef2TC`，`succTerm`，`stdClosedVal_succTerm`，`succInd_shape_Zef2TC`，`budgetedEmbedsV3_succInd`

**8. `Inversion.lean`**（元 L2401–2519, 2571–2906）
- `allω_inversion`（Embedding と Pass の双方から使われるためここに置く）
- `and_inversion_left`，`and_inversion_right`，`or_inversion`，`falsum_erase`

**9. `Embedding.lean`**（元 L256–290, 2363–2400, 2520–2568）
- `goodsteinBody`，`goodsteinSentence_eq_all_body`，`goodsteinBodyE`（Goodstein 文の形は埋め込みと read-off の双方で使うが，Readoff が Embedding に依存するのでここで足りる）
- `budgetedEmbedsV3_axm`（PA⁻／succInd ディスパッチャ），`budgetedEmbeddingV3`（`Derivation2` 上の組み立て済みラダー）
- `coe_goodsteinSentence_eq`，`embedding_Zef2TC_V3`

**10. `CutStep.lean`**（元 L2908–3148）
- `stepAnd_Zef2TC`，`false_nrel_erase`，`false_rel_erase`，`stepAtom_Zef2TC`，`stepVerum_Zef2TC`

**11. `Pass.lean`**（元 L3150–3784）
- `Zef2TCProv` と namespace（`Zef2TCProv.of`／`.mono`／`.weakening`／`.mono_f`）
- `cutReduceAllAuxRunning_TC`，`stepAllωTC_bnd`，`passAuxTC`
- 640 行は既存最大（`OperatorZef2/CutStep.lean` 692 行）の範囲内なので1ファイルとする．将来さらに割るなら `CutReduce.lean`（`Zef2TCProv`＋`cutReduceAllAuxRunning_TC`＋`stepAllωTC_bnd`，~320行）と `Pass.lean`（`passAuxTC`，~320行）の2分割が自然な切れ目．

**12. `Rank0.lean`**（元 L3786–3907）
- `rankToZeroAuxTC`，`rankToZero_TC`，`sound0_TC`

**13. `Readoff.lean`**（元 L3909–4256）
- `three_le_rel1_rootSlot`
- `Sslot`，`Sslot_mono`，`Sslot_infl`
- `readoffVTC_core`，`readoff_value_Zef2TC`，`readoff_value_pipeline`
- `goodsteinBodyE_inst_shape`，`readoff_value_goodstein`

**14. `Wainer.lean`**（元 L4258–4496）
- `goodsteinBodyE_semantic_link`
- `readoff_value_pipeline'`，`embedding_Zef2TC_V3_linearK`，`readoff_value_goodstein'`
- `wainer_bound_witness`（最終成果物．`Statement.lean` が消費）

## 2. import 依存（DAG，全て `public import`）

```
Basic
├─→ Em
│    ├─→ EmbedTC          （葉．下流消費者なし）
│    ├─→ EmbedV3          （TermBound も import）
│    └─→ SuccInd          （EmbedV3 経由＋em_cong1 直接使用）
├─→ TermBound ─→ EmbedV3
│                 ├─→ Axm ────────┐
│                 └─→ SuccInd ────┤
└─→ Inversion                     ├─→ Embedding
     ├──────────────────────────┘         │
     └─→ CutStep ─→ Pass ─→ Rank0 ─┐      │
                                    ├─→ Readoff ─→ Wainer
                                    │      ↑
                          Embedding ┘──────┘
```

具体的な import 行:
- `Em` ← `Basic` / `EmbedTC` ← `Em` / `TermBound` ← `Basic` / `EmbedV3` ← `Em`, `TermBound`
- `Axm` ← `EmbedV3` / `SuccInd` ← `EmbedV3`, `Em` / `Inversion` ← `Basic`
- `Embedding` ← `Axm`, `SuccInd`, `Inversion` / `CutStep` ← `Inversion`
- `Pass` ← `CutStep` / `Rank0` ← `Pass` / `Readoff` ← `Rank0`, `Embedding` / `Wainer` ← `Readoff`

循環なし．並列作業する場合，`{EmbedTC}`・`{Axm, SuccInd}`・`{CutStep 以降}`・`{Embedding}` は互いに独立に進められる．

## 3. 命名の根拠

- `Basic`・`Inversion`・`Embedding` — `Zinfty/{Basic,Inversion,Embedding}.lean` と同名同役割（定義＋基本補題／連結子反転／埋め込み定理）．
- `CutStep`・`Pass`・`Rank0` — `OperatorZef2/{CutStep,Pass,Rank0}.lean` と同名同役割（principal cut 簡約／カット除去 pass／rank-0 還元）．`Zef2TC` は `Zef2` の拡張calculus なので対応が明快．
- `Em`・`EmbedTC`・`EmbedV3`・`TermBound`・`Axm`・`SuccInd`・`Readoff`・`Wainer` — 既存に直接の対応物が無い新テーマ．`GateArith.lean`（156行の小さな算術ファイル）に相当する粒度として `TermBound` を独立させた．
- namespace は当面 `GoodsteinPA.E1EmbeddingGrind` のまま変えない．`OperatorZef2/` も namespace は `GoodsteinPA.OperatorZeh` でディレクトリ名と一致していない先例がある．namespace 改名（例: `GoodsteinPA.OperatorZef2TC`）は下流の `wainer_bound_witness` 参照の書き換えを伴うため，別 PR の follow-up とし本分割のスコープ外とする．

## 4. 各ファイルで必要なクリーンアップ（後続の Sonnet リファクタ担当への指示）

作業ログ残骸は grep で81箇所ヒットする．CLAUDE.md の規約（プラン番号・issue 番号・lap 番号依存の記述は提出前に全削除）に基づき，分割と同時または直後に以下を行う．削除・書き換え後は
`grep -n "see plan\|issue #\|Step [0-9]\|§[0-9]\|L[0-9]-[0-9]\|lap[- ]\?[0-9]\|SERIES-[0-9]\|PENDING_WORK\|FULLY PROVED\|Claim [A-Z]\|sub-fact\|RETIRED\|block[- ][0-9]\|Block 1[0-9]\|ledger\|ratif\|rung [A-E]\|E-[01] \|W[0-9] \|judge\|DIRECTION"`
で残存確認する．

- 全ファイル共通: module docstring を「このファイルが今何を定義するか」だけの記述に書き直す（`Series-3`・`E-1 block N`・`W1/W3`・`block-6 amendment`・`Block 12c–f`・`E-seam piece (1)/(2)`・`Route-(c)`・`2b prep/item (d)`・`Lap 210 (SERIES-4 S-3/S-5)`・`DIRECTION lap-206` 等のセクション見出し・ラベルを全廃）．「judge input, NOT ratified」「wip-only ruling input」「ledger block 6」のような裁定プロセス由来の文言も削除．docstring は120文字までは1行化．
- `Basic.lean`: 冒頭 module docstring が最重量．`wip/E0Ax2NeedProbe.lean § E-1 seam probe` への参照（実在しないパス）ごと削除し，`Zef2TC` が `Zef2`＋(Ax2)＋有限連結子規則である旨だけ残す．「E–W Def-23」等の文献言及は `references.bib` のキー引用（`- [Key, Definition 23]` 形式）に統一．
- `Em.lean`: `Embedding.lean` の `provable_em` への言及は，どのファイルか曖昧（`Zinfty/Embedding.lean` のこと）なので現行パスに修正するか削除．
- `EmbedTC.lean`: 「RETIRED (SERIES-5 Lane C)」「Deleted to reach `src` sorry-free」「carries `sorryAx` through three disclosed hard leaves」等の削除済みドラフトの墓標コメント群を全て削除（現存コードの説明として意味を成さない）．
- `Embedding.lean`: 「AMENDED rung-E statement DRAFT」「decorative judge-input」コメント，「REALIZED (V3 + inversion; judge input, NOT ratified)」を削除し，`embedding_Zef2TC_V3` の statement 説明のみ残す．
- `Axm.lean`: 「disclosed `sorry`, next E-1 block」（既に sorry-free なので虚偽）を削除．
- `Rank0.lean`／`Readoff.lean`: 「`sorry` pending the guard-carrying statement the judge ratifies for rung D/E」「superseded by the V-threaded read-off」等の経緯説明を削除．
- `Wainer.lean`: 「Lap 210」「SERIES-4 S-5」「the axiom's VERBATIM type」等を削除し，`wainer_bound_witness` が `Statement.lean` の消費する形であることだけ述べる．

## 5. 下流の import 付け替え

`E1EmbeddingGrind` を参照するファイルは3つ．

1. `GoodsteinPA/Statement.lean`（`public import GoodsteinPA.E1EmbeddingGrind`，`E1EmbeddingGrind.wainer_bound_witness` を参照）→ import を `public import GoodsteinPA.Zef2TC.Wainer` に差し替え．namespace を維持するため参照名の変更は不要．
2. `GoodsteinPA.lean`（mk_all 生成の all-import）→ 手で書き換えず，分割完了後に `just mk-all` で再生成．
3. `GoodsteinPA/ReadoffValueGate.lean`（docstring 中の言及のみ）→ `E1EmbeddingGrind.lean` への文言を新ファイル名（`Zef2TC/Wainer.lean` 等の該当箇所）に更新．コードの変更は無し．

## 6. 実施手順（機械的分割の進め方）

1. `GoodsteinPA/Zef2TC/` を作成し，依存順（`Basic` → … → `Wainer`）に各ファイルへ該当行ブロックを証明を一切変えず移す．各ファイルに `module`・import 行・`@[expose] public section`・`namespace GoodsteinPA.E1EmbeddingGrind`・`open LO LO.FirstOrder LO.FirstOrder.ArithmeticTerm ONote Ordinal` / `open GoodsteinPA.OperatorZeh GoodsteinPA.OperatorZinfty` のヘッダを複製する．
2. 元ファイル内での順序移動は3箇所のみ: `index_le_relSlot_zero`（→ `Basic`），`goodsteinBody` 群（→ `Embedding`），`clT`（→ `Basic`）．いずれも移動先が使用元より上流になることを確認済み．
3. `E1EmbeddingGrind.lean` を削除（aggregator ファイルは作らない）．
4. `Statement.lean` の import を差し替え，`just mk-all` を実行．
5. `lake build` で全体確認（証明を変えていないので通るはず．通らない場合は import 漏れのみを疑う）．
6. §4 のクリーンアップを各ファイル担当の `lean4-proof-refactorer`（Sonnet）に委任し，再度 `lake build`＋残骸 grep で検証．
7. `just shake` は PR 後の CI 結果を見てからのみ実行．

---

補足: 残存 `sorry` は無し（実体0，コメント中の文字列のみ）．`BudgetedEmbedsTC` ラダー一式（`EmbedTC.lean` 行き）は下流未使用のため，保持か削除かの判断ポイントとして PR 本文に明記することを推奨．
