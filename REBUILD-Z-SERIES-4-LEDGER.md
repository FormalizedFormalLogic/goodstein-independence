# REBUILD-Z — SERIES-4 LEDGER (append-only; block per lane-advance)

Order in force: `E-2026-07-03-JUDGE-series3-validation.md` §4 (the SERIES-4 FINAL-DISCHARGE order).
Baseline for judge diffs: `ab41710` (lap-210 baton; Lane S landed across laps 209–210).

---

## Block 1 — LANE S COMPLETE (S-1…S-5): `wainer_bound_witness` GREEN at the axiom's VERBATIM type

**Laps**: 209–210 · **Files**: `wip/HardyMajorization.lean`, `wip/ReadoffValueGate.lean`,
`wip/E1EmbeddingGrind.lean` (src UNTOUCHED; the swap is judge-gated) · **Build**: 🟢 all three
modules re-compiled clean via `lake env lean` this lap (lap 211, 2026-07-03).

### The summit statement (S-5, `649b1e4`)

`GoodsteinPA.E1EmbeddingGrind.wainer_bound_witness` (wip/E1EmbeddingGrind.lean:4985) concludes,
from hypotheses `Hcert`/`HSdom`/`Hconv` (see pairing below) and `h : 𝗣𝗔 ⊢ ↑goodsteinSentence`:

```lean
∃ o : ONote, o.NF ∧
  GoodsteinPA.WainerRoute.EventuallyLE GoodsteinPA.Dom.goodsteinLength
    (fun n => fastGrowing o n)
```

— the VERBATIM type of the sole route axiom `wainer_bound_of_pa_proves_goodstein`
(`src/GoodsteinPA/WainerRoute.lean:119-121`), copied not composed (namespace-qualified since wip
sits outside the `GoodsteinPA.WainerRoute` namespace; `EventuallyLE`/`goodsteinLength`/
`fastGrowing`/`goodsteinSentence` are the same src decls).

### Hypothesis pairing (the three-module seam)

The three wip modules cannot import each other (standalone `lake env lean` files), so S-5 takes
the sibling results as hypotheses whose statements are the siblings' VERBATIM statements:

| S-5 hypothesis | = verbatim statement of | location | delta |
|---|---|---|---|
| `Hcert` | `ReadoffValueGate.gated_certificate_uniform` | RVG:590 | none (binder-for-binder) |
| `HSdom` | `HardyMajorization.Scirc_dom_pad` | HM:1301 | none (`oadd (ofNat 2) 1 0` spelled identically; `Wpow`-free) |
| `Hconv` | `HardyMajorization.master_conversion` | HM:1344 | none (implicit-binder order identical) |

Judge splice = concatenate/import the three modules in src and apply the three theorems to the
witness's hypotheses — zero statement adaptation required.

### `#print axioms` transcript (lap 211 re-verification, real compiler output)

```
'GoodsteinPA.E1EmbeddingGrind.wainer_bound_witness' depends on axioms: [propext, Classical.choice, Quot.sound]
'GoodsteinPA.E1EmbeddingGrind.readoff_value_goodstein'' depends on axioms: [propext, Classical.choice, Quot.sound]
'GoodsteinPA.E1EmbeddingGrind.readoff_value_pipeline'' depends on axioms: [propext, Classical.choice, Quot.sound]
'GoodsteinPA.E1EmbeddingGrind.embedding_Zef2TC_V3_linearK' depends on axioms: [propext, Classical.choice, Quot.sound]
'GoodsteinPA.ReadoffValueGate.gated_certificate_uniform' depends on axioms: [propext, Classical.choice, Quot.sound]
'GoodsteinPA.ReadoffValueGate.gvb_le_iter' depends on axioms: [propext, Classical.choice, Quot.sound]
'GoodsteinPA.ReadoffValueGate.gvb_substs_q_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'GoodsteinPA.HardyMajorization.Scirc_dom_pad' depends on axioms: [propext, Classical.choice, Quot.sound]
'GoodsteinPA.HardyMajorization.master_conversion' depends on axioms: [propext, Classical.choice, Quot.sound]
'GoodsteinPA.HardyMajorization.ewIterTower_dom_pad' depends on axioms: [propext, Classical.choice, Quot.sound]
'GoodsteinPA.HardyMajorization.ewIter_dom_pad_levelcap' depends on axioms: [propext, Classical.choice, Quot.sound]
'GoodsteinPA.HardyMajorization.hardy_pad_lt_fastGrowing_osucc' depends on axioms: [propext, Classical.choice, Quot.sound]
```

**Disclosure**: `wip/E1EmbeddingGrind.lean` contains exactly TWO `sorryAx`-bearing decls —
`readoffTC_core` and `readoff_delta0_Zef2TC` — the SUPERSEDED pre-value read-off (the lap-205
`allω` trap, route (c) replaced it with `readoffVTC_core`/`readoff_value_*`, lap 207). Neither is
in `wainer_bound_witness`'s dependency cone (its transcript above is sorryAx-free, which is the
kernel's own certification of that). Judge may retire both at splice time. RVG and HM transcripts
are sorryAx-free in full.

### Chain of custody (commit per stage)

- S-1 `ewIterTower_dom_pad` — `564b51f`
- S-2 `gvb_le_iter` `15f6617` · `hardy_Wpow_iter_dom_pad`/`dom_pad_max`/`Sstar_dom_pad` `b22dbc3`
- S-3 `ewIter_dom_pad_levelcap`+`two_pow_le_hardy_Wpow2` `b22d33f` · primed pipeline
  (`readoff_value_pipeline'`/`embedding_Zef2TC_V3_linearK`/`readoff_value_goodstein'`) `d5f044a`
  · `dom_pad_comp` `4511346` · `gated_certificate_uniform` `5370cf0` ·
  `master_conversion`+`Scirc_dom_pad`+`two_mul_add_le_hardy_omega_sq` `64902f1`
- S-4 `hardy_pad_lt_fastGrowing_osucc`+`dom_pad_eventuallyLE` — `19065e7`
- S-5 `wainer_bound_witness` — `649b1e4`

**Lane S status: COMPLETE.** Remaining for the SERIES-4 pass: Lane B (blocks below) + judge
executes the src splice and axiom→theorem swap.

---

## Block 2 — LANE B-1 CRACKED: the 12 native_decide base cases proven KERNEL-ONLY

**Lap**: 211 · **File**: `wip/KernelBaseCases.lean` (NEW; src untouched this lap) ·
**Build**: 🟢 `lake env lean wip/KernelBaseCases.lean` clean.

**Result**: `base_cases_kernel` — the VERBATIM statement of `goodsteinLength_base_cases`
(`4 ≤ M < 16 → 2^{M+1} + M ≤ goodsteinLength M`) — on exactly
`[propext, Classical.choice, Quot.sound]`. **No `Lean.ofReduceBool`.** Compiles in seconds
(vs. minutes of native computation before).

**The insight (checkpoint survival)**: `le_bump` ⇒ the Goodstein value drops by at most 1 per
step ⇒ `goodsteinSeq M k = v ≥ 1` certifies `goodsteinLength M ≥ k + v`
(`glen_ge_of_seq_value`, with `goodsteinSeq_zero_absorb` covering steps before `k`). Every seed
`4 ≤ M < 16` reaches `v ≥ 2^{M+1}+M − k` by step `k ≤ 4` (max value 326593 at M=15) — the
65551-step forward pass was never needed. Kernel evaluation via `gvalF`/`bumpF` (fuel-based
structural clone of `bump`, fuel = n; `bumpF_eq` bridges; mathlib's `Nat.log` is already
structural hence kernel-reducible — the old "WF-recursion forces native_decide" note is now
HALF-stale: it still holds for `bump`, no longer for `Nat.log`).

**NEXT (mechanical, grind-legal)**: move the 5 helpers + swap the proof body of
`goodsteinLength_base_cases` in `Domination.lean` (statement FROZEN, satisfied verbatim), full
`lake build`, re-`#print axioms` the growth headline — `Lean.ofReduceBool` should drop from
`goodsteinLength_exp_lower_uncond` and everything downstream. The 12 anti-vacuity `example`s
elsewhere may keep native_decide (they sit on no theorem's axiom path).

---

## Block 3 — B-1 src swap EXECUTED (lap 212)

**Commit**: (this commit) · full bare `lake build` GREEN (1342 jobs).

The 5 kernel helpers (`bumpF`, `bumpF_eq`, `gvalF`, `gvalF_goodstein`, `goodsteinSeq_zero_absorb`,
`glen_ge_of_seq_value`) moved from `wip/KernelBaseCases.lean` into
`src/GoodsteinPA/Domination.lean` directly above `goodsteinLength_base_cases`; that theorem's
proof body swapped to the kernel checkpoint route (statement byte-identical, FROZEN). The
`native_decide` route (`glen_ge_of_gpos` + 12 native passes) no longer feeds any theorem.

**Axiom transcript AFTER swap** (fresh `lake env lean` run, 2026-07-03):

```
'GoodsteinPA.Dom.goodsteinLength_base_cases'      : [propext, Classical.choice, Quot.sound]
'GoodsteinPA.Dom.goodsteinLength_exp_lower_uncond': [propext, Classical.choice, Quot.sound]
'GoodsteinPA.Dom.fastGrowing_two_le_goodsteinLength': [propext, Classical.choice, Quot.sound]
'GoodsteinPA.WainerRoute.goodsteinLength_eventually_dominates_fixed_fastGrowing':
                                                    [propext, Classical.choice, Quot.sound]
```

**BEFORE** (Block 2 / pre-lap-211): the same chain carried `Lean.ofReduceBool` from the 12
`native_decide` base cases. **`Lean.ofReduceBool` is now OFF the growth headline entirely.**
Anti-vacuity `example`s elsewhere retain native_decide by design (no theorem's axiom path).

---

## Block 4 — B-2: the 15 src `sorry` sites — re-point / retirement PROPOSALS (lap 212)

Inventory is exact (regex over `src/`, 2026-07-03): 15 proof-term `sorry`s. NONE is on the
headline axiom path (`peano_not_proves_goodstein` = `[propext, choice, Quot.sound,
goodstein_implies_consistency]`, re-verified lap 209; growth headline now ofReduceBool-free per
Block 3). Proposals only — **the judge executes all deletions/edits**.

### Group 1 — discharged by the SERIES-4 splice (1 site)
| site | decl | proposal |
|---|---|---|
| `WainerLadder.lean:45` | `wainer_splice_Zef2` | **RE-POINT at the judge pass**: statement's conclusion is verbatim `wainer_bound_witness`'s (Lane S summit, Block 1); its 3 hypotheses are kernel-clean module theorems. The SERIES-4 splice closes this `sorry` by composition — no restatement. |

### Group 2 — dead `red`-cluster (Route-A superseded engine) — RETIREMENT proposals (6 sites)
The `red`-engine soundness cluster was superseded laps 141–144 (engine = `iRKcCrit`/keep-tip;
memory + `DIRECTION.md` lap-140/142 blocks: "`red` is the WRONG engine; 1108/82 are false
shadows"; lap-166: "dead `red` cluster STILL sorries"). None feeds the live genReduct/master-key
frontier or any headline.
| site | decl / locus | proposal |
|---|---|---|
| `Crux2Blueprint.lean:82` | `zKValidF_iIndReduct_of_zInd` | **RETIRE** — target kernel-refuted lap 136 (ordinal shadow; correct reduct is the substituted multi-step chain, realized via `iIndReductSeqG`). Unprovable as stated. |
| `Crux2Blueprint.lean:1299` | `ZDerivation_red_zK_crit` | **RETIRE** — false shadow (ex-:1108); superseded by sorry-free `ZDerivation_iRKcCrit_critical_all` (lap 142). |
| `Crux2Blueprint.lean:1411` | `ZDerivation_red_zK_splice` | **RETIRE** — same cluster; splice superseded by GenReductCert flatten route (lap 151). |
| `Crux2Blueprint.lean:1607` | `redSound` dispatcher, axNeg Path-C residual | **RETIRE with cluster** — axNeg handled red-free by keep-tip reconstruction (lap 144). |
| `Crux2Blueprint.lean:1698` | `redSound` dispatcher, `redZKReady` residual | **RETIRE with cluster**. |
| `Crux2Blueprint.lean:1814` | `redSoundGen` chain-REPLACE IH residual | **RETIRE with cluster** — recursion realized on the genReduct side (master keys, laps 152–153). |
Retirement = judge deletes the decls + their dead downstream consumers (audit: nothing outside
the cluster references them; `blueprint_audit` must stay green after deletion).

### Group 3 — LIVE Route-A crux-2 frontier — KEEP as disclosed decomposition (6 sites)
These are the named decomposition of `false_of_ZDerivesEmpty`'s builder (the structural escape
set + master-key no-redex cases + the M2 entry bridge). They are the *active* Route-A frontier —
deleting them would erase the decomposition, not debt. Not currently mandated (growth route is),
but not retirable.
| site | decl | status |
|---|---|---|
| `Crux2Blueprint.lean:1931` | `foundation_bot_to_Z_empty` | KEEP — the M2 embedding entry (Foundation ⊥-derivation → Z). |
| `Crux2Blueprint.lean:3691` | `ind_reduct_anySucc` | KEEP — named leaf 1 (generalized Ind reduct off `seqSucc = ⊥`). |
| `Crux2Blueprint.lean:4542/4546/4548/4550` | `GenReductCert (zK …)` no-redex arms | KEEP — §14.254b replace-recursion cases (the genuine wall, lap-148 record). |

### Group 4 — superseded pin / live Phase-3 wall (2 sites)
| site | decl | proposal |
|---|---|---|
| `OperatorZeh.lean:1925` | `cutElimPass_Zf` (pin 3, lap-5 entrance gate) | **RETIRE (SUPERSEDED)** — `cutElimPass_Zef2` (`OperatorZef2.lean:1105`, via `passAux`) is now a REAL kernel-clean theorem `[propext, choice, Quot.sound]` (fresh `#print axioms`, 2026-07-03) at the upgraded Zef2 judgment; no consumer of `cutElimPass_Zf` exists outside `OperatorZeh.lean`. LOCK-owned → judge amends the LOCK + deletes (or downgrades to a historical comment). ⚠️ Same check exposed STALE comments in `OperatorZef2.lean` (lines 20, 363, 1103: "pass stays `sorry`/three sub-sorries") — judge should refresh them; the pass is sorry-free. |
| `DescentSemantic.lean:582` | `no_min_descent_absurd_of_goodstein` | **KEEP** — the lone Phase-3 wall (Rathjen §3 inside `M`), discharge plan documented in-file. Feeds the `goodstein_implies_consistency` girder (Route independent of the growth splice). Genuinely open math, correctly stated; not retirable, not superseded. |

**Net if all proposals executed**: 15 → 8 src sorries (Groups 1+2+pin-3 gone), every survivor a
live, correctly-stated frontier obligation.

---

## Block 5 — SERIES-4 judge package: COMPLETE (lap 212)

Per DIRECTION §4 STOP condition: **S-5 ledgered** (Block 1: `wainer_bound_witness` at the
axiom's verbatim type, kernel-clean, hypothesis pairing table + transcripts) · **B-1 ledgered**
(Blocks 2–3: base cases kernel-only, src swap executed, ofReduceBool OFF the growth chain) ·
**B-2 ledgered** (Block 4: all 15 sites classified with proposals). Judge-gated remainder (grind
FORBIDDEN, untouched): the src axiom→theorem swap in `WainerRoute.lean`, the rung-C crown
re-point, `Statement.lean`, all deletions. The SERIES-4 judge pass can execute from this ledger
alone.
