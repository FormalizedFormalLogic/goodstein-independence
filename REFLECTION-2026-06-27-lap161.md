# Reflection — 2026-06-27 (lap 161, DEEP REFLECTION, every-9th; prev altitude lap-158)

Altitude pass. Build re-verified 🟢 green (1326 jobs, `lake build GoodsteinPA`, exit 0). Real
`#print axioms` (in-kernel, `lake env lean`):

| theorem | `#print axioms` | reading |
|---|---|---|
| `peano_not_proves_goodstein` (headline) | `[propext, sorryAx, choice, Quot.sound]` | bare-sorry headline — 0 math axioms |
| `peano_not_proves_consistency` | `[propext, choice, Quot.sound]` | CLEAN (Gödel II hook) |
| `goodsteinSentence_faithful` | `[propext, choice, Quot.sound]` | CLEAN (faithfulness spine intact) |
| `false_of_ZDerivesEmpty` (crux-2) | `[propext, sorryAx, choice, Quot.sound]` | 0 math axioms, 6 live sorries |

No cited math axioms anywhere — the project uses disclosed sorrys, not smuggled axioms. Good discipline.

---

## 1. The direction call

**KEEP** the existence-form / constructive-`GenReductCert` pivot off `red`, and the focus on driving
`false_of_ZDerivesEmpty` (crux-2 / M1b-term) to 0 sorries. But the binding lap-158 directive was
**STALE and internally contradictory**, and I have re-synced it (`DIRECTION.md` CURRENT DIRECTIVE, lap-161).

### The core finding: the {3,4}-producer core is CRACKED; the directive didn't know it

Within lap 158, the *review* half wrote a directive mandating a **"design spike FIRST → OUTER induction on
the degree `idg`"** (standard Buchholz double-induction; the hypothesis being that the missing `irk < idg`
headroom comes from eliminating highest-rank cuts first). But the *spike* half of the SAME lap (`9ac1bf3`,
`wip/GenReductAnySucc.lean`) found the **opposite**:

> the genReduct generalization off `seqSucc=⊥` closes by the EXISTING CODE-induction — NOT an outer
> degree-induction. The {3,4} producer closes via `certReplace_of_premise_cert`, whose flatten rank-headroom
> comes from the PREMISE's own `irk+1 ≤ idg(premise)`, NOT the chain's degree.

Laps 159-160 followed the spike (correctly) and **wired + closed the {3,4}-producer core in-kernel**:
`repProducerClose` (Crux2Blueprint:3455) `:= Or.inl (certReplace_of_premise_cert … (IH m …))`, non-sorried,
**consumed in the live dispatch** at `:3578-3581` (tag-3 zInd / tag-4 zK → `repProducerClose`). Build green.

So "the irreducible {3,4}-producer cut-reduction = Buchholz Thm 2.1, the heart of crux-2" that the directive
still describes as the open frontier **is closed**. The directive text never got updated to reflect its own
spike's overturning of its own hypothesis. The grind laps were working PAST the directive — which means the
directive had stopped steering. That is exactly the failure mode a reflection lap exists to catch.

### What the open `residual` actually is now

`residual` (:3451) and the ⊥-version `axMajorResidual` (:3735) are reached ONLY for the **structural escape
set** (read the dispatch at :3550-3618):
- **(i) ⊥-exit ex-falso** — a tag-0/7 leaf (or tag-5 escape) puts `⊥∈Γ` / `^∀⊥∈Γ`; `⊥∈Γ ⟹ Γ→C` has **no
  single Z-rule** (the lone ex-falso `zAxNeg` needs a complementary `¬q,q` pair, not bare `⊥`). This is the
  ONE genuinely-new piece — needs an internal **⊥-elim / weakening** lemma (lap-160 finding #2).
- **(ii) C-exit R-intro replay** — a tag-1/2 major produces the conclusion succedent `C` directly.
- **(iii) tag-5 climb-escape / tag-6 partial thread** — shared between `residual` and `axMajorResidual`.

This is admissible-rule structural work, **not** the deep cut-elimination core. The deep core is done.

---

## 2. Are we attacking the highest-value thing?

Yes — crux-2 (`false_of_ZDerivesEmpty`) is the deepest, feasibility-in-doubt piece (it is the internal core
of Rathjen girder #2, `PRWO(ε₀)→Con(PA)`), and hardest-first justifies it. The trajectory is **genuine forward
motion, not circling**: residual content shrank monotonically — general `Γ→⊥` cut-elim (lap 148) → tag-5/6
cut-partner (154) → {3,4} producer + escapes (157) → **escapes only, producer closed** (160). Real narrowing.

**One honest blemish:** laps 155-160 closed many SUB-cases inside lemmas but the whole-lemma src sorry count
went **4 → 6** (the 3 anySucc leaves were added as scaffolding for the off-`⊥` generalization). No whole-lemma
sorry has DROPPED since lap 153/154. The success metric is a whole-lemma DROP; the next laps must deliver one.

---

## 3. What a sharp outside expert would flag (the altitude value-add)

1. **The directive was the bug, not the math.** The grind laps were RIGHT (they followed the spike). The
   directive lagged its own evidence. Fixed: re-synced `DIRECTION.md` to name the closed producer and the
   structural-escape frontier. This is the load-bearing deliverable of the lap.

2. **The six sorries are NOT independent — one structural lemma + the port collapses four of them.** `residual`
   (:3451) and `axMajorResidual` (:3735) share content (iii); and the anySucc generalization is designed so
   that once the 3 anySucc leaves (`ind_reduct_anySucc` :3382, `genReduct_chain_hasRedex_anySucc` :3391,
   `genReduct_chain_noRedex_anySucc` :3407) close, `genReduct_botSucc`/`genReduct_anySucc` become thin wrappers
   that DROP `axMajorResidual` (:3735) AND its Γ=∅ twin `descent_step_K_noncrit_axMajor` (:4180, same content).
   So the highest-leverage single target is the internal **ex-falso/weakening** lemma — the one new piece of
   `residual` — built as a standalone reusable Z-lemma (mirror the `leafCloseC`/`axNegCloseGen` cert shape at
   :3462/:3473). gDef (:4309) is the separable fifth piece (definability via primrec witness-bound or a
   constructive reduct, NOT μ-min — refuted lap-139).

3. **The dominant remaining UNKNOWN is the bridge, not the crux.** Even a sorry-free `false_of_ZDerivesEmpty`
   is not the headline. `goodstein_implies_consistency` (`Reduction.lean:68`) is a BARE sorry, and
   `false_of_ZDerivesEmpty` is **not yet wired to it** — the M2/M4 embedding (PA-proof → `ZDerivesEmptyR`) is
   ~0% built (`Zinfty.lean:7` / `ZinftyGen.lean:7` literally say "does not yet connect to the headline"), and
   girder #1 (γ→PRWO, internal Cor 3.4) is only partly built. I weighed **pivoting to M2 now** (the crux's
   feasibility is largely de-risked, so the bridge is arguably the higher-variance bet). I decided **against**:
   `false_of_ZDerivesEmpty` is only a handful of structural sorries from a clean, citable milestone; abandoning
   it mid-flight to open a 0%-built bridge would be a thrash, and the standing operator forbid on M2/M4 holds.
   The disciplined call: **finish crux-2, then hand to an altitude lap to re-plan the bridge.** Recorded as the
   sharpened ALTITUDE CAUTION in the directive.

---

## 4. KEEP / STOP / next target

**KEEP:** the constructive `GenReductCert` cut-elimination; the in-kernel refutation discipline (this project
repeatedly kernel-refutes false sub-goals — e.g. the `seqUpdate` splice lap-151, the same-degree õ-drop
lap-157 — which is exactly right); per-lap `#print axioms` faithfulness re-verification; hardest-first on crux-2.

**STOP:** (a) treating the {3,4} producer / outer degree-induction as open — it's closed and the degree-induction
hypothesis was refuted by its own spike; do NOT rebuild or re-spike it. (b) Narrowing internal residuals without
dropping a whole-lemma src sorry — the next laps must DROP. (c) Obeying the stale lap-158 degree-induction mandate.

**Single highest-value next target:** build the internal **ex-falso / weakening** lemma
(`⊥ ∈ seqAnt s ⟹ ∃ d', ZDerivation deriving Γ→C`, finite-head ordinal that õ-drops vs `zK s r ds`; plus the
`^∀⊥∈Γ` variant), then wire it + the C-exit R-intro replay + a factored shared `threadEscapeClose` to CLOSE
`residual` (:3451). Reasoning: it is the ONE genuinely-new content in `residual`; everything else is reuse; and
closing `residual` is the first domino that (with the 2 other anySucc leaves) collapses four of the six sorries.

---

## 5. Faithfulness at altitude

Headline statement `peano_not_proves_goodstein : 𝗣𝗔 ⊬ ↑goodsteinSentence` (Statement.lean:22) — correct
Kirby-Paris statement, properly gated anti-vacuity (the docstring requires `goodsteinSentence` faithful + the
`(ℕ⊨γ)↔terminates` bridge, both present and axiom-clean: `goodsteinSentence_faithful` =
`[propext, choice, Quot.sound]`). No transcription drift detected. The standing deep risk (not auditable in one
lap) is whether the bespoke `InternalZ` Z-system + the ordinal assignment `iord`/`idg` faithfully realize
Buchholz's PA_∞; the project defends this with `native_decide` anchors + per-reduct soundness banking, which is
the right instrument. Flagged as a standing risk, not chased this lap.
