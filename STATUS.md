# STATUS — GoodsteinPA 📊

**Kirby–Paris: `𝗣𝗔 ⊬ Goodstein`, via Towsner's Route B (two-phase: witness-FREE `Z_∞` ε₀
cut-elimination [M5, done] + Hardy lower bound on the cut-free result [M6, done], joined by an
embedding [M4] + a bounding bridge).** · **Build**: 🟢 green (1257 jobs, `lake build GoodsteinPA`)
· **Updated**: lap 9 (deep-reflection) · 2026-06-22 · `1f32e49`

## Where it stands
Two of the three Phase-2 girders are **machine-checked and `#print axioms`-clean**: the ε₀
cut-elimination for the infinitary calculus (M5, `src/Zinfty.lean`) and the **full cut-free Hardy
lower bound, Towsner Thm 17.1, with no hypotheses beyond `α.NF`** (M6, `src/LowerBound.lean`:
`lowerBound_hardy_selfcontained`). Phase 0 (encoding + faithfulness bridge, M1) and Phase 1 (Gödel II
hook, M2) are landed and clean. The headline `Statement.peano_not_proves_goodstein` is **still a
literal `sorry`** (anti-fraud — correct; `#print axioms` = `[propext, sorryAx, choice, Quot.sound]`,
0 math axioms). **Lap-9 reflection course-correction:** laps 6–8 built three successive
witness-bounded cut-elim calculi (`BoundedZinfty→SplitZinfty→OperatorZinfty/Zekd`) chasing §19.6
`cutReduceAll`; the lap-8 findings PROVED that thread is off the critical path (single-index Hardy
inequality is false; literature never threads the witness index through cut-elim). **That thread is
now officially BANKED/abandoned** — do not resume `cutReduceAllAux`. The genuinely-remaining,
**universal** bottleneck — needed on *every* route (A, two-phase B, and Zekd) and untouched since
lap-6 recon — is **M4, the embedding `PA ⊢ φ ⟹ Z_∞ ⊢ φ`** (Foundation `Derivation` → `Provable`,
finite induction → ω-rule). That is the highest-value next target. The bounding bridge that joins
M5↔M6 shrinks to a single induction on the cut-free `Deriv` once M4 + the transparent arithmetization
(M7a) are in hand. See `REFLECTION-2026-06-22.md` and Outstanding.

## Route decision (lap 7) — STAY ON ROUTE B (Towsner)
The operator delegated Route A vs B to the box (`archive/findings/…operator-route-choice.md`). **Decision:
Route B.** Rationale: (1) the one genuinely-doubtful Route-B girder — the `(α,k)` cut-elimination
`k`/`τ` bookkeeping — was the reason to hesitate, and **lap 7 resolved it** (it is not a wall; `k`
simply grows and the lower bound holds for all `k` — see `ANALYSIS-2026-06-22-cutelim-k-threading.md`).
(2) M5+M6 are both Route-B assets already banked. (3) The remaining Route-B risk is M4 (embedding) +
M7a (the PA↔PA⁺ arithmetization bridge); Route A trades those for the full Gentzen `TI(ε₀)⊢Con(PA)` +
`Goodstein⟹TI(ε₀)` + the `PA_delta1Definable` Foundation axiom — a *larger* unproven surface, not
smaller. Revisit only if M7a proves intractable after sustained effort.

## What's happened (newest first)
- **2026-06-22 (lap 9 — DEEP REFLECTION: course-correct off the witness-bounded detour, name M4 as the
  universal bottleneck):** Took altitude. Read DIRECTION/STATUS/HANDOFF/PENDING + the lap-6→8 history +
  the cross-lap landscape memory + all three findings docs. **Findings:** (1) The destination
  (`peano_not_proves_goodstein` axiom-clean) is still right and worth it — net-new in Lean. (2) The
  **two-phase pivot (lap-8) is correct** and well-supported (Buchholz §5 / Schwichtenberg–Wainer Ch.4:
  never thread the witness index through cut-elim). (3) **But laps 6–8 fixated** on building/rebuilding
  witness-bounded cut-elim calculi (`BoundedZinfty→SplitZinfty→OperatorZinfty/Zekd`, ~3 laps), which the
  findings + landscape memory both show was **never on the critical path** — M5 (witness-free cut-elim)
  has been done & clean since lap 3. (4) The **real, universal, untouched bottleneck is M4** (embedding
  `PA ⊢ φ ⟹ Z_∞ ⊢ φ`): it is required on *every* route to the headline (A, two-phase B, Zekd), and has
  sat at "recon done lap 6" for 8 laps while the easier-but-off-path cut-elim thread absorbed effort.
  (5) **Architecture seam named:** M5 is over mathlib `Ordinal.{0}`+real `ℒₒᵣ`; M6 is over `ONote`+abstract
  `GForm` — the bridge must cross an ordinal-type seam + a language seam. **Reframe:** prove the bounding
  lemma *directly* on M5's real cut-free `Deriv` (reusing M6's `hardy_lt_goodsteinLength` ℕ-domination
  fact — the reusable core of M6 — not transporting into the abstract `B` calculus). **Decision:** STOP
  the `cutReduceAllAux`/Zekd thread (bank `wip/` as reference); next target = **M4 feasibility probe**,
  with **M7a (transparent arithmetization)** as the parallel shovel-ready / fallback thread. Refreshed
  STATUS + wrote `REFLECTION-2026-06-22.md` + rewrote HANDOFF to inherit the course change. Build green
  (1257), headline `sorry` intact, ledger re-confirmed by real `#print axioms`.
- **2026-06-22 (lap 8 — control-ordinal operator calculus built through §19.5; Hardy infra BANKED):**
  Resolved the **Hardy-infrastructure layer** of the §19.6 crux (both directions, axiom-clean, in
  `src/`): `hardy_add_comp`/`hardy_add_collapse` (`H_{γ+δ}=H_γ∘H_δ` for non-absorbing `γ+δ` — the
  cut-elim control collapse) and `hardy_comp_lt_goodsteinLength` (`H_α(H_e(m)) < G(m)` eventually, any
  NF `α,e` — the lower-bound nested-index domination, via `ω^Q·2` exceeding both + the coefficient law).
  Then built `wip/OperatorZinfty.lean`: the **control-ordinal operator calculus `Zekd α e k d c Γ`**
  (witness bound `hardy e (k+d)` decoupled from the derivation ordinal `α`), sorry-free through §19.5 —
  inductive + `mono_k/d/c` + the NEW **`mono_e`** (control-axis monotonicity, via the banked
  `hardy_le_of_lt`) + full inversion suite (orInv/andInvL/R/allInv) + §19.5 cutReduceConj/Disj + all
  §19.6/19.7 ordinal/norm helpers. **Design validated (`ANALYSIS-…-cutelim-k-threading.md` ADDENDUM 5):**
  the single control ordinal `e` (numeric Buchholz form, NOT the set-valued `H`) closes the ADDENDUM-4
  witness-index obstruction — commuting cases keep `e` inert, `e` rises only at the top cut via `mono_e`,
  the lower bound survives via `hardy_comp_lt_goodsteinLength`. **Remaining girder = §19.6 `cutReduceAll`
  on `Zekd`** (port `Zinfty.lean:785` + bounded bookkeeping); a NF-threading subtlety in the leaf cases
  surfaced (norm_add_le is NF-essential) — fix + 3 options recorded in ADDENDUM 5.
  **STRATEGIC PIVOT (ON-LINE-FINDINGS, end of lap 8):** the §19.6 commuting bound is **provably
  unclosable in any single-numeric-index system** (the Hardy inequality is FALSE; Towsner hand-waves it;
  `cutReduceAllAux`'s commuting cases hit exactly this). The literature-standard fix is **two-phase**:
  cut-eliminate on the witness-index-FREE calculus (**= M5, `src/Zinfty.lean`, DONE**) then Hardy-bound
  the CUT-FREE result (**= M6, DONE**). **The remaining critical-path work is the BRIDGE** (cut-free
  `Z∞ {gAll}` → `B`-derivation via subformula property + a Hardy bounding lemma → contradiction), NOT the
  witness-bounded cut-elim. `Zekd`/`SplitZinfty` are now banked alternatives. See `PENDING_WORK.md` top.
- **2026-06-22 (lap 7, cont. — §19.6 norm ingredient PROVED; commuting-case frontier mapped):**
  Proved `norm_addAux_le` and `norm_add_le {α γ NF} : norm(α+γ) ≤ norm α + norm γ` (axiom-clean; the
  `τ(α#β)≤τα+τβ` budget fact; NF essential — NF-free version machine-checked FALSE, eq-merge killed by
  additive-principality absorption). `wip/BoundedZinfty.lean` now **sorry-free**. Then, starting
  `cutReduceAll`, **uncovered a genuine §19.6 obstruction**: the `allω`-commuting case cannot preserve
  the ω-rule's `max{k,n}` norm budget after adding `α` to the bound (`norm(α+βₙ)~norm α+n > max K n` for
  large `n`). Towsner's "follows from IH" glosses this; the fix needs Buchholz operator-control or a
  controlled `Zk.allω` index. Precisely characterized + 3 attack options in
  `ANALYSIS-2026-06-22-cutelim-k-threading.md` ADDENDUM; `ON-LINE-REQUEST` re-filed (one layer down).
  Then proved two Hardy domination lemmas (`hardy_add_ofNat`, `hardy_shift_lt_goodsteinLength`, banked in
  `src/`, axiom-clean, build green 1257). **Tried + ELIMINATED option 2** (global index swap `max k n →
  k + n`): fixes §19.6-commuting but breaks `allInv` (needs `max`'s idempotence; `+` ⟹ slope-2 index ⟹
  lower bound needs multiplicative rescaling). Derived + **IMPLEMENTED** the split-index
  `(k,d)` design (`wip/SplitZinfty.lean`, 665 lines, sorry-free): calculus `Zkd` + `mono_k/d/c` + full
  inversion suite + §19.5 cut-reductions + all §19.6/19.7 ordinal/norm/descent helpers. `allInv`'s
  principal case compiling validates the split end-to-end for the inversion layer. **BUT — ADDENDUM 4 —
  `(k,d)` is insufficient for §19.6 `cutReduceAll`**: it closes the norm-budget obstruction (the
  `d`-bump) but NOT the *witness-index* one (the principal cut's witness `hardy γ(·)` makes the k-part
  grow super-linearly through commuting ω-rules; `max k n` can't absorb it). **Next: the full Buchholz
  operator calculus** (`hardy`-closed witness-index `H` + the additive `d`); §19.2–19.5 port mechanically
  from `SplitZinfty`. See `ANALYSIS-…-cutelim-k-threading.md` ADDENDA 1–4.
- **2026-06-22 (lap 7 — cut-elim `k`/`τ` crux RESOLVED, offline):** Read Towsner §15–§20 on disk and
  answered the open `ON-LINE-REQUEST` directly. **Finding:** the lap-6 "norm grows under addition so
  cut-elim might break `norm<k`" worry was a misframing. (a) `k` is **not** fixed — it grows (§19.5
  `k↦2k`; §19.6 `k↦h_{β#ω}(k)`; §19.7 `k↦h_{ω^α}(k)`), engineered to absorb `τ(α#β)≤τ(α)+τ(β)`.
  (b) The lower bound `lowerBound_hardy_selfcontained` is already `∀k`, so growth is harmless.
  (c) Every `ONote` is `<ε₀` by construction, so the ε₀ side-condition is **free**. ⟹ state the whole
  cut-elim chain **existentially in `k`** (`CutFree α Γ := ∃k, Zk α k 0 Γ`); ordinary `+` with slack
  suffices (no `nadd` needed). `ON-LINE-REQUEST` closed; route chosen (B). See
  `ANALYSIS-2026-06-22-cutelim-k-threading.md`. **§19.6/§19.7 port now unblocked.**
- **2026-06-22 (lap 6 — review + build-out):** **M6 lower-bound half DONE** — promoted
  `wip/LowerBoundHardy.lean → src/GoodsteinPA/LowerBound.lean`; `lowerBound_hardy_selfcontained` =
  full Towsner Thm 17.1, only `α.NF` (axioms = trust base + 🟢 `native_decide` base cases). Then
  **built the step-1 keystone** `wip/BoundedZinfty.lean`: the **witness-bounded calculus `Zᵏ` over real
  `SyntacticFormula ℒₒᵣ`** (ONote-indexed, B-style, with the truth rule `τ α<k` + `∃`-witness bound
  `v≤h_α(k)` + cut) and its whole §19.2–19.5 cut-elim front: `mono_k`/`mono_c`/`wk`/`weakening`, the
  **full inversion suite** (∨, ∧-L/R, ∀ — all axiom-clean), and the **§19.5 ∧/∨ cut-reductions**
  (`cutReduceConj`/`Disj`, axiom-clean). **Finding:** the `ω^α` blow-up preserves the `norm<k` budget
  (`norm(ω^α)=max(norm α,1)`, machine-checked) but ordinal *addition* bumps it (`norm(ω+ω)=2`) — so
  §19.6's bound bookkeeping needs care (filed `ON-LINE-REQUEST.md` for Towsner's precise `τ`/`k`
  threading). Remaining: §19.6 (∀/∃ reduction) + `cutElimStep`/`cutElim`, then M4 + M7.
- **2026-06-22 (lap 5):** RESOLVED the gAll/I∀ lower-bound frontier (the lap-4 wall), machine-checked.
  Ported the Hardy hierarchy → `src/Hardy.lean` (`hardy`/`norm` = Towsner `h_α`/`τ`); built the
  witness-bounded calculus `B` over `ONote` with the **concrete** Hardy data; proved
  `lowerBound_existential_hardy` (∀-free, zero abstract hyps), `B.allInv` (∀-inversion), and
  `lowerBound_hardy` (full Thm 17.1 mod `Hdom`). Resolution = **invert `gAll` away, don't accumulate**
  (a set-sequent `gAll` lets the ω-rule re-expand at a reachable index & `trueR`-close). Ported the
  Goodstein-dominates-fastGrowing chain → `src/Domination.lean`. (`ANALYSIS-2026-06-22-bounding-resolution.md`.)
- **2026-06-22 (lap 4):** Ground-truthed Towsner §10–§19 vs the Lean. Found + machine-checked
  (`wip/WitnessBound.lean`) the **witness-bound gap**: the M5 `(α,c)` cut-elim is OFF the headline path
  (unbounded `∃` ⇒ lower bound false for it). Built the corrected witness-bounded calculus, proved the
  ∃-fragment lower bound, proved the unbounded calculus collapses (`unbounded_proves_goodstein`).
- **2026-06-22 (lap 3):** Proved the ENTIRE Z_∞ cut-elimination (Towsner §19), zero sorries,
  axiom-clean: inversions + cut reductions §19.5 (∧/∨) & §19.6 (∀/∃) + `cutElimStep` §19.7 + `cutElim`
  §19.9. `Ordinal.nadd` ABSENT in mathlib v4.31.0 → ordinary `+` with `+1` slack (additive principality
  of `ω^c`). Promoted `wip/ZinftyF.lean → src/GoodsteinPA/Zinfty.lean`. (M5 ✅)
- **2026-06-22 (lap 2):** Built the real `Z_∞` calculus over Foundation's `SyntacticFormula ℒₒᵣ` with
  set sequents; proved all three inversion lemmas (§19.2–19.4); reduced cut-elim to `cutElimStep`.
- **2026-06-22 (lap 1):** M1 (`goodsteinTerminates_re`, Phase 0 axiom-clean), M2 (`Reduction.lean`
  Gödel II hook), Phase-2 decomposition doc (Towsner-grounded ladder).

## Outstanding
M5 (witness-free ε₀ cut-elim) and M6 (Hardy lower bound) are both **done & clean** but live on
disconnected substrates (M5: `Ordinal`+`ℒₒᵣ`; M6: `ONote`+`GForm`). The two-phase route joins them via
an embedding (M4) + a bounding bridge. Priorities are now **hardest-first = unavoidable-first**:

### Short-term (mirror PENDING_WORK top) — the universal bottleneck first
1. **M4 — embedding `PA ⊢ φ ⟹ Z_∞ ⊢^{α}_c {φ}`** (α<ε₀, finite c), Towsner §16/§18 / Buchholz §5.5.
   **THE highest-value target: required on every route, untouched since lap-6 recon.** Induct on
   Foundation's finitary `Derivation`; map rules to `ZinftyF.Provable` (axL/verumR/andI/orI/cut are
   structural); the crux is **finite induction axiom → ω-rule** (the lap-6 "derivation-substitution"
   2nd-deep-case). Lap-9 plan: write the embedding skeleton, get structural cases green, isolate the
   induction-axiom case as the disclosed `sorry` crux = a clean feasibility readout on the deepest
   unknown. **Banks nothing toward the dead witness-bounded thread.**
2. **M7a — transparent arithmetization** (parallel / fallback to M4; shovel-ready, faithfulness-gated).
   Headline `goodsteinSentence = ∀⁰ (codeOfREPred goodsteinTerminates)` is an **opaque Σ₁** blob; the
   calculus / bounding bridge needs a **transparent Π₂** `gAllReal = ∀x∃y[g_y(x)=0]` + `𝗣𝗔 ⊢
   goodsteinSentence ↔ gAllReal`, gated by `Bridge.lean`'s spec so faithfulness can't regress. Pure
   arithmetization over Foundation's Σ₁ tools — no deep proof theory, real committed progress, and good
   recon for M4's Foundation-`Derivation`/term-encoding API.
3. **Bounding bridge (small, once 1+2 land)** — prove `cut-free Provable α 0 Γ` (Γ in the g-fragment)
   ⟹ ∃-witnesses `≤ hardy (toONote α) N`, by induction on the cut-free `Deriv` (allInv the ∀ away, read
   the `exI` witness numeral off — no `+α` growth, the whole point of cut-freeness), then combine with
   M6's `hardy_lt_goodsteinLength` (`G(n) > hardy α N` eventually) ⟹ `False`. **Prove it on M5's real
   `Deriv` directly**; reuse M6's ℕ-domination fact, NOT the abstract `B`-calculus transport. The
   abstract `B` lower bound (`lowerBound_hardy_selfcontained`) is the *template* for this induction, now
   a banked reference like the witness-bounded calculi.
4. **Assembly (M7b)** — chain M4-embed ⟹ M5-cutElim ⟹ bounding bridge ⟹ contradiction with M6 ⟹
   discharge the headline `sorry`. Only then, only if `#print axioms` is clean.

### Long-term / banked
- **Ordinal-type reconciliation** for the bounding bridge: M5's cut-free `α : Ordinal.{0}` (`<ε₀`) must
  feed M6's `ONote`-based `hardy`. Either a standalone `∀ α<ε₀, ∃ o:ONote, o.NF ∧ o.repr = α`
  (`ONote.repr` surjectivity onto `[0,ε₀)` — check mathlib first) applied once at the end, or re-state
  the bounding lemma's ordinal in `ONote`. Light (one `toONote` at the leaf), not a calculus rebuild.
- **BANKED (do NOT resume):** the witness-bounded cut-elim thread — `wip/{BoundedZinfty,SplitZinfty,
  OperatorZinfty}.lean`, `Zekd cutReduceAllAux`. Proven off the critical path (findings + landscape).
  Kept in `wip/` as reference (§19.2–19.5 ports, `mono_e`, inversion suites); never on the headline path.
- **Route A** (`goodstein_implies_consistency` in `Reduction.lean`, via `Con(PA)` + Gödel II) stays as
  the documented escape hatch; it re-introduces the `PA_delta1Definable` Foundation axiom (🟡) and also
  needs M4. Revisit only if M4 + M7a prove intractable after sustained effort.

### To completion
Headline discharged ⟺ M4 (embedding) + M7a (transparent arithmetization) + the bounding bridge + M7b
(assembly) land AND `#print axioms peano_not_proves_goodstein` is `[propext, Classical.choice,
Quot.sound]` (+ the documented `native_decide` Goodstein base-cases from the domination path — 🟢 finite
witnesses; no `PA_delta1Definable` on Route B).

## Axiom ledger (per headline / landmark theorem — the fidelity spine)
| theorem | paper claim | `#print axioms` shows | status |
|---|---|---|---|
| `peano_not_proves_goodstein` (headline) | uncond. (Kirby–Paris) | `propext, sorryAx, choice, Quot.sound` | 🔓 open `sorry` — M4 + M7a + bounding bridge + assembly remain; **0** real math axioms |
| `goodsteinSentence_faithful` (bridge) | encoding correctness | `propext, choice, Quot.sound` | 🟢 clean (trust base) |
| `goodsteinTerminates_re` (M1) | r.e. of termination | `propext, choice, Quot.sound` | 🟢 clean |
| `Deriv.Provable.cutElim` (M5, §19.9) | ε₀ cut-elimination | `propext, choice, Quot.sound` | 🟢 clean — over real `ℒₒᵣ`, witness-FREE `(α,c)`; used **as-is** on the two-phase path (NO `k` retrofit) |
| `hardy_le_of_lt` (M6, `src/Hardy`) | Hardy index monotonicity (Hmono) | `propext, choice, Quot.sound` | 🟢 clean |
| `lowerBound_existential_hardy` (M6) | ∃-fragment 17.1, concrete Hardy/`G` | `propext, choice, Quot.sound` | 🟢 clean — zero abstract hyps |
| `B.allInv` (M6) | ∀-inversion (I∀-frontier resolution) | `propext, choice, Quot.sound` | 🟢 clean |
| `lowerBound_hardy` (M6) | full Thm 17.1 mod `Hdom` | `propext, choice, Quot.sound` | 🟢 clean |
| `lowerBound_hardy_selfcontained` (M6, **lap 6**) | **full Thm 17.1, only `α.NF`** | `propext, choice, Quot.sound` + 12 `native_decide` base-case `ax_*` | 🟢 clean — the `ax_*` are 🟢 finite Goodstein base-case witnesses (acceptable indefinitely) |
| `hardy_add_comp`/`_collapse` (lap 8, `src/Hardy`) | `H_{γ+δ}=H_γ∘H_δ` (non-absorbing) | `propext, choice, Quot.sound` | 🟢 clean — banked Hardy infra (was for the dead Zekd thread; still a usable composition law) |
| `hardy_comp_lt_goodsteinLength` (lap 8, `src/LowerBound`) | `H_α(H_e(m)) < G(m)` eventually | `propext, choice, Quot.sound` + the M6 `native_decide` base-cases | 🟢 clean — banked nested-index domination (reusable if a bridge ever needs a nested control index) |
| `not_proves_of_implies_consistency` (Route A) | meta-reduction | `…, PA_delta1Definable` | 🟡 Foundation axiom; **Route A only** — Route B avoids it |

Math-axiom count on the (eventual) Route-B headline target: **0** beyond the trust base + the 🟢
`native_decide` Goodstein base-case witnesses on the domination path. The `sorryAx` on the headline is
the honest open marker. `PA_delta1Definable` (🟡) sits only under the unused Route-A hook.

## Pointers
ROADMAP/plan: `EXPEDITION-PLAN.md`, `PHASE2-DECOMPOSITION.md` · **lap-9 reflection (course change):
`REFLECTION-2026-06-22.md`** · architecture: `ANALYSIS-2026-06-22-bounding-resolution.md` · newest
baton: `HANDOFF.md` · open-items: `PENDING_WORK.md` · charter: `DIRECTION.md`
