# STATUS — GoodsteinPA 📊

**Kirby–Paris: `𝗣𝗔 ⊬ Goodstein`, via Gentzen/Buchholz ordinal analysis — witness-FREE `Z_∞` (embedding
[M4 `embedC`, done] + ε₀ cut-elim [M5, done]) + **Boundedness** (Thm 5.4, DONE lap 14, axiom-clean) ⟹
`𝗣𝗔 ⊬ TI(ε₀)`, then Goodstein⟹TI(ε₀).** · **Build**: 🟢 green (1264 jobs, `lake build GoodsteinPA`)
· **Updated**: lap 15 (review) · 2026-06-22 · `f16d3be`

## ⏭️ Lap-15 focus — execute C₁/C₂, the connective tissue to Thm 5.6
The Buchholz Boundedness route (lap-12 pivot) is **half-done**: the two textbook-hard pieces M4 `embedC`
+ M5 `cutElim` were already axiom-clean, and **lap 14 added the crux Boundedness (Thm 5.4) + corollary B,
axiom-clean**. What remains to assemble **Thm 5.6 (`Z ⊢ TI_≺(X) ⟹ ‖≺‖ < ε₀` = `PA ⊬ TI(ε₀)`)** is the
**connective tissue**: **C₁** port `ZinftyGen.cutElim` to an `XFreeAx`-tracking, cut-rank-carrying `PXFc`
twin (reach cr=0 keeping `XFreeAx` — validated feasible lap 15, the `atomCut` truth-branch is vacuous on
`XFreeAx` inputs) and **C₂** port `embedC` to generic `LX` (X-induction axioms via the meta-induction
tower of cuts, NOT `provable_true` — would lone-X-`axTrue`). Then **E** Goodstein⟹TI bridge + **F** the
arithmetization seam (`‖≺‖=ε₀`, discharge `hprec`/`hprecXPos`) ⟹ headline. See newest `HANDOFF`.

## Where it stands
**THREE of the four hard pieces of the Buchholz §5 analysis are now machine-checked and `#print
axioms`-clean** and on the critical path: the **embedding** M4 `embedC` (Thm 5.5, `src/Embedding.lean`),
the **ε₀ cut-elimination** M5 `cutElim` (Thms 5.1–5.3, `src/Zinfty.lean` + generic `src/ZinftyGen.lean`),
and **lap 14's Boundedness** Thm 5.4 + corollary `Z∞⊢^β_1 TI ⟹ ‖≺‖≤2^β` (`src/Boundedness.lean`,
`boundedness`/`orderType_le_of_TIderiv`). Phase 0 (M1, `goodsteinTerminates_re` clean) + Phase 1 (Gödel II
hook) landed. The headline `Statement.peano_not_proves_goodstein` is **still a literal `sorry`** (anti-fraud
— correct; `#print axioms` = `[propext, sorryAx, choice, Quot.sound]`, 0 math axioms). The connective
tissue to assemble **Thm 5.6 = `PA ⊬ TI(ε₀)`** is C₁ (XFreeAx-preserving cutElim→cr=0) + C₂ (`embedC` over
LX); then the bridge (E, Goodstein⟹TI) + arithmetization seam (F, `‖≺‖=ε₀`). **Lap-12 pivot** (see route decision):
the project drifted (laps 4–11) into Towsner's witness-bounded variant and hit a genuine wall (§19.6
witness-budget needs the operator `H`). Buchholz §5 shows the witness-FREE route — M4+M5 (done) +
**Boundedness (Thm 5.4)** + Goodstein⟹TI(ε₀) — is the standard, shorter path. Next target = the truth
semantics `⊨^α` + Boundedness. M6 (Hardy lower bound) and the `wip/` witness-bounded calculi are banked
off-path. See `ANALYSIS-2026-06-22-lap12-buchholz-pivot.md` and Outstanding.

## Route decision (lap 12) — PIVOT to Buchholz's Boundedness route (RETRACTS the lap-7 Route-B choice)
**Decision: the Gentzen/Buchholz `TI(ε₀)` route, via Boundedness (Thm 5.4) on the witness-FREE `Z∞`.**
The lap-7 "stay on Towsner Route B" rested on a claim that **lap 12 falsified**: the `(α,k)` cut-elim was
NOT a resolved bookkeeping detail — its §19.6 commuting-ω case is provably unclosable with any numeric
control (ADDENDUM 7), needing the Buchholz operator `H` (multi-lap). Meanwhile Buchholz §5 shows the
witness-FREE route reuses **M5 cut-elim (done) + M4 `embedC` (done)** and needs only **Boundedness +
Goodstein⟹TI(ε₀)** — strictly less unproven surface than Towsner's `Zᵏ` + bounded-cut-elim + bridge, and
the textbook-standard analysis. M6 (Hardy lower bound) was the main "Route B asset" justifying the lap-7
choice, but it is Towsner-specific and now OFF the critical path (banked, not deleted). See
`ANALYSIS-2026-06-22-lap12-buchholz-pivot.md`. (Route A via `Con(PA)`+Gödel-II stays the documented
escape hatch; it re-introduces the `PA_delta1Definable` Foundation axiom 🟡.)

## What's happened (newest first)
- **2026-06-22 (lap 16 — C₂ STRUCTURAL PORT landed; the `exs` case mapped to a calculus retrofit):**
  Built `src/GoodsteinPA/EmbeddingX.lean` (green, one disclosed `sorry`): **`embedC_LX_gen`** — the
  `axm`-abstracted structural embedding of `Derivation2 𝓢 Γ` into `PXFc` over `LX`, all 9 structural
  cases (`closed` via `provable_em_x`; `verum/and/or/all/wk/shift/cut`; `axm` as hypothesis `hax`),
  every builder `XFreeAx`-safe — plus **`provable_true_x`** (ω-completeness for true closed **X-free**
  formulas, the X-free `axm` engine) and **`XFreeForm`** (structural X-freeness + rewriting-invariance).
  **Then ground-truthed the `exs` case against Buchholz §5 (PDF pp.26–30) and found the lap-15
  "mechanical" claim was wrong:** faithfully embedding Foundation's `exs` (arbitrary-term ∃-intro) over
  X-atom bodies needs Buchholz's **value-congruent X-pair axiom** `{Xs,¬Xt}` (`sᴺ=tᴺ`, `AX(Z∞)`, p.27),
  which our same-atom `Deriv.axL` lacks. The faithful fix is a calculus retrofit (generalise the literal
  axiom to value-congruent pairs `Deriv.axLv`); Boundedness case 1.2 (p.29) + cut-elim's literal-cut
  (Remark p.27) already handle them in Buchholz. **Probed the retrofit** (added `axLv` + threaded the
  ZinftyGen leaf branches): 5/8 sites mechanical, `atomCutAux` is the one hard spot, and the XFreeAx
  interaction is benign (reverted as an uncommittable mid-big-bang; it's a single-lap effort with no
  intermediate green). Headline still an honest `sorry`. See `ANALYSIS-2026-06-22-lap16-exs-axLv.md`.
- **2026-06-22 (lap 15 — FRESH-MIND REVIEW: validated the lap-14 cr=0 design against a feared
  obstruction; direction confirmed sound):** Took altitude. Re-derived the full Buchholz §5 chain and
  stress-tested the lap-14 architecture. **Nearly flagged a wall:** Boundedness is implemented at
  `d.cr = 0` (fully cut-free), whereas Buchholz states it at `⊢^β_1` (cut-rank ≤ 1, atomic cuts allowed,
  his case 8 = the X-atomic cut). The worry: getting a cr=0 `XFreeAx` derivation of `{TI}` needs cutElim
  to *eliminate X-atomic cuts*, and the truth-layer surgery (`removeFalseLit`) would emit `axTrue false
  Xsym` leaves — breaking `XFreeAx`. **Resolved by reading `atomCutAux`:** our `Provable.axL` is the
  *same-atom* EM axiom `{Xs,¬Xs}` (not Buchholz's value-matched `{Xs,¬Xt}`), so an X-atomic cut closes by
  **set idempotence** (the `axL` branch, no truth), and the truth-surgery branch is **vacuous under
  `XFreeAx`** (it fires only on an `axTrue` leaf *equal to* the cut atom — i.e. an X-`axTrue` leaf, which
  `XFreeAx` forbids). So `atomCut` preserves `XFreeAx` when cutting X-atoms on `XFreeAx` inputs, and the
  lap-14 C₁ plan (port cutElim to a `cr`-carrying `PXFc` twin, all the way to cr=0) is **feasible as
  written**. **Then GROUND IT OUT (same lap):** built `src/GoodsteinPA/XFreeCutElim.lean` (1456 lines,
  all `[propext,choice,Quot.sound]`) — **C₁ DONE** (the full §19 cut-elim ported to the `XFreeAx`-tracking
  `PXFc` carrier: builders + inversions-at-cr≤c + cut reductions + truth layer + `cutElim`), **D DONE**
  (`orderType_le_of_TIprovable` = Thm 5.6 tail), and the **C₂ crux** (`metaInduction`, the X-induction
  embedding via a cut-tower — the lap-14-flagged faithfulness case — + `provable_em_x`, LX excluded
  middle). Headline still an honest `sorry`. **Remaining to Thm 5.6: the C₂ structural `embedC` port.**
- **2026-06-22 (lap 14 — CRUX CRACKED: Boundedness Thm 5.4 + the full corollary B, axiom-clean):**
  Proved **`boundedness`** (Thm 5.4) — the 9-`Deriv`-case nested induction (outer strong-induction on the
  ordinal height `o d`, inner structural), hardest **case 2** (`¬Prog` `∃⁰`-inversion + the `α→α+2^{β₀}`
  rank bump) machine-checked — and **`orderType_le_of_TIderiv`**, the FULL corollary `Z∞ ⊢^β_1 TI_≺(X)
  ⟹ ‖≺‖ ≤ 2^β` (invert TI's `🡒`/`∀` via the new `XFreeAx`-preserving inversion suite `andInv_xfree`/
  `orInv_xfree`/`allInv_xfree`, feed Boundedness). Built the **`PXF`** carrier (cut-free `XFreeAx`-tracking
  provability + smart constructors). All 17 deliverables `[propext,choice,Quot.sound]`, no math axioms,
  modulo the two legitimate seam hypotheses `hprec`/`hprecXPos` (discharged at arithmetization, step F).
  This is Buchholz's crux done. Remaining to Thm 5.6: C₁ (XFreeAx cutElim→cr=0) + C₂ (`embedC` over LX).
- **2026-06-22 (lap 13 — Boundedness prerequisites; generic Z∞ over LX):** Read Buchholz §5 pp.26–31
  end-to-end. Shipped (green, axiom-clean, `src/`): **`LangX`** (`structLX (S:ℕ→Prop) : Structure LX ℕ`,
  the `⊨^S` carrier), **`ZinftyGen`** (M5 cut-elim **generalised over `{L}[ORing L][Structure L ℕ][DecEq…]`**,
  `Provable.cutElim` axiom-clean — reused wholesale on the X-route, no cut-elim re-proof), **`TruthSem`**
  (`rk`/`orderType`/`models (⊨^γ)`/`Sat` + X-free invariance `models_lMap`), **`XPositive`** (`XPos` +
  `models_mono`, the Buchholz cases 2/3/4 monotonicity). Confirmed VERIFY-(a): the set variable `X` is
  plumbing, not math. See `ANALYSIS-2026-06-22-lap13-boundedness-design.md`.
- **2026-06-22 (lap 12 — §19.6 norm-machinery PROVED + PIVOT to Buchholz's Boundedness route):** Reviewed
  the whole spine fresh. **(a)** Cracked the **norm-budget** half of the 5-lap §19.6 wall: proved
  `cutReduceAllAux` (Towsner's ∀/∃ cut-reduction) on the witness-bounded `Zekd` calculus, axiom-clean
  (`wip/OperatorZinfty.lean`) — via a self-derived **norm-carrying `ZekdProv` wrapper** + threaded
  `norm γ<k+dd` + `+1` d-bump (the plain `≤`-wrapper threw away the norm bound the `allω` reassembly
  needs, since `norm` isn't `≤`-monotone — the actual 5-lap blocker). **(b)** But feeding it from
  `cutReduceAll` exposed the **witness-budget** obstruction is REAL and numeric-unclosable (ADDENDUM 7;
  `allInv` gives the ∀-family at `max k₀ n`, Towsner's commuting-ω bound is false for large `n`) — needs
  the operator `H`. **(c) ⟹ Read Buchholz §5 and PIVOTED:** the witness-FREE `Z∞` + **Boundedness**
  (Thm 5.4) is the standard route and reuses **M4 `embedC` + M5 `cutElim` (both done, axiom-clean)**;
  lap-11's "need witness-bounded `Zᵏ`" was a conflation of order-type-boundedness (valid) with
  witness-boundedness (walled). New critical path = Boundedness + Goodstein⟹TI(ε₀); M6 (Hardy) drops off
  it. See `ANALYSIS-2026-06-22-lap12-buchholz-pivot.md` + ADDENDA 6/7. Build green; headline `sorry` intact.
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
  STATUS + wrote `REFLECTION-2026-06-22.md` + rewrote HANDOFF to inherit the course change. **Then
  started the M4 grind (post-synthesis):** `wip/Embedding.lean` — `embed : Derivation2 (𝗣𝗔:Schema) Γ →
  ∃ α c, Provable α c Γ` over the SAME `Finset (SyntacticFormula ℒₒᵣ)` substrate (no language
  translation). **6/10 cases proved** (verum/and/or/wk/cut/closed); **`provable_em` (Z∞ excluded-middle)
  FULLY PROVED + axiom-clean.** 4 deep cases remain (`axm`/`all`/`exs`/`shift`), all needing a shared M5
  renaming/subst lemma (the `Derivation.rewrite` analogue) = the next target. Build green (1257),
  headline `sorry` intact, ledger re-confirmed by real `#print axioms`.
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
  of `ω^c`). Promoted `wip/ZinftyF.lean → src/GoodsteinPA/Zinfty.lean`. (M5 ✅)  *(laps 1–2 trimmed —
  M1/M2/Phase-0-1 landed + the real `Z_∞` calculus & inversions built; see git history.)*

## Outstanding
**New route (Buchholz §5, lap-12 pivot).** M4 `embedC` (Embedding, Thm 5.5) and M5 `cutElim` (Thms
5.1/5.2/5.3) are **done & axiom-clean** and ARE the two hard pieces. Remaining = Boundedness + the
Goodstein⟹TI bridge. Priorities (see `ANALYSIS-2026-06-22-lap12-buchholz-pivot.md`):

### Short-term (mirror PENDING_WORK top) — execute the Buchholz route
0. **VERIFY-FIRST (lap 13, before deep work):** (a) M5/M4 cleanly take the set variable `X` (extend
   `ℒₒᵣ`→`ℒₒᵣ∪{X}`, or add `X` as a fixed extra relation symbol — `embedC`'s `axm`/`provable_true` only
   needs the `X`-free PA axioms, so it should extend); (b) the **Goodstein ⟹ TI_≺(X)** bridge's exact
   shape is provable in PA via the Phase-0 CNF-ε₀ encoding. Neither is a known wall; confirm before
   sinking laps.
1. **Truth semantics `⊨^α Γ`** — `X := {n : |n|_≺ < α}`, plus `Prog_≺`, the ≺-norm `|n|_≺`, order type
   `‖≺‖`, X-positivity. Light self-contained defs over `Z∞` sequents.
2. **Boundedness (Thm 5.4) — THE new theorem.** `Z∞ ⊢^β_1 ¬Prog_≺(X),¬Xs₁,…,¬Xsₖ,Γ & |sᵢ|_≺ ≤ α ⟹
   ⊨^{α+2^β} Γ` (Γ X-positive), by induction on the cut-free `Provable β 0`-derivation (8 cases, p.29 of
   Buchholz). Corollary `Z∞ ⊢^β_1 TI_≺(X) ⟹ ‖≺‖ ≤ 2^β`. No Hardy, no witness bound.
3. **Goodstein ⟹ TI_≺(X)** for the ε₀-order `≺` (the bridge) — PA ⊢ Goodstein-termination ⟹ PA ⊢
   `TI_≺(X)` (Goodstein descent = ε₀-descent; Kirby–Paris/Cichoń). Reuses Phase-0 encoding.
4. **Assembly:** PA ⊢ Goodstein ⟹ (M4) Z∞-deriv ⟹ (M5) cut-free at `β<ε₀` ⟹ (Boundedness) `‖≺‖≤2^β<ε₀`,
   but the ε₀-order has `‖≺‖=ε₀` ⟹ `False` ⟹ discharge the headline. Only if `#print axioms` is clean.

### Long-term / banked
- **BANKED, OFF the critical path (do NOT resume on the Buchholz route):** the witness-bounded cut-elim
  thread — `wip/{BoundedZinfty,SplitZinfty,OperatorZinfty}.lean`. Lap-12 `cutReduceAllAux` (norm-machinery,
  axiom-clean) is the furthest it got; closing it fully needs the operator `H` (ADDENDUM 7). Kept as
  reference for the operator-`H` build IF the Buchholz route ever stalls. **M6 (Hardy lower bound,
  `lowerBound_hardy_selfcontained`)** — Towsner-specific, a correct theorem, now OFF the critical path.
- **Route A** (`goodstein_implies_consistency` in `Reduction.lean`, via `Con(PA)` + Gödel II) stays as
  the documented escape hatch; it re-introduces the `PA_delta1Definable` Foundation axiom (🟡) and also
  needs M4. Revisit only if M4 + M7a prove intractable after sustained effort.

### To completion
Headline discharged ⟺ **Boundedness (Thm 5.4) + truth semantics + Goodstein⟹TI(ε₀) bridge + assembly**
land on top of the done M4 `embedC` + M5 `cutElim`, AND `#print axioms peano_not_proves_goodstein` is
`[propext, Classical.choice, Quot.sound]` (+ any documented `native_decide` Goodstein base-cases — 🟢
finite witnesses; no `PA_delta1Definable` on this route). M6 (Hardy) is no longer required.

## Axiom ledger (per headline / landmark theorem — the fidelity spine)
| theorem | paper claim | `#print axioms` shows | status |
|---|---|---|---|
| `peano_not_proves_goodstein` (headline) | uncond. (Kirby–Paris) | `propext, sorryAx, choice, Quot.sound` | 🔓 open `sorry` — **C₁ DONE (lap 15)**; C₂ (`embedC`/LX) + E (Goodstein⟹TI) + F (arithmetization seam) remain; **0** real math axioms |
| `goodsteinSentence_faithful` (bridge) | encoding correctness | `propext, choice, Quot.sound` | 🟢 clean (trust base) |
| `goodsteinTerminates_re` (M1) | r.e. of termination | `propext, choice, Quot.sound` | 🟢 clean |
| `Deriv.Provable.cutElim` (M5, §19.9, `src/Zinfty`) | ε₀ cut-elimination (ℒₒᵣ) | `propext, choice, Quot.sound` | 🟢 clean — witness-FREE `(α,c)` |
| `ZinftyGen.…Provable.cutElim` (M5-generic, lap 13) | ε₀ cut-elim over `{L}` | `propext, choice, Quot.sound` | 🟢 clean — the X-route carrier (`L=LX`); reused wholesale, no re-proof |
| `Boundedness.boundedness` (Thm 5.4, **lap 14**) | order-type Boundedness | `propext, choice, Quot.sound` | 🟢 clean — modulo seam hyps `hprec`/`hprecXPos` (discharged at F) |
| `Boundedness.orderType_le_of_TIderiv` (Cor B, **lap 14**) | `Z∞⊢^β_1 TI ⟹ ‖≺‖≤2^β` | `propext, choice, Quot.sound` | 🟢 clean — modulo `hprec`/`hprecXPos`; consumes a cr=0 `XFreeAx` `⊢{TI}` (C₁+C₂ supply it) |
| `embedC` (M4, `src/Embedding`) | PA⊢φ ⟹ Z∞⊢φ (ℒₒᵣ) | `propext, choice, Quot.sound` | 🟢 clean — needs C₂ generic-LX port for the X-route |
| `PXFc.cutElim` (C₁, **lap 15**, `src/XFreeCutElim`) | `XFreeAx` cut-elim → cr=0 | `propext, choice, Quot.sound` (+ `sorryAx` since lap 16) | 🟡 was clean for the same-atom calculus; lap-16 generalised the calculus to value-congruent literal axioms (`Deriv.axLv`), and `atomCutAux`'s value-cong **X-atom-cut** case is one disclosed `sorry` pending `nrel_value_subst` (value-cong negative-literal renaming). Clears to clean once that lemma lands. |
| `orderType_le_of_TIprovable` (D, **lap 15**) | Thm 5.6 tail `PXFc {TI} ⟹ ‖≺‖≤2^(ω_c^α)` | `propext, choice, Quot.sound` | 🟢 clean — C₁ ∘ corollary B; modulo seam hyps `hprec`/`hprecXPos` (F) |
| `provable_em_x` (C₂, **lap 15**) | `Z∞` excluded middle over LX | `propext, choice, Quot.sound` | 🟢 clean — `XFreeAx`-automatic (never `axTrue`) |
| `metaInduction` (C₂ crux, **lap 15**) | X-induction via cut-tower (Buchholz 5.5) | `propext, choice, Quot.sound` | 🟢 clean — the faithfulness-critical embedding step; abstract in `step` (Foundation-DSL glue ⟹ later) |
| `provable_true_x` (C₂, **lap 16**, `src/EmbeddingX`) | ω-completeness, true closed X-free ⟹ `XFreeAx` | `propext, choice, Quot.sound` | 🟢 clean — the X-free `axm` engine |
| `embedC_LX_gen` (C₂-struct, **lap 16**) | structural embedding `Derivation2 𝓢 Γ ⟹ PXFc` over LX | `propext, choice, Quot.sound` + `sorryAx` | 🔓 9/10 cases; `exs` disclosed `sorry` (needs the `axLv` value-congruent-literal retrofit — Buchholz `AX(Z∞)` p.27); `axm` abstracted as `hax` |
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
