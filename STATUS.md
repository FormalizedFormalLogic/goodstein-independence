# STATUS — GoodsteinPA 📊

**Kirby–Paris: `𝗣𝗔 ⊬ Goodstein`, via Gentzen/Buchholz ordinal analysis — witness-FREE `Z_∞` (embedding
[M4 `embedC`, done] + ε₀ cut-elim [M5, done]) + **Boundedness** (Thm 5.4, NEW) ⟹ `𝗣𝗔 ⊬ TI(ε₀)`, then
Goodstein⟹TI(ε₀).** · **Build**: 🟢 green (1258 jobs, `lake build GoodsteinPA`)
· **Updated**: lap 12 · 2026-06-22 · `605d5ba`

## ⏭️ Lap-12 — TWO findings: (a) §19.6 norm-machinery PROVED; (b) **PIVOT to Buchholz's Boundedness route** (reuses M4+M5, avoids the wall)
**(a)** Proved Towsner's §19.6 ∀/∃ cut-reduction core `cutReduceAllAux` on the witness-bounded `Zekd`
calculus (`wip/OperatorZinfty.lean`, axiom-clean), cracking the **norm-budget** half of the 5-lap wall
via a **norm-carrying `ZekdProv` wrapper** + threaded `norm γ<k+dd` + `+1` d-bump (ADDENDUM 6). **But**
the **witness-budget** half (ADDENDUM 7) is provably NOT closable with any numeric control (single `k`,
`(k,d)`, or single control ordinal `e`): `allInv` yields the ∀-family at index `max k₀ n`, and Towsner's
commuting-ω bound `h_{βₙ#ω}(max{k,n}) ≤ max{h_{β#ω}(k),n}` is FALSE for large `n`. Closing it needs the
Buchholz set-operator `H` — a multi-lap build. **(b) ⟹ PIVOT (see `ANALYSIS-2026-06-22-lap12-buchholz-
pivot.md`).** Reading Buchholz "Beweistheorie" §5 shows the STANDARD Gentzen analysis bounds PA's ordinal
via the **witness-FREE** `Z∞` + a **Boundedness** theorem on `TI_≺(X)` — exactly **M5 (cut-elim, done) +
M4 `embedC` (done)** + one new clean induction (Thm 5.4). The lap-11 "embedC is the wrong object / need
witness-bounded `Zᵏ`" verdict was a **conflation**: lap 11 killed naive *witness*-extraction (height ≠
witness bound), but Buchholz's Boundedness bounds the **order type** of `≺` via the set variable `X` +
X-positive truth semantics `⊨^α` — sidestepping witnesses entirely. **New critical path: Boundedness
(Thm 5.4) + Goodstein⟹TI(ε₀); drop the witness-bounded wall + M6 (Hardy) off the critical path.** This
returns to `DIRECTION.md`'s original Gentzen/TI(ε₀) plan. Headline still an honest `sorry`.

## ⏭️ Lap-10 headline — M5 `axTrue` truth-layer surgery DONE (read `ANALYSIS-2026-06-22-truth-layer-gap.md`)
Uncovered + closed the **truth-layer gap**: M5's pure-logic `Z_∞` couldn't host the embedding (`axm`
needs *true closed atomic* axioms like `nm n + 0 = nm n`, which `Deriv` lacked). The fix is now
**implemented and axiom-clean**: `Deriv.axTrue` (ω-logic atomic-truth leaf) + a truth-layer
cut-elimination (`removeFalseLitAux`, `atomCutAux` truth split) — `cutElim` = `[propext, choice,
Quot.sound]`, no `sorryAx`. **M5 now hosts the embedding.** Next: the **assignment-carrying (all-closed)
embedding** (`∀ e, ZProvable (Γ.image (ρe ▹))`) — discharges `axm` (via `axTrue`) and `exs` (closed-term
collapse); supersedes the naive open `provable_rew`. M4 enabler `rew_subst_nm` also discharged this lap.

## Where it stands
The two hardest pieces of the standard Gentzen/Buchholz analysis are **machine-checked and `#print
axioms`-clean and ON the (lap-12-pivoted) critical path**: the **embedding** `PA ⊢ φ ⟹ Z∞ ⊢ φ` (M4
`embedC`, `src/Embedding.lean` — Buchholz Thm 5.5) and the **ε₀ cut-elimination** for the witness-free
infinitary calculus (M5, `src/Zinfty.lean` — Buchholz Thms 5.1/5.2/5.3). Phase 0 (encoding + faithfulness
bridge, M1) and Phase 1 (Gödel II hook, M2) are landed and clean. The headline
`Statement.peano_not_proves_goodstein` is **still a literal `sorry`** (anti-fraud — correct; `#print
axioms` = `[propext, sorryAx, choice, Quot.sound]`, 0 math axioms). **Lap-12 pivot** (see route decision):
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
  of `ω^c`). Promoted `wip/ZinftyF.lean → src/GoodsteinPA/Zinfty.lean`. (M5 ✅)
- **2026-06-22 (lap 2):** Built the real `Z_∞` calculus over Foundation's `SyntacticFormula ℒₒᵣ` with
  set sequents; proved all three inversion lemmas (§19.2–19.4); reduced cut-elim to `cutElimStep`.
- **2026-06-22 (lap 1):** M1 (`goodsteinTerminates_re`, Phase 0 axiom-clean), M2 (`Reduction.lean`
  Gödel II hook), Phase-2 decomposition doc (Towsner-grounded ladder).

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
