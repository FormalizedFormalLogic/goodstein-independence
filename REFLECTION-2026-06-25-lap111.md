# REFLECTION — lap 111 (DEEP, every-9th) · 2026-06-25

> Strong-model altitude lap. Job: take stock of the WHOLE project, not the next `sorry`.
> Build re-verified green (1326). Headline footprint re-verified IN-KERNEL this lap
> (`lake env lean`): `peano_not_proves_goodstein = [propext, sorryAx, Classical.choice, Quot.sound]`
> — **0 math axioms**. Statement faithfulness re-audited vs the paper — **no drift** (details below).

---

## 0. The kernel facts I actually re-verified this lap (not from docs)

| theorem | real `#print axioms` (lap 111, `lake env lean`) |
|---|---|
| `peano_not_proves_goodstein` (headline) | `[propext, sorryAx, Classical.choice, Quot.sound]` — 0 math axioms |
| `goodstein_implies_consistency` (the lone open girder) | `[propext, sorryAx, Classical.choice, Quot.sound]` |
| `peano_not_proves_consistency` (Gödel-II hook) | `[propext, Classical.choice, Quot.sound]` — **CLEAN** |
| `not_proves_of_implies_consistency` | `[propext, Classical.choice, Quot.sound]` — CLEAN |
| `goodsteinSentence_faithful` (anti-vacuity anchor) | `[propext, Classical.choice, Quot.sound]` — CLEAN |

**Statement audit (charter item 4).** `peano_not_proves_goodstein : 𝗣𝗔 ⊬ ↑goodsteinSentence`;
`goodsteinSentence = “∀ m, ∃ N, !igoodsteinDef 0 m N”` and `goodsteinSentence_faithful` certifies
`(ℕ ⊧ₘ goodsteinSentence) ↔ ∀ m, ∃ N, goodsteinSeq m N = 0` over the audited hereditary-base
`goodsteinSeq`. The headline says exactly Kirby–Paris. **No transcription drift.**

**One doc-drift found + fixed this lap.** `Reduction.lean` (the `⚠️ Foundation-side axiom
dependency` note + the `goodstein_implies_consistency` docstring) still claimed
`peano_not_proves_consistency` carries Foundation's `PA_delta1Definable`. The kernel says it is
clean (lap-89 discharged `𝗣𝗔.Δ₁` upstream into a real instance). The comment overstated the axiom
debt — the safe direction of error, but dishonest by omission of the lap-89 fact. Corrected.

---

## 1. Is the DESTINATION still right? — KEEP. (with an honest timeline)

**Where this is going.** `𝗣𝗔 ⊬ Goodstein` (Kirby–Paris 1982), fully axiom-free. Route A
(Rathjen 2014 "Goodstein revisited", Cor 3.7): inside `𝗣𝗔`, `γ → PRWO(ε₀) → Con(𝗣𝗔)`, then
Gödel II gives `𝗣𝗔 ⊬ Con(𝗣𝗔)`, hence `𝗣𝗔 ⊬ γ`. This is a genuine landmark — a fully
machine-checked, axiom-free Kirby–Paris with the consistency strength carried by an
**IΣ₁-internalized** Gentzen ordinal analysis. KEEP.

**The honest endpoint.** crux-1 (`γ → PRWO(ε₀)`) is DONE and axiom-clean (lap 57). crux-2
(`PRWO(ε₀) → Con(𝗣𝗔)`, internalized) is the wall. crux-2 is **internalized Gentzen
cut-elimination in IΣ₁, total on non-standard codes** — to my knowledge there is no prior fully
IΣ₁-internal formalization of Gentzen's consistency proof (the Bryce–Goré Coq work and the repo's
own `Zinfty.lean` are META-level: external well-founded trees, mathlib ordinals — NOT arithmetized
on V-codes in every model of IΣ₁, which is what the reduction inside `𝗣𝗔` requires). This is a
multi-year-scale target. The operator mandate is explicit (axiom-free), and the repo's own
faithfulness invariant forbids a cited axiom for the ordinal-analysis girder. So the destination
stays "axiom-free, headline `sorry` until clean." The honest near-term milestone: **every girder
except the cut-elimination inversion built and axiom-clean** (M2 embedding + M3 PRWO-plumbing +
the descent bookkeeping), with the inversion as the last, deepest hold-out.

Verdict: **DESTINATION KEPT.** No new information (paper, mathlib, Aristotle) changes the endpoint.

---

## 2. Are we attacking the highest-value thing? — Mostly. One real imbalance.

**Not pure circling.** Despite ~50 laps frozen on the same headline footprint, lap 110 produced a
genuine, kernel-grounded root cause: `iCritReductG` cuts the critical reduct on the **principal**
formula `A_i`, but Buchholz Thm 3.4(a) cuts on the **stripped** `A(d)` with *strictly* lower rank
(`rk(A(d)) = rk(A_i) − 1` for `A_i ∈ {∀xF, ¬A}`). This off-by-one is exactly why the splice rank
bound `hr'` and the critical-case soundness `ZDerivation_red_zK_crit` both fail. The fix (redefine
the cut formula to the stripped `A(d)`) is concrete and correct. That is real forward motion.

**But the work is imbalanced — and that IS a form of drift.** The effort has concentrated on the
**ordinal-DESCENT bookkeeping** (`iord_descent_red`: Ind + critical + 3 replace-leaf bundles done;
~80% closed), while the genuine **cut-elimination CONTENT** — the ∀/¬-**inversion** (Buchholz
3.4(a): from `d ⊢ Γ,A` produce the two halves `d{0} ⊢ Θ→A(d)`, `d{1} ⊢ A(d),Θ→D`) — has been
deferred lap after lap. Its only attempt was the **external prototype `ZInf.allInv`, which lap 107
proved VACUOUS** and killed. The inversion is `ZDerivation_red_zK_crit` (`Crux2Blueprint:96/100`)
and it is ≈0% done on the load-bearing Σ₁ engine. **Per hardest-first, the inversion is the prize
and it is the piece being avoided.**

**The FIXPOINT defect is a selection bug masquerading as a descent gap.** Three `iord_descent_red`
K-case branches (`Crux2Blueprint:568/610/612`, selected premise = atom/axAll/axNeg) are stuck on
`red dᵢ = dᵢ` → "no descent". The chain-REPLACE IH (`:594`) is likewise *false at atom-fixpoints*
(lap 109). These are NOT genuine per-branch descent obligations — they are symptoms of the engine's
selection (`permIdx`) pointing at an **axiom leaf**, which has no cut to reduce, so the reduction
stalls. In a correct cut-elimination you never select a normal leaf as the redex; you reduce the
lowest genuine cut. This is the same "engine stalls after one step" defect diagnosed in-kernel at
laps 104 and 107 — it keeps **resurfacing branch by branch** because the descent lemma is being
ground against an engine whose `red` can be the identity on a non-cut-free derivation.

---

## 3. What a sharp outside expert would say we're MISSING

**(a) Switch the endgame from "infinite descent" to "terminating reduction to an absurd normal
form."** Today: `false_of_ZDerivesEmpty ← iord_red_iterate_descends` (an *infinite, always-strict*
ε₀-descent) + PRWO. The always-strict requirement is exactly what the fixpoint defect breaks. The
standard Gentzen argument is instead: cut-reduction lowers the ordinal *while a cut remains*; by
well-foundedness (= PRWO) it terminates at a **cut-free** derivation; a cut-free `∅→⊥` derivation
is **impossible**. Reformulate:

- `iord_descent_red'` : `red d = d ∨ icmp (iord (red d)) (iord d) = 0`  *(disjunctive — WEAKER)*
- `red_fixpoint_iff_cutfree` : `red d = d ↔ d is cut-free`  *(the real obligation)*
- `no_cutfree_empty_to_bot` : no cut-free derivation of `∅→⊥`  *(clean, standard)*

In the disjunctive form the three fixpoint branches close **trivially** (they prove the LEFT
disjunct, `red d = d`, which the engine already gives — `red_zK_fixpoint_of_atom_selected`). The
burden moves to the ONE honest place: `red d = d ⟹ d cut-free`, i.e. *selection correctness*. This
does not magically remove the hard part — it makes the hard part **explicit and singular** instead
of scattered across ~4 unprovable "descent" sorries. It is also strictly more faithful to Gentzen.
**This is the highest-value STRUCTURAL move and it should be tested first** (it is contained:
`iord_descent_red` is consumed only via `iord_red_iterate_descends → false_of_ZDerivesEmpty`).

**(b) The genuine remaining content is the ∀/¬-INVERSION on the Σ₁ engine — START it.** The META
inversion is already proven and axiom-clean: `Zinfty.allInv` / `andInv` / `orInv` / `cutElim`
(`src/Zinfty.lean`, one-sided Tait, mathlib ordinals). The work is the **two-calculi bridge** pinned
at lap 106: META is one-sided Tait + mathlib `Ordinal`; the engine is two-sided Buchholz + V-internal
ε₀-codes. The external-inductive shortcut (`ZInf`) is dead (lap 107). The port must land on the Σ₁
engine `red`/`iord`. This is where the multi-year mass sits; it is the irreducible hard core; it has
been avoided. The cut-formula-strip fix (lap 110) is its immediate prerequisite (you cannot state
"derive the stripped `A(d)`" until the reduct cuts on `A(d)`).

**(c) Architecture note (not actionable now).** The two-calculi bridge is the standing tax. A
one-sided-Tait engine matching the META would let the inversions port near-verbatim — but the
8000-line `InternalZ` is two-sided Buchholz; a rewrite is not worth it. Record it as the known
source of friction, not a task.

---

## 4. The call

**KEEP** the destination (axiom-free Kirby–Paris) and the carrier (the Σ₁ engine `red`/`iord`,
re-confirmed load-bearing at lap 107). **KEEP** lap-110's cut-formula-strip fix as the immediate
mechanical step (correct; closes `hr'`).

**STOP** treating the `iord_descent_red` fixpoint branches as per-branch descent obligations (they
are a selection bug). **STOP** any further investment in the external-inductive prototypes
(`ZInf`/`ZcOK`/`ZcDer`) — dead since lap 107. **STOP** grinding new K-case descent leaves before the
structural reformulation (3a) collapses the fixpoint sorries.

**DO, in order:**
1. **(structural, do first — collapses ~4 sorries)** Reformulate `iord_descent_red` to the
   disjunctive `red d = d ∨ iord ≺`, and `false_of_ZDerivesEmpty` to "terminate-at-cut-free ⟹
   absurd". Fixpoint branches close trivially; the real obligation becomes the single
   `red d = d ⟹ cut-free` (selection correctness) + `no cut-free ∅→⊥`.
2. **(mechanical, concrete)** Land lap-110's `iCritReductG` cut-formula = stripped `A(d)`; close the
   splice `hr'` with the strict stripped rank bound (`irk_cut_lt_rank_forall`/`_neg`).
3. **(THE PRIZE, hardest-first)** Start the ∀/¬-inversion on the Σ₁ engine (`ZDerivation_red_zK_crit`):
   the two halves derive the stripped endsequents. Template `Zinfty.allInv` (META, axiom-clean);
   bridge the one-sided-Tait / two-sided-Buchholz fork on V-codes.

**Single highest-value next target:** the structural reformulation (1) — it is contained, it
dissolves the fixpoint stalls that have re-appeared across laps 104/107/109/110, and it sharpens the
entire remaining crux-2 obligation down to "selection correctness + no-cut-free-⊥ + the inversion,"
which is the honest shape of what's left.

---

## 5. Pacing / meta

50 laps frozen on one footprint is the symptom that justifies this altitude pass. The cause is not
laziness — it is that crux-2 is genuinely the hard internalization no one has done, and the engine
has a real selection defect that the descent-side grind cannot fix. The reformulation in §3a is the
lever to stop the branch-by-branch resurfacing. After this synthesis commits, resume the grind on
target (1), not on another descent leaf.
