/-
# wip/InternalZomega.lean — the ω-rule de-risk SPIKE (lap 101 reflection PRIORITY 1)

**Purpose (see `REFLECTION-2026-06-25-lap101.md`, `NEXT_STEPS.md`).** Settle the finitary-vs-ω-rule
sub-route fork with EVIDENCE, not conviction. The lap-92 reflection recommended pivoting crux-2's
internalized cut-elimination from Buchholz's *finitary eigenvariable* system to the *infinitary ω-rule*
system (`Z^∞`), arguing it dissolves O1 (freshness), O2 (eigen-subst), AND the route-B `tpReduce`
conclusion-tracking motive (`redZKReady`) at once, because a critical ∀-cut SELECTS the premise `dₜ`
(already deriving `Γ→F(t)`) rather than substituting. Lap-95 overruled to the finitary Path X **without
running the spike lap-92 said to run first.** This file runs it.

NOT imported by `GoodsteinPA.lean` — a self-contained probe; it cannot affect the green gate. Verify with
`lake env lean wip/InternalZomega.lean`.

## What this spike DEMONSTRATES (in-kernel, axiom-clean)

The decisive dissolution claim, made concrete on the EXISTING machinery: **the ω-rule premise family is
already materializable from a finitary I∀ node, and its validity is discharged purely by the
construction-time freshness bound `maxEigen d0 < a` (= `ZRegular`, which `red` already maintains) — with NO
criticality / conclusion-tracking motive.** A critical ∀-cut's reduct is the SELECTION `zOmegaPrem d0 a t`,
whose validity is `zOmegaPrem_valid` (a hypothesis-level fact about a well-formed ∀-node), NOT an obligation
discharged inside the cut-elimination recursion. Contrast the finitary K-case, whose validity needs the
`redZKReady` hereditary-all-Rep motive (`Crux2Blueprint.redSoundGen`'s open `sorry`).

**Where the substitution-validity work goes under the ω-rule view:** to NODE-CONSTRUCTION time (proving the
premise family `∀ t, ZDerivation (zsubst d0 a t)` once, with the clean freshness bound), NOT into the
cut-elimination recursion. That decoupling is exactly why the conclusion-tracking motive evaporates: the
selected premise's conclusion `Γ→F(t)` is COMPUTED (`zOmegaPrem_concl`), never threaded.

## The arithmetization-risk probe — substantially RETIRED this lap (see Probe 1, bottom)

The lap-92 reflection named the riskiest unknown as "premise-`t` as a Σ₁ recursive notation + cut-elimination
recursion on `iord`, selecting premises from infinite families." This spike retires the two hardest pieces
in-kernel: the premise family is materialized on demand by `zsubst` (Buchholz §6 `Z*`: `h[t] = h₀(x/t)`), so
premise access is Σ₁ (`zOmegaPrem`); its validity is motive-free (`zOmegaPrem_valid`); and the premise-family
ordinal is CONSTANT `= iord d0` (`iord_zOmegaPrem_constant`), so the ω-node's `iord` is the finite `iord d0 +
1` — no sup-over-infinite-family primitive. The single remaining open piece is the ω-rule cut-elimination
STEP itself (Probe 2, bottom), which needs the ω-node datatype + Fixpoint extension (the templated rebuild).
-/
import GoodsteinPA.Zsubst

namespace GoodsteinPA.InternalZ

open Classical
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.HierarchySymbol ISigma1 PeanoMinus
open LO.FirstOrder.Arithmetic.Bootstrapping
open GoodsteinPA.InternalONote

variable {V : Type*} [ORingStructure V] [V ⊧ₘ* 𝗜𝚺₁]

/-! ## The ω-rule premise family, materialized from a finitary I∀ node

The finitary I∀ node `zIall s a p d0` packages a single eigenvariable premise `d0 ⊢ Γ→F(a)`. Its ω-rule
view is the premise family indexed by closed terms `t`: premise-`t` = `zsubst d0 a t ⊢ Γ→F(t)`. This is
exactly Buchholz §6 `Z*` (`h[t] = h₀(x/t)`): a finite code (`d0`) with premise-`t` computed on demand. -/

/-- **The `t`-th ω-rule premise** generated from the I∀ premise `d0` with eigenvariable `a`: substitute the
closed term `t` for `a`. The whole ω-rule premise family is `t ↦ zOmegaPrem d0 a t`. -/
noncomputable def zOmegaPrem (d0 a t : V) : V := zsubst d0 a t

/-- **The ω-rule ∀-cut reduct is VALIDITY-FREE (the Path-C dissolution, concrete).** Every premise of the
ω-rule family generated from a valid I∀ node is a `ZDerivation`, discharged PURELY by the construction-time
freshness bound `maxEigen d0 < a` — NO criticality, NO conclusion-tracking motive. A critical ∀-cut on
`∀x F` SELECTS `zOmegaPrem d0 a t` (the premise for the cut witness `t`); its validity is THIS lemma, a
hypothesis-level fact about the well-formed ∀-node — not an obligation inside the cut-elimination recursion.
This is the in-kernel evidence that the ω-rule presentation retires the `redZKReady` wall. -/
theorem zOmegaPrem_valid {s a p d0 t : V} (ht : IsSemiterm ℒₒᵣ 0 t)
    (hZ : ZDerivation (zIall s a p d0)) (hfresh : maxEigen d0 < a) :
    ZDerivation (zOmegaPrem d0 a t) :=
  ZDerivation_zsubst_zIall_premise ht hZ hfresh

/-- **The selected premise's conclusion is COMPUTED, never threaded (conclusion-tracking automatic).**
`zOmegaPrem d0 a t` derives exactly `Γ→F(t)` (`= seqSetSucc s (substs1 t p)`), given the eigenvariable `a`
is fresh in the matrix `p` (`hpfresh`) and the antecedent `Γ = seqAnt s` (`hΓfresh`) — Buchholz's
eigenvariable side condition, supplied at the I∀ node, NOT re-discharged per cut. The finitary route's
`tpReduce` conclusion-reduction + the `redZKReady` hereditary-Rep motive exist only to recover THIS
equation through the chain machinery; under the ω-rule view it is a direct computation. Generalizes
`red_zIall_tpReduce` (its `t = 0` instance) to the whole premise family. -/
theorem zOmegaPrem_concl {s a p d0 t : V} (hZ : ZDerivation (zIall s a p d0))
    (hpfresh : fvSubst ℒₒᵣ a t p = p)
    (hΓfresh : fvSubstSeq a t (seqAnt s) = seqAnt s)
    (ht : IsSemiterm ℒₒᵣ 0 t) :
    fstIdx (zOmegaPrem d0 a t) = seqSetSucc s (substs1 ℒₒᵣ t p) := by
  obtain ⟨hd0, _, hwff⟩ := zDerivation_zIall_inv hZ
  have hfa : IsSemiterm ℒₒᵣ 0 (^&a : V) := by simp
  rw [zOmegaPrem, fstIdx_zsubst _ _ hd0]
  simp only [fvSubstSeqt, seqSetSucc, hwff.1, hwff.2.1, hΓfresh,
    fvSubst_substs1 ht hfa hwff.2.2, termFvSubst_fvar_self, hpfresh]

/-! ## Probe 1 — `iord` for the ω-node: the premise-family ordinal is CONSTANT (risk DISSOLVED)

The lap-92 reflection named "premise-`n` as a Σ₁ recursive notation + cut-elimination recursion on `iord`"
as the riskiest unprobed assumption. For the `iord` half it dissolves cleanly: the eigensubst already
preserves the ordinal (`iord_zsubst`, proven axiom-clean), so the ω-node's premise family `t ↦ zOmegaPrem
d0 a t` has CONSTANT ordinal `iord d0`. Hence the would-be `sup_t (iord (premise t))` is the sup of a
constant family `= iord d0` — NO sup over an infinite family is needed; `iord(zAllω) := iord d0 + 1` is a
FINITE, computable ordinal assignment built with the existing `iord` engine, no new primitive. -/

/-- **Every ω-rule premise has the SAME ordinal `iord d0`.** The eigensubst `zsubst d0 a t` preserves
`iord` (`iord_zsubst`), so the premise-family ordinal is constant in the index `t`. -/
theorem iord_zOmegaPrem {d0 a t : V} (ht : IsUTerm ℒₒᵣ t) (hZ : ZDerivation d0) :
    iord (zOmegaPrem d0 a t) = iord d0 := by
  rw [zOmegaPrem]; exact iord_zsubst ht hZ a

/-- **Probe 1 RESOLVED (the arithmetization-risk de-risk).** The ω-node's ordinal is `iord d0 + 1` — a
FINITE successor of the single I∀-premise ordinal, NOT a sup over an infinite premise family. Concretely:
for any two closed terms `t₁ t₂`, the premises `zOmegaPrem d0 a t₁` and `zOmegaPrem d0 a t₂` have EQUAL
ordinal, so the family's supremum is just `iord d0`. The "sup over an infinite family" that looked like the
Path-C wall does not arise; the existing `iord`/ω-tower engine assigns the ω-node its ordinal unchanged.
This is the in-kernel evidence that the ω-rule node arithmetizes — the strongest single signal for the
pivot. -/
theorem iord_zOmegaPrem_constant {d0 a t₁ t₂ : V}
    (ht₁ : IsUTerm ℒₒᵣ t₁) (ht₂ : IsUTerm ℒₒᵣ t₂) (hZ : ZDerivation d0) :
    iord (zOmegaPrem d0 a t₁) = iord (zOmegaPrem d0 a t₂) := by
  rw [iord_zOmegaPrem ht₁ hZ, iord_zOmegaPrem ht₂ hZ]

/-! ## Capstone — the ω-rule ∀-node is REALIZABLE from a regular finitary I∀ node

The decisive structural point: a (would-be) ω-node `zAllω s a p d0` carries the SAME finite data as the
existing `zIall s a p d0` — premise-`t` is computed on demand (`zsubst d0 a t`), never stored. And its full
ω-rule validity (premise family valid + conclusions correct + ordinals uniform) is DERIVED from the existing
regular `zIall` node, with no chain machinery and no conclusion-tracking motive. So a Path-C rebuild reuses
the existing I∀ embedding wholesale (PA's ∀-intro already produces a regular `zIall` with fresh
eigenvariable = O3). -/

/-- **Spike capstone — a regular `zIall` realizes the full ω-rule ∀-node.** From `ZDerivation (zIall s a p
d0)`, the freshness bound `maxEigen d0 < a`, and the eigenvariable side-condition O3 (`a` not free in the
matrix `p` or antecedent `Γ`, phrased as substitution-invariance — exactly what the embedding's fresh
eigenvariable choice supplies), EVERY closed term `t` gives: the premise `zOmegaPrem d0 a t` is a
`ZDerivation` of exactly `Γ→F(t)`, with ordinal `iord d0` (uniform across the family). This is the formal
object the ω-rule cut-elimination consumes — assembled from `zOmegaPrem_valid` (motive-free validity),
`zOmegaPrem_concl` (computed conclusion), `iord_zOmegaPrem` (finite uniform ordinal), all in-kernel. -/
theorem zIall_realizes_omega {s a p d0 : V}
    (hZ : ZDerivation (zIall s a p d0)) (hreg : maxEigen d0 < a)
    (hO3p : ∀ t, IsSemiterm ℒₒᵣ 0 t → fvSubst ℒₒᵣ a t p = p)
    (hO3Γ : ∀ t, IsSemiterm ℒₒᵣ 0 t → fvSubstSeq a t (seqAnt s) = seqAnt s) :
    ∀ t, IsSemiterm ℒₒᵣ 0 t →
      ZDerivation (zOmegaPrem d0 a t) ∧
      fstIdx (zOmegaPrem d0 a t) = seqSetSucc s (substs1 ℒₒᵣ t p) ∧
      iord (zOmegaPrem d0 a t) = iord d0 := by
  intro t ht
  exact ⟨zOmegaPrem_valid ht hZ hreg,
    zOmegaPrem_concl hZ (hO3p t ht) (hO3Γ t ht) ht,
    iord_zOmegaPrem ht.isUTerm (zDerivation_zIall_inv hZ).1⟩

/-! ## Spike verdict so far + the one remaining Path-C obligation (Probe 2 — OPEN)

**Evidence gathered (all axiom-clean, in-kernel):**
- `zOmegaPrem_valid` — premise family uniformly valid, motive-free (freshness bound only).
- `zOmegaPrem_concl` — selected premise's conclusion computed, not threaded.
- `iord_zOmegaPrem` / `iord_zOmegaPrem_constant` — premise-family ordinal is CONSTANT `= iord d0`, so the
  ω-node's `iord` is the finite `iord d0 + 1` (no sup-over-infinite-family primitive needed). Probe 1's
  arithmetization-risk concern is RETIRED.

**The single remaining open question (Probe 2 — the ω-rule cut-elimination STEP):** a cut with R-premise an
ω-node `∀x F` and L-premise its dual reduces to a cut on `F(t)` against `zOmegaPrem d0 a t` (premise
selection) — the Schütte/Tait reduction `Zinfty.lean` does at the META level. The arithmetized step
recurses on `iord` (now known finite, Probe 1); the selected premise's validity is `zOmegaPrem_valid`
(already discharged), so the reduction introduces NO new substitution-validity obligation. What it DOES need
is the ω-node datatype (a new tag in the `zconstruction` Fixpoint) + extending `ZPhi`/`iord`/`tp` to it —
the ~2–3k-line rebuild. That is the genuine cost of the pivot, but it is now ENGINEERING against a settled
template (`Zinfty.lean`), with the two hardest sub-questions (premise validity, ordinal assignment) already
answered above.

**NET CALL (updated by this spike):** the evidence runs in favour of the Path-C pivot — both the validity
(`zOmegaPrem_valid`, motive-free) and the ordinal (`iord_zOmegaPrem_constant`, finite) of the ω-node are
in-kernel facts on the EXISTING engine, and they are exactly the two obligations the finitary route turns
into the open `redZKReady` motive + `iord_descent_red` K-case. The remaining work is the (large but
templated) ω-node datatype + cut-elimination rebuild. **NEXT LAP:** decide commit-to-pivot vs one more
de-risk (a minimal ω-node datatype `zAllω` as tag 7 + its `red`/`iord` equations) — see `NEXT_STEPS.md`. -/

end GoodsteinPA.InternalZ
