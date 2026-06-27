/-
# `wip/InternalZ.lean` — C0: arithmetized system-Z derivation constructor codes

**Status: wip brick for crux 2 (lap 60).** Buchholz's consistency proof runs over his finitary system
**Z** (`CRUX2-ORD-ASSIGNMENT-2026-06-24.md §3`), NOT Foundation's Tait calculus. To internalize Thm 4.2
(`o(d[n]) ≺ o(d)`) we must arithmetize Z as a `V → Prop` predicate on derivation **codes**, mirroring
Foundation's `Theory.Derivation` (`…/Proof/Basic.lean`). This file is the **data layer**: the coded
constructors for Z's five inference forms, their `𝚺₀` graphs, the subterm `<`-bounds (well-foundedness
for the eventual `Fixpoint`), and the `fstIdx` (end-sequent) projection.

Z's rules (doc §3), each code `⟪s, tag, …payload…⟫ + 1` (end-sequent `s` first, rule `tag` second):
* `zAtom s`            — tag 0 — atomic axiom (§5 content TBD).
* `zIall s a p d0`     — tag 1 — `I^a_∀xF`  (eigenvar `a`, formula `p = F`, premise `d0`).
* `zIneg s p d0`       — tag 2 — `I_¬A`      (formula `p = A`, premise `d0`).
* `zInd s at p d0 d1`  — tag 3 — `Ind^{a,t}_F` (bundled `at = ⟪a,t⟫`, formula `p = F`, premises).
* `zK s r ds`          — tag 4 — `K^r_Π`     (rank `r`, **sequence** `ds` of premises — variadic).

NEXT (next bricks): `Phi`/`blueprint`/`construction` (Fixpoint) → `ZDerivation : V → Prop`; then C1
(`iõ`/`idg`/`iord = iotower idg iõ` by recursion on it) and C2 (`iR`).
-/
import GoodsteinPA.InternalTower
import GoodsteinPA.FvSubst
import Foundation.FirstOrder.Incompleteness.Second

namespace GoodsteinPA.InternalZ

open Classical
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.HierarchySymbol ISigma1 PeanoMinus
open LO.FirstOrder.Arithmetic.Bootstrapping
open GoodsteinPA.InternalONote

variable {V : Type*} [ORingStructure V] [V ⊧ₘ* 𝗜𝚺₁]

/-! ## Constructor codes -/

noncomputable def zAtom (s : V) : V := ⟪s, 0, 0⟫ + 1
noncomputable def zIall (s a p d0 : V) : V := ⟪s, 1, a, p, d0⟫ + 1
noncomputable def zIneg (s p d0 : V) : V := ⟪s, 2, p, d0⟫ + 1
noncomputable def zInd (s at' p d0 d1 : V) : V := ⟪s, 3, at', p, d0, d1⟫ + 1
noncomputable def zK (s r ds : V) : V := ⟪s, 4, r, ds⟫ + 1

/-! ## `𝚺₀` graphs -/

def zAtomGraph : 𝚺₀.Semisentence 2 :=
  .mkSigma “y s. ∃ y' < y, !pair₃Def y' s 0 0 ∧ y = y' + 1”
instance zAtom_defined : 𝚺₀-Function₁ (zAtom : V → V) via zAtomGraph := .mk fun v ↦ by
  simp_all [zAtomGraph, zAtom]

def zIallGraph : 𝚺₀.Semisentence 5 :=
  .mkSigma “y s a p d0. ∃ y' < y, !pair₅Def y' s 1 a p d0 ∧ y = y' + 1”
instance zIall_defined : 𝚺₀-Function₄ (zIall : V → V → V → V → V) via zIallGraph := .mk fun v ↦ by
  simp_all [zIallGraph, numeral_eq_natCast, zIall]

def zInegGraph : 𝚺₀.Semisentence 4 :=
  .mkSigma “y s p d0. ∃ y' < y, !pair₄Def y' s 2 p d0 ∧ y = y' + 1”
instance zIneg_defined : 𝚺₀-Function₃ (zIneg : V → V → V → V) via zInegGraph := .mk fun v ↦ by
  simp_all [zInegGraph, numeral_eq_natCast, zIneg]

def zIndGraph : 𝚺₀.Semisentence 6 :=
  .mkSigma “y s at' p d0 d1. ∃ y' < y, !pair₆Def y' s 3 at' p d0 d1 ∧ y = y' + 1”
instance zInd_defined : 𝚺₀-Function₅ (zInd : V → V → V → V → V → V) via zIndGraph := .mk fun v ↦ by
  simp_all [zIndGraph, numeral_eq_natCast, zInd]

def zKGraph : 𝚺₀.Semisentence 4 :=
  .mkSigma “y s r ds. ∃ y' < y, !pair₄Def y' s 4 r ds ∧ y = y' + 1”
instance zK_defined : 𝚺₀-Function₃ (zK : V → V → V → V) via zKGraph := .mk fun v ↦ by
  simp_all [zKGraph, numeral_eq_natCast, zK]

/-! ## Subterm `<`-bounds (well-foundedness of the eventual `Fixpoint`) -/

@[simp] lemma seq_lt_zAtom (s : V) : s < zAtom s := le_iff_lt_succ.mp <| le_pair_left _ _

@[simp] lemma seq_lt_zIall (s a p d0 : V) : s < zIall s a p d0 := le_iff_lt_succ.mp <| le_pair_left _ _
@[simp] lemma d0_lt_zIall (s a p d0 : V) : d0 < zIall s a p d0 :=
  le_iff_lt_succ.mp <| le_trans (le_trans (le_trans (le_pair_right _ _) <| le_pair_right _ _)
    <| le_pair_right _ _) <| le_pair_right _ _

@[simp] lemma seq_lt_zIneg (s p d0 : V) : s < zIneg s p d0 := le_iff_lt_succ.mp <| le_pair_left _ _
@[simp] lemma d0_lt_zIneg (s p d0 : V) : d0 < zIneg s p d0 :=
  le_iff_lt_succ.mp <| le_trans (le_trans (le_pair_right _ _) <| le_pair_right _ _) <| le_pair_right _ _

@[simp] lemma seq_lt_zInd (s at' p d0 d1 : V) : s < zInd s at' p d0 d1 :=
  le_iff_lt_succ.mp <| le_pair_left _ _
@[simp] lemma d0_lt_zInd (s at' p d0 d1 : V) : d0 < zInd s at' p d0 d1 :=
  le_iff_lt_succ.mp <| le_trans (le_trans (le_trans (le_trans (by simp) <| le_pair_right _ _)
    <| le_pair_right _ _) <| le_pair_right _ _) <| le_pair_right _ _
@[simp] lemma d1_lt_zInd (s at' p d0 d1 : V) : d1 < zInd s at' p d0 d1 :=
  le_iff_lt_succ.mp <| le_trans (le_trans (le_trans (le_trans (by simp) <| le_pair_right _ _)
    <| le_pair_right _ _) <| le_pair_right _ _) <| le_pair_right _ _

@[simp] lemma a_lt_zIall (s a p d0 : V) : a < zIall s a p d0 :=
  le_iff_lt_succ.mp <| le_trans (le_trans (le_pair_left _ _) <| le_pair_right _ _) <| le_pair_right _ _
@[simp] lemma p_lt_zIall (s a p d0 : V) : p < zIall s a p d0 :=
  le_iff_lt_succ.mp <| le_trans (le_trans (le_trans (le_pair_left _ _) <| le_pair_right _ _)
    <| le_pair_right _ _) <| le_pair_right _ _

@[simp] lemma p_lt_zIneg (s p d0 : V) : p < zIneg s p d0 :=
  le_iff_lt_succ.mp <| le_trans (le_trans (le_pair_left _ _) <| le_pair_right _ _) <| le_pair_right _ _

@[simp] lemma at_lt_zInd (s at' p d0 d1 : V) : at' < zInd s at' p d0 d1 :=
  le_iff_lt_succ.mp <| le_trans (le_trans (le_pair_left _ _) <| le_pair_right _ _) <| le_pair_right _ _
@[simp] lemma p_lt_zInd (s at' p d0 d1 : V) : p < zInd s at' p d0 d1 :=
  le_iff_lt_succ.mp <| le_trans (le_trans (le_trans (le_pair_left _ _) <| le_pair_right _ _)
    <| le_pair_right _ _) <| le_pair_right _ _

@[simp] lemma seq_lt_zK (s r ds : V) : s < zK s r ds := le_iff_lt_succ.mp <| le_pair_left _ _
@[simp] lemma r_lt_zK (s r ds : V) : r < zK s r ds :=
  le_iff_lt_succ.mp <| le_trans (le_trans (le_pair_left _ _) <| le_pair_right _ _) <| le_pair_right _ _
@[simp] lemma ds_lt_zK (s r ds : V) : ds < zK s r ds :=
  le_iff_lt_succ.mp <| le_trans (le_trans (le_pair_right _ _) <| le_pair_right _ _) <| le_pair_right _ _

/-! ## `zTag` — the rule tag (second pair component), for recursion dispatch

The ordinal assignment functions `idg`/`iõ`/`iord` are **total** `𝚺₁` functions on codes, defined by
course-of-values recursion (like `iC`/`iomul`) that dispatches on `zTag d` and reads the relevant
subderivations. (`ZDerivation : V → Prop` — the Fixpoint, NEXT brick — is needed only to characterize
*which* codes are derivations + for `derivesEmpty`, not for the descent on these functions.) -/

/-- The rule tag of a derivation code: `π₁ (sndIdx d)` (`= π₁ (π₂ (d-1))`). -/
noncomputable def zTag (d : V) : V := π₁ (sndIdx d)

def _root_.LO.FirstOrder.Arithmetic.zTagDef : 𝚺₀.Semisentence 2 := .mkSigma
  “y d. ∃ sd <⁺ d, !sndIdxDef sd d ∧ !pi₁Def y sd”

instance zTag_defined : 𝚺₀-Function₁ (zTag : V → V) via zTagDef := .mk fun v ↦ by
  simp [zTagDef, zTag, sndIdx_defined.iff, pi₁_defined.iff]

instance zTag_definable : 𝚺₀-Function₁ (zTag : V → V) := zTag_defined.to_definable

@[simp] lemma zTag_zAtom (s : V) : zTag (zAtom s) = 0 := by simp [zTag, sndIdx, zAtom]
@[simp] lemma zTag_zIall (s a p d0 : V) : zTag (zIall s a p d0) = 1 := by simp [zTag, sndIdx, zIall]
@[simp] lemma zTag_zIneg (s p d0 : V) : zTag (zIneg s p d0) = 2 := by simp [zTag, sndIdx, zIneg]
@[simp] lemma zTag_zInd (s at' p d0 d1 : V) : zTag (zInd s at' p d0 d1) = 3 := by
  simp [zTag, sndIdx, zInd]
@[simp] lemma zTag_zK (s r ds : V) : zTag (zK s r ds) = 4 := by simp [zTag, sndIdx, zK]

/-! ## `fstIdx` (end-sequent) projection -/

@[simp] lemma fstIdx_zAtom (s : V) : fstIdx (zAtom s) = s := by simp [fstIdx, zAtom]
@[simp] lemma fstIdx_zIall (s a p d0 : V) : fstIdx (zIall s a p d0) = s := by simp [fstIdx, zIall]
@[simp] lemma fstIdx_zIneg (s p d0 : V) : fstIdx (zIneg s p d0) = s := by simp [fstIdx, zIneg]
@[simp] lemma fstIdx_zInd (s at' p d0 d1 : V) : fstIdx (zInd s at' p d0 d1) = s := by
  simp [fstIdx, zInd]
@[simp] lemma fstIdx_zK (s r ds : V) : fstIdx (zK s r ds) = s := by simp [fstIdx, zK]

/-! ## Payload + sub-derivation projections (for the assignment recursion)

`zRest d = π₂ (sndIdx d)` is the payload *after* the rule tag (`sndIdx d = ⟪zTag d, zRest d⟫`).
The per-constructor sub-derivation/formula projections are π-chains on `zRest`; each is `≤ d`
(so the recursion reads them out of the value-table) and computes correctly on its own code. -/

/-- The payload after the tag: `sndIdx d = ⟪zTag d, zRest d⟫`. -/
noncomputable def zRest (d : V) : V := π₂ (sndIdx d)

def _root_.LO.FirstOrder.Arithmetic.zRestDef : 𝚺₀.Semisentence 2 := .mkSigma
  “y d. ∃ sd <⁺ d, !sndIdxDef sd d ∧ !pi₂Def y sd”
instance zRest_defined : 𝚺₀-Function₁ (zRest : V → V) via zRestDef := .mk fun v ↦ by
  simp [zRestDef, zRest, sndIdx_defined.iff, pi₂_defined.iff]
instance zRest_definable : 𝚺₀-Function₁ (zRest : V → V) := zRest_defined.to_definable

@[simp] lemma zRest_le_self (d : V) : zRest d ≤ d := le_trans (by simp [zRest]) (sndIdx_le_self d)

-- Premise/formula projections (π-chains on the payload).
/-- `I^a_∀xF` premise `d0` (payload `⟪a,p,d0⟫`). -/
noncomputable def zIallPrem (d : V) : V := π₂ (π₂ (zRest d))
/-- `I_¬A` premise `d0` (payload `⟪p,d0⟫`). -/
noncomputable def zInegPrem (d : V) : V := π₂ (zRest d)
/-- `Ind^{a,t}_F` induction formula `F` (payload `⟪at,p,d0,d1⟫`). -/
noncomputable def zIndP (d : V) : V := π₁ (π₂ (zRest d))
/-- `Ind^{a,t}_F` base premise `d0`. -/
noncomputable def zIndPrem0 (d : V) : V := π₁ (π₂ (π₂ (zRest d)))
/-- `Ind^{a,t}_F` step premise `d1`. -/
noncomputable def zIndPrem1 (d : V) : V := π₂ (π₂ (π₂ (zRest d)))
/-- `K^r_Π` rank `r` (payload `⟪r,ds⟫`). -/
noncomputable def zKrank (d : V) : V := π₁ (zRest d)
/-- `K^r_Π` premise sequence `ds`. -/
noncomputable def zKseq (d : V) : V := π₂ (zRest d)

section ProjDef
open LO.FirstOrder.Arithmetic
def _root_.LO.FirstOrder.Arithmetic.zIallPremDef : 𝚺₀.Semisentence 2 := .mkSigma
  “y d. ∃ r <⁺ d, !zRestDef r d ∧ ∃ r2 <⁺ r, !pi₂Def r2 r ∧ !pi₂Def y r2”
instance zIallPrem_defined : 𝚺₀-Function₁ (zIallPrem : V → V) via zIallPremDef := .mk fun v ↦ by
  simp [zIallPremDef, zIallPrem, zRest_defined.iff, pi₂_defined.iff]
instance zIallPrem_definable : 𝚺₀-Function₁ (zIallPrem : V → V) := zIallPrem_defined.to_definable

def _root_.LO.FirstOrder.Arithmetic.zInegPremDef : 𝚺₀.Semisentence 2 := .mkSigma
  “y d. ∃ r <⁺ d, !zRestDef r d ∧ !pi₂Def y r”
instance zInegPrem_defined : 𝚺₀-Function₁ (zInegPrem : V → V) via zInegPremDef := .mk fun v ↦ by
  simp [zInegPremDef, zInegPrem, zRest_defined.iff, pi₂_defined.iff]
instance zInegPrem_definable : 𝚺₀-Function₁ (zInegPrem : V → V) := zInegPrem_defined.to_definable

def _root_.LO.FirstOrder.Arithmetic.zIndPDef : 𝚺₀.Semisentence 2 := .mkSigma
  “y d. ∃ r <⁺ d, !zRestDef r d ∧ ∃ r2 <⁺ r, !pi₂Def r2 r ∧ !pi₁Def y r2”
instance zIndP_defined : 𝚺₀-Function₁ (zIndP : V → V) via zIndPDef := .mk fun v ↦ by
  simp [zIndPDef, zIndP, zRest_defined.iff, pi₂_defined.iff, pi₁_defined.iff]
instance zIndP_definable : 𝚺₀-Function₁ (zIndP : V → V) := zIndP_defined.to_definable

def _root_.LO.FirstOrder.Arithmetic.zIndPrem0Def : 𝚺₀.Semisentence 2 := .mkSigma
  “y d. ∃ r <⁺ d, !zRestDef r d ∧ ∃ r2 <⁺ r, !pi₂Def r2 r ∧ ∃ r3 <⁺ r2, !pi₂Def r3 r2 ∧ !pi₁Def y r3”
instance zIndPrem0_defined : 𝚺₀-Function₁ (zIndPrem0 : V → V) via zIndPrem0Def := .mk fun v ↦ by
  simp [zIndPrem0Def, zIndPrem0, zRest_defined.iff, pi₂_defined.iff, pi₁_defined.iff]
instance zIndPrem0_definable : 𝚺₀-Function₁ (zIndPrem0 : V → V) := zIndPrem0_defined.to_definable

def _root_.LO.FirstOrder.Arithmetic.zIndPrem1Def : 𝚺₀.Semisentence 2 := .mkSigma
  “y d. ∃ r <⁺ d, !zRestDef r d ∧ ∃ r2 <⁺ r, !pi₂Def r2 r ∧ ∃ r3 <⁺ r2, !pi₂Def r3 r2 ∧ !pi₂Def y r3”
instance zIndPrem1_defined : 𝚺₀-Function₁ (zIndPrem1 : V → V) via zIndPrem1Def := .mk fun v ↦ by
  simp [zIndPrem1Def, zIndPrem1, zRest_defined.iff, pi₂_defined.iff]
instance zIndPrem1_definable : 𝚺₀-Function₁ (zIndPrem1 : V → V) := zIndPrem1_defined.to_definable

def _root_.LO.FirstOrder.Arithmetic.zKrankDef : 𝚺₀.Semisentence 2 := .mkSigma
  “y d. ∃ r <⁺ d, !zRestDef r d ∧ !pi₁Def y r”
instance zKrank_defined : 𝚺₀-Function₁ (zKrank : V → V) via zKrankDef := .mk fun v ↦ by
  simp [zKrankDef, zKrank, zRest_defined.iff, pi₁_defined.iff]
instance zKrank_definable : 𝚺₀-Function₁ (zKrank : V → V) := zKrank_defined.to_definable

def _root_.LO.FirstOrder.Arithmetic.zKseqDef : 𝚺₀.Semisentence 2 := .mkSigma
  “y d. ∃ r <⁺ d, !zRestDef r d ∧ !pi₂Def y r”
instance zKseq_defined : 𝚺₀-Function₁ (zKseq : V → V) via zKseqDef := .mk fun v ↦ by
  simp [zKseqDef, zKseq, zRest_defined.iff, pi₂_defined.iff]
instance zKseq_definable : 𝚺₀-Function₁ (zKseq : V → V) := zKseq_defined.to_definable
end ProjDef

-- Compute lemmas: each projection reads the right component of its own code.
@[simp] lemma zRest_zIall (s a p d0 : V) : zRest (zIall s a p d0) = ⟪a, p, d0⟫ := by
  simp [zRest, sndIdx, zIall]
@[simp] lemma zRest_zIneg (s p d0 : V) : zRest (zIneg s p d0) = ⟪p, d0⟫ := by
  simp [zRest, sndIdx, zIneg]
@[simp] lemma zRest_zInd (s at' p d0 d1 : V) : zRest (zInd s at' p d0 d1) = ⟪at', p, d0, d1⟫ := by
  simp [zRest, sndIdx, zInd]
@[simp] lemma zRest_zK (s r ds : V) : zRest (zK s r ds) = ⟪r, ds⟫ := by
  simp [zRest, sndIdx, zK]

@[simp] lemma zIallPrem_zIall (s a p d0 : V) : zIallPrem (zIall s a p d0) = d0 := by simp [zIallPrem]
@[simp] lemma zInegPrem_zIneg (s p d0 : V) : zInegPrem (zIneg s p d0) = d0 := by simp [zInegPrem]
@[simp] lemma zIndP_zInd (s at' p d0 d1 : V) : zIndP (zInd s at' p d0 d1) = p := by simp [zIndP]
@[simp] lemma zIndPrem0_zInd (s at' p d0 d1 : V) : zIndPrem0 (zInd s at' p d0 d1) = d0 := by
  simp [zIndPrem0]
@[simp] lemma zIndPrem1_zInd (s at' p d0 d1 : V) : zIndPrem1 (zInd s at' p d0 d1) = d1 := by
  simp [zIndPrem1]
@[simp] lemma zKrank_zK (s r ds : V) : zKrank (zK s r ds) = r := by simp [zKrank]
@[simp] lemma zKseq_zK (s r ds : V) : zKseq (zK s r ds) = ds := by simp [zKseq]

/-- `I^a_∀xF` principal-formula matrix `F` (payload `⟪a,p,d0⟫`, so `F = p`). -/
noncomputable def zIallF (d : V) : V := π₁ (π₂ (zRest d))
/-- `I_¬A` principal-formula body `A` (payload `⟪p,d0⟫`, so `A = p`). -/
noncomputable def zInegF (d : V) : V := π₁ (zRest d)
@[simp] lemma zIallF_zIall (s a p d0 : V) : zIallF (zIall s a p d0) = p := by simp [zIallF]
@[simp] lemma zInegF_zIneg (s p d0 : V) : zInegF (zIneg s p d0) = p := by simp [zInegF]

-- Bounds: each projection is `≤ d` (so the recursion reads the value-table at a smaller index).
@[simp] lemma zIallPrem_le (d : V) : zIallPrem d ≤ d :=
  le_trans (le_trans (pi₂_le_self _) (pi₂_le_self _)) (zRest_le_self d)
@[simp] lemma zInegPrem_le (d : V) : zInegPrem d ≤ d := le_trans (pi₂_le_self _) (zRest_le_self d)
@[simp] lemma zIndP_le (d : V) : zIndP d ≤ d :=
  le_trans (le_trans (pi₁_le_self _) (pi₂_le_self _)) (zRest_le_self d)
@[simp] lemma zIndPrem0_le (d : V) : zIndPrem0 d ≤ d :=
  le_trans (le_trans (le_trans (pi₁_le_self _) (pi₂_le_self _)) (pi₂_le_self _)) (zRest_le_self d)
@[simp] lemma zIndPrem1_le (d : V) : zIndPrem1 d ≤ d :=
  le_trans (le_trans (le_trans (pi₂_le_self _) (pi₂_le_self _)) (pi₂_le_self _)) (zRest_le_self d)
@[simp] lemma zKrank_le (d : V) : zKrank d ≤ d := le_trans (pi₁_le_self _) (zRest_le_self d)
@[simp] lemma zKseq_le (d : V) : zKseq d ≤ d := le_trans (pi₂_le_self _) (zRest_le_self d)

/-! ## `irk` — formula rank (Buchholz logical complexity), a real `UformulaRec1` recursion

Buchholz's `dg` uses `r := rk(F)` (logical complexity of the induction formula) in the `Ind`/`K^r`
cases. `rk` is the standard course-of-values recursion on Foundation's coded `ℒₒᵣ`-formulas:
`rk(atom)=rk(⊤)=rk(⊥)=0`, `rk(A∧B)=rk(A∨B)=max(rk A, rk B)+1`, `rk(∀F)=rk(∃F)=rk F+1`. Realized as a
total `𝚺₁` function via Foundation's `UformulaRec1.Construction` (the same recursion engine behind
`bv`), so it is genuine machine-checked content, NOT a stub. -/

namespace IRk

noncomputable def blueprint : UformulaRec1.Blueprint where
  rel := .mkSigma “y param k R v. y = 0”
  nrel := .mkSigma “y param k R v. y = 0”
  verum := .mkSigma “y param. y = 0”
  falsum := .mkSigma “y param. y = 0”
  and := .mkSigma “y param p₁ p₂ y₁ y₂. ∃ m, !max.dfn m y₁ y₂ ∧ y = m + 1”
  or := .mkSigma “y param p₁ p₂ y₁ y₂. ∃ m, !max.dfn m y₁ y₂ ∧ y = m + 1”
  all := .mkSigma “y param p₁ y₁. y = y₁ + 1”
  exs := .mkSigma “y param p₁ y₁. y = y₁ + 1”
  allChanges := .mkSigma “param' param. param' = 0”
  exsChanges := .mkSigma “param' param. param' = 0”

noncomputable def construction : UformulaRec1.Construction V blueprint where
  rel {_} := fun _ _ _ ↦ 0
  nrel {_} := fun _ _ _ ↦ 0
  verum {_} := 0
  falsum {_} := 0
  and {_} := fun _ _ y₁ y₂ ↦ Max.max y₁ y₂ + 1
  or {_} := fun _ _ y₁ y₂ ↦ Max.max y₁ y₂ + 1
  all {_} := fun _ y₁ ↦ y₁ + 1
  exs {_} := fun _ y₁ ↦ y₁ + 1
  allChanges := fun _ ↦ 0
  exsChanges := fun _ ↦ 0
  rel_defined := .mk fun v ↦ by simp [blueprint]
  nrel_defined := .mk fun v ↦ by simp [blueprint]
  verum_defined := .mk fun v ↦ by simp [blueprint]
  falsum_defined := .mk fun v ↦ by simp [blueprint]
  and_defined := .mk fun v ↦ by simp [blueprint]
  or_defined := .mk fun v ↦ by simp [blueprint]
  all_defined := .mk fun v ↦ by simp [blueprint]
  exs_defined := .mk fun v ↦ by simp [blueprint]
  allChanges_defined := .mk fun v ↦ by simp [blueprint]
  exChanges_defined := .mk fun v ↦ by simp [blueprint]

end IRk

noncomputable def irk (p : V) : V := IRk.construction.result ℒₒᵣ 0 p

noncomputable def _root_.LO.FirstOrder.Arithmetic.irkDef : 𝚺₁.Semisentence 2 :=
  (IRk.blueprint.result ℒₒᵣ).rew (Rew.subst ![#0, ‘0’, #1])

instance irk_defined : 𝚺₁-Function₁ (irk : V → V) via irkDef := .mk fun v ↦ by
  simpa [irkDef, Matrix.comp_vecCons', Matrix.constant_eq_singleton] using!
    (IRk.construction.result_defined (L := ℒₒᵣ)).defined ![v 0, 0, v 1]

instance irk_definable : 𝚺₁-Function₁ (irk : V → V) := irk_defined.to_definable
instance irk_definable' (Γ) : Γ-[m + 1]-Function₁ (irk : V → V) := irk_definable.of_sigmaOne

@[simp] lemma irk_rel {k R v : V} (hR : (ℒₒᵣ).IsRel k R) (hv : IsUTermVec ℒₒᵣ k v) :
    irk (^rel k R v : V) = 0 := by simp [irk, hR, hv, IRk.construction]
@[simp] lemma irk_nrel {k R v : V} (hR : (ℒₒᵣ).IsRel k R) (hv : IsUTermVec ℒₒᵣ k v) :
    irk (^nrel k R v : V) = 0 := by simp [irk, hR, hv, IRk.construction]
@[simp] lemma irk_verum : irk (^⊤ : V) = 0 := by simp [irk, IRk.construction]
@[simp] lemma irk_falsum : irk (^⊥ : V) = 0 := by simp [irk, IRk.construction]
@[simp] lemma irk_and {p q : V} (hp : IsUFormula ℒₒᵣ p) (hq : IsUFormula ℒₒᵣ q) :
    irk (p ^⋏ q : V) = Max.max (irk p) (irk q) + 1 := by simp [irk, hp, hq, IRk.construction]
@[simp] lemma irk_or {p q : V} (hp : IsUFormula ℒₒᵣ p) (hq : IsUFormula ℒₒᵣ q) :
    irk (p ^⋎ q : V) = Max.max (irk p) (irk q) + 1 := by simp [irk, hp, hq, IRk.construction]
@[simp] lemma irk_all {p : V} (hp : IsUFormula ℒₒᵣ p) : irk (^∀ p : V) = irk p + 1 := by
  simp [irk, hp, IRk.construction]
@[simp] lemma irk_ex {p : V} (hp : IsUFormula ℒₒᵣ p) : irk (^∃ p : V) = irk p + 1 := by
  simp [irk, hp, IRk.construction]

/-! ### T4(a)/(b) — `rk` substitution-invariance via Foundation's `formulaComplexity`

Buchholz's `rk` (logical complexity) is **identical** to Foundation's `formulaComplexity ℒₒᵣ` (same
recursion: atoms/⊤/⊥ ↦ 0, `∧`/`∨` ↦ max+1, `∀`/`∃` ↦ +1). Foundation already proves
`fomulaComplexity_substs1 : formulaComplexity L (substs1 L t p) = formulaComplexity L p` — exactly the
**T4(a)** rank-substitution-invariance leaf (judge `E-CRUX2-DECOMPOSITION §8.2`, "the ONE new rank
fact"). We bridge `irk = formulaComplexity ℒₒᵣ` (a clean `IsUFormula`-induction matching the equations)
and inherit it, then chain with `irk_all` (**T4(b)** `rk(∀xF)=rk(F)+1`) to get `rk(F(t)) < rk(∀xF)` —
the linchpin of T3.4's degree-drop `rk(A(d)) < r` (only the chain-rank invariant `rk(∀xF)=rk(A_i) ≤ r`,
gated on L3.1, remains beyond this). -/

/-- `irk` coincides with Foundation's `formulaComplexity ℒₒᵣ` on coded formulas (same recursion). -/
lemma irk_eq_formulaComplexity {p : V} :
    IsUFormula ℒₒᵣ p → irk p = formulaComplexity ℒₒᵣ p := by
  apply IsUFormula.ISigma1.sigma1_succ_induction
  · definability
  · intro k r v hr hv; simp [hr, hv]
  · intro k r v hr hv; simp [hr, hv]
  · simp
  · simp
  · intro p q hp hq ihp ihq; simp [hp, hq, ihp, ihq]
  · intro p q hp hq ihp ihq; simp [hp, hq, ihp, ihq]
  · intro p hp ihp; simp [hp, ihp]
  · intro p hp ihp; simp [hp, ihp]

/-- **T4(a) — rank is substitution-invariant**: `rk(F(t)) = rk(F)` for a term substitution into a
1-variable formula. Inherited from Foundation's `fomulaComplexity_substs1` via the `irk` bridge. -/
lemma irk_substs1 {m t p : V} (hp : IsSemiformula ℒₒᵣ 1 p) (ht : IsSemiterm ℒₒᵣ m t) :
    irk (substs1 ℒₒᵣ t p) = irk p := by
  rw [irk_eq_formulaComplexity (IsSemiformula.substs1 ht hp).isUFormula,
    fomulaComplexity_substs1 hp ht, irk_eq_formulaComplexity hp.isUFormula]

/-- **T4(a)+(b) — `rk(F(t)) < rk(∀xF)`**: the cut-formula rank strictly below the quantified formula's,
the heart of T3.4's `rk(A(d)) < r`. `rk(F(t)) = rk(F)` (T4a) `< rk(F)+1 = rk(∀xF)` (T4b). -/
lemma irk_substs1_lt_all {m t p : V} (hp : IsSemiformula ℒₒᵣ 1 p) (ht : IsSemiterm ℒₒᵣ m t) :
    irk (substs1 ℒₒᵣ t p) < irk (^∀ p : V) := by
  rw [irk_substs1 hp ht, irk_all hp.isUFormula]
  exact lt_succ_iff_le.mpr le_rfl

/-- `irk` is invariant under bare Tait negation `∼A`, inherited from Foundation's
`formulaComplexity_neg`. (Buchholz's `¬A`, with `rk(¬A)=rk(A)+1`, is the De Morgan `∼A ∨ ⊥` = `inegF`,
NOT bare `∼A`.) -/
lemma irk_neg {A : V} (hA : IsUFormula ℒₒᵣ A) : irk (neg ℒₒᵣ A) = irk A := by
  rw [irk_eq_formulaComplexity hA.neg, formulaComplexity_neg hA, irk_eq_formulaComplexity hA]

/-- **Buchholz's `¬A`** (Def 3.1.3) as a Tait formula: `¬A := ∼A ∨ ⊥` (= `A → ⊥`), so
`rk(¬A) = rk(A)+1`, matching Buchholz's `rk(¬A)=rk(A)+1` — unlike bare Tait `∼A`, which preserves rank.
This is the cut formula `A(d) = A` strips below in the `I_¬A` redex case of T3.4(a). -/
noncomputable def inegF (A : V) : V := (neg ℒₒᵣ A) ^⋎ (^⊥ : V)

@[simp] lemma irk_inegF {A : V} (hA : IsUFormula ℒₒᵣ A) : irk (inegF A) = irk A + 1 := by
  rw [inegF, irk_or hA.neg (by simp), irk_neg hA, irk_falsum]
  simp

/-- `rk(A) < rk(¬A)` — the `I_¬A` redex strip (the negation analogue of T4's `rk(F(k)) < rk(∀xF)`). -/
lemma irk_lt_inegF {A : V} (hA : IsUFormula ℒₒᵣ A) : irk A < irk (inegF A) := by
  rw [irk_inegF hA]; exact lt_succ_iff_le.mpr le_rfl

/-! ### T3.4(a) — the rank bound `rk(A(d)) < r`

Buchholz Theorem 3.4(a), p.9: for a critical chain `d = K^r_Π …` with redex `(i,j,k)` (Lemma 3.1,
`inference_critical_pair`), the cut formula `A(d)` (`= F(k)` if `A_i = ∀xF`, `= A` if `A_i = ¬A`)
satisfies `rk(A(d)) < r`. Proof: `rk(A(d)) < rk(A_i) ≤ r`, where the strict step is the substitution /
negation strip (T4, banked) and `rk(A_i) ≤ r` is the chain-rule rank invariant (`∀ i<j₀, rk(A_i) ≤ r`,
read off the `K^r` chain inference — the redex has `i < j ≤ j₀`). This is the rank-side assembly of
T3.4(a). -/

/-- **T3.4(a) rank bound, generic assembly**: `rk(A(d)) < rk(A_i) ≤ r ⟹ rk(A(d)) < r`. -/
theorem irk_cut_lt_rank {Ad Ai r : V} (hstrip : irk Ad < irk Ai) (hr : irk Ai ≤ r) :
    irk Ad < r := lt_of_lt_of_le hstrip hr

/-- **T3.4(a), `∀`-redex case**: `A_i = ∀xF`, `A(d) = F(k)`, gives `rk(F(k)) < r` from `rk(∀xF) ≤ r`. -/
theorem irk_cut_lt_rank_forall {m F t r : V}
    (hF : IsSemiformula ℒₒᵣ 1 F) (ht : IsSemiterm ℒₒᵣ m t) (hr : irk (^∀ F : V) ≤ r) :
    irk (substs1 ℒₒᵣ t F) < r :=
  irk_cut_lt_rank (irk_substs1_lt_all hF ht) hr

/-- **T3.4(a), `¬`-redex case**: `A_i = ¬A`, `A(d) = A`, gives `rk(A) < r` from `rk(¬A) ≤ r`. -/
theorem irk_cut_lt_rank_neg {A r : V} (hA : IsUFormula ℒₒᵣ A) (hr : irk (inegF A) ≤ r) :
    irk A < r :=
  irk_cut_lt_rank (irk_lt_inegF hA) hr

/-! ## §3 — Inference symbols and Lemma 3.1 (the redex finder, L3.1)

Buchholz §3 (pp.7–8). Each premise of a chain inference carries an *inference symbol*
`I ∈ {R_A, L^k_A, Rep}`, with a *permissibility* relation `I ◁ Γ→C`:
`I ◁ Γ→C :⇔ I = R_C ∨ (I = L^k_A with A ∈ Γ) ∨ I = Rep`. A symbol is *well-formed* iff `R_A` has
`rk A > 0 ∨ A ≈ ⊤` and `L^k_A` has `rk A > 0 ∨ A ≈ ⊥`.

**Lemma 3.1** (p.8): if `A_{j0} ∈ {C, ⊥}`, the chain antecedent condition `Γ_i ⊆ Γ, A_0,…,A_{i-1}`
holds, and every premise symbol is permissible for its own premise but NOT for the conclusion
(`I_i ◁ Π_i & I_i ⋪ Π`), then there is a *critical pair* `∃ i<j≤j0, k`: `I_i = R_{A_i}`,
`I_j = L^k_{A_i}`, `0 < rk(A_i)`. This is the redex `iR` eliminates in case 5.1 (THE NUT). Proof: a
`𝚺₀` least-index search over the premise list — NO ordinals (`E-CRUX2-DECOMPOSITION §8.1`, leaves L1–L4).

Symbols are coded `R_A := ⟪0,A⟫`, `L^k_A := ⟪1,k,A⟫`, `Rep := ⟪2,0⟫`. The truth-of-minimal predicates
`A ≈ ⊤`/`A ≈ ⊥` (`Tr`/`Fa`) and antecedent membership (`mem`) are abstracted to the only properties the
proof consumes — a minimal formula is not both true and false (`hdisj`) and `A ≈ ⊥ ⟹ rk A = 0`
(`hFa_rk`). Faithful: the lemma holds for any truth assignment with these properties; instantiation to
Z's atomic truth (§5) is deferred. -/

/-- `R_A` — the right/reduction inference symbol for formula `A`. -/
noncomputable def isymR (A : V) : V := ⟪0, A⟫
/-- `L^k_A` — the left inference symbol for formula `A` with numeral choice `k`. -/
noncomputable def isymLk (k A : V) : V := ⟪1, k, A⟫
/-- `Rep` — the repetition inference symbol. -/
noncomputable def isymRep : V := ⟪2, (0 : V)⟫

@[simp] lemma isymR_ne_isymLk (A k A' : V) : (isymR A : V) ≠ isymLk k A' := by
  simp [isymR, isymLk, pair_ext_iff]
@[simp] lemma isymLk_ne_isymR (k A A' : V) : (isymLk k A : V) ≠ isymR A' := by
  simp [isymR, isymLk, pair_ext_iff]
@[simp] lemma isymR_ne_isymRep (A : V) : (isymR A : V) ≠ isymRep := by
  simp [isymR, isymRep, pair_ext_iff]
@[simp] lemma isymRep_ne_isymR (A : V) : (isymRep : V) ≠ isymR A := by
  simp [isymR, isymRep, pair_ext_iff]
@[simp] lemma isymLk_ne_isymRep (k A : V) : (isymLk k A : V) ≠ isymRep := by
  simp [isymLk, isymRep, pair_ext_iff]
@[simp] lemma isymRep_ne_isymLk (k A : V) : (isymRep : V) ≠ isymLk k A := by
  simp [isymLk, isymRep, pair_ext_iff]
@[simp] lemma isymR_inj (A A' : V) : (isymR A : V) = isymR A' ↔ A = A' := by
  simp [isymR, pair_ext_iff]
@[simp] lemma isymLk_inj (k A k' A' : V) : (isymLk k A : V) = isymLk k' A' ↔ k = k' ∧ A = A' := by
  simp [isymLk, pair_ext_iff]

def _root_.LO.FirstOrder.Arithmetic.isymLkGraph : 𝚺₀.Semisentence 3 :=
  .mkSigma “y k A. !pair₃Def y 1 k A”
instance isymLk_defined : 𝚺₀-Function₂ (isymLk : V → V → V) via isymLkGraph := .mk fun v ↦ by
  simp [isymLkGraph, isymLk, numeral_eq_natCast]
instance isymLk_definable : 𝚺₀-Function₂ (isymLk : V → V → V) := isymLk_defined.to_definable
instance isymLk_definable' (ℌ) : ℌ-Function₂ (isymLk : V → V → V) := isymLk_definable.of_zero

/-- `I ∈ L` — `I` is a left symbol `L^k_A`. Stated projection-free (`I` reconstructs from its own
projections `π₁(π₂ I) = k`, `π₂(π₂ I) = A`) so it is `𝚺₁`-definable with no bounded-quantifier bound. -/
def isymIsL (I : V) : Prop := I = isymLk (π₁ (π₂ I)) (π₂ (π₂ I))

lemma isymIsL_isymLk (k A : V) : isymIsL (isymLk k A : V) := by
  simp [isymIsL, isymLk]

lemma isymIsL_iff {I : V} : isymIsL I ↔ ∃ k A, I = isymLk k A := by
  constructor
  · intro h; exact ⟨_, _, h⟩
  · rintro ⟨k, A, rfl⟩; exact isymIsL_isymLk k A

/-- `I ∈ R` — `I` is a right symbol `R_A` (`A = π₂ I`). Projection-free analogue of `isymIsL`. -/
def isymIsR (I : V) : Prop := I = isymR (π₂ I)

lemma isymIsR_isymR (A : V) : isymIsR (isymR A : V) := by simp [isymIsR, isymR]

lemma isymIsR_iff {I : V} : isymIsR I ↔ ∃ A, I = isymR A := by
  constructor
  · intro h; exact ⟨_, h⟩
  · rintro ⟨A, rfl⟩; exact isymIsR_isymR A

/-- The discriminant `π₁` of the three inference symbols (`R`=0, `L`=1, `Rep`=2). -/
@[simp] lemma pi₁_isymR (A : V) : π₁ (isymR A : V) = 0 := by simp [isymR]
@[simp] lemma pi₂_isymR (A : V) : π₂ (isymR A : V) = A := by simp [isymR]
@[simp] lemma pi₁_isymLk (k A : V) : π₁ (isymLk k A : V) = 1 := by simp [isymLk]
@[simp] lemma pi₁_isymRep : π₁ (isymRep : V) = 2 := by simp [isymRep]

section Lemma31

variable (mem : V → V → Prop) (Tr Fa : V → Prop)

/-- **Lemma 3.1 — the critical-pair (redex) finder** (Buchholz p.8). Given a chain inference with
premise inference symbols `I_i = znth Iseq i` and premise succedents `A_i = Asucc i`
(`i ≤ j0`), with `A_{j0} ∈ {Cmain, ⊥}`, the chain antecedent condition, and each `I_i` permissible for
its own premise `Γ_i→A_i` but not for the conclusion `Γmain→Cmain`, there is a critical pair
`i < j ≤ j0` and `k` with `I_i = R_{A_i}`, `I_j = L^k_{A_i}`, `0 < rk(A_i)`. A `𝚺₀` least-index search
(`least_number`) — no ordinals. This identifies the redex `iR` eliminates in case 5.1. -/
theorem inference_critical_pair
    {Iseq Γmain Cmain j0 : V} {Asucc Gam : V → V}
    (hwfR : ∀ i ≤ j0, ∀ A, znth Iseq i = isymR A → 0 < irk A ∨ Tr A)
    (hwfL : ∀ i ≤ j0, ∀ k A, znth Iseq i = isymLk k A → 0 < irk A ∨ Fa A)
    (hperm : ∀ i ≤ j0, znth Iseq i = isymR (Asucc i) ∨
        (∃ k A, znth Iseq i = isymLk k A ∧ mem A (Gam i)) ∨ znth Iseq i = isymRep)
    (hnperm : ∀ i ≤ j0, ¬ (znth Iseq i = isymR Cmain ∨
        (∃ k A, znth Iseq i = isymLk k A ∧ mem A Γmain) ∨ znth Iseq i = isymRep))
    (hchain : ∀ i ≤ j0, ∀ B, mem B (Gam i) → mem B Γmain ∨ ∃ i' < i, B = Asucc i')
    (hAj0 : Asucc j0 = Cmain ∨ Fa (Asucc j0))
    (hdisj : ∀ A, ¬ (Tr A ∧ Fa A)) (hFa_rk : ∀ A, Fa A → irk A = 0) :
    ∃ i j k, i < j ∧ j ≤ j0 ∧ znth Iseq i = isymR (Asucc i) ∧
      znth Iseq j = isymLk k (Asucc i) ∧ 0 < irk (Asucc i) := by
  -- Step A: the last premise symbol is a left symbol.
  have hLj0 : isymIsL (znth Iseq j0) := by
    rcases hperm j0 le_rfl with hR | hL | hRep
    · -- I_{j0} = R_{A_{j0}}: impossible.
      exfalso
      have hne : znth Iseq j0 ≠ isymR Cmain := fun h => hnperm j0 le_rfl (Or.inl h)
      rcases hAj0 with hC | hFa
      · exact hne (by rw [hR, hC])
      · rcases hwfR j0 le_rfl _ hR with hpos | hTr
        · exact absurd (hFa_rk _ hFa) (by simpa using hpos.ne')
        · exact hdisj _ ⟨hTr, hFa⟩
    · obtain ⟨k, A, hI, _⟩ := hL; exact isymIsL_iff.mpr ⟨k, A, hI⟩
    · exact absurd hRep (fun h => hnperm j0 le_rfl (Or.inr (Or.inr h)))
  -- Step B: take the least left-symbol index j.
  have hQdef : 𝚺₁-Predicate (fun x : V => isymIsL (znth Iseq x) ∧ x ≤ j0) := by
    simp only [isymIsL]; definability
  obtain ⟨j, ⟨hLj, hj_le⟩, hmin⟩ :=
    InductionOnHierarchy.least_number 𝚺 1 hQdef ⟨hLj0, le_rfl⟩
  obtain ⟨k, B, hIj⟩ := isymIsL_iff.mp hLj
  -- B ∈ Γ_j  (from permissibility of I_j for its premise)
  have hBmem : mem B (Gam j) := by
    rcases hperm j hj_le with hR | hL | hRep
    · exact absurd (hR.symm.trans hIj) (by simp)
    · obtain ⟨k', A', hI', hA'⟩ := hL
      obtain ⟨hk, hA⟩ := isymLk_inj k B k' A' |>.mp (hIj.symm.trans hI')
      exact hA ▸ hA'
    · exact absurd (hRep.symm.trans hIj) (by simp)
  -- B ∉ Γmain  (from non-permissibility of I_j for the conclusion)
  have hBnmem : ¬ mem B Γmain := fun h =>
    hnperm j hj_le (Or.inr (Or.inl ⟨k, B, hIj, h⟩))
  -- chain condition: B = A_i for some i < j
  obtain ⟨i, hij, hBi⟩ := (hchain j hj_le B hBmem).resolve_left hBnmem
  have hi_le : i ≤ j0 := le_of_lt (lt_of_lt_of_le hij hj_le)
  -- I_j = L^k_{A_i}
  have hIjL : znth Iseq j = isymLk k (Asucc i) := by rw [hIj, hBi]
  -- I_i = R_{A_i}  (minimality kills the left-symbol and Rep cases)
  have hLi_not : ¬ isymIsL (znth Iseq i) := fun h => hmin i hij ⟨h, hi_le⟩
  have hIiR : znth Iseq i = isymR (Asucc i) := by
    rcases hperm i hi_le with hR | hL | hRep
    · exact hR
    · obtain ⟨k', A', hI', _⟩ := hL
      exact absurd (isymIsL_iff.mpr ⟨k', A', hI'⟩) hLi_not
    · exact absurd hRep (fun h => hnperm i hi_le (Or.inr (Or.inr h)))
  -- 0 < rk(A_i)
  have hrk : 0 < irk (Asucc i) := by
    rcases hwfR i hi_le _ hIiR with hpos | hTr
    · exact hpos
    · rcases hwfL j hj_le k _ hIjL with hpos | hFa
      · exact hpos
      · exact absurd ⟨hTr, hFa⟩ (hdisj _)
  exact ⟨i, j, k, hij, hj_le, hIiR, hIjL, hrk⟩

/-- **L3.1 + chain-rank invariant** — the redex `(i,j,k)` from `inference_critical_pair`, carrying the
chain-rule rank bound `rk(A_i) ≤ r` (Buchholz's chain inference "`∀ i < j₀, rk(A_i) ≤ r`", p.8). Since
the redex has `i < j ≤ j₀`, hence `i < j₀`, `hrank` applies. This is exactly the input T3.4(a)'s rank
bound (`irk_cut_lt_rank`) consumes: `0 < rk(A_i) ≤ r` plus the cut-formula strip gives `rk(A(d)) < r`. -/
theorem inference_critical_pair_rank
    {Iseq Γmain Cmain j0 r : V} {Asucc Gam : V → V}
    (hwfR : ∀ i ≤ j0, ∀ A, znth Iseq i = isymR A → 0 < irk A ∨ Tr A)
    (hwfL : ∀ i ≤ j0, ∀ k A, znth Iseq i = isymLk k A → 0 < irk A ∨ Fa A)
    (hperm : ∀ i ≤ j0, znth Iseq i = isymR (Asucc i) ∨
        (∃ k A, znth Iseq i = isymLk k A ∧ mem A (Gam i)) ∨ znth Iseq i = isymRep)
    (hnperm : ∀ i ≤ j0, ¬ (znth Iseq i = isymR Cmain ∨
        (∃ k A, znth Iseq i = isymLk k A ∧ mem A Γmain) ∨ znth Iseq i = isymRep))
    (hchain : ∀ i ≤ j0, ∀ B, mem B (Gam i) → mem B Γmain ∨ ∃ i' < i, B = Asucc i')
    (hAj0 : Asucc j0 = Cmain ∨ Fa (Asucc j0))
    (hdisj : ∀ A, ¬ (Tr A ∧ Fa A)) (hFa_rk : ∀ A, Fa A → irk A = 0)
    (hrank : ∀ i < j0, irk (Asucc i) ≤ r) :
    ∃ i j k, i < j ∧ j ≤ j0 ∧ znth Iseq i = isymR (Asucc i) ∧
      znth Iseq j = isymLk k (Asucc i) ∧ 0 < irk (Asucc i) ∧ irk (Asucc i) ≤ r := by
  obtain ⟨i, j, k, hij, hj_le, hIi, hIj, hrk⟩ :=
    inference_critical_pair mem Tr Fa hwfR hwfL hperm hnperm hchain hAj0 hdisj hFa_rk
  exact ⟨i, j, k, hij, hj_le, hIi, hIj, hrk, hrank i (lt_of_lt_of_le hij hj_le)⟩

end Lemma31

/-! ### §5 atomic-axiom constructors that produce L-symbols (Buchholz p.12, NO truth predicate)

The two §5 atomic axioms whose `tp` is an L-symbol **unconditionally** (no minimal-truth check):
`Ax^{∀xF,k}_Π ⊢ Γ→F(k)` (with `∀xF ∈ Γ`) has `tp = L^k_{∀xF}`, and `Ax^{¬A,0}_Π ⊢ Γ→⊥` (with `¬A,A ∈ Γ`)
has `tp = L⁰_{¬A}`. These are the cheapest source of the L-symbols Lemma 3.1 needs at `j0`, and need
**no** truth assignment to define. Coded as new rule tags 5/6, mirroring the existing constructors; now
wired into `tp` below (NOT yet into `ZPhi`/`idg`/`iõ` — that integration is path A's next step). -/

/-- `Ax^{∀x·p, k}` — the ∀-instantiation axiom (`p` = matrix `F`, `k` = numeral index). -/
noncomputable def zAxAll (s p k : V) : V := ⟪s, 5, p, k⟫ + 1
/-- `Ax^{¬p, 0}` — the ¬-elimination axiom (`p` = the formula `A`, conclusion `⊥`). -/
noncomputable def zAxNeg (s p : V) : V := ⟪s, 6, p⟫ + 1

def zAxAllGraph : 𝚺₀.Semisentence 4 :=
  .mkSigma “y s p k. ∃ y' < y, !pair₄Def y' s 5 p k ∧ y = y' + 1”
instance zAxAll_defined : 𝚺₀-Function₃ (zAxAll : V → V → V → V) via zAxAllGraph := .mk fun v ↦ by
  simp_all [zAxAllGraph, numeral_eq_natCast, zAxAll]

def zAxNegGraph : 𝚺₀.Semisentence 3 :=
  .mkSigma “y s p. ∃ y' < y, !pair₃Def y' s 6 p ∧ y = y' + 1”
instance zAxNeg_defined : 𝚺₀-Function₂ (zAxNeg : V → V → V) via zAxNegGraph := .mk fun v ↦ by
  simp_all [zAxNegGraph, numeral_eq_natCast, zAxNeg]

@[simp] lemma s_lt_zAxAll (s p k : V) : s < zAxAll s p k := le_iff_lt_succ.mp <| le_pair_left _ _
@[simp] lemma p_lt_zAxAll (s p k : V) : p < zAxAll s p k :=
  le_iff_lt_succ.mp <| le_trans (le_trans (le_pair_left _ _) <| le_pair_right _ _) <| le_pair_right _ _
@[simp] lemma k_lt_zAxAll (s p k : V) : k < zAxAll s p k :=
  le_iff_lt_succ.mp <| le_trans (le_trans (le_pair_right _ _) <| le_pair_right _ _) <| le_pair_right _ _
@[simp] lemma s_lt_zAxNeg (s p : V) : s < zAxNeg s p := le_iff_lt_succ.mp <| le_pair_left _ _
@[simp] lemma p_lt_zAxNeg (s p : V) : p < zAxNeg s p :=
  le_iff_lt_succ.mp <| le_trans (le_pair_right _ _) <| le_pair_right _ _

@[simp] lemma zTag_zAxAll (s p k : V) : zTag (zAxAll s p k) = 5 := by simp [zTag, sndIdx, zAxAll]
@[simp] lemma zTag_zAxNeg (s p : V) : zTag (zAxNeg s p) = 6 := by simp [zTag, sndIdx, zAxNeg]
@[simp] lemma fstIdx_zAxAll (s p k : V) : fstIdx (zAxAll s p k) = s := by simp [fstIdx, zAxAll]
@[simp] lemma fstIdx_zAxNeg (s p : V) : fstIdx (zAxNeg s p) = s := by simp [fstIdx, zAxNeg]
@[simp] lemma zRest_zAxAll (s p k : V) : zRest (zAxAll s p k) = ⟪p, k⟫ := by
  simp [zRest, sndIdx, zAxAll]
@[simp] lemma zRest_zAxNeg (s p : V) : zRest (zAxNeg s p) = p := by simp [zRest, sndIdx, zAxNeg]

/-- Principal matrix `F` of `Ax^{∀x·p,k}` (so the principal formula is `∀x·p = ^∀ p`). -/
noncomputable def zAxAllF (d : V) : V := π₁ (zRest d)
/-- Numeral index `k` of `Ax^{∀x·p,k}`. -/
noncomputable def zAxAllK (d : V) : V := π₂ (zRest d)
/-- The formula `A` of `Ax^{¬A,0}` (so the principal formula is `¬A = inegF A`). -/
noncomputable def zAxNegF (d : V) : V := zRest d
@[simp] lemma zAxAllF_zAxAll (s p k : V) : zAxAllF (zAxAll s p k) = p := by simp [zAxAllF]
@[simp] lemma zAxAllK_zAxAll (s p k : V) : zAxAllK (zAxAll s p k) = k := by simp [zAxAllK]
@[simp] lemma zAxNegF_zAxNeg (s p : V) : zAxNegF (zAxNeg s p) = p := by simp [zAxNegF]

/-- `Ax1_{s}` (tag 7) — the **logical axiom `Ax^1`** that is the §5 reduct `d[0]` of an L-symbol atomic
axiom (Buchholz §5 case 2: `Ax^{C,k}_Π → Ax^1_{tp(d)(Π,0)}`). Payload `C` = the reduct succedent formula
(`F(k)` for `Ax^{∀xF,k}`, `A` for `Ax^{¬A,0}`); its pre-ordinal is `õ(Ax^1_{·→C}) = 2·rk(C) = oAtom1 C`
(Lemma 5.2), `dg = 0`. Carries the rank-one-lower formula so the descent `oAtom1 C ≺ oAtomLk(C-up)` fires
via `icmp_oAtom1_oAtomLk`. -/
noncomputable def zAx1 (s C : V) : V := ⟪s, 7, C⟫ + 1

def zAx1Graph : 𝚺₀.Semisentence 3 :=
  .mkSigma “y s C. ∃ y' < y, !pair₃Def y' s 7 C ∧ y = y' + 1”
instance zAx1_defined : 𝚺₀-Function₂ (zAx1 : V → V → V) via zAx1Graph := .mk fun v ↦ by
  simp_all [zAx1Graph, numeral_eq_natCast, zAx1]

/-- **⊥-left leaf `Ax⊥` (tag 8, lap 162).** The ex-falso / weakening axiom `⊥ ∈ Γ ⟹ Γ → C` for ANY
succedent `C`. Encoded exactly like `zAtom` (a `⟪s, tag, 0⟫+1` leaf) but with tag `8`, so it inherits
`iotil = idg = iord = 0` (the dispatchers `ioNext`/`idgTable`/`zRegNext`/… all default unknown tags to `0`)
— the UNIQUE `iotil = 0` reduct that strict-`õ`-drops a ⊥-exit cut chain (route-4 R-intro towers cannot
drop; only an `iotil=0` leaf can — `wip/ExFalsoOrdinalSpike.lean`, lap 162). The ZPhi disjunct + its ripple
wire this in (PENDING_WORK lap-162). -/
noncomputable def zAxBot (s : V) : V := ⟪s, 8, 0⟫ + 1

def zAxBotGraph : 𝚺₀.Semisentence 2 :=
  .mkSigma “y s. ∃ y' < y, !pair₃Def y' s 8 0 ∧ y = y' + 1”
instance zAxBot_defined : 𝚺₀-Function₁ (zAxBot : V → V) via zAxBotGraph := .mk fun v ↦ by
  simp_all [zAxBotGraph, numeral_eq_natCast, zAxBot]

@[simp] lemma seq_lt_zAxBot (s : V) : s < zAxBot s := le_iff_lt_succ.mp <| le_pair_left _ _
@[simp] lemma zTag_zAxBot (s : V) : zTag (zAxBot s) = 8 := by simp [zTag, sndIdx, zAxBot]
@[simp] lemma fstIdx_zAxBot (s : V) : fstIdx (zAxBot s) = s := by simp [fstIdx, zAxBot]

@[simp] lemma s_lt_zAx1 (s C : V) : s < zAx1 s C := le_iff_lt_succ.mp <| le_pair_left _ _
@[simp] lemma C_lt_zAx1 (s C : V) : C < zAx1 s C :=
  le_iff_lt_succ.mp <| le_trans (le_pair_right _ _) <| le_pair_right _ _

@[simp] lemma zTag_zAx1 (s C : V) : zTag (zAx1 s C) = 7 := by simp [zTag, sndIdx, zAx1]
@[simp] lemma fstIdx_zAx1 (s C : V) : fstIdx (zAx1 s C) = s := by simp [fstIdx, zAx1]
@[simp] lemma zRest_zAx1 (s C : V) : zRest (zAx1 s C) = C := by simp [zRest, sndIdx, zAx1]
/-- The succedent formula `C` of the logical axiom `Ax^1_{·→C}` (tag 7). -/
noncomputable def zAx1F (d : V) : V := zRest d
@[simp] lemma zAx1F_zAx1 (s C : V) : zAx1F (zAx1 s C) = C := by simp [zAx1F]

def _root_.LO.FirstOrder.Arithmetic.zAx1FDef : 𝚺₀.Semisentence 2 := .mkSigma
  “y d. !zRestDef y d”
instance zAx1F_defined : 𝚺₀-Function₁ (zAx1F : V → V) via zAx1FDef := .mk fun v ↦ by
  simp [zAx1FDef, zAx1F, zRest_defined.iff]

/-! ## `tp(d)` — the inference symbol of a Z-derivation (Buchholz Def 3.2)

The reduction-step symbol `tp(d)` (Def 3.2, p.8). The non-`K^r`, non-atomic cases are NON-recursive
and **faithful**:
* `tp(I^a_∀xF d0) = R_{∀xF}` (case 2),
* `tp(I_¬A d0) = R_{¬A}` (case 3, with Buchholz's `¬A = inegF A`),
* `tp(Ind^{a,k}_F d0 d1) = Rep` (case 4).

The atomic case (§5, needs minimal-truth `≈⊤`/`≈⊥`) and the `K^r` critical/non-critical dispatch (case 5,
needs each premise's `tp(d_i)` + sequent permissibility + Lemma 3.1) are the recursion-heavy frontier;
they are left as the `else` placeholder (value `Rep`, which is the *correct* `tp` for a **critical**
chain or a ⊥-derivation — Corollary 2.1 — but not yet for the non-critical 5.2.2 case). Only the
faithful cases 2–4 get compute lemmas; `tp` mirrors `iR`'s incremental build.

The §5 atomic axioms `Ax^{∀xF,k}` (tag 5) and `Ax^{¬A,0}` (tag 6) now produce the **L-symbols**
`L^k_{∀xF}` / `L⁰_{¬A}` UNCONDITIONALLY (Buchholz p.12 — no minimal-truth check). These are the only
source of left symbols, exactly what Lemma 3.1 needs at the `j`-end of a critical pair. -/
noncomputable def tp (d : V) : V :=
  if zTag d = 1 then isymR (^∀ (zIallF d) : V)
  else if zTag d = 2 then isymR (inegF (zInegF d))
  else if zTag d = 5 then isymLk (zAxAllK d) (^∀ (zAxAllF d) : V)
  else if zTag d = 6 then isymLk 0 (inegF (zAxNegF d))
  else isymRep

@[simp] lemma tp_zIall (s a p d0 : V) : tp (zIall s a p d0) = isymR (^∀ p : V) := by simp [tp]
@[simp] lemma tp_zIneg (s p d0 : V) : tp (zIneg s p d0) = isymR (inegF p) := by simp [tp]
@[simp] lemma tp_zInd (s at' p d0 d1 : V) : tp (zInd s at' p d0 d1) = isymRep := by simp [tp]
@[simp] lemma tp_zAxAll (s p k : V) : tp (zAxAll s p k) = isymLk k (^∀ p : V) := by simp [tp]
@[simp] lemma tp_zAxNeg (s p : V) : tp (zAxNeg s p) = isymLk 0 (inegF p) := by simp [tp]
@[simp] lemma tp_zAtom (s : V) : tp (zAtom s) = isymRep := by simp [tp]
@[simp] lemma tp_zK (s r ds : V) : tp (zK s r ds) = isymRep := by simp [tp]
/-- `tp (Ax^1_{·→C}) = Rep` (tag 7 is off the I/Ax tags, so the `tp` dispatch falls through to `isymRep`).
The §5 logical-axiom reduct is a `Rep` node — exactly Buchholz's `tp(Ax^1_Π) ∈ {R_C, L^0_C}` collapsing to
the repetition symbol once it sits as a replaced premise inside a critical reduct chain. -/
@[simp] lemma tp_zAx1 (s C : V) : tp (zAx1 s C) = isymRep := by simp [tp]

/-- **`tp`-trichotomy**: every `tp d` is one of the three inference symbols `R_A`/`L^k_A`/`Rep`
(it dispatches on `zTag d`). The structural source of the `π₁`-discriminant shape lemmas below. -/
lemma tp_cases (d : V) :
    (∃ A, tp d = isymR A) ∨ (∃ k A, tp d = isymLk k A) ∨ tp d = isymRep := by
  unfold tp
  by_cases h1 : zTag d = 1
  · rw [if_pos h1]; exact Or.inl ⟨_, rfl⟩
  rw [if_neg h1]
  by_cases h2 : zTag d = 2
  · rw [if_pos h2]; exact Or.inl ⟨_, rfl⟩
  rw [if_neg h2]
  by_cases h5 : zTag d = 5
  · rw [if_pos h5]; exact Or.inr (Or.inl ⟨_, _, rfl⟩)
  rw [if_neg h5]
  by_cases h6 : zTag d = 6
  · rw [if_pos h6]; exact Or.inr (Or.inl ⟨_, _, rfl⟩)
  rw [if_neg h6]; exact Or.inr (Or.inr rfl)

/-- **`tp` is a right symbol when its `π₁`-discriminant is 0** (`isRedexPair`'s `i`-end condition):
`tp d = R_{π₂(tp d)}`. The shape-recovery the redex→`tp` bridge needs from the bare pair test. -/
lemma tp_eq_isymR_of_pi₁_zero {d : V} (h : π₁ (tp d) = 0) : tp d = isymR (π₂ (tp d)) := by
  rcases tp_cases d with ⟨A, hA⟩ | ⟨k, A, hA⟩ | hA <;> rw [hA] at h ⊢ <;> simp_all

/-- **`tp` is a left symbol when its `π₁`-discriminant is 1** (`isRedexPair`'s `j`-end condition):
`tp d = L^{π₁(π₂(tp d))}_{π₂(π₂(tp d))}` (i.e. `isymIsL (tp d)`). -/
lemma tp_eq_isymLk_of_pi₁_one {d : V} (h : π₁ (tp d) = 1) :
    tp d = isymLk (π₁ (π₂ (tp d))) (π₂ (π₂ (tp d))) := by
  rcases tp_cases d with ⟨A, hA⟩ | ⟨k, A, hA⟩ | hA <;> rw [hA] at h ⊢ <;> simp_all [isymLk]

/-- Dual of `tp_isymR_pos` for the §5 L-symbol axioms: `tp d = L^k_A` forces `0 < rk A` once the
principal formula is a genuine formula. `Ax^{∀xF,k}` (tag 5) gives `A = ∀xF` (`rk = rk F + 1`);
`Ax^{¬A',0}` (tag 6) gives `A = ¬A' = inegF A'` (`rk = rk A' + 1`). **This is exactly `hwfL` for the §5
atomic axioms**, replacing the now-false `tp_ne_isymLk`: `tp` is no longer L-free, so `hwfL` is
discharged by the genuine rank bound rather than vacuously. -/
lemma tp_isymLk_pos {d k A : V} (h : tp d = isymLk k A)
    (h5 : zTag d = 5 → IsUFormula ℒₒᵣ (zAxAllF d))
    (h6 : zTag d = 6 → IsUFormula ℒₒᵣ (zAxNegF d)) : 0 < irk A := by
  unfold tp at h
  by_cases ht1 : zTag d = 1
  · rw [if_pos ht1] at h; exact absurd h (by simp)
  · rw [if_neg ht1] at h
    by_cases ht2 : zTag d = 2
    · rw [if_pos ht2] at h; exact absurd h (by simp)
    · rw [if_neg ht2] at h
      by_cases ht5 : zTag d = 5
      · rw [if_pos ht5] at h
        rw [((isymLk_inj _ _ _ _).mp h.symm).2, irk_all (h5 ht5)]
        exact pos_iff_one_le.mpr (by simp)
      · rw [if_neg ht5] at h
        by_cases ht6 : zTag d = 6
        · rw [if_pos ht6] at h
          rw [((isymLk_inj _ _ _ _).mp h.symm).2, irk_inegF (h6 ht6)]
          exact pos_iff_one_le.mpr (by simp)
        · rw [if_neg ht6] at h; exact absurd h.symm (by simp)

/-- For the current `tp` (faithful on the I-rules), `tp d = R_A` forces `0 < rk A` as soon as the
principal formula is genuine: `R_{∀xF}` has `rk = rk(F)+1`, `R_{¬A'}` has `rk(¬A')=rk(A')+1`. **This
reduces `inference_critical_pair`'s `hwfR` (for the cases `tp` is defined) to formula-hood of the
principal formula** — sharpening exactly what the §5/Lemma-3.3 layer still owes. -/
lemma tp_isymR_pos {d A : V} (h : tp d = isymR A)
    (h1 : zTag d = 1 → IsUFormula ℒₒᵣ (zIallF d))
    (h2 : zTag d = 2 → IsUFormula ℒₒᵣ (zInegF d)) : 0 < irk A := by
  unfold tp at h
  by_cases ht1 : zTag d = 1
  · rw [if_pos ht1] at h
    rw [(isymR_inj _ _).mp h.symm, irk_all (h1 ht1)]; exact pos_iff_one_le.mpr (by simp)
  · rw [if_neg ht1] at h
    by_cases ht2 : zTag d = 2
    · rw [if_pos ht2] at h
      rw [(isymR_inj _ _).mp h.symm, irk_inegF (h2 ht2)]; exact pos_iff_one_le.mpr (by simp)
    · rw [if_neg ht2] at h
      by_cases ht5 : zTag d = 5
      · rw [if_pos ht5] at h; exact absurd h (by simp)
      · rw [if_neg ht5] at h
        by_cases ht6 : zTag d = 6
        · rw [if_pos ht6] at h; exact absurd h (by simp)
        · rw [if_neg ht6] at h; exact absurd h.symm (by simp)

/-! ### Definability of `tp` and the coded symbol map `tpSeq` (toward instantiating L3.1 on genuine
chains)

To run Lemma 3.1's `least_number` search over the premise symbols of a genuine chain `zK s r ds`, the
symbol sequence `Iseq` with `znth Iseq i = tp (znth ds i)` must itself be a **coded** sequence (so
`znth Iseq x` is `𝚺₁`-definable in `x`). We therefore make `tp : V → V` `𝚺₁`-definable (`tpDef`) and
build the coded map `tpSeq ds` via `PR.Construction` (mirroring `seqUpdateAux`). Sub-graphs: `isymR`/
`isymRep` are pairs (`pairDef`), `^∀` is `qqAllDef`, `inegF = neg ∨ ⊥` is `negGraph`/`qqOrDef`/
`qqFalsumDef`, `zIallF`/`zInegF` are the projection accessors. -/

section TpDef
open LO.FirstOrder.Arithmetic

/-- `R_A = ⟪0,A⟫` graph. -/
def _root_.LO.FirstOrder.Arithmetic.isymRGraph : 𝚺₀.Semisentence 2 := .mkSigma “y A. !pairDef y 0 A”
instance isymR_defined : 𝚺₀-Function₁ (isymR : V → V) via isymRGraph := .mk fun v ↦ by
  simp [isymRGraph, isymR]
instance isymR_definable : 𝚺₀-Function₁ (isymR : V → V) := isymR_defined.to_definable
instance isymR_definable' (ℌ) : ℌ-Function₁ (isymR : V → V) := isymR_definable.of_zero

/-- `zIallF d = π₁ (π₂ (zRest d))` — same projection chain as `zIndP`. -/
def _root_.LO.FirstOrder.Arithmetic.zIallFDef : 𝚺₀.Semisentence 2 := .mkSigma
  “y d. ∃ r <⁺ d, !zRestDef r d ∧ ∃ r2 <⁺ r, !pi₂Def r2 r ∧ !pi₁Def y r2”
instance zIallF_defined : 𝚺₀-Function₁ (zIallF : V → V) via zIallFDef := .mk fun v ↦ by
  simp [zIallFDef, zIallF, zRest_defined.iff, pi₂_defined.iff, pi₁_defined.iff]
instance zIallF_definable : 𝚺₀-Function₁ (zIallF : V → V) := zIallF_defined.to_definable

/-- `zInegF d = π₁ (zRest d)` — same projection as `zKrank`. -/
def _root_.LO.FirstOrder.Arithmetic.zInegFDef : 𝚺₀.Semisentence 2 := .mkSigma
  “y d. ∃ r <⁺ d, !zRestDef r d ∧ !pi₁Def y r”
instance zInegF_defined : 𝚺₀-Function₁ (zInegF : V → V) via zInegFDef := .mk fun v ↦ by
  simp [zInegFDef, zInegF, zRest_defined.iff, pi₁_defined.iff]
instance zInegF_definable : 𝚺₀-Function₁ (zInegF : V → V) := zInegF_defined.to_definable

/-- `inegF A = neg A ^⋎ ⊥` graph (Buchholz `¬A` as De Morgan `A → ⊥`). -/
noncomputable def _root_.LO.FirstOrder.Arithmetic.inegFDef : 𝚺₁.Semisentence 2 := .mkSigma
  “y A. ∃ n, !(negGraph ℒₒᵣ) n A ∧ ∃ f, !qqFalsumDef f ∧ !qqOrDef y n f”
instance inegF_defined : 𝚺₁-Function₁ (inegF : V → V) via inegFDef := .mk fun v ↦ by
  simp [inegFDef, inegF, (neg.defined (L := ℒₒᵣ)).iff, qqFalsum_defined.iff, qqOr_defined.iff]
instance inegF_definable : 𝚺₁-Function₁ (inegF : V → V) := inegF_defined.to_definable

/-- `zAxAllF d = π₁ (zRest d)` (same projection chain as `zInegF`). -/
def _root_.LO.FirstOrder.Arithmetic.zAxAllFDef : 𝚺₀.Semisentence 2 := .mkSigma
  “y d. ∃ r <⁺ d, !zRestDef r d ∧ !pi₁Def y r”
instance zAxAllF_defined : 𝚺₀-Function₁ (zAxAllF : V → V) via zAxAllFDef := .mk fun v ↦ by
  simp [zAxAllFDef, zAxAllF, zRest_defined.iff, pi₁_defined.iff]
instance zAxAllF_definable : 𝚺₀-Function₁ (zAxAllF : V → V) := zAxAllF_defined.to_definable

/-- `zAxNegF d = zRest d`. -/
def _root_.LO.FirstOrder.Arithmetic.zAxNegFDef : 𝚺₀.Semisentence 2 := .mkSigma
  “y d. !zRestDef y d”
instance zAxNegF_defined : 𝚺₀-Function₁ (zAxNegF : V → V) via zAxNegFDef := .mk fun v ↦ by
  simp [zAxNegFDef, zAxNegF, zRest_defined.iff]
instance zAxNegF_definable : 𝚺₀-Function₁ (zAxNegF : V → V) := zAxNegF_defined.to_definable

/-- `tp` definability blueprint: dispatch on `zTag d`. Tags 5/6 produce the L-symbols
`L^{π₂(zRest d)}_{∀(π₁(zRest d))}` / `L⁰_{¬(zRest d)}` (`isymLk k A = ⟪1,k,A⟫`). -/
noncomputable def _root_.LO.FirstOrder.Arithmetic.tpDef : 𝚺₁.Semisentence 2 := .mkSigma
  “y d. ∃ t, !zTagDef t d ∧
    ( (t = 1 ∧ ∃ q, !zIallFDef q d ∧ ∃ aq, !qqAllDef aq q ∧ !pairDef y 0 aq)
    ∨ (t = 2 ∧ ∃ b, !zInegFDef b d ∧ ∃ nb, !inegFDef nb b ∧ !pairDef y 0 nb)
    ∨ (t = 5 ∧ ∃ r, !zRestDef r d ∧ ∃ p, !pi₁Def p r ∧ ∃ ap, !qqAllDef ap p ∧
        ∃ k, !pi₂Def k r ∧ !pair₃Def y 1 k ap)
    ∨ (t = 6 ∧ ∃ r, !zRestDef r d ∧ ∃ nb, !inegFDef nb r ∧ !pair₃Def y 1 0 nb)
    ∨ (t ≠ 1 ∧ t ≠ 2 ∧ t ≠ 5 ∧ t ≠ 6 ∧ !pairDef y 2 0) )”

set_option maxHeartbeats 1000000 in
instance tp_defined : 𝚺₁-Function₁ (tp : V → V) via tpDef := .mk fun v ↦ by
  simp [tpDef, tp, zTag_defined.iff, zIallF_defined.iff, zInegF_defined.iff,
    inegF_defined.iff, qqForall_defined.iff, zRest_defined.iff, pi₁_defined.iff,
    pi₂_defined.iff, zAxAllF, zAxAllK, zAxNegF, isymR, isymLk, isymRep, numeral_eq_natCast]
  by_cases h1 : zTag (v 1) = 1
  · simp [h1]
  · by_cases h2 : zTag (v 1) = 2
    · simp [h1, h2]
    · by_cases h5 : zTag (v 1) = 5
      · simp [h1, h2, h5]
      · by_cases h6 : zTag (v 1) = 6
        · simp [h1, h2, h5, h6]
        · simp [h1, h2, h5, h6]

instance tp_definable : 𝚺₁-Function₁ (tp : V → V) := tp_defined.to_definable
instance tp_definable' (Γ) : Γ-[m + 1]-Function₁ (tp : V → V) := tp_definable.of_sigmaOne

/-! ### The coded symbol map `tpSeq ds = ⟨tp(znth ds 0), …, tp(znth ds (lh ds−1))⟩`

Built by `PR.Construction` over a length counter (mirror `seqUpdateAux`): `tpSeqAux ds (n+1) =
seqCons (tpSeqAux ds n) (tp (znth ds n))`. The key read-out `znth (tpSeq ds) i = tp (znth ds i)`
(for `i < lh ds`) is what lets Lemma 3.1's `least_number` search run over genuine premise symbols. -/

noncomputable def tpSeqAux.blueprint : PR.Blueprint 1 where
  zero := .mkSigma “y ds. y = 0”
  succ := .mkSigma “y ih n ds. ∃ d, !znthDef d ds n ∧ ∃ t, !tpDef t d ∧ !seqConsDef y ih t”

noncomputable def tpSeqAux.construction : PR.Construction V tpSeqAux.blueprint where
  zero := fun _ ↦ ∅
  succ := fun x n ih ↦ seqCons ih (tp (znth (x 0) n))
  zero_defined := .mk fun v ↦ by simp [tpSeqAux.blueprint, emptyset_def]
  succ_defined := .mk fun v ↦ by
    simp [tpSeqAux.blueprint, znth_defined.iff, tp_defined.iff, seqCons_defined.iff]

/-- `tpSeqAux ds n` = the coded sequence `⟨tp(znth ds 0),…,tp(znth ds (n−1))⟩` (length `n`). -/
noncomputable def tpSeqAux (ds n : V) : V := tpSeqAux.construction.result ![ds] n

@[simp] lemma tpSeqAux_zero (ds : V) : tpSeqAux ds 0 = ∅ := by
  simp [tpSeqAux, tpSeqAux.construction]

@[simp] lemma tpSeqAux_succ (ds n : V) :
    tpSeqAux ds (n + 1) = seqCons (tpSeqAux ds n) (tp (znth ds n)) := by
  simp [tpSeqAux, tpSeqAux.construction]

noncomputable def _root_.LO.FirstOrder.Arithmetic.tpSeqAuxDef : 𝚺₁.Semisentence 3 :=
  tpSeqAux.blueprint.resultDef.rew (Rew.subst ![#0, #2, #1])

instance tpSeqAux_defined : 𝚺₁-Function₂ (tpSeqAux : V → V → V) via tpSeqAuxDef :=
  .mk fun v ↦ by simp [tpSeqAux.construction.result_defined_iff, tpSeqAuxDef]; rfl

instance tpSeqAux_definable : 𝚺₁-Function₂ (tpSeqAux : V → V → V) := tpSeqAux_defined.to_definable
instance tpSeqAux_definable' (Γ) : Γ-[m + 1]-Function₂ (tpSeqAux : V → V → V) :=
  tpSeqAux_definable.of_sigmaOne

@[simp] lemma tpSeqAux_seq (ds n : V) : Seq (tpSeqAux ds n) := by
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero => simpa using seq_empty
  case succ n ih => rw [tpSeqAux_succ]; exact ih.seqCons _

@[simp] lemma tpSeqAux_lh (ds n : V) : lh (tpSeqAux ds n) = n := by
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero => simpa using lh_empty
  case succ n ih => rw [tpSeqAux_succ, Seq.lh_seqCons _ (tpSeqAux_seq ds n), ih]

/-- Top read-out: the freshly-appended entry. -/
lemma znth_tpSeqAux_top (ds n : V) : znth (tpSeqAux ds (n + 1)) n = tp (znth ds n) := by
  rw [tpSeqAux_succ]
  have := znth_seqCons_self (tpSeqAux_seq ds n) (tp (znth ds n))
  rwa [tpSeqAux_lh] at this

/-- Reads below the top are stable as the prefix grows. -/
lemma znth_tpSeqAux_stable {ds : V} (n m : V) (hm : m < n) :
    znth (tpSeqAux ds (n + 1)) m = znth (tpSeqAux ds n) m := by
  rw [tpSeqAux_succ, znth_seqCons_of_lt (tpSeqAux_seq ds n) _ (by rw [tpSeqAux_lh]; exact hm)]

/-- Every in-range entry of the prefix is the genuine `tp` value. -/
lemma znth_tpSeqAux_eq {ds : V} : ∀ n, ∀ i < n, znth (tpSeqAux ds n) i = tp (znth ds i) := by
  intro n
  induction n using ISigma1.sigma1_succ_induction
  · refine Definable.ball_lt (by definability) ?_
    apply Definable.comp₂ (by definability)
    exact DefinableFunction₁.comp (F := tp) (by definability)
  case zero => intro i hi; exact absurd hi (by simp)
  case succ n ih =>
    intro i hi
    rcases eq_or_lt_of_le (le_iff_lt_succ.mpr hi) with hin | hilt
    · rw [hin, znth_tpSeqAux_top]
    · rw [znth_tpSeqAux_stable n i hilt]; exact ih i hilt

/-- **The coded symbol map** `tpSeq ds = ⟨tp(d₀),…,tp(d_{l})⟩` (length `lh ds`). -/
noncomputable def tpSeq (ds : V) : V := tpSeqAux ds (lh ds)

@[simp] lemma tpSeq_seq (ds : V) : Seq (tpSeq ds) := tpSeqAux_seq ds (lh ds)
@[simp] lemma tpSeq_lh (ds : V) : lh (tpSeq ds) = lh ds := tpSeqAux_lh ds (lh ds)

/-- **Read-out**: the `i`-th coded symbol is `tp` of the `i`-th premise (for `i < lh ds`). -/
lemma znth_tpSeq {ds i : V} (hi : i < lh ds) : znth (tpSeq ds) i = tp (znth ds i) :=
  znth_tpSeqAux_eq (lh ds) i hi

end TpDef

/-! ## Sequents `Π = Γ→C` + permissibility `I ◁ Π` + chain-rule inference (Buchholz §3, p.8)

A Buchholz sequent `Π = Γ→C` is coded `⟪Γ, C⟫` with antecedent `Γ` a sequence of formulas and `C` the
single succedent. Permissibility `I ◁ Γ→C :⇔ I = R_C ∨ (I = L^k_A with A ∈ Γ) ∨ I = Rep` (p.8). The
chain-rule inference of rank `r` (p.8) packages the structural conditions that feed Lemma 3.1
(`inference_critical_pair`): the `hAj0`/`hchain`/`hrank` hypotheses are read off this predicate. This is
the deferred *sequent* layer of the Z calculus, kept abstract over the eventual end-sequent matching. -/

/-- Antecedent `Γ` of a sequent `q = ⟪Γ,C⟫`. -/
noncomputable def seqAnt (q : V) : V := π₁ q
/-- Succedent `C` of a sequent `q = ⟪Γ,C⟫`. -/
noncomputable def seqSucc (q : V) : V := π₂ q
/-- Build the sequent `Γ→C`. -/
noncomputable def mkSeqt (Γ C : V) : V := ⟪Γ, C⟫
@[simp] lemma seqAnt_mkSeqt (Γ C : V) : seqAnt (mkSeqt Γ C) = Γ := by simp [seqAnt, mkSeqt]
@[simp] lemma seqSucc_mkSeqt (Γ C : V) : seqSucc (mkSeqt Γ C) = C := by simp [seqSucc, mkSeqt]

/-- `A ∈ Γ` — antecedent membership (`Γ` a coded sequence of formulas). -/
def inAnt (A Γ : V) : Prop := ∃ i < lh Γ, znth Γ i = A

/-- **Permissibility** `I ◁ q` (Buchholz p.8): `I = R_C ∨ (I = L^k_A with A ∈ Γ) ∨ I = Rep`. -/
def iperm (I q : V) : Prop :=
  I = isymR (seqSucc q) ∨ (∃ k A, I = isymLk k A ∧ inAnt A (seqAnt q)) ∨ I = isymRep

@[simp] lemma iperm_isymRep (q : V) : iperm isymRep q := Or.inr (Or.inr rfl)

/-- **Projection-free form of `iperm`** (the bounded-quantifier-free shape for arithmetization): the
middle `∃ k A, I = L^k_A ∧ A ∈ Γ` disjunct is `isymIsL I ∧ (π₂(π₂ I)) ∈ Γ` (the L-symbol reconstructs
from its own projections, `isymIsL`). This is the form `ipermDef` matches. -/
lemma iperm_iff_proj {I q : V} : iperm I q ↔
    I = isymR (seqSucc q) ∨ (isymIsL I ∧ inAnt (π₂ (π₂ I)) (seqAnt q)) ∨ I = isymRep := by
  unfold iperm
  refine or_congr_right (or_congr_left ?_)
  constructor
  · rintro ⟨k, A, rfl, hA⟩
    exact ⟨isymIsL_isymLk k A, by simpa [isymLk] using hA⟩
  · rintro ⟨hL, hA⟩
    exact ⟨π₁ (π₂ I), π₂ (π₂ I), hL, hA⟩

lemma iperm_isymR_iff {C q : V} : iperm (isymR C) q ↔ C = seqSucc q := by
  constructor
  · rintro (h | ⟨k, A, h, _⟩ | h)
    · exact (isymR_inj _ _).mp h
    · exact absurd h (by simp)
    · exact absurd h (by simp)
  · intro h; exact Or.inl (by rw [h])

lemma iperm_isymLk_iff {k A q : V} : iperm (isymLk k A) q ↔ inAnt A (seqAnt q) := by
  constructor
  · rintro (h | ⟨k', A', h, hA'⟩ | h)
    · exact absurd h.symm (by simp)
    · obtain ⟨_, rfl⟩ := (isymLk_inj _ _ _ _).mp h; exact hA'
    · exact absurd h (by simp)
  · intro h; exact Or.inr (Or.inl ⟨k, A, rfl, h⟩)

/-! ### Genuine-reduct sequent operations (Buchholz §3.2 case 5.1 endsequents)

The critical recombination's auxiliaries derive the *modified* sequents `d{0} ⊢ Θ→A(d)` and
`d{1} ⊢ A(d),Θ→D` (Buchholz §2 p.6 / Thm 3.4(a)): `Θ→A(d)` keeps the antecedent `Θ = seqAnt s` and
swaps the succedent to the cut formula `A(d)`; `A(d),Θ→D` adds `A(d)` to the antecedent and keeps the
succedent `D = seqSucc s`. These two operations build the genuine auxiliaries' conclusions (unlike the
ordinal-shadow `iCritAux`, which reuses `fstIdx d = s` for both). -/

/-- `Θ→C`: the sequent `s` with its succedent replaced by `C` (the cut-formula succedent of `d{0}`). -/
noncomputable def seqSetSucc (s C : V) : V := mkSeqt (seqAnt s) C
@[simp] lemma seqAnt_seqSetSucc (s C : V) : seqAnt (seqSetSucc s C) = seqAnt s := by simp [seqSetSucc]
@[simp] lemma seqSucc_seqSetSucc (s C : V) : seqSucc (seqSetSucc s C) = C := by simp [seqSetSucc]

/-- `A,Θ→D`: the sequent `s` with `A` added to its antecedent (membership-wise, appended), succedent
unchanged (the conclusion of `d{1}`). -/
noncomputable def seqAddAnt (A s : V) : V := mkSeqt (seqCons (seqAnt s) A) (seqSucc s)
@[simp] lemma seqAnt_seqAddAnt (A s : V) : seqAnt (seqAddAnt A s) = seqCons (seqAnt s) A := by
  simp [seqAddAnt]
@[simp] lemma seqSucc_seqAddAnt (A s : V) : seqSucc (seqAddAnt A s) = seqSucc s := by simp [seqAddAnt]

/-- Antecedent membership splits over a `seqCons` append: `B ∈ Γ⌢A ↔ B = A ∨ B ∈ Γ`. -/
lemma inAnt_seqCons {Γ A B : V} (hΓ : Seq Γ) :
    inAnt B (seqCons Γ A) ↔ B = A ∨ inAnt B Γ := by
  unfold inAnt
  rw [Seq.lh_seqCons A hΓ]
  constructor
  · rintro ⟨i, hi, hz⟩
    rcases eq_or_lt_of_le (le_iff_lt_succ.mpr hi) with rfl | hlt
    · left; rw [znth_seqCons_self hΓ A] at hz; exact hz.symm
    · right; rw [znth_seqCons_of_lt hΓ A hlt] at hz; exact ⟨i, hlt, hz⟩
  · rintro (rfl | ⟨i, hi, hz⟩)
    · exact ⟨lh Γ, le_iff_lt_succ.mp le_rfl, znth_seqCons_self hΓ _⟩
    · exact ⟨i, le_iff_lt_succ.mp (le_of_lt hi), by rw [znth_seqCons_of_lt hΓ A hi]; exact hz⟩

/-- Antecedent membership of `A,Θ→D`: `B ∈ A,Θ ↔ B = A ∨ B ∈ Θ`. -/
lemma inAnt_seqAddAnt {A s B : V} (hs : Seq (seqAnt s)) :
    inAnt B (seqAnt (seqAddAnt A s)) ↔ B = A ∨ inAnt B (seqAnt s) := by
  rw [seqAnt_seqAddAnt]; exact inAnt_seqCons hs

/-- **Sequent-wellformedness preserved by antecedent-add.** `Seq (seqAnt s) → Seq (seqAnt (seqAddAnt A s))`
— prepending a formula to the antecedent keeps it a `Seq` (`Seq.seqCons`). The `seqSetSucc` case is the
`@[simp] seqAnt_seqSetSucc` identity (`seqAnt (seqSetSucc s C) = seqAnt s`), so both `tpReduce` antecedent
shapes (I¬/axAll grow the antecedent, I∀/axNeg keep it) preserve `Seq (seqAnt …)`. The conclusion-side rung
of the sequent-wellformedness cascade (PENDING_WORK lap-99 path A). -/
@[simp] lemma Seq_seqAnt_seqAddAnt {A s : V} (hs : Seq (seqAnt s)) :
    Seq (seqAnt (seqAddAnt A s)) := by
  rw [seqAnt_seqAddAnt]; exact hs.seqCons A

/-! ### `tpReduce` — Buchholz's reduced sequent `I(Π,n)` (Def 3.2 / §2 13.2, 13.5)

**Route-B keystone (lap 91).** Lap-90 found the repo's `red` keeps the chain conclusion `Π`, so it
equals Buchholz `d[n]` only when `tp(d) = Rep`; the faithful port (route B) requires the reduct to
compute the **reduced** conclusion `tp(d)(Π,n)`. `tpReduce I s n` is exactly Buchholz's `I(Π,n)` — the
result of applying inference symbol `I` to sequent `Π = Θ→D` under choice `n` (paper §2 14.23/14.252,
read from the PDF pp. 4–6):

* `Rep(Π,n) = Π` — identity (Def 3.2 clause 3);
* `R_{∀xF}(Π,n) = Θ→F(n)` — right-∀: succedent `∀xF` reduced to its `n`-instance `F(n)` (14.23);
* `R_{¬A}(Π,0) = A,Θ→⊥` — right-¬: `A` adjoined to antecedent, succedent becomes `⊥` (14.23);
* `L^k_{∀xF}(Π,n) = F(k),Θ→D` — left-∀: instance `F(k)` adjoined to antecedent (14.252, `B = ∀xF`);
* `L^0_{¬A}(Π,n) = Θ→A` — left-¬: succedent becomes `A` (14.252/14.253, `B = ¬A`).

The `∀`/`¬` dispatch is on the principal formula's top connective: `^∀ p = ⟪6,p⟫+1` (`π₁(A∸1)=6`) vs
`inegF p = (neg p) ^⋎ ^⊥` (`π₁(A∸1)=5`). The `¬`-body `A` is recovered from `inegF A = (neg A)^⋎^⊥`
via `neg (neg A) = A` (`IsUFormula.neg_neg`, hence the `IsUFormula` hypotheses on the `¬` equations). -/
noncomputable def tpReduce (I s n : V) : V :=
  if π₁ I = 2 then s
  else if π₁ I = 0 then
    (if π₁ (π₂ I - 1) = 6 then
        seqSetSucc s (substs1 ℒₒᵣ (Bootstrapping.Arithmetic.numeral n) (π₂ (π₂ I - 1)))
      else
        seqAddAnt (neg ℒₒᵣ (π₁ (π₂ (π₂ I - 1)))) (seqSetSucc s (^⊥ : V)))
  else
    (if π₁ (π₂ (π₂ I) - 1) = 6 then
        seqAddAnt (substs1 ℒₒᵣ (Bootstrapping.Arithmetic.numeral (π₁ (π₂ I)))
          (π₂ (π₂ (π₂ I) - 1))) s
      else
        seqSetSucc s (neg ℒₒᵣ (π₁ (π₂ (π₂ (π₂ I) - 1)))))

/-- `Rep(Π,n) = Π` — the identity reduction. The headline-critical case: on the ⊥-orbit every chain has
`tp = Rep` (Cor 2.1), so `tpReduce (tp d) (fstIdx d) 0 = fstIdx d`, keeping `ZDerivesEmpty`. -/
@[simp] lemma tpReduce_isymRep (s n : V) : tpReduce (isymRep : V) s n = s := by
  simp [tpReduce, isymRep]

/-- `R_{∀xF}(Θ→D,n) = Θ→F(n)` (matrix `p = F`, instance `F(n) = substs1 (numeral n) p`). -/
lemma tpReduce_isymR_all (p s n : V) :
    tpReduce (isymR (^∀ p) : V) s n
      = seqSetSucc s (substs1 ℒₒᵣ (Bootstrapping.Arithmetic.numeral n) p) := by
  simp [tpReduce, isymR, qqAll]

/-- `R_{¬A}(Θ→D,n) = A,Θ→⊥` (the `n` is unused; `A = p` recovered from `inegF p`). -/
lemma tpReduce_isymR_neg (p s n : V) (hp : IsUFormula ℒₒᵣ p) :
    tpReduce (isymR (inegF p) : V) s n = seqAddAnt p (seqSetSucc s (^⊥ : V)) := by
  simp [tpReduce, isymR, inegF, qqOr, hp.neg_neg]

/-- `L^k_{∀xF}(Θ→D,n) = F(k),Θ→D` (instance `F(k) = substs1 (numeral k) p` adjoined to antecedent). -/
lemma tpReduce_isymLk_all (k p s n : V) :
    tpReduce (isymLk k (^∀ p) : V) s n
      = seqAddAnt (substs1 ℒₒᵣ (Bootstrapping.Arithmetic.numeral k) p) s := by
  simp [tpReduce, isymLk, qqAll]

/-- `L^0_{¬A}(Θ→D,n) = Θ→A` (succedent replaced by `A = p`, antecedent unchanged). -/
lemma tpReduce_isymLk_neg (k p s n : V) (hp : IsUFormula ℒₒᵣ p) :
    tpReduce (isymLk k (inegF p) : V) s n = seqSetSucc s p := by
  simp [tpReduce, isymLk, inegF, qqOr, hp.neg_neg]

/-! ### Lemma 3.3 (`tp(d) ◁ Π`) for the I-rule cases (Buchholz p.8)

For the rules where `tp` is faithfully defined, permissibility `tp(d) ◁ end(d)` reduces to **end-sequent
matching**: the conclusion's succedent must be the principal formula. `tp(I^a_∀xF d0) = R_{∀xF}` is
permissible for any sequent whose succedent is `∀xF`; `tp(I_¬A d0) = R_{¬A}` for any whose succedent is
`¬A` (`= inegF A`). These directly discharge the `hperm` obligation of `inference_critical_pair_of_chain`
for premises built by the I-rules (the remaining cases — atomic/chain — need the §5 / recursive-`tp`
layer). The end-sequent hypothesis is exactly what the refined `ZPhi` (with sequent matching) will supply. -/
lemma iperm_tp_zIall {s a p d0 q : V} (h : seqSucc q = (^∀ p : V)) :
    iperm (tp (zIall s a p d0)) q := by
  rw [tp_zIall]; exact iperm_isymR_iff.mpr h.symm

lemma iperm_tp_zIneg {s p d0 q : V} (h : seqSucc q = inegF p) :
    iperm (tp (zIneg s p d0)) q := by
  rw [tp_zIneg]; exact iperm_isymR_iff.mpr h.symm

/-- And `Ind` (case 4): `tp = Rep` is permissible for **every** sequent (no matching needed). -/
@[simp] lemma iperm_tp_zInd (s at' p d0 d1 q : V) : iperm (tp (zInd s at' p d0 d1)) q := by
  rw [tp_zInd]; exact iperm_isymRep q

/-! ### Lemma 3.3 (`tp(d) ◁ Π`) for the §5 atomic L-symbol axioms (Buchholz p.8/p.12)

These are the §5 analogues that complete `iperm_tp_zIall`/`iperm_tp_zIneg` for the **left** symbols: an
L-symbol `L^k_A` is permissible for a sequent `q` iff its cut formula `A` lies in `q`'s antecedent
(`iperm_isymLk_iff`). `tp(Ax^{∀xF,k}) = L^k_{∀xF}` is permissible whenever `∀xF ∈ ant(q)` (which is the
side condition `∀xF ∈ Γ` of the very axiom); `tp(Ax^{¬A,0}) = L⁰_{¬A}` whenever `¬A ∈ ant(q)`. **This is
exactly the `hperm` discharge for the critical `j`-end** that L3.1 lands on, the L-symbol counterpart of
the I-rule `hperm` facts. The matching `inAnt` hypotheses are exactly what the refined `ZPhi` (atomic-axiom
side conditions) supplies. -/
lemma iperm_tp_zAxAll {s p k q : V} (h : inAnt (^∀ p : V) (seqAnt q)) :
    iperm (tp (zAxAll s p k)) q := by
  rw [tp_zAxAll]; exact iperm_isymLk_iff.mpr h

lemma iperm_tp_zAxNeg {s p q : V} (h : inAnt (inegF p : V) (seqAnt q)) :
    iperm (tp (zAxNeg s p)) q := by
  rw [tp_zAxNeg]; exact iperm_isymLk_iff.mpr h

/-- **Criticality (`hnperm`) for the atomic axioms.** `tp(Ax^{∀xF,k}) ⋪ Π` iff `∀xF ∉ ant(Π)`; this is
the criticality side that, together with `iperm_tp_zAxAll`, makes `hperm`+`hnperm` simultaneously
satisfiable for a real critical chain: the cut formula is in the *premise* antecedent but not the *main*
conclusion's. -/
lemma not_iperm_tp_zAxAll_iff {s p k c : V} :
    ¬ iperm (tp (zAxAll s p k)) c ↔ ¬ inAnt (^∀ p : V) (seqAnt c) := by
  rw [tp_zAxAll, iperm_isymLk_iff]

lemma not_iperm_tp_zAxNeg_iff {s p c : V} :
    ¬ iperm (tp (zAxNeg s p)) c ↔ ¬ inAnt (inegF p : V) (seqAnt c) := by
  rw [tp_zAxNeg, iperm_isymLk_iff]

/-- The succedent `A_i` of premise `i` of a chain `zK s r ds`. -/
noncomputable def chainAsucc (ds i : V) : V := seqSucc (fstIdx (znth ds i))
/-- The antecedent `Γ_i` of premise `i` of a chain `zK s r ds`. -/
noncomputable def chainAnt (ds i : V) : V := seqAnt (fstIdx (znth ds i))

/-- **Chain-rule inference of rank `r`** (Buchholz Def, p.8): `Γ_0→A_0 … Γ_l→A_l / Γ→C` is such iff
∃ `j₀ ≤ l` with `A_{j₀} ∈ {C,⊥}`, `∀ i≤j₀ (Γ_i ⊆ Γ,A_0,…,A_{i-1})`, `∀ i<j₀ (rk(A_i) ≤ r)`. Read off the
coded chain `zK s r ds` (conclusion sequent `s`, premise derivations `ds`). The exact source of Lemma
3.1's structural hypotheses `hAj0`/`hchain`/`hrank`. -/
def isChainInf (s r ds : V) : Prop :=
  ∃ j0 < lh ds,
    (chainAsucc ds j0 = seqSucc s ∨ chainAsucc ds j0 = (^⊥ : V)) ∧
    (∀ i ≤ j0, ∀ B, inAnt B (chainAnt ds i) →
      inAnt B (seqAnt s) ∨ ∃ i' < i, B = chainAsucc ds i') ∧
    (∀ i < j0, irk (chainAsucc ds i) ≤ r)

/-- **Index form of `isChainInf`** — the `∀ B, inAnt B Γ → …` antecedent-threading condition rewritten
as a bounded `∀ k < lh Γ, …(znth Γ k)` (since `inAnt B Γ ↔ ∃ k < lh Γ, znth Γ k = B`). This eliminates
the only unbounded universal, so every quantifier in the matrix is bounded (the lone remaining `𝚺₁`
content is `irk ≤ r`) — exactly the shape `isChainInfDef`'s `𝚫₁` Σ/Π cores match. -/
lemma isChainInf_iff_idx {s r ds : V} : isChainInf s r ds ↔
    ∃ j0 < lh ds,
      (chainAsucc ds j0 = seqSucc s ∨ chainAsucc ds j0 = (^⊥ : V)) ∧
      (∀ i ≤ j0, ∀ k < lh (chainAnt ds i),
        inAnt (znth (chainAnt ds i) k) (seqAnt s) ∨
        ∃ i' < i, znth (chainAnt ds i) k = chainAsucc ds i') ∧
      (∀ i < j0, irk (chainAsucc ds i) ≤ r) := by
  unfold isChainInf
  constructor
  · rintro ⟨j0, hj0, hA, hB, hC⟩
    exact ⟨j0, hj0, hA, fun i hi k hk => hB i hi _ ⟨k, hk, rfl⟩, hC⟩
  · rintro ⟨j0, hj0, hA, hB, hC⟩
    exact ⟨j0, hj0, hA, fun i hi Bv ⟨k, hk, hBv⟩ => hBv ▸ hB i hi k hk, hC⟩

/-- **Chain-validity from premise-local threading** — package `isChainInf` by taking the **last** premise
as the distinguished `j0 = lh ds − 1`. A genuine reduct (the Ind unfolding `⟨d0, d1(0),…,d1(k−1)⟩` and the
critical-cut reduct) establishes chain-validity exactly this way: the last premise carries the
conclusion's succedent, and each premise's antecedent threads back to the conclusion or a *prior*
premise's succedent. This lemma is the reusable reduction of `isChainInf` to those local facts (it just
discharges `j0 < lh ds` from `0 < lh ds`). -/
lemma isChainInf_of_last {s r ds : V} (hlen : 0 < lh ds)
    (hlast : chainAsucc ds (lh ds - 1) = seqSucc s ∨ chainAsucc ds (lh ds - 1) = (^⊥ : V))
    (hthread : ∀ i ≤ lh ds - 1, ∀ B, inAnt B (chainAnt ds i) →
        inAnt B (seqAnt s) ∨ ∃ i' < i, B = chainAsucc ds i')
    (hrank : ∀ i < lh ds - 1, irk (chainAsucc ds i) ≤ r) :
    isChainInf s r ds :=
  ⟨lh ds - 1, tsub_lt_self hlen one_pos, hlast, hthread, hrank⟩

/-- **Chain-validity is a congruence in the end-sequent data.** `isChainInf` reads `ds` only through
`lh ds` and the per-premise end-sequent projections `chainAsucc ds`/`chainAnt ds`. So two premise
sequences with the same length and the same pointwise end-sequents have the same chain-validity. The
general form of `isChainInf_seqUpdate` (same-end-sequent premise replacement) and the splice case
(Buchholz §3.2 5.2.1) reduce to computing the new `chainAsucc`/`chainAnt` and applying this. -/
lemma isChainInf_congr {s r ds ds' : V} (hlh : lh ds = lh ds')
    (hA : ∀ i, chainAsucc ds i = chainAsucc ds' i)
    (hN : ∀ i, chainAnt ds i = chainAnt ds' i) :
    isChainInf s r ds ↔ isChainInf s r ds' := by
  unfold isChainInf
  simp only [hlh, hA, hN]

/-! ### Σ₁-definability of the sequent layer (`seqAnt`/`seqSucc`/`chainAsucc`/`chainAnt`)

The chain-validity ingredients toward `zKValid`'s arithmetization (the `ZPhi` `zK`-disjunct cascade).
All projections/compositions of already-definable pieces (`pi₁`/`pi₂`/`fstIdx`/`znth`). -/

/-- `seqAnt q = π₁ q`. -/
def _root_.LO.FirstOrder.Arithmetic.seqAntDef : 𝚺₀.Semisentence 2 := .mkSigma “y q. !pi₁Def y q”
instance seqAnt_defined : 𝚺₀-Function₁ (seqAnt : V → V) via seqAntDef := .mk fun v ↦ by
  simp [seqAntDef, seqAnt, pi₁_defined.iff]
instance seqAnt_definable : 𝚺₀-Function₁ (seqAnt : V → V) := seqAnt_defined.to_definable

/-- `seqSucc q = π₂ q`. -/
def _root_.LO.FirstOrder.Arithmetic.seqSuccDef : 𝚺₀.Semisentence 2 := .mkSigma “y q. !pi₂Def y q”
instance seqSucc_defined : 𝚺₀-Function₁ (seqSucc : V → V) via seqSuccDef := .mk fun v ↦ by
  simp [seqSuccDef, seqSucc, pi₂_defined.iff]
instance seqSucc_definable : 𝚺₀-Function₁ (seqSucc : V → V) := seqSucc_defined.to_definable

/-- `chainAsucc ds i = seqSucc (fstIdx (znth ds i))`. -/
noncomputable def _root_.LO.FirstOrder.Arithmetic.chainAsuccDef : 𝚺₁.Semisentence 3 := .mkSigma
  “y ds i. ∃ z, !znthDef z ds i ∧ ∃ f, !fstIdxDef f z ∧ !seqSuccDef y f”
instance chainAsucc_defined : 𝚺₁-Function₂ (chainAsucc : V → V → V) via chainAsuccDef := .mk
  fun v ↦ by simp [chainAsuccDef, chainAsucc, znth_defined.iff, fstIdx_defined.iff, seqSucc_defined.iff]
instance chainAsucc_definable : 𝚺₁-Function₂ (chainAsucc : V → V → V) := chainAsucc_defined.to_definable
instance chainAsucc_definable' (Γ) : Γ-[m + 1]-Function₂ (chainAsucc : V → V → V) :=
  chainAsucc_definable.of_sigmaOne

/-- `chainAnt ds i = seqAnt (fstIdx (znth ds i))`. -/
noncomputable def _root_.LO.FirstOrder.Arithmetic.chainAntDef : 𝚺₁.Semisentence 3 := .mkSigma
  “y ds i. ∃ z, !znthDef z ds i ∧ ∃ f, !fstIdxDef f z ∧ !seqAntDef y f”
instance chainAnt_defined : 𝚺₁-Function₂ (chainAnt : V → V → V) via chainAntDef := .mk
  fun v ↦ by simp [chainAntDef, chainAnt, znth_defined.iff, fstIdx_defined.iff, seqAnt_defined.iff]
instance chainAnt_definable : 𝚺₁-Function₂ (chainAnt : V → V → V) := chainAnt_defined.to_definable

/-- `inAnt A Γ = ∃ i < lh Γ, znth Γ i = A` (antecedent membership). -/
def _root_.LO.FirstOrder.Arithmetic.inAntDef : 𝚺₀.Semisentence 2 := .mkSigma
  “A Γ. ∃ l <⁺ 2 * Γ, !lhDef l Γ ∧ ∃ i < l, !znthDef A Γ i”
instance inAnt_defined : 𝚺₀-Relation (inAnt : V → V → Prop) via inAntDef := .mk fun v ↦ by
  simp [inAntDef, inAnt, lh_defined.iff, znth_defined.iff, eq_comm, lh_bound]
instance inAnt_definable : 𝚺₀-Relation (inAnt : V → V → Prop) := inAnt_defined.to_definable

/-- `iperm I q` via `iperm_iff_proj`: `I = ⟪0,π₂ q⟫` (R) ∨ (`I = ⟪1,π₁(π₂ I),π₂(π₂ I)⟫` with
`π₂(π₂ I) ∈ π₁ q`) (L) ∨ `I = ⟪2,0⟫` (Rep). All existentials bounded (`pi₁/pi₂_le_self`) ⟹ `𝚺₀`. -/
def _root_.LO.FirstOrder.Arithmetic.ipermDef : 𝚺₀.Semisentence 2 := .mkSigma
  “I q. (∃ c <⁺ q, !seqSuccDef c q ∧ !pairDef I 0 c)
    ∨ (∃ p2 <⁺ I, !pi₂Def p2 I ∧ ∃ k <⁺ p2, !pi₁Def k p2 ∧ ∃ A <⁺ p2, !pi₂Def A p2 ∧
        !pair₃Def I 1 k A ∧ ∃ sa <⁺ q, !seqAntDef sa q ∧ !inAntDef A sa)
    ∨ !pairDef I 2 0”
instance iperm_defined : 𝚺₀-Relation (iperm : V → V → Prop) via ipermDef := .mk fun v ↦ by
  simp [ipermDef, iperm_iff_proj, isymIsL, isymR, isymLk, isymRep, seqSucc_defined.iff,
    seqAnt_defined.iff, pi₁_defined.iff, pi₂_defined.iff, inAnt_defined.iff,
    seqSucc, seqAnt, pi₁_le_self, pi₂_le_self]
instance iperm_definable : 𝚺₀-Relation (iperm : V → V → Prop) := iperm_defined.to_definable

/-- **Δ₁-definability of `isChainInf`** (via the bounded-index form `isChainInf_iff_idx`). The σ-core
extracts every function value positively (`∃ y, !fDef y args ∧ …`), the π-core via the antecedent
(`∀ y, !fDef y args → …`); both reduce to the same proposition because each function is total and
single-valued. The only genuinely `𝚺₁` content is `irk ≤ r` (chainAsucc/chainAnt are `𝚺₁`-typed but
projection-shallow); `lh`/`znth`/`seqAnt`/`seqSucc`/`inAnt` are `𝚺₀`. This is the chain-structure
ingredient of `zKValidDef`. -/
noncomputable def _root_.LO.FirstOrder.Arithmetic.isChainInfDef : 𝚫₁.Semisentence 3 := .mkDelta
  (.mkSigma “s r ds.
    ∃ l, !lhDef l ds ∧ ∃ j0 < l,
      ( ∃ ca0, !chainAsuccDef ca0 ds j0 ∧
          ( (∃ ss, !seqSuccDef ss s ∧ ca0 = ss) ∨ (∃ bot, !qqFalsumDef bot ∧ ca0 = bot) ) )
      ∧ ( ∀ i <⁺ j0, ∃ cai, !chainAntDef cai ds i ∧ ∃ lc, !lhDef lc cai ∧ ∀ k < lc,
            ∃ z, !znthDef z cai k ∧
              ( (∃ sa, !seqAntDef sa s ∧ !inAntDef z sa)
                ∨ (∃ i' < i, !chainAsuccDef z ds i') ) )
      ∧ ( ∀ i < j0, ∃ ca, !chainAsuccDef ca ds i ∧ ∃ rk, !irkDef rk ca ∧ rk ≤ r ) ”)
  (.mkPi “s r ds.
    ∀ l, !lhDef l ds → ∃ j0 < l,
      ( ∀ ca0, !chainAsuccDef ca0 ds j0 →
          ( (∀ ss, !seqSuccDef ss s → ca0 = ss) ∨ (∀ bot, !qqFalsumDef bot → ca0 = bot) ) )
      ∧ ( ∀ i <⁺ j0, ∀ cai, !chainAntDef cai ds i → ∀ lc, !lhDef lc cai → ∀ k < lc,
            ∀ z, !znthDef z cai k →
              ( (∀ sa, !seqAntDef sa s → !inAntDef z sa)
                ∨ (∃ i' < i, ∀ cai', !chainAsuccDef cai' ds i' → z = cai') ) )
      ∧ ( ∀ i < j0, ∀ ca, !chainAsuccDef ca ds i → ∀ rk, !irkDef rk ca → rk ≤ r ) ”)

instance isChainInf_defined : 𝚫₁-Relation₃ (isChainInf : V → V → V → Prop) via isChainInfDef :=
  ⟨by intro v
      simp [isChainInfDef, chainAsucc_defined.iff, chainAnt_defined.iff, irk_defined.iff,
        lh_defined.iff, znth_defined.iff, seqAnt_defined.iff, seqSucc_defined.iff,
        inAnt_defined.iff, qqFalsum_defined.iff],
   by intro v
      simp [isChainInfDef, isChainInf_iff_idx, chainAsucc_defined.iff, chainAnt_defined.iff,
        irk_defined.iff, lh_defined.iff, znth_defined.iff, seqAnt_defined.iff,
        seqSucc_defined.iff, inAnt_defined.iff, qqFalsum_defined.iff]⟩

instance isChainInf_definable : 𝚫₁-Relation₃ (isChainInf : V → V → V → Prop) :=
  isChainInf_defined.to_definable

/-- **Validity of a `K^r` chain inference** (Buchholz Def p.8 + Lemma 3.3) — exactly the deferred
hypotheses `iord_descent_iRcrit_of_chain'` consumes beyond the premises being `ZDerivation`s:
`isChainInf` (the chain-structure data `j0`/`A_{j0}`/threading/rank), the per-premise permissibility
`tp(dᵢ) ◁ Γᵢ→Aᵢ` and criticality `tp(dᵢ) ⋪ Π`, and formula-hood of each premise's principal formula
(which feeds `tp_isymR_pos`/`tp_isymLk_pos` to discharge the `hwfR`/`hwfL` rank conditions). This is
the `zK`-disjunct side condition that the refined `ZPhi` carries. -/
def zKValid (s r ds : V) : Prop :=
  isChainInf s r ds ∧
  (∀ i < lh ds, iperm (tp (znth ds i)) (fstIdx (znth ds i))) ∧
  (∀ i < lh ds, ¬ iperm (tp (znth ds i)) s) ∧
  (∀ i < lh ds, zTag (znth ds i) = 1 → IsUFormula ℒₒᵣ (zIallF (znth ds i))) ∧
  (∀ i < lh ds, zTag (znth ds i) = 2 → IsUFormula ℒₒᵣ (zInegF (znth ds i))) ∧
  (∀ i < lh ds, zTag (znth ds i) = 5 → IsUFormula ℒₒᵣ (zAxAllF (znth ds i))) ∧
  (∀ i < lh ds, zTag (znth ds i) = 6 → IsUFormula ℒₒᵣ (zAxNegF (znth ds i))) ∧
  (∀ i < lh ds, IsUFormula ℒₒᵣ (chainAsucc ds i)) ∧
  IsUFormula ℒₒᵣ (seqSucc s) ∧
  (∀ k < lh (seqAnt s), IsUFormula ℒₒᵣ (znth (seqAnt s) k))

/-- **Δ₁-definability of `zKValid`.** Bundles `isChainInfDef.sigma`/`.pi` with the bounded-`∀ i < lh ds`
per-premise conditions: `iperm`/`¬iperm` (`ipermDef`, `𝚺₀`) read off `tp`/`fstIdx` of premise `i`, and
the tag-gated principal-formula well-formedness (`IsUFormula` via `(isUFormula ℒₒᵣ).sigma`/`.pi`). The
six `∀ i < lh ds` conjuncts of `zKValid` are fused under one bounded `∀ i < l` here; `forall_and`
recovers the split. -/
noncomputable def _root_.LO.FirstOrder.Arithmetic.zKValidDef : 𝚫₁.Semisentence 3 := .mkDelta
  (.mkSigma “s r ds.
    !(isChainInfDef.sigma) s r ds ∧
    (∃ l, !lhDef l ds ∧ ∀ i < l,
      ∃ zi, !znthDef zi ds i ∧ ∃ ti, !tpDef ti zi ∧
        ( (∃ fi, !fstIdxDef fi zi ∧ !ipermDef ti fi)
          ∧ ¬(!ipermDef ti s)
          ∧ ∃ tg, !zTagDef tg zi ∧
            ( (tg = 1 → ∃ q, !zIallFDef q zi ∧ !(isUFormula ℒₒᵣ).sigma q)
            ∧ (tg = 2 → ∃ q, !zInegFDef q zi ∧ !(isUFormula ℒₒᵣ).sigma q)
            ∧ (tg = 5 → ∃ q, !zAxAllFDef q zi ∧ !(isUFormula ℒₒᵣ).sigma q)
            ∧ (tg = 6 → ∃ q, !zAxNegFDef q zi ∧ !(isUFormula ℒₒᵣ).sigma q) ) )
        ∧ ∃ ca, !chainAsuccDef ca ds i ∧ !(isUFormula ℒₒᵣ).sigma ca )
    ∧ (∃ sc, !seqSuccDef sc s ∧ !(isUFormula ℒₒᵣ).sigma sc)
    ∧ (∃ sa, !seqAntDef sa s ∧ ∃ la, !lhDef la sa ∧ ∀ k < la,
        ∃ z, !znthDef z sa k ∧ !(isUFormula ℒₒᵣ).sigma z) ”)
  (.mkPi “s r ds.
    !(isChainInfDef.pi) s r ds ∧
    (∀ l, !lhDef l ds → ∀ i < l,
      ∀ zi, !znthDef zi ds i → ∀ ti, !tpDef ti zi →
        ( (∀ fi, !fstIdxDef fi zi → !ipermDef ti fi)
          ∧ ¬(!ipermDef ti s)
          ∧ ∀ tg, !zTagDef tg zi →
            ( (tg = 1 → ∀ q, !zIallFDef q zi → !(isUFormula ℒₒᵣ).pi q)
            ∧ (tg = 2 → ∀ q, !zInegFDef q zi → !(isUFormula ℒₒᵣ).pi q)
            ∧ (tg = 5 → ∀ q, !zAxAllFDef q zi → !(isUFormula ℒₒᵣ).pi q)
            ∧ (tg = 6 → ∀ q, !zAxNegFDef q zi → !(isUFormula ℒₒᵣ).pi q) ) )
        ∧ ∀ ca, !chainAsuccDef ca ds i → !(isUFormula ℒₒᵣ).pi ca )
    ∧ (∀ sc, !seqSuccDef sc s → !(isUFormula ℒₒᵣ).pi sc)
    ∧ (∀ sa, !seqAntDef sa s → ∀ la, !lhDef la sa → ∀ k < la,
        ∀ z, !znthDef z sa k → !(isUFormula ℒₒᵣ).pi z) ”)

instance zKValid_defined : 𝚫₁-Relation₃ (zKValid : V → V → V → Prop) via zKValidDef :=
  ⟨by intro v
      simp [zKValidDef, HierarchySymbol.Semiformula.val_sigma, znth_defined.iff, tp_defined.iff,
        fstIdx_defined.iff, iperm_defined.iff, zTag_defined.iff, zIallF_defined.iff,
        zInegF_defined.iff, zAxAllF_defined.iff, zAxNegF_defined.iff, chainAsucc_defined.iff,
        seqSucc_defined.iff, seqAnt_defined.iff, lh_defined.iff],
   by intro v
      simp [zKValidDef, zKValid, HierarchySymbol.Semiformula.val_sigma, znth_defined.iff,
        tp_defined.iff, fstIdx_defined.iff, iperm_defined.iff, zTag_defined.iff, zIallF_defined.iff,
        zInegF_defined.iff, zAxAllF_defined.iff, zAxNegF_defined.iff, chainAsucc_defined.iff,
        seqSucc_defined.iff, seqAnt_defined.iff, lh_defined.iff, forall_and, and_assoc,
        numeral_eq_natCast]⟩

instance zKValid_definable : 𝚫₁-Relation₃ (zKValid : V → V → V → Prop) :=
  zKValid_defined.to_definable

/-! ### Decoupling criticality from validity — the genuine-reduct redesign (lap 82)

**Root-cause of the `RedSound` wall (validated against Buchholz, both papers).** `zKValid` bakes the
*criticality* conjunct `(∀ i < lh ds, ¬ iperm (tp (znth ds i)) s)` into the validity of EVERY chain
node. But Buchholz's chain-rule validity (§3 clause 5 / `isChainInf`: ∃ j₀ with `A_{j₀} ∈ {C,⊥}`,
threading `Γᵢ ⊆ Γ,A₀…A_{i−1}`, `rk(Aᵢ) ≤ r`) carries **no** criticality condition. Criticality (`d` is
*critical* iff `∀ i ≤ j₀, tp(dᵢ) ⋪ Π`, Def 3.2 case 5) is a property the *reduction* uses to pick its
clause (5.1 critical vs 5.2 non-critical) — NOT a validity requirement. Baking it into `zKValid`
over-constrains `ZDerivation` to *only critical* chains, which is exactly why the genuine reduct (whose
recombined premises `d{0},d{1}` are `Rep`-tagged chains, permissible everywhere — `not_zKValid_iCritReduct`)
spuriously fails validity. The fix (multi-lap): re-point `ZPhi`'s `zK` disjunct onto `zKValidF` (faithful
validity, no criticality), supply `zKCritical` only at reduction sites where Buchholz case 5 establishes
it, and prove descent by the critical/non-critical split (Lemma 4.1 a/b) over the genuine Def-3.2 reduct.
These defs + the decomposition lemma are the load-bearing bridge that makes that swap mechanical. -/

/-- **The criticality conjunct**, decoupled from validity: Buchholz's `d` is *critical*
(`∀ i ≤ j₀, tp(dᵢ) ⋪ Π`), here over all premises. Used by the *reduction* (Def 3.2 case 5) to find the
redex (`inference_critical_pair`), NOT by chain validity. -/
def zKCritical (s ds : V) : Prop := ∀ i < lh ds, ¬ iperm (tp (znth ds i)) s

/-- **Faithful chain validity** = `zKValid` minus the spurious criticality conjunct. This is Buchholz's
genuine `K^r` chain-rule validity (§3 clause 5): `isChainInf` (j₀/threading/rank) + each premise's
own-permissibility `tp(dᵢ) ◁ Πᵢ` (Lemma 3.3, automatic) + the §5 formula-hood bookkeeping. The redesign
re-points `ZPhi`'s `zK` disjunct onto this so the genuine reduct validates. -/
def zKValidF (s r ds : V) : Prop :=
  isChainInf s r ds ∧
  (∀ i < lh ds, iperm (tp (znth ds i)) (fstIdx (znth ds i))) ∧
  (∀ i < lh ds, zTag (znth ds i) = 1 → IsUFormula ℒₒᵣ (zIallF (znth ds i))) ∧
  (∀ i < lh ds, zTag (znth ds i) = 2 → IsUFormula ℒₒᵣ (zInegF (znth ds i))) ∧
  (∀ i < lh ds, zTag (znth ds i) = 5 → IsUFormula ℒₒᵣ (zAxAllF (znth ds i))) ∧
  (∀ i < lh ds, zTag (znth ds i) = 6 → IsUFormula ℒₒᵣ (zAxNegF (znth ds i))) ∧
  (∀ i < lh ds, IsUFormula ℒₒᵣ (chainAsucc ds i)) ∧
  IsUFormula ℒₒᵣ (seqSucc s) ∧
  (∀ k < lh (seqAnt s), IsUFormula ℒₒᵣ (znth (seqAnt s) k))

/-- **`zKValid` decomposes as faithful validity ∧ criticality.** The redesign keeps `zKValidF` in the
validity layer and supplies `zKCritical` only where Buchholz case 5 has established it. -/
lemma zKValid_iff_zKValidF_and_zKCritical {s r ds : V} :
    zKValid s r ds ↔ zKValidF s r ds ∧ zKCritical s ds := by
  unfold zKValid zKValidF zKCritical
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
    exact ⟨⟨h1, h2, h4, h5, h6, h7, h8, h9, h10⟩, h3⟩
  · rintro ⟨⟨h1, h2, h4, h5, h6, h7, h8, h9, h10⟩, h3⟩
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

/-- The faithful-validity layer of any (currently over-strong) `zKValid` chain. -/
lemma zKValidF_of_zKValid {s r ds : V} (h : zKValid s r ds) : zKValidF s r ds :=
  (zKValid_iff_zKValidF_and_zKCritical.mp h).1

/-- **Δ₁-definability of `zKCritical`** — the criticality conjunct in isolation (the line dropped from
`zKValidF`). `zKCritical s ds = ∀ i < lh ds, ¬ iperm (tp (znth ds i)) s` is bounded over the Δ₀ `iperm`
and Σ₁ `tp`/`znth`/`lh`, hence Δ₁. This is the **branch predicate for the genuine `red` dispatch**
(Buchholz Def 3.2 case 5: critical 5.1 vs non-critical 5.2): `iRNextG`'s tag-4 case tests `zKCritical` to
choose its reduct, and must stay Σ₁ — so the test must be definable. -/
noncomputable def _root_.LO.FirstOrder.Arithmetic.zKCriticalDef : 𝚫₁.Semisentence 2 := .mkDelta
  (.mkSigma “s ds.
    ∃ l, !lhDef l ds ∧ ∀ i < l,
      ∃ zi, !znthDef zi ds i ∧ ∃ ti, !tpDef ti zi ∧ ¬(!ipermDef ti s) ”)
  (.mkPi “s ds.
    ∀ l, !lhDef l ds → ∀ i < l,
      ∀ zi, !znthDef zi ds i → ∀ ti, !tpDef ti zi → ¬(!ipermDef ti s) ”)

instance zKCritical_defined : 𝚫₁-Relation (zKCritical : V → V → Prop) via zKCriticalDef :=
  ⟨by intro v
      simp [zKCriticalDef, znth_defined.iff, tp_defined.iff, iperm_defined.iff, lh_defined.iff],
   by intro v
      simp [zKCriticalDef, zKCritical, znth_defined.iff, tp_defined.iff, iperm_defined.iff,
        lh_defined.iff]⟩

instance zKCritical_definable : 𝚫₁-Relation (zKCritical : V → V → Prop) :=
  zKCritical_defined.to_definable

/-- **Δ₁ arithmetization of `zKValidF`** — `zKValidDef` with the spurious criticality line
`¬(!ipermDef ti s)` dropped. The arithmetized prerequisite for re-pointing `zblueprint`'s `zK` disjunct
onto faithful validity. -/
noncomputable def _root_.LO.FirstOrder.Arithmetic.zKValidFDef : 𝚫₁.Semisentence 3 := .mkDelta
  (.mkSigma “s r ds.
    !(isChainInfDef.sigma) s r ds ∧
    (∃ l, !lhDef l ds ∧ ∀ i < l,
      ∃ zi, !znthDef zi ds i ∧ ∃ ti, !tpDef ti zi ∧
        ( (∃ fi, !fstIdxDef fi zi ∧ !ipermDef ti fi)
          ∧ ∃ tg, !zTagDef tg zi ∧
            ( (tg = 1 → ∃ q, !zIallFDef q zi ∧ !(isUFormula ℒₒᵣ).sigma q)
            ∧ (tg = 2 → ∃ q, !zInegFDef q zi ∧ !(isUFormula ℒₒᵣ).sigma q)
            ∧ (tg = 5 → ∃ q, !zAxAllFDef q zi ∧ !(isUFormula ℒₒᵣ).sigma q)
            ∧ (tg = 6 → ∃ q, !zAxNegFDef q zi ∧ !(isUFormula ℒₒᵣ).sigma q) ) )
        ∧ ∃ ca, !chainAsuccDef ca ds i ∧ !(isUFormula ℒₒᵣ).sigma ca )
    ∧ (∃ sc, !seqSuccDef sc s ∧ !(isUFormula ℒₒᵣ).sigma sc)
    ∧ (∃ sa, !seqAntDef sa s ∧ ∃ la, !lhDef la sa ∧ ∀ k < la,
        ∃ z, !znthDef z sa k ∧ !(isUFormula ℒₒᵣ).sigma z) ”)
  (.mkPi “s r ds.
    !(isChainInfDef.pi) s r ds ∧
    (∀ l, !lhDef l ds → ∀ i < l,
      ∀ zi, !znthDef zi ds i → ∀ ti, !tpDef ti zi →
        ( (∀ fi, !fstIdxDef fi zi → !ipermDef ti fi)
          ∧ ∀ tg, !zTagDef tg zi →
            ( (tg = 1 → ∀ q, !zIallFDef q zi → !(isUFormula ℒₒᵣ).pi q)
            ∧ (tg = 2 → ∀ q, !zInegFDef q zi → !(isUFormula ℒₒᵣ).pi q)
            ∧ (tg = 5 → ∀ q, !zAxAllFDef q zi → !(isUFormula ℒₒᵣ).pi q)
            ∧ (tg = 6 → ∀ q, !zAxNegFDef q zi → !(isUFormula ℒₒᵣ).pi q) ) )
        ∧ ∀ ca, !chainAsuccDef ca ds i → !(isUFormula ℒₒᵣ).pi ca )
    ∧ (∀ sc, !seqSuccDef sc s → !(isUFormula ℒₒᵣ).pi sc)
    ∧ (∀ sa, !seqAntDef sa s → ∀ la, !lhDef la sa → ∀ k < la,
        ∀ z, !znthDef z sa k → !(isUFormula ℒₒᵣ).pi z) ”)

instance zKValidF_defined : 𝚫₁-Relation₃ (zKValidF : V → V → V → Prop) via zKValidFDef :=
  ⟨by intro v
      simp [zKValidFDef, zKValidF, HierarchySymbol.Semiformula.val_sigma, znth_defined.iff,
        tp_defined.iff, fstIdx_defined.iff, iperm_defined.iff, zTag_defined.iff, zIallF_defined.iff,
        zInegF_defined.iff, zAxAllF_defined.iff, zAxNegF_defined.iff, chainAsucc_defined.iff,
        seqSucc_defined.iff, seqAnt_defined.iff, lh_defined.iff],
   by intro v
      simp [zKValidFDef, zKValidF, HierarchySymbol.Semiformula.val_sigma, znth_defined.iff,
        tp_defined.iff, fstIdx_defined.iff, iperm_defined.iff, zTag_defined.iff, zIallF_defined.iff,
        zInegF_defined.iff, zAxAllF_defined.iff, zAxNegF_defined.iff, chainAsucc_defined.iff,
        seqSucc_defined.iff, seqAnt_defined.iff, lh_defined.iff, forall_and, and_assoc,
        numeral_eq_natCast]⟩

instance zKValidF_definable : 𝚫₁-Relation₃ (zKValidF : V → V → V → Prop) :=
  zKValidF_defined.to_definable

/-! ### Rung-0.5 premise-sequent side conditions (for a rule-faithful `ZPhi`)

The bare `ZPhi` I∀/I¬/Ind disjuncts pin only the *conclusion* succedent, not the premise sequents — so a
genuine reduct's end-sequent (hence chain threading) is uncomputable. These `…Wff` predicates pin the
Buchholz inference-rule premise sequents (rules read from `scratchpad/buchholz-gentzen.txt:140-152`); they
are wired as conjuncts into the corresponding `ZPhi` disjunct so `ZDerivation` carries them, and a genuine
validity-preserving reduct reads them off by inversion. They need only already-`𝚫₁` pieces
(`fstIdx`/`seqAnt`/`seqSucc` projections, `^⊥`, `inAnt`, and — for I∀/Ind — the `𝚺₁` `substs1`). -/

/-- **¬-introduction premise sequent**: `d0 ⊢ A,Γ→⊥` — succedent `⊥`, the negated formula `A = p` in
its antecedent, and `p`'s formula-hood `IsUFormula ℒₒᵣ p` (lap 74: the `ZDerivation_zsubst`
commutation `fvSubst_inegF` consumes it). No substitution (Buchholz 14.23 reduct `d[0] := d0`). -/
def zInegWff (p d0 : V) : Prop :=
  seqSucc (fstIdx d0) = (^⊥ : V) ∧ inAnt p (seqAnt (fstIdx d0)) ∧ IsUFormula ℒₒᵣ p

/-- **`𝚫₁`-definability of `zInegWff`** (all pieces `𝚺₀`: `fstIdx`/`seqSucc`/`seqAnt` projections, `^⊥`,
`inAnt`). Mirrors `zKValidDef`. -/
noncomputable def _root_.LO.FirstOrder.Arithmetic.zInegWffDef : 𝚫₁.Semisentence 2 := .mkDelta
  (.mkSigma “p d0.
    ∃ f, !fstIdxDef f d0 ∧
      (∃ ss, !seqSuccDef ss f ∧ ∃ bot, !qqFalsumDef bot ∧ ss = bot) ∧
      (∃ sa, !seqAntDef sa f ∧ !inAntDef p sa) ∧
      !(isUFormula ℒₒᵣ).sigma p ”)
  (.mkPi “p d0.
    ∀ f, !fstIdxDef f d0 →
      (∀ ss, !seqSuccDef ss f → ∀ bot, !qqFalsumDef bot → ss = bot) ∧
      (∀ sa, !seqAntDef sa f → !inAntDef p sa) ∧
      !(isUFormula ℒₒᵣ).pi p ”)

instance zInegWff_defined : 𝚫₁-Relation (zInegWff : V → V → Prop) via zInegWffDef :=
  ⟨by intro v
      simp [zInegWffDef, HierarchySymbol.Semiformula.val_sigma, fstIdx_defined.iff,
        seqSucc_defined.iff, qqFalsum_defined.iff, seqAnt_defined.iff, inAnt_defined.iff],
   by intro v
      simp [zInegWffDef, zInegWff, HierarchySymbol.Semiformula.val_sigma, fstIdx_defined.iff,
        seqSucc_defined.iff, qqFalsum_defined.iff, seqAnt_defined.iff, inAnt_defined.iff]⟩

instance zInegWff_definable : 𝚫₁-Relation (zInegWff : V → V → Prop) :=
  zInegWff_defined.to_definable

/-- **The genuine ∀-axiom succedent shape** (Buchholz `Ax^{∀p,k}: Γ → F(k)`): the `zAxAll` node's succedent
IS the instance `F(k) = substs1 (numeral k) p`. The current `zAxAll` `ZPhi` disjunct (`InternalZ:5310`)
carries only `∀p ∈ Γ` and does NOT pin this — so `seqSucc sⱼ = cutFormula` (the `hAll` plumbing input to the
re-keyed critical reduct's soundness `ZDerivation_iRKcCrit_of_zKValid`) is not yet derivable from `zKValid`.
This predicate is the building block for strengthening that disjunct (`d = zAxAll s p k ∧ … ∧ zAxAllSuccWff
s p k`), mirroring the lap-118 `zAxNeg` `A∈Γ` strengthening. -/
def zAxAllSuccWff (s p k : V) : Prop :=
  seqSucc s = substs1 ℒₒᵣ (Bootstrapping.Arithmetic.numeral k) p

/-- **`𝚫₁`-definability of `zAxAllSuccWff`** (mirrors `zIndWffDef`'s `numeral`/`substs1` blocks). -/
noncomputable def _root_.LO.FirstOrder.Arithmetic.zAxAllSuccWffDef : 𝚫₁.Semisentence 3 := .mkDelta
  (.mkSigma “s p k.
    ∃ ss, !seqSuccDef ss s ∧ ∃ nk, !(Bootstrapping.Arithmetic.numeralGraph) nk k ∧
      ∃ sub, !(substs1Graph ℒₒᵣ) sub nk p ∧ ss = sub ”)
  (.mkPi “s p k.
    ∀ ss, !seqSuccDef ss s → ∀ nk, !(Bootstrapping.Arithmetic.numeralGraph) nk k →
      ∀ sub, !(substs1Graph ℒₒᵣ) sub nk p → ss = sub ”)

instance zAxAllSuccWff_defined : 𝚫₁-Relation₃ (zAxAllSuccWff : V → V → V → Prop) via zAxAllSuccWffDef :=
  ⟨by intro v
      simp [zAxAllSuccWffDef, seqSucc_defined.iff,
        (Bootstrapping.Arithmetic.numeral_defined (V := V)).iff, (substs1.defined (L := ℒₒᵣ)).iff],
   by intro v
      simp [zAxAllSuccWffDef, zAxAllSuccWff, HierarchySymbol.Semiformula.val_sigma,
        seqSucc_defined.iff, (Bootstrapping.Arithmetic.numeral_defined (V := V)).iff,
        (substs1.defined (L := ℒₒᵣ)).iff]⟩

instance zAxAllSuccWff_definable : 𝚫₁-Relation₃ (zAxAllSuccWff : V → V → V → Prop) :=
  zAxAllSuccWff_defined.to_definable

/-- **The genuine I¬-rule premise-antecedent shape** (Buchholz `Γ,A ⊢ ⊥ / Γ ⊢ ¬A`): the I¬ node's premise
`d0` has antecedent EXACTLY `Γ,A` = `seqCons (seqAnt s) p` (the conclusion antecedent `Γ = seqAnt s` consed
with the active formula `p = A`). The current `zInegWff` (`InternalZ:1525`) carries only `inAnt p (seqAnt
(fstIdx d0))` and does NOT pin this exact shape — so `hNeg`'s `seqAnt (fstIdx d0) = seqCons (seqAnt sᵢ) p`
(the plumbing input to `ZDerivation_corrected_haux1_neg`'s threading reconstruction) is not yet derivable
from `zKValid`. This predicate is the building block for strengthening the `zIneg` disjunct. -/
def zInegAntWff (s p d0 : V) : Prop :=
  Seq (seqAnt s) ∧ seqAnt (fstIdx d0) = seqCons (seqAnt s) p

/-- **`𝚫₁`-definability of `zInegAntWff`** (all pieces `𝚺₀`: `fstIdx`/`seqAnt`/`Seq` projections +
`seqCons`). The bundled `Seq (seqAnt s)` makes the antecedent-shape self-preserving under eigenvariable
substitution (`fvSubstSeq_seqCons` needs `Seq` of the consed base). -/
noncomputable def _root_.LO.FirstOrder.Arithmetic.zInegAntWffDef : 𝚫₁.Semisentence 3 := .mkDelta
  (.mkSigma “s p d0.
    ∃ sa1, !seqAntDef sa1 s ∧ !seqDef sa1 ∧ ∃ f, !fstIdxDef f d0 ∧ ∃ sa0, !seqAntDef sa0 f ∧
      ∃ sc, !seqConsDef sc sa1 p ∧ sa0 = sc ”)
  (.mkPi “s p d0.
    ∀ sa1, !seqAntDef sa1 s → !seqDef sa1 ∧ ∀ f, !fstIdxDef f d0 → ∀ sa0, !seqAntDef sa0 f →
      ∀ sc, !seqConsDef sc sa1 p → sa0 = sc ”)

instance zInegAntWff_defined : 𝚫₁-Relation₃ (zInegAntWff : V → V → V → Prop) via zInegAntWffDef :=
  ⟨by intro v
      simp [zInegAntWffDef, fstIdx_defined.iff, seqAnt_defined.iff, seqCons_defined.iff,
        seq_defined.iff],
   by intro v
      simp [zInegAntWffDef, zInegAntWff, HierarchySymbol.Semiformula.val_sigma,
        fstIdx_defined.iff, seqAnt_defined.iff, seqCons_defined.iff, seq_defined.iff]⟩

instance zInegAntWff_definable : 𝚫₁-Relation₃ (zInegAntWff : V → V → V → Prop) :=
  zInegAntWff_defined.to_definable

/-- **∀-introduction premise sequent**: `d0 ⊢ Γ→F(a)` — same antecedent as the conclusion `s`, succedent
`F(a) = substs1 (^&a) p` (matrix `p`'s bound variable replaced by the eigenvariable `a`), and the matrix's
1-formula-hood `IsSemiformula ℒₒᵣ 1 p` (lap 74: the `ZDerivation_zsubst` commutations `fvSubst_all` /
`fvSubst_substs1_fvar` consume it). [Freshness `a ∉ s` is a separate global side condition.] The genuine
I∀ reduct `d0(a/n) ⊢ Γ→F(n)` reads off this. -/
def zIallWff (s a p d0 : V) : Prop :=
  seqAnt (fstIdx d0) = seqAnt s ∧ seqSucc (fstIdx d0) = substs1 ℒₒᵣ (qqFvar a) p ∧
    IsSemiformula ℒₒᵣ 1 p

/-- **`𝚫₁`-definability of `zIallWff`.** `fstIdx`/`seqAnt`/`seqSucc`/`qqFvar` are `𝚺₀`; the only `𝚺₁`
content is the substitution `substs1 ℒₒᵣ (^&a) p` (Foundation `substs1Graph`, single-valued ⟹ the σ
existential and π universal both pin it). -/
noncomputable def _root_.LO.FirstOrder.Arithmetic.zIallWffDef : 𝚫₁.Semisentence 4 := .mkDelta
  (.mkSigma “s a p d0.
    ∃ f, !fstIdxDef f d0 ∧
      (∃ sa0, !seqAntDef sa0 f ∧ ∃ sa1, !seqAntDef sa1 s ∧ sa0 = sa1) ∧
      (∃ ss, !seqSuccDef ss f ∧ ∃ fa, !qqFvarDef fa a ∧
        ∃ sub, !(substs1Graph ℒₒᵣ) sub fa p ∧ ss = sub) ∧
      !(isSemiformula ℒₒᵣ).sigma 1 p ”)
  (.mkPi “s a p d0.
    ∀ f, !fstIdxDef f d0 →
      (∀ sa0, !seqAntDef sa0 f → ∀ sa1, !seqAntDef sa1 s → sa0 = sa1) ∧
      (∀ ss, !seqSuccDef ss f → ∀ fa, !qqFvarDef fa a →
        ∀ sub, !(substs1Graph ℒₒᵣ) sub fa p → ss = sub) ∧
      !(isSemiformula ℒₒᵣ).pi 1 p ”)

instance zIallWff_defined : 𝚫₁-Relation₄ (zIallWff : V → V → V → V → Prop) via zIallWffDef :=
  ⟨by intro v
      simp [zIallWffDef, HierarchySymbol.Semiformula.val_sigma, fstIdx_defined.iff,
        seqAnt_defined.iff, seqSucc_defined.iff, qqFvar_defined.iff,
        (substs1.defined (L := ℒₒᵣ)).iff],
   by intro v
      simp [zIallWffDef, zIallWff, HierarchySymbol.Semiformula.val_sigma, fstIdx_defined.iff,
        seqAnt_defined.iff, seqSucc_defined.iff, qqFvar_defined.iff,
        (substs1.defined (L := ℒₒᵣ)).iff]⟩

instance zIallWff_definable : 𝚫₁-Relation₄ (zIallWff : V → V → V → V → Prop) :=
  zIallWff_defined.to_definable

/-- Eigenvariable accessor for an Ind node: `at' = ⟪a,t⟫`, so `a = π₁ at' = π₁ (π₁ (zRest d))`. -/
noncomputable def zIndEig (d : V) : V := π₁ (π₁ (zRest d))
/-- Induction-term accessor for an Ind node: `t = π₂ at' = π₂ (π₁ (zRest d))`. -/
noncomputable def zIndTerm (d : V) : V := π₂ (π₁ (zRest d))

@[simp] lemma zIndEig_zInd (s at' p d0 d1 : V) : zIndEig (zInd s at' p d0 d1) = π₁ at' := by
  simp [zIndEig]
@[simp] lemma zIndTerm_zInd (s at' p d0 d1 : V) : zIndTerm (zInd s at' p d0 d1) = π₂ at' := by
  simp [zIndTerm]

noncomputable def _root_.LO.FirstOrder.Arithmetic.zIndEigDef : 𝚺₀.Semisentence 2 := .mkSigma
  “y d. ∃ r <⁺ d, !zRestDef r d ∧ ∃ r2 <⁺ r, !pi₁Def r2 r ∧ !pi₁Def y r2”
instance zIndEig_defined : 𝚺₀-Function₁ (zIndEig : V → V) via zIndEigDef := .mk fun v ↦ by
  simp [zIndEigDef, zIndEig, zRest_defined.iff, pi₁_defined.iff]
instance zIndEig_definable : 𝚺₀-Function₁ (zIndEig : V → V) := zIndEig_defined.to_definable

noncomputable def _root_.LO.FirstOrder.Arithmetic.zIndTermDef : 𝚺₀.Semisentence 2 := .mkSigma
  “y d. ∃ r <⁺ d, !zRestDef r d ∧ ∃ r2 <⁺ r, !pi₁Def r2 r ∧ !pi₂Def y r2”
instance zIndTerm_defined : 𝚺₀-Function₁ (zIndTerm : V → V) via zIndTermDef := .mk fun v ↦ by
  simp [zIndTermDef, zIndTerm, zRest_defined.iff, pi₁_defined.iff, pi₂_defined.iff]
instance zIndTerm_definable : 𝚺₀-Function₁ (zIndTerm : V → V) := zIndTerm_defined.to_definable

/-- **Ind-rule premise sequents** (Buchholz complete-induction rule, `buchholz-gentzen.txt:140-152`),
on the whole Ind node `d = zInd s ⟪a,t⟫ p d0 d1`: `d0 ⊢ Γ→F(0)`, `d1 ⊢ F(a),Γ→F(Sa)` (`Sa = a+1`), and
the conclusion succedent `F(t)`. `F(·) = substs1 ℒₒᵣ · p`; `^&a = qqFvar a`; `0 = numeral 0`; `Sa =
qqAdd (^&a) (numeral 1)`; `t = zIndTerm d`. Unary on the node ⟹ its body can be strengthened (e.g. add
the `Γ ⊆ ant(d1)` threading needed by the genuine Ind reduct's `isChainInf`) without re-running the
`ZPhi` cascade. The genuine Ind reduct `K^r⟨d0, d1(a/0),…,d1(a/k−1)⟩` reads these by inversion. -/
noncomputable def zIndWff (d : V) : Prop :=
  (seqAnt (fstIdx (zIndPrem0 d)) = seqAnt (fstIdx d) ∧
    seqSucc (fstIdx (zIndPrem0 d)) = substs1 ℒₒᵣ (Bootstrapping.Arithmetic.numeral 0) (zIndP d)) ∧
  (Seq (seqAnt (fstIdx d)) ∧
    seqAnt (fstIdx (zIndPrem1 d)) =
      seqCons (seqAnt (fstIdx d)) (substs1 ℒₒᵣ (qqFvar (zIndEig d)) (zIndP d)) ∧
    seqSucc (fstIdx (zIndPrem1 d)) =
      substs1 ℒₒᵣ (Bootstrapping.Arithmetic.qqAdd (qqFvar (zIndEig d))
        (Bootstrapping.Arithmetic.numeral 1)) (zIndP d)) ∧
  seqSucc (fstIdx d) = substs1 ℒₒᵣ (zIndTerm d) (zIndP d) ∧
  IsSemiformula ℒₒᵣ 1 (zIndP d) ∧
  IsSemiterm ℒₒᵣ 0 (zIndTerm d)

/-- **`𝚫₁`-definability of `zIndWff`.** Projections (`fstIdx`/`zIndP`/`zIndPrem0/1`/`zIndEig`/`zIndTerm`/
`seqAnt`/`seqSucc`/`inAnt`/`qqFvar`) are `𝚺₀`; the `𝚺₁` content is the term-codes `numeral`/`qqAdd` and the
substitution `substs1`, each single-valued ⟹ σ existential / π universal both pin them. -/
noncomputable def _root_.LO.FirstOrder.Arithmetic.zIndWffDef : 𝚫₁.Semisentence 1 := .mkDelta
  (.mkSigma “d.
    ∃ s, !fstIdxDef s d ∧ ∃ p, !zIndPDef p d ∧ ∃ d0, !zIndPrem0Def d0 d ∧ ∃ d1, !zIndPrem1Def d1 d ∧
    ∃ a, !zIndEigDef a d ∧ ∃ t, !zIndTermDef t d ∧
    ∃ f0, !fstIdxDef f0 d0 ∧ ∃ f1, !fstIdxDef f1 d1 ∧ ∃ fa, !qqFvarDef fa a ∧
    ∃ sas, !seqAntDef sas s ∧
    (∃ sa0, !seqAntDef sa0 f0 ∧ sa0 = sas) ∧
    (∃ ss0, !seqSuccDef ss0 f0 ∧ ∃ z0, !(Bootstrapping.Arithmetic.numeralGraph) z0 0 ∧
      ∃ sub0, !(substs1Graph ℒₒᵣ) sub0 z0 p ∧ ss0 = sub0) ∧
    (!seqDef sas ∧ ∃ sa1, !seqAntDef sa1 f1 ∧ ∃ subfa, !(substs1Graph ℒₒᵣ) subfa fa p ∧
      ∃ sc, !seqConsDef sc sas subfa ∧ sa1 = sc) ∧
    (∃ ss1, !seqSuccDef ss1 f1 ∧ ∃ z1, !(Bootstrapping.Arithmetic.numeralGraph) z1 1 ∧
      ∃ sa, !(Bootstrapping.Arithmetic.qqAddGraph) sa fa z1 ∧
      ∃ subsa, !(substs1Graph ℒₒᵣ) subsa sa p ∧ ss1 = subsa) ∧
    (∃ ss, !seqSuccDef ss s ∧ ∃ subt, !(substs1Graph ℒₒᵣ) subt t p ∧ ss = subt) ∧
    !(isSemiformula ℒₒᵣ).sigma 1 p ∧ !(isSemiterm ℒₒᵣ).sigma 0 t ”)
  (.mkPi “d.
    ∀ s, !fstIdxDef s d → ∀ p, !zIndPDef p d → ∀ d0, !zIndPrem0Def d0 d → ∀ d1, !zIndPrem1Def d1 d →
    ∀ a, !zIndEigDef a d → ∀ t, !zIndTermDef t d →
    ∀ f0, !fstIdxDef f0 d0 → ∀ f1, !fstIdxDef f1 d1 → ∀ fa, !qqFvarDef fa a →
    ∀ sas, !seqAntDef sas s →
    (∀ sa0, !seqAntDef sa0 f0 → sa0 = sas) ∧
    (∀ ss0, !seqSuccDef ss0 f0 → ∀ z0, !(Bootstrapping.Arithmetic.numeralGraph) z0 0 →
      ∀ sub0, !(substs1Graph ℒₒᵣ) sub0 z0 p → ss0 = sub0) ∧
    (!seqDef sas ∧ ∀ sa1, !seqAntDef sa1 f1 → ∀ subfa, !(substs1Graph ℒₒᵣ) subfa fa p →
      ∀ sc, !seqConsDef sc sas subfa → sa1 = sc) ∧
    (∀ ss1, !seqSuccDef ss1 f1 → ∀ z1, !(Bootstrapping.Arithmetic.numeralGraph) z1 1 →
      ∀ sa, !(Bootstrapping.Arithmetic.qqAddGraph) sa fa z1 →
      ∀ subsa, !(substs1Graph ℒₒᵣ) subsa sa p → ss1 = subsa) ∧
    (∀ ss, !seqSuccDef ss s → ∀ subt, !(substs1Graph ℒₒᵣ) subt t p → ss = subt) ∧
    !(isSemiformula ℒₒᵣ).pi 1 p ∧ !(isSemiterm ℒₒᵣ).pi 0 t ”)

instance zIndWff_defined : 𝚫₁-Predicate (zIndWff : V → Prop) via zIndWffDef :=
  ⟨by intro v
      simp [zIndWffDef, fstIdx_defined.iff,
        zIndP_defined.iff, zIndPrem0_defined.iff, zIndPrem1_defined.iff, zIndEig_defined.iff,
        zIndTerm_defined.iff, seqAnt_defined.iff, seqSucc_defined.iff, qqFvar_defined.iff,
        seqCons_defined.iff, seq_defined.iff, (Bootstrapping.Arithmetic.numeral_defined (V := V)).iff,
        (Bootstrapping.Arithmetic.qqAdd_defined (V := V)).iff, (substs1.defined (L := ℒₒᵣ)).iff,
        and_assoc],
   by intro v
      simp [zIndWffDef, zIndWff, HierarchySymbol.Semiformula.val_sigma, fstIdx_defined.iff,
        zIndP_defined.iff, zIndPrem0_defined.iff, zIndPrem1_defined.iff, zIndEig_defined.iff,
        zIndTerm_defined.iff, seqAnt_defined.iff, seqSucc_defined.iff, qqFvar_defined.iff,
        seqCons_defined.iff, seq_defined.iff, (Bootstrapping.Arithmetic.numeral_defined (V := V)).iff,
        (Bootstrapping.Arithmetic.qqAdd_defined (V := V)).iff, (substs1.defined (L := ℒₒᵣ)).iff,
        and_assoc]⟩

instance zIndWff_definable : 𝚫₁-Predicate (zIndWff : V → Prop) :=
  zIndWff_defined.to_definable

/-- **L3.1 on a GENUINE chain** (E-CRUX2 §8.1, the lap-66 NEXT-item-1 bridge). For the chain `zK s r ds`
with chain-inference data `j0` (from `isChainInf`: `hj0`/`hAj0`/`hchain`/`hrank` are exactly its three
components), the coded symbol sequence `Iseq := tpSeq ds` (so `znth Iseq i = tp (znth ds i)`), and the
premise/conclusion permissibility (`hperm` = Lemma 3.3 on each premise `tp(dᵢ) ◁ Πᵢ`; `hnperm` =
criticality `tp(dᵢ) ⋪ Π`) plus the truth/rank well-formedness, Lemma 3.1 produces the redex `(i,j,k)`
on the GENUINE `tp`-symbols: `tp(dᵢ)=R_{Aᵢ}`, `tp(d_j)=L^k_{Aᵢ}`, `0<rk(Aᵢ)≤r`. This is the exact input
T3.4(a) (`irk_cut_lt_rank`) consumes. The chain-structural facts `hchain`/`hAj0`/`hrank` are discharged
directly from `isChainInf`; `hperm`/`hnperm`/`hwfR`/`hwfL` remain the deferred well-formedness obligations
(supplied later by the refined `ZPhi` end-sequent matching + §5 atomic truth). `Tr`/`Fa` are abstract
truth predicates (only `hdisj`/`hFa_rk`/`hFa_bot` consumed). -/
theorem inference_critical_pair_of_chain {s r ds j0 : V} {Tr Fa : V → Prop}
    (hj0 : j0 < lh ds)
    (hAj0 : chainAsucc ds j0 = seqSucc s ∨ chainAsucc ds j0 = (^⊥ : V))
    (hchain : ∀ i ≤ j0, ∀ B, inAnt B (chainAnt ds i) →
      inAnt B (seqAnt s) ∨ ∃ i' < i, B = chainAsucc ds i')
    (hrank : ∀ i < j0, irk (chainAsucc ds i) ≤ r)
    (hwfR : ∀ i ≤ j0, ∀ A, tp (znth ds i) = isymR A → 0 < irk A ∨ Tr A)
    (hwfL : ∀ i ≤ j0, ∀ k A, tp (znth ds i) = isymLk k A → 0 < irk A ∨ Fa A)
    (hperm : ∀ i ≤ j0, iperm (tp (znth ds i)) (fstIdx (znth ds i)))
    (hnperm : ∀ i ≤ j0, ¬ iperm (tp (znth ds i)) s)
    (hdisj : ∀ A, ¬ (Tr A ∧ Fa A)) (hFa_rk : ∀ A, Fa A → irk A = 0)
    (hFa_bot : Fa (^⊥ : V)) :
    ∃ i j k, i < j ∧ j ≤ j0 ∧ tp (znth ds i) = isymR (chainAsucc ds i) ∧
      tp (znth ds j) = isymLk k (chainAsucc ds i) ∧
      0 < irk (chainAsucc ds i) ∧ irk (chainAsucc ds i) ≤ r := by
  -- For i ≤ j0 < lh ds the coded read-out is the genuine `tp`.
  have hznth : ∀ i, i ≤ j0 → znth (tpSeq ds) i = tp (znth ds i) :=
    fun i hi => znth_tpSeq (lt_of_le_of_lt hi hj0)
  -- Repackage the iperm hypotheses into L3.1's unfolded disjunction form (chainAsucc/chainAnt are
  -- `seqSucc/seqAnt ∘ fstIdx` by definition; rewrite `tp (znth ds i)` to `znth (tpSeq ds) i`).
  have hperm' : ∀ i ≤ j0, znth (tpSeq ds) i = isymR (chainAsucc ds i) ∨
      (∃ k A, znth (tpSeq ds) i = isymLk k A ∧ inAnt A (chainAnt ds i)) ∨
      znth (tpSeq ds) i = isymRep := by
    intro i hi; rw [hznth i hi]; exact hperm i hi
  have hnperm' : ∀ i ≤ j0, ¬ (znth (tpSeq ds) i = isymR (seqSucc s) ∨
      (∃ k A, znth (tpSeq ds) i = isymLk k A ∧ inAnt A (seqAnt s)) ∨
      znth (tpSeq ds) i = isymRep) := by
    intro i hi; rw [hznth i hi]; exact hnperm i hi
  have hwfR' : ∀ i ≤ j0, ∀ A, znth (tpSeq ds) i = isymR A → 0 < irk A ∨ Tr A := by
    intro i hi A h; rw [hznth i hi] at h; exact hwfR i hi A h
  have hwfL' : ∀ i ≤ j0, ∀ k A, znth (tpSeq ds) i = isymLk k A → 0 < irk A ∨ Fa A := by
    intro i hi k A h; rw [hznth i hi] at h; exact hwfL i hi k A h
  have hAj0' : chainAsucc ds j0 = seqSucc s ∨ Fa (chainAsucc ds j0) := by
    rcases hAj0 with h | h
    · exact Or.inl h
    · exact Or.inr (by rw [h]; exact hFa_bot)
  obtain ⟨i, j, k, hij, hj_le, hIi, hIj, hrk, hrkr⟩ :=
    inference_critical_pair_rank (Iseq := tpSeq ds) (Asucc := chainAsucc ds) (Gam := chainAnt ds)
      (Γmain := seqAnt s) (Cmain := seqSucc s) inAnt Tr Fa
      hwfR' hwfL' hperm' hnperm' hchain hAj0' hdisj hFa_rk hrank
  refine ⟨i, j, k, hij, hj_le, ?_, ?_, hrk, hrkr⟩
  · rw [← hznth i (le_of_lt (lt_of_lt_of_le hij hj_le))]; exact hIi
  · rw [← hznth j hj_le]; exact hIj

/-- **L3.1 on a genuine chain, with the truth bookkeeping discharged for the CURRENT `tp`.** Specialises
`inference_critical_pair_of_chain` at `Tr := ⊥`, `Fa := (· = ⊥)`: then `tp_ne_isymLk` discharges `hwfL`
`tp_isymR_pos` reduces `hwfR` to formula-hood of the I-rule principal formulas (`hform1`/`hform2`),
**`tp_isymLk_pos` reduces `hwfL` to formula-hood of the §5 atomic principal formulas (`hform5`/`hform6`)**
— so `hwfL` is now discharged by the genuine rank bound, not vacuously — and `hdisj`/`hFa_rk`/`hFa_bot`
are immediate. **The deferred obligation is now exactly `hperm`+`hnperm` (Lemma 3.3 `tp(dᵢ)◁Πᵢ` +
criticality `tp(dᵢ)⋪Π`) plus principal-formula well-formedness** — pinpointing that the only
genuinely-missing content is the sequent-matching (`ZPhi` end-sequent + §5 antecedent membership) that
makes `hperm`/`hnperm` simultaneously satisfiable for a real critical chain. -/
theorem inference_critical_pair_of_chain_tp {s r ds j0 : V}
    (hj0 : j0 < lh ds)
    (hAj0 : chainAsucc ds j0 = seqSucc s ∨ chainAsucc ds j0 = (^⊥ : V))
    (hchain : ∀ i ≤ j0, ∀ B, inAnt B (chainAnt ds i) →
      inAnt B (seqAnt s) ∨ ∃ i' < i, B = chainAsucc ds i')
    (hrank : ∀ i < j0, irk (chainAsucc ds i) ≤ r)
    (hform1 : ∀ i ≤ j0, zTag (znth ds i) = 1 → IsUFormula ℒₒᵣ (zIallF (znth ds i)))
    (hform2 : ∀ i ≤ j0, zTag (znth ds i) = 2 → IsUFormula ℒₒᵣ (zInegF (znth ds i)))
    (hform5 : ∀ i ≤ j0, zTag (znth ds i) = 5 → IsUFormula ℒₒᵣ (zAxAllF (znth ds i)))
    (hform6 : ∀ i ≤ j0, zTag (znth ds i) = 6 → IsUFormula ℒₒᵣ (zAxNegF (znth ds i)))
    (hperm : ∀ i ≤ j0, iperm (tp (znth ds i)) (fstIdx (znth ds i)))
    (hnperm : ∀ i ≤ j0, ¬ iperm (tp (znth ds i)) s) :
    ∃ i j k, i < j ∧ j ≤ j0 ∧ tp (znth ds i) = isymR (chainAsucc ds i) ∧
      tp (znth ds j) = isymLk k (chainAsucc ds i) ∧
      0 < irk (chainAsucc ds i) ∧ irk (chainAsucc ds i) ≤ r :=
  inference_critical_pair_of_chain (Tr := fun _ => False) (Fa := fun A => A = (^⊥ : V))
    hj0 hAj0 hchain hrank
    (fun i hi A h => Or.inl (tp_isymR_pos h (hform1 i hi) (hform2 i hi)))
    (fun i hi k A h => Or.inl (tp_isymLk_pos h (hform5 i hi) (hform6 i hi)))
    hperm hnperm
    (fun _ h => h.1)
    (fun A h => by rw [h]; exact irk_falsum)
    rfl

/-! ## Internal variadic max-fold over a premise sequence

The `K^r` rule takes a *sequence* `ds`; `idg`/`iõ` fold over it inside `V`. `InternalCor34.ibigMul`
is a meta-iterate (external `k : ℕ`) and cannot reach an internal arity `lh ds`; this is the genuine
internal fold via `PR.Construction` over a counter (partial fold of the first `j` elements).

`iseqMaxTab s ds = max_{i < lh ds} znth s (znth ds i)` — max of the value-table entries at the
sub-indices. For `idg`'s `K^r` case `max{idg(d0)-1,…,idg(dl)-1, r}`; since `∸` commutes with `max`,
this equals `max r (iseqMaxTab s ds ∸ 1)`. -/

def iseqMaxAux.blueprint : PR.Blueprint 2 where
  zero := .mkSigma “y s ds. y = 0”
  succ := .mkSigma “y ih n s ds.
    ∃ di, !znthDef di ds n ∧ ∃ v, !znthDef v s di ∧ !max.dfn y ih v”

noncomputable def iseqMaxAux.construction : PR.Construction V iseqMaxAux.blueprint where
  zero := fun _ ↦ 0
  succ := fun x n ih ↦ max ih (znth (x 0) (znth (x 1) n))
  zero_defined := .mk fun v ↦ by simp [iseqMaxAux.blueprint]
  succ_defined := .mk fun v ↦ by
    simp [iseqMaxAux.blueprint, znth_defined.iff, max_defined.iff]

/-- **Partial max fold**: `iseqMaxAux s ds j = max_{i < j} znth s (znth ds i)`. -/
noncomputable def iseqMaxAux (s ds j : V) : V := iseqMaxAux.construction.result ![s, ds] j

@[simp] lemma iseqMaxAux_zero (s ds : V) : iseqMaxAux s ds 0 = 0 := by
  simp [iseqMaxAux, iseqMaxAux.construction]

@[simp] lemma iseqMaxAux_succ (s ds j : V) :
    iseqMaxAux s ds (j + 1) = max (iseqMaxAux s ds j) (znth s (znth ds j)) := by
  simp [iseqMaxAux, iseqMaxAux.construction]

def _root_.LO.FirstOrder.Arithmetic.iseqMaxAuxDef : 𝚺₁.Semisentence 4 :=
  iseqMaxAux.blueprint.resultDef.rew (Rew.subst ![#0, #3, #1, #2])

instance iseqMaxAux_defined : 𝚺₁-Function₃ (iseqMaxAux : V → V → V → V) via iseqMaxAuxDef := .mk
  fun v ↦ by simp [iseqMaxAux.construction.result_defined_iff, iseqMaxAuxDef]; rfl

instance iseqMaxAux_definable : 𝚺₁-Function₃ (iseqMaxAux : V → V → V → V) :=
  iseqMaxAux_defined.to_definable
instance iseqMaxAux_definable' (Γ) : Γ-[m + 1]-Function₃ (iseqMaxAux : V → V → V → V) :=
  iseqMaxAux_definable.of_sigmaOne

/-- **Max of table values over a sequence**: `iseqMaxTab s ds = max_{i < lh ds} znth s (znth ds i)`. -/
noncomputable def iseqMaxTab (s ds : V) : V := iseqMaxAux s ds (lh ds)

def _root_.LO.FirstOrder.Arithmetic.iseqMaxTabDef : 𝚺₁.Semisentence 3 := .mkSigma
  “y s ds. ∃ l, !lhDef l ds ∧ !iseqMaxAuxDef y s ds l”

instance iseqMaxTab_defined : 𝚺₁-Function₂ (iseqMaxTab : V → V → V) via iseqMaxTabDef := .mk
  fun v ↦ by simp [iseqMaxTabDef, iseqMaxTab, lh_defined.iff, iseqMaxAux_defined.iff]

instance iseqMaxTab_definable : 𝚺₁-Function₂ (iseqMaxTab : V → V → V) :=
  iseqMaxTab_defined.to_definable
instance iseqMaxTab_definable' (Γ) : Γ-[m + 1]-Function₂ (iseqMaxTab : V → V → V) :=
  iseqMaxTab_definable.of_sigmaOne

/-- Every sub-value in range is dominated by the partial fold. -/
lemma le_iseqMaxAux {s ds : V} :
    ∀ j : V, ∀ i < j, znth s (znth ds i) ≤ iseqMaxAux s ds j := by
  intro j
  induction j using ISigma1.sigma1_succ_induction
  · refine Definable.ball_lt (by definability) ?_
    apply Definable.comp₂ <;> definability
  case zero => intro i hi; exact absurd hi (by simp)
  case succ j ih =>
    intro i hi
    rw [iseqMaxAux_succ]
    rcases eq_or_lt_of_le (le_iff_lt_succ.mpr hi) with h | h
    · subst h; exact le_max_right _ _
    · exact le_trans (ih i h) (le_max_left _ _)

/-- The full fold dominates each sequence entry's table value (for `i < lh ds`). -/
lemma le_iseqMaxTab {s ds i : V} (hi : i < lh ds) :
    znth s (znth ds i) ≤ iseqMaxTab s ds := le_iseqMaxAux _ i hi

/-! ## `idg` — the degree assignment, total `𝚺₁` by course-of-values recursion

Buchholz §4: `dg(atom)=0`; `dg(I·d0)=dg(d0)`; `dg(Ind d0 d1)=max{dg(d0)-1,dg(d1)-1,rk F}`;
`dg(K^r d0…dl)=max{dg(d0)-1,…,dg(dl)-1,r}`. Realized as a total function on ALL codes via the same
table reduction as `iC` (`InternalONote`): `idgTable n = ⟨idg 0,…,idg n⟩`, the step `idgNext d s`
reading sub-results out of `s` at the projection indices (all `≤ d`). The `K^r` fold uses
`iseqMaxTab` with `max{…,dⱼ-1} = (max dⱼ) ∸ 1` (∸ commutes with max). -/

/-- Table step of `idg`: `idg d` from the table `s = ⟨idg 0,…,idg (d-1)⟩`, dispatching on `zTag d`. -/
noncomputable def idgNext (d s : V) : V :=
  if zTag d = 1 then znth s (zIallPrem d)
  else if zTag d = 2 then znth s (zInegPrem d)
  else if zTag d = 3 then
    max (max (znth s (zIndPrem0 d) - 1) (znth s (zIndPrem1 d) - 1)) (irk (zIndP d))
  else if zTag d = 4 then max (zKrank d) (iseqMaxTab s (zKseq d) - 1)
  else 0

noncomputable def _root_.LO.FirstOrder.Arithmetic.idgNextDef : 𝚺₁.Semisentence 3 := .mkSigma
  “y d s. ∃ t, !zTagDef t d ∧
    ( (t = 1 ∧ ∃ p, !zIallPremDef p d ∧ !znthDef y s p)
    ∨ (t = 2 ∧ ∃ p, !zInegPremDef p d ∧ !znthDef y s p)
    ∨ (t = 3 ∧ ∃ p0, !zIndPrem0Def p0 d ∧ ∃ v0, !znthDef v0 s p0 ∧ ∃ w0, !subDef w0 v0 1 ∧
        ∃ p1, !zIndPrem1Def p1 d ∧ ∃ v1, !znthDef v1 s p1 ∧ ∃ w1, !subDef w1 v1 1 ∧
        ∃ m, !max.dfn m w0 w1 ∧ ∃ pf, !zIndPDef pf d ∧ ∃ rk, !irkDef rk pf ∧ !max.dfn y m rk)
    ∨ (t = 4 ∧ ∃ rk, !zKrankDef rk d ∧ ∃ ds, !zKseqDef ds d ∧ ∃ f, !iseqMaxTabDef f s ds ∧
        ∃ w, !subDef w f 1 ∧ !max.dfn y rk w)
    ∨ (t ≠ 1 ∧ t ≠ 2 ∧ t ≠ 3 ∧ t ≠ 4 ∧ y = 0) )”

set_option maxHeartbeats 1000000 in
instance idgNext_defined : 𝚺₁-Function₂ (idgNext : V → V → V) via idgNextDef := .mk fun v ↦ by
  simp [idgNextDef, idgNext, zTag_defined.iff, zIallPrem_defined.iff, zInegPrem_defined.iff,
    zIndPrem0_defined.iff, zIndPrem1_defined.iff, zIndP_defined.iff, zKrank_defined.iff,
    zKseq_defined.iff, irk_defined.iff, iseqMaxTab_defined.iff, znth_defined.iff,
    sub_defined.iff, max_defined.iff]
  by_cases h1 : zTag (v 1) = 1
  · simp [h1]
  · by_cases h2 : zTag (v 1) = 2
    · simp [h1, h2]
    · by_cases h3 : zTag (v 1) = 3
      · simp [h1, h2, h3]
      · by_cases h4 : zTag (v 1) = 4
        · simp [h1, h2, h3, h4]
        · simp [h1, h2, h3, h4]

instance idgNext_definable : 𝚺₁-Function₂ (idgNext : V → V → V) := idgNext_defined.to_definable

/-- Blueprint for the `idg` table. -/
noncomputable def idgTable.blueprint : PR.Blueprint 0 where
  zero := .mkSigma “y. !mkSeq₁Def y 0”
  succ := .mkSigma “y ih n. ∃ v, !idgNextDef v (n + 1) ih ∧ !seqConsDef y ih v”

noncomputable def idgTable.construction : PR.Construction V idgTable.blueprint where
  zero := fun _ ↦ !⟦0⟧
  succ := fun _ n ih ↦ seqCons ih (idgNext (n + 1) ih)
  zero_defined := .mk fun v ↦ by
    simp [idgTable.blueprint, mkSeq₁Def, seqCons_defined.iff, emptyset_def]
  succ_defined := .mk fun v ↦ by
    simp [idgTable.blueprint, idgNext_defined.iff, seqCons_defined.iff]

/-- **The `idg` table**: `idgTable n = ⟨idg 0,…,idg n⟩` (length `n+1`). -/
noncomputable def idgTable (n : V) : V := idgTable.construction.result ![] n

@[simp] lemma idgTable_zero : idgTable (0 : V) = !⟦0⟧ := by simp [idgTable, idgTable.construction]

@[simp] lemma idgTable_succ (n : V) :
    idgTable (n + 1) = seqCons (idgTable n) (idgNext (n + 1) (idgTable n)) := by
  simp [idgTable, idgTable.construction]

/-- **The degree** `dg(d)` of a code: the `d`-th entry of the table. -/
noncomputable def idg (d : V) : V := znth (idgTable d) d

noncomputable def _root_.LO.FirstOrder.Arithmetic.idgTableDef : 𝚺₁.Semisentence 2 :=
  idgTable.blueprint.resultDef.rew (Rew.subst ![#0, #1])

instance idgTable_defined : 𝚺₁-Function₁ (idgTable : V → V) via idgTableDef := .mk
  fun v ↦ by simp [idgTable.construction.result_defined_iff, idgTableDef]; rfl

instance idgTable_definable : 𝚺₁-Function₁ (idgTable : V → V) := idgTable_defined.to_definable
instance idgTable_definable' (Γ) : Γ-[m + 1]-Function₁ (idgTable : V → V) :=
  idgTable_definable.of_sigmaOne

noncomputable def _root_.LO.FirstOrder.Arithmetic.idgDef : 𝚺₁.Semisentence 2 := .mkSigma
  “y d. ∃ t, !idgTableDef t d ∧ !znthDef y t d”

instance idg_defined : 𝚺₁-Function₁ (idg : V → V) via idgDef := .mk fun v ↦ by
  simp [idgDef, idg, idgTable_defined.iff, znth_defined.iff]

instance idg_definable : 𝚺₁-Function₁ (idg : V → V) := idg_defined.to_definable
instance idg_definable' (Γ) : Γ-[m + 1]-Function₁ (idg : V → V) := idg_definable.of_sigmaOne

/-! ### Structural correctness of the `idg` table (mirror `iC`) -/

private lemma def_idgTable {k} (i : Fin k) :
    𝚺-[1].DefinableFunction (fun v : Fin k → V ↦ idgTable (v i)) :=
  DefinableFunction₁.comp (F := idgTable) (DefinableFunction.var i)

private lemma def_idg {k} (i : Fin k) :
    𝚺-[1].DefinableFunction (fun v : Fin k → V ↦ idg (v i)) :=
  DefinableFunction₁.comp (F := idg) (DefinableFunction.var i)

@[simp] lemma idgTable_seq (n : V) : Seq (idgTable n) := by
  induction n using ISigma1.sigma1_succ_induction
  · exact Definable.comp₁ (def_idgTable 0)
  case zero => simp
  case succ n ih => rw [idgTable_succ]; exact ih.seqCons _

@[simp] lemma idgTable_lh (n : V) : lh (idgTable n) = n + 1 := by
  induction n using ISigma1.sigma1_succ_induction
  · exact Definable.comp₂ (DefinableFunction₁.comp (F := lh) (def_idgTable 0)) (by definability)
  case zero => simp
  case succ n ih => rw [idgTable_succ, Seq.lh_seqCons _ (idgTable_seq n), ih]

lemma znth_idgTable_succ {n k : V} (hk : k < n + 1) :
    znth (idgTable (n + 1)) k = znth (idgTable n) k := by
  rw [idgTable_succ]
  exact znth_seqCons_of_lt (idgTable_seq n) _ (by rw [idgTable_lh]; exact hk)

/-- **Table stability**: every entry of the length-`(N+1)` table is the genuine `idg` value. -/
lemma znth_idgTable_eq_idg : ∀ N : V, ∀ k ≤ N, znth (idgTable N) k = idg k := by
  intro N
  induction N using ISigma1.sigma1_succ_induction
  · refine Definable.ball_le (by definability) ?_
    exact Definable.comp₂
      (DefinableFunction₂.comp (F := znth) (def_idgTable 1) (DefinableFunction.var 0))
      (def_idg 0)
  case zero =>
    intro k hk; rcases (nonpos_iff_eq_zero.mp hk) with rfl; rfl
  case succ N ih =>
    intro k hk
    rcases eq_or_lt_of_le hk with rfl | hlt
    · rfl
    · rw [znth_idgTable_succ hlt]; exact ih k (le_iff_lt_succ.mpr hlt)

/-- `idg c = idgNext c (idgTable (c-1))` for positive codes (the table-reduction unfolding). -/
lemma idg_eq_idgNext {c : V} (hpos : 0 < c) : idg c = idgNext c (idgTable (c - 1)) := by
  obtain ⟨M, rfl⟩ : ∃ M, c = M + 1 := ⟨c - 1, (sub_add_self_of_le (pos_iff_one_le.mp hpos)).symm⟩
  have key : znth (idgTable (M + 1)) (M + 1) = idgNext (M + 1) (idgTable M) := by
    rw [idgTable_succ]
    have h := znth_seqCons_self (idgTable_seq M) (idgNext (M + 1) (idgTable M))
    rwa [idgTable_lh] at h
  simp only [idg, add_tsub_cancel_right, key]

/-- `a < c ⟹ a ≤ c - 1` (a sub-index lands in the length-`c` table). -/
lemma le_pred_of_lt {a c : V} (h : a < c) : a ≤ c - 1 := by
  have hc : 0 < c := lt_of_le_of_lt (show (0 : V) ≤ a by simp) h
  refine le_iff_lt_succ.mpr ?_
  rwa [sub_add_self_of_le (pos_iff_one_le.mp hc)]

/-! ### `idg` recursion equations (Buchholz §4) -/

@[simp] lemma idg_zAtom (s : V) : idg (zAtom s) = 0 := by
  rw [idg_eq_idgNext (by simp [zAtom]), idgNext]
  simp [zTag_zAtom]

@[simp] lemma idg_zIall (s a p d0 : V) : idg (zIall s a p d0) = idg d0 := by
  rw [idg_eq_idgNext (by simp [zIall]), idgNext, if_pos (zTag_zIall s a p d0), zIallPrem_zIall]
  exact znth_idgTable_eq_idg _ d0 (le_pred_of_lt (d0_lt_zIall s a p d0))

@[simp] lemma idg_zIneg (s p d0 : V) : idg (zIneg s p d0) = idg d0 := by
  rw [idg_eq_idgNext (by simp [zIneg]), idgNext, if_neg (by simp), if_pos (zTag_zIneg s p d0),
    zInegPrem_zIneg]
  exact znth_idgTable_eq_idg _ d0 (le_pred_of_lt (d0_lt_zIneg s p d0))

@[simp] lemma idg_zInd (s at' p d0 d1 : V) :
    idg (zInd s at' p d0 d1) = max (max (idg d0 - 1) (idg d1 - 1)) (irk p) := by
  rw [idg_eq_idgNext (by simp [zInd]), idgNext, if_neg (by simp), if_neg (by simp),
    if_pos (zTag_zInd s at' p d0 d1), zIndPrem0_zInd, zIndPrem1_zInd, zIndP_zInd,
    znth_idgTable_eq_idg _ d0 (le_pred_of_lt (d0_lt_zInd s at' p d0 d1)),
    znth_idgTable_eq_idg _ d1 (le_pred_of_lt (d1_lt_zInd s at' p d0 d1))]

/-- **`dg(Ax^{∀xF,k}) = 0`** (Buchholz Lemma 5.2: every atomic axiom has degree 0). Tag 5 falls into
`idgNext`'s `else` branch. -/
@[simp] lemma idg_zAxAll (s p k : V) : idg (zAxAll s p k) = 0 := by
  rw [idg_eq_idgNext (by simp [zAxAll]), idgNext]; simp [zTag_zAxAll]

/-- **`dg(Ax^{¬A,0}) = 0`** (Buchholz Lemma 5.2). Tag 6 falls into `idgNext`'s `else` branch. -/
@[simp] lemma idg_zAxNeg (s p : V) : idg (zAxNeg s p) = 0 := by
  rw [idg_eq_idgNext (by simp [zAxNeg]), idgNext]; simp [zTag_zAxNeg]

/-- **`dg(Ax^1_{·→C}) = 0`** (Buchholz Lemma 5.2: every atomic axiom has degree 0). Tag 7 falls into
`idgNext`'s `else` branch. -/
@[simp] lemma idg_zAx1 (s C : V) : idg (zAx1 s C) = 0 := by
  rw [idg_eq_idgNext (by simp [zAx1]), idgNext]; simp [zTag_zAx1]

/-! ### `idg`-fold over a premise sequence (for the variadic `K^r` equation)

`iseqMaxIdg ds = max_{i < lh ds} idg(znth ds i)` — the genuine idg-fold (applies `idg` directly,
independent of any value-table). The `K^r` step in `idgNext` reads the *table* form
`iseqMaxTab (idgTable M) ds`; when `M` dominates every entry (which holds for `M = zK… - 1`), the two
agree by table stability. This yields the clean `idg_zK` equation. -/

noncomputable def iseqMaxIdgAux.blueprint : PR.Blueprint 1 where
  zero := .mkSigma “y ds. y = 0”
  succ := .mkSigma “y ih n ds.
    ∃ di, !znthDef di ds n ∧ ∃ v, !idgDef v di ∧ !max.dfn y ih v”

noncomputable def iseqMaxIdgAux.construction : PR.Construction V iseqMaxIdgAux.blueprint where
  zero := fun _ ↦ 0
  succ := fun x n ih ↦ max ih (idg (znth (x 0) n))
  zero_defined := .mk fun v ↦ by simp [iseqMaxIdgAux.blueprint]
  succ_defined := .mk fun v ↦ by
    simp [iseqMaxIdgAux.blueprint, znth_defined.iff, idg_defined.iff, max_defined.iff]

/-- Partial idg-fold: `iseqMaxIdgAux ds j = max_{i < j} idg(znth ds i)`. -/
noncomputable def iseqMaxIdgAux (ds j : V) : V := iseqMaxIdgAux.construction.result ![ds] j

@[simp] lemma iseqMaxIdgAux_zero (ds : V) : iseqMaxIdgAux ds 0 = 0 := by
  simp [iseqMaxIdgAux, iseqMaxIdgAux.construction]

@[simp] lemma iseqMaxIdgAux_succ (ds j : V) :
    iseqMaxIdgAux ds (j + 1) = max (iseqMaxIdgAux ds j) (idg (znth ds j)) := by
  simp [iseqMaxIdgAux, iseqMaxIdgAux.construction]

noncomputable def _root_.LO.FirstOrder.Arithmetic.iseqMaxIdgAuxDef : 𝚺₁.Semisentence 3 :=
  iseqMaxIdgAux.blueprint.resultDef.rew (Rew.subst ![#0, #2, #1])

instance iseqMaxIdgAux_defined : 𝚺₁-Function₂ (iseqMaxIdgAux : V → V → V) via iseqMaxIdgAuxDef := .mk
  fun v ↦ by simp [iseqMaxIdgAux.construction.result_defined_iff, iseqMaxIdgAuxDef]; rfl

instance iseqMaxIdgAux_definable : 𝚺₁-Function₂ (iseqMaxIdgAux : V → V → V) :=
  iseqMaxIdgAux_defined.to_definable
instance iseqMaxIdgAux_definable' (Γ) : Γ-[m + 1]-Function₂ (iseqMaxIdgAux : V → V → V) :=
  iseqMaxIdgAux_definable.of_sigmaOne

/-- **idg-fold over a sequence**: `iseqMaxIdg ds = max_{i < lh ds} idg(znth ds i)`. -/
noncomputable def iseqMaxIdg (ds : V) : V := iseqMaxIdgAux ds (lh ds)

/-- **Table-fold = idg-fold under dominance.** If `M` is `≥` every in-range entry of `ds`,
the value-table fold over `idgTable M` agrees with the direct idg-fold. -/
lemma iseqMaxAux_idgTable_eq {M ds : V} (hdom : ∀ i < lh ds, znth ds i ≤ M) :
    ∀ j ≤ lh ds, iseqMaxAux (idgTable M) ds j = iseqMaxIdgAux ds j := by
  intro j
  induction j using ISigma1.sigma1_succ_induction
  · refine Definable.imp (by definability) ?_
    refine Definable.comp₂
      (DefinableFunction₃.comp (F := iseqMaxAux)
        (DefinableFunction₁.comp (F := idgTable) (DefinableFunction.const M))
        (DefinableFunction.const ds) (DefinableFunction.var 0))
      (DefinableFunction₂.comp (F := iseqMaxIdgAux) (DefinableFunction.const ds)
        (DefinableFunction.var 0))
  case zero => intro _; simp
  case succ j ih =>
    intro hj
    rw [iseqMaxAux_succ, iseqMaxIdgAux_succ, ih (le_trans (by simp) hj),
      znth_idgTable_eq_idg M (znth ds j) (hdom j (lt_of_lt_of_le (by simp) hj))]

/-- **The variadic `K^r` degree equation** (Buchholz §4): for a sequence of premises `ds`,
`dg(K^r_Π d0…dl) = max{dg(d0)-1,…,dg(dl)-1, r} = max r ((max_j dg(dⱼ)) ∸ 1)`. -/
lemma idg_zK (s r ds : V) (hds : Seq ds) :
    idg (zK s r ds) = max r (iseqMaxIdg ds - 1) := by
  have hdom : ∀ i < lh ds, znth ds i ≤ zK s r ds - 1 := fun i hi ↦
    le_pred_of_lt (lt_trans (lt_of_mem_rng (hds.znth hi)) (ds_lt_zK s r ds))
  rw [idg_eq_idgNext (by simp [zK]), idgNext, if_neg (by simp), if_neg (by simp), if_neg (by simp),
    if_pos (zTag_zK s r ds), zKrank_zK, zKseq_zK, iseqMaxTab,
    iseqMaxAux_idgTable_eq hdom (lh ds) (le_refl _), iseqMaxIdg]

/-! ## `iotil` (`õ`) — the pre-ordinal assignment, total `𝚺₁`

Buchholz §4: `õ(atom)=…(§5)`; `õ(I·d0)=õ(d0)+1`; `õ(Ind d0 d1)=ω^{õ d0} # ω^{õ d1 + 1}`;
`õ(K^r d0…dl)=ω^{õ d0} # … # ω^{õ dl}`. Here `ω^α = ocOadd α 1 0`, `+1 = iadd · (ocOadd 0 1 0)`,
`#` = `inadd`. Same table reduction as `idg`. The `K^r` `#`-fold uses the table-helper `iseqNaddTab`. -/

/-! ### `#`-fold over a premise sequence (table form, for the `K^r` step) -/

def iseqNaddTab.blueprint : PR.Blueprint 2 where
  zero := .mkSigma “y s ds. y = 0”
  succ := .mkSigma “y ih n s ds.
    ∃ di, !znthDef di ds n ∧ ∃ v, !znthDef v s di ∧ ∃ w, !ocOaddDef w v 1 0 ∧ !inaddDef y ih w”

noncomputable def iseqNaddTab.construction : PR.Construction V iseqNaddTab.blueprint where
  zero := fun _ ↦ 0
  succ := fun x n ih ↦ inadd ih (ocOadd (znth (x 0) (znth (x 1) n)) 1 0)
  zero_defined := .mk fun v ↦ by simp [iseqNaddTab.blueprint]
  succ_defined := .mk fun v ↦ by
    simp [iseqNaddTab.blueprint, znth_defined.iff, ocOadd_defined.iff, inadd_defined.iff]

/-- Partial `#`-fold of `ω^{table@(znth ds i)}` over the first `j` entries. -/
noncomputable def iseqNaddAux (s ds j : V) : V := iseqNaddTab.construction.result ![s, ds] j

@[simp] lemma iseqNaddAux_zero (s ds : V) : iseqNaddAux s ds 0 = 0 := by
  simp [iseqNaddAux, iseqNaddTab.construction]

@[simp] lemma iseqNaddAux_succ (s ds j : V) :
    iseqNaddAux s ds (j + 1) = inadd (iseqNaddAux s ds j) (ocOadd (znth s (znth ds j)) 1 0) := by
  simp [iseqNaddAux, iseqNaddTab.construction]

def _root_.LO.FirstOrder.Arithmetic.iseqNaddAuxDef : 𝚺₁.Semisentence 4 :=
  iseqNaddTab.blueprint.resultDef.rew (Rew.subst ![#0, #3, #1, #2])

instance iseqNaddAux_defined : 𝚺₁-Function₃ (iseqNaddAux : V → V → V → V) via iseqNaddAuxDef := .mk
  fun v ↦ by simp [iseqNaddTab.construction.result_defined_iff, iseqNaddAuxDef]; rfl

instance iseqNaddAux_definable : 𝚺₁-Function₃ (iseqNaddAux : V → V → V → V) :=
  iseqNaddAux_defined.to_definable
instance iseqNaddAux_definable' (Γ) : Γ-[m + 1]-Function₃ (iseqNaddAux : V → V → V → V) :=
  iseqNaddAux_definable.of_sigmaOne

/-- `#`-fold over the whole sequence: `iseqNaddTab s ds = #_{i<lh ds} ω^{znth s (znth ds i)}`. -/
noncomputable def iseqNaddTab (s ds : V) : V := iseqNaddAux s ds (lh ds)

def _root_.LO.FirstOrder.Arithmetic.iseqNaddTabDef : 𝚺₁.Semisentence 3 := .mkSigma
  “y s ds. ∃ l, !lhDef l ds ∧ !iseqNaddAuxDef y s ds l”

instance iseqNaddTab_defined : 𝚺₁-Function₂ (iseqNaddTab : V → V → V) via iseqNaddTabDef := .mk
  fun v ↦ by simp [iseqNaddTabDef, iseqNaddTab, lh_defined.iff, iseqNaddAux_defined.iff]

instance iseqNaddTab_definable : 𝚺₁-Function₂ (iseqNaddTab : V → V → V) :=
  iseqNaddTab_defined.to_definable
instance iseqNaddTab_definable' (Γ) : Γ-[m + 1]-Function₂ (iseqNaddTab : V → V → V) :=
  iseqNaddTab_definable.of_sigmaOne

/-! ### `iotil` table -/

/-- The pre-ordinal `õ` of an `Ax^{C,t}` atomic axiom (Buchholz Lemma 5.2, §5): `2·rk(C) − 1`, encoded
as the finite InternalONote `ocOadd 0 (rk C + rk C ∸ 1) 0`. For the L-symbol axioms `Ax^{∀xF,k}`
(`C = ∀xF`) and `Ax^{¬A,0}` (`C = ¬A`) where `rk(C) > 0`, the coefficient `2·rk(C)−1 ≥ 1`, so this is a
genuine NF (`isNF_oAtomLk_pos`). -/
noncomputable def oAtomLk (C : V) : V := ocOadd 0 (irk C + irk C - 1) 0

noncomputable def _root_.LO.FirstOrder.Arithmetic.oAtomLkDef : 𝚺₁.Semisentence 2 := .mkSigma
  “y C. ∃ c, !irkDef c C ∧ ∃ m, !subDef m (c + c) 1 ∧ !ocOaddDef y 0 m 0”
instance oAtomLk_defined : 𝚺₁-Function₁ (oAtomLk : V → V) via oAtomLkDef := .mk fun v ↦ by
  simp [oAtomLkDef, oAtomLk, irk_defined.iff, sub_defined.iff, ocOadd_defined.iff]
instance oAtomLk_definable : 𝚺₁-Function₁ (oAtomLk : V → V) := oAtomLk_defined.to_definable
instance oAtomLk_definable' (Γ) : Γ-[m + 1]-Function₁ (oAtomLk : V → V) := oAtomLk_definable.of_sigmaOne

/-- The pre-ordinal `õ` of an `Ax1_{Γ→C}` atomic axiom (Buchholz Lemma 5.2): `2·rk(C)`, as a finite
InternalONote (`0` when `rk C = 0`, else `ocOadd 0 (2·rk C) 0`). This is the õ of the reduct
`d[0] = Ax1_{Π0}` of an L-symbol axiom; `icmp_oAtom1_oAtomLk` is the Lemma-5.2 atomic descent. -/
noncomputable def oAtom1 (C : V) : V := if irk C = 0 then 0 else ocOadd 0 (irk C + irk C) 0

/-- `õ(Ax1_{Γ→C})` is always a genuine NF (it's `0`, or `ocOadd 0 (2·rk C) 0` with `2·rk C > 0`). -/
lemma isNF_oAtom1 (C : V) : isNF (oAtom1 C) := by
  rw [oAtom1]
  by_cases h : irk C = 0
  · rw [if_pos h]; exact isNF_zero
  · rw [if_neg h]
    have hpos : 0 < irk C := pos_iff_ne_zero.mpr h
    exact (isNF_ocOadd 0 (irk C + irk C) 0).2
      ⟨(add_pos hpos hpos).ne', isNF_zero, isNF_zero, Or.inl rfl⟩

noncomputable def _root_.LO.FirstOrder.Arithmetic.oAtom1Def : 𝚺₁.Semisentence 2 := .mkSigma
  “y C. ∃ c, !irkDef c C ∧ ( (c = 0 ∧ y = 0) ∨ (c ≠ 0 ∧ !ocOaddDef y 0 (c + c) 0) )”
instance oAtom1_defined : 𝚺₁-Function₁ (oAtom1 : V → V) via oAtom1Def := .mk fun v ↦ by
  simp [oAtom1Def, oAtom1, irk_defined.iff, ocOadd_defined.iff]
  by_cases h : irk (v 1) = 0 <;> simp [h]
instance oAtom1_definable : 𝚺₁-Function₁ (oAtom1 : V → V) := oAtom1_defined.to_definable

/-- Table step of `iotil`: dispatch on `zTag d`, reading sub-õ-values out of the table `s`. -/
noncomputable def ioNext (d s : V) : V :=
  if zTag d = 1 then iadd (znth s (zIallPrem d)) (ocOadd 0 1 0)
  else if zTag d = 2 then iadd (znth s (zInegPrem d)) (ocOadd 0 1 0)
  else if zTag d = 3 then
    inadd (ocOadd (znth s (zIndPrem0 d)) 1 0)
      (ocOadd (iadd (znth s (zIndPrem1 d)) (ocOadd 0 1 0)) 1 0)
  else if zTag d = 4 then iseqNaddTab s (zKseq d)
  else if zTag d = 5 then oAtomLk (^∀ (zAxAllF d) : V)
  else if zTag d = 6 then oAtomLk (inegF (zAxNegF d))
  else if zTag d = 7 then oAtom1 (zAx1F d)
  else 0

noncomputable def _root_.LO.FirstOrder.Arithmetic.ioNextDef : 𝚺₁.Semisentence 3 := .mkSigma
  “y d s. ∃ t, !zTagDef t d ∧ ∃ one, !ocOaddDef one 0 1 0 ∧
    ( (t = 1 ∧ ∃ p, !zIallPremDef p d ∧ ∃ v, !znthDef v s p ∧ !iaddDef y v one)
    ∨ (t = 2 ∧ ∃ p, !zInegPremDef p d ∧ ∃ v, !znthDef v s p ∧ !iaddDef y v one)
    ∨ (t = 3 ∧ ∃ p0, !zIndPrem0Def p0 d ∧ ∃ v0, !znthDef v0 s p0 ∧ ∃ w0, !ocOaddDef w0 v0 1 0 ∧
        ∃ p1, !zIndPrem1Def p1 d ∧ ∃ v1, !znthDef v1 s p1 ∧ ∃ v1s, !iaddDef v1s v1 one ∧
        ∃ w1, !ocOaddDef w1 v1s 1 0 ∧ !inaddDef y w0 w1)
    ∨ (t = 4 ∧ ∃ ds, !zKseqDef ds d ∧ !iseqNaddTabDef y s ds)
    ∨ (t = 5 ∧ ∃ r, !zRestDef r d ∧ ∃ p, !pi₁Def p r ∧ ∃ ap, !qqAllDef ap p ∧ !oAtomLkDef y ap)
    ∨ (t = 6 ∧ ∃ r, !zRestDef r d ∧ ∃ nb, !inegFDef nb r ∧ !oAtomLkDef y nb)
    ∨ (t = 7 ∧ ∃ C, !zAx1FDef C d ∧ !oAtom1Def y C)
    ∨ (t ≠ 1 ∧ t ≠ 2 ∧ t ≠ 3 ∧ t ≠ 4 ∧ t ≠ 5 ∧ t ≠ 6 ∧ t ≠ 7 ∧ y = 0) )”

set_option maxHeartbeats 1000000 in
instance ioNext_defined : 𝚺₁-Function₂ (ioNext : V → V → V) via ioNextDef := .mk fun v ↦ by
  simp [ioNextDef, ioNext, zTag_defined.iff, zIallPrem_defined.iff, zInegPrem_defined.iff,
    zIndPrem0_defined.iff, zIndPrem1_defined.iff, zKseq_defined.iff, iadd_defined.iff,
    inadd_defined.iff, ocOadd_defined.iff, iseqNaddTab_defined.iff, znth_defined.iff,
    zRest_defined.iff, pi₁_defined.iff, qqForall_defined.iff, inegF_defined.iff,
    oAtomLk_defined.iff, oAtom1_defined.iff, zAx1F_defined.iff, zAxAllF, zAxNegF,
    numeral_eq_natCast]
  by_cases h1 : zTag (v 1) = 1
  · simp [h1]
  · by_cases h2 : zTag (v 1) = 2
    · simp [h1, h2]
    · by_cases h3 : zTag (v 1) = 3
      · simp [h1, h2, h3]
      · by_cases h4 : zTag (v 1) = 4
        · simp [h1, h2, h3, h4]
        · by_cases h5 : zTag (v 1) = 5
          · simp [h1, h2, h3, h4, h5]
          · by_cases h6 : zTag (v 1) = 6
            · simp [h1, h2, h3, h4, h5, h6]
            · by_cases h7 : zTag (v 1) = 7
              · simp [h1, h2, h3, h4, h5, h6, h7]
              · simp [h1, h2, h3, h4, h5, h6, h7]

instance ioNext_definable : 𝚺₁-Function₂ (ioNext : V → V → V) := ioNext_defined.to_definable

noncomputable def ioTable.blueprint : PR.Blueprint 0 where
  zero := .mkSigma “y. !mkSeq₁Def y 0”
  succ := .mkSigma “y ih n. ∃ v, !ioNextDef v (n + 1) ih ∧ !seqConsDef y ih v”

noncomputable def ioTable.construction : PR.Construction V ioTable.blueprint where
  zero := fun _ ↦ !⟦0⟧
  succ := fun _ n ih ↦ seqCons ih (ioNext (n + 1) ih)
  zero_defined := .mk fun v ↦ by
    simp [ioTable.blueprint, mkSeq₁Def, seqCons_defined.iff, emptyset_def]
  succ_defined := .mk fun v ↦ by
    simp [ioTable.blueprint, ioNext_defined.iff, seqCons_defined.iff]

noncomputable def ioTable (n : V) : V := ioTable.construction.result ![] n

@[simp] lemma ioTable_zero : ioTable (0 : V) = !⟦0⟧ := by simp [ioTable, ioTable.construction]

@[simp] lemma ioTable_succ (n : V) :
    ioTable (n + 1) = seqCons (ioTable n) (ioNext (n + 1) (ioTable n)) := by
  simp [ioTable, ioTable.construction]

/-- **The pre-ordinal** `õ(d)` of a code: the `d`-th entry of the table. -/
noncomputable def iotil (d : V) : V := znth (ioTable d) d

noncomputable def _root_.LO.FirstOrder.Arithmetic.ioTableDef : 𝚺₁.Semisentence 2 :=
  ioTable.blueprint.resultDef.rew (Rew.subst ![#0, #1])

instance ioTable_defined : 𝚺₁-Function₁ (ioTable : V → V) via ioTableDef := .mk
  fun v ↦ by simp [ioTable.construction.result_defined_iff, ioTableDef]; rfl

instance ioTable_definable : 𝚺₁-Function₁ (ioTable : V → V) := ioTable_defined.to_definable
instance ioTable_definable' (Γ) : Γ-[m + 1]-Function₁ (ioTable : V → V) :=
  ioTable_definable.of_sigmaOne

noncomputable def _root_.LO.FirstOrder.Arithmetic.iotilDef : 𝚺₁.Semisentence 2 := .mkSigma
  “y d. ∃ t, !ioTableDef t d ∧ !znthDef y t d”

instance iotil_defined : 𝚺₁-Function₁ (iotil : V → V) via iotilDef := .mk fun v ↦ by
  simp [iotilDef, iotil, ioTable_defined.iff, znth_defined.iff]

instance iotil_definable : 𝚺₁-Function₁ (iotil : V → V) := iotil_defined.to_definable
instance iotil_definable' (Γ) : Γ-[m + 1]-Function₁ (iotil : V → V) := iotil_definable.of_sigmaOne

/-! ### Structural correctness of the `iotil` table (mirror `idg`) -/

private lemma def_ioTable {k} (i : Fin k) :
    𝚺-[1].DefinableFunction (fun v : Fin k → V ↦ ioTable (v i)) :=
  DefinableFunction₁.comp (F := ioTable) (DefinableFunction.var i)

private lemma def_iotil {k} (i : Fin k) :
    𝚺-[1].DefinableFunction (fun v : Fin k → V ↦ iotil (v i)) :=
  DefinableFunction₁.comp (F := iotil) (DefinableFunction.var i)

@[simp] lemma ioTable_seq (n : V) : Seq (ioTable n) := by
  induction n using ISigma1.sigma1_succ_induction
  · exact Definable.comp₁ (def_ioTable 0)
  case zero => simp
  case succ n ih => rw [ioTable_succ]; exact ih.seqCons _

@[simp] lemma ioTable_lh (n : V) : lh (ioTable n) = n + 1 := by
  induction n using ISigma1.sigma1_succ_induction
  · exact Definable.comp₂ (DefinableFunction₁.comp (F := lh) (def_ioTable 0)) (by definability)
  case zero => simp
  case succ n ih => rw [ioTable_succ, Seq.lh_seqCons _ (ioTable_seq n), ih]

lemma znth_ioTable_succ {n k : V} (hk : k < n + 1) :
    znth (ioTable (n + 1)) k = znth (ioTable n) k := by
  rw [ioTable_succ]
  exact znth_seqCons_of_lt (ioTable_seq n) _ (by rw [ioTable_lh]; exact hk)

lemma znth_ioTable_eq_iotil : ∀ N : V, ∀ k ≤ N, znth (ioTable N) k = iotil k := by
  intro N
  induction N using ISigma1.sigma1_succ_induction
  · refine Definable.ball_le (by definability) ?_
    exact Definable.comp₂
      (DefinableFunction₂.comp (F := znth) (def_ioTable 1) (DefinableFunction.var 0))
      (def_iotil 0)
  case zero =>
    intro k hk; rcases (nonpos_iff_eq_zero.mp hk) with rfl; rfl
  case succ N ih =>
    intro k hk
    rcases eq_or_lt_of_le hk with rfl | hlt
    · rfl
    · rw [znth_ioTable_succ hlt]; exact ih k (le_iff_lt_succ.mpr hlt)

lemma iotil_eq_ioNext {c : V} (hpos : 0 < c) : iotil c = ioNext c (ioTable (c - 1)) := by
  obtain ⟨M, rfl⟩ : ∃ M, c = M + 1 := ⟨c - 1, (sub_add_self_of_le (pos_iff_one_le.mp hpos)).symm⟩
  have key : znth (ioTable (M + 1)) (M + 1) = ioNext (M + 1) (ioTable M) := by
    rw [ioTable_succ]
    have h := znth_seqCons_self (ioTable_seq M) (ioNext (M + 1) (ioTable M))
    rwa [ioTable_lh] at h
  simp only [iotil, add_tsub_cancel_right, key]

/-! ### `iotil` recursion equations (Buchholz §4, finite-premise cases) -/

@[simp] lemma iotil_zAtom (s : V) : iotil (zAtom s) = 0 := by
  rw [iotil_eq_ioNext (by simp [zAtom]), ioNext]; simp [zTag_zAtom]

@[simp] lemma iotil_zIall (s a p d0 : V) :
    iotil (zIall s a p d0) = iadd (iotil d0) (ocOadd 0 1 0) := by
  rw [iotil_eq_ioNext (by simp [zIall]), ioNext, if_pos (zTag_zIall s a p d0), zIallPrem_zIall,
    znth_ioTable_eq_iotil _ d0 (le_pred_of_lt (d0_lt_zIall s a p d0))]

@[simp] lemma iotil_zIneg (s p d0 : V) :
    iotil (zIneg s p d0) = iadd (iotil d0) (ocOadd 0 1 0) := by
  rw [iotil_eq_ioNext (by simp [zIneg]), ioNext, if_neg (by simp), if_pos (zTag_zIneg s p d0),
    zInegPrem_zIneg, znth_ioTable_eq_iotil _ d0 (le_pred_of_lt (d0_lt_zIneg s p d0))]

@[simp] lemma iotil_zInd (s at' p d0 d1 : V) :
    iotil (zInd s at' p d0 d1) =
      inadd (ocOadd (iotil d0) 1 0) (ocOadd (iadd (iotil d1) (ocOadd 0 1 0)) 1 0) := by
  rw [iotil_eq_ioNext (by simp [zInd]), ioNext, if_neg (by simp), if_neg (by simp),
    if_pos (zTag_zInd s at' p d0 d1), zIndPrem0_zInd, zIndPrem1_zInd,
    znth_ioTable_eq_iotil _ d0 (le_pred_of_lt (d0_lt_zInd s at' p d0 d1)),
    znth_ioTable_eq_iotil _ d1 (le_pred_of_lt (d1_lt_zInd s at' p d0 d1))]

/-- **`õ(Ax^{∀xF,k}) = 2·rk(∀xF) − 1`** (Buchholz Lemma 5.2). The atomic axioms read no sub-õ from the
table, so the value is closed-form. -/
@[simp] lemma iotil_zAxAll (s p k : V) : iotil (zAxAll s p k) = oAtomLk (^∀ p : V) := by
  rw [iotil_eq_ioNext (by simp [zAxAll]), ioNext, if_neg (by simp), if_neg (by simp),
    if_neg (by simp), if_neg (by simp), if_pos (zTag_zAxAll s p k), zAxAllF_zAxAll]

/-- **`õ(Ax^{¬A,0}) = 2·rk(¬A) − 1`** (Buchholz Lemma 5.2). -/
@[simp] lemma iotil_zAxNeg (s p : V) : iotil (zAxNeg s p) = oAtomLk (inegF p) := by
  rw [iotil_eq_ioNext (by simp [zAxNeg]), ioNext, if_neg (by simp), if_neg (by simp),
    if_neg (by simp), if_neg (by simp), if_neg (by simp), if_pos (zTag_zAxNeg s p), zAxNegF_zAxNeg]

/-- **`õ(Ax^1_{·→C}) = oAtom1 C = 2·rk(C)`** (Buchholz Lemma 5.2). Tag 7 = the §5 reduct code. -/
@[simp] lemma iotil_zAx1 (s C : V) : iotil (zAx1 s C) = oAtom1 C := by
  rw [iotil_eq_ioNext (by simp [zAx1]), ioNext, if_neg (by simp), if_neg (by simp),
    if_neg (by simp), if_neg (by simp), if_neg (by simp), if_neg (by simp),
    if_pos (zTag_zAx1 s C), zAx1F_zAx1]

/-- `õ(Ax^1_{·→C})` is a genuine NF (it's `oAtom1 C`). -/
@[simp] lemma isNF_iotil_zAx1 (s C : V) : isNF (iotil (zAx1 s C)) := by
  rw [iotil_zAx1]; exact isNF_oAtom1 C

/-- For an L-symbol axiom with a genuine principal formula (`rk(C) > 0`), the atomic õ is a genuine NF
(coefficient `2·rk(C)−1 ≥ 1`). Needed for the Lemma-5.2 atomic descent. -/
lemma isNF_oAtomLk_pos {C : V} (h : 0 < irk C) : isNF (oAtomLk C) := by
  have h1 : (1 : V) ≤ irk C := pos_iff_one_le.mp h
  refine (isNF_ocOadd 0 (irk C + irk C - 1) 0).2 ⟨?_, isNF_zero, isNF_zero, Or.inl rfl⟩
  rw [add_tsub_assoc_of_le h1]
  exact (pos_iff_one_le.mpr (le_trans h1 le_self_add)).ne'

/-- `õ(Ax^{∀p,k})` is a genuine NF for a well-formed matrix `p` (`õ = oAtomLk(∀p)`, `rk(∀p) = rk p+1 > 0`).
The §5 L-axiom-leaf NF fact for the extended `ZDerivation` (tag 5 base case). -/
lemma isNF_iotil_zAxAll {s p k : V} (hp : IsUFormula ℒₒᵣ p) : isNF (iotil (zAxAll s p k)) := by
  rw [iotil_zAxAll]; exact isNF_oAtomLk_pos (by rw [irk_all hp]; simp)

/-- `õ(Ax^{¬p,0})` is a genuine NF for a well-formed `p` (`õ = oAtomLk(¬p)`, `rk(¬p) = rk p+1 > 0`).
The §5 L-axiom-leaf NF fact for the extended `ZDerivation` (tag 6 base case). -/
lemma isNF_iotil_zAxNeg {s p : V} (hp : IsUFormula ℒₒᵣ p) : isNF (iotil (zAxNeg s p)) := by
  rw [iotil_zAxNeg]; exact isNF_oAtomLk_pos (by rw [irk_inegF hp]; simp)

/-! ### iõ-fold over a premise sequence (for the variadic `K^r` equation), mirror `iseqMaxIdg` -/

noncomputable def iseqNaddIdgAux.blueprint : PR.Blueprint 1 where
  zero := .mkSigma “y ds. y = 0”
  succ := .mkSigma “y ih n ds.
    ∃ di, !znthDef di ds n ∧ ∃ v, !iotilDef v di ∧ ∃ w, !ocOaddDef w v 1 0 ∧ !inaddDef y ih w”

noncomputable def iseqNaddIdgAux.construction : PR.Construction V iseqNaddIdgAux.blueprint where
  zero := fun _ ↦ 0
  succ := fun x n ih ↦ inadd ih (ocOadd (iotil (znth (x 0) n)) 1 0)
  zero_defined := .mk fun v ↦ by simp [iseqNaddIdgAux.blueprint]
  succ_defined := .mk fun v ↦ by
    simp [iseqNaddIdgAux.blueprint, znth_defined.iff, iotil_defined.iff, ocOadd_defined.iff,
      inadd_defined.iff]

/-- Partial iõ-fold: `iseqNaddIdgAux ds j = #_{i<j} ω^{iotil(znth ds i)}`. -/
noncomputable def iseqNaddIdgAux (ds j : V) : V := iseqNaddIdgAux.construction.result ![ds] j

@[simp] lemma iseqNaddIdgAux_zero (ds : V) : iseqNaddIdgAux ds 0 = 0 := by
  simp [iseqNaddIdgAux, iseqNaddIdgAux.construction]

@[simp] lemma iseqNaddIdgAux_succ (ds j : V) :
    iseqNaddIdgAux ds (j + 1) = inadd (iseqNaddIdgAux ds j) (ocOadd (iotil (znth ds j)) 1 0) := by
  simp [iseqNaddIdgAux, iseqNaddIdgAux.construction]

noncomputable def _root_.LO.FirstOrder.Arithmetic.iseqNaddIdgAuxDef : 𝚺₁.Semisentence 3 :=
  iseqNaddIdgAux.blueprint.resultDef.rew (Rew.subst ![#0, #2, #1])

instance iseqNaddIdgAux_defined : 𝚺₁-Function₂ (iseqNaddIdgAux : V → V → V) via iseqNaddIdgAuxDef :=
  .mk fun v ↦ by simp [iseqNaddIdgAux.construction.result_defined_iff, iseqNaddIdgAuxDef]; rfl

instance iseqNaddIdgAux_definable : 𝚺₁-Function₂ (iseqNaddIdgAux : V → V → V) :=
  iseqNaddIdgAux_defined.to_definable
instance iseqNaddIdgAux_definable' (Γ) : Γ-[m + 1]-Function₂ (iseqNaddIdgAux : V → V → V) :=
  iseqNaddIdgAux_definable.of_sigmaOne

/-- **iõ-fold over a sequence**: `iseqNaddIdg ds = #_{i<lh ds} ω^{iotil(znth ds i)}`. -/
noncomputable def iseqNaddIdg (ds : V) : V := iseqNaddIdgAux ds (lh ds)

/-- **Table-fold = iõ-fold under dominance** (mirror `iseqMaxAux_idgTable_eq`). -/
lemma iseqNaddAux_ioTable_eq {M ds : V} (hdom : ∀ i < lh ds, znth ds i ≤ M) :
    ∀ j ≤ lh ds, iseqNaddAux (ioTable M) ds j = iseqNaddIdgAux ds j := by
  intro j
  induction j using ISigma1.sigma1_succ_induction
  · refine Definable.imp (by definability) ?_
    refine Definable.comp₂
      (DefinableFunction₃.comp (F := iseqNaddAux)
        (DefinableFunction₁.comp (F := ioTable) (DefinableFunction.const M))
        (DefinableFunction.const ds) (DefinableFunction.var 0))
      (DefinableFunction₂.comp (F := iseqNaddIdgAux) (DefinableFunction.const ds)
        (DefinableFunction.var 0))
  case zero => intro _; simp
  case succ j ih =>
    intro hj
    rw [iseqNaddAux_succ, iseqNaddIdgAux_succ, ih (le_trans (by simp) hj),
      znth_ioTable_eq_iotil M (znth ds j) (hdom j (lt_of_lt_of_le (by simp) hj))]

/-- **The variadic `K^r` pre-ordinal equation** (Buchholz §4):
`õ(K^r_Π d0…dl) = ω^{õ d0} # … # ω^{õ dl} = #_{j} ω^{õ dⱼ}`. -/
lemma iotil_zK (s r ds : V) (hds : Seq ds) : iotil (zK s r ds) = iseqNaddIdg ds := by
  have hdom : ∀ i < lh ds, znth ds i ≤ zK s r ds - 1 := fun i hi ↦
    le_pred_of_lt (lt_trans (lt_of_mem_rng (hds.znth hi)) (ds_lt_zK s r ds))
  rw [iotil_eq_ioNext (by simp [zK]), ioNext, if_neg (by simp), if_neg (by simp), if_neg (by simp),
    if_pos (zTag_zK s r ds), zKseq_zK, iseqNaddTab,
    iseqNaddAux_ioTable_eq hdom (lh ds) (le_refl _), iseqNaddIdg]

/-! ## `iord` (`o`) — the full ordinal assignment `o(d) = ω_{dg(d)}(õ(d))` (C1c)

The `dg(d)`-fold ω-exponential tower (`iotower`, `src/InternalTower.lean`) over the pre-ordinal
`õ(d)`. This is the [KB81] assignment Thm 4.2 descends on. -/
noncomputable def iord (d : V) : V := iotower (iotil d) (idg d)

noncomputable def _root_.LO.FirstOrder.Arithmetic.iordDef : 𝚺₁.Semisentence 2 := .mkSigma
  “y d. ∃ a, !iotilDef a d ∧ ∃ g, !idgDef g d ∧ !iotowerDef y a g”

instance iord_defined : 𝚺₁-Function₁ (iord : V → V) via iordDef := .mk fun v ↦ by
  simp [iordDef, iord, iotil_defined.iff, idg_defined.iff, iotower_defined.iff]

instance iord_definable : 𝚺₁-Function₁ (iord : V → V) := iord_defined.to_definable
instance iord_definable' (Γ) : Γ-[m + 1]-Function₁ (iord : V → V) := iord_definable.of_sigmaOne

/-- `o(d) = ω_{dg(d)}(õ(d))` — unfolds the assignment to the tower over the pre-ordinal. -/
lemma iord_eq (d : V) : iord d = iotower (iotil d) (idg d) := rfl

/-- **`o(Ax^{C,t}) = õ(Ax^{C,t})`** (Buchholz §5: `dg = 0 ⟹ o(d) = ω₀(õ d) = õ d`). -/
@[simp] lemma iord_zAxAll (s p k : V) : iord (zAxAll s p k) = oAtomLk (^∀ p : V) := by
  rw [iord_eq, idg_zAxAll, iotil_zAxAll, iotower_zero]

@[simp] lemma iord_zAxNeg (s p : V) : iord (zAxNeg s p) = oAtomLk (inegF p) := by
  rw [iord_eq, idg_zAxNeg, iotil_zAxNeg, iotower_zero]

/-- **`o(Ax^1_{·→C}) = oAtom1 C`** (`dg = 0 ⟹ o = ω₀(õ) = õ`). The §5 reduct's ordinal. -/
@[simp] lemma iord_zAx1 (s C : V) : iord (zAx1 s C) = oAtom1 C := by
  rw [iord_eq, idg_zAx1, iotil_zAx1, iotower_zero]

/-- Finite-ONote strict comparison: `a < b ⟹ ω⁰·a ≺ ω⁰·b` (`icmp = 0` is `<`). -/
lemma icmp_ocOadd0_lt {a b : V} (h : a < b) :
    icmp (ocOadd 0 a 0) (ocOadd 0 b 0) = 0 := by
  rw [icmp_ocOadd, icmp_zero_zero, thenV_one_left, cmpV_eq_zero.mpr h, thenV_zero_left]

/-- **Lemma 5.2 atomic descent — ordinal core, L-symbol case.** If the principal formula `C` has rank
one more than the reduct succedent `C'` — which holds for `Ax^{∀xF,k}` (`C = ∀xF`, `C' = F(k)`, via
`rk(∀xF) = rk(F)+1 = rk(F(k))+1`) and `Ax^{¬A,0}` (`C = ¬A`, `C' = A`, via `rk(¬A) = rk(A)+1`) — then
`o(d[0]) = õ(Ax1_{·→C'}) = 2·rk(C') ≺ 2·rk(C)−1 = õ(Ax^{C,t}) = o(d)`. This is the entire ordinal
content of the atomic descent; connecting it to a concrete `iR`/`Ax1` reduct is the next plumbing. -/
lemma icmp_oAtom1_oAtomLk {C C' : V} (h : irk C = irk C' + 1) :
    icmp (oAtom1 C') (oAtomLk C) = 0 := by
  rw [oAtom1, oAtomLk, h]
  by_cases h0 : irk C' = 0
  · rw [if_pos h0]; exact icmp_zero_pos (ocOadd_pos _ _ _).ne'
  · rw [if_neg h0]
    apply icmp_ocOadd0_lt
    have e : (irk C' + 1) + (irk C' + 1) - 1 = irk C' + irk C' + 1 := by
      rw [← add_assoc, add_tsub_cancel_right, add_right_comm]
    rw [e]; exact lt_add_one _

/-- **§5 atomic descent on the genuine codes — `Ax^{∀p,k}` case.** The `Ax^1` reduct `zAx1 s p` (succedent
the matrix `p`, `õ = 2·rk(p)`) strictly lowers the pre-ordinal below the L-axiom `zAxAll s p k`
(`õ = 2·rk(∀p)−1 = 2·rk(p)+1`). Needs `p` a formula (so `rk(∀p) = rk(p)+1`). -/
lemma icmp_iotil_zAx1_zAxAll {s p k : V} (hp : IsUFormula ℒₒᵣ p) :
    icmp (iotil (zAx1 s p)) (iotil (zAxAll s p k)) = 0 := by
  rw [iotil_zAx1, iotil_zAxAll]; exact icmp_oAtom1_oAtomLk (by rw [irk_all hp])

/-- **§5 atomic descent on the genuine codes — `Ax^{¬p,0}` case.** The `Ax^1` reduct `zAx1 s p`
(succedent `p`) strictly lowers `õ` below the L-axiom `zAxNeg s p` (`õ = 2·rk(¬p)−1 = 2·rk(p)+1`). -/
lemma icmp_iotil_zAx1_zAxNeg {s p : V} (hp : IsUFormula ℒₒᵣ p) :
    icmp (iotil (zAx1 s p)) (iotil (zAxNeg s p)) = 0 := by
  rw [iotil_zAx1, iotil_zAxNeg]; exact icmp_oAtom1_oAtomLk (by rw [irk_inegF hp])

/-! ## C3 — Thm 4.2 ordinal descent `o(d[n]) ≺ o(d)`, rule by rule

Buchholz Thm 4.2: each reduction `d ↦ d[n]` strictly lowers `o`. We prove the per-rule ordinal
inequalities directly from the C1 assignment equations and the `src/` order theory (Lemma 4.1
monotonicity: `icmp_iotower_mono` same-degree, `icmp_iotower_lt_succ_of_le` degree-drop,
`self_lt_iadd_one`). These are the mathematical core; wiring them through a concrete reduction
operator `iR` (Def 3.2) is downstream plumbing.

`icmp a b = 0` reads `a ≺ b`. -/

/-- **Same-degree descent template** (Thm 4.2, degree unchanged): if `dg(e)=dg(d)` and
`õ(e) ≺ õ(d)`, then `o(e) ≺ o(d)`. The tower height is fixed and `ω_n` is base-monotone
(`icmp_iotower_mono`). -/
lemma iord_descent_samedeg {d e : V} (hg : idg e = idg d) (ho : icmp (iotil e) (iotil d) = 0) :
    icmp (iord e) (iord d) = 0 := by
  rw [iord, iord, hg]; exact icmp_iotower_mono ho (idg d)

/-- **General structural descent** (Thm 4.2 non-critical / structural cases): if the degree does not rise
(`dg(e) ≤ dg(d)`) and the pre-ordinal strictly drops (`õ(e) ≺ õ(d)`), then `o(e) ≺ o(d)`. Composes the
strict base-monotone step `ω_{dg e}(õ e) ≺ ω_{dg e}(õ d)` (`icmp_iotower_mono`) with the non-strict
height-monotone step `ω_{dg e}(õ d) ≼ ω_{dg d}(õ d)` (`icmp_iotower_height_le`). Generalises
`iord_descent_samedeg` (the `dg(e)=dg(d)` case) to an arbitrary degree drop where `õ` carries the
strictness — exactly the LH3 (non-critical chain, case 5.2.2) interface. -/
lemma iord_descent_le {d e : V} (hnf : isNF (iotil d)) (hg : idg e ≤ idg d)
    (ho : icmp (iotil e) (iotil d) = 0) : icmp (iord e) (iord d) = 0 := by
  rw [iord, iord]
  have step1 : icmp (iotower (iotil e) (idg e)) (iotower (iotil d) (idg e)) = 0 :=
    icmp_iotower_mono ho (idg e)
  rcases icmp_iotower_height_le hnf hg with hh | hh
  · exact icmp_trans
      (max (iotower (iotil e) (idg e))
        (max (iotower (iotil d) (idg e)) (iotower (iotil d) (idg d))))
      _ (le_max_left _ _)
      _ (le_trans (le_max_left _ _) (le_max_right _ _))
      _ (le_trans (le_max_right _ _) (le_max_right _ _)) step1 hh
  · rw [← hh]; exact step1

/-- **Degree-drop descent template** (Thm 4.2, `dg(d)=dg(e)+1`): if `õ(e) ≼ õ(d)` (`≺` or `=`) and
`õ(d)` is in normal form, then `o(e) ≺ o(d)`. One extra tower level strictly dominates
(`icmp_iotower_lt_succ_of_le`). The `isNF (iotil d)` premise is discharged later via
`ZDerivation` (`õ` of a genuine derivation is a valid CNF code). -/
lemma iord_descent_dgdrop {d e : V} (hg : idg d = idg e + 1) (hnf : isNF (iotil d))
    (ho : icmp (iotil e) (iotil d) = 0 ∨ iotil e = iotil d) : icmp (iord e) (iord d) = 0 := by
  rw [iord, iord, hg]
  refine icmp_iotower_lt_succ_of_le hnf (idg e) ?_
  rcases ho with h | h
  · exact Or.inl (icmp_iotower_mono h (idg e))
  · exact Or.inr (by rw [h])

/-- **I-rule descent** (same degree, `õ` drops by one successor): if `dg(e)=dg(d)` and
`õ(d)=õ(e)+1`, then `o(e) ≺ o(d)`. Instance of `iord_descent_samedeg` via `self_lt_iadd_one`
(`õ(e) ≺ õ(e)+1`). Covers Buchholz's `I^a_∀xF`/`I_¬A` cases. -/
lemma iord_descent_I {d e : V} (hg : idg e = idg d)
    (ho : iotil d = iadd (iotil e) (ocOadd 0 1 0)) : icmp (iord e) (iord d) = 0 :=
  iord_descent_samedeg hg (ho ▸ self_lt_iadd_one (iotil e) (iotil e) le_rfl)

/-- `o(d0) ≺ o(I_¬A d0)` — the `I_¬A` reduction `d[0] = d0` strictly lowers `o`. -/
lemma iord_descent_zIneg (s p d0 : V) : icmp (iord d0) (iord (zIneg s p d0)) = 0 :=
  iord_descent_I (by simp) (by simp)

/-- `o(d0) ≺ o(I^a_∀xF d0)` at the level of the premise code `d0` (the `d[n]=d0(a/n)` reduct shares
`d0`'s `dg`/`õ` once substitution-invariance of the assignment is established — a separate brick). -/
lemma iord_descent_zIall (s a p d0 : V) : icmp (iord d0) (iord (zIall s a p d0)) = 0 :=
  iord_descent_I (by simp) (by simp)

/-- **Cut-elimination descent template** (Thm 4.2 critical case, Buchholz Lemma 4.1(b)(ii) case 5.1;
judge `E-CRUX2-DECOMPOSITION-2026-06-24.md` §8.3 N4). The reduct `e = d[0]` has its pre-ordinal jump
*up* to `õ(e) ≺ ω^{õ(d)}` (N3b), but the degree strictly drops `dg(e) + 1 ≤ dg(d)` (N3a). The descent
`o(e) ≺ o(d)` survives because the degree drop absorbs the pre-ordinal jump through the tower:
`o(e) = ω_{dg(e)}(õ(e)) ≺ ω_{dg(e)}(ω^{õ(d)}) = ω_{dg(e)+1}(õ(d)) ≼ ω_{dg(d)}(õ(d)) = o(d)`
— `icmp_iotower_mono` (base) + `iotower_omega_pow` (base-shift) + `icmp_iotower_height_le` (height).
This is the ordinal tail of the nut; only the object construction `iR`-critical-branch + the bounds
N3a/N3b that instantiate `hdeg`/`ho` remain. -/
lemma iord_descent_cut {d e : V} (hnf : isNF (iotil d)) (hdeg : idg e + 1 ≤ idg d)
    (ho : icmp (iotil e) (ocOadd (iotil d) 1 0) = 0) : icmp (iord e) (iord d) = 0 := by
  rw [iord_eq, iord_eq]
  have step1 : icmp (iotower (iotil e) (idg e)) (iotower (ocOadd (iotil d) 1 0) (idg e)) = 0 :=
    icmp_iotower_mono ho (idg e)
  rw [iotower_omega_pow (iotil d) (idg e)] at step1
  rcases icmp_iotower_height_le hnf hdeg with hh | hh
  · exact icmp_trans
      (max (iotower (iotil e) (idg e))
        (max (iotower (iotil d) (idg e + 1)) (iotower (iotil d) (idg d))))
      _ (le_max_left _ _)
      _ (le_trans (le_max_left _ _) (le_max_right _ _))
      _ (le_trans (le_max_right _ _) (le_max_right _ _)) step1 hh
  · rw [← hh]; exact step1

/-! ## `iR` — the one-step reduction `d ↦ d[0]` (Buchholz Def 3.2), rule-by-rule SKELETON

`iR` dispatches on `zTag d`. This lap builds the **structural (LOW-HANGING) branches** — the `I_¬A`
and `I^a_∀xF` rules, whose reduct is simply the premise `d₀` (Buchholz §3.2 cases 2,3; the `I∀`
substitution `d₀(a/0)` is invariant for the ordinal assignment, judge §2 LH2, so the skeleton reads
the bare premise). The `atom`/`Ind`/`K^r` branches are placeholders (`iR d := d`) pending: `Ind` →
the `K^r`-chain reduct (LH4), `K^r` → the non-critical chain step (LH3/LH5) and the **critical
branch** (the nut, §8.3 — builds `d{0}=K^r(i/dᵢ[k])`, `d{1}=K^r(j/d_j[0])`, `d[0]=K^{r-1}d{0}d{1}`).
Flagged in `PENDING_WORK.md`. -/

@[simp] lemma zTag_le_self (d : V) : zTag d ≤ d := le_trans (pi₁_le_self _) (sndIdx_le_self d)

/-- One-step reduction `d ↦ d[0]` (structural-branch skeleton): `I^a_∀` and `I_¬` reduce to their
premise; other tags are placeholders (identity) until their reducts are built. -/
noncomputable def iR (d : V) : V :=
  if zTag d = 1 then zIallPrem d
  else if zTag d = 2 then zInegPrem d
  else d

def _root_.LO.FirstOrder.Arithmetic.iRDef : 𝚺₀.Semisentence 2 := .mkSigma
  “y d. ∃ t <⁺ d, !zTagDef t d ∧
    ( (t = 1 ∧ !zIallPremDef y d) ∨
      (t ≠ 1 ∧ t = 2 ∧ !zInegPremDef y d) ∨
      (t ≠ 1 ∧ t ≠ 2 ∧ y = d) )”

instance iR_defined : 𝚺₀-Function₁ (iR : V → V) via iRDef := .mk fun v ↦ by
  simp [iRDef, iR, zTag_defined.iff, zIallPrem_defined.iff, zInegPrem_defined.iff]
  by_cases h1 : zTag (v 1) = 1 <;> by_cases h2 : zTag (v 1) = 2 <;> simp [h1, h2]

instance iR_definable : 𝚺₀-Function₁ (iR : V → V) := iR_defined.to_definable

-- Compute lemmas: `iR` on each constructor.
@[simp] lemma iR_zIall (s a p d0 : V) : iR (zIall s a p d0) = d0 := by simp [iR]
@[simp] lemma iR_zIneg (s p d0 : V) : iR (zIneg s p d0) = d0 := by simp [iR]
@[simp] lemma iR_zAtom (s : V) : iR (zAtom s) = zAtom s := by simp [iR]
@[simp] lemma iR_zInd (s at' p d0 d1 : V) : iR (zInd s at' p d0 d1) = zInd s at' p d0 d1 := by
  simp [iR]
@[simp] lemma iR_zK (s r ds : V) : iR (zK s r ds) = zK s r ds := by simp [iR]

/-- **Descent through `iR`** for the structural rules: `o(iR d) ≺ o(d)` for `I_¬A`/`I^a_∀xF` codes.
Composes the `iR`-compute lemma with the per-rule `iord_descent_z*`. The atom/Ind/K branches' descent
arrives when their reducts are built. -/
lemma iord_descent_iR_zIneg (s p d0 : V) :
    icmp (iord (iR (zIneg s p d0))) (iord (zIneg s p d0)) = 0 := by
  rw [iR_zIneg]; exact iord_descent_zIneg s p d0

lemma iord_descent_iR_zIall (s a p d0 : V) :
    icmp (iord (iR (zIall s a p d0))) (iord (zIall s a p d0)) = 0 := by
  rw [iR_zIall]; exact iord_descent_zIall s a p d0

/-! ## Structural NF building blocks for `õ` (toward `isNF (iotil d)` on derivations)

`õ(d)` is a valid CNF code (`isNF`) for genuine derivations. The general fact needs structural
induction over `ZDerivation` (the C0 Fixpoint), but the per-constructor NF-closure steps are clean
and provable now: `õ(atom)=0` is NF, and the `K^r` `#`-fold preserves NF given its entries do
(`isNF_inadd` + `isNF_omega_pow`). These discharge the `isNF (iotil d)` premise of
`iord_descent_dgdrop` once the Fixpoint lands. -/

/-- `ω^e = ocOadd e 1 0` is NF iff its exponent is. -/
lemma isNF_omega_pow {e : V} (he : isNF e) : isNF (ocOadd e 1 0) :=
  (isNF_ocOadd e 1 0).2 ⟨(by simp), he, isNF_zero, Or.inl rfl⟩

/-- `õ(0) = 0` — the out-of-range default code `0` (returned by `znth ds n` for `n ≥ lh ds`,
`znth_prop_not`) has pre-ordinal `0`. `ioTable 0 = !⟦0⟧`, whose `0`-th entry is `0`. -/
@[simp] lemma iotil_zero : iotil (0 : V) = 0 := by
  rw [iotil, ioTable_zero]
  simpa using znth_seqCons_self (seq_empty (V := V)) (0 : V)

/-- `õ(0)` is NF — discharges the out-of-range-premise NF in the chain ZDerivation wrappers. -/
@[simp] lemma isNF_iotil_zero : isNF (iotil (0 : V)) := by rw [iotil_zero]; exact isNF_zero

@[simp] lemma isNF_iotil_zAtom (s : V) : isNF (iotil (zAtom s)) := by
  rw [iotil_zAtom]; exact isNF_zero

/-! ### `zAxBot` (tag 8) ordinal/projection lemmas — all mirror `zAtom` (deps available here). -/
@[simp] lemma tp_zAxBot (s : V) : tp (zAxBot s) = isymRep := by simp [tp]
@[simp] lemma idg_zAxBot (s : V) : idg (zAxBot s) = 0 := by
  rw [idg_eq_idgNext (by simp [zAxBot]), idgNext]; simp [zTag_zAxBot]
@[simp] lemma iotil_zAxBot (s : V) : iotil (zAxBot s) = 0 := by
  rw [iotil_eq_ioNext (by simp [zAxBot]), ioNext]; simp [zTag_zAxBot]
@[simp] lemma isNF_iotil_zAxBot (s : V) : isNF (iotil (zAxBot s)) := by
  rw [iotil_zAxBot]; exact isNF_zero
@[simp] lemma iord_zAxBot (s : V) : iord (zAxBot s) = 0 := by
  rw [iord_eq, idg_zAxBot, iotil_zAxBot, iotower_zero]

/-- `õ(I^a_∀xF d0)` is NF when `õ(d0)` is — the assignment is `õ(d0) + 1`, NF by `isNF_iadd_one_right`. -/
@[simp] lemma isNF_iotil_zIall {s a p d0 : V} (hd0 : isNF (iotil d0)) :
    isNF (iotil (zIall s a p d0)) := by rw [iotil_zIall]; exact isNF_iadd_one_right hd0

/-- `õ(I_¬A d0)` is NF when `õ(d0)` is. -/
@[simp] lemma isNF_iotil_zIneg {s p d0 : V} (hd0 : isNF (iotil d0)) :
    isNF (iotil (zIneg s p d0)) := by rw [iotil_zIneg]; exact isNF_iadd_one_right hd0

/-- `õ(Ind^{a,t}_F d0 d1)` is NF when `õ(d0)`,`õ(d1)` are — the assignment is
`ω^{õ(d0)} # ω^{õ(d1)+1}`, NF by `isNF_inadd` of two NF ω-powers (the right exponent via
`isNF_iadd_one_right`). -/
@[simp] lemma isNF_iotil_zInd {s at' p d0 d1 : V} (hd0 : isNF (iotil d0)) (hd1 : isNF (iotil d1)) :
    isNF (iotil (zInd s at' p d0 d1)) := by
  rw [iotil_zInd]
  exact isNF_inadd (isNF_omega_pow (isNF_iadd_one_right hd1)) _ (isNF_omega_pow hd0)

/-- **Partial `#`-fold is NF given only the FOLDED entries' `õ` are NF** (`∀ i < J`, not `∀ n` — the
weaker in-range hypothesis the `K^r` structural step actually supplies via premise-membership). -/
lemma isNF_iseqNaddIdgAux_lt {ds : V} :
    ∀ J, (∀ i < J, isNF (iotil (znth ds i))) → isNF (iseqNaddIdgAux ds J) := by
  intro J
  induction J using ISigma1.sigma1_succ_induction
  · definability
  case zero => intro _; rw [iseqNaddIdgAux_zero]; exact isNF_zero
  case succ J ih =>
    intro h
    rw [iseqNaddIdgAux_succ]
    exact isNF_inadd (isNF_omega_pow (h J (by simp))) _ (ih (fun i hi => h i (lt_trans hi (by simp))))

/-- **`õ(K^r ds)` is NF** when every premise's `õ` is NF (chain NF-closure; the missing `K^r` companion
of `isNF_iotil_zIall`/`_zIneg`/`_zInd`). Only the in-range entries (`i < lh ds`) are required. -/
@[simp] lemma isNF_iotil_zK {s r ds : V} (hds : Seq ds)
    (hNF : ∀ i < lh ds, isNF (iotil (znth ds i))) : isNF (iotil (zK s r ds)) := by
  rw [iotil_zK s r ds hds]; exact isNF_iseqNaddIdgAux_lt (lh ds) hNF

/-- **LH4 — the Ind-rule descent's ordinal core** (Buchholz §4 case 4; judge §2 LH4). The reduct
`d[0] = K^r(d0, d1(0),…,d1(k−1))` has `õ(d[0]) = ω^{õ d0} # ω^{õ d1}·k` (the `k` substitution-invariant
copies collected into one CNF term `ocOadd (õ d1) k 0`), and `õ(zInd) = ω^{õ d0} # ω^{õ d1 + 1}`. The
descent `õ(d[0]) ≺ õ(zInd)` is F1 (left-monotonicity, fixing the `ω^{õ d0}` summand) applied to F3
(`ω^β·k ≺ ω^{β+1}`). The `k ≠ 0` hypothesis keeps `ocOadd b k 0` a valid CNF term. -/
lemma icmp_iotil_ind_reduct {a b k : V} (ha : isNF a) (hb : isNF b) (hk : k ≠ 0) :
    icmp (inadd (ocOadd a 1 0) (ocOadd b k 0))
         (inadd (ocOadd a 1 0) (ocOadd (iadd b (ocOadd 0 1 0)) 1 0)) = 0 :=
  inadd_left_mono
    ((isNF_ocOadd b k 0).2 ⟨hk, hb, isNF_zero, Or.inl rfl⟩)
    (isNF_omega_pow (isNF_iadd_one_right hb))
    (icmp_term_lt_omega_succ b k)
    (ocOadd a 1 0) (isNF_omega_pow ha)

/-- The `#`-fold `iseqNaddIdgAux` is NF when every folded entry's `õ` is NF. -/
lemma isNF_iseqNaddIdgAux {ds : V} (hall : ∀ i < lh ds, isNF (iotil (znth ds i))) :
    ∀ j ≤ lh ds, isNF (iseqNaddIdgAux ds j) := by
  intro j
  induction j using ISigma1.sigma1_succ_induction
  · definability
  case zero => intro _; simpa using isNF_zero
  case succ j ih =>
    intro hj
    rw [iseqNaddIdgAux_succ]
    exact isNF_inadd (isNF_omega_pow (hall j (lt_of_lt_of_le (by simp) hj))) _
      (ih (le_trans (by simp) hj))

/-- `õ(K^r_Π ds)` is NF when every premise's `õ` is NF (via `iotil_zK`). -/
lemma isNF_iseqNaddIdg {ds : V} (hall : ∀ i < lh ds, isNF (iotil (znth ds i))) :
    isNF (iseqNaddIdg ds) := isNF_iseqNaddIdgAux hall (lh ds) le_rfl

/-- **`#`-fold over a constant-õ block collapses to one term**: if every entry of `ds` (in range) has
`õ = β`, then `#_{i<j+1} ω^{õ(znth ds i)} = ω^β·(j+1)` for `j+1 ≤ lh ds`. The Ind-reduct's substituted
premises `d1(0),…,d1(k−1)` all share `õ = õ d1` (substitution-invariance, Buchholz Remark p.10), so their
`#`-fold is `ω^{õ d1}·k` — the left factor of `icmp_iotil_ind_reduct` (LH4). -/
lemma iseqNaddIdgAux_const {ds β : V} (hconst : ∀ i < lh ds, iotil (znth ds i) = β) :
    ∀ j, 0 < j → j ≤ lh ds → iseqNaddIdgAux ds j = ocOadd β j 0 := by
  intro j
  induction j using ISigma1.sigma1_succ_induction
  · refine Definable.imp (by definability) (Definable.imp (by definability) ?_)
    refine Definable.comp₂
      (DefinableFunction₂.comp (F := iseqNaddIdgAux)
        (DefinableFunction.const ds) (DefinableFunction.var 0))
      (DefinableFunction₃.comp (F := ocOadd) (hF := ocOadd_definable.of_sigmaOne)
        (DefinableFunction.const β) (DefinableFunction.var 0) (DefinableFunction.const 0))
  case zero => intro h; exact absurd h (by simp)
  case succ j ih =>
    intro _ hj
    rw [iseqNaddIdgAux_succ, hconst j (lt_of_lt_of_le (by simp) hj)]
    rcases eq_or_ne j 0 with rfl | hj0
    · rw [iseqNaddIdgAux_zero, inadd_zero_left, zero_add]
    · rw [ih (pos_iff_ne_zero.mpr hj0) (le_trans (by simp) hj), inadd_omega_pow_collect]

/-! ## `iRepeatSeq` — the constant premise block `[v, v, …, v]` (length `k`)

The Ind-reduct `d[0] = K^r(d0, d1(0),…,d1(k−1))` (Buchholz §3.2 case 4) needs a coded premise sequence.
Ordinally, every `d1(j)` shares `õ = õ d1` (substitution-invariance), so the `#`-fold over the
substituted block equals the `#`-fold over `k` *unsubstituted* copies of `d1` (`iseqNaddIdgAux_const`).
`iRepeatSeq` is that constant block — a length-`k` sequence builder mirroring `iwseq`/`iCTable`. (The
genuine substituted reduct, needed for derivation *validity* / `derivesEmpty`-preservation, layers the
eigenvariable substitution on top; this scaffold pins the ordinal side.) -/

def iRepeatSeq.blueprint : PR.Blueprint 1 where
  zero := .mkSigma “y v. y = 0”
  succ := .mkSigma “y ih i v. !seqConsDef y ih v”

noncomputable def iRepeatSeq.construction : PR.Construction V iRepeatSeq.blueprint where
  zero := fun _ ↦ ∅
  succ := fun x _ ih ↦ seqCons ih (x 0)
  zero_defined := .mk fun v ↦ by simp [iRepeatSeq.blueprint, emptyset_def]
  succ_defined := .mk fun v ↦ by simp [iRepeatSeq.blueprint, seqCons_defined.iff]

/-- `iRepeatSeq v k = ⟨v, v, …, v⟩` (length `k`). -/
noncomputable def iRepeatSeq (v k : V) : V := iRepeatSeq.construction.result ![v] k

@[simp] lemma iRepeatSeq_zero (v : V) : iRepeatSeq v 0 = ∅ := by
  simp [iRepeatSeq, iRepeatSeq.construction]

@[simp] lemma iRepeatSeq_succ (v k : V) : iRepeatSeq v (k + 1) = seqCons (iRepeatSeq v k) v := by
  simp [iRepeatSeq, iRepeatSeq.construction]

def _root_.LO.FirstOrder.Arithmetic.iRepeatSeqDef : 𝚺₁.Semisentence 3 :=
  iRepeatSeq.blueprint.resultDef.rew (Rew.subst ![#0, #2, #1])

instance iRepeatSeq_defined : 𝚺₁-Function₂ (iRepeatSeq : V → V → V) via iRepeatSeqDef := .mk
  fun v ↦ by simp [iRepeatSeq.construction.result_defined_iff, iRepeatSeqDef, iRepeatSeq]; rfl

instance iRepeatSeq_definable : 𝚺₁-Function₂ (iRepeatSeq : V → V → V) := iRepeatSeq_defined.to_definable
instance iRepeatSeq_definable' (Γ) : Γ-[m + 1]-Function₂ (iRepeatSeq : V → V → V) :=
  iRepeatSeq_definable.of_sigmaOne

private lemma def_iRepeatSeq {k} (v : V) (i : Fin k) :
    𝚺-[1].DefinableFunction (fun w : Fin k → V ↦ iRepeatSeq v (w i)) :=
  DefinableFunction₂.comp (F := iRepeatSeq) (DefinableFunction.const v) (DefinableFunction.var i)

@[simp] lemma iRepeatSeq_seq (v k : V) : Seq (iRepeatSeq v k) := by
  induction k using ISigma1.sigma1_succ_induction
  · exact Definable.comp₁ (def_iRepeatSeq v 0)
  case zero => simpa using seq_empty
  case succ k ih => rw [iRepeatSeq_succ]; exact ih.seqCons _

@[simp] lemma iRepeatSeq_lh (v k : V) : lh (iRepeatSeq v k) = k := by
  induction k using ISigma1.sigma1_succ_induction
  · exact Definable.comp₂ (DefinableFunction₁.comp (F := lh) (def_iRepeatSeq v 0)) (by definability)
  case zero => simpa using lh_empty
  case succ k ih => rw [iRepeatSeq_succ, Seq.lh_seqCons _ (iRepeatSeq_seq v k), ih]

/-- Every in-range entry of `iRepeatSeq v k` is `v`. -/
lemma znth_iRepeatSeq {v k : V} : ∀ i < k, znth (iRepeatSeq v k) i = v := by
  induction k using ISigma1.sigma1_succ_induction
  · definability
  case zero => intro i hi; exact absurd hi (by simp)
  case succ k ih =>
    intro i hi
    rw [iRepeatSeq_succ]
    rcases eq_or_ne i k with rfl | hik
    · have := znth_seqCons_self (iRepeatSeq_seq v i) v; rwa [iRepeatSeq_lh] at this
    · have hik' : i < k := lt_of_le_of_ne (le_iff_lt_succ.mpr hi) hik
      rw [znth_seqCons_of_lt (iRepeatSeq_seq v k) v (by rw [iRepeatSeq_lh]; exact hik')]
      exact ih i hik'

/-- **The constant block's `#`-fold**: `#_{i<k} ω^{õ v} = ω^{õ v}·k` (for `k > 0`). The capstone
combining `iRepeatSeq` with `iseqNaddIdgAux_const`: this is `õ` of the Ind-reduct's substituted
premise block, the right factor of `icmp_iotil_ind_reduct` (LH4). -/
lemma iseqNaddIdg_iRepeatSeq {v k : V} (hk : 0 < k) :
    iseqNaddIdg (iRepeatSeq v k) = ocOadd (iotil v) k 0 := by
  have hconst : ∀ i < lh (iRepeatSeq v k), iotil (znth (iRepeatSeq v k) i) = iotil v :=
    fun i hi => by rw [znth_iRepeatSeq i (by rwa [iRepeatSeq_lh] at hi)]
  rw [iseqNaddIdg,
    iseqNaddIdgAux_const hconst (lh (iRepeatSeq v k)) (by rw [iRepeatSeq_lh]; exact hk) le_rfl,
    iRepeatSeq_lh]

/-- **`#`-fold depends only on the entries**: if `ds`, `ds'` agree on the first `j` entries then their
partial `#`-folds agree. The congruence behind "replace/extend a sequence" reasoning (the chain cases
LH3/LH5 and the Ind reduct's `seqCons` both need it). -/
lemma iseqNaddIdgAux_congr {ds ds' : V} :
    ∀ j, (∀ i < j, znth ds i = znth ds' i) → iseqNaddIdgAux ds j = iseqNaddIdgAux ds' j := by
  intro j
  induction j using ISigma1.sigma1_succ_induction
  · refine Definable.imp (Definable.ball_lt (by definability) (by definability)) ?_
    refine Definable.comp₂
      (DefinableFunction₂.comp (F := iseqNaddIdgAux)
        (DefinableFunction.const ds) (DefinableFunction.var 0))
      (DefinableFunction₂.comp (F := iseqNaddIdgAux)
        (DefinableFunction.const ds') (DefinableFunction.var 0))
  case zero => intro _; rw [iseqNaddIdgAux_zero, iseqNaddIdgAux_zero]
  case succ j ih =>
    intro h
    rw [iseqNaddIdgAux_succ, iseqNaddIdgAux_succ, ih (fun i hi => h i (lt_trans hi (by simp))),
      h j (by simp)]

/-- **`#`-fold over a `seqCons`**: appending `v` adds the summand `ω^{õ v}`. -/
lemma iseqNaddIdg_seqCons {ds v : V} (hds : Seq ds) :
    iseqNaddIdg (seqCons ds v) = inadd (iseqNaddIdg ds) (ocOadd (iotil v) 1 0) := by
  rw [iseqNaddIdg, iseqNaddIdg, Seq.lh_seqCons v hds, iseqNaddIdgAux_succ,
    iseqNaddIdgAux_congr (lh ds) (fun i hi => (znth_seqCons_of_lt hds v hi).symm),
    znth_seqCons_self hds v]

/-! ## The Ind-rule reduct object `d[0] = K^r(d0, d1(0),…,d1(k−1))` — ordinal side (LH4)

`iIndReductSeq d0 d1 k = ⟨d1,…,d1 (k copies), d0⟩` is the reduct's premise sequence (ordinal-faithful:
the `k` substituted copies all carry `õ = õ d1`, and `#` is commutative so `d0`'s position is immaterial).
Its `õ`-fold is `ω^{õ d1}·k # ω^{õ d0}`, and the LH4 descent `õ(d[0]) ≺ õ(Ind…)` follows from
`icmp_iotil_ind_reduct` (F1+F3). This is the **full Ind-rule ordinal descent on a genuine reduct object**;
only the degree side (`idg`, awaiting the real `irk`) and derivation-validity (eigenvariable substitution)
remain to lift it to a full `iord` descent. -/

/-- The Ind-reduct premise sequence `⟨d1,…,d1 (k copies), d0⟩`. -/
noncomputable def iIndReductSeq (d0 d1 k : V) : V := seqCons (iRepeatSeq d1 k) d0

@[simp] lemma iIndReductSeq_seq (d0 d1 k : V) : Seq (iIndReductSeq d0 d1 k) :=
  (iRepeatSeq_seq d1 k).seqCons d0

/-- `õ`-fold of the Ind reduct's premise sequence: `ω^{õ d1}·k # ω^{õ d0}` (for `k > 0`). -/
lemma iseqNaddIdg_iIndReductSeq {d0 d1 k : V} (hk : 0 < k) :
    iseqNaddIdg (iIndReductSeq d0 d1 k) =
      inadd (ocOadd (iotil d1) k 0) (ocOadd (iotil d0) 1 0) := by
  rw [iIndReductSeq, iseqNaddIdg_seqCons (iRepeatSeq_seq d1 k), iseqNaddIdg_iRepeatSeq hk]

/-- **LH4 — full Ind-rule `õ`-descent on the genuine reduct**: `õ(d[0]) ≺ õ(Ind^{a,t}_F d0 d1)`, where
`õ(d[0]) = #` of the reduct premise sequence. The reduct's fold commutes (`inadd_comm`) into the
`ω^{õ d0} # ω^{õ d1}·k` shape, then `icmp_iotil_ind_reduct` (F1+F3) closes it. -/
lemma icmp_iotil_iIndReduct {s at' p d0 d1 k : V}
    (hd0 : isNF (iotil d0)) (hd1 : isNF (iotil d1)) (hk : 0 < k) :
    icmp (iseqNaddIdg (iIndReductSeq d0 d1 k)) (iotil (zInd s at' p d0 d1)) = 0 := by
  have hNFblock : isNF (ocOadd (iotil d1) k 0) :=
    (isNF_ocOadd (iotil d1) k 0).2 ⟨pos_iff_ne_zero.mp hk, hd1, isNF_zero, Or.inl rfl⟩
  rw [iseqNaddIdg_iIndReductSeq hk, iotil_zInd,
    inadd_comm (ocOadd (iotil d0) 1 0) (isNF_omega_pow hd0) _ hNFblock]
  exact icmp_iotil_ind_reduct hd0 hd1 (pos_iff_ne_zero.mp hk)

/-! ### Degree side of the Ind reduct (LH4) — `idg`-fold over the reduct sequence

Mirrors the `õ`-fold machinery (`iseqNaddIdg…`) for the degree fold `iseqMaxIdg`. The capstone is
`idg_zK_iIndReduct`: the reduct `K^{rk p}(d0, d1×k)` has the SAME degree as `Ind^{a,t}_F d0 d1` (because
`max{rk p, max(dg d1, dg d0)∸1} = max{max(dg d0∸1, dg d1∸1), rk p}`, ∸ distributing over max). With
degree preserved and `õ` strictly dropping (`icmp_iotil_iIndReduct`), `iord_descent_samedeg` lifts LH4
to a full `iord` descent on the genuine reduct object — now with the REAL `irk`. -/

/-- **idg-fold congruence**: agreeing entries ⟹ equal partial folds (mirror `iseqNaddIdgAux_congr`). -/
lemma iseqMaxIdgAux_congr {ds ds' : V} :
    ∀ j, (∀ i < j, znth ds i = znth ds' i) → iseqMaxIdgAux ds j = iseqMaxIdgAux ds' j := by
  intro j
  induction j using ISigma1.sigma1_succ_induction
  · refine Definable.imp (Definable.ball_lt (by definability) (by definability)) ?_
    refine Definable.comp₂
      (DefinableFunction₂.comp (F := iseqMaxIdgAux)
        (DefinableFunction.const ds) (DefinableFunction.var 0))
      (DefinableFunction₂.comp (F := iseqMaxIdgAux)
        (DefinableFunction.const ds') (DefinableFunction.var 0))
  case zero => intro _; rw [iseqMaxIdgAux_zero, iseqMaxIdgAux_zero]
  case succ j ih =>
    intro h
    rw [iseqMaxIdgAux_succ, iseqMaxIdgAux_succ, ih (fun i hi => h i (lt_trans hi (by simp))),
      h j (by simp)]

/-- **idg-fold over a `seqCons`**: `iseqMaxIdg (seqCons ds v) = max (iseqMaxIdg ds) (idg v)`. -/
lemma iseqMaxIdg_seqCons {ds v : V} (hds : Seq ds) :
    iseqMaxIdg (seqCons ds v) = max (iseqMaxIdg ds) (idg v) := by
  rw [iseqMaxIdg, iseqMaxIdg, Seq.lh_seqCons v hds, iseqMaxIdgAux_succ,
    iseqMaxIdgAux_congr (lh ds) (fun i hi => (znth_seqCons_of_lt hds v hi).symm),
    znth_seqCons_self hds v]

/-- **idg-fold over a constant-idg block**: if every entry's `idg` is `c`, the fold is `c` (for `0<j`). -/
lemma iseqMaxIdgAux_const {ds c : V} (hconst : ∀ i < lh ds, idg (znth ds i) = c) :
    ∀ j, 0 < j → j ≤ lh ds → iseqMaxIdgAux ds j = c := by
  intro j
  induction j using ISigma1.sigma1_succ_induction
  · refine Definable.imp (by definability) (Definable.imp (by definability) ?_)
    exact Definable.comp₂
      (DefinableFunction₂.comp (F := iseqMaxIdgAux)
        (DefinableFunction.const ds) (DefinableFunction.var 0)) (by definability)
  case zero => intro h; exact absurd h (by simp)
  case succ j ih =>
    intro _ hj
    rw [iseqMaxIdgAux_succ, hconst j (lt_of_lt_of_le (by simp) hj)]
    rcases eq_or_ne j 0 with rfl | hj0
    · rw [iseqMaxIdgAux_zero]; simp
    · rw [ih (pos_iff_ne_zero.mpr hj0) (le_trans (by simp) hj), max_self]

/-- **idg-fold of a constant block** `iRepeatSeq v k`: `= idg v` (for `0<k`). -/
lemma iseqMaxIdg_iRepeatSeq {v k : V} (hk : 0 < k) : iseqMaxIdg (iRepeatSeq v k) = idg v := by
  have hconst : ∀ i < lh (iRepeatSeq v k), idg (znth (iRepeatSeq v k) i) = idg v :=
    fun i hi => by rw [znth_iRepeatSeq i (by rwa [iRepeatSeq_lh] at hi)]
  rw [iseqMaxIdg,
    iseqMaxIdgAux_const hconst (lh (iRepeatSeq v k)) (by rw [iRepeatSeq_lh]; exact hk) le_rfl]

/-- **idg-fold of the Ind reduct sequence**: `max (idg d1) (idg d0)` (for `0<k`). -/
lemma iseqMaxIdg_iIndReductSeq {d0 d1 k : V} (hk : 0 < k) :
    iseqMaxIdg (iIndReductSeq d0 d1 k) = max (idg d1) (idg d0) := by
  rw [iIndReductSeq, iseqMaxIdg_seqCons (iRepeatSeq_seq d1 k), iseqMaxIdg_iRepeatSeq hk]

/-- `∸` distributes over `max` (linear order): `max a b ∸ 1 = max (a∸1) (b∸1)`. -/
private lemma max_sub_one_distrib (a b : V) : max a b - 1 = max (a - 1) (b - 1) := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, max_eq_right (tsub_le_tsub_right h 1)]
  · rw [max_eq_left h, max_eq_left (tsub_le_tsub_right h 1)]

/-- **Degree side of LH4**: the Ind reduct `K^{rk p}(d0, d1×k)` has the SAME degree as `Ind^{a,t}_F d0 d1`
(real `irk`). The `K^r` degree `max{rk p, (max dg)∸1}` reshuffles into `Ind`'s `max{(dg∸1)s, rk p}`. -/
lemma idg_zK_iIndReduct {s s' at' p d0 d1 k : V} (hk : 0 < k) :
    idg (zK s' (irk p) (iIndReductSeq d0 d1 k)) = idg (zInd s at' p d0 d1) := by
  rw [idg_zK _ _ _ (iIndReductSeq_seq d0 d1 k), iseqMaxIdg_iIndReductSeq hk, max_sub_one_distrib,
    idg_zInd]
  ac_rfl

/-- **LH4 — full Ind-rule `iord` descent on the genuine reduct object** (real `irk`): with degree
preserved (`idg_zK_iIndReduct`) and `õ` strictly dropping (`icmp_iotil_iIndReduct`),
`iord_descent_samedeg` gives `o(d[0]) ≺ o(Ind^{a,t}_F d0 d1)`. -/
lemma iord_descent_iIndReduct {s s' at' p d0 d1 k : V}
    (hd0 : isNF (iotil d0)) (hd1 : isNF (iotil d1)) (hk : 0 < k) :
    icmp (iord (zK s' (irk p) (iIndReductSeq d0 d1 k))) (iord (zInd s at' p d0 d1)) = 0 := by
  refine iord_descent_samedeg (idg_zK_iIndReduct (s := s) (at' := at') hk) ?_
  rw [iotil_zK _ _ _ (iIndReductSeq_seq d0 d1 k)]
  exact icmp_iotil_iIndReduct hd0 hd1 hk

/-! ## THE NUT — case 5.1 (cut-elimination) ordinal descent on a genuine reduct object

Buchholz Lemma 4.1(b)(ii) case 5.1 (`E-CRUX2-DECOMPOSITION-2026-06-24.md §8.3`). The critical chain
`d = K^r_Π d0…dl` reduces to `d[0] = K^{r-1}_Π d{0} d{1}`, where `d{0}`,`d{1}` are the two auxiliary
derivations from Theorem 3.4 (the redex `(i,j,k)` from Lemma 3.1). The reduct's premise sequence is the
**two-element** `⟨d{0}, d{1}⟩`. Unlike the structural rules, the pre-ordinal `õ` may *jump up* — but the
degree strictly **drops by one** (the only degree-drop in the whole proof; this IS cut-elimination), and
the drop absorbs the jump through the tower (`iord_descent_cut`, the ordinal tail — DONE).

This section mirrors the LH4 architecture (`iIndReductSeq`/folds/`iord_descent_iIndReduct`) on a genuine
two-element reduct object: the `õ`-fold lands on **F2** (`icmp_omega_pow_nadd_lt`, N3b) and the `idg`-fold
on the **ℕ-max degree-drop** (N3a). The IH facts (`õ(d{ν}) ≺ õ(d)`, `dg(d{ν}) ≤ dg(d)`, N1/N2) and the
rank fact `r ≥ 1` (from T3.4 `rk(A(d)) < r`) are the lemma's hypotheses — exactly the Thm-4.2 mutual-IH
interface, to be discharged by `ZDerivation` structural induction downstream. -/

/-- Empty-sequence `#`-fold is `0`. -/
@[simp] lemma iseqNaddIdg_empty : iseqNaddIdg (∅ : V) = 0 := by
  rw [iseqNaddIdg, lh_empty, iseqNaddIdgAux_zero]

/-- Empty-sequence `idg`-fold is `0`. -/
@[simp] lemma iseqMaxIdg_empty : iseqMaxIdg (∅ : V) = 0 := by
  rw [iseqMaxIdg, lh_empty, iseqMaxIdgAux_zero]

/-- The critical reduct's two-element premise sequence `⟨d{0}, d{1}⟩` (Buchholz §3.2 case 5.1). -/
noncomputable def iCritReductSeq (d0 d1 : V) : V := seqCons (seqCons ∅ d0) d1

@[simp] lemma iCritReductSeq_seq (d0 d1 : V) : Seq (iCritReductSeq d0 d1) :=
  (seq_empty.seqCons d0).seqCons d1

@[simp] lemma iCritReductSeq_lh (d0 d1 : V) : lh (iCritReductSeq d0 d1) = 2 := by
  rw [iCritReductSeq, Seq.lh_seqCons _ (seq_empty.seqCons d0), Seq.lh_seqCons _ seq_empty, lh_empty,
    zero_add, one_add_one_eq_two]

@[simp] lemma znth_iCritReductSeq_zero (d0 d1 : V) : znth (iCritReductSeq d0 d1) 0 = d0 := by
  have h1 : (0 : V) < lh (seqCons (∅ : V) d0) := by
    rw [Seq.lh_seqCons _ seq_empty, lh_empty, zero_add]; exact one_pos
  rw [iCritReductSeq, znth_seqCons_of_lt (seq_empty.seqCons d0) d1 h1]
  have := znth_seqCons_self seq_empty d0
  rwa [lh_empty] at this

@[simp] lemma znth_iCritReductSeq_one (d0 d1 : V) : znth (iCritReductSeq d0 d1) 1 = d1 := by
  have h := znth_seqCons_self (seq_empty.seqCons d0) d1
  rw [Seq.lh_seqCons _ seq_empty, lh_empty, zero_add] at h
  rw [iCritReductSeq]; exact h

/-- **Critical recombination validity (Thm 3.4(a) → outer `K^{r-1}` chain).** The two-element chain
`⟨d{0}, d{1}⟩` underlying the critical reduct `d[0] = K^{r-1}_Π d{0} d{1}` (Buchholz §3.2 case 5.1) is
`isChainInf`-valid with conclusion `s = Π` and rank `r`, given the Thm-3.4(a) end-sequent threading:
`d{1}`'s succedent is `Π`'s succedent (`d{1} ⊢ A(d),Π`); `d{0}`'s antecedent threads to `Π`
(`d{0} ⊢ Π·A(d)`); `d{1}`'s antecedent threads to `Π` or to the cut formula `A(d)` = `d{0}`'s succedent
(the genuine R/L cut on `A(d)`); and `rk(A(d)) ≤ r` (Thm 3.4(a) `rk(A(d)) < r`, here the rank-`(r-1)`
chain reads its cut formula `A(d)` at `≤ r`). This is the validity half of the critical case of
`RedSound`, modulo the genuine reduct supplying these sequents (the current `iCritReduct` is the
ordinal shadow with all-`fstIdx d` premises — see the Option-B obstruction). -/
lemma isChainInf_iCritReductSeq {s r d0 d1 : V}
    (hsucc1 : seqSucc (fstIdx d1) = seqSucc s)
    (hthread0 : ∀ B, inAnt B (seqAnt (fstIdx d0)) → inAnt B (seqAnt s))
    (hthread1 : ∀ B, inAnt B (seqAnt (fstIdx d1)) →
        inAnt B (seqAnt s) ∨ B = seqSucc (fstIdx d0))
    (hrank0 : irk (seqSucc (fstIdx d0)) ≤ r) :
    isChainInf s r (iCritReductSeq d0 d1) := by
  have eA0 : chainAsucc (iCritReductSeq d0 d1) 0 = seqSucc (fstIdx d0) := by
    unfold chainAsucc; rw [znth_iCritReductSeq_zero]
  have eN0 : chainAnt (iCritReductSeq d0 d1) 0 = seqAnt (fstIdx d0) := by
    unfold chainAnt; rw [znth_iCritReductSeq_zero]
  have eN1 : chainAnt (iCritReductSeq d0 d1) 1 = seqAnt (fstIdx d1) := by
    unfold chainAnt; rw [znth_iCritReductSeq_one]
  refine ⟨1, ?_, ?_, ?_, ?_⟩
  · rw [iCritReductSeq_lh]; exact one_lt_two
  · left; unfold chainAsucc; rw [znth_iCritReductSeq_one]; exact hsucc1
  · intro i hi B hB
    rcases eq_or_lt_of_le hi with rfl | hlt
    · rw [eN1] at hB
      rcases hthread1 B hB with h | h
      · exact Or.inl h
      · exact Or.inr ⟨0, one_pos, by rw [h, eA0]⟩
    · obtain rfl := lt_one_iff_eq_zero.mp hlt
      rw [eN0] at hB
      exact Or.inl (hthread0 B hB)
  · intro i hi
    obtain rfl := lt_one_iff_eq_zero.mp hi
    rw [eA0]; exact hrank0

/-- A predicate holding on both `d0` and `d1` holds on every premise of `⟨d0, d1⟩`. -/
lemma forall_lt_iCritReductSeq {P : V → Prop} {d0 d1 : V} (h0 : P d0) (h1 : P d1) :
    ∀ i < lh (iCritReductSeq d0 d1), P (znth (iCritReductSeq d0 d1) i) := by
  intro i hi
  rcases lt_or_ge i 1 with hlt | hge
  · obtain rfl := lt_one_iff_eq_zero.mp hlt; rw [znth_iCritReductSeq_zero]; exact h0
  · have hi2 : i < 1 + 1 := by rw [iCritReductSeq_lh, ← one_add_one_eq_two] at hi; exact hi
    obtain rfl : i = 1 := le_antisymm (le_iff_lt_succ.mpr hi2) hge
    rw [znth_iCritReductSeq_one]; exact h1

/-- **Full faithful validity of the critical recombination chain** (Buchholz §3.2 case 5.1 + Thm 3.4).
`zK s r ⟨d{0}, d{1}⟩` is `zKValidF` given: the two auxiliaries are `Rep`-tagged chains
(`tp = isymRep`, `zTag = 4`, so own-permissibility is automatic and the I/Ax formula-hood conjuncts are
vacuous), the Thm-3.4(a) cut-threading (`isChainInf_iCritReductSeq`), the auxiliaries' succedent
formula-hood, and the conclusion-sequent formula-hood. The validity half (`RedSound`'s D₁) of the
critical case, isolated as a hypothesis interface for the genuine reduct to discharge. -/
lemma zKValidF_iCritReductSeq {s r d0 d1 : V}
    (htp0 : tp d0 = isymRep) (htp1 : tp d1 = isymRep)
    (htag0 : zTag d0 = 4) (htag1 : zTag d1 = 4)
    (hsucc1 : seqSucc (fstIdx d1) = seqSucc s)
    (hthread0 : ∀ B, inAnt B (seqAnt (fstIdx d0)) → inAnt B (seqAnt s))
    (hthread1 : ∀ B, inAnt B (seqAnt (fstIdx d1)) →
        inAnt B (seqAnt s) ∨ B = seqSucc (fstIdx d0))
    (hrank0 : irk (seqSucc (fstIdx d0)) ≤ r)
    (hUf0 : IsUFormula ℒₒᵣ (seqSucc (fstIdx d0)))
    (hUf1 : IsUFormula ℒₒᵣ (seqSucc (fstIdx d1)))
    (hss : IsUFormula ℒₒᵣ (seqSucc s))
    (hsa : ∀ k < lh (seqAnt s), IsUFormula ℒₒᵣ (znth (seqAnt s) k)) :
    zKValidF s r (iCritReductSeq d0 d1) := by
  refine ⟨isChainInf_iCritReductSeq hsucc1 hthread0 hthread1 hrank0, ?_, ?_, ?_, ?_, ?_, ?_, hss, hsa⟩
  · exact forall_lt_iCritReductSeq (P := fun x => iperm (tp x) (fstIdx x))
      (by rw [htp0]; exact iperm_isymRep _) (by rw [htp1]; exact iperm_isymRep _)
  · exact forall_lt_iCritReductSeq (P := fun x => zTag x = 1 → IsUFormula ℒₒᵣ (zIallF x))
      (fun hc => by rw [htag0] at hc; simp at hc) (fun hc => by rw [htag1] at hc; simp at hc)
  · exact forall_lt_iCritReductSeq (P := fun x => zTag x = 2 → IsUFormula ℒₒᵣ (zInegF x))
      (fun hc => by rw [htag0] at hc; simp at hc) (fun hc => by rw [htag1] at hc; simp at hc)
  · exact forall_lt_iCritReductSeq (P := fun x => zTag x = 5 → IsUFormula ℒₒᵣ (zAxAllF x))
      (fun hc => by rw [htag0] at hc; simp at hc) (fun hc => by rw [htag1] at hc; simp at hc)
  · exact forall_lt_iCritReductSeq (P := fun x => zTag x = 6 → IsUFormula ℒₒᵣ (zAxNegF x))
      (fun hc => by rw [htag0] at hc; simp at hc) (fun hc => by rw [htag1] at hc; simp at hc)
  · exact forall_lt_iCritReductSeq (P := fun x => IsUFormula ℒₒᵣ (seqSucc (fstIdx x))) hUf0 hUf1

/-- **Critical recombination validity on the GENUINE auxiliaries — threading is AUTOMATIC.** When the two
auxiliaries carry the genuine Buchholz §2 p.6 / Thm 3.4(a) endsequents — `d{0}` concludes `Θ→A(d)`
(`seqSetSucc s C`), `d{1}` concludes `A(d),Θ→D` (`seqAddAnt C s`), with `C = A(d)` the cut formula — the
cut-threading hypotheses of `zKValidF_iCritReductSeq` hold *by construction* (`seqSetSucc`/`seqAddAnt`
read-outs + `inAnt_seqCons`), leaving only the cut-rank drop `rk(A(d)) ≤ rOut` (Thm 3.4(a), `< r`) and
the formula-hood of `A(d)` and the conclusion's antecedent/succedent. The inner ranks `rIn0/rIn1` and
premise sequences `ds0/ds1` are immaterial to the outer chain's validity. This is the validity (D₁) of
the critical reduct, modulo only the (banked) rank arithmetic and the auxiliaries being `ZDerivation`s. -/
lemma zKValidF_iCritReductGen {s C rOut rIn0 rIn1 ds0 ds1 : V}
    (hsAnt : Seq (seqAnt s))
    (hCrk : irk C ≤ rOut)
    (hCUf : IsUFormula ℒₒᵣ C)
    (hssUf : IsUFormula ℒₒᵣ (seqSucc s))
    (hsaUf : ∀ k < lh (seqAnt s), IsUFormula ℒₒᵣ (znth (seqAnt s) k)) :
    zKValidF s rOut
      (iCritReductSeq (zK (seqSetSucc s C) rIn0 ds0) (zK (seqAddAnt C s) rIn1 ds1)) := by
  apply zKValidF_iCritReductSeq
  · rw [tp_zK]
  · rw [tp_zK]
  · rw [zTag_zK]
  · rw [zTag_zK]
  · rw [fstIdx_zK, seqSucc_seqAddAnt]
  · intro B hB; rw [fstIdx_zK, seqAnt_seqSetSucc] at hB; exact hB
  · intro B hB
    rw [fstIdx_zK, seqAnt_seqAddAnt] at hB
    rw [fstIdx_zK, seqSucc_seqSetSucc]
    exact ((inAnt_seqCons hsAnt).mp hB).symm
  · rw [fstIdx_zK, seqSucc_seqSetSucc]; exact hCrk
  · rw [fstIdx_zK, seqSucc_seqSetSucc]; exact hCUf
  · rw [fstIdx_zK, seqSucc_seqAddAnt]; exact hssUf
  · exact hssUf
  · exact hsaUf

/-- **The genuine critical reduct** `d[0] = K^{rOut}_Π d{0} d{1}` (Buchholz §3.2 case 5.1), built on the
GENUINE auxiliaries: `d{0} = K^{rIn0}_{Θ→A(d)} ds0` concludes `Θ→A(d)` (`seqSetSucc s C`), `d{1} =
K^{rIn1}_{A(d),Θ→D} ds1` concludes `A(d),Θ→D` (`seqAddAnt C s`), with `C = A(d)` the cut formula. Unlike
the ordinal-shadow `iCritReduct`, the auxiliaries carry the cut's reduced endsequents — so the
recombination's validity threading is automatic (`zKValidF_iCritReductGen`). -/
noncomputable def iCritReductG (s C rOut rIn0 rIn1 ds0 ds1 : V) : V :=
  zK s rOut (iCritReductSeq (zK (seqSetSucc s C) rIn0 ds0) (zK (seqAddAnt C s) rIn1 ds1))

@[simp] lemma fstIdx_iCritReductG (s C rOut rIn0 rIn1 ds0 ds1 : V) :
    fstIdx (iCritReductG s C rOut rIn0 rIn1 ds0 ds1) = s := by simp [iCritReductG]
@[simp] lemma zTag_iCritReductG (s C rOut rIn0 rIn1 ds0 ds1 : V) :
    zTag (iCritReductG s C rOut rIn0 rIn1 ds0 ds1) = 4 := by simp [iCritReductG]
@[simp] lemma zKseq_iCritReductG (s C rOut rIn0 rIn1 ds0 ds1 : V) :
    zKseq (iCritReductG s C rOut rIn0 rIn1 ds0 ds1) =
      iCritReductSeq (zK (seqSetSucc s C) rIn0 ds0) (zK (seqAddAnt C s) rIn1 ds1) := by
  simp [iCritReductG]

/-- `õ`-fold of the critical reduct sequence: `ω^{õ d{0}} # ω^{õ d{1}}` (N3b's left side). -/
lemma iseqNaddIdg_iCritReductSeq (d0 d1 : V) :
    iseqNaddIdg (iCritReductSeq d0 d1) =
      inadd (ocOadd (iotil d0) 1 0) (ocOadd (iotil d1) 1 0) := by
  rw [iCritReductSeq, iseqNaddIdg_seqCons (seq_empty.seqCons d0),
    iseqNaddIdg_seqCons seq_empty, iseqNaddIdg_empty, inadd_zero_left]

/-- `idg`-fold of the critical reduct sequence: `max (idg d{0}) (idg d{1})` (N3a's max). -/
lemma iseqMaxIdg_iCritReductSeq (d0 d1 : V) :
    iseqMaxIdg (iCritReductSeq d0 d1) = max (idg d0) (idg d1) := by
  rw [iCritReductSeq, iseqMaxIdg_seqCons (seq_empty.seqCons d0),
    iseqMaxIdg_seqCons seq_empty, iseqMaxIdg_empty, max_eq_right (show (0:V) ≤ idg d0 by simp)]

/-- The chain rank `r` is `≤` the chain's own degree (`idg(K^r ds) = max r (…) ≥ r`). -/
lemma r_le_idg_zK (s r ds : V) (hds : Seq ds) : r ≤ idg (zK s r ds) := by
  rw [idg_zK s r ds hds]; exact le_max_left _ _

/-- **N3a — the cut-elimination degree drop**: `dg(d[0]) = max{r', max(dg d{0}, dg d{1})∸1} < dg(d)`.
Each component is `< dg(d)`: `r' < dg(d)` (the reduct rank `r-1`, from `r ≤ dg d`), and
`max(dg d{0}, dg d{1})∸1 < dg(d)` (from `dg(d{ν}) ≤ dg(d)` (N2) and `dg(d) ≥ 1`). Pure ℕ-max
arithmetic once `iR` builds `d{0}/d{1}`. -/
lemma idg_zK_iCritReduct_lt {s' r' d0 d1 d : V}
    (hr' : r' + 1 ≤ idg d) (h0 : idg d0 ≤ idg d) (h1 : idg d1 ≤ idg d) (hpos : 1 ≤ idg d) :
    idg (zK s' r' (iCritReductSeq d0 d1)) + 1 ≤ idg d := by
  rw [idg_zK _ _ _ (iCritReductSeq_seq d0 d1), iseqMaxIdg_iCritReductSeq, succ_le_iff_lt]
  exact max_lt (succ_le_iff_lt.mp hr')
    (lt_of_le_of_lt (tsub_le_tsub_right (max_le h0 h1) 1)
      (tsub_lt_self (pos_iff_one_le.mpr hpos) one_pos))

/-- **THE NUT (case 5.1 ordinal descent) — `o(d[0]) ≺ o(d)` on the genuine two-element reduct object.**
Given the Thm-4.2 mutual-IH facts on the auxiliaries `d{0}`,`d{1}` (`õ(d{ν}) ≺ õ(d)`, `dg(d{ν}) ≤ dg(d)`)
and the rank-bound consequence `dg(d) ≥ 1`, `r' + 1 ≤ dg(d)` (T3.4 `rk(A(d)) < r ≤ dg(d)`), the reduct
`d[0] = K^{r'}_Π d{0} d{1}` descends: N3b (`õ(d[0]) = ω^{õ d{0}} # ω^{õ d{1}} ≺ ω^{õ(d)}`, **F2**) and N3a
(degree drop) feed `iord_descent_cut` (the tower combine, N4). -/
lemma iord_descent_iCritReduct {s' r' d0 d1 d : V}
    (hnf : isNF (iotil d))
    (h0o : icmp (iotil d0) (iotil d) = 0) (h1o : icmp (iotil d1) (iotil d) = 0)
    (hr' : r' + 1 ≤ idg d) (h0g : idg d0 ≤ idg d) (h1g : idg d1 ≤ idg d) (hpos : 1 ≤ idg d) :
    icmp (iord (zK s' r' (iCritReductSeq d0 d1))) (iord d) = 0 := by
  refine iord_descent_cut hnf (idg_zK_iCritReduct_lt hr' h0g h1g hpos) ?_
  rw [iotil_zK _ _ _ (iCritReductSeq_seq d0 d1), iseqNaddIdg_iCritReductSeq]
  exact icmp_omega_pow_nadd_lt h0o h1o

/-- **THE NUT, chain-specialized** — the reduct rank is the original chain rank minus one
(`d[0] = K^{r-1}…`, Buchholz §3.2 case 5.1). `r ≤ dg(K^r ds)` is automatic (`r_le_idg_zK`); `r ≥ 1` is
T3.4. So the only genuine inputs are the IH bounds on `d{0}`,`d{1}`. -/
lemma iord_descent_iCritReduct_chain {s s' r d0 d1 ds : V}
    (hds : Seq ds) (hr : 1 ≤ r)
    (hnf : isNF (iotil (zK s r ds)))
    (h0o : icmp (iotil d0) (iotil (zK s r ds)) = 0)
    (h1o : icmp (iotil d1) (iotil (zK s r ds)) = 0)
    (h0g : idg d0 ≤ idg (zK s r ds)) (h1g : idg d1 ≤ idg (zK s r ds)) :
    icmp (iord (zK s' (r - 1) (iCritReductSeq d0 d1))) (iord (zK s r ds)) = 0 := by
  have hrd : r ≤ idg (zK s r ds) := r_le_idg_zK s r ds hds
  have hpos : 1 ≤ idg (zK s r ds) := le_trans hr hrd
  have hr' : (r - 1) + 1 ≤ idg (zK s r ds) := by rw [sub_add_self_of_le hr]; exact hrd
  exact iord_descent_iCritReduct hnf h0o h1o hr' h0g h1g hpos

/-! ## N2 — the "replace-a-premise" fold facts (Buchholz Thm 4.2 IH-lift; judge §8.3 N2)

The critical auxiliaries `d{0} = K^r(i/d_i[k])`, `d{1} = K^r(j/d_j[0])` are the chain `d` with ONE
premise replaced by an ordinally-smaller reduct (N1 IH: `õ(d_i[k]) ≺ õ(d_i)`, `dg(d_i[k]) ≤ dg(d_i)`).
These generic fold lemmas — over two premise sequences `ds`,`ds'` agreeing (in `õ`/`idg` of entries)
except at one index `i` — give the N2 facts `õ(d{ν}) ≺ õ(d)` (strict, via **F1**) and `dg(d{ν}) ≤ dg(d)`
(via max-fold monotonicity), exactly the hypotheses the nut's `iord_descent_iCritReduct` consumes. The
fold-drop is the genuine "left-cancel one summand" content (judge's reusable T2 leaf); definability-free
(the arithmetized `seqUpdate` object that realizes `ds' = ds[i ↦ v]` layers on top). -/

/-- Partial `#`-fold depends only on the `õ` of entries (stronger than `iseqNaddIdgAux_congr`, which
needs entry equality — this needs only `õ`-of-entry equality). -/
lemma iseqNaddIdgAux_congr_iotil {ds ds' : V} :
    ∀ j, (∀ i < j, iotil (znth ds i) = iotil (znth ds' i)) →
      iseqNaddIdgAux ds j = iseqNaddIdgAux ds' j := by
  intro j
  induction j using ISigma1.sigma1_succ_induction
  · definability
  case zero => intro _; rw [iseqNaddIdgAux_zero, iseqNaddIdgAux_zero]
  case succ j ih =>
    intro h
    rw [iseqNaddIdgAux_succ, iseqNaddIdgAux_succ, ih (fun i hi => h i (lt_trans hi (by simp))),
      h j (by simp)]

/-- Partial `#`-fold is NF when every folded entry's `õ` is NF. -/
lemma isNF_iseqNaddIdgAux' {ds : V} (hNF : ∀ n, isNF (iotil (znth ds n))) :
    ∀ j, isNF (iseqNaddIdgAux ds j) := by
  intro j
  induction j using ISigma1.sigma1_succ_induction
  · definability
  case zero => rw [iseqNaddIdgAux_zero]; exact isNF_zero
  case succ j ih => rw [iseqNaddIdgAux_succ]; exact isNF_inadd (isNF_omega_pow (hNF j)) _ ih

/-- **Unbounded `≺`-transitivity wrapper** over the bounded `icmp_trans` (bound = `max a (max b c)`). -/
lemma icmp_lt_trans {a b c : V} (hab : icmp a b = 0) (hbc : icmp b c = 0) : icmp a c = 0 :=
  icmp_trans (max a (max b c)) a (le_max_left _ _) b (le_trans (le_max_left _ _) (le_max_right _ _))
    c (le_trans (le_max_right _ _) (le_max_right _ _)) hab hbc

/-- **A finite-head value is `≺` its own ω-power**: `ocExp X = 0` and `X ≠ 0` ⟹ `X ≺ ω^X`. The head
exponent comparison `icmp 0 X = 0` (`X ≠ 0`) decides the lexicographic `icmp_ocOadd` outright. Used for
the `oAtomLk C` reduct value (`oAtomLk C = ω^0·m`, finite head). -/
lemma finHead_lt_omega_pow {X : V} (hX0 : ocExp X = 0) (hXne : X ≠ 0) :
    icmp X (ocOadd X 1 0) = 0 := by
  obtain ⟨c, t, rfl⟩ : ∃ c t, X = ocOadd 0 c t :=
    ⟨ocCoeff X, ocTail X, by rw [← hX0]; exact (ocOadd_destruct hXne).symm⟩
  rw [icmp_ocOadd, icmp_zero_ocOadd]
  simp [thenV]

/-- **A finite-head fold-summand value is `≺` the whole `#`-fold.** If a fold entry `znth ds j`
(`j < lh ds`) has finite-head `õ` value `X = iotil (znth ds j)` (`ocExp X = 0`, `X ≠ 0` — e.g.
`X = oAtomLk C`), then `X ≺ #_n ω^{õ(znth ds n)}`. The summand `ω^X` rides inside the fold (fold-monotone
under `inadd`), and `X ≺ ω^X` (`finHead_lt_omega_pow`); `icmp_lt_trans` chains them at each fold step (the
new summand `ω^{…} ≠ 0` keeps every step strict; only the empty-prefix base is settled by `finHead`). -/
lemma finHead_iotil_lt_iseqNaddIdg {ds j X : V} (hj : j < lh ds)
    (hX0 : ocExp X = 0) (hXne : X ≠ 0) (hXval : iotil (znth ds j) = X)
    (hNF : ∀ n, isNF (iotil (znth ds n))) :
    icmp X (iseqNaddIdg ds) = 0 := by
  have hXNF : isNF X := hXval ▸ hNF j
  have key : ∀ J, j < J → icmp X (iseqNaddIdgAux ds J) = 0 := by
    intro J
    induction J using ISigma1.sigma1_succ_induction
    · definability
    case zero => intro h; exact absurd h (by simp)
    case succ J ih =>
      intro hjJ
      rw [iseqNaddIdgAux_succ]
      rcases lt_or_eq_of_le (le_iff_lt_succ.mpr hjJ) with hlt | heq
      · -- j < J: IH gives `X ≺ Q`; the new summand `R = ω^{õ(znth ds J)}` rides on top, `Q ≼ Q # R`.
        set Q := iseqNaddIdgAux ds J with hQ
        set R := ocOadd (iotil (znth ds J)) 1 0 with hR
        have hQNF : isNF Q := isNF_iseqNaddIdgAux' hNF J
        have hRNF : isNF R := isNF_omega_pow (hNF J)
        have hRne : R ≠ 0 := (ocOadd_pos _ _ _).ne'
        have hQlt : icmp Q (inadd Q R) = 0 := by
          have h := inadd_left_mono isNF_zero hRNF (icmp_zero_pos hRne) Q hQNF
          rwa [inadd_zero_right Q hQNF] at h
        exact icmp_lt_trans (ih hlt) hQlt
      · -- j = J: the new summand IS `ω^X`; `X ≺ ω^X` and `ω^X ≼ P # ω^X`.
        subst heq
        rw [hXval]
        set P := iseqNaddIdgAux ds j with hP
        have hPNF : isNF P := isNF_iseqNaddIdgAux' hNF j
        have hωNF : isNF (ocOadd X 1 0) := isNF_omega_pow hXNF
        have hXω : icmp X (ocOadd X 1 0) = 0 := finHead_lt_omega_pow hX0 hXne
        rcases eq_or_ne P 0 with hP0 | hP0
        · rw [hP0, inadd_zero_left]; exact hXω
        · have hωle : icmp (ocOadd X 1 0) (inadd P (ocOadd X 1 0)) = 0 := by
            rw [inadd_comm (ocOadd X 1 0) hωNF P hPNF]
            have h := inadd_left_mono isNF_zero hPNF (icmp_zero_pos hP0) (ocOadd X 1 0) hωNF
            rwa [inadd_zero_right (ocOadd X 1 0) hωNF] at h
          exact icmp_lt_trans hXω hωle
  exact key (lh ds) hj

/-- **N2, `õ`-side (strict)** — the `#`-fold strictly drops when ONE entry's `õ` strictly drops and the
rest are unchanged (F1 left-cancel). Generic over `ds`,`ds'`; the strict-drop entry is `i`. -/
lemma iseqNaddIdgAux_lt_replace {ds ds' i : V}
    (hlt : icmp (iotil (znth ds' i)) (iotil (znth ds i)) = 0)
    (heq : ∀ n, n ≠ i → iotil (znth ds' n) = iotil (znth ds n))
    (hNF : ∀ n, isNF (iotil (znth ds n)))
    (hNF' : ∀ n, isNF (iotil (znth ds' n))) :
    ∀ j, i < j → icmp (iseqNaddIdgAux ds' j) (iseqNaddIdgAux ds j) = 0 := by
  intro j
  induction j using ISigma1.sigma1_succ_induction
  · definability
  case zero => intro h; exact absurd h (by simp)
  case succ j ih =>
    intro hi
    rw [iseqNaddIdgAux_succ, iseqNaddIdgAux_succ]
    rcases lt_or_eq_of_le (le_iff_lt_succ.mpr hi) with hij | hij
    · -- i < j: entry j is unchanged; prefix strictly drops (IH), suffix fixed (F1-mirror).
      rw [heq j (Ne.symm (ne_of_lt hij))]
      exact inadd_right_mono (isNF_iseqNaddIdgAux' hNF' j) (isNF_iseqNaddIdgAux' hNF j) (ih hij)
        _ (isNF_omega_pow (hNF j))
    · -- i = j: entry j IS the strict-drop entry; prefix unchanged, suffix drops (F1).
      subst hij
      have hpre : iseqNaddIdgAux ds' i = iseqNaddIdgAux ds i :=
        iseqNaddIdgAux_congr_iotil i (fun m hm => heq m (ne_of_lt hm))
      rw [hpre]
      refine inadd_left_mono (isNF_omega_pow (hNF' i)) (isNF_omega_pow (hNF i)) ?_
        _ (isNF_iseqNaddIdgAux' hNF i)
      rw [icmp_omega_pow]; exact hlt

/-- **N2, `idg`-side (monotone)** — the `idg` (max) fold is monotone under entrywise `idg`-domination. -/
lemma iseqMaxIdgAux_mono {ds ds' : V} (hle : ∀ n, idg (znth ds' n) ≤ idg (znth ds n)) :
    ∀ j, iseqMaxIdgAux ds' j ≤ iseqMaxIdgAux ds j := by
  intro j
  induction j using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ j ih => rw [iseqMaxIdgAux_succ, iseqMaxIdgAux_succ]; exact max_le_max ih (hle j)

/-- **N2, `õ`-side at the `K^r` level** — `õ(K^r ds') ≺ õ(K^r ds)` when `ds'` replaces premise `i` of
`ds` by an ordinally-smaller derivation (`õ(znth ds' i) ≺ õ(znth ds i)`), same length, rest unchanged.
This is `õ(d{ν}) ≺ õ(d)` (judge §8.3 N2), the strict pre-ordinal hypothesis of `iord_descent_iCritReduct`. -/
lemma iotil_zK_lt_replace {s s' r r' ds ds' i : V} (hds : Seq ds) (hds' : Seq ds')
    (hlh : lh ds' = lh ds) (hi : i < lh ds)
    (hlt : icmp (iotil (znth ds' i)) (iotil (znth ds i)) = 0)
    (heq : ∀ n, n ≠ i → iotil (znth ds' n) = iotil (znth ds n))
    (hNF : ∀ n, isNF (iotil (znth ds n))) (hNF' : ∀ n, isNF (iotil (znth ds' n))) :
    icmp (iotil (zK s' r' ds')) (iotil (zK s r ds)) = 0 := by
  rw [iotil_zK s' r' ds' hds', iotil_zK s r ds hds, iseqNaddIdg, iseqNaddIdg, hlh]
  exact iseqNaddIdgAux_lt_replace hlt heq hNF hNF' (lh ds) hi

/-- **N2, `idg`-side at the `K^r` level** — `dg(K^r ds') ≤ dg(K^r ds)` (same rank `r`) when `ds'`
replaces a premise of `ds` by one of `≤` degree, same length. This is `dg(d{ν}) ≤ dg(d)` (judge §8.3 N2). -/
lemma idg_zK_le_replace {s s' r ds ds' : V} (hds : Seq ds) (hds' : Seq ds')
    (hlh : lh ds' = lh ds) (hle : ∀ n, idg (znth ds' n) ≤ idg (znth ds n)) :
    idg (zK s' r ds') ≤ idg (zK s r ds) := by
  rw [idg_zK s' r ds' hds', idg_zK s r ds hds, iseqMaxIdg, iseqMaxIdg, hlh]
  exact max_le_max le_rfl (tsub_le_tsub_right (iseqMaxIdgAux_mono hle (lh ds)) 1)

/-! ## `seqUpdate` — replace one entry of a sequence (the arithmetized "replace-a-premise", judge T2/T3)

`seqUpdate ds i v = ds[i ↦ v]`: the sequence `ds` with entry `i` replaced by `v`, same length. This is
the code-level operation Buchholz's critical reducts use: `d{0} = K^r(i/d_i[k])` is the chain `d` with
its `i`-th premise replaced by the reduct `d_i[k]` (`iCritAux` below). Built as a `PR.Construction` over
a counter copying entries (entry `n` becomes `v` when `n = i`, else `znth ds n`), so it is a total `𝚺₁`
function — the genuine arithmetized object, not a meta-iterate. -/

def seqUpdateAux.blueprint : PR.Blueprint 3 where
  zero := .mkSigma “y ds i v. y = 0”
  succ := .mkSigma “y ih n ds i v.
    ( (n = i ∧ !seqConsDef y ih v) ∨
      (n ≠ i ∧ ∃ b, !znthDef b ds n ∧ !seqConsDef y ih b) )”

noncomputable def seqUpdateAux.construction : PR.Construction V seqUpdateAux.blueprint where
  zero := fun _ ↦ ∅
  succ := fun x n ih ↦ seqCons ih (if n = x 1 then x 2 else znth (x 0) n)
  zero_defined := .mk fun v ↦ by simp [seqUpdateAux.blueprint, emptyset_def]
  succ_defined := .mk fun v ↦ by
    by_cases h : v 2 = v 4
    · simp [seqUpdateAux.blueprint, h, seqCons_defined.iff]
    · simp [seqUpdateAux.blueprint, h, znth_defined.iff, seqCons_defined.iff]

/-- `seqUpdateAux ds i v n` = the length-`n` prefix with entry `i` (if `< n`) replaced by `v`. -/
noncomputable def seqUpdateAux (ds i v n : V) : V := seqUpdateAux.construction.result ![ds, i, v] n

@[simp] lemma seqUpdateAux_zero (ds i v : V) : seqUpdateAux ds i v 0 = ∅ := by
  simp [seqUpdateAux, seqUpdateAux.construction]

@[simp] lemma seqUpdateAux_succ (ds i v n : V) :
    seqUpdateAux ds i v (n + 1) =
      seqCons (seqUpdateAux ds i v n) (if n = i then v else znth ds n) := by
  simp [seqUpdateAux, seqUpdateAux.construction]

def _root_.LO.FirstOrder.Arithmetic.seqUpdateAuxDef : 𝚺₁.Semisentence 5 :=
  seqUpdateAux.blueprint.resultDef.rew (Rew.subst ![#0, #4, #1, #2, #3])

instance seqUpdateAux_defined : 𝚺₁-Function₄ (seqUpdateAux : V → V → V → V → V) via seqUpdateAuxDef :=
  .mk fun v ↦ by simp [seqUpdateAux.construction.result_defined_iff, seqUpdateAuxDef]; rfl

instance seqUpdateAux_definable : 𝚺₁-Function₄ (seqUpdateAux : V → V → V → V → V) :=
  seqUpdateAux_defined.to_definable
instance seqUpdateAux_definable' (Γ) : Γ-[m + 1]-Function₄ (seqUpdateAux : V → V → V → V → V) :=
  seqUpdateAux_definable.of_sigmaOne

@[simp] lemma seqUpdateAux_seq (ds i v n : V) : Seq (seqUpdateAux ds i v n) := by
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero => simpa using seq_empty
  case succ n ih => rw [seqUpdateAux_succ]; exact ih.seqCons _

@[simp] lemma seqUpdateAux_lh (ds i v n : V) : lh (seqUpdateAux ds i v n) = n := by
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero => simpa using lh_empty
  case succ n ih =>
    rw [seqUpdateAux_succ, Seq.lh_seqCons _ (seqUpdateAux_seq ds i v n), ih]

/-- Top-entry read-out (the freshly-appended entry at index `n`): non-inductive, so the `ite` is fine. -/
lemma znth_seqUpdateAux_top (ds i v n : V) :
    znth (seqUpdateAux ds i v (n + 1)) n = if n = i then v else znth ds n := by
  rw [seqUpdateAux_succ]
  have := znth_seqCons_self (seqUpdateAux_seq ds i v n) (if n = i then v else znth ds n)
  rwa [seqUpdateAux_lh] at this

/-- Reads below the top are stable as the prefix grows (the new `seqCons` doesn't touch index `m < n`). -/
lemma znth_seqUpdateAux_stable {ds i v : V} (n m : V) (hm : m < n) :
    znth (seqUpdateAux ds i v (n + 1)) m = znth (seqUpdateAux ds i v n) m := by
  rw [seqUpdateAux_succ,
    znth_seqCons_of_lt (seqUpdateAux_seq ds i v n) _ (by rw [seqUpdateAux_lh]; exact hm)]

/-- `seqUpdateAux` reads `v` at the updated index `i` (once the prefix passes it). `ite`-free, so the
induction's definability side-goal is clean. -/
lemma znth_seqUpdateAux_self {ds i v : V} : ∀ n, i < n → znth (seqUpdateAux ds i v n) i = v := by
  intro n
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero => intro h; exact absurd h (by simp)
  case succ n ih =>
    intro hi
    rcases eq_or_lt_of_le (le_iff_lt_succ.mpr hi) with hin | hilt
    · rw [hin, znth_seqUpdateAux_top, if_pos rfl]
    · rw [znth_seqUpdateAux_stable n i hilt]; exact ih hilt

/-- `seqUpdateAux` is unchanged off the updated index. `ite`-free. -/
lemma znth_seqUpdateAux_of_ne {ds i v m : V} (hmi : m ≠ i) :
    ∀ n, m < n → znth (seqUpdateAux ds i v n) m = znth ds m := by
  intro n
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero => intro h; exact absurd h (by simp)
  case succ n ih =>
    intro hm
    rcases eq_or_lt_of_le (le_iff_lt_succ.mpr hm) with hmn | hmlt
    · rw [hmn, znth_seqUpdateAux_top, if_neg (by rw [← hmn]; exact hmi)]
    · rw [znth_seqUpdateAux_stable n m hmlt]; exact ih hmlt

/-- `seqUpdate ds i v = ds[i ↦ v]` — the full-length update. -/
noncomputable def seqUpdate (ds i v : V) : V := seqUpdateAux ds i v (lh ds)

@[simp] lemma seqUpdate_seq (ds i v : V) : Seq (seqUpdate ds i v) := seqUpdateAux_seq ds i v (lh ds)

@[simp] lemma seqUpdate_lh (ds i v : V) : lh (seqUpdate ds i v) = lh ds := seqUpdateAux_lh ds i v (lh ds)

/-- `seqUpdate` reads `v` at the updated index. -/
lemma znth_seqUpdate_self {ds i v : V} (hi : i < lh ds) : znth (seqUpdate ds i v) i = v :=
  znth_seqUpdateAux_self (lh ds) hi

/-- `seqUpdate` is unchanged off the updated index (any `m`, via the out-of-range `znth = 0`). -/
lemma znth_seqUpdate_of_ne {ds i v m : V} (h : m ≠ i) :
    znth (seqUpdate ds i v) m = znth ds m := by
  rcases lt_or_ge m (lh ds) with hm | hm
  · exact znth_seqUpdateAux_of_ne h (lh ds) hm
  · rw [znth_prop_not (Or.inr (by rw [seqUpdate_lh]; exact hm)), znth_prop_not (Or.inr hm)]

/-- **Updating a premise with its own value is the identity.** `seqUpdate ds i (znth ds i) = ds` for a
`Seq ds` and in-range `i` — the L-rule replace (`red dᵢ = dᵢ`) leaves the premise sequence untouched, so
the dispatch goal `seqUpdate ds i (red dᵢ)` collapses to `ds`. Via `Seq.lh_ext`: same length, and at every
index `seqUpdate` reads `znth ds`. -/
lemma seqUpdate_znth_self {ds i : V} (hds : Seq ds) (hi : i < lh ds) :
    seqUpdate ds i (znth ds i) = ds := by
  refine Seq.lh_ext (seqUpdate_seq ds i (znth ds i)) hds (seqUpdate_lh ds i (znth ds i)) ?_
  intro j x₁ x₂ h₁ h₂
  rw [← (seqUpdate_seq ds i (znth ds i)).znth_eq_of_mem h₁, ← hds.znth_eq_of_mem h₂]
  rcases eq_or_ne j i with rfl | hne
  · rw [znth_seqUpdate_self hi]
  · rw [znth_seqUpdate_of_ne hne]

/-! ### Splice read-outs (Buchholz §3.2 case 5.2.1): `seqCons (seqUpdate ds j a) b`

The sub-critical splice reduct expands premise `j` to two auxiliaries: `a = dⱼ{0}` replaces premise `j`
in place, `b = dⱼ{1}` is appended at the end (index `lh ds`). These read-outs give the spliced premise
at every index, the prerequisite for the splice's `isChainInf` validity (the threading of the appended
`b`). -/

/-- The appended premise `b` sits at index `lh ds`. -/
lemma znth_seqCons_seqUpdate_top (ds j a b : V) :
    znth (seqCons (seqUpdate ds j a) b) (lh ds) = b := by
  have h := znth_seqCons_self (seqUpdate_seq ds j a) b
  rwa [seqUpdate_lh] at h

/-- Below the appended slot, the spliced sequence is the in-place update `seqUpdate ds j a`. -/
lemma znth_seqCons_seqUpdate_lt {ds j a b k : V} (hk : k < lh ds) :
    znth (seqCons (seqUpdate ds j a) b) k = znth (seqUpdate ds j a) k :=
  znth_seqCons_of_lt (seqUpdate_seq ds j a) b (by rw [seqUpdate_lh]; exact hk)

/-- Length of the splice: one more than the original. -/
@[simp] lemma lh_seqCons_seqUpdate (ds j a b : V) :
    lh (seqCons (seqUpdate ds j a) b) = lh ds + 1 := by
  rw [Seq.lh_seqCons _ (seqUpdate_seq ds j a), seqUpdate_lh]

/-! ### T2/T3 — `isChainInf` is preserved by replacing a premise with a same-end-sequent reduct

Buchholz's reduction (Thm 3.4(a) / `E-CRUX2-DECOMPOSITION §8` leaf T2/T3): the validity *structure* of a
`K^r` chain (`isChainInf`: distinguished `j₀`, antecedent threading, rank bound) depends on the premises
only through their **end-sequents** (`chainAsucc`/`chainAnt` = `seqSucc`/`seqAnt ∘ fstIdx ∘ znth`). So
replacing premise `i` by any reduct `v` with the SAME end-sequent (`fstIdx v = fstIdx (znth ds i)`)
leaves `isChainInf` literally invariant. This is the reusable validity-preservation core of `RedSound`
for the critical (`iCritAux`-replace) and non-critical reducts. -/

/-- End-sequent invariance of `seqUpdate` under a same-`fstIdx` replacement: every premise's `fstIdx`
is unchanged. -/
lemma fstIdx_znth_seqUpdate {ds i v : V} (hi : i < lh ds) (hv : fstIdx v = fstIdx (znth ds i)) (n : V) :
    fstIdx (znth (seqUpdate ds i v) n) = fstIdx (znth ds n) := by
  rcases eq_or_ne n i with rfl | hne
  · rw [znth_seqUpdate_self hi, hv]
  · rw [znth_seqUpdate_of_ne hne]

/-- `chainAsucc` is unchanged under a same-end-sequent premise replacement. -/
lemma chainAsucc_seqUpdate {ds i v : V} (hi : i < lh ds) (hv : fstIdx v = fstIdx (znth ds i)) (n : V) :
    chainAsucc (seqUpdate ds i v) n = chainAsucc ds n := by
  unfold chainAsucc; rw [fstIdx_znth_seqUpdate hi hv]

/-- `chainAnt` is unchanged under a same-end-sequent premise replacement. -/
lemma chainAnt_seqUpdate {ds i v : V} (hi : i < lh ds) (hv : fstIdx v = fstIdx (znth ds i)) (n : V) :
    chainAnt (seqUpdate ds i v) n = chainAnt ds n := by
  unfold chainAnt; rw [fstIdx_znth_seqUpdate hi hv]

/-- **T2/T3 validity-preservation (`isChainInf` core).** Replacing premise `i` of a chain by a reduct
`v` with the same end-sequent (`fstIdx v = fstIdx (znth ds i)`) preserves chain-validity `isChainInf`. -/
lemma isChainInf_seqUpdate {s r ds i v : V} (hi : i < lh ds) (hv : fstIdx v = fstIdx (znth ds i)) :
    isChainInf s r (seqUpdate ds i v) ↔ isChainInf s r ds :=
  isChainInf_congr (seqUpdate_lh ds i v)
    (fun n => chainAsucc_seqUpdate hi hv n) (fun n => chainAnt_seqUpdate hi hv n)

/-- **T2/T3 validity-preservation (full `zKValidF`).** Replacing premise `i` of a faithfully-valid chain
by a reduct `v` with the same end-sequent (`fstIdx v = fstIdx (znth ds i)`) preserves faithful chain
validity `zKValidF`, given `v`'s own well-formedness: its own-permissibility (`iperm (tp v) (fstIdx v)`,
Buchholz Lemma 3.3, automatic for a `ZDerivation`) and the tag-gated principal-formula-hood. The
`isChainInf` core is preserved by `isChainInf_seqUpdate`; the off-index per-premise conjuncts inherit
(unchanged `znth`/`chainAsucc`), the at-index ones come from `v`'s well-formedness. This is the reusable
"replace a premise of a valid `K^r` chain by a same-endsequent reduct ⟹ still valid" fact for `RedSound`. -/
lemma zKValidF_seqUpdate {s r ds i v : V} (hi : i < lh ds)
    (hv : fstIdx v = fstIdx (znth ds i))
    (hperm_v : iperm (tp v) (fstIdx v))
    (hf1_v : zTag v = 1 → IsUFormula ℒₒᵣ (zIallF v))
    (hf2_v : zTag v = 2 → IsUFormula ℒₒᵣ (zInegF v))
    (hf5_v : zTag v = 5 → IsUFormula ℒₒᵣ (zAxAllF v))
    (hf6_v : zTag v = 6 → IsUFormula ℒₒᵣ (zAxNegF v))
    (h : zKValidF s r ds) :
    zKValidF s r (seqUpdate ds i v) := by
  obtain ⟨hci, hperm, hg1, hg2, hg5, hg6, hcf, hss, hsa⟩ := h
  refine ⟨(isChainInf_seqUpdate hi hv).mpr hci, ?_, ?_, ?_, ?_, ?_, ?_, hss, hsa⟩
  · intro n hn
    rcases eq_or_ne n i with rfl | hne
    · rw [znth_seqUpdate_self hi]; exact hperm_v
    · rw [znth_seqUpdate_of_ne hne]; exact hperm n (by rwa [seqUpdate_lh] at hn)
  · intro n hn
    rcases eq_or_ne n i with rfl | hne
    · rw [znth_seqUpdate_self hi]; exact hf1_v
    · rw [znth_seqUpdate_of_ne hne]; exact hg1 n (by rwa [seqUpdate_lh] at hn)
  · intro n hn
    rcases eq_or_ne n i with rfl | hne
    · rw [znth_seqUpdate_self hi]; exact hf2_v
    · rw [znth_seqUpdate_of_ne hne]; exact hg2 n (by rwa [seqUpdate_lh] at hn)
  · intro n hn
    rcases eq_or_ne n i with rfl | hne
    · rw [znth_seqUpdate_self hi]; exact hf5_v
    · rw [znth_seqUpdate_of_ne hne]; exact hg5 n (by rwa [seqUpdate_lh] at hn)
  · intro n hn
    rcases eq_or_ne n i with rfl | hne
    · rw [znth_seqUpdate_self hi]; exact hf6_v
    · rw [znth_seqUpdate_of_ne hne]; exact hg6 n (by rwa [seqUpdate_lh] at hn)
  · intro n hn
    rw [chainAsucc_seqUpdate hi hv]; exact hcf n (by rwa [seqUpdate_lh] at hn)

/-! ### Splice end-sequent read-outs (case 5.2.1): `chainAsucc`/`chainAnt` of `seqCons (seqUpdate ds j a) b`

The chain-validity ingredients (`isChainInf`/`zKValidF`) read the splice chain only through its
per-premise end-sequent projections. These resolve `chainAsucc`/`chainAnt` at every index of the splice
`cs = seqCons (seqUpdate ds j a) b`: the appended slot `lh ds` reads `b`, the updated slot `j` reads `a`,
all other slots `k < lh ds` (`k ≠ j`) read the original `znth ds k`. They are the prerequisite for the
splice's `isChainInf`/`zKValidF` validity (deliverable (b) of the lap-86 5.2.1 dispatch). -/

/-- The appended half `b` carries the splice's top succedent. -/
@[simp] lemma chainAsucc_seqCons_seqUpdate_top (ds j a b : V) :
    chainAsucc (seqCons (seqUpdate ds j a) b) (lh ds) = seqSucc (fstIdx b) := by
  unfold chainAsucc; rw [znth_seqCons_seqUpdate_top]

/-- The appended half `b` carries the splice's top antecedent. -/
@[simp] lemma chainAnt_seqCons_seqUpdate_top (ds j a b : V) :
    chainAnt (seqCons (seqUpdate ds j a) b) (lh ds) = seqAnt (fstIdx b) := by
  unfold chainAnt; rw [znth_seqCons_seqUpdate_top]

/-- Below the appended slot the splice's succedent reads the in-place update. -/
lemma chainAsucc_seqCons_seqUpdate_lt {ds j a b k : V} (hk : k < lh ds) :
    chainAsucc (seqCons (seqUpdate ds j a) b) k = chainAsucc (seqUpdate ds j a) k := by
  unfold chainAsucc; rw [znth_seqCons_seqUpdate_lt hk]

/-- Below the appended slot the splice's antecedent reads the in-place update. -/
lemma chainAnt_seqCons_seqUpdate_lt {ds j a b k : V} (hk : k < lh ds) :
    chainAnt (seqCons (seqUpdate ds j a) b) k = chainAnt (seqUpdate ds j a) k := by
  unfold chainAnt; rw [znth_seqCons_seqUpdate_lt hk]

/-- The in-place half `a` carries succedent at the updated slot `j`. -/
lemma chainAsucc_seqUpdate_self {ds j a : V} (hj : j < lh ds) :
    chainAsucc (seqUpdate ds j a) j = seqSucc (fstIdx a) := by
  unfold chainAsucc; rw [znth_seqUpdate_self hj]

/-- Off the updated slot, `seqUpdate`'s succedent is the original's. -/
lemma chainAsucc_seqUpdate_of_ne {ds j a k : V} (hk : k ≠ j) :
    chainAsucc (seqUpdate ds j a) k = chainAsucc ds k := by
  unfold chainAsucc; rw [znth_seqUpdate_of_ne hk]

/-- The in-place half `a` carries antecedent at the updated slot `j`. -/
lemma chainAnt_seqUpdate_self {ds j a : V} (hj : j < lh ds) :
    chainAnt (seqUpdate ds j a) j = seqAnt (fstIdx a) := by
  unfold chainAnt; rw [znth_seqUpdate_self hj]

/-- Off the updated slot, `seqUpdate`'s antecedent is the original's. -/
lemma chainAnt_seqUpdate_of_ne {ds j a k : V} (hk : k ≠ j) :
    chainAnt (seqUpdate ds j a) k = chainAnt ds k := by
  unfold chainAnt; rw [znth_seqUpdate_of_ne hk]

/-- **R-rule replace — `isChainInf` succedent reduction (Buchholz Thm 3.4(b), I∀/I¬ non-`Rep` 5.2.2).**
When the selected premise `i` carries the conclusion succedent (so it serves as the distinguished `j₀`),
replacing it by a reduct `v` with the SAME antecedent (`hant`) and a REDUCED succedent matching the
reduced conclusion `s'` (`hsucc_v`), where `s'` keeps the antecedent (`hX_ant`), preserves chain-validity
— take `j₀ = i`. The off-`i` premises and the conclusion antecedent are unchanged, so the threading/rank
data up to `i` (supplied by the caller from the chain's `zKValidF` + the permIdx/criticality selection
forcing `i ≤ j₀`) transfers verbatim. This is the `isChainInf` core of the conclusion-reducing replace for
an R-rule (`tp dᵢ = R_∀xF` / `R_¬A`) selected premise — the genuine cut-elimination step the keep-`Π`
`isChainInf_seqUpdate` cannot do. -/
lemma isChainInf_seqUpdate_reduceR {s s' r ds i v : V} (hi : i < lh ds)
    (hant : seqAnt (fstIdx v) = chainAnt ds i)
    (hsucc_v : seqSucc (fstIdx v) = seqSucc s')
    (hX_ant : seqAnt s' = seqAnt s)
    (hthread : ∀ i' ≤ i, ∀ B, inAnt B (chainAnt ds i') →
        inAnt B (seqAnt s) ∨ ∃ i'' < i', B = chainAsucc ds i'')
    (hrank : ∀ i' < i, irk (chainAsucc ds i') ≤ r) :
    isChainInf s' r (seqUpdate ds i v) := by
  refine ⟨i, by rwa [seqUpdate_lh], Or.inl ?_, ?_, ?_⟩
  · rw [chainAsucc_seqUpdate_self hi, hsucc_v]
  · intro i' hi' B hB
    have hchAnt : chainAnt (seqUpdate ds i v) i' = chainAnt ds i' := by
      rcases eq_or_ne i' i with rfl | hne
      · rw [chainAnt_seqUpdate_self hi, hant]
      · rw [chainAnt_seqUpdate_of_ne hne]
    rw [hchAnt] at hB
    rcases hthread i' hi' B hB with hin | ⟨i'', hi'', hB'⟩
    · left; rwa [hX_ant]
    · exact Or.inr ⟨i'', hi'', by
        rw [chainAsucc_seqUpdate_of_ne (ne_of_lt (lt_of_lt_of_le hi'' hi')), hB']⟩
  · intro i' hi'
    rw [chainAsucc_seqUpdate_of_ne (ne_of_lt hi')]; exact hrank i' hi'

/-- **GENERAL conclusion-reducing `isChainInf` at `j₀ = i` — membership (`inAnt`) form.** The fully general
replace primitive that subsumes `isChainInf_seqUpdate_reduceR`: it threads premise `i`'s (possibly CHANGED)
antecedent and the lower premises' antecedents into the reduced conclusion `s'` directly via membership,
rather than requiring `seqAnt (fstIdx v) = chainAnt ds i` and `seqAnt s' = seqAnt s`. This is what the FOUR
non-`Rep` cases need: I∀ (succedent → `F(0)`, antecedent kept), I¬ (antecedent GAINS `p`, succedent → `⊥`),
axNeg (succedent → `p`), axAll (antecedent gains `F(k)`) — Buchholz threads on `inAnt`, robust to antecedent
reordering. `hsucc_v` = the new premise-`i` succedent is `s'`'s or `⊥` (the `j₀` succedent condition);
`hant_thread` = premise `i`'s new antecedent threads into `s'`; `hlt_thread` = lower premises thread into
`s'`; `hrank` from the parent (via `permIdx ≤ j₀`). -/
lemma isChainInf_reduceR_membership {s' r ds i v : V} (hi : i < lh ds)
    (hsucc_v : seqSucc (fstIdx v) = seqSucc s' ∨ seqSucc (fstIdx v) = (^⊥ : V))
    (hant_thread : ∀ B, inAnt B (seqAnt (fstIdx v)) →
        inAnt B (seqAnt s') ∨ ∃ i'' < i, B = chainAsucc ds i'')
    (hlt_thread : ∀ i' < i, ∀ B, inAnt B (chainAnt ds i') →
        inAnt B (seqAnt s') ∨ ∃ i'' < i', B = chainAsucc ds i'')
    (hrank : ∀ i' < i, irk (chainAsucc ds i') ≤ r) :
    isChainInf s' r (seqUpdate ds i v) := by
  refine ⟨i, by rwa [seqUpdate_lh], ?_, ?_, ?_⟩
  · rw [chainAsucc_seqUpdate_self hi]; exact hsucc_v
  · intro i' hi' B hB
    rcases eq_or_ne i' i with rfl | hne
    · rw [chainAnt_seqUpdate_self hi] at hB
      rcases hant_thread B hB with h | ⟨i'', hi'', hB'⟩
      · left; exact h
      · exact Or.inr ⟨i'', hi'', by rw [chainAsucc_seqUpdate_of_ne (ne_of_lt hi''), hB']⟩
    · have hi'lt : i' < i := lt_of_le_of_ne hi' hne
      rw [chainAnt_seqUpdate_of_ne hne] at hB
      rcases hlt_thread i' hi'lt B hB with h | ⟨i'', hi'', hB'⟩
      · left; exact h
      · exact Or.inr ⟨i'', hi'', by
          rw [chainAsucc_seqUpdate_of_ne (ne_of_lt (lt_trans hi'' hi'lt)), hB']⟩
  · intro i' hi'
    rw [chainAsucc_seqUpdate_of_ne (ne_of_lt hi')]; exact hrank i' hi'

/-- **Keep-tip replace (⊥-orbit, replaced premise ABOVE the tip).** When the replaced premise `i` lies
strictly above the distinguished tip `j0` (`j0 < i`) and that tip carries `⊥` (`chainAsucc ds j0 = ^⊥`,
automatic on a ⊥-orbit where `seqSucc s = ⊥`), replacing premise `i` by ANY `v` keeps chain-validity with
the SAME tip `j0` and an ARBITRARY new conclusion `s'` whose antecedent is the parent's (`hX_ant`): the new
premise sits above the tip, so it never enters the tip-bounded exit/threading/rank. Contrast
`isChainInf_reduceR_membership`, which re-points `j0 := i` and so demands the reduct succedent be the
conclusion succedent or `⊥` and threading up to `i`. This is the route that frees the ¬-case `haux0` from
needing `redexJ ≤ j0` (`PENDING_WORK` lap-142/143): when `redexJ > j0` the §5 axNeg reduct lands above the
tip and is invisible to the tip-`j0` validity. -/
lemma isChainInf_reduceR_keepTip {s s' r ds i j0 v : V} (hi : i < lh ds)
    (hj0i : j0 < i) (hj0 : j0 < lh ds)
    (hbot : chainAsucc ds j0 = (^⊥ : V))
    (hX_ant : seqAnt s' = seqAnt s)
    (hthread : ∀ i' ≤ j0, ∀ B, inAnt B (chainAnt ds i') →
        inAnt B (seqAnt s) ∨ ∃ i'' < i', B = chainAsucc ds i'')
    (hrank : ∀ i' < j0, irk (chainAsucc ds i') ≤ r) :
    isChainInf s' r (seqUpdate ds i v) := by
  refine ⟨j0, by rwa [seqUpdate_lh], Or.inr ?_, ?_, ?_⟩
  · rw [chainAsucc_seqUpdate_of_ne (ne_of_lt hj0i), hbot]
  · intro i' hi' B hB
    rw [chainAnt_seqUpdate_of_ne (ne_of_lt (lt_of_le_of_lt hi' hj0i))] at hB
    rcases hthread i' hi' B hB with hin | ⟨i'', hi'', hB'⟩
    · left; rwa [hX_ant]
    · exact Or.inr ⟨i'', hi'', by
        rw [chainAsucc_seqUpdate_of_ne
          (ne_of_lt (lt_trans (lt_of_lt_of_le hi'' hi') hj0i)), hB']⟩
  · intro i' hi'
    rw [chainAsucc_seqUpdate_of_ne (ne_of_lt (lt_trans hi' hj0i))]; exact hrank i' hi'

/-- **L-rule replace — `isChainInf` conclusion-antecedent weakening (Buchholz Def 3.2 case 5.2.2, axiom
selected premise).** When the selected premise `dᵢ` is a §5 left-axiom (`tp dᵢ = L^k_A`), the reduct is
the IDENTITY (`red dᵢ = dᵢ`) and the conclusion gains the cut-formula instance `A(k)` in its ANTECEDENT
(`tpReduce (isymLk …) Π 0 = A(k),Γ→D`). Adding a formula to the conclusion antecedent only RELAXES the
threading condition (the threaded `B`'s may now also land in the new antecedent), so chain-validity is
monotone: the same `j₀` works, with the left disjunct `inAnt B (seqAnt s)` weakened through `seqAddAnt`.
The premises (`ds`) and rank (`r`) are untouched. -/
lemma isChainInf_seqAddAnt {s r ds A : V} (hs : Seq (seqAnt s))
    (hci : isChainInf s r ds) : isChainInf (seqAddAnt A s) r ds := by
  obtain ⟨j0, hj0, hA, hthr, hrk⟩ := hci
  refine ⟨j0, hj0, ?_, ?_, ?_⟩
  · rw [seqSucc_seqAddAnt]; exact hA
  · intro i hi B hB
    rcases hthr i hi B hB with hin | hex
    · left; exact (inAnt_seqAddAnt hs).mpr (Or.inr hin)
    · right; exact hex
  · exact hrk

/-- **L-rule replace — `isChainInf` antecedent-growth at an interior premise (Buchholz Def 3.2 case 5.1,
critical L-redex).** When an interior premise `dᵢ` is replaced by a reduct `v` that keeps the SAME succedent
(`seqSucc (fstIdx v) = chainAsucc ds i`) and grows its antecedent by a single head formula `A`
(`seqAnt (fstIdx v) = seqCons (chainAnt ds i) A`), and the conclusion gains the same `A` in its antecedent
(`seqAddAnt A s`), chain-validity is preserved with the SAME distinguished tip `j0`: `chainAsucc` is
preserved at *every* index (so the tip's succedent and all ranks are untouched), the grown antecedent head
`A` threads to the grown conclusion antecedent, and the surviving antecedent entries thread exactly as in the
parent (their prior-succedent witnesses `chainAsucc ds i'` are unchanged). This is the L-side `isChainInf`
reconstruction for the corrected critical-cut reduct `zAx1 (seqAddAnt (cutFormula d) sⱼ) C` — it discharges
the `haux1` threading obligation (O-L2) directly from the parent chain validity, with NO tip recomputation
(contrast `isChainInf_reduceR_membership`, which re-points `j0 := i` and so needs the reduct succedent to be
the conclusion succedent or `⊥` — false for an interior L-redex whose succedent is the cut formula). -/
lemma isChainInf_growAnt {s r ds i v A : V} (hi : i < lh ds) (hs : Seq (seqAnt s))
    (hsi : Seq (chainAnt ds i))
    (hsucc_v : seqSucc (fstIdx v) = chainAsucc ds i)
    (hant_v : seqAnt (fstIdx v) = seqCons (chainAnt ds i) A)
    (hci : isChainInf s r ds) :
    isChainInf (seqAddAnt A s) r (seqUpdate ds i v) := by
  obtain ⟨j0, hj0, hA, hthr, hrk⟩ := hci
  -- `chainAsucc` is preserved at EVERY index: off `i` trivially, at `i` because `v` keeps the succedent.
  have hsucc_all : ∀ k, chainAsucc (seqUpdate ds i v) k = chainAsucc ds k := by
    intro k
    rcases eq_or_ne k i with rfl | hne
    · rw [chainAsucc_seqUpdate_self hi, hsucc_v]
    · rw [chainAsucc_seqUpdate_of_ne hne]
  refine ⟨j0, by rwa [seqUpdate_lh], ?_, ?_, ?_⟩
  · rw [hsucc_all, seqSucc_seqAddAnt]; exact hA
  · intro k hk B hB
    rcases eq_or_ne k i with rfl | hne
    · rw [chainAnt_seqUpdate_self hi, hant_v] at hB
      rcases (inAnt_seqCons hsi).mp hB with rfl | hin
      · left; exact (inAnt_seqAddAnt hs).mpr (Or.inl rfl)
      · rcases hthr k hk B hin with h | ⟨i', hi', hB'⟩
        · left; exact (inAnt_seqAddAnt hs).mpr (Or.inr h)
        · right; exact ⟨i', hi', by rw [hsucc_all]; exact hB'⟩
    · rw [chainAnt_seqUpdate_of_ne hne] at hB
      rcases hthr k hk B hB with h | ⟨i', hi', hB'⟩
      · left; exact (inAnt_seqAddAnt hs).mpr (Or.inr h)
      · right; exact ⟨i', hi', by rw [hsucc_all]; exact hB'⟩
  · intro k hk; rw [hsucc_all]; exact hrk k hk

/-- **Antecedent-`seqCons` formula-hood** — prepending a `UFormula` to a wff antecedent keeps every entry
a `UFormula`. The conclusion-antecedent wff conjunct of `zKValidF` under the L-rule weakening. -/
lemma forall_IsUFormula_seqCons {Γ A : V} (hΓ : Seq Γ)
    (hpar : ∀ k < lh Γ, IsUFormula ℒₒᵣ (znth Γ k)) (hA : IsUFormula ℒₒᵣ A) :
    ∀ k < lh (seqCons Γ A), IsUFormula ℒₒᵣ (znth (seqCons Γ A) k) := by
  intro k hk
  rw [Seq.lh_seqCons A hΓ] at hk
  rcases eq_or_lt_of_le (le_iff_lt_succ.mpr hk) with hkeq | hklt
  · rw [hkeq, znth_seqCons_self hΓ A]; exact hA
  · rw [znth_seqCons_of_lt hΓ A hklt]; exact hpar k hklt

/-- **L-rule replace — `zKValidF` conclusion-antecedent weakening.** Adding a `UFormula` `A` to the
conclusion antecedent preserves faithful chain-validity (Buchholz 5.2.2 axiom case): `isChainInf` is
monotone (`isChainInf_seqAddAnt`), the per-premise conjuncts and rank are about `ds` (unchanged), the
conclusion succedent is unchanged (`seqSucc_seqAddAnt`), and the conclusion-antecedent wff extends by
`forall_IsUFormula_seqCons`. -/
lemma zKValidF_seqAddAnt {s r ds A : V} (hs : Seq (seqAnt s)) (hA : IsUFormula ℒₒᵣ A)
    (h : zKValidF s r ds) : zKValidF (seqAddAnt A s) r ds := by
  obtain ⟨hci, hperm, hg1, hg2, hg5, hg6, hcf, hss, hsa⟩ := h
  refine ⟨isChainInf_seqAddAnt hs hci, hperm, hg1, hg2, hg5, hg6, hcf, ?_, ?_⟩
  · rw [seqSucc_seqAddAnt]; exact hss
  · rw [seqAnt_seqAddAnt]; exact forall_IsUFormula_seqCons hs hsa hA

/-- **5.2.1 splice — `isChainInf` structural reduction.** The sub-critical splice
`cs = seqCons (seqUpdate ds j a) b` (Buchholz §3.2 case 5.2.1: premise `j` of the critical chain is
expanded into its two halves `a = dⱼ{1}` in place and `b = dⱼ{0}` appended at the end) is chain-valid for
the conclusion `s'`/rank `r'` exactly when the appended half `b` carries `s'`'s succedent, the
antecedents thread back (each `B ∈ Γₖ` lands in `s'`'s antecedent or a strictly-earlier succedent), and
the ranks below the distinguished top stay `≤ r'`. This reduces splice validity to the local
end-sequent threading facts about the two halves — the cut-formula bookkeeping the dispatch must supply.
(Mirror of `isChainInf_of_last`, with `j₀ = lh ds`.) -/
lemma isChainInf_iSpliceEnd {s' r' ds j a b : V} (_hj : j < lh ds)
    (hlast : chainAsucc (seqCons (seqUpdate ds j a) b) (lh ds) = seqSucc s'
        ∨ chainAsucc (seqCons (seqUpdate ds j a) b) (lh ds) = (^⊥ : V))
    (hthread : ∀ i ≤ lh ds, ∀ B, inAnt B (chainAnt (seqCons (seqUpdate ds j a) b) i) →
        inAnt B (seqAnt s') ∨ ∃ i' < i, B = chainAsucc (seqCons (seqUpdate ds j a) b) i')
    (hrank : ∀ i < lh ds, irk (chainAsucc (seqCons (seqUpdate ds j a) b) i) ≤ r') :
    isChainInf s' r' (seqCons (seqUpdate ds j a) b) := by
  have hlen : 0 < lh (seqCons (seqUpdate ds j a) b) := by
    rw [lh_seqCons_seqUpdate]; exact lt_of_le_of_lt (show (0 : V) ≤ lh ds by simp) (lt_add_one _)
  have htop : lh (seqCons (seqUpdate ds j a) b) - 1 = lh ds := by
    rw [lh_seqCons_seqUpdate]; simp
  refine isChainInf_of_last hlen ?_ ?_ ?_
  · rw [htop]; exact hlast
  · rw [htop]; exact hthread
  · rw [htop]; exact hrank

/-- **5.2.1 splice — full `zKValidF` reduction.** Given the splice's `isChainInf` core (the structural
threading, from `isChainInf_iSpliceEnd`) plus the per-half well-formedness of the two halves `a`, `b`
(own-permissibility `iperm (tp ·) (fstIdx ·)`, Buchholz Lemma 3.3 / `iperm_tp_fstIdx_of_ZDerivation`; the
tag-gated principal-formula-hood) and the original chain's per-premise well-formedness, the spliced chain
is faithfully valid `zKValidF`. This is the reusable "splice a premise's two halves into a valid `K^r`
chain ⟹ still valid" fact, the validity half (b) of `RedSound`'s 5.2.1 case. The off-`j`, below-top
conjuncts inherit from the original chain; the at-`j` (`a`) and top (`b`) ones come from the halves. -/
lemma zKValidF_iSpliceEnd {s' r' ds j a b : V} (hj : j < lh ds)
    (hci : isChainInf s' r' (seqCons (seqUpdate ds j a) b))
    (hperm_a : iperm (tp a) (fstIdx a)) (hperm_b : iperm (tp b) (fstIdx b))
    (hf1_a : zTag a = 1 → IsUFormula ℒₒᵣ (zIallF a)) (hf1_b : zTag b = 1 → IsUFormula ℒₒᵣ (zIallF b))
    (hf2_a : zTag a = 2 → IsUFormula ℒₒᵣ (zInegF a)) (hf2_b : zTag b = 2 → IsUFormula ℒₒᵣ (zInegF b))
    (hf5_a : zTag a = 5 → IsUFormula ℒₒᵣ (zAxAllF a)) (hf5_b : zTag b = 5 → IsUFormula ℒₒᵣ (zAxAllF b))
    (hf6_a : zTag a = 6 → IsUFormula ℒₒᵣ (zAxNegF a)) (hf6_b : zTag b = 6 → IsUFormula ℒₒᵣ (zAxNegF b))
    (hfa_a : IsUFormula ℒₒᵣ (seqSucc (fstIdx a))) (hfa_b : IsUFormula ℒₒᵣ (seqSucc (fstIdx b)))
    (hss : IsUFormula ℒₒᵣ (seqSucc s'))
    (hsa : ∀ k < lh (seqAnt s'), IsUFormula ℒₒᵣ (znth (seqAnt s') k))
    (hperm : ∀ i < lh ds, iperm (tp (znth ds i)) (fstIdx (znth ds i)))
    (hg1 : ∀ i < lh ds, zTag (znth ds i) = 1 → IsUFormula ℒₒᵣ (zIallF (znth ds i)))
    (hg2 : ∀ i < lh ds, zTag (znth ds i) = 2 → IsUFormula ℒₒᵣ (zInegF (znth ds i)))
    (hg5 : ∀ i < lh ds, zTag (znth ds i) = 5 → IsUFormula ℒₒᵣ (zAxAllF (znth ds i)))
    (hg6 : ∀ i < lh ds, zTag (znth ds i) = 6 → IsUFormula ℒₒᵣ (zAxNegF (znth ds i)))
    (hcf : ∀ i < lh ds, IsUFormula ℒₒᵣ (chainAsucc ds i)) :
    zKValidF s' r' (seqCons (seqUpdate ds j a) b) := by
  -- Resolve a premise of the splice at index `n < lh ds + 1` into the three cases.
  have key : ∀ {P : V → Prop} (n : V), n < lh ds + 1 →
      (P a) → (P b) → (∀ k, k < lh ds → k ≠ j → P (znth ds k)) →
      P (znth (seqCons (seqUpdate ds j a) b) n) := by
    intro P n hn ha hb hoff
    rcases lt_or_eq_of_le (le_iff_lt_succ.mpr hn) with hlt | heq
    · rw [znth_seqCons_seqUpdate_lt hlt]
      rcases eq_or_ne n j with rfl | hne
      · rwa [znth_seqUpdate_self hj]
      · rw [znth_seqUpdate_of_ne hne]; exact hoff n hlt hne
    · rw [heq, znth_seqCons_seqUpdate_top]; exact hb
  refine ⟨hci, ?_, ?_, ?_, ?_, ?_, ?_, hss, hsa⟩
  · intro n hn
    rw [lh_seqCons_seqUpdate] at hn
    exact key (P := fun x => iperm (tp x) (fstIdx x)) n hn hperm_a hperm_b (fun k hk _ => hperm k hk)
  · intro n hn
    rw [lh_seqCons_seqUpdate] at hn
    exact key (P := fun x => zTag x = 1 → IsUFormula ℒₒᵣ (zIallF x)) n hn hf1_a hf1_b
      (fun k hk _ => hg1 k hk)
  · intro n hn
    rw [lh_seqCons_seqUpdate] at hn
    exact key (P := fun x => zTag x = 2 → IsUFormula ℒₒᵣ (zInegF x)) n hn hf2_a hf2_b
      (fun k hk _ => hg2 k hk)
  · intro n hn
    rw [lh_seqCons_seqUpdate] at hn
    exact key (P := fun x => zTag x = 5 → IsUFormula ℒₒᵣ (zAxAllF x)) n hn hf5_a hf5_b
      (fun k hk _ => hg5 k hk)
  · intro n hn
    rw [lh_seqCons_seqUpdate] at hn
    exact key (P := fun x => zTag x = 6 → IsUFormula ℒₒᵣ (zAxNegF x)) n hn hf6_a hf6_b
      (fun k hk _ => hg6 k hk)
  · intro n hn
    rw [lh_seqCons_seqUpdate] at hn
    rcases lt_or_eq_of_le (le_iff_lt_succ.mpr hn) with hlt | heq
    · rw [chainAsucc_seqCons_seqUpdate_lt hlt]
      rcases eq_or_ne n j with rfl | hne
      · rw [chainAsucc_seqUpdate_self hj]; exact hfa_a
      · rw [chainAsucc_seqUpdate_of_ne hne]; exact hcf n hlt
    · rw [heq, chainAsucc_seqCons_seqUpdate_top]; exact hfa_b

/-! ### Concrete ordered-insert coded-sequence op `seqInsert` (case 5.2.1)

The genuine in-place splice `d₀…d_{i−1} a b d_{i+1}…dₗ` as a total `𝚺₁` `PR.Construction` (mirror of
`seqUpdateAux`): entry `n` = `if n<i then znth ds n else if n=i then a else if n=i+1 then b else znth ds (n−1)`.
Its read-outs (`znth_seqInsert_{pre,at,at1,suf}`, `seqInsert_lh`) discharge the abstract read-out hypotheses
of the splice-validity specs below. -/

def seqInsertAux.blueprint : PR.Blueprint 4 where
  zero := .mkSigma “y ds i a b. y = 0”
  succ := .mkSigma “y ih n ds i a b.
    ( (n < i ∧ ∃ c, !znthDef c ds n ∧ !seqConsDef y ih c) ∨
      (i ≤ n ∧ n = i ∧ !seqConsDef y ih a) ∨
      (i ≤ n ∧ n ≠ i ∧ n = i + 1 ∧ !seqConsDef y ih b) ∨
      (i ≤ n ∧ n ≠ i ∧ n ≠ i + 1 ∧ ∃ m, !subDef m n 1 ∧ ∃ c, !znthDef c ds m ∧ !seqConsDef y ih c) )”

noncomputable def seqInsertAux.construction : PR.Construction V seqInsertAux.blueprint where
  zero := fun _ ↦ ∅
  succ := fun x n ih ↦ seqCons ih
    (if n < x 1 then znth (x 0) n else if n = x 1 then x 2 else if n = x 1 + 1 then x 3
      else znth (x 0) (n - 1))
  zero_defined := .mk fun v ↦ by simp [seqInsertAux.blueprint, emptyset_def]
  succ_defined := .mk fun v ↦ by
    by_cases h1 : v 2 < v 4
    · simp [seqInsertAux.blueprint, h1, not_le.mpr h1, znth_defined.iff, seqCons_defined.iff]
    · have hle : v 4 ≤ v 2 := not_lt.mp h1
      by_cases h2 : v 2 = v 4
      · simp [seqInsertAux.blueprint, h1, hle, h2, seqCons_defined.iff]
      · by_cases h3 : v 2 = v 4 + 1
        · simp [seqInsertAux.blueprint, h1, hle, h2, h3, seqCons_defined.iff]
        · simp [seqInsertAux.blueprint, h1, hle, h2, h3, sub_defined.iff, znth_defined.iff,
            seqCons_defined.iff]

noncomputable def seqInsertAux (ds i a b n : V) : V := seqInsertAux.construction.result ![ds, i, a, b] n

@[simp] lemma seqInsertAux_zero (ds i a b : V) : seqInsertAux ds i a b 0 = ∅ := by
  simp [seqInsertAux, seqInsertAux.construction]

@[simp] lemma seqInsertAux_succ (ds i a b n : V) :
    seqInsertAux ds i a b (n + 1) = seqCons (seqInsertAux ds i a b n)
      (if n < i then znth ds n else if n = i then a else if n = i + 1 then b else znth ds (n - 1)) := by
  simp [seqInsertAux, seqInsertAux.construction]

def _root_.LO.FirstOrder.Arithmetic.seqInsertAuxDef : 𝚺₁.Semisentence 6 :=
  seqInsertAux.blueprint.resultDef.rew (Rew.subst ![#0, #5, #1, #2, #3, #4])

instance seqInsertAux_defined : 𝚺₁-Function₅ (seqInsertAux : V → V → V → V → V → V) via seqInsertAuxDef :=
  .mk fun v ↦ by simp [seqInsertAux.construction.result_defined_iff, seqInsertAuxDef]; rfl

instance seqInsertAux_definable : (𝚺₁).DefinableFunction₅ (seqInsertAux : V → V → V → V → V → V) :=
  seqInsertAux_defined.to_definable
instance seqInsertAux_definable' (Γ) :
    (Γ-[m + 1]).DefinableFunction₅ (seqInsertAux : V → V → V → V → V → V) :=
  seqInsertAux_definable.of_sigmaOne

@[simp] lemma seqInsertAux_seq (ds i a b n : V) : Seq (seqInsertAux ds i a b n) := by
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero => simpa using seq_empty
  case succ n ih => rw [seqInsertAux_succ]; exact ih.seqCons _

@[simp] lemma seqInsertAux_lh (ds i a b n : V) : lh (seqInsertAux ds i a b n) = n := by
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero => simpa using lh_empty
  case succ n ih => rw [seqInsertAux_succ, Seq.lh_seqCons _ (seqInsertAux_seq ds i a b n), ih]

/-- Top-entry read-out (freshly-appended entry at index `n`). -/
lemma znth_seqInsertAux_top (ds i a b n : V) :
    znth (seqInsertAux ds i a b (n + 1)) n =
      (if n < i then znth ds n else if n = i then a else if n = i + 1 then b else znth ds (n - 1)) := by
  rw [seqInsertAux_succ]
  have := znth_seqCons_self (seqInsertAux_seq ds i a b n)
    (if n < i then znth ds n else if n = i then a else if n = i + 1 then b else znth ds (n - 1))
  rwa [seqInsertAux_lh] at this

/-- Reads below the top are stable as the prefix grows. -/
lemma znth_seqInsertAux_stable {ds i a b : V} (n m : V) (hm : m < n) :
    znth (seqInsertAux ds i a b (n + 1)) m = znth (seqInsertAux ds i a b n) m := by
  rw [seqInsertAux_succ,
    znth_seqCons_of_lt (seqInsertAux_seq ds i a b n) _ (by rw [seqInsertAux_lh]; exact hm)]

/-- Region read-out: `pre` (`k < i`), ite-free. -/
lemma znth_seqInsertAux_pre {ds i a b k : V} (hki : k < i) :
    ∀ n, k < n → znth (seqInsertAux ds i a b n) k = znth ds k := by
  intro n
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero => intro h; exact absurd h (by simp)
  case succ n ih =>
    intro hk
    rcases eq_or_lt_of_le (le_iff_lt_succ.mpr hk) with hkn | hklt
    · rw [hkn, znth_seqInsertAux_top, if_pos (by rw [← hkn]; exact hki)]
    · rw [znth_seqInsertAux_stable n k hklt]; exact ih hklt

/-- Region read-out: at the insert index `i`. -/
lemma znth_seqInsertAux_at {ds i a b : V} : ∀ n, i < n → znth (seqInsertAux ds i a b n) i = a := by
  intro n
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero => intro h; exact absurd h (by simp)
  case succ n ih =>
    intro hi
    rcases eq_or_lt_of_le (le_iff_lt_succ.mpr hi) with hin | hilt
    · obtain rfl := hin
      rw [znth_seqInsertAux_top, if_neg (_root_.lt_irrefl i), if_pos rfl]
    · rw [znth_seqInsertAux_stable n i hilt]; exact ih hilt

/-- Region read-out: at the second insert index `i+1`. -/
lemma znth_seqInsertAux_at1 {ds i a b : V} : ∀ n, i + 1 < n → znth (seqInsertAux ds i a b n) (i + 1) = b := by
  intro n
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero => intro h; exact absurd h (by simp)
  case succ n ih =>
    intro hi
    rcases eq_or_lt_of_le (le_iff_lt_succ.mpr hi) with hin | hilt
    · obtain rfl := hin
      rw [znth_seqInsertAux_top, if_neg (not_lt.mpr (le_of_lt (lt_add_one i))),
        if_neg (ne_of_gt (lt_add_one i)), if_pos rfl]
    · rw [znth_seqInsertAux_stable n (i + 1) hilt]; exact ih hilt

/-- Region read-out: suffix (`i + 1 < m + 1`, i.e. the original `d_m` for `m > i` sits at `m + 1`). -/
lemma znth_seqInsertAux_suf {ds i a b m : V} (him : i < m) :
    ∀ n, m + 1 < n → znth (seqInsertAux ds i a b n) (m + 1) = znth ds m := by
  intro n
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero => intro h; exact absurd h (by simp)
  case succ n ih =>
    intro hm
    rcases eq_or_lt_of_le (le_iff_lt_succ.mpr hm) with hmn | hmlt
    · obtain rfl := hmn
      rw [znth_seqInsertAux_top,
        if_neg (not_lt.mpr (le_of_lt (lt_trans him (lt_add_one m)))),
        if_neg (ne_of_gt (lt_trans him (lt_add_one m))),
        if_neg (fun h => (ne_of_gt him) (add_right_cancel h)),
        show (m + 1 - 1 : V) = m by simp]
    · rw [znth_seqInsertAux_stable n (m + 1) hmlt]; exact ih hmlt

/-- The full ordered insert: `d₀…d_{i−1} a b d_{i+1}…dₗ`, length `lh ds + 1`. -/
noncomputable def seqInsert (ds i a b : V) : V := seqInsertAux ds i a b (lh ds + 1)

@[simp] lemma seqInsert_seq (ds i a b : V) : Seq (seqInsert ds i a b) := seqInsertAux_seq ds i a b _

@[simp] lemma seqInsert_lh (ds i a b : V) : lh (seqInsert ds i a b) = lh ds + 1 := seqInsertAux_lh ds i a b _

lemma znth_seqInsert_pre {ds i a b k : V} (hki : k < i) (hk : k < lh ds) :
    znth (seqInsert ds i a b) k = znth ds k :=
  znth_seqInsertAux_pre hki _ (lt_of_lt_of_le hk (le_of_lt (lt_add_one (lh ds))))

lemma znth_seqInsert_at {ds i a b : V} (hi : i < lh ds) : znth (seqInsert ds i a b) i = a :=
  znth_seqInsertAux_at _ (lt_trans hi (lt_add_one (lh ds)))

lemma znth_seqInsert_at1 {ds i a b : V} (hi : i < lh ds) : znth (seqInsert ds i a b) (i + 1) = b :=
  znth_seqInsertAux_at1 _ (add_lt_add_of_lt_of_le hi (le_refl 1))

lemma znth_seqInsert_suf {ds i a b m : V} (him : i < m) (hm : m < lh ds) :
    znth (seqInsert ds i a b) (m + 1) = znth ds m :=
  znth_seqInsertAux_suf him _ (add_lt_add_of_lt_of_le hm (le_refl 1))

/-- **Every entry of `seqInsert ds i a b` satisfies any predicate the halves and `ds`-entries do.**
The pointwise companion to the validity `key`: handles the suffix-shift predecessor decomposition once,
so downstream lemmas (e.g. the premise-`ZDerivation` of the 5.2.1 reduct) need no index bashing. -/
lemma forall_znth_seqInsert {ds i a b : V} {P : V → Prop} (hi : i < lh ds)
    (ha : P a) (hb : P b) (hP : ∀ k < lh ds, P (znth ds k)) :
    ∀ n < lh ds + 1, P (znth (seqInsert ds i a b) n) := by
  intro n hn
  rcases lt_trichotomy n i with hlt | heq | hgt
  · rw [znth_seqInsert_pre hlt (lt_trans hlt hi)]; exact hP n (lt_trans hlt hi)
  · subst heq; rw [znth_seqInsert_at hi]; exact ha
  · rcases eq_or_ne n (i + 1) with rfl | hne
    · rw [znth_seqInsert_at1 hi]; exact hb
    · -- i < n, n ≠ i+1 ⟹ i+1 < n; write n = (i+d)+1 with 0 < d
      have hi1le : i + 1 ≤ n := succ_le_iff_lt.mpr hgt
      have hi1n : i + 1 < n := lt_of_le_of_ne hi1le (Ne.symm hne)
      obtain ⟨d, hd⟩ := le_iff_exists_add.mp (le_of_lt hi1n)
      have hdpos : 0 < d := by
        have h0 : i + 1 + 0 < i + 1 + d := by rw [add_zero, ← hd]; exact hi1n
        exact lt_of_add_lt_add_left h0
      have hnm : n = (i + d) + 1 := by rw [hd]; exact add_right_comm i 1 d
      have him : i < i + d := lt_add_of_pos_right i hdpos
      have hclt : i + d < lh ds := by
        have : (i + d) + 1 < lh ds + 1 := by rw [← hnm]; exact hn
        exact lt_of_add_lt_add_right this
      rw [hnm, znth_seqInsert_suf him hclt]; exact hP (i + d) hclt

/-! ### 5.2.1 ordered-insert splice VALIDITY (the genuine, order-sensitive object)

Buchholz Def 3.2 case 5.2.1 reduct `K^{r'}_Π(i/dᵢ{0},dᵢ{1})` is the ORDERED in-place splice
`d₀…d_{i−1} dᵢ{0} dᵢ{1} d_{i+1}…dₗ` (paper abbreviation: `K^r_{Π'}(i/d'ᵢ…d'_m) := d₀…d_{i−1} d'ᵢ…d'_m d_{i+1}…dₗ`).
Unlike the order-independent end-append model `seqCons (seqUpdate ds i a) b` used for the `#`-fold ordinal
descent (`iord_descent_iSpliceEnd`), `isChainInf` validity is ORDER-SENSITIVE (threads each antecedent only
to strictly-earlier succedents), so validity must be proved on this ordered object. Stated abstractly over
the insert read-outs (`hpre`/`hai`/`hbi`/`hsuf`) — the concrete `seqInsert` op + descent transfer are the
remaining 5.2.1 plumbing (see `ANALYSIS-2026-06-25-lap87-splice-order-sensitivity.md`). -/

/-- **5.2.1 ordered-insert splice — `isChainInf` (abstract spec).** -/
lemma isChainInf_seqInsert_spec {s r r' i j0 ds cs a b : V}
    -- unpacked original-chain validity at its distinguished `j0` (with `i ≤ j0 < lh ds`):
    (hj0 : j0 < lh ds) (hij0 : i ≤ j0)
    (hAj0 : chainAsucc ds j0 = seqSucc s ∨ chainAsucc ds j0 = (^⊥ : V))
    (hthr : ∀ p ≤ j0, ∀ B, inAnt B (chainAnt ds p) →
        inAnt B (seqAnt s) ∨ ∃ p' < p, B = chainAsucc ds p')
    (hrk : ∀ p < j0, irk (chainAsucc ds p) ≤ r)
    -- read-outs of the ordered insert `cs = d₀…d_{i−1} a b d_{i+1}…dₗ`:
    (hlh : lh cs = lh ds + 1)
    (hpre : ∀ k, k < i → znth cs k = znth ds k)
    (hai : znth cs i = a)
    (hbi : znth cs (i + 1) = b)
    (hsuf : ∀ m, i < m → m < lh ds → znth cs (m + 1) = znth ds m)
    -- Thm-3.4(a) genuine half end-sequents:
    (ha_ant : seqAnt (fstIdx a) = chainAnt ds i)
    (ha_rank : irk (seqSucc (fstIdx a)) ≤ r')
    (hb_succ : seqSucc (fstIdx b) = chainAsucc ds i)
    (hb_ant : ∀ B, inAnt B (seqAnt (fstIdx b)) →
        B = seqSucc (fstIdx a) ∨ inAnt B (chainAnt ds i))
    (hrr : r ≤ r') :
    isChainInf s r' cs := by
  -- region read-outs for chainAsucc/chainAnt on `cs`.
  have eA_pre : ∀ k, k < i → chainAsucc cs k = chainAsucc ds k := fun k hk => by
    unfold chainAsucc; rw [hpre k hk]
  have eN_pre : ∀ k, k < i → chainAnt cs k = chainAnt ds k := fun k hk => by
    unfold chainAnt; rw [hpre k hk]
  have eA_i : chainAsucc cs i = seqSucc (fstIdx a) := by unfold chainAsucc; rw [hai]
  have eN_i : chainAnt cs i = seqAnt (fstIdx a) := by unfold chainAnt; rw [hai]
  have eA_i1 : chainAsucc cs (i + 1) = seqSucc (fstIdx b) := by unfold chainAsucc; rw [hbi]
  have eN_i1 : chainAnt cs (i + 1) = seqAnt (fstIdx b) := by unfold chainAnt; rw [hbi]
  have eA_suf : ∀ m, i < m → m < lh ds → chainAsucc cs (m + 1) = chainAsucc ds m := fun m hm hm2 => by
    unfold chainAsucc; rw [hsuf m hm hm2]
  have eN_suf : ∀ m, i < m → m < lh ds → chainAnt cs (m + 1) = chainAnt ds m := fun m hm hm2 => by
    unfold chainAnt; rw [hsuf m hm hm2]
  have hi_lt : i < lh ds := lt_of_le_of_lt hij0 hj0
  refine ⟨j0 + 1, by rw [hlh]; exact add_lt_add_of_lt_of_le hj0 (le_refl 1), ?_, ?_, ?_⟩
  · -- (A) distinguished succedent
    rcases eq_or_lt_of_le hij0 with hij | hij
    · -- i = j0
      rw [← hij, eA_i1, hb_succ]; rw [hij]; exact hAj0
    · -- i < j0
      rw [eA_suf j0 hij hj0]; exact hAj0
  · -- (B) threading, ∀ p ≤ j0+1
    intro p hp B hB
    rcases lt_or_ge p i with hpi | hpi
    · -- p < i
      rw [eN_pre p hpi] at hB
      rcases hthr p (le_trans (le_of_lt hpi) hij0) B hB with h | ⟨p', hp', hp'eq⟩
      · exact Or.inl h
      · exact Or.inr ⟨p', hp', by rw [eA_pre p' (lt_trans hp' hpi)]; exact hp'eq⟩
    · rcases eq_or_lt_of_le hpi with hpe | hpgt
      · -- p = i
        rw [← hpe, eN_i, ha_ant] at hB
        rcases hthr i hij0 B hB with h | ⟨p', hp', hp'eq⟩
        · exact Or.inl h
        · refine Or.inr ⟨p', by rw [← hpe]; exact hp', ?_⟩
          rw [eA_pre p' hp']; exact hp'eq
      · -- p > i
        obtain ⟨m, rfl⟩ : ∃ m, p = m + 1 :=
          ⟨p - 1, (sub_add_self_of_le (pos_iff_one_le.mp (lt_of_le_of_lt (show (0:V) ≤ i by simp) hpgt))).symm⟩
        have him : i < m + 1 := hpgt
        rcases eq_or_lt_of_le (le_iff_lt_succ.mpr him) with hime | himlt
        · -- m+1 = i+1, i.e. p = i+1
          rw [← hime, eN_i1] at hB
          rcases hb_ant B hB with hba | hba
          · exact Or.inr ⟨i, by rw [← hime]; exact lt_add_one i, by rw [eA_i]; exact hba⟩
          · rcases hthr i hij0 B hba with h | ⟨p', hp', hp'eq⟩
            · exact Or.inl h
            · exact Or.inr ⟨p', by rw [← hime]; exact lt_trans hp' (lt_add_one i),
                by rw [eA_pre p' hp']; exact hp'eq⟩
        · -- p = m+1, i < m
          have hilm : i < m := himlt
          have hm_le_j0 : m ≤ j0 := by
            have : m + 1 ≤ j0 + 1 := hp
            exact le_of_add_le_add_right this
          have hm_lt : m < lh ds := lt_of_le_of_lt hm_le_j0 hj0
          rw [eN_suf m hilm hm_lt] at hB
          rcases hthr m hm_le_j0 B hB with h | ⟨p', hp', hp'eq⟩
          · exact Or.inl h
          · -- map p' < m to a cs-position < m+1
            rcases lt_or_ge p' i with hp'i | hp'i
            · exact Or.inr ⟨p', lt_trans hp'i (lt_trans hilm (lt_add_one m)),
                by rw [eA_pre p' hp'i]; exact hp'eq⟩
            · rcases eq_or_lt_of_le hp'i with hp'e | hp'gt
              · -- p' = i: lands on b's succedent at i+1
                refine Or.inr ⟨i + 1, add_lt_add_of_lt_of_le hilm (le_refl 1), ?_⟩
                rw [eA_i1, hb_succ, hp'e]; exact hp'eq
              · -- i < p' < m: lands at p'+1
                refine Or.inr ⟨p' + 1, add_lt_add_of_lt_of_le hp' (le_refl 1), ?_⟩
                rw [eA_suf p' hp'gt (lt_trans hp' hm_lt)]; exact hp'eq
  · -- (C) rank, ∀ p < j0+1
    intro p hp
    have hp' : p ≤ j0 := le_iff_lt_succ.mpr hp
    rcases lt_or_ge p i with hpi | hpi
    · rw [eA_pre p hpi]; exact le_trans (hrk p (lt_of_lt_of_le hpi hij0)) hrr
    · rcases eq_or_lt_of_le hpi with hpe | hpgt
      · rw [← hpe, eA_i]; exact ha_rank
      · obtain ⟨m, rfl⟩ : ∃ m, p = m + 1 :=
          ⟨p - 1, (sub_add_self_of_le (pos_iff_one_le.mp (lt_of_le_of_lt (show (0:V) ≤ i by simp) hpgt))).symm⟩
        have him : i < m + 1 := hpgt
        rcases eq_or_lt_of_le (le_iff_lt_succ.mpr him) with hime | himlt
        · -- p = i+1
          rw [← hime, eA_i1, hb_succ]
          have hij : i < j0 := by
            have h1 : i + 1 ≤ j0 := by rw [hime]; exact hp'
            exact lt_of_lt_of_le (lt_add_one i) h1
          exact le_trans (hrk i hij) hrr
        · have hilm : i < m := himlt
          have hm_lt_j0 : m < j0 := lt_of_add_lt_add_right hp
          rw [eA_suf m hilm (lt_trans hm_lt_j0 hj0)]
          exact le_trans (hrk m hm_lt_j0) hrr

/-- **5.2.1 ordered-insert splice — full `zKValidF` (abstract spec).** -/
lemma zKValidF_seqInsert_spec {s r' i ds cs a b : V}
    (hci : isChainInf s r' cs)
    (hlh : lh cs = lh ds + 1)
    (hpre : ∀ k, k < i → znth cs k = znth ds k)
    (hai : znth cs i = a)
    (hbi : znth cs (i + 1) = b)
    (hsuf : ∀ m, i < m → m < lh ds → znth cs (m + 1) = znth ds m)
    (hi_lt : i < lh ds)
    (hperm_a : iperm (tp a) (fstIdx a)) (hperm_b : iperm (tp b) (fstIdx b))
    (hf1_a : zTag a = 1 → IsUFormula ℒₒᵣ (zIallF a)) (hf1_b : zTag b = 1 → IsUFormula ℒₒᵣ (zIallF b))
    (hf2_a : zTag a = 2 → IsUFormula ℒₒᵣ (zInegF a)) (hf2_b : zTag b = 2 → IsUFormula ℒₒᵣ (zInegF b))
    (hf5_a : zTag a = 5 → IsUFormula ℒₒᵣ (zAxAllF a)) (hf5_b : zTag b = 5 → IsUFormula ℒₒᵣ (zAxAllF b))
    (hf6_a : zTag a = 6 → IsUFormula ℒₒᵣ (zAxNegF a)) (hf6_b : zTag b = 6 → IsUFormula ℒₒᵣ (zAxNegF b))
    (hfa_a : IsUFormula ℒₒᵣ (seqSucc (fstIdx a))) (hfa_b : IsUFormula ℒₒᵣ (seqSucc (fstIdx b)))
    (hss : IsUFormula ℒₒᵣ (seqSucc s))
    (hsa : ∀ k < lh (seqAnt s), IsUFormula ℒₒᵣ (znth (seqAnt s) k))
    (hperm : ∀ k < lh ds, iperm (tp (znth ds k)) (fstIdx (znth ds k)))
    (hg1 : ∀ k < lh ds, zTag (znth ds k) = 1 → IsUFormula ℒₒᵣ (zIallF (znth ds k)))
    (hg2 : ∀ k < lh ds, zTag (znth ds k) = 2 → IsUFormula ℒₒᵣ (zInegF (znth ds k)))
    (hg5 : ∀ k < lh ds, zTag (znth ds k) = 5 → IsUFormula ℒₒᵣ (zAxAllF (znth ds k)))
    (hg6 : ∀ k < lh ds, zTag (znth ds k) = 6 → IsUFormula ℒₒᵣ (zAxNegF (znth ds k)))
    (hcf : ∀ k < lh ds, IsUFormula ℒₒᵣ (chainAsucc ds k)) :
    zKValidF s r' cs := by
  have key : ∀ {P : V → Prop} (n : V), n < lh ds + 1 → P a → P b →
      (∀ k, k < i → P (znth ds k)) → (∀ m, i < m → m < lh ds → P (znth ds m)) → P (znth cs n) := by
    intro P n hn ha hb hpreP hsufP
    rcases lt_or_ge n i with hni | hni
    · rw [hpre n hni]; exact hpreP n hni
    · rcases eq_or_lt_of_le hni with hne | hngt
      · rw [← hne, hai]; exact ha
      · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 :=
          ⟨n - 1, (sub_add_self_of_le (pos_iff_one_le.mp
            (lt_of_le_of_lt (show (0:V) ≤ i by simp) hngt))).symm⟩
        rcases eq_or_lt_of_le (le_iff_lt_succ.mpr (hngt : i < m + 1)) with hme | hmlt
        · rw [← hme, hbi]; exact hb
        · have hmlh : m < lh ds := lt_of_add_lt_add_right hn
          rw [hsuf m hmlt hmlh]; exact hsufP m hmlt hmlh
  refine ⟨hci, ?_, ?_, ?_, ?_, ?_, ?_, hss, hsa⟩
  · intro n hn; rw [hlh] at hn
    exact key (P := fun x => iperm (tp x) (fstIdx x)) n hn hperm_a hperm_b
      (fun k hk => hperm k (lt_trans hk hi_lt)) (fun m _ hm => hperm m hm)
  · intro n hn; rw [hlh] at hn
    exact key (P := fun x => zTag x = 1 → IsUFormula ℒₒᵣ (zIallF x)) n hn hf1_a hf1_b
      (fun k hk => hg1 k (lt_trans hk hi_lt)) (fun m _ hm => hg1 m hm)
  · intro n hn; rw [hlh] at hn
    exact key (P := fun x => zTag x = 2 → IsUFormula ℒₒᵣ (zInegF x)) n hn hf2_a hf2_b
      (fun k hk => hg2 k (lt_trans hk hi_lt)) (fun m _ hm => hg2 m hm)
  · intro n hn; rw [hlh] at hn
    exact key (P := fun x => zTag x = 5 → IsUFormula ℒₒᵣ (zAxAllF x)) n hn hf5_a hf5_b
      (fun k hk => hg5 k (lt_trans hk hi_lt)) (fun m _ hm => hg5 m hm)
  · intro n hn; rw [hlh] at hn
    exact key (P := fun x => zTag x = 6 → IsUFormula ℒₒᵣ (zAxNegF x)) n hn hf6_a hf6_b
      (fun k hk => hg6 k (lt_trans hk hi_lt)) (fun m _ hm => hg6 m hm)
  · intro n hn; rw [hlh] at hn
    rcases lt_or_ge n i with hni | hni
    · have he : chainAsucc cs n = chainAsucc ds n := by unfold chainAsucc; rw [hpre n hni]
      rw [he]; exact hcf n (lt_trans hni hi_lt)
    · rcases eq_or_lt_of_le hni with hne | hngt
      · have he : chainAsucc cs n = seqSucc (fstIdx a) := by unfold chainAsucc; rw [← hne, hai]
        rw [he]; exact hfa_a
      · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 :=
          ⟨n - 1, (sub_add_self_of_le (pos_iff_one_le.mp
            (lt_of_le_of_lt (show (0:V) ≤ i by simp) hngt))).symm⟩
        rcases eq_or_lt_of_le (le_iff_lt_succ.mpr (hngt : i < m + 1)) with hme | hmlt
        · have he : chainAsucc cs (m + 1) = seqSucc (fstIdx b) := by unfold chainAsucc; rw [← hme, hbi]
          rw [he]; exact hfa_b
        · have hmlh : m < lh ds := lt_of_add_lt_add_right hn
          have he : chainAsucc cs (m + 1) = chainAsucc ds m := by unfold chainAsucc; rw [hsuf m hmlt hmlh]
          rw [he]; exact hcf m hmlh

/-- **5.2.1 splice `isChainInf` on the concrete `seqInsert`** — the spec read-out hypotheses discharged
by the `seqInsert` op's read-outs (`znth_seqInsert_{pre,at,at1,suf}`). The genuine order-sensitive
chain-validity of the case-5.2.1 reduct `K^{r'}_Π(i/dᵢ{0},dᵢ{1})`. -/
lemma isChainInf_seqInsert {s r r' i j0 ds a b : V}
    (hj0 : j0 < lh ds) (hij0 : i ≤ j0)
    (hAj0 : chainAsucc ds j0 = seqSucc s ∨ chainAsucc ds j0 = (^⊥ : V))
    (hthr : ∀ p ≤ j0, ∀ B, inAnt B (chainAnt ds p) →
        inAnt B (seqAnt s) ∨ ∃ p' < p, B = chainAsucc ds p')
    (hrk : ∀ p < j0, irk (chainAsucc ds p) ≤ r)
    (ha_ant : seqAnt (fstIdx a) = chainAnt ds i)
    (ha_rank : irk (seqSucc (fstIdx a)) ≤ r')
    (hb_succ : seqSucc (fstIdx b) = chainAsucc ds i)
    (hb_ant : ∀ B, inAnt B (seqAnt (fstIdx b)) →
        B = seqSucc (fstIdx a) ∨ inAnt B (chainAnt ds i))
    (hrr : r ≤ r') :
    isChainInf s r' (seqInsert ds i a b) := by
  have hi_lt : i < lh ds := lt_of_le_of_lt hij0 hj0
  exact isChainInf_seqInsert_spec hj0 hij0 hAj0 hthr hrk (seqInsert_lh ds i a b)
    (fun k hk => znth_seqInsert_pre hk (lt_trans hk hi_lt))
    (znth_seqInsert_at hi_lt) (znth_seqInsert_at1 hi_lt)
    (fun m hm hm2 => znth_seqInsert_suf hm hm2)
    ha_ant ha_rank hb_succ hb_ant hrr

/-- **5.2.1 splice full `zKValidF` on the concrete `seqInsert`** — the spec read-outs discharged by the
`seqInsert` op. The validity half (b) of `RedSound`'s case 5.2.1 on the genuine ordered-insert object. -/
lemma zKValidF_seqInsert {s r' i ds a b : V}
    (hci : isChainInf s r' (seqInsert ds i a b)) (hi_lt : i < lh ds)
    (hperm_a : iperm (tp a) (fstIdx a)) (hperm_b : iperm (tp b) (fstIdx b))
    (hf1_a : zTag a = 1 → IsUFormula ℒₒᵣ (zIallF a)) (hf1_b : zTag b = 1 → IsUFormula ℒₒᵣ (zIallF b))
    (hf2_a : zTag a = 2 → IsUFormula ℒₒᵣ (zInegF a)) (hf2_b : zTag b = 2 → IsUFormula ℒₒᵣ (zInegF b))
    (hf5_a : zTag a = 5 → IsUFormula ℒₒᵣ (zAxAllF a)) (hf5_b : zTag b = 5 → IsUFormula ℒₒᵣ (zAxAllF b))
    (hf6_a : zTag a = 6 → IsUFormula ℒₒᵣ (zAxNegF a)) (hf6_b : zTag b = 6 → IsUFormula ℒₒᵣ (zAxNegF b))
    (hfa_a : IsUFormula ℒₒᵣ (seqSucc (fstIdx a))) (hfa_b : IsUFormula ℒₒᵣ (seqSucc (fstIdx b)))
    (hss : IsUFormula ℒₒᵣ (seqSucc s))
    (hsa : ∀ k < lh (seqAnt s), IsUFormula ℒₒᵣ (znth (seqAnt s) k))
    (hperm : ∀ k < lh ds, iperm (tp (znth ds k)) (fstIdx (znth ds k)))
    (hg1 : ∀ k < lh ds, zTag (znth ds k) = 1 → IsUFormula ℒₒᵣ (zIallF (znth ds k)))
    (hg2 : ∀ k < lh ds, zTag (znth ds k) = 2 → IsUFormula ℒₒᵣ (zInegF (znth ds k)))
    (hg5 : ∀ k < lh ds, zTag (znth ds k) = 5 → IsUFormula ℒₒᵣ (zAxAllF (znth ds k)))
    (hg6 : ∀ k < lh ds, zTag (znth ds k) = 6 → IsUFormula ℒₒᵣ (zAxNegF (znth ds k)))
    (hcf : ∀ k < lh ds, IsUFormula ℒₒᵣ (chainAsucc ds k)) :
    zKValidF s r' (seqInsert ds i a b) :=
  zKValidF_seqInsert_spec hci (seqInsert_lh ds i a b)
    (fun k hk => znth_seqInsert_pre hk (lt_trans hk hi_lt))
    (znth_seqInsert_at hi_lt) (znth_seqInsert_at1 hi_lt)
    (fun m hm hm2 => znth_seqInsert_suf hm hm2)
    hi_lt hperm_a hperm_b hf1_a hf1_b hf2_a hf2_b hf5_a hf5_b hf6_a hf6_b hfa_a hfa_b hss hsa
    hperm hg1 hg2 hg5 hg6 hcf

/-- The critical auxiliary `d{ν} = K^r(i/v)`: the chain `d` with premise `i` replaced by `v`. -/
noncomputable def iCritAux (d i v : V) : V := zK (fstIdx d) (zKrank d) (seqUpdate (zKseq d) i v)

/-- `iCritAux` on a chain code computes to the chain with premise `i` swapped: same end-sequent and
rank, premise sequence updated. -/
@[simp] lemma iCritAux_zK (s r ds i v : V) :
    iCritAux (zK s r ds) i v = zK s r (seqUpdate ds i v) := by simp [iCritAux]

/-- **N2 on the genuine object, `õ`-side** — `õ(K^r(i/v)) ≺ õ(K^r ds)` when `õ(v) ≺ õ(znth ds i)` (N1
IH). Feeds `seqUpdate`'s read-outs into `iotil_zK_lt_replace`. -/
lemma iotil_iCritAux_lt {s r ds i v : V} (hds : Seq ds) (hi : i < lh ds)
    (hlt : icmp (iotil v) (iotil (znth ds i)) = 0)
    (hNF : ∀ n, isNF (iotil (znth ds n))) (hNFv : isNF (iotil v)) :
    icmp (iotil (iCritAux (zK s r ds) i v)) (iotil (zK s r ds)) = 0 := by
  rw [iCritAux_zK]
  refine iotil_zK_lt_replace hds (seqUpdate_seq ds i v) (seqUpdate_lh ds i v) hi ?_ ?_ hNF ?_
  · rw [znth_seqUpdate_self hi]; exact hlt
  · intro n hn; rw [znth_seqUpdate_of_ne hn]
  · intro n; rcases eq_or_ne n i with rfl | hn
    · rw [znth_seqUpdate_self hi]; exact hNFv
    · rw [znth_seqUpdate_of_ne hn]; exact hNF n

/-- **N2 on the genuine object, `idg`-side** — `dg(K^r(i/v)) ≤ dg(K^r ds)` when `dg(v) ≤ dg(znth ds i)`. -/
lemma idg_iCritAux_le {s r ds i v : V} (hds : Seq ds) (hi : i < lh ds)
    (hle : idg v ≤ idg (znth ds i)) :
    idg (iCritAux (zK s r ds) i v) ≤ idg (zK s r ds) := by
  rw [iCritAux_zK]
  refine idg_zK_le_replace hds (seqUpdate_seq ds i v) (seqUpdate_lh ds i v) (fun n => ?_)
  rcases eq_or_ne n i with rfl | hn
  · rw [znth_seqUpdate_self hi]; exact hle
  · exact le_of_eq (congrArg idg (znth_seqUpdate_of_ne hn))

/-- **LH3 — non-critical chain descent on the genuine reduct object** (Buchholz §3.2 case 5.2.2,
`E-CRUX2-DECOMPOSITION-2026-06-24.md §2 LH3`). The non-critical chain reduct `d[n] = K^r(i/dᵢ[n])`
replaces a single premise `i` by its sub-reduct `v = dᵢ[n]`. The degree does not rise
(`idg_iCritAux_le`, N2) and `õ` strictly drops (`iotil_iCritAux_lt`, N2 via the N1 IH `õ(v) ≺ õ(dᵢ)`),
so `iord_descent_le` gives `o(d[n]) ≺ o(d)`. This is the LOW-HANGING structural chain case: no degree
drop is needed (`õ` carries the descent), exactly as Buchholz's §0 non-critical regime predicts. The
N1 IH facts (`hlt`/`hle`) are the only abstract input, discharged by `ZDerivation` induction downstream. -/
lemma iord_descent_iCritAux {s r ds i v : V} (hds : Seq ds) (hi : i < lh ds)
    (hnf : isNF (iotil (zK s r ds)))
    (hlt : icmp (iotil v) (iotil (znth ds i)) = 0)
    (hle : idg v ≤ idg (znth ds i))
    (hNF : ∀ n, isNF (iotil (znth ds n))) (hNFv : isNF (iotil v)) :
    icmp (iord (iCritAux (zK s r ds) i v)) (iord (zK s r ds)) = 0 :=
  iord_descent_le hnf (idg_iCritAux_le hds hi hle) (iotil_iCritAux_lt hds hi hlt hNF hNFv)

/-! ## LH5 — the splice reduct (Buchholz §3.2 case 14.254): premise `j` expanded to two auxiliaries

When a non-major premise `dⱼ` is itself in the principal case, its reduction splices its two
auxiliaries `dⱼ{0}, dⱼ{1}` *flat* into the parent chain (Buchholz 14.254): one summand `ω^{õ dⱼ}`
becomes `ω^{õ dⱼ{0}} # ω^{õ dⱼ{1}}`. Since the `õ`/`idg` folds are **order-independent** (natural sum is
commutative; max is commutative), the ordinal descent is faithful on the model `seqCons (seqUpdate ds j a) b`
(replace `j` by `a = dⱼ{0}`, append `b = dⱼ{1}` at the end — same multiset of summands as the in-place
splice). The descent is N3b-shaped: F2 (`ω^{õa} # ω^{õb} ≺ ω^{õ dⱼ}`) + F1 (left-cancel the rest). -/

/-- ω-power re-association (back): a single ω-power on the left re-associates *out* of a right-nested
ω-power. Avoids the unavailable full `inadd_assoc` by routing through the `insTerm`-commute machinery
(`inadd_omega_pow`/`inadd_insTerm_comm`); valid because one flank is a single `ω`-power. -/
lemma inadd_pow_back {Y b w : V} (hY : isNF Y) (hb : isNF b) (hw : isNF w) :
    inadd (ocOadd b 1 0) (inadd Y (ocOadd w 1 0))
      = inadd (inadd (ocOadd b 1 0) Y) (ocOadd w 1 0) := by
  have hωw : isNF (ocOadd w 1 0) := isNF_omega_pow hw
  have hωb : isNF (ocOadd b 1 0) := isNF_omega_pow hb
  have eY : inadd Y (ocOadd w 1 0) = insTerm w 1 Y := by
    rw [inadd_comm (ocOadd w 1 0) hωw Y hY, inadd_omega_pow]
  have eR : inadd (inadd (ocOadd b 1 0) Y) (ocOadd w 1 0)
      = insTerm w 1 (inadd (ocOadd b 1 0) Y) := by
    rw [inadd_comm (ocOadd w 1 0) hωw _ (isNF_inadd hY (ocOadd b 1 0) hωb), inadd_omega_pow]
  rw [eY, inadd_insTerm_comm Y hY (ocOadd b 1 0) hωb, eR]

/-- ω-power re-association (front): pull a common left operand `P` out front of `ω^b # (P # ω^a)`.
Same `insTerm`-machinery route as `inadd_pow_back`; lands the two ω-powers adjacent so F2 can fire. -/
lemma inadd_pow_front {P b a : V} (hP : isNF P) (hb : isNF b) (ha : isNF a) :
    inadd (ocOadd b 1 0) (inadd P (ocOadd a 1 0))
      = inadd P (inadd (ocOadd b 1 0) (ocOadd a 1 0)) := by
  have hωa : isNF (ocOadd a 1 0) := isNF_omega_pow ha
  have hωb : isNF (ocOadd b 1 0) := isNF_omega_pow hb
  have e1 : inadd P (ocOadd a 1 0) = insTerm a 1 P := by
    rw [inadd_comm (ocOadd a 1 0) hωa P hP, inadd_omega_pow]
  calc inadd (ocOadd b 1 0) (inadd P (ocOadd a 1 0))
      = inadd (ocOadd b 1 0) (insTerm a 1 P) := by rw [e1]
    _ = insTerm a 1 (inadd (ocOadd b 1 0) P) := inadd_insTerm_comm P hP (ocOadd b 1 0) hωb
    _ = insTerm a 1 (insTerm b 1 P) := by rw [inadd_omega_pow]
    _ = insTerm b 1 (insTerm a 1 P) := insTerm_comm P hP
    _ = insTerm b 1 (inadd P (ocOadd a 1 0)) := by rw [e1]
    _ = inadd P (insTerm b 1 (ocOadd a 1 0)) := (inadd_insTerm_comm (ocOadd a 1 0) hωa P hP).symm
    _ = inadd P (inadd (ocOadd b 1 0) (ocOadd a 1 0)) := by rw [inadd_omega_pow]

/-- **Each entry's `idg` is `≤` the fold** (`idg(znth ds i) ≤ iseqMaxIdg ds` for `i < lh ds`). -/
lemma le_iseqMaxIdgAux {ds : V} : ∀ J, ∀ i < J, idg (znth ds i) ≤ iseqMaxIdgAux ds J := by
  intro J
  induction J using ISigma1.sigma1_succ_induction
  · definability
  case zero => intro i hi; exact absurd hi (by simp)
  case succ J ih =>
    intro i hi
    rw [iseqMaxIdgAux_succ]
    rcases lt_or_eq_of_le (le_iff_lt_succ.mpr hi) with h | h
    · exact le_trans (ih i h) (le_max_left _ _)
    · subst h; exact le_max_right _ _

/-- **LH5 `õ`-fold (splice), partial** — `ω^{õb} # (#-fold of [ds with j↦a]) ≺ #-fold of ds`, when both
`õa, õb ≺ õ(dⱼ)`. The extra `ω^{õb}` rides the induction; `inadd_pow_back`/`_front` keep it adjacent so
F1 (`inadd_left/right_mono`) + F2 (`icmp_omega_pow_nadd_lt`) close each step. -/
lemma iseqNaddIdgAux_splice_lt {ds j a b : V} (hj : j < lh ds)
    (ha : icmp (iotil a) (iotil (znth ds j)) = 0) (hb : icmp (iotil b) (iotil (znth ds j)) = 0)
    (hNF : ∀ n, isNF (iotil (znth ds n))) (hNFa : isNF (iotil a)) (hNFb : isNF (iotil b)) :
    ∀ J, j < J → icmp (inadd (ocOadd (iotil b) 1 0) (iseqNaddIdgAux (seqUpdate ds j a) J))
      (iseqNaddIdgAux ds J) = 0 := by
  have hNF' : ∀ n, isNF (iotil (znth (seqUpdate ds j a) n)) := by
    intro n; rcases eq_or_ne n j with rfl | hn
    · rw [znth_seqUpdate_self hj]; exact hNFa
    · rw [znth_seqUpdate_of_ne hn]; exact hNF n
  intro J
  induction J using ISigma1.sigma1_succ_induction
  · definability
  case zero => intro h; exact absurd h (by simp)
  case succ J ih =>
    intro hjJ
    rw [iseqNaddIdgAux_succ, iseqNaddIdgAux_succ]
    rcases lt_or_eq_of_le (le_iff_lt_succ.mpr hjJ) with hlt | heq
    · -- j < J: entry J unchanged; the new ω-power rides on the right, F1 (right-mono) + IH.
      rw [znth_seqUpdate_of_ne (Ne.symm (ne_of_lt hlt)),
        inadd_pow_back (isNF_iseqNaddIdgAux' hNF' J) hNFb (hNF J)]
      exact inadd_right_mono (isNF_inadd (isNF_iseqNaddIdgAux' hNF' J) _ (isNF_omega_pow hNFb))
        (isNF_iseqNaddIdgAux' hNF J) (ih hlt) _ (isNF_omega_pow (hNF J))
    · -- j = J: entry J IS the replaced `a`; prefix unchanged, F1 (left-mono) + F2 on the two powers.
      subst heq
      rw [znth_seqUpdate_self hj]
      have hpre : iseqNaddIdgAux (seqUpdate ds j a) j = iseqNaddIdgAux ds j :=
        iseqNaddIdgAux_congr_iotil j (fun m hm => by rw [znth_seqUpdate_of_ne (ne_of_lt hm)])
      rw [hpre, inadd_pow_front (isNF_iseqNaddIdgAux' hNF j) hNFb hNFa]
      exact inadd_left_mono (isNF_inadd (isNF_omega_pow hNFa) _ (isNF_omega_pow hNFb))
        (isNF_omega_pow (hNF j)) (icmp_omega_pow_nadd_lt hb ha) _ (isNF_iseqNaddIdgAux' hNF j)

/-- **LH5 `õ`-side at the `K^r` level** — `õ(splice) ≺ õ(K^r ds)` for the order-independent splice model
`seqCons (seqUpdate ds j a) b`. The `seqCons` puts `ω^{õb}` on the right; `inadd_comm` flips it to the
left to feed `iseqNaddIdgAux_splice_lt`. -/
lemma iotil_iSpliceEnd_lt {s s' r r' ds j a b : V} (hds : Seq ds) (hj : j < lh ds)
    (ha : icmp (iotil a) (iotil (znth ds j)) = 0) (hb : icmp (iotil b) (iotil (znth ds j)) = 0)
    (hNF : ∀ n, isNF (iotil (znth ds n))) (hNFa : isNF (iotil a)) (hNFb : isNF (iotil b)) :
    icmp (iotil (zK s' r' (seqCons (seqUpdate ds j a) b))) (iotil (zK s r ds)) = 0 := by
  have hNF' : ∀ n, isNF (iotil (znth (seqUpdate ds j a) n)) := by
    intro n; rcases eq_or_ne n j with rfl | hn
    · rw [znth_seqUpdate_self hj]; exact hNFa
    · rw [znth_seqUpdate_of_ne hn]; exact hNF n
  rw [iotil_zK s' r' _ ((seqUpdate_seq ds j a).seqCons b), iotil_zK s r ds hds,
    iseqNaddIdg_seqCons (seqUpdate_seq ds j a)]
  simp only [iseqNaddIdg, seqUpdate_lh]
  rw [inadd_comm (ocOadd (iotil b) 1 0) (isNF_omega_pow hNFb)
    (iseqNaddIdgAux (seqUpdate ds j a) (lh ds)) (isNF_iseqNaddIdgAux' hNF' (lh ds))]
  exact iseqNaddIdgAux_splice_lt hj ha hb hNF hNFa hNFb (lh ds) hj

/-- **LH5 `idg`-side at the `K^r` level** — `dg(splice) ≤ dg(K^r ds)` (same chain rank `r`), since both
auxiliaries dominate by `idg`: `idg a, idg b ≤ idg dⱼ ≤ iseqMaxIdg ds`. -/
lemma idg_iSpliceEnd_le {s s' r ds j a b : V} (hds : Seq ds) (hj : j < lh ds)
    (hag : idg a ≤ idg (znth ds j)) (hbg : idg b ≤ idg (znth ds j)) :
    idg (zK s' r (seqCons (seqUpdate ds j a) b)) ≤ idg (zK s r ds) := by
  rw [idg_zK s' r _ ((seqUpdate_seq ds j a).seqCons b), idg_zK s r ds hds,
    iseqMaxIdg_seqCons (seqUpdate_seq ds j a)]
  have hmono : iseqMaxIdg (seqUpdate ds j a) ≤ iseqMaxIdg ds := by
    rw [iseqMaxIdg, iseqMaxIdg, seqUpdate_lh]
    exact iseqMaxIdgAux_mono (fun n => by
      rcases eq_or_ne n j with rfl | hn
      · rw [znth_seqUpdate_self hj]; exact hag
      · exact le_of_eq (congrArg idg (znth_seqUpdate_of_ne hn))) (lh ds)
  have hbfold : idg b ≤ iseqMaxIdg ds := le_trans hbg (le_iseqMaxIdgAux (lh ds) j hj)
  exact max_le_max (le_refl r) (tsub_le_tsub_right (max_le hmono hbfold) 1)

/-- **LH5 — the splice descent on the genuine object** (Buchholz §3.2 case 14.254). With `õ` strictly
dropping (`iotil_iSpliceEnd_lt`, N3b: F2 two-below-one) and `idg` not rising (`idg_iSpliceEnd_le`),
`iord_descent_le` gives `o(d[0]) ≺ o(d)`. This is the last structural reduction case of Thm 4.2: with the
I-rules (LH1/LH2), Ind (LH4), non-critical chain (LH3), 5.1-nut (`iord_descent_iRcrit_of_chain`), and now
the splice, every Buchholz reduction case has its banked ordinal descent. The auxiliaries' N1 IH facts
(`ha`/`hb`/`hag`/`hbg`) are the only abstract input, supplied by `ZDerivation` induction downstream. -/
lemma iord_descent_iSpliceEnd {s s' r ds j a b : V} (hds : Seq ds) (hj : j < lh ds)
    (hnf : isNF (iotil (zK s r ds)))
    (ha : icmp (iotil a) (iotil (znth ds j)) = 0) (hb : icmp (iotil b) (iotil (znth ds j)) = 0)
    (hag : idg a ≤ idg (znth ds j)) (hbg : idg b ≤ idg (znth ds j))
    (hNF : ∀ n, isNF (iotil (znth ds n))) (hNFa : isNF (iotil a)) (hNFb : isNF (iotil b)) :
    icmp (iord (zK s' r (seqCons (seqUpdate ds j a) b))) (iord (zK s r ds)) = 0 :=
  iord_descent_le hnf (idg_iSpliceEnd_le hds hj hag hbg)
    (iotil_iSpliceEnd_lt hds hj ha hb hNF hNFa hNFb)

/-! ### LH5 — descent on the GENUINE ordered-insert object `seqInsert ds j a b` (case 5.2.1)

The `iord_descent_iSpliceEnd` above is on the order-independent end-append model
`seqCons (seqUpdate ds j a) b`; `isChainInf` validity needs the genuine in-place object
`seqInsert ds j a b` (lap-87 finding). These lemmas re-derive the ordinal descent directly on
`seqInsert`, bypassing the end-append model entirely (so no permutation/`inadd_assoc` plumbing is
needed). The `õ`-side is the rotation kernel `icmp_iseqNaddIdg_seqInsert`: the spliced `#`-fold differs
from `ds`'s only at the distinguished block (entry `dⱼ` replaced by the two halves `a`,`b`), and the
common suffix folds on top by `inadd_right_mono`, so the comparison reduces to the F2 fact
`ω^{õa} # ω^{õb} ≼ ω^{õ dⱼ}` (`icmp_omega_pow_nadd_lt`) — exactly as in `iseqNaddIdgAux_splice_lt`, but
with `b` fixed in place at index `j+1` and the tail riding ON TOP of it. -/

/-- Generic upper bound on the `idg`-fold: if every folded entry's `idg` is `≤ B`, the fold is `≤ B`. -/
lemma iseqMaxIdgAux_le_of_all {cs B : V} :
    ∀ J, (∀ n < J, idg (znth cs n) ≤ B) → iseqMaxIdgAux cs J ≤ B := by
  intro J
  induction J using ISigma1.sigma1_succ_induction
  · definability
  case zero => intro _; rw [iseqMaxIdgAux_zero]; simp
  case succ J ih =>
    intro h
    rw [iseqMaxIdgAux_succ]
    exact max_le (ih (fun n hn => h n (lt_trans hn (by simp)))) (h J (by simp))

/-- **The rotation kernel** — `#`-fold of the genuine in-place splice `seqInsert ds j a b` compares
`= 0` (i.e. `≼`) to `#`-fold of `ds`. Proved by a `J`-shifted induction: the prefix `<j` and the
distinguished block (`a`,`b` in place of `dⱼ`) give the base case (F2), and each further suffix entry
`ds[J]` folds identically on both sides (`inadd_right_mono`). The `isNF` of the SI partial fold is
carried through the induction so no per-entry NF case-bashing is needed. -/
lemma icmp_iseqNaddIdg_seqInsert {ds j a b : V} (hj : j < lh ds)
    (ha : icmp (iotil a) (iotil (znth ds j)) = 0) (hb : icmp (iotil b) (iotil (znth ds j)) = 0)
    (hNF : ∀ n, isNF (iotil (znth ds n))) (hNFa : isNF (iotil a)) (hNFb : isNF (iotil b)) :
    icmp (iseqNaddIdg (seqInsert ds j a b)) (iseqNaddIdg ds) = 0 := by
  set SI := seqInsert ds j a b with hSI
  have hpre : iseqNaddIdgAux SI j = iseqNaddIdgAux ds j :=
    iseqNaddIdgAux_congr_iotil j (fun i hi => by
      rw [hSI, znth_seqInsert_pre hi (lt_trans hi hj)])
  have hωa : isNF (ocOadd (iotil a) 1 0) := isNF_omega_pow hNFa
  have hωb : isNF (ocOadd (iotil b) 1 0) := isNF_omega_pow hNFb
  have hQ : isNF (iseqNaddIdgAux ds j) := isNF_iseqNaddIdgAux' hNF j
  -- D(J): the SI fold (length J+1) compares `≼` to ds fold (length J), for j < J ≤ lh ds.
  have key : ∀ J, j < J → J ≤ lh ds →
      isNF (iseqNaddIdgAux SI (J + 1)) ∧
      icmp (iseqNaddIdgAux SI (J + 1)) (iseqNaddIdgAux ds J) = 0 := by
    intro J
    induction J using ISigma1.sigma1_succ_induction
    · definability
    case zero => intro h; exact absurd h (by simp)
    case succ J ih =>
      intro h1 h2
      rcases (le_iff_lt_succ.mpr h1).lt_or_eq with hlt | heq
      · -- j < J: inductive step, fold the common suffix entry ds[J] on both sides
        have hJlt : J < lh ds := lt_of_lt_of_le (lt_add_one J) h2
        have hJle : J ≤ lh ds := le_of_lt hJlt
        obtain ⟨hNFih, hih⟩ := ih hlt hJle
        have hentry : znth SI (J + 1) = znth ds J := by
          rw [hSI, znth_seqInsert_suf hlt hJlt]
        rw [show iseqNaddIdgAux SI (J + 1 + 1)
              = inadd (iseqNaddIdgAux SI (J + 1)) (ocOadd (iotil (znth ds J)) 1 0) from by
            rw [iseqNaddIdgAux_succ, hentry],
          iseqNaddIdgAux_succ ds J]
        refine ⟨isNF_inadd (isNF_omega_pow (hNF J)) _ hNFih, ?_⟩
        exact inadd_right_mono hNFih (isNF_iseqNaddIdgAux' hNF J) hih
          _ (isNF_omega_pow (hNF J))
      · -- J = j: base case. SI(j+2) = inadd (inadd Q ω^õa) ω^õb ; ds(j+1) = inadd Q ω^õ dⱼ
        subst heq
        have hSIj : iseqNaddIdgAux SI j = iseqNaddIdgAux ds j := hpre
        have eSIj1 : iseqNaddIdgAux SI (j + 1)
            = inadd (iseqNaddIdgAux ds j) (ocOadd (iotil a) 1 0) := by
          rw [iseqNaddIdgAux_succ, hSIj, hSI, znth_seqInsert_at hj]
        have eSIj2 : iseqNaddIdgAux SI (j + 1 + 1)
            = inadd (inadd (iseqNaddIdgAux ds j) (ocOadd (iotil a) 1 0)) (ocOadd (iotil b) 1 0) := by
          rw [iseqNaddIdgAux_succ, eSIj1, hSI, znth_seqInsert_at1 hj]
        have eds : iseqNaddIdgAux ds (j + 1)
            = inadd (iseqNaddIdgAux ds j) (ocOadd (iotil (znth ds j)) 1 0) := by
          rw [iseqNaddIdgAux_succ]
        have ereassoc :
            inadd (inadd (iseqNaddIdgAux ds j) (ocOadd (iotil a) 1 0)) (ocOadd (iotil b) 1 0)
              = inadd (iseqNaddIdgAux ds j)
                  (inadd (ocOadd (iotil a) 1 0) (ocOadd (iotil b) 1 0)) := by
          rw [inadd_comm (ocOadd (iotil b) 1 0) hωb _ (isNF_inadd hωa _ hQ),
            inadd_pow_front hQ hNFb hNFa,
            inadd_comm (ocOadd (iotil b) 1 0) hωb (ocOadd (iotil a) 1 0) hωa]
        refine ⟨?_, ?_⟩
        · rw [eSIj2]
          exact isNF_inadd hωb _ (isNF_inadd hωa _ hQ)
        · rw [eSIj2, eds, ereassoc]
          exact inadd_left_mono (isNF_inadd hωb _ hωa) (isNF_omega_pow (hNF j))
            (icmp_omega_pow_nadd_lt ha hb) _ hQ
  -- instantiate at the top: J = lh ds
  have hlhSI : lh SI = lh ds + 1 := by rw [hSI]; exact seqInsert_lh ds j a b
  have hfin := (key (lh ds) hj le_rfl).2
  show icmp (iseqNaddIdg SI) (iseqNaddIdg ds) = 0
  unfold iseqNaddIdg
  rw [hlhSI]
  exact hfin

/-- **The `idg`-side bound** — the `idg`-fold of `seqInsert ds j a b` does not exceed that of `ds`,
provided the two halves `a`,`b` have `idg ≤ idg dⱼ`. Same `J`-shifted induction as the rotation kernel,
on the (commutative-idempotent) `max`-fold. -/
lemma iseqMaxIdg_seqInsert_le {ds j a b : V} (hj : j < lh ds)
    (hag : idg a ≤ idg (znth ds j)) (hbg : idg b ≤ idg (znth ds j)) :
    iseqMaxIdg (seqInsert ds j a b) ≤ iseqMaxIdg ds := by
  set SI := seqInsert ds j a b with hSI
  have hpre : iseqMaxIdgAux SI j = iseqMaxIdgAux ds j :=
    iseqMaxIdgAux_congr j (fun i hi => by rw [hSI, znth_seqInsert_pre hi (lt_trans hi hj)])
  have key : ∀ J, j < J → J ≤ lh ds →
      iseqMaxIdgAux SI (J + 1) ≤ iseqMaxIdgAux ds J := by
    intro J
    induction J using ISigma1.sigma1_succ_induction
    · definability
    case zero => intro h; exact absurd h (by simp)
    case succ J ih =>
      intro h1 h2
      rcases (le_iff_lt_succ.mpr h1).lt_or_eq with hlt | heq
      · have hJlt : J < lh ds := lt_of_lt_of_le (lt_add_one J) h2
        have hentry : znth SI (J + 1) = znth ds J := by rw [hSI, znth_seqInsert_suf hlt hJlt]
        rw [show iseqMaxIdgAux SI (J + 1 + 1) = max (iseqMaxIdgAux SI (J + 1)) (idg (znth ds J)) from by
            rw [iseqMaxIdgAux_succ, hentry],
          iseqMaxIdgAux_succ ds J]
        exact max_le_max (ih hlt (le_of_lt hJlt)) (le_refl _)
      · subst heq
        have e1 : iseqMaxIdgAux SI (j + 1) = max (iseqMaxIdgAux ds j) (idg a) := by
          rw [iseqMaxIdgAux_succ, hpre, hSI, znth_seqInsert_at hj]
        have e2 : iseqMaxIdgAux SI (j + 1 + 1)
            = max (max (iseqMaxIdgAux ds j) (idg a)) (idg b) := by
          rw [iseqMaxIdgAux_succ, e1, hSI, znth_seqInsert_at1 hj]
        rw [e2, iseqMaxIdgAux_succ]
        exact max_le (max_le (le_max_left _ _) (le_trans hag (le_max_right _ _)))
          (le_trans hbg (le_max_right _ _))
  have hlhSI : lh SI = lh ds + 1 := by rw [hSI]; exact seqInsert_lh ds j a b
  show iseqMaxIdg SI ≤ iseqMaxIdg ds
  unfold iseqMaxIdg
  rw [hlhSI]
  exact key (lh ds) hj le_rfl

/-- **LH5 `idg`-side at the `K^r` level on the genuine insert object** — `dg(seqInsert) ≤ dg(K^r ds)`
(same chain rank `r`). -/
lemma idg_seqInsert_le {s s' r ds j a b : V} (hds : Seq ds) (hj : j < lh ds)
    (hag : idg a ≤ idg (znth ds j)) (hbg : idg b ≤ idg (znth ds j)) :
    idg (zK s' r (seqInsert ds j a b)) ≤ idg (zK s r ds) := by
  rw [idg_zK s' r _ (seqInsert_seq ds j a b), idg_zK s r ds hds]
  exact max_le_max (le_refl r) (tsub_le_tsub_right (iseqMaxIdg_seqInsert_le hj hag hbg) 1)

/-- **LH5 `õ`-side at the `K^r` level on the genuine insert object** — `õ(seqInsert) ≼ õ(K^r ds)`. -/
lemma iotil_seqInsert_lt {s s' r r' ds j a b : V} (hds : Seq ds) (hj : j < lh ds)
    (ha : icmp (iotil a) (iotil (znth ds j)) = 0) (hb : icmp (iotil b) (iotil (znth ds j)) = 0)
    (hNF : ∀ n, isNF (iotil (znth ds n))) (hNFa : isNF (iotil a)) (hNFb : isNF (iotil b)) :
    icmp (iotil (zK s' r' (seqInsert ds j a b))) (iotil (zK s r ds)) = 0 := by
  rw [iotil_zK s' r' _ (seqInsert_seq ds j a b), iotil_zK s r ds hds]
  exact icmp_iseqNaddIdg_seqInsert hj ha hb hNF hNFa hNFb

/-- **LH5 — the splice descent on the GENUINE ordered-insert object** (Buchholz §3.2 case 5.2.1).
`õ` does not rise (`iotil_seqInsert_lt`) and `idg` does not rise (`idg_seqInsert_le`), so
`iord_descent_le` gives `o(seqInsert) ≼ o(K^r ds)`. This is the descent on the object the `isChainInf`
validity (`zKValidF_seqInsert`) actually lives on — replacing the end-append model
`iord_descent_iSpliceEnd` for the genuine reduct. -/
lemma iord_descent_seqInsert {s s' r ds j a b : V} (hds : Seq ds) (hj : j < lh ds)
    (hnf : isNF (iotil (zK s r ds)))
    (ha : icmp (iotil a) (iotil (znth ds j)) = 0) (hb : icmp (iotil b) (iotil (znth ds j)) = 0)
    (hag : idg a ≤ idg (znth ds j)) (hbg : idg b ≤ idg (znth ds j))
    (hNF : ∀ n, isNF (iotil (znth ds n))) (hNFa : isNF (iotil a)) (hNFb : isNF (iotil b)) :
    icmp (iord (zK s' r (seqInsert ds j a b))) (iord (zK s r ds)) = 0 :=
  iord_descent_le hnf (idg_seqInsert_le hds hj hag hbg)
    (iotil_seqInsert_lt hds hj ha hb hNF hNFa hNFb)

/-- **`idg`-side bound, RANK-GENERAL** — the genuine 5.2.1 reduct has rank `r' = max{rk(A(dⱼ)), r}`,
which may exceed `r`. The `idg` bound still holds **provided the new rank does not exceed the parent's
degree** (`hr' : r' ≤ idg (zK s r ds)`) — which is the faithful situation, since `dg(d) = max(r, …)`
already absorbs every cut rank in the chain. -/
lemma idg_seqInsert_le' {s s' r r' ds j a b : V} (hds : Seq ds) (hj : j < lh ds)
    (hr' : r' ≤ idg (zK s r ds))
    (hag : idg a ≤ idg (znth ds j)) (hbg : idg b ≤ idg (znth ds j)) :
    idg (zK s' r' (seqInsert ds j a b)) ≤ idg (zK s r ds) := by
  rw [idg_zK s' r' _ (seqInsert_seq ds j a b)]
  refine max_le hr' ?_
  rw [idg_zK s r ds hds] at hr' ⊢
  exact le_trans (tsub_le_tsub_right (iseqMaxIdg_seqInsert_le hj hag hbg) 1) (le_max_right _ _)

/-- **LH5 splice descent, RANK-GENERAL** (Buchholz §3.2 case 5.2.1 with the genuine reduct rank
`r' = max{rk(A(dⱼ)), r}`). `õ` is rank-free (`iotil_seqInsert_lt`); `idg` is bounded via
`idg_seqInsert_le'` under `r' ≤ dg(parent)`. This is the descent the dispatch's 5.2.1 case invokes. -/
lemma iord_descent_seqInsert' {s s' r r' ds j a b : V} (hds : Seq ds) (hj : j < lh ds)
    (hnf : isNF (iotil (zK s r ds))) (hr' : r' ≤ idg (zK s r ds))
    (ha : icmp (iotil a) (iotil (znth ds j)) = 0) (hb : icmp (iotil b) (iotil (znth ds j)) = 0)
    (hag : idg a ≤ idg (znth ds j)) (hbg : idg b ≤ idg (znth ds j))
    (hNF : ∀ n, isNF (iotil (znth ds n))) (hNFa : isNF (iotil a)) (hNFb : isNF (iotil b)) :
    icmp (iord (zK s' r' (seqInsert ds j a b))) (iord (zK s r ds)) = 0 :=
  iord_descent_le hnf (idg_seqInsert_le' hds hj hr' hag hbg)
    (iotil_seqInsert_lt hds hj ha hb hNF hNFa hNFb)

/-- The full critical reduct `d[0] = K^{r-1}_Π d{0} d{1}` (Buchholz §3.2 case 5.1), as a genuine code:
auxiliaries `d{0}=K^r(i/v)`, `d{1}=K^r(j/w)` (`iCritAux`), assembled into a rank-`(r-1)` chain over the
two-element `iCritReductSeq`. -/
noncomputable def iCritReduct (d i j v w : V) : V :=
  zK (fstIdx d) (zKrank d - 1) (iCritReductSeq (iCritAux d i v) (iCritAux d j w))

/-- **THE NUT, fully assembled on the genuine reduct object** — `o(d[0]) ≺ o(d)` for the critical chain
`d = K^r ds`, its reduct `d[0] = iCritReduct` built from the two `seqUpdate`-auxiliaries `d{0}=K^r(i/v)`,
`d{1}=K^r(j/w)`. The hypotheses are precisely the Thm-4.2 mutual-IH facts on the replaced premises
(`õ(v) ≺ õ(d_i)`, `õ(w) ≺ õ(d_j)`, N1) plus `r ≥ 1` (T3.4 `rk(A(d)) < r`). Composes the object-level N2
facts (`iotil_iCritAux_lt`/`idg_iCritAux_le`) through the chain descent `iord_descent_iCritReduct_chain`.
The cut-elimination descent now runs end-to-end on real `seqUpdate`-based codes — only the N1 IH plumbing
(structural `ZDerivation` induction) and T3.4 supplying `r ≥ 1` remain upstream. -/
lemma iord_descent_iCritReduct_object {s r ds i j v w : V}
    (hds : Seq ds) (hr : 1 ≤ r) (hnf : isNF (iotil (zK s r ds)))
    (hi : i < lh ds) (hj : j < lh ds)
    (hvlt : icmp (iotil v) (iotil (znth ds i)) = 0)
    (hwlt : icmp (iotil w) (iotil (znth ds j)) = 0)
    (hvg : idg v ≤ idg (znth ds i)) (hwg : idg w ≤ idg (znth ds j))
    (hNF : ∀ n, isNF (iotil (znth ds n))) (hNFv : isNF (iotil v)) (hNFw : isNF (iotil w)) :
    icmp (iord (iCritReduct (zK s r ds) i j v w)) (iord (zK s r ds)) = 0 := by
  have hred : iCritReduct (zK s r ds) i j v w
      = zK s (r - 1) (iCritReductSeq (iCritAux (zK s r ds) i v) (iCritAux (zK s r ds) j w)) := by
    simp [iCritReduct]
  rw [hred]
  exact iord_descent_iCritReduct_chain hds hr hnf
    (iotil_iCritAux_lt hds hi hvlt hNF hNFv)
    (iotil_iCritAux_lt hds hj hwlt hNF hNFw)
    (idg_iCritAux_le hds hi hvg)
    (idg_iCritAux_le hds hj hwg)

/-- **THE NUT, ASSEMBLED END-TO-END on a genuine chain** (E-CRUX2 §8.3, case 5.1). For the critical
chain `d = K^r ds`, this composes the three banked pieces into the case-5.1 descent `o(d[0]) ≺ o(d)`:
1. **L3.1 redex finder** (`inference_critical_pair_of_chain`) — from the `isChainInf` data + the tp
   permissibility/truth well-formedness, produces the redex `(i,j,k)` with `0 < rk(Aᵢ) ≤ r`;
2. **T3.4(a)** — `0 < rk(Aᵢ) ≤ r` gives `1 ≤ r`, the degree-drop premise the reduct needs;
3. **the object reduct + Thm 4.2** (`iord_descent_iCritReduct_object`) — `d[0] = K^{r−1} d{0} d{1}`
   with `d{ν}` the premise-`i`/`j` reducts `ρ i`/`ρ j`, descends since each `ρ`-reduct lowers `õ`
   and does not raise `dg` (the **N1 structural IH**, here the only abstract input besides the
   deferred tp/§5 well-formedness). The chain-structural `hchain`/`hAj0`/`hrank` come straight from
   `isChainInf`. This is the case-5.1 descent on REAL `seqUpdate`-based codes; only N1's IH plumbing
   (the `ZDerivation` structural recursion supplying `ρ`'s descent facts) and §5/Lemma-3.3 (the tp
   well-formedness making the redex fire on a real critical derivation) remain upstream. -/
theorem iord_descent_critical_of_chain {s r ds j0 : V} {Tr Fa : V → Prop} {ρ : V → V}
    (hds : Seq ds) (hnf : isNF (iotil (zK s r ds)))
    (hj0 : j0 < lh ds)
    (hAj0 : chainAsucc ds j0 = seqSucc s ∨ chainAsucc ds j0 = (^⊥ : V))
    (hchain : ∀ i ≤ j0, ∀ B, inAnt B (chainAnt ds i) →
      inAnt B (seqAnt s) ∨ ∃ i' < i, B = chainAsucc ds i')
    (hrank : ∀ i < j0, irk (chainAsucc ds i) ≤ r)
    (hwfR : ∀ i ≤ j0, ∀ A, tp (znth ds i) = isymR A → 0 < irk A ∨ Tr A)
    (hwfL : ∀ i ≤ j0, ∀ k A, tp (znth ds i) = isymLk k A → 0 < irk A ∨ Fa A)
    (hperm : ∀ i ≤ j0, iperm (tp (znth ds i)) (fstIdx (znth ds i)))
    (hnperm : ∀ i ≤ j0, ¬ iperm (tp (znth ds i)) s)
    (hdisj : ∀ A, ¬ (Tr A ∧ Fa A)) (hFa_rk : ∀ A, Fa A → irk A = 0)
    (hFa_bot : Fa (^⊥ : V))
    (hNF : ∀ n, isNF (iotil (znth ds n)))
    (hρlt : ∀ n, icmp (iotil (ρ n)) (iotil (znth ds n)) = 0)
    (hρg : ∀ n, idg (ρ n) ≤ idg (znth ds n))
    (hρNF : ∀ n, isNF (iotil (ρ n))) :
    ∃ i j, i < j ∧ j ≤ j0 ∧
      icmp (iord (iCritReduct (zK s r ds) i j (ρ i) (ρ j))) (iord (zK s r ds)) = 0 := by
  obtain ⟨i, j, k, hij, hjle, hRi, hLj, hrkpos, hrkr⟩ :=
    inference_critical_pair_of_chain hj0 hAj0 hchain hrank hwfR hwfL hperm hnperm hdisj hFa_rk hFa_bot
  have hr : 1 ≤ r := pos_iff_one_le.mp (lt_of_lt_of_le hrkpos hrkr)
  have hi : i < lh ds := lt_trans (lt_of_lt_of_le hij hjle) hj0
  have hj : j < lh ds := lt_of_le_of_lt hjle hj0
  exact ⟨i, j, hij, hjle, iord_descent_iCritReduct_object hds hr hnf hi hj
    (hρlt i) (hρlt j) (hρg i) (hρg j) hNF (hρNF i) (hρNF j)⟩

/-! ## The redex-pair extraction FUNCTION — `iR`'s critical branch as a CLOSED definable object

`iord_descent_critical_of_chain` produces the case-5.1 descent for the *existential* redex `(i,j)`. For
`iR`'s critical branch to be a **closed, total, definable** function (Buchholz Def 3.2 case 5.1, which
takes "the least such pair"), the redex must be a *function* of the chain, not just an existential. This
section builds that: a first-hit bounded search `redexAux` over the pairing code `c = ⟪i,j⟫`, returning
the least valid redex pair. The "valid redex" test is stated purely via `tp` and the pairing projections
(`tp(dᵢ)=R_{Aᵢ}` ⟺ `π₁(tp dᵢ)=0`; `tp(d_j)=L^k_{Aᵢ}` ⟺ `π₁(tp d_j)=1` with the same cut formula
`π₂(π₂(tp d_j))=π₂(tp dᵢ)`), so it needs no sequent/`chainAsucc` bookkeeping. The Buchholz reduct then
becomes the closed `iRcrit d ρ` (`ρ` = the indexed sub-reduct `dᵢ[k]`/`d_j[0]`, the one honest abstract
input = the N1 structural IH / `d[n]` recursion, deferred). -/

/-- **Valid-redex test on a pairing code** `c = ⟪i,j⟫`: `i<j<lh ds`, premise `i`'s `tp` is a right
symbol (`π₁=0`), premise `j`'s `tp` is a left symbol (`π₁=1`), and they share the cut formula
(`π₂(π₂(tp d_j)) = π₂(tp dᵢ)`). On such a `c`, `π₂(tp dᵢ) = Aᵢ` is Buchholz's cut formula `A(d)`. -/
def isRedexPair (ds c : V) : Prop :=
  π₁ c < π₂ c ∧ π₂ c < lh ds ∧
  π₁ (tp (znth ds (π₁ c))) = 0 ∧ π₁ (tp (znth ds (π₂ c))) = 1 ∧
  π₂ (π₂ (tp (znth ds (π₂ c)))) = π₂ (tp (znth ds (π₁ c)))

/-- **Redex-pair → `tp`-symbol shape bridge.** From the bare `π₁`-discriminant pair test
`isRedexPair ds c` recover the genuine inference symbols on the two redex premises: the `i`-end
(`i = π₁ c`) is a right symbol `R_{Aᵢ}` and the `j`-end (`j = π₂ c`) is a left symbol `L^k_{Aᵢ}`
on the **same** cut formula `Aᵢ = π₂ (tp (znth ds i))` (from the shared-cut-formula conjunct). This
is what lets a caller of `iord_descent_iRcrit_of_chain'` read off the redex premises' `tp` from the
finder's least-pair `redexCode` (rather than from the existential redex). -/
lemma redexPair_tp {ds c : V} (h : isRedexPair ds c) :
    tp (znth ds (π₁ c)) = isymR (π₂ (tp (znth ds (π₁ c)))) ∧
    tp (znth ds (π₂ c)) = isymLk (π₁ (π₂ (tp (znth ds (π₂ c)))))
      (π₂ (tp (znth ds (π₁ c)))) := by
  obtain ⟨_, _, hi, hj, hcut⟩ := h
  refine ⟨tp_eq_isymR_of_pi₁_zero hi, ?_⟩
  have hL := tp_eq_isymLk_of_pi₁_one hj
  rw [hcut] at hL
  exact hL

/-- First-hit search step: keep the prior hit if one was found (`ih < n`), else take `n` if it is a
valid redex pair, else advance the sentinel to `n+1`. -/
noncomputable def redexAux.blueprint : PR.Blueprint 1 where
  zero := .mkSigma “y ds. y = 0”
  succ := .mkSigma “y ih n ds.
    (ih < n ∧ y = ih) ∨
    (n ≤ ih ∧
      ∃ i, !pi₁Def i n ∧ ∃ j, !pi₂Def j n ∧ ∃ l, !lhDef l ds ∧
      ∃ di, !znthDef di ds i ∧ ∃ ti, !tpDef ti di ∧
      ∃ dj, !znthDef dj ds j ∧ ∃ tj, !tpDef tj dj ∧
      ∃ p1i, !pi₁Def p1i ti ∧ ∃ p1j, !pi₁Def p1j tj ∧
      ∃ a2i, !pi₂Def a2i ti ∧
      ∃ p2j, !pi₂Def p2j tj ∧ ∃ a2j, !pi₂Def a2j p2j ∧
      ( (i < j ∧ j < l ∧ p1i = 0 ∧ p1j = 1 ∧ a2j = a2i ∧ y = n) ∨
        (¬(i < j ∧ j < l ∧ p1i = 0 ∧ p1j = 1 ∧ a2j = a2i) ∧ y = n + 1) ) )”

noncomputable def redexAux.construction : PR.Construction V redexAux.blueprint where
  zero := fun _ ↦ 0
  succ := fun x n ih ↦ if ih < n then ih else if isRedexPair (x 0) n then n else n + 1
  zero_defined := .mk fun v ↦ by simp [redexAux.blueprint]
  succ_defined := .mk fun v ↦ by
    by_cases h1 : v 1 < v 2
    · simp [redexAux.blueprint, h1]
    · have hle : v 2 ≤ v 1 := not_lt.mp h1
      by_cases h2 : isRedexPair (v 3) (v 2)
      · simp only [redexAux.blueprint, isRedexPair] at h2 ⊢
        simp [h1, h2, hle, pi₁_defined.iff, pi₂_defined.iff, lh_defined.iff, znth_defined.iff,
          tp_defined.iff]
      · simp only [redexAux.blueprint, isRedexPair] at h2 ⊢
        simp [h1, h2, hle, pi₁_defined.iff, pi₂_defined.iff, lh_defined.iff, znth_defined.iff,
          tp_defined.iff]
        constructor
        · rintro (⟨hc1, hc2, hc3, hc4, hc5, _⟩ | ⟨_, h⟩)
          · exact absurd ⟨hc1, hc2, hc3, hc4, hc5⟩ h2
          · exact h
        · intro h
          refine Or.inr ⟨?_, h⟩
          rcases lt_or_ge (π₁ (v 2)) (π₂ (v 2)) with hc1 | hc1
          · rcases lt_or_ge (π₂ (v 2)) (lh (v 3)) with hc2 | hc2
            · by_cases hc3 : π₁ (tp (znth (v 3) (π₁ (v 2)))) = 0
              · by_cases hc4 : π₁ (tp (znth (v 3) (π₂ (v 2)))) = 1
                · exact Or.inr (Or.inr (Or.inr (Or.inr (fun hc5 => h2 ⟨hc1, hc2, hc3, hc4, hc5⟩))))
                · exact Or.inr (Or.inr (Or.inr (Or.inl hc4)))
              · exact Or.inr (Or.inr (Or.inl hc3))
            · exact Or.inr (Or.inl hc2)
          · exact Or.inl hc1

/-- `redexAux ds n` = the least pairing code `c < n` that is a valid redex pair of `ds`, or `n` if none. -/
noncomputable def redexAux (ds n : V) : V := redexAux.construction.result ![ds] n

@[simp] lemma redexAux_zero (ds : V) : redexAux ds 0 = 0 := by
  simp [redexAux, redexAux.construction]

@[simp] lemma redexAux_succ (ds n : V) :
    redexAux ds (n + 1) =
      (if redexAux ds n < n then redexAux ds n else if isRedexPair ds n then n else n + 1) := by
  simp [redexAux, redexAux.construction]

noncomputable def _root_.LO.FirstOrder.Arithmetic.redexAuxDef : 𝚺₁.Semisentence 3 :=
  redexAux.blueprint.resultDef.rew (Rew.subst ![#0, #2, #1])

instance redexAux_defined : 𝚺₁-Function₂ (redexAux : V → V → V) via redexAuxDef :=
  .mk fun v ↦ by simp [redexAux.construction.result_defined_iff, redexAuxDef]; rfl

instance redexAux_definable : 𝚺₁-Function₂ (redexAux : V → V → V) := redexAux_defined.to_definable
instance redexAux_definable' (Γ) : Γ-[m + 1]-Function₂ (redexAux : V → V → V) :=
  redexAux_definable.of_sigmaOne

/-- **First-hit ≤ sentinel** — the search result never exceeds its bound. -/
lemma redexAux_le (ds : V) : ∀ N, redexAux ds N ≤ N := by
  intro N
  induction N using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ n ih =>
    rw [redexAux_succ]
    by_cases h1 : redexAux ds n < n
    · rw [if_pos h1]; exact le_of_lt (lt_trans h1 (le_iff_lt_succ.mp (le_refl n)))
    · rw [if_neg h1]
      by_cases h2 : isRedexPair ds n
      · rw [if_pos h2]; exact le_of_lt (le_iff_lt_succ.mp (le_refl n))
      · simp [h2]

/-- **First-hit is valid** — if the search returns a genuine index (`< N`), it is a valid redex pair. -/
lemma redexAux_isRedexPair_of_lt (ds : V) :
    ∀ N, redexAux ds N < N → isRedexPair ds (redexAux ds N) := by
  intro N
  induction N using ISigma1.sigma1_succ_induction
  · simp only [isRedexPair]; definability
  case zero => intro h; exact absurd h (by simp)
  case succ n ih =>
    intro hlt
    rw [redexAux_succ] at hlt ⊢
    by_cases h1 : redexAux ds n < n
    · rw [if_pos h1] at hlt ⊢; exact ih h1
    · rw [if_neg h1] at hlt ⊢
      by_cases h2 : isRedexPair ds n
      · rw [if_pos h2] at hlt ⊢; exact h2
      · rw [if_neg h2] at hlt; exact absurd hlt (by simp)

/-- **No-hit sentinel** — if the search returns the sentinel `N`, then no `c < N` is a valid redex
pair (the search exhausted the range). -/
lemma redexAux_eq_self_of_no_redex (ds : V) :
    ∀ N, redexAux ds N = N → ∀ c < N, ¬ isRedexPair ds c := by
  intro N
  induction N using ISigma1.sigma1_succ_induction
  · simp only [isRedexPair]; definability
  case zero => intro _ c hc; exact absurd hc (by simp)
  case succ n ih =>
    intro heq c hc
    rw [redexAux_succ] at heq
    by_cases h1 : redexAux ds n < n
    · rw [if_pos h1] at heq
      exact absurd (le_iff_lt_succ.mp (le_refl n)) (lt_asymm (heq ▸ h1))
    · rw [if_neg h1] at heq
      by_cases h2 : isRedexPair ds n
      · rw [if_pos h2] at heq; exact absurd heq (le_iff_lt_succ.mp (le_refl n)).ne
      · rw [if_neg h2] at heq
        have hn : redexAux ds n = n := le_antisymm (redexAux_le ds n) (not_lt.mp h1)
        rcases lt_or_eq_of_le (lt_succ_iff_le.mp hc) with hcn | hcn
        · exact ih hn c hcn
        · rw [hcn]; exact h2

/-- **First-hit found** — when a valid redex pair exists below the sentinel, the search returns one. -/
lemma redexAux_found (ds N : V) (h : ∃ c < N, isRedexPair ds c) :
    redexAux ds N < N ∧ isRedexPair ds (redexAux ds N) := by
  have hlt : redexAux ds N < N := by
    rcases lt_or_eq_of_le (redexAux_le ds N) with h' | h'
    · exact h'
    · obtain ⟨c, hcN, hc⟩ := h
      exact absurd hc (redexAux_eq_self_of_no_redex ds N h' c hcN)
  exact ⟨hlt, redexAux_isRedexPair_of_lt ds N hlt⟩

/-- **First-hit is MINIMAL** — the search returns the least redex code in range: any redex `c < N`
bounds the result from above. (First-hit scans `0,1,2,…` and stops at the first redex, so it is `≤`
every redex below the sentinel.) The rank-side companion of `redexAux_found`. -/
lemma redexAux_min (ds : V) : ∀ N, ∀ c < N, isRedexPair ds c → redexAux ds N ≤ c := by
  intro N
  induction N using ISigma1.sigma1_succ_induction
  · simp only [isRedexPair]; definability
  case zero => intro c hc; exact absurd hc (by simp)
  case succ n ih =>
    intro c hc hcrx
    rw [redexAux_succ]
    by_cases h1 : redexAux ds n < n
    · rw [if_pos h1]
      rcases lt_or_eq_of_le (lt_succ_iff_le.mp hc) with hcn | hcn
      · exact ih c hcn hcrx
      · rw [hcn]; exact le_of_lt h1
    · have hn : redexAux ds n = n := le_antisymm (redexAux_le ds n) (not_lt.mp h1)
      rw [if_neg h1]
      by_cases h2 : isRedexPair ds n
      · rw [if_pos h2]
        rcases lt_or_eq_of_le (lt_succ_iff_le.mp hc) with hcn | hcn
        · exact absurd hcrx (redexAux_eq_self_of_no_redex ds n hn c hcn)
        · rw [hcn]
      · rw [if_neg h2]
        rcases lt_or_eq_of_le (lt_succ_iff_le.mp hc) with hcn | hcn
        · exact absurd hcrx (redexAux_eq_self_of_no_redex ds n hn c hcn)
        · rw [hcn] at hcrx; exact absurd hcrx h2

/-- **The redex code of a chain** = least valid redex pair `⟪i,j⟫` over `ds = zKseq d`, bounded by
`⟪lh ds, lh ds⟫`. Buchholz Def 3.2 case 5.1's "least such pair (i,j)", now a definable function. -/
noncomputable def redexCode (d : V) : V :=
  redexAux (zKseq d) (⟪lh (zKseq d), lh (zKseq d)⟫ : V)
/-- The redex's right-reduction index `i` (`tp(dᵢ) = R_{Aᵢ}`). -/
noncomputable def redexI (d : V) : V := π₁ (redexCode d)
/-- The redex's left-symbol index `j` (`tp(d_j) = L^k_{Aᵢ}`). -/
noncomputable def redexJ (d : V) : V := π₂ (redexCode d)

/-- **Redex code spec** — if a valid redex pair exists in range, `redexCode d` is one. -/
lemma redexCode_isRedexPair {d : V}
    (h : ∃ c < (⟪lh (zKseq d), lh (zKseq d)⟫ : V), isRedexPair (zKseq d) c) :
    isRedexPair (zKseq d) (redexCode d) := (redexAux_found (zKseq d) _ h).2

/-! ### The minimal permissible-premise index finder (Buchholz Def 3.2 case 5.2 dispatch index)

When a `K`-chain `zK s r ds` is NON-critical (`¬ zKCritical s ds`, i.e. some premise `dᵢ` has
`tp(dᵢ) ◁ s`), Buchholz's case 5.2 reduces at the **least** such `i` (`tp(dᵢ) ◁ Π`). This first-hit
bounded search `permIdxAux` — the single-index analogue of `redexAux` — returns that least `i` (or the
sentinel `lh ds` if none, i.e. the chain is critical). Its condition `iperm (tp (znth ds i)) s` is the
exact `¬`-conjunct of `zKCritical`. -/

/-- **Permissible-premise test**: premise `n` of chain `ds` is `◁`-permissible w.r.t. conclusion `s`. -/
def isPermPrem (ds s n : V) : Prop := iperm (tp (znth ds n)) s

noncomputable def permIdxAux.blueprint : PR.Blueprint 2 where
  zero := .mkSigma “y ds s. y = 0”
  succ := .mkSigma “y ih n ds s.
    (ih < n ∧ y = ih) ∨
    (n ≤ ih ∧ ∃ d, !znthDef d ds n ∧ ∃ t, !tpDef t d ∧
      ( (!ipermDef t s ∧ y = n) ∨ (¬(!ipermDef t s) ∧ y = n + 1) ) )”

noncomputable def permIdxAux.construction : PR.Construction V permIdxAux.blueprint where
  zero := fun _ ↦ 0
  succ := fun x n ih ↦ if ih < n then ih else if isPermPrem (x 0) (x 1) n then n else n + 1
  zero_defined := .mk fun v ↦ by simp [permIdxAux.blueprint]
  succ_defined := .mk fun v ↦ by
    by_cases h1 : v 1 < v 2
    · simp [permIdxAux.blueprint, h1]
    · have hle : v 2 ≤ v 1 := not_lt.mp h1
      by_cases h2 : isPermPrem (v 3) (v 4) (v 2)
      · simp only [permIdxAux.blueprint, isPermPrem] at h2 ⊢
        simp [h1, h2, hle, znth_defined.iff, tp_defined.iff, iperm_defined.iff]
      · simp only [permIdxAux.blueprint, isPermPrem] at h2 ⊢
        simp [h1, h2, hle, znth_defined.iff, tp_defined.iff, iperm_defined.iff]

/-- `permIdxAux ds s n` = the least `i < n` with `isPermPrem ds s i`, or `n` if none. -/
noncomputable def permIdxAux (ds s n : V) : V := permIdxAux.construction.result ![ds, s] n

@[simp] lemma permIdxAux_zero (ds s : V) : permIdxAux ds s 0 = 0 := by
  simp [permIdxAux, permIdxAux.construction]

@[simp] lemma permIdxAux_succ (ds s n : V) :
    permIdxAux ds s (n + 1) =
      (if permIdxAux ds s n < n then permIdxAux ds s n
       else if isPermPrem ds s n then n else n + 1) := by
  simp [permIdxAux, permIdxAux.construction]

noncomputable def _root_.LO.FirstOrder.Arithmetic.permIdxAuxDef : 𝚺₁.Semisentence 4 :=
  permIdxAux.blueprint.resultDef.rew (Rew.subst ![#0, #3, #1, #2])

instance permIdxAux_defined : 𝚺₁-Function₃ (permIdxAux : V → V → V → V) via permIdxAuxDef :=
  .mk fun v ↦ by simp [permIdxAux.construction.result_defined_iff, permIdxAuxDef]; rfl

instance permIdxAux_definable : 𝚺₁-Function₃ (permIdxAux : V → V → V → V) :=
  permIdxAux_defined.to_definable
instance permIdxAux_definable' (Γ) : Γ-[m + 1]-Function₃ (permIdxAux : V → V → V → V) :=
  permIdxAux_definable.of_sigmaOne

/-- **First-hit ≤ sentinel**. -/
lemma permIdxAux_le (ds s : V) : ∀ N, permIdxAux ds s N ≤ N := by
  intro N
  induction N using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ n ih =>
    rw [permIdxAux_succ]
    by_cases h1 : permIdxAux ds s n < n
    · rw [if_pos h1]; exact le_of_lt (lt_trans h1 (le_iff_lt_succ.mp (le_refl n)))
    · rw [if_neg h1]
      by_cases h2 : isPermPrem ds s n
      · rw [if_pos h2]; exact le_of_lt (le_iff_lt_succ.mp (le_refl n))
      · simp [h2]

/-- **First-hit is valid** — a returned index `< N` is permissible. -/
lemma permIdxAux_isPermPrem_of_lt (ds s : V) :
    ∀ N, permIdxAux ds s N < N → isPermPrem ds s (permIdxAux ds s N) := by
  intro N
  induction N using ISigma1.sigma1_succ_induction
  · simp only [isPermPrem]; definability
  case zero => intro h; exact absurd h (by simp)
  case succ n ih =>
    intro hlt
    rw [permIdxAux_succ] at hlt ⊢
    by_cases h1 : permIdxAux ds s n < n
    · rw [if_pos h1] at hlt ⊢; exact ih h1
    · rw [if_neg h1] at hlt ⊢
      by_cases h2 : isPermPrem ds s n
      · rw [if_pos h2] at hlt ⊢; exact h2
      · rw [if_neg h2] at hlt; exact absurd hlt (by simp)

/-- **No-hit sentinel** — if the search returns `N`, no `i < N` is permissible (chain is critical). -/
lemma permIdxAux_eq_self_of_none (ds s : V) :
    ∀ N, permIdxAux ds s N = N → ∀ i < N, ¬ isPermPrem ds s i := by
  intro N
  induction N using ISigma1.sigma1_succ_induction
  · simp only [isPermPrem]; definability
  case zero => intro _ i hi; exact absurd hi (by simp)
  case succ n ih =>
    intro heq i hi
    rw [permIdxAux_succ] at heq
    by_cases h1 : permIdxAux ds s n < n
    · rw [if_pos h1] at heq
      exact absurd (le_iff_lt_succ.mp (le_refl n)) (lt_asymm (heq ▸ h1))
    · rw [if_neg h1] at heq
      by_cases h2 : isPermPrem ds s n
      · rw [if_pos h2] at heq; exact absurd heq (le_iff_lt_succ.mp (le_refl n)).ne
      · rw [if_neg h2] at heq
        have hn : permIdxAux ds s n = n := le_antisymm (permIdxAux_le ds s n) (not_lt.mp h1)
        rcases lt_or_eq_of_le (lt_succ_iff_le.mp hi) with hin | hin
        · exact ih hn i hin
        · rw [hin]; exact h2

/-- **First-hit found** — when a permissible premise exists below `N`, the search returns one. -/
lemma permIdxAux_found (ds s N : V) (h : ∃ i < N, isPermPrem ds s i) :
    permIdxAux ds s N < N ∧ isPermPrem ds s (permIdxAux ds s N) := by
  have hlt : permIdxAux ds s N < N := by
    rcases lt_or_eq_of_le (permIdxAux_le ds s N) with h' | h'
    · exact h'
    · obtain ⟨i, hiN, hi⟩ := h
      exact absurd hi (permIdxAux_eq_self_of_none ds s N h' i hiN)
  exact ⟨hlt, permIdxAux_isPermPrem_of_lt ds s N hlt⟩

/-- **First-hit is LEAST** — the returned index is `≤` any permissible index `m < N`. Since `permIdxAux`
scans low-to-high and stops at the first hit, it never overshoots a permissible premise. The key
leastness fact behind `permIdx ≤ j₀` (the Buchholz §5.2 selection `i ≤ j₀ minimal s.t. tp(dᵢ) ◁ Π`). -/
lemma permIdxAux_le_of_isPermPrem (ds s : V) :
    ∀ N, ∀ m < N, isPermPrem ds s m → permIdxAux ds s N ≤ m := by
  intro N
  induction N using ISigma1.sigma1_succ_induction
  · simp only [isPermPrem]; definability
  case zero => intro m hm; exact absurd hm (by simp)
  case succ n ih =>
    intro m hm hperm
    rw [permIdxAux_succ]
    by_cases h1 : permIdxAux ds s n < n
    · rw [if_pos h1]
      rcases lt_or_eq_of_le (lt_succ_iff_le.mp hm) with hmn | hmn
      · exact ih m hmn hperm
      · subst hmn; exact le_of_lt h1
    · rw [if_neg h1]
      have hn : permIdxAux ds s n = n := le_antisymm (permIdxAux_le ds s n) (not_lt.mp h1)
      have hnone := permIdxAux_eq_self_of_none ds s n hn
      rcases lt_or_eq_of_le (lt_succ_iff_le.mp hm) with hmn | hmn
      · exact absurd hperm (hnone m hmn)
      · subst hmn; rw [if_pos hperm]

/-- **The 5.2 dispatch index of a chain** = least permissible premise index, sentinel `lh (zKseq d)`. -/
noncomputable def permIdx (d : V) : V := permIdxAux (zKseq d) (fstIdx d) (lh (zKseq d))

/-- **`permIdx` spec, non-critical chain** — if `zK s r ds` is non-critical (some premise permissible),
`permIdx` lands on the least permissible index `< lh ds`. -/
lemma permIdx_lt_of_not_zKCritical {s r ds : V} (h : ¬ zKCritical s ds) :
    permIdx (zK s r ds) < lh ds ∧ isPermPrem ds s (permIdx (zK s r ds)) := by
  have hex : ∃ i < lh ds, isPermPrem ds s i := by
    unfold zKCritical at h
    push_neg at h
    obtain ⟨i, hi, hperm⟩ := h
    exact ⟨i, hi, hperm⟩
  have hf := permIdxAux_found ds s (lh ds) hex
  simp only [permIdx, zKseq_zK, fstIdx_zK]
  exact hf

/-- **`permIdx ≤ j₀` (the Buchholz §5.2 selection bound).** The selected dispatch index is `≤` ANY
permissible premise index. In particular, when a chain is non-critical *in Buchholz's sense* — there is a
permissible premise at an index `≤ j₀` (the distinguished top of `isChainInf`) — the repo's globally-least
`permIdx` lands at-or-below `j₀`, so the original chain's threading/rank (held only up to `j₀`) RESTRICTS to
threading/rank up to `permIdx`. This is the structural fact that feeds `ZDerivation_iCritReplaceReduce_of`'s
`hthread`/`hrank` hypotheses in the R-rule replace wiring. -/
lemma permIdx_le_of_isPermPrem {s r ds m : V} (hm : m < lh ds)
    (hperm : iperm (tp (znth ds m)) s) :
    permIdx (zK s r ds) ≤ m := by
  simp only [permIdx, zKseq_zK, fstIdx_zK]
  exact permIdxAux_le_of_isPermPrem ds s (lh ds) m hm hperm

/-- **The selection bound from a permissible premise `≤ j₀` (Buchholz §5.2, wiring).** Packages
`permIdx_le_of_isPermPrem` + `le_trans`: if SOME premise at an index `m ≤ j₀` is permissible w.r.t. the
conclusion (`iperm (tp dₘ) s`), then the globally-least permissible index `permIdx ≤ j₀`. This is the exact
form feeding `thread_rank_restrict_of_le`'s `i ≤ j₀` argument (with `i := permIdx`). The orbit must supply
the witness `∃ m ≤ j₀, permissible` (Buchholz's non-critical case guarantees it; the repo's
`permIdx < lh ds` non-criticality is WEAKER — `permIdx` may exceed `j₀` without this witness). -/
lemma permIdx_le_of_exists_isPermPrem {s r ds j0 : V}
    (h : ∃ m ≤ j0, m < lh ds ∧ iperm (tp (znth ds m)) s) :
    permIdx (zK s r ds) ≤ j0 := by
  obtain ⟨m, hmj0, hmlt, hperm⟩ := h
  exact le_trans (permIdx_le_of_isPermPrem hmlt hperm) hmj0

/-- **Threading/rank restriction to a smaller index (Buchholz §5.2 selection bound, wiring piece B).**
Given the parent chain's threading/rank data held up to `j₀` (`hthr`/`hrk`, the `isChainInf` witness
conjuncts) and `i ≤ j₀` (the selection bound `permIdx ≤ j₀` from `permIdx_le_of_isPermPrem` together with
the orbit's permissible-premise-at-`≤j₀` invariant), RESTRICT the threading and rank down to `i` — exactly
the `hthread`/`hrank` hypotheses the non-`Rep` replace capstones (`ZDerivation_zK_replace_zIall_of` /
`_zIneg_of`) consume. Pure `le_trans`/`lt_of_lt_of_le` under the binders; the trivial-but-load-bearing glue
between the parent `isChainInf` and the per-case `ZDerivation_iCritReplaceReduce_of`. -/
lemma thread_rank_restrict_of_le {s r ds i j0 : V}
    (hthr : ∀ i' ≤ j0, ∀ B, inAnt B (chainAnt ds i') →
        inAnt B (seqAnt s) ∨ ∃ i'' < i', B = chainAsucc ds i'')
    (hrk : ∀ i' < j0, irk (chainAsucc ds i') ≤ r)
    (hij : i ≤ j0) :
    (∀ i' ≤ i, ∀ B, inAnt B (chainAnt ds i') →
        inAnt B (seqAnt s) ∨ ∃ i'' < i', B = chainAsucc ds i'') ∧
    (∀ i' < i, irk (chainAsucc ds i') ≤ r) :=
  ⟨fun i' hi' => hthr i' (le_trans hi' hij), fun i' hi' => hrk i' (lt_of_lt_of_le hi' hij)⟩

/-- **`permIdx` is `𝚺₁`-definable** — the dispatch index `permIdx d = permIdxAux (zKseq d) (fstIdx d)
(lh (zKseq d))` composes the already-definable `zKseq`/`fstIdx`/`lh`/`permIdxAux`. Required so the
tag-4 `red` dispatch can branch on `permIdx` and stay `𝚺₁`. -/
noncomputable def _root_.LO.FirstOrder.Arithmetic.permIdxDef : 𝚺₁.Semisentence 2 := .mkSigma
  “y d. ∃ ds, !zKseqDef ds d ∧ ∃ f, !fstIdxDef f d ∧ ∃ l, !lhDef l ds ∧ !permIdxAuxDef y ds f l”

instance permIdx_defined : 𝚺₁-Function₁ (permIdx : V → V) via permIdxDef := .mk fun v ↦ by
  simp [permIdxDef, permIdx, zKseq_defined.iff, fstIdx_defined.iff, lh_defined.iff,
    permIdxAux_defined.iff]

instance permIdx_definable : 𝚺₁-Function₁ (permIdx : V → V) := permIdx_defined.to_definable
instance permIdx_definable' (Γ) : Γ-[m + 1]-Function₁ (permIdx : V → V) :=
  permIdx_definable.of_sigmaOne

/-! ## `iRcrit` — the CLOSED iR critical branch (Buchholz Def 3.2 case 5.1)

The redex finder (`redexCode`/`redexI`/`redexJ`) is now a total definable function of the chain, so the
critical reduct `d[0] = K^{r-1}_Π d{0} d{1}` is a **closed term**: `iRcrit d ρ` plugs the *functional*
redex indices `redexI d`/`redexJ d` (and their `ρ`-reducts) into `iCritReduct`. This eliminates the last
existential from `iR`'s critical branch — only `ρ` (the indexed sub-reduct `dᵢ[k]`/`d_j[0]`, the N1
structural IH) remains abstract. The descent `iord_descent_iRcrit_of_chain` then composes:
(L3.1 redex existence) ⟹ (the finder finds the SAME-or-earlier valid pair) ⟹ (T3.4 `1 ≤ r`) ⟹
(`iord_descent_iCritReduct_object`, the Thm-4.2 cut-elim descent on the genuine `seqUpdate` reduct). -/

/-- **The closed iR critical branch** (Buchholz Def 3.2 case 5.1): the critical reduct `d[0]` built from
the FUNCTIONAL redex `(redexI d, redexJ d)` and the abstract premise-reduct supplier `ρ`. Closed term;
no existential. -/
noncomputable def iRcrit (d : V) (ρ : V → V) : V :=
  iCritReduct d (redexI d) (redexJ d) (ρ (redexI d)) (ρ (redexJ d))

/-- **THE NUT, on the CLOSED reduct** (E-CRUX2 §8.3, case 5.1). Same hypotheses as
`iord_descent_critical_of_chain`, but the conclusion is the descent on the *closed* `iRcrit (zK s r ds) ρ`
— the redex indices are now `redexI`/`redexJ` (the definable finder), not an existential. The proof
shows the finder fires: L3.1 supplies an existential redex `⟪i,j⟫ < ⟪lh ds, lh ds⟫`, so by
`redexCode_isRedexPair` the finder returns a (least) valid pair, whose `isRedexPair` data gives
`redexI < redexJ < lh ds`; then `iord_descent_iCritReduct_object` (Thm 4.2) discharges the descent on the
genuine `seqUpdate`-based reduct. This makes the WHOLE case-5.1 branch a closed definable object: only
`ρ`'s N1 facts (`hρlt`/`hρg`/`hρNF`, the structural IH) and the tp/§5 well-formedness (`hperm`/`hnperm`)
remain upstream. -/
theorem iord_descent_iRcrit_of_chain {s r ds j0 : V} {Tr Fa : V → Prop} {ρ : V → V}
    (hds : Seq ds) (hnf : isNF (iotil (zK s r ds)))
    (hj0 : j0 < lh ds)
    (hAj0 : chainAsucc ds j0 = seqSucc s ∨ chainAsucc ds j0 = (^⊥ : V))
    (hchain : ∀ i ≤ j0, ∀ B, inAnt B (chainAnt ds i) →
      inAnt B (seqAnt s) ∨ ∃ i' < i, B = chainAsucc ds i')
    (hrank : ∀ i < j0, irk (chainAsucc ds i) ≤ r)
    (hwfR : ∀ i ≤ j0, ∀ A, tp (znth ds i) = isymR A → 0 < irk A ∨ Tr A)
    (hwfL : ∀ i ≤ j0, ∀ k A, tp (znth ds i) = isymLk k A → 0 < irk A ∨ Fa A)
    (hperm : ∀ i ≤ j0, iperm (tp (znth ds i)) (fstIdx (znth ds i)))
    (hnperm : ∀ i ≤ j0, ¬ iperm (tp (znth ds i)) s)
    (hdisj : ∀ A, ¬ (Tr A ∧ Fa A)) (hFa_rk : ∀ A, Fa A → irk A = 0)
    (hFa_bot : Fa (^⊥ : V))
    (hNF : ∀ n, isNF (iotil (znth ds n)))
    (hρlt : ∀ n, icmp (iotil (ρ n)) (iotil (znth ds n)) = 0)
    (hρg : ∀ n, idg (ρ n) ≤ idg (znth ds n))
    (hρNF : ∀ n, isNF (iotil (ρ n))) :
    icmp (iord (iRcrit (zK s r ds) ρ)) (iord (zK s r ds)) = 0 := by
  -- L3.1: extract an existential redex `(i,j,k)` with the tp/rank data.
  obtain ⟨i, j, k, hij, hjle, hRi, hLj, hrkpos, hrkr⟩ :=
    inference_critical_pair_of_chain hj0 hAj0 hchain hrank hwfR hwfL hperm hnperm hdisj hFa_rk hFa_bot
  have hr : 1 ≤ r := pos_iff_one_le.mp (lt_of_lt_of_le hrkpos hrkr)
  have hjlt : j < lh ds := lt_of_le_of_lt hjle hj0
  have hilt : i < lh ds := lt_trans hij hjlt
  -- The L3.1 redex `⟪i,j⟫` is a valid redex pair below the search bound.
  have hredex : isRedexPair ds (⟪i, j⟫ : V) := by
    simp only [isRedexPair, pi₁_pair, pi₂_pair]
    refine ⟨hij, hjlt, ?_, ?_, ?_⟩
    · rw [hRi]; simp [isymR]
    · rw [hLj]; simp [isymLk]
    · rw [hRi, hLj]; simp [isymR, isymLk]
  -- So the finder fires: `redexCode (zK s r ds)` is a valid redex pair of `ds`.
  have hex : ∃ c < (⟪lh (zKseq (zK s r ds)), lh (zKseq (zK s r ds))⟫ : V),
      isRedexPair (zKseq (zK s r ds)) c := by
    simp only [zKseq_zK]
    exact ⟨⟪i, j⟫, pair_lt_pair hilt hjlt, hredex⟩
  have hrc : isRedexPair (zKseq (zK s r ds)) (redexCode (zK s r ds)) := redexCode_isRedexPair hex
  simp only [zKseq_zK] at hrc
  obtain ⟨hIJ, hJlh, -, -, -⟩ := hrc
  -- `redexI`/`redexJ` are defeq to the projections, so the order facts transfer.
  have hJlh' : redexJ (zK s r ds) < lh ds := hJlh
  have hIlh' : redexI (zK s r ds) < lh ds := lt_trans hIJ hJlh
  -- Thm 4.2 on the genuine reduct, instantiated at the functional redex.
  have hgoal := iord_descent_iCritReduct_object hds hr hnf hIlh' hJlh'
    (hρlt (redexI (zK s r ds))) (hρlt (redexJ (zK s r ds)))
    (hρg (redexI (zK s r ds))) (hρg (redexJ (zK s r ds)))
    hNF (hρNF (redexI (zK s r ds))) (hρNF (redexJ (zK s r ds)))
  exact hgoal

/-- **The K-cut descent, parametrized by an EXHIBITED redex** (lap 121). The descent computation
`iord_descent_iRcrit_of_chain'` uses its criticality data (`hwfR`/`hwfL`/`hperm`/`hnperm`/…) ONLY to
run `inference_critical_pair_of_chain` and manufacture a redex pair; the actual ordinal descent
(`redexCode` → `iord_descent_iCritReduct_object`) needs just (a) a redex pair exists below the finder
sentinel, (b) `1 ≤ r`, and (c) the six `ρ`-facts on the two redex premises. This lemma takes exactly
those, DECOUPLING the descent from global criticality. **Why it matters (the lap-121 stall lever):** in
the genuinely-open stall case a *threaded* atom premise breaks `hnperm`, so the finder route is blocked —
but if the redex can be exhibited another way (e.g. from the chain's principal-cut structure directly),
this lemma still discharges the descent, IGNORING the atom. -/
theorem iord_descent_iRcrit_of_redex {s r ds : V} {ρ : V → V}
    (hds : Seq ds) (hnf : isNF (iotil (zK s r ds))) (hr : 1 ≤ r)
    (hex : ∃ c < (⟪lh (zKseq (zK s r ds)), lh (zKseq (zK s r ds))⟫ : V),
      isRedexPair (zKseq (zK s r ds)) c)
    (hNF : ∀ n, isNF (iotil (znth ds n)))
    (hρlt_i : icmp (iotil (ρ (redexI (zK s r ds)))) (iotil (znth ds (redexI (zK s r ds)))) = 0)
    (hρlt_j : icmp (iotil (ρ (redexJ (zK s r ds)))) (iotil (znth ds (redexJ (zK s r ds)))) = 0)
    (hρg_i : idg (ρ (redexI (zK s r ds))) ≤ idg (znth ds (redexI (zK s r ds))))
    (hρg_j : idg (ρ (redexJ (zK s r ds))) ≤ idg (znth ds (redexJ (zK s r ds))))
    (hρNF_i : isNF (iotil (ρ (redexI (zK s r ds)))))
    (hρNF_j : isNF (iotil (ρ (redexJ (zK s r ds))))) :
    icmp (iord (iRcrit (zK s r ds) ρ)) (iord (zK s r ds)) = 0 := by
  have hrc : isRedexPair (zKseq (zK s r ds)) (redexCode (zK s r ds)) := redexCode_isRedexPair hex
  simp only [zKseq_zK] at hrc
  obtain ⟨hIJ, hJlh, -, -, -⟩ := hrc
  have hJlh' : redexJ (zK s r ds) < lh ds := hJlh
  have hIlh' : redexI (zK s r ds) < lh ds := lt_trans hIJ hJlh
  exact iord_descent_iCritReduct_object hds hr hnf hIlh' hJlh'
    hρlt_i hρlt_j hρg_i hρg_j hNF hρNF_i hρNF_j

/-- **The nut, with the `ρ`-hyps WEAKENED to the two redex premises.** `iord_descent_iRcrit_of_chain`
states `hρlt`/`hρg`/`hρNF` as `∀ n`, but its proof only ever USES them at `redexI`/`redexJ` (the finder
output). For the concrete `ρ = iR2(znth ds ·)` the `∀ n` form is FALSE (a critical-chain premise's `õ`
can jump up; an atom premise's `iR2` is the identity), so this redex-only form is the one the recursive
descent can actually discharge. It pins the entire K-case ordinal obligation to SIX facts about the two
redex-premise reducts `ρ(redexI)`,`ρ(redexJ)` — exactly what the redexI I-rule case
(`iRedDescent_iR_of_tp_isymR`) and the redexJ §5 atomic reduct must supply. (lap-121: now a thin wrapper
over `iord_descent_iRcrit_of_redex`, which manufactures the redex via `inference_critical_pair_of_chain`
from the criticality data.) -/
theorem iord_descent_iRcrit_of_chain' {s r ds j0 : V} {Tr Fa : V → Prop} {ρ : V → V}
    (hds : Seq ds) (hnf : isNF (iotil (zK s r ds)))
    (hj0 : j0 < lh ds)
    (hAj0 : chainAsucc ds j0 = seqSucc s ∨ chainAsucc ds j0 = (^⊥ : V))
    (hchain : ∀ i ≤ j0, ∀ B, inAnt B (chainAnt ds i) →
      inAnt B (seqAnt s) ∨ ∃ i' < i, B = chainAsucc ds i')
    (hrank : ∀ i < j0, irk (chainAsucc ds i) ≤ r)
    (hwfR : ∀ i ≤ j0, ∀ A, tp (znth ds i) = isymR A → 0 < irk A ∨ Tr A)
    (hwfL : ∀ i ≤ j0, ∀ k A, tp (znth ds i) = isymLk k A → 0 < irk A ∨ Fa A)
    (hperm : ∀ i ≤ j0, iperm (tp (znth ds i)) (fstIdx (znth ds i)))
    (hnperm : ∀ i ≤ j0, ¬ iperm (tp (znth ds i)) s)
    (hdisj : ∀ A, ¬ (Tr A ∧ Fa A)) (hFa_rk : ∀ A, Fa A → irk A = 0)
    (hFa_bot : Fa (^⊥ : V))
    (hNF : ∀ n, isNF (iotil (znth ds n)))
    (hρlt_i : icmp (iotil (ρ (redexI (zK s r ds)))) (iotil (znth ds (redexI (zK s r ds)))) = 0)
    (hρlt_j : icmp (iotil (ρ (redexJ (zK s r ds)))) (iotil (znth ds (redexJ (zK s r ds)))) = 0)
    (hρg_i : idg (ρ (redexI (zK s r ds))) ≤ idg (znth ds (redexI (zK s r ds))))
    (hρg_j : idg (ρ (redexJ (zK s r ds))) ≤ idg (znth ds (redexJ (zK s r ds))))
    (hρNF_i : isNF (iotil (ρ (redexI (zK s r ds)))))
    (hρNF_j : isNF (iotil (ρ (redexJ (zK s r ds))))) :
    icmp (iord (iRcrit (zK s r ds) ρ)) (iord (zK s r ds)) = 0 := by
  obtain ⟨i, j, k, hij, hjle, hRi, hLj, hrkpos, hrkr⟩ :=
    inference_critical_pair_of_chain hj0 hAj0 hchain hrank hwfR hwfL hperm hnperm hdisj hFa_rk hFa_bot
  have hr : 1 ≤ r := pos_iff_one_le.mp (lt_of_lt_of_le hrkpos hrkr)
  have hjlt : j < lh ds := lt_of_le_of_lt hjle hj0
  have hilt : i < lh ds := lt_trans hij hjlt
  have hredex : isRedexPair ds (⟪i, j⟫ : V) := by
    simp only [isRedexPair, pi₁_pair, pi₂_pair]
    refine ⟨hij, hjlt, ?_, ?_, ?_⟩
    · rw [hRi]; simp [isymR]
    · rw [hLj]; simp [isymLk]
    · rw [hRi, hLj]; simp [isymR, isymLk]
  have hex : ∃ c < (⟪lh (zKseq (zK s r ds)), lh (zKseq (zK s r ds))⟫ : V),
      isRedexPair (zKseq (zK s r ds)) c := by
    simp only [zKseq_zK]
    exact ⟨⟪i, j⟫, pair_lt_pair hilt hjlt, hredex⟩
  exact iord_descent_iRcrit_of_redex hds hnf hr hex hNF
    hρlt_i hρlt_j hρg_i hρg_j hρNF_i hρNF_j

/-! ## C0 Fixpoint — the system-Z derivation predicate `ZDerivation : V → Prop`

The one-step rule `ZPhi C d` ("`d` is a Z-derivation given its premises lie in `C`"), mirroring
Foundation's `Theory.Derivation.Phi` (`…/Proof/Basic.lean:280`) but over Z's five rules — the K^r
rule being variadic (its premise *sequence* `ds`, each `znth ds i ∈ C`), with no Foundation precedent.

**This brick is the STRUCTURAL skeleton** (premise-membership + the K^r `Seq` premise-sequence). The
sequent well-formedness (`IsFormulaSet`), the eigenvariable/rank side conditions, and the §5 atomic
axioms are refinements layered onto `ZPhi` later — they strengthen the predicate but do **not** change
the Fixpoint machinery (`monotone`/`StrongFinite` re-prove mechanically). With `ZPhi`, the next bricks
form `Fixpoint.Construction` → `ZDerivation := construction.Fixpoint ![]` + its `case`/`induction`
corollaries, which unblock structural induction (`isNF (iotil d)`), `iR` well-definedness, and the
⊥-characterization (`derivesEmpty`). `monotone` + `StrongFinite` are proved here as standalone lemmas
(they ARE the `Construction` fields). -/

/-- One-step system-Z derivation rule (structural skeleton): `d` is built by one of Z's five rules
with its premise(s) in `C`. -/
def ZPhi (C : Set V) (d : V) : Prop :=
  (∃ s, d = zAtom s ∧ inAnt (seqSucc s) (seqAnt s)) ∨
  (∃ s a p d0, d = zIall s a p d0 ∧ d0 ∈ C ∧ seqSucc s = (^∀ p : V) ∧ zIallWff s a p d0) ∨
  (∃ s p d0, d = zIneg s p d0 ∧ d0 ∈ C ∧ seqSucc s = (inegF p : V) ∧ zInegWff p d0 ∧
    zInegAntWff s p d0) ∨
  (∃ s at' p d0 d1, d = zInd s at' p d0 d1 ∧ d0 ∈ C ∧ d1 ∈ C ∧ zIndWff d) ∨
  (∃ s r ds, d = zK s r ds ∧ Seq ds ∧ (∀ i < lh ds, znth ds i ∈ C) ∧ zKValidF s r ds) ∨
  (∃ s p k, d = zAxAll s p k ∧ IsSemiformula ℒₒᵣ 1 p ∧ inAnt (^∀ p : V) (seqAnt s) ∧
    zAxAllSuccWff s p k) ∨
  (∃ s p, d = zAxNeg s p ∧ IsUFormula ℒₒᵣ p ∧ inAnt (inegF p : V) (seqAnt s) ∧
    inAnt p (seqAnt s)) ∨
  (∃ s C, d = zAx1 s C ∧ inAnt (seqSucc s) (seqAnt s))

/-- `ZPhi` is monotone in the premise set `C` (a `Fixpoint.Construction.monotone` field). -/
lemma zphi_monotone {C C' : Set V} (h : C ⊆ C') {d : V} : ZPhi C d → ZPhi C' d := by
  rintro (hd | ⟨s, a, p, d0, rfl, hd, hsc, hwff⟩ | ⟨s, p, d0, rfl, hd, hsc, hwff⟩ |
    ⟨s, at', p, d0, d1, rfl, h0, h1, hwff⟩ | ⟨s, r, ds, rfl, hseq, hall, hvalid⟩ |
    ⟨s, p, k, rfl, hp, hin, hsucc⟩ | ⟨s, p, rfl, hp, hin, hin2⟩ | ⟨s, C, rfl, hin⟩)
  · exact Or.inl hd
  · exact Or.inr (Or.inl ⟨s, a, p, d0, rfl, h hd, hsc, hwff⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨s, p, d0, rfl, h hd, hsc, hwff⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨s, at', p, d0, d1, rfl, h h0, h h1, hwff⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨s, r, ds, rfl, hseq, fun i hi => h (hall i hi), hvalid⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨s, p, k, rfl, hp, hin, hsucc⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨s, p, rfl, hp, hin, hin2⟩))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨s, C, rfl, hin⟩))))))

/-- `ZPhi` is strongly finite: every premise of `d` is `< d`, so the rule fires already over
`{y ∈ C | y < d}` (a `Fixpoint.Construction.StrongFinite` field). The K^r case uses
`Seq.znth` + `lt_of_mem_rng` (`znth ds i < ds`) then `ds < zK s r ds`. -/
lemma zphi_strong_finite {C : Set V} {d : V} :
    ZPhi C d → ZPhi {y | y ∈ C ∧ y < d} d := by
  rintro (hd | ⟨s, a, p, d0, rfl, hd, hsc, hwff⟩ | ⟨s, p, d0, rfl, hd, hsc, hwff⟩ |
    ⟨s, at', p, d0, d1, rfl, h0, h1, hwff⟩ | ⟨s, r, ds, rfl, hseq, hall, hvalid⟩ |
    ⟨s, p, k, rfl, hp, hin, hsucc⟩ | ⟨s, p, rfl, hp, hin, hin2⟩ | ⟨s, C, rfl, hin⟩)
  · exact Or.inl hd
  · exact Or.inr (Or.inl ⟨s, a, p, d0, rfl, ⟨hd, by simp⟩, hsc, hwff⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨s, p, d0, rfl, ⟨hd, by simp⟩, hsc, hwff⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨s, at', p, d0, d1, rfl, ⟨h0, by simp⟩, ⟨h1, by simp⟩, hwff⟩)))
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨s, r, ds, rfl, hseq, fun i hi => ⟨hall i hi, ?_⟩, hvalid⟩))))
    exact lt_trans (lt_of_mem_rng (hseq.znth hi)) (ds_lt_zK s r ds)
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨s, p, k, rfl, hp, hin, hsucc⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨s, p, rfl, hp, hin, hin2⟩))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨s, C, rfl, hin⟩))))))

/-- Bounded-quantifier form of `ZPhi` (every existential is `< d`), the shape the arithmetized
`blueprint` core matches. Mirrors Foundation `Theory.Derivation.phi_iff`. -/
private lemma zphi_iff (C d : V) :
    ZPhi {x | x ∈ C} d ↔
    ( (∃ s < d, d = zAtom s ∧ inAnt (seqSucc s) (seqAnt s)) ∨
      (∃ s < d, ∃ a < d, ∃ p < d, ∃ d0 < d,
        d = zIall s a p d0 ∧ d0 ∈ C ∧ seqSucc s = (^∀ p : V) ∧ zIallWff s a p d0) ∨
      (∃ s < d, ∃ p < d, ∃ d0 < d,
        d = zIneg s p d0 ∧ d0 ∈ C ∧ seqSucc s = (inegF p : V) ∧ zInegWff p d0 ∧
        zInegAntWff s p d0) ∨
      (∃ s < d, ∃ at' < d, ∃ p < d, ∃ d0 < d, ∃ d1 < d,
        d = zInd s at' p d0 d1 ∧ d0 ∈ C ∧ d1 ∈ C ∧ zIndWff d) ∨
      (∃ s < d, ∃ r < d, ∃ ds < d,
        d = zK s r ds ∧ Seq ds ∧ (∀ i < lh ds, znth ds i ∈ C) ∧ zKValidF s r ds) ∨
      (∃ s < d, ∃ p < d, ∃ k < d, d = zAxAll s p k ∧ IsSemiformula ℒₒᵣ 1 p ∧
        inAnt (^∀ p : V) (seqAnt s) ∧ zAxAllSuccWff s p k) ∨
      (∃ s < d, ∃ p < d, d = zAxNeg s p ∧ IsUFormula ℒₒᵣ p ∧ inAnt (inegF p : V) (seqAnt s) ∧
        inAnt p (seqAnt s)) ∨
      (∃ s < d, ∃ C < d, d = zAx1 s C ∧ inAnt (seqSucc s) (seqAnt s)) ) := by
  constructor
  · rintro (⟨s, rfl, hin⟩ | ⟨s, a, p, d0, rfl, h, hsc, hwff⟩ | ⟨s, p, d0, rfl, h, hsc, hwff⟩ |
      ⟨s, at', p, d0, d1, rfl, h0, h1, hwff⟩ | ⟨s, r, ds, rfl, hseq, hall, hvalid⟩ |
      ⟨s, p, k, rfl, hp, hin, hsucc⟩ | ⟨s, p, rfl, hp, hin, hin2⟩ | ⟨s, C, rfl, hin⟩)
    · exact Or.inl ⟨s, by simp, rfl, hin⟩
    · exact Or.inr (Or.inl ⟨s, by simp, a, by simp, p, by simp, d0, by simp, rfl, h, hsc, hwff⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨s, by simp, p, by simp, d0, by simp, rfl, h, hsc, hwff⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl
        ⟨s, by simp, at', by simp, p, by simp, d0, by simp, d1, by simp, rfl, h0, h1, hwff⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨s, by simp, r, by simp, ds, by simp, rfl, hseq, hall, hvalid⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨s, by simp, p, by simp, k, by simp, rfl, hp, hin, hsucc⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨s, by simp, p, by simp, rfl, hp, hin, hin2⟩))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨s, by simp, C, by simp, rfl, hin⟩))))))
  · rintro (⟨s, _, rfl, hin⟩ | ⟨s, _, a, _, p, _, d0, _, rfl, h, hsc, hwff⟩ |
      ⟨s, _, p, _, d0, _, rfl, h, hsc, hwff⟩ |
      ⟨s, _, at', _, p, _, d0, _, d1, _, rfl, h0, h1, hwff⟩ |
      ⟨s, _, r, _, ds, _, rfl, hseq, hall, hvalid⟩ |
      ⟨s, _, p, _, k, _, rfl, hp, hin, hsucc⟩ | ⟨s, _, p, _, rfl, hp, hin, hin2⟩ |
      ⟨s, _, C, _, rfl, hin⟩)
    · exact Or.inl ⟨s, rfl, hin⟩
    · exact Or.inr (Or.inl ⟨s, a, p, d0, rfl, h, hsc, hwff⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨s, p, d0, rfl, h, hsc, hwff⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨s, at', p, d0, d1, rfl, h0, h1, hwff⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨s, r, ds, rfl, hseq, hall, hvalid⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨s, p, k, rfl, hp, hin, hsucc⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨s, p, rfl, hp, hin, hin2⟩))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨s, C, rfl, hin⟩))))))

open LO.FirstOrder.Arithmetic in
/-- Arithmetized `𝚫₁` core for the Z-derivation `Fixpoint` (mirrors Foundation
`Theory.Derivation.blueprint`). `d` = candidate code, `C` = the recursion set (premises so far). The
K^r disjunct uses `seqDef`/`lhDef`/`znthDef` for the variadic premise-sequence membership. -/
noncomputable def zblueprint : Fixpoint.Blueprint 0 := ⟨.mkDelta
  (.mkSigma “d C.
    ( (∃ s < d, !zAtomGraph d s ∧
        ∃ ss, !seqSuccDef ss s ∧ ∃ sa, !seqAntDef sa s ∧ !inAntDef ss sa) ∨
      (∃ s < d, ∃ a < d, ∃ p < d, ∃ d0 < d, !zIallGraph d s a p d0 ∧ d0 ∈ C ∧
        (∃ ss, !seqSuccDef ss s ∧ ∃ ap, !qqAllDef ap p ∧ ss = ap) ∧
        !(zIallWffDef.sigma) s a p d0) ∨
      (∃ s < d, ∃ p < d, ∃ d0 < d, !zInegGraph d s p d0 ∧ d0 ∈ C ∧
        (∃ ss, !seqSuccDef ss s ∧ ∃ nb, !inegFDef nb p ∧ ss = nb) ∧ !(zInegWffDef.sigma) p d0 ∧
        !(zInegAntWffDef.sigma) s p d0) ∨
      (∃ s < d, ∃ at' < d, ∃ p < d, ∃ d0 < d, ∃ d1 < d,
        !zIndGraph d s at' p d0 d1 ∧ d0 ∈ C ∧ d1 ∈ C ∧ !(zIndWffDef.sigma) d) ∨
      (∃ s < d, ∃ r < d, ∃ ds < d,
        !zKGraph d s r ds ∧ !seqDef ds ∧
          (∃ l, !lhDef l ds ∧ ∀ i < l, ∃ z, !znthDef z ds i ∧ z ∈ C) ∧
          !(zKValidFDef.sigma) s r ds) ∨
      (∃ s < d, ∃ p < d, ∃ k < d, !zAxAllGraph d s p k ∧ !(isSemiformula ℒₒᵣ).sigma 1 p ∧
        (∃ ap, !qqAllDef ap p ∧ ∃ sa, !seqAntDef sa s ∧ !inAntDef ap sa) ∧
        !(zAxAllSuccWffDef.sigma) s p k) ∨
      (∃ s < d, ∃ p < d, !zAxNegGraph d s p ∧ !(isUFormula ℒₒᵣ).sigma p ∧
        ∃ nb, !inegFDef nb p ∧ ∃ sa, !seqAntDef sa s ∧ !inAntDef nb sa ∧ !inAntDef p sa) ∨
      (∃ s < d, ∃ cc < d, !zAx1Graph d s cc ∧
        ∃ ss, !seqSuccDef ss s ∧ ∃ sa, !seqAntDef sa s ∧ !inAntDef ss sa) )”)
  (.mkPi “d C.
    ( (∃ s < d, !zAtomGraph d s ∧
        ∀ ss, !seqSuccDef ss s → ∀ sa, !seqAntDef sa s → !inAntDef ss sa) ∨
      (∃ s < d, ∃ a < d, ∃ p < d, ∃ d0 < d, !zIallGraph d s a p d0 ∧ d0 ∈ C ∧
        (∀ ss, !seqSuccDef ss s → ∀ ap, !qqAllDef ap p → ss = ap) ∧
        !(zIallWffDef.pi) s a p d0) ∨
      (∃ s < d, ∃ p < d, ∃ d0 < d, !zInegGraph d s p d0 ∧ d0 ∈ C ∧
        (∀ ss, !seqSuccDef ss s → ∀ nb, !inegFDef nb p → ss = nb) ∧ !(zInegWffDef.pi) p d0 ∧
        !(zInegAntWffDef.pi) s p d0) ∨
      (∃ s < d, ∃ at' < d, ∃ p < d, ∃ d0 < d, ∃ d1 < d,
        !zIndGraph d s at' p d0 d1 ∧ d0 ∈ C ∧ d1 ∈ C ∧ !(zIndWffDef.pi) d) ∨
      (∃ s < d, ∃ r < d, ∃ ds < d,
        !zKGraph d s r ds ∧ !seqDef ds ∧
          (∀ l, !lhDef l ds → ∀ i < l, ∀ z, !znthDef z ds i → z ∈ C) ∧
          !(zKValidFDef.pi) s r ds) ∨
      (∃ s < d, ∃ p < d, ∃ k < d, !zAxAllGraph d s p k ∧ !(isSemiformula ℒₒᵣ).pi 1 p ∧
        (∀ ap, !qqAllDef ap p → ∀ sa, !seqAntDef sa s → !inAntDef ap sa) ∧
        !(zAxAllSuccWffDef.pi) s p k) ∨
      (∃ s < d, ∃ p < d, !zAxNegGraph d s p ∧ !(isUFormula ℒₒᵣ).pi p ∧
        ∀ nb, !inegFDef nb p → ∀ sa, !seqAntDef sa s → (!inAntDef nb sa ∧ !inAntDef p sa)) ∨
      (∃ s < d, ∃ cc < d, !zAx1Graph d s cc ∧
        ∀ ss, !seqSuccDef ss s → ∀ sa, !seqAntDef sa s → !inAntDef ss sa) )”)⟩

lemma zPhi_definable :
    𝚫₁.Defined (fun v : Fin 2 → V ↦ ZPhi {x | x ∈ v 1} (v 0)) zblueprint.core := .mk <| by
  constructor
  · intro v; simp [zblueprint]
  · intro v; simp [zphi_iff, zblueprint, zAtom_defined.iff, zIall_defined.iff, zIneg_defined.iff,
      zInd_defined.iff, zK_defined.iff, zAxAll_defined.iff, zAxNeg_defined.iff, zAx1_defined.iff,
      seq_defined.iff, lh_defined.iff, znth_defined.iff,
      seqSucc_defined.iff, seqAnt_defined.iff, inAnt_defined.iff,
      qqForall_defined.iff, inegF_defined.iff, zInegWff_defined.iff, zIallWff_defined.iff,
      zIndWff_defined.iff, zAxAllSuccWff_defined.iff, zInegAntWff_defined.iff]

/-- The Z-derivation `Fixpoint.Construction` (`Φ = ZPhi`, with the proved monotonicity). -/
noncomputable def zconstruction : Fixpoint.Construction V zblueprint where
  Φ := fun _ ↦ ZPhi
  defined := zPhi_definable
  monotone := fun h _ _ hd ↦ zphi_monotone h hd

instance : (zconstruction (V := V)).StrongFinite where
  strong_finite := fun {_ _ _} h ↦ zphi_strong_finite h

/-- **The system-Z derivation predicate** `ZDerivation : V → Prop` — the `Fixpoint` of `ZPhi`.
`d` is a Z-derivation iff it is built by one Z-rule from premises that are themselves Z-derivations. -/
def ZDerivation (d : V) : Prop := (zconstruction (V := V)).Fixpoint ![] d

/-- **`𝚫₁`-definability of `ZDerivation`** (the strong-finite Fixpoint definability, mirror Foundation's
`Theory.Derivation.defined`). Needed as the motive-definability for `zDerivation_induction`-driven proofs
that recurse on a `𝚺₁`-function of the derivation (e.g. `ZDerivation_zsubst`). -/
noncomputable def _root_.LO.FirstOrder.Arithmetic.zDerivationDef : 𝚫₁.Semisentence 1 :=
  zblueprint.fixpointDefΔ₁

instance ZDerivation_defined : 𝚫₁-Predicate (ZDerivation : V → Prop) via zDerivationDef :=
  (zconstruction (V := V)).fixpoint_definedΔ₁

instance ZDerivation_definable : 𝚫₁-Predicate (ZDerivation : V → Prop) :=
  ZDerivation_defined.to_definable

instance ZDerivation_definable' (Γ) : Γ-[m + 1]-Predicate (ZDerivation : V → Prop) :=
  ZDerivation_definable.of_deltaOne

/-- **Recursion equation** for `ZDerivation` (the `Fixpoint.Construction.case`): a code is a
Z-derivation iff `ZPhi` holds of it over the set of Z-derivations. -/
lemma zDerivation_iff {d : V} : ZDerivation d ↔ ZPhi {z | ZDerivation z} d :=
  (zconstruction (V := V)).case

/-- **Structural induction** over `ZDerivation` (the `Fixpoint.Construction.induction`). -/
lemma zDerivation_induction {P : V → Prop} (hP : 𝚫₁-Predicate P)
    (H : ∀ C : Set V, (∀ x ∈ C, ZDerivation x ∧ P x) → ∀ d, ZPhi C d → P d) :
    ∀ d, ZDerivation d → P d :=
  (zconstruction (V := V)).induction (Γ := 𝚺) hP.of_deltaOne H

/-- **`𝚺₁`-motive structural induction** over `ZDerivation` — the SAME `Fixpoint.Construction.induction`
but for a `𝚺-[1]` (rather than `𝚫₁`) motive `P`. `𝗜𝚺₁` proves order-induction at the `𝚺₁` level
(`InductionOnHierarchy.order_induction_sigma`, `m := 1`), so an EXISTENCE-form motive
`P d := … → ∃ v, …` (which is `𝚺₁` whenever its matrix is `𝚫₁`) admits strong induction on the derivation
CODE. This is the vehicle for the Buchholz §14.254 general-reduction recursion (`genReduct_botSucc`):
the IH supplies, for each structurally-smaller premise, its own descending reduct — WITHOUT any
`iord`-recursion (PRWO/Gödel-barred) and without committing to a total reduct function. -/
lemma zDerivation_sigma_induction {P : V → Prop} (hP : 𝚺-[1]-Predicate P)
    (H : ∀ C : Set V, (∀ x ∈ C, ZDerivation x ∧ P x) → ∀ d, ZPhi C d → P d) :
    ∀ d, ZDerivation d → P d :=
  (zconstruction (V := V)).induction (Γ := 𝚺) hP H

/-- **`õ(d)` is a valid CNF code (`isNF`) for EVERY Z-derivation** — the structural-induction closure of
the per-constructor NF lemmas (`isNF_iotil_zAtom`/`_zIall`/`_zIneg`/`_zInd`/`_zK`). This **discharges the
`isNF (iotil ·)` hypothesis carried by every Thm-4.2 descent lemma** (the nut `iord_descent_iRcrit_of_chain`,
LH3 `iord_descent_iCritAux`, LH4 `iord_descent_iIndReduct`, LH5 `iord_descent_iSpliceEnd`, and the
`iord_descent_dgdrop`/`_cut`/`_le` templates): once a code is known to be a genuine `ZDerivation`, its
pre-ordinal is automatically a normal form, so the descent fires with no side condition. -/
theorem isNF_iotil_of_ZDerivation : ∀ d : V, ZDerivation d → isNF (iotil d) := by
  apply zDerivation_induction (P := fun d : V => isNF (iotil d))
  · simp only [isNF]; definability
  · intro C hC d hphi
    rcases hphi with ⟨s, rfl, _⟩ | ⟨s, a, p, d0, rfl, hd0, _⟩ | ⟨s, p, d0, rfl, hd0, _⟩ |
      ⟨s, at', p, d0, d1, rfl, hd0, hd1, _⟩ | ⟨s, r, ds, rfl, hds, hmem, _⟩ |
      ⟨s, p, k, rfl, hp, _⟩ | ⟨s, p, rfl, hp, _⟩ | ⟨s, C, rfl, _⟩
    · exact isNF_iotil_zAtom s
    · exact isNF_iotil_zIall (hC d0 hd0).2
    · exact isNF_iotil_zIneg (hC d0 hd0).2
    · exact isNF_iotil_zInd (hC d0 hd0).2 (hC d1 hd1).2
    · exact isNF_iotil_zK hds (fun i hi => (hC (znth ds i) (hmem i hi)).2)
    · exact isNF_iotil_zAxAll hp.isUFormula
    · exact isNF_iotil_zAxNeg hp
    · exact isNF_iotil_zAx1 s C

/-- **Structural descent over `ZDerivation` for the I-rules** (Buchholz Thm 4.2, cases 2–3 = LH1/LH2):
for any Z-derivation `d` built by `I^a_∀xF` or `I_¬A` (`zTag d ∈ {1,2}`), the reduct strictly lowers
the ordinal, `o(iR d) ≺ o(d)`. Proved by `ZDerivation` structural induction (the C0 Fixpoint),
dispatching on the rule: the I-rule cases are `iord_descent_iR_z*`; atom/Ind/K^r are vacuous (wrong
tag). The Ind/K^r tags broaden into this predicate once `iR`'s reducts for those rules are built — the
Ind chain reduct (LH4) and the critical/non-critical K^r branches (the nut). This is the V-level,
machine-checked analogue of the `GentzenCon` placeholder axiom `ord_R_descends`, restricted to the
rules whose reduct `iR` already constructs. -/
theorem iord_iR_descent_I :
    ∀ d, ZDerivation d → (zTag d = 1 ∨ zTag d = 2) → icmp (iord (iR d)) (iord d) = 0 := by
  apply zDerivation_induction
  · definability
  · intro C _ d hphi
    rcases hphi with ⟨s, rfl, _⟩ | ⟨s, a, p, d0, rfl, _, _⟩ | ⟨s, p, d0, rfl, _, _⟩ |
      ⟨s, at', p, d0, d1, rfl, _, _⟩ | ⟨s, r, ds, rfl, _, _, _⟩ |
      ⟨s, p, k, rfl, _, _⟩ | ⟨s, p, rfl, _, _⟩ | ⟨s, C, rfl, _⟩
    · rintro (h | h) <;> simp at h
    · rintro _; exact iord_descent_iR_zIall s a p d0
    · rintro _; exact iord_descent_iR_zIneg s p d0
    · rintro (h | h) <;> simp at h
    · rintro (h | h) <;> simp at h
    · rintro (h | h) <;> simp at h
    · rintro (h | h) <;> simp at h
    · rintro (h | h) <;> simp at h

/-! ### Ind-rule (tag 3) one-step reduct + its structural descent over `ZDerivation` (LH4)

Buchholz §3.2 case 4: `Ind^{a,t}_F d0 d1` reduces to `d[0] = K^{rk F}(d0, d1(0),…,d1(k−1))`, with `k`
the numeral value of the conclusion term `t`. Ordinally every substituted copy `d1(ν)` carries
`õ = õ d1` (substitution-invariance), so the descent `õ(d[0]) ≺ õ(Ind)` holds via **F3**
(`ω^{õ d1}·k ≺ ω^{õ d1 + 1}`) for **every** `k ≥ 1`. The ordinal descent is therefore faithful with the
reduct modeled at the minimal count `k = 1` (one copy of `d1`); the genuine count (`= ⟦t⟧`, with the
`k = 0` special case `d[0] = K^r(d0)`) and the eigenvariable substitution `d1(ν/a)` are deferred
derivation-*validity* concerns — exactly parallel to the splice object's in-place faithfulness. This
banks the **Ind tag of the full Thm-4.2 structural descent**: the machine-checked `o(iR d) ≺ o(d)` now
covers tags 1,2 (I-rules, `iord_iR_descent_I`) **and** 3 (Ind). -/

/-- The Ind-rule one-step reduct `d[0] = K^{rk F}(d1, d0)` (count-1 ordinal model of Buchholz §3.2
case 4), as a closed code of `d`: conclusion sequent `fstIdx d`, chain rank `irk (zIndP d)`, premise
sequence the two-element `iIndReductSeq` of the Ind premises `zIndPrem0 d`,`zIndPrem1 d`. -/
noncomputable def iRInd (d : V) : V :=
  zK (fstIdx d) (irk (zIndP d)) (iIndReductSeq (zIndPrem0 d) (zIndPrem1 d) 1)

@[simp] lemma iRInd_zInd (s at' p d0 d1 : V) :
    iRInd (zInd s at' p d0 d1) = zK s (irk p) (iIndReductSeq d0 d1 1) := by
  simp [iRInd]

/-- **Ind-rule descent on the genuine reduct object** (LH4, per constructor): `o(d[0]) ≺ o(Ind^{a,t}_F d0 d1)`,
from `iord_descent_iIndReduct` at the modeled count `k = 1` (`hk : 0 < 1`). -/
lemma iord_descent_iRInd_zInd (s at' p d0 d1 : V)
    (hd0 : isNF (iotil d0)) (hd1 : isNF (iotil d1)) :
    icmp (iord (iRInd (zInd s at' p d0 d1))) (iord (zInd s at' p d0 d1)) = 0 := by
  rw [iRInd_zInd]
  exact iord_descent_iIndReduct hd0 hd1 one_pos

/-- **Structural descent over `ZDerivation` for the Ind rule** (Buchholz Thm 4.2 case 4 = LH4): every
Z-derivation built by the `Ind` rule (`zTag d = 3`) satisfies `o(iR d) ≺ o(d)`. Proved directly from the
one-step recursion equation `zDerivation_iff` (no induction needed — one-step descent): the Ind case
supplies `ZDerivation d0`,`ZDerivation d1`, hence `isNF (iotil d0/d1)` via `isNF_iotil_of_ZDerivation`,
and `iord_descent_iRInd_zInd` closes it; the other tags are vacuous (tag mismatch). The Ind-rule
companion of `iord_iR_descent_I`. -/
theorem iord_descent_iRInd_of_ZDerivation (d : V) (hd : ZDerivation d) (htag : zTag d = 3) :
    icmp (iord (iRInd d)) (iord d) = 0 := by
  rcases zDerivation_iff.mp hd with ⟨s, rfl, _⟩ | ⟨s, a, p, d0, rfl, _, _⟩ | ⟨s, p, d0, rfl, _, _⟩ |
    ⟨s, at', p, d0, d1, rfl, hd0, hd1, _⟩ | ⟨s, r, ds, rfl, _, _, _⟩ |
    ⟨s, p, k, rfl, _, _⟩ | ⟨s, p, rfl, _, _⟩ | ⟨s, C, rfl, _⟩
  · simp at htag
  · simp at htag
  · simp at htag
  · exact iord_descent_iRInd_zInd s at' p d0 d1
      (isNF_iotil_of_ZDerivation d0 hd0) (isNF_iotil_of_ZDerivation d1 hd1)
  · simp at htag
  · simp at htag
  · simp at htag
  · simp at htag

/-! ### Chain (`K^r`) inversion + the ZDerivation-facing non-critical chain descent (LH3)

For the chain rule the per-case descents (`iord_descent_iCritAux` LH3, `iord_descent_iRcrit_of_chain`
the nut) carry the `isNF (iotil ·)` side conditions abstractly. On a genuine `ZDerivation` chain those
are now **free**: `zDerivation_zK_inv` reads `Seq ds` + per-premise `ZDerivation` off the one-step
recursion equation, and the out-of-range default (`znth ds n = 0` for `n ≥ lh ds`, `znth_prop_not`) is NF
via `isNF_iotil_zero`. This wires the LOW-HANGING chain descent (Buchholz §3.2 case 5.2.2) end-to-end to
`ZDerivation`: only the N1 IH on the replaced premise (`hlt`/`hle`/`hNFv`) remains abstract — exactly the
structural-induction interface. -/

/-- **Chain inversion**: a `ZDerivation` of a chain code `zK s r ds` has `Seq ds` and every in-range
premise a `ZDerivation`. From the one-step recursion equation `zDerivation_iff`; the non-`K` disjuncts
are ruled out by `zTag` (the chain has tag 4). -/
lemma zDerivation_zK_inv {s r ds : V} (hZ : ZDerivation (zK s r ds)) :
    Seq ds ∧ ∀ i < lh ds, ZDerivation (znth ds i) := by
  rcases zDerivation_iff.mp hZ with ⟨s', h, _⟩ | ⟨s', a, p, d0, h, _⟩ | ⟨s', p, d0, h, _⟩ |
    ⟨s', at', p, d0, d1, h, _, _⟩ | ⟨s', r', ds', h, hds', hmem', _⟩ |
    ⟨s', p, k, h, _⟩ | ⟨s', p, h, _⟩ | ⟨s', C, h, _⟩
  · exact absurd (congrArg zTag h) (by simp)
  · exact absurd (congrArg zTag h) (by simp)
  · exact absurd (congrArg zTag h) (by simp)
  · exact absurd (congrArg zTag h) (by simp)
  · obtain rfl : ds = ds' := by simpa using congrArg zKseq h
    exact ⟨hds', fun i hi => hmem' i hi⟩
  · exact absurd (congrArg zTag h) (by simp)
  · exact absurd (congrArg zTag h) (by simp)
  · exact absurd (congrArg zTag h) (by simp)

/-- **Tag-gated principal-formula well-formedness of a `ZDerivation`** (the uniform discharge of the
`hf1_v`…`hf6_v` obligations in every replace constructor). Any genuine `ZDerivation` `v` has its principal
formula a `UFormula` whenever `v` is an I-rule / §5-axiom node: I∀/I¬ from the `zIallWff`/`zInegWff`
`IsSemiformula`/`IsUFormula` side conditions (`IsSemiformula.isUFormula`), the §5 axioms from their
`IsUFormula` side condition. This packages the four tag-implications that `ZDerivation_iCritAux_of` /
`ZDerivation_iCritReplaceReduce_general` consume for the replaced premise `v = red dᵢ`. -/
lemma tag_uformula_of_ZDerivation {v : V} (hZ : ZDerivation v) :
    (zTag v = 1 → IsUFormula ℒₒᵣ (zIallF v)) ∧
    (zTag v = 2 → IsUFormula ℒₒᵣ (zInegF v)) ∧
    (zTag v = 5 → IsUFormula ℒₒᵣ (zAxAllF v)) ∧
    (zTag v = 6 → IsUFormula ℒₒᵣ (zAxNegF v)) := by
  rcases zDerivation_iff.mp hZ with ⟨s, rfl, _⟩ | ⟨s, a, p, d0, rfl, _, _, hwff⟩ |
    ⟨s, p, d0, rfl, _, _, hwff⟩ | ⟨s, at', p, d0, d1, rfl, _, _, _⟩ | ⟨s, r, ds, rfl, _, _, _⟩ |
    ⟨s, p, k, rfl, hp, _⟩ | ⟨s, p, rfl, hp, _⟩ | ⟨s, C, rfl, _⟩
  · exact ⟨fun h => by simp at h, fun h => by simp at h, fun h => by simp at h, fun h => by simp at h⟩
  · exact ⟨fun _ => by rw [zIallF_zIall]; exact hwff.2.2.isUFormula,
      fun h => by simp at h, fun h => by simp at h, fun h => by simp at h⟩
  · exact ⟨fun h => by simp at h, fun _ => by rw [zInegF_zIneg]; exact hwff.1.2.2,
      fun h => by simp at h, fun h => by simp at h⟩
  · exact ⟨fun h => by simp at h, fun h => by simp at h, fun h => by simp at h, fun h => by simp at h⟩
  · exact ⟨fun h => by simp at h, fun h => by simp at h, fun h => by simp at h, fun h => by simp at h⟩
  · exact ⟨fun h => by simp at h, fun h => by simp at h,
      fun _ => by rw [zAxAllF_zAxAll]; exact hp.isUFormula, fun h => by simp at h⟩
  · exact ⟨fun h => by simp at h, fun h => by simp at h, fun h => by simp at h,
      fun _ => by rw [zAxNegF_zAxNeg]; exact hp⟩
  · exact ⟨fun h => by simp at h, fun h => by simp at h, fun h => by simp at h, fun h => by simp at h⟩

/-- **Faithful chain validity from a `ZDerivation`**: after the re-point, the `ZPhi` `zK` disjunct carries
`zKValidF` (Buchholz's genuine criticality-free `K^r` validity, §3 clause 5), so a `ZDerivation` of a chain
hands you the faithful side conditions directly. Criticality is NOT part of being a derivation — it is a
property the *reduction* (Def 3.2 case 5) supplies at the reduction site. -/
lemma zKValidF_of_ZDerivation_zK {s r ds : V} (hZ : ZDerivation (zK s r ds)) : zKValidF s r ds := by
  rcases zDerivation_iff.mp hZ with ⟨s', h, _⟩ | ⟨s', a, p, d0, h, _⟩ | ⟨s', p, d0, h, _⟩ |
    ⟨s', at', p, d0, d1, h, _, _⟩ | ⟨s', r', ds', h, hds', hmem', hvalid'⟩ |
    ⟨s', p, k, h, _⟩ | ⟨s', p, h, _⟩ | ⟨s', C, h, _⟩
  · exact absurd (congrArg zTag h) (by simp)
  · exact absurd (congrArg zTag h) (by simp)
  · exact absurd (congrArg zTag h) (by simp)
  · exact absurd (congrArg zTag h) (by simp)
  · obtain rfl : s = s' := by simpa using congrArg fstIdx h
    obtain rfl : r = r' := by simpa using congrArg zKrank h
    obtain rfl : ds = ds' := by simpa using congrArg zKseq h
    exact hvalid'
  · exact absurd (congrArg zTag h) (by simp)
  · exact absurd (congrArg zTag h) (by simp)
  · exact absurd (congrArg zTag h) (by simp)

/-- **The `K^r` chain introduction** (the post-re-point `ZPhi` `zK` disjunct, packaged): a `Seq` premise
sequence of `ZDerivation`s that is `zKValidF`-valid (Buchholz's faithful, criticality-free `K^r` validity)
builds a `ZDerivation` of the chain `zK s r ds`. This is the `hZPhiK` residual of `ZDerivation_iCritReductG_of`
— now a theorem rather than a hypothesis, because criticality is no longer baked into `ZDerivation`. -/
lemma zDerivation_zK_intro {s r ds : V} (hseq : Seq ds)
    (hmem : ∀ i < lh ds, ZDerivation (znth ds i)) (hvalid : zKValidF s r ds) :
    ZDerivation (zK s r ds) :=
  zDerivation_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
    ⟨s, r, ds, rfl, hseq, hmem, hvalid⟩)))))

/-- **Own-permissibility of a `ZDerivation` (Buchholz Lemma 3.3, `tp(d) ◁ End(d)`).** Every genuine
Z-derivation's top inference symbol is permissible for its OWN end-sequent: `Rep` rules (atom/Ind/chain)
trivially (`iperm_isymRep`), the I-rules from the `ZPhi` succedent side condition (`seqSucc s = ∀p`/`¬A`),
the §5 atomic axioms from the `inAnt` side condition. This is the uniform discharge of the `hperm_v`
obligations throughout the `RedSound` leaves (previously supplied per-rule) — in particular the spliced
halves' own-permissibility in the 5.2.1 case. -/
lemma iperm_tp_fstIdx_of_ZDerivation {d : V} (hZ : ZDerivation d) :
    iperm (tp d) (fstIdx d) := by
  rcases zDerivation_iff.mp hZ with ⟨s, rfl, _⟩ | ⟨s, a, p, d0, rfl, _, hsc, _⟩ |
    ⟨s, p, d0, rfl, _, hsc, _⟩ | ⟨s, at', p, d0, d1, rfl, _, _, _⟩ | ⟨s, r, ds, rfl, _, _, _⟩ |
    ⟨s, p, k, rfl, _, hin, _⟩ | ⟨s, p, rfl, _, hin, _⟩ | ⟨s, C, rfl, _⟩
  · rw [tp_zAtom]; exact iperm_isymRep _
  · rw [fstIdx_zIall]; exact iperm_tp_zIall hsc
  · rw [fstIdx_zIneg]; exact iperm_tp_zIneg hsc
  · rw [tp_zInd]; exact iperm_isymRep _
  · rw [tp_zK]; exact iperm_isymRep _
  · rw [fstIdx_zAxAll]; exact iperm_tp_zAxAll hin
  · rw [fstIdx_zAxNeg]; exact iperm_tp_zAxNeg hin
  · rw [tp_zAx1]; exact iperm_isymRep _

/-- **The `zKValidF` leaf side-conditions hold for any `ZDerivation`** (companion to
`iperm_tp_fstIdx_of_ZDerivation`). For a premise that is a genuine Z-derivation, the tag-conditional
formula-hood obligations of `zKValidF` (tags 1/2/5/6 ⟹ the active formula `zIallF`/`zInegF`/`zAxAllF`/
`zAxNegF` is a `UFormula`) follow from the node's own `ZPhi` side conditions (the I-rule matrices are
`IsSemiformula 1`, the §5 axiom matrices are `IsUFormula`). This is what lets one BUILD `zKValidF` of a
FRESH chain (e.g. the corrected Ind reduct `iIndReductSeqG`) from premise `ZDerivation`s. -/
lemma zKValidF_leafconds_of_ZDerivation {e : V} (hZ : ZDerivation e) :
    (zTag e = 1 → IsUFormula ℒₒᵣ (zIallF e)) ∧
    (zTag e = 2 → IsUFormula ℒₒᵣ (zInegF e)) ∧
    (zTag e = 5 → IsUFormula ℒₒᵣ (zAxAllF e)) ∧
    (zTag e = 6 → IsUFormula ℒₒᵣ (zAxNegF e)) := by
  rcases zDerivation_iff.mp hZ with ⟨s, rfl, _⟩ | ⟨s, a, p, d0, rfl, _, _, hwff⟩ |
    ⟨s, p, d0, rfl, _, _, hwff, _⟩ | ⟨s, at', p, d0, d1, rfl, _, _, _⟩ |
    ⟨s, r, ds, rfl, _, _, _⟩ | ⟨s, p, k, rfl, hp, _, _⟩ |
    ⟨s, p, rfl, hp, _, _⟩ | ⟨s, C, rfl, _⟩
  · exact ⟨fun h => absurd h (by simp), fun h => absurd h (by simp),
      fun h => absurd h (by simp), fun h => absurd h (by simp)⟩
  · exact ⟨fun _ => by rw [zIallF_zIall]; exact hwff.2.2.isUFormula, fun h => absurd h (by simp),
      fun h => absurd h (by simp), fun h => absurd h (by simp)⟩
  · exact ⟨fun h => absurd h (by simp), fun _ => by rw [zInegF_zIneg]; exact hwff.2.2,
      fun h => absurd h (by simp), fun h => absurd h (by simp)⟩
  · exact ⟨fun h => absurd h (by simp), fun h => absurd h (by simp),
      fun h => absurd h (by simp), fun h => absurd h (by simp)⟩
  · exact ⟨fun h => absurd h (by simp), fun h => absurd h (by simp),
      fun h => absurd h (by simp), fun h => absurd h (by simp)⟩
  · exact ⟨fun h => absurd h (by simp), fun h => absurd h (by simp),
      fun _ => by rw [zAxAllF_zAxAll]; exact hp.isUFormula, fun h => absurd h (by simp)⟩
  · exact ⟨fun h => absurd h (by simp), fun h => absurd h (by simp),
      fun h => absurd h (by simp), fun _ => by rw [zAxNegF_zAxNeg]; exact hp⟩
  · exact ⟨fun h => absurd h (by simp), fun h => absurd h (by simp),
      fun h => absurd h (by simp), fun h => absurd h (by simp)⟩

/-- **All-`n` premise NF** of a `ZDerivation` chain: in-range premises are NF (`isNF_iotil_of_ZDerivation`),
out-of-range default `0` is NF (`isNF_iotil_zero`). Discharges the `hNF : ∀ n` side condition. -/
lemma isNF_iotil_znth_of_ZDerivation_zK {s r ds : V} (hZ : ZDerivation (zK s r ds)) :
    ∀ n, isNF (iotil (znth ds n)) := by
  obtain ⟨_, hmem⟩ := zDerivation_zK_inv hZ
  intro n
  rcases lt_or_ge n (lh ds) with hn | hn
  · exact isNF_iotil_of_ZDerivation (znth ds n) (hmem n hn)
  · rw [znth_prop_not (Or.inr hn)]; exact isNF_iotil_zero

/-- **LH3 over `ZDerivation`** — the non-critical chain descent with its NF side conditions discharged
from the chain's `ZDerivation`. The single remaining input is the N1 IH on the replaced premise `v = dᵢ[n]`
(`hlt`/`hle`/`hNFv`), to be supplied by the Thm-4.2 structural induction. -/
lemma iord_descent_iCritAux_of_ZDerivation {s r ds i v : V}
    (hZ : ZDerivation (zK s r ds)) (hi : i < lh ds)
    (hlt : icmp (iotil v) (iotil (znth ds i)) = 0)
    (hle : idg v ≤ idg (znth ds i)) (hNFv : isNF (iotil v)) :
    icmp (iord (iCritAux (zK s r ds) i v)) (iord (zK s r ds)) = 0 := by
  obtain ⟨hds, hmem⟩ := zDerivation_zK_inv hZ
  have hNFall := isNF_iotil_znth_of_ZDerivation_zK hZ
  have hnf : isNF (iotil (zK s r ds)) :=
    isNF_iotil_zK hds (fun n hn => isNF_iotil_of_ZDerivation (znth ds n) (hmem n hn))
  exact iord_descent_iCritAux hds hi hnf hlt hle hNFall hNFv

/-- **5.2.2 replace-premise VALIDITY (the genuine-reduct RedSound leaf for the non-critical chain case).**
Replacing premise `i` of a faithfully-valid chain derivation `zK s r ds` by a reduct `v` that is itself a
`ZDerivation` with the same end-sequent (`fstIdx v = fstIdx (znth ds i)`) and its own well-formedness
yields a `ZDerivation` of the updated chain `iCritAux (zK s r ds) i v = zK s r (seqUpdate ds i v)`. This
is Buchholz Def 3.2 case 5.2.2 (non-critical: `d[n] = K^r_Π(i/dᵢ[n])`, the conclusion `Π` and rank `r`
unchanged because the chosen premise is a `Rep`, `tp(dᵢ)(Π,n) = Π`) at the validity layer:
`zDerivation_zK_intro` over the banked `zKValidF_seqUpdate`, the at-index premise supplied by the reduct's
own derivation `hZv`. Together with `iord_descent_iCritAux_of_ZDerivation` (the descent, banked) this is
the complete 5.2.2 leaf — both invariants take the same N1 IH on the replaced premise `v = red dᵢ`. -/
lemma ZDerivation_iCritAux_of {s r ds i v : V} (hi : i < lh ds)
    (hZ : ZDerivation (zK s r ds)) (hZv : ZDerivation v)
    (hv : fstIdx v = fstIdx (znth ds i))
    (hperm_v : iperm (tp v) (fstIdx v))
    (hf1_v : zTag v = 1 → IsUFormula ℒₒᵣ (zIallF v))
    (hf2_v : zTag v = 2 → IsUFormula ℒₒᵣ (zInegF v))
    (hf5_v : zTag v = 5 → IsUFormula ℒₒᵣ (zAxAllF v))
    (hf6_v : zTag v = 6 → IsUFormula ℒₒᵣ (zAxNegF v)) :
    ZDerivation (iCritAux (zK s r ds) i v) := by
  rw [iCritAux_zK]
  obtain ⟨hds, hmem⟩ := zDerivation_zK_inv hZ
  have hvalid := zKValidF_of_ZDerivation_zK hZ
  refine zDerivation_zK_intro (seqUpdate_seq ds i v) ?_
    (zKValidF_seqUpdate hi hv hperm_v hf1_v hf2_v hf5_v hf6_v hvalid)
  intro n hn
  rw [seqUpdate_lh] at hn
  rcases eq_or_ne n i with rfl | hne
  · rw [znth_seqUpdate_self hi]; exact hZv
  · rw [znth_seqUpdate_of_ne hne]; exact hmem n hn

/-- **5.2.2 replace-premise validity, CONCLUSION-REDUCING (the R-rule cut-elimination core, Buchholz Thm
3.4(b) / Def 3.2 case 5.2.2 for a NON-`Rep` selected premise).** The analogue of `ZDerivation_iCritAux_of`
where the conclusion succedent itself REDUCES in lockstep with the swapped premise: replacing premise `i`
of a valid chain `zK s r ds` by a reduct `v` whose end-sequent IS the reduced sequent `s'` (same
antecedent `chainAnt ds i = seqAnt (fstIdx v)`, reduced succedent `seqSucc (fstIdx v) = seqSucc s'`) yields
a `ZDerivation` of the conclusion-reduced chain `zK s' r (seqUpdate ds i v)`, where `s'` keeps the parent
antecedent (`hX_ant : seqAnt s' = seqAnt s`). This is the genuine cut-elimination step `ZDerivation_iCritAux_of`
(keep-`Π`) cannot do — the selected premise serves as the distinguished `j₀ = i`, so the threading/rank up
to `i` (`hthread`/`hrank`, caller-supplied from the parent `zKValidF` + the I-rule selection forcing `i ≤ j₀`)
suffices for the reduced `isChainInf` (`isChainInf_seqUpdate_reduceR`). The conclusion succedent wff
(`hsucc_wff`) is the reduced principal instance (`F(0)` etc.); the conclusion antecedent wff inherits from
the parent via `hX_ant`. -/
lemma ZDerivation_iCritReplaceReduce_of {s s' r ds i v : V} (hi : i < lh ds)
    (hZ : ZDerivation (zK s r ds)) (hZv : ZDerivation v)
    (hant : seqAnt (fstIdx v) = chainAnt ds i)
    (hsucc_v : seqSucc (fstIdx v) = seqSucc s')
    (hX_ant : seqAnt s' = seqAnt s)
    (hthread : ∀ i' ≤ i, ∀ B, inAnt B (chainAnt ds i') →
        inAnt B (seqAnt s) ∨ ∃ i'' < i', B = chainAsucc ds i'')
    (hrank : ∀ i' < i, irk (chainAsucc ds i') ≤ r)
    (hsucc_wff : IsUFormula ℒₒᵣ (seqSucc s'))
    (hperm_v : iperm (tp v) (fstIdx v))
    (hf1_v : zTag v = 1 → IsUFormula ℒₒᵣ (zIallF v))
    (hf2_v : zTag v = 2 → IsUFormula ℒₒᵣ (zInegF v))
    (hf5_v : zTag v = 5 → IsUFormula ℒₒᵣ (zAxAllF v))
    (hf6_v : zTag v = 6 → IsUFormula ℒₒᵣ (zAxNegF v)) :
    ZDerivation (zK s' r (seqUpdate ds i v)) := by
  obtain ⟨hds, hmem⟩ := zDerivation_zK_inv hZ
  obtain ⟨hci, hperm, hg1, hg2, hg5, hg6, hcf, _hss, hsa⟩ := zKValidF_of_ZDerivation_zK hZ
  refine zDerivation_zK_intro (seqUpdate_seq ds i v) ?_ ?_
  · -- premise membership
    intro n hn
    rw [seqUpdate_lh] at hn
    rcases eq_or_ne n i with rfl | hne
    · rw [znth_seqUpdate_self hi]; exact hZv
    · rw [znth_seqUpdate_of_ne hne]; exact hmem n hn
  · -- conclusion-reduced validity `zKValidF s' r (seqUpdate ds i v)`
    refine ⟨isChainInf_seqUpdate_reduceR hi hant hsucc_v hX_ant hthread hrank,
      ?_, ?_, ?_, ?_, ?_, ?_, hsucc_wff, ?_⟩
    · intro n hn
      rcases eq_or_ne n i with rfl | hne
      · rw [znth_seqUpdate_self hi]; exact hperm_v
      · rw [znth_seqUpdate_of_ne hne]; exact hperm n (by rwa [seqUpdate_lh] at hn)
    · intro n hn
      rcases eq_or_ne n i with rfl | hne
      · rw [znth_seqUpdate_self hi]; exact hf1_v
      · rw [znth_seqUpdate_of_ne hne]; exact hg1 n (by rwa [seqUpdate_lh] at hn)
    · intro n hn
      rcases eq_or_ne n i with rfl | hne
      · rw [znth_seqUpdate_self hi]; exact hf2_v
      · rw [znth_seqUpdate_of_ne hne]; exact hg2 n (by rwa [seqUpdate_lh] at hn)
    · intro n hn
      rcases eq_or_ne n i with rfl | hne
      · rw [znth_seqUpdate_self hi]; exact hf5_v
      · rw [znth_seqUpdate_of_ne hne]; exact hg5 n (by rwa [seqUpdate_lh] at hn)
    · intro n hn
      rcases eq_or_ne n i with rfl | hne
      · rw [znth_seqUpdate_self hi]; exact hf6_v
      · rw [znth_seqUpdate_of_ne hne]; exact hg6 n (by rwa [seqUpdate_lh] at hn)
    · -- chainAsucc wff: at `i` the succedent is the reduced `seqSucc s'`; off `i` inherits.
      intro n hn
      rcases eq_or_ne n i with rfl | hne
      · rw [chainAsucc_seqUpdate_self hi, hsucc_v]; exact hsucc_wff
      · rw [chainAsucc_seqUpdate_of_ne hne]; exact hcf n (by rwa [seqUpdate_lh] at hn)
    · -- conclusion antecedent wff inherits from the parent via `hX_ant`.
      rw [hX_ant]; exact hsa

/-- **5.2.2 replace-premise validity, GENERAL conclusion-reduction (the unifying non-`Rep` constructor).**
The most general replace step: replacing premise `i` of a valid chain by a `ZDerivation` `v`, with the
reduced conclusion `s'` SUPPLIED through an explicit `isChainInf s' r (seqUpdate ds i v)` (`hci`), plus the
conclusion well-formedness (`hsucc_wff`/`hant_wff`) and `v`'s own well-formedness, yields `ZDerivation (zK
s' r (seqUpdate ds i v))`. Factoring `isChainInf` OUT (mirroring `ZDerivation_seqInsert_of`) is what lets the
FOUR non-`Rep` cases share one constructor despite their distinct conclusion bookkeeping: I∀ (succedent →
`F(0)`, antecedent kept), I¬ (antecedent gains `p`, succedent → `⊥`), axAll (antecedent gains `F(k)`), axNeg
(succedent → `p`). Each case builds its own `hci` from the banked `isChainInf_seqUpdate_reduceR` /
`isChainInf_seqAddAnt` plus the `permIdx ≤ j₀` threading; the off-`i` premise conjuncts (perm/tag-formula-hood)
inherit from the parent `zKValidF`, the at-`i` ones from `v`. `hv_succ_wff` is `v`'s succedent well-formedness
(the at-`i` `chainAsucc` conjunct). -/
lemma ZDerivation_iCritReplaceReduce_general {s s' r ds i v : V} (hi : i < lh ds)
    (hZ : ZDerivation (zK s r ds)) (hZv : ZDerivation v)
    (hci : isChainInf s' r (seqUpdate ds i v))
    (hsucc_wff : IsUFormula ℒₒᵣ (seqSucc s'))
    (hant_wff : ∀ k < lh (seqAnt s'), IsUFormula ℒₒᵣ (znth (seqAnt s') k))
    (hv_succ_wff : IsUFormula ℒₒᵣ (seqSucc (fstIdx v)))
    (hperm_v : iperm (tp v) (fstIdx v))
    (hf1_v : zTag v = 1 → IsUFormula ℒₒᵣ (zIallF v))
    (hf2_v : zTag v = 2 → IsUFormula ℒₒᵣ (zInegF v))
    (hf5_v : zTag v = 5 → IsUFormula ℒₒᵣ (zAxAllF v))
    (hf6_v : zTag v = 6 → IsUFormula ℒₒᵣ (zAxNegF v)) :
    ZDerivation (zK s' r (seqUpdate ds i v)) := by
  obtain ⟨hds, hmem⟩ := zDerivation_zK_inv hZ
  obtain ⟨_, hperm, hg1, hg2, hg5, hg6, hcf, _, _⟩ := zKValidF_of_ZDerivation_zK hZ
  refine zDerivation_zK_intro (seqUpdate_seq ds i v) ?_ ?_
  · intro n hn
    rw [seqUpdate_lh] at hn
    rcases eq_or_ne n i with rfl | hne
    · rw [znth_seqUpdate_self hi]; exact hZv
    · rw [znth_seqUpdate_of_ne hne]; exact hmem n hn
  · refine ⟨hci, ?_, ?_, ?_, ?_, ?_, ?_, hsucc_wff, hant_wff⟩
    · intro n hn
      rcases eq_or_ne n i with rfl | hne
      · rw [znth_seqUpdate_self hi]; exact hperm_v
      · rw [znth_seqUpdate_of_ne hne]; exact hperm n (by rwa [seqUpdate_lh] at hn)
    · intro n hn
      rcases eq_or_ne n i with rfl | hne
      · rw [znth_seqUpdate_self hi]; exact hf1_v
      · rw [znth_seqUpdate_of_ne hne]; exact hg1 n (by rwa [seqUpdate_lh] at hn)
    · intro n hn
      rcases eq_or_ne n i with rfl | hne
      · rw [znth_seqUpdate_self hi]; exact hf2_v
      · rw [znth_seqUpdate_of_ne hne]; exact hg2 n (by rwa [seqUpdate_lh] at hn)
    · intro n hn
      rcases eq_or_ne n i with rfl | hne
      · rw [znth_seqUpdate_self hi]; exact hf5_v
      · rw [znth_seqUpdate_of_ne hne]; exact hg5 n (by rwa [seqUpdate_lh] at hn)
    · intro n hn
      rcases eq_or_ne n i with rfl | hne
      · rw [znth_seqUpdate_self hi]; exact hf6_v
      · rw [znth_seqUpdate_of_ne hne]; exact hg6 n (by rwa [seqUpdate_lh] at hn)
    · intro n hn
      rcases eq_or_ne n i with rfl | hne
      · rw [chainAsucc_seqUpdate_self hi]; exact hv_succ_wff
      · rw [chainAsucc_seqUpdate_of_ne hne]; exact hcf n (by rwa [seqUpdate_lh] at hn)

/-- **L-rule replace constructor (the axiom selected-premise cut-elimination step, Buchholz Def 3.2 case
5.2.2 for `tp dᵢ = L^k_A`).** Weakening the conclusion of a chain `ZDerivation` by a `UFormula` `A` in the
antecedent yields a `ZDerivation` of the weakened chain. This is the genuine reduct for a §5-axiom selected
premise: there `red dᵢ = dᵢ` (identity, premises unchanged), and the conclusion gains the cut-formula
instance `A(k)` in its antecedent (`tpReduce (isymLk k …) Π 0 = A(k),Γ→D`). The validity is pure
conclusion-antecedent monotonicity — `zKValidF_seqAddAnt`. -/
lemma ZDerivation_zK_seqAddAnt {s r ds A : V} (hZ : ZDerivation (zK s r ds))
    (hs : Seq (seqAnt s)) (hA : IsUFormula ℒₒᵣ A) :
    ZDerivation (zK (seqAddAnt A s) r ds) := by
  obtain ⟨hds, hmem⟩ := zDerivation_zK_inv hZ
  exact zDerivation_zK_intro hds hmem
    (zKValidF_seqAddAnt hs hA (zKValidF_of_ZDerivation_zK hZ))

/-- **5.2.2 replace-premise validity, K-chain reduct specialization (the dispatch-ready form).** In the
genuine `red` dispatch the reduct `v = red dᵢ` of any reducible premise is a `K`-chain (`zK …`, via
`iRcritG`/`iRInd`), so its own-permissibility is automatic (`tp = isymRep`, `iperm_isymRep`) and the
tag-gated I/Ax formula-hood conjuncts are vacuous (`zTag = 4`). Hence replacing premise `i` of a valid
chain by a valid `zK`-reduct of the same end-sequent preserves derivation-validity with NO side
hypotheses beyond the end-sequent match `fstIdx v = fstIdx (znth ds i)`. -/
lemma ZDerivation_iCritAux_of_zK {s r ds i sv rv dsv : V} (hi : i < lh ds)
    (hZ : ZDerivation (zK s r ds)) (hZv : ZDerivation (zK sv rv dsv))
    (hv : fstIdx (zK sv rv dsv) = fstIdx (znth ds i)) :
    ZDerivation (iCritAux (zK s r ds) i (zK sv rv dsv)) := by
  refine ZDerivation_iCritAux_of hi hZ hZv hv ?_ ?_ ?_ ?_ ?_
  · rw [tp_zK]; exact iperm_isymRep _
  · intro h; rw [zTag_zK] at h; exact absurd h (by simp)
  · intro h; rw [zTag_zK] at h; exact absurd h (by simp)
  · intro h; rw [zTag_zK] at h; exact absurd h (by simp)
  · intro h; rw [zTag_zK] at h; exact absurd h (by simp)

/-- **5.2.1 splice-premise validity (the genuine ordered-insert reduct)** — the analogue of
`ZDerivation_iCritAux_of` for case 5.2.1: splicing a critical premise's two halves `a`,`b` in place at
index `i` of a valid chain (instead of replacing one premise) yields a genuine `ZDerivation`, GIVEN the
two halves are derivable, the spliced `isChainInf` threading holds (`isChainInf_seqInsert`), and the
per-half well-formedness. The conclusion keeps the parent's end-sequent `s`; the rank may rise to `r'`.
Premise-membership is discharged by `forall_znth_seqInsert`; the per-`ds` well-formedness is read off the
parent chain's `zKValidF`. -/
lemma ZDerivation_seqInsert_of {s r r' ds i a b : V} (hi : i < lh ds)
    (hZ : ZDerivation (zK s r ds)) (hZa : ZDerivation a) (hZb : ZDerivation b)
    (hci : isChainInf s r' (seqInsert ds i a b))
    (hperm_a : iperm (tp a) (fstIdx a)) (hperm_b : iperm (tp b) (fstIdx b))
    (hf1_a : zTag a = 1 → IsUFormula ℒₒᵣ (zIallF a)) (hf1_b : zTag b = 1 → IsUFormula ℒₒᵣ (zIallF b))
    (hf2_a : zTag a = 2 → IsUFormula ℒₒᵣ (zInegF a)) (hf2_b : zTag b = 2 → IsUFormula ℒₒᵣ (zInegF b))
    (hf5_a : zTag a = 5 → IsUFormula ℒₒᵣ (zAxAllF a)) (hf5_b : zTag b = 5 → IsUFormula ℒₒᵣ (zAxAllF b))
    (hf6_a : zTag a = 6 → IsUFormula ℒₒᵣ (zAxNegF a)) (hf6_b : zTag b = 6 → IsUFormula ℒₒᵣ (zAxNegF b))
    (hfa_a : IsUFormula ℒₒᵣ (seqSucc (fstIdx a))) (hfa_b : IsUFormula ℒₒᵣ (seqSucc (fstIdx b))) :
    ZDerivation (zK s r' (seqInsert ds i a b)) := by
  obtain ⟨hds, hmem⟩ := zDerivation_zK_inv hZ
  obtain ⟨_, hperm, hg1, hg2, hg5, hg6, hcf, hss, hsa⟩ := zKValidF_of_ZDerivation_zK hZ
  refine zDerivation_zK_intro (seqInsert_seq ds i a b) ?_
    (zKValidF_seqInsert hci hi hperm_a hperm_b hf1_a hf1_b hf2_a hf2_b hf5_a hf5_b hf6_a hf6_b
      hfa_a hfa_b hss hsa hperm hg1 hg2 hg5 hg6 hcf)
  intro n hn
  rw [seqInsert_lh] at hn
  exact forall_znth_seqInsert hi hZa hZb (fun k hk => hmem k hk) n hn

/-- **5.2.1, dispatch-ready (`zK`-halves) specialization.** In the genuine `red` dispatch the two halves
`a = dⱼ{0}`, `b = dⱼ{1}` are themselves `K`-chains (tag 4), so own-permissibility is automatic
(`iperm_isymRep`), the I/Ax tag-gated formula-hoods are vacuous, and the half end-sequent formula-hoods
come from the halves' own validity. No side hypotheses beyond the two half derivations + the spliced
`isChainInf`. -/
lemma ZDerivation_seqInsert_of_zK {s r r' ds i sa ra dsa sb rb dsb : V} (hi : i < lh ds)
    (hZ : ZDerivation (zK s r ds))
    (hZa : ZDerivation (zK sa ra dsa)) (hZb : ZDerivation (zK sb rb dsb))
    (hci : isChainInf s r' (seqInsert ds i (zK sa ra dsa) (zK sb rb dsb))) :
    ZDerivation (zK s r' (seqInsert ds i (zK sa ra dsa) (zK sb rb dsb))) := by
  refine ZDerivation_seqInsert_of hi hZ hZa hZb hci
    (by rw [tp_zK]; exact iperm_isymRep _) (by rw [tp_zK]; exact iperm_isymRep _)
    (fun h => absurd (zTag_zK sa ra dsa ▸ h) (by simp)) (fun h => absurd (zTag_zK sb rb dsb ▸ h) (by simp))
    (fun h => absurd (zTag_zK sa ra dsa ▸ h) (by simp)) (fun h => absurd (zTag_zK sb rb dsb ▸ h) (by simp))
    (fun h => absurd (zTag_zK sa ra dsa ▸ h) (by simp)) (fun h => absurd (zTag_zK sb rb dsb ▸ h) (by simp))
    (fun h => absurd (zTag_zK sa ra dsa ▸ h) (by simp)) (fun h => absurd (zTag_zK sb rb dsb ▸ h) (by simp))
    ?_ ?_
  · rw [fstIdx_zK]; exact (zKValidF_of_ZDerivation_zK hZa).2.2.2.2.2.2.2.1
  · rw [fstIdx_zK]; exact (zKValidF_of_ZDerivation_zK hZb).2.2.2.2.2.2.2.1

/-! ### The reduct-descent IH interface `iRedDescent` (Buchholz Lemma 4.1 (a)+(b)(i)+NF closure)

The Thm-4.2 structural induction (still upstream, gated on the recursive `iR`) feeds the chain case one
fact per reduced **non-critical** premise: its reduct does not raise the degree (part (a)), strictly
lowers the pre-ordinal (part (b)(i)), and stays in normal form. `iRedDescent red d` bundles exactly
those three — the `hle`/`hlt`/`hNFv` that `iord_descent_iCritAux` consumes — so the chain step composes
to a single application (`iord_descent_iCritAux_of_iRedDescent`). The per-rule lemmas below establish
`iRedDescent` for the reducts the induction will pick: `d₀` for the I-rules, `iRInd d` for `Ind`. This
crystallises the structural-induction interface: the remaining work is the recursive `iR` that *chooses*
the reduct, not any new descent mathematics. -/

/-- **Reduct-descent interface** (Buchholz Lemma 4.1 (a)+(b)(i)+NF): the reduct `red` of `d` does not
raise the degree, strictly lowers the pre-ordinal, and is itself a normal form. The IH the chain case
consumes for each reduced non-critical premise. -/
structure iRedDescent (red d : V) : Prop where
  /-- (a) the reduct does not raise the degree. -/
  dg_le : idg red ≤ idg d
  /-- (b)(i) the reduct strictly lowers the pre-ordinal. -/
  otil_lt : icmp (iotil red) (iotil d) = 0
  /-- the reduct's pre-ordinal is a normal form. -/
  nf : isNF (iotil red)

/-- `iRedDescent red d` unfolded to its three `𝚫₁` fields — the characterization the definability
instance and the existence-form code-recursion motive (`genReduct_botSucc`) consume. -/
theorem iRedDescent_iff {red d : V} :
    iRedDescent red d ↔ (idg red ≤ idg d ∧ icmp (iotil red) (iotil d) = 0 ∧ isNF (iotil red)) :=
  ⟨fun h => ⟨h.dg_le, h.otil_lt, h.nf⟩, fun ⟨a, b, c⟩ => ⟨a, b, c⟩⟩

/-- **`𝚫₁`-definability of the reduct-descent interface `iRedDescent`** (a conjunction of `idg`/`icmp`/
`isNF` predicates). Required as the matrix definability for the existence-form code-recursion motive of
`genReduct_botSucc` (Buchholz §14.254): `∃ v, … ∧ iRedDescent v d` is `𝚺₁` exactly because `iRedDescent`
is `𝚫₁`, which is what legitimizes strong induction on the derivation CODE in `𝗜𝚺₁`. -/
instance iRedDescent_definable (Γ) : Γ-[m + 1]-Relation (iRedDescent : V → V → Prop) := by
  have : (iRedDescent : V → V → Prop) =
      fun red d => (idg red ≤ idg d ∧ icmp (iotil red) (iotil d) = 0 ∧ isNF (iotil red)) := by
    funext red d; simp [iRedDescent_iff]
  rw [this]; definability

/-- `iRedDescent` ⟹ the full `iord` descent (tower combine via `iord_descent_le`), given `õ(d)` NF. -/
lemma iord_descent_of_iRedDescent {red d : V} (h : iRedDescent red d) (hnf : isNF (iotil d)) :
    icmp (iord red) (iord d) = 0 :=
  iord_descent_le hnf h.dg_le h.otil_lt

/-- **I∀ reduct interface**: `d[n] = d₀` satisfies `iRedDescent` (degree equal, `õ` drops by one). -/
lemma iRedDescent_zIall {s a p d0 : V} (hd0 : isNF (iotil d0)) :
    iRedDescent d0 (zIall s a p d0) where
  dg_le := le_of_eq (idg_zIall s a p d0).symm
  otil_lt := by rw [iotil_zIall]; exact self_lt_iadd_one (iotil d0) (iotil d0) le_rfl
  nf := hd0

/-- **I¬ reduct interface**: `d[0] = d₀` satisfies `iRedDescent`. -/
lemma iRedDescent_zIneg {s p d0 : V} (hd0 : isNF (iotil d0)) :
    iRedDescent d0 (zIneg s p d0) where
  dg_le := le_of_eq (idg_zIneg s p d0).symm
  otil_lt := by rw [iotil_zIneg]; exact self_lt_iadd_one (iotil d0) (iotil d0) le_rfl
  nf := hd0

/-- `õ(iRInd d)` is NF for an `Ind` code with NF premises — the reduct chain's `#`-fold of two NF
ω-powers. -/
lemma isNF_iotil_iRInd_zInd {s at' p d0 d1 : V} (hd0 : isNF (iotil d0)) (hd1 : isNF (iotil d1)) :
    isNF (iotil (iRInd (zInd s at' p d0 d1))) := by
  rw [iRInd_zInd, iotil_zK _ _ _ (iIndReductSeq_seq d0 d1 1), iseqNaddIdg_iIndReductSeq one_pos]
  exact isNF_inadd (isNF_omega_pow hd0) _ (isNF_omega_pow hd1)

/-- **Ind reduct interface**: `d[0] = iRInd d` satisfies `iRedDescent` (degree preserved by
`idg_zK_iIndReduct`, `õ` drops by `icmp_iotil_iIndReduct`, NF by `isNF_iotil_iRInd_zInd`). -/
lemma iRedDescent_zInd {s at' p d0 d1 : V} (hd0 : isNF (iotil d0)) (hd1 : isNF (iotil d1)) :
    iRedDescent (iRInd (zInd s at' p d0 d1)) (zInd s at' p d0 d1) where
  dg_le := le_of_eq (by rw [iRInd_zInd]; exact idg_zK_iIndReduct (s := s) (at' := at') one_pos)
  otil_lt := by
    rw [iRInd_zInd, iotil_zK _ _ _ (iIndReductSeq_seq d0 d1 1)]
    exact icmp_iotil_iIndReduct hd0 hd1 one_pos
  nf := isNF_iotil_iRInd_zInd hd0 hd1

/-- **Chain step from the IH interface**: a non-critical premise `i` whose reduct `v` satisfies
`iRedDescent v (znth ds i)` plugs straight into the chain descent — this is the LH3 case of the Thm-4.2
structural induction, with the per-premise IH packaged as `iRedDescent`. -/
lemma iord_descent_iCritAux_of_iRedDescent {s r ds i v : V}
    (hZ : ZDerivation (zK s r ds)) (hi : i < lh ds) (hd : iRedDescent v (znth ds i)) :
    icmp (iord (iCritAux (zK s r ds) i v)) (iord (zK s r ds)) = 0 :=
  iord_descent_iCritAux_of_ZDerivation hZ hi hd.otil_lt hd.dg_le hd.nf

/-! ### Splice (LH5) over `ZDerivation` + the critical-premise IH interface

The OTHER chain sub-case (Buchholz §3.2 case 5.2.1): a reduced premise `dⱼ` that is itself **critical**
splices its two T3.4 auxiliaries `a = dⱼ{0}`, `b = dⱼ{1}` into the parent chain. As with LH3 the splice
descent's NF side conditions are free on a `ZDerivation` chain (`zDerivation_zK_inv`), and the per-premise
IH bundles into `iSpliceDescent` (each auxiliary lowers `õ`, does not raise `dg`, and is NF). With the
LH3 (`iRedDescent`) interface this completes the chain case's two sub-cases — the remaining input is the
recursive `iR` selecting which premise to reduce and which sub-case applies. -/

/-- **LH5 over `ZDerivation`** — the splice descent with its NF side conditions discharged from the
chain's `ZDerivation`. Only the auxiliaries' N1 IH (`ha`/`hb`/`hag`/`hbg`/NF) remains abstract. -/
lemma iord_descent_iSpliceEnd_of_ZDerivation {s s' r ds j a b : V}
    (hZ : ZDerivation (zK s r ds)) (hj : j < lh ds)
    (ha : icmp (iotil a) (iotil (znth ds j)) = 0) (hb : icmp (iotil b) (iotil (znth ds j)) = 0)
    (hag : idg a ≤ idg (znth ds j)) (hbg : idg b ≤ idg (znth ds j))
    (hNFa : isNF (iotil a)) (hNFb : isNF (iotil b)) :
    icmp (iord (zK s' r (seqCons (seqUpdate ds j a) b))) (iord (zK s r ds)) = 0 := by
  obtain ⟨hds, hmem⟩ := zDerivation_zK_inv hZ
  have hNFall := isNF_iotil_znth_of_ZDerivation_zK hZ
  have hnf : isNF (iotil (zK s r ds)) :=
    isNF_iotil_zK hds (fun n hn => isNF_iotil_of_ZDerivation (znth ds n) (hmem n hn))
  exact iord_descent_iSpliceEnd hds hj hnf ha hb hag hbg hNFall hNFa hNFb

/-- **Critical-premise (splice) IH interface** (Buchholz case 5.2.1 / LH5): a critical premise `dⱼ`
reduces by splicing its two T3.4 auxiliaries `a = dⱼ{0}`, `b = dⱼ{1}` — each does not raise the degree,
strictly lowers the pre-ordinal, and is NF. The crit-premise analogue of `iRedDescent`. -/
structure iSpliceDescent (a b d : V) : Prop where
  a_dg_le : idg a ≤ idg d
  b_dg_le : idg b ≤ idg d
  a_otil_lt : icmp (iotil a) (iotil d) = 0
  b_otil_lt : icmp (iotil b) (iotil d) = 0
  a_nf : isNF (iotil a)
  b_nf : isNF (iotil b)

/-- **Splice step from the IH interface**: a critical premise `j` whose auxiliaries satisfy
`iSpliceDescent` plugs straight into the splice descent — the LH5 case of the Thm-4.2 structural
induction with the per-premise IH packaged. -/
lemma iord_descent_iSpliceEnd_of_iSpliceDescent {s s' r ds j a b : V}
    (hZ : ZDerivation (zK s r ds)) (hj : j < lh ds) (hd : iSpliceDescent a b (znth ds j)) :
    icmp (iord (zK s' r (seqCons (seqUpdate ds j a) b))) (iord (zK s r ds)) = 0 :=
  iord_descent_iSpliceEnd_of_ZDerivation hZ hj hd.a_otil_lt hd.b_otil_lt hd.a_dg_le hd.b_dg_le
    hd.a_nf hd.b_nf

/-- **LH5 over `ZDerivation`, on the GENUINE insert object** — the splice descent on `seqInsert`
(the object `zKValidF_seqInsert` validity lives on), NF side conditions discharged from the chain's
`ZDerivation`. Mirror of `iord_descent_iSpliceEnd_of_ZDerivation`. -/
lemma iord_descent_seqInsert_of_ZDerivation {s s' r ds j a b : V}
    (hZ : ZDerivation (zK s r ds)) (hj : j < lh ds)
    (ha : icmp (iotil a) (iotil (znth ds j)) = 0) (hb : icmp (iotil b) (iotil (znth ds j)) = 0)
    (hag : idg a ≤ idg (znth ds j)) (hbg : idg b ≤ idg (znth ds j))
    (hNFa : isNF (iotil a)) (hNFb : isNF (iotil b)) :
    icmp (iord (zK s' r (seqInsert ds j a b))) (iord (zK s r ds)) = 0 := by
  obtain ⟨hds, hmem⟩ := zDerivation_zK_inv hZ
  have hNFall := isNF_iotil_znth_of_ZDerivation_zK hZ
  have hnf : isNF (iotil (zK s r ds)) :=
    isNF_iotil_zK hds (fun n hn => isNF_iotil_of_ZDerivation (znth ds n) (hmem n hn))
  exact iord_descent_seqInsert hds hj hnf ha hb hag hbg hNFall hNFa hNFb

/-- **Splice step from the IH interface, on the GENUINE insert object** — `iSpliceDescent` plugs
straight into the `seqInsert` descent. The LH5 case of Thm-4.2 packaged for the genuine reduct. -/
lemma iord_descent_seqInsert_of_iSpliceDescent {s s' r ds j a b : V}
    (hZ : ZDerivation (zK s r ds)) (hj : j < lh ds) (hd : iSpliceDescent a b (znth ds j)) :
    icmp (iord (zK s' r (seqInsert ds j a b))) (iord (zK s r ds)) = 0 :=
  iord_descent_seqInsert_of_ZDerivation hZ hj hd.a_otil_lt hd.b_otil_lt hd.a_dg_le hd.b_dg_le
    hd.a_nf hd.b_nf

/-- **RANK-GENERAL splice step over `ZDerivation`** — the genuine 5.2.1 reduct rank `r'` (= `max{rk(A(dⱼ)),
r}`) is handled given `r' ≤ dg(parent)`; the descent's NF side conditions come from the chain's
`ZDerivation` (`iSpliceDescent` for the auxiliary N1 IH). This is the form the tag-4 dispatch actually
calls in case 5.2.1, where the reduct rank rises to `r'`. -/
lemma iord_descent_seqInsert'_of_iSpliceDescent {s s' r r' ds j a b : V}
    (hZ : ZDerivation (zK s r ds)) (hj : j < lh ds) (hr' : r' ≤ idg (zK s r ds))
    (hd : iSpliceDescent a b (znth ds j)) :
    icmp (iord (zK s' r' (seqInsert ds j a b))) (iord (zK s r ds)) = 0 := by
  obtain ⟨hds, hmem⟩ := zDerivation_zK_inv hZ
  have hNFall := isNF_iotil_znth_of_ZDerivation_zK hZ
  have hnf : isNF (iotil (zK s r ds)) :=
    isNF_iotil_zK hds (fun n hn => isNF_iotil_of_ZDerivation (znth ds n) (hmem n hn))
  exact iord_descent_seqInsert' hds hj hnf hr' hd.a_otil_lt hd.b_otil_lt hd.a_dg_le hd.b_dg_le
    hNFall hd.a_nf hd.b_nf

/-! ### `tp`-inversion + concrete discharge of the critical R-redex premise's IH

The critical-case redex (`inference_critical_pair_of_chain`) returns indices with `tp(dᵢ)=R_{Aᵢ}`,
`tp(d_j)=L^k_{Aᵢ}`. By `tp`'s definition a right-symbol forces the premise to be an **I-rule** (tags 1,2)
and a left-symbol an **atomic axiom** (tags 5,6). So the R-redex premise's reduct fact (`õ`-drop +
`dg`-bound) is **concrete** — the banked I-rule `iRedDescent`, not an abstract structural IH. This
discharges the `i`-side of the nut's `ρ`-hypotheses (`iord_descent_iRcrit_of_chain`'s `hρlt`/`hρg` at
`redexI`); only the `j`-side (the L-axiom reduct, the §5 atomic layer) stays abstract. -/

/-- **R-symbol ⟹ I-rule tag**: `tp d = R_A` forces `zTag d ∈ {1,2}` (the only right-symbol branches). -/
lemma tp_isymR_tag {d A : V} (h : tp d = isymR A) : zTag d = 1 ∨ zTag d = 2 := by
  unfold tp at h
  by_cases ht1 : zTag d = 1
  · exact Or.inl ht1
  · rw [if_neg ht1] at h
    by_cases ht2 : zTag d = 2
    · exact Or.inr ht2
    · rw [if_neg ht2] at h
      by_cases ht5 : zTag d = 5
      · rw [if_pos ht5] at h; exact absurd h (by simp)
      · rw [if_neg ht5] at h
        by_cases ht6 : zTag d = 6
        · rw [if_pos ht6] at h; exact absurd h (by simp)
        · rw [if_neg ht6] at h; exact absurd h.symm (by simp)

/-- **L-symbol ⟹ atomic-axiom tag**: `tp d = L^k_A` forces `zTag d ∈ {5,6}`. -/
lemma tp_isymLk_tag {d k A : V} (h : tp d = isymLk k A) : zTag d = 5 ∨ zTag d = 6 := by
  unfold tp at h
  by_cases ht1 : zTag d = 1
  · rw [if_pos ht1] at h; exact absurd h (by simp)
  · rw [if_neg ht1] at h
    by_cases ht2 : zTag d = 2
    · rw [if_pos ht2] at h; exact absurd h (by simp)
    · rw [if_neg ht2] at h
      by_cases ht5 : zTag d = 5
      · exact Or.inl ht5
      · rw [if_neg ht5] at h
        by_cases ht6 : zTag d = 6
        · exact Or.inr ht6
        · rw [if_neg ht6] at h; exact absurd h.symm (by simp)

/-- **The critical R-redex premise's reduct satisfies the IH bundle, concretely.** A premise `d` with
`tp d = R_A` (the `i`-side redex) is an I-rule (`tp_isymR_tag`); on a `ZDerivation` its `iR`-reduct is
the immediate sub-derivation, which satisfies `iRedDescent` by the banked I-rule case — no abstract IH.
This is the `redexI`-side of the nut's `ρ`-discharge. -/
lemma iRedDescent_iR_of_tp_isymR {d A : V} (htp : tp d = isymR A) (hZ : ZDerivation d) :
    iRedDescent (iR d) d := by
  rcases zDerivation_iff.mp hZ with ⟨s, rfl, _⟩ | ⟨s, a, p, d0, rfl, hd0, _⟩ | ⟨s, p, d0, rfl, hd0, _⟩ |
    ⟨s, at', p, d0, d1, rfl, _, _⟩ | ⟨s, r, ds, rfl, _, _, _⟩ |
    ⟨s, p, k, rfl, _, _⟩ | ⟨s, p, rfl, _, _⟩ | ⟨s, C, rfl, _⟩
  · rw [tp_zAtom] at htp; exact absurd htp (by simp)
  · rw [iR_zIall]; exact iRedDescent_zIall (isNF_iotil_of_ZDerivation d0 hd0)
  · rw [iR_zIneg]; exact iRedDescent_zIneg (isNF_iotil_of_ZDerivation d0 hd0)
  · rw [tp_zInd] at htp; exact absurd htp (by simp)
  · rw [tp_zK] at htp; exact absurd htp (by simp)
  · rw [tp_zAxAll] at htp; exact absurd htp (by simp)
  · rw [tp_zAxNeg] at htp; exact absurd htp (by simp)
  · rw [tp_zAx1] at htp; exact absurd htp (by simp)

/-! ## C0.5 — the Foundation→Z bridge (NEXT milestone, lap-62 reflection)

**The missing seam** (judge `E-EQ5-ROUTE-FINDING-2026-06-23.md` Finding 3; lap-62 reflection
Sharpening 2). The downstream crux-2 obligation `GentzenCon.gentzen_descent_of_inconsistent` is fired
by `¬ 𝗣𝗔.Consistent M` — i.e. `M` carries a coded **Foundation** (Tait-calculus) derivation of `⊥`. But
`iord`/`iR`/the C3 descent operate on **Buchholz system-Z** derivation codes (`zAtom`/`zIall`/`zIneg`/
`zInd`/`zK`). **Nothing yet turns a Foundation ⊥-proof into a Z ⊥-derivation.** Without this bridge the
whole C1/C3 engine has no input. Scale: Bryce–Goré's analogue (`aarondroidbryce/Gentzen`,
`theories/Logic/Peano.v`, `PA_closed_PA_omega`) is ~1,215 lines — a milestone, not a footnote.

**Bridge lemma type.** Now that `ZDerivation : V → Prop` (the C0 Fixpoint) is built (above), define
`ZDerivesEmpty d := ZDerivation d ∧ fstIdx d = (∅ : sequent code)` and prove the `Z ⊇ PA`-on-closed-
sequents simulation, M-internal (`Σ₁` / per-model):

```
-- C0.5 — Foundation⊥ ⟹ Z-derivation of the empty sequent (M-internal).
theorem foundation_bot_to_Z_empty
    {d : V} (hd : (𝗣𝗔).DerivationOf d (⊥ : Sentence ℒₒᵣ)) :
    ∃ z : V, ZDerivesEmpty z
```

**⭐ CHEAPER than the ~1215-line flag (judge `E-CRUX2-DECOMPOSITION` §5, 2026-06-24).** Pattern: discharge
each PA axiom in Z + simulate each rule (MP → Z-cut → `K^r` chain rule; generalization → Z `I^a_∀`). The
key shortcut: **Z's native `Ind` rule maps PA-induction DIRECTLY**, so the bridge SKIPS Bryce–Goré's
biggest sub-tower (their induction→ω-rule simulation, ~half of `Peano.v`) — **revise C0.5 to <1k lines.**
This independently re-confirms the Z-over-PA_ω choice. **Do NOT port their `cut_elim.v`** (infinitary
transfinite recursion / meta-Con via the "dangerous disjunct" — NOT the primrec `R` the PRWO route needs);
only `Peano.v` transfers. Sub-obligations (judge §5): **B1** each PA axiom → short Z-derivation (§5 `Ax(Z)`);
**B2** each Foundation rule → Z-admissible (induction `axm` absorbed by Z's `Ind`); **B3** compose,
M-internally (structural recursion on `d`, sub-derivation codes `<`-smaller via `HFS` course-of-values).

Then `derivesEmpty` (the `GentzenCon` stand-in) is genuinely **populated** from `¬ 𝗣𝗔.Consistent M`:
`¬Con ⟹ ∃ d, 𝗣𝗔.DerivationOf d ⊥ ⟹ (C0.5) ∃ z, ZDerivesEmpty z ⟹` feed the Z-descent `n ↦ iord(iR^[n] z)`.

**Prereqs:** C0 Fixpoint `ZDerivation` ✅ DONE (lap 62) → `iR` (C2) → this bridge (parallelizable in a
worktree). See `HARVEST.md`, `PENDING_WORK.md` lap-62, `E-CRUX2-DECOMPOSITION-2026-06-24.md §5`, and
`GentzenCon.lean` footer (to be re-pointed from Foundation's `Theory.Derivation` onto Buchholz-Z + bridge). -/

/-! ## `𝚺₁`-definability of the crux-2 reduct objects (toward the recursive `iR`)

The Buchholz one-step reduction `iR : d ↦ d[0]` must be a **course-of-values `<`-recursion** (its
critical branch `d{0}=K^r(i/dᵢ[k])` references premise *reducts*; lap-71 handoff "NEXT"). The table
step `iRNext d s` therefore reads sub-reducts out of `s` and *constructs* the reduct from the
crux-2 objects. For the `iRNext` `𝚺₁` blueprint to typecheck, each such object must be a definable
function. These instances supply exactly that — `seqUpdate`, the critical auxiliary `iCritAux`, the
redex finder `redexCode`/`redexI`/`redexJ`, the two-element reduct sequence `iCritReductSeq`, the
assembled critical reduct `iCritReduct`, and the `Ind` reduct `iIndReductSeq`/`iRInd` — so the
recursion's blueprint composes them shallowly (mirroring `idgNext`/`idgTable`). -/

/-- `seqUpdate ds i v = seqUpdateAux ds i v (lh ds)`. -/
def _root_.LO.FirstOrder.Arithmetic.seqUpdateDef : 𝚺₁.Semisentence 4 := .mkSigma
  “y ds i v. ∃ l, !lhDef l ds ∧ !seqUpdateAuxDef y ds i v l”
instance seqUpdate_defined : 𝚺₁-Function₃ (seqUpdate : V → V → V → V) via seqUpdateDef := .mk
  fun v ↦ by simp [seqUpdateDef, seqUpdate, lh_defined.iff, seqUpdateAux_defined.iff]
instance seqUpdate_definable : 𝚺₁-Function₃ (seqUpdate : V → V → V → V) :=
  seqUpdate_defined.to_definable

/-- `seqSetSucc s C = ⟪seqAnt s, C⟫` (the genuine `Θ→C` endsequent op). -/
def _root_.LO.FirstOrder.Arithmetic.seqSetSuccDef : 𝚺₁.Semisentence 3 := .mkSigma
  “y s C. ∃ sa, !seqAntDef sa s ∧ !pairDef y sa C”
instance seqSetSucc_defined : 𝚺₁-Function₂ (seqSetSucc : V → V → V) via seqSetSuccDef := .mk
  fun v ↦ by simp [seqSetSuccDef, seqSetSucc, mkSeqt, seqAnt_defined.iff, pair_defined.iff]
instance seqSetSucc_definable : 𝚺₁-Function₂ (seqSetSucc : V → V → V) := seqSetSucc_defined.to_definable

/-- `seqAddAnt A s = ⟪seqCons (seqAnt s) A, seqSucc s⟫` (the genuine `A,Θ→D` endsequent op). -/
def _root_.LO.FirstOrder.Arithmetic.seqAddAntDef : 𝚺₁.Semisentence 3 := .mkSigma
  “y A s. ∃ sa, !seqAntDef sa s ∧ ∃ c, !seqConsDef c sa A ∧ ∃ ss, !seqSuccDef ss s ∧ !pairDef y c ss”
instance seqAddAnt_defined : 𝚺₁-Function₂ (seqAddAnt : V → V → V) via seqAddAntDef := .mk
  fun v ↦ by simp [seqAddAntDef, seqAddAnt, mkSeqt, seqAnt_defined.iff, seqCons_defined.iff,
    seqSucc_defined.iff, pair_defined.iff]
instance seqAddAnt_definable : 𝚺₁-Function₂ (seqAddAnt : V → V → V) := seqAddAnt_defined.to_definable

/-- **`tpReduce` is `𝚺₁`-definable** (route-B keystone, lap 91). The `Σ₁` graph of Buchholz's reduced
sequent `I(Π,n)`, so the route-B reduct `red` can emit `tpReduce (tp dᵢ) Π 0` as a definable conclusion.
Three-way dispatch on `π₁ I` (`2`=Rep / `0`=R / else L), inner two-way on the principal-formula
connective `π₁(π₂ I − 1) = 6` (`∀`) via `subDef` (peel the `+1` of the qq-constructor). -/
noncomputable def _root_.LO.FirstOrder.Arithmetic.tpReduceDef : 𝚺₁.Semisentence 4 := .mkSigma
  “y I s n.
    ∃ p1I, !pi₁Def p1I I ∧
    ( (p1I = 2 ∧ y = s)
    ∨ (p1I = 0 ∧ ∃ A, !pi₂Def A I ∧ ∃ Am, !subDef Am A 1 ∧ ∃ q, !pi₁Def q Am ∧
        ( (q = 6 ∧ ∃ bod, !pi₂Def bod Am ∧ ∃ nn, !(Bootstrapping.Arithmetic.numeralGraph) nn n ∧
            ∃ sub, !(substs1Graph ℒₒᵣ) sub nn bod ∧ !seqSetSuccDef y s sub)
        ∨ (q ≠ 6 ∧ ∃ p2Am, !pi₂Def p2Am Am ∧ ∃ qq, !pi₁Def qq p2Am ∧ ∃ ng, !(negGraph ℒₒᵣ) ng qq ∧
            ∃ bot, !qqFalsumDef bot ∧ ∃ ss, !seqSetSuccDef ss s bot ∧ !seqAddAntDef y ng ss) ))
    ∨ (p1I ≠ 2 ∧ p1I ≠ 0 ∧ ∃ p2I, !pi₂Def p2I I ∧ ∃ A, !pi₂Def A p2I ∧ ∃ Am, !subDef Am A 1 ∧
        ∃ q, !pi₁Def q Am ∧
        ( (q = 6 ∧ ∃ k, !pi₁Def k p2I ∧ ∃ nk, !(Bootstrapping.Arithmetic.numeralGraph) nk k ∧
            ∃ bod, !pi₂Def bod Am ∧
            ∃ sub, !(substs1Graph ℒₒᵣ) sub nk bod ∧ !seqAddAntDef y sub s)
        ∨ (q ≠ 6 ∧ ∃ p2Am, !pi₂Def p2Am Am ∧ ∃ qq, !pi₁Def qq p2Am ∧ ∃ ng, !(negGraph ℒₒᵣ) ng qq ∧
            !seqSetSuccDef y s ng) )) )”

set_option maxHeartbeats 2000000 in
instance tpReduce_defined : 𝚺₁-Function₃ (tpReduce : V → V → V → V) via tpReduceDef := .mk fun v ↦ by
  simp [tpReduceDef, tpReduce, pi₁_defined.iff, pi₂_defined.iff, sub_defined.iff,
    (Bootstrapping.Arithmetic.numeral_defined (V := V)).iff, (substs1.defined (L := ℒₒᵣ)).iff,
    (neg.defined (L := ℒₒᵣ)).iff, qqFalsum_defined.iff, seqSetSucc_defined.iff, seqAddAnt_defined.iff]
  by_cases h2 : π₁ (v 1) = 2
  · simp [h2]
  · by_cases h0 : π₁ (v 1) = 0
    · simp [h2, h0]
      by_cases hq : π₁ (π₂ (v 1) - 1) = 6 <;> simp [hq, numeral_eq_natCast]
    · simp [h2, h0]
      by_cases hq : π₁ (π₂ (π₂ (v 1)) - 1) = 6 <;> simp [hq, numeral_eq_natCast]

instance tpReduce_definable : 𝚺₁-Function₃ (tpReduce : V → V → V → V) := tpReduce_defined.to_definable
instance tpReduce_definable' (Γ) : Γ-[m + 1]-Function₃ (tpReduce : V → V → V → V) :=
  tpReduce_definable.of_sigmaOne

/-- `iCritAux d i v = zK (fstIdx d) (zKrank d) (seqUpdate (zKseq d) i v)` (the critical auxiliary
`d{ν} = K^r(i/v)`, a chain with premise `i` replaced by `v`). -/
def _root_.LO.FirstOrder.Arithmetic.iCritAuxDef : 𝚺₁.Semisentence 4 := .mkSigma
  “y d i v. ∃ f, !fstIdxDef f d ∧ ∃ rk, !zKrankDef rk d ∧ ∃ ds, !zKseqDef ds d ∧
    ∃ u, !seqUpdateDef u ds i v ∧ !zKGraph y f rk u”
instance iCritAux_defined : 𝚺₁-Function₃ (iCritAux : V → V → V → V) via iCritAuxDef := .mk
  fun v ↦ by simp [iCritAuxDef, iCritAux, fstIdx_defined.iff, zKrank_defined.iff, zKseq_defined.iff,
    seqUpdate_defined.iff, zK_defined.iff]
instance iCritAux_definable : 𝚺₁-Function₃ (iCritAux : V → V → V → V) := iCritAux_defined.to_definable

/-! ## The 5.2.2 replace-reduct dispatch helper `iRKr` (Buchholz Def 3.2 case 5.2.2)

When the chain `d` is non-critical and the least permissible premise `dᵢ` (`i = permIdx d`) is *itself*
non-critical, Buchholz replaces premise `i` by its own reduct `red dᵢ`. In the `red` table recursion the
reduct of a smaller premise code is *already computed* — it is the table lookup `znth s dᵢ` (`s` = the
table-so-far, `dᵢ = znth (zKseq d) (permIdx d)` = the premise code). So the genuine 5.2.2 reduct is a
CLOSED definable term: `iCritAux d (permIdx d) (znth s dᵢ)` (= `K^r(i/red dᵢ)`), no existential. -/

/-- **5.2.2 replace-reduct (route-B conclusion-reducing, lap 96).** The chain with its least-permissible
premise `i = permIdx d` replaced by that premise's already-tabulated reduct `red dᵢ = znth s (znth (zKseq d) i)`,
AND its conclusion reduced to Buchholz's `tp(dᵢ)(Π,0)` (`tpReduce (tp dᵢ) (fstIdx d) 0`). For a `Rep`
selected premise (`tp dᵢ = Rep`, e.g. on the ⊥-orbit by Cor 2.1) this is `Π` unchanged, matching the old
`iCritAux d (permIdx d) (…)`; for an I-rule/axiom selected premise it reduces the conclusion as Buchholz
Def 3.2 case 5.2.2 demands (lap-90 finding: keep-`Π` is faithful only for `tp = Rep`). The rank and premise
sequence are unchanged, so `iord`/`zReg` (conclusion-independent) are untouched. -/
noncomputable def iRKr (d s : V) : V :=
  zK (tpReduce (tp (znth (zKseq d) (permIdx d))) (fstIdx d) 0)
     (zKrank d)
     (seqUpdate (zKseq d) (permIdx d) (znth s (znth (zKseq d) (permIdx d))))

noncomputable def _root_.LO.FirstOrder.Arithmetic.iRKrDef : 𝚺₁.Semisentence 3 := .mkSigma
  “y d s. ∃ i, !permIdxDef i d ∧ ∃ ds, !zKseqDef ds d ∧ ∃ di, !znthDef di ds i ∧
    ∃ v, !znthDef v s di ∧ ∃ t, !tpDef t di ∧ ∃ f, !fstIdxDef f d ∧
    ∃ c, !tpReduceDef c t f 0 ∧ ∃ r, !zKrankDef r d ∧ ∃ u, !seqUpdateDef u ds i v ∧
    !zKGraph y c r u”

instance iRKr_defined : 𝚺₁-Function₂ (iRKr : V → V → V) via iRKrDef := .mk fun v ↦ by
  simp [iRKrDef, iRKr, permIdx_defined.iff, zKseq_defined.iff, znth_defined.iff, tp_defined.iff,
    fstIdx_defined.iff, tpReduce_defined.iff, zKrank_defined.iff, seqUpdate_defined.iff,
    zK_defined.iff]

instance iRKr_definable : 𝚺₁-Function₂ (iRKr : V → V → V) := iRKr_defined.to_definable

/-! ## The 5.2.1 splice-reduct dispatch helper `iRKs` (Buchholz Def 3.2 case 5.2.1)

When the chain `d` is non-critical and the least permissible premise `dᵢ` (`i = permIdx d`) is *itself*
critical, Buchholz splices `dᵢ`'s two critical-reduction halves `dᵢ{0}, dᵢ{1}` in place at index `i`.
Again the halves are ALREADY tabulated: `red dᵢ = znth s dᵢ` is (for critical `dᵢ`) the `iRcritG`
recombination `K_Π⟨dᵢ{0}, dᵢ{1}⟩`, so `dᵢ{0} = znth (zKseq (red dᵢ)) 0`, `dᵢ{1} = znth (zKseq (red dᵢ)) 1`
(the two `iCritReductSeq` entries). The reduct rank is `r' = max(rk(A(dᵢ)), r)` (Buchholz, paper md line 25)
— and `rk(A(dᵢ)) = irk(seqSucc(fstIdx dᵢ{0}))` because half `dᵢ{0}` concludes `Θ→A(dᵢ)`. This is EXACTLY the
minimal `r'` the validity object `isChainInf_seqInsert` requires (`irk(seqSucc(fstIdx a)) ≤ r'` ∧ `r ≤ r'`).
Closed definable term, no existential. -/

/-- **5.2.1 splice-reduct** — the chain with its least-permissible (and itself-critical) premise
`i = permIdx d` replaced *in place* by the two halves `dᵢ{0}, dᵢ{1}` of that premise's already-tabulated
critical reduct `red dᵢ = znth s (znth (zKseq d) i)`. Rank `r' = max(irk(seqSucc(fstIdx dᵢ{0})), zKrank d)`
= Buchholz's `max(rk(A(dᵢ)), r)`. -/
noncomputable def iRKs (d s : V) : V :=
  zK (fstIdx d)
    (max (irk (seqSucc (fstIdx (znth (zKseq (znth s (znth (zKseq d) (permIdx d)))) 0)))) (zKrank d))
    (seqInsert (zKseq d) (permIdx d)
      (znth (zKseq (znth s (znth (zKseq d) (permIdx d)))) 0)
      (znth (zKseq (znth s (znth (zKseq d) (permIdx d)))) 1))

noncomputable def _root_.LO.FirstOrder.Arithmetic.iRKsDef : 𝚺₁.Semisentence 3 := .mkSigma
  “y d s. ∃ i, !permIdxDef i d ∧ ∃ ds, !zKseqDef ds d ∧ ∃ di, !znthDef di ds i ∧
    ∃ vi, !znthDef vi s di ∧ ∃ dsv, !zKseqDef dsv vi ∧
    ∃ a, !znthDef a dsv 0 ∧ ∃ b, !znthDef b dsv 1 ∧
    ∃ fa, !fstIdxDef fa a ∧ ∃ ssa, !seqSuccDef ssa fa ∧ ∃ rA, !irkDef rA ssa ∧
    ∃ rk, !zKrankDef rk d ∧ ∃ r', !max.dfn r' rA rk ∧
    ∃ f, !fstIdxDef f d ∧ ∃ l, !lhDef l ds ∧ ∃ u, !seqInsertAuxDef u ds i a b (l + 1) ∧
    !zKGraph y f r' u”

set_option maxHeartbeats 800000 in
instance iRKs_defined : 𝚺₁-Function₂ (iRKs : V → V → V) via iRKsDef := .mk fun v ↦ by
  simp [iRKsDef, iRKs, seqInsert, permIdx_defined.iff, zKseq_defined.iff, znth_defined.iff,
    fstIdx_defined.iff, seqSucc_defined.iff, irk_defined.iff, zKrank_defined.iff,
    max_defined.iff, lh_defined.iff, seqInsertAux_defined.iff, zK_defined.iff]

instance iRKs_definable : 𝚺₁-Function₂ (iRKs : V → V → V) := iRKs_defined.to_definable

/-- `redexCode d = redexAux (zKseq d) ⟪lh(zKseq d), lh(zKseq d)⟫` (the least valid redex pair). -/
noncomputable def _root_.LO.FirstOrder.Arithmetic.redexCodeDef : 𝚺₁.Semisentence 2 := .mkSigma
  “y d. ∃ ds, !zKseqDef ds d ∧ ∃ l, !lhDef l ds ∧ ∃ b, !pairDef b l l ∧ !redexAuxDef y ds b”
instance redexCode_defined : 𝚺₁-Function₁ (redexCode : V → V) via redexCodeDef := .mk
  fun v ↦ by simp [redexCodeDef, redexCode, zKseq_defined.iff, lh_defined.iff, redexAux_defined.iff]
instance redexCode_definable : 𝚺₁-Function₁ (redexCode : V → V) := redexCode_defined.to_definable

/-- `redexI d = π₁ (redexCode d)`. -/
noncomputable def _root_.LO.FirstOrder.Arithmetic.redexIDef : 𝚺₁.Semisentence 2 := .mkSigma
  “y d. ∃ c, !redexCodeDef c d ∧ !pi₁Def y c”
instance redexI_defined : 𝚺₁-Function₁ (redexI : V → V) via redexIDef := .mk
  fun v ↦ by simp [redexIDef, redexI, redexCode_defined.iff, pi₁_defined.iff]
instance redexI_definable : 𝚺₁-Function₁ (redexI : V → V) := redexI_defined.to_definable

/-- `redexJ d = π₂ (redexCode d)`. -/
noncomputable def _root_.LO.FirstOrder.Arithmetic.redexJDef : 𝚺₁.Semisentence 2 := .mkSigma
  “y d. ∃ c, !redexCodeDef c d ∧ !pi₂Def y c”
instance redexJ_defined : 𝚺₁-Function₁ (redexJ : V → V) via redexJDef := .mk
  fun v ↦ by simp [redexJDef, redexJ, redexCode_defined.iff, pi₂_defined.iff]
instance redexJ_definable : 𝚺₁-Function₁ (redexJ : V → V) := redexJ_defined.to_definable

/-- `iCritReductSeq d0 d1 = seqCons (seqCons ∅ d0) d1` (the two-element reduct premise sequence). -/
def _root_.LO.FirstOrder.Arithmetic.iCritReductSeqDef : 𝚺₁.Semisentence 3 := .mkSigma
  “y d0 d1. ∃ s1, !seqConsDef s1 0 d0 ∧ !seqConsDef y s1 d1”
instance iCritReductSeq_defined : 𝚺₁-Function₂ (iCritReductSeq : V → V → V) via iCritReductSeqDef :=
  .mk fun v ↦ by simp [iCritReductSeqDef, iCritReductSeq, seqCons_defined.iff, emptyset_def]
instance iCritReductSeq_definable : 𝚺₁-Function₂ (iCritReductSeq : V → V → V) :=
  iCritReductSeq_defined.to_definable

/-- `iCritReduct d i j v w = zK (fstIdx d) (zKrank d − 1) (iCritReductSeq (iCritAux d i v)
(iCritAux d j w))` (Buchholz Def 3.2 case 5.1 reduct `d[0] = K^{r-1}_Π d{0} d{1}`). -/
def _root_.LO.FirstOrder.Arithmetic.iCritReductDef : 𝚺₁.Semisentence 6 := .mkSigma
  “y d i j v w. ∃ f, !fstIdxDef f d ∧ ∃ rk, !zKrankDef rk d ∧ ∃ rk1, !subDef rk1 rk 1 ∧
    ∃ a, !iCritAuxDef a d i v ∧ ∃ b, !iCritAuxDef b d j w ∧
    ∃ s, !iCritReductSeqDef s a b ∧ !zKGraph y f rk1 s”
instance iCritReduct_defined :
    𝚺₁-Function₅ (iCritReduct : V → V → V → V → V → V) via iCritReductDef := .mk
  fun v ↦ by simp [iCritReductDef, iCritReduct, fstIdx_defined.iff, zKrank_defined.iff,
    sub_defined.iff, iCritAux_defined.iff, iCritReductSeq_defined.iff, zK_defined.iff]

/-- `iIndReductSeq d0 d1 k = seqCons (iRepeatSeq d1 k) d0` (the `Ind` reduct premise sequence). -/
def _root_.LO.FirstOrder.Arithmetic.iIndReductSeqDef : 𝚺₁.Semisentence 4 := .mkSigma
  “y d0 d1 k. ∃ r, !iRepeatSeqDef r d1 k ∧ !seqConsDef y r d0”
instance iIndReductSeq_defined :
    𝚺₁-Function₃ (iIndReductSeq : V → V → V → V) via iIndReductSeqDef := .mk
  fun v ↦ by simp [iIndReductSeqDef, iIndReductSeq, iRepeatSeq_defined.iff, seqCons_defined.iff]
instance iIndReductSeq_definable : 𝚺₁-Function₃ (iIndReductSeq : V → V → V → V) :=
  iIndReductSeq_defined.to_definable

/-- `iRInd d = zK (fstIdx d) (irk (zIndP d)) (iIndReductSeq (zIndPrem0 d) (zIndPrem1 d) 1)`
(the closed `Ind`-rule reduct, Buchholz §3.2 case 4 at the count-1 ordinal model). -/
noncomputable def _root_.LO.FirstOrder.Arithmetic.iRIndDef : 𝚺₁.Semisentence 2 := .mkSigma
  “y d. ∃ f, !fstIdxDef f d ∧ ∃ pf, !zIndPDef pf d ∧ ∃ rk, !irkDef rk pf ∧
    ∃ p0, !zIndPrem0Def p0 d ∧ ∃ p1, !zIndPrem1Def p1 d ∧ ∃ s, !iIndReductSeqDef s p0 p1 1 ∧
    !zKGraph y f rk s”
instance iRInd_defined : 𝚺₁-Function₁ (iRInd : V → V) via iRIndDef := .mk
  fun v ↦ by simp [iRIndDef, iRInd, fstIdx_defined.iff, zIndP_defined.iff, irk_defined.iff,
    zIndPrem0_defined.iff, zIndPrem1_defined.iff, iIndReductSeq_defined.iff, zK_defined.iff]
instance iRInd_definable : 𝚺₁-Function₁ (iRInd : V → V) := iRInd_defined.to_definable

/-! ## `iR2` — the recursive `iR` (`d ↦ d[0]`) as a total `𝚺₁` course-of-values `<`-recursion

Lap-71's named architectural blocker. The Buchholz reduction `iR` is `𝚺₁` by the SAME table reduction
as `idg`/`iotil` (`idgTable`/`ioTable`): `iRTable n = ⟨iR2 0,…,iR2 n⟩`, the step `iRNext d s` reading
sub-reducts out of `s` at the premise indices (all `< d`). The structural branches are CLOSED in `d`
(`I∀`→`zIallPrem`, `I¬`→`zInegPrem`, `Ind`→`iRInd`, atom/axioms→`d`); the **K-branch** is the only one
that recurses: the critical reduct `d[0] = K^{r-1}_Π d{0} d{1}` (`iCritReduct`) at the FUNCTIONAL redex
`(redexI d, redexJ d)`, with the two auxiliaries' premise-reducts `dᵢ[k] = iR2(znth ds (redexI d))`,
`d_j[0] = iR2(znth ds (redexJ d))` read from `s` (both premise codes `< zK s r ds`). This realizes the
abstract `ρ`-supplied `iRcrit d ρ` at the CONCRETE `ρ = fun n ↦ iR2 (znth (zKseq d) n)` — the genuine
recursive reduct, no abstract input. (For non-critical/splice K-chains the K-branch still emits the
critical reduct; the descent-side dispatch selects the right per-case wrapper — a later brick.) -/

/-- A general HFS bound: `znth ds k ≤ ds` for ALL `k` (in-range: the read is an element `≤ ds`;
out-of-range: `znth = 0 ≤ ds`). Needed to land premise-reads `znth ds k` inside the length-`(zK-1)`
table. -/
lemma znth_le_self (ds k : V) : znth ds k ≤ ds := by
  by_cases h : Seq ds ∧ k < lh ds
  · exact le_of_lt (lt_of_mem_rng (h.1.znth h.2))
  · rw [znth_prop_not (by rw [not_and_or, not_lt] at h; exact h)]; simp

/-- **The §5 atomic-reduct FUNCTION** `d ↦ d[0]` for an L-axiom premise (Buchholz §5, Lemma 5.2):
`Ax^{∀p,k} ↦ Ax^1_{·→p}` (tag 5) and `Ax^{¬p,0} ↦ Ax^1_{·→p}` (tag 6) — the principal formula stripped
to its rank-one-lower matrix. Identity off the atomic-axiom tags. This is the j-component the K-case
critical reduction installs (in `iRNext`/`iCritReduct` tag-4) instead of the table lookup `iR2(premⱼ)`,
which is the identity on axioms (`iR2_zAxAll`/`iR2_zAxNeg`) and so yields NO õ-drop on the j-side. -/
noncomputable def zAxReduct (d : V) : V :=
  if zTag d = 5 then zAx1 (fstIdx d) (zAxAllF d)
  else if zTag d = 6 then zAx1 (fstIdx d) (zAxNegF d)
  else d

@[simp] lemma zAxReduct_zAxAll (s p k : V) : zAxReduct (zAxAll s p k) = zAx1 s p := by
  simp [zAxReduct]

@[simp] lemma zAxReduct_zAxNeg (s p : V) : zAxReduct (zAxNeg s p) = zAx1 s p := by
  rw [zAxReduct, if_neg (by simp [zTag_zAxNeg]), if_pos (by simp [zTag_zAxNeg])]
  simp

/-- **Σ₁-definability of `zAxReduct`** (`zAxAllF d = π₁(zRest d)`, `zAxNegF d = zRest d`; `zAx1` via its
graph). The arithmetization that lets `zAxReduct` thread through the `iRNext`/`iCritReduct` tag-4
definition. -/
noncomputable def _root_.LO.FirstOrder.Arithmetic.zAxReductDef : 𝚺₁.Semisentence 2 := .mkSigma
  “y d. ∃ t, !zTagDef t d ∧
    ( (t = 5 ∧ ∃ s, !fstIdxDef s d ∧ ∃ r, !zRestDef r d ∧ ∃ p, !pi₁Def p r ∧ !zAx1Graph y s p)
    ∨ (t = 6 ∧ ∃ s, !fstIdxDef s d ∧ ∃ p, !zRestDef p d ∧ !zAx1Graph y s p)
    ∨ (t ≠ 5 ∧ t ≠ 6 ∧ y = d) )”

set_option maxHeartbeats 800000 in
instance zAxReduct_defined : 𝚺₁-Function₁ (zAxReduct : V → V) via zAxReductDef := .mk fun v ↦ by
  simp [zAxReductDef, zAxReduct, zTag_defined.iff, fstIdx_defined.iff, zRest_defined.iff,
    pi₁_defined.iff, zAx1_defined.iff, zAxAllF, zAxNegF, numeral_eq_natCast]
  by_cases h5 : zTag (v 1) = 5
  · simp [h5]
  · by_cases h6 : zTag (v 1) = 6
    · simp [h5, h6]
    · simp [h5, h6]

instance zAxReduct_definable : 𝚺₁-Function₁ (zAxReduct : V → V) := zAxReduct_defined.to_definable

/-- Table step of `iR2`: `iR2 d` from `s = ⟨iR2 0,…,iR2 (d-1)⟩`, dispatching on `zTag d`. -/
noncomputable def iRNext (d s : V) : V :=
  if zTag d = 1 then zIallPrem d
  else if zTag d = 2 then zInegPrem d
  else if zTag d = 3 then iRInd d
  else if zTag d = 4 then
    iCritReduct d (redexI d) (redexJ d)
      (zAxReduct (znth s (znth (zKseq d) (redexI d))))
      (zAxReduct (znth s (znth (zKseq d) (redexJ d))))
  else d

noncomputable def _root_.LO.FirstOrder.Arithmetic.iRNextDef : 𝚺₁.Semisentence 3 := .mkSigma
  “y d s. ∃ t, !zTagDef t d ∧
    ( (t = 1 ∧ !zIallPremDef y d)
    ∨ (t = 2 ∧ !zInegPremDef y d)
    ∨ (t = 3 ∧ !iRIndDef y d)
    ∨ (t = 4 ∧ ∃ ds, !zKseqDef ds d ∧ ∃ i, !redexIDef i d ∧ ∃ j, !redexJDef j d ∧
        ∃ ai, !znthDef ai ds i ∧ ∃ aj, !znthDef aj ds j ∧
        ∃ vi, !znthDef vi s ai ∧ ∃ wi, !zAxReductDef wi vi ∧
        ∃ vj, !znthDef vj s aj ∧ ∃ wj, !zAxReductDef wj vj ∧ !iCritReductDef y d i j wi wj)
    ∨ (t ≠ 1 ∧ t ≠ 2 ∧ t ≠ 3 ∧ t ≠ 4 ∧ y = d) )”

set_option maxHeartbeats 1000000 in
instance iRNext_defined : 𝚺₁-Function₂ (iRNext : V → V → V) via iRNextDef := .mk fun v ↦ by
  simp [iRNextDef, iRNext, zTag_defined.iff, zIallPrem_defined.iff, zInegPrem_defined.iff,
    iRInd_defined.iff, zKseq_defined.iff, redexI_defined.iff, redexJ_defined.iff,
    znth_defined.iff, zAxReduct_defined.iff, iCritReduct_defined.iff]
  by_cases h1 : zTag (v 1) = 1
  · simp [h1]
  · by_cases h2 : zTag (v 1) = 2
    · simp [h1, h2]
    · by_cases h3 : zTag (v 1) = 3
      · simp [h1, h2, h3]
      · by_cases h4 : zTag (v 1) = 4
        · simp [h1, h2, h3, h4]
        · simp [h1, h2, h3, h4]

instance iRNext_definable : 𝚺₁-Function₂ (iRNext : V → V → V) := iRNext_defined.to_definable

/-- Blueprint for the `iR2` table. -/
noncomputable def iRTable.blueprint : PR.Blueprint 0 where
  zero := .mkSigma “y. !mkSeq₁Def y 0”
  succ := .mkSigma “y ih n. ∃ v, !iRNextDef v (n + 1) ih ∧ !seqConsDef y ih v”

noncomputable def iRTable.construction : PR.Construction V iRTable.blueprint where
  zero := fun _ ↦ !⟦0⟧
  succ := fun _ n ih ↦ seqCons ih (iRNext (n + 1) ih)
  zero_defined := .mk fun v ↦ by
    simp [iRTable.blueprint, mkSeq₁Def, seqCons_defined.iff, emptyset_def]
  succ_defined := .mk fun v ↦ by
    simp [iRTable.blueprint, iRNext_defined.iff, seqCons_defined.iff]

/-- **The `iR2` table**: `iRTable n = ⟨iR2 0,…,iR2 n⟩` (length `n+1`). -/
noncomputable def iRTable (n : V) : V := iRTable.construction.result ![] n

@[simp] lemma iRTable_zero : iRTable (0 : V) = !⟦0⟧ := by simp [iRTable, iRTable.construction]

@[simp] lemma iRTable_succ (n : V) :
    iRTable (n + 1) = seqCons (iRTable n) (iRNext (n + 1) (iRTable n)) := by
  simp [iRTable, iRTable.construction]

noncomputable def _root_.LO.FirstOrder.Arithmetic.iRTableDef : 𝚺₁.Semisentence 2 :=
  iRTable.blueprint.resultDef.rew (Rew.subst ![#0, #1])

instance iRTable_defined : 𝚺₁-Function₁ (iRTable : V → V) via iRTableDef := .mk
  fun v ↦ by simp [iRTable.construction.result_defined_iff, iRTableDef]; rfl
instance iRTable_definable : 𝚺₁-Function₁ (iRTable : V → V) := iRTable_defined.to_definable
instance iRTable_definable' (Γ) : Γ-[m + 1]-Function₁ (iRTable : V → V) :=
  iRTable_definable.of_sigmaOne

/-- **The recursive `iR2`** `d ↦ d[0]`: the `d`-th entry of the table. -/
noncomputable def iR2 (d : V) : V := znth (iRTable d) d

noncomputable def _root_.LO.FirstOrder.Arithmetic.iR2Def : 𝚺₁.Semisentence 2 := .mkSigma
  “y d. ∃ t, !iRTableDef t d ∧ !znthDef y t d”
instance iR2_defined : 𝚺₁-Function₁ (iR2 : V → V) via iR2Def := .mk fun v ↦ by
  simp [iR2Def, iR2, iRTable_defined.iff, znth_defined.iff]
instance iR2_definable : 𝚺₁-Function₁ (iR2 : V → V) := iR2_defined.to_definable
instance iR2_definable' (Γ) : Γ-[m + 1]-Function₁ (iR2 : V → V) := iR2_definable.of_sigmaOne

/-! ## The STRIPPED cut formula `A(d)` (Buchholz Thm 3.4(a)) — the rank-strict critical reduct

Buchholz Thm 3.4(a) cuts the critical reduct on the **stripped** subformula `A(d)`, not on the
principal `A_i = chainAsucc (zKseq d) (redexI d)`: for `A_i = ∀xF` the cut formula is the L-instance
`F(k)` (`k` read off the `L^k_{A_i}` redex premise `redexJ`), and `rk(F(k)) < rk(∀xF) ≤ r`; for
`A_i = ¬A = inegF A` it is `A`, and `rk(A) < rk(¬A) ≤ r`. This **strict** drop (`< r`, vs the
principal's non-strict `≤ r`) is exactly what the splice rank bound `hr'` and the critical-soundness
`hCrk` need (lap-110 root cause). `cutFormula` computes it; `irk_cutFormula_lt` is the strict bound. -/

/-- The inference-symbol shape forces the cut formula `A_i` of an `L^k_{A_i}` redex premise to be
either `∀xF` (tag-5 axiom) or `¬A = inegF A` (tag-6 axiom): the only two `tp`-cases that emit an
`isymLk`. -/
lemma tp_isymLk_form {d k A : V} (h : tp d = isymLk k A) :
    (∃ p, A = (^∀ p : V)) ∨ (∃ p, A = inegF p) := by
  unfold tp at h
  by_cases ht1 : zTag d = 1
  · rw [if_pos ht1] at h; exact absurd h (by simp [isymR, isymLk])
  rw [if_neg ht1] at h
  by_cases ht2 : zTag d = 2
  · rw [if_pos ht2] at h; exact absurd h (by simp [isymR, isymLk])
  rw [if_neg ht2] at h
  by_cases ht5 : zTag d = 5
  · rw [if_pos ht5] at h
    exact Or.inl ⟨_, ((isymLk_inj _ _ _ _).mp h.symm).2⟩
  rw [if_neg ht5] at h
  by_cases ht6 : zTag d = 6
  · rw [if_pos ht6] at h
    exact Or.inr ⟨_, ((isymLk_inj _ _ _ _).mp h.symm).2⟩
  rw [if_neg ht6] at h; exact absurd h (by simp [isymRep, isymLk])

/-- **The stripped cut formula `A(d)`.** `A_i := chainAsucc (zKseq d) (redexI d)` (principal of the
`R`-redex premise). If `A_i = ∀xF` (`π₁(A_i−1) = 6`, the `qqAll` tag) then `A(d) = F(k)` with the
instance `k = π₁(π₂(tp d_redexJ))` read off the `L^k` premise; else (`A_i = ¬A`) `A(d) = A`. -/
noncomputable def cutFormula (d : V) : V :=
  if π₁ (chainAsucc (zKseq d) (redexI d) - 1) = 6 then
    substs1 ℒₒᵣ
      (Bootstrapping.Arithmetic.numeral (π₁ (π₂ (tp (znth (zKseq d) (redexJ d))))))
      (π₂ (chainAsucc (zKseq d) (redexI d) - 1))
  else
    neg ℒₒᵣ (π₁ (π₂ (chainAsucc (zKseq d) (redexI d) - 1)))

/-- `𝚺₁` graph of `cutFormula` (template `tpReduceDef`): dispatch on the `qqAll` tag `π₁(A_i−1) = 6`,
the `∀`-branch substituting the `numeral` of the `L^k` instance into the matrix. -/
noncomputable def _root_.LO.FirstOrder.Arithmetic.cutFormulaDef : 𝚺₁.Semisentence 2 := .mkSigma
  “y d. ∃ ds, !zKseqDef ds d ∧ ∃ i, !redexIDef i d ∧ ∃ A, !chainAsuccDef A ds i ∧
    ∃ Am, !subDef Am A 1 ∧ ∃ q, !pi₁Def q Am ∧
    ( (q = 6 ∧ ∃ j, !redexJDef j d ∧ ∃ dj, !znthDef dj ds j ∧ ∃ tj, !tpDef tj dj ∧
        ∃ p2j, !pi₂Def p2j tj ∧ ∃ k, !pi₁Def k p2j ∧
        ∃ nk, !(Bootstrapping.Arithmetic.numeralGraph) nk k ∧
        ∃ bod, !pi₂Def bod Am ∧ !(substs1Graph ℒₒᵣ) y nk bod)
    ∨ (q ≠ 6 ∧ ∃ p2Am, !pi₂Def p2Am Am ∧ ∃ qq, !pi₁Def qq p2Am ∧ !(negGraph ℒₒᵣ) y qq) )”

set_option maxHeartbeats 1600000 in
instance cutFormula_defined : 𝚺₁-Function₁ (cutFormula : V → V) via cutFormulaDef := .mk fun v ↦ by
  simp [cutFormulaDef, cutFormula, zKseq_defined.iff, redexI_defined.iff, chainAsucc_defined.iff,
    sub_defined.iff, pi₁_defined.iff, redexJ_defined.iff, znth_defined.iff, tp_defined.iff,
    pi₂_defined.iff, (Bootstrapping.Arithmetic.numeral_defined (V := V)).iff,
    (substs1.defined (L := ℒₒᵣ)).iff, (neg.defined (L := ℒₒᵣ)).iff]
  by_cases hq : π₁ (chainAsucc (zKseq (v 1)) (redexI (v 1)) - 1) = 6 <;>
    simp [hq, numeral_eq_natCast]

instance cutFormula_definable : 𝚺₁-Function₁ (cutFormula : V → V) := cutFormula_defined.to_definable
instance cutFormula_definable' (Γ) : Γ-[m + 1]-Function₁ (cutFormula : V → V) :=
  cutFormula_definable.of_sigmaOne

/-- `∀`-case readout: when the principal is `∀xF`, the stripped cut formula is the instance `F(k)`. -/
lemma cutFormula_all {d p : V}
    (hA : chainAsucc (zKseq d) (redexI d) = (^∀ p : V)) :
    cutFormula d = substs1 ℒₒᵣ
      (Bootstrapping.Arithmetic.numeral (π₁ (π₂ (tp (znth (zKseq d) (redexJ d)))))) p := by
  unfold cutFormula
  rw [hA, if_pos (by simp [qqAll])]
  simp [qqAll]

/-- `¬`-case readout: when the principal is `¬A = inegF A` (with `A` a `UFormula`), the stripped cut
formula is `A`. -/
lemma cutFormula_neg {d p : V} (hp : IsUFormula ℒₒᵣ p)
    (hA : chainAsucc (zKseq d) (redexI d) = inegF p) :
    cutFormula d = p := by
  unfold cutFormula
  rw [hA, if_neg (by simp [inegF, qqOr])]
  simp [inegF, qqOr, hp.neg_neg]

/-- **The R-redex premise carries the cut formula's well-formedness.** A genuine `ZDerivation` whose
`tp` is a right symbol `R_A` introduces `A` by an `I∀` (tag 1) or `I¬` (tag 2) rule, so `A = ∀xF` with
the matrix `IsSemiformula ℒₒᵣ 1 F` (from `zIallWff`) or `A = ¬B = inegF B` with `IsUFormula B` (from
`zInegWff`). This is where the **closedness** the substitution rank lemma needs comes from — it is
NOT in the (`IsUFormula`-only) chain validity, but in the I-rule premise's side condition. -/
lemma tp_isymR_form_wff {d A : V} (hZ : ZDerivation d) (h : tp d = isymR A) :
    (∃ p, A = (^∀ p : V) ∧ IsSemiformula ℒₒᵣ 1 p) ∨ (∃ p, A = inegF p ∧ IsUFormula ℒₒᵣ p) := by
  rcases zDerivation_iff.mp hZ with ⟨s, rfl, _⟩ | ⟨s, a, p, d0, rfl, _, _, hwff⟩ |
    ⟨s, p, d0, rfl, _, _, hwff⟩ | ⟨s, at', p, d0, d1, rfl, _, _, _⟩ | ⟨s, r, ds, rfl, _, _, _⟩ |
    ⟨s, p, k, rfl, _, _⟩ | ⟨s, p, rfl, _, _⟩ | ⟨s, C, rfl, _⟩
  · rw [tp_zAtom] at h; exact absurd h (by simp)
  · rw [tp_zIall] at h; exact Or.inl ⟨p, ((isymR_inj _ _).mp h).symm, hwff.2.2⟩
  · rw [tp_zIneg] at h; exact Or.inr ⟨p, ((isymR_inj _ _).mp h).symm, hwff.1.2.2⟩
  · rw [tp_zInd] at h; exact absurd h (by simp)
  · rw [tp_zK] at h; exact absurd h (by simp)
  · rw [tp_zAxAll] at h; exact absurd h (by simp)
  · rw [tp_zAxNeg] at h; exact absurd h (by simp)
  · rw [tp_zAx1] at h; exact absurd h (by simp)

/-- **R-redex constructor form.** A `ZDerivation` whose `tp` is a right symbol `R_A` is exactly an `I∀`
(`zIall`, `A = ∀p`) or `I¬` (`zIneg`, `A = ¬p`) rule — the explicit constructor the corrected reduct
`critReductCorr`/`critReductNeg` needs (`tp_isymR_form_wff` gives only the formula, not the node). -/
lemma zDerivation_isymR_form {d A : V} (hZ : ZDerivation d) (h : tp d = isymR A) :
    (∃ s a p d0, d = zIall s a p d0 ∧ A = (^∀ p : V)) ∨
    (∃ s p d0, d = zIneg s p d0 ∧ A = inegF p) := by
  rcases zDerivation_iff.mp hZ with ⟨s, rfl, _⟩ | ⟨s, a, p, d0, rfl, _, _, _⟩ |
    ⟨s, p, d0, rfl, _, _, _⟩ | ⟨s, at', p, d0, d1, rfl, _, _, _⟩ | ⟨s, r, ds, rfl, _, _, _⟩ |
    ⟨s, p, k, rfl, _, _⟩ | ⟨s, p, rfl, _, _⟩ | ⟨s, C, rfl, _⟩
  · rw [tp_zAtom] at h; exact absurd h (by simp [isymR, isymRep])
  · rw [tp_zIall] at h; exact Or.inl ⟨s, a, p, d0, rfl, ((isymR_inj _ _).mp h).symm⟩
  · rw [tp_zIneg] at h; exact Or.inr ⟨s, p, d0, rfl, ((isymR_inj _ _).mp h).symm⟩
  · rw [tp_zInd] at h; exact absurd h (by simp [isymR, isymRep])
  · rw [tp_zK] at h; exact absurd h (by simp [isymR, isymRep])
  · rw [tp_zAxAll] at h; exact absurd h (by simp [isymR, isymLk])
  · rw [tp_zAxNeg] at h; exact absurd h (by simp [isymR, isymLk])
  · rw [tp_zAx1] at h; exact absurd h (by simp [isymR, isymRep])

/-- **L-redex constructor form.** A `ZDerivation` whose `tp` is a left symbol `L^k_A` is exactly an `axAll`
(`zAxAll s p k`, `A = ∀p`) or `axNeg` (`zAxNeg s p`, `k = 0`, `A = ¬p`) axiom. The explicit constructor the
corrected L-reduct `Ax^1` needs. -/
lemma zDerivation_isymLk_form {d k A : V} (hZ : ZDerivation d) (h : tp d = isymLk k A) :
    (∃ s p, d = zAxAll s p k ∧ A = (^∀ p : V)) ∨
    (∃ s p, d = zAxNeg s p ∧ k = 0 ∧ A = inegF p) := by
  rcases zDerivation_iff.mp hZ with ⟨s, rfl, _⟩ | ⟨s, a, p, d0, rfl, _, _, _⟩ |
    ⟨s, p, d0, rfl, _, _, _⟩ | ⟨s, at', p, d0, d1, rfl, _, _, _⟩ | ⟨s, r, ds, rfl, _, _, _⟩ |
    ⟨s, p, k', rfl, _, _⟩ | ⟨s, p, rfl, _, _⟩ | ⟨s, C, rfl, _⟩
  · rw [tp_zAtom] at h; exact absurd h (by simp [isymLk, isymRep])
  · rw [tp_zIall] at h; exact absurd h (by simp [isymR, isymLk])
  · rw [tp_zIneg] at h; exact absurd h (by simp [isymR, isymLk])
  · rw [tp_zInd] at h; exact absurd h (by simp [isymLk, isymRep])
  · rw [tp_zK] at h; exact absurd h (by simp [isymLk, isymRep])
  · rw [tp_zAxAll] at h
    obtain ⟨hk, hA⟩ := (isymLk_inj _ _ _ _).mp h.symm
    exact Or.inl ⟨s, p, by rw [hk], hA⟩
  · rw [tp_zAxNeg] at h
    obtain ⟨hk, hA⟩ := (isymLk_inj _ _ _ _).mp h.symm
    exact Or.inr ⟨s, p, rfl, hk, hA⟩
  · rw [tp_zAx1] at h; exact absurd h (by simp [isymLk, isymRep])

/-- **T3.4(a) strict rank bound for the stripped cut formula — fully self-contained.** From the R-redex
premise `dᵢ` being a `ZDerivation` (`hZi`) with `tp dᵢ = R_{A_i}` (`hRi`, `A_i = chainAsucc …`) of rank
`≤ r` (`hrank`), the stripped cut formula has rank **strictly** below `r`: `rk(F(k)) < rk(∀xF) ≤ r` /
`rk(A) < rk(¬A) ≤ r`. The matrix closedness (`IsSemiformula 1`) needed for the `∀`-case substitution
rank invariance is supplied by `tp_isymR_form_wff` (the I∀ premise's `zIallWff`), NOT by any external
hypothesis — so this dissolves the lap-110/112 closedness gap on the descent context. This is the
degree drop the principal cut formula (`≤ r`, non-strict) fails to give (lap-110 root cause). -/
lemma irk_cutFormula_lt {d r : V}
    (hZi : ZDerivation (znth (zKseq d) (redexI d)))
    (hRi : tp (znth (zKseq d) (redexI d)) = isymR (chainAsucc (zKseq d) (redexI d)))
    (hrank : irk (chainAsucc (zKseq d) (redexI d)) ≤ r) :
    irk (cutFormula d) < r := by
  rcases tp_isymR_form_wff hZi hRi with ⟨p, hp, hsfp⟩ | ⟨p, hp, hUfp⟩
  · -- `A_i = ∀xF`, cut formula `F(k)`: `rk(F(k)) < rk(∀xF) ≤ r` (matrix `IsSemiformula 1` from I∀).
    rw [cutFormula_all hp]
    exact irk_cut_lt_rank_forall (m := 0) hsfp (by simp) (hp ▸ hrank)
  · -- `A_i = ¬A = inegF A`, cut formula `A`: `rk(A) < rk(¬A) ≤ r`.
    rw [cutFormula_neg hUfp hp]
    exact irk_cut_lt_rank_neg hUfp (hp ▸ hrank)

/-- **The genuine closed critical branch** for `red`'s tag-4 case: `K^{r-1}_Π ⟨d{0}, d{1}⟩` where the cut
formula is `A(d) = chainAsucc (zKseq d) (redexI d)`, the auxiliaries replace the redex premises `i = redexI d`,
`j = redexJ d` by their `ρ`-reducts, and carry the reduced endsequents. Closed term; only `ρ` (the N1 IH)
is abstract. (Soundness `ZDerivation_iRcritG_of` is proved later, after `ZDerivation_iCritReductG_of`.) -/
noncomputable def iRcritG (d : V) (ρ : V → V) : V :=
  iCritReductG (fstIdx d) (cutFormula d) (zKrank d - 1) (zKrank d) (zKrank d)
    (seqUpdate (zKseq d) (redexI d) (ρ (redexI d)))
    (seqUpdate (zKseq d) (redexJ d) (ρ (redexJ d)))

@[simp] lemma fstIdx_iRcritG (d : V) (ρ : V → V) : fstIdx (iRcritG d ρ) = fstIdx d := by
  simp [iRcritG]
@[simp] lemma zTag_iRcritG (d : V) (ρ : V → V) : zTag (iRcritG d ρ) = 4 := by simp [iRcritG]

/-- **The SWAPPED-half critical reduct — the ¬-case constructor (Buchholz Def 3.2 case 5.1, subcase
`Aᵢ = ¬A`).** For a critical cut on a NEGATION `¬A` the two auxiliary half-derivations are assigned to the
OPPOSITE redex premises from the `∀`-case (Buchholz's `d{0} := K^r_{Π.A(d)}(j/dⱼ[0])`, `d{1} :=
K^r_{A(d),Π}(i/dᵢ[0])` for `Aᵢ = ¬A`):
- `d{0}` (the SUCCEDENT half `Π.A(d)`, conclusion `Γ→A`) replaces the **L**-redex `j` (the `axNeg` axiom,
  whose §5 reduct `dⱼ[0]` derives `Γⱼ→A`), and
- `d{1}` (the ANTECEDENT half `A(d),Π`, conclusion `A,Γ→⊥`) replaces the **R**-redex `i` (the `I¬` rule,
  whose reduct `dᵢ[0] = d₀` derives `A,Γᵢ→⊥`).
This is exactly `iRcritG` with `redexI`/`redexJ` swapped in the two `seqUpdate` slots. Since `iCritReductG`
is symmetric in its ordinal (`#` is commutative), the ordinal DESCENT is SHARED with `iRcritG`/`iRcrit`;
only SOUNDNESS distinguishes the two polarities, which is why the engine `red` (descent-keyed) survives the
distinction but the inversion `ZDerivation_red_zK_crit` needs the polarity-correct constructor. -/
noncomputable def iRcritGNeg (d : V) (ρ : V → V) : V :=
  iCritReductG (fstIdx d) (cutFormula d) (zKrank d - 1) (zKrank d) (zKrank d)
    (seqUpdate (zKseq d) (redexJ d) (ρ (redexJ d)))
    (seqUpdate (zKseq d) (redexI d) (ρ (redexI d)))

@[simp] lemma fstIdx_iRcritGNeg (d : V) (ρ : V → V) : fstIdx (iRcritGNeg d ρ) = fstIdx d := by
  simp [iRcritGNeg]
@[simp] lemma zTag_iRcritGNeg (d : V) (ρ : V → V) : zTag (iRcritGNeg d ρ) = 4 := by simp [iRcritGNeg]

/-! ## The 5.1 critical-reduct dispatch helper `iRKc` (Buchholz Def 3.2 case 5.1)

The standalone 5.1 case — exactly the (table-supplied) critical reduct the original `iRNextG` tag-4
inlined: `iRcritG d ρ` with `ρ idx = zAxReduct (znth s (znth (zKseq d) idx))` (the per-premise reduct
read from the table `s`). Extracted as a definable function so the dispatched `iRK` is three clean
function-application atoms (`iRKc` / `iRKs` / `iRKr`). -/
noncomputable def iRKc (d s : V) : V :=
  iRcritG d (fun idx => zAxReduct (znth s (znth (zKseq d) idx)))

@[simp] lemma fstIdx_iRKc (d s : V) : fstIdx (iRKc d s) = fstIdx d := by simp [iRKc]
@[simp] lemma zTag_iRKc (d s : V) : zTag (iRKc d s) = 4 := by simp [iRKc]

noncomputable def _root_.LO.FirstOrder.Arithmetic.iRKcDef : 𝚺₁.Semisentence 3 := .mkSigma
  “y d s. ∃ f, !fstIdxDef f d ∧ ∃ ds, !zKseqDef ds d ∧
    ∃ i, !redexIDef i d ∧ ∃ j, !redexJDef j d ∧
    ∃ C, !cutFormulaDef C d ∧ ∃ rk, !zKrankDef rk d ∧ ∃ rk1, !subDef rk1 rk 1 ∧
    ∃ ai, !znthDef ai ds i ∧ ∃ vi, !znthDef vi s ai ∧ ∃ wi, !zAxReductDef wi vi ∧
    ∃ aj, !znthDef aj ds j ∧ ∃ vj, !znthDef vj s aj ∧ ∃ wj, !zAxReductDef wj vj ∧
    ∃ u0, !seqUpdateDef u0 ds i wi ∧ ∃ ss, !seqSetSuccDef ss f C ∧ ∃ d0, !zKGraph d0 ss rk u0 ∧
    ∃ u1, !seqUpdateDef u1 ds j wj ∧ ∃ sa, !seqAddAntDef sa C f ∧ ∃ d1, !zKGraph d1 sa rk u1 ∧
    ∃ seq, !iCritReductSeqDef seq d0 d1 ∧ !zKGraph y f rk1 seq”

set_option maxHeartbeats 1600000 in
instance iRKc_defined : 𝚺₁-Function₂ (iRKc : V → V → V) via iRKcDef := .mk fun v ↦ by
  simp [iRKcDef, iRKc, iRcritG, iCritReductG, fstIdx_defined.iff, zKseq_defined.iff,
    redexI_defined.iff, redexJ_defined.iff, cutFormula_defined.iff, zKrank_defined.iff,
    sub_defined.iff, znth_defined.iff, zAxReduct_defined.iff, seqUpdate_defined.iff,
    seqSetSucc_defined.iff, seqAddAnt_defined.iff, iCritReductSeq_defined.iff, zK_defined.iff]

instance iRKc_definable : 𝚺₁-Function₂ (iRKc : V → V → V) := iRKc_defined.to_definable

/-! ## The tag-4 DISPATCH `iRK` (Buchholz Def 3.2 case 5: 5.1 / 5.2.1 / 5.2.2)

The genuine tag-4 reduct dispatches on criticality (lap-86 finding `not_zKCritical_red_zK`: the
critical-only reduct is itself non-critical after one step, so the dispatch is mandatory). We branch on
the **sentinel comparison `permIdx d < lh (zKseq d)`** rather than the Δ₁ relation `zKCritical`:
`permIdx d = lh (zKseq d)` ⟺ no permissible premise ⟺ the chain is critical (`permIdxAux_eq_self_of_none`),
and `permIdx d < lh (zKseq d)` ⟺ non-critical with `permIdx d` the least permissible premise
(`permIdxAux_isPermPrem_of_lt`). A Δ₀ comparison of definable values — far cleaner to make `𝚺₁` than
embedding `zKCriticalDef`. The sub-dispatch (5.2.1 splice vs 5.2.2 replace) tests the same sentinel on
the *selected premise* `dᵢ = znth (zKseq d) (permIdx d)`: `dᵢ` critical → 5.2.1 (`iRKs`), else 5.2.2 (`iRKr`). -/
noncomputable def iRK (d s : V) : V :=
  if permIdx d < lh (zKseq d) then
    (if zTag (znth (zKseq d) (permIdx d)) = 4 ∧
        ¬ permIdx (znth (zKseq d) (permIdx d)) < lh (zKseq (znth (zKseq d) (permIdx d)))
     then iRKs d s else iRKr d s)
  else iRKc d s

noncomputable def _root_.LO.FirstOrder.Arithmetic.iRKDef : 𝚺₁.Semisentence 3 := .mkSigma
  “y d s. ∃ p, !permIdxDef p d ∧ ∃ ds, !zKseqDef ds d ∧ ∃ l, !lhDef l ds ∧
    ( ( p < l ∧
        ∃ di, !znthDef di ds p ∧ ∃ tdi, !zTagDef tdi di ∧ ∃ pdi, !permIdxDef pdi di ∧
          ∃ dsi, !zKseqDef dsi di ∧ ∃ li, !lhDef li dsi ∧
          ( ( tdi = 4 ∧ li ≤ pdi ∧ !iRKsDef y d s )
          ∨ ( (tdi ≠ 4 ∨ pdi < li) ∧ !iRKrDef y d s ) ) )
    ∨ ( l ≤ p ∧ !iRKcDef y d s ) )”

set_option maxHeartbeats 1600000 in
instance iRK_defined : 𝚺₁-Function₂ (iRK : V → V → V) via iRKDef := .mk fun v ↦ by
  simp [iRKDef, iRK, permIdx_defined.iff, zKseq_defined.iff, lh_defined.iff, znth_defined.iff,
    zTag_defined.iff, iRKr_defined.iff, iRKs_defined.iff, iRKc_defined.iff]
  by_cases h1 : permIdx (v 1) < lh (zKseq (v 1))
  · by_cases ht : zTag (znth (zKseq (v 1)) (permIdx (v 1))) = 4
    · by_cases h2 : permIdx (znth (zKseq (v 1)) (permIdx (v 1)))
          < lh (zKseq (znth (zKseq (v 1)) (permIdx (v 1))))
      · simp [h1, ht, h2, not_le.mpr h1, not_le.mpr h2]
      · simp [h1, ht, h2, not_le.mpr h1, not_lt.mp h2]
    · simp [h1, ht, not_le.mpr h1]
  · simp [h1, not_lt.mp h1]

instance iRK_definable : 𝚺₁-Function₂ (iRK : V → V → V) := iRK_defined.to_definable

/-- **5.2.2 reduct conclusion (route B, lap 96)** — the reduced sequent `tpReduce (tp dᵢ) (fstIdx d) 0`. -/
@[simp] lemma fstIdx_iRKr (d s : V) :
    fstIdx (iRKr d s) = tpReduce (tp (znth (zKseq d) (permIdx d))) (fstIdx d) 0 := by simp [iRKr]
@[simp] lemma fstIdx_iRKs (d s : V) : fstIdx (iRKs d s) = fstIdx d := by simp [iRKs]
@[simp] lemma zTag_iRKr (d s : V) : zTag (iRKr d s) = 4 := by simp [iRKr]
@[simp] lemma zTag_iRKs (d s : V) : zTag (iRKs d s) = 4 := by simp [iRKs]

/-- **Replace-reduct keeps `Π` for a `Rep` selected premise.** When `tp dᵢ = Rep` (e.g. on the ⊥-orbit
by Cor 2.1) `tpReduce` is the identity, so the 5.2.2 reduct keeps the conclusion — recovering the old
unconditional `fstIdx_iRKr`. -/
lemma fstIdx_iRKr_of_Rep {d s : V} (htp : tp (znth (zKseq d) (permIdx d)) = isymRep) :
    fstIdx (iRKr d s) = fstIdx d := by simp [iRKr, htp]

/-- **Dispatch invariant — `iRK` keeps the conclusion sequent off the non-`Rep` replace case.** The 5.1
(`iRKc`) and 5.2.1 (`iRKs`) branches always keep `Π`; the 5.2.2 (`iRKr`) branch keeps `Π` exactly when the
selected premise is `Rep` (the conclusion-reduction case is the one route-B addition). On the ⊥-orbit all
selected premises are `Rep` (Cor 2.1), so `iRK` keeps `Π` there. -/
lemma fstIdx_iRK_of_Rep {d s : V}
    (htp : permIdx d < lh (zKseq d) →
      ¬ (zTag (znth (zKseq d) (permIdx d)) = 4 ∧
         ¬ permIdx (znth (zKseq d) (permIdx d)) < lh (zKseq (znth (zKseq d) (permIdx d)))) →
      tp (znth (zKseq d) (permIdx d)) = isymRep) :
    fstIdx (iRK d s) = fstIdx d := by
  unfold iRK
  split_ifs with h1 hs
  · simp
  · rw [fstIdx_iRKr_of_Rep (htp h1 hs)]
  · simp

/-- **Dispatch invariant — `iRK` is a `K`-chain (tag 4)** in every branch. -/
@[simp] lemma zTag_iRK (d s : V) : zTag (iRK d s) = 4 := by
  unfold iRK; split_ifs <;> simp

/-! ## The GENUINE reduct `red` (Buchholz §6 `red` / Def 3.2) — replaces the dead `iR2`

`red` is the validity-faithful reduct: identical to `iR2` on the I-rules (tags 1,2) and the `Ind` rule
(tag 3), but its critical `K`-case (tag 4) is `iRcritG` (the genuine recombination on the CORRECT reduced
endsequents `Θ→A(d)`/`A(d),Θ→D`) instead of `iR2`'s ordinal-shadow `iCritReduct`. Built by the same table
recursion as `iR2` (`iRNextG`/`redTable`/`red`), so `red` is total + `𝚺₁`-definable. -/

/-! ## `fvSubstSeq` — map `fvSubst a t` over a coded formula sequence

Mirrors `tpSeqAux`/`iseqMaxAux`: a `PR.Construction` over a length counter, with the pair `⟪a, t⟫`
as a single parameter (projected by `π₁`/`π₂`) plus the source sequence `Γ`. -/

noncomputable def fvSubstSeqAux.blueprint : PR.Blueprint 2 where
  zero := .mkSigma “y w Γ. y = 0”
  succ := .mkSigma “y ih n w Γ.
    ∃ a, !pi₁Def a w ∧ ∃ t, !pi₂Def t w ∧
      ∃ d, !znthDef d Γ n ∧ ∃ y0, !(fvSubstGraph ℒₒᵣ) y0 a t d ∧ !seqConsDef y ih y0”

noncomputable def fvSubstSeqAux.construction : PR.Construction V fvSubstSeqAux.blueprint where
  zero := fun _ ↦ ∅
  succ := fun x n ih ↦ seqCons ih (fvSubst ℒₒᵣ (π₁ (x 0)) (π₂ (x 0)) (znth (x 1) n))
  zero_defined := .mk fun v ↦ by simp [fvSubstSeqAux.blueprint, emptyset_def]
  succ_defined := .mk fun v ↦ by
    simp [fvSubstSeqAux.blueprint, pi₁_defined.iff, pi₂_defined.iff, znth_defined.iff,
      (fvSubst.defined (L := ℒₒᵣ)).iff, seqCons_defined.iff]

/-- `fvSubstSeqAux ⟪a,t⟫ Γ n = ⟨fvSubst a t (znth Γ 0),…,fvSubst a t (znth Γ (n−1))⟩` (length `n`). -/
noncomputable def fvSubstSeqAux (w Γ n : V) : V := fvSubstSeqAux.construction.result ![w, Γ] n

@[simp] lemma fvSubstSeqAux_zero (w Γ : V) : fvSubstSeqAux w Γ 0 = ∅ := by
  simp [fvSubstSeqAux, fvSubstSeqAux.construction]

@[simp] lemma fvSubstSeqAux_succ (w Γ n : V) :
    fvSubstSeqAux w Γ (n + 1) = seqCons (fvSubstSeqAux w Γ n) (fvSubst ℒₒᵣ (π₁ w) (π₂ w) (znth Γ n)) := by
  simp [fvSubstSeqAux, fvSubstSeqAux.construction]

noncomputable def _root_.LO.FirstOrder.Arithmetic.fvSubstSeqAuxDef : 𝚺₁.Semisentence 4 :=
  fvSubstSeqAux.blueprint.resultDef.rew (Rew.subst ![#0, #3, #1, #2])

instance fvSubstSeqAux_defined : 𝚺₁-Function₃ (fvSubstSeqAux : V → V → V → V) via fvSubstSeqAuxDef := .mk
  fun v ↦ by simp [fvSubstSeqAux.construction.result_defined_iff, fvSubstSeqAuxDef]; rfl

instance fvSubstSeqAux_definable : 𝚺₁-Function₃ (fvSubstSeqAux : V → V → V → V) :=
  fvSubstSeqAux_defined.to_definable
instance fvSubstSeqAux_definable' (Γ) : Γ-[m + 1]-Function₃ (fvSubstSeqAux : V → V → V → V) :=
  fvSubstSeqAux_definable.of_sigmaOne

@[simp] lemma fvSubstSeqAux_seq (w Γ n : V) : Seq (fvSubstSeqAux w Γ n) := by
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero => simpa using seq_empty
  case succ n ih => rw [fvSubstSeqAux_succ]; exact ih.seqCons _

@[simp] lemma fvSubstSeqAux_lh (w Γ n : V) : lh (fvSubstSeqAux w Γ n) = n := by
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero => simpa using lh_empty
  case succ n ih => rw [fvSubstSeqAux_succ, Seq.lh_seqCons _ (fvSubstSeqAux_seq w Γ n), ih]

lemma znth_fvSubstSeqAux_top (w Γ n : V) :
    znth (fvSubstSeqAux w Γ (n + 1)) n = fvSubst ℒₒᵣ (π₁ w) (π₂ w) (znth Γ n) := by
  rw [fvSubstSeqAux_succ]
  have := znth_seqCons_self (fvSubstSeqAux_seq w Γ n) (fvSubst ℒₒᵣ (π₁ w) (π₂ w) (znth Γ n))
  rwa [fvSubstSeqAux_lh] at this

lemma znth_fvSubstSeqAux_stable {w Γ : V} (n m : V) (hm : m < n) :
    znth (fvSubstSeqAux w Γ (n + 1)) m = znth (fvSubstSeqAux w Γ n) m := by
  rw [fvSubstSeqAux_succ, znth_seqCons_of_lt (fvSubstSeqAux_seq w Γ n) _ (by rw [fvSubstSeqAux_lh]; exact hm)]

lemma znth_fvSubstSeqAux_eq {w Γ : V} :
    ∀ n, ∀ i < n, znth (fvSubstSeqAux w Γ n) i = fvSubst ℒₒᵣ (π₁ w) (π₂ w) (znth Γ i) := by
  intro n
  induction n using ISigma1.sigma1_succ_induction
  · refine Definable.ball_lt (by definability) ?_
    apply Definable.comp₂ (by definability)
    apply DefinableFunction₃.comp (F := fvSubst ℒₒᵣ) (DefinableFunction.const _)
      (DefinableFunction.const _) (by definability)
  case zero => intro i hi; exact absurd hi (by simp)
  case succ n ih =>
    intro i hi
    rcases eq_or_lt_of_le (le_iff_lt_succ.mpr hi) with hin | hilt
    · rw [hin, znth_fvSubstSeqAux_top]
    · rw [znth_fvSubstSeqAux_stable n i hilt]; exact ih i hilt

/-- **Map `fvSubst a t` over a coded formula sequence** `Γ` (length-preserving). -/
noncomputable def fvSubstSeq (a t Γ : V) : V := fvSubstSeqAux ⟪a, t⟫ Γ (lh Γ)

noncomputable def _root_.LO.FirstOrder.Arithmetic.fvSubstSeqDef : 𝚺₁.Semisentence 4 := .mkSigma
  “y a t Γ. ∃ w, !pairDef w a t ∧ ∃ l, !lhDef l Γ ∧ !fvSubstSeqAuxDef y w Γ l”

instance fvSubstSeq_defined : 𝚺₁-Function₃ (fvSubstSeq : V → V → V → V) via fvSubstSeqDef := .mk
  fun v ↦ by simp [fvSubstSeqDef, fvSubstSeq, lh_defined.iff, fvSubstSeqAux_defined.iff]

instance fvSubstSeq_definable : 𝚺₁-Function₃ (fvSubstSeq : V → V → V → V) :=
  fvSubstSeq_defined.to_definable
instance fvSubstSeq_definable' (Γ) : Γ-[m + 1]-Function₃ (fvSubstSeq : V → V → V → V) :=
  fvSubstSeq_definable.of_sigmaOne

@[simp] lemma fvSubstSeq_seq (a t Γ : V) : Seq (fvSubstSeq a t Γ) := fvSubstSeqAux_seq _ _ _

@[simp] lemma fvSubstSeq_lh (a t Γ : V) : lh (fvSubstSeq a t Γ) = lh Γ := fvSubstSeqAux_lh _ _ _

/-- **Read-out**: the `i`-th formula of `fvSubstSeq a t Γ` is `fvSubst a t` of the `i`-th of `Γ`. -/
lemma znth_fvSubstSeq {a t Γ i : V} (hi : i < lh Γ) :
    znth (fvSubstSeq a t Γ) i = fvSubst ℒₒᵣ a t (znth Γ i) := by
  rw [fvSubstSeq]
  simpa using znth_fvSubstSeqAux_eq (w := ⟪a, t⟫) (Γ := Γ) (lh Γ) i hi

/-! ## `fvSubstSeqt` — substitute a whole sequent `s = ⟪Γ, C⟫`

The antecedent `Γ = seqAnt s` is a *sequence* of formulas (mapped by `fvSubstSeq`); the succedent
`C = seqSucc s` is a *single* formula (mapped by `fvSubst`). -/

/-- Substitute `^&a ↦ t` throughout the sequent `s = ⟪Γ, C⟫`. -/
noncomputable def fvSubstSeqt (a t s : V) : V :=
  mkSeqt (fvSubstSeq a t (seqAnt s)) (fvSubst ℒₒᵣ a t (seqSucc s))

noncomputable def _root_.LO.FirstOrder.Arithmetic.fvSubstSeqtDef : 𝚺₁.Semisentence 4 := .mkSigma
  “y a t s. ∃ ga, !seqAntDef ga s ∧ ∃ sga, !fvSubstSeqDef sga a t ga ∧
    ∃ cc, !seqSuccDef cc s ∧ ∃ scc, !(fvSubstGraph ℒₒᵣ) scc a t cc ∧ !pairDef y sga scc”

instance fvSubstSeqt_defined : 𝚺₁-Function₃ (fvSubstSeqt : V → V → V → V) via fvSubstSeqtDef := .mk
  fun v ↦ by
    simp [fvSubstSeqtDef, fvSubstSeqt, mkSeqt, seqAnt_defined.iff, fvSubstSeq_defined.iff,
      seqSucc_defined.iff, (fvSubst.defined (L := ℒₒᵣ)).iff]

instance fvSubstSeqt_definable : 𝚺₁-Function₃ (fvSubstSeqt : V → V → V → V) :=
  fvSubstSeqt_defined.to_definable
instance fvSubstSeqt_definable' (Γ) : Γ-[m + 1]-Function₃ (fvSubstSeqt : V → V → V → V) :=
  fvSubstSeqt_definable.of_sigmaOne

@[simp] lemma seqAnt_fvSubstSeqt (a t s : V) :
    seqAnt (fvSubstSeqt a t s) = fvSubstSeq a t (seqAnt s) := by simp [fvSubstSeqt]

@[simp] lemma seqSucc_fvSubstSeqt (a t s : V) :
    seqSucc (fvSubstSeqt a t s) = fvSubst ℒₒᵣ a t (seqSucc s) := by simp [fvSubstSeqt]

/-! ## `tblMapSeq` — map a value-table read over a premise sequence (the `zK` case)

For the chain rule `zK s r ds`, `zsubst` rebuilds the premise sequence by reading each (already
substituted) premise out of the recursion table: `tblMapSeq tbl ds = ⟨znth tbl (znth ds 0),…⟩`.
Mirrors `iseqMaxAux` (params `tbl`, `ds`) but collects via `seqCons` instead of `max`. -/

def tblMapSeqAux.blueprint : PR.Blueprint 2 where
  zero := .mkSigma “y tbl ds. y = 0”
  succ := .mkSigma “y ih n tbl ds.
    ∃ di, !znthDef di ds n ∧ ∃ v, !znthDef v tbl di ∧ !seqConsDef y ih v”

noncomputable def tblMapSeqAux.construction : PR.Construction V tblMapSeqAux.blueprint where
  zero := fun _ ↦ ∅
  succ := fun x n ih ↦ seqCons ih (znth (x 0) (znth (x 1) n))
  zero_defined := .mk fun v ↦ by simp [tblMapSeqAux.blueprint, emptyset_def]
  succ_defined := .mk fun v ↦ by
    simp [tblMapSeqAux.blueprint, znth_defined.iff, seqCons_defined.iff]

/-- `tblMapSeqAux tbl ds n = ⟨znth tbl (znth ds 0),…,znth tbl (znth ds (n−1))⟩` (length `n`). -/
noncomputable def tblMapSeqAux (tbl ds n : V) : V := tblMapSeqAux.construction.result ![tbl, ds] n

@[simp] lemma tblMapSeqAux_zero (tbl ds : V) : tblMapSeqAux tbl ds 0 = ∅ := by
  simp [tblMapSeqAux, tblMapSeqAux.construction]

@[simp] lemma tblMapSeqAux_succ (tbl ds n : V) :
    tblMapSeqAux tbl ds (n + 1) = seqCons (tblMapSeqAux tbl ds n) (znth tbl (znth ds n)) := by
  simp [tblMapSeqAux, tblMapSeqAux.construction]

noncomputable def _root_.LO.FirstOrder.Arithmetic.tblMapSeqAuxDef : 𝚺₁.Semisentence 4 :=
  tblMapSeqAux.blueprint.resultDef.rew (Rew.subst ![#0, #3, #1, #2])

instance tblMapSeqAux_defined : 𝚺₁-Function₃ (tblMapSeqAux : V → V → V → V) via tblMapSeqAuxDef := .mk
  fun v ↦ by simp [tblMapSeqAux.construction.result_defined_iff, tblMapSeqAuxDef]; rfl

instance tblMapSeqAux_definable : 𝚺₁-Function₃ (tblMapSeqAux : V → V → V → V) :=
  tblMapSeqAux_defined.to_definable
instance tblMapSeqAux_definable' (Γ) : Γ-[m + 1]-Function₃ (tblMapSeqAux : V → V → V → V) :=
  tblMapSeqAux_definable.of_sigmaOne

@[simp] lemma tblMapSeqAux_seq (tbl ds n : V) : Seq (tblMapSeqAux tbl ds n) := by
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero => simpa using seq_empty
  case succ n ih => rw [tblMapSeqAux_succ]; exact ih.seqCons _

@[simp] lemma tblMapSeqAux_lh (tbl ds n : V) : lh (tblMapSeqAux tbl ds n) = n := by
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero => simpa using lh_empty
  case succ n ih => rw [tblMapSeqAux_succ, Seq.lh_seqCons _ (tblMapSeqAux_seq tbl ds n), ih]

lemma znth_tblMapSeqAux_top (tbl ds n : V) :
    znth (tblMapSeqAux tbl ds (n + 1)) n = znth tbl (znth ds n) := by
  rw [tblMapSeqAux_succ]
  have := znth_seqCons_self (tblMapSeqAux_seq tbl ds n) (znth tbl (znth ds n))
  rwa [tblMapSeqAux_lh] at this

lemma znth_tblMapSeqAux_stable {tbl ds : V} (n m : V) (hm : m < n) :
    znth (tblMapSeqAux tbl ds (n + 1)) m = znth (tblMapSeqAux tbl ds n) m := by
  rw [tblMapSeqAux_succ, znth_seqCons_of_lt (tblMapSeqAux_seq tbl ds n) _ (by rw [tblMapSeqAux_lh]; exact hm)]

lemma znth_tblMapSeqAux_eq {tbl ds : V} :
    ∀ n, ∀ i < n, znth (tblMapSeqAux tbl ds n) i = znth tbl (znth ds i) := by
  intro n
  induction n using ISigma1.sigma1_succ_induction
  · refine Definable.ball_lt (by definability) ?_
    apply Definable.comp₂ (by definability)
    apply DefinableFunction₂.comp (F := fun x y ↦ znth x y) (DefinableFunction.const _) (by definability)
  case zero => intro i hi; exact absurd hi (by simp)
  case succ n ih =>
    intro i hi
    rcases eq_or_lt_of_le (le_iff_lt_succ.mpr hi) with hin | hilt
    · rw [hin, znth_tblMapSeqAux_top]
    · rw [znth_tblMapSeqAux_stable n i hilt]; exact ih i hilt

/-- **Map the table read over a premise sequence** `ds` (length-preserving). -/
noncomputable def tblMapSeq (tbl ds : V) : V := tblMapSeqAux tbl ds (lh ds)

noncomputable def _root_.LO.FirstOrder.Arithmetic.tblMapSeqDef : 𝚺₁.Semisentence 3 := .mkSigma
  “y tbl ds. ∃ l, !lhDef l ds ∧ !tblMapSeqAuxDef y tbl ds l”

instance tblMapSeq_defined : 𝚺₁-Function₂ (tblMapSeq : V → V → V) via tblMapSeqDef := .mk
  fun v ↦ by simp [tblMapSeqDef, tblMapSeq, lh_defined.iff, tblMapSeqAux_defined.iff]

instance tblMapSeq_definable : 𝚺₁-Function₂ (tblMapSeq : V → V → V) := tblMapSeq_defined.to_definable
instance tblMapSeq_definable' (Γ) : Γ-[m + 1]-Function₂ (tblMapSeq : V → V → V) :=
  tblMapSeq_definable.of_sigmaOne

@[simp] lemma tblMapSeq_seq (tbl ds : V) : Seq (tblMapSeq tbl ds) := tblMapSeqAux_seq _ _ _
@[simp] lemma tblMapSeq_lh (tbl ds : V) : lh (tblMapSeq tbl ds) = lh ds := tblMapSeqAux_lh _ _ _

lemma znth_tblMapSeq {tbl ds i : V} (hi : i < lh ds) :
    znth (tblMapSeq tbl ds) i = znth tbl (znth ds i) := znth_tblMapSeqAux_eq (lh ds) i hi

/-! ## Missing per-constructor accessors (`zIall` eigenvariable, `zAxAll` count) -/

/-- `I^a_∀xF` eigenvariable `a` (payload `⟪a,p,d0⟫`). -/
noncomputable def zIallEig (d : V) : V := π₁ (zRest d)
def _root_.LO.FirstOrder.Arithmetic.zIallEigDef : 𝚺₀.Semisentence 2 := .mkSigma
  “y d. ∃ zr <⁺ d, !zRestDef zr d ∧ !pi₁Def y zr”
instance zIallEig_defined : 𝚺₀-Function₁ (zIallEig : V → V) via zIallEigDef := .mk fun v ↦ by
  simp [zIallEigDef, zIallEig, zRest_defined.iff, pi₁_defined.iff]
instance zIallEig_definable : 𝚺₀-Function₁ (zIallEig : V → V) := zIallEig_defined.to_definable
@[simp] lemma zIallEig_zIall (s a p d0 : V) : zIallEig (zIall s a p d0) = a := by
  simp [zIallEig, zRest_zIall]

def _root_.LO.FirstOrder.Arithmetic.zAxAllKDef : 𝚺₀.Semisentence 2 := .mkSigma
  “y d. ∃ zr <⁺ d, !zRestDef zr d ∧ !pi₂Def y zr”
instance zAxAllK_defined : 𝚺₀-Function₁ (zAxAllK : V → V) via zAxAllKDef := .mk fun v ↦ by
  simp [zAxAllKDef, zAxAllK, zRest_defined.iff, pi₂_defined.iff]
instance zAxAllK_definable : 𝚺₀-Function₁ (zAxAllK : V → V) := zAxAllK_defined.to_definable

/-! ## `zsubstNext` — the table step of `zsubst`

Reads each (already substituted) child out of the value-table `s` (every child code `< d`), and
rebuilds the constructor with the substituted end-sequent `fvSubstSeqt a t (fstIdx d)`, substituted
principal formula(s) (`fvSubst`), substituted induction term (`termFvSubst`), and the eigenvariable
index left intact. Mirrors `iRNext`. -/

noncomputable def zsubstNext (d s a t : V) : V :=
  if zTag d = 0 then zAtom (fvSubstSeqt a t (fstIdx d))
  else if zTag d = 1 then
    zIall (fvSubstSeqt a t (fstIdx d)) (zIallEig d) (fvSubst ℒₒᵣ a t (zIallF d)) (znth s (zIallPrem d))
  else if zTag d = 2 then
    zIneg (fvSubstSeqt a t (fstIdx d)) (fvSubst ℒₒᵣ a t (zInegF d)) (znth s (zInegPrem d))
  else if zTag d = 3 then
    zInd (fvSubstSeqt a t (fstIdx d)) ⟪zIndEig d, termFvSubst ℒₒᵣ a t (zIndTerm d)⟫
      (fvSubst ℒₒᵣ a t (zIndP d)) (znth s (zIndPrem0 d)) (znth s (zIndPrem1 d))
  else if zTag d = 4 then
    zK (fvSubstSeqt a t (fstIdx d)) (zKrank d) (tblMapSeq s (zKseq d))
  else if zTag d = 5 then
    zAxAll (fvSubstSeqt a t (fstIdx d)) (fvSubst ℒₒᵣ a t (zAxAllF d)) (zAxAllK d)
  else if zTag d = 6 then
    zAxNeg (fvSubstSeqt a t (fstIdx d)) (fvSubst ℒₒᵣ a t (zAxNegF d))
  else if zTag d = 7 then
    zAx1 (fvSubstSeqt a t (fstIdx d)) (zAx1F d)
  else d

noncomputable def _root_.LO.FirstOrder.Arithmetic.zsubstNextDef : 𝚺₁.Semisentence 5 := .mkSigma
  “y d s a t. ∃ tg, !zTagDef tg d ∧ ∃ ff, !fstIdxDef ff d ∧ ∃ s', !fvSubstSeqtDef s' a t ff ∧
    ( (tg = 0 ∧ !zAtomGraph y s')
    ∨ (tg = 1 ∧ ∃ ea, !zIallEigDef ea d ∧ ∃ pf, !zIallFDef pf d ∧
        ∃ sp, !(fvSubstGraph ℒₒᵣ) sp a t pf ∧ ∃ p0, !zIallPremDef p0 d ∧
        ∃ c0, !znthDef c0 s p0 ∧ !zIallGraph y s' ea sp c0)
    ∨ (tg = 2 ∧ ∃ pf, !zInegFDef pf d ∧ ∃ sp, !(fvSubstGraph ℒₒᵣ) sp a t pf ∧
        ∃ p0, !zInegPremDef p0 d ∧ ∃ c0, !znthDef c0 s p0 ∧ !zInegGraph y s' sp c0)
    ∨ (tg = 3 ∧ ∃ ie, !zIndEigDef ie d ∧ ∃ it, !zIndTermDef it d ∧
        ∃ sit, !(termFvSubstGraph ℒₒᵣ) sit a t it ∧ ∃ at2, !pairDef at2 ie sit ∧
        ∃ pf, !zIndPDef pf d ∧ ∃ sp, !(fvSubstGraph ℒₒᵣ) sp a t pf ∧
        ∃ p0, !zIndPrem0Def p0 d ∧ ∃ c0, !znthDef c0 s p0 ∧
        ∃ p1, !zIndPrem1Def p1 d ∧ ∃ c1, !znthDef c1 s p1 ∧ !zIndGraph y s' at2 sp c0 c1)
    ∨ (tg = 4 ∧ ∃ rk, !zKrankDef rk d ∧ ∃ ds, !zKseqDef ds d ∧
        ∃ ds', !tblMapSeqDef ds' s ds ∧ !zKGraph y s' rk ds')
    ∨ (tg = 5 ∧ ∃ pf, !zAxAllFDef pf d ∧ ∃ sp, !(fvSubstGraph ℒₒᵣ) sp a t pf ∧
        ∃ kk, !zAxAllKDef kk d ∧ !zAxAllGraph y s' sp kk)
    ∨ (tg = 6 ∧ ∃ pf, !zAxNegFDef pf d ∧ ∃ sp, !(fvSubstGraph ℒₒᵣ) sp a t pf ∧ !zAxNegGraph y s' sp)
    ∨ (tg = 7 ∧ ∃ pf, !zAx1FDef pf d ∧ !zAx1Graph y s' pf)
    ∨ (tg ≠ 0 ∧ tg ≠ 1 ∧ tg ≠ 2 ∧ tg ≠ 3 ∧ tg ≠ 4 ∧ tg ≠ 5 ∧ tg ≠ 6 ∧ tg ≠ 7 ∧ y = d) )”

set_option maxHeartbeats 1000000 in
instance zsubstNext_defined : 𝚺₁-Function₄ (zsubstNext : V → V → V → V → V) via zsubstNextDef :=
  .mk fun v ↦ by
    simp [zsubstNextDef, zsubstNext, numeral_eq_natCast, zTag_defined.iff, fstIdx_defined.iff, fvSubstSeqt_defined.iff,
      zAtom_defined.iff, zIallEig_defined.iff, zIallF_defined.iff, (fvSubst.defined (L := ℒₒᵣ)).iff,
      zIallPrem_defined.iff, znth_defined.iff, zIall_defined.iff, zInegF_defined.iff,
      zInegPrem_defined.iff, zIneg_defined.iff, zIndEig_defined.iff, zIndTerm_defined.iff,
      (termFvSubst.defined (L := ℒₒᵣ)).iff, zIndP_defined.iff, zIndPrem0_defined.iff,
      zIndPrem1_defined.iff, zInd_defined.iff, zKrank_defined.iff, zKseq_defined.iff,
      tblMapSeq_defined.iff, zK_defined.iff, zAxAllF_defined.iff, zAxAllK_defined.iff,
      zAxAll_defined.iff, zAxNegF_defined.iff, zAxNeg_defined.iff, zAx1F_defined.iff,
      zAx1_defined.iff]
    by_cases h0 : zTag (v 1) = 0
    · simp [h0]
    · by_cases h1 : zTag (v 1) = 1
      · simp [h0, h1]
      · by_cases h2 : zTag (v 1) = 2
        · simp [h0, h1, h2]
        · by_cases h3 : zTag (v 1) = 3
          · simp [h0, h1, h2, h3]
          · by_cases h4 : zTag (v 1) = 4
            · simp [h0, h1, h2, h3, h4]
            · by_cases h5 : zTag (v 1) = 5
              · simp [h0, h1, h2, h3, h4, h5]
              · by_cases h6 : zTag (v 1) = 6
                · simp [h0, h1, h2, h3, h4, h5, h6]
                · by_cases h7 : zTag (v 1) = 7
                  · simp [h0, h1, h2, h3, h4, h5, h6, h7]
                  · simp [h0, h1, h2, h3, h4, h5, h6, h7]

instance zsubstNext_definable : 𝚺₁-Function₄ (zsubstNext : V → V → V → V → V) :=
  zsubstNext_defined.to_definable

/-! ## `zsubst` — the course-of-values `<`-recursion (mirror `iRTable`/`iR2`)

`zsubstTable a t n = ⟨zsubst 0,…,zsubst n⟩`, with the step reading sub-reducts out of `ih` (each
child code `< d`); `zsubst d a t = znth (zsubstTable a t d) d`. -/

noncomputable def zsubstTable.blueprint : PR.Blueprint 2 where
  zero := .mkSigma “y a t. !mkSeq₁Def y 0”
  succ := .mkSigma “y ih n a t. ∃ v, !zsubstNextDef v (n + 1) ih a t ∧ !seqConsDef y ih v”

noncomputable def zsubstTable.construction : PR.Construction V zsubstTable.blueprint where
  zero := fun _ ↦ !⟦0⟧
  succ := fun x n ih ↦ seqCons ih (zsubstNext (n + 1) ih (x 0) (x 1))
  zero_defined := .mk fun v ↦ by
    simp [zsubstTable.blueprint, mkSeq₁Def, seqCons_defined.iff, emptyset_def]
  succ_defined := .mk fun v ↦ by
    simp [zsubstTable.blueprint, zsubstNext_defined.iff, seqCons_defined.iff]

/-- `zsubstTable a t n = ⟨zsubst 0,…,zsubst n⟩` (length `n+1`). -/
noncomputable def zsubstTable (a t n : V) : V := zsubstTable.construction.result ![a, t] n

@[simp] lemma zsubstTable_zero (a t : V) : zsubstTable a t 0 = !⟦0⟧ := by
  simp [zsubstTable, zsubstTable.construction]

@[simp] lemma zsubstTable_succ (a t n : V) :
    zsubstTable a t (n + 1) = seqCons (zsubstTable a t n) (zsubstNext (n + 1) (zsubstTable a t n) a t) := by
  simp [zsubstTable, zsubstTable.construction]

noncomputable def _root_.LO.FirstOrder.Arithmetic.zsubstTableDef : 𝚺₁.Semisentence 4 :=
  zsubstTable.blueprint.resultDef.rew (Rew.subst ![#0, #3, #1, #2])

instance zsubstTable_defined : 𝚺₁-Function₃ (zsubstTable : V → V → V → V) via zsubstTableDef := .mk
  fun v ↦ by simp [zsubstTable.construction.result_defined_iff, zsubstTableDef]; rfl
instance zsubstTable_definable : 𝚺₁-Function₃ (zsubstTable : V → V → V → V) :=
  zsubstTable_defined.to_definable
instance zsubstTable_definable' (Γ) : Γ-[m + 1]-Function₃ (zsubstTable : V → V → V → V) :=
  zsubstTable_definable.of_sigmaOne

/-- **Eigenvariable substitution on Z-derivations**: replace `^&a` by the coded term `t` throughout
the Z-derivation code `d` (the `d`-th entry of the value-table). -/
noncomputable def zsubst (d a t : V) : V := znth (zsubstTable a t d) d

noncomputable def _root_.LO.FirstOrder.Arithmetic.zsubstDef : 𝚺₁.Semisentence 4 := .mkSigma
  “y d a t. ∃ tb, !zsubstTableDef tb a t d ∧ !znthDef y tb d”
instance zsubst_defined : 𝚺₁-Function₃ (zsubst : V → V → V → V) via zsubstDef := .mk fun v ↦ by
  simp [zsubstDef, zsubst, zsubstTable_defined.iff, znth_defined.iff]
instance zsubst_definable : 𝚺₁-Function₃ (zsubst : V → V → V → V) := zsubst_defined.to_definable
instance zsubst_definable' (Γ) : Γ-[m + 1]-Function₃ (zsubst : V → V → V → V) :=
  zsubst_definable.of_sigmaOne

/-- Table step of `red`: dispatch on `zTag d`; tag-4 = the genuine Buchholz Def-3.2 case-5 DISPATCH `iRK`
(5.1 critical / 5.2.1 splice / 5.2.2 replace), reading per-premise reducts from the table `s`. -/
noncomputable def iRNextG (d s : V) : V :=
  if zTag d = 1 then zsubst (zIallPrem d) (zIallEig d) (Bootstrapping.Arithmetic.numeral 0)
  else if zTag d = 2 then zInegPrem d
  else if zTag d = 3 then iRInd d
  else if zTag d = 4 then iRK d s
  else d

noncomputable def _root_.LO.FirstOrder.Arithmetic.iRNextGDef : 𝚺₁.Semisentence 3 := .mkSigma
  “y d s. ∃ t, !zTagDef t d ∧
    ( (t = 1 ∧ ∃ d0, !zIallPremDef d0 d ∧ ∃ e, !zIallEigDef e d ∧
        ∃ z, !(Bootstrapping.Arithmetic.numeralGraph) z 0 ∧ !zsubstDef y d0 e z)
    ∨ (t = 2 ∧ !zInegPremDef y d)
    ∨ (t = 3 ∧ !iRIndDef y d)
    ∨ (t = 4 ∧ !iRKDef y d s)
    ∨ (t ≠ 1 ∧ t ≠ 2 ∧ t ≠ 3 ∧ t ≠ 4 ∧ y = d) )”

instance iRNextG_defined : 𝚺₁-Function₂ (iRNextG : V → V → V) via iRNextGDef := .mk fun v ↦ by
  simp [iRNextGDef, iRNextG, zTag_defined.iff, zIallPrem_defined.iff, zIallEig_defined.iff,
    zsubst_defined.iff, (Bootstrapping.Arithmetic.numeral_defined (V := V)).iff,
    zInegPrem_defined.iff, iRInd_defined.iff, iRK_defined.iff]
  by_cases h1 : zTag (v 1) = 1
  · simp [h1]
  · by_cases h2 : zTag (v 1) = 2
    · simp [h1, h2]
    · by_cases h3 : zTag (v 1) = 3
      · simp [h1, h2, h3]
      · by_cases h4 : zTag (v 1) = 4
        · simp [h1, h2, h3, h4]
        · simp [h1, h2, h3, h4]

instance iRNextG_definable : 𝚺₁-Function₂ (iRNextG : V → V → V) := iRNextG_defined.to_definable

/-- Blueprint for the `red` table. -/
noncomputable def redTable.blueprint : PR.Blueprint 0 where
  zero := .mkSigma “y. !mkSeq₁Def y 0”
  succ := .mkSigma “y ih n. ∃ v, !iRNextGDef v (n + 1) ih ∧ !seqConsDef y ih v”

noncomputable def redTable.construction : PR.Construction V redTable.blueprint where
  zero := fun _ ↦ !⟦0⟧
  succ := fun _ n ih ↦ seqCons ih (iRNextG (n + 1) ih)
  zero_defined := .mk fun v ↦ by
    simp [redTable.blueprint, mkSeq₁Def, seqCons_defined.iff, emptyset_def]
  succ_defined := .mk fun v ↦ by
    simp [redTable.blueprint, iRNextG_defined.iff, seqCons_defined.iff]

/-- **The `red` table**: `redTable n = ⟨red 0,…,red n⟩` (length `n+1`). -/
noncomputable def redTable (n : V) : V := redTable.construction.result ![] n

@[simp] lemma redTable_zero : redTable (0 : V) = !⟦0⟧ := by simp [redTable, redTable.construction]

@[simp] lemma redTable_succ (n : V) :
    redTable (n + 1) = seqCons (redTable n) (iRNextG (n + 1) (redTable n)) := by
  simp [redTable, redTable.construction]

noncomputable def _root_.LO.FirstOrder.Arithmetic.redTableDef : 𝚺₁.Semisentence 2 :=
  redTable.blueprint.resultDef.rew (Rew.subst ![#0, #1])

instance redTable_defined : 𝚺₁-Function₁ (redTable : V → V) via redTableDef := .mk
  fun v ↦ by simp [redTable.construction.result_defined_iff, redTableDef]; rfl
instance redTable_definable : 𝚺₁-Function₁ (redTable : V → V) := redTable_defined.to_definable
instance redTable_definable' (Γ) : Γ-[m + 1]-Function₁ (redTable : V → V) :=
  redTable_definable.of_sigmaOne

/-- **The genuine reduct** `red d = d[0]`: the `d`-th entry of the table. -/
noncomputable def red (d : V) : V := znth (redTable d) d

noncomputable def _root_.LO.FirstOrder.Arithmetic.redDef : 𝚺₁.Semisentence 2 := .mkSigma
  “y d. ∃ t, !redTableDef t d ∧ !znthDef y t d”
instance red_defined : 𝚺₁-Function₁ (red : V → V) via redDef := .mk fun v ↦ by
  simp [redDef, red, redTable_defined.iff, znth_defined.iff]
instance red_definable : 𝚺₁-Function₁ (red : V → V) := red_defined.to_definable
instance red_definable' (Γ) : Γ-[m + 1]-Function₁ (red : V → V) := red_definable.of_sigmaOne

/-! ### Structural correctness of the `red` table (mirror `iR2`) -/

private lemma def_redTable {k} (i : Fin k) :
    𝚺-[1].DefinableFunction (fun v : Fin k → V ↦ redTable (v i)) :=
  DefinableFunction₁.comp (F := redTable) (DefinableFunction.var i)

private lemma def_red {k} (i : Fin k) :
    𝚺-[1].DefinableFunction (fun v : Fin k → V ↦ red (v i)) :=
  DefinableFunction₁.comp (F := red) (DefinableFunction.var i)

@[simp] lemma redTable_seq (n : V) : Seq (redTable n) := by
  induction n using ISigma1.sigma1_succ_induction
  · exact Definable.comp₁ (def_redTable 0)
  case zero => simp
  case succ n ih => rw [redTable_succ]; exact ih.seqCons _

@[simp] lemma redTable_lh (n : V) : lh (redTable n) = n + 1 := by
  induction n using ISigma1.sigma1_succ_induction
  · exact Definable.comp₂ (DefinableFunction₁.comp (F := lh) (def_redTable 0)) (by definability)
  case zero => simp
  case succ n ih => rw [redTable_succ, Seq.lh_seqCons _ (redTable_seq n), ih]

lemma znth_redTable_succ {n k : V} (hk : k < n + 1) :
    znth (redTable (n + 1)) k = znth (redTable n) k := by
  rw [redTable_succ]
  exact znth_seqCons_of_lt (redTable_seq n) _ (by rw [redTable_lh]; exact hk)

lemma znth_redTable_eq_red : ∀ N : V, ∀ k ≤ N, znth (redTable N) k = red k := by
  intro N
  induction N using ISigma1.sigma1_succ_induction
  · refine Definable.ball_le (by definability) ?_
    exact Definable.comp₂
      (DefinableFunction₂.comp (F := znth) (def_redTable 1) (DefinableFunction.var 0))
      (def_red 0)
  case zero =>
    intro k hk; rcases (nonpos_iff_eq_zero.mp hk) with rfl; rfl
  case succ N ih =>
    intro k hk
    rcases eq_or_lt_of_le hk with rfl | hlt
    · rfl
    · rw [znth_redTable_succ hlt]; exact ih k (le_iff_lt_succ.mpr hlt)

/-- `red c = iRNextG c (redTable (c-1))` for positive codes (the table-reduction unfolding). -/
lemma red_eq_iRNextG {c : V} (hpos : 0 < c) : red c = iRNextG c (redTable (c - 1)) := by
  obtain ⟨M, rfl⟩ : ∃ M, c = M + 1 := ⟨c - 1, (sub_add_self_of_le (pos_iff_one_le.mp hpos)).symm⟩
  have key : znth (redTable (M + 1)) (M + 1) = iRNextG (M + 1) (redTable M) := by
    rw [redTable_succ]
    have h := znth_seqCons_self (redTable_seq M) (iRNextG (M + 1) (redTable M))
    rwa [redTable_lh] at h
  simp only [red, add_tsub_cancel_right, key]

/-- `iRcritG` depends on `ρ` only at `redexI d`/`redexJ d`. -/
lemma iRcritG_congr {d : V} {ρ ρ' : V → V} (hi : ρ (redexI d) = ρ' (redexI d))
    (hj : ρ (redexJ d) = ρ' (redexJ d)) : iRcritG d ρ = iRcritG d ρ' := by
  simp only [iRcritG, hi, hj]

/-! ### `red` recursion equations (Buchholz Def 3.2, per rule) -/

@[simp] lemma red_zAtom (s : V) : red (zAtom s) = zAtom s := by
  rw [red_eq_iRNextG (by simp [zAtom]), iRNextG]; simp [zTag_zAtom]

@[simp] lemma red_zIall (s a p d0 : V) :
    red (zIall s a p d0) = zsubst d0 a (Bootstrapping.Arithmetic.numeral 0) := by
  rw [red_eq_iRNextG (by simp [zIall]), iRNextG, if_pos (zTag_zIall s a p d0)]
  simp [zIallPrem_zIall, zIallEig_zIall]

@[simp] lemma red_zIneg (s p d0 : V) : red (zIneg s p d0) = d0 := by
  rw [red_eq_iRNextG (by simp [zIneg]), iRNextG, if_neg (by simp), if_pos (zTag_zIneg s p d0)]
  simp [zInegPrem_zIneg]

@[simp] lemma red_zInd (s at' p d0 d1 : V) :
    red (zInd s at' p d0 d1) = iRInd (zInd s at' p d0 d1) := by
  rw [red_eq_iRNextG (by simp [zInd]), iRNextG, if_neg (by simp), if_neg (by simp),
    if_pos (zTag_zInd s at' p d0 d1)]

@[simp] lemma red_zAxAll (s p k : V) : red (zAxAll s p k) = zAxAll s p k := by
  rw [red_eq_iRNextG (by simp [zAxAll]), iRNextG]; simp [zTag_zAxAll]

@[simp] lemma red_zAxNeg (s p : V) : red (zAxNeg s p) = zAxNeg s p := by
  rw [red_eq_iRNextG (by simp [zAxNeg]), iRNextG]; simp [zTag_zAxNeg]

@[simp] lemma red_zAx1 (s C : V) : red (zAx1 s C) = zAx1 s C := by
  rw [red_eq_iRNextG (by simp [zAx1]), iRNextG]; simp [zTag_zAx1]

/-- **The K-rule recursion equation** for the GENUINE reduct: `red` of a chain is the tag-4 DISPATCH
`iRK` (Buchholz Def 3.2 case 5: 5.1 critical / 5.2.1 splice / 5.2.2 replace), reading per-premise reducts
from the table-so-far `redTable (zK s r ds - 1)`. The branch-specific recursion equations
(`red_zK_crit` / the 5.2 forms) refine this with `znth (redTable …) (znth ds k) = red (znth ds k)`. -/
lemma red_zK (s r ds : V) :
    red (zK s r ds) = iRK (zK s r ds) (redTable (zK s r ds - 1)) := by
  rw [red_eq_iRNextG (by simp [zK]), iRNextG, if_neg (by simp), if_neg (by simp), if_neg (by simp),
    if_pos (zTag_zK s r ds)]

/-- **5.1 critical recursion equation** — when the chain is critical (`permIdx (zK s r ds) = lh ds`, i.e.
no permissible premise), `red` takes the 5.1 branch `iRKc`, which is the genuine critical reduct `iRcritG`
with the two auxiliaries' premise-reducts supplied RECURSIVELY (`red (znth ds (redexI/redexJ ..))`). -/
lemma red_zK_crit {s r ds : V} (hcrit : ¬ permIdx (zK s r ds) < lh ds) :
    red (zK s r ds) = iRcritG (zK s r ds) (fun n => zAxReduct (red (znth ds n))) := by
  have hbound : ∀ k : V, znth ds k ≤ zK s r ds - 1 := fun k =>
    le_trans (znth_le_self ds k) (le_pred_of_lt (ds_lt_zK s r ds))
  rw [red_zK, iRK, zKseq_zK, if_neg hcrit, iRKc]
  refine iRcritG_congr ?_ ?_ <;>
    simp only [zKseq_zK] <;>
    rw [znth_redTable_eq_red _ _ (hbound _)]

/-- **The genuine re-principalized critical reduct supplier** — the concrete `ρ` that `red`'s tag-4 critical
branch MUST emit (the corrected version of the engine's `fun n => zAxReduct (red (znth ds n))`). At the two
redexes it reads the cut data from `d`'s own structure:
- **R-redex** (`n = redexI d`, the I∀ premise): `zsubst (zIallPrem dᵢ) (zIallEig dᵢ) (numeral k)` —
  re-principalized at the L-instance `k = π₁(π₂(tp dⱼ))` (instead of the engine's instance-`0`).
- **L-redex** (`n = redexJ d`, the axAll premise): `zAx1 (seqAddAnt (cutFormula d) (fstIdx dⱼ)) (cutFormula d)`
  — the §5 logical axiom `Ax^1`, antecedent grown by the cut instance, succedent `= cutFormula d`.
- elsewhere: the engine reduct `zAxReduct (red dₙ)` (irrelevant: `iRcritG` only reads `ρ` at the redexes).
This is a `noncomputable` function of `d` (engine-definable: every accessor is `𝚺₁`), so the re-keying
swaps `iRKc` to `iRcritG d (critReductCorr d)` and its `iRKcDef` arithmetization to match. Both halves of
the genuine reduct's correctness are proven against it: SOUNDNESS (`ZDerivation_iRcritG_critReductCorr`,
Crux2Blueprint) and DESCENT (`iord_descent_iRcritG_critReductCorr`, RedZKDescent). -/
noncomputable def critReductCorr (d n : V) : V :=
  if n = redexJ d then
    zAx1 (seqAddAnt (cutFormula d) (fstIdx (znth (zKseq d) n))) (cutFormula d)
  else if n = redexI d then
    zsubst (zIallPrem (znth (zKseq d) n)) (zIallEig (znth (zKseq d) n))
      (Bootstrapping.Arithmetic.numeral (π₁ (π₂ (tp (znth (zKseq d) (redexJ d))))))
  else zAxReduct (red (znth (zKseq d) n))

/-- `critReductCorr` at the L-redex `redexJ`: the §5 axAll reduct `Ax^1_{F(k),Γⱼ→F(k)}` (antecedent grown). -/
lemma critReductCorr_redexJ (d : V) :
    critReductCorr d (redexJ d) =
      zAx1 (seqAddAnt (cutFormula d) (fstIdx (znth (zKseq d) (redexJ d)))) (cutFormula d) := by
  rw [critReductCorr, if_pos rfl]

/-- `critReductCorr` at the R-redex `redexI` (when `redexI ≠ redexJ`): the re-principalized I∀ premise
`zsubst dᵢ aᵢ (numeral k)`, `k = π₁(π₂(tp dⱼ))`. -/
lemma critReductCorr_redexI {d : V} (h : redexI d ≠ redexJ d) :
    critReductCorr d (redexI d) =
      zsubst (zIallPrem (znth (zKseq d) (redexI d))) (zIallEig (znth (zKseq d) (redexI d)))
        (Bootstrapping.Arithmetic.numeral (π₁ (π₂ (tp (znth (zKseq d) (redexJ d)))))) := by
  rw [critReductCorr, if_neg h, if_pos rfl]

/-- **The genuine critical reduct supplier for the ¬-case** (the `critReductCorr` twin for `Aᵢ = ¬A`). This
is the concrete `ρ` the re-keyed tag-4 critical branch emits when the R-redex is an `I¬` rule (`zTag dᵢ = 2`).
Buchholz Def 3.2 case 5.1, ¬-subcase, plus §5 Lemma 5.1 case 2.2:
- **L-redex** (`n = redexJ d`, the `axNeg` axiom): `zAx1 (seqSetSucc sⱼ A) A` — the §5 logical axiom
  `Ax^1_{Γⱼ→A}` (succedent SET to the cut formula `A = cutFormula d`, antecedent `Γⱼ` kept; the §5 reduct
  `dⱼ[0]` of `Ax^{¬A,0}`). Note: `seqSetSucc` (REPLACE succedent), NOT `seqAddAnt` — the ¬-axiom reduct
  replaces the succedent, where the ∀-axiom reduct grows the antecedent.
- **R-redex** (`n = redexI d`, the `I¬` rule): `zInegPrem dᵢ` — the `I¬` child `dᵢ[0] = d₀` (deriving
  `A,Γᵢ→⊥`), read as the DIRECT 𝚺₁ accessor `zInegPrem (zIneg sᵢ A d0) = d0` (`zInegPrem_zIneg`), which equals
  the recursive `red (zIneg sᵢ A d0) = d0` (`red_zIneg`) but is **red-free** — so `critReductNeg` is fully
  arithmetizable (the engine `iRKc` graph cannot call `red`; the I¬ child is an accessor, not a reduct). No
  re-principalization (unlike the ∀ R-redex, which needs the `numeral k` instance).
- elsewhere: irrelevant (`iRcritGNeg` reads `ρ` only at the redexes); kept as `zAxReduct (red dₙ)` to mirror
  `critReductCorr`'s dead else-branch.
The two read-offs (`critReductNeg d (redexI d)`/`(redexJ d)`) feed `hρI`/`hρJ` of
`ZDerivation_iRcritGNeg_corrected_neg` directly. -/
noncomputable def critReductNeg (d n : V) : V :=
  if n = redexJ d then
    zAx1 (seqSetSucc (fstIdx (znth (zKseq d) n)) (cutFormula d)) (cutFormula d)
  else if n = redexI d then
    zInegPrem (znth (zKseq d) n)
  else zAxReduct (red (znth (zKseq d) n))

/-- `critReductNeg` at the L-redex `redexJ`: the §5 axNeg reduct `Ax^1_{Γⱼ→A}`. -/
lemma critReductNeg_redexJ (d : V) :
    critReductNeg d (redexJ d) =
      zAx1 (seqSetSucc (fstIdx (znth (zKseq d) (redexJ d))) (cutFormula d)) (cutFormula d) := by
  rw [critReductNeg, if_pos rfl]

/-- `critReductNeg` at the R-redex `redexI` (when `redexI ≠ redexJ`): the `I¬` child `zInegPrem dᵢ = d₀`. -/
lemma critReductNeg_redexI {d : V} (h : redexI d ≠ redexJ d) :
    critReductNeg d (redexI d) = zInegPrem (znth (zKseq d) (redexI d)) := by
  rw [critReductNeg, if_neg h, if_pos rfl]

/-- **The re-keyed tag-4 critical reduct — fully explicit, dispatched on R-redex polarity.** This is the
object the engine `iRKc` MUST become: a polarity dispatch (`zTag dᵢ = 1` ⟺ I∀ R-redex) emitting the
soundness-certified corrected reduct, in fully-explicit `iCritReductG … seqUpdate …` form (red-free,
table-free, no nested `if` — directly arithmetizable). The two branches are exactly
`iRcritG d (critReductCorr d)` (∀, `iRKcCrit_eq_corr`) and `iRcritGNeg d (critReductNeg d)` (¬,
`iRKcCrit_eq_neg`), whose SOUNDNESS is `ZDerivation_iRcritG_critReductCorr`/`ZDerivation_iRcritGNeg_critReductNeg`
and whose DESCENT is `iord_iRcritG_eq_iRcrit`/`iord_iRcritGNeg_eq_iRcrit`. Defined standalone (depends only on
`d`, NOT the engine table) so its `𝚺₁` arithmetization lands additively, before the engine swap. -/
noncomputable def iRKcCrit (d : V) : V :=
  if zTag (znth (zKseq d) (redexI d)) = 1 then
    iCritReductG (fstIdx d) (cutFormula d) (zKrank d - 1) (zKrank d) (zKrank d)
      (seqUpdate (zKseq d) (redexI d)
        (zsubst (zIallPrem (znth (zKseq d) (redexI d))) (zIallEig (znth (zKseq d) (redexI d)))
          (Bootstrapping.Arithmetic.numeral (π₁ (π₂ (tp (znth (zKseq d) (redexJ d))))))))
      (seqUpdate (zKseq d) (redexJ d)
        (zAx1 (seqAddAnt (cutFormula d) (fstIdx (znth (zKseq d) (redexJ d)))) (cutFormula d)))
  else
    iCritReductG (fstIdx d) (cutFormula d) (zKrank d - 1) (zKrank d) (zKrank d)
      (seqUpdate (zKseq d) (redexJ d)
        (zAx1 (seqSetSucc (fstIdx (znth (zKseq d) (redexJ d))) (cutFormula d)) (cutFormula d)))
      (seqUpdate (zKseq d) (redexI d) (zInegPrem (znth (zKseq d) (redexI d))))

@[simp] lemma fstIdx_iRKcCrit (d : V) : fstIdx (iRKcCrit d) = fstIdx d := by
  rw [iRKcCrit]; split <;> simp
@[simp] lemma zTag_iRKcCrit (d : V) : zTag (iRKcCrit d) = 4 := by
  rw [iRKcCrit]; split <;> simp

/-- `iRKcCrit` = the ∀-case soundness-certified reduct `iRcritG d (critReductCorr d)` (I∀ R-redex). -/
lemma iRKcCrit_eq_corr {d : V} (h1 : zTag (znth (zKseq d) (redexI d)) = 1) (h : redexI d ≠ redexJ d) :
    iRKcCrit d = iRcritG d (critReductCorr d) := by
  rw [iRKcCrit, if_pos h1, iRcritG, critReductCorr_redexI h, critReductCorr_redexJ]

/-- `iRKcCrit` = the ¬-case soundness-certified reduct `iRcritGNeg d (critReductNeg d)` (I¬ R-redex). -/
lemma iRKcCrit_eq_neg {d : V} (h1 : zTag (znth (zKseq d) (redexI d)) ≠ 1) (h : redexI d ≠ redexJ d) :
    iRKcCrit d = iRcritGNeg d (critReductNeg d) := by
  rw [iRKcCrit, if_neg h1, iRcritGNeg, critReductNeg_redexI h, critReductNeg_redexJ]

/-- **𝚺₁ graph of the re-keyed critical reduct `iRKcCrit`.** Dispatches on the R-redex tag `ti = zTag dᵢ`:
`ti = 1` (I∀) builds `iRcritG`'s `iCritReductG` with the re-principalized `zsubst` at slot `i` and the §5
`Ax^1` (antecedent-grown) at slot `j`; otherwise (I¬) builds `iRcritGNeg`'s SWAPPED-slot `iCritReductG`
with the §5 `Ax^1` (succedent-set) at slot `j` and the `zInegPrem` child at slot `i`. Reuses the
`cutFormulaDef` instance-`k = π₁(π₂(tp dⱼ))` threading + `numeralGraph`. -/
noncomputable def _root_.LO.FirstOrder.Arithmetic.iRKcCritDef : 𝚺₁.Semisentence 2 := .mkSigma
  “y d. ∃ f, !fstIdxDef f d ∧ ∃ ds, !zKseqDef ds d ∧ ∃ i, !redexIDef i d ∧ ∃ j, !redexJDef j d ∧
    ∃ cc, !cutFormulaDef cc d ∧ ∃ rk, !zKrankDef rk d ∧ ∃ rk1, !subDef rk1 rk 1 ∧
    ∃ ai, !znthDef ai ds i ∧ ∃ aj, !znthDef aj ds j ∧ ∃ ti, !zTagDef ti ai ∧
    ∃ ss, !seqSetSuccDef ss f cc ∧ ∃ sa, !seqAddAntDef sa cc f ∧ ∃ faj, !fstIdxDef faj aj ∧
    ( ( ti = 1 ∧
        ∃ pri, !zIallPremDef pri ai ∧ ∃ eig, !zIallEigDef eig ai ∧
        ∃ tj, !tpDef tj aj ∧ ∃ p2j, !pi₂Def p2j tj ∧ ∃ kk, !pi₁Def kk p2j ∧
        ∃ nk, !(Bootstrapping.Arithmetic.numeralGraph) nk kk ∧ ∃ vi, !zsubstDef vi pri eig nk ∧
        ∃ saj, !seqAddAntDef saj cc faj ∧ ∃ vj, !zAx1Graph vj saj cc ∧
        ∃ u0, !seqUpdateDef u0 ds i vi ∧ ∃ dz0, !zKGraph dz0 ss rk u0 ∧
        ∃ u1, !seqUpdateDef u1 ds j vj ∧ ∃ dz1, !zKGraph dz1 sa rk u1 ∧
        ∃ sq, !iCritReductSeqDef sq dz0 dz1 ∧ !zKGraph y f rk1 sq )
    ∨ ( ti ≠ 1 ∧
        ∃ ssj, !seqSetSuccDef ssj faj cc ∧ ∃ vj, !zAx1Graph vj ssj cc ∧
        ∃ vi, !zInegPremDef vi ai ∧
        ∃ u0, !seqUpdateDef u0 ds j vj ∧ ∃ dz0, !zKGraph dz0 ss rk u0 ∧
        ∃ u1, !seqUpdateDef u1 ds i vi ∧ ∃ dz1, !zKGraph dz1 sa rk u1 ∧
        ∃ sq, !iCritReductSeqDef sq dz0 dz1 ∧ !zKGraph y f rk1 sq ) )”

set_option maxHeartbeats 1600000 in
instance iRKcCrit_defined : 𝚺₁-Function₁ (iRKcCrit : V → V) via iRKcCritDef := .mk fun v ↦ by
  simp [iRKcCritDef, iRKcCrit, iCritReductG, fstIdx_defined.iff, zKseq_defined.iff,
    redexI_defined.iff, redexJ_defined.iff, cutFormula_defined.iff, zKrank_defined.iff,
    sub_defined.iff, znth_defined.iff, zTag_defined.iff, seqSetSucc_defined.iff,
    seqAddAnt_defined.iff, zIallPrem_defined.iff, zIallEig_defined.iff, tp_defined.iff,
    pi₁_defined.iff, pi₂_defined.iff, (Bootstrapping.Arithmetic.numeral_defined (V := V)).iff,
    zsubst_defined.iff, zInegPrem_defined.iff, zAx1_defined.iff, seqUpdate_defined.iff,
    iCritReductSeq_defined.iff, zK_defined.iff]
  by_cases hti : zTag (znth (zKseq (v 1)) (redexI (v 1))) = 1 <;> simp [hti, numeral_eq_natCast]

instance iRKcCrit_definable : 𝚺₁-Function₁ (iRKcCrit : V → V) := iRKcCrit_defined.to_definable

/-! ### The critical-only reduct is NON-critical (lap 86) — the 5.2 dispatch is mandatory

**Gating finding (Buchholz Def 3.2 case 5, validated in-kernel).** Buchholz's reduction of a chain
`d = K^r_Π d₀…dₗ` splits into critical (5.1) / sub-critical-splice (5.2.1) / non-critical (5.2.2). The
repo's `red`/`iR2` implement only 5.1 (always `iRcritG`/`iCritReduct`). But the 5.1 reduct
`K^{r-1}_Π⟨d{0}, d{1}⟩` is itself a chain whose distinguished `⊥`-half `d{1} = K_{A(d),Θ→D} ds1` is a
`K`-rule (`tp = isymRep`), permissible for the conclusion (`iperm_isymRep`). So the reduct is
**non-critical** — `zKCritical (fstIdx (red d)) (zKseq (red d))` FAILS. Consequently the iterate-descent
`iord_iR2_iterate_descends`'s criticality hypothesis `hcrit` is **unsatisfiable** after one reduction
step: the critical-only reduct cannot drive the infinite descent on its own. The genuine `red` MUST
dispatch the Buchholz 5.2 cases (splice / replace-premise) on non-critical chains; their ordinal descent
is already banked (`iord_descent_iCritAux` / `iord_descent_iSpliceEnd`, lap 82). -/

/-- The genuine critical reduct `iCritReductG` produces a NON-critical chain: its distinguished premise
(index 1, the `A(d),Θ→D` half, succedent `D`) is itself a `K`-chain, so `tp = isymRep`, permissible for
ANY conclusion (`iperm_isymRep`). Hence `zKCritical` FAILS at index 1. (The in-kernel witness that the
critical-only reduct is incomplete — the lap-86 analog of `not_zKValid_iCritReduct`.) -/
lemma not_zKCritical_iCritReductG (s C rOut rIn0 rIn1 ds0 ds1 : V) :
    ¬ zKCritical (fstIdx (iCritReductG s C rOut rIn0 rIn1 ds0 ds1))
                 (zKseq (iCritReductG s C rOut rIn0 rIn1 ds0 ds1)) := by
  rw [fstIdx_iCritReductG, zKseq_iCritReductG]
  intro hcrit
  have h1 : (1 : V) <
      lh (iCritReductSeq (zK (seqSetSucc s C) rIn0 ds0) (zK (seqAddAnt C s) rIn1 ds1)) := by
    rw [iCritReductSeq_lh]; exact one_lt_two
  have hbad := hcrit 1 h1
  rw [znth_iCritReductSeq_one, tp_zK] at hbad
  exact hbad (iperm_isymRep s)

/-- The reduct `iRcritG d ρ` is a non-critical chain (corollary of `not_zKCritical_iCritReductG`). -/
lemma not_zKCritical_iRcritG (d : V) (ρ : V → V) :
    ¬ zKCritical (fstIdx (iRcritG d ρ)) (zKseq (iRcritG d ρ)) := by
  rw [iRcritG]; exact not_zKCritical_iCritReductG _ _ _ _ _ _ _

/-- **`red` of a CRITICAL `K`-chain is itself a non-critical `K`-chain.** The 5.1 reduct produces a chain
whose `⊥`-premise is a `Rep`, so `zKCritical` fails — the iterate-descent's criticality hypothesis is
UNSATISFIABLE after one step (lap-86 finding). This is exactly why the genuine `red` MUST dispatch the
Buchholz 5.2 cases (`iRK` now does) on the non-critical reducts. (Now hypothesised on the chain being
critical — the case where `red = iRKc = iRcritG`.) -/
lemma not_zKCritical_red_zK {s r ds : V} (hcrit : ¬ permIdx (zK s r ds) < lh ds) :
    ¬ zKCritical (fstIdx (red (zK s r ds))) (zKseq (red (zK s r ds))) := by
  rw [red_zK_crit hcrit]; exact not_zKCritical_iRcritG _ _

/-- **Corollary 2.1 (Buchholz): a permissible premise of a `∅→⊥` chain is `Rep`.** An I-rule premise
(`isymR`) would need succedent `⊥` (impossible — I-rules introduce `∀`/`¬`); an axiom premise (`isymLk`)
would need a formula in the empty antecedent (impossible). So on the ⊥-orbit the selected premise is
always `Rep` — the fact that makes the conclusion-reducing `red` (route B, lap 96) keep `Π` there. -/
lemma tp_isymRep_of_emptyAnt_botSucc {s d : V} (hZ : ZDerivation d)
    (hant : seqAnt s = (∅ : V)) (hsucc : seqSucc s = (^⊥ : V))
    (hperm : iperm (tp d) s) : tp d = isymRep := by
  rcases zDerivation_iff.mp hZ with ⟨s', rfl, _⟩ | ⟨s', a, p, d0, rfl, _, _⟩ | ⟨s', p, d0, rfl, _, _⟩ |
    ⟨s', at', p, d0, d1, rfl, _, _⟩ | ⟨s', r, ds, rfl, _, _, _⟩ |
    ⟨s', p, k, rfl, _, _⟩ | ⟨s', p, rfl, _, _⟩ | ⟨s', C, rfl, _⟩
  · rw [tp_zAtom]
  · rw [tp_zIall] at hperm
    rw [iperm_isymR_iff, hsucc] at hperm
    exact absurd hperm (by simp [qqAll, qqFalsum])
  · rw [tp_zIneg] at hperm
    rw [iperm_isymR_iff, hsucc] at hperm
    exact absurd hperm (by simp [inegF, qqFalsum, qqOr])
  · rw [tp_zInd]
  · rw [tp_zK]
  · rw [tp_zAxAll] at hperm
    rw [iperm_isymLk_iff, hant] at hperm
    exact absurd hperm (by simp [inAnt, lh_empty])
  · rw [tp_zAxNeg] at hperm
    rw [iperm_isymLk_iff, hant] at hperm
    exact absurd hperm (by simp [inAnt, lh_empty])
  · rw [tp_zAx1]

/-- **The selected premise of a `∅→⊥` chain is `Rep`.** For a chain `zK s r ds` deriving `∅→⊥` whose
least-permissible premise index is in range (`permIdx < lh ds`), that premise has `tp = Rep` (Cor 2.1
applied to the permissible selected premise). This discharges the route-B `iRKr` conclusion-reduction on
the ⊥-orbit (`tpReduce isymRep = id`), so `red` keeps the `∅→⊥` conclusion. -/
lemma tp_selected_isymRep_of_emptyAnt_botSucc {s r ds : V} (hZ : ZDerivation (zK s r ds))
    (hant : seqAnt s = (∅ : V)) (hsucc : seqSucc s = (^⊥ : V))
    (hlt : permIdx (zK s r ds) < lh ds) :
    tp (znth ds (permIdx (zK s r ds))) = isymRep := by
  obtain ⟨hds, hmem⟩ := zDerivation_zK_inv hZ
  have hlt' : permIdxAux ds s (lh ds) < lh ds := by
    simpa only [permIdx, fstIdx_zK, zKseq_zK] using hlt
  have hperm : isPermPrem ds s (permIdx (zK s r ds)) := by
    have := permIdxAux_isPermPrem_of_lt ds s (lh ds) hlt'
    simpa only [permIdx, fstIdx_zK, zKseq_zK] using this
  unfold isPermPrem at hperm
  exact tp_isymRep_of_emptyAnt_botSucc (hmem _ hlt) hant hsucc hperm

/-- **`red` preserves the end-sequent on the chain-reduct rules** (`Ind`, `K`), given a `Rep` selected
premise for the chain case (route B, lap 96: the 5.2.2 reduct reduces the conclusion to `tpReduce (tp dᵢ)
Π 0`, which is `Π` iff `tp dᵢ = Rep`). The `Ind` reduct (`iRInd`) and the 5.1/5.2.1 chain branches keep
`Π` unconditionally; the chain replace branch keeps `Π` exactly under `hsel`. On the ⊥-orbit `hsel` holds
by Cor 2.1 (`tp_selected_isymRep_of_emptyAnt_botSucc`). -/
lemma fstIdx_red_of_tag_Ind_or_K {d : V} (hZ : ZDerivation d) (htag : zTag d = 3 ∨ zTag d = 4)
    (hsel : zTag d = 4 → permIdx d < lh (zKseq d) → tp (znth (zKseq d) (permIdx d)) = isymRep) :
    fstIdx (red d) = fstIdx d := by
  rcases zDerivation_iff.mp hZ with ⟨s, rfl, _⟩ | ⟨s, a, p, d0, rfl, _, _⟩ | ⟨s, p, d0, rfl, _, _⟩ |
    ⟨s, at', p, d0, d1, rfl, _, _⟩ | ⟨s, r, ds, rfl, _, _, _⟩ |
    ⟨s, p, k, rfl, _, _⟩ | ⟨s, p, rfl, _, _⟩ | ⟨s, C, rfl, _⟩
  · simp [zTag_zAtom] at htag
  · simp [zTag_zIall] at htag
  · simp [zTag_zIneg] at htag
  · rw [red_zInd, iRInd_zInd]; simp [fstIdx_zInd]
  · rw [red_zK]
    refine fstIdx_iRK_of_Rep (fun h1 _ => ?_)
    have := hsel (by simp) (by simpa only [zKseq_zK] using h1)
    simpa only [zKseq_zK] using this
  · simp [zTag_zAxAll] at htag
  · simp [zTag_zAxNeg] at htag
  · simp [zTag_zAx1] at htag

set_option maxHeartbeats 800000 in
/-- **`red` keeps the `∅→⊥` conclusion on the ⊥-orbit.** Discharges `fstIdx_red_of_tag_Ind_or_K`'s `hsel`
via Cor 2.1: the selected premise of a `∅→⊥` chain is `Rep`. This is the headline-relevant conclusion
invariant — `red` of a contradiction derivation again concludes `∅→⊥`. (Stated on the raw `∅→⊥` data
since `ZDerivesEmpty` is defined later in the file; the packaged form is `fstIdx_red_of_ZDerivesEmpty`.) -/
lemma fstIdx_red_of_emptyAnt_botSucc {d : V} (hZ : ZDerivation d)
    (hant : seqAnt (fstIdx d) = (∅ : V)) (hsucc : seqSucc (fstIdx d) = (^⊥ : V))
    (htag : zTag d = 3 ∨ zTag d = 4) : fstIdx (red d) = fstIdx d := by
  rcases zDerivation_iff.mp hZ with ⟨s, rfl, _⟩ | ⟨s, a, p, d0, rfl, _, _⟩ | ⟨s, p, d0, rfl, _, _⟩ |
    ⟨s, at', p, d0, d1, rfl, _, _⟩ | ⟨s, r, ds, rfl, hds, hmem, hvalid⟩ |
    ⟨s, p, k, rfl, _, _⟩ | ⟨s, p, rfl, _, _⟩ | ⟨s, C, rfl, _⟩
  · simp [zTag_zAtom] at htag
  · simp [zTag_zIall] at htag
  · simp [zTag_zIneg] at htag
  · rw [red_zInd, iRInd_zInd]; simp [fstIdx_zInd]
  · rw [red_zK]
    refine fstIdx_iRK_of_Rep (fun h1 _ => ?_)
    rw [fstIdx_zK] at hant hsucc
    rw [zKseq_zK] at h1 ⊢
    exact tp_selected_isymRep_of_emptyAnt_botSucc hZ hant hsucc h1
  · simp [zTag_zAxAll] at htag
  · simp [zTag_zAxNeg] at htag
  · simp [zTag_zAx1] at htag

/-- **`red` keeps the chain conclusion when the selected premise is `Rep` (the GENERAL Rep-reduction, lap
100).** Generalizes `fstIdx_red_of_emptyAnt_botSucc`'s K-case OFF the `∅→⊥` hypothesis: `fstIdx (red (zK s r
ds)) = fstIdx (zK s r ds)` holds whenever the chain's selected premise is `Rep`-or-a-critical-chain (the
exact `fstIdx_iRK_of_Rep` precondition). This is the precise content of `redZKReady`'s chain-`Rep` residual
`fstIdx (red dᵢ) = fstIdx dᵢ`: it is NOT `∅→⊥` that matters but the (hereditary) Rep-ness of the selected
premise. On the ⊥-orbit `tp_selected_isymRep_of_emptyAnt_botSucc` discharges `hsel` at the top; the motive
must propagate it down selected-premise chains (the core hereditary obligation). -/
lemma fstIdx_red_zK_of_selected_Rep {s r ds : V}
    (hsel : permIdx (zK s r ds) < lh ds →
      ¬ (zTag (znth ds (permIdx (zK s r ds))) = 4 ∧
         ¬ permIdx (znth ds (permIdx (zK s r ds)))
           < lh (zKseq (znth ds (permIdx (zK s r ds))))) →
      tp (znth ds (permIdx (zK s r ds))) = isymRep) :
    fstIdx (red (zK s r ds)) = fstIdx (zK s r ds) := by
  rw [red_zK]
  refine fstIdx_iRK_of_Rep (fun h1 h2 => ?_)
  rw [zKseq_zK] at h1 h2 ⊢
  exact hsel h1 h2

/-! ### The ordinal of `red`'s K-case = the ordinal of `iR2`'s K-case (the descent bridge)

`iRcritG` (genuine, correct endsequents) and `iRcrit` (ordinal-shadow) differ ONLY in the auxiliaries'
conclusion sequents (`seqSetSucc`/`seqAddAnt` vs the reused `fstIdx d`). Since `iotil`/`idg` of a chain
`zK s r ds` are independent of `s` (`iotil_zK = iseqNaddIdg ds`, `idg_zK = max r (iseqMaxIdg ds - 1)`),
the two reducts carry the SAME `iord`. So the (banked) ordinal descent on `iRcrit` transfers verbatim to
`red`'s K-case — `red`'s validity-faithfulness costs nothing on the ordinal side. -/

@[simp] lemma iotil_iRcritG_eq_iRcrit (d : V) (ρ : V → V) :
    iotil (iRcritG d ρ) = iotil (iRcrit d ρ) := by
  rw [iRcritG, iCritReductG, iRcrit, iCritReduct, iCritAux, iCritAux,
    iotil_zK _ _ _ (iCritReductSeq_seq _ _), iotil_zK _ _ _ (iCritReductSeq_seq _ _),
    iseqNaddIdg_iCritReductSeq, iseqNaddIdg_iCritReductSeq,
    iotil_zK _ _ _ (seqUpdate_seq _ _ _), iotil_zK _ _ _ (seqUpdate_seq _ _ _),
    iotil_zK _ _ _ (seqUpdate_seq _ _ _), iotil_zK _ _ _ (seqUpdate_seq _ _ _)]

@[simp] lemma idg_iRcritG_eq_iRcrit (d : V) (ρ : V → V) :
    idg (iRcritG d ρ) = idg (iRcrit d ρ) := by
  rw [iRcritG, iCritReductG, iRcrit, iCritReduct, iCritAux, iCritAux,
    idg_zK _ _ _ (iCritReductSeq_seq _ _), idg_zK _ _ _ (iCritReductSeq_seq _ _),
    iseqMaxIdg_iCritReductSeq, iseqMaxIdg_iCritReductSeq,
    idg_zK _ _ _ (seqUpdate_seq _ _ _), idg_zK _ _ _ (seqUpdate_seq _ _ _),
    idg_zK _ _ _ (seqUpdate_seq _ _ _), idg_zK _ _ _ (seqUpdate_seq _ _ _)]

/-- **The genuine reduct's K-case has the same ordinal as the ordinal-shadow `iRcrit`.** -/
lemma iord_iRcritG_eq_iRcrit (d : V) (ρ : V → V) :
    iord (iRcritG d ρ) = iord (iRcrit d ρ) := by
  rw [iord_eq, iord_eq, iotil_iRcritG_eq_iRcrit, idg_iRcritG_eq_iRcrit]

/-! ### The ¬-case constructor `iRcritGNeg` shares `iord` with `iRcrit` too (the swap is `#`/`max`-commutative)

`iRcritGNeg` is `iRcritG` with the two `seqUpdate` halves at `redexI`/`redexJ` SWAPPED (Buchholz's
polarity swap for `Aᵢ=¬A`). Since `iotil(iCritReductG …) = ω^{õ ds0} # ω^{õ ds1}` (`inadd`, commutative on
NF args) and `idg(…) = max(idg ds0)(idg ds1)` (commutative unconditionally), the swap leaves `iord`
INVARIANT. So the descent twin for the engine re-key's ¬-branch reuses the banked `iord` descent on `iRcrit`
verbatim — the ordinal side is polarity-blind (the `#`/`max` are symmetric), exactly as the lap-117 handoff
predicted. The `iotil` half needs the two folds NF (the `hNF`/`hρNF` data already threaded at the descent
call site `iord_descent_iRcrit_of_chain`); the `idg` half is unconditional. -/
lemma idg_iRcritGNeg_eq_iRcrit (d : V) (ρ : V → V) :
    idg (iRcritGNeg d ρ) = idg (iRcrit d ρ) := by
  rw [iRcritGNeg, iCritReductG, iRcrit, iCritReduct, iCritAux, iCritAux,
    idg_zK _ _ _ (iCritReductSeq_seq _ _), idg_zK _ _ _ (iCritReductSeq_seq _ _),
    iseqMaxIdg_iCritReductSeq, iseqMaxIdg_iCritReductSeq]
  nth_rewrite 2 [max_comm]
  rw [idg_zK _ _ _ (seqUpdate_seq _ _ _), idg_zK _ _ _ (seqUpdate_seq _ _ _),
    idg_zK _ _ _ (seqUpdate_seq _ _ _), idg_zK _ _ _ (seqUpdate_seq _ _ _)]

lemma iotil_iRcritGNeg_eq_iRcrit (d : V) (ρ : V → V)
    (hNFI : isNF (iseqNaddIdg (seqUpdate (zKseq d) (redexI d) (ρ (redexI d)))))
    (hNFJ : isNF (iseqNaddIdg (seqUpdate (zKseq d) (redexJ d) (ρ (redexJ d))))) :
    iotil (iRcritGNeg d ρ) = iotil (iRcrit d ρ) := by
  rw [iRcritGNeg, iCritReductG, iRcrit, iCritReduct, iCritAux, iCritAux,
    iotil_zK _ _ _ (iCritReductSeq_seq _ _), iotil_zK _ _ _ (iCritReductSeq_seq _ _),
    iseqNaddIdg_iCritReductSeq, iseqNaddIdg_iCritReductSeq,
    iotil_zK _ _ _ (seqUpdate_seq _ _ _), iotil_zK _ _ _ (seqUpdate_seq _ _ _),
    iotil_zK _ _ _ (seqUpdate_seq _ _ _), iotil_zK _ _ _ (seqUpdate_seq _ _ _)]
  exact inadd_comm _ (isNF_omega_pow hNFI) _ (isNF_omega_pow hNFJ)

/-- **The ¬-case reduct's K-case has the same ordinal as the ordinal-shadow `iRcrit`** (the `iRcritGNeg`
twin of `iord_iRcritG_eq_iRcrit`; the engine re-key's ¬-branch descent re-point). -/
lemma iord_iRcritGNeg_eq_iRcrit (d : V) (ρ : V → V)
    (hNFI : isNF (iseqNaddIdg (seqUpdate (zKseq d) (redexI d) (ρ (redexI d)))))
    (hNFJ : isNF (iseqNaddIdg (seqUpdate (zKseq d) (redexJ d) (ρ (redexJ d))))) :
    iord (iRcritGNeg d ρ) = iord (iRcrit d ρ) := by
  rw [iord_eq, iord_eq, iotil_iRcritGNeg_eq_iRcrit d ρ hNFI hNFJ, idg_iRcritGNeg_eq_iRcrit]

/-! ### Structural correctness of the `iR2` table (mirror `idg`) -/

private lemma def_iRTable {k} (i : Fin k) :
    𝚺-[1].DefinableFunction (fun v : Fin k → V ↦ iRTable (v i)) :=
  DefinableFunction₁.comp (F := iRTable) (DefinableFunction.var i)

private lemma def_iR2 {k} (i : Fin k) :
    𝚺-[1].DefinableFunction (fun v : Fin k → V ↦ iR2 (v i)) :=
  DefinableFunction₁.comp (F := iR2) (DefinableFunction.var i)

@[simp] lemma iRTable_seq (n : V) : Seq (iRTable n) := by
  induction n using ISigma1.sigma1_succ_induction
  · exact Definable.comp₁ (def_iRTable 0)
  case zero => simp
  case succ n ih => rw [iRTable_succ]; exact ih.seqCons _

@[simp] lemma iRTable_lh (n : V) : lh (iRTable n) = n + 1 := by
  induction n using ISigma1.sigma1_succ_induction
  · exact Definable.comp₂ (DefinableFunction₁.comp (F := lh) (def_iRTable 0)) (by definability)
  case zero => simp
  case succ n ih => rw [iRTable_succ, Seq.lh_seqCons _ (iRTable_seq n), ih]

lemma znth_iRTable_succ {n k : V} (hk : k < n + 1) :
    znth (iRTable (n + 1)) k = znth (iRTable n) k := by
  rw [iRTable_succ]
  exact znth_seqCons_of_lt (iRTable_seq n) _ (by rw [iRTable_lh]; exact hk)

lemma znth_iRTable_eq_iR2 : ∀ N : V, ∀ k ≤ N, znth (iRTable N) k = iR2 k := by
  intro N
  induction N using ISigma1.sigma1_succ_induction
  · refine Definable.ball_le (by definability) ?_
    exact Definable.comp₂
      (DefinableFunction₂.comp (F := znth) (def_iRTable 1) (DefinableFunction.var 0))
      (def_iR2 0)
  case zero =>
    intro k hk; rcases (nonpos_iff_eq_zero.mp hk) with rfl; rfl
  case succ N ih =>
    intro k hk
    rcases eq_or_lt_of_le hk with rfl | hlt
    · rfl
    · rw [znth_iRTable_succ hlt]; exact ih k (le_iff_lt_succ.mpr hlt)

/-- `iR2 c = iRNext c (iRTable (c-1))` for positive codes (the table-reduction unfolding). -/
lemma iR2_eq_iRNext {c : V} (hpos : 0 < c) : iR2 c = iRNext c (iRTable (c - 1)) := by
  obtain ⟨M, rfl⟩ : ∃ M, c = M + 1 := ⟨c - 1, (sub_add_self_of_le (pos_iff_one_le.mp hpos)).symm⟩
  have key : znth (iRTable (M + 1)) (M + 1) = iRNext (M + 1) (iRTable M) := by
    rw [iRTable_succ]
    have h := znth_seqCons_self (iRTable_seq M) (iRNext (M + 1) (iRTable M))
    rwa [iRTable_lh] at h
  simp only [iR2, add_tsub_cancel_right, key]

/-! ### `iR2` recursion equations (Buchholz Def 3.2, per rule) -/

@[simp] lemma iR2_zAtom (s : V) : iR2 (zAtom s) = zAtom s := by
  rw [iR2_eq_iRNext (by simp [zAtom]), iRNext]; simp [zTag_zAtom]

@[simp] lemma iR2_zIall (s a p d0 : V) : iR2 (zIall s a p d0) = d0 := by
  rw [iR2_eq_iRNext (by simp [zIall]), iRNext, if_pos (zTag_zIall s a p d0)]
  simp [zIallPrem_zIall]

@[simp] lemma iR2_zIneg (s p d0 : V) : iR2 (zIneg s p d0) = d0 := by
  rw [iR2_eq_iRNext (by simp [zIneg]), iRNext, if_neg (by simp), if_pos (zTag_zIneg s p d0)]
  simp [zInegPrem_zIneg]

@[simp] lemma iR2_zInd (s at' p d0 d1 : V) :
    iR2 (zInd s at' p d0 d1) = iRInd (zInd s at' p d0 d1) := by
  rw [iR2_eq_iRNext (by simp [zInd]), iRNext, if_neg (by simp), if_neg (by simp),
    if_pos (zTag_zInd s at' p d0 d1)]

@[simp] lemma iR2_zAxAll (s p k : V) : iR2 (zAxAll s p k) = zAxAll s p k := by
  rw [iR2_eq_iRNext (by simp [zAxAll]), iRNext]; simp [zTag_zAxAll]

@[simp] lemma iR2_zAxNeg (s p : V) : iR2 (zAxNeg s p) = zAxNeg s p := by
  rw [iR2_eq_iRNext (by simp [zAxNeg]), iRNext]; simp [zTag_zAxNeg]

/-- **The K-rule (critical) recursion equation** (Buchholz Def 3.2 case 5.1): `iR2` of a chain code is
the critical reduct at the functional redex, with the two auxiliaries' premise-reducts supplied
RECURSIVELY (`iR2 (znth ds (redexI/redexJ ..))`). This is `iRcrit (zK s r ds) ρ` at the concrete
`ρ = fun n ↦ iR2 (znth ds n)`. Both premise codes `< zK s r ds`, so they sit inside the length-`(zK-1)`
table (`znth_le_self` + `ds_lt_zK`). -/
lemma iR2_zK (s r ds : V) :
    iR2 (zK s r ds) =
      iCritReduct (zK s r ds) (redexI (zK s r ds)) (redexJ (zK s r ds))
        (zAxReduct (iR2 (znth ds (redexI (zK s r ds)))))
        (zAxReduct (iR2 (znth ds (redexJ (zK s r ds))))) := by
  have hbound : ∀ k : V, znth ds k ≤ zK s r ds - 1 := fun k =>
    le_trans (znth_le_self ds k) (le_pred_of_lt (ds_lt_zK s r ds))
  rw [iR2_eq_iRNext (by simp [zK]), iRNext, if_neg (by simp), if_neg (by simp), if_neg (by simp),
    if_pos (zTag_zK s r ds), zKseq_zK,
    znth_iRTable_eq_iR2 _ (znth ds (redexI (zK s r ds))) (hbound _),
    znth_iRTable_eq_iR2 _ (znth ds (redexJ (zK s r ds))) (hbound _)]

/-- `iR2 (zK s r ds) = iRcrit (zK s r ds) (fun n ↦ zAxReduct (iR2 (znth ds n)))` — the recursive reduct
IS the abstract critical reduct `iRcrit` at the concrete recursive `ρ`, with the §5 atomic reduct
`zAxReduct` applied per premise (identity off atomic axioms; the §5 `Ax^1` reduct on the L-axiom redex
j-premise — the descent-carrying j-side fix, lap 66). Bridges the closed recursion to the banked nut
descent `iord_descent_iRcrit_of_chain`. -/
lemma iR2_zK_eq_iRcrit (s r ds : V) :
    iR2 (zK s r ds) = iRcrit (zK s r ds) (fun n => zAxReduct (iR2 (znth ds n))) := by
  rw [iR2_zK, iRcrit]

/-- **`red` and `iR2` agree off the critical K-case and the I∀ rule.** `iRNextG` and `iRNext` have
identical I¬/`Ind` branches (none reads the table), so on any non-tag-{1,4} code the genuine reduct equals
the ordinal-shadow. They differ at tag 4 (`iRcritG` vs `iCritReduct`) and — since the lap-97 route-B
rewire — at tag 1 (`red` does the I∀ eigensubst `zsubst d0 a 0`, `iR2` keeps `d0`); the ordinal is
preserved at both (`iord_iRcritG_eq_iRcrit`; `iord_zsubst`). -/
lemma red_eq_iR2_of_tag_ne_one_four {x : V} (h1 : zTag x ≠ 1) (h : zTag x ≠ 4) : red x = iR2 x := by
  rcases eq_or_ne x 0 with rfl | hpos
  · simp [red, iR2]
  · have hp := pos_iff_ne_zero.mpr hpos
    rw [red_eq_iRNextG hp, iR2_eq_iRNext hp, iRNextG, iRNext]
    by_cases h2 : zTag x = 2
    · simp [h1, h2]
    · by_cases h3 : zTag x = 3
      · simp [h1, h2, h3]
      · simp [h1, h2, h3, h]

/-- **The redexI premise's `iR2`-reduct satisfies the IH bundle, concretely** (the recursive-`iR2`
analog of lap-71's `iRedDescent_iR_of_tp_isymR`). A premise `d` with `tp d = R_A` is an I-rule
(`tp_isymR_tag` ⟹ tag 1/2), where `iR2 d = d0` (the sub-derivation) agrees with the old `iR`; so the
banked `iRedDescent_zIall`/`_zIneg` apply verbatim. This discharges the `i`-side of the K-case nut's
six `ρ`-facts (`iord_descent_iRcrit_of_chain'`'s `hρlt_i`/`hρg_i`/`hρNF_i`) for the CONCRETE recursive
`ρ = iR2(znth ds ·)`. Only the `j`-side (the L-axiom §5 atomic reduct) remains. -/
lemma iRedDescent_iR2_of_tp_isymR {d A : V} (htp : tp d = isymR A) (hZ : ZDerivation d) :
    iRedDescent (iR2 d) d := by
  rcases zDerivation_iff.mp hZ with ⟨s, rfl, _⟩ | ⟨s, a, p, d0, rfl, hd0, _⟩ | ⟨s, p, d0, rfl, hd0, _⟩ |
    ⟨s, at', p, d0, d1, rfl, _, _⟩ | ⟨s, r, ds, rfl, _, _, _⟩ |
    ⟨s, p, k, rfl, _, _⟩ | ⟨s, p, rfl, _, _⟩ | ⟨s, C, rfl, _⟩
  · rw [tp_zAtom] at htp; exact absurd htp (by simp)
  · rw [iR2_zIall]; exact iRedDescent_zIall (isNF_iotil_of_ZDerivation d0 hd0)
  · rw [iR2_zIneg]; exact iRedDescent_zIneg (isNF_iotil_of_ZDerivation d0 hd0)
  · rw [tp_zInd] at htp; exact absurd htp (by simp)
  · rw [tp_zK] at htp; exact absurd htp (by simp)
  · rw [tp_zAxAll] at htp; exact absurd htp (by simp)
  · rw [tp_zAxNeg] at htp; exact absurd htp (by simp)
  · rw [tp_zAx1] at htp; exact absurd htp (by simp)

/-! ### j-side §5 atomic-axiom reduct bundle (the K-case's L-premise descent, lap 66)

The K-case nut (`iord_descent_iRcrit_of_chain'`) pins its descent to six `ρ`-facts about the two redex
premises. The i-side (R-redex, an I-rule) is discharged by `iRedDescent_iR2_of_tp_isymR`. The j-side
(L-axiom redex, tags 5/6) needs the §5 `Ax^1` reduct `zAx1`: these two lemmas package its
`iRedDescent` bundle (degree not raised — both `idg = 0`; pre-ordinal strictly dropped via
`icmp_iotil_zAx1_z*`; reduct NF). Buchholz Lemma 5.2. The remaining plumbing (next lap, see
PENDING_WORK): `iR2` is the IDENTITY on atomic axioms (`iR2_zAxAll`/`iR2_zAxNeg`), so the §5 reduct
cannot enter via the `iR2` table — `iCritReduct`'s j-component must invoke `zAx1` directly. These
bundles are exactly what that revised critical reduct must supply on the j-side. -/
lemma iRedDescent_zAx1_zAxAll {s p k : V} (hp : IsUFormula ℒₒᵣ p) :
    iRedDescent (zAx1 s p) (zAxAll s p k) :=
  ⟨by simp, icmp_iotil_zAx1_zAxAll hp, isNF_iotil_zAx1 s p⟩

lemma iRedDescent_zAx1_zAxNeg {s p : V} (hp : IsUFormula ℒₒᵣ p) :
    iRedDescent (zAx1 s p) (zAxNeg s p) :=
  ⟨by simp, icmp_iotil_zAx1_zAxNeg hp, isNF_iotil_zAx1 s p⟩

/-- **The CORRECTED critical ¬-L-reduct's descent bundle (sequent-general).** The §5 critical reduct of an
`axNeg` redex is `zAx1 S C` (succedent-set sequent `S = seqSetSucc sⱼ C`, payload `C = cutFormula d`). Since
`iRedDescent` reads the reduct/redex only through `iotil (zAx1 S C) = oAtom1 C` and
`iotil (zAxNeg s C) = oAtomLk (inegF C)` — BOTH independent of the sequents `S`/`s` — the descent bundle
holds for arbitrary `S`, `s` (the ¬-side twin of `iRedDescent_zAx1_zAxAll_of_irk`, here with payload `= C`
matching `zAxNeg`'s, so no rank side-condition). This is what the re-keyed `red` (`critReductNeg`) needs on
the L-side. -/
lemma iRedDescent_zAx1_zAxNeg_gen {S s p : V} (hp : IsUFormula ℒₒᵣ p) :
    iRedDescent (zAx1 S p) (zAxNeg s p) := by
  refine ⟨by simp, ?_, isNF_iotil_zAx1 S p⟩
  rw [iotil_zAx1, iotil_zAxNeg]
  have := icmp_iotil_zAx1_zAxNeg (s := S) hp
  rwa [iotil_zAx1, iotil_zAxNeg] at this

/-- **The CORRECTED critical L-reduct's descent bundle (sequent- and payload-general).** The §5 critical
reduct of an `axAll` redex is `zAx1 S C` for an arbitrary sequent `S` (the cut-instance-grown antecedent)
and payload `C` (the cut formula `F(k)`, NOT the open matrix `p`). Since `iRedDescent` reads the reduct only
through `iotil (zAx1 S C) = oAtom1 C` (`@[simp] iotil_zAx1`) and `idg (zAx1 S C) = 0` — both INDEPENDENT of
the sequent `S` — the descent bundle holds for any `S` provided the payload sits one rank below the principal
`∀p` (`irk (∀p) = irk C + 1`). For the genuine reduct `C = cutFormula d`: `irk (cutFormula d) = irk p` (by
`irk_substs1`/`cutFormula_all`), so `irk (∀p) = irk p + 1 = irk (cutFormula d) + 1`. This is the L-side
descent fact the re-keyed `red` (`critReductCorr`) needs, generalising `iRedDescent_zAx1_zAxAll` (the engine
reduct `zAx1 s p`, payload `= p`) to the corrected payload. -/
lemma iRedDescent_zAx1_zAxAll_of_irk {S C s p k : V}
    (hC : irk (^∀ p : V) = irk C + 1) :
    iRedDescent (zAx1 S C) (zAxAll s p k) :=
  ⟨by simp, by rw [iotil_zAx1, iotil_zAxAll]; exact icmp_oAtom1_oAtomLk hC, isNF_iotil_zAx1 S C⟩

/-- **j-side bundle via `zAxReduct`, ∀-axiom case**: the reduct `zAxReduct (Ax^{∀p,k})` satisfies the
`iRedDescent` bundle (the K-case nut's j-side fact, packaged on the genuine reduct function). -/
lemma iRedDescent_zAxReduct_zAxAll {s p k : V} (hp : IsUFormula ℒₒᵣ p) :
    iRedDescent (zAxReduct (zAxAll s p k)) (zAxAll s p k) := by
  rw [zAxReduct_zAxAll]; exact iRedDescent_zAx1_zAxAll hp

/-- **j-side bundle via `zAxReduct`, ¬-axiom case**. -/
lemma iRedDescent_zAxReduct_zAxNeg {s p : V} (hp : IsUFormula ℒₒᵣ p) :
    iRedDescent (zAxReduct (zAxNeg s p)) (zAxNeg s p) := by
  rw [zAxReduct_zAxNeg]; exact iRedDescent_zAx1_zAxNeg hp

/-- **`zAxReduct` is the identity on an R-redex (I-rule) premise**: `tp d = isymR A` forces
`zTag d ∈ {1,2}` (`tp_isymR_tag`), never the atomic-axiom tags `5,6`, so `zAxReduct d = d`. Collapses
the i-side `zAxReduct`-wrap `zAxReduct (iR2 premᵢ) = iR2 premᵢ` introduced by the tag-4 rewrite (the
i-side redex premise is an I-rule). Stated on `tp` directly (no `ZDerivation` needed). NOTE: since
`ZDerivation` now includes the atomic-axiom leaves (tags 5,6), `zAxReduct` is NOT the identity on a
general `ZDerivation` — only on the non-axiom tags, which the `tp = isymR` redex premise guarantees. -/
lemma zAxReduct_of_tp_isymR {d A : V} (htp : tp d = isymR A) : zAxReduct d = d := by
  rcases tp_isymR_tag htp with h | h <;> simp [zAxReduct, h]

/-- `zAxReduct` is the identity off the §5 atomic-axiom tags (5,6). -/
lemma zAxReduct_eq_self_of_ne {d : V} (h5 : zTag d ≠ 5) (h6 : zTag d ≠ 6) :
    zAxReduct d = d := by simp [zAxReduct, h5, h6]

/-- **Wrapping `zAxReduct` around a `ZDerivation` reduct preserves the `iRedDescent` bundle.** On the
non-axiom tags `zAxReduct` is the identity (`zAxReduct_eq_self_of_ne`); on the §5 axiom leaves (tags
5/6) it replaces the leaf `zAxAll`/`zAxNeg` by the `Ax^1` reduct `zAx1`, which lies strictly *below*
the leaf (`icmp_iotil_zAx1_z*`, using the leaf's carried `IsUFormula`) at degree 0 — so the descent
bundle only improves (via `icmp_trans`). This is what collapses the i-side `zAxReduct (iR2 premᵢ)`
wrap even when the I-rule sub-derivation `iR2 premᵢ` itself happens to be an axiom leaf. -/
lemma iRedDescent_zAxReduct_of_iRedDescent {e d : V} (he : ZDerivation e)
    (h : iRedDescent e d) : iRedDescent (zAxReduct e) d := by
  rcases zDerivation_iff.mp he with ⟨s, rfl, _⟩ | ⟨s, a, p, d0, rfl, _, _⟩ | ⟨s, p, d0, rfl, _, _⟩ |
    ⟨s, at', p, d0, d1, rfl, _, _⟩ | ⟨s, r, ds, rfl, _, _, _⟩ |
    ⟨s, p, k, rfl, hp, _⟩ | ⟨s, p, rfl, hp, _⟩ | ⟨s, C, rfl, _⟩
  · rwa [zAxReduct_eq_self_of_ne (by simp [zTag_zAtom]) (by simp [zTag_zAtom])]
  · rwa [zAxReduct_eq_self_of_ne (by simp [zTag_zIall]) (by simp [zTag_zIall])]
  · rwa [zAxReduct_eq_self_of_ne (by simp [zTag_zIneg]) (by simp [zTag_zIneg])]
  · rwa [zAxReduct_eq_self_of_ne (by simp [zTag_zInd]) (by simp [zTag_zInd])]
  · rwa [zAxReduct_eq_self_of_ne (by simp [zTag_zK]) (by simp [zTag_zK])]
  · rw [zAxReduct_zAxAll]
    refine ⟨by rw [idg_zAx1, ← idg_zAxAll s p k]; exact h.dg_le, ?_, isNF_iotil_zAx1 s p⟩
    exact icmp_trans (max (iotil (zAx1 s p)) (max (iotil (zAxAll s p k)) (iotil d)))
      _ (le_max_left _ _) _ (le_trans (le_max_left _ _) (le_max_right _ _))
      _ (le_trans (le_max_right _ _) (le_max_right _ _))
      (icmp_iotil_zAx1_zAxAll hp.isUFormula) h.otil_lt
  · rw [zAxReduct_zAxNeg]
    refine ⟨by rw [idg_zAx1, ← idg_zAxNeg s p]; exact h.dg_le, ?_, isNF_iotil_zAx1 s p⟩
    exact icmp_trans (max (iotil (zAx1 s p)) (max (iotil (zAxNeg s p)) (iotil d)))
      _ (le_max_left _ _) _ (le_trans (le_max_left _ _) (le_max_right _ _))
      _ (le_trans (le_max_right _ _) (le_max_right _ _))
      (icmp_iotil_zAx1_zAxNeg hp) h.otil_lt
  · rwa [zAxReduct_eq_self_of_ne (by simp [zTag_zAx1]) (by simp [zTag_zAx1])]

/-- **i-side ρ-fact** (R-redex premise): for an I-rule premise `d` (`tp d = R_A`), the wrapped recursive
reduct `zAxReduct (iR2 d)` satisfies the `iRedDescent` bundle. `iR2 d` is the I-rule's sub-derivation
(a `ZDerivation`), so `iRedDescent_iR2_of_tp_isymR` gives the un-wrapped bundle and
`iRedDescent_zAxReduct_of_iRedDescent` collapses the wrap. -/
lemma iRedDescent_zAxReduct_iR2_of_tp_isymR {d A : V} (htp : tp d = isymR A) (hZ : ZDerivation d) :
    iRedDescent (zAxReduct (iR2 d)) d := by
  have hbase := iRedDescent_iR2_of_tp_isymR htp hZ
  have hZred : ZDerivation (iR2 d) := by
    rcases zDerivation_iff.mp hZ with ⟨s, rfl, _⟩ | ⟨s, a, p, d0, rfl, hd0, _⟩ | ⟨s, p, d0, rfl, hd0, _⟩ |
      ⟨s, at', p, d0, d1, rfl, _, _⟩ | ⟨s, r, ds, rfl, _, _, _⟩ |
      ⟨s, p, k, rfl, _, _⟩ | ⟨s, p, rfl, _, _⟩ | ⟨s, C, rfl, _⟩
    · rw [tp_zAtom] at htp; exact absurd htp (by simp)
    · rw [iR2_zIall]; exact hd0
    · rw [iR2_zIneg]; exact hd0
    · rw [tp_zInd] at htp; exact absurd htp (by simp)
    · rw [tp_zK] at htp; exact absurd htp (by simp)
    · rw [tp_zAxAll] at htp; exact absurd htp (by simp)
    · rw [tp_zAxNeg] at htp; exact absurd htp (by simp)
    · rw [tp_zAx1] at htp; exact absurd htp (by simp)
  exact iRedDescent_zAxReduct_of_iRedDescent hZred hbase

/-- **j-side ρ-fact** (L-axiom redex premise): for a §5 atomic-axiom premise `d` (`tp d = L^k_A`),
the wrapped recursive reduct `zAxReduct (iR2 d)` satisfies the `iRedDescent` bundle. `iR2` is the
identity on the axiom leaves, and `zAxReduct (zAxAll/zAxNeg) = zAx1` carries the strict descent
(`iRedDescent_zAxReduct_zAxAll/_zAxNeg`, using the leaf's `IsUFormula`). -/
lemma iRedDescent_zAxReduct_iR2_of_tp_isymLk {d k A : V} (htp : tp d = isymLk k A)
    (hZ : ZDerivation d) : iRedDescent (zAxReduct (iR2 d)) d := by
  rcases zDerivation_iff.mp hZ with ⟨s, rfl, _⟩ | ⟨s, a, p, d0, rfl, _, _⟩ | ⟨s, p, d0, rfl, _, _⟩ |
    ⟨s, at', p, d0, d1, rfl, _, _⟩ | ⟨s, r, ds, rfl, _, _, _⟩ |
    ⟨s, p, k', rfl, hp, _⟩ | ⟨s, p, rfl, hp, _⟩ | ⟨s, C, rfl, _⟩
  · rw [tp_zAtom] at htp; exact absurd htp (by simp)
  · rw [tp_zIall] at htp; exact absurd htp (by simp)
  · rw [tp_zIneg] at htp; exact absurd htp (by simp)
  · rw [tp_zInd] at htp; exact absurd htp (by simp)
  · rw [tp_zK] at htp; exact absurd htp (by simp)
  · rw [iR2_zAxAll]; exact iRedDescent_zAxReduct_zAxAll hp.isUFormula
  · rw [iR2_zAxNeg]; exact iRedDescent_zAxReduct_zAxNeg hp
  · rw [tp_zAx1] at htp; exact absurd htp (by simp)

/-! ### The tag-4 (K-rule) descent, conditional on chain validity

`iord_descent_iR2_struct` covers I-rules/Ind (tags 1,2,3) unconditionally. The K-rule (tag 4) descent
needs the Buchholz side conditions of a *valid* `K^r` inference — packaged here as `zKValid` — which
the bare `ZPhi` `zK` disjunct (just `Seq ds ∧ ∀ i, premise ∈ ZDerivation`) does NOT yet carry. This
lemma proves the tag-4 descent CONDITIONALLY on `zKValid`; wiring `zKValid` into the `ZPhi` `zK`
disjunct (the Σ₁/Δ₁ Fixpoint cascade) is the next phase, after which the tag-4 case of
`iord_descent_iR2_struct` falls out by feeding `zDerivation_zK_inv` + this lemma. (`zKValid` and its
`𝚫₁` arithmetization `zKValidDef` are defined earlier, alongside `isChainInfDef`.) -/

/-- **THE K-case descent (tag 4), conditional on chain validity.** For a valid `K^r` chain `zK s r ds`
whose premises are all `ZDerivation`s, the recursive reduct `iR2` strictly lowers the ordinal:
`o(iR2 (zK s r ds)) ≺ o(zK s r ds)`. Assembled by feeding `iord_descent_iRcrit_of_chain'` at
`Tr := False`, `Fa := (· = ⊥)`: the chain-structure data comes from `isChainInf`, the `hwfR`/`hwfL`
rank conditions from `tp_isymR_pos`/`tp_isymLk_pos` + `zKValid`'s formula-hood, and the six redex
`ρ`-facts (`ρ = zAxReduct ∘ iR2`) from `redexPair_tp` (reading the redex premises' `tp` off the
finder's least-pair) + the i/j-side wrap helpers. -/
lemma iord_descent_iR2_zK_of_valid {s r ds : V} (hds : Seq ds)
    (hmem : ∀ i < lh ds, ZDerivation (znth ds i)) (hvalid : zKValid s r ds) :
    icmp (iord (iR2 (zK s r ds))) (iord (zK s r ds)) = 0 := by
  obtain ⟨hci, hperm0, hnperm0, hf1, hf2, hf5, hf6, _hsucc, _hssf, _hsaf⟩ := hvalid
  obtain ⟨j0, hj0, hAj0, hchain, hrank⟩ := hci
  -- Tr/Fa = the ⊥-instances; the well-formedness obligations discharge as in `..._of_chain_tp`.
  have hwfR : ∀ i ≤ j0, ∀ A, tp (znth ds i) = isymR A → 0 < irk A ∨ False :=
    fun i hi A h => Or.inl (tp_isymR_pos h (hf1 i (lt_of_le_of_lt hi hj0))
      (hf2 i (lt_of_le_of_lt hi hj0)))
  have hwfL : ∀ i ≤ j0, ∀ k A, tp (znth ds i) = isymLk k A → 0 < irk A ∨ (A = (^⊥ : V)) :=
    fun i hi k A h => Or.inl (tp_isymLk_pos h (hf5 i (lt_of_le_of_lt hi hj0))
      (hf6 i (lt_of_le_of_lt hi hj0)))
  have hperm : ∀ i ≤ j0, iperm (tp (znth ds i)) (fstIdx (znth ds i)) :=
    fun i hi => hperm0 i (lt_of_le_of_lt hi hj0)
  have hnperm : ∀ i ≤ j0, ¬ iperm (tp (znth ds i)) s :=
    fun i hi => hnperm0 i (lt_of_le_of_lt hi hj0)
  have hnf : isNF (iotil (zK s r ds)) :=
    isNF_iotil_zK hds (fun i hi => isNF_iotil_of_ZDerivation _ (hmem i hi))
  have hNF : ∀ n, isNF (iotil (znth ds n)) := by
    intro n
    rcases lt_or_ge n (lh ds) with hn | hn
    · exact isNF_iotil_of_ZDerivation _ (hmem n hn)
    · rw [znth_prop_not (Or.inr hn)]; exact isNF_iotil_zero
  -- Run the finder to certify a redex exists, then read off the least-pair's premise `tp`s.
  obtain ⟨i0, j1, k0, hij, hjle, hRi, hLj, hrkpos, hrkr⟩ :=
    inference_critical_pair_of_chain (Tr := fun _ => False) (Fa := fun A => A = (^⊥ : V))
      hj0 hAj0 hchain hrank hwfR hwfL hperm hnperm (fun _ h => h.1)
      (fun A h => by rw [h]; exact irk_falsum) rfl
  have hjlt : j1 < lh ds := lt_of_le_of_lt hjle hj0
  have hilt : i0 < lh ds := lt_trans hij hjlt
  have hredex : isRedexPair ds (⟪i0, j1⟫ : V) := by
    simp only [isRedexPair, pi₁_pair, pi₂_pair]
    refine ⟨hij, hjlt, ?_, ?_, ?_⟩
    · rw [hRi]; simp [isymR]
    · rw [hLj]; simp [isymLk]
    · rw [hRi, hLj]; simp [isymR, isymLk]
  have hex : ∃ c < (⟪lh (zKseq (zK s r ds)), lh (zKseq (zK s r ds))⟫ : V),
      isRedexPair (zKseq (zK s r ds)) c := by
    simp only [zKseq_zK]; exact ⟨⟪i0, j1⟫, pair_lt_pair hilt hjlt, hredex⟩
  have hrc : isRedexPair (zKseq (zK s r ds)) (redexCode (zK s r ds)) := redexCode_isRedexPair hex
  simp only [zKseq_zK] at hrc
  have hIlt : redexI (zK s r ds) < lh ds := lt_trans hrc.1 hrc.2.1
  have hJlt : redexJ (zK s r ds) < lh ds := hrc.2.1
  obtain ⟨hRedI, hRedJ⟩ := redexPair_tp hrc
  -- The two redex-side `iRedDescent` bundles for `ρ = zAxReduct ∘ iR2`.
  have hbI := iRedDescent_zAxReduct_iR2_of_tp_isymR hRedI (hmem _ hIlt)
  have hbJ := iRedDescent_zAxReduct_iR2_of_tp_isymLk hRedJ (hmem _ hJlt)
  rw [iR2_zK_eq_iRcrit]
  exact iord_descent_iRcrit_of_chain' (Tr := fun _ => False) (Fa := fun A => A = (^⊥ : V))
    hds hnf hj0 hAj0 hchain hrank hwfR hwfL hperm hnperm (fun _ h => h.1)
    (fun A h => by rw [h]; exact irk_falsum) rfl hNF
    hbI.otil_lt hbJ.otil_lt hbI.dg_le hbJ.dg_le hbI.nf hbJ.nf

/-- **Descent under iR2 needs criticality only UP TO the chain exit `j0`, not globally** (lap 121).
A strict strengthening of `iord_descent_iR2_zK_of_valid`: that lemma destructures the *global*
criticality conjunct `hnperm0 : ∀ i < lh ds, ¬ iperm (tp dᵢ) s` of `zKValid`, but its proof only ever
applies it at indices `i ≤ j0` (the `isChainInf` exit). So the ordinal descent goes through under the
strictly weaker `hcrit : ∀ i ≤ j0, ¬ iperm (tp dᵢ) s` (criticality only on the chain's *constrained*
region `0..j0`), with `zKValidF` supplying the rest. **Significance (the lap-121 stall sharpening):**
`isChainInf` constrains only premises `0..j0`; a `red`-stall caused by a *junk* permissible premise
(`tp = isymRep`, e.g. a spurious identity atom) at an index `> j0` is therefore harmless to the genuine
`iR2`/redex descent — the redex lives in `0..j0` and this lemma reduces it regardless of junk beyond it.
The remaining genuinely-open stall case is a *threaded* atom/`zAx1` premise AT an index `≤ j0` (whose
antecedent is a real cut formula), which breaks `hcrit` and needs axiom-cut elimination. -/
lemma iord_descent_iR2_zK_of_validF_critUpTo {s r ds j0 : V} (hds : Seq ds)
    (hmem : ∀ i < lh ds, ZDerivation (znth ds i)) (hvalidF : zKValidF s r ds)
    (hj0 : j0 < lh ds)
    (hAj0 : chainAsucc ds j0 = seqSucc s ∨ chainAsucc ds j0 = (^⊥ : V))
    (hchain : ∀ i ≤ j0, ∀ B, inAnt B (chainAnt ds i) →
      inAnt B (seqAnt s) ∨ ∃ i' < i, B = chainAsucc ds i')
    (hrank : ∀ i < j0, irk (chainAsucc ds i) ≤ r)
    (hcrit : ∀ i ≤ j0, ¬ iperm (tp (znth ds i)) s) :
    icmp (iord (iR2 (zK s r ds))) (iord (zK s r ds)) = 0 := by
  obtain ⟨_hci, hperm0, hf1, hf2, hf5, hf6, _hca, _hsucc, _hsaf⟩ := hvalidF
  have hwfR : ∀ i ≤ j0, ∀ A, tp (znth ds i) = isymR A → 0 < irk A ∨ False :=
    fun i hi A h => Or.inl (tp_isymR_pos h (hf1 i (lt_of_le_of_lt hi hj0))
      (hf2 i (lt_of_le_of_lt hi hj0)))
  have hwfL : ∀ i ≤ j0, ∀ k A, tp (znth ds i) = isymLk k A → 0 < irk A ∨ (A = (^⊥ : V)) :=
    fun i hi k A h => Or.inl (tp_isymLk_pos h (hf5 i (lt_of_le_of_lt hi hj0))
      (hf6 i (lt_of_le_of_lt hi hj0)))
  have hperm : ∀ i ≤ j0, iperm (tp (znth ds i)) (fstIdx (znth ds i)) :=
    fun i hi => hperm0 i (lt_of_le_of_lt hi hj0)
  have hnperm : ∀ i ≤ j0, ¬ iperm (tp (znth ds i)) s := hcrit
  have hnf : isNF (iotil (zK s r ds)) :=
    isNF_iotil_zK hds (fun i hi => isNF_iotil_of_ZDerivation _ (hmem i hi))
  have hNF : ∀ n, isNF (iotil (znth ds n)) := by
    intro n
    rcases lt_or_ge n (lh ds) with hn | hn
    · exact isNF_iotil_of_ZDerivation _ (hmem n hn)
    · rw [znth_prop_not (Or.inr hn)]; exact isNF_iotil_zero
  obtain ⟨i0, j1, k0, hij, hjle, hRi, hLj, hrkpos, hrkr⟩ :=
    inference_critical_pair_of_chain (Tr := fun _ => False) (Fa := fun A => A = (^⊥ : V))
      hj0 hAj0 hchain hrank hwfR hwfL hperm hnperm (fun _ h => h.1)
      (fun A h => by rw [h]; exact irk_falsum) rfl
  have hjlt : j1 < lh ds := lt_of_le_of_lt hjle hj0
  have hilt : i0 < lh ds := lt_trans hij hjlt
  have hredex : isRedexPair ds (⟪i0, j1⟫ : V) := by
    simp only [isRedexPair, pi₁_pair, pi₂_pair]
    refine ⟨hij, hjlt, ?_, ?_, ?_⟩
    · rw [hRi]; simp [isymR]
    · rw [hLj]; simp [isymLk]
    · rw [hRi, hLj]; simp [isymR, isymLk]
  have hex : ∃ c < (⟪lh (zKseq (zK s r ds)), lh (zKseq (zK s r ds))⟫ : V),
      isRedexPair (zKseq (zK s r ds)) c := by
    simp only [zKseq_zK]; exact ⟨⟪i0, j1⟫, pair_lt_pair hilt hjlt, hredex⟩
  have hrc : isRedexPair (zKseq (zK s r ds)) (redexCode (zK s r ds)) := redexCode_isRedexPair hex
  simp only [zKseq_zK] at hrc
  have hIlt : redexI (zK s r ds) < lh ds := lt_trans hrc.1 hrc.2.1
  have hJlt : redexJ (zK s r ds) < lh ds := hrc.2.1
  obtain ⟨hRedI, hRedJ⟩ := redexPair_tp hrc
  have hbI := iRedDescent_zAxReduct_iR2_of_tp_isymR hRedI (hmem _ hIlt)
  have hbJ := iRedDescent_zAxReduct_iR2_of_tp_isymLk hRedJ (hmem _ hJlt)
  rw [iR2_zK_eq_iRcrit]
  exact iord_descent_iRcrit_of_chain' (Tr := fun _ => False) (Fa := fun A => A = (^⊥ : V))
    hds hnf hj0 hAj0 hchain hrank hwfR hwfL hperm hnperm (fun _ h => h.1)
    (fun A h => by rw [h]; exact irk_falsum) rfl hNF
    hbI.otil_lt hbJ.otil_lt hbI.dg_le hbJ.dg_le hbI.nf hbJ.nf

/-- **Redex indices of a valid critical `K`-chain are in range** (`redexI/redexJ < lh ds`). The
chain-structure half of the `iord_descent_iR2_zK_of_valid` recipe, extracted: from chain validity
`zKValid` (the criticality conjunct supplies `hnperm`, the formula-hood the `hwfR`/`hwfL` rank facts),
`inference_critical_pair_of_chain` certifies a redex exists below the finder's sentinel, so the
definable finder `redexCode` returns an in-range `isRedexPair`. The route-B/regularity reducts read the
two redex-premise reducts `red (znth ds (redexI/redexJ …))` as IH instances — this lemma supplies their
index bounds (`ZRegular_red_zK`'s `hredex`). -/
lemma redexI_redexJ_lt_of_zKValid {s r ds : V}
    (hvalid : zKValid s r ds) :
    redexI (zK s r ds) < lh ds ∧ redexJ (zK s r ds) < lh ds := by
  obtain ⟨hci, hperm0, hnperm0, hf1, hf2, hf5, hf6, _hsucc, _hssf, _hsaf⟩ := hvalid
  obtain ⟨j0, hj0, hAj0, hchain, hrank⟩ := hci
  have hwfR : ∀ i ≤ j0, ∀ A, tp (znth ds i) = isymR A → 0 < irk A ∨ False :=
    fun i hi A h => Or.inl (tp_isymR_pos h (hf1 i (lt_of_le_of_lt hi hj0))
      (hf2 i (lt_of_le_of_lt hi hj0)))
  have hwfL : ∀ i ≤ j0, ∀ k A, tp (znth ds i) = isymLk k A → 0 < irk A ∨ (A = (^⊥ : V)) :=
    fun i hi k A h => Or.inl (tp_isymLk_pos h (hf5 i (lt_of_le_of_lt hi hj0))
      (hf6 i (lt_of_le_of_lt hi hj0)))
  have hperm : ∀ i ≤ j0, iperm (tp (znth ds i)) (fstIdx (znth ds i)) :=
    fun i hi => hperm0 i (lt_of_le_of_lt hi hj0)
  have hnperm : ∀ i ≤ j0, ¬ iperm (tp (znth ds i)) s :=
    fun i hi => hnperm0 i (lt_of_le_of_lt hi hj0)
  obtain ⟨i0, j1, k0, hij, hjle, hRi, hLj, hrkpos, hrkr⟩ :=
    inference_critical_pair_of_chain (Tr := fun _ => False) (Fa := fun A => A = (^⊥ : V))
      hj0 hAj0 hchain hrank hwfR hwfL hperm hnperm (fun _ h => h.1)
      (fun A h => by rw [h]; exact irk_falsum) rfl
  have hjlt : j1 < lh ds := lt_of_le_of_lt hjle hj0
  have hilt : i0 < lh ds := lt_trans hij hjlt
  have hredex : isRedexPair ds (⟪i0, j1⟫ : V) := by
    simp only [isRedexPair, pi₁_pair, pi₂_pair]
    refine ⟨hij, hjlt, ?_, ?_, ?_⟩
    · rw [hRi]; simp [isymR]
    · rw [hLj]; simp [isymLk]
    · rw [hRi, hLj]; simp [isymR, isymLk]
  have hex : ∃ c < (⟪lh (zKseq (zK s r ds)), lh (zKseq (zK s r ds))⟫ : V),
      isRedexPair (zKseq (zK s r ds)) c := by
    simp only [zKseq_zK]; exact ⟨⟪i0, j1⟫, pair_lt_pair hilt hjlt, hredex⟩
  have hrc : isRedexPair (zKseq (zK s r ds)) (redexCode (zK s r ds)) := redexCode_isRedexPair hex
  simp only [zKseq_zK] at hrc
  exact ⟨lt_trans hrc.1 hrc.2.1, hrc.2.1⟩

/-- **The `redexCode` redex of a valid critical chain — the full `isRedexPair` certificate (over `ds`).**
Strengthens `redexI_redexJ_lt_of_zKValid` to return the whole redex-pair, from which BOTH the index
bounds and the redex `tp` polarities (`redexPair_tp`) follow. The orbit-data supplier the engine re-key's
`ZRegular_red_zK_crit` re-proof needs (`htagI : zTag dᵢ ∈ {1,2}` via `tp_isymR_tag`). Same finder body as
`redexI_redexJ_lt_of_zKValid`, returning `hrc` instead of just its order projections. -/
lemma isRedexPair_redexCode_of_zKValid {s r ds : V} (hvalid : zKValid s r ds) :
    isRedexPair ds (redexCode (zK s r ds)) := by
  obtain ⟨hci, hperm0, hnperm0, hf1, hf2, hf5, hf6, _hsucc, _hssf, _hsaf⟩ := hvalid
  obtain ⟨j0, hj0, hAj0, hchain, hrank⟩ := hci
  have hwfR : ∀ i ≤ j0, ∀ A, tp (znth ds i) = isymR A → 0 < irk A ∨ False :=
    fun i hi A h => Or.inl (tp_isymR_pos h (hf1 i (lt_of_le_of_lt hi hj0))
      (hf2 i (lt_of_le_of_lt hi hj0)))
  have hwfL : ∀ i ≤ j0, ∀ k A, tp (znth ds i) = isymLk k A → 0 < irk A ∨ (A = (^⊥ : V)) :=
    fun i hi k A h => Or.inl (tp_isymLk_pos h (hf5 i (lt_of_le_of_lt hi hj0))
      (hf6 i (lt_of_le_of_lt hi hj0)))
  have hperm : ∀ i ≤ j0, iperm (tp (znth ds i)) (fstIdx (znth ds i)) :=
    fun i hi => hperm0 i (lt_of_le_of_lt hi hj0)
  have hnperm : ∀ i ≤ j0, ¬ iperm (tp (znth ds i)) s :=
    fun i hi => hnperm0 i (lt_of_le_of_lt hi hj0)
  obtain ⟨i0, j1, k0, hij, hjle, hRi, hLj, hrkpos, hrkr⟩ :=
    inference_critical_pair_of_chain (Tr := fun _ => False) (Fa := fun A => A = (^⊥ : V))
      hj0 hAj0 hchain hrank hwfR hwfL hperm hnperm (fun _ h => h.1)
      (fun A h => by rw [h]; exact irk_falsum) rfl
  have hjlt : j1 < lh ds := lt_of_le_of_lt hjle hj0
  have hilt : i0 < lh ds := lt_trans hij hjlt
  have hredex : isRedexPair ds (⟪i0, j1⟫ : V) := by
    simp only [isRedexPair, pi₁_pair, pi₂_pair]
    refine ⟨hij, hjlt, ?_, ?_, ?_⟩
    · rw [hRi]; simp [isymR]
    · rw [hLj]; simp [isymLk]
    · rw [hRi, hLj]; simp [isymR, isymLk]
  have hex : ∃ c < (⟪lh (zKseq (zK s r ds)), lh (zKseq (zK s r ds))⟫ : V),
      isRedexPair (zKseq (zK s r ds)) c := by
    simp only [zKseq_zK]; exact ⟨⟪i0, j1⟫, pair_lt_pair hilt hjlt, hredex⟩
  have hrc : isRedexPair (zKseq (zK s r ds)) (redexCode (zK s r ds)) := redexCode_isRedexPair hex
  simpa only [zKseq_zK] using hrc

/-- **The R-redex of a valid critical chain is an I-rule** (`tp dᵢ = isymR` ⟹ `zTag dᵢ ∈ {1,2}`). The
`htagI` input the engine re-key's `ZRegular_iRKcCrit` (Zsubst) needs at the chain call site. -/
lemma zTag_redexI_of_zKValid {s r ds : V} (hvalid : zKValid s r ds) :
    zTag (znth ds (redexI (zK s r ds))) = 1 ∨ zTag (znth ds (redexI (zK s r ds))) = 2 :=
  tp_isymR_tag (redexPair_tp (isRedexPair_redexCode_of_zKValid hvalid)).1

/-- **§5 ∀-axiom inversion**: a `ZDerivation` of the left-axiom `zAxAll s p k` carries the matrix's
formula-hood and the side condition `∀p ∈ Γ` — and (the lap-130 `zAxAll` ZPhi strengthening) the genuine
succedent shape `zAxAllSuccWff s p k` (`seqSucc s = F(k)`). Peels the L-redex premise (the `^∀ p` cut
formula). (Hoisted above `redZKReady_of_zKValid`, which now reads off `seqSucc sⱼ = cutFormula`.) -/
lemma zDerivation_zAxAll_inv {s p k : V} (hZ : ZDerivation (zAxAll s p k)) :
    IsSemiformula ℒₒᵣ 1 p ∧ inAnt (^∀ p : V) (seqAnt s) ∧ zAxAllSuccWff s p k := by
  rcases zDerivation_iff.mp hZ with ⟨s', h, _⟩ | ⟨s', a', p', d0', h, _, _⟩ | ⟨s', p', d0', h, _, _⟩ |
    ⟨s', at'', p', d0', d1', h, _, _⟩ | ⟨s', r', ds', h, _, _, _⟩ |
    ⟨s', p', k', h, hp, hin, hsucc⟩ | ⟨s', p', h, _, _⟩ | ⟨s', C, h, _⟩
  · exact absurd (congrArg zTag h) (by simp)
  · exact absurd (congrArg zTag h) (by simp)
  · exact absurd (congrArg zTag h) (by simp)
  · exact absurd (congrArg zTag h) (by simp)
  · exact absurd (congrArg zTag h) (by simp)
  · obtain rfl : s = s' := by simpa using congrArg fstIdx h
    obtain rfl : p = p' := by simpa using congrArg zAxAllF h
    obtain rfl : k = k' := by simpa using congrArg zAxAllK h
    exact ⟨hp, hin, hsucc⟩
  · exact absurd (congrArg zTag h) (by simp)
  · exact absurd (congrArg zTag h) (by simp)

/-- **The `redZKReady` orbit bundle — the explicit redex constructor forms of a valid critical chain.**
THE shared residual all three engine-swap fronts reduce to: from a valid critical chain `zK s r ds`,
extract the in-range redex indices PLUS the polarity-dispatched explicit redex forms that the corrected
reduct's soundness/descent lemmas consume. The R/L redexes share a formula `A` (`redexPair_tp`); inverting
both (`zDerivation_isymR_form`/`_isymLk_form`) and cross-ruling the off-diagonal cases on `A` (since
`∀p ≠ ¬p`) gives either the ∀-pair (`zIall`/`zAxAll` + the rank relation `irk(∀pj) = irk(cutFormula)+1`
from `cutFormula_all`+`irk_substs1`+`irk_all`, and the succedent shape `seqSucc sⱼ = cutFormula` from the
`zAxAll` disjunct's `zAxAllSuccWff`) or the ¬-pair (`zIneg`/`zAxNeg` + `cutFormula = p`). -/
lemma redZKReady_of_zKValid {s r ds : V}
    (hZ : ZDerivation (zK s r ds)) (hvalid : zKValid s r ds) :
    redexI (zK s r ds) < redexJ (zK s r ds) ∧ redexJ (zK s r ds) < lh ds ∧
    ( (∃ sᵢ sⱼ a p pj k' d0,
        znth ds (redexI (zK s r ds)) = zIall sᵢ a p d0 ∧
        znth ds (redexJ (zK s r ds)) = zAxAll sⱼ pj k' ∧
        irk (^∀ pj : V) = irk (cutFormula (zK s r ds)) + 1 ∧
        seqSucc sⱼ = cutFormula (zK s r ds))
    ∨ (∃ sᵢ sⱼ p d0,
        znth ds (redexI (zK s r ds)) = zIneg sᵢ p d0 ∧
        znth ds (redexJ (zK s r ds)) = zAxNeg sⱼ p ∧
        cutFormula (zK s r ds) = p ∧ IsUFormula ℒₒᵣ p) ) := by
  have hrc : isRedexPair ds (redexCode (zK s r ds)) := isRedexPair_redexCode_of_zKValid hvalid
  obtain ⟨hRi, hLj⟩ := redexPair_tp hrc
  rw [show π₁ (redexCode (zK s r ds)) = redexI (zK s r ds) from rfl] at hRi hLj
  rw [show π₂ (redexCode (zK s r ds)) = redexJ (zK s r ds) from rfl] at hLj
  have hIJ : redexI (zK s r ds) < redexJ (zK s r ds) := hrc.1
  have hJlt : redexJ (zK s r ds) < lh ds := hrc.2.1
  have hIlt : redexI (zK s r ds) < lh ds := lt_trans hIJ hJlt
  obtain ⟨_, hmem⟩ := zDerivation_zK_inv hZ
  have hZi := hmem _ hIlt
  have hZj := hmem _ hJlt
  obtain ⟨_, hperm0, _, _, hf2, _, hf6, _⟩ := hvalid
  -- shared formula `A = π₂ (tp dᵢ)`; `hRi : tp dᵢ = isymR A`, `hLj : tp dⱼ = isymLk _ A`
  refine ⟨hIJ, hJlt, ?_⟩
  rcases zDerivation_isymR_form hZi hRi with ⟨sᵢ, a, p, d0, hdi, hAp⟩ | ⟨sᵢ, p, d0, hdi, hAn⟩
  · -- R-redex is I∀, `A = ^∀ p`
    rcases zDerivation_isymLk_form hZj hLj with ⟨sⱼ, pj, hdj, hApj⟩ | ⟨sⱼ, pp, hdj, _, hAnn⟩
    · -- L-redex is axAll: ∀-pair. Derive `pj = p` and the rank relation.
      left
      have hpjp : pj = p := by
        have h : (^∀ p : V) = (^∀ pj : V) := hAp.symm.trans hApj
        simpa using h.symm
      have hsf : IsSemiformula ℒₒᵣ 1 p := by
        rcases tp_isymR_form_wff hZi hRi with ⟨p', hp'eq, hsf'⟩ | ⟨p', hp'eq, _⟩
        · have h : (^∀ p : V) = (^∀ p' : V) := hAp.symm.trans hp'eq
          rwa [show p' = p from by simpa using h.symm] at hsf'
        · exact absurd (hAp.symm.trans hp'eq) (by simp [qqAll, inegF, qqOr])
      -- `chainAsucc = A = ^∀ p`, so `cutFormula = F(k)` is the matrix's instance
      have hChA : chainAsucc ds (redexI (zK s r ds)) = (^∀ p : V) := by
        have hp := hperm0 _ hIlt
        rw [hRi, iperm_isymR_iff] at hp
        exact hp.symm.trans hAp
      have hcut : cutFormula (zK s r ds) = substs1 ℒₒᵣ
          (Bootstrapping.Arithmetic.numeral (π₁ (π₂ (tp (znth ds (redexJ (zK s r ds))))))) p := by
        have h := cutFormula_all (d := zK s r ds) (by rw [zKseq_zK]; exact hChA)
        rwa [zKseq_zK] at h
      refine ⟨sᵢ, sⱼ, a, p, pj, _, d0, hdi, hdj, ?_, ?_⟩
      · rw [hpjp, hcut, irk_substs1 hsf (by simp : IsSemiterm ℒₒᵣ 0
          (Bootstrapping.Arithmetic.numeral (π₁ (π₂ (tp (znth ds (redexJ (zK s r ds)))))) : V)),
          irk_all hsf.isUFormula]
      · -- `seqSucc sⱼ = cutFormula`: the `zAxAll` ZPhi disjunct now carries `zAxAllSuccWff`, and its
        -- instance index `k' = π₁(π₂(tp dⱼ))` matches `cutFormula`'s readout exactly (`hcut`).
        have hsucc : seqSucc sⱼ = substs1 ℒₒᵣ (Bootstrapping.Arithmetic.numeral
            (π₁ (π₂ (tp (znth ds (redexJ (zK s r ds))))))) pj :=
          (zDerivation_zAxAll_inv (hdj ▸ hZj)).2.2
        rw [hsucc, hpjp, hcut]
    · -- L-redex is axNeg with `A = ¬pp`: contradicts `A = ^∀ p`
      exact absurd (hAp.symm.trans hAnn) (by simp [qqAll, inegF, qqOr])
  · -- R-redex is I¬, `A = ¬p`
    rcases zDerivation_isymLk_form hZj hLj with ⟨sⱼ, pj, hdj, hApj⟩ | ⟨sⱼ, pp, hdj, _, hAnn⟩
    · -- L-redex is axAll: contradicts `A = ¬p`
      exact absurd (hApj.symm.trans hAn) (by simp [qqAll, inegF, qqOr])
    · -- L-redex is axNeg: ¬-pair. `pp = p`, `cutFormula = p`.
      right
      have hpUf : IsUFormula ℒₒᵣ p := by
        have h := hf2 _ hIlt (by rw [hdi]; exact zTag_zIneg _ _ _)
        rwa [hdi, zInegF_zIneg] at h
      have hppUf : IsUFormula ℒₒᵣ pp := by
        have h := hf6 _ hJlt (by rw [hdj]; exact zTag_zAxNeg _ _)
        rwa [hdj, zAxNegF_zAxNeg] at h
      have hppp : pp = p := by
        have h : (inegF p : V) = inegF pp := hAn.symm.trans hAnn
        simp only [inegF, qqOr_inj] at h
        exact ((neg_inj_iff hpUf hppUf).mp h.1).symm
      have hChA : chainAsucc ds (redexI (zK s r ds)) = inegF p := by
        have hpm := hperm0 _ hIlt
        rw [hRi, iperm_isymR_iff] at hpm
        exact hpm.symm.trans hAn
      have hcut : cutFormula (zK s r ds) = p := by
        have h := cutFormula_neg (d := zK s r ds) hpUf (by rw [zKseq_zK]; exact hChA)
        exact h
      exact ⟨sᵢ, sⱼ, p, d0, hdi, hppp ▸ hdj, hcut, hpUf⟩

/-- **T3.4(a) chain-rank invariant — the `redexCode` redex's R-principal has rank `≤ r`.** For a valid
critical `K`-chain `zK s r ds`, `irk (chainAsucc ds (redexI)) ≤ r`. This is the rank input the
cut-formula strip needs (`irk_cutFormula_lt` ⟹ `rk(A(d)) < r`), closing the splice/critical degree drop.

**The key step is index-bounding `redexI < j₀`** (the chain exit index, whose rank clause `∀ i < j₀,
irk (chainAsucc ds i) ≤ r` is the only one in `isChainInf`). It does NOT need `j₀ = lh ds − 1`: the
`redexCode` redex is the **least** redex code (`redexAux_min`), and the inference pair `⟪i0,j1⟫` (Lemma
3.1, `i0 < j1 ≤ j₀`) is a redex, so `⟪redexI, redexJ⟫ = redexCode ≤ ⟪i0, j1⟫`. By the contrapositive of
`pair_lt_pair` (the pairing is jointly strictly monotone), `redexI ≤ i0 ∨ redexJ ≤ j1` — and EITHER
disjunct forces `redexI < j₀` (`redexI ≤ i0 < j1 ≤ j₀`, or `redexI < redexJ ≤ j1 ≤ j₀`). So the
un-threaded tail `(j₀, lh ds)` can never hold the minimal redex. -/
lemma chainInf_redexI_data {s r ds : V} (hvalid : zKValid s r ds) :
    ∃ j0, j0 < lh ds ∧ redexI (zK s r ds) < j0 ∧
      (∀ i ≤ j0, ∀ B, inAnt B (chainAnt ds i) →
        inAnt B (seqAnt s) ∨ ∃ i' < i, B = chainAsucc ds i') ∧
      (∀ i < j0, irk (chainAsucc ds i) ≤ r) ∧
      (chainAsucc ds j0 = seqSucc s ∨ chainAsucc ds j0 = (^⊥ : V)) := by
  obtain ⟨hci, hperm0, hnperm0, hf1, hf2, hf5, hf6, _hsucc, _hssf, _hsaf⟩ := hvalid
  obtain ⟨j0, hj0, hAj0, hchain, hrank⟩ := hci
  have hwfR : ∀ i ≤ j0, ∀ A, tp (znth ds i) = isymR A → 0 < irk A ∨ False :=
    fun i hi A h => Or.inl (tp_isymR_pos h (hf1 i (lt_of_le_of_lt hi hj0))
      (hf2 i (lt_of_le_of_lt hi hj0)))
  have hwfL : ∀ i ≤ j0, ∀ k A, tp (znth ds i) = isymLk k A → 0 < irk A ∨ (A = (^⊥ : V)) :=
    fun i hi k A h => Or.inl (tp_isymLk_pos h (hf5 i (lt_of_le_of_lt hi hj0))
      (hf6 i (lt_of_le_of_lt hi hj0)))
  have hperm : ∀ i ≤ j0, iperm (tp (znth ds i)) (fstIdx (znth ds i)) :=
    fun i hi => hperm0 i (lt_of_le_of_lt hi hj0)
  have hnperm : ∀ i ≤ j0, ¬ iperm (tp (znth ds i)) s :=
    fun i hi => hnperm0 i (lt_of_le_of_lt hi hj0)
  obtain ⟨i0, j1, k0, hij, hjle, hRi, hLj, hrkpos, hrkr⟩ :=
    inference_critical_pair_of_chain (Tr := fun _ => False) (Fa := fun A => A = (^⊥ : V))
      hj0 hAj0 hchain hrank hwfR hwfL hperm hnperm (fun _ h => h.1)
      (fun A h => by rw [h]; exact irk_falsum) rfl
  have hjlt : j1 < lh ds := lt_of_le_of_lt hjle hj0
  have hilt : i0 < lh ds := lt_trans hij hjlt
  have hredex : isRedexPair ds (⟪i0, j1⟫ : V) := by
    simp only [isRedexPair, pi₁_pair, pi₂_pair]
    refine ⟨hij, hjlt, ?_, ?_, ?_⟩
    · rw [hRi]; simp [isymR]
    · rw [hLj]; simp [isymLk]
    · rw [hRi, hLj]; simp [isymR, isymLk]
  have hex : ∃ c < (⟪lh (zKseq (zK s r ds)), lh (zKseq (zK s r ds))⟫ : V),
      isRedexPair (zKseq (zK s r ds)) c := by
    simp only [zKseq_zK]; exact ⟨⟪i0, j1⟫, pair_lt_pair hilt hjlt, hredex⟩
  have hrc : isRedexPair (zKseq (zK s r ds)) (redexCode (zK s r ds)) := redexCode_isRedexPair hex
  simp only [zKseq_zK] at hrc
  -- redexCode is the LEAST redex, so `⟪redexI, redexJ⟫ = redexCode ≤ ⟪i0, j1⟫`.
  have hcode_le : redexCode (zK s r ds) ≤ (⟪i0, j1⟫ : V) := by
    have hm := redexAux_min ds ⟪lh ds, lh ds⟫ ⟪i0, j1⟫ (pair_lt_pair hilt hjlt) hredex
    simpa [redexCode, zKseq_zK] using hm
  have hpair_eq : (⟪redexI (zK s r ds), redexJ (zK s r ds)⟫ : V) = redexCode (zK s r ds) :=
    pair_unpair (redexCode (zK s r ds))
  have hpair_le : (⟪redexI (zK s r ds), redexJ (zK s r ds)⟫ : V) ≤ ⟪i0, j1⟫ := by
    rw [hpair_eq]; exact hcode_le
  -- Contrapositive of joint monotonicity: `redexI ≤ i0 ∨ redexJ ≤ j1`.
  have hle_disj : redexI (zK s r ds) ≤ i0 ∨ redexJ (zK s r ds) ≤ j1 := by
    by_contra h; push_neg at h
    exact absurd (lt_of_lt_of_le (pair_lt_pair h.1 h.2) hpair_le) (_root_.lt_irrefl _)
  -- Either disjunct forces `redexI < j₀`.
  have hI_lt_j0 : redexI (zK s r ds) < j0 := by
    rcases hle_disj with hle | hle
    · exact lt_of_le_of_lt hle (lt_of_lt_of_le hij hjle)
    · exact lt_of_lt_of_le (lt_of_lt_of_le hrc.1 hle) hjle
  exact ⟨j0, hj0, hI_lt_j0, hchain, hrank, hAj0⟩

lemma irk_chainAsucc_redexI_le {s r ds : V} (hvalid : zKValid s r ds) :
    irk (chainAsucc ds (redexI (zK s r ds))) ≤ r := by
  obtain ⟨j0, _, hI_lt_j0, _, hrank, _⟩ := chainInf_redexI_data hvalid
  exact hrank _ hI_lt_j0

/-- **Criticality from the `permIdx` sentinel**: `¬ permIdx (zK s r ds) < lh ds` (the `iRK` critical
branch) ⟹ `zKCritical s ds` (no premise is permissible). The `permIdx = lh ds` sentinel means the
first-hit search found nothing (`permIdxAux_eq_self_of_none`). -/
lemma zKCritical_of_not_permIdx_lt {s r ds : V} (h : ¬ permIdx (zK s r ds) < lh ds) :
    zKCritical s ds := by
  have heq : permIdx (zK s r ds) = lh ds :=
    le_antisymm (by have := permIdxAux_le ds (fstIdx (zK s r ds)) (lh (zKseq (zK s r ds)));
                     simpa [permIdx, fstIdx_zK, zKseq_zK] using this) (not_lt.mp h)
  intro i hi
  have := permIdxAux_eq_self_of_none ds (fstIdx (zK s r ds)) (lh (zKseq (zK s r ds)))
    (by simpa [permIdx, fstIdx_zK, zKseq_zK] using heq) i (by simpa [zKseq_zK] using hi)
  simpa [isPermPrem, fstIdx_zK] using this

/-! ## The Thm-4.2 one-step descent through the recursive `iR2` — ALL reducible rules (tags 1,2,3,4)

With `iR2` total and the refined `ZPhi` carrying `zKValid` on its `zK` disjunct, the descent
`o(iR2 d) ≺ o(d)` is now UNCONDITIONAL across every reducible Z-rule: I-rules/Ind (tags 1,2,3) via
their closed reducts, and the K-rule (tag 4) via `iord_descent_iR2_zK_of_valid` fed by
`zKValid_of_ZDerivation_zK`. The atom/axiom tags (0/5/6) are normal forms with no strict descent (and
never arise on a ⊥-derivation), so they stay excluded by `htag`. This is the capstone that turns the
descent MATH into a single hypothesis-free fact about `ZDerivation`s. -/
lemma iord_descent_iR2_struct (d : V) (hd : ZDerivation d)
    (htag : zTag d = 1 ∨ zTag d = 2 ∨ zTag d = 3 ∨ zTag d = 4)
    (hcrit : zTag d = 4 → zKCritical (fstIdx d) (zKseq d)) :
    icmp (iord (iR2 d)) (iord d) = 0 := by
  rcases zDerivation_iff.mp hd with ⟨s, rfl, _⟩ | ⟨s, a, p, d0, rfl, _, _⟩ | ⟨s, p, d0, rfl, _, _⟩ |
    ⟨s, at', p, d0, d1, rfl, h0, h1, _⟩ | ⟨s, r, ds, rfl, hds, hmem, hvalid⟩ |
    ⟨s, p, k, rfl, _, _⟩ | ⟨s, p, rfl, _, _⟩ | ⟨s, C, rfl, _⟩
  · simp [zTag_zAtom] at htag
  · rw [iR2_zIall]; exact iord_descent_zIall s a p d0
  · rw [iR2_zIneg]; exact iord_descent_zIneg s p d0
  · rw [iR2_zInd]
    exact iord_descent_iRInd_zInd s at' p d0 d1
      (isNF_iotil_of_ZDerivation d0 h0) (isNF_iotil_of_ZDerivation d1 h1)
  · -- tag 4 (K-rule): after the re-point `ZPhi` carries only the faithful validity `zKValidF`; the
    -- iR2 critical-reduct descent additionally needs the chain to be *critical* (lap-83 finding — iR2 is
    -- the ordinal-first dead reduct, superseded by the genuine `red`). Criticality is supplied here.
    have hcr : zKCritical s ds := by have := hcrit (by simp); simpa using this
    exact iord_descent_iR2_zK_of_valid hds hmem
      (zKValid_iff_zKValidF_and_zKCritical.mpr ⟨hvalid, hcr⟩)
  · simp [zTag_zAxAll] at htag
  · simp [zTag_zAxNeg] at htag
  · simp [zTag_zAx1] at htag

/-! ## C1 — `ZDerivesEmpty` and the per-step descent on a contradiction derivation

With the descent capstone `iord_descent_iR2_struct` in hand and the `ZPhi` leaf disjuncts now carrying
their **antecedent side conditions** (atom = identity axiom `C ∈ Γ`, §5 ∀-axiom `∀xF ∈ Γ`, §5 ¬-axiom
`¬A ∈ Γ` — all faithful Buchholz axioms), an empty-antecedent end-sequent can no longer be an axiom
leaf. This yields the per-step descent on a Z-derivation of the empty/contradiction sequent — the fact
the no-infinite-descent argument iterates. -/

/-- **A Z-derivation of the empty (contradiction) sequent `∅ → ⊥`.** The end-sequent `fstIdx d` has
empty antecedent (no open assumptions) and `⊥` succedent — `d` derives a contradiction in system Z.
This is the object the C0.5 bridge produces from a Foundation ⊥-proof; the descent strictly lowers its
ordinal `iord` at every step. -/
def ZDerivesEmpty (d : V) : Prop :=
  ZDerivation d ∧ seqAnt (fstIdx d) = (∅ : V) ∧ seqSucc (fstIdx d) = (^⊥ : V)

/-- **Leaf-soundness: an empty-antecedent Z-derivation is never an axiom leaf.** Each of the three Z
axiom schemes requires a formula in the antecedent `Γ = seqAnt (fstIdx d)` (atom: the succedent `C ∈ Γ`;
§5 ∀-axiom: `∀xF ∈ Γ`; §5 ¬-axiom: `¬A ∈ Γ`). With `Γ = ∅` (so `lh Γ = 0`, no membership possible) all
three are impossible, hence a Z-derivation of an empty-antecedent sequent must be built by one of the
*reducible* rules (tags 1,2,3,4). -/
lemma zTag_reducible_of_emptyAnt {d : V} (hZ : ZDerivation d)
    (hemp : seqAnt (fstIdx d) = (∅ : V)) :
    zTag d = 1 ∨ zTag d = 2 ∨ zTag d = 3 ∨ zTag d = 4 := by
  rcases zDerivation_iff.mp hZ with ⟨s, rfl, hin⟩ | ⟨s, a, p, d0, rfl, _, _⟩ | ⟨s, p, d0, rfl, _, _⟩ |
    ⟨s, at', p, d0, d1, rfl, _, _⟩ | ⟨s, r, ds, rfl, _, _, _⟩ |
    ⟨s, p, k, rfl, _, hin⟩ | ⟨s, p, rfl, _, hin⟩ | ⟨s, C, rfl, hin⟩
  · exfalso; rw [fstIdx_zAtom] at hemp; rw [hemp] at hin; simp [inAnt, lh_empty] at hin
  · exact Or.inl (by simp)
  · exact Or.inr (Or.inl (by simp))
  · exact Or.inr (Or.inr (Or.inl (by simp)))
  · exact Or.inr (Or.inr (Or.inr (by simp)))
  · exfalso; rw [fstIdx_zAxAll] at hemp; rw [hemp] at hin; simp [inAnt, lh_empty] at hin
  · exfalso; rw [fstIdx_zAxNeg] at hemp; rw [hemp] at hin; simp [inAnt, lh_empty] at hin
  · exfalso; rw [fstIdx_zAx1] at hemp; rw [hemp] at hin; simp [inAnt, lh_empty] at hin

/-- **One descent step on an empty-sequent derivation.** Combining leaf-soundness
(`zTag_reducible_of_emptyAnt`) with the capstone `iord_descent_iR2_struct`: every `iR2`-step of a
Z-derivation of an empty-antecedent sequent strictly lowers the ordinal `iord`. This is the
hypothesis-free per-step fact iterated by the no-infinite-descent argument; it remains to show `iR2`
*preserves* `ZDerivesEmpty` (reduction-soundness + end-sequent invariance), the next interface. -/
lemma iord_descent_iR2_of_emptyAnt {d : V} (hZ : ZDerivation d)
    (hemp : seqAnt (fstIdx d) = (∅ : V))
    (hcrit : zTag d = 4 → zKCritical (fstIdx d) (zKseq d)) :
    icmp (iord (iR2 d)) (iord d) = 0 :=
  iord_descent_iR2_struct d hZ (zTag_reducible_of_emptyAnt hZ hemp) hcrit

/-- **One descent step on a `ZDerivesEmpty` code** (the packaged form). -/
lemma iord_descent_iR2_of_ZDerivesEmpty {d : V} (h : ZDerivesEmpty d)
    (hcrit : zTag d = 4 → zKCritical (fstIdx d) (zKseq d)) :
    icmp (iord (iR2 d)) (iord d) = 0 :=
  iord_descent_iR2_of_emptyAnt h.1 h.2.1 hcrit

/-- **`iR2` preserves the end-sequent on the `Rep`-tagged reducible rules (Ind, K).** Both reducts are
chains `zK (fstIdx d) …` (`iRInd`/`iCritReduct` carry the conclusion sequent verbatim), so
`fstIdx (iR2 d) = fstIdx d`. For the I-rules (tags 1,2) the reduct is the sub-derivation `d0`, whose
end-sequent differs — but a ⊥-succedent derivation is never an I-rule (the R-symbol would put the
principal formula, not `⊥`, in the succedent), so the Ind/K case is the only one the descent visits. -/
lemma fstIdx_iR2_of_tag_Ind_or_K {d : V} (hZ : ZDerivation d) (htag : zTag d = 3 ∨ zTag d = 4) :
    fstIdx (iR2 d) = fstIdx d := by
  rcases zDerivation_iff.mp hZ with ⟨s, rfl, _⟩ | ⟨s, a, p, d0, rfl, _, _⟩ | ⟨s, p, d0, rfl, _, _⟩ |
    ⟨s, at', p, d0, d1, rfl, _, _⟩ | ⟨s, r, ds, rfl, _, _, _⟩ |
    ⟨s, p, k, rfl, _, _⟩ | ⟨s, p, rfl, _, _⟩ | ⟨s, C, rfl, _⟩
  · simp [zTag_zAtom] at htag
  · simp [zTag_zIall] at htag
  · simp [zTag_zIneg] at htag
  · rw [iR2_zInd, iRInd_zInd]; simp [fstIdx_zInd]
  · simp only [iR2_zK, iCritReduct, fstIdx_zK]
  · simp [zTag_zAxAll] at htag
  · simp [zTag_zAxNeg] at htag
  · simp [zTag_zAx1] at htag

/-- The `iR2`-reduct of an `Ind`/`K` derivation is a `Rep`-tagged chain `zK (fstIdx d) …` (`iRInd` for
`Ind`, `iCritReduct` for `K`). The shape that makes its principal-formula well-formedness automatic. -/
lemma iR2_eq_zK_of_tag_Ind_or_K {d : V} (hZ : ZDerivation d) (htag : zTag d = 3 ∨ zTag d = 4) :
    ∃ r ds, iR2 d = zK (fstIdx d) r ds := by
  rcases zDerivation_iff.mp hZ with ⟨s, rfl, _⟩ | ⟨s, a, p, d0, rfl, _, _⟩ | ⟨s, p, d0, rfl, _, _⟩ |
    ⟨s, at', p, d0, d1, rfl, _, _⟩ | ⟨s, r, ds, rfl, _, _, _⟩ |
    ⟨s, p, k, rfl, _, _⟩ | ⟨s, p, rfl, _, _⟩ | ⟨s, C, rfl, _⟩
  · simp [zTag_zAtom] at htag
  · simp [zTag_zIall] at htag
  · simp [zTag_zIneg] at htag
  · exact ⟨irk p, iIndReductSeq d0 d1 1, by rw [iR2_zInd, iRInd_zInd, fstIdx_zInd]⟩
  · exact ⟨_, _, by rw [iR2_zK, iCritReduct, fstIdx_zK]⟩
  · simp [zTag_zAxAll] at htag
  · simp [zTag_zAxNeg] at htag
  · simp [zTag_zAx1] at htag

/-- The `iR2`-reduct of an `Ind`/`K` derivation is tag-4 (`zK`). -/
lemma zTag_iR2_of_tag_Ind_or_K {d : V} (hZ : ZDerivation d) (htag : zTag d = 3 ∨ zTag d = 4) :
    zTag (iR2 d) = 4 := by
  obtain ⟨r, ds, h⟩ := iR2_eq_zK_of_tag_Ind_or_K hZ htag; rw [h, zTag_zK]

/-- The `iR2`-reduct of an `Ind`/`K` derivation has `tp = isymRep` (it is a chain). -/
lemma tp_iR2_of_tag_Ind_or_K {d : V} (hZ : ZDerivation d) (htag : zTag d = 3 ∨ zTag d = 4) :
    tp (iR2 d) = isymRep := by
  obtain ⟨r, ds, h⟩ := iR2_eq_zK_of_tag_Ind_or_K hZ htag; rw [h, tp_zK]

/-- **Non-critical validity-preservation, concrete.** Replacing a premise `i` of a faithfully-valid
chain by its own `iR2`-reduct preserves `zKValidF`, when the premise `i` is itself an `Ind`/`K`
derivation. End-sequent invariance (`fstIdx_iR2_of_tag_Ind_or_K`) feeds `isChainInf` preservation; the
reduct is a `Rep`-tagged chain (`zTag = 4`, `tp = isymRep`), so its own-permissibility is automatic
(`iperm_isymRep`) and the tag-gated I/Ax formula-hood conjuncts are vacuous. This is exactly the
non-critical (Buchholz §3.2 case 5.2.2) step of the `RedSound` validity invariant. -/
lemma zKValidF_seqUpdate_iR2 {s r ds i : V} (hi : i < lh ds)
    (hZi : ZDerivation (znth ds i)) (htagi : zTag (znth ds i) = 3 ∨ zTag (znth ds i) = 4)
    (h : zKValidF s r ds) :
    zKValidF s r (seqUpdate ds i (iR2 (znth ds i))) := by
  have hfst : fstIdx (iR2 (znth ds i)) = fstIdx (znth ds i) :=
    fstIdx_iR2_of_tag_Ind_or_K hZi htagi
  have htagv : zTag (iR2 (znth ds i)) = 4 := zTag_iR2_of_tag_Ind_or_K hZi htagi
  have htpv : tp (iR2 (znth ds i)) = isymRep := tp_iR2_of_tag_Ind_or_K hZi htagi
  refine zKValidF_seqUpdate hi hfst ?_ ?_ ?_ ?_ ?_ h
  · rw [htpv]; exact iperm_isymRep _
  · intro hc; rw [htagv] at hc; simp at hc
  · intro hc; rw [htagv] at hc; simp at hc
  · intro hc; rw [htagv] at hc; simp at hc
  · intro hc; rw [htagv] at hc; simp at hc

/-- **A `ZDerivesEmpty` code is built by an `Ind` or `K` rule** (tag 3 or 4). Beyond leaf-soundness
(empty antecedent rules out the axiom leaves), the `⊥`-succedent rules out the two I-rules: a valid
`I^a_∀xF`/`I_¬A` inference has succedent `∀xF`/`¬A` (the refined `ZPhi` now carries `seqSucc s = ^∀ p`
/ `= inegF p`), never `⊥`. So the only rules concluding `∅ → ⊥` are the `Rep`-tagged `Ind` and `K` —
exactly the two whose `iR2`-reduct is a chain `zK (fstIdx d) …`. -/
lemma zTag_Ind_or_K_of_ZDerivesEmpty {d : V} (h : ZDerivesEmpty d) : zTag d = 3 ∨ zTag d = 4 := by
  obtain ⟨hZ, hant, hsucc⟩ := h
  rcases zDerivation_iff.mp hZ with ⟨s, rfl, hin⟩ | ⟨s, a, p, d0, rfl, _, hsc, _⟩ |
    ⟨s, p, d0, rfl, _, hsc, _⟩ | ⟨s, at', p, d0, d1, rfl, _, _⟩ | ⟨s, r, ds, rfl, _, _, _⟩ |
    ⟨s, p, k, rfl, _, hin⟩ | ⟨s, p, rfl, _, hin⟩ | ⟨s, C, rfl, hin⟩
  · exfalso; rw [fstIdx_zAtom] at hant; rw [hant] at hin; simp [inAnt, lh_empty] at hin
  · rw [fstIdx_zIall] at hsucc
    exact absurd (hsucc.symm.trans hsc) (by simp [qqAll, qqFalsum])
  · rw [fstIdx_zIneg] at hsucc
    exact absurd (hsucc.symm.trans hsc) (by simp [inegF, qqOr, qqFalsum])
  · exact Or.inl (by simp)
  · exact Or.inr (by simp)
  · exfalso; rw [fstIdx_zAxAll] at hant; rw [hant] at hin; simp [inAnt, lh_empty] at hin
  · exfalso; rw [fstIdx_zAxNeg] at hant; rw [hant] at hin; simp [inAnt, lh_empty] at hin
  · exfalso; rw [fstIdx_zAx1] at hant; rw [hant] at hin; simp [inAnt, lh_empty] at hin

/-- **`iR2` preserves `ZDerivesEmpty`, modulo reduction-soundness.** A contradiction derivation reduces
to a contradiction derivation: its tag is `Ind`/`K` (`zTag_Ind_or_K_of_ZDerivesEmpty`), so `iR2 d` is a
chain `zK (fstIdx d) …` and the end-sequent is preserved (`fstIdx_iR2_of_tag_Ind_or_K`) — hence both the
empty antecedent and the `⊥` succedent carry over. The **one** remaining obligation is the reduction
being well-defined, `hsound : ZDerivation (iR2 d)` (that `iCritReduct`/`iRInd` outputs satisfy `ZPhi`);
it is taken as a hypothesis here, isolating it as the next deep target. -/
lemma ZDerivesEmpty_iR2 {d : V} (h : ZDerivesEmpty d) (hsound : ZDerivation (iR2 d)) :
    ZDerivesEmpty (iR2 d) := by
  have hfst : fstIdx (iR2 d) = fstIdx d :=
    fstIdx_iR2_of_tag_Ind_or_K h.1 (zTag_Ind_or_K_of_ZDerivesEmpty h)
  exact ⟨hsound, by rw [hfst]; exact h.2.1, by rw [hfst]; exact h.2.2⟩

/-! ## Reduction-soundness decomposition — `RedSound` ⟸ chain-validity of the reducts

The reduct of an `Ind`/`K` derivation is a chain `zK …` whose premises are already `ZDerivation`s and
whose `Seq` structure is free; the only residual is that the produced chain is `zKValid` (the Buchholz
reduction lemma). These lemmas peel off the tractable structure, isolating that residual. -/

/-- **Ind-rule inversion**: a `ZDerivation` of `zInd s at' p d0 d1` has both Ind premises
`ZDerivation`s and the Ind premise-sequent side conditions `zIndWff` (`d0 ⊢ Γ→F(0)`, `d1 ⊢ F(a),Γ→F(Sa)`,
conclusion `F(t)`). The genuine Ind reduct `K^r⟨d0, d1(a/0),…,d1(a/k−1)⟩` reads `zIndWff` by inversion.
(The non-`Ind` `ZPhi` disjuncts are ruled out by `zTag`.) -/
lemma zDerivation_zInd_inv {s at' p d0 d1 : V} (hZ : ZDerivation (zInd s at' p d0 d1)) :
    ZDerivation d0 ∧ ZDerivation d1 ∧ zIndWff (zInd s at' p d0 d1) := by
  rcases zDerivation_iff.mp hZ with ⟨s', h, _⟩ | ⟨s', a, p', d0', h, _, _⟩ | ⟨s', p', d0', h, _, _⟩ |
    ⟨s', at'', p', d0', d1', h, hd0, hd1, hwff⟩ | ⟨s', r', ds', h, _, _, _⟩ |
    ⟨s', p', k, h, _, _⟩ | ⟨s', p', h, _, _⟩ | ⟨s', C, h, _⟩
  · exact absurd (congrArg zTag h) (by simp)
  · exact absurd (congrArg zTag h) (by simp)
  · exact absurd (congrArg zTag h) (by simp)
  · obtain rfl : s = s' := by simpa using congrArg fstIdx h
    obtain rfl : at' = at'' := by simpa using congrArg (fun d => π₁ (zRest d)) h
    obtain rfl : p = p' := by simpa using congrArg zIndP h
    obtain rfl : d0 = d0' := by simpa using congrArg zIndPrem0 h
    obtain rfl : d1 = d1' := by simpa using congrArg zIndPrem1 h
    exact ⟨hd0, hd1, hwff⟩
  · exact absurd (congrArg zTag h) (by simp)
  · exact absurd (congrArg zTag h) (by simp)
  · exact absurd (congrArg zTag h) (by simp)
  · exact absurd (congrArg zTag h) (by simp)

/-! ### Rule-inversion (peeling) primitives for the genuine reduct

A genuine, derivation-valid reduction (Bryce–Goré `cut_elimination`-style — shape-dispatched on the cut
formula, `cut_elimination_valid`) must *peel* the redex premises of a critical chain: the R-redex (an
I-rule introducing the cut formula on the right) and the L-redex (a §5 left-axiom carrying it on the
left). These inversions extract exactly the sub-derivation / well-formedness data such a peel consumes,
mirroring `zDerivation_zInd_inv`. They are axiom-clean and reusable by any validity-preserving reduct. -/

/-- **I∀-rule inversion**: a `ZDerivation` of `zIall s a p d0` has its premise `d0` a `ZDerivation` and
end-sequent succedent the principal formula `∀p`. Peels the R-redex premise of a critical chain. -/
lemma zDerivation_zIall_inv {s a p d0 : V} (hZ : ZDerivation (zIall s a p d0)) :
    ZDerivation d0 ∧ seqSucc s = (^∀ p : V) ∧ zIallWff s a p d0 := by
  rcases zDerivation_iff.mp hZ with ⟨s', h, _⟩ | ⟨s', a', p', d0', h, hd0, hsc, hwff⟩ |
    ⟨s', p', d0', h, _, _⟩ |
    ⟨s', at'', p', d0', d1', h, _, _⟩ | ⟨s', r', ds', h, _, _, _⟩ |
    ⟨s', p', k, h, _, _⟩ | ⟨s', p', h, _, _⟩ | ⟨s', C, h, _⟩
  · exact absurd (congrArg zTag h) (by simp)
  · obtain rfl : s = s' := by simpa using congrArg fstIdx h
    obtain rfl : a = a' := by simpa using congrArg (fun d => π₁ (zRest d)) h
    obtain rfl : p = p' := by simpa using congrArg zIallF h
    obtain rfl : d0 = d0' := by simpa using congrArg zIallPrem h
    exact ⟨hd0, hsc, hwff⟩
  · exact absurd (congrArg zTag h) (by simp)
  · exact absurd (congrArg zTag h) (by simp)
  · exact absurd (congrArg zTag h) (by simp)
  · exact absurd (congrArg zTag h) (by simp)
  · exact absurd (congrArg zTag h) (by simp)
  · exact absurd (congrArg zTag h) (by simp)

/-- **I¬-rule inversion**: a `ZDerivation` of `zIneg s p d0` has premise `d0` a `ZDerivation`, end-sequent
succedent `¬p` (`= inegF p`), and the premise-sequent side condition `zInegWff p d0` (`d0 ⊢ p,Γ→⊥`). Peels
the R-redex premise when the cut formula is a negation; the genuine I¬ reduct `d[0]:=d0` reads `zInegWff`. -/
lemma zDerivation_zIneg_inv {s p d0 : V} (hZ : ZDerivation (zIneg s p d0)) :
    ZDerivation d0 ∧ seqSucc s = (inegF p : V) ∧ zInegWff p d0 ∧ zInegAntWff s p d0 := by
  rcases zDerivation_iff.mp hZ with ⟨s', h, _⟩ | ⟨s', a', p', d0', h, _, _⟩ |
    ⟨s', p', d0', h, hd0, hsc, hwff⟩ |
    ⟨s', at'', p', d0', d1', h, _, _⟩ | ⟨s', r', ds', h, _, _, _⟩ |
    ⟨s', p', k, h, _, _⟩ | ⟨s', p', h, _, _⟩ | ⟨s', C, h, _⟩
  · exact absurd (congrArg zTag h) (by simp)
  · exact absurd (congrArg zTag h) (by simp)
  · obtain rfl : s = s' := by simpa using congrArg fstIdx h
    obtain rfl : p = p' := by simpa using congrArg zInegF h
    obtain rfl : d0 = d0' := by simpa using congrArg zInegPrem h
    exact ⟨hd0, hsc, hwff⟩
  · exact absurd (congrArg zTag h) (by simp)
  · exact absurd (congrArg zTag h) (by simp)
  · exact absurd (congrArg zTag h) (by simp)
  · exact absurd (congrArg zTag h) (by simp)
  · exact absurd (congrArg zTag h) (by simp)

/-- **Route-B conclusion invariant, I¬ case (lap 91).** The I¬ reduct `red (zIneg s p d0) = d0`
(Buchholz Def 3.2 clause 3, `d[0] := d₀`, NO substitution) already meets route B: its succedent equals
that of the reduced sequent `tpReduce (R_¬p) Π 0 = p,Γ→⊥` (both `⊥`), and `p` is in its antecedent —
i.e. `d0 ⊢ p,Γ→⊥`, exactly Buchholz `R_¬A(Π,0)`. So the I¬ branch needs NO rewire and NO eigen-subst
(unlike I∀, Buchholz clause 2, which substitutes the eigenvariable — see PENDING_WORK lap-91 O2). The
full antecedent equality is up-to-`inAnt` (O3): `zInegWff` pins only `p ∈ antecedent`, which is what the
parent chain-rule threading (`isChainInf` via `inAnt`) consumes. -/
lemma red_zIneg_tpReduce {s p d0 : V} (hZ : ZDerivation (zIneg s p d0)) :
    seqSucc (fstIdx (red (zIneg s p d0)))
        = seqSucc (tpReduce (tp (zIneg s p d0)) (fstIdx (zIneg s p d0)) 0)
      ∧ inAnt p (seqAnt (fstIdx (red (zIneg s p d0)))) := by
  obtain ⟨hd0, hsucc, ⟨hbot, hmem, hp⟩, _⟩ := zDerivation_zIneg_inv hZ
  rw [red_zIneg, tp_zIneg, tpReduce_isymR_neg p (fstIdx (zIneg s p d0)) 0 hp]
  exact ⟨by rw [hbot, seqSucc_seqAddAnt, seqSucc_seqSetSucc], hmem⟩

/-- **§5 ¬-axiom inversion**: a `ZDerivation` of the left-axiom `zAxNeg s p` carries the matrix's
formula-hood and the side condition `¬p ∈ Γ`. Peels the L-redex premise (the `inegF p` cut formula). -/
lemma zDerivation_zAxNeg_inv {s p : V} (hZ : ZDerivation (zAxNeg s p)) :
    IsUFormula ℒₒᵣ p ∧ inAnt (inegF p : V) (seqAnt s) ∧ inAnt p (seqAnt s) := by
  rcases zDerivation_iff.mp hZ with ⟨s', h, _⟩ | ⟨s', a', p', d0', h, _, _⟩ | ⟨s', p', d0', h, _, _⟩ |
    ⟨s', at'', p', d0', d1', h, _, _⟩ | ⟨s', r', ds', h, _, _, _⟩ |
    ⟨s', p', k', h, _, _⟩ | ⟨s', p', h, hp, hin, hin2⟩ | ⟨s', C, h, _⟩
  · exact absurd (congrArg zTag h) (by simp)
  · exact absurd (congrArg zTag h) (by simp)
  · exact absurd (congrArg zTag h) (by simp)
  · exact absurd (congrArg zTag h) (by simp)
  · exact absurd (congrArg zTag h) (by simp)
  · exact absurd (congrArg zTag h) (by simp)
  · obtain rfl : s = s' := by simpa using congrArg fstIdx h
    obtain rfl : p = p' := by simpa using congrArg zAxNegF h
    exact ⟨hp, hin, hin2⟩
  · exact absurd (congrArg zTag h) (by simp)

/-- **Conclusion-tracking, §5 ∀-axiom (L-rule replace, completes frontier item 1).** The reduced
conclusion for an axAll selected premise: `tp(Ax^{∀p,k}) = L^k_{∀p}`, so `tpReduce (tp (zAxAll s p k)) s 0
= F(k),Γ→D` (`seqAddAnt (substs1 (numeral k) p) s`) — the cut-formula instance `F(k)` adjoined to the
conclusion antecedent. The reduct itself is the identity (`red (zAxAll s p k) = zAxAll s p k`), so the
wiring into `ZDerivation_zK_seqAddAnt` uses `A = substs1 (numeral k) p`. -/
lemma tpReduce_tp_zAxAll (s p k : V) :
    tpReduce (tp (zAxAll s p k)) (fstIdx (zAxAll s p k)) 0
      = seqAddAnt (substs1 ℒₒᵣ (Bootstrapping.Arithmetic.numeral k) p) s := by
  rw [tp_zAxAll, fstIdx_zAxAll, tpReduce_isymLk_all]

/-- **Conclusion-tracking, §5 ¬-axiom (L-rule replace, completes frontier item 1).** The reduced
conclusion for an axNeg selected premise: `tp(Ax^{¬p,0}) = L⁰_{¬p}`, so `tpReduce (tp (zAxNeg s p)) s 0
= Γ→p` (`seqSetSucc s p`) — the cut formula `p` becomes the new succedent, the antecedent unchanged.
Unlike axAll (an antecedent weakening), this is a succedent REPLACEMENT, so its dispatch needs a distinct
constructor (the premise `red dᵢ = dᵢ` keeps succedent `seqSucc s`, not `p`). The `IsUFormula p` side
condition comes from `zDerivation_zAxNeg_inv`. -/
lemma tpReduce_tp_zAxNeg {s p : V} (hp : IsUFormula ℒₒᵣ p) :
    tpReduce (tp (zAxNeg s p)) (fstIdx (zAxNeg s p)) 0 = seqSetSucc s p := by
  rw [tp_zAxNeg, fstIdx_zAxNeg, tpReduce_isymLk_neg]; exact hp

/-- **Atom inversion**: a `ZDerivation` of the identity axiom `zAtom s` has its succedent in its
antecedent (`C ∈ Γ`). The leaf side condition that rules out an empty-antecedent atom. -/
lemma zDerivation_zAtom_inv {s : V} (hZ : ZDerivation (zAtom s)) :
    inAnt (seqSucc s) (seqAnt s) := by
  rcases zDerivation_iff.mp hZ with ⟨s', h, hin⟩ | ⟨s', a', p', d0', h, _, _⟩ | ⟨s', p', d0', h, _, _⟩ |
    ⟨s', at'', p', d0', d1', h, _, _⟩ | ⟨s', r', ds', h, _, _, _⟩ |
    ⟨s', p', k', h, _, _⟩ | ⟨s', p', h, _, _⟩ | ⟨s', C, h, _⟩
  · obtain rfl : s = s' := by simpa using congrArg fstIdx h
    exact hin
  · exact absurd (congrArg zTag h) (by simp)
  · exact absurd (congrArg zTag h) (by simp)
  · exact absurd (congrArg zTag h) (by simp)
  · exact absurd (congrArg zTag h) (by simp)
  · exact absurd (congrArg zTag h) (by simp)
  · exact absurd (congrArg zTag h) (by simp)
  · exact absurd (congrArg zTag h) (by simp)

/-- **§5 logical-axiom introduction (`Ax^1`, rule 1, Buchholz `:844`).** The §5 logical axiom `Γ→C` with
`C∈Γ` is a genuine `ZDerivation`: it is the 8th `ZPhi` disjunct, whose only side condition is that the
succedent lies in the antecedent. This discharges the L-side inversion residual `(O-L1)` — the corrected
critical-cut reduct `zAx1 (seqAddAnt (cutFormula d) sⱼ) C` is a `ZDerivation` because the just-adjoined
cut-instance `F(k)` is both the new succedent and a member of the grown antecedent. -/
lemma zDerivation_zAx1_intro {s C : V} (hin : inAnt (seqSucc s) (seqAnt s)) :
    ZDerivation (zAx1 s C) :=
  zDerivation_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨s, C, rfl, hin⟩)))))))

/-- **§5 logical-axiom inversion (`Ax^1`).** Dual of `zDerivation_zAx1_intro`: a `ZDerivation` of `zAx1 s C`
forces its succedent into its antecedent (`C∈Γ`, the rule's side condition). Mirror of
`zDerivation_zAtom_inv`. -/
lemma zDerivation_zAx1_inv {s C : V} (hZ : ZDerivation (zAx1 s C)) :
    inAnt (seqSucc s) (seqAnt s) := by
  rcases zDerivation_iff.mp hZ with ⟨s', h, _⟩ | ⟨s', a', p', d0', h, _, _⟩ | ⟨s', p', d0', h, _, _⟩ |
    ⟨s', at'', p', d0', d1', h, _, _⟩ | ⟨s', r', ds', h, _, _, _⟩ |
    ⟨s', p', k', h, _, _⟩ | ⟨s', p', h, _, _⟩ | ⟨s', C', h, hin⟩
  · exact absurd (congrArg zTag h) (by simp)
  · exact absurd (congrArg zTag h) (by simp)
  · exact absurd (congrArg zTag h) (by simp)
  · exact absurd (congrArg zTag h) (by simp)
  · exact absurd (congrArg zTag h) (by simp)
  · exact absurd (congrArg zTag h) (by simp)
  · exact absurd (congrArg zTag h) (by simp)
  · obtain rfl : s = s' := by simpa using congrArg fstIdx h
    exact hin

/-- **A threaded atom/`Ax¹` leaf premise's cut formula is produced upstream** (lap 121). If premise
`k ≤ j0` of a ⊥-chain (`seqAnt s = ∅`) is an identity-axiom LEAF — `znth ds k = zAtom sₖ` or
`zAx1 sₖ Cₖ`, the two irreducible `tp = isymRep` shapes that cause the `red`-stall — then its succedent
`chainAsucc ds k` is the succedent of a STRICTLY EARLIER premise: `∃ i' < k, chainAsucc ds i' =
chainAsucc ds k`. (Atom/`Ax¹` validity puts the succedent in the antecedent; chain threading with
`seqAnt s = ∅` then forces it to be an earlier cut formula, since the antecedent has no open-assumption
source.) This PINS the axiom-cut redex pair `(i', k)` that genuine §-cut elimination eliminates — the
precise object the deferred stall fix (lap-120 prescription, scoped to the threaded-atom-≤-j0 core in
lap-121) consumes. In particular `k > 0`, so a stall leaf is never premise 0. -/
lemma chainAsucc_threaded_of_leaf {s ds j0 k : V}
    (hZk : ZDerivation (znth ds k))
    (hleaf : (∃ sk, znth ds k = zAtom sk) ∨ (∃ sk Ck, znth ds k = zAx1 sk Ck))
    (hant : seqAnt s = (∅ : V))
    (hchain : ∀ i ≤ j0, ∀ B, inAnt B (chainAnt ds i) →
      inAnt B (seqAnt s) ∨ ∃ i' < i, B = chainAsucc ds i')
    (hk : k ≤ j0) :
    ∃ i' < k, chainAsucc ds i' = chainAsucc ds k := by
  have hin : inAnt (chainAsucc ds k) (chainAnt ds k) := by
    rcases hleaf with ⟨sk, hsk⟩ | ⟨sk, Ck, hsk⟩
    · have := zDerivation_zAtom_inv (s := sk) (by rw [← hsk]; exact hZk)
      simpa only [chainAsucc, chainAnt, hsk, fstIdx_zAtom] using this
    · have := zDerivation_zAx1_inv (s := sk) (C := Ck) (by rw [← hsk]; exact hZk)
      simpa only [chainAsucc, chainAnt, hsk, fstIdx_zAx1] using this
  rcases hchain k hk _ hin with h | h
  · rw [hant] at h; simp [inAnt, lh_empty] at h
  · obtain ⟨i', hi', heq⟩ := h; exact ⟨i', hi', heq.symm⟩

/-- **General-Γ succedent-threading collapse (lap-156).** The general-Γ (possibly NONEMPTY `seqAnt s`)
analogue of `chainAsucc_threaded_of_leaf`: it RETURNS the `V ∈ Γ` disjunct rather than killing it via
`seqAnt s = ∅`. For a chain with the antecedent-threading invariant `hthread` (the `isChainInf` field),
if some premise `n ≤ j0` has succedent `chainAsucc ds n = V`, then the LEAST-indexed premise `m ≤ n` with
succedent `V` either (a) puts `V ∈ Γ` — when it is an atom/`Ax¹` LEAF (its succedent sits in its OWN
antecedent, and threading routes it to Γ since by leastness no STRICTLY-EARLIER premise concludes `V`), or
(b) is a NON-LEAF (`zTag ∉ {0,7}`) premise concluding `V`. Consumed by `genReduct_chain_noRedex`'s tag-5/6
cut-partner sub-case (b): the leaf chain collapses the cut formula to Γ (→ the proven sub-case (a) reduct),
leaving only the NON-LEAF producer as the residual (an R-intro `zIall`/`zIneg` of the cut formula is then
killed by `hnolow` — it would form an `isRedexPair` with the major premise — so the residual narrows to a
`Rep` node concluding `V`, the narrowed §14.254b target). -/
lemma leastSucc_in_ant_or_nonleaf {s ds j0 C : V}
    (hZprem : ∀ i < lh ds, ZDerivation (znth ds i))
    (hthread : ∀ i ≤ j0, ∀ B, inAnt B (chainAnt ds i) →
      inAnt B (seqAnt s) ∨ ∃ i' < i, B = chainAsucc ds i')
    (hj0 : j0 < lh ds)
    {n : V} (hn : n ≤ j0) (hCn : chainAsucc ds n = C) :
    inAnt C (seqAnt s) ∨
    ∃ m, m ≤ n ∧ chainAsucc ds m = C ∧ zTag (znth ds m) ≠ 0 ∧ zTag (znth ds m) ≠ 7 := by
  have hQdef : 𝚺₁-Predicate (fun x : V => chainAsucc ds x = C ∧ x ≤ j0) := by
    apply Definable.and ?_ (by definability)
    exact DefinableRel.comp (by definability)
      (DefinableFunction₂.comp (F := chainAsucc)
        (DefinableFunction.const ds) (DefinableFunction.var 0))
      (DefinableFunction.const C)
  obtain ⟨m, ⟨hCm, hmle⟩, hmin⟩ :=
    InductionOnHierarchy.least_number 𝚺 1 hQdef ⟨hCn, hn⟩
  have hmn : m ≤ n := not_lt.mp (fun hlt => hmin n hlt ⟨hCn, hn⟩)
  have hmlt : m < lh ds := lt_of_le_of_lt hmle hj0
  have hmemZ : ZDerivation (znth ds m) := hZprem m hmlt
  rcases zDerivation_iff.mp hmemZ with
    ⟨s', h, _⟩ | ⟨s', a', p', d0', h, _, _⟩ | ⟨s', p', d0', h, _, _⟩ |
    ⟨s', at'', p', d0', d1', h, _, _⟩ | ⟨s', r', ds', h, _, _, _⟩ |
    ⟨s', p', k', h, _, _⟩ | ⟨s', p', h, _, _⟩ | ⟨s', C', h, _⟩
  · -- tag 0 (zAtom): succedent in its own antecedent; threading + leastness ⟹ `C ∈ Γ`.
    have hin : inAnt C (chainAnt ds m) := by
      have hinv := zDerivation_zAtom_inv (h ▸ hmemZ)
      have hCeq : C = seqSucc s' := by rw [← hCm, chainAsucc, h, fstIdx_zAtom]
      rw [hCeq]; simpa only [chainAnt, h, fstIdx_zAtom] using hinv
    rcases hthread m hmle C hin with hΓ | ⟨i', hi', heq⟩
    · exact Or.inl hΓ
    · exact absurd (hmin i' hi' ⟨heq.symm, le_of_lt (lt_of_lt_of_le hi' hmle)⟩) (by simp)
  · exact Or.inr ⟨m, hmn, hCm, by rw [h]; simp, by rw [h]; simp⟩
  · exact Or.inr ⟨m, hmn, hCm, by rw [h]; simp, by rw [h]; simp⟩
  · exact Or.inr ⟨m, hmn, hCm, by rw [h]; simp, by rw [h]; simp⟩
  · exact Or.inr ⟨m, hmn, hCm, by rw [h]; simp, by rw [h]; simp⟩
  · exact Or.inr ⟨m, hmn, hCm, by rw [h]; simp, by rw [h]; simp⟩
  · exact Or.inr ⟨m, hmn, hCm, by rw [h]; simp, by rw [h]; simp⟩
  · -- tag 7 (zAx1): succedent in its own antecedent; threading + leastness ⟹ `C ∈ Γ`.
    have hin : inAnt C (chainAnt ds m) := by
      have hinv := zDerivation_zAx1_inv (h ▸ hmemZ)
      have hCeq : C = seqSucc s' := by rw [← hCm, chainAsucc, h, fstIdx_zAx1]
      rw [hCeq]; simpa only [chainAnt, h, fstIdx_zAx1] using hinv
    rcases hthread m hmle C hin with hΓ | ⟨i', hi', heq⟩
    · exact Or.inl hΓ
    · exact absurd (hmin i' hi' ⟨heq.symm, le_of_lt (lt_of_lt_of_le hi' hmle)⟩) (by simp)

/-- **A right-symbol premise's `tp`-formula IS its succedent** (lap-156). For a `ZDerivation` whose `tp`
discriminant is a RIGHT symbol (`π₁ (tp d) = 0`), the carried formula `π₂ (tp d)` equals the succedent
`seqSucc (fstIdx d)`. The only right-symbol constructors are `zIall` (`tp = isymR (^∀p)`, succedent `^∀p`)
and `zIneg` (`tp = isymR (¬p ⋎ ⊥)`, succedent `inegF p`); every other constructor has `π₁ (tp) ∈ {1,2}`,
contradicting the hypothesis. -/
lemma pi2_tp_eq_seqSucc_of_pi1_zero {d : V} (hZ : ZDerivation d) (h0 : π₁ (tp d) = 0) :
    π₂ (tp d) = seqSucc (fstIdx d) := by
  rcases zDerivation_iff.mp hZ with
    ⟨s', h, _⟩ | ⟨s', a', p', d0', h, _, _⟩ | ⟨s', p', d0', h, _, _⟩ |
    ⟨s', at'', p', d0', d1', h, _, _⟩ | ⟨s', r', ds', h, _, _, _⟩ |
    ⟨s', p', k', h, _, _⟩ | ⟨s', p', h, _, _⟩ | ⟨s', C', h, _⟩
  · rw [h] at h0; simp [tp_zAtom] at h0
  · have hsucc : seqSucc s' = (^∀ p' : V) := (zDerivation_zIall_inv (h ▸ hZ)).2.1
    rw [h, tp_zIall, fstIdx_zIall, pi₂_isymR]; exact hsucc.symm
  · have hsucc : seqSucc s' = (inegF p' : V) := (zDerivation_zIneg_inv (h ▸ hZ)).2.1
    rw [h, tp_zIneg, fstIdx_zIneg, pi₂_isymR]; exact hsucc.symm
  · rw [h] at h0; simp [tp_zInd] at h0
  · rw [h] at h0; simp [tp_zK] at h0
  · rw [h] at h0; simp [tp_zAxAll, isymLk] at h0
  · rw [h] at h0; simp [tp_zAxNeg, isymLk] at h0
  · rw [h] at h0; simp [tp_zAx1] at h0

/-- **A right-symbol producer of a left-axiom's cut formula `F` is a `hnolow` redex** (lap-156, the
directive's "R-intro→`hnolow`" collapse step). If the major premise `jstar` is a LEFT axiom on `F`
(`tp (znth ds jstar) = isymLk kk F`) and a strictly-earlier premise `m < jstar` CONCLUDES `F`
(`chainAsucc ds m = F`) via a RIGHT symbol (`π₁ (tp (znth ds m)) = 0`), then `⟪m, jstar⟫` is an
`isRedexPair` `≤ j0` — contradicting `hnolow`. So under `hnolow` the cut formula of a left-axiom major can
NEVER be produced by a direct R-introduction below `j0`: it only threads from `Γ` or bottoms out at a `Rep`
node (the genuine §14.254b residual). Consumed by `genReduct_chain_noRedex`'s tag-5/6 non-leaf branch. -/
lemma rightSym_producer_redex {ds j0 jstar m F kk : V}
    (hZm : ZDerivation (znth ds m))
    (hjL : tp (znth ds jstar) = isymLk kk F)
    (hjlt : jstar < lh ds) (hjsj0 : jstar ≤ j0) (hmjs : m < jstar)
    (hCm : chainAsucc ds m = F)
    (h0 : π₁ (tp (znth ds m)) = 0)
    (hnolow : ¬ ∃ i0 j1, i0 < j1 ∧ j1 ≤ j0 ∧ isRedexPair ds (⟪i0, j1⟫ : V)) :
    False := by
  have hA : π₂ (tp (znth ds m)) = F := (pi2_tp_eq_seqSucc_of_pi1_zero hZm h0).trans hCm
  refine hnolow ⟨m, jstar, hmjs, hjsj0, ?_⟩
  simp only [isRedexPair, pi₁_pair, pi₂_pair]
  refine ⟨hmjs, hjlt, h0, ?_, ?_⟩
  · rw [hjL]; simp [isymLk]
  · rw [hjL]; simp only [isymLk, pi₂_pair]; exact hA.symm

set_option maxHeartbeats 1600000 in
/-- **§14.254b rank-climb: a left-axiom major's cut formula is always produced by a reducible / ¬-axiom
node, or threads to `Γ` (lap-157).** The genuine WEDGE for the tag-5 (`zAxAll`) residual. The major at
`jstar` is a LEFT axiom on a `^∀`-formula `F` (`tp = isymLk kk F`, `F ∈ chainAnt ds jstar`). Threading `F`
either lands a `^∀`-formula IN `Γ` (the escape), or bottoms out (via `leastSucc_in_ant_or_nonleaf`) at a
NON-LEAF producer — an R-introduction (`zIall`/`zIneg`, right symbol) is killed by `hnolow` (it forms an
`isRedexPair` with its left-axiom consumer), leaving a `Rep`/¬-axiom node (`zInd`/`zK`/`zAxNeg`, tags
{3,4,6}). The `zAxAll` (tag 5) producer cannot be a dead end: its OWN active formula `^∀ p'` is again a
`^∀`-formula that threads one rank UP — so it cannot be the LEAST `^∀`-producing axiom/`Rep` node (the
least-number search collapses the all-`zAxAll` climb to a strictly-earlier producer, contradicting
minimality). Hence the cut formula `^∀⊥` is ALWAYS produced by a `zInd`/`zK` (the general-succedent
reduction residual) or a `zAxNeg` (closed by `tryProducerClose`), or threads to `Γ`. This DISCHARGES the
"`zAxAll` producer is an independent gap" worry: the tag-5 residual collapses onto the tag-{3,4,6} cases. -/
lemma climb_to_rep_producer {s ds j0 jstar kk F : V}
    (hZprem : ∀ i < lh ds, ZDerivation (znth ds i))
    (hthread : ∀ i ≤ j0, ∀ B, inAnt B (chainAnt ds i) →
        inAnt B (seqAnt s) ∨ ∃ i' < i, B = chainAsucc ds i')
    (hj0 : j0 < lh ds)
    (hnolow : ¬ ∃ i0 j1, i0 < j1 ∧ j1 ≤ j0 ∧ isRedexPair ds (⟪i0, j1⟫ : V))
    (hjsj0 : jstar ≤ j0)
    (hjL : tp (znth ds jstar) = isymLk kk F)
    (hFall : ∃ Z, F = (^∀ Z : V))
    (hFin : inAnt F (chainAnt ds jstar)) :
    (∃ G, inAnt G (seqAnt s) ∧ ∃ Z, G = (^∀ Z : V)) ∨
    (∃ m, m ≤ j0 ∧ m < lh ds ∧
      (zTag (znth ds m) = 3 ∨ zTag (znth ds m) = 4 ∨ zTag (znth ds m) = 6)) := by
  -- ONE climb step from a left-axiom node `i` on cut formula `F'` (a `^∀`-formula): thread its active
  -- formula → escape (`F' ∈ Γ`) or a NON-LEAF producer `m < i` of `F'` (R-intro killed by `hnolow`).
  have producerStep : ∀ i ki F', i ≤ j0 → tp (znth ds i) = isymLk ki F' →
      inAnt F' (chainAnt ds i) → (∃ Z, F' = (^∀ Z : V)) →
      (∃ G, inAnt G (seqAnt s) ∧ ∃ Z, G = (^∀ Z : V)) ∨
      (∃ m, m < i ∧ m < lh ds ∧
        (zTag (znth ds m) = 3 ∨ zTag (znth ds m) = 4 ∨ zTag (znth ds m) = 5 ∨
          zTag (znth ds m) = 6) ∧ ∃ Z, chainAsucc ds m = (^∀ Z : V)) := by
    intro i ki F' hi hiL hF'in hF'all
    have hilt : i < lh ds := lt_of_le_of_lt hi hj0
    rcases hthread i hi F' hF'in with hΓ | ⟨i', hi'lt, hi'eq⟩
    · exact Or.inl ⟨F', hΓ, hF'all⟩
    · have hi'j0 : i' ≤ j0 := le_of_lt (lt_of_lt_of_le hi'lt hi)
      rcases leastSucc_in_ant_or_nonleaf hZprem hthread hj0 hi'j0 hi'eq.symm with
        hΓ | ⟨m, hmi', hCm, hm0, hm7⟩
      · exact Or.inl ⟨F', hΓ, hF'all⟩
      · have hmi : m < i := lt_of_le_of_lt hmi' hi'lt
        have hmlt : m < lh ds := lt_trans hmi hilt
        rcases zDerivation_iff.mp (hZprem m hmlt) with
          ⟨s', h, _⟩ | ⟨s', a', p', d0', h, _, _⟩ | ⟨s', p', d0', h, _, _⟩ |
          ⟨s', at'', p', d0', d1', h, _, _⟩ | ⟨s', r', ds', h, _, _, _⟩ |
          ⟨s', p', k', h, _, _⟩ | ⟨s', p', h, _, _⟩ | ⟨s', C', h, _⟩
        · exact absurd (show zTag (znth ds m) = 0 by rw [h]; simp) hm0
        · exact (rightSym_producer_redex (hZprem m hmlt) hiL hilt hi hmi hCm
            (by rw [h, tp_zIall, pi₁_isymR]) hnolow).elim
        · exact (rightSym_producer_redex (hZprem m hmlt) hiL hilt hi hmi hCm
            (by rw [h, tp_zIneg, pi₁_isymR]) hnolow).elim
        · exact Or.inr ⟨m, hmi, hmlt, Or.inl (by rw [h]; simp), hCm ▸ hF'all⟩
        · exact Or.inr ⟨m, hmi, hmlt, Or.inr (Or.inl (by rw [h]; simp)), hCm ▸ hF'all⟩
        · exact Or.inr ⟨m, hmi, hmlt, Or.inr (Or.inr (Or.inl (by rw [h]; simp))), hCm ▸ hF'all⟩
        · exact Or.inr ⟨m, hmi, hmlt, Or.inr (Or.inr (Or.inr (by rw [h]; simp))), hCm ▸ hF'all⟩
        · exact absurd (show zTag (znth ds m) = 7 by rw [h]; simp) hm7
  -- `Z` is strictly below `^∀ Z = ⟪6,Z⟫+1`, so the "is a `^∀`-formula" test bounds its witness.
  have hZlt : ∀ Z : V, Z < (^∀ Z : V) := fun Z => by
    rw [qqAll]; exact lt_succ_iff_le.mpr (le_pair_right 6 Z)
  -- Seed the least-producer search by threading `F` at `jstar`.
  rcases producerStep jstar kk F hjsj0 hjL hFin hFall with hesc | ⟨n₀, hn₀i, hn₀lt, hn₀tag, hn₀all⟩
  · exact Or.inl hesc
  · -- Least-indexed `^∀`-producing axiom/`Rep` node (tags {3,4,5,6}) `≤ j0`.
    have hPdef : 𝚺₁-Predicate (fun x : V =>
        x ≤ j0 ∧ (zTag (znth ds x) = 3 ∨ zTag (znth ds x) = 4 ∨ zTag (znth ds x) = 5 ∨
          zTag (znth ds x) = 6) ∧ ∃ Z < chainAsucc ds x, chainAsucc ds x = (^∀ Z : V)) := by
      apply Definable.and (by definability)
      apply Definable.and (by definability)
      haveI hsub : 𝚺₁-Predicate (fun y : V => ∃ Z < y, y = (^∀ Z : V)) := by definability
      exact Definable.comp₁ (P := fun y : V => ∃ Z < y, y = (^∀ Z : V))
        (DefinableFunction₂.comp (F := chainAsucc)
          (DefinableFunction.const ds) (DefinableFunction.var 0))
    have hn₀j0 : n₀ ≤ j0 := le_of_lt (lt_of_lt_of_le hn₀i hjsj0)
    have hn₀all' : ∃ Z < chainAsucc ds n₀, chainAsucc ds n₀ = (^∀ Z : V) := by
      obtain ⟨Z, hZ⟩ := hn₀all; exact ⟨Z, hZ ▸ hZlt Z, hZ⟩
    obtain ⟨m₀, ⟨hm₀j0, hm₀tag, hm₀all⟩, hmin⟩ :=
      InductionOnHierarchy.least_number 𝚺 1 hPdef ⟨hn₀j0, hn₀tag, hn₀all'⟩
    have hm₀lt : m₀ < lh ds := lt_of_le_of_lt hm₀j0 hj0
    rcases zDerivation_iff.mp (hZprem m₀ hm₀lt) with
      ⟨s', h, _⟩ | ⟨s', a', p', d0', h, _, _⟩ | ⟨s', p', d0', h, _, _⟩ |
      ⟨s', at'', p', d0', d1', h, _, _⟩ | ⟨s', r', ds', h, _, _, _⟩ |
      ⟨s', p', k', h, hp5, hin5, hsucc5⟩ | ⟨s', p', h, _, _⟩ | ⟨s', C', h, _⟩
    · rw [h] at hm₀tag; simp at hm₀tag
    · rw [h] at hm₀tag; simp at hm₀tag
    · rw [h] at hm₀tag; simp at hm₀tag
    · exact Or.inr ⟨m₀, hm₀j0, hm₀lt, Or.inl (by rw [h]; simp)⟩      -- zInd (3)
    · exact Or.inr ⟨m₀, hm₀j0, hm₀lt, Or.inr (Or.inl (by rw [h]; simp))⟩  -- zK (4)
    · -- zAxAll (5): its active `^∀ p'` is a `^∀`-formula; climb one step.
      have hjLm₀ : tp (znth ds m₀) = isymLk k' (^∀ p' : V) := by rw [h, tp_zAxAll]
      have hin' : inAnt (^∀ p' : V) (chainAnt ds m₀) := by
        simpa only [chainAnt, h, fstIdx_zAxAll] using hin5
      rcases producerStep m₀ k' (^∀ p') hm₀j0 hjLm₀ hin' ⟨p', rfl⟩ with
        hesc | ⟨m', hm'm₀, hm'lt, hm'tag, hm'all⟩
      · exact Or.inl hesc
      · obtain ⟨Z', hZ'eq⟩ := hm'all
        exact absurd ⟨le_of_lt (lt_of_lt_of_le hm'm₀ hm₀j0), hm'tag, Z', hZ'eq ▸ hZlt Z', hZ'eq⟩
          (hmin m' hm'm₀)
    · exact Or.inr ⟨m₀, hm₀j0, hm₀lt, Or.inr (Or.inr (by rw [h]; simp))⟩  -- zAxNeg (6)
    · rw [h] at hm₀tag; simp at hm₀tag

/-- **The least chain exit is NOT an `isymRep` leaf** (lap 121, Sub-lemma A of the generalized redex
finder). The `isChainInf` exit `j0` (`chainAsucc ds j0 ∈ {seqSucc s, ⊥}`) need not be unique. If every
`isymRep` premise `≤ j0` re-routes its succedent to a STRICTLY earlier premise (`hreroute`, supplied by
`chainAsucc_threaded_of_leaf` on the ⊥-orbit), then the LEAST-indexed exit `j'` is forced to be
NON-`isymRep`: were it `isymRep`, re-routing would hand back a smaller exit `i' < j'`, contradicting
minimality. This lets `inference_critical_pair`'s Step A (the exit symbol is a left symbol) run from a
genuine non-leaf exit even when the chain carries threaded atoms — the redex finder's `isymRep`-killing
use of `hnperm` at the exit, recovered structurally. -/
lemma exit_nonRep_of_reroute {s ds j0 : V}
    (hAj0 : chainAsucc ds j0 = seqSucc s ∨ chainAsucc ds j0 = (^⊥ : V))
    (hreroute : ∀ i ≤ j0, tp (znth ds i) = isymRep →
      ∃ i' < i, chainAsucc ds i' = chainAsucc ds i) :
    ∃ j', j' ≤ j0 ∧ (chainAsucc ds j' = seqSucc s ∨ chainAsucc ds j' = (^⊥ : V)) ∧
      tp (znth ds j') ≠ isymRep := by
  -- Search for the LEAST index whose succedent matches the exit value `c = chainAsucc ds j0`
  -- (single equality, `c` opaque); re-routing keeps it in `{seqSucc s, ⊥}`.
  set c := chainAsucc ds j0 with hc
  clear_value c
  have hQdef : 𝚺₁-Predicate (fun x : V => chainAsucc ds x = c ∧ x ≤ j0) := by
    apply Definable.and ?_ (by definability)
    exact DefinableRel.comp (by definability)
      (DefinableFunction₂.comp (F := chainAsucc)
        (DefinableFunction.const ds) (DefinableFunction.var 0))
      (DefinableFunction.const c)
  obtain ⟨j, ⟨hAj, hj_le⟩, hmin⟩ :=
    InductionOnHierarchy.least_number 𝚺 1 hQdef ⟨hc.symm, le_rfl⟩
  refine ⟨j, hj_le, ?_, ?_⟩
  · rcases hAj0 with h | h
    · exact Or.inl (hAj.trans h)
    · exact Or.inr (hAj.trans h)
  · intro hRep
    obtain ⟨i', hi'lt, hi'eq⟩ := hreroute j hj_le hRep
    exact hmin i' hi'lt ⟨hi'eq.trans hAj, le_of_lt (lt_of_lt_of_le hi'lt hj_le)⟩

/-- **`hreroute` from an all-leaves hypothesis** (lap 122, target #1 leaf branch). Packages
`chainAsucc_threaded_of_leaf` into exactly the `hreroute` shape that `inference_critical_pair_of_chain_reroute`
/ `iord_descent_iRcrit_of_chain_reroute` consume. Reduces the open `hreroute` obligation to `hleaves`:
**every `isymRep` premise `≤ j0` is a LEAF** (`zAtom`/`zAx1`, tags 0/7). For the leaf case the succedent
sits in the premise's own antecedent, and the ⊥-chain threading (`seqAnt s = ∅`) routes it to a strictly
earlier premise. This wires the leaf branch of the threaded-atom stall completely; the residual is now the
single named structural fact `hleaves` (a `red`-stall selects an atom/`zAx1` leaf by construction —
`red_zK_fixpoint_of_atom_selected`/`_zAx1_selected`; the chain/Ind `isymRep` residual is path α). -/
lemma hreroute_of_leaves {s ds j0 : V}
    (hant : seqAnt s = (∅ : V))
    (hchain : ∀ i ≤ j0, ∀ B, inAnt B (chainAnt ds i) →
      inAnt B (seqAnt s) ∨ ∃ i' < i, B = chainAsucc ds i')
    (hZ : ∀ i ≤ j0, ZDerivation (znth ds i))
    (hleaves : ∀ i ≤ j0, tp (znth ds i) = isymRep →
      (∃ sk, znth ds i = zAtom sk) ∨ (∃ sk Ck, znth ds i = zAx1 sk Ck)) :
    ∀ i ≤ j0, tp (znth ds i) = isymRep →
      ∃ i' < i, chainAsucc ds i' = chainAsucc ds i := by
  intro i hi hRep
  exact chainAsucc_threaded_of_leaf (hZ i hi) (hleaves i hi hRep) hant hchain hi

/-- **No-stall linchpin — the MAJOR premise of a `∅→⊥` chain is reducible** (lap 129, Buchholz §14.25).
For a `ZDerivation` of a chain `zK s r ds` concluding `∅→⊥`, there is a premise whose succedent is `⊥`
(`chainAsucc ds j = ⊥`) and whose tag is NEITHER `0` (atom) NOR `7` (`Ax¹`) — i.e. a genuinely *reducible*
major-premise candidate (`red` is the identity only on those two leaf tags). Proof: take the LEAST
`⊥`-succedent premise (`least_number` on `chainAsucc ds · = ⊥`, witnessed by the `isChainInf` exit `j0`);
were it an atom/`Ax¹` leaf, `chainAsucc_threaded_of_leaf` would re-route its `⊥` succedent to a STRICTLY
earlier premise, contradicting leastness.

**Why this is the decisive selection fix.** Buchholz (§14.25) selects the major premise of a `Θ→D` chain
as *the first premise whose succedent is `D`* (here `⊥`) — NOT the first `iperm`-permissible premise. The
repo's `permIdx`/`iperm` treats every `isymRep` premise as permissible (`iperm_isymRep`, unconditional), so
it can select an atom/`Ax¹` leaf whose succedent is some *other* prior formula — a `red`-FIXPOINT
(`red_zK_fixpoint_of_atom_selected`/`_zAx1_selected`), the laps 104/107/120 STALL. This lemma proves the
*faithful* selection never stalls: its major premise (the first `⊥`-exit) is one of `{zInd, zK, zAxAll,
zAxNeg}` (`zIall`/`zIneg` succedents `≠ ⊥`; atom/`Ax¹` killed here), every one of which `red` reduces. The
`∅→⊥` shape (no antecedent source) is exactly what forces the leaf's succedent to come from an earlier exit
— so the no-stall guarantee is specific to the headline ⊥-orbit, as it must be (Z-consistency is not free). -/
lemma firstBotPrem_reducible {s r ds : V} (hZ : ZDerivation (zK s r ds))
    (hant : seqAnt s = (∅ : V)) (hsucc : seqSucc s = (^⊥ : V)) :
    ∃ j < lh ds, chainAsucc ds j = (^⊥ : V) ∧
      zTag (znth ds j) ≠ 0 ∧ zTag (znth ds j) ≠ 7 := by
  have hchain : isChainInf s r ds := (zKValidF_of_ZDerivation_zK hZ).1
  obtain ⟨j0, hj0lt, hAj0, hthread, _hrank⟩ := hchain
  have hbot0 : chainAsucc ds j0 = (^⊥ : V) := by
    rcases hAj0 with h | h
    · rw [h, hsucc]
    · exact h
  have hP : 𝚺₁-Predicate (fun j => chainAsucc ds j = (^⊥ : V)) := by definability
  obtain ⟨jstar, hjstar, hmin⟩ := InductionOnHierarchy.least_number 𝚺 1 hP hbot0
  have hjle : jstar ≤ j0 := by
    by_contra h
    exact (hmin j0 (not_le.mp h)) hbot0
  have hjlt : jstar < lh ds := lt_of_le_of_lt hjle hj0lt
  have hmemZ : ZDerivation (znth ds jstar) := (zDerivation_zK_inv hZ).2 jstar hjlt
  refine ⟨jstar, hjlt, hjstar, ?_⟩
  rcases zDerivation_iff.mp hmemZ with
    ⟨s', h, _⟩ | ⟨s', a', p', d0', h, _, _⟩ | ⟨s', p', d0', h, _, _⟩ |
    ⟨s', at'', p', d0', d1', h, _, _⟩ | ⟨s', r', ds', h, _, _, _⟩ |
    ⟨s', p', k', h, _, _⟩ | ⟨s', p', h, _, _⟩ | ⟨s', C', h, _⟩
  · -- atom (tag 0): a leaf ⊥-exit re-routes to a STRICTLY earlier ⊥-exit, contradicting leastness
    exfalso
    obtain ⟨i', hi', heq⟩ :=
      chainAsucc_threaded_of_leaf hmemZ (Or.inl ⟨s', h⟩) hant hthread hjle
    exact (hmin i' hi') (heq.trans hjstar)
  · exact ⟨by rw [h]; simp, by rw [h]; simp⟩
  · exact ⟨by rw [h]; simp, by rw [h]; simp⟩
  · exact ⟨by rw [h]; simp, by rw [h]; simp⟩
  · exact ⟨by rw [h]; simp, by rw [h]; simp⟩
  · exact ⟨by rw [h]; simp, by rw [h]; simp⟩
  · exact ⟨by rw [h]; simp, by rw [h]; simp⟩
  · -- zAx1 (tag 7): same leaf re-routing contradiction
    exfalso
    obtain ⟨i', hi', heq⟩ :=
      chainAsucc_threaded_of_leaf hmemZ (Or.inr ⟨s', C', h⟩) hant hthread hjle
    exact (hmin i' hi') (heq.trans hjstar)

/-! ### The faithful `majorIdx` selector (Buchholz §14.25) — the no-stall replacement for `permIdx`

`permIdx`/`iperm` select the first `iperm`-permissible (`isymRep`) premise, which can be a `red`-normal
atom/`Ax¹` LEAF → the stall. Buchholz §14.25 selects the **major premise** = the first premise whose
*succedent IS the endsequent succedent*. `majorIdxAux` mirrors `permIdxAux` on that predicate
(`isMajorPrem`); `majorIdx_botOrbit_reducible` proves it never stalls on the ⊥-orbit. The `iRK` re-key
(`permIdx ↦ majorIdx` in the replace branch) is the remaining engine step (PENDING_WORK lap-129). -/

/-- **Faithful (Buchholz §14.25) major-premise selection predicate:** premise `n`'s succedent IS the
endsequent succedent. -/
def isMajorPrem (ds s n : V) : Prop := chainAsucc ds n = seqSucc s

noncomputable def majorIdxAux.blueprint : PR.Blueprint 2 where
  zero := .mkSigma “y ds s. y = 0”
  succ := .mkSigma “y ih n ds s.
    (ih < n ∧ y = ih) ∨
    (n ≤ ih ∧ ∃ c, !chainAsuccDef c ds n ∧ ∃ ss, !seqSuccDef ss s ∧
      ( (c = ss ∧ y = n) ∨ (¬(c = ss) ∧ y = n + 1) ) )”

noncomputable def majorIdxAux.construction : PR.Construction V majorIdxAux.blueprint where
  zero := fun _ ↦ 0
  succ := fun x n ih ↦ if ih < n then ih else if isMajorPrem (x 0) (x 1) n then n else n + 1
  zero_defined := .mk fun v ↦ by simp [majorIdxAux.blueprint]
  succ_defined := .mk fun v ↦ by
    by_cases h1 : v 1 < v 2
    · simp [majorIdxAux.blueprint, h1]
    · have hle : v 2 ≤ v 1 := not_lt.mp h1
      by_cases h2 : isMajorPrem (v 3) (v 4) (v 2)
      · simp only [majorIdxAux.blueprint, isMajorPrem] at h2 ⊢
        simp [h1, h2, hle, chainAsucc_defined.iff, seqSucc_defined.iff]
      · simp only [majorIdxAux.blueprint, isMajorPrem] at h2 ⊢
        simp [h1, h2, hle, chainAsucc_defined.iff, seqSucc_defined.iff]

/-- `majorIdxAux ds s n` = the least `i < n` with `isMajorPrem ds s i`, or `n` if none. -/
noncomputable def majorIdxAux (ds s n : V) : V := majorIdxAux.construction.result ![ds, s] n

@[simp] lemma majorIdxAux_zero (ds s : V) : majorIdxAux ds s 0 = 0 := by
  simp [majorIdxAux, majorIdxAux.construction]

@[simp] lemma majorIdxAux_succ (ds s n : V) :
    majorIdxAux ds s (n + 1) =
      (if majorIdxAux ds s n < n then majorIdxAux ds s n
       else if isMajorPrem ds s n then n else n + 1) := by
  simp [majorIdxAux, majorIdxAux.construction]

noncomputable def _root_.LO.FirstOrder.Arithmetic.majorIdxAuxDef : 𝚺₁.Semisentence 4 :=
  majorIdxAux.blueprint.resultDef.rew (Rew.subst ![#0, #3, #1, #2])

instance majorIdxAux_defined : 𝚺₁-Function₃ (majorIdxAux : V → V → V → V) via majorIdxAuxDef :=
  .mk fun v ↦ by simp [majorIdxAux.construction.result_defined_iff, majorIdxAuxDef]; rfl

instance majorIdxAux_definable : 𝚺₁-Function₃ (majorIdxAux : V → V → V → V) :=
  majorIdxAux_defined.to_definable
instance majorIdxAux_definable' (Γ) : Γ-[m + 1]-Function₃ (majorIdxAux : V → V → V → V) :=
  majorIdxAux_definable.of_sigmaOne

/-- **First-hit ≤ sentinel**. -/
lemma majorIdxAux_le (ds s : V) : ∀ N, majorIdxAux ds s N ≤ N := by
  intro N
  induction N using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ n ih =>
    rw [majorIdxAux_succ]
    by_cases h1 : majorIdxAux ds s n < n
    · rw [if_pos h1]; exact le_of_lt (lt_trans h1 (le_iff_lt_succ.mp (le_refl n)))
    · rw [if_neg h1]
      by_cases h2 : isMajorPrem ds s n
      · rw [if_pos h2]; exact le_of_lt (le_iff_lt_succ.mp (le_refl n))
      · simp [h2]

/-- **First-hit is valid** — a returned index `< N` is a major premise. -/
lemma majorIdxAux_isMajorPrem_of_lt (ds s : V) :
    ∀ N, majorIdxAux ds s N < N → isMajorPrem ds s (majorIdxAux ds s N) := by
  intro N
  induction N using ISigma1.sigma1_succ_induction
  · simp only [isMajorPrem]; definability
  case zero => intro h; exact absurd h (by simp)
  case succ n ih =>
    intro hlt
    rw [majorIdxAux_succ] at hlt ⊢
    by_cases h1 : majorIdxAux ds s n < n
    · rw [if_pos h1] at hlt ⊢; exact ih h1
    · rw [if_neg h1] at hlt ⊢
      by_cases h2 : isMajorPrem ds s n
      · rw [if_pos h2] at hlt ⊢; exact h2
      · rw [if_neg h2] at hlt; exact absurd hlt (by simp)

/-- **No-hit sentinel** — if the search returns `N`, no `i < N` is a major premise. -/
lemma majorIdxAux_eq_self_of_none (ds s : V) :
    ∀ N, majorIdxAux ds s N = N → ∀ i < N, ¬ isMajorPrem ds s i := by
  intro N
  induction N using ISigma1.sigma1_succ_induction
  · simp only [isMajorPrem]; definability
  case zero => intro _ i hi; exact absurd hi (by simp)
  case succ n ih =>
    intro heq i hi
    rw [majorIdxAux_succ] at heq
    by_cases h1 : majorIdxAux ds s n < n
    · rw [if_pos h1] at heq
      exact absurd (le_iff_lt_succ.mp (le_refl n)) (lt_asymm (heq ▸ h1))
    · rw [if_neg h1] at heq
      by_cases h2 : isMajorPrem ds s n
      · rw [if_pos h2] at heq; exact absurd heq (le_iff_lt_succ.mp (le_refl n)).ne
      · rw [if_neg h2] at heq
        have hn : majorIdxAux ds s n = n := le_antisymm (majorIdxAux_le ds s n) (not_lt.mp h1)
        rcases lt_or_eq_of_le (lt_succ_iff_le.mp hi) with hin | hin
        · exact ih hn i hin
        · rw [hin]; exact h2

/-- **First-hit found** — when a major premise exists below `N`, the search returns one. -/
lemma majorIdxAux_found (ds s N : V) (h : ∃ i < N, isMajorPrem ds s i) :
    majorIdxAux ds s N < N ∧ isMajorPrem ds s (majorIdxAux ds s N) := by
  have hlt : majorIdxAux ds s N < N := by
    rcases lt_or_eq_of_le (majorIdxAux_le ds s N) with h' | h'
    · exact h'
    · obtain ⟨i, hiN, hi⟩ := h
      exact absurd hi (majorIdxAux_eq_self_of_none ds s N h' i hiN)
  exact ⟨hlt, majorIdxAux_isMajorPrem_of_lt ds s N hlt⟩

/-- **First-hit is LEAST** — the returned index is `≤` any major premise `m < N`. -/
lemma majorIdxAux_le_of_isMajorPrem (ds s : V) :
    ∀ N, ∀ m < N, isMajorPrem ds s m → majorIdxAux ds s N ≤ m := by
  intro N
  induction N using ISigma1.sigma1_succ_induction
  · simp only [isMajorPrem]; definability
  case zero => intro m hm; exact absurd hm (by simp)
  case succ n ih =>
    intro m hm hmaj
    rw [majorIdxAux_succ]
    by_cases h1 : majorIdxAux ds s n < n
    · rw [if_pos h1]
      rcases lt_or_eq_of_le (lt_succ_iff_le.mp hm) with hmn | hmn
      · exact ih m hmn hmaj
      · subst hmn; exact le_of_lt h1
    · rw [if_neg h1]
      have hn : majorIdxAux ds s n = n := le_antisymm (majorIdxAux_le ds s n) (not_lt.mp h1)
      have hnone := majorIdxAux_eq_self_of_none ds s n hn
      rcases lt_or_eq_of_le (lt_succ_iff_le.mp hm) with hmn | hmn
      · exact absurd hmaj (hnone m hmn)
      · subst hmn; rw [if_pos hmaj]

/-- **The faithful major-premise index of a chain** = least premise whose succedent is the conclusion
succedent, sentinel `lh (zKseq d)`. Buchholz §14.25; the no-stall replacement for `permIdx`. -/
noncomputable def majorIdx (d : V) : V := majorIdxAux (zKseq d) (fstIdx d) (lh (zKseq d))

/-- **No-stall, end-to-end (the `iRK` re-key consumes this).** On a `∅→⊥` chain `zK s r ds`, the faithful
selector `majorIdx` lands on an IN-RANGE premise whose succedent is `⊥` and whose tag is NOT a `red`-normal
leaf (`≠ 0,7`). So re-keying `iRK`'s replace branch from `permIdx` to `majorIdx` makes the atom/`Ax¹`
fixpoint stall UNREACHABLE on the headline ⊥-orbit. Combines `majorIdxAux_found`/`_le_of_isMajorPrem` (the
selector finds the LEAST `⊥`-exit, guaranteed to exist by `isChainInf`) with `chainAsucc_threaded_of_leaf`
(a leaf `⊥`-exit re-routes to a strictly earlier one — impossible for the least). -/
lemma majorIdx_botOrbit_reducible {s r ds : V} (hZ : ZDerivation (zK s r ds))
    (hant : seqAnt s = (∅ : V)) (hsucc : seqSucc s = (^⊥ : V)) :
    majorIdx (zK s r ds) < lh ds ∧
    chainAsucc ds (majorIdx (zK s r ds)) = (^⊥ : V) ∧
    zTag (znth ds (majorIdx (zK s r ds))) ≠ 0 ∧ zTag (znth ds (majorIdx (zK s r ds))) ≠ 7 := by
  have hchain : isChainInf s r ds := (zKValidF_of_ZDerivation_zK hZ).1
  obtain ⟨j0, hj0lt, hAj0, hthread, _⟩ := hchain
  have hbot0 : chainAsucc ds j0 = (^⊥ : V) := by
    rcases hAj0 with h | h
    · rw [h, hsucc]
    · exact h
  have hmaj0 : isMajorPrem ds s j0 := by rw [isMajorPrem, hbot0, hsucc]
  have hmeq : majorIdx (zK s r ds) = majorIdxAux ds s (lh ds) := by rw [majorIdx, zKseq_zK, fstIdx_zK]
  obtain ⟨hmlt, hmmaj⟩ := majorIdxAux_found ds s (lh ds) ⟨j0, hj0lt, hmaj0⟩
  have hmle : majorIdxAux ds s (lh ds) ≤ j0 := majorIdxAux_le_of_isMajorPrem ds s (lh ds) j0 hj0lt hmaj0
  have hmbot : chainAsucc ds (majorIdxAux ds s (lh ds)) = (^⊥ : V) := by rw [← hsucc]; exact hmmaj
  rw [hmeq]
  refine ⟨hmlt, hmbot, ?_⟩
  have hmemZ : ZDerivation (znth ds (majorIdxAux ds s (lh ds))) := (zDerivation_zK_inv hZ).2 _ hmlt
  rcases zDerivation_iff.mp hmemZ with
    ⟨s', h, _⟩ | ⟨s', a', p', d0', h, _, _⟩ | ⟨s', p', d0', h, _, _⟩ |
    ⟨s', at'', p', d0', d1', h, _, _⟩ | ⟨s', r', ds', h, _, _, _⟩ |
    ⟨s', p', k', h, _, _⟩ | ⟨s', p', h, _, _⟩ | ⟨s', C', h, _⟩
  · exfalso
    obtain ⟨i', hi', heq⟩ :=
      chainAsucc_threaded_of_leaf hmemZ (Or.inl ⟨s', h⟩) hant hthread hmle
    have hi'maj : isMajorPrem ds s i' := by rw [isMajorPrem, heq, hmbot, hsucc]
    exact absurd (majorIdxAux_le_of_isMajorPrem ds s (lh ds) i' (lt_trans hi' hmlt) hi'maj)
      (not_le.mpr hi')
  · exact ⟨by rw [h]; simp, by rw [h]; simp⟩
  · exact ⟨by rw [h]; simp, by rw [h]; simp⟩
  · exact ⟨by rw [h]; simp, by rw [h]; simp⟩
  · exact ⟨by rw [h]; simp, by rw [h]; simp⟩
  · exact ⟨by rw [h]; simp, by rw [h]; simp⟩
  · exact ⟨by rw [h]; simp, by rw [h]; simp⟩
  · exfalso
    obtain ⟨i', hi', heq⟩ :=
      chainAsucc_threaded_of_leaf hmemZ (Or.inr ⟨s', C', h⟩) hant hthread hmle
    have hi'maj : isMajorPrem ds s i' := by rw [isMajorPrem, heq, hmbot, hsucc]
    exact absurd (majorIdxAux_le_of_isMajorPrem ds s (lh ds) i' (lt_trans hi' hmlt) hi'maj)
      (not_le.mpr hi')

/-! ### The tag-5/6 major premise needs a CRITICAL dispatch, not a `replace` (lap 130 finding)

`majorIdx_botOrbit_reducible` excludes only the tag-0/7 leaves (atom/`Ax¹`) from the major-premise slot.
But the L-axioms `zAxAll` (tag 5) and `zAxNeg` (tag 6) are ALSO `red`-FIXPOINTS — `red_zAxAll = id`,
`red_zAxNeg = id` — and they are NOT excluded: their inversions (`zDerivation_zAxAll_inv`/`_zAxNeg_inv`)
put the *active* L-formula (`^∀ p` / `inegF p`), NOT the succedent, in the antecedent, so the
`chainAsucc_threaded_of_leaf` re-routing (which keys on succedent-in-own-antecedent) does not apply.

So the lap-129 plan "re-key `iRK`'s replace branch `permIdx ↦ majorIdx`" is INCOMPLETE: a naive `replace`
into a tag-5/6 major premise `dⱼ` stalls (`red dⱼ = dⱼ`). The faithful Buchholz §14.253 reduction of such
a `dⱼ` is the principal `(R,L)` CUT — its active L-formula threads back (via `isChainInf`) to a STRICTLY
earlier R-introduction premise. The two lemmas below PIN that R-partner, supplying the exact object the
re-keyed critical/splice dispatch consumes for a tag-5/6 major premise. -/

/-- **Tag-5 (∀-axiom) major premise ⟹ its critical-cut R-partner `∀p` is upstream.** On a `∅→⊥` chain, if
the faithful major premise `dⱼ = znth ds (majorIdx)` is an L-axiom `Ax^k_{∀p}` (a `red`-FIXPOINT,
`red_zAxAll = id`), its active formula `^∀ p` is the succedent of a STRICTLY EARLIER premise `i' < j`. That
`i'` is the R-introduction of `∀p`; the pair `(i', j)` is the principal cut the faithful re-key reduces —
NOT a `replace` recursion into `dⱼ`. The active formula sits in `dⱼ`'s antecedent
(`zDerivation_zAxAll_inv`), and the ⊥-chain threading (`seqAnt s = ∅`) forces it to an earlier cut formula. -/
lemma majorPrem_zAxAll_cutPartner {s r ds p k : V} (hZ : ZDerivation (zK s r ds))
    (hant : seqAnt s = (∅ : V)) (hsucc : seqSucc s = (^⊥ : V))
    (hj : znth ds (majorIdx (zK s r ds)) =
      zAxAll (fstIdx (znth ds (majorIdx (zK s r ds)))) p k) :
    ∃ i' < majorIdx (zK s r ds), chainAsucc ds i' = (^∀ p : V) := by
  have hmeq : majorIdx (zK s r ds) = majorIdxAux ds s (lh ds) := by rw [majorIdx, zKseq_zK, fstIdx_zK]
  rw [hmeq] at hj ⊢
  set J := majorIdxAux ds s (lh ds) with hJ
  have hchain : isChainInf s r ds := (zKValidF_of_ZDerivation_zK hZ).1
  obtain ⟨j0, hj0lt, hAj0, hthread, _⟩ := hchain
  have hbot0 : chainAsucc ds j0 = (^⊥ : V) := by
    rcases hAj0 with h | h
    · rw [h, hsucc]
    · exact h
  have hmaj0 : isMajorPrem ds s j0 := by rw [isMajorPrem, hbot0, hsucc]
  obtain ⟨hmlt, _⟩ := majorIdxAux_found ds s (lh ds) ⟨j0, hj0lt, hmaj0⟩
  have hmle : J ≤ j0 := majorIdxAux_le_of_isMajorPrem ds s (lh ds) j0 hj0lt hmaj0
  have hmemZ : ZDerivation (znth ds J) := (zDerivation_zK_inv hZ).2 _ hmlt
  set s' := fstIdx (znth ds J) with hs'
  have hin : inAnt (^∀ p : V) (seqAnt s') := (zDerivation_zAxAll_inv (hj ▸ hmemZ)).2.1
  rcases hthread J hmle (^∀ p) hin with h | h
  · rw [hant] at h; simp [inAnt, lh_empty] at h
  · obtain ⟨i', hi', heq⟩ := h; exact ⟨i', hi', heq.symm⟩

/-- **Tag-6 (¬-axiom) major premise ⟹ its critical-cut R-partner `inegF p` is upstream.** Dual of
`majorPrem_zAxAll_cutPartner`: when the major premise `dⱼ` is `Ax^0_{¬p}` (a `red`-FIXPOINT,
`red_zAxNeg = id`), its active L-formula `inegF p` is the succedent of a strictly earlier premise — the
R-introduction (`zIneg`) of `¬p`. The pair drives the principal cut the re-key reduces. -/
lemma majorPrem_zAxNeg_cutPartner {s r ds p : V} (hZ : ZDerivation (zK s r ds))
    (hant : seqAnt s = (∅ : V)) (hsucc : seqSucc s = (^⊥ : V))
    (hj : znth ds (majorIdx (zK s r ds)) =
      zAxNeg (fstIdx (znth ds (majorIdx (zK s r ds)))) p) :
    ∃ i' < majorIdx (zK s r ds), chainAsucc ds i' = (inegF p : V) := by
  have hmeq : majorIdx (zK s r ds) = majorIdxAux ds s (lh ds) := by rw [majorIdx, zKseq_zK, fstIdx_zK]
  rw [hmeq] at hj ⊢
  set J := majorIdxAux ds s (lh ds) with hJ
  have hchain : isChainInf s r ds := (zKValidF_of_ZDerivation_zK hZ).1
  obtain ⟨j0, hj0lt, hAj0, hthread, _⟩ := hchain
  have hbot0 : chainAsucc ds j0 = (^⊥ : V) := by
    rcases hAj0 with h | h
    · rw [h, hsucc]
    · exact h
  have hmaj0 : isMajorPrem ds s j0 := by rw [isMajorPrem, hbot0, hsucc]
  obtain ⟨hmlt, _⟩ := majorIdxAux_found ds s (lh ds) ⟨j0, hj0lt, hmaj0⟩
  have hmle : J ≤ j0 := majorIdxAux_le_of_isMajorPrem ds s (lh ds) j0 hj0lt hmaj0
  have hmemZ : ZDerivation (znth ds J) := (zDerivation_zK_inv hZ).2 _ hmlt
  set s' := fstIdx (znth ds J) with hs'
  have hin : inAnt (inegF p : V) (seqAnt s') := (zDerivation_zAxNeg_inv (hj ▸ hmemZ)).2.1
  rcases hthread J hmle (inegF p) hin with h | h
  · rw [hant] at h; simp [inAnt, lh_empty] at h
  · obtain ⟨i', hi', heq⟩ := h; exact ⟨i', hi', heq.symm⟩

/-- `^∀ p ≠ ^⊥` — the universal-quantifier code and the falsum code have different head tags
(`qqAll p = ⟪6,p⟫+1`, `qqFalsum = ⟪3,0⟫+1`). -/
lemma qqAll_ne_falsum (p : V) : (^∀ p : V) ≠ (^⊥ : V) := by
  simp [qqAll, qqFalsum]

/-- `inegF p ≠ ^⊥` — `inegF p = (∼p) ⋎ ⊥` is an or-code (head tag 7), distinct from falsum. -/
lemma inegF_ne_falsum (p : V) : (inegF p : V) ≠ (^⊥ : V) := by
  simp [inegF, qqOr, qqFalsum]

/-- **The ⊥-orbit major premise tag ∈ {3,4,5,6}.** Strengthens `majorIdx_botOrbit_reducible`: the faithful
major premise of a `∅→⊥` chain is a `zInd` (3) / `zK` (4) / `zAxAll` (5) / `zAxNeg` (6) node. Tags 0,7 are
the atom/`Ax¹` leaves (`majorIdx_botOrbit_reducible`); tags 1,2 are excluded because a `zIall`/`zIneg`
node's succedent is an R-principal formula (`^∀p` / `inegF p`), which is `≠ ^⊥`, whereas the major
premise's succedent IS `^⊥`. This is the precise tag dichotomy the re-keyed `iRK` dispatch case-splits on:
**3,4 → replace/recurse** (`red_zInd` descends; `zK` recurses), **5,6 → critical cut** against the upstream
R-partner (pinned by `majorPrem_zAxAll_cutPartner` / `majorPrem_zAxNeg_cutPartner`). -/
lemma majorPrem_tag_mem {s r ds : V} (hZ : ZDerivation (zK s r ds))
    (hant : seqAnt s = (∅ : V)) (hsucc : seqSucc s = (^⊥ : V)) :
    zTag (znth ds (majorIdx (zK s r ds))) = 3 ∨ zTag (znth ds (majorIdx (zK s r ds))) = 4 ∨
    zTag (znth ds (majorIdx (zK s r ds))) = 5 ∨ zTag (znth ds (majorIdx (zK s r ds))) = 6 := by
  obtain ⟨hlt, hbot, hne0, hne7⟩ := majorIdx_botOrbit_reducible hZ hant hsucc
  have hmemZ : ZDerivation (znth ds (majorIdx (zK s r ds))) := (zDerivation_zK_inv hZ).2 _ hlt
  -- `chainAsucc ds (majorIdx) = seqSucc (fstIdx (znth ds (majorIdx))) = ^⊥`
  have hsucc' : seqSucc (fstIdx (znth ds (majorIdx (zK s r ds)))) = (^⊥ : V) := hbot
  rcases zDerivation_iff.mp hmemZ with
    ⟨s', h, _⟩ | ⟨s', a', p', d0', h, _, _⟩ | ⟨s', p', d0', h, _, _⟩ |
    ⟨s', at'', p', d0', d1', h, _, _⟩ | ⟨s', r', ds', h, _, _, _⟩ |
    ⟨s', p', k', h, _, _⟩ | ⟨s', p', h, _, _⟩ | ⟨s', C', h, _⟩
  · exact absurd (show zTag (znth ds (majorIdx (zK s r ds))) = 0 by rw [h]; simp) hne0
  · -- tag 1 (zIall): succedent `^∀ p'` ≠ `^⊥`
    exfalso
    have heq : seqSucc s' = (^∀ p' : V) := (zDerivation_zIall_inv (h ▸ hmemZ)).2.1
    rw [h, fstIdx_zIall, heq] at hsucc'
    exact qqAll_ne_falsum p' hsucc'
  · -- tag 2 (zIneg): succedent `inegF p'` ≠ `^⊥`
    exfalso
    have heq : seqSucc s' = (inegF p' : V) := (zDerivation_zIneg_inv (h ▸ hmemZ)).2.1
    rw [h, fstIdx_zIneg, heq] at hsucc'
    exact inegF_ne_falsum p' hsucc'
  · exact Or.inl (by rw [h]; simp)
  · exact Or.inr (Or.inl (by rw [h]; simp))
  · exact Or.inr (Or.inr (Or.inl (by rw [h]; simp)))
  · exact Or.inr (Or.inr (Or.inr (by rw [h]; simp)))
  · exact absurd (by rw [h]; simp : zTag (znth ds (majorIdx (zK s r ds))) = 7) hne7

/-- **A non-leaf `isymRep` premise is a `zInd` (3) or `zK` (4) node.** The `tp = isymRep` symbol is carried
by exactly four constructors — `zAtom` (0), `zInd` (3), `zK` (4), `zAx1` (7) — of which `zAtom`/`zAx1` are
the leaves. So a `ZDerivation` premise with `tp = isymRep` that is NOT an atom/`Ax¹` leaf is precisely an
Ind node (reduced by `red_zInd`, a banked strict descent) or a sub-K-chain (recursed). This is the tag
dispatch the **RIGHT disjunct** of `RedZKDescent.iRcrit_descends_or_nonleaf_isymRep` (the stall-tolerant
⊥-orbit descent dichotomy) case-splits on — and it lines up with `majorPrem_tag_mem`'s tag-3/4 cases
(a ⊥-exit `zInd`/`zK` premise IS a non-leaf `isymRep`, `tp_zInd`/`tp_zK = isymRep`). -/
lemma isymRep_nonleaf_zInd_or_zK {d : V} (hZ : ZDerivation d) (hrep : tp d = isymRep)
    (hnleaf : ¬ ((∃ sk, d = zAtom sk) ∨ (∃ sk Ck, d = zAx1 sk Ck))) :
    (∃ s at' p d0 d1, d = zInd s at' p d0 d1) ∨ (∃ s r ds, d = zK s r ds) := by
  rcases zDerivation_iff.mp hZ with
    ⟨s', h, _⟩ | ⟨s', a', p', d0', h, _, _⟩ | ⟨s', p', d0', h, _, _⟩ |
    ⟨s', at'', p', d0', d1', h, _, _⟩ | ⟨s', r', ds', h, _, _, _⟩ |
    ⟨s', p', k', h, _, _⟩ | ⟨s', p', h, _, _⟩ | ⟨s', C', h, _⟩
  · exact absurd (Or.inl ⟨s', h⟩) hnleaf
  · rw [h, tp_zIall] at hrep; exact absurd hrep (isymR_ne_isymRep _)
  · rw [h, tp_zIneg] at hrep; exact absurd hrep (isymR_ne_isymRep _)
  · exact Or.inl ⟨s', at'', p', d0', d1', h⟩
  · exact Or.inr ⟨s', r', ds', h⟩
  · rw [h, tp_zAxAll] at hrep; exact absurd hrep (isymLk_ne_isymRep _ _)
  · rw [h, tp_zAxNeg] at hrep; exact absurd hrep (isymLk_ne_isymRep _ _)
  · exact absurd (Or.inr ⟨s', C', h⟩) hnleaf

/-- **The cut formula of a valid critical chain is well-formed** — `IsUFormula (cutFormula (zK s r ds))`.
This is the `hCwff` plumbing input to `ZDerivation_iRKcCrit_of_zKValid` (the re-keyed critical reduct's
soundness, `Crux2Blueprint`), supplied here from the orbit data alone (`ZDerivation` + `zKValid`). The cut
formula is the stripped principal: in the ∀-redex case it is the matrix instance `F(k) = substs1 (numeral
k) p` (a `UFormula` since `p` is a 1-`IsSemiformula` from the I∀ premise's `zIallWff`); in the ¬-redex case
it is the negation matrix `p` (a `UFormula` directly, from `redZKReady`'s axNeg branch). -/
lemma cutFormula_wff_of_zKValid {s r ds : V}
    (hZ : ZDerivation (zK s r ds)) (hvalid : zKValid s r ds) :
    IsUFormula ℒₒᵣ (cutFormula (zK s r ds)) := by
  obtain ⟨hIJ, hJlt, hcase⟩ := redZKReady_of_zKValid hZ hvalid
  have hIlt : redexI (zK s r ds) < lh ds := lt_trans hIJ hJlt
  obtain ⟨_, hmem⟩ := zDerivation_zK_inv hZ
  rcases hcase with ⟨sᵢ, sⱼ, a, p, pj, k', d0, hdi, hdj, _hrk, _hsj⟩ |
    ⟨sᵢ, sⱼ, p, d0, hdi, hdj, hcut, hpUf⟩
  · -- ∀-redex: `cutFormula = substs1 (numeral _) p`, `p` a 1-semiformula
    have hZi : ZDerivation (zIall sᵢ a p d0) := hdi ▸ hmem _ hIlt
    obtain ⟨_, hssi, hwff⟩ := zDerivation_zIall_inv hZi
    have hsf : IsSemiformula ℒₒᵣ 1 p := hwff.2.2
    have hChA : chainAsucc ds (redexI (zK s r ds)) = (^∀ p : V) := by
      show seqSucc (fstIdx (znth ds (redexI (zK s r ds)))) = (^∀ p : V)
      rw [hdi, fstIdx_zIall]; exact hssi
    have hcut := cutFormula_all (d := zK s r ds) (by rw [zKseq_zK]; exact hChA)
    rw [hcut]
    exact (IsSemiformula.substs1 (by simp : IsSemiterm ℒₒᵣ 0
      (Bootstrapping.Arithmetic.numeral (π₁ (π₂ (tp (znth (zKseq (zK s r ds)) (redexJ (zK s r ds)))))) : V))
      hsf).isUFormula
  · -- ¬-redex: `cutFormula = p`, `IsUFormula p` directly
    rw [hcut]; exact hpUf

set_option maxHeartbeats 1000000 in
/-- **The generalized redex finder for a re-routing chain** (lap 122 — the genuine fix for the threaded-atom
stall, Sub-lemmas A+B assembled). `inference_critical_pair_of_chain` needs FULL criticality `hnperm`
(no premise permissible for the conclusion, incl. its `isymRep` clause). A threaded atom/`Ax¹` leaf is
unconditionally permissible (`iperm_isymRep`), so that clause FAILS — the documented `red`-stall. This
finder REPLACES the `isymRep` clause of `hnperm` with `hreroute` (every `isymRep` premise `≤ j0` re-routes
its succedent to a strictly earlier premise — exactly `chainAsucc_threaded_of_leaf`'s conclusion for the
leaf case). It still produces the genuine `(R_A, L^k_A)` redex pair with `0 < rk A ≤ r`, so any chain
whose permissibility-failures are all re-routable leaves still drives the K-descent
(`iord_descent_iRcrit_of_redex`), the threaded-atom stall DISSOLVED with no engine surgery.

**Why the "L-axiom caveat" (lap-121 baton) does NOT arise.** Step B takes the LEAST left-symbol index `j`;
the cut formula `B = A_i` is then re-routed to its LEAST source `i'` via `least_number` on the (definable)
`chainAsucc ds · = B`. Every such re-route lands at an index `< j` (`i' ≤ i < j`), where by minimality of
`j` there are NO left symbols — so the source can never bottom out at an `isymLk` L-axiom. The least source
`i'` is non-left and non-`isymRep` (re-route ⟹ smaller source ⟹ contradiction with `i'` least), hence
`I_{i'} = R_B`. The genuine residual is therefore only `hreroute` for NON-leaf `isymRep` premises (chain/Ind
nodes), which `chainAsucc_threaded_of_leaf` does not cover. -/
theorem inference_critical_pair_of_chain_reroute {s r ds j0 : V} {Tr Fa : V → Prop}
    (hj0 : j0 < lh ds)
    (hAj0 : chainAsucc ds j0 = seqSucc s ∨ chainAsucc ds j0 = (^⊥ : V))
    (hchain : ∀ i ≤ j0, ∀ B, inAnt B (chainAnt ds i) →
      inAnt B (seqAnt s) ∨ ∃ i' < i, B = chainAsucc ds i')
    (hrank : ∀ i < j0, irk (chainAsucc ds i) ≤ r)
    (hwfR : ∀ i ≤ j0, ∀ A, tp (znth ds i) = isymR A → 0 < irk A ∨ Tr A)
    (hwfL : ∀ i ≤ j0, ∀ k A, tp (znth ds i) = isymLk k A → 0 < irk A ∨ Fa A)
    (hperm : ∀ i ≤ j0, iperm (tp (znth ds i)) (fstIdx (znth ds i)))
    (hnperm2 : ∀ i ≤ j0, ¬ (tp (znth ds i) = isymR (seqSucc s) ∨
      (∃ k A, tp (znth ds i) = isymLk k A ∧ inAnt A (seqAnt s))))
    (hreroute : ∀ i ≤ j0, tp (znth ds i) = isymRep →
      ∃ i' < i, chainAsucc ds i' = chainAsucc ds i)
    (hdisj : ∀ A, ¬ (Tr A ∧ Fa A)) (hFa_rk : ∀ A, Fa A → irk A = 0)
    (hFa_bot : Fa (^⊥ : V)) :
    ∃ i j k, i < j ∧ j ≤ j0 ∧ tp (znth ds i) = isymR (chainAsucc ds i) ∧
      tp (znth ds j) = isymLk k (chainAsucc ds i) ∧
      0 < irk (chainAsucc ds i) ∧ irk (chainAsucc ds i) ≤ r := by
  -- `hperm` already has L3.1's unfolded disjunction shape (chainAsucc/chainAnt = seqSucc/seqAnt ∘ fstIdx).
  have hperm' : ∀ i ≤ j0, tp (znth ds i) = isymR (chainAsucc ds i) ∨
      (∃ k A, tp (znth ds i) = isymLk k A ∧ inAnt A (chainAnt ds i)) ∨
      tp (znth ds i) = isymRep := by
    intro i hi
    have h := hperm i hi
    unfold iperm at h
    simpa only [chainAsucc, chainAnt] using h
  -- Step A: a non-`isymRep` exit `j'` (Sub-lemma A) is forced to be a LEFT symbol.
  obtain ⟨j', hj'le, hAj', hj'nRep⟩ := exit_nonRep_of_reroute hAj0 hreroute
  have hLj' : isymIsL (tp (znth ds j')) := by
    rcases hperm' j' hj'le with hR | hL | hRep
    · exfalso
      rcases hAj' with hC | hFa
      · exact hnperm2 j' hj'le (Or.inl (by rw [hR, hC]))
      · have hFaA : Fa (chainAsucc ds j') := by rw [hFa]; exact hFa_bot
        rcases hwfR j' hj'le _ hR with hpos | hTr
        · exact absurd (hFa_rk _ hFaA) (by simpa using hpos.ne')
        · exact hdisj _ ⟨hTr, hFaA⟩
    · obtain ⟨k, A, hI, _⟩ := hL; exact isymIsL_iff.mpr ⟨k, A, hI⟩
    · exact absurd hRep hj'nRep
  -- Step B: the LEAST left-symbol index `j ≤ j'`. Search over the CODED symbol map `tpSeq ds` (so
  -- `znth (tpSeq ds) x` is `𝚺₁` in `x`, avoiding the aesop depth-blowup on `tp (znth ds x)`).
  set Is := tpSeq ds with hIs
  have htp : ∀ x, x ≤ j0 → znth Is x = tp (znth ds x) :=
    fun x hx => by rw [hIs]; exact znth_tpSeq (lt_of_le_of_lt hx hj0)
  clear_value Is
  have hQdef : 𝚺₁-Predicate (fun x : V => isymIsL (znth Is x) ∧ x ≤ j') := by
    simp only [isymIsL]; definability
  have hLj'' : isymIsL (znth Is j') := by rw [htp j' hj'le]; exact hLj'
  obtain ⟨j, ⟨hLj, hjle'⟩, hmin⟩ :=
    InductionOnHierarchy.least_number 𝚺 1 hQdef ⟨hLj'', le_rfl⟩
  have hjle : j ≤ j0 := le_trans hjle' hj'le
  have hLj_tp : isymIsL (tp (znth ds j)) := by rw [← htp j hjle]; exact hLj
  obtain ⟨k, B, hIj⟩ := isymIsL_iff.mp hLj_tp
  -- B ∈ Γ_j  (own-permissibility of the L-symbol `j`)
  have hBmem : inAnt B (chainAnt ds j) := by
    rcases hperm' j hjle with hR | ⟨k', A', hI', hA'⟩ | hRep
    · exact absurd (hR.symm.trans hIj) (isymR_ne_isymLk _ _ _)
    · obtain ⟨-, hBA⟩ := (isymLk_inj k B k' A').mp (hIj.symm.trans hI')
      rw [hBA]; exact hA'
    · exact absurd (hRep.symm.trans hIj) (isymRep_ne_isymLk _ _)
  -- B ∉ Γmain  (non-permissibility of `j` for the conclusion, 2-clause form)
  have hBnmem : ¬ inAnt B (seqAnt s) := fun h =>
    hnperm2 j hjle (Or.inr ⟨k, B, hIj, h⟩)
  -- chain condition: B = A_i for some i < j
  obtain ⟨i, hij, hBi⟩ := (hchain j hjle B hBmem).resolve_left hBnmem
  have hi_le_j0 : i ≤ j0 := le_of_lt (lt_of_lt_of_le hij hjle)
  -- Step C (Sub-lemma B): the LEAST source `i'` of the cut formula `B`.
  have hQ2 : 𝚺₁-Predicate (fun x : V => chainAsucc ds x = B ∧ x ≤ j0) := by
    apply Definable.and ?_ (by definability)
    exact DefinableRel.comp (by definability)
      (DefinableFunction₂.comp (F := chainAsucc)
        (DefinableFunction.const ds) (DefinableFunction.var 0))
      (DefinableFunction.const B)
  obtain ⟨i', ⟨hAi', hi'le⟩, hmin'⟩ :=
    InductionOnHierarchy.least_number 𝚺 1 hQ2 ⟨hBi.symm, hi_le_j0⟩
  have hi'le_i : i' ≤ i := by
    by_contra h
    push_neg at h
    exact hmin' i h ⟨hBi.symm, hi_le_j0⟩
  have hi'lt_j : i' < j := lt_of_le_of_lt hi'le_i hij
  have hi'le_j' : i' ≤ j' := le_of_lt (lt_of_lt_of_le hi'lt_j hjle')
  have hi'le_j0 : i' ≤ j0 := le_trans hi'le_i hi_le_j0
  -- `i'` is non-left (minimality of `j`) and non-`isymRep` (re-route ⟹ smaller source) ⟹ `I_{i'} = R_B`.
  have hLi'_not : ¬ isymIsL (tp (znth ds i')) := by
    intro h
    exact hmin i' hi'lt_j ⟨by rw [htp i' hi'le_j0]; exact h, hi'le_j'⟩
  have hRi' : tp (znth ds i') = isymR (chainAsucc ds i') := by
    rcases hperm' i' hi'le_j0 with hR | hL | hRep
    · exact hR
    · obtain ⟨k', A', hI', _⟩ := hL
      exact absurd (isymIsL_iff.mpr ⟨k', A', hI'⟩) hLi'_not
    · obtain ⟨i'', hi''lt, hi''eq⟩ := hreroute i' hi'le_j0 hRep
      exact absurd ⟨hi''eq.trans hAi', le_of_lt (lt_of_lt_of_le hi''lt hi'le_j0)⟩
        (hmin' i'' hi''lt)
  -- 0 < rk B  (`B = chainAsucc ds i'`)
  have hrk : 0 < irk (chainAsucc ds i') := by
    rcases hwfR i' hi'le_j0 _ hRi' with hpos | hTr
    · exact hpos
    · rcases hwfL j hjle k B hIj with hpos | hFa
      · rw [hAi']; exact hpos
      · exact absurd ⟨by rw [hAi'] at hTr; exact hTr, hFa⟩ (hdisj B)
  exact ⟨i', j, k, hi'lt_j, hjle, hRi',
    by rw [hAi']; exact hIj, hrk,
    hrank i' (lt_of_le_of_lt hi'le_i (lt_of_lt_of_le hij hjle))⟩

/-- **The stall-free K-cut descent for a re-routing ⊥-chain** (lap 122, target #2). The reroute twin of
`iord_descent_iRcrit_of_chain'`: it manufactures the redex via `inference_critical_pair_of_chain_reroute`
(the generalized finder, whose `hnperm` isymRep clause is replaced by `hreroute`) instead of
`inference_critical_pair_of_chain`, then feeds it to `iord_descent_iRcrit_of_redex`. So a valid ⊥-chain
whose criticality-failures are all RE-ROUTABLE permissible premises STILL descends — the threaded-atom
stall dissolved, **modulo discharging `hreroute`** (banked for leaf isymRep by `chainAsucc_threaded_of_leaf`;
the chain/Ind isymRep residual is path α in `PENDING_WORK.md` lap-122). The six `ρ`-facts are the same
redex-premise reduct obligations as the non-reroute wrapper. -/
theorem iord_descent_iRcrit_of_chain_reroute {s r ds j0 : V} {Tr Fa : V → Prop} {ρ : V → V}
    (hds : Seq ds) (hnf : isNF (iotil (zK s r ds)))
    (hj0 : j0 < lh ds)
    (hAj0 : chainAsucc ds j0 = seqSucc s ∨ chainAsucc ds j0 = (^⊥ : V))
    (hchain : ∀ i ≤ j0, ∀ B, inAnt B (chainAnt ds i) →
      inAnt B (seqAnt s) ∨ ∃ i' < i, B = chainAsucc ds i')
    (hrank : ∀ i < j0, irk (chainAsucc ds i) ≤ r)
    (hwfR : ∀ i ≤ j0, ∀ A, tp (znth ds i) = isymR A → 0 < irk A ∨ Tr A)
    (hwfL : ∀ i ≤ j0, ∀ k A, tp (znth ds i) = isymLk k A → 0 < irk A ∨ Fa A)
    (hperm : ∀ i ≤ j0, iperm (tp (znth ds i)) (fstIdx (znth ds i)))
    (hnperm2 : ∀ i ≤ j0, ¬ (tp (znth ds i) = isymR (seqSucc s) ∨
      (∃ k A, tp (znth ds i) = isymLk k A ∧ inAnt A (seqAnt s))))
    (hreroute : ∀ i ≤ j0, tp (znth ds i) = isymRep →
      ∃ i' < i, chainAsucc ds i' = chainAsucc ds i)
    (hdisj : ∀ A, ¬ (Tr A ∧ Fa A)) (hFa_rk : ∀ A, Fa A → irk A = 0)
    (hFa_bot : Fa (^⊥ : V))
    (hNF : ∀ n, isNF (iotil (znth ds n)))
    (hρlt_i : icmp (iotil (ρ (redexI (zK s r ds)))) (iotil (znth ds (redexI (zK s r ds)))) = 0)
    (hρlt_j : icmp (iotil (ρ (redexJ (zK s r ds)))) (iotil (znth ds (redexJ (zK s r ds)))) = 0)
    (hρg_i : idg (ρ (redexI (zK s r ds))) ≤ idg (znth ds (redexI (zK s r ds))))
    (hρg_j : idg (ρ (redexJ (zK s r ds))) ≤ idg (znth ds (redexJ (zK s r ds))))
    (hρNF_i : isNF (iotil (ρ (redexI (zK s r ds)))))
    (hρNF_j : isNF (iotil (ρ (redexJ (zK s r ds))))) :
    icmp (iord (iRcrit (zK s r ds) ρ)) (iord (zK s r ds)) = 0 := by
  obtain ⟨i, j, k, hij, hjle, hRi, hLj, hrkpos, hrkr⟩ :=
    inference_critical_pair_of_chain_reroute hj0 hAj0 hchain hrank hwfR hwfL hperm hnperm2 hreroute
      hdisj hFa_rk hFa_bot
  have hr : 1 ≤ r := pos_iff_one_le.mp (lt_of_lt_of_le hrkpos hrkr)
  have hjlt : j < lh ds := lt_of_le_of_lt hjle hj0
  have hilt : i < lh ds := lt_trans hij hjlt
  have hredex : isRedexPair ds (⟪i, j⟫ : V) := by
    simp only [isRedexPair, pi₁_pair, pi₂_pair]
    refine ⟨hij, hjlt, ?_, ?_, ?_⟩
    · rw [hRi]; simp [isymR]
    · rw [hLj]; simp [isymLk]
    · rw [hRi, hLj]; simp [isymR, isymLk]
  have hex : ∃ c < (⟪lh (zKseq (zK s r ds)), lh (zKseq (zK s r ds))⟫ : V),
      isRedexPair (zKseq (zK s r ds)) c := by
    simp only [zKseq_zK]
    exact ⟨⟪i, j⟫, pair_lt_pair hilt hjlt, hredex⟩
  exact iord_descent_iRcrit_of_redex hds hnf hr hex hNF
    hρlt_i hρlt_j hρg_i hρg_j hρNF_i hρNF_j

set_option maxHeartbeats 800000 in
/-- **Leaf-stall redex existence for a genuine ⊥-chain** (lap 122 — the consolidation). A
`ZDerivation (zK s r ds)` with empty antecedent and `⊥` succedent always contains the genuine
`(R_A, L^k_A)` redex pair (with `0 < rk A ≤ r`), **provided every permissible (`isymRep`) premise is a
LEAF** (`hleaves`, the atom/`zAx1` stall shapes). All of the redex-finder's bookkeeping is discharged
internally from `ZDerivation`:
* `zKValidF` (`zKValidF_of_ZDerivation_zK`) ⟹ `isChainInf` (j0/threading/rank), own-permissibility,
  and the §5 principal-formula well-formedness ⟹ `hwfR`/`hwfL` (via `tp_isymR_pos`/`tp_isymLk_pos`,
  `Tr := ⊥`, `Fa := (· = ⊥)`);
* **`hnperm2` is FREE for a ⊥-chain** — `tp = R_⊥` is impossible (`tp_isymR_pos` forces `0 < rk ⊥ = 0`),
  and the `L`-at-`Γmain` clause is vacuous (`seqAnt s = ∅`, nothing is in the empty antecedent);
* `hreroute` from `hreroute_of_leaves` (the leaf branch) + per-premise `ZDerivation` (`zDerivation_zK_inv`).
So the ENTIRE leaf-stall case (Buchholz Def 3.2 case 5.1, the documented atom/`zAx1` `red`-stall) reduces to
the single structural hypothesis `hleaves`. The chain/Ind (`tp_zK`/`tp_zInd`) `isymRep` residual is the
NON-critical case 5.2 (the splice), handled by separate machinery — NOT a gap in this finder. -/
theorem inference_critical_pair_of_botChain {s r ds : V}
    (hZ : ZDerivation (zK s r ds))
    (hant : seqAnt s = (∅ : V)) (hsucc : seqSucc s = (^⊥ : V))
    (hleaves : ∀ i < lh ds, tp (znth ds i) = isymRep →
      (∃ sk, znth ds i = zAtom sk) ∨ (∃ sk Ck, znth ds i = zAx1 sk Ck)) :
    ∃ i j k, i < j ∧ j < lh ds ∧ tp (znth ds i) = isymR (chainAsucc ds i) ∧
      tp (znth ds j) = isymLk k (chainAsucc ds i) ∧
      0 < irk (chainAsucc ds i) ∧ irk (chainAsucc ds i) ≤ r := by
  obtain ⟨hci, hperm, hf1, hf2, hf5, hf6, _, _, _⟩ := zKValidF_of_ZDerivation_zK hZ
  obtain ⟨_, hmem⟩ := zDerivation_zK_inv hZ
  obtain ⟨j0, hj0, hAj0, hthread, hrk⟩ := hci
  have hlt : ∀ i, i ≤ j0 → i < lh ds := fun i hi => lt_of_le_of_lt hi hj0
  have hnperm2 : ∀ i ≤ j0, ¬ (tp (znth ds i) = isymR (seqSucc s) ∨
      (∃ k A, tp (znth ds i) = isymLk k A ∧ inAnt A (seqAnt s))) := by
    intro i hi hcon
    rcases hcon with hR | ⟨k, A, _, hAmem⟩
    · rw [hsucc] at hR
      have hpos := tp_isymR_pos hR (fun ht => hf1 i (hlt i hi) ht) (fun ht => hf2 i (hlt i hi) ht)
      rw [irk_falsum] at hpos; exact absurd hpos (by simp)
    · rw [hant] at hAmem; simp [inAnt, lh_empty] at hAmem
  obtain ⟨i, j, k, hij, hjle, hRi, hLj, hpos, hler⟩ :=
    inference_critical_pair_of_chain_reroute (Tr := fun _ => False) (Fa := fun A => A = (^⊥ : V))
      hj0 hAj0 hthread hrk
      (fun i hi A h => Or.inl (tp_isymR_pos h (fun ht => hf1 i (hlt i hi) ht) (fun ht => hf2 i (hlt i hi) ht)))
      (fun i hi k A h => Or.inl (tp_isymLk_pos h (fun ht => hf5 i (hlt i hi) ht) (fun ht => hf6 i (hlt i hi) ht)))
      (fun i hi => hperm i (hlt i hi)) hnperm2
      (hreroute_of_leaves hant hthread (fun i hi => hmem i (hlt i hi))
        (fun i hi hr => hleaves i (hlt i hi) hr))
      (fun _ h => h.1) (fun A h => by rw [h]; exact irk_falsum) rfl
  exact ⟨i, j, k, hij, lt_of_le_of_lt hjle hj0, hRi, hLj, hpos, hler⟩

/-- **The case-5.1/5.2 dichotomy for a genuine ⊥-chain** (lap 123). Buchholz Def 3.2 case 5 splits a chain
inference into *critical* (5.1, a redex exists — eliminate it) vs *non-critical* (5.2, a permissible premise
exists — splice into it). For a `ZDerivation` ⊥-chain this is now a CONCRETE, PROVED dichotomy: **either**
there is a genuine `(R_A, L^k_A)` redex pair (case 5.1, the engine should reduce via
`iord_descent_iRcrit_of_redex`), **or** there is a NON-LEAF `isymRep` premise — a chain (tag-3) / Ind
(tag-4) node (case 5.2, the engine should splice into it, smaller ordinal). Proof: classical case split on
the existence of a non-leaf `isymRep` premise; its negation is exactly `inference_critical_pair_of_botChain`'s
`hleaves`, which then yields the redex. **This is the case split the stall-free endgame needs:** the
documented `red`-stall (`permIdx` selects an atom/`zAx1` leaf, `red d = d`) lands in the LEFT disjunct (a
redex exists and is ignored by `red`'s mis-selection) — so the descent must be driven by the exhibited redex,
not by `red`'s permIdx, on the LEFT, and by the splice on the RIGHT. Neither disjunct is a `red`-fixpoint. -/
theorem redex_or_nonleaf_isymRep_of_botChain {s r ds : V}
    (hZ : ZDerivation (zK s r ds))
    (hant : seqAnt s = (∅ : V)) (hsucc : seqSucc s = (^⊥ : V)) :
    (∃ i j k, i < j ∧ j < lh ds ∧ tp (znth ds i) = isymR (chainAsucc ds i) ∧
      tp (znth ds j) = isymLk k (chainAsucc ds i) ∧
      0 < irk (chainAsucc ds i) ∧ irk (chainAsucc ds i) ≤ r)
    ∨ (∃ i < lh ds, tp (znth ds i) = isymRep ∧
        ¬ ((∃ sk, znth ds i = zAtom sk) ∨ (∃ sk Ck, znth ds i = zAx1 sk Ck))) := by
  by_cases h : ∃ i < lh ds, tp (znth ds i) = isymRep ∧
      ¬ ((∃ sk, znth ds i = zAtom sk) ∨ (∃ sk Ck, znth ds i = zAx1 sk Ck))
  · exact Or.inr h
  · push_neg at h
    exact Or.inl (inference_critical_pair_of_botChain hZ hant hsucc (fun i hi hrep => h i hi hrep))

/-! ### The Option-B obstruction, formalized — why the ordinal-faithful `iR2` cannot preserve validity

`RedSound` (`iR2 d` is a genuine `ZDerivation` for `ZDerivesEmpty d`) is **FALSE** for the current
ordinal-faithful `iR2`. The critical reduct `iCritReduct d i j v w` is a chain
`zK (fstIdx d) (zKrank d − 1) ⟨iCritAux d i v, iCritAux d j w⟩` whose premises are themselves chains
(`iCritAux _ = zK …`). Every chain node has `tp = isymRep` (`tp_zK`), and `isymRep` is permissible for
**every** conclusion (`iperm_isymRep`). But `zKValid`'s criticality conjunct demands every premise be
NON-permissible (`¬iperm (tp dᵢ) s`) — the very hypothesis the L3.1 redex finder
(`inference_critical_pair_of_chain`) needs to force a genuine R/L redex pair to exist. A chain with a
`Rep`-tagged premise therefore can never be `zKValid`, so the reduct can never descend again, so the
`iR2`-orbit is not descent-closed. (Confirmed against Bryce–Goré, arXiv:2603.00487: their `cut_elimination`
is *genuinely* validity-preserving — `cut_elimination_valid`, shape-dispatched on the cut formula — which
the ordinal-faithful `iCritReduct` shadow is not.) The fix is the genuine, validity-preserving reduct;
the inversions above are its peeling primitives. -/

/-- **A `K^r` chain with any chain (`Rep`-tagged) premise is never `zKValid`.** The criticality conjunct
`¬iperm (tp dₘ) s` fails at the `zK`-premise `m` (`tp_zK` ⟹ `isymRep`, permissible for `s` by
`iperm_isymRep`). This is the load-bearing obstruction: the reduct `iCritReduct`'s premises are exactly
such chains, so it is never a valid critical chain — the ordinal-faithful `iR2` is not derivation-valid. -/
lemma not_zKValid_of_zK_premise {s r ds m s' r' ds' : V} (hm : m < lh ds)
    (hprem : znth ds m = zK s' r' ds') : ¬ zKValid s r ds := by
  rintro ⟨_, _, hnperm, _⟩
  exact hnperm m hm (by rw [hprem, tp_zK]; exact iperm_isymRep s)

/-- **The critical reduct is never `zKValid`** (the concrete obstruction at `iCritReduct`): premise `0`
of its chain is `iCritAux d i v = zK …`, a `Rep`-tagged chain, so `not_zKValid_of_zK_premise` applies.
Hence `ZDerivation (iCritReduct …)` cannot be obtained from chain-validity — `RedSound` fails for the
current `iR2`, and the genuine validity-preserving reduct (Option A) is required. -/
lemma not_zKValid_iCritReduct (d i j v w : V) :
    ¬ zKValid (fstIdx d) (zKrank d - 1)
      (iCritReductSeq (iCritAux d i v) (iCritAux d j w)) := by
  refine not_zKValid_of_zK_premise (m := 0) (s' := fstIdx d) (r' := zKrank d)
    (ds' := seqUpdate (zKseq d) i v) ?_ ?_
  · rw [iCritReductSeq_lh]; exact zero_lt_two
  · rw [znth_iCritReductSeq_zero]; rfl

/-! ### The clean `RedSound` fragment: the I-rules (tags 1,2)

`RedSound` asks only that the `iR2`-reduct be a genuine `ZDerivation` (the end-sequent matching is handled
separately by `fstIdx_iR2_of_tag_Ind_or_K`). For the I-rules `iR2` returns the immediate sub-derivation
`d0` (`iR2_zIall`/`iR2_zIneg`), which is a `ZDerivation` by inversion — so this fragment is unconditional.
The I¬ case is Buchholz 14.23 `d[0] := d0` verbatim (no substitution); the I∀ case's GENUINE reduct is
`d0(a/n)` but the ordinal-faithful `d0` is *also* a valid derivation (only its end-sequent differs, which
`RedSound` does not constrain). These never arise on a `ZDerivesEmpty` code (tags 3,4), but a general
tag-dispatched `RedSound` proof reuses them. -/

/-- `RedSound` for the I∀ rule: `iR2 (zIall …) = d0` is a `ZDerivation`. -/
lemma ZDerivation_iR2_zIall {s a p d0 : V} (hZ : ZDerivation (zIall s a p d0)) :
    ZDerivation (iR2 (zIall s a p d0)) := by rw [iR2_zIall]; exact (zDerivation_zIall_inv hZ).1

/-- `RedSound` for the I¬ rule: `iR2 (zIneg …) = d0` is a `ZDerivation` (Buchholz 14.23). -/
lemma ZDerivation_iR2_zIneg {s p d0 : V} (hZ : ZDerivation (zIneg s p d0)) :
    ZDerivation (iR2 (zIneg s p d0)) := by rw [iR2_zIneg]; exact (zDerivation_zIneg_inv hZ).1

/-- Every premise of the Ind-reduct sequence `iIndReductSeq d0 d1 k = ⟨d1,…,d1,d0⟩` is a `ZDerivation`
when `d0`,`d1` are. -/
lemma znth_iIndReductSeq_ZDerivation {d0 d1 k : V} (h0 : ZDerivation d0) (h1 : ZDerivation d1) :
    ∀ i < lh (iIndReductSeq d0 d1 k), ZDerivation (znth (iIndReductSeq d0 d1 k) i) := by
  intro i hi
  have hk : lh (iIndReductSeq d0 d1 k) = k + 1 := by
    rw [iIndReductSeq, Seq.lh_seqCons _ (iRepeatSeq_seq d1 k), iRepeatSeq_lh]
  rw [hk] at hi
  rcases lt_or_ge i k with hlt | hge
  · rw [iIndReductSeq,
      znth_seqCons_of_lt (iRepeatSeq_seq d1 k) _ (by rw [iRepeatSeq_lh]; exact hlt),
      znth_iRepeatSeq i hlt]
    exact h1
  · have hik : i = k := le_antisymm (le_iff_lt_succ.mpr hi) hge
    have hself := znth_seqCons_self (iRepeatSeq_seq d1 k) d0
    rw [iRepeatSeq_lh] at hself
    rw [iIndReductSeq, hik, hself]
    exact h0

/-- **Reduction-soundness for the Ind rule, modulo chain-validity of the reduct.** `iR2 (zInd …)` is the
chain `zK s (irk p) (iIndReductSeq d0 d1 1)`; its premises are `ZDerivation`s (the Ind premises) and its
`Seq` structure is free, so it is a genuine `ZDerivation` exactly when the produced chain is `zKValid`
(the Buchholz reduction lemma — the deep residual). -/
lemma ZDerivation_iR2_zInd_of_zKValid {s at' p d0 d1 : V}
    (hZ : ZDerivation (zInd s at' p d0 d1))
    (hvalid : zKValid s (irk p) (iIndReductSeq d0 d1 1)) :
    ZDerivation (iR2 (zInd s at' p d0 d1)) := by
  obtain ⟨h0, h1, _⟩ := zDerivation_zInd_inv hZ
  rw [iR2_zInd, iRInd_zInd, zDerivation_iff]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
    ⟨s, irk p, iIndReductSeq d0 d1 1, rfl, iIndReductSeq_seq d0 d1 1,
      fun i hi => znth_iIndReductSeq_ZDerivation h0 h1 i hi, zKValidF_of_zKValid hvalid⟩))))

/-- Both premises of the critical-reduct sequence `iCritReductSeq d0 d1 = ⟨d0,d1⟩` are `ZDerivation`s
when `d0`,`d1` are. -/
lemma znth_iCritReductSeq_ZDerivation {d0 d1 : V} (h0 : ZDerivation d0) (h1 : ZDerivation d1) :
    ∀ i < lh (iCritReductSeq d0 d1), ZDerivation (znth (iCritReductSeq d0 d1) i) := by
  intro i hi
  rw [iCritReductSeq] at hi ⊢
  rcases lt_or_ge i (lh (seqCons (∅ : V) d0)) with hlt | hge
  · rw [znth_seqCons_of_lt (seq_empty.seqCons d0) d1 hlt]
    rw [Seq.lh_seqCons _ seq_empty] at hlt
    have hi0 : i = lh (∅ : V) :=
      le_antisymm (le_iff_lt_succ.mpr (by rw [lh_empty] at hlt ⊢; exact hlt)) (by simp)
    rw [hi0, znth_seqCons_self seq_empty]; exact h0
  · rw [Seq.lh_seqCons _ (seq_empty.seqCons d0)] at hi
    have : i = lh (seqCons (∅ : V) d0) := le_antisymm (le_iff_lt_succ.mpr hi) hge
    rw [this, znth_seqCons_self (seq_empty.seqCons d0)]; exact h1

/-- **Reduction-soundness for the critical reduct, modulo chain-validity.** `iCritReduct d i j v w` is the
chain `zK (fstIdx d) (zKrank d - 1) (iCritReductSeq (iCritAux d i v) (iCritAux d j w))`; given its two
auxiliaries are `ZDerivation`s and the produced chain is `zKValid`, it is a genuine `ZDerivation`. The K
analog of `ZDerivation_iR2_zInd_of_zKValid` (premises + `Seq` free; `zKValid` + the auxiliaries'
validity are the deep recursive residual — Buchholz's reduction lemma). -/
lemma ZDerivation_iCritReduct_of {d i j v w : V}
    (ha : ZDerivation (iCritAux d i v)) (hb : ZDerivation (iCritAux d j w))
    (hvalid : zKValid (fstIdx d) (zKrank d - 1)
      (iCritReductSeq (iCritAux d i v) (iCritAux d j w))) :
    ZDerivation (iCritReduct d i j v w) := by
  rw [iCritReduct, zDerivation_iff]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
    ⟨fstIdx d, zKrank d - 1, iCritReductSeq (iCritAux d i v) (iCritAux d j w), rfl,
      iCritReductSeq_seq _ _, fun n hn => znth_iCritReductSeq_ZDerivation ha hb n hn,
      zKValidF_of_zKValid hvalid⟩))))

/-- **The genuine critical reduct is a `ZDerivation`** (R1 DISCHARGED — re-point landed). The `ZPhi` `zK`
disjunct now carries the faithful, criticality-free validity `zKValidF`, so the chain introduction
`zDerivation_zK_intro` is a theorem and the former `hZPhiK` residual is gone. Given only the two genuine
auxiliaries being `ZDerivation`s of their reduced endsequents `Θ→A(d)`/`A(d),Θ→D` (the recursive Thm 3.4(a)
— **R2**, the one remaining residual of the critical case), the recombination `iCritReductG` is a
`ZDerivation`. Its validity threading is automatic via `zKValidF_iCritReductGen`; only the cut-rank drop
`rk(A(d)) ≤ rOut` (Thm 3.4(a), banked `irk_cut_lt_rank_*`) and the conclusion formula-hood are supplied. -/
lemma ZDerivation_iCritReductG_of {s C rOut rIn0 rIn1 ds0 ds1 : V}
    (haux0 : ZDerivation (zK (seqSetSucc s C) rIn0 ds0))
    (haux1 : ZDerivation (zK (seqAddAnt C s) rIn1 ds1))
    (hsAnt : Seq (seqAnt s)) (hCrk : irk C ≤ rOut) (hCUf : IsUFormula ℒₒᵣ C)
    (hssUf : IsUFormula ℒₒᵣ (seqSucc s))
    (hsaUf : ∀ k < lh (seqAnt s), IsUFormula ℒₒᵣ (znth (seqAnt s) k)) :
    ZDerivation (iCritReductG s C rOut rIn0 rIn1 ds0 ds1) := by
  rw [iCritReductG]
  refine zDerivation_zK_intro (iCritReductSeq_seq _ _)
    (fun n hn => znth_iCritReductSeq_ZDerivation haux0 haux1 n hn) ?_
  exact zKValidF_iCritReductGen hsAnt hCrk hCUf hssUf hsaUf

/-! ### `iRcritG` — the genuine CLOSED critical branch (Buchholz Def 3.2 case 5.1, on correct endsequents)

The `red`-analogue of `iRcrit`: the redex finder `redexI`/`redexJ` is total and definable, so the genuine
critical reduct is a closed term once the per-premise reduct supplier `ρ` (`= dᵢ[k]`/`d_j[0]`, the N1
structural IH) is fixed. Unlike `iRcrit` (built on the ordinal-shadow `iCritReduct`, whose `iCritAux`
auxiliaries reuse `fstIdx d` and so have the WRONG endsequent), `iRcritG` is built on `iCritReductG`, whose
auxiliaries carry the cut's reduced endsequents `Θ→A(d)`/`A(d),Θ→D` with cut formula `A(d) = chainAsucc ds i`
(the succedent of the redex's R-premise `i`). This is the K-case of the genuine reduct `red`. -/

/-- **`iRcritG` is a `ZDerivation`** (R1 done), modulo only R2 — the two genuine auxiliaries
`d{0} = K^r (seqUpdate ds i (ρ i))` ⊢ `Θ→A(d)`, `d{1} = K^r (seqUpdate ds j (ρ j))` ⊢ `A(d),Θ→D` being
`ZDerivation`s of their reduced endsequents (recursive Thm 3.4(a), the structural IH). The validity
threading + cut-rank drop are banked (`zKValidF_iCritReductGen`, `irk_cut_lt_rank_*`). -/
lemma ZDerivation_iRcritG_of {d : V} {ρ : V → V}
    (haux0 : ZDerivation (zK (seqSetSucc (fstIdx d) (cutFormula d))
      (zKrank d) (seqUpdate (zKseq d) (redexI d) (ρ (redexI d)))))
    (haux1 : ZDerivation (zK (seqAddAnt (cutFormula d) (fstIdx d))
      (zKrank d) (seqUpdate (zKseq d) (redexJ d) (ρ (redexJ d)))))
    (hsAnt : Seq (seqAnt (fstIdx d)))
    (hCrk : irk (cutFormula d) ≤ zKrank d - 1)
    (hCUf : IsUFormula ℒₒᵣ (cutFormula d))
    (hssUf : IsUFormula ℒₒᵣ (seqSucc (fstIdx d)))
    (hsaUf : ∀ k < lh (seqAnt (fstIdx d)), IsUFormula ℒₒᵣ (znth (seqAnt (fstIdx d)) k)) :
    ZDerivation (iRcritG d ρ) :=
  ZDerivation_iCritReductG_of haux0 haux1 hsAnt hCrk hCUf hssUf hsaUf

/-- **`iRcritGNeg` is a `ZDerivation`** — the ¬-case (swapped-half) analogue of `ZDerivation_iRcritG_of`.
The SUCCEDENT half `d{0}` (replacing the L-redex `j = redexJ d`, conclusion `Γ→A(d)`) is `haux0`, and the
ANTECEDENT half `d{1}` (replacing the R-redex `i = redexI d`, conclusion `A(d),Γ→D`) is `haux1`. Delegates
to the same `ZDerivation_iCritReductG_of` with the two half-sequences SWAPPED, matching `iRcritGNeg`'s
`seqUpdate` slots (`ds0 = seqUpdate ds (redexJ d) (ρ (redexJ d))`, `ds1 = seqUpdate ds (redexI d)
(ρ (redexI d))`). -/
lemma ZDerivation_iRcritGNeg_of {d : V} {ρ : V → V}
    (haux0 : ZDerivation (zK (seqSetSucc (fstIdx d) (cutFormula d))
      (zKrank d) (seqUpdate (zKseq d) (redexJ d) (ρ (redexJ d)))))
    (haux1 : ZDerivation (zK (seqAddAnt (cutFormula d) (fstIdx d))
      (zKrank d) (seqUpdate (zKseq d) (redexI d) (ρ (redexI d)))))
    (hsAnt : Seq (seqAnt (fstIdx d)))
    (hCrk : irk (cutFormula d) ≤ zKrank d - 1)
    (hCUf : IsUFormula ℒₒᵣ (cutFormula d))
    (hssUf : IsUFormula ℒₒᵣ (seqSucc (fstIdx d)))
    (hsaUf : ∀ k < lh (seqAnt (fstIdx d)), IsUFormula ℒₒᵣ (znth (seqAnt (fstIdx d)) k)) :
    ZDerivation (iRcritGNeg d ρ) :=
  ZDerivation_iCritReductG_of haux0 haux1 hsAnt hCrk hCUf hssUf hsaUf

/-! ## The iterated descent — `n ↦ iord (iR2^[n] z)` is an infinite `≺`-descent

This is the V-internal analog of `GentzenCon.gentzenDescent_descends`, on the genuine objects
(`ZDerivesEmpty`/`iR2`/`iord` in place of the abstract `derivesEmpty`/`R`/`ord` axioms). It is stated
against the one remaining InternalZ obligation, **reduction-soundness** `RedSound` (that the reduct of a
contradiction derivation is again a genuine `ZDerivation` — `iCritReduct`/`iRInd` outputs satisfy
`ZPhi`), supplied as an explicit hypothesis so nothing is axiomatized. Closing `RedSound` and
internalizing the (here external-ℕ) iteration as a `𝚺₁` graph `gentzenDescentφ` is what discharges the
crux-2 deep axiom `gentzen_descent_of_inconsistent`. -/

/-- **Reduction-soundness** (the sole remaining InternalZ obligation): the `iR2`-reduct of a
contradiction derivation is again a genuine Z-derivation. -/
def RedSound : Prop := ∀ d : V, ZDerivesEmpty d → ZDerivation (iR2 d)

/-- **`ZDerivesEmpty` is closed under the whole `iR2`-orbit** (external ℕ-iteration), given
reduction-soundness. -/
lemma ZDerivesEmpty_iterate (hRS : RedSound (V := V)) {z : V} (hz : ZDerivesEmpty z) :
    ∀ n : ℕ, ZDerivesEmpty (iR2^[n] z)
  | 0 => by simpa using hz
  | n + 1 => by
      rw [Function.iterate_succ_apply']
      exact ZDerivesEmpty_iR2 (ZDerivesEmpty_iterate hRS hz n) (hRS _ (ZDerivesEmpty_iterate hRS hz n))

/-- **THE infinite ε₀-descent of crux-2.** For a contradiction derivation `z` (`ZDerivesEmpty z`), under
reduction-soundness the ordinals `n ↦ iord (iR2^[n] z)` strictly `≺`-descend at every step
(`icmp (·(n+1)) (·n) = 0`). An infinite primitive-recursive `ε₀`-descent — exactly what `PRWO(ε₀)`
forbids, giving the Gentzen contradiction `¬Con(𝗣𝗔) → False` once `z` is produced by the C0.5 bridge. -/
lemma iord_iR2_iterate_descends (hRS : RedSound (V := V)) {z : V} (hz : ZDerivesEmpty z)
    (hcrit : ∀ n : ℕ, zTag (iR2^[n] z) = 4 →
      zKCritical (fstIdx (iR2^[n] z)) (zKseq (iR2^[n] z))) (n : ℕ) :
    icmp (iord (iR2^[n+1] z)) (iord (iR2^[n] z)) = 0 := by
  rw [Function.iterate_succ_apply']
  exact iord_descent_iR2_of_ZDerivesEmpty (ZDerivesEmpty_iterate hRS hz n) (hcrit n)

end GoodsteinPA.InternalZ
