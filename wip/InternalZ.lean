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

namespace GoodsteinPA.InternalZ

open Classical
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.HierarchySymbol ISigma1 PeanoMinus

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

@[simp] lemma seq_lt_zK (s r ds : V) : s < zK s r ds := le_iff_lt_succ.mp <| le_pair_left _ _
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

end GoodsteinPA.InternalZ
