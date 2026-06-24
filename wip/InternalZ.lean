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

/-! ## `irk` — formula rank (STUB)

Buchholz's `dg` uses `r := rk(F)` (logical complexity of the induction formula) in the `Ind`/`K^r`
cases. A faithful `rk` is a course-of-values recursion on Foundation's coded formulas (qqAnd/qqAll/…),
its own brick. **STUB this lap:** `irk d := 0` — a genuine total `𝚺₀` function (NOT an axiom), placed
in `wip/` off the build, to be replaced by the real rank. The degree it produces is therefore a
lower bound on the faithful degree; correct enough to wire `idg`'s skeleton, flagged for replacement
(`PENDING_WORK.md`). -/
noncomputable def irk (_d : V) : V := 0

def _root_.LO.FirstOrder.Arithmetic.irkDef : 𝚺₀.Semisentence 2 := .mkSigma “y d. y = 0”
instance irk_defined : 𝚺₀-Function₁ (irk : V → V) via irkDef := .mk fun v ↦ by simp [irkDef, irk]
instance irk_definable : 𝚺₀-Function₁ (irk : V → V) := irk_defined.to_definable
instance irk_definable' (Γ) : Γ-Function₁ (irk : V → V) := irk_definable.of_zero

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

def _root_.LO.FirstOrder.Arithmetic.idgNextDef : 𝚺₁.Semisentence 3 := .mkSigma
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
def idgTable.blueprint : PR.Blueprint 0 where
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

def _root_.LO.FirstOrder.Arithmetic.idgTableDef : 𝚺₁.Semisentence 2 :=
  idgTable.blueprint.resultDef.rew (Rew.subst ![#0, #1])

instance idgTable_defined : 𝚺₁-Function₁ (idgTable : V → V) via idgTableDef := .mk
  fun v ↦ by simp [idgTable.construction.result_defined_iff, idgTableDef]; rfl

instance idgTable_definable : 𝚺₁-Function₁ (idgTable : V → V) := idgTable_defined.to_definable
instance idgTable_definable' (Γ) : Γ-[m + 1]-Function₁ (idgTable : V → V) :=
  idgTable_definable.of_sigmaOne

def _root_.LO.FirstOrder.Arithmetic.idgDef : 𝚺₁.Semisentence 2 := .mkSigma
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

/-! ### `idg`-fold over a premise sequence (for the variadic `K^r` equation)

`iseqMaxIdg ds = max_{i < lh ds} idg(znth ds i)` — the genuine idg-fold (applies `idg` directly,
independent of any value-table). The `K^r` step in `idgNext` reads the *table* form
`iseqMaxTab (idgTable M) ds`; when `M` dominates every entry (which holds for `M = zK… - 1`), the two
agree by table stability. This yields the clean `idg_zK` equation. -/

def iseqMaxIdgAux.blueprint : PR.Blueprint 1 where
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

def _root_.LO.FirstOrder.Arithmetic.iseqMaxIdgAuxDef : 𝚺₁.Semisentence 3 :=
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

/-- Table step of `iotil`: dispatch on `zTag d`, reading sub-õ-values out of the table `s`. -/
noncomputable def ioNext (d s : V) : V :=
  if zTag d = 1 then iadd (znth s (zIallPrem d)) (ocOadd 0 1 0)
  else if zTag d = 2 then iadd (znth s (zInegPrem d)) (ocOadd 0 1 0)
  else if zTag d = 3 then
    inadd (ocOadd (znth s (zIndPrem0 d)) 1 0)
      (ocOadd (iadd (znth s (zIndPrem1 d)) (ocOadd 0 1 0)) 1 0)
  else if zTag d = 4 then iseqNaddTab s (zKseq d)
  else 0

def _root_.LO.FirstOrder.Arithmetic.ioNextDef : 𝚺₁.Semisentence 3 := .mkSigma
  “y d s. ∃ t, !zTagDef t d ∧ ∃ one, !ocOaddDef one 0 1 0 ∧
    ( (t = 1 ∧ ∃ p, !zIallPremDef p d ∧ ∃ v, !znthDef v s p ∧ !iaddDef y v one)
    ∨ (t = 2 ∧ ∃ p, !zInegPremDef p d ∧ ∃ v, !znthDef v s p ∧ !iaddDef y v one)
    ∨ (t = 3 ∧ ∃ p0, !zIndPrem0Def p0 d ∧ ∃ v0, !znthDef v0 s p0 ∧ ∃ w0, !ocOaddDef w0 v0 1 0 ∧
        ∃ p1, !zIndPrem1Def p1 d ∧ ∃ v1, !znthDef v1 s p1 ∧ ∃ v1s, !iaddDef v1s v1 one ∧
        ∃ w1, !ocOaddDef w1 v1s 1 0 ∧ !inaddDef y w0 w1)
    ∨ (t = 4 ∧ ∃ ds, !zKseqDef ds d ∧ !iseqNaddTabDef y s ds)
    ∨ (t ≠ 1 ∧ t ≠ 2 ∧ t ≠ 3 ∧ t ≠ 4 ∧ y = 0) )”

set_option maxHeartbeats 1000000 in
instance ioNext_defined : 𝚺₁-Function₂ (ioNext : V → V → V) via ioNextDef := .mk fun v ↦ by
  simp [ioNextDef, ioNext, zTag_defined.iff, zIallPrem_defined.iff, zInegPrem_defined.iff,
    zIndPrem0_defined.iff, zIndPrem1_defined.iff, zKseq_defined.iff, iadd_defined.iff,
    inadd_defined.iff, ocOadd_defined.iff, iseqNaddTab_defined.iff, znth_defined.iff]
  by_cases h1 : zTag (v 1) = 1
  · simp [h1]
  · by_cases h2 : zTag (v 1) = 2
    · simp [h1, h2]
    · by_cases h3 : zTag (v 1) = 3
      · simp [h1, h2, h3]
      · by_cases h4 : zTag (v 1) = 4
        · simp [h1, h2, h3, h4]
        · simp [h1, h2, h3, h4]

instance ioNext_definable : 𝚺₁-Function₂ (ioNext : V → V → V) := ioNext_defined.to_definable

def ioTable.blueprint : PR.Blueprint 0 where
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

def _root_.LO.FirstOrder.Arithmetic.ioTableDef : 𝚺₁.Semisentence 2 :=
  ioTable.blueprint.resultDef.rew (Rew.subst ![#0, #1])

instance ioTable_defined : 𝚺₁-Function₁ (ioTable : V → V) via ioTableDef := .mk
  fun v ↦ by simp [ioTable.construction.result_defined_iff, ioTableDef]; rfl

instance ioTable_definable : 𝚺₁-Function₁ (ioTable : V → V) := ioTable_defined.to_definable
instance ioTable_definable' (Γ) : Γ-[m + 1]-Function₁ (ioTable : V → V) :=
  ioTable_definable.of_sigmaOne

def _root_.LO.FirstOrder.Arithmetic.iotilDef : 𝚺₁.Semisentence 2 := .mkSigma
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

/-! ### iõ-fold over a premise sequence (for the variadic `K^r` equation), mirror `iseqMaxIdg` -/

def iseqNaddIdgAux.blueprint : PR.Blueprint 1 where
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

def _root_.LO.FirstOrder.Arithmetic.iseqNaddIdgAuxDef : 𝚺₁.Semisentence 3 :=
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

def _root_.LO.FirstOrder.Arithmetic.iordDef : 𝚺₁.Semisentence 2 := .mkSigma
  “y d. ∃ a, !iotilDef a d ∧ ∃ g, !idgDef g d ∧ !iotowerDef y a g”

instance iord_defined : 𝚺₁-Function₁ (iord : V → V) via iordDef := .mk fun v ↦ by
  simp [iordDef, iord, iotil_defined.iff, idg_defined.iff, iotower_defined.iff]

instance iord_definable : 𝚺₁-Function₁ (iord : V → V) := iord_defined.to_definable
instance iord_definable' (Γ) : Γ-[m + 1]-Function₁ (iord : V → V) := iord_definable.of_sigmaOne

/-- `o(d) = ω_{dg(d)}(õ(d))` — unfolds the assignment to the tower over the pre-ordinal. -/
lemma iord_eq (d : V) : iord d = iotower (iotil d) (idg d) := rfl

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

@[simp] lemma isNF_iotil_zAtom (s : V) : isNF (iotil (zAtom s)) := by
  rw [iotil_zAtom]; exact isNF_zero

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
  (∃ s, d = zAtom s) ∨
  (∃ s a p d0, d = zIall s a p d0 ∧ d0 ∈ C) ∨
  (∃ s p d0, d = zIneg s p d0 ∧ d0 ∈ C) ∨
  (∃ s at' p d0 d1, d = zInd s at' p d0 d1 ∧ d0 ∈ C ∧ d1 ∈ C) ∨
  (∃ s r ds, d = zK s r ds ∧ Seq ds ∧ ∀ i < lh ds, znth ds i ∈ C)

/-- `ZPhi` is monotone in the premise set `C` (a `Fixpoint.Construction.monotone` field). -/
lemma zphi_monotone {C C' : Set V} (h : C ⊆ C') {d : V} : ZPhi C d → ZPhi C' d := by
  rintro (hd | ⟨s, a, p, d0, rfl, hd⟩ | ⟨s, p, d0, rfl, hd⟩ |
    ⟨s, at', p, d0, d1, rfl, h0, h1⟩ | ⟨s, r, ds, rfl, hseq, hall⟩)
  · exact Or.inl hd
  · exact Or.inr (Or.inl ⟨s, a, p, d0, rfl, h hd⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨s, p, d0, rfl, h hd⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨s, at', p, d0, d1, rfl, h h0, h h1⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨s, r, ds, rfl, hseq, fun i hi => h (hall i hi)⟩)))

/-- `ZPhi` is strongly finite: every premise of `d` is `< d`, so the rule fires already over
`{y ∈ C | y < d}` (a `Fixpoint.Construction.StrongFinite` field). The K^r case uses
`Seq.znth` + `lt_of_mem_rng` (`znth ds i < ds`) then `ds < zK s r ds`. -/
lemma zphi_strong_finite {C : Set V} {d : V} :
    ZPhi C d → ZPhi {y | y ∈ C ∧ y < d} d := by
  rintro (hd | ⟨s, a, p, d0, rfl, hd⟩ | ⟨s, p, d0, rfl, hd⟩ |
    ⟨s, at', p, d0, d1, rfl, h0, h1⟩ | ⟨s, r, ds, rfl, hseq, hall⟩)
  · exact Or.inl hd
  · exact Or.inr (Or.inl ⟨s, a, p, d0, rfl, hd, by simp⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨s, p, d0, rfl, hd, by simp⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨s, at', p, d0, d1, rfl, ⟨h0, by simp⟩, ⟨h1, by simp⟩⟩)))
  · refine Or.inr (Or.inr (Or.inr (Or.inr ⟨s, r, ds, rfl, hseq, fun i hi => ⟨hall i hi, ?_⟩⟩)))
    exact lt_trans (lt_of_mem_rng (hseq.znth hi)) (ds_lt_zK s r ds)

/-- Bounded-quantifier form of `ZPhi` (every existential is `< d`), the shape the arithmetized
`blueprint` core matches. Mirrors Foundation `Theory.Derivation.phi_iff`. -/
private lemma zphi_iff (C d : V) :
    ZPhi {x | x ∈ C} d ↔
    ( (∃ s < d, d = zAtom s) ∨
      (∃ s < d, ∃ a < d, ∃ p < d, ∃ d0 < d, d = zIall s a p d0 ∧ d0 ∈ C) ∨
      (∃ s < d, ∃ p < d, ∃ d0 < d, d = zIneg s p d0 ∧ d0 ∈ C) ∨
      (∃ s < d, ∃ at' < d, ∃ p < d, ∃ d0 < d, ∃ d1 < d,
        d = zInd s at' p d0 d1 ∧ d0 ∈ C ∧ d1 ∈ C) ∨
      (∃ s < d, ∃ r < d, ∃ ds < d, d = zK s r ds ∧ Seq ds ∧ ∀ i < lh ds, znth ds i ∈ C) ) := by
  constructor
  · rintro (⟨s, rfl⟩ | ⟨s, a, p, d0, rfl, h⟩ | ⟨s, p, d0, rfl, h⟩ |
      ⟨s, at', p, d0, d1, rfl, h0, h1⟩ | ⟨s, r, ds, rfl, hseq, hall⟩)
    · exact Or.inl ⟨s, by simp, rfl⟩
    · exact Or.inr (Or.inl ⟨s, by simp, a, by simp, p, by simp, d0, by simp, rfl, h⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨s, by simp, p, by simp, d0, by simp, rfl, h⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl
        ⟨s, by simp, at', by simp, p, by simp, d0, by simp, d1, by simp, rfl, h0, h1⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨s, by simp, r, by simp, ds, by simp, rfl, hseq, hall⟩)))
  · rintro (⟨s, _, rfl⟩ | ⟨s, _, a, _, p, _, d0, _, rfl, h⟩ | ⟨s, _, p, _, d0, _, rfl, h⟩ |
      ⟨s, _, at', _, p, _, d0, _, d1, _, rfl, h0, h1⟩ | ⟨s, _, r, _, ds, _, rfl, hseq, hall⟩)
    · exact Or.inl ⟨s, rfl⟩
    · exact Or.inr (Or.inl ⟨s, a, p, d0, rfl, h⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨s, p, d0, rfl, h⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨s, at', p, d0, d1, rfl, h0, h1⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨s, r, ds, rfl, hseq, hall⟩)))

open LO.FirstOrder.Arithmetic in
/-- Arithmetized `𝚫₁` core for the Z-derivation `Fixpoint` (mirrors Foundation
`Theory.Derivation.blueprint`). `d` = candidate code, `C` = the recursion set (premises so far). The
K^r disjunct uses `seqDef`/`lhDef`/`znthDef` for the variadic premise-sequence membership. -/
noncomputable def zblueprint : Fixpoint.Blueprint 0 := ⟨.mkDelta
  (.mkSigma “d C.
    ( (∃ s < d, !zAtomGraph d s) ∨
      (∃ s < d, ∃ a < d, ∃ p < d, ∃ d0 < d, !zIallGraph d s a p d0 ∧ d0 ∈ C) ∨
      (∃ s < d, ∃ p < d, ∃ d0 < d, !zInegGraph d s p d0 ∧ d0 ∈ C) ∨
      (∃ s < d, ∃ at' < d, ∃ p < d, ∃ d0 < d, ∃ d1 < d,
        !zIndGraph d s at' p d0 d1 ∧ d0 ∈ C ∧ d1 ∈ C) ∨
      (∃ s < d, ∃ r < d, ∃ ds < d,
        !zKGraph d s r ds ∧ !seqDef ds ∧
          ∃ l, !lhDef l ds ∧ ∀ i < l, ∃ z, !znthDef z ds i ∧ z ∈ C) )”)
  (.mkPi “d C.
    ( (∃ s < d, !zAtomGraph d s) ∨
      (∃ s < d, ∃ a < d, ∃ p < d, ∃ d0 < d, !zIallGraph d s a p d0 ∧ d0 ∈ C) ∨
      (∃ s < d, ∃ p < d, ∃ d0 < d, !zInegGraph d s p d0 ∧ d0 ∈ C) ∨
      (∃ s < d, ∃ at' < d, ∃ p < d, ∃ d0 < d, ∃ d1 < d,
        !zIndGraph d s at' p d0 d1 ∧ d0 ∈ C ∧ d1 ∈ C) ∨
      (∃ s < d, ∃ r < d, ∃ ds < d,
        !zKGraph d s r ds ∧ !seqDef ds ∧
          ∀ l, !lhDef l ds → ∀ i < l, ∀ z, !znthDef z ds i → z ∈ C) )”)⟩

lemma zPhi_definable :
    𝚫₁.Defined (fun v : Fin 2 → V ↦ ZPhi {x | x ∈ v 1} (v 0)) zblueprint.core := .mk <| by
  constructor
  · intro v; simp [zblueprint]
  · intro v; simp [zphi_iff, zblueprint, zAtom_defined.iff, zIall_defined.iff, zIneg_defined.iff,
      zInd_defined.iff, zK_defined.iff, seq_defined.iff, lh_defined.iff, znth_defined.iff]

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

/-- **Recursion equation** for `ZDerivation` (the `Fixpoint.Construction.case`): a code is a
Z-derivation iff `ZPhi` holds of it over the set of Z-derivations. -/
lemma zDerivation_iff {d : V} : ZDerivation d ↔ ZPhi {z | ZDerivation z} d :=
  (zconstruction (V := V)).case

/-- **Structural induction** over `ZDerivation` (the `Fixpoint.Construction.induction`). -/
lemma zDerivation_induction {P : V → Prop} (hP : 𝚫₁-Predicate P)
    (H : ∀ C : Set V, (∀ x ∈ C, ZDerivation x ∧ P x) → ∀ d, ZPhi C d → P d) :
    ∀ d, ZDerivation d → P d :=
  (zconstruction (V := V)).induction (Γ := 𝚺) hP.of_deltaOne H

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
    rcases hphi with ⟨s, rfl⟩ | ⟨s, a, p, d0, rfl, _⟩ | ⟨s, p, d0, rfl, _⟩ |
      ⟨s, at', p, d0, d1, rfl, _, _⟩ | ⟨s, r, ds, rfl, _, _⟩
    · rintro (h | h) <;> simp at h
    · rintro _; exact iord_descent_iR_zIall s a p d0
    · rintro _; exact iord_descent_iR_zIneg s p d0
    · rintro (h | h) <;> simp at h
    · rintro (h | h) <;> simp at h

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

end GoodsteinPA.InternalZ
