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

end GoodsteinPA.InternalZ
