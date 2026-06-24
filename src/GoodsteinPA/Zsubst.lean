/-
# `Zsubst.lean` — eigenvariable substitution on Z-derivations (rung 1 of the RedSound ladder)

`zsubst d a t` replaces the free variable `^&a` by a (closed) coded term `t` throughout a
Z-derivation code `d`. It is the foundational brick of the genuine internalized cut-elimination
reduct (`RedSound`, crux-2's last wall): the Buchholz I∀/Ind reducts substitute the eigenvariable
by a numeral throughout the minor premise (`d[n] := d0(a/n)`).

This file builds, bottom-up:
* `fvSubstSeq a t Γ` — map the formula-level `fvSubst a t` over a coded sequence of formulas.
* `fvSubstSeqt a t s` — substitute the whole sequent `s = ⟪Γ, C⟫` (antecedent sequence + succedent).
* `zsubst d a t` — the course-of-values `<`-recursion over the derivation tree (mirrors `iRTable`).

The replacement `t` is always closed (`IsSemiterm ℒₒᵣ 0 t`), so `fvSubst`'s `IsSemiformula`
preservation applies (`fvSubst_isSemiformula`).
-/
import GoodsteinPA.InternalZ
import GoodsteinPA.FvSubst

namespace GoodsteinPA.InternalZ

open Classical
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.HierarchySymbol ISigma1 PeanoMinus
open LO.FirstOrder.Arithmetic.Bootstrapping
open GoodsteinPA.InternalONote

variable {V : Type*} [ORingStructure V] [V ⊧ₘ* 𝗜𝚺₁]

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
    ∨ (tg ≠ 0 ∧ tg ≠ 1 ∧ tg ≠ 2 ∧ tg ≠ 3 ∧ tg ≠ 4 ∧ tg ≠ 5 ∧ tg ≠ 6 ∧ y = d) )”

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
      zAxAll_defined.iff, zAxNegF_defined.iff, zAxNeg_defined.iff]
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
                · simp [h0, h1, h2, h3, h4, h5, h6]

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

/-! ## Structural correctness of the `zsubst` table (mirror `iR2`/`iotil`)

The table read-out + diagonal unfolding + per-constructor recursion equations, proven exactly as the
`iR2`/`iotil` analogs in `InternalZ.lean`. The payoff is `fstIdx_zsubst` and the recursion equations
that `ZDerivation_zsubst` (rung-1 correctness) will consume. -/

private lemma def_zsubstTable {k} (a t : V) (i : Fin k) :
    𝚺-[1].DefinableFunction (fun v : Fin k → V ↦ zsubstTable a t (v i)) :=
  DefinableFunction₃.comp (F := zsubstTable) (DefinableFunction.const a)
    (DefinableFunction.const t) (DefinableFunction.var i)

private lemma def_zsubst {k} (a t : V) (i : Fin k) :
    𝚺-[1].DefinableFunction (fun v : Fin k → V ↦ zsubst (v i) a t) :=
  DefinableFunction₃.comp (F := zsubst) (DefinableFunction.var i)
    (DefinableFunction.const a) (DefinableFunction.const t)

@[simp] lemma zsubstTable_seq (a t n : V) : Seq (zsubstTable a t n) := by
  induction n using ISigma1.sigma1_succ_induction
  · exact Definable.comp₁ (def_zsubstTable a t 0)
  case zero => simp
  case succ n ih => rw [zsubstTable_succ]; exact ih.seqCons _

@[simp] lemma zsubstTable_lh (a t n : V) : lh (zsubstTable a t n) = n + 1 := by
  induction n using ISigma1.sigma1_succ_induction
  · exact Definable.comp₂ (DefinableFunction₁.comp (F := lh) (def_zsubstTable a t 0)) (by definability)
  case zero => simp
  case succ n ih => rw [zsubstTable_succ, Seq.lh_seqCons _ (zsubstTable_seq a t n), ih]

lemma znth_zsubstTable_succ (a t : V) {n k : V} (hk : k < n + 1) :
    znth (zsubstTable a t (n + 1)) k = znth (zsubstTable a t n) k := by
  rw [zsubstTable_succ]
  exact znth_seqCons_of_lt (zsubstTable_seq a t n) _ (by rw [zsubstTable_lh]; exact hk)

lemma znth_zsubstTable_eq_zsubst (a t : V) : ∀ N : V, ∀ k ≤ N, znth (zsubstTable a t N) k = zsubst k a t := by
  intro N
  induction N using ISigma1.sigma1_succ_induction
  · refine Definable.ball_le (by definability) ?_
    exact Definable.comp₂
      (DefinableFunction₂.comp (F := znth) (def_zsubstTable a t 1) (DefinableFunction.var 0))
      (def_zsubst a t 0)
  case zero =>
    intro k hk; rcases (nonpos_iff_eq_zero.mp hk) with rfl; rfl
  case succ N ih =>
    intro k hk
    rcases eq_or_lt_of_le hk with rfl | hlt
    · rfl
    · rw [znth_zsubstTable_succ a t hlt]; exact ih k (le_iff_lt_succ.mpr hlt)

lemma zsubst_eq_zsubstNext (a t : V) {c : V} (hpos : 0 < c) :
    zsubst c a t = zsubstNext c (zsubstTable a t (c - 1)) a t := by
  obtain ⟨M, rfl⟩ : ∃ M, c = M + 1 := ⟨c - 1, (sub_add_self_of_le (pos_iff_one_le.mp hpos)).symm⟩
  have key : znth (zsubstTable a t (M + 1)) (M + 1) = zsubstNext (M + 1) (zsubstTable a t M) a t := by
    rw [zsubstTable_succ]
    have h := znth_seqCons_self (zsubstTable_seq a t M) (zsubstNext (M + 1) (zsubstTable a t M) a t)
    rwa [zsubstTable_lh] at h
  simp only [zsubst, add_tsub_cancel_right, key]

/-! ### `zsubst` recursion equations (per Z-rule) -/

@[simp] lemma zsubst_zAtom (s a t : V) : zsubst (zAtom s) a t = zAtom (fvSubstSeqt a t s) := by
  rw [zsubst_eq_zsubstNext a t (by simp [zAtom]), zsubstNext]; simp [zTag_zAtom]

@[simp] lemma zsubst_zIall (s e p d0 a t : V) :
    zsubst (zIall s e p d0) a t =
      zIall (fvSubstSeqt a t s) e (fvSubst ℒₒᵣ a t p) (zsubst d0 a t) := by
  rw [zsubst_eq_zsubstNext a t (by simp [zIall]), zsubstNext, if_neg (by simp), if_pos (zTag_zIall s e p d0)]
  simp only [fstIdx_zIall, zIallEig_zIall, zIallF_zIall, zIallPrem_zIall]
  rw [znth_zsubstTable_eq_zsubst a t _ d0 (le_pred_of_lt (d0_lt_zIall s e p d0))]

@[simp] lemma zsubst_zIneg (s p d0 a t : V) :
    zsubst (zIneg s p d0) a t = zIneg (fvSubstSeqt a t s) (fvSubst ℒₒᵣ a t p) (zsubst d0 a t) := by
  rw [zsubst_eq_zsubstNext a t (by simp [zIneg]), zsubstNext, if_neg (by simp), if_neg (by simp),
    if_pos (zTag_zIneg s p d0)]
  simp only [fstIdx_zIneg, zInegF_zIneg, zInegPrem_zIneg]
  rw [znth_zsubstTable_eq_zsubst a t _ d0 (le_pred_of_lt (d0_lt_zIneg s p d0))]

@[simp] lemma zsubst_zInd (s e u p d0 d1 a t : V) :
    zsubst (zInd s ⟪e, u⟫ p d0 d1) a t =
      zInd (fvSubstSeqt a t s) ⟪e, termFvSubst ℒₒᵣ a t u⟫ (fvSubst ℒₒᵣ a t p)
        (zsubst d0 a t) (zsubst d1 a t) := by
  rw [zsubst_eq_zsubstNext a t (by simp [zInd]), zsubstNext, if_neg (by simp), if_neg (by simp),
    if_neg (by simp), if_pos (zTag_zInd s _ p d0 d1)]
  simp only [fstIdx_zInd, zIndEig_zInd, zIndTerm_zInd, zIndP_zInd, zIndPrem0_zInd, zIndPrem1_zInd,
    pi₁_pair, pi₂_pair]
  rw [znth_zsubstTable_eq_zsubst a t _ d0 (le_pred_of_lt (d0_lt_zInd s _ p d0 d1)),
    znth_zsubstTable_eq_zsubst a t _ d1 (le_pred_of_lt (d1_lt_zInd s _ p d0 d1))]

@[simp] lemma zsubst_zK (s r ds a t : V) :
    zsubst (zK s r ds) a t = zK (fvSubstSeqt a t s) r (tblMapSeq (zsubstTable a t (zK s r ds - 1)) ds) := by
  rw [zsubst_eq_zsubstNext a t (by simp [zK]), zsubstNext, if_neg (by simp), if_neg (by simp),
    if_neg (by simp), if_neg (by simp), if_pos (zTag_zK s r ds)]
  simp only [fstIdx_zK, zKrank_zK, zKseq_zK]

@[simp] lemma zsubst_zAxAll (s p k a t : V) :
    zsubst (zAxAll s p k) a t = zAxAll (fvSubstSeqt a t s) (fvSubst ℒₒᵣ a t p) k := by
  rw [zsubst_eq_zsubstNext a t (by simp [zAxAll]), zsubstNext, if_neg (by simp), if_neg (by simp),
    if_neg (by simp), if_neg (by simp), if_neg (by simp), if_pos (zTag_zAxAll s p k)]
  simp only [fstIdx_zAxAll, zAxAllF_zAxAll, zAxAllK_zAxAll]

@[simp] lemma zsubst_zAxNeg (s p a t : V) :
    zsubst (zAxNeg s p) a t = zAxNeg (fvSubstSeqt a t s) (fvSubst ℒₒᵣ a t p) := by
  rw [zsubst_eq_zsubstNext a t (by simp [zAxNeg]), zsubstNext, if_neg (by simp), if_neg (by simp),
    if_neg (by simp), if_neg (by simp), if_neg (by simp), if_neg (by simp), if_pos (zTag_zAxNeg s p)]
  simp only [fstIdx_zAxNeg, zAxNegF_zAxNeg]

/-! ### `fstIdx_zsubst` — the end-sequent of the substituted derivation computes (rung-1 step 1)

For any genuine Z-derivation `d`, the reduct's end-sequent is the substituted end-sequent. Proven by
the 7-way `ZDerivation` case split (each constructor's recursion equation + `fstIdx (z* s' …) = s'`). -/

lemma fstIdx_zsubst {d : V} (a t : V) (hZ : ZDerivation d) :
    fstIdx (zsubst d a t) = fvSubstSeqt a t (fstIdx d) := by
  rcases zDerivation_iff.mp hZ with ⟨s, rfl, _⟩ | ⟨s, e, p, d0, rfl, _, _⟩ | ⟨s, p, d0, rfl, _, _⟩ |
    ⟨s, at', p, d0, d1, rfl, _, _⟩ | ⟨s, r, ds, rfl, _, _, _⟩ |
    ⟨s, p, k, rfl, _, _⟩ | ⟨s, p, rfl, _, _⟩
  · rw [zsubst_zAtom, fstIdx_zAtom, fstIdx_zAtom]
  · rw [zsubst_zIall, fstIdx_zIall, fstIdx_zIall]
  · rw [zsubst_zIneg, fstIdx_zIneg, fstIdx_zIneg]
  · rw [show at' = ⟪π₁ at', π₂ at'⟫ from (pair_unpair at').symm, zsubst_zInd, fstIdx_zInd, fstIdx_zInd]
  · rw [zsubst_zK, fstIdx_zK, fstIdx_zK]
  · rw [zsubst_zAxAll, fstIdx_zAxAll, fstIdx_zAxAll]
  · rw [zsubst_zAxNeg, fstIdx_zAxNeg, fstIdx_zAxNeg]

end GoodsteinPA.InternalZ
