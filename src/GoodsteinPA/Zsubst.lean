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

end GoodsteinPA.InternalZ
