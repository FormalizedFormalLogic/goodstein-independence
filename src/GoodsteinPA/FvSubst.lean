/-
# `FvSubst.lean` — free-variable substitution on coded terms/formulas (the `zsubst` substrate)

The genuine internalized cut-elimination reduct (`RedSound`, crux-2's last wall) needs
**eigenvariable substitution on Z-derivations**: replace a free variable `^&a` throughout a
derivation by a numeral `n`. Foundation's `subst`/`substs1` substitute the *bound* variables
`^#i` only (`termSubst_fvar : termSubst L w ^&x = ^&x` is the identity on free vars), so they
cannot realize `^&a ↦ t`. This file builds the missing operation from scratch, mirroring
Foundation's `TermSubst`/`TermShift`/`Substs` `Language.TermRec`/`UformulaRec1` recursions:

* `termFvSubst a t u` — replace `^&a` by term `t` in coded term `u` (identity on `^&x`, `x ≠ a`).
* `fvSubst a t p`     — the same on a coded formula `p` (rewrites the atom term-vectors).

Both are `𝚺₁`-definable and preserve `IsSemiterm`/`IsSemiformula`. The derivation-level
`zsubst` (rung 1 of the lap-70 ladder) recurses these over a Z-derivation tree.
-/
module

public import Foundation.FirstOrder.Incompleteness.Second

@[expose] public section

namespace LO.FirstOrder.Arithmetic.Bootstrapping

variable {V : Type*} [ORingStructure V] [V ⊧ₘ* 𝗜𝚺₁]

section

variable {L : Language} [L.Encodable] [L.LORDefinable]

/-! ## Term-level free-variable substitution `^&a ↦ t` -/

namespace TermFvSubst

/-- Recursion blueprint: params `a` (free-var index, `param 0`) and `t` (replacement, `param 1`). -/
def blueprint : Language.TermRec.Blueprint 2 where
  bvar := .mkSigma “y z p₀ p₁. !qqBvarDef y z”
  fvar := .mkSigma “y x p₀ p₁. (x = p₀ → y = p₁) ∧ (x ≠ p₀ → !qqFvarDef y x)”
  func := .mkSigma “y k f v v' p₀ p₁. !qqFuncDef y k f v'”

noncomputable def construction : Language.TermRec.Construction V blueprint where
  bvar (_     z)        := ^#z
  fvar (param x)        := if x = param 0 then param 1 else ^&x
  func (_     k f _ v') := ^func k f v'
  bvar_defined := .mk fun v ↦ by simp [blueprint]
  fvar_defined := .mk fun v ↦ by
    simp [blueprint]
    by_cases h : v 1 = v 2 <;> simp [h]
  func_defined := .mk fun v ↦ by simp [blueprint]

end TermFvSubst

section termFvSubst

open TermFvSubst

variable (L)

/-- Replace the free variable `^&a` by the coded term `t` throughout the coded term `u`. -/
noncomputable def termFvSubst (a t u : V) : V := construction.result L ![a, t] u

/-- The same on a coded term-vector. -/
noncomputable def termFvSubstVec (a t k v : V) : V := construction.resultVec L ![a, t] k v

noncomputable def termFvSubstGraph : 𝚺₁.Semisentence 4 :=
  (blueprint.result L).rew <| Rew.subst ![#0, #3, #1, #2]

noncomputable def termFvSubstVecGraph : 𝚺₁.Semisentence 5 :=
  (blueprint.resultVec L).rew <| Rew.subst ![#0, #3, #4, #1, #2]

variable {L}

variable {a t k w : V}

@[simp] lemma termFvSubst_bvar (z) : termFvSubst L a t ^#z = ^#z := by
  simp [termFvSubst, construction]

@[simp] lemma termFvSubst_fvar_self : termFvSubst L a t ^&a = t := by
  simp [termFvSubst, construction]

@[simp] lemma termFvSubst_fvar_ne {x} (h : x ≠ a) : termFvSubst L a t ^&x = ^&x := by
  simp [termFvSubst, construction, h]

@[simp] lemma termFvSubst_func {kk f v} (hkf : L.IsFunc kk f) (hv : IsUTermVec L kk v) :
    termFvSubst L a t (^func kk f v) = ^func kk f (termFvSubstVec L a t kk v) := by
  simp [termFvSubst, termFvSubstVec, construction, hkf, hv]

section

instance termFvSubst.defined : 𝚺₁-Function₃ termFvSubst (V := V) L via termFvSubstGraph L := .mk fun v ↦ by
  simpa [termFvSubstGraph, termFvSubst, Matrix.constant_eq_singleton, Matrix.comp_vecCons']
    using construction.result_defined.defined ![v 0, v 3, v 1, v 2]

instance termFvSubst.definable : 𝚺₁-Function₃ termFvSubst (V := V) L := termFvSubst.defined.to_definable

instance termFvSubst.definable' : Γ-[i + 1]-Function₃ termFvSubst (V := V) L :=
  termFvSubst.definable.of_sigmaOne

instance termFvSubstVec.defined : 𝚺₁-Function₄ termFvSubstVec (V := V) L via termFvSubstVecGraph L := .mk fun v ↦ by
  simpa [termFvSubstVecGraph, termFvSubstVec, Matrix.constant_eq_singleton, Matrix.comp_vecCons']
    using construction.resultVec_defined.defined ![v 0, v 3, v 4, v 1, v 2]

instance termFvSubstVec.definable : 𝚺₁-Function₄ termFvSubstVec (V := V) L := termFvSubstVec.defined.to_definable

instance termFvSubstVec.definable' : Γ-[i + 1]-Function₄ termFvSubstVec (V := V) L :=
  termFvSubstVec.definable.of_sigmaOne

end

@[simp] lemma len_termFvSubstVec {kk ts : V} (hts : IsUTermVec L kk ts) :
    len (termFvSubstVec L a t kk ts) = kk := construction.resultVec_lh L _ hts

@[simp] lemma nth_termFvSubstVec {kk ts i : V} (hts : IsUTermVec L kk ts) (hi : i < kk) :
    (termFvSubstVec L a t kk ts).[i] = termFvSubst L a t ts.[i] :=
  construction.nth_resultVec L _ hts hi

@[simp] lemma termFvSubstVec_nil (a t : V) : termFvSubstVec L a t 0 0 = 0 :=
  construction.resultVec_nil L _

lemma termFvSubstVec_cons {kk u us : V} (hu : IsUTerm L u) (hus : IsUTermVec L kk us) :
    termFvSubstVec L a t (kk + 1) (u ∷ us) = termFvSubst L a t u ∷ termFvSubstVec L a t kk us :=
  construction.resultVec_cons L ![a, t] hus hu

@[simp] lemma IsSemitermVec.termFvSubst {n u} (ht : IsSemiterm L n t) (hu : IsSemiterm L n u) :
    IsSemiterm L n (termFvSubst L a t u) := by
  apply IsSemiterm.induction 𝚺 ?_ ?_ ?_ ?_ u hu
  · definability
  · intro z hz; simpa using hz
  · intro x; by_cases h : x = a <;> simp [h, ht]
  · intro kk f v hkf hv ih
    simp only [hkf, hv.isUTerm, termFvSubst_func, IsSemiterm.func, true_and]
    exact IsSemitermVec.iff.mpr
      ⟨by simp [hv.isUTerm], fun i hi ↦ by rw [nth_termFvSubstVec hv.isUTerm hi]; exact ih i hi⟩

@[simp] lemma IsSemitermVec.termFvSubstVec {kk n v} (ht : IsSemiterm L n t) (hv : IsSemitermVec L kk n v) :
    IsSemitermVec L kk n (termFvSubstVec L a t kk v) := IsSemitermVec.iff.mpr
  ⟨by simp [hv.isUTerm], fun i hi ↦ by
    rw [nth_termFvSubstVec hv.isUTerm hi]; exact IsSemitermVec.termFvSubst ht (hv.nth hi)⟩

end termFvSubst

end

end LO.FirstOrder.Arithmetic.Bootstrapping
