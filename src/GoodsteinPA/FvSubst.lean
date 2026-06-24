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

/-- Bound-variable-depth weakening: a semiterm in context `n` is a semiterm in any wider context. -/
lemma isSemiterm_weaken {n m u : V} (h : IsSemiterm L n u) (hnm : n ≤ m) : IsSemiterm L m u :=
  IsSemiterm.def.mpr ⟨(IsSemiterm.def.mp h).1, le_trans (IsSemiterm.def.mp h).2 hnm⟩

/-- **`termFvSubst` preserves `IsUTerm`** (for an `IsUTerm` replacement `t`). The `IsUTerm` analog of
`IsSemitermVec.termFvSubst`, needed for the constructor-commutation lemmas (`fvSubst_neg`) that work at
the `IsUFormula`/`IsUTerm` level. -/
lemma IsUTerm.termFvSubst (ht : IsUTerm L t) {u} (hu : IsUTerm L u) :
    IsUTerm L (termFvSubst L a t u) := by
  apply IsUTerm.induction 𝚺 ?_ ?_ ?_ ?_ u hu
  · definability
  · intro z; simp
  · intro x; by_cases h : x = a <;> simp [h, ht]
  · intro k f v hkf hv ih
    rw [termFvSubst_func hkf hv]
    refine IsUTerm.mk (Or.inr (Or.inr ⟨k, f, _, hkf, ⟨(len_termFvSubstVec hv).symm, ?_⟩, rfl⟩))
    intro i hi; rw [nth_termFvSubstVec hv hi]; exact ih i hi

/-- **`termFvSubstVec` preserves `IsUTermVec`** (for an `IsUTerm` replacement `t`). -/
lemma IsUTermVec.termFvSubst (ht : IsUTerm L t) {kk v} (hv : IsUTermVec L kk v) :
    IsUTermVec L kk (termFvSubstVec L a t kk v) :=
  ⟨(len_termFvSubstVec hv).symm, fun i hi ↦ by
    rw [nth_termFvSubstVec hv hi]; exact IsUTerm.termFvSubst ht (hv.2 i hi)⟩

/-- **Term-level substitution lemma**: free-variable substitution `^&a ↦ t` (closed `t`) commutes with
bound-variable substitution `termSubst w`. The bound-var substitution image of the renamed vector
`termFvSubstVec a t n w` is applied to the renamed term. The freshness/closedness enters in the `fvar`
case: substituting `^&a ↦ t` on a free var `x = a` yields the closed `t`, which `termSubst` then leaves
fixed (`termSubst_eq_self`, valid because `t` is closed). -/
lemma termFvSubst_termSubst (ht : IsSemiterm L 0 t) {n m w u : V}
    (hw : IsSemitermVec L n m w) (hu : IsSemiterm L n u) :
    termFvSubst L a t (termSubst L w u) =
      termSubst L (termFvSubstVec L a t n w) (termFvSubst L a t u) := by
  apply IsSemiterm.induction 𝚺 ?_ ?_ ?_ ?_ u hu
  · definability
  · intro z hz
    rw [termSubst_bvar, termFvSubst_bvar, termSubst_bvar, nth_termFvSubstVec hw.isUTerm hz]
  · intro x
    rw [termSubst_fvar]
    by_cases h : x = a
    · subst h
      rw [termFvSubst_fvar_self, termSubst_eq_self (n := 0) ht (by simp)]
    · rw [termFvSubst_fvar_ne h, termSubst_fvar]
  · intro k f ts hf hts ih
    have htsf : IsSemitermVec L k n (termFvSubstVec L a t k ts) :=
      IsSemitermVec.termFvSubstVec (isSemiterm_weaken ht (by simp)) hts
    rw [termSubst_func hf hts.isUTerm,
      termFvSubst_func hf (hw.termSubstVec hts).isUTerm,
      termFvSubst_func hf hts.isUTerm,
      termSubst_func hf htsf.isUTerm]
    simp only [qqFunc_inj, true_and]
    apply nth_ext' k
      (by rw [len_termFvSubstVec (hw.termSubstVec hts).isUTerm])
      (by rw [len_termSubstVec htsf.isUTerm])
    intro i hi
    rw [nth_termFvSubstVec (hw.termSubstVec hts).isUTerm hi,
      nth_termSubstVec hts.isUTerm hi,
      nth_termSubstVec htsf.isUTerm hi,
      nth_termFvSubstVec hts.isUTerm hi, ih i hi]

/-- A **closed term is fixed by bound-variable shifting** (`termBShift` raises bound vars; a closed term
has none). Needed for the binder case of the formula substitution lemma. -/
lemma termBShift_eq_self_of_closed (ht : IsSemiterm L 0 t) : termBShift L t = t := by
  apply IsSemiterm.induction 𝚺 ?_ ?_ ?_ ?_ t ht
  · definability
  · intro z hz; exact absurd hz (by simp)
  · intro x; simp
  · intro k f v hf hv ih
    rw [termBShift_func hf hv.isUTerm]
    simp only [qqFunc_inj, true_and]
    apply nth_ext' k (by rw [len_termBShiftVec hv.isUTerm]) (by simp [hv.lh])
    intro i hi
    rw [nth_termBShiftVec hv.isUTerm hi, ih i hi]

/-- **`termFvSubst` commutes with bound-variable shift `termBShift`** (closed `t`). The binder-traversal
input to the formula substitution lemma: under a quantifier `subst` applies `qVec` (= `^#0 ∷ bShift`),
and `fvSubst`'s identity-`allChanges` must agree with that shift. -/
lemma termFvSubst_termBShift (ht : IsSemiterm L 0 t) {n u : V} (hu : IsSemiterm L n u) :
    termFvSubst L a t (termBShift L u) = termBShift L (termFvSubst L a t u) := by
  apply IsSemiterm.induction 𝚺 ?_ ?_ ?_ ?_ u hu
  · definability
  · intro z hz; simp
  · intro x
    by_cases h : x = a
    · subst h; simp [termBShift_eq_self_of_closed ht]
    · simp [h]
  · intro k f v hf hv ih
    have hvf : IsSemitermVec L k n (termFvSubstVec L a t k v) :=
      IsSemitermVec.termFvSubstVec (isSemiterm_weaken ht (by simp)) hv
    rw [termBShift_func hf hv.isUTerm,
      termFvSubst_func hf hv.termBShiftVec.isUTerm,
      termFvSubst_func hf hv.isUTerm,
      termBShift_func hf hvf.isUTerm]
    simp only [qqFunc_inj, true_and]
    apply nth_ext' k
      (by rw [len_termFvSubstVec hv.termBShiftVec.isUTerm])
      (by rw [len_termBShiftVec hvf.isUTerm])
    intro i hi
    rw [nth_termFvSubstVec hv.termBShiftVec.isUTerm hi,
      nth_termBShiftVec hv.isUTerm hi,
      nth_termBShiftVec hvf.isUTerm hi,
      nth_termFvSubstVec hv.isUTerm hi, ih i hi]

/-- **`termFvSubstVec` commutes with `qVec`** (closed `t`): the cons of `^#0` survives, and the shifted
tail commutes by `termFvSubst_termBShift`. This is the equation the binder case of the formula
substitution lemma `fvSubst_subst` reduces to. -/
lemma termFvSubstVec_qVec (ht : IsSemiterm L 0 t) {n m w : V} (hw : IsSemitermVec L n m w) :
    termFvSubstVec L a t (n + 1) (qVec L w) = qVec L (termFvSubstVec L a t n w) := by
  have hfw : IsSemitermVec L n m (termFvSubstVec L a t n w) :=
    IsSemitermVec.termFvSubstVec (isSemiterm_weaken ht (by simp)) hw
  have hqw : IsUTermVec L (n + 1) (qVec L w) := hw.qVec.isUTerm
  apply nth_ext' (n + 1)
    (by rw [len_termFvSubstVec hqw])
    (by rw [hfw.qVec.isUTerm.lh])
  intro i hi
  rw [nth_termFvSubstVec hqw hi]
  rcases zero_or_succ i with rfl | ⟨j, rfl⟩
  · simp [qVec]
  · have hj : j < n := by simpa using hi
    simp only [qVec, hw.lh, hfw.lh, nth_adjoin_succ]
    rw [nth_termBShiftVec hw.isUTerm hj, nth_termBShiftVec hfw.isUTerm hj,
      nth_termFvSubstVec hw.isUTerm hj, termFvSubst_termBShift ht (hw.nth hj)]

end termFvSubst

/-! ## Formula-level free-variable substitution `^&a ↦ t`

The recursion parameter bundles the eigenvariable index and the replacement term as a pair
`⟪a, t⟫` (projected by `π₁`/`π₂` inside the atom case). The replacement `t` in our use is always a
*closed* term (a numeral), so going under a quantifier leaves it unchanged — `allChanges`/
`exsChanges` are the identity. (A general `t` would need `termBShift` here; we don't need it.) -/

namespace FvSubst

variable (L)

noncomputable def blueprint : UformulaRec1.Blueprint where
  rel    := .mkSigma “y param k R v.
    ∃ a, !pi₁Def a param ∧ ∃ tt, !pi₂Def tt param ∧
      ∃ v', !(termFvSubstVecGraph L) v' a tt k v ∧ !qqRelDef y k R v'”
  nrel   := .mkSigma “y param k R v.
    ∃ a, !pi₁Def a param ∧ ∃ tt, !pi₂Def tt param ∧
      ∃ v', !(termFvSubstVecGraph L) v' a tt k v ∧ !qqNRelDef y k R v'”
  verum  := .mkSigma “y param. !qqVerumDef y”
  falsum := .mkSigma “y param. !qqFalsumDef y”
  and    := .mkSigma “y param p₁ p₂ y₁ y₂. !qqAndDef y y₁ y₂”
  or     := .mkSigma “y param p₁ p₂ y₁ y₂. !qqOrDef y y₁ y₂”
  all    := .mkSigma “y param p₁ y₁. !qqAllDef y y₁”
  exs    := .mkSigma “y param p₁ y₁. !qqExsDef y y₁”
  allChanges := .mkSigma “param' param. param' = param”
  exsChanges := .mkSigma “param' param. param' = param”

noncomputable def construction : UformulaRec1.Construction V (blueprint L) where
  rel    (param k R v) := ^rel k R (termFvSubstVec L (π₁ param) (π₂ param) k v)
  nrel   (param k R v) := ^nrel k R (termFvSubstVec L (π₁ param) (π₂ param) k v)
  verum  _             := ^⊤
  falsum _             := ^⊥
  and    _ _ _ y₁ y₂   := y₁ ^⋏ y₂
  or     _ _ _ y₁ y₂   := y₁ ^⋎ y₂
  all    _ _ y₁        := ^∀ y₁
  exs    _ _ y₁        := ^∃ y₁
  allChanges param     := param
  exsChanges param     := param
  rel_defined := .mk fun v ↦ by
    simp [blueprint, pi₁_defined.iff, pi₂_defined.iff, termFvSubstVec.defined.iff]
  nrel_defined := .mk fun v ↦ by
    simp [blueprint, pi₁_defined.iff, pi₂_defined.iff, termFvSubstVec.defined.iff]
  verum_defined := .mk fun v ↦ by simp [blueprint]
  falsum_defined := .mk fun v ↦ by simp [blueprint]
  and_defined := .mk fun v ↦ by simp [blueprint]
  or_defined := .mk fun v ↦ by simp [blueprint]
  all_defined := .mk fun v ↦ by simp [blueprint]
  exs_defined := .mk fun v ↦ by simp [blueprint]
  allChanges_defined := .mk fun v ↦ by simp [blueprint]
  exChanges_defined := .mk fun v ↦ by simp [blueprint]

end FvSubst

section fvSubst

open FvSubst

variable (L)

/-- Replace the free variable `^&a` by the coded term `t` throughout the coded formula `p`. -/
noncomputable def fvSubst (a t p : V) : V := (construction L).result L ⟪a, t⟫ p

noncomputable def fvSubstGraph : 𝚺₁.Semisentence 4 := .mkSigma
  “y a t p. ∃ param, !pairDef param a t ∧ !((blueprint L).result L) y param p”

variable {L}

variable {a t : V}

instance fvSubst.defined : 𝚺₁-Function₃[V] (fvSubst L) via fvSubstGraph L := .mk fun v ↦ by
  simp [fvSubstGraph, fvSubst, (construction L).result_defined.iff]

instance fvSubst.definable : 𝚺₁-Function₃[V] (fvSubst L) := fvSubst.defined.to_definable

instance fvSubst.definable' : Γ-[m + 1]-Function₃[V] (fvSubst L) := fvSubst.definable.of_sigmaOne

@[simp] lemma fvSubst_rel {k R v} (hR : L.IsRel k R) (hv : IsUTermVec L k v) :
    fvSubst L a t (^rel k R v) = ^rel k R (termFvSubstVec L a t k v) := by
  simp [fvSubst, construction, hR, hv]

@[simp] lemma fvSubst_nrel {k R v} (hR : L.IsRel k R) (hv : IsUTermVec L k v) :
    fvSubst L a t (^nrel k R v) = ^nrel k R (termFvSubstVec L a t k v) := by
  simp [fvSubst, construction, hR, hv]

@[simp] lemma fvSubst_verum : fvSubst L a t ^⊤ = ^⊤ := by simp [fvSubst, construction]

@[simp] lemma fvSubst_falsum : fvSubst L a t ^⊥ = ^⊥ := by simp [fvSubst, construction]

@[simp] lemma fvSubst_and {p q} (hp : IsUFormula L p) (hq : IsUFormula L q) :
    fvSubst L a t (p ^⋏ q) = fvSubst L a t p ^⋏ fvSubst L a t q := by
  simp [fvSubst, construction, hp, hq]

@[simp] lemma fvSubst_or {p q} (hp : IsUFormula L p) (hq : IsUFormula L q) :
    fvSubst L a t (p ^⋎ q) = fvSubst L a t p ^⋎ fvSubst L a t q := by
  simp [fvSubst, construction, hp, hq]

@[simp] lemma fvSubst_all {p} (hp : IsUFormula L p) :
    fvSubst L a t (^∀ p) = ^∀ (fvSubst L a t p) := by
  simp [fvSubst, construction, hp]

@[simp] lemma fvSubst_ex {p} (hp : IsUFormula L p) :
    fvSubst L a t (^∃ p) = ^∃ (fvSubst L a t p) := by
  simp [fvSubst, construction, hp]

/-- **`fvSubst` preserves `IsSemiformula`** (for a closed replacement `t`). Order-induction over the
formula, mirroring Foundation's `IsSemiformula.subst`; under a quantifier the bound-var context grows
`n → n+1`, harmless since `t` is closed so `IsSemiterm L 0 t` weakens to every level. -/
lemma fvSubst_isSemiformula (ht : IsSemiterm L 0 t) {n p : V} (hp : IsSemiformula L n p) :
    IsSemiformula L n (fvSubst L a t p) := by
  let f : V → V → V := fun _ n ↦ n + 1
  have hf : 𝚺₁-Function₂ f := by definability
  revert hp
  apply bounded_all_sigma1_order_induction hf
    (P := fun p n ↦ IsSemiformula L n p → IsSemiformula L n (fvSubst L a t p)) ?_ ?_ p n
  · definability
  intro p n ih hp
  rcases IsSemiformula.case_iff.mp hp with
    (⟨k, R, v, hR, hv, rfl⟩ | ⟨k, R, v, hR, hv, rfl⟩ | rfl | rfl |
      ⟨p₁, p₂, h₁, h₂, rfl⟩ | ⟨p₁, p₂, h₁, h₂, rfl⟩ | ⟨p₁, h₁, rfl⟩ | ⟨p₁, h₁, rfl⟩)
  · have : IsSemitermVec L k n (termFvSubstVec L a t k v) :=
      IsSemitermVec.termFvSubstVec (isSemiterm_weaken ht (by simp)) hv
    simp [hR, hv.isUTerm, this]
  · have : IsSemitermVec L k n (termFvSubstVec L a t k v) :=
      IsSemitermVec.termFvSubstVec (isSemiterm_weaken ht (by simp)) hv
    simp [hR, hv.isUTerm, this]
  · simp
  · simp
  · have ih₁ : IsSemiformula L n (fvSubst L a t p₁) := ih p₁ (by simp) n (by simp [f]) h₁
    have ih₂ : IsSemiformula L n (fvSubst L a t p₂) := ih p₂ (by simp) n (by simp [f]) h₂
    simp [h₁.isUFormula, h₂.isUFormula, ih₁, ih₂]
  · have ih₁ : IsSemiformula L n (fvSubst L a t p₁) := ih p₁ (by simp) n (by simp [f]) h₁
    have ih₂ : IsSemiformula L n (fvSubst L a t p₂) := ih p₂ (by simp) n (by simp [f]) h₂
    simp [h₁.isUFormula, h₂.isUFormula, ih₁, ih₂]
  · have ih₁ : IsSemiformula L (n + 1) (fvSubst L a t p₁) := ih p₁ (by simp) (n + 1) (by simp [f]) h₁
    simpa [h₁.isUFormula] using ih₁
  · have ih₁ : IsSemiformula L (n + 1) (fvSubst L a t p₁) := ih p₁ (by simp) (n + 1) (by simp [f]) h₁
    simpa [h₁.isUFormula] using ih₁

/-- **`fvSubst` preserves `IsUFormula`** (for an `IsUTerm` replacement `t`). Mirrors `IsUFormula.neg`. -/
lemma IsUFormula.fvSubst (ht : IsUTerm L t) {p} (hp : IsUFormula L p) :
    IsUFormula L (fvSubst L a t p) := by
  apply IsUFormula.ISigma1.sigma1_succ_induction ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ p hp
  · definability
  · intro k r v hr hv; simp [hr, hv, hv.termFvSubst ht]
  · intro k r v hr hv; simp [hr, hv, hv.termFvSubst ht]
  · simp
  · simp
  · intro p q hp hq ihp ihq; simp [hp, hq, ihp, ihq]
  · intro p q hp hq ihp ihq; simp [hp, hq, ihp, ihq]
  · intro p hp ihp; simp [hp, ihp]
  · intro p hp ihp; simp [hp, ihp]

/-- **`fvSubst` commutes with coded negation** (`fvSubst a t (∼p) = ∼(fvSubst a t p)`, for an `IsUTerm`
replacement `t`). Both are `UformulaRec1` structural recursions that touch only the atom term-vectors
(identically on `rel`/`nrel`); the rule needed to transfer the `zIneg` succedent `inegF p` under
substitution. -/
lemma fvSubst_neg (ht : IsUTerm L t) {p} (hp : IsUFormula L p) :
    fvSubst L a t (neg L p) = neg L (fvSubst L a t p) := by
  apply IsUFormula.ISigma1.sigma1_succ_induction ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ p hp
  · definability
  · intro k r v hr hv; simp [hr, hv, hv.termFvSubst ht]
  · intro k r v hr hv; simp [hr, hv, hv.termFvSubst ht]
  · simp
  · simp
  · intro p q hp hq ihp ihq
    simp [hp, hq, hp.neg, hq.neg, IsUFormula.fvSubst ht hp, IsUFormula.fvSubst ht hq, ihp, ihq]
  · intro p q hp hq ihp ihq
    simp [hp, hq, hp.neg, hq.neg, IsUFormula.fvSubst ht hp, IsUFormula.fvSubst ht hq, ihp, ihq]
  · intro p hp ihp; simp [hp, hp.neg, IsUFormula.fvSubst ht hp, ihp]
  · intro p hp ihp; simp [hp, hp.neg, IsUFormula.fvSubst ht hp, ihp]

/-- **Formula-level substitution lemma**: free-variable substitution `^&a ↦ t` (closed `t`) commutes
with bound-variable substitution `subst w`. The renamed vector `termFvSubstVec a t n w` is applied to
the renamed formula. The atom cases reduce to the term-level `termFvSubst_termSubst`; the binder cases
to `termFvSubstVec_qVec`. Proved by `IsSemiformula.pi1_structural_induction`, mirror of `substs_substs`. -/
lemma fvSubst_subst (ht : IsSemiterm L 0 t) {n m w p : V}
    (hp : IsSemiformula L n p) (hw : IsSemitermVec L n m w) :
    fvSubst L a t (subst L w p) = subst L (termFvSubstVec L a t n w) (fvSubst L a t p) := by
  refine IsSemiformula.pi1_structural_induction
    (P := fun n p => ∀ m w, IsSemitermVec L n m w →
      fvSubst L a t (subst L w p) = subst L (termFvSubstVec L a t n w) (fvSubst L a t p))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hp m w hw
  · definability
  · intro n k R v hR hv m w hw
    have hvf : IsSemitermVec L k n (termFvSubstVec L a t k v) :=
      IsSemitermVec.termFvSubstVec (isSemiterm_weaken ht (by simp)) hv
    rw [substs_rel hR hv.isUTerm, fvSubst_rel hR (hw.termSubstVec hv).isUTerm,
      fvSubst_rel hR hv.isUTerm, substs_rel hR hvf.isUTerm]
    simp only [qqRel_inj, true_and]
    apply nth_ext' k
      (by rw [len_termFvSubstVec (hw.termSubstVec hv).isUTerm])
      (by rw [len_termSubstVec hvf.isUTerm])
    intro i hi
    rw [nth_termFvSubstVec (hw.termSubstVec hv).isUTerm hi, nth_termSubstVec hv.isUTerm hi,
      nth_termSubstVec hvf.isUTerm hi, nth_termFvSubstVec hv.isUTerm hi,
      termFvSubst_termSubst ht hw (hv.nth hi)]
  · intro n k R v hR hv m w hw
    have hvf : IsSemitermVec L k n (termFvSubstVec L a t k v) :=
      IsSemitermVec.termFvSubstVec (isSemiterm_weaken ht (by simp)) hv
    rw [substs_nrel hR hv.isUTerm, fvSubst_nrel hR (hw.termSubstVec hv).isUTerm,
      fvSubst_nrel hR hv.isUTerm, substs_nrel hR hvf.isUTerm]
    simp only [qqNRel_inj, true_and]
    apply nth_ext' k
      (by rw [len_termFvSubstVec (hw.termSubstVec hv).isUTerm])
      (by rw [len_termSubstVec hvf.isUTerm])
    intro i hi
    rw [nth_termFvSubstVec (hw.termSubstVec hv).isUTerm hi, nth_termSubstVec hv.isUTerm hi,
      nth_termSubstVec hvf.isUTerm hi, nth_termFvSubstVec hv.isUTerm hi,
      termFvSubst_termSubst ht hw (hv.nth hi)]
  · intro n m w hw; simp
  · intro n m w hw; simp
  · intro n p q hp hq ihp ihq m w hw
    rw [substs_and hp.isUFormula hq.isUFormula,
      fvSubst_and (hp.subst hw).isUFormula (hq.subst hw).isUFormula,
      fvSubst_and hp.isUFormula hq.isUFormula,
      substs_and (IsUFormula.fvSubst ht.isUTerm hp.isUFormula)
        (IsUFormula.fvSubst ht.isUTerm hq.isUFormula),
      ihp m w hw, ihq m w hw]
  · intro n p q hp hq ihp ihq m w hw
    rw [substs_or hp.isUFormula hq.isUFormula,
      fvSubst_or (hp.subst hw).isUFormula (hq.subst hw).isUFormula,
      fvSubst_or hp.isUFormula hq.isUFormula,
      substs_or (IsUFormula.fvSubst ht.isUTerm hp.isUFormula)
        (IsUFormula.fvSubst ht.isUTerm hq.isUFormula),
      ihp m w hw, ihq m w hw]
  · intro n p hp ih m w hw
    rw [substs_all hp.isUFormula, fvSubst_all (hp.subst hw.qVec).isUFormula,
      ih (m + 1) (qVec L w) hw.qVec, fvSubst_all hp.isUFormula,
      substs_all (IsUFormula.fvSubst ht.isUTerm hp.isUFormula),
      termFvSubstVec_qVec ht hw]
  · intro n p hp ih m w hw
    rw [substs_ex hp.isUFormula, fvSubst_ex (hp.subst hw.qVec).isUFormula,
      ih (m + 1) (qVec L w) hw.qVec, fvSubst_ex hp.isUFormula,
      substs_ex (IsUFormula.fvSubst ht.isUTerm hp.isUFormula),
      termFvSubstVec_qVec ht hw]

/-- **`fvSubst` commutes with `substs1` by a fresh free variable** (`a' ≠ a`, closed `t`): the key
freshness-gated rule. The `zIall`/`zInd` premise succedents `substs1 (^&a') p` (eigenvariable `a'`)
transfer under `^&a ↦ t` iff `a` differs from the eigenvariable `a'` — Buchholz's regularity. -/
lemma fvSubst_substs1_fvar (ht : IsSemiterm L 0 t) {a' p : V} (haa : a' ≠ a)
    (hp : IsSemiformula L 1 p) :
    fvSubst L a t (substs1 L ^&a' p) = substs1 L ^&a' (fvSubst L a t p) := by
  have hw : IsSemitermVec L 1 0 (?[^&a'] : V) := IsSemitermVec.singleton.mpr (by simp)
  have hvec : termFvSubstVec L a t 1 (?[^&a'] : V) = ?[^&a'] := by
    rw [show (1 : V) = 0 + 1 from by simp, termFvSubstVec_cons (by simp) (by simp)]
    simp [termFvSubst_fvar_ne haa]
  unfold substs1
  rw [fvSubst_subst ht hp hw, hvec]

end fvSubst

end

end LO.FirstOrder.Arithmetic.Bootstrapping
