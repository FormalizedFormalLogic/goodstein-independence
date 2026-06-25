/-
# Discharging `PA_delta1Definable` — the second front to the axiom-free headline

**Goal (operator directive, lap 78).** The headline `peano_not_proves_goodstein` must be
`#print axioms`-clean (trust base only). Two blockers: crux 2 (the `RedSound` cut-elimination,
architecture-blocked — see `ANALYSIS-2026-06-24-lap78-criticality-substitution-wall.md`) and
**`PA_delta1Definable`** — Foundation's disclosed `axiom 𝗣𝗔.Δ₁` (`Incompleteness/Examples.lean:17`,
the arithmetization of PA's Δ₁-definability, a standing TODO upstream). Gödel II for `𝗣𝗔`
(`peano_not_proves_consistency`, `Reduction.lean`) routes through it, so the headline carries it.

This file discharges that axiom **without editing the pinned Foundation package**: it rebuilds the
`𝗣𝗔.Δ₁` instance in-repo as a `def`, so `Reduction.lean` can pass it explicitly to
`consistent_unprovable` and drop `PA_delta1Definable` from `#print axioms`.

## Status (lap 78)
- ✅ `paMinusDelta1 : 𝗣𝗔⁻.Δ₁` — **axiom-clean.** `𝗣𝗔⁻` is finite (`PeanoMinus.finite`), so
  `Theory.Δ₁.ofFinite` gives it directly (the `singleton`/`add`/`ofList` combinators enumerate the
  17 axioms + the finite `𝗘𝗤` over `ℒₒᵣ`).
- ⏳ `inductionSchemeUnivDelta1 : (InductionScheme ℒₒᵣ Set.univ).Δ₁` — **the genuine wall** (one
  disclosed `sorry`). The infinite induction scheme has no finite enumeration; it needs an internal
  Δ₁ recognizer for codes of `univCl (succInd φ)`. See the obligation note on that def.
- ✅ `paDelta1 : 𝗣𝗔.Δ₁ := paMinusDelta1.add inductionSchemeUnivDelta1` — the assembly is `rfl`-valid
  (`𝗣𝗔 = 𝗣𝗔⁻ + InductionScheme ℒₒᵣ Set.univ`); ready to rewire `Reduction.lean` once the scheme is
  sorry-free.

ANTI-FRAUD: `paDelta1` carries `sorryAx` until `inductionSchemeUnivDelta1` is real. Do NOT rewire
`Reduction.lean` to `paDelta1` while the `sorry` stands — that would merely swap `PA_delta1Definable`
for `sorryAx` with no honesty gain. Rewire only when the scheme recognizer is machine-checked.
-/
import Foundation.FirstOrder.Incompleteness.Examples

namespace GoodsteinPA

open LO LO.FirstOrder LO.FirstOrder.Arithmetic

/-! ## Brick 1 — the internal `succInd` builder (lap 78, axiom-clean)

`succIndCodeT` mirrors `succInd φ = φ/[0] 🡒 ∀⁰(φ/[#0] 🡒 φ/[#0+1]) 🡒 ∀⁰ φ/[#0]` on Foundation's
typed coded-formula layer (`Bootstrapping.Semiformula`), and `succIndCodeT_quote` proves it commutes
with the quote: `succIndCodeT ⌜φ⌝ = ⌜succInd φ⌝`. This is the first reusable piece of the
induction-axiom recognizer; only the universal-closure wrapper (`univCl`) remains. -/

section SuccIndCode

open LO.FirstOrder.Arithmetic.Bootstrapping
open LO.FirstOrder.Arithmetic.Bootstrapping.Arithmetic

variable {V : Type*} [ORingStructure V] [V ⊧ₘ* 𝗜𝚺₁]

/-- Internal `succInd` builder on the typed coded-formula layer: from a code `p` of a 1-bound-var
formula, build the code of `succInd`'s matrix `p/[0] 🡒 ∀⁰(p/[#0] 🡒 p/[#0+1]) 🡒 ∀⁰ p/[#0]`. -/
noncomputable def succIndCodeT (p : Semiformula V ℒₒᵣ 1) : Formula V ℒₒᵣ :=
  (p.subst ![typedNumeral 0]) 🡒
    ((∀⁰ ((p.subst ![Semiterm.bvar 0]) 🡒
          (p.subst ![(Semiterm.bvar 0 : Semiterm V ℒₒᵣ 1) + typedNumeral 1]))) 🡒
      (∀⁰ (p.subst ![Semiterm.bvar 0])))

/-- **Quote-correctness of the internal `succInd` builder.** `succIndCodeT ⌜φ⌝ = ⌜succInd φ⌝` — the
internal builder applied to a quoted formula computes the quote of the external `succInd φ`. Proved by
unfolding both and discharging via the `typed_quote_*` coding simp set. -/
@[simp] lemma succIndCodeT_quote (φ : Semiformula ℒₒᵣ ℕ 1) :
    succIndCodeT (⌜φ⌝ : Semiformula V ℒₒᵣ 1) = ⌜succInd φ⌝ := by
  unfold succIndCodeT succInd
  simp [Matrix.constant_eq_singleton]

/-- **Raw-V `succInd` builder** (the `𝚺₁`-definable function the recognizer formula needs). In
simp-normal form: the two identity substitutions `p/[#0]` are `= p`. -/
noncomputable def succIndCodeRaw (p : V) : V :=
  imp ℒₒᵣ (substs1 ℒₒᵣ (numeral 0) p)
    (imp ℒₒᵣ
      (qqAll (imp ℒₒᵣ p (substs1 ℒₒᵣ (qqAdd (^#0) (numeral 1)) p)))
      (qqAll p))

/-- The typed builder's underlying code is the raw builder. -/
@[simp] lemma succIndCodeT_val (p : Semiformula V ℒₒᵣ 1) :
    (succIndCodeT p).val = succIndCodeRaw p.val := by
  unfold succIndCodeT succIndCodeRaw; simp [substs1]

/-- **Raw quote-correctness:** `succIndCodeRaw ⌜φ⌝ = ⌜succInd φ⌝` over `V`. -/
@[simp] lemma succIndCodeRaw_quote (φ : Semiformula ℒₒᵣ ℕ 1) :
    succIndCodeRaw (⌜φ⌝ : V) = (⌜succInd φ⌝ : V) := by
  show succIndCodeRaw (⌜φ⌝ : Semiformula V ℒₒᵣ 1).val = (⌜succInd φ⌝ : Semiformula V ℒₒᵣ 0).val
  rw [← succIndCodeT_val, succIndCodeT_quote]

/-- `succIndCodeRaw` is a `𝚺₁` function (composition of the `imp`/`qqAll`/`substs1`/`numeral`/`qqAdd`
defined functions). -/
instance succIndCodeRaw_definable : 𝚺₁-Function₁ (succIndCodeRaw : V → V) := by
  unfold succIndCodeRaw; definability

end SuccIndCode

/-! ## Brick 2a — the internal iterated universal quantifier `qqAllItr` (lap 79)

`qqAllItr p k = ^∀^[k] p` (wrap the code `p` in `k` leading `^∀`s). A primitive recursion
(`PR.Construction`), hence `𝚺₁`. Quote-correctness `qqAllItr ⌜φ⌝ n = ⌜∀⁰* φ⌝` lets the
universal-closure half of `closeAll` commute with the quote. This is the FIRST of the two pieces of
the internal `univCl'`; the second is the free-variable→bound rewrite (`fixitr` analog), still open. -/

section QQAllItr

open LO.FirstOrder.Arithmetic.Bootstrapping
open LO.FirstOrder.Arithmetic.Bootstrapping.Arithmetic

variable {V : Type*} [ORingStructure V] [V ⊧ₘ* 𝗜𝚺₁]

namespace QQAllItr

noncomputable def blueprint : PR.Blueprint 1 where
  zero := .mkSigma “y p. y = p”
  succ := .mkSigma “y ih k p. !qqAllDef y ih”

noncomputable def construction : PR.Construction V blueprint where
  zero param := param 0
  succ _ _ ih := qqAll ih
  zero_defined := .mk fun v ↦ by simp [blueprint]
  succ_defined := .mk fun v ↦ by simp [blueprint]

end QQAllItr

open QQAllItr

/-- Internal iterated universal quantifier: `qqAllItr p k = ^∀^[k] p`. -/
noncomputable def qqAllItr (p k : V) : V := construction.result ![p] k

@[simp] lemma qqAllItr_zero (p : V) : qqAllItr p 0 = p := by simp [qqAllItr, construction]

@[simp] lemma qqAllItr_succ (p k : V) : qqAllItr p (k + 1) = qqAll (qqAllItr p k) := by
  simp [qqAllItr, construction]

noncomputable def qqAllItrGraph : 𝚺₁.Semisentence 3 := blueprint.resultDef |>.rew (Rew.subst ![#0, #2, #1])

instance qqAllItr.defined : 𝚺₁-Function₂[V] qqAllItr via qqAllItrGraph := .mk fun v ↦ by
  simp [construction.result_defined_iff, qqAllItrGraph, qqAllItr, Matrix.comp_vecCons',
    Matrix.constant_eq_singleton]

instance qqAllItr.definable : 𝚺₁-Function₂ (qqAllItr : V → V → V) := qqAllItr.defined.to_definable

instance qqAllItr.definable' : Γ-[m + 1]-Function₂ (qqAllItr : V → V → V) := .of_sigmaOne qqAllItr.definable

/-- `^∀` can be peeled from the front of the iteration: `qqAllItr p (k+1) = qqAllItr (^∀ p) k`. -/
lemma qqAllItr_succ' (p k : V) : qqAllItr p (k + 1) = qqAllItr (qqAll p) k := by
  induction k using ISigma1.sigma1_succ_induction
  · definability
  case zero => rw [qqAllItr_succ, qqAllItr_zero, qqAllItr_zero]
  case succ k ih => rw [qqAllItr_succ, ih, ← qqAllItr_succ]

/-- **Quote-correctness of `qqAllItr`:** the internal `k`-fold `^∀` wrap of a quoted `n`-ary formula
computes the quote of its external universal closure. -/
lemma qqAllItr_quote {n : ℕ} (φ : Semiformula ℒₒᵣ ℕ n) :
    qqAllItr (⌜φ⌝ : V) (n : V) = (⌜(∀⁰* φ : Formula ℒₒᵣ ℕ)⌝ : V) := by
  induction n
  case zero => simp
  case succ n ih =>
    rw [Nat.cast_succ, qqAllItr_succ']
    exact ih (∀⁰ φ)

end QQAllItr

/-! ## Brick 2b — internal free→bound rewrite `freeToBound` (the `Rew.fixitr 0 m` analog, lap 79)

`Rew.fixitr 0 m ▹ φ` (`Basic/Syntax/Rew.lean:639`) sends a free variable `&i` (with `i < m`) occurring
at binder-depth `d` to the bound variable `#(i + d)` and leaves local bound vars in place. We arithmetize
this as `freeToBound d p` (formula) / `termFreeToBound d t` (term): the leaf rewrites every `^&x` to
`^#(x + d)`, and the recursion increments the depth `d ↦ d + 1` under each `^∀`/`^∃`. Both are `𝚺₁`
functions via `TermRec`/`UformulaRec1`, mirroring `termSubst`/`subst`. -/

section FreeToBound

open LO.FirstOrder.Arithmetic.Bootstrapping
open LO.FirstOrder.Arithmetic.Bootstrapping.Arithmetic

variable {V : Type*} [ORingStructure V] [V ⊧ₘ* 𝗜𝚺₁]
variable {L : Language} [L.Encodable] [L.LORDefinable]

namespace TermFreeToBound

def blueprint : Language.TermRec.Blueprint 1 where
  bvar := .mkSigma “y z d. !qqBvarDef y z”
  fvar := .mkSigma “y x d. !qqBvarDef y (x + d)”
  func := .mkSigma “y k f v v' d. !qqFuncDef y k f v'”

noncomputable def construction : Language.TermRec.Construction V blueprint where
  bvar (_ z)        := ^#z
  fvar (param x)    := ^#(x + param 1)
  func (_ k f _ v') := ^func k f v'
  bvar_defined := .mk fun v ↦ by simp [blueprint]
  fvar_defined := .mk fun v ↦ by simp [blueprint]
  func_defined := .mk fun v ↦ by simp [blueprint]

end TermFreeToBound

section

open TermFreeToBound

variable (L)

/-- Internal term free→bound: `termFreeToBound d t` sends `^&x ↦ ^#(x+d)`, fixes `^#z`. -/
noncomputable def termFreeToBound (d t : V) : V := construction.result L ![d] t

noncomputable def termFreeToBoundVec (k d v : V) : V := construction.resultVec L ![d] k v

noncomputable def termFreeToBoundGraph : 𝚺₁.Semisentence 3 :=
  (blueprint.result L).rew <| Rew.subst ![#0, #2, #1]

noncomputable def termFreeToBoundVecGraph : 𝚺₁.Semisentence 4 :=
  (blueprint.resultVec L).rew <| Rew.subst ![#0, #1, #3, #2]

variable {L}

@[simp] lemma termFreeToBound_bvar (d z : V) :
    termFreeToBound L d ^#z = ^#z := by simp [termFreeToBound, construction]

@[simp] lemma termFreeToBound_fvar (d x : V) :
    termFreeToBound L d ^&x = ^#(x + d) := by simp [termFreeToBound, construction]

@[simp] lemma termFreeToBound_func {k f v : V} (hkf : L.IsFunc k f) (hv : IsUTermVec L k v) :
    termFreeToBound L d (^func k f v) = ^func k f (termFreeToBoundVec L k d v) := by
  simp [termFreeToBound, termFreeToBoundVec, construction, hkf, hv]

instance termFreeToBound.defined : 𝚺₁-Function₂ termFreeToBound (V := V) L via termFreeToBoundGraph L :=
  .mk fun v ↦ by
    simpa [termFreeToBoundGraph, termFreeToBound, Matrix.constant_eq_singleton, Matrix.comp_vecCons']
      using construction.result_defined.defined ![v 0, v 2, v 1]

instance termFreeToBound.definable : 𝚺₁-Function₂ termFreeToBound (V := V) L :=
  termFreeToBound.defined.to_definable

instance termFreeToBound.definable' : Γ-[k + 1]-Function₂ termFreeToBound (V := V) L :=
  termFreeToBound.definable.of_sigmaOne

instance termFreeToBoundVec.defined : 𝚺₁-Function₃ termFreeToBoundVec (V := V) L via termFreeToBoundVecGraph L :=
  .mk fun v ↦ by
    simpa [termFreeToBoundVecGraph, termFreeToBoundVec, Matrix.constant_eq_singleton, Matrix.comp_vecCons']
      using construction.resultVec_defined.defined ![v 0, v 1, v 3, v 2]

instance termFreeToBoundVec.definable : 𝚺₁-Function₃ termFreeToBoundVec (V := V) L :=
  termFreeToBoundVec.defined.to_definable

instance termFreeToBoundVec.definable' : Γ-[i + 1]-Function₃ termFreeToBoundVec (V := V) L :=
  termFreeToBoundVec.definable.of_sigmaOne

@[simp] lemma len_termFreeToBoundVec {k ts : V} (hts : IsUTermVec L k ts) :
    len (termFreeToBoundVec L k d ts) = k := construction.resultVec_lh L _ hts

@[simp] lemma nth_termFreeToBoundVec {k ts i : V} (hts : IsUTermVec L k ts) (hi : i < k) :
    (termFreeToBoundVec L k d ts).[i] = termFreeToBound L d ts.[i] :=
  construction.nth_resultVec L _ hts hi

end

/-! ### Formula-level `freeToBound` (lap 79) -/

namespace FreeToBoundF

variable (L)

noncomputable def blueprint : UformulaRec1.Blueprint where
  rel    := .mkSigma “y param k R v. ∃ v', !(termFreeToBoundVecGraph L) v' k param v ∧ !qqRelDef y k R v'”
  nrel   := .mkSigma “y param k R v. ∃ v', !(termFreeToBoundVecGraph L) v' k param v ∧ !qqNRelDef y k R v'”
  verum  := .mkSigma “y param. !qqVerumDef y”
  falsum := .mkSigma “y param. !qqFalsumDef y”
  and    := .mkSigma “y param p₁ p₂ y₁ y₂. !qqAndDef y y₁ y₂”
  or     := .mkSigma “y param p₁ p₂ y₁ y₂. !qqOrDef y y₁ y₂”
  all    := .mkSigma “y param p₁ y₁. !qqAllDef y y₁”
  exs    := .mkSigma “y param p₁ y₁. !qqExsDef y y₁”
  allChanges := .mkSigma “param' param. param' = param + 1”
  exsChanges := .mkSigma “param' param. param' = param + 1”

noncomputable def construction : UformulaRec1.Construction V (blueprint L) where
  rel (param)  := fun k R v ↦ ^rel k R (termFreeToBoundVec L k param v)
  nrel (param) := fun k R v ↦ ^nrel k R (termFreeToBoundVec L k param v)
  verum _      := ^⊤
  falsum _     := ^⊥
  and _        := fun _ _ y₁ y₂ ↦ y₁ ^⋏ y₂
  or _         := fun _ _ y₁ y₂ ↦ y₁ ^⋎ y₂
  all _        := fun _ y₁ ↦ ^∀ y₁
  exs _        := fun _ y₁ ↦ ^∃ y₁
  allChanges (param) := param + 1
  exsChanges (param) := param + 1
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

end FreeToBoundF

section

open FreeToBoundF

variable (L)

/-- Internal formula free→bound: `freeToBound d p` sends each free var `^&x` at binder-depth `δ`
to the bound var `^#(x + d + δ)`, incrementing the depth under each `^∀`/`^∃`. Mirrors
`Rew.fixitr 0 m ▹ ·` (with `d` the running offset, `0` at the top level). -/
noncomputable def freeToBound (d p : V) : V := (construction L).result L d p

noncomputable def freeToBoundGraph : 𝚺₁.Semisentence 3 := (blueprint L).result L

variable {L}

instance freeToBound.defined : 𝚺₁-Function₂[V] freeToBound L via freeToBoundGraph L :=
  (construction L).result_defined

instance freeToBound.definable : 𝚺₁-Function₂[V] freeToBound L := freeToBound.defined.to_definable

instance freeToBound.definable' : Γ-[m + 1]-Function₂[V] freeToBound L := freeToBound.definable.of_sigmaOne

@[simp] lemma freeToBound_rel {k R v : V} (hR : L.IsRel k R) (hv : IsUTermVec L k v) :
    freeToBound L d (^relk R v) = ^rel k R (termFreeToBoundVec L k d v) := by
  simp [freeToBound, hR, hv, construction]

@[simp] lemma freeToBound_nrel {k R v : V} (hR : L.IsRel k R) (hv : IsUTermVec L k v) :
    freeToBound L d (^nrelk R v) = ^nrel k R (termFreeToBoundVec L k d v) := by
  simp [freeToBound, hR, hv, construction]

@[simp] lemma freeToBound_verum (d : V) : freeToBound L d ^⊤ = ^⊤ := by simp [freeToBound, construction]

@[simp] lemma freeToBound_falsum (d : V) : freeToBound L d ^⊥ = ^⊥ := by simp [freeToBound, construction]

@[simp] lemma freeToBound_and {p q : V} (hp : IsUFormula L p) (hq : IsUFormula L q) :
    freeToBound L d (p ^⋏ q) = freeToBound L d p ^⋏ freeToBound L d q := by
  simp [freeToBound, hp, hq, construction]

@[simp] lemma freeToBound_or {p q : V} (hp : IsUFormula L p) (hq : IsUFormula L q) :
    freeToBound L d (p ^⋎ q) = freeToBound L d p ^⋎ freeToBound L d q := by
  simp [freeToBound, hp, hq, construction]

@[simp] lemma freeToBound_all {p : V} (hp : IsUFormula L p) :
    freeToBound L d (^∀ p) = ^∀ (freeToBound L (d + 1) p) := by simp [freeToBound, hp, construction]

@[simp] lemma freeToBound_exs {p : V} (hp : IsUFormula L p) :
    freeToBound L d (^∃ p) = ^∃ (freeToBound L (d + 1) p) := by simp [freeToBound, hp, construction]

end

end FreeToBound

/-! ## Brick 2c — internal free-variable sequence `fvarSeq` (lap 79)

`fvarSeq m = ⟨^&0, ^&1, …, ^&(m-1)⟩` — the substitution vector that, fed to `subst`, sends bound
`#i ↦ ^&i` (undoing `fixitr`). Built exactly like `qVec` (`Term/Functions.lean §qVec`) but with the
free-var head `^&0` and the free-var shift `termShiftVec` (`^&x ↦ ^&(x+1)`):
`fvarSeq (m+1) = ^&0 ∷ termShiftVec L m (fvarSeq m)`. -/

section FvarSeq

open LO.FirstOrder.Arithmetic.Bootstrapping
open LO.FirstOrder.Arithmetic.Bootstrapping.Arithmetic

variable {V : Type*} [ORingStructure V] [V ⊧ₘ* 𝗜𝚺₁]

namespace FvarSeqC

noncomputable def blueprint : PR.Blueprint 0 where
  zero := .mkSigma “y. y = 0”
  succ := .mkSigma “y ih k. ∃ sv, !(termShiftVecGraph ℒₒᵣ) sv k ih ∧ ∃ fz, !qqFvarDef fz 0 ∧ !adjoinDef y fz sv”

noncomputable def construction : PR.Construction V blueprint where
  zero _ := 0
  succ _ k ih := ^&0 ∷ termShiftVec ℒₒᵣ k ih
  zero_defined := .mk fun v ↦ by simp [blueprint]
  succ_defined := .mk fun v ↦ by simp [blueprint]

end FvarSeqC

section

open FvarSeqC

/-- Internal free-variable sequence `fvarSeq m = ⟨^&0, …, ^&(m-1)⟩`. -/
noncomputable def fvarSeq (m : V) : V := construction.result ![] m

noncomputable def fvarSeqGraph : 𝚺₁.Semisentence 2 := blueprint.resultDef

@[simp] lemma fvarSeq_zero : fvarSeq (0 : V) = 0 := by simp [fvarSeq, construction]

@[simp] lemma fvarSeq_succ (m : V) :
    fvarSeq (m + 1) = ^&0 ∷ termShiftVec ℒₒᵣ m (fvarSeq m) := by simp [fvarSeq, construction]

instance fvarSeq.defined : 𝚺₁-Function₁[V] fvarSeq via fvarSeqGraph := .mk fun v ↦ by
  simp [construction.result_defined_iff, fvarSeqGraph, fvarSeq, Matrix.comp_vecCons',
    Matrix.constant_eq_singleton, Matrix.empty_eq]

instance fvarSeq.definable : 𝚺₁-Function₁ (fvarSeq : V → V) := fvarSeq.defined.to_definable

instance fvarSeq.definable' : Γ-[m + 1]-Function₁ (fvarSeq : V → V) := .of_sigmaOne fvarSeq.definable

@[simp] lemma IsSemitermVec_fvarSeq (m : V) : IsSemitermVec ℒₒᵣ m 0 (fvarSeq m) := by
  induction m using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ m ih =>
    rw [fvarSeq_succ]
    exact (ih.termShiftVec).adjoin (by simp)

@[simp] lemma len_fvarSeq (m : V) : len (fvarSeq m) = m := by
  induction m using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ m ih => simp [len_termShiftVec (IsSemitermVec_fvarSeq m).isUTerm]

@[simp] lemma nth_fvarSeq {m i : V} (hi : i < m) : (fvarSeq m).[i] = ^&i := by
  induction m using ISigma1.sigma1_succ_induction generalizing i
  · definability
  case zero => simp at hi
  case succ m ih =>
    rcases zero_or_succ i with (rfl | ⟨i, rfl⟩)
    · simp
    · have him : i < m := by simpa using hi
      rw [fvarSeq_succ, nth_adjoin_succ,
        nth_termShiftVec (L := ℒₒᵣ) (IsSemitermVec_fvarSeq m).isUTerm him, ih him,
        termShift_fvar (L := ℒₒᵣ)]

end

end FvarSeq

/-- **`𝗣𝗔⁻` is Δ₁-definable** (axiom-clean). `𝗣𝗔⁻` is a finite theory (`PeanoMinus.finite`:
`𝗣𝗔⁻ = 𝗘𝗤 ∪ {17 axioms}`, all over the finite-symbol language `ℒₒᵣ`), so the finite-theory
combinator `Theory.Δ₁.ofFinite` enumerates it into a `𝚫₁.Semisentence 1`. -/
@[reducible] noncomputable def paMinusDelta1 : (𝗣𝗔⁻ : ArithmeticTheory).Δ₁ :=
  Theory.Δ₁.ofFinite 𝗣𝗔⁻ PeanoMinus.finite

/-- **The full induction scheme is Δ₁-definable** — the remaining obligation toward the axiom-free
headline (one disclosed `sorry`).

`InductionScheme ℒₒᵣ Set.univ = { ψ | ∃ φ : Semiformula ℒₒᵣ ℕ 1, ψ = univCl (succInd φ) }`
where `succInd φ = “φ(0) → (∀x, φ(x) → φ(x+1)) → ∀x φ(x)”` and `univCl` closes the free parameters.

**What `Theory.Δ₁` requires** (`ch : 𝚫₁.Semisentence 1`, `mem_iff`, `isDelta1 : ch.ProvablyProperOn 𝗜𝚺₁`):
a Δ₁ formula `ch(y)` with `ℕ ⊧ ch(⌜ψ⌝) ↔ ∃φ, ψ = univCl (succInd φ)`, provably Σ↔Π in `𝗜𝚺₁`.

**Construction plan** (all primitives exist in `Foundation/.../Bootstrapping/Syntax/`):
1. ✅ **DONE (lap 78): `succIndCodeT` + `succIndCodeT_quote`** above — the internal `succInd` builder,
   quote-correct (`succIndCodeT ⌜φ⌝ = ⌜succInd φ⌝`), axiom-clean.
2. Internal `univClClose q` = iterate `qqAll` over the free `^&i` of `q` (count = max fvar + 1) — a
   `𝚺₁` function; the closure makes the result a sentence. **THE remaining wall** (no internal `fvSup`/
   closure machinery in Foundation; needs a Σ₁-recursion over the formula + a bounded ∀-wrap loop).
3. `ch(y) := ∃ p < y, IsSemiformula 1 p ∧ y = univClClose (succIndCode p)` — bounded `∃` (the
   construction strictly grows the code), hence Δ₁ (Δ₀ over the Δ₁ pieces).
4. `mem_iff`: bridge `⌜univCl (succInd φ)⌝ = univClClose (succIndCode ⌜φ⌝)` via the
   quote/`substs`/`qqAll` coding lemmas (`typed_quote_substs`, the `qq*` quote computations).
5. `isDelta1`: `ProvablyProperOn.ofProperOn` + properness of the bounded `∃` over already-proper pieces.

This is a substantial but math-free arithmetization (Foundation's own `ISigma1_delta1Definable` is
likewise still an axiom). It is the precise, resumable next step on this front. -/
@[reducible] noncomputable def inductionSchemeUnivDelta1 : (InductionScheme ℒₒᵣ Set.univ).Δ₁ := sorry

/-- **`𝗣𝗔` is Δ₁-definable**, assembled from the finite base and the scheme. The defeq
`𝗣𝗔 = 𝗣𝗔⁻ + InductionScheme ℒₒᵣ Set.univ` makes `Theory.Δ₁.add` land directly. Once
`inductionSchemeUnivDelta1` is sorry-free, `Reduction.lean` rewires `peano_not_proves_consistency`
to `@consistent_unprovable 𝗣𝗔 paDelta1 _ _`, dropping `PA_delta1Definable` from the headline. -/
@[reducible] noncomputable def paDelta1 : (𝗣𝗔 : ArithmeticTheory).Δ₁ :=
  paMinusDelta1.add inductionSchemeUnivDelta1

end GoodsteinPA
