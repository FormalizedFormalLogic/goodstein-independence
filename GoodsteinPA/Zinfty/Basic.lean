/-
# `Z_∞` calculus — core definitions

The definition layer of the infinitary ω-rule calculus `Z_∞` over Foundation's real PA syntax
(`ArithmeticFormula ℕ`): the closed formulas, numerals `nm`, signed literals
`signedLit`/`LitTrue`, the calculus `Derivation`, and the derivation measures
`ordinalBound` / `cutRank` together with the bounded-provability predicate `Provable`. Sequents
are finite sets of closed formulas (`Finset (ArithmeticFormula ℕ)`). The cut-elimination lemmas
built on top of these live in `GoodsteinPA.Zinfty.Cut`.

- [Tow20, §13, §15, §18]
-/
module

public import Foundation.FirstOrder.Incompleteness.Second
public import Foundation.FirstOrder.Arithmetic.R0.Representation
public import Mathlib.SetTheory.Ordinal.Principal
public import Mathlib.SetTheory.Ordinal.Veblen
public import Mathlib.Data.ENat.Lattice
public import GoodsteinPA.ToFoundation.Numeral

@[expose] public section

namespace GoodsteinPA.Zinfty

open LO LO.FirstOrder LO.FirstOrder.ArithmeticTerm

/-- A **signed atomic literal**: `signedLit true r v = rel r v`, `signedLit false r v = nrel r v`. The
atomic-truth axiom `axTrue` ranges over *true closed literals* of either polarity (the ω-logic
leaf that lets `Z_∞` prove PA's equational/arithmetic axioms). -/
@[grind =]
def signedLit : Bool → {k : ℕ} → (ℒₒᵣ).Rel k → (Fin k → ArithmeticSemiterm ℕ 0) → ArithmeticFormula ℕ
  | true, _, r, v => Semiformula.rel r v
  | false, _, r, v => Semiformula.nrel r v

/-- **ℕ-truth of a closed formula** (the side condition `axTrue` carries on its literal): the
standard ℒₒᵣ-model evaluation with no bound variables. For a closed literal the free-variable
assignment is immaterial (fixed to `id`). -/
@[grind =]
def LitTrue (φ : ArithmeticFormula ℕ) : Prop := Semiformula.gEvalm ℕ ![] (id : ℕ → ℕ) φ

/-- `∼`-duality: a closed formula is true iff its negation is false. -/
@[simp, grind =]
lemma litTrue_neg (φ : ArithmeticFormula ℕ) : LitTrue (∼φ) ↔ ¬ LitTrue φ := by simp [LitTrue];

/-- Totality (classical): every closed formula is true or its negation is. -/
lemma litTrue_or_neg (φ : ArithmeticFormula ℕ) : LitTrue φ ∨ LitTrue (∼φ) := by simp [LitTrue, em];

@[simp] lemma litTrue_verum : LitTrue ⊤ := by simp [LitTrue]
@[simp] lemma litTrue_falsum : ¬(LitTrue ⊥) := by simp [LitTrue]
lemma iff_litTrue_or : LitTrue (φ ⋎ ψ) ↔ LitTrue φ ∨ LitTrue ψ := by simp [LitTrue]
lemma iff_litTrue_and : LitTrue (φ ⋏ ψ) ↔ LitTrue φ ∧ LitTrue ψ := by simp [LitTrue]

variable {k : ℕ} {b : Bool} {r : (ℒₒᵣ).Rel k} {v : Fin k → ArithmeticSemiterm ℕ 0}

/-- The negation of a signed literal flips its sign. -/
@[simp, grind =]
lemma neg_lit: ∼(signedLit b r v) = signedLit (!b) r v := by cases b <;> simp [signedLit]

/-- Flipping a signed literal's polarity flips its truth value: the opposite literal is true iff the
literal is false. (The atomic-cut / false-literal-removal truth pivot.) -/
@[grind =] lemma litTrue_flip : LitTrue (signedLit (!b) r v) ↔ ¬LitTrue (signedLit b r v) := by
  simp [←neg_lit, litTrue_neg];

@[simp, grind .] lemma lit_ne_verum : signedLit b r v ≠ ⊤ := by cases b <;> simp [signedLit]
@[simp, grind .] lemma lit_ne_falsum : signedLit b r v ≠ ⊥ := by cases b <;> simp [signedLit]

/-- **The `Z_∞` calculus** over real `ℒₒᵣ` syntax. The `allω` (ω-rule) constructor stores one
sub-derivation per numeral `n`: from `insert (φ/[nm n]) Γ` for every `n`, conclude
`insert (∀⁰ φ) Γ`.
- [Tow20, §13] -/
inductive Derivation : Finset (ArithmeticFormula ℕ) → Type
  | axL {Γ} {k} (r : (ℒₒᵣ).Rel k) (v)
    (hp : Semiformula.rel r v ∈ Γ)
    (hn : Semiformula.nrel r v ∈ Γ)
    : Derivation Γ
  | axTrue {Γ} {k} (b : Bool) (r : (ℒₒᵣ).Rel k) (v)
    (htrue : LitTrue (signedLit b r v))
    (hmem : signedLit b r v ∈ Γ)
    : Derivation Γ
  | verumR {Γ} (h : ⊤ ∈ Γ) : Derivation Γ
  | weak {Δ Γ} (D : Derivation Δ) (h : Δ ⊆ Γ) : Derivation Γ
  | andI {Γ} (φ ψ) (D₁ : Derivation (insert φ Γ)) (D₂ : Derivation (insert ψ Γ)) :
    Derivation (insert (φ ⋏ ψ) Γ)
  | orI {Γ} (φ ψ) (D : Derivation (insert φ (insert ψ Γ))) : Derivation (insert (φ ⋎ ψ) Γ)
  | allω {Γ} (φₓ : ArithmeticSemiformula ℕ 1) (Dₓ : (n : ℕ) → Derivation (insert (φₓ/[nm n]) Γ))
    : Derivation (insert (∀⁰ φₓ) Γ)
  | exI {Γ} (φₓ : ArithmeticSemiformula ℕ 1) (n : ℕ) (D : Derivation (insert (φₓ/[nm n]) Γ))
    : Derivation (insert (∃⁰ φₓ) Γ)
  | cut {Γ} φ (D₁ : Derivation (insert φ Γ)) (D₂ : Derivation (insert (∼φ) Γ)) : Derivation Γ

namespace Derivation

/-- **Ordinal bound** of a derivation: the ordinal height, realizing the superscript `α` of the
bounded-deduction judgement `Z_∞ ⊢^{α,k}_c Γ`. The source defines the bounded system by baking the
bound into the rules (every premise bounded by an ordinal `< α`); here it is instead a measure
computed by recursion on the unbounded `Derivation` tree — the ω-rule node takes the supremum of its
`ℕ`-many premise bounds, then `+1`, and weakening is height-preserving.
- [Tow20, §15] -/
@[grind =]
noncomputable def ordinalBound : Derivation Γ → Ordinal.{0}
  | axL _ _ _ _ => 0
  | axTrue _ _ _ _ _ => 0
  | verumR _ => 0
  | weak D _ => D.ordinalBound
  | andI _ _ D₁ D₂ => max (D₁.ordinalBound) (D₂.ordinalBound) + 1
  | orI _ _ D => D.ordinalBound + 1
  | allω _ Dₓ => (⨆ n, (Dₓ n).ordinalBound) + 1
  | exI _ _ D => D.ordinalBound + 1
  | cut _ D₁ D₂ => max (D₁.ordinalBound) (D₂.ordinalBound) + 1

/-- The ω-rule bound strictly dominates each premise bound. -/
@[simp, grind .]
lemma o_allω_gt {Dₓ : (n : ℕ) → Derivation (insert (φₓ/[nm n]) Γ)}
  : (Dₓ n).ordinalBound < (allω φₓ Dₓ).ordinalBound := by
  calc
    _ ≤ ⨆ m, ordinalBound (Dₓ m)       := Ordinal.le_iSup (fun m => ordinalBound (Dₓ m)) n
    _ < (⨆ m, ordinalBound (Dₓ m)) + 1 := lt_add_of_pos_right _ one_pos
    _ = _                              := rfl

/-- **Cut rank** of a derivation, realizing the subscript `c` of `Z_∞ ⊢^{α,k}_c Γ`: the maximum over
the cut formulas used of their rank `+ 1`, taken in `ℕ∞` so the ω-rule supremum is well-defined.
Foundation's `complexity` plays the role of Towsner's formula rank `rk`. *Crucially finite per cut*
(`complexity φ : ℕ`), so `Provable α (c : ℕ)` meaningfully bounds quantified cut formulas. A cut-free
derivation has `cutRank = 0`.
- [Tow20, §18, Definition 16.2] -/
@[grind =]
noncomputable def cutRank : Derivation Γ → ℕ∞
  | axL _ _ _ _ => 0
  | axTrue _ _ _ _ _ => 0
  | verumR _ => 0
  | weak D _ => D.cutRank
  | andI _ _ D₁ D₂ => max (D₁.cutRank) (D₂.cutRank)
  | orI _ _ D => D.cutRank
  | allω _ Dₓ => ⨆ n, (Dₓ n).cutRank
  | exI _ _ D => D.cutRank
  | cut φ D₁ D₂ => max (φ.complexity + 1) (max (D₁.cutRank) (D₂.cutRank))

end Derivation

/-- The bounded-derivability predicate `Z_∞ ⊢^{α}_c Γ`: existence of a derivation with
`ordinalBound ≤ α` and `cutRank ≤ c` (every cut formula has rank `< c`). This drops the source's
numeric side bound `k` (the `τ(α) < k` complexity condition), keeping only the ordinal bound `α`
and the cut rank `c`.
- [Tow20, §18] -/
@[grind =]
def Provable (α : Ordinal.{0}) (c : ℕ) (Γ : Finset (ArithmeticFormula ℕ)) : Prop :=
  ∃ D : Derivation Γ, D.ordinalBound ≤ α ∧ D.cutRank ≤ (c : ℕ∞)

variable {α β : Ordinal.{0}} {c c' : ℕ} {k n ar : ℕ}
         {φ ψ : ArithmeticFormula ℕ} {φₓ : ArithmeticSemiformula ℕ 1}
         {Γ Δ : Finset (ArithmeticFormula ℕ)}
namespace Provable

/-- **Bound monotonicity**: relax either recorded bound.
- [Tow20, Lemma 16.4] -/
@[grind →]
lemma mono (hα : α ≤ β) (hc : c ≤ c') : Provable α c Γ → Provable β c' Γ := by
  rintro ⟨D, ho, hcr⟩;
  exact ⟨D, ho.trans hα, hcr.trans (by exact_mod_cast hc)⟩

lemma mono_ordinalBound (h : α ≤ β) : Provable α c Γ → Provable β c Γ := mono h le_rfl
lemma mono_cutRank (h : c ≤ c') : Provable α c Γ → Provable α c' Γ := mono le_rfl h

/-- **Sequent weakening**: enlarge the sequent without raising bounds.
- [Tow20, Lemma 19.1] -/
@[grind →]
lemma weakening (h : Γ ⊆ Δ) : Provable α c Γ → Provable α c Δ := by
  rintro ⟨D, ho, hcr⟩
  exact ⟨D.weak h, by tauto, by tauto⟩

/-- Provability respects set equality of sequents. -/
lemma cast (e : Γ = Δ) : Provable α c Γ → Provable α c Δ := fun h => e ▸ h

/-- **Absorption**: a formula already present in `Γ` can be dropped from an extra `insert`. -/
@[grind →]
lemma insert_absorb (h : Provable α c (insert φ Γ)) (hmem : φ ∈ Γ) : Provable α c Γ := by
  rwa [Finset.insert_eq_self.mpr hmem] at h

/-- Identity axiom: `rel r v` and `nrel r v` together close at bound `0`, cut rank `0`.
- [Tow20, §13] -/
@[grind →]
lemma axL (r : (ℒₒᵣ).Rel k) (v) (hp : Semiformula.rel r v ∈ Γ) (hn : Semiformula.nrel r v ∈ Γ)
  : Provable 0 0 Γ :=
  ⟨Derivation.axL r v hp hn, by tauto, by tauto⟩

/-- **Atomic-truth axiom** (the ω-logic leaf): a true closed literal closes any sequent containing
it, at bound `0`, cut rank `0`.
- [Tow20, §13] -/
@[grind →]
lemma axTrue (b : Bool) (r : (ℒₒᵣ).Rel k) (v) (htrue : LitTrue (signedLit b r v)) (hmem : signedLit b r v ∈ Γ)
  : Provable 0 0 Γ :=
  ⟨Derivation.axTrue b r v htrue hmem, by tauto, by tauto⟩

/-- `⊤` closes a sequent at bound `0`, cut rank `0`.
- [Tow20, §13] -/
@[grind →]
lemma verumR (h : ⊤ ∈ Γ) : Provable 0 0 Γ := ⟨Derivation.verumR h, by tauto, by tauto⟩

/-- Predicate-level `∧`-introduction.
- [Tow20, §13] -/
@[grind →]
lemma andI (hφ : Provable α c (insert φ Γ)) (hψ : Provable β c (insert ψ Γ)) :
  Provable (max α β + 1) c (insert (φ ⋏ ψ) Γ) := by
  obtain ⟨Dφ, hoφ, hcφ⟩ := hφ;
  obtain ⟨Dψ, hoψ, hcψ⟩ := hψ;
  refine ⟨Derivation.andI φ ψ Dφ Dψ, ?_, ?_⟩
  · simp only [Derivation.ordinalBound]; exact add_le_add (max_le_max hoφ hoψ) le_rfl
  · simp only [Derivation.cutRank]; exact max_le hcφ hcψ

/-- Predicate-level `∨`-introduction.
- [Tow20, §13] -/
@[grind →]
lemma orI (h : Provable α c (insert φ (insert ψ Γ))) : Provable (α + 1) c (insert (φ ⋎ ψ) Γ) := by
  obtain ⟨D, ho, hcr⟩ := h;
  exact ⟨
    Derivation.orI φ ψ D,
    by simpa [Derivation.ordinalBound] using add_le_add_right ho 1,
    by tauto
  ⟩

/-- Predicate-level `∃`-introduction (witness rule). The witness is a **numeral** `nm n`: in the
arithmetic term model every closed term denotes a numeral, and numeral witnesses are what the
ω-rule inversion (`allInv`) produces, so the ∀/∃ cut-reduction (§19.6) can match the witness
against the inverted ∀-family.
- [Tow20, §13] -/
@[grind →]
lemma exI (n : ℕ) (h : Provable α c (insert (φₓ/[nm n]) Γ)) :
  Provable (α + 1) c (insert (∃⁰ φₓ) Γ) := by
  obtain ⟨D, ho, hcr⟩ := h;
  exact ⟨
    Derivation.exI φₓ n D,
    by simpa [Derivation.ordinalBound] using add_le_add_right ho 1,
    by tauto;
  ⟩

/-- **Predicate-level ω-rule.** From a uniform-cut-rank family of premises with ordinal bounds
`βₓ n`, conclude `∀` at bound `(⨆ n, βₓ n) + 1`.
- [Tow20, §13] -/
lemma allω {βₓ : ℕ → Ordinal.{0}}
  (h : ∀ n, Provable (βₓ n) c (insert (φₓ/[nm n]) Γ)) :
  Provable ((⨆ n, βₓ n) + 1) c (insert (∀⁰ φₓ) Γ) := by
  choose Dₓ ho hcr using h;
  refine ⟨Derivation.allω φₓ Dₓ, ?_, ?_⟩
  · apply add_le_add ?_ le_rfl;
    exact Ordinal.iSup_le fun n => (ho n).trans (Ordinal.le_iSup βₓ n);
  · exact iSup_le hcr;

/-- **Contraction is free** (the payoff of set sequents): a duplicate insert collapses.
- [Tow20, §13] -/
@[grind →]
lemma contr (φ : ArithmeticFormula ℕ) (h : Provable α c (insert φ (insert φ Γ)))
  : Provable α c (insert φ Γ) := by
  simpa [Finset.insert_idem] using h

/-- **Predicate-level cut.** From `insert φ Γ` and `insert (∼φ) Γ` at cut rank `≤ c` with
`complexity φ < c`, conclude `Γ` at the same cut rank.
- [Tow20, §13] -/
lemma cut (χ : ArithmeticFormula ℕ) (hc : (χ.complexity + 1 : ℕ∞) ≤ (c : ℕ∞))
  (h₁ : Provable α c (insert χ Γ)) (h₂ : Provable β c (insert (∼χ) Γ)) :
  Provable (max α β + 1) c Γ := by
  obtain ⟨D₁, ho₁, hcr₁⟩ := h₁;
  obtain ⟨D₂, ho₂, hcr₂⟩ := h₂;
  use Derivation.cut χ D₁ D₂;
  constructor;
  · exact add_le_add (max_le_max ho₁ ho₂) le_rfl
  · exact max_le hc (max_le hcr₁ hcr₂)

attribute [grind =]
  Semiformula.complexity_and
  Semiformula.complexity_or
  Semiformula.complexity_all
  Semiformula.complexity_exs

/-- Auxiliary step shared by the `∧`/`∨` cases of the excluded-middle induction (`lemAux`): given a
conjunction `A ⋏ B` and a disjunction `C ⋎ D` both in `Γ`, derivability of `A` and of `B` alongside
`C`, `D` on the left collapses to derivability of `Γ` alone. -/
lemma em_binaryStep (hab : A ⋏ B ∈ Γ) (hcd : C ⋎ D ∈ Γ)
    (h1 : ∃ a, Provable a 0 (insert A (insert C (insert D Γ))))
    (h2 : ∃ a, Provable a 0 (insert B (insert C (insert D Γ)))) :
    ∃ a, Provable a 0 Γ := by
  obtain ⟨a, h1⟩ := h1
  obtain ⟨b, h2⟩ := h2
  have hand := (Provable.andI h1 h2).insert_absorb
    (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hab))
  exact ⟨_, hand.orI.insert_absorb hcd⟩

/-- Auxiliary step shared by the `∀`/`∃` cases of the excluded-middle induction (`lemAux`): given
`∀⁰ φₓ` and `∃⁰ ψₓ` both in `Γ`, derivability of every instance `ψₓ/[nm n]` alongside `φₓ/[nm n]` on
the left collapses to derivability of `Γ` alone. -/
lemma em_quantStep (hall' : (∀⁰ φₓ) ∈ Γ) (hexs' : (∃⁰ ψₓ) ∈ Γ)
    (fam : ∀ n, ∃ a, Provable a 0 (insert (ψₓ/[nm n]) (insert (φₓ/[nm n]) Γ))) :
    ∃ a, Provable a 0 Γ := by
  choose β hβ using fam
  have hex : ∀ n, Provable (β n + 1) 0 (insert (φₓ/[nm n]) Γ) :=
    fun n => (Provable.exI n (hβ n)).insert_absorb (Finset.mem_insert_of_mem hexs')
  exact ⟨_, (Provable.allω hex).insert_absorb hall'⟩

lemma lemAux (φ  : ArithmeticFormula ℕ) (hk : φ.complexity ≤ k) (hp : φ ∈ Γ) (hn : ∼φ ∈ Γ) : ∃ α, Provable α 0 Γ := by
  induction k generalizing φ Γ with
  | zero =>
    cases φ using Semiformula.cases' with
    | hverum    => exact ⟨0, Provable.verumR hp⟩
    | hfalsum   => exact ⟨0, Provable.verumR (by simpa using hn)⟩
    | hrel r v  => exact ⟨0, Provable.axL r v hp (by simpa using hn)⟩
    | hnrel r v => exact ⟨0, Provable.axL r v (by simpa using hn) hp⟩
    | _ => simp at hk
  | succ k ih =>
    cases φ using Semiformula.cases' with
    | hverum    => exact ⟨0, Provable.verumR hp⟩
    | hfalsum   => exact ⟨0, Provable.verumR (by simpa using hn)⟩
    | hrel r v  => exact ⟨0, Provable.axL r v hp (by simpa using hn)⟩
    | hnrel r v => exact ⟨0, Provable.axL r v (by simpa using hn) hp⟩
    | hand φ ψ =>
      haveI : φ.complexity ≤ k := by grind;
      haveI : ψ.complexity ≤ k := by grind;
      obtain ⟨α1, h1⟩ := ih φ ‹_› (Γ := insert φ (insert (∼φ) (insert (∼ψ) Γ))) (by grind) (by grind);
      obtain ⟨α2, h2⟩ := ih ψ ‹_› (Γ := insert ψ (insert (∼φ) (insert (∼ψ) Γ))) (by grind) (by grind);
      exact Provable.em_binaryStep hp (show (∼φ ⋎ ∼ψ) ∈ Γ by simpa using hn) ⟨α1, h1⟩ ⟨α2, h2⟩
    | hor φ ψ =>
      haveI : φ.complexity ≤ k := by grind
      haveI : ψ.complexity ≤ k := by grind
      obtain ⟨α1, h1⟩ := ih φ ‹_› (Γ := insert (∼φ) (insert φ (insert ψ Γ))) (by grind) (by grind)
      obtain ⟨α2, h2⟩ := ih ψ ‹_› (Γ := insert (∼ψ) (insert φ (insert ψ Γ))) (by grind) (by grind)
      exact Provable.em_binaryStep (show (∼φ ⋏ ∼ψ) ∈ Γ by simpa using hn) hp ⟨α1, h1⟩ ⟨α2, h2⟩
    | hall ψ =>
      refine Provable.em_quantStep hp (show (∃⁰ ∼ψ) ∈ Γ by simpa using hn) fun n => ?_
      have hcomp : (ψ/[nm n]).complexity ≤ k := calc
        _ = ψ.complexity := by simp;
        _ ≤ k            := by grind;
      obtain ⟨α, hα⟩ := ih (ψ/[nm n]) hcomp (Γ := insert (∼(ψ/[nm n])) (insert (ψ/[nm n]) Γ)) (by grind) (by grind)
      have heq : (∼ψ)/[nm n] = ∼(ψ/[nm n]) := by simp
      exact ⟨α, heq ▸ hα⟩
    | hexs ψ =>
      refine Provable.em_quantStep (show (∀⁰ ∼ψ) ∈ Γ by simpa using hn) hp fun n => ?_
      have hcomp : (ψ/[nm n]).complexity ≤ k := calc
        _ = ψ.complexity := by simp
        _ ≤ k            := by grind;
      obtain ⟨α, hα⟩ := ih (ψ/[nm n]) hcomp (Γ := insert (ψ/[nm n]) (insert (∼(ψ/[nm n])) Γ)) (by simp) (by simp)
      have heq : (∼ψ)/[nm n] = ∼(ψ/[nm n]) := by simp
      exact ⟨α, heq ▸ hα⟩

/-- **Identity / law of excluded middle for `Z_∞`** (the `closed` case). For any `φ`, a sequent
containing both `φ` and `∼φ` is `Z_∞`-derivable cut-free. Proved by induction on a `complexity`
bound (the standard Tait `em`, cf. Foundation `Derivation.em`, `Calculus.lean:164`). The atomic /
propositional cases are discharged here; the **∀/∃ cases** use the numeral ω-family (`allω` over
all `nm n`, each premise closed by `exI` + the inductive hypothesis at the substitution instance `φ/[nm n]`,
whose `complexity` equals `φ`'s).
- [Tow20, §14] -/
theorem lem (hp : φ ∈ Γ) (hn : ∼φ ∈ Γ) : ∃ α, Provable α 0 Γ := lemAux φ le_rfl hp hn

/-- **ω-completeness for true closed formulas.** Any closed (`ArithmeticFormula ℕ`) formula that is
TRUE in the standard model `ℕ` (`LitTrue`) is `Z∞`-derivable, cut-free. Proof by induction on
`complexity`: atomic via `axTrue`, `∀` via the ω-rule `allω`, `∃` by choosing a true witness.
- [Tow20, §14] -/
theorem of_trueAux (hk : φ.complexity ≤ k) (htrue : LitTrue φ) (hmem : φ ∈ Γ) : ∃ α, Provable α 0 Γ := by
  induction k generalizing φ Γ htrue hmem with
  | zero =>
    cases φ using Semiformula.cases' with
    | hfalsum   => simp_all;
    | hverum    => exact ⟨0, Provable.verumR hmem⟩
    | hrel r v  => exact ⟨0, Provable.axTrue true r v htrue hmem⟩
    | hnrel r v => exact ⟨0, Provable.axTrue false r v htrue hmem⟩
    | _ => simp at hk
  | succ k ih =>
    cases φ using Semiformula.cases' with
    | hfalsum  => simp_all;
    | hverum   => exact ⟨0, Provable.verumR hmem⟩
    | hrel r v => exact ⟨0, Provable.axTrue true r v htrue hmem⟩
    | hnrel r v => exact ⟨0, Provable.axTrue false r v htrue hmem⟩
    | hand φ ψ =>
      have : φ.complexity ≤ k := by simp only [Semiformula.complexity_and] at hk; omega
      have : ψ.complexity ≤ k := by simp only [Semiformula.complexity_and] at hk; omega
      obtain ⟨hta, htb⟩ := iff_litTrue_and.mp htrue
      obtain ⟨α1, h1⟩ := ih ‹_› hta (Γ := insert φ Γ) (by simp)
      obtain ⟨α2, h2⟩ := ih ‹_› htb (Γ := insert ψ Γ) (by simp)
      exact ⟨_, (Provable.andI h1 h2).insert_absorb hmem⟩
    | hor φ ψ =>
      rcases (iff_litTrue_or.mp htrue) with hta | htb
      · have : φ.complexity ≤ k := by grind;
        obtain ⟨α1, h1⟩ := ih ‹_› hta (Γ := insert φ (insert ψ Γ)) (by simp)
        exact ⟨_, (Provable.orI h1).insert_absorb hmem⟩;
      · have : ψ.complexity ≤ k := by grind;
        obtain ⟨α2, h2⟩ := ih ‹_› htb (Γ := insert φ (insert ψ Γ)) (by simp)
        exact ⟨_, (Provable.orI h2).insert_absorb hmem⟩;
    | hall a =>
      have hak : a.complexity ≤ k := by grind;
      have hfam : ∀ n, LitTrue (a/[nm n]) := by
        intro n
        have := htrue
        simp only [LitTrue, Semiformula.eval_all] at this
        simpa [LitTrue, Semiformula.eval_substs, valm_nm, Matrix.constant_eq_singleton]
          using this n
      have fam : ∀ n, ∃ x, Provable x 0 (insert (a/[nm n]) Γ) := by
        intro n
        have hcomp : (a/[nm n]).complexity ≤ k := by
          have : (a/[nm n]).complexity = a.complexity := by simp
          rw [this]; exact hak
        exact ih (φ := a/[nm n]) hcomp (hfam n) (by simp)
      choose β hβ using fam
      exact ⟨_, (Provable.allω hβ).insert_absorb hmem⟩
    | hexs a =>
      have hak : a.complexity ≤ k := by simp only [Semiformula.complexity_exs] at hk; omega
      have hex : ∃ n, LitTrue (a/[nm n]) := by
        have := htrue
        simp only [LitTrue, Semiformula.eval_ex] at this
        obtain ⟨x, hx⟩ := this
        exact ⟨x, by simpa [LitTrue, Semiformula.eval_substs, valm_nm,
          Matrix.constant_eq_singleton] using hx⟩
      obtain ⟨n, hn⟩ := hex
      have hcomp : (a/[nm n]).complexity ≤ k := by
        have : (a/[nm n]).complexity = a.complexity := by simp
        rw [this]; exact hak
      obtain ⟨x, hx⟩ := ih (φ := a/[nm n]) hcomp hn (Γ := insert (a/[nm n]) Γ) (by simp)
      exact ⟨_, (Provable.exI n hx).insert_absorb hmem⟩

lemma of_true (htrue : LitTrue φ) (hmem : φ ∈ Γ) : ∃ α, Provable α 0 Γ := of_trueAux le_rfl htrue hmem

end Provable

end GoodsteinPA.Zinfty
