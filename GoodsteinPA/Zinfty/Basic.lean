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

namespace GoodsteinPA.ZinftyF

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
def LitTrue (φ : ArithmeticFormula ℕ) : Prop := GoodsteinPA.Compat.gEvalm ℕ ![] (id : ℕ → ℕ) φ

/-- `∼`-duality: a closed formula is true iff its negation is false. -/
@[simp, grind =]
lemma litTrue_neg (φ : ArithmeticFormula ℕ) : LitTrue (∼φ) ↔ ¬ LitTrue φ := by simp [LitTrue];

/-- Totality (classical): every closed formula is true or its negation is. -/
lemma litTrue_or_neg (φ : ArithmeticFormula ℕ) : LitTrue φ ∨ LitTrue (∼φ) := by simp [LitTrue, em];

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

/-- **Sequent weakening**: enlarge the sequent without raising bounds.
- [Tow20, Lemma 19.1] -/
@[grind →]
lemma weakening (h : Γ ⊆ Δ) : Provable α c Γ → Provable α c Δ := by
  rintro ⟨D, ho, hcr⟩
  exact ⟨Derivation.weak D h, by tauto, by tauto⟩

/-- Provability respects set equality of sequents. -/
lemma cast (e : Γ = Δ) : Provable α c Γ → Provable α c Δ := fun h => e ▸ h

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

end Provable

end GoodsteinPA.ZinftyF
