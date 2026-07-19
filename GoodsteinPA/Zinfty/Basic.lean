/-
# `Z_∞` calculus — core definitions

The definition layer of the infinitary ω-rule calculus `Z_∞` over Foundation's real PA syntax
(`ArithmeticFormula ℕ`): the closed formulas, numerals `nm`, signed literals
`signedLit`/`LitTrue`, the calculus `Derivation`, and the derivation measures
`ordinalBound` / `cutRank` together with the bounded-provability predicate `Provable`. Sequents
are finite sets of closed formulas (`Finset (ArithmeticFormula ℕ)`). The cut-elimination lemmas
built on top of these live in `GoodsteinPA.Zinfty`.

- [Tow20, §13, §15, §18]
-/
module

public import Foundation.FirstOrder.Incompleteness.Second
public import Foundation.FirstOrder.Arithmetic.R0.Representation
public import Mathlib.SetTheory.Ordinal.Principal
public import Mathlib.SetTheory.Ordinal.Veblen
public import Mathlib.Data.ENat.Lattice
public import GoodsteinPA.Compat

@[expose] public section

namespace GoodsteinPA.ZinftyF

open LO LO.FirstOrder

/-- The `n`-th numeral of `ℒₒᵣ` as a closed term, ready for substitution `φ/[nm n]`. -/
noncomputable def nm (n : ℕ) : Semiterm ℒₒᵣ ℕ 0 := (Semiterm.Operator.numeral ℒₒᵣ n).const

/-- A **signed atomic literal**: `signedLit true r v = rel r v`, `signedLit false r v = nrel r v`. The
atomic-truth axiom `axTrue` ranges over *true closed literals* of either polarity (the ω-logic
leaf that lets `Z_∞` prove PA's equational/arithmetic axioms). -/
@[grind =]
def signedLit : Bool → {k : ℕ} → (ℒₒᵣ).Rel k → (Fin k → Semiterm ℒₒᵣ ℕ 0) → (ArithmeticFormula ℕ)
  | true, _, r, v => Semiformula.rel r v
  | false, _, r, v => Semiformula.nrel r v

/-- **ℕ-truth of a closed formula** (the side condition `axTrue` carries on its literal): the
standard ℒₒᵣ-model evaluation with no bound variables. For a closed literal the free-variable
assignment is immaterial (fixed to `id`). -/
@[grind =]
def LitTrue (φ : (ArithmeticFormula ℕ)) : Prop := GoodsteinPA.Compat.gEvalm ℕ ![] (id : ℕ → ℕ) φ

/-- `∼`-duality: a closed formula is true iff its negation is false. -/
@[simp, grind =]
lemma litTrue_neg (φ : (ArithmeticFormula ℕ)) : LitTrue (∼φ) ↔ ¬ LitTrue φ := by
  unfold LitTrue; simp

/-- Totality (classical): every closed formula is true or its negation is. -/
lemma litTrue_or_neg (φ : (ArithmeticFormula ℕ)) : LitTrue φ ∨ LitTrue (∼φ) := by
  rw [litTrue_neg]; exact em _

variable {k : ℕ}

/-- The negation of a signed literal flips its sign. -/
@[simp, grind =]
lemma neg_lit (b : Bool) (r : (ℒₒᵣ).Rel k) (v) :
    ∼(signedLit b r v) = signedLit (!b) r v := by cases b <;> simp [signedLit]

/-- Flipping a signed literal's polarity flips its truth value: the opposite literal is true iff the
literal is false. (The atomic-cut / false-literal-removal truth pivot.) -/
@[grind =]
lemma litTrue_flip (b : Bool) (r : (ℒₒᵣ).Rel k) (v) :
  LitTrue (signedLit (!b) r v) ↔ ¬ LitTrue (signedLit b r v) := by
  rw [← neg_lit]; exact litTrue_neg _

/-- A signed literal is never `⊤`. -/
@[simp, grind .]
lemma lit_ne_verum (b : Bool) (r : (ℒₒᵣ).Rel k) (v) :
    signedLit b r v ≠ (⊤ : (ArithmeticFormula ℕ)) := by cases b <;> simp [signedLit]

/-- A signed literal is never `⊥`. -/
@[simp, grind .]
lemma lit_ne_falsum (b : Bool) (r : (ℒₒᵣ).Rel k) (v) :
    signedLit b r v ≠ (⊥ : (ArithmeticFormula ℕ)) := by cases b <;> simp [signedLit]

/-- **The `Z_∞` calculus** over real `ℒₒᵣ` syntax. The `allω` (ω-rule) constructor stores one
sub-derivation per numeral `n`: from `insert (φ/[nm n]) Γ` for every `n`, conclude
`insert (∀⁰ φ) Γ`.
- [Tow20, §13] -/
inductive Derivation : Finset (ArithmeticFormula ℕ) → Type
  | axL {Γ : Finset (ArithmeticFormula ℕ)} {k} (r : (ℒₒᵣ).Rel k) (v) (hp : Semiformula.rel r v ∈ Γ)
      (hn : Semiformula.nrel r v ∈ Γ) : Derivation Γ
  | axTrue {Γ : Finset (ArithmeticFormula ℕ)} {k} (b : Bool) (r : (ℒₒᵣ).Rel k) (v) (htrue : LitTrue (signedLit b r v))
      (hmem : signedLit b r v ∈ Γ) : Derivation Γ
  | verumR {Γ : Finset (ArithmeticFormula ℕ)} (h : (⊤ : (ArithmeticFormula ℕ)) ∈ Γ) : Derivation Γ
  | weak {Δ Γ : Finset (ArithmeticFormula ℕ)} (d : Derivation Δ) (h : Δ ⊆ Γ) : Derivation Γ
  | andI {Γ : Finset (ArithmeticFormula ℕ)} (φ ψ : (ArithmeticFormula ℕ)) (dφ : Derivation (insert φ Γ)) (dψ : Derivation (insert ψ Γ)) :
      Derivation (insert (φ ⋏ ψ) Γ)
  | orI {Γ : Finset (ArithmeticFormula ℕ)} (φ ψ : (ArithmeticFormula ℕ)) (d : Derivation (insert φ (insert ψ Γ))) : Derivation (insert (φ ⋎ ψ) Γ)
  | allω {Γ : Finset (ArithmeticFormula ℕ)} (φ : ArithmeticSemiformula ℕ 1)
      (d : (n : ℕ) → Derivation (insert (φ/[nm n]) Γ)) : Derivation (insert (∀⁰ φ) Γ)
  | exI {Γ : Finset (ArithmeticFormula ℕ)} (φ : ArithmeticSemiformula ℕ 1) (n : ℕ)
      (d : Derivation (insert (φ/[nm n]) Γ)) : Derivation (insert (∃⁰ φ) Γ)
  | cut {Γ : Finset (ArithmeticFormula ℕ)} (φ : (ArithmeticFormula ℕ)) (d₁ : Derivation (insert φ Γ)) (d₂ : Derivation (insert (∼φ) Γ)) : Derivation Γ

namespace Derivation

/-- **Ordinal bound** of a derivation: the ordinal height, realizing the superscript `α` of the
bounded-deduction judgement `Z_∞ ⊢^{α,k}_c Γ`. The source defines the bounded system by baking the
bound into the rules (every premise bounded by an ordinal `< α`); here it is instead a measure
computed by recursion on the unbounded `Derivation` tree — the ω-rule node takes the supremum of its
`ℕ`-many premise bounds, then `+1`, and weakening is height-preserving.
- [Tow20, §15] -/
@[grind =]
noncomputable def ordinalBound : {Γ : Finset (ArithmeticFormula ℕ)} → Derivation Γ → Ordinal.{0}
  | _, axL _ _ _ _ => 0
  | _, axTrue _ _ _ _ _ => 0
  | _, verumR _ => 0
  | _, weak d _ => ordinalBound d
  | _, andI _ _ dφ dψ => max (ordinalBound dφ) (ordinalBound dψ) + 1
  | _, orI _ _ d => ordinalBound d + 1
  | _, allω _ d => (⨆ n, ordinalBound (d n)) + 1
  | _, exI _ _ d => ordinalBound d + 1
  | _, cut _ d₁ d₂ => max (ordinalBound d₁) (ordinalBound d₂) + 1

/-- **Cut rank** of a derivation, realizing the subscript `c` of `Z_∞ ⊢^{α,k}_c Γ`: the maximum over
the cut formulas used of their rank `+ 1`, taken in `ℕ∞` so the ω-rule supremum is well-defined.
Foundation's `complexity` plays the role of Towsner's formula rank `rk`. *Crucially finite per cut*
(`complexity φ : ℕ`), so `Provable α (c : ℕ)` meaningfully bounds quantified cut formulas. A cut-free
derivation has `cutRank = 0`.
- [Tow20, §18, Definition 16.2] -/
@[grind =]
noncomputable def cutRank : {Γ : Finset (ArithmeticFormula ℕ)} → Derivation Γ → ℕ∞
  | _, axL _ _ _ _ => 0
  | _, axTrue _ _ _ _ _ => 0
  | _, verumR _ => 0
  | _, weak d _ => cutRank d
  | _, andI _ _ dφ dψ => max (cutRank dφ) (cutRank dψ)
  | _, orI _ _ d => cutRank d
  | _, allω _ d => ⨆ n, cutRank (d n)
  | _, exI _ _ d => cutRank d
  | _, cut φ d₁ d₂ => max (φ.complexity + 1 : ℕ∞) (max (cutRank d₁) (cutRank d₂))

end Derivation

/-- The bounded-derivability predicate `Z_∞ ⊢^{α}_c Γ`: existence of a derivation with
`ordinalBound ≤ α` and `cutRank ≤ c` (every cut formula has rank `< c`). This drops the source's
numeric side bound `k` (the `τ(α) < k` complexity condition), keeping only the ordinal bound `α`
and the cut rank `c`.
- [Tow20, §18] -/
@[grind =]
def Provable (α : Ordinal.{0}) (c : ℕ) (Γ : Finset (ArithmeticFormula ℕ)) : Prop :=
  ∃ d : Derivation Γ, d.ordinalBound ≤ α ∧ d.cutRank ≤ (c : ℕ∞)

end GoodsteinPA.ZinftyF
