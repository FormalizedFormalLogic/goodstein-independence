/-
# `Z_∞` provability — the inference-rule API

Predicate-level inference rules for the bounded provability judgement `Provable` (`Z_∞ ⊢`):
weakening/monotonicity of the bounds, the axiom leaves, and the introduction rules for
`∧`/`∨`/`∃`/`∀` (ω-rule), contraction, and cut.
-/
module

public import GoodsteinPA.Zinfty.Basic

@[expose] public section

namespace GoodsteinPA.ZinftyF

open LO LO.FirstOrder LO.FirstOrder.ArithmeticTerm

variable {Γ : Finset (ArithmeticFormula ℕ)} {α β : Ordinal.{0}} {c : ℕ}

namespace Derivation

/-- The ω-rule bound strictly dominates each premise bound. -/
lemma o_allω_gt (φ : ArithmeticSemiformula ℕ 1)
    (d : (n : ℕ) → Derivation (insert (φ/[nm n]) Γ)) (n : ℕ) : ordinalBound (d n) < ordinalBound (allω φ d) := by
  have h : ordinalBound (d n) ≤ ⨆ m, ordinalBound (d m) := Ordinal.le_iSup (fun m => ordinalBound (d m)) n
  calc ordinalBound (d n) ≤ ⨆ m, ordinalBound (d m) := h
    _ < (⨆ m, ordinalBound (d m)) + 1 := lt_add_of_pos_right _ one_pos
    _ = ordinalBound (allω φ d) := by simp only [ordinalBound]

end Derivation

open Derivation

namespace Provable

/-- **Bound monotonicity**: relax either recorded bound.
- [Tow20, Lemma 16.4] -/
@[grind →]
lemma mono {c' : ℕ} (hα : α ≤ β) (hc : c ≤ c') {Γ : Finset (ArithmeticFormula ℕ)} :
    Provable α c Γ → Provable β c' Γ := by
  rintro ⟨d, ho, hcr⟩
  exact ⟨d, ho.trans hα, hcr.trans (by exact_mod_cast hc)⟩

/-- **Sequent weakening**: enlarge the sequent without raising bounds.
- [Tow20, Lemma 19.1] -/
@[grind →]
lemma weakening {Δ : Finset (ArithmeticFormula ℕ)} (h : Γ ⊆ Δ) :
    Provable α c Γ → Provable α c Δ := by
  rintro ⟨d, ho, hcr⟩
  exact ⟨Derivation.weak d h, by simpa [Derivation.ordinalBound] using ho, by simpa [Derivation.cutRank] using hcr⟩

/-- Provability respects set equality of sequents. -/
lemma cast {Δ : Finset (ArithmeticFormula ℕ)} (e : Γ = Δ) :
    Provable α c Γ → Provable α c Δ := fun h => e ▸ h

/-- Identity axiom: `rel r v` and `nrel r v` together close at bound `0`, cut rank `0`.
- [Tow20, §13] -/
@[grind →]
lemma axL (r : (ℒₒᵣ).Rel k) (v)
    (hp : Semiformula.rel r v ∈ Γ) (hn : Semiformula.nrel r v ∈ Γ) : Provable 0 0 Γ :=
  ⟨Derivation.axL r v hp hn, by simp [Derivation.ordinalBound], by simp [Derivation.cutRank]⟩

/-- **Atomic-truth axiom** (the ω-logic leaf): a true closed literal closes any sequent containing
it, at bound `0`, cut rank `0`.
- [Tow20, §13] -/
@[grind →]
lemma axTrue (b : Bool) (r : (ℒₒᵣ).Rel k) (v)
    (htrue : LitTrue (signedLit b r v)) (hmem : signedLit b r v ∈ Γ) : Provable 0 0 Γ :=
  ⟨Derivation.axTrue b r v htrue hmem, by simp [Derivation.ordinalBound], by simp [Derivation.cutRank]⟩

/-- `⊤` closes a sequent at bound `0`, cut rank `0`.
- [Tow20, §13] -/
@[grind →]
lemma verumR (h : ⊤ ∈ Γ) : Provable 0 0 Γ :=
  ⟨Derivation.verumR h, by simp [Derivation.ordinalBound], by simp [Derivation.cutRank]⟩

/-- Predicate-level `∧`-introduction.
- [Tow20, §13] -/
@[grind →]
lemma andI (φ ψ)
    (hφ : Provable α c (insert φ Γ)) (hψ : Provable β c (insert ψ Γ)) :
    Provable (max α β + 1) c (insert (φ ⋏ ψ) Γ) := by
  rcases hφ with ⟨dφ, hoφ, hcφ⟩
  rcases hψ with ⟨dψ, hoψ, hcψ⟩
  refine ⟨Derivation.andI φ ψ dφ dψ, ?_, ?_⟩
  · simp only [Derivation.ordinalBound]; exact add_le_add (max_le_max hoφ hoψ) le_rfl
  · simp only [Derivation.cutRank]; exact max_le hcφ hcψ

/-- Predicate-level `∨`-introduction.
- [Tow20, §13] -/
@[grind →]
lemma orI (φ ψ)
    (h : Provable α c (insert φ (insert ψ Γ))) : Provable (α + 1) c (insert (φ ⋎ ψ) Γ) := by
  rcases h with ⟨d, ho, hcr⟩
  exact ⟨Derivation.orI φ ψ d, by simpa [Derivation.ordinalBound] using add_le_add_right ho 1,
    by simpa [Derivation.cutRank] using hcr⟩

/-- Predicate-level `∃`-introduction (witness rule). The witness is a **numeral** `nm n`: in the
arithmetic term model every closed term denotes a numeral, and numeral witnesses are what the
ω-rule inversion (`allInv`) produces, so the ∀/∃ cut-reduction (§19.6) can match the witness
against the inverted ∀-family.
- [Tow20, §13] -/
@[grind →]
lemma exI (φ : ArithmeticSemiformula ℕ 1)
    (n : ℕ) (h : Provable α c (insert (φ/[nm n]) Γ)) :
    Provable (α + 1) c (insert (∃⁰ φ) Γ) := by
  rcases h with ⟨d, ho, hcr⟩
  exact ⟨Derivation.exI φ n d, by simpa [Derivation.ordinalBound] using add_le_add_right ho 1,
    by simpa [Derivation.cutRank] using hcr⟩

/-- **Predicate-level ω-rule.** From a uniform-cut-rank family of premises with ordinal bounds
`β n`, conclude `∀` at bound `(⨆ n, β n) + 1`.
- [Tow20, §13] -/
lemma allω {β : ℕ → Ordinal.{0}}
    (φ : ArithmeticSemiformula ℕ 1) (h : ∀ n, Provable (β n) c (insert (φ/[nm n]) Γ)) :
    Provable ((⨆ n, β n) + 1) c (insert (∀⁰ φ) Γ) := by
  choose d ho hcr using h
  have hsup : (⨆ n, ordinalBound (d n)) ≤ ⨆ n, β n :=
    Ordinal.iSup_le fun n => (ho n).trans (Ordinal.le_iSup β n)
  refine ⟨Derivation.allω φ d, ?_, ?_⟩
  · simp only [Derivation.ordinalBound]; exact add_le_add hsup le_rfl
  · simp only [Derivation.cutRank]; exact iSup_le hcr

/-- **Contraction is free** (the payoff of set sequents): a duplicate insert collapses.
- [Tow20, §13] -/
@[grind →]
lemma contr (φ)
    (h : Provable α c (insert φ (insert φ Γ))) : Provable α c (insert φ Γ) := by
  simpa [Finset.insert_idem] using h

/-- **Predicate-level cut.** From `insert φ Γ` and `insert (∼φ) Γ` at cut rank `≤ c` with
`complexity φ < c`, conclude `Γ` at the same cut rank.
- [Tow20, §13] -/
@[grind →]
lemma cut (χ)
    (hc : (χ.complexity + 1 : ℕ∞) ≤ (c : ℕ∞))
    (h₁ : Provable α c (insert χ Γ)) (h₂ : Provable β c (insert (∼χ) Γ)) :
    Provable (max α β + 1) c Γ := by
  rcases h₁ with ⟨d₁, ho₁, hcr₁⟩
  rcases h₂ with ⟨d₂, ho₂, hcr₂⟩
  refine ⟨Derivation.cut χ d₁ d₂, ?_, ?_⟩
  · simp only [Derivation.ordinalBound]; exact add_le_add (max_le_max ho₁ ho₂) le_rfl
  · simp only [Derivation.cutRank]; exact max_le hc (max_le hcr₁ hcr₂)

end Provable

end GoodsteinPA.ZinftyF
