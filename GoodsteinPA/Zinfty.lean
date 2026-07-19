/-
# `Z_∞` calculus — provability predicate API

The provability layer over the core definitions in `GoodsteinPA.Zinfty.Basic`: the predicate
`Provable α c Γ` (recording an ordinal bound `α` and cut rank `c` for a `Z_∞`-derivable sequent
`Γ`) and its structural inference API — `mono`/`weakening`/`contr` (contraction free, via set
sequents) and the predicate-level introduction rules matching each `Derivation` constructor
(`axL`, `axTrue`, `verumR`, `andI`, `orI`, `exI`, `allω`, `cut`).

Sequents are finite sets of closed formulas (`Finset (SyntacticFormula ℒₒᵣ)`), matching Towsner's
finite-set `Γ`. Consequently contraction is free (`insert φ (insert φ Γ) = insert φ Γ`
definitionally), so the calculus needs no `contr` rule — which is what keeps the inversion lemmas
tractable, since an explicit height-preserving `contr` rule would force the principal-contraction
case to re-invert a remaining copy of the principal formula, breaking both structural and
ordinal-strong induction. The finitary eigenvariable `all` rule is replaced by the ω-rule `allω`
(one premise per numeral `n`, `Ordinal` height), and `ordinalBound` / `cutRank` are computed
measures by structural recursion on the infinitely-branching tree.

Inversion lemmas (`orInv`, `andInvL/R`, `allInv`) live in `GoodsteinPA.Zinfty.Inversion`; the
Gentzen-style cut-elimination built on top of them (`cutReduceConj/Disj`, `cutReduceAll`,
`atomCut`, `removeFalsum`, `cutElimStep`, `cutElim`) lives in `GoodsteinPA.Zinfty.Cut`.

- [Tow20, §16, §17, §18, §19]
-/
module

public import GoodsteinPA.Zinfty.Basic

@[expose] public section

namespace GoodsteinPA.ZinftyF

open LO LO.FirstOrder

variable {Γ : Finset Formula} {α β : Ordinal.{0}} {c : ℕ}

namespace Derivation

/-- The ω-rule bound strictly dominates each premise bound. -/
lemma o_allω_gt (φ : SyntacticSemiformula ℒₒᵣ 1)
    (d : (n : ℕ) → Derivation (insert (φ/[nm n]) Γ)) (n : ℕ) : ordinalBound (d n) < ordinalBound (allω φ d) := by
  have h : ordinalBound (d n) ≤ ⨆ m, ordinalBound (d m) := Ordinal.le_iSup (fun m => ordinalBound (d m)) n
  calc ordinalBound (d n) ≤ ⨆ m, ordinalBound (d m) := h
    _ < (⨆ m, ordinalBound (d m)) + 1 := lt_add_of_pos_right _ one_pos
    _ = ordinalBound (allω φ d) := by simp only [ordinalBound]

end Derivation

open Derivation

/-- **Bound monotonicity** (Towsner Lemma 16.4): relax either recorded bound. -/
@[grind →]
lemma Provable.mono {c' : ℕ} (hα : α ≤ β) (hc : c ≤ c') {Γ : Finset Formula} :
    Provable α c Γ → Provable β c' Γ := by
  rintro ⟨d, ho, hcr⟩
  exact ⟨d, ho.trans hα, hcr.trans (by exact_mod_cast hc)⟩

/-- **Sequent weakening** (Towsner Lemma 19.1): enlarge the sequent without raising bounds. -/
@[grind →]
lemma Provable.weakening {Δ : Finset Formula} (h : Γ ⊆ Δ) :
    Provable α c Γ → Provable α c Δ := by
  rintro ⟨d, ho, hcr⟩
  exact ⟨Derivation.weak d h, by simpa [Derivation.ordinalBound] using ho, by simpa [Derivation.cutRank] using hcr⟩

/-- Provability respects set equality of sequents. -/
lemma Provable.cast {Δ : Finset Formula} (e : Γ = Δ) :
    Provable α c Γ → Provable α c Δ := fun h => e ▸ h

/-- Identity axiom: `rel r v` and `nrel r v` together close at bound `0`, cut rank `0`. -/
@[grind →]
lemma Provable.axL {k} (r : (ℒₒᵣ).Rel k) (v)
    (hp : Semiformula.rel r v ∈ Γ) (hn : Semiformula.nrel r v ∈ Γ) : Provable 0 0 Γ :=
  ⟨Derivation.axL r v hp hn, by simp [Derivation.ordinalBound], by simp [Derivation.cutRank]⟩

/-- **Atomic-truth axiom** (the ω-logic leaf): a true closed literal closes any sequent containing
it, at bound `0`, cut rank `0`. -/
@[grind →]
lemma Provable.axTrue {k} (b : Bool) (r : (ℒₒᵣ).Rel k) (v)
    (htrue : LitTrue (signedLit b r v)) (hmem : signedLit b r v ∈ Γ) : Provable 0 0 Γ :=
  ⟨Derivation.axTrue b r v htrue hmem, by simp [Derivation.ordinalBound], by simp [Derivation.cutRank]⟩

/-- `⊤` closes a sequent at bound `0`, cut rank `0`. -/
@[grind →]
lemma Provable.verumR (h : (⊤ : Formula) ∈ Γ) : Provable 0 0 Γ :=
  ⟨Derivation.verumR h, by simp [Derivation.ordinalBound], by simp [Derivation.cutRank]⟩

/-- Predicate-level `∧`-introduction. -/
@[grind →]
lemma Provable.andI (φ ψ : Formula)
    (hφ : Provable α c (insert φ Γ)) (hψ : Provable β c (insert ψ Γ)) :
    Provable (max α β + 1) c (insert (φ ⋏ ψ) Γ) := by
  rcases hφ with ⟨dφ, hoφ, hcφ⟩
  rcases hψ with ⟨dψ, hoψ, hcψ⟩
  refine ⟨Derivation.andI φ ψ dφ dψ, ?_, ?_⟩
  · simp only [Derivation.ordinalBound]; exact add_le_add (max_le_max hoφ hoψ) le_rfl
  · simp only [Derivation.cutRank]; exact max_le hcφ hcψ

/-- Predicate-level `∨`-introduction. -/
@[grind →]
lemma Provable.orI (φ ψ : Formula)
    (h : Provable α c (insert φ (insert ψ Γ))) : Provable (α + 1) c (insert (φ ⋎ ψ) Γ) := by
  rcases h with ⟨d, ho, hcr⟩
  exact ⟨Derivation.orI φ ψ d, by simpa [Derivation.ordinalBound] using add_le_add_right ho 1,
    by simpa [Derivation.cutRank] using hcr⟩

/-- Predicate-level `∃`-introduction (witness rule). The witness is a **numeral** `nm n`: in the
arithmetic term model every closed term denotes a numeral, and numeral witnesses are what the
ω-rule inversion (`allInv`) produces, so the ∀/∃ cut-reduction (§19.6) can match the witness
against the inverted ∀-family. -/
@[grind →]
lemma Provable.exI (φ : SyntacticSemiformula ℒₒᵣ 1)
    (n : ℕ) (h : Provable α c (insert (φ/[nm n]) Γ)) :
    Provable (α + 1) c (insert (∃⁰ φ) Γ) := by
  rcases h with ⟨d, ho, hcr⟩
  exact ⟨Derivation.exI φ n d, by simpa [Derivation.ordinalBound] using add_le_add_right ho 1,
    by simpa [Derivation.cutRank] using hcr⟩

/-- **Predicate-level ω-rule.** From a uniform-cut-rank family of premises with ordinal bounds
`β n`, conclude `∀` at bound `(⨆ n, β n) + 1`. -/
lemma Provable.allω {β : ℕ → Ordinal.{0}}
    (φ : SyntacticSemiformula ℒₒᵣ 1) (h : ∀ n, Provable (β n) c (insert (φ/[nm n]) Γ)) :
    Provable ((⨆ n, β n) + 1) c (insert (∀⁰ φ) Γ) := by
  choose d ho hcr using h
  have hsup : (⨆ n, ordinalBound (d n)) ≤ ⨆ n, β n :=
    Ordinal.iSup_le fun n => (ho n).trans (Ordinal.le_iSup β n)
  refine ⟨Derivation.allω φ d, ?_, ?_⟩
  · simp only [Derivation.ordinalBound]; exact add_le_add hsup le_rfl
  · simp only [Derivation.cutRank]; exact iSup_le hcr

/-- **Contraction is free** (the payoff of set sequents): a duplicate insert collapses. -/
@[grind →]
lemma Provable.contr (φ : Formula)
    (h : Provable α c (insert φ (insert φ Γ))) : Provable α c (insert φ Γ) := by
  simpa [Finset.insert_idem] using h

/-- **Predicate-level cut.** From `insert φ Γ` and `insert (∼φ) Γ` at cut rank `≤ c` with
`complexity φ < c`, conclude `Γ` at the same cut rank. -/
@[grind →]
lemma Provable.cut (χ : Formula)
    (hc : (χ.complexity + 1 : ℕ∞) ≤ (c : ℕ∞))
    (h₁ : Provable α c (insert χ Γ)) (h₂ : Provable β c (insert (∼χ) Γ)) :
    Provable (max α β + 1) c Γ := by
  rcases h₁ with ⟨d₁, ho₁, hcr₁⟩
  rcases h₂ with ⟨d₂, ho₂, hcr₂⟩
  refine ⟨Derivation.cut χ d₁ d₂, ?_, ?_⟩
  · simp only [Derivation.ordinalBound]; exact add_le_add (max_le_max ho₁ ho₂) le_rfl
  · simp only [Derivation.cutRank]; exact max_le hc (max_le hcr₁ hcr₂)

end GoodsteinPA.ZinftyF
