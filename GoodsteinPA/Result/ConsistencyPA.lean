/-
# `𝗣𝗔` consistency as an integration check on `Zinfty.Embedding` / `Zinfty.Cut`

Not new content: `Entailment.consistent_of_model` already gives `𝗣𝗔`'s consistency from
`ℕ ⊧ₘ* 𝗣𝗔`. This chains `of_derivation2_cutFree` and `remove_falsum` end-to-end instead, as a
sanity check that the two connect correctly.
-/
module

public import GoodsteinPA.Zinfty.Embedding

@[expose] public section

namespace GoodsteinPA.Zinfty

open LO LO.FirstOrder LO.FirstOrder.ArithmeticTerm

/-- A true formula in `insert φ Γ` is either `φ` itself or a true formula already in `Γ`. -/
private lemma exists_litTrue_insert {φ : ArithmeticFormula ℕ} {Γ : Finset (ArithmeticFormula ℕ)}
  (h : ∃ χ ∈ insert φ Γ, LitTrue χ) : LitTrue φ ∨ ∃ χ ∈ Γ, LitTrue χ :=
  (Finset.exists_mem_insert φ Γ LitTrue).mp h

/-- **Soundness of `Z_∞`.** Every derivation's conclusion sequent contains a true closed formula. -/
theorem Derivation.sound (D : Derivation Γ) : ∃ φ ∈ Γ, LitTrue φ := by
  induction D with
  | axL r v hp hn =>
    rcases litTrue_or_neg (Semiformula.rel r v) with h | h;
    · exact ⟨_, hp, h⟩;
    · exact ⟨_, hn, by simpa [signedLit] using h⟩;
  | axTrue b r v htrue hmem => exact ⟨_, hmem, htrue⟩;
  | verumR h => exact ⟨_, h, litTrue_verum⟩;
  | weak D h ih => obtain ⟨φ, hφ, ht⟩ := ih; exact ⟨φ, h hφ, ht⟩;
  | andI φ ψ D₁ D₂ ih₁ ih₂ =>
    rcases exists_litTrue_insert ih₁ with hφ | ⟨χ, hχ, ht⟩;
    · rcases exists_litTrue_insert ih₂ with hψ | ⟨χ, hχ, ht⟩;
      · exact ⟨_, Finset.mem_insert_self _ _, iff_litTrue_and.mpr ⟨hφ, hψ⟩⟩;
      · exact ⟨_, Finset.mem_insert_of_mem hχ, ht⟩;
    · exact ⟨_, Finset.mem_insert_of_mem hχ, ht⟩;
  | orI φ ψ D ih =>
    rcases exists_litTrue_insert ih with hφ | ⟨χ, hχ, ht⟩;
    · exact ⟨_, Finset.mem_insert_self _ _, iff_litTrue_or.mpr (Or.inl hφ)⟩;
    · rcases exists_litTrue_insert ⟨χ, hχ, ht⟩ with hψ | ⟨χ', hχ', ht'⟩;
      · exact ⟨_, Finset.mem_insert_self _ _, iff_litTrue_or.mpr (Or.inr hψ)⟩;
      · exact ⟨_, Finset.mem_insert_of_mem hχ', ht'⟩;
  | @allω Γ' φₓ Dₓ ih =>
    rcases Classical.em (∃ χ ∈ Γ', LitTrue χ) with h | h;
    · obtain ⟨χ, hχ, ht⟩ := h;
      exact ⟨_, Finset.mem_insert_of_mem hχ, ht⟩;
    · refine ⟨_, Finset.mem_insert_self _ _, ?_⟩;
      have key : ∀ n, LitTrue (φₓ/[nm n]) := by
        intro n;
        rcases exists_litTrue_insert (ih n) with ht | h';
        · exact ht;
        · exact absurd h' h;
      simp only [LitTrue, Semiformula.eval_all];
      intro x;
      simpa [LitTrue, Semiformula.eval_substs, valm_nm, Matrix.constant_eq_singleton]
        using key x;
  | exI φₓ n D ih =>
    rcases exists_litTrue_insert ih with ht | ⟨χ, hχ, ht⟩;
    · refine ⟨_, Finset.mem_insert_self _ _, ?_⟩;
      simp only [LitTrue, Semiformula.eval_ex];
      exact ⟨n, by
        simpa [LitTrue, Semiformula.eval_substs, valm_nm, Matrix.constant_eq_singleton] using ht⟩;
    · exact ⟨_, Finset.mem_insert_of_mem hχ, ht⟩;
  | cut φ D₁ D₂ ih₁ ih₂ =>
    rcases litTrue_or_neg φ with hφ | hφ;
    · rcases exists_litTrue_insert ih₂ with h | ⟨χ, hχ, ht⟩;
      · exact absurd hφ ((litTrue_neg φ).mp h);
      · exact ⟨_, hχ, ht⟩;
    · rcases exists_litTrue_insert ih₁ with h | ⟨χ, hχ, ht⟩;
      · exact absurd h ((litTrue_neg φ).mp hφ);
      · exact ⟨_, hχ, ht⟩;

/-- The empty sequent has no `Z_∞` derivation at any bound. -/
theorem Provable.no_provable_empty : ¬Provable α c ∅ := by
  rintro ⟨D, -, -⟩;
  obtain ⟨φ, hφ, -⟩ := D.sound;
  simp at hφ;

theorem consistency_PA : 𝗣𝗔 ⊬ ⊥ := by
  by_contra h;
  obtain ⟨d⟩ := (provable_iff_derivable2 (L := ℒₒᵣ)).mp h;
  obtain ⟨α, hα⟩ := Provable.of_derivation2_cutFree d (fun _ => 0);
  exact Provable.no_provable_empty (Provable.remove_falsum hα);

end GoodsteinPA.Zinfty
