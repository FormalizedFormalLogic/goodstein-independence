/-
# Inversion lemmas for the `Z_∞` calculus

`∨`-, `∧`-, and `∀` (ω-rule) inversion: from a `Z_∞`-derivable sequent containing a compound
formula, recover derivations of the immediate subformula(s) — without raising the ordinal bound
or the cut rank.
- [Tow20, §19.2, §19.3, §19.4]
-/
module

public import GoodsteinPA.Zinfty.Basic

@[expose] public section

namespace GoodsteinPA.ZinftyF

open LO LO.FirstOrder LO.FirstOrder.ArithmeticTerm
open Derivation

variable {α : Ordinal.{0}} {c : ℕ}
         {φ ψ : ArithmeticFormula ℕ} {φₓ : ArithmeticSemiformula ℕ 1}
         {Γ Δ : Finset (ArithmeticFormula ℕ)}

/-- Reorder helper: inverting under an `insert a` lands inside `insert a` of the inversion. -/
private theorem inv_push (a : ArithmeticFormula ℕ) (s : Finset (ArithmeticFormula ℕ)) :
  insert φ (insert ψ ((insert a s).erase (φ ⋎ ψ))) ⊆ insert a (insert φ (insert ψ (s.erase (φ ⋎ ψ)))) := by
  intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto

/-- Reverse reorder helper, valid when the head `a` is not the inverted formula. -/
private theorem inv_pull {a : ArithmeticFormula ℕ} (h : a ≠ (φ ⋎ ψ)) (s : Finset (ArithmeticFormula ℕ)) :
  insert a (insert φ (insert ψ (s.erase (φ ⋎ ψ)))) ⊆ insert φ (insert ψ ((insert a s).erase (φ ⋎ ψ))) := by
  intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
  rcases hx with rfl | hx
  · tauto
  · tauto

/-- Reorder helper (single insert): invert under `insert a`, push it outside. -/
private theorem inv_push_single (b a : ArithmeticFormula ℕ) (e : ArithmeticFormula ℕ) (s : Finset (ArithmeticFormula ℕ)) :
  insert b ((insert a s).erase e) ⊆ insert a (insert b (s.erase e)) := by
  intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto

/-- Reverse reorder helper (single insert), valid when the head `a` is not the erased formula. -/
private theorem inv_pull_single (b : ArithmeticFormula ℕ) {a e : ArithmeticFormula ℕ} (h : a ≠ e) (s : Finset (ArithmeticFormula ℕ)) :
  insert a (insert b (s.erase e)) ⊆ insert b ((insert a s).erase e) := by
  intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
  rcases hx with rfl | hx
  · tauto
  · tauto

/-! ### Head-connective distinctness (shared side conditions)

Reusable `@[simp, grind]` facts that let `grind`/`simp` discharge the `head ≠ principal` side
conditions arising in all three inversions (`orInvAux`, `allInvAux`, `andInvAux`). The cross-shape
cases (different outer connective) follow from constructor injectivity (`simp`); the same-outer-shape
subformula cases (`φ ≠ φ ⋏ ψ`, `φₓ/[nm n] ≠ ∀⁰ φₓ`, …) follow from `complexity`. -/

-- distinctness from a disjunction `φ ⋎ ψ`
@[simp, grind .] lemma rel_ne_or : Semiformula.rel r v ≠ φ ⋎ ψ := by simp
@[simp, grind .] lemma nrel_ne_or : Semiformula.nrel r v ≠ φ ⋎ ψ := by simp
@[simp, grind .] lemma verum_ne_or : ⊤ ≠ φ ⋎ ψ := by simp
@[simp, grind .] lemma and_ne_or : φ' ⋏ ψ' ≠ φ ⋎ ψ := by simp
@[simp, grind .] lemma all_ne_or : ∀⁰ φₓ ≠ φ ⋎ ψ := by simp
@[simp, grind .] lemma exs_ne_or : ∃⁰ φₓ ≠ φ ⋎ ψ := by simp
@[simp, grind .] lemma ne_or_left : φ ≠ φ ⋎ ψ := Semiformula.ne_of_ne_complexity (by simp)
@[simp, grind .] lemma ne_or_right : ψ ≠ φ ⋎ ψ := Semiformula.ne_of_ne_complexity (by simp)

-- distinctness from a conjunction `φ ⋏ ψ`
@[simp, grind .] lemma rel_ne_and : Semiformula.rel r v ≠ φ ⋏ ψ := by simp
@[simp, grind .] lemma nrel_ne_and : Semiformula.nrel r v ≠ φ ⋏ ψ := by simp
@[simp, grind .] lemma verum_ne_and : ⊤ ≠ φ ⋏ ψ := by simp
@[simp, grind .] lemma or_ne_and : φ' ⋎ ψ' ≠ φ ⋏ ψ := by simp
@[simp, grind .] lemma all_ne_and : ∀⁰ φₓ ≠ φ ⋏ ψ := by simp
@[simp, grind .] lemma exs_ne_and : ∃⁰ φₓ ≠ φ ⋏ ψ := by simp
@[simp, grind .] lemma ne_and_left : φ ≠ φ ⋏ ψ := Semiformula.ne_of_ne_complexity (by simp)
@[simp, grind .] lemma ne_and_right : ψ ≠ φ ⋏ ψ := Semiformula.ne_of_ne_complexity (by simp)

-- distinctness from a universal `∀⁰ φₓ`
@[simp, grind .] lemma rel_ne_all : Semiformula.rel r v ≠ ∀⁰ φₓ := by simp
@[simp, grind .] lemma nrel_ne_all : Semiformula.nrel r v ≠ ∀⁰ φₓ := by simp
@[simp, grind .] lemma verum_ne_all : ⊤ ≠ ∀⁰ φₓ := by simp
@[simp, grind .] lemma and_ne_all : φ' ⋏ ψ' ≠ ∀⁰ φₓ := by simp
@[simp, grind .] lemma or_ne_all : φ' ⋎ ψ' ≠ ∀⁰ φₓ := by simp
@[simp, grind .] lemma exs_ne_all : ∃⁰ φ' ≠ ∀⁰ φₓ := by simp
@[simp, grind .] lemma ne_all_inst : φₓ/[nm n] ≠ ∀⁰ φₓ := Semiformula.ne_of_ne_complexity (by simp)

/-! ### Inversion lemmas (Towsner §19.2–19.4)

The genuine syntactic content feeding `cutElimStep`. `orInv` (∨-inversion) is the template:
proved by **structural induction on the derivation** (tractable precisely because set sequents
remove the explicit `contr` rule). The other inversions (∧, ω/∀) follow the same pattern. -/

section InversionOr

namespace Provable

/-- **∨-inversion.** If `φ ⋎ ψ` occurs in a `Z_∞`-derivable sequent, then
replacing it by `φ` and `ψ` is derivable at the *same* ordinal bound and cut rank. Proved by
structural induction on the derivation.
- [Tow20, §19.2] -/
lemma orInvAux (D : Derivation Γ) (hcr : D.cutRank ≤ c) (hmem : (φ ⋎ ψ) ∈ Γ) :
  Provable D.ordinalBound c (insert φ (insert ψ (Γ.erase (φ ⋎ ψ)))) := by
  induction D with
  | @axL Γ k r v hp hn =>
    exact (Provable.axL r v (by grind) (by grind)).mono_cutRank (by omega)
  | @axTrue Γ k b r v htrue hmem =>
    apply (Provable.axTrue b r v htrue ?_).mono_cutRank (by omega);
    . cases b <;> . simp [signedLit, Vee.vee]; grind;
  | @verumR Γ h => exact (Provable.verumR (by grind)).mono_cutRank (by omega)
  | @weak Δ Γ D' hsub ih =>
    by_cases hd : (φ ⋎ ψ) ∈ Δ
    · apply (ih hcr hd).weakening;
      intro χ;
      simp only [Finset.mem_insert, Finset.mem_erase];
      grind;
    · have : Provable D'.ordinalBound c Δ := ⟨D', le_rfl, hcr⟩
      apply this.weakening;
      intro χ;
      simp only [Finset.mem_insert, Finset.mem_erase];
      grind;
  | @andI Γ₀ φ' ψ' Dφ Dψ ihφ ihψ =>
    apply (Provable.andI ?_ ?_).weakening $ inv_pull (by grind) Γ₀;
    . exact ihφ (le_trans (le_max_left _ _) hcr) (by grind) |>.weakening $ inv_push φ' Γ₀;
    . exact ihψ (le_trans (le_max_right _ _) hcr) (by grind) |>.weakening $ inv_push ψ' Γ₀;
  | @orI Γ₀ φ' ψ' D' ih =>
    by_cases hhd : (φ' ⋎ ψ') = (φ ⋎ ψ);
    · obtain ⟨rfl, rfl⟩ := (Semiformula.or_inj _ _ _ _).mp hhd.symm;
      by_cases hd : (φ ⋎ ψ) ∈ Γ₀;
      · have := ih hcr (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hd))
        apply (this.weakening ?_).mono_ordinalBound (le_of_lt (lt_add_of_pos_right _ one_pos));
        . intro χ;
          simp only [Finset.mem_insert, Finset.mem_erase];
          grind;
      · have : Provable D'.ordinalBound c (insert φ (insert ψ Γ₀)) := ⟨D', le_rfl, hcr⟩;
        apply (this.weakening ?_).mono_ordinalBound (le_of_lt (lt_add_of_pos_right _ one_pos));
        . intro χ;
          simp only [Finset.mem_insert, Finset.mem_erase];
          grind;
    · apply (Provable.orI ?_).weakening $ inv_pull hhd Γ₀;
      apply (ih hcr (by grind)).weakening;
      intro χ;
      simp only [Finset.mem_insert, Finset.mem_erase];
      grind;
  | @allω Γ₀ φₓ Dₓ ih =>
    apply (Provable.allω ?_).weakening $ inv_pull ?_ Γ₀;
    . grind;
    . intro n;
      apply ih n (le_trans (le_iSup (fun m => (Dₓ m).cutRank) n) hcr) (by grind) |>.weakening;
      exact inv_push (φₓ/[nm n]) Γ₀;
  | @exI Γ₀ φₓ n Dₓ ih =>
    apply (Provable.exI n ?_).weakening (inv_pull ?_ Γ₀);
    . grind;
    . exact ih hcr (by grind) |>.weakening $ inv_push (φₓ/[nm n]) Γ₀;
  | @cut Γ₀ χ D₁ D₂ ih₁ ih₂ =>
    apply Provable.cut χ;
    . exact (le_max_left _ _).trans hcr
    . apply ih₁ ?_ (by grind) |>.weakening (inv_push χ Γ₀);
      exact (le_max_left D₁.cutRank D₂.cutRank).trans ((le_max_right _ _).trans hcr);
    . apply ih₂ ?_ (by grind) |>.weakening (inv_push (∼χ) Γ₀);
      exact (le_max_right D₁.cutRank D₂.cutRank).trans ((le_max_right _ _).trans hcr);

/-- **∨-inversion at a relaxed bound** (the form used downstream).
- [Tow20, §19.2] -/
@[grind →]
lemma orInv (hmem : (φ ⋎ ψ) ∈ Γ) (h : Provable α c Γ) : Provable α c (insert φ (insert ψ (Γ.erase (φ ⋎ ψ)))) := by
  obtain ⟨D, ho, hcr⟩ := h;
  exact (orInvAux D hcr hmem).mono_ordinalBound ho

end Provable

end InversionOr


/-! ### ω-rule inversion (Towsner §19.4)

The distinctive infinitary inversion: inverting a `∀⁰ χ` yields, for *each* numeral `n`, the
instance `χ/[nm n]`. The principal case `allω` supplies exactly the right instance from its
ω-indexed premise family. Same structural-induction template as `orInvAux`. -/

section InversionAll

namespace Provable

/-- **ω/∀-inversion.** If `∀⁰ χ` occurs in a `Z_∞`-derivable sequent, then for
every numeral `n` the instance `χ/[nm n]` is derivable at the *same* ordinal bound and cut rank.
Proved by structural induction on the derivation (`n` fixed).
- [Tow20, §19.4] -/
lemma allInvAux (n : ℕ) (D : Derivation Γ) (hcr : D.cutRank ≤ c) (hmem : (∀⁰ φₓ) ∈ Γ) :
  Provable D.ordinalBound c (insert (φₓ/[nm n]) (Γ.erase (∀⁰ φₓ))) := by
  induction D with
  | @axL Γ k r v hp hn =>
    exact (Provable.axL r v (by grind) (by grind)).mono_cutRank (by omega)
  | @axTrue Γ k b r v htrue hmem =>
    apply (Provable.axTrue b r v htrue ?_).mono_cutRank (by omega);
    . cases b <;> . simp [signedLit]; grind;
  | @verumR Γ h => exact (Provable.verumR (by grind)).mono_cutRank (by omega)
  | @weak Δ Γ D' hsub ih =>
    by_cases hd : (∀⁰ φₓ) ∈ Δ
    · apply (ih hcr hd).weakening;
      intro χ;
      simp only [Finset.mem_insert, Finset.mem_erase];
      grind;
    · have : Provable D'.ordinalBound c Δ := ⟨D', le_rfl, hcr⟩
      apply this.weakening;
      intro χ;
      simp only [Finset.mem_insert, Finset.mem_erase];
      grind;
  | @andI Γ₀ φ' ψ' Dφ Dψ ihφ ihψ =>
    apply (Provable.andI ?_ ?_).weakening $ inv_pull_single _ (by grind) Γ₀;
    . exact ihφ (le_trans (le_max_left _ _) hcr) (by grind) |>.weakening $ inv_push_single _ φ' _ Γ₀;
    . exact ihψ (le_trans (le_max_right _ _) hcr) (by grind) |>.weakening $ inv_push_single _ ψ' _ Γ₀;
  | @orI Γ₀ φ' ψ' D' ih =>
    apply (Provable.orI ?_).weakening $ inv_pull_single _ (by grind) Γ₀;
    apply (ih hcr (by grind)).weakening;
    intro χ;
    simp only [Finset.mem_insert, Finset.mem_erase];
    grind;
  | @allω Γ₀ χ' Dₓ ih =>
    by_cases hhd : (∀⁰ χ') = (∀⁰ φₓ);
    · obtain rfl := (Semiformula.all_inj _ _).mp hhd;
      have hcrn : (Dₓ n).cutRank ≤ c := le_trans (le_iSup (fun m => (Dₓ m).cutRank) n) hcr;
      have hbound : (Dₓ n).ordinalBound ≤ (⨆ m, (Dₓ m).ordinalBound) + 1 :=
        le_trans (Ordinal.le_iSup (fun m => (Dₓ m).ordinalBound) n) (le_of_lt (lt_add_of_pos_right _ one_pos));
      by_cases hd : (∀⁰ χ') ∈ Γ₀;
      · apply ((ih n hcrn (Finset.mem_insert_of_mem hd)).weakening ?_).mono_ordinalBound hbound;
        intro χ;
        simp only [Finset.mem_insert, Finset.mem_erase];
        grind;
      · have base : Provable (Dₓ n).ordinalBound c (insert (χ'/[nm n]) Γ₀) := ⟨Dₓ n, le_rfl, hcrn⟩;
        apply (base.weakening ?_).mono_ordinalBound hbound;
        intro χ;
        simp only [Finset.mem_insert, Finset.mem_erase];
        grind;
    · apply (Provable.allω ?_).weakening $ inv_pull_single _ hhd Γ₀;
      intro m;
      exact (ih m (le_trans (le_iSup (fun j => (Dₓ j).cutRank) m) hcr) (by grind)).weakening
        (inv_push_single _ (χ'/[nm m]) _ Γ₀);
  | @exI Γ₀ χ' m Dₓ ih =>
    apply (Provable.exI m ?_).weakening (inv_pull_single _ (by grind) Γ₀);
    exact (ih hcr (by grind)).weakening (inv_push_single _ (χ'/[nm m]) _ Γ₀);
  | @cut Γ₀ ξ D₁ D₂ ih₁ ih₂ =>
    apply Provable.cut ξ;
    . exact (le_max_left _ _).trans hcr
    . apply ih₁ ?_ (by grind) |>.weakening (inv_push_single _ ξ _ Γ₀);
      exact (le_max_left D₁.cutRank D₂.cutRank).trans ((le_max_right _ _).trans hcr);
    . apply ih₂ ?_ (by grind) |>.weakening (inv_push_single _ (∼ξ) _ Γ₀);
      exact (le_max_right D₁.cutRank D₂.cutRank).trans ((le_max_right _ _).trans hcr);

/-- **ω-inversion at a relaxed bound** (the form used downstream).
- [Tow20, §19.4] -/
lemma allInv (hmem : (∀⁰ φₓ) ∈ Γ) (n : ℕ) (h : Provable α c Γ) : Provable α c (insert (φₓ/[nm n]) (Γ.erase (∀⁰ φₓ))) := by
  obtain ⟨D, ho, hcr⟩ := h;
  exact (allInvAux n D hcr hmem).mono_ordinalBound ho

end Provable

end InversionAll



/-! ### ∧-inversion (Towsner §19.3)

Inverting `φ ⋏ ψ` yields *both* conjuncts (two conclusions). Standard FO inversion; same template
as `orInvAux`, principal case `andI` supplies the two conjunct premises. We prove the conjunction
in one induction (`andInvAux`) and expose each side as a corollary. -/
section InversionAnd

namespace Provable

/-- **∧-inversion.** If `φ ⋏ ψ` occurs in a `Z_∞`-derivable sequent, then both
`φ` and `ψ` (with the conjunction erased) are derivable at the same ordinal bound and cut rank.
- [Tow20, §19.3] -/
lemma andInvAux (D : Derivation Γ) (hcr : D.cutRank ≤ c) (hmem : (φ ⋏ ψ) ∈ Γ) :
    Provable D.ordinalBound c (insert φ (Γ.erase (φ ⋏ ψ))) ∧
    Provable D.ordinalBound c (insert ψ (Γ.erase (φ ⋏ ψ))) := by
  induction D with
  | @axL Γ k r v hp hn =>
    exact ⟨(Provable.axL r v (by grind) (by grind)).mono_cutRank (by omega),
           (Provable.axL r v (by grind) (by grind)).mono_cutRank (by omega)⟩
  | @axTrue Γ k b r v htrue hmem =>
    refine ⟨(Provable.axTrue b r v htrue ?_).mono_cutRank (by omega),
            (Provable.axTrue b r v htrue ?_).mono_cutRank (by omega)⟩;
    . cases b <;> . simp [signedLit]; grind;
    . cases b <;> . simp [signedLit]; grind;
  | @verumR Γ h =>
    exact ⟨(Provable.verumR (by grind)).mono_cutRank (by omega),
           (Provable.verumR (by grind)).mono_cutRank (by omega)⟩
  | @weak Δ Γ D' hsub ih =>
    by_cases hd : (φ ⋏ ψ) ∈ Δ
    · refine ⟨(ih hcr hd).1.weakening ?_, (ih hcr hd).2.weakening ?_⟩ <;>
        (intro χ; simp only [Finset.mem_insert, Finset.mem_erase]; grind)
    · have base : Provable D'.ordinalBound c Δ := ⟨D', le_rfl, hcr⟩
      refine ⟨base.weakening ?_, base.weakening ?_⟩ <;>
        (intro χ; simp only [Finset.mem_insert, Finset.mem_erase]; grind)
  | @andI Γ₀ φ' ψ' Dφ Dψ ihφ ihψ =>
    have hcrφ : Dφ.cutRank ≤ c := le_trans (le_max_left _ _) hcr
    have hcrψ : Dψ.cutRank ≤ c := le_trans (le_max_right _ _) hcr
    by_cases hhd : (φ' ⋏ ψ') = (φ ⋏ ψ)
    · obtain ⟨rfl, rfl⟩ := (Semiformula.and_inj _ _ _ _).mp hhd.symm
      have hbφ : Dφ.ordinalBound ≤ max Dφ.ordinalBound Dψ.ordinalBound + 1 :=
        le_trans (le_max_left _ _) (le_of_lt (lt_add_of_pos_right _ one_pos))
      have hbψ : Dψ.ordinalBound ≤ max Dφ.ordinalBound Dψ.ordinalBound + 1 :=
        le_trans (le_max_right _ _) (le_of_lt (lt_add_of_pos_right _ one_pos))
      refine ⟨?_, ?_⟩
      · by_cases hd : (φ ⋏ ψ) ∈ Γ₀
        · apply ((ihφ hcrφ (Finset.mem_insert_of_mem hd)).1.weakening ?_).mono_ordinalBound hbφ;
          intro χ; simp only [Finset.mem_insert, Finset.mem_erase]; grind
        · have base : Provable Dφ.ordinalBound c (insert φ Γ₀) := ⟨Dφ, le_rfl, hcrφ⟩
          apply (base.weakening ?_).mono_ordinalBound hbφ;
          intro χ; simp only [Finset.mem_insert, Finset.mem_erase]; grind
      · by_cases hd : (φ ⋏ ψ) ∈ Γ₀
        · apply ((ihψ hcrψ (Finset.mem_insert_of_mem hd)).2.weakening ?_).mono_ordinalBound hbψ;
          intro χ; simp only [Finset.mem_insert, Finset.mem_erase]; grind
        · have base : Provable Dψ.ordinalBound c (insert ψ Γ₀) := ⟨Dψ, le_rfl, hcrψ⟩
          apply (base.weakening ?_).mono_ordinalBound hbψ;
          intro χ; simp only [Finset.mem_insert, Finset.mem_erase]; grind
    · refine ⟨?_, ?_⟩
      · exact (Provable.andI ((ihφ hcrφ (by grind)).1.weakening (inv_push_single _ φ' _ Γ₀))
                             ((ihψ hcrψ (by grind)).1.weakening (inv_push_single _ ψ' _ Γ₀))).weakening (inv_pull_single _ hhd Γ₀)
      · exact (Provable.andI ((ihφ hcrφ (by grind)).2.weakening (inv_push_single _ φ' _ Γ₀))
                             ((ihψ hcrψ (by grind)).2.weakening (inv_push_single _ ψ' _ Γ₀))).weakening (inv_pull_single _ hhd Γ₀)
  | @orI Γ₀ φ' ψ' D' ih =>
    refine ⟨?_, ?_⟩
    · apply (Provable.orI ?_).weakening $ inv_pull_single _ (by grind) Γ₀;
      apply (ih hcr (by grind)).1.weakening;
      intro χ; simp only [Finset.mem_insert, Finset.mem_erase]; grind
    · apply (Provable.orI ?_).weakening $ inv_pull_single _ (by grind) Γ₀;
      apply (ih hcr (by grind)).2.weakening;
      intro χ; simp only [Finset.mem_insert, Finset.mem_erase]; grind
  | @allω Γ₀ χ' Dₓ ih =>
    refine ⟨?_, ?_⟩
    · apply (Provable.allω ?_).weakening $ inv_pull_single _ (by grind) Γ₀;
      intro m;
      exact (ih m (le_trans (le_iSup (fun j => (Dₓ j).cutRank) m) hcr) (by grind)).1.weakening
        (inv_push_single _ (χ'/[nm m]) _ Γ₀)
    · apply (Provable.allω ?_).weakening $ inv_pull_single _ (by grind) Γ₀;
      intro m;
      exact (ih m (le_trans (le_iSup (fun j => (Dₓ j).cutRank) m) hcr) (by grind)).2.weakening
        (inv_push_single _ (χ'/[nm m]) _ Γ₀)
  | @exI Γ₀ χ' m Dₓ ih =>
    refine ⟨?_, ?_⟩
    · apply (Provable.exI m ?_).weakening (inv_pull_single _ (by grind) Γ₀);
      exact (ih hcr (by grind)).1.weakening (inv_push_single _ (χ'/[nm m]) _ Γ₀)
    · apply (Provable.exI m ?_).weakening (inv_pull_single _ (by grind) Γ₀);
      exact (ih hcr (by grind)).2.weakening (inv_push_single _ (χ'/[nm m]) _ Γ₀)
  | @cut Γ₀ ξ D₁ D₂ ih₁ ih₂ =>
    refine ⟨?_, ?_⟩
    · apply Provable.cut ξ;
      . exact (le_max_left _ _).trans hcr
      . apply (ih₁ ?_ (by grind)).1.weakening (inv_push_single _ ξ _ Γ₀);
        exact (le_max_left D₁.cutRank D₂.cutRank).trans ((le_max_right _ _).trans hcr)
      . apply (ih₂ ?_ (by grind)).1.weakening (inv_push_single _ (∼ξ) _ Γ₀);
        exact (le_max_right D₁.cutRank D₂.cutRank).trans ((le_max_right _ _).trans hcr)
    · apply Provable.cut ξ;
      . exact (le_max_left _ _).trans hcr
      . apply (ih₁ ?_ (by grind)).2.weakening (inv_push_single _ ξ _ Γ₀);
        exact (le_max_left D₁.cutRank D₂.cutRank).trans ((le_max_right _ _).trans hcr)
      . apply (ih₂ ?_ (by grind)).2.weakening (inv_push_single _ (∼ξ) _ Γ₀);
        exact (le_max_right D₁.cutRank D₂.cutRank).trans ((le_max_right _ _).trans hcr)

/-- **∧-inversion, left conjunct, relaxed bound.**
- [Tow20, §19.3] -/
@[grind →]
lemma andInvL (hmem : (φ ⋏ ψ) ∈ Γ) (h : Provable α c Γ) : Provable α c (insert φ (Γ.erase (φ ⋏ ψ))) := by
  obtain ⟨D, ho, hcr⟩ := h;
  exact (andInvAux D hcr hmem).1.mono_ordinalBound ho

/-- **∧-inversion, right conjunct, relaxed bound.**
- [Tow20, §19.3] -/
@[grind →]
lemma andInvR (hmem : (φ ⋏ ψ) ∈ Γ) (h : Provable α c Γ) : Provable α c (insert ψ (Γ.erase (φ ⋏ ψ))) := by
  obtain ⟨D, ho, hcr⟩ := h;
  exact (andInvAux D hcr hmem).2.mono_ordinalBound ho

end Provable

end InversionAnd

end GoodsteinPA.ZinftyF
