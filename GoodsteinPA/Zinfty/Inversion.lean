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

variable {α : Ordinal.{0}} {c : ℕ} {Γ : Finset (ArithmeticFormula ℕ)}
         {φ ψ : ArithmeticFormula ℕ} {φₓ : ArithmeticSemiformula ℕ 1}

/-- Reorder helper: inverting under an `insert a` lands inside `insert a` of the inversion. -/
private theorem invPush (a : ArithmeticFormula ℕ) (s : Finset (ArithmeticFormula ℕ)) :
  insert φ (insert ψ ((insert a s).erase (φ ⋎ ψ))) ⊆ insert a (insert φ (insert ψ (s.erase (φ ⋎ ψ)))) := by
  intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto

/-- Reverse reorder helper, valid when the head `a` is not the inverted formula. -/
private theorem invPull {a : ArithmeticFormula ℕ} (h : a ≠ (φ ⋎ ψ)) (s : Finset (ArithmeticFormula ℕ)) :
  insert a (insert φ (insert ψ (s.erase (φ ⋎ ψ)))) ⊆ insert φ (insert ψ ((insert a s).erase (φ ⋎ ψ))) := by
  intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
  rcases hx with rfl | hx
  · tauto
  · tauto

/-- Reorder helper (single insert): invert under `insert a`, push it outside. -/
private theorem invPush1 (b a : ArithmeticFormula ℕ) (e : ArithmeticFormula ℕ) (s : Finset (ArithmeticFormula ℕ)) :
  insert b ((insert a s).erase e) ⊆ insert a (insert b (s.erase e)) := by
  intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto

/-- Reverse reorder helper (single insert), valid when the head `a` is not the erased formula. -/
private theorem invPull1 (b : ArithmeticFormula ℕ) {a e : ArithmeticFormula ℕ} (h : a ≠ e) (s : Finset (ArithmeticFormula ℕ)) :
  insert a (insert b (s.erase e)) ⊆ insert b ((insert a s).erase e) := by
  intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
  rcases hx with rfl | hx
  · tauto
  · tauto

/-! ### Inversion lemmas (Towsner §19.2–19.4)

The genuine syntactic content feeding `cutElimStep`. `orInv` (∨-inversion) is the template:
proved by **structural induction on the derivation** (tractable precisely because set sequents
remove the explicit `contr` rule). The other inversions (∧, ω/∀) follow the same pattern. -/

section InversionOr

@[simp, grind .] lemma ttt : φ ≠ (φ ⋎ ψ) := Semiformula.ne_or_left φ ψ
@[simp, grind .] lemma ttt' : ψ ≠ (φ ⋎ ψ) := Semiformula.ne_or_right φ ψ
@[simp, grind .] lemma tttt : ⊤ ≠ (φ ⋎ ψ) := by simp [Vee.vee]
@[simp, grind .] lemma ww : Semiformula.rel r v ≠ φ ⋎ ψ := by simp [Vee.vee];
@[simp, grind .] lemma wwe : Semiformula.nrel r v ≠ φ ⋎ ψ := by simp [Vee.vee];
@[simp, grind .] lemma aa : ∃⁰ φₓ ≠ φ ⋎ ψ := by simp [Vee.vee];
@[simp, grind .] lemma nn : ∀⁰ φₓ ≠ φ ⋎ ψ := by simp [Vee.vee];
@[simp, grind .] lemma www : φ' ⋏ ψ' ≠ φ ⋎ ψ := by simp [Wedge.wedge, Vee.vee];
namespace Provable

/-- **∨-inversion.** If `φ ⋎ ψ` occurs in a `Z_∞`-derivable sequent, then
replacing it by `φ` and `ψ` is derivable at the *same* ordinal bound and cut rank. Proved by
structural induction on the derivation.
- [Tow20, §19.2] -/
lemma orInvAux (D : Derivation Γ) (hcr : cutRank D ≤ (c : ℕ∞)) (hmem : (φ ⋎ ψ) ∈ Γ) :
  Provable (ordinalBound D) c (insert φ (insert ψ (Γ.erase (φ ⋎ ψ)))) := by
  induction D with
  | @axL Γ k r v hp hn =>
    exact (Provable.axL r v (by grind) (by grind)).mono le_rfl (by omega)
  | @axTrue Γ k b r v htrue hmem =>
    apply (Provable.axTrue b r v htrue ?_).mono le_rfl (by omega);
    . cases b <;> . simp [signedLit, Vee.vee]; grind;
  | @verumR Γ h => exact (Provable.verumR (by grind)).mono le_rfl (by omega)
  | @weak Δ Γ D' hsub ih =>
    by_cases hd : (φ ⋎ ψ) ∈ Δ
    · apply (ih hcr hd).weakening;
      intro χ;
      simp only [Finset.mem_insert, Finset.mem_erase];
      grind;
    · have : Provable (ordinalBound D') c Δ := ⟨D', le_rfl, hcr⟩
      apply this.weakening;
      intro χ;
      simp only [Finset.mem_insert, Finset.mem_erase];
      grind;
  | @andI Γ₀ φ' ψ' Dφ Dψ ihφ ihψ =>
    apply (Provable.andI ?_ ?_).weakening $ invPull (by grind) Γ₀;
    . exact ihφ (le_trans (le_max_left _ _) hcr) (by grind) |>.weakening $ invPush φ' Γ₀;
    . exact ihψ (le_trans (le_max_right _ _) hcr) (by grind) |>.weakening $ invPush ψ' Γ₀;
  | @orI Γ₀ φ' ψ' D' ih =>
    by_cases hhd : (φ' ⋎ ψ') = (φ ⋎ ψ);
    · obtain ⟨rfl, rfl⟩ := (Semiformula.or_inj _ _ _ _).mp hhd.symm;
      by_cases hd : (φ ⋎ ψ) ∈ Γ₀;
      · have := ih hcr (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hd))
        apply (this.weakening ?_).mono (le_of_lt (lt_add_of_pos_right _ one_pos)) le_rfl;
        . intro χ;
          simp only [Finset.mem_insert, Finset.mem_erase];
          grind;
      · have : Provable (ordinalBound D') c (insert φ (insert ψ Γ₀)) := ⟨D', le_rfl, hcr⟩;
        apply (this.weakening ?_).mono (le_of_lt (lt_add_of_pos_right _ one_pos)) le_rfl;
        . intro χ;
          simp only [Finset.mem_insert, Finset.mem_erase];
          grind;
    · apply (Provable.orI ?_).weakening $ invPull hhd Γ₀;
      apply (ih hcr (by grind)).weakening;
      intro χ;
      simp only [Finset.mem_insert, Finset.mem_erase];
      grind;
  | @allω Γ₀ φₓ Dₓ ih =>
    apply (Provable.allω ?_).weakening $ invPull ?_ Γ₀;
    . grind;
    . intro n;
      apply ih n (le_trans (le_iSup (fun m => (Dₓ m).cutRank) n) hcr) (by grind) |>.weakening;
      exact invPush (φₓ/[nm n]) Γ₀;
  | @exI Γ₀ φₓ n Dₓ ih =>
    apply (Provable.exI n ?_).weakening (invPull ?_ Γ₀);
    . grind;
    . exact ih hcr (by grind) |>.weakening $ invPush (φₓ/[nm n]) Γ₀;
  | @cut Γ₀ χ D₁ D₂ ih₁ ih₂ =>
    apply Provable.cut χ;
    . exact (le_max_left _ _).trans hcr
    . apply ih₁ ?_ (by grind) |>.weakening (invPush χ Γ₀);
      exact (le_max_left (cutRank D₁) (cutRank D₂)).trans ((le_max_right _ _).trans hcr);
    . apply ih₂ ?_ (by grind) |>.weakening (invPush (∼χ) Γ₀);
      exact (le_max_right (cutRank D₁) (cutRank D₂)).trans ((le_max_right _ _).trans hcr);

/-- **∨-inversion at a relaxed bound** (the form used downstream).
- [Tow20, §19.2] -/
@[grind →]
lemma orInv (hmem : (φ ⋎ ψ) ∈ Γ) (h : Provable α c Γ) : Provable α c (insert φ (insert ψ (Γ.erase (φ ⋎ ψ)))) := by
  obtain ⟨D, ho, hcr⟩ := h;
  exact (orInvAux D hcr hmem).mono ho le_rfl

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
lemma allInvAux (n : ℕ) (d : Derivation Γ) : cutRank d ≤ (c : ℕ∞) →
  (∀⁰ φₓ) ∈ Γ → Provable (ordinalBound d) c (insert (φₓ/[nm n]) (Γ.erase (∀⁰ φₓ))) := by
  have hb0 : (φₓ/[nm n]) ≠ (∀⁰ φₓ) := Semiformula.ne_of_ne_complexity (by simp)
  induction d with
  | @axL Γ k r v hp hn =>
    intro _ _
    have hr : Semiformula.rel r v ∈ Γ.erase (∀⁰ φₓ) :=
      Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), hp⟩
    have hn' : Semiformula.nrel r v ∈ Γ.erase (∀⁰ φₓ) :=
      Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), hn⟩
    simp only [Derivation.ordinalBound]
    exact (Provable.axL r v (Finset.mem_insert_of_mem hr)
      (Finset.mem_insert_of_mem hn')).mono le_rfl (Nat.zero_le c)
  | @axTrue Γ k b r v htrue hmem =>
    intro _ _
    have hl : signedLit b r v ∈ Γ.erase (∀⁰ φₓ) :=
      Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by cases b <;> simp [signedLit]), hmem⟩
    simp only [Derivation.ordinalBound]
    exact (Provable.axTrue b r v htrue (Finset.mem_insert_of_mem hl)).mono le_rfl (Nat.zero_le c)
  | @verumR Γ h =>
    intro _ _
    have ht : (⊤ : (ArithmeticFormula ℕ)) ∈ Γ.erase (∀⁰ φₓ) :=
      Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), h⟩
    simp only [Derivation.ordinalBound]
    exact (Provable.verumR (Finset.mem_insert_of_mem ht)).mono le_rfl (Nat.zero_le c)
  | @weak Δ Γ d' hsub ih =>
    intro hcr hmem
    simp only [Derivation.cutRank] at hcr
    simp only [Derivation.ordinalBound]
    by_cases hd : (∀⁰ φₓ) ∈ Δ
    · exact (ih hcr hd).weakening
        (Finset.insert_subset_insert _ (Finset.erase_subset_erase _ hsub))
    · have base : Provable (ordinalBound d') c Δ := ⟨d', le_rfl, hcr⟩
      refine base.weakening ?_
      intro x hx
      exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨fun e => hd (e ▸ hx), hsub hx⟩)
  | @andI Γ₀ φ' ψ' dφ dψ ihφ ihψ =>
    intro hcr hmem
    simp only [Derivation.cutRank] at hcr
    simp only [Derivation.ordinalBound]
    have hhead : (φ' ⋏ ψ') ≠ (∀⁰ φₓ) := by intro h; simp [Wedge.wedge] at h
    have hmem0 : (∀⁰ φₓ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
    have hcrφ : cutRank dφ ≤ (c : ℕ∞) := le_trans (le_max_left _ _) hcr
    have hcrψ : cutRank dψ ≤ (c : ℕ∞) := le_trans (le_max_right _ _) hcr
    have Pφ := (ihφ hcrφ (Finset.mem_insert_of_mem hmem0)).weakening (invPush1 _ φ' _ Γ₀)
    have Pψ := (ihψ hcrψ (Finset.mem_insert_of_mem hmem0)).weakening (invPush1 _ ψ' _ Γ₀)
    exact (Provable.andI Pφ Pψ).weakening (invPull1 _ hhead Γ₀)
  | @orI Γ₀ φ' ψ' d' ih =>
    intro hcr hmem
    simp only [Derivation.cutRank] at hcr
    simp only [Derivation.ordinalBound]
    have hhead : (φ' ⋎ ψ') ≠ (∀⁰ φₓ) := by intro h; simp [Vee.vee] at h
    have hmem0 : (∀⁰ φₓ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
    have hsub : insert (φₓ/[nm n]) ((insert φ' (insert ψ' Γ₀)).erase (∀⁰ φₓ))
          ⊆ insert φ' (insert ψ' (insert (φₓ/[nm n]) (Γ₀.erase (∀⁰ φₓ)))) := by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto
    have P := (ih hcr (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hmem0))).weakening hsub
    exact (Provable.orI P).weakening (invPull1 _ hhead Γ₀)
  | @allω Γ₀ χ' d' ih =>
    intro hcr hmem
    simp only [Derivation.cutRank] at hcr
    simp only [Derivation.ordinalBound]
    by_cases hhd : (∀⁰ χ') = (∀⁰ φₓ)
    · -- principal: χ' = χ (obtain rfl eliminates χ, keeping χ')
      obtain rfl := (Semiformula.all_inj _ _).mp hhd
      have hcrn : cutRank (d' n) ≤ (c : ℕ∞) := le_trans (le_iSup (fun m => cutRank (d' m)) n) hcr
      have hbound : ordinalBound (d' n) ≤ (⨆ m, ordinalBound (d' m)) + 1 :=
        le_trans (Ordinal.le_iSup (fun m => ordinalBound (d' m)) n) (le_of_lt (lt_add_of_pos_right _ one_pos))
      by_cases hd : (∀⁰ χ') ∈ Γ₀
      · have P := ih n hcrn (Finset.mem_insert_of_mem hd)
        refine (P.weakening ?_).mono hbound le_rfl
        intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto
      · have base : Provable (ordinalBound (d' n)) c (insert (χ'/[nm n]) Γ₀) := ⟨d' n, le_rfl, hcrn⟩
        refine (base.weakening ?_).mono hbound le_rfl
        intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
        rcases hx with rfl | hx
        · tauto
        · exact Or.inr ⟨fun e => hd (e ▸ hx), Or.inr hx⟩
    · -- side
      have hmem0 : (∀⁰ φₓ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhd e.symm
      have key : ∀ m, Provable (ordinalBound (d' m)) c
          (insert (χ'/[nm m]) (insert (φₓ/[nm n]) (Γ₀.erase (∀⁰ φₓ)))) := fun m =>
        (ih m (le_trans (le_iSup (fun j => cutRank (d' j)) m) hcr)
          (Finset.mem_insert_of_mem hmem0)).weakening (invPush1 _ (χ'/[nm m]) _ Γ₀)
      exact (Provable.allω key).weakening (invPull1 _ hhd Γ₀)
  | @exI Γ₀ χ' n d' ih =>
    intro hcr hmem
    simp only [Derivation.cutRank] at hcr
    simp only [Derivation.ordinalBound]
    have hhead : (∃⁰ χ') ≠ (∀⁰ φₓ) := by intro h; simp [ExsQuantifier.exs, UnivQuantifier.all] at h
    have hmem0 : (∀⁰ φₓ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
    have P := (ih hcr (Finset.mem_insert_of_mem hmem0)).weakening (invPush1 _ (χ'/[nm n]) _ Γ₀)
    exact (Provable.exI n P).weakening (invPull1 _ hhead Γ₀)
  | @cut Γ₀ ξ d₁ d₂ ih₁ ih₂ =>
    intro hcr hmem
    simp only [Derivation.cutRank] at hcr
    simp only [Derivation.ordinalBound]
    have hcξ : (ξ.complexity + 1 : ℕ∞) ≤ (c : ℕ∞) := (le_max_left _ _).trans hcr
    have hcr1 : cutRank d₁ ≤ (c : ℕ∞) := (le_max_left (cutRank d₁) (cutRank d₂)).trans ((le_max_right _ _).trans hcr)
    have hcr2 : cutRank d₂ ≤ (c : ℕ∞) := (le_max_right (cutRank d₁) (cutRank d₂)).trans ((le_max_right _ _).trans hcr)
    have P₁ := (ih₁ hcr1 (Finset.mem_insert_of_mem hmem)).weakening (invPush1 _ ξ _ Γ₀)
    have P₂ := (ih₂ hcr2 (Finset.mem_insert_of_mem hmem)).weakening (invPush1 _ (∼ξ) _ Γ₀)
    exact Provable.cut ξ hcξ P₁ P₂

/-- **ω-inversion at a relaxed bound** (the form used downstream).
- [Tow20, §19.4] -/
lemma allInv (hmem : (∀⁰ φₓ) ∈ Γ) (n : ℕ) (h : Provable α c Γ) : Provable α c (insert (φₓ/[nm n]) (Γ.erase (∀⁰ φₓ))) := by
  obtain ⟨D, ho, hcr⟩ := h;
  exact (allInvAux n D hcr hmem).mono ho le_rfl

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
lemma andInvAux (d : Derivation Γ) : cutRank d ≤ (c : ℕ∞) → (φ ⋏ ψ) ∈ Γ →
    Provable (ordinalBound d) c (insert φ (Γ.erase (φ ⋏ ψ))) ∧
    Provable (ordinalBound d) c (insert ψ (Γ.erase (φ ⋏ ψ))) := by
  have hφ0 : φ ≠ (φ ⋏ ψ) := Semiformula.ne_of_ne_complexity (by simp)
  have hψ0 : ψ ≠ (φ ⋏ ψ) := Semiformula.ne_of_ne_complexity (by simp)
  induction d with
  | @axL Γ k r v hp hn =>
    intro _ _
    have hr : Semiformula.rel r v ∈ Γ.erase (φ ⋏ ψ) :=
      Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), hp⟩
    have hn' : Semiformula.nrel r v ∈ Γ.erase (φ ⋏ ψ) :=
      Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), hn⟩
    simp only [Derivation.ordinalBound]
    exact ⟨(Provable.axL r v (Finset.mem_insert_of_mem hr) (Finset.mem_insert_of_mem hn')).mono
        le_rfl (Nat.zero_le c),
      (Provable.axL r v (Finset.mem_insert_of_mem hr) (Finset.mem_insert_of_mem hn')).mono
        le_rfl (Nat.zero_le c)⟩
  | @axTrue Γ k b r v htrue hmem =>
    intro _ _
    have hl : signedLit b r v ∈ Γ.erase (φ ⋏ ψ) :=
      Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by cases b <;> simp [signedLit]), hmem⟩
    simp only [Derivation.ordinalBound]
    exact ⟨(Provable.axTrue b r v htrue (Finset.mem_insert_of_mem hl)).mono le_rfl (Nat.zero_le c),
      (Provable.axTrue b r v htrue (Finset.mem_insert_of_mem hl)).mono le_rfl (Nat.zero_le c)⟩
  | @verumR Γ h =>
    intro _ _
    have ht : (⊤ : (ArithmeticFormula ℕ)) ∈ Γ.erase (φ ⋏ ψ) :=
      Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), h⟩
    simp only [Derivation.ordinalBound]
    exact ⟨(Provable.verumR (Finset.mem_insert_of_mem ht)).mono le_rfl (Nat.zero_le c),
      (Provable.verumR (Finset.mem_insert_of_mem ht)).mono le_rfl (Nat.zero_le c)⟩
  | @weak Δ Γ d' hsub ih =>
    intro hcr hmem
    simp only [Derivation.cutRank] at hcr
    simp only [Derivation.ordinalBound]
    by_cases hd : (φ ⋏ ψ) ∈ Δ
    · exact ⟨(ih hcr hd).1.weakening
          (Finset.insert_subset_insert _ (Finset.erase_subset_erase _ hsub)),
        (ih hcr hd).2.weakening
          (Finset.insert_subset_insert _ (Finset.erase_subset_erase _ hsub))⟩
    · have base : Provable (ordinalBound d') c Δ := ⟨d', le_rfl, hcr⟩
      have hsub' : Δ ⊆ Δ.erase (φ ⋏ ψ) := fun x hx =>
        Finset.mem_erase.mpr ⟨fun e => hd (e ▸ hx), hx⟩
      have hΔ : Δ ⊆ Γ.erase (φ ⋏ ψ) := fun x hx =>
        Finset.mem_erase.mpr ⟨fun e => hd (e ▸ hx), hsub hx⟩
      exact ⟨base.weakening (fun x hx => Finset.mem_insert_of_mem (hΔ hx)),
        base.weakening (fun x hx => Finset.mem_insert_of_mem (hΔ hx))⟩
  | @andI Γ₀ φ' ψ' dφ dψ ihφ ihψ =>
    intro hcr hmem
    simp only [Derivation.cutRank] at hcr
    simp only [Derivation.ordinalBound]
    have hcrφ : cutRank dφ ≤ (c : ℕ∞) := le_trans (le_max_left _ _) hcr
    have hcrψ : cutRank dψ ≤ (c : ℕ∞) := le_trans (le_max_right _ _) hcr
    have hbφ : ordinalBound dφ ≤ max (ordinalBound dφ) (ordinalBound dψ) + 1 :=
      le_trans (le_max_left _ _) (le_of_lt (lt_add_of_pos_right _ one_pos))
    have hbψ : ordinalBound dψ ≤ max (ordinalBound dφ) (ordinalBound dψ) + 1 :=
      le_trans (le_max_right _ _) (le_of_lt (lt_add_of_pos_right _ one_pos))
    by_cases hhd : (φ' ⋏ ψ') = (φ ⋏ ψ)
    · -- principal: φ' = φ, ψ' = ψ
      obtain ⟨rfl, rfl⟩ := (Semiformula.and_inj _ _ _ _).mp hhd.symm
      have hL : Provable (max (ordinalBound dφ) (ordinalBound dψ) + 1) c (insert φ ((insert (φ ⋏ ψ) Γ₀).erase (φ ⋏ ψ))) := by
        by_cases hd : (φ ⋏ ψ) ∈ Γ₀
        · refine ((ihφ hcrφ (Finset.mem_insert_of_mem hd)).1.weakening ?_).mono hbφ le_rfl
          intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto
        · have base : Provable (ordinalBound dφ) c (insert φ Γ₀) := ⟨dφ, le_rfl, hcrφ⟩
          refine (base.weakening ?_).mono hbφ le_rfl
          intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
          rcases hx with rfl | hx
          · tauto
          · exact Or.inr ⟨fun e => hd (e ▸ hx), Or.inr hx⟩
      have hR : Provable (max (ordinalBound dφ) (ordinalBound dψ) + 1) c (insert ψ ((insert (φ ⋏ ψ) Γ₀).erase (φ ⋏ ψ))) := by
        by_cases hd : (φ ⋏ ψ) ∈ Γ₀
        · refine ((ihψ hcrψ (Finset.mem_insert_of_mem hd)).2.weakening ?_).mono hbψ le_rfl
          intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto
        · have base : Provable (ordinalBound dψ) c (insert ψ Γ₀) := ⟨dψ, le_rfl, hcrψ⟩
          refine (base.weakening ?_).mono hbψ le_rfl
          intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
          rcases hx with rfl | hx
          · tauto
          · exact Or.inr ⟨fun e => hd (e ▸ hx), Or.inr hx⟩
      exact ⟨hL, hR⟩
    · -- side
      have hmem0 : (φ ⋏ ψ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhd e.symm
      refine ⟨?_, ?_⟩
      · have Pφ := ((ihφ hcrφ (Finset.mem_insert_of_mem hmem0)).1).weakening (invPush1 _ φ' _ Γ₀)
        have Pψ := ((ihψ hcrψ (Finset.mem_insert_of_mem hmem0)).1).weakening (invPush1 _ ψ' _ Γ₀)
        exact (Provable.andI Pφ Pψ).weakening (invPull1 _ hhd Γ₀)
      · have Pφ := ((ihφ hcrφ (Finset.mem_insert_of_mem hmem0)).2).weakening (invPush1 _ φ' _ Γ₀)
        have Pψ := ((ihψ hcrψ (Finset.mem_insert_of_mem hmem0)).2).weakening (invPush1 _ ψ' _ Γ₀)
        exact (Provable.andI Pφ Pψ).weakening (invPull1 _ hhd Γ₀)
  | @orI Γ₀ φ' ψ' d' ih =>
    intro hcr hmem
    simp only [Derivation.cutRank] at hcr
    simp only [Derivation.ordinalBound]
    have hhead : (φ' ⋎ ψ') ≠ (φ ⋏ ψ) := by intro h; simp [Vee.vee, Wedge.wedge] at h
    have hmem0 : (φ ⋏ ψ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
    have mk : ∀ b : (ArithmeticFormula ℕ),
        Provable (ordinalBound d') c (insert b ((insert φ' (insert ψ' Γ₀)).erase (φ ⋏ ψ))) →
        Provable (ordinalBound d' + 1) c (insert b ((insert (φ' ⋎ ψ') Γ₀).erase (φ ⋏ ψ))) := by
      intro b P
      have hsub : insert b ((insert φ' (insert ψ' Γ₀)).erase (φ ⋏ ψ))
            ⊆ insert φ' (insert ψ' (insert b (Γ₀.erase (φ ⋏ ψ)))) := by
        intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto
      exact (Provable.orI (P.weakening hsub)).weakening (invPull1 _ hhead Γ₀)
    exact ⟨mk φ ((ih hcr (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hmem0))).1),
      mk ψ ((ih hcr (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hmem0))).2)⟩
  | @allω Γ₀ χ' d' ih =>
    intro hcr hmem
    simp only [Derivation.cutRank] at hcr
    simp only [Derivation.ordinalBound]
    have hhead : (∀⁰ χ') ≠ (φ ⋏ ψ) := by intro h; simp [Wedge.wedge] at h
    have hmem0 : (φ ⋏ ψ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
    have mk : ∀ b : (ArithmeticFormula ℕ),
        (∀ m, Provable (ordinalBound (d' m)) c (insert b ((insert (χ'/[nm m]) Γ₀).erase (φ ⋏ ψ)))) →
        Provable ((⨆ m, ordinalBound (d' m)) + 1) c (insert b ((insert (∀⁰ χ') Γ₀).erase (φ ⋏ ψ))) := by
      intro b P
      have key : ∀ m, Provable (ordinalBound (d' m)) c (insert (χ'/[nm m]) (insert b (Γ₀.erase (φ ⋏ ψ)))) :=
        fun m => (P m).weakening (invPush1 _ (χ'/[nm m]) _ Γ₀)
      exact (Provable.allω key).weakening (invPull1 _ hhead Γ₀)
    refine ⟨mk φ (fun m => ?_), mk ψ (fun m => ?_)⟩
    · exact (ih m (le_trans (le_iSup (fun j => cutRank (d' j)) m) hcr)
        (Finset.mem_insert_of_mem hmem0)).1
    · exact (ih m (le_trans (le_iSup (fun j => cutRank (d' j)) m) hcr)
        (Finset.mem_insert_of_mem hmem0)).2
  | @exI Γ₀ χ' n d' ih =>
    intro hcr hmem
    simp only [Derivation.cutRank] at hcr
    simp only [Derivation.ordinalBound]
    have hhead : (∃⁰ χ') ≠ (φ ⋏ ψ) := by intro h; simp [ExsQuantifier.exs, Wedge.wedge] at h
    have hmem0 : (φ ⋏ ψ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
    refine ⟨?_, ?_⟩
    · have P := ((ih hcr (Finset.mem_insert_of_mem hmem0)).1).weakening (invPush1 _ (χ'/[nm n]) _ Γ₀)
      exact (Provable.exI n P).weakening (invPull1 _ hhead Γ₀)
    · have P := ((ih hcr (Finset.mem_insert_of_mem hmem0)).2).weakening (invPush1 _ (χ'/[nm n]) _ Γ₀)
      exact (Provable.exI n P).weakening (invPull1 _ hhead Γ₀)
  | @cut Γ₀ ξ d₁ d₂ ih₁ ih₂ =>
    intro hcr hmem
    simp only [Derivation.cutRank] at hcr
    simp only [Derivation.ordinalBound]
    have hcξ : (ξ.complexity + 1 : ℕ∞) ≤ (c : ℕ∞) := (le_max_left _ _).trans hcr
    have hcr1 : cutRank d₁ ≤ (c : ℕ∞) := (le_max_left (cutRank d₁) (cutRank d₂)).trans ((le_max_right _ _).trans hcr)
    have hcr2 : cutRank d₂ ≤ (c : ℕ∞) := (le_max_right (cutRank d₁) (cutRank d₂)).trans ((le_max_right _ _).trans hcr)
    refine ⟨?_, ?_⟩
    · have P₁ := ((ih₁ hcr1 (Finset.mem_insert_of_mem hmem)).1).weakening (invPush1 _ ξ _ Γ₀)
      have P₂ := ((ih₂ hcr2 (Finset.mem_insert_of_mem hmem)).1).weakening (invPush1 _ (∼ξ) _ Γ₀)
      exact Provable.cut ξ hcξ P₁ P₂
    · have P₁ := ((ih₁ hcr1 (Finset.mem_insert_of_mem hmem)).2).weakening (invPush1 _ ξ _ Γ₀)
      have P₂ := ((ih₂ hcr2 (Finset.mem_insert_of_mem hmem)).2).weakening (invPush1 _ (∼ξ) _ Γ₀)
      exact Provable.cut ξ hcξ P₁ P₂

/-- **∧-inversion, left conjunct, relaxed bound.**
- [Tow20, §19.3] -/
@[grind →]
lemma andInvL (hmem : (φ ⋏ ψ) ∈ Γ) (h : Provable α c Γ) : Provable α c (insert φ (Γ.erase (φ ⋏ ψ))) := by
  obtain ⟨D, ho, hcr⟩ := h;
  exact (andInvAux D hcr hmem).1.mono ho le_rfl

/-- **∧-inversion, right conjunct, relaxed bound.**
- [Tow20, §19.3] -/
@[grind →]
lemma andInvR (hmem : (φ ⋏ ψ) ∈ Γ) (h : Provable α c Γ) : Provable α c (insert ψ (Γ.erase (φ ⋏ ψ))) := by
  obtain ⟨D, ho, hcr⟩ := h;
  exact (andInvAux D hcr hmem).2.mono ho le_rfl

end Provable

end InversionAnd

end GoodsteinPA.ZinftyF
