/-
# Inversion lemmas for the `Z_∞` calculus

`∨`-, `∧`-, and `∀` (ω-rule) inversion: from a `Z_∞`-derivable sequent containing a compound
formula, recover derivations of the immediate subformula(s) — without raising the ordinal bound
or the cut rank.
- [Tow20, §19.2, §19.3, §19.4]
-/
module

public import GoodsteinPA.Zinfty

@[expose] public section

namespace GoodsteinPA.ZinftyF

open LO LO.FirstOrder
open Derivation

/-! ### Inversion lemmas (Towsner §19.2–19.4)

The genuine syntactic content feeding `cutElimStep`. `orInv` (∨-inversion) is the template:
proved by **structural induction on the derivation** (tractable precisely because set sequents
remove the explicit `contr` rule). The other inversions (∧, ω/∀) follow the same pattern. -/

section Inversion

variable {φ ψ : Formula} {α : Ordinal.{0}} {c : ℕ} {Γ : Finset Formula}

/-- Reorder helper: inverting under an `insert a` lands inside `insert a` of the inversion. -/
private theorem invPush (a : Formula) (s : Finset Formula) :
    insert φ (insert ψ ((insert a s).erase (φ ⋎ ψ)))
      ⊆ insert a (insert φ (insert ψ (s.erase (φ ⋎ ψ)))) := by
  intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto

/-- Reverse reorder helper, valid when the head `a` is not the inverted formula. -/
private theorem invPull {a : Formula} (h : a ≠ (φ ⋎ ψ)) (s : Finset Formula) :
    insert a (insert φ (insert ψ (s.erase (φ ⋎ ψ))))
      ⊆ insert φ (insert ψ ((insert a s).erase (φ ⋎ ψ))) := by
  intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
  rcases hx with rfl | hx
  · tauto
  · tauto

/-- **∨-inversion (Towsner §19.2 analog).** If `φ ⋎ ψ` occurs in a `Z_∞`-derivable sequent, then
replacing it by `φ` and `ψ` is derivable at the *same* ordinal bound and cut rank. Proved by
structural induction on the derivation. -/
lemma orInvAux : ∀ {Γ : Finset Formula} (d : Derivation Γ), cutRank d ≤ (c : ℕ∞) → (φ ⋎ ψ) ∈ Γ →
    Provable (ordinalBound d) c (insert φ (insert ψ (Γ.erase (φ ⋎ ψ)))) := by
  have hφ0 : φ ≠ (φ ⋎ ψ) := Semiformula.ne_or_left φ ψ
  have hψ0 : ψ ≠ (φ ⋎ ψ) := Semiformula.ne_or_right φ ψ
  intro Γ d
  induction d with
  | @axL Γ k r v hp hn =>
    intro _ _
    have hr : Semiformula.rel r v ∈ Γ.erase (φ ⋎ ψ) :=
      Finset.mem_erase.mpr ⟨by intro h; simp [Vee.vee] at h, hp⟩
    have hn' : Semiformula.nrel r v ∈ Γ.erase (φ ⋎ ψ) :=
      Finset.mem_erase.mpr ⟨by intro h; simp [Vee.vee] at h, hn⟩
    simp only [Derivation.ordinalBound]
    exact (Provable.axL r v (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hr))
      (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hn'))).mono le_rfl (Nat.zero_le c)
  | @axTrue Γ k b r v htrue hmem =>
    intro _ _
    have hl : signedLit b r v ∈ Γ.erase (φ ⋎ ψ) :=
      Finset.mem_erase.mpr ⟨by cases b <;> simp [signedLit, Vee.vee], hmem⟩
    simp only [Derivation.ordinalBound]
    exact (Provable.axTrue b r v htrue
      (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hl))).mono le_rfl (Nat.zero_le c)
  | @verumR Γ h =>
    intro _ _
    have ht : (⊤ : Formula) ∈ Γ.erase (φ ⋎ ψ) :=
      Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), h⟩
    simp only [Derivation.ordinalBound]
    exact (Provable.verumR (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem ht))).mono
      le_rfl (Nat.zero_le c)
  | @weak Δ Γ d' hsub ih =>
    intro hcr hmem
    simp only [Derivation.cutRank] at hcr
    simp only [Derivation.ordinalBound]
    by_cases hd : (φ ⋎ ψ) ∈ Δ
    · exact (ih hcr hd).weakening
        (Finset.insert_subset_insert _ (Finset.insert_subset_insert _
          (Finset.erase_subset_erase _ hsub)))
    · have base : Provable (ordinalBound d') c Δ := ⟨d', le_rfl, hcr⟩
      refine base.weakening ?_
      intro x hx
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_erase.mpr ⟨fun e => hd (e ▸ hx), hsub hx⟩))
  | @andI Γ₀ φ' ψ' dφ dψ ihφ ihψ =>
    intro hcr hmem
    simp only [Derivation.cutRank] at hcr
    simp only [Derivation.ordinalBound]
    have hhead : (φ' ⋏ ψ') ≠ (φ ⋎ ψ) := by intro h; simp [Wedge.wedge, Vee.vee] at h
    have hmem0 : (φ ⋎ ψ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
    have hcrφ : cutRank dφ ≤ (c : ℕ∞) := le_trans (le_max_left _ _) hcr
    have hcrψ : cutRank dψ ≤ (c : ℕ∞) := le_trans (le_max_right _ _) hcr
    have Pφ := (ihφ hcrφ (Finset.mem_insert_of_mem hmem0)).weakening (invPush φ' Γ₀)
    have Pψ := (ihψ hcrψ (Finset.mem_insert_of_mem hmem0)).weakening (invPush ψ' Γ₀)
    exact (Provable.andI φ' ψ' Pφ Pψ).weakening (invPull hhead Γ₀)
  | @orI Γ₀ φ' ψ' d' ih =>
    intro hcr hmem
    simp only [Derivation.cutRank] at hcr
    simp only [Derivation.ordinalBound]
    by_cases hhd : (φ' ⋎ ψ') = (φ ⋎ ψ)
    · -- principal: φ' ⋎ ψ' = φ ⋎ ψ
      obtain ⟨rfl, rfl⟩ := (Semiformula.or_inj _ _ _ _).mp hhd.symm
      by_cases hd : (φ ⋎ ψ) ∈ Γ₀
      · have P := ih hcr (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hd))
        refine (P.weakening ?_).mono (le_of_lt (lt_add_of_pos_right _ one_pos)) le_rfl
        intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto
      · have base : Provable (ordinalBound d') c (insert φ (insert ψ Γ₀)) := ⟨d', le_rfl, hcr⟩
        refine (base.weakening ?_).mono (le_of_lt (lt_add_of_pos_right _ one_pos)) le_rfl
        intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
        rcases hx with rfl | rfl | hx
        · tauto
        · tauto
        · exact Or.inr (Or.inr ⟨fun e => hd (e ▸ hx), Or.inr hx⟩)
    · -- side: head ≠ the inverted formula
      have hmem0 : (φ ⋎ ψ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhd e.symm
      have hsub : insert φ (insert ψ ((insert φ' (insert ψ' Γ₀)).erase (φ ⋎ ψ)))
            ⊆ insert φ' (insert ψ' (insert φ (insert ψ (Γ₀.erase (φ ⋎ ψ))))) := by
        intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto
      have P := (ih hcr (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hmem0))).weakening hsub
      exact (Provable.orI φ' ψ' P).weakening (invPull hhd Γ₀)
  | @allω Γ₀ χ d ih =>
    intro hcr hmem
    simp only [Derivation.cutRank] at hcr
    simp only [Derivation.ordinalBound]
    have hhead : (∀⁰ χ) ≠ (φ ⋎ ψ) := by intro h; simp [Vee.vee] at h
    have hmem0 : (φ ⋎ ψ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
    have key : ∀ n, Provable (ordinalBound (d n)) c (insert (χ/[nm n]) (insert φ (insert ψ (Γ₀.erase (φ ⋎ ψ))))) :=
      fun n => (ih n (le_trans (le_iSup (fun m => cutRank (d m)) n) hcr)
        (Finset.mem_insert_of_mem hmem0)).weakening (invPush (χ/[nm n]) Γ₀)
    exact (Provable.allω χ key).weakening (invPull hhead Γ₀)
  | @exI Γ₀ χ n d ih =>
    intro hcr hmem
    simp only [Derivation.cutRank] at hcr
    simp only [Derivation.ordinalBound]
    have hhead : (∃⁰ χ) ≠ (φ ⋎ ψ) := by intro h; simp [Vee.vee] at h
    have hmem0 : (φ ⋎ ψ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
    have P := (ih hcr (Finset.mem_insert_of_mem hmem0)).weakening (invPush (χ/[nm n]) Γ₀)
    exact (Provable.exI χ n P).weakening (invPull hhead Γ₀)
  | @cut Γ₀ χ d₁ d₂ ih₁ ih₂ =>
    intro hcr hmem
    simp only [Derivation.cutRank] at hcr
    simp only [Derivation.ordinalBound]
    have hcχ : (χ.complexity + 1 : ℕ∞) ≤ (c : ℕ∞) := (le_max_left _ _).trans hcr
    have hcr1 : cutRank d₁ ≤ (c : ℕ∞) := (le_max_left (cutRank d₁) (cutRank d₂)).trans ((le_max_right _ _).trans hcr)
    have hcr2 : cutRank d₂ ≤ (c : ℕ∞) := (le_max_right (cutRank d₁) (cutRank d₂)).trans ((le_max_right _ _).trans hcr)
    have P₁ := (ih₁ hcr1 (Finset.mem_insert_of_mem hmem)).weakening (invPush χ Γ₀)
    have P₂ := (ih₂ hcr2 (Finset.mem_insert_of_mem hmem)).weakening (invPush (∼χ) Γ₀)
    exact Provable.cut χ hcχ P₁ P₂

/-- **∨-inversion at a relaxed bound** (the form used downstream). -/
@[grind →]
lemma Provable.orInv (hmem : (φ ⋎ ψ) ∈ Γ)
    (h : Provable α c Γ) : Provable α c (insert φ (insert ψ (Γ.erase (φ ⋎ ψ)))) := by
  rcases h with ⟨d, ho, hcr⟩
  exact (orInvAux d hcr hmem).mono ho le_rfl

end Inversion

/-! ### ω-rule inversion (Towsner §19.4)

The distinctive infinitary inversion: inverting a `∀⁰ χ` yields, for *each* numeral `n`, the
instance `χ/[nm n]`. The principal case `allω` supplies exactly the right instance from its
ω-indexed premise family. Same structural-induction template as `orInvAux`. -/

section InversionAll

variable {χ : SyntacticSemiformula ℒₒᵣ 1} {α : Ordinal.{0}} {c : ℕ} {Γ : Finset Formula}

/-- Reorder helper (single insert): invert under `insert a`, push it outside. -/
private theorem invPush1 (b a : Formula) (e : Formula) (s : Finset Formula) :
    insert b ((insert a s).erase e) ⊆ insert a (insert b (s.erase e)) := by
  intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto

/-- Reverse reorder helper (single insert), valid when the head `a` is not the erased formula. -/
private theorem invPull1 (b : Formula) {a e : Formula} (h : a ≠ e) (s : Finset Formula) :
    insert a (insert b (s.erase e)) ⊆ insert b ((insert a s).erase e) := by
  intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
  rcases hx with rfl | hx
  · tauto
  · tauto

/-- **ω/∀-inversion (Towsner §19.4).** If `∀⁰ χ` occurs in a `Z_∞`-derivable sequent, then for
every numeral `n` the instance `χ/[nm n]` is derivable at the *same* ordinal bound and cut rank.
Proved by structural induction on the derivation (`n` fixed). -/
lemma allInvAux (n : ℕ) : ∀ {Γ : Finset Formula} (d : Derivation Γ), cutRank d ≤ (c : ℕ∞) →
    (∀⁰ χ) ∈ Γ → Provable (ordinalBound d) c (insert (χ/[nm n]) (Γ.erase (∀⁰ χ))) := by
  have hb0 : (χ/[nm n]) ≠ (∀⁰ χ) := Semiformula.ne_of_ne_complexity (by simp)
  intro Γ d
  induction d with
  | @axL Γ k r v hp hn =>
    intro _ _
    have hr : Semiformula.rel r v ∈ Γ.erase (∀⁰ χ) :=
      Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), hp⟩
    have hn' : Semiformula.nrel r v ∈ Γ.erase (∀⁰ χ) :=
      Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), hn⟩
    simp only [Derivation.ordinalBound]
    exact (Provable.axL r v (Finset.mem_insert_of_mem hr)
      (Finset.mem_insert_of_mem hn')).mono le_rfl (Nat.zero_le c)
  | @axTrue Γ k b r v htrue hmem =>
    intro _ _
    have hl : signedLit b r v ∈ Γ.erase (∀⁰ χ) :=
      Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by cases b <;> simp [signedLit]), hmem⟩
    simp only [Derivation.ordinalBound]
    exact (Provable.axTrue b r v htrue (Finset.mem_insert_of_mem hl)).mono le_rfl (Nat.zero_le c)
  | @verumR Γ h =>
    intro _ _
    have ht : (⊤ : Formula) ∈ Γ.erase (∀⁰ χ) :=
      Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), h⟩
    simp only [Derivation.ordinalBound]
    exact (Provable.verumR (Finset.mem_insert_of_mem ht)).mono le_rfl (Nat.zero_le c)
  | @weak Δ Γ d' hsub ih =>
    intro hcr hmem
    simp only [Derivation.cutRank] at hcr
    simp only [Derivation.ordinalBound]
    by_cases hd : (∀⁰ χ) ∈ Δ
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
    have hhead : (φ' ⋏ ψ') ≠ (∀⁰ χ) := by intro h; simp [Wedge.wedge] at h
    have hmem0 : (∀⁰ χ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
    have hcrφ : cutRank dφ ≤ (c : ℕ∞) := le_trans (le_max_left _ _) hcr
    have hcrψ : cutRank dψ ≤ (c : ℕ∞) := le_trans (le_max_right _ _) hcr
    have Pφ := (ihφ hcrφ (Finset.mem_insert_of_mem hmem0)).weakening (invPush1 _ φ' _ Γ₀)
    have Pψ := (ihψ hcrψ (Finset.mem_insert_of_mem hmem0)).weakening (invPush1 _ ψ' _ Γ₀)
    exact (Provable.andI φ' ψ' Pφ Pψ).weakening (invPull1 _ hhead Γ₀)
  | @orI Γ₀ φ' ψ' d' ih =>
    intro hcr hmem
    simp only [Derivation.cutRank] at hcr
    simp only [Derivation.ordinalBound]
    have hhead : (φ' ⋎ ψ') ≠ (∀⁰ χ) := by intro h; simp [Vee.vee] at h
    have hmem0 : (∀⁰ χ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
    have hsub : insert (χ/[nm n]) ((insert φ' (insert ψ' Γ₀)).erase (∀⁰ χ))
          ⊆ insert φ' (insert ψ' (insert (χ/[nm n]) (Γ₀.erase (∀⁰ χ)))) := by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto
    have P := (ih hcr (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hmem0))).weakening hsub
    exact (Provable.orI φ' ψ' P).weakening (invPull1 _ hhead Γ₀)
  | @allω Γ₀ χ' d' ih =>
    intro hcr hmem
    simp only [Derivation.cutRank] at hcr
    simp only [Derivation.ordinalBound]
    by_cases hhd : (∀⁰ χ') = (∀⁰ χ)
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
      have hmem0 : (∀⁰ χ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhd e.symm
      have key : ∀ m, Provable (ordinalBound (d' m)) c
          (insert (χ'/[nm m]) (insert (χ/[nm n]) (Γ₀.erase (∀⁰ χ)))) := fun m =>
        (ih m (le_trans (le_iSup (fun j => cutRank (d' j)) m) hcr)
          (Finset.mem_insert_of_mem hmem0)).weakening (invPush1 _ (χ'/[nm m]) _ Γ₀)
      exact (Provable.allω χ' key).weakening (invPull1 _ hhd Γ₀)
  | @exI Γ₀ χ' n d' ih =>
    intro hcr hmem
    simp only [Derivation.cutRank] at hcr
    simp only [Derivation.ordinalBound]
    have hhead : (∃⁰ χ') ≠ (∀⁰ χ) := by intro h; simp [ExsQuantifier.exs, UnivQuantifier.all] at h
    have hmem0 : (∀⁰ χ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
    have P := (ih hcr (Finset.mem_insert_of_mem hmem0)).weakening (invPush1 _ (χ'/[nm n]) _ Γ₀)
    exact (Provable.exI χ' n P).weakening (invPull1 _ hhead Γ₀)
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

/-- **ω-inversion at a relaxed bound** (the form used downstream). -/
lemma Provable.allInv (hmem : (∀⁰ χ) ∈ Γ) (n : ℕ)
    (h : Provable α c Γ) : Provable α c (insert (χ/[nm n]) (Γ.erase (∀⁰ χ))) := by
  rcases h with ⟨d, ho, hcr⟩
  exact (allInvAux n d hcr hmem).mono ho le_rfl

end InversionAll

/-! ### ∧-inversion (Towsner §19.3)

Inverting `φ ⋏ ψ` yields *both* conjuncts (two conclusions). Standard FO inversion; same template
as `orInvAux`, principal case `andI` supplies the two conjunct premises. We prove the conjunction
in one induction (`andInvAux`) and expose each side as a corollary. -/

section InversionAnd

variable {φ ψ : Formula} {α : Ordinal.{0}} {c : ℕ} {Γ : Finset Formula}

/-- **∧-inversion (Towsner §19.3).** If `φ ⋏ ψ` occurs in a `Z_∞`-derivable sequent, then both
`φ` and `ψ` (with the conjunction erased) are derivable at the same ordinal bound and cut rank. -/
lemma andInvAux : ∀ {Γ : Finset Formula} (d : Derivation Γ), cutRank d ≤ (c : ℕ∞) → (φ ⋏ ψ) ∈ Γ →
    Provable (ordinalBound d) c (insert φ (Γ.erase (φ ⋏ ψ))) ∧
      Provable (ordinalBound d) c (insert ψ (Γ.erase (φ ⋏ ψ))) := by
  have hφ0 : φ ≠ (φ ⋏ ψ) := Semiformula.ne_of_ne_complexity (by simp)
  have hψ0 : ψ ≠ (φ ⋏ ψ) := Semiformula.ne_of_ne_complexity (by simp)
  intro Γ d
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
    have ht : (⊤ : Formula) ∈ Γ.erase (φ ⋏ ψ) :=
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
        exact (Provable.andI φ' ψ' Pφ Pψ).weakening (invPull1 _ hhd Γ₀)
      · have Pφ := ((ihφ hcrφ (Finset.mem_insert_of_mem hmem0)).2).weakening (invPush1 _ φ' _ Γ₀)
        have Pψ := ((ihψ hcrψ (Finset.mem_insert_of_mem hmem0)).2).weakening (invPush1 _ ψ' _ Γ₀)
        exact (Provable.andI φ' ψ' Pφ Pψ).weakening (invPull1 _ hhd Γ₀)
  | @orI Γ₀ φ' ψ' d' ih =>
    intro hcr hmem
    simp only [Derivation.cutRank] at hcr
    simp only [Derivation.ordinalBound]
    have hhead : (φ' ⋎ ψ') ≠ (φ ⋏ ψ) := by intro h; simp [Vee.vee, Wedge.wedge] at h
    have hmem0 : (φ ⋏ ψ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
    have mk : ∀ b : Formula,
        Provable (ordinalBound d') c (insert b ((insert φ' (insert ψ' Γ₀)).erase (φ ⋏ ψ))) →
        Provable (ordinalBound d' + 1) c (insert b ((insert (φ' ⋎ ψ') Γ₀).erase (φ ⋏ ψ))) := by
      intro b P
      have hsub : insert b ((insert φ' (insert ψ' Γ₀)).erase (φ ⋏ ψ))
            ⊆ insert φ' (insert ψ' (insert b (Γ₀.erase (φ ⋏ ψ)))) := by
        intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto
      exact (Provable.orI φ' ψ' (P.weakening hsub)).weakening (invPull1 _ hhead Γ₀)
    exact ⟨mk φ ((ih hcr (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hmem0))).1),
      mk ψ ((ih hcr (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hmem0))).2)⟩
  | @allω Γ₀ χ' d' ih =>
    intro hcr hmem
    simp only [Derivation.cutRank] at hcr
    simp only [Derivation.ordinalBound]
    have hhead : (∀⁰ χ') ≠ (φ ⋏ ψ) := by intro h; simp [Wedge.wedge] at h
    have hmem0 : (φ ⋏ ψ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
    have mk : ∀ b : Formula,
        (∀ m, Provable (ordinalBound (d' m)) c (insert b ((insert (χ'/[nm m]) Γ₀).erase (φ ⋏ ψ)))) →
        Provable ((⨆ m, ordinalBound (d' m)) + 1) c (insert b ((insert (∀⁰ χ') Γ₀).erase (φ ⋏ ψ))) := by
      intro b P
      have key : ∀ m, Provable (ordinalBound (d' m)) c (insert (χ'/[nm m]) (insert b (Γ₀.erase (φ ⋏ ψ)))) :=
        fun m => (P m).weakening (invPush1 _ (χ'/[nm m]) _ Γ₀)
      exact (Provable.allω χ' key).weakening (invPull1 _ hhead Γ₀)
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
      exact (Provable.exI χ' n P).weakening (invPull1 _ hhead Γ₀)
    · have P := ((ih hcr (Finset.mem_insert_of_mem hmem0)).2).weakening (invPush1 _ (χ'/[nm n]) _ Γ₀)
      exact (Provable.exI χ' n P).weakening (invPull1 _ hhead Γ₀)
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

/-- **∧-inversion, left conjunct, relaxed bound.** -/
@[grind →]
lemma Provable.andInvL (hmem : (φ ⋏ ψ) ∈ Γ)
    (h : Provable α c Γ) : Provable α c (insert φ (Γ.erase (φ ⋏ ψ))) := by
  rcases h with ⟨d, ho, hcr⟩
  exact (andInvAux d hcr hmem).1.mono ho le_rfl

/-- **∧-inversion, right conjunct, relaxed bound.** -/
@[grind →]
lemma Provable.andInvR (hmem : (φ ⋏ ψ) ∈ Γ)
    (h : Provable α c Γ) : Provable α c (insert ψ (Γ.erase (φ ⋏ ψ))) := by
  rcases h with ⟨d, ho, hcr⟩
  exact (andInvAux d hcr hmem).2.mono ho le_rfl

end InversionAnd

end GoodsteinPA.ZinftyF
