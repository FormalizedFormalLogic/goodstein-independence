module

public import GoodsteinPA.OperatorZinfty.Basic

@[expose] public section

namespace GoodsteinPA.OperatorZinfty

open LO LO.FirstOrder ONote

namespace Provable

private lemma invPush (A b : ArithmeticFormula ℕ) (s : Finset (ArithmeticFormula ℕ)) {φ ψ} :
    insert φ (insert ψ ((insert b s).erase A)) ⊆ insert b (insert φ (insert ψ (s.erase A))) := by
  intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto

private lemma invPull (A : ArithmeticFormula ℕ) {b} (h : b ≠ A) (s : Finset (ArithmeticFormula ℕ)) {φ ψ} :
    insert b (insert φ (insert ψ (s.erase A))) ⊆ insert φ (insert ψ ((insert b s).erase A)) := by
  intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
  rcases hx with rfl | rfl | rfl | hx
  · exact Or.inr (Or.inr ⟨h, Or.inl rfl⟩)
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr ⟨hx.1, Or.inr hx.2⟩)

private lemma invPush2 (A b₁ b₂ : ArithmeticFormula ℕ) (s : Finset (ArithmeticFormula ℕ)) {φ ψ} :
    insert φ (insert ψ ((insert b₁ (insert b₂ s)).erase A))
      ⊆ insert b₁ (insert b₂ (insert φ (insert ψ (s.erase A)))) := by
  intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto

private lemma princOrSub {A} (s : Finset (ArithmeticFormula ℕ)) {φ ψ} :
    insert φ (insert ψ ((insert φ (insert ψ s)).erase A)) ⊆ insert φ (insert ψ (s.erase A)) := by
  intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto

variable {α e : ONote} {k d c : ℕ} {Γ : Finset (ArithmeticFormula ℕ)} {φ ψ}

/-- **∨-inversion.** Replace `φ ⋎ ψ` by `φ`, `ψ`, same `(α,k,d,c)`. -/
lemma orInv (dd : Provable α e k d c Γ) (hmem0 : (φ ⋎ ψ) ∈ Γ) :
  Provable α e k d c (insert φ (insert ψ (Γ.erase (φ ⋎ ψ)))) := by
  have hφ0 : φ ≠ (φ ⋎ ψ) := Semiformula.ne_or_left φ ψ
  have hψ0 : ψ ≠ (φ ⋎ ψ) := Semiformula.ne_or_right φ ψ
  induction dd with
  | @axL α e k d c Γ ar r v hp hn =>
      refine Provable.axL r v ?_ ?_ <;>
        exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
          (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), by assumption⟩))
  | @verumR α e k d c Γ h =>
      exact Provable.verumR (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), h⟩)))
  | @trueRel α e k d c Γ ar r v htrue hτ hαNF hmem =>
      exact Provable.trueRel r v htrue hτ hαNF (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), hmem⟩)))
  | @trueNrel α e k d c Γ ar r v htrue hτ hαNF hmem =>
      exact Provable.trueNrel r v htrue hτ hαNF (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), hmem⟩)))
  | @wk α e k d c Δ Γ hsub _ ih =>
      by_cases hd : (φ ⋎ ψ) ∈ Δ
      · exact Provable.wk (Finset.insert_subset_insert _ (Finset.insert_subset_insert _
          (Finset.erase_subset_erase _ hsub))) (ih hd)
      · refine Provable.wk ?_ (by assumption)
        intro x hx
        exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
          (Finset.mem_erase.mpr ⟨fun e => hd (e ▸ hx), hsub hx⟩))
  | @weak α β e k d c Δ Γ hβ hβNF hαNF hτ hsub _ ih =>
      by_cases hd : (φ ⋎ ψ) ∈ Δ
      · exact Provable.weak hβ hβNF hαNF hτ (Finset.insert_subset_insert _ (Finset.insert_subset_insert _
          (Finset.erase_subset_erase _ hsub))) (ih hd)
      · refine Provable.weak hβ hβNF hαNF hτ ?_ (by assumption)
        intro x hx
        exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
          (Finset.mem_erase.mpr ⟨fun e => hd (e ▸ hx), hsub hx⟩))
  | @andI α βφ' βψ' e k d c Γ₀ φ' ψ' hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ _ _ ihφ ihψ =>
      have hhead : (φ' ⋏ ψ') ≠ (φ ⋎ ψ) := by intro h; simp [Wedge.wedge, Vee.vee] at h
      have hmem : (φ ⋎ ψ) ∈ Γ₀ := (Finset.mem_insert.mp hmem0).resolve_left fun e => hhead e.symm
      have Pφ := Provable.wk (invPush (φ ⋎ ψ) φ' Γ₀) (ihφ (Finset.mem_insert_of_mem hmem))
      have Pψ := Provable.wk (invPush (φ ⋎ ψ) ψ' Γ₀) (ihψ (Finset.mem_insert_of_mem hmem))
      exact Provable.wk (invPull (φ ⋎ ψ) hhead Γ₀) (Provable.andI φ' ψ' hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ Pφ Pψ)
  | @orI α β e k d c Γ₀ φ' ψ' hβ hβNF hαNF hτ _ ih =>
      by_cases hhd : (φ' ⋎ ψ') = (φ ⋎ ψ)
      · obtain ⟨rfl, rfl⟩ := (Semiformula.or_inj _ _ _ _).mp hhd.symm
        rw [Finset.erase_insert_eq_erase]
        by_cases hd : (φ ⋎ ψ) ∈ Γ₀
        · exact Provable.weak hβ hβNF hαNF hτ (princOrSub Γ₀)
            (ih (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hd)))
        · rw [Finset.erase_eq_of_notMem hd]
          exact Provable.weak hβ hβNF hαNF hτ (Finset.Subset.refl _) (by assumption)
      · have hmem : (φ ⋎ ψ) ∈ Γ₀ := (Finset.mem_insert.mp hmem0).resolve_left fun e => hhd e.symm
        have P := Provable.wk (invPush2 (φ ⋎ ψ) φ' ψ' Γ₀)
          (ih (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hmem)))
        exact Provable.wk (invPull (φ ⋎ ψ) hhd Γ₀) (Provable.orI φ' ψ' hβ hβNF hαNF hτ P)
  | @allω α e k d c Γ₀ χ β hβ hβNF hαNF hτ _ ih =>
      have hhead : (∀⁰ χ) ≠ (φ ⋎ ψ) := by intro h; simp [Vee.vee] at h
      have hmem : (φ ⋎ ψ) ∈ Γ₀ := (Finset.mem_insert.mp hmem0).resolve_left fun e => hhead e.symm
      have key : ∀ n, Provable (β n) e (max k n) d c
          (insert (χ/[nm n]) (insert φ (insert ψ (Γ₀.erase (φ ⋎ ψ))))) := fun n =>
        Provable.wk (invPush (φ ⋎ ψ) (χ/[nm n]) Γ₀) (ih n (Finset.mem_insert_of_mem hmem))
      exact Provable.wk (invPull (φ ⋎ ψ) hhead Γ₀) (Provable.allω χ β hβ hβNF hαNF hτ key)
  | @exI α β e k d c Γ₀ χ n hβ hβNF hαNF hτ hbound _ ih =>
      have hhead : (∃⁰ χ) ≠ (φ ⋎ ψ) := by intro h; simp [Vee.vee] at h
      have hmem : (φ ⋎ ψ) ∈ Γ₀ := (Finset.mem_insert.mp hmem0).resolve_left fun e => hhead e.symm
      have P := Provable.wk (invPush (φ ⋎ ψ) (χ/[nm n]) Γ₀) (ih (Finset.mem_insert_of_mem hmem))
      exact Provable.wk (invPull (φ ⋎ ψ) hhead Γ₀) (Provable.exI χ n hβ hβNF hαNF hτ hbound P)
  | @cut α βφ' βψ' e k d c Γ₀ χ hcompl hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ _ _ ih₁ ih₂ =>
      have P₁ := Provable.wk (invPush (φ ⋎ ψ) χ Γ₀) (ih₁ (Finset.mem_insert_of_mem hmem0))
      have P₂ := Provable.wk (invPush (φ ⋎ ψ) (∼χ) Γ₀) (ih₂ (Finset.mem_insert_of_mem hmem0))
      exact Provable.cut χ hcompl hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ P₁ P₂

/-! ### Single-insert reshuffle helpers (for ∧-inversion and the ∀-inversion). -/

private lemma inv1Push (A e b : ArithmeticFormula ℕ) (s : Finset (ArithmeticFormula ℕ)) :
    insert e ((insert b s).erase A) ⊆ insert b (insert e (s.erase A)) := by
  intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto

private lemma inv1Pull (A e : ArithmeticFormula ℕ) {b} (h : b ≠ A) (s : Finset (ArithmeticFormula ℕ)) :
    insert b (insert e (s.erase A)) ⊆ insert e ((insert b s).erase A) := by
  intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
  rcases hx with rfl | rfl | hx
  · exact Or.inr ⟨h, Or.inl rfl⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨hx.1, Or.inr hx.2⟩

private lemma inv1Push2 (A e b₁ b₂ : ArithmeticFormula ℕ) (s : Finset (ArithmeticFormula ℕ)) :
    insert e ((insert b₁ (insert b₂ s)).erase A) ⊆ insert b₁ (insert b₂ (insert e (s.erase A))) := by
  intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto

private lemma princAllSub (A e : ArithmeticFormula ℕ) (s : Finset (ArithmeticFormula ℕ)) :
    insert e ((insert e s).erase A) ⊆ insert e (s.erase A) := by
  intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto

/-- **∧-inversion, left**: replace `φ ⋏ ψ` by `φ`, same `(α,k,d,c)`.

- [Tow20, §19.3] -/
lemma andInvL (dd : Provable α e k d c Γ) (hmem0 : (φ ⋏ ψ) ∈ Γ) :
  Provable α e k d c (insert φ (Γ.erase (φ ⋏ ψ))) := by
  induction dd with
  | @axL α e k d c Γ ar r v hp hn =>
      refine Provable.axL r v ?_ ?_ <;>
        exact Finset.mem_insert_of_mem
          (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), by assumption⟩)
  | @verumR α e k d c Γ h =>
      exact Provable.verumR (Finset.mem_insert_of_mem
        (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), h⟩))
  | @trueRel α e k d c Γ ar r v htrue hτ hαNF hmem =>
      exact Provable.trueRel r v htrue hτ hαNF (Finset.mem_insert_of_mem
        (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), hmem⟩))
  | @trueNrel α e k d c Γ ar r v htrue hτ hαNF hmem =>
      exact Provable.trueNrel r v htrue hτ hαNF (Finset.mem_insert_of_mem
        (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), hmem⟩))
  | @wk α e k d c Δ Γ hsub _ ih =>
      by_cases hh : (φ ⋏ ψ) ∈ Δ
      · exact Provable.wk (Finset.insert_subset_insert _ (Finset.erase_subset_erase _ hsub)) (ih hh)
      · refine Provable.wk ?_ (by assumption)
        intro x hx
        exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨fun e => hh (e ▸ hx), hsub hx⟩)
  | @weak α β e k d c Δ Γ hβ hβNF hαNF hτ hsub _ ih =>
      by_cases hh : (φ ⋏ ψ) ∈ Δ
      · exact Provable.weak hβ hβNF hαNF hτ
          (Finset.insert_subset_insert _ (Finset.erase_subset_erase _ hsub)) (ih hh)
      · refine Provable.weak hβ hβNF hαNF hτ ?_ (by assumption)
        intro x hx
        exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨fun e => hh (e ▸ hx), hsub hx⟩)
  | @andI α βφ' βψ' e k d c Γ₀ φ' ψ' hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ dφ _ ihφ ihψ =>
      by_cases hhd : (φ' ⋏ ψ') = (φ ⋏ ψ)
      · obtain ⟨rfl, rfl⟩ := (Semiformula.and_inj _ _ _ _).mp hhd.symm
        rw [Finset.erase_insert_eq_erase]
        by_cases hh : (φ ⋏ ψ) ∈ Γ₀
        · exact Provable.weak hβφ hβφNF hαNF hτφ (princAllSub (φ ⋏ ψ) _ Γ₀)
            (ihφ (Finset.mem_insert_of_mem hh))
        · rw [Finset.erase_eq_of_notMem hh]
          exact Provable.weak hβφ hβφNF hαNF hτφ (Finset.Subset.refl _) dφ
      · have hmem : (φ ⋏ ψ) ∈ Γ₀ := (Finset.mem_insert.mp hmem0).resolve_left fun e => hhd e.symm
        have Pφ := Provable.wk (inv1Push (φ ⋏ ψ) _ φ' Γ₀) (ihφ (Finset.mem_insert_of_mem hmem))
        have Pψ := Provable.wk (inv1Push (φ ⋏ ψ) _ ψ' Γ₀) (ihψ (Finset.mem_insert_of_mem hmem))
        exact Provable.wk (inv1Pull (φ ⋏ ψ) _ hhd Γ₀)
          (Provable.andI φ' ψ' hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ Pφ Pψ)
  | @orI α β e k d c Γ₀ φ' ψ' hβ hβNF hαNF hτ _ ih =>
      have hhead : (φ' ⋎ ψ') ≠ (φ ⋏ ψ) := by intro h; simp [Vee.vee, Wedge.wedge] at h
      have hmem : (φ ⋏ ψ) ∈ Γ₀ := (Finset.mem_insert.mp hmem0).resolve_left fun e => hhead e.symm
      have P := Provable.wk (inv1Push2 (φ ⋏ ψ) _ φ' ψ' Γ₀)
        (ih (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hmem)))
      exact Provable.wk (inv1Pull (φ ⋏ ψ) _ hhead Γ₀) (Provable.orI φ' ψ' hβ hβNF hαNF hτ P)
  | @allω α e k d c Γ₀ χ β hβ hβNF hαNF hτ _ ih =>
      have hhead : (∀⁰ χ) ≠ (φ ⋏ ψ) := by intro h; simp [UnivQuantifier.all, Wedge.wedge] at h
      have hmem : (φ ⋏ ψ) ∈ Γ₀ := (Finset.mem_insert.mp hmem0).resolve_left fun e => hhead e.symm
      have key : ∀ n, Provable (β n) e (max k n) d c (insert (χ/[nm n]) (insert φ (Γ₀.erase (φ ⋏ ψ)))) :=
        fun n => Provable.wk (inv1Push (φ ⋏ ψ) _ (χ/[nm n]) Γ₀) (ih n (Finset.mem_insert_of_mem hmem))
      exact Provable.wk (inv1Pull (φ ⋏ ψ) _ hhead Γ₀) (Provable.allω χ β hβ hβNF hαNF hτ key)
  | @exI α β e k d c Γ₀ χ n hβ hβNF hαNF hτ hbound _ ih =>
      have hhead : (∃⁰ χ) ≠ (φ ⋏ ψ) := by intro h; simp [ExsQuantifier.exs, Wedge.wedge] at h
      have hmem : (φ ⋏ ψ) ∈ Γ₀ := (Finset.mem_insert.mp hmem0).resolve_left fun e => hhead e.symm
      have P := Provable.wk (inv1Push (φ ⋏ ψ) _ (χ/[nm n]) Γ₀) (ih (Finset.mem_insert_of_mem hmem))
      exact Provable.wk (inv1Pull (φ ⋏ ψ) _ hhead Γ₀) (Provable.exI χ n hβ hβNF hαNF hτ hbound P)
  | @cut α βφ' βψ' e k d c Γ₀ χ hcompl hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ _ _ ih₁ ih₂ =>
      have P₁ := Provable.wk (inv1Push (φ ⋏ ψ) _ χ Γ₀) (ih₁ (Finset.mem_insert_of_mem hmem0))
      have P₂ := Provable.wk (inv1Push (φ ⋏ ψ) _ (∼χ) Γ₀) (ih₂ (Finset.mem_insert_of_mem hmem0))
      exact Provable.cut χ hcompl hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ P₁ P₂

/-- **∧-inversion, right**: replace `φ ⋏ ψ` by `ψ`, same `(α,k,d,c)`.

- [Tow20, §19.3] -/
lemma andInvR (dd : Provable α e k d c Γ) (hmem0 : (φ ⋏ ψ) ∈ Γ) :
  Provable α e k d c (insert ψ (Γ.erase (φ ⋏ ψ))) := by
  induction dd with
  | @axL α e k d c Γ ar r v hp hn =>
      refine Provable.axL r v ?_ ?_ <;>
        exact Finset.mem_insert_of_mem
          (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), by assumption⟩)
  | @verumR α e k d c Γ h =>
      exact Provable.verumR (Finset.mem_insert_of_mem
        (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), h⟩))
  | @trueRel α e k d c Γ ar r v htrue hτ hαNF hmem =>
      exact Provable.trueRel r v htrue hτ hαNF (Finset.mem_insert_of_mem
        (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), hmem⟩))
  | @trueNrel α e k d c Γ ar r v htrue hτ hαNF hmem =>
      exact Provable.trueNrel r v htrue hτ hαNF (Finset.mem_insert_of_mem
        (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), hmem⟩))
  | @wk α e k d c Δ Γ hsub _ ih =>
      by_cases hh : (φ ⋏ ψ) ∈ Δ
      · exact Provable.wk (Finset.insert_subset_insert _ (Finset.erase_subset_erase _ hsub)) (ih hh)
      · refine Provable.wk ?_ (by assumption)
        intro x hx
        exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨fun e => hh (e ▸ hx), hsub hx⟩)
  | @weak α β e k d c Δ Γ hβ hβNF hαNF hτ hsub _ ih =>
      by_cases hh : (φ ⋏ ψ) ∈ Δ
      · exact Provable.weak hβ hβNF hαNF hτ
          (Finset.insert_subset_insert _ (Finset.erase_subset_erase _ hsub)) (ih hh)
      · refine Provable.weak hβ hβNF hαNF hτ ?_ (by assumption)
        intro x hx
        exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨fun e => hh (e ▸ hx), hsub hx⟩)
  | @andI α βφ' βψ' e k d c Γ₀ φ' ψ' hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ _ dψ ihφ ihψ =>
      by_cases hhd : (φ' ⋏ ψ') = (φ ⋏ ψ)
      · obtain ⟨rfl, rfl⟩ := (Semiformula.and_inj _ _ _ _).mp hhd.symm
        rw [Finset.erase_insert_eq_erase]
        by_cases hh : (φ ⋏ ψ) ∈ Γ₀
        · exact Provable.weak hβψ hβψNF hαNF hτψ (princAllSub (φ ⋏ ψ) _ Γ₀)
            (ihψ (Finset.mem_insert_of_mem hh))
        · rw [Finset.erase_eq_of_notMem hh]
          exact Provable.weak hβψ hβψNF hαNF hτψ (Finset.Subset.refl _) dψ
      · have hmem : (φ ⋏ ψ) ∈ Γ₀ := (Finset.mem_insert.mp hmem0).resolve_left fun e => hhd e.symm
        have Pφ := Provable.wk (inv1Push (φ ⋏ ψ) _ φ' Γ₀) (ihφ (Finset.mem_insert_of_mem hmem))
        have Pψ := Provable.wk (inv1Push (φ ⋏ ψ) _ ψ' Γ₀) (ihψ (Finset.mem_insert_of_mem hmem))
        exact Provable.wk (inv1Pull (φ ⋏ ψ) _ hhd Γ₀)
          (Provable.andI φ' ψ' hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ Pφ Pψ)
  | @orI α β e k d c Γ₀ φ' ψ' hβ hβNF hαNF hτ _ ih =>
      have hhead : (φ' ⋎ ψ') ≠ (φ ⋏ ψ) := by intro h; simp [Vee.vee, Wedge.wedge] at h
      have hmem : (φ ⋏ ψ) ∈ Γ₀ := (Finset.mem_insert.mp hmem0).resolve_left fun e => hhead e.symm
      have P := Provable.wk (inv1Push2 (φ ⋏ ψ) _ φ' ψ' Γ₀)
        (ih (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hmem)))
      exact Provable.wk (inv1Pull (φ ⋏ ψ) _ hhead Γ₀) (Provable.orI φ' ψ' hβ hβNF hαNF hτ P)
  | @allω α e k d c Γ₀ χ β hβ hβNF hαNF hτ _ ih =>
      have hhead : (∀⁰ χ) ≠ (φ ⋏ ψ) := by intro h; simp [UnivQuantifier.all, Wedge.wedge] at h
      have hmem : (φ ⋏ ψ) ∈ Γ₀ := (Finset.mem_insert.mp hmem0).resolve_left fun e => hhead e.symm
      have key : ∀ n, Provable (β n) e (max k n) d c (insert (χ/[nm n]) (insert ψ (Γ₀.erase (φ ⋏ ψ)))) :=
        fun n => Provable.wk (inv1Push (φ ⋏ ψ) _ (χ/[nm n]) Γ₀) (ih n (Finset.mem_insert_of_mem hmem))
      exact Provable.wk (inv1Pull (φ ⋏ ψ) _ hhead Γ₀) (Provable.allω χ β hβ hβNF hαNF hτ key)
  | @exI α β e k d c Γ₀ χ n hβ hβNF hαNF hτ hbound _ ih =>
      have hhead : (∃⁰ χ) ≠ (φ ⋏ ψ) := by intro h; simp [ExsQuantifier.exs, Wedge.wedge] at h
      have hmem : (φ ⋏ ψ) ∈ Γ₀ := (Finset.mem_insert.mp hmem0).resolve_left fun e => hhead e.symm
      have P := Provable.wk (inv1Push (φ ⋏ ψ) _ (χ/[nm n]) Γ₀) (ih (Finset.mem_insert_of_mem hmem))
      exact Provable.wk (inv1Pull (φ ⋏ ψ) _ hhead Γ₀) (Provable.exI χ n hβ hβNF hαNF hτ hbound P)
  | @cut α βφ' βψ' e k d c Γ₀ χ hcompl hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ _ _ ih₁ ih₂ =>
      have P₁ := Provable.wk (inv1Push (φ ⋏ ψ) _ χ Γ₀) (ih₁ (Finset.mem_insert_of_mem hmem0))
      have P₂ := Provable.wk (inv1Push (φ ⋏ ψ) _ (∼χ) Γ₀) (ih₂ (Finset.mem_insert_of_mem hmem0))
      exact Provable.cut χ hcompl hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ P₁ P₂

/-- **∀-inversion** — the bound-critical one (the subformula bridge to `B` consumes it).
Result raises the **`k`-part** to `max k n₀` (`d` inert): the principal case's idempotent collapse
`max (max k n₀) n₀ = max k n₀` is exactly why the split index keeps `allInv` working.

- [Tow20, §19.4] -/
lemma allInv {φ₀ : ArithmeticSemiformula ℕ 1} (n₀ : ℕ) (dd : Provable α e k d c Γ)
  (hmem0 : (∀⁰ φ₀) ∈ Γ) : Provable α e (max k n₀) d c (insert (φ₀/[nm n₀]) (Γ.erase (∀⁰ φ₀))) := by
  have hI0 : (φ₀/[nm n₀]) ≠ (∀⁰ φ₀) := Semiformula.ne_of_ne_complexity (by simp)
  induction dd with
  | @axL α e k d c Γ ar r v hp hn =>
      refine Provable.axL r v ?_ ?_ <;>
        exact Finset.mem_insert_of_mem
          (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), by assumption⟩)
  | @verumR α e k d c Γ h =>
      exact Provable.verumR (Finset.mem_insert_of_mem
        (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), h⟩))
  | @trueRel α e k d c Γ ar r v htrue hτ hαNF hmem =>
      exact Provable.trueRel r v htrue (lt_of_lt_of_le hτ (Nat.add_le_add_right (le_max_left _ _) d)) hαNF
        (Finset.mem_insert_of_mem
          (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), hmem⟩))
  | @trueNrel α e k d c Γ ar r v htrue hτ hαNF hmem =>
      exact Provable.trueNrel r v htrue (lt_of_lt_of_le hτ (Nat.add_le_add_right (le_max_left _ _) d)) hαNF
        (Finset.mem_insert_of_mem
          (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), hmem⟩))
  | @wk α e k d c Δ Γ hsub _ ih =>
      by_cases hh : (∀⁰ φ₀) ∈ Δ
      · exact Provable.wk (Finset.insert_subset_insert _ (Finset.erase_subset_erase _ hsub)) (ih hh)
      · refine Provable.wk ?_ (Provable.mono_k (by assumption) (le_max_left _ _))
        intro x hx
        exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨fun e => hh (e ▸ hx), hsub hx⟩)
  | @weak α β e k d c Δ Γ hβ hβNF hαNF hτ hsub _ ih =>
      by_cases hh : (∀⁰ φ₀) ∈ Δ
      · exact Provable.weak hβ hβNF hαNF (lt_of_lt_of_le hτ (Nat.add_le_add_right (le_max_left _ _) d))
          (Finset.insert_subset_insert _ (Finset.erase_subset_erase _ hsub)) (ih hh)
      · refine Provable.weak hβ hβNF hαNF (lt_of_lt_of_le hτ (Nat.add_le_add_right (le_max_left _ _) d)) ?_
          (Provable.mono_k (by assumption) (le_max_left _ _))
        intro x hx
        exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨fun e => hh (e ▸ hx), hsub hx⟩)
  | @andI α βφ' βψ' e k d c Γ₀ φ' ψ' hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ _ _ ihφ ihψ =>
      have hhead : (φ' ⋏ ψ') ≠ (∀⁰ φ₀) := by intro h; simp [Wedge.wedge, UnivQuantifier.all] at h
      have hmem : (∀⁰ φ₀) ∈ Γ₀ := (Finset.mem_insert.mp hmem0).resolve_left fun e => hhead e.symm
      have Pφ := Provable.wk (inv1Push (∀⁰ φ₀) _ φ' Γ₀) (ihφ (Finset.mem_insert_of_mem hmem))
      have Pψ := Provable.wk (inv1Push (∀⁰ φ₀) _ ψ' Γ₀) (ihψ (Finset.mem_insert_of_mem hmem))
      exact Provable.wk (inv1Pull (∀⁰ φ₀) _ hhead Γ₀)
        (Provable.andI φ' ψ' hβφ hβψ hβφNF hβψNF hαNF
          (lt_of_lt_of_le hτφ (Nat.add_le_add_right (le_max_left _ _) d))
          (lt_of_lt_of_le hτψ (Nat.add_le_add_right (le_max_left _ _) d)) Pφ Pψ)
  | @orI α β e k d c Γ₀ φ' ψ' hβ hβNF hαNF hτ _ ih =>
      have hhead : (φ' ⋎ ψ') ≠ (∀⁰ φ₀) := by intro h; simp [Vee.vee, UnivQuantifier.all] at h
      have hmem : (∀⁰ φ₀) ∈ Γ₀ := (Finset.mem_insert.mp hmem0).resolve_left fun e => hhead e.symm
      have P := Provable.wk (inv1Push2 (∀⁰ φ₀) _ φ' ψ' Γ₀)
        (ih (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hmem)))
      exact Provable.wk (inv1Pull (∀⁰ φ₀) _ hhead Γ₀)
        (Provable.orI φ' ψ' hβ hβNF hαNF (lt_of_lt_of_le hτ (Nat.add_le_add_right (le_max_left _ _) d)) P)
  | @allω α e k d c Γ₀ χ β hβ hβNF hαNF hτ dd ih =>
      by_cases hhd : (∀⁰ χ) = (∀⁰ φ₀)
      · obtain rfl := (Semiformula.all_inj _ _).mp hhd
        rw [Finset.erase_insert_eq_erase]
        by_cases hh : (∀⁰ χ) ∈ Γ₀
        · have h := ih n₀ (Finset.mem_insert_of_mem hh)
          rw [max_eq_left (le_max_right k n₀)] at h
          exact Provable.weak (hβ n₀) (hβNF n₀) hαNF (hτ n₀) (princAllSub (∀⁰ χ) _ Γ₀) h
        · rw [Finset.erase_eq_of_notMem hh]
          exact Provable.weak (hβ n₀) (hβNF n₀) hαNF (hτ n₀) (Finset.Subset.refl _) (dd n₀)
      · have hmem : (∀⁰ φ₀) ∈ Γ₀ := (Finset.mem_insert.mp hmem0).resolve_left fun e => hhd e.symm
        have key : ∀ n, Provable (β n) e (max (max k n₀) n) d c
            (insert (χ/[nm n]) (insert (φ₀/[nm n₀]) (Γ₀.erase (∀⁰ φ₀)))) := by
          intro n
          have h := Provable.wk (inv1Push (∀⁰ φ₀) _ (χ/[nm n]) Γ₀) (ih n (Finset.mem_insert_of_mem hmem))
          rw [show max (max k n₀) n = max (max k n) n₀ from by omega]
          exact h
        exact Provable.wk (inv1Pull (∀⁰ φ₀) _ hhd Γ₀)
          (Provable.allω χ β hβ hβNF hαNF (fun n => lt_of_lt_of_le (hτ n) (by omega)) key)
  | @exI α β e k d c Γ₀ χ n hβ hβNF hαNF hτ hbound _ ih =>
      have hhead : (∃⁰ χ) ≠ (∀⁰ φ₀) := by intro h; simp [ExsQuantifier.exs, UnivQuantifier.all] at h
      have hmem : (∀⁰ φ₀) ∈ Γ₀ := (Finset.mem_insert.mp hmem0).resolve_left fun e => hhead e.symm
      have P := Provable.wk (inv1Push (∀⁰ φ₀) _ (χ/[nm n]) Γ₀) (ih (Finset.mem_insert_of_mem hmem))
      exact Provable.wk (inv1Pull (∀⁰ φ₀) _ hhead Γ₀)
        (Provable.exI χ n hβ hβNF hαNF (lt_of_lt_of_le hτ (Nat.add_le_add_right (le_max_left _ _) d))
          (le_trans hbound (hardy_monotone _ (Nat.add_le_add_right (le_max_left _ _) d))) P)
  | @cut α βφ' βψ' e k d c Γ₀ χ hcompl hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ _ _ ih₁ ih₂ =>
      have P₁ := Provable.wk (inv1Push (∀⁰ φ₀) _ χ Γ₀) (ih₁ (Finset.mem_insert_of_mem hmem0))
      have P₂ := Provable.wk (inv1Push (∀⁰ φ₀) _ (∼χ) Γ₀) (ih₂ (Finset.mem_insert_of_mem hmem0))
      exact Provable.cut χ hcompl hβφ hβψ hβφNF hβψNF hαNF
        (lt_of_lt_of_le hτφ (Nat.add_le_add_right (le_max_left _ _) d))
        (lt_of_lt_of_le hτψ (Nat.add_le_add_right (le_max_left _ _) d)) P₁ P₂


end Provable

end GoodsteinPA.OperatorZinfty
