module

public import GoodsteinPA.Zef2TC.Basic

@[expose] public section

namespace GoodsteinPA.E1EmbeddingGrind

open LO LO.FirstOrder LO.FirstOrder.ArithmeticTerm ONote
open GoodsteinPA.OperatorZeh GoodsteinPA.OperatorZinfty

/-! ### allω INVERSION — the E→R/D seam converter

The rungs R/D consume per-instance SINGLETONS `{body/[nm m]}`, while the V3 master ladder
concludes at the ∀-sentence.  Inversion replays the derivation at branch slot `rel1 f m`,
replacing `∀⁰ φ` by its `m`-th numeral instance throughout.  Operators are phantoms in
`Zef2TC` (`change_H`), so only the slot/gate bookkeeping is live: every gate `≤ f 0` lifts
to `≤ rel1 f m 0` by monotonicity, and nested ω-branches commute via `rel1_rel1`+`max_comm`. -/

set_option maxHeartbeats 1600000 in
theorem allω_inversion {φ : ArithmeticSemiformula ℕ 1} (m : ℕ)
    {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Finset (ArithmeticFormula ℕ)}
    (dd : Zef2TC α e H f c Γ) : Monotone f →
      Zef2TC α e H (rel1 f m) c (insert (φ/[nm m]) (Γ.erase (∀⁰ φ))) := by
  have hkey : ∀ (f : ℕ → ℕ), Monotone f → ∀ x, f x ≤ rel1 f m x := by
    intro f hmono x
    exact hmono (le_max_right m x)
  -- re-shape an inverted premise `insert inst ((insert χ Γ).erase ∀φ)` into the
  -- rebuilt rule's premise `insert χ (insert inst (Γ.erase ∀φ))`
  have hreshape : ∀ (χ : ArithmeticFormula ℕ) (Γ : Finset (ArithmeticFormula ℕ)),
      insert (φ/[nm m]) ((insert χ Γ).erase (∀⁰ φ))
        ⊆ insert χ (insert (φ/[nm m]) (Γ.erase (∀⁰ φ))) := by
    intro χ Γ x hx
    simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
    tauto
  -- targets: conclusion reshaping `insert χ (insert inst (Γ.erase ∀φ)) ⊇ goal` when χ ∈ Γ-form
  induction dd with
  | axL hαN r v hp hn =>
      intro hmono
      refine Zef2TC.axL (le_trans hαN (hkey _ hmono 0)) r v ?_ ?_
      · exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨by simp, hp⟩)
      · exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨by simp, hn⟩)
  | trueRel hαN r v htrue hmem =>
      intro hmono
      exact Zef2TC.trueRel (le_trans hαN (hkey _ hmono 0)) r v htrue
        (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨by simp, hmem⟩))
  | trueNrel hαN r v htrue hmem =>
      intro hmono
      exact Zef2TC.trueNrel (le_trans hαN (hkey _ hmono 0)) r v htrue
        (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨by simp, hmem⟩))
  | verumR hαN h =>
      intro hmono
      exact Zef2TC.verumR (le_trans hαN (hkey _ hmono 0))
        (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨by simp, h⟩))
  | wk hαN hsub _ ih =>
      intro hmono
      exact Zef2TC.wk (le_trans hαN (hkey _ hmono 0))
        (Finset.insert_subset_insert _ (Finset.erase_subset_erase _ hsub)) (ih hmono)
  | @weak α' β' e' H' F' c' Δ' Γ' hαN hβ hβNF hαNF hβH hsub _ ih =>
      intro hmono
      exact Zef2TC.weak (le_trans hαN (hkey _ hmono 0)) hβ hβNF hαNF hβH
        (Finset.insert_subset_insert _ (Finset.erase_subset_erase _ hsub)) (ih hmono)
  | @andI α' βφ' βψ' e' H' F' c' Γ' hαN χ₁ χ₂ hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH _ _ ih₁ ih₂ =>
      intro hmono
      have hne : χ₁ ⋏ χ₂ ≠ ∀⁰ φ := by simp
      rw [Finset.erase_insert_of_ne hne]
      rw [Finset.insert_comm]
      refine Zef2TC.andI (le_trans hαN (hkey _ hmono 0)) χ₁ χ₂ hβφ hβψ hβφNF hβψNF hαNF
        hβφH hβψH ?_ ?_
      · exact Zef2TC.wk (ih₁ hmono).gate (hreshape χ₁ Γ') (ih₁ hmono)
      · exact Zef2TC.wk (ih₂ hmono).gate (hreshape χ₂ Γ') (ih₂ hmono)
  | @orI α' β' e' H' F' c' Γ' hαN χ₁ χ₂ hβ hβNF hαNF hβH _ ih =>
      intro hmono
      have hne : χ₁ ⋎ χ₂ ≠ ∀⁰ φ := by simp
      rw [Finset.erase_insert_of_ne hne, Finset.insert_comm]
      refine Zef2TC.orI (le_trans hαN (hkey _ hmono 0)) χ₁ χ₂ hβ hβNF hαNF hβH ?_
      have h := ih hmono
      refine Zef2TC.wk h.gate ?_ h
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
      tauto
  | @allω α' e' H' F' c' Γ' hαN χ β hβ hβNF hαNF hβH dd ih =>
      intro hmono
      by_cases hchi : (∀⁰ χ : ArithmeticFormula ℕ) = ∀⁰ φ
      · -- PRINCIPAL: take branch m, re-invert it, drop the duplicate instance
        have hφχ : χ = φ := by simpa using hchi
        subst hφχ
        have hbr := (ih m) (rel1_monotone hmono m)
        -- slot: rel1 (rel1 F m) m = rel1 F m
        rw [rel1_rel1, max_self] at hbr
        -- context: insert inst ((insert inst Γ').erase ∀χ) = insert inst (Γ'.erase ∀χ)
        have hctx : insert ((χ : ArithmeticSemiformula ℕ 1)/[nm m])
              ((insert (χ/[nm m]) Γ').erase (∀⁰ χ))
            = insert (χ/[nm m]) (Γ'.erase (∀⁰ χ)) := by
          rw [Finset.erase_insert_of_ne (by
            intro h
            have := congrArg Semiformula.complexity h
            simp at this)]
          exact Finset.insert_idem _ _
        rw [hctx] at hbr
        have hbr' := hbr.change_H (H' := H')
        refine Zef2TC.weak (le_trans hαN (hkey _ hmono 0)) (hβ m) (hβNF m) hαNF
          (Cl_of_NF (hβNF m)) ?_ hbr'
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
        tauto
      · -- NON-PRINCIPAL: rebuild the ω-rule over the inverted branches
        rw [Finset.erase_insert_of_ne hchi, Finset.insert_comm]
        refine Zef2TC.allω (le_trans hαN (hkey _ hmono 0)) χ β hβ hβNF hαNF
          (fun n => hβH n) ?_
        intro n
        have h := (ih n) (rel1_monotone hmono n)
        rw [rel1_rel1, max_comm n m, ← rel1_rel1] at h
        have h' := h.change_H (H' := adjoin H' n)
        refine Zef2TC.wk h'.gate ?_ h'
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
        tauto
  | @exI α' β' e' H' F' c' Γ' hαN χ n hβ hβNF hαNF hβH hbound _ ih =>
      intro hmono
      have hne : (∃⁰ χ : ArithmeticFormula ℕ) ≠ ∀⁰ φ := by simp
      rw [Finset.erase_insert_of_ne hne, Finset.insert_comm]
      refine Zef2TC.exI (le_trans hαN (hkey _ hmono 0)) χ n hβ hβNF hαNF hβH
        (le_trans hbound (hkey _ hmono 0)) ?_
      have h := ih hmono
      refine Zef2TC.wk h.gate ?_ h
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
      tauto
  | @cut α' βφ' βψ' e' H' F' c' Γ' hαN χ hcompl hcutRead hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH _ _ ih₁ ih₂ =>
      intro hmono
      refine Zef2TC.cut (le_trans hαN (hkey _ hmono 0)) χ hcompl
        (le_trans hcutRead (hkey _ hmono 0)) hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH ?_ ?_
      · exact Zef2TC.wk (ih₁ hmono).gate (hreshape χ Γ') (ih₁ hmono)
      · exact Zef2TC.wk (ih₂ hmono).gate (hreshape (∼χ) Γ') (ih₂ hmono)
/-! ### The TC pass-port kit, part 1 — finite inversions + ⊥-erase

`passAux`'s inert-shape discharge (`Zef2.erase_inert`) breaks over `Zef2TC` (⋏/⋎/⊤ ARE
principal here).  The port needs: and/or-INVERSION (the finite mirrors of `allω_inversion` —
no slot change, no operator change), and ⊥-erase (⊥ is still never principal in TC). -/

/-- Left ⋏-inversion: replace `χ₁ ⋏ χ₂` by `χ₁` throughout.  Same ordinal, slot, rank. -/
theorem and_inversion_left {χ₁ χ₂}
    {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Finset (ArithmeticFormula ℕ)}
    (dd : Zef2TC α e H f c Γ) :
      Zef2TC α e H f c (insert χ₁ (Γ.erase (χ₁ ⋏ χ₂))) := by
  have hreshape : ∀ (χ : ArithmeticFormula ℕ) (Γ : Finset (ArithmeticFormula ℕ)),
      insert χ₁ ((insert χ Γ).erase (χ₁ ⋏ χ₂))
        ⊆ insert χ (insert χ₁ (Γ.erase (χ₁ ⋏ χ₂))) := by
    intro χ Γ x hx
    simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
    tauto
  induction dd with
  | axL hαN r v hp hn =>
      exact Zef2TC.axL hαN r v
        (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨by simp, hp⟩))
        (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨by simp, hn⟩))
  | trueRel hαN r v htrue hmem =>
      exact Zef2TC.trueRel hαN r v htrue
        (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨by simp, hmem⟩))
  | trueNrel hαN r v htrue hmem =>
      exact Zef2TC.trueNrel hαN r v htrue
        (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨by simp, hmem⟩))
  | verumR hαN h =>
      exact Zef2TC.verumR hαN
        (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨by simp, h⟩))
  | wk hαN hsub _ ih =>
      exact Zef2TC.wk hαN
        (Finset.insert_subset_insert _ (Finset.erase_subset_erase _ hsub)) ih
  | weak hαN hβ hβNF hαNF hβH hsub _ ih =>
      exact Zef2TC.weak hαN hβ hβNF hαNF hβH
        (Finset.insert_subset_insert _ (Finset.erase_subset_erase _ hsub)) ih
  | @andI α' βφ' βψ' e' H' F' c' Γ' hαN φ ψ hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH d₁ _ ih₁ ih₂ =>
      by_cases hchi : (φ ⋏ ψ : ArithmeticFormula ℕ) = χ₁ ⋏ χ₂
      · -- PRINCIPAL: use the LEFT premise, re-invert, drop the duplicate
        have hφ₁ : φ = χ₁ ∧ ψ = χ₂ := by simpa using hchi
        obtain ⟨rfl, rfl⟩ := hφ₁
        have hctx : insert (φ : ArithmeticFormula ℕ) ((insert φ Γ').erase (φ ⋏ ψ))
            = insert φ (Γ'.erase (φ ⋏ ψ)) := by
          rw [Finset.erase_insert_of_ne (by
            intro h
            have := congrArg Semiformula.complexity h
            simp at this)]
          exact Finset.insert_idem _ _
        rw [hctx] at ih₁
        refine Zef2TC.weak hαN hβφ hβφNF hαNF hβφH ?_ ih₁
        rw [hchi]
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
        tauto
      · rw [Finset.erase_insert_of_ne hchi, Finset.insert_comm]
        refine Zef2TC.andI hαN φ ψ hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH ?_ ?_
        · exact Zef2TC.wk ih₁.gate (hreshape φ Γ') ih₁
        · exact Zef2TC.wk ih₂.gate (hreshape ψ Γ') ih₂
  | @orI α' β' e' H' F' c' Γ' hαN φ ψ hβ hβNF hαNF hβH _ ih =>
      have hne : (φ ⋎ ψ : ArithmeticFormula ℕ) ≠ χ₁ ⋏ χ₂ := by simp
      rw [Finset.erase_insert_of_ne hne, Finset.insert_comm]
      refine Zef2TC.orI hαN φ ψ hβ hβNF hαNF hβH ?_
      refine Zef2TC.wk ih.gate ?_ ih
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
      tauto
  | @allω α' e' H' F' c' Γ' hαN φ β hβ hβNF hαNF hβH _ ih =>
      have hne : (∀⁰ φ : ArithmeticFormula ℕ) ≠ χ₁ ⋏ χ₂ := by simp
      rw [Finset.erase_insert_of_ne hne, Finset.insert_comm]
      refine Zef2TC.allω hαN φ β hβ hβNF hαNF hβH ?_
      intro n
      refine Zef2TC.wk (ih n).gate ?_ (ih n)
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
      tauto
  | @exI α' β' e' H' F' c' Γ' hαN φ n hβ hβNF hαNF hβH hbound _ ih =>
      have hne : (∃⁰ φ : ArithmeticFormula ℕ) ≠ χ₁ ⋏ χ₂ := by simp
      rw [Finset.erase_insert_of_ne hne, Finset.insert_comm]
      refine Zef2TC.exI hαN φ n hβ hβNF hαNF hβH hbound ?_
      refine Zef2TC.wk ih.gate ?_ ih
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
      tauto
  | @cut α' βφ' βψ' e' H' F' c' Γ' hαN φ hcompl hcutRead hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH _ _ ih₁ ih₂ =>
      refine Zef2TC.cut hαN φ hcompl hcutRead hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH ?_ ?_
      · exact Zef2TC.wk ih₁.gate (hreshape φ Γ') ih₁
      · exact Zef2TC.wk ih₂.gate (hreshape (∼φ) Γ') ih₂

/-- Right ⋏-inversion. -/
theorem and_inversion_right {χ₁ χ₂}
    {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Finset (ArithmeticFormula ℕ)}
    (dd : Zef2TC α e H f c Γ) :
      Zef2TC α e H f c (insert χ₂ (Γ.erase (χ₁ ⋏ χ₂))) := by
  have hreshape : ∀ (χ : ArithmeticFormula ℕ) (Γ : Finset (ArithmeticFormula ℕ)),
      insert χ₂ ((insert χ Γ).erase (χ₁ ⋏ χ₂))
        ⊆ insert χ (insert χ₂ (Γ.erase (χ₁ ⋏ χ₂))) := by
    intro χ Γ x hx
    simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
    tauto
  induction dd with
  | axL hαN r v hp hn =>
      exact Zef2TC.axL hαN r v
        (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨by simp, hp⟩))
        (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨by simp, hn⟩))
  | trueRel hαN r v htrue hmem =>
      exact Zef2TC.trueRel hαN r v htrue
        (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨by simp, hmem⟩))
  | trueNrel hαN r v htrue hmem =>
      exact Zef2TC.trueNrel hαN r v htrue
        (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨by simp, hmem⟩))
  | verumR hαN h =>
      exact Zef2TC.verumR hαN
        (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨by simp, h⟩))
  | wk hαN hsub _ ih =>
      exact Zef2TC.wk hαN
        (Finset.insert_subset_insert _ (Finset.erase_subset_erase _ hsub)) ih
  | weak hαN hβ hβNF hαNF hβH hsub _ ih =>
      exact Zef2TC.weak hαN hβ hβNF hαNF hβH
        (Finset.insert_subset_insert _ (Finset.erase_subset_erase _ hsub)) ih
  | @andI α' βφ' βψ' e' H' F' c' Γ' hαN φ ψ hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH _ d₂ ih₁ ih₂ =>
      by_cases hchi : (φ ⋏ ψ : ArithmeticFormula ℕ) = χ₁ ⋏ χ₂
      · have hφ₁ : φ = χ₁ ∧ ψ = χ₂ := by simpa using hchi
        obtain ⟨rfl, rfl⟩ := hφ₁
        have hctx : insert (ψ : ArithmeticFormula ℕ) ((insert ψ Γ').erase (φ ⋏ ψ))
            = insert ψ (Γ'.erase (φ ⋏ ψ)) := by
          rw [Finset.erase_insert_of_ne (by
            intro h
            have := congrArg Semiformula.complexity h
            simp at this)]
          exact Finset.insert_idem _ _
        rw [hctx] at ih₂
        refine Zef2TC.weak hαN hβψ hβψNF hαNF hβψH ?_ ih₂
        rw [hchi]
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
        tauto
      · rw [Finset.erase_insert_of_ne hchi, Finset.insert_comm]
        refine Zef2TC.andI hαN φ ψ hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH ?_ ?_
        · exact Zef2TC.wk ih₁.gate (hreshape φ Γ') ih₁
        · exact Zef2TC.wk ih₂.gate (hreshape ψ Γ') ih₂
  | @orI α' β' e' H' F' c' Γ' hαN φ ψ hβ hβNF hαNF hβH _ ih =>
      have hne : (φ ⋎ ψ : ArithmeticFormula ℕ) ≠ χ₁ ⋏ χ₂ := by simp
      rw [Finset.erase_insert_of_ne hne, Finset.insert_comm]
      refine Zef2TC.orI hαN φ ψ hβ hβNF hαNF hβH ?_
      refine Zef2TC.wk ih.gate ?_ ih
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
      tauto
  | @allω α' e' H' F' c' Γ' hαN φ β hβ hβNF hαNF hβH _ ih =>
      have hne : (∀⁰ φ : ArithmeticFormula ℕ) ≠ χ₁ ⋏ χ₂ := by simp
      rw [Finset.erase_insert_of_ne hne, Finset.insert_comm]
      refine Zef2TC.allω hαN φ β hβ hβNF hαNF hβH ?_
      intro n
      refine Zef2TC.wk (ih n).gate ?_ (ih n)
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
      tauto
  | @exI α' β' e' H' F' c' Γ' hαN φ n hβ hβNF hαNF hβH hbound _ ih =>
      have hne : (∃⁰ φ : ArithmeticFormula ℕ) ≠ χ₁ ⋏ χ₂ := by simp
      rw [Finset.erase_insert_of_ne hne, Finset.insert_comm]
      refine Zef2TC.exI hαN φ n hβ hβNF hαNF hβH hbound ?_
      refine Zef2TC.wk ih.gate ?_ ih
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
      tauto
  | @cut α' βφ' βψ' e' H' F' c' Γ' hαN φ hcompl hcutRead hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH _ _ ih₁ ih₂ =>
      refine Zef2TC.cut hαN φ hcompl hcutRead hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH ?_ ?_
      · exact Zef2TC.wk ih₁.gate (hreshape φ Γ') ih₁
      · exact Zef2TC.wk ih₂.gate (hreshape (∼φ) Γ') ih₂

/-- ⋎-inversion: replace `χ₁ ⋎ χ₂` by BOTH disjuncts. -/
theorem or_inversion {χ₁ χ₂}
    {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Finset (ArithmeticFormula ℕ)}
    (dd : Zef2TC α e H f c Γ) :
      Zef2TC α e H f c (insert χ₁ (insert χ₂ (Γ.erase (χ₁ ⋎ χ₂)))) := by
  have hreshape : ∀ (χ : ArithmeticFormula ℕ) (Γ : Finset (ArithmeticFormula ℕ)),
      insert χ₁ (insert χ₂ ((insert χ Γ).erase (χ₁ ⋎ χ₂)))
        ⊆ insert χ (insert χ₁ (insert χ₂ (Γ.erase (χ₁ ⋎ χ₂)))) := by
    intro χ Γ x hx
    simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
    tauto
  induction dd with
  | axL hαN r v hp hn =>
      exact Zef2TC.axL hαN r v
        (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
          (Finset.mem_erase.mpr ⟨by simp, hp⟩)))
        (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
          (Finset.mem_erase.mpr ⟨by simp, hn⟩)))
  | trueRel hαN r v htrue hmem =>
      exact Zef2TC.trueRel hαN r v htrue
        (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
          (Finset.mem_erase.mpr ⟨by simp, hmem⟩)))
  | trueNrel hαN r v htrue hmem =>
      exact Zef2TC.trueNrel hαN r v htrue
        (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
          (Finset.mem_erase.mpr ⟨by simp, hmem⟩)))
  | verumR hαN h =>
      exact Zef2TC.verumR hαN
        (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
          (Finset.mem_erase.mpr ⟨by simp, h⟩)))
  | wk hαN hsub _ ih =>
      exact Zef2TC.wk hαN
        (Finset.insert_subset_insert _ (Finset.insert_subset_insert _
          (Finset.erase_subset_erase _ hsub))) ih
  | weak hαN hβ hβNF hαNF hβH hsub _ ih =>
      exact Zef2TC.weak hαN hβ hβNF hαNF hβH
        (Finset.insert_subset_insert _ (Finset.insert_subset_insert _
          (Finset.erase_subset_erase _ hsub))) ih
  | @andI α' βφ' βψ' e' H' F' c' Γ' hαN φ ψ hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH _ _ ih₁ ih₂ =>
      have hne : (φ ⋏ ψ : ArithmeticFormula ℕ) ≠ χ₁ ⋎ χ₂ := by simp
      rw [Finset.erase_insert_of_ne hne]
      rw [show insert (χ₁ : ArithmeticFormula ℕ) (insert χ₂ (insert (φ ⋏ ψ) (Γ'.erase (χ₁ ⋎ χ₂))))
          = insert (φ ⋏ ψ) (insert χ₁ (insert χ₂ (Γ'.erase (χ₁ ⋎ χ₂)))) from by
        rw [Finset.insert_comm χ₂, Finset.insert_comm χ₁]]
      refine Zef2TC.andI hαN φ ψ hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH ?_ ?_
      · exact Zef2TC.wk ih₁.gate (hreshape φ Γ') ih₁
      · exact Zef2TC.wk ih₂.gate (hreshape ψ Γ') ih₂
  | @orI α' β' e' H' F' c' Γ' hαN φ ψ hβ hβNF hαNF hβH d₁ ih =>
      by_cases hchi : (φ ⋎ ψ : ArithmeticFormula ℕ) = χ₁ ⋎ χ₂
      · -- PRINCIPAL: the premise carries BOTH disjuncts; re-invert and clean up
        have hφ₁ : φ = χ₁ ∧ ψ = χ₂ := by simpa using hchi
        obtain ⟨rfl, rfl⟩ := hφ₁
        have hctx : insert (φ : ArithmeticFormula ℕ) (insert ψ
              ((insert φ (insert ψ Γ')).erase (φ ⋎ ψ)))
            = insert φ (insert ψ (Γ'.erase (φ ⋎ ψ))) := by
          rw [Finset.erase_insert_of_ne (by
              intro h
              have := congrArg Semiformula.complexity h
              simp at this),
            Finset.erase_insert_of_ne (by
              intro h
              have := congrArg Semiformula.complexity h
              simp at this)]
          ext x
          simp only [Finset.mem_insert]
          tauto
        rw [hctx] at ih
        refine Zef2TC.weak hαN hβ hβNF hαNF hβH ?_ ih
        rw [hchi]
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
        tauto
      · rw [Finset.erase_insert_of_ne hchi]
        rw [show insert (χ₁ : ArithmeticFormula ℕ) (insert χ₂ (insert (φ ⋎ ψ) (Γ'.erase (χ₁ ⋎ χ₂))))
            = insert (φ ⋎ ψ) (insert χ₁ (insert χ₂ (Γ'.erase (χ₁ ⋎ χ₂)))) from by
          rw [Finset.insert_comm χ₂, Finset.insert_comm χ₁]]
        refine Zef2TC.orI hαN φ ψ hβ hβNF hαNF hβH ?_
        refine Zef2TC.wk ih.gate ?_ ih
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
        tauto
  | @allω α' e' H' F' c' Γ' hαN φ β hβ hβNF hαNF hβH _ ih =>
      have hne : (∀⁰ φ : ArithmeticFormula ℕ) ≠ χ₁ ⋎ χ₂ := by simp
      rw [Finset.erase_insert_of_ne hne]
      rw [show insert (χ₁ : ArithmeticFormula ℕ) (insert χ₂ (insert (∀⁰ φ) (Γ'.erase (χ₁ ⋎ χ₂))))
          = insert (∀⁰ φ) (insert χ₁ (insert χ₂ (Γ'.erase (χ₁ ⋎ χ₂)))) from by
        rw [Finset.insert_comm χ₂, Finset.insert_comm χ₁]]
      refine Zef2TC.allω hαN φ β hβ hβNF hαNF hβH ?_
      intro n
      refine Zef2TC.wk (ih n).gate ?_ (ih n)
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
      tauto
  | @exI α' β' e' H' F' c' Γ' hαN φ n hβ hβNF hαNF hβH hbound _ ih =>
      have hne : (∃⁰ φ : ArithmeticFormula ℕ) ≠ χ₁ ⋎ χ₂ := by simp
      rw [Finset.erase_insert_of_ne hne]
      rw [show insert (χ₁ : ArithmeticFormula ℕ) (insert χ₂ (insert (∃⁰ φ) (Γ'.erase (χ₁ ⋎ χ₂))))
          = insert (∃⁰ φ) (insert χ₁ (insert χ₂ (Γ'.erase (χ₁ ⋎ χ₂)))) from by
        rw [Finset.insert_comm χ₂, Finset.insert_comm χ₁]]
      refine Zef2TC.exI hαN φ n hβ hβNF hαNF hβH hbound ?_
      refine Zef2TC.wk ih.gate ?_ ih
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
      tauto
  | @cut α' βφ' βψ' e' H' F' c' Γ' hαN φ hcompl hcutRead hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH _ _ ih₁ ih₂ =>
      refine Zef2TC.cut hαN φ hcompl hcutRead hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH ?_ ?_
      · exact Zef2TC.wk ih₁.gate (hreshape φ Γ') ih₁
      · exact Zef2TC.wk ih₂.gate (hreshape (∼φ) Γ') ih₂

/-- ⊥-erase: `⊥` is never principal in `Zef2TC` (no rule introduces `falsum`), so it can be
erased from any context. -/
theorem falsum_erase {α e} {H} {f} {c}
    {Γ : Finset (ArithmeticFormula ℕ)} (dd : Zef2TC α e H f c Γ) :
      Zef2TC α e H f c (Γ.erase (⊥ : ArithmeticFormula ℕ)) := by
  have hreshape : ∀ (χ : ArithmeticFormula ℕ) (Γ : Finset (ArithmeticFormula ℕ)),
      (insert χ Γ).erase (⊥ : ArithmeticFormula ℕ) ⊆ insert χ (Γ.erase (⊥ : ArithmeticFormula ℕ)) := by
    intro χ Γ x hx
    simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
    tauto
  induction dd with
  | axL hαN r v hp hn =>
      exact Zef2TC.axL hαN r v
        (Finset.mem_erase.mpr ⟨by simp, hp⟩) (Finset.mem_erase.mpr ⟨by simp, hn⟩)
  | trueRel hαN r v htrue hmem =>
      exact Zef2TC.trueRel hαN r v htrue (Finset.mem_erase.mpr ⟨by simp, hmem⟩)
  | trueNrel hαN r v htrue hmem =>
      exact Zef2TC.trueNrel hαN r v htrue (Finset.mem_erase.mpr ⟨by simp, hmem⟩)
  | verumR hαN h =>
      exact Zef2TC.verumR hαN (Finset.mem_erase.mpr ⟨by simp, h⟩)
  | wk hαN hsub _ ih =>
      exact Zef2TC.wk hαN (Finset.erase_subset_erase _ hsub) ih
  | weak hαN hβ hβNF hαNF hβH hsub _ ih =>
      exact Zef2TC.weak hαN hβ hβNF hαNF hβH (Finset.erase_subset_erase _ hsub) ih
  | @andI α' βφ' βψ' e' H' F' c' Γ' hαN φ ψ hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH _ _ ih₁ ih₂ =>
      rw [Finset.erase_insert_of_ne (by simp : (φ ⋏ ψ : ArithmeticFormula ℕ) ≠ ⊥)]
      refine Zef2TC.andI hαN φ ψ hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH ?_ ?_
      · exact Zef2TC.wk ih₁.gate (hreshape φ Γ') ih₁
      · exact Zef2TC.wk ih₂.gate (hreshape ψ Γ') ih₂
  | @orI α' β' e' H' F' c' Γ' hαN φ ψ hβ hβNF hαNF hβH _ ih =>
      rw [Finset.erase_insert_of_ne (by simp : (φ ⋎ ψ : ArithmeticFormula ℕ) ≠ ⊥)]
      refine Zef2TC.orI hαN φ ψ hβ hβNF hαNF hβH ?_
      refine Zef2TC.wk ih.gate ?_ ih
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
      tauto
  | @allω α' e' H' F' c' Γ' hαN φ β hβ hβNF hαNF hβH _ ih =>
      rw [Finset.erase_insert_of_ne (by simp : (∀⁰ φ : ArithmeticFormula ℕ) ≠ ⊥)]
      refine Zef2TC.allω hαN φ β hβ hβNF hαNF hβH ?_
      intro n
      exact Zef2TC.wk (ih n).gate (hreshape _ Γ') (ih n)
  | @exI α' β' e' H' F' c' Γ' hαN φ n hβ hβNF hαNF hβH hbound _ ih =>
      rw [Finset.erase_insert_of_ne (by simp : (∃⁰ φ : ArithmeticFormula ℕ) ≠ ⊥)]
      refine Zef2TC.exI hαN φ n hβ hβNF hαNF hβH hbound ?_
      exact Zef2TC.wk ih.gate (hreshape _ Γ') ih
  | @cut α' βφ' βψ' e' H' F' c' Γ' hαN φ hcompl hcutRead hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH _ _ ih₁ ih₂ =>
      refine Zef2TC.cut hαN φ hcompl hcutRead hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH ?_ ?_
      · exact Zef2TC.wk ih₁.gate (hreshape φ Γ') ih₁
      · exact Zef2TC.wk ih₂.gate (hreshape (∼φ) Γ') ih₂

/-! ### The TC pass-port kit, part 2 — the ⋏/⋎ principal cut-reduction + ⊤/⊥ principal cuts

Block 12b: the finite mirror of `stepAllω_Zf2_bnd`.  A top-rank cut on `φ ⋏ ψ` reduces to two
nested LOWER-complexity cuts (on `ψ`, then `φ`) via the block-12a inversions.  No slot change,
no operator change; ordinal cost = two successors above the ordinal SUM of the premises
(`osucc (osucc (βφ + βψ))`) — strictly under `collapse α` at the pass's call site via
`collapse_add_lt` + limit headroom.  The gate is paid by the single slack hypothesis
`Nlog (βφ + βψ) + 2 ≤ f 0` (both successor gates ride `Nlog_osucc_le`).

The ⋎-principal cut is the SAME lemma with the premises swapped (`∼(φ ⋎ ψ) = ∼φ ⋏ ∼ψ`, and
`φ ⋎ ψ = ∼(∼φ) ⋎ ∼(∼ψ)` after double-negation cleanup — exactly how `passAux`'s `exs` case
reuses `all`).  The ⊤/⊥ principal cuts are FREE: `∼⊤ = ⊥` and ⊥ is never principal
(`falsum_erase`), so the ⊥-side premise already derives `Γ`. -/

end GoodsteinPA.E1EmbeddingGrind
