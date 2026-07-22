module

public import GoodsteinPA.Zef2TC.Basic

@[expose] public section

namespace GoodsteinPA.E1EmbeddingGrind

open LO LO.FirstOrder LO.FirstOrder.ArithmeticTerm ONote
open GoodsteinPA.OperatorZeh GoodsteinPA.OperatorZinfty

variable {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Finset (ArithmeticFormula ℕ)}

/-! ### Finset reshaping helpers

Pure `Finset` erase/insert commutation facts, reused across every inversion lemma below. -/

private lemma inv1_push (A e b : ArithmeticFormula ℕ) (s : Finset (ArithmeticFormula ℕ)) :
    insert e ((insert b s).erase A) ⊆ insert b (insert e (s.erase A)) := by
  intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto

private lemma inv2_push (A e₁ e₂ b : ArithmeticFormula ℕ) (s : Finset (ArithmeticFormula ℕ)) :
    insert e₁ (insert e₂ ((insert b s).erase A)) ⊆ insert b (insert e₁ (insert e₂ (s.erase A))) := by
  intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto

/-- Single-formula variant with the head split over two inserts (an `orI` branch's context). -/
private lemma inv1_push' (A e b₁ b₂ : ArithmeticFormula ℕ) (s : Finset (ArithmeticFormula ℕ)) :
    insert e ((insert b₁ (insert b₂ s)).erase A) ⊆ insert b₁ (insert b₂ (insert e (s.erase A))) := by
  intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto

private lemma erase_insert_subset (A b : ArithmeticFormula ℕ) (s : Finset (ArithmeticFormula ℕ)) :
    (insert b s).erase A ⊆ insert b (s.erase A) := by
  intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto

/-- No-formula variant with the head split over two inserts (an `orI` branch, `⊥`-erase form). -/
private lemma erase_insert_subset' (A b₁ b₂ : ArithmeticFormula ℕ) (s : Finset (ArithmeticFormula ℕ)) :
    (insert b₁ (insert b₂ s)).erase A ⊆ insert b₁ (insert b₂ (s.erase A)) := by
  intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto

/-- Collapse a duplicated instance: erasing `A` from `insert χ Γ` and reinserting `χ` (with
`χ ≠ A`) is the same as discharging `A` from `Γ` and inserting `χ` once. -/
private lemma insert_erase_idem {χ A : ArithmeticFormula ℕ} (hne : χ ≠ A) (Γ : Finset (ArithmeticFormula ℕ)) :
    insert χ ((insert χ Γ).erase A) = insert χ (Γ.erase A) := by
  rw [Finset.erase_insert_of_ne hne]; exact Finset.insert_idem _ _

/-- `f` dominates its own `m`-relativized slot `rel1 f m`, for monotone `f`. -/
private lemma f_le_rel1 (hf : Monotone f) (m x : ℕ) : f x ≤ rel1 f m x := hf (le_max_right m x)

/-! ### `allω`-inversion

Replays a `Zef2TC` derivation at branch slot `rel1 f m`, replacing `∀⁰ φ` by its `m`-th numeral
instance throughout the context.  Every gate `≤ f 0` lifts to `≤ rel1 f m 0` by monotonicity of
`f`, and nested ω-branches commute via `rel1_rel1` + `max_comm`.

- [Tow20, Theorem 19.4]
-/
lemma allω_inversion {φ : ArithmeticSemiformula ℕ 1} (m : ℕ)
    (dd : Zef2TC α e H f c Γ) (hmono : Monotone f) :
    Zef2TC α e H (rel1 f m) c (insert (φ/[nm m]) (Γ.erase (∀⁰ φ))) := by
  induction dd with
  | axL hαN r v hp hn =>
      refine Zef2TC.axL (le_trans hαN (f_le_rel1 hmono m 0)) r v ?_ ?_
      · exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨by simp, hp⟩)
      · exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨by simp, hn⟩)
  | trueRel hαN r v htrue hmem =>
      exact Zef2TC.trueRel (le_trans hαN (f_le_rel1 hmono m 0)) r v htrue
        (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨by simp, hmem⟩))
  | trueNrel hαN r v htrue hmem =>
      exact Zef2TC.trueNrel (le_trans hαN (f_le_rel1 hmono m 0)) r v htrue
        (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨by simp, hmem⟩))
  | verumR hαN h =>
      exact Zef2TC.verumR (le_trans hαN (f_le_rel1 hmono m 0))
        (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨by simp, h⟩))
  | wk hαN hsub _ ih =>
      exact Zef2TC.wk (le_trans hαN (f_le_rel1 hmono m 0))
        (Finset.insert_subset_insert _ (Finset.erase_subset_erase _ hsub)) (ih hmono)
  | @weak α' β' e' H' F' c' Δ' Γ' hαN hβ hβNF hαNF hβH hsub _ ih =>
      exact Zef2TC.weak (le_trans hαN (f_le_rel1 hmono m 0)) hβ hβNF hαNF hβH
        (Finset.insert_subset_insert _ (Finset.erase_subset_erase _ hsub)) (ih hmono)
  | @andI α' βφ' βψ' e' H' F' c' Γ' hαN χ₁ χ₂ hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH _ _ ih₁ ih₂ =>
      have hne : χ₁ ⋏ χ₂ ≠ ∀⁰ φ := by simp
      rw [Finset.erase_insert_of_ne hne, Finset.insert_comm]
      refine Zef2TC.andI (le_trans hαN (f_le_rel1 hmono m 0)) χ₁ χ₂ hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH ?_ ?_
      · exact Zef2TC.wk (ih₁ hmono).gate (inv1_push _ _ _ Γ') (ih₁ hmono)
      · exact Zef2TC.wk (ih₂ hmono).gate (inv1_push _ _ _ Γ') (ih₂ hmono)
  | @orI α' β' e' H' F' c' Γ' hαN χ₁ χ₂ hβ hβNF hαNF hβH _ ih =>
      have hne : χ₁ ⋎ χ₂ ≠ ∀⁰ φ := by simp
      rw [Finset.erase_insert_of_ne hne, Finset.insert_comm]
      exact Zef2TC.orI (le_trans hαN (f_le_rel1 hmono m 0)) χ₁ χ₂ hβ hβNF hαNF hβH
        (Zef2TC.wk (ih hmono).gate (inv1_push' _ _ _ _ Γ') (ih hmono))
  | @allω α' e' H' F' c' Γ' hαN χ β hβ hβNF hαNF hβH dd ih =>
      by_cases hchi : (∀⁰ χ : ArithmeticFormula ℕ) = ∀⁰ φ
      · -- PRINCIPAL: take branch m, re-invert it, drop the duplicate instance
        have hφχ : χ = φ := by simpa using hchi
        subst hφχ
        have hbr := ih m (rel1_monotone hmono m)
        rw [rel1_rel1, max_self] at hbr -- slot: rel1 (rel1 f m) m = rel1 f m
        rw [insert_erase_idem (Semiformula.ne_of_ne_complexity (by simp)) Γ'] at hbr
        refine Zef2TC.weak (le_trans hαN (f_le_rel1 hmono m 0)) (hβ m) (hβNF m) hαNF (Cl_of_NF (hβNF m))
          ?_ hbr.change_H
        rw [Finset.erase_insert_eq_erase]
      · -- NON-PRINCIPAL: rebuild the ω-rule over the inverted branches
        rw [Finset.erase_insert_of_ne hchi, Finset.insert_comm]
        refine Zef2TC.allω (le_trans hαN (f_le_rel1 hmono m 0)) χ β hβ hβNF hαNF (fun n => hβH n) ?_
        intro n
        have h := ih n (rel1_monotone hmono n)
        rw [rel1_rel1, max_comm n m, ← rel1_rel1] at h
        exact Zef2TC.wk (h.change_H (H' := adjoin H' n)).gate (inv1_push _ _ _ Γ')
          (h.change_H (H' := adjoin H' n))
  | @exI α' β' e' H' F' c' Γ' hαN χ n hβ hβNF hαNF hβH hbound _ ih =>
      have hne : (∃⁰ χ : ArithmeticFormula ℕ) ≠ ∀⁰ φ := by simp
      rw [Finset.erase_insert_of_ne hne, Finset.insert_comm]
      exact Zef2TC.exI (le_trans hαN (f_le_rel1 hmono m 0)) χ n hβ hβNF hαNF hβH
        (le_trans hbound (f_le_rel1 hmono m 0)) (Zef2TC.wk (ih hmono).gate (inv1_push _ _ _ Γ') (ih hmono))
  | @cut α' βφ' βψ' e' H' F' c' Γ' hαN χ hcompl hcutRead hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH _ _ ih₁ ih₂ =>
      refine Zef2TC.cut (le_trans hαN (f_le_rel1 hmono m 0)) χ hcompl (le_trans hcutRead (f_le_rel1 hmono m 0))
        hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH ?_ ?_
      · exact Zef2TC.wk (ih₁ hmono).gate (inv1_push _ _ _ Γ') (ih₁ hmono)
      · exact Zef2TC.wk (ih₂ hmono).gate (inv1_push _ _ _ Γ') (ih₂ hmono)

/-! ### Propositional inversions and `⊥`-erase

The finite mirrors of `allω_inversion` for `⋏`/`⋎`: no slot or operator change, since `Zef2TC`'s
`andI`/`orI` rules make these connectives principal.  `⊥` is never principal (no rule introduces
`falsum`), so it can always be erased from a context. -/

variable {χ₁ χ₂ : ArithmeticFormula ℕ}

/-- Left `⋏`-inversion: replace `χ₁ ⋏ χ₂` by `χ₁` throughout, at the same ordinal/slot/rank.

- [Tow20, Theorem 19.3]
-/
lemma and_inversion_left (dd : Zef2TC α e H f c Γ) :
    Zef2TC α e H f c (insert χ₁ (Γ.erase (χ₁ ⋏ χ₂))) := by
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
        rw [insert_erase_idem (Semiformula.ne_of_ne_complexity (by simp)) Γ'] at ih₁
        refine Zef2TC.weak hαN hβφ hβφNF hαNF hβφH ?_ ih₁
        rw [hchi, Finset.erase_insert_eq_erase]
      · rw [Finset.erase_insert_of_ne hchi, Finset.insert_comm]
        refine Zef2TC.andI hαN φ ψ hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH ?_ ?_
        · exact Zef2TC.wk ih₁.gate (inv1_push _ _ _ Γ') ih₁
        · exact Zef2TC.wk ih₂.gate (inv1_push _ _ _ Γ') ih₂
  | @orI α' β' e' H' F' c' Γ' hαN φ ψ hβ hβNF hαNF hβH _ ih =>
      have hne : (φ ⋎ ψ : ArithmeticFormula ℕ) ≠ χ₁ ⋏ χ₂ := by simp
      rw [Finset.erase_insert_of_ne hne, Finset.insert_comm]
      exact Zef2TC.orI hαN φ ψ hβ hβNF hαNF hβH (Zef2TC.wk ih.gate (inv1_push' _ _ _ _ Γ') ih)
  | @allω α' e' H' F' c' Γ' hαN φ β hβ hβNF hαNF hβH _ ih =>
      have hne : (∀⁰ φ : ArithmeticFormula ℕ) ≠ χ₁ ⋏ χ₂ := by simp
      rw [Finset.erase_insert_of_ne hne, Finset.insert_comm]
      refine Zef2TC.allω hαN φ β hβ hβNF hαNF hβH ?_
      intro n; exact Zef2TC.wk (ih n).gate (inv1_push _ _ _ Γ') (ih n)
  | @exI α' β' e' H' F' c' Γ' hαN φ n hβ hβNF hαNF hβH hbound _ ih =>
      have hne : (∃⁰ φ : ArithmeticFormula ℕ) ≠ χ₁ ⋏ χ₂ := by simp
      rw [Finset.erase_insert_of_ne hne, Finset.insert_comm]
      exact Zef2TC.exI hαN φ n hβ hβNF hαNF hβH hbound (Zef2TC.wk ih.gate (inv1_push _ _ _ Γ') ih)
  | @cut α' βφ' βψ' e' H' F' c' Γ' hαN φ hcompl hcutRead hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH _ _ ih₁ ih₂ =>
      refine Zef2TC.cut hαN φ hcompl hcutRead hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH ?_ ?_
      · exact Zef2TC.wk ih₁.gate (inv1_push _ _ _ Γ') ih₁
      · exact Zef2TC.wk ih₂.gate (inv1_push _ _ _ Γ') ih₂

/-- Right `⋏`-inversion: replace `χ₁ ⋏ χ₂` by `χ₂` throughout, at the same ordinal/slot/rank.

- [Tow20, Theorem 19.3]
-/
lemma and_inversion_right (dd : Zef2TC α e H f c Γ) :
    Zef2TC α e H f c (insert χ₂ (Γ.erase (χ₁ ⋏ χ₂))) := by
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
        rw [insert_erase_idem (Semiformula.ne_of_ne_complexity (by simp)) Γ'] at ih₂
        refine Zef2TC.weak hαN hβψ hβψNF hαNF hβψH ?_ ih₂
        rw [hchi, Finset.erase_insert_eq_erase]
      · rw [Finset.erase_insert_of_ne hchi, Finset.insert_comm]
        refine Zef2TC.andI hαN φ ψ hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH ?_ ?_
        · exact Zef2TC.wk ih₁.gate (inv1_push _ _ _ Γ') ih₁
        · exact Zef2TC.wk ih₂.gate (inv1_push _ _ _ Γ') ih₂
  | @orI α' β' e' H' F' c' Γ' hαN φ ψ hβ hβNF hαNF hβH _ ih =>
      have hne : (φ ⋎ ψ : ArithmeticFormula ℕ) ≠ χ₁ ⋏ χ₂ := by simp
      rw [Finset.erase_insert_of_ne hne, Finset.insert_comm]
      exact Zef2TC.orI hαN φ ψ hβ hβNF hαNF hβH (Zef2TC.wk ih.gate (inv1_push' _ _ _ _ Γ') ih)
  | @allω α' e' H' F' c' Γ' hαN φ β hβ hβNF hαNF hβH _ ih =>
      have hne : (∀⁰ φ : ArithmeticFormula ℕ) ≠ χ₁ ⋏ χ₂ := by simp
      rw [Finset.erase_insert_of_ne hne, Finset.insert_comm]
      refine Zef2TC.allω hαN φ β hβ hβNF hαNF hβH ?_
      intro n; exact Zef2TC.wk (ih n).gate (inv1_push _ _ _ Γ') (ih n)
  | @exI α' β' e' H' F' c' Γ' hαN φ n hβ hβNF hαNF hβH hbound _ ih =>
      have hne : (∃⁰ φ : ArithmeticFormula ℕ) ≠ χ₁ ⋏ χ₂ := by simp
      rw [Finset.erase_insert_of_ne hne, Finset.insert_comm]
      exact Zef2TC.exI hαN φ n hβ hβNF hαNF hβH hbound (Zef2TC.wk ih.gate (inv1_push _ _ _ Γ') ih)
  | @cut α' βφ' βψ' e' H' F' c' Γ' hαN φ hcompl hcutRead hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH _ _ ih₁ ih₂ =>
      refine Zef2TC.cut hαN φ hcompl hcutRead hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH ?_ ?_
      · exact Zef2TC.wk ih₁.gate (inv1_push _ _ _ Γ') ih₁
      · exact Zef2TC.wk ih₂.gate (inv1_push _ _ _ Γ') ih₂

/-- `⋎`-inversion: replace `χ₁ ⋎ χ₂` by both disjuncts, at the same ordinal/slot/rank. `∨`-
inversion is standard and has no dedicated theorem number in `[Tow20]` (`∨` is
symmetric/trivial there). -/
lemma or_inversion (dd : Zef2TC α e H f c Γ) :
    Zef2TC α e H f c (insert χ₁ (insert χ₂ (Γ.erase (χ₁ ⋎ χ₂)))) := by
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
      rw [Finset.erase_insert_of_ne hne,
        show insert (χ₁ : ArithmeticFormula ℕ) (insert χ₂ (insert (φ ⋏ ψ) (Γ'.erase (χ₁ ⋎ χ₂))))
          = insert (φ ⋏ ψ) (insert χ₁ (insert χ₂ (Γ'.erase (χ₁ ⋎ χ₂)))) from by
          rw [Finset.insert_comm χ₂, Finset.insert_comm χ₁]]
      refine Zef2TC.andI hαN φ ψ hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH ?_ ?_
      · exact Zef2TC.wk ih₁.gate (inv2_push _ _ _ _ Γ') ih₁
      · exact Zef2TC.wk ih₂.gate (inv2_push _ _ _ _ Γ') ih₂
  | @orI α' β' e' H' F' c' Γ' hαN φ ψ hβ hβNF hαNF hβH d₁ ih =>
      by_cases hchi : (φ ⋎ ψ : ArithmeticFormula ℕ) = χ₁ ⋎ χ₂
      · -- PRINCIPAL: the premise carries BOTH disjuncts; re-invert and clean up
        have hφ₁ : φ = χ₁ ∧ ψ = χ₂ := by simpa using hchi
        obtain ⟨rfl, rfl⟩ := hφ₁
        have hctx : insert (φ : ArithmeticFormula ℕ) (insert ψ
              ((insert φ (insert ψ Γ')).erase (φ ⋎ ψ)))
            = insert φ (insert ψ (Γ'.erase (φ ⋎ ψ))) := by
          rw [Finset.erase_insert_of_ne (a := φ) (Semiformula.ne_of_ne_complexity (by simp)),
            Finset.erase_insert_of_ne (a := ψ) (Semiformula.ne_of_ne_complexity (by simp))]
          ext x; simp only [Finset.mem_insert]; tauto
        rw [hctx] at ih
        refine Zef2TC.weak hαN hβ hβNF hαNF hβH ?_ ih
        rw [hchi, Finset.erase_insert_eq_erase]
      · rw [Finset.erase_insert_of_ne hchi,
          show insert (χ₁ : ArithmeticFormula ℕ) (insert χ₂ (insert (φ ⋎ ψ) (Γ'.erase (χ₁ ⋎ χ₂))))
            = insert (φ ⋎ ψ) (insert χ₁ (insert χ₂ (Γ'.erase (χ₁ ⋎ χ₂)))) from by
            rw [Finset.insert_comm χ₂, Finset.insert_comm χ₁]]
        refine Zef2TC.orI hαN φ ψ hβ hβNF hαNF hβH (Zef2TC.wk ih.gate ?_ ih)
        intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto
  | @allω α' e' H' F' c' Γ' hαN φ β hβ hβNF hαNF hβH _ ih =>
      have hne : (∀⁰ φ : ArithmeticFormula ℕ) ≠ χ₁ ⋎ χ₂ := by simp
      rw [Finset.erase_insert_of_ne hne,
        show insert (χ₁ : ArithmeticFormula ℕ) (insert χ₂ (insert (∀⁰ φ) (Γ'.erase (χ₁ ⋎ χ₂))))
          = insert (∀⁰ φ) (insert χ₁ (insert χ₂ (Γ'.erase (χ₁ ⋎ χ₂)))) from by
          rw [Finset.insert_comm χ₂, Finset.insert_comm χ₁]]
      refine Zef2TC.allω hαN φ β hβ hβNF hαNF hβH ?_
      intro n; exact Zef2TC.wk (ih n).gate (inv2_push _ _ _ _ Γ') (ih n)
  | @exI α' β' e' H' F' c' Γ' hαN φ n hβ hβNF hαNF hβH hbound _ ih =>
      have hne : (∃⁰ φ : ArithmeticFormula ℕ) ≠ χ₁ ⋎ χ₂ := by simp
      rw [Finset.erase_insert_of_ne hne,
        show insert (χ₁ : ArithmeticFormula ℕ) (insert χ₂ (insert (∃⁰ φ) (Γ'.erase (χ₁ ⋎ χ₂))))
          = insert (∃⁰ φ) (insert χ₁ (insert χ₂ (Γ'.erase (χ₁ ⋎ χ₂)))) from by
          rw [Finset.insert_comm χ₂, Finset.insert_comm χ₁]]
      exact Zef2TC.exI hαN φ n hβ hβNF hαNF hβH hbound (Zef2TC.wk ih.gate (inv2_push _ _ _ _ Γ') ih)
  | @cut α' βφ' βψ' e' H' F' c' Γ' hαN φ hcompl hcutRead hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH _ _ ih₁ ih₂ =>
      refine Zef2TC.cut hαN φ hcompl hcutRead hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH ?_ ?_
      · exact Zef2TC.wk ih₁.gate (inv2_push _ _ _ _ Γ') ih₁
      · exact Zef2TC.wk ih₂.gate (inv2_push _ _ _ _ Γ') ih₂

/-- `⊥`-erase: `⊥` is never principal in `Zef2TC` (no rule introduces `falsum`), so it can be
erased from any context. -/
lemma falsum_erase (dd : Zef2TC α e H f c Γ) :
    Zef2TC α e H f c (Γ.erase (⊥ : ArithmeticFormula ℕ)) := by
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
      · exact Zef2TC.wk ih₁.gate (erase_insert_subset _ φ Γ') ih₁
      · exact Zef2TC.wk ih₂.gate (erase_insert_subset _ ψ Γ') ih₂
  | @orI α' β' e' H' F' c' Γ' hαN φ ψ hβ hβNF hαNF hβH _ ih =>
      rw [Finset.erase_insert_of_ne (by simp : (φ ⋎ ψ : ArithmeticFormula ℕ) ≠ ⊥)]
      exact Zef2TC.orI hαN φ ψ hβ hβNF hαNF hβH (Zef2TC.wk ih.gate (erase_insert_subset' _ φ ψ Γ') ih)
  | @allω α' e' H' F' c' Γ' hαN φ β hβ hβNF hαNF hβH _ ih =>
      rw [Finset.erase_insert_of_ne (by simp : (∀⁰ φ : ArithmeticFormula ℕ) ≠ ⊥)]
      refine Zef2TC.allω hαN φ β hβ hβNF hαNF hβH ?_
      intro n; exact Zef2TC.wk (ih n).gate (erase_insert_subset _ _ Γ') (ih n)
  | @exI α' β' e' H' F' c' Γ' hαN φ n hβ hβNF hαNF hβH hbound _ ih =>
      rw [Finset.erase_insert_of_ne (by simp : (∃⁰ φ : ArithmeticFormula ℕ) ≠ ⊥)]
      exact Zef2TC.exI hαN φ n hβ hβNF hαNF hβH hbound (Zef2TC.wk ih.gate (erase_insert_subset _ _ Γ') ih)
  | @cut α' βφ' βψ' e' H' F' c' Γ' hαN φ hcompl hcutRead hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH _ _ ih₁ ih₂ =>
      refine Zef2TC.cut hαN φ hcompl hcutRead hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH ?_ ?_
      · exact Zef2TC.wk ih₁.gate (erase_insert_subset _ φ Γ') ih₁
      · exact Zef2TC.wk ih₂.gate (erase_insert_subset _ (∼φ) Γ') ih₂

end GoodsteinPA.E1EmbeddingGrind
