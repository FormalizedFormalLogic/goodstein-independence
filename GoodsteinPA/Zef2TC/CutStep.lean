module

public import GoodsteinPA.Zef2TC.Inversion

@[expose] public section

namespace GoodsteinPA.E1EmbeddingGrind

open LO LO.FirstOrder LO.FirstOrder.ArithmeticTerm ONote
open GoodsteinPA.OperatorZeh GoodsteinPA.OperatorZinfty

variable {e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Finset (ArithmeticFormula ℕ)}

/-- The ⋏-principal top-rank cut reduction: from `⊢ φ⋏ψ, Γ` and `⊢ ∼φ⋎∼ψ, Γ` (same slot `f`, rank
`c`), derive `Γ` at rank `c` and ordinal `osucc (osucc (βφ + βψ))`. -/
theorem stepAnd_Zef2TC {φ ψ} {βφ βψ}
    (hβφNF : βφ.NF) (hβψNF : βψ.NF)
    (hφc : φ.complexity < c) (hψc : ψ.complexity < c)
    (hφRead : φ.complexity ≤ f 0) (hψRead : ψ.complexity ≤ f 0)
    (hgate : Nlog (βφ + βψ) + 2 ≤ f 0)
    (D₁ : Zef2TC βφ e H f c (insert (φ ⋏ ψ) Γ))
    (D₂ : Zef2TC βψ e H f c (insert (∼φ ⋎ ∼ψ) Γ)) :
    Zef2TC (osucc (osucc (βφ + βψ))) e H f c Γ := by
  have hσNF : (βφ + βψ).NF := ONote.add_nf βφ βψ
  have hα₁NF : (osucc (βφ + βψ)).NF := osucc_NF hσNF
  have hα₂NF : (osucc (osucc (βφ + βψ))).NF := osucc_NF hα₁NF
  have hβφ1 : βφ < osucc (βφ + βψ) :=
    lt_of_le_of_lt (le_add_right_NF hβφNF hβψNF) (lt_osucc hσNF)
  have hβψ1 : βψ < osucc (βφ + βψ) :=
    lt_of_le_of_lt (le_add_left_NF hβφNF hβψNF) (lt_osucc hσNF)
  have h12 : osucc (βφ + βψ) < osucc (osucc (βφ + βψ)) := lt_osucc hα₁NF
  have hβφ2 : βφ < osucc (osucc (βφ + βψ)) := lt_trans hβφ1 h12
  have hα₁N : Nlog (osucc (βφ + βψ)) ≤ f 0 :=
    le_trans (Nlog_osucc_le hσNF) (by omega)
  have hα₂N : Nlog (osucc (osucc (βφ + βψ))) ≤ f 0 := by
    have h1 := Nlog_osucc_le hα₁NF
    have h2 := Nlog_osucc_le hσNF
    omega
  -- left ⋏-inversion → `⊢ φ, Γ` at `βφ`
  have PL : Zef2TC βφ e H f c (insert φ Γ) := by
    have A := and_inversion_left (χ₁ := φ) (χ₂ := ψ) D₁
    rw [Finset.erase_insert_eq_erase] at A
    exact Zef2TC.wk A.gate
      (Finset.insert_subset_insert _ (Finset.erase_subset _ _)) A
  -- right ⋏-inversion → `⊢ ψ, ∼φ, Γ` at `βφ`
  have PR : Zef2TC βφ e H f c (insert ψ (insert (∼φ) Γ)) := by
    have B := and_inversion_right (χ₁ := φ) (χ₂ := ψ) D₁
    rw [Finset.erase_insert_eq_erase] at B
    refine Zef2TC.wk B.gate ?_ B
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
    tauto
  -- ⋎-inversion → `⊢ ∼ψ, ∼φ, Γ` at `βψ`
  have PN : Zef2TC βψ e H f c (insert (∼ψ) (insert (∼φ) Γ)) := by
    have C := or_inversion (χ₁ := ∼φ) (χ₂ := ∼ψ) D₂
    rw [Finset.erase_insert_eq_erase] at C
    refine Zef2TC.wk C.gate ?_ C
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
    tauto
  -- inner cut on `ψ` → `⊢ ∼φ, Γ` at `osucc (βφ + βψ)`
  have cutψ : Zef2TC (osucc (βφ + βψ)) e H f c (insert (∼φ) Γ) :=
    Zef2TC.cut hα₁N ψ hψc hψRead hβφ1 hβψ1 hβφNF hβψNF hα₁NF
      (Cl_of_NF hβφNF) (Cl_of_NF hβψNF) PR PN
  -- outer cut on `φ` → `⊢ Γ`
  exact Zef2TC.cut hα₂N φ hφc hφRead hβφ2 h12 hβφNF hα₁NF hα₂NF
    (Cl_of_NF hβφNF) (Cl_of_NF hα₁NF) PL cutψ

/-! ### Atomic truth-leaf surgery: the atomic top-rank cut needs no splice

Over `Zef2TC`, exactly one of `rel rr vv` / `nrel rr vv` is `atomTrue` (`atomTrue_nrel_iff_not_rel`),
so the atomic top-rank cut dissolves by erasing the FALSE literal from its own premise, without the
`axL`-pair splice `atomCutRun_Zf2` needs. The only rules where the false literal could be
"principal" are `axL` (the pair leaf collapses to `trueRel`/`trueNrel` on the surviving TRUE half)
and the matching truth leaf itself (excluded by exclusivity). Same ordinal, same slot. -/

variable {ar : ℕ} {rr : (ℒₒᵣ).Rel ar} {vv : Fin ar → Semiterm ℒₒᵣ ℕ 0}

/-- Erase a FALSE `nrel` literal (its `rel` is `atomTrue`): never honestly principal. -/
lemma false_nrel_erase (htrue : atomTrue (Semiformula.rel rr vv)) {α : ONote}
    (dd : Zef2TC α e H f c Γ) :
      Zef2TC α e H f c (Γ.erase (Semiformula.nrel rr vv)) := by
  have hreshape : ∀ (χ : ArithmeticFormula ℕ) (Γ : Finset (ArithmeticFormula ℕ)),
      (insert χ Γ).erase (Semiformula.nrel rr vv)
        ⊆ insert χ (Γ.erase (Semiformula.nrel rr vv)) := by
    intro χ Γ x hx
    simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
    tauto
  induction dd with
  | @axL α' e' H' F' c' Γ' ar' hαN r v hp hn =>
      by_cases h : (Semiformula.nrel r v : ArithmeticFormula ℕ) = Semiformula.nrel rr vv
      · -- the pair leaf collapses to a `trueRel` leaf on the surviving TRUE half
        have hrel : (Semiformula.rel r v : ArithmeticFormula ℕ) = Semiformula.rel rr vv := by
          have := congrArg (∼·) h
          simpa using this
        have htrue' : atomTrue (Semiformula.rel r v) := by rw [hrel]; exact htrue
        exact Zef2TC.trueRel hαN r v htrue' (Finset.mem_erase.mpr ⟨by simp, hp⟩)
      · exact Zef2TC.axL hαN r v
          (Finset.mem_erase.mpr ⟨by simp, hp⟩) (Finset.mem_erase.mpr ⟨h, hn⟩)
  | trueRel hαN r v htrue' hmem =>
      exact Zef2TC.trueRel hαN r v htrue' (Finset.mem_erase.mpr ⟨by simp, hmem⟩)
  | @trueNrel α' e' H' F' c' Γ' ar' hαN r v htrue' hmem =>
      by_cases h : (Semiformula.nrel r v : ArithmeticFormula ℕ) = Semiformula.nrel rr vv
      · -- exclusivity: a TRUE `nrel` leaf on the FALSE literal is impossible
        rw [h] at htrue'
        exact absurd htrue ((atomTrue_nrel_iff_not_rel rr vv).mp htrue')
      · exact Zef2TC.trueNrel hαN r v htrue' (Finset.mem_erase.mpr ⟨h, hmem⟩)
  | verumR hαN h =>
      exact Zef2TC.verumR hαN (Finset.mem_erase.mpr ⟨by simp, h⟩)
  | wk hαN hsub _ ih =>
      exact Zef2TC.wk hαN (Finset.erase_subset_erase _ hsub) ih
  | weak hαN hβ hβNF hαNF hβH hsub _ ih =>
      exact Zef2TC.weak hαN hβ hβNF hαNF hβH (Finset.erase_subset_erase _ hsub) ih
  | @andI α' βφ' βψ' e' H' F' c' Γ' hαN φ ψ hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH _ _ ih₁ ih₂ =>
      rw [Finset.erase_insert_of_ne (by simp : (φ ⋏ ψ : ArithmeticFormula ℕ) ≠ Semiformula.nrel rr vv)]
      refine Zef2TC.andI hαN φ ψ hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH ?_ ?_
      · exact Zef2TC.wk ih₁.gate (hreshape φ Γ') ih₁
      · exact Zef2TC.wk ih₂.gate (hreshape ψ Γ') ih₂
  | @orI α' β' e' H' F' c' Γ' hαN φ ψ hβ hβNF hαNF hβH _ ih =>
      rw [Finset.erase_insert_of_ne (by simp : (φ ⋎ ψ : ArithmeticFormula ℕ) ≠ Semiformula.nrel rr vv)]
      refine Zef2TC.orI hαN φ ψ hβ hβNF hαNF hβH ?_
      refine Zef2TC.wk ih.gate ?_ ih
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
      tauto
  | @allω α' e' H' F' c' Γ' hαN φ β hβ hβNF hαNF hβH _ ih =>
      rw [Finset.erase_insert_of_ne (by simp : (∀⁰ φ : ArithmeticFormula ℕ) ≠ Semiformula.nrel rr vv)]
      refine Zef2TC.allω hαN φ β hβ hβNF hαNF hβH ?_
      intro n
      exact Zef2TC.wk (ih n).gate (hreshape _ Γ') (ih n)
  | @exI α' β' e' H' F' c' Γ' hαN φ n hβ hβNF hαNF hβH hbound _ ih =>
      rw [Finset.erase_insert_of_ne (by simp : (∃⁰ φ : ArithmeticFormula ℕ) ≠ Semiformula.nrel rr vv)]
      refine Zef2TC.exI hαN φ n hβ hβNF hαNF hβH hbound ?_
      exact Zef2TC.wk ih.gate (hreshape _ Γ') ih
  | @cut α' βφ' βψ' e' H' F' c' Γ' hαN φ hcompl hcutRead hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH _ _ ih₁ ih₂ =>
      refine Zef2TC.cut hαN φ hcompl hcutRead hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH ?_ ?_
      · exact Zef2TC.wk ih₁.gate (hreshape φ Γ') ih₁
      · exact Zef2TC.wk ih₂.gate (hreshape (∼φ) Γ') ih₂

/-- Erase a FALSE `rel` literal (its `nrel` is `atomTrue`): dual of `false_nrel_erase`. -/
lemma false_rel_erase (htrue : atomTrue (Semiformula.nrel rr vv)) {α : ONote}
    (dd : Zef2TC α e H f c Γ) :
      Zef2TC α e H f c (Γ.erase (Semiformula.rel rr vv)) := by
  have hreshape : ∀ (χ : ArithmeticFormula ℕ) (Γ : Finset (ArithmeticFormula ℕ)),
      (insert χ Γ).erase (Semiformula.rel rr vv)
        ⊆ insert χ (Γ.erase (Semiformula.rel rr vv)) := by
    intro χ Γ x hx
    simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
    tauto
  induction dd with
  | @axL α' e' H' F' c' Γ' ar' hαN r v hp hn =>
      by_cases h : (Semiformula.rel r v : ArithmeticFormula ℕ) = Semiformula.rel rr vv
      · -- the pair leaf collapses to a `trueNrel` leaf on the surviving TRUE half
        have hnrel : (Semiformula.nrel r v : ArithmeticFormula ℕ) = Semiformula.nrel rr vv := by
          have := congrArg (∼·) h
          simpa using this
        have htrue' : atomTrue (Semiformula.nrel r v) := by rw [hnrel]; exact htrue
        exact Zef2TC.trueNrel hαN r v htrue' (Finset.mem_erase.mpr ⟨by simp, hn⟩)
      · exact Zef2TC.axL hαN r v
          (Finset.mem_erase.mpr ⟨h, hp⟩) (Finset.mem_erase.mpr ⟨by simp, hn⟩)
  | @trueRel α' e' H' F' c' Γ' ar' hαN r v htrue' hmem =>
      by_cases h : (Semiformula.rel r v : ArithmeticFormula ℕ) = Semiformula.rel rr vv
      · rw [h] at htrue'
        exact absurd htrue ((atomTrue_rel_iff_not_nrel rr vv).mp htrue')
      · exact Zef2TC.trueRel hαN r v htrue' (Finset.mem_erase.mpr ⟨h, hmem⟩)
  | trueNrel hαN r v htrue' hmem =>
      exact Zef2TC.trueNrel hαN r v htrue' (Finset.mem_erase.mpr ⟨by simp, hmem⟩)
  | verumR hαN h =>
      exact Zef2TC.verumR hαN (Finset.mem_erase.mpr ⟨by simp, h⟩)
  | wk hαN hsub _ ih =>
      exact Zef2TC.wk hαN (Finset.erase_subset_erase _ hsub) ih
  | weak hαN hβ hβNF hαNF hβH hsub _ ih =>
      exact Zef2TC.weak hαN hβ hβNF hαNF hβH (Finset.erase_subset_erase _ hsub) ih
  | @andI α' βφ' βψ' e' H' F' c' Γ' hαN φ ψ hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH _ _ ih₁ ih₂ =>
      rw [Finset.erase_insert_of_ne (by simp : (φ ⋏ ψ : ArithmeticFormula ℕ) ≠ Semiformula.rel rr vv)]
      refine Zef2TC.andI hαN φ ψ hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH ?_ ?_
      · exact Zef2TC.wk ih₁.gate (hreshape φ Γ') ih₁
      · exact Zef2TC.wk ih₂.gate (hreshape ψ Γ') ih₂
  | @orI α' β' e' H' F' c' Γ' hαN φ ψ hβ hβNF hαNF hβH _ ih =>
      rw [Finset.erase_insert_of_ne (by simp : (φ ⋎ ψ : ArithmeticFormula ℕ) ≠ Semiformula.rel rr vv)]
      refine Zef2TC.orI hαN φ ψ hβ hβNF hαNF hβH ?_
      refine Zef2TC.wk ih.gate ?_ ih
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
      tauto
  | @allω α' e' H' F' c' Γ' hαN φ β hβ hβNF hαNF hβH _ ih =>
      rw [Finset.erase_insert_of_ne (by simp : (∀⁰ φ : ArithmeticFormula ℕ) ≠ Semiformula.rel rr vv)]
      refine Zef2TC.allω hαN φ β hβ hβNF hαNF hβH ?_
      intro n
      exact Zef2TC.wk (ih n).gate (hreshape _ Γ') (ih n)
  | @exI α' β' e' H' F' c' Γ' hαN φ n hβ hβNF hαNF hβH hbound _ ih =>
      rw [Finset.erase_insert_of_ne (by simp : (∃⁰ φ : ArithmeticFormula ℕ) ≠ Semiformula.rel rr vv)]
      refine Zef2TC.exI hαN φ n hβ hβNF hαNF hβH hbound ?_
      exact Zef2TC.wk ih.gate (hreshape _ Γ') ih
  | @cut α' βφ' βψ' e' H' F' c' Γ' hαN φ hcompl hcutRead hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH _ _ ih₁ ih₂ =>
      refine Zef2TC.cut hαN φ hcompl hcutRead hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH ?_ ?_
      · exact Zef2TC.wk ih₁.gate (hreshape φ Γ') ih₁
      · exact Zef2TC.wk ih₂.gate (hreshape (∼φ) Γ') ih₂

/-- The atomic top-rank cut reduction over `Zef2TC`: from `⊢ rel rr vv, Γ` and `⊢ nrel rr vv, Γ`
(same slot `f`, rank `c`), derive `Γ` at rank `c` and ordinal `osucc (βφ + βψ)`. -/
theorem stepAtom_Zef2TC {βφ βψ : ONote}
    (hβφNF : βφ.NF) (hβψNF : βψ.NF)
    (hgate : Nlog (βφ + βψ) + 1 ≤ f 0)
    (D₁ : Zef2TC βφ e H f c (insert (Semiformula.rel rr vv) Γ))
    (D₂ : Zef2TC βψ e H f c (insert (Semiformula.nrel rr vv) Γ)) :
    Zef2TC (osucc (βφ + βψ)) e H f c Γ := by
  have hσNF : (βφ + βψ).NF := ONote.add_nf βφ βψ
  have hα₁NF : (osucc (βφ + βψ)).NF := osucc_NF hσNF
  have hα₁N : Nlog (osucc (βφ + βψ)) ≤ f 0 :=
    le_trans (Nlog_osucc_le hσNF) (by omega)
  by_cases htrue : atomTrue (Semiformula.rel rr vv)
  · -- `nrel` is FALSE: erase it from `D₂`
    have E := false_nrel_erase htrue D₂
    rw [Finset.erase_insert_eq_erase] at E
    have E' : Zef2TC βψ e H f c Γ := Zef2TC.wk E.gate (Finset.erase_subset _ _) E
    exact Zef2TC.weak hα₁N
      (lt_of_le_of_lt (le_add_left_NF hβφNF hβψNF) (lt_osucc hσNF))
      hβψNF hα₁NF (Cl_of_NF hβψNF) (Finset.Subset.refl _) E'
  · -- `rel` is FALSE: erase it from `D₁`
    have hntrue : atomTrue (Semiformula.nrel rr vv) :=
      (atomTrue_nrel_iff_not_rel rr vv).mpr htrue
    have E := false_rel_erase hntrue D₁
    rw [Finset.erase_insert_eq_erase] at E
    have E' : Zef2TC βφ e H f c Γ := Zef2TC.wk E.gate (Finset.erase_subset _ _) E
    exact Zef2TC.weak hα₁N
      (lt_of_le_of_lt (le_add_right_NF hβφNF hβψNF) (lt_osucc hσNF))
      hβφNF hα₁NF (Cl_of_NF hβφNF) (Finset.Subset.refl _) E'

/-- The ⊤-principal top-rank cut reduction: since `∼⊤ = ⊥` is never principal, `⊢ ⊥, Γ` at
ordinal `βψ` already derives `Γ` at the same ordinal `βψ`. -/
theorem stepVerum_Zef2TC {βψ : ONote}
    (D₂ : Zef2TC βψ e H f c (insert (⊥ : ArithmeticFormula ℕ) Γ)) :
    Zef2TC βψ e H f c Γ := by
  have C := falsum_erase D₂
  rw [Finset.erase_insert_eq_erase] at C
  exact Zef2TC.wk C.gate (Finset.erase_subset _ _) C

end GoodsteinPA.E1EmbeddingGrind
