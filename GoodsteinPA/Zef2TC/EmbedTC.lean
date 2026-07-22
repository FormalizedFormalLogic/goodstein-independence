module

public import GoodsteinPA.Zef2TC.Em

@[expose] public section

namespace GoodsteinPA.E1EmbeddingGrind

open LO LO.FirstOrder LO.FirstOrder.ArithmeticTerm ONote Ordinal
open GoodsteinPA.OperatorZeh GoodsteinPA.OperatorZinfty

/-! ### The master predicate and the `Derivation2` case ladder -/

variable {Γ : Finset (ArithmeticFormula ℕ)}

/-- `Γ` is `Zef2TC`-embeddable at some structural budgets `B` (slot), `d` (cut rank), `e`
(control tower), with a per-assignment env-local relativization index `K` and node ordinal `α`;
the operator is fixed at the full closure `Cl (⊤)`. -/
def BudgetedEmbedsTC (Γ : Finset (ArithmeticFormula ℕ)) : Prop :=
  ∃ B d : ℕ, ∃ e : ONote, e.NF ∧ ∀ env : ℕ → ℕ, ∃ K : ℕ, ∃ α : ONote, α.NF ∧
    Zef2TC α e (fun _ => True) (rel1 (ewRootSlot e B) K) d
      (Γ.image (fun φ => asg env ▹ φ))
/-- The `closed` case: `Γ` embeds when it contains both a formula and its negation. -/
theorem budgetedEmbedsTC_closed
    (φ : ArithmeticFormula ℕ) (hp : φ ∈ Γ) (hn : ∼φ ∈ Γ) :
    BudgetedEmbedsTC Γ := by
  refine ⟨clog (2 * φ.complexity + 1), 0, 0, ONote.NF.zero, fun env => ?_⟩
  refine ⟨0, ONote.ofNat (2 * (asg env ▹ φ).complexity + 1), ONote.nf_ofNat _, ?_⟩
  have hf1 := ewRootSlot_f1 0 (clog (2 * φ.complexity + 1))
  have hmono : Monotone (rel1 (ewRootSlot 0 (clog (2 * φ.complexity + 1))) 0) :=
    rel1_monotone hf1.1.monotone 0
  have hinfl : ∀ m, m ≤ rel1 (ewRootSlot 0 (clog (2 * φ.complexity + 1))) 0 m :=
    rel1_infl (fun m => by have := hf1.2 m; omega) 0
  have hgate : clog (2 * (asg env ▹ φ).complexity + 1)
      ≤ rel1 (ewRootSlot 0 (clog (2 * φ.complexity + 1))) 0 0 := by
    simp only [Semiformula.complexity_rew]
    exact le_relSlot_zero 0 _ 0
  exact em_Zef2TC' (asg env ▹ φ) hmono hinfl hgate
    (Finset.mem_image_of_mem _ hp)
    (by simpa using Finset.mem_image_of_mem (fun ψ => asg env ▹ ψ) hn)

/-- The `verum` case: `Γ` embeds when it contains `⊤`. -/
theorem budgetedEmbedsTC_verum
    (h : (⊤ : ArithmeticFormula ℕ) ∈ Γ) :
    BudgetedEmbedsTC Γ := by
  refine ⟨0, 0, 0, ONote.NF.zero, fun env => ⟨0, 0, ONote.NF.zero, ?_⟩⟩
  have hmem : (⊤ : ArithmeticFormula ℕ) ∈ Γ.image (fun ψ => asg env ▹ ψ) := by
    have := Finset.mem_image_of_mem (fun ψ => asg env ▹ ψ) h
    simpa using this
  exact Zef2TC.verumR (by simp) hmem

/-- The `wk` case: weakening from a subset `Δ` to `Γ`. -/
theorem budgetedEmbedsTC_wk {Δ}
    (hsub : Δ ⊆ Γ) (ih : BudgetedEmbedsTC Δ) :
    BudgetedEmbedsTC Γ := by
  obtain ⟨B, d, e, he, ih⟩ := ih
  refine ⟨B, d, e, he, fun env => ?_⟩
  obtain ⟨K, α, hαNF, D⟩ := ih env
  exact ⟨K, α, hαNF, D.wk D.gate (Finset.image_subset_image hsub)⟩

/-- The `shift` case: `Γ` embeds implies its `Rewriting.shift`-image also embeds. -/
theorem budgetedEmbedsTC_shift
    (ih : BudgetedEmbedsTC Γ) :
    BudgetedEmbedsTC (Γ.image Rewriting.shift) := by
  obtain ⟨B, d, e, he, ih⟩ := ih
  refine ⟨B, d, e, he, fun env => ?_⟩
  obtain ⟨K, α, hαNF, D⟩ := ih (fun x => env (x + 1))
  refine ⟨K, α, hαNF, ?_⟩
  have himg : (Γ.image (Rewriting.shift : ArithmeticFormula ℕ → ArithmeticFormula ℕ)).image
        (fun φ => asg env ▹ φ)
      = Γ.image (fun φ => asg (fun x => env (x + 1)) ▹ φ) := by
    have hcompB : (asg env).comp Rew.shift
        = asg (fun x => env (x + 1)) := by
      ext x
      · exact Fin.elim0 x
      · simp [asg, Rew.comp_app]
    rw [Finset.image_image]
    refine Finset.image_congr (fun ψ _ => ?_)
    show asg env ▹ (Rew.shift ▹ ψ) = asg (fun x => env (x + 1)) ▹ ψ
    rw [← TransitiveRewriting.comp_app, hcompB]
  rwa [himg]

/-- The `or` case: `φ ⋎ ψ ∈ Γ` and `insert φ (insert ψ Γ)` embeds implies `Γ` embeds. -/
theorem budgetedEmbedsTC_or
    {φ ψ : ArithmeticFormula ℕ} (h : φ ⋎ ψ ∈ Γ)
    (ih : BudgetedEmbedsTC (insert φ (insert ψ Γ))) :
    BudgetedEmbedsTC Γ := by
  obtain ⟨B, d, e, he, ih⟩ := ih
  refine ⟨B, d, e, he, fun env => ?_⟩
  obtain ⟨K, α, hαNF, D⟩ := ih env
  refine ⟨K + 1, osucc α, osucc_NF hαNF, ?_⟩
  have hgate := D.gate
  rw [Finset.image_insert, Finset.image_insert] at D
  have D' := D.mono_f (relSlot_mono (le_refl B) (Nat.le_succ K))
  have hg : Nlog (osucc α) ≤ rel1 (ewRootSlot e B) (K + 1) 0 := by
    have hs := Nlog_osucc_le hαNF
    have hgap := relSlot_succ_gap e B K
    omega
  have hor := Zef2TC.orI (α := osucc α) hg
    (asg env ▹ φ) (asg env ▹ ψ)
    (lt_osucc hαNF) hαNF (osucc_NF hαNF) (clT α) D'
  have hmem : (asg env ▹ φ ⋎ asg env ▹ ψ)
      ∈ Γ.image (fun χ => asg env ▹ χ) := by
    have := Finset.mem_image_of_mem (fun χ => asg env ▹ χ) h
    simpa using this
  rwa [Finset.insert_eq_self.mpr hmem] at hor

/-- The `and` case: `φ ⋏ ψ ∈ Γ` and both `insert φ Γ`, `insert ψ Γ` embed implies `Γ` embeds. -/
theorem budgetedEmbedsTC_and
    {φ ψ : ArithmeticFormula ℕ} (h : φ ⋏ ψ ∈ Γ)
    (ihp : BudgetedEmbedsTC (insert φ Γ)) (ihq : BudgetedEmbedsTC (insert ψ Γ)) :
    BudgetedEmbedsTC Γ := by
  obtain ⟨B₁, d₁, e₁, he₁, ih₁⟩ := ihp
  obtain ⟨B₂, d₂, e₂, he₂, ih₂⟩ := ihq
  have headdNF : (e₁ + e₂).NF := by haveI := he₁; haveI := he₂; exact ONote.add_nf e₁ e₂
  have heNF : (osucc (e₁ + e₂)).NF := osucc_NF headdNF
  have hlt₁ : e₁ < osucc (e₁ + e₂) :=
    lt_of_le_of_lt (le_add_right_NF he₁ he₂) (lt_osucc headdNF)
  have hlt₂ : e₂ < osucc (e₁ + e₂) :=
    lt_of_le_of_lt (le_add_left_NF he₁ he₂) (lt_osucc headdNF)
  refine ⟨B₁ + B₂ + norm e₁ + norm e₂, max d₁ d₂, osucc (e₁ + e₂), heNF, fun env => ?_⟩
  obtain ⟨K₁, α₁, hα₁NF, D₁⟩ := ih₁ env
  obtain ⟨K₂, α₂, hα₂NF, D₂⟩ := ih₂ env
  have haddNF : (α₁ + α₂).NF := by haveI := hα₁NF; haveI := hα₂NF; exact ONote.add_nf α₁ α₂
  refine ⟨max K₁ K₂ + 1, osucc (α₁ + α₂), osucc_NF haddNF, ?_⟩
  have hg₁ := D₁.gate
  have hg₂ := D₂.gate
  rw [Finset.image_insert] at D₁ D₂
  have hff₁ : ∀ x, rel1 (ewRootSlot e₁ B₁) K₁ x
      ≤ rel1 (ewRootSlot (osucc (e₁ + e₂)) (B₁ + B₂ + norm e₁ + norm e₂))
          (max K₁ K₂ + 1) x :=
    relSlot_le he₁ heNF hlt₁ (by omega) (by omega) (by omega)
  have hff₂ : ∀ x, rel1 (ewRootSlot e₂ B₂) K₂ x
      ≤ rel1 (ewRootSlot (osucc (e₁ + e₂)) (B₁ + B₂ + norm e₁ + norm e₂))
          (max K₁ K₂ + 1) x :=
    relSlot_le he₂ heNF hlt₂ (by omega) (by omega) (by omega)
  have D₁' := ((D₁.change_e (osucc (e₁ + e₂))).mono_f hff₁).mono_c (le_max_left d₁ d₂)
  have D₂' := ((D₂.change_e (osucc (e₁ + e₂))).mono_f hff₂).mono_c (le_max_right d₁ d₂)
  have hg : Nlog (osucc (α₁ + α₂))
      ≤ rel1 (ewRootSlot (osucc (e₁ + e₂)) (B₁ + B₂ + norm e₁ + norm e₂))
          (max K₁ K₂ + 1) 0 := by
    have hs := Nlog_osucc_le haddNF
    have ha := Nlog_add_le_max_succ α₁ hα₁NF α₂ hα₂NF
    have j₁ : rel1 (ewRootSlot e₁ B₁) K₁ 0
        ≤ rel1 (ewRootSlot (osucc (e₁ + e₂)) (B₁ + B₂ + norm e₁ + norm e₂)) (max K₁ K₂) 0 :=
      relSlot_le he₁ heNF hlt₁ (by omega) (le_max_left _ _) (by omega) 0
    have j₂ : rel1 (ewRootSlot e₂ B₂) K₂ 0
        ≤ rel1 (ewRootSlot (osucc (e₁ + e₂)) (B₁ + B₂ + norm e₁ + norm e₂)) (max K₁ K₂) 0 :=
      relSlot_le he₂ heNF hlt₂ (by omega) (le_max_right _ _) (by omega) 0
    have hgap := relSlot_succ_gap (osucc (e₁ + e₂)) (B₁ + B₂ + norm e₁ + norm e₂) (max K₁ K₂)
    omega
  have hand := Zef2TC.andI (α := osucc (α₁ + α₂)) hg
    (asg env ▹ φ) (asg env ▹ ψ)
    (lt_of_le_of_lt (le_add_right_NF hα₁NF hα₂NF) (lt_osucc haddNF))
    (lt_of_le_of_lt (le_add_left_NF hα₁NF hα₂NF) (lt_osucc haddNF))
    hα₁NF hα₂NF (osucc_NF haddNF) (clT α₁) (clT α₂) D₁' D₂'
  have hmem : (asg env ▹ φ ⋏ asg env ▹ ψ)
      ∈ Γ.image (fun χ => asg env ▹ χ) := by
    have := Finset.mem_image_of_mem (fun χ => asg env ▹ χ) h
    simpa using this
  rwa [Finset.insert_eq_self.mpr hmem] at hand

/-- The `cut` case: `insert φ Γ` and `insert (∼φ) Γ` both embed implies `Γ` embeds. -/
theorem budgetedEmbedsTC_cut
    {φ : ArithmeticFormula ℕ}
    (ihp : BudgetedEmbedsTC (insert φ Γ)) (ihn : BudgetedEmbedsTC (insert (∼φ) Γ)) :
    BudgetedEmbedsTC Γ := by
  obtain ⟨B₁, d₁, e₁, he₁, ih₁⟩ := ihp
  obtain ⟨B₂, d₂, e₂, he₂, ih₂⟩ := ihn
  have headdNF : (e₁ + e₂).NF := by haveI := he₁; haveI := he₂; exact ONote.add_nf e₁ e₂
  have heNF : (osucc (e₁ + e₂)).NF := osucc_NF headdNF
  have hlt₁ : e₁ < osucc (e₁ + e₂) :=
    lt_of_le_of_lt (le_add_right_NF he₁ he₂) (lt_osucc headdNF)
  have hlt₂ : e₂ < osucc (e₁ + e₂) :=
    lt_of_le_of_lt (le_add_left_NF he₁ he₂) (lt_osucc headdNF)
  refine ⟨B₁ + B₂ + norm e₁ + norm e₂ + φ.complexity, max (max d₁ d₂) (φ.complexity + 1),
    osucc (e₁ + e₂), heNF, fun env => ?_⟩
  obtain ⟨K₁, α₁, hα₁NF, D₁⟩ := ih₁ env
  obtain ⟨K₂, α₂, hα₂NF, D₂⟩ := ih₂ env
  have haddNF : (α₁ + α₂).NF := by haveI := hα₁NF; haveI := hα₂NF; exact ONote.add_nf α₁ α₂
  refine ⟨max K₁ K₂ + 1, osucc (α₁ + α₂), osucc_NF haddNF, ?_⟩
  have hg₁ := D₁.gate
  have hg₂ := D₂.gate
  rw [Finset.image_insert] at D₁ D₂
  have hff₁ : ∀ x, rel1 (ewRootSlot e₁ B₁) K₁ x
      ≤ rel1 (ewRootSlot (osucc (e₁ + e₂)) (B₁ + B₂ + norm e₁ + norm e₂ + φ.complexity))
          (max K₁ K₂ + 1) x :=
    relSlot_le he₁ heNF hlt₁ (by omega) (by omega) (by omega)
  have hff₂ : ∀ x, rel1 (ewRootSlot e₂ B₂) K₂ x
      ≤ rel1 (ewRootSlot (osucc (e₁ + e₂)) (B₁ + B₂ + norm e₁ + norm e₂ + φ.complexity))
          (max K₁ K₂ + 1) x :=
    relSlot_le he₂ heNF hlt₂ (by omega) (by omega) (by omega)
  have D₁' := ((D₁.change_e (osucc (e₁ + e₂))).mono_f hff₁).mono_c
    (c' := max (max d₁ d₂) (φ.complexity + 1))
    (le_trans (le_max_left d₁ d₂) (le_max_left _ _))
  have D₂' := ((D₂.change_e (osucc (e₁ + e₂))).mono_f hff₂).mono_c
    (c' := max (max d₁ d₂) (φ.complexity + 1))
    (le_trans (le_max_right d₁ d₂) (le_max_left _ _))
  rw [show asg env ▹ (∼φ) = ∼(asg env ▹ φ) by simp] at D₂'
  have hg : Nlog (osucc (α₁ + α₂))
      ≤ rel1 (ewRootSlot (osucc (e₁ + e₂)) (B₁ + B₂ + norm e₁ + norm e₂ + φ.complexity))
          (max K₁ K₂ + 1) 0 := by
    have hs := Nlog_osucc_le haddNF
    have ha := Nlog_add_le_max_succ α₁ hα₁NF α₂ hα₂NF
    have j₁ : rel1 (ewRootSlot e₁ B₁) K₁ 0
        ≤ rel1 (ewRootSlot (osucc (e₁ + e₂))
            (B₁ + B₂ + norm e₁ + norm e₂ + φ.complexity)) (max K₁ K₂) 0 :=
      relSlot_le he₁ heNF hlt₁ (by omega) (le_max_left _ _) (by omega) 0
    have j₂ : rel1 (ewRootSlot e₂ B₂) K₂ 0
        ≤ rel1 (ewRootSlot (osucc (e₁ + e₂))
            (B₁ + B₂ + norm e₁ + norm e₂ + φ.complexity)) (max K₁ K₂) 0 :=
      relSlot_le he₂ heNF hlt₂ (by omega) (le_max_right _ _) (by omega) 0
    have hgap := relSlot_succ_gap (osucc (e₁ + e₂))
      (B₁ + B₂ + norm e₁ + norm e₂ + φ.complexity) (max K₁ K₂)
    omega
  have hread : (asg env ▹ φ).complexity
      ≤ rel1 (ewRootSlot (osucc (e₁ + e₂)) (B₁ + B₂ + norm e₁ + norm e₂ + φ.complexity))
          (max K₁ K₂ + 1) 0 := by
    simp only [Semiformula.complexity_rew]
    exact le_trans (by omega) (le_relSlot_zero _ _ _)
  have hcompl : (asg env ▹ φ).complexity < max (max d₁ d₂) (φ.complexity + 1) := by
    simp only [Semiformula.complexity_rew]
    omega
  exact Zef2TC.cut hg (asg env ▹ φ) hcompl hread
    (lt_of_le_of_lt (le_add_right_NF hα₁NF hα₂NF) (lt_osucc haddNF))
    (lt_of_le_of_lt (le_add_left_NF hα₁NF hα₂NF) (lt_osucc haddNF))
    hα₁NF hα₂NF (osucc_NF haddNF) (clT α₁) (clT α₂) D₁' D₂'

/-! ### The value-congruent EM engine + the closed-term collapse (the `exs` kit)

Mirror of `Provable.em_cong_gen`/`Provable.exI_closed` (`Embedding.lean`) with the `Zef2TC`
budget bookkeeping of `em_Zef2TC`; the congruence kit
(`stdClosedVal`/`atomTrue_rel_congr`/`embedding_subst_q_cons_app`) is banked in
`OperatorZinfty`. -/
/-- The `exs` case: `∃⁰ φ ∈ Γ` and `insert (φ/[t]) Γ` embeds implies `Γ` embeds, for any
witness term `t`. -/
theorem budgetedEmbedsTC_exs
    {φ : ArithmeticSemiformula ℕ 1} (h : ∃⁰ φ ∈ Γ) (t : ArithmeticTerm ℕ)
    (ih : BudgetedEmbedsTC (insert (φ/[t]) Γ)) :
    BudgetedEmbedsTC Γ := by
  obtain ⟨B₁, d₁, e₁, he₁, ih₁⟩ := ih
  refine ⟨B₁ + φ.complexity + clog (2 * φ.complexity + 1), max d₁ (φ.complexity + 1), e₁,
    he₁, fun env => ?_⟩
  set B : ℕ := B₁ + φ.complexity + clog (2 * φ.complexity + 1) with hB
  set d : ℕ := max d₁ (φ.complexity + 1) with hd
  obtain ⟨K₁, α₁, hα₁NF, D₁⟩ := ih₁ env
  -- the closed witness (`s`) and its standard value (`m`); the ∃-witness for the goal is `m`,
  -- absorbed into the relativization index `K := max K₁ m + 3`
  set ψ' : ArithmeticSemiformula ℕ 1 := (asg env).q ▹ φ with hψ'
  set s : ArithmeticTerm ℕ := asg env t with hs
  set m : ℕ := stdClosedVal s with hm
  set K : ℕ := max K₁ m + 3 with hK
  set F : ℕ → ℕ := rel1 (ewRootSlot e₁ B) K with hF
  have hψc : ψ'.complexity = φ.complexity := by simp [hψ']
  have hf1 := ewRootSlot_f1 e₁ B
  have hFmono : Monotone F := rel1_monotone hf1.1.monotone K
  have hFinfl : ∀ x, x ≤ F x := rel1_infl (fun x => by have := hf1.2 x; omega) K
  -- the IH derivation, re-based to the joined budget and rewritten to the substituted head
  have hg₁ := D₁.gate
  rw [Finset.image_insert, rew_subst_term (asg env) φ t] at D₁
  have D₁' := (D₁.mono_f (relSlot_mono (show B₁ ≤ B by omega) (show K₁ ≤ K by omega))).mono_c
    (c' := d) (le_max_left _ _)
  -- left cut premise: add ψ'/[nm m] to the context
  have Dsrc : Zef2TC α₁ e₁ (fun _ => True) F d
      (insert (ψ'/[s]) (insert (ψ'/[nm m])
        (Γ.image (fun χ => asg env ▹ χ)))) :=
    D₁'.wk D₁'.gate (Finset.insert_subset_insert _ (Finset.subset_insert _ _))
  -- right cut premise: value-congruent EM at the pair (nm m, s)
  have hgateEM : clog (2 * ψ'.complexity + 1) ≤ F 0 := by
    rw [hψc]
    exact le_trans (by omega) (le_relSlot_zero e₁ B K)
  have Dcong : Zef2TC (ONote.ofNat (2 * ψ'.complexity + 1)) e₁ (fun _ => True) F 0
      (insert (∼(ψ'/[s])) (insert (ψ'/[nm m])
        (Γ.image (fun χ => asg env ▹ χ)))) := by
    refine em_cong1_Zef2TC (nm m) s (by simp [hm]) ψ' hFmono hFinfl hgateEM ?_ ?_
    · exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    · exact Finset.mem_insert_self _ _
  have Dcong' := Dcong.mono_c (c' := d) (Nat.zero_le d)
  -- the cut, at root `osucc (α₁ + ofNat (2·complexity+1))`
  have hofNF : (ONote.ofNat (2 * ψ'.complexity + 1)).NF := ONote.nf_ofNat _
  have haddNF : (α₁ + ONote.ofNat (2 * ψ'.complexity + 1)).NF := by
    haveI := hα₁NF; haveI := hofNF; exact ONote.add_nf _ _
  have hslack : ∀ M, rel1 (ewRootSlot e₁ B) M 0 + 2
      ≤ rel1 (ewRootSlot e₁ B) (M + 2) 0 := by
    intro M
    have g1 := relSlot_succ_gap e₁ B M
    have g2 := relSlot_succ_gap e₁ B (M + 1)
    rw [show M + 1 + 1 = M + 2 from rfl] at g2
    omega
  have hgcut : Nlog (osucc (α₁ + ONote.ofNat (2 * ψ'.complexity + 1))) ≤ F 0 := by
    rw [hF, hK]
    have hs' := Nlog_osucc_le haddNF
    have ha := Nlog_add_le_max_succ α₁ hα₁NF _ hofNF
    have hα₁K : rel1 (ewRootSlot e₁ B₁) K₁ 0 ≤ rel1 (ewRootSlot e₁ B) (max K₁ m) 0 :=
      relSlot_mono (by omega) (le_max_left _ _) 0
    have hof : Nlog (ONote.ofNat (2 * ψ'.complexity + 1)) ≤ rel1 (ewRootSlot e₁ B) (max K₁ m) 0 :=
      le_trans (Nlog_ofNat_le _) (le_trans (by rw [hψc]; omega)
        (le_relSlot_zero e₁ B (max K₁ m)))
    have hgap := hslack (max K₁ m)
    have hlast := relSlot_succ_gap e₁ B (max K₁ m + 2)
    rw [show max K₁ m + 2 + 1 = max K₁ m + 3 from rfl] at hlast
    omega
  have hcompl : (ψ'/[s]).complexity < d := by
    have : (ψ'/[s]).complexity = φ.complexity := by simp [hψ']
    omega
  have hread : (ψ'/[s]).complexity ≤ F 0 := by
    have hc : (ψ'/[s]).complexity = φ.complexity := by simp [hψ']
    rw [hc]
    exact le_trans (by omega) (le_relSlot_zero e₁ B K)
  have Dnum : Zef2TC (osucc (α₁ + ONote.ofNat (2 * ψ'.complexity + 1))) e₁ (fun _ => True) F d
      (insert (ψ'/[nm m]) (Γ.image (fun χ => asg env ▹ χ))) :=
    Zef2TC.cut hgcut (ψ'/[s]) hcompl hread
      (lt_of_le_of_lt (le_add_right_NF hα₁NF hofNF) (lt_osucc haddNF))
      (lt_of_le_of_lt (le_add_left_NF hα₁NF hofNF) (lt_osucc haddNF))
      hα₁NF hofNF (osucc_NF haddNF) (clT _) (clT _) Dsrc Dcong'
  -- the ∃-introduction at the numeral witness `m`
  refine ⟨K, osucc (osucc (α₁ + ONote.ofNat (2 * ψ'.complexity + 1))),
    osucc_NF (osucc_NF haddNF), ?_⟩
  have hgout : Nlog (osucc (osucc (α₁ + ONote.ofNat (2 * ψ'.complexity + 1)))) ≤ F 0 := by
    rw [hF, hK]
    have hs' := Nlog_osucc_le (osucc_NF haddNF)
    have hs'' := Nlog_osucc_le haddNF
    have ha := Nlog_add_le_max_succ α₁ hα₁NF _ hofNF
    have hα₁K : rel1 (ewRootSlot e₁ B₁) K₁ 0 ≤ rel1 (ewRootSlot e₁ B) (max K₁ m) 0 :=
      relSlot_mono (by omega) (le_max_left _ _) 0
    have hof : Nlog (ONote.ofNat (2 * ψ'.complexity + 1)) ≤ rel1 (ewRootSlot e₁ B) (max K₁ m) 0 :=
      le_trans (Nlog_ofNat_le _) (le_trans (by rw [hψc]; omega)
        (le_relSlot_zero e₁ B (max K₁ m)))
    have g1 := relSlot_succ_gap e₁ B (max K₁ m)
    have g2 := relSlot_succ_gap e₁ B (max K₁ m + 1)
    have g3 := relSlot_succ_gap e₁ B (max K₁ m + 2)
    rw [show max K₁ m + 1 + 1 = max K₁ m + 2 from rfl] at g2
    rw [show max K₁ m + 2 + 1 = max K₁ m + 3 from rfl] at g3
    omega
  have hwit : m ≤ F 0 := le_trans (by omega) (index_le_relSlot_zero e₁ B K)
  have hexI := Zef2TC.exI (α := osucc (osucc (α₁ + ONote.ofNat (2 * ψ'.complexity + 1))))
    hgout ψ' m
    (lt_osucc (osucc_NF haddNF)) (osucc_NF haddNF)
    (osucc_NF (osucc_NF haddNF)) (clT _) hwit Dnum
  have hmem : (∃⁰ ψ') ∈ Γ.image (fun χ => asg env ▹ χ) := by
    have := Finset.mem_image_of_mem (fun χ => asg env ▹ χ) h
    simpa [hψ'] using this
  rwa [Finset.insert_eq_self.mpr hmem] at hexI

end GoodsteinPA.E1EmbeddingGrind
