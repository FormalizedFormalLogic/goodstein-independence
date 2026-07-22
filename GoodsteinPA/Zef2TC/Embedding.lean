module

public import GoodsteinPA.Zef2TC.Axm
public import GoodsteinPA.Zef2TC.SuccInd
public import GoodsteinPA.Zef2TC.Inversion

@[expose] public section

namespace GoodsteinPA.E1EmbeddingGrind

open LO LO.FirstOrder LO.FirstOrder.ArithmeticTerm ONote
open GoodsteinPA.OperatorZeh GoodsteinPA.OperatorZinfty

variable {Γ : Finset (ArithmeticFormula ℕ)}

/-! ## The embedded goodstein sentence -/

/-- The goodstein Π₂ body: `∃ N, igoodsteinDef 0 x N`, so that `goodsteinSentence` is its
`∀`-closure. -/
noncomputable def goodsteinBody : ArithmeticSemisentence 1 :=
  “∃ N, !LO.FirstOrder.Arithmetic.igoodsteinDef 0 #1 N”

@[grind =]
lemma goodsteinSentence_eq_all_body :
    GoodsteinPA.goodsteinSentence = ∀⁰ goodsteinBody := rfl

/-- The embedding of `goodsteinBody` into `ArithmeticSemiformula ℕ 1`. -/
noncomputable def goodsteinBodyE : ArithmeticSemiformula ℕ 1 :=
  Rewriting.emb goodsteinBody

/-! ## The V3 `axm` dispatcher and the assembled V3 master ladder

The master predicate `BudgetedEmbedsV3` carries an env-local relativization index `K`: the
derivation runs at slot `rel1 (ewRootSlot e B) K` rather than at a fixed structural slot
`ewRootSlot e B`, since the Σ₁ witness at the root (`exI`) is env-dependent and unbounded while
`ewRootSlot e B` is chosen before `∀ env`. `rel1`-slots compose with the ω-rule
(`rel1_rel1 : rel1 (rel1 f m) n = rel1 f (max m n)`) and keep `EwF1`/`EwF2` (`rel1_low`), so the
downstream pass/read-off pipeline is undisturbed. -/

/-- **V3 `axm`, complete**: every 𝗣𝗔 axiom in `Γ` is budgeted-embeddable — 𝗣𝗔 splits as
𝗣𝗔⁻ (`budgetedEmbedsV3_axm_PAminus`) + the universal induction scheme
(`budgetedEmbedsV3_succInd`). -/
lemma budgetedEmbedsV3_axm (σ : ArithmeticSentence) (hσ : σ ∈ (𝗣𝗔 : ArithmeticTheory))
    (hΓ : (↑σ : ArithmeticFormula ℕ) ∈ Γ) : BudgetedEmbedsV3 Γ := by
  have hsplit : σ ∈ (𝗣𝗔⁻ : ArithmeticTheory) ∨ σ ∈ Arithmetic.InductionScheme ℒₒᵣ Set.univ := by
    simpa [Arithmetic.Peano, Set.mem_union] using hσ
  rcases hsplit with h | h
  · exact budgetedEmbedsV3_axm_PAminus σ h hΓ
  · obtain ⟨φ, -, rfl⟩ := h
    exact budgetedEmbedsV3_succInd φ hΓ

/-- Every `Derivation2` from 𝗣𝗔 is budgeted-embeddable into `Zef2TC` under the structural-budget
predicate `BudgetedEmbedsV3`. -/
lemma budgetedEmbeddingV3 (d : Derivation2 (𝗣𝗔 : ArithmeticTheory) Γ) : BudgetedEmbedsV3 Γ := by
  induction d with
  | closed Γ φ hp hn => exact budgetedEmbedsV3_closed φ hp hn
  | axm φ hφ hΓ => exact budgetedEmbedsV3_axm φ hφ hΓ
  | verum h => exact budgetedEmbedsV3_verum h
  | @and Γ φ ψ h _dp _dq ihp ihq => exact budgetedEmbedsV3_and h ihp ihq
  | @or Γ φ ψ h _d ih => exact budgetedEmbedsV3_or h ih
  | @all Γ φ h _d ih => exact budgetedEmbedsV3_all h ih
  | @exs Γ φ h t _d ih => exact budgetedEmbedsV3_exs h t ih
  | @wk Δ Γ _d hsub ih => exact budgetedEmbedsV3_wk hsub ih
  | @shift Γ _d ih => exact budgetedEmbedsV3_shift ih
  | @cut Γ φ _dp _dn ihp ihn => exact budgetedEmbedsV3_cut ihp ihn

/-! ## `embedding_Zef2TC_V3`: the V3 realization, via `budgetedEmbeddingV3` and inversion -/

/-- The embedded goodstein sentence is the ∀-closure of the embedded body. -/
@[grind =]
lemma coe_goodsteinSentence_eq :
    (↑GoodsteinPA.goodsteinSentence : ArithmeticFormula ℕ) = ∀⁰ goodsteinBodyE := by
  rw [goodsteinSentence_eq_all_body]; simp [goodsteinBodyE, Rewriting.emb]

/-- From a PA proof of the goodstein sentence: uniform structural budgets `B, d`, control `e`,
node `α` (`m`-uniform), and for every `m` a relativization index `K` together with a `Zef2TC`
derivation of the Σ₁ instance singleton at slot `rel1 (ewRootSlot e B) K`. -/
theorem embedding_Zef2TC_V3 (h : 𝗣𝗔 ⊢ ↑GoodsteinPA.goodsteinSentence) :
    ∃ B d : ℕ, ∃ e α : ONote, e.NF ∧ α.NF ∧ ∀ m : ℕ, ∃ K : ℕ,
      ∃ H : ONote → Prop, Cl H α ∧
        Zef2TC α e H (rel1 (ewRootSlot e B) K) d {(goodsteinBodyE/[nm m])} := by
  -- upstream `𝗣𝗔 ⊢ σ` repackages as a `Derivation2 𝗣𝗔 {↑σ}` via `provable_iff_derivable2`
  have hV3 : BudgetedEmbedsV3 {(↑GoodsteinPA.goodsteinSentence : ArithmeticFormula ℕ)} := by
    obtain ⟨d2⟩ := (provable_iff_derivable2 (L := ℒₒᵣ)).mp h
    exact budgetedEmbeddingV3 d2
  obtain ⟨B, d, N, e, α, he, hαNF, hNlogB, hD⟩ := hV3
  refine ⟨B, d, e, α, he, hαNF, fun m => ?_⟩
  have hD0 := hD (fun _ => 0)
  have himg : ({(↑GoodsteinPA.goodsteinSentence : ArithmeticFormula ℕ)} :
        Finset (ArithmeticFormula ℕ)).image
        (fun φ => asg (fun _ => 0) ▹ φ)
      = {(↑GoodsteinPA.goodsteinSentence : ArithmeticFormula ℕ)} := by
    rw [Finset.image_singleton, asg_emb_fix]
  rw [himg, coe_goodsteinSentence_eq] at hD0
  have hf1 := ewRootSlot_f1 e B
  have hmono : Monotone (rel1 (ewRootSlot e B) (envSup (fun _ => 0) N)) :=
    rel1_monotone hf1.1.monotone _
  have hinv := allω_inversion (φ := goodsteinBodyE) m hD0 hmono
  rw [rel1_rel1] at hinv
  refine ⟨max (envSup (fun _ => 0) N) m, fun _ => True, Cl_of_NF hαNF, ?_⟩
  have hctx : insert (goodsteinBodyE/[nm m])
        (({(∀⁰ goodsteinBodyE : ArithmeticFormula ℕ)} :
          Finset (ArithmeticFormula ℕ)).erase (∀⁰ goodsteinBodyE))
      = {(goodsteinBodyE/[nm m])} := by
    rw [Finset.erase_singleton]
    rfl
  rw [hctx] at hinv
  exact hinv.change_H

end GoodsteinPA.E1EmbeddingGrind
