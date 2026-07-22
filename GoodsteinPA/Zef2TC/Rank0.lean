module

public import GoodsteinPA.Zef2TC.Pass

@[expose] public section

namespace GoodsteinPA.E1EmbeddingGrind

open LO LO.FirstOrder LO.FirstOrder.ArithmeticTerm ONote
open GoodsteinPA.OperatorZeh GoodsteinPA.OperatorZinfty

/-! ### Rank descent (`rankToZero_TC`) and the rank-0 truth core (`sound0_TC`)

`rankToZeroAuxTC` mirrors `rankToZeroAux` verbatim (the extra `3 ≤ f 0` conjunct survives the
tower: `ewIter f α 0 ≥ f 0`). `sound0_TC` extends `sound0` to the full rule set: the truth leaves
ARE their own witnesses, `verumR` gives `⊤`, and `andI`/`orI` combine premise truths through the
connective evaluation. -/

/-- **`rankToZeroAuxTC`** — iterate `passAuxTC` down the cut rank `d → 0`. -/
theorem rankToZeroAuxTC (e : ONote) (heNF : e.NF) (d : ℕ) {α : ONote} {H : ONote → Prop}
    {f : ℕ → ℕ} {Γ : Finset (ArithmeticFormula ℕ)} (D : Zef2TC α e H f d Γ) (hmono : Monotone f)
    (hinfl : ∀ x, x ≤ f x) (hlow : ∀ m, 2 * m + 1 ≤ f m) (hbase3 : 3 ≤ f 0) (hαNF : α.NF)
    (hαH : Cl H α) :
    Zef2TCProv (collapseIter d α) e H (ewIterTower f d α) 0 Γ := by
  induction d generalizing α H f Γ hmono hinfl hlow hbase3 hαNF hαH with
  | zero => exact Zef2TCProv.of hαNF hαH (Zef2TC.gate D) D
  | succ d ih =>
      obtain ⟨β, hβle, hβNF, hβH, hβgate, Dβ⟩ :=
        passAuxTC d heNF D rfl hmono hinfl hlow hbase3 hαNF hαH
      have hg := Nlog_collapse_le hlow (Zef2TC.gate D)
      have Dcol : Zef2TC (collapse α) e H (ewIter f α) d Γ := by
        rcases lt_or_eq_of_le (ONote.le_def.mp hβle) with hlt | heq
        · exact Zef2TC.weak hg (ONote.lt_def.mpr hlt) hβNF (collapse_NF hαNF) hβH
            (Finset.Subset.refl Γ) Dβ
        · have hβeq : β = collapse α := by
            haveI := hβNF; haveI := collapse_NF hαNF
            exact ONote.repr_inj.mp heq
          exact hβeq ▸ Dβ
      have hrec := ih Dcol (ewIter_monotone hmono hinfl α) (ewIter_infl hinfl α)
        (fun m => ewIter_low hinfl hlow α m)
        (le_trans hbase3 (ewIter_base_le hinfl α))
        (collapse_NF hαNF) (Cl_of_NF (collapse_NF hαNF))
      rw [collapseIter_collapse α d, ewIterTower_collapse f α d] at hrec
      exact hrec

/-- **`rankToZero_TC`** — the rung-R analog over `Zef2TC` (EwF1/EwF2 entry point; the extra
`3 ≤ f 0` is satisfied by every real root slot, e.g. `ewRootSlot e m 0 ≥ 3`). -/
theorem rankToZero_TC {α e} {H} {d} {Γ} (f : ℕ → ℕ)
    (heNF : e.NF) (hαNF : α.NF) (hαH : Cl H α) (hf0 : 3 ≤ f 0)
    (D : Zef2TC α e H f d Γ) (hf1 : EwF1 f) (_hf2 : EwF2 f) :
    Zef2TCProv (collapseIter d α) e H (ewIterTower f d α) 0 Γ :=
  rankToZeroAuxTC e heNF d D hf1.monotone hf1.infl hf1.2 hf0 hαNF hαH

/-- **Rank-0 `Zef2TC` soundness** — the truth core over the FULL rule set: a cut-free (rank-0)
`Zef2TC` derivation has a standard-model-true member. Truth leaves are their own witnesses;
`andI`/`orI` combine premise truths through the connective evaluation. -/
theorem sound0_TC {α e} {H} {f} {c} {Γ}
    (dd : Zef2TC α e H f c Γ) (hc : c = 0) : ∃ ψ ∈ Γ, atomTrue ψ := by
  induction dd with
  | @axL α e H f c Γ ar hαN r v hp hn =>
      by_cases htrue : atomTrue (Semiformula.rel r v)
      · exact ⟨_, hp, htrue⟩
      · refine ⟨_, hn, ?_⟩
        simpa [atomTrue, Semiformula.eval_nrel, Semiformula.eval_rel, Function.comp_def] using htrue
  | trueRel hαN r v htrue hmem => exact ⟨_, hmem, htrue⟩
  | trueNrel hαN r v htrue hmem => exact ⟨_, hmem, htrue⟩
  | verumR hαN h => exact ⟨⊤, h, by simp [atomTrue]⟩
  | @wk α e H f c Δ Γ hαN hsub _ ih =>
      obtain ⟨ψ, hψ, htrue⟩ := ih hc
      exact ⟨ψ, hsub hψ, htrue⟩
  | @weak α β e H f c Δ Γ hαN hβ hβNF hαNF hβH hsub _ ih =>
      obtain ⟨ψ, hψ, htrue⟩ := ih hc
      exact ⟨ψ, hsub hψ, htrue⟩
  | @andI α βφ βψ e H f c Γ hαN φ ψ hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH _ _ ih₁ ih₂ =>
      obtain ⟨ψ₁, hψ₁, htrue₁⟩ := ih₁ hc
      obtain ⟨ψ₂, hψ₂, htrue₂⟩ := ih₂ hc
      rcases Finset.mem_insert.mp hψ₁ with rfl | hΓ₁
      · rcases Finset.mem_insert.mp hψ₂ with rfl | hΓ₂
        · refine ⟨ψ₁ ⋏ ψ₂, Finset.mem_insert_self _ _, ?_⟩
          have h12 : atomTrue ψ₁ ∧ atomTrue ψ₂ := ⟨htrue₁, htrue₂⟩
          simpa [atomTrue] using h12
        · exact ⟨ψ₂, Finset.mem_insert_of_mem hΓ₂, htrue₂⟩
      · exact ⟨ψ₁, Finset.mem_insert_of_mem hΓ₁, htrue₁⟩
  | @orI α β e H f c Γ hαN φ ψ hβ hβNF hαNF hβH _ ih =>
      obtain ⟨ψ', hψ', htrue'⟩ := ih hc
      rcases Finset.mem_insert.mp hψ' with rfl | hψ'2
      · refine ⟨ψ' ⋎ ψ, Finset.mem_insert_self _ _, ?_⟩
        have h1 : atomTrue ψ' ∨ atomTrue ψ := Or.inl htrue'
        simpa [atomTrue] using h1
      · rcases Finset.mem_insert.mp hψ'2 with rfl | hΓ
        · refine ⟨φ ⋎ ψ', Finset.mem_insert_self _ _, ?_⟩
          have h1 : atomTrue φ ∨ atomTrue ψ' := Or.inr htrue'
          simpa [atomTrue] using h1
        · exact ⟨ψ', Finset.mem_insert_of_mem hΓ, htrue'⟩
  | @allω α e H f c Γ hαN φ β hβ hβNF hαNF hβH _ ih =>
      rcases Classical.em (∃ n : ℕ, ∃ ψ ∈ Γ, atomTrue ψ) with hctx | hctx
      · obtain ⟨n, ψ, hψ, htrue⟩ := hctx
        exact ⟨ψ, Finset.mem_insert_of_mem hψ, htrue⟩
      · refine ⟨∀⁰ φ, Finset.mem_insert_self _ _, ?_⟩
        have hall : ∀ n, atomTrue (φ/[nm n]) := by
          intro n
          obtain ⟨ψ, hψ, htrue⟩ := ih n hc
          rcases Finset.mem_insert.mp hψ with rfl | hψΓ
          · exact htrue
          · exact absurd ⟨n, ψ, hψΓ, htrue⟩ hctx
        exact (atomTrue_all_iff φ).mpr hall
  | @exI α β e H f c Γ hαN φ n hβ hβNF hαNF hβH hbound _ ih =>
      obtain ⟨ψ, hψ, htrue⟩ := ih hc
      rcases Finset.mem_insert.mp hψ with rfl | hψΓ
      · exact ⟨∃⁰ φ, Finset.mem_insert_self _ _, (atomTrue_ex_iff φ).mpr ⟨n, htrue⟩⟩
      · exact ⟨ψ, Finset.mem_insert_of_mem hψΓ, htrue⟩
  | @cut α βφ βψ e H f c Γ hαN φ hcompl hcutRead _ _ _ _ _ _ _ _ _ _ _ =>
      subst hc
      exact absurd hcompl (by omega)

end GoodsteinPA.E1EmbeddingGrind
