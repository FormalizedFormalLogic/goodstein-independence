module

public import GoodsteinPA.Zef2TC.Rank0
public import GoodsteinPA.Zef2TC.Embedding

@[expose] public section

namespace GoodsteinPA.E1EmbeddingGrind

open LO LO.FirstOrder LO.FirstOrder.ArithmeticTerm ONote
open GoodsteinPA.OperatorZeh GoodsteinPA.OperatorZinfty

/-! ### Root-slot `EwLow` facts and tower inflationarity

The pipeline's root slot `rel1 (ewRootSlot e B) K` is not `EwF1` (the `rel1` plateau below `K`
breaks `StrictMono`), so it enters `rankToZeroAuxTC` (the `EwLow` entry: `Monotone ∧ infl ∧ 2m+1 ∧
3 ≤ f 0`) rather than the `EwF1`-based `rankToZero_TC`. -/

/-- `3 ≤ (rel1 (ewRootSlot e B) K) 0` — the root slot pays `rankToZeroAuxTC`'s `3 ≤ f 0` gate
(`ewRootSlot _ _ x = 2·(…) + 3 ≥ 3`). -/
@[grind .]
lemma three_le_rel1_rootSlot (e : ONote) (B K : ℕ) : 3 ≤ (rel1 (ewRootSlot e B) K) 0 := by
  simp only [rel1, ewRootSlot]; omega

/-! ### The V-threaded value-budget read-off

The read-off pipeline needs a WITNESS BOUND for the top `∃⁰ φ` member of a rank-0 sequent, not
merely `sound0_TC`'s unbounded true member.  The tracked `∃⁰ φ` invariant, threaded through every
rule at a slot `g = rel1 f₀ j`, would trap at the `allω` case: a standard-false `∀⁰ χ` can still
have a true `0`-instance, so a naive bound at the CONSTANT slot `f₀ j` cannot absorb the descent.
This is resolved by threading a VALUE BUDGET `V` alongside `j` and requiring every sequent member
to be `Gated P V` (`GoodsteinPA.ReadoffValueGate.Gated`, the hereditary semantic value gate): a
false `∀⁰ χ` member then always admits a false branch `k₀ ≤ P V`, and `T3_descent'` absorbs the
resulting budget bump `V ↦ max V k₀` against the combined step `S x := max (f₀ x) (P x)`. -/

open GoodsteinPA.ReadoffValueGate (Gated Gated_and_iff Gated_or_iff Gated_all_iff Gated_exs_iff
  Gated_mono)

/-- The combined value-budget step `S x := max (f₀ x) (P x)`. -/
def Sslot (f₀ P : ℕ → ℕ) : ℕ → ℕ := fun x => max (f₀ x) (P x)

lemma Sslot_mono {f₀ P : ℕ → ℕ} (hf : Monotone f₀) (hP : Monotone P) :
    Monotone (Sslot f₀ P) := fun _ _ h => max_le_max (hf h) (hP h)

lemma Sslot_infl {f₀ P : ℕ → ℕ} (hf_infl : ∀ m, m ≤ f₀ m) :
    ∀ m, m ≤ Sslot f₀ P m := fun m => le_trans (hf_infl m) (le_max_left _ _)

variable {φ : ArithmeticSemiformula ℕ 1} {f₀ P : ℕ → ℕ} (hf_mono : Monotone f₀)
  (hf_infl : ∀ m, m ≤ f₀ m) (hP_mono : Monotone P) {α e : ONote} {H : ONote → Prop} (V : ℕ)
  (hroot : Gated P V (∃⁰ φ))

include hf_mono hf_infl hP_mono in
/-- The V-threaded value-budget read-off. Invariant: the tracked `∃⁰ φ` is a member, every member
is `Gated P V`, every non-tracked member is standard-false; slot frame `g = rel1 f₀ j`, `j ≤ V`.
Conclusion bound: `ewIter S α (S V)` for the combined step `S = Sslot f₀ P`. -/
lemma readoffVTC_core {g : ℕ → ℕ} {c : ℕ} {Γ : Finset (ArithmeticFormula ℕ)}
    (dd : Zef2TC α e H g c Γ) : c = 0 →
      ∀ (V j : ℕ), g = rel1 f₀ j → j ≤ V →
      (∃⁰ φ) ∈ Γ →
      (∀ ψ ∈ Γ, Gated P V ψ ∧ (ψ = (∃⁰ φ) ∨ ¬ atomTrue ψ)) →
      ∃ n, n ≤ ewIter (Sslot f₀ P) α (Sslot f₀ P V) ∧ atomTrue (φ/[nm n]) := by
  have hS_mono : Monotone (Sslot f₀ P) := Sslot_mono hf_mono hP_mono
  have hS_infl : ∀ m, m ≤ Sslot f₀ P m := Sslot_infl hf_infl
  induction dd with
  | @axL α e H g c Γ ar hαN r v hp hn =>
      intro _ _ _ _ _ _ hinv
      have h1 : ¬ atomTrue (Semiformula.rel r v) :=
        (hinv _ hp).2.resolve_left (Semiformula.ne_of_ne_complexity (by simp))
      have h2 : ¬ atomTrue (Semiformula.nrel r v) :=
        (hinv _ hn).2.resolve_left (Semiformula.ne_of_ne_complexity (by simp))
      exact absurd ((atomTrue_nrel_iff_not_rel r v).mpr h1) h2
  | trueRel hαN r v htrue hmem =>
      intro _ _ _ _ _ _ hinv
      exact absurd htrue ((hinv _ hmem).2.resolve_left (Semiformula.ne_of_ne_complexity (by simp)))
  | trueNrel hαN r v htrue hmem =>
      intro _ _ _ _ _ _ hinv
      exact absurd htrue ((hinv _ hmem).2.resolve_left (Semiformula.ne_of_ne_complexity (by simp)))
  | verumR hαN h =>
      intro _ _ _ _ _ _ hinv
      have hf := (hinv _ h).2.resolve_left (Semiformula.ne_of_ne_complexity (by simp))
      exact absurd (show atomTrue (⊤ : ArithmeticFormula ℕ) by simp [atomTrue]) hf
  | @wk α e H g c Δ Γ hαN hsub dpr ih =>
      intro hc V j hg hjV _ hinv
      obtain ⟨ψ, hψΔ, htψ⟩ := sound0_TC dpr hc
      have hφΔ : (∃⁰ φ) ∈ Δ := by
        rcases (hinv ψ (hsub hψΔ)).2 with rfl | hfalse
        · exact hψΔ
        · exact absurd htψ hfalse
      exact ih hc V j hg hjV hφΔ (fun ψ' hψ' => hinv ψ' (hsub hψ'))
  | @weak α β e H g c Δ Γ hαN hβ hβNF hαNF hβH hsub dpr ih =>
      intro hc V j hg hjV _ hinv
      obtain ⟨ψ, hψΔ, htψ⟩ := sound0_TC dpr hc
      have hφΔ : (∃⁰ φ) ∈ Δ := by
        rcases (hinv ψ (hsub hψΔ)).2 with rfl | hfalse
        · exact hψΔ
        · exact absurd htψ hfalse
      obtain ⟨n, hn, htn⟩ := ih hc V j hg hjV hφΔ (fun ψ' hψ' => hinv ψ' (hsub hψ'))
      refine ⟨n, le_trans hn ?_, htn⟩
      refine T3_descent' hS_mono hS_infl hβNF hβ (hS_infl V) ?_
      have hgpr : Nlog β ≤ g 0 := dpr.gate
      have hg0 : g 0 = f₀ j := by simp [hg, rel1]
      calc Nlog β ≤ f₀ j := hg0 ▸ hgpr
        _ ≤ Sslot f₀ P V := le_trans (hf_mono hjV) (le_max_left _ _)
        _ ≤ Sslot f₀ P (Sslot f₀ P V) := hS_infl _
  | @andI α βφ βψ e H g c Γ hαN χ₁ χ₂ hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH dφ dψ ih₁ ih₂ =>
      intro hc V j hg hjV hmem hinv
      have hφΓ : (∃⁰ φ) ∈ Γ :=
        (Finset.mem_insert.mp hmem).resolve_left
          (fun h => (by simp : (χ₁ ⋏ χ₂) ≠ (∃⁰ φ)) h.symm)
      obtain ⟨hgAnd, horAnd⟩ := hinv _ (Finset.mem_insert_self _ _)
      obtain ⟨hg1, hg2⟩ := Gated_and_iff.mp hgAnd
      have hfalse : ¬ (atomTrue χ₁ ∧ atomTrue χ₂) := by
        have hnand : ¬ atomTrue (χ₁ ⋏ χ₂) := horAnd.resolve_left (by simp)
        simpa [atomTrue] using hnand
      have hgate : Nlog βφ ≤ Sslot f₀ P (Sslot f₀ P V) ∧
          Nlog βψ ≤ Sslot f₀ P (Sslot f₀ P V) := by
        have hgφ : Nlog βφ ≤ g 0 := dφ.gate
        have hgψ : Nlog βψ ≤ g 0 := dψ.gate
        have hg0 : g 0 = f₀ j := by simp [hg, rel1]
        have hto : f₀ j ≤ Sslot f₀ P (Sslot f₀ P V) :=
          le_trans (le_trans (hf_mono hjV) (le_max_left _ _)) (hS_infl _)
        exact ⟨le_trans (hg0 ▸ hgφ) hto, le_trans (hg0 ▸ hgψ) hto⟩
      rcases not_and_or.mp hfalse with h1 | h2
      · obtain ⟨n, hn, htn⟩ := ih₁ hc V j hg hjV (Finset.mem_insert_of_mem hφΓ) (fun ψ hψ => by
          rcases Finset.mem_insert.mp hψ with rfl | hψΓ
          · exact ⟨hg1, Or.inr h1⟩
          · exact hinv ψ (Finset.mem_insert_of_mem hψΓ))
        exact ⟨n, le_trans hn
          (T3_descent' hS_mono hS_infl hβφNF hβφ (hS_infl V) hgate.1), htn⟩
      · obtain ⟨n, hn, htn⟩ := ih₂ hc V j hg hjV (Finset.mem_insert_of_mem hφΓ) (fun ψ hψ => by
          rcases Finset.mem_insert.mp hψ with rfl | hψΓ
          · exact ⟨hg2, Or.inr h2⟩
          · exact hinv ψ (Finset.mem_insert_of_mem hψΓ))
        exact ⟨n, le_trans hn
          (T3_descent' hS_mono hS_infl hβψNF hβψ (hS_infl V) hgate.2), htn⟩
  | @orI α β e H g c Γ hαN χ₁ χ₂ hβ hβNF hαNF hβH dpr ih =>
      intro hc V j hg hjV hmem hinv
      have hφΓ : (∃⁰ φ) ∈ Γ :=
        (Finset.mem_insert.mp hmem).resolve_left
          (fun h => (by simp : (χ₁ ⋎ χ₂) ≠ (∃⁰ φ)) h.symm)
      obtain ⟨hgOr, horOr⟩ := hinv _ (Finset.mem_insert_self _ _)
      obtain ⟨hg1, hg2⟩ := Gated_or_iff.mp hgOr
      have hfalse : ¬ (atomTrue χ₁ ∨ atomTrue χ₂) := by
        have hnor : ¬ atomTrue (χ₁ ⋎ χ₂) := horOr.resolve_left (by simp)
        simpa [atomTrue] using hnor
      obtain ⟨hf1, hf2⟩ := not_or.mp hfalse
      obtain ⟨n, hn, htn⟩ := ih hc V j hg hjV
        (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hφΓ)) (fun ψ hψ => by
          rcases Finset.mem_insert.mp hψ with rfl | hψ'
          · exact ⟨hg1, Or.inr hf1⟩
          · rcases Finset.mem_insert.mp hψ' with rfl | hψΓ
            · exact ⟨hg2, Or.inr hf2⟩
            · exact hinv ψ (Finset.mem_insert_of_mem hψΓ))
      refine ⟨n, le_trans hn (T3_descent' hS_mono hS_infl hβNF hβ (hS_infl V) ?_), htn⟩
      have hgpr : Nlog β ≤ g 0 := dpr.gate
      have hg0 : g 0 = f₀ j := by simp [hg, rel1]
      calc Nlog β ≤ f₀ j := hg0 ▸ hgpr
        _ ≤ Sslot f₀ P (Sslot f₀ P V) :=
          le_trans (le_trans (hf_mono hjV) (le_max_left _ _)) (hS_infl _)
  | @allω α e H g c Γ hαN χ β hβ hβNF hαNF hβH dpr ih =>
      intro hc V j hg hjV hmem hinv
      have hφΓ : (∃⁰ φ) ∈ Γ :=
        (Finset.mem_insert.mp hmem).resolve_left (by simp)
      obtain ⟨hgAll, horAll⟩ := hinv _ (Finset.mem_insert_self _ _)
      have hnall : ¬ atomTrue (∀⁰ χ) := horAll.resolve_left (by simp)
      rw [Gated_all_iff] at hgAll
      obtain ⟨k₀, hk₀P, hk₀f⟩ := hgAll.1 hnall
      -- descend into the GATED false branch k₀ at bumped budget max V k₀
      obtain ⟨n, hn, htn⟩ := ih k₀ hc (max V k₀) (max j k₀)
        (by rw [hg, rel1_rel1])
        (max_le_max hjV le_rfl)
        (Finset.mem_insert_of_mem hφΓ)
        (fun ψ hψ => by
          rcases Finset.mem_insert.mp hψ with rfl | hψΓ
          · exact ⟨hgAll.2 k₀, Or.inr hk₀f⟩
          · obtain ⟨hgψ, horψ⟩ := hinv ψ (Finset.mem_insert_of_mem hψΓ)
            exact ⟨Gated_mono hP_mono ψ V (max V k₀) (le_max_left _ _) hgψ, horψ⟩)
      refine ⟨n, le_trans hn (T3_descent' hS_mono hS_infl (hβNF k₀) (hβ k₀) ?_ ?_), htn⟩
      · -- V' = max V k₀ ≤ S V
        exact max_le (le_trans (hf_infl V) (le_max_left _ _))
          (le_trans hk₀P (le_max_right _ _))
      · -- gate: Nlog (β k₀) ≤ (rel1 g k₀) 0 = f₀ (max j k₀) ≤ S (S V)
        have hgpr : Nlog (β k₀) ≤ (rel1 g k₀) 0 := (dpr k₀).gate
        have hg0 : (rel1 g k₀) 0 = f₀ (max j k₀) := by simp [hg, rel1]
        have harg : max j k₀ ≤ Sslot f₀ P V :=
          max_le (le_trans hjV (hS_infl V)) (le_trans hk₀P (le_max_right _ _))
        calc Nlog (β k₀) ≤ f₀ (max j k₀) := hg0 ▸ hgpr
          _ ≤ f₀ (Sslot f₀ P V) := hf_mono harg
          _ ≤ Sslot f₀ P (Sslot f₀ P V) := le_max_left _ _
  | @exI α β e H g c Γ hαN χ n hβ hβNF hαNF hβH hbound dpr ih =>
      intro hc V j hg hjV hmem hinv
      have hnfj : n ≤ f₀ j := by
        have := hbound
        rw [hg] at this
        simpa [rel1] using this
      have hnSV : n ≤ Sslot f₀ P V :=
        le_trans (le_trans hnfj (hf_mono hjV)) (le_max_left _ _)
      have hgate : Nlog β ≤ Sslot f₀ P (Sslot f₀ P V) := by
        have hgpr : Nlog β ≤ g 0 := dpr.gate
        have hg0 : g 0 = f₀ j := by simp [hg, rel1]
        calc Nlog β ≤ f₀ j := hg0 ▸ hgpr
          _ ≤ Sslot f₀ P (Sslot f₀ P V) :=
            le_trans (le_trans (hf_mono hjV) (le_max_left _ _)) (hS_infl _)
      have hVbump : max V n ≤ Sslot f₀ P V := max_le (hS_infl V) hnSV
      by_cases hχφ : (∃⁰ χ) = (∃⁰ φ)
      · have hχeq : χ = φ := by simpa using hχφ
        subst hχeq
        by_cases htn : atomTrue (χ/[nm n])
        · exact ⟨n, le_trans hnSV (ewIter_infl hS_infl α _), htn⟩
        · obtain ⟨hgEx, _⟩ := hinv _ hmem
          have hgInst : Gated P (max V n) (χ/[nm n]) := (Gated_exs_iff.mp hgEx) n
          have hInvP : ∀ ψ ∈ insert (χ/[nm n]) Γ,
              Gated P (max V n) ψ ∧ (ψ = (∃⁰ χ) ∨ ¬ atomTrue ψ) := by
            intro ψ hψ
            rcases Finset.mem_insert.mp hψ with rfl | hψΓ
            · exact ⟨hgInst, Or.inr htn⟩
            · obtain ⟨hgψ, horψ⟩ := hinv ψ (Finset.mem_insert_of_mem hψΓ)
              exact ⟨Gated_mono hP_mono ψ V (max V n) (le_max_left _ _) hgψ, horψ⟩
          by_cases hin : (∃⁰ χ) ∈ insert (χ/[nm n]) Γ
          · obtain ⟨n', hn', htn'⟩ := ih hc (max V n) j hg
              (le_trans hjV (le_max_left _ _)) hin hInvP
            exact ⟨n', le_trans hn'
              (T3_descent' hS_mono hS_infl hβNF hβ hVbump hgate), htn'⟩
          · obtain ⟨ψ, hψ, htψ⟩ := sound0_TC dpr hc
            rcases (hInvP ψ hψ).2 with rfl | hfψ
            · exact absurd hψ hin
            · exact absurd htψ hfψ
      · have hφΓ : (∃⁰ φ) ∈ Γ :=
          (Finset.mem_insert.mp hmem).resolve_left (fun h => hχφ h.symm)
        obtain ⟨hgEx, horEx⟩ := hinv _ (Finset.mem_insert_self _ _)
        have hexχ : ¬ atomTrue (∃⁰ χ) := horEx.resolve_left hχφ
        have hχn : ¬ atomTrue (χ/[nm n]) :=
          fun ht => hexχ ((atomTrue_ex_iff χ).mpr ⟨n, ht⟩)
        have hgInst : Gated P (max V n) (χ/[nm n]) := (Gated_exs_iff.mp hgEx) n
        obtain ⟨n', hn', htn'⟩ := ih hc (max V n) j hg
          (le_trans hjV (le_max_left _ _))
          (Finset.mem_insert_of_mem hφΓ)
          (fun ψ hψ => by
            rcases Finset.mem_insert.mp hψ with rfl | hψΓ
            · exact ⟨hgInst, Or.inr hχn⟩
            · obtain ⟨hgψ, horψ⟩ := hinv ψ (Finset.mem_insert_of_mem hψΓ)
              exact ⟨Gated_mono hP_mono ψ V (max V n) (le_max_left _ _) hgψ, horψ⟩)
        exact ⟨n', le_trans hn'
          (T3_descent' hS_mono hS_infl hβNF hβ hVbump hgate), htn'⟩
  | @cut α βφ βψ e H g c Γ hαN χ hcompl hcutRead _ _ _ _ _ _ _ _ _ _ _ =>
      intro hc _ _ _ _ _ _; subst hc
      exact absurd hcompl (by omega)

/-- The value-budget read-off at the singleton root `{∃⁰ φ}`: given a root `Gated` certificate,
a TRUE numeral instance for `φ` exists under the master bound `ewIter (Sslot f₀ P) α (Sslot f₀ P V)`.
-/
lemma readoff_value_Zef2TC {φ : ArithmeticSemiformula ℕ 1} {f₀ P : ℕ → ℕ}
    (hf_mono : Monotone f₀) (hf_infl : ∀ m, m ≤ f₀ m) (hP_mono : Monotone P)
    {α e : ONote} {H : ONote → Prop} (dd : Zef2TC α e H f₀ 0 {(∃⁰ φ)}) (V : ℕ)
    (hroot : Gated P V (∃⁰ φ)) :
    ∃ n, n ≤ ewIter (Sslot f₀ P) α (Sslot f₀ P V) ∧ atomTrue (φ/[nm n]) :=
  readoffVTC_core hf_mono hf_infl hP_mono dd rfl V 0
    (by funext x; simp [rel1]) (Nat.zero_le V)
    (Finset.mem_singleton_self _)
    (fun ψ hψ => by
      rcases Finset.mem_singleton.mp hψ with rfl
      exact ⟨hroot, Or.inl rfl⟩)

/-- The structural read-off pipeline (bound-shape-independent): from a rank-`d` `Zef2TC`
derivation of a singleton `{∃⁰ φ}` at the embedding's root slot `rel1 (ewRootSlot e B) K` (the
`embedding_Zef2TC_V3` output shape) and a root `Gated` certificate, composing `rankToZeroAuxTC`
with `readoff_value_Zef2TC` yields a TRUE numeral instance under the concrete
`ewIter (Sslot tower P)` bound at some NF ordinal `α' ≤ collapseIter d α`. -/
lemma readoff_value_pipeline {φ : ArithmeticSemiformula ℕ 1} {P : ℕ → ℕ} (hP_mono : Monotone P)
    {α e : ONote} {H : ONote → Prop} {B K d : ℕ} (heNF : e.NF) (hαNF : α.NF) (hαH : Cl H α)
    (D : Zef2TC α e H (rel1 (ewRootSlot e B) K) d {(∃⁰ φ)}) (V : ℕ) (hroot : Gated P V (∃⁰ φ)) :
    ∃ α', α' ≤ collapseIter d α ∧ α'.NF ∧
      ∃ n, n ≤ ewIter (Sslot (ewIterTower (rel1 (ewRootSlot e B) K) d α) P) α'
              (Sslot (ewIterTower (rel1 (ewRootSlot e B) K) d α) P V) ∧
        atomTrue (φ/[nm n]) := by
  have hf1 := ewRootSlot_f1 e B
  have hmono : Monotone (rel1 (ewRootSlot e B) K) := rel1_monotone hf1.monotone K
  have hinfl : ∀ x, x ≤ rel1 (ewRootSlot e B) K x := rel1_infl hf1.infl K
  have hlow : ∀ m, 2 * m + 1 ≤ rel1 (ewRootSlot e B) K m := rel1_low hf1.monotone hf1.2 K
  obtain ⟨α', hα'le, hα'NF, _hα'H, _hα'N, D0⟩ :=
    rankToZeroAuxTC e heNF d D hmono hinfl hlow (three_le_rel1_rootSlot e B K) hαNF hαH
  obtain ⟨n, hn, htn⟩ := readoff_value_Zef2TC
    (ewIterTower_monotone hmono hinfl α d) (ewIterTower_infl hinfl α d)
    hP_mono D0 V hroot
  exact ⟨α', hα'le, hα'NF, n, hn, htn⟩

/-- The pipeline instance `goodsteinBodyE/[nm m]` is definitionally an `∃⁰ χ`, and it is
`Hierarchy 𝚺 1` (this feeds `GoodsteinPA.ReadoffValueGate.gated_root_of_sigma1` at assembly to
discharge the root `Gated` certificate). -/
lemma goodsteinBodyE_inst_shape (m : ℕ) :
    ∃ χ : ArithmeticSemiformula ℕ 1,
      goodsteinBodyE/[nm m] = (∃⁰ χ) ∧ Arithmetic.Hierarchy 𝚺 1 (∃⁰ χ) := by
  refine ⟨_, rfl, ?_⟩
  show Arithmetic.Hierarchy 𝚺 1 (goodsteinBodyE/[nm m])
  apply Arithmetic.Hierarchy.rew
  apply Arithmetic.Hierarchy.rew
  simp [goodsteinBody]

/-- From a PA proof of the goodstein sentence, the value-budget read-off pipeline (composed with
`embedding_Zef2TC_V3` at `goodsteinBodyE`) yields uniform budgets `B, d`, control `e`, node `α`,
and per-`m` a matrix `χ` and slot stage `K` such that any `Gated` certificate for `∃⁰ χ` produces a
TRUE numeral instance under the concrete `ewIter (Sslot tower P)` bound. -/
theorem readoff_value_goodstein
    (h : 𝗣𝗔 ⊢ ↑GoodsteinPA.goodsteinSentence) :
    ∃ B d : ℕ, ∃ e α : ONote, e.NF ∧ α.NF ∧ ∀ m : ℕ,
      ∃ (χ : ArithmeticSemiformula ℕ 1) (K : ℕ),
        goodsteinBodyE/[nm m] = (∃⁰ χ) ∧ Arithmetic.Hierarchy 𝚺 1 (∃⁰ χ) ∧
        ∀ (P : ℕ → ℕ) (V : ℕ), Monotone P → Gated P V (∃⁰ χ) →
          ∃ α', α' ≤ collapseIter d α ∧ α'.NF ∧
            ∃ n, n ≤ ewIter (Sslot (ewIterTower (rel1 (ewRootSlot e B) K) d α) P)
                    α' (Sslot (ewIterTower (rel1 (ewRootSlot e B) K) d α) P V) ∧
              atomTrue (χ/[nm n]) := by
  obtain ⟨B, d, e, α, heNF, hαNF, hall⟩ := embedding_Zef2TC_V3 h
  refine ⟨B, d, e, α, heNF, hαNF, fun m => ?_⟩
  obtain ⟨K, H, hαH, D⟩ := hall m
  obtain ⟨χ, hχeq, hchiS⟩ := goodsteinBodyE_inst_shape m
  rw [hχeq] at D
  refine ⟨χ, K, hχeq, hchiS, fun P V hP_mono hroot => ?_⟩
  exact readoff_value_pipeline hP_mono heNF hαNF hαH D V hroot

end GoodsteinPA.E1EmbeddingGrind
