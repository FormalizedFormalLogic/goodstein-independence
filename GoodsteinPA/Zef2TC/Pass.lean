module

public import GoodsteinPA.Zef2TC.CutStep

@[expose] public section

namespace GoodsteinPA.E1EmbeddingGrind

open LO LO.FirstOrder LO.FirstOrder.ArithmeticTerm ONote
open GoodsteinPA.OperatorZeh GoodsteinPA.OperatorZinfty

variable {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Finset (ArithmeticFormula ℕ)}

/-- The `≤`-slack wrapper over `Zef2TC` (mirror of `Zef2Prov`). -/
def Zef2TCProv (α e : ONote) (H : ONote → Prop) (f : ℕ → ℕ) (c : ℕ) (Γ : Finset (ArithmeticFormula ℕ)) : Prop :=
  ∃ α', α' ≤ α ∧ α'.NF ∧ Cl H α' ∧ Nlog α' ≤ f 0 ∧ Zef2TC α' e H f c Γ

namespace Zef2TCProv

lemma of (hNF : α.NF) (hH : Cl H α) (hN : Nlog α ≤ f 0) (D : Zef2TC α e H f c Γ) :
    Zef2TCProv α e H f c Γ :=
  ⟨α, le_refl _, hNF, hH, hN, D⟩

lemma mono {β} (hα : α ≤ β) : Zef2TCProv α e H f c Γ → Zef2TCProv β e H f c Γ := by
  rintro ⟨α', hα', hNF, hH, hN, D⟩
  exact ⟨α', le_trans hα' hα, hNF, hH, hN, D⟩

lemma weakening {Δ} (h : Γ ⊆ Δ) : Zef2TCProv α e H f c Γ → Zef2TCProv α e H f c Δ := by
  rintro ⟨α', hα', hNF, hH, hN, D⟩
  exact ⟨α', hα', hNF, hH, hN, Zef2TC.wk hN h D⟩

lemma mono_f {f'} (h : ∀ x, f x ≤ f' x) : Zef2TCProv α e H f c Γ → Zef2TCProv α e H f' c Γ := by
  rintro ⟨α', hα', hNF, hH, hN, D⟩
  exact ⟨α', hα', hNF, hH, le_trans hN (h 0), D.mono_f h⟩

end Zef2TCProv

set_option maxHeartbeats 1000000 in
/-- The running-family ∀/∃ cut-reduction over `Zef2TC`: given a running family of proofs of
`φ/[n]` at a fixed root `α` and a proof `D` of `Δ` containing `∃⁰ ∼φ`, produces a proof of
`(Δ.erase (∃⁰ ∼φ)) ∪ Γ` at the fresh root `α + γ` and output slot `g ∘ f`.
- [Tow20, §19.6] -/
theorem cutReduceAllAuxRunning_TC {φ : ArithmeticSemiformula ℕ 1} {c} {α e}
    {Γ : Finset (ArithmeticFormula ℕ)} {g : ℕ → ℕ} (hφc : φ.complexity < c) (hαNF : α.NF) (heNF : e.NF)
    (hg_mono : Monotone g) (hg_infl : ∀ x, x ≤ g x)
    (fam : ∀ n (H' : ONote → Prop), Zef2TC α e H' (rel1 g n) c (insert (φ/[nm n]) Γ))
    {γ : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {Δ : Finset (ArithmeticFormula ℕ)}
    (D : Zef2TC γ e H f c Δ) : γ.NF →
      Monotone f → (∀ x, x ≤ f x) → (∀ k, f 0 ≤ k → max (g 0) k + 1 ≤ g k) →
      φ.complexity ≤ f 0 → (∃⁰ ∼φ) ∈ Δ →
      Zef2TCProv (α + γ) e H (g ∘ f) c (Δ.erase (∃⁰ ∼φ) ∪ Γ) := by
  have hg0 : Nlog α ≤ g 0 := by
    have h := Zef2TC.gate (fam 0 (fun _ => True)); simpa [rel1] using h
  induction D with
  | @axL γ e H f c Δ ar hαN r v hp hn =>
      intro hγNF _ _ hsl _ hmem
      refine Zef2TCProv.of (ONote.add_nf α γ) (Cl_of_NF (ONote.add_nf α γ))
        (Nlog_add_le_comp hαNF hγNF hg0 hαN (hsl _ le_rfl)) ?_
      exact Zef2TC.axL (Nlog_add_le_comp hαNF hγNF hg0 hαN (hsl _ le_rfl)) r v
        (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), hp⟩))
        (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), hn⟩))
  | @trueRel γ e H f c Δ ar hαN r v htrue hmemr =>
      intro hγNF _ _ hsl _ hmem
      refine Zef2TCProv.of (ONote.add_nf α γ) (Cl_of_NF (ONote.add_nf α γ))
        (Nlog_add_le_comp hαNF hγNF hg0 hαN (hsl _ le_rfl)) ?_
      exact Zef2TC.trueRel (Nlog_add_le_comp hαNF hγNF hg0 hαN (hsl _ le_rfl)) r v htrue
        (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), hmemr⟩))
  | @trueNrel γ e H f c Δ ar hαN r v htrue hmemr =>
      intro hγNF _ _ hsl _ hmem
      refine Zef2TCProv.of (ONote.add_nf α γ) (Cl_of_NF (ONote.add_nf α γ))
        (Nlog_add_le_comp hαNF hγNF hg0 hαN (hsl _ le_rfl)) ?_
      exact Zef2TC.trueNrel (Nlog_add_le_comp hαNF hγNF hg0 hαN (hsl _ le_rfl)) r v htrue
        (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), hmemr⟩))
  | @verumR γ e H f c Δ hαN hmemv =>
      intro hγNF _ _ hsl _ hmem
      refine Zef2TCProv.of (ONote.add_nf α γ) (Cl_of_NF (ONote.add_nf α γ))
        (Nlog_add_le_comp hαNF hγNF hg0 hαN (hsl _ le_rfl)) ?_
      exact Zef2TC.verumR (Nlog_add_le_comp hαNF hγNF hg0 hαN (hsl _ le_rfl))
        (Finset.mem_union_left _ (Finset.mem_erase.mpr
          ⟨by intro h; simp [ExsQuantifier.exs] at h, hmemv⟩))
  | @wk γ e H f c Δsub Δsup hαN hsub D' ih =>
      intro hγNF hmono hinfl hsl hφread hmem
      by_cases hd : (∃⁰ ∼φ) ∈ Δsub
      · exact (ih hφc heNF fam hγNF hmono hinfl hsl hφread hd).weakening (by
          intro x hx; simp only [Finset.mem_union, Finset.mem_erase] at hx ⊢
          rcases hx with ⟨hne, hxs⟩ | hxΓ
          · exact Or.inl ⟨hne, hsub hxs⟩
          · exact Or.inr hxΓ)
      · exact ⟨γ, le_add_left_NF hαNF hγNF, hγNF, Cl_of_NF hγNF,
          le_trans hαN (reslot_exside hg_infl 0),
          Zef2TC.wk (le_trans hαN (reslot_exside hg_infl 0)) (by
            intro x hx; simp only [Finset.mem_union, Finset.mem_erase]
            exact Or.inl ⟨fun e0 => hd (e0 ▸ hx), hsub hx⟩) (D'.mono_f (reslot_exside hg_infl))⟩
  | @weak γ β e H f c Δsub Δsup hαN hβ hβNF hγNF' hβH hsub D' ih =>
      intro hγNF hmono hinfl hsl hφread hmem
      by_cases hd : (∃⁰ ∼φ) ∈ Δsub
      · exact ((ih hφc heNF fam hβNF hmono hinfl hsl hφread hd).weakening (by
          intro x hx; simp only [Finset.mem_union, Finset.mem_erase] at hx ⊢
          rcases hx with ⟨hne, hxs⟩ | hxΓ
          · exact Or.inl ⟨hne, hsub hxs⟩
          · exact Or.inr hxΓ)).mono
          (le_of_lt (add_lt_add_left_NF hαNF hβNF hγNF hβ))
      · exact ⟨β, le_of_lt (lt_of_lt_of_le hβ (le_add_left_NF hαNF hγNF)), hβNF, Cl_of_NF hβNF,
          le_trans (Zef2TC.gate D') (reslot_exside hg_infl 0),
          Zef2TC.wk (le_trans (Zef2TC.gate D') (reslot_exside hg_infl 0)) (by
            intro x hx; simp only [Finset.mem_union, Finset.mem_erase]
            exact Or.inl ⟨fun e0 => hd (e0 ▸ hx), hsub hx⟩) (D'.mono_f (reslot_exside hg_infl))⟩
  | @andI γ βφ' βψ' e H f c Γ₀ hαN χ₁ χ₂ hβφ hβψ hβφNF hβψNF hγNF' hβφH hβψH d₁ d₂ ih₁ ih₂ =>
      intro hγNF hmono hinfl hsl hφread hmem
      have hhead : (χ₁ ⋏ χ₂ : ArithmeticFormula ℕ) ≠ (∃⁰ ∼φ) := by
        intro h; simp [ExsQuantifier.exs] at h
      have hmem0 : (∃⁰ ∼φ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
      have haddNF : (α + γ).NF := ONote.add_nf α γ
      obtain ⟨a₁, ha₁le, ha₁NF, ha₁H, ha₁g, D₁⟩ := ih₁ hφc heNF fam hβφNF hmono hinfl hsl hφread
        (Finset.mem_insert_of_mem hmem0)
      obtain ⟨a₂, ha₂le, ha₂NF, ha₂H, ha₂g, D₂⟩ := ih₂ hφc heNF fam hβψNF hmono hinfl hsl hφread
        (Finset.mem_insert_of_mem hmem0)
      have D₁' : Zef2TC a₁ e H (g ∘ f) c (insert χ₁ (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) :=
        Zef2TC.wk ha₁g (by
          intro x hx
          simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢; tauto) D₁
      have D₂' : Zef2TC a₂ e H (g ∘ f) c (insert χ₂ (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) :=
        Zef2TC.wk ha₂g (by
          intro x hx
          simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢; tauto) D₂
      refine Zef2TCProv.of haddNF (Cl_of_NF haddNF)
        (Nlog_add_le_comp hαNF hγNF hg0 hαN (hsl _ le_rfl)) ?_
      have hAnd : Zef2TC (α + γ) e H (g ∘ f) c
          (insert (χ₁ ⋏ χ₂) (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) :=
        Zef2TC.andI (Nlog_add_le_comp hαNF hγNF hg0 hαN (hsl _ le_rfl)) χ₁ χ₂
          (lt_of_le_of_lt ha₁le (add_lt_add_left_NF hαNF hβφNF hγNF hβφ))
          (lt_of_le_of_lt ha₂le (add_lt_add_left_NF hαNF hβψNF hγNF hβψ))
          ha₁NF ha₂NF haddNF ha₁H ha₂H D₁' D₂'
      exact Zef2TC.wk (Nlog_add_le_comp hαNF hγNF hg0 hαN (hsl _ le_rfl)) (by
        intro x hx
        simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢
        rcases hx with rfl | hx
        · exact Or.inl ⟨hhead, Or.inl rfl⟩
        · tauto) hAnd
  | @orI γ β e H f c Γ₀ hαN χ₁ χ₂ hβ hβNF hγNF' hβH d₁ ih =>
      intro hγNF hmono hinfl hsl hφread hmem
      have hhead : (χ₁ ⋎ χ₂ : ArithmeticFormula ℕ) ≠ (∃⁰ ∼φ) := by
        intro h; simp [ExsQuantifier.exs] at h
      have hmem0 : (∃⁰ ∼φ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
      have haddNF : (α + γ).NF := ONote.add_nf α γ
      obtain ⟨a, hale, haNF, haH, hag, Da⟩ := ih hφc heNF fam hβNF hmono hinfl hsl hφread
        (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hmem0))
      have Da' : Zef2TC a e H (g ∘ f) c
          (insert χ₁ (insert χ₂ (Γ₀.erase (∃⁰ ∼φ) ∪ Γ))) :=
        Zef2TC.wk hag (by
          intro x hx
          simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢; tauto) Da
      refine Zef2TCProv.of haddNF (Cl_of_NF haddNF)
        (Nlog_add_le_comp hαNF hγNF hg0 hαN (hsl _ le_rfl)) ?_
      have hOr : Zef2TC (α + γ) e H (g ∘ f) c
          (insert (χ₁ ⋎ χ₂) (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) :=
        Zef2TC.orI (Nlog_add_le_comp hαNF hγNF hg0 hαN (hsl _ le_rfl)) χ₁ χ₂
          (lt_of_le_of_lt hale (add_lt_add_left_NF hαNF hβNF hγNF hβ))
          haNF haddNF haH Da'
      exact Zef2TC.wk (Nlog_add_le_comp hαNF hγNF hg0 hαN (hsl _ le_rfl)) (by
        intro x hx
        simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢
        rcases hx with rfl | hx
        · exact Or.inl ⟨hhead, Or.inl rfl⟩
        · tauto) hOr
  | @allω γ e H f c Γ₀ hαN χ β hβ hβNF hγNF' hβH dd ih =>
      intro hγNF hmono hinfl hsl hφread hmem
      have hhead : (∀⁰ χ) ≠ (∃⁰ ∼φ) := by intro h; simp [UnivQuantifier.all, ExsQuantifier.exs] at h
      have hmem0 : (∃⁰ ∼φ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
      have haddNF : (α + γ).NF := ONote.add_nf α γ
      have ihn : ∀ n, Zef2TCProv (α + β n) e (adjoin H n) (g ∘ rel1 f n) c
          (insert (χ/[nm n]) (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) := by
        intro n
        have hread : φ.complexity ≤ (rel1 f n) 0 := by
          simp only [rel1]; exact le_trans hφread (hmono (Nat.zero_le _))
        exact (ih n hφc heNF fam (hβNF n) (rel1_monotone hmono n) (rel1_infl hinfl n)
          (fun k hk => hsl k (le_trans (by
            simp only [rel1]; exact hmono (Nat.zero_le _)) hk))
          hread (Finset.mem_insert_of_mem hmem0)).weakening (by
            intro x hx
            simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢; tauto)
      refine Zef2TCProv.of haddNF (Cl_of_NF haddNF) (Nlog_add_le_comp hαNF hγNF hg0 hαN (hsl _ le_rfl)) ?_
      have hAll : Zef2TC (α + γ) e H (g ∘ f) c
          (insert (∀⁰ χ) (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) := by
        exact Zef2TC.allω (Nlog_add_le_comp hαNF hγNF hg0 hαN (hsl _ le_rfl)) χ (fun n => (ihn n).choose)
          (fun n => lt_of_le_of_lt (ihn n).choose_spec.1
            (add_lt_add_left_NF hαNF (hβNF n) hγNF (hβ n)))
          (fun n => (ihn n).choose_spec.2.1) haddNF
          (fun n => Cl_of_NF (ihn n).choose_spec.2.1)
          (fun n => (ihn n).choose_spec.2.2.2.2)
      exact Zef2TC.wk (Nlog_add_le_comp hαNF hγNF hg0 hαN (hsl _ le_rfl)) (by
        intro x hx
        simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢
        rcases hx with rfl | hx
        · exact Or.inl ⟨hhead, Or.inl rfl⟩
        · tauto) hAll
  | @exI γ β e H f c Γ₀ hαN χ n hβ hβNF hγNF' hβH hbound dχ ih =>
      intro hγNF hmono hinfl hsl hφread hmem
      have haddNF : (α + γ).NF := ONote.add_nf α γ
      by_cases hhd : (∃⁰ χ) = (∃⁰ ∼φ)
      · have hχ : χ = ∼φ := by simpa [ExsQuantifier.exs] using hhd
        subst hχ
        rw [Finset.erase_insert_eq_erase]
        have hNeg : (∼φ)/[nm n] = ∼(φ/[nm n]) := by simp
        have hcompl : (φ/[nm n]).complexity < c := by simpa using hφc
        have hcutRead : (φ/[nm n]).complexity ≤ (g ∘ f) 0 := by
          have he : (φ/[nm n]).complexity = φ.complexity := by simp
          rw [he]; exact le_trans hφread (hg_infl (f 0))
        have hg0comp : Nlog α ≤ (g ∘ f) 0 := le_trans hg0 (hg_mono (Nat.zero_le _))
        have famn : Zef2TC α e H (g ∘ f) c (insert (φ/[nm n]) (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) :=
          Zef2TC.wk hg0comp (by
            intro x hx; simp only [Finset.mem_insert, Finset.mem_union] at hx ⊢; tauto)
            ((fam n H).mono_f (reslot_family hg_mono hinfl hmono hbound))
        have hαlt : α < α + γ := by
          haveI := hαNF; haveI := hγNF
          refine ONote.lt_def.mpr ?_
          rw [ONote.repr_add]
          have hγpos : (0 : Ordinal) < γ.repr := lt_of_le_of_lt (by simp) (ONote.lt_def.mp hβ)
          simpa using (add_lt_add_iff_left α.repr).mpr hγpos
        by_cases hd : (∃⁰ ∼φ) ∈ Γ₀
        · obtain ⟨a, hale, haNF, haH, hag, Da⟩ := ih hφc heNF fam hβNF hmono hinfl hsl hφread
            (Finset.mem_insert_of_mem hd)
          have Da' : Zef2TC a e H (g ∘ f) c
              (insert (∼(φ/[nm n])) (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) :=
            Zef2TC.wk hag (by
              intro x hx
              simp only [hNeg, Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢; tauto) Da
          refine Zef2TCProv.of haddNF (Cl_of_NF haddNF) (Nlog_add_le_comp hαNF hγNF hg0 hαN (hsl _ le_rfl)) ?_
          exact Zef2TC.cut (Nlog_add_le_comp hαNF hγNF hg0 hαN (hsl _ le_rfl)) (φ/[nm n]) hcompl hcutRead hαlt
            (lt_of_le_of_lt hale (add_lt_add_left_NF hαNF hβNF hγNF hβ))
            hαNF haNF haddNF (Cl_of_NF hαNF) haH famn Da'
        · have Dβ' : Zef2TC β e H (g ∘ f) c
              (insert (∼(φ/[nm n])) (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) :=
            Zef2TC.wk (le_trans (Zef2TC.gate dχ) (reslot_exside hg_infl 0)) (by
              intro x hx
              simp only [hNeg, Finset.mem_insert] at hx
              simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_erase]
              rcases hx with rfl | hxΓ₀
              · exact Or.inl rfl
              · exact Or.inr (Or.inl ⟨fun e0 => hd (e0 ▸ hxΓ₀), hxΓ₀⟩))
              (dχ.mono_f (reslot_exside hg_infl))
          refine Zef2TCProv.of haddNF (Cl_of_NF haddNF) (Nlog_add_le_comp hαNF hγNF hg0 hαN (hsl _ le_rfl)) ?_
          exact Zef2TC.cut (Nlog_add_le_comp hαNF hγNF hg0 hαN (hsl _ le_rfl)) (φ/[nm n]) hcompl hcutRead hαlt
            (lt_of_lt_of_le hβ (le_add_left_NF hαNF hγNF))
            hαNF hβNF haddNF (Cl_of_NF hαNF) (Cl_of_NF hβNF) famn Dβ'
      · have hmem0 : (∃⁰ ∼φ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhd e.symm
        obtain ⟨a, hale, haNF, haH, hag, Da⟩ := ih hφc heNF fam hβNF hmono hinfl hsl hφread
          (Finset.mem_insert_of_mem hmem0)
        have Da' : Zef2TC a e H (g ∘ f) c (insert (χ/[nm n]) (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) :=
          Zef2TC.wk hag (by
            intro x hx
            simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢; tauto) Da
        refine Zef2TCProv.of haddNF (Cl_of_NF haddNF) (Nlog_add_le_comp hαNF hγNF hg0 hαN (hsl _ le_rfl)) ?_
        have hbound' : n ≤ (g ∘ f) 0 := le_trans hbound (hg_infl (f 0))
        exact Zef2TC.wk (Nlog_add_le_comp hαNF hγNF hg0 hαN (hsl _ le_rfl)) (by
          intro x hx
          simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢
          rcases hx with rfl | hx
          · exact Or.inl ⟨hhd, Or.inl rfl⟩
          · tauto)
          (Zef2TC.exI (Nlog_add_le_comp hαNF hγNF hg0 hαN (hsl _ le_rfl)) χ n
            (lt_of_le_of_lt hale (add_lt_add_left_NF hαNF hβNF hγNF hβ))
            haNF haddNF haH hbound' Da')
  | @cut γ βφ βψ e H f c Γ₀ hαN χ hχc hcutRead' hβφ hβψ hβφNF hβψNF hγNF' hβφH hβψH d₁ d₂ ih₁ ih₂ =>
      intro hγNF hmono hinfl hsl hφread hmem
      obtain ⟨a₁, ha₁le, ha₁NF, ha₁H, ha₁g, D₁⟩ := ih₁ hφc heNF fam hβφNF hmono hinfl hsl hφread
        (Finset.mem_insert_of_mem hmem)
      obtain ⟨a₂, ha₂le, ha₂NF, ha₂H, ha₂g, D₂⟩ := ih₂ hφc heNF fam hβψNF hmono hinfl hsl hφread
        (Finset.mem_insert_of_mem hmem)
      have haddNF : (α + γ).NF := ONote.add_nf α γ
      have D₁' : Zef2TC a₁ e H (g ∘ f) c (insert χ (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) :=
        Zef2TC.wk ha₁g (by
          intro x hx
          simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢; tauto) D₁
      have D₂' : Zef2TC a₂ e H (g ∘ f) c (insert (∼χ) (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) :=
        Zef2TC.wk ha₂g (by
          intro x hx
          simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢; tauto) D₂
      refine Zef2TCProv.of haddNF (Cl_of_NF haddNF) (Nlog_add_le_comp hαNF hγNF hg0 hαN (hsl _ le_rfl)) ?_
      exact Zef2TC.cut (Nlog_add_le_comp hαNF hγNF hg0 hαN (hsl _ le_rfl)) χ hχc
        (le_trans hcutRead' (hg_infl (f 0)))
        (lt_of_le_of_lt ha₁le (add_lt_add_left_NF hαNF hβφNF hγNF hβφ))
        (lt_of_le_of_lt ha₂le (add_lt_add_left_NF hαNF hβψNF hγNF hβψ))
        ha₁NF ha₂NF haddNF ha₁H ha₂H D₁' D₂'

/-- The bound-exposing principal ∀/∃ cut-reduction step over `Zef2TC`: inverts the ∀-side proof
via `allω_inversion`, feeds `cutReduceAllAuxRunning_TC`, and bounds the output witness by `P₁ + P₂`.
- [Tow20, §19.6] -/
theorem stepAllωTC_bnd {E} {H} {c} {Γ}
    {χ : ArithmeticSemiformula ℕ 1} {P₁ P₂ : ONote} {f g : ℕ → ℕ}
    (hP₁ : P₁.NF) (hP₂ : P₂.NF)
    (hENF : E.NF) (hχc : χ.complexity < c)
    (hg_mono : Monotone g) (hg_infl : ∀ x, x ≤ g x)
    (hg_slack : ∀ k, f 0 ≤ k → max (g 0) k + 1 ≤ g k)
    (hf_mono : Monotone f) (hf_infl : ∀ x, x ≤ f x) (hχRead : χ.complexity ≤ f 0)
    (D₁ : Zef2TCProv P₁ E H g c (insert (∀⁰ χ) Γ))
    (D₂ : Zef2TCProv P₂ E H f c (insert (∃⁰ ∼χ) Γ)) :
    Zef2TCProv (P₁ + P₂) E H (g ∘ f) c Γ := by
  obtain ⟨α₁, hα₁le, hNF₁, _, _, d₁⟩ := D₁
  obtain ⟨γ₁, hγ₁le, hNF₂, _, _, d₂⟩ := D₂
  have fam : ∀ n (H' : ONote → Prop), Zef2TC α₁ E H' (rel1 g n) c (insert (χ/[nm n]) Γ) := by
    intro n H'
    have hinv := allω_inversion (φ := χ) n d₁ hg_mono
    rw [Finset.erase_insert_eq_erase] at hinv
    exact (Zef2TC.wk (Zef2TC.gate hinv)
      (Finset.insert_subset_insert _ (Finset.erase_subset _ _)) hinv).change_H
  have hred := cutReduceAllAuxRunning_TC hχc hNF₁ hENF hg_mono hg_infl fam
    d₂ hNF₂ hf_mono hf_infl hg_slack hχRead (Finset.mem_insert_self _ _)
  have hbnd : α₁ + γ₁ ≤ P₁ + P₂ := by
    haveI := hNF₁; haveI := hNF₂; haveI := hP₁; haveI := hP₂
    rw [ONote.le_def, ONote.repr_add, ONote.repr_add]
    exact add_le_add (ONote.le_def.mp hα₁le) (ONote.le_def.mp hγ₁le)
  exact ((hred.weakening
    (Finset.union_subset (Finset.erase_insert_subset _ _) (Finset.Subset.refl Γ))).mono hbnd)

set_option maxHeartbeats 3200000 in
/-- One cut-elimination pass over `Zef2TC`: given a proof at rank `r = c + 1`, produces a proof
at rank `c` whose ordinal is the collapse `collapse α` and whose witness slot iterates to
`ewIter f α`. The top-rank cut dispatches by cut-formula shape to `stepAllωTC_bnd` (∀/∃),
`stepAnd_Zef2TC` (⋏/⋎), `stepVerum_Zef2TC` (⊤/⊥), and `stepAtom_Zef2TC` (atoms). -/
theorem passAuxTC (c : ℕ) {e} (heNF : e.NF)
    {α : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {Γ : Finset (ArithmeticFormula ℕ)} {r : ℕ}
    (D : Zef2TC α e H f r Γ) : r = c + 1 → Monotone f → (∀ x, x ≤ f x) → (∀ m, 2 * m + 1 ≤ f m) →
      3 ≤ f 0 → α.NF → Cl H α →
      Zef2TCProv (collapse α) e H (ewIter f α) c Γ := by
  induction D with
  | @axL α e H f r Γ ar hαN rel v hp hn =>
      intro hr hmono hinfl hlow hbase3 hαNF hαH
      have hg := Nlog_collapse_le hlow hαN
      exact Zef2TCProv.of (collapse_NF hαNF) (Cl_of_NF (collapse_NF hαNF)) hg
        (Zef2TC.axL hg rel v hp hn)
  | @trueRel α e H f r Γ ar hαN rel v htrue hmem =>
      intro hr hmono hinfl hlow hbase3 hαNF hαH
      have hg := Nlog_collapse_le hlow hαN
      exact Zef2TCProv.of (collapse_NF hαNF) (Cl_of_NF (collapse_NF hαNF)) hg
        (Zef2TC.trueRel hg rel v htrue hmem)
  | @trueNrel α e H f r Γ ar hαN rel v htrue hmem =>
      intro hr hmono hinfl hlow hbase3 hαNF hαH
      have hg := Nlog_collapse_le hlow hαN
      exact Zef2TCProv.of (collapse_NF hαNF) (Cl_of_NF (collapse_NF hαNF)) hg
        (Zef2TC.trueNrel hg rel v htrue hmem)
  | @verumR α e H f r Γ hαN hmem =>
      intro hr hmono hinfl hlow hbase3 hαNF hαH
      have hg := Nlog_collapse_le hlow hαN
      exact Zef2TCProv.of (collapse_NF hαNF) (Cl_of_NF (collapse_NF hαNF)) hg
        (Zef2TC.verumR hg hmem)
  | @wk α e H f r Δ Γ hαN hsub D' ih =>
      intro hr hmono hinfl hlow hbase3 hαNF hαH
      exact (ih heNF hr hmono hinfl hlow hbase3 hαNF hαH).weakening hsub
  | @weak α β e H f r Δ Γ hαN hβ hβNF hαNF' hβH hsub D' ih =>
      intro hr hmono hinfl hlow hbase3 hαNF hαH
      obtain ⟨a, hale, haNF, haH, hag, Da⟩ := ih heNF hr hmono hinfl hlow hbase3 hβNF (Cl_of_NF hβNF)
      have hslot := ewIter_slot_le hmono hinfl hβNF hβ (Zef2TC.gate D')
      exact ⟨a, le_trans hale (le_of_lt (collapse_strictMono hβNF hβ)), haNF, haH,
        le_trans hag (hslot 0), Zef2TC.wk (le_trans hag (hslot 0)) hsub (Da.mono_f hslot)⟩
  | @andI α βφ βψ e H f r Γ hαN φ ψ hβφ hβψ hβφNF hβψNF hαNF' hβφH hβψH dφ dψ ih₁ ih₂ =>
      intro hr hmono hinfl hlow hbase3 hαNF hαH
      have hg := Nlog_collapse_le hlow hαN
      obtain ⟨a₁, ha₁le, ha₁NF, ha₁H, ha₁g, D₁⟩ :=
        ih₁ heNF hr hmono hinfl hlow hbase3 hβφNF (Cl_of_NF hβφNF)
      obtain ⟨a₂, ha₂le, ha₂NF, ha₂H, ha₂g, D₂⟩ :=
        ih₂ heNF hr hmono hinfl hlow hbase3 hβψNF (Cl_of_NF hβψNF)
      have hsφ := ewIter_slot_le hmono hinfl hβφNF hβφ (Zef2TC.gate dφ)
      have hsψ := ewIter_slot_le hmono hinfl hβψNF hβψ (Zef2TC.gate dψ)
      refine Zef2TCProv.of (collapse_NF hαNF) (Cl_of_NF (collapse_NF hαNF)) hg ?_
      exact Zef2TC.andI hg φ ψ
        (lt_of_le_of_lt ha₁le (collapse_strictMono hβφNF hβφ))
        (lt_of_le_of_lt ha₂le (collapse_strictMono hβψNF hβψ))
        ha₁NF ha₂NF (collapse_NF hαNF) ha₁H ha₂H (D₁.mono_f hsφ) (D₂.mono_f hsψ)
  | @orI α β e H f r Γ hαN φ ψ hβ hβNF hαNF' hβH dd ih =>
      intro hr hmono hinfl hlow hbase3 hαNF hαH
      have hg := Nlog_collapse_le hlow hαN
      obtain ⟨a, hale, haNF, haH, hag, Da⟩ :=
        ih heNF hr hmono hinfl hlow hbase3 hβNF (Cl_of_NF hβNF)
      have hslot := ewIter_slot_le hmono hinfl hβNF hβ (Zef2TC.gate dd)
      refine Zef2TCProv.of (collapse_NF hαNF) (Cl_of_NF (collapse_NF hαNF)) hg ?_
      exact Zef2TC.orI hg φ ψ
        (lt_of_le_of_lt hale (collapse_strictMono hβNF hβ))
        haNF (collapse_NF hαNF) haH (Da.mono_f hslot)
  | @allω α e H f r Γ hαN χ β hβ hβNF hαNF' hβH dd ih =>
      intro hr hmono hinfl hlow hbase3 hαNF hαH
      have hg := Nlog_collapse_le hlow hαN
      have hbranch : ∀ n, Zef2TCProv (collapse (β n)) e (adjoin H n)
          (ewIter (rel1 f n) (β n)) c (insert (χ/[nm n]) Γ) := fun n =>
        ih n heNF hr (rel1_monotone hmono n) (rel1_infl hinfl n) (rel1_low hmono hlow n)
          (le_trans hbase3 (by simp only [rel1]; exact hmono (Nat.zero_le _)))
          (hβNF n) (Cl_of_NF (hβNF n))
      choose a hale haNF haH hagate Da using hbranch
      have hlift : ∀ n x, ewIter (rel1 f n) (β n) x ≤ rel1 (ewIter f α) n x := by
        intro n x
        refine le_trans (ewIter_rel1_le hmono hinfl (β n) n x) ?_
        have hgate : Nlog (β n) ≤ f (Nlog α + max n x) := by
          have hgn := Zef2TC.gate (dd n)
          simp only [rel1] at hgn
          refine le_trans hgn (hmono ?_)
          omega
        simpa [rel1] using ewIter_le_of_lt (f := f) hinfl (hβNF n) (hβ n) hgate
      have Da' : ∀ n, Zef2TC (a n) e (adjoin H n) (rel1 (ewIter f α) n) c
          (insert (χ/[nm n]) Γ) := fun n => (Da n).mono_f (hlift n)
      have haltcol : ∀ n, a n < collapse α :=
        fun n => lt_of_le_of_lt (hale n) (collapse_strictMono (hβNF n) (hβ n))
      refine Zef2TCProv.of (collapse_NF hαNF) (Cl_of_NF (collapse_NF hαNF)) hg ?_
      exact Zef2TC.allω hg χ a haltcol haNF (collapse_NF hαNF)
        (fun n => Cl_of_NF (haNF n)) Da'
  | @exI α β e H f r Γ hαN χ n hβ hβNF hαNF' hβH hbound dχ ih =>
      intro hr hmono hinfl hlow hbase3 hαNF hαH
      obtain ⟨a, hale, haNF, haH, hag, Da⟩ :=
        ih heNF hr hmono hinfl hlow hbase3 hβNF (Cl_of_NF hβNF)
      have hslot := ewIter_slot_le hmono hinfl hβNF hβ (Zef2TC.gate dχ)
      have haltcol : a < collapse α := lt_of_le_of_lt hale (collapse_strictMono hβNF hβ)
      have hg := Nlog_collapse_le hlow hαN
      have hbound' : n ≤ ewIter f α 0 := le_trans hbound (ewIter_base_le hinfl α)
      refine Zef2TCProv.of (collapse_NF hαNF) (Cl_of_NF (collapse_NF hαNF)) hg ?_
      exact Zef2TC.exI hg χ n haltcol haNF (collapse_NF hαNF) haH hbound'
        (Zef2TC.wk (le_trans hag (hslot 0)) (Finset.Subset.refl _) (Da.mono_f hslot))
  | @cut α βφ βψ e H f r Γ hαN χ hcompl hcutRead hβφ hβψ hβφNF hβψNF hαNF' hβφH hβψH d₁ d₂ ih₁ ih₂ =>
      intro hr hmono hinfl hlow hbase3 hαNF hαH
      have hg := Nlog_collapse_le hlow hαN
      have hf0 : f 0 ≤ ewIter f α 0 := ewIter_base_le hinfl α
      have hαpos : (0 : ONote) < α := by
        cases α with
        | zero => exact absurd (ONote.lt_def.mp hβφ) not_lt_zero
        | oadd e' n' a' => exact oadd_pos e' n' a'
      by_cases hc : χ.complexity < c
      · -- SUB-RANK cut: keep it, rebuild at rank `c`
        obtain ⟨aφ, haφle, haφNF, haφH, haφg, Dφ⟩ :=
          ih₁ heNF hr hmono hinfl hlow hbase3 hβφNF (Cl_of_NF hβφNF)
        obtain ⟨aψ, haψle, haψNF, haψH, haψg, Dψ⟩ :=
          ih₂ heNF hr hmono hinfl hlow hbase3 hβψNF (Cl_of_NF hβψNF)
        have hsφ := ewIter_slot_le hmono hinfl hβφNF hβφ (Zef2TC.gate d₁)
        have hsψ := ewIter_slot_le hmono hinfl hβψNF hβψ (Zef2TC.gate d₂)
        have haφcol : aφ < collapse α := lt_of_le_of_lt haφle (collapse_strictMono hβφNF hβφ)
        have haψcol : aψ < collapse α := lt_of_le_of_lt haψle (collapse_strictMono hβψNF hβψ)
        refine Zef2TCProv.of (collapse_NF hαNF) (Cl_of_NF (collapse_NF hαNF)) hg ?_
        exact Zef2TC.cut hg χ hc (le_trans hcutRead hf0) haφcol haψcol
          haφNF haψNF (collapse_NF hαNF) haφH haψH (Dφ.mono_f hsφ) (Dψ.mono_f hsψ)
      · -- TOP-RANK cut: eliminate by cut-formula shape
        have hgφ : Nlog βφ ≤ f 0 := Zef2TC.gate d₁
        have hgψ : Nlog βψ ≤ f 0 := Zef2TC.gate d₂
        have hcomp : ∀ m, ewIter f βφ (ewIter f βψ m) ≤ ewIter f α m :=
          ewIter_comp_le hmono hinfl hβφNF hβψNF hβφ hβψ hgφ hgψ
        have hcomp' : ∀ m, ewIter f βψ (ewIter f βφ m) ≤ ewIter f α m :=
          ewIter_comp_le hmono hinfl hβψNF hβφNF hβψ hβφ hgψ hgφ
        have hcollt : collapse βφ + collapse βψ < collapse α :=
          collapse_add_lt hβφNF hβψNF hαNF hβφ hβψ
        have hcollt' : collapse βψ + collapse βφ < collapse α :=
          collapse_add_lt hβψNF hβφNF hαNF hβψ hβφ
        have P₁ := ih₁ heNF hr hmono hinfl hlow hbase3 hβφNF (Cl_of_NF hβφNF)
        have P₂ := ih₂ heNF hr hmono hinfl hlow hbase3 hβψNF (Cl_of_NF hβψNF)
        have hsφ := ewIter_slot_le hmono hinfl hβφNF hβφ hgφ
        have hsψ := ewIter_slot_le hmono hinfl hβψNF hβψ hgψ
        -- the `Nlog … + 2` gate for the finite-step roots, paid by `hbase3` + `ewIter_low`
        have hFφ : 2 * ewIter f βφ 0 + 1 ≤ ewIter f α 0 :=
          le_trans (ewIter_low hinfl hlow βφ _)
            (ewIter_lower hβφNF hβφ (le_trans hgφ (hmono (Nat.zero_le _))))
        have hFψ : 2 * ewIter f βψ 0 + 1 ≤ ewIter f α 0 :=
          le_trans (ewIter_low hinfl hlow βψ _)
            (ewIter_lower hβψNF hβψ (le_trans hgψ (hmono (Nat.zero_le _))))
        have hxφ3 : 3 ≤ ewIter f βφ 0 := le_trans hbase3 (ewIter_base_le hinfl βφ)
        have hxψ3 : 3 ≤ ewIter f βψ 0 := le_trans hbase3 (ewIter_base_le hinfl βψ)
        cases χ with
        | verum =>
            obtain ⟨a₂, ha₂le, ha₂NF, ha₂H, ha₂g, Da₂⟩ := P₂
            have Da₂' : Zef2TC a₂ e H (ewIter f βψ) c (insert (⊥ : ArithmeticFormula ℕ) Γ) := Da₂
            have hD := stepVerum_Zef2TC Da₂'
            exact ⟨a₂, le_trans ha₂le (le_of_lt (collapse_strictMono hβψNF hβψ)), ha₂NF, ha₂H,
              le_trans ha₂g (hsψ 0), hD.mono_f hsψ⟩
        | falsum =>
            obtain ⟨a₁, ha₁le, ha₁NF, ha₁H, ha₁g, Da₁⟩ := P₁
            have hD := stepVerum_Zef2TC Da₁
            exact ⟨a₁, le_trans ha₁le (le_of_lt (collapse_strictMono hβφNF hβφ)), ha₁NF, ha₁H,
              le_trans ha₁g (hsφ 0), hD.mono_f hsφ⟩
        | and φ₁ φ₂ =>
            have hcR := hcutRead
            have hcm := hcompl
            have hcn := hc
            simp only [Semiformula.complexity_and'] at hcR hcm hcn
            have hφ₁c : φ₁.complexity < c := by omega
            have hφ₂c : φ₂.complexity < c := by omega
            have hread₁ : φ₁.complexity ≤ ewIter f α 0 := by omega
            have hread₂ : φ₂.complexity ≤ ewIter f α 0 := by omega
            obtain ⟨a₁, ha₁le, ha₁NF, ha₁H, ha₁g, Da₁⟩ := P₁
            obtain ⟨a₂, ha₂le, ha₂NF, ha₂H, ha₂g, Da₂'⟩ := P₂
            have Da₂ : Zef2TC a₂ e H (ewIter f βψ) c (insert (∼φ₁ ⋎ ∼φ₂) Γ) := Da₂'
            have hb1 := Nlog_add_le_max_succ a₁ ha₁NF a₂ ha₂NF
            have hgate : Nlog (a₁ + a₂) + 2 ≤ ewIter f α 0 := by
              have h₁ := hsφ 0
              have h₂ := hsψ 0
              omega
            have hstep := stepAnd_Zef2TC ha₁NF ha₂NF hφ₁c hφ₂c hread₁ hread₂ hgate
              (Da₁.mono_f hsφ) (Da₂.mono_f hsψ)
            have hσNF : (a₁ + a₂).NF := ONote.add_nf a₁ a₂
            have hσlt : a₁ + a₂ < collapse α := by
              refine lt_of_le_of_lt ?_ hcollt
              haveI := ha₁NF; haveI := ha₂NF
              haveI := collapse_NF hβφNF; haveI := collapse_NF hβψNF
              haveI := ONote.add_nf a₁ a₂
              haveI := ONote.add_nf (collapse βφ) (collapse βψ)
              rw [ONote.le_def, ONote.repr_add, ONote.repr_add]
              exact add_le_add (ONote.le_def.mp ha₁le) (ONote.le_def.mp ha₂le)
            have h1 := osucc_lt_collapse hσNF hαNF hαpos hσlt
            have h2 := osucc_lt_collapse (osucc_NF hσNF) hαNF hαpos h1
            have hNg : Nlog (osucc (osucc (a₁ + a₂))) ≤ ewIter f α 0 := by
              have hs1 := Nlog_osucc_le hσNF
              have hs2 := Nlog_osucc_le (osucc_NF hσNF)
              omega
            exact ⟨osucc (osucc (a₁ + a₂)), le_of_lt h2, osucc_NF (osucc_NF hσNF),
              Cl_of_NF (osucc_NF (osucc_NF hσNF)), hNg, hstep⟩
        | or φ₁ φ₂ =>
            have hcR := hcutRead
            have hcm := hcompl
            have hcn := hc
            simp only [Semiformula.complexity_or'] at hcR hcm hcn
            have hn₁ : (∼φ₁ : ArithmeticFormula ℕ).complexity = φ₁.complexity := Semiformula.complexity_neg φ₁
            have hn₂ : (∼φ₂ : ArithmeticFormula ℕ).complexity = φ₂.complexity := Semiformula.complexity_neg φ₂
            have hφ₁c : (∼φ₁ : ArithmeticFormula ℕ).complexity < c := by omega
            have hφ₂c : (∼φ₂ : ArithmeticFormula ℕ).complexity < c := by omega
            have hread₁ : (∼φ₁ : ArithmeticFormula ℕ).complexity ≤ ewIter f α 0 := by omega
            have hread₂ : (∼φ₂ : ArithmeticFormula ℕ).complexity ≤ ewIter f α 0 := by omega
            obtain ⟨a₁, ha₁le, ha₁NF, ha₁H, ha₁g, Da₁⟩ := P₁
            obtain ⟨a₂, ha₂le, ha₂NF, ha₂H, ha₂g, Da₂'⟩ := P₂
            have Da₂ : Zef2TC a₂ e H (ewIter f βψ) c (insert (∼φ₁ ⋏ ∼φ₂) Γ) := Da₂'
            have hd₁ : Zef2TC a₁ e H (ewIter f α) c (insert (∼(∼φ₁) ⋎ ∼(∼φ₂)) Γ) := by
              rw [show (∼(∼φ₁) ⋎ ∼(∼φ₂) : ArithmeticFormula ℕ) = φ₁ ⋎ φ₂ from by simp]
              exact Da₁.mono_f hsφ
            have hb1 := Nlog_add_le_max_succ a₂ ha₂NF a₁ ha₁NF
            have hgate : Nlog (a₂ + a₁) + 2 ≤ ewIter f α 0 := by
              have h₁ := hsφ 0
              have h₂ := hsψ 0
              omega
            have hstep := stepAnd_Zef2TC ha₂NF ha₁NF hφ₁c hφ₂c hread₁ hread₂ hgate
              (Da₂.mono_f hsψ) hd₁
            have hσNF : (a₂ + a₁).NF := ONote.add_nf a₂ a₁
            have hσlt : a₂ + a₁ < collapse α := by
              refine lt_of_le_of_lt ?_ hcollt'
              haveI := ha₁NF; haveI := ha₂NF
              haveI := collapse_NF hβφNF; haveI := collapse_NF hβψNF
              haveI := ONote.add_nf a₂ a₁
              haveI := ONote.add_nf (collapse βψ) (collapse βφ)
              rw [ONote.le_def, ONote.repr_add, ONote.repr_add]
              exact add_le_add (ONote.le_def.mp ha₂le) (ONote.le_def.mp ha₁le)
            have h1 := osucc_lt_collapse hσNF hαNF hαpos hσlt
            have h2 := osucc_lt_collapse (osucc_NF hσNF) hαNF hαpos h1
            have hNg : Nlog (osucc (osucc (a₂ + a₁))) ≤ ewIter f α 0 := by
              have hs1 := Nlog_osucc_le hσNF
              have hs2 := Nlog_osucc_le (osucc_NF hσNF)
              omega
            exact ⟨osucc (osucc (a₂ + a₁)), le_of_lt h2, osucc_NF (osucc_NF hσNF),
              Cl_of_NF (osucc_NF (osucc_NF hσNF)), hNg, hstep⟩
        | rel r' v' =>
            obtain ⟨a₁, ha₁le, ha₁NF, ha₁H, ha₁g, Da₁⟩ := P₁
            obtain ⟨a₂, ha₂le, ha₂NF, ha₂H, ha₂g, Da₂⟩ := P₂
            have Da₂n : Zef2TC a₂ e H (ewIter f βψ) c (insert (Semiformula.nrel r' v') Γ) := Da₂
            have hb1 := Nlog_add_le_max_succ a₁ ha₁NF a₂ ha₂NF
            have hgate : Nlog (a₁ + a₂) + 1 ≤ ewIter f α 0 := by
              have h₁ := hsφ 0
              have h₂ := hsψ 0
              omega
            have hstep := stepAtom_Zef2TC ha₁NF ha₂NF hgate
              (Da₁.mono_f hsφ) (Da₂n.mono_f hsψ)
            have hσNF : (a₁ + a₂).NF := ONote.add_nf a₁ a₂
            have hσlt : a₁ + a₂ < collapse α := by
              refine lt_of_le_of_lt ?_ hcollt
              haveI := ha₁NF; haveI := ha₂NF
              haveI := collapse_NF hβφNF; haveI := collapse_NF hβψNF
              haveI := ONote.add_nf a₁ a₂
              haveI := ONote.add_nf (collapse βφ) (collapse βψ)
              rw [ONote.le_def, ONote.repr_add, ONote.repr_add]
              exact add_le_add (ONote.le_def.mp ha₁le) (ONote.le_def.mp ha₂le)
            have h1 := osucc_lt_collapse hσNF hαNF hαpos hσlt
            have hNg : Nlog (osucc (a₁ + a₂)) ≤ ewIter f α 0 := by
              have hs1 := Nlog_osucc_le hσNF
              omega
            exact ⟨osucc (a₁ + a₂), le_of_lt h1, osucc_NF hσNF, Cl_of_NF (osucc_NF hσNF), hNg, hstep⟩
        | nrel r' v' =>
            obtain ⟨a₁, ha₁le, ha₁NF, ha₁H, ha₁g, Da₁⟩ := P₁
            obtain ⟨a₂, ha₂le, ha₂NF, ha₂H, ha₂g, Da₂⟩ := P₂
            have Da₂n : Zef2TC a₂ e H (ewIter f βψ) c (insert (Semiformula.rel r' v') Γ) := Da₂
            have hb1 := Nlog_add_le_max_succ a₂ ha₂NF a₁ ha₁NF
            have hgate : Nlog (a₂ + a₁) + 1 ≤ ewIter f α 0 := by
              have h₁ := hsφ 0
              have h₂ := hsψ 0
              omega
            have hstep := stepAtom_Zef2TC ha₂NF ha₁NF hgate
              (Da₂n.mono_f hsψ) (Da₁.mono_f hsφ)
            have hσNF : (a₂ + a₁).NF := ONote.add_nf a₂ a₁
            have hσlt : a₂ + a₁ < collapse α := by
              refine lt_of_le_of_lt ?_ hcollt'
              haveI := ha₁NF; haveI := ha₂NF
              haveI := collapse_NF hβφNF; haveI := collapse_NF hβψNF
              haveI := ONote.add_nf a₂ a₁
              haveI := ONote.add_nf (collapse βψ) (collapse βφ)
              rw [ONote.le_def, ONote.repr_add, ONote.repr_add]
              exact add_le_add (ONote.le_def.mp ha₂le) (ONote.le_def.mp ha₁le)
            have h1 := osucc_lt_collapse hσNF hαNF hαpos hσlt
            have hNg : Nlog (osucc (a₂ + a₁)) ≤ ewIter f α 0 := by
              have hs1 := Nlog_osucc_le hσNF
              omega
            exact ⟨osucc (a₂ + a₁), le_of_lt h1, osucc_NF hσNF, Cl_of_NF (osucc_NF hσNF), hNg, hstep⟩
        | all ψ =>
            have h : (Semiformula.all ψ : ArithmeticFormula ℕ).complexity = ψ.complexity + 1 := rfl
            have hψc : ψ.complexity < c := by omega
            have hread : ψ.complexity ≤ ewIter f βψ 0 := by
              have h2 : ψ.complexity ≤ f 0 := by omega
              exact le_trans h2 (ewIter_base_le hinfl βψ)
            have hstep := stepAllωTC_bnd (collapse_NF hβφNF) (collapse_NF hβψNF) heNF hψc
              (ewIter_monotone hmono hinfl βφ) (ewIter_infl hinfl βφ)
              (hslack_kit_ge hmono hinfl hlow βφ βψ)
              (ewIter_monotone hmono hinfl βψ) (ewIter_infl hinfl βψ) hread P₁ P₂
            obtain ⟨w, hwle, hwNF, hwH, hwg, Dw⟩ := hstep
            exact ⟨w, le_trans hwle (le_of_lt hcollt), hwNF, hwH,
              le_trans hwg (hcomp 0), Dw.mono_f hcomp⟩
        | exs ψ =>
            have h : (Semiformula.exs ψ : ArithmeticFormula ℕ).complexity = ψ.complexity + 1 := rfl
            have h2 : (∼ψ).complexity = ψ.complexity := Semiformula.complexity_neg ψ
            have hψc : (∼ψ).complexity < c := by omega
            have hread : (∼ψ).complexity ≤ ewIter f βφ 0 := by
              have h3 : (∼ψ).complexity ≤ f 0 := by omega
              exact le_trans h3 (ewIter_base_le hinfl βφ)
            have P₁' : Zef2TCProv (collapse βφ) e H (ewIter f βφ) c (insert (∃⁰ ∼(∼ψ)) Γ) := by
              have hnn : (∼(∼ψ)) = ψ := by simp
              rw [hnn]
              exact P₁
            have hstep := stepAllωTC_bnd (collapse_NF hβψNF) (collapse_NF hβφNF) heNF hψc
              (ewIter_monotone hmono hinfl βψ) (ewIter_infl hinfl βψ)
              (hslack_kit_ge hmono hinfl hlow βψ βφ)
              (ewIter_monotone hmono hinfl βφ) (ewIter_infl hinfl βφ) hread P₂ P₁'
            obtain ⟨w, hwle, hwNF, hwH, hwg, Dw⟩ := hstep
            exact ⟨w, le_trans hwle (le_of_lt hcollt'), hwNF, hwH,
              le_trans hwg (hcomp' 0), Dw.mono_f hcomp'⟩

end GoodsteinPA.E1EmbeddingGrind
