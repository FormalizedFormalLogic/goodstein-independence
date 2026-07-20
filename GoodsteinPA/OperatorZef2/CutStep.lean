module

public import GoodsteinPA.OperatorZef2.Basic
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

namespace GoodsteinPA.OperatorZeh

open LO LO.FirstOrder ONote Ordinal
open GoodsteinPA.OperatorZinfty

/-! ## The reduction and inversion lemmas over `Zef2` — re-proven natively -/

/-- `β < γ → α < α + γ` (NF): the fresh `α + γ` root strictly dominates the `∀`-family base `α`
whenever the `∃`-side ordinal `γ` is positive (which a strict descendant `β < γ` witnesses).  The
`α + γ` analogue of the old `α < osucc (α + γ)`. -/
private theorem lt_add_of_inner_lt {α β γ : ONote} (hαNF : α.NF) (hγNF : γ.NF) (hβ : β < γ) :
    α < α + γ := by
  haveI := hαNF; haveI := hγNF
  refine lt_def.mpr ?_
  rw [repr_add]
  have hγpos : (0 : Ordinal) < γ.repr := lt_of_le_of_lt (by simp) (lt_def.mp hβ)
  simpa using (add_lt_add_iff_left α.repr).mpr hγpos

/-! ### Case lemmas for `cutReduceAllAuxRunning_Zf2`

Each lemma below discharges one constructor case of the induction on `Zef2 γ e H f c Δ` inside
`cutReduceAllAuxRunning_Zf2`.  Splitting the cases into separate declarations keeps each proof
well within the default heartbeat budget (the combined single-declaration proof did not). -/

private theorem cutRun_axL {φ : ArithmeticSemiformula ℕ 1} {α γ e : ONote} {H : ONote → Prop} {f : ℕ → ℕ}
    {c : ℕ} {Γ Δ : Finset (ArithmeticFormula ℕ)} {g : ℕ → ℕ} {ar : ℕ} (hαNF : α.NF) (hg0 : Nlog α ≤ g 0)
    (hαN : Nlog γ ≤ f 0) (r : (ℒₒᵣ).Rel ar) (v : Fin ar → Semiterm ℒₒᵣ ℕ 0)
    (hp : Semiformula.rel r v ∈ Δ) (hn : Semiformula.nrel r v ∈ Δ)
    (hγNF : γ.NF) (_hmono : Monotone f) (_hinfl : ∀ x, x ≤ f x)
    (hsl : ∀ k, f 0 ≤ k → max (g 0) k + 1 ≤ g k) (_hφread : φ.complexity ≤ f 0)
    (_hmem : (∃⁰ ∼φ) ∈ Δ) :
    Zef2Prov (α + γ) e H (g ∘ f) c (Δ.erase (∃⁰ ∼φ) ∪ Γ) := by
  refine Zef2Prov.of (ONote.add_nf α γ) (Cl_of_NF (ONote.add_nf α γ))
    (Nlog_add_le_comp hαNF hγNF hg0 hαN (hsl _ le_rfl)) ?_
  exact Zef2.axL (Nlog_add_le_comp hαNF hγNF hg0 hαN (hsl _ le_rfl)) r v
    (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), hp⟩))
    (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), hn⟩))

private theorem cutRun_wk {φ : ArithmeticSemiformula ℕ 1} {α γ e : ONote} {H : ONote → Prop} {f : ℕ → ℕ}
    {c : ℕ} {Γ Δsub Δsup : Finset (ArithmeticFormula ℕ)} {g : ℕ → ℕ} (hαNF : α.NF) (hg_infl : ∀ x, x ≤ g x)
    (hαN : Nlog γ ≤ f 0) (hsub : Δsub ⊆ Δsup) (D' : Zef2 γ e H f c Δsub)
    (ih : γ.NF → Monotone f → (∀ x, x ≤ f x) → (∀ k, f 0 ≤ k → max (g 0) k + 1 ≤ g k) →
      φ.complexity ≤ f 0 → (∃⁰ ∼φ) ∈ Δsub → Zef2Prov (α + γ) e H (g ∘ f) c (Δsub.erase (∃⁰ ∼φ) ∪ Γ))
    (hγNF : γ.NF) (hmono : Monotone f) (hinfl : ∀ x, x ≤ f x)
    (hsl : ∀ k, f 0 ≤ k → max (g 0) k + 1 ≤ g k) (hφread : φ.complexity ≤ f 0)
    (_hmem : (∃⁰ ∼φ) ∈ Δsup) :
    Zef2Prov (α + γ) e H (g ∘ f) c (Δsup.erase (∃⁰ ∼φ) ∪ Γ) := by
  by_cases hd : (∃⁰ ∼φ) ∈ Δsub
  · exact (ih hγNF hmono hinfl hsl hφread hd).weakening (by
      intro x hx; simp only [Finset.mem_union, Finset.mem_erase] at hx ⊢
      rcases hx with ⟨hne, hxs⟩ | hxΓ
      · exact Or.inl ⟨hne, hsub hxs⟩
      · exact Or.inr hxΓ)
  · exact ⟨γ, Zekd.le_add_left_NF hαNF hγNF, hγNF, Cl_of_NF hγNF,
      le_trans hαN (reslot_exside hg_infl 0),
      (D'.mono_f (reslot_exside hg_infl)).wk (le_trans hαN (reslot_exside hg_infl 0)) (by
        intro x hx; simp only [Finset.mem_union, Finset.mem_erase]
        exact Or.inl ⟨fun e0 => hd (e0 ▸ hx), hsub hx⟩)⟩

private theorem cutRun_weak {φ : ArithmeticSemiformula ℕ 1} {α γ β e : ONote} {H : ONote → Prop} {f : ℕ → ℕ}
    {c : ℕ} {Γ Δsub Δsup : Finset (ArithmeticFormula ℕ)} {g : ℕ → ℕ} (hαNF : α.NF) (hg_infl : ∀ x, x ≤ g x)
    (hβ : β < γ) (hβNF : β.NF) (hsub : Δsub ⊆ Δsup) (D' : Zef2 β e H f c Δsub)
    (ih : β.NF → Monotone f → (∀ x, x ≤ f x) → (∀ k, f 0 ≤ k → max (g 0) k + 1 ≤ g k) →
      φ.complexity ≤ f 0 → (∃⁰ ∼φ) ∈ Δsub → Zef2Prov (α + β) e H (g ∘ f) c (Δsub.erase (∃⁰ ∼φ) ∪ Γ))
    (hγNF : γ.NF) (hmono : Monotone f) (hinfl : ∀ x, x ≤ f x)
    (hsl : ∀ k, f 0 ≤ k → max (g 0) k + 1 ≤ g k) (hφread : φ.complexity ≤ f 0)
    (_hmem : (∃⁰ ∼φ) ∈ Δsup) :
    Zef2Prov (α + γ) e H (g ∘ f) c (Δsup.erase (∃⁰ ∼φ) ∪ Γ) := by
  by_cases hd : (∃⁰ ∼φ) ∈ Δsub
  · exact ((ih hβNF hmono hinfl hsl hφread hd).weakening (by
      intro x hx; simp only [Finset.mem_union, Finset.mem_erase] at hx ⊢
      rcases hx with ⟨hne, hxs⟩ | hxΓ
      · exact Or.inl ⟨hne, hsub hxs⟩
      · exact Or.inr hxΓ)).mono
      (le_of_lt (Zekd.add_lt_add_left_NF hαNF hβNF hγNF hβ))
  · exact ⟨β, le_of_lt (lt_of_lt_of_le hβ (Zekd.le_add_left_NF hαNF hγNF)), hβNF, Cl_of_NF hβNF,
      le_trans (Zef2.gate D') (reslot_exside hg_infl 0),
      (D'.mono_f (reslot_exside hg_infl)).wk (le_trans (Zef2.gate D') (reslot_exside hg_infl 0)) (by
        intro x hx; simp only [Finset.mem_union, Finset.mem_erase]
        exact Or.inl ⟨fun e0 => hd (e0 ▸ hx), hsub hx⟩)⟩

private theorem cutRun_allω {φ : ArithmeticSemiformula ℕ 1} {α γ e : ONote} {H : ONote → Prop} {f : ℕ → ℕ}
    {c : ℕ} {Γ Γ₀ : Finset (ArithmeticFormula ℕ)} {g : ℕ → ℕ} (hαNF : α.NF) (hg0 : Nlog α ≤ g 0)
    (hαN : Nlog γ ≤ f 0) (χ : ArithmeticSemiformula ℕ 1) (β : ℕ → ONote)
    (hβ : ∀ n, β n < γ) (hβNF : ∀ n, (β n).NF)
    (ih : ∀ n, (β n).NF → Monotone (rel1 f n) → (∀ x, x ≤ rel1 f n x) →
      (∀ k, rel1 f n 0 ≤ k → max (g 0) k + 1 ≤ g k) → φ.complexity ≤ rel1 f n 0 →
      (∃⁰ ∼φ) ∈ insert (χ/[nm n]) Γ₀ →
      Zef2Prov (α + β n) e (adjoin H n) (g ∘ rel1 f n) c
        ((insert (χ/[nm n]) Γ₀).erase (∃⁰ ∼φ) ∪ Γ))
    (hγNF : γ.NF) (hmono : Monotone f) (hinfl : ∀ x, x ≤ f x)
    (hsl : ∀ k, f 0 ≤ k → max (g 0) k + 1 ≤ g k) (hφread : φ.complexity ≤ f 0)
    (hmem : (∃⁰ ∼φ) ∈ insert (∀⁰ χ) Γ₀) :
    Zef2Prov (α + γ) e H (g ∘ f) c ((insert (∀⁰ χ) Γ₀).erase (∃⁰ ∼φ) ∪ Γ) := by
  have hhead : (∀⁰ χ) ≠ (∃⁰ ∼φ) := by intro h; simp [UnivQuantifier.all, ExsQuantifier.exs] at h
  have hmem0 : (∃⁰ ∼φ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
  have haddNF : (α + γ).NF := ONote.add_nf α γ
  have ihn : ∀ n, Zef2Prov (α + β n) e (adjoin H n) (g ∘ rel1 f n) c
      (insert (χ/[nm n]) (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) := by
    intro n
    have hread : φ.complexity ≤ (rel1 f n) 0 := by
      simp only [rel1]; exact le_trans hφread (hmono (Nat.zero_le _))
    exact (ih n (hβNF n) (rel1_monotone hmono n) (rel1_infl hinfl n)
      (fun k hk => hsl k (le_trans (by
        simp only [rel1]; exact hmono (Nat.zero_le _)) hk))
      hread (Finset.mem_insert_of_mem hmem0)).weakening (by
        intro x hx
        simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢; tauto)
  refine Zef2Prov.of haddNF (Cl_of_NF haddNF) (Nlog_add_le_comp hαNF hγNF hg0 hαN (hsl _ le_rfl)) ?_
  have hAll : Zef2 (α + γ) e H (g ∘ f) c
      (insert (∀⁰ χ) (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) := by
    exact Zef2.allω (Nlog_add_le_comp hαNF hγNF hg0 hαN (hsl _ le_rfl)) χ (fun n => (ihn n).choose)
      (fun n => lt_of_le_of_lt (ihn n).choose_spec.1
        (Zekd.add_lt_add_left_NF hαNF (hβNF n) hγNF (hβ n)))
      (fun n => (ihn n).choose_spec.2.1) haddNF
      (fun n => Cl_of_NF (ihn n).choose_spec.2.1)
      (fun n => (ihn n).choose_spec.2.2.2.2)
  exact hAll.wk (Nlog_add_le_comp hαNF hγNF hg0 hαN (hsl _ le_rfl)) (by
    intro x hx
    simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢
    rcases hx with rfl | hx
    · exact Or.inl ⟨hhead, Or.inl rfl⟩
    · tauto)

private theorem cutRun_exI {φ : ArithmeticSemiformula ℕ 1} {α γ β e : ONote} {H : ONote → Prop} {f : ℕ → ℕ}
    {c : ℕ} {Γ Γ₀ : Finset (ArithmeticFormula ℕ)} {g : ℕ → ℕ}
    (hαNF : α.NF) (hg_mono : Monotone g) (hg_infl : ∀ x, x ≤ g x) (hg0 : Nlog α ≤ g 0)
    (fam : ∀ n (H' : ONote → Prop), Zef2 α e H' (rel1 g n) c (insert (φ/[nm n]) Γ))
    (hαN : Nlog γ ≤ f 0) (hφc : φ.complexity < c) (χ : ArithmeticSemiformula ℕ 1) (n : ℕ) (hβ : β < γ)
    (hβNF : β.NF) (hbound : n ≤ f 0) (dχ : Zef2 β e H f c (insert (χ/[nm n]) Γ₀))
    (ih : β.NF → Monotone f → (∀ x, x ≤ f x) → (∀ k, f 0 ≤ k → max (g 0) k + 1 ≤ g k) →
      φ.complexity ≤ f 0 → (∃⁰ ∼φ) ∈ insert (χ/[nm n]) Γ₀ →
      Zef2Prov (α + β) e H (g ∘ f) c ((insert (χ/[nm n]) Γ₀).erase (∃⁰ ∼φ) ∪ Γ))
    (hγNF : γ.NF) (hmono : Monotone f) (hinfl : ∀ x, x ≤ f x)
    (hsl : ∀ k, f 0 ≤ k → max (g 0) k + 1 ≤ g k) (hφread : φ.complexity ≤ f 0)
    (hmem : (∃⁰ ∼φ) ∈ insert (∃⁰ χ) Γ₀) :
    Zef2Prov (α + γ) e H (g ∘ f) c ((insert (∃⁰ χ) Γ₀).erase (∃⁰ ∼φ) ∪ Γ) := by
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
    have famn : Zef2 α e H (g ∘ f) c (insert (φ/[nm n]) (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) :=
      ((fam n H).mono_f (reslot_family hg_mono hinfl hmono hbound)).wk hg0comp (by
        intro x hx; simp only [Finset.mem_insert, Finset.mem_union] at hx ⊢; tauto)
    have hαlt : α < α + γ := lt_add_of_inner_lt hαNF hγNF hβ
    by_cases hd : (∃⁰ ∼φ) ∈ Γ₀
    · obtain ⟨a, hale, haNF, haH, hag, Da⟩ := ih hβNF hmono hinfl hsl hφread
        (Finset.mem_insert_of_mem hd)
      have Da' : Zef2 a e H (g ∘ f) c
          (insert (∼(φ/[nm n])) (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) :=
        Da.wk hag (by
          intro x hx
          simp only [hNeg, Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢; tauto)
      refine Zef2Prov.of haddNF (Cl_of_NF haddNF) (Nlog_add_le_comp hαNF hγNF hg0 hαN (hsl _ le_rfl)) ?_
      exact Zef2.cut (Nlog_add_le_comp hαNF hγNF hg0 hαN (hsl _ le_rfl)) (φ/[nm n]) hcompl hcutRead hαlt
        (lt_of_le_of_lt hale (Zekd.add_lt_add_left_NF hαNF hβNF hγNF hβ))
        hαNF haNF haddNF (Cl_of_NF hαNF) haH famn Da'
    · have Dβ' : Zef2 β e H (g ∘ f) c
          (insert (∼(φ/[nm n])) (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) :=
        (dχ.mono_f (reslot_exside hg_infl)).wk
          (le_trans (Zef2.gate dχ) (reslot_exside hg_infl 0)) (by
          intro x hx
          simp only [hNeg, Finset.mem_insert] at hx
          simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_erase]
          rcases hx with rfl | hxΓ₀
          · exact Or.inl rfl
          · exact Or.inr (Or.inl ⟨fun e0 => hd (e0 ▸ hxΓ₀), hxΓ₀⟩))
      refine Zef2Prov.of haddNF (Cl_of_NF haddNF) (Nlog_add_le_comp hαNF hγNF hg0 hαN (hsl _ le_rfl)) ?_
      exact Zef2.cut (Nlog_add_le_comp hαNF hγNF hg0 hαN (hsl _ le_rfl)) (φ/[nm n]) hcompl hcutRead hαlt
        (lt_of_lt_of_le hβ (Zekd.le_add_left_NF hαNF hγNF))
        hαNF hβNF haddNF (Cl_of_NF hαNF) (Cl_of_NF hβNF) famn Dβ'
  · have hmem0 : (∃⁰ ∼φ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhd e.symm
    obtain ⟨a, hale, haNF, haH, hag, Da⟩ := ih hβNF hmono hinfl hsl hφread
      (Finset.mem_insert_of_mem hmem0)
    have Da' : Zef2 a e H (g ∘ f) c (insert (χ/[nm n]) (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) :=
      Da.wk hag (by
        intro x hx
        simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢; tauto)
    refine Zef2Prov.of haddNF (Cl_of_NF haddNF) (Nlog_add_le_comp hαNF hγNF hg0 hαN (hsl _ le_rfl)) ?_
    have hbound' : n ≤ (g ∘ f) 0 := le_trans hbound (hg_infl (f 0))
    exact Zef2.exI (Nlog_add_le_comp hαNF hγNF hg0 hαN (hsl _ le_rfl)) χ n
      (lt_of_le_of_lt hale (Zekd.add_lt_add_left_NF hαNF hβNF hγNF hβ))
      haNF haddNF haH hbound' Da'
    |>.wk (Nlog_add_le_comp hαNF hγNF hg0 hαN (hsl _ le_rfl)) (by
      intro x hx
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢
      rcases hx with rfl | hx
      · exact Or.inl ⟨hhd, Or.inl rfl⟩
      · tauto)

private theorem cutRun_cut {φ : ArithmeticSemiformula ℕ 1} {α γ βφ βψ e : ONote} {H : ONote → Prop}
    {f : ℕ → ℕ} {c : ℕ} {Γ Γ₀ : Finset (ArithmeticFormula ℕ)} {g : ℕ → ℕ}
    (hαNF : α.NF) (hg_infl : ∀ x, x ≤ g x) (hg0 : Nlog α ≤ g 0)
    (hαN : Nlog γ ≤ f 0) (χ : ArithmeticFormula ℕ) (hχc : χ.complexity < c)
    (hcutRead' : χ.complexity ≤ f 0) (hβφ : βφ < γ) (hβψ : βψ < γ) (hβφNF : βφ.NF) (hβψNF : βψ.NF)
    (ih₁ : βφ.NF → Monotone f → (∀ x, x ≤ f x) → (∀ k, f 0 ≤ k → max (g 0) k + 1 ≤ g k) →
      φ.complexity ≤ f 0 → (∃⁰ ∼φ) ∈ insert χ Γ₀ →
      Zef2Prov (α + βφ) e H (g ∘ f) c ((insert χ Γ₀).erase (∃⁰ ∼φ) ∪ Γ))
    (ih₂ : βψ.NF → Monotone f → (∀ x, x ≤ f x) → (∀ k, f 0 ≤ k → max (g 0) k + 1 ≤ g k) →
      φ.complexity ≤ f 0 → (∃⁰ ∼φ) ∈ insert (∼χ) Γ₀ →
      Zef2Prov (α + βψ) e H (g ∘ f) c ((insert (∼χ) Γ₀).erase (∃⁰ ∼φ) ∪ Γ))
    (hγNF : γ.NF) (hmono : Monotone f) (hinfl : ∀ x, x ≤ f x)
    (hsl : ∀ k, f 0 ≤ k → max (g 0) k + 1 ≤ g k) (hφread : φ.complexity ≤ f 0)
    (hmem : (∃⁰ ∼φ) ∈ Γ₀) :
    Zef2Prov (α + γ) e H (g ∘ f) c (Γ₀.erase (∃⁰ ∼φ) ∪ Γ) := by
  obtain ⟨a₁, ha₁le, ha₁NF, ha₁H, ha₁g, D₁⟩ := ih₁ hβφNF hmono hinfl hsl hφread
    (Finset.mem_insert_of_mem hmem)
  obtain ⟨a₂, ha₂le, ha₂NF, ha₂H, ha₂g, D₂⟩ := ih₂ hβψNF hmono hinfl hsl hφread
    (Finset.mem_insert_of_mem hmem)
  have haddNF : (α + γ).NF := ONote.add_nf α γ
  have D₁' : Zef2 a₁ e H (g ∘ f) c (insert χ (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) :=
    D₁.wk ha₁g (by
      intro x hx
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢; tauto)
  have D₂' : Zef2 a₂ e H (g ∘ f) c (insert (∼χ) (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) :=
    D₂.wk ha₂g (by
      intro x hx
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢; tauto)
  refine Zef2Prov.of haddNF (Cl_of_NF haddNF) (Nlog_add_le_comp hαNF hγNF hg0 hαN (hsl _ le_rfl)) ?_
  exact Zef2.cut (Nlog_add_le_comp hαNF hγNF hg0 hαN (hsl _ le_rfl)) χ hχc
    (le_trans hcutRead' (hg_infl (f 0)))
    (lt_of_le_of_lt ha₁le (Zekd.add_lt_add_left_NF hαNF hβφNF hγNF hβφ))
    (lt_of_le_of_lt ha₂le (Zekd.add_lt_add_left_NF hαNF hβψNF hγNF hβψ))
    ha₁NF ha₂NF haddNF ha₁H ha₂H D₁' D₂'

/-- **The running-family cut-reduction over `Zef2`.**  Port of
`cutReduceAllAuxRunning_Zf` with the `Nlog`/cut-read gate re-threaded at every rebuilt node.

The reduction's fresh root is `α + γ`: no successor `+1` is taken, unlike the
old `osucc (α + γ)` form.  The two additions to the signature — `hg_base : ∀ k, g 0 + k ≤ g k`
(a per-step growth floor on the `∀`-side slot) and `φ.complexity ≤ f 0` (the fresh cut-read) —
close the fresh node's gates: `Nlog (α + γ) ≤ g (f 0)` via `Nlog_add_le_comp` and
`φ.complexity ≤ (g ∘ f) 0` via `hg_infl`.  Premises land strictly below `α + γ` by the
covariance of the reduction.

- [EW12, Lemma 25]
-/
theorem cutReduceAllAuxRunning_Zf2 {φ : ArithmeticSemiformula ℕ 1} {c : ℕ} {α e : ONote}
    {Γ : Finset (ArithmeticFormula ℕ)} {g : ℕ → ℕ} (hφc : φ.complexity < c) (hαNF : α.NF) (heNF : e.NF)
    (hg_mono : Monotone g) (hg_infl : ∀ x, x ≤ g x)
    (fam : ∀ n (H' : ONote → Prop), Zef2 α e H' (rel1 g n) c (insert (φ/[nm n]) Γ))
    {γ : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {Δ : Finset (ArithmeticFormula ℕ)}
    (D : Zef2 γ e H f c Δ) (hγNF : γ.NF)
    (hmono : Monotone f) (hinfl : ∀ x, x ≤ f x) (hsl : ∀ k, f 0 ≤ k → max (g 0) k + 1 ≤ g k)
    (hφread : φ.complexity ≤ f 0) (hmem : (∃⁰ ∼φ) ∈ Δ) :
    Zef2Prov (α + γ) e H (g ∘ f) c (Δ.erase (∃⁰ ∼φ) ∪ Γ) := by
  have hg0 : Nlog α ≤ g 0 := by
    have h := Zef2.gate (fam 0 (fun _ => True)); simpa [rel1] using h
  induction D with
  | @axL γ e H f c Δ ar hαN r v hp hn =>
      exact cutRun_axL hαNF hg0 hαN r v hp hn hγNF hmono hinfl hsl hφread hmem
  | @wk γ e H f c Δsub Δsup hαN hsub D' ih =>
      exact cutRun_wk hαNF hg_infl hαN hsub D' (ih hφc heNF fam) hγNF hmono hinfl hsl hφread hmem
  | @weak γ β e H f c Δsub Δsup hαN hβ hβNF _hγNF' _hβH hsub D' ih =>
      exact cutRun_weak hαNF hg_infl hβ hβNF hsub D' (ih hφc heNF fam) hγNF hmono hinfl hsl hφread hmem
  | @allω γ e H f c Γ₀ hαN χ β hβ hβNF _hγNF' _hβH _dd ih =>
      exact cutRun_allω hαNF hg0 hαN χ β hβ hβNF (fun n => ih n hφc heNF fam) hγNF hmono hinfl hsl hφread hmem
  | @exI γ β e H f c Γ₀ hαN χ n hβ hβNF _hγNF' _hβH hbound dχ ih =>
      exact cutRun_exI hαNF hg_mono hg_infl hg0 fam hαN hφc χ n hβ hβNF hbound dχ (ih hφc heNF fam)
        hγNF hmono hinfl hsl hφread hmem
  | @cut γ βφ βψ e H f c Γ₀ hαN χ hχc hcutRead' hβφ hβψ hβφNF hβψNF _hγNF' _hβφH _hβψH _d₁ _d₂ ih₁ ih₂ =>
      exact cutRun_cut hαNF hg_infl hg0 hαN χ hχc hcutRead' hβφ hβψ hβφNF hβψNF
        (ih₁ hφc heNF fam) (ih₂ hφc heNF fam) hγNF hmono hinfl hsl hφread hmem

/-- `f x ≤ rel1 f n₀ x` for monotone `f`. -/
private theorem f_le_rel1_2 {f : ℕ → ℕ} (hf : Monotone f) (n₀ : ℕ) :
    ∀ x, f x ≤ rel1 f n₀ x := fun x => hf (le_max_right n₀ x)

/-- Transport a gate `Nlog α ≤ f 0` to the relativized slot `rel1 f n₀`. -/
private theorem gate_rel1 {f : ℕ → ℕ} (hmono : Monotone f) {α : ONote} (n₀ : ℕ)
    (h : Nlog α ≤ f 0) : Nlog α ≤ rel1 f n₀ 0 := by
  refine le_trans h ?_
  simp only [rel1]
  exact hmono (Nat.zero_le _)

/-- **`allInv_Zef2`** — ∀-inversion over `Zef2` (port of `allInv_Zef`).  Ordinals are unchanged by
inversion, so every rebuilt node's gate re-threads from its input gate through the relativized
slot `rel1 f n₀` (`gate_rel1`, `f` monotone). -/
theorem allInv_Zef2 {φ₀ : ArithmeticSemiformula ℕ 1} (n₀ : ℕ) {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ}
    {c : ℕ} {Γ : Finset (ArithmeticFormula ℕ)} (dd : Zef2 α e H f c Γ) (hmono : Monotone f)
    (hmem : (∀⁰ φ₀) ∈ Γ) :
    Zef2 α e (adjoin H n₀) (rel1 f n₀) c (insert (φ₀/[nm n₀]) (Γ.erase (∀⁰ φ₀))) := by
  induction dd with
  | @axL α e H f c Γ ar hαN r v hp hn =>
      refine Zef2.axL (gate_rel1 hmono n₀ hαN) r v ?_ ?_ <;>
        exact Finset.mem_insert_of_mem
          (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), by assumption⟩)
  | @wk α e H f c Δ Γ hαN hsub dd ih =>
      by_cases hh : (∀⁰ φ₀) ∈ Δ
      · exact Zef2.wk (gate_rel1 hmono n₀ hαN)
          (Finset.insert_subset_insert _ (Finset.erase_subset_erase _ hsub)) (ih hmono hh)
      · refine Zef2.wk (gate_rel1 hmono n₀ hαN) ?_ (dd.mono_Hf (f_le_rel1_2 hmono n₀))
        intro x hx
        exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨fun e => hh (e ▸ hx), hsub hx⟩)
  | @weak α β e H f c Δ Γ hαN hβ hβNF hαNF hβH hsub dd ih =>
      by_cases hh : (∀⁰ φ₀) ∈ Δ
      · exact Zef2.weak (gate_rel1 hmono n₀ hαN) hβ hβNF hαNF (Cl_of_NF hβNF)
          (Finset.insert_subset_insert _ (Finset.erase_subset_erase _ hsub)) (ih hmono hh)
      · refine Zef2.weak (gate_rel1 hmono n₀ hαN) hβ hβNF hαNF (Cl_of_NF hβNF) ?_
          (dd.mono_Hf (f_le_rel1_2 hmono n₀))
        intro x hx
        exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨fun e => hh (e ▸ hx), hsub hx⟩)
  | @allω α e H f c Γ₀ hαN χ β hβ hβNF hαNF hβH dd ih =>
      by_cases hhd : (∀⁰ χ) = (∀⁰ φ₀)
      · obtain rfl := (Semiformula.all_inj _ _).mp hhd
        rw [Finset.erase_insert_eq_erase]
        by_cases hh : (∀⁰ χ) ∈ Γ₀
        · have h := ih n₀ (rel1_monotone hmono n₀) (Finset.mem_insert_of_mem hh)
          have h2 : Zef2 (β n₀) e (adjoin H n₀) (rel1 f n₀) c
              (insert (χ/[nm n₀]) ((insert (χ/[nm n₀]) Γ₀).erase (∀⁰ χ))) :=
            h.mono_Hf (fun x => le_of_eq (by simp only [rel1]; congr 1; omega))
          exact Zef2.weak (gate_rel1 hmono n₀ hαN) (hβ n₀) (hβNF n₀) hαNF (Cl_of_NF (hβNF n₀))
            (princAllSub (∀⁰ χ) _ Γ₀) h2
        · rw [Finset.erase_eq_of_notMem hh]
          exact Zef2.weak (gate_rel1 hmono n₀ hαN) (hβ n₀) (hβNF n₀) hαNF (Cl_of_NF (hβNF n₀))
            (Finset.Subset.refl _) (dd n₀)
      · have hmem0 : (∀⁰ φ₀) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhd e.symm
        have key : ∀ n, Zef2 (β n) e (adjoin (adjoin H n₀) n) (rel1 (rel1 f n₀) n) c
            (insert (χ/[nm n]) (insert (φ₀/[nm n₀]) (Γ₀.erase (∀⁰ φ₀)))) := by
          intro n
          have h := ih n (rel1_monotone hmono n) (Finset.mem_insert_of_mem hmem0)
          have hg : Nlog (β n) ≤ rel1 (rel1 f n₀) n 0 := by
            have hgn := Zef2.gate (dd n)
            simp only [rel1] at hgn ⊢
            exact le_trans hgn (hmono (le_max_right n₀ (max n 0)))
          exact Zef2.wk hg (inv1Push (∀⁰ φ₀) _ (χ/[nm n]) Γ₀)
            (h.mono_Hf (fun x => le_of_eq (by simp only [rel1]; congr 1; omega)))
        refine Zef2.wk (gate_rel1 hmono n₀ hαN) (inv1Pull (∀⁰ φ₀) _ hhd Γ₀) ?_
        exact Zef2.allω (gate_rel1 hmono n₀ hαN) χ β hβ hβNF hαNF
          (fun n => Cl_of_NF (hβNF n)) key
  | @exI α β e H f c Γ₀ hαN χ n hβ hβNF hαNF hβH hbound dd ih =>
      have hhead : (∃⁰ χ) ≠ (∀⁰ φ₀) := by intro h; simp [ExsQuantifier.exs, UnivQuantifier.all] at h
      have hmem0 : (∀⁰ φ₀) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
      have P := Zef2.wk (Zef2.gate (ih hmono (Finset.mem_insert_of_mem hmem0)))
        (inv1Push (∀⁰ φ₀) _ (χ/[nm n]) Γ₀) (ih hmono (Finset.mem_insert_of_mem hmem0))
      refine Zef2.wk (gate_rel1 hmono n₀ hαN) (inv1Pull (∀⁰ φ₀) _ hhead Γ₀) ?_
      exact Zef2.exI (gate_rel1 hmono n₀ hαN) χ n hβ hβNF hαNF (Cl_of_NF hβNF)
        (le_trans hbound (by simp only [rel1]; exact hmono (Nat.zero_le _))) P
  | @cut α βφ βψ e H f c Γ₀ hαN χ hcompl hcutRead hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH d₁ d₂ ih₁ ih₂ =>
      have P₁ := Zef2.wk (Zef2.gate (ih₁ hmono (Finset.mem_insert_of_mem hmem)))
        (inv1Push (∀⁰ φ₀) _ χ Γ₀) (ih₁ hmono (Finset.mem_insert_of_mem hmem))
      have P₂ := Zef2.wk (Zef2.gate (ih₂ hmono (Finset.mem_insert_of_mem hmem)))
        (inv1Push (∀⁰ φ₀) _ (∼χ) Γ₀) (ih₂ hmono (Finset.mem_insert_of_mem hmem))
      exact Zef2.cut (gate_rel1 hmono n₀ hαN) χ hcompl (le_trans hcutRead
        (by simp only [rel1]; exact hmono (Nat.zero_le _))) hβφ hβψ hβφNF hβψNF hαNF
        (Cl_of_NF hβφNF) (Cl_of_NF hβψNF) P₁ P₂

variable {E : ONote} {H : ONote → Prop} {c : ℕ} {Γ : Finset (ArithmeticFormula ℕ)} {χ : ArithmeticSemiformula ℕ 1}
  {f g : ℕ → ℕ}

/-- **`stepAllω_Zf2`** — the principal ∀/∃ cut-reduction step over `Zef2` — invert the
∀-side via `allInv_Zef2`, feed `cutReduceAllAuxRunning_Zf2`, with the `hg_base` floor and
`hχRead : χ.complexity ≤ f 0` cut-read on the signature. -/
theorem stepAllω_Zf2 {βφ βψ : ONote}
    (hENF : E.NF) (hχc : χ.complexity < c)
    (hg_mono : Monotone g) (hg_infl : ∀ x, x ≤ g x)
    (hg_slack : ∀ k, f 0 ≤ k → max (g 0) k + 1 ≤ g k)
    (hf_mono : Monotone f) (hf_infl : ∀ x, x ≤ f x) (hχRead : χ.complexity ≤ f 0)
    (D₁ : Zef2Prov (expTower βφ) E H g c (insert (∀⁰ χ) Γ))
    (D₂ : Zef2Prov (expTower βψ) E H f c (insert (∃⁰ ∼χ) Γ)) :
    ∃ δ : ONote, δ.NF ∧ Cl H δ ∧ Zef2Prov δ E H (g ∘ f) c Γ := by
  obtain ⟨α₁, _, hNF₁, _, _, d₁⟩ := D₁
  obtain ⟨γ₁, _, hNF₂, _, _, d₂⟩ := D₂
  have fam : ∀ n (H' : ONote → Prop), Zef2 α₁ E H' (rel1 g n) c (insert (χ/[nm n]) Γ) := by
    intro n H'
    have hinv := allInv_Zef2 n d₁ hg_mono (Finset.mem_insert_self _ _)
    exact (hinv.wk (Zef2.gate hinv)
      (Finset.insert_subset_insert _ (Finset.erase_insert_subset _ _))).change_H
  have hred := cutReduceAllAuxRunning_Zf2 hχc hNF₁ hENF hg_mono hg_infl fam
    d₂ hNF₂ hf_mono hf_infl hg_slack hχRead (Finset.mem_insert_self _ _)
  refine ⟨α₁ + γ₁, ONote.add_nf α₁ γ₁, Cl_of_NF (ONote.add_nf α₁ γ₁), ?_⟩
  exact hred.weakening
    (Finset.union_subset (Finset.erase_insert_subset _ _) (Finset.Subset.refl Γ))

/-- **`stepAllω_Zf2_bnd`** — the bound-EXPOSING variant of `stepAllω_Zf2`.  Same principal ∀/∃
cut-reduction, but the output witness ordinal is bounded by `P₁ + P₂` (the sum of the two premises'
ordinals), which the cut-elimination pass needs to place the eliminated cut strictly under
`collapse α` (via `collapse_add_lt`).  The generic `stepAllω_Zf2` hides `δ`; here we keep the two
`≤`-bounds from the `Zef2Prov` witnesses and add-monotone them (`repr_add` + `add_le_add`). -/
theorem stepAllω_Zf2_bnd {P₁ P₂ : ONote}
    (hP₁ : P₁.NF) (hP₂ : P₂.NF)
    (hENF : E.NF) (hχc : χ.complexity < c)
    (hg_mono : Monotone g) (hg_infl : ∀ x, x ≤ g x)
    (hg_slack : ∀ k, f 0 ≤ k → max (g 0) k + 1 ≤ g k)
    (hf_mono : Monotone f) (hf_infl : ∀ x, x ≤ f x) (hχRead : χ.complexity ≤ f 0)
    (D₁ : Zef2Prov P₁ E H g c (insert (∀⁰ χ) Γ))
    (D₂ : Zef2Prov P₂ E H f c (insert (∃⁰ ∼χ) Γ)) :
    Zef2Prov (P₁ + P₂) E H (g ∘ f) c Γ := by
  obtain ⟨α₁, hα₁le, hNF₁, _, _, d₁⟩ := D₁
  obtain ⟨γ₁, hγ₁le, hNF₂, _, _, d₂⟩ := D₂
  have fam : ∀ n (H' : ONote → Prop), Zef2 α₁ E H' (rel1 g n) c (insert (χ/[nm n]) Γ) := by
    intro n H'
    have hinv := allInv_Zef2 n d₁ hg_mono (Finset.mem_insert_self _ _)
    exact (hinv.wk (Zef2.gate hinv)
      (Finset.insert_subset_insert _ (Finset.erase_insert_subset _ _))).change_H
  have hred := cutReduceAllAuxRunning_Zf2 hχc hNF₁ hENF hg_mono hg_infl fam
    d₂ hNF₂ hf_mono hf_infl hg_slack hχRead (Finset.mem_insert_self _ _)
  have hbnd : α₁ + γ₁ ≤ P₁ + P₂ := by
    haveI := hNF₁; haveI := hNF₂; haveI := hP₁; haveI := hP₂
    rw [le_def, repr_add, repr_add]
    exact add_le_add (le_def.mp hα₁le) (le_def.mp hγ₁le)
  exact ((hred.weakening
    (Finset.union_subset (Finset.erase_insert_subset _ _) (Finset.Subset.refl Γ))).mono hbnd)

/-! ## Inert-shape erasure and the atomic-cut splice

`Zef2` has NO `⊤/⊥/⋏/⋎` rules, so formulas of those shapes are never principal — they can be
erased from any context (`Zef2.erase_inert`).  This closes the top-rank cut for the four inert
cut-formula shapes.  The two atomic shapes (`rel`/`nrel`) are closed by the flagged atom-cut
lemma (`atomCutRun_Zf2`, the axL-pair surgery — a fixed-premise mirror of the running
reduction).  The two quantifier shapes are `stepAllω_Zf2_bnd`. -/

/-- A formula shape never principal in any `Zef2` rule. -/
def InertForm (A : ArithmeticFormula ℕ) : Prop :=
  (∀ (ar : ℕ) (r : (ℒₒᵣ).Rel ar) (v : Fin ar → Semiterm ℒₒᵣ ℕ 0),
      A ≠ Semiformula.rel r v ∧ A ≠ Semiformula.nrel r v) ∧
  ∀ (χ : ArithmeticSemiformula ℕ 1), A ≠ (∀⁰ χ) ∧ A ≠ (∃⁰ χ)

theorem inertForm_verum : InertForm ⊤ :=
  ⟨fun _ _ _ => ⟨nofun, nofun⟩, fun _ => ⟨nofun, nofun⟩⟩

theorem inertForm_falsum : InertForm ⊥ :=
  ⟨fun _ _ _ => ⟨nofun, nofun⟩, fun _ => ⟨nofun, nofun⟩⟩

theorem inertForm_and (φ₁ φ₂ : ArithmeticFormula ℕ) : InertForm (φ₁ ⋏ φ₂) :=
  ⟨fun _ _ _ => ⟨nofun, nofun⟩, fun _ => ⟨nofun, nofun⟩⟩

theorem inertForm_or (φ₁ φ₂ : ArithmeticFormula ℕ) : InertForm (φ₁ ⋎ φ₂) :=
  ⟨fun _ _ _ => ⟨nofun, nofun⟩, fun _ => ⟨nofun, nofun⟩⟩

/-- **Inert erasure**: a formula of inert shape can be erased from any `Zef2` context (it is
never principal, so every rule commutes; instance formulas `χ/[nm n]` that happen to EQUAL the
inert formula are restored by plain `wk`).  All gates ride unchanged (same `α`, same `f`). -/
theorem Zef2.erase_inert {A : ArithmeticFormula ℕ} (hA : InertForm A)
    {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Finset (ArithmeticFormula ℕ)}
    (dd : Zef2 α e H f c Γ) : Zef2 α e H f c (Γ.erase A) := by
  induction dd with
  | @axL α e H f c Γ ar hαN r v hp hn =>
      exact Zef2.axL hαN r v
        (Finset.mem_erase.mpr ⟨Ne.symm (hA.1 _ r v).1, hp⟩)
        (Finset.mem_erase.mpr ⟨Ne.symm (hA.1 _ r v).2, hn⟩)
  | @wk α e H f c Δ Γ hαN hsub _ ih =>
      exact Zef2.wk hαN (Finset.erase_subset_erase A hsub) ih
  | @weak α β e H f c Δ Γ hαN hβ hβNF hαNF hβH hsub _ ih =>
      exact Zef2.weak hαN hβ hβNF hαNF hβH (Finset.erase_subset_erase A hsub) ih
  | @allω α e H f c Γ₀ hαN χ β hβ hβNF hαNF hβH dd ih =>
      have hne : (∀⁰ χ) ≠ A := Ne.symm (hA.2 χ).1
      have hgoal : (insert (∀⁰ χ) Γ₀).erase A = insert (∀⁰ χ) (Γ₀.erase A) := by
        ext x
        simp only [Finset.mem_erase, Finset.mem_insert]
        constructor
        · rintro ⟨hxA, rfl | hx⟩
          · exact Or.inl rfl
          · exact Or.inr ⟨hxA, hx⟩
        · rintro (rfl | ⟨hxA, hx⟩)
          · exact ⟨hne, Or.inl rfl⟩
          · exact ⟨hxA, Or.inr hx⟩
      rw [hgoal]
      refine Zef2.allω hαN χ β hβ hβNF hαNF hβH (fun n => ?_)
      exact (ih n).wk (Zef2.gate (ih n)) (by
        intro x hx
        simp only [Finset.mem_erase, Finset.mem_insert] at hx ⊢; tauto)
  | @exI α β e H f c Γ₀ hαN χ n hβ hβNF hαNF hβH hbound _ ih =>
      have hne : (∃⁰ χ) ≠ A := Ne.symm (hA.2 χ).2
      have hgoal : (insert (∃⁰ χ) Γ₀).erase A = insert (∃⁰ χ) (Γ₀.erase A) := by
        ext x
        simp only [Finset.mem_erase, Finset.mem_insert]
        constructor
        · rintro ⟨hxA, rfl | hx⟩
          · exact Or.inl rfl
          · exact Or.inr ⟨hxA, hx⟩
        · rintro (rfl | ⟨hxA, hx⟩)
          · exact ⟨hne, Or.inl rfl⟩
          · exact ⟨hxA, Or.inr hx⟩
      rw [hgoal]
      refine Zef2.exI hαN χ n hβ hβNF hαNF hβH hbound ?_
      exact ih.wk (Zef2.gate ih) (by
        intro x hx
        simp only [Finset.mem_erase, Finset.mem_insert] at hx ⊢; tauto)
  | @cut α βφ βψ e H f c Γ₀ hαN χ hcompl hcutRead hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH _ _ ih₁ ih₂ =>
      refine Zef2.cut hαN χ hcompl hcutRead hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH
        (ih₁.wk (Zef2.gate ih₁) ?_) (ih₂.wk (Zef2.gate ih₂) ?_) <;>
        · intro x hx
          simp only [Finset.mem_erase, Finset.mem_insert] at hx ⊢; tauto

/-! ### Case lemmas for `atomCutRun_Zf2`

Each lemma below discharges one constructor case of the induction on `Zef2 γ e H f c Δ` inside
`atomCutRun_Zf2`.  Splitting the cases into separate declarations keeps each proof well within
the default heartbeat budget (the combined single-declaration proof did not). -/

private theorem atomRun_axL {ar : ℕ} {rr : (ℒₒᵣ).Rel ar} {vv : Fin ar → Semiterm ℒₒᵣ ℕ 0}
    {βψ γ e : ONote} {H H₂ : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ Δ : Finset (ArithmeticFormula ℕ)}
    {g : ℕ → ℕ} {ar' : ℕ} (hβψNF : βψ.NF) (hg_mono : Monotone g) (hg_infl : ∀ x, x ≤ g x)
    (hg0 : Nlog βψ ≤ g 0) (hαN : Nlog γ ≤ f 0) (r : (ℒₒᵣ).Rel ar') (v : Fin ar' → Semiterm ℒₒᵣ ℕ 0)
    (hp : Semiformula.rel r v ∈ Δ) (hn : Semiformula.nrel r v ∈ Δ)
    (D₂ : Zef2 βψ e H₂ g c (insert (Semiformula.nrel rr vv) Γ))
    (hγNF : γ.NF) (_hmono : Monotone f) (hinfl : ∀ x, x ≤ f x)
    (_hsl : ∀ k, f 0 ≤ k → max (g 0) k + 1 ≤ g k) :
    Zef2Prov (βψ + γ) e H (g ∘ f) c (Δ.erase (Semiformula.rel rr vv) ∪ Γ) := by
  by_cases hsplice : Semiformula.rel r v = Semiformula.rel rr vv
  · have hnrel : Semiformula.nrel r v = Semiformula.nrel rr vv := by
      have := congrArg (∼·) hsplice
      simpa using this
    have hnmem : Semiformula.nrel rr vv ∈ Δ.erase (Semiformula.rel rr vv) ∪ Γ :=
      Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨by simp, hnrel ▸ hn⟩)
    have hgate : Nlog βψ ≤ (g ∘ f) 0 := le_trans hg0 (hg_mono (Nat.zero_le _))
    refine ⟨βψ, Zekd.le_add_right_NF hβψNF hγNF, hβψNF, Cl_of_NF hβψNF, hgate, ?_⟩
    exact ((D₂.change_H (H' := H)).mono_f (fun x => hg_mono (hinfl x))).wk hgate (by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hxΓ
      · exact hnmem
      · exact Finset.mem_union_right _ hxΓ)
  · have hgate : Nlog γ ≤ (g ∘ f) 0 := le_trans hαN (hg_infl (f 0))
    refine ⟨γ, Zekd.le_add_left_NF hβψNF hγNF, hγNF, Cl_of_NF hγNF, hgate, ?_⟩
    exact Zef2.axL hgate r v
      (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hsplice, hp⟩))
      (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨by simp, hn⟩))

private theorem atomRun_wk {ar : ℕ} {rr : (ℒₒᵣ).Rel ar} {vv : Fin ar → Semiterm ℒₒᵣ ℕ 0}
    {βψ γ e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ Δsub Δsup : Finset (ArithmeticFormula ℕ)}
    {g : ℕ → ℕ} (hsub : Δsub ⊆ Δsup)
    (ih : γ.NF → Monotone f → (∀ x, x ≤ f x) → (∀ k, f 0 ≤ k → max (g 0) k + 1 ≤ g k) →
      Zef2Prov (βψ + γ) e H (g ∘ f) c (Δsub.erase (Semiformula.rel rr vv) ∪ Γ))
    (hγNF : γ.NF) (hmono : Monotone f) (hinfl : ∀ x, x ≤ f x)
    (hsl : ∀ k, f 0 ≤ k → max (g 0) k + 1 ≤ g k) :
    Zef2Prov (βψ + γ) e H (g ∘ f) c (Δsup.erase (Semiformula.rel rr vv) ∪ Γ) := by
  exact (ih hγNF hmono hinfl hsl).weakening (by
    intro x hx; simp only [Finset.mem_union, Finset.mem_erase] at hx ⊢
    rcases hx with ⟨hne, hxs⟩ | hxΓ
    · exact Or.inl ⟨hne, hsub hxs⟩
    · exact Or.inr hxΓ)

private theorem atomRun_weak {ar : ℕ} {rr : (ℒₒᵣ).Rel ar} {vv : Fin ar → Semiterm ℒₒᵣ ℕ 0}
    {βψ γ β e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ}
    {Γ Δsub Δsup : Finset (ArithmeticFormula ℕ)} {g : ℕ → ℕ} (hβψNF : βψ.NF) (hβ : β < γ) (hβNF : β.NF)
    (hsub : Δsub ⊆ Δsup)
    (ih : β.NF → Monotone f → (∀ x, x ≤ f x) → (∀ k, f 0 ≤ k → max (g 0) k + 1 ≤ g k) →
      Zef2Prov (βψ + β) e H (g ∘ f) c (Δsub.erase (Semiformula.rel rr vv) ∪ Γ))
    (hγNF : γ.NF) (hmono : Monotone f) (hinfl : ∀ x, x ≤ f x)
    (hsl : ∀ k, f 0 ≤ k → max (g 0) k + 1 ≤ g k) :
    Zef2Prov (βψ + γ) e H (g ∘ f) c (Δsup.erase (Semiformula.rel rr vv) ∪ Γ) := by
  exact ((ih hβNF hmono hinfl hsl).weakening (by
    intro x hx; simp only [Finset.mem_union, Finset.mem_erase] at hx ⊢
    rcases hx with ⟨hne, hxs⟩ | hxΓ
    · exact Or.inl ⟨hne, hsub hxs⟩
    · exact Or.inr hxΓ)).mono
    (le_of_lt (Zekd.add_lt_add_left_NF hβψNF hβNF hγNF hβ))

private theorem atomRun_allω {ar : ℕ} {rr : (ℒₒᵣ).Rel ar} {vv : Fin ar → Semiterm ℒₒᵣ ℕ 0}
    {βψ γ e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ Γ₀ : Finset (ArithmeticFormula ℕ)}
    {g : ℕ → ℕ} (hβψNF : βψ.NF) (hg0 : Nlog βψ ≤ g 0) (hαN : Nlog γ ≤ f 0) (χ : ArithmeticSemiformula ℕ 1)
    (β : ℕ → ONote) (hβ : ∀ n, β n < γ) (hβNF : ∀ n, (β n).NF)
    (ih : ∀ n, (β n).NF → Monotone (rel1 f n) → (∀ x, x ≤ rel1 f n x) →
      (∀ k, rel1 f n 0 ≤ k → max (g 0) k + 1 ≤ g k) →
      Zef2Prov (βψ + β n) e (adjoin H n) (g ∘ rel1 f n) c
        ((insert (χ/[nm n]) Γ₀).erase (Semiformula.rel rr vv) ∪ Γ))
    (hγNF : γ.NF) (hmono : Monotone f) (hinfl : ∀ x, x ≤ f x)
    (hsl : ∀ k, f 0 ≤ k → max (g 0) k + 1 ≤ g k) :
    Zef2Prov (βψ + γ) e H (g ∘ f) c ((insert (∀⁰ χ) Γ₀).erase (Semiformula.rel rr vv) ∪ Γ) := by
  have hhead : (∀⁰ χ) ≠ Semiformula.rel rr vv := (fun h => by cases h)
  have haddNF : (βψ + γ).NF := ONote.add_nf βψ γ
  have ihn : ∀ n, Zef2Prov (βψ + β n) e (adjoin H n) (g ∘ rel1 f n) c
      (insert (χ/[nm n]) (Γ₀.erase (Semiformula.rel rr vv) ∪ Γ)) := by
    intro n
    refine (ih n (hβNF n) (rel1_monotone hmono n)
      (rel1_infl hinfl n)
      (fun k hk => hsl k (le_trans (by
        simp only [rel1]; exact hmono (Nat.zero_le _)) hk))).weakening (by
        intro x hx
        simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢; tauto)
  refine Zef2Prov.of haddNF (Cl_of_NF haddNF)
    (Nlog_add_le_comp hβψNF hγNF hg0 hαN (hsl _ le_rfl)) ?_
  have hAll : Zef2 (βψ + γ) e H (g ∘ f) c
      (insert (∀⁰ χ) (Γ₀.erase (Semiformula.rel rr vv) ∪ Γ)) := by
    exact Zef2.allω (Nlog_add_le_comp hβψNF hγNF hg0 hαN (hsl _ le_rfl)) χ
      (fun n => (ihn n).choose)
      (fun n => lt_of_le_of_lt (ihn n).choose_spec.1
        (Zekd.add_lt_add_left_NF hβψNF (hβNF n) hγNF (hβ n)))
      (fun n => (ihn n).choose_spec.2.1) haddNF
      (fun n => Cl_of_NF (ihn n).choose_spec.2.1)
      (fun n => (ihn n).choose_spec.2.2.2.2)
  exact hAll.wk (Nlog_add_le_comp hβψNF hγNF hg0 hαN (hsl _ le_rfl)) (by
    intro x hx
    simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢
    rcases hx with rfl | hx
    · exact Or.inl ⟨hhead, Or.inl rfl⟩
    · tauto)

private theorem atomRun_exI {ar : ℕ} {rr : (ℒₒᵣ).Rel ar} {vv : Fin ar → Semiterm ℒₒᵣ ℕ 0}
    {βψ γ β e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ Γ₀ : Finset (ArithmeticFormula ℕ)}
    {g : ℕ → ℕ} (hβψNF : βψ.NF) (hg0 : Nlog βψ ≤ g 0) (hg_infl : ∀ x, x ≤ g x) (hαN : Nlog γ ≤ f 0)
    (χ : ArithmeticSemiformula ℕ 1) (n : ℕ) (hβ : β < γ) (hβNF : β.NF) (hbound : n ≤ f 0)
    (ih : β.NF → Monotone f → (∀ x, x ≤ f x) → (∀ k, f 0 ≤ k → max (g 0) k + 1 ≤ g k) →
      Zef2Prov (βψ + β) e H (g ∘ f) c ((insert (χ/[nm n]) Γ₀).erase (Semiformula.rel rr vv) ∪ Γ))
    (hγNF : γ.NF) (hmono : Monotone f) (hinfl : ∀ x, x ≤ f x)
    (hsl : ∀ k, f 0 ≤ k → max (g 0) k + 1 ≤ g k) :
    Zef2Prov (βψ + γ) e H (g ∘ f) c ((insert (∃⁰ χ) Γ₀).erase (Semiformula.rel rr vv) ∪ Γ) := by
  have hhead : (∃⁰ χ) ≠ Semiformula.rel rr vv := (fun h => by cases h)
  have haddNF : (βψ + γ).NF := ONote.add_nf βψ γ
  obtain ⟨a, hale, haNF, haH, hag, Da⟩ := ih hβNF hmono hinfl hsl
  have Da' : Zef2 a e H (g ∘ f) c
      (insert (χ/[nm n]) (Γ₀.erase (Semiformula.rel rr vv) ∪ Γ)) :=
    Da.wk hag (by
      intro x hx
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢; tauto)
  refine Zef2Prov.of haddNF (Cl_of_NF haddNF)
    (Nlog_add_le_comp hβψNF hγNF hg0 hαN (hsl _ le_rfl)) ?_
  have hbound' : n ≤ (g ∘ f) 0 := le_trans hbound (hg_infl (f 0))
  exact Zef2.exI (Nlog_add_le_comp hβψNF hγNF hg0 hαN (hsl _ le_rfl)) χ n
    (lt_of_le_of_lt hale (Zekd.add_lt_add_left_NF hβψNF hβNF hγNF hβ))
    haNF haddNF haH hbound' Da'
  |>.wk (Nlog_add_le_comp hβψNF hγNF hg0 hαN (hsl _ le_rfl)) (by
    intro x hx
    simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢
    rcases hx with rfl | hx
    · exact Or.inl ⟨hhead, Or.inl rfl⟩
    · tauto)

private theorem atomRun_cut {ar : ℕ} {rr : (ℒₒᵣ).Rel ar} {vv : Fin ar → Semiterm ℒₒᵣ ℕ 0}
    {βψ γ βφ βψ' e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ}
    {Γ Γ₀ : Finset (ArithmeticFormula ℕ)} {g : ℕ → ℕ} (hβψNF : βψ.NF) (hg0 : Nlog βψ ≤ g 0)
    (hg_infl : ∀ x, x ≤ g x) (hαN : Nlog γ ≤ f 0) (χ : ArithmeticFormula ℕ) (hχc : χ.complexity < c)
    (hcutRead' : χ.complexity ≤ f 0) (hβφ : βφ < γ) (hβψ' : βψ' < γ) (hβφNF : βφ.NF) (hβψNF' : βψ'.NF)
    (ih₁ : βφ.NF → Monotone f → (∀ x, x ≤ f x) → (∀ k, f 0 ≤ k → max (g 0) k + 1 ≤ g k) →
      Zef2Prov (βψ + βφ) e H (g ∘ f) c ((insert χ Γ₀).erase (Semiformula.rel rr vv) ∪ Γ))
    (ih₂ : βψ'.NF → Monotone f → (∀ x, x ≤ f x) → (∀ k, f 0 ≤ k → max (g 0) k + 1 ≤ g k) →
      Zef2Prov (βψ + βψ') e H (g ∘ f) c ((insert (∼χ) Γ₀).erase (Semiformula.rel rr vv) ∪ Γ))
    (hγNF : γ.NF) (hmono : Monotone f) (hinfl : ∀ x, x ≤ f x)
    (hsl : ∀ k, f 0 ≤ k → max (g 0) k + 1 ≤ g k) :
    Zef2Prov (βψ + γ) e H (g ∘ f) c (Γ₀.erase (Semiformula.rel rr vv) ∪ Γ) := by
  obtain ⟨a₁, ha₁le, ha₁NF, ha₁H, ha₁g, Dc₁⟩ := ih₁ hβφNF hmono hinfl hsl
  obtain ⟨a₂, ha₂le, ha₂NF, ha₂H, ha₂g, Dc₂⟩ := ih₂ hβψNF' hmono hinfl hsl
  have haddNF : (βψ + γ).NF := ONote.add_nf βψ γ
  have Dc₁' : Zef2 a₁ e H (g ∘ f) c
      (insert χ (Γ₀.erase (Semiformula.rel rr vv) ∪ Γ)) :=
    Dc₁.wk ha₁g (by
      intro x hx
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢; tauto)
  have Dc₂' : Zef2 a₂ e H (g ∘ f) c
      (insert (∼χ) (Γ₀.erase (Semiformula.rel rr vv) ∪ Γ)) :=
    Dc₂.wk ha₂g (by
      intro x hx
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢; tauto)
  refine Zef2Prov.of haddNF (Cl_of_NF haddNF)
    (Nlog_add_le_comp hβψNF hγNF hg0 hαN (hsl _ le_rfl)) ?_
  exact Zef2.cut (Nlog_add_le_comp hβψNF hγNF hg0 hαN (hsl _ le_rfl)) χ hχc
    (le_trans hcutRead' (hg_infl (f 0)))
    (lt_of_le_of_lt ha₁le (Zekd.add_lt_add_left_NF hβψNF hβφNF hγNF hβφ))
    (lt_of_le_of_lt ha₂le (Zekd.add_lt_add_left_NF hβψNF hβψNF' hγNF hβψ'))
    ha₁NF ha₂NF haddNF ha₁H ha₂H Dc₁' Dc₂'

/-- **The atom-cut lemma (axL-pair surgery)** — the `c = 0`-shape sub-crux of the top-rank
cut, at general rank.  A fixed premise `D₂` deriving `insert (nrel rr vv) Γ` is spliced into a
derivation of a context containing `rel rr vv`: every axL leaf whose pair IS `(rr, vv)` is
replaced by `D₂` (weakened); all other nodes rebuild at the fresh root `βψ + γ` with the
absorbing gate (`Nlog_add_le_comp` + the slot-threaded slack, exactly as in the running
reduction).  Output slot `g ∘ f`. -/
theorem atomCutRun_Zf2 {ar : ℕ} {rr : (ℒₒᵣ).Rel ar} {vv : Fin ar → Semiterm ℒₒᵣ ℕ 0}
    {c : ℕ} {βψ e : ONote} {Γ : Finset (ArithmeticFormula ℕ)} {g : ℕ → ℕ} {H₂ : ONote → Prop}
    (hβψNF : βψ.NF) (heNF : e.NF)
    (hg_mono : Monotone g) (hg_infl : ∀ x, x ≤ g x)
    (D₂ : Zef2 βψ e H₂ g c (insert (Semiformula.nrel rr vv) Γ))
    {γ : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {Δ : Finset (ArithmeticFormula ℕ)}
    (D : Zef2 γ e H f c Δ) (hγNF : γ.NF)
    (hmono : Monotone f) (hinfl : ∀ x, x ≤ f x) (hsl : ∀ k, f 0 ≤ k → max (g 0) k + 1 ≤ g k) :
    Zef2Prov (βψ + γ) e H (g ∘ f) c (Δ.erase (Semiformula.rel rr vv) ∪ Γ) := by
  have hg0 : Nlog βψ ≤ g 0 := Zef2.gate D₂
  induction D with
  | @axL γ e H f c Δ ar' hαN r v hp hn =>
      exact atomRun_axL hβψNF hg_mono hg_infl hg0 hαN r v hp hn D₂ hγNF hmono hinfl hsl
  | @wk γ e H f c Δsub Δsup hαN hsub D' ih =>
      exact atomRun_wk hsub (ih heNF D₂) hγNF hmono hinfl hsl
  | @weak γ β e H f c Δsub Δsup hαN hβ hβNF _hγNF' _hβH hsub D' ih =>
      exact atomRun_weak hβψNF hβ hβNF hsub (ih heNF D₂) hγNF hmono hinfl hsl
  | @allω γ e H f c Γ₀ hαN χ β hβ hβNF _hγNF' _hβH _dd ih =>
      exact atomRun_allω hβψNF hg0 hαN χ β hβ hβNF (fun n => ih n heNF D₂) hγNF hmono hinfl hsl
  | @exI γ β e H f c Γ₀ hαN χ n hβ hβNF _hγNF' _hβH hbound _dχ ih =>
      exact atomRun_exI hβψNF hg0 hg_infl hαN χ n hβ hβNF hbound (ih heNF D₂) hγNF hmono hinfl hsl
  | @cut γ βφ' βψ' e H f c Γ₀ hαN χ hχc hcutRead' hβφ hβψ' hβφNF hβψNF' _hγNF' _hβφH _hβψH _d₁ _d₂ ih₁ ih₂ =>
      exact atomRun_cut hβψNF hg0 hg_infl hαN χ hχc hcutRead' hβφ hβψ' hβφNF hβψNF'
        (ih₁ heNF D₂) (ih₂ heNF D₂) hγNF hmono hinfl hsl

end GoodsteinPA.OperatorZeh
