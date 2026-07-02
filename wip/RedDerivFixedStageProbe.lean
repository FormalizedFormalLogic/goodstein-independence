/-
# `RedDerivFixedStageProbe` — diagnostic for the REBUILD-Z lap-2 reduction wall

Companion to `REBUILD-Z-LAP2-FINDING-2026-07-02-fixed-stage-reduction-wall.md`.

`src/GoodsteinPA/OperatorZeh.lean`'s `redDeriv` (the running-family §19.6 reduction) closes
every case of the induction EXCEPT the principal `exI`, where the family member `fam n` — at the
RUNNING stage `max m₀ n` — forces the cut output up to stage `max m n`, which cannot be lowered to
the required output stage `m`.

**This probe isolates the culprit.**  It is `redDeriv` verbatim, with ONE change: the family is
supplied at the FIXED stage `m₀` instead of the running stage `max m₀ n`.  With that single
change the principal `exI` closes **sorry-free** (raise `fam n` from `m₀` to the ambient `m` via
`m₀ ≤ m`, cut at `m`, output at `m` — no leak).  So the obstruction is EXACTLY the running stage
of the inverted family (`allInv_Zeh` returns the `n`-th ω-premise, and the `allω` rule bakes
`max m n` into every branch).  The reduction itself is otherwise standard.

Off the live build (`wip/`, not in a `lean_lib`); check with `lake env lean wip/RedDerivFixedStageProbe.lean`.
-/
import GoodsteinPA.OperatorZeh

namespace GoodsteinPA.OperatorZeh

open LO LO.FirstOrder ONote Ordinal
open GoodsteinPA.FastGrowing
open GoodsteinPA.OperatorZinfty

/-- `redDeriv` with the family at the FIXED stage `m₀` — closes SORRY-FREE.  The ONLY difference
from `src`'s `redDeriv` is `fam`'s stage (`m₀`, not `max m₀ n`) and, consequently, the principal
`exI` cut runs at the ambient `m` (no stage leak). -/
theorem redDerivFixed {φ : SyntacticSemiformula ℒₒᵣ 1} {c m₀ : ℕ} {α e : ONote} {Γ : Seq}
    (hφc : φ.complexity < c) (hαNF : α.NF) (heNF : e.NF)
    (fam : ∀ n (H' : ONote → Prop), Zeh α e H' m₀ c (insert (φ/[nm n]) Γ)) :
    ∀ {γ : ONote} {H : ONote → Prop} {m : ℕ} {Δ : Seq}, Zeh γ e H m c Δ → γ.NF →
      m₀ ≤ m → (∃⁰ ∼φ) ∈ Δ →
      ZehProv (osucc (α + γ)) e H m c (Δ.erase (∃⁰ ∼φ) ∪ Γ) := by
  intro γ H m Δ D
  induction D with
  | @axL γ e H m c Δ ar r v hp hn =>
      intro hγNF hm hmem
      refine ZehProv.of (osucc_NF (ONote.add_nf α γ)) (Cl_of_NF (osucc_NF (ONote.add_nf α γ))) ?_
      exact Zeh.axL r v
        (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), hp⟩))
        (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), hn⟩))
  | @wk γ e H m c Δsub Δsup hsub D' ih =>
      intro hγNF hm hmem
      by_cases hd : (∃⁰ ∼φ) ∈ Δsub
      · exact (ih hφc heNF fam hγNF hm hd).weakening (by
          intro x hx; simp only [Finset.mem_union, Finset.mem_erase] at hx ⊢
          rcases hx with ⟨hne, hxs⟩ | hxΓ
          · exact Or.inl ⟨hne, hsub hxs⟩
          · exact Or.inr hxΓ)
      · refine ⟨γ, le_trans (Zekd.le_add_left_NF hαNF hγNF)
          (le_of_lt (Zekd.lt_osucc (ONote.add_nf α γ))), hγNF, Cl_of_NF hγNF, D'.wk (by
            intro x hx; simp only [Finset.mem_union, Finset.mem_erase]
            exact Or.inl ⟨fun e0 => hd (e0 ▸ hx), hsub hx⟩)⟩
  | @weak γ β e H m c Δsub Δsup hβ hβNF hγNF' hβH hsub D' ih =>
      intro hγNF hm hmem
      by_cases hd : (∃⁰ ∼φ) ∈ Δsub
      · exact ((ih hφc heNF fam hβNF hm hd).weakening (by
          intro x hx; simp only [Finset.mem_union, Finset.mem_erase] at hx ⊢
          rcases hx with ⟨hne, hxs⟩ | hxΓ
          · exact Or.inl ⟨hne, hsub hxs⟩
          · exact Or.inr hxΓ)).mono
          (le_of_lt (Zekd.add_osucc_descent hαNF hβNF hγNF hβ))
      · refine ⟨β, le_of_lt (lt_of_lt_of_le hβ (le_trans (Zekd.le_add_left_NF hαNF hγNF)
          (le_of_lt (Zekd.lt_osucc (ONote.add_nf α γ))))), hβNF, Cl_of_NF hβNF, D'.wk (by
            intro x hx; simp only [Finset.mem_union, Finset.mem_erase]
            exact Or.inl ⟨fun e0 => hd (e0 ▸ hx), hsub hx⟩)⟩
  | @allω γ e H m c Γ₀ χ β hβ hβNF hγNF' hβH dd ih =>
      intro hγNF hm hmem
      have hhead : (∀⁰ χ) ≠ (∃⁰ ∼φ) := by intro h; simp [UnivQuantifier.all, ExsQuantifier.exs] at h
      have hmem0 : (∃⁰ ∼φ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
      have hsuccNF : (osucc (α + γ)).NF := osucc_NF (ONote.add_nf α γ)
      have ihn : ∀ n, ZehProv (osucc (α + β n)) e (adjoin H n) (max m n) c
          (insert (χ/[nm n]) (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) := by
        intro n
        exact (ih n hφc heNF fam (hβNF n) (le_trans hm (le_max_left _ _)) (Finset.mem_insert_of_mem hmem0)).weakening (by
          intro x hx
          simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢; tauto)
      refine ZehProv.of hsuccNF (Cl_of_NF hsuccNF) ?_
      have hAll : Zeh (osucc (α + γ)) e H m c
          (insert (∀⁰ χ) (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) := by
        refine Zeh.allω χ (fun n => (ihn n).choose)
          (fun n => lt_of_le_of_lt (ihn n).choose_spec.1
            (Zekd.add_osucc_descent hαNF (hβNF n) hγNF (hβ n)))
          (fun n => (ihn n).choose_spec.2.1) hsuccNF
          (fun n => Cl_of_NF (ihn n).choose_spec.2.1)
          (fun n => (ihn n).choose_spec.2.2.2)
      exact hAll.wk (by
        intro x hx
        simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢
        rcases hx with rfl | hx
        · exact Or.inl ⟨hhead, Or.inl rfl⟩
        · tauto)
  | @exI γ β e H m c Γ₀ χ n hβ hβNF hγNF' hβH hbound dχ ih =>
      intro hγNF hm hmem
      have hsuccNF : (osucc (α + γ)).NF := osucc_NF (ONote.add_nf α γ)
      by_cases hhd : (∃⁰ χ) = (∃⁰ ∼φ)
      · -- PRINCIPAL: χ = ∼φ; cut `fam n` (FIXED stage `m₀`, raised to `m`) against the ∃-premise.
        have hχ : χ = ∼φ := by simpa [ExsQuantifier.exs] using hhd
        subst hχ
        rw [Finset.erase_insert_eq_erase]
        have hNeg : (∼φ)/[nm n] = ∼(φ/[nm n]) := by simp
        have hcompl : (φ/[nm n]).complexity < c := by simpa using hφc
        -- KEY: `fam n` at fixed `m₀` lifts to the ambient `m` (`m₀ ≤ m`).  Cut runs at `m`.
        have famn : Zeh α e H m c (insert (φ/[nm n]) (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) :=
          ((fam n H).mono_H (fun _ h => h) hm).wk (by
            intro x hx; simp only [Finset.mem_insert, Finset.mem_union] at hx ⊢; tauto)
        have hαlt : α < osucc (α + γ) :=
          lt_of_le_of_lt (Zekd.le_add_right_NF hαNF hγNF) (Zekd.lt_osucc (ONote.add_nf α γ))
        refine ZehProv.of hsuccNF (Cl_of_NF hsuccNF) ?_
        by_cases hd : (∃⁰ ∼φ) ∈ Γ₀
        · obtain ⟨a, hale, haNF, haH, Da⟩ := ih hφc heNF fam hβNF hm (Finset.mem_insert_of_mem hd)
          have Da' : Zeh a e H m c (insert (∼(φ/[nm n])) (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) :=
            Da.wk (by
              intro x hx
              simp only [hNeg, Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢; tauto)
          exact Zeh.cut (φ/[nm n]) hcompl hαlt
            (lt_of_le_of_lt hale (Zekd.add_osucc_descent hαNF hβNF hγNF hβ))
            hαNF haNF hsuccNF (Cl_of_NF hαNF) haH famn Da'
        · have Dβ' : Zeh β e H m c (insert (∼(φ/[nm n])) (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) :=
            dχ.wk (by
              intro x hx
              simp only [hNeg, Finset.mem_insert] at hx
              simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_erase]
              rcases hx with rfl | hxΓ₀
              · exact Or.inl rfl
              · exact Or.inr (Or.inl ⟨fun e0 => hd (e0 ▸ hxΓ₀), hxΓ₀⟩))
          exact Zeh.cut (φ/[nm n]) hcompl hαlt
            (lt_of_lt_of_le hβ (le_trans (Zekd.le_add_left_NF hαNF hγNF)
              (le_of_lt (Zekd.lt_osucc (ONote.add_nf α γ)))))
            hαNF hβNF hsuccNF (Cl_of_NF hαNF) (Cl_of_NF hβNF) famn Dβ'
      · have hmem0 : (∃⁰ ∼φ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhd e.symm
        obtain ⟨a, hale, haNF, haH, Da⟩ := ih hφc heNF fam hβNF hm (Finset.mem_insert_of_mem hmem0)
        have Da' : Zeh a e H m c (insert (χ/[nm n]) (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) :=
          Da.wk (by
            intro x hx
            simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢; tauto)
        refine ZehProv.of hsuccNF (Cl_of_NF hsuccNF) ?_
        have hExI : Zeh (osucc (α + γ)) e H m c
            (insert (∃⁰ χ) (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) :=
          Zeh.exI χ n (lt_of_le_of_lt hale (Zekd.add_osucc_descent hαNF hβNF hγNF hβ))
            haNF hsuccNF haH hbound Da'
        exact hExI.wk (by
          intro x hx
          simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢
          rcases hx with rfl | hx
          · exact Or.inl ⟨hhd, Or.inl rfl⟩
          · tauto)
  | @cut γ βφ βψ e H m c Γ₀ χ hχc hβφ hβψ hβφNF hβψNF hγNF' hβφH hβψH d₁ d₂ ih₁ ih₂ =>
      intro hγNF hm hmem
      obtain ⟨a₁, ha₁le, ha₁NF, ha₁H, D₁⟩ := ih₁ hφc heNF fam hβφNF hm (Finset.mem_insert_of_mem hmem)
      obtain ⟨a₂, ha₂le, ha₂NF, ha₂H, D₂⟩ := ih₂ hφc heNF fam hβψNF hm (Finset.mem_insert_of_mem hmem)
      have hsuccNF : (osucc (α + γ)).NF := osucc_NF (ONote.add_nf α γ)
      have D₁' : Zeh a₁ e H m c (insert χ (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) :=
        D₁.wk (by
          intro x hx
          simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢; tauto)
      have D₂' : Zeh a₂ e H m c (insert (∼χ) (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) :=
        D₂.wk (by
          intro x hx
          simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢; tauto)
      refine ZehProv.of hsuccNF (Cl_of_NF hsuccNF) ?_
      exact Zeh.cut χ hχc
        (lt_of_le_of_lt ha₁le (Zekd.add_osucc_descent hαNF hβφNF hγNF hβφ))
        (lt_of_le_of_lt ha₂le (Zekd.add_osucc_descent hαNF hβψNF hγNF hβψ))
        ha₁NF ha₂NF hsuccNF ha₁H ha₂H D₁' D₂'

end GoodsteinPA.OperatorZeh

#print axioms GoodsteinPA.OperatorZeh.redDerivFixed
