module

public import GoodsteinPA.OperatorZeh.Inversion
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

namespace GoodsteinPA.OperatorZeh

open LO LO.FirstOrder ONote Ordinal
open GoodsteinPA.OperatorZinfty

/-! ## The re-slot domination facts (restated for `rel1 · ·` slots) -/

/-- **The ∀-family member re-slots to `g∘f`**: for `g` monotone, `f` monotone + inflationary,
and witness `n ≤ f 0`, `rel1 g n ≤ g∘f` pointwise. -/
theorem reslot_family {f g : ℕ → ℕ} (hg_mono : Monotone g)
    (hf_infl : ∀ x, x ≤ f x) (hf_mono : Monotone f) {n : ℕ} (hn : n ≤ f 0) :
    ∀ x, rel1 g n x ≤ (g ∘ f) x := by
  intro x
  simp only [rel1, Function.comp]
  refine hg_mono ?_
  rcases le_total n x with h | h
  · rw [max_eq_right h]; exact hf_infl x
  · rw [max_eq_left h]; exact le_trans hn (hf_mono (Nat.zero_le x))

/-- **The ∃-side reduct re-slots to `g∘f`**: `f ≤ g∘f` for `g` inflationary. -/
theorem reslot_exside {f g : ℕ → ℕ} (hg_infl : ∀ x, x ≤ g x) :
    ∀ x, f x ≤ (g ∘ f) x := fun x => hg_infl (f x)

/-! ## The running-family reduction, sorry-free -/

/-- **`cutReduceAllAuxRunning_Zf`** — the running-family cut-reduction shape of [Tow20,
Theorem 19.6], carried through in the function-slot form [EW12, Lemma 25]: the stage `m` is
replaced by the current slot `f'` (threaded monotone + inflationary), output slot `g∘f'`, via
the two axis-critical moves:
- **principal `exI`** — both cut premises re-slot to `g∘f'` (`reslot_family` / `reslot_exside`),
  cut lands at `g∘f'` (the conclusion slot) with NO leak — the gap the fixed `hardy e m` bound
  could not cross;
- **`allω`** — each branch's IH output slot `g ∘ rel1 f' n` is `rel1 (g∘f') n` by `rel1_comp`
  (definitional), exactly the `allω` node's branch slot. -/
theorem cutReduceAllAuxRunning_Zf {φ : ArithmeticSemiformula ℕ 1} {c : ℕ} {α e : ONote} {Γ : Finset (ArithmeticFormula ℕ)}
    {g : ℕ → ℕ} (hφc : φ.complexity < c) (hαNF : α.NF) (heNF : e.NF)
    (hg_mono : Monotone g) (hg_infl : ∀ x, x ≤ g x)
    (fam : ∀ n (H' : ONote → Prop), Zef α e H' (rel1 g n) c (insert (φ/[nm n]) Γ))
    {γ : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {Δ : Finset (ArithmeticFormula ℕ)} (D : Zef γ e H f c Δ)
    (hγNF : γ.NF) (hmono : Monotone f) (hinfl : ∀ x, x ≤ f x) (hmem : (∃⁰ ∼φ) ∈ Δ) :
    ZefProv (osucc (α + γ)) e H (g ∘ f) c (Δ.erase (∃⁰ ∼φ) ∪ Γ) := by
  induction D with
  | @axL γ e H f c Δ ar r v hp hn =>
      refine ZefProv.of (osucc_NF (ONote.add_nf α γ)) (Cl_of_NF (osucc_NF (ONote.add_nf α γ))) ?_
      exact Zef.axL r v
        (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), hp⟩))
        (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), hn⟩))
  | @wk γ e H f c Δsub Δsup hsub D' ih =>
      by_cases hd : (∃⁰ ∼φ) ∈ Δsub
      · exact (ih hφc heNF fam hγNF hmono hinfl hd).weakening (by
          intro x hx; simp only [Finset.mem_union, Finset.mem_erase] at hx ⊢
          rcases hx with ⟨hne, hxs⟩ | hxΓ
          · exact Or.inl ⟨hne, hsub hxs⟩
          · exact Or.inr hxΓ)
      · refine ⟨γ, le_trans (Zekd.le_add_left_NF hαNF hγNF)
          (le_of_lt (Zekd.lt_osucc (ONote.add_nf α γ))), hγNF, Cl_of_NF hγNF,
          (D'.mono_f (reslot_exside hg_infl)).wk (by
            intro x hx; simp only [Finset.mem_union, Finset.mem_erase]
            exact Or.inl ⟨fun e0 => hd (e0 ▸ hx), hsub hx⟩)⟩
  | @weak γ β e H f c Δsub Δsup hβ hβNF hγNF' hβH hsub D' ih =>
      by_cases hd : (∃⁰ ∼φ) ∈ Δsub
      · exact ((ih hφc heNF fam hβNF hmono hinfl hd).weakening (by
          intro x hx; simp only [Finset.mem_union, Finset.mem_erase] at hx ⊢
          rcases hx with ⟨hne, hxs⟩ | hxΓ
          · exact Or.inl ⟨hne, hsub hxs⟩
          · exact Or.inr hxΓ)).mono
          (le_of_lt (Zekd.add_osucc_descent hαNF hβNF hγNF hβ))
      · refine ⟨β, le_of_lt (lt_of_lt_of_le hβ (le_trans (Zekd.le_add_left_NF hαNF hγNF)
          (le_of_lt (Zekd.lt_osucc (ONote.add_nf α γ))))), hβNF, Cl_of_NF hβNF,
          (D'.mono_f (reslot_exside hg_infl)).wk (by
            intro x hx; simp only [Finset.mem_union, Finset.mem_erase]
            exact Or.inl ⟨fun e0 => hd (e0 ▸ hx), hsub hx⟩)⟩
  | @allω γ e H f c Γ₀ χ β hβ hβNF hγNF' hβH dd ih =>
      have hhead : (∀⁰ χ) ≠ (∃⁰ ∼φ) := by intro h; simp [UnivQuantifier.all, ExsQuantifier.exs] at h
      have hmem0 : (∃⁰ ∼φ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
      have hsuccNF : (osucc (α + γ)).NF := osucc_NF (ONote.add_nf α γ)
      have ihn : ∀ n, ZefProv (osucc (α + β n)) e (adjoin H n) (g ∘ rel1 f n) c
          (insert (χ/[nm n]) (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) := by
        intro n
        exact (ih n hφc heNF fam (hβNF n) (rel1_monotone hmono n) (rel1_infl hinfl n)
          (Finset.mem_insert_of_mem hmem0)).weakening (by
            intro x hx
            simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢; tauto)
      refine ZefProv.of hsuccNF (Cl_of_NF hsuccNF) ?_
      have hAll : Zef (osucc (α + γ)) e H (g ∘ f) c
          (insert (∀⁰ χ) (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) := by
        -- branch slot `g ∘ rel1 f n` is `rel1 (g∘f) n` by `rel1_comp` (definitional)
        refine Zef.allω χ (fun n => (ihn n).choose)
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
  | @exI γ β e H f c Γ₀ χ n hβ hβNF hγNF' hβH hbound dχ ih =>
      have hsuccNF : (osucc (α + γ)).NF := osucc_NF (ONote.add_nf α γ)
      by_cases hhd : (∃⁰ χ) = (∃⁰ ∼φ)
      · -- PRINCIPAL: χ = ∼φ; cut `fam n` (re-slotted to `g∘f`) against the ∃-premise.
        have hχ : χ = ∼φ := by simpa [ExsQuantifier.exs] using hhd
        subst hχ
        rw [Finset.erase_insert_eq_erase]
        have hNeg : (∼φ)/[nm n] = ∼(φ/[nm n]) := by simp
        have hcompl : (φ/[nm n]).complexity < c := by simpa using hφc
        -- `fam n` re-slots `rel1 g n → g∘f` (both premises land at the conclusion slot `g∘f`)
        have famn : Zef α e H (g ∘ f) c (insert (φ/[nm n]) (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) :=
          ((fam n H).mono_f (reslot_family hg_mono hinfl hmono hbound)).wk (by
            intro x hx; simp only [Finset.mem_insert, Finset.mem_union] at hx ⊢; tauto)
        have hαlt : α < osucc (α + γ) :=
          lt_of_le_of_lt (Zekd.le_add_right_NF hαNF hγNF) (Zekd.lt_osucc (ONote.add_nf α γ))
        by_cases hd : (∃⁰ ∼φ) ∈ Γ₀
        · obtain ⟨a, hale, haNF, haH, Da⟩ := ih hφc heNF fam hβNF hmono hinfl
            (Finset.mem_insert_of_mem hd)
          have Da' : Zef a e H (g ∘ f) c
              (insert (∼(φ/[nm n])) (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) :=
            Da.wk (by
              intro x hx
              simp only [hNeg, Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢; tauto)
          refine ZefProv.of hsuccNF (Cl_of_NF hsuccNF) ?_
          exact Zef.cut (φ/[nm n]) hcompl hαlt
            (lt_of_le_of_lt hale (Zekd.add_osucc_descent hαNF hβNF hγNF hβ))
            hαNF haNF hsuccNF (Cl_of_NF hαNF) haH famn Da'
        · -- ∃-premise `dχ` re-slots `f → g∘f`
          have Dβ' : Zef β e H (g ∘ f) c
              (insert (∼(φ/[nm n])) (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) :=
            (dχ.mono_f (reslot_exside hg_infl)).wk (by
              intro x hx
              simp only [hNeg, Finset.mem_insert] at hx
              simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_erase]
              rcases hx with rfl | hxΓ₀
              · exact Or.inl rfl
              · exact Or.inr (Or.inl ⟨fun e0 => hd (e0 ▸ hxΓ₀), hxΓ₀⟩))
          refine ZefProv.of hsuccNF (Cl_of_NF hsuccNF) ?_
          exact Zef.cut (φ/[nm n]) hcompl hαlt
            (lt_of_lt_of_le hβ (le_trans (Zekd.le_add_left_NF hαNF hγNF)
              (le_of_lt (Zekd.lt_osucc (ONote.add_nf α γ)))))
            hαNF hβNF hsuccNF (Cl_of_NF hαNF) (Cl_of_NF hβNF) famn Dβ'
      · have hmem0 : (∃⁰ ∼φ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhd e.symm
        obtain ⟨a, hale, haNF, haH, Da⟩ := ih hφc heNF fam hβNF hmono hinfl
          (Finset.mem_insert_of_mem hmem0)
        have Da' : Zef a e H (g ∘ f) c (insert (χ/[nm n]) (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) :=
          Da.wk (by
            intro x hx
            simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢; tauto)
        refine ZefProv.of hsuccNF (Cl_of_NF hsuccNF) ?_
        -- non-principal `exI`: witness bound `n ≤ f 0 ≤ (g∘f) 0` (via `hg_infl` at `f 0`)
        have hbound' : n ≤ (g ∘ f) 0 := le_trans hbound (hg_infl (f 0))
        have hExI : Zef (osucc (α + γ)) e H (g ∘ f) c
            (insert (∃⁰ χ) (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) :=
          Zef.exI χ n (lt_of_le_of_lt hale (Zekd.add_osucc_descent hαNF hβNF hγNF hβ))
            haNF hsuccNF haH hbound' Da'
        exact hExI.wk (by
          intro x hx
          simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢
          rcases hx with rfl | hx
          · exact Or.inl ⟨hhd, Or.inl rfl⟩
          · tauto)
  | @cut γ βφ βψ e H f c Γ₀ χ hχc hβφ hβψ hβφNF hβψNF hγNF' hβφH hβψH d₁ d₂ ih₁ ih₂ =>
      obtain ⟨a₁, ha₁le, ha₁NF, ha₁H, D₁⟩ := ih₁ hφc heNF fam hβφNF hmono hinfl (Finset.mem_insert_of_mem hmem)
      obtain ⟨a₂, ha₂le, ha₂NF, ha₂H, D₂⟩ := ih₂ hφc heNF fam hβψNF hmono hinfl (Finset.mem_insert_of_mem hmem)
      have hsuccNF : (osucc (α + γ)).NF := osucc_NF (ONote.add_nf α γ)
      have D₁' : Zef a₁ e H (g ∘ f) c (insert χ (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) :=
        D₁.wk (by
          intro x hx
          simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢; tauto)
      have D₂' : Zef a₂ e H (g ∘ f) c (insert (∼χ) (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) :=
        D₂.wk (by
          intro x hx
          simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢; tauto)
      refine ZefProv.of hsuccNF (Cl_of_NF hsuccNF) ?_
      exact Zef.cut χ hχc
        (lt_of_le_of_lt ha₁le (Zekd.add_osucc_descent hαNF hβφNF hγNF hβφ))
        (lt_of_le_of_lt ha₂le (Zekd.add_osucc_descent hαNF hβψNF hγNF hβψ))
        ha₁NF ha₂NF hsuccNF ha₁H ha₂H D₁' D₂'

/-- **`stepAllω_Zf`** — the principal ∀/∃ cut-reduction step in the slot calculus, IHs at one
control `E` and stage-slots, output slot `g∘f`.  Invert the ∀-side `D₁` (slot `g`) to the
running family via `allInv_Zef`, then apply `cutReduceAllAuxRunning_Zf` against the ∃-side `D₂`
(slot `f`).  Both premises are `ZefProv` wrappers; slots monotone + inflationary. -/
theorem stepAllω_Zf {E : ONote} {H : ONote → Prop} {c : ℕ} {Γ : Finset (ArithmeticFormula ℕ)}
    {χ : ArithmeticSemiformula ℕ 1} {βφ βψ : ONote} {f g : ℕ → ℕ}
    (hENF : E.NF) (hχc : χ.complexity < c)
    (hg_mono : Monotone g) (hg_infl : ∀ x, x ≤ g x)
    (hf_mono : Monotone f) (hf_infl : ∀ x, x ≤ f x)
    (D₁ : ZefProv (expTower βφ) E H g c (insert (∀⁰ χ) Γ))
    (D₂ : ZefProv (expTower βψ) E H f c (insert (∃⁰ ∼χ) Γ)) :
    ∃ δ : ONote, δ.NF ∧ Cl H δ ∧ ZefProv δ E H (g ∘ f) c Γ := by
  obtain ⟨α₁, _, hNF₁, hH₁, d₁⟩ := D₁
  obtain ⟨γ₁, _, hNF₂, hH₂, d₂⟩ := D₂
  have fam : ∀ n (H' : ONote → Prop), Zef α₁ E H' (rel1 g n) c (insert (χ/[nm n]) Γ) := by
    intro n H'
    exact ((allInv_Zef n d₁ hg_mono (Finset.mem_insert_self _ _)).weakening
      (Finset.insert_subset_insert _ (Finset.erase_insert_subset _ _))).change_H
  have hred := cutReduceAllAuxRunning_Zf hχc hNF₁ hENF hg_mono hg_infl fam d₂ hNF₂ hf_mono hf_infl
    (Finset.mem_insert_self _ _)
  refine ⟨osucc (α₁ + γ₁), osucc_NF (ONote.add_nf α₁ γ₁),
    Cl_of_NF (osucc_NF (ONote.add_nf α₁ γ₁)), ?_⟩
  exact hred.weakening (Finset.union_subset (Finset.erase_insert_subset _ _) (Finset.Subset.refl Γ))

/-- **Seam-1 composition probe, slot form.**  The ∀/∃ arm at an ω-branch: the two premises'
slots `g` (∀-family) and `f` (∃-side) compose to `g ∘ f` on the output, at the fixed control `E`
(the raise/iteration live in `cutElimPass_Zf` alone).  A direct consequence of `stepAllω_Zf`;
seam 1 reverses in the slot form. -/
theorem probe_cut_all_arm_Zf {E : ONote} {H : ONote → Prop} {c : ℕ} {Γ : Finset (ArithmeticFormula ℕ)}
    {χ : ArithmeticSemiformula ℕ 1} {βφ βψ : ONote} {f g : ℕ → ℕ}
    (hENF : E.NF) (hχc : χ.complexity < c)
    (hg_mono : Monotone g) (hg_infl : ∀ x, x ≤ g x)
    (hf_mono : Monotone f) (hf_infl : ∀ x, x ≤ f x)
    (IH1 : ZefProv (expTower βφ) E H g c (insert (∀⁰ χ) Γ))
    (IH2 : ZefProv (expTower βψ) E H f c (insert (∃⁰ ∼χ) Γ)) :
    ∃ δ : ONote, δ.NF ∧ Cl H δ ∧ ZefProv δ E H (g ∘ f) c Γ :=
  stepAllω_Zf hENF hχc hg_mono hg_infl hf_mono hf_infl IH1 IH2

/-! ## Kernel-footprint attributes for the discharged reduction nodes

Both nodes are `clean` (real kernel footprint = trust base only), checked against
`Lean.collectAxioms`.  `cutElimPass_Zf` stays `notready` (`sorryAx`-bearing). -/

attribute [goodstein_blueprint 12 clean "zeh_reduction_pin1" "0" 100 cutReduceAllAuxRunning_Zf
  []
  ["compose the slot at a principal cut; [EW12, Lemma 25]",
   "running-family cut-reduction, output slot g∘f at fixed control; [Tow20, Theorem 19.6]",
   "Discharged in the Zef function-slot judgment; the ℕ-stage Zeh form was kernel-refuted (principal_witness_exceeds_stage)"]
  "Pin 1: the running-family cut-reduction, function-slot form (fixed control, output slot g∘f)."]
  cutReduceAllAuxRunning_Zf

attribute [goodstein_blueprint 13 clean "zeh_step_pin2" "0" 100 stepAllω_Zf
  []
  ["common-control ∀/∃ step; [EW12, Lemma 25]",
   "Q3-unified (one ⋁-principal reduction; the ∀-side enters via allInv_Zef)",
   "Discharged in the Zef function-slot judgment"]
  "Pin 2: the common-control ∀/∃ step motive, function-slot form (feeds pin 1 via allInv_Zef inversion)."]
  stepAllω_Zf

end GoodsteinPA.OperatorZeh
