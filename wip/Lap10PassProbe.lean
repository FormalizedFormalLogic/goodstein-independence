import GoodsteinPA.OperatorZef2

/-!
# lap-10 SERIES-1 Stage-3 PASS PROBE — the cut-elimination step's ordinal + slot containments

The cut-elimination pass `cutElimPass_Zef2` eliminates a top-rank cut by feeding the two IH-reduced
premises (rank-`c` at `collapse βφ`, `collapse βψ`, `βφ,βψ < α`) into the reduction pin
`stepAllω_Zf2`, which outputs ordinal `≤ collapse βφ + collapse βψ` and slot
`ewIter f βφ ∘ ewIter f βψ`.  Both must fit under the pass's declared output `collapse α = ω^α` /
`ewIter f α`.  This file kernel-checks the two decisive containments BEFORE the pass grind commits.

* **`expTower_add_lt`** (ordinal side) — `βφ,βψ < α → ω^βφ + ω^βψ < ω^α`, i.e. the reduction's
  additive output stays strictly below the single collapse.  Pure additive principality of `ω^α`.
-/

namespace GoodsteinPA.OperatorZeh

open ONote Ordinal
open LO LO.FirstOrder
open GoodsteinPA.OperatorZinfty GoodsteinPA.FastGrowing

/-- `repr (expTower x) = ω ^ repr x`. -/
theorem repr_expTower (x : ONote) : (expTower x).repr = ω ^ x.repr := by
  simp [expTower, ONote.repr]

/-- **Ordinal-collapse containment.**  For `βφ, βψ < α` (NF), the reduction pin's additive output
`collapse βφ + collapse βψ` stays strictly below the single collapse `collapse α = ω^α` — the
additive principality of `ω^α`.  Feeds the pass's `Zef2Prov.mono` down to `collapse α`. -/
theorem expTower_add_lt {βφ βψ α : ONote} (hβφ : βφ.NF) (hβψ : βψ.NF) (hα : α.NF)
    (hφ : βφ < α) (hψ : βψ < α) : expTower βφ + expTower βψ < expTower α := by
  haveI := hβφ; haveI := hβψ; haveI := hα
  haveI := expTower_NF hβφ; haveI := expTower_NF hβψ; haveI := expTower_NF hα
  haveI := ONote.add_nf (expTower βφ) (expTower βψ)
  refine lt_def.mpr ?_
  rw [repr_add, repr_expTower, repr_expTower, repr_expTower]
  have hφr : (ω : Ordinal) ^ βφ.repr < ω ^ α.repr :=
    (opow_lt_opow_iff_right one_lt_omega0).2 (lt_def.mp hφ)
  have hψr : (ω : Ordinal) ^ βψ.repr < ω ^ α.repr :=
    (opow_lt_opow_iff_right one_lt_omega0).2 (lt_def.mp hψ)
  exact (Ordinal.isPrincipal_add_omega0_opow α.repr) hφr hψr

/-! ## Pass induction skeleton probe — the generalized-`f` helper (Monotone+infl threading) -/

/-- Skeleton probe: the pass as a Monotone+infl-threaded induction (NOT EwF1 on the slot, since
`allω` branches carry `rel1 f n` which doesn't preserve strictness).  Establishes the motive +
case tags compile; cases are disclosed sub-goals. -/
theorem passAux_skel (c : ℕ) {e : ONote} (heNF : e.NF) :
    ∀ {α : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {Γ : Seq} {r : ℕ},
      Zef2 α e H f r Γ → r = c + 1 → Monotone f → (∀ x, x ≤ f x) → (∀ m, 2 * m + 1 ≤ f m) →
      α.NF → Cl H α →
      Zef2Prov (collapse α) e H (ewIter f α) c Γ := by
  intro α H f Γ r D
  induction D with
  | @axL α e H f r Γ ar hαN rel v hp hn =>
      intro hr hmono hinfl hlow hαNF hαH
      have hg := ewN_collapse_le hlow hαN
      exact Zef2Prov.of (collapse_NF hαNF) (Cl_of_NF (collapse_NF hαNF)) hg
        (Zef2.axL hg rel v hp hn)
  | @wk α e H f r Δ Γ hαN hsub D' ih =>
      intro hr hmono hinfl hlow hαNF hαH
      exact (ih heNF hr hmono hinfl hlow hαNF hαH).weakening hsub
  | @weak α β e H f r Δ Γ hαN hβ hβNF hαNF' hβH hsub D' ih =>
      intro hr hmono hinfl hlow hαNF hαH
      obtain ⟨a, hale, haNF, haH, hag, Da⟩ := ih heNF hr hmono hinfl hlow hβNF (Cl_of_NF hβNF)
      have hslot := ewIter_slot_le hmono hinfl hβ (Zef2.gate D')
      exact ⟨a, le_trans hale (le_of_lt (collapse_strictMono hβNF hβ)), haNF, haH,
        le_trans hag (hslot 0), (Da.mono_f hslot).wk (le_trans hag (hslot 0)) hsub⟩
  | @allω α e H f r Γ hαN χ β hβ hβNF hαNF' hβH dd ih =>
      intro hr hmono hinfl hlow hαNF hαH; sorry
  | @exI α β e H f r Γ hαN χ n hβ hβNF hαNF' hβH hbound dχ ih =>
      intro hr hmono hinfl hlow hαNF hαH; sorry
  | @cut α βφ βψ e H f r Γ hαN χ hcompl hcutRead hβφ hβψ hβφNF hβψNF hαNF' hβφH hβψH d₁ d₂ ih₁ ih₂ =>
      intro hr hmono hinfl hlow hαNF hαH; sorry

end GoodsteinPA.OperatorZeh
