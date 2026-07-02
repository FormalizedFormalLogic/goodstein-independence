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

/-- **Gated ordinal-monotonicity of `ewIter`** — the fact trap-8 refuted for the bare `iterSlot`
but which the ewN GATE restores for `ewIter`.  For `β < α` with the ball gate
`ewN β ≤ f (ewN α + m)`, the smaller-ordinal iterate is dominated by the larger:
`ewIter f β m ≤ ewIter f α m`.  Two lines: inflate once, then `ewIter_lower`.  THIS is what
un-walls the pass's slot side (the cut-elim step composes iterates at DIFFERENT ordinals). -/
theorem ewIter_le_of_lt {f : ℕ → ℕ} (hf_infl : ∀ m, m ≤ f m) {β α : ONote} {m : ℕ}
    (hβα : β < α) (hgate : ewN β ≤ f (ewN α + m)) :
    ewIter f β m ≤ ewIter f α m :=
  le_trans (ewIter_infl hf_infl β (ewIter f β m)) (ewIter_lower hβα hgate)

end GoodsteinPA.OperatorZeh
