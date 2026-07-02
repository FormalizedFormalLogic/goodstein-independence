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

/-- `ewN (collapse α) = ewN α + 1` (`collapse α = oadd α 1 0`). -/
theorem ewN_collapse (α : ONote) : ewN (collapse α) = ewN α + 1 := by
  simp [collapse, expTower, ewN]

/-- **Per-node gate for the pass** — the rebuilt node at `collapse α` with slot `ewIter f α` needs
gate `ewN (collapse α) ≤ (ewIter f α) 0`.  From the input derivation's base gate `ewN α ≤ f 0` +
`EwF1 f`: `ewN (collapse α) = ewN α + 1`, and `ewIter f α 0 ≥ f (f 0) ≥ 2·f 0 + 1 ≥ ewN α + 1`
(the `f(f 0)` floor via `ewIter_lower` at `0 < α`; `EwF1` at the base for `α = 0`). -/
theorem ewN_collapse_le {f : ℕ → ℕ} (hf1 : EwF1 f) {α : ONote} (hgate : ewN α ≤ f 0) :
    ewN (collapse α) ≤ ewIter f α 0 := by
  rw [ewN_collapse]
  by_cases hα : α = 0
  · subst hα
    simp only [ewN_zero, ewIter_zero]
    have := hf1.2 0; omega
  · have h0α : (0 : ONote) < α := by
      cases α with
      | zero => exact (hα rfl).elim
      | oadd e n a => exact oadd_pos e n a
    have hgate0 : ewN (0 : ONote) ≤ f (ewN α + 0) := Nat.zero_le _
    have hlow := ewIter_lower (f := f) (β := 0) (α := α) (m := 0) h0α hgate0
    have hff : f (f 0) ≤ ewIter f α 0 := by simpa [ewIter_zero] using hlow
    have hb : 2 * f 0 + 1 ≤ f (f 0) := hf1.2 (f 0)
    have : ewN α + 1 ≤ f (f 0) := by omega
    exact le_trans this hff

end GoodsteinPA.OperatorZeh
