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

/-- **Slot-composition containment** — the pass's cut-elimination step merges two IH-reduced
premises' slots `ewIter f α₀ ∘ ewIter f α₁` (`α₀,α₁ < α`) and must fit under the declared output
`ewIter f α`.  Proof: pick δ = the larger of α₀,α₁ (< α); lift both iterates to δ by gated
ordinal-monotonicity (`ewIter_le_of_lt`), giving the two-fold `ewIter f δ (ewIter f δ m)`; then
`ewIter_lower` at δ < α collapses the two-fold to one-fold `ewIter f α m`.  All ball gates follow
from the base gates `ewN αᵢ ≤ f 0` + `f 0 ≤ f _` (monotone).  This CLOSES the slot side of the cut
step — no `EwF1`-of-`rel1` needed. -/
theorem ewIter_comp_le {f : ℕ → ℕ} (hf_mono : Monotone f) (hf_infl : ∀ m, m ≤ f m)
    {α₀ α₁ α : ONote} (hα₀ : α₀.NF) (hα₁ : α₁.NF)
    (h0 : α₀ < α) (h1 : α₁ < α) (g0 : ewN α₀ ≤ f 0) (g1 : ewN α₁ ≤ f 0) (m : ℕ) :
    ewIter f α₀ (ewIter f α₁ m) ≤ ewIter f α m := by
  haveI := hα₀; haveI := hα₁
  -- ball gates from base gates + monotonicity
  have gate0 : ∀ k, ewN α₀ ≤ f (ewN α + k) := fun k => le_trans g0 (hf_mono (Nat.zero_le _))
  have gate1 : ∀ k, ewN α₁ ≤ f (ewN α + k) := fun k => le_trans g1 (hf_mono (Nat.zero_le _))
  rcases lt_trichotomy α₀.repr α₁.repr with hlt | heq | hgt
  · -- α₀ < α₁ ; δ = α₁
    have hα₀α₁ : α₀ < α₁ := lt_def.mpr hlt
    have g01 : ∀ k, ewN α₀ ≤ f (ewN α₁ + k) := fun k => le_trans g0 (hf_mono (Nat.zero_le _))
    have step1 : ewIter f α₀ (ewIter f α₁ m) ≤ ewIter f α₁ (ewIter f α₁ m) :=
      ewIter_le_of_lt hf_infl hα₀α₁ (g01 _)
    exact le_trans step1 (ewIter_lower h1 (gate1 m))
  · -- α₀ = α₁ ; δ = α₀ = α₁
    have hαeq : α₀ = α₁ := repr_inj.mp heq
    subst hαeq
    exact ewIter_lower h0 (gate0 m)
  · -- α₁ < α₀ ; δ = α₀
    have hα₁α₀ : α₁ < α₀ := lt_def.mpr hgt
    have g10 : ewN α₁ ≤ f (ewN α₀ + m) := le_trans g1 (hf_mono (Nat.zero_le _))
    have hinner : ewIter f α₁ m ≤ ewIter f α₀ m := ewIter_le_of_lt hf_infl hα₁α₀ g10
    have step1 : ewIter f α₀ (ewIter f α₁ m) ≤ ewIter f α₀ (ewIter f α₀ m) :=
      ewIter_monotone hf_mono hf_infl α₀ hinner
    exact le_trans step1 (ewIter_lower h0 (gate0 m))

end GoodsteinPA.OperatorZeh
