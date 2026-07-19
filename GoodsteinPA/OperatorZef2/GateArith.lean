module

public import GoodsteinPA.OperatorZeh

@[expose] public section

namespace GoodsteinPA.OperatorZeh

open LO LO.FirstOrder ONote Ordinal
open GoodsteinPA.OperatorZinfty

variable {α γ βφ βψ : ONote} {f g : ℕ → ℕ}

/-! ## `ewN` arithmetic — the size norm is sub-additive under `+` and near-additive under `osucc`

These are the size-control facts the reduction's synthesized `osucc (α + γ)` roots need: the gate
`ewN (osucc (α + γ)) ≤ ewN α + ewN γ + 1`.  Unconditional for `+`, needs `NF` for `osucc`. -/

/-- `ewN` is sub-additive over `addAux`. -/
theorem ewN_addAux_le (e : ONote) (n : ℕ+) (o : ONote) :
    ewN (addAux e n o) ≤ ewN e + (n : ℕ) + ewN o := by
  unfold addAux
  cases o with
  | zero => simp [ewN]
  | oadd e' n' a' =>
      simp only
      cases h : ONote.cmp e e' with
      | lt => simp only [ewN_oadd]; omega
      | eq =>
          have he : e = e' := eq_of_cmp_eq h
          subst he
          simp only [ewN_oadd, PNat.add_coe]; omega
      | gt => simp only [ewN_oadd]; omega

/-- `ewN` is sub-additive over ordinal addition (unconditional). -/
theorem ewN_add_le : ∀ (a o : ONote), ewN (a + o) ≤ ewN a + ewN o := by
  intro a
  induction a with
  | zero => intro o; simp [ewN]
  | oadd e n b ihe ih =>
      intro o
      rw [oadd_add]
      refine le_trans (ewN_addAux_le e n (b + o)) ?_
      have := ih o
      simp only [ewN_oadd]; omega

/-- `ewN` grows by at most one under the notation successor (for normal forms). -/
theorem ewN_osucc_le : ∀ {o : ONote}, o.NF → ewN (osucc o) ≤ ewN o + 1
  | 0, _ => by simp [osucc, ewN]
  | oadd 0 n a, h => by
      have ha0 : a = 0 := by
        have hlt : a.repr < ω ^ (0 : ONote).repr := h.snd'.repr_lt
        rw [repr_zero, opow_zero] at hlt
        exact (@repr_inj a 0 h.snd NF.zero).1 (by rw [repr_zero]; exact Order.lt_one_iff.1 hlt)
      subst ha0
      show ewN (oadd 0 (n + 1) 0) ≤ ewN (oadd 0 n 0) + 1
      simp only [ewN_oadd, ewN_zero, PNat.add_coe, PNat.one_coe]; omega
  | oadd (oadd e' n' a') m b, h => by
      show ewN (oadd (oadd e' n' a') m (osucc b)) ≤ ewN (oadd (oadd e' n' a') m b) + 1
      have hIH := ewN_osucc_le h.snd
      simp only [ewN_oadd] at hIH ⊢; omega

/-- The composite the reduction roots need: `ewN (osucc (α + γ)) ≤ ewN α + ewN γ + 1`. -/
theorem ewN_osucc_add_le (hαNF : α.NF) (hγNF : γ.NF) :
    ewN (osucc (α + γ)) ≤ ewN α + ewN γ + 1 := by
  refine le_trans (ewN_osucc_le (ONote.add_nf α γ)) ?_
  have := ewN_add_le α γ
  omega

/-- **The composed-slot base gate** — the `α + γ` output gate.
`ewN α ≤ g 0`, `ewN γ ≤ f 0`, and the `∀`-side per-step floor `g 0 + k ≤ g k` close the fresh
node's gate `ewN (α + γ) ≤ (g ∘ f) 0 = g (f 0)`. -/
theorem ewN_add_le_comp
    (hα : ewN α ≤ g 0) (hγ : ewN γ ≤ f 0) (hg_base : ∀ k, g 0 + k ≤ g k) :
    ewN (α + γ) ≤ g (f 0) :=
  le_trans (ewN_add_le α γ) (base_add_le_comp hg_base hα hγ)

/-! ## The pass's ordinal-collapse containment -/

/-- `repr (collapse x) = ω ^ repr x` (`collapse = expTower = oadd · 1 0`). -/
theorem repr_collapse (x : ONote) : (collapse x).repr = ω ^ x.repr := by
  simp [collapse, expTower, ONote.repr]

/-- **Ordinal-collapse containment** — the cut-elimination step feeds two
IH-reduced premises (at `collapse βφ`, `collapse βψ`, `βφ,βψ < α`) into the running-family
cut-reduction (`cutReduceAllAuxRunning_Zf2`), whose additive output `collapse βφ + collapse βψ`
must fit strictly under the single collapse `collapse α = ω^α`.  This is the additive principality
of `ω^α`. -/
theorem collapse_add_lt (hβφ : βφ.NF) (hβψ : βψ.NF) (_hα : α.NF)
    (hφ : βφ < α) (hψ : βψ < α) : collapse βφ + collapse βψ < collapse α := by
  haveI := hβφ; haveI := hβψ; haveI := _hα
  haveI := collapse_NF hβφ; haveI := collapse_NF hβψ; haveI := collapse_NF _hα
  haveI := ONote.add_nf (collapse βφ) (collapse βψ)
  refine lt_def.mpr ?_
  rw [repr_add, repr_collapse, repr_collapse, repr_collapse]
  have hφr : (ω : Ordinal) ^ βφ.repr < ω ^ α.repr :=
    (opow_lt_opow_iff_right one_lt_omega0).2 (lt_def.mp hφ)
  have hψr : (ω : Ordinal) ^ βψ.repr < ω ^ α.repr :=
    (opow_lt_opow_iff_right one_lt_omega0).2 (lt_def.mp hψ)
  exact (Ordinal.isPrincipal_add_omega0_opow α.repr) hφr hψr

/-- `ewN (collapse α) = ewN α + 1` (`collapse α = oadd α 1 0`). -/
theorem ewN_collapse (α : ONote) : ewN (collapse α) = ewN α + 1 := by
  simp [collapse, expTower, ewN]

/-- **Per-node gate for the pass** — the rebuilt node at `collapse α` with slot `ewIter f α` needs
gate `ewN (collapse α) ≤ (ewIter f α) 0`.  From the derivation's base gate `ewN α ≤ f 0` + the
`2m+1 ≤ f m` LOWER bound (`hlow`): `ewN (collapse α) = ewN α + 1`, and `ewIter f α 0 ≥ f (f 0) ≥
2·f 0 + 1 ≥ ewN α + 1` (the `f(f 0)` floor via `ewIter_lower` at `0 < α`; `hlow` at the base for
`α = 0`).  Crucially uses only `hlow`, NOT strict monotonicity — so it survives the pass's `allω`
branches where the slot is `rel1 f n` (which preserves `hlow` via `rel1_low` but breaks
strictness). -/
theorem ewN_collapse_le (hlow : ∀ m, 2 * m + 1 ≤ f m)
    (hgate : ewN α ≤ f 0) : ewN (collapse α) ≤ ewIter f α 0 := by
  rw [ewN_collapse]
  by_cases hα : α = 0
  · subst hα
    simp only [ewN_zero, ewIter_zero]
    have := hlow 0; omega
  · have h0α : (0 : ONote) < α := by
      cases α with
      | zero => exact (hα rfl).elim
      | oadd e n a => exact oadd_pos e n a
    have hlow' := ewIter_lower (f := f) (β := 0) (α := α) (m := 0) NF.zero h0α (Nat.zero_le _)
    have hff : f (f 0) ≤ ewIter f α 0 := by simpa [ewIter_zero] using hlow'
    have hb : 2 * f 0 + 1 ≤ f (f 0) := hlow (f 0)
    exact le_trans (by omega : ewN α + 1 ≤ f (f 0)) hff

/-- `Nlog (collapse α) = Nlog α + 1` (`collapse α = oadd α 1 0`, `clog 1 = 1`) — the `Nlog`
analog of `ewN_collapse`. -/
theorem Nlog_collapse (α : ONote) : Nlog (collapse α) = Nlog α + 1 := by
  show Nlog (oadd α 1 0) = Nlog α + 1
  have hc : clog 1 = 1 := by decide
  simp [Nlog_oadd, hc]

/-- **Per-node gate for the pass over `Nlog`** — the analog of `ewN_collapse_le`: the rebuilt
node at `collapse α` with slot `ewIter f α` closes its `Nlog` gate from the derivation's base
gate `Nlog α ≤ f 0` + the EwLow floor.  Same `f (f 0)` mechanism; only `hlow`, no strictness,
so it survives the `allω` branches' `rel1 f n` slots. -/
theorem Nlog_collapse_le (hlow : ∀ m, 2 * m + 1 ≤ f m)
    (hgate : Nlog α ≤ f 0) : Nlog (collapse α) ≤ ewIter f α 0 := by
  rw [Nlog_collapse]
  by_cases hα : α = 0
  · subst hα
    simp only [Nlog_zero, ewIter_zero]
    have := hlow 0; omega
  · have h0α : (0 : ONote) < α := by
      cases α with
      | zero => exact (hα rfl).elim
      | oadd e n a => exact oadd_pos e n a
    have hlow' := ewIter_lower (f := f) (β := 0) (α := α) (m := 0) NF.zero h0α (Nat.zero_le _)
    have hff : f (f 0) ≤ ewIter f α 0 := by simpa [ewIter_zero] using hlow'
    have hb : 2 * f 0 + 1 ≤ f (f 0) := hlow (f 0)
    omega

end GoodsteinPA.OperatorZeh
