import GoodsteinPA.OperatorZef2

/-!
# lap-10 SERIES-1 Stage-1 SEAM PROBE (R-0) — kernel-check the `α + γ` reduction seam

Per `REBUILD-Z-SERIES-1-ORDER-2026-07-02.md` Stage 1, R-0.  The judge (ruling §3, trap 9,
E–W Lemma 25) fixed the reduction's output ordinal at `α + γ` — NO `osucc`, NO `+1`.  This file
kernel-checks the three seams the pins-1–2 grind (Stage 2) will lean on, BEFORE any statement
grind consumes them.  All facts `#print axioms`-clean.

* **(i)** ONote `+` strict left-covariance on NF: `β < γ → α + β < α + γ` and `0 < γ → α < α + γ`.
  These make the reduction's premises (at `α + βⱼ`, `βⱼ < γ`) land STRICTLY below the fresh root
  `α + γ`, which is what every `Zef2` node's `hβ`/`hβφ`/`hβψ < α` demands.
* **(ii)** the composed-slot base gate: `ewN α ≤ g 0 → ewN γ ≤ f 0 → (∀ k, g 0 + k ≤ g k) →
  ewN (α + γ) ≤ g (f 0)`.  This is the `noOsucc_closes` pattern (lap-9) with the `+`-additive norm;
  it closes every fresh node's `hαN : ewN (α+γ) ≤ (g∘f) 0` gate.
* **(iii)** instance-complexity invariance + the fresh cut-read: `(φ/[nm n]).complexity =
  φ.complexity`, then `φ.complexity ≤ f 0 → f 0 ≤ g (f 0) → φ.complexity ≤ (g∘f) 0`, which closes
  the fresh `cut` node's `hcutRead`.

**T-S1**: any kernel failure here → halt lane P, escalate with this probe.  All three PASS.
-/

namespace GoodsteinPA.OperatorZeh

open ONote GoodsteinPA.OperatorZinfty GoodsteinPA.FastGrowing
open LO LO.FirstOrder

/-! ## (i) strict left-covariance of ONote `+` on normal forms -/

/-- `β < γ → α + β < α + γ` (NF) — this is exactly `OperatorZinfty.add_lt_add_left_NF`, restated
here to confirm it is in scope for the Zef2 grind. -/
theorem seam_add_lt_add_left {α β γ : ONote} (hαNF : α.NF) (hβNF : β.NF) (hγNF : γ.NF)
    (h : β < γ) : α + β < α + γ :=
  Zekd.add_lt_add_left_NF hαNF hβNF hγNF h

/-- `0 < γ → α < α + γ` (NF): the fresh root `α + γ` strictly dominates the `∀`-family base `α`. -/
theorem seam_lt_add_of_pos {α γ : ONote} (hαNF : α.NF) (hγNF : γ.NF) (h : 0 < γ) :
    α < α + γ := by
  haveI := hαNF; haveI := hγNF
  refine lt_def.mpr ?_
  rw [repr_add]
  have hγpos : (0 : Ordinal) < γ.repr := by
    have : (0 : ONote).repr < γ.repr := lt_def.mp h
    simpa using this
  simpa using (add_lt_add_iff_left α.repr).mpr hγpos

/-! ## (ii) the composed-slot base gate — the `noOsucc_closes` pattern over the `+`-additive norm -/

/-- **The base-additive gate** (R-0(ii)).  With the judge's `α + γ` output (no successor `+1`), the
banked sub-additivity `ewN_add_le` plus a per-step growth floor `g 0 + k ≤ g k` closes the fresh
node's composed-slot gate `ewN (α + γ) ≤ g (f 0)` from the two available input gates.  Promoted to
`src` (`ewN_add_le_comp`) as reusable Stage-2 content. -/
theorem seam_ewN_add_comp {α γ : ONote} {f g : ℕ → ℕ}
    (hα : ewN α ≤ g 0) (hγ : ewN γ ≤ f 0) (hg_base : ∀ k, g 0 + k ≤ g k) :
    ewN (α + γ) ≤ g (f 0) := by
  have hsub : ewN (α + γ) ≤ ewN α + ewN γ := ewN_add_le α γ
  have hbase : g 0 + f 0 ≤ g (f 0) := hg_base (f 0)
  omega

/-! ## (iii) instance-complexity invariance + the fresh cut-read gate -/

/-- `(φ/[nm n]).complexity = φ.complexity` — substituting a closed numeral leaves complexity fixed
(so `hφc : φ.complexity < c` and `hχRead : φ.complexity ≤ f 0` survive instantiation). -/
theorem seam_complexity_nm (φ : SyntacticSemiformula ℒₒᵣ 1) (n : ℕ) :
    (φ/[nm n]).complexity = φ.complexity := by simp

/-- The fresh `cut` node's read gate: from `φ.complexity ≤ f 0` and the base floor `f 0 ≤ g (f 0)`
(a consequence of `hg_infl`/`hg_base` on the `∀`-side slot), the composed-slot cut-read closes:
`φ.complexity ≤ (g ∘ f) 0`. -/
theorem seam_cutRead_comp {c₀ : ℕ} {f g : ℕ → ℕ}
    (hRead : c₀ ≤ f 0) (hg_infl : ∀ x, x ≤ g x) : c₀ ≤ (g ∘ f) 0 := by
  have : f 0 ≤ g (f 0) := hg_infl (f 0)
  simpa [Function.comp] using le_trans hRead this

end GoodsteinPA.OperatorZeh

-- Axiom audit (kernel-verified 2026-07-02, lap-10 SERIES-1 Stage-1 R-0 — T-S1 PASSES):
--   seam_add_lt_add_left  [propext, Classical.choice, Quot.sound]
--   seam_lt_add_of_pos    [propext, Classical.choice, Quot.sound]
--   seam_ewN_add_comp     [propext, Quot.sound]
--   seam_complexity_nm    [propext]
--   seam_cutRead_comp     [propext]
-- All three seams sorryAx-free: the judge's `α + γ` output discharges the reduction gates.
