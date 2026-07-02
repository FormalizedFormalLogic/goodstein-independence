/-
# `ZefCutElim` — feasibility probe for pin 3 (cut-ELIMINATION) in the slot calculus

Continues `wip/ZefSlotCalculus.lean` (reduction/inversion/step/read-off, all sorry-free).  The
next E–W step is cut-ELIMINATION (Lemma 26/27/30 — the collapse where the control raises and the
numeric slot ITERATES `f ↦ f^{…}`).  This is pin 3's territory; the pins' `∃ f'` conjunct is
kernel-vacuous (`normControlled_exists_trivial`), so the Q2 ruling requires `f'` PINNED to the E–W
iterate of the input slot.  **This file builds that iterate + the cut-elimination-pass skeleton,
localizing the remaining hard part (the ordinal-collapse bookkeeping) to disclosed `sorry`s** —
exactly as lap-2 localized the reduction to one gap.

`wip/` feasibility probe (off the live build); NOT a `src` pin-3 commit.  Determines the correct
pin-3 restatement (the lap-5 deliverable) with kernel evidence.  `lake env lean wip/ZefCutElim.lean`.
-/
import GoodsteinPA.OperatorZeh

namespace GoodsteinPA.OperatorZeh

open LO LO.FirstOrder ONote Ordinal
open GoodsteinPA.FastGrowing

/-! ## The numeric-slot ITERATE (E–W `f^{k}`, Def 16) — the carrier pin 3's `∃ f'` must be pinned to

`Function.iterate` (`f^[k]`) is the `k`-fold composition; these preserve exactly the operator
conditions the reduction threads (monotone, inflationary, `NormControlled`).  A cut-elimination
pass eliminating a chain of `k` top-rank cuts composes the slot `k` times — the output slot is
`f^[k]`, NOT a bare existential. -/

/-- The iterate is monotone if `f` is. -/
theorem iter_monotone {f : ℕ → ℕ} (hf : Monotone f) : ∀ k, Monotone f^[k]
  | 0 => monotone_id
  | k + 1 => by rw [Function.iterate_succ]; exact (iter_monotone hf k).comp hf

/-- The iterate is inflationary if `f` is. -/
theorem iter_infl {f : ℕ → ℕ} (hf : ∀ x, x ≤ f x) : ∀ k x, x ≤ f^[k] x
  | 0, x => le_rfl
  | k + 1, x => by
      rw [Function.iterate_succ']
      exact le_trans (iter_infl hf k x) (hf _)

/-- The iterate preserves `NormControlled` (for `k ≥ 1`): `f^[k+1] x ≥ f x ≥ hardy e (max m x)`,
via `f^[k]` inflationary. -/
theorem iter_normControlled {f : ℕ → ℕ} {e : ONote} {m : ℕ}
    (hf : NormControlled f e m) (hf_infl : ∀ x, x ≤ f x) (k : ℕ) :
    NormControlled f^[k + 1] e m := by
  intro x
  rw [Function.iterate_succ, Function.comp_apply]
  exact le_trans (hf x) (iter_infl hf_infl k (f x))

/-- Iterate monotone in the index count: `f^[j] ≤ f^[k]` pointwise for `j ≤ k`, `f` inflationary +
monotone (each extra composition only grows).  Feeds `mono_f` when a pass outputs a longer iterate
than a sibling branch needs (the `max`-of-counts reconciliation). -/
theorem iter_le_of_le {f : ℕ → ℕ} (hf_mono : Monotone f) (hf_infl : ∀ x, x ≤ f x)
    {j k : ℕ} (hjk : j ≤ k) : ∀ x, f^[j] x ≤ f^[k] x := by
  intro x
  obtain ⟨d, rfl⟩ := Nat.le.dest hjk
  rw [Function.iterate_add_apply]
  exact iter_monotone hf_mono j (iter_infl hf_infl d x)

/-- **Iterates compose to iterates** (`f^[j] ∘ f^[k] = f^[j+k]`) — the numeric core of the
cut-elimination pass: a `∃`-cut composes the two premises' slots (`g∘f`, `stepAllω_Zef`), and when
both are iterates of the SAME base `f` the composite is again an iterate.  So the slot stays
`f^[·]` under `∃`-cut composition — the count ADDS.  This is why pin 3's `f'` is a *pinned* iterate
(Q2), not a free slot: it is `f^[k]` for an explicit count `k`. -/
theorem iter_comp (f : ℕ → ℕ) (j k : ℕ) : f^[j] ∘ f^[k] = f^[j + k] :=
  (Function.iterate_add f j k).symm

/-! ## FINDING (this lap): pin 3's output slot is the ORDINAL-count iterate, not a free slot NOR a plain `f^[k]`

Attempting `cutElimPass : Zef α e H f (c+1) Γ → ∃ α' k, ZefProv α' e H f^[k] c Γ` (rank-lowering
by induction on the derivation, eliminating each top-rank `∃`-cut via `stepAllω_Zef`) reveals the
true shape, and where the ε₀ girder lives:

- **`∃`-cut / atomic / structural cases would thread** with the slot as a plain iterate `f^[k]`:
  a top-rank `∃`-cut turns premise slots `f^[k₁]`, `f^[k₂]` into `f^[k₁] ∘ f^[k₂] = f^[k₁+k₂]`
  (`iter_comp`) — the count ADDS, staying an iterate.  This confirms Q2: `f'` is a pinned iterate,
  NOT the vacuous free slot.

- **The `allω` node BREAKS the plain-`f^[k]` form.**  An `allω` has ℕ-many branches; cut-eliminating
  each yields a per-branch count `kₙ`, and there is NO finite `max kₙ` (the counts grow with the
  branch index — the same branch-unbounded numeric demand that killed the `(k,d)` calculus,
  SPIKE-W4B).  So the `allω` node's slot cannot be a single `f^[k]`; it must be the RELATIVIZED
  iterate `rel1 (f^[·]) n` with the count `kₙ` bounded by an ORDINAL function of the branch —
  exactly E–W Lemma 19 (`N(α) ≤ f^{F^α(0)}(0)`): the iterate index is `F^α(0)`, tying the numeric
  slot to the ORDINAL operator.  This is the "doubly operator-controlled" coupling (E–W §Conclusion).

**So pin 3's correct restatement (the lap-5 deliverable) is:**
`cutElimPass_Zf : Zef α e H f (c+1) Γ → ZefProv (collapse α) e H (f^[Fω α]) c Γ`
with `collapse α` the E–W ordinal collapse (Lemma 30, `F^α(0)`) and `Fω α` the matching
ordinal-indexed iterate count (Lemma 19/20) — NOT the draft's `∃ f'` (vacuous, Q2) and NOT a plain
`f^[k]` (breaks at `allω`).  The iterate infrastructure above (`iter_monotone`/`iter_infl`/
`iter_normControlled`/`iter_le_of_le`/`iter_comp`) is the numeric carrier this restatement needs;
the OPEN hard part is the ordinal-collapse arithmetic (`collapse`, `Fω`) — the ε₀ girder, E–W
Lemmas 19/20/26/27/30.  This localizes pin 3 exactly as lap-2 localized the reduction. -/

end GoodsteinPA.OperatorZeh
