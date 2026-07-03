import GoodsteinPA.OperatorZef2

/-!
# D-3 probe (Series-3) — rung-D vacuity: evidence + the any-rank corollary

The spine-head machinery (`spineHead`, `zef2_rank0_uniform_spine_underivable`,
`zef2_rank0_singleton_ex_underivable`) was promoted to `src/GoodsteinPA/OperatorZef2.lean` as
the load-bearing proof of the R-4′-restated `readoff_delta0_Zef2`.  This probe keeps the
evidence record + the any-rank corollary (E-0 ruling input).

## Why the ORDERED route (aux at the `ewIter` bound) was NOT taken

The Series-3 order's D-3 plan — "re-prove `readoffD_aux` at the achievable bound; the trapped
case closes via `ewIter_lower` aggregation" — hits the lap-195 `k₀` wall unchanged: the false
branch index `k₀` of an `allω` node is SEMANTIC (least false instance of the matrix), not
controlled by any gate.  Adversary (prose, general-Γ aux invariant): matrix `χ = (x < N)`,
`Γ₀ = {∃⁰ φ, ∼(φ/[nm N])} ∪ {∼(χ/[nm i]) : i < N}` with `φ = (x = N)`, slot `f = ·+1`, `α = 2`:
branches `n < N` close by the `axL` pair `(χ/[nm n], ∼(χ/[nm n]))`, branches `n ≥ N` by `exI`
at witness `N ≤ f n` then the pair `(φ/[nm N], ∼(φ/[nm N]))`; the dichotomy hypothesis holds,
yet the sole true `φ`-instance is `N ≫ ewIter f 2 0`.  So the aux-invariant-at-`ewIter`-bound
is FALSE for general contexts — no structural aggregation exists.  What saves the RUNG is that
such adversarial contexts can never descend from the SINGLETON root `{∃⁰ φ}`: all members of
any sequent reachable from a singleton share one spine head, so no `axL` pair ever forms and
the source derivation itself cannot exist (the src vacuity theorem).

## Any-rank corollary

With rungs P+R real (Series-3 N-2), rank-`d` singleton derivations map to rank-0 ones, so
`Zef2` cannot derive `{∃⁰ φ}` at ANY rank (under the rung-R side conditions).  Decisive E-0
input: the rung-E embedding cannot target `Zef2` even with cuts — its leaves need E–W's (Ax2)
true-literal closure (`Zef2T`), exactly as the Stage-B probe predicted (B(iii)).
-/

namespace GoodsteinPA.OperatorZeh

open LO LO.FirstOrder ONote Ordinal
open GoodsteinPA.FastGrowing
open GoodsteinPA.OperatorZinfty

/-- **Any-rank vacuity**: composing rung R (`rankToZero_Zef2`, real since N-2) with the rank-0
singleton underivability, `Zef2` cannot derive `{∃⁰ φ}` at ANY cut rank `d` (under rung R's
side conditions).  The embedding must target `Zef2T`. -/
theorem zef2_singleton_ex_underivable_anyRank {φ : SyntacticSemiformula ℒₒᵣ 1}
    {α e : ONote} {H : ONote → Prop} {d : ℕ} (f : ℕ → ℕ)
    (heNF : e.NF) (hαNF : α.NF) (hαH : Cl H α) (hf1 : EwF1 f) (hf2 : EwF2 f) :
    ¬ Zef2 α e H f d {(∃⁰ φ)} := by
  intro D
  obtain ⟨α', _, _, _, _, D0⟩ := rankToZero_Zef2 f heNF hαNF hαH D hf1 hf2
  exact zef2_rank0_singleton_ex_underivable D0

end GoodsteinPA.OperatorZeh
