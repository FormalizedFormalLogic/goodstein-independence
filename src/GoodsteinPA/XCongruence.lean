/-
# `XCongruence.lean` — the X-congruence discharge (INTEGRATED into `EmbeddingX`/`EmbeddingBound`, lap-32)

**Status.** The lap-31 deliverables of this file — the per-numeral X-congruence Tait matrix and its
cut-free `PXFc` derivation — have been **promoted** into the embedding machinery and *wired into
`paLX`*. They now live where the axiom-discharge needs them:

- `GoodsteinPA.EmbeddingX.litTrue_eq_iff`, `relExtBody`, `relExt_Xsym_eq`, `relExtBody_subst_eq`,
  `pxfc_relExtMatrix`, `pxfc_relExt_Xsym` — the base lemmas + the **unbounded** discharge.
- `GoodsteinPA.EmbeddingBound.pxfc_relExt_Xsym_bdd`, `relExt_bound_lt_epsilon0` — the **bounded**
  (`< ε₀`, uniform-over-`e`) discharge used by `peano_not_proves_TI`.

**What changed (lap-32, Task A1 complete).** `paLX` now carries the single equality axiom
`Theory.Eq.relExt Xsym` (X-congruence `∀ x y, x = y → X(x) → X(y)`), so that `𝗘𝗤 ⪯ paLX` can hold
(every other `𝗘𝗤(LX)` axiom is an `lMap Φ`-image of an `𝗘𝗤(ℒₒᵣ)` axiom already provable from
`lMap Φ 𝗣𝗔⁻ ⊆ paLX`). Both axiom discharges (`EmbeddingX.hax_paLX`, `EmbeddingBound.hax_paLX_bdd`)
gained the new `heq` branch closing X-congruence into the `PXFc`/`XFreeAx` `Z∞` carrier at a finite,
`e`-independent ordinal — so `peano_not_proves_TI` re-validates with the larger axiom set (the cut-rank
bound is unchanged; the embedded ordinal only gains a finite contribution).

This module is retained as the design record; the live lemmas are the ones above.
-/
import GoodsteinPA.EmbeddingBound

namespace GoodsteinPA.XCongruence

end GoodsteinPA.XCongruence
