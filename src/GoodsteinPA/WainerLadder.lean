/-
# Wainer ladder — the splice rung, homed at the concrete goodstein translation

This module is the **L-E-direction home** (Series-1 ruling §4) for the Wainer ladder's
top rungs, the ones whose faithful statement must bind the concrete `𝗣𝗔`-goodstein
translation.  It imports the `Zef2` slot calculus (`OperatorZef2`) *and* the translation
apparatus (`WainerRoute`: `EventuallyLE`, `goodsteinSentence`, `GoodsteinPA.Dom.goodsteinLength`,
`fastGrowing`), so the rung-W statement can be stated at its ratified, non-parametric shape
instead of the parametric placeholder that lived in `OperatorZef2.lean` (voided as the
lap-8-ruling L-W trivial shape, R-5 debt).

Rung E (the embedding) is NOT yet homed here as a src theorem: its faithful statement (source
hypothesis `𝗣𝗔 ⊢ ↑goodsteinSentence`, target `Γ_G` bound to the concrete goodstein translation)
is the Stage-B rung-E statement lap — it stays a `wip/Ax2AdequacyProbe.lean` draft (docstring
text only) until the judge ratifies it.  See `REBUILD-Z-SERIES-2-ORDER-2026-07-03.md` Stage B.

TODO(rung E, Stage-B statement lap): once the judge ratifies the W3-K-hypothesis shape re-based
onto `Zef2` (or `Zef2T`), add `embedding_Zef2 : (𝗣𝗔 ⊢ ↑goodsteinSentence) → ∃ …, Zef2 α e H
(ewRootSlot e B) d Γ_G` here with `Γ_G` bound to the concrete translation.  The old parametric
`embedding_Zef2` (over an abstract `Γ_G`) was DELETED from `OperatorZef2.lean` per R-6.
-/
import GoodsteinPA.OperatorZef2
import GoodsteinPA.WainerRoute
import GoodsteinPA.WainerBound

namespace GoodsteinPA.WainerLadder

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open ONote GoodsteinPA.FastGrowing
open GoodsteinPA.WainerRoute

/-- **RUNG W (L-W) `wainer_splice_Zef2`** — the splice: compose rung E → R → D and convert the
exit witness bound to the `hardy`/`fastGrowing` vocabulary via the banked Hardy Lemma-19
brackets, producing exactly the statement of the `wainer_bound_of_pa_proves_goodstein` axiom.
This is the rung that flips that axiom from `axiom` to `theorem`.

Restated VERBATIM at the Series-1 order R-5 shape (non-parametric, homed at the concrete
goodstein translation): from a PA proof of the goodstein sentence, produce a single fixed
fast-growing `f_o`, `o.NF`, eventually dominating `goodsteinLength`.

**SERIES-5 Lane C: DISCHARGED.** The splice is now realized — this rung's statement is byte-identical
to `WainerRoute.wainer_bound_of_pa_proves_goodstein`, which was discharged (axiom → theorem) via the
`embed → pass → rank-0 → Δ₀ value read-off → Hardy-majorization` ladder. Re-points to it. -/
theorem wainer_splice_Zef2 :
    (𝗣𝗔 ⊢ ↑goodsteinSentence) →
      ∃ o : ONote, o.NF ∧
        EventuallyLE GoodsteinPA.Dom.goodsteinLength (fun n => fastGrowing o n) :=
  GoodsteinPA.WainerRoute.wainer_bound_of_pa_proves_goodstein

end GoodsteinPA.WainerLadder
