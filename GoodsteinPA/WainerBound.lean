/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import GoodsteinPA.WainerRoute
import GoodsteinPA.E1EmbeddingGrind
import GoodsteinPA.ReadoffValueGate
import GoodsteinPA.HardyMajorization

/-!
# Wainer bound — the discharged route-B growth axiom (SERIES-4, judge pass 2026-07-03)

`WainerRoute.wainer_bound_of_pa_proves_goodstein` was the sole route-B axiom. It is discharged
HERE into a theorem, by applying `E1EmbeddingGrind.wainer_bound_witness` to its three
hypothesis-theorems:

* `ReadoffValueGate.gated_certificate_uniform`  (`Hcert`)
* `HardyMajorization.Scirc_dom_pad`             (`HSdom`)
* `HardyMajorization.master_conversion`         (`Hconv`)

This is a verified **copy-not-compose** splice: each hypothesis type in `wainer_bound_witness` is
the *verbatim* statement of the corresponding theorem (checked at the judge pass), so the four
names apply directly with zero adaptation.

The module lives DOWNSTREAM of the embedding chain (`E1EmbeddingGrind` imports `WainerRoute`),
so the discharged theorem — and the route-B headline that consumes it — live here, not in
`WainerRoute`, to break the `E1EmbeddingGrind → WainerRoute` import cycle. The theorem's type is
byte-identical to the former axiom's type (the designated audit surface).
-/

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open ONote GoodsteinPA.FastGrowing

namespace GoodsteinPA.WainerRoute

/-- **Wainer classification, specialized to this route.** Formerly the sole route-B axiom
`wainer_bound_of_pa_proves_goodstein`; now a theorem, discharged via the
embedding → pass → rank-0 → Δ₀ value read-off → Hardy-majorization ladder. The type is the
verbatim former-axiom type. -/
theorem wainer_bound_of_pa_proves_goodstein :
    (𝗣𝗔 ⊢ ↑goodsteinSentence) ->
      ∃ o : ONote, o.NF ∧ EventuallyLE GoodsteinPA.Dom.goodsteinLength (fun n => fastGrowing o n) :=
  -- SERIES-5 Lane A splice (Gated-duplication snag resolved: E1EmbeddingGrind now imports
  -- ReadoffValueGate and shares the single canonical `Gated`, so `Hcert` unifies with
  -- `gated_certificate_uniform`). Copy-not-compose: the three hypothesis types are the verbatim
  -- statements of the three theorems.
  fun h => E1EmbeddingGrind.wainer_bound_witness
    ReadoffValueGate.gated_certificate_uniform
    HardyMajorization.Scirc_dom_pad HardyMajorization.master_conversion h

attribute [goodstein_blueprint 14 clean "wainer_axiom" "0" 100 wainer_bound_of_pa_proves_goodstein
  []
  ["SERIES-4 (laps 209-212 + judge pass 2026-07-03): discharged axiom -> theorem. Lane S built wainer_bound_witness at the axiom's VERBATIM type (kernel-clean [propext,choice,Quot.sound]); the three hypotheses gated_certificate_uniform (RVG) / Scirc_dom_pad + master_conversion (HM) are all kernel-clean; the judge pass promoted the three wip modules into src and spliced.",
   "Splice = wainer_bound_witness gated_certificate_uniform Scirc_dom_pad master_conversion h (copy-not-compose; the hypothesis types are the theorem statements verbatim)."]
  "The specialized Wainer classification, discharged by the wainer ladder over the Z^e operator calculus (embed -> pass -> rank-0 -> Delta_0 read-off -> splice)."]
  wainer_bound_of_pa_proves_goodstein

/-- **Kirby--Paris via Wainer/Cichon/Caicedo** (route-B headline). If PA proved Goodstein, Wainer
would put the Goodstein length below a fixed `f_o`; Cichon/Caicedo says no fixed `f_o` bounds it. -/
theorem peano_not_proves_goodstein_growth : 𝗣𝗔 ⊬ ↑goodsteinSentence := by
  intro hpa
  obtain ⟨o, ho, hbound⟩ := wainer_bound_of_pa_proves_goodstein hpa
  exact cichon_caicedo_not_eventually_bounded_by_fixed_fastGrowing o ho hbound

attribute [goodstein_blueprint 15 clean "routeB_headline" "0" 100 peano_not_proves_goodstein_growth
  []
  ["Route-B independence headline: PA ⊬ Goodstein from Wainer's fixed-f_o bound vs Cichon/Caicedo no-fixed-bound. Assembly (intro; obtain from wainer_bound; exact cichon_caicedo) over the now-discharged wainer_bound_of_pa_proves_goodstein."]
  "Route-B independence headline: PA ⊬ Goodstein via growth rates; clean once the Wainer bound landed."]
  peano_not_proves_goodstein_growth

end GoodsteinPA.WainerRoute
