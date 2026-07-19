/-
# The headline: PA does not prove Goodstein's theorem (Kirby–Paris)

**Designated audit surface.** The crown `peano_not_proves_goodstein` is a kernel-clean proof
via the growth route:

  PA proves Goodstein
    → the Goodstein length function is PA-provably total
    → Wainer: it is then eventually bounded by a fixed fast-growing `f_o`, `o < ε₀`
      (`wainer_bound_of_pa_proves_goodstein`, discharged through the embedding → pass →
      rank-0 → Δ₀ value read-off → Hardy-majorization ladder)
    → Cichon/Caicedo: no fixed `f_o` eventually bounds the Goodstein length
      (`Goodstein.cichon_caicedo_not_eventually_bounded_by_fixed_fastGrowing`)
    → contradiction.

Footprint: `[propext, Classical.choice, Quot.sound]` (no `sorry`, no blueprint axiom, no
`native_decide`/`ofReduceBool`) — pinned by the guarded `#print axioms` in
`scripts/AxiomCheck.lean`, the enforced point of truth. (An earlier, still-incomplete
Con(𝗣𝗔)/Gödel-II route — resting on the open `goodstein_implies_consistency` girder — is
banked in `Reduction.lean` as `peano_not_proves_goodstein_routeA`, off the clean summit.)

⚠️ Anti-vacuity: this headline is only meaningful because `goodsteinSentence` (`Encoding.lean`)
is the faithful encoding AND the bridge `(ℕ ⊨ goodsteinSentence) ↔ Goodstein-terminates` is
proved (`wip/Bridge.lean`, axiom-clean). Those faithfulness anchors are LOCKED.
-/
module

public import GoodsteinPA.Reduction
public import GoodsteinPA.BlueprintAttr
public import GoodsteinPA.ToMathlib.Goodstein.CichonCaicedo
public import GoodsteinPA.E1EmbeddingGrind
public import GoodsteinPA.ReadoffValueGate
public import GoodsteinPA.ToMathlib.Hardy.Majorization

@[expose] public section

namespace GoodsteinPA

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open ONote
open Goodstein

/-- **Wainer classification, specialized to this route.** If PA proves the Goodstein sentence,
the Goodstein length function is eventually bounded by a fixed fast-growing `f_o`, `o < ε₀`.
Formerly the sole route axiom; discharged via the embedding → pass → rank-0 → Δ₀ value
read-off → Hardy-majorization ladder. -/
theorem wainer_bound_of_pa_proves_goodstein :
    (𝗣𝗔 ⊢ ↑goodsteinSentence) ->
      ∃ o : ONote, o.NF ∧ EventuallyLE Goodstein.Dom.goodsteinLength (fun n => fastGrowing o n) :=
  -- Copy-not-compose splice: each hypothesis type of `wainer_bound_witness` is the verbatim
  -- statement of the corresponding theorem, so the three names apply with zero adaptation.
  fun h => E1EmbeddingGrind.wainer_bound_witness
    ReadoffValueGate.gated_certificate_uniform
    Scirc_dom_pad master_conversion h

attribute [goodstein_blueprint 14 clean "wainer_axiom" "0" 100 wainer_bound_of_pa_proves_goodstein
  []
  ["Discharged axiom → theorem: wainer_bound_witness applied at the axiom's verbatim type; the three hypotheses gated_certificate_uniform (ReadoffValueGate) / Scirc_dom_pad + master_conversion (Hardy majorization) are all kernel-clean."]
  "The specialized Wainer classification, discharged by the wainer ladder over the Z^e operator calculus (embed → pass → rank-0 → Δ₀ read-off → splice)."]
  wainer_bound_of_pa_proves_goodstein

/-- **Kirby–Paris (1982).** Peano Arithmetic does not prove that every Goodstein sequence
terminates. If PA proved Goodstein, Wainer would put the Goodstein length below a fixed `f_o`
(`wainer_bound_of_pa_proves_goodstein`); Cichon/Caicedo says no fixed `f_o` bounds it
(`Goodstein.cichon_caicedo_not_eventually_bounded_by_fixed_fastGrowing`). The earlier Route-A
consistency-girder body is banked in `Reduction.lean`. Ledger: `#print axioms` ⇒
`[propext, Classical.choice, Quot.sound]`. -/
theorem peano_not_proves_goodstein : 𝗣𝗔 ⊬ ↑goodsteinSentence := by
  intro hpa
  obtain ⟨o, ho, hbound⟩ := wainer_bound_of_pa_proves_goodstein hpa
  exact cichon_caicedo_not_eventually_bounded_by_fixed_fastGrowing o ho hbound

attribute [goodstein_blueprint 16 clean "pa_not_proves_goodstein" "0" 100 peano_not_proves_goodstein
  []
  ["Crown: PA ⊬ Goodstein assembled from the discharged Wainer bound vs the Cichon/Caicedo no-fixed-bound theorem."]
  "Crown: the PA ⊬ Goodstein summit, proved from wainer_bound_of_pa_proves_goodstein and Goodstein.cichon_caicedo_not_eventually_bounded_by_fixed_fastGrowing; footprint [propext, Classical.choice, Quot.sound]. The Route-A consistency-girder body is banked in Reduction.lean as peano_not_proves_goodstein_routeA."]
  peano_not_proves_goodstein

end GoodsteinPA
