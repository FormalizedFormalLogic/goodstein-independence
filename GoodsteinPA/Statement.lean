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
`scripts/AxiomCheck.lean`, the enforced point of truth.

⚠️ Anti-vacuity: this headline is only meaningful because `goodsteinSentence` (`Encoding.lean`)
is the faithful encoding AND the bridge `(ℕ ⊨ goodsteinSentence) ↔ Goodstein-terminates` is
proved (`goodsteinSentence_faithful`, `Encoding.lean`, axiom-clean). Those faithfulness anchors
are LOCKED.
-/
module

public import GoodsteinPA.E1EmbeddingGrind
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

/-- **Kirby–Paris (1982).** Peano Arithmetic does not prove that every Goodstein sequence
terminates. If PA proved Goodstein, Wainer would put the Goodstein length below a fixed `f_o`
(`wainer_bound_of_pa_proves_goodstein`); Cichon/Caicedo says no fixed `f_o` bounds it
(`Goodstein.cichon_caicedo_not_eventually_bounded_by_fixed_fastGrowing`). Ledger:
`#print axioms` ⇒ `[propext, Classical.choice, Quot.sound]`. -/
theorem peano_not_proves_goodstein : 𝗣𝗔 ⊬ ↑goodsteinSentence := by
  intro hpa
  obtain ⟨o, ho, hbound⟩ := wainer_bound_of_pa_proves_goodstein hpa
  exact cichon_caicedo_not_eventually_bounded_by_fixed_fastGrowing o ho hbound

/-- PA cannot refute the Goodstein sentence either: `ℕ` satisfies `goodsteinSentence`
(every genuine Goodstein sequence terminates) and PA is sound with respect to `ℕ`, so no
proof of the negation exists. -/
theorem peano_not_proves_not_goodstein : 𝗣𝗔 ⊬ ∼↑goodsteinSentence := by
  apply unprovable_of_countermodel 𝗣𝗔 (M := ℕ);
  simp only [Semantics.NotModels, Semantics.Not.models_not, not_not];
  apply goodsteinSentence_faithful.mpr;
  exact Dom.goodstein_terminates;

/-- **Independence.** Goodstein's theorem is independent of Peano Arithmetic: PA proves
neither `goodsteinSentence` nor its negation. -/
theorem goodstein_independent : Independent 𝗣𝗔 goodsteinSentence := ⟨
  peano_not_proves_goodstein,
  peano_not_proves_not_goodstein
⟩

end GoodsteinPA
