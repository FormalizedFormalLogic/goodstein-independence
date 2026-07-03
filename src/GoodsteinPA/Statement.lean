/-
# The headline: PA does not prove Goodstein's theorem (Kirby–Paris)

**Designated audit surface.** This is the open target of the expedition. As of lap 166 it is a
**real proof** resting on the named-axiom blueprint (see the methodology note below), NOT a bare
`sorry`. Its only non-canonical dependency is the single, faithfully-stated Phase 2–3 girder
`goodstein_implies_consistency` (`Reduction.lean`); everything else — the Gödel-II contraposition
`not_proves_of_implies_consistency`, `peano_not_proves_consistency` — is axiom-clean.

**Named-axiom blueprint (the in-progress ledger discipline).** A `sorry`'d headline collapses all
outstanding debt to one opaque `sorryAx`. Instead, each not-yet-proven *milestone* is a NAMED
`axiom` carrying an honest, audited subgoal statement, and the headline is a real proof composing
them — so `#print axioms peano_not_proves_goodstein` reports EXACTLY which milestones remain. The
forcing function is unchanged: the result is *done* only when every blueprint axiom is discharged
(`axiom` → `theorem`) and the headline shows ONLY `[propext, Classical.choice, Quot.sound]`. The
named axiom is the *audit surface* — it gets more scrutiny than a hidden `sorry`, not less.

The in-progress green-gate is therefore `#print axioms`-based (allowlist = the 3 canonical axioms +
the declared blueprint axioms), enforced by `lean-axiom-gate` / the CI "Axiom-clean gate" step.
This supersedes the older "a custom `axiom` on the headline is smuggling" framing: a *faithful*,
*declared*, *allowlisted*, *intended-to-discharge* milestone axiom is the honest blueprint node; the
fraud it guards against is an *undeclared* / *off-allowlist* / *false* axiom, or `native_decide` /
vacuous restatement. See `DIRECTION.md` (ANTI-FRAUD guard) and the KB note `named-axiom-blueprint`.

⚠️ Anti-vacuity (unchanged): this headline is only meaningful because `goodsteinSentence`
(`Encoding.lean`) is the faithful encoding AND the bridge `(ℕ ⊨ goodsteinSentence) ↔
Goodstein-terminates` is proved (`Bridge.lean`, axiom-clean). Those faithfulness anchors are LOCKED.
-/
import GoodsteinPA.Reduction
import GoodsteinPA.BlueprintAttr
import GoodsteinPA.WainerBound

namespace GoodsteinPA

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment

/-- **Route-A body, banked.** The original summit proof via the Phase 2–3 consistency girder
(`goodstein_implies_consistency`, a declared blueprint `axiom`) + Gödel II. Kept under its own
name; the crown below now re-points to the route-B growth headline (SERIES-5 Lane B), which is
fully kernel-clean `[propext, Classical.choice, Quot.sound]`. -/
theorem peano_not_proves_goodstein_routeA : 𝗣𝗔 ⊬ ↑goodsteinSentence :=
  not_proves_of_implies_consistency goodstein_implies_consistency

/-- **Kirby–Paris (1982).** Peano Arithmetic does not prove that every Goodstein sequence
terminates. Re-points (SERIES-5 Lane B) to the route-B growth headline
`peano_not_proves_goodstein_growth` (Wainer bound vs Cichon/Caicedo), now discharged
axiom-clean; the literally-identical proposition `𝗣𝗔 ⊬ ↑goodsteinSentence`. The Route-A
consistency-girder body is banked above. Ledger: `#print axioms` ⇒
`[propext, Classical.choice, Quot.sound]`. -/
theorem peano_not_proves_goodstein : 𝗣𝗔 ⊬ ↑goodsteinSentence :=
  GoodsteinPA.WainerRoute.peano_not_proves_goodstein_growth

/- Blueprint ledger: the CROWN is a RE-POINT node — zero intrinsic laps by design. The summit
is currently proven through the banked Route-A wiring, so its machine-audited footprint carries
`goodstein_implies_consistency` (⇒ `debt`). All of its real work lives in its dependency chain
(the wainer ladder + the W7 native_decide burndown); when `routeB_headline` goes clean, the
summit flips green in ONE lap by re-pointing its body to `peano_not_proves_goodstein_growth`
(the literally identical proposition `𝗣𝗔 ⊬ ↑goodsteinSentence`). The Route-A body stays banked
under its own name. See `WAINER-LADDER-2026-07-02.md` rung C. -/
attribute [goodstein_blueprint 16 clean "pa_not_proves_goodstein" "0" 100 peano_not_proves_goodstein
  []
  ["WAINER-LADDER-2026-07-02.md rung C: crown re-point, unlocked by routeB_headline clean (ladder P/R/D/E/W + W7)",
   "Both headlines state the identical proposition; the rewire is `:= peano_not_proves_goodstein_growth`"]
  "Crown: the PA ⊬ Goodstein summit. Zero intrinsic work — re-points to the route-B headline when it goes clean; debt inherited from the banked Route-A axiom until then."]
  peano_not_proves_goodstein

end GoodsteinPA
