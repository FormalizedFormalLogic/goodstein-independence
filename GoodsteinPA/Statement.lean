/-
# The headline: PA does not prove Goodstein's theorem (Kirby–Paris)

**Designated audit surface.** The summit of the expedition. It is now a **kernel-clean proof**:
the crown re-points to the route-B growth headline `peano_not_proves_goodstein_growth` (the Wainer
bound vs Cichon/Caicedo), whose footprint is exactly `[propext, Classical.choice, Quot.sound]` (no
`sorry`, no blueprint axiom, no `native_decide`/`ofReduceBool`). Confirm with
`#print axioms peano_not_proves_goodstein`. (An earlier, still-incomplete Con(𝗣𝗔)/Gödel-II route —
resting on the open `goodstein_implies_consistency` girder — is banked in `Reduction.lean` as
`peano_not_proves_goodstein_routeA`, off the clean summit.)

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
module

public import GoodsteinPA.Reduction
public import GoodsteinPA.BlueprintAttr
public import GoodsteinPA.WainerBound

@[expose] public section

namespace GoodsteinPA

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment

/-- **Kirby–Paris (1982).** Peano Arithmetic does not prove that every Goodstein sequence
terminates. Re-points (SERIES-5 Lane B) to the route-B growth headline
`peano_not_proves_goodstein_growth` (Wainer bound vs Cichon/Caicedo), now discharged
axiom-clean; the literally-identical proposition `𝗣𝗔 ⊬ ↑goodsteinSentence`. The earlier Route-A
consistency-girder body is banked in `Reduction.lean`. Ledger: `#print axioms` ⇒
`[propext, Classical.choice, Quot.sound]`. -/
theorem peano_not_proves_goodstein : 𝗣𝗔 ⊬ ↑goodsteinSentence :=
  GoodsteinPA.WainerRoute.peano_not_proves_goodstein_growth

/- Blueprint ledger: the CROWN is a RE-POINT node with zero intrinsic laps by design. The re-point
has LANDED (SERIES-5 Lane B): the summit body is `peano_not_proves_goodstein_growth`, whose route-B
chain (the wainer ladder + the W7 native_decide burndown, since discharged kernel-only) is
axiom-clean, so the summit's machine-audited footprint is `[propext, Classical.choice, Quot.sound]`
(⇒ `clean`). The Route-A consistency-girder body stays banked in `Reduction.lean` as `peano_not_proves_goodstein_routeA`.
See `WAINER-LADDER-2026-07-02.md` rung C. -/
attribute [goodstein_blueprint 16 clean "pa_not_proves_goodstein" "0" 100 peano_not_proves_goodstein
  []
  ["WAINER-LADDER-2026-07-02.md rung C: crown re-point, unlocked by routeB_headline clean (ladder P/R/D/E/W + W7)",
   "Both headlines state the identical proposition; the rewire is `:= peano_not_proves_goodstein_growth`"]
  "Crown: the PA ⊬ Goodstein summit. Zero intrinsic work: re-points to the route-B growth headline, now discharged kernel-clean; footprint [propext, Classical.choice, Quot.sound]. The Route-A consistency-girder body is banked in Reduction.lean as peano_not_proves_goodstein_routeA."]
  peano_not_proves_goodstein

end GoodsteinPA

/- Axiom ledger: the summit's footprint (and every other headline's) is pinned by a GUARDED
`#print axioms` in `scripts/AxiomCheck.lean` — the enforced point of truth. A bare `#print axioms`
here would only *log* (a `sorryAx`/new-axiom regression would still build green) and spam every
compile, so the audit lives in that one guarded file instead. Expected everywhere, enforced there:
`[propext, Classical.choice, Quot.sound]`. -/
