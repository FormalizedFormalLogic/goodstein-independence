/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import GoodsteinPA.Statement
import GoodsteinPA.Reduction
import GoodsteinPA.Bridge
import GoodsteinPA.Domination

/-!
# Axiom audit — the reference point of truth

`#print axioms` for every headline theorem, each wrapped in `#guard_msgs` asserting the EXACT
expected axiom set: the standard mathlib triple `[propext, Classical.choice, Quot.sound]` — no
`sorry` (`sorryAx`), no custom/blueprint axiom, no `native_decide`/`ofReduceBool`.

Why guard instead of a bare `#print axioms`? A bare print only emits an `info` message — a `sorryAx`
or new-axiom regression would still build **green** and nobody would notice. `#guard_msgs` turns the
audit into an assertion: any drift (a new axiom, a `sorry`, or a renamed/removed theorem) makes THIS
FILE fail to elaborate. On success the guards consume their messages, so a clean run is **silent**:

    lake env lean scripts/AxiomCheck.lean   # no output + exit 0 = all clean

CI (`.github/workflows/ci.yml`, the build job's axiom-clean gate) runs exactly that and gates on the
exit code. This is the single source of truth for the headline set — no count to bump, renames caught
automatically. `whitespace := lax` tolerates the pretty-printer wrapping a long qualified name.
-/

-- The summit: `𝗣𝗔 ⊬ ↑goodsteinSentence` (Kirby–Paris), re-pointed to the axiom-clean route-B headline.
/-- info: 'GoodsteinPA.peano_not_proves_goodstein' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GoodsteinPA.peano_not_proves_goodstein

-- Consistency corollary: `𝗣𝗔 ⊬ ↑𝗣𝗔.consistent`.
/-- info: 'GoodsteinPA.peano_not_proves_consistency' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GoodsteinPA.peano_not_proves_consistency

-- ℕ-level truth companion: every Goodstein sequence terminates (the true statement PA cannot prove).
/-- info: 'GoodsteinPA.Dom.goodstein_terminates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GoodsteinPA.Dom.goodstein_terminates

-- Anti-vacuity anchor: the encoding is faithful (`ℕ ⊨ goodsteinSentence ↔ Goodstein terminates`).
/-- info: 'GoodsteinPA.goodsteinSentence_faithful' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GoodsteinPA.goodsteinSentence_faithful
