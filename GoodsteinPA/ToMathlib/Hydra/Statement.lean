/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/

module

public import GoodsteinPA.ToMathlib.Hydra.Engine

@[expose] public section

/-
VENDORED from LeanGallery rev `a834bbad2f36eedcc16066b2bc4da49f98ab5b85`
(`LeanGallery/Logic/Hydra/`), verbatim except for the module-system header: this repo's root is a
`module`, and Lean 4.31 forbids a `module` from importing a non-`module`, so the gallery files
cannot be imported directly until the gallery migrates.  The namespace is kept as
`LeanGallery.Logic.Hydra` to record provenance and to keep the arc's `open` lines unchanged.
-/


/-!
# Kirby–Paris hydra: Hercules always wins — Kirby & Paris (1982)

**Designated audit surface** (with `Basic.lean`). The well-foundedness engine lives in
the sibling file; this statement delegates.

## What this says
A *battle* is a sequence of hydras `H 0, H 1, …` in which each `H (k + 1)` is obtained
from `H k` by one legal Kirby–Paris move (`Step`, see `Basic.lean`) at turn `turn k`,
for as long as the hydra is still alive. The theorem: every battle reaches the dead
hydra `leaf` in finitely many moves. Quantifying over **all** such sequences captures
"Hercules wins no matter which heads he chops"; letting `turn` be an arbitrary `ℕ → ℕ`
makes it independent of the regrowth schedule (the standard game, where turn `k` grafts
`k` copies, is the special case `turn k = k`).

## Proof (positive theorem, provable here)
Assign each hydra its Kirby–Paris ordinal `< ε₀` — the order-free natural sum
`♯ ωᵒ⁽ᶜ⁾` over children — realized as a recursive multiset (path) order `HLt` built on
mathlib's `Relation.CutExpand`. Every chop strictly lowers it (`step_hlt`), and `HLt`
is well-founded (`hlt_wf`, from `Relation.WellFounded.cutExpand` transported through the
tree). So no battle is infinite — `WellFounded.has_min` — and each finite one ends at
`leaf`. Verified axiom-clean: `#print axioms hydra_terminates` reports only
`[propext, Classical.choice, Quot.sound]`.

## Scope — POSITIVE theorem only
This is the Kirby–Paris hydra *termination* theorem (true; provable in ZFC, hence
trivially in Lean's stronger logic). The **independence result** — that Peano
Arithmetic cannot prove it (Kirby & Paris 1982, the ε₀ proof-theoretic strength of the
game) — is a *metamathematical* statement about PA, proved in `GoodsteinPA.HydraIndependence`.
-/

namespace LeanGallery.Logic.Hydra

open Hydra

/-- **Kirby–Paris hydra termination ("Hercules always wins").** For every battle — any
sequence of hydras in which each step is a legal move at its turn while the hydra is
alive — the hydra is dead (`leaf`) after finitely many moves, no matter how the heads
are chosen and no matter how fast it regrows. (The well-founded-descent proof lives in
`Engine.lean`; this is the thin, faithful audit statement.) -/
theorem hydra_terminates {H : ℕ → Hydra} {turn : ℕ → ℕ}
    (hstep : ∀ k, H k ≠ leaf → Step (turn k) (H k) (H (k + 1))) :
    ∃ N, H N = leaf :=
  hydra_terminates_engine hstep

/-- **Hercules wins** — alias for `hydra_terminates`. -/
theorem hercules_wins {H : ℕ → Hydra} {turn : ℕ → ℕ}
    (hstep : ∀ k, H k ≠ leaf → Step (turn k) (H k) (H (k + 1))) :
    ∃ N, H N = leaf :=
  hydra_terminates hstep

end LeanGallery.Logic.Hydra

end
