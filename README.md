# Goodstein independence over PA

**Goal.** Formalize **Kirby--Paris (1982)**: Peano Arithmetic does *not* prove
Goodstein's theorem. In this repo's notation:

```lean
GoodsteinPA.Statement.peano_not_proves_goodstein : 𝗣𝗔 ⊬ ↑goodsteinSentence
```

where `goodsteinSentence` is the faithful arithmetic sentence "every Goodstein
sequence terminates."

## How this came to be

No grand plan:

1. I watched a YouTube video about Goodstein's theorem. Neat.
2. "Let's formalize it." Mathlib's 1000-theorems list wanted it, so someone was
   even asking.
3. "Wait, PA isn't strong enough to prove this? That's weird."
4. So formalize *that* too. The independence became the point, and the Goodstein
   process became the setup.
5. Having finished it, I am only very slightly wiser about *why* PA cannot prove
   Goodstein.

Step 5 is the honest one. Formalization gets sold as a route to understanding, and
I can't claim much of that here. What is here instead is an artifact you do not have
to take my word for: the axiom ledger below is machine-checked, and so is the bridge
that keeps the statement from being vacuous.

The work was AI-assisted, with Claude driving a Lean build loop. The axiom ledger and
the faithfulness anchor exist precisely because of that.

## Route: why growth-rate, not Gödel-II

**Decision, 2026-07-01: pivot to the Wainer/Cichon/Caicedo growth-rate route.**
This is the route that landed; the history below is why.

The previous active route tried to finish the headline through Foundation's Godel-II
surface:

```text
PA proves Goodstein -> PA proves Con(PA) -> contradiction by Godel II
```

That forced an IΣ₁-internalized Gentzen/cut-elimination bridge over coded
derivations. After the lap-167--171 M2 probe, the decisive PA-induction leaf exposed
a calculus-expressiveness gap: internal Z has numeral-only forall-left and no
free-variable forall-left/implication-left machinery for the required induction step.
That is not a local proof-engineering snag; it is the finitary-Z versus omega-rule
design fork.

The new mainline is the growth-rate proof:

```text
PA proves Goodstein
  -> the Goodstein length function is PA-provably total
  -> Wainer: every PA-provably-total recursive function is eventually dominated
     by some fast-growing f_alpha, alpha < epsilon_0
  -> Cichon/Caicedo: Goodstein length outgrows every fixed f_alpha below epsilon_0
  -> contradiction.
```

This does **not** make the proof-theoretic strength disappear. It isolates it in the
Wainer provably-total classification instead of spreading it through an internalized
cut-elimination engine. That is the right trade for this repo now: the local Lean
work becomes concrete ordinal/growth arithmetic, and the remaining proof-theory
dependency is a named, citable theorem.

## What is already built

- The Goodstein process itself is local and audited in `GoodsteinPA.Defs`.
- The first-order sentence is faithful:
  `GoodsteinPA.goodsteinSentence_faithful`.
- The growth substrate is substantial: `GoodsteinPA.Hardy`,
  `GoodsteinPA.Domination`, and `GoodsteinPA.LowerBound` prove the core
  Cichon/Caicedo lower-bound direction that Goodstein length eventually dominates
  every fixed fast-growing level below `epsilon_0`, up to the documented additive
  slack.
- `GoodsteinPA.WainerRoute` is now the route spine: it records the Wainer-route
  theorem, the machine-backed domination lemma already proved here, and the exact
  no-fixed-bound theorem needed to contradict a fixed Wainer upper bound.

## Status

**Proved, axiom-clean** (`#print axioms` verified 2026-07-16). The summit and the
anti-vacuity anchor each depend on exactly the three canonical axioms — `propext`,
`Classical.choice`, `Quot.sound` — and nothing else. No `sorry`, no blueprint axiom,
no `native_decide`:

- `GoodsteinPA.peano_not_proves_goodstein : 𝗣𝗔 ⊬ ↑goodsteinSentence`
- `GoodsteinPA.goodsteinSentence_faithful : (ℕ ⊧ₘ goodsteinSentence) ↔ ∀ m, ∃ N, goodsteinSeq m N = 0`

The second is what makes the first worth anything: it is the machine-checked promise
that the encoded sentence really does say "every Goodstein sequence terminates," so
the headline is not a clean proof of the wrong statement.

Both halves of the growth route are in Lean and proved:

- **Wainer classification, specialized** —
  `GoodsteinPA.WainerRoute.wainer_bound_of_pa_proves_goodstein`. If PA proves
  Goodstein, the Goodstein length function is eventually bounded by some `f_alpha`,
  `alpha < epsilon_0`.
- **Cichon/Caicedo, no fixed bound** —
  `GoodsteinPA.WainerRoute.cichon_caicedo_not_eventually_bounded_by_fixed_fastGrowing`.
  It follows from the Goodstein lower bound at `osucc alpha` plus the successor-level
  gap `f_alpha(n) + 2 < f_{osucc alpha}(n)` for large `n`.

Their contradiction is `GoodsteinPA.WainerRoute.peano_not_proves_goodstein_growth`,
which the headline re-points to.

Remaining work is infrastructure rather than mathematics. See
`ROUTE-DECISION-2026-07-01-WAINER.md` and `DIRECTION.md`.

## License

[Apache License 2.0](LICENSE), Copyright 2026 Trevor Morris
