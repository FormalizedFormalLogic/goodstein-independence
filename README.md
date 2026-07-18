**DISCLAIMER**: This repository contains a large number of AI/LLM-generated proofs, and still under review by FFL. Whether this formalization is successful remains an open question within FFL.

# Goodstein independence over PA

**Goal.** Formalize **Kirby--Paris (1982)**: Peano Arithmetic does *not* prove
Goodstein's theorem. In this repo's notation:

```lean
GoodsteinPA.Statement.peano_not_proves_goodstein : 𝗣𝗔 ⊬ ↑goodsteinSentence
```

where `goodsteinSentence` is the faithful arithmetic sentence "every Goodstein
sequence terminates." The proof is
[`src/GoodsteinPA/Statement.lean`](src/GoodsteinPA/Statement.lean) — the headline
theorem and this repo's designated audit surface.

## How this came to be

This is an AI-assisted formalization: Claude (via Claude Code) drove a Lean build
loop against a hand-written [blueprint](#blueprint--docs). The full, honest account
of how the project came about is in
[`docs/how-this-came-to-be.md`](docs/how-this-came-to-be.md).

The axiom ledger ([Status](#status)) and the faithfulness anchor are machine-checked
precisely because the work was AI-assisted: they are what let a reader trust the
result without trusting the process that produced it.

## Blueprint & docs

The proof was guided by a **dependency blueprint** — a prose-plus-graph sketch of the
argument, with each node linked to the Lean declaration that discharges it. It uses
[`leanblueprint`](https://github.com/PatrickMassot/leanblueprint), the same tooling
behind the [Fermat's Last Theorem](https://imperialcollegelondon.github.io/FLT/) and
[Prime Number Theorem](https://alexkontorovich.github.io/PrimeNumberTheoremAnd/)
projects.

- **Rendered blueprint + API docs**: https://gotrevor.github.io/goodstein-independence/
  — the dependency graph and prose at
  [`/blueprint/`](https://gotrevor.github.io/goodstein-independence/blueprint/), and the
  doc-gen4 Lean API reference at
  [`/docs/`](https://gotrevor.github.io/goodstein-independence/docs/).
- **Blueprint source**: [`blueprint/`](blueprint), rebuilt on push by
  [`.github/workflows/docs.yml`](.github/workflows/docs.yml). Each node's status is
  machine-synced from the `@[goodstein_blueprint]` attributes in the Lean source by
  [`blueprint/annotate_depgraph.py`](blueprint/annotate_depgraph.py), so the graph
  cannot silently drift from what actually compiles.

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

The mathematics is complete. Route history and planning notes are archived under
[`archive/`](archive) — the growth-rate pivot is recorded in
[`archive/routes/ROUTE-DECISION-2026-07-01-WAINER.md`](archive/routes/ROUTE-DECISION-2026-07-01-WAINER.md).

## License

[Apache License 2.0](LICENSE), Copyright 2026 Trevor Morris
