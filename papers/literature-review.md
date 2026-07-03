# Literature review — what the on-disk corpus says about the routes

> **What this is, and how it differs from `SOURCES.md`.** `SOURCES.md` is the flat *catalog* (one entry
> per PDF). This file is the route-oriented *synthesis* on top of it: what the corpus **collectively** says
> about the documented proofs of `PA ⊬ Goodstein` — which sources back each route, what is already
> *precedented* (in any prover) vs what must be *originated*, and what is missing from the literature.
>
> **It is deliberately AGNOSTIC about the current plan.** It maps what the literature says; it does NOT
> pick a route, track the project's live state, or carry confidence numbers. The directional calls — which
> route we're on, current finishability, what to do next — live in `DIRECTION.md` / `ROUTE-ESCALATION-*` /
> the reflection synthesis, and turn over fast; this map changes only when the *literature* does.
>
> The deep reflection lap reads this to re-ground its route/feasibility judgments in the actual sources
> instead of accumulated handoff optimism. **Infinitary proof theory is exactly where an LLM confabulates
> a plausible-but-wrong argument — quote the source (the per-PDF `.md` summaries are the record), don't
> reconstruct it. And challenge THIS file too — it is a past lap's read of the literature, not ground
> truth; verify against the sources.** Update it when new reading (or a returned `ON-LINE-FINDINGS-*`)
> changes the map. Last updated: 2026-07-03 (lap 206 — E–W witnessing-mechanism note added to Route B).

## The question the corpus answers
`PA ⊬ Goodstein` is documented textbook math (Kirby–Paris 1982) that has **never been formalized in any
prover** (mathlib: a listed-but-unclaimed `1000.yaml` target; Isabelle/Coq have Goodstein *termination*,
not the *independence*). A Lean proof is net-new whichever route is taken. The corpus maps: of the
documented proofs of this one theorem, what does each route need, and how much is already precedented
somewhere?

## The routes the literature offers, and which sources back each

### Route A — proof-theoretic ( Gentzen: `γ → PRWO(ε₀) → Con(PA)` → Gödel II )
Girder is `TI(ε₀) ⊢ Con(PA)` (PA∞ / ω-rule, ordinal assignment `< ε₀`, ε₀-bounded cut-elimination). When
routed through Gödel II it must be carried out **PA-internally over coded derivations**.
- **Construction sources:** `buchholz-beweistheorie-lecture-notes.md` (German; cleanest end-to-end PA∞ +
  ε₀-cut-elim ⟹ Con(PA)) and `buchholz-on-gentzens-first-consistency-proof.md` (the reduction-procedure
  form + the `o(d)=ω_{dg(d)}(õ(d))` ordinal assignment).
- **Modern expositions:** `freund-unprovability-first-course-...md` (most accessible on-ramp tying PA + ε₀
  + cut-elim + Gödel II), `buss-handbook-ch2-...md` (the most on-target textbook chapter),
  `buss-handbook-ch1-...md` (finitary cut-elim engine), `rathjen-2006-art-of-ordinal-analysis.md` (field
  map), `freund-second-course-...md` (deeper).
- **Route entry point:** `rathjen-2014-goodsteins-theorem-revisited.md` (the `γ → PRWO(ε₀)` link).
- **Cross-check / fallback mechanism (not a drop-in):** `siders-...md` independently fingers the hard nut
  (contraction on the cut formula) + a Howard vector-assignment descent — but it is a 26-slide deck
  targeting intuitionistic HA.
- **Method-exemplar one storey too high:** `arai-lectures-on-ordinal-analysis.md` is KPω-and-above; ε₀
  only as scaffolding.
- **Precedent in a prover:** **Bryce–Goré (arXiv:2603.00487, Coq `Con(PA)`, on disk at
  `scratchpad/Gentzen-bg/`, not a `papers/` PDF)** machine-checked `Con(PA)` — but **META** (over ordinary
  Coq types, via infinitary PA_ω), *not* the IΣ₁-internalized-over-codes version. So it establishes that
  *meta* ordinal-analysis-in-a-prover is feasible; the *internalization* (coded-derivation arithmetization)
  is **unprecedented in any prover**.

### Route B — growth-rate / fast-growing ( `Goodstein ~ H_{ε₀}` outgrows all PA-provably-total functions )
Reaches `PA ⊬ γ` **meta-level** — no internal-`Con`, no Gödel II, no Foundation→Z bridge, no
coded-derivation arithmetization.
- **Route, stated:** `cichon-1983-short-proof-independence.md` (independence via Hardy hierarchies) +
  `towsner-...md` (Goodstein ↔ well-foundedness of ε₀ ↔ what PA can't prove) +
  `caicedo-goodstein-function-notes.md` / `agboola(=Sladek)-...md` (the Goodstein-length ↔ ordinal closed
  form + the Kreisel/Kirby–Paris domination chain).
- **Substrate precedent (Coq, axiom-free):** `casteran-hydra-battles-in-coq.md` — the ε₀ CNF notation,
  well-foundedness, fundamental sequences `{α}(n)`, the **Hardy `H_α`** and **Wainer `F_α`** hierarchies +
  KS81 domination lemmas are all **fully formalized**. A bounded (non-research) Lean port; hits the known
  Lean WF-recursion guard-checker friction. Isabelle cross-check: `nested-multisets-...-isabelle...md`
  (ε₀ as hereditary multisets + a machine-checked Goodstein *sequence*).
- **The Wainer upper bound** (every PA-provably-recursive function is `H_{<ε₀}`-dominated) — Castéran builds
  the hierarchies but leaves this classification as future work; it is **un-formalized anywhere** (still the
  monument). ✅ **The source, however, is no longer a gap (2026-07-01):** its canonical statement + proof is
  on disk, open, in **Buchholz–Wainer 1987** (`buchholz-wainer-1987-...`) and the **Wainer 2013 Stanford
  slides** — superseding the paywalled Fairtlough–Wainer ch. III. ⚠️ Reading them confirms the upper bound's
  proof is **PA ↪ ω-rule system + cut-elimination + ordinal assignment `<ε₀`** — i.e. the classification
  route's capstone **is the ε₀ girder**, not an alternative to it. So "port not invent" (Castéran) covers
  only the *lower* bound (already done: `goodsteinLength_dominates_fastGrowing`); the upper bound must be
  originated and is Bryce–Goré-scale.

- **Mechanism note (2026-07-03, from `eguchi-weiermann-2012-operator-controlled-id1.md` §4–5;
  relevant to ANY function-slot re-implementation of the witnessing read-off):** E–W's calculus
  carries the numeric content in the CONTROL the whole way down — the embedding relativizes the
  numeric operator by numeral *values* (Lemma 33 `f[m+k]`; Lemma 34 "the numeral's value enters the
  f-relativization"), the ⋀/ω-rule relativizes each branch to `f[N(ι)]`, and rule side conditions
  (`N(ι₀) ≤ f(0)`, `N(max k^Π(A)) ≤ f(0)`) gate every index that the terminal Witnessing Lemma 31
  must descend through. Consequently their Thm-37 exit bound is an **α-indexed iterate**
  `∃n ≤ s^α(m₀+⋯+m_{l-1})` absorbing the relativization tower — NOT a constant `f(0)`. A
  re-implementation whose ω-rule does *not* gate branch indices (e.g. a bare `allω` over all of ℕ)
  will hit a "standard-false ∀ with true 0-instance" trap at the read-off: the false-branch index
  is bounded only by the *semantic term values* of the principal formula, so the gate must be
  reconstructed semantically (subformula closure from the read-off's root + bounded-quantifier
  value gate + a value-budget iterate as the exit bound), or built into the rules as E–W do.

### Route C — model-theoretic ( Kirby–Paris original: nonstandard models + indicators )
- **Source:** `kirby-paris-1982-accessible-independence.md` — the *original* proof, via nonstandard models
  of PA, indicators, and Ketonen–Solovay. Avoids cut-elimination entirely, but its substrate (model theory
  of arithmetic, indicators) is **also absent from Lean / mathlib** and has no prover precedent on disk.

## Cross-cutting observations (neutral facts, not a recommendation)
- **All three routes are type-3** (originate a Lean formalization of known math); none is pure assembly —
  the ordinal analysis of PA exists in no Lean library (EXPEDITION-PLAN, day one).
- **The routes differ in PRECEDENT SHAPE.** Route A's girder (internalized cut-elim over codes) is
  unprecedented in any prover; a *meta* version is precedented (Bryce–Goré, Coq). Route B's girder (Wainer
  classification) is also un-formalized, but is meta and sits on a *tested Coq substrate* (Castéran). Route
  C's substrate has no prover precedent on disk. (Stated as what exists, not as a verdict — the route call
  lives in `DIRECTION.md`.)
- **Reusable substrate already in a prover:** the ε₀/Hardy/Wainer machinery (Castéran, Coq) and ε₀ ordinals
  (Blanchette et al., Isabelle) are the cross-prover references to port intuition from for any route that
  needs the ordinal-notation / growth-hierarchy layer.

## Provenance caveats (do not over-trust — also flagged in `SOURCES.md`)
- `agboola-termite-and-tower-goodstein.pdf` is **Sladek (2007)**, not Agboola (filename is a misnomer).
- `siders-...pdf` is a **26-slide deck**, not a paper — do not cite lemmas from it.
- `arai-...pdf` is **KPω-tier**, not an ε₀-girder working source.
- `nested-multisets-...` is **Blanchette–Fleury–Traytel**, not Felgenhauer (the separate `Goodstein_Lambda`
  AFP entry).
- **Bryce–Goré is NOT in `papers/`** — it is the Coq clone at `scratchpad/Gentzen-bg/`; it is PA_ω
  (infinitary), the wrong vehicle for a finitary primrec-PRWO route — cite it as a feasibility witness +
  `Peano.v` bridge blueprint, not as the cut-elim method.

## Known literature gaps (candidate `ON-LINE-REQUEST`s)
- ~~**Fairtlough–Wainer** "Hierarchies of provably recursive functions" (Handbook ch. III) — paywalled.~~
  ✅ **RESOLVED 2026-07-01** — the Wainer-classification capstone is now on disk, open, via **Buchholz–Wainer
  1987** + **Wainer 2013 slides**. No longer an `ON-LINE-REQUEST` candidate.
- **Gentzen 1936/1938/1943** originals — paywalled; content reconstructed in Buchholz/Buss (sufficient).
- **Pohlers / Schütte / Takeuti** textbooks — paywalled; the modern PA∞ + ε₀ cut-elim references.
