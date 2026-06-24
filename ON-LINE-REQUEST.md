# ON-LINE-REQUEST — offline literature/source gaps

A networked host session fulfills these: commit `ON-LINE-FINDINGS-<date>-<topic>.md`, delete the answered
item here, remove this file once nothing is open. The box is network-isolated (`WebFetch` 60s-timeouts).

---

## 2026-06-24 (lap 62) — Bryce–Goré Coq Gentzen formalization, for the C0.5 Foundation→Z bridge

**Source:** Bryce & Goré, *machine-checked `Con(PA)` via ordinal cut-elimination* — arXiv:2603.00487,
GitHub repo **`aarondroidbryce/Gentzen`** (Coq, ~18k lines; surfaced by the lap-61 judge,
`E-EQ5-ROUTE-FINDING-2026-06-23.md` Finding 2).

**What I need (in priority order):**
1. **`theories/Logic/Peano.v`** (~1,215 lines) — specifically the `PA_closed_PA_omega` simulation: how every
   PA axiom and inference rule is shown admissible in their proof system. This is the structural blueprint
   for **our C0.5 Foundation→Z bridge** (`(𝗣𝗔).DerivationOf d ⊥ → ∃ z, ZDerivesEmpty z`, M-internal). The
   bridge is the one unplanned load-bearing seam (judge Finding 3); their analogue is the precedent.
2. **The ordinal-assignment file(s)** (their `ord`/`degree` on derivations) + the **`cut_elim.v` reduction
   `R`** signature/structure — to cross-check our `iord`/`iR` (Buchholz-Z) per-rule arithmetic against an
   independent machine-checked source (faithfulness, not correctness — different statements).
3. The paper's **statement of the main theorem** + which ε₀-ordinal-notation library they build on
   (reportedly Castéran) — to confirm the route caveat (they use infinitary PA_ω, we use finitary Z).

**Why it unblocks:** C0.5 is ~1k-line scale; designing it from their blueprint instead of from scratch could
save weeks. **How to deliver:** the relevant `.v` files mirrored under `papers/bryce-gore-gentzen/` (or pasted
into a findings doc) — plain Coq source is readable offline. NB the route is PA_ω not Z, so port the *bridge
shape*, not line counts.

**Lower priority — `PA_delta1Definable`:** is the current Foundation pin's `PA_delta1Definable` still an
`axiom` (in `FirstOrder/Incompleteness/Examples.lean`), or has a later Foundation version proved it? It is now
a mandatory sub-task (operator: axiom-free or abandoned). If still an axiom upstream, note the file/line so a
future lap can scope the induction-scheme-Δ₁ arithmetization.
