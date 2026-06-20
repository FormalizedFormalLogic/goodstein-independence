# Goodstein independence over PA (expedition)

**Goal.** Formalize **Kirby–Paris (1982)**: Peano Arithmetic does *not* prove Goodstein's
theorem. `𝐏𝐀 ⊬ γ`, where `γ` is the arithmetic sentence "every Goodstein sequence
terminates."

**Status: PLANNING / not built.** This repo currently holds the design only
(`EXPEDITION-PLAN.md`). The proof is a genuine research-formalization milestone — to our
knowledge no prover has it — and it is explicitly **not** an overnight / autonomous-treadmill
job (see the plan for why: the load-bearing piece, the *ordinal analysis of PA*, exists in no
Lean library and must be originated).

**Companion.** The *positive* theorem (Goodstein terminates) is already done + axiom-clean in
`~/src/lean-formalizations` (`Logic/Goodstein`). That work is reused here as the model-side of
the bridge (its ordinal descent *is* the semantic content of transfinite induction up to ε₀).

**Why it's tractable-in-principle now.** Three of the four big pieces already exist in Lean:
- Gödel's incompleteness apparatus for arithmetic — `FormalizedFormalLogic` (`Foundation` +
  `Incompleteness`): provability predicate, derivability conditions D1/D2/D3, `Con[·]`.
- Cut-elimination for first-order logic (Gentzen's Hauptsatz) — `Foundation`.
- ε₀ (via the Veblen hierarchy) and all ordinal machinery — **mathlib**.
- `Foundation` is itself built on **mathlib @ v4.29.0** ≈ our `v4.29.1`, so PA and ε₀ can share
  one mathlib. No tower-bridging impedance mismatch.

The **one missing girder**: the ordinal analysis of PA — `TI(ε₀) ⊢ Con(PA)` (Gentzen) and
`Goodstein ⟹ TI(ε₀)`. Absent everywhere. That's the multi-month core.

See `EXPEDITION-PLAN.md`.

## License

[Apache License 2.0](LICENSE), Copyright 2026 Trevor Morris
