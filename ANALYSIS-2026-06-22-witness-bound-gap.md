# ANALYSIS (lap 11) — the witness-bound `k` is on the critical path; embedC is the *unbounded* embedding

**TL;DR.** Reading Towsner §13–17 carefully (`papers/towsner-goodstein-epsilon0-unprovability.pdf`)
resolves a confusion that the lap-9 pivot glossed over. The Route-B lower bound (Thm 17.1) bites only
because the bounded calculus `Z∞^{α,k}` constrains the **∃-witness value** (`value(t) ≤ h_α(k)` in the
I∃ rule). M5's `Provable α c Γ` tracks the **cut rank `c`**, NOT this witness bound `k` — exactly the
gap flagged at lap 4 (`ANALYSIS-…-bounding-resolution.md`, step 1: "the bound `src/Zinfty.lean`
currently drops"). Consequences:

1. **The lap-11 bridge `cutfree_lt_eps0_absurd` (in `wip/Bounding.lean`) is FALSE as stated.**
   `↑goodsteinSentence` is TRUE, so `provable_true` (= Towsner Thm 14.2, ω-completeness) builds a
   **cut-free** derivation of `{↑gs}`. Its M5 ordinal `o` is `< ε₀` (in fact `< ω^ω`): the only
   ordinal-raising rule that depends on data is `allω` (`+1` over an ω-family); bounded quantifiers
   `∀i<B` become a single `allω` of ordinal `ω` *regardless of `B`*, and `exI` adds `+1` *regardless
   of the witness value*. The astronomically-large Goodstein witnesses cost **zero** ordinal. So a
   cut-free `Provable α 0 {↑gs}` with `α < ε₀` EXISTS — the ordinal alone does not prevent it. Only
   the witness bound `k` (which forbids `exI` with `value > h_α(k)`) makes Thm 17.1 bite.

2. **`embedC` (M4, this lap) is the *unbounded* embedding** (Towsner Thm 14.2 territory), not the
   bounded Thm 16.7. Its `axm` case uses `provable_true`, which is the ω-completeness that Towsner
   explicitly calls "useless" for unprovability (§15 opening): `PA ⊢ φ ⟹ φ true ⟹ provable_true ⟹
   Z∞ ⊢ φ`, so `embedC` adds nothing over `provable_true` + soundness. It is a correct, axiom-clean
   result and its **building blocks are reusable** (see below), but it is NOT the headline-critical
   object.

## What the headline actually needs (Towsner §16–17, precise)
The bounded calculus `Z∞^{α,k}` (M6's `B α k` IS its cut-free fragment) with the I∃ rule:
> ∃t closed, `value(t) ≤ h_α(k)`, and `β<α` with `τ(β)<k`, s.t. `Z∞^{β,k} Γ,φ[x↦t]` ⟹ `Z∞^{α,k} Γ,∃xφ`.
and the I∀ rule with `β_n < α`, `τ(β_n) < max{k,n}`. Then:
- **Thm 16.1 (universal axioms `𝗣𝗔⁻`):** `Z∞^{k,k+1} ψ` for a true universal `ψ` with `k` vars
  (just I∀ over True leaves) — finite ordinal `k`. **Reuses `provable_true`-style on the quantifier-
  free matrix** (which IS bounded — no `∃`).
- **Thm 16.5 (induction axiom):** `Z∞^{ω·4#2^{rk(φ)}#2, m}` via a **bounded meta-induction on `n`**
  (NOT ω-completeness): build `Γ, φ[n]` from `Γ, φ[n+1-side]` using I∧/I∃/C, witness `n+1 ≤ h_α(k)`.
  Specific ordinal `< ε₀`. **Reuses `provable_em` (the `φ,∼φ` leaf) and `exI` carefully.**
- **Thm 16.7:** chains 16.1/16.5 + the propositional/quantifier rules over a `𝗣𝗔⁺` proof ⟹ bounded
  deduction with `α < ε₀`, finite cut rank.
- **Thm 19.9:** cut-elimination **preserving the `(α,k)` bound** (raises `α`, keeps `< ε₀`).
- **Thm 17.1 = M6 `lowerBound_hardy_selfcontained`:** no bounded cut-free deduction of `{↑gs}`.

## The corrected critical path (supersedes the lap-9 "bound directly on unbounded Deriv" reframe)
The lap-9 reflection pivoted M4 onto the *unbounded* M5 `Provable`, reasoning the bounding lemma
could be redone "directly on the cut-free `Deriv` reusing M6's ℕ-domination." **That is not viable:**
a cut-free *unbounded* `Deriv` of `{↑gs}` need not have bounded witnesses (point 1), so it cannot be
mapped to M6's `B` (whose `exI` demands `v ≤ h_α k`). The witness bound must live IN the calculus.

So the witness-bounded calculus `Zᵏ` (= M5 `Deriv` + the `(α,k)` I∃ bound) — the laps-6–8 thread
(`BoundedZinfty`/`SplitZinfty`/`OperatorZinfty`/`Zekd`, banked in `wip/`) — is **back on the critical
path**, not off it. The lap-8/9 abandonment ("single-index Hardy inequality false; literature never
threads the witness index through cut-elim") was about a specific bookkeeping formulation; Towsner DOES
thread `(α,k)` through cut-elim (Thm 19.9). The correct next phase is steps 1–4 of the lap-5 plan
(`ANALYSIS-…-bounding-resolution.md`): build `Zᵏ`, the **bounded** embedding `16.1/16.5/16.7`,
`(α,k)`-cut-elim `19.9`, then the subformula bridge to `B`.

## What is BANKED and reusable (do NOT discard — these are correct, axiom-clean assets)
All in `src/GoodsteinPA/Embedding.lean`, `[propext, choice, Quot.sound]`:
- **`provable_true`** — ω-completeness. Directly gives Thm 16.1 (universal axioms) once witnessed in
  `Zᵏ`: the quantifier-free matrix has no `∃`, so its `Zᵏ` derivation is automatically bounded.
- **`provable_em` / `provable_em_cong_gen` / `Provable.exI_closed`** — the `φ,∼φ` leaf (Thm 14.1) and
  closed-witness `∃`-intro: exactly the pieces Thm 16.5's meta-induction needs.
- **`embedC`** — the unbounded embedding; its structural-rule cases (and/or/cut/wk/shift/all) port
  almost verbatim to the bounded `Zᵏ` embedding (only `axm`/`exs` change: `axm` → 16.1/16.5 with
  ordinals; `exs` → bounded `exI` with `value ≤ h_α(k)`).
- M5 `cutElim` machinery — the template for the `(α,k)`-tracking cut-elim (the `wip/` Zekd analyses
  already worked §19.2–19.5 with the control axis).

## Recommendation for next lap (Trevor: this revisits the lap-9 route call)
1. **Decide the calculus carrier for `k`.** Cleanest per lap-8: a `Provable`-style wrapper over a
   witness-bounded `Deriv` (`Zᵏ`/`Zekd`), `∃ α' ≤ α, α'.NF ∧ Zᵏ …`. Reuse the banked `wip/` Zekd.
2. **Bounded embedding (Thm 16.x)** reusing the banked assets above. `axm` = 16.1 (`provable_true`
   on the bounded matrix) + 16.5 (meta-induction via `provable_em`/`exI_closed`), with the specific
   ordinals `k` / `ω·4#2^{rk}#2`.
3. **`(α,k)` cut-elim (19.9)** — the `wip/` Zekd §19 grind, now correctly motivated.
4. **Subformula bridge to `B`** + assemble vs `lowerBound_hardy_selfcontained`.

The lap-11 `wip/Bounding.lean` assembly skeleton stays valid in SHAPE (embed → cutElim → bridge), but
every arrow must be over `Zᵏ` (with `k`), and the bridge must read `value ≤ h_α k`, not just `α < ε₀`.
