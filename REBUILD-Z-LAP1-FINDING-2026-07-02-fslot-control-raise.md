# REBUILD-Z LAP-1 FINDING (lap 176) — the f-slot pins conflate E-W Lemma 25 & Lemma 30, and that conflation IS the P1 obstruction

> **Read alongside `REBUILD-Z-LAP1-VERDICT.md` before opening the reduction-discharge gate.**
> This is a faithfulness finding on the **NOT-LOCKED** §5 f-slot draft (LOCK §6), produced by a
> direct cross-check of the three pins against the primary source
> (`papers/eguchi-weiermann-2012-operator-controlled-id1.md`, arXiv:1205.2879, Def. 23 +
> Lemmas 24–31). It touches **no gated body** — statement-shape audit only. It does **not**
> challenge a LOCKED form; §5 is exactly the judge-gated draft the judge is meant to weigh.
> Confidence the tension is real and decision-relevant: **~80%.**

## The two E-W lemmas the reduction/pass must mirror

From the source (§4 lemma-engine table, lines 174–189):

| E-W lemma | ordinal operator `F` | numeric operator `f` |
|---|---|---|
| **25 Cut-reduction** (`C≃⋁`, `rk(C)=ρ`) | **UNCHANGED** (both premises + conclusion at `F`) | **composition `f∘g`** |
| **26 / 27 / 30 Collapse & cut-elim** | **RAISED** (`F ↦ F^{α+1}`, e.g. Lemma 30) | **iteration `f ↦ f^{F^α(0)+1}`** |

The division of labor is the paper's whole point (Conclusion, p. 25; source lines 42–45): the
super-affine demand that a numeric *counter* could never absorb (the SPIKE-W4B death) is paid by
**moving up the function hierarchy at the collapse** — *composition at cut-reduction, iteration at
the rank-collapse*. They are different lemmas with different updates; no single E-W lemma both
raises the control and merely composes the numeric slot.

## What the pins actually state (`src/GoodsteinPA/OperatorZeh.lean` §5)

`raise e α := e + ω^α` (line 58) — a genuine control-index raise; `hardy (raise e α)` grows
*strictly faster* than `hardy e` at large arguments (and can be *smaller* at small ones — `raise
(ofNat 5) 1 = ω`, `hardy ω 0 = 1 < hardy 5 0 = 5`, kernel-checked at line 216). So `raise` is the
Hardy-side analog of E-W's `F ↦ F^{α+1}` collapse move, **not** a reduction move.

| pin (line) | output control | output numeric slot | E-W move it mixes |
|---|---|---|---|
| `cutReduceAllAuxRunning_Zf` (659) | `raise e α` (RAISE) | `f∘g` (COMPOSE) | Lemma 30 raise **+** Lemma 25 compose |
| `stepAllω_Zf` (674) | `raise E δ` (RAISE) | `f∘g` (COMPOSE) | Lemma 30 raise **+** Lemma 25 compose |
| `cutElimPass_Zf` (690) | `raise e α'` (RAISE) | `f'` iterated, ∃ (ITERATE) | Lemma 30 raise **+** Lemma 30 iterate ✓ |

Both **inputs** to pins 1 and 2 are held at one control (`e` / `E`) — R3-compliant on the input
side. It is the **output** that raises. Pin 3 is internally consistent with Lemma 30. Pins 1–2
are not consistent with any single E-W lemma.

## Why this conflation *is* the P1 obstruction (the payoff)

The verdict's #1 judge-question and `PENDING_WORK` both flag
`NormControlled (f∘g) (raise e α) m` as "the open threading question / false unconditionally per
K2b." Unfold it: `∀x, hardy (raise e α) (max m x) ≤ (f∘g) x`. This asks **composition** `f∘g` to
dominate the **raised, faster-growing** `hardy (raise e α)`. In E-W that is a category error:
composition suffices to dominate the *fixed-control* Hardy target (Lemma 25); dominating a *raised*
control is precisely what **iteration** buys (Lemma 30, via the norm bound Lemma 19
`N(α) ≤ f^{F^α(0)}(0)`). The conjunct reads as "unprovable / K2b-false" **because it demands of
composition what only iteration can deliver** — a direct consequence of gluing Lemma 30's raise
onto Lemma 25's numeric update.

## The fix this points to (for the judge to rule on)

**Option A (faithful E-W architecture; recommended).** Keep the *reduction* at **fixed control**:
- `cutReduceAllAuxRunning_Zf` / `stepAllω_Zf` output at `e` / `E` (not `raise …`), numeric slot
  `f∘g`; conjunct becomes `NormControlled (f∘g) e m` — composition dominating the **same-control**
  Hardy target, which is *not* subject to the K2b raise pathology and is provable from the input
  domination (`NormControlled.mono` + the `f∘g` growth already banked as
  `seam1_bump_absorbed_by_composition`).
- **All** control-raising *and* numeric iteration is confined to `cutElimPass_Zf` (pin 3), faithful
  to Lemma 30. The genuine "domination under raise" obligation lives there and is discharged by the
  **iterated** slot `f'` via the Lemma 19 norm bound — *not* by hardy-domination of a composed slot.

  Consequence: the P1 obstruction as currently stated **dissolves** (it was mis-located at the
  reduction). This also repairs the R3 tension below for free.

**Option B (raise stays at the reduction).** Then the numeric update on pins 1–2 must be
**iteration**, not composition — but a raise+iterate reduction *is* a collapse, so pins 1–2 would
no longer be "the running-family reduction." This collapses the three-pin structure into one and
should be rejected unless there is a Zeh-specific reason (see the no-`mono_e` argument below) that
the reduction genuinely cannot stay at fixed control.

## Secondary tension (independent of the numeric-slot point): R3 "once per pass"

LOCK R3: "control changes happen at STATEMENT level, **once per elimination pass** (A2)." But pins
1 and 2 each raise the control *per reduction/step*. A single pass (`cutElimPass_Zf`) reduces *many*
cuts; if each underlying reduction/step raises `e`, the pass raises many times — and with **no
`mono_e`** (`mono_e_membership_gate_refuted`) there is nothing to unify the accumulated raises back
to one. Under **Option A** this evaporates: reductions keep `e` fixed, the pass raises exactly once
— which is what R3 says and what E-W does (Lemma 25 fixed-`F`, Lemma 30 raises once). Under Option B
the design owes an account of how per-step raises reconcile with "once per pass" absent `mono_e`;
this looks like a re-entry of exactly the per-branch-raise-then-unify mechanism SPIKE-W4B killed.

## What is NOT claimed

- Not claimed: a LOCKED form is wrong (§5 is NOT-LOCKED by design; this is input to the gate).
- Not claimed: `T-R(i)` fires. The E–W carrier still composes at both seams (verdict stands); this
  is about *where* the raise/iteration sit across the three lemmas, not whether the carrier works.
- Not claimed with certainty: the ~20% escape is that Zeh's info-free `H`-membership (K1) blocks the
  E-W "run-at-`F[K]`-then-absorb-to-`F`" step, *forcing* a raise into the reduction. Even then the
  numeric slot must become iteration (Option B), and the R3/no-`mono_e` account is still owed.

## Recommended gate action

Before opening laps 2–4: rule on Option A vs B. If A (recommended), amend the §5 draft so the
control-raise and numeric-iteration live **only** in `cutElimPass_Zf`, and restate the reduction
conjuncts at fixed control. That amendment is a statement change (judge-owned), and it is the
cheapest possible place to catch the fifth statement trap — before any reduction body is ground
against an obligation that is unprovable *as stated* for a structural, source-identifiable reason.
