# REBUILD-Z LAP-1 FINDING (lap 176) — the f-slot pins conflate E-W Lemma 25 & Lemma 30, and that conflation IS the P1 obstruction

> **Read alongside `REBUILD-Z-LAP1-VERDICT.md` before opening the reduction-discharge gate.**
> This is a faithfulness finding on the **NOT-LOCKED** §5 f-slot draft (LOCK §6), produced by a
> direct cross-check of the three pins against the primary source
> (`papers/eguchi-weiermann-2012-operator-controlled-id1.md`, arXiv:1205.2879, Def. 23 +
> Lemmas 24–31). It touches **no gated body** — statement-shape audit only. It does **not**
> challenge a LOCKED form; §5 is exactly the judge-gated draft the judge is meant to weigh.
> Confidence: originally ~80%; the ~20% escape (Option B) is now **CLOSED in-kernel** (see the
> "escape is CLOSED" section — `mono_e_membership_gate_refuted` makes a reduction-level control-raise
> unsound). **Option A is kernel-forced.**

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
  Hardy target, which is *not* subject to the K2b raise pathology and is **now discharged
  in-kernel** by the banked lemma `NormControlled.comp` (added this lap,
  `[propext, choice, Quot.sound]`): `NormControlled g e m → (∀y, y ≤ f y) → NormControlled (f∘g) e m`,
  the inflationary hypothesis being exactly E-W's `(f.1)`. Option A's reduction obligation is a
  one-liner from banked plumbing.
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

## The ~20% escape is CLOSED in-kernel — Option A is FORCED, not merely recommended

The remaining doubt was: could Zeh's info-free `H`-membership (K1) block E-W's
"run-at-`F[K]`-then-absorb-to-`F`" step and *force* a raise into the reduction (Option B)? **No —
the existing theorem `mono_e_membership_gate_refuted` (`OperatorZeh.lean:224`) settles it.** It
proves `∃ e e' m, e' = raise e 1 ∧ e.NF ∧ e'.NF ∧ (∀S, Cl S e ∧ Cl S e') ∧ hardy e' m < hardy e m`
(concretely `hardy ω 0 = 1 < 5 = hardy 5 0`), with the docstring's exact conclusion: *"no `Zeh`-rule
package of (NF, `<`, membership) facts can re-establish the `exI` bound after a raise."*

Consequence for the reduction: a reduct concluding at control `raise e α` from premises at `e` must
re-establish every `exI` witness bound `n ≤ hardy e m` as `n ≤ hardy (raise e α) m`. Since
`hardy (raise e α)` can be *strictly smaller* (K2b) and there is no `mono_e`, that re-tag is
**unsound** — the calculus has no way to produce it. So pins 1–2's `raise e α` output is not merely
unfaithful to E-W Lemma 25; it is **unprovable/unsound as a reduction** (its numeric partner `f∘g`
cannot pay bounds that even a control-raise's own machinery can't re-establish). **Option A is
therefore forced, not a preference.**

Why the *pass* (pin 3) may legally raise where the reduction may not: the collapse (E-W Lemma 30)
does not *re-tag* an existing derivation — it *constructs* one at the raised control with the
**iterated** slot `f'` growing fast enough to dominate `hardy (raise e α')`. That is exactly why `f'`
must be the pinned iterate (Addendum): the raise is legal *only* when accompanied by the iteration
that pays the new bounds. Reduction = compose, no raise (Lemma 25); pass = raise, iterate (Lemma
30). The two are now kernel-separated, not merely stylistically distinct.

## What is NOT claimed

- Not claimed: a LOCKED form is wrong (§5 is NOT-LOCKED by design; this is input to the gate).
- Not claimed: `T-R(i)` fires. The E–W carrier still composes at both seams (verdict stands); this
  is about *where* the raise/iteration sit across the three lemmas, not whether the carrier works.

## Addendum (same lap, kernel-checked): pin 3's existential `f'` is VACUOUS — it breaks the read-off

`cutElimPass_Zf` (line 690) concludes `∃ α' f', … ∧ ZehProv α' (raise e α') H m c Γ ∧
NormControlled f' (raise e α') m`. Since the judgment `ZehProv` is **f-free** (LOCK §3), `f'`
appears ONLY in the `NormControlled f'` conjunct — nowhere is it tied to the derivation. And that
conjunct is trivially satisfiable on its own. Kernel-checked this lap (sorry-free):

```lean
example (e' : ONote) (m : ℕ) : ∃ f' : ℕ → ℕ, NormControlled f' e' m :=
  ⟨fun x => hardy e' (max m x), fun x => le_rfl⟩
```

So the existential-`f'` conjunct of pin 3 adds **no quantitative content** — pick
`f' := hardy (raise e α')` post hoc and it holds regardless of the collapse. This is stronger than
verdict question #2's framing ("is the existential the right abstraction?"): the existential is not
merely loose, it is **vacuous and read-off-breaking**. E-W's entire quantitative payoff is that the
numeric operator is carried *faithfully as the iterate* `f ↦ f^{F^α(0)+1}` (Lemma 30) all the way
down, so that Lemma 31 reads off `witness ≤ f(0)` for **that specific `f`**. An existential `f'`
severs `f` from the derivation and the final `f(0)` bound has no concrete `f` to name.

**Consequence for the gate:** `f'` MUST be pinned to the E-W iterate of the INPUT slot `f`
(`f' = f^{…}`, index = the collapse's ordinal count), not left existential. This is the locus where
lap-176's Option A relocates the real P1 work — and note it is *achievable* there: E-W's Lemma 19
(`N(α) ≤ f^{F^α(0)}(0)`) is exactly the bound that a pinned iterate satisfies, which composition at
the reduction could never deliver. Contrast pins 1–2: their `f, g` are explicit parameters and
`f∘g` is determined, so their conjunct is a *real* obligation (not vacuous) — the vacuity is
specific to pin 3's `∃ f'`.

## Resolution of verdict judge-question #3 (source-grounded): do NOT split `stepAllω_Zf`

Core check (lines 260–270): `allω` introduces `∀⁰φ` with premises over **every** branch `n`,
relativized (`adjoin H n`, `max m n`) — exactly E-W's **(⋀)** rule `f[N(ι)], F[ord(ι)] ⊢ Γ,A_ι ∀ι`.
`exI` introduces `∃⁰φ` from **one** premise at a bounded witness `n ≤ hardy e m` — exactly E-W's
**(⋁)** rule (one `ι₀`, `N(ι₀) ≤ f(0)`).

`stepAllω_Zf`'s principal cut is on the complementary pair `{∀χ, ∃¬χ}` (D₁ derives `Γ,∀χ`; D₂
derives `Γ,∃¬χ`). In E-W this is a **single ⋁-principal cut-reduction** (Lemma 25 with `C = ∃¬χ`
the ⋁-type, `¬C = ∀χ` the ⋀-type): extract the witness `n₀` from D₂'s `exI`, **invert** D₁ at `n₀`
via `allInv_Zeh` (= Lemma 24, now proven), cut `χ(n₀)` vs `¬χ(n₀)` at lower complexity. So:

**Answer: keep `stepAllω_Zf` unified — do NOT split into ∀- and ∃-principal steps.** `∀χ` and
`∃¬χ` are the *same* cut (dual formulas); there is one reduction, not two. The ∀-side is never a
separate reduction — it enters the single ⋁-principal reduction via inversion. Splitting would
duplicate the ⋁ machinery and falsely model ∀ as having its own reduction rule (it does not; `∀χ`
is always the `¬C` side, inverted). The only statement refinement worth making: the unified step's
docstring should record the asymmetry (D₂ = witness-provider, D₁ = inverted) — the body is where
`allInv_Zeh` lands, gated.

## Complete judge-input package (this lap)

| verdict Q | resolution (source-grounded, this lap) |
|---|---|
| #1 P1 conjunct locus | It is a **Lemma 25/30 conflation artifact** (main finding). Fix = Option A: fixed-control reduction (`NormControlled (f∘g) e m`, discharged in-kernel by banked `NormControlled.comp`); confine raise+iteration to the pass. P1 dissolves. |
| #2 `cutElimPass_Zf` existential slot | The existential `f'` is **vacuous & read-off-breaking** (kernel-checked). Must be **pinned** to the E-W iterate `f^{…}` (Lemma 30); Lemma 19 makes it achievable. |
| #3 split `stepAllω_Zf` ∀/∃? | **No** — one ⋁-principal reduction (E-W Lemma 25); ∀-side enters via `allInv_Zeh` inversion. |

## Adversarial self-check — three attempts to REFUTE the finding, all fail

A finding that survives its author's refutation is worth more to the judge. Three concrete attacks
on "pins 1–2's `raise e α` is unsound":

1. **"The reduct's `exI` witnesses are bounded by `hardy (raise e α)`, not `hardy e`, so the raise
   is fine."** No — in E-W cut-reduction the witnesses come from the *original* premises (bounded by
   `hardy e`, via the `exI` rule `n ≤ hardy e m`). Re-tagging them to control `raise e α` needs
   `n ≤ hardy (raise e α) m`, and `mono_e_membership_gate_refuted` exhibits `n=5 ≤ hardy 5 0` with
   `hardy (raise 5 1) 0 = hardy ω 0 = 1 < 5`. The re-tag fails on a concrete witness. **Attack fails.**
2. **"Pins 1–2 are vacuously provable — the premises are unsatisfiable, so the raise never bites."**
   No — `two_level_config_Zeh` (banked, sorry-free) is an explicit non-vacuity witness: derivations
   in exactly the premise shape exist. **Attack fails.**
3. **"`raise e α` might collapse to `e` (no-op) in the cases that matter."** No — `raise e α =
   e + ω^α` (line 58) is strictly increasing: `mono_e_membership_gate_refuted` already carries the
   kernel-proven clause `e < e'` for `e' = raise e 1` (via `↑5 < ω`), and `raise_lt_raise` (line 65)
   gives strict monotonicity in the exponent. The raise is never a no-op. **Attack fails.**

The finding is robust: pins 1–2 as stated are unsound reductions, Option A is forced. (The one thing
NOT refuted — because it is not a defect — is pin 3's raise, which is sound *precisely* because it
carries the iterate; that asymmetry is the finding's core, not a counterexample to it.)

## Recommended gate action

Before opening laps 2–4: rule on Option A vs B. If A (recommended), amend the §5 draft so the
control-raise and numeric-iteration live **only** in `cutElimPass_Zf`, and restate the reduction
conjuncts at fixed control. That amendment is a statement change (judge-owned), and it is the
cheapest possible place to catch the fifth statement trap — before any reduction body is ground
against an obligation that is unprovable *as stated* for a structural, source-identifiable reason.
