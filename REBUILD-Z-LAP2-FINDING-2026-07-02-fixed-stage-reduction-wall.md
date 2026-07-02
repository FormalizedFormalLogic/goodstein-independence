# REBUILD-Z LAP 2 — FINDING: the fixed-CONTROL reduction is obstructed at fixed OUTPUT STAGE

> Deliverable of `REBUILD-Z-ORDER-2026-07-02.md` laps 2–4 (discharge pins 1–2 against the
> judge-AMENDED fixed-control §5 statements).  Work site: `src/GoodsteinPA/OperatorZeh.lean`.
> Per the LOCK ("a lap that believes a locked/gated form is wrong STOPS and escalates, it does
> not improvise"): this is that escalation.  Build 🟢 1333, headline no drift.

## Verdict: **the reduction pins reduce cleanly to ONE localized gap, and that gap is a candidate SIXTH statement trap.**

Pins 1–2 are now **sorry-free modulo a single, precisely-characterized obstruction** in the new
helper `redDeriv`.  The obstruction is the exact analog of the judge's fifth trap, on the OTHER
axis: the fifth trap was "`NormControlled (f∘g)` at a **raised CONTROL** is false"; this is
"the reduction's derivation at the **fixed input STAGE** is unachievable."  Both have the same
root — the E–W cut-reduction genuinely **composes the witness bound** (`f∘g`, Lemma 25), and the
`Zeh` judgment's single-value `hardy e m` witness bound (LOCK §1 A1) cannot express a composed
bound internally.

## What was built (all in `src/GoodsteinPA/OperatorZeh.lean`, build 🟢 1333)

Kernel-clean infrastructure (`#print axioms` = `[propext, Classical.choice, Quot.sound]`):

- **`Zeh.change_H`** — operator irrelevance.  Every `Cl H β` side condition in a derivation is
  at an NF ordinal, so `Cl_of_NF` supplies membership in the closure of ANY generator set.  The
  generator slot `H` is freely replaceable in BOTH directions (the strong form `mono_H` cannot
  state).  This is rail **R1** realized in-kernel, and it dissolves ALL operator threading in
  the reduction (the running relativization `adjoin H n` of the inversion family and the ambient
  `H` of the ∃-side are interchangeable at will).
- **`normControlled_comp_running`** — the `NormControlled (f∘g) e m` conjunct of pins 1–2,
  DISCHARGED (judge **Q1**).  Needs no separate inflationarity hypothesis: control of `g` forces
  `g` inflationary (`x ≤ max m₀ x ≤ hardy e (max m₀ x) ≤ g x`, via `le_hardy`), then
  `f (g x) ≥ hardy e (max m (g x)) ≥ hardy e (max m x)` (`hf` at `g x`, `hardy_monotone`).
- **`principal_witness_exceeds_stage`** — `m < hardy ω m` (`= 2m+1`), the reduction-stage analog
  of the judge's fifth-trap kernel fact `hardy ω 0 = 1 > 0`.

The reduction skeleton (`sorryAx`-bearing, the gap disclosed):

- **`redDeriv`** — the full Towsner §19.6 running-family cut-reduction, induction on the ∃-side
  derivation `D`, mirroring the banked `Zekd.cutReduceAllAux` (`OperatorZinfty.lean:789`) with
  the norm bookkeeping deleted and the numeric `(k,d)` axis replaced by the stage axis `m`.
  **Every case closes** — `axL`, `wk`, `weak`, `allω` (reassembly lowers branch stage `max m n`
  back to `m`), `exI`-non-principal, `cut` — **except the principal `exI`**, reduced to exactly
  one gap (2 subcases, same wall).
- **`cutReduceAllAuxRunning_Zf`** (pin 1): body = `⟨redDeriv …, normControlled_comp_running hg hf⟩`.
- **`stepAllω_Zf`** (pin 2): body = invert D₁ via `allInv_Zeh` → running family → pin 1 (exactly
  the `probe_cut_all_arm_Zf` construction), Q3-unified; both conjuncts assembled.

## The gap, exactly

In `redDeriv`'s principal `exI` case (the ∃-side introduces the cut formula `∃⁰∼φ` at witness `n`):

```
hCut : Zeh (osucc (α+γ)) e H (max m n) c (Γ₀.erase (∃⁰∼φ) ∪ Γ)     -- the cut, at stage `max m n`
⊢     ZehProv (osucc (α+γ)) e H m c (Γ₀.erase (∃⁰∼φ) ∪ Γ)          -- required at stage `m`
       hbound : n ≤ hardy e m        hm : m₀ ≤ m
```

The cut combines:
- `famn` = `fam n` (the inverted ∀-family's `n`-th member) raised to the cut stage.  `fam n`
  lives at stage **`max m₀ n`** — its witnesses run up to `hardy e (max m₀ n)`.
- `Da'/Dβ'` = the recursively-reduced ∃-premise, whose witnesses are `≤ hardy e m` (raising its
  stage label from `m` to `max m n` adds no witnesses).

So the ONLY reason `hCut` needs stage `max m n` is `famn`'s witnesses.  To land the output at the
required stage `m`, one would need `max m₀ n ≤ m`, i.e. **`n ≤ m`**.  The available bound is only
`n ≤ hardy e m`, and `hardy e m > m` at every nontrivial control (`principal_witness_exceeds_stage`;
the headline control is `e = ω`).  `Zeh` has **no stage-lowering rule** (LOCK §1 A1: "no rule
lowers `m`"), and `famn`'s high witnesses are genuine (not bookkeeping) — so the gap cannot be
closed by any structural move.  This is `OperatorZinfty.lean:766–773`'s "witness-budget" failure
("the numeric single-index bound is provably FALSE") recurring on the `Zeh` stage axis.

## Why fixed-STAGE output is the trap (root cause)

The inverted family is **inherently running-stage**: `allInv_Zeh` returns the `n`-th ω-premise,
and the `allω` rule bakes stage `max m n` into every branch (LOCK §1 A1).  There is no
fixed-stage family to invert to.  Cutting a running-stage family member therefore inherently
raises the output stage; over nested principal cuts the required stage compounds as
`hardy e (hardy e (… m))` — which is precisely the E–W **`f∘g` composition** (Lemma 25) and the
Lemma-19 iterate.  The `Zeh` judgment bounds `exI` by a single `hardy e (stage)` value, so it
**cannot represent a composed witness bound** at a fixed stage.  The `NormControlled (f∘g) e m`
slot is external (the judgment does not read it), and it dominates `hardy e` (wrong direction to
bound an internal witness).  Hence: pins 1–2 as amended (fixed control **and** fixed output
stage `m`) are unprovable for `e > 0`.

Note the amendment repaired the CONTROL axis correctly (Option A is right — the reduction does
compose at fixed control, matching E–W Lemma 25's `f,F & g,F ⟹ f∘g,F`).  The residual defect is
on the STAGE axis, which the Option-A amendment did not touch: it kept the output stage tied to
the input `m`, inheriting the numeric-calculus witness-budget wall.

## Proposed resolutions (for the judge — statement-level, gated)

1. **Grow the output stage.**  Output `ZehProv (osucc(α+γ)) e H m' c (…)` at a stage `m'` the
   reduction determines, with `NormControlled (f∘g) e m'` linking.  Clean only if `m'` is a
   single value; the compounding over nested cuts suggests it is not (⇒ iterate).
2. **Function-valued `exI` bound in the judgment** (a LOCK §1 change): replace `hbound : n ≤
   hardy e m` by `n ≤ f n`-style control, so cut → `f∘g` is expressible internally and no stage
   grows.  This is the faithful E–W shape (R4 taken all the way into the judgment) but reopens
   the Z1 spike's judgment form — outside a grind lap.
3. **BW87 fallback (pre-registered P1).**  Do NOT thread the reduction at all: eliminate cuts
   (ordinal towers), then read off the cut-free derivation with the proven `readoff_sigma1`.
   The LOCK §5 P1 already blesses this; it requires the cut-free output to be a legal `Zeh`
   derivation (bounds payable at the raised control), which is `cutElimPass_Zf`'s (pin 3, lap 5)
   territory.

Resolution (2) is the one that makes the running-family reduction TRUE as a fixed-stage lemma;
(1) restates the pin; (3) routes around it.  **Which to adopt is a judge/architect call** (LOCK
§1 is locked; the pin shape is judge-owned).  Grinding the gap as written is refused, per the
LOCK escalation rail.

## Decisive diagnosis: the RUNNING STAGE is the sole culprit (kernel-proven)

`wip/RedDerivFixedStageProbe.lean` is `redDeriv` **verbatim with ONE change** — the family is
supplied at the FIXED stage `m₀` (`∀ n H', Zeh α e H' m₀ c …`) instead of the running stage
`max m₀ n`.  With that single change the principal `exI` **closes sorry-free** (raise `fam n` from
`m₀` to the ambient `m` via `m₀ ≤ m`, cut at `m`, output at `m` — no leak), and the whole
reduction is axiom-clean:

```
redDerivFixed   [propext, Classical.choice, Quot.sound]     -- sorry-FREE (lake env lean wip/RedDerivFixedStageProbe.lean)
```

So the obstruction is EXACTLY the running stage `max m₀ n` of the inverted family, nothing else.
`allInv_Zeh` returns the `n`-th ω-premise, and the `allω` rule bakes `max m n` into every branch
(LOCK §1 A1) — so a fixed-stage inversion does not exist in the calculus.  This pinpoints the fix:
either the ∀-side must be invertible to a FIXED-stage family (a change to `allInv_Zeh`/the `allω`
stage discipline — LOCK §1), or the witness bound must be function-valued so the running stage is
never read (resolution 2), or the reduction is routed around (resolution 3).  Restating the pin's
output stage (resolution 1) does NOT suffice on its own — `redDerivFixed` shows the reduction
wants the INPUT family at a fixed stage, not merely a grown output.

## Kernel evidence (real `#print axioms`, build 🟢 1333)

```
Zeh.change_H                         [propext, choice, Quot.sound]
normControlled_comp_running          [propext, choice, Quot.sound]
principal_witness_exceeds_stage      [propext, choice, Quot.sound]
cutReduceAllAuxRunning_Zf (pin 1)    [propext, sorryAx, choice, Quot.sound]  (sole sorry = the gap)
stepAllω_Zf               (pin 2)    [propext, sorryAx, choice, Quot.sound]  (sole sorry = the gap, via pin 1)
redDeriv                             [propext, sorryAx, choice, Quot.sound]  (the gap, 2 subcases)
peano_not_proves_goodstein           [propext, choice, goodstein_implies_consistency, Quot.sound]  — NO DRIFT
```

`redDeriv` closing every case but the one gap is the machine-checked proof that the difficulty is
localized exactly here, not spread across the induction.  The §6 seam probes stay green.
