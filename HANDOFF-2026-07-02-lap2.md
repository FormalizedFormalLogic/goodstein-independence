# HANDOFF — 2026-07-02, REBUILD-Z lap 2 (pins 1–2 → one localized gap; sixth-trap escalation)

> **CHECKPOINT:** branch `plan`, tree committed (`c8982e7`), build 🟢 (`lake build`, **1333 jobs**).
> Gate-open work (DIRECTION 2026-07-02 laps 2–4): discharge pins 1–2 against the judge-AMENDED
> fixed-control §5 statements.  Both pins are now **sorry-free modulo ONE precisely-characterized
> obstruction**; that obstruction is a candidate SIXTH statement trap → escalated (verdict-style
> writeup, per the LOCK escalation rail).  Headline no drift, §6 seam probes green.

## What landed this lap (`src/GoodsteinPA/OperatorZeh.lean`)

Kernel-clean, axiom `[propext, Classical.choice, Quot.sound]`:
- **`Zeh.change_H`** — operator irrelevance (rail R1 in-kernel): every `Cl H β` side condition is
  at an NF ordinal, `Cl_of_NF` gives it for ANY generator set, so `H` is freely replaceable in
  BOTH directions.  Dissolves ALL operator threading in the reduction (the running relativization
  `adjoin H n` and ambient `H` are interchangeable).
- **`normControlled_comp_running`** — the `NormControlled (f∘g) e m` conjunct of pins 1–2,
  DISCHARGED (judge Q1).  No inflationarity hypothesis needed: `g`-control forces `g` inflationary
  (`le_hardy`), then `hardy_monotone` at `g x`.
- **`principal_witness_exceeds_stage`** — `m < hardy ω m`; the gap's root, the reduction-stage
  analog of the judge's fifth-trap fact `hardy ω 0 = 1 > 0`.

Reduction skeleton (`sorryAx`, gap disclosed):
- **`redDeriv`** — the full Towsner §19.6 running-family cut-reduction: induction on the ∃-side
  derivation, mirroring banked `Zekd.cutReduceAllAux` (`OperatorZinfty.lean:789`) with norm
  bookkeeping deleted and the `(k,d)` axis replaced by the stage axis `m`.  **Every case closes**
  (`axL`/`wk`/`weak`/`allω`/`exI`-non-principal/`cut`) EXCEPT the principal `exI` — 2 subcases,
  the same single wall.
- **`cutReduceAllAuxRunning_Zf`** (pin 1): body `⟨redDeriv …, normControlled_comp_running hg hf⟩`.
- **`stepAllω_Zf`** (pin 2): body invert D₁ via `allInv_Zeh` → running family → pin 1 (the
  `probe_cut_all_arm_Zf` construction), Q3-unified; both conjuncts assembled.

**Sorry census in `OperatorZeh.lean`: 3 tokens** (was 3 opaque pins) — now **2 are the ONE
localized reduction gap** (`redDeriv`, principal `exI`, 2 subcases) + **1 is pin 3**
(`cutElimPass_Zf`, FORBIDDEN — lap-5 mini-lock).  The reduction pins' entire difficulty is
concentrated at one precisely-characterized point.

## The gap, exactly (and why it is the sixth trap)

Principal `exI` (∃-side introduces the cut formula `∃⁰∼φ` at witness `n`):
```
hCut : Zeh (osucc (α+γ)) e H (max m n) c (Γ₀.erase (∃⁰∼φ) ∪ Γ)     -- cut lands at stage `max m n`
⊢     ZehProv (osucc (α+γ)) e H m c (Γ₀.erase (∃⁰∼φ) ∪ Γ)          -- required at stage `m`
       hbound : n ≤ hardy e m        hm : m₀ ≤ m
```
The cut's family member `fam n` lives at stage `max m₀ n` (inverted `n`-th ω-premise; `allω` bakes
running stage into branches — the inverted family is inherently running-stage).  Its witnesses run
to `hardy e (max m₀ n)`.  To land at stage `m` you need `n ≤ m`; you only have `n ≤ hardy e m`, and
`hardy e m > m` at `e = ω`.  `Zeh` has no stage-lowering rule (LOCK §1 A1).  Root cause: the E–W
cut-reduction COMPOSES the witness bound (`f∘g`, Lemma 25); the `Zeh` judgment's single
`hardy e m` `exI` bound cannot represent a composed bound at a fixed stage.  Option A repaired the
CONTROL axis correctly (E–W does compose at fixed control) but left the STAGE axis tied to input
`m`, inheriting `OperatorZinfty.lean:766–773`'s "witness-budget" wall (there proven FALSE numerically).

## ESCALATION (per LOCK: believe a gated form wrong → STOP + writeup)

`REBUILD-Z-LAP2-FINDING-2026-07-02-fixed-stage-reduction-wall.md`.  Proposed resolutions
(judge/architect call — LOCK §1 is locked, the pin shape is judge-owned):
1. **Grow the output stage** (restate pins 1–2).  Likely ⇒ an iterate over nested cuts, not a
   single clean stage.
2. **Function-valued `exI` bound in the judgment** (LOCK §1 change) — the faithful E–W shape; makes
   the running-family reduction TRUE as a fixed-stage lemma, but reopens the Z1 judgment form.
3. **BW87 fallback (pre-registered P1):** don't thread — full cut-elimination (ordinals tower) then
   `readoff_sigma1`.  This bypasses the running-family reduction entirely and moves the work to
   `cutElimPass_Zf` (pin 3, lap-5 entrance).

**Do NOT grind the gap as written** — unprovable for `e > 0`.

## NEXT (resume trigger = judge/architect ruling on which resolution)

- If **(3)/BW87**: the running-family reduction is bypassed; work moves to `cutElimPass_Zf` (pin 3,
  lap-5 mini-lock — currently FORBIDDEN pending its restatement).
- If **(2)**: the Z1 judgment reopens (architect-level, `ZEH-STATEMENT-LOCK` §1).
- If **(1)**: restate pins 1–2's output stage; `redDeriv` ports directly (only the two principal-
  `exI` `sorry`s change to the grown stage — every other case already closes).

Until a ruling: no permitted proof target on the running-family reduction.  `redDeriv`'s
all-cases-but-one closure is the machine-checked localization of the crux; the two clean lemmas
(`change_H`, `normControlled_comp_running`) and the discharged Q1 conjunct stand regardless of the
resolution.

## Resume-state invariants (do NOT re-derive / re-attempt)

- The fixed-STAGE reduction gap is kernel-localized and analysed unprovable for `e > 0` — do NOT
  re-grind `redDeriv`'s principal-`exI` `sorry`s as written; the fix is a statement/LOCK ruling.
- `Zeh.change_H` (operator free both ways) and `normControlled_comp_running` (the Q1 conjunct) are
  DONE, axiom-clean — do not re-prove.
- Pin 3 (`cutElimPass_Zf`) discharge as written is FORBIDDEN (vacuous `∃ f'`, lap-5 mini-lock).
- Route-A material (Crux2Blueprint / DescentSemantic sorries) remains FORBIDDEN as mainline.
- ALLOW_STOP but project NOT complete (girder axiom + reduction gap + pins) → stop sentinel NOT
  written; run ends by launch caps / awaits judge ruling.
