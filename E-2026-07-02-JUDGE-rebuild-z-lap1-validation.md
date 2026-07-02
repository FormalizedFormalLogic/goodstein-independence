# E — JUDGE validation of REBUILD-Z lap 1 (Ren, 2026-07-02)

> Host-side judge pass on the lap-1 statement lap (`48d9a4a` verdict, session laps 175–181,
> report delivered lap 181), per the don't-trust-box-handoffs rule. Companion to
> `E-2026-07-02-JUDGE-spike-z1-validation.md`. The gate under judgment:
> `REBUILD-Z-LAP1-VERDICT.md` + its three open questions + the lap-176/177 findings
> (`REBUILD-Z-LAP1-FINDING-2026-07-02-fslot-control-raise.md`).

## 1. Verdict RATIFIED — **WITH the Option-A statement amendment, applied by the judge**

The lap-1 PASS stands (A1 seed verbatim ✓, A3 inversion suite complete ✓, A2 f-slot suite
drafted with both Z1 seams re-composed ✓, T-R(i) does not fire ✓) — but the §5 draft
contained the **fifth statement trap**, caught at statement time by the box's own lap-176
audit and independently confirmed by this judge pass (§3). The trap-bearing conjuncts are
now **amended in `src/GoodsteinPA/OperatorZeh.lean`** (judge-owned statement change, LOCK §6):
pins 1–2 + the seam-1 arm probe restated at **fixed control**; pin 3 flagged DRAFT-INVALID
pending its lap-5 restatement. Post-amendment: `lake build` green (1333 jobs), still exactly
3 sorries (the pins), all footprints unchanged.

## 2. Independent re-verification (kernel-grounded, pre- and post-amendment)

- `lake build` → **1333 jobs green** (both before and after the amendment).
- **Exactly 3 `sorry`s**, all §5 pins; no new `axiom`, no `native_decide`, no
  `set_option`/`unsafe` (grep clean).
- My own `#print axioms` sweep (26 declarations) matches the box's report line for line:
  the A3 suite (`allInv_Zeh`, `orInv_Zeh`, `andInvL_Zeh`, `andInvR_Zeh`) all
  `[propext, Classical.choice, Quot.sound]`; the read-off exit clean; `sorryAx` confined to
  the 3 pins + `probe_cut_all_arm_Zf` (sole dependence = the reduction pin, since
  `allInv_Zeh` is now proven); the lap-175 `ZehProv` combinators (`cut`/`exI`/`allω`) clean;
  the lap-180 growth brick `hardy_add_le_comp` clean.
- **Headline drift check**: `peano_not_proves_goodstein` =
  `[propext, Classical.choice, goodstein_implies_consistency, Quot.sound]` — no drift.
- **A3 completeness argument verified**: the banked `Zekd` suite carries exactly the four
  companion inversions; the minimal `Zeh` core (six constructors, no `andI`/`orI`) admits no
  fifth (∃/¬ non-invertible) — "mined out" is a checked claim, not an assertion.
- **Faithfulness cross-check** (`REBUILD-Z-LAP181-FAITHFULNESS-2026-07-02.md`) reviewed:
  Aristotle formalized Kirby–Paris from prose only (never shown the repo Lean); the
  adjudication (same theory PA⁻+IND, syntactic `⊬` ≡ semantic via completeness, faithful
  hereditary-base-bump `goodsteinSeq`, graph-definability anti-vacuity anchor) is sound.
  A genuine independent corroboration of the LOCKED headline surface — banked.

## 3. The fifth statement trap — confirmed by two independent refutations

The drafted pins 1–2 concluded `… ZehProv … (raise e α) … ∧ NormControlled (f∘g) (raise e α) m`
— composition asked to dominate a **raised** control. Two independent attacks kill it:

- **Lap-176 (the box)**: the E–W Lemma 25/30 conflation finding — cut-reduction composes at
  FIXED `F`; only the collapse raises, and it pays with ITERATION. The re-tag of `exI`
  bounds at a raised control is unsound absent `mono_e` (kernel: K2b re-tag fails on the
  concrete witness `n=5`, `hardy ω 0 = 1 < 5`), and the Option-B escape is closed in-kernel.
- **This judge pass (independent)**: the conjunct is **falsifiable outright by
  instantiation** — `axL` derivations exist at ANY NF ordinal, so the pin's derivation
  hypotheses give no leverage. Take `e = ofNat 0`, `m = m₀ = 0`, `f = g = id` (controlled:
  `hardy 0 x = x`), dual-literal sequents for `fam`/`D₂`, any NF `α ≥ 1`: the conjunct
  demands `∀x, hardy (ω^α) x ≤ x`, false at `x = 0` (`hardy ω 0 = 1`). The same shape
  refutes pin 2 (the ∃δ gives no escape: every `raise E δ` control has `hardy … 0 ≥ 1 > 0`).

Two different proof strategies, same defect — the amendment is kernel-forced, not stylistic.
This is the fifth statement-level trap caught at statement time across the campaign (W3
spike, W3 judge catch, W4 amendment, W4B/Zᵉ pin corrections, this) — the statement-lap +
judge-gate cadence keeps paying: this trap would otherwise have been laps 2–4 grinding
against a provably-false obligation.

## 4. Rulings on the three gate questions

1. **Q1 (P1 conjunct locus): Option A, kernel-forced — APPLIED.** Reduction/step statements
   at fixed control with `NormControlled (f∘g) e m` (discharge near-immediate via the banked
   `NormControlled.comp` + hardy-inflationarity); ALL control-raising and numeric iteration
   confined to `cutElimPass_Zf` (Lemma 30). The P1 obstruction as previously stated
   **dissolves** (it was mis-located at the reduction); the genuine domination-under-raise
   obligation lives at the pass, paid by the iterate (Lemma 19 shape, `hardy_add_le_comp` +
   the lap-179 brackets are the banked ammunition). This also repairs the LOCK-R3 "once per
   pass" tension for free.
2. **Q2 (pin 3's `∃ f'`): VACUOUS — restatement required, deferred with teeth.** The
   vacuity is kernel-checked (`normControlled_exists_trivial`); a bare existential severs
   `f` from the derivation and breaks the E–W Lemma 31 read-off. `f'` must be pinned to the
   explicit E–W iterate of the input slot; the exact index expression needs the assembly's
   ordinal bookkeeping, so **pin 3's restatement is the lap-5 ENTRANCE gate** (statement
   mini-lock, judge-gated) and **discharging pin 3 as written is FORBIDDEN** (docstring +
   DIRECTION now say so — a trivial "discharge" of the vacuous form would be a fake advance).
3. **Q3 (split `stepAllω_Zf`?): NO — stays unified.** Source-grounded (one ⋁-principal
   cut-reduction; `∀χ` is always the `¬C` side, entering via `allInv_Zeh` inversion — there
   is no separate ∀-reduction). The docstring now records the asymmetry (D₂ =
   witness-provider, D₁ = inverted).

## 5. What opens, and with what ammunition

**Laps 2–4 are OPEN: discharge pins 1–2 against the AMENDED fixed-control statements.**
The fixed-control reduction is the standard cut-reduction — no re-tag anywhere (`exI`
bounds carry verbatim; memberships by closure; inversion is control-preserving and PROVEN).
Banked and ready to wire: the full inversion suite (§4/§7), `NormControlled.comp` +
`normControlled_rel1`, the `ZehProv` combinators (`cut`/`exI`/`allω`), the splice-descent
bricks (`osucc_add_mem`, `add_lt_osucc_add`, …), and the growth lane
(`hardy_add_le_comp`, E–W Lemma 19 brackets, the ε₀-diagonal capstone) for the pass work
later. The §6 seam probes are the standing composition tests — they must stay green as the
pins discharge. Still gated: pin 3 (lap-5 entrance mini-lock), the Δ₀ read-off extension
(laps 8–10), Route-A (unchanged).

## 6. Process notes

- **The holding-pattern token burn (laps 176–181) was the flip side of the safety design**,
  and the box behaved exactly as ordered (no gated grinding, no manufactured side-leaves —
  the "forbidden drift" rail held). But most of those tokens bought verification-and-wait,
  not proof. For future gated runs: size `--max-laps` to the permitted scope (~3 here, not
  5+), or arrange the judge pass between runs. The productive share of this run was still
  substantial: the statement lap, the full inversion suite, the ZehProv API, the growth-lane
  bricks, the Q1–Q3 kernel findings, and the faithfulness cross-check.
- Evidence hygiene held throughout: findings are kernel-backed in-file (not prose claims),
  the lap-180 review corrected a lap-179 overclaim ("lane mined") with an inventory, and the
  faithfulness check kept Aristotle blind to the repo Lean.

## 7. Gate state after this pass

| gate | state |
|---|---|
| Lap-1 verdict | **RATIFIED with judge amendment (Option A applied)** |
| Laps 2–4 (pins 1–2 discharge, fixed-control) | **OPEN** — starts when the operator fires |
| Lap 5 (assembly) entrance | statement mini-lock: pin 3 restated with explicit iterate, judge-gated |
| Pin 3 discharge as written | **FORBIDDEN** (vacuous form) |
| Laps 8–10 (Δ₀ read-off extension) | gated behind the assembly |
| T-R | not fired; pre-registration unchanged |
