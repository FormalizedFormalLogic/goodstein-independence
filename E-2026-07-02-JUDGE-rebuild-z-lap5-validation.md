# E — JUDGE validation of REBUILD-Z lap 5 (Ren, 2026-07-02)

> Host-side judge pass on the lap-5 statement lap (global lap 185, commits `435ed72` + `04f071e`),
> per the templates + `REBUILD-Z-LAP5-ENTRANCE-2026-07-02.md`. Companion to the laps-2–4 ruling
> (`E-2026-07-02-JUDGE-rebuild-z-laps2-4-validation.md`).

## 1. Verdict: **PASS WITH JUDGE AMENDMENT — the SEVENTH statement trap, caught at statement time**

The lap executed the entrance lock faithfully (a–e all delivered, frozen surfaces untouched,
gates green) and its `collapse`/pin-shape/exit-corollary work is RATIFIED. But the draft's
iterate index — `iterCount α := norm α + 1`, a fixed syntactic count — is **kernel-refuted at
the `allω` reassembly** (§3). The box itself flagged the risk (T-Z5(iii)) but mis-classified it
as a deferred grind risk; it is a statement defect, and laps 6–7 grinding against it would have
been the exact anti-pattern the statement-lap cadence exists to prevent. The amendment
(judge-owned, applied per the lap-1/Option-A precedent): `iterSlot` is redefined as the
**diagonalizing ordinal-indexed iterate** (E–W Lemma 19's transfinite `F^α(0)`, realized by the
same fundamental-sequence recursion as the repo's own `hardy`). Post-amendment: build 🟢 1333,
pin statement + exit corollary recompile verbatim, headline undrifted. **Laps 6–7 are OPEN**
against the amended statement.

## 2. Independent re-verification (kernel-grounded, all run by this judge)

- `lake build` → **1333 jobs green** (before and after the amendment).
- **Freeze checks** (entrance lock §4): `cutReduceAllAuxRunning_Zf`, `stepAllω_Zf`,
  `inductive Zeh`, `inductive Zef`, `zeh_to_zef` — **hash-identical** across
  `9673a77 → post-amendment HEAD` (awk-extracted, md5). The read-off block untouched. The
  retired vacuous pin-3 form (`∃ f'` / `raise e α'`) deleted, as mandated.
- **My own `#print axioms` sweep**: pin 3 restated = `[propext, sorryAx, Classical.choice,
  Quot.sound]`; `cutElimPass_exit_root` sorryAx **solely via the pin** (the C3 composition is a
  real derivation); `collapse_NF`/`collapse_strictMono`/`iterSlot_def`/`iterSlot_zero`/
  `iterSlot_infl` + the five iterate bricks all standard-triple or less; frozen pins 1–2 +
  bridge + read-off unchanged; headline `peano_not_proves_goodstein` — **no drift**.
- **C1 conformance**: the restated pin's conclusion is `ZefProv (collapse α) e H (iterSlot f α)
  c Γ` — control `e` untouched, no `raise` anywhere. ✓
- **C3 conformance**: the exit corollary's bound `iterSlot (rel1 (hardy e) m) α 0` is visible in
  the statement and consumed by `headline_readoff_Zef`. ✓ (Survives the amendment verbatim.)
- `lake exe blueprint_audit` → PASSED (15 nodes — includes two in-flight WainerRoute ledger
  attributes from a parallel host session, uncommitted here; consistent).
- Sorry accounting: `OperatorZeh.lean` = **2 disclosed pins** (pin 3 body; `iterSlot_monotone`,
  the C5 obligation pinned by the amendment with lap 6 named). No other src file touched by the
  lap or the amendment.

## 3. The SEVENTH statement trap — the fixed-count iterate (kernel evidence: `wip/JudgeTrap7Probe.lean`)

The pass's induction at an `allω` node hands branch `n` its eliminated derivation at slot
`iterSlot (rel1 f n) (β n)`; the pin's conclusion forces the parent's branch slot
`rel1 (iterSlot f α) n` (the branch ordinal never enters — the lap-5 docstring mis-read its own
statement here, describing branch slots as `rel1 (iterSlot f (β n)) n`). Since `Zef.mono_f`
only raises slots, reassembly requires the pointwise containment

```
(rel1 f n)^[norm (β n) + 1]  ≤  rel1 (f^[norm α + 1]) n .
```

**Kernel counterexample** (probe compiled by this judge, `trap7_containment_fails`): at the
W4B-shaped instance `α = ω`, `β 2 = ofNat 2`, `f = hardy ω` (`= 2·+1`), `x = 0`:
parent side `f^[2] 2 = 11 < 23 = (rel1 f 2)^[3] 0`. Root cause: **`norm` is not monotone along
`<`** — `norm (ofNat n) = n` grows without bound along ω's fundamental sequence while
`norm ω = 1` — so *no* fixed ℕ-count read off the parent ordinal can dominate the branches.
Worst-case branch derivations genuinely realize witnesses up to their slot bound (exI at the
branch slot; the `two_level_config_Zef` shape), so this is a statement-level obstruction of the
same evidence grade as trap 6 (kernel-localized + structurally forced), not a proof-shape
inconvenience. Evidence-grade note: as with trap 6, this is *unprovable-as-stated with the
obstruction kernel-anchored*, not a falsity proof of the full pin — sufficient for a statement
amendment under the mandate, and the two grades stay distinguished in the record.

## 4. The amendment (judge-owned, applied)

`iterSlot f α` is now the **diagonalizing** iterate, by the same well-founded
fundamental-sequence recursion as `hardy` (which is precisely `iterSlot` of the successor, up to
the base case):

```
iterSlot f 0       = f
iterSlot f (a+1) n = iterSlot f a (f n)
iterSlot f λ n     = iterSlot f (λ[n]) n        (limit — the diagonalization)
```

- **Why this is the fix**: at the reassembly, `rel1 (iterSlot f α) n` evaluates the ordinal
  index at `α[max n x]`-stages — the branch index rides the numeric argument, absorbing the
  branch-growing budgets the fixed count could not. This is E–W's Lemma 19 taken literally
  (`F^α(0)` is a transfinite iterate); on finite ordinals the amendment agrees with the retired
  count form (`iterSlot f (ofNat k) = f^[k+1]`), so the `∃`-cut lane's `iter_comp` arithmetic is
  unaffected.
- **What carried over**: `collapse := expTower` (ratified as drafted — NF-preserving + strictly
  monotone, both proven); the pin's statement text (only the definition under `iterSlot`
  changed); the C3 exit corollary verbatim; `iterSlot_zero` (re-proven); characterization
  lemmas `iterSlot_zero'`/`iterSlot_succ`/`iterSlot_limit` + unfolding `iterSlot_def` added
  (mirroring `hardy_def`).
- **New obligations**: `iterSlot_infl` PROVEN (le_hardy pattern); `iterSlot_monotone` is a
  **disclosed sorry pin** (LOCK R5), discharging lap = **lap 6, FIRST item** — the proof
  mirrors `hardy_monotone` (zero/successor thread; the limit case needs the f-relative
  `reaches` comparison, the `hardy_le_of_reaches`/`fastGrowing_bachmann_reach` pattern
  generalized to base `f`). Its signature takes `Monotone f` + inflationarity (the diagonal
  case genuinely needs both).

## 5. What opens (laps 6–7), and the residual risk profile

**OPEN: discharge the restated pin 3** against the amended `iterSlot`, in this order:
1. `iterSlot_monotone` (the C5 pin — unblocks slot bookkeeping everywhere).
2. The pass induction: `∃`-cut lane via `stepAllω_Zf` + finite-ordinal iterate arithmetic;
   structural cases thread; the `allω` lane is the long pole — it needs the
   ordinal-monotonicity of `iterSlot` along fundamental-sequence reachability at sufficient
   budget (the repo's `reaches_of_lt`/norm-budget machinery around `hardy` is the template —
   this is why the amendment rides `hardy`'s exact recursion).
3. Composed smoke test stays green each lap (`cutElimPass_exit_root`).

Pre-registered triggers T-Z5(i)/(ii) cleared at statement level; T-Z5(iii) is **resolved by
this amendment at statement time** — its grind-lap residue is the reachability arithmetic in
(2), a proof burden, not a statement unknown. Estimates: 2–4 grind sessions (calibration 2–4×
optimistic applies), `allω`/reaches lane the likely majority.

## 6. Process notes

- The box's conduct was clean: statement-lap discipline held (no gated grinding, honest
  T-Z5(iii) flag, evidence in-file, frozen surfaces untouched, scoped stop honored). The
  mis-classification of T-Z5(iii) as grind-deferrable is a judgment error, not a violation —
  and it is precisely the class of error the judge gate exists to catch. Seven statement traps
  caught at statement time; zero have reached a grind lap.
- The uncommitted `WainerRoute.lean` ledger attributes (14–15) in the working tree belong to a
  parallel host session's blueprint curation — left uncommitted here (audit passes with them);
  that session owns their commit.

## 7. Gate state after this pass

| gate | state |
|---|---|
| Lap 5 (statement lap) | **PASS with judge amendment** (trap 7: fixed-count iterate → diagonalizing `iterSlot`) |
| Pin 3 statement | **LOCKED as amended** (C1–C3 conformant; kernel-checked; exit corollary green) |
| Laps 6–7 (pin-3 discharge grind) | **OPEN** — first item `iterSlot_monotone`, then the pass induction |
| Pin-3 discharge order | `iterSlot_monotone` → `∃`-cut/structural lanes → `allω`/reaches lane |
| Laps 8–10 (Δ₀ read-off extension) | gated behind the assembly (unchanged) |
| T-Z5(i)/(ii) | cleared at statement level |
| T-Z5(iii) | **resolved by amendment** (statement-time); residue = grind-lane proof burden |
