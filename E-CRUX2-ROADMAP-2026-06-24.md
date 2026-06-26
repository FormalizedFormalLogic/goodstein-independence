# E — Crux-2 milestone roadmap: the 80–160 behemoth as 4 bounded steps (judge, 2026-06-24)

> Project-management cut of crux-2 (complements `E-CRUX2-DECOMPOSITION-2026-06-24.md`, which is the
> *leaf-math* cut). Each milestone ≤ 40 laps, with a **measurable "done-when"** so progress is observable,
> not asserted. Front-2 (`PA_delta1Definable`) is **already discharged** (Foundation re-pin `e6e1ad1`,
> verified: real 1385-line `InductionSchemeDelta1.lean` instance, no sorry/axiom) — crux-2 is the SOLE
> remaining blocker. State at write time: lap 83, src sorries 3 (all crux-2/headline), descent banked,
> wall = validity + dispatch.

> **⚙️ OPERATOR DECISION (Trevor, 2026-06-25): M2 is NOT parallelized.** This roadmap originally floated
> running M2 (the Foundation→Z bridge) in a second box concurrently with M1. Trevor has decided against it:
> **M2 runs serial in the one box, after M1.** Do NOT spin a second worktree/treadmill for M2. The "parallel
> floor" numbers below are kept for reference only — the **serial path (~115 laps from lap 83) is the plan of
> record.** M1/M2 file-disjointness is still a true (and useful) fact; it just isn't being used to parallelize.

## The four milestones
| # | Milestone | Delivers / clears | Laps | Conf | Parallel? |
|---|---|---|---|---|---|
| **M1a** | Build the reduct `red` + auxiliary objects (construction only) | `red` 5-case primrec (Buchholz §6 Thm 6.6 / Def 3.2); critical case `d{0}=K^r(i/d_i[k])`, `d{1}=K^r(j/d_j[0])`, `red(d)=K^{r-1}d{0}d{1}` per 3.2(5.1); end-sequent (`tp`/`fstIdx`) transfer + `rk(A(d))<r` (T3.4(a)), on the built `inference_critical_pair` (L3.1) + rank cases (T4). **✔ `red` defined, end-sequent correct, T3.4(a) proven** | **10–18** | 65% | no |
| **M1b** | Prove `RedSound` (validity) + re-point (the cut-elim core) | `RedSound : ∀ d, ZDerivesEmpty d → ZDerivation (red d)` as the parallel-induction invariant (Thm 3.4(b)/Thm 6.2: principal sequent ⊆ Γ, cut-rank `< m`), threading banked `zKValidFDef`; re-point `RedSound`+descent onto `red`, off dead `iR2`. **✔ `RedSound` proven + chain `#print axioms`-clean** | **12–22** | 60% | no |
| **M2** | C0.5 Foundation→Z bridge | `foundation_bot_to_Z_empty : 𝗣𝗔.DerivationOf d ⊥ → ∃ z, ZDerivesEmpty z` (M-internal). Bryce–Goré `Peano.v` blueprint B1–B3: PA axioms→Z atomic; cut→`K^r`, ∀→`I_∀`, **PA-induction→native `Ind` (cheap)**; compose | **15–30** | 65% | **no** (operator 2026-06-25: serial) |
| **M3** | Descent assembly → `PA ⊢ (PRWO(ε₀)→Con(PA))` | wire M1+M2+banked ε₀-descent → `gentzen_descent_of_inconsistent` → no-infinite-primrec-descent ⊥ → `ZDerivesEmpty→False` → Con(PA). Clears `DescentSemantic:582`. Leaves: C4 (`isNF`/≠0 of `iord` on ⊥-derivs), C5 (descent as Σ₁ graph; least ⊥-proof via bridge) | **15–30** | 60% | no |
| **M4** | Headline wire-up + axiom-clean cert | discharge `goodstein_implies_consistency` (`Reduction.lean:68`) = crux-1 (γ→PRWO, done) ∘ M3; discharge `peano_not_proves_goodstein` (`Statement.lean:22`) via Gödel II | **5–15** | 70% | no |

## M1 proof approach (what the literature says — sound + precedented + mostly-equipped)
1. **Two parallel inductions** (Buchholz, both papers): validity (Thm 3.4) and descent (Lemma 4.1/Thm 4.2)
   are proved *separately, simultaneously* over the same `red` — this is *why* "ordinal-faithful but not
   valid" was never a contradiction, and it is the M1a/M1b seam. Carry validity as its own invariant; do NOT
   recover it post-hoc from the reduct.
2. **The reduct is an explicit primrec function** (§6 `red` Thm 6.6 / Def 3.2): deterministic 5-case
   recursion; only search = L3.1 least redex pair (built: `inference_critical_pair`). M1a is *porting*, not
   inventing. Beweistheorie's `Z*`/`tp(h)`/`h[ι]` is closest to the coded-derivation setting; align `h[ι]↔d[n]`.
3. **Validity is a concrete invariant** (Thm 6.2): principal sequent ⊆ Γ + cut-rank strictly drops =
   exactly the banked `zKValidFDef`.
4. **One hard case (5.1), gated on L3.1 + T3.4 — both already in the repo.** Genuinely-new content = the 4
   small leaves of `E-CRUX2-DECOMPOSITION`, mostly done. The wall is a staircase.
5. **Precedented**: Bryce–Goré machine-checked the analogous reduct+validity in Coq (`cut_elim.v` ~1.2k lines).
6. **Residual risk is M1b plumbing, not math**: threading the validity predicate through the *IΣ₁-internalized
   coded recursion* (the part B–G didn't face — theirs is meta-level). If the degree-drop validity stays
   intractable there, fallback = Siders' Howard vector-assignment descent (HA/intuitionistic, a redesign —
   exhaust the Buchholz parallel-induction route first). See `papers/siders-…md`.

## Sequencing
```
M1a─►M1b─┐
         ├─► M3 ─► M4
   M2 ───┘
```
M1 and M2 are **independent + file-disjoint** (M1 = `InternalZ.lean`/reduct; M2 = a new bridge module + the
Foundation calculus). That disjointness *would* permit running M2 in a second box concurrently — but
**operator decision (Trevor, 2026-06-25): we are NOT parallelizing. M2 runs serial, in the one box, after
M1.** Do not spin a second worktree/treadmill for it.

- **Serial (one box) — THE PLAN OF RECORD:** ~40 + 30 + 30 + 15 ≈ **115 laps**
- **+ research tail on M1:** up to ~150
- *(Reference only, not chosen)* Parallel (M1‖M2): ~max(40,30) + 25 + 12 ≈ **75 laps**

Planned path is the serial **~115–150 laps** (from lap 83). The ~75-lap parallel floor is documented for
context but is **not** being pursued.

## Measurable checkpoints (watch for drift, don't trust "progress")
- **M1 alive:** `red` exists as a 5-case function AND validity is proved *in the same induction* as descent
  (Buchholz parallel-induction). ❌ if a lap is still polishing `iR2` or recovering validity post-hoc.
- **M2 alive:** the PA-induction → Z-`Ind` case lands (the cheap part B–G paid for and we skip).
- **M3 alive:** `DescentSemantic:582` clears.
- **M4 (finish tape):** `#print axioms peano_not_proves_goodstein = [propext, Classical.choice, Quot.sound]`
  (PA_delta1Definable already gifted ⟹ no extra axiom).

## Overrun trigger (the one with real research risk)
**M1 is the only milestone that can blow past 40.** If M1 passes ~40 laps without `RedSound` materializing as
a proven theorem, **stop grinding and reweigh the Route-B / growth-rate pivot** (`E-ROUTE-OPTIONS-2026-06-24.md`)
— that's the pre-agreed decision point, not a vibe. M2/M3/M4 are bounded engineering; M1 is the wall.
