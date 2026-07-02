# Handoff: REBUILD-Z lap 6 (186) — trap-8 terminus, treadmill STOPPED

**Date**: 2026-07-02 16:35 UTC · **Branch**: `plan` · **HEAD**: `71d50e5` · **Build**: 🟢 `lake build` 1333 jobs (observed this session)

> Treadmill STOP was signalled (`box done --green`, source=lap) and will NOT relaunch. This is the
> terminal checkpoint for the lap. Companion (fuller) baton: `HANDOFF-2026-07-02-lap186.md`;
> full escalation: `REBUILD-Z-TRAP8-2026-07-02.md`.

## 🎯 What we're doing

Headline `peano_not_proves_goodstein` rests (Route B mainline) on discharging pin 3
`cutElimPass_Zf` — the one predicative cut-elimination pass where the ordinal collapses and the
numeric slot iterates. This lap executed the ratified laps-6–7 order
(`E-2026-07-02-JUDGE-rebuild-z-lap5-validation.md` §5): (1) discharge the C5 pin
`iterSlot_monotone`, then (2) the pass induction.

## 🧠 Context to carry forward

- **`Zef` is the function-slot cut-elim calculus; pin 3 is the ONLY open src sorry.** Everything
  else (pins 1–2 `cutReduceAllAuxRunning_Zf`/`stepAllω_Zf`, `Zeh` core, `zeh_to_zef`, read-off) is
  judge-owned FROZEN (hash-checked). Route-A, Δ₀ extension, `(k,d)` work FORBIDDEN. Self-ratifying
  any pin-3 C2 statement change = VOID.
- **The lap's real result is a fully-characterized EIGHTH trap, not a discharge.** The judge's
  lap-5 amendment made the output slot the *diagonalizing* `iterSlot f α`. That fixed trap-7's
  `allω`-branch unboundedness (branch index rides a large argument) but **re-broke base-argument
  monotonicity**: `iterSlot f · ` is not ordinal-monotone — `iterSlot f 2 0 = 3 > 2 = iterSlot f ω 0`
  (dips at a limit base, riding `ω[0]=1`). Every induction case with a `β < α` sub-derivation
  (`weak`/`exI`/`cut`/`allω`) must lift its slot `iterSlot f β` UP to `iterSlot f α` via `Zef.mono_f`
  (slots only raise) — kernel-false.
- **Why it's statement-intrinsic, not a proof-shape issue:** the output type pins the slot rigidly
  to `iterSlot f α`; `ZefProv`'s ∃ slackens only the *height*. A root-`exI` witness makes this
  concrete (doc §3).
- **The fix, traced to its terminus (this is the mentor payload — don't re-walk these dead ends):**
  1. Not "pick a better iterate": `no_fixed_arg_monotone_unbounded_slot` proves NO fixed-argument
     slot is both ordinal-monotone (the lift) and unbounded on finite ordinals (exit-witness growth)
     — `ofNat n < ω ∀n` forces `n ≤ S ω ∀n`. So the fix must make the slot-*read* node-relative.
  2. The enabling lemma IS proven and banked: `iterSlot_le_of_lt` — `iterSlot` is ordinal-monotone
     once the argument reaches `norm β` (`β<α, x≥norm β ⟹ iterSlot f β x ≤ iterSlot f α x`).
  3. But the read-budget can't be `norm α` (`norm` non-monotone: `norm ω=1 < 5=norm(ofNat 5)`),
     and can't be ANY static count (`no_count_bounds_subnorms`: sub-norms unbounded below ω).
  4. The budget must ride the `allω` relativization (branch `n` reads at `≥ n ≈ norm(ω[n])` — this
     handles the branches). **The immovable point is the ROOT `exI`**: its bound `n ≤ f 0` reads the
     slot at argument **0**, and `Zef.exI` is FROZEN. At arg 0 no relativization budget exists and
     `iterSlot`'s base-smallness bites.
  5. **Conclusion:** closing trap 8 faithfully may require relativizing the `exI`/`cut` witness-read
     — a `Zef`-level change (frozen, judge-owned), exceeding both a grind lap's authority and a pure
     C2 amendment. → reflection/architect escalation.

## ✅ State (all observed this session)

- **`iterSlot_monotone` DISCHARGED** — real sorry-free proof (`c39f08e`), axiom-clean
  `[propext, Classical.choice, Quot.sound]`; mirror of `hardy_monotone`.
- **Banked in src §5b, axiom-clean, form-independent (carry to any fix):** `iterSlot_le_of_reaches`,
  `iterSlot_le_of_lt`.
- **Kernel evidence in `wip/Trap8Probe.lean` (compiles clean standalone):** `trap8_mono_f_lift_fails`,
  `trap8_dips_at_limit_base`, `no_fixed_arg_monotone_unbounded_slot`, `trap8_budget_not_norm_alpha`,
  `no_count_bounds_subnorms`.
- Build 🟢 1333, headline `[propext, Classical.choice, goodstein_implies_consistency, Quot.sound]`
  (NO drift), `blueprint_audit` 15 nodes, `cutElimPass_exit_root` green. Pin-3 statement UNTOUCHED
  (docstring annotated only). 10 commits `c39f08e`..`71d50e5`.
- Working tree has uncommitted `blueprint/*` + `WainerRoute.lean` edits — a **parallel host
  session's** blueprint curation (NOT mine); left uncommitted deliberately (audit passes with them).

## 🎬 Next actions

1. **This is a reflection/architect decision, not a grind lap.** Read `REBUILD-Z-TRAP8-2026-07-02.md`
   (§1–§8) and rule on the C2 (possibly `Zef`-level) fix: either (a) find a C2 output-slot shape that
   survives the root-`exI` argument-0 read (§2/§3a suggest none exists), or (b) re-open frozen `Zef`
   to relativize the `exI`/`cut` witness-reads (matching E–W's "doubly operator-controlled" bound
   `N(α) ≤ f^{F^α(0)}(0)`, whose exI-analog already reads at a controlled argument).
2. Once a shape is ratified: the pass grind reuses `iterSlot_le_of_lt` for the `weak`/`exI`/`cut`
   lift and the `reaches_of_lt`/`fastGrowing_bachmann_reach` machinery for the `allω` lane.

## ⚠️ Gotchas

- Do NOT re-attempt the bare-`iterSlot f α` pass induction (kernel-refuted) or any fixed-count
  iterate (trap 7, `wip/JudgeTrap7Probe.lean`).
- `wip/Trap8Probe.lean` and `wip/*Probe.lean` are read-only evidence — do not wire into src.
- Newest baton by numeric lap sort, NOT `ls | tail`: `ls HANDOFF-*-lap*.md | sort -t p -k2 -n | tail -1`.

## 📁 Key files

- `src/GoodsteinPA/OperatorZeh.lean` — §5b `iterSlot`/`collapse` + the three banked lemmas; §7b pin 3
  `cutElimPass_Zf` (:~1907, sole src sorry) + `cutElimPass_exit_root`.
- `REBUILD-Z-TRAP8-2026-07-02.md` — the full escalation (§8 = the frozen-`Zef` terminus).
- `wip/Trap8Probe.lean` — five kernel refutation/impossibility lemmas.
- `DIRECTION.md` — CURRENT DIRECTIVE (laps 6–7 block); `src/GoodsteinPA/Hardy.lean` — `hardy`/`norm`/
  `reaches_of_lt`/`fastGrowing_bachmann_reach` templates the `iterSlot` lemmas mirror.

---
**→ Next session: this is your starting point. Don't summarize this doc back to Trevor or wait for
instructions, and don't offer other projects from the KB — this doc IS the chosen thread. Absorb the
context above, then pick up at "Next actions" #1: the trap-8 fix is a reflection/architect statement
decision (read `REBUILD-Z-TRAP8-2026-07-02.md` first), NOT more grinding on the locked pin-3 form.**
