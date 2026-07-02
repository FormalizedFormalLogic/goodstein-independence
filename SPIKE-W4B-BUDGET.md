# SPIKE W4B — the principal ∀/∃ `d`-BUDGET spike (running-family reduction under ω-nodes; operator-commissioned, 2026-07-02)

> **One bounded session. Deliverable = a minimal kernel probe of ONE composition point + a binary
> verdict file. NOT a proof campaign.** Deciding experiment #3, resolving the residual that
> SPIKE-W4 located (`SPIKE-W4-VERDICT.md` §"the residual") — the last design unknown before the
> W-ladder grind. Its pre-registered trigger **T-W4B** is the early-firing form of the masterplan's
> T-W4: a kernel-confirmed obstruction here fires the **Buchholz operator-controlled (`Zᵉ`)
> fallback fork on day 1** instead of 20 laps into the phase. Either outcome is a win.

## Context (read first, in order)

- `SPIKE-W4-VERDICT.md` — esp. §"the residual" (the analysis you are confirming/refuting) and the
  per-case table. `E-2026-07-02-JUDGE-spike-w4-validation.md` §5 (judge concurrence + the honesty
  bar for this spike).
- `wip/SpikeW4CutElim.lean` — the pinned step statement + skeleton; your probe composes with its
  motive. `step_cut_principal`'s docstring names both obligations.
- `src/GoodsteinPA/OperatorZinfty.lean:756–800` — `cutReduceAllAux` (the banked FIXED-family ∀/∃
  reduction, output slot `dd + norm α + 1`) + the `:764` SCOPE block (the known gap this probes);
  `:2262/:2283` (`cutReduceAllAux_control`); `allInv` (`:2209`).
- `src/GoodsteinPA/ZinftyGen.lean:1547–1694` — the unbounded template.
- Towsner §19.6–19.9; `papers/buchholz-wainer-1987-…`; `papers/buchholz-beweistheorie-skriptum.pdf`
  (operator-controlled derivations — the fallback you may end up pinning).

## Standing doctrine (traps already caught twice — do not re-hit them)

The recursion runs at the `Zekd`/`ZekdProv` level; the someK `∃K` is opened at the ROOT only
(never inside an induction — `∀n ∃Kₙ ↛ ∃K ∀n`). The control `e` is constant through a `Zekd`
derivation; branch dependence enters ONLY via the running index `max k n`. Budgets in a motive
must be functions of structure, never of a branch index.

## The one open design question

SPIKE-W4's step motive concludes at budget slot `d + norm e + 1` (uniform). At a **principal ∀/∃
cut node sitting under an enclosing ω-node** (branch `n`, node index `k_node = max k n`):

- the IHs arrive at slot `dd_in = d + norm e + 1`;
- the banked reduction's output slot is `dd_in + norm α_fam + 1` with `α_fam = expTower βφ`
  (the reduced ∀-side's ordinal), so the bump is `≈ norm βφ + 2`, and the only available bound is
  `norm βφ < k_node + d` — **branch-dependent**;
- the node must emit at slot `d + norm e + 1`. Overflow `≈ k_node + d` — not absorbable by any
  structural functional (analysis; NOT yet kernel-verified). Note the wall does NOT bite at the
  root (`operatorCutElimStep` raises `K` freely via `mono_k`); it bites exactly for interior cuts
  under ω-nodes — so the probe MUST model the two-level configuration (cut node under one `allω`).

**Question: does the numeric `(k, d)` budget calculus admit ANY statement-level fix, or does the
overflow kernel-confirm — forcing the `Zᵉ` redesign?**

## Objective

In `wip/SpikeW4BBudget.lean` (new file; `wip/` only, no `src/` edits):

1. **Pin the running-family reduction statement** (body may be `sorry`): `cutReduceAllAux`
   generalized fixed `k₀` → running `max k₀ n` (family from `allInv`), control raised per
   SPIKE-W4's `raise`, with an EXPLICIT output ordinal shape (`osucc (α_fam + γ)`-class) and an
   explicit output budget. **Admissibility rail (the honesty bar — a sorried statement must be
   plausibly provable):** any output-norm bound you assume must be achievable by the output
   ordinal's own `norm` — reality-check it on concrete `ONote` instances (`norm`/`ONote`
   arithmetic is computable; `decide` the instances). Assuming away the `norm α_fam` contribution
   that the output ordinal genuinely contains is a fake PASS.
2. **Build the composition probe** — the two-level configuration: the ∀/∃ arm of
   `step_cut_principal` consuming (1)'s output, sitting as a branch of one enclosing `allω`
   re-assembly. Kernel-check the budget max-algebra at both seams (IH slot → reduction output slot
   → ω-node's uniform-`d` demand), exactly as `step_allω` kernel-checked the control half.
3. **Try the candidate dodges, in this order** (each dies at a named seam on the armchair — the
   kernel decides; you may find shapes not listed):
   - **(a) tighter output norm**: strengthen (1) so the output wrapper's norm rides the ∃-side
     `γ` + structural constants only, shedding `norm α_fam` where it is bookkeeping (vs genuinely
     carried by the output ordinal — the admissibility rail above draws that line).
   - **(b) ordinal-indexed slot**: motive slot `d + norm e + norm α + 1` where `α` is the
     sub-derivation's OWN ordinal (structure at every node). Armchair failure point: the `allω`
     re-assembly demands ONE `d` for all premises while `norm (β n)` varies — check whether
     `mono_d` + the wrapper's slack can bridge it; this is the sharpest single kernel check in
     the spike.
   - **(c) rebalance into the `k`-slot**: believed provably wrong-direction (`allω` premises must
     sit at exactly `max k n`; cf. the `:764` hardy counterexample) — confirm cheaply, move on.
4. **If a shape closes**: re-elaborate the SPIKE-W4 skeleton's motive on the amended slot (a
   mechanical slot-expression edit across the 12 case-lemma signatures + the assembly) and confirm
   the induction still consumes every arm — a statement amendment is only validated by re-running
   the assembly (the W3 lesson). Then PASS.

## Verdict criteria — write `SPIKE-W4B-VERDICT.md`, then STOP

- **PASS** = the two-level composition closes in-kernel (or transparently reduces to
  `mono`/`norm_*` lemmas) with all budgets structural, AND the amended motive re-assembles the
  full skeleton. State the pinned reduction statement + the amended step statement; flag every
  place the admissibility rail was load-bearing.
- **FAIL** = the overflow kernel-confirms: for EACH attempted shape, the failing inequality is
  reduced to a concrete kernel-checked counterexample (`decide` on explicit `ONote`s/indices) or a
  named unsatisfiable side condition. **T-W4B fires** — then PIN (do NOT build) the `Zᵉ` redesign:
  what replaces `(k, d)` (control FUNCTION/set `H` closed under `+`, `ω^·`, `osucc`; "norms in
  budget" → "ordinals in `H`"), which banked assets carry over unchanged (SPIKE-W4's `raise` +
  `step_allω` argument, the 12-case skeleton shape, `mono_e`, the unbounded template), which must
  be rebuilt, and a lap estimate. That fork goes to the operator.
- Either way: real `#print axioms` on every probe theorem (expect `sorryAx` + the 3 canonical —
  **NO new `axiom` declarations**), verdict file, commit, STOP.

## Forbidden

- Proving the full running-family `cutReduceAllAux` (a 1.6M-heartbeat monster) beyond what the
  probe needs — the question is the COMPOSITION arithmetic, not the reduction port.
- Grinding the seven mechanical cases, the rank-0 twins, or anything in the W4 phase proper.
- `src/` edits; new `axiom` declarations; LOCK files; `DIRECTION.md`; building the `Zᵉ` redesign
  (FAIL pins it, the operator green-lights it); someK-level induction.
- Run only when no other session/box is live on this tree (bind-mount races).
