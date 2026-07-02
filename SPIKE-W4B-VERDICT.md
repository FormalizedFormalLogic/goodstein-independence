# SPIKE W4B — VERDICT

> Deciding experiment #3 (`SPIKE-W4B-BUDGET.md`), resolving the residual located by
> `SPIKE-W4-VERDICT.md` §"the residual". One bounded session. Deliverable: kernel probe
> `wip/SpikeW4BBudget.lean` + this verdict.

## Verdict: **FAIL — the overflow kernel-confirms. T-W4B FIRES.**

The one open design question — *does the numeric `(k, d)` budget calculus admit ANY
statement-level fix for the principal ∀/∃ cut's `d`-bump under an enclosing ω-node?* — is
answered **NO**: for every candidate statement shape (the work order's three dodges, the
uniform-slot baseline, plus one discovered shape), the failing inequality is reduced in the
kernel to a checked counterexample or a named unsatisfiable side condition. The masterplan's
pre-registered fallback fork — **Buchholz operator-controlled derivations (`Zᵉ`)** — is hereby
pinned (NOT built) and goes to the operator. Firing on day 1 instead of 20 laps into the W4
grind is the spike's designed win condition.

## What was built (evidence)

`wip/SpikeW4BBudget.lean` — elaborates green under the repo toolchain
(`lake env lean wip/SpikeW4BBudget.lean`), ONE `sorry` (the §1 statement pin, by design),
**no new `axiom` declarations, no `src/` edits**. Real `#print axioms`, in-file:

```
cutReduceAllAuxRunning         [propext, sorryAx, Classical.choice, Quot.sound]  (the pin)
rail_norm_genuinely_carried    [propext, Quot.sound]
dodge_a_norm_not_sheddable     [propext, Quot.sound]
two_level_config               [propext, Classical.choice, Quot.sound]
probe_cut_all_arm              [propext, sorryAx, Classical.choice, Quot.sound]  (via the pin ONLY)
seam1_uniform_slot_unpayable   [propext, Quot.sound]
seam2_no_uniform_slot          [propext, Quot.sound]
dodge_b_slot_not_monotone      [propext, Classical.choice, Quot.sound]
dodge_b_allomega_unbridgeable  [propext, Classical.choice, Quot.sound]
dodge_c_k_rebalance_escapes    [propext, Quot.sound]
control_seam_overshoot         [propext, Classical.choice, Quot.sound]
control_exponent_escape        [propext, Classical.choice, Quot.sound]
```

- **The pinned running-family reduction** (`cutReduceAllAuxRunning`, body `sorry`): banked
  `cutReduceAllAux` generalized to the running family `fam : ∀ n, Zekd α e (max k₀ n) dd₀ c …`
  (exactly `allInv`'s output shape), control raised per SPIKE-W4's `raise`, output ordinal
  `osucc (α + γ)`, output budget `dd + norm α + 1` — the **rail-minimal** budget for that output
  class (see the rail below; any smaller budget is a fake statement).
- **Non-vacuity** (`two_level_config`, sorry-free): the two-level configuration is a REAL `Zekd`
  derivation — one `allω` node at `ω^ω`, `(k,d) = (0,3)`, whose EVERY branch `n` is a rank-`c`
  principal ∀/∃ cut with premise ordinals `ω·(n+1)` of norm `n+1`: the residual's
  branch-unbounded quantity realized in the kernel, legal by the rules' own `max k n + d` slack.
- **The composition probe** (`probe_cut_all_arm`, a REAL proof): the ∀/∃ arm of
  `step_cut_principal` at an ω-branch consuming the pin's output. It kernel-checks the seam-1
  max-algebra end-to-end (the `mono_e` control-unification budgets, `allInv`'s running index
  feeding the pin's family shape exactly, the reduction application, sequent cleanup) and
  records what the arm CAN emit: slot `(d + norm e + 1) + norm αf + 1` at control
  `raise (raise e B) αf`, with `norm αf` bounded ONLY branch-dependently
  (`< max k nBr + d + norm e + 1`, the wrapper's carried clause). The motive demands slot
  `d + norm e + 1` at control `raise e B`.

## The failing inequality, per attempted shape (FAIL criterion)

| Shape | Required inequality (at the seam) | Kernel refutation |
|---|---|---|
| Uniform slot `d + norm e + 1` (SPIKE-W4's) | `dd_in + norm αf + 1 ≤ dd_in` | `seam1_uniform_slot_unpayable`: false for EVERY bump value, even 0 — `Zekd` has no `d`-lowering |
| ANY enlarged uniform slot `D(e,d,k)` | `∃ D, ∀ n, dd_in + norm (ω^(ω·(n+1))) + 2 ≤ D` | `seam2_no_uniform_slot`: branch-`n` slot grows like `n`; `Zekd.allω` accepts ONE `d` (constructor syntax — named unsatisfiable side condition) |
| **(a)** tighter output norm (shed `norm α`) | `norm (osucc (α + γ)) ≤ norm γ + C` | `dodge_a_norm_not_sheddable`, **parametric in `C`**: `norm (osucc (ω·(C+2) + ω)) = C+3 > 1+C`. Equal-exponent CNF merge is additive in the head coefficient (`rail_norm_genuinely_carried`): the `norm α` contribution is genuinely carried by the output ordinal, not bookkeeping |
| **(b)** ordinal-indexed slot `d + norm e + norm α + 1` | seam ①: `norm β ≤ norm α` for premise `β < α`; seam ②: premise slots bounded across the ω-family | `dodge_b_slot_not_monotone`: `ω·2 < ω^ω` with norms `2 > 1` — `norm` is not `<`-monotone, so the premise IH sits at a STRICTLY larger slot than the node at `weak`/`andI`/`orI`/`cut`/`allω`; `dodge_b_allomega_unbridgeable`: over the legitimate family `ω·(n+1) < ω^ω` the premise norms are unbounded — `mono_d` (raising-only) + wrapper slack cannot bridge (the work order's "sharpest single kernel check") |
| **(c)** rebalance into the `k`-slot | `max k n + B ≤ max (k+B) n` | `dodge_c_k_rebalance_escapes`: fails at `n = k+B+1` for every `k` and every bump `B ≥ 1`; `Zekd.allω` premises sit at EXACTLY `max k_node n` and there is no index-lowering (semantic form banked at `OperatorZinfty.lean:764`: `h_{βₙ#ω}(max{k,n}) ≰ max{h_{β#ω}(k),n}`) |
| **(d)** (discovered) subtree-weight-indexed slot | node weight ≥ sup of ω-branch weights | same seam-2 unboundedness: the sup over an ω-branching family of growing weights does not exist as a ℕ-slot — named unsatisfiable side condition |

**Control-side findings (secondary, statement-time):** the pinned raise-shape ALSO fails to
compose — `control_seam_overshoot`: `E < raise E X` unconditionally, so the reduction's output
control can never re-enter the motive's single raise `raise e B` (`mono_e` raises only); and
`control_exponent_escape`: re-basing the raise at the original `e` with exponent the fam ordinal
`αf` escapes too (`βφ = 1 < B = 2` but `αf = ω^1 = ω > 2`). Analysis flag (not load-bearing for
this verdict): the raise the witness half genuinely needs is hardy-of-hardy-sized
(`hardy e' ≳ hardy e ∘ hardy e`, i.e. `ω^X ≳ e` — not implied by any structural `X`), so the
control slot has the same branch-dependence disease as the `d`-slot. This SHARPENS the W4
verdict: its "control raise carries over unchanged" holds for the traversal, but at the
principal ∀/∃ node the numeric calculus fails on BOTH axes.

## Why this is a genuine kernel confirmation (and its honest scope)

The residual's overflow is now **structural, not accounting**: every `Zekd` rule is affine in
the branch index with slope 1 (`max k n + d`), while the reduction's output demands — the
output-wrapper norm (`norm α + norm γ`, both reaching their budgets: slope 2) and the ω-node's
uniform-`d` re-entry — cannot be expressed at slope 1 by ANY function of the statement's data
`(α, e, k, d, c)`. The kernel checks refute the composition inequalities of every statement form
in the probed space (uniform / ordinal-indexed / `k`-rebalanced / subtree-weight slots; the
pinned raise class on the control side). What the probe does NOT do: prove the step statement
FALSE (on trivial sequents it is true), or exclude recursion restructurings that abandon
per-statement numeric budgets — but any such restructuring IS the `Zᵉ` fork by definition
(doctrine: budgets in a motive must be functions of structure; the probe shows no such function
exists at this node).

**Where the admissibility rail was load-bearing:** (i) pinning §1's output budget at
`dd + norm α + 1` (rail-minimal — `rail_norm_genuinely_carried` shows the output ordinal's OWN
norm reaches `norm α + norm γ` exactly, so no smaller budget is honestly statable); (ii) killing
dodge (a) — without the rail, "shed `norm α_fam` as bookkeeping" would have been a fake PASS.

## The `Zᵉ` pin (T-W4B consequence — design pinned, NOT built; operator green-lights)

**What replaces `(k, d)`.** A control SET `H` (Buchholz operator-controlled derivations;
`papers/buchholz-beweistheorie-skriptum.pdf` on disk, cf. Buchholz–Wainer 1987): judgment
`Zeh α e H c Γ` with `H : ONote → Prop` (a represented, countable, `≤`-downward-irrelevant
operator) **closed under `+`, `ω^·` (`expTower`), `osucc`, `ofNat`**, containing the derivation
parameters. Every numeric side condition `norm β < k + d` becomes `β ∈ H`; the ω-rule premise
`n` runs at the relativization `H[n]` (adjoin `ofNat n` and close — the literature's `H[Θ]`);
the `exI` witness bound stays hardy-based on the control ordinal `e` (the numeric argument
supplied by `H`'s finite part, e.g. `n ≤ hardy e m` for some `m ∈ H ∩ ℕ`). **Why this kills the
confirmed seams simultaneously:** the splice ordinal `osucc (α_fam + γ)` lies in `H[n]` by
CLOSURE from `α_fam, γ ∈ H[n]` — there is no numeric bump to absorb (seam 1 gone), and the
ω-node re-assembles because every branch's output is `H[n]`-controlled, which is exactly the
ω-rule's premise form (seam 2 gone); "premise norms in budget" → "premise ordinals in `H`" is
stable under the reduction.

**Carries over unchanged.**
- SPIKE-W4's `raise` + the `step_allω` argument: the control axis `e` is untouched; `mono_e`'s
  numeric gate `norm e ≤ k + d` becomes `e ∈ H`; the uniformization mechanism
  (`raise_lt_raise` + per-branch `mono_e` lift) is verbatim.
- The 12-case skeleton shape + the `c' = c + 1` rank threading + root-only someK discipline
  (`wip/SpikeW4CutElim.lean`) — the case split is rule-driven, not budget-driven.
- The unbounded template (`ZinftyGen.lean:1547–1694`) and the banked `cutReduceAllAux`
  STRUCTURAL port — the `:764` SCOPE block already records: "every case carries to the
  `H`-calculus verbatim except the `exI`/`allω` witness side-condition".
- The Hardy bank (`hardy_add_collapse`, `hardy_le_of_lt`, `hardy_monotone`) and the §19.5
  `cutReduceConj/Disj` argument shapes.

**Must be rebuilt.**
- The inductive core (`Zekd` → `Zeh`) + structural layer: `mono_k`/`mono_d` collapse into
  `H`-monotonicity (`H ⊆ H' →`), `mono_e`/`mono_c`/`weakening` re-threaded; the ~15-lemma
  inversion suite (`orInv`/`andInv*`/`allInv` + the two §19.5 reductions + §19.6) — mechanical
  re-threading over `OperatorZinfty.lean`'s ~2600 lines, with the norm-budget plumbing DELETED
  rather than ported (a simplification: the 3-move norm-wrapper machinery of the `:775` block
  exists only to serve the numeric shadow).
- The `H`-machinery itself: representation (concrete `H`s as hardy-/norm-definable sets),
  closure lemmas, relativization `H[n]`.
- The M2-bridge exit: witness extraction must re-derive `witness ≤ hardy e (·)` from the
  `H`-form at ONE concrete instantiation — the **Σ₁-definability of that concrete `H` is the
  new headline risk, to be spiked FIRST** (crux-2 discipline: per-instance, no universal
  evaluator — cf. the banked `prwoInstance` precedent).

**Lap estimate.** 1 spike lap (re-run THIS probe's two seams as `Zeh` statement forms — the
deciding experiment BEFORE any grind, verifying closure really absorbs both seams and the
Σ₁-instance is statable) + 4–7 laps calculus/structural/inversions + 2–3 laps re-landing the
two banked reductions and the W4 step skeleton on `Zeh` ≈ **7–11 laps**, replacing (not adding
to) the current W4 phase estimate.

## Bottom line for the masterplan

The W4 phase as sequenced is **correctly halted at its first task**: do NOT grind the seven
mechanical cases, the rank-0 twins, or the running-family port on the `(k,d)` motive — all
would be re-keyed by the fork. The residual is no longer "analysis": both seams and every
in-space dodge are kernel-refuted. The decision in front of the operator is the pre-named one:
green-light the `Zᵉ` redesign (pinned above), with SPIKE-W4's control-raise assets and the
skeleton carrying over, and the first `Zᵉ` lap being the re-run of this very probe.
