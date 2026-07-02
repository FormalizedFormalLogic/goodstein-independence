# E — JUDGE validation of SPIKE-W4B (Ren, 2026-07-02)

> Host-side judge pass on the W4B spike (`862ff8f`), per the don't-trust-box-handoffs rule.
> Companion to the W3/W4 judge docs. A FAIL verdict carries the highest stakes of the three —
> it mandates a calculus redesign — so this pass hunted specifically for strawman refutations
> and uncounted escapes. It found neither. **FAIL is RATIFIED; T-W4B has fired.**

## 1. Independently re-verified

- `lake env lean wip/SpikeW4BBudget.lean` → **exit 0**; exactly **ONE** sorry (`:101` — the §1
  statement pin, by design); all 12 in-file `#print axioms` lines match the verdict's table
  **verbatim** (`sorryAx` appears ONLY on the pin and on `probe_cut_all_arm`, whose sole
  possible source is the pin — there is literally one sorry in the file). No new `axiom`
  declarations. `two_level_config` and every seam/dodge refutation are sorry-free.
- Commit `862ff8f` scope: the probe + verdict + lap-173 baton only. No `src/` edits, no LOCK,
  no `DIRECTION.md`, stopped after the verdict. Forbidden-list discipline held.
- The concurrent-session concern the box flagged: it was the blueprint session
  (`30414b0`/`bf2cec0`, disjoint paths); all commits landed cleanly; tree is clean.

## 2. Faithfulness checks (the strawman hunt)

- **The pin is the banked statement, honestly generalized**: `cutReduceAllAuxRunning` =
  `OperatorZinfty.lean:789` with the family at the running index — and the probe's `fam`
  construction from `Zekd.allInv` **type-checks**, so "this is exactly what `allInv` hands the
  recursion" is kernel-verified, not asserted. The control raise makes the pin the most
  generous plausible member of its class (disclosed caveat (ii) is correctly one-directional:
  generosity can only weaken a FAIL).
- **Rail-minimality, hand-verified**: with output ordinal class `osucc (α + γ)` and the wrapper
  needing `norm(output) < k + slot`, the budget `dd + norm α + 1` is *exactly* minimal —
  `dd + norm α` fails by equality (`norm γ ≤ k + dd − 1` gives output norm up to
  `norm α + k + dd`, and `<` demands the `+1`). So the pin neither over- nor under-pays; a
  smaller-budget statement is not honestly statable for this output class
  (`rail_norm_genuinely_carried` + parametric `dodge_a`).
- **The probe's "motive demands" are the real SPIKE-W4 motive**: `probe_cut_all_arm`'s IHs are
  `operatorCutElimStepAux`'s IH shape at a branch position, verbatim (slot `d + norm e + 1`,
  control `raise e βφ`, index `max k nBr`). No convenient variant.
- **Non-vacuity is genuine**: `two_level_config` is a legal, sorry-free `Zekd` derivation with
  branch-`n` principal-cut premise norms `n + 1` — legal precisely by the rules' own
  `max k n + d` slack. The "that configuration can't arise" objection is dead in-kernel.
- **The refutations are parametric, not single-point**: `dodge_a` over every constant `C`,
  `seam2` over every slot `D` (hence every structural functional evaluated at the fixed
  configuration), `dodge_c` over every `(k, B ≥ 1)`. Form (d) (subtree-weight) is subsumed by
  `seam2`'s arbitrary-`D` quantification.

## 3. Escapes hand-closed beyond the file

- **The low-norm re-anchor escape** (not an explicit lemma; closed by the calculus itself):
  weakening the overflowing output up to a big-but-low-norm ordinal (e.g. `ω^ω`, norm 1) does
  not dodge the budget — `Zekd.weak`'s own `hτ` demands the SOURCE ordinal's norm fit the
  budget at that node, so the high norm is paid once regardless. This is the verdict's
  slope-1/slope-2 argument made concrete: every rule is affine in the branch index with slope
  1, and no rule lowers `d`, `k`, or norm-obligations retroactively.
- **The doubled-raise motive on the control axis**: my arithmetic suggests a motive concluding
  at control `raise (raise e B) (expTower B)` *could* unify the branch controls at an
  enlarged-but-structural `mono_e` budget — i.e. the control axis alone may not be fatal for
  every conceivable motive, slightly narrower than the verdict's "fails on BOTH axes" phrasing.
  **Moot**: `seam2` (the `d`-slot) kills any such motive independently, and the kernel
  refutations of the pinned shapes (`control_seam_overshoot`, `control_exponent_escape`) stand
  as stated. The load-bearing axis is the `d`-seam, and it is clean. (The verdict's
  hardy-of-hardy witness-insufficiency note is correctly flagged as analysis, not load-bearing.)

## 4. Honest scope of the FAIL (what "kernel-confirmed" means here)

The kernel refutes the composition inequality of **every statement shape in the probed space**
(uniform / enlarged-uniform / ordinal-indexed / `k`-rebalanced / subtree-weight slots; pinned
and re-based raise shapes on the control side) against the **rail-admissible reduction class**.
It does not — cannot — refute statement shapes outside per-node numeric budgets; but the
standing doctrine (budgets in a motive are functions of structure) plus the probe's result (no
such function exists at this node) makes any escape definitionally the `Zᵉ` fork. Decisive
corroboration: this is not a novel wall — it is the exact phenomenon Buchholz built
operator-controlled derivations FOR, and the repo's own `OperatorZinfty.lean:764` SCOPE block
predicted its witness-half a month before the `d`-half was confirmed. Three independent seams
failing with the same signature, on a literature-predicted wall, with the literature's own tool
pre-named — that is as confirmed as a design question gets short of a full impossibility
theorem, which the W4B order never asked for.

## 5. The `Zᵉ` pin — ratified as the fork content

- The design (judgment `Zeh α e H c Γ`, `H` closed under `+`/`ω^·`/`osucc`/`ofNat`, ω-premises
  at `H[n]`, numeric side conditions → `∈ H`) matches Buchholz–Wainer and the `:764` block's own
  recommendation; the closure argument kills both confirmed seams simultaneously and is the
  literature's argument, not an invention.
- Carries-over list is credible and specific (the control axis is untouched by `H`, so
  SPIKE-W4's `raise` + `step_allω` survive; the 12-case skeleton is rule-driven, not
  budget-driven; the `:764` block already records the reduction cases carry to the `H`-calculus
  verbatim except the witness side conditions). The rebuild list (~2600-line re-threading with
  the norm-plumbing DELETED) is plausibly a simplification, not just a port.
- **The new headline risk is real and correctly sequenced**: Σ₁-definability of the concrete
  `H` instance at the M2-bridge exit — spike it FIRST, as the verdict mandates. The first `Zᵉ`
  session must be deciding experiment #4 (re-run THIS probe's two seams as `Zeh` statement
  forms + the Σ₁-instance statability), NOT a grind.
- Estimate: 7–11 laps replacing W4's 5–10. Calibration note for the operator: the repo's
  estimate culture runs 2–4× optimistic on grind laps, though the three spikes have landed
  1-session-accurate — read the envelope as ~7–20 laps, tightened after the `Zeh` seam-spike.

## 6. Effect on the masterplan

- Hard bet #2 resolves AGAINST the `(k, d)` numeric calculus and INTO the pre-registered
  fallback. The masterplan's "with the `Zᵉ` fallback ~70–75%" branch is now the mainline;
  subtract something for the newly-surfaced Σ₁-definability-of-`H` risk until its spike lands
  (call it ~65–75%, spike-gated). The W4 phase estimate is replaced, not added to.
- The halt discipline worked exactly as designed: zero laps were spent grinding mechanical
  cases or rank-0 twins on a motive that is now known re-keyed — the residual-first sequencing
  (W4 verdict → W4B order) saved the entire would-be sunk cost, and firing T-W4B cost one
  session instead of 20 laps.
- Do NOT start any W-ladder grind on the `(k, d)` motive. The decision in front of the
  operator is the pre-named fork: **green-light the `Zᵉ` redesign (first session = the `Zeh`
  seam-spike) or abandon per the 2026-07-01 mandate.** Judge recommendation: green-light — the
  wall is the literature's wall, the tool is the literature's tool, the carried assets are
  majority, and the abandon criterion (both triggers fired AND the fallback failing) is not
  met: T-W4B firing is the mechanism selecting the fallback, not the fallback failing.
