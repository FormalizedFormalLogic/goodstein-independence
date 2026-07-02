# REBUILD-Z LAP 178 — FINDING: the Hardy additive identity has an ABSORPTION WALL

> Scope: permitted-sibling probe of the P1 raised-control obligation, under the lap-177 precedent
> (`NormControlled.comp` / `normControlled_exists_trivial` — facts about STABLE `hardy`/`+` defs,
> consuming no f-slot pin, touching no gated pin body, ruling on no judge Option-A/B question).
> Work site: `wip/HardyAddProbe.lean` (evidence artifact, not in the build target). No `src/` edit,
> no pin touched. Build unchanged: `lake build` green, 1333 jobs, `OperatorZeh` exactly 3 §5 pins.

## The question

`cutElimPass_Zf`'s conjunct is `NormControlled f' (raise e α') m`, and
`raise e α' = e + expTower α' = e + ω^{α'}`.  The tempting discharge: the classical additive Hardy
identity `H_{e+β} = H_e ∘ H_β` would exhibit `f' := hardy e ∘ hardy (ω^{α'})` as a CONCRETE E–W
iterate slot, collapsing the pin-3 "transfinite iterate `f ↦ f^{…}`" (judge Q2) to a single,
already-defined composition of `hardy`.

## The finding (kernel-verified in `wip/HardyAddProbe.lean`, sorry-free)

**The UNCONDITIONAL identity `H_{e+β} = H_e ∘ H_β` is FALSE.**  It splits by the shape of the right
summand `β`:

- **Successor / finite `β`: TRUE, unconditional.**
  - `fundamentalSequence_add_succ` (NEW, proven): if `β` is the notation-successor of `β'`, then
    `e + β` is the notation-successor of `e + β'` — for ALL `e` (even absorbing ones), because
    `repr (e+β) = succ (repr (e+β'))` is always a successor with a unique predecessor, and
    `FundamentalSequenceProp` forces `fundamentalSequence (e+β)`'s shape (neither `0` nor a limit).
  - This is the notation-level generalization of the banked, load-bearing
    `hardy_add_ofNat` (`Hardy.lean:1257`, `H_{α+c}(n) = H_α(n+c)`, used in `LowerBound.lean`) — the
    finite/no-absorption slice.

- **Limit `β` under ABSORPTION: FALSE.**  Kernel `rfl` witnesses:
  - `add_omega_absorbs : (1 : ONote) + ω = ω`  (`ω = oadd 1 1 0`).
  - `fundamentalSequence_absorbs : fundamentalSequence (1+ω) = fundamentalSequence ω`.

  So `H_{1+ω} = H_ω`, whereas `H_1 ∘ H_ω = (·+1) ∘ H_ω ≠ H_ω`.  The would-be limit-branch fs
  homomorphism `fundamentalSequence (e+β) = inr (fun i => e + f i)` fails: the actual sequence is
  `f` itself (`f 0 = ofNat 1`), while `1 + f 0 = ofNat 2 ≠ f 0`.

## Consequence for the crux (P1 / judge Q1–Q2)

The `raise` in cut-elimination GROWS the control by `ω^{α'}`, with `α'` the cut/height ordinal —
the regime where `ω^{α'}` **absorbs** `e`.  That is exactly the FALSE regime above.  Under
absorption `hardy (raise e α') = hardy (e + ω^{α'}) ≈ hardy (ω^{α'})`, which does NOT see the input
control `hardy e` at all.  Therefore:

1. **Additive decomposition does NOT discharge P1.**  The raised-control obligation is not an
   algebraic identity in `hardy e`; it is the genuine fast-growing DOMINATION
   `hardy (ω^{α'}) (·) ≤ (iterate of the input slot)` — E–W Lemma 19 / the `f ↦ f^{F^{α'}(0)}`
   iterate.  The iterate index in pin 3 (`cutElimPass_Zf`, judge Q2) is therefore *essential*, not
   an abstraction to be collapsed to a composition.  This is a NEGATIVE result that closes off the
   "collapse `f'` to `hardy e ∘ hardy(ω^{α'})`" shortcut.
2. **Corroborates the BW87 cut-free fallback** (`readoff_sigma1`, proven): if the fast-growing
   domination stays hard, the pre-validated escape is the cut-free read-off, not an additive trick.
3. **Bears on judge Q1** (locus of the P1 conjunct): the domination is inherently a per-α' /
   per-instance fast-growing bound, favoring the headline-shape per-instance obligation over an
   in-motive conjunct that would (falsely) suggest an algebraic composition suffices.

## What is banked (all in `wip/HardyAddProbe.lean`, `#print axioms`-clean, no `sorry`)

| name | statement | status |
|------|-----------|--------|
| `onote_add_zero` | `o + 0 = o` (NF) | proven |
| `fundamentalSequence_add_succ` | successor fs homomorphism, unconditional | proven (NEW) |
| `add_omega_absorbs` | `1 + ω = ω` | `rfl` |
| `fundamentalSequence_absorbs` | fs collapses under absorption | `rfl` |

`fundamentalSequence_add_succ` is a clean, reusable general ONote lemma (mathlib-PR-shaped, next to
`fundamentalSequence_oadd_succ`); relocate to `Hardy.lean` if a later lap needs the successor
homomorphism outside the finite slice.  The refutation is why the LIMIT homomorphism is NOT banked
(it is false), and why nothing was pushed to `src/`.

---

## ADDENDUM (same lap) — lap-177's "no fast-growing `F`" is WRONG; the real bridge is a DOMINATION

Chasing the surviving route (E–W Lemma 19, the fast-growing side), I checked lap-177's premise that
"the substrate has `norm` but no fast-growing `F` and no iterate `f^k`."  **That is false.**
`ONote.fastGrowing : ONote → ℕ → ℕ` is defined in mathlib and the repo carries its full growth
theory (`Hardy.lean` §Basic: `le_fastGrowing`, `fastGrowing_le_of_reaches`, `fastGrowing_*`), and
`f^k` is just `Function.iterate`.  So E–W Lemma 19 is STATEABLE with existing stable-def machinery —
no new cut-elim definitions required for the fast-growing bound itself.

The repo's own B4 note (`Hardy.lean:1082`) calls the connecting identity `H_{ω^α} = f_α`.  **That
EQUALITY is kernel-FALSE, off by TWO successive shifts** (two more convincing-identity traps caught
this session):
1. `H_{ω^1}(3) = 7 ≠ 6 = f_1(3)` (`native_decide`).  The shifted `=` is
   `hardy(oadd α 1 0) n + 1 = fastGrowing α (n+1)` (`#eval`-anchored α ∈ {0,1,2}; α=2 data
   hardy = 7,23,63 vs fastGrowing(n+1) = 8,24,64 — exact −1).
2. **Even that `=` holds ONLY at successor/finite exponents.**  At a LIMIT exponent `α` (fund. seq.
   `f`), `H_{ω^α}(n) = H_{ω^{f n}}(n)` uses `f n` while `f_α(n+1) = f_{f(n+1)}(n+1)` uses
   `f(n+1) > f n`, and `fastGrowing` is strictly ordinal-monotone — so the LHS is STRICTLY smaller.
   (`fastGrowing ω`-scale values are too large to `#eval`; the strict-monotone argument is decisive.)

So the UNCONDITIONAL, load-bearing truth is the INEQUALITY

    hardy (oadd α 1 0) n + 1 ≤ fastGrowing α (n + 1)     -- H_{ω^α}(n) < f_α(n+1)

— which is EXACTLY the upper bound P1 needs.  **Consequence for P1:** in the absorbing regime the
raised control is `≈ hardy(ω^{α'})`, and this bound (`hardy_omega_pow_lt_fastGrowing`, proven from
the target) REDUCES P1's raised-control domination to E–W Lemma 19 in the form
`fastGrowing α' (n+1) ≤ (iterate of the input slot)` — a fast-growing bound stateable/attackable with
existing stable-def machinery.

Banked in `wip/HardyFastGrowingBridge.lean` (out of build target): the `≤` TARGET
`hardy_omega_pow_add_one_le` (**base case α=0 AND the LIMIT case proven** — the limit via IH +
`fastGrowing_bachmann_reach`/`fastGrowing_le_of_reaches`; the SUCCESSOR case α=β+1 is the sole open
sorry, needing the coefficient intermediate `H_{ω^β·(m+1)}(n) + 1 = f_β^{[m+1]}(n+1)`, kernel-verified
β∈{0,1}, provable by induction on the coefficient with base = the outer IH at β — the classical
Cichoń–Wainer core), the corollary `hardy_omega_pow_lt_fastGrowing`, and `native_decide` anchors
(incl. the equality-is-false anchor so no lap re-attempts `H_{ω^α} = f_α`).  This REOPENS a concrete,
permitted, stable-def attack path on the P1 domination that lap-177 wrongly declared closed —
the `≤` bridge is grindable now as B4 (finish the successor case), Lemma 19 + pin-3 wiring stay
judge-gated.
