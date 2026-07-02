# SPIKE Z1 — the `Zᵉ` seam + Σ₁-instance spike (operator-commissioned, 2026-07-02)

> **One bounded session. Deliverable = a minimal `Zeh` statement core + TWO kernel probes + a
> binary verdict. NOT a proof campaign, NOT the calculus rebuild.** Deciding experiment #4,
> the first session of the operator-green-lit `Zᵉ` fork (2026-07-02, after T-W4B fired). It
> answers the ONLY two questions that decide whether the fork is real, BEFORE any re-threading
> grind: (1) does operator-set closure actually absorb both kernel-confirmed W4B seams, and
> (2) is the concrete `H` instance workable at the witness read-off (the new headline risk)?
> Pre-registered trigger **T-Z1** (below) — if it fires, the fork goes back to the operator
> with abandon on the table.

## Context (read first, in order)

- `SPIKE-W4B-VERDICT.md` — the FAIL + **the `Zᵉ` pin** (your design brief: `Zeh α e H c Γ`,
  `H` closed under `+`/`ω^·`(`expTower`)/`osucc`/`ofNat`, ω-premises at the relativization
  `H[n]`, numeric side conditions `norm β < k + d` → `β ∈ H`); the two seams you are re-running.
- `E-2026-07-02-JUDGE-spike-w4b-validation.md` — esp. §3 (the low-norm re-anchor escape is
  closed by side conditions: your `Zeh` rules must preserve that property — every rule demands
  its ordinals ∈ H, no retroactive absolution) and §5 (what carries, what rebuilds).
- `wip/SpikeW4BBudget.lean` — the probe you are mirroring: `two_level_config` (re-use its
  shape), `probe_cut_all_arm` (the seam-1 composition you are re-running), §1's pin discipline
  (sorried reduction, admissibility rail).
- `wip/SpikeW4CutElim.lean` — `raise`/`expTower` + `step_allω` (carries over: the control axis
  is untouched by `H`).
- `src/GoodsteinPA/OperatorZinfty.lean:756–800` — the `:764` SCOPE block ("every case carries
  to the `H`-calculus verbatim except the `exI`/`allω` witness side-condition") + the banked
  `cutReduceAllAux` whose `Zeh` twin you pin.
- `papers/buchholz-beweistheorie-skriptum.pdf` + `papers/buchholz-wainer-1987-…` — the
  literature's operator-controlled derivations; ground the rule forms there (`H[Θ]`
  relativization). The banked `prwoInstance` precedent for per-instance Σ₁ discipline.

## Standing doctrine (three spikes' traps — do not re-hit)

Existentials open at the ROOT only, never inside an induction. The control `e` is constant
through a derivation. Branch dependence enters ONLY via the relativization `H[n]` (the `Zᵉ`
analog of `max k n`). Budgets/side conditions in a motive are functions of structure — in
`Zeh`, "structure" includes `H` itself, which is the whole point: closure makes the previously
branch-dependent quantities *members*, not *bounds*.

## The two deciding questions

**Q1 (seams).** W4B kernel-refuted the `(k,d)` composition at two seams: (seam 1) the ∀/∃
reduction's output demands a budget bump `norm α_fam + 1` that no structural slot absorbs;
(seam 2) `Zekd.allω` demands ONE `d` while branch demands grow unboundedly. The `Zᵉ` pin claims
closure kills both: the splice ordinal `osucc (α_fam + γ)` lies in `H[n]` **by closure** from
`α_fam, γ ∈ H[n]` (no bump exists to absorb), and the ω-node re-assembles because "every
branch's output is `H[n]`-controlled" IS the ω-rule's premise form. **Show both, in-kernel, as
REAL proofs at the seams** (reduction pinned sorried, per the W4B discipline).

**Q2 (the concrete `H` / read-off).** The M2-bridge exit needs witness extraction at ONE
concrete `H`: from the `Zeh` form, recover a NUMERIC witness bound (`≤ hardy e m`-shaped) at
the headline instantiation — per-instance, NO universal evaluator/truth predicate
(`prwoInstance` discipline). **Show the concrete `H` is workable**: representation + closure +
the bounding read-off statable, with the closure-to-hardy bounding lemma PROVEN on at least a
small concrete case.

## Objective

In `wip/SpikeZ1Seams.lean` (new file; `wip/` only, no `src/` edits):

1. **Pin the minimal `Zeh` core** (an inductive in the spike namespace, mirroring `Zekd`'s
   constructors with the numeric side conditions swapped for `H`-membership). Minimal =
   exactly the rules the probes need: `axL`, `allω` (premises at `H[n]`), `exI` (witness bound
   hardy-based per the pin: `n ≤ hardy e m` for a designated `m` with `ofNat m ∈ H` — confront
   this design point explicitly), `cut`, `weak` (source ordinal ∈ H — the judge's re-anchor
   closure), plus a `mono_H` (`H ⊆ H' →`) in place of `mono_k`/`mono_d`. Carry `IsOperator H`
   as a structure bundling the closure conditions; define the relativization `H[n]` (adjoin
   `ofNat n`, close — or an inductive-closure formulation where `H[n]` is generation from
   `gen ∪ {ofNat n}`). The `ZekdProv` norm-wrapper has NO twin — deleting it is the
   simplification the fork buys; the judgment carries `α ∈ H` directly.
2. **Q1 probe** — mirror W4B §4 on `Zeh`:
   - Pin the `Zeh` running-family reduction (body `sorry`; same admissibility discipline —
     the output ordinal class stays `osucc (α + γ)`, the output control stays SPIKE-W4's
     `raise e α`; what changes is ONLY that the budget slot is replaced by
     `osucc (α + γ) ∈ H[…]`-membership, which your closure lemmas must DERIVE, not assume).
   - `probe_cut_all_arm_Zeh`: the ∀/∃ arm at an ω-branch consuming the pin — a REAL proof
     emitting IN the motive's form (this is the seam-1 reversal: where W4B recorded an
     unabsorbable bump, you derive membership by closure).
   - `probe_allomega_reassembly_Zeh`: the ω-node re-assembly over a branch-family whose W4B
     analog was unbounded (re-use `two_level_config`'s family shape `ω·(n+1)`) — a REAL proof
     (seam-2 reversal).
   - **Anti-fake-PASS rail**: the closure obligations discharged at the seams must come from
     `IsOperator`'s conditions (kernel-checked closure lemmas), NEVER from a sorried
     membership. Sorries are allowed ONLY in the reduction pin's body and clearly-flagged
     grind-shaped leaves (list them in the verdict); every seam-crossing membership fact must
     be a real proof.
3. **Q2 probe** — ONE concrete represented `H`:
   - Define it (recommended shape: an inductive closure `InH gen : ONote → Prop` — generators
     + one constructor per operation; membership witnesses are finite trees; relativization =
     generation from `ofNat n :: gen`). Prove `IsOperator (InH gen)`.
   - Prove the **bounding read-off lemma on a small case**: from an explicit membership tree,
     extract the numeric bound (e.g. every `β ∈ InH gen` with `β` a numeral satisfies
     `toNat β ≤ hardy e m` for a structure-determined `m` — or the honest analog the papers
     support; state what Buchholz–Wainer actually licenses). Kernel-check it on at least one
     concrete instance (`decide`/explicit tree).
   - State (sorry allowed, statability is the test) the headline-instantiation read-off: the
     `Zeh` root at the concrete `H` yields the `≤ hardy e (·)` witness bound the W5/M2 exit
     consumes. If this CANNOT be stated without a universal evaluator / truth predicate /
     non-arithmetic quantification — that is a FAIL finding, name it precisely.

## Verdict criteria — write `SPIKE-Z1-VERDICT.md`, then STOP

- **PASS** = both Q1 probes are REAL kernel proofs (seams close by closure, no sorried
  membership at any seam) AND Q2's concrete `H` has proven closure + a proven small-case
  read-off + a statable headline read-off. State the pinned `Zeh` rule forms (they become
  binding for the rebuild), every disclosed sorry, and anything the probes surfaced that
  re-scopes the ~7–11-lap estimate.
- **FAIL (T-Z1 fires)** = either (i) a seam does NOT close under the pinned closure conditions
  (name the missing closure operation precisely — if a finite extension of `IsOperator` fixes
  it, that is an AMENDMENT, not a FAIL; FAIL means no finite closure-condition set suffices),
  or (ii) the Q2 read-off genuinely requires a universal evaluator / leaves the per-instance
  Σ₁ discipline (name the obstruction; assess whether a different concrete `H` representation
  dodges it). T-Z1 goes to the operator with the abandon branch live — `Zᵉ` was the
  pre-registered fallback; there is no fallback-to-the-fallback pinned.
- Either way: real `#print axioms` on every probe theorem (expect `sorryAx` only via the
  disclosed pins + the 3 canonical — **NO new `axiom` declarations**), verdict file, commit,
  STOP.

## Forbidden

- Re-threading `OperatorZinfty.lean` / building the inversion suite / porting the reductions —
  that is the rebuild grind (laps 2+), gated on THIS verdict.
- `src/` edits; new `axiom` declarations; LOCK files; `DIRECTION.md`; grinding past the
  mandate; someK-style existentials inside inductions.
- Run only when no other session/box is live on this tree (bind-mount races — check
  `git status` is clean and recent commits are yours alone before starting).
