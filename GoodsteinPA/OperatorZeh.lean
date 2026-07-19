/-
# `OperatorZeh` — the `Zᵉ` operator-controlled calculus

The `Zeh` cut-elimination substrate: the calculus core (`GoodsteinPA.OperatorZeh.Operator`,
`.Zeh`), the structural layer (`mono_H`, `ZehProv`), and the read-off exit
(`GoodsteinPA.OperatorZeh.Readoff`).

**Superseded:** the function-slot judgment `Zef` (`GoodsteinPA.OperatorZeh.Zef`), `iterSlot`
and its supporting lemmas (`GoodsteinPA.OperatorZeh.Slot`), and the unfinished
rank-lowering pass `cutElimPass_Zf` are superseded by `OperatorZef2.lean` (`Zef2`, the
ewN-gated calculus). They remain here as frozen evidence — statement tokens untouched.

* **The inversion suite (`GoodsteinPA.OperatorZeh.Inversion`).**  `allInv_Zeh` is a real
  proof — the six-case induction mirroring `Zekd.allInv` (`OperatorZinfty.lean`), with the
  numeric `max k n₀` bookkeeping re-keyed to the stage `max m n₀` and the relativization
  `adjoin H n₀`.
* **The f-slot elimination suite (`GoodsteinPA.OperatorZeh.Cut`).**  The Eguchi–Weiermann
  function-slot forms: the running-family reduction `cutReduceAllAuxRunning_Zf` and the
  common-control step motive `stepAllω_Zf` are real sorry-free theorems in the function-slot
  judgment `Zef` — the slot `f : ℕ → ℕ` composed at principal cuts (output slot `g ∘ f`),
  max-relativized at ω-nodes (`rel1`), instantiated to `hardy e` at the root.  The ℕ-stage
  judgment `Zeh` cannot carry this reduction (kernel-refuted,
  `principal_witness_exceeds_stage`), which is why the function-slot judgment `Zef` replaces
  the ℕ-stage with the function-slot.
* **The two seams re-expressed in the f-form (`GoodsteinPA.OperatorZeh.Examples`).**  The
  seam probes re-run against the f-slot statements: seam 1
  (`seam1_bump_absorbed_by_composition`) and seam 2 (`seam2_function_slot_payable`) close as
  real proofs against the function-slot reduction shape.

Standing invariants: no numeric fact routes through `H`-membership (R1); existentials open at
the root only (R2); `e` is constant through a derivation, control changes at statement level
(R3); numeric budgets are function-valued (R4); no new `axiom` declarations (R5).

This file is a thin re-export aggregator; the content lives in the `GoodsteinPA.OperatorZeh.*`
submodules (`Operator`, `Slot`, `Zeh`, `Zef`, `Inversion`, `Cut`, `Readoff`, `Examples`).

- [Tow20, §19]
- [EW12, Lemma 25, Lemma 27, Lemma 31]
- [BW87]
-/
module

public import GoodsteinPA.OperatorZeh.Operator
public import GoodsteinPA.OperatorZeh.Slot
public import GoodsteinPA.OperatorZeh.Zeh
public import GoodsteinPA.OperatorZeh.Zef
public import GoodsteinPA.OperatorZeh.Inversion
public import GoodsteinPA.OperatorZeh.Cut
public import GoodsteinPA.OperatorZeh.Readoff
public import GoodsteinPA.OperatorZeh.Examples
