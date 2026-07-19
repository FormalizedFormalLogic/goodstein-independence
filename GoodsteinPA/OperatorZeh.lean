/-
# `OperatorZeh` — the `Zᵉ` operator-controlled calculus (REBUILD-Z lap 1)

The `Zeh` cut-elimination substrate, promoted from the judge-ratified spike
`wip/SpikeZ1Seams.lean` into `src/` per `REBUILD-Z-ORDER-2026-07-02.md` (Scope-A) and
`ZEH-STATEMENT-LOCK-2026-07-02.md`.  The calculus core (§0–§2), the structural layer
(`mono_H`, `ZehProv`), and the read-off exit (§3) are the LOCK §1 forms VERBATIM
(namespace change only, `SpikeZ1 → OperatorZeh`).

**SUPERSEDED (lap 8, ratified in `E-2026-07-02-JUDGE-rebuild-z-lap8-validation.md`):** the
`Zef` layer (§5/§7), `iterSlot` + the §5b lemmas, and old pin 3 (`cutElimPass_Zf`) are
superseded by `OperatorZef2.lean` (`Zef2`, the ewN-gated calculus). They remain here as frozen
evidence — statement tokens untouched.

Beyond the verbatim seed this module carries the lap-1 statement work:

* **§4 — the inversion suite (A3, PROVEN).**  `allInv_Zeh` (Z1 pin 1) is discharged as a
  real proof — the six-case induction mirroring the banked `Zekd.allInv`
  (`OperatorZinfty.lean:484`) with the numeric `max k n₀`/`d`-inert bookkeeping re-keyed to
  the stage `max m n₀` and the relativization `adjoin H n₀`.  `#print axioms` clean.
* **§5/§7 — the f-slot elimination suite (A2; pins 1–2 DISCHARGED lap 184, pin 3 `sorry`).**
  The Eguchi–Weiermann function-slot forms (LOCK §3): the running-family reduction
  `cutReduceAllAuxRunning_Zf` (pin 1) and the common-control step motive `stepAllω_Zf`
  (pin 2) are **real sorry-free theorems** in the function-slot judgment `Zef` (§7) — the
  slot `f : ℕ → ℕ` composed at principal cuts (output slot `g ∘ f`), max-relativized at
  ω-nodes (`rel1`), instantiated to `hardy e` at the root.  This required amending LOCK
  §1-A1/§3: the ℕ-stage judgment `Zeh` could not carry the reduction (kernel-refuted,
  `principal_witness_exceeds_stage`), so the R4-compliant slot judgment `Zef` replaces the
  ℕ-stage with the function-slot (RATIFIED lap 184,
  `REBUILD-Z-LAP4-RATIFICATION-2026-07-02.md`).  The collapse/iteration shape
  `cutElimPass_Zf` (pin 3) stays the lap-5 entrance gate — `sorry`, discharge FORBIDDEN.
* **§6 — the two Z1 seams RE-EXPRESSED in the f-form (A2, PROVEN).**  The Z1 seam probes
  re-run against the §5 statements: seam 1 (`seam1_f_absorbed_by_composition`) and seam 2
  (`seam2_f_slot_payable`) close as REAL proofs against the function-slot reduction shape —
  no sorried membership, no sorried slot.  If either failed here it would be T-R(i) (the
  E–W carrier failing where the ℕ-slots failed); it does not.

Standing rails honored (LOCK §2): no numeric fact routes through `H`-membership (R1);
existentials open at the root only (R2); `e` is constant through a derivation, control
changes at statement level (R3); numeric budgets are function-valued (R4); no new `axiom`
declarations (R5).

This file is a thin re-export aggregator; the content lives in the `GoodsteinPA.OperatorZeh.*`
submodules (`Operator`, `Slot`, `Zeh`, `Zef`, `Inversion`, `Cut`, `Readoff`, `Examples`).
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
