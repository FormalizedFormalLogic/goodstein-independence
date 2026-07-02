/-
# `JudgeTrap8FixProbe` — judge-authored (laps-6–7 judge pass, 2026-07-02): the E–W side
condition ALONE does not rescue the fundamental-sequence iterate; the iterate FORM must
change too.

Context: trap 8 (`wip/Trap8Probe.lean`, ratified) kernel-refuted the pointwise lift
`iterSlot f β ≤ iterSlot f α` for `β < α` at `f = (·+1)`, `β = 2`, `α = ω`.  In E–W
(arXiv:1205.2879, Def 23) every node of a controlled derivation carries the side condition
`N(α) ≤ f(0)` (HYP), so one could hope the LOCKED fs-recursion `iterSlot` becomes
ordinal-monotone once restricted to admissible pairs (`norm β ≤ f 0`).  **It does not**:
with `f = (·+2)` the trap-8 instance is admissible (`norm 2 = 2 ≤ 2 = f 0`) and the dip
persists (`iterSlot f ω 0 = 4 < 6 = iterSlot f 2 0`) — the fs-recursion rides `ω[0] = 1`
regardless of how large `f` is.

E–W's own iterate (Def 16) is NOT fs-recursion but the norm-gated MAX
`f^α(m) = max{f^β(f^β(m)) | β < α, N(β) ≤ f(N(α)+m)}`, which dominates every admissible
`f^β` by construction (Cor 17.2).  Consequence for the trap-8 fix: BOTH changes are needed —
the judgment-level norm side condition (Def 23 HYP) AND the norm-gated max form of the
iterate (Def 16).  Neither alone suffices (side-condition-only refuted HERE;
iterate-form-only is refuted by `Trap8Probe.no_fixed_arg_monotone_unbounded_slot` — without
the side condition the admissible family is all of `β < α` and the sharp impossibility
applies).

Read-only evidence artifact; do NOT wire into `src`.  Architect order:
`REBUILD-Z-LAP7-ENTRANCE-2026-07-02.md`.
-/
import GoodsteinPA.OperatorZeh
open GoodsteinPA.OperatorZeh ONote
open GoodsteinPA.FastGrowing

namespace GoodsteinPA.OperatorZeh

/-- `f = (·+2)`: monotone + inflationary (the pin's hypotheses), and large enough that the
trap-8 instance `β = 2 < ω` is E–W-admissible: `norm (ofNat 2) = 2 ≤ 2 = f 0`. -/
def fjudge : ℕ → ℕ := fun n => n + 2

theorem fjudge_mono : Monotone fjudge := fun a b h => by simp only [fjudge]; omega
theorem fjudge_infl : ∀ x, x ≤ fjudge x := fun x => by simp only [fjudge]; omega

/-- The two decisive values (kernel-computed): `iterSlot fjudge 2 0 = fjudge^[3] 0 = 6`;
`iterSlot fjudge ω 0` rides `ω[0] = 1`, giving `fjudge^[2] 0 = 4`. -/
theorem iterSlot_fjudge_two_zero : iterSlot fjudge (ONote.ofNat 2) 0 = 6 := by native_decide
theorem iterSlot_fjudge_omega_zero : iterSlot fjudge (oadd 1 1 0) 0 = 4 := by native_decide

/-- **The finding**: the trap-8 dip persists on an E–W-ADMISSIBLE instance.  `β = ofNat 2`
satisfies the Def-23-style side condition `norm β ≤ fjudge 0`, and still
`iterSlot fjudge ω 0 < iterSlot fjudge β 0`.  So adding the HYP side condition to the
judgment while keeping the fs-recursion iterate would leave pin 3 exactly as unprovable as
trap 8 found it — the iterate must ALSO move to the E–W Def-16 norm-gated max form. -/
theorem side_condition_alone_does_not_rescue_fs_iterate :
    norm (ONote.ofNat 2) ≤ fjudge 0 ∧
    iterSlot fjudge (oadd 1 1 0) 0 < iterSlot fjudge (ONote.ofNat 2) 0 := by
  refine ⟨by native_decide, ?_⟩
  rw [iterSlot_fjudge_two_zero, iterSlot_fjudge_omega_zero]
  omega

end GoodsteinPA.OperatorZeh
