import GoodsteinPA.WainerLadder

/-!
# SERIES-2 Stage C-2 probe — does the goodstein matrix satisfy the `readoffD_trapped_of_mono` guard?

**Question (`REBUILD-Z-SERIES-2-ORDER-2026-07-03.md` Stage C-2).**  Do the goodstein matrix's
bounded-∀ step clauses satisfy the guard condition `atomTrue (χ/[nm 0]) → atomTrue (∀⁰ χ)`
that makes `readoffD_trapped_of_mono` close the lane-D residue?

**ANSWER: NO — the bounded-∀ GUARD SHAPE refutes the mono condition, kernel-checked.**
The concrete `igoodsteinDef` matrix (the `PR.Blueprint.resultDef` β-coding) certifies a run by
step clauses of the shape `∀ i (i < N → step-i-equation)`: a guarded implication whose
`0`-instance truth says only "step 0 is coded correctly" and says NOTHING about steps `≥ 1`.
`guardShape_not_mono` below exhibits this on the minimal representative of the shape class
(`χ = (x < 2 → x = 0)`, a guard + atomic equation): the `0`-instance is TRUE while the
`1`-instance (inside the guard) is FALSE — evaluated in the kernel via `Evalm ℕ` `simp`
(no `native_decide`, no axioms beyond the classical trio).

**Consequence for ruling (2) — Option B is LOAD-BEARING, not just convenient.**  The
`readoffD_trapped_of_mono` fragment does NOT cover the concrete goodstein translation: its
guard fails exactly on the run-certifying clauses (a run miscoded at step `k ≥ 1` but correct
at step `0` is the standard false-branch adversary).  So the lane-D residue on the headline
path must be closed by one of the two judged amendments — and Stage C-1
(`wip/OptionBSpliceProbe.lean`) showed the R-4′ restatement (Option B, bound `ewIter f α 0`)
is structurally FREE for the splice, while (Ax2) is the heavier calculus change (Stage B).
Stage C's combined evidence therefore points at the R-4′ restatement as the ruling-(2)
recommendation, with (Ax2) remaining solely a rung-E faithfulness question.

**Scope honesty.**  `guardShape_not_mono` is the SHAPE-CLASS refutation, not a computation
inside the machine-generated `resultDef` blob: it shows the guard condition FAILS for
guarded-implication clauses in general, hence cannot be discharged by any argument generic in
the shape (which is what `readoffD_trapped_of_mono`'s `hmono` hypothesis would have to be
instantiated with).  A per-`resultDef` semantic analysis could conceivably rescue `hmono` for
the specific goodstein coding — but the run-miscoding adversary above is a semantic
counterexample family for it too (correct step 0, broken step 1), so we record the shape-class
refutation as the ruling input.

wip-only ruling input (SERIES-2 order Stage C-2 / ladder P2).  `src` untouched.
-/

namespace GoodsteinPA.GuardMonoProbe

open LO LO.FirstOrder ONote
open GoodsteinPA.OperatorZeh GoodsteinPA.OperatorZinfty

/-- The minimal representative of the bounded-∀ guarded step-clause shape
`i < N → step-i-equation`: here `x < 2 → x = 0` (guard bound `2`, atomic equation body).
Its `0`-instance is true (`0 = 0`), its `1`-instance is false (`1 < 2` but `1 ≠ 0`) —
the run-miscoded-at-step-1 adversary. -/
noncomputable def guardStep : SyntacticSemiformula ℒₒᵣ 1 :=
  ↑(“x. x < 2 → x = 0” : Semisentence ℒₒᵣ 1)

/-- The `0`-instance of the guard clause is TRUE at ℕ. -/
theorem guardStep_zero_true : atomTrue (guardStep/[nm 0]) := by
  simp [guardStep, atomTrue, nm]

/-- The ω-universal over the guard clause is FALSE at ℕ (the `1`-instance fails). -/
theorem guardStep_all_false : ¬ atomTrue (∀⁰ guardStep) := by
  intro h
  have h1 := (atomTrue_all_iff guardStep).mp h 1
  simp [guardStep, atomTrue, nm] at h1

/-- **The C-2 refutation** — the bounded-∀ guard shape does NOT satisfy the
`readoffD_trapped_of_mono` condition `atomTrue (χ/[nm 0]) → atomTrue (∀⁰ χ)`. -/
theorem guardShape_not_mono :
    ¬ (atomTrue (guardStep/[nm 0]) → atomTrue (∀⁰ guardStep)) := fun h =>
  guardStep_all_false (h guardStep_zero_true)

end GoodsteinPA.GuardMonoProbe
