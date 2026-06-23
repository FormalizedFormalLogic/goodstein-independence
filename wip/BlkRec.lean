/-
# `wip/BlkRec.lean` — Crux 1 brick 1: the internal block bookkeeping `blk`/`off`

**Status: building the definable `blk`/`off` over an abstract width sequence code (wip).**

Rathjen §3 Cor 3.4 carves the descent index `j` into *blocks* whose widths are
`W_t = iC(β_{t+1})`. The slowed sequence `α j = ω^(l+1)·β_{blk j} + igt (blk j) (off j)`
(`wip/StdCor34.salpha`) consumes a block index `blk j` and an in-block offset `off j` with three
arithmetic properties (`StdCor34.salpha_desc`/`_C_le`):

* the **dichotomy** `blk (j+1) = blk j ∨ blk (j+1) = blk j + 1`;
* the **offset recurrence** `blk (j+1) = blk j → off (j+1) = off j + 1` (within a block the in-block
  offset advances, so the `igt`-tail descends), and `off (j+1) = 0` at a block boundary;
* the **C-bookkeeping** `blk j + off j ≤ j` (hence `blk j ≤ j`, feeding `iC(β_{blk j}) ≤ Cβ + j`).

The ℕ-template `Grz.wsum`/`widx`/`woff` realises this with `Nat.findGreatest` over the partial-sum
function. Internalising `findGreatest` is awkward; instead we build `blk`/`off` directly as a single
**`𝚺₁` primitive recursion** (a state machine that advances the offset within a block and rolls to the
next block when `off+1` reaches the width), mirroring `InternalCor34.iAboveTable.construction`. The
width is supplied abstractly as a **sequence code `wseq`** read by `znth wseq (blk j)`, so every lemma
here is independent of the concrete `β` — instantiated only when the descent `β` lands.

The four arithmetic facts proved here are *exactly* the bookkeeping hypotheses of `salpha_desc`/`_C_le`
(`hblk_dich`, the within-block off-advance behind `higt_within`, and `hnm : blk j + off j ≤ j`).
-/
import GoodsteinPA.InternalCor34

namespace GoodsteinPA.BlkRec

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open GoodsteinPA

variable {V : Type*} [ORingStructure V] [V ⊧ₘ* 𝗜𝚺₁]

/-! ## The block state-machine step

State is the pair `⟪blk, off⟫`. One step reads the current block's width `w = znth wseq blk` and
either advances the offset (`off+1 < w`) or rolls to the next block (`w ≤ off+1`, reset offset). -/

/-- One block-recurrence step on the state `ih = ⟪blk, off⟫` against width sequence `wseq`. -/
noncomputable def boStep (wseq ih : V) : V :=
  if π₂ ih + 1 < znth wseq (π₁ ih) then ⟪π₁ ih, π₂ ih + 1⟫ else ⟪π₁ ih + 1, 0⟫

def _root_.LO.FirstOrder.Arithmetic.boStepDef : 𝚺₁.Semisentence 3 := .mkSigma
  “y wseq ih. ∃ b, !pi₁Def b ih ∧ ∃ o, !pi₂Def o ih ∧ ∃ w, !znthDef w wseq b ∧
    ( (o + 1 < w ∧ !pairDef y b (o + 1)) ∨ (w ≤ o + 1 ∧ !pairDef y (b + 1) 0) )”

instance boStep_defined : 𝚺₁-Function₂ (boStep : V → V → V) via boStepDef := .mk fun v ↦ by
  simp [boStepDef, boStep, pi₁_defined.iff, pi₂_defined.iff, znth_defined.iff, pair_defined.iff]
  by_cases h : π₂ (v 2) + 1 < znth (v 1) (π₁ (v 2))
  · simp [h, not_le.mpr h]
  · simp [h, not_lt.mp h]

instance boStep_definable : 𝚺₁-Function₂ (boStep : V → V → V) := boStep_defined.to_definable
instance boStep_definable' (Γ) : Γ-[m + 1]-Function₂ (boStep : V → V → V) :=
  boStep_definable.of_sigmaOne

/-! ## The block state `⟪blk j, off j⟫` as a `𝚺₁` primitive recursion -/

/-- Blueprint for the block state (1 parameter = the width sequence code `wseq`). -/
def boState.blueprint : PR.Blueprint 1 where
  zero := .mkSigma “y x. !pairDef y 0 0”
  succ := .mkSigma “y ih n x. !boStepDef y x ih”

noncomputable def boState.construction : PR.Construction V boState.blueprint where
  zero := fun _ ↦ ⟪0, 0⟫
  succ := fun x _ ih ↦ boStep (x 0) ih
  zero_defined := .mk fun v ↦ by simp [boState.blueprint, pair_defined.iff]
  succ_defined := .mk fun v ↦ by simp [boState.blueprint, boStep_defined.iff]

/-- The block state `⟪blk wseq j, off wseq j⟫` at index `j`. -/
noncomputable def boState (wseq j : V) : V := boState.construction.result ![wseq] j

@[simp] lemma boState_zero (wseq : V) : boState wseq 0 = ⟪0, 0⟫ := by
  simp [boState, boState.construction]

@[simp] lemma boState_succ (wseq j : V) :
    boState wseq (j + 1) = boStep wseq (boState wseq j) := by
  simp [boState, boState.construction]

def _root_.LO.FirstOrder.Arithmetic.boStateDef : 𝚺₁.Semisentence 3 :=
  boState.blueprint.resultDef.rew (Rew.subst ![#0, #2, #1])

instance boState_defined : 𝚺₁-Function₂ (boState : V → V → V) via boStateDef := .mk
  fun v ↦ by simp [boState.construction.result_defined_iff, boStateDef]; rfl

instance boState_definable : 𝚺₁-Function₂ (boState : V → V → V) := boState_defined.to_definable
instance boState_definable' (Γ) : Γ-[m + 1]-Function₂ (boState : V → V → V) :=
  boState_definable.of_sigmaOne

/-- Block index at step `j`. -/
noncomputable def blk (wseq j : V) : V := π₁ (boState wseq j)
/-- In-block offset at step `j`. -/
noncomputable def off (wseq j : V) : V := π₂ (boState wseq j)

instance blk_definable (Γ) : Γ-[m + 1]-Function₂ (blk : V → V → V) := by unfold blk; definability
instance off_definable (Γ) : Γ-[m + 1]-Function₂ (off : V → V → V) := by unfold off; definability

@[simp] lemma blk_zero (wseq : V) : blk wseq 0 = 0 := by simp [blk]
@[simp] lemma off_zero (wseq : V) : off wseq 0 = 0 := by simp [off]

/-! ## The two step alternatives -/

/-- **Within-block step.** If `off+1 < W(blk)`, the block index is fixed and the offset advances. -/
theorem blk_off_within (wseq j : V) (h : off wseq j + 1 < znth wseq (blk wseq j)) :
    blk wseq (j + 1) = blk wseq j ∧ off wseq (j + 1) = off wseq j + 1 := by
  unfold blk off at h ⊢
  rw [boState_succ, boStep, if_pos h]
  simp

/-- **Boundary step.** If `off+1 ≥ W(blk)`, roll to the next block and reset the offset. -/
theorem blk_off_boundary (wseq j : V) (h : znth wseq (blk wseq j) ≤ off wseq j + 1) :
    blk wseq (j + 1) = blk wseq j + 1 ∧ off wseq (j + 1) = 0 := by
  unfold blk off at h ⊢
  rw [boState_succ, boStep, if_neg (not_lt.mpr h)]
  simp

/-- **The dichotomy** consumed by `StdCor34.salpha_desc`'s `hblk_dich`. -/
theorem blk_succ_dich (wseq j : V) :
    blk wseq (j + 1) = blk wseq j ∨ blk wseq (j + 1) = blk wseq j + 1 := by
  by_cases h : off wseq j + 1 < znth wseq (blk wseq j)
  · exact Or.inl (blk_off_within wseq j h).1
  · exact Or.inr (blk_off_boundary wseq j (not_lt.mp h)).1

/-- **Within-block offset advance** — the bridge feeding `StdCor34.salpha_desc`'s `higt_within`
(within a block the offset is `off j + 1`, so the `igt`-tail descends). -/
theorem off_succ_of_blk_eq (wseq j : V) (hb : blk wseq (j + 1) = blk wseq j) :
    off wseq (j + 1) = off wseq j + 1 := by
  by_cases h : off wseq j + 1 < znth wseq (blk wseq j)
  · exact (blk_off_within wseq j h).2
  · -- boundary would give `blk (j+1) = blk j + 1`, contradicting `hb`
    have hbd := blk_off_boundary wseq j (not_lt.mp h)
    have : blk wseq j + 1 = blk wseq j := by rw [← hbd.1]; exact hb
    exact absurd this (lt_add_one _).ne'

/-! ## The C-bookkeeping `blk j + off j ≤ j` -/

/-- **`blk j + off j ≤ j`** — the slowness bookkeeping consumed by `StdCor34.salpha_C_le`'s `hnm`.
Proved by `𝚺₁` induction on `j`: the sum increases by exactly `1` on a within-block step and *drops*
to `blk j + 1` on a boundary step, so it never outruns `j`. -/
theorem blk_add_off_le (wseq : V) : ∀ j : V, blk wseq j + off wseq j ≤ j := by
  intro j
  induction j using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ j ih =>
    by_cases h : off wseq j + 1 < znth wseq (blk wseq j)
    · obtain ⟨hb, ho⟩ := blk_off_within wseq j h
      rw [hb, ho]
      calc blk wseq j + (off wseq j + 1)
          = (blk wseq j + off wseq j) + 1 := by rw [add_assoc]
        _ ≤ j + 1 := by gcongr
    · obtain ⟨hb, ho⟩ := blk_off_boundary wseq j (not_lt.mp h)
      rw [hb, ho, add_zero]
      have hbj : blk wseq j ≤ j := le_trans le_self_add ih
      gcongr

/-- **`blk j ≤ j`** — feeds `iC(β_{blk j}) ≤ Cβ + j` in `StdCor34.salpha_C_le`'s `hβC`. -/
theorem blk_le (wseq j : V) : blk wseq j ≤ j :=
  le_trans le_self_add (blk_add_off_le wseq j)

end GoodsteinPA.BlkRec
