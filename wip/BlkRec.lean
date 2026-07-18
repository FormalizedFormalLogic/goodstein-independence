/-
# `wip/BlkRec.lean` — Crux 1 brick 1: the internal block bookkeeping `blk`/`off`

**Status: COMPLETE (axiom-clean, in the build). Crux-1 brick 1.**

Rathjen §3 Cor 3.4 carves the descent index `j` into *blocks* whose widths are
`W_t = iC(β_{t+1})`. The slowed sequence `α j = ω^(l+1)·β_{blk j} + igt (blk j) (off j)`
(`wip/StdCor34.salpha`) consumes a block index `blk j` and an in-block offset `off j` with three
arithmetic properties (`StdCor34.salpha_desc`/`_C_le`):

* the **dichotomy** `blk (j+1) = blk j ∨ blk (j+1) = blk j + 1`;
* the **offset recurrence** `blk (j+1) = blk j → off (j+1) = off j + 1` (within a block the in-block
  offset advances, so the `igt`-tail descends), and `off (j+1) = 0` at a block boundary;
* the **C-bookkeeping** `blk j + off j ≤ j` (block count); and the elapsed-*width* invariant
  `wsumc (blk j) ≤ j` (`wsumc_blk_le`), the fact `hβC : iC(β_{blk j}) ≤ Cβ + j` actually needs on the
  width/block route — block-count `blk j ≤ j` alone is NOT enough (codex review, lap 52).

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
import GoodsteinPA.Compat

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

/-- **Within-block ⟹ strict offset headroom.** If the block index is fixed across a step
(`blk (j+1) = blk j`), the step must have taken the *advance* branch, so `off j + 1` is still
strictly below the current block width. The exact fact `StdCor34`'s domination hypothesis `hdom`
needs: it then only remains to dominate the *width* by `iF l₀ (blk j)`. -/
theorem off_succ_lt_width_of_blk_eq (wseq j : V) (hb : blk wseq (j + 1) = blk wseq j) :
    off wseq j + 1 < znth wseq (blk wseq j) := by
  by_cases h : off wseq j + 1 < znth wseq (blk wseq j)
  · exact h
  · have hbd := blk_off_boundary wseq j (not_lt.mp h)
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

/-- **`blk j ≤ j`** — a *block-count* bound (NOT by itself enough for `hβC`; see the width invariant
`wsumc_blk_le` below, which is the elapsed-*width* fact `StdCor34.salpha_C_le`'s `hβC` actually needs). -/
theorem blk_le (wseq j : V) : blk wseq j ≤ j :=
  le_trans le_self_add (blk_add_off_le wseq j)

/-! ## The elapsed-*width* invariant (for `hβC`)

`blk_le` (block-count `blk j ≤ j`) is **not** what `StdCor34.salpha_C_le`'s `hβC :
iC (β (blk j)) ≤ Cβ + j` needs on the width/block route — there the relevant fact is the *cumulative
width* `wsumc (blk j) ≤ j` (RAthjen Cor 3.4: the `C`-growth of `β` is bookkept against the elapsed
width `Σ_{b<blk j} W(b)`, not the block count). We prove `wsumc (blk j) + off j = j` (exact, under
positive widths), hence `wsumc (blk j) ≤ j`. The width of block `b` is `znth wseq b`. -/

/-- Cumulative width `wsumc wseq i = Σ_{b<i} znth wseq b`. -/
def wsumc.blueprint : PR.Blueprint 1 where
  zero := .mkSigma “y x. y = 0”
  succ := .mkSigma “y ih i x. ∃ w, !znthDef w x i ∧ y = ih + w”

noncomputable def wsumc.construction : PR.Construction V wsumc.blueprint where
  zero := fun _ ↦ 0
  succ := fun x i ih ↦ ih + znth (x 0) i
  zero_defined := .mk fun v ↦ by simp [wsumc.blueprint]
  succ_defined := .mk fun v ↦ by simp [wsumc.blueprint, znth_defined.iff]

/-- Cumulative width up to (excluding) block `i`. -/
noncomputable def wsumc (wseq i : V) : V := wsumc.construction.result ![wseq] i

@[simp] lemma wsumc_zero (wseq : V) : wsumc wseq 0 = 0 := by
  simp [wsumc, wsumc.construction]

@[simp] lemma wsumc_succ (wseq i : V) : wsumc wseq (i + 1) = wsumc wseq i + znth wseq i := by
  simp [wsumc, wsumc.construction]

def _root_.LO.FirstOrder.Arithmetic.wsumcDef : 𝚺₁.Semisentence 3 :=
  wsumc.blueprint.resultDef.rew (Rew.subst ![#0, #2, #1])

instance wsumc_defined : 𝚺₁-Function₂ (wsumc : V → V → V) via wsumcDef := .mk
  fun v ↦ by simp [wsumc.construction.result_defined_iff, wsumcDef, wsumc]; rfl

instance wsumc_definable : 𝚺₁-Function₂ (wsumc : V → V → V) := wsumc_defined.to_definable
instance wsumc_definable' (Γ) : Γ-[m + 1]-Function₂ (wsumc : V → V → V) :=
  wsumc_definable.of_sigmaOne

/-- **Offset stays below the current block width** (under positive widths). The within-block invariant
that makes a boundary fire exactly at `off = width - 1`. -/
-- Positivity is needed only on the **prefix** `[0, j]` (the indices `blk`/`off` actually read), so a
-- *finite* width code (`znth = 0` past its length) still works once it covers `[0, j]`.
theorem off_lt_width (wseq : V) :
    ∀ j, (∀ b, b ≤ j → 1 ≤ znth wseq b) → off wseq j < znth wseq (blk wseq j) := by
  intro j
  induction j using ISigma1.sigma1_succ_induction
  · definability
  case zero => intro hpos; simpa using lt_of_lt_of_le _root_.zero_lt_one (hpos 0 (le_refl _))
  case succ j ih =>
    intro hpos
    by_cases h : off wseq j + 1 < znth wseq (blk wseq j)
    · obtain ⟨hb, ho⟩ := blk_off_within wseq j h; rw [hb, ho]; exact h
    · obtain ⟨hb, ho⟩ := blk_off_boundary wseq j (not_lt.mp h)
      rw [hb, ho]
      refine lt_of_lt_of_le _root_.zero_lt_one (hpos (blk wseq j + 1) ?_)
      have := blk_le wseq j; gcongr

/-- **The elapsed-width identity** (under prefix-positive widths): `wsumc (blk j) + off j = j`. The
total steps `j` is exactly the cumulative width of completed blocks plus the current in-block offset. -/
theorem wsumc_blk_add_off (wseq : V) :
    ∀ j, (∀ b, b ≤ j → 1 ≤ znth wseq b) → wsumc wseq (blk wseq j) + off wseq j = j := by
  intro j
  induction j using ISigma1.sigma1_succ_induction
  · definability
  case zero => intro _; simp
  case succ j ih =>
    intro hpos
    have hpos_j : ∀ b, b ≤ j → 1 ≤ znth wseq b := fun b hb => hpos b (le_trans hb le_self_add)
    by_cases h : off wseq j + 1 < znth wseq (blk wseq j)
    · obtain ⟨hb, ho⟩ := blk_off_within wseq j h
      rw [hb, ho, ← add_assoc, ih hpos_j]
    · obtain ⟨hb, ho⟩ := blk_off_boundary wseq j (not_lt.mp h)
      have hw : znth wseq (blk wseq j) = off wseq j + 1 :=
        le_antisymm (not_lt.mp h) (lt_iff_succ_le.mp (off_lt_width wseq j hpos_j))
      rw [hb, ho, add_zero, wsumc_succ, hw, ← add_assoc, ih hpos_j]

/-- **`wsumc (blk j) ≤ j`** — the elapsed-*width* bound `StdCor34.salpha_C_le`'s `hβC` consumes on the
width/block route (the honest replacement for the over-claimed `blk_le`). -/
theorem wsumc_blk_le (wseq j : V) (hpos : ∀ b, b ≤ j → 1 ≤ znth wseq b) :
    wsumc wseq (blk wseq j) ≤ j :=
  le_trans le_self_add (le_of_eq (wsumc_blk_add_off wseq j hpos))

/-! ## Prefix-invariance (the `wseq` seam, codex review lap 52)

`blk`/`off` at step `j` read the width code `wseq` only at indices `b ≤ blk j ≤ j`. So they depend
only on a **prefix** of `wseq`: any two codes agreeing on `znth · b` for `b ≤ j` give the same state.
This is what lets crux-1 integration feed a *long-enough prefix code* of the true (definable) widths
`W t = iC(β(t+1))` into the abstract `BlkRec`, instead of threading a global width function's `Def`. -/

/-- **Prefix-invariance of the block state.** Agreement of the width codes on `[0, j]` forces equal
states at step `j`. -/
theorem boState_congr {wseq wseq' : V} :
    ∀ j, (∀ b, b ≤ j → znth wseq b = znth wseq' b) → boState wseq j = boState wseq' j := by
  intro j
  induction j using ISigma1.sigma1_succ_induction
  · definability
  case zero => intro _; simp
  case succ j ih =>
    intro hagree
    have iheq := ih (fun b hb => hagree b (le_trans hb le_self_add))
    have hblk_le : π₁ (boState wseq' j) ≤ j := by
      have := blk_le wseq' j; unfold blk at this; exact this
    rw [boState_succ, boState_succ, iheq, boStep, boStep,
      hagree (π₁ (boState wseq' j)) (le_trans hblk_le le_self_add)]

theorem blk_prefix_congr {wseq wseq' j : V}
    (hagree : ∀ b, b ≤ j → znth wseq b = znth wseq' b) : blk wseq j = blk wseq' j := by
  unfold blk; rw [boState_congr j hagree]

theorem off_prefix_congr {wseq wseq' j : V}
    (hagree : ∀ b, b ≤ j → znth wseq b = znth wseq' b) : off wseq j = off wseq' j := by
  unfold off; rw [boState_congr j hagree]

end GoodsteinPA.BlkRec
