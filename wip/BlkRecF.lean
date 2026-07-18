/-
# `BlkRecF.lean` — Crux 1: block bookkeeping over a width FUNCTION (not a finite code)

**Status: COMPLETE (axiom-clean, in the build). Crux-1 brick — the lap-57 width-code-wall fix.**

`src/BlkRec.lean` reads the Cor-3.4 block width from a **finite sequence code** `wseq : V` via
`znth wseq b`. `ANALYSIS-2026-06-23-lap57-width-code-wall.md` shows no finite code can drive an infinite
descent (past `lh wseq`, `znth = 0` ⟹ `blk wseq j ∼ j` ⟹ the slowness C-bound fails for the
complexity-growing descents Cor 3.4 targets). This file re-states the *same* block state machine over a
`𝚺₁`-definable width **function** `W : V → V` (baked in via its graph `WDef`, mirroring
`InternalGrz.iwseq`'s `fDef`/`f`/`hf` pattern). The four bookkeeping facts + the elapsed-width invariant
are ported verbatim (the proofs only use the `boStep` if-then-else structure, not `znth` specifics).

Next: re-thread `StdCor34`/`SeqDominated` onto `blkF`/`wsumcF` (width `W = fun t => iC (β (t+1))`).
-/
import GoodsteinPA.BlkRec
import GoodsteinPA.Compat

namespace GoodsteinPA.BlkRecF

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open GoodsteinPA

set_option maxHeartbeats 400000

variable {V : Type*} [ORingStructure V] [V ⊧ₘ* 𝗜𝚺₁]

/-! ## The block state-machine step over a width function `W` -/

/-- One block-recurrence step reading the current block width `W (blk)` from a function. -/
noncomputable def boStepF (W : V → V) (ih : V) : V :=
  if π₂ ih + 1 < W (π₁ ih) then ⟪π₁ ih, π₂ ih + 1⟫ else ⟪π₁ ih + 1, 0⟫

variable {WDef : 𝚺₁.Semisentence 2} {W : V → V} {hW : 𝚺₁.DefinedFunction₁ W WDef}

def _root_.LO.FirstOrder.Arithmetic.boStepFDef (WDef : 𝚺₁.Semisentence 2) : 𝚺₁.Semisentence 2 :=
  .mkSigma “y ih. ∃ b, !pi₁Def b ih ∧ ∃ o, !pi₂Def o ih ∧ ∃ w, !WDef w b ∧
    ( (o + 1 < w ∧ !pairDef y b (o + 1)) ∨ (w ≤ o + 1 ∧ !pairDef y (b + 1) 0) )”

lemma boStepF_defined (hW : 𝚺₁.DefinedFunction₁ W WDef) :
    𝚺₁-Function₁ (boStepF W : V → V) via boStepFDef WDef := .mk fun v ↦ by
  simp [boStepFDef, boStepF, pi₁_defined.iff, pi₂_defined.iff, hW.iff, pair_defined.iff]
  by_cases h : π₂ (v 1) + 1 < W (π₁ (v 1))
  · simp [h]
  · simp [h, not_lt.mp h]

/-! ## The block state `⟪blkF j, offF j⟫` as a `𝚺₁` primitive recursion (0 params, `W` baked in) -/

def boStateF.blueprint (WDef : 𝚺₁.Semisentence 2) : PR.Blueprint 0 where
  zero := .mkSigma “y. !pairDef y 0 0”
  succ := .mkSigma “y ih n. !(boStepFDef WDef) y ih”

noncomputable def boStateF.construction (WDef : 𝚺₁.Semisentence 2) (W : V → V)
    (hW : 𝚺₁.DefinedFunction₁ W WDef) : PR.Construction V (boStateF.blueprint WDef) where
  zero := fun _ ↦ ⟪0, 0⟫
  succ := fun _ _ ih ↦ boStepF W ih
  zero_defined := .mk fun v ↦ by simp [boStateF.blueprint, pair_defined.iff]
  succ_defined := .mk fun v ↦ by simp [boStateF.blueprint, (boStepF_defined (hW := hW)).iff]

/-- The block state `⟪blkF W j, offF W j⟫` at index `j`. -/
noncomputable def boStateF (WDef : 𝚺₁.Semisentence 2) (W : V → V)
    (hW : 𝚺₁.DefinedFunction₁ W WDef) (j : V) : V := (boStateF.construction WDef W hW).result ![] j

@[simp] lemma boStateF_zero : boStateF WDef W hW 0 = ⟪0, 0⟫ := by
  simp [boStateF, boStateF.construction]

@[simp] lemma boStateF_succ (j : V) :
    boStateF WDef W hW (j + 1) = boStepF W (boStateF WDef W hW j) := by
  simp [boStateF, boStateF.construction]

def _root_.LO.FirstOrder.Arithmetic.boStateFDef (WDef : 𝚺₁.Semisentence 2) : 𝚺₁.Semisentence 2 :=
  (boStateF.blueprint WDef).resultDef

lemma boStateF_defined : 𝚺₁-Function₁ (boStateF WDef W hW : V → V) via boStateFDef WDef := .mk
  fun v ↦ by
    simp [(boStateF.construction WDef W hW).result_defined_iff, boStateFDef, boStateF, Matrix.empty_eq]

instance boStateF_definable : 𝚺₁-Function₁ (boStateF WDef W hW : V → V) :=
  (boStateF_defined (hW := hW)).to_definable
instance boStateF_definable' (Γ) : Γ-[m + 1]-Function₁ (boStateF WDef W hW : V → V) :=
  boStateF_definable.of_sigmaOne

/-- Block index at step `j`. -/
noncomputable def blkF (WDef : 𝚺₁.Semisentence 2) (W : V → V)
    (hW : 𝚺₁.DefinedFunction₁ W WDef) (j : V) : V := π₁ (boStateF WDef W hW j)
/-- In-block offset at step `j`. -/
noncomputable def offF (WDef : 𝚺₁.Semisentence 2) (W : V → V)
    (hW : 𝚺₁.DefinedFunction₁ W WDef) (j : V) : V := π₂ (boStateF WDef W hW j)

instance blkF_definable (Γ) : Γ-[m + 1]-Function₁ (blkF WDef W hW : V → V) := by
  unfold blkF; definability
instance offF_definable (Γ) : Γ-[m + 1]-Function₁ (offF WDef W hW : V → V) := by
  unfold offF; definability

@[simp] lemma blkF_zero : blkF WDef W hW 0 = 0 := by simp [blkF]
@[simp] lemma offF_zero : offF WDef W hW 0 = 0 := by simp [offF]

/-! ## The two step alternatives -/

theorem blkF_offF_within (j : V) (h : offF WDef W hW j + 1 < W (blkF WDef W hW j)) :
    blkF WDef W hW (j + 1) = blkF WDef W hW j ∧ offF WDef W hW (j + 1) = offF WDef W hW j + 1 := by
  unfold blkF offF at h ⊢
  rw [boStateF_succ, boStepF, if_pos h]
  simp

theorem blkF_offF_boundary (j : V) (h : W (blkF WDef W hW j) ≤ offF WDef W hW j + 1) :
    blkF WDef W hW (j + 1) = blkF WDef W hW j + 1 ∧ offF WDef W hW (j + 1) = 0 := by
  unfold blkF offF at h ⊢
  rw [boStateF_succ, boStepF, if_neg (not_lt.mpr h)]
  simp

/-- **The dichotomy** consumed by `StdCor34.salpha_desc`'s `hblk_dich`. -/
theorem blkF_succ_dich (j : V) :
    blkF WDef W hW (j + 1) = blkF WDef W hW j ∨ blkF WDef W hW (j + 1) = blkF WDef W hW j + 1 := by
  by_cases h : offF WDef W hW j + 1 < W (blkF WDef W hW j)
  · exact Or.inl (blkF_offF_within j h).1
  · exact Or.inr (blkF_offF_boundary j (not_lt.mp h)).1

/-- **Within-block offset advance** — the bridge feeding `StdCor34.salpha_desc`'s `higt_within`. -/
theorem offF_succ_of_blkF_eq (j : V) (hb : blkF WDef W hW (j + 1) = blkF WDef W hW j) :
    offF WDef W hW (j + 1) = offF WDef W hW j + 1 := by
  by_cases h : offF WDef W hW j + 1 < W (blkF WDef W hW j)
  · exact (blkF_offF_within j h).2
  · have hbd := blkF_offF_boundary j (not_lt.mp h)
    have : blkF WDef W hW j + 1 = blkF WDef W hW j := by rw [← hbd.1]; exact hb
    exact absurd this (lt_add_one _).ne'

/-- **Within-block ⟹ strict offset headroom.** -/
theorem offF_succ_lt_width_of_blkF_eq (j : V) (hb : blkF WDef W hW (j + 1) = blkF WDef W hW j) :
    offF WDef W hW j + 1 < W (blkF WDef W hW j) := by
  by_cases h : offF WDef W hW j + 1 < W (blkF WDef W hW j)
  · exact h
  · have hbd := blkF_offF_boundary j (not_lt.mp h)
    have : blkF WDef W hW j + 1 = blkF WDef W hW j := by rw [← hbd.1]; exact hb
    exact absurd this (lt_add_one _).ne'

/-! ## The C-bookkeeping `blkF j + offF j ≤ j` -/

theorem blkF_add_offF_le : ∀ j : V, blkF WDef W hW j + offF WDef W hW j ≤ j := by
  intro j
  induction j using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ j ih =>
    by_cases h : offF WDef W hW j + 1 < W (blkF WDef W hW j)
    · obtain ⟨hb, ho⟩ := blkF_offF_within j h
      rw [hb, ho]
      calc blkF WDef W hW j + (offF WDef W hW j + 1)
          = (blkF WDef W hW j + offF WDef W hW j) + 1 := by rw [add_assoc]
        _ ≤ j + 1 := by gcongr
    · obtain ⟨hb, ho⟩ := blkF_offF_boundary j (not_lt.mp h)
      rw [hb, ho, add_zero]
      have hbj : blkF WDef W hW j ≤ j := le_trans le_self_add ih
      gcongr

theorem blkF_le (j : V) : blkF WDef W hW j ≤ j :=
  le_trans le_self_add (blkF_add_offF_le j)

/-! ## The elapsed-*width* invariant (for `hβC`), now over the function `W` -/

/-- Cumulative width `wsumcF W i = Σ_{b<i} W b` (0 params, `W` baked in). -/
def wsumcF.blueprint (WDef : 𝚺₁.Semisentence 2) : PR.Blueprint 0 where
  zero := .mkSigma “y. y = 0”
  succ := .mkSigma “y ih i. ∃ w, !WDef w i ∧ y = ih + w”

noncomputable def wsumcF.construction (WDef : 𝚺₁.Semisentence 2) (W : V → V)
    (hW : 𝚺₁.DefinedFunction₁ W WDef) : PR.Construction V (wsumcF.blueprint WDef) where
  zero := fun _ ↦ 0
  succ := fun _ i ih ↦ ih + W i
  zero_defined := .mk fun v ↦ by simp [wsumcF.blueprint]
  succ_defined := .mk fun v ↦ by simp [wsumcF.blueprint, hW.iff]

noncomputable def wsumcF (WDef : 𝚺₁.Semisentence 2) (W : V → V)
    (hW : 𝚺₁.DefinedFunction₁ W WDef) (i : V) : V := (wsumcF.construction WDef W hW).result ![] i

@[simp] lemma wsumcF_zero : wsumcF WDef W hW 0 = 0 := by simp [wsumcF, wsumcF.construction]

@[simp] lemma wsumcF_succ (i : V) : wsumcF WDef W hW (i + 1) = wsumcF WDef W hW i + W i := by
  simp [wsumcF, wsumcF.construction]

def _root_.LO.FirstOrder.Arithmetic.wsumcFDef (WDef : 𝚺₁.Semisentence 2) : 𝚺₁.Semisentence 2 :=
  (wsumcF.blueprint WDef).resultDef

lemma wsumcF_defined : 𝚺₁-Function₁ (wsumcF WDef W hW : V → V) via wsumcFDef WDef := .mk
  fun v ↦ by
    simp [(wsumcF.construction WDef W hW).result_defined_iff, wsumcFDef, wsumcF, Matrix.empty_eq]

instance wsumcF_definable : 𝚺₁-Function₁ (wsumcF WDef W hW : V → V) :=
  (wsumcF_defined (hW := hW)).to_definable
instance wsumcF_definable' (Γ) : Γ-[m + 1]-Function₁ (wsumcF WDef W hW : V → V) :=
  wsumcF_definable.of_sigmaOne

/-- **Offset stays below the current block width** (under global positive widths). -/
theorem offF_lt_width (hpos : ∀ b, 1 ≤ W b) :
    ∀ j, offF WDef W hW j < W (blkF WDef W hW j) := by
  haveI : 𝚺₁-Function₁ (W : V → V) := hW.to_definable
  intro j
  induction j using ISigma1.sigma1_succ_induction
  · definability
  case zero => simpa using lt_of_lt_of_le _root_.zero_lt_one (hpos 0)
  case succ j ih =>
    by_cases h : offF WDef W hW j + 1 < W (blkF WDef W hW j)
    · obtain ⟨hb, ho⟩ := blkF_offF_within j h; rw [hb, ho]; exact h
    · obtain ⟨hb, ho⟩ := blkF_offF_boundary j (not_lt.mp h)
      rw [hb, ho]
      exact lt_of_lt_of_le _root_.zero_lt_one (hpos (blkF WDef W hW j + 1))

/-- **The elapsed-width identity**: `wsumcF (blkF j) + offF j = j`. -/
theorem wsumcF_blkF_add_offF (hpos : ∀ b, 1 ≤ W b) :
    ∀ j, wsumcF WDef W hW (blkF WDef W hW j) + offF WDef W hW j = j := by
  intro j
  induction j using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ j ih =>
    by_cases h : offF WDef W hW j + 1 < W (blkF WDef W hW j)
    · obtain ⟨hb, ho⟩ := blkF_offF_within j h
      rw [hb, ho, ← add_assoc, ih]
    · obtain ⟨hb, ho⟩ := blkF_offF_boundary j (not_lt.mp h)
      have hw : W (blkF WDef W hW j) = offF WDef W hW j + 1 :=
        le_antisymm (not_lt.mp h) (lt_iff_succ_le.mp (offF_lt_width hpos j))
      rw [hb, ho, add_zero, wsumcF_succ, hw, ← add_assoc, ih]

/-- **`wsumcF (blkF j) ≤ j`** — the elapsed-*width* bound `hβC` consumes. -/
theorem wsumcF_blkF_le (hpos : ∀ b, 1 ≤ W b) (j : V) :
    wsumcF WDef W hW (blkF WDef W hW j) ≤ j :=
  le_trans le_self_add (le_of_eq (wsumcF_blkF_add_offF hpos j))

end GoodsteinPA.BlkRecF
