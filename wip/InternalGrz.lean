/-
# `InternalGrz.lean` — Crux 1: the internal block decomposition for `ig` (Rathjen `g`-padding)

**Status: COMPLETE (sorry-free, axiom-clean); promoted to `src/` (lap 53), in the build.**

Rathjen's `g (l+1) n m` recurses through the block decomposition `m ↦ (blockIdx, blockOff)` where
block `i` has width `f^[i+1] n` (`f = F l`). This file supplies that decomposition internally by
**reusing the already-complete `BlkRec` bookkeeping** (`src/`): the widths `f^[i+1] n` are packaged
as a finite width *code* `iwseq f n N = ⟨f^[1]n, …, f^[N]n⟩`, and the decomposition of `m` is then
`BlkRec.blk (iwseq f n (m+1)) m` / `BlkRec.off (…) m` — with `BlkRec`'s invariants (`blk_succ_dich`,
`wsumc_blk_add_off`, `off_lt_width`, prefix-invariance) carrying over for free.

The key bridge proved here is **`wsumc (iwseq f n N) = ipsum f n`** (cumulative width of the code = the
internal partial-sum of iterates `Σ_{t=1}^i f^[t] n`), which turns `BlkRec.wsumc_blk_add_off` into the
classical `m = psum (blockIdx) + blockOff` decomposition law (`Grz.psum_add_blockOff`).
-/
import GoodsteinPA.IIter
import GoodsteinPA.BlkRec
import GoodsteinPA.Compat

namespace GoodsteinPA.InternalGrz

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.HierarchySymbol
open GoodsteinPA GoodsteinPA.IIter GoodsteinPA.InternalONote

variable {V : Type*} [ORingStructure V] [V ⊧ₘ* 𝗜𝚺₁]

variable {fDef : 𝚺₁.Semisentence 2} {f : V → V} {hf : 𝚺₁.DefinedFunction₁ f fDef}

-- `iIter_succ` is `@[simp]`; inside `definability` it rewrites `iIter n (k+1) ↦ f (iIter n k)`,
-- exposing the abstract `f` (which has no standalone definability). Drop it from the simp set here.
attribute [-simp] IIter.iIter_succ

-- Re-expose the `(fDef,f,hf)`-family definability as *instances* (the `IIter` versions are lemmas,
-- since `f`/`hf` aren't determined by the `Def` alone — but here they're fixed section variables, so
-- unification on the function head recovers them). Lets `definability`/`DefinableFunction₂.comp` fire.
instance iIter_inst' (Γ) : Γ-[m + 1]-Function₂ (iIter fDef f hf : V → V → V) :=
  IIter.iIter_definable' (hf := hf) Γ
instance ipsum_inst' (Γ) : Γ-[m + 1]-Function₂ (ipsum fDef f hf : V → V → V) :=
  IIter.ipsum_definable' (hf := hf) Γ

/-! ## The width code `iwseq f n N = ⟨f^[1]n, f^[2]n, …, f^[N]n⟩` -/

/-- Blueprint for `iwseq` (1 parameter = the seed `n`): append `f^[i+1] n` at step `i`. -/
def iwseq.blueprint (fDef : 𝚺₁.Semisentence 2) : PR.Blueprint 1 where
  zero := .mkSigma “y x. y = 0”
  succ := .mkSigma “y ih i x. ∃ w, !(iIterDef fDef) w x (i + 1) ∧ !seqConsDef y ih w”

noncomputable def iwseq.construction (fDef : 𝚺₁.Semisentence 2) (f : V → V)
    (hf : 𝚺₁.DefinedFunction₁ f fDef) : PR.Construction V (iwseq.blueprint fDef) where
  zero := fun _ ↦ ∅
  succ := fun x i ih ↦ seqCons ih (iIter fDef f hf (x 0) (i + 1))
  zero_defined := .mk fun v ↦ by simp [iwseq.blueprint, emptyset_def]
  succ_defined := .mk fun v ↦ by
    simp [iwseq.blueprint, (IIter.iIter_defined (hf := hf)).iff, seqCons_defined.iff]

/-- The length-`N` width code `⟨f^[1]n, …, f^[N]n⟩`. -/
noncomputable def iwseq (fDef : 𝚺₁.Semisentence 2) (f : V → V) (hf : 𝚺₁.DefinedFunction₁ f fDef)
    (n N : V) : V := (iwseq.construction fDef f hf).result ![n] N

@[simp] lemma iwseq_zero (n : V) : iwseq fDef f hf n 0 = ∅ := by
  simp [iwseq, iwseq.construction]

@[simp] lemma iwseq_succ (n N : V) :
    iwseq fDef f hf n (N + 1) = seqCons (iwseq fDef f hf n N) (iIter fDef f hf n (N + 1)) := by
  simp [iwseq, iwseq.construction]

def iwseqDef (fDef : 𝚺₁.Semisentence 2) : 𝚺₁.Semisentence 3 :=
  (iwseq.blueprint fDef).resultDef.rew (Rew.subst ![#0, #2, #1])

lemma iwseq_defined : 𝚺₁-Function₂ (iwseq fDef f hf : V → V → V) via iwseqDef fDef := .mk
  fun v ↦ by simp [(iwseq.construction fDef f hf).result_defined_iff, iwseqDef, iwseq]; rfl

instance iwseq_definable : 𝚺₁-Function₂ (iwseq fDef f hf : V → V → V) :=
  (iwseq_defined (hf := hf)).to_definable
instance iwseq_definable' (Γ) : Γ-[m + 1]-Function₂ (iwseq fDef f hf : V → V → V) :=
  iwseq_definable.of_sigmaOne

@[simp] lemma iwseq_seq (n N : V) : Seq (iwseq fDef f hf n N) := by
  induction N using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ N ih => rw [iwseq_succ]; exact ih.seqCons _

@[simp] lemma iwseq_lh (n N : V) : lh (iwseq fDef f hf n N) = N := by
  induction N using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ N ih => rw [iwseq_succ, Seq.lh_seqCons _ (iwseq_seq (hf := hf) n N), ih]

/-- **The defining property**: `znth (iwseq f n N) k = f^[k+1] n` for `k < N`. -/
theorem znth_iwseq {n N : V} : ∀ k < N, znth (iwseq fDef f hf n N) k = iIter fDef f hf n (k + 1) := by
  induction N using ISigma1.sigma1_succ_induction
  · definability
  case zero => intro k hk; exact absurd hk (by simp)
  case succ N ih =>
    intro k hk
    rw [iwseq_succ]
    rcases lt_or_eq_of_le (le_iff_lt_succ.mpr hk) with hlt | heq
    · rw [znth_seqCons_of_lt (iwseq_seq (hf := hf) n N) _ (by rw [iwseq_lh (hf := hf)]; exact hlt)]
      exact ih k hlt
    · subst heq
      have hself := znth_seqCons_self (iwseq_seq (hf := hf) n k) (iIter fDef f hf n (k + 1))
      rw [iwseq_lh (hf := hf)] at hself
      exact hself

/-! ## The bridge `wsumc (iwseq f n N) i = ipsum f n i`

The cumulative width of the code (read by `BlkRec.wsumc`) is exactly the internal partial-sum of
iterates `ipsum` — so `BlkRec`'s elapsed-width identity `wsumc (blk m) + off m = m` becomes Rathjen's
`m = psum (blockIdx) + blockOff`. -/

theorem wsumc_iwseq {n N : V} : ∀ i ≤ N,
    BlkRec.wsumc (iwseq fDef f hf n N) i = ipsum fDef f hf n i := by
  intro i
  induction i using ISigma1.sigma1_succ_induction
  · definability
  case zero => intro _; simp
  case succ i ih =>
    intro hiN
    have hi_le : i ≤ N := le_trans le_self_add hiN
    have hi_lt : i < N := lt_of_lt_of_le (lt_add_one i) hiN
    rw [BlkRec.wsumc_succ, ih hi_le, znth_iwseq (hf := hf) i hi_lt, ipsum_succ]

/-! ## Positivity of the iterates (so the block widths are positive)

For `f` that preserves positivity (`1 ≤ x → 1 ≤ f x`, e.g. every `iF l` for `l ≥ 0`) and `1 ≤ n`,
every iterate `f^[c] n ≥ 1`, hence every block width `f^[i+1] n ≥ 1`. -/

theorem iIter_pos {n : V} (hn : 1 ≤ n) (hfpos : ∀ x, 1 ≤ x → 1 ≤ f x) :
    ∀ c, 1 ≤ iIter fDef f hf n c := by
  intro c
  induction c using ISigma1.sigma1_succ_induction
  · definability
  case zero => simpa using hn
  case succ c ih => rw [IIter.iIter_succ]; exact hfpos _ ih

/-- Each block width `znth (iwseq f n N) b = f^[b+1] n` is `≥ 1` on the code's prefix. -/
theorem one_le_znth_iwseq {n N : V} (hn : 1 ≤ n) (hfpos : ∀ x, 1 ≤ x → 1 ≤ f x) :
    ∀ b, b < N → 1 ≤ znth (iwseq fDef f hf n N) b := by
  intro b hb
  rw [znth_iwseq (hf := hf) b hb]
  exact iIter_pos (hf := hf) hn hfpos (b + 1)

/-! ## The block decomposition `m ↦ (iblockIdx, iblockOff)` via `BlkRec` -/

/-- Block index of `m` for the width hierarchy `f^[·+1] n` (`= Grz.blockIdx (F l) n m`). -/
noncomputable def iblockIdx (fDef : 𝚺₁.Semisentence 2) (f : V → V)
    (hf : 𝚺₁.DefinedFunction₁ f fDef) (n m : V) : V := BlkRec.blk (iwseq fDef f hf n (m + 1)) m

/-- Within-block offset of `m` (`= Grz.blockOff (F l) n m`). -/
noncomputable def iblockOff (fDef : 𝚺₁.Semisentence 2) (f : V → V)
    (hf : 𝚺₁.DefinedFunction₁ f fDef) (n m : V) : V := BlkRec.off (iwseq fDef f hf n (m + 1)) m

/-- `iblockIdx ≤ m`. -/
theorem iblockIdx_le (n m : V) : iblockIdx fDef f hf n m ≤ m := BlkRec.blk_le _ m

/-- Prefix-positivity of the width code `iwseq f n (m+1)` on `[0, m]` (its live indices). -/
private theorem hpos_prefix {n m : V} (hn : 1 ≤ n) (hfpos : ∀ x, 1 ≤ x → 1 ≤ f x) :
    ∀ b, b ≤ m → 1 ≤ znth (iwseq fDef f hf n (m + 1)) b := fun b hb =>
  one_le_znth_iwseq (hf := hf) hn hfpos b (lt_of_le_of_lt hb (lt_add_one m))

/-- **The decomposition law** `m = ipsum f n (iblockIdx) + iblockOff` (`Grz.psum_add_blockOff`,
internalised): the `BlkRec` elapsed-width identity transported through the `wsumc = ipsum` bridge. -/
theorem ipsum_iblockIdx_add_iblockOff {n m : V} (hn : 1 ≤ n) (hfpos : ∀ x, 1 ≤ x → 1 ≤ f x) :
    ipsum fDef f hf n (iblockIdx fDef f hf n m) + iblockOff fDef f hf n m = m := by
  have hbridge : BlkRec.wsumc (iwseq fDef f hf n (m + 1)) (iblockIdx fDef f hf n m)
      = ipsum fDef f hf n (iblockIdx fDef f hf n m) :=
    wsumc_iwseq (hf := hf) _ (le_trans (iblockIdx_le n m) le_self_add)
  rw [← hbridge, iblockIdx, iblockOff]
  exact BlkRec.wsumc_blk_add_off _ m (hpos_prefix (hf := hf) hn hfpos)

/-- **The offset is below its block width** `iblockOff < f^[iblockIdx + 1] n` (`Grz.blockOff_lt_width`,
internalised). -/
theorem iblockOff_lt_width {n m : V} (hn : 1 ≤ n) (hfpos : ∀ x, 1 ≤ x → 1 ≤ f x) :
    iblockOff fDef f hf n m < iIter fDef f hf n (iblockIdx fDef f hf n m + 1) := by
  have hlt := BlkRec.off_lt_width (iwseq fDef f hf n (m + 1)) m
    (hpos_prefix (hf := hf) hn hfpos)
  rwa [← iblockIdx, ← iblockOff,
    znth_iwseq (hf := hf) (iblockIdx fDef f hf n m)
      (lt_of_le_of_lt (iblockIdx_le n m) (lt_add_one m))] at hlt

end GoodsteinPA.InternalGrz
