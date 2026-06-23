/-
# `wip/InternalIg.lean` — Crux 1: the internal Grzegorczyk `g` recursion `ig` (Rathjen Lemma 3.3)

**Status: building the standard-level internal `g`-padding `ig` (wip, off the build target).**

`ig : ℕ → V → V → V` is the internal mirror of `Grz.g` (`Grzegorczyk.lean:343`), built by
**meta-recursion on the standard level `l : ℕ`** (lap-50 insight: the headline needs only a
*standard* level ⟹ no internal Ackermann). The recursion:

  `ig 0 n m = ig0 n m`                                          (base, `InternalCor34`)
  `ig (l+1) n m = iblk (l+1) (max 1 (n - iblockIdx n m))        (for `m < iF(l+1) n`, else `0`)
                    (ig l ((iF l)^[iblockIdx n m] n) (iblockOff n m))`

reading the block decomposition `m ↦ (iblockIdx, iblockOff)` from `InternalGrz` (over the width
hierarchy `f^[·+1] n`, `f = iF l`) and the lead term `ω^(l+1)·c + x` from `InternalCor34.iblk`. The
coefficient `max 1 (n - iblockIdx)` is the faithful internal mirror of Rathjen's `(n - blockIdx).toPNat'`
(`Grz.g` uses an `ℕ+` coefficient, so the lead is always live) — equal to `n - iblockIdx` in the live
regime (`iblockIdx < n`) and clamped to `1` otherwise, keeping `ig` in normal form unconditionally.

This file establishes the recursion's **structural invariants** (this lap): `iF`-positivity, the
recursion equations, the top-exponent shape (`ig l n m < ω^(l+1)` on codes), and `isNF (ig l n m)`.
The remaining `StdCor34.igt`-interface obligations — the `iC ≤ Kg·(n+m+1)` bound (`g_C_bound`), the
within-block descent (`g_desc`), nonzero-in-range (`higt0`) — are the next bricks.
-/
import GoodsteinPA.InternalGrz

namespace GoodsteinPA.InternalIg

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open GoodsteinPA GoodsteinPA.IIter GoodsteinPA.InternalGrz
open GoodsteinPA.InternalONote

variable {V : Type*} [ORingStructure V] [V ⊧ₘ* 𝗜𝚺₁]

/-! ## `iF l` preserves positivity (every block width `(iF l)^[t+1] n ≥ 1`) -/

/-- **Positivity preservation of every meta-level `iF l`** (`1 ≤ x → 1 ≤ iF l x`), by meta-induction
on `l` through `iIter_pos` (`iF (l+1) x = (iF l)^[x] x` keeps `≥ 1` from `iF l`'s preservation). This
is the `hfpos` input the `InternalGrz` block-decomposition laws need (positive widths). -/
theorem iF_pos : ∀ (l : ℕ) (x : V), 1 ≤ x → 1 ≤ iF l x := by
  intro l
  induction l with
  | zero => intro x hx; rw [iF_zero]; exact le_trans hx le_self_add
  | succ l ih =>
      intro x hx
      rw [iF_succ]
      exact iIter_pos (hf := iF_defined l) hx ih x

/-! ## The `ig` recursion and its equations -/

/-- The internal Grzegorczyk `g` (Rathjen Lemma 3.3), standard level. Mirror of `Grz.g`. -/
noncomputable def ig : ℕ → V → V → V
  | 0,     n, m => ig0 n m
  | l + 1, n, m =>
      if m < iF (l + 1) n then
        iblk (l + 1)
          (max 1 (n - iblockIdx (iFDef l) (iF l) (iF_defined l) n m))
          (ig l (iIter (iFDef l) (iF l) (iF_defined l) n
                  (iblockIdx (iFDef l) (iF l) (iF_defined l) n m))
                (iblockOff (iFDef l) (iF l) (iF_defined l) n m))
      else 0

@[simp] theorem ig_zero (n m : V) : ig 0 n m = ig0 n m := rfl

theorem ig_succ_of_lt {l : ℕ} {n m : V} (h : m < iF (l + 1) n) :
    ig (l + 1) n m = iblk (l + 1)
      (max 1 (n - iblockIdx (iFDef l) (iF l) (iF_defined l) n m))
      (ig l (iIter (iFDef l) (iF l) (iF_defined l) n
              (iblockIdx (iFDef l) (iF l) (iF_defined l) n m))
            (iblockOff (iFDef l) (iF l) (iF_defined l) n m)) := by
  simp only [ig, if_pos h]

theorem ig_succ_of_ge {l : ℕ} {n m : V} (h : ¬ m < iF (l + 1) n) : ig (l + 1) n m = 0 := by
  simp only [ig, if_neg h]

/-! ## Top-exponent shape: `ig l n m < ω^(l+1)` on codes (internal `Grz.g_lt`)

The top exponent of `ig l n m` is read off its outermost constructor — either `0` (out of range, or
the finite base `ig0`) or the finite level code `ocOadd 0 (l) 0` (the `iblk l` lead). A direct case
analysis, NO induction. This is the clean-append condition `StdCor34.habove_of_igt_exp` consumes. -/

/-- **`ig l n m`'s top exponent is `≤ l`** (i.e. `ig l n m < ω^(l+1)`): either `0` or `ocOadd 0 l 0`. -/
theorem higt_exp_ig (l : ℕ) (n m : V) :
    ocExp (ig l n m) = 0 ∨ ∃ j : V, j ≤ (l : V) ∧ ocExp (ig l n m) = ocOadd 0 j 0 := by
  cases l with
  | zero =>
      left
      rw [ig_zero]
      rcases lt_or_ge m (n + 2) with h | h
      · exact ocExp_ig0 h
      · rw [ig0_of_ge (not_lt.mpr h)]; exact ocExp_zero
  | succ l =>
      rcases lt_or_ge m (iF (l + 1) n) with h | h
      · right
        refine ⟨((l + 1 : ℕ) : V), le_rfl, ?_⟩
        rw [ig_succ_of_lt h]
        simp only [iblk, ocExp_ocOadd]
      · left
        rw [ig_succ_of_ge (not_lt.mpr h)]; exact ocExp_zero

/-! ## Normal form: `isNF (ig l n m)` (internal `Grz.g_NF`, unconditional) -/

/-- **Every `ig l n m` is a valid normal-form code.** Meta-induction on `l`: the base is `isNF_ig0`;
the step is `isNF_iblk` with a live coefficient (`max 1 _ ≥ 1`), an NF tail (IH), and the tail nesting
below the block exponent `ocOadd 0 (l+1) 0` — which holds because `ig l`'s top exponent is `≤ l < l+1`
(`higt_exp_ig`). -/
theorem isNF_ig : ∀ (l : ℕ) (n m : V), isNF (ig l n m) := by
  intro l
  induction l with
  | zero => intro n m; rw [ig_zero]; exact isNF_ig0 n m
  | succ l ih =>
      intro n m
      rcases lt_or_ge m (iF (l + 1) n) with h | h
      · rw [ig_succ_of_lt h]
        set bi := iblockIdx (iFDef l) (iF l) (iF_defined l) n m with hbi
        set tn := iIter (iFDef l) (iF l) (iF_defined l) n bi with htn
        set tm := iblockOff (iFDef l) (iF l) (iF_defined l) n m with htm
        refine isNF_iblk (Nat.le_add_left 1 l) ?_ (ih tn tm) ?_
        · -- coefficient `max 1 _ ≠ 0`
          exact (lt_of_lt_of_le _root_.zero_lt_one (le_max_left _ _)).ne'
        · -- tail nests below `ocOadd 0 (l+1) 0`
          right
          rcases higt_exp_ig l tn tm with h0 | ⟨j, hjl, hj⟩
          · rw [h0]; exact icmp_zero_ocOadd _ _ _
          · rw [hj]
            exact icmp_ocOadd_lt_coeff
              (lt_of_le_of_lt hjl (by exact_mod_cast Nat.lt_succ_self l))
      · rw [ig_succ_of_ge (not_lt.mpr h)]; exact isNF_zero

end GoodsteinPA.InternalIg
