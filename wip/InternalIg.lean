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

/-! ## The coefficient C-bound: `iC (ig l n m) ≤ Kg·(n+m+1)` (internal `Grz.g_C_bound`)

The block-bookkeeping support (`iIter_le_add_ipsum`, `iter_add_iblockOff_le`) mirrors `Grz.iter_le_add_psum`
/ `iter_add_blockOff_le`; both are generic over the fixed `𝚺₁`-function `f`. -/

section Support
variable {fDef : 𝚺₁.Semisentence 2} {f : V → V} {hf : 𝚺₁.DefinedFunction₁ f fDef}

/-- `f^[i] n ≤ n + ipsum f n i` (for `i ≥ 1` the iterate is itself a summand of `ipsum`). -/
theorem iIter_le_add_ipsum (n i : V) :
    iIter fDef f hf n i ≤ n + ipsum fDef f hf n i := by
  induction i using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ i _ => rw [ipsum_succ, ← add_assoc]; exact le_add_self

/-- Block bookkeeping for the bound: `f^[iblockIdx] n + iblockOff ≤ n + m` (`Grz.iter_add_blockOff_le`,
internalised) — the iterate is `≤ n + ipsum`, and `ipsum + iblockOff = m`. -/
theorem iter_add_iblockOff_le {n m : V} (hn : 1 ≤ n) (hfpos : ∀ x, 1 ≤ x → 1 ≤ f x) :
    iIter fDef f hf n (iblockIdx fDef f hf n m) + iblockOff fDef f hf n m ≤ n + m := by
  have h1 := iIter_le_add_ipsum (hf := hf) n (iblockIdx fDef f hf n m)
  have h2 := ipsum_iblockIdx_add_iblockOff (hf := hf) (m := m) hn hfpos
  calc iIter fDef f hf n (iblockIdx fDef f hf n m) + iblockOff fDef f hf n m
      ≤ (n + ipsum fDef f hf n (iblockIdx fDef f hf n m)) + iblockOff fDef f hf n m := by
        gcongr
    _ = n + (ipsum fDef f hf n (iblockIdx fDef f hf n m) + iblockOff fDef f hf n m) := by
        rw [add_assoc]
    _ = n + m := by rw [h2]

end Support

/-- **Lemma 3.3(2) — the coefficient bound** (internal `Grz.g_C_bound`). For each standard level `l`
there is `Kg > 0` with `iC (ig l n m) ≤ Kg·(n+m+1)` for all `n,m`. Meta-induction on `l`: base `Kg=2`
(`iC_ig0_le`); step takes `max (↑(l+1)) K`, the lead data (`l+1`, the clamped coeff `≤ n+1`) and the
tail's bound `K·(tn+tm+1) ≤ K·(n+m+1)` (via `iter_add_iblockOff_le`) each `≤ Kg·(n+m+1)`. -/
theorem iC_ig_bound : ∀ (l : ℕ), ∃ Kg : V, 0 < Kg ∧ ∀ (n m : V), iC (ig l n m) ≤ Kg * (n + m + 1) := by
  intro l
  induction l with
  | zero =>
      refine ⟨2, by norm_num, fun n m => ?_⟩
      rw [ig_zero]
      calc iC (ig0 n m) ≤ n + 2 := iC_ig0_le n m
        _ = 2 + n := by rw [add_comm]
        _ ≤ 2 + n + m := le_self_add
        _ = 2 + (n + m) := by rw [add_assoc]
        _ ≤ 2 * (n + m + 1) := iconst_add_le_mul one_le_two
  | succ l ih =>
      obtain ⟨K, hKpos, hK⟩ := ih
      refine ⟨max (((l + 1 : ℕ) : V)) K, lt_of_lt_of_le hKpos (le_max_right _ _), fun n m => ?_⟩
      rcases lt_or_ge m (iF (l + 1) n) with h | h
      · -- in-range branch (forces `1 ≤ n`, since `iF (l+1) 0 = 0`)
        have hn1 : 1 ≤ n := by
          rcases eq_or_ne n 0 with rfl | hn0
          · rw [iF_succ, iIter_zero] at h
            exact absurd h (not_lt.mpr (Arithmetic.zero_le m))
          · exact pos_iff_one_le.mp (pos_iff_ne_zero.mpr hn0)
        rw [ig_succ_of_lt h, iC_iblk]
        set bi := iblockIdx (iFDef l) (iF l) (iF_defined l) n m with hbi
        set tn := iIter (iFDef l) (iF l) (iF_defined l) n bi with htn
        set tm := iblockOff (iFDef l) (iF l) (iF_defined l) n m with htm
        set M := max (((l + 1 : ℕ) : V)) K with hM
        have hMpos : 1 ≤ M := le_trans (pos_iff_one_le.mp hKpos) (le_max_right _ _)
        have hW1 : (1 : V) ≤ n + m + 1 := le_add_self
        -- piece A: `↑(l+1) ≤ M·(n+m+1)`
        have hA : ((l + 1 : ℕ) : V) ≤ M * (n + m + 1) :=
          le_trans (le_max_left _ _) (le_mul_of_one_le_right (Arithmetic.zero_le _) hW1)
        -- piece B: clamped coefficient `max 1 (n - bi) ≤ M·(n+m+1)`
        have hB : max 1 (n - bi) ≤ M * (n + m + 1) := by
          have hcoeff : max 1 (n - bi) ≤ n + m + 1 :=
            max_le le_add_self (le_trans (sub_le_self n bi) (le_trans le_self_add le_self_add))
          exact le_trans hcoeff (le_mul_of_one_le_left (Arithmetic.zero_le _) hMpos)
        -- piece C: tail `iC (ig l tn tm) ≤ M·(n+m+1)`
        have hCt : iC (ig l tn tm) ≤ M * (n + m + 1) := by
          have hle := iter_add_iblockOff_le (hf := iF_defined l) (m := m) hn1 (iF_pos l)
          calc iC (ig l tn tm) ≤ K * (tn + tm + 1) := hK tn tm
            _ ≤ K * (n + m + 1) := by gcongr
            _ ≤ M * (n + m + 1) := by gcongr; exact le_max_right _ _
        exact max_le (max_le hA hB) hCt
      · rw [ig_succ_of_ge (not_lt.mpr h), iC_zero]; exact Arithmetic.zero_le _

end GoodsteinPA.InternalIg
