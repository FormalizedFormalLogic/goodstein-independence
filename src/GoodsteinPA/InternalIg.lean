/-
# `InternalIg.lean` — Crux 1: the internal Grzegorczyk `g` recursion `ig` (Rathjen Lemma 3.3)

**Status: COMPLETE (sorry-free, axiom-clean); promoted to `src/` (lap 54), in the build.** The full
`StdCor34.igt`-interface (NF, `≠0`, within-block descent `= Grz.g_desc`, `iC`-bound, top-exponent shape)
plus the totalized `igtTot` (unconditional props) are built here.

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
import GoodsteinPA.Compat

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

/-! ### Block-step laws for the descent (mirror of `Grz.blockIdx_eq`'s within/boundary outcomes)

The descent `g_desc` reasons about how `blockIdx`/`blockOff` change under `m ↦ m+1`. Internally the
`BlkRec` step laws (`blk_off_within`/`blk_off_boundary`) give this directly — but `iblockIdx … n m`
and `iblockIdx … n (m+1)` read *different* width codes (`iwseq … (m+1)` vs `iwseq … (m+2)`), so we
first re-express the `m`-state against the longer common code `iwseq … (m+1+1)` via prefix-invariance
(`BlkRec.blk_prefix_congr`). -/

/-- `iblockIdx … n m` against the *longer* common code `iwseq … n (m+1+1)` (prefix-invariance: the two
codes agree on `[0,m]`, the indices `blk m` actually reads). -/
theorem iblockIdx_common (n m : V) :
    iblockIdx fDef f hf n m = BlkRec.blk (iwseq fDef f hf n (m + 1 + 1)) m := by
  rw [iblockIdx]
  apply BlkRec.blk_prefix_congr
  intro b hb
  rw [znth_iwseq (hf := hf) b (lt_of_le_of_lt hb (lt_add_one m)),
      znth_iwseq (hf := hf) b (lt_trans (lt_of_le_of_lt hb (lt_add_one m)) (lt_add_one (m + 1)))]

/-- `iblockOff … n m` against the longer common code (prefix-invariance, as `iblockIdx_common`). -/
theorem iblockOff_common (n m : V) :
    iblockOff fDef f hf n m = BlkRec.off (iwseq fDef f hf n (m + 1 + 1)) m := by
  rw [iblockOff]
  apply BlkRec.off_prefix_congr
  intro b hb
  rw [znth_iwseq (hf := hf) b (lt_of_le_of_lt hb (lt_add_one m)),
      znth_iwseq (hf := hf) b (lt_trans (lt_of_le_of_lt hb (lt_add_one m)) (lt_add_one (m + 1)))]

/-- **The block step dichotomy** (`Grz.blockIdx_eq` outcomes, internalised). Under `m ↦ m+1` either the
block index is fixed and the offset advances by one (within block), or the index rolls to the next
block and the offset resets to `0` (boundary). Read straight off the `BlkRec` step laws on the common
code `iwseq … n (m+1+1)`. -/
theorem iblock_step (n m : V) :
    (iblockIdx fDef f hf n (m + 1) = iblockIdx fDef f hf n m ∧
        iblockOff fDef f hf n (m + 1) = iblockOff fDef f hf n m + 1)
      ∨ (iblockIdx fDef f hf n (m + 1) = iblockIdx fDef f hf n m + 1 ∧
        iblockOff fDef f hf n (m + 1) = 0) := by
  have hI1 : iblockIdx fDef f hf n (m + 1)
      = BlkRec.blk (iwseq fDef f hf n (m + 1 + 1)) (m + 1) := rfl
  have hO1 : iblockOff fDef f hf n (m + 1)
      = BlkRec.off (iwseq fDef f hf n (m + 1 + 1)) (m + 1) := rfl
  rw [hI1, hO1, iblockIdx_common (hf := hf) n m, iblockOff_common (hf := hf) n m]
  by_cases h : BlkRec.off (iwseq fDef f hf n (m + 1 + 1)) m + 1
      < znth (iwseq fDef f hf n (m + 1 + 1)) (BlkRec.blk (iwseq fDef f hf n (m + 1 + 1)) m)
  · exact Or.inl (BlkRec.blk_off_within _ m h)
  · exact Or.inr (BlkRec.blk_off_boundary _ m (not_lt.mp h))

/-! ### `ipsum` monotonicity and the `iblockIdx < n` bound (mirror of `Grz.blockIdx_lt`) -/

/-- `ipsum f n i ≤ ipsum f n (i + d)`: each extra block has nonneg width. -/
theorem ipsum_le_add {n i : V} : ∀ d : V, ipsum fDef f hf n i ≤ ipsum fDef f hf n (i + d) := by
  intro d
  induction d using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ d ih => rw [← add_assoc, ipsum_succ]; exact le_trans ih le_self_add

/-- `ipsum` is monotone in the block count. -/
theorem ipsum_le_of_le {n i j : V} (h : i ≤ j) :
    ipsum fDef f hf n i ≤ ipsum fDef f hf n j := by
  have he : i + (j - i) = j := by rw [add_comm]; exact sub_add_self_of_le h
  calc ipsum fDef f hf n i ≤ ipsum fDef f hf n (i + (j - i)) := ipsum_le_add _
    _ = ipsum fDef f hf n j := by rw [he]

/-- The diagonal iterate is below the full block-sum: `f^[n] n ≤ ipsum f n n` (mirror of
`Grz.F_succ_le_psum`; the last summand `f^[n] n` is one term of `ipsum f n n`). -/
theorem iter_le_ipsum_diag {n : V} (hn : 1 ≤ n) :
    iIter fDef f hf n n ≤ ipsum fDef f hf n n := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, (sub_add_self_of_le hn).symm⟩
  rw [ipsum_succ]; exact le_add_self

/-- **`iblockIdx … n m < n`** in the live range (mirror of `Grz.blockIdx_lt`). If `iblockIdx ≥ n` then
`ipsum f n n ≤ ipsum f n iblockIdx ≤ m`, contradicting `m < ipsum f n n`. -/
theorem iblockIdx_lt {n m : V} (hn : 1 ≤ n) (hfpos : ∀ x, 1 ≤ x → 1 ≤ f x)
    (hm : m < ipsum fDef f hf n n) : iblockIdx fDef f hf n m < n := by
  by_contra hge
  rw [not_lt] at hge
  have hdecomp := ipsum_iblockIdx_add_iblockOff (hf := hf) (m := m) hn hfpos
  have h1 : ipsum fDef f hf n (iblockIdx fDef f hf n m) ≤ m :=
    le_trans le_self_add (le_of_eq hdecomp)
  have h2 : ipsum fDef f hf n n ≤ ipsum fDef f hf n (iblockIdx fDef f hf n m) :=
    ipsum_le_of_le hge
  exact absurd hm (not_lt.mpr (le_trans h2 h1))

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

/-! ## The within-block descent: `m < iF l n → ig l n (m+1) ≺ ig l n m` (internal `Grz.g_desc`)

THE deep brick of the `igt` interface (`StdCor34.salpha_desc`'s `higt_within`). Meta-induction on the
standard level `l`; base is `icmp_ig0_desc`. The step decomposes `m`'s block via `iblock_step`:
- **within block** (`iblockOff ↦ +1`, index fixed): the lead `ω^(l+1)·c` is unchanged and the
  `ig l`-tail descends by the IH (offset `< iF l (iIter … iblockIdx)` by `iblockOff_lt_width`) —
  `icmp_iblk_within`;
- **block boundary** (`iblockOff ↦ 0`, index `+1`): the lead coefficient `max 1 (n - iblockIdx)`
  *strictly drops* (since `iblockIdx (m+1) < n` by `iblockIdx_lt`, so `n - (i+1) < n - i` with both
  `≥ 1`), deciding `≺` outright regardless of the tails — `icmp_iblk_boundary`;
- **exhaustion** (`m+1 ≥ iF(l+1)n`): `ig l n (m+1) = 0 ≺ ig l n m` (a positive `iblk`) by
  `icmp_zero_ocOadd`. -/
theorem higt_within : ∀ (l : ℕ) (n m : V), m < iF l n →
    icmp (ig l n (m + 1)) (ig l n m) = 0 := by
  intro l
  induction l with
  | zero =>
      intro n m hm
      simp only [ig_zero]
      rw [iF_zero] at hm
      exact icmp_ig0_desc hm
  | succ l ih =>
      intro n m hm
      have hn : 1 ≤ n := by
        rcases eq_or_ne n 0 with rfl | hn0
        · rw [iF_succ, iIter_zero] at hm
          exact absurd hm (not_lt.mpr (Arithmetic.zero_le m))
        · exact pos_iff_one_le.mp (pos_iff_ne_zero.mpr hn0)
      have hfpos := iF_pos (V := V) l
      rw [ig_succ_of_lt hm]
      by_cases hm1 : m + 1 < iF (l + 1) n
      · rw [ig_succ_of_lt hm1]
        rcases iblock_step (hf := iF_defined l) n m with ⟨hidx, hoff⟩ | ⟨hidx, hoff⟩
        · -- within block: lead fixed, the `ig l`-tail descends by the IH
          rw [hidx, hoff]
          refine icmp_iblk_within (l + 1) _ (ih _ _ ?_)
          have h := iblockOff_lt_width (hf := iF_defined l) (m := m) hn hfpos
          rwa [iIter_succ] at h
        · -- block boundary: the lead coefficient strictly drops
          rw [hidx, hoff]
          refine icmp_iblk_boundary (l + 1) ?_
          have hlt : iblockIdx (iFDef l) (iF l) (iF_defined l) n (m + 1) < n :=
            iblockIdx_lt (hf := iF_defined l) hn hfpos
              (lt_of_lt_of_le hm1 (by rw [iF_succ]; exact iter_le_ipsum_diag (hf := iF_defined l) hn))
          rw [hidx] at hlt
          have hbin : iblockIdx (iFDef l) (iF l) (iF_defined l) n m < n :=
            lt_trans (lt_add_one _) hlt
          have hnbi : 1 ≤ n - iblockIdx (iFDef l) (iF l) (iF_defined l) n m :=
            pos_iff_one_le.mp (pos_sub_iff_lt.mpr hbin)
          have h1 : 1 ≤ n - (iblockIdx (iFDef l) (iF l) (iF_defined l) n m + 1) :=
            pos_iff_one_le.mp (pos_sub_iff_lt.mpr hlt)
          have heq : n - (iblockIdx (iFDef l) (iF l) (iF_defined l) n m + 1)
              = n - iblockIdx (iFDef l) (iF l) (iF_defined l) n m - 1 := Arithmetic.sub_sub.symm
          rw [max_eq_right h1, heq]
          calc n - iblockIdx (iFDef l) (iF l) (iF_defined l) n m - 1
                < (n - iblockIdx (iFDef l) (iF l) (iF_defined l) n m - 1) + 1 := lt_add_one _
            _ = n - iblockIdx (iFDef l) (iF l) (iF_defined l) n m := sub_add_self_of_le hnbi
            _ ≤ max 1 (n - iblockIdx (iFDef l) (iF l) (iF_defined l) n m) := le_max_right _ _
      · -- exhaustion: `ig (l+1) n (m+1) = 0 ≺` a positive `iblk`
        rw [ig_succ_of_ge hm1, iblk]
        exact icmp_zero_ocOadd _ _ _

/-! ## Nonzero in range: `m < iF l n → ig l n m ≠ 0` (internal `Grz.g`-positivity, the `higt0` prop)

In the live range `ig l n m` is a positive code: `ig0` is `ω^0·(n+2-m)` (`ig0_ne_zero`) and `iblk (l+1)`
is `ω^(ω·…)·c + x` (`ocOadd_ne_zero`). This is the `StdCor34.salpha_*` `higt0` input. -/
theorem ig_ne_zero (l : ℕ) (n m : V) (hm : m < iF l n) : ig l n m ≠ 0 := by
  cases l with
  | zero =>
      rw [ig_zero, iF_zero] at *
      have hm2 : m < n + 2 := by
        have h : m < n + 1 + 1 := lt_trans hm (lt_add_one _)
        rwa [add_assoc, one_add_one_eq_two] at h
      exact ig0_ne_zero hm2
  | succ l =>
      rw [ig_succ_of_lt hm, iblk]
      exact ocOadd_ne_zero _ _ _

/-! ## Totalized `igt` for the `StdCor34` interface (unconditional NF/≠0/exp/C; in-range descent)

The `StdCor34.salpha_*` interface demands `higtNF`/`higt0`/`habove`/`higtC` **unconditionally**, but
`ig l n m = 0` out of range (`ig_succ_of_ge`). Totalize with a fixed nonzero finite default
`ig0 0 0 = ω^0·2` so those four props become unconditional; the within-block descent (`igtTot_within`)
stays **in-range** — the single place Rathjen's domination (Lemma 3.2: block width `≤ iF l (blk)`) is
consumed when wiring `salpha_desc`'s `higt_within` hypothesis. -/

/-- The totalized internal Grzegorczyk tail: `ig l n m` in range, a fixed nonzero finite code else. -/
noncomputable def igtTot (l : ℕ) (n m : V) : V := if m < iF l n then ig l n m else ig0 0 0

theorem igtTot_in {l : ℕ} {n m : V} (h : m < iF l n) : igtTot l n m = ig l n m := if_pos h
theorem igtTot_out {l : ℕ} {n m : V} (h : ¬ m < iF l n) : igtTot l n m = ig0 0 0 := if_neg h

/-- **`higtNF`** (unconditional): NF in range via `isNF_ig`, NF of the finite default else. -/
theorem isNF_igtTot (l : ℕ) (n m : V) : isNF (igtTot l n m) := by
  rcases lt_or_ge m (iF l n) with h | h
  · rw [igtTot_in h]; exact isNF_ig l n m
  · rw [igtTot_out (not_lt.mpr h)]; exact isNF_ig0 0 0

/-- **`higt0`** (unconditional): nonzero in range via `ig_ne_zero`, nonzero default else. -/
theorem igtTot_ne_zero (l : ℕ) (n m : V) : igtTot l n m ≠ 0 := by
  rcases lt_or_ge m (iF l n) with h | h
  · rw [igtTot_in h]; exact ig_ne_zero l n m h
  · rw [igtTot_out (not_lt.mpr h)]; exact ig0_ne_zero (by norm_num)

/-- **`higt_exp`** (unconditional): top exponent `0` or finite `≤ l` in range (`higt_exp_ig`); `0` for
the finite default. Feeds `StdCor34.habove_of_igt_exp`. -/
theorem higt_exp_igtTot (l : ℕ) (n m : V) :
    ocExp (igtTot l n m) = 0 ∨ ∃ j : V, j ≤ (l : V) ∧ ocExp (igtTot l n m) = ocOadd 0 j 0 := by
  rcases lt_or_ge m (iF l n) with h | h
  · rw [igtTot_in h]; exact higt_exp_ig l n m
  · rw [igtTot_out (not_lt.mpr h)]; exact Or.inl (ocExp_ig0 (by norm_num))

/-- **`higtC`** (unconditional): the in-range `iC_ig_bound` bumped to also cover the constant default
(`iC (ig0 0 0) ≤ 2`), using `Kg' = max 2 Kg`. -/
theorem iC_igtTot_bound (l : ℕ) :
    ∃ Kg : V, 0 < Kg ∧ ∀ n m, iC (igtTot l n m) ≤ Kg * (n + m + 1) := by
  obtain ⟨Kg, hKgpos, hKg⟩ := iC_ig_bound (V := V) l
  refine ⟨max 2 Kg, lt_of_lt_of_le hKgpos (le_max_right _ _), fun n m => ?_⟩
  rcases lt_or_ge m (iF l n) with h | h
  · rw [igtTot_in h]; exact le_trans (hKg n m) (by gcongr; exact le_max_right _ _)
  · rw [igtTot_out (not_lt.mpr h)]
    calc iC (ig0 (0 : V) 0) ≤ (0 : V) + 2 := iC_ig0_le 0 0
      _ = 2 := by rw [zero_add]
      _ ≤ max 2 Kg * (n + m + 1) :=
          le_trans (le_max_left _ _) (le_mul_of_one_le_right (Arithmetic.zero_le _) le_add_self)

/-- **The in-range within-block descent** (the `salpha_desc.higt_within` brick). Under the within-block
condition `m + 1 < iF l n` (supplied at the `StdCor34` level by domination: offsets stay below the
block width `≤ iF l (blk)`), both `igtTot` values are `ig`, and `higt_within` gives the descent. -/
theorem igtTot_within (l : ℕ) (n m : V) (h : m + 1 < iF l n) :
    icmp (igtTot l n (m + 1)) (igtTot l n m) = 0 := by
  have hm : m < iF l n := lt_trans (lt_add_one m) h
  rw [igtTot_in h, igtTot_in hm]
  exact higt_within l n m hm

/-! ## Definability of the `ig`-recursion leaf functions (toward the crux-1 `hdef` obligation)

The `crux1_internal_run` (`wip/StdCor34.lean`) needs `𝚺₁`-definability of the slowed sequence. These
leaf instances are the reusable bottom of that chain — built with **explicit `Definable.comp` terms**
(the `definability` aesop tactic blows its depth limit on the nested `ocOadd`/`iwseq` compositions; see
memory `definability-aesop-depth-blowup`). The remaining links (`ig0`/`ig`/`igtTot`/`salpha`/`bbeta`)
need an `ite`-definability lemma + the `ig` meta-recursion, deferred (`PENDING_WORK`). -/

open LO.FirstOrder.Arithmetic.HierarchySymbol in
omit [V ⊧ₘ* 𝗜𝚺₁] in
/-- **`ite`-definability** (the key unlock for the `ig`/`bbeta` chain — Foundation has no direct
helper). `fun v ↦ if P v then f v else g v` is definable from a Δ-definable `P` (both `P` and `¬P`
definable) and definable `f`,`g`, via the graph disjunction `z = ite ↔ (P ∧ z=f) ∨ (¬P ∧ z=g)`. -/
lemma definableFunction_ite {k : ℕ} {Γ : SigmaPiDelta} {M : ℕ}
    {P : (Fin k → V) → Prop} [DecidablePred P] {f g : (Fin k → V) → V}
    (hP : Γ-[M + 1].Definable P) (hnP : Γ-[M + 1].Definable (fun v => ¬ P v))
    (hf : Γ-[M + 1].DefinableFunction f) (hg : Γ-[M + 1].DefinableFunction g) :
    Γ-[M + 1].DefinableFunction (fun v => if P v then f v else g v) := by
  refine Definable.of_iff
    (Q := fun v : Fin (k + 1) → V =>
      (P (fun i => v i.succ) ∧ v 0 = f (fun i => v i.succ)) ∨
      ((¬ P (fun i => v i.succ)) ∧ v 0 = g (fun i => v i.succ))) ?_ ?_
  · exact Definable.or (Definable.and (hP.retraction Fin.succ) hf)
      (Definable.and (hnP.retraction Fin.succ) hg)
  · intro v
    by_cases h : P (fun i => v i.succ) <;> simp [h]

open LO.FirstOrder.Arithmetic.HierarchySymbol in
/-- `iblk k` is `𝚺₁`-definable in `(c, x)` (the lead `ω^k·c + x`, fixed standard level `k`). -/
instance iblk_definable (k : ℕ) (Γ) : Γ-[m + 1]-Function₂ (iblk k : V → V → V) := by
  unfold iblk
  exact DefinableFunction₃.comp (F := ocOadd) (hF := ocOadd_definable.of_sigmaOne)
    (DefinableFunction.const (ocOadd 0 (k : V) 0))
    (DefinableFunction.var 0) (DefinableFunction.var 1)

open LO.FirstOrder.Arithmetic.HierarchySymbol in
/-- `iblockIdx` (for the concrete level `l`) is `𝚺₁`-definable in `(n, m)`: `blk (iwseq … n (m+1)) m`. -/
instance iblockIdx_definable (l : ℕ) (Γ) :
    Γ-[m + 1]-Function₂ (iblockIdx (iFDef l) (iF l) (iF_defined l) : V → V → V) := by
  unfold iblockIdx
  exact DefinableFunction₂.comp (F := BlkRec.blk)
    (DefinableFunction₂.comp (F := iwseq (iFDef l) (iF l) (iF_defined l))
      (DefinableFunction.var 0)
      (DefinableFunction₂.comp (F := (· + ·)) (DefinableFunction.var 1) (DefinableFunction.const 1)))
    (DefinableFunction.var 1)

open LO.FirstOrder.Arithmetic.HierarchySymbol in
/-- `iblockOff` (for the concrete level `l`) is `𝚺₁`-definable in `(n, m)`: `off (iwseq … n (m+1)) m`. -/
instance iblockOff_definable (l : ℕ) (Γ) :
    Γ-[m + 1]-Function₂ (iblockOff (iFDef l) (iF l) (iF_defined l) : V → V → V) := by
  unfold iblockOff
  exact DefinableFunction₂.comp (F := BlkRec.off)
    (DefinableFunction₂.comp (F := iwseq (iFDef l) (iF l) (iF_defined l))
      (DefinableFunction.var 0)
      (DefinableFunction₂.comp (F := (· + ·)) (DefinableFunction.var 1) (DefinableFunction.const 1)))
    (DefinableFunction.var 1)

open LO.FirstOrder.Arithmetic.HierarchySymbol in
/-- `ig0 n m = if m < n+2 then ω^0·(n+2-m) else 0` is `𝚺₁`-definable in `(n, m)`.
Via `definableFunction_ite`: the guard `m < n+2` is `Δ₀`, the then-branch is an `ocOadd`-comp
(with a `(n+2-m)` sub/add leaf), the else-branch is the constant `0`. -/
instance ig0_definable (Γ) : Γ-[m + 1]-Function₂ (ig0 : V → V → V) := by
  have h : (fun v : Fin 2 → V => ig0 (v 0) (v 1))
      = (fun v : Fin 2 → V => if v 1 < v 0 + 2 then ocOadd 0 (v 0 + 2 - v 1) 0 else 0) := by
    funext v; simp only [ig0]
  show Γ-[m + 1].DefinableFunction (fun v : Fin 2 → V => ig0 (v 0) (v 1))
  rw [h]
  apply definableFunction_ite
  · definability
  · definability
  · exact DefinableFunction₃.comp (F := ocOadd) (hF := ocOadd_definable.of_sigmaOne)
      (DefinableFunction.const 0)
      (DefinableFunction₂.comp (F := (· - ·))
        (DefinableFunction₂.comp (F := (· + ·)) (DefinableFunction.var 0) (DefinableFunction.const 2))
        (DefinableFunction.var 1))
      (DefinableFunction.const 0)
  · exact DefinableFunction.const 0

open LO.FirstOrder.Arithmetic.HierarchySymbol in
/-- **`ig l` is `𝚺₁`-definable in `(n, m)`, for every standard level `l`.** Meta-induction on `l`
(NOT internal): base `ig 0 = ig0` (`ig0_definable`); step `ig (l+1) = if m < iF(l+1)n then
iblk(l+1) (max 1 (n - iblockIdx)) (ig l (iIter n iblockIdx) iblockOff) else 0` via
`definableFunction_ite`, the recursive `ig l` discharged by the IH. Proved at the `𝚺₁` level so the
IH and all sub-arguments live on the `𝚺` side that `DefinableFunction₂.comp` expects. -/
lemma ig_definable_aux : ∀ l : ℕ, 𝚺₁-Function₂ (ig l : V → V → V)
  | 0 => by
      show 𝚺₁.DefinableFunction (fun v : Fin 2 → V => ig 0 (v 0) (v 1))
      simp only [ig_zero]; exact ig0_definable 𝚺
  | l + 1 => by
      have ih := ig_definable_aux l
      have h : (fun v : Fin 2 → V => ig (l + 1) (v 0) (v 1))
          = (fun v : Fin 2 → V => if v 1 < iF (l + 1) (v 0) then
              iblk (l + 1)
                (max 1 (v 0 - iblockIdx (iFDef l) (iF l) (iF_defined l) (v 0) (v 1)))
                (ig l (iIter (iFDef l) (iF l) (iF_defined l) (v 0)
                        (iblockIdx (iFDef l) (iF l) (iF_defined l) (v 0) (v 1)))
                      (iblockOff (iFDef l) (iF l) (iF_defined l) (v 0) (v 1)))
            else 0) := by
        funext v; simp only [ig]
      show 𝚺₁.DefinableFunction (fun v : Fin 2 → V => ig (l + 1) (v 0) (v 1))
      rw [h]
      apply definableFunction_ite
      · -- guard `v 1 < iF (l+1) (v 0)`
        have hiF : 𝚺-[(0:ℕ) + 1].DefinableFunction₁ (iF (l + 1) : V → V) :=
          iF_definable' (l + 1) 𝚺
        exact Definable.comp₂ (P := (· < ·)) (DefinableFunction.var 1)
          (DefinableFunction₁.comp (hF := hiF) (DefinableFunction.var 0))
      · have hiF : 𝚺-[(0:ℕ) + 1].DefinableFunction₁ (iF (l + 1) : V → V) :=
          iF_definable' (l + 1) 𝚺
        exact Definable.not (Definable.comp₂ (P := (· < ·)) (DefinableFunction.var 1)
          (DefinableFunction₁.comp (hF := hiF) (DefinableFunction.var 0)))
      · -- then-branch: the `iblk`-comp
        refine DefinableFunction₂.comp (F := iblk (l + 1)) (hF := iblk_definable (l + 1) 𝚺)
          ?_ ?_
        · -- `max 1 (v0 - iblockIdx … v0 v1)`
          exact DefinableFunction₂.comp (F := max) (hF := max_definable 𝚺₁)
            (DefinableFunction.const 1)
            (DefinableFunction₂.comp (F := (· - ·))
              (DefinableFunction.var 0)
              (DefinableFunction₂.comp (F := iblockIdx (iFDef l) (iF l) (iF_defined l))
                (DefinableFunction.var 0) (DefinableFunction.var 1)))
        · -- `ig l (iIter … v0 iblockIdx) (iblockOff … v0 v1)`
          refine DefinableFunction₂.comp (F := ig l) (hF := ih) ?_ ?_
          · exact DefinableFunction₂.comp (F := iIter (iFDef l) (iF l) (iF_defined l))
              (DefinableFunction.var 0)
              (DefinableFunction₂.comp (F := iblockIdx (iFDef l) (iF l) (iF_defined l))
                (DefinableFunction.var 0) (DefinableFunction.var 1))
          · exact DefinableFunction₂.comp (F := iblockOff (iFDef l) (iF l) (iF_defined l))
              (DefinableFunction.var 0) (DefinableFunction.var 1)
      · exact DefinableFunction.const 0

open LO.FirstOrder.Arithmetic.HierarchySymbol in
/-- `ig l` definable at every hierarchy level (the form the `salpha`/`bbeta` definability chain wants). -/
instance ig_definable (l : ℕ) (Γ) : Γ-[m + 1]-Function₂ (ig l : V → V → V) :=
  (ig_definable_aux l).of_sigmaOne

open LO.FirstOrder.Arithmetic.HierarchySymbol in
/-- `igtTot l n m = if m < iF l n then ig l n m else ig0 0 0` is `𝚺₁`-definable in `(n, m)`. -/
instance igtTot_definable (l : ℕ) (Γ) : Γ-[m + 1]-Function₂ (igtTot l : V → V → V) := by
  have h : (fun v : Fin 2 → V => igtTot l (v 0) (v 1))
      = (fun v : Fin 2 → V => if v 1 < iF l (v 0) then ig l (v 0) (v 1) else ig0 0 0) := by
    funext v; simp only [igtTot]
  show Γ-[m + 1].DefinableFunction (fun v : Fin 2 → V => igtTot l (v 0) (v 1))
  rw [h]
  apply definableFunction_ite
  · have hiF : 𝚺-[m + 1].DefinableFunction₁ (iF l : V → V) := iF_definable' l 𝚺
    exact Definable.comp₂ (P := (· < ·)) (DefinableFunction.var 1)
      (DefinableFunction₁.comp (hF := hiF) (DefinableFunction.var 0))
  · have hiF : 𝚺-[m + 1].DefinableFunction₁ (iF l : V → V) := iF_definable' l 𝚺
    exact Definable.not (Definable.comp₂ (P := (· < ·)) (DefinableFunction.var 1)
      (DefinableFunction₁.comp (hF := hiF) (DefinableFunction.var 0)))
  · exact DefinableFunction₂.comp (F := ig l) (hF := ig_definable l Γ)
      (DefinableFunction.var 0) (DefinableFunction.var 1)
  · exact DefinableFunction.const (ig0 0 0)

end GoodsteinPA.InternalIg
