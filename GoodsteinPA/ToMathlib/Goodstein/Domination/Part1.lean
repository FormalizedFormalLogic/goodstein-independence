/-
# Goodstein.Dom — Part1
-/
module

public import Mathlib.Algebra.Order.SuccPred
public import Mathlib.SetTheory.Ordinal.Exponential
public import Mathlib.SetTheory.Ordinal.Notation
public meta import Mathlib.SetTheory.Ordinal.Notation  -- shake: keep
public import Mathlib.Tactic.Ring
public import GoodsteinPA.ToMathlib.Goodstein.Defs
public meta import GoodsteinPA.ToMathlib.Goodstein.Defs  -- shake: keep
public import GoodsteinPA.ToMathlib.Hardy
public meta import GoodsteinPA.ToMathlib.Hardy  -- shake: keep

@[expose] public section

namespace Goodstein.Dom

open ONote Ordinal

-- ════════════════ ported: Engine.lean ════════════════
/-
# Goodstein — proof engine (ordinal descent)

This file is the proof machinery behind `goodstein_terminates`. It is NOT part of
the audit surface (that is `Defs`/`Statement`/`Anchors`); it just has to be
correct, which the kernel checks.

## Strategy
Interpret `n`, read in hereditary base `b`, as an ordinal `toOrdinal b n` by
replacing the base `b` with `ω` (same peeling recursion as `bump`). Two facts:

* **Bump invariance** — `toOrdinal (b+1) (bump b n) = toOrdinal b n` (`b ≥ 2`):
  bumping the base `b ↦ b+1` does not change the ordinal, since both read the base
  as `ω`.
* **Strict monotonicity** — `m < n → toOrdinal b m < toOrdinal b n` (`b ≥ 2`):
  the natural order maps to the ordinal order.

Then `a k := toOrdinal (k+2) (G k)` is strictly decreasing while `G k ≠ 0`
(subtract-one strictly lowers the ordinal, the base-bump preserves it), and
`Ordinal` is well-founded, so some `G N = 0`.

Both monotonicity and the leading-coefficient bound are proved together by one
strong induction; `bump` gets the parallel pair over `ℕ`.
-/



/-- **Ordinal interpretation.** Read `n` in hereditary base `b`, replacing `b` by
`ω`. Same top-power peeling as `bump`: with `e = log b n`, `c = n / b^e`,
`r = n % b^e`, `toOrdinal b n = ω^(toOrdinal b e) * c + toOrdinal b r`. -/
noncomputable def toOrdinal (b : ℕ) (n : ℕ) : Ordinal.{0} :=
  if h : n = 0 then 0
  else
    have _hn : n ≠ 0 := h
    ω ^ toOrdinal b (Nat.log b n) * (n / b ^ Nat.log b n : ℕ)
      + toOrdinal b (n % b ^ Nat.log b n)
termination_by n
decreasing_by
  · exact Nat.log_lt_self b h
  · have hb : 0 < b ^ Nat.log b n := by
      rcases Nat.eq_zero_or_pos b with hb0 | hbpos
      · subst hb0; simp [Nat.log_zero_left]
      · exact Nat.pow_pos hbpos
    exact lt_of_lt_of_le (Nat.mod_lt _ hb) (Nat.pow_log_le_self b h)

@[simp] lemma toOrdinal_zero (b : ℕ) : toOrdinal b 0 = 0 := by
  rw [toOrdinal]; simp

@[simp] lemma bump_zero (b : ℕ) : bump b 0 = 0 := by
  rw [bump]; simp

/-- Unfolding `toOrdinal` at a nonzero argument (peel the top power). -/
lemma toOrdinal_pos (b n : ℕ) (h : n ≠ 0) :
    toOrdinal b n =
      ω ^ toOrdinal b (Nat.log b n) * (n / b ^ Nat.log b n : ℕ)
        + toOrdinal b (n % b ^ Nat.log b n) := by
  rw [toOrdinal]; simp [h]

/-- Unfolding `bump` at a nonzero argument (peel the top power). -/
lemma bump_pos (b n : ℕ) (h : n ≠ 0) :
    bump b n =
      n / b ^ Nat.log b n * (b + 1) ^ bump b (Nat.log b n) + bump b (n % b ^ Nat.log b n) := by
  rw [bump]; simp [h]

/-- **Crux (ordinal side).** For `b ≥ 2`, the map `n ↦ toOrdinal b n` is strictly
monotone, and each value is bounded by `ω^(toOrdinal b (log b n) + 1)`. Both halves
are proved together by strong induction, because each needs the other on smaller
arguments. -/
theorem toOrdinal_mono_and_bound (b : ℕ) (hb : 2 ≤ b) (n : ℕ) :
    (∀ m, m < n → toOrdinal b m < toOrdinal b n) ∧
      (n ≠ 0 → toOrdinal b n < ω ^ (toOrdinal b (Nat.log b n) + 1)) := by
  have hb1 : 1 < b := by omega
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    -- Remainder bound: `r < b^e'`, `e' < n`, `r < n` ⇒ `toOrdinal b r < ω^(toOrdinal b e')`.
    have rb : ∀ r e', e' < n → r < b ^ e' → r < n →
        toOrdinal b r < ω ^ toOrdinal b e' := by
      intro r e' he'n hre' hrn
      rcases eq_or_ne r 0 with rfl | hr0
      · simpa using opow_pos (toOrdinal b e') omega0_pos
      · have hlogr : Nat.log b r < e' := (Nat.log_lt_iff_lt_pow hb1 hr0).2 hre'
        have h1 : toOrdinal b (Nat.log b r) < toOrdinal b e' := (ih e' he'n).1 _ hlogr
        have h2 : toOrdinal b r < ω ^ (toOrdinal b (Nat.log b r) + 1) := (ih r hrn).2 hr0
        refine h2.trans_le (opow_le_opow_right omega0_pos ?_)
        rw [← Order.succ_eq_add_one]; exact Order.succ_le_of_lt h1
    constructor
    · ----- Part A: strict monotonicity into `n`
      intro m hmn
      have hn0 : n ≠ 0 := by omega
      have hbe_pos : 0 < b ^ Nat.log b n := Nat.pow_pos (by omega)
      have hbe_le : b ^ Nat.log b n ≤ n := Nat.pow_log_le_self b hn0
      have hc_pos : 0 < n / b ^ Nat.log b n := Nat.div_pos hbe_le hbe_pos
      have hr_lt : n % b ^ Nat.log b n < b ^ Nat.log b n := Nat.mod_lt _ hbe_pos
      have hr_lt_n : n % b ^ Nat.log b n < n := lt_of_lt_of_le hr_lt hbe_le
      have he_lt_n : Nat.log b n < n := Nat.log_lt_self b hn0
      have hn_eq := toOrdinal_pos b n hn0
      have hrb : toOrdinal b (n % b ^ Nat.log b n) < ω ^ toOrdinal b (Nat.log b n) :=
        rb _ _ he_lt_n hr_lt hr_lt_n
      have hpos : (0 : Ordinal) < ω ^ toOrdinal b (Nat.log b n) * (n / b ^ Nat.log b n : ℕ) := by
        apply mul_pos (opow_pos _ omega0_pos)
        exact_mod_cast hc_pos
      rcases eq_or_ne m 0 with rfl | hm0
      · rw [toOrdinal_zero, hn_eq]
        exact lt_of_lt_of_le hpos (le_self_add)
      · -- `m ≥ 1`; compare leading exponents
        have hem_le : Nat.log b m ≤ Nat.log b n := Nat.log_mono_right hmn.le
        rcases lt_or_eq_of_le hem_le with hem_lt | hem_eq
        · -- `log b m < log b n`: `m`'s whole ordinal sits below `ω^(toOrdinal b (log b n))`
          have hmb : toOrdinal b m < ω ^ (toOrdinal b (Nat.log b m) + 1) := (ih m hmn).2 hm0
          have hexp : toOrdinal b (Nat.log b m) + 1 ≤ toOrdinal b (Nat.log b n) := by
            rw [← Order.succ_eq_add_one]
            exact Order.succ_le_of_lt ((ih _ he_lt_n).1 _ hem_lt)
          calc toOrdinal b m
              < ω ^ (toOrdinal b (Nat.log b m) + 1) := hmb
            _ ≤ ω ^ toOrdinal b (Nat.log b n) := opow_le_opow_right omega0_pos hexp
            _ = ω ^ toOrdinal b (Nat.log b n) * 1 := (mul_one _).symm
            _ ≤ ω ^ toOrdinal b (Nat.log b n) * (n / b ^ Nat.log b n : ℕ) :=
                  mul_le_mul_right (by exact_mod_cast hc_pos) _
            _ ≤ toOrdinal b n := by rw [hn_eq]; exact le_self_add
        · -- equal leading exponents: compare the leading digit, then the remainder
          have hbem_pos : 0 < b ^ Nat.log b m := Nat.pow_pos (by omega)
          have hbem_le : b ^ Nat.log b m ≤ m := Nat.pow_log_le_self b hm0
          have hrm_lt : m % b ^ Nat.log b m < b ^ Nat.log b m := Nat.mod_lt _ hbem_pos
          have hm_eq := toOrdinal_pos b m hm0
          -- rewrite `log b m` to `log b n` everywhere
          rw [hm_eq, hn_eq, hem_eq]
          have hcm_le : m / b ^ Nat.log b n ≤ n / b ^ Nat.log b n := by
            rw [← hem_eq]; exact Nat.div_le_div_right hmn.le
          have hrm_lt' : m % b ^ Nat.log b n < b ^ Nat.log b n := by
            rw [← hem_eq]; exact hrm_lt
          have hrm_lt_n : m % b ^ Nat.log b n < n :=
            lt_of_lt_of_le hrm_lt' hbe_le
          have hrbm : toOrdinal b (m % b ^ Nat.log b n) < ω ^ toOrdinal b (Nat.log b n) :=
            rb _ _ he_lt_n hrm_lt' hrm_lt_n
          rcases lt_or_eq_of_le hcm_le with hcm_lt | hcm_eq
          · -- leading digit strictly smaller
            calc ω ^ toOrdinal b (Nat.log b n) * (m / b ^ Nat.log b n : ℕ)
                  + toOrdinal b (m % b ^ Nat.log b n)
                < ω ^ toOrdinal b (Nat.log b n) * (m / b ^ Nat.log b n : ℕ)
                  + ω ^ toOrdinal b (Nat.log b n) := (add_lt_add_iff_left _).2 hrbm
              _ = ω ^ toOrdinal b (Nat.log b n) * ((m / b ^ Nat.log b n : ℕ) + 1) := by
                    rw [mul_add_one]
              _ ≤ ω ^ toOrdinal b (Nat.log b n) * (n / b ^ Nat.log b n : ℕ) :=
                    mul_le_mul_right (by exact_mod_cast hcm_lt) _
              _ ≤ ω ^ toOrdinal b (Nat.log b n) * (n / b ^ Nat.log b n : ℕ)
                  + toOrdinal b (n % b ^ Nat.log b n) := le_self_add
          · -- equal leading digit: remainder strictly smaller
            have hrm_rn : m % b ^ Nat.log b n < n % b ^ Nat.log b n := by
              have em := Nat.div_add_mod m (b ^ Nat.log b n)
              have en := Nat.div_add_mod n (b ^ Nat.log b n)
              rw [← hcm_eq] at en
              omega
            rw [hcm_eq]
            have hlt : toOrdinal b (m % b ^ Nat.log b n) < toOrdinal b (n % b ^ Nat.log b n) :=
              (ih _ hr_lt_n).1 _ hrm_rn
            exact (add_lt_add_iff_left _).2 hlt
    · ----- Part B': leading bound
      intro hn0
      have hbe_pos : 0 < b ^ Nat.log b n := Nat.pow_pos (by omega)
      have hbe_le : b ^ Nat.log b n ≤ n := Nat.pow_log_le_self b hn0
      have hc_lt : n / b ^ Nat.log b n < b := by
        rw [Nat.div_lt_iff_lt_mul hbe_pos, ← pow_succ']
        exact Nat.lt_pow_succ_log_self hb1 n
      have hr_lt : n % b ^ Nat.log b n < b ^ Nat.log b n := Nat.mod_lt _ hbe_pos
      have hr_lt_n : n % b ^ Nat.log b n < n := lt_of_lt_of_le hr_lt hbe_le
      have he_lt_n : Nat.log b n < n := Nat.log_lt_self b hn0
      have hrb : toOrdinal b (n % b ^ Nat.log b n) < ω ^ toOrdinal b (Nat.log b n) :=
        rb _ _ he_lt_n hr_lt hr_lt_n
      rw [toOrdinal_pos b n hn0]
      calc ω ^ toOrdinal b (Nat.log b n) * (n / b ^ Nat.log b n : ℕ)
            + toOrdinal b (n % b ^ Nat.log b n)
          < ω ^ toOrdinal b (Nat.log b n) * (n / b ^ Nat.log b n : ℕ)
            + ω ^ toOrdinal b (Nat.log b n) := (add_lt_add_iff_left _).2 hrb
        _ = ω ^ toOrdinal b (Nat.log b n) * ((n / b ^ Nat.log b n : ℕ) + 1) := by rw [mul_add_one]
        _ ≤ ω ^ toOrdinal b (Nat.log b n) * ω :=
              mul_le_mul_right (by rw [← Nat.cast_add_one]; exact (natCast_lt_omega0 _).le) _
        _ = ω ^ (toOrdinal b (Nat.log b n) + 1) := by rw [← opow_succ, Order.succ_eq_add_one]

/-- **Crux (ℕ side).** The exact analog of `toOrdinal_mono_and_bound` for `bump`:
`bump b` is strictly monotone with leading bound `(b+1)^(bump b (log b n) + 1)`.
Same proof, with `(b+1)` in place of `ω`. Used to read off the base-`(b+1)`
digit structure of `bump b n` in the invariance lemma. -/
theorem bump_mono_and_bound (b : ℕ) (hb : 2 ≤ b) (n : ℕ) :
    (∀ m, m < n → bump b m < bump b n) ∧
      (n ≠ 0 → bump b n < (b + 1) ^ (bump b (Nat.log b n) + 1)) := by
  have hb1 : 1 < b := by omega
  have hb1' : 1 ≤ b + 1 := by omega
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have rb : ∀ r e', e' < n → r < b ^ e' → r < n →
        bump b r < (b + 1) ^ bump b e' := by
      intro r e' he'n hre' hrn
      rcases eq_or_ne r 0 with rfl | hr0
      · simp
      · have hlogr : Nat.log b r < e' := (Nat.log_lt_iff_lt_pow hb1 hr0).2 hre'
        have h1 : bump b (Nat.log b r) < bump b e' := (ih e' he'n).1 _ hlogr
        have h2 : bump b r < (b + 1) ^ (bump b (Nat.log b r) + 1) := (ih r hrn).2 hr0
        exact h2.trans_le (Nat.pow_le_pow_right hb1' h1)
    constructor
    · intro m hmn
      have hn0 : n ≠ 0 := by omega
      have hbe_pos : 0 < b ^ Nat.log b n := Nat.pow_pos (by omega)
      have hbe_le : b ^ Nat.log b n ≤ n := Nat.pow_log_le_self b hn0
      have hc_pos : 0 < n / b ^ Nat.log b n := Nat.div_pos hbe_le hbe_pos
      have hr_lt : n % b ^ Nat.log b n < b ^ Nat.log b n := Nat.mod_lt _ hbe_pos
      have hr_lt_n : n % b ^ Nat.log b n < n := lt_of_lt_of_le hr_lt hbe_le
      have he_lt_n : Nat.log b n < n := Nat.log_lt_self b hn0
      have hn_eq := bump_pos b n hn0
      have hrb : bump b (n % b ^ Nat.log b n) < (b + 1) ^ bump b (Nat.log b n) :=
        rb _ _ he_lt_n hr_lt hr_lt_n
      have hpe : 0 < (b + 1) ^ bump b (Nat.log b n) := Nat.pow_pos (by omega)
      rcases eq_or_ne m 0 with rfl | hm0
      · rw [bump_zero, hn_eq]
        have : 0 < n / b ^ Nat.log b n * (b + 1) ^ bump b (Nat.log b n) :=
          Nat.mul_pos hc_pos hpe
        omega
      · have hem_le : Nat.log b m ≤ Nat.log b n := Nat.log_mono_right hmn.le
        rcases lt_or_eq_of_le hem_le with hem_lt | hem_eq
        · have hmb : bump b m < (b + 1) ^ (bump b (Nat.log b m) + 1) := (ih m hmn).2 hm0
          have hexp : bump b (Nat.log b m) + 1 ≤ bump b (Nat.log b n) :=
            (ih _ he_lt_n).1 _ hem_lt
          calc bump b m
              < (b + 1) ^ (bump b (Nat.log b m) + 1) := hmb
            _ ≤ (b + 1) ^ bump b (Nat.log b n) := Nat.pow_le_pow_right hb1' hexp
            _ ≤ n / b ^ Nat.log b n * (b + 1) ^ bump b (Nat.log b n) :=
                  Nat.le_mul_of_pos_left _ hc_pos
            _ ≤ bump b n := by rw [hn_eq]; exact Nat.le_add_right _ _
        · have hbem_pos : 0 < b ^ Nat.log b m := Nat.pow_pos (by omega)
          have hrm_lt : m % b ^ Nat.log b m < b ^ Nat.log b m := Nat.mod_lt _ hbem_pos
          have hm_eq := bump_pos b m hm0
          rw [hm_eq, hn_eq, hem_eq]
          have hcm_le : m / b ^ Nat.log b n ≤ n / b ^ Nat.log b n := by
            rw [← hem_eq]; exact Nat.div_le_div_right hmn.le
          have hrm_lt' : m % b ^ Nat.log b n < b ^ Nat.log b n := by
            rw [← hem_eq]; exact hrm_lt
          have hrm_lt_n : m % b ^ Nat.log b n < n := lt_of_lt_of_le hrm_lt' hbe_le
          have hrbm : bump b (m % b ^ Nat.log b n) < (b + 1) ^ bump b (Nat.log b n) :=
            rb _ _ he_lt_n hrm_lt' hrm_lt_n
          rcases lt_or_eq_of_le hcm_le with hcm_lt | hcm_eq
          · calc m / b ^ Nat.log b n * (b + 1) ^ bump b (Nat.log b n)
                  + bump b (m % b ^ Nat.log b n)
                < m / b ^ Nat.log b n * (b + 1) ^ bump b (Nat.log b n)
                  + (b + 1) ^ bump b (Nat.log b n) := Nat.add_lt_add_left hrbm _
              _ = (m / b ^ Nat.log b n + 1) * (b + 1) ^ bump b (Nat.log b n) := by ring
              _ ≤ n / b ^ Nat.log b n * (b + 1) ^ bump b (Nat.log b n) :=
                    Nat.mul_le_mul_right _ hcm_lt
              _ ≤ n / b ^ Nat.log b n * (b + 1) ^ bump b (Nat.log b n)
                  + bump b (n % b ^ Nat.log b n) := Nat.le_add_right _ _
          · rw [hcm_eq]
            have hrm_rn : m % b ^ Nat.log b n < n % b ^ Nat.log b n := by
              have em := Nat.div_add_mod m (b ^ Nat.log b n)
              have en := Nat.div_add_mod n (b ^ Nat.log b n)
              rw [← hcm_eq] at en
              omega
            have hlt : bump b (m % b ^ Nat.log b n) < bump b (n % b ^ Nat.log b n) :=
              (ih _ hr_lt_n).1 _ hrm_rn
            exact Nat.add_lt_add_left hlt _
    · intro hn0
      have hbe_pos : 0 < b ^ Nat.log b n := Nat.pow_pos (by omega)
      have hbe_le : b ^ Nat.log b n ≤ n := Nat.pow_log_le_self b hn0
      have hc_lt : n / b ^ Nat.log b n < b := by
        rw [Nat.div_lt_iff_lt_mul hbe_pos, ← pow_succ']
        exact Nat.lt_pow_succ_log_self hb1 n
      have hr_lt : n % b ^ Nat.log b n < b ^ Nat.log b n := Nat.mod_lt _ hbe_pos
      have hr_lt_n : n % b ^ Nat.log b n < n := lt_of_lt_of_le hr_lt hbe_le
      have he_lt_n : Nat.log b n < n := Nat.log_lt_self b hn0
      have hrb : bump b (n % b ^ Nat.log b n) < (b + 1) ^ bump b (Nat.log b n) :=
        rb _ _ he_lt_n hr_lt hr_lt_n
      rw [bump_pos b n hn0]
      calc n / b ^ Nat.log b n * (b + 1) ^ bump b (Nat.log b n)
            + bump b (n % b ^ Nat.log b n)
          < n / b ^ Nat.log b n * (b + 1) ^ bump b (Nat.log b n)
            + (b + 1) ^ bump b (Nat.log b n) := Nat.add_lt_add_left hrb _
        _ = (n / b ^ Nat.log b n + 1) * (b + 1) ^ bump b (Nat.log b n) := by ring
        _ ≤ (b + 1) * (b + 1) ^ bump b (Nat.log b n) :=
              Nat.mul_le_mul_right _ (by omega)
        _ = (b + 1) ^ (bump b (Nat.log b n) + 1) := by rw [pow_succ]; ring

/-- Remainder bound for `bump`: if `r < b^e` then `bump b r < (b+1)^(bump b e)`.
The base-`(b+1)` analog of the leading bound. -/
lemma bump_lt_pow (b : ℕ) (hb : 2 ≤ b) {r e : ℕ} (h : r < b ^ e) :
    bump b r < (b + 1) ^ bump b e := by
  rcases eq_or_ne r 0 with rfl | hr0
  · simp
  · have hb1 : 1 < b := by omega
    have hlogr : Nat.log b r < e := (Nat.log_lt_iff_lt_pow hb1 hr0).2 h
    have hmono := (bump_mono_and_bound b hb e).1 (Nat.log b r) hlogr
    have hbound := (bump_mono_and_bound b hb r).2 hr0
    exact hbound.trans_le (Nat.pow_le_pow_right (by omega) hmono)

/-- **Bump invariance.** For `b ≥ 2`, bumping the base does not change the ordinal:
`toOrdinal (b+1) (bump b n) = toOrdinal b n`. Both read the base as `ω`; the
proof reads off the base-`(b+1)` digit structure of `bump b n` (leading exponent
`bump b (log b n)`, leading digit `n / b^(log b n)`, remainder `bump b (n % …)`)
and recurses. -/
lemma toOrdinal_bump (b : ℕ) (hb : 2 ≤ b) (n : ℕ) :
    toOrdinal (b + 1) (bump b n) = toOrdinal b n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases eq_or_ne n 0 with rfl | hn0
    · simp
    · have hb1 : 1 < b := by omega
      set e := Nat.log b n with he
      have hbe_pos : 0 < b ^ e := Nat.pow_pos (by omega)
      have hbe_le : b ^ e ≤ n := Nat.pow_log_le_self b hn0
      have hc_pos : 0 < n / b ^ e := Nat.div_pos hbe_le hbe_pos
      have hc_lt : n / b ^ e < b := by
        rw [Nat.div_lt_iff_lt_mul hbe_pos, ← pow_succ']; exact Nat.lt_pow_succ_log_self hb1 n
      have hr_lt : n % b ^ e < b ^ e := Nat.mod_lt _ hbe_pos
      have he_lt_n : e < n := Nat.log_lt_self b hn0
      have hr_lt_n : n % b ^ e < n := lt_of_lt_of_le hr_lt hbe_le
      have hBE_pos : 0 < (b + 1) ^ bump b e := Nat.pow_pos (by omega)
      have hR_lt : bump b (n % b ^ e) < (b + 1) ^ bump b e := bump_lt_pow b hb hr_lt
      have hbump_eq : bump b n
          = n / b ^ e * (b + 1) ^ bump b e + bump b (n % b ^ e) := bump_pos b n hn0
      have hbn_pos : 0 < bump b n := by
        rw [hbump_eq]
        have : 0 < n / b ^ e * (b + 1) ^ bump b e := Nat.mul_pos hc_pos hBE_pos
        omega
      have hlog : Nat.log (b + 1) (bump b n) = bump b e := by
        rw [hbump_eq]
        apply Nat.log_eq_of_pow_le_of_lt_pow
        · calc (b + 1) ^ bump b e
              = 1 * (b + 1) ^ bump b e := (one_mul _).symm
            _ ≤ n / b ^ e * (b + 1) ^ bump b e := Nat.mul_le_mul_right _ hc_pos
            _ ≤ n / b ^ e * (b + 1) ^ bump b e + bump b (n % b ^ e) := Nat.le_add_right _ _
        · calc n / b ^ e * (b + 1) ^ bump b e + bump b (n % b ^ e)
              < n / b ^ e * (b + 1) ^ bump b e + (b + 1) ^ bump b e := by omega
            _ = (n / b ^ e + 1) * (b + 1) ^ bump b e := by ring
            _ ≤ (b + 1) * (b + 1) ^ bump b e := Nat.mul_le_mul_right _ (by omega)
            _ = (b + 1) ^ (bump b e + 1) := by rw [pow_succ]; ring
      have hdiv : bump b n / (b + 1) ^ bump b e = n / b ^ e := by
        rw [hbump_eq, mul_comm (n / b ^ e), Nat.mul_add_div hBE_pos,
          Nat.div_eq_of_lt hR_lt, Nat.add_zero]
      have hmod : bump b n % (b + 1) ^ bump b e = bump b (n % b ^ e) := by
        rw [hbump_eq, mul_comm (n / b ^ e), Nat.mul_add_mod, Nat.mod_eq_of_lt hR_lt]
      have key : toOrdinal (b + 1) (bump b n)
          = ω ^ toOrdinal (b + 1) (bump b e) * (n / b ^ e : ℕ)
            + toOrdinal (b + 1) (bump b (n % b ^ e)) := by
        conv_lhs => rw [toOrdinal_pos (b + 1) (bump b n) (by omega)]
        rw [hlog, hdiv, hmod]
      rw [key, ih e he_lt_n, ih (n % b ^ e) hr_lt_n]
      exact (toOrdinal_pos b n hn0).symm

/-- Ordinal value assigned to the `k`-th Goodstein term, read in its base `k+2`. -/
noncomputable def seqOrd (m k : ℕ) : Ordinal.{0} := toOrdinal (k + 2) (goodsteinSeq m k)

/-- **Descent.** While the term is nonzero, one Goodstein step strictly lowers the
ordinal value: the base-bump preserves it (invariance) and the subtract-one
strictly drops it (monotonicity). -/
lemma seqOrd_step (m k : ℕ) (h : goodsteinSeq m k ≠ 0) : seqOrd m (k + 1) < seqOrd m k := by
  have hb : 2 ≤ k + 2 := by omega
  have hstep : goodsteinSeq m (k + 1) = bump (k + 2) (goodsteinSeq m k) - 1 := rfl
  have hMpos : 0 < bump (k + 2) (goodsteinSeq m k) := by
    rw [bump_pos (k + 2) _ h]
    have h1 : 0 < goodsteinSeq m k / (k + 2) ^ Nat.log (k + 2) (goodsteinSeq m k) :=
      Nat.div_pos (Nat.pow_log_le_self _ h) (Nat.pow_pos (by omega))
    have h2 : 0 < (k + 2 + 1) ^ bump (k + 2) (Nat.log (k + 2) (goodsteinSeq m k)) :=
      Nat.pow_pos (by omega)
    have := Nat.mul_pos h1 h2
    omega
  have hmono := (toOrdinal_mono_and_bound (k + 2 + 1) (by omega) (bump (k + 2) (goodsteinSeq m k))).1
                  (bump (k + 2) (goodsteinSeq m k) - 1) (by omega)
  have hinv := toOrdinal_bump (k + 2) hb (goodsteinSeq m k)
  unfold seqOrd
  rw [hstep, show k + 1 + 2 = k + 2 + 1 from by ring]
  exact hmono.trans_le (le_of_eq hinv)

/-- Every Goodstein sequence reaches `0` (engine form). If it never did, `seqOrd`
would be an infinite strictly-decreasing sequence of ordinals, contradicting
well-foundedness of `<` on `Ordinal`. -/
theorem goodstein_terminates_engine (m : ℕ) : ∃ N, goodsteinSeq m N = 0 := by
  by_contra hcon
  rw [not_exists] at hcon
  have hdec : ∀ k, seqOrd m (k + 1) < seqOrd m k := fun k => seqOrd_step m k (hcon k)
  obtain ⟨a, ⟨N, hNa⟩, hmin⟩ :=
    Ordinal.lt_wf.has_min (Set.range (seqOrd m)) ⟨seqOrd m 0, 0, rfl⟩
  exact hmin (seqOrd m (N + 1)) ⟨N + 1, rfl⟩ (hNa ▸ hdec N)


-- ════════════════ ported: Statement.lean ════════════════
/-
# Goodstein's theorem: every Goodstein sequence terminates — Goodstein (1944)

**Designated audit surface** (with `Defs.lean` and `Anchors.lean`). The proof
engine lives in sibling files; this statement delegates.

## What this says
For every starting value `m`, the Goodstein sequence seeded at `m` (see `Defs.lean`)
eventually reaches `0`. Despite the early astronomical growth (the `m = 4` sequence
peaks around `3·2^402653211` before descending), it always terminates.

## Proof (positive theorem, provable here)
Map each term `G k`, written in hereditary base `k+2`, to an ordinal by replacing
the base `k+2` with `ω`. The base-bump `k+2 ↦ k+3` leaves this ordinal unchanged
(it is `ω` regardless of base); the subtract-one strictly decreases it. So the
ordinal sequence is strictly decreasing, and `Ordinal` is well-founded
(`Ordinal.wellFoundedLT`) — no infinite descent — so it must reach `0`, forcing
`G k = 0`. mathlib supplies the Cantor-normal-form machinery
(`Ordinal.CNF`, `Ordinal.coeff`/`Ordinal.eval`) and well-foundedness.

## Scope — POSITIVE theorem only
This is Goodstein's theorem proper (true; provable in ZFC, hence trivially in
Lean's stronger logic). The **Kirby–Paris independence result** — that Peano
Arithmetic cannot prove this theorem (Kirby & Paris 1982, via `Goodstein ⟹ Con(PA)`
+ Gödel II) — is a *metamathematical* statement about PA and is explicitly OUT OF
SCOPE. See `README.md`.
-/


/-- **Goodstein's theorem.** For every starting value `m`, the Goodstein sequence
seeded at `m` eventually reaches `0`. (The ordinal-descent proof lives in
`Engine.lean`; this is the thin, faithful audit statement.) -/
theorem goodstein_terminates (m : ℕ) : ∃ N, goodsteinSeq m N = 0 :=
  goodstein_terminates_engine m


-- ════════════════ ported: Length.lean ════════════════
/-
# The Goodstein length function

The **Goodstein length** `goodsteinLength m` is the step at which the Goodstein
sequence seeded at `m` first reaches `0`. It is well-defined by `goodstein_terminates`
(every Goodstein sequence terminates — proved axiom-clean in `Engine.lean`).

This function is the bridge to the *independence* story. Its growth rate is
astronomically fast — it tracks the Hardy function `H_{ε₀}` (equivalently the
fast-growing `f_{ε₀}` of `Mathlib.SetTheory.Ordinal.Notation`, `ONote.fastGrowingε₀`).
Because every PA-provably-total function is dominated by some `f_α` with `α < ε₀`,
and `goodsteinLength` eventually outgrows every such `f_α`, PA cannot prove that
`goodsteinLength` is total — which is the Kirby–Paris independence result. The
*growth content* of that argument (the part that lives entirely in mathlib, no
first-order-logic machinery) is what the `Logic/FastGrowing/` files develop, and
`Logic/Goodstein/Growth.lean` (to be built) connects this function to it.

The PA-syntactic wrapper (`PA ⊬ γ`) is a separate expedition; see the repo
`~/src/goodstein-independence`. This file builds only the object-level function and
its basic API.
-/


/-- The **Goodstein length** of `m`: the least step `N` at which the Goodstein
sequence seeded at `m` reaches `0`. Total by `goodstein_terminates`. -/
def goodsteinLength (m : ℕ) : ℕ := Nat.find (goodstein_terminates m)

/-- Defining property: the sequence is `0` at its length. -/
theorem goodsteinSeq_goodsteinLength (m : ℕ) :
    goodsteinSeq m (goodsteinLength m) = 0 :=
  Nat.find_spec (goodstein_terminates m)

/-- The length is the *least* zero: any zero step is `≥ goodsteinLength m`. -/
theorem goodsteinLength_le {m N : ℕ} (h : goodsteinSeq m N = 0) :
    goodsteinLength m ≤ N :=
  Nat.find_le h

/-- Before the length, the sequence is nonzero. -/
theorem goodsteinSeq_ne_zero_of_lt {m N : ℕ} (h : N < goodsteinLength m) :
    goodsteinSeq m N ≠ 0 :=
  Nat.find_min (goodstein_terminates m) h

/-! ## Anchors (anti-vacuity)

Small computed values, off any headline axiom path. A wrong definition of
`goodsteinSeq` could not satisfy these. -/

example : goodsteinLength 0 = 0 := by native_decide
example : goodsteinLength 2 = 3 := by native_decide
example : goodsteinLength 3 = 5 := by native_decide


-- ════════════════ ported: Growth.lean ════════════════
/-
# C2 — the semantic bridge `Engine.toOrdinal` ↔ `ONote.repr`

The Goodstein termination proof (`Logic/Goodstein/Engine.lean`) maps each Goodstein term to
an ordinal `< ε₀` via `toOrdinal b n` — read `n` in hereditary base `b`, replace `b` by `ω`.
That ordinal is exactly the `ONote.repr` of the Cantor-normal-form notation of `n` in base
`b`. This file builds that notation, `toONote b n`, and proves the bridge

  `repr (toONote b n) = toOrdinal b n`  (`repr_toONote`)   and   `(toONote b n).NF`.

With the bridge, the engine's ε₀-descent (`Engine.seqOrd_step`) is expressed on the
*computable* ordinal notations `ONote`, the home of the fast-growing growth theory
(`Logic/FastGrowing/*`). This is the prerequisite (C2) for the growth theorem C3
(`goodsteinLength` tracks `fastGrowingε₀`).
-/



/-- The ordinal **notation** whose `repr` is `Engine.toOrdinal b n`: the Cantor normal form
of `n` written in base `b` with the base read as `ω`. Mirrors `toOrdinal`'s recursion
(peel the top power `b^(log b n)`), keeping everything computable. -/
def toONote (b : ℕ) (n : ℕ) : ONote :=
  if h : n = 0 then 0
  else
    have _hn : n ≠ 0 := h
    oadd (toONote b (Nat.log b n)) (n / b ^ Nat.log b n).toPNat'
        (toONote b (n % b ^ Nat.log b n))
termination_by n
decreasing_by
  · exact Nat.log_lt_self b h
  · have hb : 0 < b ^ Nat.log b n := by
      rcases Nat.eq_zero_or_pos b with hb0 | hbpos
      · subst hb0; simp [Nat.log_zero_left]
      · exact Nat.pow_pos hbpos
    exact lt_of_lt_of_le (Nat.mod_lt _ hb) (Nat.pow_log_le_self b h)

@[simp] theorem toONote_zero (b : ℕ) : toONote b 0 = 0 := by rw [toONote]; simp

/-- **The bridge (repr side).** `repr (toONote b n) = toOrdinal b n`: the notation really does
represent the engine's ordinal. Structural induction mirroring `toOrdinal_pos`. -/
theorem repr_toONote (b : ℕ) (hb : 2 ≤ b) : ∀ n, (toONote b n).repr = toOrdinal b n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · have hlog : Nat.log b n < n := Nat.log_lt_self b hn
      have hbe_pos : 0 < b ^ Nat.log b n := Nat.pow_pos (by omega)
      have hbe_le : b ^ Nat.log b n ≤ n := Nat.pow_log_le_self b hn
      have hr_lt_n : n % b ^ Nat.log b n < n := lt_of_lt_of_le (Nat.mod_lt _ hbe_pos) hbe_le
      have hc_pos : 0 < n / b ^ Nat.log b n := Nat.div_pos hbe_le hbe_pos
      rw [toONote, dif_neg hn, toOrdinal_pos b n hn, ONote.repr, ih _ hlog, ih _ hr_lt_n]
      congr 2
      exact_mod_cast PNat.toPNat'_coe hc_pos

/-- **The bridge (normal-form side).** `toONote b n` is a genuine normal-form notation. The
only nontrivial obligation is the leading-exponent ordering of each `oadd`, i.e. the tail's
ordinal sits below `ω^(leading exponent)` — exactly the remainder bound inside
`Engine.toOrdinal_mono_and_bound` (`toOrdinal b r < ω^(toOrdinal b e')` when `r < b^e'`),
reconstructed here from the public monotonicity + bound. -/
theorem toONote_NF (b : ℕ) (hb : 2 ≤ b) : ∀ n, (toONote b n).NF := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases eq_or_ne n 0 with rfl | hn
    · rw [toONote_zero]; exact NF.zero
    · have hb1 : 1 < b := by omega
      have hlog : Nat.log b n < n := Nat.log_lt_self b hn
      have hbe_pos : 0 < b ^ Nat.log b n := Nat.pow_pos (by omega)
      have hbe_le : b ^ Nat.log b n ≤ n := Nat.pow_log_le_self b hn
      have hr_lt : n % b ^ Nat.log b n < b ^ Nat.log b n := Nat.mod_lt _ hbe_pos
      have hr_lt_n : n % b ^ Nat.log b n < n := lt_of_lt_of_le hr_lt hbe_le
      have hbound : toOrdinal b (n % b ^ Nat.log b n) < ω ^ toOrdinal b (Nat.log b n) := by
        rcases eq_or_ne (n % b ^ Nat.log b n) 0 with hr0 | hr0
        · rw [hr0, toOrdinal_zero]; exact opow_pos _ omega0_pos
        · have hlogr : Nat.log b (n % b ^ Nat.log b n) < Nat.log b n :=
            (Nat.log_lt_iff_lt_pow hb1 hr0).2 hr_lt
          have hmono : toOrdinal b (Nat.log b (n % b ^ Nat.log b n)) < toOrdinal b (Nat.log b n) :=
            (toOrdinal_mono_and_bound b hb (Nat.log b n)).1 _ hlogr
          refine ((toOrdinal_mono_and_bound b hb (n % b ^ Nat.log b n)).2 hr0).trans_le
            (opow_le_opow_right omega0_pos ?_)
          rw [← Order.succ_eq_add_one]; exact Order.succ_le_of_lt hmono
      rw [toONote, dif_neg hn]
      refine NF.oadd (ih _ hlog) _ (NF.below_of_lt' ?_ (ih _ hr_lt_n))
      rw [repr_toONote b hb, repr_toONote b hb]; exact hbound

/-! ### The Goodstein descent, expressed on `ONote`

With the bridge in hand, the engine's ordinal value `Engine.seqOrd m k` becomes a computable
notation `seqONote m k`, and the strict ε₀-descent `Engine.seqOrd_step` becomes a strict
`ONote` `<`-descent. This is the C2 deliverable: the Goodstein termination descent now lives
on the same `ONote` where the fast-growing growth theory (`Logic/FastGrowing/*`, A4) does —
the bridge that C3 (the growth theorem) will cross. -/

/-- The `k`-th Goodstein term as an ordinal **notation** (read in its base `k+2`). -/
def seqONote (m k : ℕ) : ONote := toONote (k + 2) (goodsteinSeq m k)

theorem seqONote_NF (m k : ℕ) : (seqONote m k).NF := toONote_NF (k + 2) (by omega) _

/-- `repr (seqONote m k) = Engine.seqOrd m k`: the notation carries the engine's ordinal. -/
theorem repr_seqONote (m k : ℕ) : (seqONote m k).repr = seqOrd m k :=
  repr_toONote (k + 2) (by omega) _

/-- **The Goodstein descent on `ONote`.** While the term is nonzero, one Goodstein step
strictly lowers the notation: `seqONote m (k+1) < seqONote m k`. Transported from
`Engine.seqOrd_step` through the `repr` bridge. -/
theorem seqONote_lt (m k : ℕ) (h : goodsteinSeq m k ≠ 0) :
    seqONote m (k + 1) < seqONote m k := by
  rw [lt_def, repr_seqONote, repr_seqONote]
  exact seqOrd_step m k h

/-- `toONote b n = 0 ↔ n = 0`: the notation vanishes exactly when its argument does (a
nonzero argument produces an `oadd`, which is positive). -/
theorem toONote_eq_zero_iff (b n : ℕ) : toONote b n = 0 ↔ n = 0 := by
  refine ⟨fun h => ?_, fun h => by rw [h, toONote_zero]⟩
  by_contra hn
  rw [toONote, dif_neg hn] at h
  exact absurd h (oadd_pos _ _ _).ne'

/-- `seqONote m k = 0 ↔ goodsteinSeq m k = 0`: the notation hits `0` exactly at termination.
Hence the ONote descent `seqONote m 0 > seqONote m 1 > …` has length `goodsteinLength m` —
the connection `goodsteinLength` ↔ ε₀-descent that C3 will turn into a Hardy growth bound. -/
theorem seqONote_eq_zero_iff (m k : ℕ) : seqONote m k = 0 ↔ goodsteinSeq m k = 0 :=
  toONote_eq_zero_iff (k + 2) (goodsteinSeq m k)

/-- The ONote descent reaches `0` exactly at index `goodsteinLength m`. -/
theorem seqONote_goodsteinLength (m : ℕ) : seqONote m (goodsteinLength m) = 0 :=
  (seqONote_eq_zero_iff m (goodsteinLength m)).2 (goodsteinSeq_goodsteinLength m)

/-- Before `goodsteinLength m` the descent is strictly positive. So `goodsteinLength m` is
*precisely* the length of the strict `ONote` descent `seqONote m 0 > … > 0` — the quantity
C3 must identify with a Hardy value of `seqONote m 0`. -/
theorem seqONote_ne_zero_of_lt (m : ℕ) {k : ℕ} (h : k < goodsteinLength m) :
    seqONote m k ≠ 0 :=
  fun hz => goodsteinSeq_ne_zero_of_lt h ((seqONote_eq_zero_iff m k).1 hz)

/-! ## C3 — the growth theorem: `goodsteinLength m = H_{seqONote m 0}(2) − 2`

The crown jewel. The Hardy hierarchy "counts the steps" of a unit-decrement ordinal descent
where the *argument* (= the Goodstein base) grows by one at each step. The bridge is the
**Cichoń correspondence**: one Goodstein step is exactly one budget-incrementing Hardy step
(`hstep`) on the notation. Concretely, on `toONote` (base `b`, value `p ≠ 0`):

  `hstep (toONote b p) b = toONote (b+1) (bump b p − 1)`   (`hstep_toONote`)

i.e. "descend the fundamental-sequence tree of `p`'s notation once at argument `b`" equals
"bump the base `b ↦ b+1` and subtract one" — the operation the Goodstein step performs.
Combined with the intrinsic Hardy step invariant `hardy_hstep` (`H_o(n) = H_{hstep o n}(n+1)`,
proved in `FastGrowing/Hardy.lean`), the Hardy value `H_{seqONote m k}(k+2)` is **constant**
along the whole Goodstein descent, so telescoping from `k = 0` to `k = goodsteinLength m`
(where the notation is `0` and `H_0(N) = N`) yields `H_{seqONote m 0}(2) = goodsteinLength m + 2`.

This is the formal "Goodstein grows like the Hardy/fast-growing hierarchy" — the growth
content behind Kirby–Paris independence (the abstract domination `f_o < f_{ε₀}` is A4
in `FastGrowing/Domination.lean`; this file pins the Goodstein length itself to a Hardy value). -/

/-- **Notation invariance under `bump`.** The ordinal *notation* of `n` is unchanged by a
hereditary base bump: `toONote (b+1) (bump b n) = toONote b n`. Both are normal-form notations
with the same `repr` (the bump invariance `toOrdinal_bump` at the ordinal level), so they are
equal by `repr_inj`. This is the notation-level companion of `Engine.toOrdinal_bump`. -/
theorem toONote_bump (b : ℕ) (hb : 2 ≤ b) (n : ℕ) :
    toONote (b + 1) (bump b n) = toONote b n := by
  haveI := toONote_NF (b + 1) (by omega) (bump b n)
  haveI := toONote_NF b hb n
  rw [← repr_inj, repr_toONote (b + 1) (by omega), repr_toONote b hb, toOrdinal_bump b hb]

/-- **Constructor form of `toONote`.** When `1 ≤ c < b` and `s < b^e`, the base-`b` notation
of `c·b^e + s` is `oadd (toONote b e) c (toONote b s)` — `c·b^e + s` already presents the
leading Cantor term, so `log`, `div`, `mod` read off `e`, `c`, `s`. -/
theorem toONote_oadd (b : ℕ) (hb : 2 ≤ b) {c e s : ℕ} (hc : 1 ≤ c) (hcb : c < b)
    (hs : s < b ^ e) : toONote b (c * b ^ e + s) = oadd (toONote b e) ⟨c, hc⟩ (toONote b s) := by
  have hbe_pos : 0 < b ^ e := Nat.pow_pos (by omega)
  have hn0 : c * b ^ e + s ≠ 0 := by positivity
  have hlow : c * b ^ e + s < b ^ (e + 1) := by
    calc c * b ^ e + s < c * b ^ e + b ^ e := by omega
      _ = (c + 1) * b ^ e := by ring
      _ ≤ b * b ^ e := Nat.mul_le_mul_right _ (by omega)
      _ = b ^ (e + 1) := by rw [pow_succ]; ring
  have hge : b ^ e ≤ c * b ^ e + s :=
    (Nat.le_mul_of_pos_left (b ^ e) hc).trans (Nat.le_add_right _ _)
  have hlog : Nat.log b (c * b ^ e + s) = e := Nat.log_eq_of_pow_le_of_lt_pow hge hlow
  have hdiv : (c * b ^ e + s) / b ^ e = c := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hbe_pos, Nat.div_eq_of_lt hs, Nat.zero_add]
  have hmod : (c * b ^ e + s) % b ^ e = s := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hs]
  rw [toONote, dif_neg hn0, hlog, hdiv, hmod]
  congr 1
  exact PNat.coe_injective (by simpa using PNat.toPNat'_coe hc)

/-- Single-digit notation: for `1 ≤ d < b`, `toONote b d = oadd 0 ⟨d,_⟩ 0` (the finite
ordinal `d`). Special case of `toONote_oadd` with exponent and remainder zero. -/
theorem toONote_single (b : ℕ) (hb : 2 ≤ b) {d : ℕ} (hd1 : 1 ≤ d) (hdb : d < b) :
    toONote b d = oadd 0 ⟨d, hd1⟩ 0 := by
  simpa using toONote_oadd b hb hd1 hdb (show (0 : ℕ) < b ^ 0 by simp)

/-- `fundamentalSequence` of `oadd 0 C 0` (a finite ordinal `C`): always a successor —
predecessor `0` when `C = 1`, else `oadd 0 (C-1) 0`. Read off the definition's nested match. -/
theorem fundamentalSequence_oadd_zero_zero (C : ℕ+) :
    fundamentalSequence (oadd 0 C 0) =
      match C.natPred with
      | 0 => Sum.inl (some 0)
      | j + 1 => Sum.inl (some (oadd 0 j.succPNat 0)) := by
  conv_lhs => rw [fundamentalSequence]
  simp only [show fundamentalSequence (0 : ONote) = Sum.inl none from rfl]
  rcases C.natPred with _ | j <;> rfl

/-- **The `r = 0`, `L = 0` (finite) base case of the Cichoń step.** For a single digit
`1 ≤ c < b`, one Hardy step on `oadd 0 c 0` (the finite ordinal `c`) is the finite notation
of `c − 1` in base `b+1`: `hstep (oadd 0 c 0) b = toONote (b+1) (c−1)`. `oadd 0 c 0` is a
successor, so the step is a single decrement. -/
theorem hstep_oadd_zero_zero (b : ℕ) (hb : 2 ≤ b) (c : ℕ) (hc1 : 1 ≤ c) (hcb : c < b) :
    hstep (oadd 0 ⟨c, hc1⟩ 0) b = toONote (b + 1) (c - 1) := by
  have hnp : PNat.natPred ⟨c, hc1⟩ = c - 1 := PNat.natPred_eq_pred hc1
  rcases eq_or_ne c 1 with rfl | hc2
  · rw [hstep_succ _ (by rw [fundamentalSequence_oadd_zero_zero, hnp]; rfl)]; simp
  · have hfs : fundamentalSequence (oadd 0 ⟨c, hc1⟩ 0)
        = Sum.inl (some (oadd 0 (c - 2).succPNat 0)) := by
      rw [fundamentalSequence_oadd_zero_zero, hnp, show c - 1 = (c - 2) + 1 from by omega]
    rw [hstep_succ _ hfs, toONote_single (b + 1) (by omega) (show 1 ≤ c - 1 by omega) (by omega)]
    show oadd 0 (c - 2).succPNat 0 = oadd 0 ⟨c - 1, by omega⟩ 0
    congr 1
    apply PNat.coe_injective
    change (c - 2) + 1 = c - 1
    omega

/-- Helper for the coefficient peel: for `E ≠ 0`, the fundamental sequence of `oadd E 1 0`
is some `inr g`, and that of `oadd E ⟨k+2⟩ 0` wraps it as `fun i => oadd E ⟨k+1⟩ (g i)`.
Read off the two non-`inl none` branches of `fundamentalSequence (oadd E · 0)` (tail `0`,
`natPred` `0` resp. `k+1`). -/
theorem fundSeq_oadd_coeff (E : ONote) (hE : E ≠ 0) (k : ℕ) :
    ∃ g, fundamentalSequence (oadd E 1 0) = Sum.inr g ∧
      fundamentalSequence (oadd E ⟨k + 2, by omega⟩ 0)
        = Sum.inr (fun i => oadd E k.succPNat (g i)) := by
  rcases e : fundamentalSequence E with (_ | E') | f
  · exact absurd ((fundamentalSequenceProp_inl_none E).1 (e ▸ fundamentalSequence_has_prop E)) hE
  · refine ⟨fun i => oadd E' i.succPNat 0, ?_, ?_⟩ <;>
      · rw [fundamentalSequence]
        simp only [show fundamentalSequence (0 : ONote) = Sum.inl none from rfl, e]
        rfl
  · refine ⟨fun i => oadd (f i) 1 0, ?_, ?_⟩ <;>
      · rw [fundamentalSequence]
        simp only [show fundamentalSequence (0 : ONote) = Sum.inl none from rfl, e]
        rfl

/-- **Lemma A (coefficient peel).** For `E ≠ 0` and `c ≥ 2`, one Hardy step on `oadd E c 0`
peels the coefficient to `c-1` and leaves a Hardy step on `oadd E 1 0`:
`hstep (oadd E ⟨c⟩ 0) b = oadd E ⟨c-1⟩ (hstep (oadd E 1 0) b)`. The descent through the
limit `oadd E ⟨c⟩ 0` lands on `oadd E ⟨c-1⟩ (g b)`, whose nonzero tail `g b` peels off
(`hstep_oadd_tail`) leaving exactly `hstep (oadd E 1 0) b = hstep (g b) b`. -/
theorem hstep_oadd_coeff (b : ℕ) {E : ONote} (hE : E ≠ 0) {c : ℕ} (hc : 2 ≤ c)
    (hc1 : 1 ≤ c) :
    hstep (oadd E ⟨c, hc1⟩ 0) b = oadd E ⟨c - 1, by omega⟩ (hstep (oadd E 1 0) b) := by
  obtain ⟨k, rfl⟩ : ∃ k, c = k + 2 := ⟨c - 2, by omega⟩
  obtain ⟨g, h1, hc2⟩ := fundSeq_oadd_coeff E hE k
  have hgb : g b ≠ 0 := fundamentalSequence_inr_ne_zero h1 b
  have hcoe : (⟨k + 2, hc1⟩ : ℕ+) = ⟨k + 2, by omega⟩ := rfl
  rw [hcoe, hstep_limit _ hc2, hstep_limit _ h1]
  dsimp only
  rw [hstep_oadd_tail E k.succPNat b (g b) hgb]
  congr 1

/-- `evalNat b o` evaluates the ordinal notation `o` at `ω ↦ b+1`: it reads `repr o`'s Cantor
normal form as a base-`(b+1)` numeral. This is the natural-number "size" the borrowing
predecessor (`hstep_oadd_one_zero`) targets: `hstep (oadd E 1 0) b` is the all-digits-`b`
notation of `(b+1)^(evalNat b E) − 1`. -/
def evalNat (b : ℕ) : ONote → ℕ
  | 0 => 0
  | oadd e n r => (n : ℕ) * (b + 1) ^ evalNat b e + evalNat b r

@[simp] theorem evalNat_zero (b : ℕ) : evalNat b 0 = 0 := rfl

theorem evalNat_oadd (b : ℕ) (e : ONote) (n : ℕ+) (r : ONote) :
    evalNat b (oadd e n r) = (n : ℕ) * (b + 1) ^ evalNat b e + evalNat b r := rfl

/-- **`evalNat` reconstructs `bump`.** Evaluating the base-`b` notation `toONote b L` at
`ω ↦ b+1` gives exactly the hereditary base-bump `bump b L`. Strong induction on `L`,
mirroring `bump`'s own recursion. Hence the borrowing answer for `E = toONote b L`,
`(b+1)^(evalNat b E) − 1`, is exactly `(b+1)^(bump b L) − 1`. -/
theorem evalNat_toONote (b : ℕ) (hb : 2 ≤ b) : ∀ L, evalNat b (toONote b L) = bump b L := by
  intro L
  induction L using Nat.strong_induction_on with
  | _ L ih =>
    rcases eq_or_ne L 0 with rfl | hL
    · simp
    · have hlog : Nat.log b L < L := Nat.log_lt_self b hL
      have hbe_pos : 0 < b ^ Nat.log b L := Nat.pow_pos (by omega)
      have hbe_le : b ^ Nat.log b L ≤ L := Nat.pow_log_le_self b hL
      have hr_lt : L % b ^ Nat.log b L < L :=
        lt_of_lt_of_le (Nat.mod_lt _ hbe_pos) hbe_le
      have hc_pos : 0 < L / b ^ Nat.log b L := Nat.div_pos hbe_le hbe_pos
      rw [toONote, dif_neg hL, evalNat_oadd, ih _ hlog, ih _ hr_lt, bump_pos b L hL]
      congr 2
      exact_mod_cast PNat.toPNat'_coe hc_pos

/-- **`evalNat` tracks a successor step.** If `fundamentalSequence E = some E'` (i.e. `E` is the
successor of `E'`), then `evalNat b E = evalNat b E' + 1`. Structural recursion on `E`, casing
the `fundamentalSequence` successor branches. -/
theorem evalNat_succ (b : ℕ) : ∀ {E E' : ONote}, fundamentalSequence E = Sum.inl (some E') →
    evalNat b E = evalNat b E' + 1 := by
  intro E
  induction E with
  | zero => intro E' h; exact absurd h (by simp [fundamentalSequence])
  | oadd a m r iha ihr =>
    intro E' h
    rw [fundamentalSequence] at h
    rcases hr : fundamentalSequence r with (_ | r') | g
    · -- r = 0: inner match on (fundamentalSequence a, m.natPred)
      rw [hr] at h
      rcases ha : fundamentalSequence a with (_ | a') | p
      · -- a = 0
        rw [ha] at h
        rcases hm : m.natPred with _ | k
        · -- m = 1, E' = 0
          rw [hm] at h
          obtain rfl : (0:ONote) = E' := by simpa using h
          have hrz : r = 0 := (fundamentalSequenceProp_inl_none r).1 (hr ▸ fundamentalSequence_has_prop r)
          have haz : a = 0 := (fundamentalSequenceProp_inl_none a).1 (ha ▸ fundamentalSequence_has_prop a)
          have hm1 : (m : ℕ) = 1 := by
            have := PNat.natPred_add_one m; omega
          subst hrz; subst haz
          simp [evalNat_oadd, hm1]
        · -- m = k+2, E' = oadd 0 (k.succPNat) 0
          rw [hm] at h
          obtain rfl : oadd 0 k.succPNat 0 = E' := by simpa using h
          have hrz : r = 0 := (fundamentalSequenceProp_inl_none r).1 (hr ▸ fundamentalSequence_has_prop r)
          have haz : a = 0 := (fundamentalSequenceProp_inl_none a).1 (ha ▸ fundamentalSequence_has_prop a)
          have hmk : (m : ℕ) = k + 2 := by
            have := PNat.natPred_add_one m; omega
          subst hrz; subst haz
          simp only [evalNat_oadd, evalNat_zero, Nat.succPNat_coe, pow_zero, mul_one, Nat.add_zero]
          omega
      · -- a successor → fundamentalSequence E = inr, contradicts h
        rw [ha] at h; rcases hm : m.natPred with _ | k <;> rw [hm] at h <;> simp at h
      · -- a limit → fundamentalSequence E = inr, contradicts h
        rw [ha] at h; rcases hm : m.natPred with _ | k <;> rw [hm] at h <;> simp at h
    · -- r successor: E' = oadd a m r', recurse on r
      rw [hr] at h
      obtain rfl : oadd a m r' = E' := by simpa using h
      have := ihr hr
      simp only [evalNat_oadd]; omega
    · -- r limit → fundamentalSequence E = inr, contradicts h
      rw [hr] at h; simp at h

end Goodstein.Dom
