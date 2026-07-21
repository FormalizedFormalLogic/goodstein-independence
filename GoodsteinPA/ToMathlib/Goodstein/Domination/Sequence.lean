/-
# Goodstein.Dom — Sequence
-/
module

public import Mathlib.Tactic.Ring
public import GoodsteinPA.ToMathlib.Goodstein.Defs
public import GoodsteinPA.ToMathlib.Hardy.Comparison

@[expose] public section

namespace Goodstein.Dom

open ONote Ordinal

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

/-- **Strict monotonicity of `toOrdinal b`, for `b ≥ 2`.** -/
lemma toOrdinal_strictMono (b : ℕ) (hb : 2 ≤ b) : StrictMono (toOrdinal b) :=
  fun m n hmn => (toOrdinal_mono_and_bound b hb n).1 m hmn

/-- Monotonicity of `toOrdinal b`, for `b ≥ 2`. -/
lemma toOrdinal_mono (b : ℕ) (hb : 2 ≤ b) : Monotone (toOrdinal b) :=
  (toOrdinal_strictMono b hb).monotone

/-- The order on `toOrdinal b` matches the order on `ℕ`, for `b ≥ 2`. -/
lemma toOrdinal_le_iff (b : ℕ) (hb : 2 ≤ b) {m n : ℕ} :
    toOrdinal b m ≤ toOrdinal b n ↔ m ≤ n :=
  (toOrdinal_strictMono b hb).le_iff_le

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
seeded at `m` eventually reaches `0`. (The ordinal-descent proof lives
above (`goodstein_terminates_engine`); this is the thin, faithful audit statement.) -/
theorem goodstein_terminates (m : ℕ) : ∃ N, goodsteinSeq m N = 0 :=
  goodstein_terminates_engine m


/-
# The Goodstein length function

The **Goodstein length** `goodsteinLength m` is the step at which the Goodstein
sequence seeded at `m` first reaches `0`. It is well-defined by `goodstein_terminates`
(every Goodstein sequence terminates — proved axiom-clean above).

This function is the bridge to the *independence* story. Its growth rate is
astronomically fast — it tracks the Hardy function `H_{ε₀}` (equivalently the
fast-growing `f_{ε₀}` of `Mathlib.SetTheory.Ordinal.Notation`, `ONote.fastGrowingε₀`).
Because every PA-provably-total function is dominated by some `f_α` with `α < ε₀`,
and `goodsteinLength` eventually outgrows every such `f_α`, PA cannot prove that
`goodsteinLength` is total — which is the Kirby–Paris independence result. The
*growth content* of that argument (the part that lives entirely in mathlib, no
first-order-logic machinery) is what the `ToMathlib/FastGrowing/` files develop, and
`Growth.lean` connects this function to it.

The PA-syntactic wrapper (`PA ⊬ γ`) is a separate expedition; see the repo
`~/src/goodstein-independence`. This file builds only the object-level function and
its basic API.
-/


/-- The **Goodstein length** of `m`: the least step `N` at which the Goodstein
sequence seeded at `m` reaches `0`. Total by `goodstein_terminates`. -/
def goodsteinLength (m : ℕ) : ℕ := Nat.find (goodstein_terminates m)

/-- Defining property: the sequence is `0` at its length. -/
lemma goodsteinSeq_goodsteinLength (m : ℕ) :
    goodsteinSeq m (goodsteinLength m) = 0 :=
  Nat.find_spec (goodstein_terminates m)

/-- The length is the *least* zero: any zero step is `≥ goodsteinLength m`. -/
lemma goodsteinLength_le {m N : ℕ} (h : goodsteinSeq m N = 0) :
    goodsteinLength m ≤ N :=
  Nat.find_le h

/-- Before the length, the sequence is nonzero. -/
lemma goodsteinSeq_ne_zero_of_lt {m N : ℕ} (h : N < goodsteinLength m) :
    goodsteinSeq m N ≠ 0 :=
  Nat.find_min (goodstein_terminates m) h

end Goodstein.Dom
