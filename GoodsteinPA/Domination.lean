/-
# Goodstein dominates Hardy — PORTED from Track-1 (toward `Hdom`)
Full Growth/Domination chain. Defs byte-identical to src/Defs.lean; Hardy = src/Hardy.lean.
Namespace localized to `GoodsteinPA.Dom`. Carries documented native_decide base-case axioms.
WIP — not in build target.
-/
module

public import Mathlib.Algebra.Order.SuccPred
public import Mathlib.SetTheory.Ordinal.Exponential
public import Mathlib.SetTheory.Ordinal.Notation
public meta import Mathlib.SetTheory.Ordinal.Notation  -- shake: keep
public import Mathlib.Tactic.Ring
public import GoodsteinPA.Defs
public meta import GoodsteinPA.Defs  -- shake: keep
public import GoodsteinPA.ToMathlib.Hardy
public meta import GoodsteinPA.ToMathlib.Hardy  -- shake: keep

@[expose] public section

namespace GoodsteinPA.Dom

open ONote Ordinal GoodsteinPA.FastGrowing

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

/-- **`evalNat` is fixed at the index `b` of a fundamental sequence.** If `E` is a limit with
`fundamentalSequence E = inr f`, then `evalNat b (f b) = evalNat b E`. The descent's coefficient
`b+1` (from `(b).succPNat`) is exactly what makes the base-`(b+1)` evaluation land back on
`evalNat b E`. Structural recursion on `E`; the successor sub-branches use `evalNat_succ`. -/
theorem evalNat_fundSeq (b : ℕ) : ∀ {E : ONote} {f : ℕ → ONote},
    fundamentalSequence E = Sum.inr f → evalNat b (f b) = evalNat b E := by
  intro E
  induction E with
  | zero => intro f h; exact absurd h (by simp [fundamentalSequence])
  | oadd a m r iha ihr =>
    intro f h
    rw [fundamentalSequence] at h
    have hbsucc : ((b.succPNat : ℕ+) : ℕ) = b + 1 := by simp [Nat.succPNat]
    rcases hr : fundamentalSequence r with (_ | r') | g
    · -- r = 0
      rw [hr] at h
      rcases ha : fundamentalSequence a with (_ | a') | p
      · -- a = 0: fundamentalSequence E is `inl`, contradicts h
        rw [ha] at h; rcases hm : m.natPred with _ | k <;> rw [hm] at h <;> simp at h
      · -- a successor (pred a'): uses evalNat_succ on a
        rw [ha] at h
        have hsa : evalNat b a = evalNat b a' + 1 := evalNat_succ b ha
        have hrz : r = 0 :=
          (fundamentalSequenceProp_inl_none r).1 (hr ▸ fundamentalSequence_has_prop r)
        subst hrz
        rcases hm : m.natPred with _ | k
        · -- m = 1
          rw [hm] at h
          obtain rfl : (fun i => oadd a' i.succPNat 0) = f := by simpa using h
          have hm1 : (m : ℕ) = 1 := by have := PNat.natPred_add_one m; omega
          simp only [evalNat_oadd, evalNat_zero, hbsucc, Nat.add_zero, hm1,
            one_mul, hsa, pow_succ]
          ring
        · -- m = k+2
          rw [hm] at h
          obtain rfl : (fun i => oadd a k.succPNat (oadd a' i.succPNat 0)) = f := by simpa using h
          have hmk : (m : ℕ) = k + 2 := by have := PNat.natPred_add_one m; omega
          simp only [evalNat_oadd, evalNat_zero, hbsucc, Nat.add_zero, Nat.succPNat_coe, hmk,
            hsa, pow_succ, Nat.succ_eq_add_one]
          ring
      · -- a limit (fund seq p): uses evalNat_fundSeq on a
        rw [ha] at h
        have hpa : evalNat b (p b) = evalNat b a := iha ha
        have hrz : r = 0 :=
          (fundamentalSequenceProp_inl_none r).1 (hr ▸ fundamentalSequence_has_prop r)
        subst hrz
        rcases hm : m.natPred with _ | k
        · -- m = 1
          rw [hm] at h
          obtain rfl : (fun i => oadd (p i) 1 0) = f := by simpa using h
          have hm1 : (m : ℕ) = 1 := by have := PNat.natPred_add_one m; omega
          simp only [evalNat_oadd, evalNat_zero, Nat.add_zero, hm1, one_mul, hpa,
            PNat.one_coe]
        · -- m = k+2
          rw [hm] at h
          obtain rfl : (fun i => oadd a k.succPNat (oadd (p i) 1 0)) = f := by simpa using h
          have hmk : (m : ℕ) = k + 2 := by have := PNat.natPred_add_one m; omega
          simp only [evalNat_oadd, evalNat_zero, Nat.add_zero, Nat.succPNat_coe, hmk, hpa,
            Nat.succ_eq_add_one]
          push_cast
          ring
    · -- r successor → fundamentalSequence E is `inl`, contradicts h
      rw [hr] at h; simp at h
    · -- r limit: recurse on r
      rw [hr] at h
      obtain rfl : (fun i => oadd a m (g i)) = f := by simpa using h
      have hgr : evalNat b (g b) = evalNat b r := ihr hr
      simp only [evalNat_oadd, hgr]

/-- Predecessor of a finite successor `oadd 0 ⟨c⟩ 0` (= the ordinal `c`) at any argument:
for `c ≥ 2`, `hstep (oadd 0 ⟨c⟩ 0) n = oadd 0 ⟨c-1⟩ 0`. -/
theorem hstep_finite_pred (c : ℕ) (hc : 2 ≤ c) (n : ℕ) :
    hstep (oadd 0 ⟨c, by omega⟩ 0) n = oadd 0 ⟨c - 1, by omega⟩ 0 := by
  obtain ⟨e, rfl⟩ : ∃ e, c = e + 2 := ⟨c - 2, by omega⟩
  have hfs : fundamentalSequence (oadd 0 ⟨e + 2, by omega⟩ 0)
      = Sum.inl (some (oadd 0 ⟨e + 1, by omega⟩ 0)) := by
    rw [fundamentalSequence_oadd_zero_zero]; rfl
  rw [hstep_succ _ hfs]
  rfl

/-- The `c = 1` fundamental sequence when `E` is a **successor** (`fundamentalSequence E = some E'`). -/
theorem fundSeq_oadd_one_of_succ {E E' : ONote} (h : fundamentalSequence E = Sum.inl (some E')) :
    fundamentalSequence (oadd E 1 0) = Sum.inr (fun i => oadd E' i.succPNat 0) := by
  rw [fundamentalSequence]
  simp only [show fundamentalSequence (0 : ONote) = Sum.inl none from rfl, h]; rfl

/-- The `c = 1` fundamental sequence when `E` is a **limit** (`fundamentalSequence E = inr f`). -/
theorem fundSeq_oadd_one_of_limit {E : ONote} {f : ℕ → ONote}
    (h : fundamentalSequence E = Sum.inr f) :
    fundamentalSequence (oadd E 1 0) = Sum.inr (fun i => oadd (f i) 1 0) := by
  rw [fundamentalSequence]
  simp only [show fundamentalSequence (0 : ONote) = Sum.inl none from rfl, h]; rfl

/-- One Hardy step on `oadd E 1 0` when `E` is a **successor** with predecessor `E'`: the
descent lands on `oadd E' ⟨b+1⟩ 0`. -/
theorem hstep_oadd_one_of_succ {E E' : ONote} (h : fundamentalSequence E = Sum.inl (some E'))
    (b : ℕ) : hstep (oadd E 1 0) b = hstep (oadd E' b.succPNat 0) b := by
  rw [hstep_limit _ (fundSeq_oadd_one_of_succ h)]

/-- One Hardy step on `oadd E 1 0` when `E` is a **limit** with fundamental sequence `f`: the
descent passes to `oadd (f b) 1 0`. -/
theorem hstep_oadd_one_of_limit {E : ONote} {f : ℕ → ONote}
    (h : fundamentalSequence E = Sum.inr f) (b : ℕ) :
    hstep (oadd E 1 0) b = hstep (oadd (f b) 1 0) b := by
  rw [hstep_limit _ (fundSeq_oadd_one_of_limit h)]

/-- Fundamental sequence of the finite ordinal `oadd 0 ⟨c⟩ 0` (`c ≥ 2`): the successor of
`oadd 0 ⟨c-1⟩ 0`. -/
theorem fundSeq_finite_succ (c : ℕ) (hc : 2 ≤ c) :
    fundamentalSequence (oadd 0 ⟨c, by omega⟩ 0) = Sum.inl (some (oadd 0 ⟨c - 1, by omega⟩ 0)) := by
  obtain ⟨e, rfl⟩ : ∃ e, c = e + 2 := ⟨c - 2, by omega⟩
  rw [fundamentalSequence_oadd_zero_zero]; rfl

/-- **Lemma B, finite base case (PROVED).** For `0 ≤ d ≤ b`, one Hardy step on
`ω^(d+1) = oadd (finite (d+1)) 1 0` at argument `b` is the all-digits-`b` notation
`(b+1)^(d+1) − 1`. Strong induction on `d`: the descent peels the coefficient `b+1` it
produces (`hstep_oadd_coeff`), recurses (`ih`), and the leading exponent reconstructs as a
single base-`(b+1)` digit (`toONote (b+1) d = finite d`, valid since `d ≤ b < b+1`). This is
the base case of the general `hstep_oadd_one_zero` and validates the full borrowing recursion
(descent → coefficient peel → IH → reconstruct) end-to-end. -/
theorem hstep_oadd_one_zero_finite (b : ℕ) (hb : 2 ≤ b) :
    ∀ d, d ≤ b →
      hstep (oadd (oadd 0 d.succPNat 0) 1 0) b = toONote (b + 1) ((b + 1) ^ (d + 1) - 1) := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro hdb
    have hbsucc : (b.succPNat : ℕ+) = ⟨b + 1, by omega⟩ := rfl
    rcases Nat.eq_zero_or_pos d with hd | hd
    · -- d = 0: exponent 1, descent on finite 1 → oadd 0 ⟨b+1⟩ 0 → decrement → finite b
      subst hd
      have hE1 : fundamentalSequence (oadd 0 (0 : ℕ).succPNat 0) = Sum.inl (some 0) := by
        rw [fundamentalSequence_oadd_zero_zero]; rfl
      rw [hstep_oadd_one_of_succ hE1 b, hbsucc, hstep_finite_pred (b + 1) (by omega) b,
        show (b + 1) ^ (0 + 1) - 1 = b from by rw [pow_succ, pow_zero, one_mul]; omega]
      exact (toONote_single (b + 1) (by omega) (show 1 ≤ b by omega) (by omega)).symm
    · -- d = e+1 ≥ 1: fundSeq(finite (e+2)) = some (finite (e+1)); descent → coefficient peel → ih e
      obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
      have hE' : (oadd 0 e.succPNat 0 : ONote) ≠ 0 := (oadd_pos _ _ _).ne'
      have hple : (1 : ℕ) ≤ (b + 1) ^ (e + 1) := Nat.one_le_pow _ _ (by omega)
      have hfd : fundamentalSequence (oadd 0 (e + 1).succPNat 0)
          = Sum.inl (some (oadd 0 e.succPNat 0)) := by
        rw [fundamentalSequence_oadd_zero_zero]; rfl
      rw [hstep_oadd_one_of_succ hfd b, hbsucc,
        hstep_oadd_coeff b hE' (by omega) (by omega : 1 ≤ b + 1),
        ih e (by omega) (by omega)]
      have hpow : (b + 1) ^ (e + 1 + 1) - 1 = b * (b + 1) ^ (e + 1) + ((b + 1) ^ (e + 1) - 1) := by
        have hsplit : (b + 1) ^ (e + 1 + 1) = (b + 1) * (b + 1) ^ (e + 1) := by rw [pow_succ']
        have hdist : (b + 1) * (b + 1) ^ (e + 1) = b * (b + 1) ^ (e + 1) + (b + 1) ^ (e + 1) := by
          ring
        rw [hsplit, hdist]; omega
      rw [hpow, toONote_oadd (b + 1) (by omega) (show 1 ≤ b by omega) (by omega)
        (show (b + 1) ^ (e + 1) - 1 < (b + 1) ^ (e + 1) by omega)]
      congr 1
      exact (toONote_single (b + 1) (by omega) (show 1 ≤ e + 1 by omega) (by omega)).symm

/-! ### Closing the borrowing core: the `Good`/`Canon` invariant + general predecessor

The lone gap (`hstep_oadd_one_zero`) is the `c = 1` predecessor of `ω^E` for general NF `E`.
We prove a general statement `hstep_pred_pow` for every NF `E` satisfying a coefficient
invariant `Good b E`, by well-founded recursion on `repr E`, then specialize to `E = toONote b L`.

Invariant: throughout the `fundamentalSequence` descent the notation is *canonical in base
`b+1`* (`Canon`: all coefficients `≤ b`) except for at most one coefficient `b+1` parked at the
"active frontier" (`Good`). `Good` is preserved by the limit descent (`Good_fundSeq`); for a
*successor* the `b+1` is forced into the finite lowest term, so its predecessor is fully `Canon`
(`Canon_pred`). A `Canon` NF notation round-trips through `evalNat`
(`canon_round_trip : toONote (b+1) (evalNat b E) = E`) — exactly the successor reconstruction. -/

/-- `toOrdinal B (B^k) = ω^(toOrdinal B k)`: a pure power is a single leading `ω`-power. -/
theorem toOrdinal_pow (B : ℕ) (hB : 2 ≤ B) (k : ℕ) :
    toOrdinal B (B ^ k) = ω ^ toOrdinal B k := by
  have hBk : B ^ k ≠ 0 := pow_ne_zero _ (by omega)
  rw [toOrdinal_pos B _ hBk, Nat.log_pow (by omega), Nat.div_self (Nat.pow_pos (by omega)),
    Nat.mod_self, toOrdinal_zero, Nat.cast_one, mul_one, add_zero]

/-- Constructor form of `toOrdinal` (the ordinal twin of `toONote_oadd`): for `1 ≤ c < B` and
`s < B^k`, `toOrdinal B (c·B^k + s) = ω^(toOrdinal B k)·c + toOrdinal B s`. -/
theorem toOrdinal_oadd (B : ℕ) (hB : 2 ≤ B) {c k s : ℕ} (hc : 1 ≤ c) (hcB : c < B)
    (hs : s < B ^ k) :
    toOrdinal B (c * B ^ k + s) = ω ^ toOrdinal B k * (c : Ordinal) + toOrdinal B s := by
  have hBk_pos : 0 < B ^ k := Nat.pow_pos (by omega)
  have hn0 : c * B ^ k + s ≠ 0 := by positivity
  have hlow : c * B ^ k + s < B ^ (k + 1) := by
    calc c * B ^ k + s < c * B ^ k + B ^ k := by omega
      _ = (c + 1) * B ^ k := by ring
      _ ≤ B * B ^ k := Nat.mul_le_mul_right _ (by omega)
      _ = B ^ (k + 1) := by rw [pow_succ]; ring
  have hge : B ^ k ≤ c * B ^ k + s :=
    (Nat.le_mul_of_pos_left (B ^ k) hc).trans (Nat.le_add_right _ _)
  have hlog : Nat.log B (c * B ^ k + s) = k := Nat.log_eq_of_pow_le_of_lt_pow hge hlow
  have hdiv : (c * B ^ k + s) / B ^ k = c := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hBk_pos, Nat.div_eq_of_lt hs, Nat.zero_add]
  have hmod : (c * B ^ k + s) % B ^ k = s := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hs]
  rw [toOrdinal_pos B _ hn0, hlog, hdiv, hmod]

/-- `Canon b o`: the notation `o` is in canonical base-`(b+1)` form — every coefficient is
`≤ b` (a valid base-`(b+1)` digit), recursively on exponents and tails. -/
def Canon (b : ℕ) : ONote → Prop
  | 0 => True
  | oadd e n r => (n : ℕ) ≤ b ∧ Canon b e ∧ Canon b r

theorem Canon_zero (b : ℕ) : Canon b 0 := trivial

theorem Canon_oadd (b : ℕ) (e : ONote) (n : ℕ+) (r : ONote) :
    Canon b (oadd e n r) ↔ (n : ℕ) ≤ b ∧ Canon b e ∧ Canon b r := Iff.rfl

/-- A `Canon` NF notation is recovered by reading `evalNat` back at the ordinal level:
`toOrdinal (b+1) (evalNat b E) = repr E`. Structural induction; the leading-term remainder
bound for `toOrdinal_oadd` comes from `NF` via the engine's strict monotonicity. -/
theorem canon_repr (b : ℕ) (hb : 1 ≤ b) :
    ∀ E : ONote, Canon b E → E.NF → toOrdinal (b + 1) (evalNat b E) = E.repr := by
  have hSM : StrictMono (toOrdinal (b + 1)) := fun a c hac =>
    (toOrdinal_mono_and_bound (b + 1) (by omega) c).1 a hac
  intro E
  induction E with
  | zero => intro _ _; simp
  | oadd e n r ihe ihr =>
    intro hcanon hNF
    obtain ⟨hn, hce, hcr⟩ := (Canon_oadd b e n r).1 hcanon
    have hNFe : e.NF := hNF.fst
    have hNFr : r.NF := hNF.snd
    have hbelow : r.repr < ω ^ e.repr := hNF.snd'.repr_lt
    have hre := ihe hce hNFe
    have hrr := ihr hcr hNFr
    have hbound : evalNat b r < (b + 1) ^ evalNat b e := by
      apply hSM.lt_iff_lt.1
      rw [toOrdinal_pow (b + 1) (by omega), hre, hrr]
      exact hbelow
    rw [evalNat_oadd, toOrdinal_oadd (b + 1) (by omega) n.pos (by omega) hbound, hre, hrr]
    simp

/-- A `Canon` NF notation round-trips through `evalNat`: `toONote (b+1) (evalNat b E) = E`. -/
theorem canon_round_trip (b : ℕ) (hb : 2 ≤ b) (E : ONote) (hcanon : Canon b E) (hNF : E.NF) :
    toONote (b + 1) (evalNat b E) = E := by
  haveI : (toONote (b + 1) (evalNat b E)).NF := toONote_NF (b + 1) (by omega) (evalNat b E)
  haveI : E.NF := hNF
  rw [← repr_inj, repr_toONote (b + 1) (by omega), canon_repr b (by omega) E hcanon hNF]

/-- `Good b o`: `o` is `Canon` except for at most one coefficient `= b+1`, parked at the active
frontier of the descent — the lowest term, deeper in the tail, or (when `o = ω^e`) inside the
exponent. Preserved by the descent; on a *successor* the `b+1` is forced low. -/
def Good (b : ℕ) : ONote → Prop
  | 0 => True
  | oadd e n r =>
      (Canon b e ∧ (n : ℕ) ≤ b ∧ Good b r) ∨
      (Canon b e ∧ (n : ℕ) = b + 1 ∧ r = 0) ∨
      ((n : ℕ) = 1 ∧ r = 0 ∧ Good b e)

theorem Good_zero (b : ℕ) : Good b 0 := trivial

theorem Good_oadd (b : ℕ) (e : ONote) (n : ℕ+) (r : ONote) :
    Good b (oadd e n r) ↔
      (Canon b e ∧ (n : ℕ) ≤ b ∧ Good b r) ∨
      (Canon b e ∧ (n : ℕ) = b + 1 ∧ r = 0) ∨
      ((n : ℕ) = 1 ∧ r = 0 ∧ Good b e) := Iff.rfl

theorem Good_of_Canon (b : ℕ) : ∀ E, Canon b E → Good b E := by
  intro E
  induction E with
  | zero => intro _; exact trivial
  | oadd e n r _ ihr =>
    intro hc
    obtain ⟨hn, hce, hcr⟩ := (Canon_oadd b e n r).1 hc
    exact (Good_oadd b e n r).2 (Or.inl ⟨hce, hn, ihr hcr⟩)

theorem Canon_toONote (b : ℕ) (hb : 2 ≤ b) : ∀ L, Canon b (toONote b L) := by
  intro L
  induction L using Nat.strong_induction_on with
  | _ L ih =>
    rcases eq_or_ne L 0 with rfl | hL
    · rw [toONote_zero]; exact Canon_zero b
    · have hlog : Nat.log b L < L := Nat.log_lt_self b hL
      have hbe_pos : 0 < b ^ Nat.log b L := Nat.pow_pos (by omega)
      have hbe_le : b ^ Nat.log b L ≤ L := Nat.pow_log_le_self b hL
      have hr_lt : L % b ^ Nat.log b L < L := lt_of_lt_of_le (Nat.mod_lt _ hbe_pos) hbe_le
      have hcb : L / b ^ Nat.log b L < b := by
        apply Nat.div_lt_of_lt_mul
        have h := Nat.lt_pow_succ_log_self (show 1 < b by omega) L
        rwa [pow_succ] at h
      rw [toONote, dif_neg hL]
      refine (Canon_oadd b _ _ _).2 ⟨?_, ih _ hlog, ih _ hr_lt⟩
      rw [PNat.toPNat'_coe (Nat.div_pos hbe_le hbe_pos)]
      omega

/-- For a `Good` *successor* notation, the predecessor is fully `Canon`: the parked `b+1`
coefficient (if any) is forced into the finite lowest term, which `pred` decrements to `≤ b`. -/
theorem Canon_pred (b : ℕ) : ∀ E E', Good b E → fundamentalSequence E = Sum.inl (some E') →
    Canon b E' := by
  intro E
  induction E with
  | zero => intro E' _ h; exact absurd h (by simp [fundamentalSequence])
  | oadd a m r _ ihr =>
    intro E' hgood h
    rw [fundamentalSequence] at h
    rcases hr : fundamentalSequence r with (_ | r') | g
    · -- r = 0
      rw [hr] at h
      have hrz : r = 0 :=
        (fundamentalSequenceProp_inl_none r).1 (hr ▸ fundamentalSequence_has_prop r)
      subst hrz
      rcases ha : fundamentalSequence a with (_ | a') | p
      · -- a = 0
        rw [ha] at h
        have haz : a = 0 :=
          (fundamentalSequenceProp_inl_none a).1 (ha ▸ fundamentalSequence_has_prop a)
        subst haz
        rcases hm : m.natPred with _ | k
        · -- m = 1, E' = 0
          rw [hm] at h
          obtain rfl : (0 : ONote) = E' := by simpa using h
          exact Canon_zero b
        · -- m = k+2, E' = oadd 0 k.succPNat 0
          rw [hm] at h
          obtain rfl : oadd 0 k.succPNat 0 = E' := by simpa using h
          have hmk : (m : ℕ) = k + 2 := by have := PNat.natPred_add_one m; omega
          have hmb : (m : ℕ) ≤ b + 1 := by
            rcases (Good_oadd b 0 m 0).1 hgood with ⟨_, hh, _⟩ | ⟨_, hh, _⟩ | ⟨hh, _, _⟩ <;> omega
          refine (Canon_oadd b _ _ _).2 ⟨?_, Canon_zero b, Canon_zero b⟩
          rw [Nat.succPNat_coe]; omega
      · -- a successor → inr, contradicts h (inl)
        rw [ha] at h; rcases hm : m.natPred with _ | k <;> rw [hm] at h <;> simp at h
      · -- a limit → inr, contradicts h (inl)
        rw [ha] at h; rcases hm : m.natPred with _ | k <;> rw [hm] at h <;> simp at h
    · -- r successor: E' = oadd a m r', recurse on r
      rw [hr] at h
      obtain rfl : oadd a m r' = E' := by simpa using h
      have hrne : r ≠ 0 := by intro h0; rw [h0] at hr; simp [fundamentalSequence] at hr
      obtain ⟨hca, hmb, hgr⟩ : Canon b a ∧ (m : ℕ) ≤ b ∧ Good b r := by
        rcases (Good_oadd b a m r).1 hgood with H | ⟨_, _, hrz⟩ | ⟨_, hrz, _⟩
        · exact H
        · exact absurd hrz hrne
        · exact absurd hrz hrne
      exact (Canon_oadd b a m r').2 ⟨hmb, hca, ihr r' hgr hr⟩
    · -- r limit → inr, contradicts h (inl)
      rw [hr] at h; simp at h

/-- `Good` is preserved by one step of the limit descent at the working index `b`:
if `Good b E` and `fundamentalSequence E = inr f`, then `Good b (f b)`. -/
theorem Good_fundSeq (b : ℕ) : ∀ E f, Good b E → fundamentalSequence E = Sum.inr f →
    Good b (f b) := by
  intro E
  induction E with
  | zero => intro f _ h; exact absurd h (by simp [fundamentalSequence])
  | oadd a m r iha ihr =>
    intro f hgood h
    rw [fundamentalSequence] at h
    have hbpnat : (b.succPNat : ℕ+) = ⟨b + 1, by omega⟩ := rfl
    have hbnat : ((b.succPNat : ℕ+) : ℕ) = b + 1 := by simp [Nat.succPNat]
    rcases hr : fundamentalSequence r with (_ | r') | g
    · -- r = 0
      rw [hr] at h
      have hrz : r = 0 :=
        (fundamentalSequenceProp_inl_none r).1 (hr ▸ fundamentalSequence_has_prop r)
      subst hrz
      rcases ha : fundamentalSequence a with (_ | a') | p
      · -- a = 0 → inl, contradicts h (inr)
        rw [ha] at h; rcases hm : m.natPred with _ | k <;> rw [hm] at h <;> simp at h
      · -- a successor a'
        rw [ha] at h
        have hga : Good b a := by
          rcases (Good_oadd b a m 0).1 hgood with ⟨hca, _, _⟩ | ⟨hca, _, _⟩ | ⟨_, _, hga⟩
          · exact Good_of_Canon b a hca
          · exact Good_of_Canon b a hca
          · exact hga
        have hca' : Canon b a' := Canon_pred b a a' hga ha
        rcases hm : m.natPred with _ | k
        · -- m = 1: f b = oadd a' b.succPNat 0
          rw [hm] at h
          obtain rfl : (fun i => oadd a' i.succPNat 0) = f := by simpa using h
          show Good b (oadd a' b.succPNat 0)
          exact (Good_oadd b a' b.succPNat 0).2 (Or.inr (Or.inl ⟨hca', hbnat, rfl⟩))
        · -- m = k+2: f b = oadd a k.succPNat (oadd a' b.succPNat 0)
          rw [hm] at h
          obtain rfl : (fun i => oadd a k.succPNat (oadd a' i.succPNat 0)) = f := by simpa using h
          have hmk : (m : ℕ) = k + 2 := by have := PNat.natPred_add_one m; omega
          have hcam : Canon b a ∧ (m : ℕ) ≤ b + 1 := by
            rcases (Good_oadd b a m 0).1 hgood with ⟨hca, hh, _⟩ | ⟨hca, hh, _⟩ | ⟨hh, _, _⟩
            · exact ⟨hca, by omega⟩
            · exact ⟨hca, by omega⟩
            · exfalso; omega
          show Good b (oadd a k.succPNat (oadd a' b.succPNat 0))
          refine (Good_oadd b a k.succPNat _).2 (Or.inl ⟨hcam.1, ?_, ?_⟩)
          · rw [Nat.succPNat_coe]; omega
          · exact (Good_oadd b a' b.succPNat 0).2 (Or.inr (Or.inl ⟨hca', hbnat, rfl⟩))
      · -- a limit p
        rw [ha] at h
        have hga : Good b a := by
          rcases (Good_oadd b a m 0).1 hgood with ⟨hca, _, _⟩ | ⟨hca, _, _⟩ | ⟨_, _, hga⟩
          · exact Good_of_Canon b a hca
          · exact Good_of_Canon b a hca
          · exact hga
        have hgpb : Good b (p b) := iha p hga ha
        rcases hm : m.natPred with _ | k
        · -- m = 1: f b = oadd (p b) 1 0
          rw [hm] at h
          obtain rfl : (fun i => oadd (p i) 1 0) = f := by simpa using h
          show Good b (oadd (p b) 1 0)
          exact (Good_oadd b (p b) 1 0).2 (Or.inr (Or.inr ⟨PNat.one_coe, rfl, hgpb⟩))
        · -- m = k+2: f b = oadd a k.succPNat (oadd (p b) 1 0)
          rw [hm] at h
          obtain rfl : (fun i => oadd a k.succPNat (oadd (p i) 1 0)) = f := by simpa using h
          have hmk : (m : ℕ) = k + 2 := by have := PNat.natPred_add_one m; omega
          have hcam : Canon b a ∧ (m : ℕ) ≤ b + 1 := by
            rcases (Good_oadd b a m 0).1 hgood with ⟨hca, hh, _⟩ | ⟨hca, hh, _⟩ | ⟨hh, _, _⟩
            · exact ⟨hca, by omega⟩
            · exact ⟨hca, by omega⟩
            · exfalso; omega
          show Good b (oadd a k.succPNat (oadd (p b) 1 0))
          refine (Good_oadd b a k.succPNat _).2 (Or.inl ⟨hcam.1, ?_, ?_⟩)
          · rw [Nat.succPNat_coe]; omega
          · exact (Good_oadd b (p b) 1 0).2 (Or.inr (Or.inr ⟨PNat.one_coe, rfl, hgpb⟩))
    · -- r successor → inl, contradicts h (inr)
      rw [hr] at h; simp at h
    · -- r limit g: f b = oadd a m (g b)
      rw [hr] at h
      obtain rfl : (fun i => oadd a m (g i)) = f := by simpa using h
      have hrne : r ≠ 0 := by intro h0; rw [h0] at hr; simp [fundamentalSequence] at hr
      obtain ⟨hca, hmb, hgr⟩ : Canon b a ∧ (m : ℕ) ≤ b ∧ Good b r := by
        rcases (Good_oadd b a m r).1 hgood with H | ⟨_, _, hrz⟩ | ⟨_, hrz, _⟩
        · exact H
        · exact absurd hrz hrne
        · exact absurd hrz hrne
      show Good b (oadd a m (g b))
      exact (Good_oadd b a m (g b)).2 (Or.inl ⟨hca, hmb, ihr g hgr hr⟩)

/-- **The general borrowing predecessor.** For every NF `E ≠ 0` satisfying the frontier
invariant `Good b E`, one Hardy step on `ω^E` (`= oadd E 1 0`) at argument `b` is the
all-digits-`b` base-`(b+1)` notation of `(b+1)^(evalNat b E) − 1`. Well-founded recursion on
`repr E`: the limit case closes via the IH on `f b` and `evalNat_fundSeq`; the successor case
peels the coefficient (`hstep_oadd_coeff`), applies the IH to the predecessor `E'`, and
reconstructs `E'` via `canon_round_trip` (valid since `Canon_pred` makes `E'` canonical). -/
theorem hstep_pred_pow (b : ℕ) (hb : 2 ≤ b) :
    ∀ E : ONote, E.NF → E ≠ 0 → Good b E →
      hstep (oadd E 1 0) b = toONote (b + 1) ((b + 1) ^ evalNat b E - 1) := by
  suffices H : ∀ o : Ordinal, ∀ E : ONote, E.repr = o → E.NF → E ≠ 0 → Good b E →
      hstep (oadd E 1 0) b = toONote (b + 1) ((b + 1) ^ evalNat b E - 1) by
    exact fun E => H E.repr E rfl
  intro o
  induction o using WellFoundedLT.induction with
  | _ o ih =>
    intro E hrepr hNF hne hgood
    have hbpnat : (b.succPNat : ℕ+) = ⟨b + 1, by omega⟩ := rfl
    rcases hfs : fundamentalSequence E with (_ | E') | f
    · exact absurd ((fundamentalSequenceProp_inl_none E).1 (hfs ▸ fundamentalSequence_has_prop E)) hne
    · -- successor: peel the coefficient, recurse on the predecessor, reconstruct
      obtain ⟨hsucc, hNFimp⟩ :=
        (fundamentalSequenceProp_inl_some E E').1 (hfs ▸ fundamentalSequence_has_prop E)
      have hNFE' : E'.NF := hNFimp hNF
      have hltE' : E'.repr < o := by rw [← hrepr, hsucc]; exact Order.lt_succ _
      have hcanonE' : Canon b E' := Canon_pred b E E' hgood hfs
      have hevalE : evalNat b E = evalNat b E' + 1 := evalNat_succ b hfs
      rcases eq_or_ne E' 0 with hE'0 | hE'0
      · subst hE'0
        rw [hstep_oadd_one_of_succ hfs b, hbpnat, hstep_finite_pred (b + 1) (by omega) b,
          hevalE, evalNat_zero,
          show (b + 1) ^ (0 + 1) - 1 = b from by rw [pow_succ, pow_zero, one_mul]; omega]
        exact (toONote_single (b + 1) (by omega) (show 1 ≤ b by omega) (by omega)).symm
      · rw [hstep_oadd_one_of_succ hfs b, hbpnat,
          hstep_oadd_coeff b hE'0 (by omega : 2 ≤ b + 1) (by omega : 1 ≤ b + 1),
          ih E'.repr hltE' E' rfl hNFE' hE'0 (Good_of_Canon b E' hcanonE'), hevalE]
        have hpos : 1 ≤ (b + 1) ^ evalNat b E' := Nat.one_le_pow _ _ (by omega)
        rw [show (b + 1) ^ (evalNat b E' + 1) - 1
              = b * (b + 1) ^ evalNat b E' + ((b + 1) ^ evalNat b E' - 1) from by
            rw [pow_succ']
            have hX : (b + 1) * (b + 1) ^ evalNat b E'
                    = b * (b + 1) ^ evalNat b E' + (b + 1) ^ evalNat b E' := by ring
            omega,
          toONote_oadd (b + 1) (by omega) (show 1 ≤ b by omega) (by omega) (by omega),
          canon_round_trip b hb E' hcanonE' hNFE']
        rfl
    · -- limit: recurse on `f b`; `evalNat_fundSeq` lands the size, no reconstruction
      obtain ⟨_, hbody, _⟩ :=
        (fundamentalSequenceProp_inr E f).1 (hfs ▸ fundamentalSequence_has_prop E)
      have hfbne : f b ≠ 0 := fundamentalSequence_inr_ne_zero hfs b
      have hNFfb : (f b).NF := (hbody b).2.2 hNF
      have hltfb : (f b).repr < o := by rw [← hrepr]; exact repr_lt_repr (hbody b).2.1
      rw [hstep_oadd_one_of_limit hfs b,
        ih (f b).repr hltfb (f b) rfl hNFfb hfbne (Good_fundSeq b E f hgood hfs),
        evalNat_fundSeq b hfs]

/-- **Lemma B (the `c = 1` predecessor — the borrowing core of C3, FULLY PROVED lap 5).** One Hardy
step on `oadd (toONote b L) 1 0` (i.e. `ω^E` for `E = toONote b L`, `L ≥ 1`) at argument `b` is the
base-`(b+1)` notation of `(b+1)^(bump b L) − 1` — the fully-filled (all-digits-`b`) expansion
produced by the borrowing descent through `fundamentalSequence`.

**PROVED + `#print axioms` clean** — this was the last disclosed `sorry` of C3 and it is discharged.
The proof closes via `hstep_pred_pow` (WF recursion on `repr E`, using the `Good`/`Canon` coefficient-
bound frontier invariant) + `evalNat_toONote`. The plan below is the historical close-out record.

**Supporting engine** (all axiom-clean, this file):
* **finite base case** `hstep_oadd_one_zero_finite` (`E = finite (d+1)`, `d ≤ b`) — exercises
  the whole engine end-to-end (descent `hstep_oadd_one_of_succ` → peel `hstep_oadd_coeff` →
  IH → reconstruct `toONote_oadd`);
* the **answer characterization** `evalNat` + `evalNat_toONote : evalNat b (toONote b L) =
  bump b L` (so the general answer `toONote (b+1) ((b+1)^(evalNat b E) − 1)` is the target);
* both **descent identities**: `evalNat_succ` (`fundamentalSequence E = some E' ⟹
  evalNat b E = evalNat b E' + 1`) and `evalNat_fundSeq` (`fundamentalSequence E = inr f ⟹
  evalNat b (f b) = evalNat b E`).

**Plan to close** — prove the general `∀ NF E ≠ 0, hstep (oadd E 1 0) b =
toONote (b+1) ((b+1)^(evalNat b E) − 1)` by well-founded recursion on `repr E`:
* **limit case CLOSES** outright: `hstep_oadd_one_of_limit` → IH on `f b` → `evalNat_fundSeq`.
* **successor case** needs `evalNat_succ` (done) plus the reconstruction
  `toONote (b+1) (evalNat b E') = E'` for `E' = pred E`. This is the LONE remaining piece: it
  requires a coefficient-bound invariant `Good b E` (all coeffs ≤ b+1, and every coeff-`(b+1)`
  term has tail `0`) carried through the recursion — `Good` holds at the start `toONote b L`
  (coeffs `< b`), is preserved by `f b` (the new `b+1` coeff sits on a tail-`0` term) and by
  `pred`, and for a *successor* `E` forces any `b+1` coeff into the finite lowest term, which
  `pred` then removes — so `pred E` has all coeffs `< b+1` and reconstructs. Then
  `hstep_oadd_one_zero` is the `E = toONote b L` instance (with `evalNat_toONote`).
Verified syntactically by `native_decide` on small cases (see anchors). -/
theorem hstep_oadd_one_zero (b : ℕ) (hb : 2 ≤ b) (L : ℕ) (hL : 1 ≤ L) :
    hstep (oadd (toONote b L) 1 0) b = toONote (b + 1) ((b + 1) ^ bump b L - 1) := by
  have hE : toONote b L ≠ 0 := by rw [Ne, toONote_eq_zero_iff]; omega
  have hNF : (toONote b L).NF := toONote_NF b hb L
  have hgood : Good b (toONote b L) := Good_of_Canon b _ (Canon_toONote b hb L)
  rw [hstep_pred_pow b hb (toONote b L) hNF hE hgood, evalNat_toONote b hb L]

/-- **The Cichoń step (THE C3 CRUX).** One budget-incrementing Hardy step on the base-`b`
notation of `p ≠ 0`, at argument `b`, equals the notation (in base `b+1`) of the
Goodstein operation `bump b p − 1`:

  `hstep (toONote b p) b = toONote (b+1) (bump b p − 1)`.

This is the heart of Cichoń's theorem (1983) identifying the Goodstein descent with the
Hardy descent. Strong induction on `p`, writing `p = c·b^L + r` (leading Cantor term):

* **`r ≠ 0` (FULLY PROVED).** The leading term is preserved and the step happens in the tail:
  `hstep (oadd E C R) b = oadd E C (hstep R b)` (`hstep_oadd_tail`), then the IH on `r < p`
  and the reconstruction `toONote_oadd` + bump-invariance `toONote_bump` close it.
* **`r = 0`.** Here `p = c·b^L` and the step computes the *predecessor* of `c·(b+1)^(bump b L)`.
  - `L = 0` (single digit, FULLY PROVED): `oadd 0 c 0` is a successor (`hstep_oadd_zero_zero`).
  - `L ≥ 1` (**FULLY PROVED**, lap 5, via `hstep_oadd_one_zero`): the genuine **borrowing** case —
    a nested `fundamentalSequence` descent producing the filled `(b+1)`-ary expansion of
    `(b+1)^(bump b L) − 1`. This was the borrowing core of C3; now discharged, `#print axioms` clean.

This theorem is now FULLY PROVED for all `p` (`r ≠ 0`, `r = 0 ∧ L = 0`, and `r = 0 ∧ L ≥ 1`). -/
theorem hstep_toONote (b : ℕ) (hb : 2 ≤ b) : ∀ p, p ≠ 0 →
    hstep (toONote b p) b = toONote (b + 1) (bump b p - 1) := by
  intro p
  induction p using Nat.strong_induction_on with
  | _ p ih =>
    intro hp
    have hbe_pos : 0 < b ^ Nat.log b p := Nat.pow_pos (by omega)
    have hbe_le : b ^ Nat.log b p ≤ p := Nat.pow_log_le_self b hp
    have hc1 : 1 ≤ p / b ^ Nat.log b p := Nat.div_pos hbe_le hbe_pos
    have hcb : p / b ^ Nat.log b p < b := by
      apply Nat.div_lt_of_lt_mul
      have h := Nat.lt_pow_succ_log_self (show 1 < b by omega) p
      rwa [pow_succ] at h
    have hr_lt : p % b ^ Nat.log b p < b ^ Nat.log b p := Nat.mod_lt _ hbe_pos
    have hp_eq : p = (p / b ^ Nat.log b p) * b ^ Nat.log b p + p % b ^ Nat.log b p := by
      rw [mul_comm]; exact (Nat.div_add_mod p _).symm
    set L := Nat.log b p
    set c := p / b ^ L with hc_def
    set r := p % b ^ L with hr_def
    have htoP : toONote b p = oadd (toONote b L) ⟨c, hc1⟩ (toONote b r) := by
      conv_lhs => rw [hp_eq]
      exact toONote_oadd b hb hc1 hcb hr_lt
    have hbump : bump b p = c * (b + 1) ^ bump b L + bump b r := bump_pos b p hp
    rcases eq_or_ne r 0 with hr0 | hr0
    · -- r = 0: the predecessor of `c·b^L`
      rcases Nat.eq_zero_or_pos L with hL0 | hLpos
      · -- L = 0: a single digit `c`; `oadd 0 c 0` is a successor (PROVED)
        have hEz : toONote b L = 0 := by rw [hL0, toONote_zero]
        have hbumpL : bump b L = 0 := by rw [hL0, bump_zero]
        rw [htoP, hr0, hEz, toONote_zero, hstep_oadd_zero_zero b hb c hc1 hcb]
        congr 1
        rw [hbump, hr0, hbumpL, bump_zero]; simp
      · -- L ≥ 1: borrowing case. Peel the coefficient (`hstep_oadd_coeff`) down to the
        -- `c = 1` predecessor `hstep_oadd_one_zero`, then reconstruct via `toONote_oadd`.
        have hE : toONote b L ≠ 0 := by rw [Ne, toONote_eq_zero_iff]; omega
        have htoP0 : toONote b p = oadd (toONote b L) ⟨c, hc1⟩ 0 := by
          rw [htoP, hr0, toONote_zero]
        have hbump0 : bump b p - 1 = c * (b + 1) ^ bump b L - 1 := by
          rw [hbump, hr0, bump_zero, Nat.add_zero]
        rcases eq_or_ne c 1 with hc1' | hc2'
        · -- c = 1: directly Lemma B
          have hcpn : (⟨c, hc1⟩ : ℕ+) = 1 := PNat.coe_injective hc1'
          rw [htoP0, hcpn, hbump0, hc1', one_mul]
          exact hstep_oadd_one_zero b hb L hLpos
        · -- c ≥ 2: peel to `oadd E ⟨c-1⟩ (hstep (oadd E 1 0) b)`, recombine
          have hMpos : 1 ≤ (b + 1) ^ bump b L := Nat.one_le_pow _ _ (by omega)
          have key : c * (b + 1) ^ bump b L - 1
              = (c - 1) * (b + 1) ^ bump b L + ((b + 1) ^ bump b L - 1) := by
            have h := Nat.sub_one_mul c ((b + 1) ^ bump b L)
            have hcX : (b + 1) ^ bump b L ≤ c * (b + 1) ^ bump b L :=
              Nat.le_mul_of_pos_left _ (by omega)
            omega
          rw [htoP0, hstep_oadd_coeff b hE (by omega) hc1, hstep_oadd_one_zero b hb L hLpos,
            hbump0, key]
          rw [toONote_oadd (b + 1) (by omega) (show 1 ≤ c - 1 by omega) (by omega)
              (show (b + 1) ^ bump b L - 1 < (b + 1) ^ bump b L by omega),
            toONote_bump b hb]
    · -- r ≠ 0: leading term preserved, the step happens in the tail
      have hRne : toONote b r ≠ 0 := by rw [Ne, toONote_eq_zero_iff]; exact hr0
      have hbr_pos : 0 < bump b r := by
        rw [bump_pos b r hr0]
        have h1 : 0 < r / b ^ Nat.log b r :=
          Nat.div_pos (Nat.pow_log_le_self _ hr0) (Nat.pow_pos (by omega))
        have h2 : 0 < (b + 1) ^ bump b (Nat.log b r) := Nat.pow_pos (by omega)
        have := Nat.mul_pos h1 h2; omega
      have hbrB : bump b r < (b + 1) ^ bump b L := bump_lt_pow b hb hr_lt
      rw [htoP, hstep_oadd_tail (toONote b L) ⟨c, hc1⟩ b (toONote b r) hRne, ih r (by omega) hr0]
      have hsub : bump b p - 1 = c * (b + 1) ^ bump b L + (bump b r - 1) := by rw [hbump]; omega
      rw [hsub, toONote_oadd (b + 1) (by omega) hc1 (by omega)
        (by omega : bump b r - 1 < (b + 1) ^ bump b L), toONote_bump b hb]

/-- The Cichoń step, specialised to the Goodstein descent: one Goodstein step is one
budget-incrementing Hardy step on the notation. `seqONote m (k+1) = hstep (seqONote m k) (k+2)`
whenever the term is nonzero. -/
theorem hstep_seqONote (m k : ℕ) (h : goodsteinSeq m k ≠ 0) :
    hstep (seqONote m k) (k + 2) = seqONote m (k + 1) := by
  show hstep (toONote (k + 2) (goodsteinSeq m k)) (k + 2) = toONote (k + 1 + 2) (goodsteinSeq m (k + 1))
  rw [hstep_toONote (k + 2) (by omega) (goodsteinSeq m k) h]
  rfl

/-- **The per-step Hardy invariant.** Along the Goodstein descent (while nonzero) the Hardy
value `H_{seqONote m k}(k+2)` is unchanged: `H_{seqONote m k}(k+2) = H_{seqONote m (k+1)}((k+1)+2)`.
Combines the intrinsic step invariant `hardy_hstep` with the Cichoń step `hstep_seqONote`. -/
theorem hardy_seqONote_step (m k : ℕ) (h : goodsteinSeq m k ≠ 0) :
    hardy (seqONote m k) (k + 2) = hardy (seqONote m (k + 1)) (k + 1 + 2) := by
  have ho : seqONote m k ≠ 0 := fun hz => h ((seqONote_eq_zero_iff m k).1 hz)
  rw [hardy_hstep (seqONote m k) (k + 2) ho, hstep_seqONote m k h]

/-- **Telescoping.** For every `j ≤ goodsteinLength m`, the Hardy value at the start equals
the Hardy value `j` steps in: `H_{seqONote m 0}(2) = H_{seqONote m j}(j+2)`. Induction on `j`
using `hardy_seqONote_step` (valid since `j < goodsteinLength m` ⟹ the `j`-th term is nonzero). -/
theorem hardy_seqONote_telescope (m : ℕ) :
    ∀ j, j ≤ goodsteinLength m → hardy (seqONote m 0) 2 = hardy (seqONote m j) (j + 2) := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ k ih =>
    intro hj
    have hk : k < goodsteinLength m := Nat.lt_of_succ_le hj
    rw [ih (Nat.le_of_lt hk), hardy_seqONote_step m k (goodsteinSeq_ne_zero_of_lt hk)]

/-- **C3 — the growth theorem (Hardy form).** The Hardy value of the starting notation at the
starting base is the Goodstein length plus two: `H_{seqONote m 0}(2) = goodsteinLength m + 2`.
At `j = goodsteinLength m` the descent reaches the zero notation, where `H_0(N) = N`. -/
theorem hardy_seqONote_zero (m : ℕ) : hardy (seqONote m 0) 2 = goodsteinLength m + 2 := by
  rw [hardy_seqONote_telescope m (goodsteinLength m) le_rfl, seqONote_goodsteinLength, hardy_zero]
  rfl

/-- **C3 — the growth theorem (length form).** The Goodstein length of `m` is exactly the
Hardy value of its starting notation (read in base 2) at argument 2, minus 2:

  `goodsteinLength m = H_{seqONote m 0}(2) − 2`.

This is Cichoń's identity formalised: the Goodstein length function *is* a Hardy function of
the starting ordinal notation. Since the Hardy/fast-growing hierarchy reaches `ε₀`
(`FastGrowing/Domination.lean`, A4), this pins `goodsteinLength`'s growth at the `ε₀` level —
the growth content of Kirby–Paris independence. -/
theorem goodsteinLength_eq_hardy (m : ℕ) : goodsteinLength m = hardy (seqONote m 0) 2 - 2 := by
  rw [hardy_seqONote_zero]; omega

/-! ### Anti-vacuity anchors (`native_decide`)

The notations are computable; small values pin them (a wrong recursion would fail). -/

example : toONote 2 1 = oadd 0 1 0 := by native_decide          -- `1 = ω^0`
example : toONote 2 2 = oadd (oadd 0 1 0) 1 0 := by native_decide -- `2 = 2^1 ↦ ω^1 = ω`
example : toONote 2 4 = oadd (oadd (oadd 0 1 0) 1 0) 1 0 := by native_decide -- `4 = 2^2 ↦ ω^ω`
example : toONote 3 5 = oadd (oadd 0 1 0) 1 (oadd 0 2 0) := by native_decide  -- `5 = 1·3^1 + 2`
-- the descent: `goodsteinSeq 3` starts `3 ↦ 3 ↦ 3 ↦ 2 ↦ …`, notations strictly drop
example : seqONote 3 0 = oadd (oadd 0 1 0) 1 (oadd 0 1 0) := by native_decide -- `G₀=3` in base 2 ↦ `ω+1`
-- the Cichoń step `hstep_toONote` (now FULLY PROVED) holds; here anchored on computable cases:
example : hstep (toONote 2 3) 2 = toONote 3 (bump 2 3 - 1) := by native_decide
example : hstep (toONote 3 5) 3 = toONote 4 (bump 3 5 - 1) := by native_decide
example : hstep (seqONote 3 0) 2 = seqONote 3 1 := by native_decide
-- C3, witnessed on a computable case: `goodsteinLength 3 = H_{seqONote 3 0}(2) − 2 = 7 − 2 = 5`
example : hardy (seqONote 3 0) 2 = goodsteinLength 3 + 2 := by native_decide


-- ════════════════ ported: Domination.lean ════════════════
/-
# The Hardy ↔ fast-growing bridge: `f_α ≤ H_{ω^α}`

The Cichoń identity (`Logic/Goodstein/Growth.lean`) gives
`goodsteinLength m = H_{toONote 2 m}(2) − 2`. To turn that into "Goodstein grows like the
fast-growing hierarchy" we relate the Hardy hierarchy `H_α` to the fast-growing hierarchy
`f_α`. The classical identity `H_{ω^α} = f_α` holds under the `ω[n]=n` convention; mathlib uses
`ω[n] = n+1`, which makes `H_{ω^α}` strictly *bigger*, so we prove the robust one-sided bound

  `fastGrowing α n ≤ hardy (oadd α 1 0) n`   (`fastGrowing_le_hardy_pow`).

The linchpin is the **Hardy iteration law** `H_{ω^e·(k+1)} = (H_{ω^e})^[k+1]`
(`hardy_oadd_iter`), whose engine is the **leading-term split**
`H_{ω^e·c + R}(n) = H_{ω^e·c}(H_R(n))` (`hardy_split`) — valid because the `NF` condition
`repr R < ω^(repr e)` is exactly the no-absorption side condition the Hardy additive law needs.
-/



/-- **Iterate domination.** If `f ≤ g` pointwise and `g` is monotone, then `f^[j] ≤ g^[j]`
pointwise. -/
theorem iterate_le_iterate {f g : ℕ → ℕ} (hfg : ∀ m, f m ≤ g m) (hg : Monotone g) :
    ∀ j x, f^[j] x ≤ g^[j] x := by
  intro j
  induction j with
  | zero => intro x; simp
  | succ j ih =>
    intro x
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    exact (ih (f x)).trans ((hg.iterate j) (hfg x))

/-- `(· + 1)^[j] n = n + j`. -/
theorem succ_iterate (j n : ℕ) : (fun m => m + 1)^[j] n = n + j := by
  induction j with
  | zero => simp
  | succ j ih => simp only [Function.iterate_succ_apply', ih]; omega

/-- **Leading-term split for the Hardy hierarchy.** For a normal-form notation `oadd e c R`
(so `repr R < ω^(repr e)`), the Hardy function splits its leading Cantor term off the tail:
`H_{ω^e·c + R}(n) = H_{ω^e·c}(H_R(n))`. Well-founded recursion on `repr R`. The `NF` hypothesis
is the no-absorption side condition that makes the Hardy additive law hold. -/
theorem hardy_split (e : ONote) (c : ℕ+) (R : ONote) (hNF : (oadd e c R).NF) (n : ℕ) :
    hardy (oadd e c R) n = hardy (oadd e c 0) (hardy R n) := by
  suffices H : ∀ o : Ordinal, ∀ R : ONote, R.repr = o → (oadd e c R).NF → ∀ n,
      hardy (oadd e c R) n = hardy (oadd e c 0) (hardy R n) by
    exact H R.repr R rfl hNF n
  intro o
  induction o using WellFoundedLT.induction with
  | _ o ih =>
    intro R hrepr hNFR n
    have hNFe : e.NF := hNFR.fst
    have hbelowR : R.repr < ω ^ e.repr := hNFR.snd'.repr_lt
    rcases hfs : fundamentalSequence R with (_ | R') | g
    · -- R = 0
      have hR0 : R = 0 :=
        (fundamentalSequenceProp_inl_none R).1 (hfs ▸ fundamentalSequence_has_prop R)
      subst hR0
      simp
    · -- R successor R'
      have hsucc := (fundamentalSequenceProp_inl_some R R').1 (hfs ▸ fundamentalSequence_has_prop R)
      have hNFR' : R'.NF := hsucc.2 hNFR.snd
      have hltR' : R'.repr < o := by rw [← hrepr, hsucc.1]; exact Order.lt_succ _
      have hbelowR' : R'.repr < ω ^ e.repr :=
        lt_trans (by rw [hrepr]; exact hltR') hbelowR
      have hNFnew : (oadd e c R').NF := NF.oadd hNFe c (NF.below_of_lt' hbelowR' hNFR')
      have hfsnew : fundamentalSequence (oadd e c R) = Sum.inl (some (oadd e c R')) := by
        rw [fundamentalSequence, hfs]
      simp only [hardy_succ _ hfsnew, hardy_succ _ hfs]
      exact ih R'.repr hltR' R' rfl hNFnew (n + 1)
    · -- R limit g
      have hprop := hfs ▸ fundamentalSequence_has_prop R
      have hgnlt : (g n).repr < o := by rw [← hrepr]; exact repr_lt_repr (hprop.2.1 n).2.1
      have hNFgn : (g n).NF := (hprop.2.1 n).2.2 hNFR.snd
      have hbelowgn : (g n).repr < ω ^ e.repr :=
        lt_trans (by rw [hrepr]; exact hgnlt) hbelowR
      have hNFnew : (oadd e c (g n)).NF := NF.oadd hNFe c (NF.below_of_lt' hbelowgn hNFgn)
      have hfsnew : fundamentalSequence (oadd e c R) = Sum.inr (fun i => oadd e c (g i)) := by
        rw [fundamentalSequence, hfs]
      simp only [hardy_limit _ hfsnew, hardy_limit _ hfs]
      exact ih (g n).repr hgnlt (g n) rfl hNFnew n

/-- Finite Hardy values: `H_{j+1}(n) = n + (j+1)` (the notation `oadd 0 ⟨j+1⟩ 0`). -/
theorem hardy_finite : ∀ j n, hardy (oadd 0 ⟨j + 1, Nat.succ_pos j⟩ 0) n = n + (j + 1) := by
  intro j
  induction j with
  | zero =>
    intro n
    show hardy (oadd 0 1 0) n = n + 1
    rw [show (oadd (0 : ONote) 1 0) = 1 from rfl, hardy_one]
  | succ j ih =>
    intro n
    have hfs : fundamentalSequence (oadd 0 ⟨j + 2, Nat.succ_pos _⟩ 0)
        = Sum.inl (some (oadd 0 ⟨j + 1, Nat.succ_pos j⟩ 0)) := by
      rw [fundamentalSequence_oadd_zero_zero]; rfl
    simp only [hardy_succ _ hfs]
    rw [ih (n + 1)]; omega

/-- **Hardy coefficient step (nonzero exponent).** For `e ≠ 0`,
`H_{ω^e·(k+2)}(n) = H_{ω^e·(k+1)}(H_{ω^e}(n))`. The descent peels one coefficient
(`fundSeq_oadd_coeff`), then `hardy_split` separates the freshly-created lowest term, whose
Hardy value is exactly `H_{ω^e}(n)` (it is the index-`n` fundamental term of `ω^e`). -/
theorem hardy_oadd_coeff_step_ne (e : ONote) (he : e ≠ 0) (hNFe : e.NF) (k n : ℕ) :
    hardy (oadd e ⟨k + 2, Nat.succ_pos _⟩ 0) n
      = hardy (oadd e ⟨k + 1, Nat.succ_pos k⟩ 0) (hardy (oadd e 1 0) n) := by
  obtain ⟨g, hg1, hgk⟩ := fundSeq_oadd_coeff e he k
  have hNFe1 : (oadd e 1 0).NF := NF.oadd hNFe 1 NFBelow.zero
  have hprop := hg1 ▸ fundamentalSequence_has_prop (oadd e 1 0)
  have hgnlt : (g n).repr < (oadd e 1 0).repr := repr_lt_repr (hprop.2.1 n).2.1
  have hNFgn : (g n).NF := (hprop.2.1 n).2.2 hNFe1
  have hbelow : (g n).repr < ω ^ e.repr := by
    have he1 : (oadd e 1 0).repr = ω ^ e.repr := by simp
    rwa [he1] at hgnlt
  have hNFsplit : (oadd e k.succPNat (g n)).NF :=
    NF.oadd hNFe _ (NF.below_of_lt' hbelow hNFgn)
  simp only [hardy_limit _ hgk]
  show hardy (oadd e k.succPNat (g n)) n
      = hardy (oadd e k.succPNat 0) (hardy (oadd e 1 0) n)
  rw [hardy_split e k.succPNat (g n) hNFsplit n]
  have heq : hardy (oadd e 1 0) n = hardy (g n) n := by simp only [hardy_limit _ hg1]
  rw [heq]

/-- **The Hardy iteration law.** `H_{ω^e·(k+1)} = (H_{ω^e})^[k+1]`. For `e = 0` this is
`H_{k+1}(n) = n+(k+1) = (·+1)^[k+1] n`; for `e ≠ 0` it is induction on `k` via the coefficient
step `hardy_oadd_coeff_step_ne`. The linchpin tying Hardy coefficients to iteration. -/
theorem hardy_oadd_iter (e : ONote) (hNFe : e.NF) :
    ∀ k n, hardy (oadd e ⟨k + 1, Nat.succ_pos k⟩ 0) n = (hardy (oadd e 1 0))^[k + 1] n := by
  rcases eq_or_ne e 0 with rfl | he
  · -- e = 0
    have hg : hardy (oadd (0 : ONote) 1 0) = fun n => n + 1 := by
      rw [show (oadd (0 : ONote) 1 0) = 1 from rfl]; exact hardy_one
    intro k n
    rw [hardy_finite k n, hg, succ_iterate]
  · -- e ≠ 0: induction on k via the coefficient step
    intro k
    induction k with
    | zero => intro n; simp
    | succ k ih =>
      intro n
      have hcoeff := hardy_oadd_coeff_step_ne e he hNFe k n
      have hk2 : (⟨k + 1 + 1, Nat.succ_pos (k + 1)⟩ : ℕ+) = ⟨k + 2, Nat.succ_pos _⟩ := rfl
      rw [hk2, hcoeff, ih (hardy (oadd e 1 0) n), ← Function.iterate_succ_apply]

/-- **The Hardy ↔ fast-growing bridge.** `fastGrowing α n ≤ hardy (oadd α 1 0) n`, i.e.
`f_α ≤ H_{ω^α}`. Well-founded recursion on `repr α`: base/limit are direct; the successor case
`f_{α'+1}(n) = (f_{α'})^[n](n)` is dominated by `(H_{ω^{α'}})^[n+1](n) = H_{ω^{α'+1}}(n)` via the
iteration law, the IH lifted through `iterate_le_iterate`, and one extra expansive iterate. -/
theorem fastGrowing_le_hardy_pow (α : ONote) (hNF : α.NF) (n : ℕ) :
    fastGrowing α n ≤ hardy (oadd α 1 0) n := by
  suffices H : ∀ o : Ordinal, ∀ α : ONote, α.repr = o → α.NF → ∀ n,
      fastGrowing α n ≤ hardy (oadd α 1 0) n by
    exact H α.repr α rfl hNF n
  intro o
  induction o using WellFoundedLT.induction with
  | _ o ih =>
    intro α hrepr hNFα n
    rcases hfs : fundamentalSequence α with (_ | α') | g
    · -- α = 0
      have hα0 : α = 0 :=
        (fundamentalSequenceProp_inl_none α).1 (hfs ▸ fundamentalSequence_has_prop α)
      subst hα0
      rw [fastGrowing_zero' 0 rfl]
      show Nat.succ n ≤ hardy (oadd 0 1 0) n
      rw [show (oadd (0 : ONote) 1 0) = 1 from rfl, hardy_one]
    · -- α successor α'
      have hsucc := (fundamentalSequenceProp_inl_some α α').1 (hfs ▸ fundamentalSequence_has_prop α)
      have hNFα' : α'.NF := hsucc.2 hNFα
      have hltα' : α'.repr < o := by rw [← hrepr, hsucc.1]; exact Order.lt_succ _
      rw [fastGrowing_succ α hfs]
      simp only [hardy_limit _ (fundSeq_oadd_one_of_succ hfs)]
      show (fastGrowing α')^[n] n ≤ hardy (oadd α' n.succPNat 0) n
      rw [show (n.succPNat : ℕ+) = ⟨n + 1, Nat.succ_pos n⟩ from rfl, hardy_oadd_iter α' hNFα' n n]
      calc (fastGrowing α')^[n] n
          ≤ (hardy (oadd α' 1 0))^[n] n :=
            iterate_le_iterate (fun m => ih α'.repr hltα' α' rfl hNFα' m) (hardy_monotone _) n n
        _ ≤ (hardy (oadd α' 1 0))^[n + 1] n := by
            rw [Function.iterate_succ_apply']
            exact le_hardy (oadd α' 1 0) _
    · -- α limit g
      have hprop := hfs ▸ fundamentalSequence_has_prop α
      have hgnlt : (g n).repr < o := by rw [← hrepr]; exact repr_lt_repr (hprop.2.1 n).2.1
      have hNFgn : (g n).NF := (hprop.2.1 n).2.2 hNFα
      rw [fastGrowing_limit α hfs]
      simp only [hardy_limit _ (fundSeq_oadd_one_of_limit hfs)]
      show fastGrowing (g n) n ≤ hardy (oadd (g n) 1 0) n
      exact ih (g n).repr hgnlt (g n) rfl hNFgn n

/-- **`toOrdinal 2` is cofinal below ε₀.** Every notation `β` is eventually exceeded by some
`toOrdinal 2 N` — the Goodstein ordinals `repr (toONote 2 m)` reach arbitrarily high below ε₀.
Structural induction on `β`: for `oadd e c r`, `repr β < ω^(repr e + 1) ≤ ω^(toOrdinal 2 Ne)
= toOrdinal 2 (2^Ne)` using `toOrdinal_pow` and the IH on the exponent `e`. -/
theorem toOrdinal_two_cofinal : ∀ β : ONote, β.NF → ∃ N : ℕ, β.repr < toOrdinal 2 N := by
  intro β
  induction β with
  | zero =>
    intro _
    refine ⟨1, ?_⟩
    have h1 : toOrdinal 2 1 = 1 := by have h := toOrdinal_pow 2 le_rfl 0; simpa using h
    have h0 : (ONote.zero : ONote).repr = 0 := rfl
    rw [h0, h1]; exact zero_lt_one
  | oadd e c r ihe _ =>
    intro hNF
    obtain ⟨Ne, hNe⟩ := ihe hNF.fst
    refine ⟨2 ^ Ne, ?_⟩
    have hbound : (oadd e c r).repr < ω ^ (e.repr + 1) := by
      have h := (NF.below_of_lt (b := e.repr + 1)
        (by rw [← Order.succ_eq_add_one]; exact Order.lt_succ _) hNF).repr_lt
      exact h
    have hle : e.repr + 1 ≤ toOrdinal 2 Ne := by
      rw [← Order.succ_eq_add_one]; exact Order.succ_le_of_lt hNe
    calc (oadd e c r).repr < ω ^ (e.repr + 1) := hbound
      _ ≤ ω ^ toOrdinal 2 Ne := opow_le_opow_right omega0_pos hle
      _ = toOrdinal 2 (2 ^ Ne) := (toOrdinal_pow 2 le_rfl Ne).symm

/-! ### A linear lower bound on the Goodstein length

`goodsteinLength m ≥ m`: a concrete (citable) growth lower bound, and sub-fact (i) toward the
full domination headline (it makes the high-budget step `j = m-2` of the telescope available).
The engine is `le_bump` (the hereditary bump never decreases its argument), which gives
`G_{k+1} = bump(..) − 1 ≥ G_k − 1`, hence `G_k ≥ m − k`, so `G_k ≠ 0` for `k < m`. -/

/-- **The hereditary bump never decreases:** `n ≤ bump b n` for `b ≥ 2`. Reading `n` in
hereditary base `b` and replacing `b` by `b+1` can only grow each digit's place value. Strong
induction mirroring `bump`'s recursion: `(b+1)^(bump b L) ≥ b^L` (via the IH `L ≤ bump b L`). -/
theorem le_bump (b : ℕ) (hb : 2 ≤ b) : ∀ n, n ≤ bump b n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · rw [bump_pos b n hn]
      set L := Nat.log b n with hL
      have hbe_pos : 0 < b ^ L := Nat.pow_pos (by omega)
      have hbe_le : b ^ L ≤ n := Nat.pow_log_le_self b hn
      have hlog : L < n := Nat.log_lt_self b hn
      have hr_lt : n % b ^ L < n := lt_of_lt_of_le (Nat.mod_lt _ hbe_pos) hbe_le
      have h1 : b ^ L ≤ (b + 1) ^ bump b L :=
        calc b ^ L ≤ (b + 1) ^ L := Nat.pow_le_pow_left (by omega) L
          _ ≤ (b + 1) ^ bump b L := Nat.pow_le_pow_right (by omega) (ih L hlog)
      have h2 : n % b ^ L ≤ bump b (n % b ^ L) := ih _ hr_lt
      have key : n / b ^ L * b ^ L + n % b ^ L
          ≤ n / b ^ L * (b + 1) ^ bump b L + bump b (n % b ^ L) := by gcongr
      have hdm : n / b ^ L * b ^ L + n % b ^ L = n := Nat.div_add_mod' n (b ^ L)
      omega

/-- **`bump` is monotone in its argument** (for `b ≥ 2`): `a ≤ a' → bump b a ≤ bump b a'`. The
hereditary base-`b` rewriting preserves order. *Proof via the ordinal bridge*, avoiding any direct
induction on the recursive `bump`: `toOrdinal b` is strictly monotone (`toOrdinal_mono_and_bound`),
and bumping is ordinal-invariant (`toOrdinal_bump : toOrdinal (b+1) (bump b n) = toOrdinal b n`), so
`a ≤ a'` lifts to `toOrdinal (b+1) (bump b a) = toOrdinal b a ≤ toOrdinal b a' =
toOrdinal (b+1) (bump b a')`, and strict monotonicity of `toOrdinal (b+1)` reflects this back to
`bump b a ≤ bump b a'`. This is the missing comparison lemma behind the **self-similarity recursion**
(`leadExp_ge_goodsteinSeq_log`): the leading-exponent sequence dominates a lower-level Goodstein
sequence, the structural heart of Cichoń's lower bound. -/
theorem bump_mono (b : ℕ) (hb : 2 ≤ b) {a a' : ℕ} (h : a ≤ a') : bump b a ≤ bump b a' := by
  have hSMb : StrictMono (toOrdinal b) := fun x y hxy =>
    (toOrdinal_mono_and_bound b hb y).1 x hxy
  have hSMb1 : StrictMono (toOrdinal (b + 1)) := fun x y hxy =>
    (toOrdinal_mono_and_bound (b + 1) (by omega) y).1 x hxy
  have hle : toOrdinal (b + 1) (bump b a) ≤ toOrdinal (b + 1) (bump b a') := by
    rw [toOrdinal_bump b hb, toOrdinal_bump b hb]; exact hSMb.monotone h
  exact hSMb1.le_iff_le.1 hle

/-- Each Goodstein term is at least `m − k` (truncated): `m − k ≤ goodsteinSeq m k`. Induction
on `k` using `le_bump` (`G_{k+1} = bump(base k, G_k) − 1 ≥ G_k − 1`). -/
theorem goodsteinSeq_ge_sub (m : ℕ) : ∀ k, m - k ≤ goodsteinSeq m k := by
  intro k
  induction k with
  | zero => have h0 : goodsteinSeq m 0 = m := rfl; omega
  | succ k ih =>
    have hb : goodsteinSeq m k ≤ bump (base k) (goodsteinSeq m k) :=
      le_bump (base k) (Nat.le_add_left 2 k) _
    show m - (k + 1) ≤ bump (base k) (goodsteinSeq m k) - 1
    omega

/-- **Goodstein length grows at least linearly:** `m ≤ goodsteinLength m`. Since
`goodsteinSeq m k ≥ m − k ≥ 1` for every `k < m`, the sequence is nonzero before step `m`, so its
first zero is at step `≥ m`. -/
theorem le_goodsteinLength (m : ℕ) : m ≤ goodsteinLength m := by
  rw [goodsteinLength, Nat.le_find_iff]
  intro k hk
  have hge := goodsteinSeq_ge_sub m k
  omega

/-! ### Growth: the Goodstein term stays `≥ m` for the first `m` steps

The linear bound `goodsteinSeq m k ≥ m − k` above only certifies *non-vanishing*; it says nothing
about growth. The genuine engine of Goodstein growth is that, **while the value is at least the
current base, one bump step does not decrease it** (`bump b n ≥ n + 1` for `n ≥ b` — the leading
power `b^L` strictly grows to `(b+1)^{bump b L} > b^L`, dominating the `−1`). Since the start value
`m` exceeds the base `k+2` for all `k ≤ m−2`, the sequence is non-decreasing across that whole
range, hence stays `≥ m`. Consequently the descent ordinal `seqOrd m j` stays `≥ ω` for the first
`~m` steps — the first "ordinal-stays-high" lower bound, and exactly sub-fact (ii) at level `o = 1`. -/

/-- **Strict growth above the base.** For `2 ≤ b` and `b ≤ n`, one bump step strictly increases
the value: `n + 1 ≤ bump b n`. The leading power `b^L` (with `L = log b n ≥ 1`) is sent to
`(b+1)^{bump b L} ≥ (b+1)^L > b^L`, so the leading term alone already exceeds `n`. -/
theorem bump_gt (b : ℕ) (hb : 2 ≤ b) {n : ℕ} (hn : b ≤ n) : n + 1 ≤ bump b n := by
  have hb1 : 1 < b := by omega
  have hn0 : n ≠ 0 := by omega
  set L := Nat.log b n with hL
  have hL1 : 1 ≤ L := Nat.log_pos hb1 hn
  have hbe_pos : 0 < b ^ L := Nat.pow_pos (by omega)
  have hbe_le : b ^ L ≤ n := Nat.pow_log_le_self b hn0
  have hq1 : 1 ≤ n / b ^ L := Nat.div_pos hbe_le hbe_pos
  have hpow_lt : b ^ L < (b + 1) ^ L := Nat.pow_lt_pow_left (by omega) (by omega)
  have hpow_le : (b + 1) ^ L ≤ (b + 1) ^ bump b L :=
    Nat.pow_le_pow_right (by omega) (le_bump b hb L)
  have hP : b ^ L + 1 ≤ (b + 1) ^ bump b L := by omega
  have hr_le : n % b ^ L ≤ bump b (n % b ^ L) := le_bump b hb _
  have hbump : bump b n = n / b ^ L * (b + 1) ^ bump b L + bump b (n % b ^ L) := bump_pos b n hn0
  have hn_eq : n / b ^ L * b ^ L + n % b ^ L = n := Nat.div_add_mod' n (b ^ L)
  set q := n / b ^ L with hq
  set BL := b ^ L with hBL
  set P := (b + 1) ^ bump b L with hPdef
  have hmul : q * (BL + 1) ≤ q * P := by gcongr
  have hexp : q * (BL + 1) = q * BL + q := by ring
  rw [hbump]
  omega

/-- **The leading exponent bumps itself.** `Nat.log (b+1) (bump b n) = bump b (Nat.log b n)`:
reading `bump b n` in the new base `b+1`, its leading exponent is the bump of `n`'s leading
exponent. The recursive skeleton behind Goodstein growth — the *exponent* evolves like a
lower-level Goodstein term, which is why the descent ordinal's leading CNF exponent stays high for
astronomically many steps. (Extracted from the `hlog` step of `toOrdinal_bump`.) -/
theorem log_bump (b : ℕ) (hb : 2 ≤ b) {n : ℕ} (hn : n ≠ 0) :
    Nat.log (b + 1) (bump b n) = bump b (Nat.log b n) := by
  have hb1 : 1 < b := by omega
  set e := Nat.log b n with he
  have hbe_pos : 0 < b ^ e := Nat.pow_pos (by omega)
  have hbe_le : b ^ e ≤ n := Nat.pow_log_le_self b hn
  have hc_pos : 0 < n / b ^ e := Nat.div_pos hbe_le hbe_pos
  have hc_lt : n / b ^ e < b := by
    rw [Nat.div_lt_iff_lt_mul hbe_pos, ← pow_succ']; exact Nat.lt_pow_succ_log_self hb1 n
  have hr_lt : n % b ^ e < b ^ e := Nat.mod_lt _ hbe_pos
  have hR_lt : bump b (n % b ^ e) < (b + 1) ^ bump b e := bump_lt_pow b hb hr_lt
  have hbump_eq : bump b n = n / b ^ e * (b + 1) ^ bump b e + bump b (n % b ^ e) := bump_pos b n hn
  rw [hbump_eq]
  apply Nat.log_eq_of_pow_le_of_lt_pow
  · calc (b + 1) ^ bump b e = 1 * (b + 1) ^ bump b e := (one_mul _).symm
      _ ≤ n / b ^ e * (b + 1) ^ bump b e := Nat.mul_le_mul_right _ hc_pos
      _ ≤ n / b ^ e * (b + 1) ^ bump b e + bump b (n % b ^ e) := Nat.le_add_right _ _
  · calc n / b ^ e * (b + 1) ^ bump b e + bump b (n % b ^ e)
        < n / b ^ e * (b + 1) ^ bump b e + (b + 1) ^ bump b e := Nat.add_lt_add_left hR_lt _
      _ = (n / b ^ e + 1) * (b + 1) ^ bump b e := by ring
      _ ≤ (b + 1) * (b + 1) ^ bump b e := Nat.mul_le_mul_right _ (by omega)
      _ = (b + 1) ^ (bump b e + 1) := by rw [pow_succ]; ring

/-- **The leading exponent does NOT drop at a non-pure-power step.** If `n` is *not* a pure power of
`b` — i.e. `b ^ log_b n < n`, equivalently `n` has a leading coefficient `≥ 2` or a nonzero lower
remainder — then the Goodstein `−1` is absorbed by the lower terms and the leading exponent is
exactly preserved across the step:
`Nat.log (b+1) (bump b n − 1) = bump b (Nat.log b n)` (the same value `log_bump` gives for `bump b n`
itself). The reason: `bump b n = c·(b+1)^{bump b e} + R` with `c ≥ 1`, `R < (b+1)^{bump b e}`, and the
not-a-pure-power hypothesis forces `bump b n > (b+1)^{bump b e}`, so subtracting `1` cannot cross the
power boundary. (When `n = b^{log_b n}` is a pure power the log *does* drop by one — the rare "borrow"
event.) **This is the structural reason leading-exponent drops are RARE** — they occur only at the
pure-power boundaries — and is the first brick of the steps-between-drops recursion that would upgrade
the domination budget `log₂ m → m` (closing the diagonal `f_o(m) ≤ goodsteinLength m`). -/
theorem log_bump_pred_of_not_pow (b : ℕ) (hb : 2 ≤ b) {n : ℕ} (hn : n ≠ 0)
    (hnp : b ^ Nat.log b n < n) :
    Nat.log (b + 1) (bump b n - 1) = bump b (Nat.log b n) := by
  have hb1 : 1 < b := by omega
  set e := Nat.log b n with he
  have hbe_pos : 0 < b ^ e := Nat.pow_pos (by omega)
  have hbe_le : b ^ e ≤ n := Nat.pow_log_le_self b hn
  have hc_pos : 0 < n / b ^ e := Nat.div_pos hbe_le hbe_pos
  have hr_lt : n % b ^ e < b ^ e := Nat.mod_lt _ hbe_pos
  have hR_lt : bump b (n % b ^ e) < (b + 1) ^ bump b e := bump_lt_pow b hb hr_lt
  have hbump_eq : bump b n = n / b ^ e * (b + 1) ^ bump b e + bump b (n % b ^ e) := bump_pos b n hn
  have hP_pos : 0 < (b + 1) ^ bump b e := Nat.pow_pos (by omega)
  -- the not-a-pure-power hypothesis: leading coeff `≥ 2`, or nonzero remainder
  have hcase : 2 ≤ n / b ^ e ∨ 0 < n % b ^ e := by
    rcases Nat.eq_zero_or_pos (n % b ^ e) with hr0 | hrpos
    · left
      have key : b ^ e * (n / b ^ e) + n % b ^ e = n := Nat.div_add_mod n (b ^ e)
      rcases Nat.lt_or_ge (n / b ^ e) 2 with hlt | hge
      · have hc1 : n / b ^ e = 1 := by omega
        rw [hc1, hr0, mul_one, add_zero] at key
        omega
      · exact hge
    · right; exact hrpos
  -- hence `bump b n > (b+1)^{bump b e}`, so the `−1` does not cross the power boundary
  have hgt : (b + 1) ^ bump b e < bump b n := by
    rcases hcase with hc2 | hrpos
    · have h2P : 2 * (b + 1) ^ bump b e ≤ n / b ^ e * (b + 1) ^ bump b e := by gcongr
      rw [hbump_eq]; omega
    · have hR1 : 1 ≤ bump b (n % b ^ e) := le_trans hrpos (le_bump b hb _)
      have hPle : (b + 1) ^ bump b e ≤ n / b ^ e * (b + 1) ^ bump b e := by
        conv_lhs => rw [← one_mul ((b + 1) ^ bump b e)]
        gcongr; omega
      rw [hbump_eq]; omega
  apply Nat.log_eq_of_pow_le_of_lt_pow
  · omega
  · have hub : bump b n < (b + 1) ^ (bump b e + 1) := by
      calc bump b n = n / b ^ e * (b + 1) ^ bump b e + bump b (n % b ^ e) := hbump_eq
        _ < n / b ^ e * (b + 1) ^ bump b e + (b + 1) ^ bump b e := by omega
        _ = (n / b ^ e + 1) * (b + 1) ^ bump b e := by ring
        _ ≤ (b + 1) * (b + 1) ^ bump b e := by
            apply Nat.mul_le_mul_right
            have hc_lt : n / b ^ e < b := by
              rw [Nat.div_lt_iff_lt_mul hbe_pos, ← pow_succ']; exact Nat.lt_pow_succ_log_self hb1 n
            omega
        _ = (b + 1) ^ (bump b e + 1) := by rw [pow_succ]; ring
    omega

/-- **The leading exponent drops by exactly one at a pure-power step** (the rare "borrow" event).
If `n = b ^ log_b n` is a pure power with `log_b n ≥ 1`, then `bump b n = (b+1)^{bump b (log_b n)}`
exactly (coefficient `1`, no lower terms), so the Goodstein `−1` borrows from the top and the leading
exponent decrements:
`Nat.log (b+1) (bump b n − 1) = bump b (Nat.log b n) − 1`.
Together with `log_bump_pred_of_not_pow` (no drop off the pure-power boundaries) this is the complete
per-step behaviour of the leading exponent: it bumps itself and grows everywhere except at the pure
powers, where it falls by exactly one. The steps-between-drops recursion = the gaps between these
pure-power events, each itself a sub-Goodstein-length. -/
theorem log_bump_pred_of_pow (b : ℕ) (hb : 2 ≤ b) {n : ℕ}
    (he1 : 1 ≤ Nat.log b n) (hnp : n = b ^ Nat.log b n) :
    Nat.log (b + 1) (bump b n - 1) = bump b (Nat.log b n) - 1 := by
  have hb1 : 1 < b := by omega
  set e := Nat.log b n with he
  have hbe_pos : 0 < b ^ e := Nat.pow_pos (by omega)
  have hn0 : n ≠ 0 := by rw [hnp]; positivity
  have hbump_eq : bump b n = n / b ^ e * (b + 1) ^ bump b e + bump b (n % b ^ e) := bump_pos b n hn0
  have hdiv : n / b ^ e = 1 := by rw [hnp]; exact Nat.div_self hbe_pos
  have hmod : n % b ^ e = 0 := by rw [hnp]; exact Nat.mod_self _
  have hb0 : bump b 0 = 0 := by rw [bump]; simp
  rw [hdiv, hmod, one_mul, hb0, add_zero] at hbump_eq
  set B := bump b e with hB
  have hB1 : 1 ≤ B := le_trans he1 (le_bump b hb e)
  have hbp_pos : 0 < (b + 1) ^ B := Nat.pow_pos (by omega)
  rw [hbump_eq]
  apply Nat.log_eq_of_pow_le_of_lt_pow
  · have hlt : (b + 1) ^ (B - 1) < (b + 1) ^ B := Nat.pow_lt_pow_right (by omega) (by omega)
    omega
  · have hBeq : (B - 1) + 1 = B := by omega
    rw [hBeq]; omega

/-- **Decrementing lowers a logarithm by at most one:** `Nat.log b x ≤ Nat.log b (x − 1) + 1`
(for `1 < b`). If `L = log b x ≥ 1` then `b^L ≤ x`, so `b^(L−1) < b^L ≤ x`, hence `b^(L−1) ≤ x−1`
and `L − 1 ≤ log b (x − 1)`. The general fact that a single decrement crosses at most one power. -/
theorem log_le_log_pred_succ (b : ℕ) (hb : 1 < b) (x : ℕ) :
    Nat.log b x ≤ Nat.log b (x - 1) + 1 := by
  rcases Nat.eq_zero_or_pos (Nat.log b x) with hL0 | hLpos
  · omega
  · have hx0 : x ≠ 0 := by
      intro h; rw [h, Nat.log_zero_right] at hLpos; exact Nat.lt_irrefl 0 hLpos
    have hbL : b ^ Nat.log b x ≤ x := Nat.pow_log_le_self b hx0
    have hb1L : b ^ 1 ≤ b ^ Nat.log b x := Nat.pow_le_pow_right (by omega) hLpos
    have hge : b ≤ x := by rw [pow_one] at hb1L; omega
    have hx1 : x - 1 ≠ 0 := by omega
    have hpowlt : b ^ (Nat.log b x - 1) < b ^ Nat.log b x := Nat.pow_lt_pow_right hb (by omega)
    have hpow : b ^ (Nat.log b x - 1) ≤ x - 1 := by omega
    have := (Nat.le_log_iff_pow_le hb hx1).2 hpow
    omega

/-- **The leading CNF exponent drops by at most one per Goodstein step** (while the term is at
least its base). Reading the leading exponent `L_k = log_{base k}(G_k)`, the step gives
`L_k ≤ L_{k+1} + 1`: `log_bump` sends the exponent `L_k` to `bump (base k) L_k ≥ L_k` in the new
base, and the `− 1` in `G_{k+1} = bump _ G_k − 1` lowers that log by at most one
(`log_le_log_pred_succ`). This is the recursion's per-level skeleton: the leading exponent itself
descends Goodstein-style, so it cannot fall below a fixed level `o` until astronomically many
steps have passed — the structural reason sub-fact (ii) holds for every fixed `o`. -/
theorem leadExp_drop_le_one (m k : ℕ) (h : base k ≤ goodsteinSeq m k) :
    Nat.log (base k) (goodsteinSeq m k)
      ≤ Nat.log (base (k + 1)) (goodsteinSeq m (k + 1)) + 1 := by
  have hb : 2 ≤ base k := Nat.le_add_left 2 k
  have hv0 : goodsteinSeq m k ≠ 0 := by omega
  have hbb1 : base (k + 1) = base k + 1 := by simp only [base]
  have hstep : goodsteinSeq m (k + 1) = bump (base k) (goodsteinSeq m k) - 1 := rfl
  rw [hbb1, hstep]
  have h1 : Nat.log (base k + 1) (bump (base k) (goodsteinSeq m k))
      ≤ Nat.log (base k + 1) (bump (base k) (goodsteinSeq m k) - 1) + 1 :=
    log_le_log_pred_succ (base k + 1) (by omega) _
  have h2 : Nat.log (base k + 1) (bump (base k) (goodsteinSeq m k))
      = bump (base k) (Nat.log (base k) (goodsteinSeq m k)) := log_bump (base k) hb hv0
  have h3 : Nat.log (base k) (goodsteinSeq m k)
      ≤ bump (base k) (Nat.log (base k) (goodsteinSeq m k)) := le_bump (base k) hb _
  omega

/-- **The leading exponent is non-decreasing while it is itself `≥ base`** (the level-2 analog of
`goodsteinSeq_ge_init`). If `L_k = log_{base k}(G_k) ≥ base k` then `bump (base k) L_k ≥ L_k + 1`
(`bump_gt`), so even after the `−1`-induced log drop, `L_{k+1} ≥ L_k`. The same non-decrease
mechanism that keeps the *value* high keeps the *leading exponent* high — one level up. -/
theorem leadExp_ge_of_base_le (m k : ℕ)
    (h : base k ≤ Nat.log (base k) (goodsteinSeq m k)) :
    Nat.log (base k) (goodsteinSeq m k) ≤ Nat.log (base (k + 1)) (goodsteinSeq m (k + 1)) := by
  have hb : 2 ≤ base k := Nat.le_add_left 2 k
  have hv : goodsteinSeq m k ≠ 0 := by
    intro h0; rw [h0, Nat.log_zero_right] at h; omega
  have hbb1 : base (k + 1) = base k + 1 := by simp only [base]
  have hstep : goodsteinSeq m (k + 1) = bump (base k) (goodsteinSeq m k) - 1 := rfl
  rw [hbb1, hstep]
  have h2 : Nat.log (base k + 1) (bump (base k) (goodsteinSeq m k))
      = bump (base k) (Nat.log (base k) (goodsteinSeq m k)) := log_bump (base k) hb hv
  have hbg : Nat.log (base k) (goodsteinSeq m k) + 1
      ≤ bump (base k) (Nat.log (base k) (goodsteinSeq m k)) := bump_gt (base k) hb h
  have h1 : Nat.log (base k + 1) (bump (base k) (goodsteinSeq m k))
      ≤ Nat.log (base k + 1) (bump (base k) (goodsteinSeq m k) - 1) + 1 :=
    log_le_log_pred_succ (base k + 1) (by omega) _
  omega

/-- **The leading exponent is non-decreasing at every NON-pure-power step** — *unconditionally* (no
`≥ base` hypothesis, unlike `leadExp_ge_of_base_le`). If `G_k` is not a pure power of `base k`, then
`log_bump_pred_of_not_pow` preserves the leading exponent exactly (`L_{k+1} = bump (base k) L_k`) and
`le_bump` gives `L_k ≤ bump (base k) L_k = L_{k+1}`. So the leading exponent only ever *falls* at the
rare pure-power steps; everywhere else it stays or grows. This is the lemma that, once paired with a
bound on the number of pure-power events, lifts the `log₂ m`-step guarantee (`leadExp_ge_sub`, which
needs `L_k ≥ base k`) to the `m`-step guarantee the diagonal `f_o(m)` headline requires. -/
theorem leadExp_ge_of_not_pow (m k : ℕ)
    (hnp : base k ^ Nat.log (base k) (goodsteinSeq m k) < goodsteinSeq m k) :
    Nat.log (base k) (goodsteinSeq m k) ≤ Nat.log (base (k + 1)) (goodsteinSeq m (k + 1)) := by
  have hb : 2 ≤ base k := Nat.le_add_left 2 k
  have hv0 : goodsteinSeq m k ≠ 0 := by
    have : 0 < base k ^ Nat.log (base k) (goodsteinSeq m k) := Nat.pow_pos (by omega)
    omega
  have hbb1 : base (k + 1) = base k + 1 := by simp only [base]
  have hstep : goodsteinSeq m (k + 1) = bump (base k) (goodsteinSeq m k) - 1 := rfl
  rw [hbb1, hstep, log_bump_pred_of_not_pow (base k) hb hv0 hnp]
  exact le_bump (base k) hb _

/-- **`bump` fixes single digits:** `bump b n = n` for `n < b`. A value below its base is a single
base-`b` digit, so peeling the top power leaves it unchanged (no base substitution happens). The
mechanism that makes the leading exponent *flat* in the small regime (`leadExp < base`). -/
theorem bump_eq_of_lt (b n : ℕ) (h : n < b) : bump b n = n := by
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0; exact bump_zero b
  · have hlog : Nat.log b n = 0 :=
      Nat.log_eq_of_pow_le_of_lt_pow (by simp only [pow_zero]; exact hpos) (by simpa using h)
    have hbp := bump_pos b n (by omega)
    rw [hlog] at hbp
    simpa [Nat.mod_one] using hbp

/-- **The leading exponent is NON-INCREASING in the small regime** (`leadExp < base`). Below its
base, the leading exponent `e` is a single digit: off pure powers it bumps to itself (`bump_eq_of_lt`)
so `leadExp` is unchanged, and at a pure power it drops by exactly one (`log_bump_pred_of_pow`). So
once the descent enters the small regime, the leading exponent only ever falls — the qualitative
companion to `leadExp_ge_of_not_pow` (growth in the large regime). Together they pin the full leadExp
trajectory: grows while `≥ base`, monotonically decreases once `< base`. The `o = 2` difficulty lives
entirely in this small regime, where the (rare) pure-power drops are the only events. -/
theorem leadExp_small_nonincreasing (m k : ℕ) (hv0 : goodsteinSeq m k ≠ 0)
    (hsmall : Nat.log (base k) (goodsteinSeq m k) < base k) :
    Nat.log (base (k + 1)) (goodsteinSeq m (k + 1)) ≤ Nat.log (base k) (goodsteinSeq m k) := by
  have hb : 2 ≤ base k := Nat.le_add_left 2 k
  have hbb1 : base (k + 1) = base k + 1 := by simp only [base]
  have hstep : goodsteinSeq m (k + 1) = bump (base k) (goodsteinSeq m k) - 1 := rfl
  have hbeq : bump (base k) (Nat.log (base k) (goodsteinSeq m k))
      = Nat.log (base k) (goodsteinSeq m k) := bump_eq_of_lt (base k) _ hsmall
  by_cases hpp : base k ^ Nat.log (base k) (goodsteinSeq m k) = goodsteinSeq m k
  · -- pure power: the exponent drops by exactly one (or is already 0)
    rcases Nat.eq_zero_or_pos (Nat.log (base k) (goodsteinSeq m k)) with he0 | hepos
    · -- e = 0 ⟹ G_k = base^0 = 1 ⟹ G_{k+1} = bump _ 1 − 1 = 0 ⟹ leadExp = 0
      have hG1 : goodsteinSeq m k = 1 := by rw [← hpp, he0, pow_zero]
      rw [hbb1, hstep, hG1, bump_eq_of_lt (base k) 1 (by omega)]
      simp
    · -- e ≥ 1: log_bump_pred_of_pow gives bump (base k) e − 1; hbeq collapses bump (base k) e = e
      rw [hbb1, hstep, log_bump_pred_of_pow (base k) hb hepos hpp.symm]
      omega
  · -- not a pure power: the exponent bumps to itself (= e, since e < base k)
    have hlt : base k ^ Nat.log (base k) (goodsteinSeq m k) < goodsteinSeq m k := by
      have hle := Nat.pow_log_le_self (base k) hv0; omega
    rw [hbb1, hstep, log_bump_pred_of_not_pow (base k) hb hv0 hlt]
    omega

/-- **The Goodstein term stays `≥ m` for the first `m` steps:** `m ≤ goodsteinSeq m k` whenever
`k + 1 ≤ m`. Induction on `k` using `bump_gt`: while `k + 2 ≤ m ≤ goodsteinSeq m k` the value is
above the base, so `goodsteinSeq m (k+1) = bump (k+2) (goodsteinSeq m k) − 1 ≥ goodsteinSeq m k`. -/
theorem goodsteinSeq_ge_init (m : ℕ) : ∀ k, k + 1 ≤ m → m ≤ goodsteinSeq m k := by
  intro k
  induction k with
  | zero => intro _; exact le_of_eq rfl
  | succ k ih =>
    intro hk
    have hv : m ≤ goodsteinSeq m k := ih (by omega)
    have hble : k + 2 ≤ goodsteinSeq m k := by omega
    have hgt : goodsteinSeq m k + 1 ≤ bump (k + 2) (goodsteinSeq m k) :=
      bump_gt (k + 2) (by omega) hble
    have hbase : base k = k + 2 := rfl
    show m ≤ bump (base k) (goodsteinSeq m k) - 1
    rw [hbase]; omega

/-- **The ordinal of a numeral dominates `ω` raised to its leading-exponent ordinal:**
`ω ^ (toOrdinal b (Nat.log b v)) ≤ toOrdinal b v` (for `v ≠ 0`, `b ≥ 2`). Immediate from
`toOrdinal_pos`: the leading Cantor term is `ω ^ (…) · c` with digit `c ≥ 1`. The bridge from the
**leading exponent** (a natural number, controlled by `leadExp_ge_sub`) to the **descent ordinal**
(`seqOrd`), needed to turn `leadExp ≥ k` into `seqOrd ≥ ω^k`. -/
theorem opow_toOrdinal_log_le (b : ℕ) (hb : 2 ≤ b) {v : ℕ} (hv : v ≠ 0) :
    ω ^ toOrdinal b (Nat.log b v) ≤ toOrdinal b v := by
  rw [toOrdinal_pos b v hv]
  have hc : (1 : Ordinal) ≤ (v / b ^ Nat.log b v : ℕ) := by
    have h0 : 0 < v / b ^ Nat.log b v :=
      Nat.div_pos (Nat.pow_log_le_self b hv) (Nat.pow_pos (by omega))
    exact_mod_cast h0
  calc ω ^ toOrdinal b (Nat.log b v)
      = ω ^ toOrdinal b (Nat.log b v) * 1 := (mul_one _).symm
    _ ≤ ω ^ toOrdinal b (Nat.log b v) * (v / b ^ Nat.log b v : ℕ) := by gcongr
    _ ≤ ω ^ toOrdinal b (Nat.log b v) * (v / b ^ Nat.log b v : ℕ)
          + toOrdinal b (v % b ^ Nat.log b v) := le_self_add

/-- **From leading exponent to descent ordinal:** if the leading exponent `leadExp_i =
Nat.log (base i)(G_i)` is `≥ k` (and `k < base i`, so `k` reads as the ordinal `k`), then the
descent ordinal dominates `ω^k`: `ω^k ≤ (seqONote m i).repr`. Chains `opow_toOrdinal_log_le` with
`toOrdinal`-monotonicity of the exponent and `toOrdinal b k = k` for `k < b`. The general bridge
behind sub-fact (ii) at level `o = k` — combine with `leadExp_ge_sub`. -/
theorem opow_le_seqONote_repr {m i k : ℕ} (hk : k ≤ Nat.log (base i) (goodsteinSeq m i))
    (hv : goodsteinSeq m i ≠ 0) (hkb : k < base i) :
    (ω : Ordinal) ^ (k : Ordinal) ≤ (seqONote m i).repr := by
  have hb : 2 ≤ base i := Nat.le_add_left 2 i
  rw [repr_seqONote]
  show (ω : Ordinal) ^ (k : Ordinal) ≤ toOrdinal (base i) (goodsteinSeq m i)
  have htk : toOrdinal (base i) k = (k : Ordinal) := by
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · subst hk0; simp
    · have hlog0 : Nat.log (base i) k = 0 := Nat.log_eq_zero_iff.2 (Or.inl hkb)
      rw [toOrdinal_pos (base i) k (by omega), hlog0]
      simp [pow_zero, Nat.div_one, Nat.mod_one, toOrdinal_zero]
  have hmono : toOrdinal (base i) k
      ≤ toOrdinal (base i) (Nat.log (base i) (goodsteinSeq m i)) := by
    rcases eq_or_lt_of_le hk with h | h
    · rw [h]
    · exact le_of_lt ((toOrdinal_mono_and_bound (base i) hb _).1 k h)
  calc (ω : Ordinal) ^ (k : Ordinal) = ω ^ toOrdinal (base i) k := by rw [htk]
    _ ≤ ω ^ toOrdinal (base i) (Nat.log (base i) (goodsteinSeq m i)) :=
        opow_le_opow_right omega0_pos hmono
    _ ≤ toOrdinal (base i) (goodsteinSeq m i) := opow_toOrdinal_log_le (base i) hb hv

/-- **The descent ordinal stays `≥ ω` for the first `m` steps.** For `m = n + 2` and any step
`j ≤ n`, the term value is `≥ m ≥ base j = j + 2`, so its ordinal `seqOrd m j` is `≥ ω`. This is
sub-fact (ii) at level `o = 1`: the Goodstein notation `seqONote m j` dominates `ω = ω^(repr 1)`. -/
theorem omega_le_seqONote_repr {n j : ℕ} (hj : j ≤ n) :
    (ω : Ordinal) ≤ (seqONote (n + 2) j).repr := by
  have hmono_le : ∀ p q : ℕ, p ≤ q → toOrdinal (j + 2) p ≤ toOrdinal (j + 2) q := by
    intro p q hpq
    rcases eq_or_lt_of_le hpq with h | h
    · rw [h]
    · exact le_of_lt ((toOrdinal_mono_and_bound (j + 2) (by omega) q).1 p h)
  have h1 : toOrdinal (j + 2) 1 = 1 := by
    have h := toOrdinal_pow (j + 2) (by omega) 0; simpa using h
  have hbeq : toOrdinal (j + 2) (j + 2) = ω := by
    have h := toOrdinal_pow (j + 2) (by omega) 1
    rw [pow_one, h1, opow_one] at h; exact h
  have hval : j + 2 ≤ goodsteinSeq (n + 2) j := by
    have h := goodsteinSeq_ge_init (n + 2) j (by omega); omega
  rw [repr_seqONote]
  show (ω : Ordinal) ≤ toOrdinal (j + 2) (goodsteinSeq (n + 2) j)
  rw [← hbeq]; exact hmono_le (j + 2) _ hval

/-- **Telescoped leading-exponent lower bound:** `Nat.log 2 m ≤ leadExp_i + i` for `i + 1 ≤ m`,
i.e. `leadExp_i ≥ (log₂ m) − i`. The leading exponent starts at `log₂ m` and drops by `≤ 1` per
step (`leadExp_drop_le_one`, applicable since the value stays `≥` base over `[0, m)`). So the
descent ordinal keeps a leading exponent `≥ 2` — hence `seqOrd m i ≥ ω²` — for the first
`~log₂ m` steps. (The genuine `≫ m`-step persistence needs the steps-between-drops recursion.) -/
theorem leadExp_ge_sub (m : ℕ) : ∀ i, i + 1 ≤ m →
    Nat.log 2 m ≤ Nat.log (base i) (goodsteinSeq m i) + i := by
  intro i
  induction i with
  | zero => intro _; show Nat.log 2 m ≤ Nat.log 2 m + 0; omega
  | succ i ih =>
    intro hi
    have hib : base i ≤ goodsteinSeq m i := by
      have := goodsteinSeq_ge_init m i (by omega)
      simp only [base]; omega
    have hdrop := leadExp_drop_le_one m i hib
    have hih := ih (by omega)
    omega

/-- **Per-step leading-exponent floor (unconditional).** `bump (base k) L_k − 1 ≤ L_{k+1}`, writing
`L_k = Nat.log (base k) (goodsteinSeq m k)`. The next leading exponent is at least the *bump* of the
current one minus one: off pure powers it equals `bump (base k) L_k` (`log_bump_pred_of_not_pow`), at
pure powers exactly `bump (base k) L_k − 1` (`log_bump_pred_of_pow`), and when the value vanishes both
sides collapse to `0`. So the leading-exponent sequence obeys the Goodstein recursion (`bump` then
`−1`) as a *lower bound* — the engine of the self-similarity below. -/
theorem leadExp_step_ge (m k : ℕ) :
    bump (base k) (Nat.log (base k) (goodsteinSeq m k)) - 1
      ≤ Nat.log (base (k + 1)) (goodsteinSeq m (k + 1)) := by
  have hb : 2 ≤ base k := Nat.le_add_left 2 k
  have hbb1 : base (k + 1) = base k + 1 := by simp only [base]
  have hstep : goodsteinSeq m (k + 1) = bump (base k) (goodsteinSeq m k) - 1 := rfl
  rcases eq_or_ne (goodsteinSeq m k) 0 with hv0 | hv0
  · rw [hv0]; simp
  · by_cases hpp : base k ^ Nat.log (base k) (goodsteinSeq m k) = goodsteinSeq m k
    · rcases Nat.eq_zero_or_pos (Nat.log (base k) (goodsteinSeq m k)) with he0 | hepos
      · rw [he0, bump_zero]; omega
      · rw [hbb1, hstep, log_bump_pred_of_pow (base k) hb hepos hpp.symm]
    · have hlt : base k ^ Nat.log (base k) (goodsteinSeq m k) < goodsteinSeq m k := by
        have hle := Nat.pow_log_le_self (base k) hv0; omega
      rw [hbb1, hstep, log_bump_pred_of_not_pow (base k) hb hv0 hlt]; omega

/-- **Self-similarity: the leading-exponent sequence dominates a lower-level Goodstein sequence.**
`goodsteinSeq (Nat.log 2 m) k ≤ Nat.log (base k) (goodsteinSeq m k)` for every `k`. The leading
exponent `L_k` starts at `L_0 = Nat.log 2 m` and, by `leadExp_step_ge`, evolves by
`L_{k+1} ≥ bump (base k) L_k − 1` — *exactly* the Goodstein recursion (`bump` then `−1`), but with the
`−1` firing only at the rare pure powers, hence dominating the genuine Goodstein sequence seeded at
`Nat.log 2 m` (which subtracts `1` at every step). Monotonicity of `bump` (`bump_mono`) carries the
induction step. **This is Cichoń's lower bound in miniature**: it reduces the `o = 2` diagonal crux
(`leadExp_k ≥ 2` for `k ≤ m`) to the *one-level-smaller* length statement
`m + 2 ≤ goodsteinLength (Nat.log 2 m)` (see `two_le_leadExp_of_log_length`) — a clean self-reference
that powers a strong induction on `m`, replacing the `ppCount` sparsity bound as the frontier. -/
theorem leadExp_ge_goodsteinSeq_log (m : ℕ) :
    ∀ k, goodsteinSeq (Nat.log 2 m) k ≤ Nat.log (base k) (goodsteinSeq m k) := by
  intro k
  induction k with
  | zero =>
    have h0 : goodsteinSeq (Nat.log 2 m) 0 = Nat.log 2 m := rfl
    have h1 : goodsteinSeq m 0 = m := rfl
    have hb : base 0 = 2 := rfl
    simp [h0, h1, hb]
  | succ k ih =>
    have hb : 2 ≤ base k := Nat.le_add_left 2 k
    have hstepM : goodsteinSeq (Nat.log 2 m) (k + 1)
        = bump (base k) (goodsteinSeq (Nat.log 2 m) k) - 1 := rfl
    rw [hstepM]
    have hmono : bump (base k) (goodsteinSeq (Nat.log 2 m) k)
        ≤ bump (base k) (Nat.log (base k) (goodsteinSeq m k)) := bump_mono (base k) hb ih
    have hstep := leadExp_step_ge m k
    omega

/-- **A Goodstein term is `≥ 2` until two steps before it terminates.** If `k + 1 < goodsteinLength M`
then `2 ≤ goodsteinSeq M k`. The value is nonzero before the length (`goodsteinSeq_ne_zero_of_lt`); and
it cannot equal `1` there, because `bump b 1 = 1` so a value of `1` at step `k` forces `0` at step
`k + 1`, i.e. `goodsteinLength M ≤ k + 1` — contradicting `k + 1 < goodsteinLength M`. So the only `1`
is at step `goodsteinLength M − 1` and the only `0` at `goodsteinLength M`. -/
theorem two_le_goodsteinSeq (M k : ℕ) (h : k + 1 < goodsteinLength M) :
    2 ≤ goodsteinSeq M k := by
  have hne0 : goodsteinSeq M k ≠ 0 := goodsteinSeq_ne_zero_of_lt (by omega)
  rcases Nat.lt_or_ge (goodsteinSeq M k) 2 with hlt | hge
  · exfalso
    have h1 : goodsteinSeq M k = 1 := by omega
    have hbump1 : bump (base k) 1 = 1 := by rw [bump_pos (base k) 1 one_ne_zero]; simp
    have hnext : goodsteinSeq M (k + 1) = 0 := by
      show bump (base k) (goodsteinSeq M k) - 1 = 0
      rw [h1, hbump1]
    have := goodsteinLength_le hnext
    omega
  · exact hge

/-- **The self-similarity reduction, made explicit.** If the *one-level-down* Goodstein sequence runs
long enough — `m + 2 ≤ goodsteinLength (Nat.log 2 m)` — then the leading exponent of the seed-`m`
descent stays `≥ 2` for the first `m` steps: `2 ≤ Nat.log (base k) (goodsteinSeq m k)` for all `k ≤ m`.
Chains `leadExp_ge_goodsteinSeq_log` (`L_k ≥ goodsteinSeq (Nat.log 2 m) k`) with `two_le_goodsteinSeq`
(the lower sequence is `≥ 2` for `k + 1 < goodsteinLength (Nat.log 2 m)`, which `k ≤ m` guarantees).
This is exactly sub-fact (ii) at `o = 2`, *reduced* to the smaller length bound. -/
theorem two_le_leadExp_of_log_length {m k : ℕ}
    (hlen : m + 2 ≤ goodsteinLength (Nat.log 2 m)) (hk : k ≤ m) :
    2 ≤ Nat.log (base k) (goodsteinSeq m k) :=
  le_trans (two_le_goodsteinSeq (Nat.log 2 m) k (by omega)) (leadExp_ge_goodsteinSeq_log m k)

/-- **The pure-power step counter.** `ppCount m k` = the number of Goodstein steps among the first
`k` at which `G_i` is a pure power of its base `base i` (`G_i = (base i)^{log_{base i} G_i}`) — the
*rare* leading-exponent "borrow" events (see `log_bump_pred_of_pow` / `log_bump_pred_of_not_pow`). -/
def ppCount (m : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => ppCount m k +
      (if base k ^ Nat.log (base k) (goodsteinSeq m k) = goodsteinSeq m k then 1 else 0)

/-- **Sharpened telescope: the leading exponent only falls at pure-power steps.**
`Nat.log 2 m ≤ leadExp_k + ppCount m k`, i.e. `leadExp_k ≥ (log₂ m) − ppCount m k`. Strictly sharper
than `leadExp_ge_sub` (which bounds the deficit by `k`): the deficit is bounded by the number of
*pure-power* steps, which are rare. Proof by induction on `k` via the per-step dichotomy — at a
non-pure-power step the exponent is non-decreasing (`leadExp_ge_of_not_pow`, deficit unchanged) and at
a pure-power step it drops by `≤ 1` (`leadExp_drop_le_one`, deficit and `ppCount` both `+1`).

**This isolates the diagonal-domination crux to a single sparsity bound.** If a future lap proves
`ppCount m m ≤ Nat.log 2 m − 2` (the genuine steps-between-drops content: pure-power events are
`≪ log₂ m` among the first `m` steps), then `leadExp_k ≥ 2` for all `k ≤ m`, hence `seqONote m (m−2)
≥ ω²`, closing the `o = 2` diagonal `f_2(m) ≤ goodsteinLength m + 2` via `fastGrowing_step_le_goodsteinLength`
— and the general `o` analogously. The regime hypothesis (`value ≥ base` over `[0,k)`) is automatic
while the exponent stays `≥ 1`, supplied here by `goodsteinSeq_ge_init`. -/
theorem leadExp_ge_sub_ppCount (m : ℕ) : ∀ k, k + 1 ≤ m →
    Nat.log 2 m ≤ Nat.log (base k) (goodsteinSeq m k) + ppCount m k := by
  intro k
  induction k with
  | zero => intro _; show Nat.log 2 m ≤ Nat.log 2 m + ppCount m 0; simp [ppCount]
  | succ k ih =>
    intro hk
    have hvk : base k ≤ goodsteinSeq m k := by
      have := goodsteinSeq_ge_init m k (by omega); simp only [base]; omega
    have hv0 : goodsteinSeq m k ≠ 0 := by
      have : 2 ≤ base k := Nat.le_add_left 2 k; omega
    have ihk := ih (by omega)
    by_cases hpp : base k ^ Nat.log (base k) (goodsteinSeq m k) = goodsteinSeq m k
    · have hdrop := leadExp_drop_le_one m k hvk
      have hpc : ppCount m (k + 1) = ppCount m k + 1 := by simp [ppCount, hpp]
      omega
    · have hlt : base k ^ Nat.log (base k) (goodsteinSeq m k) < goodsteinSeq m k := by
        have hle := Nat.pow_log_le_self (base k) hv0
        omega
      have hge := leadExp_ge_of_not_pow m k hlt
      have hpc : ppCount m (k + 1) = ppCount m k := by simp [ppCount, hpp]
      omega

/-- **The descent ordinal reaches `ω^k` for the first `~log₂ m` steps.** Combining the telescoped
leading-exponent bound `leadExp_ge_sub` (`leadExp_i ≥ log₂ m − i`) with the bridge
`opow_le_seqONote_repr`: whenever `k + i ≤ log₂ m` (and `k < i + 2`), the Goodstein descent ordinal
satisfies `ω^k ≤ (seqONote m i).repr`. Generalizes `omega_le_seqONote_repr` (the `k = 1` case) to
every fixed level `k` — the ordinal stays `≥ ω^k` for the first `log₂ m − k` steps. (Reaching `ω^k`
for `≥ m` steps — the full sub-fact (ii) at `o = k` — needs the steps-between-drops recursion.) -/
theorem omega_opow_le_seqONote_repr {m i k : ℕ} (hi : i + 1 ≤ m)
    (hk : k + i ≤ Nat.log 2 m) (hkb : k < i + 2) :
    (ω : Ordinal) ^ (k : Ordinal) ≤ (seqONote m i).repr := by
  have hle := leadExp_ge_sub m i hi
  have hkle : k ≤ Nat.log (base i) (goodsteinSeq m i) := by omega
  have hv : goodsteinSeq m i ≠ 0 := by
    have := goodsteinSeq_ge_init m i hi; omega
  have hkb' : k < base i := by simp only [base]; omega
  exact opow_le_seqONote_repr hkle hv hkb'

/-- The Goodstein value drops by **at most one** per step (`bump b v ≥ v`, so
`goodsteinSeq m (j+1) = bump _ v − 1 ≥ v − 1`). Telescoped: `goodsteinSeq m j ≤
goodsteinSeq m (j + i) + i` — the value `i` steps later is at least `(value now) − i`. -/
theorem goodsteinSeq_sub_le (m j : ℕ) : ∀ i, goodsteinSeq m j ≤ goodsteinSeq m (j + i) + i := by
  intro i
  induction i with
  | zero => simp
  | succ i ih =>
    have hstep : goodsteinSeq m (j + i) ≤ goodsteinSeq m (j + i + 1) + 1 := by
      have h := le_bump (base (j + i)) (Nat.le_add_left 2 (j + i)) (goodsteinSeq m (j + i))
      show goodsteinSeq m (j + i) ≤ bump (base (j + i)) (goodsteinSeq m (j + i)) - 1 + 1
      omega
    have hassoc : j + (i + 1) = j + i + 1 := by ring
    rw [hassoc]; omega

/-- **Goodstein length is at least `2m − 1`** (improving the linear `≥ m`). The value stays `≥ m`
through step `m − 1` (`goodsteinSeq_ge_init`), and thereafter decreases by at most one per step
(`goodsteinSeq_sub_le`), so it stays positive through step `2m − 2`; its first zero is at `≥ 2m−1`.
A super-linear-constant lower bound; it also re-derives `f_1`-domination elementarily
(`2m ≤ (2m−1) + 2`). -/
theorem two_mul_sub_one_le_goodsteinLength (n : ℕ) :
    2 * n + 3 ≤ goodsteinLength (n + 2) := by
  rw [goodsteinLength, Nat.le_find_iff]
  intro k hk
  by_cases hkle : k ≤ n + 1
  · have h := goodsteinSeq_ge_init (n + 2) k (by omega)
    omega
  · have hinit : n + 2 ≤ goodsteinSeq (n + 2) (n + 1) :=
      goodsteinSeq_ge_init (n + 2) (n + 1) (by omega)
    have hsub := goodsteinSeq_sub_le (n + 2) (n + 1) (k - (n + 1))
    rw [Nat.add_sub_cancel' (by omega : n + 1 ≤ k)] at hsub
    omega

/-! ### The CNF norm of a Goodstein notation is bounded by its step index

A Goodstein notation `seqONote m j = toONote (j+2) (goodsteinSeq m j)` is, by construction, a
base-`(j+2)` hereditary numeral: *every* coefficient appearing anywhere in its Cantor normal
form (digits and recursively the exponents) is a base-`(j+2)` digit, hence `< j+2`. So its CNF
norm is `≤ j+1`. The structural consequence: **the Hardy budget `norm ≤ argument` is always met
at the telescope step `j+2`** — the budget obstruction is automatic on the descent itself, and
`hardy_le_of_lt` can be applied in either comparison direction at every telescope step. -/

/-- Every coefficient of `toONote b n` is a base-`b` digit, so its CNF norm is `< b`
(for `b ≥ 2`). Strong induction mirroring `toONote`'s peeling recursion: the leading digit
`n / b^(log b n) < b`, and the exponent `toONote b (log b n)` and tail `toONote b (n % …)`
recurse on strictly smaller arguments. -/
theorem norm_toONote_lt (b : ℕ) (hb : 2 ≤ b) : ∀ n, norm (toONote b n) < b := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases eq_or_ne n 0 with rfl | hn
    · rw [toONote_zero, norm_zero]; omega
    · have hb1 : 1 < b := by omega
      have hlog : Nat.log b n < n := Nat.log_lt_self b hn
      have hbe_pos : 0 < b ^ Nat.log b n := Nat.pow_pos (by omega)
      have hbe_le : b ^ Nat.log b n ≤ n := Nat.pow_log_le_self b hn
      have hr_lt : n % b ^ Nat.log b n < b ^ Nat.log b n := Nat.mod_lt _ hbe_pos
      have hr_lt_n : n % b ^ Nat.log b n < n := lt_of_lt_of_le hr_lt hbe_le
      have hc_pos : 0 < n / b ^ Nat.log b n := Nat.div_pos hbe_le hbe_pos
      have hc_lt : n / b ^ Nat.log b n < b := by
        rw [Nat.div_lt_iff_lt_mul hbe_pos, ← pow_succ']
        exact Nat.lt_pow_succ_log_self hb1 n
      rw [toONote, dif_neg hn, norm_oadd]
      have hcoeff : ((n / b ^ Nat.log b n).toPNat' : ℕ) = n / b ^ Nat.log b n :=
        PNat.toPNat'_coe hc_pos
      rw [hcoeff]
      have h1 := ih _ hlog
      have h2 := ih _ hr_lt_n
      omega

/-- **The Goodstein descent always meets the Hardy budget.** `norm (seqONote m j) ≤ j + 1`,
hence `≤ j + 2 =` the telescope argument. So `hardy_le_of_lt` is applicable at every telescope
step `j+2` (against any notation the budget reaches), with no further budget hypothesis. -/
theorem norm_seqONote_le (m j : ℕ) : norm (seqONote m j) ≤ j + 1 := by
  have h := norm_toONote_lt (j + 2) (by omega) (goodsteinSeq m j)
  show norm (toONote (j + 2) (goodsteinSeq m j)) ≤ j + 1
  omega

/-! ### The domination headline, reduced to the single index sub-fact (ii)

The full chain of the growth headline — `fastGrowing o m ≤ goodsteinLength m + 2` — is here
assembled and machine-checked, modulo exactly one deep input: that after `m` Goodstein steps the
descent notation `seqONote m m` still exceeds `ω^o = oadd o 1 0` (sub-fact (ii), the
"ordinal-stays-high" / super-exponential term bound). Everything else is banked:

* the Cichoń telescope `hardy_seqONote_telescope` at `j = m` (valid by the linear length bound
  `le_goodsteinLength`, sub-fact (i)) plus `hardy_seqONote_zero`, giving
  `goodsteinLength m + 2 = H_{seqONote m m}(m+2)`;
* the **budget-valid** index step `hardy_le_of_lt` (the norm budget `m+2 ≥ norm (oadd o 1 0)` now
  holds — this is why we evaluate at the high-budget step `m+2`, not at the fixed argument `2`);
* the Hardy↔fast-growing bridge `fastGrowing_le_hardy_pow` at matching argument `m+2`;
* argument-monotonicity `fastGrowing_monotone` to descend `m+2 ↦ m`.

This isolates the remaining mathematical content to `hidx` alone. -/

/-- **Domination, reduced to the index sub-fact (ii).** Given that the Goodstein descent stays
above `ω^o` for at least `m` steps (`hidx : oadd o 1 0 < seqONote m m`) and the budget is met
(`norm o ≤ m`), the Goodstein length dominates the fast-growing level `o` at the diagonal:
`fastGrowing o m ≤ goodsteinLength m + 2`. The whole Cichoń assembly is machine-checked here;
the only open input is `hidx`. -/
theorem goodstein_dominates_of_index {o : ONote} (ho : o.NF) {m : ℕ}
    (hnorm : norm o ≤ m) (hidx : oadd o 1 0 < seqONote m m) :
    fastGrowing o m ≤ goodsteinLength m + 2 := by
  have hNFidx : (oadd o 1 0).NF := NF.oadd ho 1 NFBelow.zero
  have hNFseq : (seqONote m m).NF := seqONote_NF m m
  have hbudget : norm (oadd o 1 0) ≤ m + 2 := by
    rw [norm_oadd, norm_zero]; simp only [PNat.one_coe]; omega
  -- index step at the high-budget argument `m+2`
  have hindex : hardy (oadd o 1 0) (m + 2) ≤ hardy (seqONote m m) (m + 2) :=
    hardy_le_of_lt hNFidx hNFseq hidx hbudget
  -- telescope: the Hardy value is invariant; at `j = m` it equals `goodsteinLength m + 2`
  have htel : hardy (seqONote m 0) 2 = hardy (seqONote m m) (m + 2) :=
    hardy_seqONote_telescope m m (le_goodsteinLength m)
  have hz : hardy (seqONote m 0) 2 = goodsteinLength m + 2 := hardy_seqONote_zero m
  calc fastGrowing o m
      ≤ fastGrowing o (m + 2) := fastGrowing_monotone o (by omega)
    _ ≤ hardy (oadd o 1 0) (m + 2) := fastGrowing_le_hardy_pow o ho (m + 2)
    _ ≤ hardy (seqONote m m) (m + 2) := hindex
    _ = hardy (seqONote m 0) 2 := htel.symm
    _ = goodsteinLength m + 2 := hz

/-- **The domination dichotomy (fully proved, unconditional).** For every fixed level `o`
(with budget `norm o ≤ m`), at the diagonal `m` exactly one of two structural alternatives
holds:

* **(A)** Goodstein dominates: `fastGrowing o m ≤ goodsteinLength m + 2`; or
* **(B)** the length is Hardy-bounded: `goodsteinLength m + 2 ≤ hardy (oadd o 1 0) (m + 2)`.

The proof needs no index hypothesis: because `norm (seqONote m m) ≤ m + 1` (the budget is
automatic on the descent, `norm_seqONote_le`), `hardy_le_of_lt` applies in *whichever*
direction the trichotomy `seqONote m m` vs `oadd o 1 0` falls. The whole headline thus reduces
to **ruling out branch (B) for large `m`** — i.e. to the deep fact that the descent stays above
`ω^o` for at least `m` steps (sub-fact (ii)); branch (B) says the descent has already dropped
below `ω^o` by step `m`, which is conjecturally impossible for large `m` but is exactly the
Cichoń lower-bound content not yet formalized. -/
theorem goodstein_dominates_or_hardy_bound {o : ONote} (ho : o.NF) {m : ℕ}
    (hnorm : norm o ≤ m) :
    fastGrowing o m ≤ goodsteinLength m + 2 ∨
      goodsteinLength m + 2 ≤ hardy (oadd o 1 0) (m + 2) := by
  have hNFidx : (oadd o 1 0).NF := NF.oadd ho 1 NFBelow.zero
  have hNFseq : (seqONote m m).NF := seqONote_NF m m
  have hval : hardy (seqONote m m) (m + 2) = goodsteinLength m + 2 := by
    rw [← hardy_seqONote_telescope m m (le_goodsteinLength m), hardy_seqONote_zero]
  have hbseq : norm (seqONote m m) ≤ m + 2 := le_trans (norm_seqONote_le m m) (by omega)
  rcases lt_trichotomy (seqONote m m).repr (oadd o 1 0).repr with hlt | heq | hgt
  · -- descent already below `ω^o` at step `m` (strict): branch (B)
    right
    have hcmp : seqONote m m < oadd o 1 0 := lt_def.2 hlt
    have h := hardy_le_of_lt hNFseq hNFidx hcmp hbseq
    rwa [hval] at h
  · -- descent exactly at `ω^o`: branch (B), via equality
    right
    have heqo : seqONote m m = oadd o 1 0 := (@repr_inj (seqONote m m) (oadd o 1 0) hNFseq hNFidx).1 heq
    exact le_of_eq (by rw [← hval, heqo])
  · -- descent still above `ω^o`: branch (A), via the reduction lemma
    left
    exact goodstein_dominates_of_index ho hnorm (lt_def.2 hgt)

/-- **Domination, generalized reduction (any telescope step, `≤` index).** If at some step `j`
the budget reaches the diagonal (`m ≤ j + 2`, `norm o ≤ j + 2`) and the descent notation is at
least `ω^o` (`(oadd o 1 0).repr ≤ (seqONote m j).repr`, allowing equality), then `goodsteinLength`
dominates `fastGrowing o` at `m`. Generalizes `goodstein_dominates_of_index`: the telescope step is
free (any `j ≤ goodsteinLength m`), and the index hypothesis is non-strict — the equality case
`oadd o 1 0 = seqONote m j` collapses the Hardy comparison to a literal `rfl`, while the strict
case uses `hardy_le_of_lt` (budget met). This is what lets the `o = 1` level close from the
non-strict ordinal bound `omega_le_seqONote_repr`. -/
theorem goodstein_dominates_of_index_le {o : ONote} (ho : o.NF) {m j : ℕ}
    (hj : j ≤ goodsteinLength m) (hmj : m ≤ j + 2) (hnorm : norm o ≤ j + 2)
    (hidx : (oadd o 1 0).repr ≤ (seqONote m j).repr) :
    fastGrowing o m ≤ goodsteinLength m + 2 := by
  have hNFidx : (oadd o 1 0).NF := NF.oadd ho 1 NFBelow.zero
  have hNFseq : (seqONote m j).NF := seqONote_NF m j
  have hbudget : norm (oadd o 1 0) ≤ j + 2 := by
    rw [norm_oadd, norm_zero]; simp only [PNat.one_coe]; omega
  have hindex : hardy (oadd o 1 0) (j + 2) ≤ hardy (seqONote m j) (j + 2) := by
    rcases eq_or_lt_of_le hidx with heq | hlt
    · have heqo : oadd o 1 0 = seqONote m j :=
        (@repr_inj (oadd o 1 0) (seqONote m j) hNFidx hNFseq).1 heq
      rw [heqo]
    · exact hardy_le_of_lt hNFidx hNFseq (lt_def.2 hlt) hbudget
  have htel : hardy (seqONote m 0) 2 = hardy (seqONote m j) (j + 2) :=
    hardy_seqONote_telescope m j hj
  have hz : hardy (seqONote m 0) 2 = goodsteinLength m + 2 := hardy_seqONote_zero m
  calc fastGrowing o m
      ≤ fastGrowing o (j + 2) := fastGrowing_monotone o hmj
    _ ≤ hardy (oadd o 1 0) (j + 2) := fastGrowing_le_hardy_pow o ho (j + 2)
    _ ≤ hardy (seqONote m j) (j + 2) := hindex
    _ = hardy (seqONote m 0) 2 := htel.symm
    _ = goodsteinLength m + 2 := hz

/-- **Goodstein length dominates `f_1`, unconditionally (every `m ≥ 2`).** This is the first
member of the fast-growing hierarchy proven dominated by `goodsteinLength` through the full
Cichoń pipeline — *not* by `native_decide`. The deep input, sub-fact (ii) at `o = 1`, is supplied
by `omega_le_seqONote_repr`: at step `j = m − 2` the descent ordinal is still `≥ ω`, so the
generalized reduction `goodstein_dominates_of_index_le` (budget `j + 2 = m`) applies. Concretely
`f_1(m) = 2m ≤ goodsteinLength m + 2`. -/
theorem fastGrowing_one_le_goodsteinLength (n : ℕ) :
    fastGrowing 1 (n + 2) ≤ goodsteinLength (n + 2) + 2 := by
  have ho : (1 : ONote).NF := NF.oadd NF.zero 1 NFBelow.zero
  have hlhs : (oadd (1 : ONote) 1 0).repr = ω := by simp [ONote.repr]
  refine goodstein_dominates_of_index_le (o := 1) (m := n + 2) (j := n) ho ?_ ?_ ?_ ?_
  · have := le_goodsteinLength (n + 2); omega
  · omega
  · have hn1 : norm (1 : ONote) = 1 := by decide
    omega
  · rw [hlhs]; exact omega_le_seqONote_repr (le_refl n)

/-- **Non-diagonal reduction (length lower bound).** Like `goodstein_dominates_of_index_le` but
without the budget constraint `m ≤ j + 2` — it concludes about `fastGrowing o (j + 2)` (the step's
own budget) instead of `fastGrowing o m`. Whenever the descent at step `j` is `≥ ω^o`, the Goodstein
length is bounded below by `f_o(j+2)`. This is what converts the early-step ordinal bounds (where
`j ≈ log₂ m ≪ m`) into a **super-linear lower bound on `goodsteinLength`** (it cannot reach the
diagonal `f_o(m)`, but it does beat every polynomial). -/
theorem fastGrowing_step_le_goodsteinLength {o : ONote} (ho : o.NF) {m j : ℕ}
    (hj : j ≤ goodsteinLength m) (hnorm : norm o ≤ j + 2)
    (hidx : (oadd o 1 0).repr ≤ (seqONote m j).repr) :
    fastGrowing o (j + 2) ≤ goodsteinLength m + 2 := by
  have hNFidx : (oadd o 1 0).NF := NF.oadd ho 1 NFBelow.zero
  have hNFseq : (seqONote m j).NF := seqONote_NF m j
  have hbudget : norm (oadd o 1 0) ≤ j + 2 := by
    rw [norm_oadd, norm_zero]; simp only [PNat.one_coe]; omega
  have hindex : hardy (oadd o 1 0) (j + 2) ≤ hardy (seqONote m j) (j + 2) := by
    rcases eq_or_lt_of_le hidx with heq | hlt
    · have heqo : oadd o 1 0 = seqONote m j :=
        (@repr_inj (oadd o 1 0) (seqONote m j) hNFidx hNFseq).1 heq
      rw [heqo]
    · exact hardy_le_of_lt hNFidx hNFseq (lt_def.2 hlt) hbudget
  calc fastGrowing o (j + 2)
      ≤ hardy (oadd o 1 0) (j + 2) := fastGrowing_le_hardy_pow o ho (j + 2)
    _ ≤ hardy (seqONote m j) (j + 2) := hindex
    _ = hardy (seqONote m 0) 2 := (hardy_seqONote_telescope m j hj).symm
    _ = goodsteinLength m + 2 := hardy_seqONote_zero m

/-- **`goodsteinLength` is SUPER-LINEAR:** `fastGrowing 2 (Nat.log 2 m) ≤ goodsteinLength m + 2`
(for `Nat.log 2 m ≥ 3`, i.e. `m ≥ 8`). Since `fastGrowing 2 n = 2^n · n`, this reads
`goodsteinLength m ≳ 2^{log₂ m} · log₂ m = m · log₂ m` — a genuine super-linear (beats every linear)
lower bound, the first proof that `goodsteinLength` outgrows the polynomial regime. Assembly: at
the early step `j = log₂ m − 2` the descent ordinal is `≥ ω² = (oadd 2 1 0).repr`
(`omega_opow_le_seqONote_repr`, leading exponent still `≥ 2`); feed the non-diagonal reduction. The
budget here is only `log₂ m`, not `m` — closing the gap to `f_2(m)` needs the deeper recursion. -/
theorem fastGrowing_two_log_le_goodsteinLength {m : ℕ} (hm : 3 ≤ Nat.log 2 m) :
    fastGrowing 2 (Nat.log 2 m) ≤ goodsteinLength m + 2 := by
  set L := Nat.log 2 m with hL
  have hLm : L ≤ m := Nat.log_le_self 2 m
  have hglen : m ≤ goodsteinLength m := le_goodsteinLength m
  have ho : (2 : ONote).NF := by decide
  have hr2 : (oadd (2 : ONote) 1 0).repr = ω ^ (2 : Ordinal) := by
    rw [show (2 : ONote) = oadd 0 2 0 from rfl]; simp [ONote.repr]
  have hidx : (oadd (2 : ONote) 1 0).repr ≤ (seqONote m (L - 2)).repr := by
    rw [hr2]
    exact omega_opow_le_seqONote_repr (m := m) (i := L - 2) (k := 2)
      (by omega) (by omega) (by omega)
  have hnorm : norm (2 : ONote) ≤ (L - 2) + 2 := by
    have : norm (2 : ONote) = 2 := by decide
    omega
  have h := fastGrowing_step_le_goodsteinLength ho (m := m) (j := L - 2)
    (by omega) hnorm hidx
  rwa [show L - 2 + 2 = L from by omega] at h

/-- **The `o = 2` diagonal domination, REDUCED to a one-level-smaller length bound.** If
`m + 2 ≤ goodsteinLength (Nat.log 2 m)` then `fastGrowing 2 m ≤ goodsteinLength m + 2` — the true
diagonal `f_2(m)` bound (budget `m`, *not* `log₂ m`), the first genuine instance of Cichoń's lower
bound beyond `o = 1`. Assembly: the hypothesis feeds `two_le_leadExp_of_log_length` to keep the
leading exponent `≥ 2` through step `j = m − 2`, so the descent ordinal there is `≥ ω² =
(oadd 2 1 0).repr` (`opow_le_seqONote_repr`); the diagonal reduction `goodstein_dominates_of_index_le`
(budget `j + 2 = m`) then closes it. **This isolates the entire remaining `o = 2` obligation to the
self-referential length bound `m + 2 ≤ goodsteinLength (Nat.log 2 m)`** — provable for large `m` by a
strong induction on `m` (the lower length is astronomically larger than `m` once `Nat.log 2 m ≥ 4`),
the clean successor to the abandoned `ppCount` sparsity route. -/
theorem fastGrowing_two_le_goodsteinLength_of_log_length {m : ℕ} (hm : 4 ≤ m)
    (hlen : m + 2 ≤ goodsteinLength (Nat.log 2 m)) :
    fastGrowing 2 m ≤ goodsteinLength m + 2 := by
  have ho : (2 : ONote).NF := by decide
  have hr2 : (oadd (2 : ONote) 1 0).repr = ω ^ (2 : Ordinal) := by
    rw [show (2 : ONote) = oadd 0 2 0 from rfl]; simp [ONote.repr]
  set j := m - 2 with hj
  have hlead : 2 ≤ Nat.log (base j) (goodsteinSeq m j) :=
    two_le_leadExp_of_log_length hlen (by omega)
  have hv : goodsteinSeq m j ≠ 0 := by
    have := goodsteinSeq_ge_init m j (by omega); omega
  have hkb : (2 : ℕ) < base j := by simp only [base]; omega
  have hidx : (oadd (2 : ONote) 1 0).repr ≤ (seqONote m j).repr := by
    rw [hr2]; exact opow_le_seqONote_repr (m := m) (i := j) (k := 2) hlead hv hkb
  have hnorm : norm (2 : ONote) ≤ j + 2 := by
    have : norm (2 : ONote) = 2 := by decide
    omega
  have hgl : j ≤ goodsteinLength m := le_trans (by omega) (le_goodsteinLength m)
  exact goodstein_dominates_of_index_le (o := 2) (m := m) (j := j) ho hgl (by omega) hnorm hidx

/-- `2·m ≤ 2^m` for `m ≥ 2` (elementary; the slack that turns `f_2(m) = 2^m·m` into a clean
`≥ 2^{m+1}` exponential length bound). -/
theorem two_mul_le_two_pow {m : ℕ} (h : 2 ≤ m) : 2 * m ≤ 2 ^ m := by
  induction m with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_or_ge n 2 with hn | hn
    · have hn1 : n = 1 := by omega
      subst hn1; norm_num
    · have := ih hn; rw [pow_succ]; omega

/-- **Inductive step of Cichoń's exponential length bound.** If the *one-level-down* Goodstein
sequence runs `≥ m + 2` steps — `m + 2 ≤ goodsteinLength (Nat.log 2 m)` — then the seed-`m` length is
at least `2^{m+1} + m`. Combines the conditional `o = 2` domination
(`fastGrowing_two_le_goodsteinLength_of_log_length`, giving `2^m·m = f_2(m) ≤ goodsteinLength m + 2`)
with the slack `2^m ≥ m + 2`: `2^m·m − 2 ≥ 2^{m+1} + m` for `m ≥ 4`. This is the engine of the strong
induction in `goodsteinLength_exp_lower`: it converts an exponential length bound at the *small* seed
`Nat.log 2 m` into one at `m`, the self-reference at the heart of Cichoń's lower bound. -/
theorem exp_le_goodsteinLength_step {m : ℕ} (hm : 4 ≤ m)
    (hlen : m + 2 ≤ goodsteinLength (Nat.log 2 m)) :
    2 ^ (m + 1) + m ≤ goodsteinLength m := by
  have hdom := fastGrowing_two_le_goodsteinLength_of_log_length hm hlen
  simp only [ONote.fastGrowing_two] at hdom
  have hpow : m + 2 ≤ 2 ^ m := le_trans (by omega) (two_mul_le_two_pow (by omega))
  set P := 2 ^ m with hP
  set G := goodsteinLength m with hG
  have hd : 2 ≤ m - 2 := by omega
  have key : (m + 2) * 2 ≤ P * (m - 2) := Nat.mul_le_mul hpow hd
  have hsplit : P * m = P * (m - 2) + 2 * P := by
    have h2 : m - 2 + 2 = m := by omega
    calc P * m = P * ((m - 2) + 2) := by rw [h2]
      _ = P * (m - 2) + P * 2 := by rw [Nat.mul_add]
      _ = P * (m - 2) + 2 * P := by ring
  have hpsucc : 2 ^ (m + 1) = 2 * P := by rw [hP, pow_succ]; ring
  rw [hpsucc]; omega

/-- **Tail-recursive forward "all-nonzero" checker.** `gpos k v fuel` is `true` iff the `fuel`
consecutive Goodstein values `v = G_k, G_{k+1}, …, G_{k+fuel−1}` are all nonzero, computed by a single
forward pass (recursion structural on `fuel`, in tail position of `&&`, so it compiles to a *loop* — no
`fuel`-deep call stack, unlike `goodsteinSeq` itself). The tool that lets `native_decide` certify the
large finite base-case length bounds `goodsteinLength M ≥ 2^{M+1} + M` (`M ≤ 15`, up to `65551` steps)
that a naive `∀ n < N, goodsteinSeq M n ≠ 0` would stack-overflow on. -/
def gpos : ℕ → ℕ → ℕ → Bool
  | _, _, 0 => true
  | k, v, fuel + 1 => decide (v ≠ 0) && gpos (k + 1) (bump (base k) v - 1) fuel

/-- **Soundness of `gpos`:** if the forward pass from `G_k` reports all-nonzero for `fuel` steps, then
`goodsteinSeq M (k + j) ≠ 0` for every `j < fuel`. Induction on `fuel`, using that the threaded value
`bump (base k) (G_k) − 1` is exactly `G_{k+1}` (defeq) so the accumulator stays on the real sequence. -/
theorem gpos_goodstein (M : ℕ) : ∀ fuel k, gpos k (goodsteinSeq M k) fuel = true →
    ∀ j, j < fuel → goodsteinSeq M (k + j) ≠ 0 := by
  intro fuel
  induction fuel with
  | zero => intro k _ j hj; omega
  | succ fuel ih =>
    intro k hgp j hj
    rw [gpos, Bool.and_eq_true, decide_eq_true_eq] at hgp
    obtain ⟨hv0, hrest⟩ := hgp
    have hstep : bump (base k) (goodsteinSeq M k) - 1 = goodsteinSeq M (k + 1) := rfl
    rw [hstep] at hrest
    rcases Nat.eq_zero_or_pos j with hj0 | hjpos
    · subst hj0; rwa [Nat.add_zero]
    · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      have hres := ih (k + 1) hrest j' (by omega)
      rwa [show k + (j' + 1) = (k + 1) + j' from by omega]

/-- **Computable length lower bound.** `gpos 0 M N = true ⟹ N ≤ goodsteinLength M`: if the forward
pass certifies the first `N` Goodstein values nonzero, the first zero is at step `≥ N`. The bridge
from `native_decide` to the base-case length bounds. -/
theorem glen_ge_of_gpos {M N : ℕ} (h : gpos 0 M N = true) : N ≤ goodsteinLength M := by
  rw [goodsteinLength, Nat.le_find_iff]
  intro n hn
  have := gpos_goodstein M N 0 h n hn
  rwa [Nat.zero_add] at this

/-- **Cichoń's exponential length lower bound, the strong-induction engine** (conditional on finitely
many base cases). Given the base bounds `2^{M+1} + M ≤ goodsteinLength M` for `4 ≤ M < 16`, the same
bound holds for *every* `m ≥ 4`. Strong induction on `m`: for `m ≥ 16` the seed `L = Nat.log 2 m` is
`≥ 4` and `< m`, so the IH gives `goodsteinLength L ≥ 2^{L+1} + L ≥ (m+1) + L ≥ m + 2` (using
`m < 2^{L+1}`), which feeds `exp_le_goodsteinLength_step` to conclude `goodsteinLength m ≥ 2^{m+1} + m`;
for `4 ≤ m < 16` it is a base case. **This is Cichoń's lower bound:** the self-similarity
(`leadExp_ge_goodsteinSeq_log`) makes the exponential length bound *reproduce itself* one scale up. The
base hypothesis is purely computational (no deep content) — discharged by `gpos`/`native_decide` in
`goodsteinLength_exp_lower_uncond`. -/
theorem goodsteinLength_exp_lower
    (hbase : ∀ M, 4 ≤ M → M < 16 → 2 ^ (M + 1) + M ≤ goodsteinLength M) :
    ∀ m, 4 ≤ m → 2 ^ (m + 1) + m ≤ goodsteinLength m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm
    rcases Nat.lt_or_ge m 16 with hsmall | hbig
    · exact hbase m hm hsmall
    · set L := Nat.log 2 m with hL
      have hL4 : 4 ≤ L := by
        calc 4 = Nat.log 2 16 := by rw [show (16 : ℕ) = 2 ^ 4 from rfl, Nat.log_pow (by norm_num)]
          _ ≤ Nat.log 2 m := Nat.log_mono_right hbig
      have hLm : L < m := Nat.log_lt_self 2 (by omega)
      have ihL := ih L hLm hL4
      have hpowL : m + 1 ≤ 2 ^ (L + 1) := by
        have h := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) m
        rw [← hL] at h
        omega
      have hlen : m + 2 ≤ goodsteinLength L := by omega
      exact exp_le_goodsteinLength_step (by omega) hlen

/-- `norm (ofNat n) = n`: a finite notation `ofNat (k+1) = oadd 0 ⟨k+1⟩ 0` has CNF norm its single
coefficient. -/
theorem norm_ofNat (n : ℕ) : norm (ONote.ofNat n) = n := by
  cases n with
  | zero => rfl
  | succ k => rw [ONote.ofNat_succ, norm_oadd, norm_zero]; simp

/-! ### General level `o = n`: the full diagonal domination (for every finite `n`)

The `o = 2` machinery (self-similarity `leadExp_ge_goodsteinSeq_log` + exponential length bound)
generalizes verbatim to every finite level `n`. The only new ingredient is a *value* lower bound on
the one-level-down sequence: `goodsteinSeq (Nat.log 2 m) k ≥ n` for the first `m` steps, which needs
`goodsteinLength (Nat.log 2 m) ≥ m + n`. That follows from the small-regime termination law
(`goodsteinLength_le_of_small`): below its base a Goodstein value falls by *exactly one* each step, so
a value `< n` at step `k` forces termination within `n` more steps — hence the value stays `≥ n` until
`n` steps before the end. -/

/-- **Small-regime step:** below its base, a Goodstein value drops by exactly one
(`bump (base k) v = v` for `v < base k`, then the `−1`). -/
theorem goodsteinSeq_small_step (M k : ℕ) (h : goodsteinSeq M k < base k) :
    goodsteinSeq M (k + 1) = goodsteinSeq M k - 1 := by
  show bump (base k) (goodsteinSeq M k) - 1 = goodsteinSeq M k - 1
  rw [bump_eq_of_lt (base k) (goodsteinSeq M k) h]

/-- **Small-regime termination law:** once a Goodstein value is below its base it decreases by one per
step (base only grows, so it stays below), reaching `0` within `goodsteinSeq M k` steps. Hence
`goodsteinLength M ≤ k + goodsteinSeq M k` whenever `goodsteinSeq M k < base k`. -/
theorem goodsteinLength_le_of_small (M : ℕ) :
    ∀ v k, goodsteinSeq M k = v → goodsteinSeq M k < base k → goodsteinLength M ≤ k + v := by
  intro v
  induction v with
  | zero => intro k hv _; have := goodsteinLength_le hv; omega
  | succ v ih =>
    intro k hv hsmall
    have hstep := goodsteinSeq_small_step M k hsmall
    have hstep' : goodsteinSeq M (k + 1) = v := by omega
    have hsmall' : goodsteinSeq M (k + 1) < base (k + 1) := by
      rw [hstep']; simp only [base] at hsmall hv ⊢; omega
    have := ih (k + 1) hstep' hsmall'
    omega

/-- **A Goodstein term stays `≥ n` until `n` steps before it terminates** (general level). If
`n ≤ base k` and `k + n ≤ goodsteinLength M` then `n ≤ goodsteinSeq M k`: were it `< n ≤ base k`, the
small-regime law would force `goodsteinLength M ≤ k + goodsteinSeq M k < k + n`, contradiction.
Generalizes `two_le_goodsteinSeq` (the `n = 2` case). -/
theorem n_le_goodsteinSeq (M k n : ℕ) (hn : n ≤ base k) (hlen : k + n ≤ goodsteinLength M) :
    n ≤ goodsteinSeq M k := by
  by_contra hc
  rw [not_le] at hc
  have hsmall : goodsteinSeq M k < base k := lt_of_lt_of_le hc hn
  have := goodsteinLength_le_of_small M (goodsteinSeq M k) k rfl hsmall
  omega

/-- **The self-similarity reduction at general level `n`:** if `m + n ≤ goodsteinLength (Nat.log 2 m)`
then the seed-`m` leading exponent at step `k ≤ m` is `≥ n` (provided `n ≤ base k`). Chains
`n_le_goodsteinSeq` (the lower sequence stays `≥ n`) through `leadExp_ge_goodsteinSeq_log`. Generalizes
`two_le_leadExp_of_log_length`. -/
theorem n_le_leadExp_of_log_length {m k n : ℕ}
    (hlen : m + n ≤ goodsteinLength (Nat.log 2 m)) (hk : k ≤ m) (hkn : n ≤ base k) :
    n ≤ Nat.log (base k) (goodsteinSeq m k) :=
  le_trans (n_le_goodsteinSeq (Nat.log 2 m) k n hkn (by omega)) (leadExp_ge_goodsteinSeq_log m k)

/-- **The general diagonal domination, REDUCED to a one-level-smaller length bound.** For every finite
level `n`, if `m + n ≤ goodsteinLength (Nat.log 2 m)` (and `n ≤ m − 2`, `m ≥ 4`) then
`fastGrowing (ofNat n) m ≤ goodsteinLength m + 2` — the *true diagonal* `f_n(m)` bound at level `n`
(budget `m`). This is Cichoń's lower bound at every finite level, modulo the self-referential length
bound. Assembly: `n_le_leadExp_of_log_length` keeps the leading exponent `≥ n` through step
`j = m − 2`, so the descent ordinal there dominates `ω^n = (oadd (ofNat n) 1 0).repr`
(`opow_le_seqONote_repr`); the diagonal reduction `goodstein_dominates_of_index_le` closes it.
Generalizes `fastGrowing_two_le_goodsteinLength_of_log_length` to all `n`. -/
theorem fastGrowing_ofNat_le_goodsteinLength_of_log_length {n m : ℕ}
    (hnm : n ≤ m - 2) (hm : 4 ≤ m)
    (hlen : m + n ≤ goodsteinLength (Nat.log 2 m)) :
    fastGrowing (ONote.ofNat n) m ≤ goodsteinLength m + 2 := by
  set j := m - 2 with hj
  have ho : (ONote.ofNat n).NF := inferInstance
  have hrepr : (ONote.ofNat n).repr = (n : Ordinal) := ONote.repr_ofNat n
  have hlead : n ≤ Nat.log (base j) (goodsteinSeq m j) :=
    n_le_leadExp_of_log_length (m := m) (k := j) (n := n) hlen (by omega) (by simp only [base]; omega)
  have hv : goodsteinSeq m j ≠ 0 := by have := goodsteinSeq_ge_init m j (by omega); omega
  have hkb : n < base j := by simp only [base]; omega
  have hidx : (oadd (ONote.ofNat n) 1 0).repr ≤ (seqONote m j).repr := by
    have hr : (oadd (ONote.ofNat n) 1 0).repr = ω ^ (n : Ordinal) := by simp [ONote.repr, hrepr]
    rw [hr]
    exact opow_le_seqONote_repr (m := m) (i := j) (k := n) hlead hv hkb
  have hnorm : norm (ONote.ofNat n) ≤ j + 2 := by rw [norm_ofNat]; omega
  have hgl : j ≤ goodsteinLength m := le_trans (by omega) (le_goodsteinLength m)
  exact goodstein_dominates_of_index_le (o := ONote.ofNat n) (m := m) (j := j) ho hgl (by omega) hnorm hidx

/-- **`goodsteinLength` is NON-ELEMENTARY:** for every finite level `n`,
`fastGrowing (ofNat n) (log₂ m − n + 2) ≤ goodsteinLength m + 2` (for `1 ≤ m`, `2n ≤ log₂ m`).
Generalizes `fastGrowing_two_log_le_goodsteinLength` to all `n`: at the early step `i = log₂ m − n`
the leading exponent is still `≥ n` (`leadExp_ge_sub`), so the descent ordinal is `≥ ω^n =
(oadd (ofNat n) 1 0).repr` (`omega_opow_le_seqONote_repr`); feed the non-diagonal reduction. The
budget is `log₂ m − n` (not `m` — leadExp and budget trade off). Taking e.g. `n = log₂ m / 2` makes
the RHS exceed `f_{(log₂ m)/2}(…)` — a tower of exponentials of height `~log₂ m`, hence
`goodsteinLength` outgrows every elementary function. The diagonal `f_n(m)` (true domination, the
headline) still needs the steps-between-drops recursion. -/
theorem fastGrowing_ofNat_log_le_goodsteinLength (n : ℕ) {m : ℕ} (hm : 1 ≤ m)
    (hn : 2 * n ≤ Nat.log 2 m) :
    fastGrowing (ONote.ofNat n) (Nat.log 2 m - n + 2) ≤ goodsteinLength m + 2 := by
  set L := Nat.log 2 m with hL
  have hLlt : L < m := Nat.log_lt_self 2 (by omega)
  have hglen : m ≤ goodsteinLength m := le_goodsteinLength m
  have ho : (ONote.ofNat n).NF := inferInstance
  have hrepr : (ONote.ofNat n).repr = (n : Ordinal) := ONote.repr_ofNat n
  have hidx : (oadd (ONote.ofNat n) 1 0).repr ≤ (seqONote m (L - n)).repr := by
    have hr : (oadd (ONote.ofNat n) 1 0).repr = ω ^ (n : Ordinal) := by
      simp [ONote.repr, hrepr]
    rw [hr]
    exact omega_opow_le_seqONote_repr (m := m) (i := L - n) (k := n)
      (by omega) (by omega) (by omega)
  have hnorm : norm (ONote.ofNat n) ≤ (L - n) + 2 := by rw [norm_ofNat]; omega
  exact fastGrowing_step_le_goodsteinLength ho (m := m) (j := L - n) (by omega) hnorm hidx

/-! ### Anti-vacuity anchors (off any headline axiom path). -/

example : hardy (oadd 1 2 (oadd 0 3 0)) 4 = hardy (oadd 1 2 0) (hardy (oadd 0 3 0) 4) := by
  native_decide
example : hardy (oadd 1 3 0) 3 = (hardy (oadd 1 1 0))^[3] 3 := by native_decide
example : fastGrowing 2 3 ≤ hardy (oadd 2 1 0) 3 := by native_decide

-- The domination inequality `fastGrowing o m ≤ goodsteinLength m + 2` holds concretely in the
-- computable regime (small `o`, where it already kicks in at small `m`). A *backwards* or
-- vacuous headline would fail these. (For `o ≥ 2` the inequality is asymptotic — it first holds
-- at `m = 4`, where `goodsteinLength` is already astronomically large and beyond `native_decide`.)
-- The growth engine, witnessed: one bump strictly grows a value above its base
-- (`bump_gt`: `4 + 1 ≤ bump 2 4 = 27`), and the term stays `≥ m` (`goodsteinSeq_ge_init`:
-- `G(4,2) = 41 ≥ 4`). A vacuous/backwards recursion would fail these.
example : 4 + 1 ≤ bump 2 4 := by native_decide
example : 4 ≤ goodsteinSeq 4 2 := by native_decide
-- `log_bump`: the leading exponent bumps itself. `bump 2 5 = 28`, `log_3 28 = 3 = bump 2 (log_2 5)`.
example : Nat.log 3 (bump 2 5) = bump 2 (Nat.log 2 5) := by native_decide
-- `log_le_log_pred_succ`: one decrement lowers a log by ≤ 1 (`log_3 9 = 2`, `log_3 8 = 1`).
example : Nat.log 3 9 ≤ Nat.log 3 8 + 1 := by native_decide
-- `leadExp_drop_le_one`: leading exponent drops by ≤ 1 per step. `G(4,2)=41` (`log_4 41 = 2`),
-- `G(4,3)=60` (`log_5 60 = 2`): `2 ≤ 2 + 1`.
example : Nat.log (base 2) (goodsteinSeq 4 2) ≤ Nat.log (base 3) (goodsteinSeq 4 3) + 1 := by
  native_decide
-- `log_bump_pred_of_not_pow`: NO drop at a non-pure-power step. `n=5` (`2²=4 < 5`, not a pure
-- power): `bump 2 5 = 28`, `28−1 = 27`, `log_3 27 = 3 = bump 2 (log_2 5) = bump 2 2 = 3`. No drop.
example : Nat.log 3 (bump 2 5 - 1) = bump 2 (Nat.log 2 5) := by native_decide
-- the hypothesis is LOAD-BEARING: at a pure power `n=4=2²` the leading exponent DOES drop.
-- `bump 2 4 = 27`, `27−1 = 26`, `log_3 26 = 2 ≠ 3 = bump 2 (log_2 4)` — a genuine "borrow".
example : Nat.log 3 (bump 2 4 - 1) ≠ bump 2 (Nat.log 2 4) := by native_decide
-- `log_bump_pred_of_pow`: at the pure power `n=4` the drop is by EXACTLY one:
-- `log_3 26 = 2 = bump 2 (log_2 4) − 1 = 3 − 1 = 2`.
example : Nat.log 3 (bump 2 4 - 1) = bump 2 (Nat.log 2 4) - 1 := by native_decide
-- `ppCount`: `G(4,0)=4=2²` is a pure power (counts), `G(3,0)=3` is not (`2¹=2≠3`).
example : ppCount 4 1 = 1 := by native_decide
example : ppCount 3 1 = 0 := by native_decide
-- the sharpened telescope `leadExp_ge_sub_ppCount`, witnessed: `log_2 4 = 2 ≤ log_3 26 + ppCount 4 1
-- = 2 + 1 = 3`. A vacuous/backwards bound would fail this.
example : Nat.log 2 4 ≤ Nat.log (base 1) (goodsteinSeq 4 1) + ppCount 4 1 := by native_decide
-- `bump_eq_of_lt`: a single digit below its base is fixed (`bump 5 3 = 3`, `3 < 5`).
example : bump 5 3 = 3 := by native_decide
-- `leadExp_small_nonincreasing`: in the small regime the leading exponent only falls. `G(2,0)=2`,
-- `log_2 2 = 1 < base 0 = 2` (small); `G(2,1)=2`, `log_3 2 = 0 ≤ 1`. Non-increasing.
example : Nat.log (base 1) (goodsteinSeq 2 1) ≤ Nat.log (base 0) (goodsteinSeq 2 0) := by native_decide

-- the super-linear bound's interpretation, witnessed: `f_2(n) = 2^n·n` (`fastGrowing_two`), and the
-- step index `Nat.log 2 8 = 3` ⟹ the bound reads `f_2(3) = 24 ≤ goodsteinLength 8 + 2` (RHS huge).
example : fastGrowing 2 3 = 2 ^ 3 * 3 := by native_decide  -- = 24
example : Nat.log 2 8 = 3 := by native_decide

-- `bump_mono`: monotone in its argument. `bump 2 3 = 4 ≤ bump 2 5 = 10`.
example : bump 2 3 ≤ bump 2 5 := by native_decide
-- `leadExp_step_ge`: the per-step floor `bump(base k)(L_k) − 1 ≤ L_{k+1}`. At `m=4, k=2`:
-- `bump 4 2 − 1 = 1 ≤ log_5 54 = 2` (with `G(4,2)=41`, `L_2 = 2`, `G(4,3)=54`, `L_3 = 2`).
example : bump (base 2) (Nat.log (base 2) (goodsteinSeq 4 2)) - 1
    ≤ Nat.log (base 3) (goodsteinSeq 4 3) := by native_decide
-- `leadExp_ge_goodsteinSeq_log` (self-similarity): the leadExp sequence dominates the one-level-down
-- Goodstein sequence. `goodsteinSeq (log₂ 4 = 2) 2 = 1 ≤ log_4 41 = 2`. A backwards bound would fail.
example : goodsteinSeq (Nat.log 2 4) 2 ≤ Nat.log (base 2) (goodsteinSeq 4 2) := by native_decide
-- `two_le_goodsteinSeq`: a term stays `≥ 2` until two steps before it terminates.
-- `goodsteinLength 3 = 5`; at `k = 2` (`2+1 < 5`) the value `goodsteinSeq 3 2 = 3 ≥ 2`.
example : 2 ≤ goodsteinSeq 3 2 := by native_decide
example : fastGrowing 0 2 ≤ goodsteinLength 2 + 2 := by native_decide  -- 3 ≤ 5
example : fastGrowing 1 2 ≤ goodsteinLength 2 + 2 := by native_decide  -- 4 ≤ 5
example : fastGrowing 0 3 ≤ goodsteinLength 3 + 2 := by native_decide  -- 4 ≤ 7
example : fastGrowing 1 3 ≤ goodsteinLength 3 + 2 := by native_decide  -- 6 ≤ 7


-- ════════════════ ported: GoodsteinLike.lean ════════════════
/-
# `GoodsteinLike` sequences and the self-similarity TOWER

Lap 9 found the winning idea — **self-similarity**: the leading-exponent sequence
`L_k = log_{base k}(G_k)` of a Goodstein descent is *itself* a Goodstein-like descent, so it
dominates the genuine Goodstein sequence seeded at `L_0 = log₂ m`. Lap 10 closed `o = ω` by iterating
that idea once. This file extracts the idea into its **clean reusable abstraction** and proves the
*fully iterated* form, the engine for climbing the ordinal tower toward `f_{ε₀}`.

A sequence `a : ℕ → ℕ` is `GoodsteinLike` when it obeys the Goodstein lower-bound recursion
`a (k+1) ≥ bump (base k) (a k) − 1` at every step (the genuine `goodsteinSeq` obeys it with equality).
Two structural facts hold for every such sequence:

* **`GoodsteinLike.dominates`** — `a` dominates `goodsteinSeq (a 0)` (self-similarity: the recursion
  with the `−1` firing at every step is the slowest, so `goodsteinSeq (a 0)` is a lower envelope).
* **`GoodsteinLike.logSeq`** — `k ↦ log_{base k} (a k)` is again `GoodsteinLike` (the leading exponent
  of a Goodstein-like sequence is Goodstein-like — the level-up that drives the tower).

Iterating the second fact (`GoodsteinLike.iterate`) and feeding the first gives the headline
**`iterLeadExp_dominates`**: the `j`-fold iterated leading exponent of the seed-`m` descent dominates
the Goodstein sequence seeded at the `j`-fold logarithm `(log₂)^[j] m`. For `j = 0` this is the value
itself; `j = 1` is lap-9's `leadExp_ge_goodsteinSeq_log`; each higher `j` is one ordinal level up
(`o = ω^j`-flavoured), the precise self-reference behind Cichoń's lower bound at the limit levels.
-/


/-- **General per-step log descent.** For any `n`, the leading exponent obeys the Goodstein recursion
as a *lower bound*: `bump b (log_b n) − 1 ≤ log_{b+1} (bump b n − 1)`. Off pure powers it is an
equality at `bump b (log_b n)` (`log_bump_pred_of_not_pow`); at a pure power it drops by exactly one
(`log_bump_pred_of_pow`); when `n = 0` both sides are `0`. Generalizes `leadExp_step_ge` from the
concrete Goodstein value to an arbitrary `n` — the brick that makes `log ∘ a` Goodstein-like. -/
theorem log_step_ge (b : ℕ) (hb : 2 ≤ b) (n : ℕ) :
    bump b (Nat.log b n) - 1 ≤ Nat.log (b + 1) (bump b n - 1) := by
  rcases eq_or_ne n 0 with hv0 | hv0
  · rw [hv0]; simp
  · by_cases hpp : b ^ Nat.log b n = n
    · rcases Nat.eq_zero_or_pos (Nat.log b n) with he0 | hepos
      · rw [he0, bump_zero]; omega
      · rw [log_bump_pred_of_pow b hb hepos hpp.symm]
    · have hlt : b ^ Nat.log b n < n := by
        have hle := Nat.pow_log_le_self b hv0; omega
      rw [log_bump_pred_of_not_pow b hb hv0 hlt]; omega

/-- A sequence is **Goodstein-like** when it obeys the Goodstein lower-bound recursion at every step:
`a (k+1) ≥ bump (base k) (a k) − 1`. The genuine `goodsteinSeq m` obeys it with equality. -/
def GoodsteinLike (a : ℕ → ℕ) : Prop := ∀ k, bump (base k) (a k) - 1 ≤ a (k + 1)

/-- The leading-exponent operator: `logSeq a k = log_{base k} (a k)`. -/
def logSeq (a : ℕ → ℕ) : ℕ → ℕ := fun k => Nat.log (base k) (a k)

/-- The genuine Goodstein sequence is Goodstein-like (with equality, by definition of the step). -/
theorem goodsteinSeq_goodsteinLike (m : ℕ) : GoodsteinLike (goodsteinSeq m) :=
  fun _ => le_of_eq rfl

/-- **Self-similarity, abstract form.** Every Goodstein-like `a` dominates the genuine Goodstein
sequence seeded at `a 0`: `goodsteinSeq (a 0) k ≤ a k` for all `k`. Induction with `bump_mono`
carrying the step — the `goodsteinSeq` recursion subtracts `1` at *every* step, while `a` does so only
where forced, so `goodsteinSeq (a 0)` is the slowest descent. Generalizes `leadExp_ge_goodsteinSeq_log`
(the case `a = leadExp = logSeq (goodsteinSeq m)`, where `a 0 = log₂ m`). -/
theorem GoodsteinLike.dominates {a : ℕ → ℕ} (ha : GoodsteinLike a) :
    ∀ k, goodsteinSeq (a 0) k ≤ a k := by
  intro k
  induction k with
  | zero => exact Nat.le_of_eq rfl
  | succ k ih =>
    have hb : 2 ≤ base k := Nat.le_add_left 2 k
    have hmono : bump (base k) (goodsteinSeq (a 0) k) ≤ bump (base k) (a k) :=
      bump_mono (base k) hb ih
    have hstep : goodsteinSeq (a 0) (k + 1) = bump (base k) (goodsteinSeq (a 0) k) - 1 := rfl
    have hak := ha k
    rw [hstep]; omega

/-- **The leading exponent of a Goodstein-like sequence is Goodstein-like.** If `a` is Goodstein-like
then so is `logSeq a = (k ↦ log_{base k} (a k))`. Per step: `log_step_ge` gives the recursion lower
bound at `bump (base k) (a k) − 1`, then monotonicity of `Nat.log` in its argument carries it through
`a (k+1) ≥ bump (base k) (a k) − 1`. This is the **level-up** that, iterated, climbs the ordinal
tower. Generalizes `leadExp_step_ge`. -/
theorem goodsteinLike_logSeq {a : ℕ → ℕ} (ha : GoodsteinLike a) : GoodsteinLike (logSeq a) := by
  intro k
  have hb : 2 ≤ base k := Nat.le_add_left 2 k
  have hbb1 : base (k + 1) = base k + 1 := by simp only [base]
  show bump (base k) (Nat.log (base k) (a k)) - 1 ≤ Nat.log (base (k + 1)) (a (k + 1))
  rw [hbb1]
  exact le_trans (log_step_ge (base k) hb (a k)) (Nat.log_mono_right (ha k))

/-- The `j`-fold iterated leading exponent of a Goodstein-like sequence is Goodstein-like. -/
theorem goodsteinLike_iterate {a : ℕ → ℕ} (ha : GoodsteinLike a) (j : ℕ) :
    GoodsteinLike (logSeq^[j] a) := by
  induction j with
  | zero => exact ha
  | succ j ih => rw [Function.iterate_succ_apply']; exact goodsteinLike_logSeq ih

/-- The seed of the `j`-fold iterated leading exponent is the `j`-fold logarithm of the original seed:
`(logSeq^[j] a) 0 = (log₂)^[j] (a 0)` (each `logSeq` reads `base 0 = 2` at index `0`). -/
theorem logSeq_iterate_zero (a : ℕ → ℕ) (j : ℕ) :
    (logSeq^[j] a) 0 = (Nat.log 2)^[j] (a 0) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    show Nat.log (base 0) ((logSeq^[j] a) 0) = Nat.log 2 ((Nat.log 2)^[j] (a 0))
    rw [show base 0 = 2 from rfl, ih]

/-- **The self-similarity TOWER (headline).** The `j`-fold iterated leading exponent of the seed-`m`
Goodstein descent dominates the Goodstein sequence seeded at the `j`-fold logarithm `(log₂)^[j] m`:
`goodsteinSeq ((log₂)^[j] m) k ≤ (logSeq^[j] (goodsteinSeq m)) k`.

* `j = 0`: the value bound `goodsteinSeq m k ≤ goodsteinSeq m k` (trivial).
* `j = 1`: lap-9's `leadExp_ge_goodsteinSeq_log` — the leading exponent dominates `goodsteinSeq (log₂ m)`.
* `j ≥ 2`: each level is one ordinal step up. To certify the descent ordinal `≥ ω^{ω^{···}}` (tower
  of height `j+1`, i.e. `o = ω^j`-flavoured) at step `≈ m`, one needs the `j`-th iterated leading
  exponent `≥ base` there, which via this bound needs `goodsteinSeq ((log₂)^[j] m) (m−2) ≥ m`, i.e. a
  length bound `goodsteinLength ((log₂)^[j] m) ≥ 2m`. The deeper seed `(log₂)^[j] m` is small, so this
  needs an increasingly strong length bound — supplied by *bootstrapping the domination already
  proved* (e.g. `f_ω(t) ≤ goodsteinLength t + 2` makes `goodsteinLength ((log₂)^[2] m) ≥ f_ω(log₂log₂m)
  ≫ 2m`). That bootstrap is the next frontier; this lemma is its reusable backbone. -/
theorem iterLeadExp_dominates (m j : ℕ) :
    ∀ k, goodsteinSeq ((Nat.log 2)^[j] m) k ≤ (logSeq^[j] (goodsteinSeq m)) k := by
  have hgl : GoodsteinLike (logSeq^[j] (goodsteinSeq m)) :=
    goodsteinLike_iterate (goodsteinSeq_goodsteinLike m) j
  have hgz : goodsteinSeq m 0 = m := rfl
  have h0 : (logSeq^[j] (goodsteinSeq m)) 0 = (Nat.log 2)^[j] m := by
    rw [logSeq_iterate_zero, hgz]
  intro k
  have hd := hgl.dominates k
  rwa [h0] at hd

/-- Anti-vacuity: at `j = 1` the tower reproduces lap-9's self-similarity verbatim. -/
example (m k : ℕ) :
    goodsteinSeq (Nat.log 2 m) k ≤ Nat.log (base k) (goodsteinSeq m k) :=
  iterLeadExp_dominates m 1 k


-- ════════════════ ported: DominationBaseCases.lean ════════════════
/-
# Cichoń's lower bound at finite levels: the unconditional closure

`Logic/Goodstein/Domination.lean` reduces the diagonal domination
`fastGrowing (ofNat n) m ≤ goodsteinLength m + 2` to **one** self-referential length bound
`goodsteinLength m ≥ 2^{m+1} + m` (`goodsteinLength_exp_lower`), via the self-similarity recursion
`leadExp_ge_goodsteinSeq_log` (the leading-exponent sequence dominates the Goodstein sequence one
scale down). That strong induction needs finitely many computational base cases — the seeds
`4 ≤ M < 16`, where the length must already be exponentially large. This file discharges them
**kernel-only** (lap 211): `le_bump` bounds the per-step drop by 1, so a checkpoint value `v` at
step `k` certifies `goodsteinLength ≥ k + v` (`glen_ge_of_seq_value`); every seed reaches the
needed `2^{M+1}+M` by step `k ≤ 4`, and the checkpoint is evaluated in the kernel by the fuel-based
structural evaluator `gvalF`/`bumpF`. The formerly-needed `native_decide` forward passes (heaviest:
a 65551-step pass for `M = 15`) are gone, so the unconditional theorems below sit on the standard
`[propext, Classical.choice, Quot.sound]` with NO `Lean.ofReduceBool`.
-/



/-- Fuel-based structural clone of `bump` (kernel-reducible). `fuel ≥ n` suffices. -/
def bumpF : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | fuel + 1, b, n =>
    if n = 0 then 0
    else
      n / b ^ Nat.log b n * (b + 1) ^ bumpF fuel b (Nat.log b n)
        + bumpF fuel b (n % b ^ Nat.log b n)

theorem bumpF_eq : ∀ fuel n, n ≤ fuel → ∀ b, bumpF fuel b n = bump b n := by
  intro fuel
  induction fuel with
  | zero =>
    intro n hn b
    have hn0 : n = 0 := by omega
    subst hn0
    rw [bumpF, bump]
    simp
  | succ fuel ih =>
    intro n hn b
    rw [bumpF, bump]
    by_cases h0 : n = 0
    · simp [h0]
    · rw [dif_neg h0, if_neg h0]
      have hlog : Nat.log b n ≤ fuel := by
        have := Nat.log_lt_self b h0; omega
      have hmod : n % b ^ Nat.log b n ≤ fuel := by
        have hb : 0 < b ^ Nat.log b n := by
          rcases Nat.eq_zero_or_pos b with hb0 | hbpos
          · subst hb0; simp [Nat.log_zero_left]
          · exact Nat.pow_pos hbpos
        have := Nat.mod_lt n hb
        have := Nat.pow_log_le_self b h0
        omega
      rw [ih _ hlog, ih _ hmod]

/-- Kernel-reducible forward Goodstein evaluator: value after `s` more steps from `(k, v)`. -/
def gvalF : ℕ → ℕ → ℕ → ℕ
  | _, v, 0 => v
  | k, v, s + 1 => gvalF (k + 1) (bumpF v (base k) v - 1) s

theorem gvalF_goodstein (M : ℕ) : ∀ s k, gvalF k (goodsteinSeq M k) s = goodsteinSeq M (k + s) := by
  intro s
  induction s with
  | zero => intro k; rfl
  | succ s ih =>
    intro k
    rw [gvalF, bumpF_eq _ _ le_rfl]
    have hstep : bump (base k) (goodsteinSeq M k) - 1 = goodsteinSeq M (k + 1) := rfl
    rw [hstep, ih (k + 1)]
    congr 1; omega

/-- Zero is absorbing for the Goodstein sequence. -/
theorem goodsteinSeq_zero_absorb (M : ℕ) {n : ℕ} (h : goodsteinSeq M n = 0) :
    ∀ i, goodsteinSeq M (n + i) = 0 := by
  intro i
  induction i with
  | zero => exact h
  | succ i ih =>
    show bump (base (n + i)) (goodsteinSeq M (n + i)) - 1 = 0
    rw [ih, bump]; simp

/-- **Survival from any checkpoint**: the sequence drops by at most 1 per step, so a value `v`
at step `k` certifies `goodsteinLength M ≥ k + v`. -/
theorem glen_ge_of_seq_value {M k v : ℕ} (hv : 1 ≤ v) (h : goodsteinSeq M k = v) :
    k + v ≤ goodsteinLength M := by
  have hsub : ∀ j, v - j ≤ goodsteinSeq M (k + j) := by
    intro j
    induction j with
    | zero => rw [Nat.add_zero, h]; omega
    | succ j ih =>
      have hb : goodsteinSeq M (k + j) ≤ bump (base (k + j)) (goodsteinSeq M (k + j)) :=
        le_bump (base (k + j)) (Nat.le_add_left 2 _) _
      have : goodsteinSeq M (k + (j + 1)) = bump (base (k + j)) (goodsteinSeq M (k + j)) - 1 := by
        rw [show k + (j + 1) = (k + j) + 1 from by omega]; rfl
      omega
  rw [goodsteinLength, Nat.le_find_iff]
  intro n hn hzero
  rcases Nat.lt_or_ge n k with hnk | hnk
  · have := goodsteinSeq_zero_absorb M hzero (k - n)
    rw [show n + (k - n) = k from by omega, h] at this; omega
  · have := hsub (n - k)
    rw [show k + (n - k) = n from by omega, hzero] at this; omega

/-- **The finitely many base cases of Cichoń's exponential length bound** (`4 ≤ M < 16`):
`2^{M+1} + M ≤ goodsteinLength M`, each discharged **kernel-only**: `le_bump` gives a per-step
drop of at most 1, so a checkpoint value at step `k ≤ 4` (computed in the kernel by the
fuel-based evaluator `gvalF`) certifies the whole exponential bound (`glen_ge_of_seq_value`).
No `native_decide` — the former 65551-step forward pass (`M = 15`) is replaced by a 4-step
kernel evaluation reaching value `326593`. -/
theorem goodsteinLength_base_cases (M : ℕ) (h4 : 4 ≤ M) (h16 : M < 16) :
    2 ^ (M + 1) + M ≤ goodsteinLength M := by
  have hM : M = 4 ∨ M = 5 ∨ M = 6 ∨ M = 7 ∨ M = 8 ∨ M = 9 ∨ M = 10 ∨ M = 11 ∨ M = 12 ∨
      M = 13 ∨ M = 14 ∨ M = 15 := by omega
  have key : ∀ (m k v : ℕ), 1 ≤ v → gvalF 0 m k = v → 2 ^ (m + 1) + m ≤ k + v →
      2 ^ (m + 1) + m ≤ goodsteinLength m := by
    intro m k v hv hval hle
    have := gvalF_goodstein m k 0
    rw [Nat.zero_add] at this
    exact le_trans hle (glen_ge_of_seq_value hv (by rw [← this]; exact hval))
  rcases hM with h | h | h | h | h | h | h | h | h | h | h | h <;> subst h
  · exact key 4 2 41 (by omega) (by decide) (by norm_num)
  · exact key 5 2 255 (by omega) (by decide) (by norm_num)
  · exact key 6 2 257 (by omega) (by decide) (by norm_num)
  · exact key 7 3 3127 (by omega) (by decide) (by norm_num)
  · exact key 8 2 553 (by omega) (by decide) (by norm_num)
  · exact key 9 3 9842 (by omega) (by decide) (by norm_num)
  · exact key 10 3 15625 (by omega) (by decide) (by norm_num)
  · exact key 11 3 15627 (by omega) (by decide) (by norm_num)
  · exact key 12 3 15685 (by omega) (by decide) (by norm_num)
  · exact key 13 4 280711 (by omega) (by decide) (by norm_num)
  · exact key 14 4 326591 (by omega) (by decide) (by norm_num)
  · exact key 15 4 326593 (by omega) (by decide) (by norm_num)

/-- **Cichoń's exponential length lower bound, UNCONDITIONAL:** `2^{m+1} + m ≤ goodsteinLength m` for
every `m ≥ 4`. The strong-induction engine `goodsteinLength_exp_lower` fed by the computational base
cases. The self-similarity makes the exponential bound reproduce itself at each scale. -/
theorem goodsteinLength_exp_lower_uncond {m : ℕ} (hm : 4 ≤ m) :
    2 ^ (m + 1) + m ≤ goodsteinLength m :=
  goodsteinLength_exp_lower goodsteinLength_base_cases m hm

/-- **THE `o = 2` DIAGONAL DOMINATION — UNCONDITIONAL (every `m ≥ 16`):**
`fastGrowing 2 m ≤ goodsteinLength m + 2`, i.e. `f_2(m) = 2^m · m ≤ goodsteinLength m + 2`. This is the
*true diagonal* bound — budget `m`, not the earlier `log₂ m` of `fastGrowing_two_log_le_goodsteinLength`
— hence Cichoń's lower bound at level `o = 2`, fully machine-checked: the Goodstein descent's leading
CNF exponent provably stays `≥ 2` for the first `m` steps. Assembly: for `m ≥ 16` the smaller seed
`L = Nat.log 2 m` is `≥ 4`, so the unconditional exponential length bound gives
`goodsteinLength L ≥ 2^{L+1} + L ≥ m + 2` (as `m < 2^{L+1}`), discharging the hypothesis of
`fastGrowing_two_le_goodsteinLength_of_log_length`. (The finite tail `4 ≤ m < 16` also holds but its
direct certification is far more expensive — `f_2(15) ≈ 5·10^5` steps — and is omitted: asymptotic
domination is the mathematically meaningful statement.) -/
theorem fastGrowing_two_le_goodsteinLength {m : ℕ} (hm : 16 ≤ m) :
    fastGrowing 2 m ≤ goodsteinLength m + 2 := by
  have hL4 : 4 ≤ Nat.log 2 m := by
    calc 4 = Nat.log 2 16 := by rw [show (16 : ℕ) = 2 ^ 4 from rfl, Nat.log_pow (by norm_num)]
      _ ≤ Nat.log 2 m := Nat.log_mono_right hm
  have hexp := goodsteinLength_exp_lower_uncond (m := Nat.log 2 m) hL4
  have hpow : m + 1 ≤ 2 ^ (Nat.log 2 m + 1) := by
    have := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) m; omega
  have hlen : m + 2 ≤ goodsteinLength (Nat.log 2 m) := by omega
  exact fastGrowing_two_le_goodsteinLength_of_log_length (by omega) hlen

/-- **THE FULL DIAGONAL DOMINATION — UNCONDITIONAL, every finite level `n`:**
`fastGrowing (ofNat n) m ≤ goodsteinLength m + 2` whenever `n + 1 ≤ Nat.log 2 m` (and `m ≥ 16`).
For each fixed `n` this holds for all sufficiently large `m` (those with `Nat.log 2 m ≥ n + 1`, i.e.
`m ≥ 2^{n+1}`). This is **Cichoń's lower bound at every finite level**, fully machine-checked: the
Goodstein descent's leading CNF exponent provably stays `≥ n` for the first `m` steps, so
`goodsteinLength` diagonally dominates the entire finite fast-growing hierarchy `f_0, f_1, f_2, …`.
The unconditional exponential length bound at the smaller seed `L = Nat.log 2 m` supplies
`goodsteinLength L ≥ 2^{L+1} + L ≥ m + n` (using `m < 2^{L+1}` and `n ≤ L − 1`), discharging the
hypothesis of `fastGrowing_ofNat_le_goodsteinLength_of_log_length`. -/
theorem fastGrowing_ofNat_le_goodsteinLength {n m : ℕ} (hm : 16 ≤ m)
    (hn : n + 1 ≤ Nat.log 2 m) :
    fastGrowing (ONote.ofNat n) m ≤ goodsteinLength m + 2 := by
  have hL4 : 4 ≤ Nat.log 2 m := by
    calc 4 = Nat.log 2 16 := by rw [show (16 : ℕ) = 2 ^ 4 from rfl, Nat.log_pow (by norm_num)]
      _ ≤ Nat.log 2 m := Nat.log_mono_right hm
  have hexp := goodsteinLength_exp_lower_uncond (m := Nat.log 2 m) hL4
  have hpow : m + 1 ≤ 2 ^ (Nat.log 2 m + 1) := by
    have := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) m; omega
  have hloglt : Nat.log 2 m < m := Nat.log_lt_self 2 (by omega)
  have hlen : m + n ≤ goodsteinLength (Nat.log 2 m) := by omega
  exact fastGrowing_ofNat_le_goodsteinLength_of_log_length (by omega) (by omega) hlen

/-- Anti-vacuity: the diagonal bound is non-trivial — `f_n` is astronomically large at its argument.
`f_2(16) = 2^16 · 16 = 1048576`, yet `≤ goodsteinLength 16 + 2`. (Not `native_decide`-able — RHS is
beyond astronomical — but `f_2(16)` itself is, witnessing the LHS is a genuine fast-growing value.) -/
example : fastGrowing 2 16 = 2 ^ 16 * 16 := by rw [ONote.fastGrowing_two]


-- ════════════════ ported: DominationOmega.lean ════════════════
/-
# Toward `o = ω`: the limit-level diagonal, isolated to its crux

With the finite-level diagonal `f_n(m) ≤ goodsteinLength m + 2` closed
(`DominationBaseCases.lean`), the next tier of Cichoń's lower bound is the **limit ordinal `ω`**:
`f_ω(m) ≤ goodsteinLength m + 2`. This file builds the ordinal bridge for `ω^ω` and reduces the
`o = ω` diagonal to a single open hypothesis — exactly the way `Domination.lean`'s
`goodstein_dominates_of_index` framed the finite levels in lap 6.

The crux it isolates: the descent's **leading exponent stays in the LARGE regime** (`≥ base`) at step
`m − 2`. For finite `o = n` we only needed `leadExp ≥ n` (a fixed constant); for `o = ω` we need
`leadExp ≥ base = m`, i.e. the leading exponent itself reaches `ω` at the ordinal level. This is one
recursion deeper than the lap-9 self-similarity (see `PENDING_WORK.md` → "NEXT FRONTIER"), and is the
genuine remaining growth content — NOT to be axiomatized.
-/



/-- **The general ordinal bridge (unifies every level).** For any ordinal `β`, if the descent's
leading CNF exponent ordinal `toOrdinal (base i) (leadExp_i)` dominates `β`, then the descent ordinal
dominates `ω^β`: `ω^β ≤ (seqONote m i).repr`. Just `opow_le_opow_right` (monotonicity of `ω^·`) chained
with `opow_toOrdinal_log_le` (the leading term `ω^{toOrdinal b (log_b v)}` is `≤ toOrdinal b v`). Every
level-specific bridge below (`ω^k`, `ω^ω`, `ω^{ω^j}`, `ω^{ω^ω}`) is this lemma fed a `toOrdinal` lower
bound on the leading exponent — and the next tier (`ε₀`) will be too. -/
theorem opow_le_seqONote_repr_of_toOrdinal {m i : ℕ} {β : Ordinal}
    (hβ : β ≤ toOrdinal (base i) (Nat.log (base i) (goodsteinSeq m i)))
    (hv : goodsteinSeq m i ≠ 0) :
    (ω : Ordinal) ^ β ≤ (seqONote m i).repr := by
  have hb : 2 ≤ base i := Nat.le_add_left 2 i
  rw [repr_seqONote]
  calc (ω : Ordinal) ^ β
      ≤ ω ^ toOrdinal (base i) (Nat.log (base i) (goodsteinSeq m i)) :=
        opow_le_opow_right omega0_pos hβ
    _ ≤ toOrdinal (base i) (goodsteinSeq m i) := opow_toOrdinal_log_le (base i) hb hv

/-- **Ordinal bridge for `ω^ω`.** If the leading exponent of `G_i` is in the *large regime*
(`base i ≤ log_{base i} G_i`), the descent ordinal dominates `ω^ω`: the leading CNF exponent
`toOrdinal (base i) (leadExp)` is then `≥ toOrdinal (base i) (base i) = ω`, so the leading term is
`≥ ω^ω`. The `ω`-level analog of `opow_le_seqONote_repr` (which handled finite exponents `ω^k`). -/
theorem omega_omega_le_seqONote_repr {m i : ℕ}
    (hreg : base i ≤ Nat.log (base i) (goodsteinSeq m i)) (hv : goodsteinSeq m i ≠ 0) :
    (ω : Ordinal) ^ (ω : Ordinal) ≤ (seqONote m i).repr := by
  have hb : 2 ≤ base i := Nat.le_add_left 2 i
  have h1 : toOrdinal (base i) 1 = 1 := by
    have h := toOrdinal_pow (base i) hb 0; simpa using h
  have hbb : toOrdinal (base i) (base i) = ω := by
    have h := toOrdinal_pow (base i) hb 1
    rw [pow_one, h1, opow_one] at h; exact h
  have hSM : StrictMono (toOrdinal (base i)) := fun a c hac =>
    (toOrdinal_mono_and_bound (base i) hb c).1 a hac
  have homega_le : (ω : Ordinal) ≤ toOrdinal (base i) (Nat.log (base i) (goodsteinSeq m i)) := by
    rw [← hbb]; exact hSM.monotone hreg
  exact opow_le_seqONote_repr_of_toOrdinal homega_le hv

/-- **The `o = ω` diagonal domination, REDUCED to its crux** (`hreg`). If the Goodstein descent's
leading exponent is still in the LARGE regime at step `m − 2` (`base (m−2) ≤ leadExp_{m−2}`), then
`fastGrowing ω m ≤ goodsteinLength m + 2` (with `ω = oadd 1 1 0`). Assembly mirrors the finite-level
`fastGrowing_ofNat_le_goodsteinLength_of_log_length`: the large-regime hypothesis gives
`ω^ω ≤ (seqONote m (m−2)).repr` (`omega_omega_le_seqONote_repr`); the diagonal reduction
`goodstein_dominates_of_index_le` (budget `m`) closes it. **The hypothesis `hreg` IS Cichoń's lower
bound at the limit level `ω`** — the open obligation for the next lap (route (a) in `PENDING_WORK.md`:
iterate the self-similarity so the one-level-down value stays `≥ base` for `~m` steps). -/
theorem fastGrowing_omega_le_goodsteinLength_of_largeRegime {m : ℕ} (hm : 4 ≤ m)
    (hreg : base (m - 2) ≤ Nat.log (base (m - 2)) (goodsteinSeq m (m - 2))) :
    fastGrowing (oadd 1 1 0) m ≤ goodsteinLength m + 2 := by
  set j := m - 2 with hj
  have ho : (oadd 1 1 0 : ONote).NF := by decide
  have hv : goodsteinSeq m j ≠ 0 := by have := goodsteinSeq_ge_init m j (by omega); omega
  have hidx : (oadd (oadd 1 1 0) 1 0).repr ≤ (seqONote m j).repr := by
    have hr : (oadd (oadd 1 1 0) 1 0 : ONote).repr = ω ^ (ω : Ordinal) := by simp [ONote.repr]
    rw [hr]; exact omega_omega_le_seqONote_repr hreg hv
  have hnorm : norm (oadd 1 1 0 : ONote) ≤ j + 2 := by
    have : norm (oadd 1 1 0 : ONote) = 1 := by decide
    omega
  have hgl : j ≤ goodsteinLength m := le_trans (by omega) (le_goodsteinLength m)
  exact goodstein_dominates_of_index_le (o := oadd 1 1 0) (m := m) (j := j) ho hgl (by omega) hnorm hidx

/-- **Doubly-iterated length bound — the `ω`-level analog of `goodsteinLength_exp_lower`.** For every
`m ≥ 2^16` the *one-level-down* Goodstein sequence (seed `L = Nat.log 2 m`) runs at least `2m − 2`
steps: `2 * m ≤ goodsteinLength (Nat.log 2 m) + 2`. The finite-level diagonal used the *exponential*
length bound `goodsteinLength M ≥ 2^{M+1}+M` at the smaller seed; that gives only `≈ m` and cannot
push the leading exponent past a fixed constant. The limit level needs more, so this lemma applies the
full unconditional **`o = 2` diagonal** `2^L·L = f_2(L) ≤ goodsteinLength L + 2`
(`fastGrowing_two_le_goodsteinLength`) at the seed `L ≥ 16`: since `m < 2^{L+1}` we have
`2·2^L ≥ m+1`, so `2^L·L ≥ 16·2^L = 8·(2·2^L) ≥ 8(m+1) ≥ 2m`. The surplus over the seed is exactly
what lifts the leading exponent into the LARGE regime (`≥ base`), discharging `hreg` below. -/
theorem two_mul_le_goodsteinLength_log {m : ℕ} (hm : 2 ^ 16 ≤ m) :
    2 * m ≤ goodsteinLength (Nat.log 2 m) + 2 := by
  have hL16 : 16 ≤ Nat.log 2 m := Nat.le_log_of_pow_le Nat.one_lt_two hm
  have hf2 := fastGrowing_two_le_goodsteinLength (m := Nat.log 2 m) hL16
  simp only [ONote.fastGrowing_two] at hf2
  set L := Nat.log 2 m with hLdef
  set P := 2 ^ L with hPdef
  have hpow : m + 1 ≤ 2 ^ (L + 1) := by
    have h := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) m
    rw [← hLdef] at h; omega
  have hpowsucc : (2 : ℕ) ^ (L + 1) = P * 2 := by rw [hPdef, pow_succ]
  rw [hpowsucc] at hpow
  have hmono : P * 16 ≤ P * L := Nat.mul_le_mul (le_refl P) hL16
  -- hf2 : P * L ≤ goodsteinLength L + 2 ;  hmono : P*16 ≤ P*L ;  hpow : m+1 ≤ P*2
  omega

/-- **THE `o = ω` DIAGONAL DOMINATION — UNCONDITIONAL (every `m ≥ 2^16`):**
`fastGrowing ω m ≤ goodsteinLength m + 2`, i.e. `f_ω(m) ≤ goodsteinLength m + 2`, with
`ω = oadd 1 1 0`. This is Cichoń's lower bound at the **first limit ordinal** — the leading CNF
exponent of the Goodstein descent provably reaches `ω` (the LARGE regime `≥ base`) and stays there
through step `m − 2`, so the descent ordinal dominates `ω^ω`.

The crux `hreg` (leading exponent `≥ base (m−2) = m` at step `m − 2`) is discharged by **iterating
the self-similarity once more**: `leadExp_ge_goodsteinSeq_log` bounds the leading exponent below by
the *one-level-down* Goodstein value `goodsteinSeq (log₂ m) (m−2)`, and `n_le_goodsteinSeq` keeps that
value `≥ m` provided the one-level-down sequence still has `≥ m` steps to run — supplied by the
doubly-iterated length bound `two_mul_le_goodsteinLength_log` (`goodsteinLength (log₂ m) ≥ 2m − 2`).
For finite `o = n` the analog only needed value `≥ n` (a constant); the jump to `o = ω` is precisely
the jump from "value `≥ n`" to "value `≥ base = m`", which the *factor-of-two* surplus in the length
bound provides. The whole reduction is then closed by `fastGrowing_omega_le_goodsteinLength_of_largeRegime`. -/
theorem fastGrowing_omega_le_goodsteinLength {m : ℕ} (hm : 2 ^ 16 ≤ m) :
    fastGrowing (oadd 1 1 0) m ≤ goodsteinLength m + 2 := by
  have h4 : 4 ≤ m := le_trans (by norm_num) hm
  apply fastGrowing_omega_le_goodsteinLength_of_largeRegime h4
  -- hreg : base (m - 2) ≤ Nat.log (base (m - 2)) (goodsteinSeq m (m - 2))
  have hbase : base (m - 2) = m := by simp only [base]; omega
  have hlen : (m - 2) + m ≤ goodsteinLength (Nat.log 2 m) := by
    have := two_mul_le_goodsteinLength_log hm; omega
  calc base (m - 2)
      = m := hbase
    _ ≤ goodsteinSeq (Nat.log 2 m) (m - 2) :=
        n_le_goodsteinSeq (Nat.log 2 m) (m - 2) m hbase.ge hlen
    _ ≤ Nat.log (base (m - 2)) (goodsteinSeq m (m - 2)) := leadExp_ge_goodsteinSeq_log m (m - 2)

/-! ### Toward `o = ω^j`: the SECOND-level tower (next limit tier of Cichoń)

`o = ω` needed the leading exponent in the LARGE regime (`leadExp ≥ base`). The next tier `o = ω^j`
needs the *second-level* leading exponent `≥ j` — equivalently the leading exponent `≥ base^j` — at
step `m − 2`. We build the general ordinal bridge and reduce `o = ω^j` to a single length bound on the
*doubly-iterated* seed `(log₂)^[2] m`, via the self-similarity tower `iterLeadExp_dominates`. -/

/-- **`ω^k ≤ toOrdinal b w`** from the leading exponent `log_b w ≥ k` (with `k < b`, `w ≠ 0`). The
`toOrdinal`-level core of `opow_le_seqONote_repr`, factored out so it applies at the *second* level
(to the leading exponent itself) — the brick of the `ω^j` tower. -/
theorem opow_le_toOrdinal (b : ℕ) (hb : 2 ≤ b) {w k : ℕ}
    (hk : k ≤ Nat.log b w) (hw : w ≠ 0) (hkb : k < b) :
    (ω : Ordinal) ^ (k : Ordinal) ≤ toOrdinal b w := by
  have htk : toOrdinal b k = (k : Ordinal) := by
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · subst hk0; simp
    · have hlog0 : Nat.log b k = 0 := Nat.log_eq_zero_iff.2 (Or.inl hkb)
      rw [toOrdinal_pos b k (by omega), hlog0]
      simp [pow_zero, Nat.div_one, Nat.mod_one, toOrdinal_zero]
  have hmono : toOrdinal b k ≤ toOrdinal b (Nat.log b w) := by
    rcases eq_or_lt_of_le hk with h | h
    · rw [h]
    · exact le_of_lt ((toOrdinal_mono_and_bound b hb _).1 k h)
  calc (ω : Ordinal) ^ (k : Ordinal) = ω ^ toOrdinal b k := by rw [htk]
    _ ≤ ω ^ toOrdinal b (Nat.log b w) := opow_le_opow_right omega0_pos hmono
    _ ≤ toOrdinal b w := opow_toOrdinal_log_le b hb hw

/-- **Level-2 ordinal bridge: `ω^{ω^j} ≤ descent`.** If the SECOND-level leading exponent is `≥ j`
(`j ≤ log_{base i}(log_{base i} G_i)`), with `j < base i` and the value/leading-exponent nonzero, the
Goodstein descent ordinal dominates `ω^{ω^j}`. Applies `opow_le_toOrdinal` to the leading exponent
(`ω^j ≤ toOrdinal (base i)(leadExp)`), then `opow_toOrdinal_log_le` once more. The `ω^j`-flavoured
analog of `omega_omega_le_seqONote_repr` (the `j` "= base", `ω^ω` case). -/
theorem omega_pow_pow_le_seqONote_repr {m i j : ℕ}
    (hj : j ≤ Nat.log (base i) (Nat.log (base i) (goodsteinSeq m i)))
    (hjb : j < base i) (hv : goodsteinSeq m i ≠ 0)
    (hlead : Nat.log (base i) (goodsteinSeq m i) ≠ 0) :
    (ω : Ordinal) ^ ((ω : Ordinal) ^ (j : Ordinal)) ≤ (seqONote m i).repr := by
  have hb : 2 ≤ base i := Nat.le_add_left 2 i
  exact opow_le_seqONote_repr_of_toOrdinal (opow_le_toOrdinal (base i) hb hj hlead hjb) hv

/-- **The `o = ω^j` diagonal, REDUCED to its second-level crux.** For finite `j ≥ 1`, if the SECOND
leading exponent of the seed-`m` descent is `≥ j` at step `m − 2`, then
`fastGrowing (ω^j) m ≤ goodsteinLength m + 2` with `ω^j = oadd (ofNat j) 1 0` (`repr = ω^j`). Mirrors
`fastGrowing_omega_le_goodsteinLength_of_largeRegime` one level up: `omega_pow_pow_le_seqONote_repr`
gives `ω^{ω^j} ≤ descent`; `goodstein_dominates_of_index_le` (budget `m`) closes it. `hreg2` is
Cichoń's lower bound at the level `ω^j`. -/
theorem fastGrowing_omega_pow_le_goodsteinLength_of_crux {m j : ℕ} (hm : 4 ≤ m) (hj1 : 1 ≤ j)
    (hjm : j < m)
    (hreg2 : j ≤ Nat.log (base (m - 2)) (Nat.log (base (m - 2)) (goodsteinSeq m (m - 2)))) :
    fastGrowing (oadd (ONote.ofNat j) 1 0) m ≤ goodsteinLength m + 2 := by
  set i := m - 2 with hi
  have hbase : base i = m := by simp only [base, hi]; omega
  have ho : (oadd (ONote.ofNat j) 1 0 : ONote).NF := NF.oadd inferInstance 1 NFBelow.zero
  have hv : goodsteinSeq m i ≠ 0 := by have := goodsteinSeq_ge_init m i (by omega); omega
  have hjb : j < base i := by rw [hbase]; exact hjm
  have hlead : Nat.log (base i) (goodsteinSeq m i) ≠ 0 := by
    intro h0; rw [h0, Nat.log_zero_right] at hreg2; omega
  have hidx : (oadd (oadd (ONote.ofNat j) 1 0) 1 0).repr ≤ (seqONote m i).repr := by
    have hr : (oadd (oadd (ONote.ofNat j) 1 0) 1 0 : ONote).repr
        = ω ^ ((ω : Ordinal) ^ (j : Ordinal)) := by
      simp [ONote.repr, ONote.repr_ofNat]
    rw [hr]
    exact omega_pow_pow_le_seqONote_repr hreg2 hjb hv hlead
  have hnorm : norm (oadd (ONote.ofNat j) 1 0) ≤ i + 2 := by
    rw [norm_oadd, norm_ofNat, norm_zero]; simp only [PNat.one_coe]; omega
  have hgl : i ≤ goodsteinLength m := le_trans (by omega) (le_goodsteinLength m)
  exact goodstein_dominates_of_index_le ho hgl (by omega) hnorm hidx

/-- **The `o = ω^j` diagonal, REDUCED to a doubly-iterated length bound.** For finite `j ≥ 1`, if the
*doubly-iterated* seed `(log₂)^[2] m` has a Goodstein length `≥ (m−2)+j`, then
`fastGrowing (ω^j) m ≤ goodsteinLength m + 2`. The second-level crux `hreg2` is discharged by the
self-similarity tower (`iterLeadExp_dominates m 2`): the second leading exponent at step `m−2`
dominates `goodsteinSeq ((log₂)^[2] m) (m−2)`, which `n_le_goodsteinSeq` keeps `≥ j` exactly when the
doubly-iterated sequence still has `≥ j` steps to run. This is the limit-level analog of
`fastGrowing_omega_le_goodsteinLength_of_largeRegime` reduced one more scale down: the SOLE remaining
obligation is the length bound `goodsteinLength ((log₂)^[2] m) ≥ m` (next-lap crux — needs an
`f_ω`-strength lower bound at the deep seed, bootstrapped from `fastGrowing_omega_le_goodsteinLength`
itself). -/
theorem fastGrowing_omega_pow_le_goodsteinLength_of_length {m j : ℕ} (hm : 4 ≤ m) (hj1 : 1 ≤ j)
    (hjm : j < m)
    (hlen : (m - 2) + j ≤ goodsteinLength ((Nat.log 2)^[2] m)) :
    fastGrowing (oadd (ONote.ofNat j) 1 0) m ≤ goodsteinLength m + 2 := by
  apply fastGrowing_omega_pow_le_goodsteinLength_of_crux hm hj1 hjm
  have hbase : base (m - 2) = m := by simp only [base]; omega
  have hval : j ≤ goodsteinSeq ((Nat.log 2)^[2] m) (m - 2) :=
    n_le_goodsteinSeq ((Nat.log 2)^[2] m) (m - 2) j (by rw [hbase]; omega) hlen
  have hdom := iterLeadExp_dominates m 2 (m - 2)
  exact le_trans hval hdom

/-! ### Discharging the `o = ω^j` crux: an `f_ω`-strength length bound at the deep seed

The sole remaining obligation is `goodsteinLength ((log₂)^[2] m) ≥ m`. The exponential length bound is
far too weak at the doubly-iterated seed `t = (log₂)^[2] m` (it gives only `≈ 2^t`, while `m ≈ 2^{2^t}`).
But we now have `f_ω(t) ≤ goodsteinLength t + 2` — a *tower-strength* lower bound — and `f_ω` outgrows
`2^{2^{·}}`. Bootstrapping the `o = ω` result against itself closes the `o = ω^j` tier. -/

/-- `f_2(n) = 2^n · n` (mathlib's closed form, transported to the `ofNat 2` notation). -/
theorem fastGrowing_ofNat_two (n : ℕ) : fastGrowing (ONote.ofNat 2) n = 2 ^ n * n := by
  rw [show (ONote.ofNat 2 : ONote) = 2 from by decide, ONote.fastGrowing_two]

/-- **`f_3` is doubly-exponential:** `2^{2^t · t} ≤ f_3(t)` for `t ≥ 2`. Since `f_3(t) = (f_2)^[t](t)`
(`fastGrowing_succ`), and `f_2` is expansive, `(f_2)^[t](t) ≥ (f_2)^[2](t) = f_2(f_2(t)) =
2^{2^t·t}·(2^t·t) ≥ 2^{2^t·t}`. The engine that makes `f_ω` outrun `2^{2^{·}}`. -/
theorem two_pow_le_fastGrowing_ofNat_three {t : ℕ} (ht : 2 ≤ t) :
    2 ^ (2 ^ t * t) ≤ fastGrowing (ONote.ofNat 3) t := by
  have hf3 : fastGrowing (ONote.ofNat 3) t = (fastGrowing (ONote.ofNat 2))^[t] t := by
    rw [show (ONote.ofNat 3 : ONote) = ONote.ofNat (2 + 1) from rfl,
        fastGrowing_succ _ (fundamentalSequence_ofNat_succ 2)]
  have hexp : (id : ℕ → ℕ) ≤ fastGrowing (ONote.ofNat 2) := fun n => le_fastGrowing _ n
  have hmono : (fastGrowing (ONote.ofNat 2))^[2] t ≤ (fastGrowing (ONote.ofNat 2))^[t] t :=
    Function.monotone_iterate_of_id_le hexp ht t
  have h2it : (fastGrowing (ONote.ofNat 2))^[2] t
      = fastGrowing (ONote.ofNat 2) (fastGrowing (ONote.ofNat 2) t) := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, Function.iterate_add_apply]; simp
  rw [hf3]
  refine le_trans ?_ hmono
  rw [h2it, fastGrowing_ofNat_two, fastGrowing_ofNat_two]
  have hpos : 1 ≤ 2 ^ t * t := by
    have : 0 < 2 ^ t * t := Nat.mul_pos (pow_pos (by norm_num) t) (by omega); omega
  calc 2 ^ (2 ^ t * t) = 2 ^ (2 ^ t * t) * 1 := (mul_one _).symm
    _ ≤ 2 ^ (2 ^ t * t) * (2 ^ t * t) := by gcongr

/-- `f_ω(t) = f_{t+1}(t)`: the fundamental sequence of `ω = oadd 1 1 0` is `i ↦ ofNat (i+1)`. -/
theorem fastGrowing_omega_eq (t : ℕ) :
    fastGrowing (oadd 1 1 0) t = fastGrowing (ONote.ofNat (t + 1)) t := by
  have hfs : fundamentalSequence (oadd 1 1 0) = Sum.inr (fun i => ONote.ofNat (i + 1)) := rfl
  rw [fastGrowing_limit (oadd 1 1 0) hfs]

/-- **The doubly-iterated length bound — `o = ω^j`'s crux DISCHARGED.** For `m` with the doubly-
iterated seed `t = (log₂)^[2] m ≥ 2^16`, `goodsteinLength t ≥ 2m`. Bootstraps the `o = ω` domination
against itself: `goodsteinLength t ≥ f_ω(t) − 2 = f_{t+1}(t) − 2 ≥ f_3(t) − 2 ≥ 2^{2^t·t} − 2`
(`fastGrowing_omega_le_goodsteinLength` ⊕ `fastGrowing_ofNat_mono` ⊕ `two_pow_le_fastGrowing_ofNat_three`),
while `m < 2^{2^{t+1}}` and `2^t·t ≥ 2^{t+1}+1` (for `t ≥ 3`) give `2^{2^t·t} ≥ 2(m+1)`. The `f_ω`
length bound carries the finite-base-case `native_decide` axioms (documented split). -/
theorem two_mul_le_goodsteinLength_loglog {m : ℕ}
    (ht : 2 ^ 16 ≤ (Nat.log 2)^[2] m) :
    2 * m ≤ goodsteinLength ((Nat.log 2)^[2] m) := by
  set t := (Nat.log 2)^[2] m with htdef
  have hteq : t = Nat.log 2 (Nat.log 2 m) := rfl
  have hA : Nat.log 2 m + 1 ≤ 2 ^ (t + 1) := by
    have h := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) (Nat.log 2 m)
    rw [hteq]; omega
  have hB : m < 2 ^ (Nat.log 2 m + 1) := Nat.lt_pow_succ_log_self (by norm_num) m
  have hD : 2 ^ (Nat.log 2 m + 1) ≤ 2 ^ (2 ^ (t + 1)) := Nat.pow_le_pow_right (by norm_num) hA
  have hm1 : m + 1 ≤ 2 ^ (2 ^ (t + 1)) := by omega
  have hlen := fastGrowing_omega_le_goodsteinLength (m := t) ht
  rw [fastGrowing_omega_eq] at hlen
  have hidx : fastGrowing (ONote.ofNat 3) t ≤ fastGrowing (ONote.ofNat (t + 1)) t :=
    fastGrowing_ofNat_mono (by omega) (by omega)
  have hf3 := two_pow_le_fastGrowing_ofNat_three (t := t) (by omega)
  have hexp_ge : 2 ^ (t + 1) + 1 ≤ 2 ^ t * t := by
    have h2t : 2 ^ (t + 1) = 2 * 2 ^ t := by rw [pow_succ]; ring
    have hb : 2 ^ t * 3 ≤ 2 ^ t * t := by gcongr; omega
    have hp : 1 ≤ 2 ^ t := Nat.one_le_two_pow
    omega
  have hpow_ge : 2 * (m + 1) ≤ 2 ^ (2 ^ t * t) := by
    have h2 : 2 * 2 ^ (2 ^ (t + 1)) = 2 ^ (2 ^ (t + 1) + 1) := by rw [pow_succ]; ring
    have h3 : 2 ^ (2 ^ (t + 1) + 1) ≤ 2 ^ (2 ^ t * t) := Nat.pow_le_pow_right (by norm_num) hexp_ge
    omega
  omega

/-- **THE `o = ω^j` DIAGONAL DOMINATION — UNCONDITIONAL** (every finite `j ≥ 1`, for `m` with
`(log₂)^[2] m ≥ 2^16`): `fastGrowing (ω^j) m ≤ goodsteinLength m + 2`, with `ω^j = oadd (ofNat j) 1 0`.
Cichoń's lower bound at the limit levels `ω, ω^2, ω^3, …` — fully machine-checked. The doubly-iterated
length bound `two_mul_le_goodsteinLength_loglog` discharges the `of_length` reduction's hypothesis
(`(m−2)+j < 2m ≤ goodsteinLength ((log₂)^[2] m)`). Carries the finite-base-case `native_decide` axioms
(documented split), inherited through the `f_ω` bootstrap. -/
theorem fastGrowing_omega_pow_le_goodsteinLength {m j : ℕ}
    (ht : 2 ^ 16 ≤ (Nat.log 2)^[2] m) (hj1 : 1 ≤ j) (hjm : j < m) :
    fastGrowing (oadd (ONote.ofNat j) 1 0) m ≤ goodsteinLength m + 2 := by
  have h1' : 1 ≤ (Nat.log 2)^[2] m := le_trans (by norm_num) ht
  have hlm0 : Nat.log 2 m ≠ 0 := by
    intro h
    rw [show (Nat.log 2)^[2] m = Nat.log 2 (Nat.log 2 m) from rfl, h, Nat.log_zero_right] at h1'
    omega
  have hlogm2 : 2 ≤ Nat.log 2 m := by
    have h := Nat.pow_le_of_le_log hlm0 (show 1 ≤ Nat.log 2 (Nat.log 2 m) from h1'); simpa using h
  have hm0 : m ≠ 0 := by intro h; rw [h, Nat.log_zero_right] at hlogm2; omega
  have hm : 4 ≤ m := by have h := Nat.pow_le_of_le_log hm0 hlogm2; simpa using h
  apply fastGrowing_omega_pow_le_goodsteinLength_of_length hm hj1 hjm
  have h2m := two_mul_le_goodsteinLength_loglog ht
  omega

/-! ### `o = ω^ω`: the second LARGE-regime level (toward `ε₀`)

`o = ω^j` (finite `j`) needed the second leading exponent `≥ j` (a constant). The next genuine limit
`o = ω^ω` needs the second leading exponent in the *large* regime — `secondLeadExp ≥ base` — exactly
as `o = ω` needed the first. Remarkably the SAME doubly-iterated length bound `≥ 2m` already proved
discharges it (`n_le_goodsteinSeq` with `n = m` at step `m−2`, budget `2m−2 ≤ 2m`). -/

/-- **`ω^ω ≤ toOrdinal b w`** from the leading exponent in the LARGE regime (`b ≤ log_b w`). The
`toOrdinal`-level core of `omega_omega_le_seqONote_repr`, factored to apply at the *second* level. -/
theorem omega_omega_le_toOrdinal (b : ℕ) (hb : 2 ≤ b) {w : ℕ}
    (hreg : b ≤ Nat.log b w) (hw : w ≠ 0) :
    (ω : Ordinal) ^ (ω : Ordinal) ≤ toOrdinal b w := by
  have h1 : toOrdinal b 1 = 1 := by have h := toOrdinal_pow b hb 0; simpa using h
  have hbb : toOrdinal b b = ω := by
    have h := toOrdinal_pow b hb 1; rw [pow_one, h1, opow_one] at h; exact h
  have hSM : StrictMono (toOrdinal b) := fun a c hac => (toOrdinal_mono_and_bound b hb c).1 a hac
  have homega_le : (ω : Ordinal) ≤ toOrdinal b (Nat.log b w) := by
    rw [← hbb]; exact hSM.monotone hreg
  calc (ω : Ordinal) ^ (ω : Ordinal)
      ≤ ω ^ toOrdinal b (Nat.log b w) := opow_le_opow_right omega0_pos homega_le
    _ ≤ toOrdinal b w := opow_toOrdinal_log_le b hb hw

/-- **Level-3 ordinal bridge: `ω^{ω^ω} ≤ descent`** from the SECOND leading exponent in the LARGE
regime (`base i ≤ secondLeadExp_i`). Applies `omega_omega_le_toOrdinal` to the leading exponent
(giving `ω^ω ≤ toOrdinal (base i)(leadExp)`), then `opow_toOrdinal_log_le`. The `ω^ω`-level analog of
`omega_omega_le_seqONote_repr`. -/
theorem omega_pow_omega_le_seqONote_repr {m i : ℕ}
    (hreg2 : base i ≤ Nat.log (base i) (Nat.log (base i) (goodsteinSeq m i)))
    (hv : goodsteinSeq m i ≠ 0) (hlead : Nat.log (base i) (goodsteinSeq m i) ≠ 0) :
    (ω : Ordinal) ^ ((ω : Ordinal) ^ (ω : Ordinal)) ≤ (seqONote m i).repr := by
  have hb : 2 ≤ base i := Nat.le_add_left 2 i
  exact opow_le_seqONote_repr_of_toOrdinal (omega_omega_le_toOrdinal (base i) hb hreg2 hlead) hv

/-- **THE `o = ω^ω` DIAGONAL DOMINATION — UNCONDITIONAL** (for `m` with `(log₂)^[2] m ≥ 2^16`):
`fastGrowing (ω^ω) m ≤ goodsteinLength m + 2`, with `ω^ω = oadd (oadd 1 1 0) 1 0`. Cichoń's lower
bound at `ω^ω` — fully machine-checked. The crux is the SECOND leading exponent in the LARGE regime
(`secondLeadExp_{m-2} ≥ base(m-2) = m`), discharged by the tower (`iterLeadExp_dominates m 2`) +
`n_le_goodsteinSeq` (`n = m`) + the doubly-iterated length bound `goodsteinLength ((log₂)^[2] m) ≥ 2m`
(`two_mul_le_goodsteinLength_loglog`, budget `(m−2)+m = 2m−2 ≤ 2m`). Carries the finite-base-case
`native_decide` axioms (documented split). -/
theorem fastGrowing_omega_pow_omega_le_goodsteinLength {m : ℕ}
    (ht : 2 ^ 16 ≤ (Nat.log 2)^[2] m) :
    fastGrowing (oadd (oadd 1 1 0) 1 0) m ≤ goodsteinLength m + 2 := by
  have h1' : 1 ≤ (Nat.log 2)^[2] m := le_trans (by norm_num) ht
  have hlm0 : Nat.log 2 m ≠ 0 := by
    intro h
    rw [show (Nat.log 2)^[2] m = Nat.log 2 (Nat.log 2 m) from rfl, h, Nat.log_zero_right] at h1'
    omega
  have hlogm2 : 2 ≤ Nat.log 2 m := by
    have h := Nat.pow_le_of_le_log hlm0 (show 1 ≤ Nat.log 2 (Nat.log 2 m) from h1'); simpa using h
  have hm0 : m ≠ 0 := by intro h; rw [h, Nat.log_zero_right] at hlogm2; omega
  have hm : 4 ≤ m := by have h := Nat.pow_le_of_le_log hm0 hlogm2; simpa using h
  set i := m - 2 with hi
  have hbase : base i = m := by simp only [base, hi]; omega
  have ho : (oadd (oadd 1 1 0) 1 0 : ONote).NF := NF.oadd (by decide) 1 NFBelow.zero
  have hv : goodsteinSeq m i ≠ 0 := by have := goodsteinSeq_ge_init m i (by omega); omega
  -- second leading exponent ≥ base = m at step m-2
  have hlen2 : (m - 2) + m ≤ goodsteinLength ((Nat.log 2)^[2] m) := by
    have := two_mul_le_goodsteinLength_loglog ht; omega
  have hval : m ≤ goodsteinSeq ((Nat.log 2)^[2] m) i :=
    n_le_goodsteinSeq ((Nat.log 2)^[2] m) i m (by rw [hbase]) hlen2
  have hreg2 : base i ≤ Nat.log (base i) (Nat.log (base i) (goodsteinSeq m i)) :=
    calc base i = m := hbase
      _ ≤ goodsteinSeq ((Nat.log 2)^[2] m) i := hval
      _ ≤ Nat.log (base i) (Nat.log (base i) (goodsteinSeq m i)) := iterLeadExp_dominates m 2 i
  have hlead : Nat.log (base i) (goodsteinSeq m i) ≠ 0 := by
    intro h0
    rw [h0, Nat.log_zero_right] at hreg2
    omega
  have hidx : (oadd (oadd (oadd 1 1 0) 1 0) 1 0).repr ≤ (seqONote m i).repr := by
    have hr : (oadd (oadd (oadd 1 1 0) 1 0) 1 0 : ONote).repr
        = ω ^ ((ω : Ordinal) ^ (ω : Ordinal)) := by simp [ONote.repr]
    rw [hr]
    exact omega_pow_omega_le_seqONote_repr hreg2 hv hlead
  have hnorm : norm (oadd (oadd 1 1 0) 1 0) ≤ i + 2 := by
    have : norm (oadd (oadd 1 1 0) 1 0 : ONote) = 1 := by decide
    omega
  have hgl : i ≤ goodsteinLength m := le_trans (by omega) (le_goodsteinLength m)
  exact goodstein_dominates_of_index_le ho hgl (by omega) hnorm hidx

/-- **Explicit-threshold form of the `o = ω^ω` domination.** For every `m ≥ 2^{2^{2^16}}`,
`fastGrowing (ω^ω) m ≤ goodsteinLength m + 2`. The threshold is the concrete `N` witnessing the
asymptotic statement "`goodsteinLength` eventually dominates `f_{ω^ω}`": `m ≥ 2^{2^{2^16}}` forces
`(log₂)^[2] m ≥ 2^16` by two applications of `Nat.le_log_of_pow_le`. -/
theorem goodsteinLength_dominates_fastGrowing_omega_pow_omega
    {m : ℕ} (hm : 2 ^ (2 ^ (2 ^ 16)) ≤ m) :
    fastGrowing (oadd (oadd 1 1 0) 1 0) m ≤ goodsteinLength m + 2 := by
  apply fastGrowing_omega_pow_omega_le_goodsteinLength
  have h1 : 2 ^ (2 ^ 16) ≤ Nat.log 2 m := Nat.le_log_of_pow_le Nat.one_lt_two hm
  exact Nat.le_log_of_pow_le Nat.one_lt_two h1

/-- **Explicit-threshold form of the `o = ω^j` domination** (every finite `j ≥ 1`). For `m` with
`m ≥ 2^{2^{2^16}}` and `j < m`, `fastGrowing (ω^j) m ≤ goodsteinLength m + 2`. The big threshold forces
`(log₂)^[2] m ≥ 2^16`; the `j < m` is the (mild) requirement that the level fit under the budget. -/
theorem goodsteinLength_dominates_fastGrowing_omega_pow {m j : ℕ}
    (hm : 2 ^ (2 ^ (2 ^ 16)) ≤ m) (hj1 : 1 ≤ j) (hjm : j < m) :
    fastGrowing (oadd (ONote.ofNat j) 1 0) m ≤ goodsteinLength m + 2 := by
  apply fastGrowing_omega_pow_le_goodsteinLength _ hj1 hjm
  have h1 : 2 ^ (2 ^ 16) ≤ Nat.log 2 m := Nat.le_log_of_pow_le Nat.one_lt_two hm
  exact Nat.le_log_of_pow_le Nat.one_lt_two h1

/-- Anti-vacuity: `ω = oadd 1 1 0` really has `repr = ω`, and `oadd ω 1 0` has `repr = ω^ω` — so the
reduction targets the genuine limit level, not a finite stand-in. -/
example : (oadd 1 1 0 : ONote).repr = ω := by simp [ONote.repr]
example : (oadd (oadd 1 1 0) 1 0 : ONote).repr = ω ^ (ω : Ordinal) := by simp [ONote.repr]
example (j : ℕ) : (oadd (oadd (ONote.ofNat j) 1 0) 1 0 : ONote).repr
    = ω ^ ((ω : Ordinal) ^ (j : Ordinal)) := by simp [ONote.repr, ONote.repr_ofNat]


-- ════════════════ ported: TowerDomination.lean ════════════════
/-
# The FULL ω-power tower: diagonal domination at every level up to ε₀

Lap 10 closed the diagonal `f_o(m) ≤ goodsteinLength m + 2` at the individual limit levels
`o = ω`, `o = ω^j` (finite `j`), and `o = ω^ω` (`DominationOmega.lean`), each by an *ad hoc* bridge.
This file makes the climb **general in one stroke**: it proves the diagonal domination at EVERY
ω-power-tower level `o = ω↑↑k` (`towerO k`, `repr = ω↑↑k`), for every `k`, unconditionally and
machine-checked. Since `sup_k ω↑↑k = ε₀`, this is Cichoń's lower bound at a cofinal family of levels
below `ε₀` — the destination of the expedition (`DIRECTION.md`: "`goodsteinLength` grows like
`f_{ε₀}`").

The proof rests on two general engines, each subsuming its per-level predecessors:

1. **The general length bootstrap** `two_mul_le_goodsteinLength_iter`:
   `goodsteinLength ((log₂)^[k] m) ≥ 2m` for every `k`. The key realization is that the *already
   proved* `o = ω` domination is strong enough at every depth — no `f_{ω^ω}`-strength bound at the
   deep seed is needed (the worry recorded in the lap-10 handoff). What carries it is the clean
   finite-level **tower lower bound** `towerN_le_fastGrowing`: `f_{k+2}(t) ≥ towerN (k+1) (t+1)`
   (an `(k+1)`-fold iterated exponential), proved by induction on `k`. Composed with
   `f_ω(t) = f_{t+1}(t) ≥ f_{k+2}(t)` (index monotonicity) and the tower upper bound on `m`
   (`succ_le_towerN_log_iter`: `m + 1 ≤ towerN k ((log₂)^[k] m + 1)`), the `f_ω` length bound clears
   `2m` at every depth. This subsumes `two_mul_le_goodsteinLength_log` (k=1) and
   `two_mul_le_goodsteinLength_loglog` (k=2).

2. **The general ordinal bridge** `omegaTower_succ_le_seqONote_repr`: if the descent's `k`-fold
   leading exponent is in the large regime (`base i ≤ (log_{base i})^[k] (G_i)`), then the descent
   ordinal dominates `ω↑↑(k+1)`. Pure `toOrdinal` induction (`omegaTower_le_toOrdinal`), peeling one
   `Nat.log` per step. This subsumes `omega_omega_le_seqONote_repr` (k=1) and
   `omega_pow_omega_le_seqONote_repr` (k=2).

The crux at step `i = m − 2` is discharged by the self-similarity tower `iterLeadExp_dominates`
(read at a fixed index via `logSeq_iterate_apply`) feeding `n_le_goodsteinSeq` the bootstrap length
bound. Everything below is unconditional; the unconditional closures carry the finite-base-case
`native_decide` axioms (documented split) inherited through the `f_ω` bootstrap.
-/



/-! ## The iterated-exponential tower `towerN` and its basic estimates -/

/-- Iterated exponential tower: `towerN 0 t = t`, `towerN (k+1) t = 2 ^ towerN k t`. -/
def towerN : ℕ → ℕ → ℕ
  | 0, t => t
  | (k + 1), t => 2 ^ towerN k t

@[simp] theorem towerN_zero (t : ℕ) : towerN 0 t = t := rfl
@[simp] theorem towerN_succ (k t : ℕ) : towerN (k + 1) t = 2 ^ towerN k t := rfl

/-- `t ≤ towerN k t` (the tower is expansive). -/
theorem towerN_id_le (k t : ℕ) : t ≤ towerN k t := by
  induction k with
  | zero => simp
  | succ k ih => rw [towerN_succ]; exact le_trans ih (le_of_lt Nat.lt_two_pow_self)

/-- `towerN k` is monotone in its argument. -/
theorem towerN_mono_right (k : ℕ) {x y : ℕ} (h : x ≤ y) : towerN k x ≤ towerN k y := by
  induction k with
  | zero => simpa using h
  | succ k ih => rw [towerN_succ, towerN_succ]; exact Nat.pow_le_pow_right (by norm_num) ih

/-- For `k ≥ 1`, `2 ^ X ≤ towerN k (X + 1)`. -/
theorem two_pow_le_towerN_succ (k X : ℕ) : 2 ^ X ≤ towerN (k + 1) (X + 1) := by
  rw [towerN_succ]
  exact Nat.pow_le_pow_right (by norm_num) (le_trans (Nat.le_succ X) (towerN_id_le k (X + 1)))

/-- `towerN k (2^x) ≤ 2 ^ towerN k x` (pushing an exponential past the tower from below). -/
theorem towerN_two_pow_le (k x : ℕ) : towerN k (2 ^ x) ≤ 2 ^ towerN k x := by
  induction k with
  | zero => simp
  | succ k ih => rw [towerN_succ, towerN_succ]; exact Nat.pow_le_pow_right (by norm_num) ih

/-! ## Engine 1: the general length bootstrap -/

/-- **The general finite-level tower lower bound (Claim B).** For every `k` and every `t ≥ 2`,
`towerN (k+1) (t+1) ≤ f_{k+2}(t)`: the `(k+2)`-nd fast-growing function at `t` dominates an
`(k+1)`-fold iterated exponential of `t+1`. By induction on `k`, using `f_{n+1}(t) = (f_n)^[t](t)`
(`fastGrowing_succ`), `(f)^[t] t ≥ (f)^[2] t = f(f(t))` (iterate monotonicity + `id ≤ f`), and the
IH applied twice — the inner application keeps the argument `≥ 2`, the outer lifts a tower height.
This is the engine that makes the *already proved* `o = ω` domination strong enough at every depth:
no deeper fast-growing bound is needed. -/
theorem towerN_le_fastGrowing (k : ℕ) : ∀ t, 2 ≤ t →
    towerN (k + 1) (t + 1) ≤ fastGrowing (ONote.ofNat (k + 2)) t := by
  induction k with
  | zero =>
    intro t ht
    rw [show (0 + 2) = 2 from rfl, fastGrowing_ofNat_two, towerN_succ, towerN_zero]
    calc 2 ^ (t + 1) = 2 ^ t * 2 := by rw [pow_succ]
      _ ≤ 2 ^ t * t := by gcongr
  | succ k ih =>
    intro t ht
    have hfs : fastGrowing (ONote.ofNat (k + 1 + 2))
        = fun i => (fastGrowing (ONote.ofNat (k + 2)))^[i] i := by
      rw [show (k + 1 + 2) = (k + 2) + 1 from rfl,
          fastGrowing_succ _ (fundamentalSequence_ofNat_succ (k + 2))]
    rw [hfs]
    set g := fastGrowing (ONote.ofNat (k + 2)) with hg
    have hexp : (id : ℕ → ℕ) ≤ g := fun n => le_fastGrowing _ n
    have hmono : g^[2] t ≤ g^[t] t := Function.monotone_iterate_of_id_le hexp ht t
    have h2it : g^[2] t = g (g t) := by
      rw [show (2 : ℕ) = 1 + 1 from rfl, Function.iterate_add_apply]; simp
    have hinner : towerN (k + 1) (t + 1) ≤ g t := ih t ht
    have hgt_ge : t + 1 ≤ g t := le_trans (towerN_id_le (k + 1) (t + 1)) hinner
    have hgt2 : 2 ≤ g t := by omega
    have houter : towerN (k + 1) (g t + 1) ≤ g (g t) := ih (g t) hgt2
    have hstep1 : towerN (k + 1) (towerN (k + 1) (t + 1) + 1) ≤ towerN (k + 1) (g t + 1) :=
      towerN_mono_right (k + 1) (by omega)
    have hstep2 : 2 ^ (towerN (k + 1) (t + 1)) ≤ towerN (k + 1) (towerN (k + 1) (t + 1) + 1) :=
      two_pow_le_towerN_succ k (towerN (k + 1) (t + 1))
    calc towerN (k + 1 + 1) (t + 1)
        = 2 ^ (towerN (k + 1) (t + 1)) := by rw [towerN_succ]
      _ ≤ towerN (k + 1) (towerN (k + 1) (t + 1) + 1) := hstep2
      _ ≤ towerN (k + 1) (g t + 1) := hstep1
      _ ≤ g (g t) := houter
      _ = g^[2] t := h2it.symm
      _ ≤ g^[t] t := hmono

/-- **The tower upper bound on the seed (Claim A).** `m + 1 ≤ towerN k ((log₂)^[k] m + 1)`: the seed
`m` is below a `k`-fold tower of its own `k`-fold logarithm. By induction on `k`, using
`Nat.lt_pow_succ_log_self` and `towerN_two_pow_le`. -/
theorem succ_le_towerN_log_iter (k m : ℕ) :
    m + 1 ≤ towerN k ((Nat.log 2)^[k] m + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hlt : (Nat.log 2)^[k] m < 2 ^ ((Nat.log 2)^[k + 1] m + 1) := by
      rw [Function.iterate_succ_apply']
      exact Nat.lt_pow_succ_log_self (by norm_num) _
    calc m + 1 ≤ towerN k ((Nat.log 2)^[k] m + 1) := ih
      _ ≤ towerN k (2 ^ ((Nat.log 2)^[k + 1] m + 1)) := towerN_mono_right k (by omega)
      _ ≤ 2 ^ towerN k ((Nat.log 2)^[k + 1] m + 1) := towerN_two_pow_le k _
      _ = towerN (k + 1) ((Nat.log 2)^[k + 1] m + 1) := by rw [towerN_succ]

/-- `(log₂)^[k] m ≤ m`: iterated logarithm never increases. -/
theorem iterLog2_le_self (k m : ℕ) : (Nat.log 2)^[k] m ≤ m := by
  induction k with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ_apply']; exact le_trans (Nat.log_le_self 2 _) ih

/-- **THE GENERAL LENGTH BOOTSTRAP.** For every `k`, with the `k`-fold log seed `≥ 2^16` (and `≥ k+1`,
so `f_ω = f_{·+1}` reaches index `k+2`), the seed-`((log₂)^[k] m)` Goodstein descent runs at least
`2m` steps: `goodsteinLength ((log₂)^[k] m) ≥ 2m`.

The bound is proved from the **`o = ω` domination alone**, at every depth:
`goodsteinLength t ≥ f_ω(t) − 2 = f_{t+1}(t) − 2 ≥ f_{k+2}(t) − 2 ≥ towerN (k+1) (t+1) − 2 ≥
2^{m+1} − 2 ≥ 2m`, where `t = (log₂)^[k] m`. The last steps use `succ_le_towerN_log_iter`
(`m+1 ≤ towerN k (t+1)`, so `2^{m+1} ≤ towerN (k+1) (t+1)`). Generalizes
`two_mul_le_goodsteinLength_log` (k=1) and `two_mul_le_goodsteinLength_loglog` (k=2). -/
theorem two_mul_le_goodsteinLength_iter (k m : ℕ)
    (ht : 2 ^ 16 ≤ (Nat.log 2)^[k] m) (hk : k + 1 ≤ (Nat.log 2)^[k] m) :
    2 * m ≤ goodsteinLength ((Nat.log 2)^[k] m) := by
  set t := (Nat.log 2)^[k] m with htdef
  have ht2 : 2 ≤ t := le_trans (by norm_num) ht
  have hlen := fastGrowing_omega_le_goodsteinLength (m := t) ht
  rw [fastGrowing_omega_eq] at hlen
  have hidx : fastGrowing (ONote.ofNat (k + 2)) t ≤ fastGrowing (ONote.ofNat (t + 1)) t :=
    fastGrowing_ofNat_mono (by omega) (by omega)
  have hB := towerN_le_fastGrowing k t ht2
  have hA : m + 1 ≤ towerN k (t + 1) := by
    have := succ_le_towerN_log_iter k m; rw [← htdef] at this; exact this
  have hA2 : 2 ^ (m + 1) ≤ towerN (k + 1) (t + 1) := by
    rw [towerN_succ]; exact Nat.pow_le_pow_right (by norm_num) hA
  have hpow : 2 * (m + 1) ≤ 2 ^ (m + 1) := by
    have hmlt : m < 2 ^ m := Nat.lt_two_pow_self
    calc 2 * (m + 1) ≤ 2 * 2 ^ m := by omega
      _ = 2 ^ (m + 1) := by rw [pow_succ]; ring
  omega

/-! ## Engine 2: the ordinal tower and the general ordinal bridge -/

/-- Ordinal tower: `omegaTower 0 = 1`, `omegaTower (k+1) = ω ^ omegaTower k`, so `omegaTower k = ω↑↑k`
(`omegaTower 1 = ω`, `omegaTower 2 = ω^ω`, `omegaTower 3 = ω^{ω^ω}`, …). -/
noncomputable def omegaTower : ℕ → Ordinal
  | 0 => 1
  | (k + 1) => (ω : Ordinal) ^ omegaTower k

theorem omegaTower_succ_eq (k : ℕ) : omegaTower (k + 1) = (ω : Ordinal) ^ omegaTower k := rfl

/-- The ω-tower is monotone in its height (`x ≤ ω^x = omegaTower (k+1)`). -/
theorem omegaTower_mono : Monotone omegaTower := by
  refine monotone_nat_of_le_succ (fun k => ?_)
  rw [omegaTower_succ_eq]; exact right_le_opow (omegaTower k) one_lt_omega0

/-- **Cofinality of the ω-tower in ε₀.** Every normal-form `ONote` — i.e. every ordinal `< ε₀` — has
`repr` strictly below some tower level `ω↑↑k`. By structural induction on the notation: the leading
term `ω^{repr e}·n` is `< ω^{omegaTower ke} = ω↑↑(ke+1)` (`mul_lt_omega0_opow` on the IH for `e`), the
tail is `< ω↑↑ka` (IH for `a`), and both are absorbed below the next tower level, which is additively
principal (`isPrincipal_add_omega0_opow`). This is what turns the per-level diagonal domination into
the literal "for every `o < ε₀`" statement. -/
theorem exists_repr_lt_omegaTower : ∀ (o : ONote), o.NF → ∃ k, o.repr < omegaTower k := by
  intro o
  induction o with
  | zero =>
    intro _
    exact ⟨0, by show (0 : Ordinal) < omegaTower 0; rw [show omegaTower 0 = 1 from rfl]; exact one_pos⟩
  | oadd e n a ihe iha =>
    intro hNF
    obtain ⟨ke, hke⟩ := ihe hNF.fst
    obtain ⟨ka, hka⟩ := iha hNF.snd
    set K := max (ke + 1) ka with hK
    have hmul : (ω : Ordinal) ^ e.repr * ((n : ℕ) : Ordinal) < omegaTower (ke + 1) := by
      rw [omegaTower_succ_eq]
      have hc0 : (0 : Ordinal) < omegaTower ke := by
        have h := omegaTower_mono (Nat.zero_le ke)
        rw [show omegaTower 0 = 1 from rfl] at h; exact zero_lt_one.trans_le h
      have hae : (ω : Ordinal) ^ e.repr < ω ^ (omegaTower ke) :=
        (opow_lt_opow_iff_right one_lt_omega0).2 hke
      exact mul_lt_omega0_opow hc0 hae (natCast_lt_omega0 _)
    have hmulK : (ω : Ordinal) ^ e.repr * ((n : ℕ) : Ordinal) < omegaTower K :=
      lt_of_lt_of_le hmul (omegaTower_mono (le_max_left _ _))
    have hakK : a.repr < omegaTower K := lt_of_lt_of_le hka (omegaTower_mono (le_max_right _ _))
    have hprin : IsPrincipal (· + ·) (omegaTower (K + 1)) := by
      rw [omegaTower_succ_eq]; exact isPrincipal_add_omega0_opow _
    have hltK1 : omegaTower K ≤ omegaTower (K + 1) := omegaTower_mono (Nat.le_succ K)
    refine ⟨K + 1, ?_⟩
    have hrepr : (oadd e n a).repr = (ω : Ordinal) ^ e.repr * ((n : ℕ) : Ordinal) + a.repr := by
      simp [ONote.repr]
    rw [hrepr]
    exact hprin (lt_of_lt_of_le hmulK hltK1) (lt_of_lt_of_le hakK hltK1)

/-- ONote realization of the ordinal tower: `towerO 0 = 1`, `towerO (k+1) = oadd (towerO k) 1 0`.
`towerO 1 = ω`, `towerO 2 = ω^ω`, … (`repr_towerO`). -/
def towerO : ℕ → ONote
  | 0 => 1
  | (k + 1) => oadd (towerO k) 1 0

theorem towerO_NF (k : ℕ) : (towerO k).NF := by
  induction k with
  | zero => exact (by decide : (1 : ONote).NF)
  | succ k ih => exact NF.oadd ih 1 NFBelow.zero

theorem repr_towerO (k : ℕ) : (towerO k).repr = omegaTower k := by
  induction k with
  | zero => show (1 : ONote).repr = (1 : Ordinal); simp
  | succ k ih =>
    show (oadd (towerO k) 1 0).repr = (ω : Ordinal) ^ omegaTower k
    rw [← ih]; simp [ONote.repr]

theorem norm_towerO (k : ℕ) : norm (towerO k) = 1 := by
  induction k with
  | zero => decide
  | succ k ih =>
    show norm (oadd (towerO k) 1 0) = 1
    rw [norm_oadd, ih, norm_zero]; simp

/-- The `k`-fold base-`b` log of `0` is `0`. -/
theorem iterLog_zero (b k : ℕ) : (Nat.log b)^[k] 0 = 0 := by
  induction k with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ_apply', ih, Nat.log_zero_right]

/-- **The general `toOrdinal` core.** If the `k`-fold base-`b` logarithm of `w` is still `≥ b`, then
`toOrdinal b w ≥ omegaTower (k+1) = ω↑↑(k+1)`. By induction on `k`, peeling one `Nat.log` from the
inside per step. Generalizes `omega_omega_le_toOrdinal` (k=1) and the finite `opow_le_toOrdinal`. -/
theorem omegaTower_le_toOrdinal (b : ℕ) (hb : 2 ≤ b) :
    ∀ (k w : ℕ), b ≤ (Nat.log b)^[k] w → omegaTower (k + 1) ≤ toOrdinal b w := by
  have h1 : toOrdinal b 1 = 1 := by have h := toOrdinal_pow b hb 0; simpa using h
  have hbb : toOrdinal b b = ω := by
    have h := toOrdinal_pow b hb 1; rw [pow_one, h1, opow_one] at h; exact h
  have hSM : StrictMono (toOrdinal b) := fun a c hac => (toOrdinal_mono_and_bound b hb c).1 a hac
  intro k
  induction k with
  | zero =>
    intro w hw
    simp only [Function.iterate_zero, id_eq] at hw
    show (ω : Ordinal) ^ omegaTower 0 ≤ toOrdinal b w
    rw [show omegaTower 0 = 1 from rfl, opow_one, ← hbb]
    exact hSM.monotone hw
  | succ k ih =>
    intro w hw
    rw [Function.iterate_succ_apply] at hw
    have hwne : w ≠ 0 := by
      intro h0; rw [h0, Nat.log_zero_right, iterLog_zero] at hw; omega
    have ihw := ih (Nat.log b w) hw
    show (ω : Ordinal) ^ omegaTower (k + 1) ≤ toOrdinal b w
    calc (ω : Ordinal) ^ omegaTower (k + 1)
        ≤ ω ^ toOrdinal b (Nat.log b w) := opow_le_opow_right omega0_pos ihw
      _ ≤ toOrdinal b w := opow_toOrdinal_log_le b hb hwne

/-- **The general ordinal bridge on the descent.** If the descent's `k`-fold leading exponent is in
the large regime (`base i ≤ (log_{base i})^[k] (G_i)`), then `omegaTower (k+1) ≤ (seqONote m i).repr`.
Generalizes `omega_omega_le_seqONote_repr` (k=1) and `omega_pow_omega_le_seqONote_repr` (k=2). -/
theorem omegaTower_succ_le_seqONote_repr {m i k : ℕ}
    (hreg : base i ≤ (Nat.log (base i))^[k] (goodsteinSeq m i)) :
    omegaTower (k + 1) ≤ (seqONote m i).repr := by
  rw [repr_seqONote]
  exact omegaTower_le_toOrdinal (base i) (Nat.le_add_left 2 i) k _ hreg

/-- `(logSeq^[k] a) i = (Nat.log (base i))^[k] (a i)`: iterating the per-step `logSeq` operator and
reading at a fixed index `i` is the same as iterating `Nat.log (base i)` on `a i` (each `logSeq`
application reads the same `base i`). This is what lets the self-similarity tower
`iterLeadExp_dominates` (stated with `logSeq^[k]`) talk about the `k`-fold *fixed-base* leading
exponent that the ordinal bridge needs. -/
theorem logSeq_iterate_apply (a : ℕ → ℕ) (k i : ℕ) :
    (logSeq^[k] a) i = (Nat.log (base i))^[k] (a i) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    show Nat.log (base i) ((logSeq^[k] a) i) = Nat.log (base i) ((Nat.log (base i))^[k] (a i))
    rw [ih]

/-! ## The general diagonal domination — Cichoń's lower bound up to ε₀ -/

/-- **THE GENERAL DIAGONAL DOMINATION — UNCONDITIONAL.** For every `k`, with the `k`-fold log seed
`(log₂)^[k] m ≥ 2^16` (and `≥ k+1`), `fastGrowing (towerO k) m ≤ goodsteinLength m + 2`, where
`towerO k` has `repr = ω↑↑k`. This is Cichoń's lower bound at EVERY ω-power-tower level:
`k = 1` is `o = ω`, `k = 2` is `o = ω^ω`, `k = 3` is `o = ω^{ω^ω}`, …, and `sup_k ω↑↑k = ε₀`. One
general theorem subsuming all the per-level closures of `DominationOmega.lean`.

Assembly: the general length bootstrap (`two_mul_le_goodsteinLength_iter`) feeds `n_le_goodsteinSeq`
to keep the seed-`((log₂)^[k] m)` value `≥ m` at step `i = m−2`; the self-similarity tower
(`iterLeadExp_dominates`, read at index `i` via `logSeq_iterate_apply`) lifts that to the `k`-fold
leading exponent of the genuine descent being `≥ base i = m`; the general ordinal bridge
(`omegaTower_succ_le_seqONote_repr`) turns that into `ω↑↑(k+1) ≤ descent`; and the diagonal reduction
`goodstein_dominates_of_index_le` (budget `m`) closes it. Carries the finite-base-case
`native_decide` axioms (documented split), inherited via the `f_ω` length bootstrap. -/
theorem fastGrowing_le_goodsteinLength_of_repr_le_tower {o : ONote} (ho : o.NF) {m k : ℕ}
    (ht : 2 ^ 16 ≤ (Nat.log 2)^[k] m) (hk : k + 1 ≤ (Nat.log 2)^[k] m)
    (hrepr : o.repr ≤ omegaTower k) (hnorm : norm o ≤ m) :
    fastGrowing o m ≤ goodsteinLength m + 2 := by
  have hmge : 2 ^ 16 ≤ m := le_trans ht (iterLog2_le_self k m)
  have hm : 4 ≤ m := le_trans (by norm_num) hmge
  set i := m - 2 with hi
  have hbase : base i = m := by simp only [base, hi]; omega
  have hlen : i + m ≤ goodsteinLength ((Nat.log 2)^[k] m) := by
    have := two_mul_le_goodsteinLength_iter k m ht hk; omega
  have hval : m ≤ goodsteinSeq ((Nat.log 2)^[k] m) i :=
    n_le_goodsteinSeq ((Nat.log 2)^[k] m) i m (by rw [hbase]) hlen
  have hdom : goodsteinSeq ((Nat.log 2)^[k] m) i ≤ (Nat.log (base i))^[k] (goodsteinSeq m i) := by
    have h := iterLeadExp_dominates m k i
    rwa [logSeq_iterate_apply] at h
  have hreg : base i ≤ (Nat.log (base i))^[k] (goodsteinSeq m i) := by
    calc base i = m := hbase
      _ ≤ goodsteinSeq ((Nat.log 2)^[k] m) i := hval
      _ ≤ (Nat.log (base i))^[k] (goodsteinSeq m i) := hdom
  have hbridge : omegaTower (k + 1) ≤ (seqONote m i).repr := omegaTower_succ_le_seqONote_repr hreg
  have hidx : (oadd o 1 0).repr ≤ (seqONote m i).repr := by
    have hle : (oadd o 1 0).repr ≤ omegaTower (k + 1) := by
      have hr : (oadd o 1 0).repr = (ω : Ordinal) ^ o.repr := by simp [ONote.repr]
      rw [hr, omegaTower_succ_eq]
      exact opow_le_opow_right omega0_pos hrepr
    exact le_trans hle hbridge
  have hgl : i ≤ goodsteinLength m := le_trans (by omega) (le_goodsteinLength m)
  exact goodstein_dominates_of_index_le ho hgl (by omega) (by omega) hidx

/-- **Tower-level diagonal domination** (the special case `o = towerO k`, `repr = ω↑↑k`): for every
`k`, `fastGrowing (towerO k) m ≤ goodsteinLength m + 2`. `k = 1` is `o = ω`, `k = 2` is `o = ω^ω`,
`k = 3` is `o = ω^{ω^ω}`, …, with `sup_k ω↑↑k = ε₀`. Subsumes the per-level closures of
`DominationOmega.lean`. Immediate corollary of `fastGrowing_le_goodsteinLength_of_repr_le_tower`
(`repr (towerO k) = ω↑↑k`, `norm (towerO k) = 1 ≤ m`). -/
theorem fastGrowing_towerO_le_goodsteinLength {m k : ℕ}
    (ht : 2 ^ 16 ≤ (Nat.log 2)^[k] m) (hk : k + 1 ≤ (Nat.log 2)^[k] m) :
    fastGrowing (towerO k) m ≤ goodsteinLength m + 2 := by
  have hmge : 4 ≤ m := le_trans (by norm_num) (le_trans ht (iterLog2_le_self k m))
  refine fastGrowing_le_goodsteinLength_of_repr_le_tower (towerO_NF k) ht hk ?_ ?_
  · exact le_of_eq (repr_towerO k)
  · rw [norm_towerO]; omega

/-! ### Explicit thresholds and the ε₀ headline -/

/-- `towerN k N ≤ m ⟹ N ≤ (log₂)^[k] m`: an explicit threshold guaranteeing the `k`-fold log seed
is large. By induction on `k` via `Nat.le_log_of_pow_le`. -/
theorem threshold_le_iterLog (k N m : ℕ) (hm : towerN k N ≤ m) : N ≤ (Nat.log 2)^[k] m := by
  induction k generalizing m with
  | zero => simpa using hm
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    rw [towerN_succ] at hm
    exact ih (Nat.log 2 m) (Nat.le_log_of_pow_le Nat.one_lt_two hm)

/-- **Explicit-threshold form of the general diagonal domination.** For every `k` and every
`m ≥ towerN k (2^16 + k)` (a tower of height `k` over `2^16 + k`),
`fastGrowing (towerO k) m ≤ goodsteinLength m + 2`. The single threshold supplies both hypotheses of
`fastGrowing_towerO_le_goodsteinLength` (`2^16 ≤ (log₂)^[k] m` and `k+1 ≤ (log₂)^[k] m`). -/
theorem goodsteinLength_dominates_fastGrowing_towerO {m k : ℕ}
    (hm : towerN k (2 ^ 16 + k) ≤ m) :
    fastGrowing (towerO k) m ≤ goodsteinLength m + 2 := by
  have h := threshold_le_iterLog k (2 ^ 16 + k) m hm
  exact fastGrowing_towerO_le_goodsteinLength (by omega) (by omega)

/-- **THE ε₀ HEADLINE.** For every ω-power-tower level `k`, `goodsteinLength` eventually dominates
`f_{ω↑↑k}`: there is a threshold `N` (namely `towerN k (2^16 + k)`) past which
`fastGrowing (towerO k) m ≤ goodsteinLength m + 2`. Since `{ω↑↑k}` is cofinal in `ε₀`, this is
Cichoń's lower bound `goodsteinLength m + 2 ≥ f_o(m)` (eventually) for a family of `o` cofinal below
`ε₀` — the expedition's destination, fully machine-checked and unconditional. -/
theorem goodsteinLength_eventually_dominates_fastGrowing_towerO (k : ℕ) :
    ∃ N, ∀ m, N ≤ m → fastGrowing (towerO k) m ≤ goodsteinLength m + 2 :=
  ⟨towerN k (2 ^ 16 + k), fun _ hm => goodsteinLength_dominates_fastGrowing_towerO hm⟩

/-- **THE FULL ε₀ HEADLINE — Cichoń's lower bound for every `o < ε₀`.** For EVERY normal-form
`ONote` `o` (every ordinal `< ε₀`), `goodsteinLength` eventually dominates `f_o`: there is a threshold
`N` past which `fastGrowing o m ≤ goodsteinLength m + 2`. This is the complete diagonal lower bound —
not merely along the tower spine `ω↑↑k`, but at *every* ordinal below `ε₀` — the destination of the
expedition (`DIRECTION.md`), unconditional and machine-checked.

Proof: `exists_repr_lt_omegaTower` places `o` below some tower level `ω↑↑k` (cofinality of the tower
in `ε₀`); the threshold `N = max (towerN k (2^16+k)) (norm o)` supplies the deep-seed bound and the
budget `norm o ≤ m`; then `fastGrowing_le_goodsteinLength_of_repr_le_tower` (whose descent dominates
`ω↑↑(k+1) ≥ ω^{repr o}`) closes it. Carries the finite-base-case `native_decide` axioms (documented
split), inherited via the `f_ω` length bootstrap. -/
theorem goodsteinLength_eventually_dominates_fastGrowing {o : ONote} (ho : o.NF) :
    ∃ N, ∀ m, N ≤ m → fastGrowing o m ≤ goodsteinLength m + 2 := by
  obtain ⟨k, hk⟩ := exists_repr_lt_omegaTower o ho
  refine ⟨max (towerN k (2 ^ 16 + k)) (norm o), fun m hm => ?_⟩
  have hm1 : towerN k (2 ^ 16 + k) ≤ m := le_trans (le_max_left _ _) hm
  have hm2 : norm o ≤ m := le_trans (le_max_right _ _) hm
  have hseed := threshold_le_iterLog k (2 ^ 16 + k) m hm1
  exact fastGrowing_le_goodsteinLength_of_repr_le_tower ho (by omega) (by omega) (le_of_lt hk) hm2

/-- Anti-vacuity: the tower notation unfolds to the concrete `oadd` forms the per-level closures
used, and carries the genuine ε₀-approaching reprs — so the general theorem really subsumes them. -/
example : towerO 1 = oadd 1 1 0 := rfl
example : towerO 2 = oadd (oadd 1 1 0) 1 0 := rfl
example : towerO 3 = oadd (oadd (oadd 1 1 0) 1 0) 1 0 := rfl
example : (towerO 1).repr = (ω : Ordinal) := by
  show (oadd 1 1 0 : ONote).repr = _; simp [ONote.repr]
example : (towerO 2).repr = (ω : Ordinal) ^ (ω : Ordinal) := by
  show (oadd (oadd 1 1 0) 1 0 : ONote).repr = _; simp [ONote.repr]
example : (towerO 3).repr = (ω : Ordinal) ^ ((ω : Ordinal) ^ (ω : Ordinal)) := by
  show (oadd (oadd (oadd 1 1 0) 1 0) 1 0 : ONote).repr = _; simp [ONote.repr]


-- ════════════════ ported: GrowthStatement.lean ════════════════
/-
# The growth theorem: `goodsteinLength` grows like `f_{ε₀}` — Cichoń's lower bound (audit surface)

**Designated audit surface for the growth headline (C3 of `DIRECTION.md`).** The proof lives in
`TowerDomination.lean` and its siblings; this file states the headline thinly and faithfully, the way
`Statement.lean` does for termination.

## What this says (the mathematical heart of Kirby–Paris)
Goodstein's theorem (termination) is proved in `Statement.lean`. Its *companion* — why Peano
Arithmetic cannot prove it (Kirby–Paris 1982) — rests on a growth gap: every PA-provably-total
function is dominated by some `f_α` with `α < ε₀`, while the Goodstein length function outgrows all of
them. The PA-syntactic statement is out of scope (see `Statement.lean` / `README.md`); the *growth
gap itself*, which lives entirely in mathlib, is the content here.

**`goodsteinLength_eventually_dominates_fastGrowing`**: for EVERY ordinal notation `o < ε₀` (every
normal-form `ONote`), `goodsteinLength` eventually dominates the fast-growing function `f_o`:
`∃ N, ∀ m ≥ N, fastGrowing o m ≤ goodsteinLength m + 2`. Since every PA-provably-total function is
dominated by some such `f_o`, `goodsteinLength` outgrows every PA-provably-total function — the formal
"Goodstein grows too fast for PA." The additive `+ 2` is the standard constant from Cichoń's identity
`goodsteinLength m = H_{o_m}(2) − 2`; the statement is domination up to `O(1)`.

This is Cichoń's lower bound in full: not merely along the `ω`-power tower `ω↑↑k` (which is cofinal in
`ε₀`), but at *every* ordinal below `ε₀`.

## Proof (delegated)
`TowerDomination.lean`: the descent ordinal of the base-2 Goodstein run stays above `ω↑↑(k+1)` for
`≈ m` steps (general ordinal bridge `omegaTower_succ_le_seqONote_repr`), where `k` is chosen by tower
cofinality (`exists_repr_lt_omegaTower`: every `o < ε₀` is below some `ω↑↑k`). The step count is
supplied by the general length bootstrap `two_mul_le_goodsteinLength_iter`, itself powered by the
already-proved `o = ω` domination and the clean finite-level tower bound `towerN_le_fastGrowing`. The
diagonal reduction `goodstein_dominates_of_index_le` (the Cichoń pipeline through the Hardy hierarchy)
closes it.

## Axioms
The unconditional closures carry the bare trust base `[propext, Classical.choice, Quot.sound]` plus
the finite-base-case `native_decide` artifacts (the computed lengths of the finitely many small
Goodstein runs `4 ≤ M < 16`) — a 🟢 finite/computational dependency, excluded from the math-axiom
count per the discharge doctrine. There are **no math axioms** and **no `sorry`**.
-/



/-- **THE GROWTH HEADLINE (C3) — Cichoń's lower bound, complete to ε₀.** For every ordinal notation
`o < ε₀` (every normal-form `ONote`), `goodsteinLength` eventually dominates `f_o`:
`∃ N, ∀ m ≥ N, fastGrowing o m ≤ goodsteinLength m + 2`. The thin, faithful audit statement;
the proof is `TowerDomination.goodsteinLength_eventually_dominates_fastGrowing`. -/
theorem goodsteinLength_dominates_fastGrowing {o : ONote} (ho : o.NF) :
    ∃ N, ∀ m, N ≤ m → fastGrowing o m ≤ goodsteinLength m + 2 :=
  goodsteinLength_eventually_dominates_fastGrowing ho

/-- **`towerO` IS mathlib's `ε₀` fundamental sequence.** The iterate `(a ↦ ω^a)` from `0` that defines
`fastGrowingε₀` (mathlib's one-step extension to `ε₀`) is exactly our `towerO`:
`(fun a => oadd a 1 0)^[k+1] 0 = towerO k`. Faithfulness anchor: the tower domination really targets
the genuine `ε₀` hierarchy `ω, ω^ω, ω^{ω^ω}, …`. -/
theorem iterate_oadd_eq_towerO (k : ℕ) : (fun a => ONote.oadd a 1 0)^[k + 1] 0 = towerO k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih]
    rfl

/-- Consequently `fastGrowingε₀ (k+1) = fastGrowing (towerO k) (k+1)`: mathlib's `ε₀`-level function
is the diagonal over our tower. (Its *level* `k` grows with the argument, so this diagonal is genuinely
`ε₀`-fast and is NOT what the per-level headline dominates — the headline dominates each *fixed* `f_o`,
the faithful reading of "tracks `f_{ε₀}`".) -/
theorem fastGrowingε₀_eq_towerO (k : ℕ) :
    ONote.fastGrowingε₀ (k + 1) = fastGrowing (towerO k) (k + 1) := by
  rw [ONote.fastGrowingε₀, iterate_oadd_eq_towerO]

/-- **The matching UPPER bound.** `goodsteinLength m + 2 ≤ f_{o_m}(2)`, where `o_m = seqONote m 0` is
the base-2 ordinal of `m` (`= toONote 2 m`). Immediate from the Cichoń identity
`goodsteinLength m + 2 = H_{o_m}(2)` (`hardy_seqONote_zero`) and `hardy_le_fastGrowing` (Hardy ≤
fast-growing at the same index). Together with `goodsteinLength_dominates_fastGrowing` this squeezes
`goodsteinLength` inside the fast-growing hierarchy at the `ε₀` frontier — the two-sided "grows like
`f_{ε₀}`": from below it eventually beats every fixed `f_o` (`o < ε₀`); from above it never exceeds
`f` at its own ordinal `o_m < ε₀` (argument `2`). -/
theorem goodsteinLength_le_fastGrowing_ordinal (m : ℕ) :
    goodsteinLength m + 2 ≤ fastGrowing (seqONote m 0) 2 := by
  rw [← hardy_seqONote_zero m]
  exact hardy_le_fastGrowing (seqONote m 0) 2 (by norm_num)

/-- **THE TWO-SIDED CAPSTONE — "`goodsteinLength` grows like `f_{ε₀}`".** Packaging both directions as
the single definitive audit surface: for every `o < ε₀` (every NF `ONote`),
* **(lower)** `goodsteinLength` eventually dominates `f_o`: `∃ N, ∀ m ≥ N, f_o(m) ≤ goodsteinLength m + 2`;
* **(upper)** `goodsteinLength` never exceeds `f` at its own base-2 ordinal: `goodsteinLength m + 2 ≤
  f_{o_m}(2)` for all `m`.
So `goodsteinLength` sits exactly within the fast-growing hierarchy at the `ε₀` frontier — the formal
"Goodstein grows too fast for PA" (every PA-provably-total function is some `f_o`, `o < ε₀`; all are
eventually dominated). The exact Hardy pin is `hardy_seqONote_zero` (Cichoń) + `hardy_omega_pow_ofNat`
(B4, `H_{ω^k}=f_k`). -/
theorem goodsteinLength_grows_like_fastGrowingε₀ :
    (∀ (o : ONote), o.NF → ∃ N, ∀ m, N ≤ m → fastGrowing o m ≤ goodsteinLength m + 2)
    ∧ (∀ m, goodsteinLength m + 2 ≤ fastGrowing (seqONote m 0) 2) :=
  ⟨fun _ ho => goodsteinLength_dominates_fastGrowing ho, goodsteinLength_le_fastGrowing_ordinal⟩

/-- Anti-vacuity: `f_{ε₀}` is the genuine extension to `ε₀` (mathlib's known value), and the tower the
headline ranges over is the genuine one. -/
example : ONote.fastGrowingε₀ 2 = 2048 := ONote.fastGrowingε₀_two
example : (towerO 1).repr = (ω : Ordinal) := by show (oadd 1 1 0 : ONote).repr = _; simp [ONote.repr]


end GoodsteinPA.Dom
