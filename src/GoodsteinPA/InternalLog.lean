/-
# `InternalLog.lean` — E-core(b) brick 3: base-`b` logarithm inside `V`

Brick 3 of the arithmetization wall (`DESCENT-PLAN.md §3`). Rathjen's hereditary base-change `bump`
(`Defs.bump`) peels the **top** base-`b` power off `n`, i.e. it needs the top exponent
`e = log_b n` (`Nat.log b n`). Foundation ships base-2 `log` only, so we build the variable-base
`ilog b n` inside an arbitrary `V ⊧ₘ* 𝗜𝚺₁`, characterized (for `2 ≤ b`, `0 < n`) by

  `b ^ (ilog b n) ≤ n < b ^ (ilog b n + 1)`.

Built by the least-number principle exactly as Foundation builds base-2 `log` (least `e` with
`n < b^e`, predecessor is the logarithm). This is the last numeric prerequisite before the
hereditary base-change `bump` itself (brick 4).
-/
import GoodsteinPA.InternalDigits

namespace GoodsteinPA.InternalPow

open LO LO.FirstOrder LO.FirstOrder.Arithmetic

variable {V : Type*} [ORingStructure V] [V ⊧ₘ* 𝗜𝚺₁]

/-- `x + 1 ≤ b ^ (x+1)` for `2 ≤ b`: the base bound that makes the log search terminate. -/
lemma succ_le_ipow_succ {b : V} (hb : 2 ≤ b) (x : V) : x + 1 ≤ ipow b (x + 1) := by
  have hb1 : (1 : V) ≤ b := le_trans (by simp) hb
  induction x using ISigma1.sigma1_succ_induction
  · definability
  case zero => simpa [ipow_one] using hb1
  case succ x ih =>
    rw [ipow_succ]
    have h1 : (1 : V) ≤ ipow b (x + 1) := one_le_ipow hb1 (x + 1)
    calc x + 1 + 1 ≤ ipow b (x + 1) + ipow b (x + 1) := add_le_add ih h1
      _ = ipow b (x + 1) * 2 := (mul_two _).symm
      _ ≤ ipow b (x + 1) * b := mul_le_mul_left' hb _

lemma lt_ipow_succ {b : V} (hb : 2 ≤ b) (x : V) : x < ipow b (x + 1) :=
  lt_of_lt_of_le (by simp) (succ_le_ipow_succ hb x)

/-- The defining graph of `ilog`, stated unconditionally (so `ilog` is total): the characterizing
inequality `b^e ≤ n < b^(e+1)` when `2 ≤ b ∧ 0 < n`, and `e = 0` otherwise. -/
lemma ilog_exists_unique (b n : V) :
    ∃! e, ((2 ≤ b ∧ 0 < n) → ipow b e ≤ n ∧ n < ipow b (e + 1))
        ∧ (¬(2 ≤ b ∧ 0 < n) → e = 0) := by
  by_cases hmain : 2 ≤ b ∧ 0 < n
  · obtain ⟨hb, hpos⟩ := hmain
    have hb1 : (1 : V) ≤ b := le_trans (by simp) hb
    -- least `y` with `n < b^y`; the logarithm is its predecessor.
    have hP : 𝚺₁-Predicate (fun e => n < ipow b e) := by definability
    have hex : n < ipow b (n + 1) := lt_ipow_succ hb n
    obtain ⟨y, hy, hmin⟩ := InductionOnHierarchy.least_number 𝚺 1 hP hex
    have hy0 : y ≠ 0 := by
      rintro rfl; simp only [ipow_zero] at hy
      exact absurd (lt_one_iff_eq_zero.mp hy) (pos_iff_ne_zero.mp hpos)
    obtain ⟨e, rfl⟩ := (zero_or_succ y).resolve_left hy0
    have hle : ipow b e ≤ n := not_lt.mp (hmin e (by simp))
    refine ExistsUnique.intro e ⟨fun _ => ⟨hle, hy⟩, fun h => absurd ⟨hb, hpos⟩ h⟩ ?_
    rintro e' ⟨he', _⟩
    obtain ⟨hle', hlt'⟩ := he' ⟨hb, hpos⟩
    -- both satisfy `b^· ≤ n < b^(·+1)`; strict monotonicity forces equality.
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have : ipow b (e' + 1) ≤ ipow b e :=
        ipow_le_ipow_right hb1 (by simpa [lt_iff_succ_le] using h)
      exact absurd (lt_of_lt_of_le hlt' (le_trans this hle)) (by simp)
    · have : ipow b (e + 1) ≤ ipow b e' :=
        ipow_le_ipow_right hb1 (by simpa [lt_iff_succ_le] using h)
      exact absurd (lt_of_lt_of_le hy (le_trans this hle')) (by simp)
  · refine ExistsUnique.intro 0 ⟨fun h => absurd h hmain, fun _ => rfl⟩ ?_
    rintro e ⟨_, he⟩; exact he hmain

/-- **Base-`b` logarithm** in `V`: the top exponent of `n` in base `b` (`0` for `n = 0` or `b < 2`). -/
noncomputable def ilog (b n : V) : V := Classical.choose! (ilog_exists_unique b n)

/-- **Defining inequality of `ilog`**: for `2 ≤ b` and `0 < n`, `b^(ilog b n) ≤ n < b^(ilog b n + 1)`. -/
lemma ilog_spec {b n : V} (hb : 2 ≤ b) (hn : 0 < n) :
    ipow b (ilog b n) ≤ n ∧ n < ipow b (ilog b n + 1) :=
  (Classical.choose!_spec (ilog_exists_unique b n)).1 ⟨hb, hn⟩

lemma ipow_ilog_le {b n : V} (hb : 2 ≤ b) (hn : 0 < n) : ipow b (ilog b n) ≤ n :=
  (ilog_spec hb hn).1

lemma lt_ipow_ilog_succ {b n : V} (hb : 2 ≤ b) (hn : 0 < n) : n < ipow b (ilog b n + 1) :=
  (ilog_spec hb hn).2

end GoodsteinPA.InternalPow
