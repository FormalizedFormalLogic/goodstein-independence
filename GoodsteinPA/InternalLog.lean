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
import GoodsteinPA.Compat

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
      _ ≤ ipow b (x + 1) * b := mul_le_mul_right hb _

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

/-- `1 ≤ ilog b n` once `b ≤ n` (the leading exponent is at least 1). If `ilog b n = 0` then
`n < ipow b 1 = b`, contradicting `b ≤ n`. -/
lemma ilog_pos {b n : V} (hb : 2 ≤ b) (hn : b ≤ n) : 1 ≤ ilog b n := by
  have hnpos : 0 < n := lt_of_lt_of_le (lt_of_lt_of_le (by simp) hb) hn
  by_contra h
  have h0 : ilog b n = 0 := nonpos_iff_eq_zero.mp (le_iff_lt_succ.mpr (by simpa using not_le.mp h))
  have hlt := lt_ipow_ilog_succ hb hnpos
  rw [h0, zero_add, ipow_one] at hlt
  exact absurd hlt (not_lt.mpr hn)

/-- **Monotonicity of `ilog`.** For `2 ≤ b` and `0 < n ≤ n'`, the leading exponent does not decrease:
`ilog b n ≤ ilog b n'`. (If it did, `b^(ilog b n) ≤ n ≤ n' < b^(ilog b n' + 1) ≤ b^(ilog b n)` — a
strict contradiction.) -/
lemma ilog_mono {b n n' : V} (hb : 2 ≤ b) (hn : 0 < n) (hle : n ≤ n') : ilog b n ≤ ilog b n' := by
  have hb1 : (1 : V) ≤ b := le_trans (by simp) hb
  have hn' : 0 < n' := lt_of_lt_of_le hn hle
  by_contra h
  -- `ilog b n' < ilog b n`, i.e. `ilog b n' + 1 ≤ ilog b n`.
  have hstep : ilog b n' + 1 ≤ ilog b n := lt_iff_succ_le.mp (not_le.mp h)
  have h1 : n' < ipow b (ilog b n' + 1) := lt_ipow_ilog_succ hb hn'
  have h2 : ipow b (ilog b n' + 1) ≤ ipow b (ilog b n) := ipow_le_ipow_right hb1 hstep
  have h3 : ipow b (ilog b n) ≤ n := ipow_ilog_le hb hn
  exact absurd (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_le_of_lt hle h1) h2) h3) (_root_.lt_irrefl n)

/-- Graph of `ilog`, for the `𝚺₁`-definability instance below. -/
lemma ilog_graph {e b n : V} :
    e = ilog b n ↔ ((2 ≤ b ∧ 0 < n) → ipow b e ≤ n ∧ n < ipow b (e + 1))
        ∧ (¬(2 ≤ b ∧ 0 < n) → e = 0) :=
  Classical.choose!_eq_iff_right _

def _root_.LO.FirstOrder.Arithmetic.ilogDef : 𝚺₁.Semisentence 3 := .mkSigma
  “e b n. (2 ≤ b ∧ 0 < n → (∃ pe, !ipowDef pe b e ∧ pe ≤ n) ∧ (∃ pf, !ipowDef pf b (e + 1) ∧ n < pf))
        ∧ (¬(2 ≤ b ∧ 0 < n) → e = 0)”

instance ilog_defined : 𝚺₁-Function₂ (ilog : V → V → V) via ilogDef := .mk fun v ↦ by
  simp [ilogDef, ilog_graph, ipow_defined.iff]
  refine fun _ => ⟨fun h hyp => h ?_, fun h hyp => h (fun h2 => hyp.resolve_left (not_lt.mpr h2))⟩
  by_cases h2 : 2 ≤ v 1
  · exact Or.inr (hyp h2)
  · exact Or.inl (not_le.mp h2)

instance ilog_definable : 𝚺₁-Function₂ (ilog : V → V → V) := ilog_defined.to_definable

instance ilog_definable' (Γ) : Γ-[m + 1]-Function₂ (ilog : V → V → V) := ilog_definable.of_sigmaOne

end GoodsteinPA.InternalPow
