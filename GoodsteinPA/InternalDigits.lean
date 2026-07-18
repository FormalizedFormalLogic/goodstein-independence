/-
# `InternalDigits.lean` — E-core(b) brick 2: base-`b` digits inside `V`

Brick 2 of the arithmetization wall (`DESCENT-PLAN.md §3`, after `InternalPow.ipow`). The PA-side
proof of Rathjen's inequality (6) is phrased over **base-`b` numerals**: the order comparison and the
hereditary base-change `bump` (`S^b_{b+1}`) are operations on the base-`b` digits of a number. This
file gives the digit accessor and its basic laws inside an arbitrary `V ⊧ₘ* 𝗜𝚺₁`:

* `idigit b n i = (n / b^i) % b` — the `i`-th base-`b` digit of `n`.

with `idigit b n i < b` (for `0 < b`) and the `𝚺₁`-definability needed for internal induction. Brick 3
will assemble these into the base-`b` hereditary base-change.
-/
import GoodsteinPA.InternalPow
import GoodsteinPA.Compat

namespace GoodsteinPA.InternalPow

open LO LO.FirstOrder LO.FirstOrder.Arithmetic

variable {V : Type*} [ORingStructure V] [V ⊧ₘ* 𝗜𝚺₁]

/-- **`i`-th base-`b` digit of `n`**: `(n / b^i) % b`. -/
noncomputable def idigit (b n i : V) : V := (n / ipow b i) % b

/-- Every base-`b` digit is `< b` (for a positive base). -/
@[simp] lemma idigit_lt {b : V} (hb : 0 < b) (n i : V) : idigit b n i < b :=
  mod_lt _ hb

lemma idigit_zero_exp (b n : V) : idigit b n 0 = n % b := by simp [idigit]

/-- **Digit shift.** The `(i+1)`-th base-`b` digit of `n` is the `i`-th digit of `n / b`. This is the
recursion that lets digit facts be proved by induction on the position. -/
lemma idigit_succ_exp (b n i : V) : idigit b n (i + 1) = idigit b (n / b) i := by
  unfold idigit
  rw [ipow_succ, mul_comm, LO.FirstOrder.Arithmetic.div_mul]

instance idigit_definable : 𝚺₁-Function₃ (idigit : V → V → V → V) := by
  unfold idigit; definability

end GoodsteinPA.InternalPow
