/-
# `InternalPow.lean` — E-core(b) brick 1: internalized base-`b` power as a `𝚺₁`-function in `V`

The deep wall of the descent **E** is **E-core(b)** (`DESCENT-PLAN.md §3`): re-expressing Rathjen §3
*inside* PA. Its kernel — inequality (6) — is arithmetized over **base-`b` numerals** (the digit /
hereditary-base-change view), so the very first prerequisite is a `𝚺₁`-definable variable-base power
`b ^ x` inside an arbitrary `V ⊧ₘ* 𝗜𝚺₁`.

Foundation's `Exponential`/`exp`/`bexp` machinery is **base-2 only** (`Arithmetic/Exponential/`); there
is no general variable-base power. We build one here from the generic primitive-recursion engine
`PR.Blueprint`/`PR.Construction` (`HFS/PRF.lean`), exactly the way `repeatVec` (`HFS/Vec.lean`) is built:

* `ipow b 0     = 1`
* `ipow b (x+1) = ipow b x * b`

and the engine certifies `ipow` is a genuine **`𝚺₁`-function** of `(b, x)` — the form the inequality-(6)
internal induction (`DescentArith.ineq6_internal`) consumes. This is brick 1 of the multi-lap wall;
brick 2 will be base-`b` digit extraction, brick 3 the hereditary base-change `bump`.
-/
import Foundation.FirstOrder.Arithmetic.HFS
import GoodsteinPA.Compat

namespace GoodsteinPA.InternalPow

open LO LO.FirstOrder LO.FirstOrder.Arithmetic

variable {V : Type*} [ORingStructure V] [V ⊧ₘ* 𝗜𝚺₁]

/-- Primitive-recursion blueprint for variable-base power: one parameter (the base `x = b`),
`zero ↦ 1`, `succ : ih ↦ ih * b`. -/
def pow.blueprint : PR.Blueprint 1 where
  zero := .mkSigma “y x. y = 1”
  succ := .mkSigma “y ih n x. y = ih * x”

/-- The model-side construction realizing `pow.blueprint`: `zero v = 1`, `succ v i ih = ih * b`. Both
component functions are `𝚺₀` (hence `𝚺₁`) so the engine yields a `𝚺₁`-definable result. -/
noncomputable def pow.construction : PR.Construction V pow.blueprint where
  zero := fun _ ↦ 1
  succ := fun x _ ih ↦ ih * x 0
  zero_defined := .mk fun v ↦ by simp [pow.blueprint]
  succ_defined := .mk fun v ↦ by simp [pow.blueprint]

/-- **Internalized variable-base power** `b ^ x` inside `V`, via primitive recursion on `x`. -/
noncomputable def ipow (b x : V) : V := pow.construction.result ![b] x

@[simp] lemma ipow_zero (b : V) : ipow b 0 = 1 := by simp [ipow, pow.construction]

@[simp] lemma ipow_succ (b x : V) : ipow b (x + 1) = ipow b x * b := by simp [ipow, pow.construction]

section

/-- `𝚺₁`-definition of `ipow`, with the argument order `(output, b, x)`. -/
def _root_.LO.FirstOrder.Arithmetic.ipowDef : 𝚺₁.Semisentence 3 :=
  pow.blueprint.resultDef.rew (Rew.subst ![#0, #2, #1])

instance ipow_defined : 𝚺₁-Function₂ (ipow : V → V → V) via ipowDef := .mk
  fun v ↦ by simp [pow.construction.result_defined_iff, ipowDef]; rfl

instance ipow_definable : 𝚺₁-Function₂ (ipow : V → V → V) := ipow_defined.to_definable

instance ipow_definable' (Γ) : Γ-[m + 1]-Function₂ (ipow : V → V → V) := ipow_definable.of_sigmaOne

end

/-! ### Power laws (internal induction in `𝗜𝚺₁`) -/

@[simp] lemma ipow_one (b : V) : ipow b 1 = b := by
  have : (1 : V) = 0 + 1 := by simp
  rw [this, ipow_succ, ipow_zero, one_mul]

lemma one_le_ipow {b : V} (hb : 1 ≤ b) (x : V) : 1 ≤ ipow b x := by
  induction x using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ x ih =>
    rw [ipow_succ]
    calc (1 : V) = 1 * 1 := by simp
      _ ≤ ipow b x * b := mul_le_mul' ih hb

lemma ipow_pos {b : V} (hb : 0 < b) (x : V) : 0 < ipow b x := by
  induction x using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ x ih => rw [ipow_succ]; exact mul_pos ih hb

lemma ipow_add (b x y : V) : ipow b (x + y) = ipow b x * ipow b y := by
  induction y using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ y ih =>
    rw [show x + (y + 1) = (x + y) + 1 from (add_assoc x y 1).symm,
      ipow_succ, ipow_succ, ih, mul_assoc]

lemma ipow_le_ipow_right {b : V} (hb : 1 ≤ b) {x y : V} (h : x ≤ y) :
    ipow b x ≤ ipow b y := by
  obtain ⟨d, rfl⟩ := le_iff_exists_add.mp h
  rw [ipow_add]
  calc ipow b x = ipow b x * 1 := by simp
    _ ≤ ipow b x * ipow b d := mul_le_mul_right (one_le_ipow hb d) _

lemma ipow_lt_ipow_right {b : V} (hb : 1 < b) {x y : V} (h : x < y) :
    ipow b x < ipow b y := by
  have hb0 : (0 : V) < b := lt_trans (by simp) hb
  have hb1 : (1 : V) ≤ b := le_of_lt hb
  obtain ⟨d, rfl⟩ := le_iff_exists_add.mp (le_of_lt h)
  have hd : 0 < d := by
    by_contra hd0
    have : d = 0 := by simpa using (nonpos_iff_eq_zero.mp (not_lt.mp hd0))
    rw [this] at h; simp at h
  rw [ipow_add]
  calc ipow b x = ipow b x * 1 := by simp
    _ < ipow b x * b := mul_lt_mul_of_pos_left hb (ipow_pos hb0 x)
    _ ≤ ipow b x * ipow b d := by
        apply _root_.mul_le_mul_right
        calc b = ipow b 1 := (ipow_one b).symm
          _ ≤ ipow b d := ipow_le_ipow_right hb1 (pos_iff_one_le.mp hd)

/-- `ipow` is monotone in the **base**: `b ≤ c → ipow b x ≤ ipow c x`. -/
lemma ipow_le_ipow_left {b c : V} (h : b ≤ c) (x : V) : ipow b x ≤ ipow c x := by
  induction x using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ x ih =>
    rw [ipow_succ, ipow_succ]
    exact mul_le_mul ih h (Arithmetic.zero_le b) (Arithmetic.zero_le (ipow c x))

/-- `ipow` is **strictly** monotone in the base at a positive exponent:
`b < c → 0 < x → ipow b x < ipow c x`. -/
lemma ipow_lt_ipow_left {b c : V} (hbc : b < c) {x : V} (hx : 0 < x) :
    ipow b x < ipow c x := by
  have hc0 : 0 < c := lt_of_le_of_lt (Arithmetic.zero_le b) hbc
  obtain ⟨m, rfl⟩ : ∃ m, x = m + 1 :=
    ⟨x - 1, (sub_add_self_of_le (pos_iff_one_le.mp hx)).symm⟩
  rw [ipow_succ, ipow_succ]
  exact mul_lt_mul' (ipow_le_ipow_left (le_of_lt hbc) m) hbc (Arithmetic.zero_le b) (ipow_pos hc0 m)

end GoodsteinPA.InternalPow
