/-
# `wip/InternalTower.lean` — the internal ω-exponential tower `ω_n(α)` on CNF codes

**Status: wip brick for crux 2 (lap 60).** Buchholz's §4 ordinal assignment closes with
`o(d) := ω_{dg(d)}(õ(d))`, where `ω_0(α) := α`, `ω_{n+1}(α) := ω^{ω_n(α)}`
(`CRUX2-ORD-ASSIGNMENT-2026-06-24.md`). This is the `dg(d)`-fold ω-exponential tower over the
pre-ordinal `õ(d)`. The degree `dg(d)` is an internal `V`-number (possibly nonstandard), so the tower
is a genuine internal primitive recursion on a counter `n`, parameterized by the base `α`.

Built directly via `PR.Construction` (no course-of-values table needed — each step uses only the
immediately previous value). Key facts: `iotower_zero`/`iotower_succ` (the recursion), `isNF_iotower`
(NF preservation), and **`icmp_iotower_mono`** — strict monotonicity in the base
(`icmp α β = 0 → icmp (ω_n α) (ω_n β) = 0`), the engine of Thm 4.2's descent when `dg` is preserved
(`o(d[k]) = ω_dg(õ(d[k])) ≺ ω_dg(õ(d)) = o(d)` from `õ(d[k]) ≺ õ(d)`). Cross-level steps
(`ω_m(α) ≺ ω_{m+1}(β)`, for the `dg`-drop cases) are pinned in `PENDING_WORK.md`.
-/
import GoodsteinPA.InternalNadd

namespace GoodsteinPA.InternalONote

open Classical
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.HierarchySymbol ISigma1 PeanoMinus

variable {V : Type*} [ORingStructure V] [V ⊧ₘ* 𝗜𝚺₁]

/-! ## `iotower α n = ω_n(α)` — the internal ω-exponential tower (recursion on counter `n`) -/

/-- Blueprint for `ω_n(α)` (parameter = base `α`): `ω_0 = α`, `ω_{n+1} = ω^{ω_n} = ocOadd ω_n 1 0`. -/
def iotower.blueprint : PR.Blueprint 1 where
  zero := .mkSigma “y x. y = x”
  succ := .mkSigma “y ih n x. !ocOaddDef y ih 1 0”

noncomputable def iotower.construction : PR.Construction V iotower.blueprint where
  zero := fun x ↦ x 0
  succ := fun _ _ ih ↦ ocOadd ih 1 0
  zero_defined := .mk fun v ↦ by simp [iotower.blueprint]
  succ_defined := .mk fun v ↦ by simp [iotower.blueprint, ocOadd_defined.iff]

/-- **The internal ω-tower** `ω_n(α)` inside `V`. -/
noncomputable def iotower (α n : V) : V := iotower.construction.result ![α] n

@[simp] lemma iotower_zero (α : V) : iotower α 0 = α := by
  simp [iotower, iotower.construction]

@[simp] lemma iotower_succ (α n : V) : iotower α (n + 1) = ocOadd (iotower α n) 1 0 := by
  simp [iotower, iotower.construction]

def _root_.LO.FirstOrder.Arithmetic.iotowerDef : 𝚺₁.Semisentence 3 :=
  iotower.blueprint.resultDef.rew (Rew.subst ![#0, #2, #1])

instance iotower_defined : 𝚺₁-Function₂ (iotower : V → V → V) via iotowerDef := .mk
  fun v ↦ by simp [iotower.construction.result_defined_iff, iotowerDef]; rfl

instance iotower_definable : 𝚺₁-Function₂ (iotower : V → V → V) := iotower_defined.to_definable
instance iotower_definable' (Γ) : Γ-[m + 1]-Function₂ (iotower : V → V → V) :=
  iotower_definable.of_sigmaOne

/-! ## Structural facts -/

/-- **`ω_n(α)` is positive for `n ≥ 1`** (it is an `ω`-power `ocOadd _ 1 0`). -/
lemma iotower_succ_ne_zero (α n : V) : iotower α (n + 1) ≠ 0 := by
  rw [iotower_succ]; exact ocOadd_ne_zero _ _ _

/-- **NF preservation.** If `α` is NF then so is every tower level `ω_n(α)` — each step is the
single-term `ω`-power `ocOadd (ω_n α) 1 0`, NF whenever its exponent is. -/
lemma isNF_iotower {α : V} (hα : isNF α) : ∀ n, isNF (iotower α n) := by
  intro n
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero => rw [iotower_zero]; exact hα
  case succ n ih =>
    rw [iotower_succ, isNF_ocOadd]
    exact ⟨(by simp), ih, isNF_zero, Or.inl rfl⟩

/-- **Strict monotonicity in the base** (the same-degree descent engine of Buchholz Thm 4.2):
`α ≺ β ⟹ ω_n(α) ≺ ω_n(β)` for every level `n`. `n = 0` is the hypothesis; the step uses that
`ω^·` is an order-embedding (`icmp_omega_pow`). -/
lemma icmp_iotower_mono {α β : V} (h : icmp α β = 0) :
    ∀ n, icmp (iotower α n) (iotower β n) = 0 := by
  intro n
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero => rw [iotower_zero, iotower_zero]; exact h
  case succ n ih =>
    rw [iotower_succ, iotower_succ, icmp_omega_pow]; exact ih

end GoodsteinPA.InternalONote
