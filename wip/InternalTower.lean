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
import GoodsteinPA.Compat

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

/-! ## Cross-level steps — the `dg`-drop descent cases of Thm 4.2

When a reduction `d ↦ d[k]` lowers the degree (`dg(d[k]) = dg(d) - 1`, the `Ind`/`K^r` cases), the
descent `o(d[k]) ≺ o(d)` crosses tower levels: `ω_m(α) ≺ ω_{m+1}(β)`. The crux is `α ≺ ω^α`
(`self_lt_omega_pow`): one tower step strictly increases. Foundation: `ocExp c ≺ c` (a CNF code's
leading exponent is `≺` the whole code). -/

/-- **A CNF code's leading exponent is `≺` the code**: `icmp (ocExp c) c = 0` (NF `c ≠ 0`). Strong
induction: the head exponent `ocExp c` compares to `c` via its own lead `ocExp (ocExp c) ≺ ocExp c`
(IH on the smaller code `ocExp c`). -/
lemma icmp_ocExp_self : ∀ w : V, ∀ c ≤ w, isNF c → c ≠ 0 → icmp (ocExp c) c = 0 := by
  intro w
  induction w using ISigma1.sigma1_order_induction
  · definability
  case ind w ih =>
    intro c hcw hc hc0
    rcases eq_or_ne (ocExp c) 0 with he | he
    · rw [he]; exact icmp_zero_pos hc0
    · have hlt : ocExp c < c := by
        have h := ocExp_lt (ocExp c) (ocCoeff c) (ocTail c)
        rwa [ocOadd_destruct hc0] at h
      have hnf_exp : isNF (ocExp c) :=
        ((isNF_ocOadd (ocExp c) (ocCoeff c) (ocTail c)).1
          (by rw [ocOadd_destruct hc0]; exact hc)).2.1
      rw [icmp_pos_pos he hc0]
      have hkey : icmp (ocExp (ocExp c)) (ocExp c) = 0 :=
        ih (ocExp c) (lt_of_lt_of_le hlt hcw) (ocExp c) le_rfl hnf_exp he
      rw [hkey]; simp [thenV]

/-- **`α ≺ ω^α`** (NF `α`): every code is strictly below its own `ω`-power. The lead exponent of `ω^α`
is `α`, while `α`'s own lead exponent is `≺ α` (`icmp_ocExp_self`), so the head decides. -/
lemma self_lt_omega_pow {α : V} (hα : isNF α) : icmp α (ocOadd α 1 0) = 0 := by
  rcases eq_or_ne α 0 with rfl | h0
  · exact icmp_zero_pos (ocOadd_ne_zero _ _ _)
  · exact icmp_pos_ocOadd_lt_exp h0 (icmp_ocExp_self α α le_rfl hα h0)

/-- **One tower step strictly increases**: `ω_m(α) ≺ ω_{m+1}(α)` (NF `α`). -/
lemma icmp_iotower_lt_succ {α : V} (hα : isNF α) (m : V) :
    icmp (iotower α m) (iotower α (m + 1)) = 0 := by
  rw [iotower_succ]; exact self_lt_omega_pow (isNF_iotower hα m)

/-- **The `dg`-drop descent step**: if `ω_m(α) ≼ ω_m(β)` (strictly `≺`, or `=`), then
`ω_m(α) ≺ ω_{m+1}(β)`. Composes `≼` at level `m` with the strict step `ω_m(β) ≺ ω_{m+1}(β)`. This is
the inequality Thm 4.2 needs whenever the reduction lowers the degree. -/
lemma icmp_iotower_lt_succ_of_le {α β : V} (hβ : isNF β) (m : V)
    (h : icmp (iotower α m) (iotower β m) = 0 ∨ iotower α m = iotower β m) :
    icmp (iotower α m) (iotower β (m + 1)) = 0 := by
  have hstep : icmp (iotower β m) (iotower β (m + 1)) = 0 := icmp_iotower_lt_succ hβ m
  rcases h with hlt | heq
  · set a := iotower α m
    set b := iotower β m
    set c := iotower β (m + 1)
    exact icmp_trans (max a (max b c)) a (le_max_left _ _)
      b (le_trans (le_max_left _ _) (le_max_right _ _))
      c (le_trans (le_max_right _ _) (le_max_right _ _)) hlt hstep
  · rw [heq]; exact hstep

/-- **Tower height-monotonicity (strict, gap `k+1`)**: `ω_m(β) ≺ ω_{m+(k+1)}(β)` (NF `β`).
The tower strictly increases as the height grows by any positive gap. Proven by induction on the
gap `k`: base = the one-step `icmp_iotower_lt_succ`, step = transitivity through one more level. -/
lemma icmp_iotower_lt_add_succ {β : V} (hβ : isNF β) (m k : V) :
    icmp (iotower β m) (iotower β (m + (k + 1))) = 0 := by
  induction k using ISigma1.sigma1_succ_induction
  · definability
  case zero => simpa using icmp_iotower_lt_succ hβ m
  case succ k ih =>
    rw [show m + (k + 1 + 1) = (m + (k + 1)) + 1 from (add_assoc m (k + 1) 1).symm]
    have hstep : icmp (iotower β (m + (k + 1))) (iotower β ((m + (k + 1)) + 1)) = 0 :=
      icmp_iotower_lt_succ hβ (m + (k + 1))
    exact icmp_trans
      (max (iotower β m) (max (iotower β (m + (k + 1))) (iotower β ((m + (k + 1)) + 1))))
      _ (le_max_left _ _)
      _ (le_trans (le_max_left _ _) (le_max_right _ _))
      _ (le_trans (le_max_right _ _) (le_max_right _ _)) ih hstep

/-- **Tower height-monotonicity (non-strict)**: `ω_m(β) ≼ ω_{m'}(β)` for `m ≤ m'` (NF `β`).
This is the general height-monotone step the cut-elimination nut (Buchholz Lemma 4.1(b)(ii) case 5.1,
judge `E-CRUX2-DECOMPOSITION-2026-06-24.md` §8.3 N4(iii)) needs: there the degree can drop by an
arbitrary gap `dg(d[0]) < dg(d)`, so the single-step `icmp_iotower_lt_succ_of_le` is not enough. -/
lemma icmp_iotower_height_le {β : V} (hβ : isNF β) {m m' : V} (h : m ≤ m') :
    icmp (iotower β m) (iotower β m') = 0 ∨ iotower β m = iotower β m' := by
  obtain ⟨k, rfl⟩ := le_iff_exists_add.mp h
  rcases eq_or_ne k 0 with rfl | hk
  · right; rw [add_zero]
  · obtain ⟨j, rfl⟩ := le_iff_exists_add.mp (pos_iff_one_le.mp (pos_iff_ne_zero.mpr hk))
    rw [add_comm 1 j]
    exact Or.inl (icmp_iotower_lt_add_succ hβ m j)

/-- **Base-shift identity** `ω_m(ω^α) = ω_{m+1}(α)`: the height-`m` tower over base `ω^α` equals the
height-`(m+1)` tower over `α`. Pure structural identity (`ω^· = ocOadd · 1 0`). **This is the exact
tower step Thm 4.2's critical (cut-elimination) case needs** — the degree-drop nut combines
`o(d[0]) = ω_{dg(d[0])}(õ(d[0])) ≺ ω_{dg(d[0])}(ω^{õ(d)}) = ω_{dg(d[0])+1}(õ(d)) ≼ ω_{dg(d)}(õ(d))`,
and this lemma supplies the middle equality (judge `E-CRUX2-DECOMPOSITION-2026-06-24.md` §4, pt-7
validation: `icmp_iotower_lt_succ_of_le` gives the height-monotone step, this gives the base shift). -/
lemma iotower_omega_pow (α m : V) :
    iotower (ocOadd α 1 0) m = iotower α (m + 1) := by
  induction m using ISigma1.sigma1_succ_induction
  · definability
  case zero => rw [iotower_zero, iotower_succ, iotower_zero]
  case succ m ih => rw [iotower_succ, ih, ← iotower_succ]

end GoodsteinPA.InternalONote
