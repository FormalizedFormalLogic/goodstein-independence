/-
# `InternalGoodstein.lean` — E-core(b) brick 5: the internal Goodstein sequence in `V`

Brick 5 (`DESCENT-PLAN.md §3`). With the hereditary base-change `ibump` built and proven correct
(`InternalBump`), the Goodstein run itself is **structural** recursion on the step index (single
predecessor), so it goes straight through `PR.Construction`:

  `Defs.goodsteinSeq m 0 = m`,   `Defs.goodsteinSeq m (k+1) = bump (k+2) (goodsteinSeq m k) - 1`.

`igoodstein m₀ k` is the `𝚺₁`-definable run `k ↦ mₖ` inside an arbitrary `V ⊧ₘ* 𝗜𝚺₁` — the concrete
`m : V → V` that `DescentArith.ineq6_internal` abstracts over. Brick 6 will be the `b`-side bound
`T̂^{k+2}∘β` and the internal `ineq6_step`.
-/
import GoodsteinPA.InternalBump
import GoodsteinPA.Compat

namespace GoodsteinPA.InternalPow

open LO LO.FirstOrder LO.FirstOrder.Arithmetic

variable {V : Type*} [ORingStructure V] [V ⊧ₘ* 𝗜𝚺₁]

/-- Blueprint for the Goodstein run: `zero ↦ m₀`, `succ : (k, v) ↦ ibump (k+2) v - 1`. -/
def goodstein.blueprint : PR.Blueprint 1 where
  zero := .mkSigma “y x. y = x”
  succ := .mkSigma “y ih n x. ∃ w, !ibumpDef w (n + 2) ih ∧ !subDef y w 1”

noncomputable def goodstein.construction : PR.Construction V goodstein.blueprint where
  zero := fun x ↦ x 0
  succ := fun _ n ih ↦ ibump (n + 2) ih - 1
  zero_defined := .mk fun v ↦ by simp [goodstein.blueprint]
  succ_defined := .mk fun v ↦ by
    simp [goodstein.blueprint, ibump_defined.iff, sub_defined.iff]

/-- **Internal Goodstein sequence** `igoodstein m₀ k = mₖ` in `V` (over the audited base `k+2`). -/
noncomputable def igoodstein (m₀ k : V) : V := goodstein.construction.result ![m₀] k

@[simp] lemma igoodstein_zero (m₀ : V) : igoodstein m₀ 0 = m₀ := by
  simp [igoodstein, goodstein.construction]

@[simp] lemma igoodstein_succ (m₀ k : V) :
    igoodstein m₀ (k + 1) = ibump (k + 2) (igoodstein m₀ k) - 1 := by
  simp [igoodstein, goodstein.construction]

section

def _root_.LO.FirstOrder.Arithmetic.igoodsteinDef : 𝚺₁.Semisentence 3 :=
  goodstein.blueprint.resultDef.rew (Rew.subst ![#0, #2, #1])

instance igoodstein_defined : 𝚺₁-Function₂ (igoodstein : V → V → V) via igoodsteinDef := .mk
  fun v ↦ by simp [goodstein.construction.result_defined_iff, igoodsteinDef]; rfl

instance igoodstein_definable : 𝚺₁-Function₂ (igoodstein : V → V → V) := igoodstein_defined.to_definable

instance igoodstein_definable' (Γ) : Γ-[m + 1]-Function₂ (igoodstein : V → V → V) :=
  igoodstein_definable.of_sigmaOne

end

end GoodsteinPA.InternalPow
