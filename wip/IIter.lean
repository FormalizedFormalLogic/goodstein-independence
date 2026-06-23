/-
# `wip/IIter.lean` — Crux 1 brick 2 core: internal iteration of a fixed `𝚺₁`-function

**Status: building the reusable internal-iterate primitive (wip, off the build target).**

The standard-level internal Grzegorczyk hierarchy `iF : ℕ → (V → V)` is built by **meta-recursion** on
the standard level `l : ℕ` (lap-50 insight: the headline needs only a *standard* level, so the level is
a fixed meta-natural, NOT an internal `V` — there is **no internal Ackermann**). Its recursion step is
Rathjen's diagonalisation

  `iF (l+1) n = (iF l)^[n] n`        (`Grz.F_succ`)

which iterates the *fixed* `𝚺₁`-total function `iF l` an **internal** number of times `n : V`. That
internal iteration is exactly what this file provides, generically: given any `f : V → V` with a `𝚺₁`
graph `fDef`, `iIter fDef f hf x c = f^[c] x` (internal `c`), as a genuine `𝚺₁` primitive recursion
(`PR.Construction`), with the two recurrence laws and the `𝚺₁`-definability of `(x, c) ↦ f^[c] x`.

Mirrors `InternalCor34.iVbigMul.construction` but with the iterated operation passed as data (`fDef`
+ the defined instance), so the same primitive serves every meta-level of `iF`.
-/
import GoodsteinPA.InternalCor34

namespace GoodsteinPA.IIter

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open GoodsteinPA

variable {V : Type*} [ORingStructure V] [V ⊧ₘ* 𝗜𝚺₁]

/-- Blueprint for `f^[·] x` (1 parameter = the start value `x`): `zero ↦ x`, `succ ↦ f (ih)`. The
iterated operation enters through its graph formula `fDef`. -/
def iIter.blueprint (fDef : 𝚺₁.Semisentence 2) : PR.Blueprint 1 where
  zero := .mkSigma “y x. y = x”
  succ := .mkSigma “y ih n x. !fDef y ih”

noncomputable def iIter.construction (fDef : 𝚺₁.Semisentence 2) (f : V → V)
    (hf : 𝚺₁.DefinedFunction₁ f fDef) : PR.Construction V (iIter.blueprint fDef) where
  zero := fun x ↦ x 0
  succ := fun _ _ ih ↦ f ih
  zero_defined := .mk fun v ↦ by simp [iIter.blueprint]
  succ_defined := .mk fun v ↦ by simp [iIter.blueprint, hf.iff]

/-- `f^[c] x` on internal `c : V`: the `V`-indexed iterate of the fixed `𝚺₁`-function `f`. -/
noncomputable def iIter (fDef : 𝚺₁.Semisentence 2) (f : V → V) (hf : 𝚺₁.DefinedFunction₁ f fDef)
    (x c : V) : V := (iIter.construction fDef f hf).result ![x] c

variable {fDef : 𝚺₁.Semisentence 2} {f : V → V} {hf : 𝚺₁.DefinedFunction₁ f fDef}

@[simp] lemma iIter_zero (x : V) : iIter fDef f hf x 0 = x := by
  simp [iIter, iIter.construction]

@[simp] lemma iIter_succ (x c : V) : iIter fDef f hf x (c + 1) = f (iIter fDef f hf x c) := by
  simp [iIter, iIter.construction]

/-- The `𝚺₁` graph of `(x, c) ↦ f^[c] x`. -/
def iIterDef (fDef : 𝚺₁.Semisentence 2) : 𝚺₁.Semisentence 3 :=
  (iIter.blueprint fDef).resultDef.rew (Rew.subst ![#0, #2, #1])

-- `f`/`hf` are not determined by `iIterDef fDef`, so these stay as named lemmas (not instances) —
-- each meta-level of `iF` supplies the concrete `f`/`hf` explicitly.
lemma iIter_defined : 𝚺₁-Function₂ (iIter fDef f hf : V → V → V) via iIterDef fDef := .mk
  fun v ↦ by
    simp [(iIter.construction fDef f hf).result_defined_iff, iIterDef, iIter]; rfl

lemma iIter_definable : 𝚺₁-Function₂ (iIter fDef f hf : V → V → V) :=
  (iIter_defined (hf := hf)).to_definable
lemma iIter_definable' (Γ) : Γ-[m + 1]-Function₂ (iIter fDef f hf : V → V → V) :=
  (iIter_definable (hf := hf)).of_sigmaOne

/-- **Standard iterate agreement.** For a *standard* iteration count `k : ℕ`, the internal iterate
`f^[k] x` coincides with the meta-iterate `f^[k]` applied at `x` — the bridge that lets every
meta-level of `iF` reduce to a fixed standard-many compositions when its argument is standard. -/
lemma iIter_natCast (x : V) : ∀ k : ℕ, iIter fDef f hf x (k : V) = f^[k] x := by
  intro k
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.cast_succ, iIter_succ, ih, Function.iterate_succ_apply']

end GoodsteinPA.IIter
