/-
# `wip/IIter.lean` — Crux 1 brick 2 core: internal iteration of a fixed `𝚺₁`-function

**Status: COMPLETE (axiom-clean, in the build). Crux-1 brick 2 substrate.**

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
import GoodsteinPA.Grzegorczyk

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

/-! ## The standard-level Grzegorczyk hierarchy `iF` (internal, meta-recursion on level `l : ℕ`)

`iF 0 = (·+1)`, `iF (l+1) n = (iF l)^[n] n` (`Grz.F`), built by **meta-recursion on the standard level
`l : ℕ`** — at each level `iF l` is a fixed `𝚺₁`-total function, and the diagonal `(iF l)^[n] n` is the
internal iterate (`iIter`) at the internal count `n`. The recursion carries the **(function, Def,
defined-proof) triple** so each level's `iIter` call has the graph it needs. NO internal Ackermann:
the level never becomes an internal `V`. -/

/-- The `𝚺₁` graph of `iF l` (independent of the model). -/
def iFDef : ℕ → 𝚺₁.Semisentence 2
  | 0 => .mkSigma “y n. y = n + 1”
  | l + 1 => .mkSigma “y n. !(iIterDef (iFDef l)) y n n”

variable (V) in
/-- `iF l` bundled with its defined-proof, so the meta-recursion can feed `iIter`. -/
noncomputable def iFwith : (l : ℕ) → { f : V → V // 𝚺₁.DefinedFunction₁ f (iFDef l) }
  | 0 => ⟨fun n ↦ n + 1, .mk fun v ↦ by simp [iFDef]⟩
  | l + 1 =>
      ⟨fun n ↦ iIter (iFDef l) (iFwith l).1 (iFwith l).2 n n,
       .mk fun v ↦ by
         simp [iFDef, (iIter_defined (hf := (iFwith l).2)).iff]⟩

/-- The internal standard-level Grzegorczyk hierarchy `iF l : V → V`. -/
noncomputable def iF (l : ℕ) : V → V := (iFwith V l).1

/-- `iF l` is `𝚺₁`-definable by `iFDef l`. -/
lemma iF_defined (l : ℕ) : 𝚺₁.DefinedFunction₁ (iF l : V → V) (iFDef l) := (iFwith V l).2

@[simp] lemma iF_zero (n : V) : iF 0 n = n + 1 := rfl

theorem iF_succ (l : ℕ) (n : V) :
    iF (l + 1) n = iIter (iFDef l) (iF l) (iF_defined l) n n := rfl

lemma iF_definable (l : ℕ) : 𝚺₁-Function₁ (iF l : V → V) := (iF_defined l).to_definable
lemma iF_definable' (l : ℕ) (Γ) : Γ-[m + 1]-Function₁ (iF l : V → V) :=
  (iF_definable l).of_sigmaOne

/-- **Standard agreement.** On a standard input `k : ℕ`, `iF l` computes the meta-`Grz.F l`'s value.
Proved by meta-induction on `l` through `iIter_natCast` — the bridge that reduces every internal `iF`
fact at a standard argument to its kernel-checked `Grz` counterpart. -/
lemma iF_natCast : ∀ (l : ℕ) (k : ℕ), iF l (k : V) = (Grz.F l k : V) := by
  intro l
  induction l with
  | zero => intro k; simp [Grz.F]
  | succ l ih =>
      -- iterate agreement at level `l` for a *general* start, by induction on the count
      have iter_agree : ∀ (i x : ℕ), (iF l)^[i] (x : V) = ((Grz.F l)^[i] x : V) := by
        intro i
        induction i with
        | zero => intro x; simp
        | succ i ihi =>
            intro x
            rw [Function.iterate_succ_apply', ihi x, ih, Function.iterate_succ_apply']
      intro k
      rw [iF_succ, Grz.F_succ, iIter_natCast, iter_agree]

/-! ## Internal partial sum of iterates `ipsum` (substrate for the block decomposition)

`ipsum f n i = Σ_{t=1}^{i} f^[t] n` (`Grz.psum`), the cumulative block-width function whose level sets
give Rathjen's `m ↦ (blockIdx, blockOff)` decomposition. Internal `𝚺₁` accumulator recursion on the
block count `i : V`, reading each iterate via `iIter`. Generic over the fixed `𝚺₁`-function `f` (so it
serves every meta-level `iF l`). -/

/-- Blueprint for `ipsum` (1 parameter = the seed `n`): `zero ↦ 0`, `succ i ↦ ih + f^[i+1] n`. -/
def ipsum.blueprint (fDef : 𝚺₁.Semisentence 2) : PR.Blueprint 1 where
  zero := .mkSigma “y x. y = 0”
  succ := .mkSigma “y ih i x. ∃ w, !(iIterDef fDef) w x (i + 1) ∧ y = ih + w”

noncomputable def ipsum.construction (fDef : 𝚺₁.Semisentence 2) (f : V → V)
    (hf : 𝚺₁.DefinedFunction₁ f fDef) : PR.Construction V (ipsum.blueprint fDef) where
  zero := fun _ ↦ 0
  succ := fun x i ih ↦ ih + iIter fDef f hf (x 0) (i + 1)
  zero_defined := .mk fun v ↦ by simp [ipsum.blueprint]
  succ_defined := .mk fun v ↦ by
    simp [ipsum.blueprint, (iIter_defined (hf := hf)).iff]

/-- `ipsum f n i = Σ_{t=1}^{i} f^[t] n` on internal `i : V`. -/
noncomputable def ipsum (fDef : 𝚺₁.Semisentence 2) (f : V → V) (hf : 𝚺₁.DefinedFunction₁ f fDef)
    (n i : V) : V := (ipsum.construction fDef f hf).result ![n] i

@[simp] lemma ipsum_zero (n : V) : ipsum fDef f hf n 0 = 0 := by
  simp [ipsum, ipsum.construction]

@[simp] lemma ipsum_succ (n i : V) :
    ipsum fDef f hf n (i + 1) = ipsum fDef f hf n i + iIter fDef f hf n (i + 1) := by
  simp [ipsum, ipsum.construction]

/-- The `𝚺₁` graph of `(n, i) ↦ ipsum f n i`. -/
def ipsumDef (fDef : 𝚺₁.Semisentence 2) : 𝚺₁.Semisentence 3 :=
  (ipsum.blueprint fDef).resultDef.rew (Rew.subst ![#0, #2, #1])

lemma ipsum_defined : 𝚺₁-Function₂ (ipsum fDef f hf : V → V → V) via ipsumDef fDef := .mk
  fun v ↦ by simp [(ipsum.construction fDef f hf).result_defined_iff, ipsumDef, ipsum]; rfl

lemma ipsum_definable : 𝚺₁-Function₂ (ipsum fDef f hf : V → V → V) :=
  (ipsum_defined (hf := hf)).to_definable
lemma ipsum_definable' (Γ) : Γ-[m + 1]-Function₂ (ipsum fDef f hf : V → V → V) :=
  (ipsum_definable (hf := hf)).of_sigmaOne

/-- **`ipsum` is monotone in the block count** (each block has nonneg width). -/
lemma ipsum_le_succ (n i : V) : ipsum fDef f hf n i ≤ ipsum fDef f hf n (i + 1) := by
  rw [ipsum_succ]; exact le_self_add

end GoodsteinPA.IIter
