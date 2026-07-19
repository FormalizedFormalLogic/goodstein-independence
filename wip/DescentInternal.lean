/-
# `DescentInternal.lean` — E-core(b): wire the bridged internal Goodstein run into the (6)-scaffold

`DescentArith.ineq6_internal`/`nonterminating_internal` are the inequality-(6) PA-induction scaffold,
abstracted over a `𝚺₁`-function run `m` and bound `b`. With `InternalGoodstein`'s `igoodstein` now
**built and proven faithful** (`InternalBridge.igoodstein_nat`: it computes the audited
`Defs.goodsteinSeq` on `ℕ`), this file supplies the concrete `m := igoodstein m₀` and reduces E-core(b)'s
non-termination to the remaining deep obligation: a `𝚺₁`-bound `b k = T̂^{k+2}_ω(βₖ)` dominating the run
plus the internalized `ineq6_step`.

This makes the *run side* of the assembly axiom-clean and pins precisely what is left (the `b`/`βₖ`
slow-down side and the internal step), which in the Route-B form is fed by the `X`-definable descent
extracted from `¬TI prec` (see `DESCENT-PLAN.md §3` + `ON-LINE-REQUEST.md`).
-/
import GoodsteinPA.DescentArith
import GoodsteinPA.InternalBridge
import GoodsteinPA.Compat

namespace GoodsteinPA.DescentArith

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.HierarchySymbol
open GoodsteinPA.InternalPow

variable {V : Type*} [ORingStructure V] [V ⊧ₘ* 𝗜𝚺₁]

/-- The internalized Goodstein run `k ↦ igoodstein m₀ k` is `𝚺₁`-definable as a unary function
(partial application of the binary `igoodstein_definable`). -/
theorem igoodstein_sigma1 (m₀ : V) : 𝚺₁-Function₁ (igoodstein m₀) :=
  DefinableFunction₂.comp (DefinableFunction.const m₀) (DefinableFunction.var 0)

/-- **E-core(b) assembly — run side.** Plugging the bridged internal Goodstein run into the
inequality-(6) scaffold: if a `𝚺₁`-bound `b` is positive everywhere, dominates the run at the seed
(`b 0 ≤ m₀`), and is preserved by the internalized step, then the run **never reaches `0`** inside any
`V ⊧ₘ* 𝗜𝚺₁` (hence in `𝗣𝗔`). This is the PA-internal non-termination that contradicts the lifted
`goodsteinSentence`; the remaining deep obligation is exactly `(b, step)` — Rathjen §3's slow-down +
the internalized `ineq6_step`. -/
theorem igoodstein_nonterminating_of_dominating {b : V → V} (hb : 𝚺₁-Function₁ b) (m₀ : V)
    (base : b 0 ≤ m₀)
    (step : ∀ k, b k ≤ igoodstein m₀ k → b (k + 1) ≤ igoodstein m₀ (k + 1))
    (hpos : ∀ k, 0 < b k) :
    ∀ k, 0 < igoodstein m₀ k :=
  nonterminating_internal (igoodstein_sigma1 m₀) hb (by simpa using base) step hpos

end GoodsteinPA.DescentArith
