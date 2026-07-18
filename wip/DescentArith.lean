/-
# `DescentArith.lean` — E-core(b) arithmetization: the inequality-(6) PA-induction, ASSEMBLED

The deep wall of the descent **E** is **E-core(b)** (see `DESCENT-PLAN.md §3`): re-expressing Rathjen
§3 *inside* PA. Its irreducible kernel is **inequality (6)** `∀ k, mₖ ≥ T̂^{k+2}_ω(βₖ)` (the special
Goodstein run seeded at `T̂²_ω(β₀)` never reaches `0`) carried out as a genuine PA-induction — the one
piece that is NOT free Σ₁ reflection (it is `Π₁ = ∀` of `Δ₀`).

This file discharges the **induction scaffold** of that kernel against the real Foundation `𝗜𝚺₁`
machinery, isolating the remaining work behind a clean, typechecked interface. Working inside an
arbitrary model `V ⊧ₘ* 𝗜𝚺₁`, given

* the run `m : V → V` (`k ↦ mₖ`) and the bound `b : V → V` (`k ↦ T̂^{k+2}_ω(βₖ)`) as **`𝚺₁`-functions**,
* the base `b 0 ≤ m 0`, and
* the **internalized `ineq6_step`** `∀ k, b k ≤ m k → b (k+1) ≤ m (k+1)`,

the conclusion `∀ k, b k ≤ m k` follows by `sigma1_pos_succ_induction` (the `𝗜𝚺₁` succ-induction). The
predicate `fun k ↦ b k ≤ m k` is `𝚺₁` (a `≤`-comparison of two `𝚺₁`-functions), so the induction applies
directly — the feasibility verified in `DESCENT-PLAN.md §3b` is here **machine-checked**.

**What remains (the deep multi-lap layer, NOT in this file):** supplying the concrete `𝚺₁`-definable `m`
(the internalized `goodsteinSeq`/`bump`, buildable on Foundation's `𝗜𝚺₁` `log`/`exp`/`bexp`) and `b`,
and proving the internalized `ineq6_step` (the numeral-`Δ₀` form of `DescentCore.ineq6_step`). This file
makes the *assembly* of those pieces axiom-clean and unambiguous.
-/
import Foundation.FirstOrder.Arithmetic.Induction
import GoodsteinPA.Compat

namespace GoodsteinPA.DescentArith

open LO LO.FirstOrder LO.FirstOrder.Arithmetic

variable {V : Type*} [ORingStructure V] [V ⊧ₘ* 𝗜𝚺₁]

/-- **Arithmetized inequality (6), induction scaffold.** Inside `𝗜𝚺₁`: from a base `b 0 ≤ m 0` and the
internalized step `b k ≤ m k → b (k+1) ≤ m (k+1)` (the `Δ₀` numeral form of `Dom.ineq6_step`), the run
`m` dominates the bound `b` at every stage. The predicate is `𝚺₁` (comparison of `𝚺₁`-functions), so
`sigma1_pos_succ_induction` applies. This is the PA-internal core of Rathjen Lemma 3.6 — modulo the
`𝚺₁`-definability of `m`, `b` (the remaining deep layer). -/
theorem ineq6_internal {m b : V → V}
    (hm : 𝚺₁-Function₁ m) (hb : 𝚺₁-Function₁ b)
    (base : b 0 ≤ m 0)
    (step : ∀ k, b k ≤ m k → b (k + 1) ≤ m (k + 1)) :
    ∀ k, b k ≤ m k := by
  have hP : 𝚺₁-Predicate fun k => b k ≤ m k := by definability
  refine sigma1_pos_succ_induction hP base (by simpa using step 0 base) ?_
  intro x hx
  simpa [add_assoc, one_add_one_eq_two] using step (x + 1) hx

/-- **Non-termination corollary (PA-internal form).** If additionally the bound is positive at every
stage (`0 < b k`, true since `βₖ ≻ 0`), then the run never reaches `0` — the arithmetized Lemma 3.6.
This is the contradiction E-core feeds the lifted `goodsteinSentence`: a Goodstein run that provably
(in PA) never terminates, refuting `𝗣𝗔 ⊢ goodstein`. -/
theorem nonterminating_internal {m b : V → V}
    (hm : 𝚺₁-Function₁ m) (hb : 𝚺₁-Function₁ b)
    (base : b 0 ≤ m 0)
    (step : ∀ k, b k ≤ m k → b (k + 1) ≤ m (k + 1))
    (hpos : ∀ k, 0 < b k) :
    ∀ k, 0 < m k := fun k => lt_of_lt_of_le (hpos k) (ineq6_internal hm hb base step k)

end GoodsteinPA.DescentArith
