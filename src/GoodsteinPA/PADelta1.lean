/-
# Discharging `PA_delta1Definable` — the second front to the axiom-free headline

**Goal (operator directive, lap 78).** The headline `peano_not_proves_goodstein` must be
`#print axioms`-clean (trust base only). Two blockers: crux 2 (the `RedSound` cut-elimination,
architecture-blocked — see `ANALYSIS-2026-06-24-lap78-criticality-substitution-wall.md`) and
**`PA_delta1Definable`** — Foundation's disclosed `axiom 𝗣𝗔.Δ₁` (`Incompleteness/Examples.lean:17`,
the arithmetization of PA's Δ₁-definability, a standing TODO upstream). Gödel II for `𝗣𝗔`
(`peano_not_proves_consistency`, `Reduction.lean`) routes through it, so the headline carries it.

This file discharges that axiom **without editing the pinned Foundation package**: it rebuilds the
`𝗣𝗔.Δ₁` instance in-repo as a `def`, so `Reduction.lean` can pass it explicitly to
`consistent_unprovable` and drop `PA_delta1Definable` from `#print axioms`.

## Status (lap 78)
- ✅ `paMinusDelta1 : 𝗣𝗔⁻.Δ₁` — **axiom-clean.** `𝗣𝗔⁻` is finite (`PeanoMinus.finite`), so
  `Theory.Δ₁.ofFinite` gives it directly (the `singleton`/`add`/`ofList` combinators enumerate the
  17 axioms + the finite `𝗘𝗤` over `ℒₒᵣ`).
- ⏳ `inductionSchemeUnivDelta1 : (InductionScheme ℒₒᵣ Set.univ).Δ₁` — **the genuine wall** (one
  disclosed `sorry`). The infinite induction scheme has no finite enumeration; it needs an internal
  Δ₁ recognizer for codes of `univCl (succInd φ)`. See the obligation note on that def.
- ✅ `paDelta1 : 𝗣𝗔.Δ₁ := paMinusDelta1.add inductionSchemeUnivDelta1` — the assembly is `rfl`-valid
  (`𝗣𝗔 = 𝗣𝗔⁻ + InductionScheme ℒₒᵣ Set.univ`); ready to rewire `Reduction.lean` once the scheme is
  sorry-free.

ANTI-FRAUD: `paDelta1` carries `sorryAx` until `inductionSchemeUnivDelta1` is real. Do NOT rewire
`Reduction.lean` to `paDelta1` while the `sorry` stands — that would merely swap `PA_delta1Definable`
for `sorryAx` with no honesty gain. Rewire only when the scheme recognizer is machine-checked.
-/
import Foundation.FirstOrder.Incompleteness.Examples

namespace GoodsteinPA

open LO LO.FirstOrder LO.FirstOrder.Arithmetic

/-! ## Brick 1 — the internal `succInd` builder (lap 78, axiom-clean)

`succIndCodeT` mirrors `succInd φ = φ/[0] 🡒 ∀⁰(φ/[#0] 🡒 φ/[#0+1]) 🡒 ∀⁰ φ/[#0]` on Foundation's
typed coded-formula layer (`Bootstrapping.Semiformula`), and `succIndCodeT_quote` proves it commutes
with the quote: `succIndCodeT ⌜φ⌝ = ⌜succInd φ⌝`. This is the first reusable piece of the
induction-axiom recognizer; only the universal-closure wrapper (`univCl`) remains. -/

section SuccIndCode

open LO.FirstOrder.Arithmetic.Bootstrapping
open LO.FirstOrder.Arithmetic.Bootstrapping.Arithmetic

variable {V : Type*} [ORingStructure V] [V ⊧ₘ* 𝗜𝚺₁]

/-- Internal `succInd` builder on the typed coded-formula layer: from a code `p` of a 1-bound-var
formula, build the code of `succInd`'s matrix `p/[0] 🡒 ∀⁰(p/[#0] 🡒 p/[#0+1]) 🡒 ∀⁰ p/[#0]`. -/
noncomputable def succIndCodeT (p : Semiformula V ℒₒᵣ 1) : Formula V ℒₒᵣ :=
  (p.subst ![typedNumeral 0]) 🡒
    ((∀⁰ ((p.subst ![Semiterm.bvar 0]) 🡒
          (p.subst ![(Semiterm.bvar 0 : Semiterm V ℒₒᵣ 1) + typedNumeral 1]))) 🡒
      (∀⁰ (p.subst ![Semiterm.bvar 0])))

/-- **Quote-correctness of the internal `succInd` builder.** `succIndCodeT ⌜φ⌝ = ⌜succInd φ⌝` — the
internal builder applied to a quoted formula computes the quote of the external `succInd φ`. Proved by
unfolding both and discharging via the `typed_quote_*` coding simp set. -/
@[simp] lemma succIndCodeT_quote (φ : Semiformula ℒₒᵣ ℕ 1) :
    succIndCodeT (⌜φ⌝ : Semiformula V ℒₒᵣ 1) = ⌜succInd φ⌝ := by
  unfold succIndCodeT succInd
  simp [Matrix.constant_eq_singleton]

end SuccIndCode

/-- **`𝗣𝗔⁻` is Δ₁-definable** (axiom-clean). `𝗣𝗔⁻` is a finite theory (`PeanoMinus.finite`:
`𝗣𝗔⁻ = 𝗘𝗤 ∪ {17 axioms}`, all over the finite-symbol language `ℒₒᵣ`), so the finite-theory
combinator `Theory.Δ₁.ofFinite` enumerates it into a `𝚫₁.Semisentence 1`. -/
@[reducible] noncomputable def paMinusDelta1 : (𝗣𝗔⁻ : ArithmeticTheory).Δ₁ :=
  Theory.Δ₁.ofFinite 𝗣𝗔⁻ PeanoMinus.finite

/-- **The full induction scheme is Δ₁-definable** — the remaining obligation toward the axiom-free
headline (one disclosed `sorry`).

`InductionScheme ℒₒᵣ Set.univ = { ψ | ∃ φ : Semiformula ℒₒᵣ ℕ 1, ψ = univCl (succInd φ) }`
where `succInd φ = “φ(0) → (∀x, φ(x) → φ(x+1)) → ∀x φ(x)”` and `univCl` closes the free parameters.

**What `Theory.Δ₁` requires** (`ch : 𝚫₁.Semisentence 1`, `mem_iff`, `isDelta1 : ch.ProvablyProperOn 𝗜𝚺₁`):
a Δ₁ formula `ch(y)` with `ℕ ⊧ ch(⌜ψ⌝) ↔ ∃φ, ψ = univCl (succInd φ)`, provably Σ↔Π in `𝗜𝚺₁`.

**Construction plan** (all primitives exist in `Foundation/.../Bootstrapping/Syntax/`):
1. ✅ **DONE (lap 78): `succIndCodeT` + `succIndCodeT_quote`** above — the internal `succInd` builder,
   quote-correct (`succIndCodeT ⌜φ⌝ = ⌜succInd φ⌝`), axiom-clean.
2. Internal `univClClose q` = iterate `qqAll` over the free `^&i` of `q` (count = max fvar + 1) — a
   `𝚺₁` function; the closure makes the result a sentence. **THE remaining wall** (no internal `fvSup`/
   closure machinery in Foundation; needs a Σ₁-recursion over the formula + a bounded ∀-wrap loop).
3. `ch(y) := ∃ p < y, IsSemiformula 1 p ∧ y = univClClose (succIndCode p)` — bounded `∃` (the
   construction strictly grows the code), hence Δ₁ (Δ₀ over the Δ₁ pieces).
4. `mem_iff`: bridge `⌜univCl (succInd φ)⌝ = univClClose (succIndCode ⌜φ⌝)` via the
   quote/`substs`/`qqAll` coding lemmas (`typed_quote_substs`, the `qq*` quote computations).
5. `isDelta1`: `ProvablyProperOn.ofProperOn` + properness of the bounded `∃` over already-proper pieces.

This is a substantial but math-free arithmetization (Foundation's own `ISigma1_delta1Definable` is
likewise still an axiom). It is the precise, resumable next step on this front. -/
@[reducible] noncomputable def inductionSchemeUnivDelta1 : (InductionScheme ℒₒᵣ Set.univ).Δ₁ := sorry

/-- **`𝗣𝗔` is Δ₁-definable**, assembled from the finite base and the scheme. The defeq
`𝗣𝗔 = 𝗣𝗔⁻ + InductionScheme ℒₒᵣ Set.univ` makes `Theory.Δ₁.add` land directly. Once
`inductionSchemeUnivDelta1` is sorry-free, `Reduction.lean` rewires `peano_not_proves_consistency`
to `@consistent_unprovable 𝗣𝗔 paDelta1 _ _`, dropping `PA_delta1Definable` from the headline. -/
@[reducible] noncomputable def paDelta1 : (𝗣𝗔 : ArithmeticTheory).Δ₁ :=
  paMinusDelta1.add inductionSchemeUnivDelta1

end GoodsteinPA
