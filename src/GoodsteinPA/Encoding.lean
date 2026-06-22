/-
# Encoding "Goodstein terminates" as a first-order arithmetic sentence

This is the **Goodstein-independence expedition** (Kirby–Paris 1982): Peano Arithmetic does
not prove that every Goodstein sequence terminates. We build on **Foundation**
(`FormalizedFormalLogic`), which supplies first-order logic, PA (`𝗣𝗔 = Peano : ArithmeticTheory`
over `ℒₒᵣ`), Σ₁ arithmetization, and Gödel II.

## The encoding route (Phase 0.2)
`γ` := the first-order `ℒₒᵣ`-sentence expressing **"∀ m, the Goodstein sequence started at m
reaches 0"**. We do *not* hand-build the arithmetic formula for the (heavily recursive)
Goodstein step. Foundation already did the hard representability work:

* `LO.FirstOrder.Arithmetic.codeOfREPred (A : ℕ → Prop) : Semisentence ℒₒᵣ 1` turns any
  **r.e. predicate** `A` on ℕ into a Σ₁ semisentence with one free variable, and
* `codeOfREPred_spec (hp : REPred A) : ℕ ⊧/![x] (codeOfREPred A) ↔ A x` certifies that the
  formula is true in the standard model at `x` **iff** `A x`.

So with the source predicate `goodsteinTerminates m := ∃ N, goodsteinSeq m N = 0` (the genuine
hereditary-base process of `Defs.lean`), the faithful sentence is just its universal closure:

  `γ := ∀⁰ (codeOfREPred goodsteinTerminates)`.

`codeOfREPred_spec` *is* the encoding-correctness half (E) of the faithfulness bridge
(`Bridge.lean`); the universal-closure eval lemma is the mechanical half (S).

## The one residual obligation
`codeOfREPred` needs `goodsteinTerminates` to be **r.e.** (`REPred`). That predicate is
`∃ N, (decidable)`, so it is r.e. *provided* the Goodstein function is computable — which
bottoms out at `Computable bump`. `bump` is defined by well-founded recursion (on `Nat.log`),
so mathlib does not derive its `Computable` witness automatically; supplying it is the bounded,
compiler-checkable, smuggling-free residual (`goodsteinTerminates_re`, below). It carries no
faithfulness risk: a computability proof either typechecks or it doesn't.

## Faithfulness note (Phase 2+ caveat)
A `codeOfREPred`-built `γ` is faithful and citable (the Phase 0 deliverable), but it is an
*opaque* representability blob. The later reduction `γ ⟹ Con(𝗣𝗔)` (Phase 2–4) may want a more
transparent, hand-built Π₂ form; if so, that refactor is gated by *matching this bridge's spec*
(`Bridge.lean`), so faithfulness can never silently regress.
-/
import Foundation.FirstOrder.Incompleteness.Second
import Foundation.FirstOrder.Arithmetic.R0.Representation
import GoodsteinPA.Defs

namespace GoodsteinPA

open LO LO.FirstOrder LO.FirstOrder.Arithmetic

/-- **Source predicate.** "The Goodstein sequence seeded at `m` reaches `0`." This is the genuine
termination statement over the audited `goodsteinSeq` (`Defs.lean`); `∀ m, goodsteinTerminates m`
is Goodstein's theorem. The encoded sentence `goodsteinSentence` is its first-order image. -/
def goodsteinTerminates (m : ℕ) : Prop := ∃ N, goodsteinSeq m N = 0

/-- **The one residual of Phase 0.2.** `goodsteinTerminates` is r.e. (semi-decidable): for each
`m`, search `N` until `goodsteinSeq m N = 0`. The only non-trivial input is computability of the
Goodstein function, which bottoms out at `Computable bump` (well-founded recursion on `Nat.log`,
not auto-derived by mathlib). Bounded, compiler-checkable, faithfulness-risk-free. -/
theorem goodsteinTerminates_re : REPred goodsteinTerminates := by
  sorry

/-- **The Goodstein sentence `γ`.** The `ℒₒᵣ`-sentence "every Goodstein sequence terminates",
obtained as the universal closure of Foundation's r.e.-predicate code for `goodsteinTerminates`.
Faithfulness (`ℕ ⊧ₘ goodsteinSentence ↔ ∀ m, ∃ N, goodsteinSeq m N = 0`) is `Bridge.lean`. -/
noncomputable def goodsteinSentence : Sentence ℒₒᵣ :=
  ∀⁰ (codeOfREPred goodsteinTerminates)

end GoodsteinPA
