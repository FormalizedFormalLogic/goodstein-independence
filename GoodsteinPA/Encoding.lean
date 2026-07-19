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
(`goodsteinSentence_faithful`, below); the universal-closure eval lemma is the mechanical half (S).

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
(`goodsteinSentence_faithful`, below), so faithfulness can never silently regress.
-/
module

public import Foundation.FirstOrder.Incompleteness.Second
public import Foundation.FirstOrder.Arithmetic.R0.Representation
public import GoodsteinPA.ToMathlib.Goodstein.Defs
public import GoodsteinPA.ToMathlib.Goodstein.Computability
public import GoodsteinPA.Internal

@[expose] public section

namespace GoodsteinPA

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open Goodstein

/-- **Source predicate.** "The Goodstein sequence seeded at `m` reaches `0`." This is the genuine
termination statement over the audited `goodsteinSeq` (`Defs.lean`); `∀ m, goodsteinTerminates m`
is Goodstein's theorem. The encoded sentence `goodsteinSentence` is its first-order image. -/
def goodsteinTerminates (m : ℕ) : Prop := ∃ N, goodsteinSeq m N = 0

/-- **The one residual of Phase 0.2.** `goodsteinTerminates` is r.e. (semi-decidable): for each
`m`, search `N` until `goodsteinSeq m N = 0`. The only non-trivial input is computability of the
Goodstein function, which bottoms out at `Computable bump` (well-founded recursion on `Nat.log`,
not auto-derived by mathlib). Bounded, compiler-checkable, faithfulness-risk-free. -/
theorem goodsteinTerminates_re : REPred goodsteinTerminates := by
  -- `(m, N) ↦ goodsteinSeq m N = 0` is a (primitive-recursive, hence) computable predicate …
  have hpred : PrimrecPred (fun mN : ℕ × ℕ => goodsteinSeq mN.1 mN.2 = 0) :=
    Primrec.eq.comp primrec_goodsteinSeq (Primrec.const 0)
  have hcomp : ComputablePred (fun mN : ℕ × ℕ => goodsteinSeq mN.1 mN.2 = 0) :=
    hpred.computablePred
  -- … hence r.e., and r.e. is closed under the existential projection over `N`.
  have hproj := REPred.projection (β := ℕ) hcomp.to_re
  exact hproj.of_eq (fun m => by simp [goodsteinTerminates])

/-- **The Goodstein sentence `γ` (transparent Σ₁/Π₂ form, lap 36).** The `ℒₒᵣ`-sentence "every
Goodstein sequence terminates", built from the repo's **own** `𝚺₁`-definable internal Goodstein run
`igoodstein` (`InternalGoodstein.lean`) via its defining formula `igoodsteinDef : 𝚺₁.Semisentence 3`
(`!igoodsteinDef 0 m N` says `igoodstein m N = 0`):

  `γ := ∀ m, ∃ N, igoodstein m N = 0`.

This **replaces** the earlier opaque `∀⁰ (codeOfREPred goodsteinTerminates)` form (Foundation's
`Classical.epsilon`-over-Kleene-normal-form r.e. blob). The refactor is **sanctioned** by the Phase-2+
caveat above and gated only on `goodsteinSentence_faithful` (below) keeping the **identical** RHS
`∀ m, ∃ N, goodsteinSeq m N = 0` (which it does, via `igoodstein_nat`) — so faithfulness cannot regress.
The win: inside any model `M ⊧ 𝗜𝚺₁`, `γ` is the *transparent* run, so the descent contradiction
(`DescentSemantic`) needs no opaque-code↔run bridge (the old "wall B"). -/
noncomputable def goodsteinSentence : Sentence ℒₒᵣ :=
  “∀ m, ∃ N, !igoodsteinDef 0 m N”

/-- **Faithfulness bridge.** The standard model `ℕ` satisfies the encoded sentence
`goodsteinSentence` iff every Goodstein sequence — the genuine hereditary-base process of
`ToMathlib.Goodstein.Defs` — reaches `0`. -/
theorem goodsteinSentence_faithful :
    (ℕ ⊧ₘ goodsteinSentence) ↔ ∀ m, ∃ N, goodsteinSeq m N = 0 := by
  unfold goodsteinSentence
  rw [models_iff]
  simp only [Nat.reduceAdd, Nat.succ_eq_add_one, Fin.isValue, Semiformula.eval_all,
    Semiformula.eval_ex, Semiformula.eval_substs, InternalPow.igoodstein_defined.iff,
    Matrix.cons_val_zero, Semiterm.val_operator₀, Structure.numeral_eq_numeral,
    ORingStructure.zero_eq_zero, Fin.succ_zero_eq_one, Matrix.cons_val_one, Semiterm.val_bvar,
    Fin.Fin1.eq_one, Matrix.cons_val_fin_one, Fin.succ_one_eq_two, Matrix.cons_app_two,
    Function.comp_def]
  simp only [InternalPow.igoodstein_nat, eq_comm]

end GoodsteinPA
