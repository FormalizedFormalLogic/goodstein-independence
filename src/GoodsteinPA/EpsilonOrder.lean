/-
# `src/GoodsteinPA/EpsilonOrder.lean` — the arithmetization seam (step F), definability half

Boundedness (`src/Boundedness.lean`) consumes two seam hypotheses about the order formula `prec`:
- `hprec : ∀ γ n, ⊨^γ ((hyp prec)/[nm n]) ↔ ∀ m, m ≺ n → |m|_≺ < γ` — the semantic spec of `prec`;
- `hprecXPos : XPos (∼ prec)` — `prec` mentions no `X`.

This file discharges `hprec` **from a single semantic-definability fact**: that `prec` is the `lMap` of
an `ℒₒᵣ`-formula `φ` that defines the order `lt` in the standard ℕ-model. That is the "definability half"
of F (per the lap-18 reflection in `PENDING_WORK.md`). Because `prec` is the image of an `ℒₒᵣ` formula it
is `X`-free, so `hprecXPos` will be automatic (the `xpos_lMap` lemma — TODO, mechanical).

What this file does NOT do (the "order-type half", the real F girder, deferred): exhibit a *concrete* `lt`
with `ε₀ ≤ ‖lt‖` (= ε₀-completeness of CNF notations, which mathlib lacks) and a concrete defining `φ`
(via Foundation's `codeOfREPred₂`). Those instantiate the hypotheses below.
-/
import GoodsteinPA.Boundedness

namespace GoodsteinPA.EpsilonOrder

open LO LO.FirstOrder
open GoodsteinPA.ZinftyGen GoodsteinPA.LangX GoodsteinPA.TruthSem GoodsteinPA.XPositive
open GoodsteinPA.Boundedness

/-! ## X-free invariance at arbitrary assignments (generalises `TruthSem.models_lMap`) -/

/-- **Generalised X-free invariance.** An `ℒₒᵣ`-formula lifted to `LX` evaluates in `structLX S`
exactly as in the standard ℕ-model — at *any* assignment `e, ε` (the lap-13 `models_lMap` was the
closed `e = ![], ε = id` case). The `X`-set `S` is irrelevant because the `ℒₒᵣ`-reduct of `structLX S`
is the standard model (`lMap_structLX`). -/
theorem eval_lMap_structLX (S : ℕ → Prop) {n} (e : Fin n → ℕ) (ε : ℕ → ℕ)
    (ψ : Semiformula ℒₒᵣ ℕ n) :
    Semiformula.Eval (structLX S) e ε (Semiformula.lMap (Language.ORing.embedding LX) ψ)
      ↔ Semiformula.Evalm ℕ e ε ψ := by
  rw [Semiformula.eval_lMap, lMap_structLX]

/-! ## The `hprec` seam hypothesis from semantic definability -/

variable (lt : ℕ → ℕ → Prop) [IsWellFounded ℕ lt]
variable (prec : Semiformula LX ℕ 2)

/-- **`hprec` from the eval of `prec`.** If `prec`, evaluated in `structLX S` at `![a,b]`, reads as
`lt a b` (uniformly in the `X`-set `S` — i.e. `prec` is `X`-free), then the Boundedness seam hypothesis
`hprec` holds. Pure unfolding of `⊨^γ` through `∀`, `→`, and the `X`-atom on the bound variable. -/
theorem hprec_of_eval
    (hdef : ∀ (S : ℕ → Prop) (a b : ℕ),
      Semiformula.Eval (structLX S) ![a, b] id prec ↔ lt a b)
    (γ : Ordinal.{0}) (n : ℕ) :
    models lt γ ((hyp prec)/[nm n]) ↔ ∀ m : ℕ, lt m n → rk lt m < γ := by
  unfold models hyp
  rw [Semiformula.eval_substs, Semiformula.eval_all]
  apply forall_congr'
  intro m
  -- The assignment `m :> (the substituted vector)` equals `![m, n]`.
  have hvec : (m :> fun i : Fin 1 =>
      Semiterm.val (structLX (levelSet lt γ)) ![] id (![nm n] i)) = ![m, n] := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · refine Fin.cases ?_ (fun k => k.elim0) j
      simp [val_nm_structLX]
  rw [hvec]
  simp only [LogicalConnective.HomClass.map_imply, LogicalConnective.Prop.arrow_eq,
    Xat, Semiformula.eval_rel₁, Semiterm.val_bvar, Matrix.cons_val_zero, structLX_rel_Xsym]
  rw [hdef (levelSet lt γ) m n]
  rfl

/-- **`hprec` from an `lMap`-definable order.** If the `ℒₒᵣ`-formula `φ` defines `lt` in the standard
model, then `prec := φ.lMap` discharges the Boundedness seam hypothesis `hprec`. -/
theorem hprec_of_lMap_defined (φ : Semiformula ℒₒᵣ ℕ 2)
    (hφ : ∀ a b : ℕ, Semiformula.Evalm ℕ ![a, b] id φ ↔ lt a b)
    (γ : Ordinal.{0}) (n : ℕ) :
    models lt γ ((hyp (Semiformula.lMap (Language.ORing.embedding LX) φ))/[nm n])
      ↔ ∀ m : ℕ, lt m n → rk lt m < γ :=
  hprec_of_eval lt _ (fun S a b => by rw [eval_lMap_structLX]; exact hφ a b) γ n

end GoodsteinPA.EpsilonOrder
