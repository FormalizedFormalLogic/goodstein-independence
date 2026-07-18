/-
# `src/GoodsteinPA/EpsilonOrder.lean` — the arithmetization seam (step F), definability half

Boundedness (`src/Boundedness.lean`) consumes two seam hypotheses about the order formula `prec`:
- `hprec : ∀ γ n, ⊨^γ ((hyp prec)/[nm n]) ↔ ∀ m, m ≺ n → |m|_≺ < γ` — the semantic spec of `prec`;
- `hprecXPos : XPos (∼ prec)` — `prec` mentions no `X`.

This file discharges BOTH seam hypotheses **from a single semantic-definability fact**: that `prec` is
the `lMap` of an `ℒₒᵣ`-formula `φ` that defines the order `lt` in the standard ℕ-model (the "definability
half" of F; see the lap-18 reflection in `PENDING_WORK.md`). `hprec` follows by unfolding `⊨^γ`
(`hprec_of_lMap_defined`); `hprecXPos` is automatic because the image of an `ℒₒᵣ` formula has no `X`-atom
(`xpos_lMap` ⟹ `hprecXPos_lMap`). The `Seam` structure bundles these with the one remaining obligation.

What this file does NOT do (the "order-type half", the real F girder, deferred): exhibit a *concrete* `lt`
with `ε₀ ≤ ‖lt‖` (= ε₀-completeness of CNF notations, which mathlib lacks; `Seam.ge`) and a concrete
defining `φ` (via Foundation's `codeOfREPred₂`). Those instantiate the `Seam` fields.
-/
import GoodsteinPA.Boundedness
import Mathlib.SetTheory.Ordinal.Veblen
import GoodsteinPA.Compat

namespace GoodsteinPA.EpsilonOrder

open scoped Ordinal

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
    GoodsteinPA.Compat.gEval (structLX S) e ε (Semiformula.lMap (Language.ORing.embedding LX) ψ)
      ↔ GoodsteinPA.Compat.gEvalm ℕ e ε ψ := by
  rw [Semiformula.eval_lMap, lMap_structLX]

/-! ## `hprecXPos` is automatic for an `lMap`'d `ℒₒᵣ` formula -/

/-- The `lMap` of any `ℒₒᵣ`-formula is `X`-positive: it contains no `X`-atom at all (the `ORing`
embedding sends every `ℒₒᵣ` relation to the `Sum.inl` side, so the only `XPos`-failing shape,
`nrel (Sum.inr X) _`, never appears). -/
theorem xpos_lMap {n} (χ : Semiformula ℒₒᵣ ℕ n) :
    XPos (Semiformula.lMap (Language.ORing.embedding LX) χ) := by
  induction χ using Semiformula.rec' with
  | hverum => trivial
  | hfalsum => trivial
  | hrel r v => trivial
  | hnrel r v =>
    show Sum.isLeft ((Language.ORing.embedding LX).rel r) = true
    cases r <;> rfl
  | hand φ ψ ihφ ihψ => exact ⟨ihφ, ihψ⟩
  | hor φ ψ ihφ ihψ => exact ⟨ihφ, ihψ⟩
  | hall φ ih => exact ih
  | hexs φ ih => exact ih

/-- **`hprecXPos` for an `lMap`-definable order is automatic.** For `prec := φ.lMap`, the Boundedness
hypothesis `XPos (∼ prec)` holds (negation of an `X`-free formula is still `X`-free). -/
theorem hprecXPos_lMap {n} (φ : Semiformula ℒₒᵣ ℕ n) :
    XPos (∼ (Semiformula.lMap (Language.ORing.embedding LX) φ)) := by
  simpa only [LogicalConnective.HomClass.map_neg] using xpos_lMap (∼ φ)

/-! ## The `hprec` seam hypothesis from semantic definability -/

section Definability

variable (lt : ℕ → ℕ → Prop) [IsWellFounded ℕ lt]
variable (prec : Semiformula LX ℕ 2)

/-- **`hprec` from the eval of `prec`.** If `prec`, evaluated in `structLX S` at `![a,b]`, reads as
`lt a b` (uniformly in the `X`-set `S` — i.e. `prec` is `X`-free), then the Boundedness seam hypothesis
`hprec` holds. Pure unfolding of `⊨^γ` through `∀`, `→`, and the `X`-atom on the bound variable. -/
theorem hprec_of_eval
    (hdef : ∀ (S : ℕ → Prop) (a b : ℕ),
      GoodsteinPA.Compat.gEval (structLX S) ![a, b] id prec ↔ lt a b)
    (γ : Ordinal.{0}) (n : ℕ) :
    models lt γ ((hyp prec)/[nm n]) ↔ ∀ m : ℕ, lt m n → rk lt m < γ := by
  unfold models hyp
  rw [Semiformula.eval_substs, Semiformula.eval_all]
  apply forall_congr'
  intro m
  -- The assignment `m :> (the substituted vector)` equals `![m, n]`.
  have hvec : (m :> fun i : Fin 1 =>
      GoodsteinPA.Compat.gVal (structLX (levelSet lt γ)) ![] id (![nm n] i)) = ![m, n] := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · refine Fin.cases ?_ (fun k => k.elim0) j
      simp [val_nm_structLX]
  -- upstream's `eval_substs` now emits the assignment in `∘`-composition normal form
  -- (`Semiterm.val ![] id ∘ ![nm n]`); expand it back to the `fun i => …` shape `hvec` matches.
  simp only [Function.comp_def]
  rw [hvec]
  simp only [LogicalConnective.HomClass.map_imply, LogicalConnective.Prop.arrow_eq,
    Xat, GoodsteinPA.Compat.eval_rel₁, Semiterm.val_bvar, Matrix.cons_val_zero, structLX_rel_Xsym]
  rw [hdef (levelSet lt γ) m n]
  rfl

/-- **`hprec` from an `lMap`-definable order.** If the `ℒₒᵣ`-formula `φ` defines `lt` in the standard
model, then `prec := φ.lMap` discharges the Boundedness seam hypothesis `hprec`. -/
theorem hprec_of_lMap_defined (φ : Semiformula ℒₒᵣ ℕ 2)
    (hφ : ∀ a b : ℕ, GoodsteinPA.Compat.gEvalm ℕ ![a, b] id φ ↔ lt a b)
    (γ : Ordinal.{0}) (n : ℕ) :
    models lt γ ((hyp (Semiformula.lMap (Language.ORing.embedding LX) φ))/[nm n])
      ↔ ∀ m : ℕ, lt m n → rk lt m < γ :=
  hprec_of_eval lt _ (fun S a b => by rw [eval_lMap_structLX]; exact hφ a b) γ n

end Definability

/-! ## The seam interface

`Seam` bundles what F must supply to the headline assembly: a well-order `lt` of ℕ, an `X`-free
`ℒₒᵣ`-formula `φ` defining it, and the order-type lower bound `ε₀ ≤ ‖lt‖`. The two *definability*
obligations are discharged here (`hprec`/`hprecXPos`, via the lemmas above); the lone remaining
obligation is `ge` — the ε₀-completeness girder (mathlib-only; see `PENDING_WORK.md`). The seam needs
only `ε₀ ≤ orderType lt` (NOT `=`): the contradiction is `‖lt‖ ≤ 2^β`, `β < ε₀`. -/
structure Seam where
  /-- the order relation on ℕ -/
  lt : ℕ → ℕ → Prop
  /-- it is a well-order (instance-implicit so `orderType`/`rk` resolve below) -/
  [wf : IsWellFounded ℕ lt]
  /-- an `X`-free `ℒₒᵣ`-formula defining `lt` in the standard ℕ-model -/
  φ : Semiformula ℒₒᵣ ℕ 2
  /-- `φ` defines `lt` -/
  hφ : ∀ a b : ℕ, GoodsteinPA.Compat.gEvalm ℕ ![a, b] id φ ↔ lt a b
  /-- the order type is at least ε₀ (the only obligation not yet discharged by this file) -/
  ge : ε₀ ≤ orderType lt

namespace Seam

attribute [instance] Seam.wf

variable (E : Seam)

/-- The `LX`-formula realising the order (the `lMap` of `E.φ`). -/
def prec : Semiformula LX ℕ 2 := Semiformula.lMap (Language.ORing.embedding LX) E.φ

/-- The Boundedness seam hypothesis `hprec`, discharged from definability. -/
theorem hprec (γ : Ordinal.{0}) (n : ℕ) :
    models E.lt γ ((hyp E.prec)/[nm n]) ↔ ∀ m : ℕ, E.lt m n → rk E.lt m < γ :=
  hprec_of_lMap_defined E.lt E.φ E.hφ γ n

/-- The Boundedness seam hypothesis `hprecXPos`, automatic for the `X`-free `prec`. -/
theorem hprecXPos : XPos (∼ E.prec) := hprecXPos_lMap E.φ

end Seam

end GoodsteinPA.EpsilonOrder
