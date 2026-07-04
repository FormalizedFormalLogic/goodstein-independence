/-
# `wip/LangX.lean` — the language `ℒₒᵣ + X` for the Buchholz Boundedness route (lap-12 pivot)

VERIFY-(a), concretely: define the extended language `ℒₒᵣ` + one unary "set variable" predicate `X`
(Buchholz §5's `L₀(X)`), give it the `ORing` instance (so the full arithmetic API transfers), and confirm
numerals + an `X`-atom formula typecheck. This is the first lego of the pivot (`ANALYSIS-2026-06-22-lap12-
buchholz-pivot.md`): the whole chain (PA, embedding M4, cut-elim M5, Boundedness) lives over this language.
-/
import Foundation.FirstOrder.Arithmetic.Basic.Model
import Foundation.FirstOrder.Basic.Operator
import GoodsteinPA.Compat

namespace GoodsteinPA.LangX

open LO LO.FirstOrder

/-- The one-unary-relation language carrying Buchholz's set variable `X`. -/
inductive XRel : ℕ → Type
  | X : XRel 1

/-- The language `{X}` (one unary predicate, no functions). -/
def Xpred : Language where
  Func := fun _ => Empty
  Rel := XRel

/-- The extended language `ℒₒᵣ + X` of Buchholz §5. -/
abbrev LX : Language := Language.add ℒₒᵣ Xpred

/-- `ℒₒᵣ`'s ring/order symbols transfer to `LX` via the left injection, giving `LX` its `ORing`
structure — so the whole `Foundation` arithmetic API (numerals, `Structure ℕ`, …) is available. -/
instance : Language.ORing LX where
  eq := Sum.inl (Language.Eq.eq)
  lt := Sum.inl (Language.LT.lt)
  zero := Sum.inl (Language.Zero.zero)
  one := Sum.inl (Language.One.one)
  add := Sum.inl (Language.Add.add)
  mul := Sum.inl (Language.Mul.mul)

/-- The set-variable predicate symbol `X` as a relation of `LX`. -/
def Xsym : LX.Rel 1 := Sum.inr XRel.X

/-- `X t` as an `LX`-formula (for a term `t`). -/
def Xatom {ξ n} (t : Semiterm LX ξ n) : Semiformula LX ξ n :=
  Semiformula.rel Xsym ![t]

-- Probes: numerals exist over `LX`, and an `X`-atom on the numeral `3` typechecks.
noncomputable example : Semiterm.Const LX := Semiterm.Operator.numeral LX 3
noncomputable example : Semiformula LX ℕ 0 := Xatom ((Semiterm.Operator.numeral LX 3).const)

/-- The `ORing` embedding `ℒₒᵣ →ᵥ LX` (Foundation's `Language.ORing.embedding`), the hook for
re-instantiating M4/M5 (currently hardwired to `ℒₒᵣ`) over `LX`. -/
noncomputable example : ℒₒᵣ →ᵥ LX := Language.ORing.embedding LX

/-! ## The ℕ-model of `LX` parametrised by a set `S ⊆ ℕ` (lap-13 task (i))

The single most-leveraged lego of the Buchholz Boundedness route: the only member of the M5/M4
instance bundle (`GenericZinftyProbe.lean`) missing for `LX` was `Structure LX ℕ`. We build it here,
parametrised by the interpretation `S : ℕ → Prop` of the set variable `X`. It *doubles* as the carrier
of Buchholz's truth semantics `⊨^α` (there `S := {n | |n|_≺ < α}`, the ≺-initial segment of norm `< α`).
Also: the two `DecidableEq` instances (`LX.Func k`, `LX.Rel k`) completing the bundle for `Finset`
sequents. -/

/-- `LX`'s function symbols at each arity are exactly `ℒₒᵣ`'s (the `Xpred` side has none). -/
instance instDecidableEqLXFunc (k : ℕ) : DecidableEq (LX.Func k) :=
  inferInstanceAs (DecidableEq (Language.Func ℒₒᵣ k ⊕ Empty))

/-- `XRel` is a one-constructor inductive, so `DecidableEq` is derivable. -/
instance instDecidableEqXRel (k : ℕ) : DecidableEq (XRel k) := fun a b => by
  cases a; cases b; exact isTrue rfl

instance instDecidableEqLXRel (k : ℕ) : DecidableEq (LX.Rel k) :=
  inferInstanceAs (DecidableEq (Language.Rel ℒₒᵣ k ⊕ XRel k))

/-- The standard ℕ-model of `ℒₒᵣ`, obtained from its registered `Structure ℒₒᵣ ℕ` instance. -/
@[reducible]
private def lorN : Structure ℒₒᵣ ℕ := inferInstance

/-- **The ℕ-model of `LX` with the set variable `X` interpreted as `S`.** The `ℒₒᵣ` fragment is the
standard arithmetic model; `X t` is true iff `S (val t)`. This is the `⊨^α` carrier. -/
@[reducible]
noncomputable def structLX (S : ℕ → Prop) : Structure LX ℕ where
  func := fun _ f =>
    Sum.elim (fun f₀ => lorN.func f₀) (fun e => e.elim) f
  rel := fun _ r =>
    Sum.elim (fun r₀ => lorN.rel r₀)
      (fun rx => match rx with | XRel.X => fun v => S (v 0)) r

/-- The `ℒₒᵣ`-fragment of `structLX S` agrees with the standard model on ring/order symbols. -/
@[simp] lemma structLX_func_inl (S : ℕ → Prop) {k} (f : Language.Func ℒₒᵣ k) (v : Fin k → ℕ) :
    (structLX S).func (Sum.inl f) v = lorN.func f v := rfl

@[simp] lemma structLX_rel_inl (S : ℕ → Prop) {k} (r : Language.Rel ℒₒᵣ k) (v : Fin k → ℕ) :
    (structLX S).rel (Sum.inl r) v = lorN.rel r v := rfl

/-- The defining equation of the `X`-atom: `X t` holds in `structLX S` iff `S` holds of the argument. -/
@[simp] lemma structLX_rel_X (S : ℕ → Prop) (v : Fin 1 → ℕ) :
    (structLX S).rel (Sum.inr XRel.X) v ↔ S (v 0) := Iff.rfl

@[simp] lemma structLX_rel_Xsym (S : ℕ → Prop) (v : Fin 1 → ℕ) :
    (structLX S).rel Xsym v ↔ S (v 0) := Iff.rfl

/-- **The carrier behaves as Buchholz's `⊨^S`.** Evaluating the `X`-atom `X t` in `structLX S` yields
`S` of the value of `t` — i.e. `X` reads as the set `S`. This is the defining property that makes
`structLX S` the `⊨^α` carrier (take `S := {n | |n|_≺ < α}`). -/
theorem eval_Xatom (S : ℕ → Prop) {ξ} (e : Fin 0 → ℕ) (ε : ξ → ℕ) (t : Semiterm LX ξ 0) :
    GoodsteinPA.Compat.gEval (structLX S) e ε (Xatom t)
      ↔ S (GoodsteinPA.Compat.gVal (structLX S) e ε t) := by
  simp only [Xatom, GoodsteinPA.Compat.eval_rel₁]
  rfl

end GoodsteinPA.LangX
