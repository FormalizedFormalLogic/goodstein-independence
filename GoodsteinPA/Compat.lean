/-
# `Compat.lean` — anti-corruption shim over Foundation's semantics API

goodstein's proof internals were written against an older `Foundation` spelling. Upstream
(`FormalizedFormalLogic/Foundation`) has since refactored that surface:

* `Structure` moved from an **explicit** argument to an **instance** argument in
  `Semiformula.Eval` / `Semiterm.val`;
* `Semiformula.Evalm` and the arity-specialised `eval_rel₀/₁/₂` (and `nrel`) `@[simp]` lemmas
  were **removed** (the general `eval_rel` / `eval_nrel` survive);
* the models-theory notation `V ⊧ₘ* T` (`ModelsTheory`) was replaced by `V↓[ℒₒᵣ] ⊧* T`
  (`ModelsSet`), which the fork proved `rfl`-equal.

Rather than chase those renames across ~200 call sites on every upstream bump, the proof
internals hang off OUR OWN stable names, defined here in terms of upstream's current API. Every
entry is a **definitional alias** (`abbrev` / `notation`) or a **proved** bridge lemma — never an
axiom or a restatement — so the shim adds nothing to the trusted base. `#print axioms` on the
summit still reports exactly `[propext, Classical.choice, Quot.sound]`, which *machine-verifies*
the shim is faithful.

The one thing we deliberately keep hanging off upstream **directly** is the statement itself
(`𝗣𝗔 ⊬ ↑goodsteinSentence` and its `⊨`-bridge, in `Statement.lean` / `Encoding.lean`):
that is the designated audit surface and must be Foundation's.

When upstream churns again, edit THIS file, not the call sites.
-/
module

public import Foundation.FirstOrder.Arithmetic.HFS

@[expose] public section

open LO LO.FirstOrder LO.FirstOrder.Arithmetic

/-- Fork models-theory notation `V ⊧ₘ* T` (was `ModelsTheory`), now `V↓[ℒₒᵣ] ⊧* T` (`ModelsSet`).
Global (no `open` needed) so a bare `import GoodsteinPA.Compat` restores the old spelling. -/
notation:45 V:46 " ⊧ₘ* " T:46 => (V↓[ℒₒᵣ]) ⊧* T

/-- Fork single-formula models notation `M ⊧ₘ σ` (`Models`), now spelled `M↓[ℒₒᵣ] ⊧ σ` upstream.
`Models` itself is unchanged — only the notation and the language coercion moved. -/
notation:45 M:46 " ⊧ₘ " σ:46 => (M↓[ℒₒᵣ]) ⊧ σ

namespace LO.FirstOrder

/- NB: upstream also removed `Schema L`, but instead of shimming it we retarget goodstein's
`Derivation2` args from `Schema` to `Theory` — upstream's `Derivation2` is now indexed by a
`Theory L` (its sequents are `Finset (Proposition L)`, and `Proposition L = Formula L ℕ`
definitionally). See the `: Theory` retarget in the embedding files. -/

/- Upstream removed the arity-specialised `Semiterm.val_operator₀/₁/₂` (+ `val_const`) simp lemmas
(the general `val_operator` survives); re-prove them in instance-`val` form. -/
namespace Semiterm
variable {L : Language} {ξ : Type*} {M : Type*} {n : ℕ} [Structure L M]
  {e : Fin n → M} {ε : ξ → M} {v : Fin 0 → Semiterm L ξ n} {t u : Semiterm L ξ n}

@[simp] lemma val_const (o : Const L) : Semiterm.val e ε o.const = o.val ![] := by
  simp [Operator.const, Semiterm.val_operator, Matrix.empty_eq]

@[simp] lemma val_operator₀ (o : Const L) : Semiterm.val e ε (o.operator v) = o.val ![] := by
  simp [Semiterm.val_operator, Matrix.empty_eq]

@[simp] lemma val_operator₁ (o : Operator L 1) :
    Semiterm.val e ε (o.operator ![t]) = o.val ![Semiterm.val e ε t] := by
  simp [Semiterm.val_operator, Matrix.fun_eq_vec_one]

@[simp] lemma val_operator₂ (o : Operator L 2) :
    Semiterm.val e ε (o.operator ![t, u]) = o.val ![Semiterm.val e ε t, Semiterm.val e ε u] := by
  simp [Semiterm.val_operator, Matrix.fun_eq_vec_two]

end Semiterm

end LO.FirstOrder

namespace GoodsteinPA.Compat

section Eval
variable {L : Language} {ξ : Type*} {M : Type*} {n : ℕ}

/-- Fork `Semiformula.Eval` — the `Structure` passed **explicitly** (upstream made it an instance). -/
abbrev gEval (s : Structure L M) (e : Fin n → M) (ε : ξ → M) : Semiformula L ξ n →ˡᶜ Prop :=
  letI := s; Semiformula.Eval e ε

/-- Fork `Semiterm.val` — the `Structure` passed **explicitly**. -/
abbrev gVal (s : Structure L M) (e : Fin n → M) (ε : ξ → M) : Semiterm L ξ n → M :=
  letI := s; Semiterm.val e ε

/-- Fork `Semiformula.Evalm` — evaluate in `M`'s registered structure, `M` named explicitly.
Upstream removed this. -/
abbrev gEvalm (M : Type*) [Structure L M] {n} (e : Fin n → M) (ε : ξ → M) :
    Semiformula L ξ n →ˡᶜ Prop := Semiformula.Eval e ε

/-- Fork `Semiterm.valm` — evaluate a term in `M`'s registered structure, `M` named explicitly.
Upstream removed this. -/
abbrev gValm (M : Type*) [Structure L M] {n} (e : Fin n → M) (ε : ξ → M) :
    Semiterm L ξ n → M := Semiterm.val e ε

end Eval

section RelLemmas
variable {L : Language} {ξ : Type*} {M : Type*} {n : ℕ}
  (s : Structure L M) (e : Fin n → M) (ε : ξ → M)

@[simp] lemma eval_rel₀ {r : L.Rel 0} : gEval s e ε (Semiformula.rel r ![]) ↔ s.rel r ![] := by
  simp [gEval, Semiformula.eval_rel, Matrix.empty_eq]

@[simp] lemma eval_rel₁ {r : L.Rel 1} (t : Semiterm L ξ n) :
    gEval s e ε (Semiformula.rel r ![t]) ↔ s.rel r ![gVal s e ε t] := by
  simp only [gEval, gVal, Semiformula.eval_rel]
  refine Iff.of_eq (congrArg (s.rel r) ?_)
  funext i; cases' i using Fin.cases with i <;> simp

@[simp] lemma eval_rel₂ {r : L.Rel 2} (t₁ t₂ : Semiterm L ξ n) :
    gEval s e ε (Semiformula.rel r ![t₁, t₂]) ↔ s.rel r ![gVal s e ε t₁, gVal s e ε t₂] := by
  simp only [gEval, gVal, Semiformula.eval_rel]
  refine Iff.of_eq (congrArg (s.rel r) ?_)
  funext i; cases' i using Fin.cases with i <;> simp

@[simp] lemma eval_nrel₀ {r : L.Rel 0} : gEval s e ε (Semiformula.nrel r ![]) ↔ ¬s.rel r ![] := by
  simp [gEval, Semiformula.eval_nrel, Matrix.empty_eq]

@[simp] lemma eval_nrel₁ {r : L.Rel 1} (t : Semiterm L ξ n) :
    gEval s e ε (Semiformula.nrel r ![t]) ↔ ¬s.rel r ![gVal s e ε t] := by
  simp only [gEval, gVal, Semiformula.eval_nrel]
  refine Iff.of_eq (congrArg (¬ s.rel r ·) ?_)
  funext i; cases' i using Fin.cases with i <;> simp

@[simp] lemma eval_nrel₂ {r : L.Rel 2} (t₁ t₂ : Semiterm L ξ n) :
    gEval s e ε (Semiformula.nrel r ![t₁, t₂]) ↔ ¬s.rel r ![gVal s e ε t₁, gVal s e ε t₂] := by
  simp only [gEval, gVal, Semiformula.eval_nrel]
  refine Iff.of_eq (congrArg (¬ s.rel r ·) ?_)
  funext i; cases' i using Fin.cases with i <;> simp

end RelLemmas

end GoodsteinPA.Compat
