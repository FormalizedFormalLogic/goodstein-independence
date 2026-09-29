/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
/-
# Two general facts about coded semiterms

Salvaged from `GoodsteinPA/ToFoundation/FvSubst.lean`, whose free-variable substitution is now
AlphaCentauri's (`AlphaCentauri.Bootstrapping.Proof.FvSubst`).  These two lemmas mention no
substitution operation and AlphaCentauri carries neither, so they stay here.
-/
module

public import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Formula.Functions

@[expose] public section

open scoped FFL.FirstOrder.Bounding
namespace FFL.FirstOrder.Arithmetic.Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

variable {L : Language} [L.Encodable] [L.LORDefinable]

variable {t : V}

/-- A semiterm in bound-variable context `n` is also a semiterm in any wider context `m ≥ n`. -/
lemma IsSemiterm.weaken {n m u : V} (h : IsSemiterm L n u) (hnm : n ≤ m) : IsSemiterm L m u :=
  IsSemiterm.def.mpr ⟨(IsSemiterm.def.mp h).1, le_trans (IsSemiterm.def.mp h).2 hnm⟩

/-- A closed term is fixed by bound-variable shifting (`termBShift` raises bound variables, and a
closed term has none). -/
lemma termBShift_eq_self_of_closed (ht : IsSemiterm L 0 t) : termBShift L t = t := by
  apply IsSemiterm.induction 𝚺 ?_ ?_ ?_ ?_ t ht
  · definability
  · intro z hz; exact absurd hz (by simp)
  · intro x; simp
  · intro k f v hf hv ih
    rw [termBShift_func hf hv.isUTerm]
    simp only [qqFunc_inj, true_and]
    apply nth_ext' k (by rw [len_termBShiftVec hv.isUTerm]) (by simp [hv.lh])
    intro i hi
    rw [nth_termBShiftVec hv.isUTerm hi, ih i hi]

end FFL.FirstOrder.Arithmetic.Bootstrapping
