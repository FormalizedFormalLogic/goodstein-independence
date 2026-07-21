/-
# `Rew.subst` composition and value-congruence lemmas

General facts about `Rew.subst`/`Rew.comp` composition and standard-value congruence under
substitution, depending only on Foundation's own API (`Rew`/`Semiterm`/`Semiformula`/the
`Compat` shim) — no `Z_∞`-specific machinery (`Provable`/`Derivation`).
-/
module

public import GoodsteinPA.ToFoundation.Numeral

@[expose] public section

namespace LO.FirstOrder

open ArithmeticTerm

variable {n : ℕ}

/-- The closing substitution: free variable `&x ↦ nm (e x)`. Sends every `ArithmeticFormula ℕ` to a
closed formula (sentence image). -/
noncomputable def asg (e : ℕ → ℕ) : Rew ℒₒᵣ ℕ 0 ℕ 0 := Rew.rewrite (fun x => nm (e x))

/-- Re-indexing the assignment along `Rew.shift`: closing by `asg e` after shifting the free
variable is the same as closing directly by `e` composed with `Nat.succ`. -/
lemma asg_comp_shift (e : ℕ → ℕ) : (asg e).comp Rew.shift = asg (e ∘ Nat.succ) := by
  ext x
  · exact Fin.elim0 x
  · simp [asg, Rew.comp_app]

/-- `Finset.image` form of `asg_comp_shift`: shifting every formula in `Γ` and then closing by
`asg e` is the same as closing `Γ` directly by `e ∘ Nat.succ`. -/
lemma asg_image_shift (e : ℕ → ℕ) (Γ : Finset (ArithmeticFormula ℕ)) :
    (Γ.image Rewriting.shift).image (fun ψ => asg e ▹ ψ) = Γ.image (fun ψ => asg (e ∘ Nat.succ) ▹ ψ) := by
  rw [Finset.image_image]
  refine Finset.image_congr ?_
  intro ψ _
  show asg e ▹ (Rew.shift ▹ ψ) = asg (e ∘ Nat.succ) ▹ ψ
  rw [← TransitiveRewriting.comp_app, asg_comp_shift]

/-- Freeing the bound variable and closing by `asg (n :>ₙ e)` (which sends `&0` to `nm n`) is the
same as closing the freed variable's slot by `asg e` and then substituting `nm n`. -/
lemma asg_cons_free (n : ℕ) (e : ℕ → ℕ) (φ : ArithmeticSemiformula ℕ 1) :
    asg (n :>ₙ e) ▹ (Rew.free ▹ φ) = ((asg e).q ▹ φ)/[nm n] := by
  have hRew : (asg (n :>ₙ e)).comp Rew.free = (Rew.subst ![nm n]).comp (asg e).q := by
    ext x
    · refine Fin.cases ?_ (fun i => Fin.elim0 i) x
      simp [asg, Rew.comp_app]
    · simp [asg, Rew.comp_app]
  show asg (n :>ₙ e) ▹ (Rew.free ▹ φ) = Rew.subst ![nm n] ▹ ((asg e).q ▹ φ)
  rw [← TransitiveRewriting.comp_app, ← TransitiveRewriting.comp_app, hRew]

/-- **General substitution–rewriting commutation**: `ω ▹ (φ/[t]) = (ω.q ▹ φ)/[ω t]`. -/
lemma rew_subst_term (ω : Rew ℒₒᵣ ℕ 0 ℕ 0) (φ : ArithmeticSemiformula ℕ 1) (t : ArithmeticTerm ℕ)
  : ω ▹ (φ/[t]) = (ω.q ▹ φ)/[ω t] := by
  show ω ▹ (Rew.subst ![t] ▹ φ) = Rew.subst ![ω t] ▹ (ω.q ▹ φ)
  have heq : ω.comp (Rew.subst ![t]) = (Rew.subst ![ω t]).comp ω.q := by
    ext x
    · cases x using Fin.cases with
      | zero => simp [Rew.comp_app]
      | succ i => exact Fin.elim0 i
    · simp [Rew.comp_app]
  rw [← TransitiveRewriting.comp_app, ← TransitiveRewriting.comp_app, heq]

/-- Substitution-composition: substituting the freed (q) variable by `nm m` after a renaming
`Rew.subst w` is the same as substituting by the extended vector `nm m :> w`. -/
lemma subst_q_cons (w : Fin n → ArithmeticTerm ℕ) (m : ℕ) :
  (Rew.subst ![nm m]).comp (Rew.subst w).q = Rew.subst (nm m :> w) := by
  ext x
  · cases x using Fin.cases with
    | zero => simp [Rew.comp_app]
    | succ i => simp [Rew.comp_app]
  · simp [Rew.comp_app]

/-- (ArithmeticFormula ℕ) form: `((Rew.subst w).q ▹ ψ)/[nm m] = Rew.subst (nm m :> w) ▹ ψ`. -/
lemma subst_q_cons_app (w : Fin n → ArithmeticTerm ℕ) (m : ℕ)
    (ψ : ArithmeticSemiformula ℕ (n + 1)) :
    ((Rew.subst w).q ▹ ψ)/[nm m] = Rew.subst (nm m :> w) ▹ ψ := by
  show Rew.subst ![nm m] ▹ ((Rew.subst w).q ▹ ψ) = Rew.subst (nm m :> w) ▹ ψ
  rw [← TransitiveRewriting.comp_app, subst_q_cons]

/-- Value of a renamed term depends only on the values of the substituted terms. -/
lemma valm_subst_congr (w w' : Fin n → ArithmeticTerm ℕ)
    (hval : ∀ i, Semiterm.gValm ℕ ![] id (w i)
                = Semiterm.gValm ℕ ![] id (w' i))
    (t : ArithmeticSemiterm ℕ n) :
    Semiterm.gValm ℕ ![] id (Rew.subst w t)
      = Semiterm.gValm ℕ ![] id (Rew.subst w' t) := by
  simp only [Semiterm.gValm, Semiterm.val_substs]
  congr 1
  funext x; exact hval x

end LO.FirstOrder
