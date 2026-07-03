import GoodsteinPA.OperatorZef2

/-! Probe for the `gated_of_sigma1` root discharge: guard shape + gate eval. -/

namespace GoodsteinPA.GateRootProbe

open LO LO.FirstOrder
open GoodsteinPA.OperatorZeh GoodsteinPA.OperatorZinfty

-- Probe 1: what does the ball guard unfold to?
example (t : Semiterm ℒₒᵣ ℕ 1) :
    (“x. x < !!t” : SyntacticSemiformula ℒₒᵣ 1)
      = Semiformula.rel Language.LT.lt ![#0, t] := by
  simp [Semiformula.Operator.lt_def]

-- Probe 2: imp unfold
example (g φ : SyntacticSemiformula ℒₒᵣ 1) : (g 🡒 φ) = (∼g ⋎ φ) := Semiformula.imp_eq g φ

-- Probe 3: neg of rel is nrel
example (t : Semiterm ℒₒᵣ ℕ 1) :
    (∼(Semiformula.rel (L := ℒₒᵣ) (ξ := ℕ) Language.LT.lt ![#0, t]))
      = Semiformula.nrel Language.LT.lt ![#0, t] := by simp

-- Probe 4: gate eval — a false ball instance pins k below the guard value
example (t : Semiterm ℒₒᵣ ℕ 1) (φ : SyntacticSemiformula ℒₒᵣ 1) (k : ℕ)
    (h : ¬ atomTrue (((“x. x < !!t” : SyntacticSemiformula ℒₒᵣ 1) 🡒 φ)/[nm k])) :
    k < Semiterm.valm ℕ ![k] (fun _ => 0) t ∧ ¬ atomTrue (φ/[nm k]) := by
  simp [atomTrue, Semiformula.imp_eq, Semiformula.Operator.lt_def, valm_nm,
    Matrix.constant_eq_singleton, Semiformula.eval_rel, Semiformula.eval_nrel] at h
  refine ⟨?_, by
    simpa [atomTrue, Semiformula.eval_substs, valm_nm, Matrix.constant_eq_singleton]
      using h.2⟩
  have he : (fun _ => (0:ℕ) : Fin 0 → ℕ) = ![] := by funext i; exact i.elim0
  have h1 : Semiterm.val (Arithmetic.standardModel ℕ) (fun _ => 0) (fun _ => 0)
      ((Rew.subst ![nm k]) t) = Semiterm.valm ℕ ![k] (fun _ => 0) t := by
    rw [Semiterm.val_rew]
    congr 1
    funext i
    rcases Fin.eq_zero i with rfl
    show Semiterm.val (Arithmetic.standardModel ℕ) (fun _ => 0) (fun _ => 0)
      ((Rew.subst ![nm k]) #0) = k
    rw [show (Rew.subst (L := ℒₒᵣ) (ξ := ℕ) ![nm k]) #0 = nm k by simp, he]
    exact valm_nm k _
  rw [h1] at h
  exact h.1

end GoodsteinPA.GateRootProbe
