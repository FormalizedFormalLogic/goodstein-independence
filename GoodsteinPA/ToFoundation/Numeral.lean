/-
# `nm` — the `ℒₒᵣ` numeral as a closed term

The shared numeral shorthand `nm n = (Semiterm.Operator.numeral ℒₒᵣ n).const`, used across the
`Z_∞` calculus and its operator refinements for numeral substitutions `φ/[nm n]`.
-/
module

public import Foundation.FirstOrder.Arithmetic.HFS

@[expose] public section

namespace FFL.FirstOrder

namespace ArithmeticTerm

/-- The `n`-th numeral of `ℒₒᵣ` as a closed term, ready for substitution `φ/[nm n]`. -/
noncomputable abbrev nm (n : ℕ) : ArithmeticTerm ℕ := (Semiterm.Operator.numeral ℒₒᵣ n).const

/-- The numeral `nm m` evaluates to `m` in the standard ℕ-model (any free assignment). -/
@[simp, grind .]
lemma valm_nm (m : ℕ) (f : ℕ → ℕ) : Semiterm.val (M := ℕ) ![] f (nm m) = m := by simp [nm]

end ArithmeticTerm

end FFL.FirstOrder
