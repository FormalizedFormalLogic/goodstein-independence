/-
# `nm` — the `ℒₒᵣ` numeral as a closed term

The shared numeral shorthand `nm n = (Semiterm.Operator.numeral ℒₒᵣ n).const`, used across the
`Z_∞` calculus and its operator refinements for numeral substitutions `φ/[nm n]`.
-/
module

public import GoodsteinPA.ToFoundation.Compat

@[expose] public section

namespace LO.FirstOrder

/-- The `n`-th numeral of `ℒₒᵣ` as a closed term, ready for substitution `φ/[nm n]`. -/
noncomputable abbrev ArithmeticTerm.nm (n : ℕ) : ArithmeticTerm ℕ := (Semiterm.Operator.numeral ℒₒᵣ n).const

end LO.FirstOrder
