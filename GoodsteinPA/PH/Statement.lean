/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/

module

public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Nat.Pairing

@[expose] public section

/-!
# The Paris–Harrington principle

`PH e r k N`: every `r`-colouring of the `e`-element subsets of `{1, …, N}` has a homogeneous
`H ⊆ {1, …, N}` with `|H| ≥ k` that is *relatively large*, `|H| ≥ min H`
(Paris–Harrington 1977, in the `S = {1, 2, …, N}` form).  `PHx x N` packs the parameters as
`x = ⟪e, ⟪r, k⟫⟫`.
-/

set_option linter.dupNamespace false

namespace GoodsteinPA.PH

open Finset

/-- **Relatively large**: the least element is at most the cardinality. -/
def RelLarge (H : Finset ℕ) : Prop := ∀ a ∈ H, (∀ b ∈ H, a ≤ b) → a ≤ H.card

/-- `H` is homogeneous for `c` on `e`-subsets: all `e`-subsets of `H` get one colour. -/
def Homog {N e r : ℕ} (c : (Icc 1 N).powersetCard e → Fin r) (H : Finset ℕ) : Prop :=
  ∃ i : Fin r, ∀ (s : Finset ℕ) (hs : s ∈ (Icc 1 N).powersetCard e), s ⊆ H → c ⟨s, hs⟩ = i

/-- **The Paris–Harrington property at `N`.** -/
def PH (e r k N : ℕ) : Prop :=
  ∀ c : (Icc 1 N).powersetCard e → Fin r,
    ∃ H ∈ (Icc 1 N).powerset, k ≤ H.card ∧ RelLarge H ∧ Homog c H

instance (e r k N : ℕ) : Decidable (PH e r k N) := by
  unfold PH RelLarge Homog; infer_instance

/-- The three parameters, packed into one input `x = ⟪e, ⟪r, k⟫⟫`. -/
def PHx (x N : ℕ) : Prop := PH x.unpair.1 x.unpair.2.unpair.1 x.unpair.2.unpair.2 N

-- Known-answer anchors (hand-computed): points (e = 1), two colours, a pair.
-- N = 2: colour 1 and 2 differently — no monochromatic pair.  N = 3: two of {1,2,3} share a
-- colour; any such pair {a,b} has min ≤ 2 = card.
-- Degenerate case: with no colours (`r = 0`) the property says `e ≤ N`.
example : ¬ PH 1 0 0 0 := by decide

example : ¬ PH 1 2 2 2 := by decide
example : PH 1 2 2 3 := by decide

end GoodsteinPA.PH

end
