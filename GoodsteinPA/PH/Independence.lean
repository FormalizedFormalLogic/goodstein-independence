/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/

module

public import GoodsteinPA.WainerGeneral
public import GoodsteinPA.PH.Statement

@[expose] public section

/-!
# PA does not prove the Paris–Harrington principle — reduction to a lower bound

The (draft) headline, for every Σ₁ `φ` defining `PHx` pointwise in ℕ, follows from stage 1's
Wainer bound and `Escapes`: for every `o < ε₀`, arbitrarily large inputs `x` whose least
Paris–Harrington witness exceeds `f_o(x)`.
-/

namespace GoodsteinPA.PH

open FFL FFL.FirstOrder ONote

/-- The lower bound the grind must deliver. -/
def Escapes : Prop :=
  ∀ o : ONote, o.NF → ∀ M : ℕ, ∃ x ≥ M, ∀ N ≤ fastGrowing o x, ¬ PHx x N

theorem pa_not_proves_ph_of_escape (hesc : Escapes)
    (φ : Semisentence ℒₒᵣ 2) (hφ : ℬ[<, ℒₒᵣ].Hierarchy 𝚺 1 φ)
    (hdef : ∀ x N : ℕ, (ℕ ⊧/![N, x] φ) ↔ PHx x N) :
    𝗣𝗔 ⊬ ↑(∀¹ ∃¹ φ : Sentence ℒₒᵣ) := by
  intro h
  obtain ⟨o, ho, M, hM⟩ :=
    GoodsteinPA.Wainer.pa_provable_pi2_eventually_witnessed_below_fastGrowing φ hφ h
  obtain ⟨x, hx, hbad⟩ := hesc o ho M
  obtain ⟨N, hN, hsem⟩ := hM x hx
  exact hbad N hN ((hdef x N).mp hsem)

end GoodsteinPA.PH

end
