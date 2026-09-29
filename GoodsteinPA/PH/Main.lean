/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/

module

public import GoodsteinPA.PH.LowerBound
public import GoodsteinPA.PH.Computable

@[expose] public section

/-!
# PA does not prove the Paris–Harrington principle (stage 3 headline)

The two statements below were RATIFIED (Astra, 2026-09-26, in Trevor's place) and are frozen.
`pa_not_proves_ph` is stage 1's Wainer bound composed with `LB.escapes`, the Buchholz/Loebl–Nešetřil
lower bound (`PH/LB/`); `exists_sigma1_ph_def` is the primitive-recursive encoding (`PH/Computable.lean`).
-/

namespace GoodsteinPA.PH

open FFL FFL.FirstOrder

/-- **PA does not prove Paris–Harrington**: for every Σ₁ `φ` defining `PHx` pointwise in ℕ, PA does
not prove `∀ x, ∃ N, φ(x, N)`. -/
theorem pa_not_proves_ph
    (φ : Semisentence ℒₒᵣ 2) (hφ : Bounding.Hierarchy ℬ[<, ℒₒᵣ] 𝚺 1 φ)
    (hdef : ∀ x N : ℕ, (ℕ ⊧/![N, x] φ) ↔ PHx x N) :
    𝗣𝗔 ⊬ ↑(∀¹ ∃¹ φ : Sentence ℒₒᵣ) :=
  pa_not_proves_ph_of_escape LB.escapes φ hφ hdef

/-- **Anti-vacuity**: some Σ₁ formula defines `PHx` pointwise in ℕ. -/
theorem exists_sigma1_ph_def :
    ∃ φ : Semisentence ℒₒᵣ 2, Bounding.Hierarchy ℬ[<, ℒₒᵣ] 𝚺 1 φ ∧
      ∀ x N : ℕ, (ℕ ⊧/![N, x] φ) ↔ PHx x N := exists_sigma1_PHx_def

end GoodsteinPA.PH

end
