/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
module

public import GoodsteinPA.WainerGeneral
public import GoodsteinPA.ToMathlib.Hydra.Canonical

@[expose] public section

/-!
# PA does not prove that the canonical hydra battle terminates

The object is `lean-gallery`'s canonical battle (`LeanGallery.Logic.Hydra.Canonical`): Hercules
chops along the first child of minimal Kirby–Paris ordinal, turn `j` regrows `j + 1` copies, and
every such move is a legal gallery `Step` (`canonStep_legal`).  The battle always ends
(`battle_terminates`); PA cannot prove it.

**Headline.**  For EVERY Σ₁ formula `φ` that
defines the battle pointwise in ℕ, `ℕ ⊧ φ(m, N) ↔ battle (ofCode m) N = leaf`, PA does not prove
`∀ m, ∃ N, φ(m, N)`; and at least one such `φ` exists (`exists_sigma1_battle_def`).

This file currently proves the headline **from the lower bound as a hypothesis**
(`pa_not_proves_hydra_of_escape`): stage 1 bounds a PA-provable witness by some `f_o`, `hdef` turns
the witness into a battle that has ended by then, and escape says it has not.
-/

namespace GoodsteinPA.Hydra

open FFL FFL.FirstOrder ONote
open LeanGallery.Logic.Hydra

/-- The lower bound the grind must deliver: for every `o < ε₀` there are arbitrarily large codes
`m` whose canonical battle is still alive at every step `N ≤ f_o(m)`. -/
def Escapes : Prop :=
  ∀ o : ONote, o.NF → ∀ M : ℕ, ∃ m ≥ M, ∀ N ≤ fastGrowing o m, battle (ofCode m) N ≠ Hydra.leaf

/-- **The headline, modulo the lower bound.** -/
theorem pa_not_proves_hydra_of_escape (hesc : Escapes)
    (φ : Semisentence ℒₒᵣ 2) (hφ : ℬ[<, ℒₒᵣ].Hierarchy 𝚺 1 φ)
    (hdef : ∀ m N : ℕ, (ℕ ⊧/![N, m] φ) ↔ battle (ofCode m) N = Hydra.leaf) :
    𝗣𝗔 ⊬ ↑(∀¹ ∃¹ φ : Sentence ℒₒᵣ) := by
  intro h
  obtain ⟨o, ho, M, hM⟩ :=
    GoodsteinPA.Wainer.pa_provable_pi2_eventually_witnessed_below_fastGrowing φ hφ h
  obtain ⟨m, hm, hlive⟩ := hesc o ho M
  obtain ⟨N, hN, hsem⟩ := hM m hm
  exact hlive N hN ((hdef m N).mp hsem)

end GoodsteinPA.Hydra

end
