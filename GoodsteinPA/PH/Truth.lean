/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/

module

public import GoodsteinPA.PH.Statement
public import GoodsteinPA.PH.Ramsey
public import Mathlib.Combinatorics.Compactness

@[expose] public section

/-!
# The Paris–Harrington principle is true

From the infinite Ramsey theorem by compactness (Mathlib's `Finset.rado_selection`): if every `N`
had a bad colouring, stitch them into one colouring `χ` of all finite sets; an infinite
`χ`-homogeneous set yields a relatively large finite homogeneous set, which one of the bad colourings
must also see.
-/

namespace GoodsteinPA.PH

open Finset

theorem ph_true (e r k : ℕ) : ∃ N, PH e r k N := by
  classical
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · -- no colours: the domain is nonempty at `N = e`, so there is no colouring at all
    refine ⟨e, fun c => ?_⟩
    have hmem : Icc 1 e ∈ (Icc 1 e).powersetCard e :=
      mem_powersetCard.mpr ⟨subset_rfl, by simp⟩
    exact (c ⟨_, hmem⟩).elim0
  by_contra hno
  push Not at hno
  simp only [PH, not_forall, not_exists, not_and] at hno
  choose bad hbad using hno
  let top : Finset (Finset ℕ) → ℕ := fun F => F.sup fun s => s.sup id
  let g : Finset (Finset ℕ) → Finset ℕ → Fin r := fun F s =>
    if hs : s ∈ (Icc 1 (top F)).powersetCard e then bad (top F) ⟨s, hs⟩ else ⟨0, hr⟩
  obtain ⟨χ, hχ⟩ := Finset.rado_selection g
  obtain ⟨H, hHS, hHinf, b, hb⟩ :=
    infinite_ramsey e χ (Set.Ici 1) (Set.Ici_infinite 1)
  -- a relatively large finite piece of `H` containing its least element
  have hHne : H.Nonempty := hHinf.nonempty
  set a₀ := sInf H with ha₀
  have ha₀H : a₀ ∈ H := Nat.sInf_mem hHne
  have ha₀pos : 1 ≤ a₀ := hHS ha₀H
  set m := max k a₀
  obtain ⟨T, hTsub, hTcard⟩ := (hHinf.sdiff (Set.finite_singleton a₀)).exists_subset_card_eq (m - 1)
  let H0 := insert a₀ T
  have ha₀T : a₀ ∉ T := fun h => by simpa using (hTsub h).2
  have hH0card : H0.card = m := by
    rw [card_insert_of_notMem ha₀T, hTcard]; omega
  have hH0H : (↑H0 : Set ℕ) ⊆ H := by
    intro x hx
    rcases mem_insert.mp hx with rfl | hx
    · exact ha₀H
    · exact (hTsub hx).1
  let F := H0.powersetCard e ∪ H0.image singleton
  obtain ⟨t, hFt, hχt⟩ := hχ F
  have hH0N : H0 ⊆ Icc 1 (top t) := by
    intro x hx
    refine mem_Icc.mpr ⟨hHS (hH0H hx), ?_⟩
    have hxF : ({x} : Finset ℕ) ∈ t := hFt (mem_union_right _ (mem_image_of_mem _ hx))
    exact le_trans (by simp) (le_sup (f := fun s => s.sup id) hxF)
  refine hbad (top t) H0 (mem_powerset.mpr hH0N) (by omega) ?_ ⟨b, fun s hs hsH => ?_⟩
  · intro a ha hmin
    have := hmin a₀ (mem_insert_self _ _)
    omega
  · have hsF : s ∈ F := mem_union_left _ (mem_powersetCard.mpr ⟨hsH, (mem_powersetCard.mp hs).2⟩)
    have h1 := hχt s hsF
    have h2 : g t s = bad (top t) ⟨s, hs⟩ := dif_pos hs
    rw [← h2, ← h1]
    exact hb s (fun x hx => hH0H (hsH hx)) (mem_powersetCard.mp hs).2

end GoodsteinPA.PH

end
