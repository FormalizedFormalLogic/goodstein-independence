/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/

module

public import GoodsteinPA.PH.LB.Colour
public import GoodsteinPA.PH.LB.Descent
public import GoodsteinPA.PH.Statement
public import Mathlib.Data.Finset.Sort

@[expose] public section

/-!
# PH lower bound: The bad colouring: Theorem 7.5 in repo form (spec §3).

Part of the skeleton indexed in `GoodsteinPA/PH/LowerBound.lean`; statements are the design.
-/

namespace GoodsteinPA.PH.LB

open ONote

/-! ### §3  The bad colouring and `¬ PH` -/

/-- The bad colouring on `(m+1)`-subsets of `{1,…,N}`: element `j` stands for `α_{j-1}`. -/
def badCol (m k : ℕ) (s : Finset ℕ) : ℕ :=
  chiK k m ((s.sort (· ≤ ·)).map fun j => alpha m k (j - 1))

/-- Strict descent of `α` between any two indices below the descent length. -/
theorem alpha_lt_of_lt {m k a b : ℕ} (hab : a < b) (hb : b ≤ descLen m k - 1) :
    alpha m k b < alpha m k a := by
  induction b with
  | zero => omega
  | succ b ih =>
    have h1 := (alpha_chain m k).2 b (by omega)
    rcases Nat.lt_succ_iff_lt_or_eq.mp hab with h | h
    · exact lt_trans h1 (ih h (by omega))
    · subst h; exact h1

/-- **Theorem 7.5, repo form.**  Below the descent length, PH fails with exponent `m + 1`,
`ncol k m` colours and size `2m + k + 4`. -/
theorem not_PH_of_le_descLen {m : ℕ} (hm : 1 ≤ m) (k : ℕ) :
    ∀ N ≤ descLen m k, ¬ PH (m + 1) (ncol k m) (2 * m + k + 4) N := by
  intro N hN hPH
  obtain ⟨H, hHP, hκ, hRL, i0, hH⟩ :=
    hPH (fun s => ⟨badCol m k s.1, chiK_lt k m hm _⟩)
  have hHN : H ⊆ Finset.Icc 1 N := Finset.mem_powerset.mp hHP
  set L := H.sort (· ≤ ·) with hLdef
  have hLp : L.Pairwise (· < ·) := (Finset.sortedLT_sort H).pairwise
  have hLlen : L.length = H.card := Finset.length_sort _
  have hLmem : ∀ x, x ∈ L ↔ x ∈ H := fun x => Finset.mem_sort _
  have hLlt : ∀ i j (hi : i < L.length) (hj : j < L.length), i < j → L[i] < L[j] :=
    List.pairwise_iff_getElem.mp hLp
  have hLin : ∀ i (hi : i < L.length), 1 ≤ L[i] ∧ L[i] ≤ N := fun i hi => by
    have := hHN ((hLmem _).mp (List.getElem_mem hi)); simpa using this
  have hgD : ∀ j (h : j < L.length), L.getD j 0 = L[j] := fun j h => by simp [h]
  set ℓ := H.card - 1 with hℓ
  have hlen : L.length = ℓ + 1 := by omega
  set β : ℕ → ONote := fun j => alpha m k (L.getD j 0 - 1) with hβdef
  have hβ : Chain β ℓ := by
    refine ⟨fun i _ => alpha_NF _ _ _, fun i hi => ?_⟩
    simp only [β, hgD i (by omega), hgD (i + 1) (by omega)]
    have := hLlt i (i + 1) (by omega) (by omega) (by omega)
    have := hLin i (by omega)
    have := hLin (i + 1) (by omega)
    exact alpha_lt_of_lt (by omega) (by omega)
  have hmℓ : m < ℓ := by omega
  have hχ : ∀ i, i + m ≤ ℓ → chiK k m (window β m i) = i0.val := by
    intro i hi
    set l := (L.drop i).take (m + 1) with hldef
    have hsub : l.Sublist L := (List.take_sublist _ _).trans (List.drop_sublist _ _)
    have hlp : l.Pairwise (· < ·) := hLp.sublist hsub
    have hnd : l.Nodup := hlp.imp ne_of_lt
    have hllen : l.length = m + 1 := by simp [l]; omega
    have hsort : l.toFinset.sort (· ≤ ·) = l :=
      (List.toFinset_sort _ hnd).mpr (hlp.imp le_of_lt)
    have hlH : l.toFinset ⊆ H := fun x hx => (hLmem x).mp (hsub.subset (List.mem_toFinset.mp hx))
    have hs : l.toFinset ∈ (Finset.Icc 1 N).powersetCard (m + 1) := by
      rw [Finset.mem_powersetCard]
      exact ⟨hlH.trans hHN, by rw [List.toFinset_card_of_nodup hnd, hllen]⟩
    have hc : badCol m k l.toFinset = i0.val := congrArg Fin.val (hH _ hs hlH)
    rw [← hc, badCol, hsort]
    congr 1
    apply List.ext_getElem
    · simp [window, hllen]
    · intro j h1 h2
      have hj : j < m + 1 := by simpa [window] using h1
      simp [window, β, l, List.getElem?_eq_getElem (show i + j < L.length by omega)]
  have h1 := chiK_homog_len hm hmℓ hβ (alpha_lt_wtow_succ hm k _) hχ
  have h2 := hs1 hm k (L.getD 0 0 - 1)
  have hL0 : L.getD 0 0 = L[0]'(by omega) := hgD 0 _
  have h0 : L.getD 0 0 ≤ H.card := by
    rw [hL0]
    refine hRL _ ((hLmem _).mp (List.getElem_mem _)) fun b hb => ?_
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp ((hLmem b).mpr hb)
    rcases Nat.eq_zero_or_pos j with h | h
    · subst h; exact le_rfl
    · exact (hLlt 0 j _ hj h).le
  have h1' : ℓ < rnorm (alpha m k (L.getD 0 0 - 1)) + m := h1
  rcases lt_max_iff.mp h2 with h | h <;> omega

end GoodsteinPA.PH.LB

end
