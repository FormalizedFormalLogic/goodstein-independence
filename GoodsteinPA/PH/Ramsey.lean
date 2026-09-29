/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/

module

public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Order.Interval.Set.Infinite
public import Mathlib.Order.Lattice.Nat

@[expose] public section

/-!
# The infinite Ramsey theorem (all exponents)

Every colouring of the finite subsets of ℕ into finitely many colours has, inside any infinite set,
an infinite set on whose `e`-element subsets it is constant.  Proof by induction on `e`: peel off the
least element `a`, recurse on the tail for the colouring `s ↦ c (insert a s)`, iterate, and
pigeonhole the colours of the peeled elements.
-/

namespace GoodsteinPA.PH

open Set

/-- **Infinite Ramsey.** -/
theorem infinite_ramsey {β : Type*} [Finite β] :
    ∀ (e : ℕ) (c : Finset ℕ → β) (S : Set ℕ), S.Infinite →
      ∃ H ⊆ S, H.Infinite ∧ ∃ b, ∀ s : Finset ℕ, (↑s : Set ℕ) ⊆ H → s.card = e → c s = b
  | 0, c, S, hS => ⟨S, subset_rfl, hS, c ∅, fun s _ hs => by rw [Finset.card_eq_zero.mp hs]⟩
  | e + 1, c, S, hS => by
    classical
    -- one peeling step on an infinite set `T`
    have step : ∀ T : {T : Set ℕ // T.Infinite}, ∃ T' : {T : Set ℕ // T.Infinite}, ∃ b : β,
        T'.1 ⊆ T.1 ∩ Ioi (sInf T.1) ∧
        ∀ s : Finset ℕ, (↑s : Set ℕ) ⊆ T'.1 → s.card = e → c (insert (sInf T.1) s) = b := by
      intro T
      have hinf : (T.1 ∩ Ioi (sInf T.1)).Infinite :=
        (T.2.sdiff (finite_Iic (sInf T.1))).mono fun y hy =>
          ⟨hy.1, lt_of_not_ge (by simpa using hy.2)⟩
      obtain ⟨H, hH, hHi, b, hb⟩ :=
        infinite_ramsey e (fun s => c (insert (sInf T.1) s)) _ hinf
      exact ⟨⟨H, hHi⟩, b, hH, hb⟩
    choose next col hnext using step
    let seq : ℕ → {T : Set ℕ // T.Infinite} := fun j => Nat.rec ⟨S, hS⟩ (fun _ T => next T) j
    have hseq : ∀ j, seq (j + 1) = next (seq j) := fun j => rfl
    let a : ℕ → ℕ := fun j => sInf (seq j).1
    have ha_mem : ∀ j, a j ∈ (seq j).1 := fun j => Nat.sInf_mem (seq j).2.nonempty
    have hsub_succ : ∀ j, (seq (j + 1)).1 ⊆ (seq j).1 ∩ Ioi (a j) := fun j => by
      rw [hseq]; exact (hnext (seq j)).1
    have hsub : ∀ j l, j ≤ l → (seq l).1 ⊆ (seq j).1 := by
      intro j l hjl
      induction hjl with
      | refl => exact subset_rfl
      | step _ ih => exact fun x hx => ih ((hsub_succ _ hx).1)
    have hlater : ∀ j l, j < l → a l ∈ (seq (j + 1)).1 := fun j l hjl =>
      hsub (j + 1) l hjl (ha_mem l)
    have ha_mono : StrictMono a := strictMono_nat_of_lt_succ fun j =>
      (hsub_succ j (ha_mem (j + 1))).2
    -- pigeonhole the colours
    obtain ⟨b, hb⟩ := Finite.exists_infinite_fiber (fun j => col (seq j))
    have hJ : ((fun j => col (seq j)) ⁻¹' {b}).Infinite := Set.infinite_coe_iff.mp hb
    refine ⟨a '' ((fun j => col (seq j)) ⁻¹' {b}), ?_, hJ.image ha_mono.injective.injOn, b, ?_⟩
    · rintro _ ⟨j, -, rfl⟩
      exact hsub 0 j (Nat.zero_le j) (ha_mem j)
    · intro s hs hcard
      have hne : s.Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨j, hj, hjm⟩ := hs (Finset.min'_mem s hne)
      have hins : s = insert (a j) (s.erase (a j)) := by
        rw [hjm, Finset.insert_erase (Finset.min'_mem s hne)]
      rw [hins]
      have hrest : (↑(s.erase (a j)) : Set ℕ) ⊆ (seq (j + 1)).1 := by
        intro x hx
        have hx' := Finset.mem_erase.mp hx
        obtain ⟨l, -, rfl⟩ := hs hx'.2
        have hlj : a j < a l := by
          rw [hjm]
          exact lt_of_le_of_ne (Finset.min'_le s _ hx'.2) (fun h => hx'.1 (by rw [hjm, h]))
        exact hlater j l (ha_mono.lt_iff_lt.mp hlj)
      have hcol := (hnext (seq j)).2 (s.erase (a j)) (by rw [← hseq]; exact hrest)
        (by rw [Finset.card_erase_of_mem (by rw [hjm]; exact Finset.min'_mem s hne)]; omega)
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hj
      rw [← hj]
      exact hcol

end GoodsteinPA.PH

end
