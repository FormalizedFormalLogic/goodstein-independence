/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/

module

public import GoodsteinPA.PH.LB.Cnf

@[expose] public section

/-!
# PH lower bound: The descent `α_i`, its length `N`, HS1 and HS2 (spec §3).

Part of the skeleton indexed in `GoodsteinPA/PH/LowerBound.lean`; statements are the design.
-/

namespace GoodsteinPA.PH.LB

open ONote

/-! ### §3  The descent and HS1 / HS2 -/

/-- `α₀ = ω_m(k) + n` with `n = m + k + 2`, `α_{i+1} = α_i[i ∸ (m+1)]`. -/
def alpha (m k : ℕ) : ℕ → ONote
  | 0 => wtow m k + ofNat (m + k + 2)
  | i + 1 => fsStep (alpha m k i) (i - (m + 1))

theorem alpha_NF (m k i : ℕ) : (alpha m k i).NF := by
  induction i with
  | zero =>
    haveI := wtow_NF m k
    exact ONote.add_nf _ _
  | succ i ih => exact fsStep_NF ih _

/-! #### Helpers -/

private theorem add_ofNat_zero' {α : ONote} (hα : α.NF) : α + ofNat 0 = α := by
  haveI := hα
  haveI : (0 : ONote).NF := NF.zero
  rw [ofNat_zero]
  haveI : (α + 0).NF := ONote.add_nf α 0
  apply repr_inj.mp
  rw [repr_add, repr_zero, add_zero]

private theorem add_ofNat_succ' {α : ONote} (hα : α.NF) (c : ℕ) :
    α + ofNat (c + 1) = osucc (α + ofNat c) := by
  haveI := hα
  haveI hac : (α + ofNat c).NF := ONote.add_nf α (ofNat c)
  haveI : (α + ofNat (c + 1)).NF := ONote.add_nf α (ofNat (c + 1))
  haveI : (osucc (α + ofNat c)).NF := osucc_NF hac
  apply repr_inj.mp
  rw [repr_osucc hac, repr_add, repr_add, repr_ofNat, repr_ofNat,
    Nat.cast_add, Nat.cast_one, ← add_assoc]

theorem fsStep_zero (x : ℕ) : fsStep 0 x = 0 := rfl

theorem fsStep_osucc {o : ONote} (ho : o.NF) (x : ℕ) : fsStep (osucc o) x = o := by
  unfold fsStep; rw [fundamentalSequence_osucc ho]

theorem fsStep_le {o : ONote} (ho : o.NF) (x : ℕ) : fsStep o x ≤ o := by
  by_cases h0 : o = 0
  · subst h0; exact le_refl _
  · exact le_of_lt (fsStep_lt ho h0 x)

/-- For `i ≤ n`, `α_i = ω_m(k) + (n - i)`. -/
theorem alpha_eq_of_le (m k : ℕ) :
    ∀ i, i ≤ m + k + 2 → alpha m k i = wtow m k + ofNat (m + k + 2 - i) := by
  intro i
  induction i with
  | zero => intro _; rfl
  | succ i ih =>
    intro hi
    rw [alpha, ih (by omega), show m + k + 2 - i = (m + k + 2 - (i + 1)) + 1 by omega,
      add_ofNat_succ' (wtow_NF m k)]
    exact fsStep_osucc (haveI := wtow_NF m k; ONote.add_nf _ _) _

theorem wtow_ne_zero {m : ℕ} (hm : 1 ≤ m) (k : ℕ) : wtow m k ≠ 0 := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rw [wtow_succ]; intro h; cases h

theorem alpha_ne_zero_of_le {m : ℕ} (hm : 1 ≤ m) (k : ℕ) {i : ℕ} (hi : i ≤ m + k + 2) :
    alpha m k i ≠ 0 := by
  rw [alpha_eq_of_le m k i hi]
  intro h
  haveI := wtow_NF m k
  have h' := congrArg ONote.repr h
  rw [repr_add, repr_zero] at h'
  have : (wtow m k).repr = 0 :=
    le_antisymm (h' ▸ le_self_add) zero_le
  exact wtow_ne_zero hm k (repr_inj.mp (by rw [this, repr_zero]))

theorem exists_alpha_eq_zero (m k : ℕ) : ∃ i, alpha m k i = 0 := by
  by_contra hne
  push Not at hne
  suffices H : ∀ o : Ordinal, ∀ i, (alpha m k i).repr = o → False from H _ 0 rfl
  intro o
  induction o using WellFoundedLT.induction with
  | ind o ih =>
    intro i hi
    refine ih _ ?_ (i + 1) rfl
    rw [← hi]
    exact lt_def.mp (fsStep_lt (alpha_NF m k i) (hne i) _)

/-- `N := min{i : α_i = 0}`. -/
def descLen (m k : ℕ) : ℕ := Nat.find (exists_alpha_eq_zero m k)

/-- The descent is strictly decreasing up to `N`. -/
theorem alpha_chain (m k : ℕ) : Chain (alpha m k) (descLen m k - 1) := by
  refine ⟨fun i _ => alpha_NF m k i, fun i hi => ?_⟩
  have hne : alpha m k i ≠ 0 := Nat.find_min (exists_alpha_eq_zero m k) (by
    unfold descLen at hi; omega)
  exact fsStep_lt (alpha_NF m k i) hne _

theorem alpha_le_alpha_zero (m k : ℕ) : ∀ i, alpha m k i ≤ alpha m k 0 := by
  intro i
  induction i with
  | zero => exact le_refl _
  | succ i ih => exact le_trans (fsStep_le (alpha_NF m k i) _) ih

theorem wtow_lt_succ (m k : ℕ) : wtow m k < wtow m (k + 1) := by
  induction m with
  | zero =>
    show ofNat k < ofNat (k + 1)
    rw [lt_def, repr_ofNat, repr_ofNat]; exact_mod_cast Nat.lt_succ_self k
  | succ m ih =>
    rw [wtow_succ, wtow_succ, lt_def]
    simp only [ONote.repr, PNat.one_coe, Nat.cast_one, mul_one, add_zero]
    exact (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mpr (lt_def.mp ih)

open Ordinal in
/-- `α_i < ω_m(k+1)` (so `χ^k_m` applies). -/
theorem alpha_lt_wtow_succ {m : ℕ} (hm : 1 ≤ m) (k i : ℕ) : alpha m k i < wtow m (k + 1) := by
  refine lt_of_le_of_lt (alpha_le_alpha_zero m k i) ?_
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  show wtow (m' + 1) k + ofNat (m' + 1 + k + 2) < wtow (m' + 1) (k + 1)
  haveI := wtow_NF (m' + 1) k
  rw [lt_def, repr_add, repr_ofNat, wtow_succ, wtow_succ]
  simp only [ONote.repr, PNat.one_coe, Nat.cast_one, mul_one, add_zero]
  have hlt : ω ^ (wtow m' k).repr < ω ^ (wtow m' (k + 1)).repr :=
    (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mpr (lt_def.mp (wtow_lt_succ m' k))
  have hpos : (0 : Ordinal) < (wtow m' (k + 1)).repr :=
    lt_of_le_of_lt zero_le (lt_def.mp (wtow_lt_succ m' k))
  have hω : ((m' + 1 + k + 2 : ℕ) : Ordinal) < ω ^ (wtow m' (k + 1)).repr := by
    refine lt_of_lt_of_le (Ordinal.natCast_lt_omega0 _) ?_
    exact Ordinal.left_le_opow _ hpos
  exact Ordinal.isPrincipal_add_omega0_opow _ hlt hω

/-- `r(ω_m(k) + j) ≤ max 2 (max k (j + 1))` for `m ≥ 1`. -/
theorem rnorm_wtow_add_ofNat_le {m : ℕ} (hm : 1 ≤ m) (k j : ℕ) :
    rnorm (wtow m k + ofNat j) ≤ max 2 (max k (j + 1)) := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have hw := rnorm_wtow_le (m' + 1) k
  rw [wtow_succ] at hw ⊢
  generalize wtow m' k = E at hw ⊢
  have he : rnorm E ≤ max 1 k := le_trans (by simp only [rnorm]; omega) hw
  rcases E with _ | ⟨e, n, a⟩
  · cases j with
    | zero =>
      show rnorm (oadd 0 1 0) ≤ _
      simp only [rnorm, tlen, PNat.one_coe]; omega
    | succ j =>
      show rnorm (oadd 0 (1 + j.succPNat) 0) ≤ _
      simp only [rnorm, tlen, PNat.add_coe, PNat.one_coe, Nat.succPNat_coe]; omega
  · cases j with
    | zero =>
      show rnorm (oadd (oadd e n a) 1 0) ≤ _
      omega
    | succ j =>
      rw [show oadd (oadd e n a) 1 0 + ofNat (j + 1) =
        oadd (oadd e n a) 1 (oadd 0 j.succPNat 0) from rfl]
      generalize oadd e n a = E at he ⊢
      simp only [rnorm, tlen, PNat.one_coe, Nat.succPNat_coe]; omega

theorem hs1_le {m : ℕ} (hm : 1 ≤ m) (k i : ℕ) (hi : i ≤ m + k + 2) :
    rnorm (alpha m k i) ≤ m + k + 3 := by
  rw [alpha_eq_of_le m k i hi]
  refine le_trans (rnorm_wtow_add_ofNat_le hm k _) ?_
  omega

theorem hs1_ge {m : ℕ} (k : ℕ) :
    ∀ j, rnorm (alpha m k (m + k + 2 + j)) + m < m + k + 2 + j := by
  intro j
  induction j with
  | zero =>
    rw [Nat.add_zero, alpha_eq_of_le m k _ le_rfl, Nat.sub_self, add_ofNat_zero' (wtow_NF m k)]
    have := rnorm_wtow_le m k
    have : max 1 k ≤ k + 1 := by omega
    omega
  | succ j ih =>
    rw [show m + k + 2 + (j + 1) = (m + k + 2 + j) + 1 by omega, alpha]
    have := rnorm_fsStep_le (alpha_NF m k (m + k + 2 + j)) (m + k + 2 + j - (m + 1))
    omega

/-- **HS1**, both halves in one: `r(α_i) + m < max(κ, i)` with `κ = 2m + k + 4`. -/
theorem hs1 {m : ℕ} (hm : 1 ≤ m) (k i : ℕ) : rnorm (alpha m k i) + m < max (2 * m + k + 4) i := by
  by_cases hi : i ≤ m + k + 2
  · have := hs1_le hm k i hi
    omega
  · obtain ⟨j, rfl⟩ : ∃ j, i = m + k + 2 + j := ⟨i - (m + k + 2), by omega⟩
    have := hs1_ge (m := m) k j
    omega

theorem hs2_inv {m : ℕ} (k : ℕ) :
    ∀ j, m + k + 2 + j ≤ descLen m k →
      hardy (alpha m k (m + k + 2)) (k + 1) ≤
        hardy (alpha m k (m + k + 2 + j)) (m + k + 2 + j - m - 1) := by
  intro j
  induction j with
  | zero => intro _; simp only [Nat.add_zero]; exact le_of_eq (by congr 1; omega)
  | succ j ih =>
    intro hj
    refine le_trans (ih (by omega)) ?_
    set i := m + k + 2 + j with hi
    have hne : alpha m k i ≠ 0 := Nat.find_min (exists_alpha_eq_zero m k) (by
      unfold descLen at hj; omega)
    rw [show m + k + 2 + (j + 1) = i + 1 by omega, alpha,
      show i - (m + 1) = i - m - 1 by omega, show i + 1 - m - 1 = i - m - 1 + 1 by omega]
    have hprop := fundamentalSequence_has_prop (alpha m k i)
    unfold fsStep
    rcases hfs : fundamentalSequence (alpha m k i) with (_ | a) | f
    · rw [hfs] at hprop; exact absurd hprop hne
    · rw [hardy_succ _ hfs]
    · rw [hardy_limit _ hfs]
      exact hardy_le_succ _ _

/-- **HS2** in the repo's `hardy` (no `+1` at limits, hence `≤`): P2-style. -/
theorem hs2 {m : ℕ} (hm : 1 ≤ m) (k : ℕ) : hardy (wtow m k) (k + 1) + m + 1 ≤ descLen m k := by
  have hn : m + k + 2 ≤ descLen m k := by
    unfold descLen
    rw [Nat.le_find_iff]
    intro i hi
    exact alpha_ne_zero_of_le hm k (by omega)
  obtain ⟨j, hj⟩ : ∃ j, descLen m k = m + k + 2 + j := ⟨descLen m k - (m + k + 2), by omega⟩
  have hinv := hs2_inv (m := m) k j (by omega)
  rw [← hj, show alpha m k (descLen m k) = 0 from Nat.find_spec (exists_alpha_eq_zero m k),
    hardy_zero, alpha_eq_of_le m k _ le_rfl, Nat.sub_self,
    add_ofNat_zero' (wtow_NF m k)] at hinv
  simp only [id] at hinv
  omega

end GoodsteinPA.PH.LB

end
