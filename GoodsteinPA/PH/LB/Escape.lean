/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/

module

public import GoodsteinPA.PH.LB.Bad
public import GoodsteinPA.PH.Independence
public import GoodsteinPA.HydraEscape

@[expose] public section

/-!
# PH lower bound: Escape: growth comparison and `Escapes` (STAGE3-PH-PLAN step 7).

Part of the skeleton indexed in `GoodsteinPA/PH/LowerBound.lean`; statements are the design.
-/

namespace GoodsteinPA.PH.LB

open ONote Ordinal

/-! ### Step 7  Escape -/

/-- The input code `x = ⟪m+1, ⟪r, κ⟫⟫`. -/
def phCode (m k : ℕ) : ℕ := Nat.pair (m + 1) (Nat.pair (ncol k m) (2 * m + k + 4))

/-- The pure tower is below every `wtow` of the same height. -/
theorem tower_le_wtow : ∀ m k : ℕ, tower m ≤ wtow m k
  | 0, k => by
    rw [le_def, tower_zero, repr_zero]; exact zero_le
  | m + 1, k => by
    have ih := le_def.mp (tower_le_wtow m k)
    rw [le_def, tower_succ, wtow_succ]
    simp only [ONote.repr, PNat.one_coe, Nat.cast_one, mul_one, add_zero]
    exact Ordinal.opow_le_opow_right Ordinal.omega0_pos ih

/-- The input code grows at least like `k`. -/
theorem le_phCode (m k : ℕ) : k ≤ phCode m k := by
  unfold phCode ncol
  exact le_trans (Nat.le_add_right _ _)
    (le_trans (Nat.left_le_pair _ _) (Nat.right_le_pair _ _))

/-- A crude polynomial bound on the input code. -/
theorem phCode_le_pow (m k : ℕ) (hk : (∑ i ∈ Finset.range m, 3 ^ i) + 3 * m + 10 ≤ k) :
    phCode m k ≤ (4 * k) ^ 4 := by
  set S := ∑ i ∈ Finset.range m, 3 ^ i
  have hin : Nat.pair (ncol k m) (2 * m + k + 4) ≤ (2 * k) ^ 2 := by
    have h := Nat.pair_lt_max_add_one_sq (ncol k m) (2 * m + k + 4)
    have hmax : max (ncol k m) (2 * m + k + 4) + 1 ≤ 2 * k := by
      unfold ncol; rw [max_def]; split <;> omega
    exact le_trans h.le (Nat.pow_le_pow_left hmax 2)
  have h := Nat.pair_lt_max_add_one_sq (m + 1) (Nat.pair (ncol k m) (2 * m + k + 4))
  have hk1 : 1 ≤ k := by omega
  have hsq : (2 * k) ^ 2 = 4 * (k * k) := by ring
  have hkk : k ≤ k * k := Nat.le_mul_self k
  have hmax : max (m + 1) (Nat.pair (ncol k m) (2 * m + k + 4)) + 1 ≤ 16 * (k * k) := by
    rw [max_def]; split <;> omega
  calc phCode m k ≤ (16 * (k * k)) ^ 2 := le_trans h.le (Nat.pow_le_pow_left hmax 2)
    _ ≤ (4 * k) ^ 4 := by
      have : (16 * (k * k)) ^ 2 = 256 * (k * k) ^ 2 := by ring
      have h2 : (4 * k) ^ 4 = 256 * (k * k) ^ 2 := by ring
      omega

theorem pow_le_two_pow_two_pow {k : ℕ} (hk : 4 ≤ k) : (4 * k) ^ 4 ≤ 2 ^ (2 ^ k * k) := by
  have h1 : 4 * k ≤ 2 ^ (k + 2) := by
    have := (Nat.lt_two_pow_self (n := k)).le
    rw [pow_add]; omega
  have h16 : 16 ≤ 2 ^ k := by
    calc (16 : ℕ) = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have h2 : 4 * k + 8 ≤ 2 ^ k * k := by
    have := Nat.mul_le_mul_right k h16
    omega
  calc (4 * k) ^ 4 ≤ (2 ^ (k + 2)) ^ 4 := Nat.pow_le_pow_left h1 4
    _ = 2 ^ (4 * k + 8) := by rw [← pow_mul]; ring_nf
    _ ≤ 2 ^ (2 ^ k * k) := Nat.pow_le_pow_right (by norm_num) h2

/-- **Growth comparison** (the analogue of stage 2's P3 in `HydraEscape.escapes`): some tower
height `m` makes `ω_m(k)`'s Hardy function beat `f_o` at the polynomial input code. -/
theorem escape_growth (o : ONote) (ho : o.NF) :
    ∃ m, 1 ≤ m ∧ ∃ K, ∀ k ≥ K, fastGrowing o (phCode m k) ≤ hardy (wtow m k) (k + 1) := by
  have h1 := osucc_NF ho
  have h2 := osucc_NF h1
  have h3 := osucc_NF h2
  have hP : (osucc (osucc (osucc (osucc o)))).NF := osucc_NF h3
  set P := osucc (osucc (osucc (osucc o))) with hPdef
  have hchain : ∀ x, 2 ≤ x → fastGrowing o x < fastGrowing P x := fun x hx =>
    lt_trans (GoodsteinPA.Hydra.fastGrowing_lt_osucc ho hx)
      (lt_trans (GoodsteinPA.Hydra.fastGrowing_lt_osucc h1 hx)
      (lt_trans (GoodsteinPA.Hydra.fastGrowing_lt_osucc h2 hx)
        (GoodsteinPA.Hydra.fastGrowing_lt_osucc h3 hx)))
  have hδ : (oadd (ofNat 3) 1 0).NF := NF.oadd_zero _ _
  have hωP : (oadd P 1 0).NF := NF.oadd_zero _ _
  have hcond : (oadd (ofNat 3) 1 0).repr < ω ^ (lastExp (oadd P 1 0)).repr := by
    show ω ^ (ofNat 3).repr * (1 : ℕ+) + 0 < ω ^ P.repr
    have hrP : P.repr = o.repr + 1 + 1 + 1 + 1 := by
      rw [hPdef, repr_osucc h3, repr_osucc h2, repr_osucc h1, repr_osucc ho]
    have e1 : ((1 : ℕ) : Ordinal) ≤ o.repr + 1 := by rw [Nat.cast_one]; exact le_add_self
    have e2 : ((2 : ℕ) : Ordinal) ≤ o.repr + 1 + 1 :=
      (Nat.cast_succ (R := Ordinal) 1).symm ▸ add_le_add_left e1 1
    have e3 : ((3 : ℕ) : Ordinal) ≤ o.repr + 1 + 1 + 1 :=
      (Nat.cast_succ (R := Ordinal) 2).symm ▸ add_le_add_left e2 1
    have e4 : ((4 : ℕ) : Ordinal) ≤ o.repr + 1 + 1 + 1 + 1 :=
      (Nat.cast_succ (R := Ordinal) 3).symm ▸ add_le_add_left e3 1
    rw [hrP, ONote.repr_ofNat]
    simp only [PNat.one_coe, Nat.cast_one, mul_one, add_zero]
    apply (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mpr
    exact lt_of_lt_of_le (Nat.cast_lt.mpr (by norm_num)) e4
  set γ := oadd P 1 0 + oadd (ofNat 3) 1 0 with hγdef
  have hγ : γ.NF := inferInstance
  have hcomp : ∀ x, hardy γ x = hardy (oadd P 1 0) (hardy (oadd (ofNat 3) 1 0) x) :=
    hardy_add_comp _ hωP _ hδ (Or.inr hcond)
  obtain ⟨j, hj⟩ := tower_cofinal γ hγ
  refine ⟨j + 1, by omega, (∑ i ∈ Finset.range (j + 1), 3 ^ i) + 3 * (j + 1) + 10 + norm γ,
    fun k hk => ?_⟩
  have hk4 : 4 ≤ k := by omega
  have hcode : phCode (j + 1) k ≤ hardy (oadd (ofNat 3) 1 0) k :=
    calc phCode (j + 1) k ≤ (4 * k) ^ 4 := phCode_le_pow _ _ (by omega)
      _ ≤ 2 ^ (2 ^ k * k) := pow_le_two_pow_two_pow hk4
      _ ≤ fastGrowing (ofNat 3) k := Goodstein.Dom.two_pow_le_fastGrowing_ofNat_three (by omega)
      _ ≤ hardy (oadd (ofNat 3) 1 0) k := fastGrowing_le_hardy_omega_pow _ k
  have hlt : γ < wtow (j + 1) k :=
    lt_of_lt_of_le hj (le_trans (tower_strictMono.monotone (Nat.le_succ j)) (tower_le_wtow _ _))
  have hxk := le_phCode (j + 1) k
  calc fastGrowing o (phCode (j + 1) k)
      ≤ fastGrowing P (phCode (j + 1) k) := (hchain _ (by omega)).le
    _ ≤ hardy (oadd P 1 0) (phCode (j + 1) k) := fastGrowing_le_hardy_omega_pow P _
    _ ≤ hardy (oadd P 1 0) (hardy (oadd (ofNat 3) 1 0) k) := hardy_monotone _ hcode
    _ = hardy γ k := (hcomp k).symm
    _ ≤ hardy γ (k + 1) := hardy_le_succ γ k
    _ ≤ hardy (wtow (j + 1) k) (k + 1) := hardy_le_of_lt hγ (wtow_NF _ _) hlt (by omega)

theorem escapes : Escapes := by
  intro o ho M
  obtain ⟨m, hm, K, hK⟩ := escape_growth o ho
  set k := max K M
  refine ⟨phCode m k, le_trans (le_max_right K M) (le_phCode m k), fun N hN => ?_⟩
  have hN' : N ≤ descLen m k := by
    have := hs2 hm k
    have := hK k (le_max_left K M)
    omega
  unfold PHx phCode
  simp only [Nat.unpair_pair]
  exact not_PH_of_le_descLen hm k N hN'

end GoodsteinPA.PH.LB

end
