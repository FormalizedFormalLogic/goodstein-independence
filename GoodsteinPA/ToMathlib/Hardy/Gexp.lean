/-
# ONote — the `ω²` Hardy engine `Gexp`

The growth engine `Gexp := H_{ω²}` and its closure facts under addition, multiplication, and iteration.
-/
module

public import GoodsteinPA.ToMathlib.Hardy.Comparison
import Mathlib.Tactic.Ring

@[expose] public section

namespace ONote

open ONote Ordinal

/-- The growth engine: `H_{ω²}`. -/
noncomputable def Gexp : ℕ → ℕ := hardy (oadd (ONote.ofNat 2) 1 0)

@[grind =]
lemma Gexp_eq (x : ℕ) : Gexp x = 2 ^ (x + 1) * (x + 1) - 1 := by
  have h := hardy_omega_pow_ofNat 2 x
  have h2 : fastGrowing (ONote.ofNat 2) (x + 1) = 2 ^ (x + 1) * (x + 1) := by
    rw [show ONote.ofNat 2 = 2 from rfl, ONote.fastGrowing_two]
  have hpos : 0 < 2 ^ (x + 1) * (x + 1) := Nat.mul_pos (Nat.two_pow_pos _) (Nat.succ_pos x)
  unfold Gexp
  omega

lemma Gexp_monotone : Monotone Gexp := hardy_monotone _

@[grind .]
lemma le_Gexp (x : ℕ) : x ≤ Gexp x := le_hardy _ x

@[grind .]
lemma succ_le_Gexp (x : ℕ) : x + 1 ≤ Gexp x := by
  rw [Gexp_eq]
  have h2 : 2 ≤ 2 ^ (x + 1) := by
    calc 2 = 2 ^ 1 := rfl
    _ ≤ 2 ^ (x + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have h3 : 2 * (x + 1) ≤ 2 ^ (x + 1) * (x + 1) := Nat.mul_le_mul_right _ h2
  omega

/-- The two closure facts term domination needs: `Gexp (max a b)` absorbs both `a + b` and `a * b`. -/
@[grind .]
lemma add_le_Gexp_max (a b : ℕ) : a + b ≤ Gexp (max a b) := by
  rw [Gexp_eq]
  have h2 : 2 ≤ 2 ^ (max a b + 1) := by
    calc 2 = 2 ^ 1 := rfl
    _ ≤ 2 ^ (max a b + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have h3 : 2 * (max a b + 1) ≤ 2 ^ (max a b + 1) * (max a b + 1) := Nat.mul_le_mul_right _ h2
  have hab : a + b ≤ 2 * max a b := by omega
  omega

@[grind .]
lemma mul_le_Gexp_max (a b : ℕ) : a * b ≤ Gexp (max a b) := by
  rw [Gexp_eq]
  have hab : a * b ≤ max a b * max a b :=
    Nat.mul_le_mul (le_max_left a b) (le_max_right a b)
  have h1 : max a b + 1 ≤ 2 ^ (max a b + 1) := le_of_lt Nat.lt_two_pow_self
  have h2 : (max a b + 1) * (max a b + 1) = max a b * max a b + 2 * max a b + 1 := by ring
  have h3 : (max a b + 1) * (max a b + 1) ≤ 2 ^ (max a b + 1) * (max a b + 1) :=
    Nat.mul_le_mul_right _ h1
  omega

lemma Gexp_iter_monotone (c : ℕ) : Monotone (Gexp^[c]) :=
  Gexp_monotone.iterate c

@[grind .]
lemma le_Gexp_iter (c x : ℕ) : x ≤ Gexp^[c] x := by
  induction c with
  | zero => simp
  | succ c ih =>
      rw [Function.iterate_succ_apply']
      exact le_trans ih (le_Gexp _)

@[grind =>]
lemma Gexp_iter_le_iter {c c'} (h : c ≤ c') (x : ℕ) : Gexp^[c] x ≤ Gexp^[c'] x := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Function.iterate_add_apply]
  exact Gexp_iter_monotone c (le_Gexp_iter k x)

@[grind .]
lemma iter_le_Gexp_iter (c x : ℕ) : c ≤ Gexp^[c] x := by
  induction c with
  | zero => exact Nat.zero_le _
  | succ c ih =>
      rw [Function.iterate_succ_apply']
      have h1 := succ_le_Gexp (Gexp^[c] x)
      omega

/-- Iterates as a single Hardy value: `Gexp^[c] = H_{ω²·c}` — `hardy_single_coeff` absorbs the
iterate budget, using that the exponent `ofNat 2` is nonzero. -/
@[grind =]
lemma Gexp_iter_eq_hardy (c : ℕ+) (x : ℕ) :
    Gexp^[(c : ℕ)] x = hardy (oadd (ONote.ofNat 2) c 0) x :=
  (hardy_single_coeff (ONote.ofNat 2) (by decide) c x).symm

end ONote
