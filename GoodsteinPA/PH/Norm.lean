/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/

module

public import GoodsteinPA.ToMathlib.Hardy.Basic

@[expose] public section

/-!
# The Loebl–Nešetřil norm on Cantor normal forms (Buchholz, *Beweistheorie* 1998, §7)

For `α = ω^{α₁}n₁ + … + ω^{α_t}n_t` in Cantor normal form, Buchholz's norm is
`r(α) = max{t, n₁, …, n_t, r(α₁), …, r(α_t)}` (Definition before Lemma 7.6).  This file defines
it on Mathlib's `ONote` and proves Lemma 7.6:

* `step_bounds` / `normr_step_le` (7.6a): `r(α[k]) ≤ max{r(α), k} + 1`;
* `normr_step_lt` (7.6b): `r(α) < n → r(α[n-1]) < n+1`;
* `normr_tower_add` (7.6c): `r(ω_m(k) + n) ≤ n + 1` for `1 ≤ m` and `k < n`.

`step α k` is the `k`-th member of Mathlib's fundamental sequence at `α`, i.e. Buchholz's `α[k]`
(the predecessor when `α` is a successor, `0` when `α = 0`).
-/

namespace GoodsteinPA.PH

open ONote

/-! ### The norm -/

/-- The number of Cantor normal form terms. -/
def nterms : ONote → ℕ
  | 0 => 0
  | oadd _ _ b => nterms b + 1

/-- **Buchholz's norm** `r(α) = max{t, n₁, …, n_t, r(α₁), …, r(α_t)}`. -/
def normr : ONote → ℕ
  | 0 => 0
  | oadd a m b => max (max (nterms b + 1) (m : ℕ)) (max (normr a) (normr b))

@[simp] theorem nterms_zero : nterms 0 = 0 := rfl
@[simp] theorem normr_zero : normr 0 = 0 := rfl
@[simp] theorem nterms_zero' : nterms ONote.zero = 0 := rfl
@[simp] theorem normr_zero' : normr ONote.zero = 0 := rfl

theorem normr_oadd (a : ONote) (m : ℕ+) (b : ONote) :
    normr (oadd a m b) = max (max (nterms b + 1) (m : ℕ)) (max (normr a) (normr b)) := rfl

theorem nterms_oadd (a : ONote) (m : ℕ+) (b : ONote) :
    nterms (oadd a m b) = nterms b + 1 := rfl

theorem nterms_le_normr : ∀ α : ONote, nterms α ≤ normr α
  | 0 => le_refl 0
  | oadd a m b => by rw [nterms_oadd, normr_oadd]; omega

/-! ### `α[k]`: one fundamental-sequence step -/

/-- Buchholz's `α[k]`: the `k`-th member of the fundamental sequence at a limit, the predecessor
at a successor, and `0` at `0`. -/
def step (α : ONote) (k : ℕ) : ONote :=
  match fundamentalSequence α with
  | Sum.inl none => 0
  | Sum.inl (some a) => a
  | Sum.inr f => f k

@[simp] theorem step_zero (k : ℕ) : step 0 k = 0 := rfl

/-- **Lemma 7.6a**, together with the `nterms` bookkeeping the induction needs. -/
theorem step_bounds : ∀ (α : ONote) (k : ℕ),
    normr (step α k) ≤ max (normr α) k + 1 ∧ nterms (step α k) ≤ nterms α + 1
  | 0, k => by simp
  | oadd a m b, k => by
    have hm1 : (m : ℕ) = m.natPred + 1 := (PNat.natPred_add_one m).symm
    have hra : normr (step a k) ≤ max (normr a) k + 1 := (step_bounds a k).1
    have ihb := step_bounds b k
    have hnb : nterms b ≤ normr b := nterms_le_normr b
    rcases eb : fundamentalSequence b with (_ | b') | fb
    · rcases ea : fundamentalSequence a with (_ | a') | fa <;>
        rcases em : (m : ℕ+).natPred with _ | m' <;>
        simp_all only [step, fundamentalSequence, normr_oadd, nterms_oadd, normr_zero,
          normr_zero', nterms_zero, nterms_zero', Nat.succPNat_coe, PNat.one_coe] <;>
        exact ⟨by omega, by omega⟩
    · simp_all only [step, fundamentalSequence, normr_oadd, nterms_oadd]
      exact ⟨by omega, by omega⟩
    · simp_all only [step, fundamentalSequence, normr_oadd, nterms_oadd]
      exact ⟨by omega, by omega⟩

/-- **Lemma 7.6a.** -/
theorem normr_step_le (α : ONote) (k : ℕ) : normr (step α k) ≤ max (normr α) k + 1 :=
  (step_bounds α k).1

/-- **Lemma 7.6b.** -/
theorem normr_step_lt {α : ONote} {n : ℕ} (h : normr α < n) : normr (step α (n - 1)) < n + 1 := by
  have := normr_step_le α (n - 1)
  omega

/-! ### The tower `ω_m(k)` and Lemma 7.6c -/

/-- `ω_m(k)` as an `ONote`: `ω_0(k) = k`, `ω_{m+1}(k) = ω^{ω_m(k)}`. -/
def towerNote : ℕ → ℕ → ONote
  | 0, k => ofNat k
  | m + 1, k => oadd (towerNote m k) 1 0

theorem normr_ofNat : ∀ n : ℕ, normr (ofNat n) = n
  | 0 => rfl
  | n + 1 => by
    rw [ofNat_succ, normr_oadd]
    simp [Nat.succPNat]

theorem nterms_ofNat_le : ∀ n : ℕ, nterms (ofNat n) ≤ 1
  | 0 => by simp
  | n + 1 => by rw [ofNat_succ, nterms_oadd]; simp

/-- `r(ω_m(k)) = max 1 k` once `k ≥ 1`; stated as the bound we need. -/
theorem normr_towerNote : ∀ (m k : ℕ), 1 ≤ k → normr (towerNote m k) = k
  | 0, k, _ => by rw [towerNote, normr_ofNat]
  | m + 1, k, hk => by
    rw [towerNote, normr_oadd, normr_towerNote m k hk]
    simp only [nterms_zero, normr_zero, PNat.one_coe]
    omega

/-- The start of the Loebl–Nešetřil descent: `ω_{m+1}(k) + n`. -/
def start (m k n : ℕ) : ONote := oadd (towerNote m k) 1 (ofNat n)

/-- **Lemma 7.6c**: `r(ω_m(k) + n) ≤ n + 1` for `1 ≤ m` and `k < n`. -/
theorem normr_start_le {m k n : ℕ} (hk : 1 ≤ k) (hkn : k < n) : normr (start m k n) ≤ n + 1 := by
  rw [start, normr_oadd, normr_towerNote m k hk, normr_ofNat]
  have := nterms_ofNat_le n
  simp only [PNat.one_coe]
  omega

end GoodsteinPA.PH

end
