/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
module

public import GoodsteinPA.ToMathlib.Hardy.Basic
public import GoodsteinPA.ToMathlib.Hydra.Canonical

@[expose] public section

/-!
# The canonical hydra battle outlasts the Hardy function of its ordinal (stage 2, P2)

`runFrom h t k` is the hydra after `k` canonical moves starting from `h` at turn `t`
(`battle h = runFrom h 0`).  Because each canonical move is one fundamental-sequence step of `ord`
(`LeanGallery.Logic.Hydra.ord_canonStep`), the battle is still alive at step `k` whenever
`t + k < hardy (ord h) t`: the successor case is `hardy_succ`, the limit case `hardy_limit` plus
`hardy_le_succ` (the move also advances the turn).
-/

namespace GoodsteinPA.Hydra

open ONote Ordinal
open LeanGallery.Logic.Hydra

/-- The canonical battle from `h`, starting at turn `t`. -/
def runFrom (h : Hydra) (t : ℕ) : ℕ → Hydra
  | 0 => h
  | k + 1 => canonStep (t + k) (runFrom h t k)

theorem battle_eq_runFrom (h : Hydra) : ∀ k, battle h k = runFrom h 0 k
  | 0 => rfl
  | k + 1 => by simp [battle, runFrom, battle_eq_runFrom h k]

theorem runFrom_succ (h : Hydra) (t : ℕ) :
    ∀ k, runFrom h t (k + 1) = runFrom (canonStep t h) (t + 1) k
  | 0 => rfl
  | k + 1 => by
    rw [runFrom, runFrom_succ h t k, runFrom]
    congr 1
    omega

/-- **P2.**  Started at turn `t`, the canonical battle is alive at every step `k` with
`t + k < hardy (ord h) t`. -/
theorem runFrom_alive_of_lt_hardy :
    ∀ (h : Hydra) (t k : ℕ), t + k < hardy (ord h) t → runFrom h t k ≠ Hydra.leaf := by
  suffices H : ∀ (o : Ordinal) (h : Hydra), ONote.repr (ord h) = o →
      ∀ t k, t + k < hardy (ord h) t → runFrom h t k ≠ Hydra.leaf from
    fun h t k => H _ h rfl t k
  intro o
  induction o using WellFoundedLT.induction with
  | ind o ih =>
    intro h hoh t k hlt
    by_cases hl : h = Hydra.leaf
    · subst hl
      rw [show ord Hydra.leaf = 0 from ord_leaf, hardy_zero] at hlt
      simp at hlt
    · cases k with
      | zero => exact hl
      | succ k =>
        rw [runFrom_succ]
        have hNF : (ord h).NF := ord_NF h
        have hprop := fundamentalSequence_has_prop (ord h)
        rcases ord_canonStep t h hl with hs | ⟨f, hf, hfn⟩
        · rw [hs] at hprop
          rw [hardy_succ _ hs] at hlt
          refine ih _ ?_ _ rfl (t + 1) k (by simp only at hlt; omega)
          rw [← hoh, hprop.1]
          exact Order.lt_succ _
        · rw [hf] at hprop
          rw [hardy_limit _ hf] at hlt
          have hmono := hardy_le_succ (f t) t
          refine ih _ ?_ _ rfl (t + 1) k ?_
          · rw [← hoh, hfn]
            exact lt_def.mp (hprop.2.1 t).2.1
          · rw [hfn]
            simp only at hlt
            omega

end GoodsteinPA.Hydra

end
