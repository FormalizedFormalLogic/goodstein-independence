/-
# ONote — Hardy vs. fast-growing hierarchy (entry point)

Two-sided comparison of `hardy` at `ω`-powers against `fastGrowing`, up to the tower diagonal.
-/
module

public import GoodsteinPA.ToMathlib.Hardy.Structure

@[expose] public section

namespace ONote

open ONote Ordinal

instance : WellFoundedLT ONote := InvImage.wf repr Ordinal.lt_wf

/-- Leading exponent of a notation's Cantor normal form (`0` for `0`). Companion to
`lastExp`; used to build a single `ω^Q` notation dominating a given `a`. -/
def lead : ONote → ONote
  | 0 => 0
  | oadd e _ _ => e

@[grind →]
lemma lead_NF {o : ONote} (ho : o.NF) : (lead o).NF := by
  cases o with
  | zero => exact NF.zero
  | oadd e n a => exact ho.fst

/-- A notation is below `ω^(E+1)` whenever its leading exponent is `≤ E`. The basic
domination brick: any `a` sits below `ω^(osucc (lead a))`. -/
lemma repr_lt_omega_opow_succ {o E : ONote} (ho : o.NF) (hle : (lead o).repr ≤ E.repr) : o.repr < ω ^ (E.repr + 1) := by
  cases o with
  | zero => show (0 : ONote).repr < ω ^ (E.repr + 1); rw [repr_zero]; exact opow_pos _ omega0_pos
  | oadd e' c R =>
    have hle' : e'.repr ≤ E.repr := hle
    have hb : NFBelow (oadd e' c R) (e'.repr + 1) := ho.below_of_lt (lt_add_one _)
    refine lt_of_lt_of_le hb.repr_lt (opow_le_opow_right omega0_pos ?_)
    rw [← Order.succ_eq_add_one, ← Order.succ_eq_add_one]
    exact Order.succ_le_succ hle'

/-- Iterate-offset transfer: if `g y + 1 = F (y+1)` for all `y`, then `g^[m] y + 1 = F^[m] (y+1)`. -/
lemma iterate_offset {g F : ℕ → ℕ} (h : ∀ y, g y + 1 = F (y + 1)) (m y : ℕ) : g^[m] y + 1 = F^[m] (y + 1) := by
  induction m generalizing y with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih (g y), h y]

private lemma ofNat_succ_ne_zero (k : ℕ) : (ofNat (k + 1) : ONote) ≠ 0 := by
  rw [ofNat_succ]; intro h; exact ONote.noConfusion h

private lemma hardy_omega_pow_ofNat_succ (k x : ℕ) :
    hardy (oadd (ofNat (k + 1)) 1 0) x + 1 = fastGrowing (ofNat (k + 1)) (x + 1) := by
  induction k generalizing x with
  | zero =>
    show hardy (oadd 1 1 0) x + 1 = fastGrowing 1 (x + 1)
    rw [hardy_omega, fastGrowing_one]
    show 2 * x + 1 + 1 = 2 * (x + 1)
    omega
  | succ k ih =>
    rw [fastGrowing_succ _ (fundamentalSequence_ofNat_succ (k + 1)),
        hardy_limit _ (fundamentalSequence_omega_pow_succ (fundamentalSequence_ofNat_succ (k + 1)))]
    show hardy (oadd (ofNat (k + 1)) x.succPNat 0) x + 1
        = (fastGrowing (ofNat (k + 1)))^[x + 1] (x + 1)
    rw [hardy_oadd_coeff (ofNat (k + 1)) (ofNat_succ_ne_zero k) x x]
    exact iterate_offset ih (x + 1) x

/-- **The Hardy/fast-growing identity at finite levels:** `H_{ω^k}(n) + 1 = f_k(n+1)` for every `k : ℕ`. -/
lemma hardy_omega_pow_ofNat (k x : ℕ) : hardy (oadd (ofNat k) 1 0) x + 1 = fastGrowing (ofNat k) (x + 1) := by
  cases k with
  | zero =>
    show hardy (oadd 0 1 0) x + 1 = fastGrowing 0 (x + 1)
    rw [show (oadd 0 1 0 : ONote) = 1 from rfl, hardy_one, fastGrowing_zero]
  | succ k => exact hardy_omega_pow_ofNat_succ k x

/-- **The Hardy/fast-growing identity at the first limit level `ω^ω`:** `H_{ω^ω}(n) + 1 = f_{n+1}(n+1)`. -/
lemma hardy_omega_pow_omega (n : ℕ) : hardy (oadd (oadd 1 1 0) 1 0) n + 1 = fastGrowing (ofNat (n + 1)) (n + 1) := by
  have hω : fundamentalSequence (oadd 1 1 0) = Sum.inr (fun i => ONote.ofNat (i + 1)) := rfl
  rw [hardy_limit _ (fundamentalSequence_omega_pow_limit hω)]
  show hardy (oadd (ofNat (n + 1)) 1 0) n + 1 = fastGrowing (ofNat (n + 1)) (n + 1)
  exact hardy_omega_pow_ofNat (n + 1) n

/-- Anti-vacuity for `hardy_le_fastGrowing` at a genuine limit: `H_ω(2) = 5 ≤ f_ω(2) = 2048`. -/
example : hardy (oadd 1 1 0) 2 ≤ fastGrowing (oadd 1 1 0) 2 := hardy_le_fastGrowing _ _ (by norm_num)

/-! ### Hardy vs. fast-growing at an arbitrary exponent

At arbitrary `a : ONote`, `H_{ω^a}(n) + 1 ≤ f_a(n+1)` unconditionally.
-/

/-- **Coefficient composition:** `H_{ω^b·(k+2)}(n) = H_{ω^b·(k+1)}(H_{ω^b}(n))`, unconditional in `b`. -/
lemma hardy_omega_pow_coeff_comp (b : ONote) (k n : ℕ) :
    hardy (oadd b (Nat.succPNat (k + 1)) 0) n
      = hardy (oadd b (Nat.succPNat k) 0) (hardy (oadd b 1 0) n) := by
  rcases eq_or_ne b 0 with hb | hb
  · subst hb
    have e1 : oadd (0 : ONote) (Nat.succPNat (k + 1)) 0 = ofNat (k + 2) := (ofNat_succ (k + 1)).symm
    have e2 : oadd (0 : ONote) (Nat.succPNat k) 0 = ofNat (k + 1) := (ofNat_succ k).symm
    have e3 : oadd (0 : ONote) 1 0 = ofNat 1 := (ofNat_succ 0).symm
    rw [e1, e2, e3]
    simp only [hardy_ofNat]
    omega
  · exact hardy_oadd_coeff_step b hb k n

/-- **The coefficient intermediate:** `H_{ω^b·(m+1)}(n) + 1 ≤ f_b^{[m+1]}(n+1)`. -/
lemma hardy_omega_pow_coeff_le {b : ONote}
    (hbase : ∀ n, hardy (oadd b 1 0) n + 1 ≤ fastGrowing b (n + 1)) (m n : ℕ) :
    hardy (oadd b (Nat.succPNat m) 0) n + 1 ≤ (fastGrowing b)^[m + 1] (n + 1) := by
  induction m generalizing n with
  | zero =>
      show hardy (oadd b 1 0) n + 1 ≤ fastGrowing b (n + 1)
      exact hbase n
  | succ m ih =>
      rw [hardy_omega_pow_coeff_comp b m n]
      have h2 : hardy (oadd b 1 0) n + 1 ≤ fastGrowing b (n + 1) := hbase n
      calc hardy (oadd b (Nat.succPNat m) 0) (hardy (oadd b 1 0) n) + 1
          ≤ (fastGrowing b)^[m + 1] (hardy (oadd b 1 0) n + 1) := ih _
        _ ≤ (fastGrowing b)^[m + 1] (fastGrowing b (n + 1)) :=
            (fastGrowing_monotone b).iterate (m + 1) h2
        _ = (fastGrowing b)^[m + 1 + 1] (n + 1) :=
            (Function.iterate_succ_apply (fastGrowing b) (m + 1) (n + 1)).symm

section
variable (a : ONote) (n : ℕ)

-- anti-vacuity at a genuine LIMIT exponent (where the bare equality is false):
-- `H_{ω^ω}(1) = 7 < f_ω(2)`.
example : hardy (oadd (oadd 1 1 0) 1 0) 1 < fastGrowing (oadd 1 1 0) 2 :=
  hardy_omega_pow_lt_fastGrowing (oadd 1 1 0) 1

/-- Pointwise domination lifts to iterates: `F ≤ g` pointwise and `g` monotone ⟹ `F^[m] ≤ g^[m]`. -/
private lemma iterate_le_iterate_of_le {F g : ℕ → ℕ} (hFg : ∀ y, F y ≤ g y)
    (hg : Monotone g) (m x : ℕ) : F^[m] x ≤ g^[m] x := by
  induction m generalizing x with
  | zero => exact le_rfl
  | succ m ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
      exact le_trans (ih (F x)) (hg.iterate m (hFg x))

/-- Inequality iterate-offset: if `g y + 1 ≤ F (y+1)` for all `y` and `F` is monotone, the `+1`
carries through the iteration one extra argument step: `g^[m] y + 1 ≤ F^[m] (y+1)`. The `≤`
generalization of `iterate_offset` (which needs the exact equality). -/
private lemma iterate_offset_le {g F : ℕ → ℕ} (hF : Monotone F) (h : ∀ y, g y + 1 ≤ F (y + 1))
    (m y : ℕ) : g^[m] y + 1 ≤ F^[m] (y + 1) := by
  induction m generalizing y with
  | zero => exact le_rfl
  | succ m ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
      exact le_trans (ih (g y)) (hF.iterate m (h y))

/-! ### The ε₀-diagonal capstone

`fastGrowingε₀ i = f_{tower i}(i)` and `tower (i+1) = ω^{tower i}` (`tower_succ`), so the `ω^a`
bracket at `a = tower i`, argument `i`, pins the ε₀-diagonal against the Hardy function at the next
tower level. This is the `ε₀`-tier reading of the E–W Lemma 19 comparison — the level at which the
Goodstein length function itself lives (`goodsteinLength` tracks `H_{ε₀}`). -/

end

end ONote
