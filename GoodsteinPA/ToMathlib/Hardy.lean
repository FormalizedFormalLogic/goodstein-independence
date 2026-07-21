/-
# ONote — Hardy vs. fast-growing hierarchy (entry point)

Two-sided comparison of `hardy` at `ω`-powers against `fastGrowing`, up to the tower diagonal.
-/
module

public import GoodsteinPA.ToMathlib.Hardy.Structure

@[expose] public section

namespace ONote

open ONote Ordinal

instance : WellFoundedLT ONote := ⟨InvImage.wf repr Ordinal.lt_wf⟩

/-- Leading exponent of a notation's Cantor normal form (`0` for `0`). Companion to
`lastExp`; used to build a single `ω^Q` notation dominating a given `α`. -/
def lead : ONote → ONote
  | 0 => 0
  | oadd e _ _ => e

lemma lead_NF {o : ONote} (ho : o.NF) : (lead o).NF := by
  cases o with
  | zero => exact NF.zero
  | oadd e n a => exact ho.fst

/-- A notation is below `ω^(E+1)` whenever its leading exponent is `≤ E`. The basic
domination brick: any `α` sits below `ω^(osucc (lead α))`. -/
lemma repr_lt_omega_opow_succ {o E : ONote} (ho : o.NF) (hle : (lead o).repr ≤ E.repr) :
    o.repr < ω ^ (E.repr + 1) := by
  cases o with
  | zero => show (0 : ONote).repr < ω ^ (E.repr + 1); rw [repr_zero]; exact opow_pos _ omega0_pos
  | oadd e' c R =>
    have hle' : e'.repr ≤ E.repr := hle
    have hb : NFBelow (oadd e' c R) (e'.repr + 1) := ho.below_of_lt (lt_add_one _)
    refine lt_of_lt_of_le hb.repr_lt (opow_le_opow_right omega0_pos ?_)
    rw [← Order.succ_eq_add_one, ← Order.succ_eq_add_one]
    exact Order.succ_le_succ hle'

/-- Iterate-offset transfer: if `g y + 1 = F (y+1)` for all `y`, then `g^[m] y + 1 = F^[m] (y+1)`. -/
lemma iterate_offset {g F : ℕ → ℕ} (h : ∀ y, g y + 1 = F (y + 1)) (m y : ℕ) :
    g^[m] y + 1 = F^[m] (y + 1) := by
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
lemma hardy_omega_pow_ofNat (k x : ℕ) :
    hardy (oadd (ofNat k) 1 0) x + 1 = fastGrowing (ofNat k) (x + 1) := by
  cases k with
  | zero =>
    show hardy (oadd 0 1 0) x + 1 = fastGrowing 0 (x + 1)
    rw [show (oadd 0 1 0 : ONote) = 1 from rfl, hardy_one, fastGrowing_zero]
  | succ k => exact hardy_omega_pow_ofNat_succ k x

/-- **The Hardy/fast-growing identity at the first limit level `ω^ω`:**
`H_{ω^ω}(n) + 1 = f_{n+1}(n+1)`. -/
lemma hardy_omega_pow_omega (n : ℕ) :
    hardy (oadd (oadd 1 1 0) 1 0) n + 1 = fastGrowing (ofNat (n + 1)) (n + 1) := by
  have hω : fundamentalSequence (oadd 1 1 0) = Sum.inr (fun i => ONote.ofNat (i + 1)) := rfl
  rw [hardy_limit _ (fundamentalSequence_omega_pow_limit hω)]
  show hardy (oadd (ofNat (n + 1)) 1 0) n + 1 = fastGrowing (ofNat (n + 1)) (n + 1)
  exact hardy_omega_pow_ofNat (n + 1) n

/-- **Hardy is dominated by fast-growing at the same index:** For `n ≥ 2`, `hardy o n ≤ fastGrowing o n`. -/
theorem hardy_le_fastGrowing (o : ONote) (n : ℕ) (hn : 2 ≤ n) :
    hardy o n ≤ fastGrowing o n := by
  rcases e : fundamentalSequence o with (_ | a) | f
  · rw [hardy_zero' o e, fastGrowing_zero' o e]; simp
  · have hlt : a < o := lt_of_fundamentalSequence_inl_some e
    rw [hardy_succ o e, fastGrowing_succ o e]
    have ih : hardy a (n + 1) ≤ fastGrowing a (n + 1) := hardy_le_fastGrowing a (n + 1) (by omega)
    have hexp : (id : ℕ → ℕ) ≤ fastGrowing a := fun m => le_fastGrowing a m
    have hmono : (fastGrowing a)^[2] n ≤ (fastGrowing a)^[n] n :=
      Function.monotone_iterate_of_id_le hexp hn n
    have h2it : (fastGrowing a)^[2] n = fastGrowing a (fastGrowing a n) := by
      rw [show (2 : ℕ) = 1 + 1 from rfl, Function.iterate_add_apply]; simp
    have hfn : n + 1 ≤ fastGrowing a n := lt_fastGrowing a (by omega)
    have hstep : fastGrowing a (n + 1) ≤ fastGrowing a (fastGrowing a n) := fastGrowing_monotone a hfn
    calc hardy a (n + 1) ≤ fastGrowing a (n + 1) := ih
      _ ≤ fastGrowing a (fastGrowing a n) := hstep
      _ = (fastGrowing a)^[2] n := h2it.symm
      _ ≤ (fastGrowing a)^[n] n := hmono
  · have hlt : f n < o := fundamentalSequence_inr_lt e n
    rw [hardy_limit o e, fastGrowing_limit o e]
    exact hardy_le_fastGrowing (f n) n hn
termination_by o
decreasing_by all_goals exact hlt

/-- Anti-vacuity for `hardy_le_fastGrowing` at a genuine limit: `H_ω(2) = 5 ≤ f_ω(2) = 2048`. -/
example : hardy (oadd 1 1 0) 2 ≤ fastGrowing (oadd 1 1 0) 2 := hardy_le_fastGrowing _ _ (by norm_num)

/-! ### Hardy vs. fast-growing at an arbitrary exponent

At arbitrary `α : ONote`, `H_{ω^α}(n) + 1 ≤ f_α(n+1)` unconditionally.
-/

/-- **Coefficient composition:** `H_{ω^β·(k+2)}(n) = H_{ω^β·(k+1)}(H_{ω^β}(n))`, unconditional in `β`. -/
lemma hardy_omega_pow_coeff_comp (β : ONote) (k n : ℕ) :
    hardy (oadd β (Nat.succPNat (k + 1)) 0) n
      = hardy (oadd β (Nat.succPNat k) 0) (hardy (oadd β 1 0) n) := by
  rcases eq_or_ne β 0 with hβ | hβ
  · subst hβ
    have e1 : oadd (0 : ONote) (Nat.succPNat (k + 1)) 0 = ofNat (k + 2) := (ofNat_succ (k + 1)).symm
    have e2 : oadd (0 : ONote) (Nat.succPNat k) 0 = ofNat (k + 1) := (ofNat_succ k).symm
    have e3 : oadd (0 : ONote) 1 0 = ofNat 1 := (ofNat_succ 0).symm
    rw [e1, e2, e3]
    simp only [hardy_ofNat]
    omega
  · exact hardy_oadd_coeff_step β hβ k n

/-- **The coefficient intermediate:** `H_{ω^β·(m+1)}(n) + 1 ≤ f_β^{[m+1]}(n+1)`. -/
lemma hardy_omega_pow_coeff_le {β : ONote}
    (hbase : ∀ n, hardy (oadd β 1 0) n + 1 ≤ fastGrowing β (n + 1)) :
    ∀ (m n : ℕ), hardy (oadd β (Nat.succPNat m) 0) n + 1 ≤ (fastGrowing β)^[m + 1] (n + 1) := by
  intro m
  induction m with
  | zero =>
      intro n
      show hardy (oadd β 1 0) n + 1 ≤ fastGrowing β (n + 1)
      exact hbase n
  | succ m ih =>
      intro n
      rw [hardy_omega_pow_coeff_comp β m n]
      have h2 : hardy (oadd β 1 0) n + 1 ≤ fastGrowing β (n + 1) := hbase n
      calc hardy (oadd β (Nat.succPNat m) 0) (hardy (oadd β 1 0) n) + 1
          ≤ (fastGrowing β)^[m + 1] (hardy (oadd β 1 0) n + 1) := ih _
        _ ≤ (fastGrowing β)^[m + 1] (fastGrowing β (n + 1)) :=
            (fastGrowing_monotone β).iterate (m + 1) h2
        _ = (fastGrowing β)^[m + 1 + 1] (n + 1) :=
            (Function.iterate_succ_apply (fastGrowing β) (m + 1) (n + 1)).symm

/-- **Hardy/fast-growing upper bound at an arbitrary exponent:** `H_{ω^α}(n) + 1 ≤ f_α(n+1)`. -/
theorem hardy_omega_pow_add_one_le (α : ONote) (n : ℕ) :
    hardy (oadd α 1 0) n + 1 ≤ fastGrowing α (n + 1) := by
  induction α using WellFoundedLT.induction generalizing n with
  | _ α ih =>
    rcases hα : fundamentalSequence α with (_ | β) | f
    · have h0 : α = 0 := eq_zero_of_fundamentalSequence_inl_none hα
      subst h0
      have hfs1 : fundamentalSequence (oadd 0 1 0) = Sum.inl (some 0) := rfl
      rw [hardy_succ (oadd 0 1 0) hfs1, hardy_zero, fastGrowing_zero]
      simp only [id_eq]; omega
    · have hlt : β < α := lt_of_fundamentalSequence_inl_some hα
      have homega : fundamentalSequence (oadd α 1 0) = Sum.inr (fun i => oadd β i.succPNat 0) :=
        fundamentalSequence_omega_pow_succ hα
      rw [hardy_limit (oadd α 1 0) homega, fastGrowing_succ α hα]
      exact hardy_omega_pow_coeff_le (ih β hlt) n n
    · have hlim_h : fundamentalSequence (oadd α 1 0) = Sum.inr (fun i => oadd (f i) 1 0) :=
        fundamentalSequence_omega_pow_limit hα
      have hlt : f n < α := fundamentalSequence_inr_lt hα n
      rw [hardy_limit (oadd α 1 0) hlim_h, fastGrowing_limit α hα]
      calc hardy (oadd (f n) 1 0) n + 1
          ≤ fastGrowing (f n) (n + 1) := ih (f n) hlt n
        _ ≤ fastGrowing (f (n + 1)) (n + 1) :=
            fastGrowing_le_of_reaches (Nat.succ_le_succ (Nat.zero_le n))
              (fastGrowing_bachmann_reach hα n)

/-- **The strict form:** `H_{ω^α}(n) < f_α(n+1)`, from the `+1 ≤` form. -/
theorem hardy_omega_pow_lt_fastGrowing (α : ONote) (n : ℕ) :
    hardy (oadd α 1 0) n < fastGrowing α (n + 1) := by
  have h := hardy_omega_pow_add_one_le α n
  omega

-- anti-vacuity at a genuine LIMIT exponent (where the bare equality is false): `H_{ω^ω}(1) = 7 < f_ω(2)`.
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

/-- **The matching lower bound at an arbitrary exponent:** `f_α(n) ≤ H_{ω^α}(n)`. -/
theorem fastGrowing_le_hardy_omega_pow (α : ONote) (n : ℕ) :
    fastGrowing α n ≤ hardy (oadd α 1 0) n := by
  induction α using WellFoundedLT.induction generalizing n with
  | _ α ih =>
    rcases hα : fundamentalSequence α with (_ | β) | f
    · have h0 : α = 0 := eq_zero_of_fundamentalSequence_inl_none hα
      subst h0
      have hfs1 : fundamentalSequence (oadd 0 1 0) = Sum.inl (some 0) := rfl
      rw [fastGrowing_zero, hardy_succ (oadd 0 1 0) hfs1, hardy_zero]
      simp only [id_eq]; omega
    · have hlt : β < α := lt_of_fundamentalSequence_inl_some hα
      have homega : fundamentalSequence (oadd α 1 0) = Sum.inr (fun i => oadd β i.succPNat 0) :=
        fundamentalSequence_omega_pow_succ hα
      rw [fastGrowing_succ α hα, hardy_limit (oadd α 1 0) homega]
      show (fastGrowing β)^[n] n ≤ hardy (oadd β n.succPNat 0) n
      rcases eq_or_ne β 0 with hβ0 | hβ0
      · subst hβ0
        rw [fastGrowing_zero, show oadd (0 : ONote) n.succPNat 0 = ofNat (n + 1) from (ofNat_succ n).symm,
          hardy_ofNat, Nat.succ_iterate]
        omega
      · rw [hardy_oadd_coeff β hβ0 n n]
        have hFg : ∀ y, fastGrowing β y ≤ hardy (oadd β 1 0) y := ih β hlt
        have hg : Monotone (hardy (oadd β 1 0)) := hardy_monotone _
        calc (fastGrowing β)^[n] n
            ≤ (hardy (oadd β 1 0))^[n] n := iterate_le_iterate_of_le hFg hg n n
          _ ≤ (hardy (oadd β 1 0))^[n + 1] n := by
              rw [Function.iterate_succ_apply']; exact le_hardy (oadd β 1 0) _
    · have hlim : fundamentalSequence (oadd α 1 0) = Sum.inr (fun i => oadd (f i) 1 0) :=
        fundamentalSequence_omega_pow_limit hα
      have hlt : f n < α := fundamentalSequence_inr_lt hα n
      rw [fastGrowing_limit α hα, hardy_limit (oadd α 1 0) hlim]
      exact ih (f n) hlt n

/-- **The two-sided bracket at `ω^α`:** `f_α(n) ≤ H_{ω^α}(n) < f_α(n+1)`, unconditional. -/
theorem hardy_omega_pow_bracket (α : ONote) (n : ℕ) :
    fastGrowing α n ≤ hardy (oadd α 1 0) n ∧ hardy (oadd α 1 0) n < fastGrowing α (n + 1) :=
  ⟨fastGrowing_le_hardy_omega_pow α n, hardy_omega_pow_lt_fastGrowing α n⟩

/-- **Coefficient-general lower bound:** `(f_α)^[k+1](n) ≤ H_{ω^α·(k+1)}(n)` for `α ≠ 0`. -/
theorem fastGrowing_iterate_le_hardy_coeff (α : ONote) (hα : α ≠ 0) (k n : ℕ) :
    (fastGrowing α)^[k + 1] n ≤ hardy (oadd α k.succPNat 0) n := by
  rw [hardy_oadd_coeff α hα k n]
  exact iterate_le_iterate_of_le (fastGrowing_le_hardy_omega_pow α) (hardy_monotone _) (k + 1) n

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

/-- **Coefficient-general upper bound:** `H_{ω^α·(k+1)}(n) + 1 ≤ (f_α)^[k+1](n+1)` for `α ≠ 0`. -/
theorem hardy_coeff_add_one_le (α : ONote) (hα : α ≠ 0) (k n : ℕ) :
    hardy (oadd α k.succPNat 0) n + 1 ≤ (fastGrowing α)^[k + 1] (n + 1) := by
  rw [hardy_oadd_coeff α hα k n]
  exact iterate_offset_le (fastGrowing_monotone α) (hardy_omega_pow_add_one_le α) (k + 1) n

/-- **The coefficient-general two-sided bracket:** `(f_α)^[k+1](n) ≤ H_{ω^α·(k+1)}(n) < (f_α)^[k+1](n+1)` for `α ≠ 0`. -/
theorem hardy_omega_pow_coeff_bracket (α : ONote) (hα : α ≠ 0) (k n : ℕ) :
    (fastGrowing α)^[k + 1] n ≤ hardy (oadd α k.succPNat 0) n
      ∧ hardy (oadd α k.succPNat 0) n < (fastGrowing α)^[k + 1] (n + 1) :=
  ⟨fastGrowing_iterate_le_hardy_coeff α hα k n,
    Nat.lt_of_succ_le (hardy_coeff_add_one_le α hα k n)⟩

/-! ### The ε₀-diagonal capstone

`fastGrowingε₀ i = f_{tower i}(i)` and `tower (i+1) = ω^{tower i}` (`tower_succ`), so the `ω^α`
bracket at `α = tower i`, argument `i`, pins the ε₀-diagonal against the Hardy function at the next
tower level. This is the `ε₀`-tier reading of the E–W Lemma 19 comparison — the level at which the
Goodstein length function itself lives (`goodsteinLength` tracks `H_{ε₀}`). -/

/-- **The ε₀ diagonal is dominated by Hardy at the tower:** `fastGrowingε₀ i ≤ H_{tower(i+1)}(i)`. -/
theorem fastGrowingε₀_le_hardy_tower_succ (i : ℕ) :
    fastGrowingε₀ i ≤ hardy (tower (i + 1)) i := by
  have h : fastGrowing (tower i) i ≤ hardy (oadd (tower i) 1 0) i :=
    (hardy_omega_pow_bracket (tower i) i).1
  rw [← tower_succ] at h
  exact h

/-- **The matching ε₀-diagonal upper bound:** `H_{tower(i+1)}(i) < f_{tower i}(i+1)`. -/
theorem hardy_tower_succ_lt_fastGrowing (i : ℕ) :
    hardy (tower (i + 1)) i < fastGrowing (tower i) (i + 1) := by
  have h := (hardy_omega_pow_bracket (tower i) i).2
  rw [← tower_succ] at h
  exact h

end ONote
