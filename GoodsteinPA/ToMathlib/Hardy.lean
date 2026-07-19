/-
# ONote — Hardy vs. fast-growing hierarchy (entry point)

Two-sided comparison of `hardy` at `ω`-powers against `fastGrowing`, up to the tower diagonal.
-/
module

public import GoodsteinPA.ToMathlib.Hardy.Structure

@[expose] public section

namespace ONote

open ONote Ordinal

/-- Leading exponent of a notation's Cantor normal form (`0` for `0`). Companion to
`lastExp`; used to build a single `ω^Q` notation dominating a given `α`. -/
def lead : ONote → ONote
  | 0 => 0
  | oadd e _ _ => e

theorem lead_NF {o : ONote} (ho : o.NF) : (lead o).NF := by
  cases o with
  | zero => exact NF.zero
  | oadd e n a => exact ho.fst

/-- A notation is below `ω^(E+1)` whenever its leading exponent is `≤ E`. The basic
domination brick: any `α` sits below `ω^(osucc (lead α))`. -/
theorem repr_lt_omega_opow_succ {o E : ONote} (ho : o.NF) (hle : (lead o).repr ≤ E.repr) :
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
theorem iterate_offset {g F : ℕ → ℕ} (h : ∀ y, g y + 1 = F (y + 1)) (m y : ℕ) :
    g^[m] y + 1 = F^[m] (y + 1) := by
  induction m generalizing y with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih (g y), h y]

private theorem ofNat_succ_ne_zero (k : ℕ) : (ofNat (k + 1) : ONote) ≠ 0 := by
  rw [ofNat_succ]; intro h; exact ONote.noConfusion h

private theorem hardy_omega_pow_ofNat_succ (k x : ℕ) :
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

/-- **B4 at finite levels: `H_{ω^k}(n) + 1 = f_k(n+1)`** for every `k : ℕ`. The classical Hardy↔
fast-growing identity `H_{ω^α} = f_α`, made precise under mathlib's `ω[n]=n+1` fundamental-sequence
convention — which shifts it by the `+1`/argument-bump seen here. (NB: the clean identity is special to
*finite/successor* exponents; at limit `α` the convention makes `H_{ω^α}` and `f_α` pick different
levels — e.g. `H_{ω^ω}(1)+1 = 8 ≠ f_ω(2) = 2048`.) Proof: induction on `k` from the `ω` base
(`hardy_omega`), the coefficient lemma turning `(ω^{k+1})[x] = ω^k·(x+1)` into `(H_{ω^k})^[x+1]`, and
`iterate_offset` carrying the `+1` through the iteration against `f_{k+1} = (f_k)^[·]`. -/
theorem hardy_omega_pow_ofNat (k x : ℕ) :
    hardy (oadd (ofNat k) 1 0) x + 1 = fastGrowing (ofNat k) (x + 1) := by
  cases k with
  | zero =>
    show hardy (oadd 0 1 0) x + 1 = fastGrowing 0 (x + 1)
    rw [show (oadd 0 1 0 : ONote) = 1 from rfl, hardy_one, fastGrowing_zero]
  | succ k => exact hardy_omega_pow_ofNat_succ k x

/-- **B4 at the first LIMIT level `ω^ω`:** `H_{ω^ω}(n) + 1 = f_{n+1}(n+1)`. Unlike finite `α`, the
clean `H_{ω^α}(n)+1 = f_α(n+1)` is FALSE at limit `α` (the `ω[n]=n+1` convention makes `H` and `f`
pick different tower levels); the TRUE limit form reads off the fundamental sequence:
`(ω^ω)[n] = ω^{n+1}`, so `H_{ω^ω}(n) = H_{ω^{n+1}}(n)` and finite B4 gives `f_{n+1}(n+1) − 1`. Note the
diagonal `n+1` argument — this is `f_{ε₀}`-flavoured (cf. `fastGrowingε₀`). Concrete witness that the
limit case is tractable with the right (non-`f_α(n+1)`) closed form. -/
theorem hardy_omega_pow_omega (n : ℕ) :
    hardy (oadd (oadd 1 1 0) 1 0) n + 1 = fastGrowing (ofNat (n + 1)) (n + 1) := by
  have hω : fundamentalSequence (oadd 1 1 0) = Sum.inr (fun i => ONote.ofNat (i + 1)) := rfl
  rw [hardy_limit _ (fundamentalSequence_omega_pow_limit hω)]
  show hardy (oadd (ofNat (n + 1)) 1 0) n + 1 = fastGrowing (ofNat (n + 1)) (n + 1)
  exact hardy_omega_pow_ofNat (n + 1) n

/-- **Hardy is dominated by fast-growing at the same index.** For `n ≥ 2`,
`hardy o n ≤ fastGrowing o n` (no `NF` needed). By well-founded recursion on the notation, mirroring
`le_fastGrowing`: the limit case is the IH verbatim; the successor case chains
`H_o(n) = H_a(n+1) ≤ f_a(n+1) ≤ f_a(f_a n) = (f_a)^[2] n ≤ (f_a)^[n] n = f_o(n)` (IH at `a`, then
`f_a` monotone via `n+1 ≤ f_a n` from `lt_fastGrowing`, then iterate-count monotone for `n ≥ 2`).

The two hierarchies the expedition built are comparable: the Hardy hierarchy (the Goodstein-length
side, via the Cichoń identity `goodsteinLength m = H_{o_m}(2) − 2`) never outruns the fast-growing
hierarchy at the same ordinal index. A reusable bridge toward the matching *upper* bound and `B4`. -/
theorem hardy_le_fastGrowing (o : ONote) (n : ℕ) (hn : 2 ≤ n) :
    hardy o n ≤ fastGrowing o n := by
  rcases e : fundamentalSequence o with (_ | a) | f
  · rw [hardy_zero' o e, fastGrowing_zero' o e]; simp
  · have hlt : a < o := by
      have hp := fundamentalSequence_has_prop o; rw [e] at hp
      rw [lt_def, hp.1]; exact Order.lt_succ _
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
  · have hlt : f n < o := by
      have hp := fundamentalSequence_has_prop o; rw [e] at hp
      exact (hp.2.1 n).2.1
    rw [hardy_limit o e, fastGrowing_limit o e]
    exact hardy_le_fastGrowing (f n) n hn
termination_by o
decreasing_by all_goals exact hlt

/-- Anti-vacuity for `hardy_le_fastGrowing` at a genuine limit: `H_ω(2) = 5 ≤ f_ω(2) = 2048`. -/
example : hardy (oadd 1 1 0) 2 ≤ fastGrowing (oadd 1 1 0) 2 := hardy_le_fastGrowing _ _ (by norm_num)

/-! ### B4 at an ARBITRARY (transfinite) exponent — the unconditional inequality `H_{ω^α}(n)+1 ≤ f_α(n+1)`

`hardy_omega_pow_ofNat`/`_omega` above give B4 as an *equality* at finite/successor exponents; at a
LIMIT exponent the equality degrades (the `ω[n]=n+1` convention makes `H` and `f` pick different
tower levels — e.g. `H_{ω^ω}(1)+1 = 8 ≠ f_ω(2) = 2048`). The UNCONDITIONAL, load-bearing truth,
proven here for *every* `α : ONote` by well-founded recursion, is the **inequality**

    hardy (oadd α 1 0) n + 1 ≤ fastGrowing α (n + 1)              -- H_{ω^α}(n) < f_α(n+1)

— exactly the E–W Lemma 19 upper bound the raised-control (P1) obligation needs: with the cut-elim
`raise e α' = e + ω^{α'}` in the absorbing regime, the raised control is `≈ hardy (ω^{α'})`, so this
bound reduces P1 to the fast-growing domination `fastGrowing α' ≤ (iterate of the input slot)`.
Pure Hardy/`fastGrowing` growth theory about the stable defs — calculus-independent. -/

/-- **Coefficient composition, unconditional in `β`** (the non-absorbing equal-exponent additive
core): `H_{ω^β·(k+2)}(n) = H_{ω^β·(k+1)}(H_{ω^β}(n))`. For `β ≠ 0` this is the banked
`hardy_oadd_coeff_step`; for `β = 0` everything is finite (`oadd 0 m.succPNat 0 = ofNat (m+1)`,
`H_{ofNat c}(x) = x + c`). -/
theorem hardy_omega_pow_coeff_comp (β : ONote) (k n : ℕ) :
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

/-- **The coefficient intermediate** (the classical Cichoń–Wainer core), parametrized by the
exponent-`β` base bound `hbase` (supplied by the outer IH in the successor case):
`H_{ω^β·(m+1)}(n) + 1 ≤ f_β^{[m+1]}(n+1)`. Induction on the coefficient `m`: base `m=0` is `hbase`;
the step composes via `hardy_omega_pow_coeff_comp` + the IH + iterate-monotonicity. -/
theorem hardy_omega_pow_coeff_le {β : ONote}
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

/-- **B4 upper bound at an arbitrary exponent `α`** — `H_{ω^α}(n) + 1 ≤ f_α(n+1)`, unconditional.
Well-founded recursion on `α`: `α = 0` is the equality; `α` a successor exponent reduces to the
coefficient intermediate `hardy_omega_pow_coeff_le` at the IH; `α` a limit uses the IH plus
`fastGrowing` index-monotonicity across the fundamental sequence. -/
theorem hardy_omega_pow_add_one_le (α : ONote) : ∀ n : ℕ,
    hardy (oadd α 1 0) n + 1 ≤ fastGrowing α (n + 1) := by
  haveI : WellFoundedLT ONote := ⟨InvImage.wf repr Ordinal.lt_wf⟩
  induction α using WellFoundedLT.induction with
  | _ α ih =>
    intro n
    rcases hα : fundamentalSequence α with (_ | β) | f
    · have h0 : α = 0 := by
        have hp := fundamentalSequence_has_prop α; rw [hα] at hp; exact hp
      subst h0
      have hfs1 : fundamentalSequence (oadd 0 1 0) = Sum.inl (some 0) := rfl
      rw [hardy_succ (oadd 0 1 0) hfs1, hardy_zero, fastGrowing_zero]
      simp only [id_eq]; omega
    · have hlt : β < α := by
        have hp := fundamentalSequence_has_prop α; rw [hα] at hp
        rw [lt_def, hp.1]; exact Order.lt_succ _
      have homega : fundamentalSequence (oadd α 1 0) = Sum.inr (fun i => oadd β i.succPNat 0) :=
        fundamentalSequence_omega_pow_succ hα
      rw [hardy_limit (oadd α 1 0) homega, fastGrowing_succ α hα]
      exact hardy_omega_pow_coeff_le (ih β hlt) n n
    · have hlim_h : fundamentalSequence (oadd α 1 0) = Sum.inr (fun i => oadd (f i) 1 0) :=
        fundamentalSequence_omega_pow_limit hα
      have hlt : f n < α := by
        have hp := fundamentalSequence_has_prop α; rw [hα] at hp; exact (hp.2.1 n).2.1
      rw [hardy_limit (oadd α 1 0) hlim_h, fastGrowing_limit α hα]
      calc hardy (oadd (f n) 1 0) n + 1
          ≤ fastGrowing (f n) (n + 1) := ih (f n) hlt n
        _ ≤ fastGrowing (f (n + 1)) (n + 1) :=
            fastGrowing_le_of_reaches (Nat.succ_le_succ (Nat.zero_le n))
              (fastGrowing_bachmann_reach hα n)

/-- **The P1 corollary:** `H_{ω^α}(n) < f_α(n+1)`, the strict upper bound the raised-control
obligation consumes, from the `+1 ≤` form. -/
theorem hardy_omega_pow_lt_fastGrowing (α : ONote) (n : ℕ) :
    hardy (oadd α 1 0) n < fastGrowing α (n + 1) := by
  have h := hardy_omega_pow_add_one_le α n
  omega

-- anti-vacuity at a genuine LIMIT exponent (where the bare equality is false): `H_{ω^ω}(1) = 7 < f_ω(2)`.
example : hardy (oadd (oadd 1 1 0) 1 0) 1 < fastGrowing (oadd 1 1 0) 2 :=
  hardy_omega_pow_lt_fastGrowing (oadd 1 1 0) 1

/-- Pointwise domination lifts to iterates: `F ≤ g` pointwise and `g` monotone ⟹ `F^[m] ≤ g^[m]`. -/
private theorem iterate_le_iterate_of_le {F g : ℕ → ℕ} (hFg : ∀ y, F y ≤ g y)
    (hg : Monotone g) (m x : ℕ) : F^[m] x ≤ g^[m] x := by
  induction m generalizing x with
  | zero => exact le_rfl
  | succ m ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
      exact le_trans (ih (F x)) (hg.iterate m (hFg x))

/-- **B4 LOWER bound at an arbitrary exponent `α`** — `f_α(n) ≤ H_{ω^α}(n)`, unconditional. The
matching *lower* half of `hardy_omega_pow_add_one_le`: together they bracket
`f_α(n) ≤ H_{ω^α}(n) < f_α(n+1)` (see `hardy_omega_pow_bracket`), the two-sided E–W Lemma 19
sandwich of the Hardy hierarchy by the fast-growing hierarchy at `ω^α`. Well-founded recursion on
`α`: `α = 0` is `n+1 = n+1`; `α` a limit is the IH verbatim (both sides pick index `α[n]` at
argument `n`); `α = β+1` reduces via `hardy_oadd_coeff` to the iterate domination
`(f_β)^[n](n) ≤ (H_{ω^β})^[n](n) ≤ (H_{ω^β})^[n+1](n)` (IH pointwise + `hardy_monotone` + `le_hardy`). -/
theorem fastGrowing_le_hardy_omega_pow (α : ONote) : ∀ n : ℕ,
    fastGrowing α n ≤ hardy (oadd α 1 0) n := by
  haveI : WellFoundedLT ONote := ⟨InvImage.wf repr Ordinal.lt_wf⟩
  induction α using WellFoundedLT.induction with
  | _ α ih =>
    intro n
    rcases hα : fundamentalSequence α with (_ | β) | f
    · have h0 : α = 0 := by
        have hp := fundamentalSequence_has_prop α; rw [hα] at hp; exact hp
      subst h0
      have hfs1 : fundamentalSequence (oadd 0 1 0) = Sum.inl (some 0) := rfl
      rw [fastGrowing_zero, hardy_succ (oadd 0 1 0) hfs1, hardy_zero]
      simp only [id_eq]; omega
    · have hlt : β < α := by
        have hp := fundamentalSequence_has_prop α; rw [hα] at hp
        rw [lt_def, hp.1]; exact Order.lt_succ _
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
      have hlt : f n < α := by
        have hp := fundamentalSequence_has_prop α; rw [hα] at hp; exact (hp.2.1 n).2.1
      rw [fastGrowing_limit α hα, hardy_limit (oadd α 1 0) hlim]
      exact ih (f n) hlt n

/-- **The two-sided E–W Lemma 19 bracket at `ω^α`:** `f_α(n) ≤ H_{ω^α}(n) < f_α(n+1)`, unconditional
over every `α : ONote`. The Hardy hierarchy is sandwiched between consecutive fast-growing values —
`H_{ω^α}` sits within one `f_α`-step of `f_α`. Combines `fastGrowing_le_hardy_omega_pow` (lower) and
`hardy_omega_pow_lt_fastGrowing` (upper). -/
theorem hardy_omega_pow_bracket (α : ONote) (n : ℕ) :
    fastGrowing α n ≤ hardy (oadd α 1 0) n ∧ hardy (oadd α 1 0) n < fastGrowing α (n + 1) :=
  ⟨fastGrowing_le_hardy_omega_pow α n, hardy_omega_pow_lt_fastGrowing α n⟩

/-- **Coefficient-general lower bound:** `(f_α)^[k+1](n) ≤ H_{ω^α·(k+1)}(n)` (for `α ≠ 0`).
The `hardy_oadd_coeff` companion of the `ω^α` lower bracket: `H_{ω^α·(k+1)} = (H_{ω^α})^[k+1]`
dominates `(f_α)^[k+1]` because `f_α ≤ H_{ω^α}` pointwise and `H_{ω^α}` is monotone. -/
theorem fastGrowing_iterate_le_hardy_coeff (α : ONote) (hα : α ≠ 0) (k n : ℕ) :
    (fastGrowing α)^[k + 1] n ≤ hardy (oadd α k.succPNat 0) n := by
  rw [hardy_oadd_coeff α hα k n]
  exact iterate_le_iterate_of_le (fastGrowing_le_hardy_omega_pow α) (hardy_monotone _) (k + 1) n

/-- Inequality iterate-offset: if `g y + 1 ≤ F (y+1)` for all `y` and `F` is monotone, the `+1`
carries through the iteration one extra argument step: `g^[m] y + 1 ≤ F^[m] (y+1)`. The `≤`
generalization of `iterate_offset` (which needs the exact equality). -/
private theorem iterate_offset_le {g F : ℕ → ℕ} (hF : Monotone F) (h : ∀ y, g y + 1 ≤ F (y + 1))
    (m y : ℕ) : g^[m] y + 1 ≤ F^[m] (y + 1) := by
  induction m generalizing y with
  | zero => exact le_rfl
  | succ m ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
      exact le_trans (ih (g y)) (hF.iterate m (h y))

/-- **Coefficient-general upper bound:** `H_{ω^α·(k+1)}(n) + 1 ≤ (f_α)^[k+1](n+1)` (for `α ≠ 0`).
The `hardy_oadd_coeff` companion of the `ω^α` upper bound: `H_{ω^α·(k+1)} = (H_{ω^α})^[k+1]`, and the
`+1` shift `H_{ω^α}(y)+1 ≤ f_α(y+1)` carries through `k+1` iterations via `iterate_offset_le`. -/
theorem hardy_coeff_add_one_le (α : ONote) (hα : α ≠ 0) (k n : ℕ) :
    hardy (oadd α k.succPNat 0) n + 1 ≤ (fastGrowing α)^[k + 1] (n + 1) := by
  rw [hardy_oadd_coeff α hα k n]
  exact iterate_offset_le (fastGrowing_monotone α) (hardy_omega_pow_add_one_le α) (k + 1) n

/-- **The coefficient-general two-sided bracket:** `(f_α)^[k+1](n) ≤ H_{ω^α·(k+1)}(n) < (f_α)^[k+1](n+1)`
(for `α ≠ 0`). The `hardy_oadd_coeff`-lifted form of `hardy_omega_pow_bracket`: the Hardy hierarchy at
`ω^α·(k+1)` is sandwiched between consecutive values of the `(k+1)`-fold iterate of `f_α`. -/
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

/-- **The ε₀ diagonal is dominated by Hardy at the tower:** `fastGrowingε₀ i ≤ H_{tower(i+1)}(i)`.
Directly the lower `ω^α` bracket at `α = tower i`, argument `i`, using `tower(i+1) = ω^{tower i}`. -/
theorem fastGrowingε₀_le_hardy_tower_succ (i : ℕ) :
    fastGrowingε₀ i ≤ hardy (tower (i + 1)) i := by
  have h : fastGrowing (tower i) i ≤ hardy (oadd (tower i) 1 0) i :=
    (hardy_omega_pow_bracket (tower i) i).1
  rw [← tower_succ] at h
  exact h

/-- **The matching ε₀-diagonal upper bound:** `H_{tower(i+1)}(i) < f_{tower i}(i+1)` — Hardy at the
next tower level is under the previous diagonal level at the bumped argument. The upper `ω^α` bracket
at `α = tower i`. Together with `fastGrowingε₀_le_hardy_tower_succ` this brackets `H_{tower(i+1)}(i)`
strictly between `fastGrowingε₀ i` and `f_{tower i}(i+1)`. -/
theorem hardy_tower_succ_lt_fastGrowing (i : ℕ) :
    hardy (tower (i + 1)) i < fastGrowing (tower i) (i + 1) := by
  have h := (hardy_omega_pow_bracket (tower i) i).2
  rw [← tower_succ] at h
  exact h

end ONote
