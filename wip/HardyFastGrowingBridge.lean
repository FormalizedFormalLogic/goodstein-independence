/-
# PROBE / TARGET: the exact Hardy–fast-growing bridge at `ω^α`

Corrects lap-177's claim "the substrate has no fast-growing `F`": `ONote.fastGrowing` IS defined
(mathlib) and the repo carries its full growth theory (`Hardy.lean` §Basic).  The repo's B4 note
(`Hardy.lean:1082`) calls the bridge `H_{ω^α} = f_α`; kernel checks this session show that EQUALITY
is off by TWO successive shift subtleties (both convincing-identity traps caught by `#eval` /
strict-monotonicity):
  1. `H_{ω^α}(n) = f_α(n)` is false — `H_{ω^1}(3)=7 ≠ 6=f_1(3)`; the shifted `=` is
     `H_{ω^α}(n) + 1 = f_α(n+1)` (kernel-`#eval`-anchored α ∈ {0,1,2}).
  2. But even THAT `=` holds only at successor/finite exponents; at LIMIT exponents it degrades to
     STRICT `<` (fund.-seq. index `f n` vs `f(n+1)`, `fastGrowing` strictly ordinal-monotone).

So the UNCONDITIONAL, load-bearing truth is the INEQUALITY

    hardy (oadd α 1 0) n + 1 ≤ fastGrowing α (n + 1)          -- H_{ω^α}(n) < f_α(n+1)

— which is EXACTLY the upper bound the P1 raised-control obligation needs: with `raise e α' =
e + ω^{α'}` in the ABSORBING regime (lap 178), the raised control is `≈ hardy(ω^{α'})`, and this
bound (`hardy_omega_pow_lt_fastGrowing`) reduces P1 to E–W Lemma 19 `fastGrowing α' ≤ f^{iterate}`.

Pure Hardy/fastGrowing growth theory about STABLE defs (mathlib `fastGrowing` + repo `hardy`);
calculus-independent (no `Zeh`, no pin, no cut-elim machinery); the repo's own long-horizon target
B4, sharpened to its true ONote inequality form.  **Base + LIMIT cases proven**; the successor case
(the coefficient intermediate `H_{ω^β·(m+1)}`, the classical Cichoń–Wainer core) is the open grind.
-/
import GoodsteinPA.Hardy

namespace GoodsteinPA.FastGrowing

open ONote

/-! ### Faithfulness anchors — the exact shift is kernel-checked, not guessed -/

example : hardy (oadd 0 1 0) 3 + 1 = fastGrowing 0 (3 + 1) := by native_decide
example : hardy (oadd 1 1 0) 3 + 1 = fastGrowing 1 (3 + 1) := by native_decide
example : hardy (oadd 1 1 0) 4 + 1 = fastGrowing 1 (4 + 1) := by native_decide
example : hardy (oadd 2 1 0) 1 + 1 = fastGrowing 2 (1 + 1) := by native_decide
example : hardy (oadd 2 1 0) 2 + 1 = fastGrowing 2 (2 + 1) := by native_decide

-- and the EQUALITY H_{ω^α}=f_α is FALSE (off by ≥1) — recorded so no lap re-attempts it:
example : hardy (oadd 1 1 0) 3 ≠ fastGrowing 1 3 := by native_decide

/-! **The `=` is limit-conditional — the UNCONDITIONAL truth is `≤`.**  Kernel-reasoned: at a LIMIT
exponent `α` (fund. seq. `f`), `H_{ω^α}(n) = H_{ω^{f n}}(n)` uses `f n`, while `f_α(n+1) =
f_{f(n+1)}(n+1)` uses `f(n+1) > f n`; `fastGrowing` is strictly monotone in the ordinal, so the LHS
is STRICTLY smaller — the equality FAILS at limits (a third convincing-identity refinement this
session; `fastGrowing ω`-scale values are too large to `#eval`, but the strict-monotone argument is
decisive).  The `native_decide` anchors above (α ∈ {0,1,2}, all successor/finite exponents) are
exactly the regime where `=` holds.  So the load-bearing target is the INEQUALITY below — and that is
precisely the UPPER bound P1 needs. -/

/-- **The coefficient intermediate** (the classical Cichoń–Wainer core), parametrized by the
exponent-`β` base bound `hbase` (supplied by the outer IH in the successor case):
`H_{ω^β·(m+1)}(n) + 1 ≤ f_β^{[m+1]}(n+1)`.  Kernel-verified for β ∈ {0,1} (`#eval`, scratch).
Induction on the coefficient `m`:
* `m = 0`: `ω^β·1 = ω^β`, `f_β^{[1]} = f_β` — exactly `hbase`.
* `m+1`: relate `H_{ω^β·(m+2)}` to `H_{ω^β·(m+1)}` (IH) with one extra `f_β`-iterate.  The
  fund. seq. of `ω^β·(m+2)` (= `reaches_coeff_step'` territory) branches on β's shape (0/succ/limit);
  this is the OPEN step. -/
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
      -- H_{ω^β·(m+2)}(n) + 1 ≤ f_β^{[m+2]}(n+1); OPEN (fund. seq. of ω^β·(m+2) branches on β).
      sorry

/-- **TARGET: the Hardy–fast-growing UPPER bound at `ω^α`** — `H_{ω^α}(n) + 1 ≤ f_α(n+1)`,
unconditional.  Well-founded recursion on `α`:
* `α = 0`: equality, `n+2 = succ(n+1)`.  ✓ (proven).
* `α` limit: `ω^α[i] = ω^{α[i]}`; IH at `f n < α` then `fastGrowing`-index-monotonicity
  (`fastGrowing_bachmann_reach` + `fastGrowing_le_of_reaches`) bridges `f n → f(n+1)`.  ✓ (proven).
* `α = β+1`: `ω^{β+1}[i] = ω^β·(i+1)`; needs the coefficient intermediate
  `H_{ω^β·(m+1)}(n) + 1 = f_β^{[m+1]}(n+1)` (kernel-verified β∈{0,1}), proved by induction on the
  coefficient `m` with base = the outer IH at `β`.  OPEN (the classical Cichoń–Wainer core). -/
theorem hardy_omega_pow_add_one_le (α : ONote) : ∀ n : ℕ,
    hardy (oadd α 1 0) n + 1 ≤ fastGrowing α (n + 1) := by
  haveI : WellFoundedLT ONote := ⟨InvImage.wf repr Ordinal.lt_wf⟩
  induction α using WellFoundedLT.induction with
  | _ α ih =>
    intro n
    rcases hα : fundamentalSequence α with (_ | β) | f
    · -- α = 0: H_{ω^0} = H_1 = (·+1); f_0 = succ.  Equality ⟹ ≤.
      have h0 : α = 0 := by
        have hp := fundamentalSequence_has_prop α; rw [hα] at hp; exact hp
      subst h0
      have hfs1 : fundamentalSequence (oadd 0 1 0) = Sum.inl (some 0) := rfl
      rw [hardy_succ (oadd 0 1 0) hfs1, hardy_zero, fastGrowing_zero]
      simp only [id_eq]; omega
    · -- α = β+1 (successor exponent): ω^{β+1}[i] = ω^β·(i+1); reduce to the coefficient intermediate.
      have hlt : β < α := by
        have hp := fundamentalSequence_has_prop α; rw [hα] at hp
        rw [lt_def, hp.1]; exact Order.lt_succ _
      have homega : fundamentalSequence (oadd α 1 0) = Sum.inr (fun i => oadd β i.succPNat 0) :=
        fundamentalSequence_omega_pow_succ hα
      rw [hardy_limit (oadd α 1 0) homega, fastGrowing_succ α hα]
      exact hardy_omega_pow_coeff_le (ih β hlt) n n
    · -- α limit: ω^α[i] = ω^{α[i]}; IH + fastGrowing index-monotonicity.
      have hlim_h : fundamentalSequence (oadd α 1 0) = Sum.inr (fun i => oadd (f i) 1 0) :=
        fundamentalSequence_omega_pow_limit hα
      have hlt : f n < α := by
        have hp := fundamentalSequence_has_prop α; rw [hα] at hp; exact (hp.2.1 n).2.1
      rw [hardy_limit (oadd α 1 0) hlim_h, fastGrowing_limit α hα]
      calc hardy (oadd (f n) 1 0) n + 1
          ≤ fastGrowing (f n) (n + 1) := ih (f n) hlt n
        _ ≤ fastGrowing (f (n + 1)) (n + 1) :=
            fastGrowing_le_of_reaches (Nat.succ_le_succ (Nat.zero_le n))
              (fastGrowing_bachmann_reach hα n)

/-- **The usable corollary:** the UPPER bound the P1 raised-control obligation needs —
`hardy(ω^α)(n) < fastGrowing α (n+1)`, from the `+1 ≤` target. -/
theorem hardy_omega_pow_lt_fastGrowing (α : ONote) (n : ℕ) :
    hardy (oadd α 1 0) n < fastGrowing α (n + 1) := by
  have h := hardy_omega_pow_add_one_le α n
  omega

end GoodsteinPA.FastGrowing
