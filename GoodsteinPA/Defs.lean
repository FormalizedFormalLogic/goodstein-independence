/-
# Goodstein sequences — faithful definition (this repo's audit surface, part 0)

Local, self-contained copy of the audited Goodstein definition (verbatim from
`lean-formalizations` `Logic/Goodstein/Defs.lean`, whose `goodstein_terminates` is
kernel-clean: `#print axioms → [propext, Classical.choice, Quot.sound]`). Owned here
so the independence repo's trust surface is local and complete — `Bridge.lean` ties the
syntactic `goodsteinSentence` to *this* def. Drift-guarded by `native_decide` anchors
(`Anchors.lean`). The verified termination *theorem* + `Engine` from `lean-formalizations`
are reused later (Phases 3–4), where the dependency earns its keep.

## The definition (standard; Goodstein 1944)
For a base `b ≥ 2`, the *hereditary base-`b`* representation writes `n` in base `b`, then
rewrites every exponent in base `b`, recursively. The **bump** `bump b n` replaces every
occurrence of the base `b` by `b + 1` (exponents bumped recursively, digits unchanged).
The **Goodstein sequence** seeded at `m` is `G 0 = m`, and `G (k+1)` = bump base
`(k+2) ↦ (k+3)` in `G k`, then **subtract 1** (`0` absorbing). Base at step `k` is `k + 2`.
-/
import Mathlib.Data.Nat.Log

namespace GoodsteinPA

/-- The base used to read `G k` at step `k`: `base k = k + 2` (so `G 0` is read in base 2,
the first bump sends `2 ↦ 3`, and so on). -/
def base (k : ℕ) : ℕ := k + 2

/-- **Hereditary-base bump.** `bump b n` reads `n` in hereditary base `b` and replaces every
occurrence of `b` by `b + 1`. Peeling the top power (`e = log b n`, `c = n / b^e`,
`r = n % b^e`): `bump b n = c · (b+1)^(bump b e) + bump b r`, with `bump b 0 = 0`. -/
def bump (b : ℕ) (n : ℕ) : ℕ :=
  if h : n = 0 then 0
  else
    n / b ^ Nat.log b n * (b + 1) ^ bump b (Nat.log b n) + bump b (n % b ^ Nat.log b n)
termination_by n
decreasing_by
  · exact Nat.log_lt_self b h
  · have hb : 0 < b ^ Nat.log b n := by
      rcases Nat.eq_zero_or_pos b with hb0 | hbpos
      · subst hb0; simp [Nat.log_zero_left]
      · exact Nat.pow_pos hbpos
    exact lt_of_lt_of_le (Nat.mod_lt _ hb) (Nat.pow_log_le_self b h)

/-- **Goodstein sequence** seeded at `m`: `goodsteinSeq m k = G k`. `G 0 = m`; `G (k+1)`
bumps the hereditary base `k+2 ↦ k+3` in `G k` and subtracts one (`0` a fixed point, as
`bump b 0 = 0` and `0 - 1 = 0`). -/
def goodsteinSeq (m : ℕ) : ℕ → ℕ
  | 0 => m
  | k + 1 => bump (base k) (goodsteinSeq m k) - 1

end GoodsteinPA
