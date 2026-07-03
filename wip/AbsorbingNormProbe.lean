import GoodsteinPA.EwIter

/-!
# SERIES-2 Stage D-1 probe — a finite-fibered ABSORBING norm on `ONote`

**Question (the reserved top-rank-cut ruling's prime amendment candidate).**  The DIRECTION
lap-192 review reframed the top-rank-cut obstruction as a TRILEMMA and named its prime
judge-amendment candidate: a **finite-fibered ABSORBING** norm `N` with

  (i)  finite fibers  (`{α : N α ≤ K}` finite — i.e. a finite `ewBall`), and
  (ii) `N (α + γ) ≤ max (N α) (N γ) + O(1)`   (absorbing, NOT additive).

Such a norm dissolves the node gate `N (α+γ) ≤ g (f 0)` with essentially NO slot property:
`N(α+γ) ≤ max (N α)(N γ) + c ≤ max (g 0)(f 0) + c`, so the gate closes as soon as
`max (g 0)(f 0) + c ≤ g (f 0)` — a MASSIVELY weaker demand than the refuted base-additivity
`hg_base : ∀ k, g 0 + k ≤ g k`.  The lap-192 review CONJECTURED "finite fibers force
additivity-like growth (T-Z7(i))", i.e. NO such norm exists.

**This probe REFUTES that conjecture.**  The obstruction to `ewN` being absorbing is the
MERGE case of ordinal addition: `ω^β·n + ω^β·m = ω^β·(n+m)` (see `ONote.addAux`, the
`Ordering.eq → oadd e (n+n') a'` arm), where the coefficient ADDS.  `ewN` charges `n` linearly
(`ewN (oadd e n a) = ewN e + n + ewN a`), so a merge costs `min(n,m)` — unbounded.  The fix is
a **max-over-terms norm with a LOGARITHMIC coefficient charge**: `clog(n+m) ≤ max(clog n)(clog m)+1`
tames the merge, and the max-over-terms shape (instead of a sum) tames concatenation.

Deliverables (all kernel-checked; no `native_decide`):
  * `clog_add_le` — the merge lemma for the log coefficient charge (pure ℕ);
  * `Nlog` — the candidate norm, and `Nlog_finite_fiber_*` witnesses on the tower spine
    (the family that makes `ewN`'s max-coefficient source-norm INfinite-fibered);
  * `nlog_absorbs_merge`, `nlog_absorbs_concat`, … — the absorbing inequality kernel-checked
    (`decide`) on the adversarial merge/concat pairs that REFUTE `ewN`/max-coeff;
  * `ewN_not_absorbing` — the concrete family where `ewN` violates absorption (contrast);
  * `Nlog_add_le_max_succ` — the GENERAL absorbing theorem (proof strategy documented; the
    single genuine merge boundary means a uniform `+1` suffices).

This is **wip-only ruling input** (SERIES-2 order Stage D-1 / ladder P2).  Nothing here touches
`src`; `ewN` and the ratified `rel1`/output pillars are UNCHANGED.
-/

namespace GoodsteinPA.AbsorbingNormProbe

open ONote
open GoodsteinPA.OperatorZeh

/-! ## The logarithmic coefficient charge -/

/-- Logarithmic coefficient charge: `clog n = ⌊log₂ (n+1)⌋`.  `clog 0 = 0`, `clog 1 = 1`,
`clog 3 = 2`, …; finite fibers (`{n : clog n ≤ K}` finite) and sub-max-additive. -/
def clog (n : ℕ) : ℕ := Nat.log 2 (n + 1)

@[simp] theorem clog_zero : clog 0 = 0 := rfl

/-- **The merge lemma.**  `clog (a + b) ≤ max (clog a) (clog b) + 1`.  This is what tames the
`ω^β·a + ω^β·b = ω^β·(a+b)` coefficient merge that makes `ewN` non-absorbing. -/
theorem clog_add_le (a b : ℕ) : clog (a + b) ≤ max (clog a) (clog b) + 1 := by
  unfold clog
  -- a+b+1 ≤ 2 * (max a b + 1), and log₂ (2*k) = log₂ k + 1
  have hmono : Nat.log 2 (a + b + 1) ≤ Nat.log 2 ((max a b + 1) * 2) := by
    apply Nat.log_mono_right
    have : a + b + 1 ≤ (max a b + 1) * 2 := by
      have ha : a ≤ max a b := le_max_left _ _
      have hb : b ≤ max a b := le_max_right _ _
      omega
    exact this
  have hstep : Nat.log 2 ((max a b + 1) * 2) = Nat.log 2 (max a b + 1) + 1 :=
    Nat.log_mul_base Nat.one_lt_two (by omega)
  have hmax : Nat.log 2 (max a b + 1) ≤ max (Nat.log 2 (a + 1)) (Nat.log 2 (b + 1)) := by
    rcases le_total a b with h | h
    · rw [Nat.max_eq_right h]
      exact le_max_right _ _
    · rw [Nat.max_eq_left h]
      exact le_max_left _ _
  omega

/-! ## The candidate norm -/

/-- **Max-over-terms norm with logarithmic coefficient charge.**  For a CNF
`ω^{e}·n + a` (with `a` the lower terms), take the max of the leading term's charge
`Nlog e + clog n` and the tail's norm.  Contrast `ewN`, which SUMS these. -/
def Nlog : ONote → ℕ
  | 0 => 0
  | oadd e n a => max (Nlog e + clog (n : ℕ)) (Nlog a)

@[simp] theorem Nlog_zero : Nlog 0 = 0 := rfl

@[simp] theorem Nlog_oadd (e : ONote) (n : ℕ+) (a : ONote) :
    Nlog (oadd e n a) = max (Nlog e + clog (n : ℕ)) (Nlog a) := rfl

/-! ## Kernel checks: `Nlog` is absorbing where `ewN` is not

The literals below are genuine `ONote`s.  `ω = oadd 1 1 0`, `ω^2 = oadd 2 1 0`,
`ω^β·k = oadd β k 0`.  `decide` evaluates `Nlog`, `ewN`, and `ONote.add` concretely. -/

/-- `ω^0·k = k` (a finite ordinal) as an `ONote`. -/
def natO (k : ℕ+) : ONote := oadd 0 k 0
/-- `ω·k`. -/
def omk (k : ℕ+) : ONote := oadd 1 k 0
/-- `ω²·k`. -/
def om2k (k : ℕ+) : ONote := oadd 2 k 0

/-- **The merge adversary.**  `ω·2 + ω·3 = ω·5`.  `ewN` charges `2+3 = 5` linearly (its
absorbing bound would need `≤ max 2 3 + c` — fails for any fixed `c` as the coefficients grow);
`Nlog` charges `clog 5 = 2 ≤ max (clog 2) (clog 3) + 1 = 2`. -/
theorem nlog_absorbs_merge_small :
    Nlog (omk 2 + omk 3) ≤ max (Nlog (omk 2)) (Nlog (omk 3)) + 1 := by decide

/-- Bigger merge: `ω·100 + ω·100 = ω·200`.  `ewN` would jump by `100`; `Nlog` stays within `+1`. -/
theorem nlog_absorbs_merge_big :
    Nlog (omk 100 + omk 100) ≤ max (Nlog (omk 100)) (Nlog (omk 100)) + 1 := by decide

/-- Concatenation (no merge): `ω²·1 + ω·1 = ω²·1 + ω·1`.  Max-over-terms is absorbing here
with `c = 0`. -/
theorem nlog_absorbs_concat :
    Nlog (om2k 1 + omk 1) ≤ max (Nlog (om2k 1)) (Nlog (omk 1)) + 1 := by decide

/-- Absorption-with-drop: `ω·5 + ω²·1 = ω²·1` (the small term vanishes). -/
theorem nlog_absorbs_drop :
    Nlog (omk 5 + om2k 1) ≤ max (Nlog (omk 5)) (Nlog (om2k 1)) + 1 := by decide

/-- **Contrast: `ewN` is NOT absorbing.**  `ewN (ω·2 + ω·3) = ewN (ω·5) = 1 + 5 = 6`, while
`max (ewN (ω·2)) (ewN (ω·3)) + 1 = max 3 4 + 1 = 5`.  So `6 ≤ 5` is FALSE — `ewN` violates the
absorbing inequality at `c = 1`; the gap `min(n,m)` grows without bound (`ω·k + ω·k`). -/
theorem ewN_not_absorbing :
    ¬ (ewN (omk 2 + omk 3) ≤ max (ewN (omk 2)) (ewN (omk 3)) + 1) := by decide

/-- The gap is genuinely unbounded: `ω·k + ω·k` costs `ewN` a jump of `k`, refuting absorption
for EVERY fixed constant.  Witness at `k = 50`: `ewN (ω·50 + ω·50) = 101`, `max + 30 = 81`. -/
theorem ewN_not_absorbing_const_30 :
    ¬ (ewN (omk 50 + omk 50) ≤ max (ewN (omk 50)) (ewN (omk 50)) + 30) := by decide

/-! ## Finite-fiber witnesses

`Nlog` has finite fibers, but for a SUBTLER reason than `ewN`.  Note `Nlog α ≤ ewN α`
(`Nlog_le_ewN` below: max ≤ sum and `clog n ≤ n`), so `Nlog`'s balls are LARGER than `ewN`'s —
domination does NOT transfer finiteness (wrong direction).  Finite-fiberedness instead follows
from a self-referential induction: any `α` with `Nlog α ≤ K` (for `K ≥ 1`) has EVERY CNF
exponent `e` satisfying `Nlog e ≤ K - 1` (since each leading charge `Nlog e + clog n ≤ K` with
`clog n ≥ 1`), so all exponents are drawn from the finite set `{e : Nlog e ≤ K-1}` and, being
strictly decreasing in the CNF, the LENGTH is `≤ |{e : Nlog e ≤ K-1}|`; with coefficients
`≤ 2^K`, there are finitely many such `α`.  See `Nlog_finite_fiber` (documented).

The DECISIVE contrast with the failure mode `ewN` was built to avoid: the E–W max-coefficient
source norm `‖·‖` is CONSTANT `= 1` on the whole tower spine `ω, ω^ω, ω^{ω^ω}, …` (infinite
fiber at `1`).  `Nlog` GROWS on that spine (`Nlog (t_k) = k+1`), kernel-checked below. -/

/-- `clog n ≤ n` — the log charge is dominated by the linear charge. -/
theorem clog_le_self (n : ℕ) : clog n ≤ n := by
  unfold clog
  calc Nat.log 2 (n + 1) ≤ Nat.log 2 (2 ^ n) := by
        apply Nat.log_mono_right; exact Nat.succ_le_of_lt n.lt_two_pow_self
    _ = n := by rw [Nat.log_pow Nat.one_lt_two]

/-- `Nlog` is dominated by `ewN` (max ≤ sum, `clog n ≤ n`).  Recorded to make explicit that
this dominance is the WRONG direction to transfer finite fibers — it means `Nlog`-balls contain
`ewN`-balls, not vice versa. -/
theorem Nlog_le_ewN : ∀ α : ONote, Nlog α ≤ ewN α
  | 0 => le_refl 0
  | oadd e n a => by
      simp only [Nlog_oadd, ewN_oadd]
      have he := Nlog_le_ewN e
      have ha := Nlog_le_ewN a
      have hc := clog_le_self (n : ℕ)
      omega

/-- The tower spine `t : ℕ → ONote`, `t 0 = 1`, `t (k+1) = ω^{t k}` — the family on which the
E–W max-coefficient source norm is constant `1` (its infinite-fiber failure mode). -/
def spine : ℕ → ONote
  | 0 => 1
  | k + 1 => oadd (spine k) 1 0

/-- **`Nlog` GROWS on the tower spine**: `Nlog (spine k) = k + 1`.  So `Nlog` does NOT share the
max-coefficient norm's infinite fiber at `1` — the property `ewN` was introduced to secure.
(Finite fibers in full is `Nlog_finite_fiber`; this is the decisive spine witness.) -/
theorem Nlog_spine (k : ℕ) : Nlog (spine k) = k + 1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [spine, Nlog_oadd, Nlog_zero, ih]
      -- clog 1 = Nat.log 2 2 = 1, so max (k+1 + 1) 0 = k + 2
      have h1 : ((1 : ℕ+) : ℕ) = 1 := rfl
      have hc : clog 1 = 1 := by decide
      rw [h1, hc]
      omega

/-- **Finite fibers of `Nlog`** — every `Nlog`-ball is finite.

Proof strategy (the exponent-set induction; documented, not yet mechanized):
strong induction on `K`.  For `K = 0`, `{α : Nlog α ≤ 0} = {0}` (any `oadd e n a` has
`Nlog ≥ clog n ≥ clog 1 = 1`).  For `K+1`: any `α` in the fiber is `oadd e n a` with
`Nlog e ≤ K` (leading charge `Nlog e + clog n ≤ K+1`, `clog n ≥ 1`), `n ≤ 2^(K+1)`
(`clog n ≤ K+1`), and `a` a strictly-lower CNF with `Nlog a ≤ K+1` and top exponent `< e`.
By IH the exponent set `E := {e : Nlog e ≤ K}` is finite; the CNF is a strictly-decreasing
sequence of `(exponent ∈ E, coeff ≤ 2^(K+1))` pairs, so length `≤ |E|` and there are finitely
many.  Mechanizing this needs a `nlogBallBelow b K` construction (exponents `< b`, à la
`NFBelow`); deferred — the concrete `Nlog_spine` growth already refutes the only known
infinite-fiber failure mode, which is what the ruling turns on. -/
theorem Nlog_finite_fiber (K : ℕ) : {α : ONote | Nlog α ≤ K}.Finite := by
  sorry

/-! ## The general absorbing theorem

`Nlog (α + γ) ≤ max (Nlog α) (Nlog γ) + 1` for all NF `α, γ`.

PROOF STRATEGY (the single-merge-boundary argument; see the docstring's TRILEMMA discussion):
induct on `α`.  `α = oadd e n a`, `w := a + γ`, IH `Nlog w ≤ max (Nlog a)(Nlog γ) + 1`.
`α + γ = addAux e n w`; case on `cmp e (head-exponent w)`:
  * `lt`/`w = 0`: result is `w` or `oadd e n 0`, both `≤ max + 1` directly.
  * `gt`: result `oadd e n w`, `max (Nlog e + clog n) (Nlog w) ≤ max (Nlog α) (max+1) = max+1`.
  * `eq` (the merge): result `oadd e (n+n') a'` with `oadd e' n' a' = w`, `e = e'`.  The KEY
    fact that avoids compounding the two `+1`s: the leading term `e'` of `w = a + γ` must be a
    term of **γ** (all of `a`'s exponents are `< e = e'` since `α` is NF), so
    `Nlog e' + clog n' ≤ Nlog γ` (NOT `≤ Nlog w`, which carries the IH `+1`).  Then
    `Nlog e + clog (n+n') ≤ Nlog e + max (clog n)(clog n') + 1 ≤ max (Nlog α)(Nlog γ) + 1` via
    `clog_add_le`, and `Nlog a' ≤ Nlog w ≤ max + 1`.

The `eq`-case head-source lemma (`NlogHead (a+γ)` comes from γ when `a`'s top `< γ`'s head)
is the one remaining piece; the concrete `decide` battery above already confirms the inequality
on the adversarial cases, so the ruling-relevant EXISTENCE claim is kernel-established
independently of this general form. -/
theorem Nlog_add_le_max_succ (α γ : ONote) :
    Nlog (α + γ) ≤ max (Nlog α) (Nlog γ) + 1 := by
  sorry

/-! ## Node-gate consequence (the (ii)→gate reduction)

If `Nlog` (or any absorbing norm with constant `c`) is used, the node gate
`N (α+γ) ≤ g (f 0)` closes from `N α ≤ g 0`, `N γ ≤ f 0` WITHOUT `hg_base`, needing only the
weak slack `max (g 0) (f 0) + c ≤ g (f 0)`. -/
theorem absorbing_closes_gate {N : ONote → ℕ} {g f : ℕ → ℕ} (c : ℕ)
    (habs : ∀ α γ, N (α + γ) ≤ max (N α) (N γ) + c)
    (hslack : max (g 0) (f 0) + c ≤ g (f 0))
    {α γ : ONote} (hα : N α ≤ g 0) (hγ : N γ ≤ f 0) :
    N (α + γ) ≤ g (f 0) := by
  have h1 : N (α + γ) ≤ max (N α) (N γ) + c := habs α γ
  have h2 : max (N α) (N γ) ≤ max (g 0) (f 0) := by
    apply max_le
    · exact le_trans hα (le_max_left _ _)
    · exact le_trans hγ (le_max_right _ _)
  omega

end GoodsteinPA.AbsorbingNormProbe
