/-
# `Grzegorczyk.lean` — the ℕ-template for Rathjen 2014 §3 "slowing down" (Lemma 3.3 / Cor 3.4)

This file is the **self-contained ℕ-template** for the genuine remaining wall of the `hbound`
obligation (`DescentSemantic.no_min_descent_absurd_of_goodstein`): Rathjen's **Corollary 3.4**, the
slow-down of an arbitrary ε₀-descent into a *slow* one (`|αᵢ| ≤ K·(i+1)`), whose workhorse is
**Lemma 3.3** — a primitive-recursive `g : ℕ² → ω^ω` with

  (1) `g(n,m) > g(n,m+1)` whenever `m < f(n)`   (strict descent within a block of length `f(n)`)
  (2) `|g(n,m)| ≤ K·(n+m+1)`                     (linearly-bounded max-coefficient `C`)

built by induction on the Grzegorczyk hierarchy `(fₗ)` (Rathjen Lemma 3.2). Everything here is pure
`ℕ`/`ONote`, zero `Foundation` dependency — it typechecks or it doesn't, no faithfulness risk. It is
the proof skeleton the *M-internal* slow-down (`InternalONote` codes) ports onto.

Downstream consumer (already built, `DescentCore.lean`): Thm 3.5 reindex (`C_betaTail_le`,
`repr_betaTail_within/_boundary`) + Lemma 3.6 (`lemma36_nonterminating`). This file supplies the
missing *input* to Thm 3.5: the slow descent.
-/
import GoodsteinPA.DescentCore

namespace GoodsteinPA.Grz

open ONote Ordinal
open GoodsteinPA.Dom (C C_zero C_one C_oadd)

/-! ## The max-coefficient `C` on finite notations -/

/-- `C (ofNat m) = m`: a finite ordinal's only coefficient is its value. -/
@[simp] theorem C_ofNat (m : ℕ) : C (ONote.ofNat m) = m := by
  cases m with
  | zero => simp
  | succ k => simp [ONote.ofNat_succ, C_oadd, C_zero]

/-! ## Rathjen's Grzegorczyk-style hierarchy `(fₗ)`

`F 0 n = n+1`, `F (l+1) n = (F l)^[n] n` (the diagonalization `(fₗ)ⁿ(n)`). Lemma 3.2 says every
primitive-recursive function is pointwise dominated by some `F l` (mathlib's `ack`/`exists_lt_ack`
gives the same domination, used only at the very end of Lemma 3.3 to reduce an arbitrary `f`). -/
def F : ℕ → ℕ → ℕ
  | 0,     n => n + 1
  | l + 1, n => (F l)^[n] n

@[simp] theorem F_zero (n : ℕ) : F 0 n = n + 1 := rfl

@[simp] theorem F_succ (l n : ℕ) : F (l + 1) n = (F l)^[n] n := rfl

/-! ## Base case `g₀` of Lemma 3.3 (for `f = F 0 = (·+1)`)

Rathjen: `g(n,m) = (n+2) -· m` (truncated subtraction), a finite ordinal. Descends for `m < n+1`
(i.e. `m ≤ n`), and `C(g₀ n m) = (n+2)-m ≤ n+2 ≤ 2·(n+m+1)`, so `K = 2`. -/
def g0 (n m : ℕ) : ONote := ONote.ofNat ((n + 2) - m)

@[simp] theorem g0_NF (n m : ℕ) : (g0 n m).NF := by
  unfold g0; infer_instance

/-- Lemma 3.3(1), base case: `g₀` strictly descends in `m` while `m < F 0 n`. -/
theorem g0_desc (n m : ℕ) (hm : m < F 0 n) : (g0 n (m + 1)).repr < (g0 n m).repr := by
  have hmn : m ≤ n := by simpa [F] using Nat.lt_succ_iff.1 (by simpa using hm)
  simp only [g0, ONote.repr_ofNat]
  have h : (n + 2) - (m + 1) < (n + 2) - m := by omega
  exact_mod_cast h

/-- Lemma 3.3(2), base case: `C(g₀ n m) ≤ 2·(n+m+1)` (so `K = 2` works for `F 0`). -/
theorem g0_bound (n m : ℕ) : C (g0 n m) ≤ 2 * (n + m + 1) := by
  simp only [g0, C_ofNat]; omega

/-! ## Induction-step building blocks: the `ω^k`-block term `ω^k·c + x`

Rathjen's induction step sets `g_{l+1}(n,m) = ω^k·(n-i) + g_l(F_l^i(n), j)`. The reusable hard core is
the **block term** `blk k c x = ω^k·c + x` (an `oadd (ofNat k) c x`) and its two ordinal facts:
*within-block descent* (fixed leading `ω^k·c`, the tail `x` shrinks) and *block-boundary descent*
(`ω^k·c' + x' < ω^k·c + x` whenever `c' < c` and `x' < ω^k`). These are exactly Rathjen's two descent
cases, proved purely on `Ordinal`/`ONote` — the genuinely delicate arithmetic, isolated and verified
once so the eventual `g` recursion only has to feed them the right `c`/`x`. -/

/-- The block term `ω^k·c + repr x`. `c : ℕ+` because the live blocks have `c = n - i ≥ 1`. -/
def blk (k : ℕ) (c : ℕ+) (x : ONote) : ONote := ONote.oadd (ONote.ofNat k) c x

@[simp] theorem repr_blk (k : ℕ) (c : ℕ+) (x : ONote) :
    (blk k c x).repr = (ω : Ordinal) ^ (k : ℕ) * (c : ℕ) + x.repr := by
  simp [blk, ONote.repr]

/-- `C` of a block term: `max(max k c) (C x)`. -/
@[simp] theorem C_blk (k : ℕ) (c : ℕ+) (x : ONote) :
    C (blk k c x) = max (max k (c : ℕ)) (C x) := by
  simp [blk, C_oadd]

/-- **Within-block descent**: same leading `ω^k·c`, a smaller tail gives a smaller block term. -/
theorem repr_blk_within (k : ℕ) (c : ℕ+) {x x' : ONote} (hx : x'.repr < x.repr) :
    (blk k c x').repr < (blk k c x).repr := by
  simp only [repr_blk]; exact (add_lt_add_iff_left _).2 hx

/-- **Block-boundary descent** (Rathjen's `ω^k·(n-(i+1)) + ω ≤ ω^k·(n-i)` step): if `c' < c` and the
tail `x'` is below `ω^k`, then `ω^k·c' + x' < ω^k·c + x` for any `x`. The whole `c'`-block sits below
`ω^k·(c'+1) ≤ ω^k·c`. -/
theorem repr_blk_boundary (k : ℕ) {c c' : ℕ+} {x x' : ONote}
    (hc : (c' : ℕ) < (c : ℕ)) (hx' : x'.repr < (ω : Ordinal) ^ (k : ℕ)) :
    (blk k c' x').repr < (blk k c x).repr := by
  simp only [repr_blk]
  calc (ω : Ordinal) ^ (k : ℕ) * (c' : ℕ) + x'.repr
      < (ω : Ordinal) ^ (k : ℕ) * (c' : ℕ) + (ω : Ordinal) ^ (k : ℕ) :=
        (add_lt_add_iff_left _).2 hx'
    _ = (ω : Ordinal) ^ (k : ℕ) * ((c' : ℕ) + 1) := by rw [mul_add, mul_one]
    _ ≤ (ω : Ordinal) ^ (k : ℕ) * (c : ℕ) :=
        mul_le_mul_right (by exact_mod_cast Nat.succ_le_of_lt hc) _
    _ ≤ (ω : Ordinal) ^ (k : ℕ) * (c : ℕ) + x.repr := le_self_add

/-! ## Iterate / partial-sum scaffolding for the block decomposition

For `m < F_{l+1}(n) = (F l)^[n] n`, Rathjen writes `m = F_l(n)+F_l²(n)+…+F_l^i(n) + j` with `i < n`,
`j < F_l^{i+1}(n)`. The partial sums `psum f n i = Σ_{t=1}^{i} f^[t](n)` carve `[0, psum f n n)` into the
`n` blocks; block `i` is `[psum f n i, psum f n (i+1))` of width `f^[i+1](n)`. -/

/-- Partial sum of iterates: `psum f n i = f^[1](n) + f^[2](n) + … + f^[i](n)`. -/
def psum (f : ℕ → ℕ) (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | i + 1 => psum f n i + f^[i + 1] n

@[simp] theorem psum_zero (f : ℕ → ℕ) (n : ℕ) : psum f n 0 = 0 := rfl

@[simp] theorem psum_succ (f : ℕ → ℕ) (n i : ℕ) :
    psum f n (i + 1) = psum f n i + f^[i + 1] n := rfl

/-- `F l n ≥ 1` for `n ≥ 1` (in fact `F l n ≥ n+1`), so each live block has positive width. -/
theorem one_le_F (l : ℕ) {n : ℕ} (hn : 1 ≤ n) : 1 ≤ F l n := by
  induction l generalizing n with
  | zero => simp
  | succ l ih =>
    simp only [F_succ]
    -- (F l)^[n] n ≥ 1 : iterating a function that is ≥1 on positives, from n ≥ 1
    have key : ∀ t, 1 ≤ (F l)^[t] n := by
      intro t
      induction t with
      | zero => simpa using hn
      | succ t iht => rw [Function.iterate_succ_apply']; exact ih iht
    exact key n

/-- The partial sums strictly increase across live blocks: `psum f n i < psum f n (i+1)` once each
iterate `f^[i+1] n ≥ 1` (true for `f = F l`, `n ≥ 1`). -/
theorem psum_strictMono_step (f : ℕ → ℕ) (n i : ℕ) (hpos : 1 ≤ f^[i + 1] n) :
    psum f n i < psum f n (i + 1) := by
  simp only [psum_succ]; omega

/-- `F (l+1) n = (F l)^[n] n ≤ psum (F l) n n`: the last iterate `(F l)^[n] n` is one summand of
`psum (F l) n n`, so `m < F (l+1) n` lands inside `[0, psum (F l) n n)` (the live block range). -/
theorem F_succ_le_psum (l : ℕ) {n : ℕ} (hn : 1 ≤ n) : F (l + 1) n ≤ psum (F l) n n := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  rw [F_succ, psum_succ]; omega

/-! ## Block decomposition `m ↦ (i, j)` (Rathjen's `m = Σ_{t≤i} f^[t](n) + j`)

`blockIdx f n m` = the largest `i ≤ n` with `psum f n i ≤ m`; `blockOff f n m = m - psum f n i` is the
offset `j` inside block `i`. For `m < psum f n n` (which holds when `m < F (l+1) n`, by
`F_succ_le_psum`), this gives the unique `i < n`, `j < f^[i+1](n)` decomposition. -/

/-- The block index `i`: largest `i ≤ n` whose partial sum `psum f n i` still fits under `m`. -/
def blockIdx (f : ℕ → ℕ) (n m : ℕ) : ℕ := Nat.findGreatest (fun i => psum f n i ≤ m) n

/-- The within-block offset `j = m - psum f n i`. -/
def blockOff (f : ℕ → ℕ) (n m : ℕ) : ℕ := m - psum f n (blockIdx f n m)

/-- Block lower bound: `psum f n (blockIdx) ≤ m` (block `0` always fits, `psum f n 0 = 0`). -/
theorem psum_blockIdx_le (f : ℕ → ℕ) (n m : ℕ) : psum f n (blockIdx f n m) ≤ m :=
  Nat.findGreatest_spec (P := fun i => psum f n i ≤ m) (m := 0) (Nat.zero_le n)
    (show psum f n 0 ≤ m by simp)

/-- `blockIdx f n m < n` when `m < psum f n n` (some block is not yet consumed). -/
theorem blockIdx_lt (f : ℕ → ℕ) {n m : ℕ} (hn : 1 ≤ n) (hm : m < psum f n n) :
    blockIdx f n m < n := by
  rcases lt_or_eq_of_le (Nat.findGreatest_le (P := fun i => psum f n i ≤ m) n) with h | h
  · exact h
  · exfalso
    have hPn : psum f n n ≤ m :=
      Nat.findGreatest_of_ne_zero (P := fun i => psum f n i ≤ m) h (by omega)
    omega

/-- Block upper bound: `m < psum f n (blockIdx + 1)` (the next block overshoots `m`). -/
theorem lt_psum_blockIdx_succ (f : ℕ → ℕ) {n m : ℕ} (hn : 1 ≤ n) (hm : m < psum f n n) :
    m < psum f n (blockIdx f n m + 1) := by
  have hb := blockIdx_lt f hn hm
  have hng := Nat.findGreatest_is_greatest (P := fun i => psum f n i ≤ m) (n := n)
    (k := blockIdx f n m + 1) (Nat.lt_succ_self (blockIdx f n m)) (by omega)
  exact not_le.1 hng

/-- The offset stays within its block's width: `blockOff f n m < f^[blockIdx+1] n`. -/
theorem blockOff_lt_width (f : ℕ → ℕ) {n m : ℕ} (hn : 1 ≤ n) (hm : m < psum f n n) :
    blockOff f n m < f^[blockIdx f n m + 1] n := by
  have h1 := psum_blockIdx_le f n m
  have h2 := lt_psum_blockIdx_succ f hn hm
  rw [psum_succ] at h2
  simp only [blockOff]; omega

/-- The decomposition is exact: `psum f n i + blockOff f n m = m`. -/
theorem psum_add_blockOff (f : ℕ → ℕ) (n m : ℕ) :
    psum f n (blockIdx f n m) + blockOff f n m = m := by
  have := psum_blockIdx_le f n m; simp only [blockOff]; omega

end GoodsteinPA.Grz
