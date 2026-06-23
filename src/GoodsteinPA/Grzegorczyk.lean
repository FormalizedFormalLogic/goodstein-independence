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

/-- **General cross-block ordinal descent** (Cor 3.4's across-block step, `δ = ω^ω`): if `a < b` and
`x' < δ`, then `δ·a + x' < δ·b + x`. The lower block sits entirely below `δ·(a+1) ≤ δ·b`. -/
theorem mul_add_lt {δ a b x x' : Ordinal} (hab : a < b) (hx' : x' < δ) :
    δ * a + x' < δ * b + x := by
  calc δ * a + x' < δ * a + δ := (add_lt_add_iff_left _).2 hx'
    _ = δ * (a + 1) := by rw [mul_add, mul_one]
    _ ≤ δ * b := mul_le_mul_right (by exact_mod_cast Order.succ_le_of_lt hab) δ
    _ ≤ δ * b + x := le_self_add

/-! ## General width-based block decomposition (for the descent/β side of Cor 3.4)

Cor 3.4 carves the index `j` into blocks whose widths are `W_n = C(β_{n+1})` (not iterates), so we need
the block machinery for an *arbitrary* width sequence `W : ℕ → ℕ`. `wsum W i = Σ_{t<i} W t`; block `i`
is `[wsum W i, wsum W (i+1))`. Mirrors `psum`/`blockIdx` with the same `Nat.findGreatest` engine. -/

/-- Cumulative width: `wsum W i = W 0 + … + W (i-1)`. -/
def wsum (W : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | i + 1 => wsum W i + W i

@[simp] theorem wsum_zero (W : ℕ → ℕ) : wsum W 0 = 0 := rfl
@[simp] theorem wsum_succ (W : ℕ → ℕ) (i : ℕ) : wsum W (i + 1) = wsum W i + W i := rfl

/-- `wsum` is monotone, and strictly so across positive-width blocks. -/
theorem wsum_strictMono (W : ℕ → ℕ) (hpos : ∀ t, 1 ≤ W t) : StrictMono (wsum W) :=
  strictMono_nat_of_lt_succ fun i => by simp only [wsum_succ]; have := hpos i; omega

/-- `i ≤ wsum W i` when all widths are positive (so `wsum` is unbounded). -/
theorem le_wsum (W : ℕ → ℕ) (hpos : ∀ t, 1 ≤ W t) (i : ℕ) : i ≤ wsum W i := by
  induction i with
  | zero => simp
  | succ i ih => simp only [wsum_succ]; have := hpos i; omega

/-- Width-block index: largest `i ≤ cap` with `wsum W i ≤ m`. -/
def widx (W : ℕ → ℕ) (cap m : ℕ) : ℕ := Nat.findGreatest (fun i => wsum W i ≤ m) cap

/-- Width-block offset. -/
def woff (W : ℕ → ℕ) (cap m : ℕ) : ℕ := m - wsum W (widx W cap m)

theorem wsum_widx_le (W : ℕ → ℕ) (cap m : ℕ) : wsum W (widx W cap m) ≤ m :=
  Nat.findGreatest_spec (P := fun i => wsum W i ≤ m) (m := 0) (Nat.zero_le cap)
    (show wsum W 0 ≤ m by simp)

theorem widx_lt (W : ℕ → ℕ) {cap m : ℕ} (hm : m < wsum W cap) (hcap : 1 ≤ cap) :
    widx W cap m < cap := by
  rcases lt_or_eq_of_le (Nat.findGreatest_le (P := fun i => wsum W i ≤ m) cap) with h | h
  · exact h
  · exact absurd (Nat.findGreatest_of_ne_zero (P := fun i => wsum W i ≤ m) h (by omega))
      (by omega)

theorem lt_wsum_widx_succ (W : ℕ → ℕ) {cap m : ℕ} (hm : m < wsum W cap) (hcap : 1 ≤ cap) :
    m < wsum W (widx W cap m + 1) := by
  have hb := widx_lt W hm hcap
  exact not_le.1 (Nat.findGreatest_is_greatest (P := fun i => wsum W i ≤ m) (n := cap)
    (k := widx W cap m + 1) (Nat.lt_succ_self (widx W cap m)) (by omega))

theorem woff_lt_width (W : ℕ → ℕ) {cap m : ℕ} (hm : m < wsum W cap) (hcap : 1 ≤ cap) :
    woff W cap m < W (widx W cap m) := by
  have h1 := wsum_widx_le W cap m
  have h2 := lt_wsum_widx_succ W hm hcap
  rw [wsum_succ] at h2; simp only [woff]; omega

theorem wsum_add_woff (W : ℕ → ℕ) (cap m : ℕ) :
    wsum W (widx W cap m) + woff W cap m = m := by
  have := wsum_widx_le W cap m; simp only [woff]; omega

/-- **Width-block uniqueness** (general `W`): block of `x` is `i` when `wsum W i ≤ x < wsum W (i+1)`. -/
theorem widx_eq (W : ℕ → ℕ) (hpos : ∀ t, 1 ≤ W t) {cap i x : ℕ} (hin : i ≤ cap)
    (hlo : wsum W i ≤ x) (hhi : x < wsum W (i + 1)) : widx W cap x = i := by
  refine le_antisymm ?_ (Nat.le_findGreatest hin hlo)
  by_contra hc
  push_neg at hc
  have hb := wsum_widx_le W cap x
  have : wsum W (i + 1) ≤ wsum W (widx W cap x) := (wsum_strictMono W hpos).monotone (by omega)
  omega

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

/-- Every iterate of `F l` stays `≥ 1` from a positive start (so every block has positive width). -/
theorem one_le_F_iter (l : ℕ) {n : ℕ} (hn : 1 ≤ n) : ∀ t, 1 ≤ (F l)^[t] n := by
  intro t
  induction t with
  | zero => simpa using hn
  | succ t ih => rw [Function.iterate_succ_apply']; exact one_le_F l ih

/-- For `f = F l` and `n ≥ 1`, the partial sums are strictly monotone (every block nonempty). -/
theorem psum_strictMono (l : ℕ) {n : ℕ} (hn : 1 ≤ n) : StrictMono (psum (F l) n) :=
  strictMono_nat_of_lt_succ fun i =>
    psum_strictMono_step (F l) n i (one_le_F_iter l hn (i + 1))

/-- **Block-index uniqueness**: if `psum (F l) n i ≤ x < psum (F l) n (i+1)` with `i ≤ n`, then `x`'s
block is exactly `i`. The engine that lets the recursion read off `blockIdx (F l) n (m+1)`. -/
theorem blockIdx_eq (l : ℕ) {n : ℕ} (hn : 1 ≤ n) {i x : ℕ} (hin : i ≤ n)
    (hlo : psum (F l) n i ≤ x) (hhi : x < psum (F l) n (i + 1)) :
    blockIdx (F l) n x = i := by
  refine le_antisymm ?_ (Nat.le_findGreatest hin hlo)
  by_contra hc
  push_neg at hc
  have hb := psum_blockIdx_le (F l) n x
  have hmono : psum (F l) n (i + 1) ≤ psum (F l) n (blockIdx (F l) n x) :=
    (psum_strictMono l hn).monotone (by omega)
  omega

/-! ## The Lemma 3.3 function `g` and its structural invariants

`g 0 = g₀` (base); `g (l+1) n m = ω^(l+1)·(n-i) + g l (F_l^i(n)) j` for `m < F(l+1)(n)` (block `i,j`
from the decomposition), else `0`. We first establish the two structural invariants — `g l n m` is
`NF`, and `repr (g l n m) < ω^(l+1)` (values stay below `ω^(l+1)`, the fact that lets each block term
nest as an `oadd` with leading exponent `l+1`). The two Lemma-3.3 *properties* (descent + the
`C ≤ K·(n+m+1)` bound) build on these next. -/

/-- Rathjen's `g` for the hierarchy `F`. -/
def g : ℕ → ℕ → ℕ → ONote
  | 0,     n, m => g0 n m
  | l + 1, n, m =>
      if m < F (l + 1) n then
        blk (l + 1) (n - blockIdx (F l) n m).toPNat'
          (g l ((F l)^[blockIdx (F l) n m] n) (blockOff (F l) n m))
      else 0

@[simp] theorem g_zero (n m : ℕ) : g 0 n m = g0 n m := rfl

theorem g_succ_of_lt {l n m : ℕ} (h : m < F (l + 1) n) :
    g (l + 1) n m = blk (l + 1) (n - blockIdx (F l) n m).toPNat'
      (g l ((F l)^[blockIdx (F l) n m] n) (blockOff (F l) n m)) := by
  simp only [g, if_pos h]

theorem g_succ_of_ge {l n m : ℕ} (h : ¬ m < F (l + 1) n) : g (l + 1) n m = 0 := by
  simp only [g, if_neg h]

/-- **Value bound invariant**: `repr (g l n m) < ω^(l+1)`. Base: `g₀` is a finite ordinal `< ω`.
Step: `ω^(l+1)·c + (tail < ω^(l+1)) < ω^(l+1)·(c+1) < ω^(l+1)·ω = ω^(l+2)`. -/
theorem g_lt : ∀ (l n m : ℕ), (g l n m).repr < (ω : Ordinal) ^ (l + 1) := by
  intro l
  induction l with
  | zero =>
    intro n m
    rw [g_zero, g0, ONote.repr_ofNat, pow_one]
    exact_mod_cast Ordinal.natCast_lt_omega0 _
  | succ l ih =>
    intro n m
    by_cases h : m < F (l + 1) n
    · rw [g_succ_of_lt h, repr_blk]
      set c : ℕ := ((n - blockIdx (F l) n m).toPNat' : ℕ) with hc
      set r : Ordinal := (g l ((F l)^[blockIdx (F l) n m] n) (blockOff (F l) n m)).repr with hr
      have hrlt : r < (ω : Ordinal) ^ (l + 1) := ih _ _
      calc (ω : Ordinal) ^ (l + 1) * (c : ℕ) + r
          < (ω : Ordinal) ^ (l + 1) * (c : ℕ) + (ω : Ordinal) ^ (l + 1) :=
            (add_lt_add_iff_left _).2 hrlt
        _ = (ω : Ordinal) ^ (l + 1) * ((c : ℕ) + 1) := by rw [mul_add, mul_one]
        _ < (ω : Ordinal) ^ (l + 1) * ω :=
            (mul_lt_mul_iff_of_pos_left (pow_pos Ordinal.omega0_pos _)).2
              (by exact_mod_cast Ordinal.natCast_lt_omega0 ((c : ℕ) + 1))
        _ = (ω : Ordinal) ^ (l + 1 + 1) := (pow_succ _ _).symm
    · rw [g_succ_of_ge h, ONote.repr_zero]
      exact pow_pos Ordinal.omega0_pos _

/-- **`NF` invariant**: every `g l n m` is in normal form. Uses `g_lt` to show the tail nests
below the leading exponent `ofNat (l+1)`. -/
theorem g_NF : ∀ (l n m : ℕ), (g l n m).NF := by
  intro l
  induction l with
  | zero => intro n m; rw [g_zero]; exact g0_NF n m
  | succ l ih =>
    intro n m
    by_cases h : m < F (l + 1) n
    · rw [g_succ_of_lt h]
      refine ONote.NF.oadd inferInstance _ (ONote.NF.below_of_lt' ?_ (ih _ _))
      rw [ONote.repr_ofNat]
      exact_mod_cast g_lt l _ _
    · rw [g_succ_of_ge h]; exact ONote.NF.zero

/-- `f^[i] n ≤ n + psum f n i` (for `i ≥ 1` the iterate is itself a summand of `psum`). -/
theorem iter_le_add_psum (f : ℕ → ℕ) (n i : ℕ) : f^[i] n ≤ n + psum f n i := by
  cases i with
  | zero => simp
  | succ i => rw [psum_succ]; omega

/-- Block bookkeeping for the bound: `f^[i] n + j ≤ n + m` where `i,j` is `m`'s block decomposition. -/
theorem iter_add_blockOff_le (l n m : ℕ) :
    (F l)^[blockIdx (F l) n m] n + blockOff (F l) n m ≤ n + m := by
  have h1 := iter_le_add_psum (F l) n (blockIdx (F l) n m)
  have h2 := psum_add_blockOff (F l) n m
  omega

/-- `(x.toPNat' : ℕ) ≤ x + 1` (equals `x` when `x>0`, else `1`). -/
theorem toPNat'_le_succ (x : ℕ) : ((x.toPNat' : ℕ)) ≤ x + 1 := by
  rcases Nat.eq_zero_or_pos x with h | h
  · subst h; simp [Nat.toPNat']
  · rw [PNat.toPNat'_coe h]; omega

/-- **Lemma 3.3(2) — the coefficient bound.** For each level `l` there is a constant `K` with
`C (g l n m) ≤ K·(n+m+1)` for all `n,m`. Induction on `l`: base `K=2` (`g₀_bound`); step takes
`max (l+1) K`, since the new leading data (`l+1`, the coefficient `n-i ≤ n`) and the tail's bound
`K·(f^[i] n + j + 1) ≤ K·(n+m+1)` (by `iter_add_blockOff_le`) are each `≤ max(l+1,K)·(n+m+1)`. -/
theorem g_C_bound : ∀ l, ∃ K, ∀ n m, C (g l n m) ≤ K * (n + m + 1) := by
  intro l
  induction l with
  | zero => exact ⟨2, fun n m => g0_bound n m⟩
  | succ l ih =>
    obtain ⟨K, hK⟩ := ih
    refine ⟨max (l + 1) K, fun n m => ?_⟩
    set M := max (l + 1) K with hM
    have hW : 1 ≤ n + m + 1 := by omega
    have hMpos : 1 ≤ M := by rw [hM]; omega
    by_cases h : m < F (l + 1) n
    · rw [g_succ_of_lt h, C_blk]
      -- the three pieces, each ≤ M*(n+m+1)
      have hA : l + 1 ≤ M * (n + m + 1) :=
        le_trans (le_max_left _ _) (Nat.le_mul_of_pos_right M hW)
      have hB : ((n - blockIdx (F l) n m).toPNat' : ℕ) ≤ M * (n + m + 1) := by
        have h1 : ((n - blockIdx (F l) n m).toPNat' : ℕ) ≤ n + m + 1 :=
          le_trans (toPNat'_le_succ _) (by omega)
        exact le_trans h1 (Nat.le_mul_of_pos_left _ hMpos)
      have hC : C (g l ((F l)^[blockIdx (F l) n m] n) (blockOff (F l) n m)) ≤ M * (n + m + 1) := by
        have hbnd := hK ((F l)^[blockIdx (F l) n m] n) (blockOff (F l) n m)
        have hle := iter_add_blockOff_le l n m
        calc C (g l ((F l)^[blockIdx (F l) n m] n) (blockOff (F l) n m))
            ≤ K * ((F l)^[blockIdx (F l) n m] n + blockOff (F l) n m + 1) := hbnd
          _ ≤ K * (n + m + 1) := Nat.mul_le_mul_left _ (by omega)
          _ ≤ M * (n + m + 1) := Nat.mul_le_mul_right _ (le_max_right _ _)
      omega
    · rw [g_succ_of_ge h, C_zero]; exact Nat.zero_le _

/-! ## The `ω^k·β` multiplier (Cor 3.4's lead term)

Cor 3.4 sets `α = ω^ω·βₙ + g(n,m)`. Since at a fixed level `l` we have `g l n m < ω^(l+1)`
(`g_lt`), it suffices to lift `β` by `ω^(l+1)` (not `ω^ω`), keeping `g` as a clean tail below the
lifted exponents. `bigMul k β = (ω·)^[k] β = ω^k·β`, built by iterating DescentCore's `ω·` so its
`C`/`repr`/`NF` laws come straight from the single-`ω` lemmas. -/

/-- `ω^k · β`, as iterated multiplication by `ω`. -/
def bigMul (k : ℕ) (β : ONote) : ONote := (fun b => GoodsteinPA.Dom.omegaO * b)^[k] β

@[simp] theorem bigMul_zero (β : ONote) : bigMul 0 β = β := rfl

theorem bigMul_succ (k : ℕ) (β : ONote) :
    bigMul (k + 1) β = GoodsteinPA.Dom.omegaO * bigMul k β :=
  Function.iterate_succ_apply' _ _ _

/-- `ω^k·β` is normal form when `β` is. -/
theorem NF_bigMul (k : ℕ) {β : ONote} (hβ : β.NF) : (bigMul k β).NF := by
  induction k with
  | zero => simpa using hβ
  | succ k ih =>
    rw [bigMul_succ]
    exact @ONote.mul_nf GoodsteinPA.Dom.omegaO (bigMul k β) GoodsteinPA.Dom.NF_omegaO ih

/-- `repr (ω^k·β) = ω^k · repr β`. -/
theorem repr_bigMul (k : ℕ) {β : ONote} (hβ : β.NF) :
    (bigMul k β).repr = (ω : Ordinal) ^ k * β.repr := by
  induction k with
  | zero => simp
  | succ k ih =>
    haveI := NF_bigMul k hβ
    haveI := GoodsteinPA.Dom.NF_omegaO
    rw [bigMul_succ, ONote.repr_mul, GoodsteinPA.Dom.repr_omegaO, ih, ← mul_assoc,
      ← pow_succ' ω k]

/-- `C (ω^k·β) ≤ C β + k` (each `ω·` bumps the max coefficient by at most one). -/
theorem C_bigMul_le (k : ℕ) (β : ONote) : C (bigMul k β) ≤ C β + k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [bigMul_succ]
    exact le_trans (GoodsteinPA.Dom.C_omega_mul_le (bigMul k β)) (by omega)

/-! ## Clean-append `C`-bound (`ω^(l+1)·β + g`, with `g` strictly below)

For slowness we need `C (α j) = C (ω^(l+1)·β_n + g) ≤ max …`. Because every exponent of `g` is
`< l+1 ≤` every exponent of `ω^(l+1)·β`, the addition appends `g` as a pure tail with no coefficient
merge, so `C (a + b) ≤ max (C a) (C b)`. `AllExpAbove b a` records "every exponent of `a` dominates
`b`" (recursively), which is exactly the clean-append condition. -/

/-- `b`'s value is below `ω^e` for every leading exponent `e` occurring in `a` (so `a + b` appends
without merging coefficients). -/
def AllExpAbove (b : ONote) : ONote → Prop
  | 0 => True
  | ONote.oadd e _ a' => b.repr < (ω : Ordinal) ^ (ONote.repr e) ∧ AllExpAbove b a'

/-- **Clean-append bound.** If every exponent of `a` dominates `b`, then `a + b` is `a` with `b`
grafted as its tail, so `C (a + b) ≤ max (C a) (C b)`. -/
theorem C_add_clean : ∀ {a : ONote}, a.NF → ∀ {b : ONote}, b.NF → AllExpAbove b a →
    C (a + b) ≤ max (C a) (C b)
  | 0, _, b, _, _ => by rw [ONote.zero_add, C_zero]; exact le_max_right _ _
  | ONote.oadd e n a', hNF, b, hb, hab => by
    obtain ⟨hbe, hab'⟩ := hab
    have hNFe : e.NF := hNF.fst
    have hNFa' : a'.NF := hNF.snd
    have ih := C_add_clean hNFa' hb hab'
    have hbelow : ONote.NFBelow (a' + b) (ONote.repr e) :=
      ONote.add_nfBelow hNF.snd' (ONote.NF.below_of_lt' hbe hb)
    have hadd : ONote.oadd e n a' + b = ONote.oadd e n (a' + b) := by
      rw [ONote.oadd_add]
      cases h : a' + b with
      | zero => simp [ONote.addAux]
      | oadd e'' n'' a'' =>
        have hbXo := h ▸ hbelow
        have hNFe'' : e''.NF := hbXo.fst
        have hlt : ONote.repr e'' < ONote.repr e := hbXo.lt
        have hcmp : ONote.cmp e e'' = Ordering.gt := by
          have hc := @ONote.cmp_compares e e'' hNFe hNFe''
          rcases hco : ONote.cmp e e'' with _ | _ | _
          · rw [hco] at hc; exact absurd (ONote.lt_def.1 hc) (not_lt.2 hlt.le)
          · rw [hco] at hc; exact absurd (congrArg ONote.repr hc) (ne_of_gt hlt)
          · rfl
        simp [ONote.addAux, hcmp]
    rw [hadd, C_oadd, C_oadd]
    omega

/-- **Lemma 3.3(1) — descent.** `g l n (m+1) ≺ g l n m` whenever `m < F l n`. Base: `g₀_desc`.
Step (`l+1`): decompose `m`'s block `i, j`; the increment `m ↦ m+1` either stays in block `i`
(`blockOff` becomes `j+1`, descent by the IH via `repr_blk_within`) or crosses into block `i+1`
(`blockOff` resets to `0`, descent via `repr_blk_boundary` since the lead coefficient `n-i` drops and
the next tail is `< ω^(l+1)` by `g_lt`); if `m+1` exhausts all blocks, `g l n (m+1) = 0 ≺ g l n m`. -/
theorem g_desc : ∀ (l n m : ℕ), m < F l n → (g l n (m + 1)).repr < (g l n m).repr := by
  intro l
  induction l with
  | zero => intro n m hm; rw [g_zero, g_zero]; exact g0_desc n m hm
  | succ l ih =>
    intro n m hm
    have hn : 1 ≤ n := by
      rcases Nat.eq_zero_or_pos n with h0 | h0
      · subst h0; simp [F_succ] at hm
      · exact h0
    have hmpsum : m < psum (F l) n n := lt_of_lt_of_le hm (F_succ_le_psum l hn)
    have hilt : blockIdx (F l) n m < n := blockIdx_lt (F l) hn hmpsum
    have hlo : psum (F l) n (blockIdx (F l) n m) ≤ m := psum_blockIdx_le (F l) n m
    have hhi : m < psum (F l) n (blockIdx (F l) n m + 1) := lt_psum_blockIdx_succ (F l) hn hmpsum
    have hjval : psum (F l) n (blockIdx (F l) n m) + blockOff (F l) n m = m :=
      psum_add_blockOff (F l) n m
    have hwidth : blockOff (F l) n m < (F l)^[blockIdx (F l) n m + 1] n :=
      blockOff_lt_width (F l) hn hmpsum
    rw [g_succ_of_lt hm]
    set i := blockIdx (F l) n m with hi
    set j := blockOff (F l) n m with hj
    by_cases hm1 : m + 1 < F (l + 1) n
    · rw [g_succ_of_lt hm1]
      by_cases hbnd : m + 1 < psum (F l) n (i + 1)
      · -- within block i: blockIdx(m+1) = i, blockOff(m+1) = j+1
        have hidx1 : blockIdx (F l) n (m + 1) = i :=
          blockIdx_eq l hn (le_of_lt hilt) (by omega) hbnd
        have hoff1 : blockOff (F l) n (m + 1) = j + 1 := by
          simp only [blockOff, hidx1]; omega
        rw [hidx1, hoff1]
        apply repr_blk_within
        have hcond : j < F l ((F l)^[i] n) := by
          rw [← Function.iterate_succ_apply' (F l) i n]; exact hwidth
        exact ih ((F l)^[i] n) j hcond
      · -- boundary: m+1 = psum(i+1), blockIdx(m+1) = i+1, blockOff(m+1) = 0
        push_neg at hbnd
        have hb_eq : m + 1 = psum (F l) n (i + 1) := by omega
        have hidx1 : blockIdx (F l) n (m + 1) = i + 1 := by
          refine blockIdx_eq l hn (by omega) (by omega) ?_
          rw [hb_eq]
          exact psum_strictMono l hn (Nat.lt_succ_self _)
        have hi1lt : i + 1 < n := by
          rw [← hidx1]
          exact blockIdx_lt (F l) hn (lt_of_lt_of_le hm1 (F_succ_le_psum l hn))
        have hoff1 : blockOff (F l) n (m + 1) = 0 := by
          simp only [blockOff, hidx1]; omega
        rw [hidx1, hoff1]
        apply repr_blk_boundary
        · rw [PNat.toPNat'_coe (by omega : 0 < n - (i + 1)),
            PNat.toPNat'_coe (by omega : 0 < n - i)]
          omega
        · exact g_lt l _ _
    · -- m+1 exhausts all blocks: g(l+1) n (m+1) = 0
      rw [g_succ_of_ge hm1, ONote.repr_zero, repr_blk]
      have hcpos : (0 : Ordinal) < ((n - i).toPNat' : ℕ) := by
        rw [PNat.toPNat'_coe (by omega : 0 < n - i)]
        exact_mod_cast (by omega : 0 < n - i)
      have hc : (0 : Ordinal) < (ω : Ordinal) ^ (l + 1) * ((n - i).toPNat' : ℕ) :=
        Left.mul_pos (pow_pos Ordinal.omega0_pos _) hcpos
      exact lt_of_lt_of_le hc le_self_add

end GoodsteinPA.Grz
