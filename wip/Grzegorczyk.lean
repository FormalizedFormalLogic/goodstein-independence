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

/-! ### Why the §3 slow-down does NOT run on an arbitrary `X`-definable descent (Lemma 3.2 is
primrec-only) — machine-checked obstruction

Rathjen's **Lemma 3.2** (the Grzegorczyk domination theorem) gives, *for every primitive recursive*
`h`, a level `l` with `h ≤ f_l`. It is **false for non-primitive-recursive `h`**: the hierarchy is
level-bounded, so its own diagonal `n ↦ F n n` escapes *every* fixed level. The lap-27+ E-reduction
tried to run Cor 3.4 on the **`X`-definable** descent, whose block-width / coefficient-growth function
`w n = C(β (n+1))` is an arbitrary `X`-definable (oracle) function, not primitive recursive. Its
domination obligation has exactly the shape `∃ l, ∀ n, w n ≤ F l n` — and the lemmas below certify, in
the kernel, that this **cannot hold once `w` is diagonal-fast** (`w n ≥ F n n + 1`). This is the precise,
machine-checked sense in which the X-definable slow-down is *blocked*, not merely hard (the structural
reason Rathjen restricts §3 to primitive-recursive sequences, and Route A — `Goodstein → primrec-PRWO(ε₀)
→ Con(PA)` via Gödel II — is his actual proof). See `E-ARCHITECTURE-REVIEW-2026-06-23.md`.

NB: realizing a *specific* `X`-definable descent with diagonal-fast `C`-growth is model-theoretic
(a nonstandard `M ⊧ paLX` + an oracle `X`) and is NOT claimed here; what is certified is the hierarchy
fact that makes the domination obligation unsatisfiable for any such descent. -/

/-- **Grzegorczyk domination is level-bounded** (the formal core of "Lemma 3.2 is primrec-only"):
any function `w` that dominates the diagonal `n ↦ F n n` is itself dominated by **no** fixed level
`F l`. Witness: at `n = l`, `F l l < F l l + 1 ≤ w l ≤ F l l` is a contradiction. -/
theorem not_dominated_of_diag_le {w : ℕ → ℕ} (hw : ∀ n, F n n + 1 ≤ w n) :
    ¬ ∃ l, ∀ n, w n ≤ F l n := by
  rintro ⟨l, h⟩
  have h1 := hw l
  have h2 := h l
  omega

/-- **The Grzegorczyk diagonal escapes every level**: `n ↦ F n n + 1` is dominated by no `F l`. The
specialization of `not_dominated_of_diag_le` at `w = F n n + 1`. This is exactly the negation of the
`xDescent_domination`-shaped obligation `∃ l, ∀ n, w n ≤ F l n` for a diagonal-fast width function. -/
theorem F_diag_not_dominated : ¬ ∃ l, ∀ n, F n n + 1 ≤ F l n :=
  not_dominated_of_diag_le (fun _ => le_refl _)

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
  push Not at hc
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
  push Not at hc
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

/-- Every exponent of `a` has `repr ≥ k` (recursively). `bigMul (l+1) β` satisfies `MinExpGe (l+1)`. -/
def MinExpGe (k : ℕ) : ONote → Prop
  | 0 => True
  | ONote.oadd e _ a' => (k : Ordinal) ≤ ONote.repr e ∧ MinExpGe k a'

theorem MinExpGe_zero : ∀ (a : ONote), MinExpGe 0 a
  | 0 => trivial
  | ONote.oadd _ _ a' => ⟨bot_le, MinExpGe_zero a'⟩

/-- `ω·` bumps every exponent's `repr` by `1`, so `MinExpGe k o → MinExpGe (k+1) (ω·o)`. -/
theorem MinExpGe_omega_mul {k : ℕ} : ∀ {o : ONote}, o.NF → MinExpGe k o →
    MinExpGe (k + 1) (GoodsteinPA.Dom.omegaO * o)
  | 0, _, _ => by simp [GoodsteinPA.Dom.omegaO, MinExpGe]
  | ONote.oadd e₂ n₂ a₂, hNF, hm => by
    obtain ⟨hke, hma⟩ := hm
    have hNFe : e₂.NF := hNF.fst
    have hNFa : a₂.NF := hNF.snd
    rw [show GoodsteinPA.Dom.omegaO = ONote.oadd 1 1 0 from rfl, ONote.oadd_mul]
    by_cases e0 : e₂ = 0
    · subst e0
      have hk0 : k = 0 := by
        simp only [ONote.repr_zero] at hke
        exact_mod_cast (nonpos_iff_eq_zero.1 hke)
      subst hk0
      simp only [↓reduceIte]
      exact ⟨by simp, trivial⟩
    · simp only [e0, ↓reduceIte]
      refine ⟨?_, MinExpGe_omega_mul hNFa hma⟩
      have hadd : ONote.repr ((1 : ONote) + e₂) = 1 + ONote.repr e₂ := by
        haveI := hNFe; rw [ONote.repr_add, ONote.repr_one]; norm_num
      rw [hadd, show ((k + 1 : ℕ) : Ordinal) = 1 + (k : Ordinal) by
        rw [show k + 1 = 1 + k from Nat.add_comm k 1, Nat.cast_add, Nat.cast_one]]
      gcongr

theorem MinExpGe_bigMul (k : ℕ) {β : ONote} (hβ : β.NF) : MinExpGe k (bigMul k β) := by
  induction k with
  | zero => exact MinExpGe_zero _
  | succ k ih => rw [bigMul_succ]; exact MinExpGe_omega_mul (NF_bigMul k hβ) ih

theorem AllExpAbove_of_MinExpGe {b : ONote} {k : ℕ} (hb : b.repr < (ω : Ordinal) ^ (k : ℕ)) :
    ∀ {a : ONote}, MinExpGe k a → AllExpAbove b a
  | 0, _ => trivial
  | ONote.oadd e _ a', hm => by
    obtain ⟨hke, hma⟩ := hm
    refine ⟨lt_of_lt_of_le hb ?_, AllExpAbove_of_MinExpGe hb hma⟩
    rw [← Ordinal.opow_natCast]
    exact Ordinal.opow_le_opow_right Ordinal.omega0_pos hke

/-- `AllExpAbove b (ω^k·β)` whenever `b < ω^k` — the clean-append condition for the Cor 3.4 sum. -/
theorem AllExpAbove_bigMul {b β : ONote} (hβ : β.NF) {k : ℕ}
    (hb : b.repr < (ω : Ordinal) ^ (k : ℕ)) : AllExpAbove b (bigMul k β) :=
  AllExpAbove_of_MinExpGe hb (MinExpGe_bigMul k hβ)

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
        push Not at hbnd
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

/-! ## Corollary 3.4 — the slowed sequence `α` (C-based, repo variant) and its slowness bound

Rathjen sets `αⱼ = ω^ω·βₙ + g(n,m)` over blocks of width `|β_{n+1}|`. Since at level `l` we have
`g l n m < ω^(l+1)` (`g_lt`), the lead lift `ω^(l+1)·βₙ` (= `bigMul (l+1) (β n)`) suffices, and the repo
variant carves the index `j` into blocks of **C-based** width `W n = C(β_{n+1})` (the lap-44-flagged
collapse of Rathjen's length `|·|` onto `C`). The block of `j` is `n = widx W (j+1) j`, the within-block
offset `m = woff W (j+1) j`.

The **slowness bound** `C(αⱼ) ≤ K·(j+1)` (this section) is the de-risking-critical piece: it is exactly
where the C-collapse must close, and it is **domination-free and prefix-free**, so it verifies the C
arithmetic of Cor 3.4 outright. (The descent property — which DOES need the domination `C(β_{n+1}) ≤ F l n`
and Rathjen's finite prefix at `n=0` — is the next brick.) -/

/-- C-based block width for the descent side: `W n = C (β_{n+1})`. -/
def corW (β : ℕ → ONote) (t : ℕ) : ℕ := C (β (t + 1))

/-- The block index of `j` (largest `n` with `Σ_{t<n} C(β_{t+1}) ≤ j`). -/
def corBlk (β : ℕ → ONote) (j : ℕ) : ℕ := widx (corW β) (j + 1) j

/-- The within-block offset of `j`. -/
def corOff (β : ℕ → ONote) (j : ℕ) : ℕ := woff (corW β) (j + 1) j

/-- **Cor 3.4 slowed sequence (within-block term).** `αⱼ = ω^(l+1)·β_n + g l n m`. -/
def corAlpha (l : ℕ) (β : ℕ → ONote) (j : ℕ) : ONote :=
  bigMul (l + 1) (β (corBlk β j)) + g l (corBlk β j) (corOff β j)

theorem wsum_corBlk_le (β : ℕ → ONote) (j : ℕ) :
    wsum (corW β) (corBlk β j) ≤ j := wsum_widx_le (corW β) (j + 1) j

theorem wsum_add_corOff (β : ℕ → ONote) (j : ℕ) :
    wsum (corW β) (corBlk β j) + corOff β j = j := wsum_add_woff (corW β) (j + 1) j

/-- `C(β n) ≤ Σ_{t<n} C(β_{t+1})` for `n ≥ 1`: `C(β n) = W(n-1)` is one summand of `wsum`. -/
theorem C_le_wsum_corW (β : ℕ → ONote) {n : ℕ} (hn : 1 ≤ n) :
    C (β n) ≤ wsum (corW β) n := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  rw [wsum_succ]
  have hcorW : corW β n' = C (β (n' + 1)) := rfl
  omega

/-- `A + j ≤ A·(j+1)` for `A ≥ 1` (absorbing a constant `A` into the linear bound). -/
theorem const_add_le_mul {A j : ℕ} (hA : 1 ≤ A) : A + j ≤ A * (j + 1) := by
  have h1 : j ≤ A * j := Nat.le_mul_of_pos_left j hA
  have h2 : A * (j + 1) = A * j + A := by ring
  omega

/-- **Cor 3.4 — slowness.** `C(αⱼ) ≤ K·(j+1)`, with `K = max (C(β 0)+(l+1)) K_g`. Domination-free,
prefix-free: the clean-append `C_add_clean` (every exponent of `ω^(l+1)·β_n` dominates `g l n m < ω^(l+1)`)
splits `C` into `max (C(ω^(l+1)·β_n)) (C(g l n m))`; the lead is `≤ C(β_n)+(l+1)` (`C_bigMul_le`) with
`C(β_n) ≤ wsum ≤ j` for `n ≥ 1` (else the `C(β 0)` constant is absorbed into `K`); the tail is
`≤ K_g·(n+m+1) ≤ K_g·(j+1)` since `n+m ≤ j`. This is the C-collapse, machine-verified. -/
theorem corAlpha_C_bound (l : ℕ) {β : ℕ → ONote} (hβNF : ∀ n, (β n).NF)
    (hWpos : ∀ t, 1 ≤ corW β t) :
    ∃ K, ∀ j, C (corAlpha l β j) ≤ K * (j + 1) := by
  obtain ⟨Kg, hKg⟩ := g_C_bound l
  refine ⟨max (C (β 0) + (l + 1)) Kg, fun j => ?_⟩
  set n := corBlk β j with hn
  set m := corOff β j with hm
  set K := max (C (β 0) + (l + 1)) Kg with hKdef
  -- block bookkeeping
  have hwle : wsum (corW β) n ≤ j := wsum_corBlk_le β j
  have hadd : wsum (corW β) n + m = j := wsum_add_corOff β j
  have hnwsum : n ≤ wsum (corW β) n := le_wsum (corW β) hWpos n
  have hnmj : n + m ≤ j := by omega
  -- clean-append split of `C`
  have hclean : C (corAlpha l β j) ≤ max (C (bigMul (l + 1) (β n))) (C (g l n m)) :=
    C_add_clean (NF_bigMul (l + 1) (hβNF n)) (g_NF l n m)
      (AllExpAbove_bigMul (hβNF n) (g_lt l n m))
  refine le_trans hclean (max_le ?_ ?_)
  · -- lead: `C(ω^(l+1)·β_n) ≤ C(β_n)+(l+1) ≤ (C(β 0)+(l+1)) + j ≤ K·(j+1)`
    have h1 : C (bigMul (l + 1) (β n)) ≤ C (β n) + (l + 1) := C_bigMul_le (l + 1) (β n)
    have h2 : C (β n) ≤ C (β 0) + j := by
      rcases Nat.eq_zero_or_pos n with h0 | h0
      · rw [h0]; omega
      · exact le_trans (C_le_wsum_corW β h0) (by omega)
    have hKge : C (β 0) + (l + 1) ≤ K := le_max_left _ _
    have hK1 : 1 ≤ K := by omega
    calc C (bigMul (l + 1) (β n)) ≤ C (β n) + (l + 1) := h1
      _ ≤ (C (β 0) + (l + 1)) + j := by omega
      _ ≤ K + j := by omega
      _ ≤ K * (j + 1) := const_add_le_mul hK1
  · -- tail: `C(g l n m) ≤ K_g·(n+m+1) ≤ K_g·(j+1) ≤ K·(j+1)`
    calc C (g l n m) ≤ Kg * (n + m + 1) := hKg n m
      _ ≤ Kg * (j + 1) := Nat.mul_le_mul_left Kg (by omega)
      _ ≤ K * (j + 1) := Nat.mul_le_mul_right (j + 1) (le_max_right _ _)

/-! ## Cor 3.4 — the descent STEP lemmas (the non-vacuous, M-portable core)

The global `∀ j, αⱼ₊₁ ≺ αⱼ` is **vacuous in ℕ** (ε₀ is well-founded, so no infinite input descent `β`
exists) and its assembly is tangled by Rathjen's `n=0` finite prefix (for `l ≥ 1`, `F l 0 = 0`, so the
width hypothesis `1 ≤ C(β_1)` and the domination `C(β_1) ≤ F l 0` are jointly contradictory — the prefix
exists precisely to skip this). What is **non-vacuous and ports verbatim to the M-internal codes** is the
per-step descent logic, in two cases: within a block (lead `ω^(l+1)·β_n` fixed, `g` tail descends) and
across a block boundary (`β_{n+1} ≺ β_n` drops the lead, the `g`-tail `< ω^(l+1)` is absorbed). These are
the genuine mathematical content of Cor 3.4's descent; the index/prefix bookkeeping is deferred to the
M-internal construction (where the descent is a real non-standard infinite one and Lemma 3.2's `max(2,·)`
indexing supplies a non-degenerate domination). -/

/-- **Within-block descent step.** Fixed lead `ω^(l+1)·β_n`; the `g`-tail descends (`m < F l n`). -/
theorem corAlpha_within (l n m : ℕ) {β : ℕ → ONote} (hβNF : (β n).NF) (hm : m < F l n) :
    (bigMul (l + 1) (β n) + g l n (m + 1)).repr < (bigMul (l + 1) (β n) + g l n m).repr := by
  haveI := NF_bigMul (l + 1) hβNF
  haveI := g_NF l n m
  haveI := g_NF l n (m + 1)
  rw [ONote.repr_add, ONote.repr_add]
  exact (add_lt_add_iff_left _).2 (g_desc l n m hm)

/-- **Block-boundary descent step.** `β_{n+1} ≺ β_n` drops the lead `ω^(l+1)·β`; the new `g`-tail
`g l (n+1) m' < ω^(l+1)` (`g_lt`) is absorbed (`mul_add_lt`). Holds for ANY offsets `m`, `m'`. -/
theorem corAlpha_boundary (l n m m' : ℕ) {β : ℕ → ONote}
    (hβNFn : (β n).NF) (hβNFn1 : (β (n + 1)).NF)
    (hβdesc : (β (n + 1)).repr < (β n).repr) :
    (bigMul (l + 1) (β (n + 1)) + g l (n + 1) m').repr
      < (bigMul (l + 1) (β n) + g l n m).repr := by
  haveI := NF_bigMul (l + 1) hβNFn
  haveI := NF_bigMul (l + 1) hβNFn1
  haveI := g_NF l n m
  haveI := g_NF l (n + 1) m'
  rw [ONote.repr_add, ONote.repr_add, repr_bigMul (l + 1) hβNFn, repr_bigMul (l + 1) hβNFn1]
  exact mul_add_lt hβdesc (g_lt l (n + 1) m')

end GoodsteinPA.Grz
