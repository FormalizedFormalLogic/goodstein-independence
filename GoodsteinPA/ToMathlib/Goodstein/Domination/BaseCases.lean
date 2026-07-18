/-
# Goodstein.Dom — BaseCases
-/
module

public import Mathlib.Algebra.Order.SuccPred
public import Mathlib.SetTheory.Ordinal.Exponential
public import Mathlib.SetTheory.Ordinal.Notation
public import Mathlib.Tactic.Ring
public import GoodsteinPA.ToMathlib.Goodstein.Defs
public import GoodsteinPA.ToMathlib.Hardy
public import GoodsteinPA.ToMathlib.Goodstein.Domination.Diagonal

@[expose] public section

namespace Goodstein.Dom

open ONote Ordinal

/-
# `GoodsteinLike` sequences and the self-similarity TOWER

Lap 9 found the winning idea — **self-similarity**: the leading-exponent sequence
`L_k = log_{base k}(G_k)` of a Goodstein descent is *itself* a Goodstein-like descent, so it
dominates the genuine Goodstein sequence seeded at `L_0 = log₂ m`. Lap 10 closed `o = ω` by iterating
that idea once. This file extracts the idea into its **clean reusable abstraction** and proves the
*fully iterated* form, the engine for climbing the ordinal tower toward `f_{ε₀}`.

A sequence `a : ℕ → ℕ` is `GoodsteinLike` when it obeys the Goodstein lower-bound recursion
`a (k+1) ≥ bump (base k) (a k) − 1` at every step (the genuine `goodsteinSeq` obeys it with equality).
Two structural facts hold for every such sequence:

* **`GoodsteinLike.dominates`** — `a` dominates `goodsteinSeq (a 0)` (self-similarity: the recursion
  with the `−1` firing at every step is the slowest, so `goodsteinSeq (a 0)` is a lower envelope).
* **`GoodsteinLike.logSeq`** — `k ↦ log_{base k} (a k)` is again `GoodsteinLike` (the leading exponent
  of a Goodstein-like sequence is Goodstein-like — the level-up that drives the tower).

Iterating the second fact (`GoodsteinLike.iterate`) and feeding the first gives the headline
**`iterLeadExp_dominates`**: the `j`-fold iterated leading exponent of the seed-`m` descent dominates
the Goodstein sequence seeded at the `j`-fold logarithm `(log₂)^[j] m`. For `j = 0` this is the value
itself; `j = 1` is lap-9's `leadExp_ge_goodsteinSeq_log`; each higher `j` is one ordinal level up
(`o = ω^j`-flavoured), the precise self-reference behind Cichoń's lower bound at the limit levels.
-/


/-- **General per-step log descent.** For any `n`, the leading exponent obeys the Goodstein recursion
as a *lower bound*: `bump b (log_b n) − 1 ≤ log_{b+1} (bump b n − 1)`. Off pure powers it is an
equality at `bump b (log_b n)` (`log_bump_pred_of_not_pow`); at a pure power it drops by exactly one
(`log_bump_pred_of_pow`); when `n = 0` both sides are `0`. Generalizes `leadExp_step_ge` from the
concrete Goodstein value to an arbitrary `n` — the brick that makes `log ∘ a` Goodstein-like. -/
theorem log_step_ge (b : ℕ) (hb : 2 ≤ b) (n : ℕ) :
    bump b (Nat.log b n) - 1 ≤ Nat.log (b + 1) (bump b n - 1) := by
  rcases eq_or_ne n 0 with hv0 | hv0
  · rw [hv0]; simp
  · by_cases hpp : b ^ Nat.log b n = n
    · rcases Nat.eq_zero_or_pos (Nat.log b n) with he0 | hepos
      · rw [he0, bump_zero]; omega
      · rw [log_bump_pred_of_pow b hb hepos hpp.symm]
    · have hlt : b ^ Nat.log b n < n := by
        have hle := Nat.pow_log_le_self b hv0; omega
      rw [log_bump_pred_of_not_pow b hb hv0 hlt]; omega

/-- A sequence is **Goodstein-like** when it obeys the Goodstein lower-bound recursion at every step:
`a (k+1) ≥ bump (base k) (a k) − 1`. The genuine `goodsteinSeq m` obeys it with equality. -/
def GoodsteinLike (a : ℕ → ℕ) : Prop := ∀ k, bump (base k) (a k) - 1 ≤ a (k + 1)

/-- The leading-exponent operator: `logSeq a k = log_{base k} (a k)`. -/
def logSeq (a : ℕ → ℕ) : ℕ → ℕ := fun k => Nat.log (base k) (a k)

/-- The genuine Goodstein sequence is Goodstein-like (with equality, by definition of the step). -/
theorem goodsteinSeq_goodsteinLike (m : ℕ) : GoodsteinLike (goodsteinSeq m) :=
  fun _ => le_of_eq rfl

/-- **Self-similarity, abstract form.** Every Goodstein-like `a` dominates the genuine Goodstein
sequence seeded at `a 0`: `goodsteinSeq (a 0) k ≤ a k` for all `k`. Induction with `bump_mono`
carrying the step — the `goodsteinSeq` recursion subtracts `1` at *every* step, while `a` does so only
where forced, so `goodsteinSeq (a 0)` is the slowest descent. Generalizes `leadExp_ge_goodsteinSeq_log`
(the case `a = leadExp = logSeq (goodsteinSeq m)`, where `a 0 = log₂ m`). -/
theorem GoodsteinLike.dominates {a : ℕ → ℕ} (ha : GoodsteinLike a) :
    ∀ k, goodsteinSeq (a 0) k ≤ a k := by
  intro k
  induction k with
  | zero => exact Nat.le_of_eq rfl
  | succ k ih =>
    have hb : 2 ≤ base k := Nat.le_add_left 2 k
    have hmono : bump (base k) (goodsteinSeq (a 0) k) ≤ bump (base k) (a k) :=
      bump_mono (base k) hb ih
    have hstep : goodsteinSeq (a 0) (k + 1) = bump (base k) (goodsteinSeq (a 0) k) - 1 := rfl
    have hak := ha k
    rw [hstep]; omega

/-- **The leading exponent of a Goodstein-like sequence is Goodstein-like.** If `a` is Goodstein-like
then so is `logSeq a = (k ↦ log_{base k} (a k))`. Per step: `log_step_ge` gives the recursion lower
bound at `bump (base k) (a k) − 1`, then monotonicity of `Nat.log` in its argument carries it through
`a (k+1) ≥ bump (base k) (a k) − 1`. This is the **level-up** that, iterated, climbs the ordinal
tower. Generalizes `leadExp_step_ge`. -/
theorem goodsteinLike_logSeq {a : ℕ → ℕ} (ha : GoodsteinLike a) : GoodsteinLike (logSeq a) := by
  intro k
  have hb : 2 ≤ base k := Nat.le_add_left 2 k
  have hbb1 : base (k + 1) = base k + 1 := by simp only [base]
  show bump (base k) (Nat.log (base k) (a k)) - 1 ≤ Nat.log (base (k + 1)) (a (k + 1))
  rw [hbb1]
  exact le_trans (log_step_ge (base k) hb (a k)) (Nat.log_mono_right (ha k))

/-- The `j`-fold iterated leading exponent of a Goodstein-like sequence is Goodstein-like. -/
theorem goodsteinLike_iterate {a : ℕ → ℕ} (ha : GoodsteinLike a) (j : ℕ) :
    GoodsteinLike (logSeq^[j] a) := by
  induction j with
  | zero => exact ha
  | succ j ih => rw [Function.iterate_succ_apply']; exact goodsteinLike_logSeq ih

/-- The seed of the `j`-fold iterated leading exponent is the `j`-fold logarithm of the original seed:
`(logSeq^[j] a) 0 = (log₂)^[j] (a 0)` (each `logSeq` reads `base 0 = 2` at index `0`). -/
theorem logSeq_iterate_zero (a : ℕ → ℕ) (j : ℕ) :
    (logSeq^[j] a) 0 = (Nat.log 2)^[j] (a 0) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    show Nat.log (base 0) ((logSeq^[j] a) 0) = Nat.log 2 ((Nat.log 2)^[j] (a 0))
    rw [show base 0 = 2 from rfl, ih]

/-- **The self-similarity TOWER (headline).** The `j`-fold iterated leading exponent of the seed-`m`
Goodstein descent dominates the Goodstein sequence seeded at the `j`-fold logarithm `(log₂)^[j] m`:
`goodsteinSeq ((log₂)^[j] m) k ≤ (logSeq^[j] (goodsteinSeq m)) k`.

* `j = 0`: the value bound `goodsteinSeq m k ≤ goodsteinSeq m k` (trivial).
* `j = 1`: lap-9's `leadExp_ge_goodsteinSeq_log` — the leading exponent dominates `goodsteinSeq (log₂ m)`.
* `j ≥ 2`: each level is one ordinal step up. To certify the descent ordinal `≥ ω^{ω^{···}}` (tower
  of height `j+1`, i.e. `o = ω^j`-flavoured) at step `≈ m`, one needs the `j`-th iterated leading
  exponent `≥ base` there, which via this bound needs `goodsteinSeq ((log₂)^[j] m) (m−2) ≥ m`, i.e. a
  length bound `goodsteinLength ((log₂)^[j] m) ≥ 2m`. The deeper seed `(log₂)^[j] m` is small, so this
  needs an increasingly strong length bound — supplied by *bootstrapping the domination already
  proved* (e.g. `f_ω(t) ≤ goodsteinLength t + 2` makes `goodsteinLength ((log₂)^[2] m) ≥ f_ω(log₂log₂m)
  ≫ 2m`). That bootstrap is the next frontier; this lemma is its reusable backbone. -/
theorem iterLeadExp_dominates (m j : ℕ) :
    ∀ k, goodsteinSeq ((Nat.log 2)^[j] m) k ≤ (logSeq^[j] (goodsteinSeq m)) k := by
  have hgl : GoodsteinLike (logSeq^[j] (goodsteinSeq m)) :=
    goodsteinLike_iterate (goodsteinSeq_goodsteinLike m) j
  have hgz : goodsteinSeq m 0 = m := rfl
  have h0 : (logSeq^[j] (goodsteinSeq m)) 0 = (Nat.log 2)^[j] m := by
    rw [logSeq_iterate_zero, hgz]
  intro k
  have hd := hgl.dominates k
  rwa [h0] at hd

/-- Anti-vacuity: at `j = 1` the tower reproduces lap-9's self-similarity verbatim. -/
example (m k : ℕ) :
    goodsteinSeq (Nat.log 2 m) k ≤ Nat.log (base k) (goodsteinSeq m k) :=
  iterLeadExp_dominates m 1 k


/-
# Cichoń's lower bound at finite levels: the unconditional closure

`Logic/Goodstein/Domination.lean` reduces the diagonal domination
`fastGrowing (ofNat n) m ≤ goodsteinLength m + 2` to **one** self-referential length bound
`goodsteinLength m ≥ 2^{m+1} + m` (`goodsteinLength_exp_lower`), via the self-similarity recursion
`leadExp_ge_goodsteinSeq_log` (the leading-exponent sequence dominates the Goodstein sequence one
scale down). That strong induction needs finitely many computational base cases — the seeds
`4 ≤ M < 16`, where the length must already be exponentially large. This file discharges them
**kernel-only** (lap 211): `le_bump` bounds the per-step drop by 1, so a checkpoint value `v` at
step `k` certifies `goodsteinLength ≥ k + v` (`glen_ge_of_seq_value`); every seed reaches the
needed `2^{M+1}+M` by step `k ≤ 4`, and the checkpoint is evaluated in the kernel by the fuel-based
structural evaluator `gvalF`/`bumpF`. The formerly-needed `native_decide` forward passes (heaviest:
a 65551-step pass for `M = 15`) are gone, so the unconditional theorems below sit on the standard
`[propext, Classical.choice, Quot.sound]` with NO `Lean.ofReduceBool`.
-/



/-- Fuel-based structural clone of `bump` (kernel-reducible). `fuel ≥ n` suffices. -/
def bumpF : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | fuel + 1, b, n =>
    if n = 0 then 0
    else
      n / b ^ Nat.log b n * (b + 1) ^ bumpF fuel b (Nat.log b n)
        + bumpF fuel b (n % b ^ Nat.log b n)

theorem bumpF_eq : ∀ fuel n, n ≤ fuel → ∀ b, bumpF fuel b n = bump b n := by
  intro fuel
  induction fuel with
  | zero =>
    intro n hn b
    have hn0 : n = 0 := by omega
    subst hn0
    rw [bumpF, bump]
    simp
  | succ fuel ih =>
    intro n hn b
    rw [bumpF, bump]
    by_cases h0 : n = 0
    · simp [h0]
    · rw [dif_neg h0, if_neg h0]
      have hlog : Nat.log b n ≤ fuel := by
        have := Nat.log_lt_self b h0; omega
      have hmod : n % b ^ Nat.log b n ≤ fuel := by
        have hb : 0 < b ^ Nat.log b n := by
          rcases Nat.eq_zero_or_pos b with hb0 | hbpos
          · subst hb0; simp [Nat.log_zero_left]
          · exact Nat.pow_pos hbpos
        have := Nat.mod_lt n hb
        have := Nat.pow_log_le_self b h0
        omega
      rw [ih _ hlog, ih _ hmod]

/-- Kernel-reducible forward Goodstein evaluator: value after `s` more steps from `(k, v)`. -/
def gvalF : ℕ → ℕ → ℕ → ℕ
  | _, v, 0 => v
  | k, v, s + 1 => gvalF (k + 1) (bumpF v (base k) v - 1) s

theorem gvalF_goodstein (M : ℕ) : ∀ s k, gvalF k (goodsteinSeq M k) s = goodsteinSeq M (k + s) := by
  intro s
  induction s with
  | zero => intro k; rfl
  | succ s ih =>
    intro k
    rw [gvalF, bumpF_eq _ _ le_rfl]
    have hstep : bump (base k) (goodsteinSeq M k) - 1 = goodsteinSeq M (k + 1) := rfl
    rw [hstep, ih (k + 1)]
    congr 1; omega

/-- Zero is absorbing for the Goodstein sequence. -/
theorem goodsteinSeq_zero_absorb (M : ℕ) {n : ℕ} (h : goodsteinSeq M n = 0) :
    ∀ i, goodsteinSeq M (n + i) = 0 := by
  intro i
  induction i with
  | zero => exact h
  | succ i ih =>
    show bump (base (n + i)) (goodsteinSeq M (n + i)) - 1 = 0
    rw [ih, bump]; simp

/-- **Survival from any checkpoint**: the sequence drops by at most 1 per step, so a value `v`
at step `k` certifies `goodsteinLength M ≥ k + v`. -/
theorem glen_ge_of_seq_value {M k v : ℕ} (hv : 1 ≤ v) (h : goodsteinSeq M k = v) :
    k + v ≤ goodsteinLength M := by
  have hsub : ∀ j, v - j ≤ goodsteinSeq M (k + j) := by
    intro j
    induction j with
    | zero => rw [Nat.add_zero, h]; omega
    | succ j ih =>
      have hb : goodsteinSeq M (k + j) ≤ bump (base (k + j)) (goodsteinSeq M (k + j)) :=
        le_bump (base (k + j)) (Nat.le_add_left 2 _) _
      have : goodsteinSeq M (k + (j + 1)) = bump (base (k + j)) (goodsteinSeq M (k + j)) - 1 := by
        rw [show k + (j + 1) = (k + j) + 1 from by omega]; rfl
      omega
  rw [goodsteinLength, Nat.le_find_iff]
  intro n hn hzero
  rcases Nat.lt_or_ge n k with hnk | hnk
  · have := goodsteinSeq_zero_absorb M hzero (k - n)
    rw [show n + (k - n) = k from by omega, h] at this; omega
  · have := hsub (n - k)
    rw [show k + (n - k) = n from by omega, hzero] at this; omega

/-- **The finitely many base cases of Cichoń's exponential length bound** (`4 ≤ M < 16`):
`2^{M+1} + M ≤ goodsteinLength M`, each discharged **kernel-only**: `le_bump` gives a per-step
drop of at most 1, so a checkpoint value at step `k ≤ 4` (computed in the kernel by the
fuel-based evaluator `gvalF`) certifies the whole exponential bound (`glen_ge_of_seq_value`).
No `native_decide` — the former 65551-step forward pass (`M = 15`) is replaced by a 4-step
kernel evaluation reaching value `326593`. -/
theorem goodsteinLength_base_cases (M : ℕ) (h4 : 4 ≤ M) (h16 : M < 16) :
    2 ^ (M + 1) + M ≤ goodsteinLength M := by
  have hM : M = 4 ∨ M = 5 ∨ M = 6 ∨ M = 7 ∨ M = 8 ∨ M = 9 ∨ M = 10 ∨ M = 11 ∨ M = 12 ∨
      M = 13 ∨ M = 14 ∨ M = 15 := by omega
  have key : ∀ (m k v : ℕ), 1 ≤ v → gvalF 0 m k = v → 2 ^ (m + 1) + m ≤ k + v →
      2 ^ (m + 1) + m ≤ goodsteinLength m := by
    intro m k v hv hval hle
    have := gvalF_goodstein m k 0
    rw [Nat.zero_add] at this
    exact le_trans hle (glen_ge_of_seq_value hv (by rw [← this]; exact hval))
  rcases hM with h | h | h | h | h | h | h | h | h | h | h | h <;> subst h
  · exact key 4 2 41 (by omega) (by decide) (by norm_num)
  · exact key 5 2 255 (by omega) (by decide) (by norm_num)
  · exact key 6 2 257 (by omega) (by decide) (by norm_num)
  · exact key 7 3 3127 (by omega) (by decide) (by norm_num)
  · exact key 8 2 553 (by omega) (by decide) (by norm_num)
  · exact key 9 3 9842 (by omega) (by decide) (by norm_num)
  · exact key 10 3 15625 (by omega) (by decide) (by norm_num)
  · exact key 11 3 15627 (by omega) (by decide) (by norm_num)
  · exact key 12 3 15685 (by omega) (by decide) (by norm_num)
  · exact key 13 4 280711 (by omega) (by decide) (by norm_num)
  · exact key 14 4 326591 (by omega) (by decide) (by norm_num)
  · exact key 15 4 326593 (by omega) (by decide) (by norm_num)

/-- **Cichoń's exponential length lower bound, UNCONDITIONAL:** `2^{m+1} + m ≤ goodsteinLength m` for
every `m ≥ 4`. The strong-induction engine `goodsteinLength_exp_lower` fed by the computational base
cases. The self-similarity makes the exponential bound reproduce itself at each scale. -/
theorem goodsteinLength_exp_lower_uncond {m : ℕ} (hm : 4 ≤ m) :
    2 ^ (m + 1) + m ≤ goodsteinLength m :=
  goodsteinLength_exp_lower goodsteinLength_base_cases m hm

/-- **THE `o = 2` DIAGONAL DOMINATION — UNCONDITIONAL (every `m ≥ 16`):**
`fastGrowing 2 m ≤ goodsteinLength m + 2`, i.e. `f_2(m) = 2^m · m ≤ goodsteinLength m + 2`. This is the
*true diagonal* bound — budget `m`, not the earlier `log₂ m` of `fastGrowing_two_log_le_goodsteinLength`
— hence Cichoń's lower bound at level `o = 2`, fully machine-checked: the Goodstein descent's leading
CNF exponent provably stays `≥ 2` for the first `m` steps. Assembly: for `m ≥ 16` the smaller seed
`L = Nat.log 2 m` is `≥ 4`, so the unconditional exponential length bound gives
`goodsteinLength L ≥ 2^{L+1} + L ≥ m + 2` (as `m < 2^{L+1}`), discharging the hypothesis of
`fastGrowing_two_le_goodsteinLength_of_log_length`. (The finite tail `4 ≤ m < 16` also holds but its
direct certification is far more expensive — `f_2(15) ≈ 5·10^5` steps — and is omitted: asymptotic
domination is the mathematically meaningful statement.) -/
theorem fastGrowing_two_le_goodsteinLength {m : ℕ} (hm : 16 ≤ m) :
    fastGrowing 2 m ≤ goodsteinLength m + 2 := by
  have hL4 : 4 ≤ Nat.log 2 m := by
    calc 4 = Nat.log 2 16 := by rw [show (16 : ℕ) = 2 ^ 4 from rfl, Nat.log_pow (by norm_num)]
      _ ≤ Nat.log 2 m := Nat.log_mono_right hm
  have hexp := goodsteinLength_exp_lower_uncond (m := Nat.log 2 m) hL4
  have hpow : m + 1 ≤ 2 ^ (Nat.log 2 m + 1) := by
    have := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) m; omega
  have hlen : m + 2 ≤ goodsteinLength (Nat.log 2 m) := by omega
  exact fastGrowing_two_le_goodsteinLength_of_log_length (by omega) hlen

/-- **THE FULL DIAGONAL DOMINATION — UNCONDITIONAL, every finite level `n`:**
`fastGrowing (ofNat n) m ≤ goodsteinLength m + 2` whenever `n + 1 ≤ Nat.log 2 m` (and `m ≥ 16`).
For each fixed `n` this holds for all sufficiently large `m` (those with `Nat.log 2 m ≥ n + 1`, i.e.
`m ≥ 2^{n+1}`). This is **Cichoń's lower bound at every finite level**, fully machine-checked: the
Goodstein descent's leading CNF exponent provably stays `≥ n` for the first `m` steps, so
`goodsteinLength` diagonally dominates the entire finite fast-growing hierarchy `f_0, f_1, f_2, …`.
The unconditional exponential length bound at the smaller seed `L = Nat.log 2 m` supplies
`goodsteinLength L ≥ 2^{L+1} + L ≥ m + n` (using `m < 2^{L+1}` and `n ≤ L − 1`), discharging the
hypothesis of `fastGrowing_ofNat_le_goodsteinLength_of_log_length`. -/
theorem fastGrowing_ofNat_le_goodsteinLength {n m : ℕ} (hm : 16 ≤ m)
    (hn : n + 1 ≤ Nat.log 2 m) :
    fastGrowing (ONote.ofNat n) m ≤ goodsteinLength m + 2 := by
  have hL4 : 4 ≤ Nat.log 2 m := by
    calc 4 = Nat.log 2 16 := by rw [show (16 : ℕ) = 2 ^ 4 from rfl, Nat.log_pow (by norm_num)]
      _ ≤ Nat.log 2 m := Nat.log_mono_right hm
  have hexp := goodsteinLength_exp_lower_uncond (m := Nat.log 2 m) hL4
  have hpow : m + 1 ≤ 2 ^ (Nat.log 2 m + 1) := by
    have := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) m; omega
  have hloglt : Nat.log 2 m < m := Nat.log_lt_self 2 (by omega)
  have hlen : m + n ≤ goodsteinLength (Nat.log 2 m) := by omega
  exact fastGrowing_ofNat_le_goodsteinLength_of_log_length (by omega) (by omega) hlen

/-- Anti-vacuity: the diagonal bound is non-trivial — `f_n` is astronomically large at its argument.
`f_2(16) = 2^16 · 16 = 1048576`, yet `≤ goodsteinLength 16 + 2`. (Not `native_decide`-able — RHS is
beyond astronomical — but `f_2(16)` itself is, witnessing the LHS is a genuine fast-growing value.) -/
example : fastGrowing 2 16 = 2 ^ 16 * 16 := by rw [ONote.fastGrowing_two]


/-
# Toward `o = ω`: the limit-level diagonal, isolated to its crux

With the finite-level diagonal `f_n(m) ≤ goodsteinLength m + 2` closed
(`DominationBaseCases.lean`), the next tier of Cichoń's lower bound is the **limit ordinal `ω`**:
`f_ω(m) ≤ goodsteinLength m + 2`. This file builds the ordinal bridge for `ω^ω` and reduces the
`o = ω` diagonal to a single open hypothesis — exactly the way `Domination.lean`'s
`goodstein_dominates_of_index` framed the finite levels in lap 6.

The crux it isolates: the descent's **leading exponent stays in the LARGE regime** (`≥ base`) at step
`m − 2`. For finite `o = n` we only needed `leadExp ≥ n` (a fixed constant); for `o = ω` we need
`leadExp ≥ base = m`, i.e. the leading exponent itself reaches `ω` at the ordinal level. This is one
recursion deeper than the lap-9 self-similarity (see `PENDING_WORK.md` → "NEXT FRONTIER"), and is the
genuine remaining growth content — NOT to be axiomatized.
-/



/-- **The general ordinal bridge (unifies every level).** For any ordinal `β`, if the descent's
leading CNF exponent ordinal `toOrdinal (base i) (leadExp_i)` dominates `β`, then the descent ordinal
dominates `ω^β`: `ω^β ≤ (seqONote m i).repr`. Just `opow_le_opow_right` (monotonicity of `ω^·`) chained
with `opow_toOrdinal_log_le` (the leading term `ω^{toOrdinal b (log_b v)}` is `≤ toOrdinal b v`). Every
level-specific bridge below (`ω^k`, `ω^ω`, `ω^{ω^j}`, `ω^{ω^ω}`) is this lemma fed a `toOrdinal` lower
bound on the leading exponent — and the next tier (`ε₀`) will be too. -/
theorem opow_le_seqONote_repr_of_toOrdinal {m i : ℕ} {β : Ordinal}
    (hβ : β ≤ toOrdinal (base i) (Nat.log (base i) (goodsteinSeq m i)))
    (hv : goodsteinSeq m i ≠ 0) :
    (ω : Ordinal) ^ β ≤ (seqONote m i).repr := by
  have hb : 2 ≤ base i := Nat.le_add_left 2 i
  rw [repr_seqONote]
  calc (ω : Ordinal) ^ β
      ≤ ω ^ toOrdinal (base i) (Nat.log (base i) (goodsteinSeq m i)) :=
        opow_le_opow_right omega0_pos hβ
    _ ≤ toOrdinal (base i) (goodsteinSeq m i) := opow_toOrdinal_log_le (base i) hb hv

/-- **Ordinal bridge for `ω^ω`.** If the leading exponent of `G_i` is in the *large regime*
(`base i ≤ log_{base i} G_i`), the descent ordinal dominates `ω^ω`: the leading CNF exponent
`toOrdinal (base i) (leadExp)` is then `≥ toOrdinal (base i) (base i) = ω`, so the leading term is
`≥ ω^ω`. The `ω`-level analog of `opow_le_seqONote_repr` (which handled finite exponents `ω^k`). -/
theorem omega_omega_le_seqONote_repr {m i : ℕ}
    (hreg : base i ≤ Nat.log (base i) (goodsteinSeq m i)) (hv : goodsteinSeq m i ≠ 0) :
    (ω : Ordinal) ^ (ω : Ordinal) ≤ (seqONote m i).repr := by
  have hb : 2 ≤ base i := Nat.le_add_left 2 i
  have h1 : toOrdinal (base i) 1 = 1 := by
    have h := toOrdinal_pow (base i) hb 0; simpa using h
  have hbb : toOrdinal (base i) (base i) = ω := by
    have h := toOrdinal_pow (base i) hb 1
    rw [pow_one, h1, opow_one] at h; exact h
  have hSM : StrictMono (toOrdinal (base i)) := fun a c hac =>
    (toOrdinal_mono_and_bound (base i) hb c).1 a hac
  have homega_le : (ω : Ordinal) ≤ toOrdinal (base i) (Nat.log (base i) (goodsteinSeq m i)) := by
    rw [← hbb]; exact hSM.monotone hreg
  exact opow_le_seqONote_repr_of_toOrdinal homega_le hv

/-- **The `o = ω` diagonal domination, REDUCED to its crux** (`hreg`). If the Goodstein descent's
leading exponent is still in the LARGE regime at step `m − 2` (`base (m−2) ≤ leadExp_{m−2}`), then
`fastGrowing ω m ≤ goodsteinLength m + 2` (with `ω = oadd 1 1 0`). Assembly mirrors the finite-level
`fastGrowing_ofNat_le_goodsteinLength_of_log_length`: the large-regime hypothesis gives
`ω^ω ≤ (seqONote m (m−2)).repr` (`omega_omega_le_seqONote_repr`); the diagonal reduction
`goodstein_dominates_of_index_le` (budget `m`) closes it. **The hypothesis `hreg` IS Cichoń's lower
bound at the limit level `ω`** — the open obligation for the next lap (route (a) in `PENDING_WORK.md`:
iterate the self-similarity so the one-level-down value stays `≥ base` for `~m` steps). -/
theorem fastGrowing_omega_le_goodsteinLength_of_largeRegime {m : ℕ} (hm : 4 ≤ m)
    (hreg : base (m - 2) ≤ Nat.log (base (m - 2)) (goodsteinSeq m (m - 2))) :
    fastGrowing (oadd 1 1 0) m ≤ goodsteinLength m + 2 := by
  set j := m - 2 with hj
  have ho : (oadd 1 1 0 : ONote).NF := by decide
  have hv : goodsteinSeq m j ≠ 0 := by have := goodsteinSeq_ge_init m j (by omega); omega
  have hidx : (oadd (oadd 1 1 0) 1 0).repr ≤ (seqONote m j).repr := by
    have hr : (oadd (oadd 1 1 0) 1 0 : ONote).repr = ω ^ (ω : Ordinal) := by simp [ONote.repr]
    rw [hr]; exact omega_omega_le_seqONote_repr hreg hv
  have hnorm : norm (oadd 1 1 0 : ONote) ≤ j + 2 := by
    have : norm (oadd 1 1 0 : ONote) = 1 := by decide
    omega
  have hgl : j ≤ goodsteinLength m := le_trans (by omega) (le_goodsteinLength m)
  exact goodstein_dominates_of_index_le (o := oadd 1 1 0) (m := m) (j := j) ho hgl (by omega) hnorm hidx

/-- **Doubly-iterated length bound — the `ω`-level analog of `goodsteinLength_exp_lower`.** For every
`m ≥ 2^16` the *one-level-down* Goodstein sequence (seed `L = Nat.log 2 m`) runs at least `2m − 2`
steps: `2 * m ≤ goodsteinLength (Nat.log 2 m) + 2`. The finite-level diagonal used the *exponential*
length bound `goodsteinLength M ≥ 2^{M+1}+M` at the smaller seed; that gives only `≈ m` and cannot
push the leading exponent past a fixed constant. The limit level needs more, so this lemma applies the
full unconditional **`o = 2` diagonal** `2^L·L = f_2(L) ≤ goodsteinLength L + 2`
(`fastGrowing_two_le_goodsteinLength`) at the seed `L ≥ 16`: since `m < 2^{L+1}` we have
`2·2^L ≥ m+1`, so `2^L·L ≥ 16·2^L = 8·(2·2^L) ≥ 8(m+1) ≥ 2m`. The surplus over the seed is exactly
what lifts the leading exponent into the LARGE regime (`≥ base`), discharging `hreg` below. -/
theorem two_mul_le_goodsteinLength_log {m : ℕ} (hm : 2 ^ 16 ≤ m) :
    2 * m ≤ goodsteinLength (Nat.log 2 m) + 2 := by
  have hL16 : 16 ≤ Nat.log 2 m := Nat.le_log_of_pow_le Nat.one_lt_two hm
  have hf2 := fastGrowing_two_le_goodsteinLength (m := Nat.log 2 m) hL16
  simp only [ONote.fastGrowing_two] at hf2
  set L := Nat.log 2 m with hLdef
  set P := 2 ^ L with hPdef
  have hpow : m + 1 ≤ 2 ^ (L + 1) := by
    have h := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) m
    rw [← hLdef] at h; omega
  have hpowsucc : (2 : ℕ) ^ (L + 1) = P * 2 := by rw [hPdef, pow_succ]
  rw [hpowsucc] at hpow
  have hmono : P * 16 ≤ P * L := Nat.mul_le_mul (le_refl P) hL16
  -- hf2 : P * L ≤ goodsteinLength L + 2 ;  hmono : P*16 ≤ P*L ;  hpow : m+1 ≤ P*2
  omega

/-- **THE `o = ω` DIAGONAL DOMINATION — UNCONDITIONAL (every `m ≥ 2^16`):**
`fastGrowing ω m ≤ goodsteinLength m + 2`, i.e. `f_ω(m) ≤ goodsteinLength m + 2`, with
`ω = oadd 1 1 0`. This is Cichoń's lower bound at the **first limit ordinal** — the leading CNF
exponent of the Goodstein descent provably reaches `ω` (the LARGE regime `≥ base`) and stays there
through step `m − 2`, so the descent ordinal dominates `ω^ω`.

The crux `hreg` (leading exponent `≥ base (m−2) = m` at step `m − 2`) is discharged by **iterating
the self-similarity once more**: `leadExp_ge_goodsteinSeq_log` bounds the leading exponent below by
the *one-level-down* Goodstein value `goodsteinSeq (log₂ m) (m−2)`, and `n_le_goodsteinSeq` keeps that
value `≥ m` provided the one-level-down sequence still has `≥ m` steps to run — supplied by the
doubly-iterated length bound `two_mul_le_goodsteinLength_log` (`goodsteinLength (log₂ m) ≥ 2m − 2`).
For finite `o = n` the analog only needed value `≥ n` (a constant); the jump to `o = ω` is precisely
the jump from "value `≥ n`" to "value `≥ base = m`", which the *factor-of-two* surplus in the length
bound provides. The whole reduction is then closed by `fastGrowing_omega_le_goodsteinLength_of_largeRegime`. -/
theorem fastGrowing_omega_le_goodsteinLength {m : ℕ} (hm : 2 ^ 16 ≤ m) :
    fastGrowing (oadd 1 1 0) m ≤ goodsteinLength m + 2 := by
  have h4 : 4 ≤ m := le_trans (by norm_num) hm
  apply fastGrowing_omega_le_goodsteinLength_of_largeRegime h4
  -- hreg : base (m - 2) ≤ Nat.log (base (m - 2)) (goodsteinSeq m (m - 2))
  have hbase : base (m - 2) = m := by simp only [base]; omega
  have hlen : (m - 2) + m ≤ goodsteinLength (Nat.log 2 m) := by
    have := two_mul_le_goodsteinLength_log hm; omega
  calc base (m - 2)
      = m := hbase
    _ ≤ goodsteinSeq (Nat.log 2 m) (m - 2) :=
        n_le_goodsteinSeq (Nat.log 2 m) (m - 2) m hbase.ge hlen
    _ ≤ Nat.log (base (m - 2)) (goodsteinSeq m (m - 2)) := leadExp_ge_goodsteinSeq_log m (m - 2)

/-! ### Toward `o = ω^j`: the SECOND-level tower (next limit tier of Cichoń)

`o = ω` needed the leading exponent in the LARGE regime (`leadExp ≥ base`). The next tier `o = ω^j`
needs the *second-level* leading exponent `≥ j` — equivalently the leading exponent `≥ base^j` — at
step `m − 2`. We build the general ordinal bridge and reduce `o = ω^j` to a single length bound on the
*doubly-iterated* seed `(log₂)^[2] m`, via the self-similarity tower `iterLeadExp_dominates`. -/

/-- **`ω^k ≤ toOrdinal b w`** from the leading exponent `log_b w ≥ k` (with `k < b`, `w ≠ 0`). The
`toOrdinal`-level core of `opow_le_seqONote_repr`, factored out so it applies at the *second* level
(to the leading exponent itself) — the brick of the `ω^j` tower. -/
theorem opow_le_toOrdinal (b : ℕ) (hb : 2 ≤ b) {w k : ℕ}
    (hk : k ≤ Nat.log b w) (hw : w ≠ 0) (hkb : k < b) :
    (ω : Ordinal) ^ (k : Ordinal) ≤ toOrdinal b w := by
  have htk : toOrdinal b k = (k : Ordinal) := by
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · subst hk0; simp
    · have hlog0 : Nat.log b k = 0 := Nat.log_eq_zero_iff.2 (Or.inl hkb)
      rw [toOrdinal_pos b k (by omega), hlog0]
      simp [pow_zero, Nat.div_one, Nat.mod_one, toOrdinal_zero]
  have hmono : toOrdinal b k ≤ toOrdinal b (Nat.log b w) := by
    rcases eq_or_lt_of_le hk with h | h
    · rw [h]
    · exact le_of_lt ((toOrdinal_mono_and_bound b hb _).1 k h)
  calc (ω : Ordinal) ^ (k : Ordinal) = ω ^ toOrdinal b k := by rw [htk]
    _ ≤ ω ^ toOrdinal b (Nat.log b w) := opow_le_opow_right omega0_pos hmono
    _ ≤ toOrdinal b w := opow_toOrdinal_log_le b hb hw

/-- **Level-2 ordinal bridge: `ω^{ω^j} ≤ descent`.** If the SECOND-level leading exponent is `≥ j`
(`j ≤ log_{base i}(log_{base i} G_i)`), with `j < base i` and the value/leading-exponent nonzero, the
Goodstein descent ordinal dominates `ω^{ω^j}`. Applies `opow_le_toOrdinal` to the leading exponent
(`ω^j ≤ toOrdinal (base i)(leadExp)`), then `opow_toOrdinal_log_le` once more. The `ω^j`-flavoured
analog of `omega_omega_le_seqONote_repr` (the `j` "= base", `ω^ω` case). -/
theorem omega_pow_pow_le_seqONote_repr {m i j : ℕ}
    (hj : j ≤ Nat.log (base i) (Nat.log (base i) (goodsteinSeq m i)))
    (hjb : j < base i) (hv : goodsteinSeq m i ≠ 0)
    (hlead : Nat.log (base i) (goodsteinSeq m i) ≠ 0) :
    (ω : Ordinal) ^ ((ω : Ordinal) ^ (j : Ordinal)) ≤ (seqONote m i).repr := by
  have hb : 2 ≤ base i := Nat.le_add_left 2 i
  exact opow_le_seqONote_repr_of_toOrdinal (opow_le_toOrdinal (base i) hb hj hlead hjb) hv

/-- **The `o = ω^j` diagonal, REDUCED to its second-level crux.** For finite `j ≥ 1`, if the SECOND
leading exponent of the seed-`m` descent is `≥ j` at step `m − 2`, then
`fastGrowing (ω^j) m ≤ goodsteinLength m + 2` with `ω^j = oadd (ofNat j) 1 0` (`repr = ω^j`). Mirrors
`fastGrowing_omega_le_goodsteinLength_of_largeRegime` one level up: `omega_pow_pow_le_seqONote_repr`
gives `ω^{ω^j} ≤ descent`; `goodstein_dominates_of_index_le` (budget `m`) closes it. `hreg2` is
Cichoń's lower bound at the level `ω^j`. -/
theorem fastGrowing_omega_pow_le_goodsteinLength_of_crux {m j : ℕ} (hm : 4 ≤ m) (hj1 : 1 ≤ j)
    (hjm : j < m)
    (hreg2 : j ≤ Nat.log (base (m - 2)) (Nat.log (base (m - 2)) (goodsteinSeq m (m - 2)))) :
    fastGrowing (oadd (ONote.ofNat j) 1 0) m ≤ goodsteinLength m + 2 := by
  set i := m - 2 with hi
  have hbase : base i = m := by simp only [base, hi]; omega
  have ho : (oadd (ONote.ofNat j) 1 0 : ONote).NF := NF.oadd inferInstance 1 NFBelow.zero
  have hv : goodsteinSeq m i ≠ 0 := by have := goodsteinSeq_ge_init m i (by omega); omega
  have hjb : j < base i := by rw [hbase]; exact hjm
  have hlead : Nat.log (base i) (goodsteinSeq m i) ≠ 0 := by
    intro h0; rw [h0, Nat.log_zero_right] at hreg2; omega
  have hidx : (oadd (oadd (ONote.ofNat j) 1 0) 1 0).repr ≤ (seqONote m i).repr := by
    have hr : (oadd (oadd (ONote.ofNat j) 1 0) 1 0 : ONote).repr
        = ω ^ ((ω : Ordinal) ^ (j : Ordinal)) := by
      simp [ONote.repr, ONote.repr_ofNat]
    rw [hr]
    exact omega_pow_pow_le_seqONote_repr hreg2 hjb hv hlead
  have hnorm : norm (oadd (ONote.ofNat j) 1 0) ≤ i + 2 := by
    rw [norm_oadd, norm_ofNat, norm_zero]; simp only [PNat.one_coe]; omega
  have hgl : i ≤ goodsteinLength m := le_trans (by omega) (le_goodsteinLength m)
  exact goodstein_dominates_of_index_le ho hgl (by omega) hnorm hidx

/-- **The `o = ω^j` diagonal, REDUCED to a doubly-iterated length bound.** For finite `j ≥ 1`, if the
*doubly-iterated* seed `(log₂)^[2] m` has a Goodstein length `≥ (m−2)+j`, then
`fastGrowing (ω^j) m ≤ goodsteinLength m + 2`. The second-level crux `hreg2` is discharged by the
self-similarity tower (`iterLeadExp_dominates m 2`): the second leading exponent at step `m−2`
dominates `goodsteinSeq ((log₂)^[2] m) (m−2)`, which `n_le_goodsteinSeq` keeps `≥ j` exactly when the
doubly-iterated sequence still has `≥ j` steps to run. This is the limit-level analog of
`fastGrowing_omega_le_goodsteinLength_of_largeRegime` reduced one more scale down: the SOLE remaining
obligation is the length bound `goodsteinLength ((log₂)^[2] m) ≥ m` (next-lap crux — needs an
`f_ω`-strength lower bound at the deep seed, bootstrapped from `fastGrowing_omega_le_goodsteinLength`
itself). -/
theorem fastGrowing_omega_pow_le_goodsteinLength_of_length {m j : ℕ} (hm : 4 ≤ m) (hj1 : 1 ≤ j)
    (hjm : j < m)
    (hlen : (m - 2) + j ≤ goodsteinLength ((Nat.log 2)^[2] m)) :
    fastGrowing (oadd (ONote.ofNat j) 1 0) m ≤ goodsteinLength m + 2 := by
  apply fastGrowing_omega_pow_le_goodsteinLength_of_crux hm hj1 hjm
  have hbase : base (m - 2) = m := by simp only [base]; omega
  have hval : j ≤ goodsteinSeq ((Nat.log 2)^[2] m) (m - 2) :=
    n_le_goodsteinSeq ((Nat.log 2)^[2] m) (m - 2) j (by rw [hbase]; omega) hlen
  have hdom := iterLeadExp_dominates m 2 (m - 2)
  exact le_trans hval hdom

/-! ### Discharging the `o = ω^j` crux: an `f_ω`-strength length bound at the deep seed

The sole remaining obligation is `goodsteinLength ((log₂)^[2] m) ≥ m`. The exponential length bound is
far too weak at the doubly-iterated seed `t = (log₂)^[2] m` (it gives only `≈ 2^t`, while `m ≈ 2^{2^t}`).
But we now have `f_ω(t) ≤ goodsteinLength t + 2` — a *tower-strength* lower bound — and `f_ω` outgrows
`2^{2^{·}}`. Bootstrapping the `o = ω` result against itself closes the `o = ω^j` tier. -/

/-- `f_2(n) = 2^n · n` (mathlib's closed form, transported to the `ofNat 2` notation). -/
theorem fastGrowing_ofNat_two (n : ℕ) : fastGrowing (ONote.ofNat 2) n = 2 ^ n * n := by
  rw [show (ONote.ofNat 2 : ONote) = 2 from by decide, ONote.fastGrowing_two]

/-- **`f_3` is doubly-exponential:** `2^{2^t · t} ≤ f_3(t)` for `t ≥ 2`. Since `f_3(t) = (f_2)^[t](t)`
(`fastGrowing_succ`), and `f_2` is expansive, `(f_2)^[t](t) ≥ (f_2)^[2](t) = f_2(f_2(t)) =
2^{2^t·t}·(2^t·t) ≥ 2^{2^t·t}`. The engine that makes `f_ω` outrun `2^{2^{·}}`. -/
theorem two_pow_le_fastGrowing_ofNat_three {t : ℕ} (ht : 2 ≤ t) :
    2 ^ (2 ^ t * t) ≤ fastGrowing (ONote.ofNat 3) t := by
  have hf3 : fastGrowing (ONote.ofNat 3) t = (fastGrowing (ONote.ofNat 2))^[t] t := by
    rw [show (ONote.ofNat 3 : ONote) = ONote.ofNat (2 + 1) from rfl,
        fastGrowing_succ _ (fundamentalSequence_ofNat_succ 2)]
  have hexp : (id : ℕ → ℕ) ≤ fastGrowing (ONote.ofNat 2) := fun n => le_fastGrowing _ n
  have hmono : (fastGrowing (ONote.ofNat 2))^[2] t ≤ (fastGrowing (ONote.ofNat 2))^[t] t :=
    Function.monotone_iterate_of_id_le hexp ht t
  have h2it : (fastGrowing (ONote.ofNat 2))^[2] t
      = fastGrowing (ONote.ofNat 2) (fastGrowing (ONote.ofNat 2) t) := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, Function.iterate_add_apply]; simp
  rw [hf3]
  refine le_trans ?_ hmono
  rw [h2it, fastGrowing_ofNat_two, fastGrowing_ofNat_two]
  have hpos : 1 ≤ 2 ^ t * t := by
    have : 0 < 2 ^ t * t := Nat.mul_pos (pow_pos (by norm_num) t) (by omega); omega
  calc 2 ^ (2 ^ t * t) = 2 ^ (2 ^ t * t) * 1 := (mul_one _).symm
    _ ≤ 2 ^ (2 ^ t * t) * (2 ^ t * t) := by gcongr

/-- `f_ω(t) = f_{t+1}(t)`: the fundamental sequence of `ω = oadd 1 1 0` is `i ↦ ofNat (i+1)`. -/
theorem fastGrowing_omega_eq (t : ℕ) :
    fastGrowing (oadd 1 1 0) t = fastGrowing (ONote.ofNat (t + 1)) t := by
  have hfs : fundamentalSequence (oadd 1 1 0) = Sum.inr (fun i => ONote.ofNat (i + 1)) := rfl
  rw [fastGrowing_limit (oadd 1 1 0) hfs]

/-- **The doubly-iterated length bound — `o = ω^j`'s crux DISCHARGED.** For `m` with the doubly-
iterated seed `t = (log₂)^[2] m ≥ 2^16`, `goodsteinLength t ≥ 2m`. Bootstraps the `o = ω` domination
against itself: `goodsteinLength t ≥ f_ω(t) − 2 = f_{t+1}(t) − 2 ≥ f_3(t) − 2 ≥ 2^{2^t·t} − 2`
(`fastGrowing_omega_le_goodsteinLength` ⊕ `fastGrowing_ofNat_mono` ⊕ `two_pow_le_fastGrowing_ofNat_three`),
while `m < 2^{2^{t+1}}` and `2^t·t ≥ 2^{t+1}+1` (for `t ≥ 3`) give `2^{2^t·t} ≥ 2(m+1)`. The `f_ω`
length bound carries the finite-base-case `native_decide` axioms (documented split). -/
theorem two_mul_le_goodsteinLength_loglog {m : ℕ}
    (ht : 2 ^ 16 ≤ (Nat.log 2)^[2] m) :
    2 * m ≤ goodsteinLength ((Nat.log 2)^[2] m) := by
  set t := (Nat.log 2)^[2] m with htdef
  have hteq : t = Nat.log 2 (Nat.log 2 m) := rfl
  have hA : Nat.log 2 m + 1 ≤ 2 ^ (t + 1) := by
    have h := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) (Nat.log 2 m)
    rw [hteq]; omega
  have hB : m < 2 ^ (Nat.log 2 m + 1) := Nat.lt_pow_succ_log_self (by norm_num) m
  have hD : 2 ^ (Nat.log 2 m + 1) ≤ 2 ^ (2 ^ (t + 1)) := Nat.pow_le_pow_right (by norm_num) hA
  have hm1 : m + 1 ≤ 2 ^ (2 ^ (t + 1)) := by omega
  have hlen := fastGrowing_omega_le_goodsteinLength (m := t) ht
  rw [fastGrowing_omega_eq] at hlen
  have hidx : fastGrowing (ONote.ofNat 3) t ≤ fastGrowing (ONote.ofNat (t + 1)) t :=
    fastGrowing_ofNat_mono (by omega) (by omega)
  have hf3 := two_pow_le_fastGrowing_ofNat_three (t := t) (by omega)
  have hexp_ge : 2 ^ (t + 1) + 1 ≤ 2 ^ t * t := by
    have h2t : 2 ^ (t + 1) = 2 * 2 ^ t := by rw [pow_succ]; ring
    have hb : 2 ^ t * 3 ≤ 2 ^ t * t := by gcongr; omega
    have hp : 1 ≤ 2 ^ t := Nat.one_le_two_pow
    omega
  have hpow_ge : 2 * (m + 1) ≤ 2 ^ (2 ^ t * t) := by
    have h2 : 2 * 2 ^ (2 ^ (t + 1)) = 2 ^ (2 ^ (t + 1) + 1) := by rw [pow_succ]; ring
    have h3 : 2 ^ (2 ^ (t + 1) + 1) ≤ 2 ^ (2 ^ t * t) := Nat.pow_le_pow_right (by norm_num) hexp_ge
    omega
  omega

/-- **THE `o = ω^j` DIAGONAL DOMINATION — UNCONDITIONAL** (every finite `j ≥ 1`, for `m` with
`(log₂)^[2] m ≥ 2^16`): `fastGrowing (ω^j) m ≤ goodsteinLength m + 2`, with `ω^j = oadd (ofNat j) 1 0`.
Cichoń's lower bound at the limit levels `ω, ω^2, ω^3, …` — fully machine-checked. The doubly-iterated
length bound `two_mul_le_goodsteinLength_loglog` discharges the `of_length` reduction's hypothesis
(`(m−2)+j < 2m ≤ goodsteinLength ((log₂)^[2] m)`). Carries the finite-base-case `native_decide` axioms
(documented split), inherited through the `f_ω` bootstrap. -/
theorem fastGrowing_omega_pow_le_goodsteinLength {m j : ℕ}
    (ht : 2 ^ 16 ≤ (Nat.log 2)^[2] m) (hj1 : 1 ≤ j) (hjm : j < m) :
    fastGrowing (oadd (ONote.ofNat j) 1 0) m ≤ goodsteinLength m + 2 := by
  have h1' : 1 ≤ (Nat.log 2)^[2] m := le_trans (by norm_num) ht
  have hlm0 : Nat.log 2 m ≠ 0 := by
    intro h
    rw [show (Nat.log 2)^[2] m = Nat.log 2 (Nat.log 2 m) from rfl, h, Nat.log_zero_right] at h1'
    omega
  have hlogm2 : 2 ≤ Nat.log 2 m := by
    have h := Nat.pow_le_of_le_log hlm0 (show 1 ≤ Nat.log 2 (Nat.log 2 m) from h1'); simpa using h
  have hm0 : m ≠ 0 := by intro h; rw [h, Nat.log_zero_right] at hlogm2; omega
  have hm : 4 ≤ m := by have h := Nat.pow_le_of_le_log hm0 hlogm2; simpa using h
  apply fastGrowing_omega_pow_le_goodsteinLength_of_length hm hj1 hjm
  have h2m := two_mul_le_goodsteinLength_loglog ht
  omega

/-! ### `o = ω^ω`: the second LARGE-regime level (toward `ε₀`)

`o = ω^j` (finite `j`) needed the second leading exponent `≥ j` (a constant). The next genuine limit
`o = ω^ω` needs the second leading exponent in the *large* regime — `secondLeadExp ≥ base` — exactly
as `o = ω` needed the first. Remarkably the SAME doubly-iterated length bound `≥ 2m` already proved
discharges it (`n_le_goodsteinSeq` with `n = m` at step `m−2`, budget `2m−2 ≤ 2m`). -/

/-- **`ω^ω ≤ toOrdinal b w`** from the leading exponent in the LARGE regime (`b ≤ log_b w`). The
`toOrdinal`-level core of `omega_omega_le_seqONote_repr`, factored to apply at the *second* level. -/
theorem omega_omega_le_toOrdinal (b : ℕ) (hb : 2 ≤ b) {w : ℕ}
    (hreg : b ≤ Nat.log b w) (hw : w ≠ 0) :
    (ω : Ordinal) ^ (ω : Ordinal) ≤ toOrdinal b w := by
  have h1 : toOrdinal b 1 = 1 := by have h := toOrdinal_pow b hb 0; simpa using h
  have hbb : toOrdinal b b = ω := by
    have h := toOrdinal_pow b hb 1; rw [pow_one, h1, opow_one] at h; exact h
  have hSM : StrictMono (toOrdinal b) := fun a c hac => (toOrdinal_mono_and_bound b hb c).1 a hac
  have homega_le : (ω : Ordinal) ≤ toOrdinal b (Nat.log b w) := by
    rw [← hbb]; exact hSM.monotone hreg
  calc (ω : Ordinal) ^ (ω : Ordinal)
      ≤ ω ^ toOrdinal b (Nat.log b w) := opow_le_opow_right omega0_pos homega_le
    _ ≤ toOrdinal b w := opow_toOrdinal_log_le b hb hw

/-- **Level-3 ordinal bridge: `ω^{ω^ω} ≤ descent`** from the SECOND leading exponent in the LARGE
regime (`base i ≤ secondLeadExp_i`). Applies `omega_omega_le_toOrdinal` to the leading exponent
(giving `ω^ω ≤ toOrdinal (base i)(leadExp)`), then `opow_toOrdinal_log_le`. The `ω^ω`-level analog of
`omega_omega_le_seqONote_repr`. -/
theorem omega_pow_omega_le_seqONote_repr {m i : ℕ}
    (hreg2 : base i ≤ Nat.log (base i) (Nat.log (base i) (goodsteinSeq m i)))
    (hv : goodsteinSeq m i ≠ 0) (hlead : Nat.log (base i) (goodsteinSeq m i) ≠ 0) :
    (ω : Ordinal) ^ ((ω : Ordinal) ^ (ω : Ordinal)) ≤ (seqONote m i).repr := by
  have hb : 2 ≤ base i := Nat.le_add_left 2 i
  exact opow_le_seqONote_repr_of_toOrdinal (omega_omega_le_toOrdinal (base i) hb hreg2 hlead) hv

/-- **THE `o = ω^ω` DIAGONAL DOMINATION — UNCONDITIONAL** (for `m` with `(log₂)^[2] m ≥ 2^16`):
`fastGrowing (ω^ω) m ≤ goodsteinLength m + 2`, with `ω^ω = oadd (oadd 1 1 0) 1 0`. Cichoń's lower
bound at `ω^ω` — fully machine-checked. The crux is the SECOND leading exponent in the LARGE regime
(`secondLeadExp_{m-2} ≥ base(m-2) = m`), discharged by the tower (`iterLeadExp_dominates m 2`) +
`n_le_goodsteinSeq` (`n = m`) + the doubly-iterated length bound `goodsteinLength ((log₂)^[2] m) ≥ 2m`
(`two_mul_le_goodsteinLength_loglog`, budget `(m−2)+m = 2m−2 ≤ 2m`). Carries the finite-base-case
`native_decide` axioms (documented split). -/
theorem fastGrowing_omega_pow_omega_le_goodsteinLength {m : ℕ}
    (ht : 2 ^ 16 ≤ (Nat.log 2)^[2] m) :
    fastGrowing (oadd (oadd 1 1 0) 1 0) m ≤ goodsteinLength m + 2 := by
  have h1' : 1 ≤ (Nat.log 2)^[2] m := le_trans (by norm_num) ht
  have hlm0 : Nat.log 2 m ≠ 0 := by
    intro h
    rw [show (Nat.log 2)^[2] m = Nat.log 2 (Nat.log 2 m) from rfl, h, Nat.log_zero_right] at h1'
    omega
  have hlogm2 : 2 ≤ Nat.log 2 m := by
    have h := Nat.pow_le_of_le_log hlm0 (show 1 ≤ Nat.log 2 (Nat.log 2 m) from h1'); simpa using h
  have hm0 : m ≠ 0 := by intro h; rw [h, Nat.log_zero_right] at hlogm2; omega
  have hm : 4 ≤ m := by have h := Nat.pow_le_of_le_log hm0 hlogm2; simpa using h
  set i := m - 2 with hi
  have hbase : base i = m := by simp only [base, hi]; omega
  have ho : (oadd (oadd 1 1 0) 1 0 : ONote).NF := NF.oadd (by decide) 1 NFBelow.zero
  have hv : goodsteinSeq m i ≠ 0 := by have := goodsteinSeq_ge_init m i (by omega); omega
  -- second leading exponent ≥ base = m at step m-2
  have hlen2 : (m - 2) + m ≤ goodsteinLength ((Nat.log 2)^[2] m) := by
    have := two_mul_le_goodsteinLength_loglog ht; omega
  have hval : m ≤ goodsteinSeq ((Nat.log 2)^[2] m) i :=
    n_le_goodsteinSeq ((Nat.log 2)^[2] m) i m (by rw [hbase]) hlen2
  have hreg2 : base i ≤ Nat.log (base i) (Nat.log (base i) (goodsteinSeq m i)) :=
    calc base i = m := hbase
      _ ≤ goodsteinSeq ((Nat.log 2)^[2] m) i := hval
      _ ≤ Nat.log (base i) (Nat.log (base i) (goodsteinSeq m i)) := iterLeadExp_dominates m 2 i
  have hlead : Nat.log (base i) (goodsteinSeq m i) ≠ 0 := by
    intro h0
    rw [h0, Nat.log_zero_right] at hreg2
    omega
  have hidx : (oadd (oadd (oadd 1 1 0) 1 0) 1 0).repr ≤ (seqONote m i).repr := by
    have hr : (oadd (oadd (oadd 1 1 0) 1 0) 1 0 : ONote).repr
        = ω ^ ((ω : Ordinal) ^ (ω : Ordinal)) := by simp [ONote.repr]
    rw [hr]
    exact omega_pow_omega_le_seqONote_repr hreg2 hv hlead
  have hnorm : norm (oadd (oadd 1 1 0) 1 0) ≤ i + 2 := by
    have : norm (oadd (oadd 1 1 0) 1 0 : ONote) = 1 := by decide
    omega
  have hgl : i ≤ goodsteinLength m := le_trans (by omega) (le_goodsteinLength m)
  exact goodstein_dominates_of_index_le ho hgl (by omega) hnorm hidx

/-- **Explicit-threshold form of the `o = ω^ω` domination.** For every `m ≥ 2^{2^{2^16}}`,
`fastGrowing (ω^ω) m ≤ goodsteinLength m + 2`. The threshold is the concrete `N` witnessing the
asymptotic statement "`goodsteinLength` eventually dominates `f_{ω^ω}`": `m ≥ 2^{2^{2^16}}` forces
`(log₂)^[2] m ≥ 2^16` by two applications of `Nat.le_log_of_pow_le`. -/
theorem goodsteinLength_dominates_fastGrowing_omega_pow_omega
    {m : ℕ} (hm : 2 ^ (2 ^ (2 ^ 16)) ≤ m) :
    fastGrowing (oadd (oadd 1 1 0) 1 0) m ≤ goodsteinLength m + 2 := by
  apply fastGrowing_omega_pow_omega_le_goodsteinLength
  have h1 : 2 ^ (2 ^ 16) ≤ Nat.log 2 m := Nat.le_log_of_pow_le Nat.one_lt_two hm
  exact Nat.le_log_of_pow_le Nat.one_lt_two h1

/-- **Explicit-threshold form of the `o = ω^j` domination** (every finite `j ≥ 1`). For `m` with
`m ≥ 2^{2^{2^16}}` and `j < m`, `fastGrowing (ω^j) m ≤ goodsteinLength m + 2`. The big threshold forces
`(log₂)^[2] m ≥ 2^16`; the `j < m` is the (mild) requirement that the level fit under the budget. -/
theorem goodsteinLength_dominates_fastGrowing_omega_pow {m j : ℕ}
    (hm : 2 ^ (2 ^ (2 ^ 16)) ≤ m) (hj1 : 1 ≤ j) (hjm : j < m) :
    fastGrowing (oadd (ONote.ofNat j) 1 0) m ≤ goodsteinLength m + 2 := by
  apply fastGrowing_omega_pow_le_goodsteinLength _ hj1 hjm
  have h1 : 2 ^ (2 ^ 16) ≤ Nat.log 2 m := Nat.le_log_of_pow_le Nat.one_lt_two hm
  exact Nat.le_log_of_pow_le Nat.one_lt_two h1

/-- Anti-vacuity: `ω = oadd 1 1 0` really has `repr = ω`, and `oadd ω 1 0` has `repr = ω^ω` — so the
reduction targets the genuine limit level, not a finite stand-in. -/
example : (oadd 1 1 0 : ONote).repr = ω := by simp [ONote.repr]
example : (oadd (oadd 1 1 0) 1 0 : ONote).repr = ω ^ (ω : Ordinal) := by simp [ONote.repr]
example (j : ℕ) : (oadd (oadd (ONote.ofNat j) 1 0) 1 0 : ONote).repr
    = ω ^ ((ω : Ordinal) ^ (j : Ordinal)) := by simp [ONote.repr, ONote.repr_ofNat]

end Goodstein.Dom
