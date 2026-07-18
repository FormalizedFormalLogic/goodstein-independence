/-
# Goodstein.Dom — Part4
-/
module

public import Mathlib.Algebra.Order.SuccPred
public import Mathlib.SetTheory.Ordinal.Exponential
public import Mathlib.SetTheory.Ordinal.Notation
public meta import Mathlib.SetTheory.Ordinal.Notation  -- shake: keep
public import Mathlib.Tactic.Ring
public import GoodsteinPA.ToMathlib.Goodstein.Defs
public meta import GoodsteinPA.ToMathlib.Goodstein.Defs  -- shake: keep
public import GoodsteinPA.ToMathlib.Hardy
public meta import GoodsteinPA.ToMathlib.Hardy  -- shake: keep
public import GoodsteinPA.ToMathlib.Goodstein.Domination.Part3
public meta import GoodsteinPA.ToMathlib.Goodstein.Domination.Part3  -- shake: keep

@[expose] public section

namespace Goodstein.Dom

open ONote Ordinal

/-- **Domination, generalized reduction (any telescope step, `≤` index).** If at some step `j`
the budget reaches the diagonal (`m ≤ j + 2`, `norm o ≤ j + 2`) and the descent notation is at
least `ω^o` (`(oadd o 1 0).repr ≤ (seqONote m j).repr`, allowing equality), then `goodsteinLength`
dominates `fastGrowing o` at `m`. Generalizes `goodstein_dominates_of_index`: the telescope step is
free (any `j ≤ goodsteinLength m`), and the index hypothesis is non-strict — the equality case
`oadd o 1 0 = seqONote m j` collapses the Hardy comparison to a literal `rfl`, while the strict
case uses `hardy_le_of_lt` (budget met). This is what lets the `o = 1` level close from the
non-strict ordinal bound `omega_le_seqONote_repr`. -/
theorem goodstein_dominates_of_index_le {o : ONote} (ho : o.NF) {m j : ℕ}
    (hj : j ≤ goodsteinLength m) (hmj : m ≤ j + 2) (hnorm : norm o ≤ j + 2)
    (hidx : (oadd o 1 0).repr ≤ (seqONote m j).repr) :
    fastGrowing o m ≤ goodsteinLength m + 2 := by
  have hNFidx : (oadd o 1 0).NF := NF.oadd ho 1 NFBelow.zero
  have hNFseq : (seqONote m j).NF := seqONote_NF m j
  have hbudget : norm (oadd o 1 0) ≤ j + 2 := by
    rw [norm_oadd, norm_zero]; simp only [PNat.one_coe]; omega
  have hindex : hardy (oadd o 1 0) (j + 2) ≤ hardy (seqONote m j) (j + 2) := by
    rcases eq_or_lt_of_le hidx with heq | hlt
    · have heqo : oadd o 1 0 = seqONote m j :=
        (@repr_inj (oadd o 1 0) (seqONote m j) hNFidx hNFseq).1 heq
      rw [heqo]
    · exact hardy_le_of_lt hNFidx hNFseq (lt_def.2 hlt) hbudget
  have htel : hardy (seqONote m 0) 2 = hardy (seqONote m j) (j + 2) :=
    hardy_seqONote_telescope m j hj
  have hz : hardy (seqONote m 0) 2 = goodsteinLength m + 2 := hardy_seqONote_zero m
  calc fastGrowing o m
      ≤ fastGrowing o (j + 2) := fastGrowing_monotone o hmj
    _ ≤ hardy (oadd o 1 0) (j + 2) := fastGrowing_le_hardy_pow o ho (j + 2)
    _ ≤ hardy (seqONote m j) (j + 2) := hindex
    _ = hardy (seqONote m 0) 2 := htel.symm
    _ = goodsteinLength m + 2 := hz

/-- **Goodstein length dominates `f_1`, unconditionally (every `m ≥ 2`).** This is the first
member of the fast-growing hierarchy proven dominated by `goodsteinLength` through the full
Cichoń pipeline — *not* by `native_decide`. The deep input, sub-fact (ii) at `o = 1`, is supplied
by `omega_le_seqONote_repr`: at step `j = m − 2` the descent ordinal is still `≥ ω`, so the
generalized reduction `goodstein_dominates_of_index_le` (budget `j + 2 = m`) applies. Concretely
`f_1(m) = 2m ≤ goodsteinLength m + 2`. -/
theorem fastGrowing_one_le_goodsteinLength (n : ℕ) :
    fastGrowing 1 (n + 2) ≤ goodsteinLength (n + 2) + 2 := by
  have ho : (1 : ONote).NF := NF.oadd NF.zero 1 NFBelow.zero
  have hlhs : (oadd (1 : ONote) 1 0).repr = ω := by simp [ONote.repr]
  refine goodstein_dominates_of_index_le (o := 1) (m := n + 2) (j := n) ho ?_ ?_ ?_ ?_
  · have := le_goodsteinLength (n + 2); omega
  · omega
  · have hn1 : norm (1 : ONote) = 1 := by decide
    omega
  · rw [hlhs]; exact omega_le_seqONote_repr (le_refl n)

/-- **Non-diagonal reduction (length lower bound).** Like `goodstein_dominates_of_index_le` but
without the budget constraint `m ≤ j + 2` — it concludes about `fastGrowing o (j + 2)` (the step's
own budget) instead of `fastGrowing o m`. Whenever the descent at step `j` is `≥ ω^o`, the Goodstein
length is bounded below by `f_o(j+2)`. This is what converts the early-step ordinal bounds (where
`j ≈ log₂ m ≪ m`) into a **super-linear lower bound on `goodsteinLength`** (it cannot reach the
diagonal `f_o(m)`, but it does beat every polynomial). -/
theorem fastGrowing_step_le_goodsteinLength {o : ONote} (ho : o.NF) {m j : ℕ}
    (hj : j ≤ goodsteinLength m) (hnorm : norm o ≤ j + 2)
    (hidx : (oadd o 1 0).repr ≤ (seqONote m j).repr) :
    fastGrowing o (j + 2) ≤ goodsteinLength m + 2 := by
  have hNFidx : (oadd o 1 0).NF := NF.oadd ho 1 NFBelow.zero
  have hNFseq : (seqONote m j).NF := seqONote_NF m j
  have hbudget : norm (oadd o 1 0) ≤ j + 2 := by
    rw [norm_oadd, norm_zero]; simp only [PNat.one_coe]; omega
  have hindex : hardy (oadd o 1 0) (j + 2) ≤ hardy (seqONote m j) (j + 2) := by
    rcases eq_or_lt_of_le hidx with heq | hlt
    · have heqo : oadd o 1 0 = seqONote m j :=
        (@repr_inj (oadd o 1 0) (seqONote m j) hNFidx hNFseq).1 heq
      rw [heqo]
    · exact hardy_le_of_lt hNFidx hNFseq (lt_def.2 hlt) hbudget
  calc fastGrowing o (j + 2)
      ≤ hardy (oadd o 1 0) (j + 2) := fastGrowing_le_hardy_pow o ho (j + 2)
    _ ≤ hardy (seqONote m j) (j + 2) := hindex
    _ = hardy (seqONote m 0) 2 := (hardy_seqONote_telescope m j hj).symm
    _ = goodsteinLength m + 2 := hardy_seqONote_zero m

/-- **`goodsteinLength` is SUPER-LINEAR:** `fastGrowing 2 (Nat.log 2 m) ≤ goodsteinLength m + 2`
(for `Nat.log 2 m ≥ 3`, i.e. `m ≥ 8`). Since `fastGrowing 2 n = 2^n · n`, this reads
`goodsteinLength m ≳ 2^{log₂ m} · log₂ m = m · log₂ m` — a genuine super-linear (beats every linear)
lower bound, the first proof that `goodsteinLength` outgrows the polynomial regime. Assembly: at
the early step `j = log₂ m − 2` the descent ordinal is `≥ ω² = (oadd 2 1 0).repr`
(`omega_opow_le_seqONote_repr`, leading exponent still `≥ 2`); feed the non-diagonal reduction. The
budget here is only `log₂ m`, not `m` — closing the gap to `f_2(m)` needs the deeper recursion. -/
theorem fastGrowing_two_log_le_goodsteinLength {m : ℕ} (hm : 3 ≤ Nat.log 2 m) :
    fastGrowing 2 (Nat.log 2 m) ≤ goodsteinLength m + 2 := by
  set L := Nat.log 2 m with hL
  have hLm : L ≤ m := Nat.log_le_self 2 m
  have hglen : m ≤ goodsteinLength m := le_goodsteinLength m
  have ho : (2 : ONote).NF := by decide
  have hr2 : (oadd (2 : ONote) 1 0).repr = ω ^ (2 : Ordinal) := by
    rw [show (2 : ONote) = oadd 0 2 0 from rfl]; simp [ONote.repr]
  have hidx : (oadd (2 : ONote) 1 0).repr ≤ (seqONote m (L - 2)).repr := by
    rw [hr2]
    exact omega_opow_le_seqONote_repr (m := m) (i := L - 2) (k := 2)
      (by omega) (by omega) (by omega)
  have hnorm : norm (2 : ONote) ≤ (L - 2) + 2 := by
    have : norm (2 : ONote) = 2 := by decide
    omega
  have h := fastGrowing_step_le_goodsteinLength ho (m := m) (j := L - 2)
    (by omega) hnorm hidx
  rwa [show L - 2 + 2 = L from by omega] at h

/-- **The `o = 2` diagonal domination, REDUCED to a one-level-smaller length bound.** If
`m + 2 ≤ goodsteinLength (Nat.log 2 m)` then `fastGrowing 2 m ≤ goodsteinLength m + 2` — the true
diagonal `f_2(m)` bound (budget `m`, *not* `log₂ m`), the first genuine instance of Cichoń's lower
bound beyond `o = 1`. Assembly: the hypothesis feeds `two_le_leadExp_of_log_length` to keep the
leading exponent `≥ 2` through step `j = m − 2`, so the descent ordinal there is `≥ ω² =
(oadd 2 1 0).repr` (`opow_le_seqONote_repr`); the diagonal reduction `goodstein_dominates_of_index_le`
(budget `j + 2 = m`) then closes it. **This isolates the entire remaining `o = 2` obligation to the
self-referential length bound `m + 2 ≤ goodsteinLength (Nat.log 2 m)`** — provable for large `m` by a
strong induction on `m` (the lower length is astronomically larger than `m` once `Nat.log 2 m ≥ 4`),
the clean successor to the abandoned `ppCount` sparsity route. -/
theorem fastGrowing_two_le_goodsteinLength_of_log_length {m : ℕ} (hm : 4 ≤ m)
    (hlen : m + 2 ≤ goodsteinLength (Nat.log 2 m)) :
    fastGrowing 2 m ≤ goodsteinLength m + 2 := by
  have ho : (2 : ONote).NF := by decide
  have hr2 : (oadd (2 : ONote) 1 0).repr = ω ^ (2 : Ordinal) := by
    rw [show (2 : ONote) = oadd 0 2 0 from rfl]; simp [ONote.repr]
  set j := m - 2 with hj
  have hlead : 2 ≤ Nat.log (base j) (goodsteinSeq m j) :=
    two_le_leadExp_of_log_length hlen (by omega)
  have hv : goodsteinSeq m j ≠ 0 := by
    have := goodsteinSeq_ge_init m j (by omega); omega
  have hkb : (2 : ℕ) < base j := by simp only [base]; omega
  have hidx : (oadd (2 : ONote) 1 0).repr ≤ (seqONote m j).repr := by
    rw [hr2]; exact opow_le_seqONote_repr (m := m) (i := j) (k := 2) hlead hv hkb
  have hnorm : norm (2 : ONote) ≤ j + 2 := by
    have : norm (2 : ONote) = 2 := by decide
    omega
  have hgl : j ≤ goodsteinLength m := le_trans (by omega) (le_goodsteinLength m)
  exact goodstein_dominates_of_index_le (o := 2) (m := m) (j := j) ho hgl (by omega) hnorm hidx

/-- `2·m ≤ 2^m` for `m ≥ 2` (elementary; the slack that turns `f_2(m) = 2^m·m` into a clean
`≥ 2^{m+1}` exponential length bound). -/
theorem two_mul_le_two_pow {m : ℕ} (h : 2 ≤ m) : 2 * m ≤ 2 ^ m := by
  induction m with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_or_ge n 2 with hn | hn
    · have hn1 : n = 1 := by omega
      subst hn1; norm_num
    · have := ih hn; rw [pow_succ]; omega

/-- **Inductive step of Cichoń's exponential length bound.** If the *one-level-down* Goodstein
sequence runs `≥ m + 2` steps — `m + 2 ≤ goodsteinLength (Nat.log 2 m)` — then the seed-`m` length is
at least `2^{m+1} + m`. Combines the conditional `o = 2` domination
(`fastGrowing_two_le_goodsteinLength_of_log_length`, giving `2^m·m = f_2(m) ≤ goodsteinLength m + 2`)
with the slack `2^m ≥ m + 2`: `2^m·m − 2 ≥ 2^{m+1} + m` for `m ≥ 4`. This is the engine of the strong
induction in `goodsteinLength_exp_lower`: it converts an exponential length bound at the *small* seed
`Nat.log 2 m` into one at `m`, the self-reference at the heart of Cichoń's lower bound. -/
theorem exp_le_goodsteinLength_step {m : ℕ} (hm : 4 ≤ m)
    (hlen : m + 2 ≤ goodsteinLength (Nat.log 2 m)) :
    2 ^ (m + 1) + m ≤ goodsteinLength m := by
  have hdom := fastGrowing_two_le_goodsteinLength_of_log_length hm hlen
  simp only [ONote.fastGrowing_two] at hdom
  have hpow : m + 2 ≤ 2 ^ m := le_trans (by omega) (two_mul_le_two_pow (by omega))
  set P := 2 ^ m with hP
  set G := goodsteinLength m with hG
  have hd : 2 ≤ m - 2 := by omega
  have key : (m + 2) * 2 ≤ P * (m - 2) := Nat.mul_le_mul hpow hd
  have hsplit : P * m = P * (m - 2) + 2 * P := by
    have h2 : m - 2 + 2 = m := by omega
    calc P * m = P * ((m - 2) + 2) := by rw [h2]
      _ = P * (m - 2) + P * 2 := by rw [Nat.mul_add]
      _ = P * (m - 2) + 2 * P := by ring
  have hpsucc : 2 ^ (m + 1) = 2 * P := by rw [hP, pow_succ]; ring
  rw [hpsucc]; omega

/-- **Tail-recursive forward "all-nonzero" checker.** `gpos k v fuel` is `true` iff the `fuel`
consecutive Goodstein values `v = G_k, G_{k+1}, …, G_{k+fuel−1}` are all nonzero, computed by a single
forward pass (recursion structural on `fuel`, in tail position of `&&`, so it compiles to a *loop* — no
`fuel`-deep call stack, unlike `goodsteinSeq` itself). The tool that lets `native_decide` certify the
large finite base-case length bounds `goodsteinLength M ≥ 2^{M+1} + M` (`M ≤ 15`, up to `65551` steps)
that a naive `∀ n < N, goodsteinSeq M n ≠ 0` would stack-overflow on. -/
def gpos : ℕ → ℕ → ℕ → Bool
  | _, _, 0 => true
  | k, v, fuel + 1 => decide (v ≠ 0) && gpos (k + 1) (bump (base k) v - 1) fuel

/-- **Soundness of `gpos`:** if the forward pass from `G_k` reports all-nonzero for `fuel` steps, then
`goodsteinSeq M (k + j) ≠ 0` for every `j < fuel`. Induction on `fuel`, using that the threaded value
`bump (base k) (G_k) − 1` is exactly `G_{k+1}` (defeq) so the accumulator stays on the real sequence. -/
theorem gpos_goodstein (M : ℕ) : ∀ fuel k, gpos k (goodsteinSeq M k) fuel = true →
    ∀ j, j < fuel → goodsteinSeq M (k + j) ≠ 0 := by
  intro fuel
  induction fuel with
  | zero => intro k _ j hj; omega
  | succ fuel ih =>
    intro k hgp j hj
    rw [gpos, Bool.and_eq_true, decide_eq_true_eq] at hgp
    obtain ⟨hv0, hrest⟩ := hgp
    have hstep : bump (base k) (goodsteinSeq M k) - 1 = goodsteinSeq M (k + 1) := rfl
    rw [hstep] at hrest
    rcases Nat.eq_zero_or_pos j with hj0 | hjpos
    · subst hj0; rwa [Nat.add_zero]
    · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      have hres := ih (k + 1) hrest j' (by omega)
      rwa [show k + (j' + 1) = (k + 1) + j' from by omega]

/-- **Computable length lower bound.** `gpos 0 M N = true ⟹ N ≤ goodsteinLength M`: if the forward
pass certifies the first `N` Goodstein values nonzero, the first zero is at step `≥ N`. The bridge
from `native_decide` to the base-case length bounds. -/
theorem glen_ge_of_gpos {M N : ℕ} (h : gpos 0 M N = true) : N ≤ goodsteinLength M := by
  rw [goodsteinLength, Nat.le_find_iff]
  intro n hn
  have := gpos_goodstein M N 0 h n hn
  rwa [Nat.zero_add] at this

/-- **Cichoń's exponential length lower bound, the strong-induction engine** (conditional on finitely
many base cases). Given the base bounds `2^{M+1} + M ≤ goodsteinLength M` for `4 ≤ M < 16`, the same
bound holds for *every* `m ≥ 4`. Strong induction on `m`: for `m ≥ 16` the seed `L = Nat.log 2 m` is
`≥ 4` and `< m`, so the IH gives `goodsteinLength L ≥ 2^{L+1} + L ≥ (m+1) + L ≥ m + 2` (using
`m < 2^{L+1}`), which feeds `exp_le_goodsteinLength_step` to conclude `goodsteinLength m ≥ 2^{m+1} + m`;
for `4 ≤ m < 16` it is a base case. **This is Cichoń's lower bound:** the self-similarity
(`leadExp_ge_goodsteinSeq_log`) makes the exponential length bound *reproduce itself* one scale up. The
base hypothesis is purely computational (no deep content) — discharged by `gpos`/`native_decide` in
`goodsteinLength_exp_lower_uncond`. -/
theorem goodsteinLength_exp_lower
    (hbase : ∀ M, 4 ≤ M → M < 16 → 2 ^ (M + 1) + M ≤ goodsteinLength M) :
    ∀ m, 4 ≤ m → 2 ^ (m + 1) + m ≤ goodsteinLength m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm
    rcases Nat.lt_or_ge m 16 with hsmall | hbig
    · exact hbase m hm hsmall
    · set L := Nat.log 2 m with hL
      have hL4 : 4 ≤ L := by
        calc 4 = Nat.log 2 16 := by rw [show (16 : ℕ) = 2 ^ 4 from rfl, Nat.log_pow (by norm_num)]
          _ ≤ Nat.log 2 m := Nat.log_mono_right hbig
      have hLm : L < m := Nat.log_lt_self 2 (by omega)
      have ihL := ih L hLm hL4
      have hpowL : m + 1 ≤ 2 ^ (L + 1) := by
        have h := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) m
        rw [← hL] at h
        omega
      have hlen : m + 2 ≤ goodsteinLength L := by omega
      exact exp_le_goodsteinLength_step (by omega) hlen

/-- `norm (ofNat n) = n`: a finite notation `ofNat (k+1) = oadd 0 ⟨k+1⟩ 0` has CNF norm its single
coefficient. -/
theorem norm_ofNat (n : ℕ) : norm (ONote.ofNat n) = n := by
  cases n with
  | zero => rfl
  | succ k => rw [ONote.ofNat_succ, norm_oadd, norm_zero]; simp

/-! ### General level `o = n`: the full diagonal domination (for every finite `n`)

The `o = 2` machinery (self-similarity `leadExp_ge_goodsteinSeq_log` + exponential length bound)
generalizes verbatim to every finite level `n`. The only new ingredient is a *value* lower bound on
the one-level-down sequence: `goodsteinSeq (Nat.log 2 m) k ≥ n` for the first `m` steps, which needs
`goodsteinLength (Nat.log 2 m) ≥ m + n`. That follows from the small-regime termination law
(`goodsteinLength_le_of_small`): below its base a Goodstein value falls by *exactly one* each step, so
a value `< n` at step `k` forces termination within `n` more steps — hence the value stays `≥ n` until
`n` steps before the end. -/

/-- **Small-regime step:** below its base, a Goodstein value drops by exactly one
(`bump (base k) v = v` for `v < base k`, then the `−1`). -/
theorem goodsteinSeq_small_step (M k : ℕ) (h : goodsteinSeq M k < base k) :
    goodsteinSeq M (k + 1) = goodsteinSeq M k - 1 := by
  show bump (base k) (goodsteinSeq M k) - 1 = goodsteinSeq M k - 1
  rw [bump_eq_of_lt (base k) (goodsteinSeq M k) h]

/-- **Small-regime termination law:** once a Goodstein value is below its base it decreases by one per
step (base only grows, so it stays below), reaching `0` within `goodsteinSeq M k` steps. Hence
`goodsteinLength M ≤ k + goodsteinSeq M k` whenever `goodsteinSeq M k < base k`. -/
theorem goodsteinLength_le_of_small (M : ℕ) :
    ∀ v k, goodsteinSeq M k = v → goodsteinSeq M k < base k → goodsteinLength M ≤ k + v := by
  intro v
  induction v with
  | zero => intro k hv _; have := goodsteinLength_le hv; omega
  | succ v ih =>
    intro k hv hsmall
    have hstep := goodsteinSeq_small_step M k hsmall
    have hstep' : goodsteinSeq M (k + 1) = v := by omega
    have hsmall' : goodsteinSeq M (k + 1) < base (k + 1) := by
      rw [hstep']; simp only [base] at hsmall hv ⊢; omega
    have := ih (k + 1) hstep' hsmall'
    omega

/-- **A Goodstein term stays `≥ n` until `n` steps before it terminates** (general level). If
`n ≤ base k` and `k + n ≤ goodsteinLength M` then `n ≤ goodsteinSeq M k`: were it `< n ≤ base k`, the
small-regime law would force `goodsteinLength M ≤ k + goodsteinSeq M k < k + n`, contradiction.
Generalizes `two_le_goodsteinSeq` (the `n = 2` case). -/
theorem n_le_goodsteinSeq (M k n : ℕ) (hn : n ≤ base k) (hlen : k + n ≤ goodsteinLength M) :
    n ≤ goodsteinSeq M k := by
  by_contra hc
  rw [not_le] at hc
  have hsmall : goodsteinSeq M k < base k := lt_of_lt_of_le hc hn
  have := goodsteinLength_le_of_small M (goodsteinSeq M k) k rfl hsmall
  omega

/-- **The self-similarity reduction at general level `n`:** if `m + n ≤ goodsteinLength (Nat.log 2 m)`
then the seed-`m` leading exponent at step `k ≤ m` is `≥ n` (provided `n ≤ base k`). Chains
`n_le_goodsteinSeq` (the lower sequence stays `≥ n`) through `leadExp_ge_goodsteinSeq_log`. Generalizes
`two_le_leadExp_of_log_length`. -/
theorem n_le_leadExp_of_log_length {m k n : ℕ}
    (hlen : m + n ≤ goodsteinLength (Nat.log 2 m)) (hk : k ≤ m) (hkn : n ≤ base k) :
    n ≤ Nat.log (base k) (goodsteinSeq m k) :=
  le_trans (n_le_goodsteinSeq (Nat.log 2 m) k n hkn (by omega)) (leadExp_ge_goodsteinSeq_log m k)

/-- **The general diagonal domination, REDUCED to a one-level-smaller length bound.** For every finite
level `n`, if `m + n ≤ goodsteinLength (Nat.log 2 m)` (and `n ≤ m − 2`, `m ≥ 4`) then
`fastGrowing (ofNat n) m ≤ goodsteinLength m + 2` — the *true diagonal* `f_n(m)` bound at level `n`
(budget `m`). This is Cichoń's lower bound at every finite level, modulo the self-referential length
bound. Assembly: `n_le_leadExp_of_log_length` keeps the leading exponent `≥ n` through step
`j = m − 2`, so the descent ordinal there dominates `ω^n = (oadd (ofNat n) 1 0).repr`
(`opow_le_seqONote_repr`); the diagonal reduction `goodstein_dominates_of_index_le` closes it.
Generalizes `fastGrowing_two_le_goodsteinLength_of_log_length` to all `n`. -/
theorem fastGrowing_ofNat_le_goodsteinLength_of_log_length {n m : ℕ}
    (hnm : n ≤ m - 2) (hm : 4 ≤ m)
    (hlen : m + n ≤ goodsteinLength (Nat.log 2 m)) :
    fastGrowing (ONote.ofNat n) m ≤ goodsteinLength m + 2 := by
  set j := m - 2 with hj
  have ho : (ONote.ofNat n).NF := inferInstance
  have hrepr : (ONote.ofNat n).repr = (n : Ordinal) := ONote.repr_ofNat n
  have hlead : n ≤ Nat.log (base j) (goodsteinSeq m j) :=
    n_le_leadExp_of_log_length (m := m) (k := j) (n := n) hlen (by omega) (by simp only [base]; omega)
  have hv : goodsteinSeq m j ≠ 0 := by have := goodsteinSeq_ge_init m j (by omega); omega
  have hkb : n < base j := by simp only [base]; omega
  have hidx : (oadd (ONote.ofNat n) 1 0).repr ≤ (seqONote m j).repr := by
    have hr : (oadd (ONote.ofNat n) 1 0).repr = ω ^ (n : Ordinal) := by simp [ONote.repr, hrepr]
    rw [hr]
    exact opow_le_seqONote_repr (m := m) (i := j) (k := n) hlead hv hkb
  have hnorm : norm (ONote.ofNat n) ≤ j + 2 := by rw [norm_ofNat]; omega
  have hgl : j ≤ goodsteinLength m := le_trans (by omega) (le_goodsteinLength m)
  exact goodstein_dominates_of_index_le (o := ONote.ofNat n) (m := m) (j := j) ho hgl (by omega) hnorm hidx

/-- **`goodsteinLength` is NON-ELEMENTARY:** for every finite level `n`,
`fastGrowing (ofNat n) (log₂ m − n + 2) ≤ goodsteinLength m + 2` (for `1 ≤ m`, `2n ≤ log₂ m`).
Generalizes `fastGrowing_two_log_le_goodsteinLength` to all `n`: at the early step `i = log₂ m − n`
the leading exponent is still `≥ n` (`leadExp_ge_sub`), so the descent ordinal is `≥ ω^n =
(oadd (ofNat n) 1 0).repr` (`omega_opow_le_seqONote_repr`); feed the non-diagonal reduction. The
budget is `log₂ m − n` (not `m` — leadExp and budget trade off). Taking e.g. `n = log₂ m / 2` makes
the RHS exceed `f_{(log₂ m)/2}(…)` — a tower of exponentials of height `~log₂ m`, hence
`goodsteinLength` outgrows every elementary function. The diagonal `f_n(m)` (true domination, the
headline) still needs the steps-between-drops recursion. -/
theorem fastGrowing_ofNat_log_le_goodsteinLength (n : ℕ) {m : ℕ} (hm : 1 ≤ m)
    (hn : 2 * n ≤ Nat.log 2 m) :
    fastGrowing (ONote.ofNat n) (Nat.log 2 m - n + 2) ≤ goodsteinLength m + 2 := by
  set L := Nat.log 2 m with hL
  have hLlt : L < m := Nat.log_lt_self 2 (by omega)
  have hglen : m ≤ goodsteinLength m := le_goodsteinLength m
  have ho : (ONote.ofNat n).NF := inferInstance
  have hrepr : (ONote.ofNat n).repr = (n : Ordinal) := ONote.repr_ofNat n
  have hidx : (oadd (ONote.ofNat n) 1 0).repr ≤ (seqONote m (L - n)).repr := by
    have hr : (oadd (ONote.ofNat n) 1 0).repr = ω ^ (n : Ordinal) := by
      simp [ONote.repr, hrepr]
    rw [hr]
    exact omega_opow_le_seqONote_repr (m := m) (i := L - n) (k := n)
      (by omega) (by omega) (by omega)
  have hnorm : norm (ONote.ofNat n) ≤ (L - n) + 2 := by rw [norm_ofNat]; omega
  exact fastGrowing_step_le_goodsteinLength ho (m := m) (j := L - n) (by omega) hnorm hidx

/-! ### Anti-vacuity anchors (off any headline axiom path). -/

example : hardy (oadd 1 2 (oadd 0 3 0)) 4 = hardy (oadd 1 2 0) (hardy (oadd 0 3 0) 4) := by
  native_decide
example : hardy (oadd 1 3 0) 3 = (hardy (oadd 1 1 0))^[3] 3 := by native_decide
example : fastGrowing 2 3 ≤ hardy (oadd 2 1 0) 3 := by native_decide

-- The domination inequality `fastGrowing o m ≤ goodsteinLength m + 2` holds concretely in the
-- computable regime (small `o`, where it already kicks in at small `m`). A *backwards* or
-- vacuous headline would fail these. (For `o ≥ 2` the inequality is asymptotic — it first holds
-- at `m = 4`, where `goodsteinLength` is already astronomically large and beyond `native_decide`.)
-- The growth engine, witnessed: one bump strictly grows a value above its base
-- (`bump_gt`: `4 + 1 ≤ bump 2 4 = 27`), and the term stays `≥ m` (`goodsteinSeq_ge_init`:
-- `G(4,2) = 41 ≥ 4`). A vacuous/backwards recursion would fail these.
example : 4 + 1 ≤ bump 2 4 := by native_decide
example : 4 ≤ goodsteinSeq 4 2 := by native_decide
-- `log_bump`: the leading exponent bumps itself. `bump 2 5 = 28`, `log_3 28 = 3 = bump 2 (log_2 5)`.
example : Nat.log 3 (bump 2 5) = bump 2 (Nat.log 2 5) := by native_decide
-- `log_le_log_pred_succ`: one decrement lowers a log by ≤ 1 (`log_3 9 = 2`, `log_3 8 = 1`).
example : Nat.log 3 9 ≤ Nat.log 3 8 + 1 := by native_decide
-- `leadExp_drop_le_one`: leading exponent drops by ≤ 1 per step. `G(4,2)=41` (`log_4 41 = 2`),
-- `G(4,3)=60` (`log_5 60 = 2`): `2 ≤ 2 + 1`.
example : Nat.log (base 2) (goodsteinSeq 4 2) ≤ Nat.log (base 3) (goodsteinSeq 4 3) + 1 := by
  native_decide
-- `log_bump_pred_of_not_pow`: NO drop at a non-pure-power step. `n=5` (`2²=4 < 5`, not a pure
-- power): `bump 2 5 = 28`, `28−1 = 27`, `log_3 27 = 3 = bump 2 (log_2 5) = bump 2 2 = 3`. No drop.
example : Nat.log 3 (bump 2 5 - 1) = bump 2 (Nat.log 2 5) := by native_decide
-- the hypothesis is LOAD-BEARING: at a pure power `n=4=2²` the leading exponent DOES drop.
-- `bump 2 4 = 27`, `27−1 = 26`, `log_3 26 = 2 ≠ 3 = bump 2 (log_2 4)` — a genuine "borrow".
example : Nat.log 3 (bump 2 4 - 1) ≠ bump 2 (Nat.log 2 4) := by native_decide
-- `log_bump_pred_of_pow`: at the pure power `n=4` the drop is by EXACTLY one:
-- `log_3 26 = 2 = bump 2 (log_2 4) − 1 = 3 − 1 = 2`.
example : Nat.log 3 (bump 2 4 - 1) = bump 2 (Nat.log 2 4) - 1 := by native_decide
-- `ppCount`: `G(4,0)=4=2²` is a pure power (counts), `G(3,0)=3` is not (`2¹=2≠3`).
example : ppCount 4 1 = 1 := by native_decide
example : ppCount 3 1 = 0 := by native_decide
-- the sharpened telescope `leadExp_ge_sub_ppCount`, witnessed: `log_2 4 = 2 ≤ log_3 26 + ppCount 4 1
-- = 2 + 1 = 3`. A vacuous/backwards bound would fail this.
example : Nat.log 2 4 ≤ Nat.log (base 1) (goodsteinSeq 4 1) + ppCount 4 1 := by native_decide
-- `bump_eq_of_lt`: a single digit below its base is fixed (`bump 5 3 = 3`, `3 < 5`).
example : bump 5 3 = 3 := by native_decide
-- `leadExp_small_nonincreasing`: in the small regime the leading exponent only falls. `G(2,0)=2`,
-- `log_2 2 = 1 < base 0 = 2` (small); `G(2,1)=2`, `log_3 2 = 0 ≤ 1`. Non-increasing.
example : Nat.log (base 1) (goodsteinSeq 2 1) ≤ Nat.log (base 0) (goodsteinSeq 2 0) := by native_decide

-- the super-linear bound's interpretation, witnessed: `f_2(n) = 2^n·n` (`fastGrowing_two`), and the
-- step index `Nat.log 2 8 = 3` ⟹ the bound reads `f_2(3) = 24 ≤ goodsteinLength 8 + 2` (RHS huge).
example : fastGrowing 2 3 = 2 ^ 3 * 3 := by native_decide  -- = 24
example : Nat.log 2 8 = 3 := by native_decide

-- `bump_mono`: monotone in its argument. `bump 2 3 = 4 ≤ bump 2 5 = 10`.
example : bump 2 3 ≤ bump 2 5 := by native_decide
-- `leadExp_step_ge`: the per-step floor `bump(base k)(L_k) − 1 ≤ L_{k+1}`. At `m=4, k=2`:
-- `bump 4 2 − 1 = 1 ≤ log_5 54 = 2` (with `G(4,2)=41`, `L_2 = 2`, `G(4,3)=54`, `L_3 = 2`).
example : bump (base 2) (Nat.log (base 2) (goodsteinSeq 4 2)) - 1
    ≤ Nat.log (base 3) (goodsteinSeq 4 3) := by native_decide
-- `leadExp_ge_goodsteinSeq_log` (self-similarity): the leadExp sequence dominates the one-level-down
-- Goodstein sequence. `goodsteinSeq (log₂ 4 = 2) 2 = 1 ≤ log_4 41 = 2`. A backwards bound would fail.
example : goodsteinSeq (Nat.log 2 4) 2 ≤ Nat.log (base 2) (goodsteinSeq 4 2) := by native_decide
-- `two_le_goodsteinSeq`: a term stays `≥ 2` until two steps before it terminates.
-- `goodsteinLength 3 = 5`; at `k = 2` (`2+1 < 5`) the value `goodsteinSeq 3 2 = 3 ≥ 2`.
example : 2 ≤ goodsteinSeq 3 2 := by native_decide
example : fastGrowing 0 2 ≤ goodsteinLength 2 + 2 := by native_decide  -- 3 ≤ 5
example : fastGrowing 1 2 ≤ goodsteinLength 2 + 2 := by native_decide  -- 4 ≤ 5
example : fastGrowing 0 3 ≤ goodsteinLength 3 + 2 := by native_decide  -- 4 ≤ 7
example : fastGrowing 1 3 ≤ goodsteinLength 3 + 2 := by native_decide  -- 6 ≤ 7


-- ════════════════ ported: GoodsteinLike.lean ════════════════
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


-- ════════════════ ported: DominationBaseCases.lean ════════════════
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


-- ════════════════ ported: DominationOmega.lean ════════════════
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

end Goodstein.Dom
