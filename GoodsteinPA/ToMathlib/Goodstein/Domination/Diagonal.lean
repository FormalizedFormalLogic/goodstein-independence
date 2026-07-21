/-
# Goodstein.Dom — Diagonal
-/
module

public import GoodsteinPA.ToMathlib.Goodstein.Domination.LowerBound

@[expose] public section

namespace Goodstein.Dom

open ONote Ordinal

/-! ### CNF norm bounds: automatic budget satisfaction

`seqONote m j` has CNF norm `≤ j+1`, so the Hardy budget `norm ≤ j+2` is always satisfied. -/

/-- Every coefficient of `toONote b n` is a base-`b` digit, so its CNF norm is `< b`
(for `b ≥ 2`). Strong induction mirroring `toONote`'s peeling recursion: the leading digit
`n / b^(log b n) < b`, and the exponent `toONote b (log b n)` and tail `toONote b (n % …)`
recurse on strictly smaller arguments. -/
lemma norm_toONote_lt (b : ℕ) (hb : 2 ≤ b) : ∀ n, norm (toONote b n) < b := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases eq_or_ne n 0 with rfl | hn
    · rw [toONote_zero, norm_zero]; omega
    · have hb1 : 1 < b := by omega
      have hlog : Nat.log b n < n := Nat.log_lt_self b hn
      have hbe_pos : 0 < b ^ Nat.log b n := Nat.pow_pos (by omega)
      have hbe_le : b ^ Nat.log b n ≤ n := Nat.pow_log_le_self b hn
      have hr_lt : n % b ^ Nat.log b n < b ^ Nat.log b n := Nat.mod_lt _ hbe_pos
      have hr_lt_n : n % b ^ Nat.log b n < n := lt_of_lt_of_le hr_lt hbe_le
      have hc_pos : 0 < n / b ^ Nat.log b n := Nat.div_pos hbe_le hbe_pos
      have hc_lt : n / b ^ Nat.log b n < b := by
        rw [Nat.div_lt_iff_lt_mul hbe_pos, ← pow_succ']
        exact Nat.lt_pow_succ_log_self hb1 n
      rw [toONote, dif_neg hn, norm_oadd]
      have hcoeff : ((n / b ^ Nat.log b n).toPNat' : ℕ) = n / b ^ Nat.log b n :=
        PNat.toPNat'_coe hc_pos
      rw [hcoeff]
      have h1 := ih _ hlog
      have h2 := ih _ hr_lt_n
      omega

/-- **The Goodstein descent always meets the Hardy budget.** `norm (seqONote m j) ≤ j + 1`,
hence `≤ j + 2 =` the telescope argument. So `hardy_le_of_lt` is applicable at every telescope
step `j+2` (against any notation the budget reaches), with no further budget hypothesis. -/
lemma norm_seqONote_le (m j : ℕ) : norm (seqONote m j) ≤ j + 1 := by
  have h := norm_toONote_lt (j + 2) (by omega) (goodsteinSeq m j)
  show norm (toONote (j + 2) (goodsteinSeq m j)) ≤ j + 1
  omega

/-! ### Domination headline, reduced to ordinal domination

Assembles the full Cichoń pipeline (Hardy telescope, budget satisfaction, bridge to fast-growing)
modulo one deep input: ordinal domination (`seqONote m m > ω^o`). -/

/-- From ordinal domination, derive diagonal domination. -/
lemma goodstein_dominates_of_index {o : ONote} (ho : o.NF) {m : ℕ}
    (hnorm : norm o ≤ m) (hidx : oadd o 1 0 < seqONote m m) :
    fastGrowing o m ≤ goodsteinLength m + 2 := by
  have hNFidx : (oadd o 1 0).NF := NF.oadd ho 1 NFBelow.zero
  have hNFseq : (seqONote m m).NF := seqONote_NF m m
  have hbudget : norm (oadd o 1 0) ≤ m + 2 := by
    rw [norm_oadd, norm_zero]; simp only [PNat.one_coe]; omega
  -- index step at the high-budget argument `m+2`
  have hindex : hardy (oadd o 1 0) (m + 2) ≤ hardy (seqONote m m) (m + 2) :=
    hardy_le_of_lt hNFidx hNFseq hidx hbudget
  -- telescope: the Hardy value is invariant; at `j = m` it equals `goodsteinLength m + 2`
  have htel : hardy (seqONote m 0) 2 = hardy (seqONote m m) (m + 2) :=
    hardy_seqONote_telescope m m (le_goodsteinLength m)
  have hz : hardy (seqONote m 0) 2 = goodsteinLength m + 2 := hardy_seqONote_zero m
  calc fastGrowing o m
      ≤ fastGrowing o (m + 2) := fastGrowing_monotone o (by omega)
    _ ≤ hardy (oadd o 1 0) (m + 2) := fastGrowing_le_hardy_pow o ho (m + 2)
    _ ≤ hardy (seqONote m m) (m + 2) := hindex
    _ = hardy (seqONote m 0) 2 := htel.symm
    _ = goodsteinLength m + 2 := hz

/-- **The domination dichotomy (fully proved, unconditional).** For every fixed level `o`
(with budget `norm o ≤ m`), at the diagonal `m` exactly one of two structural alternatives
holds:

* **(A)** Goodstein dominates: `fastGrowing o m ≤ goodsteinLength m + 2`; or
* **(B)** the length is Hardy-bounded: `goodsteinLength m + 2 ≤ hardy (oadd o 1 0) (m + 2)`.

The proof needs no index hypothesis: because `norm (seqONote m m) ≤ m + 1` (the budget is
automatic on the descent, `norm_seqONote_le`), `hardy_le_of_lt` applies in *whichever*
direction the trichotomy `seqONote m m` vs `oadd o 1 0` falls. The whole headline thus reduces
to **ruling out branch (B) for large `m`** — i.e. to the deep fact that the descent stays above
`ω^o` for at least `m` steps; branch (B) says the descent has already dropped
below `ω^o` by step `m`, which is conjecturally impossible for large `m` but is exactly the
Cichoń lower-bound content not yet formalized. -/
lemma goodstein_dominates_or_hardy_bound {o : ONote} (ho : o.NF) {m : ℕ}
    (hnorm : norm o ≤ m) :
    fastGrowing o m ≤ goodsteinLength m + 2 ∨
      goodsteinLength m + 2 ≤ hardy (oadd o 1 0) (m + 2) := by
  have hNFidx : (oadd o 1 0).NF := NF.oadd ho 1 NFBelow.zero
  have hNFseq : (seqONote m m).NF := seqONote_NF m m
  have hval : hardy (seqONote m m) (m + 2) = goodsteinLength m + 2 := by
    rw [← hardy_seqONote_telescope m m (le_goodsteinLength m), hardy_seqONote_zero]
  have hbseq : norm (seqONote m m) ≤ m + 2 := le_trans (norm_seqONote_le m m) (by omega)
  rcases lt_trichotomy (seqONote m m).repr (oadd o 1 0).repr with hlt | heq | hgt
  · -- descent already below `ω^o` at step `m` (strict): branch (B)
    right
    have hcmp : seqONote m m < oadd o 1 0 := lt_def.2 hlt
    have h := hardy_le_of_lt hNFseq hNFidx hcmp hbseq
    rwa [hval] at h
  · -- descent exactly at `ω^o`: branch (B), via equality
    right
    have heqo : seqONote m m = oadd o 1 0 := (@repr_inj (seqONote m m) (oadd o 1 0) hNFseq hNFidx).1 heq
    exact le_of_eq (by rw [← hval, heqo])
  · -- descent still above `ω^o`: branch (A), via the reduction lemma
    left
    exact goodstein_dominates_of_index ho hnorm (lt_def.2 hgt)

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
Cichoń pipeline — *not* by `native_decide`. The deep input, at `o = 1`, is supplied
by `omega_le_seqONote_repr`: at step `j = m − 2` the descent ordinal is still `≥ ω`, so the
generalized reduction `goodstein_dominates_of_index_le` (budget `j + 2 = m`) applies. Concretely
`f_1(m) = 2m ≤ goodsteinLength m + 2`. -/
lemma fastGrowing_one_le_goodsteinLength (n : ℕ) :
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
lemma fastGrowing_step_le_goodsteinLength {o : ONote} (ho : o.NF) {m j : ℕ}
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
lemma fastGrowing_two_log_le_goodsteinLength {m : ℕ} (hm : 3 ≤ Nat.log 2 m) :
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
lemma fastGrowing_two_le_goodsteinLength_of_log_length {m : ℕ} (hm : 4 ≤ m)
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
lemma two_mul_le_two_pow {m : ℕ} (h : 2 ≤ m) : 2 * m ≤ 2 ^ m := by
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
lemma exp_le_goodsteinLength_step {m : ℕ} (hm : 4 ≤ m)
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
lemma gpos_goodstein (M : ℕ) : ∀ fuel k, gpos k (goodsteinSeq M k) fuel = true →
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
lemma glen_ge_of_gpos {M N : ℕ} (h : gpos 0 M N = true) : N ≤ goodsteinLength M := by
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
lemma norm_ofNat (n : ℕ) : norm (ONote.ofNat n) = n := by
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
lemma goodsteinSeq_small_step (M k : ℕ) (h : goodsteinSeq M k < base k) :
    goodsteinSeq M (k + 1) = goodsteinSeq M k - 1 := by
  show bump (base k) (goodsteinSeq M k) - 1 = goodsteinSeq M k - 1
  rw [bump_eq_of_lt (base k) (goodsteinSeq M k) h]

/-- **Small-regime termination law:** once a Goodstein value is below its base it decreases by one per
step (base only grows, so it stays below), reaching `0` within `goodsteinSeq M k` steps. Hence
`goodsteinLength M ≤ k + goodsteinSeq M k` whenever `goodsteinSeq M k < base k`. -/
lemma goodsteinLength_le_of_small (M : ℕ) :
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
lemma n_le_goodsteinSeq (M k n : ℕ) (hn : n ≤ base k) (hlen : k + n ≤ goodsteinLength M) :
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
lemma n_le_leadExp_of_log_length {m k n : ℕ}
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

end Goodstein.Dom
