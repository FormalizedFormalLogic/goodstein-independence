/-
# Goodstein.Dom — Tower
-/
module

public import GoodsteinPA.ToMathlib.Goodstein.Domination.BaseCases

@[expose] public section

namespace Goodstein.Dom

open ONote Ordinal

/-
# The FULL ω-power tower: diagonal domination at every level up to ε₀

`BaseCases.lean` closes the diagonal `f_o(m) ≤ goodsteinLength m + 2` at the individual limit
levels `o = ω`, `o = ω^j` (finite `j`), and `o = ω^ω`, each by an *ad hoc* bridge. This file makes
the climb **general in one stroke**: it proves the diagonal domination at EVERY ω-power-tower
level `o = ω↑↑k` (`towerO k`, `repr = ω↑↑k`), for every `k`, unconditionally and machine-checked.
Since `sup_k ω↑↑k = ε₀`, this is Cichoń's lower bound at a cofinal family of levels below `ε₀` —
"`goodsteinLength` grows like `f_{ε₀}`".

The proof rests on two general engines, each subsuming its per-level predecessors:

1. **The general length bootstrap** `two_mul_le_goodsteinLength_iter`:
   `goodsteinLength ((log₂)^[k] m) ≥ 2m` for every `k`. The key realization is that the *already
   proved* `o = ω` domination is strong enough at every depth — no `f_{ω^ω}`-strength bound at the
   deep seed is needed. What carries it is the clean finite-level **tower lower bound**
   `towerN_le_fastGrowing`: `f_{k+2}(t) ≥ towerN (k+1) (t+1)` (an `(k+1)`-fold iterated
   exponential), proved by induction on `k`. Composed with `f_ω(t) = f_{t+1}(t) ≥ f_{k+2}(t)`
   (index monotonicity) and the tower upper bound on `m` (`succ_le_towerN_log_iter`:
   `m + 1 ≤ towerN k ((log₂)^[k] m + 1)`), the `f_ω` length bound clears `2m` at every depth. This
   subsumes `two_mul_le_goodsteinLength_log` (k=1) and `two_mul_le_goodsteinLength_loglog` (k=2).

2. **The general ordinal bridge** `omegaTower_succ_le_seqONote_repr`: if the descent's `k`-fold
   leading exponent is in the large regime (`base i ≤ (log_{base i})^[k] (G_i)`), then the descent
   ordinal dominates `ω↑↑(k+1)`. Pure `toOrdinal` induction (`omegaTower_le_toOrdinal`), peeling one
   `Nat.log` per step. This subsumes `omega_omega_le_seqONote_repr` (k=1) and
   `omega_pow_omega_le_seqONote_repr` (k=2).

The crux at step `i = m − 2` is discharged by the self-similarity tower `iterLeadExp_dominates`
(read at a fixed index via `logSeq_iterate_apply`) feeding `n_le_goodsteinSeq` the bootstrap length
bound. Everything below is unconditional; the unconditional closures carry the finite-base-case
`native_decide` axioms (documented split) inherited through the `f_ω` bootstrap.
-/



/-! ## The iterated-exponential tower `towerN` and its basic estimates -/

/-- Iterated exponential tower: `towerN 0 t = t`, `towerN (k+1) t = 2 ^ towerN k t`. -/
def towerN : ℕ → ℕ → ℕ
  | 0, t => t
  | (k + 1), t => 2 ^ towerN k t

@[simp] lemma towerN_zero (t : ℕ) : towerN 0 t = t := rfl
@[simp] lemma towerN_succ (k t : ℕ) : towerN (k + 1) t = 2 ^ towerN k t := rfl

/-- `t ≤ towerN k t` (the tower is expansive). -/
lemma towerN_id_le (k t : ℕ) : t ≤ towerN k t := by
  induction k with
  | zero => simp
  | succ k ih => rw [towerN_succ]; exact le_trans ih (le_of_lt Nat.lt_two_pow_self)

/-- `towerN k` is monotone in its argument. -/
lemma towerN_mono_right (k : ℕ) {x y : ℕ} (h : x ≤ y) : towerN k x ≤ towerN k y := by
  induction k with
  | zero => simpa using h
  | succ k ih => rw [towerN_succ, towerN_succ]; exact Nat.pow_le_pow_right (by norm_num) ih

/-- For `k ≥ 1`, `2 ^ X ≤ towerN k (X + 1)`. -/
lemma two_pow_le_towerN_succ (k X : ℕ) : 2 ^ X ≤ towerN (k + 1) (X + 1) := by
  rw [towerN_succ]
  exact Nat.pow_le_pow_right (by norm_num) (le_trans (Nat.le_succ X) (towerN_id_le k (X + 1)))

/-- `towerN k (2^x) ≤ 2 ^ towerN k x` (pushing an exponential past the tower from below). -/
lemma towerN_two_pow_le (k x : ℕ) : towerN k (2 ^ x) ≤ 2 ^ towerN k x := by
  induction k with
  | zero => simp
  | succ k ih => rw [towerN_succ, towerN_succ]; exact Nat.pow_le_pow_right (by norm_num) ih

/-! ## Engine 1: the general length bootstrap -/

/-- **The general finite-level tower lower bound.** For every `k` and every `t ≥ 2`,
`towerN (k+1) (t+1) ≤ f_{k+2}(t)`: the `(k+2)`-nd fast-growing function at `t` dominates an
`(k+1)`-fold iterated exponential of `t+1`. By induction on `k`, using `f_{n+1}(t) = (f_n)^[t](t)`
(`fastGrowing_succ`), `(f)^[t] t ≥ (f)^[2] t = f(f(t))` (iterate monotonicity + `id ≤ f`), and the
IH applied twice — the inner application keeps the argument `≥ 2`, the outer lifts a tower height.
This is the engine that makes the *already proved* `o = ω` domination strong enough at every depth:
no deeper fast-growing bound is needed. -/
lemma towerN_le_fastGrowing (k : ℕ) : ∀ t, 2 ≤ t →
    towerN (k + 1) (t + 1) ≤ fastGrowing (ONote.ofNat (k + 2)) t := by
  induction k with
  | zero =>
    intro t ht
    rw [show (0 + 2) = 2 from rfl, fastGrowing_ofNat_two, towerN_succ, towerN_zero]
    calc 2 ^ (t + 1) = 2 ^ t * 2 := by rw [pow_succ]
      _ ≤ 2 ^ t * t := by gcongr
  | succ k ih =>
    intro t ht
    have hfs : fastGrowing (ONote.ofNat (k + 1 + 2))
        = fun i => (fastGrowing (ONote.ofNat (k + 2)))^[i] i := by
      rw [show (k + 1 + 2) = (k + 2) + 1 from rfl,
          fastGrowing_succ _ (fundamentalSequence_ofNat_succ (k + 2))]
    rw [hfs]
    set g := fastGrowing (ONote.ofNat (k + 2)) with hg
    have hexp : (id : ℕ → ℕ) ≤ g := fun n => le_fastGrowing _ n
    have hmono : g^[2] t ≤ g^[t] t := Function.monotone_iterate_of_id_le hexp ht t
    have h2it : g^[2] t = g (g t) := by
      rw [show (2 : ℕ) = 1 + 1 from rfl, Function.iterate_add_apply]; simp
    have hinner : towerN (k + 1) (t + 1) ≤ g t := ih t ht
    have hgt_ge : t + 1 ≤ g t := le_trans (towerN_id_le (k + 1) (t + 1)) hinner
    have hgt2 : 2 ≤ g t := by omega
    have houter : towerN (k + 1) (g t + 1) ≤ g (g t) := ih (g t) hgt2
    have hstep1 : towerN (k + 1) (towerN (k + 1) (t + 1) + 1) ≤ towerN (k + 1) (g t + 1) :=
      towerN_mono_right (k + 1) (by omega)
    have hstep2 : 2 ^ (towerN (k + 1) (t + 1)) ≤ towerN (k + 1) (towerN (k + 1) (t + 1) + 1) :=
      two_pow_le_towerN_succ k (towerN (k + 1) (t + 1))
    calc towerN (k + 1 + 1) (t + 1)
        = 2 ^ (towerN (k + 1) (t + 1)) := by rw [towerN_succ]
      _ ≤ towerN (k + 1) (towerN (k + 1) (t + 1) + 1) := hstep2
      _ ≤ towerN (k + 1) (g t + 1) := hstep1
      _ ≤ g (g t) := houter
      _ = g^[2] t := h2it.symm
      _ ≤ g^[t] t := hmono

/-- **The tower upper bound on the seed.** `m + 1 ≤ towerN k ((log₂)^[k] m + 1)`: the seed
`m` is below a `k`-fold tower of its own `k`-fold logarithm. By induction on `k`, using
`Nat.lt_pow_succ_log_self` and `towerN_two_pow_le`. -/
lemma succ_le_towerN_log_iter (k m : ℕ) :
    m + 1 ≤ towerN k ((Nat.log 2)^[k] m + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hlt : (Nat.log 2)^[k] m < 2 ^ ((Nat.log 2)^[k + 1] m + 1) := by
      rw [Function.iterate_succ_apply']
      exact Nat.lt_pow_succ_log_self (by norm_num) _
    calc m + 1 ≤ towerN k ((Nat.log 2)^[k] m + 1) := ih
      _ ≤ towerN k (2 ^ ((Nat.log 2)^[k + 1] m + 1)) := towerN_mono_right k (by omega)
      _ ≤ 2 ^ towerN k ((Nat.log 2)^[k + 1] m + 1) := towerN_two_pow_le k _
      _ = towerN (k + 1) ((Nat.log 2)^[k + 1] m + 1) := by rw [towerN_succ]

/-- `(log₂)^[k] m ≤ m`: iterated logarithm never increases. -/
lemma iterLog2_le_self (k m : ℕ) : (Nat.log 2)^[k] m ≤ m := by
  induction k with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ_apply']; exact le_trans (Nat.log_le_self 2 _) ih

/-- **THE GENERAL LENGTH BOOTSTRAP.** For every `k`, with the `k`-fold log seed `≥ 2^16` (and `≥ k+1`,
so `f_ω = f_{·+1}` reaches index `k+2`), the seed-`((log₂)^[k] m)` Goodstein descent runs at least
`2m` steps: `goodsteinLength ((log₂)^[k] m) ≥ 2m`.

The bound is proved from the **`o = ω` domination alone**, at every depth:
`goodsteinLength t ≥ f_ω(t) − 2 = f_{t+1}(t) − 2 ≥ f_{k+2}(t) − 2 ≥ towerN (k+1) (t+1) − 2 ≥
2^{m+1} − 2 ≥ 2m`, where `t = (log₂)^[k] m`. The last steps use `succ_le_towerN_log_iter`
(`m+1 ≤ towerN k (t+1)`, so `2^{m+1} ≤ towerN (k+1) (t+1)`). Generalizes
`two_mul_le_goodsteinLength_log` (k=1) and `two_mul_le_goodsteinLength_loglog` (k=2). -/
lemma two_mul_le_goodsteinLength_iter (k m : ℕ)
    (ht : 2 ^ 16 ≤ (Nat.log 2)^[k] m) (hk : k + 1 ≤ (Nat.log 2)^[k] m) :
    2 * m ≤ goodsteinLength ((Nat.log 2)^[k] m) := by
  set t := (Nat.log 2)^[k] m with htdef
  have ht2 : 2 ≤ t := le_trans (by norm_num) ht
  have hlen := fastGrowing_omega_le_goodsteinLength (m := t) ht
  rw [fastGrowing_omega_eq] at hlen
  have hidx : fastGrowing (ONote.ofNat (k + 2)) t ≤ fastGrowing (ONote.ofNat (t + 1)) t :=
    fastGrowing_ofNat_mono (by omega) (by omega)
  have hB := towerN_le_fastGrowing k t ht2
  have hA : m + 1 ≤ towerN k (t + 1) := by
    have := succ_le_towerN_log_iter k m; rw [← htdef] at this; exact this
  have hA2 : 2 ^ (m + 1) ≤ towerN (k + 1) (t + 1) := by
    rw [towerN_succ]; exact Nat.pow_le_pow_right (by norm_num) hA
  have hpow : 2 * (m + 1) ≤ 2 ^ (m + 1) := by
    have hmlt : m < 2 ^ m := Nat.lt_two_pow_self
    calc 2 * (m + 1) ≤ 2 * 2 ^ m := by omega
      _ = 2 ^ (m + 1) := by rw [pow_succ]; ring
  omega

/-! ## Engine 2: the ordinal tower and the general ordinal bridge -/

/-- Ordinal tower: `omegaTower 0 = 1`, `omegaTower (k+1) = ω ^ omegaTower k`, so `omegaTower k = ω↑↑k`
(`omegaTower 1 = ω`, `omegaTower 2 = ω^ω`, `omegaTower 3 = ω^{ω^ω}`, …). -/
noncomputable def omegaTower : ℕ → Ordinal
  | 0 => 1
  | (k + 1) => (ω : Ordinal) ^ omegaTower k

lemma omegaTower_succ_eq (k : ℕ) : omegaTower (k + 1) = (ω : Ordinal) ^ omegaTower k := rfl

/-- The ω-tower is monotone in its height (`x ≤ ω^x = omegaTower (k+1)`). -/
lemma omegaTower_mono : Monotone omegaTower := by
  refine monotone_nat_of_le_succ (fun k => ?_)
  rw [omegaTower_succ_eq]; exact right_le_opow (omegaTower k) one_lt_omega0

/-- **Cofinality of the ω-tower in ε₀.** Every normal-form `ONote` — i.e. every ordinal `< ε₀` — has
`repr` strictly below some tower level `ω↑↑k`. By structural induction on the notation: the leading
term `ω^{repr e}·n` is `< ω^{omegaTower ke} = ω↑↑(ke+1)` (`mul_lt_omega0_opow` on the IH for `e`), the
tail is `< ω↑↑ka` (IH for `a`), and both are absorbed below the next tower level, which is additively
principal (`isPrincipal_add_omega0_opow`). This is what turns the per-level diagonal domination into
the literal "for every `o < ε₀`" statement. -/
lemma exists_repr_lt_omegaTower : ∀ (o : ONote), o.NF → ∃ k, o.repr < omegaTower k := by
  intro o
  induction o with
  | zero =>
    intro _
    exact ⟨0, by show (0 : Ordinal) < omegaTower 0; rw [show omegaTower 0 = 1 from rfl]; exact one_pos⟩
  | oadd e n a ihe iha =>
    intro hNF
    obtain ⟨ke, hke⟩ := ihe hNF.fst
    obtain ⟨ka, hka⟩ := iha hNF.snd
    set K := max (ke + 1) ka with hK
    have hmul : (ω : Ordinal) ^ e.repr * ((n : ℕ) : Ordinal) < omegaTower (ke + 1) := by
      rw [omegaTower_succ_eq]
      have hc0 : (0 : Ordinal) < omegaTower ke := by
        have h := omegaTower_mono (Nat.zero_le ke)
        rw [show omegaTower 0 = 1 from rfl] at h; exact zero_lt_one.trans_le h
      have hae : (ω : Ordinal) ^ e.repr < ω ^ (omegaTower ke) :=
        (opow_lt_opow_iff_right one_lt_omega0).2 hke
      exact mul_lt_omega0_opow hc0 hae (natCast_lt_omega0 _)
    have hmulK : (ω : Ordinal) ^ e.repr * ((n : ℕ) : Ordinal) < omegaTower K :=
      lt_of_lt_of_le hmul (omegaTower_mono (le_max_left _ _))
    have hakK : a.repr < omegaTower K := lt_of_lt_of_le hka (omegaTower_mono (le_max_right _ _))
    have hprin : IsPrincipal (· + ·) (omegaTower (K + 1)) := by
      rw [omegaTower_succ_eq]; exact isPrincipal_add_omega0_opow _
    have hltK1 : omegaTower K ≤ omegaTower (K + 1) := omegaTower_mono (Nat.le_succ K)
    refine ⟨K + 1, ?_⟩
    have hrepr : (oadd e n a).repr = (ω : Ordinal) ^ e.repr * ((n : ℕ) : Ordinal) + a.repr := by
      simp [ONote.repr]
    rw [hrepr]
    exact hprin (lt_of_lt_of_le hmulK hltK1) (lt_of_lt_of_le hakK hltK1)

/-- ONote realization of the ordinal tower: `towerO 0 = 1`, `towerO (k+1) = oadd (towerO k) 1 0`.
`towerO 1 = ω`, `towerO 2 = ω^ω`, … (`repr_towerO`). -/
def towerO : ℕ → ONote
  | 0 => 1
  | (k + 1) => oadd (towerO k) 1 0

lemma towerO_NF (k : ℕ) : (towerO k).NF := by
  induction k with
  | zero => exact (by decide : (1 : ONote).NF)
  | succ k ih => exact NF.oadd ih 1 NFBelow.zero

lemma repr_towerO (k : ℕ) : (towerO k).repr = omegaTower k := by
  induction k with
  | zero => show (1 : ONote).repr = (1 : Ordinal); simp
  | succ k ih =>
    show (oadd (towerO k) 1 0).repr = (ω : Ordinal) ^ omegaTower k
    rw [← ih]; simp [ONote.repr]

lemma norm_towerO (k : ℕ) : norm (towerO k) = 1 := by
  induction k with
  | zero => decide
  | succ k ih =>
    show norm (oadd (towerO k) 1 0) = 1
    rw [norm_oadd, ih, norm_zero]; simp

/-- The `k`-fold base-`b` log of `0` is `0`. -/
lemma iterLog_zero (b k : ℕ) : (Nat.log b)^[k] 0 = 0 := by
  induction k with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ_apply', ih, Nat.log_zero_right]

/-- **The general `toOrdinal` core.** If the `k`-fold base-`b` logarithm of `w` is still `≥ b`, then
`toOrdinal b w ≥ omegaTower (k+1) = ω↑↑(k+1)`. By induction on `k`, peeling one `Nat.log` from the
inside per step. Generalizes `omega_omega_le_toOrdinal` (k=1) and the finite `opow_le_toOrdinal`. -/
lemma omegaTower_le_toOrdinal (b : ℕ) (hb : 2 ≤ b) :
    ∀ (k w : ℕ), b ≤ (Nat.log b)^[k] w → omegaTower (k + 1) ≤ toOrdinal b w := by
  have h1 : toOrdinal b 1 = 1 := by have h := toOrdinal_pow b hb 0; simpa using h
  have hbb : toOrdinal b b = ω := by
    have h := toOrdinal_pow b hb 1; rw [pow_one, h1, opow_one] at h; exact h
  have hSM : StrictMono (toOrdinal b) := fun a c hac => (toOrdinal_mono_and_bound b hb c).1 a hac
  intro k
  induction k with
  | zero =>
    intro w hw
    simp only [Function.iterate_zero, id_eq] at hw
    show (ω : Ordinal) ^ omegaTower 0 ≤ toOrdinal b w
    rw [show omegaTower 0 = 1 from rfl, opow_one, ← hbb]
    exact hSM.monotone hw
  | succ k ih =>
    intro w hw
    rw [Function.iterate_succ_apply] at hw
    have hwne : w ≠ 0 := by
      intro h0; rw [h0, Nat.log_zero_right, iterLog_zero] at hw; omega
    have ihw := ih (Nat.log b w) hw
    show (ω : Ordinal) ^ omegaTower (k + 1) ≤ toOrdinal b w
    calc (ω : Ordinal) ^ omegaTower (k + 1)
        ≤ ω ^ toOrdinal b (Nat.log b w) := opow_le_opow_right omega0_pos ihw
      _ ≤ toOrdinal b w := opow_toOrdinal_log_le b hb hwne

/-- **The general ordinal bridge on the descent.** If the descent's `k`-fold leading exponent is in
the large regime (`base i ≤ (log_{base i})^[k] (G_i)`), then `omegaTower (k+1) ≤ (seqONote m i).repr`.
Generalizes `omega_omega_le_seqONote_repr` (k=1) and `omega_pow_omega_le_seqONote_repr` (k=2). -/
lemma omegaTower_succ_le_seqONote_repr {m i k : ℕ}
    (hreg : base i ≤ (Nat.log (base i))^[k] (goodsteinSeq m i)) :
    omegaTower (k + 1) ≤ (seqONote m i).repr := by
  rw [repr_seqONote]
  exact omegaTower_le_toOrdinal (base i) (Nat.le_add_left 2 i) k _ hreg

/-- `(logSeq^[k] a) i = (Nat.log (base i))^[k] (a i)`: iterating the per-step `logSeq` operator and
reading at a fixed index `i` is the same as iterating `Nat.log (base i)` on `a i` (each `logSeq`
application reads the same `base i`). This is what lets the self-similarity tower
`iterLeadExp_dominates` (stated with `logSeq^[k]`) talk about the `k`-fold *fixed-base* leading
exponent that the ordinal bridge needs. -/
lemma logSeq_iterate_apply (a : ℕ → ℕ) (k i : ℕ) :
    (logSeq^[k] a) i = (Nat.log (base i))^[k] (a i) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    show Nat.log (base i) ((logSeq^[k] a) i) = Nat.log (base i) ((Nat.log (base i))^[k] (a i))
    rw [ih]

/-! ## The general diagonal domination — Cichoń's lower bound up to ε₀ -/

/-- **THE GENERAL DIAGONAL DOMINATION — UNCONDITIONAL.** For every `k`, with the `k`-fold log seed
`(log₂)^[k] m ≥ 2^16` (and `≥ k+1`), `fastGrowing (towerO k) m ≤ goodsteinLength m + 2`, where
`towerO k` has `repr = ω↑↑k`. This is Cichoń's lower bound at EVERY ω-power-tower level:
`k = 1` is `o = ω`, `k = 2` is `o = ω^ω`, `k = 3` is `o = ω^{ω^ω}`, …, and `sup_k ω↑↑k = ε₀`. One
general theorem subsuming all the per-level closures of `DominationOmega.lean`.

Assembly: the general length bootstrap (`two_mul_le_goodsteinLength_iter`) feeds `n_le_goodsteinSeq`
to keep the seed-`((log₂)^[k] m)` value `≥ m` at step `i = m−2`; the self-similarity tower
(`iterLeadExp_dominates`, read at index `i` via `logSeq_iterate_apply`) lifts that to the `k`-fold
leading exponent of the genuine descent being `≥ base i = m`; the general ordinal bridge
(`omegaTower_succ_le_seqONote_repr`) turns that into `ω↑↑(k+1) ≤ descent`; and the diagonal reduction
`goodstein_dominates_of_index_le` (budget `m`) closes it. Carries the finite-base-case
`native_decide` axioms (documented split), inherited via the `f_ω` length bootstrap. -/
lemma fastGrowing_le_goodsteinLength_of_repr_le_tower {o : ONote} (ho : o.NF) {m k : ℕ}
    (ht : 2 ^ 16 ≤ (Nat.log 2)^[k] m) (hk : k + 1 ≤ (Nat.log 2)^[k] m)
    (hrepr : o.repr ≤ omegaTower k) (hnorm : norm o ≤ m) :
    fastGrowing o m ≤ goodsteinLength m + 2 := by
  have hmge : 2 ^ 16 ≤ m := le_trans ht (iterLog2_le_self k m)
  have hm : 4 ≤ m := le_trans (by norm_num) hmge
  set i := m - 2 with hi
  have hbase : base i = m := by simp only [base, hi]; omega
  have hlen : i + m ≤ goodsteinLength ((Nat.log 2)^[k] m) := by
    have := two_mul_le_goodsteinLength_iter k m ht hk; omega
  have hval : m ≤ goodsteinSeq ((Nat.log 2)^[k] m) i :=
    n_le_goodsteinSeq ((Nat.log 2)^[k] m) i m (by rw [hbase]) hlen
  have hdom : goodsteinSeq ((Nat.log 2)^[k] m) i ≤ (Nat.log (base i))^[k] (goodsteinSeq m i) := by
    have h := iterLeadExp_dominates m k i
    rwa [logSeq_iterate_apply] at h
  have hreg : base i ≤ (Nat.log (base i))^[k] (goodsteinSeq m i) := by
    calc base i = m := hbase
      _ ≤ goodsteinSeq ((Nat.log 2)^[k] m) i := hval
      _ ≤ (Nat.log (base i))^[k] (goodsteinSeq m i) := hdom
  have hbridge : omegaTower (k + 1) ≤ (seqONote m i).repr := omegaTower_succ_le_seqONote_repr hreg
  have hidx : (oadd o 1 0).repr ≤ (seqONote m i).repr := by
    have hle : (oadd o 1 0).repr ≤ omegaTower (k + 1) := by
      have hr : (oadd o 1 0).repr = (ω : Ordinal) ^ o.repr := by simp [ONote.repr]
      rw [hr, omegaTower_succ_eq]
      exact opow_le_opow_right omega0_pos hrepr
    exact le_trans hle hbridge
  have hgl : i ≤ goodsteinLength m := le_trans (by omega) (le_goodsteinLength m)
  exact goodstein_dominates_of_index_le ho hgl (by omega) (by omega) hidx

/-- **Tower-level diagonal domination** (the special case `o = towerO k`, `repr = ω↑↑k`): for every
`k`, `fastGrowing (towerO k) m ≤ goodsteinLength m + 2`. `k = 1` is `o = ω`, `k = 2` is `o = ω^ω`,
`k = 3` is `o = ω^{ω^ω}`, …, with `sup_k ω↑↑k = ε₀`. Subsumes the per-level closures of
`DominationOmega.lean`. Immediate corollary of `fastGrowing_le_goodsteinLength_of_repr_le_tower`
(`repr (towerO k) = ω↑↑k`, `norm (towerO k) = 1 ≤ m`). -/
lemma fastGrowing_towerO_le_goodsteinLength {m k : ℕ}
    (ht : 2 ^ 16 ≤ (Nat.log 2)^[k] m) (hk : k + 1 ≤ (Nat.log 2)^[k] m) :
    fastGrowing (towerO k) m ≤ goodsteinLength m + 2 := by
  have hmge : 4 ≤ m := le_trans (by norm_num) (le_trans ht (iterLog2_le_self k m))
  refine fastGrowing_le_goodsteinLength_of_repr_le_tower (towerO_NF k) ht hk ?_ ?_
  · exact le_of_eq (repr_towerO k)
  · rw [norm_towerO]; omega

/-! ### Explicit thresholds and the ε₀ headline -/

/-- `towerN k N ≤ m ⟹ N ≤ (log₂)^[k] m`: an explicit threshold guaranteeing the `k`-fold log seed
is large. By induction on `k` via `Nat.le_log_of_pow_le`. -/
lemma threshold_le_iterLog (k N m : ℕ) (hm : towerN k N ≤ m) : N ≤ (Nat.log 2)^[k] m := by
  induction k generalizing m with
  | zero => simpa using hm
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    rw [towerN_succ] at hm
    exact ih (Nat.log 2 m) (Nat.le_log_of_pow_le Nat.one_lt_two hm)

/-- **Explicit-threshold form of the general diagonal domination.** For every `k` and every
`m ≥ towerN k (2^16 + k)` (a tower of height `k` over `2^16 + k`),
`fastGrowing (towerO k) m ≤ goodsteinLength m + 2`. The single threshold supplies both hypotheses of
`fastGrowing_towerO_le_goodsteinLength` (`2^16 ≤ (log₂)^[k] m` and `k+1 ≤ (log₂)^[k] m`). -/
lemma goodsteinLength_dominates_fastGrowing_towerO {m k : ℕ}
    (hm : towerN k (2 ^ 16 + k) ≤ m) :
    fastGrowing (towerO k) m ≤ goodsteinLength m + 2 := by
  have h := threshold_le_iterLog k (2 ^ 16 + k) m hm
  exact fastGrowing_towerO_le_goodsteinLength (by omega) (by omega)

/-- **THE ε₀ HEADLINE.** For every ω-power-tower level `k`, `goodsteinLength` eventually dominates
`f_{ω↑↑k}`: there is a threshold `N` (namely `towerN k (2^16 + k)`) past which
`fastGrowing (towerO k) m ≤ goodsteinLength m + 2`. Since `{ω↑↑k}` is cofinal in `ε₀`, this is
Cichoń's lower bound `goodsteinLength m + 2 ≥ f_o(m)` (eventually) for a family of `o` cofinal below
`ε₀` — the expedition's destination, fully machine-checked and unconditional. -/
lemma goodsteinLength_eventually_dominates_fastGrowing_towerO (k : ℕ) :
    ∃ N, ∀ m, N ≤ m → fastGrowing (towerO k) m ≤ goodsteinLength m + 2 :=
  ⟨towerN k (2 ^ 16 + k), fun _ hm => goodsteinLength_dominates_fastGrowing_towerO hm⟩

/-- **THE FULL ε₀ HEADLINE — Cichoń's lower bound for every `o < ε₀`.** For EVERY normal-form
`ONote` `o` (every ordinal `< ε₀`), `goodsteinLength` eventually dominates `f_o`: there is a threshold
`N` past which `fastGrowing o m ≤ goodsteinLength m + 2`. This is the complete diagonal lower bound —
not merely along the tower spine `ω↑↑k`, but at *every* ordinal below `ε₀` —
unconditional and machine-checked.

Proof: `exists_repr_lt_omegaTower` places `o` below some tower level `ω↑↑k` (cofinality of the tower
in `ε₀`); the threshold `N = max (towerN k (2^16+k)) (norm o)` supplies the deep-seed bound and the
budget `norm o ≤ m`; then `fastGrowing_le_goodsteinLength_of_repr_le_tower` (whose descent dominates
`ω↑↑(k+1) ≥ ω^{repr o}`) closes it. Carries the finite-base-case `native_decide` axioms (documented
split), inherited via the `f_ω` length bootstrap. -/
theorem goodsteinLength_eventually_dominates_fastGrowing {o : ONote} (ho : o.NF) :
    ∃ N, ∀ m, N ≤ m → fastGrowing o m ≤ goodsteinLength m + 2 := by
  obtain ⟨k, hk⟩ := exists_repr_lt_omegaTower o ho
  refine ⟨max (towerN k (2 ^ 16 + k)) (norm o), fun m hm => ?_⟩
  have hm1 : towerN k (2 ^ 16 + k) ≤ m := le_trans (le_max_left _ _) hm
  have hm2 : norm o ≤ m := le_trans (le_max_right _ _) hm
  have hseed := threshold_le_iterLog k (2 ^ 16 + k) m hm1
  exact fastGrowing_le_goodsteinLength_of_repr_le_tower ho (by omega) (by omega) (le_of_lt hk) hm2

/-- Anti-vacuity: the tower notation unfolds to the concrete `oadd` forms the per-level closures
used, and carries the genuine ε₀-approaching reprs — so the general theorem really subsumes them. -/
example : towerO 1 = oadd 1 1 0 := rfl
example : towerO 2 = oadd (oadd 1 1 0) 1 0 := rfl
example : towerO 3 = oadd (oadd (oadd 1 1 0) 1 0) 1 0 := rfl
example : (towerO 1).repr = (ω : Ordinal) := by
  show (oadd 1 1 0 : ONote).repr = _; simp [ONote.repr]
example : (towerO 2).repr = (ω : Ordinal) ^ (ω : Ordinal) := by
  show (oadd (oadd 1 1 0) 1 0 : ONote).repr = _; simp [ONote.repr]
example : (towerO 3).repr = (ω : Ordinal) ^ ((ω : Ordinal) ^ (ω : Ordinal)) := by
  show (oadd (oadd (oadd 1 1 0) 1 0) 1 0 : ONote).repr = _; simp [ONote.repr]


/-
# The growth theorem: `goodsteinLength` grows like `f_{ε₀}` — Cichoń's lower bound (audit surface)

**Designated audit surface for the growth headline.** The proof lives in this file and its
siblings (`Domination/*.lean`); the theorem below states the headline thinly and faithfully, the
way `Statement.lean` does for termination.

## What this says (the mathematical heart of Kirby–Paris)
Goodstein's theorem (termination) is proved in `Statement.lean`. Its *companion* — why Peano
Arithmetic cannot prove it (Kirby–Paris 1982) — rests on a growth gap: every PA-provably-total
function is dominated by some `f_α` with `α < ε₀`, while the Goodstein length function outgrows all of
them. The PA-syntactic statement is out of scope (see `Statement.lean` / `README.md`); the *growth
gap itself*, which lives entirely in mathlib, is the content here.

**`goodsteinLength_eventually_dominates_fastGrowing`**: for EVERY ordinal notation `o < ε₀` (every
normal-form `ONote`), `goodsteinLength` eventually dominates the fast-growing function `f_o`:
`∃ N, ∀ m ≥ N, fastGrowing o m ≤ goodsteinLength m + 2`. Since every PA-provably-total function is
dominated by some such `f_o`, `goodsteinLength` outgrows every PA-provably-total function — the formal
"Goodstein grows too fast for PA." The additive `+ 2` is the standard constant from Cichoń's identity
`goodsteinLength m = H_{o_m}(2) − 2`; the statement is domination up to `O(1)`.

This is Cichoń's lower bound in full: not merely along the `ω`-power tower `ω↑↑k` (which is cofinal in
`ε₀`), but at *every* ordinal below `ε₀`.

## Proof (delegated)
The descent ordinal of the base-2 Goodstein run stays above `ω↑↑(k+1)` for
`≈ m` steps (general ordinal bridge `omegaTower_succ_le_seqONote_repr`), where `k` is chosen by tower
cofinality (`exists_repr_lt_omegaTower`: every `o < ε₀` is below some `ω↑↑k`). The step count is
supplied by the general length bootstrap `two_mul_le_goodsteinLength_iter`, itself powered by the
already-proved `o = ω` domination and the clean finite-level tower bound `towerN_le_fastGrowing`. The
diagonal reduction `goodstein_dominates_of_index_le` (the Cichoń pipeline through the Hardy hierarchy)
closes it.

## Axioms
The unconditional closures carry the bare trust base `[propext, Classical.choice, Quot.sound]` plus
the finite-base-case `native_decide` artifacts (the computed lengths of the finitely many small
Goodstein runs `4 ≤ M < 16`) — a 🟢 finite/computational dependency, excluded from the math-axiom
count per the discharge doctrine. There are **no math axioms** and **no `sorry`**.
-/



/-- **THE GROWTH HEADLINE — Cichoń's lower bound, complete to ε₀.** For every ordinal notation
`o < ε₀` (every normal-form `ONote`), `goodsteinLength` eventually dominates `f_o`:
`∃ N, ∀ m ≥ N, fastGrowing o m ≤ goodsteinLength m + 2`. The thin, faithful audit statement;
the proof is `goodsteinLength_eventually_dominates_fastGrowing`. -/
theorem goodsteinLength_dominates_fastGrowing {o : ONote} (ho : o.NF) :
    ∃ N, ∀ m, N ≤ m → fastGrowing o m ≤ goodsteinLength m + 2 :=
  goodsteinLength_eventually_dominates_fastGrowing ho

/-- **`towerO` IS mathlib's `ε₀` fundamental sequence.** The iterate `(a ↦ ω^a)` from `0` that defines
`fastGrowingε₀` (mathlib's one-step extension to `ε₀`) is exactly our `towerO`:
`(fun a => oadd a 1 0)^[k+1] 0 = towerO k`. Faithfulness anchor: the tower domination really targets
the genuine `ε₀` hierarchy `ω, ω^ω, ω^{ω^ω}, …`. -/
lemma iterate_oadd_eq_towerO (k : ℕ) : (fun a => ONote.oadd a 1 0)^[k + 1] 0 = towerO k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih]
    rfl

/-- Consequently `fastGrowingε₀ (k+1) = fastGrowing (towerO k) (k+1)`: mathlib's `ε₀`-level function
is the diagonal over our tower. (Its *level* `k` grows with the argument, so this diagonal is genuinely
`ε₀`-fast and is NOT what the per-level headline dominates — the headline dominates each *fixed* `f_o`,
the faithful reading of "tracks `f_{ε₀}`".) -/
lemma fastGrowingε₀_eq_towerO (k : ℕ) :
    ONote.fastGrowingε₀ (k + 1) = fastGrowing (towerO k) (k + 1) := by
  rw [ONote.fastGrowingε₀, iterate_oadd_eq_towerO]

/-- **The matching UPPER bound.** `goodsteinLength m + 2 ≤ f_{o_m}(2)`, where `o_m = seqONote m 0` is
the base-2 ordinal of `m` (`= toONote 2 m`). Immediate from the Cichoń identity
`goodsteinLength m + 2 = H_{o_m}(2)` (`hardy_seqONote_zero`) and `hardy_le_fastGrowing` (Hardy ≤
fast-growing at the same index). Together with `goodsteinLength_dominates_fastGrowing` this squeezes
`goodsteinLength` inside the fast-growing hierarchy at the `ε₀` frontier — the two-sided "grows like
`f_{ε₀}`": from below it eventually beats every fixed `f_o` (`o < ε₀`); from above it never exceeds
`f` at its own ordinal `o_m < ε₀` (argument `2`). -/
theorem goodsteinLength_le_fastGrowing_ordinal (m : ℕ) :
    goodsteinLength m + 2 ≤ fastGrowing (seqONote m 0) 2 := by
  rw [← hardy_seqONote_zero m]
  exact hardy_le_fastGrowing (seqONote m 0) 2 (by norm_num)

/-- **THE TWO-SIDED CAPSTONE — "`goodsteinLength` grows like `f_{ε₀}`".** Packaging both directions as
the single definitive audit surface: for every `o < ε₀` (every NF `ONote`),
* **(lower)** `goodsteinLength` eventually dominates `f_o`: `∃ N, ∀ m ≥ N, f_o(m) ≤ goodsteinLength m + 2`;
* **(upper)** `goodsteinLength` never exceeds `f` at its own base-2 ordinal: `goodsteinLength m + 2 ≤
  f_{o_m}(2)` for all `m`.
So `goodsteinLength` sits exactly within the fast-growing hierarchy at the `ε₀` frontier — the formal
"Goodstein grows too fast for PA" (every PA-provably-total function is some `f_o`, `o < ε₀`; all are
eventually dominated). The exact Hardy pin is `hardy_seqONote_zero` (Cichoń) + `hardy_omega_pow_ofNat`
(`H_{ω^k}=f_k`). -/
theorem goodsteinLength_grows_like_fastGrowingε₀ :
    (∀ (o : ONote), o.NF → ∃ N, ∀ m, N ≤ m → fastGrowing o m ≤ goodsteinLength m + 2)
    ∧ (∀ m, goodsteinLength m + 2 ≤ fastGrowing (seqONote m 0) 2) :=
  ⟨fun _ ho => goodsteinLength_dominates_fastGrowing ho, goodsteinLength_le_fastGrowing_ordinal⟩

/-- Anti-vacuity: `f_{ε₀}` is the genuine extension to `ε₀` (mathlib's known value), and the tower the
headline ranges over is the genuine one. -/
example : ONote.fastGrowingε₀ 2 = 2048 := ONote.fastGrowingε₀_two
example : (towerO 1).repr = (ω : Ordinal) := by show (oadd 1 1 0 : ONote).repr = _; simp [ONote.repr]

end Goodstein.Dom
