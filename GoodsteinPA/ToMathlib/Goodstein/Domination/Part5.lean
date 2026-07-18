/-
# Goodstein.Dom — Part5
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
public import GoodsteinPA.ToMathlib.Goodstein.Domination.Part4
public meta import GoodsteinPA.ToMathlib.Goodstein.Domination.Part4  -- shake: keep

@[expose] public section

namespace Goodstein.Dom

open ONote Ordinal

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


-- ════════════════ ported: TowerDomination.lean ════════════════
/-
# The FULL ω-power tower: diagonal domination at every level up to ε₀

Lap 10 closed the diagonal `f_o(m) ≤ goodsteinLength m + 2` at the individual limit levels
`o = ω`, `o = ω^j` (finite `j`), and `o = ω^ω` (`DominationOmega.lean`), each by an *ad hoc* bridge.
This file makes the climb **general in one stroke**: it proves the diagonal domination at EVERY
ω-power-tower level `o = ω↑↑k` (`towerO k`, `repr = ω↑↑k`), for every `k`, unconditionally and
machine-checked. Since `sup_k ω↑↑k = ε₀`, this is Cichoń's lower bound at a cofinal family of levels
below `ε₀` — the destination of the expedition (`DIRECTION.md`: "`goodsteinLength` grows like
`f_{ε₀}`").

The proof rests on two general engines, each subsuming its per-level predecessors:

1. **The general length bootstrap** `two_mul_le_goodsteinLength_iter`:
   `goodsteinLength ((log₂)^[k] m) ≥ 2m` for every `k`. The key realization is that the *already
   proved* `o = ω` domination is strong enough at every depth — no `f_{ω^ω}`-strength bound at the
   deep seed is needed (the worry recorded in the lap-10 handoff). What carries it is the clean
   finite-level **tower lower bound** `towerN_le_fastGrowing`: `f_{k+2}(t) ≥ towerN (k+1) (t+1)`
   (an `(k+1)`-fold iterated exponential), proved by induction on `k`. Composed with
   `f_ω(t) = f_{t+1}(t) ≥ f_{k+2}(t)` (index monotonicity) and the tower upper bound on `m`
   (`succ_le_towerN_log_iter`: `m + 1 ≤ towerN k ((log₂)^[k] m + 1)`), the `f_ω` length bound clears
   `2m` at every depth. This subsumes `two_mul_le_goodsteinLength_log` (k=1) and
   `two_mul_le_goodsteinLength_loglog` (k=2).

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

@[simp] theorem towerN_zero (t : ℕ) : towerN 0 t = t := rfl
@[simp] theorem towerN_succ (k t : ℕ) : towerN (k + 1) t = 2 ^ towerN k t := rfl

/-- `t ≤ towerN k t` (the tower is expansive). -/
theorem towerN_id_le (k t : ℕ) : t ≤ towerN k t := by
  induction k with
  | zero => simp
  | succ k ih => rw [towerN_succ]; exact le_trans ih (le_of_lt Nat.lt_two_pow_self)

/-- `towerN k` is monotone in its argument. -/
theorem towerN_mono_right (k : ℕ) {x y : ℕ} (h : x ≤ y) : towerN k x ≤ towerN k y := by
  induction k with
  | zero => simpa using h
  | succ k ih => rw [towerN_succ, towerN_succ]; exact Nat.pow_le_pow_right (by norm_num) ih

/-- For `k ≥ 1`, `2 ^ X ≤ towerN k (X + 1)`. -/
theorem two_pow_le_towerN_succ (k X : ℕ) : 2 ^ X ≤ towerN (k + 1) (X + 1) := by
  rw [towerN_succ]
  exact Nat.pow_le_pow_right (by norm_num) (le_trans (Nat.le_succ X) (towerN_id_le k (X + 1)))

/-- `towerN k (2^x) ≤ 2 ^ towerN k x` (pushing an exponential past the tower from below). -/
theorem towerN_two_pow_le (k x : ℕ) : towerN k (2 ^ x) ≤ 2 ^ towerN k x := by
  induction k with
  | zero => simp
  | succ k ih => rw [towerN_succ, towerN_succ]; exact Nat.pow_le_pow_right (by norm_num) ih

/-! ## Engine 1: the general length bootstrap -/

/-- **The general finite-level tower lower bound (Claim B).** For every `k` and every `t ≥ 2`,
`towerN (k+1) (t+1) ≤ f_{k+2}(t)`: the `(k+2)`-nd fast-growing function at `t` dominates an
`(k+1)`-fold iterated exponential of `t+1`. By induction on `k`, using `f_{n+1}(t) = (f_n)^[t](t)`
(`fastGrowing_succ`), `(f)^[t] t ≥ (f)^[2] t = f(f(t))` (iterate monotonicity + `id ≤ f`), and the
IH applied twice — the inner application keeps the argument `≥ 2`, the outer lifts a tower height.
This is the engine that makes the *already proved* `o = ω` domination strong enough at every depth:
no deeper fast-growing bound is needed. -/
theorem towerN_le_fastGrowing (k : ℕ) : ∀ t, 2 ≤ t →
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

/-- **The tower upper bound on the seed (Claim A).** `m + 1 ≤ towerN k ((log₂)^[k] m + 1)`: the seed
`m` is below a `k`-fold tower of its own `k`-fold logarithm. By induction on `k`, using
`Nat.lt_pow_succ_log_self` and `towerN_two_pow_le`. -/
theorem succ_le_towerN_log_iter (k m : ℕ) :
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
theorem iterLog2_le_self (k m : ℕ) : (Nat.log 2)^[k] m ≤ m := by
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
theorem two_mul_le_goodsteinLength_iter (k m : ℕ)
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

theorem omegaTower_succ_eq (k : ℕ) : omegaTower (k + 1) = (ω : Ordinal) ^ omegaTower k := rfl

/-- The ω-tower is monotone in its height (`x ≤ ω^x = omegaTower (k+1)`). -/
theorem omegaTower_mono : Monotone omegaTower := by
  refine monotone_nat_of_le_succ (fun k => ?_)
  rw [omegaTower_succ_eq]; exact right_le_opow (omegaTower k) one_lt_omega0

/-- **Cofinality of the ω-tower in ε₀.** Every normal-form `ONote` — i.e. every ordinal `< ε₀` — has
`repr` strictly below some tower level `ω↑↑k`. By structural induction on the notation: the leading
term `ω^{repr e}·n` is `< ω^{omegaTower ke} = ω↑↑(ke+1)` (`mul_lt_omega0_opow` on the IH for `e`), the
tail is `< ω↑↑ka` (IH for `a`), and both are absorbed below the next tower level, which is additively
principal (`isPrincipal_add_omega0_opow`). This is what turns the per-level diagonal domination into
the literal "for every `o < ε₀`" statement. -/
theorem exists_repr_lt_omegaTower : ∀ (o : ONote), o.NF → ∃ k, o.repr < omegaTower k := by
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

theorem towerO_NF (k : ℕ) : (towerO k).NF := by
  induction k with
  | zero => exact (by decide : (1 : ONote).NF)
  | succ k ih => exact NF.oadd ih 1 NFBelow.zero

theorem repr_towerO (k : ℕ) : (towerO k).repr = omegaTower k := by
  induction k with
  | zero => show (1 : ONote).repr = (1 : Ordinal); simp
  | succ k ih =>
    show (oadd (towerO k) 1 0).repr = (ω : Ordinal) ^ omegaTower k
    rw [← ih]; simp [ONote.repr]

theorem norm_towerO (k : ℕ) : norm (towerO k) = 1 := by
  induction k with
  | zero => decide
  | succ k ih =>
    show norm (oadd (towerO k) 1 0) = 1
    rw [norm_oadd, ih, norm_zero]; simp

/-- The `k`-fold base-`b` log of `0` is `0`. -/
theorem iterLog_zero (b k : ℕ) : (Nat.log b)^[k] 0 = 0 := by
  induction k with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ_apply', ih, Nat.log_zero_right]

/-- **The general `toOrdinal` core.** If the `k`-fold base-`b` logarithm of `w` is still `≥ b`, then
`toOrdinal b w ≥ omegaTower (k+1) = ω↑↑(k+1)`. By induction on `k`, peeling one `Nat.log` from the
inside per step. Generalizes `omega_omega_le_toOrdinal` (k=1) and the finite `opow_le_toOrdinal`. -/
theorem omegaTower_le_toOrdinal (b : ℕ) (hb : 2 ≤ b) :
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
theorem omegaTower_succ_le_seqONote_repr {m i k : ℕ}
    (hreg : base i ≤ (Nat.log (base i))^[k] (goodsteinSeq m i)) :
    omegaTower (k + 1) ≤ (seqONote m i).repr := by
  rw [repr_seqONote]
  exact omegaTower_le_toOrdinal (base i) (Nat.le_add_left 2 i) k _ hreg

/-- `(logSeq^[k] a) i = (Nat.log (base i))^[k] (a i)`: iterating the per-step `logSeq` operator and
reading at a fixed index `i` is the same as iterating `Nat.log (base i)` on `a i` (each `logSeq`
application reads the same `base i`). This is what lets the self-similarity tower
`iterLeadExp_dominates` (stated with `logSeq^[k]`) talk about the `k`-fold *fixed-base* leading
exponent that the ordinal bridge needs. -/
theorem logSeq_iterate_apply (a : ℕ → ℕ) (k i : ℕ) :
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
theorem fastGrowing_le_goodsteinLength_of_repr_le_tower {o : ONote} (ho : o.NF) {m k : ℕ}
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
theorem fastGrowing_towerO_le_goodsteinLength {m k : ℕ}
    (ht : 2 ^ 16 ≤ (Nat.log 2)^[k] m) (hk : k + 1 ≤ (Nat.log 2)^[k] m) :
    fastGrowing (towerO k) m ≤ goodsteinLength m + 2 := by
  have hmge : 4 ≤ m := le_trans (by norm_num) (le_trans ht (iterLog2_le_self k m))
  refine fastGrowing_le_goodsteinLength_of_repr_le_tower (towerO_NF k) ht hk ?_ ?_
  · exact le_of_eq (repr_towerO k)
  · rw [norm_towerO]; omega

/-! ### Explicit thresholds and the ε₀ headline -/

/-- `towerN k N ≤ m ⟹ N ≤ (log₂)^[k] m`: an explicit threshold guaranteeing the `k`-fold log seed
is large. By induction on `k` via `Nat.le_log_of_pow_le`. -/
theorem threshold_le_iterLog (k N m : ℕ) (hm : towerN k N ≤ m) : N ≤ (Nat.log 2)^[k] m := by
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
theorem goodsteinLength_dominates_fastGrowing_towerO {m k : ℕ}
    (hm : towerN k (2 ^ 16 + k) ≤ m) :
    fastGrowing (towerO k) m ≤ goodsteinLength m + 2 := by
  have h := threshold_le_iterLog k (2 ^ 16 + k) m hm
  exact fastGrowing_towerO_le_goodsteinLength (by omega) (by omega)

/-- **THE ε₀ HEADLINE.** For every ω-power-tower level `k`, `goodsteinLength` eventually dominates
`f_{ω↑↑k}`: there is a threshold `N` (namely `towerN k (2^16 + k)`) past which
`fastGrowing (towerO k) m ≤ goodsteinLength m + 2`. Since `{ω↑↑k}` is cofinal in `ε₀`, this is
Cichoń's lower bound `goodsteinLength m + 2 ≥ f_o(m)` (eventually) for a family of `o` cofinal below
`ε₀` — the expedition's destination, fully machine-checked and unconditional. -/
theorem goodsteinLength_eventually_dominates_fastGrowing_towerO (k : ℕ) :
    ∃ N, ∀ m, N ≤ m → fastGrowing (towerO k) m ≤ goodsteinLength m + 2 :=
  ⟨towerN k (2 ^ 16 + k), fun _ hm => goodsteinLength_dominates_fastGrowing_towerO hm⟩

/-- **THE FULL ε₀ HEADLINE — Cichoń's lower bound for every `o < ε₀`.** For EVERY normal-form
`ONote` `o` (every ordinal `< ε₀`), `goodsteinLength` eventually dominates `f_o`: there is a threshold
`N` past which `fastGrowing o m ≤ goodsteinLength m + 2`. This is the complete diagonal lower bound —
not merely along the tower spine `ω↑↑k`, but at *every* ordinal below `ε₀` — the destination of the
expedition (`DIRECTION.md`), unconditional and machine-checked.

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


-- ════════════════ ported: GrowthStatement.lean ════════════════
/-
# The growth theorem: `goodsteinLength` grows like `f_{ε₀}` — Cichoń's lower bound (audit surface)

**Designated audit surface for the growth headline (C3 of `DIRECTION.md`).** The proof lives in
`TowerDomination.lean` and its siblings; this file states the headline thinly and faithfully, the way
`Statement.lean` does for termination.

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
`TowerDomination.lean`: the descent ordinal of the base-2 Goodstein run stays above `ω↑↑(k+1)` for
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



/-- **THE GROWTH HEADLINE (C3) — Cichoń's lower bound, complete to ε₀.** For every ordinal notation
`o < ε₀` (every normal-form `ONote`), `goodsteinLength` eventually dominates `f_o`:
`∃ N, ∀ m ≥ N, fastGrowing o m ≤ goodsteinLength m + 2`. The thin, faithful audit statement;
the proof is `TowerDomination.goodsteinLength_eventually_dominates_fastGrowing`. -/
theorem goodsteinLength_dominates_fastGrowing {o : ONote} (ho : o.NF) :
    ∃ N, ∀ m, N ≤ m → fastGrowing o m ≤ goodsteinLength m + 2 :=
  goodsteinLength_eventually_dominates_fastGrowing ho

/-- **`towerO` IS mathlib's `ε₀` fundamental sequence.** The iterate `(a ↦ ω^a)` from `0` that defines
`fastGrowingε₀` (mathlib's one-step extension to `ε₀`) is exactly our `towerO`:
`(fun a => oadd a 1 0)^[k+1] 0 = towerO k`. Faithfulness anchor: the tower domination really targets
the genuine `ε₀` hierarchy `ω, ω^ω, ω^{ω^ω}, …`. -/
theorem iterate_oadd_eq_towerO (k : ℕ) : (fun a => ONote.oadd a 1 0)^[k + 1] 0 = towerO k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih]
    rfl

/-- Consequently `fastGrowingε₀ (k+1) = fastGrowing (towerO k) (k+1)`: mathlib's `ε₀`-level function
is the diagonal over our tower. (Its *level* `k` grows with the argument, so this diagonal is genuinely
`ε₀`-fast and is NOT what the per-level headline dominates — the headline dominates each *fixed* `f_o`,
the faithful reading of "tracks `f_{ε₀}`".) -/
theorem fastGrowingε₀_eq_towerO (k : ℕ) :
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
(B4, `H_{ω^k}=f_k`). -/
theorem goodsteinLength_grows_like_fastGrowingε₀ :
    (∀ (o : ONote), o.NF → ∃ N, ∀ m, N ≤ m → fastGrowing o m ≤ goodsteinLength m + 2)
    ∧ (∀ m, goodsteinLength m + 2 ≤ fastGrowing (seqONote m 0) 2) :=
  ⟨fun _ ho => goodsteinLength_dominates_fastGrowing ho, goodsteinLength_le_fastGrowing_ordinal⟩

/-- Anti-vacuity: `f_{ε₀}` is the genuine extension to `ε₀` (mathlib's known value), and the tower the
headline ranges over is the genuine one. -/
example : ONote.fastGrowingε₀ 2 = 2048 := ONote.fastGrowingε₀_two
example : (towerO 1).repr = (ω : Ordinal) := by show (oadd 1 1 0 : ONote).repr = _; simp [ONote.repr]

end Goodstein.Dom
