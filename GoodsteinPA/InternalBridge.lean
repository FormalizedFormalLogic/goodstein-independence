/-
# `InternalBridge.lean` — E-core(b) brick 6: the standard-model bridge (faithfulness)

The internal `ipow`/`ilog`/`ibump`/`igoodstein` were built inside an arbitrary `V ⊧ₘ* 𝗜𝚺₁`. For the
expedition's **anti-fraud** guarantee they must agree with the *audited* `Defs.bump`/`Defs.goodsteinSeq`
on the standard model `ℕ` (itself a model of `𝗜𝚺₁`). This file establishes that absoluteness:

* `ipow b n = b ^ n`              (over `ℕ`)
* `ilog b n = Nat.log b n`        (over `ℕ`)
* `ibump b n = Defs.bump b n`     (over `ℕ`, base `2 ≤ b` — the only case Goodstein uses)
* `igoodstein m k = goodsteinSeq m k`

so the `𝚺₁`-definable internal run is the genuine Goodstein process, not a look-alike.
-/
module

public import GoodsteinPA.InternalGoodstein
public import GoodsteinPA.ToMathlib.Goodstein.Defs
public import GoodsteinPA.Domination
public import Mathlib.Data.Nat.Log
public import GoodsteinPA.Compat

@[expose] public section

namespace GoodsteinPA.InternalPow

open LO LO.FirstOrder LO.FirstOrder.Arithmetic

/-- Over `ℕ`, the internal power is `Nat.pow`. -/
@[simp] lemma ipow_nat (b n : ℕ) : ipow b n = b ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [ipow_succ, ih, pow_succ]

/-- Over `ℕ`, the internal logarithm is `Nat.log`. (Foundation's scoped `≤` on `ℕ` is `=∨<`, so we
convert it to `Nat.le` via `LO.FirstOrder.Arithmetic.le_def`; the `<` underneath is already `Nat.lt`.) -/
@[simp] lemma ilog_nat (b n : ℕ) : ilog b n = Nat.log b n := by
  symm
  rw [ilog_graph]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨hb, hn⟩ := h
    rw [LO.FirstOrder.Arithmetic.le_def] at hb
    rw [ipow_nat, ipow_nat, LO.FirstOrder.Arithmetic.le_def]
    exact ⟨Nat.eq_or_lt_of_le (Nat.pow_log_le_self b hn.ne'),
      Nat.lt_pow_succ_log_self (by omega) n⟩
  · rcases not_and_or.mp h with h1 | h1
    · rw [LO.FirstOrder.Arithmetic.le_def] at h1
      push Not at h1
      exact Nat.log_of_left_le_one (by omega) n
    · have : n = 0 := by omega
      subst this; simp

/-! ### Foundation `/`,`%` over `ℕ` agree with `Nat.div`/`Nat.mod`

Over `V = ℕ` the scoped Foundation `Div`/`Mod` instances are `Classical.choose!`-built and so are NOT
defeq to `Nat.instDiv`/`Nat.instMod`; the `ibump` peel recursion (`ibump_succ`) exposes the raw
Foundation `/`,`%`. These two bridges convert them to `Nat.div`/`Nat.mod` (`*`,`+`,`-` over `ℕ` ARE
already defeq, so only `/`,`%` need bridging), feeding the standard-model `ibump_nat`. -/

/-- Foundation division over `ℕ` is `Nat.div`. (Stated via `div_eq_of`, whose conclusion carries the
Foundation `Div` instance; the RHS `x / d` is `Nat`'s.) -/
lemma fdiv_nat (x d : ℕ) (hd : 0 < d) :
    @HDiv.hDiv ℕ ℕ ℕ (@instHDiv ℕ (@LO.FirstOrder.Arithmetic.instDiv_foundation ℕ _ _)) x d
      = x / d := by
  have hdm := Nat.div_add_mod x d
  have hml : x % d < d := Nat.mod_lt x hd
  refine div_eq_of (b := d) (c := x / d) ?_ ?_
  · rw [LO.FirstOrder.Arithmetic.le_def]
    rcases (show d * (x / d) ≤ x from by omega).lt_or_eq with h | h
    · exact Or.inr h
    · exact Or.inl h
  · show x < d * (x / d + 1)
    rw [Nat.mul_succ]; omega

/-- Foundation truncated subtraction over `ℕ` is `Nat.sub`. -/
lemma fsub_nat (x y : ℕ) :
    @HSub.hSub ℕ ℕ ℕ (@instHSub ℕ (@LO.FirstOrder.Arithmetic.instSub_foundation ℕ _ _)) x y
      = x - y := by
  by_cases h : y ≤ x
  · have hle : @LE.le ℕ (@LO.FirstOrder.Arithmetic.instLE_foundation ℕ _) y x :=
      LO.FirstOrder.Arithmetic.le_def.mpr (Or.symm h.lt_or_eq)
    have hf := LO.FirstOrder.Arithmetic.sub_spec_of_ge hle
    omega
  · have h' : x ≤ y := le_of_lt (Nat.lt_of_not_le h)
    have hle : @LE.le ℕ (@LO.FirstOrder.Arithmetic.instLE_foundation ℕ _) x y :=
      LO.FirstOrder.Arithmetic.le_def.mpr (Or.symm h'.lt_or_eq)
    rw [LO.FirstOrder.Arithmetic.sub_spec_of_le hle]
    omega

/-- Foundation remainder over `ℕ` is `Nat.mod`. -/
lemma fmod_nat (x d : ℕ) (hd : 0 < d) :
    @HMod.hMod ℕ ℕ ℕ (@instHMod ℕ (@LO.FirstOrder.Arithmetic.instMod_foundation ℕ _ _)) x d
      = x % d := by
  have hdm := Nat.div_add_mod x d
  rw [LO.FirstOrder.Arithmetic.mod_def, fdiv_nat x d hd, fsub_nat]
  omega

/-! ### The internal `bump`/`goodsteinSeq` are the audited ones over `ℕ` -/

/-- Over `ℕ` (base `2 ≤ b`), the internal hereditary base-change is `Defs.bump`. -/
theorem ibump_nat (b : ℕ) (hb : 2 ≤ b) (n : ℕ) : ibump b n = GoodsteinPA.bump b n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
      show ibump b (m + 1) = GoodsteinPA.bump b (m + 1)
      have hbF : @LE.le ℕ (@LO.FirstOrder.Arithmetic.instLE_foundation ℕ _) 2 b :=
        LO.FirstOrder.Arithmetic.le_def.mpr (Or.symm hb.lt_or_eq)
      have hb0 : 0 < b := by omega
      set e := Nat.log b (m + 1) with he
      have hpe : 0 < b ^ e := Nat.pow_pos hb0
      have hen : e < m + 1 := Nat.log_lt_self b (Nat.succ_ne_zero m)
      have hrn : (m + 1) % b ^ e < m + 1 :=
        lt_of_lt_of_le (Nat.mod_lt (m + 1) hpe) (Nat.pow_log_le_self b (Nat.succ_ne_zero m))
      rw [ibump_succ hbF m]
      simp only [ipow_nat, ilog_nat, ← he]
      rw [fdiv_nat (m + 1) (b ^ e) hpe, fmod_nat (m + 1) (b ^ e) hpe,
        ih e hen, ih ((m + 1) % b ^ e) hrn,
        GoodsteinPA.Dom.bump_pos b (m + 1) (Nat.succ_ne_zero m), ← he]

/-- Over `ℕ`, the internal Goodstein run is `Defs.goodsteinSeq`. -/
theorem igoodstein_nat (m₀ : ℕ) (k : ℕ) : igoodstein m₀ k = GoodsteinPA.goodsteinSeq m₀ k := by
  induction k with
  | zero => simp only [igoodstein_zero]; rfl
  | succ k ih =>
    -- `igoodstein_succ` produces `ibump (k+2) _` with the generic `AtLeastTwo` numeral and Foundation
    -- truncated subtraction; `fsub_nat` Natifies the `- 1` and `show` re-casts `k+2` to `Nat`'s literal
    -- so `ibump_nat` matches syntactically.
    rw [igoodstein_succ, ih, fsub_nat]
    show ibump (k + 2) (GoodsteinPA.goodsteinSeq m₀ k) - 1 = GoodsteinPA.goodsteinSeq m₀ (k + 1)
    rw [ibump_nat (k + 2) (by omega)]
    rfl

end GoodsteinPA.InternalPow
