/-
# `InternalCor34.lean` — the M-internal Rathjen §3 Cor 3.4 construction (codes)

The deepest remaining layer of the `hbound` wall: porting the ℕ-template Cor 3.4 slow-down
(`Grzegorczyk.lean`) onto the `InternalONote` codes inside `V ⊧ 𝗜𝚺₁`, to produce the slowed
`X`-definable descent `β : V → V` that `DescentSemantic.nonterminating_of_xDescent` consumes.

This file builds it bottom-up. **First brick: the lead-term multiplier `ibigMul`** (`ω^k·β` on codes).
Because in Cor 3.4 the lift `ω^(l+1)·βₙ` has a FIXED meta-level `l+1` (the Grzegorczyk domination
level from Lemma 3.2, a standard natural), `ibigMul` is a **meta-iterate of the internal `iomul`** — no
new `𝚺₁`-recursion table is needed; its `isNF`/`icmp`/`iC` laws come straight from the single-`ω` lemmas
(`isNF_iomul`, `icmp_iomul`, `iC_iomul`). This mirrors `Grz.bigMul`/`NF_bigMul`/`C_bigMul_le`.
-/
import GoodsteinPA.InternalONote

namespace GoodsteinPA.InternalONote

open LO LO.FirstOrder LO.FirstOrder.Arithmetic

variable {V : Type*} [ORingStructure V] [V ⊧ₘ* 𝗜𝚺₁]

/-- `ω^k · c` on codes, as the meta-`k`-fold iterate of the internal `ω·` (`iomul`). -/
noncomputable def ibigMul (k : ℕ) (c : V) : V := (iomul)^[k] c

@[simp] lemma ibigMul_zero (c : V) : ibigMul 0 c = c := rfl

lemma ibigMul_succ (k : ℕ) (c : V) : ibigMul (k + 1) c = iomul (ibigMul k c) :=
  Function.iterate_succ_apply' _ _ _

/-- `ω^k·c` is NF when `c` is (`isNF_iomul` iterated). -/
lemma isNF_ibigMul (k : ℕ) {c : V} (hc : isNF c) : isNF (ibigMul k c) := by
  induction k with
  | zero => simpa using hc
  | succ k ih => rw [ibigMul_succ]; exact isNF_iomul ih

/-- **`ω^k·` preserves the code comparison** (`icmp_iomul` iterated): the lead-term lift is
order-faithful, so Cor 3.4's across-block descent `β_{n+1} ≺ β_n ⟹ ω^k·β_{n+1} ≺ ω^k·β_n` transfers.
Mirror of the ℕ `repr_bigMul` monotonicity used in `Grz.corAlpha_boundary`. -/
lemma icmp_ibigMul (k : ℕ) {a b : V} (ha : isNF a) (hb : isNF b) :
    icmp (ibigMul k a) (ibigMul k b) = icmp a b := by
  induction k with
  | zero => simp [ibigMul_zero]
  | succ k ih =>
    rw [ibigMul_succ, ibigMul_succ, icmp_iomul (isNF_ibigMul k ha) (isNF_ibigMul k hb), ih]

/-- **`iC (ω^k·c) ≤ iC c + k`** (`iC_iomul` iterated; each `ω·` bumps the max coefficient by ≤ 1).
Mirror of `Grz.C_bigMul_le`; `k` is a meta-natural cast into `V`. -/
lemma iC_ibigMul_le (k : ℕ) (c : V) : iC (ibigMul k c) ≤ iC c + (k : V) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [ibigMul_succ]
    have h2 : iC (ibigMul k c) + 1 ≤ (iC c + (k : V)) + 1 := by gcongr
    have h3 : (iC c + (k : V)) + 1 = iC c + ((k + 1 : ℕ) : V) := by
      rw [Nat.cast_add, Nat.cast_one, add_assoc]
    calc iC (iomul (ibigMul k c)) ≤ iC (ibigMul k c) + 1 := iC_iomul _
      _ ≤ (iC c + (k : V)) + 1 := h2
      _ = iC c + ((k + 1 : ℕ) : V) := h3

/-! ## The internal `g0` — base case of the Rathjen Lemma 3.3 recursion (level `l = 0`)

Mirror of `Grz.g0 n m = ofNat ((n+2) -· m)`: a finite code `ω^0·((n+2)-m) = ocOadd 0 ((n+2)-m) 0`
when `m < n+2`, else `0`. This is the base of the meta-recursion `ig l` on the (standard) Grzegorczyk
level `l`. Its three structural laws — `isNF`, the within-block descent (`icmp`-decrease while
`m < n+1`, the internal `F 0 n`), and the value bound `iC ≤ n+2` — port `g0_NF`/`g0_desc`/`g0_bound`
verbatim, computed on codes with no ordinals (digit-direct `icmp_ocOadd`/`iC_ocOadd`). -/

/-- The internal base function `ig0 n m = ω^0·((n+2)-m)` on codes (a finite code), `0` past the block. -/
noncomputable def ig0 (n m : V) : V := if m < n + 2 then ocOadd 0 (n + 2 - m) 0 else 0

lemma ig0_of_lt {n m : V} (h : m < n + 2) : ig0 n m = ocOadd 0 (n + 2 - m) 0 := by
  simp only [ig0, if_pos h]

lemma ig0_of_ge {n m : V} (h : ¬ m < n + 2) : ig0 n m = 0 := by simp only [ig0, if_neg h]

/-- **Lemma 3.3 base, NF invariant**: every `ig0 n m` is a valid normal-form code. -/
lemma isNF_ig0 (n m : V) : isNF (ig0 n m) := by
  rcases lt_or_ge m (n + 2) with h | h
  · rw [ig0_of_lt h, isNF_ocOadd]
    refine ⟨?_, isNF_zero, isNF_zero, Or.inl rfl⟩
    exact (pos_sub_iff_lt.mpr h).ne'
  · rw [ig0_of_ge (not_lt.mpr h)]; exact isNF_zero

/-- **Lemma 3.3(1) base, descent**: `ig0 n (m+1) ≺ ig0 n m` while `m < F 0 n = n+1`
(`icmp … = 0` is the internal strict-`≺`). Both terms are finite; the coefficient drops by one. -/
lemma icmp_ig0_desc {n m : V} (hm : m < n + 1) :
    icmp (ig0 n (m + 1)) (ig0 n m) = 0 := by
  have hmn2 : m < n + 2 := lt_trans hm (by simp)
  have hm1n2 : m + 1 < n + 2 := by
    have h : m + 1 < (n + 1) + 1 := add_lt_add_of_lt_of_le hm (le_refl 1)
    have e : n + 1 + 1 = n + 2 := by rw [add_assoc, one_add_one_eq_two]
    rwa [e] at h
  rw [ig0_of_lt hm1n2, ig0_of_lt hmn2, icmp_ocOadd, icmp_zero_zero]
  -- thenV 1 _ = _ ; reduce to the coefficient comparison
  simp only [thenV]
  have hcmp : cmpV (n + 2 - (m + 1)) (n + 2 - m) = 0 := by
    apply cmpV_eq_zero.mpr
    -- (n+2)-(m+1) = ((n+2)-m) - 1 < (n+2)-m, since (n+2)-m > 0
    have hpos : (0 : V) < n + 2 - m := pos_sub_iff_lt.mpr hmn2
    have hrw : n + 2 - (m + 1) = n + 2 - m - 1 := Arithmetic.sub_sub.symm
    rw [hrw]
    have h1 : (1 : V) ≤ n + 2 - m := Arithmetic.one_le_of_zero_lt _ hpos
    calc (n + 2 - m) - 1 < ((n + 2 - m) - 1) + 1 := lt_add_one _
      _ = n + 2 - m := sub_add_self_of_le h1
  rw [hcmp]
  simp

/-- **Lemma 3.3(2) base, coefficient bound**: `iC (ig0 n m) ≤ n + 2` (`K = 2` half on codes). -/
lemma iC_ig0_le (n m : V) : iC (ig0 n m) ≤ n + 2 := by
  rcases lt_or_ge m (n + 2) with h | h
  · rw [ig0_of_lt h, iC_ocOadd, iC_zero]
    refine max_le (max_le (Arithmetic.zero_le _) ?_) (Arithmetic.zero_le _)
    exact sub_le_self _ _
  · rw [ig0_of_ge (not_lt.mpr h), iC_zero]; exact Arithmetic.zero_le _

end GoodsteinPA.InternalONote
