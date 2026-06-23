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

end GoodsteinPA.InternalONote
