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
import GoodsteinPA.Compat

namespace GoodsteinPA.InternalONote

open Classical
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.HierarchySymbol

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

/-! ## The V-indexed `ω^l · β` (generic Cor 3.4 lead, non-standard level `l : V`)

The meta-iterate `ibigMul (k : ℕ)` above is the **standard-level** lead `ω^(l+1)·β`. The generic
Rathjen §3 route needs `l : V` (the Grzegorczyk domination level computed from an *internal* primrec
descent index is itself internal, possibly non-standard). `iVbigMul β l = (ω·)^l β` is therefore built
as a genuine `𝚺₁` primitive recursion over `l : V` (mirroring `iAboveTable.construction`), with the
same three structural laws as `ibigMul` — but now provable by internal `sigma1_succ_induction` on `l`. -/

/-- Blueprint for `iVbigMul` (1 parameter = the seed `β`): `zero ↦ β`, `succ ↦ ω·(ih)`. -/
def iVbigMul.blueprint : PR.Blueprint 1 where
  zero := .mkSigma “y x. y = x”
  succ := .mkSigma “y ih n x. !iomulDef y ih”

noncomputable def iVbigMul.construction : PR.Construction V iVbigMul.blueprint where
  zero := fun x ↦ x 0
  succ := fun _ _ ih ↦ iomul ih
  zero_defined := .mk fun v ↦ by simp [iVbigMul.blueprint]
  succ_defined := .mk fun v ↦ by simp [iVbigMul.blueprint, iomul_defined.iff]

/-- `ω^l · β` on codes for an internal level `l : V` (the V-indexed iterate of `iomul`). -/
noncomputable def iVbigMul (β l : V) : V := iVbigMul.construction.result ![β] l

@[simp] lemma iVbigMul_zero (β : V) : iVbigMul β 0 = β := by
  simp [iVbigMul, iVbigMul.construction]

@[simp] lemma iVbigMul_succ (β l : V) : iVbigMul β (l + 1) = iomul (iVbigMul β l) := by
  simp [iVbigMul, iVbigMul.construction]

def _root_.LO.FirstOrder.Arithmetic.iVbigMulDef : 𝚺₁.Semisentence 3 :=
  iVbigMul.blueprint.resultDef.rew (Rew.subst ![#0, #2, #1])

instance iVbigMul_defined : 𝚺₁-Function₂ (iVbigMul : V → V → V) via iVbigMulDef := .mk
  fun v ↦ by simp [iVbigMul.construction.result_defined_iff, iVbigMulDef]; rfl

instance iVbigMul_definable : 𝚺₁-Function₂ (iVbigMul : V → V → V) := iVbigMul_defined.to_definable
instance iVbigMul_definable' (Γ) : Γ-[m + 1]-Function₂ (iVbigMul : V → V → V) :=
  iVbigMul_definable.of_sigmaOne

/-- `ω^l·β` is NF when `β` is (`isNF_iomul` iterated internally over `l : V`). -/
lemma isNF_iVbigMul {β : V} (hβ : isNF β) : ∀ l : V, isNF (iVbigMul β l) := by
  intro l
  induction l using ISigma1.sigma1_succ_induction
  · definability
  case zero => simpa using hβ
  case succ l ih => rw [iVbigMul_succ]; exact isNF_iomul ih

/-- **`ω^l·` preserves the code comparison** (`icmp_iomul` iterated internally over `l : V`). The
generic across-block descent `β_{n+1} ≺ β_n ⟹ ω^l·β_{n+1} ≺ ω^l·β_n`. -/
lemma icmp_iVbigMul {a b : V} (ha : isNF a) (hb : isNF b) :
    ∀ l : V, icmp (iVbigMul a l) (iVbigMul b l) = icmp a b := by
  intro l
  induction l using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ l ih => rw [iVbigMul_succ, iVbigMul_succ, icmp_iomul (isNF_iVbigMul ha l) (isNF_iVbigMul hb l), ih]

/-- **`iC (ω^l·c) ≤ iC c + l`** (`iC_iomul` iterated internally over `l : V`). -/
lemma iC_iVbigMul_le (c : V) : ∀ l : V, iC (iVbigMul c l) ≤ iC c + l := by
  intro l
  induction l using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ l ih =>
    rw [iVbigMul_succ]
    calc iC (iomul (iVbigMul c l)) ≤ iC (iVbigMul c l) + 1 := iC_iomul _
      _ ≤ (iC c + l) + 1 := by gcongr
      _ = iC c + (l + 1) := (add_assoc _ _ _)

-- The recursion `iVbigMul.construction.result ![β] l` never reduces definitionally on a variable `l`,
-- so any `whnf`/`isDefEq` that meets `iVbigMul β (l+1)` loops to the heartbeat limit. All downstream
-- use goes through the rewrite lemmas (`iVbigMul_zero`/`_succ`) and registered definability instance,
-- so making it irreducible (after those are established) is free and kills the blow-up.
attribute [irreducible] iVbigMul

/-- `ω^l·β ≠ 0` whenever `β ≠ 0` (each `ω·` preserves non-zero-ness). -/
lemma iVbigMul_ne_zero {β : V} (hβ0 : β ≠ 0) : ∀ l : V, iVbigMul β l ≠ 0 := by
  intro l
  induction l using ISigma1.sigma1_succ_induction
  · definability
  case zero => simpa using hβ0
  case succ l ih => rw [iVbigMul_succ]; exact iomul_ne_zero ih

/-- A finite code `ocOadd 0 c 0` (`c ≠ 0`) is in normal form. -/
lemma isNF_finCode {c : V} (hc : c ≠ 0) : isNF (ocOadd 0 c 0) := by
  rw [isNF_ocOadd]; exact ⟨hc, isNF_zero, isNF_zero, Or.inl rfl⟩

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

/-- `ig0 n m ≠ 0` in-block (`m < n+2`): it is a positive finite code. -/
lemma ig0_ne_zero {n m : V} (h : m < n + 2) : ig0 n m ≠ 0 := by
  rw [ig0_of_lt h]; exact ocOadd_ne_zero _ _ _

/-- `ocExp (ig0 n m) = 0` in-block: `ig0` is a finite code `ω^0·c`, top exponent `0`. -/
lemma ocExp_ig0 {n m : V} (h : m < n + 2) : ocExp (ig0 n m) = 0 := by
  rw [ig0_of_lt h, ocExp_ocOadd]

/-- **Lemma 3.3(2) base, coefficient bound**: `iC (ig0 n m) ≤ n + 2` (`K = 2` half on codes). -/
lemma iC_ig0_le (n m : V) : iC (ig0 n m) ≤ n + 2 := by
  rcases lt_or_ge m (n + 2) with h | h
  · rw [ig0_of_lt h, iC_ocOadd, iC_zero]
    refine max_le (max_le (Arithmetic.zero_le _) ?_) (Arithmetic.zero_le _)
    exact sub_le_self _ _
  · rw [ig0_of_ge (not_lt.mpr h), iC_zero]; exact Arithmetic.zero_le _

/-! ## The internal block term `iblk k c x = ω^k·c + x` (Rathjen Lemma 3.3 step lead term)

Mirror of `Grz.blk k c x = oadd (ofNat k) c x`. The lead exponent is the (standard) Grzegorczyk
level `k = l+1 ≥ 1`, so its code is the finite-ordinal code `ocOadd 0 k 0`. Two descent laws — the
*within-block* comparison (same `ω^k·c` head, the tail decides: `icmp_ocOadd_same_head`) and the
*block-boundary* comparison (a strictly smaller coefficient `c' < c` decides outright on NF codes:
`icmp_ocOadd_lt_coeff`) — are the internal `repr_blk_within`/`repr_blk_boundary`, proved purely by
the digit-direct `icmp_ocOadd` (no ordinals). They port verbatim into the `ig (l+1)` recursion. -/

/-- `iC (ocOadd 0 c 0) = c`: a finite-ordinal code's only coefficient is its value. -/
lemma iC_finCode (c : V) : iC (ocOadd 0 c 0) = c := by
  rw [iC_ocOadd]
  simp only [iC_zero]
  rw [max_eq_right (Arithmetic.zero_le c), max_eq_left (Arithmetic.zero_le c)]

/-- **Within-block comparison**: codes sharing the SAME head `ω^?·c` compare by their tails.
`icmp (ω^E·c + x') (ω^E·c + x) = icmp x' x`. (`Grz.repr_blk_within`, internal & general.) -/
lemma icmp_ocOadd_same_head (E c x x' : V) :
    icmp (ocOadd E c x') (ocOadd E c x) = icmp x' x := by
  rw [icmp_ocOadd, icmp_self E E le_rfl, cmpV_self]
  simp [thenV]

/-- **Block-boundary comparison**: a strictly smaller head coefficient decides `≺` outright — for
NF codes the tail is below `ω^E`, so the CNF (lexicographic) comparison ignores it.
`c' < c ⟹ icmp (ω^E·c' + x') (ω^E·c + x) = 0`. (`Grz.repr_blk_boundary`, internal & general.) -/
lemma icmp_ocOadd_lt_coeff {E c c' x x' : V} (hcc : c' < c) :
    icmp (ocOadd E c' x') (ocOadd E c x) = 0 := by
  rw [icmp_ocOadd, icmp_self E E le_rfl]
  have hc : cmpV c' c = 0 := cmpV_eq_zero.mpr hcc
  simp [thenV, hc]

/-- The internal block term `ω^k·c + x` on codes, lead exponent the finite level `k` (`k = l+1 ≥ 1`
in the recursion). Mirror of `Grz.blk`. -/
noncomputable def iblk (k : ℕ) (c x : V) : V := ocOadd (ocOadd 0 (k : V) 0) c x

/-- `iC (iblk k c x) = max (max k c) (iC x)` (`Grz.C_blk`, internal). -/
lemma iC_iblk (k : ℕ) (c x : V) : iC (iblk k c x) = max (max (k : V) c) (iC x) := by
  rw [iblk, iC_ocOadd, iC_finCode]

/-- **Within-block descent for `iblk`**: a strictly `≺`-smaller tail descends. -/
lemma icmp_iblk_within (k : ℕ) (c : V) {x x' : V} (hx : icmp x' x = 0) :
    icmp (iblk k c x') (iblk k c x) = 0 := by
  rw [iblk, iblk, icmp_ocOadd_same_head, hx]

/-- **Block-boundary descent for `iblk`**: a strictly smaller coefficient descends (any tails). -/
lemma icmp_iblk_boundary (k : ℕ) {c c' x x' : V} (hcc : c' < c) :
    icmp (iblk k c' x') (iblk k c x) = 0 := by
  rw [iblk, iblk]; exact icmp_ocOadd_lt_coeff hcc

/-- **NF of `iblk`** (`Grz.NF` step): NF when the level is live (`k ≥ 1`), the coefficient nonzero,
the tail NF, and the tail's lead exponent below the block exponent (`x = 0 ∨ icmp (ocExp x) … = 0`). -/
lemma isNF_iblk {k : ℕ} (hk : 1 ≤ k) {c x : V} (hc : c ≠ 0) (hx : isNF x)
    (htail : x = 0 ∨ icmp (ocExp x) (ocOadd 0 (k : V) 0) = 0) :
    isNF (iblk k c x) := by
  rw [iblk, isNF_ocOadd]
  refine ⟨hc, ?_, hx, htail⟩
  rw [isNF_ocOadd]
  refine ⟨?_, isNF_zero, isNF_zero, Or.inl rfl⟩
  have : (0 : V) < (k : V) := by exact_mod_cast hk
  exact this.ne'

/-! ## Internal Thm 3.5 reindex — the C-bound `iC(ω·αₙ + (K-i)) ≤ K(n+1)+i+1`

Rathjen **Theorem 3.5** reindexes a *slow* descent `α` (`iC(αₙ) ≤ K·(n+1)`) into the canonical-form
sequence `β_{K(n+1)+i} = ω·αₙ + (K-i)` with `C(βᵣ) ≤ r+1`. The internal C-bound below is the heart of
that reindex on codes — the mirror of `DescentCore.C_betaTail_le`, built purely from the existing
finite-tail toolkit (`iC_iomul` = "ω· bumps C by ≤1", `iC_iadd_finite` = clean append of a finite tail).
It is **level-agnostic** (no Grzegorczyk `g`, no Ackermann), so it is route-independent and lands in
IΣ₁. The within/boundary descent of the reindex is already `icmp_betaTail_within`/`_boundary`
(`InternalONote.lean`); the NF is `isNF_iadd_finite`. The remaining gap before a full internal `β : V → V`
is the index bookkeeping (`r = K(n+1)+i` via internal division) + the `j < K` ω-tower prefix, and the
*input* slow `α` (the deep Cor 3.4 crux). -/

/-- **Internal Thm 3.5 tail-term C-bound** (mirror of `DescentCore.C_betaTail_le`, on codes): the
reindex block `β_{K(n+1)+i} = ω·αₙ + (K-i)` of a slow descent has `iC ≤ K(n+1)+i+1`. Inputs: the
slowness `iC c ≤ K·(n+1)` of the block's base `c = αₙ`. -/
lemma iC_betaTail_le {c K n i : V} (hslow : iC c ≤ K * (n + 1)) :
    iC (iadd (iomul c) (ocOadd 0 (K - i) 0)) ≤ K * (n + 1) + i + 1 := by
  refine le_trans (iC_iadd_finite c (K - i)) (max_le ?_ ?_)
  · -- lead `ω·c`: `iC(ω·c) ≤ iC c + 1 ≤ K(n+1)+1 ≤ K(n+1)+i+1`
    calc iC (iomul c) ≤ iC c + 1 := iC_iomul c
      _ ≤ K * (n + 1) + 1 := by gcongr
      _ ≤ K * (n + 1) + i + 1 := add_le_add le_self_add (le_refl 1)
  · -- finite tail `K-i ≤ K ≤ K(n+1) ≤ K(n+1)+i+1`
    have hKi : K - i ≤ K := sub_le_self K i
    have hK : K ≤ K * (n + 1) := by
      calc K = K * 1 := (mul_one K).symm
        _ ≤ K * (n + 1) := by gcongr; exact le_add_self
    calc K - i ≤ K := hKi
      _ ≤ K * (n + 1) := hK
      _ ≤ K * (n + 1) + i + 1 := le_trans le_self_add le_self_add

/-! ## General clean-append for `iadd` (Cor 3.4's `ω^(l+1)·β + g`, `g` a genuine ordinal `< ω^(l+1)`)

Cor 3.4's slowed term is `αⱼ = ω^(l+1)·βₙ + g(l,n,m)` where the padding `g` is NOT finite (its `C` must
stay linear while it descends over a whole block of width `f_l(n)`). So the existing finite-tail toolkit
(`icmp_betaTail_within/_boundary`, tail `ocOadd 0 m 0`) does not apply: we need a **general clean append**
`iadd a b` where every leading exponent down `a`'s spine strictly dominates `b`'s leading exponent
(`icmp ea (ocExp b) = 2`), so `iadd` grafts `b` as a pure tail without merging. This is the internal
analog of `Grz.AllExpAbove` / `C_add_clean` / `corAlpha_within` / `corAlpha_boundary`.

The foundational fact is the single-step recursion `iadd_clean_step`: under the clean head condition the
`iadd` recursion takes its `gt` branch, preserving the head term and recursing into the tail. -/

/-- **Clean-append step.** When the second summand `b` is nonzero and the head exponent `ea` strictly
dominates `b`'s leading exponent (`icmp ea (ocExp b) = 2`), `iadd` keeps the head term and recurses into
the tail: `iadd (ω^ea·na + ra) b = ω^ea·na + iadd ra b`. (The `gt` branch of `iadd_ocOadd`.) -/
lemma iadd_clean_step {ea na ra b : V} (hb : b ≠ 0) (hcmp : icmp ea (ocExp b) = 2) :
    iadd (ocOadd ea na ra) b = ocOadd ea na (iadd ra b) := by
  rw [iadd_ocOadd, if_neg hb, if_neg (by rw [hcmp]; exact _root_.two_ne_zero),
      if_neg (by rw [hcmp]; exact (one_lt_two).ne')]

/-! ### The spine-dominance flag `iAbove e0 a` (every leading exponent down `a`'s spine `≻ e0`)

`iAbove e0 a = 1` iff every leading exponent occurring in `a`'s CNF spine strictly dominates `e0`
(`icmp · e0 = 2`) — the internal analog of `Grz.MinExpGe`/`AllExpAbove`. Then `iadd a b` with
`e0 = ocExp b` is a *clean append* (`b` grafted as a pure tail). Built as a parameterized (`e0`) `0/1`
flag via a course-of-values table, exactly like `isNFb` (parameter handled like `iaddTable`'s `b`). -/

/-- Step flag for `iAbove` (only evaluated at positive codes `i`, since index `0` is seeded): `1` iff
`i`'s leading exponent dominates `e0` AND the tail's flag (read at `ocTail i < i`) is `1`. -/
noncomputable def iAboveNext (e0 i s : V) : V :=
  if icmp (ocExp i) e0 = 2 then znth s (ocTail i) else 0

def _root_.LO.FirstOrder.Arithmetic.iAboveNextDef : 𝚺₁.Semisentence 4 := .mkSigma
  “y e0 i s.
    ∃ ei, !ocExpDef ei i ∧ ∃ cm, !icmpDef cm ei e0 ∧
      ( (cm = 2 ∧ ∃ ti, !sndIdxDef ti i ∧ !znthDef y s ti)
      ∨ (cm ≠ 2 ∧ y = 0) )”

instance iAboveNext_defined : 𝚺₁-Function₃ (iAboveNext : V → V → V → V) via iAboveNextDef := .mk
  fun v ↦ by
  simp [iAboveNextDef, iAboveNext, ocExp_defined.iff, ocTail, sndIdx_defined.iff,
    icmp_defined.iff, znth_defined.iff]
  by_cases h2 : icmp (ocExp (v 2)) (v 1) = 2 <;> simp [h2]

instance iAboveNext_definable : 𝚺₁-Function₃ (iAboveNext : V → V → V → V) :=
  iAboveNext_defined.to_definable

/-- Blueprint for the `iAbove` table (parameter = the threshold exponent `e0`). -/
def iAboveTable.blueprint : PR.Blueprint 1 where
  zero := .mkSigma “y x. !mkSeq₁Def y 1”
  succ := .mkSigma “y ih n x. ∃ v, !iAboveNextDef v x (n + 1) ih ∧ !seqConsDef y ih v”

noncomputable def iAboveTable.construction : PR.Construction V iAboveTable.blueprint where
  zero := fun _ ↦ !⟦1⟧
  succ := fun x n ih ↦ seqCons ih (iAboveNext (x 0) (n + 1) ih)
  zero_defined := .mk fun v ↦ by
    simp [iAboveTable.blueprint, mkSeq₁Def, seqCons_defined.iff, emptyset_def]
  succ_defined := .mk fun v ↦ by
    simp [iAboveTable.blueprint, iAboveNext_defined.iff, seqCons_defined.iff]

noncomputable def iAboveTable (e0 n : V) : V := iAboveTable.construction.result ![e0] n

@[simp] lemma iAboveTable_zero (e0 : V) : iAboveTable e0 0 = !⟦1⟧ := by
  simp [iAboveTable, iAboveTable.construction]

@[simp] lemma iAboveTable_succ (e0 n : V) :
    iAboveTable e0 (n + 1) = seqCons (iAboveTable e0 n) (iAboveNext e0 (n + 1) (iAboveTable e0 n)) := by
  simp [iAboveTable, iAboveTable.construction]

/-- **Spine-dominance flag** (`0/1`): `1` iff every leading exponent of `a`'s spine `≻ e0`. -/
noncomputable def iAboveb (e0 a : V) : V := znth (iAboveTable e0 a) a

/-- **Spine-dominance predicate**: every leading exponent down `a`'s CNF spine strictly dominates `e0`. -/
def iAbove (e0 a : V) : Prop := iAboveb e0 a = 1

def _root_.LO.FirstOrder.Arithmetic.iAboveTableDef : 𝚺₁.Semisentence 3 :=
  iAboveTable.blueprint.resultDef.rew (Rew.subst ![#0, #2, #1])

instance iAboveTable_defined : 𝚺₁-Function₂ (iAboveTable : V → V → V) via iAboveTableDef := .mk
  fun v ↦ by simp [iAboveTable.construction.result_defined_iff, iAboveTableDef]; rfl

instance iAboveTable_definable : 𝚺₁-Function₂ (iAboveTable : V → V → V) := iAboveTable_defined.to_definable
instance iAboveTable_definable' (Γ) : Γ-[m + 1]-Function₂ (iAboveTable : V → V → V) :=
  iAboveTable_definable.of_sigmaOne

def _root_.LO.FirstOrder.Arithmetic.iAvbDef : 𝚺₁.Semisentence 3 := .mkSigma
  “y e0 a. ∃ t, !iAboveTableDef t e0 a ∧ !znthDef y t a”

instance iAboveb_defined : 𝚺₁-Function₂ (iAboveb : V → V → V) via iAvbDef := .mk fun v ↦ by
  simp [iAvbDef, iAboveb, iAboveTable_defined.iff, znth_defined.iff]

instance iAboveb_definable : 𝚺₁-Function₂ (iAboveb : V → V → V) := iAboveb_defined.to_definable
instance iAboveb_definable' (Γ) : Γ-[m + 1]-Function₂ (iAboveb : V → V → V) :=
  iAboveb_definable.of_sigmaOne

instance iAbove_definable (Γ) : Γ-[m + 1]-Relation (iAbove : V → V → Prop) := by
  unfold iAbove; definability

/-! #### Structural correctness of the `iAbove` table -/

private lemma def_iAboveTable {k} (e0 : V) (i : Fin k) :
    𝚺-[1].DefinableFunction (fun v : Fin k → V ↦ iAboveTable e0 (v i)) :=
  DefinableFunction₂.comp (F := iAboveTable) (DefinableFunction.const e0) (DefinableFunction.var i)

@[simp] lemma iAboveTable_seq (e0 n : V) : Seq (iAboveTable e0 n) := by
  induction n using ISigma1.sigma1_succ_induction
  · exact Definable.comp₁ (def_iAboveTable e0 0)
  case zero => simp
  case succ n ih => rw [iAboveTable_succ]; exact ih.seqCons _

@[simp] lemma iAboveTable_lh (e0 n : V) : lh (iAboveTable e0 n) = n + 1 := by
  induction n using ISigma1.sigma1_succ_induction
  · exact Definable.comp₂ (DefinableFunction₁.comp (F := lh) (def_iAboveTable e0 0)) (by definability)
  case zero => simp
  case succ n ih => rw [iAboveTable_succ, Seq.lh_seqCons _ (iAboveTable_seq e0 n), ih]

lemma znth_iAboveTable_succ {e0 n k : V} (hk : k < n + 1) :
    znth (iAboveTable e0 (n + 1)) k = znth (iAboveTable e0 n) k := by
  rw [iAboveTable_succ]
  exact znth_seqCons_of_lt (iAboveTable_seq e0 n) _ (by rw [iAboveTable_lh]; exact hk)

lemma znth_iAboveTable_eq_iAboveb (e0 : V) : ∀ N : V, ∀ k ≤ N, znth (iAboveTable e0 N) k = iAboveb e0 k := by
  intro N
  induction N using ISigma1.sigma1_succ_induction
  · refine Definable.ball_le (by definability) ?_
    exact Definable.comp₂
      (DefinableFunction₂.comp (F := znth) (def_iAboveTable e0 1) (DefinableFunction.var 0))
      (DefinableFunction₂.comp (F := iAboveb) (DefinableFunction.const e0) (DefinableFunction.var 0))
  case zero =>
    intro k hk
    rcases (nonpos_iff_eq_zero.mp hk) with rfl
    rfl
  case succ N ih =>
    intro k hk
    rcases eq_or_lt_of_le hk with rfl | hlt
    · rfl
    · rw [znth_iAboveTable_succ hlt]
      exact ih k (le_iff_lt_succ.mpr hlt)

@[simp] lemma iAboveb_zero (e0 : V) : iAboveb e0 0 = 1 := by
  rw [iAboveb, iAboveTable_zero]
  exact (singleton_seq 1).znth_eq_of_mem ((mem_singleton_seq_iff 1 1).mpr rfl)

@[simp] lemma iAbove_zero (e0 : V) : iAbove e0 0 := by rw [iAbove, iAboveb_zero]

/-- **`iAbove` recursion law**: a positive code dominates iff its head exponent does and its tail does. -/
lemma iAboveb_pos {e0 c : V} (hc : c ≠ 0) :
    iAboveb e0 c = if icmp (ocExp c) e0 = 2 then iAboveb e0 (ocTail c) else 0 := by
  have hpos : 0 < c := pos_iff_ne_zero.mpr hc
  obtain ⟨M, hM⟩ : ∃ M, c = M + 1 :=
    ⟨c - 1, (sub_add_self_of_le (pos_iff_one_le.mp hpos)).symm⟩
  have key : znth (iAboveTable e0 c) c = iAboveNext e0 c (iAboveTable e0 M) := by
    rw [hM, iAboveTable_succ]
    have := znth_seqCons_self (iAboveTable_seq e0 M) (iAboveNext e0 (M + 1) (iAboveTable e0 M))
    rwa [iAboveTable_lh] at this
  have htail : ocTail c ≤ M := le_iff_lt_succ.mpr (hM ▸ ocTail_lt_of_pos hpos)
  rw [iAboveb, key, iAboveNext, znth_iAboveTable_eq_iAboveb e0 M (ocTail c) htail]

/-- `iAbove` of an `ocOadd`: head dominates and tail dominates. -/
lemma iAbove_ocOadd {e0 ec n rc : V} :
    iAbove e0 (ocOadd ec n rc) ↔ icmp ec e0 = 2 ∧ iAbove e0 rc := by
  rw [iAbove, iAboveb_pos (ocOadd_ne_zero ec n rc), ocExp_ocOadd, ocTail_ocOadd]
  by_cases h : icmp ec e0 = 2
  · simp [h, iAbove]
  · simp [h]

/-! ### Clean-append comparison lemmas (the internal `corAlpha_within` core)

With both tails `b₁`, `b₂` clean below `a`'s spine (`iAbove (ocExp bᵢ) a`), the additions `iadd a bᵢ`
share the entire `a`-spine and differ only in the grafted tail. So they compare exactly by their tails:
`icmp (iadd a b₁) (iadd a b₂) = icmp b₁ b₂` — the internal analog of `corAlpha_within` (fixed lead
`ω^(l+1)·βₙ`, the `g`-tail decides). Proved by strong induction peeling `a`'s spine via `iadd_clean_step`
+ `icmp_ocOadd_same_head`. -/

/-- **Within-block clean-append comparison.** Two clean appends onto the *same* head compare by their
tails. (`Grz.corAlpha_within`, internal & general — `g`'s descent transfers through the fixed lead.) -/
lemma icmp_iadd_clean_within {b₁ b₂ : V} (hb₁ : b₁ ≠ 0) (hb₂ : b₂ ≠ 0) :
    ∀ a, iAbove (ocExp b₁) a → iAbove (ocExp b₂) a → icmp (iadd a b₁) (iadd a b₂) = icmp b₁ b₂ := by
  intro a
  induction a using ISigma1.sigma1_order_induction
  · definability
  case ind a IH =>
    intro h₁ h₂
    rcases eq_or_ne a 0 with rfl | ha
    · rw [iadd_zero_left, iadd_zero_left]
    · obtain ⟨ea, na, ra, rfl⟩ : ∃ ea na ra, a = ocOadd ea na ra :=
        ⟨ocExp a, ocCoeff a, ocTail a, (ocOadd_destruct ha).symm⟩
      obtain ⟨hc₁, hr₁⟩ := iAbove_ocOadd.mp h₁
      obtain ⟨hc₂, hr₂⟩ := iAbove_ocOadd.mp h₂
      rw [iadd_clean_step hb₁ hc₁, iadd_clean_step hb₂ hc₂, icmp_ocOadd_same_head]
      have hra_lt : ra < ocOadd ea na ra := by
        have := ocTail_lt ea na ra; rwa [ocTail_ocOadd] at this
      exact IH ra hra_lt hr₁ hr₂

/-- **`iadd` preserves the head exponent under a clean append** (the spine is untouched): if every
spine exponent of `a` dominates `ocExp b` and `a` is positive, `iadd a b` keeps `a`'s leading exponent. -/
lemma ocExp_iadd_clean {a b : V} (hb : b ≠ 0) (ha : a ≠ 0) (habove : iAbove (ocExp b) a) :
    ocExp (iadd a b) = ocExp a := by
  obtain ⟨ea, na, ra, rfl⟩ : ∃ ea na ra, a = ocOadd ea na ra :=
    ⟨ocExp a, ocCoeff a, ocTail a, (ocOadd_destruct ha).symm⟩
  obtain ⟨hc, _⟩ := iAbove_ocOadd.mp habove
  rw [iadd_clean_step hb hc, ocExp_ocOadd, ocExp_ocOadd]

/-! ### The unified clean-append comparison (within + boundary), the internal `corAlpha_*` core

The full `Grz.corAlpha` descent needs *both* the within-block comparison (fixed lead, `g`-tail decides)
and the boundary comparison (lead drops, the `g`-tail `< ω^(l+1)` is absorbed). Both are the single
identity `icmp (iadd a₁ b₁) (iadd a₂ b₂) = thenV (icmp a₁ a₂) (icmp b₁ b₂)` whenever each tail `bᵢ` is
clean below *both* spines `a₁`, `a₂` (`iAbove (ocExp bᵢ) aⱼ` for all four pairs — automatic in Cor 3.4
since every `g < ω^(l+1)` and every `ω^(l+1)·β`-spine exponent `≥ l+1`). The clean appends share the
entire `a`-spines and graft their tails strictly below, so the lexicographic comparison is decided in
the spine exactly as `icmp a₁ a₂` and only falls through to `icmp b₁ b₂` on full spine-equality.

Proved by strong induction on the pair `⟪a₁, a₂⟫`: at a both-positive head the comparison is the
lexicographic combine (`icmp_pos_pos`) of (exponent, coefficient, tail), the tails recurse by the IH,
and `thenV` associates the recursive combine back onto `icmp a₁ a₂` (`thenV_assoc`). The mixed base
cases (one spine ends first) use `icmp_pos_ocOadd_lt_exp` + the `icmp` antisymmetry `icmp_two_iff_swap_zero`
(the grafted tail's leading exponent is dominated by the other still-running spine head). -/
set_option maxHeartbeats 1000000 in
lemma icmp_iadd_clean_aux {b₁ b₂ : V} (hb₁ : b₁ ≠ 0) (hb₂ : b₂ ≠ 0) :
    ∀ p : V, iAbove (ocExp b₁) (π₁ p) → iAbove (ocExp b₁) (π₂ p) →
             iAbove (ocExp b₂) (π₁ p) → iAbove (ocExp b₂) (π₂ p) →
      icmp (iadd (π₁ p) b₁) (iadd (π₂ p) b₂)
        = thenV (icmp (π₁ p) (π₂ p)) (icmp b₁ b₂) := by
  intro p
  induction p using ISigma1.sigma1_order_induction
  · -- definability built by hand: the 4 antecedents (𝚷₁ iAbove-compositions) and the
    -- equation conclusion (𝚺₁) are each shallow; `Definable.imp` chains them.
    refine Definable.imp ?_ (Definable.imp ?_ (Definable.imp ?_ (Definable.imp ?_ ?_)))
    · definability
    · definability
    · definability
    · definability
    · definability
  case ind p IH =>
    intro h11 h12 h21 h22
    have hp : (⟪π₁ p, π₂ p⟫ : V) = p := pair_unpair p
    rcases eq_or_ne (π₁ p) 0 with ha | ha
    · rcases eq_or_ne (π₂ p) 0 with hb | hb
      · -- both spines empty: tails compare directly
        rw [ha, hb, iadd_zero_left, iadd_zero_left, icmp_zero_zero]; simp [thenV]
      · -- left spine empty, right runs: `b₁ ≺ iadd a₂ b₂` (b₁'s exp below the right head)
        obtain ⟨e₂, n₂, r₂, ha2⟩ : ∃ e n r, π₂ p = ocOadd e n r :=
          ⟨_, _, _, (ocOadd_destruct hb).symm⟩
        obtain ⟨hc₂, _⟩ := iAbove_ocOadd.mp (ha2 ▸ h22)
        obtain ⟨hd₂, _⟩ := iAbove_ocOadd.mp (ha2 ▸ h12)
        rw [ha, ha2, iadd_zero_left, iadd_clean_step hb₂ hc₂, icmp_zero_pos (ocOadd_ne_zero _ _ _)]
        rw [icmp_pos_ocOadd_lt_exp hb₁ (icmp_two_iff_swap_zero.mp hd₂)]
        simp [thenV]
    · rcases eq_or_ne (π₂ p) 0 with hb | hb
      · -- right spine empty, left runs: `iadd a₁ b₁ ≻ b₂`
        obtain ⟨e₁, n₁, r₁, ha1⟩ : ∃ e n r, π₁ p = ocOadd e n r :=
          ⟨_, _, _, (ocOadd_destruct ha).symm⟩
        obtain ⟨hc₁, _⟩ := iAbove_ocOadd.mp (ha1 ▸ h11)
        obtain ⟨hd₁, _⟩ := iAbove_ocOadd.mp (ha1 ▸ h21)
        rw [hb, ha1, iadd_zero_left, iadd_clean_step hb₁ hc₁, icmp_pos_zero (ocOadd_ne_zero _ _ _)]
        rw [icmp_two_iff_swap_zero.mpr
          (icmp_pos_ocOadd_lt_exp hb₂ (icmp_two_iff_swap_zero.mp hd₁))]
        simp [thenV]
      · -- both spines run: lockstep peel, tails by IH
        obtain ⟨e₁, n₁, r₁, ha1⟩ : ∃ e n r, π₁ p = ocOadd e n r :=
          ⟨_, _, _, (ocOadd_destruct ha).symm⟩
        obtain ⟨e₂, n₂, r₂, ha2⟩ : ∃ e n r, π₂ p = ocOadd e n r :=
          ⟨_, _, _, (ocOadd_destruct hb).symm⟩
        obtain ⟨hc₁, ht₁₁⟩ := iAbove_ocOadd.mp (ha1 ▸ h11)
        obtain ⟨hc₂, ht₁₂⟩ := iAbove_ocOadd.mp (ha2 ▸ h12)
        obtain ⟨hd₁, ht₂₁⟩ := iAbove_ocOadd.mp (ha1 ▸ h21)
        obtain ⟨hd₂, ht₂₂⟩ := iAbove_ocOadd.mp (ha2 ▸ h22)
        -- IH at the tail pair ⟪r₁, r₂⟫ < p
        have hlt : (⟪r₁, r₂⟫ : V) < p := by
          have h := pair_lt_pair
            (show r₁ < π₁ p by rw [ha1]; have := ocTail_lt e₁ n₁ r₁; rwa [ocTail_ocOadd] at this)
            (show r₂ < π₂ p by rw [ha2]; have := ocTail_lt e₂ n₂ r₂; rwa [ocTail_ocOadd] at this)
          rwa [hp] at h
        have hih := IH _ hlt
        simp only [pi₁_pair, pi₂_pair] at hih
        have hihr := hih ht₁₁ ht₁₂ ht₂₁ ht₂₂
        have e1 : iadd (ocOadd e₁ n₁ r₁) b₁ = ocOadd e₁ n₁ (iadd r₁ b₁) := iadd_clean_step hb₁ hc₁
        have e2 : iadd (ocOadd e₂ n₂ r₂) b₂ = ocOadd e₂ n₂ (iadd r₂ b₂) := iadd_clean_step hb₂ hd₂
        rw [ha1, ha2, e1, e2]
        simp only [icmp_ocOadd, hihr, thenV_assoc]

/-- **Unified clean-append comparison** (`Grz.corAlpha_within` + `corAlpha_boundary`, internal): when
each tail `bᵢ` is clean below both spines, two clean appends compare exactly as their spines, falling
through to the tails only on full spine-equality:
`icmp (iadd a₁ b₁) (iadd a₂ b₂) = thenV (icmp a₁ a₂) (icmp b₁ b₂)`. -/
lemma icmp_iadd_clean (a₁ a₂ : V) {b₁ b₂ : V} (hb₁ : b₁ ≠ 0) (hb₂ : b₂ ≠ 0)
    (h₁₁ : iAbove (ocExp b₁) a₁) (h₁₂ : iAbove (ocExp b₁) a₂)
    (h₂₁ : iAbove (ocExp b₂) a₁) (h₂₂ : iAbove (ocExp b₂) a₂) :
    icmp (iadd a₁ b₁) (iadd a₂ b₂) = thenV (icmp a₁ a₂) (icmp b₁ b₂) := by
  have h := icmp_iadd_clean_aux hb₁ hb₂ ⟪a₁, a₂⟫
  simp only [pi₁_pair, pi₂_pair] at h
  exact h h₁₁ h₁₂ h₂₁ h₂₂

/-- **Boundary clean-append descent** (`Grz.corAlpha_boundary`, internal): if the lead drops
(`a₁ ≺ a₂`) then the clean appends descend (`iadd a₁ b₁ ≺ iadd a₂ b₂`), for any clean tails. -/
lemma icmp_iadd_clean_boundary {a₁ a₂ b₁ b₂ : V} (hb₁ : b₁ ≠ 0) (hb₂ : b₂ ≠ 0)
    (h₁₁ : iAbove (ocExp b₁) a₁) (h₁₂ : iAbove (ocExp b₁) a₂)
    (h₂₁ : iAbove (ocExp b₂) a₁) (h₂₂ : iAbove (ocExp b₂) a₂)
    (hlt : icmp a₁ a₂ = 0) :
    icmp (iadd a₁ b₁) (iadd a₂ b₂) = 0 := by
  rw [icmp_iadd_clean a₁ a₂ hb₁ hb₂ h₁₁ h₁₂ h₂₁ h₂₂, hlt]; simp [thenV]

/-! ### The clean-append C-split (internal `Grz.C_add_clean`)

When the tail `b` is clean below `a`'s spine (`iAbove (ocExp b) a`), `iadd a b` grafts `b` as a
fresh bottom summand — no coefficient merges — so `iC (iadd a b) ≤ max (iC a) (iC b)`. This is the
C-split powering Cor 3.4's slowness bound (`Grz.corAlpha_C_bound`): the lead `ω^(l+1)·βₙ` and the
`g`-tail contribute their `C`s independently. Strong induction on `a` peeling its spine by
`iadd_clean_step`. -/
lemma iC_iadd_clean {b : V} (hb : b ≠ 0) :
    ∀ a, iAbove (ocExp b) a → iC (iadd a b) ≤ max (iC a) (iC b) := by
  intro a
  induction a using ISigma1.sigma1_order_induction
  · definability
  case ind a IH =>
    intro habove
    rcases eq_or_ne a 0 with rfl | ha
    · rw [iadd_zero_left, iC_zero]; simp
    · obtain ⟨ea, na, ra, rfl⟩ : ∃ ea na ra, a = ocOadd ea na ra :=
        ⟨ocExp a, ocCoeff a, ocTail a, (ocOadd_destruct ha).symm⟩
      obtain ⟨hc, hra⟩ := iAbove_ocOadd.mp habove
      have hra_lt : ra < ocOadd ea na ra := by
        have := ocTail_lt ea na ra; rwa [ocTail_ocOadd] at this
      rw [iadd_clean_step hb hc, iC_ocOadd, iC_ocOadd]
      calc max (max (iC ea) na) (iC (iadd ra b))
          ≤ max (max (iC ea) na) (max (iC ra) (iC b)) :=
            max_le_max (le_refl _) (IH ra hra_lt hra)
        _ = max (max (max (iC ea) na) (iC ra)) (iC b) := (max_assoc _ _ _).symm

/-- **Clean-append NF** (the missing sibling of `icmp_iadd_clean`/`iC_iadd_clean`): when the tail `b`
is clean below `a`'s spine (`iAbove (ocExp b) a`), grafting `b` as the bottom summand preserves normal
form — the whole CNF spine of `a` is followed by `b`'s exponents, all strictly decreasing. Strong
induction on `a` peeling its spine via `iadd_clean_step`: the new bottom head-condition is the `iAbove`
head at the spine's end (`icmp_two_iff_swap_zero`), and `a`'s own head-condition transported through
`ocExp_iadd_clean` above it. This certifies `isNF (icorAlpha β g l)` for `InternalThm35.bbeta`. -/
lemma isNF_iadd_clean {b : V} (hb : b ≠ 0) (hbNF : isNF b) :
    ∀ a, isNF a → iAbove (ocExp b) a → isNF (iadd a b) := by
  intro a
  induction a using ISigma1.sigma1_order_induction
  · definability
  case ind a IH =>
    intro haNF habove
    rcases eq_or_ne a 0 with rfl | ha
    · rw [iadd_zero_left]; exact hbNF
    · obtain ⟨ea, na, ra, rfl⟩ : ∃ ea na ra, a = ocOadd ea na ra :=
        ⟨ocExp a, ocCoeff a, ocTail a, (ocOadd_destruct ha).symm⟩
      obtain ⟨hc, hra_above⟩ := iAbove_ocOadd.mp habove
      rw [isNF_ocOadd] at haNF
      obtain ⟨hna, hea_NF, hra_NF, hhead⟩ := haNF
      have hra_lt : ra < ocOadd ea na ra := by
        have := ocTail_lt ea na ra; rwa [ocTail_ocOadd] at this
      rw [iadd_clean_step hb hc, isNF_ocOadd]
      refine ⟨hna, hea_NF, IH ra hra_lt hra_NF hra_above, ?_⟩
      rcases eq_or_ne ra 0 with rfl | hra0
      · -- spine ends: the grafted `b` becomes the new bottom; its exp `≺ ea` by `iAbove`'s head
        rw [iadd_zero_left]
        exact Or.inr (icmp_two_iff_swap_zero.mp hc)
      · -- above the bottom: the original head-condition transports through `ocExp_iadd_clean`
        right
        rw [ocExp_iadd_clean hb hra0 hra_above]
        rcases hhead with h0 | hlt
        · exact absurd h0 hra0
        · exact hlt

/-! ### `iAbove` preservation under `ω·` (internal `Grz.MinExpGe_omega_mul`)

`iomul` bumps every leading exponent `e ↦ 1+e`, and `1+·` is order-faithful (`icmp_one_add`, NF
exponents), so the spine-dominance flag lifts with the threshold bumped the same way:
`iAbove e0 a ⟹ iAbove (1+e0) (ω·a)`. This is the inductive step of the internal `MinExpGe`
chain that certifies the Cor 3.4 lead `ω^(l+1)·β` is clean above any `g < ω^(l+1)`. -/
lemma iAbove_iomul {e0 : V} (he0 : isNF e0) :
    ∀ a, isNF a → iAbove e0 a → iAbove (iadd (ocOadd 0 1 0) e0) (iomul a) := by
  intro a
  induction a using ISigma1.sigma1_order_induction
  · definability
  case ind a IH =>
    intro hNF habove
    rcases eq_or_ne a 0 with rfl | ha
    · rw [iomul_zero]; exact iAbove_zero _
    · obtain ⟨ea, na, ra, rfl⟩ : ∃ ea na ra, a = ocOadd ea na ra :=
        ⟨ocExp a, ocCoeff a, ocTail a, (ocOadd_destruct ha).symm⟩
      obtain ⟨hc, hra_above⟩ := iAbove_ocOadd.mp habove
      rw [isNF_ocOadd] at hNF
      obtain ⟨_, hea_NF, hra_NF, _⟩ := hNF
      have hra_lt : ra < ocOadd ea na ra := by
        have := ocTail_lt ea na ra; rwa [ocTail_ocOadd] at this
      rw [iomul_ocOadd, iAbove_ocOadd]
      refine ⟨?_, IH ra hra_lt hra_NF hra_above⟩
      rw [icmp_one_add hea_NF he0]; exact hc

/-- **Base of the `MinExpGe` chain**: `ω·a` has every leading exponent `≻ 0` (each is `1+e ≠ 0`),
i.e. `iAbove 0 (ω·a)` for any `a ≠ 0`. (Internal `MinExpGe 1 (ω·a)`, no NF needed.) -/
lemma iAbove_zero_iomul : ∀ a : V, a ≠ 0 → iAbove 0 (iomul a) := by
  intro a
  induction a using ISigma1.sigma1_order_induction
  · definability
  case ind a IH =>
    intro ha
    obtain ⟨ea, na, ra, rfl⟩ : ∃ ea na ra, a = ocOadd ea na ra :=
      ⟨ocExp a, ocCoeff a, ocTail a, (ocOadd_destruct ha).symm⟩
    have hra_lt : ra < ocOadd ea na ra := by
      have := ocTail_lt ea na ra; rwa [ocTail_ocOadd] at this
    rw [iomul_ocOadd, iAbove_ocOadd]
    refine ⟨icmp_pos_zero (iadd_one_ne_zero ea), ?_⟩
    rcases eq_or_ne ra 0 with rfl | hra
    · rw [iomul_zero]; exact iAbove_zero 0
    · exact IH ra hra_lt hra

/-- The `MinExpGe` threshold iterate `(1+·)^[k] 0` is NF at every step (`isNF_iadd_one`). -/
lemma isNF_oadd1iter (k : ℕ) : isNF ((iadd (ocOadd 0 1 0))^[k] (0 : V)) := by
  induction k with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ_apply']; exact isNF_iadd_one ih

/-- **`MinExpGe` meta-iterate** (internal `Grz.MinExpGe_bigMul`): `ω^(k+1)·β` has every leading
exponent strictly above the threshold `(1+·)^[k] 0` (= the finite code `k`). Base = `iAbove_zero_iomul`,
step = `iAbove_iomul` (`isNF_ibigMul` supplies the NF arg). -/
lemma iAbove_ibigMul_iter {β : V} (hβNF : isNF β) (hβ0 : β ≠ 0) (k : ℕ) :
    iAbove ((iadd (ocOadd 0 1 0))^[k] (0 : V)) (ibigMul (k + 1) β) := by
  induction k with
  | zero =>
    have h := iAbove_zero_iomul β hβ0
    rw [Function.iterate_zero_apply]
    rwa [ibigMul_succ, ibigMul_zero]
  | succ k ih =>
    rw [Function.iterate_succ_apply', ibigMul_succ]
    exact iAbove_iomul (isNF_oadd1iter k) _ (isNF_ibigMul (k + 1) hβNF) ih

/-- **Cast identity for the `MinExpGe` threshold iterate.** For `k ≥ 1` the iterated `1+·` collapses
to the finite code `ocOadd 0 (k:V) 0`: each `1+·` step bumps a finite head coefficient by one
(`iadd_one_fin`), the base `k=1` is `iadd_one_zero`. Bridges `iAbove_ibigMul_iter`'s threshold
`(1+·)^[k] 0` to the `ocOadd 0 (l:V) 0` finite-code shape that `iAbove_finThresh_mono` consumes. -/
lemma oadd1iter_eq_succ (k : ℕ) :
    (iadd (ocOadd 0 1 0))^[k + 1] (0 : V) = ocOadd 0 ((k : V) + 1) 0 := by
  induction k with
  | zero => simp only [zero_add, Function.iterate_one, iadd_one_zero, Nat.cast_zero]
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih,
        iadd_one_fin (ocOadd_ne_zero 0 ((k : V) + 1) 0) (ocExp_ocOadd 0 ((k : V) + 1) 0),
        ocCoeff_ocOadd, ocTail_ocOadd]
    congr 1
    push_cast
    rw [add_comm 1 ((k : V) + 1)]

/-- **Lead is clean above the finite code `l`** (`Grz.MinExpGe_bigMul` reindexed to a finite code).
The Cor 3.4 lead `ω^(l+1)·β` (here `ibigMul (k+2) β` with `l = k+1`) has every leading exponent
strictly above `ocOadd 0 (l:V) 0`. Combines `iAbove_ibigMul_iter` (threshold `(1+·)^[k+1] 0`) with the
cast identity `oadd1iter_eq_succ`. -/
lemma iAbove_ibigMul_finCode {β : V} (hβNF : isNF β) (hβ0 : β ≠ 0) (k : ℕ) :
    iAbove (ocOadd 0 ((k : V) + 1) 0) (ibigMul (k + 2) β) := by
  have h := iAbove_ibigMul_iter hβNF hβ0 (k + 1)
  rwa [oadd1iter_eq_succ k] at h

/-- **Finite-threshold weakening of `iAbove`** (spine-lifted `icmp_finThresh_mono`): dominance above
the finite code `l` implies dominance above any smaller finite code `j ≤ l`. Used to bring the
`MinExpGe` threshold down to `ocExp g` (a finite code `⪯ l`) when `g < ω^(l+1)`. -/
lemma iAbove_finThresh_mono {l j : V} (hjl : j ≤ l) :
    ∀ a : V, iAbove (ocOadd 0 l 0) a → iAbove (ocOadd 0 j 0) a := by
  intro a
  induction a using ISigma1.sigma1_order_induction
  · definability
  case ind a IH =>
    intro habove
    rcases eq_or_ne a 0 with rfl | ha
    · exact iAbove_zero _
    · obtain ⟨ea, na, ra, rfl⟩ : ∃ ea na ra, a = ocOadd ea na ra :=
        ⟨ocExp a, ocCoeff a, ocTail a, (ocOadd_destruct ha).symm⟩
      obtain ⟨hc, hra⟩ := iAbove_ocOadd.mp habove
      have hra_lt : ra < ocOadd ea na ra := by
        have := ocTail_lt ea na ra; rwa [ocTail_ocOadd] at this
      rw [iAbove_ocOadd]
      exact ⟨icmp_finThresh_mono hc hjl, IH ra hra_lt hra⟩

/-! ### V-indexed MinExpGe (the generic-route lead is clean above its `g`-tail)

The meta-level `iAbove_ibigMul_finCode` only covers a *standard* level. For the generic Cor 3.4 lead
`iVbigMul β (l+1)` at a non-standard `l : V`, the same MinExpGe holds, proved by internal
`sigma1_succ_induction` on `l`. -/

/-- `1 + ω^0·(c+1) = ω^0·(c+2)` on finite codes (the `MinExpGe` threshold bump). -/
lemma iadd_one_finCode (c : V) :
    iadd (ocOadd 0 1 0) (ocOadd 0 (c + 1) 0) = ocOadd 0 (c + 1 + 1) 0 := by
  rw [iadd_one_fin (ocOadd_ne_zero 0 (c + 1) 0) (ocExp_ocOadd 0 (c + 1) 0),
      ocCoeff_ocOadd, ocTail_ocOadd]
  congr 1; rw [add_comm 1 (c + 1)]

/-- **V-indexed `iAbove 0`**: `ω^(l+1)·β` has every leading exponent nonzero (needs only `β ≠ 0`). -/
lemma iAbove_zero_iVbigMul {β : V} (hβ0 : β ≠ 0) (l : V) :
    iAbove 0 (iVbigMul β (l + 1)) := by
  rw [iVbigMul_succ]
  exact iAbove_zero_iomul (iVbigMul β l) (iVbigMul_ne_zero hβ0 l)

/-- **V-indexed MinExpGe** (generic `Grz.MinExpGe_bigMul`, non-standard level): `ω^(l+2)·β` has every
leading exponent strictly above the finite code `l+1`. Internal induction on `l : V`: base `l=0` lifts
`iAbove 0 (ω·β)` through one `ω·` (`iAbove_iomul` + `iadd_one_zero`); step bumps the threshold
`l+1 ↦ l+2` (`iadd_one_finCode`). This certifies the generic Cor 3.4 lead `ω^(l+1)·β` is clean above any
`g < ω^(l+1)` (whose top exponent is a finite code `⪯ l+1`). -/
lemma iAbove_finCode_iVbigMul {β : V} (hβNF : isNF β) (hβ0 : β ≠ 0) :
    ∀ l : V, iAbove (ocOadd 0 (l + 1) 0) (iVbigMul β (l + 1 + 1)) := by
  intro l
  induction l using ISigma1.sigma1_succ_induction
  · refine Definable.comp₂ (P := iAbove)
      (DefinableFunction₃.comp (F := ocOadd) (hF := ocOadd_definable.of_sigmaOne)
        (DefinableFunction.const 0)
        (DefinableFunction₂.comp (F := (· + ·)) (DefinableFunction.var 0) (DefinableFunction.const 1))
        (DefinableFunction.const 0))
      (DefinableFunction₂.comp (F := iVbigMul) (DefinableFunction.const β)
        (DefinableFunction₂.comp (F := (· + ·))
          (DefinableFunction₂.comp (F := (· + ·)) (DefinableFunction.var 0) (DefinableFunction.const 1))
          (DefinableFunction.const 1)))
  case zero =>
    rw [iVbigMul_succ, iVbigMul_succ, iVbigMul_zero, zero_add]
    have h := iAbove_iomul isNF_zero (iomul β) (isNF_iomul hβNF) (iAbove_zero_iomul β hβ0)
    rwa [iadd_one_zero] at h
  case succ l ih =>
    rw [show l + 1 + 1 + 1 = (l + 1 + 1) + 1 from rfl, iVbigMul_succ]
    have hNF : isNF (ocOadd 0 (l + 1) 0) := isNF_finCode (by simp)
    have h := iAbove_iomul hNF (iVbigMul β (l + 1 + 1)) (isNF_iVbigMul hβNF _) ih
    rwa [iadd_one_finCode l] at h

/-- **Cor 3.4 lead is clean above the finite code `l`** (for `l ≥ 1`): reindexed
`iAbove_finCode_iVbigMul`, the generic lead `ω^(l+1)·β` has every leading exponent strictly above
`ocOadd 0 l 0`. -/
lemma iAbove_code_iVbigMul {β : V} (hβNF : isNF β) (hβ0 : β ≠ 0) {l : V} (hl : 0 < l) :
    iAbove (ocOadd 0 l 0) (iVbigMul β (l + 1)) := by
  obtain ⟨p, rfl⟩ : ∃ p, l = p + 1 :=
    ⟨l - 1, (sub_add_self_of_le (pos_iff_one_le.mp hl)).symm⟩
  exact iAbove_finCode_iVbigMul hβNF hβ0 p

/-- **Clean-append discharge, finite `g`-tail.** If `g`'s top exponent is `0` (`g` a finite code `< ω`),
it sits below the lead `ω^(l+1)·β`'s spine for any level. (`Grz.AllExpAbove_bigMul` base.) -/
lemma iAbove_ocExp_iVbigMul_fin {β g : V} (hβ0 : β ≠ 0) (l : V) (hexp : ocExp g = 0) :
    iAbove (ocExp g) (iVbigMul β (l + 1)) := by
  rw [hexp]; exact iAbove_zero_iVbigMul hβ0 l

/-- **Clean-append discharge, infinite `g`-tail.** If `g`'s top exponent is the finite code `j ≤ l`
(`g < ω^(l+1)` with a genuine `ω`-power leading term, forcing `l ≥ 1`), it sits below the lead
`ω^(l+1)·β`'s spine: `iAbove (ocExp g) (ω^(l+1)·β)` by `iAbove_code_iVbigMul` + threshold weakening.
This is the internal `Grz.AllExpAbove_bigMul` (the Cor 3.4 slowness clean-append side condition). -/
lemma iAbove_ocExp_iVbigMul_inf {β g : V} (hβNF : isNF β) (hβ0 : β ≠ 0) {l j : V}
    (hl : 0 < l) (hjl : j ≤ l) (hexp : ocExp g = ocOadd 0 j 0) :
    iAbove (ocExp g) (iVbigMul β (l + 1)) := by
  rw [hexp]
  exact iAbove_finThresh_mono hjl _ (iAbove_code_iVbigMul hβNF hβ0 hl)

/-! ## `icorAlpha` — the Cor 3.4 slowed term (generic level), per-step properties

`αⱼ = ω^(l+1)·β + g` on codes (`Grz.corAlpha`), with the lead built from the V-indexed `iVbigMul`
(so the level `l : V` may be non-standard) and the `g`-tail kept **abstract** (lap-45 path #2): its
NF / value-bound / clean-append / descent facts are HYPOTHESES, to be discharged when the internal
`ig` f-recursion (crux-1 step 3) lands. The three properties below are the portable mathematical
content of Cor 3.4 (mirroring the sorry-free `Grz.corAlpha_within`/`_boundary`/`_C_bound`); the lead is
concrete and the clean-append side conditions are dischargeable via `iAbove_ocExp_iVbigMul_fin/_inf`. -/

/-- The Cor 3.4 slowed within-block term `ω^(l+1)·β + g` on codes (generic level `l : V`). -/
noncomputable def icorAlpha (β g l : V) : V := iadd (iVbigMul β (l + 1)) g

/-- **Within-block descent** (`Grz.corAlpha_within`): fixed lead `ω^(l+1)·β`, the `g`-tail descends
(`icmp g₁ g₂ = 0`) ⟹ the slowed terms descend. Both tails are clean below the lead's spine. -/
lemma icorAlpha_within {β g1 g2 l : V} (hg1 : g1 ≠ 0) (hg2 : g2 ≠ 0)
    (hab1 : iAbove (ocExp g1) (iVbigMul β (l + 1)))
    (hab2 : iAbove (ocExp g2) (iVbigMul β (l + 1)))
    (hdesc : icmp g1 g2 = 0) :
    icmp (icorAlpha β g1 l) (icorAlpha β g2 l) = 0 := by
  rw [icorAlpha, icorAlpha,
      icmp_iadd_clean_within hg1 hg2 (iVbigMul β (l + 1)) hab1 hab2, hdesc]

/-- **Block-boundary descent** (`Grz.corAlpha_boundary`): the lead drops (`β₁ ≺ β₂` ⟹ `ω^(l+1)·β₁ ≺
ω^(l+1)·β₂` by `icmp_iVbigMul`) ⟹ the slowed terms descend, for ANY clean tails. -/
lemma icorAlpha_boundary {β1 β2 g1 g2 l : V} (hβ1NF : isNF β1) (hβ2NF : isNF β2)
    (hg1 : g1 ≠ 0) (hg2 : g2 ≠ 0)
    (hab1_1 : iAbove (ocExp g1) (iVbigMul β1 (l + 1)))
    (hab1_2 : iAbove (ocExp g1) (iVbigMul β2 (l + 1)))
    (hab2_1 : iAbove (ocExp g2) (iVbigMul β1 (l + 1)))
    (hab2_2 : iAbove (ocExp g2) (iVbigMul β2 (l + 1)))
    (hβdesc : icmp β1 β2 = 0) :
    icmp (icorAlpha β1 g1 l) (icorAlpha β2 g2 l) = 0 := by
  rw [icorAlpha, icorAlpha]
  refine icmp_iadd_clean_boundary hg1 hg2 hab1_1 hab1_2 hab2_1 hab2_2 ?_
  rw [icmp_iVbigMul hβ1NF hβ2NF]; exact hβdesc

/-- **Slowness C-bound** (`Grz.corAlpha_C_bound` C-split): the clean append splits `C` between the lead
`ω^(l+1)·β` (`≤ iC β + (l+1)`, `iC_iVbigMul_le`) and the `g`-tail, with no coefficient merge. -/
lemma icorAlpha_C_le {β g l : V} (hg : g ≠ 0)
    (hab : iAbove (ocExp g) (iVbigMul β (l + 1))) :
    iC (icorAlpha β g l) ≤ max (iC β + (l + 1)) (iC g) := by
  rw [icorAlpha]
  exact le_trans (iC_iadd_clean hg _ hab) (max_le_max (iC_iVbigMul_le β (l + 1)) le_rfl)

/-- **NF of the Cor 3.4 slowed term** `ω^(l+1)·β + g`: the lead `ω^(l+1)·β` is NF (`isNF_iVbigMul`)
and the `g`-tail is NF and clean below it (`iAbove`), so the clean append is NF (`isNF_iadd_clean`).
Completes the `icorAlpha` brick set (within / boundary / C-bound / NF) needed to feed the slowed
sequence into `InternalThm35.bbeta` (Thm 3.5). -/
lemma isNF_icorAlpha {β g l : V} (hβNF : isNF β) (hgNF : isNF g) (hg0 : g ≠ 0)
    (hab : iAbove (ocExp g) (iVbigMul β (l + 1))) :
    isNF (icorAlpha β g l) := by
  rw [icorAlpha]
  exact isNF_iadd_clean hg0 hgNF (iVbigMul β (l + 1)) (isNF_iVbigMul hβNF (l + 1)) hab

/-- **Constant-absorption** (`Grz.const_add_le_mul`, internal): `A + j ≤ A·(j+1)` for `A ≥ 1`. Absorbs the
lead's constant `iC β + (l+1)` into the linear Cor 3.4 bound `K·(j+1)`. No `omega` (generic `V`): `j ≤ A·j`
(since `1 ≤ A`) and `A·(j+1) = A·j + A`. -/
lemma iconst_add_le_mul {A j : V} (hA : 1 ≤ A) : A + j ≤ A * (j + 1) := by
  have h1 : j ≤ A * j := by
    calc j = 1 * j := (one_mul j).symm
      _ ≤ A * j := by gcongr
  calc A + j ≤ A + A * j := by gcongr
    _ = A * j + A := by rw [add_comm]
    _ = A * (j + 1) := by rw [mul_add, mul_one]

/-! ### End-to-end validation at the concrete base level `l = 0`

Instantiating the abstract `icorAlpha_*` properties with the concrete level-0 `g`-tail `ig0`
(`Grz.g0`) confirms the interface composes with a real `g` (de-risking before the deep internal `ig`
f-recursion lands). At level 0 the lead is `ω·β`, the tail `ig0 n m` is a finite code (`ocExp = 0`),
so the clean-append condition discharges via `iAbove_ocExp_iVbigMul_fin`. -/

/-- **Level-0 within-block descent, concrete.** `ω·β + ig0 n (m+1) ≺ ω·β + ig0 n m` while `m < n+1`
(the internal `F 0 n`). The whole `icorAlpha` interface, end-to-end on `ig0`. -/
lemma icorAlpha_ig0_within {β : V} (hβ0 : β ≠ 0) {n m : V} (hm : m < n + 1) :
    icmp (icorAlpha β (ig0 n (m + 1)) 0) (icorAlpha β (ig0 n m) 0) = 0 := by
  have hmn2 : m < n + 2 := lt_trans hm (by simp)
  have hm1n2 : m + 1 < n + 2 := by
    have h : m + 1 < (n + 1) + 1 := add_lt_add_of_lt_of_le hm (le_refl 1)
    have e : n + 1 + 1 = n + 2 := by rw [add_assoc, one_add_one_eq_two]
    rwa [e] at h
  exact icorAlpha_within (ig0_ne_zero hm1n2) (ig0_ne_zero hmn2)
    (iAbove_ocExp_iVbigMul_fin hβ0 0 (ocExp_ig0 hm1n2))
    (iAbove_ocExp_iVbigMul_fin hβ0 0 (ocExp_ig0 hmn2))
    (icmp_ig0_desc hm)

end GoodsteinPA.InternalONote
