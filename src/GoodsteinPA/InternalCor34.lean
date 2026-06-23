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

end GoodsteinPA.InternalONote
