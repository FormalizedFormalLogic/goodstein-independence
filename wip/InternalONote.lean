/-
# `InternalONote.lean` — internal ONote (CNF) codes inside `V ⊧ₘ* 𝗜𝚺₁`

The lone remaining wall (`hbound` in `DescentSemantic.no_min_descent_absurd_of_goodstein`) needs
the Rathjen §3 slow-down run inside a model `M`, on an `≺`-descent. The deep content is the
**order-reflection** of the descent (see `ANALYSIS-2026-06-23-lap37-order-reflection-opacity.md`):
to compute the slow-down `βₖ` one must read the **Cantor normal form** of the descent elements
inside `M`. That requires ONote CNF terms presented as `M`-elements with `𝚺₁`-definable structure.

This file lays the foundation: **CNF codes as nested HFS pairs**, the decode projections, and the
**subterm-bound lemmas** (`ocExp/ocCoeff/ocTail` of an `oadd`-code are `<` the code). The bounds are
exactly what a course-of-values recursion over the code value needs (à la `InternalBump.ibumpTable`),
so the next bricks — `isONoteCode`, `iC` (max coefficient), `ievalNat`, the CNF comparison `icmp`
with internal `evalNat_lt_iff` — can recurse on the code. Pure HFS pairing; no `sorry`.

Coding: `0 ↦ (0 : V)`, and `oadd e n r ↦ ⟪⟪ec, n⟫, rc⟫ + 1` (the `+1` tags every non-zero ONote with
a positive code, so `0` is the *unique* code of the ordinal `0`).
-/
import GoodsteinPA.InternalBump
import GoodsteinPA.Compat

namespace GoodsteinPA.InternalONote

open Classical
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.HierarchySymbol
open GoodsteinPA.InternalPow

variable {V : Type*} [ORingStructure V] [V ⊧ₘ* 𝗜𝚺₁]

/-- Code of `oadd e n r` from the subcodes `ec` (exponent), `n` (coefficient), `rc` (tail). -/
noncomputable def ocOadd (ec n rc : V) : V := ⟪⟪ec, n⟫, rc⟫ + 1

/-- The exponent subcode of a code: `π₁ (fstIdx c)` (`fstIdx c = π₁ (c-1) = ⟪ec,n⟫`). -/
noncomputable def ocExp (c : V) : V := π₁ (fstIdx c)

/-- The coefficient of a code: `π₂ (fstIdx c)`. -/
noncomputable def ocCoeff (c : V) : V := π₂ (fstIdx c)

/-- The tail subcode of a code: `sndIdx c = π₂ (c-1) = rc`. -/
noncomputable def ocTail (c : V) : V := sndIdx c

@[simp] lemma ocOadd_pos (ec n rc : V) : 0 < ocOadd ec n rc := by simp [ocOadd]

@[simp] lemma ocOadd_ne_zero (ec n rc : V) : ocOadd ec n rc ≠ 0 :=
  (ocOadd_pos ec n rc).ne'

/-! ### `𝚺₀`-definability of the decode projections -/

def _root_.LO.FirstOrder.Arithmetic.ocExpDef : 𝚺₀.Semisentence 2 := .mkSigma
  “n c. ∃ f <⁺ c, !fstIdxDef f c ∧ !pi₁Def n f”

instance ocExp_defined : 𝚺₀-Function₁ (ocExp : V → V) via ocExpDef := .mk fun v ↦ by
  simp [ocExpDef, ocExp, fstIdx_defined.iff, pi₁_defined.iff]

instance ocExp_definable : 𝚺₀-Function₁ (ocExp : V → V) := ocExp_defined.to_definable
instance ocExp_definable' (Γ) : Γ-Function₁ (ocExp : V → V) := ocExp_definable.of_zero

def _root_.LO.FirstOrder.Arithmetic.ocCoeffDef : 𝚺₀.Semisentence 2 := .mkSigma
  “n c. ∃ f <⁺ c, !fstIdxDef f c ∧ !pi₂Def n f”

instance ocCoeff_defined : 𝚺₀-Function₁ (ocCoeff : V → V) via ocCoeffDef := .mk fun v ↦ by
  simp [ocCoeffDef, ocCoeff, fstIdx_defined.iff, pi₂_defined.iff]

instance ocCoeff_definable : 𝚺₀-Function₁ (ocCoeff : V → V) := ocCoeff_defined.to_definable
instance ocCoeff_definable' (Γ) : Γ-Function₁ (ocCoeff : V → V) := ocCoeff_definable.of_zero

instance ocTail_defined : 𝚺₀-Function₁ (ocTail : V → V) via sndIdxDef := .mk fun v ↦ by
  simp [ocTail, sndIdx_defined.iff]

instance ocTail_definable : 𝚺₀-Function₁ (ocTail : V → V) := ocTail_defined.to_definable
instance ocTail_definable' (Γ) : Γ-Function₁ (ocTail : V → V) := ocTail_definable.of_zero

/-! ### Round-trip: decode recovers the subcodes -/

@[simp] lemma fstIdx_ocOadd (ec n rc : V) : fstIdx (ocOadd ec n rc) = ⟪ec, n⟫ := by
  simp [fstIdx, ocOadd]

@[simp] lemma sndIdx_ocOadd (ec n rc : V) : sndIdx (ocOadd ec n rc) = rc := by
  simp [sndIdx, ocOadd]

@[simp] lemma ocExp_ocOadd (ec n rc : V) : ocExp (ocOadd ec n rc) = ec := by
  simp [ocExp]

@[simp] lemma ocCoeff_ocOadd (ec n rc : V) : ocCoeff (ocOadd ec n rc) = n := by
  simp [ocCoeff]

@[simp] lemma ocTail_ocOadd (ec n rc : V) : ocTail (ocOadd ec n rc) = rc := by
  simp [ocTail]

/-! ### Subterm bounds (course-of-values decrease)

Each subcode of an `oadd`-code is strictly smaller than the code itself: the pairing places the
subterm `≤` the inner pair `≤` the outer pair `< (+1) =` the code. These are the strict-decrease
facts a course-of-values recursion on the code value relies on. -/

lemma ocExp_lt (ec n rc : V) : ocExp (ocOadd ec n rc) < ocOadd ec n rc := by
  rw [ocExp_ocOadd]
  calc ec ≤ ⟪ec, n⟫ := le_pair_left ec n
    _ ≤ ⟪⟪ec, n⟫, rc⟫ := le_pair_left _ rc
    _ < ⟪⟪ec, n⟫, rc⟫ + 1 := by simp
    _ = ocOadd ec n rc := rfl

lemma ocCoeff_lt (ec n rc : V) : ocCoeff (ocOadd ec n rc) < ocOadd ec n rc := by
  rw [ocCoeff_ocOadd]
  calc n ≤ ⟪ec, n⟫ := le_pair_right ec n
    _ ≤ ⟪⟪ec, n⟫, rc⟫ := le_pair_left _ rc
    _ < ⟪⟪ec, n⟫, rc⟫ + 1 := by simp
    _ = ocOadd ec n rc := rfl

lemma ocTail_lt (ec n rc : V) : ocTail (ocOadd ec n rc) < ocOadd ec n rc := by
  rw [ocTail_ocOadd]
  calc rc ≤ ⟪⟪ec, n⟫, rc⟫ := le_pair_right _ rc
    _ < ⟪⟪ec, n⟫, rc⟫ + 1 := by simp
    _ = ocOadd ec n rc := rfl

/-- The exponent subcode of any positive code is `< c` (via `ocExp = π₁ (fstIdx c)` and the pairing
bounds, with `fstIdx c ≤ c - 1 < c`). The form a recursion uses when it only knows `0 < c`. -/
lemma ocExp_lt_of_pos {c : V} (hc : 0 < c) : ocExp c < c := by
  have h1 : ocExp c ≤ fstIdx c := by simp [ocExp]
  have h2 : fstIdx c ≤ c - 1 := by simp [fstIdx]
  have h3 : c - 1 < c := pred_lt_self_of_pos hc
  exact lt_of_le_of_lt (le_trans h1 h2) h3

lemma ocTail_lt_of_pos {c : V} (hc : 0 < c) : ocTail c < c := by
  have h1 : ocTail c ≤ c - 1 := by simp [ocTail, sndIdx]
  exact lt_of_le_of_lt h1 (pred_lt_self_of_pos hc)

/-! ### Internal max-coefficient `iC` via course-of-values recursion

`iC` is Rathjen's `C` (`DescentCore.C`): `C 0 = 0`, `C (oadd e n r) = max (max (C e) n) (C r)`. Inside
`V` it recurses on the code value through the subterm bounds (`ocExp c`, `ocTail c` `< c`), so we
build it by the same table reduction as `ibump`: `iCTable c = ⟨iC 0,…,iC c⟩`, reading the two
sub-results out of the table. -/

/-- Table step of `iC`: `iC c` computed from the table `s = ⟨iC 0,…,iC (c-1)⟩`. The two recursive
sub-results sit at `ocExp c` and `ocTail c` (both `< c`); the coefficient is `ocCoeff c`. -/
noncomputable def iCNext (c s : V) : V :=
  max (max (znth s (ocExp c)) (ocCoeff c)) (znth s (ocTail c))

def _root_.LO.FirstOrder.Arithmetic.iCNextDef : 𝚺₁.Semisentence 3 := .mkSigma
  “y c s.
    ∃ e, !ocExpDef e c ∧ ∃ te, !znthDef te s e ∧ ∃ co, !ocCoeffDef co c ∧
      ∃ t, !sndIdxDef t c ∧ ∃ tt, !znthDef tt s t ∧
        ∃ m1, !max.dfn m1 te co ∧ !max.dfn y m1 tt”

instance iCNext_defined : 𝚺₁-Function₂ (iCNext : V → V → V) via iCNextDef := .mk fun v ↦ by
  simp [iCNextDef, iCNext, ocExp_defined.iff, ocCoeff_defined.iff, ocTail, znth_defined.iff,
    sndIdx_defined.iff, max_defined.iff]

instance iCNext_definable : 𝚺₁-Function₂ (iCNext : V → V → V) := iCNext_defined.to_definable

/-- Blueprint for the `iC` table: `iCTable 0 = ⟨0⟩`, `iCTable (n+1)` appends `iCNext (n+1) (iCTable n)`. -/
def iCTable.blueprint : PR.Blueprint 0 where
  zero := .mkSigma “y. !mkSeq₁Def y 0”
  succ := .mkSigma “y ih n. ∃ v, !iCNextDef v (n + 1) ih ∧ !seqConsDef y ih v”

noncomputable def iCTable.construction : PR.Construction V iCTable.blueprint where
  zero := fun _ ↦ !⟦0⟧
  succ := fun _ n ih ↦ seqCons ih (iCNext (n + 1) ih)
  zero_defined := .mk fun v ↦ by
    simp [iCTable.blueprint, mkSeq₁Def, seqCons_defined.iff, emptyset_def]
  succ_defined := .mk fun v ↦ by
    simp [iCTable.blueprint, iCNext_defined.iff, seqCons_defined.iff]

/-- **The `iC` table** inside `V`: `iCTable n = ⟨iC 0,…,iC n⟩` (length `n+1`). -/
noncomputable def iCTable (n : V) : V := iCTable.construction.result ![] n

@[simp] lemma iCTable_zero : iCTable (0 : V) = !⟦0⟧ := by
  simp [iCTable, iCTable.construction]

@[simp] lemma iCTable_succ (n : V) :
    iCTable (n + 1) = seqCons (iCTable n) (iCNext (n + 1) (iCTable n)) := by
  simp [iCTable, iCTable.construction]

/-- **Internal max-coefficient** `C` of a code: the `c`-th entry of the table. -/
noncomputable def iC (c : V) : V := znth (iCTable c) c

def _root_.LO.FirstOrder.Arithmetic.iCTableDef : 𝚺₁.Semisentence 2 :=
  iCTable.blueprint.resultDef.rew (Rew.subst ![#0, #1])

instance iCTable_defined : 𝚺₁-Function₁ (iCTable : V → V) via iCTableDef := .mk
  fun v ↦ by simp [iCTable.construction.result_defined_iff, iCTableDef]; rfl

instance iCTable_definable : 𝚺₁-Function₁ (iCTable : V → V) := iCTable_defined.to_definable
instance iCTable_definable' (Γ) : Γ-[m + 1]-Function₁ (iCTable : V → V) :=
  iCTable_definable.of_sigmaOne

def _root_.LO.FirstOrder.Arithmetic.iCDef : 𝚺₁.Semisentence 2 := .mkSigma
  “y c. ∃ t, !iCTableDef t c ∧ !znthDef y t c”

instance iC_defined : 𝚺₁-Function₁ (iC : V → V) via iCDef := .mk fun v ↦ by
  simp [iCDef, iC, iCTable_defined.iff, znth_defined.iff]

instance iC_definable : 𝚺₁-Function₁ (iC : V → V) := iC_defined.to_definable
instance iC_definable' (Γ) : Γ-[m + 1]-Function₁ (iC : V → V) := iC_definable.of_sigmaOne

/-! ### Structural correctness of the `iC` table -/

private lemma def_iCTable {k} (i : Fin k) :
    𝚺-[1].DefinableFunction (fun v : Fin k → V ↦ iCTable (v i)) :=
  DefinableFunction₁.comp (F := iCTable) (DefinableFunction.var i)

private lemma def_iC {k} (i : Fin k) :
    𝚺-[1].DefinableFunction (fun v : Fin k → V ↦ iC (v i)) :=
  DefinableFunction₁.comp (F := iC) (DefinableFunction.var i)

@[simp] lemma iCTable_seq (n : V) : Seq (iCTable n) := by
  induction n using ISigma1.sigma1_succ_induction
  · exact Definable.comp₁ (def_iCTable 0)
  case zero => simp
  case succ n ih => rw [iCTable_succ]; exact ih.seqCons _

@[simp] lemma iCTable_lh (n : V) : lh (iCTable n) = n + 1 := by
  induction n using ISigma1.sigma1_succ_induction
  · exact Definable.comp₂ (DefinableFunction₁.comp (F := lh) (def_iCTable 0)) (by definability)
  case zero => simp
  case succ n ih => rw [iCTable_succ, Seq.lh_seqCons _ (iCTable_seq n), ih]

lemma znth_seqCons_of_lt {s : V} (h : Seq s) (x : V) {i} (hi : i < lh s) :
    znth (seqCons s x) i = znth s i :=
  (h.seqCons x).znth_eq_of_mem (Seq.subset_seqCons s x (h.znth hi))

lemma znth_iCTable_succ {n k : V} (hk : k < n + 1) :
    znth (iCTable (n + 1)) k = znth (iCTable n) k := by
  rw [iCTable_succ]
  exact znth_seqCons_of_lt (iCTable_seq n) _ (by rw [iCTable_lh]; exact hk)

lemma znth_seqCons_self {s : V} (h : Seq s) (x : V) : znth (seqCons s x) (lh s) = x :=
  (h.seqCons x).znth_eq_of_mem (lh_mem_seqCons s x)

/-- **Table stability.** Every entry of the length-`(N+1)` table is the genuine `iC` value. -/
lemma znth_iCTable_eq_iC : ∀ N : V, ∀ k ≤ N, znth (iCTable N) k = iC k := by
  intro N
  induction N using ISigma1.sigma1_succ_induction
  · refine Definable.ball_le (by definability) ?_
    exact Definable.comp₂
      (DefinableFunction₂.comp (F := znth) (def_iCTable 1) (DefinableFunction.var 0))
      (def_iC 0)
  case zero =>
    intro k hk
    rcases (nonpos_iff_eq_zero.mp hk) with rfl
    rfl
  case succ N ih =>
    intro k hk
    rcases eq_or_lt_of_le hk with rfl | hlt
    · rfl
    · rw [znth_iCTable_succ hlt]
      exact ih k (le_iff_lt_succ.mpr hlt)

@[simp] lemma iC_zero : iC (0 : V) = 0 := by
  simp only [iC, iCTable_zero]
  exact (singleton_seq 0).znth_eq_of_mem ((mem_singleton_seq_iff 0 0).mpr rfl)

/-- **The internal `C` recursion**: `iC (oadd e n r) = max (max (iC e) n) (iC r)` (Rathjen's
`C_oadd`), realized on codes inside `V`. The two sub-results are read out of the table at
`ocExp`/`ocTail`, which the subterm bounds place `< c`. -/
lemma iC_ocOadd (ec n rc : V) :
    iC (ocOadd ec n rc) = max (max (iC ec) n) (iC rc) := by
  set c := ocOadd ec n rc with hc
  have hpos : 0 < c := ocOadd_pos ec n rc
  obtain ⟨M, hM⟩ : ∃ M, c = M + 1 :=
    ⟨c - 1, (sub_add_self_of_le (pos_iff_one_le.mp hpos)).symm⟩
  have key : znth (iCTable c) c = iCNext c (iCTable M) := by
    rw [hM, iCTable_succ]
    have := znth_seqCons_self (iCTable_seq M) (iCNext (M + 1) (iCTable M))
    rwa [iCTable_lh] at this
  have hexp : ocExp c ≤ M := by
    have := ocExp_lt ec n rc; rw [← hc] at this; exact le_iff_lt_succ.mpr (hM ▸ this)
  have htail : ocTail c ≤ M := by
    have := ocTail_lt ec n rc; rw [← hc] at this; exact le_iff_lt_succ.mpr (hM ▸ this)
  rw [iC, key, iCNext,
    znth_iCTable_eq_iC M (ocExp c) hexp, znth_iCTable_eq_iC M (ocTail c) htail,
    ocExp_ocOadd, ocCoeff_ocOadd, ocTail_ocOadd]

/-! ### Internal evaluation `ievalNat` (Rathjen's `T̂^b_ω`) via course-of-values recursion

`ievalNat b c` is `Domination.evalNat b` on the code `c`: `evalNat b 0 = 0`,
`evalNat b (oadd e n r) = n * (b+1)^(evalNat b e) + evalNat b r`. Same table reduction as `iC`/`ibump`,
parameterized by the base `b`. The sub-results at `ocExp`/`ocTail` come out of the table. This is the
`T̂` the descent's order-reflection runs on; on standard inputs it matches `evalNat`, and its base-bump
is `ibump` (`evalNat_succ_base`). -/

/-- Table step of `ievalNat`: `n * (b+1)^(table@ocExp) + table@ocTail`. -/
noncomputable def ievalNext (b c s : V) : V :=
  ocCoeff c * ipow (b + 1) (znth s (ocExp c)) + znth s (ocTail c)

def _root_.LO.FirstOrder.Arithmetic.ievalNextDef : 𝚺₁.Semisentence 4 := .mkSigma
  “y b c s.
    ∃ co, !ocCoeffDef co c ∧ ∃ e, !ocExpDef e c ∧ ∃ te, !znthDef te s e ∧
      ∃ pe, !ipowDef pe (b + 1) te ∧ ∃ t, !sndIdxDef t c ∧ ∃ tt, !znthDef tt s t ∧
        y = co * pe + tt”

instance ievalNext_defined : 𝚺₁-Function₃ (ievalNext : V → V → V → V) via ievalNextDef := .mk
  fun v ↦ by
    simp [ievalNextDef, ievalNext, ocCoeff_defined.iff, ocExp_defined.iff, ocTail, znth_defined.iff,
      ipow_defined.iff, sndIdx_defined.iff]

instance ievalNext_definable : 𝚺₁-Function₃ (ievalNext : V → V → V → V) :=
  ievalNext_defined.to_definable

/-- Blueprint for the `ievalNat` table (parameter = base `b`). -/
def ievalTable.blueprint : PR.Blueprint 1 where
  zero := .mkSigma “y x. !mkSeq₁Def y 0”
  succ := .mkSigma “y ih n x. ∃ v, !ievalNextDef v x (n + 1) ih ∧ !seqConsDef y ih v”

noncomputable def ievalTable.construction : PR.Construction V ievalTable.blueprint where
  zero := fun _ ↦ !⟦0⟧
  succ := fun x n ih ↦ seqCons ih (ievalNext (x 0) (n + 1) ih)
  zero_defined := .mk fun v ↦ by
    simp [ievalTable.blueprint, mkSeq₁Def, seqCons_defined.iff, emptyset_def]
  succ_defined := .mk fun v ↦ by
    simp [ievalTable.blueprint, ievalNext_defined.iff, seqCons_defined.iff]

/-- **The `ievalNat` table**: `ievalTable b n = ⟨ievalNat b 0,…,ievalNat b n⟩`. -/
noncomputable def ievalTable (b n : V) : V := ievalTable.construction.result ![b] n

@[simp] lemma ievalTable_zero (b : V) : ievalTable b 0 = !⟦0⟧ := by
  simp [ievalTable, ievalTable.construction]

@[simp] lemma ievalTable_succ (b n : V) :
    ievalTable b (n + 1) = seqCons (ievalTable b n) (ievalNext b (n + 1) (ievalTable b n)) := by
  simp [ievalTable, ievalTable.construction]

/-- **Internal evaluation** `T̂^b_ω(code)` inside `V`: the `c`-th entry of the table. -/
noncomputable def ievalNat (b c : V) : V := znth (ievalTable b c) c

def _root_.LO.FirstOrder.Arithmetic.ievalTableDef : 𝚺₁.Semisentence 3 :=
  ievalTable.blueprint.resultDef.rew (Rew.subst ![#0, #2, #1])

instance ievalTable_defined : 𝚺₁-Function₂ (ievalTable : V → V → V) via ievalTableDef := .mk
  fun v ↦ by simp [ievalTable.construction.result_defined_iff, ievalTableDef]; rfl

instance ievalTable_definable : 𝚺₁-Function₂ (ievalTable : V → V → V) := ievalTable_defined.to_definable
instance ievalTable_definable' (Γ) : Γ-[m + 1]-Function₂ (ievalTable : V → V → V) :=
  ievalTable_definable.of_sigmaOne

def _root_.LO.FirstOrder.Arithmetic.ievalNatDef : 𝚺₁.Semisentence 3 := .mkSigma
  “y b c. ∃ t, !ievalTableDef t b c ∧ !znthDef y t c”

instance ievalNat_defined : 𝚺₁-Function₂ (ievalNat : V → V → V) via ievalNatDef := .mk fun v ↦ by
  simp [ievalNatDef, ievalNat, ievalTable_defined.iff, znth_defined.iff]

instance ievalNat_definable : 𝚺₁-Function₂ (ievalNat : V → V → V) := ievalNat_defined.to_definable
instance ievalNat_definable' (Γ) : Γ-[m + 1]-Function₂ (ievalNat : V → V → V) :=
  ievalNat_definable.of_sigmaOne

/-! ### Structural correctness of `ievalNat` -/

private lemma def_ievalTable {k} (b : V) (i : Fin k) :
    𝚺-[1].DefinableFunction (fun v : Fin k → V ↦ ievalTable b (v i)) :=
  DefinableFunction₂.comp (F := ievalTable) (DefinableFunction.const b) (DefinableFunction.var i)

private lemma def_ievalNat {k} (b : V) (i : Fin k) :
    𝚺-[1].DefinableFunction (fun v : Fin k → V ↦ ievalNat b (v i)) :=
  DefinableFunction₂.comp (F := ievalNat) (DefinableFunction.const b) (DefinableFunction.var i)

@[simp] lemma ievalTable_seq (b n : V) : Seq (ievalTable b n) := by
  induction n using ISigma1.sigma1_succ_induction
  · exact Definable.comp₁ (def_ievalTable b 0)
  case zero => simp
  case succ n ih => rw [ievalTable_succ]; exact ih.seqCons _

@[simp] lemma ievalTable_lh (b n : V) : lh (ievalTable b n) = n + 1 := by
  induction n using ISigma1.sigma1_succ_induction
  · exact Definable.comp₂ (DefinableFunction₁.comp (F := lh) (def_ievalTable b 0)) (by definability)
  case zero => simp
  case succ n ih => rw [ievalTable_succ, Seq.lh_seqCons _ (ievalTable_seq b n), ih]

lemma znth_ievalTable_succ {b n k : V} (hk : k < n + 1) :
    znth (ievalTable b (n + 1)) k = znth (ievalTable b n) k := by
  rw [ievalTable_succ]
  exact znth_seqCons_of_lt (ievalTable_seq b n) _ (by rw [ievalTable_lh]; exact hk)

lemma znth_ievalTable_eq_ievalNat (b : V) : ∀ N : V, ∀ k ≤ N, znth (ievalTable b N) k = ievalNat b k := by
  intro N
  induction N using ISigma1.sigma1_succ_induction
  · refine Definable.ball_le (by definability) ?_
    exact Definable.comp₂
      (DefinableFunction₂.comp (F := znth) (def_ievalTable b 1) (DefinableFunction.var 0))
      (def_ievalNat b 0)
  case zero =>
    intro k hk
    rcases (nonpos_iff_eq_zero.mp hk) with rfl
    rfl
  case succ N ih =>
    intro k hk
    rcases eq_or_lt_of_le hk with rfl | hlt
    · rfl
    · rw [znth_ievalTable_succ hlt]
      exact ih k (le_iff_lt_succ.mpr hlt)

@[simp] lemma ievalNat_zero (b : V) : ievalNat b 0 = 0 := by
  simp only [ievalNat, ievalTable_zero]
  exact (singleton_seq 0).znth_eq_of_mem ((mem_singleton_seq_iff 0 0).mpr rfl)

/-- **The internal `evalNat` recursion**: `ievalNat b (oadd e n r) = n * (b+1)^(ievalNat b e) +
ievalNat b r` (Rathjen's `T̂`/`evalNat_oadd`), on codes inside `V`. -/
lemma ievalNat_ocOadd (b ec n rc : V) :
    ievalNat b (ocOadd ec n rc) = n * ipow (b + 1) (ievalNat b ec) + ievalNat b rc := by
  set c := ocOadd ec n rc with hc
  have hpos : 0 < c := ocOadd_pos ec n rc
  obtain ⟨M, hM⟩ : ∃ M, c = M + 1 :=
    ⟨c - 1, (sub_add_self_of_le (pos_iff_one_le.mp hpos)).symm⟩
  have key : znth (ievalTable b c) c = ievalNext b c (ievalTable b M) := by
    rw [hM, ievalTable_succ]
    have := znth_seqCons_self (ievalTable_seq b M) (ievalNext b (M + 1) (ievalTable b M))
    rwa [ievalTable_lh] at this
  have hexp : ocExp c ≤ M := by
    have := ocExp_lt ec n rc; rw [← hc] at this; exact le_iff_lt_succ.mpr (hM ▸ this)
  have htail : ocTail c ≤ M := by
    have := ocTail_lt ec n rc; rw [← hc] at this; exact le_iff_lt_succ.mpr (hM ▸ this)
  rw [ievalNat, key, ievalNext,
    znth_ievalTable_eq_ievalNat b M (ocExp c) hexp, znth_ievalTable_eq_ievalNat b M (ocTail c) htail,
    ocExp_ocOadd, ocCoeff_ocOadd, ocTail_ocOadd]

/-! ### Internal `Canon` (`C ≤ b`) — free from `iC`

Rathjen's `Canon b o` ("every coefficient `≤ b`") is `C o ≤ b` (`DescentCore.Canon_iff_C_le`), so the
internal `Canon` predicate is just `iC c ≤ b` — no separate recursion needed. Its `oadd` law is the
`iC_ocOadd` recursion read through `max ≤`. `iCanon` is `𝚺₁` (in fact `𝚫₁`) via `iC_defined`. -/

/-- Internal `Canon b c`: every coefficient of the code `c` is `≤ b`, i.e. `iC c ≤ b`. -/
def iCanon (b c : V) : Prop := iC c ≤ b

lemma iCanon_def (b c : V) : iCanon b c ↔ iC c ≤ b := Iff.rfl

@[simp] lemma iCanon_zero (b : V) : iCanon b 0 := by simp [iCanon]

/-- **Internal `Canon_oadd`**: `Canon b (oadd e n r) ↔ n ≤ b ∧ Canon b e ∧ Canon b r`. -/
lemma iCanon_ocOadd (b ec n rc : V) :
    iCanon b (ocOadd ec n rc) ↔ n ≤ b ∧ iCanon b ec ∧ iCanon b rc := by
  simp only [iCanon, iC_ocOadd, max_le_iff]
  tauto

instance iCanon_definable (Γ) : Γ-[m + 1]-Relation (iCanon : V → V → Prop) := by
  unfold iCanon; definability


/-! ## Internal CNF comparison `icmp` (ordering codes lt=0, eq=1, gt=2)

The lexicographic comparison `ONote.cmp` (mirroring `ONoteComp.cmpStep`), internalized on codes via a
course-of-values table indexed by the pair `⟪c1,c2⟫` (sub-comparisons sit at `⟪ocExp c1, ocExp c2⟫`
and `⟪ocTail c1, ocTail c2⟫`, both `< ⟪c1,c2⟫` by pairing monotonicity). The order-reflection
`ievalNat b o < ievalNat b p ↔ icmp o p = 0` on the `iCanon b`/`isNF` domain (next lap) is what the
descent's slow-down consumes. -/

/-- `Ordering.then` on ordering codes (lt=0, eq=1, gt=2): take `a` unless `a = eq`. -/
noncomputable def thenV (a b : V) : V := if a = 1 then b else a

def _root_.LO.FirstOrder.Arithmetic.thenVDef : 𝚺₀.Semisentence 3 := .mkSigma
  “y a b. (a = 1 ∧ y = b) ∨ (a ≠ 1 ∧ y = a)”

instance thenV_defined : 𝚺₀-Function₂ (thenV : V → V → V) via thenVDef := .mk fun v ↦ by
  simp [thenVDef, thenV]
  by_cases h : v 1 = 1 <;> simp [h]

instance thenV_definable : 𝚺₀-Function₂ (thenV : V → V → V) := thenV_defined.to_definable
instance thenV_definable' (Γ) : Γ-Function₂ (thenV : V → V → V) := thenV_definable.of_zero

/-- `cmp` on ordering codes: 0 if `a<b`, 1 if `a=b`, 2 otherwise. -/
noncomputable def cmpV (a b : V) : V := if a < b then 0 else if a = b then 1 else 2

def _root_.LO.FirstOrder.Arithmetic.cmpVDef : 𝚺₀.Semisentence 3 := .mkSigma
  “y a b. (a < b ∧ y = 0) ∨ (a ≥ b ∧ a = b ∧ y = 1) ∨ (a ≥ b ∧ a ≠ b ∧ y = 2)”

instance cmpV_defined : 𝚺₀-Function₂ (cmpV : V → V → V) via cmpVDef := .mk fun v ↦ by
  simp [cmpVDef, cmpV]
  rcases lt_trichotomy (v 1) (v 2) with h | h | h
  · simp [h]
  · simp [h]
  · simp [not_lt.mpr (le_of_lt h), le_of_lt h, (ne_of_lt h).symm]

instance cmpV_definable : 𝚺₀-Function₂ (cmpV : V → V → V) := cmpV_defined.to_definable
instance cmpV_definable' (Γ) : Γ-Function₂ (cmpV : V → V → V) := cmpV_definable.of_zero

/-- Order-code involution swapping `0`↔`2` (lt↔gt), fixing `1` (eq). `icmp` is antisymmetric
through it: `icmp c2 c1 = oswap (icmp c1 c2)` (`icmp_swap`). -/
noncomputable def oswap (x : V) : V := if x = 0 then 2 else if x = 2 then 0 else x

def _root_.LO.FirstOrder.Arithmetic.oswapDef : 𝚺₀.Semisentence 2 := .mkSigma
  “y x. (x = 0 ∧ y = 2) ∨ (x ≠ 0 ∧ x = 2 ∧ y = 0) ∨ (x ≠ 0 ∧ x ≠ 2 ∧ y = x)”

instance oswap_defined : 𝚺₀-Function₁ (oswap : V → V) via oswapDef := .mk fun v ↦ by
  simp [oswapDef, oswap]
  by_cases h0 : v 1 = 0 <;> by_cases h2 : v 1 = 2 <;> simp [h0, h2]

instance oswap_definable : 𝚺₀-Function₁ (oswap : V → V) := oswap_defined.to_definable

@[simp] lemma oswap_zero : oswap (0 : V) = 2 := by simp [oswap]
@[simp] lemma oswap_two : oswap (2 : V) = 0 := by simp [oswap]
@[simp] lemma oswap_one : oswap (1 : V) = 1 := by simp [oswap]

lemma oswap_eq_one {x : V} : oswap x = 1 ↔ x = 1 := by
  rcases eq_or_ne x 1 with rfl | h
  · simp
  · constructor
    · intro hx; simp only [oswap] at hx
      by_cases h0 : x = 0 <;> by_cases h2 : x = 2 <;> simp_all
    · intro hx; exact absurd hx h

/-- `oswap` is a `thenV`-homomorphism (lexicographic-combine commutes with the swap). -/
lemma oswap_thenV (a b : V) : oswap (thenV a b) = thenV (oswap a) (oswap b) := by
  unfold thenV
  by_cases ha : a = 1
  · simp [ha]
  · rw [if_neg ha, if_neg (by rw [oswap_eq_one]; exact ha)]

@[simp] lemma thenV_one_left (x : V) : thenV 1 x = x := by simp [thenV]
@[simp] lemma thenV_zero_left (x : V) : thenV 0 x = 0 := by
  rw [thenV, if_neg (zero_ne_one)]

/-- `thenV` is associative (lexicographic combine). -/
lemma thenV_assoc (a b c : V) : thenV (thenV a b) c = thenV a (thenV b c) := by
  unfold thenV
  by_cases ha : a = 1 <;> simp [ha]

/-- `cmpV` is antisymmetric through `oswap`. -/
lemma cmpV_swap (a b : V) : cmpV b a = oswap (cmpV a b) := by
  rcases lt_trichotomy a b with h | h | h
  · have e1 : cmpV a b = 0 := by rw [cmpV, if_pos h]
    have e2 : cmpV b a = 2 := by rw [cmpV, if_neg (not_lt.mpr h.le), if_neg h.ne']
    rw [e1, e2]; simp
  · subst h
    have e1 : cmpV a a = 1 := by rw [cmpV, if_neg (_root_.lt_irrefl a), if_pos rfl]
    rw [e1]; simp
  · have e1 : cmpV a b = 2 := by rw [cmpV, if_neg (not_lt.mpr h.le), if_neg h.ne']
    have e2 : cmpV b a = 0 := by rw [cmpV, if_pos h]
    rw [e1, e2]; simp

/-- The "both-positive" branch of the comparison step on the pair index `i = ⟪c1,c2⟫` with table `s`:
lexicographic `then`-combine of the exponent comparison (read at `⟪ocExp c1, ocExp c2⟫`), the leading
coefficient comparison (`cmpV`), and the tail comparison (read at `⟪ocTail c1, ocTail c2⟫`). -/
noncomputable def icmpMain (i s : V) : V :=
  thenV (znth s ⟪ocExp (π₁ i), ocExp (π₂ i)⟫)
    (thenV (cmpV (ocCoeff (π₁ i)) (ocCoeff (π₂ i)))
      (znth s ⟪ocTail (π₁ i), ocTail (π₂ i)⟫))

def _root_.LO.FirstOrder.Arithmetic.icmpMainDef : 𝚺₁.Semisentence 3 := .mkSigma
  “y i s.
    ∃ c1, !pi₁Def c1 i ∧ ∃ c2, !pi₂Def c2 i ∧
      ∃ e1, !ocExpDef e1 c1 ∧ ∃ e2, !ocExpDef e2 c2 ∧ ∃ ie, !pairDef ie e1 e2 ∧
        ∃ re, !znthDef re s ie ∧
      ∃ co1, !ocCoeffDef co1 c1 ∧ ∃ co2, !ocCoeffDef co2 c2 ∧ ∃ cn, !cmpVDef cn co1 co2 ∧
      ∃ t1, !sndIdxDef t1 c1 ∧ ∃ t2, !sndIdxDef t2 c2 ∧ ∃ ia, !pairDef ia t1 t2 ∧
        ∃ ra, !znthDef ra s ia ∧
      ∃ inner, !thenVDef inner cn ra ∧ !thenVDef y re inner”

instance icmpMain_defined : 𝚺₁-Function₂ (icmpMain : V → V → V) via icmpMainDef := .mk fun v ↦ by
  simp [icmpMainDef, icmpMain, pi₁_defined.iff, pi₂_defined.iff, ocExp_defined.iff,
    ocCoeff_defined.iff, ocTail, sndIdx_defined.iff, pair_defined.iff, znth_defined.iff,
    cmpV_defined.iff, thenV_defined.iff]

instance icmpMain_definable : 𝚺₁-Function₂ (icmpMain : V → V → V) := icmpMain_defined.to_definable

/-- Table step of `icmp` on the pair index `i = ⟪c1,c2⟫`: handle the zero base cases (eq=1, lt=0,
gt=2), else the lexicographic `icmpMain`. -/
noncomputable def icmpNext (i s : V) : V :=
  if π₁ i = 0 then (if π₂ i = 0 then 1 else 0)
  else if π₂ i = 0 then 2
  else icmpMain i s

def _root_.LO.FirstOrder.Arithmetic.icmpNextDef : 𝚺₁.Semisentence 3 := .mkSigma
  “y i s.
    ∃ c1, !pi₁Def c1 i ∧ ∃ c2, !pi₂Def c2 i ∧
      ( (c1 = 0 ∧ c2 = 0 ∧ y = 1)
      ∨ (c1 = 0 ∧ c2 ≠ 0 ∧ y = 0)
      ∨ (c1 ≠ 0 ∧ c2 = 0 ∧ y = 2)
      ∨ (c1 ≠ 0 ∧ c2 ≠ 0 ∧ !icmpMainDef y i s) )”

instance icmpNext_defined : 𝚺₁-Function₂ (icmpNext : V → V → V) via icmpNextDef := .mk fun v ↦ by
  simp [icmpNextDef, icmpNext, pi₁_defined.iff, pi₂_defined.iff, icmpMain_defined.iff]
  by_cases h1 : π₁ (v 1) = 0 <;> by_cases h2 : π₂ (v 1) = 0 <;> simp [h1, h2]

instance icmpNext_definable : 𝚺₁-Function₂ (icmpNext : V → V → V) := icmpNext_defined.to_definable

/-! ### The `icmp` table -/

/-- Blueprint for the `icmp` table: position `j` holds `icmpNext j (table @ 0..j-1)`. -/
def icmpTable.blueprint : PR.Blueprint 0 where
  zero := .mkSigma “y. !mkSeq₁Def y 1”
  succ := .mkSigma “y ih n. ∃ v, !icmpNextDef v (n + 1) ih ∧ !seqConsDef y ih v”

noncomputable def icmpTable.construction : PR.Construction V icmpTable.blueprint where
  zero := fun _ ↦ !⟦1⟧
  succ := fun _ n ih ↦ seqCons ih (icmpNext (n + 1) ih)
  zero_defined := .mk fun v ↦ by
    simp [icmpTable.blueprint, mkSeq₁Def, seqCons_defined.iff, emptyset_def]
  succ_defined := .mk fun v ↦ by
    simp [icmpTable.blueprint, icmpNext_defined.iff, seqCons_defined.iff]

noncomputable def icmpTable (n : V) : V := icmpTable.construction.result ![] n

@[simp] lemma icmpTable_zero : icmpTable (0 : V) = !⟦1⟧ := by
  simp [icmpTable, icmpTable.construction]

@[simp] lemma icmpTable_succ (n : V) :
    icmpTable (n + 1) = seqCons (icmpTable n) (icmpNext (n + 1) (icmpTable n)) := by
  simp [icmpTable, icmpTable.construction]

/-- **Internal CNF comparison.** `icmp c1 c2` = ordering code (lt=0, eq=1, gt=2) of the CNF codes
`c1`, `c2`, read out of the table at the pair index `⟪c1,c2⟫`. -/
noncomputable def icmp (c1 c2 : V) : V := znth (icmpTable ⟪c1, c2⟫) ⟪c1, c2⟫

def _root_.LO.FirstOrder.Arithmetic.icmpTableDef : 𝚺₁.Semisentence 2 :=
  icmpTable.blueprint.resultDef.rew (Rew.subst ![#0, #1])

instance icmpTable_defined : 𝚺₁-Function₁ (icmpTable : V → V) via icmpTableDef := .mk
  fun v ↦ by simp [icmpTable.construction.result_defined_iff, icmpTableDef]; rfl

instance icmpTable_definable : 𝚺₁-Function₁ (icmpTable : V → V) := icmpTable_defined.to_definable
instance icmpTable_definable' (Γ) : Γ-[m + 1]-Function₁ (icmpTable : V → V) :=
  icmpTable_definable.of_sigmaOne

def _root_.LO.FirstOrder.Arithmetic.icmpDef : 𝚺₁.Semisentence 3 := .mkSigma
  “y c1 c2. ∃ i, !pairDef i c1 c2 ∧ ∃ t, !icmpTableDef t i ∧ !znthDef y t i”

instance icmp_defined : 𝚺₁-Function₂ (icmp : V → V → V) via icmpDef := .mk fun v ↦ by
  simp [icmpDef, icmp, pair_defined.iff, icmpTable_defined.iff, znth_defined.iff]

instance icmp_definable : 𝚺₁-Function₂ (icmp : V → V → V) := icmp_defined.to_definable
instance icmp_definable' (Γ) : Γ-[m + 1]-Function₂ (icmp : V → V → V) := icmp_definable.of_sigmaOne

/-! ### Structural correctness of the `icmp` table -/

private lemma def_icmpTable {k} (i : Fin k) :
    𝚺-[1].DefinableFunction (fun v : Fin k → V ↦ icmpTable (v i)) :=
  DefinableFunction₁.comp (F := icmpTable) (DefinableFunction.var i)

@[simp] lemma icmpTable_seq (n : V) : Seq (icmpTable n) := by
  induction n using ISigma1.sigma1_succ_induction
  · exact Definable.comp₁ (def_icmpTable 0)
  case zero => simp
  case succ n ih => rw [icmpTable_succ]; exact ih.seqCons _

@[simp] lemma icmpTable_lh (n : V) : lh (icmpTable n) = n + 1 := by
  induction n using ISigma1.sigma1_succ_induction
  · exact Definable.comp₂ (DefinableFunction₁.comp (F := lh) (def_icmpTable 0)) (by definability)
  case zero => simp
  case succ n ih => rw [icmpTable_succ, Seq.lh_seqCons _ (icmpTable_seq n), ih]

lemma znth_icmpTable_succ {n k : V} (hk : k < n + 1) :
    znth (icmpTable (n + 1)) k = znth (icmpTable n) k := by
  rw [icmpTable_succ]
  exact znth_seqCons_of_lt (icmpTable_seq n) _ (by rw [icmpTable_lh]; exact hk)

/-- **Table stability.** Every entry of the length-`(N+1)` table is the genuine `icmp` value at that
pair index. (`icmp` itself reads `znth (icmpTable ⟪c1,c2⟫) ⟪c1,c2⟫`; this connects the two via the
pair round-trip `⟪π₁ k, π₂ k⟫ = k`.) -/
lemma znth_icmpTable_eq_icmp : ∀ N : V, ∀ k ≤ N, znth (icmpTable N) k = icmp (π₁ k) (π₂ k) := by
  intro N
  induction N using ISigma1.sigma1_succ_induction
  · refine Definable.ball_le (by definability) ?_
    exact Definable.comp₂
      (DefinableFunction₂.comp (F := znth) (def_icmpTable 1) (DefinableFunction.var 0))
      (DefinableFunction₂.comp (F := icmp)
        (DefinableFunction₁.comp (F := pi₁) (DefinableFunction.var 0))
        (DefinableFunction₁.comp (F := pi₂) (DefinableFunction.var 0)))
  case zero =>
    intro k hk
    rcases (nonpos_iff_eq_zero.mp hk) with rfl
    rw [icmp]; simp
  case succ N ih =>
    intro k hk
    rcases eq_or_lt_of_le hk with rfl | hlt
    · rw [icmp, pair_unpair]
    · rw [znth_icmpTable_succ hlt]
      exact ih k (le_iff_lt_succ.mpr hlt)

/-! ### Base cases & the `icmp` recursion law -/

lemma pair_zero_zero : (⟪(0 : V), 0⟫ : V) = 0 := by simp [pair]

@[simp] lemma icmp_zero_zero : icmp (0 : V) 0 = 1 := by
  rw [icmp, pair_zero_zero, icmpTable_zero]
  exact (singleton_seq 1).znth_eq_of_mem ((mem_singleton_seq_iff 1 1).mpr rfl)

lemma icmp_zero_ocOadd (ec n rc : V) : icmp (0 : V) (ocOadd ec n rc) = 0 := by
  set c2 := ocOadd ec n rc with hc2
  have hpos2 : 0 < c2 := ocOadd_pos ec n rc
  set m := (⟪(0 : V), c2⟫ : V) with hm
  have hmpos : 0 < m := lt_of_lt_of_le hpos2 (by rw [hm]; exact le_pair_right 0 c2)
  obtain ⟨M, hM⟩ : ∃ M, m = M + 1 :=
    ⟨m - 1, (sub_add_self_of_le (pos_iff_one_le.mp hmpos)).symm⟩
  have key : znth (icmpTable m) m = icmpNext m (icmpTable M) := by
    rw [hM, icmpTable_succ]
    have := znth_seqCons_self (icmpTable_seq M) (icmpNext (M + 1) (icmpTable M))
    rwa [icmpTable_lh] at this
  have hpi1 : π₁ m = 0 := by rw [hm]; simp
  have hpi2 : π₂ m = c2 := by rw [hm]; simp
  rw [icmp, ← hm, key, icmpNext, hpi1, hpi2]
  simp [hpos2.ne']

lemma icmp_ocOadd_zero (ec n rc : V) : icmp (ocOadd ec n rc) 0 = 2 := by
  set c1 := ocOadd ec n rc with hc1
  have hpos1 : 0 < c1 := ocOadd_pos ec n rc
  set m := (⟪c1, (0 : V)⟫ : V) with hm
  have hmpos : 0 < m := lt_of_lt_of_le hpos1 (by rw [hm]; exact le_pair_left c1 0)
  obtain ⟨M, hM⟩ : ∃ M, m = M + 1 :=
    ⟨m - 1, (sub_add_self_of_le (pos_iff_one_le.mp hmpos)).symm⟩
  have key : znth (icmpTable m) m = icmpNext m (icmpTable M) := by
    rw [hM, icmpTable_succ]
    have := znth_seqCons_self (icmpTable_seq M) (icmpNext (M + 1) (icmpTable M))
    rwa [icmpTable_lh] at this
  have hpi1 : π₁ m = c1 := by rw [hm]; simp
  have hpi2 : π₂ m = 0 := by rw [hm]; simp
  rw [icmp, ← hm, key, icmpNext, hpi1, hpi2]
  simp [hpos1.ne']

/-- **The internal `icmp` recursion**: comparison of two positive (`oadd`) codes is the lexicographic
`then`-combine of (exponent comparison, leading-coefficient comparison, tail comparison). Mirrors
`ONoteComp.cmpStep`/`ONote.cmp`, realized on codes inside `V`. -/
lemma icmp_ocOadd (e1 n1 r1 e2 n2 r2 : V) :
    icmp (ocOadd e1 n1 r1) (ocOadd e2 n2 r2)
      = thenV (icmp e1 e2) (thenV (cmpV n1 n2) (icmp r1 r2)) := by
  set c1 := ocOadd e1 n1 r1 with hc1
  set c2 := ocOadd e2 n2 r2 with hc2
  have hpos1 : 0 < c1 := ocOadd_pos e1 n1 r1
  have hpos2 : 0 < c2 := ocOadd_pos e2 n2 r2
  set m := (⟪c1, c2⟫ : V) with hm
  have hmpos : 0 < m := lt_of_lt_of_le hpos1 (by rw [hm]; exact le_pair_left c1 c2)
  obtain ⟨M, hM⟩ : ∃ M, m = M + 1 :=
    ⟨m - 1, (sub_add_self_of_le (pos_iff_one_le.mp hmpos)).symm⟩
  have key : znth (icmpTable m) m = icmpNext m (icmpTable M) := by
    rw [hM, icmpTable_succ]
    have := znth_seqCons_self (icmpTable_seq M) (icmpNext (M + 1) (icmpTable M))
    rwa [icmpTable_lh] at this
  -- the two sub-indices are `≤ M`
  have hpi1 : π₁ m = c1 := by rw [hm]; simp
  have hpi2 : π₂ m = c2 := by rw [hm]; simp
  have hexplt : (⟪ocExp c1, ocExp c2⟫ : V) < m := by
    rw [hm]; exact pair_lt_pair (ocExp_lt e1 n1 r1) (ocExp_lt e2 n2 r2)
  have htaillt : (⟪ocTail c1, ocTail c2⟫ : V) < m := by
    rw [hm]; exact pair_lt_pair (ocTail_lt e1 n1 r1) (ocTail_lt e2 n2 r2)
  have hexple : (⟪ocExp c1, ocExp c2⟫ : V) ≤ M := le_iff_lt_succ.mpr (hM ▸ hexplt)
  have htaille : (⟪ocTail c1, ocTail c2⟫ : V) ≤ M := le_iff_lt_succ.mpr (hM ▸ htaillt)
  rw [icmp, ← hm, key, icmpNext, hpi1, hpi2]
  simp only [hpos1.ne', hpos2.ne', if_false]
  rw [icmpMain, hpi1, hpi2,
    znth_icmpTable_eq_icmp M _ hexple, znth_icmpTable_eq_icmp M _ htaille]
  simp only [pi₁_pair, pi₂_pair, ocExp_ocOadd, ocCoeff_ocOadd, ocTail_ocOadd, hc1, hc2]



/-! ## Internal `NF` predicate `isNF` (CNF well-formedness flag)

`isNF c` (`isNFb c = 1`) holds iff the code `c` is a valid Cantor-normal-form notation: positive
coefficients, NF sub-exponent and tail, and the tail's leading exponent strictly below the head's
(`icmp (ocExp r) e = 0`). Built as a `0/1` flag via a course-of-values table (product of four
definable indicator flags, so the step stays `𝚺₁` with no negated existentials). The recursion
`isNF_ocOadd` is the form the order-reflection and `βₖ`-construction consume. -/


/-- `0/1` indicator that `a ≠ 0`. -/
noncomputable def nzIndic (a : V) : V := if a = 0 then 0 else 1

def _root_.LO.FirstOrder.Arithmetic.nzIndicDef : 𝚺₀.Semisentence 2 := .mkSigma
  “y a. (a = 0 ∧ y = 0) ∨ (a ≠ 0 ∧ y = 1)”

instance nzIndic_defined : 𝚺₀-Function₁ (nzIndic : V → V) via nzIndicDef := .mk fun v ↦ by
  simp [nzIndicDef, nzIndic]; by_cases h : v 1 = 0 <;> simp [h]

instance nzIndic_definable : 𝚺₀-Function₁ (nzIndic : V → V) := nzIndic_defined.to_definable
instance nzIndic_definable' (Γ) : Γ-Function₁ (nzIndic : V → V) := nzIndic_definable.of_zero

/-- `0/1` indicator that `icmp a b = 0` (i.e. `a ≺ b`). -/
noncomputable def ltIndic (a b : V) : V := if icmp a b = 0 then 1 else 0

def _root_.LO.FirstOrder.Arithmetic.ltIndicDef : 𝚺₁.Semisentence 3 := .mkSigma
  “y a b. ∃ c, !icmpDef c a b ∧ ((c = 0 ∧ y = 1) ∨ (c ≠ 0 ∧ y = 0))”

instance ltIndic_defined : 𝚺₁-Function₂ (ltIndic : V → V → V) via ltIndicDef := .mk fun v ↦ by
  simp [ltIndicDef, ltIndic, icmp_defined.iff]
  by_cases h : icmp (v 1) (v 2) = 0 <;> simp [h]

instance ltIndic_definable : 𝚺₁-Function₂ (ltIndic : V → V → V) := ltIndic_defined.to_definable

/-- The tail-exponent condition flag for `c` (an `oadd`-code): `1` if the tail is `0` or its leading
exponent is `≺` `c`'s exponent, else `0`. -/
noncomputable def tailOk (c : V) : V :=
  if ocTail c = 0 then 1 else ltIndic (ocExp (ocTail c)) (ocExp c)

def _root_.LO.FirstOrder.Arithmetic.tailOkDef : 𝚺₁.Semisentence 2 := .mkSigma
  “y c. ∃ t, !sndIdxDef t c ∧
    ((t = 0 ∧ y = 1) ∨ (t ≠ 0 ∧ ∃ et, !ocExpDef et t ∧ ∃ e, !ocExpDef e c ∧ !ltIndicDef y et e))”

instance tailOk_defined : 𝚺₁-Function₁ (tailOk : V → V) via tailOkDef := .mk fun v ↦ by
  simp [tailOkDef, tailOk, ocTail, sndIdx_defined.iff, ocExp_defined.iff, ltIndic_defined.iff]
  by_cases h : sndIdx (v 1) = 0 <;> simp [h]

instance tailOk_definable : 𝚺₁-Function₁ (tailOk : V → V) := tailOk_defined.to_definable

/-- Table step of `isNFb` (only ever evaluated at codes `c > 0`, since position `0` is seeded): the
product of the four CNF well-formedness flags — coefficient positive, exponent NF, tail NF, tail
exponent below `c`'s exponent (`znth s e`, `znth s r` read the NF flags of the subcodes). -/
noncomputable def isNFbNext (c s : V) : V :=
  nzIndic (ocCoeff c) * znth s (ocExp c) * znth s (ocTail c) * tailOk c

def _root_.LO.FirstOrder.Arithmetic.isNFbNextDef : 𝚺₁.Semisentence 3 := .mkSigma
  “y c s.
    ∃ co, !ocCoeffDef co c ∧ ∃ nc, !nzIndicDef nc co ∧
    ∃ e, !ocExpDef e c ∧ ∃ se, !znthDef se s e ∧
    ∃ t, !sndIdxDef t c ∧ ∃ st, !znthDef st s t ∧
    ∃ tk, !tailOkDef tk c ∧
    y = nc * se * st * tk”

instance isNFbNext_defined : 𝚺₁-Function₂ (isNFbNext : V → V → V) via isNFbNextDef := .mk fun v ↦ by
  simp [isNFbNextDef, isNFbNext, ocCoeff_defined.iff, nzIndic_defined.iff, ocExp_defined.iff,
    ocTail, sndIdx_defined.iff, znth_defined.iff, tailOk_defined.iff]

instance isNFbNext_definable : 𝚺₁-Function₂ (isNFbNext : V → V → V) := isNFbNext_defined.to_definable

/-! ### Indicator value lemmas -/

@[simp] lemma nzIndic_eq_one_iff (a : V) : nzIndic a = 1 ↔ a ≠ 0 := by
  unfold nzIndic; by_cases h : a = 0 <;> simp [h]

lemma nzIndic_le_one (a : V) : nzIndic a ≤ 1 := by
  unfold nzIndic; by_cases h : a = 0 <;> simp [h]

@[simp] lemma ltIndic_eq_one_iff (a b : V) : ltIndic a b = 1 ↔ icmp a b = 0 := by
  unfold ltIndic; by_cases h : icmp a b = 0 <;> simp [h]

lemma ltIndic_le_one (a b : V) : ltIndic a b ≤ 1 := by
  unfold ltIndic; by_cases h : icmp a b = 0 <;> simp [h]

lemma tailOk_le_one (c : V) : tailOk c ≤ 1 := by
  unfold tailOk; by_cases h : ocTail c = 0 <;> simp [h, ltIndic_le_one]

lemma tailOk_ocOadd (ec n rc : V) :
    tailOk (ocOadd ec n rc) = if rc = 0 then 1 else ltIndic (ocExp rc) ec := by
  unfold tailOk; rw [ocTail_ocOadd, ocExp_ocOadd]

/-! ### The `isNFb` table -/

def isNFbTable.blueprint : PR.Blueprint 0 where
  zero := .mkSigma “y. !mkSeq₁Def y 1”
  succ := .mkSigma “y ih n. ∃ v, !isNFbNextDef v (n + 1) ih ∧ !seqConsDef y ih v”

noncomputable def isNFbTable.construction : PR.Construction V isNFbTable.blueprint where
  zero := fun _ ↦ !⟦1⟧
  succ := fun _ n ih ↦ seqCons ih (isNFbNext (n + 1) ih)
  zero_defined := .mk fun v ↦ by
    simp [isNFbTable.blueprint, mkSeq₁Def, seqCons_defined.iff, emptyset_def]
  succ_defined := .mk fun v ↦ by
    simp [isNFbTable.blueprint, isNFbNext_defined.iff, seqCons_defined.iff]

noncomputable def isNFbTable (n : V) : V := isNFbTable.construction.result ![] n

@[simp] lemma isNFbTable_zero : isNFbTable (0 : V) = !⟦1⟧ := by
  simp [isNFbTable, isNFbTable.construction]

@[simp] lemma isNFbTable_succ (n : V) :
    isNFbTable (n + 1) = seqCons (isNFbTable n) (isNFbNext (n + 1) (isNFbTable n)) := by
  simp [isNFbTable, isNFbTable.construction]

/-- **Internal CNF well-formedness flag** (`0/1`): `1` iff the code `c` is a valid CNF notation. -/
noncomputable def isNFb (c : V) : V := znth (isNFbTable c) c

/-- **Internal `NF` predicate** on codes inside `V`. -/
def isNF (c : V) : Prop := isNFb c = 1

def _root_.LO.FirstOrder.Arithmetic.isNFbTableDef : 𝚺₁.Semisentence 2 :=
  isNFbTable.blueprint.resultDef.rew (Rew.subst ![#0, #1])

instance isNFbTable_defined : 𝚺₁-Function₁ (isNFbTable : V → V) via isNFbTableDef := .mk
  fun v ↦ by simp [isNFbTable.construction.result_defined_iff, isNFbTableDef]; rfl

instance isNFbTable_definable : 𝚺₁-Function₁ (isNFbTable : V → V) := isNFbTable_defined.to_definable
instance isNFbTable_definable' (Γ) : Γ-[m + 1]-Function₁ (isNFbTable : V → V) :=
  isNFbTable_definable.of_sigmaOne

def _root_.LO.FirstOrder.Arithmetic.isNFbDef : 𝚺₁.Semisentence 2 := .mkSigma
  “y c. ∃ t, !isNFbTableDef t c ∧ !znthDef y t c”

instance isNFb_defined : 𝚺₁-Function₁ (isNFb : V → V) via isNFbDef := .mk fun v ↦ by
  simp [isNFbDef, isNFb, isNFbTable_defined.iff, znth_defined.iff]

instance isNFb_definable : 𝚺₁-Function₁ (isNFb : V → V) := isNFb_defined.to_definable
instance isNFb_definable' (Γ) : Γ-[m + 1]-Function₁ (isNFb : V → V) := isNFb_definable.of_sigmaOne

instance isNF_definable (Γ) : Γ-[m + 1]-Predicate (isNF : V → Prop) := by
  unfold isNF; definability

/-! ### Structural correctness of the `isNFb` table -/

private lemma def_isNFbTable {k} (i : Fin k) :
    𝚺-[1].DefinableFunction (fun v : Fin k → V ↦ isNFbTable (v i)) :=
  DefinableFunction₁.comp (F := isNFbTable) (DefinableFunction.var i)

private lemma def_isNFb {k} (i : Fin k) :
    𝚺-[1].DefinableFunction (fun v : Fin k → V ↦ isNFb (v i)) :=
  DefinableFunction₁.comp (F := isNFb) (DefinableFunction.var i)

@[simp] lemma isNFbTable_seq (n : V) : Seq (isNFbTable n) := by
  induction n using ISigma1.sigma1_succ_induction
  · exact Definable.comp₁ (def_isNFbTable 0)
  case zero => simp
  case succ n ih => rw [isNFbTable_succ]; exact ih.seqCons _

@[simp] lemma isNFbTable_lh (n : V) : lh (isNFbTable n) = n + 1 := by
  induction n using ISigma1.sigma1_succ_induction
  · exact Definable.comp₂ (DefinableFunction₁.comp (F := lh) (def_isNFbTable 0)) (by definability)
  case zero => simp
  case succ n ih => rw [isNFbTable_succ, Seq.lh_seqCons _ (isNFbTable_seq n), ih]

lemma znth_isNFbTable_succ {n k : V} (hk : k < n + 1) :
    znth (isNFbTable (n + 1)) k = znth (isNFbTable n) k := by
  rw [isNFbTable_succ]
  exact znth_seqCons_of_lt (isNFbTable_seq n) _ (by rw [isNFbTable_lh]; exact hk)

lemma znth_isNFbTable_eq_isNFb : ∀ N : V, ∀ k ≤ N, znth (isNFbTable N) k = isNFb k := by
  intro N
  induction N using ISigma1.sigma1_succ_induction
  · refine Definable.ball_le (by definability) ?_
    exact Definable.comp₂
      (DefinableFunction₂.comp (F := znth) (def_isNFbTable 1) (DefinableFunction.var 0))
      (def_isNFb 0)
  case zero =>
    intro k hk
    rcases (nonpos_iff_eq_zero.mp hk) with rfl
    rfl
  case succ N ih =>
    intro k hk
    rcases eq_or_lt_of_le hk with rfl | hlt
    · rfl
    · rw [znth_isNFbTable_succ hlt]
      exact ih k (le_iff_lt_succ.mpr hlt)

@[simp] lemma isNFb_zero : isNFb (0 : V) = 1 := by
  simp only [isNFb, isNFbTable_zero]
  exact (singleton_seq 1).znth_eq_of_mem ((mem_singleton_seq_iff 1 1).mpr rfl)

@[simp] lemma isNF_zero : isNF (0 : V) := by simp [isNF]

/-- **The internal `isNFb` recursion** on codes. -/
lemma isNFb_ocOadd (ec n rc : V) :
    isNFb (ocOadd ec n rc)
      = nzIndic n * isNFb ec * isNFb rc * tailOk (ocOadd ec n rc) := by
  set c := ocOadd ec n rc with hc
  have hpos : 0 < c := ocOadd_pos ec n rc
  obtain ⟨M, hM⟩ : ∃ M, c = M + 1 :=
    ⟨c - 1, (sub_add_self_of_le (pos_iff_one_le.mp hpos)).symm⟩
  have key : znth (isNFbTable c) c = isNFbNext c (isNFbTable M) := by
    rw [hM, isNFbTable_succ]
    have := znth_seqCons_self (isNFbTable_seq M) (isNFbNext (M + 1) (isNFbTable M))
    rwa [isNFbTable_lh] at this
  have hexp : ocExp c ≤ M := le_iff_lt_succ.mpr (hM ▸ ocExp_lt ec n rc)
  have htail : ocTail c ≤ M := le_iff_lt_succ.mpr (hM ▸ ocTail_lt ec n rc)
  rw [isNFb, key, isNFbNext,
    znth_isNFbTable_eq_isNFb M (ocExp c) hexp, znth_isNFbTable_eq_isNFb M (ocTail c) htail,
    ocCoeff_ocOadd, ocExp_ocOadd, ocTail_ocOadd]

/-- `isNFb` is a `0/1` flag. -/
lemma isNFb_le_one (c : V) : isNFb c ≤ 1 := by
  induction c using ISigma1.sigma1_order_induction
  · exact Definable.comp₂ (def_isNFb 0) (by definability)
  case ind c ih =>
    rcases eq_or_ne c 0 with rfl | hc
    · simp
    · obtain ⟨M, hM⟩ : ∃ M, c = M + 1 :=
        ⟨c - 1, (sub_add_self_of_le (pos_iff_one_le.mp (pos_iff_ne_zero.mpr hc))).symm⟩
      have key : znth (isNFbTable c) c = isNFbNext c (isNFbTable M) := by
        rw [hM, isNFbTable_succ]
        have := znth_seqCons_self (isNFbTable_seq M) (isNFbNext (M + 1) (isNFbTable M))
        rwa [isNFbTable_lh] at this
      have hexp : ocExp c ≤ M := by
        have := ocExp_lt_of_pos (pos_iff_ne_zero.mpr hc); exact le_iff_lt_succ.mpr (hM ▸ this)
      have htail : ocTail c ≤ M := by
        have := ocTail_lt_of_pos (pos_iff_ne_zero.mpr hc); exact le_iff_lt_succ.mpr (hM ▸ this)
      have hse : isNFb (ocExp c) ≤ 1 := ih _ (ocExp_lt_of_pos (pos_iff_ne_zero.mpr hc))
      have hst : isNFb (ocTail c) ≤ 1 := ih _ (ocTail_lt_of_pos (pos_iff_ne_zero.mpr hc))
      rw [isNFb, key, isNFbNext,
        znth_isNFbTable_eq_isNFb M (ocExp c) hexp, znth_isNFbTable_eq_isNFb M (ocTail c) htail]
      have h1 := nzIndic_le_one (ocCoeff c)
      have h4 := tailOk_le_one c
      calc nzIndic (ocCoeff c) * isNFb (ocExp c) * isNFb (ocTail c) * tailOk c
          ≤ 1 * 1 * 1 * 1 := by gcongr
        _ = 1 := by simp

private lemma prod4_eq_one {a b c d : V} (ha : a ≤ 1) (hb : b ≤ 1) (hc : c ≤ 1) (hd : d ≤ 1) :
    a * b * c * d = 1 ↔ a = 1 ∧ b = 1 ∧ c = 1 ∧ d = 1 := by
  constructor
  · intro h
    have ka : a * b * c * d ≤ a := by
      calc a * b * c * d ≤ a * 1 * 1 * 1 := by gcongr
        _ = a := by simp
    have kb : a * b * c * d ≤ b := by
      calc a * b * c * d ≤ 1 * b * 1 * 1 := by gcongr
        _ = b := by simp
    have kc : a * b * c * d ≤ c := by
      calc a * b * c * d ≤ 1 * 1 * c * 1 := by gcongr
        _ = c := by simp
    have kd : a * b * c * d ≤ d := by
      calc a * b * c * d ≤ 1 * 1 * 1 * d := by gcongr
        _ = d := by simp
    refine ⟨le_antisymm ha (h ▸ ka), le_antisymm hb (h ▸ kb),
      le_antisymm hc (h ▸ kc), le_antisymm hd (h ▸ kd)⟩
  · rintro ⟨rfl, rfl, rfl, rfl⟩; simp

lemma tailFlag_eq_one_iff (ec rc : V) :
    (if rc = 0 then (1 : V) else ltIndic (ocExp rc) ec) = 1
      ↔ (rc = 0 ∨ icmp (ocExp rc) ec = 0) := by
  by_cases h : rc = 0 <;> simp [h]

/-- **The internal `NF` recursion** (the form the order-reflection and `βₖ`-construction consume). -/
lemma isNF_ocOadd (ec n rc : V) :
    isNF (ocOadd ec n rc) ↔
      n ≠ 0 ∧ isNF ec ∧ isNF rc ∧ (rc = 0 ∨ icmp (ocExp rc) ec = 0) := by
  unfold isNF
  rw [isNFb_ocOadd, tailOk_ocOadd,
    prod4_eq_one (nzIndic_le_one n) (isNFb_le_one ec) (isNFb_le_one rc)
      (by by_cases h : rc = 0 <;> simp [h, ltIndic_le_one]),
    nzIndic_eq_one_iff, tailFlag_eq_one_iff]


/-! ## Order-reflection: `ievalNat b` reflects the CNF (`icmp`) order (Rathjen 2.3(iii))

The descent's `ineq6_step` consumes `o ≺ p ⟹ ievalNat b o < ievalNat b p` on the `isNF`/`iCanon b`
domain. Proved digit-direct (no ordinals, so it internalizes): the value-bound `TB` and the
monotonicity `MONO` are mutually recursive (the leading term dominates iff the tail is bounded by the
leading power, which needs monotonicity at the exponents), so both are carried in one strong induction
on a single code measure. `icmp_eq_imp_eq` (a separate induction) supplies the `eq` case. -/

/-- **Destructor**: a positive code is the `ocOadd` of its decoded parts. -/
lemma ocOadd_destruct {c : V} (hc : c ≠ 0) :
    ocOadd (ocExp c) (ocCoeff c) (ocTail c) = c := by
  have hpos : 0 < c := pos_iff_ne_zero.mpr hc
  unfold ocOadd ocExp ocCoeff ocTail fstIdx sndIdx
  rw [pair_unpair, pair_unpair]
  exact sub_add_self_of_le (pos_iff_one_le.mp hpos)

/-! ### `thenV` / `cmpV` value lemmas -/

lemma thenV_eq_one {a b : V} : thenV a b = 1 ↔ a = 1 ∧ b = 1 := by
  unfold thenV; by_cases h : a = 1 <;> simp [h]

lemma thenV_eq_zero {a b : V} : thenV a b = 0 ↔ a = 0 ∨ (a = 1 ∧ b = 0) := by
  unfold thenV; by_cases h : a = 1 <;> simp [h]

lemma cmpV_eq_zero {a b : V} : cmpV a b = 0 ↔ a < b := by
  unfold cmpV
  by_cases h : a < b
  · simp [h]
  · simp only [h]; by_cases h2 : a = b <;> simp [h2]

lemma cmpV_eq_one {a b : V} : cmpV a b = 1 ↔ a = b := by
  unfold cmpV
  by_cases h : a < b
  · simp only [if_pos h]
    constructor
    · intro h0; simp at h0
    · rintro rfl; exact absurd h (_root_.lt_irrefl a)
  · by_cases h2 : a = b
    · subst h2; simp
    · simp [h, h2]

/-! ### Positivity & the tail-bound ⟹ whole-bound step -/

/-- A nonzero NF code has positive value. -/
lemma ievalNat_pos {b c : V} (hnf : isNF c) (hc : c ≠ 0) : 0 < ievalNat b c := by
  obtain ⟨e, n, r, rfl⟩ : ∃ e n r, c = ocOadd e n r :=
    ⟨ocExp c, ocCoeff c, ocTail c, (ocOadd_destruct hc).symm⟩
  rw [ievalNat_ocOadd]
  have hn : n ≠ 0 := ((isNF_ocOadd e n r).1 hnf).1
  have hnp : 0 < n := pos_iff_ne_zero.mpr hn
  have hp : 0 < ipow (b + 1) (ievalNat b e) := ipow_pos (by simp) _
  calc (0 : V) < n * ipow (b + 1) (ievalNat b e) := mul_pos hnp hp
    _ ≤ n * ipow (b + 1) (ievalNat b e) + ievalNat b r := le_self_add

/-- **Tail-bound ⟹ whole-bound.** If the tail value is below `(b+1)^E` (`E = ievalNat b (ocExp c)`)
then the whole code value is below `(b+1)^(E+1)`. Uses `n ≤ b` (`iCanon`). -/
lemma tb_imp_bd {b c : V} (hnf : isNF c) (hcanon : iCanon b c) (hc : c ≠ 0)
    (htb : ievalNat b (ocTail c) < ipow (b + 1) (ievalNat b (ocExp c))) :
    ievalNat b c < ipow (b + 1) (ievalNat b (ocExp c) + 1) := by
  obtain ⟨e, n, r, rfl⟩ : ∃ e n r, c = ocOadd e n r :=
    ⟨ocExp c, ocCoeff c, ocTail c, (ocOadd_destruct hc).symm⟩
  rw [ievalNat_ocOadd, ocExp_ocOadd] at *
  rw [ocTail_ocOadd] at htb
  set E := ievalNat b e with hE
  have hn : n ≤ b := ((iCanon_ocOadd b e n r).1 hcanon).1
  have hpe : 0 < ipow (b + 1) E := ipow_pos (by simp) _
  rw [ipow_succ]
  calc n * ipow (b + 1) E + ievalNat b r
      < n * ipow (b + 1) E + ipow (b + 1) E := by gcongr
    _ = (n + 1) * ipow (b + 1) E := by rw [add_mul, one_mul]
    _ ≤ (b + 1) * ipow (b + 1) E := by gcongr
    _ = ipow (b + 1) E * (b + 1) := by rw [mul_comm]

/-! ### Subterm NF/Canon projections -/

private lemma isNF_ocExp {c : V} (h : isNF c) (hc : c ≠ 0) : isNF (ocExp c) := by
  have := (isNF_ocOadd (ocExp c) (ocCoeff c) (ocTail c)).1 (by rw [ocOadd_destruct hc]; exact h)
  exact this.2.1

private lemma isNF_ocTail {c : V} (h : isNF c) (hc : c ≠ 0) : isNF (ocTail c) := by
  have := (isNF_ocOadd (ocExp c) (ocCoeff c) (ocTail c)).1 (by rw [ocOadd_destruct hc]; exact h)
  exact this.2.2.1

private lemma coeff_ne_zero {c : V} (h : isNF c) (hc : c ≠ 0) : ocCoeff c ≠ 0 := by
  have := (isNF_ocOadd (ocExp c) (ocCoeff c) (ocTail c)).1 (by rw [ocOadd_destruct hc]; exact h)
  exact this.1

private lemma tailExp_cond {c : V} (h : isNF c) (hc : c ≠ 0) :
    ocTail c = 0 ∨ icmp (ocExp (ocTail c)) (ocExp c) = 0 := by
  have := (isNF_ocOadd (ocExp c) (ocCoeff c) (ocTail c)).1 (by rw [ocOadd_destruct hc]; exact h)
  exact this.2.2.2

private lemma iCanon_ocExp {b c : V} (h : iCanon b c) (hc : c ≠ 0) : iCanon b (ocExp c) := by
  have := (iCanon_ocOadd b (ocExp c) (ocCoeff c) (ocTail c)).1 (by rw [ocOadd_destruct hc]; exact h)
  exact this.2.1

private lemma iCanon_ocTail {b c : V} (h : iCanon b c) (hc : c ≠ 0) : iCanon b (ocTail c) := by
  have := (iCanon_ocOadd b (ocExp c) (ocCoeff c) (ocTail c)).1 (by rw [ocOadd_destruct hc]; exact h)
  exact this.2.2

private lemma coeff_le {b c : V} (h : iCanon b c) (hc : c ≠ 0) : ocCoeff c ≤ b := by
  have := (iCanon_ocOadd b (ocExp c) (ocCoeff c) (ocTail c)).1 (by rw [ocOadd_destruct hc]; exact h)
  exact this.1

/-! ### `icmp` reflects equality -/

private lemma code_lt_of_exp {e n r w : V} (h : ocOadd e n r ≤ w) : e < w := by
  have : e < ocOadd e n r := by have := ocExp_lt e n r; rwa [ocExp_ocOadd] at this
  exact lt_of_lt_of_le this h

private lemma code_lt_of_tail {e n r w : V} (h : ocOadd e n r ≤ w) : r < w := by
  have : r < ocOadd e n r := by have := ocTail_lt e n r; rwa [ocTail_ocOadd] at this
  exact lt_of_lt_of_le this h

theorem icmp_eq_imp_eq : ∀ w : V, ∀ a ≤ w, ∀ c ≤ w, icmp a c = 1 → a = c := by
  intro w
  induction w using ISigma1.sigma1_order_induction
  · definability
  case ind w ih =>
    intro a haw c hcw hcmp
    rcases eq_or_ne a 0 with rfl | ha
    · rcases eq_or_ne c 0 with rfl | hc
      · rfl
      · obtain ⟨e, n, r, rfl⟩ : ∃ e n r, c = ocOadd e n r :=
          ⟨ocExp c, ocCoeff c, ocTail c, (ocOadd_destruct hc).symm⟩
        rw [icmp_zero_ocOadd] at hcmp; exact absurd hcmp (zero_ne_one)
    · rcases eq_or_ne c 0 with rfl | hc
      · obtain ⟨e, n, r, rfl⟩ : ∃ e n r, a = ocOadd e n r :=
          ⟨ocExp a, ocCoeff a, ocTail a, (ocOadd_destruct ha).symm⟩
        rw [icmp_ocOadd_zero] at hcmp; exact absurd hcmp (one_lt_two).ne'
      · obtain ⟨e1, n1, r1, rfl⟩ : ∃ e n r, a = ocOadd e n r :=
          ⟨ocExp a, ocCoeff a, ocTail a, (ocOadd_destruct ha).symm⟩
        obtain ⟨e2, n2, r2, rfl⟩ : ∃ e n r, c = ocOadd e n r :=
          ⟨ocExp c, ocCoeff c, ocTail c, (ocOadd_destruct hc).symm⟩
        rw [icmp_ocOadd, thenV_eq_one, thenV_eq_one] at hcmp
        obtain ⟨he, hn, hr⟩ := hcmp
        have he1w : e1 < w := code_lt_of_exp haw
        have he2w : e2 < w := code_lt_of_exp hcw
        have hr1w : r1 < w := code_lt_of_tail haw
        have hr2w : r2 < w := code_lt_of_tail hcw
        have hee : e1 = e2 :=
          ih (max e1 e2) (max_lt he1w he2w) e1 (le_max_left _ _) e2 (le_max_right _ _) he
        have hnn : n1 = n2 := cmpV_eq_one.mp hn
        have hrr : r1 = r2 :=
          ih (max r1 r2) (max_lt hr1w hr2w) r1 (le_max_left _ _) r2 (le_max_right _ _) hr
        rw [hee, hnn, hrr]

/-! ### The combined tail-bound + monotonicity induction -/

private def TBstmt (b c : V) : Prop :=
  isNF c → iCanon b c → c ≠ 0 →
    ievalNat b (ocTail c) < ipow (b + 1) (ievalNat b (ocExp c))

private def MONOstmt (b o p : V) : Prop :=
  isNF o → isNF p → iCanon b o → iCanon b p → icmp o p = 0 →
    ievalNat b o < ievalNat b p

private def Combined (b w : V) : Prop :=
  (∀ c ≤ w, TBstmt b c) ∧ (∀ o ≤ w, ∀ p ≤ w, MONOstmt b o p)

theorem evalNat_reflect_combined {b : V} (_ : 1 ≤ b) : ∀ w, Combined b w := by
  have hB1 : (1 : V) ≤ b + 1 := by simp
  intro w
  induction w using ISigma1.sigma1_order_induction
  · unfold Combined TBstmt MONOstmt; definability
  case ind w ih =>
    refine ⟨?tb, ?mono⟩
    case tb =>
      intro c hcw hnf hcanon hc0
      rcases eq_or_ne (ocTail c) 0 with hr0 | hr0
      · rw [hr0, ievalNat_zero]; exact ipow_pos (by simp) _
      · have hicmp : icmp (ocExp (ocTail c)) (ocExp c) = 0 := (tailExp_cond hnf hc0).resolve_left hr0
        have hnfr : isNF (ocTail c) := isNF_ocTail hnf hc0
        have hcanonr : iCanon b (ocTail c) := iCanon_ocTail hcanon hc0
        have htail_lt : ocTail c < c := ocTail_lt_of_pos (pos_iff_ne_zero.mpr hc0)
        have hrw : ocTail c < w := lt_of_lt_of_le htail_lt hcw
        have htbr : TBstmt b (ocTail c) := (ih (ocTail c) hrw).1 (ocTail c) le_rfl
        have hbdr : ievalNat b (ocTail c) < ipow (b + 1) (ievalNat b (ocExp (ocTail c)) + 1) :=
          tb_imp_bd hnfr hcanonr hr0 (htbr hnfr hcanonr hr0)
        -- E(ocExp (ocTail c)) < E(ocExp c) via MONO at smaller codes
        have hexpr_lt : ocExp (ocTail c) < w :=
          lt_of_lt_of_le (lt_trans (ocExp_lt_of_pos (pos_iff_ne_zero.mpr hr0)) htail_lt) hcw
        have hexpc_lt : ocExp c < w := lt_of_lt_of_le (ocExp_lt_of_pos (pos_iff_ne_zero.mpr hc0)) hcw
        have hmono : ievalNat b (ocExp (ocTail c)) < ievalNat b (ocExp c) :=
          (ih (max (ocExp (ocTail c)) (ocExp c)) (max_lt hexpr_lt hexpc_lt)).2
            (ocExp (ocTail c)) (le_max_left _ _) (ocExp c) (le_max_right _ _)
            (isNF_ocExp hnfr hr0) (isNF_ocExp hnf hc0) (iCanon_ocExp hcanonr hr0)
            (iCanon_ocExp hcanon hc0) hicmp
        calc ievalNat b (ocTail c)
            < ipow (b + 1) (ievalNat b (ocExp (ocTail c)) + 1) := hbdr
          _ ≤ ipow (b + 1) (ievalNat b (ocExp c)) :=
              ipow_le_ipow_right hB1 (lt_iff_succ_le.mp hmono)
    case mono =>
      -- TB component, available for codes ≤ w (proved above; re-derive as a local fact)
      have hTB : ∀ c ≤ w, TBstmt b c := by
        intro c hcw hnf hcanon hc0
        rcases eq_or_ne (ocTail c) 0 with hr0 | hr0
        · rw [hr0, ievalNat_zero]; exact ipow_pos (by simp) _
        · have hicmp : icmp (ocExp (ocTail c)) (ocExp c) = 0 :=
            (tailExp_cond hnf hc0).resolve_left hr0
          have hnfr : isNF (ocTail c) := isNF_ocTail hnf hc0
          have hcanonr : iCanon b (ocTail c) := iCanon_ocTail hcanon hc0
          have htail_lt : ocTail c < c := ocTail_lt_of_pos (pos_iff_ne_zero.mpr hc0)
          have hrw : ocTail c < w := lt_of_lt_of_le htail_lt hcw
          have htbr : TBstmt b (ocTail c) := (ih (ocTail c) hrw).1 (ocTail c) le_rfl
          have hbdr : ievalNat b (ocTail c) < ipow (b + 1) (ievalNat b (ocExp (ocTail c)) + 1) :=
            tb_imp_bd hnfr hcanonr hr0 (htbr hnfr hcanonr hr0)
          have hexpr_lt : ocExp (ocTail c) < w :=
            lt_of_lt_of_le (lt_trans (ocExp_lt_of_pos (pos_iff_ne_zero.mpr hr0)) htail_lt) hcw
          have hexpc_lt : ocExp c < w :=
            lt_of_lt_of_le (ocExp_lt_of_pos (pos_iff_ne_zero.mpr hc0)) hcw
          have hmono : ievalNat b (ocExp (ocTail c)) < ievalNat b (ocExp c) :=
            (ih (max (ocExp (ocTail c)) (ocExp c)) (max_lt hexpr_lt hexpc_lt)).2
              (ocExp (ocTail c)) (le_max_left _ _) (ocExp c) (le_max_right _ _)
              (isNF_ocExp hnfr hr0) (isNF_ocExp hnf hc0) (iCanon_ocExp hcanonr hr0)
              (iCanon_ocExp hcanon hc0) hicmp
          calc ievalNat b (ocTail c)
              < ipow (b + 1) (ievalNat b (ocExp (ocTail c)) + 1) := hbdr
            _ ≤ ipow (b + 1) (ievalNat b (ocExp c)) :=
                ipow_le_ipow_right hB1 (lt_iff_succ_le.mp hmono)
      intro o how p hpw hno hnp hco hcp hcmp
      rcases eq_or_ne o 0 with rfl | ho0
      · rcases eq_or_ne p 0 with rfl | hp0
        · rw [icmp_zero_zero] at hcmp; exact absurd hcmp _root_.one_ne_zero
        · rw [ievalNat_zero]; exact ievalNat_pos hnp hp0
      · rcases eq_or_ne p 0 with rfl | hp0
        · obtain ⟨e, n, r, rfl⟩ : ∃ e n r, o = ocOadd e n r :=
            ⟨ocExp o, ocCoeff o, ocTail o, (ocOadd_destruct ho0).symm⟩
          rw [icmp_ocOadd_zero] at hcmp; exact absurd hcmp (_root_.two_ne_zero)
        · obtain ⟨e1, n1, r1, rfl⟩ : ∃ e n r, o = ocOadd e n r :=
            ⟨ocExp o, ocCoeff o, ocTail o, (ocOadd_destruct ho0).symm⟩
          obtain ⟨e2, n2, r2, rfl⟩ : ∃ e n r, p = ocOadd e n r :=
            ⟨ocExp p, ocCoeff p, ocTail p, (ocOadd_destruct hp0).symm⟩
          obtain ⟨hn1, hne1, hnr1, _⟩ := (isNF_ocOadd e1 n1 r1).1 hno
          obtain ⟨hn2, hne2, hnr2, _⟩ := (isNF_ocOadd e2 n2 r2).1 hnp
          obtain ⟨hb1le, hbe1, hbr1⟩ := (iCanon_ocOadd b e1 n1 r1).1 hco
          obtain ⟨hb2le, hbe2, hbr2⟩ := (iCanon_ocOadd b e2 n2 r2).1 hcp
          have hn2pos : 1 ≤ n2 := pos_iff_one_le.mp (pos_iff_ne_zero.mpr hn2)
          -- tail bounds
          have htr1 : ievalNat b r1 < ipow (b + 1) (ievalNat b e1) := by
            have := hTB (ocOadd e1 n1 r1) how hno hco (ocOadd_ne_zero _ _ _)
            rwa [ocTail_ocOadd, ocExp_ocOadd] at this
          have htr2 : ievalNat b r2 < ipow (b + 1) (ievalNat b e2) := by
            have := hTB (ocOadd e2 n2 r2) hpw hnp hcp (ocOadd_ne_zero _ _ _)
            rwa [ocTail_ocOadd, ocExp_ocOadd] at this
          rw [icmp_ocOadd, thenV_eq_zero] at hcmp
          rw [ievalNat_ocOadd, ievalNat_ocOadd]
          set E1 := ievalNat b e1 with hE1
          set E2 := ievalNat b e2 with hE2
          have hpe1 : 0 < ipow (b + 1) E1 := ipow_pos (by simp) _
          have hpe2 : 0 < ipow (b + 1) E2 := ipow_pos (by simp) _
          rcases hcmp with he | ⟨he1, hinner⟩
          · -- icmp e1 e2 = 0 : E1 < E2, leading term of p dominates o
            have he1w : e1 < w := lt_of_lt_of_le (by have := ocExp_lt e1 n1 r1; rwa [ocExp_ocOadd] at this) how
            have he2w : e2 < w := lt_of_lt_of_le (by have := ocExp_lt e2 n2 r2; rwa [ocExp_ocOadd] at this) hpw
            have hElt : E1 < E2 :=
              (ih (max e1 e2) (max_lt he1w he2w)).2 e1 (le_max_left _ _) e2 (le_max_right _ _)
                hne1 hne2 hbe1 hbe2 he
            calc n1 * ipow (b + 1) E1 + ievalNat b r1
                < n1 * ipow (b + 1) E1 + ipow (b + 1) E1 := by gcongr
              _ = (n1 + 1) * ipow (b + 1) E1 := by rw [add_mul, one_mul]
              _ ≤ (b + 1) * ipow (b + 1) E1 := by gcongr
              _ = ipow (b + 1) (E1 + 1) := by rw [ipow_succ, mul_comm]
              _ ≤ ipow (b + 1) E2 := ipow_le_ipow_right hB1 (lt_iff_succ_le.mp hElt)
              _ = 1 * ipow (b + 1) E2 := (one_mul _).symm
              _ ≤ n2 * ipow (b + 1) E2 := by gcongr
              _ ≤ n2 * ipow (b + 1) E2 + ievalNat b r2 := le_self_add
          · -- icmp e1 e2 = 1 : e1 = e2, so E1 = E2; compare coefficients then tails
            have heq : e1 = e2 := by
              have he1w : e1 ≤ w := le_of_lt (lt_of_lt_of_le (by have := ocExp_lt e1 n1 r1; rwa [ocExp_ocOadd] at this) how)
              have he2w : e2 ≤ w := le_of_lt (lt_of_lt_of_le (by have := ocExp_lt e2 n2 r2; rwa [ocExp_ocOadd] at this) hpw)
              exact icmp_eq_imp_eq w e1 he1w e2 he2w he1
            have hEeq : E1 = E2 := by rw [hE1, hE2, heq]
            rw [thenV_eq_zero] at hinner
            rcases hinner with hcn | ⟨hcn, hri⟩
            · -- n1 < n2
              have hnlt : n1 < n2 := cmpV_eq_zero.mp hcn
              calc n1 * ipow (b + 1) E1 + ievalNat b r1
                  < n1 * ipow (b + 1) E1 + ipow (b + 1) E1 := by gcongr
                _ = (n1 + 1) * ipow (b + 1) E1 := by rw [add_mul, one_mul]
                _ ≤ n2 * ipow (b + 1) E1 := by gcongr; exact lt_iff_succ_le.mp hnlt
                _ = n2 * ipow (b + 1) E2 := by rw [hEeq]
                _ ≤ n2 * ipow (b + 1) E2 + ievalNat b r2 := le_self_add
            · -- n1 = n2, r1 ≺ r2
              have hneq : n1 = n2 := cmpV_eq_one.mp hcn
              have hr1w : r1 < w := lt_of_lt_of_le (by have := ocTail_lt e1 n1 r1; rwa [ocTail_ocOadd] at this) how
              have hr2w : r2 < w := lt_of_lt_of_le (by have := ocTail_lt e2 n2 r2; rwa [ocTail_ocOadd] at this) hpw
              have hrlt : ievalNat b r1 < ievalNat b r2 :=
                (ih (max r1 r2) (max_lt hr1w hr2w)).2 r1 (le_max_left _ _) r2 (le_max_right _ _)
                  hnr1 hnr2 hbr1 hbr2 hri
              calc n1 * ipow (b + 1) E1 + ievalNat b r1
                  < n1 * ipow (b + 1) E1 + ievalNat b r2 := by gcongr
                _ = n2 * ipow (b + 1) E2 + ievalNat b r2 := by rw [hneq, hEeq]

/-- **Internal order-reflection (forward direction)**: on the `isNF`/`iCanon b` domain, `≺` (i.e.
`icmp = 0`) implies the strict `ievalNat b` order. This is the Rathjen 2.3(iii) half the descent's
`ineq6_step` consumes. -/
theorem ievalNat_lt_of_icmp_eq_zero {b : V} (hb : 1 ≤ b) {o p : V}
    (hno : isNF o) (hnp : isNF p) (hco : iCanon b o) (hcp : iCanon b p)
    (h : icmp o p = 0) : ievalNat b o < ievalNat b p :=
  (evalNat_reflect_combined hb (max o p)).2 o (le_max_left _ _) p (le_max_right _ _)
    hno hnp hco hcp h

/-! ### `evalNat`'s base-bump law (the substrate bridge to `ibump`) -/

/-- **`ilog` from explicit bounds.** If `b^E ≤ x < b^(E+1)` then `ilog b x = E` — uniqueness of the
leading exponent (mirrors `ilog_exists_unique`'s uniqueness clause). -/
lemma ilog_eq_of_bounds {b x E : V} (hb : 2 ≤ b) (h1 : ipow b E ≤ x) (h2 : x < ipow b (E + 1)) :
    ilog b x = E := by
  have hb1 : (1 : V) ≤ b := le_trans (by simp) hb
  have hx : 0 < x := lt_of_lt_of_le (ipow_pos (lt_of_lt_of_le (by simp) hb) E) h1
  have hle : ipow b (ilog b x) ≤ x := ipow_ilog_le hb hx
  have hlt : x < ipow b (ilog b x + 1) := lt_ipow_ilog_succ hb hx
  rcases lt_trichotomy (ilog b x) E with h | h | h
  · exact absurd (lt_of_lt_of_le (lt_of_lt_of_le hlt
      (ipow_le_ipow_right hb1 (lt_iff_succ_le.mp h))) h1) (_root_.lt_irrefl x)
  · exact h
  · exact absurd (lt_of_lt_of_le (lt_of_lt_of_le h2
      (ipow_le_ipow_right hb1 (lt_iff_succ_le.mp h))) hle) (_root_.lt_irrefl x)

/-- **Tail value bound** (extracted from `evalNat_reflect_combined`'s TB component): on `isNF`/`iCanon b`,
the tail value is strictly below the leading power `(b+1)^(ievalNat b (ocExp c))`. -/
lemma ievalNat_tail_lt {b : V} (hb : 1 ≤ b) {c : V} (hnf : isNF c) (hcanon : iCanon b c)
    (hc : c ≠ 0) : ievalNat b (ocTail c) < ipow (b + 1) (ievalNat b (ocExp c)) :=
  (evalNat_reflect_combined hb c).1 c le_rfl hnf hcanon hc

/-- **Internal `evalNat` base-bump law** (Rathjen's `T̂ ∘ T` bridge, internalized — the analogue of
`DescentCore.evalNat_succ_base`). Raising the evaluation base by one is exactly the hereditary
base-change `ibump (b+1)` of the value: `ievalNat (b+1) c = ibump (b+1) (ievalNat b c)` for `isNF`/
`iCanon b` codes. Proved **digit-direct** by strong induction on the code: peel the leading term
(`ilog`/`/`/`%` via `ilog_eq_of_bounds` + the tail bound), unfold `ibump_pos`, recurse on the exponent
and tail. (No ordinals ⟹ it internalizes; the ℕ-level `toONote`/`repr` route does not.) -/
theorem evalNat_succ_base {b : V} (hb : 1 ≤ b) :
    ∀ w : V, ∀ c ≤ w, isNF c → iCanon b c →
      ievalNat (b + 1) c = ibump (b + 1) (ievalNat b c) := by
  have hb2 : (2 : V) ≤ b + 1 := by rw [← one_add_one_eq_two]; gcongr
  have hb0 : (0 : V) < b + 1 := lt_of_lt_of_le (by simp) hb2
  intro w
  induction w using ISigma1.sigma1_order_induction
  · definability
  case ind w ih =>
    intro c hcw hnf hcanon
    rcases eq_or_ne c 0 with rfl | hc
    · simp
    · obtain ⟨e, n, r, rfl⟩ : ∃ e n r, c = ocOadd e n r :=
        ⟨ocExp c, ocCoeff c, ocTail c, (ocOadd_destruct hc).symm⟩
      obtain ⟨hn0, hnfe, hnfr, _⟩ := (isNF_ocOadd e n r).1 hnf
      obtain ⟨hnb, hcae, hcar⟩ := (iCanon_ocOadd b e n r).1 hcanon
      have hn1 : 1 ≤ n := by simpa using lt_iff_succ_le.mp (pos_iff_ne_zero.mpr hn0)
      have hDpos : 0 < ipow (b + 1) (ievalNat b e) := ipow_pos hb0 _
      have hvpos : 0 < ievalNat b (ocOadd e n r) := ievalNat_pos hnf (ocOadd_ne_zero e n r)
      have htb : ievalNat b r < ipow (b + 1) (ievalNat b e) := by
        have := ievalNat_tail_lt hb hnf hcanon (ocOadd_ne_zero e n r)
        rwa [ocTail_ocOadd, ocExp_ocOadd] at this
      have hilog : ilog (b + 1) (ievalNat b (ocOadd e n r)) = ievalNat b e := by
        rw [ievalNat_ocOadd]
        refine ilog_eq_of_bounds hb2 ?_ ?_
        · calc ipow (b + 1) (ievalNat b e)
              = 1 * ipow (b + 1) (ievalNat b e) := (one_mul _).symm
            _ ≤ n * ipow (b + 1) (ievalNat b e) := by gcongr
            _ ≤ n * ipow (b + 1) (ievalNat b e) + ievalNat b r := le_self_add
        · rw [ipow_succ]
          calc n * ipow (b + 1) (ievalNat b e) + ievalNat b r
              < n * ipow (b + 1) (ievalNat b e) + ipow (b + 1) (ievalNat b e) := by gcongr
            _ = (n + 1) * ipow (b + 1) (ievalNat b e) := by rw [add_mul, one_mul]
            _ ≤ (b + 1) * ipow (b + 1) (ievalNat b e) := by gcongr
            _ = ipow (b + 1) (ievalNat b e) * (b + 1) := mul_comm _ _
      have hdiv : ievalNat b (ocOadd e n r) / ipow (b + 1) (ievalNat b e) = n := by
        rw [ievalNat_ocOadd]; exact div_mul_add n _ htb
      have hmod : ievalNat b (ocOadd e n r) % ipow (b + 1) (ievalNat b e) = ievalNat b r := by
        rw [ievalNat_ocOadd, add_comm (n * ipow (b + 1) (ievalNat b e)),
          mod_add_mul _ n hDpos, mod_eq_self_of_lt htb]
      have he_lt : e < w :=
        lt_of_lt_of_le (by have := ocExp_lt e n r; rwa [ocExp_ocOadd] at this) hcw
      have hr_lt : r < w :=
        lt_of_lt_of_le (by have := ocTail_lt e n r; rwa [ocTail_ocOadd] at this) hcw
      have ihe : ievalNat (b + 1) e = ibump (b + 1) (ievalNat b e) := ih e he_lt e le_rfl hnfe hcae
      have ihr : ievalNat (b + 1) r = ibump (b + 1) (ievalNat b r) := ih r hr_lt r le_rfl hnfr hcar
      rw [ievalNat_ocOadd, ibump_pos hb2 hvpos, hilog, hdiv, hmod, ihe, ihr]

/-! ### Internalized Rathjen inequality (6) -/

/-- **Internal `ineq6_step`** (the `step` of the descent's `hbound`; internalized
`DescentCore.ineq6_step`, Rathjen Lemma 3.6 inequality (6)). For a one-step `≺`-descent `bk1 ≺ bk`
with coefficient bounds `C(bk) ≤ k+1`, `C(bk1) ≤ k+2`, if the run value `m` already dominates
`T̂^{k+1}(bk)` then after one Goodstein bump it dominates `T̂^{k+2}(bk1)`:
`ievalNat (k+2) bk1 ≤ ibump (k+2) m - 1`.

Proved **digit-direct** (no `toONote`/`repr`, unlike the ℕ-level proof) by chaining the three
substrate facts: `evalNat_succ_base` (base-bump `ievalNat (k+2) bk = ibump (k+2) (ievalNat (k+1) bk)`),
`ibump_mono` (monotonicity of the bump), and `ievalNat_lt_of_icmp_eq_zero` (order-reflection at base
`k+2`). The chain is `ievalNat (k+2) bk1 < ievalNat (k+2) bk = ibump (k+2) (ievalNat (k+1) bk)
≤ ibump (k+2) m`. -/
theorem ineq6_step_internal {k bk bk1 : V}
    (hNFk : isNF bk) (hNFk1 : isNF bk1)
    (hck : iCanon (k + 1) bk) (hck1 : iCanon (k + 2) bk1)
    (hdesc : icmp bk1 bk = 0) {m : V} (hm : ievalNat (k + 1) bk ≤ m) :
    ievalNat (k + 2) bk1 ≤ ibump (k + 2) m - 1 := by
  have hk1 : (1 : V) ≤ k + 1 := by simp
  have hk2 : (2 : V) ≤ k + 2 := by simp
  have h121 : (1 : V) ≤ k + 2 := le_trans (by simp) hk2
  have hk12 : k + 1 + 1 = k + 2 := by rw [add_assoc, one_add_one_eq_two]
  -- `iCanon (k+1) bk → iCanon (k+2) bk` (max coefficient ≤ k+1 ≤ k+2)
  have hck' : iCanon (k + 2) bk := by
    rw [iCanon_def] at hck ⊢
    exact le_trans hck (by rw [← hk12]; exact le_self_add)
  -- base-bump law at base `k+1`
  have hbase : ievalNat (k + 2) bk = ibump (k + 2) (ievalNat (k + 1) bk) := by
    have h := evalNat_succ_base hk1 bk bk le_rfl hNFk hck
    rwa [hk12] at h
  -- chain to a strict bound, then `≤ · - 1`
  refine le_sub_one_of_lt ?_
  calc ievalNat (k + 2) bk1
      < ievalNat (k + 2) bk := ievalNat_lt_of_icmp_eq_zero h121 hNFk1 hNFk hck1 hck' hdesc
    _ = ibump (k + 2) (ievalNat (k + 1) bk) := hbase
    _ ≤ ibump (k + 2) m := ibump_mono hk2 hm


/-! ### Internal CNF ordinal addition `iadd` (toward the Rathjen §3 slow-down)

`iadd a b` is `ONote.add a b` on codes. Cantor-normal-form addition recurses on the **first**
argument's tail (`ONote.add (oadd e n r) b = ...` reads `r + b`), with `b` a fixed parameter — so it
is a course-of-values recursion indexed by `a` (parameter `b`), exactly like `ievalNat` (param =
base). The three cases compare leading exponents via `icmp`:
`oadd e n r + oadd e' n' r' = ` `oadd e' n' r'` if `e < e'`; `oadd e (n+n') r'` if `e = e'`;
`oadd e n (r + b)` if `e > e'`. Only the `gt` branch reads the table (at `ocTail a < a`). -/

/-- `ocOadd ec n rc = ⟪⟪ec,n⟫,rc⟫+1` as a graph (for inlining in `iaddNext`'s formula). -/
def _root_.LO.FirstOrder.Arithmetic.ocOaddDef : 𝚺₁.Semisentence 4 := .mkSigma
  “y ec n rc. ∃ p, !pairDef p ec n ∧ ∃ q, !pairDef q p rc ∧ y = q + 1”

instance ocOadd_defined : 𝚺₁-Function₃ (ocOadd : V → V → V → V) via ocOaddDef := .mk fun v ↦ by
  simp [ocOaddDef, ocOadd, pair_defined.iff]

instance ocOadd_definable : 𝚺₁-Function₃ (ocOadd : V → V → V → V) := ocOadd_defined.to_definable

/-- Table step of `iadd` at first-argument index `c` (param `b`, table `s` of `iadd · b`). -/
noncomputable def iaddNext (b c s : V) : V :=
  if c = 0 then b
  else if b = 0 then c
  else if icmp (ocExp c) (ocExp b) = 0 then b
  else if icmp (ocExp c) (ocExp b) = 1 then
    ocOadd (ocExp c) (ocCoeff c + ocCoeff b) (ocTail b)
  else ocOadd (ocExp c) (ocCoeff c) (znth s (ocTail c))

def _root_.LO.FirstOrder.Arithmetic.iaddNextDef : 𝚺₁.Semisentence 4 := .mkSigma
  “y b c s.
    (c = 0 ∧ y = b)
  ∨ (c ≠ 0 ∧ b = 0 ∧ y = c)
  ∨ (c ≠ 0 ∧ b ≠ 0 ∧ ∃ ec, !ocExpDef ec c ∧ ∃ eb, !ocExpDef eb b ∧
       ∃ cm, !icmpDef cm ec eb ∧
       ( (cm = 0 ∧ y = b)
       ∨ (cm = 1 ∧ ∃ cc, !ocCoeffDef cc c ∧ ∃ cb, !ocCoeffDef cb b ∧ ∃ tb, !sndIdxDef tb b ∧
            !ocOaddDef y ec (cc + cb) tb)
       ∨ (cm ≠ 0 ∧ cm ≠ 1 ∧ ∃ cc, !ocCoeffDef cc c ∧ ∃ tc, !sndIdxDef tc c ∧
            ∃ st, !znthDef st s tc ∧ !ocOaddDef y ec cc st) ) )”

instance iaddNext_defined : 𝚺₁-Function₃ (iaddNext : V → V → V → V) via iaddNextDef := .mk
  fun v ↦ by
  simp [iaddNextDef, iaddNext, ocExp_defined.iff, ocCoeff_defined.iff, ocTail,
    sndIdx_defined.iff, icmp_defined.iff, znth_defined.iff, ocOadd_defined.iff]
  by_cases hc : v 2 = 0
  · simp [hc]
  · by_cases hb : v 1 = 0
    · simp [hc, hb]
    · by_cases h0 : icmp (ocExp (v 2)) (ocExp (v 1)) = 0
      · simp [hc, hb, h0]
      · by_cases h1 : icmp (ocExp (v 2)) (ocExp (v 1)) = 1
        · simp [hc, hb, h1]
        · simp [hc, hb, h0, h1]

instance iaddNext_definable : 𝚺₁-Function₃ (iaddNext : V → V → V → V) := iaddNext_defined.to_definable

/-- Blueprint for the `iadd` table (parameter = second summand `b`). -/
def iaddTable.blueprint : PR.Blueprint 1 where
  zero := .mkSigma “y x. !mkSeq₁Def y x”
  succ := .mkSigma “y ih n x. ∃ v, !iaddNextDef v x (n + 1) ih ∧ !seqConsDef y ih v”

noncomputable def iaddTable.construction : PR.Construction V iaddTable.blueprint where
  zero := fun x ↦ !⟦x 0⟧
  succ := fun x n ih ↦ seqCons ih (iaddNext (x 0) (n + 1) ih)
  zero_defined := .mk fun v ↦ by
    simp [iaddTable.blueprint, mkSeq₁Def, seqCons_defined.iff, emptyset_def]
  succ_defined := .mk fun v ↦ by
    simp [iaddTable.blueprint, iaddNext_defined.iff, seqCons_defined.iff]

/-- **The `iadd` table**: `iaddTable b n = ⟨iadd 0 b,…,iadd n b⟩`. -/
noncomputable def iaddTable (b n : V) : V := iaddTable.construction.result ![b] n

@[simp] lemma iaddTable_zero (b : V) : iaddTable b 0 = !⟦b⟧ := by
  simp [iaddTable, iaddTable.construction]

@[simp] lemma iaddTable_succ (b n : V) :
    iaddTable b (n + 1) = seqCons (iaddTable b n) (iaddNext b (n + 1) (iaddTable b n)) := by
  simp [iaddTable, iaddTable.construction]

/-- **Internal CNF ordinal addition** `a + b` inside `V`: the `a`-th entry of the table. -/
noncomputable def iadd (a b : V) : V := znth (iaddTable b a) a

def _root_.LO.FirstOrder.Arithmetic.iaddTableDef : 𝚺₁.Semisentence 3 :=
  iaddTable.blueprint.resultDef.rew (Rew.subst ![#0, #2, #1])

instance iaddTable_defined : 𝚺₁-Function₂ (iaddTable : V → V → V) via iaddTableDef := .mk
  fun v ↦ by simp [iaddTable.construction.result_defined_iff, iaddTableDef]; rfl

instance iaddTable_definable : 𝚺₁-Function₂ (iaddTable : V → V → V) := iaddTable_defined.to_definable
instance iaddTable_definable' (Γ) : Γ-[m + 1]-Function₂ (iaddTable : V → V → V) :=
  iaddTable_definable.of_sigmaOne

def _root_.LO.FirstOrder.Arithmetic.iaddDef : 𝚺₁.Semisentence 3 := .mkSigma
  “y a b. ∃ t, !iaddTableDef t b a ∧ !znthDef y t a”

instance iadd_defined : 𝚺₁-Function₂ (iadd : V → V → V) via iaddDef := .mk fun v ↦ by
  simp [iaddDef, iadd, iaddTable_defined.iff, znth_defined.iff]

instance iadd_definable : 𝚺₁-Function₂ (iadd : V → V → V) := iadd_defined.to_definable
instance iadd_definable' (Γ) : Γ-[m + 1]-Function₂ (iadd : V → V → V) := iadd_definable.of_sigmaOne

/-! ### Structural correctness of `iadd` -/

private lemma def_iaddTable {k} (b : V) (i : Fin k) :
    𝚺-[1].DefinableFunction (fun v : Fin k → V ↦ iaddTable b (v i)) :=
  DefinableFunction₂.comp (F := iaddTable) (DefinableFunction.const b) (DefinableFunction.var i)

private lemma def_iadd {k} (b : V) (i : Fin k) :
    𝚺-[1].DefinableFunction (fun v : Fin k → V ↦ iadd (v i) b) :=
  DefinableFunction₂.comp (F := iadd) (DefinableFunction.var i) (DefinableFunction.const b)

@[simp] lemma iaddTable_seq (b n : V) : Seq (iaddTable b n) := by
  induction n using ISigma1.sigma1_succ_induction
  · exact Definable.comp₁ (def_iaddTable b 0)
  case zero => simp
  case succ n ih => rw [iaddTable_succ]; exact ih.seqCons _

@[simp] lemma iaddTable_lh (b n : V) : lh (iaddTable b n) = n + 1 := by
  induction n using ISigma1.sigma1_succ_induction
  · exact Definable.comp₂ (DefinableFunction₁.comp (F := lh) (def_iaddTable b 0)) (by definability)
  case zero => simp
  case succ n ih => rw [iaddTable_succ, Seq.lh_seqCons _ (iaddTable_seq b n), ih]

lemma znth_iaddTable_succ {b n k : V} (hk : k < n + 1) :
    znth (iaddTable b (n + 1)) k = znth (iaddTable b n) k := by
  rw [iaddTable_succ]
  exact znth_seqCons_of_lt (iaddTable_seq b n) _ (by rw [iaddTable_lh]; exact hk)

lemma znth_iaddTable_eq_iadd (b : V) : ∀ N : V, ∀ k ≤ N, znth (iaddTable b N) k = iadd k b := by
  intro N
  induction N using ISigma1.sigma1_succ_induction
  · refine Definable.ball_le (by definability) ?_
    exact Definable.comp₂
      (DefinableFunction₂.comp (F := znth) (def_iaddTable b 1) (DefinableFunction.var 0))
      (def_iadd b 0)
  case zero =>
    intro k hk
    rcases (nonpos_iff_eq_zero.mp hk) with rfl
    rfl
  case succ N ih =>
    intro k hk
    rcases eq_or_lt_of_le hk with rfl | hlt
    · rfl
    · rw [znth_iaddTable_succ hlt]
      exact ih k (le_iff_lt_succ.mpr hlt)

@[simp] lemma iadd_zero_left (b : V) : iadd 0 b = b := by
  simp only [iadd, iaddTable_zero]
  exact (singleton_seq b).znth_eq_of_mem ((mem_singleton_seq_iff b b).mpr rfl)

/-- **The internal CNF-addition recursion**: `iadd (oadd e n r) b` evaluates the three-way leading
exponent comparison (the `gt` branch recursing into `iadd r b`). -/
lemma iadd_ocOadd (ec n rc b : V) :
    iadd (ocOadd ec n rc) b =
      (if b = 0 then ocOadd ec n rc
       else if icmp ec (ocExp b) = 0 then b
       else if icmp ec (ocExp b) = 1 then ocOadd ec (n + ocCoeff b) (ocTail b)
       else ocOadd ec n (iadd rc b)) := by
  set c := ocOadd ec n rc with hc
  have hpos : 0 < c := ocOadd_pos ec n rc
  obtain ⟨M, hM⟩ : ∃ M, c = M + 1 :=
    ⟨c - 1, (sub_add_self_of_le (pos_iff_one_le.mp hpos)).symm⟩
  have key : znth (iaddTable b c) c = iaddNext b c (iaddTable b M) := by
    rw [hM, iaddTable_succ]
    have := znth_seqCons_self (iaddTable_seq b M) (iaddNext b (M + 1) (iaddTable b M))
    rwa [iaddTable_lh] at this
  have htail : ocTail c ≤ M := by
    have := ocTail_lt ec n rc; rw [← hc] at this; exact le_iff_lt_succ.mpr (hM ▸ this)
  have hcne : c ≠ 0 := hpos.ne'
  rw [iadd, key, iaddNext, if_neg hcne]
  rw [znth_iaddTable_eq_iadd b M (ocTail c) htail, ocExp_ocOadd, ocCoeff_ocOadd, ocTail_ocOadd]

/-! ### Internal ω-multiplication `iomul` (Rathjen Def 3.1: `ω·α` on codes)

`iomul α = ω·α = ω^1·α`. On CNF, `ω·(ω^e·n + r) = ω^{1+e}·n + ω·r` (Rathjen Def 3.1's
`ω^α·β = Σ ω^{α+βⱼ}·lⱼ`, specialized `α = 1`). So `iomul` maps each leading exponent `e` to `1+e`
(`= iadd (ocOadd 0 1 0) e`, using the `iadd` just built) and recurses into the tail — a
course-of-values recursion indexed by the code (no parameter), like `iC`. The exponent bump `1+e`
raises the max-coefficient by at most one (Rathjen Thm 3.5), the engine of the slow-down's `C`-bound. -/

/-- Table step of `iomul` at code index `c` (table `s` of `iomul · `). -/
noncomputable def iomulNext (c s : V) : V :=
  if c = 0 then 0
  else ocOadd (iadd (ocOadd 0 1 0) (ocExp c)) (ocCoeff c) (znth s (ocTail c))

def _root_.LO.FirstOrder.Arithmetic.iomulNextDef : 𝚺₁.Semisentence 3 := .mkSigma
  “y c s.
    (c = 0 ∧ y = 0)
  ∨ (c ≠ 0 ∧ ∃ one, !ocOaddDef one 0 1 0 ∧ ∃ ex, !ocExpDef ex c ∧
       ∃ se, !iaddDef se one ex ∧ ∃ co, !ocCoeffDef co c ∧ ∃ t, !sndIdxDef t c ∧
       ∃ st, !znthDef st s t ∧ !ocOaddDef y se co st)”

instance iomulNext_defined : 𝚺₁-Function₂ (iomulNext : V → V → V) via iomulNextDef := .mk
  fun v ↦ by
  simp [iomulNextDef, iomulNext, ocExp_defined.iff, ocCoeff_defined.iff, ocTail,
    sndIdx_defined.iff, iadd_defined.iff, znth_defined.iff, ocOadd_defined.iff]
  by_cases hc : v 1 = 0 <;> simp [hc]

instance iomulNext_definable : 𝚺₁-Function₂ (iomulNext : V → V → V) := iomulNext_defined.to_definable

/-- Blueprint for the `iomul` table. -/
def iomulTable.blueprint : PR.Blueprint 0 where
  zero := .mkSigma “y. !mkSeq₁Def y 0”
  succ := .mkSigma “y ih n. ∃ v, !iomulNextDef v (n + 1) ih ∧ !seqConsDef y ih v”

noncomputable def iomulTable.construction : PR.Construction V iomulTable.blueprint where
  zero := fun _ ↦ !⟦0⟧
  succ := fun _ n ih ↦ seqCons ih (iomulNext (n + 1) ih)
  zero_defined := .mk fun v ↦ by
    simp [iomulTable.blueprint, mkSeq₁Def, seqCons_defined.iff, emptyset_def]
  succ_defined := .mk fun v ↦ by
    simp [iomulTable.blueprint, iomulNext_defined.iff, seqCons_defined.iff]

noncomputable def iomulTable (n : V) : V := iomulTable.construction.result ![] n

@[simp] lemma iomulTable_zero : iomulTable (0 : V) = !⟦0⟧ := by
  simp [iomulTable, iomulTable.construction]

@[simp] lemma iomulTable_succ (n : V) :
    iomulTable (n + 1) = seqCons (iomulTable n) (iomulNext (n + 1) (iomulTable n)) := by
  simp [iomulTable, iomulTable.construction]

/-- **Internal ω-multiplication** `ω·c` inside `V`: the `c`-th entry of the table. -/
noncomputable def iomul (c : V) : V := znth (iomulTable c) c

def _root_.LO.FirstOrder.Arithmetic.iomulTableDef : 𝚺₁.Semisentence 2 :=
  iomulTable.blueprint.resultDef.rew (Rew.subst ![#0, #1])

instance iomulTable_defined : 𝚺₁-Function₁ (iomulTable : V → V) via iomulTableDef := .mk
  fun v ↦ by simp [iomulTable.construction.result_defined_iff, iomulTableDef]; rfl

instance iomulTable_definable : 𝚺₁-Function₁ (iomulTable : V → V) := iomulTable_defined.to_definable
instance iomulTable_definable' (Γ) : Γ-[m + 1]-Function₁ (iomulTable : V → V) :=
  iomulTable_definable.of_sigmaOne

def _root_.LO.FirstOrder.Arithmetic.iomulDef : 𝚺₁.Semisentence 2 := .mkSigma
  “y c. ∃ t, !iomulTableDef t c ∧ !znthDef y t c”

instance iomul_defined : 𝚺₁-Function₁ (iomul : V → V) via iomulDef := .mk fun v ↦ by
  simp [iomulDef, iomul, iomulTable_defined.iff, znth_defined.iff]

instance iomul_definable : 𝚺₁-Function₁ (iomul : V → V) := iomul_defined.to_definable
instance iomul_definable' (Γ) : Γ-[m + 1]-Function₁ (iomul : V → V) := iomul_definable.of_sigmaOne

/-! ### Structural correctness of `iomul` -/

private lemma def_iomulTable {k} (i : Fin k) :
    𝚺-[1].DefinableFunction (fun v : Fin k → V ↦ iomulTable (v i)) :=
  DefinableFunction₁.comp (F := iomulTable) (DefinableFunction.var i)

private lemma def_iomul {k} (i : Fin k) :
    𝚺-[1].DefinableFunction (fun v : Fin k → V ↦ iomul (v i)) :=
  DefinableFunction₁.comp (F := iomul) (DefinableFunction.var i)

@[simp] lemma iomulTable_seq (n : V) : Seq (iomulTable n) := by
  induction n using ISigma1.sigma1_succ_induction
  · exact Definable.comp₁ (def_iomulTable 0)
  case zero => simp
  case succ n ih => rw [iomulTable_succ]; exact ih.seqCons _

@[simp] lemma iomulTable_lh (n : V) : lh (iomulTable n) = n + 1 := by
  induction n using ISigma1.sigma1_succ_induction
  · exact Definable.comp₂ (DefinableFunction₁.comp (F := lh) (def_iomulTable 0)) (by definability)
  case zero => simp
  case succ n ih => rw [iomulTable_succ, Seq.lh_seqCons _ (iomulTable_seq n), ih]

lemma znth_iomulTable_succ {n k : V} (hk : k < n + 1) :
    znth (iomulTable (n + 1)) k = znth (iomulTable n) k := by
  rw [iomulTable_succ]
  exact znth_seqCons_of_lt (iomulTable_seq n) _ (by rw [iomulTable_lh]; exact hk)

lemma znth_iomulTable_eq_iomul : ∀ N : V, ∀ k ≤ N, znth (iomulTable N) k = iomul k := by
  intro N
  induction N using ISigma1.sigma1_succ_induction
  · refine Definable.ball_le (by definability) ?_
    exact Definable.comp₂
      (DefinableFunction₂.comp (F := znth) (def_iomulTable 1) (DefinableFunction.var 0))
      (def_iomul 0)
  case zero =>
    intro k hk
    rcases (nonpos_iff_eq_zero.mp hk) with rfl
    rfl
  case succ N ih =>
    intro k hk
    rcases eq_or_lt_of_le hk with rfl | hlt
    · rfl
    · rw [znth_iomulTable_succ hlt]
      exact ih k (le_iff_lt_succ.mpr hlt)

@[simp] lemma iomul_zero : iomul (0 : V) = 0 := by
  simp only [iomul, iomulTable_zero]
  exact (singleton_seq 0).znth_eq_of_mem ((mem_singleton_seq_iff 0 0).mpr rfl)

/-- **The internal ω-multiplication recursion**: `ω·(oadd e n r) = oadd (1+e) n (ω·r)`
(Rathjen Def 3.1, `α = 1`). The leading exponent is bumped `e ↦ 1+e = iadd (ocOadd 0 1 0) e`. -/
lemma iomul_ocOadd (ec n rc : V) :
    iomul (ocOadd ec n rc) = ocOadd (iadd (ocOadd 0 1 0) ec) n (iomul rc) := by
  set c := ocOadd ec n rc with hc
  have hpos : 0 < c := ocOadd_pos ec n rc
  obtain ⟨M, hM⟩ : ∃ M, c = M + 1 :=
    ⟨c - 1, (sub_add_self_of_le (pos_iff_one_le.mp hpos)).symm⟩
  have key : znth (iomulTable c) c = iomulNext c (iomulTable M) := by
    rw [hM, iomulTable_succ]
    have := znth_seqCons_self (iomulTable_seq M) (iomulNext (M + 1) (iomulTable M))
    rwa [iomulTable_lh] at this
  have htail : ocTail c ≤ M := by
    have := ocTail_lt ec n rc; rw [← hc] at this; exact le_iff_lt_succ.mpr (hM ▸ this)
  have hcne : c ≠ 0 := hpos.ne'
  rw [iomul, key, iomulNext, if_neg hcne,
    znth_iomulTable_eq_iomul M (ocTail c) htail, ocExp_ocOadd, ocCoeff_ocOadd, ocTail_ocOadd]

/-! ### `iC`-arithmetic of the slow-down (Rathjen Thm 3.5: multiplying by `ω` bumps `C` by ≤ 1) -/

/-- **`iC (1 + e) ≤ iC e + 1`** — left-adding `1` raises the max-coefficient by at most one
(internal `DescentCore.C_one_add_le`). `1 = ocOadd 0 1 0`; the addition only merges into the head
when `e`'s leading exponent is `0` (a finite head), bumping the head coefficient by `1`. -/
lemma iC_one_add (e : V) : iC (iadd (ocOadd 0 1 0) e) ≤ iC e + 1 := by
  rw [iadd_ocOadd]
  by_cases he : e = 0
  · subst he; simp [iC_ocOadd]
  · rw [if_neg he]
    by_cases hee : ocExp e = 0
    · have h2 : icmp 0 (ocExp e) = 1 := by rw [hee]; exact icmp_zero_zero
      have h1 : icmp 0 (ocExp e) ≠ 0 := by rw [h2]; exact _root_.one_ne_zero
      rw [if_neg h1, if_pos h2, iC_ocOadd, iC_zero]
      have hde : iC e = max (max (iC (ocExp e)) (ocCoeff e)) (iC (ocTail e)) := by
        rw [← iC_ocOadd, ocOadd_destruct he]
      have hcoeff : ocCoeff e ≤ iC e := by rw [hde]; exact le_max_of_le_left (le_max_right _ _)
      have htail : iC (ocTail e) ≤ iC e := by rw [hde]; exact le_max_right _ _
      refine max_le_iff.mpr ⟨max_le_iff.mpr ⟨?_, ?_⟩, ?_⟩
      · exact zero_le
      · rw [add_comm 1 (ocCoeff e)]; exact add_le_add hcoeff (le_refl 1)
      · exact le_trans htail le_self_add
    · have h0 : icmp 0 (ocExp e) = 0 :=
        (ocOadd_destruct hee) ▸
          icmp_zero_ocOadd (ocExp (ocExp e)) (ocCoeff (ocExp e)) (ocTail (ocExp e))
      rw [if_pos h0]
      exact le_self_add

/-- **`iC (ω·c) ≤ iC c + 1`** (Rathjen Thm 3.5; internal `DescentCore.C_omega_mul_le`). Strong
induction on the code: `ω·(oadd e n r) = oadd (1+e) n (ω·r)`, with `iC (1+e) ≤ iC e + 1` (`iC_one_add`)
and the IH on the tail `r`. -/
lemma iC_iomul (c : V) : iC (iomul c) ≤ iC c + 1 := by
  induction c using ISigma1.sigma1_order_induction
  · definability
  case ind c ih =>
    rcases eq_or_ne c 0 with hc | hc
    · subst hc; simp
    · obtain ⟨ee, ne, re, rfl⟩ : ∃ ee ne re, c = ocOadd ee ne re :=
        ⟨ocExp c, ocCoeff c, ocTail c, (ocOadd_destruct hc).symm⟩
      rw [iomul_ocOadd, iC_ocOadd, iC_ocOadd]
      have h1 : iC (iadd (ocOadd 0 1 0) ee) ≤ iC ee + 1 := iC_one_add ee
      have hre : re < ocOadd ee ne re := by
        have := ocTail_lt ee ne re; rwa [ocTail_ocOadd] at this
      have h2 : iC (iomul re) ≤ iC re + 1 := ih re hre
      set Mx := max (max (iC ee) ne) (iC re) with hMx
      have hee_le : iC ee ≤ Mx := le_max_of_le_left (le_max_left _ _)
      have hne_le : ne ≤ Mx := le_max_of_le_left (le_max_right _ _)
      have hre_le : iC re ≤ Mx := le_max_right _ _
      refine max_le_iff.mpr ⟨max_le_iff.mpr ⟨?_, ?_⟩, ?_⟩
      · exact le_trans h1 (add_le_add hee_le (le_refl 1))
      · exact le_trans hne_le le_self_add
      · exact le_trans h2 (add_le_add hre_le (le_refl 1))

/-! ### `icmp` reflexivity + the within-block descent of the slow-down -/

@[simp] lemma cmpV_self (a : V) : cmpV a a = 1 := by simp [cmpV]

/-- **`icmp a a = 1`** (reflexivity / equality of a code with itself). Structural induction: at an
`oadd` head the exponent and coefficient compare equal (`icmp e e = 1`, `cmpV n n = 1`) and `thenV`
passes through to the tail. -/
lemma icmp_self : ∀ w : V, ∀ a ≤ w, icmp a a = 1 := by
  intro w
  induction w using ISigma1.sigma1_order_induction
  · definability
  case ind w ih =>
    intro a haw
    rcases eq_or_ne a 0 with rfl | ha
    · exact icmp_zero_zero
    · obtain ⟨e, n, r, rfl⟩ : ∃ e n r, a = ocOadd e n r :=
        ⟨ocExp a, ocCoeff a, ocTail a, (ocOadd_destruct ha).symm⟩
      have he_lt : e < w := lt_of_lt_of_le (by have := ocExp_lt e n r; rwa [ocExp_ocOadd] at this) haw
      have hr_lt : r < w := lt_of_lt_of_le (by have := ocTail_lt e n r; rwa [ocTail_ocOadd] at this) haw
      rw [icmp_ocOadd, ih e he_lt e le_rfl, cmpV_self, ih r hr_lt r le_rfl]
      simp [thenV]

/-- `1 + e ≠ 0` on codes (internal `DescentCore.one_add_ne_zero`): left-adding `1` always leaves a
head term. Used to see that every leading exponent of `ω·c` is non-zero (so `ω·c` is `NoFin`). -/
lemma iadd_one_ne_zero (e : V) : iadd (ocOadd 0 1 0) e ≠ 0 := by
  rw [iadd_ocOadd]
  by_cases he : e = 0
  · rw [if_pos he]; exact (ocOadd_pos _ _ _).ne'
  · rw [if_neg he]
    by_cases hee : ocExp e = 0
    · have h2 : icmp 0 (ocExp e) = 1 := by rw [hee]; exact icmp_zero_zero
      have h1 : icmp 0 (ocExp e) ≠ 0 := by rw [h2]; exact _root_.one_ne_zero
      rw [if_neg h1, if_pos h2]; exact (ocOadd_pos _ _ _).ne'
    · have h0 : icmp 0 (ocExp e) = 0 := (ocOadd_destruct hee) ▸ icmp_zero_ocOadd _ _ _
      rw [if_pos h0]; exact he

/-- **`iC (ω·c + m) ≤ max (iC (ω·c)) m`** for a finite `m`-term `ocOadd 0 m 0` (internal
`DescentCore.C_add_ofNat_le`, specialized to the `NoFin` ordinal `ω·c`). Because every leading
exponent of `ω·c` is non-zero, the finite term lands as a fresh bottom summand and never merges into
an existing coefficient. With `iC_iomul` this gives `C(βₖ) ≤ k+1` for `βₖ = ω·αₖ + (K-i)`. -/
lemma iC_iadd_finite (c m : V) :
    iC (iadd (iomul c) (ocOadd 0 m 0)) ≤ max (iC (iomul c)) m := by
  induction c using ISigma1.sigma1_order_induction
  · definability
  case ind c ih =>
    rcases eq_or_ne c 0 with hc | hc
    · subst hc
      rw [iomul_zero, iadd_zero_left, iC_ocOadd, iC_zero]
      simp
    · obtain ⟨ee, ne, re, rfl⟩ : ∃ ee ne re, c = ocOadd ee ne re :=
        ⟨ocExp c, ocCoeff c, ocTail c, (ocOadd_destruct hc).symm⟩
      rw [iomul_ocOadd]
      set E := iadd (ocOadd 0 1 0) ee with hE
      have hEne : E ≠ 0 := iadd_one_ne_zero ee
      have hicmp : icmp E 0 = 2 := (ocOadd_destruct hEne) ▸ icmp_ocOadd_zero _ _ _
      have hre_lt : re < ocOadd ee ne re := by
        have := ocTail_lt ee ne re; rwa [ocTail_ocOadd] at this
      rw [iadd_ocOadd, if_neg (ocOadd_pos 0 m 0).ne', ocExp_ocOadd]
      rw [if_neg (by rw [hicmp]; exact _root_.two_ne_zero),
          if_neg (by rw [hicmp]; exact (one_lt_two).ne'), iC_ocOadd]
      -- gt-branch: ocOadd E ne (iadd (iomul re) (ocOadd 0 m 0))
      calc max (max (iC E) ne) (iC (iadd (iomul re) (ocOadd 0 m 0)))
          ≤ max (max (iC E) ne) (max (iC (iomul re)) m) :=
            max_le_max (le_refl _) (ih re hre_lt)
        _ = max (max (max (iC E) ne) (iC (iomul re))) m := (max_assoc _ _ _).symm
        _ = max (iC (ocOadd E ne (iomul re))) m := by rw [iC_ocOadd]

/-- **Within-block comparison of slow-down terms**: two `ω·α + (finite)` codes with the *same*
`ω·α` prefix compare exactly by their finite tails — `icmp (ω·α + p) (ω·α + q) = cmpV p q`. Structural
induction down the shared `ω·α` spine (`icmp E E = 1`, `cmpV n n = 1`, `thenV` passes through). -/
lemma icmp_iadd_iomul_finite (α p q : V) :
    icmp (iadd (iomul α) (ocOadd 0 p 0)) (iadd (iomul α) (ocOadd 0 q 0)) = cmpV p q := by
  induction α using ISigma1.sigma1_order_induction
  · definability
  case ind α ih =>
    rcases eq_or_ne α 0 with rfl | hα
    · rw [iomul_zero, iadd_zero_left, iadd_zero_left, icmp_ocOadd, icmp_zero_zero]
      by_cases hpq : cmpV p q = 1 <;> simp [thenV, hpq]
    · obtain ⟨e, n, r, rfl⟩ : ∃ e n r, α = ocOadd e n r :=
        ⟨ocExp α, ocCoeff α, ocTail α, (ocOadd_destruct hα).symm⟩
      rw [iomul_ocOadd]
      set E := iadd (ocOadd 0 1 0) e with hE
      have hEne : E ≠ 0 := iadd_one_ne_zero e
      have hic : icmp E 0 = 2 := (ocOadd_destruct hEne) ▸ icmp_ocOadd_zero _ _ _
      have hexpand : ∀ s : V, iadd (ocOadd E n (iomul r)) (ocOadd 0 s 0)
          = ocOadd E n (iadd (iomul r) (ocOadd 0 s 0)) := by
        intro s
        rw [iadd_ocOadd, if_neg (ocOadd_pos 0 s 0).ne', ocExp_ocOadd,
            if_neg (by rw [hic]; exact _root_.two_ne_zero),
            if_neg (by rw [hic]; exact (one_lt_two).ne')]
      have hr_lt : r < ocOadd e n r := by
        have := ocTail_lt e n r; rwa [ocTail_ocOadd] at this
      rw [hexpand p, hexpand q, icmp_ocOadd, icmp_self E E le_rfl, cmpV_self, ih r hr_lt]
      simp [thenV]

/-- **Within-block descent** (`DescentCore.repr_betaTail_within`, internal): a larger finite tail
gives a strictly `≺`-larger code, so `ω·α + p ≺ ω·α + (p+1)`. -/
lemma icmp_betaTail_within (α p : V) :
    icmp (iadd (iomul α) (ocOadd 0 p 0)) (iadd (iomul α) (ocOadd 0 (p + 1) 0)) = 0 := by
  rw [icmp_iadd_iomul_finite]; simp [cmpV]

/-! ### `1 + e` order-preservation (toward `icmp_iomul`, the boundary descent) -/

/-- Clean normal form of `1 + e` on codes: `ocOadd 0 1 0` if `e = 0`; the head coefficient bumped
by `1` if `e` has a finite head (`ocExp e = 0`); else `e` unchanged (the `1` is absorbed). -/
lemma iadd_one_eq (e : V) :
    iadd (ocOadd 0 1 0) e =
      (if e = 0 then ocOadd 0 1 0
       else if ocExp e = 0 then ocOadd 0 (1 + ocCoeff e) (ocTail e)
       else e) := by
  rw [iadd_ocOadd]
  by_cases he : e = 0
  · simp [he]
  · rw [if_neg he, if_neg he]
    by_cases hee : ocExp e = 0
    · have h2 : icmp 0 (ocExp e) = 1 := by rw [hee]; exact icmp_zero_zero
      rw [if_neg (by rw [h2]; exact _root_.one_ne_zero), if_pos h2, if_pos hee]
    · have h0 : icmp 0 (ocExp e) = 0 := (ocOadd_destruct hee) ▸ icmp_zero_ocOadd _ _ _
      rw [if_pos h0, if_neg hee]

@[simp] lemma ocExp_zero : ocExp (0 : V) = 0 := by
  have h : π₁ (0 : V) = 0 := by have := pi₁_pair (0 : V) 0; rwa [pair_zero_zero] at this
  simp [ocExp, fstIdx, h]

@[simp] lemma iadd_one_zero : iadd (ocOadd 0 1 0) (0 : V) = ocOadd 0 1 0 := by
  rw [iadd_one_eq]; simp

lemma iadd_one_fin {e : V} (he : e ≠ 0) (hf : ocExp e = 0) :
    iadd (ocOadd 0 1 0) e = ocOadd 0 (1 + ocCoeff e) (ocTail e) := by
  rw [iadd_one_eq, if_neg he, if_pos hf]

lemma iadd_one_inf {e : V} (hf : ocExp e ≠ 0) : iadd (ocOadd 0 1 0) e = e := by
  have he : e ≠ 0 := by rintro rfl; exact hf ocExp_zero
  rw [iadd_one_eq, if_neg he, if_neg hf]

/-- `cmpV (1+c₁) (1+c₂) = cmpV c₁ c₂` — left-adding `1` is order- and equality-preserving. -/
@[simp] lemma cmpV_one_add (c1 c2 : V) : cmpV (1 + c1) (1 + c2) = cmpV c1 c2 := by
  simp only [cmpV, add_lt_add_iff_left, add_right_inj]

lemma icmp_zero_pos {c : V} (hc : c ≠ 0) : icmp 0 c = 0 := by
  obtain ⟨e, n, r, rfl⟩ : ∃ e n r, c = ocOadd e n r := ⟨_, _, _, (ocOadd_destruct hc).symm⟩
  exact icmp_zero_ocOadd e n r

lemma icmp_pos_zero {c : V} (hc : c ≠ 0) : icmp c 0 = 2 := by
  obtain ⟨e, n, r, rfl⟩ : ∃ e n r, c = ocOadd e n r := ⟨_, _, _, (ocOadd_destruct hc).symm⟩
  exact icmp_ocOadd_zero e n r

/-- `icmp` of two positive codes, with the head pieces exposed (`icmp_ocOadd` + destructuring). -/
lemma icmp_pos_pos {a b : V} (ha : a ≠ 0) (hb : b ≠ 0) :
    icmp a b = thenV (icmp (ocExp a) (ocExp b))
      (thenV (cmpV (ocCoeff a) (ocCoeff b)) (icmp (ocTail a) (ocTail b))) := by
  obtain ⟨ea, ca, ta, rfl⟩ : ∃ x y z, a = ocOadd x y z := ⟨_, _, _, (ocOadd_destruct ha).symm⟩
  obtain ⟨eb, cb, tb, rfl⟩ : ∃ x y z, b = ocOadd x y z := ⟨_, _, _, (ocOadd_destruct hb).symm⟩
  rw [icmp_ocOadd]; simp only [ocExp_ocOadd, ocCoeff_ocOadd, ocTail_ocOadd]

/-- **A strictly smaller leading exponent decides `≺`** (head version): if `b` is positive and its
leading exponent is `≺ e`, then `b ≺ ω^e·n + r` outright. -/
lemma icmp_pos_ocOadd_lt_exp {b e n r : V} (hb : b ≠ 0) (h : icmp (ocExp b) e = 0) :
    icmp b (ocOadd e n r) = 0 := by
  conv_lhs => rw [← ocOadd_destruct hb]
  rw [icmp_ocOadd, h]; simp [thenV]

/-- **`icmp` is antisymmetric through `oswap`** (auxiliary, on a pair index): comparison swaps its
arguments by swapping `lt`↔`gt`. Strong induction on the pair `m = ⟪c1,c2⟫`: at the both-positive
head it is the lexicographic combine of (exponent, coefficient, tail) comparisons, each of which
swaps by the IH (`oswap` is a `thenV`-homomorphism). -/
lemma icmp_swap_aux : ∀ m : V, icmp (π₂ m) (π₁ m) = oswap (icmp (π₁ m) (π₂ m)) := by
  intro m
  induction m using ISigma1.sigma1_order_induction
  · definability
  case ind m IH =>
    have hm : (⟪π₁ m, π₂ m⟫ : V) = m := pair_unpair m
    rcases eq_or_ne (π₁ m) 0 with ha | ha
    · rcases eq_or_ne (π₂ m) 0 with hb | hb
      · rw [ha, hb, icmp_zero_zero]; simp
      · rw [ha, icmp_zero_pos hb, icmp_pos_zero hb]; simp
    · rcases eq_or_ne (π₂ m) 0 with hb | hb
      · rw [hb, icmp_pos_zero ha, icmp_zero_pos ha]; simp
      · rw [icmp_pos_pos ha hb, icmp_pos_pos hb ha]
        have hexp : (⟪ocExp (π₁ m), ocExp (π₂ m)⟫ : V) < m := by
          have h := pair_lt_pair (ocExp_lt_of_pos (pos_iff_ne_zero.mpr ha))
            (ocExp_lt_of_pos (pos_iff_ne_zero.mpr hb))
          rwa [hm] at h
        have htail : (⟪ocTail (π₁ m), ocTail (π₂ m)⟫ : V) < m := by
          have h := pair_lt_pair (ocTail_lt_of_pos (pos_iff_ne_zero.mpr ha))
            (ocTail_lt_of_pos (pos_iff_ne_zero.mpr hb))
          rwa [hm] at h
        have he := IH _ hexp
        have ht := IH _ htail
        simp only [pi₁_pair, pi₂_pair] at he ht
        rw [he, ht, cmpV_swap, oswap_thenV, oswap_thenV]

/-- **`icmp` antisymmetry**: `icmp c2 c1 = oswap (icmp c1 c2)` (lt↔gt swap, eq fixed). -/
lemma icmp_swap (c1 c2 : V) : icmp c2 c1 = oswap (icmp c1 c2) := by
  have := icmp_swap_aux ⟪c1, c2⟫
  simpa using this

lemma oswap_eq_two {x : V} : oswap x = 2 ↔ x = 0 := by
  rcases eq_or_ne x 0 with rfl | h0
  · simp
  · rcases eq_or_ne x 2 with rfl | h2
    · simp
    · rw [oswap, if_neg h0, if_neg h2]; exact ⟨fun h => absurd h h2, fun h => absurd h h0⟩

/-- `icmp a b = 2 ⟺ icmp b a = 0` (the `≻`/`≺` antisymmetry, the direction the clean-append
boundary descent needs). -/
lemma icmp_two_iff_swap_zero {a b : V} : icmp a b = 2 ↔ icmp b a = 0 := by
  rw [icmp_swap b a, oswap_eq_two]

/-- A finite-head code (`ocExp a = 0`) is `≺` an infinite-head code (`ocExp b ≠ 0`). -/
lemma icmp_finHead_infHead {a b : V} (ha : a ≠ 0) (hb : b ≠ 0)
    (hfa : ocExp a = 0) (hfb : ocExp b ≠ 0) : icmp a b = 0 := by
  obtain ⟨ea, ca, ta, rfl⟩ : ∃ x y z, a = ocOadd x y z := ⟨_, _, _, (ocOadd_destruct ha).symm⟩
  obtain ⟨eb, cb, tb, rfl⟩ : ∃ x y z, b = ocOadd x y z := ⟨_, _, _, (ocOadd_destruct hb).symm⟩
  rw [ocExp_ocOadd] at hfa hfb
  subst hfa
  rw [icmp_ocOadd, icmp_zero_pos hfb]; simp [thenV]

/-- An infinite-head code (`ocExp a ≠ 0`) is `≻` a finite-head code (`ocExp b = 0`). -/
lemma icmp_infHead_finHead {a b : V} (ha : a ≠ 0) (hb : b ≠ 0)
    (hfa : ocExp a ≠ 0) (hfb : ocExp b = 0) : icmp a b = 2 := by
  obtain ⟨ea, ca, ta, rfl⟩ : ∃ x y z, a = ocOadd x y z := ⟨_, _, _, (ocOadd_destruct ha).symm⟩
  obtain ⟨eb, cb, tb, rfl⟩ : ∃ x y z, b = ocOadd x y z := ⟨_, _, _, (ocOadd_destruct hb).symm⟩
  rw [ocExp_ocOadd] at hfa hfb
  subst hfb
  rw [icmp_ocOadd, icmp_pos_zero hfa]; simp [thenV]

/-- **Finite-threshold monotonicity** (avoids a general `icmp` transitivity): a code that strictly
dominates the finite code `ω^0·l` also dominates every smaller finite code `ω^0·j` (`j ≤ l`).
Concrete case split on the dominating code's head: an infinite head dominates any finite code
outright; a finite head dominates by its (larger) coefficient/tail, which the `ℕ`-order carries
down to `j`. Used to weaken the `MinExpGe` threshold from the level `l` down to `ocExp g` when
`g < ω^(l+1)` (g's exponent is a finite code `⪯ ω^0·l`). -/
lemma icmp_finThresh_mono {s l j : V} (hsl : icmp s (ocOadd 0 l 0) = 2) (hjl : j ≤ l) :
    icmp s (ocOadd 0 j 0) = 2 := by
  have hs0 : s ≠ 0 := by
    rintro rfl
    rcases eq_or_ne (ocOadd 0 l 0 : V) 0 with h | h
    · rw [h, icmp_zero_zero] at hsl; exact (one_lt_two).ne hsl
    · rw [icmp_zero_pos h] at hsl; exact (two_ne_zero).symm hsl
  obtain ⟨es, cs, ts, rfl⟩ : ∃ es cs ts, s = ocOadd es cs ts :=
    ⟨ocExp s, ocCoeff s, ocTail s, (ocOadd_destruct hs0).symm⟩
  rw [icmp_ocOadd es cs ts 0 l 0] at hsl
  rw [icmp_ocOadd es cs ts 0 j 0]
  rcases eq_or_ne es 0 with hes | hes
  · -- finite head: the decision is `cmpV cs ·` then the tail
    subst hes
    rw [icmp_zero_zero, thenV_one_left] at hsl ⊢
    -- hsl : thenV (cmpV cs l) (icmp ts 0) = 2 ; goal same with j
    rcases lt_trichotomy cs l with hcl | hcl | hcl
    · -- cs < l : premise forces thenV = 0, contradiction
      rw [show cmpV cs l = 0 by rw [cmpV, if_pos hcl], thenV_zero_left] at hsl
      exact absurd hsl (two_ne_zero).symm
    · -- cs = l : ties at l, premise needs icmp ts 0 = 2 (ts ≠ 0)
      rw [show cmpV cs l = 1 by rw [cmpV, if_neg (not_lt.mpr hcl.ge), if_pos hcl], thenV_one_left]
        at hsl
      rcases lt_or_eq_of_le hjl with hjlt | hje
      · rw [show cmpV cs j = 2 by
          rw [cmpV, if_neg (not_lt.mpr (hcl ▸ hjlt.le)), if_neg (hcl ▸ hjlt.ne')]]
        simp [thenV]
      · rw [show cmpV cs j = 1 by rw [cmpV, if_neg (not_lt.mpr (hje ▸ hcl.ge)),
          if_pos (hcl.trans hje.symm)], thenV_one_left]
        exact hsl
    · -- cs > l ≥ j : dominates outright at the coefficient
      have hcj : j < cs := lt_of_le_of_lt hjl hcl
      rw [show cmpV cs j = 2 by rw [cmpV, if_neg (not_lt.mpr hcj.le), if_neg hcj.ne']]
      simp [thenV]
  · -- infinite head: dominates any finite code
    rw [icmp_pos_zero hes, thenV, if_neg (one_lt_two).ne']

/-- **`1 + ·` preserves the code comparison** for NF exponents: `icmp (1+e₁) (1+e₂) = icmp e₁ e₂`.
The crux of `icmp_iomul`. NF is needed: with a zero coefficient the finite-head bump could spuriously
tie. Nine-way case split on the head kinds (zero / finite-head / infinite-head) of `e₁`, `e₂`. -/
lemma icmp_one_add {e1 e2 : V} (h1 : isNF e1) (h2 : isNF e2) :
    icmp (iadd (ocOadd 0 1 0) e1) (iadd (ocOadd 0 1 0) e2) = icmp e1 e2 := by
  have hbump : ∀ {e : V}, isNF e → e ≠ 0 → ocExp e = 0 → (1 : V) < 1 + ocCoeff e := by
    intro e he hne _
    exact lt_add_of_pos_right 1 (pos_iff_ne_zero.mpr (coeff_ne_zero he hne))
  by_cases hz1 : e1 = 0 <;> by_cases hz2 : e2 = 0
  · subst hz1; subst hz2
    simp only [iadd_one_zero, icmp_zero_zero]; exact icmp_self _ _ le_rfl
  · subst hz1
    by_cases hf2 : ocExp e2 = 0
    · rw [iadd_one_zero, iadd_one_fin hz2 hf2,
        icmp_ocOadd 0 1 0 0 (1 + ocCoeff e2) (ocTail e2), icmp_zero_zero, icmp_zero_pos hz2]
      have hlt := hbump h2 hz2 hf2
      have : cmpV 1 (1 + ocCoeff e2) = 0 := by simp [cmpV, hlt]
      rw [this]; simp [thenV]
    · rw [iadd_one_zero, iadd_one_inf hf2, icmp_zero_pos hz2,
        icmp_finHead_infHead (ocOadd_pos 0 1 0).ne' hz2 (ocExp_ocOadd 0 1 0) hf2]
  · subst hz2
    by_cases hf1 : ocExp e1 = 0
    · rw [iadd_one_zero, iadd_one_fin hz1 hf1,
        icmp_ocOadd 0 (1 + ocCoeff e1) (ocTail e1) 0 1 0, icmp_zero_zero, icmp_pos_zero hz1]
      have hlt := hbump h1 hz1 hf1
      have : cmpV (1 + ocCoeff e1) 1 = 2 := by
        simp [cmpV, not_lt.mpr (le_of_lt hlt), (ne_of_lt hlt).symm]
      rw [this]; simp [thenV]
    · rw [iadd_one_zero, iadd_one_inf hf1, icmp_pos_zero hz1,
        icmp_infHead_finHead hz1 (ocOadd_pos 0 1 0).ne' hf1 (ocExp_ocOadd 0 1 0)]
  · by_cases hf1 : ocExp e1 = 0 <;> by_cases hf2 : ocExp e2 = 0
    · rw [iadd_one_fin hz1 hf1, iadd_one_fin hz2 hf2,
        icmp_ocOadd 0 (1 + ocCoeff e1) (ocTail e1) 0 (1 + ocCoeff e2) (ocTail e2), cmpV_one_add,
        icmp_pos_pos hz1 hz2, hf1, hf2]
    · rw [iadd_one_fin hz1 hf1, iadd_one_inf hf2,
        icmp_finHead_infHead (ocOadd_pos _ _ _).ne' hz2 (ocExp_ocOadd 0 _ _) hf2,
        icmp_finHead_infHead hz1 hz2 hf1 hf2]
    · rw [iadd_one_inf hf1, iadd_one_fin hz2 hf2,
        icmp_infHead_finHead hz1 (ocOadd_pos _ _ _).ne' hf1 (ocExp_ocOadd 0 _ _),
        icmp_infHead_finHead hz1 hz2 hf1 hf2]
    · rw [iadd_one_inf hf1, iadd_one_inf hf2]

/-- `ω·c ≠ 0` for a positive code `c` (the head term survives the exponent bump). -/
lemma iomul_ne_zero {c : V} (hc : c ≠ 0) : iomul c ≠ 0 := by
  obtain ⟨e, n, r, rfl⟩ : ∃ e n r, c = ocOadd e n r := ⟨_, _, _, (ocOadd_destruct hc).symm⟩
  rw [iomul_ocOadd]; exact (ocOadd_pos _ _ _).ne'

/-- **`ω·` preserves the code comparison** on NF codes (auxiliary, bounded form):
`icmp (ω·a) (ω·b) = icmp a b`. Structural induction down the shared spine — at each `oadd` head the
exponents `e ↦ 1+e` compare identically (`icmp_one_add`, needs the exponents NF) and the coefficients
are untouched, so `thenV` passes the decision to the tails (IH). -/
private theorem icmp_iomul_aux :
    ∀ w : V, ∀ a ≤ w, ∀ b ≤ w, isNF a → isNF b → icmp (iomul a) (iomul b) = icmp a b := by
  intro w
  induction w using ISigma1.sigma1_order_induction
  · definability
  case ind w ih =>
    intro a haw b hbw ha hb
    rcases eq_or_ne a 0 with rfl | hane
    · rcases eq_or_ne b 0 with rfl | hbne
      · simp
      · rw [iomul_zero, icmp_zero_pos (iomul_ne_zero hbne), icmp_zero_pos hbne]
    · rcases eq_or_ne b 0 with rfl | hbne
      · rw [iomul_zero, icmp_pos_zero (iomul_ne_zero hane), icmp_pos_zero hane]
      · obtain ⟨ea, ca, ta, rfl⟩ : ∃ e n r, a = ocOadd e n r :=
          ⟨_, _, _, (ocOadd_destruct hane).symm⟩
        obtain ⟨eb, cb, tb, rfl⟩ : ∃ e n r, b = ocOadd e n r :=
          ⟨_, _, _, (ocOadd_destruct hbne).symm⟩
        obtain ⟨_, hnea, hnta, _⟩ := (isNF_ocOadd ea ca ta).1 ha
        obtain ⟨_, hneb, hntb, _⟩ := (isNF_ocOadd eb cb tb).1 hb
        have hta_w : ta < w := code_lt_of_tail haw
        have htb_w : tb < w := code_lt_of_tail hbw
        rw [iomul_ocOadd, iomul_ocOadd, icmp_ocOadd, icmp_ocOadd, icmp_one_add hnea hneb,
          ih (max ta tb) (max_lt hta_w htb_w) ta (le_max_left _ _) tb (le_max_right _ _) hnta hntb]

/-- **`ω·` preserves the code comparison** on NF codes (`DescentCore.repr_omega_mul_mono`, internal):
`icmp (ω·a) (ω·b) = icmp a b`. The order-preservation of the Rathjen §3 slow-down across blocks. -/
lemma icmp_iomul {a b : V} (ha : isNF a) (hb : isNF b) :
    icmp (iomul a) (iomul b) = icmp a b :=
  icmp_iomul_aux (max a b) a (le_max_left _ _) b (le_max_right _ _) ha hb

/-! ### Boundary descent of the slow-down (`ω·α + finite` across distinct blocks) -/

/-- Appending a finite term `+ m` to `ω·(oadd e n r)` walks down the NoFin spine: the head `(1+e, n)`
is untouched and the recursion continues into the tail. (The finite term lands as a fresh bottom
summand because every leading exponent `1+e` of `ω·c` is non-zero.) -/
lemma iadd_iomul_ocOadd_finite (e n r s : V) :
    iadd (iomul (ocOadd e n r)) (ocOadd 0 s 0)
      = ocOadd (iadd (ocOadd 0 1 0) e) n (iadd (iomul r) (ocOadd 0 s 0)) := by
  rw [iomul_ocOadd]
  set E := iadd (ocOadd 0 1 0) e with hE
  have hEne : E ≠ 0 := iadd_one_ne_zero e
  have hic : icmp E 0 = 2 := (ocOadd_destruct hEne) ▸ icmp_ocOadd_zero _ _ _
  rw [iadd_ocOadd, if_neg (ocOadd_pos 0 s 0).ne', ocExp_ocOadd,
      if_neg (by rw [hic]; exact _root_.two_ne_zero),
      if_neg (by rw [hic]; exact (one_lt_two).ne')]

/-- `thenV` propagates a `≺` (value `0`) decision monotonically through a fixed two-level head: if the
nested comparison `thenV x (thenV y u) = 0` and the innermost `u = 0` forces `v = 0`, then
`thenV x (thenV y v) = 0`. The head levels (`x`, `y`) are shared, so either they already decide `0`
or the decision descends to the innermost slot. -/
lemma thenV_zero_mono {x y u v : V} (huv : u = 0 → v = 0)
    (h : thenV x (thenV y u) = 0) : thenV x (thenV y v) = 0 := by
  rw [thenV_eq_zero] at h ⊢
  rcases h with hx | ⟨hx, hyu⟩
  · exact Or.inl hx
  · refine Or.inr ⟨hx, ?_⟩
    rw [thenV_eq_zero] at hyu ⊢
    rcases hyu with hy | ⟨hy, hu⟩
    · exact Or.inl hy
    · exact Or.inr ⟨hy, huv hu⟩

/-- **Boundary descent** (auxiliary, bounded form): if `ω·a ≺ ω·b` then appending arbitrary finite
tails preserves the strict order — `ω·a + s ≺ ω·b + t`. The decision is reached on the NoFin spine
(via `icmp_iomul`/the head comparison) before the finite tails matter; `thenV_zero_mono` carries it. -/
private theorem icmp_iadd_finite_mono (s t : V) :
    ∀ w : V, ∀ a ≤ w, ∀ b ≤ w, isNF a → isNF b →
      icmp (iomul a) (iomul b) = 0 →
      icmp (iadd (iomul a) (ocOadd 0 s 0)) (iadd (iomul b) (ocOadd 0 t 0)) = 0 := by
  intro w
  induction w using ISigma1.sigma1_order_induction
  · definability
  case ind w ih =>
    intro a haw b hbw ha hb hlt
    rcases eq_or_ne a 0 with rfl | hane
    · rcases eq_or_ne b 0 with rfl | hbne
      · rw [iomul_zero, icmp_zero_zero] at hlt; exact absurd hlt _root_.one_ne_zero
      · obtain ⟨eb, cb, tb, rfl⟩ : ∃ e n r, b = ocOadd e n r :=
          ⟨_, _, _, (ocOadd_destruct hbne).symm⟩
        rw [iomul_zero, iadd_zero_left, iadd_iomul_ocOadd_finite]
        exact icmp_finHead_infHead (ocOadd_pos 0 s 0).ne' (ocOadd_pos _ _ _).ne'
          (ocExp_ocOadd 0 s 0) (by rw [ocExp_ocOadd]; exact iadd_one_ne_zero eb)
    · rcases eq_or_ne b 0 with rfl | hbne
      · rw [iomul_zero, icmp_pos_zero (iomul_ne_zero hane)] at hlt
        exact absurd hlt _root_.two_ne_zero
      · obtain ⟨ea, ca, ta, rfl⟩ : ∃ e n r, a = ocOadd e n r :=
          ⟨_, _, _, (ocOadd_destruct hane).symm⟩
        obtain ⟨eb, cb, tb, rfl⟩ : ∃ e n r, b = ocOadd e n r :=
          ⟨_, _, _, (ocOadd_destruct hbne).symm⟩
        rw [iadd_iomul_ocOadd_finite, iadd_iomul_ocOadd_finite, icmp_ocOadd]
        rw [iomul_ocOadd, iomul_ocOadd, icmp_ocOadd] at hlt
        refine thenV_zero_mono ?_ hlt
        intro htail
        obtain ⟨_, hnea, hnta, _⟩ := (isNF_ocOadd ea ca ta).1 ha
        obtain ⟨_, hneb, hntb, _⟩ := (isNF_ocOadd eb cb tb).1 hb
        exact ih (max ta tb) (max_lt (code_lt_of_tail haw) (code_lt_of_tail hbw))
          ta (le_max_left _ _) tb (le_max_right _ _) hnta hntb htail

/-- **Boundary descent of the slow-down** (`DescentCore.repr_betaTail_boundary`, internal): when the
prefixes descend (`a ≺ b` as NF codes), the slowed-down terms descend regardless of their finite
tails — `ω·a + s ≺ ω·b + t`. Built on `icmp_iomul` (the block comparison reduces to `icmp a b`). -/
lemma icmp_betaTail_boundary {a b : V} (ha : isNF a) (hb : isNF b)
    (hab : icmp a b = 0) (s t : V) :
    icmp (iadd (iomul a) (ocOadd 0 s 0)) (iadd (iomul b) (ocOadd 0 t 0)) = 0 :=
  icmp_iadd_finite_mono s t (max a b) a (le_max_left _ _) b (le_max_right _ _) ha hb
    (by rw [icmp_iomul ha hb]; exact hab)

/-! ### `isNF` preservation for the slow-down (`ω·α` and `ω·α + finite`) -/

/-- `icmp y 0 ∈ {1, 2}`: nothing is `≺ 0`. -/
lemma icmp_right_zero_ne_zero (y : V) : icmp y 0 ≠ 0 := by
  rcases eq_or_ne y 0 with rfl | hy
  · rw [icmp_zero_zero]; exact _root_.one_ne_zero
  · rw [icmp_pos_zero hy]; exact _root_.two_ne_zero

/-- An NF code with a *finite* head (`ocExp e = 0`) has an empty tail: the NF tail-condition
`icmp (ocExp (ocTail e)) (ocExp e) = 0` is unsatisfiable when `ocExp e = 0` (nothing is `≺ 0`). -/
private lemma finHead_NF_tail_zero {e : V} (he : isNF e) (hne : e ≠ 0) (hf : ocExp e = 0) :
    ocTail e = 0 := by
  have h := (isNF_ocOadd (ocExp e) (ocCoeff e) (ocTail e)).1 (by rw [ocOadd_destruct hne]; exact he)
  rcases h.2.2.2 with h0 | h0
  · exact h0
  · rw [hf] at h0; exact absurd h0 (icmp_right_zero_ne_zero _)

/-- **`1 + e` is NF when `e` is** — the exponent bump of the slow-down preserves normal form. (For a
finite-head `e` the tail is empty, so the bump just raises the lone coefficient; for an infinite head
the `1` is absorbed.) -/
lemma isNF_iadd_one {e : V} (he : isNF e) : isNF (iadd (ocOadd 0 1 0) e) := by
  rcases eq_or_ne e 0 with rfl | hne
  · rw [iadd_one_zero]
    exact (isNF_ocOadd 0 1 0).2 ⟨_root_.one_ne_zero, isNF_zero, isNF_zero, Or.inl rfl⟩
  · by_cases hf : ocExp e = 0
    · rw [iadd_one_fin hne hf]
      have htail0 : ocTail e = 0 := finHead_NF_tail_zero he hne hf
      refine (isNF_ocOadd 0 _ _).2 ⟨(lt_of_lt_of_le one_pos le_self_add).ne', isNF_zero, ?_, ?_⟩
      · rw [htail0]; exact isNF_zero
      · rw [htail0]; exact Or.inl rfl
    · rw [iadd_one_inf hf]; exact he

/-- **`ω·c` is NF when `c` is** (auxiliary, bounded). Every leading exponent `e ↦ 1+e` stays NF
(`isNF_iadd_one`) and strictly decreasing (`icmp_one_add` on the NF tail-condition of `c`). -/
private lemma isNF_iomul_aux : ∀ w : V, ∀ c ≤ w, isNF c → isNF (iomul c) := by
  intro w
  induction w using ISigma1.sigma1_order_induction
  · definability
  case ind w ih =>
    intro c hcw hc
    rcases eq_or_ne c 0 with rfl | hcne
    · rw [iomul_zero]; exact isNF_zero
    · obtain ⟨e, n, r, rfl⟩ : ∃ e n r, c = ocOadd e n r := ⟨_, _, _, (ocOadd_destruct hcne).symm⟩
      obtain ⟨hn, hne, hnr, htc⟩ := (isNF_ocOadd e n r).1 hc
      rw [iomul_ocOadd]
      refine (isNF_ocOadd _ _ _).2 ⟨hn, isNF_iadd_one hne, ih r (code_lt_of_tail hcw) r le_rfl hnr, ?_⟩
      rcases eq_or_ne r 0 with rfl | hrne
      · left; exact iomul_zero
      · right
        have hexp : ocExp (iomul r) = iadd (ocOadd 0 1 0) (ocExp r) := by
          obtain ⟨er, nr, rr, hrdef⟩ : ∃ x y z, r = ocOadd x y z :=
            ⟨_, _, _, (ocOadd_destruct hrne).symm⟩
          rw [hrdef, iomul_ocOadd, ocExp_ocOadd, ocExp_ocOadd]
        rw [hexp, icmp_one_add (isNF_ocExp hnr hrne) hne]
        exact htc.resolve_left hrne

/-- **`ω·c` is NF when `c` is** (Rathjen §3 slow-down preserves normal form). -/
lemma isNF_iomul {c : V} (hc : isNF c) : isNF (iomul c) :=
  isNF_iomul_aux c c le_rfl hc

/-- **`ω·α + m` is NF** for NF `α` and a positive finite `m` (auxiliary, bounded). The finite term
`ocOadd 0 m 0` lands as a fresh bottom summand: its head exponent `0` is `≺` the non-zero head
exponent `1 + ocExp r` of the block above it (`icmp_zero_pos`). -/
private lemma isNF_iadd_finite_aux (m : V) (hm : m ≠ 0) :
    ∀ w : V, ∀ α ≤ w, isNF α → isNF (iadd (iomul α) (ocOadd 0 m 0)) := by
  intro w
  induction w using ISigma1.sigma1_order_induction
  · definability
  case ind w ih =>
    intro α hαw hα
    rcases eq_or_ne α 0 with rfl | hαne
    · rw [iomul_zero, iadd_zero_left]
      exact (isNF_ocOadd 0 m 0).2 ⟨hm, isNF_zero, isNF_zero, Or.inl rfl⟩
    · obtain ⟨e, n, r, rfl⟩ : ∃ e n r, α = ocOadd e n r := ⟨_, _, _, (ocOadd_destruct hαne).symm⟩
      obtain ⟨hn, hne, hnr, htc⟩ := (isNF_ocOadd e n r).1 hα
      rw [iadd_iomul_ocOadd_finite]
      refine (isNF_ocOadd _ _ _).2 ⟨hn, isNF_iadd_one hne, ih r (code_lt_of_tail hαw) r le_rfl hnr, ?_⟩
      right
      rcases eq_or_ne r 0 with rfl | hrne
      · rw [iomul_zero, iadd_zero_left, ocExp_ocOadd]
        exact icmp_zero_pos (iadd_one_ne_zero e)
      · have hexp : ocExp (iadd (iomul r) (ocOadd 0 m 0)) = iadd (ocOadd 0 1 0) (ocExp r) := by
          obtain ⟨er, nr, rr, hrdef⟩ : ∃ x y z, r = ocOadd x y z :=
            ⟨_, _, _, (ocOadd_destruct hrne).symm⟩
          rw [hrdef, iadd_iomul_ocOadd_finite, ocExp_ocOadd, ocExp_ocOadd]
        rw [hexp, icmp_one_add (isNF_ocExp hnr hrne) hne]
        exact htc.resolve_left hrne

/-- **`ω·α + m` is NF** for NF `α` and positive finite `m` — the slow-down term `βₖ` is a valid
notation. -/
lemma isNF_iadd_finite {α m : V} (hα : isNF α) (hm : m ≠ 0) :
    isNF (iadd (iomul α) (ocOadd 0 m 0)) :=
  isNF_iadd_finite_aux m hm α α le_rfl hα

end GoodsteinPA.InternalONote
