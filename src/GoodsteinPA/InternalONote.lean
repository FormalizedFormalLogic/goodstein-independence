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

namespace GoodsteinPA.InternalONote

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

end GoodsteinPA.InternalONote
