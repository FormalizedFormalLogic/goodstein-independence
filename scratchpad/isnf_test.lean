import GoodsteinPA.InternalONote

namespace GoodsteinPA.InternalONote
open Classical
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.HierarchySymbol
variable {V : Type*} [ORingStructure V] [V ⊧ₘ* 𝗜𝚺₁]

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
