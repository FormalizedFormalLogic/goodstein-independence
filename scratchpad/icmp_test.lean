import GoodsteinPA.InternalONote

namespace GoodsteinPA.InternalONote
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.HierarchySymbol
variable {V : Type*} [ORingStructure V] [V ⊧ₘ* 𝗜𝚺₁]

/-- `Ordering.then` on ordering codes (lt=0, eq=1, gt=2): take `a` unless `a = eq`. -/
noncomputable def thenV (a b : V) : V := if a = 1 then b else a

def _root_.LO.FirstOrder.Arithmetic.thenVDef : 𝚺₀.Semisentence 3 := .mkSigma
  “y a b. (a = 1 ∧ y = b) ∨ (a ≠ 1 ∧ y = a)”

instance thenV_defined : 𝚺₀-Function₂ (thenV : V → V → V) via thenVDef := .mk fun v ↦ by
  simp [thenVDef, thenV]
  by_cases h : v 1 = 1 <;> simp [h]

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
  simp only [hpos1.ne', hpos2.ne', if_false, ite_false]
  rw [icmpMain, hpi1, hpi2,
    znth_icmpTable_eq_icmp M _ hexple, znth_icmpTable_eq_icmp M _ htaille]
  simp only [pi₁_pair, pi₂_pair, ocExp_ocOadd, ocCoeff_ocOadd, ocTail_ocOadd, hc1, hc2]

end GoodsteinPA.InternalONote
