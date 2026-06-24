/-
# `wip/InternalNadd.lean` — internal natural (Hessenberg) sum `inadd` on CNF codes

**Status: wip brick for crux 2 (lap 58+).** Buchholz's pre-ordinal `õ` (§4 ordinal assignment,
`CRUX2-ORD-ASSIGNMENT-2026-06-24.md`) uses the **natural sum** `#`:
`õ(K d0…dl) = ω^{õ(d0)} # … # ω^{õ(dl)}`. `iadd` (ordinary ordinal `+`) absorbs smaller leading
terms, so it is NOT the natural sum. This file builds the genuine `#` on `InternalONote` CNF codes.

Natural sum factors into two single-argument course-of-values recursions (mirroring `iomul`/`iadd`):
* `insTerm e n b` — insert the single term `ω^e·n` into the NF code `b` (combine on equal exponent,
  place in `≺`-order). Recursion on `b`.
* `inadd a b = insTerm (ocExp a) (ocCoeff a) (inadd (ocTail a) b)` — fold the leading terms of `a`
  into `b`. Recursion on `a`.

Equational core only (this lap). The NF/`icmp`/`iC` property lemmas (the `# `-commutativity, NF
preservation, `iC (a # b) ≤ iC a + iC b`, descent monotonicity) are the next bricks; once those land,
promote to `src/`. `icmp` convention: `0`=lt, `1`=eq, `2`=gt (`cmpV`).
-/
import GoodsteinPA.InternalONote

namespace GoodsteinPA.InternalONote

open Classical
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.HierarchySymbol ISigma1 PeanoMinus
open GoodsteinPA.InternalPow

variable {V : Type*} [ORingStructure V] [V ⊧ₘ* 𝗜𝚺₁]

/-! ## `insTerm e n b` — insert `ω^e·n` into the NF code `b` (recursion on `b`) -/

/-- Table step of `insTerm` at code index `c` (params `e n`, table `s` of `insTerm e n ·`). -/
noncomputable def insTermNext (e n c s : V) : V :=
  if c = 0 then ocOadd e n 0
  else if icmp e (ocExp c) = 2 then ocOadd e n c
  else if icmp e (ocExp c) = 1 then ocOadd e (n + ocCoeff c) (ocTail c)
  else ocOadd (ocExp c) (ocCoeff c) (znth s (ocTail c))

def _root_.LO.FirstOrder.Arithmetic.insTermNextDef : 𝚺₁.Semisentence 5 := .mkSigma
  “y e n c s.
    (c = 0 ∧ !ocOaddDef y e n 0)
  ∨ (c ≠ 0 ∧ ∃ ex, !ocExpDef ex c ∧ ∃ cm, !icmpDef cm e ex ∧
       ( (cm = 2 ∧ !ocOaddDef y e n c)
       ∨ (cm ≠ 2 ∧ cm = 1 ∧ ∃ cc, !ocCoeffDef cc c ∧ ∃ t, !sndIdxDef t c ∧
            !ocOaddDef y e (n + cc) t)
       ∨ (cm ≠ 2 ∧ cm ≠ 1 ∧ ∃ cc, !ocCoeffDef cc c ∧ ∃ t, !sndIdxDef t c ∧
            ∃ st, !znthDef st s t ∧ !ocOaddDef y ex cc st) ) )”

instance insTermNext_defined : 𝚺₁-Function₄ (insTermNext : V → V → V → V → V) via insTermNextDef := .mk
  fun v ↦ by
  simp [insTermNextDef, insTermNext, ocExp_defined.iff, ocCoeff_defined.iff, ocTail,
    sndIdx_defined.iff, icmp_defined.iff, znth_defined.iff, ocOadd_defined.iff]
  by_cases hc : v 3 = 0
  · simp [hc]
  · by_cases h2 : icmp (v 1) (ocExp (v 3)) = 2
    · simp [hc, h2]
    · by_cases h1 : icmp (v 1) (ocExp (v 3)) = 1
      · simp [hc, h2, h1]
      · simp [hc, h2, h1]

instance insTermNext_definable : 𝚺₁-Function₄ (insTermNext : V → V → V → V → V) :=
  insTermNext_defined.to_definable

/-- Blueprint for the `insTerm` table (params = `e`, `n`). -/
def insTermTable.blueprint : PR.Blueprint 2 where
  zero := .mkSigma “y e n. ∃ z, !ocOaddDef z e n 0 ∧ !mkSeq₁Def y z”
  succ := .mkSigma “y ih i e n. ∃ v, !insTermNextDef v e n (i + 1) ih ∧ !seqConsDef y ih v”

noncomputable def insTermTable.construction : PR.Construction V insTermTable.blueprint where
  zero := fun x ↦ !⟦ocOadd (x 0) (x 1) 0⟧
  succ := fun x i ih ↦ seqCons ih (insTermNext (x 0) (x 1) (i + 1) ih)
  zero_defined := .mk fun v ↦ by
    simp [insTermTable.blueprint, mkSeq₁Def, seqCons_defined.iff, emptyset_def, ocOadd_defined.iff]
  succ_defined := .mk fun v ↦ by
    simp [insTermTable.blueprint, insTermNext_defined.iff, seqCons_defined.iff]

/-- The `insTerm` table: `insTermTable e n N = ⟨insTerm e n 0,…,insTerm e n N⟩`. -/
noncomputable def insTermTable (e n c : V) : V := insTermTable.construction.result ![e, n] c

@[simp] lemma insTermTable_zero (e n : V) : insTermTable e n 0 = !⟦ocOadd e n 0⟧ := by
  simp [insTermTable, insTermTable.construction]

@[simp] lemma insTermTable_succ (e n c : V) :
    insTermTable e n (c + 1) =
      seqCons (insTermTable e n c) (insTermNext e n (c + 1) (insTermTable e n c)) := by
  simp [insTermTable, insTermTable.construction]

/-- **Insert one term** `ω^e·n` into the NF code `b`: the `b`-th entry of the table. -/
noncomputable def insTerm (e n b : V) : V := znth (insTermTable e n b) b

def _root_.LO.FirstOrder.Arithmetic.insTermTableDef : 𝚺₁.Semisentence 4 :=
  insTermTable.blueprint.resultDef.rew (Rew.subst ![#0, #3, #1, #2])

instance insTermTable_defined : 𝚺₁-Function₃ (insTermTable : V → V → V → V) via insTermTableDef := .mk
  fun v ↦ by simp [insTermTable.construction.result_defined_iff, insTermTableDef]; rfl

instance insTermTable_definable : 𝚺₁-Function₃ (insTermTable : V → V → V → V) :=
  insTermTable_defined.to_definable
instance insTermTable_definable' (Γ) : Γ-[m + 1]-Function₃ (insTermTable : V → V → V → V) :=
  insTermTable_definable.of_sigmaOne

def _root_.LO.FirstOrder.Arithmetic.insTermDef : 𝚺₁.Semisentence 4 := .mkSigma
  “y e n b. ∃ t, !insTermTableDef t e n b ∧ !znthDef y t b”

instance insTerm_defined : 𝚺₁-Function₃ (insTerm : V → V → V → V) via insTermDef := .mk fun v ↦ by
  simp [insTermDef, insTerm, insTermTable_defined.iff, znth_defined.iff]

instance insTerm_definable : 𝚺₁-Function₃ (insTerm : V → V → V → V) := insTerm_defined.to_definable
instance insTerm_definable' (Γ) : Γ-[m + 1]-Function₃ (insTerm : V → V → V → V) :=
  insTerm_definable.of_sigmaOne

/-! ### Structural correctness of `insTerm` -/

private lemma def_insTermTable {k} (e n : V) (i : Fin k) :
    𝚺-[1].DefinableFunction (fun v : Fin k → V ↦ insTermTable e n (v i)) :=
  DefinableFunction₃.comp (F := insTermTable) (DefinableFunction.const e) (DefinableFunction.const n)
    (DefinableFunction.var i)

private lemma def_insTerm {k} (e n : V) (i : Fin k) :
    𝚺-[1].DefinableFunction (fun v : Fin k → V ↦ insTerm e n (v i)) :=
  DefinableFunction₃.comp (F := insTerm) (DefinableFunction.const e) (DefinableFunction.const n)
    (DefinableFunction.var i)

@[simp] lemma insTermTable_seq (e n c : V) : Seq (insTermTable e n c) := by
  induction c using ISigma1.sigma1_succ_induction
  · exact Definable.comp₁ (def_insTermTable e n 0)
  case zero => simp
  case succ c ih => rw [insTermTable_succ]; exact ih.seqCons _

@[simp] lemma insTermTable_lh (e n c : V) : lh (insTermTable e n c) = c + 1 := by
  induction c using ISigma1.sigma1_succ_induction
  · exact Definable.comp₂ (DefinableFunction₁.comp (F := lh) (def_insTermTable e n 0)) (by definability)
  case zero => simp
  case succ c ih => rw [insTermTable_succ, Seq.lh_seqCons _ (insTermTable_seq e n c), ih]

lemma znth_insTermTable_succ {e n c k : V} (hk : k < c + 1) :
    znth (insTermTable e n (c + 1)) k = znth (insTermTable e n c) k := by
  rw [insTermTable_succ]
  exact znth_seqCons_of_lt (insTermTable_seq e n c) _ (by rw [insTermTable_lh]; exact hk)

lemma znth_insTermTable_eq_insTerm (e n : V) :
    ∀ N : V, ∀ k ≤ N, znth (insTermTable e n N) k = insTerm e n k := by
  intro N
  induction N using ISigma1.sigma1_succ_induction
  · refine Definable.ball_le (by definability) ?_
    exact Definable.comp₂
      (DefinableFunction₂.comp (F := znth) (def_insTermTable e n 1) (DefinableFunction.var 0))
      (def_insTerm e n 0)
  case zero =>
    intro k hk
    rcases (nonpos_iff_eq_zero.mp hk) with rfl
    rfl
  case succ N ih =>
    intro k hk
    rcases eq_or_lt_of_le hk with rfl | hlt
    · rfl
    · rw [znth_insTermTable_succ hlt]
      exact ih k (le_iff_lt_succ.mpr hlt)

@[simp] lemma insTerm_zero (e n : V) : insTerm e n 0 = ocOadd e n 0 := by
  simp only [insTerm, insTermTable_zero]
  exact (singleton_seq (ocOadd e n 0)).znth_eq_of_mem
    ((mem_singleton_seq_iff _ _).mpr rfl)

/-- **The `insTerm` recursion**: inserting `ω^e·n` into `ocOadd e' n' r'` compares `e` with `e'`. -/
lemma insTerm_ocOadd (e n ec nc rc : V) :
    insTerm e n (ocOadd ec nc rc) =
      (if icmp e ec = 2 then ocOadd e n (ocOadd ec nc rc)
       else if icmp e ec = 1 then ocOadd e (n + nc) rc
       else ocOadd ec nc (insTerm e n rc)) := by
  set c := ocOadd ec nc rc with hc
  have hpos : 0 < c := ocOadd_pos ec nc rc
  obtain ⟨M, hM⟩ : ∃ M, c = M + 1 :=
    ⟨c - 1, (sub_add_self_of_le (pos_iff_one_le.mp hpos)).symm⟩
  have key : znth (insTermTable e n c) c = insTermNext e n c (insTermTable e n M) := by
    rw [hM, insTermTable_succ]
    have := znth_seqCons_self (insTermTable_seq e n M) (insTermNext e n (M + 1) (insTermTable e n M))
    rwa [insTermTable_lh] at this
  have htail : ocTail c ≤ M := by
    have := ocTail_lt ec nc rc; rw [← hc] at this; exact le_iff_lt_succ.mpr (hM ▸ this)
  have hcne : c ≠ 0 := hpos.ne'
  rw [insTerm, key, insTermNext, if_neg hcne,
    znth_insTermTable_eq_insTerm e n M (ocTail c) htail, ocExp_ocOadd, ocCoeff_ocOadd, ocTail_ocOadd]

/-! ## `inadd a b` — natural (Hessenberg) sum (recursion on `a`, param `b`) -/

/-- Table step of `inadd` at first-argument index `c` (param `b`, table `s` of `inadd · b`). -/
noncomputable def inaddNext (b c s : V) : V :=
  if c = 0 then b
  else insTerm (ocExp c) (ocCoeff c) (znth s (ocTail c))

def _root_.LO.FirstOrder.Arithmetic.inaddNextDef : 𝚺₁.Semisentence 4 := .mkSigma
  “y b c s.
    (c = 0 ∧ y = b)
  ∨ (c ≠ 0 ∧ ∃ ex, !ocExpDef ex c ∧ ∃ cc, !ocCoeffDef cc c ∧ ∃ t, !sndIdxDef t c ∧
       ∃ st, !znthDef st s t ∧ !insTermDef y ex cc st)”

instance inaddNext_defined : 𝚺₁-Function₃ (inaddNext : V → V → V → V) via inaddNextDef := .mk
  fun v ↦ by
  simp [inaddNextDef, inaddNext, ocExp_defined.iff, ocCoeff_defined.iff, ocTail,
    sndIdx_defined.iff, insTerm_defined.iff, znth_defined.iff]
  by_cases hc : v 2 = 0 <;> simp [hc]

instance inaddNext_definable : 𝚺₁-Function₃ (inaddNext : V → V → V → V) := inaddNext_defined.to_definable

/-- Blueprint for the `inadd` table (parameter = second summand `b`). -/
def inaddTable.blueprint : PR.Blueprint 1 where
  zero := .mkSigma “y x. !mkSeq₁Def y x”
  succ := .mkSigma “y ih n x. ∃ v, !inaddNextDef v x (n + 1) ih ∧ !seqConsDef y ih v”

noncomputable def inaddTable.construction : PR.Construction V inaddTable.blueprint where
  zero := fun x ↦ !⟦x 0⟧
  succ := fun x n ih ↦ seqCons ih (inaddNext (x 0) (n + 1) ih)
  zero_defined := .mk fun v ↦ by
    simp [inaddTable.blueprint, mkSeq₁Def, seqCons_defined.iff, emptyset_def]
  succ_defined := .mk fun v ↦ by
    simp [inaddTable.blueprint, inaddNext_defined.iff, seqCons_defined.iff]

noncomputable def inaddTable (b n : V) : V := inaddTable.construction.result ![b] n

@[simp] lemma inaddTable_zero (b : V) : inaddTable b 0 = !⟦b⟧ := by
  simp [inaddTable, inaddTable.construction]

@[simp] lemma inaddTable_succ (b n : V) :
    inaddTable b (n + 1) = seqCons (inaddTable b n) (inaddNext b (n + 1) (inaddTable b n)) := by
  simp [inaddTable, inaddTable.construction]

/-- **Internal natural (Hessenberg) sum** `a # b` inside `V`: the `a`-th entry of the table. -/
noncomputable def inadd (a b : V) : V := znth (inaddTable b a) a

def _root_.LO.FirstOrder.Arithmetic.inaddTableDef : 𝚺₁.Semisentence 3 :=
  inaddTable.blueprint.resultDef.rew (Rew.subst ![#0, #2, #1])

instance inaddTable_defined : 𝚺₁-Function₂ (inaddTable : V → V → V) via inaddTableDef := .mk
  fun v ↦ by simp [inaddTable.construction.result_defined_iff, inaddTableDef]; rfl

instance inaddTable_definable : 𝚺₁-Function₂ (inaddTable : V → V → V) := inaddTable_defined.to_definable
instance inaddTable_definable' (Γ) : Γ-[m + 1]-Function₂ (inaddTable : V → V → V) :=
  inaddTable_definable.of_sigmaOne

def _root_.LO.FirstOrder.Arithmetic.inaddDef : 𝚺₁.Semisentence 3 := .mkSigma
  “y a b. ∃ t, !inaddTableDef t b a ∧ !znthDef y t a”

instance inadd_defined : 𝚺₁-Function₂ (inadd : V → V → V) via inaddDef := .mk fun v ↦ by
  simp [inaddDef, inadd, inaddTable_defined.iff, znth_defined.iff]

instance inadd_definable : 𝚺₁-Function₂ (inadd : V → V → V) := inadd_defined.to_definable
instance inadd_definable' (Γ) : Γ-[m + 1]-Function₂ (inadd : V → V → V) := inadd_definable.of_sigmaOne

/-! ### Structural correctness of `inadd` -/

private lemma def_inaddTable {k} (b : V) (i : Fin k) :
    𝚺-[1].DefinableFunction (fun v : Fin k → V ↦ inaddTable b (v i)) :=
  DefinableFunction₂.comp (F := inaddTable) (DefinableFunction.const b) (DefinableFunction.var i)

private lemma def_inadd {k} (b : V) (i : Fin k) :
    𝚺-[1].DefinableFunction (fun v : Fin k → V ↦ inadd (v i) b) :=
  DefinableFunction₂.comp (F := inadd) (DefinableFunction.var i) (DefinableFunction.const b)

@[simp] lemma inaddTable_seq (b n : V) : Seq (inaddTable b n) := by
  induction n using ISigma1.sigma1_succ_induction
  · exact Definable.comp₁ (def_inaddTable b 0)
  case zero => simp
  case succ n ih => rw [inaddTable_succ]; exact ih.seqCons _

@[simp] lemma inaddTable_lh (b n : V) : lh (inaddTable b n) = n + 1 := by
  induction n using ISigma1.sigma1_succ_induction
  · exact Definable.comp₂ (DefinableFunction₁.comp (F := lh) (def_inaddTable b 0)) (by definability)
  case zero => simp
  case succ n ih => rw [inaddTable_succ, Seq.lh_seqCons _ (inaddTable_seq b n), ih]

lemma znth_inaddTable_succ {b n k : V} (hk : k < n + 1) :
    znth (inaddTable b (n + 1)) k = znth (inaddTable b n) k := by
  rw [inaddTable_succ]
  exact znth_seqCons_of_lt (inaddTable_seq b n) _ (by rw [inaddTable_lh]; exact hk)

lemma znth_inaddTable_eq_inadd (b : V) : ∀ N : V, ∀ k ≤ N, znth (inaddTable b N) k = inadd k b := by
  intro N
  induction N using ISigma1.sigma1_succ_induction
  · refine Definable.ball_le (by definability) ?_
    exact Definable.comp₂
      (DefinableFunction₂.comp (F := znth) (def_inaddTable b 1) (DefinableFunction.var 0))
      (def_inadd b 0)
  case zero =>
    intro k hk
    rcases (nonpos_iff_eq_zero.mp hk) with rfl
    rfl
  case succ N ih =>
    intro k hk
    rcases eq_or_lt_of_le hk with rfl | hlt
    · rfl
    · rw [znth_inaddTable_succ hlt]
      exact ih k (le_iff_lt_succ.mpr hlt)

@[simp] lemma inadd_zero_left (b : V) : inadd 0 b = b := by
  simp only [inadd, inaddTable_zero]
  exact (singleton_seq b).znth_eq_of_mem ((mem_singleton_seq_iff b b).mpr rfl)

/-- **The natural-sum recursion**: `(ω^e·n + r) # b = insTerm e n (r # b)` — fold the leading term
of the first summand into the natural sum of the rest. -/
lemma inadd_ocOadd (ec nc rc b : V) :
    inadd (ocOadd ec nc rc) b = insTerm ec nc (inadd rc b) := by
  set c := ocOadd ec nc rc with hc
  have hpos : 0 < c := ocOadd_pos ec nc rc
  obtain ⟨M, hM⟩ : ∃ M, c = M + 1 :=
    ⟨c - 1, (sub_add_self_of_le (pos_iff_one_le.mp hpos)).symm⟩
  have key : znth (inaddTable b c) c = inaddNext b c (inaddTable b M) := by
    rw [hM, inaddTable_succ]
    have := znth_seqCons_self (inaddTable_seq b M) (inaddNext b (M + 1) (inaddTable b M))
    rwa [inaddTable_lh] at this
  have htail : ocTail c ≤ M := by
    have := ocTail_lt ec nc rc; rw [← hc] at this; exact le_iff_lt_succ.mpr (hM ▸ this)
  have hcne : c ≠ 0 := hpos.ne'
  rw [inadd, key, inaddNext, if_neg hcne,
    znth_inaddTable_eq_inadd b M (ocTail c) htail, ocExp_ocOadd, ocCoeff_ocOadd, ocTail_ocOadd]

/-! ## Supporting `icmp` trichotomy (lt/eq/gt are the only outcomes) -/

lemma cmpV_tri (a b : V) : cmpV a b = 0 ∨ cmpV a b = 1 ∨ cmpV a b = 2 := by
  unfold cmpV; split_ifs <;> simp

lemma thenV_tri {a b : V} (ha : a = 0 ∨ a = 1 ∨ a = 2) (hb : b = 0 ∨ b = 1 ∨ b = 2) :
    thenV a b = 0 ∨ thenV a b = 1 ∨ thenV a b = 2 := by
  unfold thenV; split_ifs with h
  · exact hb
  · exact ha

/-- **`icmp` trichotomy**: the comparison code is always `0` (lt), `1` (eq), or `2` (gt). -/
lemma icmp_tri (c1 c2 : V) : icmp c1 c2 = 0 ∨ icmp c1 c2 = 1 ∨ icmp c1 c2 = 2 := by
  suffices h : ∀ m : V, icmp (π₁ m) (π₂ m) = 0 ∨ icmp (π₁ m) (π₂ m) = 1 ∨ icmp (π₁ m) (π₂ m) = 2 by
    have := h ⟪c1, c2⟫; simpa using this
  intro m
  induction m using ISigma1.sigma1_order_induction
  · definability
  case ind m IH =>
    have hm : (⟪π₁ m, π₂ m⟫ : V) = m := pair_unpair m
    rcases eq_or_ne (π₁ m) 0 with ha | ha
    · rcases eq_or_ne (π₂ m) 0 with hb | hb
      · rw [ha, hb, icmp_zero_zero]; tauto
      · rw [ha, icmp_zero_pos hb]; tauto
    · rcases eq_or_ne (π₂ m) 0 with hb | hb
      · rw [hb, icmp_pos_zero ha]; tauto
      · rw [icmp_pos_pos ha hb]
        have hexp : (⟪ocExp (π₁ m), ocExp (π₂ m)⟫ : V) < m := by
          have h := pair_lt_pair (ocExp_lt_of_pos (pos_iff_ne_zero.mpr ha))
            (ocExp_lt_of_pos (pos_iff_ne_zero.mpr hb))
          rwa [hm] at h
        have htail : (⟪ocTail (π₁ m), ocTail (π₂ m)⟫ : V) < m := by
          have h := pair_lt_pair (ocTail_lt_of_pos (pos_iff_ne_zero.mpr ha))
            (ocTail_lt_of_pos (pos_iff_ne_zero.mpr hb))
          rwa [hm] at h
        have he := IH _ hexp; simp only [pi₁_pair, pi₂_pair] at he
        have ht := IH _ htail; simp only [pi₁_pair, pi₂_pair] at ht
        exact thenV_tri he (thenV_tri (cmpV_tri _ _) ht)

/-- If the comparison is neither `eq` nor `gt`, it is `lt` (`= 0`). -/
lemma icmp_eq_zero_of_ne {a b : V} (h1 : icmp a b ≠ 1) (h2 : icmp a b ≠ 2) : icmp a b = 0 := by
  rcases icmp_tri a b with h | h | h
  · exact h
  · exact absurd h h1
  · exact absurd h h2

/-! ## Positivity and leading exponent of `insTerm` -/

/-- `insTerm e n b` is always a positive code (every recursion branch is an `ocOadd`). -/
@[simp] lemma insTerm_pos (e n b : V) : 0 < insTerm e n b := by
  rcases eq_or_ne b 0 with rfl | hb
  · rw [insTerm_zero]; exact ocOadd_pos _ _ _
  · obtain ⟨e', n', r', rfl⟩ : ∃ e' n' r', b = ocOadd e' n' r' :=
      ⟨ocExp b, ocCoeff b, ocTail b, (ocOadd_destruct hb).symm⟩
    rw [insTerm_ocOadd]; split_ifs <;> exact ocOadd_pos _ _ _

lemma insTerm_ne_zero (e n b : V) : insTerm e n b ≠ 0 := (insTerm_pos e n b).ne'

/-- **Leading exponent of `insTerm`**: the head exponent is `e` unless `e ≺ (lead exp of b)`, in which
case it stays `ocExp b`. -/
lemma ocExp_insTerm (e n b : V) :
    ocExp (insTerm e n b) = if b = 0 then e else if icmp e (ocExp b) = 0 then ocExp b else e := by
  rcases eq_or_ne b 0 with rfl | hb
  · simp [insTerm_zero]
  · obtain ⟨e', n', r', rfl⟩ : ∃ e' n' r', b = ocOadd e' n' r' :=
      ⟨ocExp b, ocCoeff b, ocTail b, (ocOadd_destruct hb).symm⟩
    rw [insTerm_ocOadd, if_neg (ocOadd_ne_zero _ _ _), ocExp_ocOadd]
    by_cases h0 : icmp e e' = 0
    · rw [if_pos h0, if_neg (by rw [h0]; simp), if_neg (by rw [h0]; simp), ocExp_ocOadd]
    · rw [if_neg h0]
      by_cases h2 : icmp e e' = 2
      · rw [if_pos h2, ocExp_ocOadd]
      · by_cases h1 : icmp e e' = 1
        · rw [if_neg h2, if_pos h1, ocExp_ocOadd]
        · exact absurd (icmp_eq_zero_of_ne h1 h2) h0

/-! ## NF preservation of `insTerm` -/

/-- **`insTerm` preserves NF.** Inserting a single term `ω^e·n` (`isNF e`, `n ≠ 0`) into an NF code
`b` yields an NF code: order-induction on `b`, mirroring the three `insTerm_ocOadd` branches. -/
lemma isNF_insTerm {e n : V} (he : isNF e) (hn : n ≠ 0) :
    ∀ b, isNF b → isNF (insTerm e n b) := by
  intro b
  induction b using ISigma1.sigma1_order_induction
  · definability
  case ind b IH =>
    intro hb
    rcases eq_or_ne b 0 with rfl | hb0
    · rw [insTerm_zero, isNF_ocOadd]
      exact ⟨hn, he, isNF_zero, Or.inl rfl⟩
    · obtain ⟨ec, nc, rc, rfl⟩ : ∃ ec nc rc, b = ocOadd ec nc rc :=
        ⟨_, _, _, (ocOadd_destruct hb0).symm⟩
      rw [isNF_ocOadd] at hb
      obtain ⟨hnc, hec, hrc, hside⟩ := hb
      rw [insTerm_ocOadd]
      by_cases h2 : icmp e ec = 2
      · -- `e ≻ ec`: prepend the new term. New tail is the (NF) old code; its lead exp `ec ≺ e`.
        rw [if_pos h2, isNF_ocOadd]
        refine ⟨hn, he, ?_, Or.inr ?_⟩
        · rw [isNF_ocOadd]; exact ⟨hnc, hec, hrc, hside⟩
        · rw [ocExp_ocOadd]; exact icmp_two_iff_swap_zero.mp h2
      · rw [if_neg h2]
        by_cases h1 : icmp e ec = 1
        · -- `e = ec`: merge coefficients. Side condition transports along `e = ec`.
          rw [if_pos h1, isNF_ocOadd]
          have hee : e = ec :=
            icmp_eq_imp_eq (max e ec) e (le_max_left _ _) ec (le_max_right _ _) h1
          have hnn : n + nc ≠ 0 :=
            (lt_of_lt_of_le (pos_iff_ne_zero.mpr hn) (le_add_right (le_refl n))).ne'
          refine ⟨hnn, he, hrc, ?_⟩
          rcases hside with h | h
          · exact Or.inl h
          · exact Or.inr (by rw [hee]; exact h)
        · -- `e ≺ ec`: recurse into the tail; keep head `ec`.
          rw [if_neg h1]
          have h0 : icmp e ec = 0 := icmp_eq_zero_of_ne h1 h2
          have hrclt : rc < ocOadd ec nc rc := by
            have := ocTail_lt ec nc rc; rwa [ocTail_ocOadd] at this
          have hrec : isNF (insTerm e n rc) := IH rc hrclt hrc
          rw [isNF_ocOadd]
          refine ⟨hnc, hec, hrec, Or.inr ?_⟩
          rw [ocExp_insTerm]
          rcases eq_or_ne rc 0 with rfl | hrc0
          · rw [if_pos rfl]; exact h0
          · rw [if_neg hrc0]
            by_cases hcmp : icmp e (ocExp rc) = 0
            · rw [if_pos hcmp]
              rcases hside with h | h
              · exact absurd h hrc0
              · exact h
            · rw [if_neg hcmp]; exact h0

/-- **`inadd` preserves NF.** The natural sum of two NF codes is NF: order-induction on the first
summand `a`, folding the leading term of `a` into the (recursively NF) `inadd rc b` via
`isNF_insTerm`. -/
lemma isNF_inadd {b : V} (hb : isNF b) : ∀ a, isNF a → isNF (inadd a b) := by
  intro a
  induction a using ISigma1.sigma1_order_induction
  · definability
  case ind a IH =>
    intro ha
    rcases eq_or_ne a 0 with rfl | ha0
    · rw [inadd_zero_left]; exact hb
    · obtain ⟨ec, nc, rc, rfl⟩ : ∃ ec nc rc, a = ocOadd ec nc rc :=
        ⟨_, _, _, (ocOadd_destruct ha0).symm⟩
      rw [isNF_ocOadd] at ha
      obtain ⟨hnc, hec, hrc, _⟩ := ha
      rw [inadd_ocOadd]
      have hrclt : rc < ocOadd ec nc rc := by
        have := ocTail_lt ec nc rc; rwa [ocTail_ocOadd] at this
      exact isNF_insTerm hec hnc _ (IH rc hrclt hrc)

/-! ## Prepend / right-unit laws -/

/-- **Prepend law for `insTerm`.** When the new exponent `e` strictly dominates `b`'s leading
exponent (or `b = 0`), `insTerm e n b` is the literal prepend `ocOadd e n b`. -/
lemma insTerm_prepend {e n b : V} (h : b = 0 ∨ icmp (ocExp b) e = 0) :
    insTerm e n b = ocOadd e n b := by
  rcases eq_or_ne b 0 with rfl | hb0
  · rw [insTerm_zero]
  · obtain ⟨ec, nc, rc, rfl⟩ : ∃ ec nc rc, b = ocOadd ec nc rc :=
      ⟨_, _, _, (ocOadd_destruct hb0).symm⟩
    have hcmp : icmp ec e = 0 := by
      rcases h with h | h
      · exact absurd h (ocOadd_ne_zero _ _ _)
      · rwa [ocExp_ocOadd] at h
    rw [insTerm_ocOadd, if_pos (icmp_two_iff_swap_zero.mpr hcmp)]

/-- **Right unit of `#`.** The natural sum of an NF code with `0` is itself: order-induction on `a`,
each leading term re-prepended via `insTerm_prepend` (NF guarantees the strict-dominance side). -/
lemma inadd_zero_right : ∀ a, isNF a → inadd a 0 = a := by
  intro a
  induction a using ISigma1.sigma1_order_induction
  · definability
  case ind a IH =>
    intro ha
    rcases eq_or_ne a 0 with rfl | ha0
    · exact inadd_zero_left 0
    · obtain ⟨ec, nc, rc, rfl⟩ : ∃ ec nc rc, a = ocOadd ec nc rc :=
        ⟨_, _, _, (ocOadd_destruct ha0).symm⟩
      rw [isNF_ocOadd] at ha
      obtain ⟨_, _, hrc, hside⟩ := ha
      rw [inadd_ocOadd]
      have hrclt : rc < ocOadd ec nc rc := by
        have := ocTail_lt ec nc rc; rwa [ocTail_ocOadd] at this
      rw [IH rc hrclt hrc]
      exact insTerm_prepend hside

/-! ## ω-power monotonicity

Buchholz's `õ` only ever natural-sums **single ω-powers** `ω^α = ocOadd α 1 0` (coefficient `1`,
empty tail): `õ(K d0…dl) = ω^{õ d0} # … # ω^{õ dl}`. On such terms the comparison collapses to the
exponent comparison, so `ω^·` is an order-embedding — the bedrock for the §4 ordinal descent. -/

/-- `thenV a 1 = a` (right `eq`-identity of the lexicographic combiner). -/
@[simp] lemma thenV_one_right (a : V) : thenV a 1 = a := by
  unfold thenV; by_cases h : a = 1 <;> simp [h]

/-- **`ω^·` is an order-embedding**: `icmp (ω^α) (ω^β) = icmp α β` (coefficient `1`, empty tail, so
the lexicographic combine passes straight through to the exponents). -/
lemma icmp_omega_pow (α β : V) :
    icmp (ocOadd α 1 0) (ocOadd β 1 0) = icmp α β := by
  rw [icmp_ocOadd, cmpV_self, icmp_zero_zero, thenV_one_right, thenV_one_right]

/-- **Folding an ω-power into a natural sum is a single `insTerm`**: `ω^α # b = insTerm α 1 b`
(the empty tail collapses the `inadd` recursion to one insertion). This is the step `õ`'s
left-fold `ω^{õ d0} # (ω^{õ d1} # … )` repeatedly takes. -/
lemma inadd_omega_pow (α b : V) : inadd (ocOadd α 1 0) b = insTerm α 1 b := by
  rw [inadd_ocOadd, inadd_zero_left]

/-- **A single-term left summand collapses to `insTerm`**: `(ω^e·n) # b = insTerm e n b`. The
general form of `inadd_omega_pow`; the bridge that recasts strict `#`-monotonicity (left-cancellation)
as the single-term insertion embedding `icmp_insTerm_congr`. -/
lemma inadd_single_term (e n b : V) : inadd (ocOadd e n 0) b = insTerm e n b := by
  rw [inadd_ocOadd, inadd_zero_left]

/-- **`cmpV` is invariant under a common left summand**: `cmpV (k+a) (k+b) = cmpV a b`. The
coefficient-merge in `insTerm` adds the inserted `n` to both sides, so the comparison is unchanged —
exactly what the `icmp_insTerm_congr` merge branch needs. -/
@[simp] lemma cmpV_add_left (k a b : V) : cmpV (k + a) (k + b) = cmpV a b := by
  simp only [cmpV, add_lt_add_iff_left, add_right_inj]

/-! ## `icmp` transitivity of `≺` (the linear-order spine the descent reasoning needs)

`InternalONote` proved `icmp` trichotomy + antisymmetry but **deliberately avoided** a general
transitivity (`icmp_finThresh_mono` docstring). The natural-sum monotonicity proof needs it (it must
chain `ea ≺ e ≺ eb`), so it is built here: lexicographic transitivity on `(exp, coeff, tail)` by
strong induction, recursing into exponents and tails (both strictly smaller codes). -/

/-- **`≺` is transitive** (bounded form): `icmp a b = 0 → icmp b c = 0 → icmp a c = 0`. -/
lemma icmp_trans : ∀ w : V, ∀ a ≤ w, ∀ b ≤ w, ∀ c ≤ w,
    icmp a b = 0 → icmp b c = 0 → icmp a c = 0 := by
  intro w
  induction w using ISigma1.sigma1_order_induction
  · definability
  case ind w ih =>
    intro a haw b hbw c hcw hab hbc
    rcases eq_or_ne a 0 with rfl | ha
    · -- a = 0: from `hbc`, c ≠ 0, so icmp 0 c = 0.
      have hc : c ≠ 0 := by
        rintro rfl
        rcases eq_or_ne b 0 with rfl | hb
        · rw [icmp_zero_zero] at hbc; exact absurd hbc (by simp)
        · rw [icmp_pos_zero hb] at hbc; exact absurd hbc (by simp)
      rw [icmp_zero_pos hc]
    · have hb : b ≠ 0 := by
        rintro rfl; rw [icmp_pos_zero ha] at hab; exact absurd hab (by simp)
      have hc : c ≠ 0 := by
        rintro rfl; rw [icmp_pos_zero hb] at hbc; exact absurd hbc (by simp)
      obtain ⟨ea, ca, ra, rfl⟩ : ∃ ea ca ra, a = ocOadd ea ca ra :=
        ⟨_, _, _, (ocOadd_destruct ha).symm⟩
      obtain ⟨eb, cb, rb, rfl⟩ : ∃ eb cb rb, b = ocOadd eb cb rb :=
        ⟨_, _, _, (ocOadd_destruct hb).symm⟩
      obtain ⟨ec, cc, rc, rfl⟩ : ∃ ec cc rc, c = ocOadd ec cc rc :=
        ⟨_, _, _, (ocOadd_destruct hc).symm⟩
      rw [icmp_ocOadd] at hab hbc ⊢
      have hea : ea < w := lt_of_lt_of_le (by simpa using ocExp_lt ea ca ra) haw
      have heb : eb < w := lt_of_lt_of_le (by simpa using ocExp_lt eb cb rb) hbw
      have hec : ec < w := lt_of_lt_of_le (by simpa using ocExp_lt ec cc rc) hcw
      have hra : ra < w := lt_of_lt_of_le (by simpa using ocTail_lt ea ca ra) haw
      have hrb : rb < w := lt_of_lt_of_le (by simpa using ocTail_lt eb cb rb) hbw
      have hrc : rc < w := lt_of_lt_of_le (by simpa using ocTail_lt ec cc rc) hcw
      have IHe : icmp ea eb = 0 → icmp eb ec = 0 → icmp ea ec = 0 := fun h1 h2 =>
        ih (max ea (max eb ec)) (max_lt hea (max_lt heb hec))
          ea (le_max_left _ _) eb (le_trans (le_max_left _ _) (le_max_right _ _))
          ec (le_trans (le_max_right _ _) (le_max_right _ _)) h1 h2
      have IHr : icmp ra rb = 0 → icmp rb rc = 0 → icmp ra rc = 0 := fun h1 h2 =>
        ih (max ra (max rb rc)) (max_lt hra (max_lt hrb hrc))
          ra (le_max_left _ _) rb (le_trans (le_max_left _ _) (le_max_right _ _))
          rc (le_trans (le_max_right _ _) (le_max_right _ _)) h1 h2
      rcases eq_or_ne (icmp ea eb) 0 with hEab | hEab
      · -- ea ≺ eb ⟹ ea ≺ ec (eb ≺ ec by IHe, or eb = ec by substitution).
        have hEac : icmp ea ec = 0 := by
          rcases eq_or_ne (icmp eb ec) 0 with hEbc | hEbc
          · exact IHe hEab hEbc
          · have hEbc1 : icmp eb ec = 1 := by
              rcases thenV_eq_zero.mp hbc with h | ⟨h, _⟩
              · exact absurd h hEbc
              · exact h
            have hee : eb = ec :=
              icmp_eq_imp_eq (max eb ec) eb (le_max_left _ _) ec (le_max_right _ _) hEbc1
            rw [← hee]; exact hEab
        rw [hEac]; simp [thenV]
      · -- ea = eb (icmp = 1); the comparison drops to (coeff, tail).
        have hEab1 : icmp ea eb = 1 := by
          rcases thenV_eq_zero.mp hab with h | ⟨h, _⟩
          · exact absurd h hEab
          · exact h
        have habCR : thenV (cmpV ca cb) (icmp ra rb) = 0 := by
          rcases thenV_eq_zero.mp hab with h | ⟨_, h⟩
          · exact absurd h hEab
          · exact h
        have heab : ea = eb :=
          icmp_eq_imp_eq (max ea eb) ea (le_max_left _ _) eb (le_max_right _ _) hEab1
        rcases eq_or_ne (icmp eb ec) 0 with hEbc | hEbc
        · -- eb ≺ ec, and ea = eb ⟹ ea ≺ ec.
          have : icmp ea ec = 0 := by rw [heab]; exact hEbc
          rw [this]; simp [thenV]
        · -- eb = ec too; ea = eb = ec, drop to (coeff, tail) transitivity.
          have hEbc1 : icmp eb ec = 1 := by
            rcases thenV_eq_zero.mp hbc with h | ⟨h, _⟩
            · exact absurd h hEbc
            · exact h
          have hbcCR : thenV (cmpV cb cc) (icmp rb rc) = 0 := by
            rcases thenV_eq_zero.mp hbc with h | ⟨_, h⟩
            · exact absurd h hEbc
            · exact h
          have hebc : eb = ec :=
            icmp_eq_imp_eq (max eb ec) eb (le_max_left _ _) ec (le_max_right _ _) hEbc1
          have hEac1 : icmp ea ec = 1 := by rw [heab, hebc]; exact icmp_self ec ec le_rfl
          rw [hEac1, thenV_one_left]
          -- goal: thenV (cmpV ca cc) (icmp ra rc) = 0, from the (C,R) lex transitivity.
          rcases eq_or_ne (cmpV ca cb) 0 with hCab | hCab
          · have hcacb : ca < cb := cmpV_eq_zero.mp hCab
            have hCac : cmpV ca cc = 0 := by
              rcases eq_or_ne (cmpV cb cc) 0 with hCbc | hCbc
              · exact cmpV_eq_zero.mpr (lt_trans hcacb (cmpV_eq_zero.mp hCbc))
              · have hCbc1 : cmpV cb cc = 1 := by
                  rcases thenV_eq_zero.mp hbcCR with h | ⟨h, _⟩
                  · exact absurd h hCbc
                  · exact h
                have hbe : cb = cc := cmpV_eq_one.mp hCbc1
                exact cmpV_eq_zero.mpr (by rw [← hbe]; exact hcacb)
            rw [hCac]; simp [thenV]
          · have hCab1 : cmpV ca cb = 1 := by
              rcases thenV_eq_zero.mp habCR with h | ⟨h, _⟩
              · exact absurd h hCab
              · exact h
            have hRab : icmp ra rb = 0 := by
              rcases thenV_eq_zero.mp habCR with h | ⟨_, h⟩
              · exact absurd h hCab
              · exact h
            have hcacb : ca = cb := cmpV_eq_one.mp hCab1
            rcases eq_or_ne (cmpV cb cc) 0 with hCbc | hCbc
            · have hCac : cmpV ca cc = 0 := cmpV_eq_zero.mpr (by rw [hcacb]; exact cmpV_eq_zero.mp hCbc)
              rw [hCac]; simp [thenV]
            · have hCbc1 : cmpV cb cc = 1 := by
                rcases thenV_eq_zero.mp hbcCR with h | ⟨h, _⟩
                · exact absurd h hCbc
                · exact h
              have hRbc : icmp rb rc = 0 := by
                rcases thenV_eq_zero.mp hbcCR with h | ⟨_, h⟩
                · exact absurd h hCbc
                · exact h
              have hcbcc : cb = cc := cmpV_eq_one.mp hCbc1
              have hCac1 : cmpV ca cc = 1 := cmpV_eq_one.mpr (hcacb.trans hcbcc)
              rw [hCac1, thenV_one_left]
              exact IHr hRab hRbc

/-! ## Strict `#`-monotonicity — helpers toward `icmp_insTerm_mono`

The §4 descent needs: replacing a summand by a strictly smaller one strictly decreases the natural
sum. Recast via `inadd_single_term`, this is the single-term insertion `≺`-preservation
`icmp_insTerm_mono` (below, the crux). Two reusable helpers first. -/

/-- **Lead exponent decides `≺`**: if both codes are positive and the leading exponents satisfy
`icmp (ocExp X) (ocExp Y) = 0`, then `icmp X Y = 0` outright (the head dominates the lexicographic
combine). -/
lemma icmp_zero_of_exp_zero {X Y : V} (hX : X ≠ 0) (hY : Y ≠ 0)
    (h : icmp (ocExp X) (ocExp Y) = 0) : icmp X Y = 0 := by
  rw [icmp_pos_pos hX hY, h]; simp [thenV]

/-- **Dominance (the `A = 0` base case of `icmp_insTerm_mono`)**: a lone term `ω^e·n` is `≺` its own
insertion into any nonzero NF code `B` — inserting either prepends/keeps a `≻`-head, merges to a
larger coefficient, or appends a positive tail. Three branches on `icmp e (ocExp B)`. -/
lemma icmp_term_insTerm {e n B : V} (hB : isNF B) (hB0 : B ≠ 0) :
    icmp (ocOadd e n 0) (insTerm e n B) = 0 := by
  obtain ⟨eb, cb, rb, rfl⟩ : ∃ eb cb rb, B = ocOadd eb cb rb :=
    ⟨_, _, _, (ocOadd_destruct hB0).symm⟩
  have hcb : cb ≠ 0 := ((isNF_ocOadd eb cb rb).mp hB).1
  rw [insTerm_ocOadd]
  by_cases h2 : icmp e eb = 2
  · rw [if_pos h2, icmp_ocOadd, icmp_self e e le_rfl, cmpV_self, icmp_zero_ocOadd]
    simp [thenV]
  · rw [if_neg h2]
    by_cases h1 : icmp e eb = 1
    · rw [if_pos h1, icmp_ocOadd, icmp_self e e le_rfl,
        show cmpV n (n + cb) = 0 from cmpV_eq_zero.mpr (lt_add_of_pos_right n (pos_iff_ne_zero.mpr hcb))]
      simp [thenV]
    · have h0 : icmp e eb = 0 := icmp_eq_zero_of_ne h1 h2
      rw [if_neg h1, icmp_ocOadd, h0]
      simp [thenV]

end GoodsteinPA.InternalONote
