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

end GoodsteinPA.InternalONote
