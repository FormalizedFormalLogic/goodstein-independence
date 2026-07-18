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
import GoodsteinPA.Compat

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
      · simp [hc, h1]
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
lemma inadd_zero_right : ∀ a : V, isNF a → inadd a 0 = a := by
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

/-- **Strict mono, strictly-smaller-lead case (non-recursive).** When `A`'s leading exponent is `≺`
`B`'s (`icmp ea eb = 0`), inserting the same `ω^e·n` into both keeps `A ≺ B`. The `3×3` grid on
`icmp e ea` × `icmp e eb`: 5 combos resolve at head/coeff/lead, 4 are impossible (they would force
`ea ⪰ eb`, contradicting `icmp ea eb = 0` — derived via `icmp_trans`/swap). -/
lemma icmp_insTerm_left {e n ea ca ra eb cb rb : V} (hcb : cb ≠ 0) (h : icmp ea eb = 0) :
    icmp (insTerm e n (ocOadd ea ca ra)) (insTerm e n (ocOadd eb cb rb)) = 0 := by
  rw [insTerm_ocOadd, insTerm_ocOadd]
  by_cases h2a : icmp e ea = 2
  · rw [if_pos h2a]
    by_cases h2b : icmp e eb = 2
    · rw [if_pos h2b, icmp_ocOadd, icmp_self e e le_rfl, cmpV_self, thenV_one_left, thenV_one_left,
        icmp_ocOadd, h]
      simp [thenV]
    · by_cases h1b : icmp e eb = 1
      · rw [if_neg h2b, if_pos h1b, icmp_ocOadd, icmp_self e e le_rfl, thenV_one_left,
          show cmpV n (n + cb) = 0 from
            cmpV_eq_zero.mpr (lt_add_of_pos_right n (pos_iff_ne_zero.mpr hcb))]
        simp [thenV]
      · have hceb0 : icmp e eb = 0 := icmp_eq_zero_of_ne h1b h2b
        rw [if_neg h2b, if_neg h1b, icmp_ocOadd, hceb0]; simp [thenV]
  · by_cases h1a : icmp e ea = 1
    · rw [if_neg h2a, if_pos h1a]
      have hea : e = ea := icmp_eq_imp_eq (max e ea) e (le_max_left _ _) ea (le_max_right _ _) h1a
      have hceb0 : icmp e eb = 0 := by rw [hea]; exact h
      rw [if_neg (by rw [hceb0]; simp), if_neg (by rw [hceb0]; simp), icmp_ocOadd, hceb0]
      simp [thenV]
    · rw [if_neg h2a, if_neg h1a]
      have hcea0 : icmp e ea = 0 := icmp_eq_zero_of_ne h1a h2a
      by_cases h2b : icmp e eb = 2
      · exfalso
        have hebe : icmp eb e = 0 := icmp_two_iff_swap_zero.mp h2b
        have hba : icmp eb ea = 0 := icmp_trans (max eb (max e ea)) eb (le_max_left _ _)
          e (le_trans (le_max_left _ _) (le_max_right _ _))
          ea (le_trans (le_max_right _ _) (le_max_right _ _)) hebe hcea0
        rw [icmp_two_iff_swap_zero.mpr hba] at h; exact absurd h (by simp)
      · by_cases h1b : icmp e eb = 1
        · exfalso
          have heb : e = eb := icmp_eq_imp_eq (max e eb) e (le_max_left _ _) eb (le_max_right _ _) h1b
          have : icmp ea eb = 2 := by rw [← heb]; exact icmp_two_iff_swap_zero.mpr hcea0
          rw [this] at h; exact absurd h (by simp)
        · rw [if_neg h2b, if_neg h1b, icmp_ocOadd, h]; simp [thenV]

/-- **Strict `#`-monotonicity in the inserted-into argument (`≺`-preservation), pair-induction core.**
`icmp A B = 0 → icmp (insTerm e n A) (insTerm e n B) = 0` for NF `A,B`. The `ea ≺ eb` case is
`icmp_insTerm_left`; the `ea = eb` case drops to `(coeff, tail)` and recurses on the tails. -/
lemma icmp_insTerm_mono_aux (e n : V) : ∀ m : V,
    isNF (π₁ m) → isNF (π₂ m) → icmp (π₁ m) (π₂ m) = 0 →
    icmp (insTerm e n (π₁ m)) (insTerm e n (π₂ m)) = 0 := by
  intro m
  induction m using ISigma1.sigma1_order_induction
  · definability
  case ind m IH =>
    intro hA hB hAB
    have hm : (⟪π₁ m, π₂ m⟫ : V) = m := pair_unpair m
    rcases eq_or_ne (π₁ m) 0 with hA0 | hA0
    · rw [hA0] at hAB ⊢
      have hB0 : π₂ m ≠ 0 := by
        rintro h0; rw [h0, icmp_zero_zero] at hAB; exact absurd hAB (by simp)
      rw [insTerm_zero]; exact icmp_term_insTerm hB hB0
    · rcases eq_or_ne (π₂ m) 0 with hB0 | hB0
      · rw [hB0, icmp_pos_zero hA0] at hAB; exact absurd hAB (by simp)
      · obtain ⟨ea, ca, ra, hAeq⟩ : ∃ ea ca ra, π₁ m = ocOadd ea ca ra :=
          ⟨_, _, _, (ocOadd_destruct hA0).symm⟩
        obtain ⟨eb, cb, rb, hBeq⟩ : ∃ eb cb rb, π₂ m = ocOadd eb cb rb :=
          ⟨_, _, _, (ocOadd_destruct hB0).symm⟩
        rw [hAeq] at hA; rw [hBeq] at hB
        obtain ⟨hca, hea, hra, hsideA⟩ := (isNF_ocOadd ea ca ra).mp hA
        obtain ⟨hcb, heb, hrb, hsideB⟩ := (isNF_ocOadd eb cb rb).mp hB
        rw [hAeq, hBeq] at hAB ⊢
        by_cases hLab : icmp ea eb = 0
        · exact icmp_insTerm_left hcb hLab
        · rw [icmp_ocOadd] at hAB
          have hLab1 : icmp ea eb = 1 := by
            rcases thenV_eq_zero.mp hAB with hh | ⟨hh, _⟩
            · exact absurd hh hLab
            · exact hh
          have hP : thenV (cmpV ca cb) (icmp ra rb) = 0 := by
            rcases thenV_eq_zero.mp hAB with hh | ⟨_, hh⟩
            · exact absurd hh hLab
            · exact hh
          have heab : ea = eb :=
            icmp_eq_imp_eq (max ea eb) ea (le_max_left _ _) eb (le_max_right _ _) hLab1
          rw [insTerm_ocOadd, insTerm_ocOadd]
          by_cases h2 : icmp e ea = 2
          · have h2b : icmp e eb = 2 := by rw [← heab]; exact h2
            rw [if_pos h2, if_pos h2b, icmp_ocOadd, icmp_self e e le_rfl, cmpV_self,
              thenV_one_left, thenV_one_left, icmp_ocOadd, hLab1, thenV_one_left]
            exact hP
          · by_cases h1 : icmp e ea = 1
            · have h1b : icmp e eb = 1 := by rw [← heab]; exact h1
              rw [if_neg h2, if_pos h1, if_neg (by rw [← heab]; exact h2), if_pos h1b,
                icmp_ocOadd, icmp_self e e le_rfl, cmpV_add_left, thenV_one_left]
              exact hP
            · have hcea0 : icmp e ea = 0 := icmp_eq_zero_of_ne h1 h2
              rw [if_neg h2, if_neg h1, if_neg (by rw [← heab]; exact h2),
                if_neg (by rw [← heab]; exact h1), icmp_ocOadd, hLab1, thenV_one_left]
              by_cases hC : cmpV ca cb = 0
              · rw [hC]; simp [thenV]
              · have hC1 : cmpV ca cb = 1 := by
                  rcases thenV_eq_zero.mp hP with hh | ⟨hh, _⟩
                  · exact absurd hh hC
                  · exact hh
                have hRab : icmp ra rb = 0 := by
                  rcases thenV_eq_zero.mp hP with hh | ⟨_, hh⟩
                  · exact absurd hh hC
                  · exact hh
                rw [hC1, thenV_one_left]
                have hlt : (⟪ra, rb⟫ : V) < m := by
                  have hra_lt : ra < π₁ m := by rw [hAeq]; simpa using ocTail_lt ea ca ra
                  have hrb_lt : rb < π₂ m := by rw [hBeq]; simpa using ocTail_lt eb cb rb
                  have := pair_lt_pair hra_lt hrb_lt; rwa [hm] at this
                have := IH ⟪ra, rb⟫ hlt (by simpa [pi₁_pair, pi₂_pair] using hra)
                  (by simpa [pi₁_pair, pi₂_pair] using hrb) (by simpa [pi₁_pair, pi₂_pair] using hRab)
                simpa [pi₁_pair, pi₂_pair] using this

/-- **Strict `#`-monotonicity (single-term, `≺`-preservation).** `icmp A B = 0 → icmp (insTerm e n A)
(insTerm e n B) = 0` for NF `A,B`. Recast via `inadd_single_term` this is the left-cancellation that
the §4 descent (F1) uses to drop the natural sum when one summand drops. -/
lemma icmp_insTerm_mono {e n A B : V} (hA : isNF A) (hB : isNF B) (hAB : icmp A B = 0) :
    icmp (insTerm e n A) (insTerm e n B) = 0 := by
  have := icmp_insTerm_mono_aux e n ⟪A, B⟫ (by simpa [pi₁_pair, pi₂_pair] using hA)
    (by simpa [pi₁_pair, pi₂_pair] using hB) (by simpa [pi₁_pair, pi₂_pair] using hAB)
  simpa [pi₁_pair, pi₂_pair] using this

/-- **F1 — strict left-monotonicity of the natural sum `#`.** `icmp X Y = 0 → icmp (g # X) (g # Y) = 0`
for NF `g, X, Y`: replacing one summand of a natural sum by a strictly `≺`-smaller one strictly
decreases the sum. This is the order fact Buchholz §4 (Lemma 4.1 / Thm 4.2) consumes in every descent
case. Proof: order-induction on `g`, each leading term folded via `icmp_insTerm_mono`. -/
lemma inadd_left_mono {X Y : V} (hX : isNF X) (hY : isNF Y) (hXY : icmp X Y = 0) :
    ∀ g, isNF g → icmp (inadd g X) (inadd g Y) = 0 := by
  intro g
  induction g using ISigma1.sigma1_order_induction
  · definability
  case ind g IH =>
    intro hg
    rcases eq_or_ne g 0 with rfl | hg0
    · rw [inadd_zero_left, inadd_zero_left]; exact hXY
    · obtain ⟨eg, cg, rg, rfl⟩ : ∃ eg cg rg, g = ocOadd eg cg rg :=
        ⟨_, _, _, (ocOadd_destruct hg0).symm⟩
      obtain ⟨hcg, heg, hrg, hside⟩ := (isNF_ocOadd eg cg rg).mp hg
      rw [inadd_ocOadd, inadd_ocOadd]
      have hrglt : rg < ocOadd eg cg rg := by
        have := ocTail_lt eg cg rg; rwa [ocTail_ocOadd] at this
      exact icmp_insTerm_mono (isNF_inadd hX rg hrg) (isNF_inadd hY rg hrg) (IH rg hrglt hrg)

/-! ## F3 — a single term is `≺` the next ω-power (`ω^β·k ≺ ω^{β+1}`)

The §4 `Ind`-rule assignment (`õ(d) = ω^{õ(d0)} # ω^{õ(d1)+1}`,
`CRUX2-ORD-ASSIGNMENT-2026-06-24.md`) raises the right summand's exponent to the **ordinal successor**
`β+1 = iadd β 1` (`1 = ocOadd 0 1 0`). The descent in case 4 needs that any single term with exponent `β`
sits below `ω^{β+1}`; this reduces to the foundational fact `β ≺ β+1`. -/

/-- **`β ≺ β + 1`** (any code is `≺` its ordinal successor). `iadd β 1` either bumps the trailing
exponent-0 coefficient (`ec = 0` branch — strictly larger coefficient) or grafts a `1` at the bottom of
the spine; in both cases the head/coeff above match and the comparison drops to the strictly-larger tail.
Strong induction down the spine of `β`. -/
lemma self_lt_iadd_one : ∀ w : V, ∀ a ≤ w, icmp a (iadd a (ocOadd 0 1 0)) = 0 := by
  intro w
  induction w using ISigma1.sigma1_order_induction
  · definability
  case ind w ih =>
    intro a haw
    rcases eq_or_ne a 0 with rfl | ha
    · rw [iadd_zero_left]; exact icmp_zero_pos (ocOadd_ne_zero 0 1 0)
    · obtain ⟨ec, n, rc, rfl⟩ : ∃ ec n rc, a = ocOadd ec n rc :=
        ⟨_, _, _, (ocOadd_destruct ha).symm⟩
      rw [iadd_ocOadd, if_neg (ocOadd_ne_zero (0 : V) 1 0), ocExp_ocOadd]
      by_cases h0 : icmp ec 0 = 0
      · exfalso
        rcases eq_or_ne ec 0 with rfl | hec
        · rw [icmp_zero_zero] at h0; exact absurd h0 (by simp)
        · rw [icmp_pos_zero hec] at h0; exact absurd h0 (by simp)
      · rw [if_neg h0]
        by_cases h1 : icmp ec 0 = 1
        · rw [if_pos h1, ocCoeff_ocOadd, ocTail_ocOadd, icmp_ocOadd, icmp_self ec ec le_rfl,
            thenV_one_left]
          have : cmpV n (n + 1) = 0 := cmpV_eq_zero.mpr (by simp)
          rw [this]; simp [thenV]
        · rw [if_neg h1, icmp_ocOadd, icmp_self ec ec le_rfl, cmpV_self, thenV_one_left,
            thenV_one_left]
          have hrc : rc < ocOadd ec n rc := by
            have := ocTail_lt ec n rc; rwa [ocTail_ocOadd] at this
          exact ih rc (lt_of_lt_of_le hrc haw) rc le_rfl

/-- **F3 — a single term is `≺` the next ω-power**: `ω^β·k ≺ ω^{β+1}` where `β+1 = iadd β 1`. The
leading exponents `β ≺ β+1` (`self_lt_iadd_one`) decide the lexicographic comparison outright. -/
lemma icmp_term_lt_omega_succ (β k : V) :
    icmp (ocOadd β k 0) (ocOadd (iadd β (ocOadd 0 1 0)) 1 0) = 0 := by
  rw [icmp_ocOadd, self_lt_iadd_one β β le_rfl]; simp [thenV]

/-! ### Right-successor normal form (`a + 1` stays NF) — for `õ`-NF of the I/Ind rules

`iotil_zIall`/`iotil_zIneg`/`iotil_zInd` all raise an exponent to the ordinal successor
`β + 1 = iadd β (ocOadd 0 1 0)`. To certify `isNF (iotil d)` on derivations (the `hnf` premise of the
degree-drop and cut descents), we need that adding `1` on the right preserves NF. Adding `1` on the
right either bumps the trailing finite coefficient or recurses into the tail; the leading exponent is
untouched, so NF (a descending-exponent spine) is preserved. -/

/-- **`ocExp` of a right-successor**: `ocExp (a + 1) = ocExp a` for `a ≠ 0`. -/
lemma ocExp_iadd_self_one {a : V} (ha : a ≠ 0) :
    ocExp (iadd a (ocOadd 0 1 0)) = ocExp a := by
  obtain ⟨ec, n, rc, rfl⟩ : ∃ ec n rc, a = ocOadd ec n rc :=
    ⟨_, _, _, (ocOadd_destruct ha).symm⟩
  rw [iadd_ocOadd, if_neg (ocOadd_ne_zero 0 1 0)]
  simp only [ocExp_ocOadd]
  by_cases h0 : icmp ec 0 = 0
  · exfalso
    rcases eq_or_ne ec 0 with rfl | hec
    · rw [icmp_zero_zero] at h0; exact absurd h0 (by simp)
    · rw [icmp_pos_zero hec] at h0; exact absurd h0 (by simp)
  · rw [if_neg h0]
    by_cases h1 : icmp ec 0 = 1
    · rw [if_pos h1, ocExp_ocOadd]
    · rw [if_neg h1, ocExp_ocOadd]

/-- **Right-successor NF (order-induction shell)**: `isNF a → isNF (a + 1)`, i.e.
`isNF (iadd a (ocOadd 0 1 0))`. Structural induction down the spine of `a`: the finite-head case
bumps the coefficient (`ocOadd ec (n+1) 0`), the infinite-head case recurses into the tail with the
leading exponent preserved (`ocExp_iadd_self_one`), so the descending-spine side condition transports. -/
lemma isNF_iadd_self_one : ∀ w : V, ∀ a ≤ w, isNF a → isNF (iadd a (ocOadd 0 1 0)) := by
  intro w
  induction w using ISigma1.sigma1_order_induction
  · definability
  case ind w ih =>
    intro a haw ha
    rcases eq_or_ne a 0 with rfl | ha0
    · rw [iadd_zero_left]
      exact (isNF_ocOadd 0 1 0).2 ⟨by simp, isNF_zero, isNF_zero, Or.inl rfl⟩
    · obtain ⟨ec, n, rc, rfl⟩ : ∃ ec n rc, a = ocOadd ec n rc :=
        ⟨_, _, _, (ocOadd_destruct ha0).symm⟩
      obtain ⟨hn, hec, hrc, hside⟩ := (isNF_ocOadd ec n rc).mp ha
      have hrclt : rc < ocOadd ec n rc := by
        have := ocTail_lt ec n rc; rwa [ocTail_ocOadd] at this
      rw [iadd_ocOadd, if_neg (ocOadd_ne_zero 0 1 0), ocExp_ocOadd]
      by_cases h0 : icmp ec 0 = 0
      · exfalso
        rcases eq_or_ne ec 0 with rfl | hecne
        · rw [icmp_zero_zero] at h0; exact absurd h0 (by simp)
        · rw [icmp_pos_zero hecne] at h0; exact absurd h0 (by simp)
      · rw [if_neg h0]
        by_cases h1 : icmp ec 0 = 1
        · rw [if_pos h1, ocCoeff_ocOadd, ocTail_ocOadd]
          exact (isNF_ocOadd ec (n + 1) 0).2 ⟨by simp, hec, isNF_zero, Or.inl rfl⟩
        · rw [if_neg h1]
          have hecne : ec ≠ 0 := fun h => h1 (by rw [h]; exact icmp_zero_zero)
          refine (isNF_ocOadd ec n (iadd rc (ocOadd 0 1 0))).2 ⟨hn, hec, ?_, ?_⟩
          · exact ih rc (lt_of_lt_of_le hrclt haw) rc le_rfl hrc
          · right
            rcases eq_or_ne rc 0 with rfl | hrc0
            · rw [iadd_zero_left, ocExp_ocOadd]; exact icmp_zero_pos hecne
            · rw [ocExp_iadd_self_one hrc0]
              rcases hside with h | h
              · exact absurd h hrc0
              · exact h

/-- **Right-successor NF** (the usable form): `isNF a → isNF (iadd a (ocOadd 0 1 0))`. -/
lemma isNF_iadd_one_right {a : V} (ha : isNF a) : isNF (iadd a (ocOadd 0 1 0)) :=
  isNF_iadd_self_one a a le_rfl ha

/-! ## F2 — a two-power natural sum below a larger ω-power (`ω^{α0} # ω^{α1} ≺ ω^{α}` when `α0,α1 ≺ α`)

The §4 `K^r`-rule assignment (`õ(d) = ω^{õ(d0)} # … # ω^{õ(dl)}`) reorganizes the immediate subderivation
ordinals into a natural sum of ω-powers. When all those exponents are `≺` a common `α`, the whole sum sits
below `ω^α` (its CNF is two terms, both with exponent `≺ α`). This is the two-term instance feeding the
critical/non-critical `K^r` split (Lemma 3.1). -/

/-- **F2 — `ω^{α0} # ω^{α1} ≺ ω^{α}`** when `α0 ≺ α` and `α1 ≺ α`. The natural sum collapses to a single
`insTerm` (`inadd_omega_pow`) whose lead exponent is `α0` or `α1` (`ocExp_insTerm`), both `≺ α`; the head
decides (`icmp_zero_of_exp_zero`). -/
lemma icmp_omega_pow_nadd_lt {α0 α1 α : V} (h0 : icmp α0 α = 0) (h1 : icmp α1 α = 0) :
    icmp (inadd (ocOadd α0 1 0) (ocOadd α1 1 0)) (ocOadd α 1 0) = 0 := by
  rw [inadd_omega_pow]
  refine icmp_zero_of_exp_zero (insTerm_ne_zero _ _ _) (ocOadd_ne_zero _ _ _) ?_
  rw [ocExp_ocOadd, ocExp_insTerm, if_neg (ocOadd_ne_zero _ _ _), ocExp_ocOadd]
  by_cases hc : icmp α0 α1 = 0
  · rw [if_pos hc]; exact h1
  · rw [if_neg hc]; exact h0

/-! ## F4 — commutativity of the natural sum `#`

`inadd a b = inadd b a` for NF `a, b`. The natural sum is order-independent: every leading term of `a`
and `b` lands at its `≺`-sorted position regardless of insertion order, merging coefficients on equal
exponents. This is the NF canonical-form fact Buchholz §4 needs to match `d[n]`'s reassembled ordinal
to `d`'s when the `K^r`-rule permutes summands. The crux is **`insTerm_comm`** (single-term insertions
commute); commutativity of the full fold then follows by `inadd_insTerm_comm` + `insTerm_prepend`. -/

/-- `insTerm` on a `>`-head: prepend the new term. -/
private lemma insTerm_gt {e n ec nc rc : V} (h : icmp e ec = 2) :
    insTerm e n (ocOadd ec nc rc) = ocOadd e n (ocOadd ec nc rc) := by
  rw [insTerm_ocOadd, if_pos h]

/-- `insTerm` on an `=`-head: merge coefficients. -/
private lemma insTerm_eq {e n ec nc rc : V} (h : icmp e ec = 1) :
    insTerm e n (ocOadd ec nc rc) = ocOadd e (n + nc) rc := by
  rw [insTerm_ocOadd, if_neg (by rw [h]; simp), if_pos h]

/-- `insTerm` on a `<`-head: keep the head, recurse into the tail. -/
private lemma insTerm_lt {e n ec nc rc : V} (h : icmp e ec = 0) :
    insTerm e n (ocOadd ec nc rc) = ocOadd ec nc (insTerm e n rc) := by
  rw [insTerm_ocOadd, if_neg (by rw [h]; simp), if_neg (by rw [h]; simp)]

/-- **Coefficient collection for equal ω-powers**: `ω^β·n # ω^β·m = ω^β·(n+m)`. The natural sum of two
single terms with the *same* exponent merges their coefficients (`insTerm_eq`). This is the algebra
behind "`k` copies of `ω^β` collect to `ω^β·k`" — the `Ind`-reduct `#`-fold (`õ(d[0]) = ω^{õ d0} #
ω^{õ d1}·k`, judge §2 LH4) reduces to it. -/
lemma inadd_omega_pow_collect (β n m : V) :
    inadd (ocOadd β n 0) (ocOadd β m 0) = ocOadd β (n + m) 0 := by
  rw [inadd_single_term, insTerm_eq (icmp_self β β le_rfl)]

/-- **Single-term insertions commute** (NF `b`): `insTerm e1 n1 (insTerm e2 n2 b) =
insTerm e2 n2 (insTerm e1 n1 b)`. Strong induction on `b`; a full 3×3 case split on
`(icmp e1 (ocExp b), icmp e2 (ocExp b))` — both-prepend reduces to a two-singleton commute, mixed
positions use `≺`-transitivity, both-recurse uses the IH on the tail, equal-exponent merges use
`add`-commutativity. -/
lemma insTerm_comm {e1 n1 e2 n2 : V} :
    ∀ b, isNF b → insTerm e1 n1 (insTerm e2 n2 b) = insTerm e2 n2 (insTerm e1 n1 b) := by
  have trans3 : ∀ x y z : V, icmp x y = 0 → icmp y z = 0 → icmp x z = 0 := fun x y z hxy hyz =>
    icmp_trans (max x (max y z)) x (le_max_left _ _) y
      (le_trans (le_max_left _ _) (le_max_right _ _)) z
      (le_trans (le_max_right _ _) (le_max_right _ _)) hxy hyz
  intro b
  induction b using ISigma1.sigma1_order_induction
  · definability
  case ind b IH =>
    intro hb
    rcases eq_or_ne b 0 with rfl | hb0
    · -- b = 0: two single terms.
      rw [insTerm_zero, insTerm_zero]
      rcases icmp_tri e1 e2 with h | h | h
      · rw [insTerm_lt h, insTerm_zero, insTerm_gt (icmp_two_iff_swap_zero.mpr h)]
      · have he : e1 = e2 :=
          icmp_eq_imp_eq (max e1 e2) e1 (le_max_left _ _) e2 (le_max_right _ _) h
        have h21 : icmp e2 e1 = 1 := by rw [he]; exact icmp_self e2 e2 le_rfl
        rw [insTerm_eq h, insTerm_eq h21, he, add_comm n1 n2]
      · rw [insTerm_gt h, insTerm_lt (icmp_two_iff_swap_zero.mp h), insTerm_zero]
    · obtain ⟨eb, nb, rb, rfl⟩ : ∃ eb nb rb, b = ocOadd eb nb rb :=
        ⟨_, _, _, (ocOadd_destruct hb0).symm⟩
      obtain ⟨hnb, heb, hrb, hside⟩ := (isNF_ocOadd eb nb rb).mp hb
      have hrblt : rb < ocOadd eb nb rb := by
        have := ocTail_lt eb nb rb; rwa [ocTail_ocOadd] at this
      rcases icmp_tri e1 eb with h1 | h1 | h1 <;> rcases icmp_tri e2 eb with h2 | h2 | h2
      · -- (0,0): both recurse into the tail; IH on rb.
        rw [insTerm_lt h2, insTerm_lt h1, insTerm_lt h1, insTerm_lt h2, IH rb hrblt hrb]
      · -- (0,1): e2 = eb; e1 ≺ eb.
        have he2 : e2 = eb :=
          icmp_eq_imp_eq (max e2 eb) e2 (le_max_left _ _) eb (le_max_right _ _) h2
        have h12 : icmp e1 e2 = 0 := by rw [he2]; exact h1
        rw [insTerm_eq h2, insTerm_lt h12, insTerm_lt h1, insTerm_eq h2]
      · -- (0,2): e1 ≺ eb ≺ e2.
        have h12 : icmp e1 e2 = 0 := trans3 e1 eb e2 h1 (icmp_two_iff_swap_zero.mp h2)
        rw [insTerm_gt h2, insTerm_lt h12, insTerm_lt h1, insTerm_gt h2]
      · -- (1,0): e1 = eb; e2 ≺ eb.
        have he1 : e1 = eb :=
          icmp_eq_imp_eq (max e1 eb) e1 (le_max_left _ _) eb (le_max_right _ _) h1
        have h21 : icmp e2 e1 = 0 := by rw [he1]; exact h2
        rw [insTerm_lt h2, insTerm_eq h1, insTerm_eq h1, insTerm_lt h21]
      · -- (1,1): e1 = eb = e2.
        have he1 : e1 = eb :=
          icmp_eq_imp_eq (max e1 eb) e1 (le_max_left _ _) eb (le_max_right _ _) h1
        have he2 : e2 = eb :=
          icmp_eq_imp_eq (max e2 eb) e2 (le_max_left _ _) eb (le_max_right _ _) h2
        have h12 : icmp e1 e2 = 1 := by rw [he1, he2]; exact icmp_self eb eb le_rfl
        have h21 : icmp e2 e1 = 1 := by rw [he1, he2]; exact icmp_self eb eb le_rfl
        rw [insTerm_eq h2, insTerm_eq h1, insTerm_eq h12, insTerm_eq h21, he1, he2, add_left_comm]
      · -- (1,2): e1 = eb ≺ e2.
        have he1 : e1 = eb :=
          icmp_eq_imp_eq (max e1 eb) e1 (le_max_left _ _) eb (le_max_right _ _) h1
        have h12 : icmp e1 e2 = 0 := by rw [he1]; exact icmp_two_iff_swap_zero.mp h2
        have h21 : icmp e2 e1 = 2 := by rw [he1]; exact h2
        rw [insTerm_gt h2, insTerm_lt h12, insTerm_eq h1, insTerm_gt h21]
      · -- (2,0): e2 ≺ eb ≺ e1.
        have h21 : icmp e2 e1 = 0 := trans3 e2 eb e1 h2 (icmp_two_iff_swap_zero.mp h1)
        rw [insTerm_lt h2, insTerm_gt h1, insTerm_gt h1, insTerm_lt h21, insTerm_lt h2]
      · -- (2,1): e2 = eb ≺ e1.
        have he2 : e2 = eb :=
          icmp_eq_imp_eq (max e2 eb) e2 (le_max_left _ _) eb (le_max_right _ _) h2
        have h12 : icmp e1 e2 = 2 := by rw [he2]; exact h1
        have h21 : icmp e2 e1 = 0 := by rw [he2]; exact icmp_two_iff_swap_zero.mp h1
        rw [insTerm_eq h2, insTerm_gt h12, insTerm_gt h1, insTerm_lt h21, insTerm_eq h2]
      · -- (2,2): both prepend; two-singleton commute on tail b.
        rw [insTerm_gt h2, insTerm_gt h1]
        rcases icmp_tri e1 e2 with h | h | h
        · rw [insTerm_lt h, insTerm_gt h1, insTerm_gt (icmp_two_iff_swap_zero.mpr h)]
        · have he : e1 = e2 :=
            icmp_eq_imp_eq (max e1 e2) e1 (le_max_left _ _) e2 (le_max_right _ _) h
          have h21 : icmp e2 e1 = 1 := by rw [he]; exact icmp_self e2 e2 le_rfl
          rw [insTerm_eq h, insTerm_eq h21, he, add_comm n1 n2]
        · rw [insTerm_gt h, insTerm_lt (icmp_two_iff_swap_zero.mp h), insTerm_gt h2]

/-- **Inserting commutes past the fold**: `inadd a (insTerm e n b) = insTerm e n (inadd a b)`
(NF `a`, NF `b`). Induction on `a`'s spine (`b` fixed); each leading term commutes past the insertion
via `insTerm_comm`. -/
lemma inadd_insTerm_comm {e n : V} (b : V) (hb : isNF b) : ∀ a, isNF a →
    inadd a (insTerm e n b) = insTerm e n (inadd a b) := by
  intro a
  induction a using ISigma1.sigma1_order_induction
  · definability
  case ind a IH =>
    intro ha
    rcases eq_or_ne a 0 with rfl | ha0
    · rw [inadd_zero_left, inadd_zero_left]
    · obtain ⟨ea, ca, ra, rfl⟩ : ∃ ea ca ra, a = ocOadd ea ca ra :=
        ⟨_, _, _, (ocOadd_destruct ha0).symm⟩
      obtain ⟨hca, hea, hra, hside⟩ := (isNF_ocOadd ea ca ra).mp ha
      have hralt : ra < ocOadd ea ca ra := by
        have := ocTail_lt ea ca ra; rwa [ocTail_ocOadd] at this
      rw [inadd_ocOadd, inadd_ocOadd, IH ra hralt hra,
        insTerm_comm _ (isNF_inadd hb ra hra)]

/-- **F4 — commutativity of the natural sum `#`**: `inadd a b = inadd b a` for NF `a, b`. Induction on
`a` (`b` fixed); the leading term of `a` commutes past the whole sum (`inadd_insTerm_comm`), and an NF
head re-prepends as itself (`insTerm_prepend`). -/
lemma inadd_comm (b : V) (hb : isNF b) : ∀ a, isNF a → inadd a b = inadd b a := by
  intro a
  induction a using ISigma1.sigma1_order_induction
  · definability
  case ind a IH =>
    intro ha
    rcases eq_or_ne a 0 with rfl | ha0
    · rw [inadd_zero_left]; exact (inadd_zero_right b hb).symm
    · obtain ⟨ea, ca, ra, rfl⟩ : ∃ ea ca ra, a = ocOadd ea ca ra :=
        ⟨_, _, _, (ocOadd_destruct ha0).symm⟩
      obtain ⟨hca, hea, hra, hside⟩ := (isNF_ocOadd ea ca ra).mp ha
      have hralt : ra < ocOadd ea ca ra := by
        have := ocTail_lt ea ca ra; rwa [ocTail_ocOadd] at this
      rw [inadd_ocOadd, IH ra hralt hra, ← inadd_insTerm_comm ra hra b hb,
        insTerm_prepend hside]

/-- **F1-mirror — strict right-monotonicity of the natural sum `#`.** `icmp X Y = 0 → icmp (X # g)
(Y # g) = 0` for NF `X, Y, g`: replacing one summand by a strictly `≺`-smaller one strictly decreases
the sum, even when that summand is *not* the leftmost (`#` is commutative — `inadd_comm`/F4 — so this
follows from `inadd_left_mono`/F1). Needed in the chain (`K^r`) descent cases where the reduced premise
sits at an arbitrary position in the `#`-fold (judge §8.3 N2). -/
lemma inadd_right_mono {X Y : V} (hX : isNF X) (hY : isNF Y) (hXY : icmp X Y = 0)
    (g : V) (hg : isNF g) : icmp (inadd X g) (inadd Y g) = 0 := by
  rw [inadd_comm g hg X hX, inadd_comm g hg Y hY]
  exact inadd_left_mono hX hY hXY g hg

end GoodsteinPA.InternalONote
