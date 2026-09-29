/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/

module

public import GoodsteinPA.ToMathlib.Hydra.Basic
public import Mathlib.SetTheory.Ordinal.Notation
public import Mathlib.Tactic.Order

@[expose] public section

/-
VENDORED from LeanGallery rev `a834bbad2f36eedcc16066b2bc4da49f98ab5b85`
(`LeanGallery/Logic/Hydra/`), verbatim except for the module-system header: this repo's root is a
`module`, and Lean 4.31 forbids a `module` from importing a non-`module`, so the gallery files
cannot be imported directly until the gallery migrates.  The namespace is kept as
`LeanGallery.Logic.Hydra` to record provenance and to keep the arc's `open` lines unchanged.
-/


/-!
# The Kirby–Paris ordinal of a hydra, as a Cantor normal form

`insertTerm e α` adds one term `ω^e` to the Cantor normal form `α` at its sorted position (bumping
a coefficient when the exponent is already present) — the natural sum `α ♯ ω^e`.  The ordinal of a
hydra folds it over the children: `ord (node cs) = ♯_{c ∈ cs} ω^{ord c}`.
-/

set_option linter.dupNamespace false

namespace LeanGallery.Logic.Hydra

open ONote Hydra

/-- Natural sum with one term: insert `ω^e` into the Cantor normal form `α`. -/
def insertTerm (e : ONote) : ONote → ONote
  | 0 => oadd e 1 0
  | oadd a n b =>
    match ONote.cmp e a with
    | .gt => oadd e 1 (oadd a n b)
    | .eq => oadd a (n + 1) b
    | .lt => oadd a n (insertTerm e b)

theorem insertTerm_nfBelow {e : ONote} (he : e.NF) :
    ∀ {α : ONote} {β : Ordinal}, NFBelow α β → ONote.repr e < β → NFBelow (insertTerm e α) β := by
  intro α β h
  induction h with
  | zero => intro hlt; exact NFBelow.oadd he NFBelow.zero hlt
  | @oadd' a n b eb β h₁ h₂ h₃ _ ih₂ =>
    intro hlt
    have : a.NF := ⟨⟨_, h₁⟩⟩
    have := he
    have hc := ONote.cmp_compares e a
    simp only [insertTerm]
    cases hcmp : ONote.cmp e a with
    | lt =>
      rw [hcmp] at hc
      exact NFBelow.oadd' h₁ (ih₂ (lt_def.mp hc)) h₃
    | eq =>
      rw [hcmp] at hc
      exact NFBelow.oadd' h₁ h₂ h₃
    | gt =>
      rw [hcmp] at hc
      have hNF : (oadd a n b).NF := ⟨⟨_, NFBelow.oadd' h₁ h₂ h₃⟩⟩
      exact NFBelow.oadd he (hNF.below_of_lt (lt_def.mp hc)) hlt

instance insertTerm_NF (e α : ONote) [he : e.NF] [hα : α.NF] : (insertTerm e α).NF := by
  obtain ⟨⟨β, hβ⟩⟩ := hα
  exact ⟨⟨_, insertTerm_nfBelow he (hβ.mono (le_max_left β (Order.succ (ONote.repr e))))
    (lt_of_lt_of_le (Order.lt_succ _) (le_max_right _ _))⟩⟩

/-- Adding one head (`ω^0 = 1`) is a successor: its fundamental "sequence" is its predecessor. -/
theorem fundamentalSequence_insertTerm_zero :
    ∀ (α : ONote) [α.NF], fundamentalSequence (insertTerm 0 α) = Sum.inl (some α)
  | 0, _ => rfl
  | oadd a n b, hNF => by
    have ha : a.NF := hNF.fst
    have hb : b.NF := hNF.snd
    by_cases ha0 : a = 0
    · subst ha0
      have hb0 : b = 0 := hNF.zero_of_zero rfl
      subst hb0
      have : ONote.cmp 0 0 = .eq := rfl
      simp only [insertTerm, this]
      obtain ⟨k, hk⟩ : ∃ k : ℕ, (n : ℕ) = k + 1 := ⟨(n : ℕ) - 1, by have := n.pos; omega⟩
      have hnp : (n + 1 : ℕ+).natPred = k + 1 := by
        simp [PNat.natPred, hk]
      simp only [fundamentalSequence, hnp]
      congr
      exact PNat.eq (by simp [hk])
    · have hlt : ONote.cmp 0 a = .lt := by
        have hc := ONote.cmp_compares 0 a
        cases h : ONote.cmp 0 a with
        | lt => rfl
        | eq => rw [h] at hc; exact (ha0 hc.symm).elim
        | gt =>
          rw [h] at hc
          have := lt_def.mp hc
          simp at this
      simp only [insertTerm, hlt]
      have ih := fundamentalSequence_insertTerm_zero b
      simp only [fundamentalSequence, ih]

/-- `e` is at most every exponent of the Cantor normal form `α`. -/
def AllGE (e : ONote) : ONote → Prop
  | 0 => True
  | oadd a _ b => e ≤ a ∧ AllGE e b

theorem cmp_eq_lt {x y : ONote} [x.NF] [y.NF] (h : x < y) : ONote.cmp x y = .lt := by
  have hc := ONote.cmp_compares x y
  cases hxy : ONote.cmp x y with
  | lt => rfl
  | eq => rw [hxy] at hc; subst hc; exact (lt_irrefl _ h).elim
  | gt => rw [hxy] at hc; exact (lt_asymm h hc).elim

theorem cmp_self {x : ONote} [x.NF] : ONote.cmp x x = .eq := by
  have hc := ONote.cmp_compares x x
  cases hxy : ONote.cmp x x with
  | lt => rw [hxy] at hc; exact (lt_irrefl _ hc).elim
  | eq => rfl
  | gt => rw [hxy] at hc; exact (lt_irrefl _ hc).elim

/-- In a normal form, a term whose exponent equals the inserted one has an empty tail below it. -/
theorem tail_zero_of_allGE {e b : ONote} {n : ℕ+} (hNF : (oadd e n b).NF)
    (hall : AllGE e b) : b = 0 := by
  cases b with
  | zero => rfl
  | oadd a' n' b' =>
    have hlt : a' < e := by
      have := hNF.snd'
      exact lt_def.mpr this.lt
    exact (not_le.mpr (lt_def.mp hlt) (le_def.mp hall.1)).elim

/-- **Limit exponent.**  Inserting `ω^e` below every term, with `e` a limit (`fs e = inr g`),
gives the sequence `i ↦ α ♯ ω^{g i}`. -/
theorem fundamentalSequence_insertTerm_limit {e : ONote} [he : e.NF] {g : ℕ → ONote}
    (hg : fundamentalSequence e = Sum.inr g) :
    ∀ (α : ONote) [α.NF], AllGE e α →
      fundamentalSequence (insertTerm e α) = Sum.inr fun i => insertTerm (g i) α
  | 0, _, _ => by
    simp only [insertTerm, fundamentalSequence, hg]
    rfl
  | oadd a n b, hα, hall => by
    have hprop := fundamentalSequence_has_prop e
    rw [hg] at hprop
    have hgi : ∀ i, g i < e ∧ (g i).NF := fun i => ⟨(hprop.2.1 i).2.1, (hprop.2.1 i).2.2 he⟩
    have ha : a.NF := hα.fst
    have hb : b.NF := hα.snd
    obtain ⟨hea, hallb⟩ := hall
    rcases lt_or_eq_of_le (le_def.mp hea) with hlt | heq
    · -- `e < a`: the insertion happens in the tail
      have hlt' : e < a := lt_def.mpr hlt
      have hc : ONote.cmp e a = .lt := cmp_eq_lt hlt'
      have hc' : ∀ i, ONote.cmp (g i) a = .lt := fun i => by
        have := (hgi i).2; exact cmp_eq_lt (lt_trans (hgi i).1 hlt')
      have ih := fundamentalSequence_insertTerm_limit hg b hallb
      simp only [insertTerm, hc, hc', fundamentalSequence, ih]
    · -- `e = a`: bump the last coefficient; the tail is empty
      have hea' : e = a := (repr_inj).mp heq
      subst hea'
      have hb0 : b = 0 := tail_zero_of_allGE hα hallb
      subst hb0
      have hc' : ∀ i, ONote.cmp (g i) e = .lt := fun i => by
        have := (hgi i).2; exact cmp_eq_lt (hgi i).1
      obtain ⟨k, hk⟩ : ∃ k : ℕ, (n : ℕ) = k + 1 := ⟨(n : ℕ) - 1, by have := n.pos; omega⟩
      have hnp : (n + 1 : ℕ+).natPred = k + 1 := by simp [PNat.natPred, hk]
      simp only [insertTerm, cmp_self, hc', fundamentalSequence, hg, hnp]
      congr 1
      funext i
      congr 1
      exact PNat.eq (by simp [hk])

theorem iterate_insertTerm_zero {e : ONote} [e.NF] :
    ∀ k : ℕ, (insertTerm e)^[k + 1] 0 = oadd e k.succPNat 0
  | 0 => rfl
  | k + 1 => by
    rw [Function.iterate_succ_apply', iterate_insertTerm_zero k]
    simp only [insertTerm, cmp_self]
    congr 1

theorem iterate_insertTerm_oadd {e a : ONote} [e.NF] [a.NF] (h : e < a) (n : ℕ+) :
    ∀ (k : ℕ) (X : ONote), (insertTerm e)^[k] (oadd a n X) = oadd a n ((insertTerm e)^[k] X)
  | 0, _ => rfl
  | k + 1, X => by
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', iterate_insertTerm_oadd h n k X]
    simp only [insertTerm, cmp_eq_lt h]

/-- **Successor exponent.**  Inserting `ω^e` below every term, with `e = e' + 1`
(`fs e = inl (some e')`), gives the sequence `i ↦ α ♯ ω^{e'}·(i+1)` — the Kirby–Paris regrowth of
`i + 1` copies. -/
theorem fundamentalSequence_insertTerm_succ {e e' : ONote} [he : e.NF]
    (hs : fundamentalSequence e = Sum.inl (some e')) :
    ∀ (α : ONote) [α.NF], AllGE e α →
      fundamentalSequence (insertTerm e α) = Sum.inr fun i => (insertTerm e')^[i + 1] α
  | 0, _, _ => by
    have hprop := fundamentalSequence_has_prop e
    rw [hs] at hprop
    have he' : e'.NF := hprop.2 he
    have h1 : (1 : ℕ+).natPred = 0 := rfl
    simp only [insertTerm, fundamentalSequence, hs, h1]
    congr 1
    funext i
    rw [iterate_insertTerm_zero]
    rfl
  | oadd a n b, hα, hall => by
    have hprop := fundamentalSequence_has_prop e
    rw [hs] at hprop
    have he' : e'.NF := hprop.2 he
    have he'e : e' < e := lt_def.mpr (by rw [hprop.1]; exact Order.lt_succ _)
    have ha : a.NF := hα.fst
    have hb : b.NF := hα.snd
    obtain ⟨hea, hallb⟩ := hall
    rcases lt_or_eq_of_le (le_def.mp hea) with hlt | heq
    · have hlt' : e < a := lt_def.mpr hlt
      have ih := fundamentalSequence_insertTerm_succ hs b hallb
      simp only [insertTerm, cmp_eq_lt hlt', fundamentalSequence, ih]
      congr 1
      funext i
      rw [iterate_insertTerm_oadd (lt_trans he'e hlt')]
    · have hea' : e = a := (repr_inj).mp heq
      subst hea'
      have hb0 : b = 0 := tail_zero_of_allGE hα hallb
      subst hb0
      obtain ⟨k, hk⟩ : ∃ k : ℕ, (n : ℕ) = k + 1 := ⟨(n : ℕ) - 1, by have := n.pos; omega⟩
      have hnp : (n + 1 : ℕ+).natPred = k + 1 := by simp [PNat.natPred, hk]
      simp only [insertTerm, cmp_self, fundamentalSequence, hs, hnp]
      congr 1
      funext i
      rw [iterate_insertTerm_oadd he'e, iterate_insertTerm_zero]
      congr 1
      exact PNat.eq (by simp [hk])

theorem cmp_eq_gt {x y : ONote} [x.NF] [y.NF] (h : y < x) : ONote.cmp x y = .gt := by
  have hc := ONote.cmp_compares x y
  cases hxy : ONote.cmp x y with
  | lt => rw [hxy] at hc; exact (lt_asymm h hc).elim
  | eq => rw [hxy] at hc; subst hc; exact (lt_irrefl _ h).elim
  | gt => rfl

/-- Trichotomy for normal forms, as the three `cmp` outcomes. -/
theorem trich (x y : ONote) [x.NF] [y.NF] : x < y ∨ x = y ∨ y < x := by
  rcases lt_trichotomy (ONote.repr x) (ONote.repr y) with h | h | h
  · exact Or.inl (lt_def.mpr h)
  · exact Or.inr (Or.inl (repr_inj.mp h))
  · exact Or.inr (Or.inr (lt_def.mpr h))

theorem insertTerm_comm (e f : ONote) [e.NF] [f.NF] :
    ∀ (α : ONote) [α.NF], insertTerm e (insertTerm f α) = insertTerm f (insertTerm e α)
  | 0, _ => by
    rcases trich e f with h | h | h
    · simp [insertTerm, cmp_eq_lt h, cmp_eq_gt h]
    · subst h; rfl
    · simp [insertTerm, cmp_eq_lt h, cmp_eq_gt h]
  | oadd a n b, hα => by
    have ha : a.NF := hα.fst
    have hb : b.NF := hα.snd
    have ih := insertTerm_comm e f b
    rcases trich e a with h1 | h1 | h1 <;> rcases trich f a with h2 | h2 | h2 <;>
      rcases trich e f with h3 | h3 | h3
    all_goals first
      | (exfalso; subst_vars; simp only [lt_def] at *; order)
      | skip
    all_goals subst_vars
    all_goals simp only [insertTerm, cmp_eq_lt, cmp_eq_gt, cmp_self, *]

/-- Natural sum of `ω^e` over a list of exponents. -/
def sumTerms (l : List ONote) : ONote := l.foldr insertTerm 0

theorem sumTerms_NF : ∀ (l : List ONote), (∀ x ∈ l, x.NF) → (sumTerms l).NF
  | [], _ => NF.zero
  | x :: l, h => by
    have : x.NF := h x (by simp)
    have : (sumTerms l).NF := sumTerms_NF l fun y hy => h y (by simp [hy])
    exact insertTerm_NF x (sumTerms l)

/-- The natural sum is independent of the order of the terms. -/
theorem sumTerms_perm {l₁ l₂ : List ONote} (hp : l₁.Perm l₂) (hNF : ∀ x ∈ l₁, x.NF) :
    sumTerms l₁ = sumTerms l₂ := by
  induction hp with
  | nil => rfl
  | cons x _ ih =>
    simp only [sumTerms, List.foldr_cons] at ih ⊢
    rw [ih fun y hy => hNF y (by simp [hy])]
  | swap x y l =>
    simp only [sumTerms, List.foldr_cons]
    have : x.NF := hNF x (by simp)
    have : y.NF := hNF y (by simp)
    have : (l.foldr insertTerm 0).NF := sumTerms_NF l fun z hz => hNF z (by simp [hz])
    exact insertTerm_comm y x _
  | trans h₁₂ _ ih₁ ih₂ =>
    rw [ih₁ hNF, ih₂ fun y hy => hNF y (h₁₂.symm.subset hy)]

/-- **The Kirby–Paris ordinal of a hydra**: `ord (node cs) = ♯_{c ∈ cs} ω^{ord c}`. -/
def ord : Hydra → ONote
  | node cs => sumTerms (cs.attach.map fun ⟨c, _⟩ => ord c)

theorem ord_node (cs : List Hydra) : ord (node cs) = sumTerms (cs.map ord) := by
  rw [ord]
  congr 1
  simp

@[simp] theorem ord_leaf : ord (node []) = 0 := by
  rw [ord_node]; rfl

theorem ord_NF : ∀ h : Hydra, (ord h).NF
  | node cs => by
    rw [ord_node]
    exact sumTerms_NF _ fun x hx => by
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
      exact ord_NF c

theorem ord_perm {cs ds : List Hydra} (h : cs.Perm ds) : ord (node cs) = ord (node ds) := by
  rw [ord_node, ord_node]
  exact sumTerms_perm (h.map ord) fun x hx => by
    obtain ⟨c, _, rfl⟩ := List.mem_map.mp hx
    exact ord_NF c

theorem allGE_insertTerm {e f : ONote} [f.NF] (hef : e ≤ f) :
    ∀ (α : ONote) [α.NF], AllGE e α → AllGE e (insertTerm f α)
  | 0, _, _ => ⟨hef, trivial⟩
  | oadd a n b, hα, hall => by
    have ha : a.NF := hα.fst
    have hb : b.NF := hα.snd
    rcases trich f a with h | h | h
    · simp only [insertTerm, cmp_eq_lt h]
      exact ⟨hall.1, allGE_insertTerm hef b hall.2⟩
    · subst h; simp only [insertTerm, cmp_self]; exact hall
    · simp only [insertTerm, cmp_eq_gt h]; exact ⟨hef, hall⟩

theorem allGE_sumTerms {e : ONote} :
    ∀ (l : List ONote), (∀ x ∈ l, x.NF ∧ e ≤ x) → AllGE e (sumTerms l)
  | [], _ => trivial
  | x :: l, h => by
    have hx := h x (by simp)
    have : x.NF := hx.1
    have : (sumTerms l).NF := sumTerms_NF l fun y hy => (h y (by simp [hy])).1
    show AllGE e (insertTerm x (sumTerms l))
    exact allGE_insertTerm hx.2 (sumTerms l) (allGE_sumTerms l fun y hy => h y (by simp [hy]))

theorem sumTerms_replicate_append (x : ONote) :
    ∀ (k : ℕ) (l : List ONote), sumTerms (List.replicate k x ++ l) = (insertTerm x)^[k] (sumTerms l)
  | 0, _ => rfl
  | k + 1, l => by
    rw [Function.iterate_succ_apply', ← sumTerms_replicate_append x k l]
    simp [sumTerms, List.replicate_succ]

end LeanGallery.Logic.Hydra

end
