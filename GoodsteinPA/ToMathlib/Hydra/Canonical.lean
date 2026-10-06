/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/

module

public import GoodsteinPA.ToMathlib.Hydra.Statement
public meta import GoodsteinPA.ToMathlib.Hydra.Ordinal
public meta import GoodsteinPA.ToMathlib.Hydra.Statement
public import GoodsteinPA.ToMathlib.Hydra.Ordinal

@[expose] public section

/-
VENDORED from LeanGallery rev `a834bbad2f36eedcc16066b2bc4da49f98ab5b85`
(`LeanGallery/Logic/Hydra/`), verbatim except for the module-system header: this repo's root is a
`module`, and Lean 4.31 forbids a `module` from importing a non-`module`, so the gallery files
cannot be imported directly until the gallery migrates.  The namespace is kept as
`LeanGallery.Logic.Hydra` to record provenance and to keep the arc's `open` lines unchanged.
-/


/-!
# The canonical hydra battle

A single, computable Hercules strategy for the Kirby–Paris game, for use as the object of the
PA-independence result.

* `ord` (`Ordinal.lean`) — the Kirby–Paris ordinal of a hydra as a Cantor-normal-form `ONote`
  (natural sum `♯ ω^{ord c}` over the children).
* `canonStep n` — the move at turn `n`: descend along the **first child of minimal ordinal** until
  a head is reached, and chop it.  Order-independent up to ties (tied children have equal
  ordinals), so the battle follows the fundamental sequence of `ord` rather than the incidental
  list order.  Output shapes are exactly those of `Step.root` / `Chop.grand` / `Chop.deep`.
* `battle h k` — the hydra after `k` canonical moves from `h`, move `j` at turn `j` (so turn `j`
  leaves `j + 1` copies of the cut node, the survivor included, per `Chop.grand`).
* `ofCode` / `toCode` — a bijection `ℕ ≃ Hydra` (Cantor pairing), the input encoding.

Main results: `canonStep_legal` (every nonterminal canonical move is a legal `Step`),
`battle_terminates` (from `hydra_terminates`), `ofCode_toCode` / `ofCode_surjective`.
-/

namespace LeanGallery.Logic.Hydra
open Hydra

/-- Index of the canonical child: the FIRST child of minimal ordinal. -/
def pickIdx : List Hydra → ℕ
  | [] => 0
  | [_] => 0
  | c :: d :: cs =>
    let j := pickIdx (d :: cs)
    match (d :: cs)[j]? with
    | some e => if ONote.cmp (ord e) (ord c) == .lt then j + 1 else 0
    | none => 0

/-- The canonical regrowing chop with `node ds` as the local root (its canonical child is not a
head): descend along canonical children until the canonical child's canonical child is a head,
then regrow `n + 1` copies one level up.  Output shapes are exactly `Chop.grand` / `Chop.deep`'s. -/
def chopC (n : ℕ) : Hydra → Hydra
  | node ds =>
    match hd : ds[pickIdx ds]? with
    | none => node ds
    | some (node es) =>
      match es[pickIdx es]? with
      | none => node ds
      | some (node []) =>
        node (ds.eraseIdx (pickIdx ds) ++ List.replicate (n + 1) (node (es.eraseIdx (pickIdx es))))
      | some _ =>
        have : sizeOf es < sizeOf ds := by
          have hm : node es ∈ ds := List.mem_of_getElem? hd
          have := List.sizeOf_lt_of_mem hm
          simp only [node.sizeOf_spec] at this; omega
        node (chopC n (node es) :: ds.eraseIdx (pickIdx ds))
termination_by h => sizeOf h

/-- **The canonical move at turn `n`.**  The dead hydra stays dead; a canonical child that is a
head is removed (`Step.root`); otherwise `chopC`. -/
def canonStep (n : ℕ) : Hydra → Hydra
  | node cs =>
    match cs[pickIdx cs]? with
    | none => leaf
    | some (node []) => node (cs.eraseIdx (pickIdx cs))
    | some _ => chopC n (node cs)

/-- The canonical battle from `h`, move `j` at turn `j`. -/
def battle (h : Hydra) : ℕ → Hydra
  | 0 => h
  | k + 1 => canonStep k (battle h k)

theorem perm_pick {ds : List Hydra} {i : ℕ} {d : Hydra} (h : ds[i]? = some d) :
    List.Perm ds (d :: ds.eraseIdx i) := by
  obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.mp h
  exact (List.getElem_cons_eraseIdx_perm hi).symm

theorem pickIdx_lt : ∀ {l : List Hydra}, l ≠ [] → pickIdx l < l.length
  | [], h => (h rfl).elim
  | [_], _ => by simp [pickIdx]
  | c :: d :: cs, _ => by
    have ih := pickIdx_lt (l := d :: cs) (by simp)
    simp only [pickIdx]
    have hs : (d :: cs)[pickIdx (d :: cs)]? = some ((d :: cs)[pickIdx (d :: cs)]) :=
      List.getElem?_eq_getElem ih
    rw [hs]
    simp only [List.length_cons] at ih ⊢
    split <;> omega

theorem pick_some {l : List Hydra} (h : l ≠ []) : ∃ d, l[pickIdx l]? = some d :=
  ⟨_, List.getElem?_eq_getElem (pickIdx_lt h)⟩

/-- `chopC` is a legal regrowing chop whenever the canonical child is not a head. -/
theorem chopC_legal (n : ℕ) : ∀ (ds es : List Hydra),
    ds[pickIdx ds]? = some (node es) → es ≠ [] → Chop n (node ds) (chopC n (node ds))
  | ds, es, hd, hes => by
    have hm : node es ∈ ds := List.mem_of_getElem? hd
    have hsz := List.sizeOf_lt_of_mem hm
    simp only [Hydra.node.sizeOf_spec] at hsz
    obtain ⟨f, hf⟩ := pick_some hes
    rw [chopC.eq_1]
    split
    · simp_all
    · rename_i es' hd'
      rw [hd] at hd'; cases hd'
      split
      · simp_all
      · rename_i he'
        exact Chop.grand (perm_pick hd) (perm_pick he')
      · rename_i g _ _
        obtain ⟨gs⟩ := g
        have hgs : gs ≠ [] := by rintro rfl; exact ‹node [] = node [] → False› rfl
        have : sizeOf es < sizeOf ds := by omega
        exact Chop.deep (perm_pick hd) (chopC_legal n es gs ‹es[pickIdx es]? = some (node gs)› hgs)
termination_by ds => sizeOf ds

/-- **Bridge: every nonterminal canonical move is a legal gallery `Step` at its turn.** -/
theorem canonStep_legal (n : ℕ) (h : Hydra) (hh : h ≠ leaf) : Step n h (canonStep n h) := by
  obtain ⟨cs⟩ := h
  have hcs : cs ≠ [] := by rintro rfl; exact hh rfl
  obtain ⟨c, hc⟩ := pick_some hcs
  obtain ⟨es⟩ := c
  rw [canonStep.eq_1]
  split
  · simp_all
  · rename_i hc'
    exact Step.root (perm_pick hc')
  · rename_i g _ _
    have hc' : cs[pickIdx cs]? = some g := ‹_›
    rw [hc] at hc'; cases hc'
    have hes : es ≠ [] := by rintro rfl; exact ‹node [] = node [] → False› rfl
    exact Step.chop (chopC_legal n cs es hc hes)

/-! ### P1: a canonical move is one fundamental-sequence step of `ord` -/

/-- The canonical child has minimal ordinal. -/
theorem pickIdx_min : ∀ {l : List Hydra} {c : Hydra}, l[pickIdx l]? = some c → ∀ x ∈ l, ord c ≤ ord x
  | [], _, h, _, _ => by simp at h
  | [y], c, h, x, hx => by
    simp [pickIdx] at h; subst h
    simp at hx; subst hx; exact le_rfl
  | y :: z :: rest, c, h, x, hx => by
    obtain ⟨e, he⟩ := pick_some (l := z :: rest) (by simp)
    have ih := pickIdx_min he
    have hy : (ord y).NF := ord_NF y
    have hoe : (ord e).NF := ord_NF e
    simp only [pickIdx, he] at h
    split at h
    · rename_i hlt
      have hlt' : ord e < ord y := by
        have hc := ONote.cmp_compares (ord e) (ord y)
        simp only [beq_iff_eq] at hlt
        rw [hlt] at hc; exact hc
      have hce : c = e := by
        have : (z :: rest)[pickIdx (z :: rest)]? = some c := by simpa using h
        rw [he] at this; exact (Option.some.inj this).symm
      subst hce
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact le_of_lt hlt'
      · exact ih x hx'
    · rename_i hnlt
      have hcy : c = y := by simpa using h.symm
      subst hcy
      have hle : ord c ≤ ord e := by
        rcases trich (ord e) (ord c) with h' | h' | h'
        · exact absurd (by simp [cmp_eq_lt h']) hnlt
        · rw [h']
        · exact le_of_lt h'
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact le_rfl
      · exact le_trans hle (ih x hx')

/-- Splitting off the canonical child: `ord (node cs) = ord rest ♯ ω^{ord c}`, and `ord c` is at
most every exponent of `ord rest`. -/
theorem ord_decomp {cs : List Hydra} {c : Hydra} (hc : cs[pickIdx cs]? = some c) :
    ord (node cs) = insertTerm (ord c) (ord (node (cs.eraseIdx (pickIdx cs)))) ∧
      AllGE (ord c) (ord (node (cs.eraseIdx (pickIdx cs)))) := by
  refine ⟨?_, ?_⟩
  · rw [ord_perm (perm_pick hc), ord_node, ord_node]
    rfl
  · rw [ord_node]
    refine allGE_sumTerms _ fun x hx => ?_
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hx
    exact ⟨ord_NF d, pickIdx_min hc d (List.mem_of_mem_eraseIdx hd)⟩

/-- **P1 at a local root**: when the canonical child is not a head, `ord` is a limit and the
regrowing chop at turn `n` lands exactly on its `n`-th fundamental-sequence element. -/
theorem ord_chopC (n : ℕ) : ∀ (ds es : List Hydra),
    ds[pickIdx ds]? = some (node es) → es ≠ [] →
      ∃ f, ONote.fundamentalSequence (ord (node ds)) = Sum.inr f ∧ ord (chopC n (node ds)) = f n
  | ds, es, hd, hes => by
    have hm : node es ∈ ds := List.mem_of_getElem? hd
    have hsz := List.sizeOf_lt_of_mem hm
    simp only [Hydra.node.sizeOf_spec] at hsz
    obtain ⟨hdec, hall⟩ := ord_decomp hd
    have hcNF : (ord (node es)).NF := ord_NF _
    have hrNF : (ord (node (ds.eraseIdx (pickIdx ds)))).NF := ord_NF _
    rw [chopC.eq_1]
    split
    · simp_all
    · rename_i es' hd'
      rw [hd] at hd'; cases hd'
      split
      · rename_i hnone
        have := pickIdx_lt hes
        simp at hnone
        omega
      · -- grand: the canonical grandchild is a head; `ord (node es)` is a successor
        rename_i he'
        obtain ⟨hdec', _⟩ := ord_decomp he'
        have hs : ONote.fundamentalSequence (ord (node es)) =
            Sum.inl (some (ord (node (es.eraseIdx (pickIdx es))))) := by
          rw [hdec', ord_leaf]
          have : (ord (node (es.eraseIdx (pickIdx es)))).NF := ord_NF _
          exact fundamentalSequence_insertTerm_zero _
        refine ⟨_, by rw [hdec]; exact fundamentalSequence_insertTerm_succ hs _ hall, ?_⟩
        rw [ord_perm List.perm_append_comm, ord_node, List.map_append, List.map_replicate,
          sumTerms_replicate_append, ← ord_node]
      · -- deep: recurse into the canonical child
        rename_i g _ _
        obtain ⟨gs⟩ := g
        have hgs : gs ≠ [] := by rintro rfl; exact ‹node [] = node [] → False› rfl
        have : sizeOf es < sizeOf ds := by omega
        obtain ⟨f, hf, hfn⟩ := ord_chopC n es gs ‹es[pickIdx es]? = some (node gs)› hgs
        refine ⟨_, by rw [hdec]; exact fundamentalSequence_insertTerm_limit hf _ hall, ?_⟩
        show ord (node (chopC n (node es) :: ds.eraseIdx (pickIdx ds))) = _
        rw [ord_node, List.map_cons, hfn, ord_node]
        rfl
termination_by ds => sizeOf ds

/-- **P1**: a canonical move on a live hydra is one step of the fundamental sequence of its
ordinal — the predecessor when `ord h` is a successor, the `n`-th element when it is a limit. -/
theorem ord_canonStep (n : ℕ) (h : Hydra) (hh : h ≠ leaf) :
    ONote.fundamentalSequence (ord h) = Sum.inl (some (ord (canonStep n h))) ∨
      ∃ f, ONote.fundamentalSequence (ord h) = Sum.inr f ∧ ord (canonStep n h) = f n := by
  obtain ⟨cs⟩ := h
  have hcs : cs ≠ [] := by rintro rfl; exact hh rfl
  obtain ⟨c, hc⟩ := pick_some hcs
  obtain ⟨es⟩ := c
  obtain ⟨hdec, hall⟩ := ord_decomp hc
  have : (ord (node (cs.eraseIdx (pickIdx cs)))).NF := ord_NF _
  rw [canonStep.eq_1]
  split
  · simp_all
  · rename_i hc'
    rw [hc] at hc'; cases hc'
    left
    rw [hdec, ord_leaf]
    exact fundamentalSequence_insertTerm_zero (ord (node (cs.eraseIdx (pickIdx cs))))
  · rename_i g _ _
    have hc' : cs[pickIdx cs]? = some g := ‹_›
    rw [hc] at hc'; cases hc'
    have hes : es ≠ [] := by rintro rfl; exact ‹node [] = node [] → False› rfl
    right
    exact ord_chopC n cs es hc hes

/-- The canonical battle terminates (the positive theorem PA will be shown unable to prove). -/
theorem battle_terminates (h : Hydra) : ∃ N, battle h N = leaf :=
  hydra_terminates (turn := id) fun k hk => canonStep_legal k (battle h k) hk

/-- **Input encoding (a bijection `ℕ ≃ Hydra`).**  `0` is the single head `leaf`;
`n + 1` with `n = ⟪a, b⟫` (Cantor pairing, `Nat.unpair`) is the hydra `ofCode b` with the extra
child `ofCode a` put in front. -/
def ofCode : ℕ → Hydra
  | 0 => leaf
  | n + 1 =>
    have := Nat.unpair_left_le n
    have := Nat.unpair_right_le n
    match ofCode n.unpair.2 with
    | node cs => node (ofCode n.unpair.1 :: cs)
termination_by n => n
decreasing_by all_goals omega

/-- The inverse of `ofCode`. -/
def toCode : Hydra → ℕ
  | node [] => 0
  | node (c :: cs) => Nat.pair (toCode c) (toCode (node cs)) + 1

theorem ofCode_toCode : ∀ h, ofCode (toCode h) = h
  | node [] => by simp [toCode, ofCode, leaf]
  | node (c :: cs) => by
    rw [toCode, ofCode]
    simp only [Nat.unpair_pair]
    rw [ofCode_toCode (node cs), ofCode_toCode c]

/-- Anti-vacuity for "every code": every hydra has a code. -/
theorem ofCode_surjective : Function.Surjective ofCode := fun h => ⟨toCode h, ofCode_toCode h⟩

end LeanGallery.Logic.Hydra

/-! ### Ground-truth anchors (hand-computed battle lengths)

`Hydra` has no `DecidableEq` (nested inductive), so each anchor compares codes: `toCode h = 0`
iff `h = leaf`.  The definitions are well-founded, so these run by `native_decide`. -/

section Anchors
open LeanGallery.Logic.Hydra Hydra

/-- `ord = 1`: one move. -/
example : toCode (battle (node [leaf]) 1) = 0 := by native_decide
/-- `ord = ω`: turn 0 regrows one head (`node [leaf]`, code 1), turn 1 chops it. -/
example : toCode (battle (node [node [leaf]]) 1) = 1 ∧ toCode (battle (node [node [leaf]]) 2) = 0 := by
  native_decide
/-- `ord = ω + 1`: the head goes first, then `ω` at turn 1 regrows two heads: four moves. -/
example : toCode (battle (node [leaf, node [leaf]]) 3) ≠ 0 ∧
    toCode (battle (node [leaf, node [leaf]]) 4) = 0 := by
  native_decide
/-- The coding is a bijection on an initial segment. -/
example : (List.range 12).map (fun n => toCode (ofCode n)) = List.range 12 := by native_decide

end Anchors

end
