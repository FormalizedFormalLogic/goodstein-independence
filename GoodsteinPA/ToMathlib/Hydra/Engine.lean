/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/

module

public import GoodsteinPA.ToMathlib.Hydra.Basic
public import Mathlib.Logic.Hydra
public import Mathlib.Tactic.Abel

@[expose] public section

/-
VENDORED from LeanGallery rev `a834bbad2f36eedcc16066b2bc4da49f98ab5b85`
(`LeanGallery/Logic/Hydra/`), verbatim except for the module-system header: this repo's root is a
`module`, and Lean 4.31 forbids a `module` from importing a non-`module`, so the gallery files
cannot be imported directly until the gallery migrates.  The namespace is kept as
`LeanGallery.Logic.Hydra` to record provenance and to keep the arc's `open` lines unchanged.
-/


/-!
# Kirby–Paris hydra — proof engine (well-founded descent)

This file is the machinery behind `hydra_terminates`. It is NOT part of the audit
surface (that is `Basic`/`Statement`); it just has to be correct, which the kernel
checks.

## Strategy

Every chop strictly lowers the Kirby–Paris ordinal of the hydra (its value `< ε₀`,
the natural sum `♯ ωᵒ⁽ᶜ⁾` over children). Rather than build that ordinal by hand
(mathlib's `Ordinal.nadd` natural sum was removed), we realize the *same* well-order
as a **recursive multiset (path) order** `HLt` on trees and reuse mathlib's hydra
engine `Relation.CutExpand`:

* `HLt (node s') (node s)` holds when `s'` is obtained from `s` by removing one child
  `a` and grafting back finitely many children all `HLt`-below `a` — i.e. one
  `CutExpand HLt` step on the child multisets. (We pin the removed `a ∈ s` into the
  definition; this makes irreflexivity a plain structural induction and breaks the
  bootstrap with well-foundedness.)
* `HLt` is **well-founded**: `node` transports `Relation.WellFounded.cutExpand`'s
  accessibility through the tree (`acc_node`), and a structural induction supplies the
  children's accessibility.
* Every legal `Step` strictly descends `HLt` (`step_hlt`); the depth-one and grandparent
  regrowth cases are both instances of the atomic "remove a head" decrease
  (`hlt_eraseHead`), lifted by the single-replacement congruence built into `HLt`.

Then a battle is `HLt`-decreasing while alive, and `WellFounded.has_min` forbids an
infinite one — mirroring Goodstein's `Engine.lean`.
-/

namespace LeanGallery.Logic.Hydra

open Hydra Relation

/-- **Recursive multiset (path) order on hydras.** `HLt x y` means `x` is one
Kirby–Paris descent below `y`: writing `x = node s'`, `y = node s`, the child multiset
`s'` is `s` with one child `a` (pinned present, `a ∈ s`) removed and an arbitrary finite
multiset `t` of strictly-`HLt`-smaller children grafted back. This is exactly a
`Relation.CutExpand HLt` step on the children, and its rank is the Kirby–Paris ordinal
`< ε₀`. -/
inductive HLt : Hydra → Hydra → Prop
  | mk {s' s t : List Hydra} {a : Hydra} (ha : a ∈ s) (hr : ∀ a' ∈ t, HLt a' a)
      (he : (s' : Multiset Hydra) + {a} = (s : Multiset Hydra) + (t : Multiset Hydra)) :
      HLt (node s') (node s)

/-- `HLt` is irreflexive. Structural induction on the tree: a self-loop
`HLt (node s) (node s)` forces (after cancelling `↑s`) the grafted multiset to be the
single removed child `a ∈ s`, so `HLt a a` — impossible by induction on that child. -/
theorem hlt_irrefl : ∀ h : Hydra, ¬ HLt h h := by
  intro h
  induction h with
  | _ s ih =>
    intro hh
    cases hh with
    | @mk s' s t a ha hr he =>
      -- cancel `↑s`: the graft `↑t` equals the singleton `{a}`
      have ht : ({a} : Multiset Hydra) = (t : Multiset Hydra) := add_left_cancel he
      have hat : a ∈ t := by
        have : a ∈ (t : Multiset Hydra) := ht ▸ Multiset.mem_singleton_self a
        simpa using this
      exact ih a ha (hr a hat)

instance : Std.Irrefl HLt := ⟨hlt_irrefl⟩

/-- A predecessor of `node s` under `HLt` is `node s'` for an `s'` that is a
`CutExpand HLt` predecessor of the child multiset `↑s`. (The easy direction; used to
transport accessibility through `node`.) -/
theorem cutExpand_of_hlt {s' s : List Hydra} (h : HLt (node s') (node s)) :
    CutExpand HLt (↑s') (↑s) := by
  cases h with
  | @mk s'2 s2 t a ha hr he =>
    exact ⟨↑t, a, fun a' ha' => hr a' (by simpa using ha'), by simpa using he⟩

/-- Transport accessibility through `node`: if the child multiset `↑s` is accessible
under `CutExpand HLt`, then `node s` is accessible under `HLt`. -/
theorem acc_node {s : List Hydra} (h : Acc (CutExpand HLt) (↑s)) : Acc HLt (node s) := by
  -- generalize the index so we can induct on the accessibility proof
  suffices H : ∀ S : Multiset Hydra, Acc (CutExpand HLt) S →
      ∀ s : List Hydra, (↑s : Multiset Hydra) = S → Acc HLt (node s) by
    exact H _ h s rfl
  intro S hS
  induction hS with
  | intro S _ ih =>
    intro s hsS
    refine Acc.intro _ fun y hy => ?_
    -- y is below node s; it is `node s'` with `s'` a CutExpand-predecessor of `↑s`
    cases y with
    | node s' =>
      have hcut : CutExpand HLt (↑s') (↑s) := cutExpand_of_hlt hy
      exact ih (↑s') (hsS ▸ hcut) s' rfl

/-- `HLt` is well-founded: structural induction supplies each child's accessibility,
`Acc.cutExpand` lifts it to the child multiset, and `acc_node` transports it up. -/
theorem hlt_wf : WellFounded HLt := by
  refine ⟨fun h => ?_⟩
  induction h with
  | _ s ih =>
    apply acc_node
    apply acc_of_singleton
    intro a ha
    exact (ih a (by simpa using ha)).cutExpand

/-! ### Each chop strictly descends `HLt` -/

/-- **Atomic decrease.** Removing one head (`leaf`) from a node strictly lowers it:
`p ~ leaf :: p'` gives `HLt (node p') (node p)`. This is the depth-one move and the
basic building block of the grandparent regrowth. -/
theorem hlt_eraseHead {p p' : List Hydra} (hp : List.Perm p (leaf :: p')) :
    HLt (node p') (node p) := by
  have hp' : (p : Multiset Hydra) = leaf ::ₘ (p' : Multiset Hydra) := by
    rw [Multiset.cons_coe]; exact Multiset.coe_eq_coe.2 hp
  refine HLt.mk (a := leaf) (t := []) ?_ ?_ ?_
  · exact (hp.mem_iff).2 (List.mem_cons_self ..)
  · intro a' ha'; exact (List.not_mem_nil ha').elim
  · rw [hp']
    simp only [← Multiset.singleton_add, Multiset.coe_nil, add_zero]
    abel

/-- Every regrowing chop strictly descends `HLt`. By induction on `Chop`: the `grand`
case grafts `n + 1` copies of the cut node `node ps'`, each `HLt`-below the removed
child `node ps` (by `hlt_eraseHead`); the `deep` case replaces one child `c` by the
inductively smaller `c'`. -/
theorem chop_hlt {n : ℕ} {h h' : Hydra} (hc : Chop n h h') : HLt h' h := by
  induction hc with
  | @grand gs gs' ps ps' hg hp =>
    -- remove `node ps` from `gs`, graft `n+1` copies of `node ps'`
    have hgs : (gs : Multiset Hydra) = node ps ::ₘ (gs' : Multiset Hydra) := by
      rw [Multiset.cons_coe]; exact Multiset.coe_eq_coe.2 hg
    refine HLt.mk (a := node ps) (t := List.replicate (n + 1) (node ps')) ?_ ?_ ?_
    · exact (hg.mem_iff).2 (List.mem_cons_self ..)
    · intro a' ha'
      rw [List.eq_of_mem_replicate ha']
      exact hlt_eraseHead hp
    · rw [hgs]
      simp only [← Multiset.coe_add, ← Multiset.singleton_add]
      abel
  | @deep cs cs' c c' hc hrec ih =>
    have hcs : (cs : Multiset Hydra) = c ::ₘ (cs' : Multiset Hydra) := by
      rw [Multiset.cons_coe]; exact Multiset.coe_eq_coe.2 hc
    refine HLt.mk (a := c) (t := [c']) ?_ ?_ ?_
    · exact (hc.mem_iff).2 (List.mem_cons_self ..)
    · intro a' ha'
      rw [List.mem_singleton.1 ha']
      exact ih
    · rw [hcs]
      simp only [← Multiset.cons_coe, ← Multiset.singleton_add]
      abel

/-- Every legal move strictly descends `HLt`. -/
theorem step_hlt {n : ℕ} {h h' : Hydra} (hs : Step n h h') : HLt h' h := by
  cases hs with
  | root h => exact hlt_eraseHead h
  | chop hc => exact chop_hlt hc

/-- **Termination (engine form).** Every battle reaches the dead hydra `leaf`. If it
never did, the values `H 0, H 1, …` would be an infinite strictly-`HLt`-decreasing
sequence, contradicting well-foundedness of `HLt` (`WellFounded.has_min`). -/
theorem hydra_terminates_engine {H : ℕ → Hydra} {turn : ℕ → ℕ}
    (hstep : ∀ k, H k ≠ leaf → Step (turn k) (H k) (H (k + 1))) :
    ∃ N, H N = leaf := by
  by_contra hcon
  rw [not_exists] at hcon
  have hdec : ∀ k, HLt (H (k + 1)) (H k) := fun k => step_hlt (hstep k (hcon k))
  obtain ⟨a, ⟨N, hNa⟩, hmin⟩ := hlt_wf.has_min (Set.range H) ⟨H 0, 0, rfl⟩
  exact hmin (H (N + 1)) ⟨N + 1, rfl⟩ (hNa ▸ hdec N)

end LeanGallery.Logic.Hydra

end
