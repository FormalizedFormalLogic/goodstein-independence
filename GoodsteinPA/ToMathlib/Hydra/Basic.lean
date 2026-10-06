/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/

module

public import Mathlib.Data.Multiset.Basic

@[expose] public section

/-
VENDORED from LeanGallery rev `a834bbad2f36eedcc16066b2bc4da49f98ab5b85`
(`LeanGallery/Logic/Hydra/`), verbatim except for the module-system header: this repo's root is a
`module`, and Lean 4.31 forbids a `module` from importing a non-`module`, so the gallery files
cannot be imported directly until the gallery migrates.  The namespace is kept as
`LeanGallery.Logic.Hydra` to record provenance and to keep the arc's `open` lines unchanged.
-/


/-!
# The Kirby–Paris hydra

*Hercules always wins: no matter how the heads are chopped, every hydra dies.* —
L. Kirby & J. Paris (1982).

This file is the **abstract and audit surface** for the formalization. It fixes the
faithful object (a finite rooted tree), the legal move (chop a head, regrow at the
grandparent), and points at the headline theorem. The well-foundedness proof lives in
`Engine.lean` and the headline in `Statement.lean`; neither is part of the trust
surface. Read this file against Kirby–Paris 1982.

## The construction (standard; Kirby–Paris 1982)

A **hydra** is a finite rooted tree. We encode it as a recursive rose tree
`Hydra.node : List Hydra → Hydra`: a node carries the *list* of its child hydras, and
a **head** is a leaf, `leaf = node []`. The list is only a convenient concrete carrier
— **order plays no role**: every definition and theorem below treats the children up to
permutation (the move is stated with `List.Perm`, and the ordinal value implicit in the
well-founded order is the order-free natural sum `♯ ωᵒ⁽ᶜ⁾`). So this is genuinely the
game on *unordered* trees.

### The move — chop a head, regrow (Kirby–Paris rule at turn `n`)

A head is a leaf. One legal move at turn `n`, on a hydra rooted at `r`:

1. Pick a head `x`. It hangs off a node `p` (its parent).
2. Remove `x` from `p`, giving `p'`.
3. **If `p` is the root**: the result is `p'` (no regrowth).
4. **If `p` is not the root**: let `g` be the grandparent (parent of `p`). Keep all of
   `g`'s children and additionally graft on **`n + 1` copies of `p'`** (the surviving
   `p'` itself plus `n` fresh copies).

`Step n` below is the relation "`after` is reachable from `before` by one such move at
turn `n`". It splits into the depth-1 case (`Step.root`, head hangs off the root, no
regrowth) and the deeper case (`Step.chop`, routed through the regrowing relation
`Chop n`). The headline quantifies over **all** sequences of legal moves — "Hercules
wins no matter how he plays and no matter how fast the hydra regrows".

## Main definitions
* `Hydra` — a finite rooted tree (rose tree); `leaf = node []` is a single head.
* `Chop n before after` — one regrowing chop at turn `n` (the head has a grandparent,
  so `n + 1` copies of the cut node are regrown one level up).
* `Step n before after` — any legal move at turn `n` (a `Chop`, or a depth-1 head off
  the root).

## Main statements
The headline lives in `Statement.lean` (proved in `Engine.lean`):
```
theorem hydra_terminates {H : ℕ → Hydra} {turn : ℕ → ℕ}
    (hstep : ∀ k, H k ≠ leaf → Step (turn k) (H k) (H (k + 1))) : ∃ N, H N = leaf
```
Every battle reaches the dead hydra `leaf` in finitely many moves, despite the
explosive early growth. The proof assigns each hydra its Kirby–Paris ordinal `< ε₀`
(the natural sum `♯ ωᵒ⁽ᶜ⁾` over children), realized here as a recursive multiset
(path) order; every chop strictly lowers it, and ordinals are well-founded, so no
infinite battle exists. Verified axiom-clean: `#print axioms hydra_terminates` reports
only `[propext, Classical.choice, Quot.sound]`.

This is the Kirby–Paris hydra *termination* theorem (provable in ZFC, hence in Lean).
The **independence result** — that Peano Arithmetic cannot prove it — is a separate
metamathematical statement and is out of scope here.

## References
* L. Kirby and J. Paris, *Accessible independence results for Peano arithmetic*,
  Bull. London Math. Soc. **14** (1982), no. 4, 285–293.
  <https://doi.org/10.1112/blms/14.4.285>
* `Mathlib/Logic/Hydra.lean` (`Relation.CutExpand`, J. Xu) — the abstract single-level
  multiset hydra, whose `TODO` (formalize the Kirby–Paris hydra) this entry answers.
-/

-- The headline type is `LeanGallery.Logic.Hydra.Hydra`; the trailing-`Hydra` dup is
-- intentional (mirrors `Mathlib/Logic/Hydra.lean`'s placement).
set_option linter.dupNamespace false

namespace LeanGallery.Logic.Hydra

/-- A **hydra**: a finite rooted tree. A node carries the list of its child hydras; a
**head** is a leaf, `leaf = node []`. The list carrier is incidental — the whole
development is invariant under permuting children (see the module doc). -/
inductive Hydra : Type
  | node : List Hydra → Hydra

namespace Hydra

/-- The dead hydra / a single head: a node with no children. -/
def leaf : Hydra := node []

/-- Structural induction for the nested rose tree `Hydra`: to prove `P (node s)` it
suffices to assume `P c` for every child `c ∈ s`. (Lean's default `induction` does not
fire on nested inductives; this is the usable eliminator.) -/
@[induction_eliminator]
theorem ind' {P : Hydra → Prop} (h : ∀ s : List Hydra, (∀ c ∈ s, P c) → P (node s)) :
    ∀ t, P t :=
  fun t =>
    Hydra.rec (motive_1 := P) (motive_2 := fun l => ∀ c ∈ l, P c)
      (fun s ih => h s ih)
      (fun c hc => (List.not_mem_nil hc).elim)
      (fun _ _ ihh iht c hc => by
        rcases List.mem_cons.1 hc with rfl | hc'
        · exact ihh
        · exact iht c hc')
      t

end Hydra

open Hydra

/-- **Regrowing chop at turn `n`.** `Chop n before after` holds when `after` results
from `before` by chopping a head whose parent is *not* the root, regrowing `n + 1`
copies of the cut node one level up. Two shapes:

* `grand` — the head is at depth two from this node: a child `node ps` of the root has
  a head `leaf` (so `ps ~ leaf :: ps'`); we drop that child and graft `n + 1` copies of
  `node ps'` onto the root.
* `deep` — the head is deeper still: recurse into a child `c`, which becomes `c'`. -/
inductive Chop (n : ℕ) : Hydra → Hydra → Prop
  | grand {gs gs' ps ps' : List Hydra}
      (hg : List.Perm gs (node ps :: gs')) (hp : List.Perm ps (leaf :: ps')) :
      Chop n (node gs) (node (gs' ++ List.replicate (n + 1) (node ps')))
  | deep {cs cs' : List Hydra} {c c' : Hydra}
      (hc : List.Perm cs (c :: cs')) (hrec : Chop n c c') :
      Chop n (node cs) (node (c' :: cs'))

/-- **One legal move at turn `n`.** `Step n before after`: either a regrowing `Chop`,
or the depth-one case where a head hangs directly off the root and is removed with no
regrowth (`cs ~ leaf :: rest`, result `node rest`). -/
inductive Step (n : ℕ) : Hydra → Hydra → Prop
  | root {cs rest : List Hydra} (h : List.Perm cs (leaf :: rest)) :
      Step n (node cs) (node rest)
  | chop {h h' : Hydra} (hc : Chop n h h') : Step n h h'

/-! ### Ground-truth anchors (faithfulness gate)

Concrete one-move derivations, given as explicit term proofs straight from the `Chop` /
`Step` constructors. They are the anti-vacuity lock on the move relation: a placeholder
or degenerate definition could not exhibit these specific transitions, and the dead
hydra being *terminal* could not be derived. Each is a standalone `example` that never
sits on `hydra_terminates`'s axiom path (and uses no `decide`/`native_decide`, so it is
itself axiom-clean) — re-check `#print axioms hydra_terminates`, not these.

`Ordinal` is noncomputable and the game is unordered, so we pin the *move* by exhibiting
derivations rather than by `decide` on an ordinal. -/

/-- A head hanging directly off the root dies in one move (depth-one case, no regrowth):
`node [leaf] → leaf`. -/
example (n : ℕ) : Step n (node [leaf]) leaf := Step.root (List.Perm.refl _)

/-- The **regrowth** rule, made concrete. On the length-two path `node [node [leaf]]`
the only head is at depth two, so chopping it grafts `n + 1` fresh heads onto the root:
`node [node [leaf]] → node (replicate (n+1) leaf)`. The hydra gets *bigger* before it
can die — the whole subtlety of the game. -/
example (n : ℕ) :
    Step n (node [node [leaf]]) (node (List.replicate (n + 1) leaf)) :=
  Step.chop (Chop.grand (List.Perm.refl _) (List.Perm.refl _))

/-- With two heads off the root, chopping one leaves the other: `node [leaf, leaf] →
node [leaf]`. -/
example (n : ℕ) : Step n (node [leaf, leaf]) (node [leaf]) :=
  Step.root (List.Perm.refl _)

/-- The dead hydra is **terminal**: no move is possible from `leaf`. (So "reaches
`leaf`" genuinely means the battle is over.) -/
example (n : ℕ) (h' : Hydra) : ¬ Step n leaf h' := by
  rintro hs
  cases hs with
  | root h => simpa using h.length_eq
  | chop hc => cases hc with
    | grand hg _ => simpa using hg.length_eq
    | deep hc _ => simpa using hc.length_eq

end LeanGallery.Logic.Hydra

end
