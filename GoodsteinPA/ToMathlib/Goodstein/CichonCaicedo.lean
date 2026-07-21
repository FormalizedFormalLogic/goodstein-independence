/-
# Cichon/Caicedo: no fixed fast-growing level bounds the Goodstein length

The Goodstein length function eventually *strictly* dominates every fixed
fast-growing level `f_o`, `o < epsilon_0`.  Consequently no fixed `f_o` can
eventually bound `Goodstein.Dom.goodsteinLength` from above — the exact
no-fixed-bound form consumed by Wainer-style provably-total-function arguments
(if PA proved Goodstein's theorem, its length function would be PA-provably
total, hence eventually bounded by some fixed `f_o`; this module refutes any
such bound).

Builds on `Goodstein.Dom.goodsteinLength_dominates_fastGrowing` (the Cichon/
Caicedo lower bound with additive slack `2`) and a successor-gap lemma
`f_o(m) + 2 < f_{o+1}(m)` absorbing the slack.
-/
module

public import GoodsteinPA.ToMathlib.Goodstein.Domination

@[expose] public section

namespace Goodstein

open ONote

/-- Eventual pointwise domination.  `EventuallyLE f g` means that, from some threshold
onward, `f n ≤ g n`. -/
def EventuallyLE (f g : ℕ → ℕ) : Prop :=
  ∃ N, ∀ n, N ≤ n → f n ≤ g n

/-- Eventual domination with a fixed additive slack on the right. -/
def EventuallyLEWithSlack (f g : ℕ → ℕ) (c : ℕ) : Prop :=
  ∃ N, ∀ n, N ≤ n → f n ≤ g n + c

/-- The already-machine-checked Cichon/Caicedo lower-bound direction in the shape the
Wainer route needs first: every fixed fast-growing level below `epsilon_0` is eventually
bounded by Goodstein length, up to the repo's documented additive slack `2`. -/
lemma goodsteinLength_eventually_dominates_fixed_fastGrowing (o : ONote) (ho : o.NF) :
    EventuallyLEWithSlack (fun n => fastGrowing o n) Goodstein.Dom.goodsteinLength 2 :=
  Goodstein.Dom.goodsteinLength_dominates_fastGrowing ho

/-- Iterating a strictly inflationary map adds at least the iteration count.

This is the elementary arithmetic engine behind the successor-level separation
`f_o(n) + 2 < f_{o+1}(n)` for large `n`. -/
lemma add_le_iterate_of_lt {g : ℕ → ℕ}
    (hstep : ∀ y, 1 ≤ y → y + 1 ≤ g y) (hpos : ∀ y, 1 ≤ y → 1 ≤ g y)
    (j : ℕ) {y : ℕ} (hy : 1 ≤ y) : y + j ≤ g^[j] y := by
  induction j generalizing y with
  | zero => simp
  | succ j ih =>
    have h1 : 1 ≤ g y := hpos y hy
    have hstepy : y + 1 ≤ g y := hstep y hy
    have hih := ih (y := g y) h1
    rw [Function.iterate_succ_apply]
    omega

/-- The strict successor gap in the fast-growing hierarchy.

For `m ≥ 4`, the notation-successor level has already iterated `f_o` long enough to
swallow the additive `+2` slack from the Goodstein lower bound:
`f_o(m) + 2 < f_{osucc o}(m)`. -/
lemma fastGrowing_fixed_add_two_lt_successor {o : ONote} (ho : o.NF) {m : ℕ}
    (hm : 4 ≤ m) :
    fastGrowing o m + 2 < fastGrowing (osucc o) m := by
  have hfs : fastGrowing (osucc o) m = (fastGrowing o)^[m] m := by
    rw [fastGrowing_succ (osucc o) (fundamentalSequence_osucc ho)]
  have hstep : ∀ y, 1 ≤ y → y + 1 ≤ fastGrowing o y := fun y hy => lt_fastGrowing o hy
  have hpos : ∀ y, 1 ≤ y → 1 ≤ fastGrowing o y :=
    fun y hy => le_trans hy (le_fastGrowing o y)
  have hsplit : (fastGrowing o)^[m] m = (fastGrowing o)^[m - 1] (fastGrowing o m) := by
    obtain ⟨n, hn⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
    rw [hn]
    simp [Function.iterate_succ_apply]
  have hiter :
      fastGrowing o m + (m - 1) ≤ (fastGrowing o)^[m - 1] (fastGrowing o m) :=
    add_le_iterate_of_lt hstep hpos (m - 1) (hpos m (by omega))
  rw [hfs, hsplit]
  omega

/-- Cichon/Caicedo in the exact no-fixed-bound form needed by Wainer: for any fixed fast-growing level `o`,
the Goodstein length eventually strictly exceeds `f_o`. -/
theorem goodsteinLength_eventually_strictly_dominates_fixed_fastGrowing (o : ONote)
    (ho : o.NF) :
    ∃ N, ∀ m, N ≤ m → fastGrowing o m < Goodstein.Dom.goodsteinLength m := by
  obtain ⟨N, hN⟩ :=
    Goodstein.Dom.goodsteinLength_dominates_fastGrowing (osucc_NF ho)
  refine ⟨max N 4, fun m hm => ?_⟩
  have hmN : N ≤ m := le_trans (le_max_left _ _) hm
  have hm4 : 4 ≤ m := le_trans (le_max_right _ _) hm
  have hdom := hN m hmN
  have hgap := fastGrowing_fixed_add_two_lt_successor ho hm4
  omega

/-- **Cichon/Caicedo exact no-fixed-bound theorem.**

This is now proved from existing machine-checked growth assets plus the successor-gap
lemma above.  It is the exact growth-route contradiction against Wainer's fixed
`f_o` upper bound. -/
theorem cichon_caicedo_not_eventually_bounded_by_fixed_fastGrowing :
    ∀ o : ONote, o.NF →
      ¬ EventuallyLE Goodstein.Dom.goodsteinLength (fun n => fastGrowing o n) := by
  intro o ho hbound
  obtain ⟨N, hN⟩ := hbound
  obtain ⟨M, hM⟩ :=
    goodsteinLength_eventually_strictly_dominates_fixed_fastGrowing o ho
  let n := max N M
  have hupper : Goodstein.Dom.goodsteinLength n ≤ fastGrowing o n :=
    hN n (le_max_left _ _)
  have hlower : fastGrowing o n < Goodstein.Dom.goodsteinLength n :=
    hM n (le_max_right _ _)
  omega

end Goodstein
