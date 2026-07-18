/-
# Wainer/Cichon/Caicedo growth-rate route

This module is the new route spine after the 2026-07-01 route decision.  The old
active route tried to derive `Con(PA)` from Goodstein inside PA and then use Godel II.
That forced an IΣ₁-internalized cut-elimination bridge.  The lap-171 M2 probe found
the decisive obstruction: the PA-induction leaf wants a free-variable forall-left /
implication-left step that the finitary internal-Z calculus does not have.

The growth route instead proves non-provability from rates of growth:

  PA proves Goodstein
    -> the Goodstein length function is PA-provably total
    -> Wainer: every PA-provably-total recursive function is eventually bounded by
       some fast-growing `f_o`, `o < epsilon_0`
    -> Cichon/Caicedo: Goodstein length is not eventually bounded by any fixed
       `f_o`, `o < epsilon_0`
    -> contradiction.

The existing repo already proves the main concrete growth asset:
`Goodstein.Dom.goodsteinLength_dominates_fastGrowing`.  This module now upgrades
that asset to the exact no-fixed-bound theorem needed by the route.  The remaining
named axiom is the Wainer PA-provably-total classification bridge.
-/
module

public import GoodsteinPA.Reduction  -- (SERIES-5 Lane B) was: import GoodsteinPA.Statement, dropped to break the WainerRoute->Statement cycle
public import GoodsteinPA.ToMathlib.Goodstein.Domination
public import GoodsteinPA.BlueprintAttr

@[expose] public section

namespace GoodsteinPA.WainerRoute

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open ONote

/-- Eventual pointwise domination.  `EventuallyLE f g` means that, from some threshold
onward, `f n <= g n`. -/
def EventuallyLE (f g : ℕ -> ℕ) : Prop :=
  ∃ N, ∀ n, N ≤ n -> f n ≤ g n

/-- Eventual domination with a fixed additive slack on the right. -/
def EventuallyLEWithSlack (f g : ℕ -> ℕ) (c : ℕ) : Prop :=
  ∃ N, ∀ n, N ≤ n -> f n ≤ g n + c

/-- The already-machine-checked Cichon/Caicedo lower-bound direction in the shape the
Wainer route needs first: every fixed fast-growing level below `epsilon_0` is eventually
bounded by Goodstein length, up to the repo's documented additive slack `2`. -/
theorem goodsteinLength_eventually_dominates_fixed_fastGrowing (o : ONote) (ho : o.NF) :
    EventuallyLEWithSlack (fun n => fastGrowing o n) Goodstein.Dom.goodsteinLength 2 :=
  Goodstein.Dom.goodsteinLength_dominates_fastGrowing ho

/-- Iterating a strictly inflationary map adds at least the iteration count.

This is the elementary arithmetic engine behind the successor-level separation
`f_o(n) + 2 < f_{o+1}(n)` for large `n`. -/
theorem add_le_iterate_of_lt {g : ℕ -> ℕ}
    (hstep : ∀ y, 1 ≤ y -> y + 1 ≤ g y)
    (hpos : ∀ y, 1 ≤ y -> 1 ≤ g y) :
    ∀ (j : ℕ) {y : ℕ}, 1 ≤ y -> y + j ≤ g^[j] y := by
  intro j
  induction j with
  | zero =>
      intro y hy
      simp
  | succ j ih =>
      intro y hy
      rw [Function.iterate_succ_apply]
      have h1 : 1 ≤ g y := hpos y hy
      have hstepy : y + 1 ≤ g y := hstep y hy
      have hih := ih (y := g y) h1
      omega

/-- The strict successor gap in the fast-growing hierarchy.

For `m >= 4`, the notation-successor level has already iterated `f_o` long enough to
swallow the additive `+2` slack from the Goodstein lower bound:
`f_o(m) + 2 < f_{osucc o}(m)`. -/
theorem fastGrowing_fixed_add_two_lt_successor {o : ONote} (ho : o.NF) {m : ℕ}
    (hm : 4 ≤ m) :
    fastGrowing o m + 2 < fastGrowing (osucc o) m := by
  have hfs : fastGrowing (osucc o) m = (fastGrowing o)^[m] m := by
    rw [fastGrowing_succ (osucc o) (fundamentalSequence_osucc ho)]
  have hstep : ∀ y, 1 ≤ y -> y + 1 ≤ fastGrowing o y := fun y hy => lt_fastGrowing o hy
  have hpos : ∀ y, 1 ≤ y -> 1 ≤ fastGrowing o y :=
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

/-- Cichon/Caicedo in the exact no-fixed-bound form needed by Wainer.

The repo's existing lower bound gives `f_{osucc o}(m) <= goodsteinLength m + 2`
eventually.  The successor-gap lemma above gives `f_o(m) + 2 < f_{osucc o}(m)` for
`m >= 4`.  Together they imply `f_o(m) < goodsteinLength m` eventually, so no fixed
`f_o` can eventually bound the Goodstein length function from above. -/
theorem goodsteinLength_eventually_strictly_dominates_fixed_fastGrowing (o : ONote)
    (ho : o.NF) :
    ∃ N, ∀ m, N ≤ m -> fastGrowing o m < Goodstein.Dom.goodsteinLength m := by
  obtain ⟨N, hN⟩ :=
    Goodstein.Dom.goodsteinLength_dominates_fastGrowing (osucc_NF ho)
  refine ⟨max N 4, fun m hm => ?_⟩
  have hmN : N ≤ m := le_trans (le_max_left _ _) hm
  have hm4 : 4 ≤ m := le_trans (le_max_right _ _) hm
  have hdom := hN m hmN
  have hgap := fastGrowing_fixed_add_two_lt_successor ho hm4
  omega

/- `wainer_bound_of_pa_proves_goodstein` (formerly the sole route-B axiom) is now a THEOREM,
discharged in `GoodsteinPA.WainerBound` — downstream of the embedding chain, which imports THIS
module, so it lives there to break the import cycle. SERIES-4 judge pass, 2026-07-03. -/

/-- **Cichon/Caicedo exact no-fixed-bound theorem.**

This is now proved from existing machine-checked growth assets plus the successor-gap
lemma above.  It is the exact growth-route contradiction against Wainer's fixed
`f_o` upper bound. -/
theorem cichon_caicedo_not_eventually_bounded_by_fixed_fastGrowing :
    ∀ o : ONote, o.NF ->
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

/- `peano_not_proves_goodstein_growth` and blueprint nodes 14 (`wainer_axiom`) / 15
(`routeB_headline`) moved to `GoodsteinPA.WainerBound` with the axiom's discharge (they consume the
now-proven bound; they cannot live here because `WainerBound` imports this module). -/

end GoodsteinPA.WainerRoute
