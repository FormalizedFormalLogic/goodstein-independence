/-
# JUDGE PROBE (lap-5 pass, 2026-07-02): the SEVENTH statement trap — the fixed-count iterate
fails the `allω` reassembly

The lap-5 draft defined pin 3's output slot as the RETIRED fixed-count form
`f^[norm α + 1]` (then `iterSlot f α := f^[iterCount α]`, `iterCount α := norm α + 1`).
At an `allω` node the pass's induction hands branch `n` its eliminated derivation at slot
`(rel1 f n)^[norm (β n) + 1]`, while the pin's conclusion forces the parent's branch slot
`rel1 (f^[norm α + 1]) n`.  `Zef.mono_f` only RAISES slots, so reassembly requires

    (rel1 f n)^[norm (β n) + 1]  ≤  rel1 (f^[norm α + 1]) n     (pointwise).

This file kernel-refutes that containment at the W4B-shaped instance `α = ω`, `β 2 = ofNat 2`,
`f = hardy ω` (`= 2·+1`), `x = 0`: parent side `f^[2] 2 = 11 < 23 = (rel1 f 2)^[3] 0`.
Root cause: `norm` is not monotone along `<` — `norm (ofNat n) = n` grows along ω's fundamental
sequence while `norm ω = 1` — so NO fixed ℕ-count read off the parent ordinal dominates the
branches.  The judge amendment replaces the count with the DIAGONALIZING ordinal-indexed
iterate (`iterSlot`, §5b — the E–W Lemma 19 `F^α(0)` transfinite form), whose limit case
`iterSlot f λ n = iterSlot f (λ[n]) n` lets the branch index ride the numeric argument, which
`rel1` raises.  Judge ruling: `E-2026-07-02-JUDGE-rebuild-z-lap5-validation.md`.

`lake env lean wip/JudgeTrap7Probe.lean` — evidence artifact, off the live build, read-only.
-/
import GoodsteinPA.OperatorZeh

namespace GoodsteinPA.OperatorZeh

open GoodsteinPA.FastGrowing ONote

/-- The RETIRED lap-5 fixed-count iterate (inlined here so this probe stays self-contained
after the src amendment). -/
def retiredIterSlot (f : ℕ → ℕ) (α : ONote) : ℕ → ℕ := f^[norm α + 1]

-- the two norm readoffs feeding the counts: the parent count is FIXED at 2 while the
-- branch count grows along ω's fundamental sequence
example : norm ONote.omega = 1 := by decide
example : norm (ONote.ofNat 2) = 2 := by decide

/-- **The containment failure witness**: parent-mandated branch slot < branch IH slot, at
`x = 0`, branch `n = 2`.  With `f = hardy ω = 2·+1`: parent `f^[2] 2 = 11`, branch
`(rel1 f 2)^[3] 0 = 23`. -/
theorem trap7_containment_fails :
    rel1 (retiredIterSlot (hardy ONote.omega) ONote.omega) 2 0
      < retiredIterSlot (rel1 (hardy ONote.omega) 2) (ONote.ofNat 2) 0 := by
  have hω : ∀ m, hardy ONote.omega m = 2 * m + 1 := fun m => by
    rw [show ONote.omega = oadd 1 1 0 from rfl, hardy_omega]
  have hcω : norm ONote.omega + 1 = 2 := by decide
  have hc2 : norm (ONote.ofNat 2) + 1 = 3 := by decide
  simp only [retiredIterSlot, rel1, hcω, hc2]
  simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq, hω]
  simp only [rel1, hω]
  norm_num

end GoodsteinPA.OperatorZeh
