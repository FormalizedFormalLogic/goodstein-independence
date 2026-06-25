/-
# Crux-2 blueprint — the genuine reduct ⟹ the Gentzen contradiction, as sorried leaves

**Blueprint (judge, 2026-06-24).** Decomposes the single open girder `Reduction.goodstein_implies_consistency`
into precise, named, sorried leaves M1a–M3, so the crux-2 contradiction `¬Con(𝗣𝗔) → False` follows
**by construction** — the assembly is wired here, not "at the end." Increasing the sorry count is the
*point*: one fat `sorry` split into small precise ones is progress, not regress.

Grounded in the existing `InternalZ` API (verified against HEAD): `ZDerivation`, `ZDerivesEmpty`, `iord`,
`icmp`, `iR2`, `RedSound`, `iord_iR2_iterate_descends`, `inference_critical_pair`. The genuine reduct
`red` (Buchholz §6 `red` / Def 3.2) *replaces* the ordinal-faithful-but-invalid `iR2`; everything the
box banked for `iR2` (the one-step ordinal descent) re-states over `red` and the descent then becomes
**unconditional** once `redSound` (M1b) is proven.

⚠️ SEED — not yet compiled by the judge (can't host-build against the live box). The grind's first task
is to make this file elaborate (fix any signature drift against HEAD), then discharge the leaves
M1a → M1b → M2 → M3. Deliberately NOT imported by `GoodsteinPA.lean`, so it cannot affect the default
`lake build GoodsteinPA`. Literature + lap budgets: `E-CRUX2-ROADMAP-2026-06-24.md`.
-/
import GoodsteinPA.InternalZ
import GoodsteinPA.Reduction

namespace GoodsteinPA.InternalZ

variable {V : Type*} [ORingStructure V] [V ⊧ₘ* 𝗜𝚺₁]

/-! ## M1a — the genuine validity-faithful reduct `red` + construction correctness
Buchholz §6 `red` / Def 3.2: a 5-case primrec dispatch on the tag; the critical/`K`-case builds the
auxiliaries `d{0},d{1}` per 3.2(5.1) from the redex `inference_critical_pair` (L3.1) and the rank bound
`inference_critical_pair_rank` (T3.4(a)) — both already in `InternalZ`. -/

/-- **M1a.** The genuine reduct (replaces `iR2`). 5-case dispatch; critical case = `K^{r-1} d{0} d{1}`. -/
noncomputable def red (d : V) : V := sorry

/-- **M1a.** `red` preserves the end-sequent (the `tp`/`fstIdx` transfer): the reduct concludes the
same sequent it reduces. (`iR2` analogue: `fstIdx_iR2_of_tag_Ind_or_K`.) -/
theorem fstIdx_red {d : V} (hd : ZDerivation d) : fstIdx (red d) = fstIdx d := sorry

/-! ## M1b — `RedSound` for `red`: validity as the parallel-induction invariant
Buchholz Thm 3.4(b) / Thm 6.2: principal sequent ⊆ Γ, cut-rank `< m`. Proved as a SEPARATE simultaneous
induction over the same `red` (not recovered post-hoc from the ordinal side) — threading the banked
`zKValidFDef` (faithful validity). This is the cut-elimination core; everything downstream is plumbing. -/

/-- **M1b — THE nut.** The `red`-reduct of a contradiction derivation is again a genuine `ZDerivation`.
(Re-pointed `RedSound`, off the dead `iR2`.) -/
theorem redSound : ∀ d : V, ZDerivesEmpty d → ZDerivation (red d) := sorry

/-- **M1b (descent re-point, one step).** The banked ordinal descent, restated over `red`
(`iR2` analogue: `iord_descent_iR2_of_ZDerivesEmpty`). -/
theorem iord_descent_red {d : V} (hd : ZDerivesEmpty d) : icmp (iord (red d)) (iord d) = 0 := sorry

/-! ## Connectives — PROVEN from the leaves (this is the "no wiring step" demonstration)
With `redSound` in hand, `ZDerivesEmpty` is closed under the whole `red`-orbit and the ε₀-descent is
**unconditional** — mirrors `ZDerivesEmpty_iterate` / `iord_iR2_iterate_descends`, minus the `RedSound`
hypothesis. Bodies left `sorry` here only because this file is uncompiled; they are pure plumbing copies. -/

/-- `ZDerivesEmpty` is closed under the `red`-orbit (no hypothesis — `redSound` discharges it). -/
theorem ZDerivesEmpty_red_iterate {z : V} (hz : ZDerivesEmpty z) :
    ∀ n : ℕ, ZDerivesEmpty (red^[n] z) := sorry

/-- **The infinite ε₀-descent of crux-2, UNCONDITIONAL.** `n ↦ iord (red^[n] z)` strictly `≺`-descends.
An infinite primitive-recursive ε₀-descent — exactly what `PRWO(ε₀)` forbids. -/
theorem iord_red_iterate_descends {z : V} (hz : ZDerivesEmpty z) (n : ℕ) :
    icmp (iord (red^[n+1] z)) (iord (red^[n] z)) = 0 := sorry

/-! ## M2 — the C0.5 Foundation→Z bridge
`Z ⊇ 𝗣𝗔` on closed sequents, M-internal (Bryce–Goré `Peano.v` blueprint, B1–B3; the PA-induction axiom
maps directly to Z's native `Ind`, skipping their biggest sub-tower). Populates `ZDerivesEmpty` from a
Foundation ⊥-proof. -/

/-- **M2.** A Foundation derivation of `⊥` in `𝗣𝗔` yields a `Z`-derivation of the empty sequent. -/
theorem foundation_bot_to_Z_empty {d : V} (hd : (𝗣𝗔).DerivationOf d (⊥ : Sentence ℒₒᵣ)) :
    ∃ z : V, ZDerivesEmpty z := sorry

/-! ## M3 — assemble the Gentzen contradiction
An inconsistency gives a `ZDerivesEmpty` (M2) whose `red`-orbit is an infinite ε₀-descent (M1b ⟹
`iord_red_iterate_descends`), which `PRWO(ε₀)`/well-foundedness forbids. This is the payload that
discharges the deep axiom `GentzenCon.gentzen_descent_of_inconsistent`; the existing `Reduction.lean`
+ `GentzenCon` scaffolding carries it the rest of the way to `goodstein_implies_consistency` and the
headline — no new top-level wiring. -/

/-- **M3.** From a `ZDerivesEmpty` witness, the unconditional ε₀-descent contradicts well-foundedness of
the internal ordinal order — the Gentzen `False`. (Internalize `n ↦ iord (red^[n] z)` as the `Σ₁` graph
`gentzenDescentφ`; the descent is `iord_red_iterate_descends`.) -/
theorem false_of_ZDerivesEmpty {z : V} (hz : ZDerivesEmpty z) : False := sorry

end GoodsteinPA.InternalZ
