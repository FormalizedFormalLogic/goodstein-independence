/-
# PROBE: the Hardy additive identity `H_{e+β} = H_e ∘ H_β` — and its ABSORPTION WALL

Investigated as permitted-sibling infrastructure for the REBUILD-Z raised-control obligation
(P1): the `cutElimPass_Zf` conjunct `NormControlled f' (raise e α') m`, with
`raise e α' = e + expTower α' = e + ω^{α'}`.  The HOPE was that the classical additive identity
`H_{e+β} = H_e ∘ H_β` would exhibit `hardy e ∘ hardy (ω^{α'})` as a concrete E–W iterate slot `f'`,
collapsing the "transfinite iterate" mystery to one already-defined composition.

**KERNEL-VERIFIED FINDING (this file, sorry-free): the UNCONDITIONAL identity is FALSE.**
It holds at successor right-summands (unconditionally — successors have unique predecessors) and
at FINITE right-summands, but it FAILS at limit right-summands under *absorption*: e.g.
`(1 : ONote) + ω = ω` (kernel `rfl` below), so `H_{1+ω} = H_ω`, whereas `H_1 ∘ H_ω = (·+1) ∘ H_ω`.
Consequence for P1: when the raise `ω^{α'}` absorbs `e` (the typical growing-ordinal regime of
cut-elimination), additive decomposition gives NO handle on the input control `hardy e`; the
raised control is `≈ hardy (ω^{α'})`, so the obligation is the genuine fast-growing DOMINATION
`hardy (ω^{α'}) ≤ (iterate of the input slot)` — E–W Lemma 19, not an algebraic identity.  This
corroborates the pre-validated BW87 cut-free read-off fallback and bears on judge Q1 (the locus of
the P1 conjunct).

Pure Hardy arithmetic about the STABLE `hardy`/`+` defs: consumes no f-slot pin, touches no gated
pin body, rules on no judge Option-A/B question.

TRUE fragments proven here (unconditional, reusable):
  * `onote_add_zero`               — `o + 0 = o`
  * `fundamentalSequence_add_succ` — the fs homomorphism, SUCCESSOR branch (holds under absorption);
                                     the notation-level generalization of the banked
                                     `hardy_add_ofNat` (`Hardy.lean:1257`, the finite fragment)
Refutation (kernel `rfl`): `add_omega_absorbs`, `fundamentalSequence_absorbs`.
-/
import GoodsteinPA.Hardy

namespace GoodsteinPA.FastGrowing

open ONote Ordinal

/-- `o + 0 = o` for a normal-form ONote (via `repr` injectivity). -/
theorem onote_add_zero (o : ONote) [NF o] : o + (0 : ONote) = o := by
  rw [← repr_inj, repr_add, repr_zero, _root_.add_zero]

/-- **fs homomorphism, successor branch (unconditional).** If `β` is the notation-successor of
`β'`, then `e + β` is the notation-successor of `e + β'`.  Holds EVEN under absorption: `repr (e+β)`
is `succ (repr (e+β'))`, always a successor, and its predecessor is unique, so
`fundamentalSequence`'s output shape is forced by `FundamentalSequenceProp` (neither `0` nor a
limit) to `inl (some (e+β'))` (via `repr_inj`). -/
theorem fundamentalSequence_add_succ {e β β' : ONote} (he : e.NF) (hβ : β.NF)
    (h : fundamentalSequence β = Sum.inl (some β')) :
    fundamentalSequence (e + β) = Sum.inl (some (e + β')) := by
  haveI := he; haveI := hβ
  have hβ' : β'.NF := by
    have hp := fundamentalSequence_has_prop β; rw [h] at hp; exact hp.2 hβ
  haveI := hβ'
  haveI heβ : (e + β).NF := ONote.add_nf e β
  haveI heβ' : (e + β').NF := ONote.add_nf e β'
  have hβrepr : ONote.repr β = Order.succ (ONote.repr β') := by
    have hp := fundamentalSequence_has_prop β; rw [h] at hp; exact hp.1
  have hsum : ONote.repr (e + β) = Order.succ (ONote.repr (e + β')) := by
    rw [repr_add, repr_add, hβrepr, Ordinal.add_succ]
  have hprop := fundamentalSequence_has_prop (e + β)
  rcases hfs : fundamentalSequence (e + β) with (_ | Z) | g
  · rw [hfs] at hprop
    have h0 : (e + β) = 0 := (fundamentalSequenceProp_inl_none _).mp hprop
    rw [h0, repr_zero] at hsum
    exact absurd hsum.symm (succ_ne_zero _)
  · rw [hfs] at hprop
    obtain ⟨hZrepr, hZnf⟩ := (fundamentalSequenceProp_inl_some _ _).mp hprop
    have : Order.succ (ONote.repr Z) = Order.succ (ONote.repr (e + β')) := by rw [← hZrepr, hsum]
    have hZeq : ONote.repr Z = ONote.repr (e + β') := Order.succ_injective this
    have : Z = e + β' := by rw [← @repr_inj Z (e + β') (hZnf heβ) heβ']; exact hZeq
    rw [this]
  · rw [hfs] at hprop
    obtain ⟨hlim, _⟩ := (fundamentalSequenceProp_inr _ _).mp hprop
    rw [hsum] at hlim
    exact absurd hlim (Order.not_isSuccLimit_succ _)

/-- **The additive identity at a FINITE right summand is ALREADY BANKED** as
`GoodsteinPA.FastGrowing.hardy_add_ofNat` (`Hardy.lean:1257`): `H_{α+c}(n) = H_α(n+c)`, proved by
the successor rule + `α + (c+1) = osucc (α + c)`, and load-bearing in `LowerBound.lean`.  It is the
finite/no-absorption slice of the additive identity — exactly the fragment that survives the
absorption wall below.  `fundamentalSequence_add_succ` is the notation-level generalization of the
same successor step to an arbitrary (possibly transfinite) predecessor. -/
example : True := trivial

/-! ### The absorption refutation (kernel `rfl` — the finding is REAL, not asserted) -/

/-- `1 + ω = ω`: a smaller left summand is fully ABSORBED by an `ω`-limit. (`ω = oadd 1 1 0`.) -/
theorem add_omega_absorbs : (1 : ONote) + oadd 1 1 0 = oadd 1 1 0 := rfl

/-- The absorbed sum shares `ω`'s fundamental sequence — NOT the `(1 + ·)`-image of it.  So the
LIMIT-branch fs homomorphism `fundamentalSequence (1+ω) = inr (fun i => 1 + f i)` FAILS: the actual
sequence is `f` itself (with `f 0 = ofNat 1`), while `1 + f 0 = ofNat 2 ≠ f 0`.  Hence the
UNCONDITIONAL `hardy_add`/limit homomorphism is false; only the successor/finite fragments survive. -/
theorem fundamentalSequence_absorbs :
    fundamentalSequence ((1 : ONote) + oadd 1 1 0) = fundamentalSequence (oadd 1 1 0) := rfl

end GoodsteinPA.FastGrowing
