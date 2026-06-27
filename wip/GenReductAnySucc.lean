/-
# SPIKE (lap 158, DIRECTION.md lap-158 mandate) — generalize `genReduct_botSucc` OFF `seqSucc = ⊥`

**Decisive question.** The residual `axMajorResidual` (`Crux2Blueprint:3417`) is the irreducible
{3,4}-producer cut-reduction: a NON-LEAF `Rep` producer `m` deriving `Γ_m → ^∀^k⊥` (tag-5/climb) or
`Γ_m → p'` (tag-6). The lap-157 refutation showed it cannot be flattened AT THE CHAIN LEVEL (needs
`irk(cutFormula)+1 ≤ idg(chain)`, not derivable). The lap-158 review found the RIGHT framing: recurse
INTO the producer to get `GenReductCert m` (m's OWN reduct, same end-sequent), then splice via
`certReplace_of_premise_cert` — which is ALREADY general-succedent (its FLATTEN rank-headroom comes
from the PREMISE's own `irk+1 ≤ idg(premise)`, line 3328-3331, NOT the chain's degree).

So the ONLY missing piece is `genReduct_anySucc` = `genReduct_botSucc` with the `seqSucc(fstIdx d)=⊥`
antecedent DROPPED. **This spike pins that statement and verifies the recursion threads by CODE-induction
(the existing `zDerivation_sigma_induction`), reusing the per-case reducts — NO outer degree-induction
needed** (the degree headroom is LOCAL to each principal-cut flatten in `genReduct_chain_hasRedex`).

Checked with: `lake env lean wip/GenReductAnySucc.lean`. The deep general-succedent reducts are sorried
(`ind_reduct_anySucc`, `genReduct_anySucc_chain`); the spike's deliverable is that the CODE-induction
ENTRY `genReduct_anySucc` typechecks off `seqSucc=⊥`, validating the recursion structure.
-/
import GoodsteinPA.Crux2Blueprint

namespace GoodsteinPA.InternalZ

open Classical
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.HierarchySymbol ISigma1 PeanoMinus
open LO.FirstOrder.Arithmetic.Bootstrapping
open GoodsteinPA.InternalONote

variable {V : Type*} [ORingStructure V] [V ⊧ₘ* 𝗜𝚺₁]

/-- **GENERALIZED Ind reduct (off `seqSucc=⊥`) — sorried in this spike.** For a `zInd` deriving
`Γ → C` (any `C`), its reduct. For `C = ^∀^k⊥` (closed) the induction is VACUOUS (`p_ind = C`,
`substs1 t p_ind = p_ind`), so the reduct is just `d0` (`õ`-drop). General `C` = the lap-136 unfolding
`⟨d0, d1[a:=0..k-1]⟩`, but on the residual `C` is always a closed ∀-tower so the vacuous case suffices. -/
lemma ind_reduct_anySucc {s at' p d0 d1 : V}
    (hZ : ZDerivation (zInd s at' p d0 d1))
    (hreg : ZRegular (zInd s at' p d0 d1)) (hfresh : ZFresh (zInd s at' p d0 d1))
    (hseqant : ZSeqAnt (zInd s at' p d0 d1)) :
    GenReductCert (zInd s at' p d0 d1) := sorry

/-- **GENERALIZED chain reduct (off `seqSucc=⊥`) — sorried in this spike.** The KEY generalization is the
**IH drops the `seqSucc (fstIdx (znth ds i)) = ⊥` clause**, so it fires on a {3,4} PRODUCER of ANY
succedent — exactly what the `axMajorResidual` residual needs. Body: extract the C-EXIT `j0`
(`chainAsucc ds j0 = seqSucc s`) from `zKValidF`, `by_cases` a redex below `j0`:
YES → `genReduct_chain_hasRedex` generalized (principal cut, LOCAL degree headroom); NO →
`genReduct_chain_noRedex` generalized, whose {3,4}-producer dispatch now CLOSES via
`certReplace_of_premise_cert` (general-succedent) fed the producer's `GenReductCert` from this IH. -/
lemma genReduct_anySucc_chain {s r ds : V}
    (hZ : ZDerivation (zK s r ds))
    (hreg : ZRegular (zK s r ds)) (hfresh : ZFresh (zK s r ds)) (hseqant : ZSeqAnt (zK s r ds))
    (IH : ∀ i < lh ds, ZRegular (znth ds i) → ZFresh (znth ds i) → ZSeqAnt (znth ds i) →
        (zTag (znth ds i) = 3 ∨ zTag (znth ds i) = 4) →
        GenReductCert (znth ds i)) :
    GenReductCert (zK s r ds) := sorry

/-- **THE generalized entry — `genReduct_botSucc` OFF `seqSucc=⊥`.** Identical CODE-induction structure
to `genReduct_botSucc` (`Crux2Blueprint:3682`), only the `seqSucc(fstIdx d)=⊥` antecedent is dropped from
the motive. If this typechecks, the recursion off `⊥` is VALIDATED: the `𝚺₁` motive is definable without
the `⊥` constraint, the code-IH threads, and tag-3/tag-4 delegate to the generalized sub-reducts. -/
lemma genReduct_anySucc {d : V} (hZ : ZDerivation d) (hreg : ZRegular d) (hfresh : ZFresh d)
    (hseqant : ZSeqAnt d) (htag : zTag d = 3 ∨ zTag d = 4) :
    GenReductCert d := by
  have key : ∀ d : V, ZDerivation d → ZRegular d → ZFresh d → ZSeqAnt d →
      (zTag d = 3 ∨ zTag d = 4) → GenReductCert d := by
    apply zDerivation_sigma_induction
      (P := fun d : V => ZRegular d → ZFresh d → ZSeqAnt d →
        (zTag d = 3 ∨ zTag d = 4) → GenReductCert d)
    · -- motive definability: `GenReductCert` banked `𝚺₁`; antecedents `𝚫₁` (no `⊥`-clause to carry)
      unfold ZRegular ZFresh ZSeqAnt; definability
    · -- inductive step: dispatch on the rule; the code-IH `hC` gives `P` on every premise
      intro C hC d hphi
      have hZd : ZDerivation d := zDerivation_iff.mpr (zphi_monotone (fun x hx => (hC x hx).1) hphi)
      intro hreg hfresh hseqant htag
      rcases hphi with ⟨s, rfl, _⟩ | ⟨s, a, p, d0, rfl, _, _⟩ | ⟨s, p, d0, rfl, _, _⟩ |
        ⟨s, at', p, d0, d1, rfl, _, _, _⟩ | ⟨s, r, ds, rfl, _, hmem, _⟩ |
        ⟨s, p, k, rfl, _, _⟩ | ⟨s, p, rfl, _, _⟩ | ⟨s, C', rfl, _⟩
      · simp at htag                                       -- zAtom (tag 0)
      · simp at htag                                       -- zIall (tag 1)
      · simp at htag                                       -- zIneg (tag 2)
      · -- zInd (tag 3): the generalized Ind reduct (no `seqSucc=⊥`)
        exact ind_reduct_anySucc hZd hreg hfresh hseqant
      · -- zK (tag 4): delegate to the generalized chain step, IH WITHOUT the `⊥`-clause
        refine genReduct_anySucc_chain hZd hreg hfresh hseqant ?_
        intro i hi hregi hfreshi hseqanti htagi
        exact (hC (znth ds i) (hmem i hi)).2 hregi hfreshi hseqanti htagi
      · simp at htag                                       -- zAxAll (tag 5)
      · simp at htag                                       -- zAxNeg (tag 6)
      · simp at htag                                       -- zAx1 (tag 7)
  exact key d hZ hreg hfresh hseqant htag

/-! ## Decisive piece 2 — the {3,4}-producer residual CLOSES via the general IH + general splice

`certReplace_of_premise_cert` (`Crux2Blueprint:3283`) is ALREADY general-succedent EXCEPT its `hbot0 :
chainAsucc ds j0 = ⊥` (used only as `Or.inr hbot0` in `isChainInf_seqInsert`). Generalize it to the
C-EXIT disjunct `chainAsucc ds j0 = seqSucc s`. Then the residual `axMajorResidual` — a {3,4} PRODUCER
`m` of the cut formula — closes by feeding the producer's `GenReductCert` (from the GENERAL IH, which
no longer carries the `seqSucc=⊥` clause) to the general splice. The wiring lemma below has a
NON-sorried body, so if it typechecks the structure is fully validated. -/

/-- Generalized `certReplace_of_premise_cert` off the `⊥`-exit (`hbot0` → the C-exit disjunct). -/
lemma certReplace_of_premise_cert_anySucc {s r ds m j0 : V}
    (hZ : ZDerivation (zK s r ds)) (hreg : ZRegular (zK s r ds))
    (hfresh : ZFresh (zK s r ds)) (hseqant : ZSeqAnt (zK s r ds))
    (hj0 : j0 < lh ds)
    (hthread0 : ∀ i ≤ j0, ∀ B, inAnt B (chainAnt ds i) →
        inAnt B (seqAnt s) ∨ ∃ i' < i, B = chainAsucc ds i')
    (hrank0 : ∀ i < j0, irk (chainAsucc ds i) ≤ r)
    (hCexit : chainAsucc ds j0 = seqSucc s)
    (hm : m < lh ds) (hmj0 : m ≤ j0)
    (hmcert : GenReductCert (znth ds m)) :
    certReplace (zK s r ds) := sorry

/-- **WIRING — the residual closes (NON-sorried body).** The {3,4} producer `m` (any succedent) is
reduced by the GENERAL IH (no `⊥`-clause) → `GenReductCert (znth ds m)` → spliced by the general
`certReplace_of_premise_cert_anySucc`. This is exactly what replaces `axMajorResidual`. -/
lemma noRedex_producer_closes {s r ds m j0 : V}
    (hZ : ZDerivation (zK s r ds)) (hreg : ZRegular (zK s r ds))
    (hfresh : ZFresh (zK s r ds)) (hseqant : ZSeqAnt (zK s r ds))
    (hj0 : j0 < lh ds)
    (hthread0 : ∀ i ≤ j0, ∀ B, inAnt B (chainAnt ds i) →
        inAnt B (seqAnt s) ∨ ∃ i' < i, B = chainAsucc ds i')
    (hrank0 : ∀ i < j0, irk (chainAsucc ds i) ≤ r)
    (hCexit : chainAsucc ds j0 = seqSucc s)
    (hm : m < lh ds) (hmj0 : m ≤ j0)
    (hregm : ZRegular (znth ds m)) (hfreshm : ZFresh (znth ds m)) (hseqantm : ZSeqAnt (znth ds m))
    (htagm : zTag (znth ds m) = 3 ∨ zTag (znth ds m) = 4)
    (IH : ∀ i < lh ds, ZRegular (znth ds i) → ZFresh (znth ds i) → ZSeqAnt (znth ds i) →
        (zTag (znth ds i) = 3 ∨ zTag (znth ds i) = 4) → GenReductCert (znth ds i)) :
    GenReductCert (zK s r ds) :=
  Or.inl (certReplace_of_premise_cert_anySucc hZ hreg hfresh hseqant hj0 hthread0 hrank0 hCexit
    hm hmj0 (IH m hm hregm hfreshm hseqantm htagm))

end GoodsteinPA.InternalZ
