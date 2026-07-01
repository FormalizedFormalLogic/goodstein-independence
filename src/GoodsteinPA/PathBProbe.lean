import GoodsteinPA.LowerBound
import GoodsteinPA.Encoding
import GoodsteinPA.BlueprintAttr

/-!
# Path B probe: witness-bounded terminal target

This file deliberately uses the current Pivot-B meaning from
`ROUTE-ESCALATION-2026-06-28.md`: the growth-rate / Towsner lower-bound route.

The old `wip/Bounding.lean` assembly is not revived here, because it is explicitly
false as stated: it routes through the unbounded `Z∞` calculus and loses Towsner's
witness bound.  The live terminal target for B is the witness-bounded calculus
`LowerBoundHardy.B`.
-/

namespace GoodsteinPA.PathBProbe

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open GoodsteinPA.LowerBoundHardy

/-- A cut-free, witness-bounded derivation of the Goodstein fragment at ordinal `α`
and witness budget `k`.  This is the terminal object that Path B must extract from
a PA proof after bounded embedding and bounded cut-elimination. -/
def CutFreeGoodsteinBounded (α : ONote) (k : ℕ) : Prop :=
  B α k ({GForm.gAll} : Seq)

/-- The promoted lower-bound theorem directly rules out the B terminal object for
every normal-form ordinal notation and every witness budget. -/
theorem no_cutFreeGoodsteinBounded {α : ONote} (hα : α.NF) (k : ℕ) :
    ¬ CutFreeGoodsteinBounded α k := by
  simpa [CutFreeGoodsteinBounded] using lowerBound_hardy_selfcontained (α := α) hα k

/-- The current B capstone, isolated from the upstream embedding work. -/
def RouteBCapstone : Prop :=
  ∃ α : ONote, α.NF ∧ ∃ k : ℕ, CutFreeGoodsteinBounded α k

/-- The lower-bound half of B is already decisive once a bounded cut-free derivation
has been produced. -/
theorem no_routeBCapstone : ¬ RouteBCapstone := by
  rintro ⟨α, hα, k, hB⟩
  exact no_cutFreeGoodsteinBounded hα k hB

/-- The terminal Path-B object is equivalent to contradiction, because Towsner's
lower-bound theorem already rules it out. -/
theorem routeBCapstone_iff_false : RouteBCapstone ↔ False :=
  ⟨no_routeBCapstone, False.elim⟩

/-- The real next B bridge: a PA proof of Goodstein must yield the witness-bounded
cut-free terminal object above, not merely an unbounded `Z∞` derivation. -/
def RouteBBridgeFromPAProof : Prop :=
  (𝗣𝗔 ⊢ ↑goodsteinSentence) → RouteBCapstone

/--
Named B obligations.  These are not global Lean axioms; they are an explicit assumption
package so the route can be reviewed by named missing theorem rather than hidden inside the
single bridge above.

The hardest field is `boundedInductionAxiomLeaf`: porting the PA-induction axiom discharge to
the witness-bounded calculus without losing the `exI` witness bound.
-/
structure RouteBNamedObligations where
  boundedUniversalAxiomLeaves : Prop
  boundedInductionAxiomLeaf : Prop
  boundedStructuralEmbedding : Prop
  boundedCutElimination : Prop
  subformulaBridgeToLowerBound : Prop
  h_boundedUniversalAxiomLeaves : boundedUniversalAxiomLeaves
  h_boundedInductionAxiomLeaf : boundedInductionAxiomLeaf
  h_boundedStructuralEmbedding : boundedStructuralEmbedding
  h_boundedCutElimination : boundedCutElimination
  h_subformulaBridgeToLowerBound : subformulaBridgeToLowerBound
  bridgeFromNamed :
    boundedUniversalAxiomLeaves →
    boundedInductionAxiomLeaf →
    boundedStructuralEmbedding →
    boundedCutElimination →
    subformulaBridgeToLowerBound →
    RouteBBridgeFromPAProof

/-- Collapse the named B obligations to the single bridge consumed by the terminal assembly. -/
def RouteBNamedObligations.bridge (h : RouteBNamedObligations) : RouteBBridgeFromPAProof :=
  h.bridgeFromNamed
    h.h_boundedUniversalAxiomLeaves
    h.h_boundedInductionAxiomLeaf
    h.h_boundedStructuralEmbedding
    h.h_boundedCutElimination
    h.h_subformulaBridgeToLowerBound

/-- Once the bounded bridge exists, the headline independence result follows from
the already-promoted lower-bound theorem. -/
theorem peano_not_proves_goodstein_of_routeBBridge
    (hbridge : RouteBBridgeFromPAProof) : 𝗣𝗔 ⊬ ↑goodsteinSentence := by
  intro hpa
  exact no_routeBCapstone (hbridge hpa)

/-- The same assembly, but with the missing B work exposed as named obligations. -/
theorem peano_not_proves_goodstein_of_routeBNamedObligations
    (h : RouteBNamedObligations) : 𝗣𝗔 ⊬ ↑goodsteinSentence :=
  peano_not_proves_goodstein_of_routeBBridge h.bridge

/-! ## Path B named capstone axioms

The declarations below are the Path-B audit ledger.  They live in `src/` because Path B is now an
active route, but they are imported through the dedicated `GoodsteinPABlueprint` root rather than
the public `GoodsteinPA` root.  The marker propositions expose the route's theorem boundaries:
most are empty inductives whose only current inhabitants are the correspondingly named capstone axioms,
while proved bookkeeping boundaries carry explicit constructors.

The primitive axioms are the open leaves.  The `_stage` theorems compose those leaves into a dependency
chain: `#print axioms pathB_inductionAxiomShell_stage`, for example, reports the open capstone axioms
up to that point. When a milestone is actually proved, replace its primitive axiom with a theorem of the
same name and keep the stage chain below unchanged.
-/

/-- Capstone marker: the encoded Goodstein sentence has been normalized to the exact
closed one-formula sequent shape consumed by the bounded embedding. -/
inductive RouteBGoodsteinSentenceShape (_hpa : 𝗣𝗔 ⊢ ↑goodsteinSentence) : Prop
  | closedTarget

/-- Capstone marker: all finite `𝗣𝗔⁻`/equality axiom leaves are derivable in the bounded operator
calculus with finite extracted witness budget. -/
inductive RouteBPeanoMinusAxiomLeaves (_hpa : 𝗣𝗔 ⊢ ↑goodsteinSentence) : Prop

/-- Capstone marker: the PA induction-axiom shell is simulated in the bounded operator calculus. -/
inductive RouteBInductionAxiomShell (_hpa : 𝗣𝗔 ⊢ ↑goodsteinSentence) : Prop

/-- Capstone marker: every Foundation `exs`/closed-witness step has a finite `K` budget. -/
inductive RouteBClosedWitnessBudgets (_hpa : 𝗣𝗔 ⊢ ↑goodsteinSentence) : Prop

/-- Capstone marker: the whole PA proof embeds into the `someK` bounded operator calculus. -/
inductive RouteBSomeKStructuralEmbedding (_hpa : 𝗣𝗔 ⊢ ↑goodsteinSentence) : Prop

/-- Capstone marker: bounded cut-elimination preserves finite witness budget after raising the
control ordinal as needed. -/
inductive RouteBOperatorCutElimination (_hpa : 𝗣𝗔 ⊢ ↑goodsteinSentence) : Prop

/-- Capstone marker: the cut-free operator derivation projects to the subformula fragment used by
Towsner's `B` calculus. -/
inductive RouteBSubformulaProjection (_hpa : 𝗣𝗔 ⊢ ↑goodsteinSentence) : Prop

/-- Capstone marker: the projected derivation has been identified with the concrete Goodstein fragment
terminal object consumed by the lower-bound contradiction. -/
inductive RouteBGoodsteinFragmentExtraction (_hpa : 𝗣𝗔 ⊢ ↑goodsteinSentence) : Prop
  | terminal (route : RouteBCapstone)

/-- Capstone 1, discharged: the Path-B input is already the closed encoded Goodstein sentence. -/
theorem pathB_goodsteinSentenceShape_capstone {hpa : 𝗣𝗔 ⊢ ↑goodsteinSentence} :
    RouteBGoodsteinSentenceShape hpa :=
  .closedTarget

/-- Capstone 2: finite `𝗣𝗔⁻` and equality axiom leaves. -/
axiom pathB_peanoMinusAxiomLeaves_capstone {hpa : 𝗣𝗔 ⊢ ↑goodsteinSentence} :
    RouteBGoodsteinSentenceShape hpa → RouteBPeanoMinusAxiomLeaves hpa

/-- Capstone 3: PA induction axiom shell. -/
axiom pathB_inductionAxiomShell_capstone {hpa : 𝗣𝗔 ⊢ ↑goodsteinSentence} :
    RouteBPeanoMinusAxiomLeaves hpa → RouteBInductionAxiomShell hpa

/-- Capstone 4: closed witness/existential budget extraction. -/
axiom pathB_closedWitnessBudgets_capstone {hpa : 𝗣𝗔 ⊢ ↑goodsteinSentence} :
    RouteBInductionAxiomShell hpa → RouteBClosedWitnessBudgets hpa

/-- Capstone 5: structural embedding into the `someK` bounded operator calculus. -/
axiom pathB_someKStructuralEmbedding_capstone {hpa : 𝗣𝗔 ⊢ ↑goodsteinSentence} :
    RouteBClosedWitnessBudgets hpa → RouteBSomeKStructuralEmbedding hpa

/-- Capstone 6: bounded operator cut-elimination. -/
axiom pathB_operatorCutElimination_capstone {hpa : 𝗣𝗔 ⊢ ↑goodsteinSentence} :
    RouteBSomeKStructuralEmbedding hpa → RouteBOperatorCutElimination hpa

/-- Capstone 7: projection from the operator calculus to the Towsner subformula fragment. -/
axiom pathB_subformulaProjection_capstone {hpa : 𝗣𝗔 ⊢ ↑goodsteinSentence} :
    RouteBOperatorCutElimination hpa → RouteBSubformulaProjection hpa

/-- Capstone 8: extraction of the concrete Goodstein fragment terminal object. -/
axiom pathB_goodsteinFragmentExtraction_capstone {hpa : 𝗣𝗔 ⊢ ↑goodsteinSentence} :
    RouteBSubformulaProjection hpa → RouteBGoodsteinFragmentExtraction hpa

/-- Capstone 9, discharged: the fragment-extraction marker carries the terminal `RouteBCapstone`. -/
theorem pathB_terminalRouteBridge_capstone {hpa : 𝗣𝗔 ⊢ ↑goodsteinSentence} :
    RouteBGoodsteinFragmentExtraction hpa → RouteBCapstone
  | .terminal route => route

/-- Stage 1: sentence-shape normalization. -/
theorem pathB_goodsteinSentenceShape_stage {hpa : 𝗣𝗔 ⊢ ↑goodsteinSentence} :
    RouteBGoodsteinSentenceShape hpa :=
  pathB_goodsteinSentenceShape_capstone (hpa := hpa)

/-- Stage 2: finite `𝗣𝗔⁻` and equality axiom leaves, after sentence-shape normalization. -/
theorem pathB_peanoMinusAxiomLeaves_stage {hpa : 𝗣𝗔 ⊢ ↑goodsteinSentence} :
    RouteBPeanoMinusAxiomLeaves hpa :=
  pathB_peanoMinusAxiomLeaves_capstone (pathB_goodsteinSentenceShape_stage (hpa := hpa))

/-- Stage 3: PA induction axiom shell, after the finite axiom leaves. -/
theorem pathB_inductionAxiomShell_stage {hpa : 𝗣𝗔 ⊢ ↑goodsteinSentence} :
    RouteBInductionAxiomShell hpa :=
  pathB_inductionAxiomShell_capstone (pathB_peanoMinusAxiomLeaves_stage (hpa := hpa))

/-- Stage 4: closed witness/existential budgets, after induction-shell simulation. -/
theorem pathB_closedWitnessBudgets_stage {hpa : 𝗣𝗔 ⊢ ↑goodsteinSentence} :
    RouteBClosedWitnessBudgets hpa :=
  pathB_closedWitnessBudgets_capstone (pathB_inductionAxiomShell_stage (hpa := hpa))

/-- Stage 5: whole-proof structural embedding into the `someK` bounded operator calculus. -/
theorem pathB_someKStructuralEmbedding_stage {hpa : 𝗣𝗔 ⊢ ↑goodsteinSentence} :
    RouteBSomeKStructuralEmbedding hpa :=
  pathB_someKStructuralEmbedding_capstone (pathB_closedWitnessBudgets_stage (hpa := hpa))

/-- Stage 6: bounded operator cut-elimination. -/
theorem pathB_operatorCutElimination_stage {hpa : 𝗣𝗔 ⊢ ↑goodsteinSentence} :
    RouteBOperatorCutElimination hpa :=
  pathB_operatorCutElimination_capstone (pathB_someKStructuralEmbedding_stage (hpa := hpa))

/-- Stage 7: subformula projection to Towsner's fragment. -/
theorem pathB_subformulaProjection_stage {hpa : 𝗣𝗔 ⊢ ↑goodsteinSentence} :
    RouteBSubformulaProjection hpa :=
  pathB_subformulaProjection_capstone (pathB_operatorCutElimination_stage (hpa := hpa))

/-- Stage 8: extraction of the concrete Goodstein fragment. -/
theorem pathB_goodsteinFragmentExtraction_stage {hpa : 𝗣𝗔 ⊢ ↑goodsteinSentence} :
    RouteBGoodsteinFragmentExtraction hpa :=
  pathB_goodsteinFragmentExtraction_capstone (pathB_subformulaProjection_stage (hpa := hpa))

/-- Stage 9: terminal Path-B bridge to the lower-bound target. -/
theorem pathB_terminalRouteBridge_stage {hpa : 𝗣𝗔 ⊢ ↑goodsteinSentence} :
    RouteBCapstone :=
  pathB_terminalRouteBridge_capstone (pathB_goodsteinFragmentExtraction_stage (hpa := hpa))

/-- Compose the named Path-B stage chain into the single bridge expected by the terminal assembly. -/
def routeBBridgeFromCapstoneAxioms : RouteBBridgeFromPAProof := by
  intro hpa
  exact pathB_terminalRouteBridge_stage (hpa := hpa)

/-- The Path-B ledger theorem: once the nine named capstones are discharged, the terminal lower-bound
theorem immediately gives the Kirby-Paris headline. -/
theorem peano_not_proves_goodstein_of_pathBCapstoneAxioms : 𝗣𝗔 ⊬ ↑goodsteinSentence :=
  peano_not_proves_goodstein_of_routeBBridge routeBBridgeFromCapstoneAxioms

attribute [goodstein_blueprint 1 clean "proved_bookkeeping" "0" 100 pathB_goodsteinSentenceShape_stage
  []
  ["Kirby-Paris 1982, Goodstein sentence as the PA target",
   "GoodsteinPA.Encoding.goodsteinSentence: transparent closed Π₂ Goodstein target",
   "GoodsteinPA.Embedding: PA provability unfolds to a singleton closed sequent over the same language"]
  "Record that the Path-B input is already a PA proof of the closed encoded Goodstein sentence."]
  pathB_goodsteinSentenceShape_capstone

attribute [goodstein_blueprint 2 debt "capstone_axiom" "1-2" 80 pathB_peanoMinusAxiomLeaves_stage
  [pathB_goodsteinSentenceShape_stage]
  ["Foundation PeanoMinus.Basic: finite PA-minus axiom inventory and [simp] standard-model truth",
   "Foundation FirstOrder Theory.EqAxiom.finite: equality axioms are finite for the arithmetic language",
   "Towsner, Goodstein's Theorem, epsilon_0, and Unprovability, Section 16: embedding PA axioms into Z_infty",
   "GoodsteinPA.OperatorZinfty.ZekdBoundedTruth and ZekdSomeK.ofBoundedTruth: bounded true leaves now derive in the witness-bounded operator calculus"]
  "Discharge the finite PA-minus/equality axiom leaves by proving their finite bounded-truth certificates; the generic operator recursion is now closed, leaving the explicit axiom case split, with addEqOfLt as the only existential-witness case."]
  pathB_peanoMinusAxiomLeaves_capstone

attribute [goodstein_blueprint 3 debt "capstone_axiom" "4-8" 65 pathB_inductionAxiomShell_stage
  [pathB_peanoMinusAxiomLeaves_stage]
  ["Towsner Sections 16 and 18: PA induction through the infinitary calculus",
   "Buchholz Theorem 5.5 / local metaInduction_cong pattern for induction axioms",
   "Foundation Arithmetic.Schemata: succInd and InductionScheme",
   "GoodsteinPA.OperatorZinfty.inductionLeaf_cutTowerStepWithTerm_someK_probe: successor-induction cut tower runs directly in the someK calculus"]
  "Simulate the PA induction-axiom shell without losing the finite witness budget; the local with-term successor step now absorbs independent existential premise budgets."]
  pathB_inductionAxiomShell_capstone

attribute [goodstein_blueprint 4 debt "capstone_axiom" "2-5" 75 pathB_closedWitnessBudgets_stage
  [pathB_inductionAxiomShell_stage]
  ["Towsner Section 15: witness-bounded derivations",
   "Towsner Section 19.6: forall/existential cut interaction and witness bound",
   "GoodsteinPA.OperatorZinfty.embedding_closedTermExI_someK_probe and ZekdSomeK.lift"]
  "Extract finite K budgets for every Foundation existential and closed-witness step."]
  pathB_closedWitnessBudgets_capstone

attribute [goodstein_blueprint 5 debt "capstone_axiom" "4-8" 65 pathB_someKStructuralEmbedding_stage
  [pathB_closedWitnessBudgets_stage]
  ["Towsner Theorems 16.1/16.5/16.7: embedding PA proofs into Z_infty",
   "GoodsteinPA.OperatorZinfty: ZekdSomeK structural combinators",
   "GoodsteinPA.OperatorZinfty.inductionLeaf_allOmegaFromStep_someK_probe: someK packaging for the bounded induction chain",
   "GoodsteinPA.OperatorZinfty.inductionLeaf_cutTowerStepWithTerm_someK_probe: local induction leaf composes at the someK surface"]
  "Embed the whole PA proof into the someK witness-bounded operator calculus; both the running-index outer layer and the local successor-induction cut tower now export existential K shapes."]
  pathB_someKStructuralEmbedding_capstone

attribute [goodstein_blueprint 6 debt "capstone_axiom" "5-10" 65 pathB_operatorCutElimination_stage
  [pathB_someKStructuralEmbedding_stage]
  ["Towsner Section 19, especially Theorems 19.5, 19.6, 19.7, 19.9: cut elimination",
   "GoodsteinPA.OperatorZinfty: control-ordinal witness-bounded operator calculus",
   "GoodsteinPA.OperatorZinfty.ZekdSomeK.cutReduceConj/cutReduceDisj/cutReduceAllAux: someK cut-reduction surfaces",
   "GoodsteinPA.OperatorZinfty.ZekdSomeK.cutReduceAllAux_control: fixed-family forall/ex reduction composes with control-ordinal raising"]
  "Run bounded operator cut-elimination while preserving finite witness budgets; principal propositional cuts, fixed-family forall/ex reduction, and control raising are now exposed at the someK surface, leaving the running-index operator-control replacement isolated."]
  pathB_operatorCutElimination_capstone

attribute [goodstein_blueprint 7 debt "capstone_axiom" "3-6" 65 pathB_subformulaProjection_stage
  [pathB_operatorCutElimination_stage]
  ["Towsner Section 17.1: lower bound for witness-bounded cut-free derivations",
   "GoodsteinPA.LowerBound: LowerBoundHardy.B and allInv/mono_k terminal calculus",
   "GoodsteinPA.OperatorZinfty.ZekdSomeK.orInv/andInvL/andInvR/allInv: someK subformula-inversion surfaces"]
  "Project the cut-free operator derivation to the subformula fragment consumed by the lower-bound theorem; operator-side someK inversions now match the lower-bound inversion interface."]
  pathB_subformulaProjection_capstone

attribute [goodstein_blueprint 8 debt "capstone_axiom" "2-5" 65 pathB_goodsteinFragmentExtraction_stage
  [pathB_subformulaProjection_stage]
  ["Towsner Section 17.1: Goodstein fragment forall x exists y g_y(x)=0",
   "GoodsteinPA.LowerBound.lowerBound_hardy_selfcontained: concrete Hardy/Goodstein lower bound",
   "GoodsteinPA.PathBProbe.RouteBGoodsteinFragmentExtraction.terminal: fragment extraction now packages RouteBCapstone directly"]
  "Identify the projected derivation with the concrete Goodstein-fragment terminal object packaged as RouteBCapstone."]
  pathB_goodsteinFragmentExtraction_capstone

attribute [goodstein_blueprint 9 clean "proved_bridge" "0" 100 pathB_terminalRouteBridge_capstone
  [pathB_goodsteinFragmentExtraction_stage]
  ["Towsner Section 20: assembly of unprovability from bounded embedding, cut elimination, and lower bound",
   "Kirby-Paris 1982: PA unprovability of Goodstein's theorem",
   "GoodsteinPA.PathBProbe.no_routeBCapstone: terminal contradiction from the promoted lower bound"]
  "Unpack the terminal RouteBCapstone carried by the fragment-extraction marker."]
  pathB_terminalRouteBridge_capstone

end GoodsteinPA.PathBProbe
