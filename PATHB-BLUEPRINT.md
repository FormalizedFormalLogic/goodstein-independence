# Path B Blueprint: Open Capstones

Generated from `@[goodstein_blueprint ...]` attributes in Lean declarations.

| # | Declaration | Stage theorem | Category | Laps | Confidence | Uses |
|---:|---|---|---:|---:|---:|---|
| 2 | `GoodsteinPA.PathBProbe.pathB_peanoMinusAxiomLeaves_capstone` | `GoodsteinPA.PathBProbe.pathB_peanoMinusAxiomLeaves_stage` | debt | 1-2 | 80% | GoodsteinPA.PathBProbe.pathB_goodsteinSentenceShape_stage |
| 3 | `GoodsteinPA.PathBProbe.pathB_inductionAxiomShell_capstone` | `GoodsteinPA.PathBProbe.pathB_inductionAxiomShell_stage` | debt | 4-8 | 65% | GoodsteinPA.PathBProbe.pathB_peanoMinusAxiomLeaves_stage |
| 4 | `GoodsteinPA.PathBProbe.pathB_closedWitnessBudgets_capstone` | `GoodsteinPA.PathBProbe.pathB_closedWitnessBudgets_stage` | debt | 2-5 | 75% | GoodsteinPA.PathBProbe.pathB_inductionAxiomShell_stage |
| 5 | `GoodsteinPA.PathBProbe.pathB_someKStructuralEmbedding_capstone` | `GoodsteinPA.PathBProbe.pathB_someKStructuralEmbedding_stage` | debt | 4-8 | 65% | GoodsteinPA.PathBProbe.pathB_closedWitnessBudgets_stage |
| 6 | `GoodsteinPA.PathBProbe.pathB_operatorCutElimination_capstone` | `GoodsteinPA.PathBProbe.pathB_operatorCutElimination_stage` | debt | 5-10 | 65% | GoodsteinPA.PathBProbe.pathB_someKStructuralEmbedding_stage |
| 7 | `GoodsteinPA.PathBProbe.pathB_subformulaProjection_capstone` | `GoodsteinPA.PathBProbe.pathB_subformulaProjection_stage` | debt | 3-6 | 65% | GoodsteinPA.PathBProbe.pathB_operatorCutElimination_stage |
| 8 | `GoodsteinPA.PathBProbe.pathB_goodsteinFragmentExtraction_capstone` | `GoodsteinPA.PathBProbe.pathB_goodsteinFragmentExtraction_stage` | debt | 2-5 | 65% | GoodsteinPA.PathBProbe.pathB_subformulaProjection_stage |

## Outline

### 2. `GoodsteinPA.PathBProbe.pathB_peanoMinusAxiomLeaves_capstone`

- Stage theorem: `GoodsteinPA.PathBProbe.pathB_peanoMinusAxiomLeaves_stage`
- Kind: `capstone_axiom`
- Category claim: `debt`
- Estimate: 1-2 laps, 80% confidence
- Summary: Discharge the finite PA-minus/equality axiom leaves by proving their finite bounded-truth certificates; the generic operator recursion is now closed, leaving the explicit axiom case split, with addEqOfLt as the only existential-witness case.
- Literature / evidence:
  - Foundation PeanoMinus.Basic: finite PA-minus axiom inventory and [simp] standard-model truth
  - Foundation FirstOrder Theory.EqAxiom.finite: equality axioms are finite for the arithmetic language
  - Towsner, Goodstein's Theorem, epsilon_0, and Unprovability, Section 16: embedding PA axioms into Z_infty
  - GoodsteinPA.OperatorZinfty.ZekdBoundedTruth and ZekdSomeK.ofBoundedTruth: bounded true leaves now derive in the witness-bounded operator calculus

### 3. `GoodsteinPA.PathBProbe.pathB_inductionAxiomShell_capstone`

- Stage theorem: `GoodsteinPA.PathBProbe.pathB_inductionAxiomShell_stage`
- Kind: `capstone_axiom`
- Category claim: `debt`
- Estimate: 4-8 laps, 65% confidence
- Summary: Simulate the PA induction-axiom shell without losing the finite witness budget; the local with-term successor step now absorbs independent existential premise budgets.
- Literature / evidence:
  - Towsner Sections 16 and 18: PA induction through the infinitary calculus
  - Buchholz Theorem 5.5 / local metaInduction_cong pattern for induction axioms
  - Foundation Arithmetic.Schemata: succInd and InductionScheme
  - GoodsteinPA.OperatorZinfty.inductionLeaf_cutTowerStepWithTerm_someK_probe: successor-induction cut tower runs directly in the someK calculus

### 4. `GoodsteinPA.PathBProbe.pathB_closedWitnessBudgets_capstone`

- Stage theorem: `GoodsteinPA.PathBProbe.pathB_closedWitnessBudgets_stage`
- Kind: `capstone_axiom`
- Category claim: `debt`
- Estimate: 2-5 laps, 75% confidence
- Summary: Extract finite K budgets for every Foundation existential and closed-witness step.
- Literature / evidence:
  - Towsner Section 15: witness-bounded derivations
  - Towsner Section 19.6: forall/existential cut interaction and witness bound
  - GoodsteinPA.OperatorZinfty.embedding_closedTermExI_someK_probe and ZekdSomeK.lift

### 5. `GoodsteinPA.PathBProbe.pathB_someKStructuralEmbedding_capstone`

- Stage theorem: `GoodsteinPA.PathBProbe.pathB_someKStructuralEmbedding_stage`
- Kind: `capstone_axiom`
- Category claim: `debt`
- Estimate: 4-8 laps, 65% confidence
- Summary: Embed the whole PA proof into the someK witness-bounded operator calculus; both the running-index outer layer and the local successor-induction cut tower now export existential K shapes.
- Literature / evidence:
  - Towsner Theorems 16.1/16.5/16.7: embedding PA proofs into Z_infty
  - GoodsteinPA.OperatorZinfty: ZekdSomeK structural combinators
  - GoodsteinPA.OperatorZinfty.inductionLeaf_allOmegaFromStep_someK_probe: someK packaging for the bounded induction chain
  - GoodsteinPA.OperatorZinfty.inductionLeaf_cutTowerStepWithTerm_someK_probe: local induction leaf composes at the someK surface

### 6. `GoodsteinPA.PathBProbe.pathB_operatorCutElimination_capstone`

- Stage theorem: `GoodsteinPA.PathBProbe.pathB_operatorCutElimination_stage`
- Kind: `capstone_axiom`
- Category claim: `debt`
- Estimate: 5-10 laps, 65% confidence
- Summary: Run bounded operator cut-elimination while preserving finite witness budgets; principal propositional cuts, fixed-family forall/ex reduction, and control raising are now exposed at the someK surface, leaving the running-index operator-control replacement isolated.
- Literature / evidence:
  - Towsner Section 19, especially Theorems 19.5, 19.6, 19.7, 19.9: cut elimination
  - GoodsteinPA.OperatorZinfty: control-ordinal witness-bounded operator calculus
  - GoodsteinPA.OperatorZinfty.ZekdSomeK.cutReduceConj/cutReduceDisj/cutReduceAllAux: someK cut-reduction surfaces
  - GoodsteinPA.OperatorZinfty.ZekdSomeK.cutReduceAllAux_control: fixed-family forall/ex reduction composes with control-ordinal raising

### 7. `GoodsteinPA.PathBProbe.pathB_subformulaProjection_capstone`

- Stage theorem: `GoodsteinPA.PathBProbe.pathB_subformulaProjection_stage`
- Kind: `capstone_axiom`
- Category claim: `debt`
- Estimate: 3-6 laps, 65% confidence
- Summary: Project the cut-free operator derivation to the subformula fragment consumed by the lower-bound theorem; operator-side someK inversions now match the lower-bound inversion interface.
- Literature / evidence:
  - Towsner Section 17.1: lower bound for witness-bounded cut-free derivations
  - GoodsteinPA.LowerBound: LowerBoundHardy.B and allInv/mono_k terminal calculus
  - GoodsteinPA.OperatorZinfty.ZekdSomeK.orInv/andInvL/andInvR/allInv: someK subformula-inversion surfaces

### 8. `GoodsteinPA.PathBProbe.pathB_goodsteinFragmentExtraction_capstone`

- Stage theorem: `GoodsteinPA.PathBProbe.pathB_goodsteinFragmentExtraction_stage`
- Kind: `capstone_axiom`
- Category claim: `debt`
- Estimate: 2-5 laps, 65% confidence
- Summary: Identify the projected derivation with the concrete Goodstein-fragment terminal object packaged as RouteBCapstone.
- Literature / evidence:
  - Towsner Section 17.1: Goodstein fragment forall x exists y g_y(x)=0
  - GoodsteinPA.LowerBound.lowerBound_hardy_selfcontained: concrete Hardy/Goodstein lower bound
  - GoodsteinPA.PathBProbe.RouteBGoodsteinFragmentExtraction.terminal: fragment extraction now packages RouteBCapstone directly

## Audit

Run the stage theorem through `#print axioms` to see the actual kernel-level open assumptions.
