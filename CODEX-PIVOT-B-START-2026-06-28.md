# Pivot-B Start Review — 2026-06-28

## Short answer

Yes: starting B does not damage A.  Path A remains exactly where the current probe left it:
`wip/M2Probe.lean` is a typechecked, reviewable artifact, and the hard A object is still the
Foundation PA-induction axiom leaf / shell simulation.  We can return to that file later without
losing the compiler-grounded information already gained.

The only real cost of starting B is attention.  Mathematically, no A proof state is consumed by B.

## What I just added

New file:

- `wip/PathBProbe.lean`

Checked with:

```bash
lake env lean wip/PathBProbe.lean
```

Result: typechecks cleanly.

The probe defines the B terminal object:

```lean
def CutFreeGoodsteinBounded (α : ONote) (k : ℕ) : Prop :=
  LowerBoundHardy.B α k ({LowerBoundHardy.GForm.gAll} : LowerBoundHardy.Seq)
```

and proves that the promoted lower-bound theorem already rules it out:

```lean
theorem no_cutFreeGoodsteinBounded {α : ONote} (hα : α.NF) (k : ℕ) :
    ¬ CutFreeGoodsteinBounded α k
```

It also isolates the exact B bridge still missing:

```lean
def RouteBBridgeFromPAProof : Prop :=
  (𝗣𝗔 ⊢ ↑goodsteinSentence) → RouteBCapstone
```

and proves the capstone assembly:

```lean
theorem peano_not_proves_goodstein_of_routeBBridge
    (hbridge : RouteBBridgeFromPAProof) : 𝗣𝗔 ⊬ ↑goodsteinSentence
```

So B is now shaped around the correct bounded target, not the old unbounded one.

## Important correction: do not revive old Route-B as-is

`wip/Bounding.lean` is useful only as an assembly-shape warning.  It explicitly says its key bridge is
false as stated, because it routes through the unbounded `Z∞` calculus and loses Towsner's witness
bound `k`.

The live B target must be:

```lean
∃ α : ONote, α.NF ∧ ∃ k : ℕ,
  LowerBoundHardy.B α k ({LowerBoundHardy.GForm.gAll} : LowerBoundHardy.Seq)
```

not merely an unbounded cut-free `Z∞` derivation below ε₀.

## What looks good for B

The terminal lower-bound half is real.  `src/GoodsteinPA/LowerBound.lean` already contains
`lowerBound_hardy_selfcontained`, which proves there is no witness-bounded cut-free derivation of
the Goodstein sentence at any normal-form `ONote` and any budget `k`.

This is a better starting point than A currently has: B has a finished contradiction theorem waiting
for the right extracted object.  A still needs the Foundation-to-Z induction-axiom simulation before
it has an equivalent decisive bridge.

## What is still hard

B is not free.  The missing theorem is a bounded embedding / bounded cut-elimination bridge:

```lean
(𝗣𝗔 ⊢ ↑goodsteinSentence) →
  ∃ α : ONote, α.NF ∧ ∃ k : ℕ,
    LowerBoundHardy.B α k ({LowerBoundHardy.GForm.gAll} : LowerBoundHardy.Seq)
```

That bridge must preserve the witness bound through the proof transformation.  If it silently falls
back to `GoodsteinPA.ZinftyF.Provable`, the route repeats the known false move.

## Recommended next B step

Start with the bounded bridge, not the headline:

1. Choose or revive the witness-bounded derivation object intended to sit between PA proofs and
   `LowerBoundHardy.B`.
2. Re-prove the cheap structural embedding cases against that bounded object.
3. Size the two axiom-leaf cases honestly: universal `PA⁻` axioms and the PA induction axiom.
4. Only then wire the bounded cut-free object into `LowerBoundHardy.B`.

Decision read: B is safe to start and has a stronger terminal asset than A, but the honest wall is the
bounded embedding/cut-elimination bridge.  Starting B now does not close or burn A; it just gives us a
second compiler-checked lane to compare against A's induction-leaf wall.

## Next probe result: named obligations + hardest witness check

Update: `wip/PathBProbe.lean` now exposes the missing B bridge as named obligations via
`RouteBNamedObligations`, with the PA-induction axiom leaf named separately as
`boundedInductionAxiomLeaf`.  This is intentionally an assumption package, not global Lean `axiom`s:
the route can be reviewed by named missing theorem without silently adding axioms to the environment.

I also started the hardest leaf in `wip/OperatorZinfty.lean`, against the actual witness-bounded
`Zekd` calculus.  The decisive witness-side facts typecheck:

```lean
theorem inductionLeaf_fixedIndex_witnessBound_impossible (e : ONote) (k d : ℕ) :
    ¬ ∀ n : ℕ, n ≤ hardy e (k + d)

theorem inductionLeaf_runningIndex_witnessBound (e : ONote) (k d n : ℕ) :
    n ≤ hardy e (max k n + d)

theorem inductionLeaf_exI_runningIndex_probe
    ... :
    Zekd α e (max k n) d c (insert (∃⁰ φ) Γ)
```

Read: the induction leaf is impossible if formulated with a fixed numeric index, but it is not blocked
by the witness bound when formulated in the Towsner shape, where the `n`-th `allω` premise runs at
`max k n`.  Remaining work is the structural port of the finite EM/cut/value-substitution tower from
`EmbeddingBound.metaInduction_cong_bdd` to `Zekd`; the most suspicious arithmetic side condition just
passed its first compiler check.

Follow-up probe: the local cut-tower step also typechecks.  New kernels:

```lean
theorem inductionLeaf_cutTowerStep_probe

theorem inductionLeaf_valueSubst_cut_probe

theorem inductionLeaf_cutTowerStepWithTerm_probe
```

The last theorem is the closest to the real PA-induction leaf: it lets the successor occurrence remain
an arbitrary closed term `succT`, builds the bad-step contradiction in `Zekd`, introduces
`∃ badStep` with the running witness budget, cuts from `ψ(n)` to `ψ(succT)`, and then uses a
value-substitution cut to obtain the numeral instance `ψ(n+1)`.

What this buys: the bounded calculus rule wiring for the induction leaf is tractable.  What remains is
not the `Zekd` witness arithmetic but the finite congruent-EM/value-substitution leaf engine and the
outer finite induction/closure packaging.

Follow-up probe: the outer finite induction and `allω` packaging now typecheck too.  New kernels:

```lean
theorem inductionLeaf_allOmegaFromStep_probe

theorem inductionLeaf_allOmegaCutTowerNumeral_probe

theorem inductionLeaf_allOmegaCutTowerWithTerm_probe
```

The first theorem packages any running finite chain `ψ(0) → ψ(1) → ...` into `Zekd.allω`, using
`mono_k` to raise the successor step from index `max k n` to the next premise index `max k (n+1)`.
The numeral theorem specializes that package to the value-congruence-free cut tower, where the local
step already concludes `ψ(n+1)`.  The final theorem is the stronger arbitrary-successor-term version:
it adds the explicit congruent-value cut needed to replace `ψ(succT)` by `ψ(n+1)`.

Read: the PA-induction leaf's `Zekd` side now composes from local step, through finite induction,
through the ω-rule.  The remaining hard pieces are the actual finite EM/congruent-value derivations
and the closure/axiom-shell plumbing, not the running witness index.

Follow-up probe: started the real bounded embedding infrastructure.  New checked kernels:

```lean
abbrev stdClosedVal

lemma stdClosedVal_nm
lemma embedding_subst_q_cons
lemma embedding_subst_q_cons_app
lemma embedding_valm_subst_congr
lemma embedding_valm_cons_nm_congr

theorem embedding_valueCongruentRelAtom_probe
theorem embedding_valueCongruentNrelAtom_probe

theorem embedding_valueCongruentRelSubstAtom_probe
theorem embedding_valueCongruentNrelSubstAtom_probe

theorem embedding_valueCongruentVerum_probe
theorem embedding_valueCongruentFalsum_probe

theorem embedding_valueCongruentAndFromChildren_probe
theorem embedding_valueCongruentOrFromChildren_probe

theorem embedding_closedTermExI_of_valueCongruentEM_probe
```

The atomic leaves are the bounded `Zekd` version of the value-congruent excluded-middle base cases from
the old unbounded embedding.  They close sequents containing `R(v), ¬R(v')` or `¬R(v), R(v')` when the
closed term vectors have equal standard values.

The latest pass adds the first parent layer of the bounded EM engine.  The `AndFromChildren` and
`OrFromChildren` kernels compose already-proved child value-congruence sequents through `Zekd.andI` and
`Zekd.orI`, with every ordinal and norm budget explicit.  The new `stdClosedVal_nm`,
`embedding_subst_q_cons_app`, and `embedding_valm_cons_nm_congr` lemmas are the local support facts
needed when the next recursive pass enters the `∀`/`∃` cases.

The closed-term `exI` adapter is the more important infrastructure step: once an open Foundation witness
term has been closed by an assignment, `stdClosedVal s` is the numeral used by `Zekd.exI`.  The theorem
reduces the bounded `exs` rule to two exact obligations:

1. produce the value-congruent premise converting `ψ[s]` to `ψ[nm (stdClosedVal s)]`;
2. prove the bound `stdClosedVal s ≤ hardy e (k+d)`.

Follow-up probe: the recursive bounded value-congruence shell now typechecks.  First came the
quantifier-free closed-term specialization:

```lean
def QFreeForm

theorem embedding_valueCongruentQFreeClosedTerm_probe
```

Then the arity-general theorem landed:

```lean
theorem embedding_valueCongruentEM_probe
```

It closes `ψ[w], ¬ψ[w']` at explicit finite height `ONote.ofNat (2*q)` for arbitrary formulas when
`ψ.complexity ≤ q` and the closed assignments have pointwise equal standard values.  The quantifier
cases are the important part: both `∀` and `∃` now package through `Zekd.allω`, and the paired `exI`
witness `m` is paid at the running premise index `max K m` via
`inductionLeaf_runningIndex_witnessBound`.

Read: the bounded EM/value-congruence engine itself is no longer the suspected wall.  The next embedding
work is to thread assignment-closed term bounds through the Foundation `exs` case and feed this EM theorem
into the existing closed-term `exI` adapter.

Follow-up probe: the EM theorem now feeds the closed-term existential adapter directly:

```lean
theorem embedding_closedTermExI_probe
theorem closedTerm_witnessBound_of_budget
theorem embedding_closedTermExI_raiseK_probe
def ZekdSomeK
theorem embedding_closedTermExI_someK_probe
```

Given a bounded derivation of `ψ[s]`, it introduces `∃⁰ ψ` by generating the congruent EM premise
internally from `embedding_valueCongruentEM_probe`.  The exposed side condition is now exactly the real
term-bound obligation `stdClosedVal s ≤ hardy e (K+d)`, plus ordinal/norm bookkeeping.

The `raiseK` adapter discharges that side condition locally by monotonicity: a derivation at `K` can be
raised to `max K (stdClosedVal s)`, where `stdClosedVal s ≤ hardy e (max K (stdClosedVal s)+d)` follows
from `le_hardy`.  So the remaining Path-B embedding work is not more logical rule plumbing; it is the
global finite-budget pass that propagates these `K` raises through the proof embedding and extracts one
terminal witness budget.

The `someK` version is the local interface for that pass: if the premise is derivable at some finite
`K`, the closed-term existential conclusion is derivable at some larger finite `K`, with all local norm
and witness side conditions paid internally.
