/-
# `wip/GentzenCon.lean` — Crux 2 scaffold: Gentzen `PRWO(ε₀) → Con(𝗣𝗔)` (Rathjen 2014 Thm 2.8)

**Status: DISCLOSED-SORRY SCAFFOLD (wip, off the build target).** This file grounds the second
Phase-2 girder of `Reduction.goodstein_implies_consistency` into a typed, lemma-by-lemma architecture.
Every deep obligation is an honest `sorry`/`axiom` citing Rathjen 2014 §2 (read lap 49, see
`CRUX2-GENTZEN-2026-06-23.md`). The point of the scaffold is to (a) pin the **PRWO formulation** — the
shared hinge of both cruxes and the project's highest confabulation-risk piece — as a concrete,
type-checked `Sentence ℒₒᵣ` built on the repo's *existing* ε₀-ordering formula `precφ`, with a
standard-model faithfulness audit; and (b) validate that crux 1 (`γ → PRWO`) and crux 2 (`PRWO → Con`)
chain into exactly the `𝗣𝗔 ⊢ γ → 𝗣𝗔 ⊢ Con(𝗣𝗔)` interface that `Reduction.lean` needs.

## Why PRWO is a *schema* (per-formula), not a single ∀-over-indices sentence
Rathjen states PRWO(ε₀) = "no infinitely descending **primitive recursive** ε₀-sequence." Expressing
"`f` is primitive recursive" with the index `e` as an **object** variable would need a universal
evaluator / Kleene-T predicate arithmetized inside the theory. **Foundation has none** (mapped lap 50:
`code`/`codeOfPartrec'`/`codeOfREPred` all encode a *meta-level* function into a *fixed* formula; there
is no `Eval(e,n,y)` with `e` a first-order term). So — as is standard for Gentzen/Rathjen in PA — PRWO is
a **schema**: one instance `prwoInstance seq` per ℒₒᵣ-formula `seq(y,n)` (= "the graph `y = f n`").
This is exactly what the proof needs:
* **crux 1** (`γ → PRWO`, Rathjen §3) proves the instance for an *arbitrary* primrec descent graph;
* **crux 2** (`PRWO → Con`, Gentzen) uses the *single* instance for `n ↦ ord(Rⁿ d₀)`.

## The ε₀-ordering is the **transparent internal `icmp`-comparison** (lap-56 REDIRECT)
**Prior (lap-50) choice — REJECTED lap 56.** `SeamDefinability.precφ : Semisentence ℒₒᵣ 2` is
`codeOfREPred₂ (natCode a < natCode b)` — Foundation's **opaque r.e.-code blob**. Its spec
`precφ_spec` is a **standard-model-ONLY** statement (`ℕ ⊧/![m,n] precφ ↔ natCode m < natCode n`); in a
**nonstandard** `M`, `M ⊧/![z,y] precφ` is an opaque Σ₁ existential search whose truth is NOT cleanly
`z ≺ y`. Building `prwoInstance` on `precφ` therefore re-creates the **wall-B opacity** that lap 36
*dissolved* for `goodsteinSentence` (memory `crux1-headline-needs-only-standard-level` neighbour;
`STATUS` lap-36) — the per-model crux-1 obligation cannot reason through it, and it forces a separate
`natCode ↔ internal-NF-code` order bridge (the lap-55 "new sub-target").

**Lap-56 fix (mirrors the lap-36 wall-B dissolution).** Use the repo's **transparent internal** ε₀-code
comparison `InternalONote.icmp` (`icmp a b = 0` ⟺ `a ≺ b`), whose graph formula
`icmpDef : 𝚺₁.Semisentence 3` has the **model-general** spec `icmp_defined.iff`
(`M ⊧/![c,a,b] icmpDef ↔ c = icmp a b`, in EVERY `M ⊧ₘ* 𝗜𝚺₁`, ℕ included). Then `prec_internal z y`
(below) unfolds transparently to `icmp z y = 0` in any `M`. Two wins: (i) the per-model obligation reasons
directly with `icmp z y = 0` — the **same** internal order `igoodstein` uses, so PRWO and the Goodstein
bridge share ONE ε₀-coding (no cross-coding mismatch), and (ii) the `natCode↔NF` bridge **dissolves**:
`nonterminating_of_seq_descent`'s descent hypothesis IS already the `icmp`-descent form
`StdCor34.crux1_internal_run_of_width_dom` consumes (`hβdesc : icmp (β (n+1)) (β n) = 0`).
*Faithfulness follow-up:* strengthen the std-model anchor with `icmp a b = 0 ↔ natCode a < natCode b`
on ℕ (a decidable std-only fact) to tie `icmp` to the mathlib-ε₀ order-type anchor; not blocking.
-/
import GoodsteinPA.SeamDefinability
import GoodsteinPA.InternalONote
import GoodsteinPA.StdCor34
import GoodsteinPA.StdCor34F
import GoodsteinPA.Reduction

namespace GoodsteinPA.GentzenCon

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open GoodsteinPA GoodsteinPA.SeamDefinability GoodsteinPA.Epsilon0Complete GoodsteinPA.InternalPow
open GoodsteinPA.InternalONote GoodsteinPA.IIter

/-! ## Step 1 — the PRWO formulation (the shared hinge) -/

/-- **Transparent internal ε₀-order** (lap-56). `prec_internal z y` ⟺ `icmp z y = 0` ⟺ `z ≺ y`, in
EVERY `M ⊧ₘ* 𝗜𝚺₁`. Built from `InternalONote.icmpDef` (the `𝚺₁` graph of `icmp`), so — unlike the opaque
`precφ` (`codeOfREPred₂`, std-model-only spec) — it unfolds the SAME way in nonstandard models. -/
noncomputable def prec_internal : Semisentence ℒₒᵣ 2 :=
  “z y. ∃ c, !icmpDef c z y ∧ c = 0”

/-- `prec_internal` evaluates transparently to the internal `icmp`-order in any model. -/
theorem eval_prec_internal {M : Type*} [ORingStructure M] [M ⊧ₘ* 𝗜𝚺₁] (z y : M) :
    (M ⊧/![z, y] prec_internal) ↔ icmp z y = 0 := by
  simp [prec_internal, Semiformula.eval_substs, icmp_defined.iff]

/-- **PRWO(ε₀), one schema instance.** For a sequence presented by its graph formula
`seq(y, n)` ("`y` is the value at position `n`"; arg `#0` = value, `#1` = index, matching the
`codeOfPartrec'` output-first convention), `prwoInstance seq` is the closed `ℒₒᵣ`-sentence

  `¬ ∀ n y z, (seq(y,n) ∧ seq(z,n+1)) → z ≺ y`,

i.e. **"`seq` does not strictly ≺-descend at every step"** = "no infinite descent through `seq`."
For a *total functional* graph this is literally Rathjen's `∃ n, ¬(f(n+1) ≺ f n)` — which is the whole
content of PRWO, because `ε₀` is well-founded so any total `f` must fail to descend somewhere.
`z ≺ y` is `prec_internal z y` (= the transparent `icmp z y = 0`). -/
noncomputable def prwoInstance (seq : Semisentence ℒₒᵣ 2) : Sentence ℒₒᵣ :=
  “¬ ∀ n y z, (!seq y n ∧ !seq z (n + 1)) → !prec_internal z y”

/-- **General-model unfolding of `prwoInstance`** (the shared hinge of both cruxes). In any
`M ⊧ₘ* 𝗜𝚺₁`, `prwoInstance seq` holds iff the `seq`-graph does *not* `icmp`-descend at every step —
the clean ∀/∃ statement the per-model crux-1 obligation reasons with, stripped of the syntactic layer.
Transparent (`eval_prec_internal`), so it holds identically in nonstandard `M`. -/
theorem prwoInstance_models_iff (seq : Semisentence ℒₒᵣ 2)
    (M : Type*) [ORingStructure M] [M ⊧ₘ* 𝗜𝚺₁] :
    (M ⊧ₘ prwoInstance seq) ↔
      ¬ (∀ n y z : M, (M ⊧/![y, n] seq) → (M ⊧/![z, n + 1] seq) → icmp z y = 0) := by
  unfold prwoInstance
  rw [models_iff]
  simp only [Nat.succ_eq_add_one, Fin.isValue, Semiformula.eval_all,
    Semiformula.eval_substs, LogicalConnective.HomClass.map_neg,
    LogicalConnective.HomClass.map_imply, LogicalConnective.HomClass.map_and,
    LogicalConnective.Prop.neg_eq, LogicalConnective.Prop.arrow_eq, LogicalConnective.Prop.and_eq,
    Matrix.comp_vecCons', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Matrix.constant_eq_singleton, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    Semiterm.val_bvar, Semiterm.val_operator₂, Semiterm.val_operator₀, Structure.Add.add,
    Structure.numeral_eq_numeral, ORingStructure.one_eq_one, eval_prec_internal]
  constructor
  · intro h hall; exact h (fun a b c hconj => hall a b c hconj.1 hconj.2)
  · intro h hall; exact h (fun n y z hYN hZN => hall n y z ⟨hYN, hZN⟩)

/-- **Faithfulness audit (standard model).** In `ℕ`, `prwoInstance seq` holds **iff** the sequence
described by `seq` is not everywhere-≺-descending — the meta-level PRWO statement, with the order read
through `icmp` (the **same** internal ε₀-coding `igoodstein` uses). Encoding-correctness anchor (cf.
`Bridge.goodsteinSentence_faithful` for `γ`); a corollary of the general `prwoInstance_models_iff`. -/
theorem prwoInstance_faithful (seq : Semisentence ℒₒᵣ 2) :
    (ℕ ⊧ₘ prwoInstance seq) ↔
      ¬ (∀ n y z : ℕ, (ℕ ⊧/![y, n] seq) → (ℕ ⊧/![z, n + 1] seq) → icmp z y = 0) :=
  prwoInstance_models_iff seq ℕ

/-! ## Step 2 — the Gentzen reduction substrate (Rathjen 2014 Thm 2.8(i), p. 9)

Gentzen (via Buchholz [6]): an ordinal assignment `ord` and a reduction procedure `R` on coded `𝗣𝗔`
derivations, both **primitive recursive**, with `ord(R D) ≺ ord D` whenever `D` derives the empty
sequent (eq. (5)). Built over Foundation's arithmetized `Theory.Derivation : V → Prop`
(`Bootstrapping/Syntax/Proof/Basic.lean:459`); here stated over ℕ-codes for the meta layer. -/

/-- Ordinal assignment: a coded derivation ↦ its `natCode`-indexed `ε₀`-ordinal. Primitive recursive
(Buchholz [6]). Placeholder; the real `ord` is an `ℒₒᵣ`-arithmetized primrec function. -/
axiom ord : ℕ → ℕ

/-- Gentzen's reduction procedure on coded derivations. Primitive recursive (Buchholz [6]).
Placeholder; the real `R` is an `ℒₒᵣ`-arithmetized primrec function. -/
axiom R : ℕ → ℕ

/-- `R` maps a derivation of the empty sequent to another derivation of the empty sequent.
`derivesEmpty d` abbreviates "`d` codes a `𝗣𝗔`-derivation of `⊥`" (the meta stand-in for
`Theory.DerivationOf d ⌜⊥⌝`). -/
axiom derivesEmpty : ℕ → Prop

axiom R_preserves_empty {d : ℕ} : derivesEmpty d → derivesEmpty (R d)

/-- **Equation (5) — the deep Gentzen core.** The reduction strictly lowers the assigned ordinal,
in the **same transparent `icmp` order** `prwoInstance` measures (lap-56; was `natCode <`). THE
ordinal-analysis content (Buchholz [6] = `papers/buchholz-on-gentzens-first-consistency-proof.pdf`
+ `papers/siders-gentzen-consistency-proofs-arithmetic.pdf`). -/
axiom ord_R_descends {d : ℕ} : derivesEmpty d → icmp (ord (R d)) (ord d) = 0

/-- The Gentzen descent sequence `n ↦ ord(Rⁿ d)` from a derivation `d` of `⊥`. Strictly
≺-descending below `ε₀` (`icmp (·) (·) = 0`) by `ord_R_descends` + `R_preserves_empty` — an infinite
primrec descent, the witness against PRWO. -/
noncomputable def gentzenDescent (d : ℕ) : ℕ → ℕ := fun n => ord (R^[n] d)

theorem derivesEmpty_iterate {d : ℕ} (hd : derivesEmpty d) (n : ℕ) :
    derivesEmpty (R^[n] d) := by
  induction n with
  | zero => simpa using hd
  | succ k ih => rw [Function.iterate_succ_apply']; exact R_preserves_empty ih

theorem gentzenDescent_descends {d : ℕ} (hd : derivesEmpty d) (n : ℕ) :
    icmp (gentzenDescent d (n + 1)) (gentzenDescent d n) = 0 := by
  have hiter : derivesEmpty (R^[n] d) := derivesEmpty_iterate hd n
  simpa [gentzenDescent, Function.iterate_succ_apply'] using ord_R_descends hiter

/-- The `ℒₒᵣ`-formula presenting `n ↦ ord(Rⁿ d₀)` as a graph `seq(y,n)`, where `d₀` is the
canonical (least) derivation of `⊥` available under `¬Con`. Arithmetized from `ord`/`R`/`Theory.proof`
+ bounded iteration; placeholder pending the primrec encodings above. -/
axiom gentzenDescentφ : Semisentence ℒₒᵣ 2

/-! ## Step 3 — the two cruxes, and their assembly into the `Reduction.lean` interface -/

/-- **Crux 2 deep content — per-model semantic form (disclosed axiom, lap-58 REFRAME).** Gentzen's
eq-(5) arithmetized and lifted to every model `M ⊧ 𝗣𝗔`: if `𝗣𝗔` is **`M`-internally inconsistent**
(`¬ 𝗣𝗔.Consistent M`, i.e. `M` carries a coded `𝗣𝗔`-derivation of `⊥`), then the Gentzen descent graph
`gentzenDescentφ` (= `n ↦ ord(Rⁿ d₀)` with `d₀` the `M`-least `⊥`-proof) is **everywhere strictly
`≺`-descending in `M`** — an `M`-internal infinite `ε₀`-descent. This is the honest deep obligation in
exactly the per-model shape that the `ord`/`R` arithmetization plugs into (mirroring the proven crux-1
route): arithmetize `ord`/`R` over Foundation's `Theory.Derivation` and prove eq-(5) `ord(R d) ≺ ord d`
for `M`-coded `⊥`-derivations (Buchholz [6] = `papers/buchholz-on-gentzens-first-consistency-proof.pdf`;
`papers/siders-*.pdf`). Decomposes into the C1–C5 milestones (file footer / `PENDING_WORK`).
NOT on the headline `#print axioms` path (`Statement.lean` `sorry` untouched). -/
axiom gentzen_descent_of_inconsistent :
    ∀ (M : Type) [ORingStructure M] [M ⊧ₘ* 𝗜𝚺₁] [M ⊧ₘ* 𝗣𝗔], ¬ 𝗣𝗔.Consistent M →
      ∀ n y z : M, (M ⊧/![y, n] gentzenDescentφ) → (M ⊧/![z, n + 1] gentzenDescentφ) →
        icmp z y = 0

/-- **Crux 2 per-model obligation — PROVED from the deep axiom.** In every model `M ⊧ 𝗣𝗔`, if the PRWO
instance for the Gentzen descent holds, then `𝗣𝗔` is `M`-internally consistent. Contrapositive of
`gentzen_descent_of_inconsistent`: `M`-inconsistency makes the descent infinitely `≺`-descending, which
`prwoInstance gentzenDescentφ` (= "it does *not* descend everywhere") refutes. -/
theorem gentzen_consistent_of_prwo (M : Type) [ORingStructure M] [M ⊧ₘ* 𝗜𝚺₁] [M ⊧ₘ* 𝗣𝗔]
    (hprwo : M ⊧ₘ prwoInstance gentzenDescentφ) : 𝗣𝗔.Consistent M := by
  by_contra hcon
  rw [prwoInstance_models_iff] at hprwo
  exact hprwo (gentzen_descent_of_inconsistent M hcon)

/-- **Crux 2 — the internalized reduction, NOW A THEOREM (lap-58).** `𝗣𝗔` proves the object-level
implication `prwoInstance gentzenDescentφ 🡒 Con(𝗣𝗔)`. Was a single **opaque object-level axiom**; now
**discharged** via Foundation's arithmetic completeness (`provable_of_models`) from the clean per-model
`gentzen_consistent_of_prwo` — exactly the model-theoretic route crux 1 uses. The deep ordinal-analysis
content is now isolated in the per-model semantic axiom `gentzen_descent_of_inconsistent` (the right
shape for the `ord`/`R` arithmetization), and this object-level wrapper is real. -/
theorem gentzen_reduction_internalized :
    𝗣𝗔 ⊢ (prwoInstance gentzenDescentφ 🡒 ↑𝗣𝗔.consistent) := by
  apply provable_of_models 𝗣𝗔 _
  intro M _ _
  haveI : M ⊧ₘ* 𝗜𝚺₁ := ModelsTheory.of_provably_subtheory' M 𝗜𝚺₁ 𝗣𝗔
  simp only [Semantics.Imp.models_imply]
  intro hprwo
  exact (Bootstrapping.consistent.defined (T := 𝗣𝗔) (V := M)).mpr (gentzen_consistent_of_prwo M hprwo)

/-- **Crux 2 — Gentzen Thm 2.8(i): `PRWO(ε₀) → Con(𝗣𝗔)`.** If `𝗣𝗔` proves the PRWO instance for the
Gentzen descent, then `𝗣𝗔` proves its own consistency. Modus ponens on the now-real theorem
`gentzen_reduction_internalized`. -/
theorem gentzen_prwo_implies_consistency :
    𝗣𝗔 ⊢ prwoInstance gentzenDescentφ → 𝗣𝗔 ⊢ ↑𝗣𝗔.consistent :=
  fun hp => gentzen_reduction_internalized ⨀ hp

/-- **The seq-specific standard-domination certificate (Rathjen Lemma 3.2), width form (lap-57).** The
value at position `n+1` has `ε₀`-code complexity `iC` bounded by a fixed **standard**-level Grzegorczyk
function `iF l₀` — i.e. the *block width* `iC (β (n+1))` (the internal `Grz.corW`) is `iF l₀`-dominated.
This is exactly the input `StdCor34F.crux1_internal_run_F` needs (no off-by-one: the certificate is
stated at the `n+1` position so `hbound (β (n+1))` gives `iC (β (n+1)) ≤ iF l₀ n` directly). For
`seq = gentzenDescentφ` (= `n ↦ ord(Rⁿd₀)`) Rathjen Lemma 3.2 gives this `l₀` from `ord`/`R`'s fixed
build tree (the `d₀`-independent bound), keeping the headline on the **standard** level
(`crux1-headline-needs-only-standard-level`). For an *arbitrary* descent it can FAIL
(`Grz.F_diag_not_dominated`) — why crux 1 must carry it as a hypothesis. -/
def SeqStdBounded (seq : Semisentence ℒₒᵣ 2) (M : Type) [ORingStructure M] [M ⊧ₘ* 𝗜𝚺₁] : Prop :=
  ∃ l₀ : ℕ, 0 < l₀ ∧ ∀ n y : M, (M ⊧/![y, n + 1] seq) → iC y ≤ iF l₀ n

/-- **The seq is realized by a total, `𝚺₁`-definable, NF-nonzero-valued branch** (lap-57). For the
construction to produce a genuine internal infinite descent, the graph `seq(y,n)` must actually be
*total functional* with normal-form, nonzero ε₀-code values — packaged as a single function `β : M → M`
realizing the graph at every position, with an **explicit parameter-free `𝚺₁` graph** `βDef`
(`DefinedFunction₁ β βDef`, NOT merely `𝚺₁-Function₁ β`: the abstract `Definable` allows `V`-parameters,
which cannot be baked into the `BlkRecF` block-recursion blueprint). This is the honest content of "`seq`
is the graph of a primitive-recursive ε₀-valued function": for `seq = gentzenDescentφ` (= `n ↦ ord(Rⁿd₀)`)
it holds because `ord`/`R` are primrec (an explicit `𝚺₁` graph) and `ord` lands in nonzero NF codes.
Supplying `β` ties the infinite-descent existence to `seq` genuinely having a descending NF branch, so
the hypotheses are jointly unsatisfiable in `ℕ` (vacuously true there) and substantive only in
nonstandard `M`. -/
def SeqRealized (seq : Semisentence ℒₒᵣ 2) (M : Type) [ORingStructure M] [M ⊧ₘ* 𝗜𝚺₁] : Prop :=
  ∃ (β : M → M) (βDef : 𝚺₁.Semisentence 2), (∀ n : M, M ⊧/![β n, n] seq) ∧ (∀ n, isNF (β n)) ∧
    (∀ n, β n ≠ 0) ∧ 𝚺₁.DefinedFunction₁ β βDef

/-- **The deep crux-1 bridge — PROVED (lap-57, width-function route).** From a model-internal
everywhere-`icmp`-descending `seq`-graph (`hdesc`) that is **realized by a total `𝚺₁` NF branch**
(`hreal`) and **standard-width-bounded** (`hstdom`, = Rathjen Lemma 3.2 width form), the internal
Goodstein run is non-terminating. The realizer `β` gives the descent `icmp (β (n+1)) (β n) = 0`
(= `hdesc` on the graph-realizations) and the width domination `iC (β (n+1)) ≤ iF l₀ n`
(= `hstdom` at the `n+1` position); these are *exactly* the inputs of the sorry-free, axiom-free
`StdCor34F.crux1_internal_run_F` (the width-FUNCTION crux-1 run that closed the lap-57 width-code wall).
**No remaining width gap** — the old `SeqDominated`/`seqDescent_dominated`/finite-`wseq` girder is gone. -/
theorem nonterminating_of_seq_descent (seq : Semisentence ℒₒᵣ 2)
    (M : Type) [ORingStructure M] [M ⊧ₘ* 𝗜𝚺₁]
    (hreal : SeqRealized seq M)
    (hdesc : ∀ n y z : M, (M ⊧/![y, n] seq) → (M ⊧/![z, n + 1] seq) → icmp z y = 0)
    (hstdom : SeqStdBounded seq M) :
    ∃ m₀ : M, ∀ k : M, 0 < igoodstein m₀ k := by
  obtain ⟨β, βDef, hgraph, hNF, h0, hβdef⟩ := hreal
  obtain ⟨l₀, hl₀, hbound⟩ := hstdom
  have hβdesc : ∀ n, icmp (β (n + 1)) (β n) = 0 := fun n =>
    hdesc n (β n) (β (n + 1)) (hgraph n) (hgraph (n + 1))
  have hwdom : ∀ n, iC (β (n + 1)) ≤ iF l₀ n := fun n => hbound n (β (n + 1)) (hgraph (n + 1))
  exact StdCor34F.crux1_internal_run_F l₀ hl₀ hNF h0 hβdesc hβdef hwdom

/-- **Per-model crux-1 obligation.** In every model `M ⊧ₘ* 𝗜𝚺₁` in which `γ` holds AND `seq` is
standard-width-bounded (`hstdom`), the PRWO instance for `seq` holds. By contradiction: `M ⊭ prwoInstance
seq` is an internal everywhere-≺-descending `seq`-graph; `nonterminating_of_seq_descent` (using `hstdom`)
turns it into an internal non-terminating Goodstein run, which directly contradicts `M ⊧ γ`
(`∀ m, ∃ N, igoodstein m N = 0`) at `m₀`. The deep content is isolated in `seqDescent_dominated`. -/
theorem prwoInstance_models_of_goodstein (seq : Semisentence ℒₒᵣ 2)
    (M : Type) [ORingStructure M] [M ⊧ₘ* 𝗜𝚺₁] (hγ : M ⊧ₘ goodsteinSentence)
    (hreal : SeqRealized seq M)
    (hstdom : SeqStdBounded seq M) :
    M ⊧ₘ prwoInstance seq := by
  -- `γ` in `M`: every internal Goodstein run reaches `0` (the general-model analog of the ℕ-only
  -- `Bridge.goodsteinSentence_faithful` universal-closure eval).
  have hγ' : ∀ m : M, ∃ N : M, igoodstein m N = 0 := by
    have h := hγ
    simp only [goodsteinSentence, models_iff, Nat.reduceAdd, Nat.succ_eq_add_one, Fin.isValue,
      Semiformula.eval_all, Semiformula.eval_ex, Semiformula.eval_substs,
      InternalPow.igoodstein_defined.iff, Matrix.cons_val_zero, Semiterm.val_operator₀,
      Structure.numeral_eq_numeral, ORingStructure.zero_eq_zero, Fin.succ_zero_eq_one,
      Matrix.cons_val_one, Semiterm.val_bvar, Fin.Fin1.eq_one, Matrix.cons_val_fin_one,
      Fin.succ_one_eq_two, Matrix.cons_app_two] at h
    exact fun m => (h m).imp fun N h0 => h0.symm
  rw [prwoInstance_models_iff]
  intro hdesc
  obtain ⟨m₀, hm₀⟩ := nonterminating_of_seq_descent seq M hreal hdesc hstdom
  obtain ⟨N, hN⟩ := hγ' m₀
  exact absurd hN (hm₀ N).ne'

/-- **Crux 1 — Rathjen §3: `γ → PRWO(ε₀)` for a standard-width-bounded `seq`, model-theoretic route.**
From `𝗣𝗔 ⊢ γ` (soundness, `models_of_provable`) `γ` holds in every arithmetic model of `𝗣𝗔`; given the
standard-domination certificate `hstdom` (Rathjen Lemma 3.2 for `seq`), the per-model obligation
`prwoInstance_models_of_goodstein` gives `prwoInstance seq` in every such model, whence (Foundation's
arithmetic completeness `provable_of_models`) `𝗣𝗔 ⊢ prwoInstance seq`. The certificate is a hypothesis,
not a theorem: `goodstein_implies_prwo` is honest for the standard-bounded descents the headline needs
(NOT the false "for arbitrary seq" form — `Grz.F_diag_not_dominated`); it is supplied at
`seq = gentzenDescentφ` by `gentzenDescentφ_dominated`. -/
theorem goodstein_implies_prwo (seq : Semisentence ℒₒᵣ 2)
    (hreal : ∀ (M : Type) [ORingStructure M] [M ⊧ₘ* 𝗜𝚺₁], SeqRealized seq M)
    (hstdom : ∀ (M : Type) [ORingStructure M] [M ⊧ₘ* 𝗜𝚺₁], SeqStdBounded seq M) :
    𝗣𝗔 ⊢ ↑goodsteinSentence → 𝗣𝗔 ⊢ prwoInstance seq := by
  intro hγ
  apply provable_of_models 𝗣𝗔 (prwoInstance seq)
  intro M _ _
  haveI : M ⊧ₘ* 𝗜𝚺₁ := ModelsTheory.of_provably_subtheory' M 𝗜𝚺₁ 𝗣𝗔
  have hγM : M ⊧ₘ goodsteinSentence := models_of_provable inferInstance hγ
  exact prwoInstance_models_of_goodstein seq M hγM (hreal M) (hstdom M)

/-- **Rathjen Lemma 3.2 for the Gentzen descent (disclosed axiom).** `gentzenDescentφ = n ↦ ord(Rⁿd₀)`
is standard-width-bounded in every model: the complexity `iC` of its `n`-th value is `≤ iF l₀ n` for a
**standard** `l₀` determined by `ord`/`R`'s fixed primitive-recursive build tree (independent of `d₀`).
This is the concrete instance of `SeqStdBounded` the headline needs — the step keeping crux 1 on the
standard level. Disclosed pending the `ord`/`R` arithmetization (crux 2); joins the `ord`/`R`/eq-(5)
placeholders, NOT on the headline `#print axioms` path (`Statement.lean` `sorry` untouched). -/
axiom gentzenDescentφ_dominated :
    ∀ (M : Type) [ORingStructure M] [M ⊧ₘ* 𝗜𝚺₁], SeqStdBounded gentzenDescentφ M

/-- **The Gentzen descent is a total NF-valued `𝚺₁` branch (disclosed axiom).** `gentzenDescentφ`
(= `n ↦ ord(Rⁿd₀)`) is realized in every model by the total function `n ↦ ord(Rⁿd₀)`: `ord`/`R` are
primitive recursive (hence `𝚺₁`-definable internal functions) and `ord` lands in nonzero normal-form
ε₀-codes. This is the honest "primitive-recursive ε₀-valued graph" content for the Gentzen instance —
the precise totality/NF data the realizer-based crux-1 needs. Disclosed pending the `ord`/`R`
arithmetization (crux 2), alongside `gentzenDescentφ`/`gentzenDescentφ_dominated`; NOT on the headline
`#print axioms` path (`Statement.lean` `sorry` untouched). -/
axiom gentzenDescentφ_realized :
    ∀ (M : Type) [ORingStructure M] [M ⊧ₘ* 𝗜𝚺₁], SeqRealized gentzenDescentφ M

/-- **The assembly.** Crux 1 (at the Gentzen-descent instance, with its Lemma-3.2 certificate) ∘ crux 2 =
exactly the girder `Reduction.goodstein_implies_consistency`. This `wip` theorem REFINES that single
`sorry` into the two-girder chain; it is **not** promoted to `src/` until both cruxes are real (anti-fraud). -/
theorem goodstein_implies_consistency_via_gentzen :
    𝗣𝗔 ⊢ ↑goodsteinSentence → 𝗣𝗔 ⊢ ↑𝗣𝗔.consistent := fun hγ =>
  gentzen_prwo_implies_consistency
    (goodstein_implies_prwo gentzenDescentφ gentzenDescentφ_realized gentzenDescentφ_dominated hγ)

/-! ## Seam checks (machine-checked integration guards)

Integration seams are this project's historical bug source (free-X vs primrec, code↔order encoding
mismatches). The `example`s below **compile iff the two cruxes actually chain into the headline route** —
they are guards, not new content, and will keep guarding as the `sorry` bodies are discharged. -/

/-- **SEAM 1 — ONE shared `PRWO(ε₀)`.** Crux 1 *outputs* `𝗣𝗔 ⊢ prwoInstance gentzenDescentφ` and crux 2
*consumes* the same; this composition type-checks **only if both reference the identical `prwoInstance`
Lean def** (same ε₀-order `precφ`, same descent encoding). Two faithful-but-distinct PRWO statements
would fail here. -/
example (hγ : 𝗣𝗔 ⊢ ↑goodsteinSentence) : 𝗣𝗔 ⊢ ↑𝗣𝗔.consistent :=
  gentzen_prwo_implies_consistency
    (goodstein_implies_prwo gentzenDescentφ gentzenDescentφ_realized gentzenDescentφ_dominated hγ)

/-- **SEAM 2 — crux 2's `Con(𝗣𝗔)` is Foundation's `Con[𝗣𝗔]`.** The whole route ends at Gödel II
(`peano_not_proves_consistency = consistent_unprovable 𝗣𝗔`, proven about `↑𝗣𝗔.consistent`). This
`example` discharges `False` from `𝗣𝗔 ⊢ γ` by feeding the assembly's output **straight into Gödel II** —
it type-checks **only if that output is definitionally Foundation's `↑𝗣𝗔.consistent`** (not a
hand-rolled consistency lookalike). -/
example (hγ : 𝗣𝗔 ⊢ ↑goodsteinSentence) : False :=
  peano_not_proves_consistency (goodstein_implies_consistency_via_gentzen hγ)

/-- **SEAM 3 — the assembly IS the open girder, end-to-end.** Routing the assembly through the
already-axiom-clean Gödel-II hook `not_proves_of_implies_consistency` yields the headline precursor
`𝗣𝗔 ⊬ ↑goodsteinSentence`. This single type-check validates: (a) crux-1 output = crux-2 input (seam 1),
(b) crux-2 output = Foundation Con (seam 2), and (c) `goodsteinSentence`/`Con` match the `Reduction.lean`
girder `goodstein_implies_consistency : 𝗣𝗔 ⊢ ↑goodsteinSentence → 𝗣𝗔 ⊢ ↑𝗣𝗔.consistent` (identical type).
Once both crux `sorry`s are real, `goodstein_implies_consistency_via_gentzen` drops in for that girder. -/
example : 𝗣𝗔 ⊬ ↑goodsteinSentence :=
  not_proves_of_implies_consistency goodstein_implies_consistency_via_gentzen

/-! ## Discharging `gentzen_descent_of_inconsistent` — the C1–C5 arithmetization milestones (NEXT)

The lap-58 reframe moved crux 2's deep content into the **per-model semantic** axiom
`gentzen_descent_of_inconsistent` (the only object-level `𝗣𝗔`-theorem, `gentzen_reduction_internalized`,
is now PROVED via completeness). To discharge that axiom, arithmetize Gentzen's `ord`/`R` over Foundation's
`Theory.Derivation : V → Prop` (`Bootstrapping/Syntax/Proof/Basic.lean:459`), working *inside* a fixed
model `M ⊧ 𝗣𝗔`. The decomposition (Buchholz [6] `papers/buchholz-on-gentzens-first-consistency-proof.pdf`;
the descent is `n ↦ iord (iR^[n] d₀)`, `d₀` = `M`-least proof of `⊥`):

* **C1 — `iord : M → M` (ordinal assignment).** `𝚺₁`-definable function on coded derivations, by
  course-of-values recursion on the derivation structure (subderivations have smaller codes:
  `d₁_lt_cutRule` etc.). Per-rule ε₀-code assignment (axL ↦ small; cut ↦ `ω`-bumped on the cut-rank).
  Substrate idiom: the repo's `PR.Construction` recursions (`BlkRecF`/`iIter`) but on `<`-strong-recursion.
* **C2 — `iR : M → M` (Gentzen reduction).** `𝚺₁`-definable; lowers the topmost cut. `iR`-preserves-`⊥`:
  `𝗣𝗔.DerivationOf d ⊥ → 𝗣𝗔.DerivationOf (iR d) ⊥` (the M-internal `R_preserves_empty`).
* **C3 — eq-(5) in `M`: `𝗣𝗔.DerivationOf d ⊥ → icmp (iord (iR d)) (iord d) = 0`.** THE deep core
  (Gentzen's reduction strictly lowers the assigned ordinal). Finitist ⟹ should internalize to `IΣ₁`.
* **C4 — NF/nonzero: `𝗣𝗔.DerivationOf d ⊥ → isNF (iord d) ∧ iord d ≠ 0`.** (Feeds `gentzenDescentφ_realized`.)
* **C5 — `gentzenDescentφ` = the graph of `n ↦ iord (iR^[n] d₀)`.** With `d₀ := μ d. 𝗣𝗔.Proof d ⌜⊥⌝`
  (`M`-internal least ⊥-proof, exists under `¬ 𝗣𝗔.Consistent M`). Then `gentzen_descent_of_inconsistent`
  = (C2 iterate keeps `⊥`-derivations) + (C3 at each step gives `icmp` descent); `_realized` = (C4 + `iord∘iR`
  primrec ⟹ `𝚺₁` branch); `_dominated` = Rathjen Lemma 3.2 width bound on `iord`'s fixed build tree.

C1/C2 are the arithmetization engineering (large but mechanical); C3 is the genuine ordinal-analysis
girder (multi-lap, ground in Buchholz [6]). All four current crux-2 axioms collapse out of C1–C5. -/

end GoodsteinPA.GentzenCon
