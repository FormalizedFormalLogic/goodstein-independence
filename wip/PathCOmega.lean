/-
# wip/PathCOmega.lean — Path C, brick 1: the stored-ordinal ω-∀-node (lap 102→)

**Purpose (see `HANDOFF-2026-06-25-lap102.md`, `NEXT_STEPS.md` PRIORITY 1).** Probe 2 (lap 102,
`wip/InternalZomega.lean`) settled the crux-2 sub-route fork in favour of **Path C** (the ω-rule), with the
refinement that the ordinal layer must be REPLACED by **stored** ordinals (Buchholz operator-controlled
derivations), not the computed `iord` — because the induction ω-node's ordinal is a genuine limit
(`iotil_zK_iIndReduct_strictMono`) the finite-`#`-fold `iord` cannot assign.

This file begins the arithmetized stored-ordinal datatype. **Brick 1 = the ω-∀-node**, the cleanest case
(its premises are eigensubsts, ordinal-PRESERVING), where the stored ordinal can be taken to be the
existing finitary `zIall` node's own `iord` and the descent side-condition is the banked
`iord_descent_zIall`. This pins the Path-C node design in-kernel and shows the existing I∀ embedding
realizes it wholesale — the ∀-cut half of the `Zinfty.cutElimStep` analogue, on the existing engine.

NOT imported by `GoodsteinPA.lean` — a `wip/` brick; verify with `lake env lean wip/PathCOmega.lean`.

## Design (Buchholz §6 `Z*` / Towsner `ZinftyF.Deriv`, arithmetized)

An ω-∀-node is `zAllOmega s d0 a α` = `⟪s, 7, d0, a, α⟫ + 1` (tag 7): conclusion sequent `s = Γ→∀x F`,
premise generator `d0` (the eigenvariable premise deriving `Γ→F(a)`), eigenvariable `a`, **stored ordinal**
`α` (a CNF code). The premise family is `t ↦ zsubst d0 a t` (Buchholz `Z*`: `h[t] = h₀(x/t)`), materialized
on demand — never stored, so no `Fixpoint.StrongFinite` issue. **Validity** (`zAllOmegaValid`) asserts: the
premise family is uniformly valid AND every premise ordinal is `≺ α` (the stored side-condition — fully Σ₁,
NO sup/limit operation, the whole point of the stored design). A critical ∀-cut SELECTS premise `t` and the
reduction drops the ordinal below `α` for free (second validity conjunct). -/
import GoodsteinPA.Zsubst

namespace GoodsteinPA.InternalZ.PathC

open Classical
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.HierarchySymbol ISigma1 PeanoMinus
open LO.FirstOrder.Arithmetic.Bootstrapping
open GoodsteinPA.InternalONote
open GoodsteinPA.InternalZ

variable {V : Type*} [ORingStructure V] [V ⊧ₘ* 𝗜𝚺₁]

/-- **The Path-C stored-ordinal ω-∀-node** (tag 7). `s` conclusion `Γ→∀x F`, `d0` eigenvariable premise,
`a` eigenvariable, `α` the STORED ordinal. Premise-`t` = `zsubst d0 a t` (computed on demand). -/
noncomputable def zAllOmega (s d0 a α : V) : V := ⟪s, 7, d0, a, α⟫ + 1

/-- **Stored-ordinal ω-∀-node validity.** The premise family is uniformly valid (`ZDerivation` for every
closed `t`), and every premise ordinal is strictly below the stored ordinal `α`. The second conjunct is the
Buchholz operator-control side-condition — a bounded Σ₁ statement over the family, with NO ordinal-sup.
(The conclusion `_s` is carried for API/definability uniformity; the conclusion-TRACKING conjunct
`fstIdx (zsubst d0 a t) = seqSetSucc s (F t)` is the spike's `zOmegaPrem_concl`, added in a later brick
once the O3 freshness data is threaded — deferred here to keep brick 1 minimal.) -/
def zAllOmegaValid (_s d0 a α : V) : Prop :=
  (∀ t, IsSemiterm ℒₒᵣ 0 t → ZDerivation (zsubst d0 a t)) ∧
  (∀ t, IsSemiterm ℒₒᵣ 0 t → icmp (iord (zsubst d0 a t)) α = 0)

/-- **Brick 1 — a regular finitary `zIall` REALIZES the stored-ordinal ω-∀-node**, with the stored ordinal
taken to be the finitary node's own `iord`. The premise family is valid (`ZDerivation_zsubst_zIall_premise`,
freshness bound only), and each premise's ordinal `= iord d0 ≺ iord (zIall …)` (the banked
`iord_descent_zIall`, via `iord_zsubst`). So the existing I∀ embedding produces a valid Path-C ω-node for
free — the stored side-condition is exactly the banked descent, no new infrastructure. This is the ∀-cut
case of the `Zinfty.cutElimStep` ordinal drop, arithmetized on the existing engine. -/
theorem zIall_realizes_zAllOmegaValid {s a p d0 : V}
    (hZ : ZDerivation (zIall s a p d0)) (hreg : maxEigen d0 < a) :
    zAllOmegaValid s d0 a (iord (zIall s a p d0)) := by
  refine ⟨fun t ht => ZDerivation_zsubst_zIall_premise ht hZ hreg, fun t ht => ?_⟩
  rw [iord_zsubst ht.isUTerm (zDerivation_zIall_inv hZ).1 a]
  exact iord_descent_zIall s a p d0

/-- **The ω-∀-cut reduct descends below the stored ordinal — UNIFORMLY in the witness.** A critical ∀-cut
on `∀x F` with the ω-node on the R-side selects premise `zsubst d0 a t` (no new substitution); its ordinal
is `≺ α` directly from validity. This is the Path-C ∀-cut termination measure — the stored-ordinal analogue
of the spike's `iord_descent_zOmegaPrem`, now reading the side-condition off the node data rather than
recomputing. The full `cutElimStep` (all cut shapes) is brick 2 (`sorry` below). -/
theorem zAllOmega_cut_descends {s d0 a α t : V}
    (hvalid : zAllOmegaValid s d0 a α) (ht : IsSemiterm ℒₒᵣ 0 t) :
    icmp (iord (zsubst d0 a t)) α = 0 :=
  hvalid.2 t ht

/-- **The selected premise of an ω-∀-cut is a `ZDerivation` — for every witness.** The reduct-validity
half, read off the node data (no cut-elimination recursion). With `zAllOmega_cut_descends` this is the full
∀-cut invariant for Path C: validity-preserving AND ordinal-decreasing below the stored `α`. -/
theorem zAllOmega_cut_valid {s d0 a α t : V}
    (hvalid : zAllOmegaValid s d0 a α) (ht : IsSemiterm ℒₒᵣ 0 t) :
    ZDerivation (zsubst d0 a t) :=
  hvalid.1 t ht

/-! ### Brick 1, completed — conclusion-TRACKING (the deferred `zAllOmegaValid` conjunct)

The minimal `zAllOmegaValid` dropped conclusion-tracking. Here it is, with the eigenvariable side-condition
O3 supplied explicitly (the embedding's fresh-eigenvariable choice gives it). The full validity predicate
`zAllOmegaValidFull` is the complete Path-C ω-∀-node datum: premise family valid + conclusion-tracked +
ordinal-bounded by the stored `α` — and a regular finitary `zIall` realizes ALL THREE. -/

/-- **Conclusion-tracking for the ω-∀-node premise.** Premise-`t` derives exactly `Γ→F(t)`
(`= seqSetSucc s (substs1 t p)`), given the O3 eigenvariable side-condition (`a` substitution-invariant in
the matrix `p` and antecedent `Γ`) — Buchholz's condition supplied at the I∀ node, NOT re-discharged per
cut. The reduct's conclusion is COMPUTED, never threaded through a motive (the contrast with the finitary
`tpReduce`/`redZKReady` machinery). -/
theorem zAllOmega_concl {s a p d0 t : V} (hZ : ZDerivation (zIall s a p d0))
    (hpfresh : fvSubst ℒₒᵣ a t p = p)
    (hΓfresh : fvSubstSeq a t (seqAnt s) = seqAnt s)
    (ht : IsSemiterm ℒₒᵣ 0 t) :
    fstIdx (zsubst d0 a t) = seqSetSucc s (substs1 ℒₒᵣ t p) := by
  obtain ⟨hd0, _, hwff⟩ := zDerivation_zIall_inv hZ
  have hfa : IsSemiterm ℒₒᵣ 0 (^&a : V) := by simp
  rw [fstIdx_zsubst _ _ hd0]
  simp only [fvSubstSeqt, seqSetSucc, hwff.1, hwff.2.1, hΓfresh,
    fvSubst_substs1 ht hfa hwff.2.2, termFvSubst_fvar_self, hpfresh]

/-- **Full Path-C ω-∀-node validity** — the complete node datum: premise family uniformly valid AND
conclusion-tracked (`Γ→F(t)`) AND every premise ordinal `≺ α`. -/
def zAllOmegaValidFull (s p d0 a α : V) : Prop :=
  (∀ t, IsSemiterm ℒₒᵣ 0 t → ZDerivation (zsubst d0 a t)) ∧
  (∀ t, IsSemiterm ℒₒᵣ 0 t → fstIdx (zsubst d0 a t) = seqSetSucc s (substs1 ℒₒᵣ t p)) ∧
  (∀ t, IsSemiterm ℒₒᵣ 0 t → icmp (iord (zsubst d0 a t)) α = 0)

/-- **Brick 1 capstone — a regular finitary `zIall` realizes the FULL Path-C ω-∀-node** (all three
conjuncts), with stored ordinal = the node's own `iord`. The existing I∀ embedding produces a complete,
valid Path-C ω-node — validity (`ZDerivation_zsubst_zIall_premise`), conclusion (`zAllOmega_concl`), and the
stored-ordinal side-condition (`iord_descent_zIall`), all from banked lemmas + the embedding's O3 data. -/
theorem zIall_realizes_zAllOmegaValidFull {s a p d0 : V}
    (hZ : ZDerivation (zIall s a p d0)) (hreg : maxEigen d0 < a)
    (hO3p : ∀ t, IsSemiterm ℒₒᵣ 0 t → fvSubst ℒₒᵣ a t p = p)
    (hO3Γ : ∀ t, IsSemiterm ℒₒᵣ 0 t → fvSubstSeq a t (seqAnt s) = seqAnt s) :
    zAllOmegaValidFull s p d0 a (iord (zIall s a p d0)) := by
  refine ⟨fun t ht => ZDerivation_zsubst_zIall_premise ht hZ hreg,
    fun t ht => zAllOmega_concl hZ (hO3p t ht) (hO3Γ t ht) ht,
    fun t ht => ?_⟩
  rw [iord_zsubst ht.isUTerm (zDerivation_zIall_inv hZ).1 a]
  exact iord_descent_zIall s a p d0

/-! ## Brick 3 kernel — the INDUCTION ω-node's stored ordinal (the limit case)

Probe 2 (`wip/InternalZomega.lean`) showed the induction ω-node's premise ordinals strictly increase in
the unfolding depth, so its ordinal is a genuine LIMIT the computed `iord` cannot reach. The stored design
sidesteps this: assign the node a FIXED ordinal `α` that provably dominates the whole premise family, and
require `∀k, o(premise k) ≺ α` as data. Here we DISCHARGE that side-condition in-kernel — the limit is
assignable as a fixed code and dominates every finite unfolding. -/

/-- **The induction ω-node's stored ordinal** = `ω_{dg}(ω^{õ d1 + 1} # ω^{õ d0})`, where `dg = idg (zInd s
at' p d0 d1)` is the unfolding's (k-independent) degree. The õ-part is the `k→∞` limit of the depth-`k`
unfolding's õ `ω^{õ d1}·k # ω^{õ d0}` (Probe 2) — the smallest CNF code dominating the whole family. -/
noncomputable def indOmegaStoredOrd (s at' p d0 d1 : V) : V :=
  iotower (inadd (ocOadd (iadd (iotil d1) (ocOadd 0 1 0)) 1 0) (ocOadd (iotil d0) 1 0))
    (idg (zInd s at' p d0 d1))

/-- **Brick 3 kernel — the stored ordinal BOUNDS every induction premise (iord level), uniformly in `k`.**
For NF premise õs, the depth-`k` unfolding's ordinal `iord (zK s' (irk p) (iIndReductSeq d0 d1 k)) ≺
indOmegaStoredOrd …` for ALL `k > 0`. Proof: the degree is constant (`idg_zK_iIndReduct`), so the
comparison lifts (`icmp_iotower_mono`) from the õ-bound `ω^{õ d1}·k # ω^{õ d0} ≺ ω^{õ d1 + 1} # ω^{õ d0}`,
which is `inadd_right_mono` applied to the banked `icmp_term_lt_omega_succ` (`ω^β·k ≺ ω^{β+1}`, all finite
`k`). This is the Buchholz operator-control side-condition for the induction ω-node, DISCHARGED — the limit
Probe 2 showed `iord` can't compute, assigned as a fixed code that provably dominates the family.

**Carrier note (design honesty).** The premise here is the FINITARY unfolding `zK … (iIndReductSeq …)`,
which under the true ω-rule (Towsner `ZinftyF.Deriv`) would be a cut-TREE deriving `F(k)`, not a Buchholz
K-chain. So this exact node is NOT the final Path-C induction node — but the ORDINAL fact IS path-portable:
Buchholz combines cut-premise ordinals by the same `#`-natural-sum, so a cut-tree unfolding of depth `k`
carries the same õ `ω^{õd1}·k # ω^{õd0}`, dominated by the same limit. This lemma stands as (i) Probe-2
evidence that the limit is the right stored ordinal, and (ii) a reusable ordinal bound for the eventual
cut-tree node. -/
theorem iord_iIndReduct_lt_storedBound {s s' at' p d0 d1 k : V} (hk : 0 < k)
    (hd0 : isNF (iotil d0)) (hd1 : isNF (iotil d1)) :
    icmp (iord (zK s' (irk p) (iIndReductSeq d0 d1 k)))
      (indOmegaStoredOrd s at' p d0 d1) = 0 := by
  rw [indOmegaStoredOrd, iord, iotil_zK _ _ _ (iIndReductSeq_seq d0 d1 k),
      iseqNaddIdg_iIndReductSeq hk, idg_zK_iIndReduct (s := s) (s' := s') (at' := at') hk]
  exact icmp_iotower_mono
    (inadd_right_mono
      ((isNF_ocOadd _ _ _).mpr ⟨hk.ne', hd1, isNF_zero, Or.inl rfl⟩)
      ((isNF_ocOadd _ _ _).mpr ⟨(by simp), isNF_iadd_one_right hd1, isNF_zero, Or.inl rfl⟩)
      (icmp_term_lt_omega_succ (iotil d1) k)
      (ocOadd (iotil d0) 1 0) (isNF_omega_pow hd0))
    (idg (zInd s at' p d0 d1))

/-! ### Brick 3 — packaging the induction ω-node (node + validity + realization)

Mirroring brick 1 (`zAllOmega`/`zAllOmegaValid`/`zIall_realizes_zAllOmegaValid`), here is the induction
ω-node as a Path-C datatype: a node `zIndOmega` (tag 8), a validity predicate `zIndOmegaValid` (premise
family uniformly valid AND every depth-`k` unfolding's `iord ≺ the stored limit ordinal`), and the
realization theorem — a regular finitary `zInd` realizes the Path-C induction ω-node with stored ordinal =
the fixed limit `indOmegaStoredOrd`, ALL THREE conjuncts axiom-clean from banked lemmas.

The premise carrier here is the engine's finitary unfolding `iIndReductSeq d0 d1 k = ⟨d1,…,d1,d0⟩` (the
depth-`k` chain), per the carrier note on `iord_iIndReduct_lt_storedBound`: the ORDINAL fact is
path-portable (the eventual cut-tree unfolding of depth `k` carries the same õ), and the per-premise
`ZDerivation`-hood (`znth_iIndReductSeq_ZDerivation`) is a genuine, motive-free fact — exactly the
premise-family validity the stored-ordinal ω-node datum requires (no `zKValid` chain wall, since validity
is read per-premise, never as a whole-chain reduct). -/

/-- **The Path-C stored-ordinal induction ω-node** (tag 8). `s` conclusion, `at'`/`p` the induction data,
`d0`/`d1` the base/step premises, `α` the STORED limit ordinal. The premise family is the depth-`k`
unfolding `k ↦ iIndReductSeq d0 d1 k` (computed on demand). -/
noncomputable def zIndOmega (s at' p d0 d1 α : V) : V := ⟪s, 8, at', p, d0, d1, α⟫ + 1

/-- **Stored-ordinal induction ω-node validity.** Every premise of every depth-`k` unfolding (`k > 0`) is a
`ZDerivation`, and every depth-`k` unfolding's ordinal `iord (zK s' (irk p) (iIndReductSeq d0 d1 k))` is
strictly below the stored limit `α`, uniformly in `k` and the unfolding's conclusion sequent `s'`. The
second conjunct is the Buchholz operator-control side-condition for the induction node — the genuine LIMIT
Probe 2 (`iotil_zK_iIndReduct_strictMono`) showed the computed `iord` cannot reach, here discharged as a
fixed `α` that provably dominates the whole family (`iord_iIndReduct_lt_storedBound`, brick 3 kernel). -/
def zIndOmegaValid (p d0 d1 α : V) : Prop :=
  (∀ k, 0 < k → ∀ i < lh (iIndReductSeq d0 d1 k), ZDerivation (znth (iIndReductSeq d0 d1 k) i)) ∧
  (∀ s' k, 0 < k → icmp (iord (zK s' (irk p) (iIndReductSeq d0 d1 k))) α = 0)

/-- **Brick 3 capstone — a regular finitary `zInd` REALIZES the stored-ordinal induction ω-node**, with the
stored ordinal taken to be the fixed limit `indOmegaStoredOrd`. Premise-family validity is the motive-free
`znth_iIndReductSeq_ZDerivation` (each Ind-unfolding premise is `d0` or `d1`, both `ZDerivation`s by
`zDerivation_zInd_inv`); the limit-domination side-condition is exactly brick 3's
`iord_iIndReduct_lt_storedBound` (the NF hypotheses are free from `isNF_iotil_of_ZDerivation`). So the
existing native `zInd` node produces a complete, valid Path-C induction ω-node whose stored ordinal is the
genuine limit — the case the computed `iord` provably cannot assign. This is the induction analogue of
`zIall_realizes_zAllOmegaValid`. -/
theorem zInd_realizes_zIndOmegaValid {s at' p d0 d1 : V}
    (hZ : ZDerivation (zInd s at' p d0 d1)) :
    zIndOmegaValid p d0 d1 (indOmegaStoredOrd s at' p d0 d1) := by
  obtain ⟨h0, h1, _⟩ := zDerivation_zInd_inv hZ
  exact ⟨fun k _ i hi => znth_iIndReductSeq_ZDerivation h0 h1 i hi,
    fun s' k hk => iord_iIndReduct_lt_storedBound (s := s) (at' := at') hk
      (isNF_iotil_of_ZDerivation _ h0) (isNF_iotil_of_ZDerivation _ h1)⟩

/-! ### The `sord` projection — the stored-ordinal map the Path-C `red` descent reads

`brick 4`'s `stored_ord_iterate_descends` is abstracted over a stored-ordinal map `ord : V → V`. For the
Path-C nodes that map is `sord`: it reads the STORED ordinal field off an ω-node (tag 7 = ∀, tag 8 = ind),
falling back to the computed `iord` on the engine's finitary nodes. This is the projection that makes the
per-node drops (bricks 1, 3) instances of brick 4's `hdrop` hypothesis — `icmp (sord premise) (sord node)`.
The tag dispatch is read directly off the `⟪…⟫` coding, exactly as `zTag`/`iord` do. -/

@[simp] lemma zTag_zAllOmega (s d0 a α : V) : zTag (zAllOmega s d0 a α) = 7 := by
  simp [zTag, sndIdx, zAllOmega]

@[simp] lemma zTag_zIndOmega (s at' p d0 d1 α : V) : zTag (zIndOmega s at' p d0 d1 α) = 8 := by
  simp [zTag, sndIdx, zIndOmega]

/-- **The Path-C stored-ordinal projection.** On an ω-∀-node (tag 7) reads the stored `α`; on an induction
ω-node (tag 8) reads the stored limit `α`; otherwise falls back to the engine's computed `iord`. This is
the `ord` map brick 4's infinite descent iterates — the stored ordinals on ω-nodes, the computed ones
elsewhere. -/
noncomputable def sord (d : V) : V :=
  if zTag d = 7 then π₂ (π₂ (zRest d))
  else if zTag d = 8 then π₂ (π₂ (π₂ (π₂ (zRest d))))
  else if zTag d = 9 then π₁ (zRest d)
  else if zTag d = 10 then π₁ (zRest d)
  else iord d

@[simp] lemma zRest_zAllOmega (s d0 a α : V) : zRest (zAllOmega s d0 a α) = ⟪d0, a, α⟫ := by
  simp [zRest, sndIdx, zAllOmega]

@[simp] lemma zRest_zIndOmega (s at' p d0 d1 α : V) :
    zRest (zIndOmega s at' p d0 d1 α) = ⟪at', p, d0, d1, α⟫ := by
  simp [zRest, sndIdx, zIndOmega]

@[simp] lemma sord_zAllOmega (s d0 a α : V) : sord (zAllOmega s d0 a α) = α := by
  rw [sord, zTag_zAllOmega, if_pos rfl, zRest_zAllOmega]; simp

@[simp] lemma sord_zIndOmega (s at' p d0 d1 α : V) : sord (zIndOmega s at' p d0 d1 α) = α := by
  rw [sord, zTag_zIndOmega, if_neg (by simp), if_pos rfl, zRest_zIndOmega]; simp

/-! #### `sord` is `𝚺₁`-definable (the arithmetization prerequisite)

`gentzenDescentφ` arithmetizes `n ↦ sord (red^[n] d₀)`; that needs `sord` to be a `𝚺₁` internal function.
It is: a 2-way `zTag`-dispatch (`𝚺₀`) over `zRest`-projections (`𝚺₀`) with an `iord` fallback (`𝚺₁`), so
the graph is `𝚺₁`. Templated on `iordDef` (the assignment's own graph), the dispatch encoded as guarded
implications matching the `if`-cascade. -/

/-- **The `𝚺₁` graph of `sord`.** `y = sord d` iff: `tg = zTag d`, `zr = zRest d`, and the tag-guarded
value (`tg=7 ⟹ y=π₂²zr`; `tg=8 ⟹ y=π₂⁴zr`; else `y=iord d`). Deterministic disjunction (the `if`-cascade
read as guarded `∨`), templated on `tpReduceDef`'s dispatch idiom. -/
noncomputable def sordDef : 𝚺₁.Semisentence 2 := .mkSigma
  “y d. ∃ tg, !zTagDef tg d ∧ ∃ zr, !zRestDef zr d ∧
    ( (tg = 7 ∧ ∃ a, !pi₂Def a zr ∧ !pi₂Def y a)
    ∨ (tg ≠ 7 ∧ tg = 8 ∧ ∃ a, !pi₂Def a zr ∧ ∃ b, !pi₂Def b a ∧ ∃ e, !pi₂Def e b ∧ !pi₂Def y e)
    ∨ (tg ≠ 7 ∧ tg ≠ 8 ∧ tg = 9 ∧ !pi₁Def y zr)
    ∨ (tg ≠ 7 ∧ tg ≠ 8 ∧ tg ≠ 9 ∧ tg = 10 ∧ !pi₁Def y zr)
    ∨ (tg ≠ 7 ∧ tg ≠ 8 ∧ tg ≠ 9 ∧ tg ≠ 10 ∧ !iordDef y d) )”

instance sord_defined : 𝚺₁-Function₁ (sord : V → V) via sordDef := .mk fun v ↦ by
  simp [sordDef, sord, zTag_defined.iff, zRest_defined.iff, pi₁_defined.iff, pi₂_defined.iff,
    iord_defined.iff]
  by_cases h7 : zTag (v 1) = 7
  · simp [h7, numeral_eq_natCast]
  · by_cases h8 : zTag (v 1) = 8
    · simp [h7, h8, numeral_eq_natCast]
    · by_cases h9 : zTag (v 1) = 9
      · simp [h7, h8, h9, numeral_eq_natCast]
      · by_cases h10 : zTag (v 1) = 10 <;> simp [h7, h8, h9, h10, numeral_eq_natCast]

instance sord_definable : 𝚺₁-Function₁ (sord : V → V) := sord_defined.to_definable

/-- **The ω-∀-cut drop, in `sord` form (brick 1 ∘ projection).** A critical ∀-cut on the stored-ordinal
ω-∀-node `zAllOmega s d0 a α` selects premise `zsubst d0 a t`, whose computed `iord` is `≺` the node's
stored `sord = α` — i.e. `icmp (iord premise) (sord node) = 0`. This is brick 1's `zAllOmega_cut_descends`
read through `sord_zAllOmega`: the exact `hdrop`-shaped fact brick 4 consumes for the ∀-cut step. -/
theorem sord_drop_zAllOmega {s d0 a α t : V}
    (hvalid : zAllOmegaValid s d0 a α) (ht : IsSemiterm ℒₒᵣ 0 t) :
    icmp (iord (zsubst d0 a t)) (sord (zAllOmega s d0 a α)) = 0 := by
  rw [sord_zAllOmega]; exact zAllOmega_cut_descends hvalid ht

/-- **The induction-cut drop, in `sord` form (brick 3 ∘ projection).** A cut on the stored-ordinal
induction ω-node `zIndOmega s at' p d0 d1 α` selects the depth-`k` unfolding, whose computed `iord` is `≺`
the node's stored limit `sord = α` — `icmp (iord unfolding) (sord node) = 0`, uniformly in `k > 0` and the
unfolding's conclusion sequent `s'`. Brick 3's `zIndOmegaValid.2` read through `sord_zIndOmega`: the
`hdrop`-shaped fact for the induction step, the genuine LIMIT case the computed `iord` cannot itself
assign. -/
theorem sord_drop_zIndOmega {s at' p d0 d1 α s' k : V}
    (hvalid : zIndOmegaValid p d0 d1 α) (hk : 0 < k) :
    icmp (iord (zK s' (irk p) (iIndReductSeq d0 d1 k))) (sord (zIndOmega s at' p d0 d1 α)) = 0 := by
  rw [sord_zIndOmega]; exact hvalid.2 s' k hk

/-! ### Brick 2 — the Path-C cut node (where the cut-elimination ordinal drop lives)

The ω-nodes (∀, ind) are the *premise providers*; the genuinely-new content of the ω-rule calculus is the
explicit binary **cut node** (Towsner `ZinftyF.Deriv`'s `Cut` constructor / Buchholz Def 3.2's cut). It is
the only node the ⊥-orbit's `red` reduces, and the only place a chain is NOT used (premise SELECTION, lap
102 (A)). A Path-C cut node `zCutOmega s α dL dR C` (tag 9) stores: conclusion `s`, **stored ordinal** `α`,
the two premises `dL`/`dR` (deriving the cut formula `C` and its negation), and `C`. Its validity
(`zCutOmegaValid`) is Buchholz's operator-control side-condition: both premises valid AND each premise's
stored ordinal `≺ α`. The reduction `red` on a cut against an ω-∀-node SELECTS the witness premise (brick
1) and rebuilds a smaller cut whose stored ordinal — bounded by the premises' (each `≺ α`) — is `≺ α`; the
drop is read off `zCutOmegaValid` directly, NO whole-chain `zKValid` reduct (the Path-X wall). -/

/-- **The Path-C cut node** (tag 9). `s` conclusion, `α` STORED ordinal, `dL`/`dR` the two cut premises,
`C` the cut formula. The stored ordinal is the FIRST payload field (`π₁ (zRest …)`), read by `sord`. -/
noncomputable def zCutOmega (s α dL dR C : V) : V := ⟪s, 9, α, dL, dR, C⟫ + 1

@[simp] lemma zTag_zCutOmega (s α dL dR C : V) : zTag (zCutOmega s α dL dR C) = 9 := by
  simp [zTag, sndIdx, zCutOmega]

@[simp] lemma zRest_zCutOmega (s α dL dR C : V) :
    zRest (zCutOmega s α dL dR C) = ⟪α, dL, dR, C⟫ := by
  simp [zRest, sndIdx, zCutOmega]

@[simp] lemma sord_zCutOmega (s α dL dR C : V) : sord (zCutOmega s α dL dR C) = α := by
  rw [sord, zTag_zCutOmega, if_neg (by simp), if_neg (by simp), if_pos rfl, zRest_zCutOmega]; simp

/-- **Cut-node validity (Buchholz operator-control).** Both cut premises are `ZDerivation`s, and each
premise's STORED ordinal (`sord`) is strictly below the cut's stored `α`. The second/third conjuncts are the
operator-control side-condition that makes cut-elimination DROP the ordinal: the reduct cut, rebuilt from
these premises, inherits a stored ordinal bounded by them, hence `≺ α`. Σ₁ (no ordinal-sup), read off the
node data — the whole point of the stored design. -/
def zCutOmegaValid (α dL dR : V) : Prop :=
  ZDerivation dL ∧ ZDerivation dR ∧ icmp (sord dL) α = 0 ∧ icmp (sord dR) α = 0

/-- **The cut-reduction left-premise drop, in `sord` form.** A cut-elimination step on `zCutOmega s α dL dR
C` reduces toward `dL` (the cut-formula side); `dL`'s stored ordinal is `≺` the cut's stored `sord = α` —
the `hdrop`-shaped fact for the cut step, read straight off `zCutOmegaValid`. (Brick 1's ∀-witness selection
supplies a premise of exactly this form when `dL` is a `zAllOmega`.) -/
theorem sord_drop_zCutOmega_left {s α dL dR C : V} (hvalid : zCutOmegaValid α dL dR) :
    icmp (sord dL) (sord (zCutOmega s α dL dR C)) = 0 := by
  rw [sord_zCutOmega]; exact hvalid.2.2.1

/-- **The cut-reduction right-premise drop, in `sord` form.** Symmetric to `sord_drop_zCutOmega_left`:
`dR`'s stored ordinal is `≺` the cut's stored `sord = α`. Together they bound the reduct cut's stored
ordinal below `α` — the strict descent the ⊥-orbit iteration needs. -/
theorem sord_drop_zCutOmega_right {s α dL dR C : V} (hvalid : zCutOmegaValid α dL dR) :
    icmp (sord dR) (sord (zCutOmega s α dL dR C)) = 0 := by
  rw [sord_zCutOmega]; exact hvalid.2.2.2

/-! ### Brick 2 — the ∀-cut reduction step (the cut-elimination ordinal DROP)

The heart of Path C: the single `red` step on a cut whose cut-formula is `∀x F` and whose `dL` is the
ω-∀-node. By premise SELECTION (lap 102 (A)) the reduct is a SMALLER cut on `F(t)` between the selected
witness premise `zsubst d0 a t` (brick 1) and the `∃`-side's witness sub-derivation `dR_t`. Its stored
ordinal is the ε₀-max of the two reduced premises' stored ordinals — and that max is STRICTLY `≺ α`
because BOTH premises are (`zAllOmega_cut_descends` gives the left, the cut's operator-control gives the
right). This is the strict per-step ordinal descent that, iterated on the ⊥-orbit, contradicts PRWO(ε₀).

The max trick is the whole point: in ANY linear order, `max(a,b) ≺ α` whenever `a ≺ α ∧ b ≺ α` — no
additive-principality of `α` needed (unlike the natural sum `#`), so the reduct ordinal drops below `α`
for an arbitrary stored `α`. -/

/-- **Unbounded `≺`-transitivity** (wrapper over the bounded `icmp_trans`, with `a+b+c` as the common
bound). `a ≺ b → b ≺ c → a ≺ c`. -/
theorem icmp_trans' {a b c : V} (h1 : icmp a b = 0) (h2 : icmp b c = 0) : icmp a c = 0 :=
  icmp_trans (a + b + c) a (le_trans (le_self_add) (le_self_add)) b
    (le_trans (le_add_self) (le_self_add)) c le_add_self h1 h2

/-- **ε₀-code max** via `icmp` (`icmp a b = 0 ⟺ a ≺ b`): `imax a b = b` if `a ≺ b`, else `a`. -/
noncomputable def imax (a b : V) : V := if icmp a b = 0 then b else a

/-- **Max of two ordinals each `≺ α` is `≺ α`** — the linear-order fact (no additive-principality of `α`).
`imax a b ∈ {a, b}`, and both are `≺ α`, so `imax a b ≺ α`. This is what lets the cut-reduct's stored
ordinal (the max of its premises') drop strictly below the cut's `α` for an ARBITRARY stored `α`. -/
theorem icmp_imax_lt {a b α : V} (ha : icmp a α = 0) (hb : icmp b α = 0) :
    icmp (imax a b) α = 0 := by
  unfold imax; split <;> assumption

/-- **`imax` is `𝚺₁`-definable** (needed for `red`'s definability). Two-way dispatch on `icmp a b = 0`. -/
noncomputable def imaxDef : 𝚺₁.Semisentence 3 := .mkSigma
  “y a b. ∃ c, !icmpDef c a b ∧ ((c = 0 ∧ y = b) ∨ (c ≠ 0 ∧ y = a))”

instance imax_defined : 𝚺₁-Function₂ (imax : V → V → V) via imaxDef := .mk fun v ↦ by
  simp [imaxDef, imax, icmp_defined.iff]
  by_cases h : icmp (v 1) (v 2) = 0 <;> simp [h]

instance imax_definable : 𝚺₁-Function₂ (imax : V → V → V) := imax_defined.to_definable

/-- **Generic cut-reduct drop — the UNIFORM ordinal descent for every cut-formula shape.** ANY rebuilt cut
`zCutOmega s (imax (sord dL) (sord dR)) dL dR C` whose two reduced premises each have `sord ≺ α` has its own
stored `sord ≺ α`. So every cut case of `red` (∀-witness selection, ∧/∨-projection, atom) drops the ordinal
by the SAME `icmp_imax_lt` argument — the reduct premises are immediate sub-derivations (smaller `sord`),
and the rebuilt cut stores their max. `sord_redCutAll_lt` is the `∀` instance; the other shapes instantiate
this verbatim once their premise-extraction is defined. -/
theorem sord_zCutOmega_imax_lt {s dL dR C α : V}
    (hL : icmp (sord dL) α = 0) (hR : icmp (sord dR) α = 0) :
    icmp (sord (zCutOmega s (imax (sord dL) (sord dR)) dL dR C)) α = 0 := by
  rw [sord_zCutOmega]; exact icmp_imax_lt hL hR

/-- **The ∀-cut reduct** (Path C `red`, the `cut`-vs-`∀x F` case). Selects the witness premise `zsubst d0 a
t` (brick 1) and the `∃`-side witness sub-derivation `dR_t`, rebuilding a smaller cut on `Cnew = F(t)` whose
stored ordinal is the ε₀-max of the two reduced premises' stored ordinals. NO chain, NO `zKValid` reduct —
pure premise selection. -/
noncomputable def redCutAll (s d0 a t Cnew dR_t : V) : V :=
  zCutOmega s (imax (iord (zsubst d0 a t)) (sord dR_t)) (zsubst d0 a t) dR_t Cnew

/-- **Brick 2 — the ∀-cut reduction STRICTLY drops the stored ordinal.** From the ω-∀-node's validity
(brick 1, giving `iord (zsubst d0 a t) ≺ α`) and the `∃`-side premise's operator-control bound (`sord dR_t
≺ α`, supplied by the original cut's `zCutOmegaValid`), the reduct cut's stored ordinal `sord (redCutAll …)
= imax(…) ≺ α`. This is the genuine per-step cut-elimination ordinal descent — `red` on a `cut`-vs-`∀`
node, axiom-clean, with NO appeal to chain validity (the Path-X wall). Combined with brick 3 (induction)
this discharges the ⊥-orbit `hdrop` brick 4 iterates into the infinite ε₀-descent. -/
theorem sord_redCutAll_lt {s d0 a α t Cnew dR_t : V}
    (hAll : zAllOmegaValid s d0 a α) (ht : IsSemiterm ℒₒᵣ 0 t)
    (hR : icmp (sord dR_t) α = 0) :
    icmp (sord (redCutAll s d0 a t Cnew dR_t)) α = 0 := by
  rw [redCutAll, sord_zCutOmega]
  exact icmp_imax_lt (zAllOmega_cut_descends hAll ht) hR

/-! ### The ∃-introduction node + the self-contained ∀/∃-cut reduction

The ∀-cut's right premise is the `∃x ¬F`-side. In the ω-rule calculus `∃` is a finitary INTRODUCTION:
`zExOmega s α C t d` (tag 10) derives `Γ → ∃x ¬F` from a single premise `d ⊢ Γ → ¬F(t)` with stored witness
`t` and stored ordinal `α`. The cut reduction reads `t` and `d` OFF this node (no guesswork), selects the
∀-node's premise at the SAME `t`, and rebuilds the smaller cut — fully self-contained, the genuine
Tait/Buchholz ∀/∃ cut reduction. -/

/-- **The Path-C ∃-introduction node** (tag 10). `s` conclusion `Γ→∃x¬F`, `α` stored ordinal, `C` the matrix
`¬F`, `t` the witness, `d` the premise (`⊢ Γ→¬F(t)`). Stored ordinal is the FIRST payload field. -/
noncomputable def zExOmega (s α C t d : V) : V := ⟪s, 10, α, C, t, d⟫ + 1

@[simp] lemma zTag_zExOmega (s α C t d : V) : zTag (zExOmega s α C t d) = 10 := by
  simp [zTag, sndIdx, zExOmega]

@[simp] lemma zRest_zExOmega (s α C t d : V) : zRest (zExOmega s α C t d) = ⟪α, C, t, d⟫ := by
  simp [zRest, sndIdx, zExOmega]

@[simp] lemma sord_zExOmega (s α C t d : V) : sord (zExOmega s α C t d) = α := by
  rw [sord, zTag_zExOmega, if_neg (by simp), if_neg (by simp), if_neg (by simp), if_pos rfl,
    zRest_zExOmega]; simp

/-- The stored witness term of an ∃-node. -/
noncomputable def zExTerm (d : V) : V := π₁ (π₂ (π₂ (zRest d)))
/-- The witness premise of an ∃-node (`⊢ Γ→¬F(t)`). -/
noncomputable def zExPrem (d : V) : V := π₂ (π₂ (π₂ (zRest d)))

@[simp] lemma zExTerm_zExOmega (s α C t d : V) : zExTerm (zExOmega s α C t d) = t := by
  simp [zExTerm, zRest_zExOmega]
@[simp] lemma zExPrem_zExOmega (s α C t d : V) : zExPrem (zExOmega s α C t d) = d := by
  simp [zExPrem, zRest_zExOmega]

/-- **∃-node validity (operator-control).** The witness premise is a `ZDerivation` with stored ordinal
`≺ α` — the same operator-control shape as the cut/ω-nodes. -/
def zExOmegaValid (α d : V) : Prop := ZDerivation d ∧ icmp (sord d) α = 0

/-- **The self-contained ∀/∃-cut reduct.** Given the cut formula `∀x F` with the ω-∀-node `zAllOmega s d0 a
αAll` on the left and the ∃-node `dR = zExOmega …` on the right, the reduct reads the witness `t = zExTerm
dR`, selects the ∀-node's premise `zsubst d0 a t` (brick 1), takes the ∃-node's premise `zExPrem dR`
(`⊢ Γ→¬F(t)`), and rebuilds the smaller cut on `Cnew = F(t)` storing the ε₀-max of the two. NO chain, NO
externally-supplied premise — the witness/premise come from the node data. -/
noncomputable def redAllEx (s d0 a Cnew dR : V) : V :=
  zCutOmega s (imax (iord (zsubst d0 a (zExTerm dR))) (sord (zExPrem dR)))
    (zsubst d0 a (zExTerm dR)) (zExPrem dR) Cnew

/-- **The self-contained ∀/∃-cut reduction STRICTLY drops the stored ordinal.** From the ω-∀-node's
validity (brick 1: the selected premise `iord ≺ αAll`, evaluated at the witness `t = zExTerm dR`) and the
∃-node's operator-control (`sord (zExPrem dR) ≺ α`), the reduct's stored ordinal `≺ α`. The genuine,
self-contained per-step cut-elimination descent — `t` and the right premise read off the ∃-node, no
external parameter. (For the SAME `α`, take `αAll = α`: the cut's `zCutOmegaValid` gives `sord dL ≺ α`, and
brick 1 lowers the selected premise further.) -/
theorem sord_redAllEx_lt {s d0 a αAll Cnew dR α : V}
    (hAll : zAllOmegaValid s d0 a αAll) (ht : IsSemiterm ℒₒᵣ 0 (zExTerm dR))
    (hAlllt : icmp αAll α = 0)
    (hEx : zExOmegaValid α (zExPrem dR)) :
    icmp (sord (redAllEx s d0 a Cnew dR)) α = 0 := by
  rw [redAllEx, sord_zCutOmega]
  -- selected ∀-premise: iord ≺ αAll (brick 1) ≺ α, so ≺ α (transitivity); ∃-premise ≺ α (hEx)
  exact icmp_imax_lt (icmp_trans' (zAllOmega_cut_descends hAll ht) hAlllt) hEx.2

/-- **The induction/∃-cut reduct.** The cut formula is the induction conclusion `∀x F` (derived by the
induction ω-node `zIndOmega`) cut against `∃x ¬F` (the ∃-node `dR`). The reduct SELECTS the depth-`t`
induction unfolding `zK s' (irk p) (iIndReductSeq d0 d1 t)` (`t = zExTerm dR`, deriving `F(t)`; brick 3) and
the ∃-premise `zExPrem dR` (`⊢ ¬F(t)`), rebuilding the smaller cut on `Cnew = F(t)` storing the ε₀-max. The
unfolding conclusion `s'` is a parameter (the ordinal bound brick 3 gives is `s'`-independent). -/
noncomputable def redIndEx (s s' at' p d0 d1 Cnew dR : V) : V :=
  zCutOmega s (imax (iord (zK s' (irk p) (iIndReductSeq d0 d1 (zExTerm dR)))) (sord (zExPrem dR)))
    (zK s' (irk p) (iIndReductSeq d0 d1 (zExTerm dR))) (zExPrem dR) Cnew

/-- **The induction/∃-cut reduction STRICTLY drops the stored ordinal.** From brick 3
(`iord_iIndReduct_lt_storedBound`: the depth-`t` unfolding's `iord ≺ indOmegaStoredOrd`, for `t > 0` and NF
premises) and the cut's operator-control on the induction node (`indOmegaStoredOrd ≺ α`), the selected
unfolding's `iord ≺ α` (transitivity); the ∃-premise's `sord ≺ α` (`hEx`); so the reduct's stored ordinal
`≺ α`. The induction analogue of `sord_redAllEx_lt` — the genuine LIMIT case the computed `iord` could not
itself assign, here discharged via the stored limit. -/
theorem sord_redIndEx_lt {s s' at' p d0 d1 Cnew dR α : V}
    (hk : 0 < zExTerm dR) (hd0 : isNF (iotil d0)) (hd1 : isNF (iotil d1))
    (hIndlt : icmp (indOmegaStoredOrd s at' p d0 d1) α = 0)
    (hEx : zExOmegaValid α (zExPrem dR)) :
    icmp (sord (redIndEx s s' at' p d0 d1 Cnew dR)) α = 0 := by
  rw [redIndEx, sord_zCutOmega]
  exact icmp_imax_lt
    (icmp_trans' (iord_iIndReduct_lt_storedBound hk hd0 hd1) hIndlt) hEx.2

/-! ### Node projections + the cut-orbit `red` (first dispatch case)

The total `red` reduces the topmost cut by reading its premises' node types off the data. Here are the
projections + the FIRST dispatch case (cut-vs-`∀/∃`), with the orbit drop on a concretely-built node so the
projections compute by `simp`. The other cases (induction-cut, `∧`/`∨`) extend the dispatch identically. -/

/-- The ∀-node's base premise `d0`. -/
noncomputable def zAllD0 (d : V) : V := π₁ (zRest d)
/-- The ∀-node's eigenvariable. -/
noncomputable def zAllEig (d : V) : V := π₁ (π₂ (zRest d))
/-- A cut node's left premise. -/
noncomputable def zCutL (d : V) : V := π₁ (π₂ (zRest d))
/-- A cut node's right premise. -/
noncomputable def zCutR (d : V) : V := π₁ (π₂ (π₂ (zRest d)))
/-- A cut node's cut formula. -/
noncomputable def zCutC (d : V) : V := π₂ (π₂ (π₂ (zRest d)))

@[simp] lemma fstIdx_zCutOmega (s α dL dR C : V) : fstIdx (zCutOmega s α dL dR C) = s := by
  simp [fstIdx, zCutOmega]
@[simp] lemma zAllD0_zAllOmega (s d0 a α : V) : zAllD0 (zAllOmega s d0 a α) = d0 := by
  simp [zAllD0, zRest_zAllOmega]
@[simp] lemma zAllEig_zAllOmega (s d0 a α : V) : zAllEig (zAllOmega s d0 a α) = a := by
  simp [zAllEig, zRest_zAllOmega]
@[simp] lemma zCutL_zCutOmega (s α dL dR C : V) : zCutL (zCutOmega s α dL dR C) = dL := by
  simp [zCutL, zRest_zCutOmega]
@[simp] lemma zCutR_zCutOmega (s α dL dR C : V) : zCutR (zCutOmega s α dL dR C) = dR := by
  simp [zCutR, zRest_zCutOmega]
@[simp] lemma zCutC_zCutOmega (s α dL dR C : V) : zCutC (zCutOmega s α dL dR C) = C := by
  simp [zCutC, zRest_zCutOmega]

/-- **The cut-orbit `red` (first dispatch case).** On a cut node (tag 9) whose left premise is an ω-∀-node
(tag 7) and right premise is an ∃-node (tag 10), reduce by the self-contained `redAllEx` (witness selection).
Other shapes: identity for now (the induction-cut and `∧`/`∨` cases extend this dispatch). -/
noncomputable def red (w : V) : V :=
  if zTag w = 9 ∧ zTag (zCutL w) = 7 ∧ zTag (zCutR w) = 10 then
    redAllEx (fstIdx w) (zAllD0 (zCutL w)) (zAllEig (zCutL w)) (zCutC w) (zCutR w)
  else w

/-- **The cut-orbit `red` STRICTLY drops the stored ordinal on a ∀/∃-cut.** On a concretely-built cut node
`zCutOmega s α (zAllOmega …) (zExOmega …) C`, `red` fires the ∀/∃ dispatch and the stored ordinal drops
below `α = sord w` — the per-step `hdrop` brick 4 iterates, on the actual node `red` produces. The genuine
cut-elimination descent step, end to end (dispatch + selection + ordinal drop), axiom-clean. -/
theorem sord_red_lt_AllEx {s s' d0 a αAll α C sE CE tE dE : V}
    (hAll : zAllOmegaValid s' d0 a αAll) (ht : IsSemiterm ℒₒᵣ 0 tE)
    (hAlllt : icmp αAll α = 0) (hEx : zExOmegaValid α dE) :
    icmp (sord (red (zCutOmega s α (zAllOmega s' d0 a αAll) (zExOmega sE α CE tE dE) C)))
      (sord (zCutOmega s α (zAllOmega s' d0 a αAll) (zExOmega sE α CE tE dE) C)) = 0 := by
  have hfire : red (zCutOmega s α (zAllOmega s' d0 a αAll) (zExOmega sE α CE tE dE) C)
      = redAllEx s d0 a C (zExOmega sE α CE tE dE) := by
    rw [red, if_pos (by simp)]; simp
  rw [hfire, sord_zCutOmega]
  refine sord_redAllEx_lt hAll ?_ hAlllt ?_
  · simpa using ht
  · simpa using hEx

/-! ## Brick 4 skeleton — the stored-ordinal infinite descent (path-portable)

**Endgame design (clarified lap 102).** Two distinct cut-elimination reductions exist; Path C uses the
RIGHT one:
- *Towsner/Zinfty `cutElimStep`* (rank `c+1→c`, ordinal `α↦ω^α`) — used for the META proof (`Zinfty.lean`),
  iterated `c` times by `cutElim`. The ordinal INCREASES per step; this gives "terminates at cut-free", not
  a single-step drop. NOT the Path-C reduction.
- *Buchholz `red`* (Def 3.2, operator-controlled) — a single reduction step that STRICTLY DROPS the
  (stored) ordinal while preserving the conclusion. This is the repo's finitary `red`, and the right Path-C
  reduction: iterating it on an ∅→⊥ derivation gives an infinite ε₀-descent (the ∅→⊥ sequent has no
  cut-free proof, so `red` never terminates), which crux-1's PRWO(ε₀) forbids. The bricks above ARE the
  per-node drops of this `red`: brick 1 (∀-cut selects premise, ord ≺ stored αR), brick 3 (induction node,
  ord bounded by the stored limit). The descent skeleton below packages the iteration, exactly mirroring
  `Crux2Blueprint.iord_red_iterate_descends` but on STORED ordinals (path-portable, no `iord` engine). -/

/-- **Brick 4 skeleton — iterated stored-ordinal descent.** A per-step strict drop of the stored ordinal
gives an infinite `≺`-descent `n ↦ ord (red^[n] z)`. The Path-C analogue of
`Crux2Blueprint.iord_red_iterate_descends`, abstracted over the stored-ordinal map `ord` and the
single-step reduction `step` — so it consumes exactly the per-node drops (bricks 1, 3) and feeds crux-1's
PRWO(ε₀)/`gentzen_descent_of_inconsistent`. Path-portable: no dependence on the computed `iord` engine. -/
theorem stored_ord_iterate_descends {step ord : V → V} {z : V}
    (hdrop : ∀ w, icmp (ord (step w)) (ord w) = 0) (n : ℕ) :
    icmp (ord (step^[n+1] z)) (ord (step^[n] z)) = 0 := by
  rw [Function.iterate_succ_apply']; exact hdrop _

/-- **Brick 4, the REALISTIC form — `red`-orbit infinite descent relative to an invariant `P`.** The
abstract `stored_ord_iterate_descends` assumes the drop holds at EVERY `w`; but the cut-elimination drop
only holds on VALID reducible nodes (`sord_red_lt_AllEx` needs the ∀/∃-cut validity). So the iteration must
carry an orbit invariant `P` ("valid reducible ⊥-derivation"): if `P` is closed under `red` (`hinv` — the
reduct is again valid+reducible, the structural cut-elimination soundness) and `red` drops `sord` on `P`
(`hdrop` — bricks above), then `n ↦ sord (red^[n] z)` strictly `≺`-descends forever. This is the EXACT
shape the endgame needs (`Crux2Blueprint.iord_red_iterate_descends` analogue): `P` carries the validity
licensing each step's drop, the descent then contradicts crux-1's PRWO(ε₀). Reduces crux-2 to: define `P`
+ prove `hinv` (orbit closure) + `hdrop` (per-step drop, ✔ for the ∀/∃ case via `sord_red_lt_AllEx`). -/
theorem red_iterate_descends {P : V → Prop}
    (hinv : ∀ w, P w → P (red w))
    (hdrop : ∀ w, P w → icmp (sord (red w)) (sord w) = 0)
    {z : V} (hz : P z) (n : ℕ) :
    icmp (sord (red^[n+1] z)) (sord (red^[n] z)) = 0 := by
  have hmem : ∀ m : ℕ, P (red^[m] z) := by
    intro m
    induction m with
    | zero => simpa using hz
    | succ k ih => rw [Function.iterate_succ_apply']; exact hinv _ ih
  rw [Function.iterate_succ_apply']; exact hdrop _ (hmem n)

/-! ### ⚠ CLOSURE-FAILURE CERTIFICATE (lap 104) — the naive dispatch-shaped `P` is NOT `red`-closed

`red_iterate_descends` is a TRUE conditional: IF the orbit invariant `P` is `red`-closed (`hinv`) and
`red` drops `sord` on `P` (`hdrop`), the descent follows. The HANDOFF framed `hinv` as "tractable via
premise selection". **That framing is wrong, and here is the in-kernel proof.**

The dispatch (`red`, above) fires only on a cut node whose left premise is *literally* a stored ω-∀-node
(`zTag (zCutL w) = 7`) and whose right is an ∃-node (`zTag (zCutR w) = 10`). But the reduct `redAllEx`
selects the ω-∀-node's BASE premise after substitution, `zsubst d0 a t`, as its new left premise. By
`zTag_zsubst`, a substituted genuine `ZDerivation` keeps `d0`'s tag, which is one of the seven engine tags
`0..6` (`zTag_ne_seven_of_ZDerivation`) — **never** the stored-ω-∀ tag `7`. So `red` is the IDENTITY on
the reduct (`red_redAllEx_eq`): the orbit STALLS after a single step, `sord` is constant from step 1, and
no infinite descent exists. Hence any `P` requiring the (7,10) dispatch shape is provably not `red`-closed
(`naive_dispatch_P_not_red_closed`).

**Consequence (the corrected next brick).** The reduct's premises `zsubst d0 a t` / `zExPrem dR` derive
`Γ→F(t)` / `Γ→¬F(t)` but need NOT be principal nodes for the smaller cut on `F(t)`. To keep the orbit
reducible, `red` must RE-PRINCIPALIZE them — i.e. it must apply Schütte/Tait INVERSION operators
(`redInv∀`, `redInv∧`, …: from any Path-C derivation of `Γ, F` extract a derivation of the immediate
subformula instance, with stored ordinal `≼`). Inversion is a recursion over the derivation, hence needs
the genuine Path-C derivation predicate (the datatype, NEXT_STEPS step 1). This certificate redirects the
endgame: `hinv` is the Hauptsatz (inversion + reduction), not naive selection. -/

/-- Every genuine engine `ZDerivation` carries one of the seven engine tags `0..6` — in particular,
NEVER the stored-ω-∀ tag `7`. (The Path-C ω-nodes `zAllOmega`/`zIndOmega`/`zCutOmega`/`zExOmega`, tags
`7..10`, are a parallel layer the engine predicate does not recognize.) -/
theorem zTag_ne_seven_of_ZDerivation {d : V} (hd : ZDerivation d) : zTag d ≠ 7 := by
  rcases zDerivation_iff.mp hd with ⟨s, rfl, _⟩ | ⟨s, e, p, d0, rfl, _, _, _⟩ |
    ⟨s, p, d0, rfl, _, _, _⟩ | ⟨s, at', p, d0, d1, rfl, _, _, _⟩ |
    ⟨s, r, ds, rfl, _, _, _⟩ | ⟨s, p, k, rfl, _, _⟩ | ⟨s, p, rfl, _, _⟩ <;> simp

/-- **The ∀/∃-cut reduct is a `red`-FIXPOINT.** Given the ∀-node base premise `d0` is a genuine
`ZDerivation`, `redAllEx`'s left premise `zsubst d0 a t` has tag `= zTag d0 ≠ 7`, so the `red` dispatch
condition fails and `red` is the identity. The orbit cannot fire a second time. -/
theorem red_redAllEx_eq {s d0 a Cnew dR : V} (hd0 : ZDerivation d0) :
    red (redAllEx s d0 a Cnew dR) = redAllEx s d0 a Cnew dR := by
  rw [red, if_neg]
  rintro ⟨_, hL, _⟩
  rw [redAllEx, zCutL_zCutOmega, zTag_zsubst hd0] at hL
  exact zTag_ne_seven_of_ZDerivation hd0 hL

/-- A `red`-fixpoint stays fixed under iteration. -/
theorem iterate_red_fixed {w : V} (h : red w = w) : ∀ n : ℕ, red^[n] w = w
  | 0 => rfl
  | n + 1 => by rw [Function.iterate_succ_apply', iterate_red_fixed h n, h]

/-- **The ∀/∃-cut orbit STALLS after one step** (the in-kernel obstruction). On a concrete ∀/∃-cut node
`w` with a genuine base premise `d0`, `red w = redAllEx …` fires once, but every further `red` is the
identity. So `sord (red^[n+1] w) = sord (red^[n] w)` for ALL `n ≥ 1` — the stored ordinal is eventually
CONSTANT, never an infinite `≺`-descent. This is why the naive dispatch-shaped invariant fails the
infinite-descent endgame: the reduct's premises are not re-principalized (no inversion). -/
theorem sord_red_iterate_stalls_AllEx {s s' d0 a αAll α C sE CE tE dE : V}
    (hd0 : ZDerivation d0) (n : ℕ) :
    sord (red^[n+2] (zCutOmega s α (zAllOmega s' d0 a αAll) (zExOmega sE α CE tE dE) C))
      = sord (red^[n+1] (zCutOmega s α (zAllOmega s' d0 a αAll) (zExOmega sE α CE tE dE) C)) := by
  set w := zCutOmega s α (zAllOmega s' d0 a αAll) (zExOmega sE α CE tE dE) C with hw
  have hfire : red w = redAllEx s d0 a C (zExOmega sE α CE tE dE) := by
    rw [hw, red, if_pos (by simp)]; simp
  have hfix : red (red w) = red w := by rw [hfire]; exact red_redAllEx_eq hd0
  -- every iterate from step 1 on equals the single-fired form `red w`
  have key : ∀ m : ℕ, red^[m + 1] w = red w := by
    intro m
    induction m with
    | zero => rw [Function.iterate_one]
    | succ j ih => rw [Function.iterate_succ_apply', ih, hfix]
  show sord (red^[(n + 1) + 1] w) = sord (red^[n + 1] w)
  rw [key (n + 1), key n]

/-- **The naive dispatch-shaped `P` is NOT `red`-closed.** Any invariant `P` that (i) holds on the
concrete ∀/∃-cut node and (ii) implies the `red`-dispatch shape `zTag w = 9 ∧ zTag (zCutL w) = 7 ∧
zTag (zCutR w) = 10` fails `hinv`: `red` of that node is `redAllEx …`, whose left premise has tag `≠ 7`,
so `P (red w)` cannot hold. Concretely: `hinv` (the `red_iterate_descends` hypothesis) is unsatisfiable
for such `P`. The genuine `P` must be a derivation predicate whose `red` re-principalizes via inversion. -/
theorem naive_dispatch_P_not_red_closed {s s' d0 a αAll α C sE CE tE dE : V}
    (hd0 : ZDerivation d0)
    (Pshape : V → Prop)
    (hshape : ∀ w, Pshape w → zTag w = 9 ∧ zTag (zCutL w) = 7 ∧ zTag (zCutR w) = 10) :
    ¬ Pshape (red (zCutOmega s α (zAllOmega s' d0 a αAll) (zExOmega sE α CE tE dE) C)) := by
  intro hP
  have hfire : red (zCutOmega s α (zAllOmega s' d0 a αAll) (zExOmega sE α CE tE dE) C)
      = redAllEx s d0 a C (zExOmega sE α CE tE dE) := by
    rw [red, if_pos (by simp)]; simp
  obtain ⟨_, hL, _⟩ := hshape _ hP
  rw [hfire, redAllEx, zCutL_zCutOmega, zTag_zsubst hd0] at hL
  exact zTag_ne_seven_of_ZDerivation hd0 hL

/-! ### Brick 5 (lap 104→) — the Path-C derivation predicate `ZcOK` as a clean inductive `Prop`

The corrected `hinv` needs a genuine derivation predicate to recurse over (inversion). Rather than pay the
full Σ₁-`Fixpoint` arithmetization first (heavy — `zconstruction` template), we PROTOTYPE the cut-elimination
math on a clean Lean `inductive ZcOK : V → Prop`: the ω-∀ constructor is INFINITARY (a premise family
indexed by closed terms `t`), strictly positive (`ZcOK (zsubst d0 a t)` — no `ZcOK` under the index), so
Lean accepts it (W-type style). `leaf` wraps an engine `ZDerivation` (the embedding's image / the cut-free
sub-derivations). Each node carries Buchholz operator-control (premise `sord ≺` node's stored `α`). This
develops + machine-checks the inversion/`red`/`hinv` MATH; the Σ₁ port (so the descent is V-internal for
PRWO) is the deferred final brick. -/
inductive ZcOK : V → Prop where
  | leaf {d : V} (hd : ZDerivation d) : ZcOK d
  | omegaAll {s d0 a α : V}
      (hprem : ∀ t, IsSemiterm ℒₒᵣ 0 t → ZcOK (zsubst d0 a t))
      (hdesc : ∀ t, IsSemiterm ℒₒᵣ 0 t → icmp (iord (zsubst d0 a t)) α = 0) :
      ZcOK (zAllOmega s d0 a α)
  | ex {s α C t d : V} (hprem : ZcOK d) (hdesc : icmp (sord d) α = 0) :
      ZcOK (zExOmega s α C t d)
  | cut {s α dL dR C : V} (hL : ZcOK dL) (hR : ZcOK dR)
      (hLdesc : icmp (sord dL) α = 0) (hRdesc : icmp (sord dR) α = 0) :
      ZcOK (zCutOmega s α dL dR C)

/-- A `ZDerivation` never carries the cut tag `9` (engine tags are `0..6`; cf. `zTag_ne_seven`). -/
theorem zTag_ne_nine_of_ZDerivation {d : V} (hd : ZDerivation d) : zTag d ≠ 9 := by
  rcases zDerivation_iff.mp hd with ⟨s, rfl, _⟩ | ⟨s, e, p, d0, rfl, _, _, _⟩ |
    ⟨s, p, d0, rfl, _, _, _⟩ | ⟨s, at', p, d0, d1, rfl, _, _, _⟩ |
    ⟨s, r, ds, rfl, _, _, _⟩ | ⟨s, p, k, rfl, _, _⟩ | ⟨s, p, rfl, _, _⟩ <;> simp

/-- A `ZDerivation` never carries the ∃-node tag `10`. -/
theorem zTag_ne_ten_of_ZDerivation {d : V} (hd : ZDerivation d) : zTag d ≠ 10 := by
  rcases zDerivation_iff.mp hd with ⟨s, rfl, _⟩ | ⟨s, e, p, d0, rfl, _, _, _⟩ |
    ⟨s, p, d0, rfl, _, _, _⟩ | ⟨s, at', p, d0, d1, rfl, _, _, _⟩ |
    ⟨s, r, ds, rfl, _, _, _⟩ | ⟨s, p, k, rfl, _, _⟩ | ⟨s, p, rfl, _, _⟩ <;> simp

/-- A `ZDerivation` never carries the induction ω-node tag `8`. -/
theorem zTag_ne_eight_of_ZDerivation {d : V} (hd : ZDerivation d) : zTag d ≠ 8 := by
  rcases zDerivation_iff.mp hd with ⟨s, rfl, _⟩ | ⟨s, e, p, d0, rfl, _, _, _⟩ |
    ⟨s, p, d0, rfl, _, _, _⟩ | ⟨s, at', p, d0, d1, rfl, _, _, _⟩ |
    ⟨s, r, ds, rfl, _, _, _⟩ | ⟨s, p, k, rfl, _, _⟩ | ⟨s, p, rfl, _, _⟩ <;> simp

/-- **A leaf's `sord` is its computed `iord`.** A `ZDerivation` carries an engine tag `0..6`, so the
`sord` dispatch (tags 7/8/9/10) falls through to the `iord` fallback. -/
theorem sord_eq_iord_of_ZDerivation {d : V} (hd : ZDerivation d) : sord d = iord d := by
  rw [sord, if_neg (zTag_ne_seven_of_ZDerivation hd), if_neg (zTag_ne_eight_of_ZDerivation hd),
    if_neg (zTag_ne_nine_of_ZDerivation hd), if_neg (zTag_ne_ten_of_ZDerivation hd)]

/-- **A leaf's computed ordinal is NF.** `iord d = iotower (iotil d) (idg d)`; `iotil d` is NF for a
`ZDerivation` (`isNF_iotil_of_ZDerivation`), and `iotower` preserves NF (`isNF_iotower`). -/
theorem isNF_iord_of_ZDerivation {d : V} (hd : ZDerivation d) : isNF (iord d) := by
  rw [iord_eq]; exact isNF_iotower (isNF_iotil_of_ZDerivation d hd) (idg d)

/-- **A leaf's `sord` is NF** — unconditional (no positivity). Discharges the `isNF (sord premise)`
hypotheses of the cut-reduct bricks (5c/5d/5e) for any engine-derivation premise (the embedding's image
and the cut-free sub-derivations). -/
theorem isNF_sord_of_ZDerivation {d : V} (hd : ZDerivation d) : isNF (sord d) := by
  rw [sord_eq_iord_of_ZDerivation hd]; exact isNF_iord_of_ZDerivation hd

/-! ### Inversion's ordinal-soundness in the `sord` measure (engine peeling → orbit measure)

When the structural `hinv` (re-principalization) peels an engine leaf — an I∀-node `zIall` or an I¬-node
`zIneg` — to extract its premise (the subformula instance), the orbit's measure `sord` must NOT increase.
The engine already proves the COMPUTED descent (`iord_descent_zIall`/`iord_descent_zIneg`, unconditional);
these bridge it to `sord` (= `iord` on leaves, brick 5f), so the peeling is `sord`-sound. These are the
ordinal halves of the I∀/I¬ inversion steps the genuine `hinv` recursion will compose with the `max+1`
cut descent. -/

/-- **I∀-peel decreases `sord`.** Peeling an I∀-node `zIall s a p d0` to its premise `d0` strictly drops
the orbit measure (`iord_descent_zIall` bridged to `sord` via brick 5f). -/
theorem sord_descent_zIall {s a p d0 : V} (hZ : ZDerivation (zIall s a p d0)) :
    icmp (sord d0) (sord (zIall s a p d0)) = 0 := by
  rw [sord_eq_iord_of_ZDerivation (zDerivation_zIall_inv hZ).1, sord_eq_iord_of_ZDerivation hZ]
  exact iord_descent_zIall s a p d0

/-- **I¬-peel decreases `sord`.** Peeling an I¬-node `zIneg s p d0` to its premise `d0` strictly drops the
orbit measure (`iord_descent_zIneg` bridged to `sord`). -/
theorem sord_descent_zIneg {s p d0 : V} (hZ : ZDerivation (zIneg s p d0)) :
    icmp (sord d0) (sord (zIneg s p d0)) = 0 := by
  rw [sord_eq_iord_of_ZDerivation (zDerivation_zIneg_inv hZ).1, sord_eq_iord_of_ZDerivation hZ]
  exact iord_descent_zIneg s p d0

/-- **Complete leaf I∀-inversion step.** Peeling an I∀-node leaf `zIall s a p d0` yields a `ZcOK` premise
`d0` (an engine `ZDerivation` by `zDerivation_zIall_inv`) with strictly smaller orbit measure. The base
case of the `∀`-inversion recursion the structural `hinv` needs: it both PRESERVES `ZcOK` and DROPS `sord`,
exactly the two invariants `red_iterate_descends` consumes (`hinv` + `hdrop`). -/
theorem zcOK_sord_descent_zIall {s a p d0 : V} (hZ : ZDerivation (zIall s a p d0)) :
    ZcOK d0 ∧ icmp (sord d0) (sord (zIall s a p d0)) = 0 :=
  ⟨.leaf (zDerivation_zIall_inv hZ).1, sord_descent_zIall hZ⟩

/-- **Complete leaf I¬-inversion step.** I¬-node analogue of `zcOK_sord_descent_zIall`: the peeled premise
is `ZcOK` with strictly smaller `sord`. -/
theorem zcOK_sord_descent_zIneg {s p d0 : V} (hZ : ZDerivation (zIneg s p d0)) :
    ZcOK d0 ∧ icmp (sord d0) (sord (zIneg s p d0)) = 0 :=
  ⟨.leaf (zDerivation_zIneg_inv hZ).1, sord_descent_zIneg hZ⟩

/-- **One-step `ZcOK` rule predicate** — the disjunction characterizing each node, the analogue of the
engine's `ZPhi`. `C` is the recursion set (the premise sub-derivations). -/
def ZcPhi (C : V → Prop) (d : V) : Prop :=
  ZDerivation d ∨
  (∃ s d0 a α, d = zAllOmega s d0 a α ∧ (∀ t, IsSemiterm ℒₒᵣ 0 t → C (zsubst d0 a t)) ∧
      (∀ t, IsSemiterm ℒₒᵣ 0 t → icmp (iord (zsubst d0 a t)) α = 0)) ∨
  (∃ s α C0 t d0, d = zExOmega s α C0 t d0 ∧ C d0 ∧ icmp (sord d0) α = 0) ∨
  (∃ s α dL dR C0, d = zCutOmega s α dL dR C0 ∧ C dL ∧ C dR ∧
      icmp (sord dL) α = 0 ∧ icmp (sord dR) α = 0)

/-- **Recursion equation for `ZcOK`** (the inductive-over-`V` analogue of `zDerivation_iff`). Proved by
`cases` on a FREE variable (which Lean CAN dependent-eliminate, unlike `cases` on a specific node), this
is the clean inversion vehicle: all node-inversion lemmas `rcases zcOK_iff.mp h` on the `∨`, then
discriminate by `zTag`. -/
theorem zcOK_iff {d : V} : ZcOK d ↔ ZcPhi ZcOK d := by
  constructor
  · intro h
    cases h with
    | leaf hd => exact Or.inl hd
    | omegaAll hprem hdesc => exact Or.inr (Or.inl ⟨_, _, _, _, rfl, hprem, hdesc⟩)
    | ex hprem hdesc => exact Or.inr (Or.inr (Or.inl ⟨_, _, _, _, _, rfl, hprem, hdesc⟩))
    | cut hL hR hLd hRd => exact Or.inr (Or.inr (Or.inr ⟨_, _, _, _, _, rfl, hL, hR, hLd, hRd⟩))
  · intro h
    rcases h with hd | ⟨s, d0, a, α, rfl, hprem, hdesc⟩ | ⟨s, α, C0, t, d0, rfl, hprem, hdesc⟩ |
      ⟨s, α, dL, dR, C0, rfl, hL, hR, hLd, hRd⟩
    · exact .leaf hd
    · exact .omegaAll hprem hdesc
    · exact .ex hprem hdesc
    · exact .cut hL hR hLd hRd

/-- **Cut-node inversion.** A `ZcOK` cut node decomposes into its two premise derivations + the
operator-control bounds. The leaf/ω-∀/∃ disjuncts of `zcOK_iff` are ruled out by `zTag` (9 vs engine,
7, 10). The template for all node-inversion lemmas. -/
theorem zcOK_cut_inv {s α dL dR C : V} (h : ZcOK (zCutOmega s α dL dR C)) :
    ZcOK dL ∧ ZcOK dR ∧ icmp (sord dL) α = 0 ∧ icmp (sord dR) α = 0 := by
  rcases zcOK_iff.mp h with hd | ⟨s', d0, a, α', heq, _, _⟩ | ⟨s', α', C0, t, d0, heq, _, _⟩ |
    ⟨s', α', dL', dR', C0, heq, hL, hR, hLd, hRd⟩
  · exact absurd (zTag_zCutOmega s α dL dR C) (zTag_ne_nine_of_ZDerivation hd)
  · exact absurd (congrArg zTag heq) (by simp)
  · exact absurd (congrArg zTag heq) (by simp)
  · have hdL : dL = dL' := by have := congrArg zCutL heq; simpa using this
    have hdR : dR = dR' := by have := congrArg zCutR heq; simpa using this
    have hα : α = α' := by have := congrArg sord heq; simpa using this
    subst hdL hdR hα
    exact ⟨hL, hR, hLd, hRd⟩

/-- **ω-∀-node inversion.** A `ZcOK` ω-∀-node decomposes into its uniformly-valid premise family + the
operator-control bounds — exactly the data the ∀-inversion `redInv∀` reads at the principal case. -/
theorem zcOK_omegaAll_inv {s d0 a α : V} (h : ZcOK (zAllOmega s d0 a α)) :
    (∀ t, IsSemiterm ℒₒᵣ 0 t → ZcOK (zsubst d0 a t)) ∧
    (∀ t, IsSemiterm ℒₒᵣ 0 t → icmp (iord (zsubst d0 a t)) α = 0) := by
  rcases zcOK_iff.mp h with hd | ⟨s', d0', a', α', heq, hprem, hdesc⟩ |
    ⟨s', α', C0, t, d0', heq, _, _⟩ | ⟨s', α', dL', dR', C0, heq, _, _, _, _⟩
  · exact absurd (zTag_zAllOmega s d0 a α) (zTag_ne_seven_of_ZDerivation hd)
  · have hd0 : d0 = d0' := by have := congrArg zAllD0 heq; simpa using this
    have ha : a = a' := by have := congrArg zAllEig heq; simpa using this
    have hα : α = α' := by have := congrArg sord heq; simpa using this
    subst hd0 ha hα; exact ⟨hprem, hdesc⟩
  · exact absurd (congrArg zTag heq) (by simp)
  · exact absurd (congrArg zTag heq) (by simp)

/-- **PRINCIPAL `∀`-inversion step (the ω-∀ case) — the central inversion case.** When the derivation's
last rule IS the ω-∀ introduction (`zAllOmega`), inversion at a witness `t` is premise SELECTION: the
stored premise family at `t`, `zsubst d0 a t`, is `ZcOK` and its computed ordinal `iord` is strictly below
the node's stored `sord = α`. BOTH inversion invariants in one statement (`ZcOK` preserved + ordinal drops)
— the principal (last-rule-introduces-the-`∀`) base case of the `∀`-inversion recursion, the case the
non-principal (commuting) cases bottom out at. No ordinal increase (the lap-104 inversion requirement). -/
theorem zcOK_iord_descent_zAllOmega {s d0 a α t : V}
    (h : ZcOK (zAllOmega s d0 a α)) (ht : IsSemiterm ℒₒᵣ 0 t) :
    ZcOK (zsubst d0 a t) ∧ icmp (iord (zsubst d0 a t)) (sord (zAllOmega s d0 a α)) = 0 := by
  obtain ⟨hprem, hdesc⟩ := zcOK_omegaAll_inv h
  exact ⟨hprem t ht, by rw [sord_zAllOmega]; exact hdesc t ht⟩

/-- **∃-node inversion.** A `ZcOK` ∃-node decomposes into its witness premise + the operator-control
bound. (With `zExTerm`/`zExPrem` the witness/premise are read off the node, lap 103.) -/
theorem zcOK_ex_inv {s α C t d : V} (h : ZcOK (zExOmega s α C t d)) :
    ZcOK d ∧ icmp (sord d) α = 0 := by
  rcases zcOK_iff.mp h with hd | ⟨s', d0', a', α', heq, _, _⟩ |
    ⟨s', α', C0, t', d0, heq, hprem, hdesc⟩ | ⟨s', α', dL', dR', C0, heq, _, _, _, _⟩
  · exact absurd (zTag_zExOmega s α C t d) (zTag_ne_ten_of_ZDerivation hd)
  · exact absurd (congrArg zTag heq) (by simp)
  · have hd0 : d = d0 := by have := congrArg zExPrem heq; simpa using this
    have hα : α = α' := by have := congrArg sord heq; simpa using this
    subst hd0 hα; exact ⟨hprem, hdesc⟩
  · exact absurd (congrArg zTag heq) (by simp)

/-! ### Brick 5b — principal ∀/∃-cut `hinv`: the STRUCTURAL closure (clean) + the ordinal obligation (isolated)

`hinv` (`red` preserves `ZcOK`) on a PRINCIPAL ∀/∃-cut (left = ω-∀-node, right = ∃-node) splits cleanly:
- **Structural half (PROVED, `zcOK_redAllEx_premises`):** the reduct's two premises (`zsubst d0 a tE` and the
  ∃-premise `dE`) are themselves `ZcOK` — `zcOK_cut_inv` ⟶ `zcOK_omegaAll_inv` (premise family at the witness)
  + `zcOK_ex_inv`. This is the genuine cut-elimination soundness content for the principal case: the reduct's
  premises are valid derivations. (For the GENERAL case where the left is not literally a ω-∀-node, this is
  where ∀-INVERSION `redInv∀` replaces premise selection — the next brick.)
- **Ordinal half (ISOLATED, `zcOK_redAllEx_of_ctrl`):** to repackage the reduct as a `ZcOK` cut, its stored
  ordinal must STRICTLY dominate both reduced premises. **⚠ Lap-104 finding: the lap-103 `imax` choice is
  insufficient here.** The reduct stores `imax (sord dL') (sord dR')`, but the `cut` constructor needs
  `sord premise ≺ stored`, and the max-ACHIEVING premise EQUALS `imax` (never `≺` — `icmp` is irreflexive).
  So `hLctrl`/`hRctrl` below cannot both hold for the naive `imax`. The genuine fix is Gentzen's RANK-AWARE
  ordinal assignment (`o(cut) = ω^{rank} ⊕ …`, strictly above premises AND ≺ the parent), which also carries
  the single-step DESCENT — the deep Gentzen-Hauptsatz content of crux-2. `imax` worked for the parent-cut
  *descent* (`sord_redAllEx_lt`) but not for the reduct's own *operator-control*; these need the same
  rank-aware `sord`. This isolates the remaining deep obligation to the ORDINAL assignment alone. -/

/-- **Principal ∀/∃-cut `hinv` — the STRUCTURAL closure (axiom-clean).** The reduct of a `ZcOK` cut whose
left premise is an ω-∀-node and right is an ∃-node has BOTH its reduced premises `ZcOK`: the witness premise
`zsubst d0 a tE` (the ω-∀-node's premise family at `tE`) and the ∃-premise `dE`. The genuine soundness
content; the reduct cut is then `ZcOK` once its stored ordinal strictly dominates these
(`zcOK_redAllEx_of_ctrl` — the isolated ordinal obligation). -/
theorem zcOK_redAllEx_premises {s α s' d0 a αAll sE αEx CE tE dE C : V}
    (h : ZcOK (zCutOmega s α (zAllOmega s' d0 a αAll) (zExOmega sE αEx CE tE dE) C))
    (htE : IsSemiterm ℒₒᵣ 0 tE) :
    ZcOK (zsubst d0 a tE) ∧ ZcOK dE := by
  obtain ⟨hL, hR, _, _⟩ := zcOK_cut_inv h
  obtain ⟨hprem, _⟩ := zcOK_omegaAll_inv hL
  obtain ⟨hdE, _⟩ := zcOK_ex_inv hR
  exact ⟨hprem tE htE, hdE⟩

/-- **Principal ∀/∃-cut `hinv` — full closure GIVEN the reduct's operator-control.** With the structural
closure (`zcOK_redAllEx_premises`) and the two ordinal-control bounds (`hLctrl`/`hRctrl` — the reduct's
premises strictly below its stored ordinal), the reduct `redAllEx …` is `ZcOK`. This exhibits EXACTLY the
remaining obligation: a stored ordinal strictly above both reduced premises. The naive `imax` cannot supply
it (max-achiever equals it); Gentzen's rank-aware assignment can — the isolated deep crux-2 content. -/
theorem zcOK_redAllEx_of_ctrl {s α s' d0 a αAll sE αEx CE tE dE C : V}
    (h : ZcOK (zCutOmega s α (zAllOmega s' d0 a αAll) (zExOmega sE αEx CE tE dE) C))
    (htE : IsSemiterm ℒₒᵣ 0 tE)
    (hLctrl : icmp (sord (zsubst d0 a tE)) (imax (iord (zsubst d0 a tE)) (sord dE)) = 0)
    (hRctrl : icmp (sord dE) (imax (iord (zsubst d0 a tE)) (sord dE)) = 0) :
    ZcOK (redAllEx s d0 a C (zExOmega sE αEx CE tE dE)) := by
  obtain ⟨hZl, hZr⟩ := zcOK_redAllEx_premises h htE
  rw [redAllEx]
  simp only [zExTerm_zExOmega, zExPrem_zExOmega]
  exact ZcOK.cut hZl hZr hLctrl hRctrl

/-! ### Brick 5c (lap 105) — the natural-sum `#` RESOLUTION of the lap-104 `imax` tension

Lap 104 found `imax` cannot serve the cut node's operator-control (`sord premise ≺ stored`): the
max-ACHIEVING premise EQUALS `imax`, never `≺` it. It framed the fix as Gentzen's rank-aware ordinal
(the `ω`-tower), deferring it as "genuinely multi-month". **That deferral is unnecessary for the
principal ∀/∃ step.** The natural (Hessenberg) sum `inadd` (`#`) on CNF codes — already used for the
induction node's stored ordinal (`indOmegaStoredOrd`) — supplies BOTH obligations at once:

- **Operator-control** holds because `#` is STRICTLY self-dominating: `X ≺ X # g` whenever `g ≻ 0`
  (`lt_inadd_self_right`), and `g ≺ X # g` whenever `X ≻ 0` (`lt_inadd_self_left`). So a cut node
  storing `(sord dL) # (sord dR)` strictly dominates BOTH premises (each other premise positive) —
  exactly what `imax` could not do.
- **Descent** holds because `#` is STRICTLY MONOTONE in both arguments (`inadd_strict_mono`): if the
  reduct's two premises are each `≺` the parent's corresponding premise (`sord (zsubst …) ≺ αAll`,
  `sord (zExPrem …) ≺ αEx`), then `(sord (zsubst …)) # (sord (zExPrem …)) ≺ αAll # αEx`. So against a
  parent that ALSO stores `#` of its premises, the reduct strictly drops — **no additive-principality
  of the parent ordinal is needed** (the worry that drove lap 104 to `imax`). The parent's `#`-stored
  ordinal is itself the operator-controlled value, and strict-monotonicity carries the descent.

This is the standard Schütte `#`-bookkeeping (Towsner's meta proof combines cut premises by natural
sum); the single-ordinal `red`-descent rides on it for the principal cut. (The remaining genuinely-deep
content — rank-mixing across compound cut formulas, where a single cut reduction spawns lower-rank cuts
— is where the `ω`-tower of `Zinfty.cutElimStep` collapses `(rank, ord)` into one ordinal; that is the
NEXT obligation, now sharply isolated to compound formulas, off the ∀/∃ principal step.) -/

/-- **Natural-sum strict self-domination, right summand.** `X ≺ X # g` for NF `X, g` with `g ≻ 0`.
The operator-control fact `imax` could not provide: the left premise is strictly below the cut's stored
`# `-ordinal. -/
theorem lt_inadd_self_right {X g : V} (hX : isNF X) (hg : isNF g) (hg0 : icmp 0 g = 0) :
    icmp X (inadd X g) = 0 := by
  have := inadd_left_mono isNF_zero hg hg0 X hX
  rwa [inadd_zero_right X hX] at this

/-- **Natural-sum strict self-domination, left summand.** `g ≺ X # g` for NF `X, g` with `X ≻ 0`. -/
theorem lt_inadd_self_left {X g : V} (hX : isNF X) (hg : isNF g) (hX0 : icmp 0 X = 0) :
    icmp g (inadd X g) = 0 := by
  have := inadd_right_mono isNF_zero hX hX0 g hg
  rwa [inadd_zero_left] at this

/-- **Natural-sum strict monotonicity (both arguments).** `a ≺ a' → b ≺ b' → a # b ≺ a' # b'`
(all NF). The descent fact: a reduct whose two premises strictly drop below the parent's two premises
has its `#`-stored ordinal strictly below the parent's `#`-stored ordinal — no additive-principality
of the parent needed. -/
theorem inadd_strict_mono {a a' b b' : V}
    (ha : isNF a) (ha' : isNF a') (hb : isNF b) (hb' : isNF b')
    (h1 : icmp a a' = 0) (h2 : icmp b b' = 0) : icmp (inadd a b) (inadd a' b') = 0 :=
  icmp_trans' (inadd_right_mono ha ha' h1 b hb) (inadd_left_mono hb hb' h2 a' ha')

/-- **The `#`-stored ∀/∃-cut reduct.** Identical to `redAllEx` but the stored ordinal is the natural
SUM `(sord (selected ∀-premise)) # (sord (∃-premise))`, not their `imax`. The sum stores the reduced
premises' OWN stored ordinals (`sord`, not `iord`) — correct even when a premise is itself a cut/ω-node
(general Path-C), unlike `imax`'s `iord` left field. -/
noncomputable def redAllExN (s d0 a Cnew dR : V) : V :=
  zCutOmega s (inadd (sord (zsubst d0 a (zExTerm dR))) (sord (zExPrem dR)))
    (zsubst d0 a (zExTerm dR)) (zExPrem dR) Cnew

/-- **Principal ∀/∃-cut `hinv` — FULL closure, `imax`-free (axiom-clean).** The `#`-stored reduct of a
`ZcOK` cut (left = ω-∀-node, right = ∃-node) is `ZcOK`. Operator-control is DISCHARGED from the
premises' positivity + NF alone (`lt_inadd_self_right`/`lt_inadd_self_left`) — no externally-supplied
`hLctrl`/`hRctrl` (contrast `zcOK_redAllEx_of_ctrl`, which had to assume them and could not prove them
for `imax`). This closes the operator-control half of `hinv` for the principal ∀/∃ step. -/
theorem zcOK_redAllExN {s α s' d0 a αAll sE αEx CE tE dE C : V}
    (h : ZcOK (zCutOmega s α (zAllOmega s' d0 a αAll) (zExOmega sE αEx CE tE dE) C))
    (htE : IsSemiterm ℒₒᵣ 0 tE)
    (hLnf : isNF (sord (zsubst d0 a tE))) (hRnf : isNF (sord dE))
    (hLpos : icmp 0 (sord (zsubst d0 a tE)) = 0) (hRpos : icmp 0 (sord dE) = 0) :
    ZcOK (redAllExN s d0 a C (zExOmega sE αEx CE tE dE)) := by
  obtain ⟨hZl, hZr⟩ := zcOK_redAllEx_premises h htE
  rw [redAllExN]
  simp only [zExTerm_zExOmega, zExPrem_zExOmega]
  refine ZcOK.cut hZl hZr ?_ ?_
  · exact lt_inadd_self_right hLnf hRnf hRpos
  · exact lt_inadd_self_left hLnf hRnf hLpos

/-- **The `#`-stored ∀/∃-cut reduction STRICTLY drops the stored ordinal — against a `#`-stored parent.**
If the reduct's selected ∀-premise and the ∃-premise each have `sord ≺` the parent's corresponding
premise ordinals (`αAll`, `αEx`), the reduct's stored `# `-ordinal is `≺ αAll # αEx` — the parent's
own `# `-stored ordinal. This is the per-step descent for the principal ∀/∃ cut WITHOUT
additive-principality (the obstruction lap-104's `imax` was chosen to dodge): strict-monotonicity of
`#` (`inadd_strict_mono`) carries it, given consistent `#`-storage on both parent and reduct. -/
theorem sord_redAllExN_lt {s d0 a Cnew dR αAll αEx : V}
    (hLlt : icmp (sord (zsubst d0 a (zExTerm dR))) αAll = 0)
    (hRlt : icmp (sord (zExPrem dR)) αEx = 0)
    (hLnf : isNF (sord (zsubst d0 a (zExTerm dR)))) (hRnf : isNF (sord (zExPrem dR)))
    (hAnf : isNF αAll) (hEnf : isNF αEx) :
    icmp (sord (redAllExN s d0 a Cnew dR)) (inadd αAll αEx) = 0 := by
  rw [redAllExN, sord_zCutOmega]
  exact inadd_strict_mono hLnf hAnf hRnf hEnf hLlt hRlt

/-! ### Brick 5d (lap 105) — the `#`-resolution is UNIFORM: the induction/∃-cut reduct too

The natural-sum resolution is not special to the ∀/∃ cut — it applies verbatim to the OTHER ω-node,
the INDUCTION node (PA's genuinely-specific rule). The induction/∃ cut reduces by selecting the depth-`k`
unfolding `zK s' (irk p) (iIndReductSeq d0 d1 t)` (`t = zExTerm dR`, deriving `F(t)`; brick 3) against the
∃-premise; the `#`-stored reduct is `ZcOK` and strictly drops the stored ordinal against a `#`-stored
parent — by the SAME `lt_inadd_self_*`/`inadd_strict_mono` argument as `redAllExN`. This confirms the
lap-105 insight is structural to the cut node, not to one cut-formula shape. (The premises' `ZcOK`-hood is
taken as hypotheses: the unfolding is an engine `ZDerivation` ⟹ `ZcOK.leaf`, the ∃-premise from the cut's
right-inversion — same provenance as `zcOK_redAllExN`, now via the brick-3 induction node once that
constructor lands in `ZcOK`.) -/

/-- **The `#`-stored induction/∃-cut reduct** (induction analogue of `redAllExN`). Stores the natural
SUM of the selected depth-`zExTerm dR` unfolding's `sord` and the ∃-premise's `sord`. -/
noncomputable def redIndExN (s s' at' p d0 d1 Cnew dR : V) : V :=
  zCutOmega s
    (inadd (sord (zK s' (irk p) (iIndReductSeq d0 d1 (zExTerm dR)))) (sord (zExPrem dR)))
    (zK s' (irk p) (iIndReductSeq d0 d1 (zExTerm dR))) (zExPrem dR) Cnew

/-- **Induction/∃-cut `hinv` — full closure, `imax`-free (axiom-clean).** Given both reduced premises
`ZcOK` (the depth-`k` unfolding + the ∃-premise) and positive/NF `sord`s, the `#`-stored induction/∃-cut
reduct is `ZcOK` — operator-control discharged by `lt_inadd_self_right`/`_left`, exactly as the ∀/∃ case. -/
theorem zcOK_redIndExN {s s' at' p d0 d1 Cnew dR : V}
    (hL : ZcOK (zK s' (irk p) (iIndReductSeq d0 d1 (zExTerm dR))))
    (hR : ZcOK (zExPrem dR))
    (hLnf : isNF (sord (zK s' (irk p) (iIndReductSeq d0 d1 (zExTerm dR)))))
    (hRnf : isNF (sord (zExPrem dR)))
    (hLpos : icmp 0 (sord (zK s' (irk p) (iIndReductSeq d0 d1 (zExTerm dR)))) = 0)
    (hRpos : icmp 0 (sord (zExPrem dR)) = 0) :
    ZcOK (redIndExN s s' at' p d0 d1 Cnew dR) := by
  rw [redIndExN]
  refine ZcOK.cut hL hR ?_ ?_
  · exact lt_inadd_self_right hLnf hRnf hRpos
  · exact lt_inadd_self_left hLnf hRnf hLpos

/-- **The `#`-stored induction/∃-cut reduction STRICTLY drops the stored ordinal — against a `#`-stored
parent.** Induction analogue of `sord_redAllExN_lt`: from the unfolding's `sord ≺ αInd` (brick 3's stored
limit) and the ∃-premise's `sord ≺ αEx`, the reduct's `#`-stored ordinal is `≺ αInd # αEx`. Same
strict-monotonicity argument; no additive-principality of the parent needed. -/
theorem sord_redIndExN_lt {s s' at' p d0 d1 Cnew dR αInd αEx : V}
    (hLlt : icmp (sord (zK s' (irk p) (iIndReductSeq d0 d1 (zExTerm dR)))) αInd = 0)
    (hRlt : icmp (sord (zExPrem dR)) αEx = 0)
    (hLnf : isNF (sord (zK s' (irk p) (iIndReductSeq d0 d1 (zExTerm dR)))))
    (hRnf : isNF (sord (zExPrem dR))) (hAnf : isNF αInd) (hEnf : isNF αEx) :
    icmp (sord (redIndExN s s' at' p d0 d1 Cnew dR)) (inadd αInd αEx) = 0 := by
  rw [redIndExN, sord_zCutOmega]
  exact inadd_strict_mono hLnf hAnf hRnf hEnf hLlt hRlt

/-! ### Brick 5e (lap 105) — the COMPLETE cut ordinal `max(a,b)+1`: no positivity, arbitrary parent

Bricks 5c/5d (`#`-storage) close operator-control only when BOTH premises have positive ordinal
(`X ≺ X#g` needs `g ≻ 0`). But an axiom LEAF has ordinal `0` (Schütte's `o(axiom)=0`), so a cut whose
premise is an axiom breaks the `#` operator-control. The textbook Tait/Schütte cut ordinal removes the
gap: store `o(cut) = max(o(dL), o(dR)) + 1` (`inc (imax …)`). Then:
- **Operator-control** holds UNCONDITIONALLY: each premise is `≼ imax ≺ imax + 1` (`lt_imax_inc_left/right`)
  — no positivity needed (the `+1` supplies the strictness `imax` itself lacked, the exact lap-104 gap).
- **Descent** holds against an ARBITRARY `max+1`-stored parent: `a' ≺ a, b' ≺ b ⟹ imax a' b' ≺ imax a b ⟹
  imax a' b' + 1 ≺ imax a b + 1` (`inc_imax_strict_mono`), via the linear-order fact `max` of two things
  each `≺ M` is `≺ M` (`icmp_imax_lt`) — no additive-principality of the parent (the lap-104 `imax` virtue,
  now WITH operator-control too). This is the complete resolution; it supersedes lap-104's bare `imax`
  (no op-control) and bricks 5c/5d's `#` (positivity-gated). The genuinely-deep content remaining is purely
  the rank-mixing tower for COMPOUND cut formulas, off the principal ω-cut step entirely. -/

/-- **Ordinal successor on CNF codes**: `inc α = α # 1` (`1 = ω^0`). NF-preserving; `α ≺ inc α` always
(`1 ≻ 0`), the strictness the bare `imax` lacked. -/
noncomputable def inc (α : V) : V := inadd α (ocOadd 0 1 0)

/-- `1 = ω^0·1` is NF. -/
theorem isNF_one_oc : isNF (ocOadd 0 1 0 : V) :=
  (isNF_ocOadd 0 1 0).mpr ⟨_root_.one_ne_zero, isNF_zero, isNF_zero, Or.inl rfl⟩

/-- `inc` preserves NF. -/
theorem isNF_inc {α : V} (hα : isNF α) : isNF (inc α) := isNF_inadd isNF_one_oc α hα

/-- **`α ≺ inc α`** (strict successor) — always, no positivity. -/
theorem lt_inc {α : V} (hα : isNF α) : icmp α (inc α) = 0 :=
  lt_inadd_self_right hα isNF_one_oc (icmp_zero_ocOadd 0 1 0)

/-- `inc` is strictly monotone: `α ≺ β → inc α ≺ inc β`. -/
theorem inc_strict_mono {α β : V} (hα : isNF α) (hβ : isNF β) (h : icmp α β = 0) :
    icmp (inc α) (inc β) = 0 :=
  inadd_right_mono hα hβ h (ocOadd 0 1 0) isNF_one_oc

/-- `imax` preserves NF. -/
theorem isNF_imax {a b : V} (ha : isNF a) (hb : isNF b) : isNF (imax a b) := by
  unfold imax; split <;> assumption

/-- **`a ≺ inc (imax a b)`** — operator-control, left premise, NO positivity. `a ≼ imax a b ≺ imax a b + 1`. -/
theorem lt_imax_inc_left {a b : V} (ha : isNF a) (hb : isNF b) : icmp a (inc (imax a b)) = 0 := by
  by_cases hab : icmp a b = 0
  · simp only [imax, if_pos hab]; exact icmp_trans' hab (lt_inc hb)
  · simp only [imax, if_neg hab]; exact lt_inc ha

/-- **`b ≺ inc (imax a b)`** — operator-control, right premise, NO positivity. -/
theorem lt_imax_inc_right {a b : V} (ha : isNF a) (hb : isNF b) : icmp b (inc (imax a b)) = 0 := by
  by_cases hab : icmp a b = 0
  · simp only [imax, if_pos hab]; exact lt_inc hb
  · simp only [imax, if_neg hab]
    rcases icmp_tri a b with h | h | h
    · exact absurd h hab
    · have he : a = b := icmp_eq_imp_eq (a + b) a le_self_add b le_add_self h
      rw [he]; exact lt_inc hb
    · exact icmp_trans' (icmp_two_iff_swap_zero.mp h) (lt_inc ha)

/-- `a' ≺ a ⟹ a' ≺ imax a b` (`a ≼ imax a b`). -/
theorem lt_imax_of_lt_left {a' a b : V} (h : icmp a' a = 0) : icmp a' (imax a b) = 0 := by
  by_cases hab : icmp a b = 0
  · simp only [imax, if_pos hab]; exact icmp_trans' h hab
  · simp only [imax, if_neg hab]; exact h

/-- `b' ≺ b ⟹ b' ≺ imax a b` (`b ≼ imax a b`). -/
theorem lt_imax_of_lt_right {b' a b : V} (h : icmp b' b = 0) : icmp b' (imax a b) = 0 := by
  by_cases hab : icmp a b = 0
  · simp only [imax, if_pos hab]; exact h
  · simp only [imax, if_neg hab]
    rcases icmp_tri a b with hh | hh | hh
    · exact absurd hh hab
    · have he : a = b := icmp_eq_imp_eq (a + b) a le_self_add b le_add_self hh
      rw [he]; exact h
    · exact icmp_trans' h (icmp_two_iff_swap_zero.mp hh)

/-- **`max+1` is strictly monotone in both premises** — the descent fact, against an arbitrary
`max+1`-stored parent (no additive-principality). `a'≺a, b'≺b ⟹ imax a' b' + 1 ≺ imax a b + 1`. -/
theorem inc_imax_strict_mono {a' a b' b : V}
    (ha' : isNF a') (ha : isNF a) (hb' : isNF b') (hb : isNF b)
    (h1 : icmp a' a = 0) (h2 : icmp b' b = 0) :
    icmp (inc (imax a' b')) (inc (imax a b)) = 0 :=
  inc_strict_mono (isNF_imax ha' hb') (isNF_imax ha hb)
    (icmp_imax_lt (lt_imax_of_lt_left h1) (lt_imax_of_lt_right h2))

/-- **The `max+1`-stored ∀/∃-cut reduct** — the complete cut ordinal. -/
noncomputable def redAllExS (s d0 a Cnew dR : V) : V :=
  zCutOmega s (inc (imax (sord (zsubst d0 a (zExTerm dR))) (sord (zExPrem dR))))
    (zsubst d0 a (zExTerm dR)) (zExPrem dR) Cnew

/-- **Principal ∀/∃-cut `hinv` — COMPLETE closure (axiom-clean, NO positivity).** The `max+1`-stored
reduct of a `ZcOK` cut (left = ω-∀-node, right = ∃-node) is `ZcOK`, with operator-control discharged from
the premises' NF ALONE (`lt_imax_inc_left/right`) — no positivity, so it holds even when a reduced premise
is an axiom leaf (ordinal `0`), the case bricks 5c/5d's `#`-storage could not handle. This is the complete
operator-control half of `hinv` for the principal ∀/∃ step. -/
theorem zcOK_redAllExS {s α s' d0 a αAll sE αEx CE tE dE C : V}
    (h : ZcOK (zCutOmega s α (zAllOmega s' d0 a αAll) (zExOmega sE αEx CE tE dE) C))
    (htE : IsSemiterm ℒₒᵣ 0 tE)
    (hLnf : isNF (sord (zsubst d0 a tE))) (hRnf : isNF (sord dE)) :
    ZcOK (redAllExS s d0 a C (zExOmega sE αEx CE tE dE)) := by
  obtain ⟨hZl, hZr⟩ := zcOK_redAllEx_premises h htE
  rw [redAllExS]
  simp only [zExTerm_zExOmega, zExPrem_zExOmega]
  refine ZcOK.cut hZl hZr ?_ ?_
  · exact lt_imax_inc_left hLnf hRnf
  · exact lt_imax_inc_right hLnf hRnf

/-- **Principal ∀/∃-cut `hinv` — COMPLETE closure for LEAF premises (zero side conditions).** When the
two reduced premises are engine `ZDerivation`s (the embedding's image / cut-free sub-derivations), their
`sord` NF is automatic (`isNF_sord_of_ZDerivation`), so the `max+1`-stored reduct is `ZcOK` with NO NF and
NO positivity hypothesis — the cleanest statement of the principal ∀/∃ operator-control. -/
theorem zcOK_redAllExS_leaf {s α s' d0 a αAll sE αEx CE tE dE C : V}
    (h : ZcOK (zCutOmega s α (zAllOmega s' d0 a αAll) (zExOmega sE αEx CE tE dE) C))
    (htE : IsSemiterm ℒₒᵣ 0 tE)
    (hLZ : ZDerivation (zsubst d0 a tE)) (hRZ : ZDerivation dE) :
    ZcOK (redAllExS s d0 a C (zExOmega sE αEx CE tE dE)) :=
  zcOK_redAllExS h htE (isNF_sord_of_ZDerivation hLZ) (isNF_sord_of_ZDerivation hRZ)

/-- **The `max+1`-stored ∀/∃-cut reduction STRICTLY drops the stored ordinal — against an ARBITRARY
`max+1`-stored parent.** From the reduct premises each `≺` the parent's corresponding premise ordinals,
the reduct's `max+1`-ordinal `≺ max(αAll, αEx) + 1` (the parent's). No additive-principality needed (the
lap-104 `imax` virtue), AND with operator-control (the lap-104 `imax` gap, now closed by the `+1`). -/
theorem sord_redAllExS_lt {s d0 a Cnew dR αAll αEx : V}
    (hLlt : icmp (sord (zsubst d0 a (zExTerm dR))) αAll = 0)
    (hRlt : icmp (sord (zExPrem dR)) αEx = 0)
    (hLnf : isNF (sord (zsubst d0 a (zExTerm dR)))) (hRnf : isNF (sord (zExPrem dR)))
    (hAnf : isNF αAll) (hEnf : isNF αEx) :
    icmp (sord (redAllExS s d0 a Cnew dR)) (inc (imax αAll αEx)) = 0 := by
  rw [redAllExS, sord_zCutOmega]
  exact inc_imax_strict_mono hLnf hAnf hRnf hEnf hLlt hRlt

/-! ### Brick 5g (lap 105) — `max+1` for the induction node too (the complete resolution is uniform)

The induction-node analogue of brick 5e: `redIndExS` stores `max(o(unfolding), o(∃-prem)) + 1`. Same
`lt_imax_inc_left/right` (operator-control, no positivity) + `inc_imax_strict_mono` (descent, arbitrary
parent). Together with brick 5e, the COMPLETE `max+1` cut ordinal closes the principal cut step for BOTH
ω-nodes (∀ and induction) with zero side conditions beyond NF — and NF is automatic for engine-derivation
premises (`isNF_sord_of_ZDerivation`, brick 5f). -/

/-- **The `max+1`-stored induction/∃-cut reduct** (induction analogue of `redAllExS`). -/
noncomputable def redIndExS (s s' at' p d0 d1 Cnew dR : V) : V :=
  zCutOmega s
    (inc (imax (sord (zK s' (irk p) (iIndReductSeq d0 d1 (zExTerm dR)))) (sord (zExPrem dR))))
    (zK s' (irk p) (iIndReductSeq d0 d1 (zExTerm dR))) (zExPrem dR) Cnew

/-- **Induction/∃-cut `hinv` — COMPLETE closure (axiom-clean, NO positivity).** Given both reduced
premises `ZcOK` and NF `sord`s, the `max+1`-stored induction/∃-cut reduct is `ZcOK` — operator-control
from NF alone, exactly as the ∀/∃ case. -/
theorem zcOK_redIndExS {s s' at' p d0 d1 Cnew dR : V}
    (hL : ZcOK (zK s' (irk p) (iIndReductSeq d0 d1 (zExTerm dR))))
    (hR : ZcOK (zExPrem dR))
    (hLnf : isNF (sord (zK s' (irk p) (iIndReductSeq d0 d1 (zExTerm dR)))))
    (hRnf : isNF (sord (zExPrem dR))) :
    ZcOK (redIndExS s s' at' p d0 d1 Cnew dR) := by
  rw [redIndExS]
  refine ZcOK.cut hL hR ?_ ?_
  · exact lt_imax_inc_left hLnf hRnf
  · exact lt_imax_inc_right hLnf hRnf

/-- **The `max+1`-stored induction/∃-cut reduction STRICTLY drops the stored ordinal — against an
ARBITRARY `max+1`-stored parent.** Induction analogue of `sord_redAllExS_lt`. -/
theorem sord_redIndExS_lt {s s' at' p d0 d1 Cnew dR αInd αEx : V}
    (hLlt : icmp (sord (zK s' (irk p) (iIndReductSeq d0 d1 (zExTerm dR)))) αInd = 0)
    (hRlt : icmp (sord (zExPrem dR)) αEx = 0)
    (hLnf : isNF (sord (zK s' (irk p) (iIndReductSeq d0 d1 (zExTerm dR)))))
    (hRnf : isNF (sord (zExPrem dR))) (hAnf : isNF αInd) (hEnf : isNF αEx) :
    icmp (sord (redIndExS s s' at' p d0 d1 Cnew dR)) (inc (imax αInd αEx)) = 0 := by
  rw [redIndExS, sord_zCutOmega]
  exact inc_imax_strict_mono hLnf hAnf hRnf hEnf hLlt hRlt

/-! ### Brick 5h (lap 105) — the canonical `max+1` cut CONSTRUCTOR (the orbit invariant's cut builder)

The red-specific bricks (5c–5g) all instantiate ONE fact: a cut node built over two `ZcOK` premises with
the canonical stored ordinal `max(sord dL, sord dR) + 1` is itself `ZcOK`, operator-control discharged from
NF alone. This is the "smart constructor" `zcOK_cutS` — the cut builder the orbit invariant `P = ZcOK ∧ …`
uses for EVERY cut, side-condition-free (NF auto for leaf premises, brick 5f). `redAllExS`/`redIndExS` are
its instances; it is also the parent-cut shape the descent lemmas (`sord_red*ExS_lt`) drop against. -/

/-- **Canonical `max+1` cut constructor (axiom-clean).** Over two `ZcOK` premises with NF `sord`s, the cut
node storing `max(sord dL, sord dR) + 1` is `ZcOK` — operator-control from NF alone, no positivity, no
externally-supplied control bounds. The reusable cut builder for the Path-C orbit. -/
theorem zcOK_cutS {s dL dR C : V} (hL : ZcOK dL) (hR : ZcOK dR)
    (hLnf : isNF (sord dL)) (hRnf : isNF (sord dR)) :
    ZcOK (zCutOmega s (inc (imax (sord dL) (sord dR))) dL dR C) :=
  ZcOK.cut hL hR (lt_imax_inc_left hLnf hRnf) (lt_imax_inc_right hLnf hRnf)

/-- **Canonical `max+1` cut constructor for LEAF premises (zero side conditions).** When both premises are
engine `ZDerivation`s, their `sord` NF is automatic (`isNF_sord_of_ZDerivation`), so the `max+1` cut is
`ZcOK` with NO hypotheses beyond the premises' derivation-hood. -/
theorem zcOK_cutS_leaf {s dL dR C : V} (hLZ : ZDerivation dL) (hRZ : ZDerivation dR) :
    ZcOK (zCutOmega s (inc (imax (sord dL) (sord dR))) dL dR C) :=
  zcOK_cutS (.leaf hLZ) (.leaf hRZ) (isNF_sord_of_ZDerivation hLZ) (isNF_sord_of_ZDerivation hRZ)

/-! ## NEXT BRICKS (Path C, `sorry`-disclosed milestones — PENDING_WORK lap 102)

Brick 1 above pins the ω-∀-node design + its cut invariant on the existing engine. The remaining Path-C
datatype (each a `wip/` milestone, ported from `ZinftyF.Deriv`/`o`/`cr`):

- **Brick 2 — `cutElimStep` (the single rank drop).** The full Schütte/Tait reduction over all node shapes
  (`Zinfty.cutElimStep`/`cutElimPrincipal`, Towsner §19.7): a rank-`c+1` derivation reduces to rank-`c` with
  stored ordinal `α ↦ ω^α`. The ∀-cut case = brick 1; the ∧/∨/atom cases are the other `cutReduce*`.
- **Brick 3 — the induction ω-node.** Kernel DONE above (`indOmegaStoredOrd` + `iord_iIndReduct_lt_storedBound`):
  the stored limit ordinal provably dominates every finite unfolding's `iord`, uniformly in `k`. Remaining:
  package it as a node + validity (premise-family `ZDerivation`s via `znth_iIndReductSeq_ZDerivation`, the
  conclusion-tracking `F(k)`, the Σ₁ side-condition), mirroring `zAllOmega`/`zAllOmegaValid`.
- **Brick 4 — `false_of_ZDerivesEmpty` (Path C).** SKELETON DONE (`stored_ord_iterate_descends`): the
  iteration of a per-step stored-ordinal drop. `red` = one Buchholz `red` step (NOT Zinfty `cutElimStep` —
  see the endgame design note above); the ∅→⊥ sequent has no cut-free proof, so `red` never terminates ⟹
  stored ordinal strictly descends forever ⟹ infinite ε₀-descent ⟹ contradicts PRWO(ε₀) (crux-1). Remaining:
  define `red` on the datatype (so `hdrop` is discharged by bricks 1/3) + wire to
  `gentzen_descent_of_inconsistent`. No chain, no `redZKReady`.
- **Σ₁-definability** of `zAllOmega`/`zAllOmegaValid` (the `⟪…⟫`/`icmp`/`iord` pieces are all already
  `𝚺₁`/`𝚫₁`; this is bookkeeping, deferred until the datatype shape stabilizes). -/

end GoodsteinPA.InternalZ.PathC



