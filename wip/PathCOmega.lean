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
    ∨ (tg ≠ 7 ∧ tg ≠ 8 ∧ tg ≠ 9 ∧ !iordDef y d) )”

instance sord_defined : 𝚺₁-Function₁ (sord : V → V) via sordDef := .mk fun v ↦ by
  simp [sordDef, sord, zTag_defined.iff, zRest_defined.iff, pi₁_defined.iff, pi₂_defined.iff,
    iord_defined.iff]
  by_cases h7 : zTag (v 1) = 7
  · simp [h7, numeral_eq_natCast]
  · by_cases h8 : zTag (v 1) = 8
    · simp [h7, h8, numeral_eq_natCast]
    · by_cases h9 : zTag (v 1) = 9 <;> simp [h7, h8, h9, numeral_eq_natCast]

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

/-- **ε₀-code max** via `icmp` (`icmp a b = 0 ⟺ a ≺ b`): `imax a b = b` if `a ≺ b`, else `a`. -/
noncomputable def imax (a b : V) : V := if icmp a b = 0 then b else a

/-- **Max of two ordinals each `≺ α` is `≺ α`** — the linear-order fact (no additive-principality of `α`).
`imax a b ∈ {a, b}`, and both are `≺ α`, so `imax a b ≺ α`. This is what lets the cut-reduct's stored
ordinal (the max of its premises') drop strictly below the cut's `α` for an ARBITRARY stored `α`. -/
theorem icmp_imax_lt {a b α : V} (ha : icmp a α = 0) (hb : icmp b α = 0) :
    icmp (imax a b) α = 0 := by
  unfold imax; split <;> assumption

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
