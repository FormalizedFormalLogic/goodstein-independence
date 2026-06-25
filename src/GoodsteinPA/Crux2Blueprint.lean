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
import GoodsteinPA.Zsubst
import GoodsteinPA.Reduction

namespace GoodsteinPA.InternalZ

open Classical
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.HierarchySymbol ISigma1 PeanoMinus
open LO.FirstOrder.Arithmetic.Bootstrapping
open GoodsteinPA.InternalONote

variable {V : Type*} [ORingStructure V] [V ⊧ₘ* 𝗜𝚺₁]

/-! ## M1a — the genuine validity-faithful reduct `red` + construction correctness
Buchholz §6 `red` / Def 3.2: a 5-case primrec dispatch on the tag; the critical/`K`-case builds the
auxiliaries `d{0},d{1}` per 3.2(5.1) from the redex `inference_critical_pair` (L3.1) and the rank bound
`inference_critical_pair_rank` (T3.4(a)) — both already in `InternalZ`. -/

/- **M1a — DONE.** The genuine reduct `red` (5-case tag dispatch; critical `K`-case = `iRcritG`, the
genuine recombination on correct reduced endsequents) is now defined + `𝚺₁`-definable in `InternalZ`,
with per-rule recursion equations (`red_zAtom`/`red_zIall`/`red_zIneg`/`red_zInd`/`red_zAxAll`/`red_zAxNeg`/
`red_zK`). The placeholder def is removed — `red` is `InternalZ.red`. -/

/-- **M1a — DONE (route B, lap 96).** `red` preserves the end-sequent on the chain-reduct rules
(`Ind`, `K`) of a `∅→⊥` derivation. With the conclusion-reducing `iRKr` the chain `K`-case keeps `Π`
only when the selected premise is `Rep`; on the ⊥-orbit that holds by Cor 2.1
(`InternalZ.fstIdx_red_of_emptyAnt_botSucc`). -/
theorem fstIdx_red {d : V} (hd : ZDerivation d)
    (hant : seqAnt (fstIdx d) = (∅ : V)) (hsucc : seqSucc (fstIdx d) = (^⊥ : V))
    (htag : zTag d = 3 ∨ zTag d = 4) :
    fstIdx (red d) = fstIdx d := fstIdx_red_of_emptyAnt_botSucc hd hant hsucc htag

/-! ## M1b — `RedSound` for `red`: validity as the parallel-induction invariant
Buchholz Thm 3.4(b) / Thm 6.2: principal sequent ⊆ Γ, cut-rank `< m`. Proved as a SEPARATE simultaneous
induction over the same `red` (not recovered post-hoc from the ordinal side) — threading the banked
`zKValidFDef` (faithful validity). This is the cut-elimination core; everything downstream is plumbing. -/

/-! ### `redSound` decomposed: structural induction skeleton + two precise validity residuals

`redSound` is the genuine cut-elimination soundness. We prove the GENERAL form
`redSoundGen : ∀ d, ZDerivation d → ZDerivation (red d)` by `zDerivation_induction`; the seven `ZPhi`
disjuncts split as:

* **atom / Ax∀ / Ax¬** (`red = d`): rebuilt directly from the disjunct via `zDerivation_iff.mpr`.
* **I∀ / I¬** (`red = d₀`, the premise): the immediate sub-derivation, from the IH.
* **Ind** (`red = zK s (irk p) (iIndReductSeq d₀ d₁ 1)`): a chain whose premises are the Ind premises
  (`znth_iIndReductSeq_ZDerivation`); a genuine `ZDerivation` once the produced chain is valid — the
  residual `zKValid_iIndReduct_of_zInd` (Buchholz Thm 3.4, Ind case).
* **K** (`red = iRK …`, the 5.1/5.2.1/5.2.2 dispatch): the genuine recombination is a `ZDerivation`
  given every premise reduct `red dᵢ` is — the residual `ZDerivation_red_zK` (Buchholz Thm 3.4, K case;
  the heart of cut-elimination).

This splits the single fat `redSound` `sorry` into exactly the two deep Buchholz-3.4 validity facts. -/

/-- **Residual (Ind case of Buchholz Thm 3.4).** The Ind-reduct chain `zK s (irk p) (iIndReductSeq d₀ d₁ 1)`
of a valid `Ind` inference is FAITHFULLY valid (`zKValidF`, no criticality). The chain's `Seq` structure
and per-premise derivability are free (`znth_iIndReductSeq_ZDerivation`); this is the validity-threading
obligation. (Stated at `zKValidF` not `zKValid`: the reduct chain need not be critical.) -/
theorem zKValidF_iIndReduct_of_zInd {s at' p d0 d1 : V}
    (hZ : ZDerivation (zInd s at' p d0 d1)) :
    zKValidF s (irk p) (iIndReductSeq d0 d1 1) := sorry

/-! ### Branch recursion equations for the tag-4 dispatch (table lookups resolved to `red dᵢ`)

`red (zK s r ds) = iRK (zK s r ds) (redTable …)` dispatches on two `permIdx` sentinels. These three
equations resolve the `redTable` lookups to `red dᵢ` (via `znth_redTable_eq_red`, exactly as `red_zK_crit`
does for the 5.1 branch), so each branch is stated over the genuine per-premise reduct the IH supplies. -/

-- (`red_zK_rep` / `red_zK_splice` / `red_zK_rep_nonchain` now live in `Zsubst.lean` and are imported;
-- the former local copies here were removed to avoid duplicate declarations once Crux2Blueprint imports
-- `GoodsteinPA.Zsubst` for the route-B regularity threading.)

/-- **5.1 critical sub-residual.** When the chain is critical, `red = iRcritG d ρ` with `ρ` the recursive
premise reducts; delegates to `ZDerivation_iRcritG_of` (R2 = the two genuine auxiliaries are derivations
of their reduced endsequents). -/
theorem ZDerivation_red_zK_crit {s r ds : V}
    (hZ : ZDerivation (zK s r ds))
    (hred : ∀ i < lh ds, ZDerivation (red (znth ds i)))
    (h1 : ¬ permIdx (zK s r ds) < lh ds) :
    ZDerivation (iRcritG (zK s r ds) (fun n => zAxReduct (red (znth ds n)))) := sorry

/-- **`tp` is `Rep` off the I/Ax tags.** `tp d = isymRep` whenever `zTag d ∉ {1,2,5,6}` (i.e. `d` is an
atom/Ind/chain). -/
theorem tp_eq_isymRep_of_zTag {d : V}
    (h : zTag d ≠ 1 ∧ zTag d ≠ 2 ∧ zTag d ≠ 5 ∧ zTag d ≠ 6) : tp d = isymRep := by
  unfold tp; rw [if_neg h.1, if_neg h.2.1, if_neg h.2.2.1, if_neg h.2.2.2]

/-- **`red` of a `Rep` derivation preserves the endsequent and stays `Rep`.** For `tp v = isymRep`
(i.e. `v` an atom/Ind/chain), Buchholz's `tp(v) = Rep ⟹ v[0] ⊢ end(v)`: `red v` keeps `fstIdx` and is
again a `Rep` derivation. **Route B (lap 96):** for the chain case the conclusion-reducing `iRKr` keeps
`Π` only when the selected premise is `Rep`, supplied by `hsel` (vacuous for atom/Ind; on the ⊥-orbit it
holds by Cor 2.1). This is the local faithfulness fact behind case 5.2.2 keeping the conclusion `Π`. -/
theorem red_rep_of_tp_isymRep {v : V} (hZ : ZDerivation v) (htp : tp v = isymRep)
    (hsel : zTag v = 4 → permIdx v < lh (zKseq v) →
      tp (znth (zKseq v) (permIdx v)) = isymRep) :
    fstIdx (red v) = fstIdx v ∧ tp (red v) = isymRep := by
  rcases zDerivation_iff.mp hZ with ⟨s, rfl, _⟩ | ⟨s, a, p, d0, rfl, _, _⟩ | ⟨s, p, d0, rfl, _, _⟩ |
    ⟨s, at', p, d0, d1, rfl, _, _⟩ | ⟨s, r, ds, rfl, _, _, _⟩ |
    ⟨s, p, k, rfl, _, _⟩ | ⟨s, p, rfl, _, _⟩
  · exact ⟨by rw [red_zAtom], by rw [red_zAtom, tp_zAtom]⟩
  · exact absurd htp (by rw [tp_zIall]; exact isymR_ne_isymRep _)
  · exact absurd htp (by rw [tp_zIneg]; exact isymR_ne_isymRep _)
  · refine ⟨by rw [red_zInd, iRInd_zInd, fstIdx_zK, fstIdx_zInd], ?_⟩
    rw [red_zInd, iRInd_zInd, tp_zK]
  · refine ⟨?_, ?_⟩
    · rw [red_zK]; exact fstIdx_iRK_of_Rep (fun h1 _ => hsel (by simp) h1)
    · rw [red_zK]
      exact tp_eq_isymRep_of_zTag (by rw [zTag_iRK]; refine ⟨?_, ?_, ?_, ?_⟩ <;> simp)
  · exact absurd htp (by rw [tp_zAxAll]; exact isymLk_ne_isymRep _ _)
  · exact absurd htp (by rw [tp_zAxNeg]; exact isymLk_ne_isymRep _ _)

/-- From `tp v = isymRep`, the I/Ax tags are excluded. -/
theorem zTag_not_iAx_of_tp_isymRep {v : V} (h : tp v = isymRep) :
    zTag v ≠ 1 ∧ zTag v ≠ 2 ∧ zTag v ≠ 5 ∧ zTag v ≠ 6 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro ht <;> simp only [tp, ht] at h <;> simp at h

-- (`tp_isymRep_of_emptyAnt_botSucc` — Buchholz Cor 2.1 — was promoted to `InternalZ` this lap, where
-- the route-B `fstIdx_red_of_emptyAnt_botSucc` consumes it; the duplicate copy is removed.)

/-- **5.2.2 replace sub-residual — PROVED for a `Rep` selected premise whose own reduct keeps its
endsequent.** Route B (lap 96): `red (zK s r ds)` now emits the reduced conclusion `tpReduce (tp dᵢ) Π 0`;
for a `Rep` selected premise (`htp`) `tpReduce` is the identity, so the goal collapses to the keep-`Π`
`iCritAux` form. Validity then needs `red dᵢ` to keep `dᵢ`'s endsequent and own-permissibility
(`hredfst`/`hredtp` — the route-B conclusion-tracking IH, `red_rep_of_tp_isymRep` instantiated for `dᵢ`),
so `ZDerivation_iCritAux_of` applies. `hredfst`/`hredtp` are the route-B invariant supplied by the
`redSoundF` induction; on the ⊥-orbit they hold hereditarily by Cor 2.1. -/
theorem ZDerivation_red_zK_replace {s r ds : V}
    (hZ : ZDerivation (zK s r ds))
    (hred : ∀ i < lh ds, ZDerivation (red (znth ds i)))
    (h1 : permIdx (zK s r ds) < lh ds)
    (htp : tp (znth ds (permIdx (zK s r ds))) = isymRep)
    (hredfst : fstIdx (red (znth ds (permIdx (zK s r ds)))) = fstIdx (znth ds (permIdx (zK s r ds))))
    (hredtp : tp (red (znth ds (permIdx (zK s r ds)))) = isymRep) :
    ZDerivation (zK (tpReduce (tp (znth ds (permIdx (zK s r ds)))) s 0) r
      (seqUpdate ds (permIdx (zK s r ds)) (red (znth ds (permIdx (zK s r ds)))))) := by
  set i := permIdx (zK s r ds) with hi_def
  rw [htp, tpReduce_isymRep]
  have hgoal : zK s r (seqUpdate ds i (red (znth ds i)))
      = iCritAux (zK s r ds) i (red (znth ds i)) := by rw [iCritAux_zK]
  rw [hgoal]
  obtain ⟨_, hmem⟩ := zDerivation_zK_inv hZ
  have hZv : ZDerivation (red (znth ds i)) := hred i h1
  obtain ⟨hne1, hne2, hne5, hne6⟩ := zTag_not_iAx_of_tp_isymRep hredtp
  exact ZDerivation_iCritAux_of h1 hZ hZv hredfst
    (by rw [hredtp]; exact iperm_isymRep _)
    (fun h => absurd h hne1) (fun h => absurd h hne2)
    (fun h => absurd h hne5) (fun h => absurd h hne6)

/-- **5.2.1 splice sub-residual. ⚠ FALSE as stated** (lap-90 finding): needs `tp dᵢ = isymRep` AND `dᵢ`
critical (so `red dᵢ = iRcritG dᵢ …` genuinely has the two reduct-halves `znth (zKseq (red dᵢ)) {0,1}`).
For a non-`Rep` `dᵢ` the halves are junk. Holds on the ⊥-orbit. Delegates (under the restriction) to
`ZDerivation_seqInsert_of_zK` with the spliced `isChainInf` at rank `max(rk(A), r)`. -/
theorem ZDerivation_red_zK_splice {s r ds : V}
    (hZ : ZDerivation (zK s r ds))
    (hred : ∀ i < lh ds, ZDerivation (red (znth ds i)))
    (h1 : permIdx (zK s r ds) < lh ds)
    (h2 : ¬ permIdx (znth ds (permIdx (zK s r ds)))
        < lh (zKseq (znth ds (permIdx (zK s r ds))))) :
    ZDerivation (zK s
        (max (irk (seqSucc (fstIdx
          (znth (zKseq (red (znth ds (permIdx (zK s r ds))))) 0)))) r)
        (seqInsert ds (permIdx (zK s r ds))
          (znth (zKseq (red (znth ds (permIdx (zK s r ds))))) 0)
          (znth (zKseq (red (znth ds (permIdx (zK s r ds))))) 1))) := sorry

/-- **I∀ non-`Rep` replace — FULLY ASSEMBLED modulo the orbit invariants (lap 99).** The capstone proving
the validity infrastructure SUFFICES for the hardest non-`Rep` case: when the selected premise `dᵢ = znth ds
i` is an I∀ node (`zIall sᵢ a p d0`), the genuine reduct `red dᵢ = zsubst d0 a 0` (deriving `Γ→F(0)`) feeds
`ZDerivation_iCritReplaceReduce_of` to produce the conclusion-reduced chain `zK (tpReduce (tp dᵢ) s 0) r
(seqUpdate ds i (red dᵢ))`. EVERYTHING is discharged from banked lemmas — `red_zIall_tpReduce` (the I∀
conclusion-tracking, needs the O3 freshness `hpfresh`/`hΓfresh`), `iperm_tp_fstIdx_of_ZDerivation` +
`tag_uformula_of_ZDerivation` (the reduct's own well-formedness), `seqAnt_seqSetSucc`/`seqSucc_seqSetSucc`.
The ONLY un-discharged inputs are the genuine orbit data: O3 freshness (`hpfresh`/`hΓfresh`), the threading/
rank up to `i` (`hthread`/`hrank`, from `permIdx ≤ j₀`), and the reduced succedent well-formedness
(`hsucc_wff`) — exactly what the strengthened `redSoundGen` motive must supply (PENDING_WORK lap-99 path A).
This DE-RISKS the entire non-`Rep` route: the I∀ case is mechanically complete given the invariants. -/
theorem ZDerivation_zK_replace_zIall_of {s r ds i sᵢ a p d0 : V}
    (hZ : ZDerivation (zK s r ds)) (hi : i < lh ds)
    (hdi : znth ds i = zIall sᵢ a p d0)
    (hZred : ZDerivation (red (zIall sᵢ a p d0)))
    (hpfresh : fvSubst ℒₒᵣ a (Bootstrapping.Arithmetic.numeral 0) p = p)
    (hΓfresh : fvSubstSeq a (Bootstrapping.Arithmetic.numeral 0) (seqAnt sᵢ) = seqAnt sᵢ)
    (hsucc_wff : IsUFormula ℒₒᵣ (substs1 ℒₒᵣ (Bootstrapping.Arithmetic.numeral 0) p))
    (hthread : ∀ i' ≤ i, ∀ B, inAnt B (chainAnt ds i') →
        inAnt B (seqAnt s) ∨ ∃ i'' < i', B = chainAsucc ds i'')
    (hrank : ∀ i' < i, irk (chainAsucc ds i') ≤ r) :
    ZDerivation (zK (tpReduce (tp (znth ds i)) s 0) r (seqUpdate ds i (red (znth ds i)))) := by
  have hZdi : ZDerivation (zIall sᵢ a p d0) := hdi ▸ (zDerivation_zK_inv hZ).2 i hi
  have htrack : fstIdx (red (zIall sᵢ a p d0))
      = seqSetSucc sᵢ (substs1 ℒₒᵣ (Bootstrapping.Arithmetic.numeral 0) p) := by
    rw [red_zIall_tpReduce hZdi hpfresh hΓfresh, tp_zIall, fstIdx_zIall, tpReduce_isymR_all]
  have hchain_i : chainAnt ds i = seqAnt sᵢ := by
    unfold chainAnt; rw [hdi, fstIdx_zIall]
  rw [hdi, tp_zIall, tpReduce_isymR_all]
  refine ZDerivation_iCritReplaceReduce_of hi hZ hZred ?_ ?_ ?_ hthread hrank ?_ ?_ ?_ ?_ ?_ ?_
  · rw [htrack, seqAnt_seqSetSucc, ← hchain_i]
  · rw [htrack, seqSucc_seqSetSucc, seqSucc_seqSetSucc]
  · rw [seqAnt_seqSetSucc]
  · rw [seqSucc_seqSetSucc]; exact hsucc_wff
  · exact iperm_tp_fstIdx_of_ZDerivation hZred
  · exact (tag_uformula_of_ZDerivation hZred).1
  · exact (tag_uformula_of_ZDerivation hZred).2.1
  · exact (tag_uformula_of_ZDerivation hZred).2.2.1
  · exact (tag_uformula_of_ZDerivation hZred).2.2.2

/-- **I¬ non-`Rep` replace — FULLY ASSEMBLED modulo the orbit invariants (lap 100).** The I¬ analogue of
`ZDerivation_zK_replace_zIall_of`: when the selected premise `dᵢ = zIneg sᵢ p d0` is an I¬ node, the
genuine reduct `red dᵢ = d0` (Buchholz Def 3.2 clause 3 — `d[0] := d₀`, **no** substitution, unlike I∀)
derives `p,Γ→⊥`, which IS the reduced sequent `tpReduce (R_¬p) Π 0 = p,Γ→⊥` (antecedent gains the cut
formula `p`, succedent → `⊥`). It feeds the unifying `ZDerivation_iCritReplaceReduce_general` (membership-
form `isChainInf`, since here the antecedent GROWS rather than being kept) to produce the conclusion-reduced
chain `zK (tpReduce (tp dᵢ) s 0) r (seqUpdate ds i (red dᵢ))`. EVERYTHING is discharged from banked lemmas
(`isChainInf_reduceR_membership`, `inAnt_seqAddAnt`, `forall_IsUFormula_seqCons`,
`iperm_tp_fstIdx_of_ZDerivation` + `tag_uformula_of_ZDerivation` for the reduct's wff). The ONLY
un-discharged inputs are the genuine orbit data: the faithful premise-antecedent `hd0ant`
(`seqAnt (fstIdx d0) = seqCons (seqAnt sᵢ) p` — the I¬ analogue of I∀'s O3 freshness; `zInegWff` pins only
`p ∈ antecedent`), the conclusion `Seq`-wellformedness (`hSeqs`/`hSeqsi`), and the threading/rank up to `i`
(`hthread`/`hrank`, from `permIdx ≤ j₀`) — exactly what the strengthened `redSoundGen` motive must supply.
This DE-RISKS the I¬ branch: it is mechanically complete given the invariants. -/
theorem ZDerivation_zK_replace_zIneg_of {s r ds i sᵢ p d0 : V}
    (hZ : ZDerivation (zK s r ds)) (hi : i < lh ds)
    (hdi : znth ds i = zIneg sᵢ p d0)
    (hd0ant : seqAnt (fstIdx d0) = seqCons (seqAnt sᵢ) p)
    (hSeqs : Seq (seqAnt s)) (hSeqsi : Seq (seqAnt sᵢ))
    (hthread : ∀ i' ≤ i, ∀ B, inAnt B (chainAnt ds i') →
        inAnt B (seqAnt s) ∨ ∃ i'' < i', B = chainAsucc ds i'')
    (hrank : ∀ i' < i, irk (chainAsucc ds i') ≤ r) :
    ZDerivation (zK (tpReduce (tp (znth ds i)) s 0) r (seqUpdate ds i (red (znth ds i)))) := by
  have hZdi : ZDerivation (zIneg sᵢ p d0) := hdi ▸ (zDerivation_zK_inv hZ).2 i hi
  obtain ⟨hZd0, _hsucceq, hbot, hmem, hp⟩ := zDerivation_zIneg_inv hZdi
  have hSeqs' : Seq (seqAnt (seqSetSucc s (^⊥ : V))) := by rw [seqAnt_seqSetSucc]; exact hSeqs
  have hchain_i : chainAnt ds i = seqAnt sᵢ := by unfold chainAnt; rw [hdi, fstIdx_zIneg]
  -- conclusion-antecedent wff of the parent chain (`zKValidF` field 9)
  obtain ⟨-, -, -, -, -, -, -, -, hsa⟩ := zKValidF_of_ZDerivation_zK hZ
  rw [hdi, tp_zIneg, tpReduce_isymR_neg p s 0 hp, red_zIneg]
  refine ZDerivation_iCritReplaceReduce_general hi hZ hZd0 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- the membership-form `isChainInf` for the reduced conclusion `p,Γ→⊥`
    refine isChainInf_reduceR_membership hi (Or.inr hbot) ?_ ?_ hrank
    · -- at-`i` antecedent threading: `B ∈ seqAnt (fstIdx d0) = (seqAnt sᵢ),p`
      intro B hB
      rw [hd0ant] at hB
      rcases (inAnt_seqCons hSeqsi).mp hB with rfl | hBin
      · left; exact (inAnt_seqAddAnt hSeqs').mpr (Or.inl rfl)
      · rcases hthread i le_rfl B (by rw [hchain_i]; exact hBin) with hins | hex
        · left; exact (inAnt_seqAddAnt hSeqs').mpr (Or.inr (by rw [seqAnt_seqSetSucc]; exact hins))
        · right; exact hex
    · -- below-`i` antecedent threading inherits, weakened through the new antecedent
      intro i' hi' B hB
      rcases hthread i' (le_of_lt hi') B hB with hins | hex
      · left; exact (inAnt_seqAddAnt hSeqs').mpr (Or.inr (by rw [seqAnt_seqSetSucc]; exact hins))
      · right; exact hex
  · -- conclusion succedent wff: `⊥`
    rw [seqSucc_seqAddAnt, seqSucc_seqSetSucc]; simp
  · -- conclusion antecedent wff: `(seqAnt s),p`, each entry a `UFormula`
    rw [seqAnt_seqAddAnt, seqAnt_seqSetSucc]
    exact forall_IsUFormula_seqCons hSeqs hsa hp
  · -- reduct succedent wff: `⊥`
    rw [hbot]; simp
  · exact iperm_tp_fstIdx_of_ZDerivation hZd0
  · exact (tag_uformula_of_ZDerivation hZd0).1
  · exact (tag_uformula_of_ZDerivation hZd0).2.1
  · exact (tag_uformula_of_ZDerivation hZd0).2.2.1
  · exact (tag_uformula_of_ZDerivation hZd0).2.2.2

/-- **axAll non-`Rep` replace — FULLY ASSEMBLED modulo the orbit invariants (lap 100).** The §5-∀-axiom
analogue, and the **cleanest** of the four: when the selected premise `dᵢ = zAxAll sᵢ p k` is a §5 left
∀-axiom, the reduct is the IDENTITY (`red dᵢ = dᵢ`, Buchholz Def 3.2 case 5.2.2 axiom case — no premise
change), so `seqUpdate ds i (red dᵢ) = ds`, and the conclusion gains the cut-formula instance `F(k) =
substs1 (numeral k) p` in its ANTECEDENT (`tpReduce (L^k_{∀p}) Π 0 = F(k),Γ→D`). The validity is pure
conclusion-antecedent monotonicity (`ZDerivation_zK_seqAddAnt`) — the threading only RELAXES, so **no
`i ≤ j₀` threading datum is needed** (unlike I∀/I¬). The only un-discharged inputs are the conclusion
`Seq`-wellformedness (`hSeqs`) and the cut-instance formula-hood (`hAwff`, the orbit/wff datum the
strengthened `redSoundGen` motive supplies). -/
theorem ZDerivation_zK_replace_zAxAll_of {s r ds i sᵢ p k : V}
    (hZ : ZDerivation (zK s r ds)) (hi : i < lh ds)
    (hdi : znth ds i = zAxAll sᵢ p k)
    (hSeqs : Seq (seqAnt s))
    (hAwff : IsUFormula ℒₒᵣ (substs1 ℒₒᵣ (Bootstrapping.Arithmetic.numeral k) p)) :
    ZDerivation (zK (tpReduce (tp (znth ds i)) s 0) r (seqUpdate ds i (red (znth ds i)))) := by
  have hds : Seq ds := (zDerivation_zK_inv hZ).1
  have hred_eq : red (znth ds i) = znth ds i := by rw [hdi, red_zAxAll]
  have htp_eq : tpReduce (tp (znth ds i)) s 0
      = seqAddAnt (substs1 ℒₒᵣ (Bootstrapping.Arithmetic.numeral k) p) s := by
    rw [hdi, tp_zAxAll, tpReduce_isymLk_all]
  rw [hred_eq, seqUpdate_znth_self hds hi, htp_eq]
  exact ZDerivation_zK_seqAddAnt hZ hSeqs hAwff

/-- **The non-`Rep` replace dispatch, FULLY ASSEMBLED for 3/4 tags (lap 100).** Routes the non-chain,
non-`Rep` selected premise `dᵢ = znth ds (permIdx)` by its node tag into the matching banked capstone:
`zIall`→`ZDerivation_zK_replace_zIall_of`, `zIneg`→`_zIneg_of`, `zAxAll`→`_zAxAll_of`. The atom/Ind tags
are excluded by `htp` (their `tp = isymRep`), the chain tag by `htag`. The per-tag orbit invariants
(freshness/faithful-antecedent/wff) are supplied as the bundled hypotheses `hIall`/`hIneg`/`hAxAll`
(conditioned on the node shape, so the caller proves only the branch that fires), the conclusion `Seq`-wff
as `hSeqs`, and the selection-bounded threading/rank as `hthread`/`hrank` (from `permIdx_le_of_isPermPrem`
+ `thread_rank_restrict_of_le`). **axNeg (tag 6) is the lone residual** (`sorry`, Path C): its reduct is a
succedent REPLACEMENT (`Γ→p`) with no premise carrying succedent `p`, so the membership-`isChainInf` route
does not apply — it needs Buchholz's genuine ¬-axiom cut (premise restructuring). This lemma DISCHARGES the
non-`Rep` branch of `ZDerivation_red_zK` modulo (a) the orbit-invariant bundle and (b) axNeg. -/
theorem ZDerivation_red_zK_nonRep {s r ds : V}
    (hZ : ZDerivation (zK s r ds))
    (hred : ∀ i < lh ds, ZDerivation (red (znth ds i)))
    (h1 : permIdx (zK s r ds) < lh ds)
    (htag : zTag (znth ds (permIdx (zK s r ds))) ≠ 4)
    (htp : ¬ tp (znth ds (permIdx (zK s r ds))) = isymRep)
    (hSeqs : Seq (seqAnt s))
    (hthread : ∀ i' ≤ permIdx (zK s r ds), ∀ B, inAnt B (chainAnt ds i') →
        inAnt B (seqAnt s) ∨ ∃ i'' < i', B = chainAsucc ds i'')
    (hrank : ∀ i' < permIdx (zK s r ds), irk (chainAsucc ds i') ≤ r)
    (hIall : ∀ sᵢ a p d0, znth ds (permIdx (zK s r ds)) = zIall sᵢ a p d0 →
        fvSubst ℒₒᵣ a (Bootstrapping.Arithmetic.numeral 0) p = p ∧
        fvSubstSeq a (Bootstrapping.Arithmetic.numeral 0) (seqAnt sᵢ) = seqAnt sᵢ ∧
        IsUFormula ℒₒᵣ (substs1 ℒₒᵣ (Bootstrapping.Arithmetic.numeral 0) p))
    (hIneg : ∀ sᵢ p d0, znth ds (permIdx (zK s r ds)) = zIneg sᵢ p d0 →
        seqAnt (fstIdx d0) = seqCons (seqAnt sᵢ) p ∧ Seq (seqAnt sᵢ))
    (hAxAll : ∀ sᵢ p k, znth ds (permIdx (zK s r ds)) = zAxAll sᵢ p k →
        IsUFormula ℒₒᵣ (substs1 ℒₒᵣ (Bootstrapping.Arithmetic.numeral k) p)) :
    ZDerivation (zK (tpReduce (tp (znth ds (permIdx (zK s r ds)))) s 0) r
      (seqUpdate ds (permIdx (zK s r ds)) (red (znth ds (permIdx (zK s r ds)))))) := by
  have hdiZ : ZDerivation (znth ds (permIdx (zK s r ds))) := (zDerivation_zK_inv hZ).2 _ h1
  rcases zDerivation_iff.mp hdiZ with ⟨s', heq, _⟩ | ⟨s', a, p, d0, heq, _, _, _⟩ |
    ⟨s', p, d0, heq, _, _, _⟩ | ⟨s', at', p, d0, d1, heq, _, _, _⟩ | ⟨s', r', ds', heq, _, _, _⟩ |
    ⟨s', p, k, heq, _, _⟩ | ⟨s', p, heq, _, _⟩
  · exact absurd (by rw [heq]; exact tp_zAtom s') htp
  · obtain ⟨hpfresh, hΓfresh, hsucc_wff⟩ := hIall s' a p d0 heq
    exact ZDerivation_zK_replace_zIall_of hZ h1 heq (heq ▸ hred _ h1)
      hpfresh hΓfresh hsucc_wff hthread hrank
  · obtain ⟨hd0ant, hSeqsi⟩ := hIneg s' p d0 heq
    exact ZDerivation_zK_replace_zIneg_of hZ h1 heq hd0ant hSeqs hSeqsi hthread hrank
  · exact absurd (by rw [heq]; exact tp_zInd s' at' p d0 d1) htp
  · exact absurd (by rw [heq, zTag_zK]) htag
  · exact ZDerivation_zK_replace_zAxAll_of hZ h1 heq hSeqs (hAxAll s' p k heq)
  · -- axNeg (Path C residual): succedent-replacement `Γ→p`, needs Buchholz's ¬-axiom cut. OPEN.
    sorry

/-- **Residual (K case of Buchholz Thm 3.4 — the cut-elimination core).** The genuine reduct `red` of a
valid chain `zK s r ds` is again a `ZDerivation`, given that the reduct of every premise is. Dispatches
(via `red_zK_crit` / `red_zK_rep` / `red_zK_splice`) into the three Buchholz case-5 sub-residuals; each
delegates to a banked validity constructor (`ZDerivation_iRcritG_of` / `ZDerivation_iCritAux_of_zK` /
`ZDerivation_seqInsert_of_zK`). -/
theorem ZDerivation_red_zK {s r ds : V}
    (hZ : ZDerivation (zK s r ds))
    (hred : ∀ i < lh ds, ZDerivation (red (znth ds i))) :
    ZDerivation (red (zK s r ds)) := by
  by_cases h1 : permIdx (zK s r ds) < lh ds
  · -- non-critical chain: dispatch on the GATED `iRK` (lap 95) — first on whether the selected
    -- premise `dᵢ` is a chain (`zTag dᵢ = 4`), then on `dᵢ`'s own criticality
    by_cases htag : zTag (znth ds (permIdx (zK s r ds))) = 4
    · by_cases h2 : permIdx (znth ds (permIdx (zK s r ds)))
          < lh (zKseq (znth ds (permIdx (zK s r ds))))
      · -- chain selected premise, non-critical → 5.2.2 replace (route-B reduced conclusion).
        rw [red_zK_rep h1 h2]
        -- OPEN (route-B residual): `ZDerivation_red_zK_replace` discharges this from the selected
        -- premise being `Rep` (`tp dᵢ = isymRep`, ⊥-orbit Cor 2.1) PLUS the conclusion-tracking IH
        -- `fstIdx (red dᵢ) = fstIdx dᵢ ∧ tp (red dᵢ) = isymRep`. Those come from the `redSoundF`
        -- induction (next lap); here they are the open ⊥-orbit invariant.
        sorry
      · -- chain selected premise, critical → 5.2.1 splice (`htag` supplies the genuine reduct-halves)
        rw [red_zK_splice h1 h2 htag]
        exact ZDerivation_red_zK_splice hZ hred h1 h2
    · -- NON-chain selected premise → 5.2.2 replace with conclusion-reduction `tpReduce (tp dᵢ) Π n`.
      -- (Lap-95 GATED dispatch — the OLD `iRK` mis-spliced here.) The deep validity residual:
      -- a keep-Π replace is faithful only for `tp = Rep`, so the conclusion must reduce (lap-90).
      rw [red_zK_rep_nonchain h1 htag]
      by_cases htp : tp (znth ds (permIdx (zK s r ds))) = isymRep
      · -- atom / Ind: `tp dᵢ = Rep`, `tpReduce` is the identity, conclusion `Π` KEPT. The premise
        -- reduct keeps its endsequent + stays `Rep` (`red_rep_of_tp_isymRep`, with `hsel` vacuous since
        -- `zTag dᵢ ≠ 4`), so the keep-`Π` `ZDerivation_red_zK_replace` discharges it. (Lap 99.)
        have hdiZ : ZDerivation (znth ds (permIdx (zK s r ds))) := (zDerivation_zK_inv hZ).2 _ h1
        obtain ⟨hredfst, hredtp⟩ := red_rep_of_tp_isymRep hdiZ htp (fun h4 _ => absurd h4 htag)
        exact ZDerivation_red_zK_replace hZ hred h1 htp hredfst hredtp
      · -- I∀ / I¬ / axAll / axNeg: genuinely conclusion-reducing (`tp dᵢ ≠ Rep`). The validity
        -- constructors are banked (`ZDerivation_iCritReplaceReduce_of` for I∀/I¬,
        -- `ZDerivation_zK_seqAddAnt` for axAll, axNeg residual); the OPEN data is the O3 eigenvariable
        -- freshness (`red_zIall_tpReduce`) + the conclusion `Seq`/wff, threaded by the strengthened
        -- `redSoundGen` motive (PENDING_WORK lap-99 path A). The `permIdx ≤ j₀` threading is banked
        -- (`permIdx_le_of_isPermPrem`).
        sorry
  · -- 5.1 critical
    rw [red_zK_crit h1]
    exact ZDerivation_red_zK_crit hZ hred h1

/-- **`redSound`, general form. ⚠ FALSE IN FULL GENERALITY — scaffold only.** See
`ANALYSIS-2026-06-25-lap90-red-faithful-only-for-rep.md`: the repo's `red` keeps the chain conclusion
`Π` (`fstIdx_iRK = fstIdx d`), so it equals Buchholz's `d[0]` only when `tp(d) = Rep`. For a chain whose
minimal-permissible premise `dᵢ` is an I-rule/axiom (`tp(dᵢ) ≠ Rep`), Buchholz 5.2.2 reduces the
conclusion to `tp(dᵢ)(Π,0) ≠ Π`, so the repo's `red` is unfaithful and `red d` is not a `ZDerivation`.
The TRUE target is `redSound` over `ZDerivesEmpty` (the ⊥-orbit, all-`Rep` by Cor 2.1). The 5 trivial
cases below + `red_zK_rep`/`red_zK_splice` are reusable; the two deep cases are the open frontier. -/
theorem redSoundGen : ∀ d : V, ZDerivation d → ZRegular d → ZDerivation (red d) := by
  have key : ∀ d : V, ZDerivation d → (ZRegular d → ZDerivation (red d)) := by
    apply zDerivation_induction (P := fun d : V => ZRegular d → ZDerivation (red d))
    · definability
    · intro C hC d hphi hreg
      rcases hphi with ⟨s, rfl, hin⟩ | ⟨s, a, p, d0, rfl, hd0, hsucc, hwff⟩ |
        ⟨s, p, d0, rfl, hd0, hsucc, hwff⟩ |
        ⟨s, at', p, d0, d1, rfl, hd0, hd1, hwff⟩ | ⟨s, r, ds, rfl, hds, hmem, hvalid⟩ |
        ⟨s, p, k, rfl, hp, hin⟩ | ⟨s, p, rfl, hp, hin⟩
      · -- zAtom: red = identity
        rw [red_zAtom]; exact zDerivation_iff.mpr (Or.inl ⟨s, rfl, hin⟩)
      · -- zIall: red = zsubst d0 a (numeral 0); regularity ⟹ maxEigen d0 < a ⟹ ZDerivation_zsubst.
        rw [red_zIall]
        rw [ZRegular, zReg_zIall] at hreg
        have hlt : maxEigen d0 < a :=
          ltFlag_eq_zero_iff.mp (nonpos_iff_eq_zero.mp (hreg ▸ le_max_left _ _))
        exact ZDerivation_zsubst (by simp) d0 (hC d0 hd0).1 hlt
      · -- zIneg: red = d0
        rw [red_zIneg]; exact (hC d0 hd0).1
      · -- zInd: red = chain reduct; residual supplies validity
        have hZ : ZDerivation (zInd s at' p d0 d1) := zDerivation_iff.mpr
          (Or.inr (Or.inr (Or.inr (Or.inl
            ⟨s, at', p, d0, d1, rfl, (hC d0 hd0).1, (hC d1 hd1).1, hwff⟩))))
        rw [red_zInd, iRInd_zInd, zDerivation_iff]
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ⟨s, irk p, iIndReductSeq d0 d1 1, rfl, iIndReductSeq_seq d0 d1 1,
            fun i hi => znth_iIndReductSeq_ZDerivation (hC d0 hd0).1 (hC d1 hd1).1 i hi,
            zKValidF_iIndReduct_of_zInd hZ⟩))))
      · -- zK: the dispatch; residual supplies validity-preservation. Premise reducts from the IH,
        -- fed the premise regularity (`ZRegular_zK_premise`) from the chain's own regularity.
        exact ZDerivation_red_zK
          (zDerivation_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
            ⟨s, r, ds, rfl, hds, fun i hi => (hC (znth ds i) (hmem i hi)).1, hvalid⟩))))))
          (fun i hi => (hC (znth ds i) (hmem i hi)).2 (ZRegular_zK_premise hds hreg hi))
      · -- zAxAll: red = identity
        rw [red_zAxAll]; exact zDerivation_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inl ⟨s, p, k, rfl, hp, hin⟩))))))
      · -- zAxNeg: red = identity
        rw [red_zAxNeg]; exact zDerivation_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr ⟨s, p, rfl, hp, hin⟩))))))
  exact key

/-- **The regular ⊥-orbit predicate.** Route B threads eigenvariable regularity (`ZRegular`, O1) alongside
`ZDerivesEmpty`: the genuine reduct `red` does the I∀ eigensubst `zsubst d0 a 0`, which is a `ZDerivation`
only when the node is regular (`maxEigen d0 < a`). The embedding (M2) produces a regular derivation; `red`
preserves both (`ZRegular_red` for O1, `fstIdx_red` for the conclusion). -/
def ZDerivesEmptyR (d : V) : Prop := ZDerivesEmpty d ∧ ZRegular d

/-- **M1b — THE nut.** The `red`-reduct of a contradiction derivation is again a genuine `ZDerivation`.
(Re-pointed `RedSound`, off the dead `iR2`.) A corollary of `redSoundGen`; the regularity comes from the
regular ⊥-orbit (`ZDerivesEmptyR`). -/
theorem redSound : ∀ d : V, ZDerivesEmptyR d → ZDerivation (red d) :=
  fun d h => redSoundGen d h.1.1 h.2

/-- **M1b (descent re-point, one step).** The banked ordinal descent, restated over `red`
(`iR2` analogue: `iord_descent_iR2_of_ZDerivesEmpty`). -/
theorem iord_descent_red {d : V} (hd : ZDerivesEmptyR d) : icmp (iord (red d)) (iord d) = 0 := sorry

/-! ## Connectives — PROVEN from the leaves (this is the "no wiring step" demonstration)
With `redSound` in hand, `ZDerivesEmpty` is closed under the whole `red`-orbit and the ε₀-descent is
**unconditional** — mirrors `ZDerivesEmpty_iterate` / `iord_iR2_iterate_descends`, minus the `RedSound`
hypothesis. Bodies left `sorry` here only because this file is uncompiled; they are pure plumbing copies. -/

/-- **`red` preserves `ZDerivesEmptyR`** (mirror of `ZDerivesEmpty_iR2`, now route-B): a regular
contradiction derivation reduces to one — `redSound` gives `ZDerivation (red d)`, `fstIdx_red` transfers
the empty antecedent + `⊥` succedent, and `ZRegular_red` (O1) preserves regularity. -/
theorem ZDerivesEmptyR_red {d : V} (h : ZDerivesEmptyR d) : ZDerivesEmptyR (red d) := by
  have hfst : fstIdx (red d) = fstIdx d :=
    fstIdx_red h.1.1 h.1.2.1 h.1.2.2 (zTag_Ind_or_K_of_ZDerivesEmpty h.1)
  exact ⟨⟨redSound d h, by rw [hfst]; exact h.1.2.1, by rw [hfst]; exact h.1.2.2⟩,
    ZRegular_red d h.1.1 h.2⟩

/-- `ZDerivesEmptyR` is closed under the `red`-orbit (no hypothesis — `redSound`+`ZRegular_red` discharge it). -/
theorem ZDerivesEmptyR_red_iterate {z : V} (hz : ZDerivesEmptyR z) :
    ∀ n : ℕ, ZDerivesEmptyR (red^[n] z)
  | 0 => by simpa using hz
  | n + 1 => by
      rw [Function.iterate_succ_apply']
      exact ZDerivesEmptyR_red (ZDerivesEmptyR_red_iterate hz n)

/-- **The infinite ε₀-descent of crux-2.** `n ↦ iord (red^[n] z)` strictly `≺`-descends along the regular
⊥-orbit. An infinite primitive-recursive ε₀-descent — exactly what `PRWO(ε₀)` forbids. -/
theorem iord_red_iterate_descends {z : V} (hz : ZDerivesEmptyR z) (n : ℕ) :
    icmp (iord (red^[n+1] z)) (iord (red^[n] z)) = 0 := by
  rw [Function.iterate_succ_apply']
  exact iord_descent_red (ZDerivesEmptyR_red_iterate hz n)

/-! ## M2 — the C0.5 Foundation→Z bridge
`Z ⊇ 𝗣𝗔` on closed sequents, M-internal (Bryce–Goré `Peano.v` blueprint, B1–B3; the PA-induction axiom
maps directly to Z's native `Ind`, skipping their biggest sub-tower). Populates `ZDerivesEmpty` from a
Foundation ⊥-proof. -/

/-- **M2.** A model-internal `𝗣𝗔`-derivation of the (coded) empty/`⊥` sequent yields a `Z`-derivation
of the empty sequent. ⚠️ **Signature to pin against Foundation's coded-provability API:** the confirmed
primitive `Theory.DerivationOf (d s : V) := fstIdx d = s ∧ T.Derivation d` takes a *coded sequent*
`s : V` (here `∅`/the `⊥`-sequent), NOT a `Sentence ℒₒᵣ` (the in-repo doc was loose); the exact
`𝗣𝗔`-internal theory term `T` is the box's to fix (it is what `¬ 𝗣𝗔.Consistent M` unfolds to internally,
cf. `Reduction.peano_not_proves_consistency`). -/
theorem foundation_bot_to_Z_empty {d : V} (hd : (𝗣𝗔 : Theory ℒₒᵣ).Derivation d) (h0 : fstIdx d = ∅) :
    ∃ z : V, ZDerivesEmptyR z := sorry

/-! ## M3 — assemble the Gentzen contradiction
An inconsistency gives a `ZDerivesEmpty` (M2) whose `red`-orbit is an infinite ε₀-descent (M1b ⟹
`iord_red_iterate_descends`), which `PRWO(ε₀)`/well-foundedness forbids. This is the payload that
discharges the deep axiom `GentzenCon.gentzen_descent_of_inconsistent`; the existing `Reduction.lean`
+ `GentzenCon` scaffolding carries it the rest of the way to `goodstein_implies_consistency` and the
headline — no new top-level wiring. -/

/-- **M3.** From a `ZDerivesEmpty` witness, the unconditional ε₀-descent contradicts well-foundedness of
the internal ordinal order — the Gentzen `False`. (Internalize `n ↦ iord (red^[n] z)` as the `Σ₁` graph
`gentzenDescentφ`; the descent is `iord_red_iterate_descends`.) -/
theorem false_of_ZDerivesEmpty {z : V} (hz : ZDerivesEmptyR z) : False := sorry

end GoodsteinPA.InternalZ
