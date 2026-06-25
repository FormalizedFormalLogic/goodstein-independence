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

/-- **5.2.2 replace recursion equation.** Non-critical chain (`permIdx d < lh ds`) whose least-permissible
premise `dᵢ` is itself non-critical (`permIdx dᵢ < lh (zKseq dᵢ)`): `red` replaces premise `i` by its
reduct `red dᵢ`. -/
lemma red_zK_rep {s r ds : V} (h1 : permIdx (zK s r ds) < lh ds)
    (h2 : permIdx (znth ds (permIdx (zK s r ds)))
        < lh (zKseq (znth ds (permIdx (zK s r ds))))) :
    red (zK s r ds)
      = zK (tpReduce (tp (znth ds (permIdx (zK s r ds)))) s 0) r
          (seqUpdate ds (permIdx (zK s r ds)) (red (znth ds (permIdx (zK s r ds))))) := by
  have hbound : znth ds (permIdx (zK s r ds)) ≤ zK s r ds - 1 :=
    le_trans (znth_le_self ds _) (le_pred_of_lt (ds_lt_zK s r ds))
  rw [red_zK, iRK]
  simp only [zKseq_zK]
  rw [if_pos h1, if_neg (by simp [h2]), iRKr, zKseq_zK, fstIdx_zK, zKrank_zK,
    znth_redTable_eq_red _ _ hbound]

/-- **5.2.1 splice recursion equation (lap-95 GATED dispatch).** Non-critical chain whose least-permissible
premise `dᵢ` is itself a CRITICAL CHAIN (`zTag dᵢ = 4` AND `¬ permIdx dᵢ < lh (zKseq dᵢ)`): `red` splices
`dᵢ`'s two reduct-halves `znth (zKseq (red dᵢ)) {0,1}` in place at `i`, rank rising to `max(rk(A), r)`. -/
lemma red_zK_splice {s r ds : V} (h1 : permIdx (zK s r ds) < lh ds)
    (h2 : ¬ permIdx (znth ds (permIdx (zK s r ds)))
        < lh (zKseq (znth ds (permIdx (zK s r ds)))))
    (htag : zTag (znth ds (permIdx (zK s r ds))) = 4) :
    red (zK s r ds)
      = zK s
          (max (irk (seqSucc (fstIdx
            (znth (zKseq (red (znth ds (permIdx (zK s r ds))))) 0)))) r)
          (seqInsert ds (permIdx (zK s r ds))
            (znth (zKseq (red (znth ds (permIdx (zK s r ds))))) 0)
            (znth (zKseq (red (znth ds (permIdx (zK s r ds))))) 1)) := by
  have hbound : znth ds (permIdx (zK s r ds)) ≤ zK s r ds - 1 :=
    le_trans (znth_le_self ds _) (le_pred_of_lt (ds_lt_zK s r ds))
  rw [red_zK, iRK]
  simp only [zKseq_zK]
  rw [if_pos h1, if_pos ⟨htag, h2⟩, iRKs, zKseq_zK, znth_redTable_eq_red _ _ hbound,
    fstIdx_zK, zKrank_zK]

/-- **5.2.2 replace for a NON-CHAIN selected premise (lap-95 GATED dispatch).** `zTag dᵢ ≠ 4` ⟹ the gated
`iRK` routes `dᵢ` to the replace branch `iRKr` regardless of its `permIdx` sentinel (the lap-94 cure). -/
lemma red_zK_rep_nonchain {s r ds : V} (h1 : permIdx (zK s r ds) < lh ds)
    (htag : zTag (znth ds (permIdx (zK s r ds))) ≠ 4) :
    red (zK s r ds)
      = zK (tpReduce (tp (znth ds (permIdx (zK s r ds)))) s 0) r
          (seqUpdate ds (permIdx (zK s r ds)) (red (znth ds (permIdx (zK s r ds))))) := by
  have hbound : znth ds (permIdx (zK s r ds)) ≤ zK s r ds - 1 :=
    le_trans (znth_le_self ds _) (le_pred_of_lt (ds_lt_zK s r ds))
  rw [red_zK, iRK]
  simp only [zKseq_zK]
  rw [if_pos h1, if_neg (by simp [htag]), iRKr, zKseq_zK, fstIdx_zK, zKrank_zK,
    znth_redTable_eq_red _ _ hbound]

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
theorem redSoundGen : ∀ d : V, ZDerivation d → ZDerivation (red d) := by
  apply zDerivation_induction (P := fun d : V => ZDerivation (red d))
  · definability
  · intro C hC d hphi
    rcases hphi with ⟨s, rfl, hin⟩ | ⟨s, a, p, d0, rfl, hd0, hsucc, hwff⟩ |
      ⟨s, p, d0, rfl, hd0, hsucc, hwff⟩ |
      ⟨s, at', p, d0, d1, rfl, hd0, hd1, hwff⟩ | ⟨s, r, ds, rfl, hds, hmem, hvalid⟩ |
      ⟨s, p, k, rfl, hp, hin⟩ | ⟨s, p, rfl, hp, hin⟩
    · -- zAtom: red = identity
      rw [red_zAtom]; exact zDerivation_iff.mpr (Or.inl ⟨s, rfl, hin⟩)
    · -- zIall: red = d0 (the premise)
      rw [red_zIall]; exact (hC d0 hd0).1
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
    · -- zK: the dispatch; residual supplies validity-preservation
      exact ZDerivation_red_zK
        (zDerivation_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ⟨s, r, ds, rfl, hds, fun i hi => (hC (znth ds i) (hmem i hi)).1, hvalid⟩))))))
        (fun i hi => (hC (znth ds i) (hmem i hi)).2)
    · -- zAxAll: red = identity
      rw [red_zAxAll]; exact zDerivation_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl ⟨s, p, k, rfl, hp, hin⟩))))))
    · -- zAxNeg: red = identity
      rw [red_zAxNeg]; exact zDerivation_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr ⟨s, p, rfl, hp, hin⟩))))))

/-- **M1b — THE nut.** The `red`-reduct of a contradiction derivation is again a genuine `ZDerivation`.
(Re-pointed `RedSound`, off the dead `iR2`.) Now a direct corollary of the general `redSoundGen`. -/
theorem redSound : ∀ d : V, ZDerivesEmpty d → ZDerivation (red d) :=
  fun d h => redSoundGen d h.1

/-- **M1b (descent re-point, one step).** The banked ordinal descent, restated over `red`
(`iR2` analogue: `iord_descent_iR2_of_ZDerivesEmpty`). -/
theorem iord_descent_red {d : V} (hd : ZDerivesEmpty d) : icmp (iord (red d)) (iord d) = 0 := sorry

/-! ## Connectives — PROVEN from the leaves (this is the "no wiring step" demonstration)
With `redSound` in hand, `ZDerivesEmpty` is closed under the whole `red`-orbit and the ε₀-descent is
**unconditional** — mirrors `ZDerivesEmpty_iterate` / `iord_iR2_iterate_descends`, minus the `RedSound`
hypothesis. Bodies left `sorry` here only because this file is uncompiled; they are pure plumbing copies. -/

/-- **`red` preserves `ZDerivesEmpty`** (mirror of `ZDerivesEmpty_iR2`, now UNCONDITIONAL): a
contradiction derivation reduces to one — `redSound` gives `ZDerivation (red d)` and `fstIdx_red`
transfers the empty antecedent + `⊥` succedent. -/
theorem ZDerivesEmpty_red {d : V} (h : ZDerivesEmpty d) : ZDerivesEmpty (red d) := by
  have hfst : fstIdx (red d) = fstIdx d :=
    fstIdx_red h.1 h.2.1 h.2.2 (zTag_Ind_or_K_of_ZDerivesEmpty h)
  exact ⟨redSound d h, by rw [hfst]; exact h.2.1, by rw [hfst]; exact h.2.2⟩

/-- `ZDerivesEmpty` is closed under the `red`-orbit (no hypothesis — `redSound` discharges it). -/
theorem ZDerivesEmpty_red_iterate {z : V} (hz : ZDerivesEmpty z) :
    ∀ n : ℕ, ZDerivesEmpty (red^[n] z)
  | 0 => by simpa using hz
  | n + 1 => by
      rw [Function.iterate_succ_apply']
      exact ZDerivesEmpty_red (ZDerivesEmpty_red_iterate hz n)

/-- **The infinite ε₀-descent of crux-2, UNCONDITIONAL.** `n ↦ iord (red^[n] z)` strictly `≺`-descends.
An infinite primitive-recursive ε₀-descent — exactly what `PRWO(ε₀)` forbids. -/
theorem iord_red_iterate_descends {z : V} (hz : ZDerivesEmpty z) (n : ℕ) :
    icmp (iord (red^[n+1] z)) (iord (red^[n] z)) = 0 := by
  rw [Function.iterate_succ_apply']
  exact iord_descent_red (ZDerivesEmpty_red_iterate hz n)

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
