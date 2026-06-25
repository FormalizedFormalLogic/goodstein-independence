/-
# `wip/InternalZdispatch.lean` — lap-95 de-risk spike: the GATED tag-4 dispatch `iRKfix`

The lap-94 obstruction (`ANALYSIS-2026-06-25-lap94-splice-dispatch-unfaithful.md`): the repo's `iRK`
(`InternalZ.lean:6108`) sub-dispatches splice-vs-replace on `permIdx dᵢ < lh (zKseq dᵢ)`, which for a
NON-chain selected premise `dᵢ` (atom/I-rule/axiom) is `0 < 0 = false`, firing the 5.2.1 SPLICE by
default — even though `dᵢ` is not a chain. So `ZRegular_red_zK`'s last hypothesis `hseltag`
(splice ⟹ `zTag dᵢ = 4`) is FALSE, and that lemma is unusable by `redSound`.

This spike defines the **gated** dispatch `iRKfix`: splice ONLY when the selected premise is a genuine
**critical chain** (`zTag dᵢ = 4 ∧ ¬ permIdx dᵢ < lh (zKseq dᵢ)`); everything else (non-chain, OR
non-critical chain) goes to the replace branch (= Buchholz Def 3.2 case 5.2.2). Then the splice branch
*contains* `zTag dᵢ = 4`, so `hseltag` is derivable and the regularity assembly closes with NO false
hypothesis (`ZRegular_iRKfix` below). This is the de-risk for the in-place port into `iRK` next lap
(see `ANALYSIS-2026-06-25-lap95-dispatch-fix-not-pivot.md`, `PENDING_WORK.md`).

`iRKfix` agrees with `iRK` on every chain selected premise; it differs ONLY on non-chain selected
premises (old: junk splice; new: replace). The three reuse cases below exploit that agreement.
-/
import GoodsteinPA.Zsubst

namespace GoodsteinPA.InternalZ

open Classical
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.HierarchySymbol ISigma1 PeanoMinus
open LO.FirstOrder.Arithmetic.Bootstrapping
open GoodsteinPA.InternalONote

variable {V : Type*} [ORingStructure V] [V ⊧ₘ* 𝗜𝚺₁]

/-- **The gated tag-4 dispatch.** Splice (5.2.1 `iRKs`) only when the selected premise
`dᵢ = znth (zKseq d) (permIdx d)` is a genuine **critical chain** (`zTag dᵢ = 4` AND `dᵢ` critical);
otherwise replace (5.2.2 `iRKr`). The non-critical chain `d` itself still goes critical (5.1 `iRKc`). -/
noncomputable def iRKfix (d s : V) : V :=
  if permIdx d < lh (zKseq d) then
    (if zTag (znth (zKseq d) (permIdx d)) = 4 ∧
        ¬ permIdx (znth (zKseq d) (permIdx d)) < lh (zKseq (znth (zKseq d) (permIdx d)))
     then iRKs d s else iRKr d s)
  else iRKc d s

/-! ## Dispatch invariants — `iRKfix` keeps the conclusion and is a tag-4 chain, every branch -/

@[simp] lemma fstIdx_iRKfix (d s : V) : fstIdx (iRKfix d s) = fstIdx d := by
  unfold iRKfix; split_ifs <;> simp

@[simp] lemma zTag_iRKfix (d s : V) : zTag (iRKfix d s) = 4 := by
  unfold iRKfix; split_ifs <;> simp

/-! ## `iRKfix` vs `red` — agreement on chain selected premises

`iRK` and `iRKfix` differ ONLY when the selected premise is a non-chain that the old sentinel calls
"critical" (`permIdx dᵢ ≥ lh (zKseq dᵢ)`). On the splice branch (`dᵢ` critical) and the 5.1 critical
branch (`d` critical), `iRK` already does what `iRKfix` does, so `red (zK …) = iRKfix (zK …) (redTable …)`
there and we reuse the banked branch lemmas verbatim. -/

/-- On the splice branch (selected premise critical), `iRKfix` = `red` (both fire `iRKs`). -/
lemma red_eq_iRKfix_splice {s r ds : V} (h1 : permIdx (zK s r ds) < lh ds)
    (hcrit : ¬ permIdx (znth ds (permIdx (zK s r ds)))
        < lh (zKseq (znth ds (permIdx (zK s r ds))))) :
    red (zK s r ds) = iRKs (zK s r ds) (redTable (zK s r ds - 1)) := by
  rw [red_zK, iRK]; simp only [zKseq_zK]; rw [if_pos h1, if_neg hcrit]

/-- On the 5.1 critical branch (chain `d` critical), `iRKfix` = `red` (both fire `iRKc`). -/
lemma red_eq_iRKc_crit {s r ds : V} (h1 : ¬ permIdx (zK s r ds) < lh ds) :
    red (zK s r ds) = iRKc (zK s r ds) (redTable (zK s r ds - 1)) := by
  rw [red_zK, iRK]; simp only [zKseq_zK]; rw [if_neg h1]

/-! ## The payoff — `ZRegular (iRKfix (zK …) (redTable …))` closes with NO `hseltag`

This is exactly `ZRegular_red_zK` (`Zsubst.lean:1788`) but against the gated dispatch, so the splice
branch's `zTag dᵢ = 4` comes FROM THE GATE (`h2.1`), not from a false hypothesis. The new content is the
non-chain replace sub-case (where `iRKfix ≠ red`); the chain splice / non-crit replace / critical cases
reuse the banked `ZRegular_red_zK_splice_of_chain` / `_replace`-data / `_crit` bricks. -/
lemma ZRegular_iRKfix {s r ds : V} (hds : Seq ds)
    (hZ : ZDerivation (zK s r ds)) (hreg : ZRegular (zK s r ds))
    (hred : ∀ i < lh ds, ZRegular (red (znth ds i))) :
    ZRegular (iRKfix (zK s r ds) (redTable (zK s r ds - 1))) := by
  unfold iRKfix
  simp only [zKseq_zK]
  by_cases h1 : permIdx (zK s r ds) < lh ds
  · rw [if_pos h1]
    by_cases h2 : zTag (znth ds (permIdx (zK s r ds))) = 4 ∧
        ¬ permIdx (znth ds (permIdx (zK s r ds)))
            < lh (zKseq (znth ds (permIdx (zK s r ds))))
    · -- SPLICE branch — selected premise is a CRITICAL CHAIN; `zTag dᵢ = 4` is `h2.1` (the gate)
      rw [if_pos h2]
      obtain ⟨htag, hcrit⟩ := h2
      have hchain : ZDerivation (znth ds (permIdx (zK s r ds))) := (zDerivation_zK_inv hZ).2 _ h1
      rw [← red_eq_iRKfix_splice h1 hcrit]
      exact ZRegular_red_zK_splice_of_chain hds hreg hred h1 hcrit hchain htag
    · -- REPLACE branch — non-chain selected premise (or non-critical chain): regular unconditionally
      rw [if_neg h2, iRKr]
      simp only [zKseq_zK]
      have hbound : znth ds (permIdx (zK s r ds)) ≤ zK s r ds - 1 :=
        le_trans (znth_le_self ds _) (le_pred_of_lt (ds_lt_zK s r ds))
      rw [znth_redTable_eq_red _ _ hbound, iCritAux_zK]
      exact ZRegular_zK_of_seqUpdate
        (fun m hm => ZRegular_zK_premise hds hreg hm) (hred _ h1)
  · -- 5.1 CRITICAL branch — redex bounds from the chain's own validity (lap-94 `hredex` discharge)
    rw [if_neg h1]
    have hvalid : zKValid s r ds := zKValid_iff_zKValidF_and_zKCritical.mpr
      ⟨zKValidF_of_ZDerivation_zK hZ, zKCritical_of_not_permIdx_lt h1⟩
    obtain ⟨hI, hJ⟩ := redexI_redexJ_lt_of_zKValid hvalid
    rw [← red_eq_iRKc_crit h1]
    exact ZRegular_red_zK_crit hds hreg (hred _ hI) (hred _ hJ) h1

end GoodsteinPA.InternalZ
