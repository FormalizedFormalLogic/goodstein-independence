/-
# `RedZKDescent.lean` — the K-case ordinal descent for the GENUINE reduct `red` (critical branch)

`iord_descent_red`'s K/cut case (`Crux2Blueprint.lean`) needs `icmp (iord (red (zK s r ds))) (iord (zK s r
ds)) = 0`. `red` dispatches three Buchholz Def-3.2 case-5 branches via `iRK`; this file ports the CRITICAL
branch (5.1) from the banked `iord_descent_iR2_zK_of_valid` (which is stated for the `iR2`-ρ).

The ρ for `red`'s critical reduct is `fun n => zAxReduct (red (znth ds n))` (vs `iR2`'s `… (iR2 …)`). The two
agree on the redex premises' `iotil`/`idg`: on the j-side axiom leaves `red = iR2 = id`; on the i-side I¬
`red = iR2 = d0`; on the i-side I∀ `red = zsubst d0 a 0` (≠ `iR2 = d0`) but `iotil_zsubst`/`idg_zsubst` give
equal `iotil`/`idg` (the eigensubst preserves the ordinal — `iord_zsubst`). So the `iRedDescent` bundles
transfer; the genuine reduct `iRcritG` shares `iord` with `iRcrit` (`iord_iRcritG_eq_iRcrit`). Net: the
banked descent transfers verbatim, the I∀ case costing only the regularity `maxEigen d0 < a`.

Sorry-free, axiom-clean (`[propext, Classical.choice, Quot.sound]`). Not yet WIRED into `iord_descent_red`'s
K-case: that needs (a) the non-critical splice/replace branch descents, and (b) `zKValid` available from the
∅→⊥ orbit (the bare `ZDerivation` `zK` disjunct does not yet carry it — see `InternalZ.lean:7517`). Banked
green-gated until then. See `PENDING_WORK.md` lap-108.
-/
import GoodsteinPA.Zsubst
import GoodsteinPA.Compat

namespace GoodsteinPA.InternalZ

open Classical
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.HierarchySymbol ISigma1 PeanoMinus
open LO.FirstOrder.Arithmetic.Bootstrapping
open GoodsteinPA.InternalONote

variable {V : Type*} [ORingStructure V] [V ⊧ₘ* 𝗜𝚺₁]

/-- **j-side `red`-ρ bundle** (L-axiom redex premise): for a §5 atomic-axiom premise `d` (`tp d = L^k_A`),
the wrapped genuine reduct `zAxReduct (red d)` satisfies the `iRedDescent` bundle. `red` is the identity on
the axiom leaves (tags 5/6, `red_zAxAll`/`red_zAxNeg`), so this is literally the banked `iR2` bundle. -/
lemma iRedDescent_zAxReduct_red_of_tp_isymLk {d k A : V} (htp : tp d = isymLk k A)
    (hZ : ZDerivation d) : iRedDescent (zAxReduct (red d)) d := by
  rcases zDerivation_iff.mp hZ with ⟨s, rfl, _⟩ | ⟨s, a, p, d0, rfl, _, _⟩ | ⟨s, p, d0, rfl, _, _⟩ |
    ⟨s, at', p, d0, d1, rfl, _, _⟩ | ⟨s, r, ds, rfl, _, _, _⟩ |
    ⟨s, p, k', rfl, hp, _⟩ | ⟨s, p, rfl, hp, _⟩ | ⟨s, C, rfl, _⟩ | ⟨s, rfl, _⟩
  · rw [tp_zAtom] at htp; exact absurd htp (by simp)
  · rw [tp_zIall] at htp; exact absurd htp (by simp)
  · rw [tp_zIneg] at htp; exact absurd htp (by simp)
  · rw [tp_zInd] at htp; exact absurd htp (by simp)
  · rw [tp_zK] at htp; exact absurd htp (by simp)
  · rw [red_zAxAll]; exact iRedDescent_zAxReduct_zAxAll hp.isUFormula
  · rw [red_zAxNeg]; exact iRedDescent_zAxReduct_zAxNeg hp
  · rw [tp_zAx1] at htp; exact absurd htp (by simp)
  · rw [tp_zAxBot] at htp; exact absurd htp (by simp)

/-- **i-side `red`-ρ bundle** (R-redex premise): for an I-rule premise `d` (`tp d = R_A`), the wrapped
genuine reduct `zAxReduct (red d)` satisfies the `iRedDescent` bundle. For I¬, `red = d0 = iR2`. For I∀,
`red = zsubst d0 a 0`; the eigensubst preserves `iotil`/`idg` (`iotil_zsubst`/`idg_zsubst`), so the base
bundle transfers from `iRedDescent_zIall`, and `ZDerivation (zsubst d0 a 0)` (needed for the `zAxReduct`
wrap) holds by `ZDerivation_zsubst` given the I∀ regularity `maxEigen d0 < a` (from `ZRegular d`). -/
lemma iRedDescent_zAxReduct_red_of_tp_isymR {d A : V} (htp : tp d = isymR A)
    (hZ : ZDerivation d) (hreg : ZRegular d) : iRedDescent (zAxReduct (red d)) d := by
  rcases zDerivation_iff.mp hZ with ⟨s, rfl, _⟩ | ⟨s, a, p, d0, rfl, hd0, _⟩ | ⟨s, p, d0, rfl, hd0, _⟩ |
    ⟨s, at', p, d0, d1, rfl, _, _⟩ | ⟨s, r, ds, rfl, _, _, _⟩ |
    ⟨s, p, k, rfl, _, _⟩ | ⟨s, p, rfl, _, _⟩ | ⟨s, C, rfl, _⟩ | ⟨s, rfl, _⟩
  · rw [tp_zAtom] at htp; exact absurd htp (by simp)
  · -- I∀: red = zsubst d0 a 0
    have ht0 : IsSemiterm ℒₒᵣ 0 (Bootstrapping.Arithmetic.numeral 0 : V) := by simp
    have hut0 : IsUTerm ℒₒᵣ (Bootstrapping.Arithmetic.numeral 0 : V) := ht0.isUTerm
    have hregd : maxEigen d0 < a := maxEigen_lt_of_regular_zIall hreg
    have hZred : ZDerivation (zsubst d0 a (Bootstrapping.Arithmetic.numeral 0)) :=
      ZDerivation_zsubst ht0 d0 hd0 hregd
    have hbase : iRedDescent (zsubst d0 a (Bootstrapping.Arithmetic.numeral 0)) (zIall s a p d0) := by
      have hb0 := iRedDescent_zIall (s := s) (a := a) (p := p) (isNF_iotil_of_ZDerivation d0 hd0)
      refine ⟨?_, ?_, ?_⟩
      · rw [idg_zsubst hut0 a d0 hd0]; exact hb0.dg_le
      · rw [iotil_zsubst hut0 a d0 hd0]; exact hb0.otil_lt
      · rw [iotil_zsubst hut0 a d0 hd0]; exact hb0.nf
    rw [red_zIall]; exact iRedDescent_zAxReduct_of_iRedDescent hZred hbase
  · -- I¬: red = d0 = iR2
    rw [red_zIneg]
    exact iRedDescent_zAxReduct_of_iRedDescent hd0 (iRedDescent_zIneg (isNF_iotil_of_ZDerivation d0 hd0))
  · rw [tp_zInd] at htp; exact absurd htp (by simp)
  · rw [tp_zK] at htp; exact absurd htp (by simp)
  · rw [tp_zAxAll] at htp; exact absurd htp (by simp)
  · rw [tp_zAxNeg] at htp; exact absurd htp (by simp)
  · rw [tp_zAx1] at htp; exact absurd htp (by simp)
  · rw [tp_zAxBot] at htp; exact absurd htp (by simp)

/-- **THE critical-branch K-case descent for the GENUINE reduct `red`.** For a valid `K^r` chain whose
selected premise is critical (`¬ permIdx < lh ds`), `red (zK s r ds) = iRcritG …` and the ordinal strictly
descends: `icmp (iord (red (zK s r ds))) (iord (zK s r ds)) = 0`. Port of `iord_descent_iR2_zK_of_valid`
(`iR2`-ρ) to the `red`-ρ, via the i/j-side `red` bundles + `iord_iRcritG_eq_iRcrit` (the genuine reduct
shares `iord` with the ordinal-shadow `iRcrit`). The I∀ redex premise costs the regularity `hreg`. -/
lemma iord_descent_red_zK_crit {s r ds : V} (hcrit : ¬ permIdx (zK s r ds) < lh ds)
    (hds : Seq ds) (hmem : ∀ i < lh ds, ZDerivation (znth ds i))
    (hreg : ∀ i < lh ds, ZRegular (znth ds i)) (hvalid : zKValid s r ds) :
    icmp (iord (red (zK s r ds))) (iord (zK s r ds)) = 0 := by
  obtain ⟨hci, hperm0, hnperm0, hf1, hf2, hf5, hf6, _hsucc, _hssf, _hsaf⟩ := hvalid
  obtain ⟨j0, hj0, hAj0, hchain, hrank⟩ := hci
  have hwfR : ∀ i ≤ j0, ∀ A, tp (znth ds i) = isymR A → 0 < irk A ∨ False :=
    fun i hi A h => Or.inl (tp_isymR_pos h (hf1 i (lt_of_le_of_lt hi hj0))
      (hf2 i (lt_of_le_of_lt hi hj0)))
  have hwfL : ∀ i ≤ j0, ∀ k A, tp (znth ds i) = isymLk k A → 0 < irk A ∨ (A = (^⊥ : V)) :=
    fun i hi k A h => Or.inl (tp_isymLk_pos h (hf5 i (lt_of_le_of_lt hi hj0))
      (hf6 i (lt_of_le_of_lt hi hj0)))
  have hperm : ∀ i ≤ j0, iperm (tp (znth ds i)) (fstIdx (znth ds i)) :=
    fun i hi => hperm0 i (lt_of_le_of_lt hi hj0)
  have hnperm : ∀ i ≤ j0, ¬ iperm (tp (znth ds i)) s :=
    fun i hi => hnperm0 i (lt_of_le_of_lt hi hj0)
  have hnf : isNF (iotil (zK s r ds)) :=
    isNF_iotil_zK hds (fun i hi => isNF_iotil_of_ZDerivation _ (hmem i hi))
  have hNF : ∀ n, isNF (iotil (znth ds n)) := by
    intro n
    rcases lt_or_ge n (lh ds) with hn | hn
    · exact isNF_iotil_of_ZDerivation _ (hmem n hn)
    · rw [znth_prop_not (Or.inr hn)]; exact isNF_iotil_zero
  obtain ⟨i0, j1, k0, hij, hjle, hRi, hLj, hrkpos, hrkr⟩ :=
    inference_critical_pair_of_chain (Tr := fun _ => False) (Fa := fun A => A = (^⊥ : V))
      hj0 hAj0 hchain hrank hwfR hwfL hperm hnperm (fun _ h => h.1)
      (fun A h => by rw [h]; exact irk_falsum) rfl
  have hjlt : j1 < lh ds := lt_of_le_of_lt hjle hj0
  have hilt : i0 < lh ds := lt_trans hij hjlt
  have hredex : isRedexPair ds (⟪i0, j1⟫ : V) := by
    simp only [isRedexPair, pi₁_pair, pi₂_pair]
    refine ⟨hij, hjlt, ?_, ?_, ?_⟩
    · rw [hRi]; simp [isymR]
    · rw [hLj]; simp [isymLk]
    · rw [hRi, hLj]; simp [isymR, isymLk]
  have hex : ∃ c < (⟪lh (zKseq (zK s r ds)), lh (zKseq (zK s r ds))⟫ : V),
      isRedexPair (zKseq (zK s r ds)) c := by
    simp only [zKseq_zK]; exact ⟨⟪i0, j1⟫, pair_lt_pair hilt hjlt, hredex⟩
  have hrc : isRedexPair (zKseq (zK s r ds)) (redexCode (zK s r ds)) := redexCode_isRedexPair hex
  simp only [zKseq_zK] at hrc
  have hIlt : redexI (zK s r ds) < lh ds := lt_trans hrc.1 hrc.2.1
  have hJlt : redexJ (zK s r ds) < lh ds := hrc.2.1
  obtain ⟨hRedI, hRedJ⟩ := redexPair_tp hrc
  have hbI := iRedDescent_zAxReduct_red_of_tp_isymR hRedI (hmem _ hIlt) (hreg _ hIlt)
  have hbJ := iRedDescent_zAxReduct_red_of_tp_isymLk hRedJ (hmem _ hJlt)
  rw [red_zK_crit hcrit, iord_iRcritG_eq_iRcrit]
  exact iord_descent_iRcrit_of_chain' (Tr := fun _ => False) (Fa := fun A => A = (^⊥ : V))
    hds hnf hj0 hAj0 hchain hrank hwfR hwfL hperm hnperm (fun _ h => h.1)
    (fun A h => by rw [h]; exact irk_falsum) rfl hNF
    hbI.otil_lt hbJ.otil_lt hbI.dg_le hbJ.dg_le hbI.nf hbJ.nf

/-- **The STALL-BYPASSING critical-reduct descent** (lap 124 — the genuine fix for the `red`-fixpoint
defect). The critical-cut reduct `iRcrit (zK s r ds) ρ` (`ρ = zAxReduct ∘ red`) of a ⊥-chain `ZDerivation`
strictly `iord`-descends **regardless of `red`'s `permIdx` selection**, provided every `isymRep` premise is a
LEAF (`hleaves`). Unlike `iord_descent_red_zK_crit` (which needs `¬ permIdx < lh ds`, i.e. a fully-critical
chain, and routes through `red = iRcritG`), this manufactures the redex via `inference_critical_pair_of_botChain`
(the reroute finder — tolerant of permissible leaves) and feeds `iord_descent_iRcrit_of_redex` DIRECTLY, never
touching `red (zK s r ds)`. **Why it matters:** in the documented stall `red (zK s r ds) = zK s r ds` (a leaf
is the first `isymRep`, `permIdx < lh ds`), so `iord_descent_red_zK_crit` does NOT apply and the `red`-orbit
gives no descent — but the genuine redex still exists and `iRcrit` still descends. This is the LEFT branch of
`redex_or_nonleaf_isymRep_of_botChain` made into an actual ordinal descent. The 6 `ρ`-facts reuse the banked
`iRedDescent_zAxReduct_red_of_tp_isymR`/`_isymLk` bundles (same as the critical case). -/
lemma iord_descent_iRcrit_botChain_leaves {s r ds : V}
    (hZ : ZDerivation (zK s r ds))
    (hant : seqAnt s = (∅ : V)) (hsucc : seqSucc s = (^⊥ : V))
    (hreg : ∀ i < lh ds, ZRegular (znth ds i))
    (hleaves : ∀ i < lh ds, tp (znth ds i) = isymRep →
      (∃ sk, znth ds i = zAtom sk) ∨ (∃ sk Ck, znth ds i = zAx1 sk Ck)) :
    icmp (iord (iRcrit (zK s r ds) (fun n => zAxReduct (red (znth ds n))))) (iord (zK s r ds)) = 0 := by
  obtain ⟨hds, hmem⟩ := zDerivation_zK_inv hZ
  obtain ⟨i0, j1, k0, hij, hjlt, hRi, hLj, hrkpos, hrkr⟩ :=
    inference_critical_pair_of_botChain hZ hant hsucc hleaves
  have hilt : i0 < lh ds := lt_trans hij hjlt
  have hnf : isNF (iotil (zK s r ds)) :=
    isNF_iotil_zK hds (fun i hi => isNF_iotil_of_ZDerivation _ (hmem i hi))
  have hNF : ∀ n, isNF (iotil (znth ds n)) := by
    intro n
    rcases lt_or_ge n (lh ds) with hn | hn
    · exact isNF_iotil_of_ZDerivation _ (hmem n hn)
    · rw [znth_prop_not (Or.inr hn)]; exact isNF_iotil_zero
  have hredex : isRedexPair ds (⟪i0, j1⟫ : V) := by
    simp only [isRedexPair, pi₁_pair, pi₂_pair]
    refine ⟨hij, hjlt, ?_, ?_, ?_⟩
    · rw [hRi]; simp [isymR]
    · rw [hLj]; simp [isymLk]
    · rw [hRi, hLj]; simp [isymR, isymLk]
  have hex : ∃ c < (⟪lh (zKseq (zK s r ds)), lh (zKseq (zK s r ds))⟫ : V),
      isRedexPair (zKseq (zK s r ds)) c := by
    simp only [zKseq_zK]; exact ⟨⟪i0, j1⟫, pair_lt_pair hilt hjlt, hredex⟩
  have hrc : isRedexPair (zKseq (zK s r ds)) (redexCode (zK s r ds)) := redexCode_isRedexPair hex
  simp only [zKseq_zK] at hrc
  have hIlt : redexI (zK s r ds) < lh ds := lt_trans hrc.1 hrc.2.1
  have hJlt : redexJ (zK s r ds) < lh ds := hrc.2.1
  obtain ⟨hRedI, hRedJ⟩ := redexPair_tp hrc
  have hbI := iRedDescent_zAxReduct_red_of_tp_isymR hRedI (hmem _ hIlt) (hreg _ hIlt)
  have hbJ := iRedDescent_zAxReduct_red_of_tp_isymLk hRedJ (hmem _ hJlt)
  have hr : 1 ≤ r := pos_iff_one_le.mp (lt_of_lt_of_le hrkpos hrkr)
  exact iord_descent_iRcrit_of_redex hds hnf hr hex hNF
    hbI.otil_lt hbJ.otil_lt hbI.dg_le hbJ.dg_le hbI.nf hbJ.nf

/-- **The descent dichotomy for a genuine ⊥-chain** (lap 124 — `redex_or_nonleaf_isymRep_of_botChain` with
its LEFT disjunct upgraded from "a redex exists" to "the critical reduct actually `iord`-descends"). For a
`ZDerivation` ⊥-chain with regular premises: **either** the critical-cut reduct `iRcrit` strictly descends
(case 5.1, stall-tolerant — `iord_descent_iRcrit_botChain_leaves`), **or** there is a NON-LEAF `isymRep`
premise (chain/Ind, case 5.2 — to be spliced). This is the exact case split the restructured
`false_of_ZDerivesEmpty` consumes: it gives a genuine `iord`-decreasing successor on the LEFT with NO
dependence on `red`'s `permIdx` (so no `red`-fixpoint branch), and isolates the residual to the case-5.2
splice on the RIGHT (the existing `ZDerivation_red_zK_splice` machinery). -/
theorem iRcrit_descends_or_nonleaf_isymRep {s r ds : V}
    (hZ : ZDerivation (zK s r ds))
    (hant : seqAnt s = (∅ : V)) (hsucc : seqSucc s = (^⊥ : V))
    (hreg : ∀ i < lh ds, ZRegular (znth ds i)) :
    icmp (iord (iRcrit (zK s r ds) (fun n => zAxReduct (red (znth ds n))))) (iord (zK s r ds)) = 0
    ∨ (∃ i < lh ds, tp (znth ds i) = isymRep ∧
        ¬ ((∃ sk, znth ds i = zAtom sk) ∨ (∃ sk Ck, znth ds i = zAx1 sk Ck))) := by
  by_cases h : ∃ i < lh ds, tp (znth ds i) = isymRep ∧
      ¬ ((∃ sk, znth ds i = zAtom sk) ∨ (∃ sk Ck, znth ds i = zAx1 sk Ck))
  · exact Or.inr h
  · push Not at h
    exact Or.inl (iord_descent_iRcrit_botChain_leaves hZ hant hsucc hreg (fun i hi hrep => h i hi hrep))

/-- **Critical-reduct halves descend below the chain — the splice sub-fact (lap 110).** For a valid
critical `K^r` chain `dᵢ = zK s r ds` (`¬ permIdx < lh ds`), `red dᵢ = iRcritG dᵢ ρ` whose two
premise-halves `a,b = znth (zKseq (red dᵢ)) {0,1}` are `K`-chains over `seqUpdate ds (redexI/J) (red·)` —
i.e. `dᵢ`'s OWN premise sequence with the redex-`R`/`L` premise replaced by its strictly-descending genuine
reduct. So each half's `õ`/`idg`-fold lies (strictly/weakly) below `dᵢ`'s and is NF — **the `õ`-jump of the
critical 5.1 reduct is in the OUTER `K^{r-1}` rank-drop, NOT in the individual halves' premise folds.**
This extracts exactly the per-half `ha`/`hb`/`hag`/`hbg`/`hNFa`/`hNFb` that `iord_descent_red_zK_chain_splice`
consumes for the parent chain-splice (Buchholz Def-3.2 case 5.2.1); the rank bound `hr'` remains the
documented residual (the cut-rank `rk(A(dᵢ))` degree-drop bookkeeping). Mirrors the redex extraction of
`iord_descent_red_zK_crit`, then applies the `iCritAux` fold-monotonicity lemmas (`iotil_iCritAux_lt`,
`idg_iCritAux_le`) since `iotil`/`idg` ignore the half's reset conclusion/rank. -/
lemma iCrit_halves_descend {s r ds : V} (hcrit : ¬ permIdx (zK s r ds) < lh ds)
    (hds : Seq ds) (hmem : ∀ i < lh ds, ZDerivation (znth ds i))
    (hreg : ∀ i < lh ds, ZRegular (znth ds i)) (hvalid : zKValid s r ds)
    (hrankI : irk (chainAsucc ds (redexI (zK s r ds))) ≤ r) :
    icmp (iotil (znth (zKseq (red (zK s r ds))) 0)) (iotil (zK s r ds)) = 0 ∧
    icmp (iotil (znth (zKseq (red (zK s r ds))) 1)) (iotil (zK s r ds)) = 0 ∧
    idg (znth (zKseq (red (zK s r ds))) 0) ≤ idg (zK s r ds) ∧
    idg (znth (zKseq (red (zK s r ds))) 1) ≤ idg (zK s r ds) ∧
    isNF (iotil (znth (zKseq (red (zK s r ds))) 0)) ∧
    isNF (iotil (znth (zKseq (red (zK s r ds))) 1)) ∧
    irk (seqSucc (fstIdx (znth (zKseq (red (zK s r ds))) 0))) < r := by
  obtain ⟨hci, hperm0, hnperm0, hf1, hf2, hf5, hf6, _hsucc, _hssf, _hsaf⟩ := hvalid
  obtain ⟨j0, hj0, hAj0, hchain, hrank⟩ := hci
  have hwfR : ∀ i ≤ j0, ∀ A, tp (znth ds i) = isymR A → 0 < irk A ∨ False :=
    fun i hi A h => Or.inl (tp_isymR_pos h (hf1 i (lt_of_le_of_lt hi hj0))
      (hf2 i (lt_of_le_of_lt hi hj0)))
  have hwfL : ∀ i ≤ j0, ∀ k A, tp (znth ds i) = isymLk k A → 0 < irk A ∨ (A = (^⊥ : V)) :=
    fun i hi k A h => Or.inl (tp_isymLk_pos h (hf5 i (lt_of_le_of_lt hi hj0))
      (hf6 i (lt_of_le_of_lt hi hj0)))
  have hperm : ∀ i ≤ j0, iperm (tp (znth ds i)) (fstIdx (znth ds i)) :=
    fun i hi => hperm0 i (lt_of_le_of_lt hi hj0)
  have hnperm : ∀ i ≤ j0, ¬ iperm (tp (znth ds i)) s :=
    fun i hi => hnperm0 i (lt_of_le_of_lt hi hj0)
  have hNF : ∀ n, isNF (iotil (znth ds n)) := by
    intro n
    rcases lt_or_ge n (lh ds) with hn | hn
    · exact isNF_iotil_of_ZDerivation _ (hmem n hn)
    · rw [znth_prop_not (Or.inr hn)]; exact isNF_iotil_zero
  obtain ⟨i0, j1, k0, hij, hjle, hRi, hLj, hrkpos, hrkr⟩ :=
    inference_critical_pair_of_chain (Tr := fun _ => False) (Fa := fun A => A = (^⊥ : V))
      hj0 hAj0 hchain hrank hwfR hwfL hperm hnperm (fun _ h => h.1)
      (fun A h => by rw [h]; exact irk_falsum) rfl
  have hjlt : j1 < lh ds := lt_of_le_of_lt hjle hj0
  have hilt : i0 < lh ds := lt_trans hij hjlt
  have hredex : isRedexPair ds (⟪i0, j1⟫ : V) := by
    simp only [isRedexPair, pi₁_pair, pi₂_pair]
    refine ⟨hij, hjlt, ?_, ?_, ?_⟩
    · rw [hRi]; simp [isymR]
    · rw [hLj]; simp [isymLk]
    · rw [hRi, hLj]; simp [isymR, isymLk]
  have hex : ∃ c < (⟪lh (zKseq (zK s r ds)), lh (zKseq (zK s r ds))⟫ : V),
      isRedexPair (zKseq (zK s r ds)) c := by
    simp only [zKseq_zK]; exact ⟨⟪i0, j1⟫, pair_lt_pair hilt hjlt, hredex⟩
  have hrc : isRedexPair (zKseq (zK s r ds)) (redexCode (zK s r ds)) := redexCode_isRedexPair hex
  simp only [zKseq_zK] at hrc
  have hIlt : redexI (zK s r ds) < lh ds := lt_trans hrc.1 hrc.2.1
  have hJlt : redexJ (zK s r ds) < lh ds := hrc.2.1
  obtain ⟨hRedI, hRedJ⟩ := redexPair_tp hrc
  have hbI := iRedDescent_zAxReduct_red_of_tp_isymR hRedI (hmem _ hIlt) (hreg _ hIlt)
  have hbJ := iRedDescent_zAxReduct_red_of_tp_isymLk hRedJ (hmem _ hJlt)
  -- The two halves, computed from `red_zK_crit` + `iRcritG`/`iCritReductSeq` read-outs. `iotil`/`idg`
  -- ignore the reset conclusion/rank, so each half's fold equals the corresponding `iCritAux` fold.
  set vI : V := zAxReduct (red (znth ds (redexI (zK s r ds)))) with hvI
  set vJ : V := zAxReduct (red (znth ds (redexJ (zK s r ds)))) with hvJ
  have e0 : znth (zKseq (red (zK s r ds))) 0
      = zK (seqSetSucc s (cutFormula (zK s r ds))) r
          (seqUpdate ds (redexI (zK s r ds)) vI) := by
    rw [red_zK_crit hcrit, iRcritG]
    simp only [fstIdx_zK, zKseq_zK, zKrank_zK, zKseq_iCritReductG, znth_iCritReductSeq_zero, hvI]
  have e1 : znth (zKseq (red (zK s r ds))) 1
      = zK (seqAddAnt (cutFormula (zK s r ds)) s) r
          (seqUpdate ds (redexJ (zK s r ds)) vJ) := by
    rw [red_zK_crit hcrit, iRcritG]
    simp only [fstIdx_zK, zKseq_zK, zKrank_zK, zKseq_iCritReductG, znth_iCritReductSeq_one, hvJ]
  have hiotil0 : iotil (znth (zKseq (red (zK s r ds))) 0)
      = iotil (iCritAux (zK s r ds) (redexI (zK s r ds)) vI) := by
    rw [e0, iCritAux_zK, iotil_zK _ _ _ (seqUpdate_seq ds _ vI), iotil_zK _ _ _ (seqUpdate_seq ds _ vI)]
  have hiotil1 : iotil (znth (zKseq (red (zK s r ds))) 1)
      = iotil (iCritAux (zK s r ds) (redexJ (zK s r ds)) vJ) := by
    rw [e1, iCritAux_zK, iotil_zK _ _ _ (seqUpdate_seq ds _ vJ), iotil_zK _ _ _ (seqUpdate_seq ds _ vJ)]
  have hidg0 : idg (znth (zKseq (red (zK s r ds))) 0)
      = idg (iCritAux (zK s r ds) (redexI (zK s r ds)) vI) := by
    rw [e0, iCritAux_zK, idg_zK _ _ _ (seqUpdate_seq ds _ vI), idg_zK _ _ _ (seqUpdate_seq ds _ vI)]
  have hidg1 : idg (znth (zKseq (red (zK s r ds))) 1)
      = idg (iCritAux (zK s r ds) (redexJ (zK s r ds)) vJ) := by
    rw [e1, iCritAux_zK, idg_zK _ _ _ (seqUpdate_seq ds _ vJ), idg_zK _ _ _ (seqUpdate_seq ds _ vJ)]
  -- The redex R-principal `A_i = chainAsucc ds (redexI)` equals `π₂ (tp dᵢ)` by R-permissibility
  -- (global `hperm0` at `redexI < lh ds`), so the redexCode's `tp = R_{A_i}` is in `chainAsucc` form
  -- — exactly what `irk_cutFormula_lt` consumes. This is the rank-side conjunct (T3.4(a) strict drop).
  have hRedI' : tp (znth ds (redexI (zK s r ds)))
      = isymR (π₂ (tp (znth ds (redexI (zK s r ds))))) := hRedI
  have hChA : chainAsucc ds (redexI (zK s r ds)) = π₂ (tp (znth ds (redexI (zK s r ds)))) := by
    have hp := hperm0 _ hIlt
    rw [hRedI', iperm_isymR_iff] at hp
    exact hp.symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hiotil0]; exact iotil_iCritAux_lt hds hIlt hbI.otil_lt hNF hbI.nf
  · rw [hiotil1]; exact iotil_iCritAux_lt hds hJlt hbJ.otil_lt hNF hbJ.nf
  · rw [hidg0]; exact idg_iCritAux_le hds hIlt hbI.dg_le
  · rw [hidg1]; exact idg_iCritAux_le hds hJlt hbJ.dg_le
  · rw [hiotil0, iCritAux_zK]
    exact isNF_iotil_zK (seqUpdate_seq ds _ vI) (fun n _ => by
      rcases eq_or_ne n (redexI (zK s r ds)) with rfl | hne
      · rw [znth_seqUpdate_self hIlt]; exact hbI.nf
      · rw [znth_seqUpdate_of_ne hne]; exact hNF n)
  · rw [hiotil1, iCritAux_zK]
    exact isNF_iotil_zK (seqUpdate_seq ds _ vJ) (fun n _ => by
      rcases eq_or_ne n (redexJ (zK s r ds)) with rfl | hne
      · rw [znth_seqUpdate_self hJlt]; exact hbJ.nf
      · rw [znth_seqUpdate_of_ne hne]; exact hNF n)
  · -- T3.4(a): `rk(A(d)) < r`. Read out the half-0 succedent as `cutFormula`, then strict drop.
    rw [e0, fstIdx_zK, seqSucc_seqSetSucc]
    refine irk_cutFormula_lt (d := zK s r ds) ?_ ?_ ?_
    · rw [zKseq_zK]; exact hmem _ hIlt
    · rw [zKseq_zK, hChA]; exact hRedI
    · rw [zKseq_zK]; exact hrankI

/-- **The non-critical REPLACE-branch K-case descent (Buchholz Def-3.2 case 5.2.2), conditional on the
selected premise's reduct descending.** Both replace dispatches (`red_zK_rep` chain-`dᵢ`-non-critical and
`red_zK_rep_nonchain` non-chain `dᵢ`) produce the SAME reduct shape `red (zK s r ds) = K^r(i/red dᵢ)` —
a `seqUpdate` of `ds` at `i = permIdx` swapping premise `dᵢ` for its reduct `red dᵢ`, same rank `r`. Given
the premise IH `iRedDescent (red dᵢ) dᵢ` (the recursive descent: `red dᵢ` doesn't raise the degree and
strictly lowers `õ`, judge §8.3 LH3/N2), the whole `K^r` ordinal strictly descends — `iotil` drops one
summand (`iotil_zK_lt_replace`, the F1 strict `#`-mono), `idg` doesn't rise (`idg_zK_le_replace`), then
`iord_descent_le` combines through the tower. Stated against the explicit reduct equation `hred` so a
single lemma covers both replace dispatches. -/
lemma iRedDescent_red_zK_replace_eq {s s' r ds i : V}
    (hds : Seq ds) (hmem : ∀ n < lh ds, ZDerivation (znth ds n)) (hi : i < lh ds)
    (hred : red (zK s r ds) = zK s' r (seqUpdate ds i (red (znth ds i))))
    (hIH : iRedDescent (red (znth ds i)) (znth ds i)) :
    iRedDescent (red (zK s r ds)) (zK s r ds) := by
  have hNF : ∀ n, isNF (iotil (znth ds n)) := fun n => by
    rcases lt_or_ge n (lh ds) with hn | hn
    · exact isNF_iotil_of_ZDerivation _ (hmem n hn)
    · rw [znth_prop_not (Or.inr hn)]; exact isNF_iotil_zero
  have hNF' : ∀ n, isNF (iotil (znth (seqUpdate ds i (red (znth ds i))) n)) := fun n => by
    rcases eq_or_ne n i with rfl | hne
    · rw [znth_seqUpdate_self hi]; exact hIH.nf
    · rw [znth_seqUpdate_of_ne hne]; exact hNF n
  have hle : ∀ n, idg (znth (seqUpdate ds i (red (znth ds i))) n) ≤ idg (znth ds n) := fun n => by
    rcases eq_or_ne n i with rfl | hne
    · rw [znth_seqUpdate_self hi]; exact hIH.dg_le
    · rw [znth_seqUpdate_of_ne hne]
  have heq : ∀ n, n ≠ i →
      iotil (znth (seqUpdate ds i (red (znth ds i))) n) = iotil (znth ds n) :=
    fun n hne => by rw [znth_seqUpdate_of_ne hne]
  have hlt : icmp (iotil (znth (seqUpdate ds i (red (znth ds i))) i)) (iotil (znth ds i)) = 0 := by
    rw [znth_seqUpdate_self hi]; exact hIH.otil_lt
  rw [hred]
  exact ⟨idg_zK_le_replace hds (seqUpdate_seq ds i _) (seqUpdate_lh ds i _) hle,
    iotil_zK_lt_replace hds (seqUpdate_seq ds i _) (seqUpdate_lh ds i _) hi hlt heq hNF hNF',
    isNF_iotil_zK (seqUpdate_seq ds i _) (fun n _ => hNF' n)⟩

/-- **`iord`-descent corollary of the REPLACE bundle** (the form the current `iord_descent_red`
non-recursive dispatch consumes). -/
lemma iord_descent_red_zK_replace_eq {s s' r ds i : V}
    (hds : Seq ds) (hmem : ∀ n < lh ds, ZDerivation (znth ds n)) (hi : i < lh ds)
    (hred : red (zK s r ds) = zK s' r (seqUpdate ds i (red (znth ds i))))
    (hIH : iRedDescent (red (znth ds i)) (znth ds i)) :
    icmp (iord (red (zK s r ds))) (iord (zK s r ds)) = 0 :=
  iord_descent_of_iRedDescent (iRedDescent_red_zK_replace_eq hds hmem hi hred hIH)
    (isNF_iotil_zK hds (fun n hn => isNF_iotil_of_ZDerivation _ (hmem n hn)))

/-- **The non-critical SPLICE-branch K-case descent (Buchholz Def-3.2 case 5.2.1), conditional on the two
spliced halves descending below the selected premise.** When the selected premise `dᵢ = znth ds i`
(`i = permIdx`) is itself a CRITICAL chain (`zTag dᵢ = 4` ∧ `dᵢ` critical), `red (zK s r ds) =
K^{r'}(seqInsert ds i a b)` splices `dᵢ`'s two critical-reduct halves `a,b = znth (zKseq (red dᵢ)) {0,1}`
in place at `i`, with the genuine reduct rank `r' = max{rk(A(dᵢ)), r}` (judge §8.3 LH5). Given each half's
`õ`/`idg` bound below `dᵢ` (`ha`/`hb`/`hag`/`hbg`, from the critical reduction of `dᵢ`) and the faithful
rank bound `r' ≤ dg(parent)` (`hr'`), the `K^r` ordinal strictly descends via the F2 rotation kernel
(`iotil_seqInsert_lt`) + the rank-general `idg` bound (`idg_seqInsert_le'`) through `iord_descent_le`,
i.e. the banked `iord_descent_seqInsert'`. Stated against the explicit reduct equation `hred`. -/
lemma iRedDescent_red_zK_splice_eq {s r ds i a b s' r' : V}
    (hds : Seq ds) (hmem : ∀ n < lh ds, ZDerivation (znth ds n)) (hi : i < lh ds)
    (hred : red (zK s r ds) = zK s' r' (seqInsert ds i a b))
    (hr' : r' ≤ idg (zK s r ds))
    (ha : icmp (iotil a) (iotil (znth ds i)) = 0) (hb : icmp (iotil b) (iotil (znth ds i)) = 0)
    (hag : idg a ≤ idg (znth ds i)) (hbg : idg b ≤ idg (znth ds i))
    (hNFa : isNF (iotil a)) (hNFb : isNF (iotil b)) :
    iRedDescent (red (zK s r ds)) (zK s r ds) := by
  have hNF : ∀ n, isNF (iotil (znth ds n)) := fun n => by
    rcases lt_or_ge n (lh ds) with hn | hn
    · exact isNF_iotil_of_ZDerivation _ (hmem n hn)
    · rw [znth_prop_not (Or.inr hn)]; exact isNF_iotil_zero
  rw [hred]
  exact ⟨idg_seqInsert_le' hds hi hr' hag hbg,
    iotil_seqInsert_lt hds hi ha hb hNF hNFa hNFb,
    isNF_iotil_zK (seqInsert_seq ds i a b) (fun n hn =>
      forall_znth_seqInsert (P := fun x => isNF (iotil x)) hi hNFa hNFb
        (fun k _ => hNF k) n (by rwa [seqInsert_lh] at hn))⟩

/-- **`iord`-descent corollary of the SPLICE bundle** (the form the current `iord_descent_red`
chain-splice dispatch consumes). -/
lemma iord_descent_red_zK_splice_eq {s r ds i a b s' r' : V}
    (hds : Seq ds) (hmem : ∀ n < lh ds, ZDerivation (znth ds n)) (hi : i < lh ds)
    (hred : red (zK s r ds) = zK s' r' (seqInsert ds i a b))
    (hr' : r' ≤ idg (zK s r ds))
    (ha : icmp (iotil a) (iotil (znth ds i)) = 0) (hb : icmp (iotil b) (iotil (znth ds i)) = 0)
    (hag : idg a ≤ idg (znth ds i)) (hbg : idg b ≤ idg (znth ds i))
    (hNFa : isNF (iotil a)) (hNFb : isNF (iotil b)) :
    icmp (iord (red (zK s r ds))) (iord (zK s r ds)) = 0 :=
  iord_descent_of_iRedDescent
    (iRedDescent_red_zK_splice_eq hds hmem hi hred hr' ha hb hag hbg hNFa hNFb)
    (isNF_iotil_zK hds (fun n hn => isNF_iotil_of_ZDerivation _ (hmem n hn)))

/-- **I∀ genuine-reduct descent bundle.** `red (zIall s a p d0) = zsubst d0 a 0` satisfies `iRedDescent`
against `zIall s a p d0` — NO regularity needed for the ORDINAL bundle (only the eigensubst-invariance of
the assignment): `iotil_zsubst`/`idg_zsubst` carry the banked `iRedDescent_zIall` (stated for the `iR2`-ρ
`d0`) onto the genuine eigensubst reduct. The selected-I∀-premise case of the non-critical K-branch
(`iord_descent_red`) feeds this to `iord_descent_red_zK_replace_eq`. -/
lemma iRedDescent_red_zIall {s a p d0 : V} (hZ : ZDerivation (zIall s a p d0)) :
    iRedDescent (red (zIall s a p d0)) (zIall s a p d0) := by
  obtain ⟨hd0, _, _⟩ := zDerivation_zIall_inv hZ
  have hut0 : IsUTerm ℒₒᵣ (Bootstrapping.Arithmetic.numeral 0 : V) :=
    (by simp : IsSemiterm ℒₒᵣ 0 (Bootstrapping.Arithmetic.numeral 0 : V)).isUTerm
  have hb0 := iRedDescent_zIall (s := s) (a := a) (p := p) (isNF_iotil_of_ZDerivation d0 hd0)
  rw [red_zIall]
  exact ⟨by rw [idg_zsubst hut0 a d0 hd0]; exact hb0.dg_le,
    by rw [iotil_zsubst hut0 a d0 hd0]; exact hb0.otil_lt,
    by rw [iotil_zsubst hut0 a d0 hd0]; exact hb0.nf⟩

/-- **The CORRECTED critical R-reduct's descent bundle (instance-general).** The §5 critical reduct of an
`I∀` redex is the re-principalized `zsubst d0 a t` for the L-instance term `t` (= `numeral k`, NOT the
engine's `numeral 0`). Since `iotil`/`idg` are INVARIANT under eigenvariable substitution
(`iotil_zsubst`/`idg_zsubst`, for ANY closed term `t`), the descent bundle `iRedDescent_zIall` (the
unsubstituted I∀ fact `õ` drops by one) transfers verbatim to `zsubst d0 a t` — this is precisely why the
ε₀-descent is instance-invariant and survives the `0 ↦ k` re-principalization. Generalises
`iRedDescent_red_zIall` (the engine reduct `zsubst d0 a (numeral 0)`) to the corrected instance. -/
lemma iRedDescent_zsubst_zIall {s a p d0 t : V} (ht : IsUTerm ℒₒᵣ t)
    (hZ : ZDerivation (zIall s a p d0)) :
    iRedDescent (zsubst d0 a t) (zIall s a p d0) := by
  obtain ⟨hd0, _, _⟩ := zDerivation_zIall_inv hZ
  have hb0 := iRedDescent_zIall (s := s) (a := a) (p := p) (isNF_iotil_of_ZDerivation d0 hd0)
  exact ⟨by rw [idg_zsubst ht a d0 hd0]; exact hb0.dg_le,
    by rw [iotil_zsubst ht a d0 hd0]; exact hb0.otil_lt,
    by rw [iotil_zsubst ht a d0 hd0]; exact hb0.nf⟩

/-- **THE corrected critical reduct DESCENDS — the ε₀-side of the re-keying, PROVEN.** The genuine
re-principalized critical reduct `iRcritG d (critReductCorr d)` strictly `≺`-descends below the chain `d`,
exactly like the engine reduct (`iord_descent_red_zK_crit`). The descent assembly
`iord_descent_iRcrit_of_chain'` reads the reduct supplier only through six per-redex bundle facts
(`õ`-drop, `dg`-non-raise, NF at `redexI`/`redexJ`); for `critReductCorr` these are supplied by the
corrected bundles `iRedDescent_zsubst_zIall` (R-redex, instance-`k`, õ/dg INVARIANT under the eigensubst)
and `iRedDescent_zAx1_zAxAll_of_irk` (L-redex, `oAtom1 (cutFormula d)` one rank below the principal). So the
descent is genuinely INSTANCE-INVARIANT — it survives the `0 ↦ k` re-principalization with no õ-bookkeeping
change. **This + `ZDerivation_iRcritG_critReductCorr` (soundness) are the two halves of "red preserves valid
+ descends" for the corrected reduct;** only the engine re-keying (`red_zK_crit ↦ critReductCorr`) remains.
Unlike the engine version this needs NO regularity hypothesis (the corrected R-bundle uses `iotil_zsubst`,
invariant for ANY closed term). -/
theorem iord_descent_iRcritG_critReductCorr {s r ds sᵢ sⱼ a p pj k' d0 : V}
    (hds : Seq ds) (hmem : ∀ i < lh ds, ZDerivation (znth ds i))
    (hvalid : zKValid s r ds)
    (hIlt : redexI (zK s r ds) < lh ds) (_ : redexJ (zK s r ds) < lh ds)
    (hIJ : redexI (zK s r ds) < redexJ (zK s r ds))
    (hdi : znth ds (redexI (zK s r ds)) = zIall sᵢ a p d0)
    (hdj : znth ds (redexJ (zK s r ds)) = zAxAll sⱼ pj k')
    (hirk : irk (^∀ pj : V) = irk (cutFormula (zK s r ds)) + 1) :
    icmp (iord (iRcritG (zK s r ds) (critReductCorr (zK s r ds)))) (iord (zK s r ds)) = 0 := by
  obtain ⟨hci, hperm0, hnperm0, hf1, hf2, hf5, hf6, _hsucc, _hssf, _hsaf⟩ := hvalid
  obtain ⟨j0, hj0, hAj0, hchain, hrank⟩ := hci
  have hwfR : ∀ i ≤ j0, ∀ A, tp (znth ds i) = isymR A → 0 < irk A ∨ False :=
    fun i hi A h => Or.inl (tp_isymR_pos h (hf1 i (lt_of_le_of_lt hi hj0))
      (hf2 i (lt_of_le_of_lt hi hj0)))
  have hwfL : ∀ i ≤ j0, ∀ k A, tp (znth ds i) = isymLk k A → 0 < irk A ∨ (A = (^⊥ : V)) :=
    fun i hi k A h => Or.inl (tp_isymLk_pos h (hf5 i (lt_of_le_of_lt hi hj0))
      (hf6 i (lt_of_le_of_lt hi hj0)))
  have hperm : ∀ i ≤ j0, iperm (tp (znth ds i)) (fstIdx (znth ds i)) :=
    fun i hi => hperm0 i (lt_of_le_of_lt hi hj0)
  have hnperm : ∀ i ≤ j0, ¬ iperm (tp (znth ds i)) s :=
    fun i hi => hnperm0 i (lt_of_le_of_lt hi hj0)
  have hnf : isNF (iotil (zK s r ds)) :=
    isNF_iotil_zK hds (fun i hi => isNF_iotil_of_ZDerivation _ (hmem i hi))
  have hNF : ∀ n, isNF (iotil (znth ds n)) := by
    intro n
    rcases lt_or_ge n (lh ds) with hn | hn
    · exact isNF_iotil_of_ZDerivation _ (hmem n hn)
    · rw [znth_prop_not (Or.inr hn)]; exact isNF_iotil_zero
  -- corrected R-bundle (instance-`k`, õ/dg invariant under the eigensubst — no regularity needed)
  have hbI : iRedDescent (critReductCorr (zK s r ds) (redexI (zK s r ds)))
      (znth ds (redexI (zK s r ds))) := by
    rw [critReductCorr, if_neg (ne_of_lt hIJ), if_pos rfl, zKseq_zK, hdi,
      zIallPrem_zIall, zIallEig_zIall]
    exact iRedDescent_zsubst_zIall
      (by simp : IsSemiterm ℒₒᵣ 0 (Bootstrapping.Arithmetic.numeral
        (π₁ (π₂ (tp (znth ds (redexJ (zK s r ds)))))) : V)).isUTerm (hdi ▸ hmem _ hIlt)
  -- corrected L-bundle (the §5 logical axiom, `oAtom1 (cutFormula d)` one rank below the principal)
  have hbJ : iRedDescent (critReductCorr (zK s r ds) (redexJ (zK s r ds)))
      (znth ds (redexJ (zK s r ds))) := by
    rw [critReductCorr, if_pos rfl]
    simp only [zKseq_zK, hdj, fstIdx_zAxAll]
    exact iRedDescent_zAx1_zAxAll_of_irk hirk
  rw [iord_iRcritG_eq_iRcrit]
  exact iord_descent_iRcrit_of_chain' (Tr := fun _ => False) (Fa := fun A => A = (^⊥ : V))
    hds hnf hj0 hAj0 hchain hrank hwfR hwfL hperm hnperm (fun _ h => h.1)
    (fun A h => by rw [h]; exact irk_falsum) rfl hNF
    hbI.otil_lt hbJ.otil_lt hbI.dg_le hbJ.dg_le hbI.nf hbJ.nf

/-- **The ¬-case corrected critical reduct DESCENDS — the `iord_descent_iRcritG_critReductCorr` twin.** For a
critical cut on `¬A` (R-redex `I¬`, L-redex `axNeg`), the reduct `iRcritGNeg d (critReductNeg d)` strictly
`≺`-descends below the chain. `iord_descent_iRcrit_of_chain'` reads the supplier through the six per-redex
bundle facts, here supplied by the ¬ bundles `iRedDescent_zIneg` (R-redex: the `I¬` child `d₀`, õ/dg below
the rule) and `iRedDescent_zAx1_zAxNeg_gen` (L-redex: the §5 `Ax^1`, `oAtom1 A` below the `axNeg` principal
`oAtomLk (¬A)`). The ordinal re-point is `iord_iRcritGNeg_eq_iRcrit` — which (unlike the ∀ `iRcritG` twin)
needs the two reduct folds NF; supplied from the per-entry NF (`hNF` for the unchanged premises, `hbI/hbJ.nf`
for the two replaced redexes) via `isNF_iseqNaddIdg`. Together with
`ZDerivation_iRcritGNeg_critReductNeg` (soundness), this is "red preserves valid + descends" for the ¬-case
corrected reduct — the ¬ twin of the ∀ pair, completing both polarities for the engine re-key's descent. -/
theorem iord_descent_iRcritGNeg_critReductNeg {s r ds sᵢ sⱼ p d0 : V}
    (hds : Seq ds) (hmem : ∀ i < lh ds, ZDerivation (znth ds i))
    (hvalid : zKValid s r ds)
    (hIlt : redexI (zK s r ds) < lh ds) (hJlt : redexJ (zK s r ds) < lh ds)
    (hIJ : redexI (zK s r ds) < redexJ (zK s r ds))
    (hdi : znth ds (redexI (zK s r ds)) = zIneg sᵢ p d0)
    (hdj : znth ds (redexJ (zK s r ds)) = zAxNeg sⱼ p)
    (hcut : cutFormula (zK s r ds) = p) (hp : IsUFormula ℒₒᵣ p) :
    icmp (iord (iRcritGNeg (zK s r ds) (critReductNeg (zK s r ds)))) (iord (zK s r ds)) = 0 := by
  obtain ⟨hci, hperm0, hnperm0, hf1, hf2, hf5, hf6, _hsucc, _hssf, _hsaf⟩ := hvalid
  obtain ⟨j0, hj0, hAj0, hchain, hrank⟩ := hci
  have hwfR : ∀ i ≤ j0, ∀ A, tp (znth ds i) = isymR A → 0 < irk A ∨ False :=
    fun i hi A h => Or.inl (tp_isymR_pos h (hf1 i (lt_of_le_of_lt hi hj0))
      (hf2 i (lt_of_le_of_lt hi hj0)))
  have hwfL : ∀ i ≤ j0, ∀ k A, tp (znth ds i) = isymLk k A → 0 < irk A ∨ (A = (^⊥ : V)) :=
    fun i hi k A h => Or.inl (tp_isymLk_pos h (hf5 i (lt_of_le_of_lt hi hj0))
      (hf6 i (lt_of_le_of_lt hi hj0)))
  have hperm : ∀ i ≤ j0, iperm (tp (znth ds i)) (fstIdx (znth ds i)) :=
    fun i hi => hperm0 i (lt_of_le_of_lt hi hj0)
  have hnperm : ∀ i ≤ j0, ¬ iperm (tp (znth ds i)) s :=
    fun i hi => hnperm0 i (lt_of_le_of_lt hi hj0)
  have hnf : isNF (iotil (zK s r ds)) :=
    isNF_iotil_zK hds (fun i hi => isNF_iotil_of_ZDerivation _ (hmem i hi))
  have hNF : ∀ n, isNF (iotil (znth ds n)) := by
    intro n
    rcases lt_or_ge n (lh ds) with hn | hn
    · exact isNF_iotil_of_ZDerivation _ (hmem n hn)
    · rw [znth_prop_not (Or.inr hn)]; exact isNF_iotil_zero
  -- ¬ R-bundle (I¬ child `d0`)
  have hbI : iRedDescent (critReductNeg (zK s r ds) (redexI (zK s r ds)))
      (znth ds (redexI (zK s r ds))) := by
    rw [critReductNeg_redexI (ne_of_lt hIJ), zKseq_zK, hdi, zInegPrem_zIneg]
    exact iRedDescent_zIneg
      (isNF_iotil_of_ZDerivation d0 (zDerivation_zIneg_inv (hdi ▸ hmem _ hIlt)).1)
  -- ¬ L-bundle (§5 axNeg reduct `Ax^1`)
  have hbJ : iRedDescent (critReductNeg (zK s r ds) (redexJ (zK s r ds)))
      (znth ds (redexJ (zK s r ds))) := by
    rw [critReductNeg_redexJ, zKseq_zK, hdj, fstIdx_zAxNeg, hcut]
    exact iRedDescent_zAx1_zAxNeg_gen hp
  -- NF of the two reduct folds (the extra obligation of `iord_iRcritGNeg_eq_iRcrit`)
  have hNFI : isNF (iseqNaddIdg (seqUpdate (zKseq (zK s r ds)) (redexI (zK s r ds))
      (critReductNeg (zK s r ds) (redexI (zK s r ds))))) := by
    rw [zKseq_zK]
    exact isNF_iseqNaddIdg (fun n _ => by
      rcases eq_or_ne n (redexI (zK s r ds)) with rfl | hne
      · rw [znth_seqUpdate_self hIlt]; exact hbI.nf
      · rw [znth_seqUpdate_of_ne hne]; exact hNF n)
  have hNFJ : isNF (iseqNaddIdg (seqUpdate (zKseq (zK s r ds)) (redexJ (zK s r ds))
      (critReductNeg (zK s r ds) (redexJ (zK s r ds))))) := by
    rw [zKseq_zK]
    exact isNF_iseqNaddIdg (fun n _ => by
      rcases eq_or_ne n (redexJ (zK s r ds)) with rfl | hne
      · rw [znth_seqUpdate_self hJlt]; exact hbJ.nf
      · rw [znth_seqUpdate_of_ne hne]; exact hNF n)
  rw [iord_iRcritGNeg_eq_iRcrit (zK s r ds) (critReductNeg (zK s r ds)) hNFI hNFJ]
  exact iord_descent_iRcrit_of_chain' (Tr := fun _ => False) (Fa := fun A => A = (^⊥ : V))
    hds hnf hj0 hAj0 hchain hrank hwfR hwfL hperm hnperm (fun _ h => h.1)
    (fun A h => by rw [h]; exact irk_falsum) rfl hNF
    hbI.otil_lt hbJ.otil_lt hbI.dg_le hbJ.dg_le hbI.nf hbJ.nf

/-- **The re-keyed critical reduct `iRKcCrit` DESCENDS — ∀-case.** Thin wrapper bringing the engine-swap
descent target to "needs only the redex forms" parity with the soundness side: `iRKcCrit_eq_corr` rewrites
`iRKcCrit (zK s r ds) = iRcritG (zK s r ds) (critReductCorr …)` (the `zTag dᵢ = 1` branch), then the banked
`iord_descent_iRcritG_critReductCorr` closes. Once the engine swaps `red ↦ iRKcCrit`, the descent's critical
branch is `rw [red_zK_crit hcrit]; exact this`. -/
theorem iord_descent_iRKcCrit_corr {s r ds sᵢ sⱼ a p pj k' d0 : V}
    (hds : Seq ds) (hmem : ∀ i < lh ds, ZDerivation (znth ds i))
    (hvalid : zKValid s r ds)
    (hIlt : redexI (zK s r ds) < lh ds) (hJlt : redexJ (zK s r ds) < lh ds)
    (hIJ : redexI (zK s r ds) < redexJ (zK s r ds))
    (hdi : znth ds (redexI (zK s r ds)) = zIall sᵢ a p d0)
    (hdj : znth ds (redexJ (zK s r ds)) = zAxAll sⱼ pj k')
    (hirk : irk (^∀ pj : V) = irk (cutFormula (zK s r ds)) + 1) :
    icmp (iord (iRKcCrit (zK s r ds))) (iord (zK s r ds)) = 0 := by
  have h1 : zTag (znth (zKseq (zK s r ds)) (redexI (zK s r ds))) = 1 := by
    rw [zKseq_zK, hdi]; exact zTag_zIall _ _ _ _
  rw [iRKcCrit_eq_corr h1 (ne_of_lt hIJ)]
  exact iord_descent_iRcritG_critReductCorr hds hmem hvalid hIlt hJlt hIJ hdi hdj hirk

/-- **The re-keyed critical reduct `iRKcCrit` DESCENDS — ¬-case.** The `iRKcCrit_eq_neg` twin of
`iord_descent_iRKcCrit_corr`: rewrites to `iRcritGNeg (zK s r ds) (critReductNeg …)` (the `zTag dᵢ ≠ 1`
branch, here `= 2` from the I¬ redex), then the banked `iord_descent_iRcritGNeg_critReductNeg` closes. -/
theorem iord_descent_iRKcCrit_neg {s r ds sᵢ sⱼ p d0 : V}
    (hds : Seq ds) (hmem : ∀ i < lh ds, ZDerivation (znth ds i))
    (hvalid : zKValid s r ds)
    (hIlt : redexI (zK s r ds) < lh ds) (hJlt : redexJ (zK s r ds) < lh ds)
    (hIJ : redexI (zK s r ds) < redexJ (zK s r ds))
    (hdi : znth ds (redexI (zK s r ds)) = zIneg sᵢ p d0)
    (hdj : znth ds (redexJ (zK s r ds)) = zAxNeg sⱼ p)
    (hcut : cutFormula (zK s r ds) = p) (hp : IsUFormula ℒₒᵣ p) :
    icmp (iord (iRKcCrit (zK s r ds))) (iord (zK s r ds)) = 0 := by
  have h1 : zTag (znth (zKseq (zK s r ds)) (redexI (zK s r ds))) ≠ 1 := by
    rw [zKseq_zK, hdi, zTag_zIneg]; simp
  rw [iRKcCrit_eq_neg h1 (ne_of_lt hIJ)]
  exact iord_descent_iRcritGNeg_critReductNeg hds hmem hvalid hIlt hJlt hIJ hdi hdj hcut hp

/-- **Chain sub-case, REPLACE dispatch (`dᵢ` a non-critical chain), reduced to the premise IH.** When the
selected premise `dᵢ = znth ds (permIdx)` is a chain (`zTag = 4`) that is itself non-critical
(`permIdx dᵢ < lh (zKseq dᵢ)`), `red (zK s r ds) = K^r(i/red dᵢ)` (`red_zK_rep`), so the descent is exactly
`iord_descent_red_zK_replace_eq` fed the recursive IH `iRedDescent (red dᵢ) dᵢ`. This is the precise interface
the strong-induction recursion supplies for the chain-replace branch. -/
lemma iRedDescent_red_zK_chain_replace {s r ds : V}
    (hds : Seq ds) (hmem : ∀ n < lh ds, ZDerivation (znth ds n))
    (h1 : permIdx (zK s r ds) < lh ds)
    (h2 : permIdx (znth ds (permIdx (zK s r ds)))
        < lh (zKseq (znth ds (permIdx (zK s r ds)))))
    (hIH : iRedDescent (red (znth ds (permIdx (zK s r ds)))) (znth ds (permIdx (zK s r ds)))) :
    iRedDescent (red (zK s r ds)) (zK s r ds) :=
  iRedDescent_red_zK_replace_eq hds hmem h1 (red_zK_rep h1 h2) hIH

lemma iord_descent_red_zK_chain_replace {s r ds : V}
    (hds : Seq ds) (hmem : ∀ n < lh ds, ZDerivation (znth ds n))
    (h1 : permIdx (zK s r ds) < lh ds)
    (h2 : permIdx (znth ds (permIdx (zK s r ds)))
        < lh (zKseq (znth ds (permIdx (zK s r ds)))))
    (hIH : iRedDescent (red (znth ds (permIdx (zK s r ds)))) (znth ds (permIdx (zK s r ds)))) :
    icmp (iord (red (zK s r ds))) (iord (zK s r ds)) = 0 :=
  iord_descent_red_zK_replace_eq hds hmem h1 (red_zK_rep h1 h2) hIH

/-- **Chain sub-case, SPLICE dispatch (`dᵢ` a critical chain), reduced to the two halves' descent.** When
the selected premise `dᵢ` is a critical chain (`zTag = 4`, `¬ permIdx dᵢ < lh (zKseq dᵢ)`),
`red (zK s r ds)` splices `dᵢ`'s critical-reduct halves (`red_zK_splice`); the descent is
`iord_descent_red_zK_splice_eq` fed the per-half `õ`/`idg` bounds + rank bound (from `dᵢ`'s critical
reduction). The genuine reduct rank is `max{rk(A(dᵢ)), r}`; here the halves `a,b` and the rank-bound `hr'`
are the recursion's outputs. -/
lemma iord_descent_red_zK_chain_splice {s r ds : V}
    (hds : Seq ds) (hmem : ∀ n < lh ds, ZDerivation (znth ds n))
    (h1 : permIdx (zK s r ds) < lh ds)
    (h2 : ¬ permIdx (znth ds (permIdx (zK s r ds)))
        < lh (zKseq (znth ds (permIdx (zK s r ds)))))
    (htag : zTag (znth ds (permIdx (zK s r ds))) = 4)
    (hr' : max (irk (seqSucc (fstIdx
        (znth (zKseq (red (znth ds (permIdx (zK s r ds))))) 0)))) r ≤ idg (zK s r ds))
    (ha : icmp (iotil (znth (zKseq (red (znth ds (permIdx (zK s r ds))))) 0))
        (iotil (znth ds (permIdx (zK s r ds)))) = 0)
    (hb : icmp (iotil (znth (zKseq (red (znth ds (permIdx (zK s r ds))))) 1))
        (iotil (znth ds (permIdx (zK s r ds)))) = 0)
    (hag : idg (znth (zKseq (red (znth ds (permIdx (zK s r ds))))) 0)
        ≤ idg (znth ds (permIdx (zK s r ds))))
    (hbg : idg (znth (zKseq (red (znth ds (permIdx (zK s r ds))))) 1)
        ≤ idg (znth ds (permIdx (zK s r ds))))
    (hNFa : isNF (iotil (znth (zKseq (red (znth ds (permIdx (zK s r ds))))) 0)))
    (hNFb : isNF (iotil (znth (zKseq (red (znth ds (permIdx (zK s r ds))))) 1))) :
    icmp (iord (red (zK s r ds))) (iord (zK s r ds)) = 0 :=
  iord_descent_red_zK_splice_eq hds hmem h1 (red_zK_splice h1 h2 htag) hr' ha hb hag hbg hNFa hNFb

/-- **`iRedDescent` form of the chain-SPLICE wrapper** (for the `iRedDescent_red` recursion). -/
lemma iRedDescent_red_zK_chain_splice {s r ds : V}
    (hds : Seq ds) (hmem : ∀ n < lh ds, ZDerivation (znth ds n))
    (h1 : permIdx (zK s r ds) < lh ds)
    (h2 : ¬ permIdx (znth ds (permIdx (zK s r ds)))
        < lh (zKseq (znth ds (permIdx (zK s r ds)))))
    (htag : zTag (znth ds (permIdx (zK s r ds))) = 4)
    (hr' : max (irk (seqSucc (fstIdx
        (znth (zKseq (red (znth ds (permIdx (zK s r ds))))) 0)))) r ≤ idg (zK s r ds))
    (ha : icmp (iotil (znth (zKseq (red (znth ds (permIdx (zK s r ds))))) 0))
        (iotil (znth ds (permIdx (zK s r ds)))) = 0)
    (hb : icmp (iotil (znth (zKseq (red (znth ds (permIdx (zK s r ds))))) 1))
        (iotil (znth ds (permIdx (zK s r ds)))) = 0)
    (hag : idg (znth (zKseq (red (znth ds (permIdx (zK s r ds))))) 0)
        ≤ idg (znth ds (permIdx (zK s r ds))))
    (hbg : idg (znth (zKseq (red (znth ds (permIdx (zK s r ds))))) 1)
        ≤ idg (znth ds (permIdx (zK s r ds))))
    (hNFa : isNF (iotil (znth (zKseq (red (znth ds (permIdx (zK s r ds))))) 0)))
    (hNFb : isNF (iotil (znth (zKseq (red (znth ds (permIdx (zK s r ds))))) 1))) :
    iRedDescent (red (zK s r ds)) (zK s r ds) :=
  iRedDescent_red_zK_splice_eq hds hmem h1 (red_zK_splice h1 h2 htag) hr' ha hb hag hbg hNFa hNFb

/-- **The atom-selection FIXPOINT defect, formalized (lap 109).** If the selected (least-permissible)
premise of a non-critical chain is a bare identity-atom `zAtom sᵢ` (`zTag = 0`, a `red`-normal form), the
genuine reduct is a **FIXPOINT**: `red (zK s r ds) = zK s r ds`. Because the non-chain replace dispatch
(`red_zK_rep_nonchain`) swaps premise `i` for `red dᵢ = dᵢ` (atoms are normal, `red_zAtom`) and reduces the
conclusion by `tpReduce (tp dᵢ) s 0 = tpReduce isymRep s 0 = s` (Rep-reduce is the identity,
`tpReduce_isymRep`), so `seqUpdate ds i dᵢ = ds` (`seqUpdate_znth_self`) leaves the whole node unchanged.

This pins the kernel obstruction to the descent recursion (PENDING_WORK lap-109): when `permIdx` selects an
atom, `iord (red (zK s r ds)) = iord (zK s r ds)` — NO strict descent, the orbit STALLS. The `isymRep` tag
conflates atoms (normal forms) with reducible Ind/chains, and `iperm isymRep` is unconditionally true
(`iperm_isymRep`), so an atom CAN be the first permissible premise. The fix is an `isPermPrem`/`permIdx`
engine refinement that excludes atom premises (so the selected premise is always reducible), OR an embedding
(`foundation_bot_to_Z_empty`) that produces atom-free chains. -/
lemma red_zK_fixpoint_of_atom_selected {s r ds sᵢ : V}
    (hds : Seq ds) (h1 : permIdx (zK s r ds) < lh ds)
    (hatom : znth ds (permIdx (zK s r ds)) = zAtom sᵢ) :
    red (zK s r ds) = zK s r ds := by
  have htag : zTag (znth ds (permIdx (zK s r ds))) ≠ 4 := by rw [hatom]; simp
  rw [red_zK_rep_nonchain h1 htag,
    show red (znth ds (permIdx (zK s r ds))) = znth ds (permIdx (zK s r ds)) from by
      rw [hatom, red_zAtom],
    seqUpdate_znth_self hds h1,
    show tp (znth ds (permIdx (zK s r ds))) = isymRep from by rw [hatom, tp_zAtom],
    tpReduce_isymRep]

/-- **`red`-fixpoint when the selected premise is a §5 logical axiom `Ax^1`.** Mirror of
`red_zK_fixpoint_of_atom_selected`: `zAx1` is `red`-normal (`red_zAx1`), `tp = isymRep` (`tp_zAx1`), so the
Rep-replace `iRKr` reinserts the same premise and keeps the conclusion (`tpReduce_isymRep`), making the
whole node a `red`-fixpoint — disjunctive descent closes on the LEFT. -/
lemma red_zK_fixpoint_of_zAx1_selected {s r ds sᵢ Cᵢ : V}
    (hds : Seq ds) (h1 : permIdx (zK s r ds) < lh ds)
    (hax1 : znth ds (permIdx (zK s r ds)) = zAx1 sᵢ Cᵢ) :
    red (zK s r ds) = zK s r ds := by
  have htag : zTag (znth ds (permIdx (zK s r ds))) ≠ 4 := by rw [hax1]; simp
  rw [red_zK_rep_nonchain h1 htag,
    show red (znth ds (permIdx (zK s r ds))) = znth ds (permIdx (zK s r ds)) from by
      rw [hax1, red_zAx1],
    seqUpdate_znth_self hds h1,
    show tp (znth ds (permIdx (zK s r ds))) = isymRep from by rw [hax1, tp_zAx1],
    tpReduce_isymRep]

/-- **`red`-fixpoint when the selected premise is the ⊥-left axiom `zAxBot`.** Mirror of
`red_zK_fixpoint_of_zAx1_selected`: `zAxBot` is `red`-normal (`red_zAxBot`), `tp = isymRep` (`tp_zAxBot`),
so the Rep-replace `iRKr` reinserts the same premise and keeps the conclusion — the whole node is a
`red`-fixpoint. -/
lemma red_zK_fixpoint_of_zAxBot_selected {s r ds sᵢ : V}
    (hds : Seq ds) (h1 : permIdx (zK s r ds) < lh ds)
    (hbot : znth ds (permIdx (zK s r ds)) = zAxBot sᵢ) :
    red (zK s r ds) = zK s r ds := by
  have htag : zTag (znth ds (permIdx (zK s r ds))) ≠ 4 := by rw [hbot]; simp
  rw [red_zK_rep_nonchain h1 htag,
    show red (znth ds (permIdx (zK s r ds))) = znth ds (permIdx (zK s r ds)) from by
      rw [hbot, red_zAxBot],
    seqUpdate_znth_self hds h1,
    show tp (znth ds (permIdx (zK s r ds))) = isymRep from by rw [hbot, tp_zAxBot],
    tpReduce_isymRep]

/-- **Tag-explicit ⊥-orbit descent dichotomy** (lap 130). Upgrades `iRcrit_descends_or_nonleaf_isymRep`'s
RIGHT disjunct from "a non-leaf `isymRep` premise exists" to the STRUCTURAL form "a `zInd` (tag 3) or `zK`
(tag 4) premise exists" (via `isymRep_nonleaf_zInd_or_zK`). This is the clean entry the restructured
`false_of_ZDerivesEmpty` consumes — and it sidesteps the `red`-`permIdx` fixpoint entirely:
- **LEFT** = the stall-tolerant critical-cut descent `iRcrit` (no `permIdx`/`red`-fixpoint dependence,
  `iord_descent_iRcrit_botChain_leaves`).
- **RIGHT** = the major-premise recursion target: a `zInd` premise (reduced by `red_zInd`, a banked strict
  descent `iord_descent_red_zInd`) or a sub-`zK`-chain premise (the genuine tag-4 recursion residual).
Tags 5/6 (L-axioms, `isymLk` not `isymRep`) never appear on the RIGHT — they are the LEFT redex's L-side,
their cut-partner pinned by `majorPrem_zAxAll_cutPartner` / `majorPrem_zAxNeg_cutPartner`. -/
theorem iRcrit_descends_or_zInd_zK_premise {s r ds : V}
    (hZ : ZDerivation (zK s r ds))
    (hant : seqAnt s = (∅ : V)) (hsucc : seqSucc s = (^⊥ : V))
    (hreg : ∀ i < lh ds, ZRegular (znth ds i)) :
    icmp (iord (iRcrit (zK s r ds) (fun n => zAxReduct (red (znth ds n))))) (iord (zK s r ds)) = 0
    ∨ (∃ i < lh ds, (∃ s' at' p d0 d1, znth ds i = zInd s' at' p d0 d1) ∨
        (∃ s' r' ds', znth ds i = zK s' r' ds') ∨ (∃ s', znth ds i = zAxBot s')) := by
  rcases iRcrit_descends_or_nonleaf_isymRep hZ hant hsucc hreg with hL | ⟨i, hi, hrep, hnleaf⟩
  · exact Or.inl hL
  · obtain ⟨_, hmem⟩ := zDerivation_zK_inv hZ
    exact Or.inr ⟨i, hi, isymRep_nonleaf_zInd_or_zK (hmem i hi) hrep hnleaf⟩

end GoodsteinPA.InternalZ


