/-
# `Zsubst.lean` — eigenvariable substitution on Z-derivations (rung 1 of the RedSound ladder)

`zsubst d a t` replaces the free variable `^&a` by a (closed) coded term `t` throughout a
Z-derivation code `d`. It is the foundational brick of the genuine internalized cut-elimination
reduct (`RedSound`, crux-2's last wall): the Buchholz I∀/Ind reducts substitute the eigenvariable
by a numeral throughout the minor premise (`d[n] := d0(a/n)`).

This file builds, bottom-up:
* `fvSubstSeq a t Γ` — map the formula-level `fvSubst a t` over a coded sequence of formulas.
* `fvSubstSeqt a t s` — substitute the whole sequent `s = ⟪Γ, C⟫` (antecedent sequence + succedent).
* `zsubst d a t` — the course-of-values `<`-recursion over the derivation tree (mirrors `iRTable`).

The replacement `t` is always closed (`IsSemiterm ℒₒᵣ 0 t`), so `fvSubst`'s `IsSemiformula`
preservation applies (`fvSubst_isSemiformula`).
-/
import GoodsteinPA.InternalZ
import GoodsteinPA.FvSubst

namespace GoodsteinPA.InternalZ

open Classical
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.HierarchySymbol ISigma1 PeanoMinus
open LO.FirstOrder.Arithmetic.Bootstrapping
open GoodsteinPA.InternalONote

variable {V : Type*} [ORingStructure V] [V ⊧ₘ* 𝗜𝚺₁]


/-! ## Structural correctness of the `zsubst` table (mirror `iR2`/`iotil`)

The table read-out + diagonal unfolding + per-constructor recursion equations, proven exactly as the
`iR2`/`iotil` analogs in `InternalZ.lean`. The payoff is `fstIdx_zsubst` and the recursion equations
that `ZDerivation_zsubst` (rung-1 correctness) will consume. -/

private lemma def_zsubstTable {k} (a t : V) (i : Fin k) :
    𝚺-[1].DefinableFunction (fun v : Fin k → V ↦ zsubstTable a t (v i)) :=
  DefinableFunction₃.comp (F := zsubstTable) (DefinableFunction.const a)
    (DefinableFunction.const t) (DefinableFunction.var i)

private lemma def_zsubst {k} (a t : V) (i : Fin k) :
    𝚺-[1].DefinableFunction (fun v : Fin k → V ↦ zsubst (v i) a t) :=
  DefinableFunction₃.comp (F := zsubst) (DefinableFunction.var i)
    (DefinableFunction.const a) (DefinableFunction.const t)

@[simp] lemma zsubstTable_seq (a t n : V) : Seq (zsubstTable a t n) := by
  induction n using ISigma1.sigma1_succ_induction
  · exact Definable.comp₁ (def_zsubstTable a t 0)
  case zero => simp
  case succ n ih => rw [zsubstTable_succ]; exact ih.seqCons _

@[simp] lemma zsubstTable_lh (a t n : V) : lh (zsubstTable a t n) = n + 1 := by
  induction n using ISigma1.sigma1_succ_induction
  · exact Definable.comp₂ (DefinableFunction₁.comp (F := lh) (def_zsubstTable a t 0)) (by definability)
  case zero => simp
  case succ n ih => rw [zsubstTable_succ, Seq.lh_seqCons _ (zsubstTable_seq a t n), ih]

lemma znth_zsubstTable_succ (a t : V) {n k : V} (hk : k < n + 1) :
    znth (zsubstTable a t (n + 1)) k = znth (zsubstTable a t n) k := by
  rw [zsubstTable_succ]
  exact znth_seqCons_of_lt (zsubstTable_seq a t n) _ (by rw [zsubstTable_lh]; exact hk)

lemma znth_zsubstTable_eq_zsubst (a t : V) : ∀ N : V, ∀ k ≤ N, znth (zsubstTable a t N) k = zsubst k a t := by
  intro N
  induction N using ISigma1.sigma1_succ_induction
  · refine Definable.ball_le (by definability) ?_
    exact Definable.comp₂
      (DefinableFunction₂.comp (F := znth) (def_zsubstTable a t 1) (DefinableFunction.var 0))
      (def_zsubst a t 0)
  case zero =>
    intro k hk; rcases (nonpos_iff_eq_zero.mp hk) with rfl; rfl
  case succ N ih =>
    intro k hk
    rcases eq_or_lt_of_le hk with rfl | hlt
    · rfl
    · rw [znth_zsubstTable_succ a t hlt]; exact ih k (le_iff_lt_succ.mpr hlt)

lemma zsubst_eq_zsubstNext (a t : V) {c : V} (hpos : 0 < c) :
    zsubst c a t = zsubstNext c (zsubstTable a t (c - 1)) a t := by
  obtain ⟨M, rfl⟩ : ∃ M, c = M + 1 := ⟨c - 1, (sub_add_self_of_le (pos_iff_one_le.mp hpos)).symm⟩
  have key : znth (zsubstTable a t (M + 1)) (M + 1) = zsubstNext (M + 1) (zsubstTable a t M) a t := by
    rw [zsubstTable_succ]
    have h := znth_seqCons_self (zsubstTable_seq a t M) (zsubstNext (M + 1) (zsubstTable a t M) a t)
    rwa [zsubstTable_lh] at h
  simp only [zsubst, add_tsub_cancel_right, key]

/-! ### `zsubst` recursion equations (per Z-rule) -/

@[simp] lemma zsubst_zAtom (s a t : V) : zsubst (zAtom s) a t = zAtom (fvSubstSeqt a t s) := by
  rw [zsubst_eq_zsubstNext a t (by simp [zAtom]), zsubstNext]; simp [zTag_zAtom]

@[simp] lemma zsubst_zIall (s e p d0 a t : V) :
    zsubst (zIall s e p d0) a t =
      zIall (fvSubstSeqt a t s) e (fvSubst ℒₒᵣ a t p) (zsubst d0 a t) := by
  rw [zsubst_eq_zsubstNext a t (by simp [zIall]), zsubstNext, if_neg (by simp), if_pos (zTag_zIall s e p d0)]
  simp only [fstIdx_zIall, zIallEig_zIall, zIallF_zIall, zIallPrem_zIall]
  rw [znth_zsubstTable_eq_zsubst a t _ d0 (le_pred_of_lt (d0_lt_zIall s e p d0))]

@[simp] lemma zsubst_zIneg (s p d0 a t : V) :
    zsubst (zIneg s p d0) a t = zIneg (fvSubstSeqt a t s) (fvSubst ℒₒᵣ a t p) (zsubst d0 a t) := by
  rw [zsubst_eq_zsubstNext a t (by simp [zIneg]), zsubstNext, if_neg (by simp), if_neg (by simp),
    if_pos (zTag_zIneg s p d0)]
  simp only [fstIdx_zIneg, zInegF_zIneg, zInegPrem_zIneg]
  rw [znth_zsubstTable_eq_zsubst a t _ d0 (le_pred_of_lt (d0_lt_zIneg s p d0))]

@[simp] lemma zsubst_zInd (s e u p d0 d1 a t : V) :
    zsubst (zInd s ⟪e, u⟫ p d0 d1) a t =
      zInd (fvSubstSeqt a t s) ⟪e, termFvSubst ℒₒᵣ a t u⟫ (fvSubst ℒₒᵣ a t p)
        (zsubst d0 a t) (zsubst d1 a t) := by
  rw [zsubst_eq_zsubstNext a t (by simp [zInd]), zsubstNext, if_neg (by simp), if_neg (by simp),
    if_neg (by simp), if_pos (zTag_zInd s _ p d0 d1)]
  simp only [fstIdx_zInd, zIndEig_zInd, zIndTerm_zInd, zIndP_zInd, zIndPrem0_zInd, zIndPrem1_zInd,
    pi₁_pair, pi₂_pair]
  rw [znth_zsubstTable_eq_zsubst a t _ d0 (le_pred_of_lt (d0_lt_zInd s _ p d0 d1)),
    znth_zsubstTable_eq_zsubst a t _ d1 (le_pred_of_lt (d1_lt_zInd s _ p d0 d1))]

@[simp] lemma zsubst_zK (s r ds a t : V) :
    zsubst (zK s r ds) a t = zK (fvSubstSeqt a t s) r (tblMapSeq (zsubstTable a t (zK s r ds - 1)) ds) := by
  rw [zsubst_eq_zsubstNext a t (by simp [zK]), zsubstNext, if_neg (by simp), if_neg (by simp),
    if_neg (by simp), if_neg (by simp), if_pos (zTag_zK s r ds)]
  simp only [fstIdx_zK, zKrank_zK, zKseq_zK]

@[simp] lemma zsubst_zAxAll (s p k a t : V) :
    zsubst (zAxAll s p k) a t = zAxAll (fvSubstSeqt a t s) (fvSubst ℒₒᵣ a t p) k := by
  rw [zsubst_eq_zsubstNext a t (by simp [zAxAll]), zsubstNext, if_neg (by simp), if_neg (by simp),
    if_neg (by simp), if_neg (by simp), if_neg (by simp), if_pos (zTag_zAxAll s p k)]
  simp only [fstIdx_zAxAll, zAxAllF_zAxAll, zAxAllK_zAxAll]

@[simp] lemma zsubst_zAxNeg (s p a t : V) :
    zsubst (zAxNeg s p) a t = zAxNeg (fvSubstSeqt a t s) (fvSubst ℒₒᵣ a t p) := by
  rw [zsubst_eq_zsubstNext a t (by simp [zAxNeg]), zsubstNext, if_neg (by simp), if_neg (by simp),
    if_neg (by simp), if_neg (by simp), if_neg (by simp), if_neg (by simp), if_pos (zTag_zAxNeg s p)]
  simp only [fstIdx_zAxNeg, zAxNegF_zAxNeg]

@[simp] lemma zsubst_zAx1 (s C a t : V) :
    zsubst (zAx1 s C) a t = zAx1 (fvSubstSeqt a t s) C := by
  rw [zsubst_eq_zsubstNext a t (by simp [zAx1]), zsubstNext, if_neg (by simp), if_neg (by simp),
    if_neg (by simp), if_neg (by simp), if_neg (by simp), if_neg (by simp), if_neg (by simp),
    if_pos (zTag_zAx1 s C)]
  simp only [fstIdx_zAx1, zAx1F_zAx1]

/-! ### `fstIdx_zsubst` — the end-sequent of the substituted derivation computes (rung-1 step 1)

For any genuine Z-derivation `d`, the reduct's end-sequent is the substituted end-sequent. Proven by
the 7-way `ZDerivation` case split (each constructor's recursion equation + `fstIdx (z* s' …) = s'`). -/

lemma fstIdx_zsubst {d : V} (a t : V) (hZ : ZDerivation d) :
    fstIdx (zsubst d a t) = fvSubstSeqt a t (fstIdx d) := by
  rcases zDerivation_iff.mp hZ with ⟨s, rfl, _⟩ | ⟨s, e, p, d0, rfl, _, _⟩ | ⟨s, p, d0, rfl, _, _⟩ |
    ⟨s, at', p, d0, d1, rfl, _, _⟩ | ⟨s, r, ds, rfl, _, _, _⟩ |
    ⟨s, p, k, rfl, _, _⟩ | ⟨s, p, rfl, _, _⟩ | ⟨s, C, rfl, _⟩
  · rw [zsubst_zAtom, fstIdx_zAtom, fstIdx_zAtom]
  · rw [zsubst_zIall, fstIdx_zIall, fstIdx_zIall]
  · rw [zsubst_zIneg, fstIdx_zIneg, fstIdx_zIneg]
  · rw [show at' = ⟪π₁ at', π₂ at'⟫ from (pair_unpair at').symm, zsubst_zInd, fstIdx_zInd, fstIdx_zInd]
  · rw [zsubst_zK, fstIdx_zK, fstIdx_zK]
  · rw [zsubst_zAxAll, fstIdx_zAxAll, fstIdx_zAxAll]
  · rw [zsubst_zAxNeg, fstIdx_zAxNeg, fstIdx_zAxNeg]
  · rw [zsubst_zAx1, fstIdx_zAx1, fstIdx_zAx1]

/-! ## Substitution-commutation substrate for `ZDerivation_zsubst` (rung-1 step 2)

The per-Z-rule transfer lemmas the genuine correctness `ZDerivation_zsubst` will consume:
* `inAnt_fvSubstSeq` — antecedent membership is preserved (atom + Ax cases; no freshness needed).
* `fvSubst_inegF` — `fvSubst` commutes with `inegF` (the `zIneg`/`zAxNeg` succedent). -/

/-- **Antecedent membership transfers under `fvSubstSeq`.** If `A ∈ Γ` (positionally) then
`fvSubst a t A ∈ fvSubstSeq a t Γ` — the atom-rule and ∀/¬-axiom cases of `ZDerivation_zsubst`. -/
lemma inAnt_fvSubstSeq {a t A Γ : V} (h : inAnt A Γ) :
    inAnt (fvSubst ℒₒᵣ a t A) (fvSubstSeq a t Γ) := by
  obtain ⟨i, hi, hA⟩ := h
  exact ⟨i, by rw [fvSubstSeq_lh]; exact hi, by rw [znth_fvSubstSeq hi, hA]⟩

/-- **`fvSubst` commutes with `inegF`** (`inegF p = ∼p ⋎ ⊥`), via `fvSubst_neg`. Needed to transfer the
`zIneg` conclusion succedent `inegF p` under eigenvariable substitution. -/
lemma fvSubst_inegF {a t p : V} (ht : IsUTerm ℒₒᵣ t) (hp : IsUFormula ℒₒᵣ p) :
    fvSubst ℒₒᵣ a t (inegF p) = inegF (fvSubst ℒₒᵣ a t p) := by
  unfold inegF
  rw [fvSubst_or hp.neg (by simp), fvSubst_neg ht hp]
  simp

/-! ## Term-substitution helpers for the `zInd` succedent terms (rung-1 step A)

The `zInd` rule's three succedent terms — `numeral 0`, `Sa = ^&e ^+ numeral 1` (`e` the eigenvariable,
`e ≠ a`), and the conclusion term `zIndTerm d` — must be transferred through `termFvSubst a t`. The
`numeral`/`Sa` cases are FIXED by `e ≠ a`-freshness (they contain no `^&a`); only `zIndTerm d` is
genuinely renamed (its closedness is supplied by the `zIndWff` conjunct). -/

/-- `termFvSubst` commutes with `qqAdd` (binary `+` function node). `termFvSubst_func` carries
hypotheses so it does not auto-fire in a bare `simp`; we discharge `IsFunc 2 addIndex` /
`IsUTermVec 2 ?[x,y]` explicitly. -/
lemma termFvSubst_qqAdd (a t x y : V) (hx : IsUTerm ℒₒᵣ x) (hy : IsUTerm ℒₒᵣ y) :
    termFvSubst ℒₒᵣ a t (x ^+ y) = (termFvSubst ℒₒᵣ a t x) ^+ (termFvSubst ℒₒᵣ a t y) := by
  have hf := Bootstrapping.Arithmetic.LOR_func_addIndex (V := V)
  have hv : IsUTermVec ℒₒᵣ 2 (?[x, y] : V) := (IsUTermVec.mkSeq₂_iff (L := ℒₒᵣ)).mpr ⟨hx, hy⟩
  simp only [Bootstrapping.Arithmetic.qqAdd]
  rw [termFvSubst_func (L := ℒₒᵣ) hf hv]
  congr 1
  rw [show (2 : V) = 1 + 1 from (one_add_one_eq_two).symm,
    termFvSubstVec_cons hx ((IsUTermVec.adjoin₁_iff (L := ℒₒᵣ)).mpr hy),
    show (1 : V) = 0 + 1 from (zero_add 1).symm, termFvSubstVec_cons hy (IsUTermVec.empty (L := ℒₒᵣ)),
    termFvSubstVec_nil (L := ℒₒᵣ)]

/-- `termFvSubst` fixes any numeral (numerals contain no free variables). Mirrors `numeral_substs`. -/
@[simp] lemma termFvSubst_numeral (a t x : V) :
    termFvSubst ℒₒᵣ a t (Bootstrapping.Arithmetic.numeral x) = Bootstrapping.Arithmetic.numeral x := by
  induction x using ISigma1.sigma1_succ_induction
  · definability
  case zero =>
    simp [Bootstrapping.Arithmetic.zero,
      Bootstrapping.Arithmetic.qqFunc_absolute, Bootstrapping.qqFuncN_eq_qqFunc]
  case succ x ih =>
    rcases zero_or_succ x with (rfl | ⟨x, rfl⟩)
    · simp [Bootstrapping.Arithmetic.one,
        Bootstrapping.Arithmetic.qqFunc_absolute, Bootstrapping.qqFuncN_eq_qqFunc]
    · rw [Bootstrapping.Arithmetic.numeral_add_two,
        termFvSubst_qqAdd a t _ _ (by simp)
          (Bootstrapping.Arithmetic.one_semiterm (V := V) (n := 0)).isUTerm, ih]
      congr 1
      simp [Bootstrapping.Arithmetic.one,
        Bootstrapping.Arithmetic.qqFunc_absolute, Bootstrapping.qqFuncN_eq_qqFunc]

/-- The `zInd` minor-premise succedent term `Sa = ^&e ^+ numeral 1` is fixed by `termFvSubst a t`
provided the eigenvariable `e ≠ a` (Buchholz regularity). -/
lemma termFvSubst_succVar {a t e : V} (he : e ≠ a) :
    termFvSubst ℒₒᵣ a t (^&e ^+ Bootstrapping.Arithmetic.numeral 1) =
      ^&e ^+ Bootstrapping.Arithmetic.numeral 1 := by
  rw [termFvSubst_qqAdd _ _ _ _ ((IsSemiterm.fvar (L := ℒₒᵣ) 0 e).isUTerm)
      (Bootstrapping.Arithmetic.numeral_uterm 1), termFvSubst_fvar_ne (L := ℒₒᵣ) he,
      termFvSubst_numeral]

/-- `Sa = ^&e ^+ numeral 1` is a closed semiterm. -/
@[simp] lemma isSemiterm_succVar (e : V) :
    IsSemiterm ℒₒᵣ 0 (^&e ^+ Bootstrapping.Arithmetic.numeral 1) := by
  have hf := Bootstrapping.Arithmetic.LOR_func_addIndex (V := V)
  rw [Bootstrapping.Arithmetic.qqAdd]
  exact (IsSemiterm.func (L := ℒₒᵣ)).mpr ⟨hf,
    (IsSemitermVec.doubleton (L := ℒₒᵣ)).mpr ⟨IsSemiterm.fvar 0 e, by simp⟩⟩

/-! ## Substitution-invariants for the `zK` chain-validity transfer (rung-1 step C.zK groundwork)

`zKValid` subst-invariance reads the chain through `irk`/`tp`/`iperm`/`isChainInf`; the foundational
fact is that `fvSubst` (substituting a closed term for a free variable) leaves the **logical complexity**
`irk` unchanged — it only touches atomic subterms. -/

/-- **`irk` is invariant under `fvSubst`** (`rk` counts logical structure; substituting a closed term for
a free variable touches only atoms). The rank ingredient of `isChainInf` subst-invariance. -/
lemma irk_fvSubst {a t : V} (ht : IsUTerm ℒₒᵣ t) {A : V} :
    IsUFormula ℒₒᵣ A → irk (fvSubst ℒₒᵣ a t A) = irk A := by
  apply IsUFormula.ISigma1.sigma1_succ_induction
  · definability
  · intro k r v hr hv
    rw [fvSubst_rel hr hv, irk_rel hr (IsUTermVec.termFvSubst ht hv), irk_rel hr hv]
  · intro k r v hr hv
    rw [fvSubst_nrel hr hv, irk_nrel hr (IsUTermVec.termFvSubst ht hv), irk_nrel hr hv]
  · simp
  · simp
  · intro p q hp hq ihp ihq
    rw [fvSubst_and hp hq, irk_and (IsUFormula.fvSubst ht hp) (IsUFormula.fvSubst ht hq),
      irk_and hp hq, ihp, ihq]
  · intro p q hp hq ihp ihq
    rw [fvSubst_or hp hq, irk_or (IsUFormula.fvSubst ht hp) (IsUFormula.fvSubst ht hq),
      irk_or hp hq, ihp, ihq]
  · intro p hp ihp
    rw [fvSubst_all hp, irk_all (IsUFormula.fvSubst ht hp), irk_all hp, ihp]
  · intro p hp ihp
    rw [fvSubst_ex hp, irk_ex (IsUFormula.fvSubst ht hp), irk_ex hp, ihp]

/-- **`zsubst` preserves the rule tag** (for a genuine Z-derivation): substituting a free variable
rebuilds the same Z-rule, so `zTag` is unchanged. Feeds the tag-gated formula-hood conjuncts of the
`zKValid` chain-validity transfer. -/
@[simp] lemma zTag_zsubst {a t : V} {d : V} (hd : ZDerivation d) :
    zTag (zsubst d a t) = zTag d := by
  rcases zDerivation_iff.mp hd with ⟨s, rfl, _⟩ | ⟨s, e, p, d0, rfl, _, _, _⟩ |
    ⟨s, p, d0, rfl, _, _, _⟩ | ⟨s, at', p, d0, d1, rfl, _, _, _⟩ |
    ⟨s, r, ds, rfl, _, _, _⟩ | ⟨s, p, k, rfl, _, _⟩ | ⟨s, p, rfl, _, _⟩ | ⟨s, C, rfl, _⟩
  · rw [zsubst_zAtom]; simp
  · rw [zsubst_zIall]; simp
  · rw [zsubst_zIneg]; simp
  · rw [show at' = ⟪π₁ at', π₂ at'⟫ from (pair_unpair at').symm, zsubst_zInd]; simp
  · rw [zsubst_zK]; simp
  · rw [zsubst_zAxAll]; simp
  · rw [zsubst_zAxNeg]; simp
  · rw [zsubst_zAx1]; simp

/-- **Permissibility (`iperm`, Lemma 3.3) transfers under `fvSubst`.** For a genuine Z-derivation `d`,
if its rule symbol `tp d` permits a sequent `q`, then the substituted symbol `tp (zsubst d a t)` permits
the substituted sequent `fvSubstSeqt a t q`. The principal formula (R-symbol succedent / L-symbol cut
formula) and the sequent's succedent/antecedent transform CONSISTENTLY by `fvSubst`, so the match is
preserved. This is the **positive** (`iperm`) conjunct of the `zKValid` chain-validity transfer; the
**criticality** (`¬iperm` vs the chain conclusion `s`) does NOT transfer this cleanly — `fvSubst` can
collapse a previously-distinct principal-formula/conclusion pair (e.g. `^∀F(^&a)` vs `^∀F(t)`), so a
spurious match can appear. Closing the `zK` case of `ZDerivation_zsubst` therefore needs an
eigenvariable-freshness hypothesis (`a ∉ FV(s)`); see `PENDING_WORK`. -/
lemma iperm_tp_zsubst {a t : V} (ht : IsSemiterm ℒₒᵣ 0 t) {d q : V} (hd : ZDerivation d)
    (h : iperm (tp d) q) : iperm (tp (zsubst d a t)) (fvSubstSeqt a t q) := by
  rcases zDerivation_iff.mp hd with ⟨s, rfl, _⟩ | ⟨s, e, p, d0, rfl, _, _, hwff⟩ |
    ⟨s, p, d0, rfl, _, _, hwff⟩ | ⟨s, at', p, d0, d1, rfl, _, _, _⟩ |
    ⟨s, r, ds, rfl, _, _, _⟩ | ⟨s, p, k, rfl, hp, _⟩ | ⟨s, p, rfl, hp, _⟩ | ⟨s, C, rfl, _⟩
  · rw [zsubst_zAtom, tp_zAtom]; exact iperm_isymRep _
  · rw [zsubst_zIall, tp_zIall]; rw [tp_zIall] at h
    refine iperm_isymR_iff.mpr ?_
    rw [seqSucc_fvSubstSeqt, ← iperm_isymR_iff.mp h, fvSubst_all hwff.2.2.isUFormula]
  · rw [zsubst_zIneg, tp_zIneg]; rw [tp_zIneg] at h
    refine iperm_isymR_iff.mpr ?_
    rw [seqSucc_fvSubstSeqt, ← iperm_isymR_iff.mp h, fvSubst_inegF ht.isUTerm hwff.2.2]
  · rw [show at' = ⟪π₁ at', π₂ at'⟫ from (pair_unpair at').symm, zsubst_zInd, tp_zInd]
    exact iperm_isymRep _
  · rw [zsubst_zK, tp_zK]; exact iperm_isymRep _
  · rw [zsubst_zAxAll, tp_zAxAll]; rw [tp_zAxAll] at h
    refine iperm_isymLk_iff.mpr ?_
    rw [seqAnt_fvSubstSeqt, ← fvSubst_all hp]
    exact inAnt_fvSubstSeq (iperm_isymLk_iff.mp h)
  · rw [zsubst_zAxNeg, tp_zAxNeg]; rw [tp_zAxNeg] at h
    refine iperm_isymLk_iff.mpr ?_
    rw [seqAnt_fvSubstSeqt, ← fvSubst_inegF ht.isUTerm hp]
    exact inAnt_fvSubstSeq (iperm_isymLk_iff.mp h)
  · rw [zsubst_zAx1, tp_zAx1]; exact iperm_isymRep _

/-- **`isChainInf` transfers under eigenvariable substitution** (the chain-structure conjunct of
`zKValid`). Given a chain `s r ds` whose premises are Z-derivations and whose succedents are genuine
formulas, the substituted chain `(fvSubstSeqt a t s) r ds'` — where `ds'` lists `zsubst (znth ds i) a t`
— is still a valid `isChainInf`. The point is that every condition is **positive** (closed under
applying `fvSubst`), so they are *preserved by the consistent substitution*, NOT merely vacuously fixed:
the `A_{j₀}∈{C,⊥}` condition by `fvSubst_falsum` + congruence, the antecedent threading by
`inAnt_fvSubstSeq`, and the rank bound by `irk_fvSubst` (rank invariance — this is the one conjunct that
consumes the succedent formula-hood `hcf`). This corrects the lap-76 worry: the chain *structure*
transfers cleanly; only the `zKValid` **criticality** conjunct (a negative `¬iperm`) is delicate. -/
lemma isChainInf_zsubst {a t s r ds ds' : V} (ht : IsUTerm ℒₒᵣ t)
    (hlh : lh ds' = lh ds)
    (hZ : ∀ i < lh ds, ZDerivation (znth ds i))
    (hmap : ∀ i < lh ds, znth ds' i = zsubst (znth ds i) a t)
    (hcf : ∀ i < lh ds, IsUFormula ℒₒᵣ (chainAsucc ds i))
    (h : isChainInf s r ds) :
    isChainInf (fvSubstSeqt a t s) r ds' := by
  have hAsucc : ∀ i < lh ds, chainAsucc ds' i = fvSubst ℒₒᵣ a t (chainAsucc ds i) := by
    intro i hi
    rw [chainAsucc, chainAsucc, hmap i hi, fstIdx_zsubst a t (hZ i hi), seqSucc_fvSubstSeqt]
  have hAnt : ∀ i < lh ds, chainAnt ds' i = fvSubstSeq a t (chainAnt ds i) := by
    intro i hi
    rw [chainAnt, chainAnt, hmap i hi, fstIdx_zsubst a t (hZ i hi), seqAnt_fvSubstSeqt]
  rw [isChainInf_iff_idx] at h ⊢
  obtain ⟨j0, hj0, hcond, hthread, hrank⟩ := h
  refine ⟨j0, by rw [hlh]; exact hj0, ?_, ?_, ?_⟩
  · -- A_{j₀} ∈ {C, ⊥} (formula-hood-free)
    rcases hcond with hc | hc
    · left; rw [hAsucc j0 hj0, hc, seqSucc_fvSubstSeqt]
    · right; rw [hAsucc j0 hj0, hc]; exact fvSubst_falsum
  · -- antecedent threading (formula-hood-free)
    intro i hi k hk
    have hilt : i < lh ds := lt_of_le_of_lt hi hj0
    have hkk : k < lh (chainAnt ds i) := by
      rwa [hAnt i hilt, fvSubstSeq_lh] at hk
    rw [hAnt i hilt, znth_fvSubstSeq hkk]
    rcases hthread i hi k hkk with hin | ⟨i', hi'lt, heq⟩
    · left; rw [seqAnt_fvSubstSeqt]; exact inAnt_fvSubstSeq hin
    · right
      refine ⟨i', hi'lt, ?_⟩
      rw [heq, hAsucc i' (lt_trans hi'lt hilt)]
  · -- rank bound (consumes succedent formula-hood via irk_fvSubst)
    intro i hi
    have hilt : i < lh ds := lt_trans hi hj0
    rw [hAsucc i hilt, irk_fvSubst ht (hcf i hilt)]
    exact hrank i hi

/-- **Reflection of `inAnt` through `fvSubstSeq`** on an `a`-free formula sequence: if `A` occurs in the
substituted antecedent `fvSubstSeq a t Γ` and every entry of `Γ ≤ a` is a genuine formula, then `A`
already occurs in `Γ`. The reverse of `inAnt_fvSubstSeq` — its entries are `a`-free so `fvSubst` fixes
them. The load-bearing step of the `zK`-criticality transfer's L-symbol case. -/
lemma inAnt_fvSubstSeq_reflect {a t A Γ : V} (hΓ : Γ ≤ a)
    (hfs : ∀ k < lh Γ, IsUFormula ℒₒᵣ (znth Γ k))
    (h : inAnt A (fvSubstSeq a t Γ)) : inAnt A Γ := by
  obtain ⟨i, hi, hA⟩ := h
  rw [fvSubstSeq_lh] at hi
  rw [znth_fvSubstSeq hi, fvSubst_eq_self_of_le (hfs i hi)
    (le_trans (znth_le_self Γ i) hΓ)] at hA
  exact ⟨i, hi, hA⟩

/-- **`tp` is invariant under eigenvariable substitution on an `a`-free derivation** (`d ≤ a`): the
principal formula is `≤ a` hence `^&a`-free, so `fvSubst` fixes it and the inference symbol is unchanged. -/
lemma tp_zsubst_eq {a t : V} (ht : IsSemiterm ℒₒᵣ 0 t) {d : V} (hd : ZDerivation d) (hda : d ≤ a) :
    tp (zsubst d a t) = tp d := by
  rcases zDerivation_iff.mp hd with ⟨s, rfl, _⟩ | ⟨s, e, p, d0, rfl, _, _, hwff⟩ |
    ⟨s, p, d0, rfl, _, _, hwff⟩ | ⟨s, at', p, d0, d1, rfl, _, _, _⟩ |
    ⟨s, r, ds, rfl, _, _, _⟩ | ⟨s, p, k, rfl, hp, _⟩ | ⟨s, p, rfl, hp, _⟩ | ⟨s, C, rfl, _⟩
  · simp only [zsubst_zAtom, tp_zAtom]
  · rw [zsubst_zIall, tp_zIall, tp_zIall,
      fvSubst_eq_self_of_le hwff.2.2.isUFormula (le_of_lt (lt_of_lt_of_le (p_lt_zIall s e p d0) hda))]
  · rw [zsubst_zIneg, tp_zIneg, tp_zIneg,
      fvSubst_eq_self_of_le hwff.2.2 (le_of_lt (lt_of_lt_of_le (p_lt_zIneg s p d0) hda))]
  · rw [show at' = ⟪π₁ at', π₂ at'⟫ from (pair_unpair at').symm]
    simp only [zsubst_zInd, tp_zInd]
  · simp only [zsubst_zK, tp_zK]
  · rw [zsubst_zAxAll, tp_zAxAll, tp_zAxAll,
      fvSubst_eq_self_of_le hp (le_of_lt (lt_of_lt_of_le (p_lt_zAxAll s p k) hda))]
  · rw [zsubst_zAxNeg, tp_zAxNeg, tp_zAxNeg,
      fvSubst_eq_self_of_le hp (le_of_lt (lt_of_lt_of_le (p_lt_zAxNeg s p) hda))]
  · simp only [zsubst_zAx1, tp_zAx1]

/-- **Permissibility against an `a`-free well-formed conclusion reflects through substitution.** If the
substituted symbol `I` permits the substituted conclusion `fvSubstSeqt a t s` and `s ≤ a` is a genuine
sequent (succedent + antecedent formulas), then `I` already permits `s`. The conclusion is `^&a`-free so
its succedent/antecedent are fixed by `fvSubst`; the L-symbol case uses `inAnt_fvSubstSeq_reflect`. This
turns the `zKValid` criticality `¬iperm (tp dᵢ) s` into `¬iperm (tp (zsubst dᵢ)) (fvSubstSeqt s)`. -/
lemma iperm_zsubst_conclusion {a t s I : V} (hsa : s ≤ a)
    (hssf : IsUFormula ℒₒᵣ (seqSucc s))
    (hsaf : ∀ k < lh (seqAnt s), IsUFormula ℒₒᵣ (znth (seqAnt s) k))
    (h : iperm I (fvSubstSeqt a t s)) : iperm I s := by
  rcases h with hR | ⟨k, A, rfl, hA⟩ | hrep
  · refine Or.inl ?_
    rw [hR, seqSucc_fvSubstSeqt, fvSubst_eq_self_of_le hssf (le_trans (pi₂_le_self s) hsa)]
  · rw [seqAnt_fvSubstSeqt] at hA
    exact Or.inr (Or.inl ⟨k, A, rfl,
      inAnt_fvSubstSeq_reflect (le_trans (pi₁_le_self s) hsa) hsaf hA⟩)
  · exact Or.inr (Or.inr hrep)

/-- Principal-formula read-out under substitution (tag 1): `zIallF` commutes with `zsubst`. -/
lemma zIallF_zsubst {a t d : V} (hd : ZDerivation d) (h : zTag d = 1) :
    zIallF (zsubst d a t) = fvSubst ℒₒᵣ a t (zIallF d) := by
  rcases zDerivation_iff.mp hd with ⟨s, rfl, _⟩ | ⟨s, e, p, d0, rfl, _, _, _⟩ |
    ⟨s, p, d0, rfl, _, _, _⟩ | ⟨s, at', p, d0, d1, rfl, _, _, _⟩ |
    ⟨s, r, ds, rfl, _, _, _⟩ | ⟨s, p, k, rfl, _, _⟩ | ⟨s, p, rfl, _, _⟩ | ⟨s, C, rfl, _⟩
  · simp at h
  · rw [zsubst_zIall]; simp
  · simp at h
  · simp at h
  · simp at h
  · simp at h
  · simp at h
  · simp at h

/-- Principal-formula read-out under substitution (tag 2): `zInegF` commutes with `zsubst`. -/
lemma zInegF_zsubst {a t d : V} (hd : ZDerivation d) (h : zTag d = 2) :
    zInegF (zsubst d a t) = fvSubst ℒₒᵣ a t (zInegF d) := by
  rcases zDerivation_iff.mp hd with ⟨s, rfl, _⟩ | ⟨s, e, p, d0, rfl, _, _, _⟩ |
    ⟨s, p, d0, rfl, _, _, _⟩ | ⟨s, at', p, d0, d1, rfl, _, _, _⟩ |
    ⟨s, r, ds, rfl, _, _, _⟩ | ⟨s, p, k, rfl, _, _⟩ | ⟨s, p, rfl, _, _⟩ | ⟨s, C, rfl, _⟩
  · simp at h
  · simp at h
  · rw [zsubst_zIneg]; simp
  · simp at h
  · simp at h
  · simp at h
  · simp at h
  · simp at h

/-- Principal-formula read-out under substitution (tag 5): `zAxAllF` commutes with `zsubst`. -/
lemma zAxAllF_zsubst {a t d : V} (hd : ZDerivation d) (h : zTag d = 5) :
    zAxAllF (zsubst d a t) = fvSubst ℒₒᵣ a t (zAxAllF d) := by
  rcases zDerivation_iff.mp hd with ⟨s, rfl, _⟩ | ⟨s, e, p, d0, rfl, _, _, _⟩ |
    ⟨s, p, d0, rfl, _, _, _⟩ | ⟨s, at', p, d0, d1, rfl, _, _, _⟩ |
    ⟨s, r, ds, rfl, _, _, _⟩ | ⟨s, p, k, rfl, _, _⟩ | ⟨s, p, rfl, _, _⟩ | ⟨s, C, rfl, _⟩
  · simp at h
  · simp at h
  · simp at h
  · simp at h
  · simp at h
  · rw [zsubst_zAxAll]; simp
  · simp at h
  · simp at h

/-- Principal-formula read-out under substitution (tag 6): `zAxNegF` commutes with `zsubst`. -/
lemma zAxNegF_zsubst {a t d : V} (hd : ZDerivation d) (h : zTag d = 6) :
    zAxNegF (zsubst d a t) = fvSubst ℒₒᵣ a t (zAxNegF d) := by
  rcases zDerivation_iff.mp hd with ⟨s, rfl, _⟩ | ⟨s, e, p, d0, rfl, _, _, _⟩ |
    ⟨s, p, d0, rfl, _, _, _⟩ | ⟨s, at', p, d0, d1, rfl, _, _, _⟩ |
    ⟨s, r, ds, rfl, _, _, _⟩ | ⟨s, p, k, rfl, _, _⟩ | ⟨s, p, rfl, _, _⟩ | ⟨s, C, rfl, _⟩
  · simp at h
  · simp at h
  · simp at h
  · simp at h
  · simp at h
  · simp at h
  · rw [zsubst_zAxNeg]; simp
  · simp at h


/-! ## `maxEigen` — the largest eigenvariable index in a derivation (Path-X freshness foundation)

`maxEigen d` = the maximum eigenvariable index over all `zIall`/`zInd` nodes of `d` (0 if none). Built by
the exact `idg` table template (`InternalZ.lean`): `maxEigenNext d s` reads the premise results out of the
running table `s` and folds in this node's own eigenvariable. The point (lap-92 DECISION): a freshness
invariant phrased on `maxEigen` is **stable under `zsubst`** (closed-term substitution preserves the
eigenvariable binders), unlike the code bound `d ≤ a` — so it is maintainable through `red`. -/

noncomputable def maxEigenNext (d s : V) : V :=
  if zTag d = 1 then max (zIallEig d) (znth s (zIallPrem d))
  else if zTag d = 2 then znth s (zInegPrem d)
  else if zTag d = 3 then
    max (zIndEig d) (max (znth s (zIndPrem0 d)) (znth s (zIndPrem1 d)))
  else if zTag d = 4 then iseqMaxTab s (zKseq d)
  else 0

noncomputable def _root_.LO.FirstOrder.Arithmetic.maxEigenNextDef : 𝚺₁.Semisentence 3 := .mkSigma
  “y d s. ∃ t, !zTagDef t d ∧
    ( (t = 1 ∧ ∃ ea, !zIallEigDef ea d ∧ ∃ p, !zIallPremDef p d ∧ ∃ v, !znthDef v s p ∧ !max.dfn y ea v)
    ∨ (t = 2 ∧ ∃ p, !zInegPremDef p d ∧ !znthDef y s p)
    ∨ (t = 3 ∧ ∃ ie, !zIndEigDef ie d ∧ ∃ p0, !zIndPrem0Def p0 d ∧ ∃ v0, !znthDef v0 s p0 ∧
        ∃ p1, !zIndPrem1Def p1 d ∧ ∃ v1, !znthDef v1 s p1 ∧ ∃ m, !max.dfn m v0 v1 ∧ !max.dfn y ie m)
    ∨ (t = 4 ∧ ∃ ds, !zKseqDef ds d ∧ !iseqMaxTabDef y s ds)
    ∨ (t ≠ 1 ∧ t ≠ 2 ∧ t ≠ 3 ∧ t ≠ 4 ∧ y = 0) )”

set_option maxHeartbeats 1000000 in
instance maxEigenNext_defined : 𝚺₁-Function₂ (maxEigenNext : V → V → V) via maxEigenNextDef :=
  .mk fun v ↦ by
    simp [maxEigenNextDef, maxEigenNext, zTag_defined.iff, zIallEig_defined.iff,
      zIallPrem_defined.iff, zInegPrem_defined.iff, zIndEig_defined.iff, zIndPrem0_defined.iff,
      zIndPrem1_defined.iff, zKseq_defined.iff, iseqMaxTab_defined.iff, znth_defined.iff,
      max_defined.iff]
    by_cases h1 : zTag (v 1) = 1
    · simp [h1]
    · by_cases h2 : zTag (v 1) = 2
      · simp [h1, h2]
      · by_cases h3 : zTag (v 1) = 3
        · simp [h1, h2, h3]
        · by_cases h4 : zTag (v 1) = 4
          · simp [h1, h2, h3, h4]
          · simp [h1, h2, h3, h4]

instance maxEigenNext_definable : 𝚺₁-Function₂ (maxEigenNext : V → V → V) :=
  maxEigenNext_defined.to_definable

/-- Blueprint for the `maxEigen` table. -/
noncomputable def maxEigenTable.blueprint : PR.Blueprint 0 where
  zero := .mkSigma “y. !mkSeq₁Def y 0”
  succ := .mkSigma “y ih n. ∃ v, !maxEigenNextDef v (n + 1) ih ∧ !seqConsDef y ih v”

noncomputable def maxEigenTable.construction : PR.Construction V maxEigenTable.blueprint where
  zero := fun _ ↦ !⟦0⟧
  succ := fun _ n ih ↦ seqCons ih (maxEigenNext (n + 1) ih)
  zero_defined := .mk fun v ↦ by
    simp [maxEigenTable.blueprint, mkSeq₁Def, seqCons_defined.iff, emptyset_def]
  succ_defined := .mk fun v ↦ by
    simp [maxEigenTable.blueprint, maxEigenNext_defined.iff, seqCons_defined.iff]

/-- **The `maxEigen` table**: `maxEigenTable n = ⟨maxEigen 0,…,maxEigen n⟩` (length `n+1`). -/
noncomputable def maxEigenTable (n : V) : V := maxEigenTable.construction.result ![] n

@[simp] lemma maxEigenTable_zero : maxEigenTable (0 : V) = !⟦0⟧ := by
  simp [maxEigenTable, maxEigenTable.construction]

@[simp] lemma maxEigenTable_succ (n : V) :
    maxEigenTable (n + 1) = seqCons (maxEigenTable n) (maxEigenNext (n + 1) (maxEigenTable n)) := by
  simp [maxEigenTable, maxEigenTable.construction]

/-- **Largest eigenvariable index** `maxEigen d`: the `d`-th entry of the table. -/
noncomputable def maxEigen (d : V) : V := znth (maxEigenTable d) d

noncomputable def _root_.LO.FirstOrder.Arithmetic.maxEigenTableDef : 𝚺₁.Semisentence 2 :=
  maxEigenTable.blueprint.resultDef.rew (Rew.subst ![#0, #1])

instance maxEigenTable_defined : 𝚺₁-Function₁ (maxEigenTable : V → V) via maxEigenTableDef := .mk
  fun v ↦ by simp [maxEigenTable.construction.result_defined_iff, maxEigenTableDef]; rfl

instance maxEigenTable_definable : 𝚺₁-Function₁ (maxEigenTable : V → V) :=
  maxEigenTable_defined.to_definable
instance maxEigenTable_definable' (Γ) : Γ-[m + 1]-Function₁ (maxEigenTable : V → V) :=
  maxEigenTable_definable.of_sigmaOne

noncomputable def _root_.LO.FirstOrder.Arithmetic.maxEigenDef : 𝚺₁.Semisentence 2 := .mkSigma
  “y d. ∃ t, !maxEigenTableDef t d ∧ !znthDef y t d”

instance maxEigen_defined : 𝚺₁-Function₁ (maxEigen : V → V) via maxEigenDef := .mk fun v ↦ by
  simp [maxEigenDef, maxEigen, maxEigenTable_defined.iff, znth_defined.iff]

instance maxEigen_definable : 𝚺₁-Function₁ (maxEigen : V → V) := maxEigen_defined.to_definable
instance maxEigen_definable' (Γ) : Γ-[m + 1]-Function₁ (maxEigen : V → V) :=
  maxEigen_definable.of_sigmaOne

/-! ### Structural correctness of the `maxEigen` table (mirror `idg`)

Identical course-of-values bookkeeping to `idgTable` (`InternalZ.lean:1920`): the length-`(N+1)`
table `maxEigenTable N` has every in-range entry equal to the genuine `maxEigen` value, so the
table-reduction unfolds to `maxEigen c = maxEigenNext c (maxEigenTable (c-1))` for positive `c`. -/

private lemma def_maxEigenTable {k} (i : Fin k) :
    𝚺-[1].DefinableFunction (fun v : Fin k → V ↦ maxEigenTable (v i)) :=
  DefinableFunction₁.comp (F := maxEigenTable) (DefinableFunction.var i)

private lemma def_maxEigen {k} (i : Fin k) :
    𝚺-[1].DefinableFunction (fun v : Fin k → V ↦ maxEigen (v i)) :=
  DefinableFunction₁.comp (F := maxEigen) (DefinableFunction.var i)

@[simp] lemma maxEigenTable_seq (n : V) : Seq (maxEigenTable n) := by
  induction n using ISigma1.sigma1_succ_induction
  · exact Definable.comp₁ (def_maxEigenTable 0)
  case zero => simp
  case succ n ih => rw [maxEigenTable_succ]; exact ih.seqCons _

@[simp] lemma maxEigenTable_lh (n : V) : lh (maxEigenTable n) = n + 1 := by
  induction n using ISigma1.sigma1_succ_induction
  · exact Definable.comp₂ (DefinableFunction₁.comp (F := lh) (def_maxEigenTable 0)) (by definability)
  case zero => simp
  case succ n ih => rw [maxEigenTable_succ, Seq.lh_seqCons _ (maxEigenTable_seq n), ih]

lemma znth_maxEigenTable_succ {n k : V} (hk : k < n + 1) :
    znth (maxEigenTable (n + 1)) k = znth (maxEigenTable n) k := by
  rw [maxEigenTable_succ]
  exact znth_seqCons_of_lt (maxEigenTable_seq n) _ (by rw [maxEigenTable_lh]; exact hk)

/-- **Table stability**: every entry of the length-`(N+1)` table is the genuine `maxEigen` value. -/
lemma znth_maxEigenTable_eq_maxEigen : ∀ N : V, ∀ k ≤ N, znth (maxEigenTable N) k = maxEigen k := by
  intro N
  induction N using ISigma1.sigma1_succ_induction
  · refine Definable.ball_le (by definability) ?_
    exact Definable.comp₂
      (DefinableFunction₂.comp (F := znth) (def_maxEigenTable 1) (DefinableFunction.var 0))
      (def_maxEigen 0)
  case zero =>
    intro k hk; rcases (nonpos_iff_eq_zero.mp hk) with rfl; rfl
  case succ N ih =>
    intro k hk
    rcases eq_or_lt_of_le hk with rfl | hlt
    · rfl
    · rw [znth_maxEigenTable_succ hlt]; exact ih k (le_iff_lt_succ.mpr hlt)

/-- `maxEigen c = maxEigenNext c (maxEigenTable (c-1))` for positive codes. -/
lemma maxEigen_eq_maxEigenNext {c : V} (hpos : 0 < c) :
    maxEigen c = maxEigenNext c (maxEigenTable (c - 1)) := by
  obtain ⟨M, rfl⟩ : ∃ M, c = M + 1 := ⟨c - 1, (sub_add_self_of_le (pos_iff_one_le.mp hpos)).symm⟩
  have key : znth (maxEigenTable (M + 1)) (M + 1) = maxEigenNext (M + 1) (maxEigenTable M) := by
    rw [maxEigenTable_succ]
    have h := znth_seqCons_self (maxEigenTable_seq M) (maxEigenNext (M + 1) (maxEigenTable M))
    rwa [maxEigenTable_lh] at h
  simp only [maxEigen, add_tsub_cancel_right, key]

/-! ### `maxEigen` recursion equations (Path-X freshness foundation)

The largest eigenvariable index folds structurally: each `zIall`/`zInd` node contributes its own
eigenvariable; chains/negations/atoms/axioms contribute nothing of their own. These mirror the
`idg` recursion equations one-for-one. The point (lap-92 DECISION): combined with
`maxEigen_zsubst` (next) these make a `maxEigen`-phrased freshness invariant maintainable. -/

@[simp] lemma maxEigen_zAtom (s : V) : maxEigen (zAtom s) = 0 := by
  rw [maxEigen_eq_maxEigenNext (by simp [zAtom]), maxEigenNext]; simp [zTag_zAtom]

@[simp] lemma maxEigen_zIall (s a p d0 : V) :
    maxEigen (zIall s a p d0) = max a (maxEigen d0) := by
  rw [maxEigen_eq_maxEigenNext (by simp [zIall]), maxEigenNext, if_pos (zTag_zIall s a p d0),
    zIallEig_zIall, zIallPrem_zIall,
    znth_maxEigenTable_eq_maxEigen _ d0 (le_pred_of_lt (d0_lt_zIall s a p d0))]

@[simp] lemma maxEigen_zIneg (s p d0 : V) : maxEigen (zIneg s p d0) = maxEigen d0 := by
  rw [maxEigen_eq_maxEigenNext (by simp [zIneg]), maxEigenNext, if_neg (by simp),
    if_pos (zTag_zIneg s p d0), zInegPrem_zIneg,
    znth_maxEigenTable_eq_maxEigen _ d0 (le_pred_of_lt (d0_lt_zIneg s p d0))]

@[simp] lemma maxEigen_zInd (s at' p d0 d1 : V) :
    maxEigen (zInd s at' p d0 d1) = max (π₁ at') (max (maxEigen d0) (maxEigen d1)) := by
  rw [maxEigen_eq_maxEigenNext (by simp [zInd]), maxEigenNext, if_neg (by simp), if_neg (by simp),
    if_pos (zTag_zInd s at' p d0 d1), zIndEig_zInd, zIndPrem0_zInd, zIndPrem1_zInd,
    znth_maxEigenTable_eq_maxEigen _ d0 (le_pred_of_lt (d0_lt_zInd s at' p d0 d1)),
    znth_maxEigenTable_eq_maxEigen _ d1 (le_pred_of_lt (d1_lt_zInd s at' p d0 d1))]

@[simp] lemma maxEigen_zAxAll (s p k : V) : maxEigen (zAxAll s p k) = 0 := by
  rw [maxEigen_eq_maxEigenNext (by simp [zAxAll]), maxEigenNext]; simp [zTag_zAxAll]

@[simp] lemma maxEigen_zAxNeg (s p : V) : maxEigen (zAxNeg s p) = 0 := by
  rw [maxEigen_eq_maxEigenNext (by simp [zAxNeg]), maxEigenNext]; simp [zTag_zAxNeg]

@[simp] lemma maxEigen_zAx1 (s C : V) : maxEigen (zAx1 s C) = 0 := by
  rw [maxEigen_eq_maxEigenNext (by simp [zAx1]), maxEigenNext]; simp [zTag_zAx1]

/-! ### `maxEigen`-fold over a premise sequence (for the variadic `K^r` equation)

`iseqMaxEigen ds = max_{i < lh ds} maxEigen(znth ds i)` — the genuine fold (applies `maxEigen`
directly). The `K^r` step in `maxEigenNext` reads the *table* form `iseqMaxTab (maxEigenTable M) ds`;
under dominance the two agree (mirror `iseqMaxIdg`/`idg_zK`). -/

noncomputable def iseqMaxEigenAux.blueprint : PR.Blueprint 1 where
  zero := .mkSigma “y ds. y = 0”
  succ := .mkSigma “y ih n ds.
    ∃ di, !znthDef di ds n ∧ ∃ v, !maxEigenDef v di ∧ !max.dfn y ih v”

noncomputable def iseqMaxEigenAux.construction : PR.Construction V iseqMaxEigenAux.blueprint where
  zero := fun _ ↦ 0
  succ := fun x n ih ↦ max ih (maxEigen (znth (x 0) n))
  zero_defined := .mk fun v ↦ by simp [iseqMaxEigenAux.blueprint]
  succ_defined := .mk fun v ↦ by
    simp [iseqMaxEigenAux.blueprint, znth_defined.iff, maxEigen_defined.iff, max_defined.iff]

/-- Partial fold: `iseqMaxEigenAux ds j = max_{i < j} maxEigen(znth ds i)`. -/
noncomputable def iseqMaxEigenAux (ds j : V) : V := iseqMaxEigenAux.construction.result ![ds] j

@[simp] lemma iseqMaxEigenAux_zero (ds : V) : iseqMaxEigenAux ds 0 = 0 := by
  simp [iseqMaxEigenAux, iseqMaxEigenAux.construction]

@[simp] lemma iseqMaxEigenAux_succ (ds j : V) :
    iseqMaxEigenAux ds (j + 1) = max (iseqMaxEigenAux ds j) (maxEigen (znth ds j)) := by
  simp [iseqMaxEigenAux, iseqMaxEigenAux.construction]

noncomputable def _root_.LO.FirstOrder.Arithmetic.iseqMaxEigenAuxDef : 𝚺₁.Semisentence 3 :=
  iseqMaxEigenAux.blueprint.resultDef.rew (Rew.subst ![#0, #2, #1])

instance iseqMaxEigenAux_defined : 𝚺₁-Function₂ (iseqMaxEigenAux : V → V → V) via iseqMaxEigenAuxDef :=
  .mk fun v ↦ by simp [iseqMaxEigenAux.construction.result_defined_iff, iseqMaxEigenAuxDef]; rfl

instance iseqMaxEigenAux_definable : 𝚺₁-Function₂ (iseqMaxEigenAux : V → V → V) :=
  iseqMaxEigenAux_defined.to_definable
instance iseqMaxEigenAux_definable' (Γ) : Γ-[m + 1]-Function₂ (iseqMaxEigenAux : V → V → V) :=
  iseqMaxEigenAux_definable.of_sigmaOne

/-- **`maxEigen`-fold over a sequence**: `iseqMaxEigen ds = max_{i < lh ds} maxEigen(znth ds i)`. -/
noncomputable def iseqMaxEigen (ds : V) : V := iseqMaxEigenAux ds (lh ds)

/-- **Table-fold = `maxEigen`-fold under dominance.** -/
lemma iseqMaxAux_maxEigenTable_eq {M ds : V} (hdom : ∀ i < lh ds, znth ds i ≤ M) :
    ∀ j ≤ lh ds, iseqMaxAux (maxEigenTable M) ds j = iseqMaxEigenAux ds j := by
  intro j
  induction j using ISigma1.sigma1_succ_induction
  · refine Definable.imp (by definability) ?_
    refine Definable.comp₂
      (DefinableFunction₃.comp (F := iseqMaxAux)
        (DefinableFunction₁.comp (F := maxEigenTable) (DefinableFunction.const M))
        (DefinableFunction.const ds) (DefinableFunction.var 0))
      (DefinableFunction₂.comp (F := iseqMaxEigenAux) (DefinableFunction.const ds)
        (DefinableFunction.var 0))
  case zero => intro _; simp
  case succ j ih =>
    intro hj
    rw [iseqMaxAux_succ, iseqMaxEigenAux_succ, ih (le_trans (by simp) hj),
      znth_maxEigenTable_eq_maxEigen M (znth ds j) (hdom j (lt_of_lt_of_le (by simp) hj))]

/-- **The variadic `K^r` eigenvariable equation**: a chain node has no eigenvariable of its own,
so `maxEigen (zK s r ds) = max_j maxEigen(dⱼ)`. -/
lemma maxEigen_zK (s r ds : V) (hds : Seq ds) :
    maxEigen (zK s r ds) = iseqMaxEigen ds := by
  have hdom : ∀ i < lh ds, znth ds i ≤ zK s r ds - 1 := fun i hi ↦
    le_pred_of_lt (lt_trans (lt_of_mem_rng (hds.znth hi)) (ds_lt_zK s r ds))
  rw [maxEigen_eq_maxEigenNext (by simp [zK]), maxEigenNext, if_neg (by simp), if_neg (by simp),
    if_neg (by simp), if_pos (zTag_zK s r ds), zKseq_zK, iseqMaxTab,
    iseqMaxAux_maxEigenTable_eq hdom (lh ds) (le_refl _), iseqMaxEigen]

/-- Every premise's `maxEigen` is dominated by the partial fold. -/
lemma le_iseqMaxEigenAux {ds : V} :
    ∀ j : V, ∀ i < j, maxEigen (znth ds i) ≤ iseqMaxEigenAux ds j := by
  intro j
  induction j using ISigma1.sigma1_succ_induction
  · refine Definable.ball_lt (by definability) ?_
    apply Definable.comp₂ <;> definability
  case zero => intro i hi; exact absurd hi (by simp)
  case succ j ih =>
    intro i hi
    rw [iseqMaxEigenAux_succ]
    rcases eq_or_lt_of_le (le_iff_lt_succ.mpr hi) with h | h
    · subst h; exact le_max_right _ _
    · exact le_trans (ih i h) (le_max_left _ _)

/-- The full fold dominates each premise's `maxEigen` (for `i < lh ds`). -/
lemma le_iseqMaxEigen {ds i : V} (hi : i < lh ds) :
    maxEigen (znth ds i) ≤ iseqMaxEigen ds := le_iseqMaxEigenAux _ i hi

/-- **Fold congruence**: equal lengths + entrywise-equal `maxEigen` ⟹ equal folds (the chain step of
`maxEigen_zsubst`). -/
lemma iseqMaxEigenAux_congr {A B : V}
    (hpt : ∀ i < lh A, maxEigen (znth A i) = maxEigen (znth B i)) :
    ∀ j ≤ lh A, iseqMaxEigenAux A j = iseqMaxEigenAux B j := by
  intro j
  induction j using ISigma1.sigma1_succ_induction
  · refine Definable.imp (by definability) ?_
    exact Definable.comp₂
      (DefinableFunction₂.comp (F := iseqMaxEigenAux) (DefinableFunction.const A)
        (DefinableFunction.var 0))
      (DefinableFunction₂.comp (F := iseqMaxEigenAux) (DefinableFunction.const B)
        (DefinableFunction.var 0))
  case zero => intro _; simp
  case succ j ih =>
    intro hj
    rw [iseqMaxEigenAux_succ, iseqMaxEigenAux_succ, ih (le_trans (by simp) hj),
      hpt j (lt_of_lt_of_le (by simp) hj)]

/-! ### `maxEigen_zsubst` — eigenvariable indices are stable under closed-term substitution (Path-X §2b)

The substitution crux of the DECISION: `zsubst d a t` rewrites every node's *data* (sequent / formula /
term) but leaves every `zIall`/`zInd` **eigenvariable index** untouched (cf. `zsubst_zIall` keeping `e`,
`zsubst_zInd` keeping `π₁ at'`). Hence `maxEigen` is invariant. Proved by `zDerivation_induction`, the
`maxEigen` recursion equations, and (chain case) the fold congruence above. This is what makes a
`maxEigen`-phrased freshness invariant maintainable through `red` — the code bound `d ≤ a` was not. -/
theorem maxEigen_zsubst (a t : V) :
    ∀ d, ZDerivation d → maxEigen (zsubst d a t) = maxEigen d := by
  apply zDerivation_induction (P := fun d => maxEigen (zsubst d a t) = maxEigen d)
  · definability
  · intro C hC d hphi
    rcases hphi with ⟨s, rfl, _⟩ | ⟨s, e, p, d0, rfl, hd0, _, _⟩ |
      ⟨s, p, d0, rfl, hd0, _, _⟩ | ⟨s, at', p, d0, d1, rfl, hd0, hd1, _⟩ |
      ⟨s, r, ds, rfl, hseq, hmem, _⟩ | ⟨s, p, k, rfl, _, _⟩ | ⟨s, p, rfl, _, _⟩ | ⟨s, C, rfl, _⟩
    -- atom
    · simp [zsubst_zAtom]
    -- zIall (eigenvariable `e` preserved)
    · rw [zsubst_zIall, maxEigen_zIall, maxEigen_zIall, (hC d0 hd0).2]
    -- zIneg
    · rw [zsubst_zIneg, maxEigen_zIneg, maxEigen_zIneg, (hC d0 hd0).2]
    -- zInd (eigenvariable `π₁ at'` preserved)
    · rw [show at' = ⟪π₁ at', π₂ at'⟫ from (pair_unpair at').symm, zsubst_zInd,
        maxEigen_zInd, maxEigen_zInd, (hC d0 hd0).2, (hC d1 hd1).2]
      simp only [pi₁_pair]
    -- zK (chain: no own eigenvariable; fold over substituted premises = fold over premises)
    · rw [zsubst_zK, maxEigen_zK _ _ _ (tblMapSeq_seq _ _), maxEigen_zK s r ds hseq]
      have hlh : lh (tblMapSeq (zsubstTable a t (zK s r ds - 1)) ds) = lh ds := tblMapSeq_lh _ _
      have hpt : ∀ i < lh (tblMapSeq (zsubstTable a t (zK s r ds - 1)) ds),
          maxEigen (znth (tblMapSeq (zsubstTable a t (zK s r ds - 1)) ds) i) = maxEigen (znth ds i) := by
        intro i hi
        rw [hlh] at hi
        rw [znth_tblMapSeq hi, znth_zsubstTable_eq_zsubst a t _ (znth ds i)
          (le_pred_of_lt (lt_of_le_of_lt (znth_le_self ds i) (ds_lt_zK s r ds)))]
        exact (hC _ (hmem i hi)).2
      simp only [iseqMaxEigen]
      rw [iseqMaxEigenAux_congr hpt _ (le_refl _), hlh]
    -- zAxAll / zAxNeg / zAx1
    · simp [zsubst_zAxAll]
    · simp [zsubst_zAxNeg]
    · simp [zsubst_zAx1]

/-! ### `iord_zsubst` — the eigensubst preserves the ordinal assignment (route-B I∀ bridge, lap 96)

The route-B faithful `red` must, on the I∀ rule, perform Buchholz's eigenvariable substitution
`red (zIall) = d0(a/n)` (currently `red (zIall) = d0`, conclusion untracked). For the ε₀-descent to
survive that rewire, the eigensubst must not change the ordinal: `iord (zsubst d a t) = iord d`. This
holds because `zsubst` rewrites node *data* (sequents/formulae/terms) but preserves every node's TAG and
RANK and maps premises recursively (`zsubst_zK` keeps `r`; `zsubst_zIall`/`_zInd` keep the eigenvariable),
and `iord = iotower (iotil d) (idg d)` reads only tags/ranks/premise-ordinals. Proved by the same
`zDerivation_induction` + fold-congruence template as `maxEigen_zsubst`. -/

/-- **idg-fold value-congruence**: entrywise-equal `idg` ⟹ equal partial folds (the chain step of
`idg_zsubst`; the existing `iseqMaxIdgAux_congr` requires `znth`-equality, too strong here since `zsubst`
changes the premises but preserves their `idg`). Mirror of `iseqMaxEigenAux_congr`. -/
lemma iseqMaxIdgAux_congr_val {A B : V}
    (hpt : ∀ i < lh A, idg (znth A i) = idg (znth B i)) :
    ∀ j ≤ lh A, iseqMaxIdgAux A j = iseqMaxIdgAux B j := by
  intro j
  induction j using ISigma1.sigma1_succ_induction
  · refine Definable.imp (by definability) ?_
    exact Definable.comp₂
      (DefinableFunction₂.comp (F := iseqMaxIdgAux) (DefinableFunction.const A)
        (DefinableFunction.var 0))
      (DefinableFunction₂.comp (F := iseqMaxIdgAux) (DefinableFunction.const B)
        (DefinableFunction.var 0))
  case zero => intro _; simp
  case succ j ih =>
    intro hj
    rw [iseqMaxIdgAux_succ, iseqMaxIdgAux_succ, ih (le_trans (by simp) hj),
      hpt j (lt_of_lt_of_le (by simp) hj)]

/-- **iõ-fold value-congruence**: entrywise-equal `iotil` ⟹ equal partial folds (the chain step of
`iotil_zsubst`). Mirror of `iseqMaxIdgAux_congr_val`. -/
lemma iseqNaddIdgAux_congr_val {A B : V}
    (hpt : ∀ i < lh A, iotil (znth A i) = iotil (znth B i)) :
    ∀ j ≤ lh A, iseqNaddIdgAux A j = iseqNaddIdgAux B j := by
  intro j
  induction j using ISigma1.sigma1_succ_induction
  · refine Definable.imp (by definability) ?_
    exact Definable.comp₂
      (DefinableFunction₂.comp (F := iseqNaddIdgAux) (DefinableFunction.const A)
        (DefinableFunction.var 0))
      (DefinableFunction₂.comp (F := iseqNaddIdgAux) (DefinableFunction.const B)
        (DefinableFunction.var 0))
  case zero => intro _; simp
  case succ j ih =>
    intro hj
    rw [iseqNaddIdgAux_succ, iseqNaddIdgAux_succ, ih (le_trans (by simp) hj),
      hpt j (lt_of_lt_of_le (by simp) hj)]

/-- **`idg` is invariant under the eigensubst.** `idg (zsubst d a t) = idg d` for `ZDerivation d`,
substituting a genuine closed term `t` (`IsUTerm`, needed only for the `zInd` rank `irk p` invariance
`irk_fvSubst`; on the headline path `t` is a numeral). -/
theorem idg_zsubst {t : V} (ht : IsUTerm ℒₒᵣ t) (a : V) :
    ∀ d, ZDerivation d → idg (zsubst d a t) = idg d := by
  apply zDerivation_induction (P := fun d => idg (zsubst d a t) = idg d)
  · definability
  · intro C hC d hphi
    rcases hphi with ⟨s, rfl, _⟩ | ⟨s, e, p, d0, rfl, hd0, _, _⟩ |
      ⟨s, p, d0, rfl, hd0, _, _⟩ | ⟨s, at', p, d0, d1, rfl, hd0, hd1, hwff⟩ |
      ⟨s, r, ds, rfl, hseq, hmem, _⟩ | ⟨s, p, k, rfl, _, _⟩ | ⟨s, p, rfl, _, _⟩ | ⟨s, C, rfl, _⟩
    · simp [zsubst_zAtom]
    · rw [zsubst_zIall, idg_zIall, idg_zIall, (hC d0 hd0).2]
    · rw [zsubst_zIneg, idg_zIneg, idg_zIneg, (hC d0 hd0).2]
    · have hp : IsSemiformula ℒₒᵣ 1 p := by
        have := hwff.2.2.2.1; rwa [zIndP_zInd] at this
      rw [show at' = ⟪π₁ at', π₂ at'⟫ from (pair_unpair at').symm, zsubst_zInd,
        idg_zInd, idg_zInd, (hC d0 hd0).2, (hC d1 hd1).2, irk_fvSubst ht hp.isUFormula]
    · rw [zsubst_zK, idg_zK _ _ _ (tblMapSeq_seq _ _), idg_zK s r ds hseq]
      have hlh : lh (tblMapSeq (zsubstTable a t (zK s r ds - 1)) ds) = lh ds := tblMapSeq_lh _ _
      have hpt : ∀ i < lh (tblMapSeq (zsubstTable a t (zK s r ds - 1)) ds),
          idg (znth (tblMapSeq (zsubstTable a t (zK s r ds - 1)) ds) i) = idg (znth ds i) := by
        intro i hi
        rw [hlh] at hi
        rw [znth_tblMapSeq hi, znth_zsubstTable_eq_zsubst a t _ (znth ds i)
          (le_pred_of_lt (lt_of_le_of_lt (znth_le_self ds i) (ds_lt_zK s r ds)))]
        exact (hC _ (hmem i hi)).2
      simp only [iseqMaxIdg]
      rw [iseqMaxIdgAux_congr_val hpt _ (le_refl _), hlh]
    · simp [zsubst_zAxAll]
    · simp [zsubst_zAxNeg]
    · simp [zsubst_zAx1]

/-- **`iotil` (pre-ordinal `õ`) is invariant under the eigensubst.** Needs `IsUTerm t` for the axiom
cases (`õ(Ax) = oAtomLk` reads the principal formula's `irk`, invariant under `fvSubst` of a real term). -/
theorem iotil_zsubst {t : V} (ht : IsUTerm ℒₒᵣ t) (a : V) :
    ∀ d, ZDerivation d → iotil (zsubst d a t) = iotil d := by
  apply zDerivation_induction (P := fun d => iotil (zsubst d a t) = iotil d)
  · definability
  · intro C hC d hphi
    rcases hphi with ⟨s, rfl, _⟩ | ⟨s, e, p, d0, rfl, hd0, _, _⟩ |
      ⟨s, p, d0, rfl, hd0, _, _⟩ | ⟨s, at', p, d0, d1, rfl, hd0, hd1, _⟩ |
      ⟨s, r, ds, rfl, hseq, hmem, _⟩ | ⟨s, p, k, rfl, hp, _⟩ | ⟨s, p, rfl, hp, _⟩ | ⟨s, C, rfl, _⟩
    · simp [zsubst_zAtom]
    · rw [zsubst_zIall, iotil_zIall, iotil_zIall, (hC d0 hd0).2]
    · rw [zsubst_zIneg, iotil_zIneg, iotil_zIneg, (hC d0 hd0).2]
    · rw [show at' = ⟪π₁ at', π₂ at'⟫ from (pair_unpair at').symm, zsubst_zInd,
        iotil_zInd, iotil_zInd, (hC d0 hd0).2, (hC d1 hd1).2]
    · rw [zsubst_zK, iotil_zK _ _ _ (tblMapSeq_seq _ _), iotil_zK s r ds hseq]
      have hlh : lh (tblMapSeq (zsubstTable a t (zK s r ds - 1)) ds) = lh ds := tblMapSeq_lh _ _
      have hpt : ∀ i < lh (tblMapSeq (zsubstTable a t (zK s r ds - 1)) ds),
          iotil (znth (tblMapSeq (zsubstTable a t (zK s r ds - 1)) ds) i) = iotil (znth ds i) := by
        intro i hi
        rw [hlh] at hi
        rw [znth_tblMapSeq hi, znth_zsubstTable_eq_zsubst a t _ (znth ds i)
          (le_pred_of_lt (lt_of_le_of_lt (znth_le_self ds i) (ds_lt_zK s r ds)))]
        exact (hC _ (hmem i hi)).2
      simp only [iseqNaddIdg]
      rw [iseqNaddIdgAux_congr_val hpt _ (le_refl _), hlh]
    · -- zAxAll: õ = oAtomLk(^∀ F), invariant since irk(^∀ (fvSubst F)) = irk(^∀ F)
      have hirk : irk (^∀ (fvSubst ℒₒᵣ a t p) : V) = irk (^∀ p : V) := by
        rw [irk_all (IsUFormula.fvSubst ht hp), irk_all hp, irk_fvSubst ht hp]
      rw [zsubst_zAxAll, iotil_zAxAll, iotil_zAxAll, oAtomLk, oAtomLk, hirk]
    · -- zAxNeg: õ = oAtomLk(¬F), invariant since irk(¬ (fvSubst F)) = irk(¬ F)
      have hirk : irk (inegF (fvSubst ℒₒᵣ a t p) : V) = irk (inegF p : V) := by
        rw [irk_inegF (IsUFormula.fvSubst ht hp), irk_inegF hp, irk_fvSubst ht hp]
      rw [zsubst_zAxNeg, iotil_zAxNeg, iotil_zAxNeg, oAtomLk, oAtomLk, hirk]
    · -- zAx1: õ = oAtom1 C reads only the unsubstituted ordinal-payload C, so it is invariant
      simp [zsubst_zAx1]

/-- **The eigensubst preserves the ordinal `iord`** (route-B I∀ bridge). With this, rewiring
`red (zIall) = d0(a/n)` keeps the ε₀-descent (`iord (zsubst d0 e n) = iord d0`, so the banked
`iord_descent_zIall` transfers). -/
theorem iord_zsubst {d t : V} (ht : IsUTerm ℒₒᵣ t) (hZ : ZDerivation d) (a : V) :
    iord (zsubst d a t) = iord d := by
  rw [iord, iord, idg_zsubst ht a d hZ, iotil_zsubst ht a d hZ]

/-! ## `zReg` — hereditary eigenvariable freshness (Path-X O1 foundation)

`zReg d` = **violation count**: `0` iff `d` is *regular*, i.e. every `zIall`/`zInd` node `n` in `d` has
`maxEigen(premise n) < eigenvar(n)` (the eigenvariable strictly exceeds every eigenvariable index used in
its premise — Buchholz's freshness side-condition). Built by the exact `maxEigen`/`idg` table template,
folding the **max** of a per-node freshness flag (`ltFlag`) and the premise violations.

This is the *additive* O1 architecture (lap 93): rather than baking freshness into `zIallWff` (which would
shrink the `ZDerivation` fixpoint and force the embedding to re-prove it), `zReg` is a standalone `𝚺₁`
function threaded *alongside* `ZDerivation`. The two facts O1 needs — the route-B bound
`maxEigen d0 < a` (from `ZRegular (zIall …)`) and stability under `red` — both follow from `zReg`'s
recursion equations and `zReg_zsubst` (regularity is preserved by closed-term substitution, since both
`maxEigen` and the eigenvariables are). -/

/-- `ltFlag x y = 0` iff `x < y`, else `1` — the per-node freshness violation indicator. -/
noncomputable def ltFlag (x y : V) : V := if x < y then 0 else 1

def _root_.LO.FirstOrder.Arithmetic.ltFlagDef : 𝚺₀.Semisentence 3 := .mkSigma
  “z x y. (x < y ∧ z = 0) ∨ (y ≤ x ∧ z = 1)”

instance ltFlag_defined : 𝚺₀-Function₂ (ltFlag : V → V → V) via ltFlagDef := .mk fun v ↦ by
  by_cases h : v 1 < v 2 <;> simp [ltFlagDef, ltFlag, h, not_lt.mp, le_of_lt, not_le.mpr] <;>
    simp [not_lt] at h ⊢ <;> omega
instance ltFlag_definable : 𝚺₀-Function₂ (ltFlag : V → V → V) := ltFlag_defined.to_definable

@[simp] lemma ltFlag_eq_zero_iff {x y : V} : ltFlag x y = 0 ↔ x < y := by
  unfold ltFlag; by_cases h : x < y <;> simp [h]

noncomputable def zRegNext (d s : V) : V :=
  if zTag d = 1 then max (ltFlag (maxEigen (zIallPrem d)) (zIallEig d)) (znth s (zIallPrem d))
  else if zTag d = 2 then znth s (zInegPrem d)
  else if zTag d = 3 then
    max (ltFlag (maxEigen (zIndPrem1 d)) (zIndEig d))
      (max (znth s (zIndPrem0 d)) (znth s (zIndPrem1 d)))
  else if zTag d = 4 then iseqMaxTab s (zKseq d)
  else 0

noncomputable def _root_.LO.FirstOrder.Arithmetic.zRegNextDef : 𝚺₁.Semisentence 3 := .mkSigma
  “y d s. ∃ t, !zTagDef t d ∧
    ( (t = 1 ∧ ∃ p, !zIallPremDef p d ∧ ∃ m, !maxEigenDef m p ∧ ∃ ea, !zIallEigDef ea d ∧
         ∃ fl, !ltFlagDef fl m ea ∧ ∃ v, !znthDef v s p ∧ !max.dfn y fl v)
    ∨ (t = 2 ∧ ∃ p, !zInegPremDef p d ∧ !znthDef y s p)
    ∨ (t = 3 ∧ ∃ p1, !zIndPrem1Def p1 d ∧ ∃ m, !maxEigenDef m p1 ∧ ∃ ie, !zIndEigDef ie d ∧
         ∃ fl, !ltFlagDef fl m ie ∧ ∃ p0, !zIndPrem0Def p0 d ∧ ∃ v0, !znthDef v0 s p0 ∧
         ∃ v1, !znthDef v1 s p1 ∧ ∃ mm, !max.dfn mm v0 v1 ∧ !max.dfn y fl mm)
    ∨ (t = 4 ∧ ∃ ds, !zKseqDef ds d ∧ !iseqMaxTabDef y s ds)
    ∨ (t ≠ 1 ∧ t ≠ 2 ∧ t ≠ 3 ∧ t ≠ 4 ∧ y = 0) )”

set_option maxHeartbeats 1000000 in
instance zRegNext_defined : 𝚺₁-Function₂ (zRegNext : V → V → V) via zRegNextDef :=
  .mk fun v ↦ by
    simp [zRegNextDef, zRegNext, zTag_defined.iff, zIallPrem_defined.iff, maxEigen_defined.iff,
      zIallEig_defined.iff, ltFlag_defined.iff, zInegPrem_defined.iff, zIndPrem0_defined.iff,
      zIndPrem1_defined.iff, zIndEig_defined.iff, zKseq_defined.iff, iseqMaxTab_defined.iff,
      znth_defined.iff, max_defined.iff]
    by_cases h1 : zTag (v 1) = 1
    · simp [h1]
    · by_cases h2 : zTag (v 1) = 2
      · simp [h1, h2]
      · by_cases h3 : zTag (v 1) = 3
        · simp [h1, h2, h3]
        · by_cases h4 : zTag (v 1) = 4
          · simp [h1, h2, h3, h4]
          · simp [h1, h2, h3, h4]

instance zRegNext_definable : 𝚺₁-Function₂ (zRegNext : V → V → V) := zRegNext_defined.to_definable

noncomputable def zRegTable.blueprint : PR.Blueprint 0 where
  zero := .mkSigma “y. !mkSeq₁Def y 0”
  succ := .mkSigma “y ih n. ∃ v, !zRegNextDef v (n + 1) ih ∧ !seqConsDef y ih v”

noncomputable def zRegTable.construction : PR.Construction V zRegTable.blueprint where
  zero := fun _ ↦ !⟦0⟧
  succ := fun _ n ih ↦ seqCons ih (zRegNext (n + 1) ih)
  zero_defined := .mk fun v ↦ by
    simp [zRegTable.blueprint, mkSeq₁Def, seqCons_defined.iff, emptyset_def]
  succ_defined := .mk fun v ↦ by
    simp [zRegTable.blueprint, zRegNext_defined.iff, seqCons_defined.iff]

noncomputable def zRegTable (n : V) : V := zRegTable.construction.result ![] n

@[simp] lemma zRegTable_zero : zRegTable (0 : V) = !⟦0⟧ := by simp [zRegTable, zRegTable.construction]

@[simp] lemma zRegTable_succ (n : V) :
    zRegTable (n + 1) = seqCons (zRegTable n) (zRegNext (n + 1) (zRegTable n)) := by
  simp [zRegTable, zRegTable.construction]

/-- **Violation count** `zReg d`: `0` iff `d` is hereditarily eigenvariable-fresh. -/
noncomputable def zReg (d : V) : V := znth (zRegTable d) d

noncomputable def _root_.LO.FirstOrder.Arithmetic.zRegTableDef : 𝚺₁.Semisentence 2 :=
  zRegTable.blueprint.resultDef.rew (Rew.subst ![#0, #1])

instance zRegTable_defined : 𝚺₁-Function₁ (zRegTable : V → V) via zRegTableDef := .mk
  fun v ↦ by simp [zRegTable.construction.result_defined_iff, zRegTableDef]; rfl
instance zRegTable_definable : 𝚺₁-Function₁ (zRegTable : V → V) := zRegTable_defined.to_definable
instance zRegTable_definable' (Γ) : Γ-[m + 1]-Function₁ (zRegTable : V → V) :=
  zRegTable_definable.of_sigmaOne

noncomputable def _root_.LO.FirstOrder.Arithmetic.zRegDef : 𝚺₁.Semisentence 2 := .mkSigma
  “y d. ∃ t, !zRegTableDef t d ∧ !znthDef y t d”

instance zReg_defined : 𝚺₁-Function₁ (zReg : V → V) via zRegDef := .mk fun v ↦ by
  simp [zRegDef, zReg, zRegTable_defined.iff, znth_defined.iff]
instance zReg_definable : 𝚺₁-Function₁ (zReg : V → V) := zReg_defined.to_definable
instance zReg_definable' (Γ) : Γ-[m + 1]-Function₁ (zReg : V → V) := zReg_definable.of_sigmaOne

/-! ### Structural correctness of the `zReg` table (mirror `maxEigen`) -/

private lemma def_zRegTable {k} (i : Fin k) :
    𝚺-[1].DefinableFunction (fun v : Fin k → V ↦ zRegTable (v i)) :=
  DefinableFunction₁.comp (F := zRegTable) (DefinableFunction.var i)

private lemma def_zReg {k} (i : Fin k) :
    𝚺-[1].DefinableFunction (fun v : Fin k → V ↦ zReg (v i)) :=
  DefinableFunction₁.comp (F := zReg) (DefinableFunction.var i)

@[simp] lemma zRegTable_seq (n : V) : Seq (zRegTable n) := by
  induction n using ISigma1.sigma1_succ_induction
  · exact Definable.comp₁ (def_zRegTable 0)
  case zero => simp
  case succ n ih => rw [zRegTable_succ]; exact ih.seqCons _

@[simp] lemma zRegTable_lh (n : V) : lh (zRegTable n) = n + 1 := by
  induction n using ISigma1.sigma1_succ_induction
  · exact Definable.comp₂ (DefinableFunction₁.comp (F := lh) (def_zRegTable 0)) (by definability)
  case zero => simp
  case succ n ih => rw [zRegTable_succ, Seq.lh_seqCons _ (zRegTable_seq n), ih]

lemma znth_zRegTable_succ {n k : V} (hk : k < n + 1) :
    znth (zRegTable (n + 1)) k = znth (zRegTable n) k := by
  rw [zRegTable_succ]
  exact znth_seqCons_of_lt (zRegTable_seq n) _ (by rw [zRegTable_lh]; exact hk)

lemma znth_zRegTable_eq_zReg : ∀ N : V, ∀ k ≤ N, znth (zRegTable N) k = zReg k := by
  intro N
  induction N using ISigma1.sigma1_succ_induction
  · refine Definable.ball_le (by definability) ?_
    exact Definable.comp₂
      (DefinableFunction₂.comp (F := znth) (def_zRegTable 1) (DefinableFunction.var 0))
      (def_zReg 0)
  case zero => intro k hk; rcases (nonpos_iff_eq_zero.mp hk) with rfl; rfl
  case succ N ih =>
    intro k hk
    rcases eq_or_lt_of_le hk with rfl | hlt
    · rfl
    · rw [znth_zRegTable_succ hlt]; exact ih k (le_iff_lt_succ.mpr hlt)

lemma zReg_eq_zRegNext {c : V} (hpos : 0 < c) : zReg c = zRegNext c (zRegTable (c - 1)) := by
  obtain ⟨M, rfl⟩ : ∃ M, c = M + 1 := ⟨c - 1, (sub_add_self_of_le (pos_iff_one_le.mp hpos)).symm⟩
  have key : znth (zRegTable (M + 1)) (M + 1) = zRegNext (M + 1) (zRegTable M) := by
    rw [zRegTable_succ]
    have h := znth_seqCons_self (zRegTable_seq M) (zRegNext (M + 1) (zRegTable M))
    rwa [zRegTable_lh] at h
  simp only [zReg, add_tsub_cancel_right, key]

/-! ### `zReg` recursion equations -/

@[simp] lemma zReg_zAtom (s : V) : zReg (zAtom s) = 0 := by
  rw [zReg_eq_zRegNext (by simp [zAtom]), zRegNext]; simp [zTag_zAtom]

@[simp] lemma zReg_zIall (s a p d0 : V) :
    zReg (zIall s a p d0) = max (ltFlag (maxEigen d0) a) (zReg d0) := by
  rw [zReg_eq_zRegNext (by simp [zIall]), zRegNext, if_pos (zTag_zIall s a p d0),
    zIallPrem_zIall, zIallEig_zIall,
    znth_zRegTable_eq_zReg _ d0 (le_pred_of_lt (d0_lt_zIall s a p d0))]

@[simp] lemma zReg_zIneg (s p d0 : V) : zReg (zIneg s p d0) = zReg d0 := by
  rw [zReg_eq_zRegNext (by simp [zIneg]), zRegNext, if_neg (by simp), if_pos (zTag_zIneg s p d0),
    zInegPrem_zIneg, znth_zRegTable_eq_zReg _ d0 (le_pred_of_lt (d0_lt_zIneg s p d0))]

@[simp] lemma zReg_zInd (s at' p d0 d1 : V) :
    zReg (zInd s at' p d0 d1) = max (ltFlag (maxEigen d1) (π₁ at')) (max (zReg d0) (zReg d1)) := by
  rw [zReg_eq_zRegNext (by simp [zInd]), zRegNext, if_neg (by simp), if_neg (by simp),
    if_pos (zTag_zInd s at' p d0 d1), zIndPrem1_zInd, zIndEig_zInd, zIndPrem0_zInd,
    znth_zRegTable_eq_zReg _ d0 (le_pred_of_lt (d0_lt_zInd s at' p d0 d1)),
    znth_zRegTable_eq_zReg _ d1 (le_pred_of_lt (d1_lt_zInd s at' p d0 d1))]

@[simp] lemma zReg_zAxAll (s p k : V) : zReg (zAxAll s p k) = 0 := by
  rw [zReg_eq_zRegNext (by simp [zAxAll]), zRegNext]; simp [zTag_zAxAll]

@[simp] lemma zReg_zAxNeg (s p : V) : zReg (zAxNeg s p) = 0 := by
  rw [zReg_eq_zRegNext (by simp [zAxNeg]), zRegNext]; simp [zTag_zAxNeg]

@[simp] lemma zReg_zAx1 (s C : V) : zReg (zAx1 s C) = 0 := by
  rw [zReg_eq_zRegNext (by simp [zAx1]), zRegNext]; simp [zTag_zAx1]

/-! ### `zReg`-fold over a premise sequence (for the `K^r` equation) -/

noncomputable def iseqRegAux.blueprint : PR.Blueprint 1 where
  zero := .mkSigma “y ds. y = 0”
  succ := .mkSigma “y ih n ds. ∃ di, !znthDef di ds n ∧ ∃ v, !zRegDef v di ∧ !max.dfn y ih v”

noncomputable def iseqRegAux.construction : PR.Construction V iseqRegAux.blueprint where
  zero := fun _ ↦ 0
  succ := fun x n ih ↦ max ih (zReg (znth (x 0) n))
  zero_defined := .mk fun v ↦ by simp [iseqRegAux.blueprint]
  succ_defined := .mk fun v ↦ by
    simp [iseqRegAux.blueprint, znth_defined.iff, zReg_defined.iff, max_defined.iff]

noncomputable def iseqRegAux (ds j : V) : V := iseqRegAux.construction.result ![ds] j

@[simp] lemma iseqRegAux_zero (ds : V) : iseqRegAux ds 0 = 0 := by
  simp [iseqRegAux, iseqRegAux.construction]

@[simp] lemma iseqRegAux_succ (ds j : V) :
    iseqRegAux ds (j + 1) = max (iseqRegAux ds j) (zReg (znth ds j)) := by
  simp [iseqRegAux, iseqRegAux.construction]

noncomputable def _root_.LO.FirstOrder.Arithmetic.iseqRegAuxDef : 𝚺₁.Semisentence 3 :=
  iseqRegAux.blueprint.resultDef.rew (Rew.subst ![#0, #2, #1])

instance iseqRegAux_defined : 𝚺₁-Function₂ (iseqRegAux : V → V → V) via iseqRegAuxDef :=
  .mk fun v ↦ by simp [iseqRegAux.construction.result_defined_iff, iseqRegAuxDef]; rfl
instance iseqRegAux_definable : 𝚺₁-Function₂ (iseqRegAux : V → V → V) := iseqRegAux_defined.to_definable
instance iseqRegAux_definable' (Γ) : Γ-[m + 1]-Function₂ (iseqRegAux : V → V → V) :=
  iseqRegAux_definable.of_sigmaOne

/-- **`zReg`-fold over a sequence**: `iseqReg ds = max_{i < lh ds} zReg(znth ds i)`. -/
noncomputable def iseqReg (ds : V) : V := iseqRegAux ds (lh ds)

lemma iseqMaxAux_zRegTable_eq {M ds : V} (hdom : ∀ i < lh ds, znth ds i ≤ M) :
    ∀ j ≤ lh ds, iseqMaxAux (zRegTable M) ds j = iseqRegAux ds j := by
  intro j
  induction j using ISigma1.sigma1_succ_induction
  · refine Definable.imp (by definability) ?_
    refine Definable.comp₂
      (DefinableFunction₃.comp (F := iseqMaxAux)
        (DefinableFunction₁.comp (F := zRegTable) (DefinableFunction.const M))
        (DefinableFunction.const ds) (DefinableFunction.var 0))
      (DefinableFunction₂.comp (F := iseqRegAux) (DefinableFunction.const ds)
        (DefinableFunction.var 0))
  case zero => intro _; simp
  case succ j ih =>
    intro hj
    rw [iseqMaxAux_succ, iseqRegAux_succ, ih (le_trans (by simp) hj),
      znth_zRegTable_eq_zReg M (znth ds j) (hdom j (lt_of_lt_of_le (by simp) hj))]

lemma zReg_zK (s r ds : V) (hds : Seq ds) : zReg (zK s r ds) = iseqReg ds := by
  have hdom : ∀ i < lh ds, znth ds i ≤ zK s r ds - 1 := fun i hi ↦
    le_pred_of_lt (lt_trans (lt_of_mem_rng (hds.znth hi)) (ds_lt_zK s r ds))
  rw [zReg_eq_zRegNext (by simp [zK]), zRegNext, if_neg (by simp), if_neg (by simp),
    if_neg (by simp), if_pos (zTag_zK s r ds), zKseq_zK, iseqMaxTab,
    iseqMaxAux_zRegTable_eq hdom (lh ds) (le_refl _), iseqReg]

lemma iseqRegAux_congr {A B : V} (hpt : ∀ i < lh A, zReg (znth A i) = zReg (znth B i)) :
    ∀ j ≤ lh A, iseqRegAux A j = iseqRegAux B j := by
  intro j
  induction j using ISigma1.sigma1_succ_induction
  · refine Definable.imp (by definability) ?_
    exact Definable.comp₂
      (DefinableFunction₂.comp (F := iseqRegAux) (DefinableFunction.const A) (DefinableFunction.var 0))
      (DefinableFunction₂.comp (F := iseqRegAux) (DefinableFunction.const B) (DefinableFunction.var 0))
  case zero => intro _; simp
  case succ j ih =>
    intro hj
    rw [iseqRegAux_succ, iseqRegAux_succ, ih (le_trans (by simp) hj),
      hpt j (lt_of_lt_of_le (by simp) hj)]

/-! ### `ZRegular` and the route-B freshness bridge -/

/-- **Regularity**: `d` is hereditarily eigenvariable-fresh (`zReg d = 0`). -/
def ZRegular (d : V) : Prop := zReg d = 0

/-- **Route-B bridge (I∀)**: a regular `zIall` node has the freshness bound `maxEigen d0 < a` that the
reformulated `ZDerivation_zsubst` consumes. -/
lemma maxEigen_lt_of_regular_zIall {s a p d0 : V} (h : ZRegular (zIall s a p d0)) :
    maxEigen d0 < a := by
  unfold ZRegular at h
  rw [zReg_zIall] at h
  exact ltFlag_eq_zero_iff.mp (nonpos_iff_eq_zero.mp (h ▸ le_max_left _ _))

/-- **Route-B bridge (Ind step premise)**: a regular `zInd` node has `maxEigen d1 < π₁ at'`. -/
lemma maxEigen_lt_of_regular_zInd {s at' p d0 d1 : V} (h : ZRegular (zInd s at' p d0 d1)) :
    maxEigen d1 < π₁ at' := by
  unfold ZRegular at h
  rw [zReg_zInd] at h
  exact ltFlag_eq_zero_iff.mp (nonpos_iff_eq_zero.mp (h ▸ le_max_left _ _))

/-! ### `zReg_zsubst` — regularity is preserved by closed-term substitution

Since `zsubst` preserves both `maxEigen` (`maxEigen_zsubst`) and the eigenvariables themselves
(`zsubst_zIall`/`zInd` keep the binder), every per-node freshness flag is unchanged, so `zReg` is
invariant. This is the substitution step of "red preserves regularity" (O1). -/
theorem zReg_zsubst (a t : V) : ∀ d, ZDerivation d → zReg (zsubst d a t) = zReg d := by
  apply zDerivation_induction (P := fun d => zReg (zsubst d a t) = zReg d)
  · definability
  · intro C hC d hphi
    rcases hphi with ⟨s, rfl, _⟩ | ⟨s, e, p, d0, rfl, hd0, _, _⟩ |
      ⟨s, p, d0, rfl, hd0, _, _⟩ | ⟨s, at', p, d0, d1, rfl, hd0, hd1, _⟩ |
      ⟨s, r, ds, rfl, hseq, hmem, _⟩ | ⟨s, p, k, rfl, _, _⟩ | ⟨s, p, rfl, _, _⟩ | ⟨s, C, rfl, _⟩
    · simp [zsubst_zAtom]
    · rw [zsubst_zIall, zReg_zIall, zReg_zIall, (hC d0 hd0).2,
        maxEigen_zsubst a t d0 (hC d0 hd0).1]
    · rw [zsubst_zIneg, zReg_zIneg, zReg_zIneg, (hC d0 hd0).2]
    · rw [show at' = ⟪π₁ at', π₂ at'⟫ from (pair_unpair at').symm, zsubst_zInd,
        zReg_zInd, zReg_zInd, (hC d0 hd0).2, (hC d1 hd1).2,
        maxEigen_zsubst a t d1 (hC d1 hd1).1]
      simp only [pi₁_pair]
    · rw [zsubst_zK, zReg_zK _ _ _ (tblMapSeq_seq _ _), zReg_zK s r ds hseq]
      have hlh : lh (tblMapSeq (zsubstTable a t (zK s r ds - 1)) ds) = lh ds := tblMapSeq_lh _ _
      have hpt : ∀ i < lh (tblMapSeq (zsubstTable a t (zK s r ds - 1)) ds),
          zReg (znth (tblMapSeq (zsubstTable a t (zK s r ds - 1)) ds) i) = zReg (znth ds i) := by
        intro i hi
        rw [hlh] at hi
        rw [znth_tblMapSeq hi, znth_zsubstTable_eq_zsubst a t _ (znth ds i)
          (le_pred_of_lt (lt_of_le_of_lt (znth_le_self ds i) (ds_lt_zK s r ds)))]
        exact (hC _ (hmem i hi)).2
      simp only [iseqReg]
      rw [iseqRegAux_congr hpt _ (le_refl _), hlh]
    · simp [zsubst_zAxAll]
    · simp [zsubst_zAxNeg]
    · simp [zsubst_zAx1]

/-! ### Regularity of the corrected-reduct premises (engine re-key prerequisite, lap 119)

The re-keyed tag-4 critical reduct `iRKcCrit` (`InternalZ`) replaces each redex premise by its genuine
§3.2-case-5.1 reduct: the I∀ R-redex by `zsubst (zIallPrem dᵢ) (zIallEig dᵢ) (numeral k)` (re-principalized
child), the I¬ R-redex by `zInegPrem dᵢ` (the I¬ child), and the L-redex axioms by `zAx1` nodes. For the
`ZRegular_red` (O1) front of the engine swap, these new premises must be shown regular. The `zAx1` slots are
free (`zReg_zAx1 = 0`); the two below are the genuine facts. -/

/-- **The ∀ R-redex's corrected-reduct premise is regular.** The §3.2-case-5.1 reduct re-principalizes the
I∀ child `d0` at a closed numeral; `zReg_zsubst` (closed-term substitution preserves regularity) plus the
I∀ node's own regularity (`zReg d0 = 0`) gives that the substituted premise is regular. -/
lemma ZRegular_zsubst_zIallPrem {e k : V} (he : ZDerivation e) (hreg : ZRegular e) (htag : zTag e = 1) :
    ZRegular (zsubst (zIallPrem e) (zIallEig e) (Bootstrapping.Arithmetic.numeral k)) := by
  rcases zDerivation_iff.mp he with ⟨s, rfl, _⟩ | ⟨s, a, p, d0, rfl, hd0, _, _⟩ |
    ⟨s, p, d0, rfl, _, _, _⟩ | ⟨s, at', p, d0, d1, rfl, _, _, _⟩ |
    ⟨s, r, ds, rfl, _, _, _⟩ | ⟨s, p, kk, rfl, _, _⟩ | ⟨s, p, rfl, _, _⟩ | ⟨s, C, rfl, _⟩
  · simp at htag
  · rw [zIallPrem_zIall, zIallEig_zIall]
    unfold ZRegular
    rw [zReg_zsubst a (Bootstrapping.Arithmetic.numeral k) d0 hd0]
    unfold ZRegular at hreg; rw [zReg_zIall] at hreg
    exact nonpos_iff_eq_zero.mp (hreg ▸ le_max_right _ _)
  · simp at htag
  · simp at htag
  · simp at htag
  · simp at htag
  · simp at htag
  · simp at htag

/-- **The ¬ R-redex's corrected-reduct premise is regular.** The §3.2-case-5.1 ¬-reduct is the I¬ child
`d0 = zInegPrem e`; regularity is hereditary (`zReg_zIneg : zReg (zIneg ..) = zReg d0`). -/
lemma ZRegular_zInegPrem {e : V} (he : ZDerivation e) (hreg : ZRegular e) (htag : zTag e = 2) :
    ZRegular (zInegPrem e) := by
  rcases zDerivation_iff.mp he with ⟨s, rfl, _⟩ | ⟨s, a, p, d0, rfl, _, _, _⟩ |
    ⟨s, p, d0, rfl, hd0, _, _⟩ | ⟨s, at', p, d0, d1, rfl, _, _, _⟩ |
    ⟨s, r, ds, rfl, _, _, _⟩ | ⟨s, p, kk, rfl, _, _⟩ | ⟨s, p, rfl, _, _⟩ | ⟨s, C, rfl, _⟩
  · simp at htag
  · simp at htag
  · rw [zInegPrem_zIneg]
    unfold ZRegular at hreg ⊢
    rwa [zReg_zIneg] at hreg
  · simp at htag
  · simp at htag
  · simp at htag
  · simp at htag
  · simp at htag

/-! ## `red` preserves `ZRegular` — the structural and Ind cases (Path-X O1, lap 93)

`red` is the genuine one-step reduction. For regularity preservation `ZRegular d → ZRegular (red d)`:
the structural rules strip to a premise (`red_zIall = d0`, `red_zIneg = d0`) or are the identity
(atoms/axioms), so regularity is immediate; the `Ind` reduct `iRInd = zK s (irk p) (iIndReductSeq d0 d1 1)`
is a chain over the *literal* premises `⟨d1, d0⟩` (no substitution at this level), so its `zReg` is
`max (zReg d1) (zReg d0)`. The remaining case is the chain dispatch `red (zK …) = iRK …` (5.1/5.2.1/5.2.2),
the genuinely hard step (it threads `zReg_zsubst` through the critical reduct's splice/replace). -/

/-- `zReg`-fold congruence on agreeing entries (znth form, mirror `iseqMaxIdgAux_congr`). -/
lemma iseqRegAux_znth_congr {ds ds' : V} :
    ∀ j, (∀ i < j, znth ds i = znth ds' i) → iseqRegAux ds j = iseqRegAux ds' j := by
  intro j
  induction j using ISigma1.sigma1_succ_induction
  · refine Definable.imp (Definable.ball_lt (by definability) (by definability)) ?_
    refine Definable.comp₂
      (DefinableFunction₂.comp (F := iseqRegAux) (DefinableFunction.const ds) (DefinableFunction.var 0))
      (DefinableFunction₂.comp (F := iseqRegAux) (DefinableFunction.const ds') (DefinableFunction.var 0))
  case zero => intro _; rw [iseqRegAux_zero, iseqRegAux_zero]
  case succ j ih =>
    intro h
    rw [iseqRegAux_succ, iseqRegAux_succ, ih (fun i hi => h i (lt_trans hi (by simp))), h j (by simp)]

/-- `zReg`-fold over a `seqCons`: `iseqReg (seqCons ds v) = max (iseqReg ds) (zReg v)`. -/
lemma iseqReg_seqCons {ds v : V} (hds : Seq ds) :
    iseqReg (seqCons ds v) = max (iseqReg ds) (zReg v) := by
  rw [iseqReg, iseqReg, Seq.lh_seqCons v hds, iseqRegAux_succ,
    iseqRegAux_znth_congr (lh ds) (fun i hi => (znth_seqCons_of_lt hds v hi).symm),
    znth_seqCons_self hds v]

/-- `zReg`-fold over a constant block: if every entry's `zReg` is `c`, the fold is `c` (for `0<j`). -/
lemma iseqRegAux_const {ds c : V} (hconst : ∀ i < lh ds, zReg (znth ds i) = c) :
    ∀ j, 0 < j → j ≤ lh ds → iseqRegAux ds j = c := by
  intro j
  induction j using ISigma1.sigma1_succ_induction
  · refine Definable.imp (by definability) (Definable.imp (by definability) ?_)
    exact Definable.comp₂
      (DefinableFunction₂.comp (F := iseqRegAux) (DefinableFunction.const ds) (DefinableFunction.var 0))
      (by definability)
  case zero => intro h; exact absurd h (by simp)
  case succ j ih =>
    intro _ hj
    rw [iseqRegAux_succ, hconst j (lt_of_lt_of_le (by simp) hj)]
    rcases eq_or_ne j 0 with rfl | hj0
    · rw [iseqRegAux_zero]; simp
    · rw [ih (pos_iff_ne_zero.mpr hj0) (le_trans (by simp) hj), max_self]

/-- `zReg`-fold of a constant block `iRepeatSeq v k`: `= zReg v` (for `0<k`). -/
lemma iseqReg_iRepeatSeq {v k : V} (hk : 0 < k) : iseqReg (iRepeatSeq v k) = zReg v := by
  have hconst : ∀ i < lh (iRepeatSeq v k), zReg (znth (iRepeatSeq v k) i) = zReg v :=
    fun i hi => by rw [znth_iRepeatSeq i (by rwa [iRepeatSeq_lh] at hi)]
  rw [iseqReg, iseqRegAux_const hconst (lh (iRepeatSeq v k)) (by rw [iRepeatSeq_lh]; exact hk) le_rfl]

/-- `zReg`-fold of the Ind reduct sequence: `max (zReg d1) (zReg d0)` (for `0<k`). -/
lemma iseqReg_iIndReductSeq {d0 d1 k : V} (hk : 0 < k) :
    iseqReg (iIndReductSeq d0 d1 k) = max (zReg d1) (zReg d0) := by
  rw [iIndReductSeq, iseqReg_seqCons (iRepeatSeq_seq d1 k), iseqReg_iRepeatSeq hk]

/-- **`red` preserves `ZRegular` (structural + Ind cases).** Stated per the `ZDerivation` constructor;
the chain (`zK`) case is the remaining frontier (the `iRK` dispatch). -/
lemma ZRegular_red_of_not_zK {d : V} (hZ : ZDerivation d) (hreg : ZRegular d)
    (hnK : zTag d ≠ 4) : ZRegular (red d) := by
  unfold ZRegular at hreg ⊢
  rcases zDerivation_iff.mp hZ with ⟨s, rfl, _⟩ | ⟨s, a, p, d0, rfl, hd0, _⟩ | ⟨s, p, d0, rfl, _, _⟩ |
    ⟨s, at', p, d0, d1, rfl, _, _⟩ | ⟨s, r, ds, rfl, _, _, _⟩ |
    ⟨s, p, k, rfl, _, _⟩ | ⟨s, p, rfl, _, _⟩ | ⟨s, C, rfl, _⟩
  · rw [red_zAtom]; simpa using hreg
  · rw [red_zIall, zReg_zsubst _ _ _ hd0]; rw [zReg_zIall] at hreg
    exact nonpos_iff_eq_zero.mp (hreg ▸ le_max_right _ _)
  · rw [red_zIneg]; rwa [zReg_zIneg] at hreg
  · -- Ind: reduct is the chain ⟨d1, d0⟩, regular since both premises are
    rw [red_zInd, iRInd_zInd, zReg_zK _ _ _ (iIndReductSeq_seq d0 d1 1), iseqReg_iIndReductSeq one_pos]
    rw [zReg_zInd] at hreg
    have h0 : zReg d0 = 0 := nonpos_iff_eq_zero.mp (hreg ▸ le_trans (le_max_left _ _) (le_max_right _ _))
    have h1 : zReg d1 = 0 := nonpos_iff_eq_zero.mp (hreg ▸ le_trans (le_max_right _ _) (le_max_right _ _))
    rw [h0, h1]; simp
  · exact absurd (zTag_zK s r ds) hnK
  · rw [red_zAxAll]; simpa using hreg
  · rw [red_zAxNeg]; simpa using hreg
  · rw [red_zAx1]; simpa using hreg

/-! ### Reusable building blocks for the `zK` chain case (5.1/5.2.1/5.2.2)

All three `iRK` branches produce a chain whose premises are regular reducts. These are the shared
lemmas: a chain with all-regular premises is regular (`ZRegular_zK_of_premises`), and the per-premise
atomic reduct `zAxReduct` preserves regularity. The remaining `zK` work is to show each branch's premise
sequence (`seqUpdate`/`iCritReductSeq`/splice) has all-regular entries — then these close it. -/

/-- A chain `iseqReg`-fold vanishes when every premise is regular. -/
lemma iseqReg_eq_zero_of {ds : V} (h : ∀ i < lh ds, zReg (znth ds i) = 0) : iseqReg ds = 0 := by
  unfold iseqReg
  rcases eq_or_ne (lh ds) 0 with h0 | h0
  · rw [h0]; simp
  · exact iseqRegAux_const h (lh ds) (pos_iff_ne_zero.mpr h0) le_rfl

/-- **A `K`-chain all of whose premises are regular is regular.** The shared closing lemma for the three
`iRK` branches (each reduct is a chain over regular premises). -/
lemma ZRegular_zK_of_premises {s r ds : V} (hds : Seq ds)
    (h : ∀ i < lh ds, ZRegular (znth ds i)) : ZRegular (zK s r ds) := by
  unfold ZRegular
  rw [zReg_zK s r ds hds]
  exact iseqReg_eq_zero_of (fun i hi => h i hi)

/-- **`zAxReduct` preserves regularity.** On atomic axioms it returns a `zAx1` node (`zReg = 0`);
otherwise it is the identity. So a regular premise yields a regular per-premise reduct. -/
lemma ZRegular_zAxReduct {x : V} (h : ZRegular x) : ZRegular (zAxReduct x) := by
  unfold zAxReduct
  by_cases h5 : zTag x = 5
  · rw [if_pos h5]; unfold ZRegular; exact zReg_zAx1 _ _
  · by_cases h6 : zTag x = 6
    · rw [if_neg h5, if_pos h6]; unfold ZRegular; exact zReg_zAx1 _ _
    · rw [if_neg h5, if_neg h6]; exact h

/-- Every premise's `zReg` is dominated by the chain fold (mirror `le_iseqMaxEigen`). -/
lemma le_iseqRegAux {ds : V} : ∀ j : V, ∀ i < j, zReg (znth ds i) ≤ iseqRegAux ds j := by
  intro j
  induction j using ISigma1.sigma1_succ_induction
  · refine Definable.ball_lt (by definability) ?_
    apply Definable.comp₂ <;> definability
  case zero => intro i hi; exact absurd hi (by simp)
  case succ j ih =>
    intro i hi
    rw [iseqRegAux_succ]
    rcases eq_or_lt_of_le (le_iff_lt_succ.mpr hi) with h | h
    · subst h; exact le_max_right _ _
    · exact le_trans (ih i h) (le_max_left _ _)

lemma le_iseqReg {ds i : V} (hi : i < lh ds) : zReg (znth ds i) ≤ iseqReg ds := le_iseqRegAux _ i hi

/-- **A premise of a regular chain is regular** (the converse of `ZRegular_zK_of_premises`; needed to
extract the splice halves' regularity in the 5.2.1 case). -/
lemma ZRegular_zK_premise {s r ds i : V} (hds : Seq ds) (h : ZRegular (zK s r ds)) (hi : i < lh ds) :
    ZRegular (znth ds i) := by
  unfold ZRegular at h ⊢
  rw [zReg_zK s r ds hds] at h
  exact nonpos_iff_eq_zero.mp (h ▸ le_iseqReg hi)

/-- **Regularity of a `seqUpdate` chain** (5.2.2 replace `iRKr`, and each half of 5.1 `iRKc`): replacing
one premise by a regular reduct keeps the chain regular. -/
lemma ZRegular_zK_of_seqUpdate {s' r' ds i v : V}
    (hall : ∀ m < lh ds, ZRegular (znth ds m)) (hv : ZRegular v) :
    ZRegular (zK s' r' (seqUpdate ds i v)) := by
  refine ZRegular_zK_of_premises (seqUpdate_seq ds i v) ?_
  intro m hm
  rw [seqUpdate_lh] at hm
  rcases eq_or_ne m i with rfl | hne
  · rw [znth_seqUpdate_self hm]; exact hv
  · rw [znth_seqUpdate_of_ne hne]; exact hall m hm

/-- **Regularity of an `iCritReductSeq` chain** (5.1 critical `iRcritG`/`iRKc`): the two-element chain
`⟨d0, d1⟩` is regular when both halves are. -/
lemma ZRegular_zK_of_iCritReductSeq {s' r' d0 d1 : V} (h0 : ZRegular d0) (h1 : ZRegular d1) :
    ZRegular (zK s' r' (iCritReductSeq d0 d1)) :=
  ZRegular_zK_of_premises (iCritReductSeq_seq d0 d1) (forall_lt_iCritReductSeq h0 h1)

/-- **The re-keyed critical reduct `iRKcCrit` is regular.** The engine swap's `ZRegular_red_zK_crit` re-proof
target: each of the two `iCritReductSeq` halves is a `seqUpdate` of the chain's premise sequence swapping one
redex premise for its §3.2-case-5.1 corrected reduct. Regular when (a) every original premise is
(`hprem`, from the chain's own regularity) and (b) the swapped reduct is — the I∀ slot via
`ZRegular_zsubst_zIallPrem`, the I¬ slot via `ZRegular_zInegPrem`, the L-redex `zAx1` slots free
(`zReg_zAx1`). The R-redex must be an I-rule (`htagI`: tag 1 or 2), which holds on the orbit
(`tp dᵢ = isymR`). Polarity-dispatch matches `iRKcCrit`'s own `zTag dᵢ = 1` branch. -/
lemma ZRegular_iRKcCrit {d : V}
    (hprem : ∀ m < lh (zKseq d), ZRegular (znth (zKseq d) m))
    (hdI : ZDerivation (znth (zKseq d) (redexI d)))
    (hregI : ZRegular (znth (zKseq d) (redexI d)))
    (htagI : zTag (znth (zKseq d) (redexI d)) = 1 ∨ zTag (znth (zKseq d) (redexI d)) = 2) :
    ZRegular (iRKcCrit d) := by
  have hax : ∀ a b : V, ZRegular (zAx1 a b) := fun a b => by unfold ZRegular; exact zReg_zAx1 _ _
  rw [iRKcCrit]
  split
  case isTrue h1 =>
    rw [iCritReductG]
    exact ZRegular_zK_of_iCritReductSeq
      (ZRegular_zK_of_seqUpdate hprem (ZRegular_zsubst_zIallPrem hdI hregI h1))
      (ZRegular_zK_of_seqUpdate hprem (hax _ _))
  case isFalse h1 =>
    have h2 : zTag (znth (zKseq d) (redexI d)) = 2 := htagI.resolve_left h1
    rw [iCritReductG]
    exact ZRegular_zK_of_iCritReductSeq
      (ZRegular_zK_of_seqUpdate hprem (hax _ _))
      (ZRegular_zK_of_seqUpdate hprem (ZRegular_zInegPrem hdI hregI h2))

/-- **Regularity of a `seqInsert` chain** (5.2.1 splice `iRKs`): inserting two regular halves `a,b` in
place of premise `i` keeps the chain regular. The 5.2.1 analogue of `ZRegular_zK_of_seqUpdate`, via the
pointwise read-out `forall_znth_seqInsert`. -/
lemma ZRegular_zK_of_seqInsert {s' r' ds i a b : V} (hi : i < lh ds)
    (hall : ∀ m < lh ds, ZRegular (znth ds m)) (ha : ZRegular a) (hb : ZRegular b) :
    ZRegular (zK s' r' (seqInsert ds i a b)) := by
  refine ZRegular_zK_of_premises (seqInsert_seq ds i a b) ?_
  intro n hn
  rw [seqInsert_lh] at hn
  exact forall_znth_seqInsert (P := ZRegular) hi ha hb hall n hn

/-! ### `red`-preserves-`ZRegular`, the `zK` chain dispatch (5.1 / 5.2.1 / 5.2.2)

`red (zK s r ds)` dispatches via `iRK` on two criticality sentinels (`red_zK_crit`/`_rep`/`_splice`).
Each branch reduct is a chain over a `seqUpdate`/`seqInsert`/`iCritReductSeq` of `ds` with one or two
premises swapped for already-tabulated reducts `red dᵢ`. The structural-block lemmas above close the
`seqUpdate`/`iCritReductSeq` branches **standalone** from the IH (`ZRegular (red premise)`); the
`seqInsert` (5.2.1) branch additionally needs the two splice **halves** `znth (zKseq (red dᵢ)) {0,1}`
regular, which holds when `red dᵢ` is a chain (`tag 4`) — exactly the `zKValidF`-supplied fact threaded
inside `redSound` (lap-93 finding). So `_replace`/`_crit` are unconditional; `_splice` takes the
halves' regularity as an explicit hypothesis. -/

/-- **5.2.2 replace recursion equation** (port of the `Crux2Blueprint` `red_zK_rep`, here in the build):
non-critical chain whose least-permissible premise is itself non-critical ⟹ `red` swaps premise
`i = permIdx d` for its tabulated reduct `red dᵢ`. -/
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

/-- **5.2.1 splice recursion equation** (lap-95 GATED dispatch): non-critical chain `d` whose
least-permissible premise `dᵢ` is itself a CRITICAL CHAIN (`zTag dᵢ = 4` AND `dᵢ` critical) ⟹ `red`
splices `dᵢ`'s two reduct-halves `znth (zKseq (red dᵢ)) {0,1}` in place at `i`. The `zTag dᵢ = 4` gate
(`htag`) is the lap-95 faithfulness fix: only a genuine chain has meaningful reduct-halves. -/
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

/-- **5.2.2 replace recursion equation for a NON-CHAIN selected premise** (lap-95 GATED dispatch).
When the least-permissible premise `dᵢ` is not a chain (`zTag dᵢ ≠ 4`) — atom / I-rule / axiom — the
gated `iRK` routes it to the replace branch `iRKr` (Buchholz Def 3.2 case 5.2.2) regardless of `dᵢ`'s
`permIdx` sentinel. This is the lap-94 obstruction's cure: the OLD `iRK` mis-spliced such premises
(`permIdx dᵢ = 0 = lh(zKseq dᵢ)` triggered the splice by default); the gate now sends them to replace. -/
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

/-! ### I∀ conclusion-tracking — `red (zIall …)` derives the `tpReduce`'d sequent (route-B, lap 98)

The replace branch of `ZDerivation_red_zK` (`Crux2Blueprint.lean:206/214`) needs, for a NON-`Rep`
selected premise `dᵢ`, that the I∀ reduct `red dᵢ = zsubst d0 a 0` carries exactly the reduced
end-sequent `tpReduce (R_∀xF) (end dᵢ) 0 = Γ→F(0)` — the lap-97 eigensubst made `red dᵢ` *derive*
`Γ→F(0)`; this lemma certifies its end-sequent IS `Γ→F(0)`, so the conclusion-reduced chain validity
(`isChainInf` on the swapped premise) can consume it. The I∀ analogue of the proved I¬
`red_zIneg_tpReduce` (`InternalZ.lean:7521`); harder because I∀ *substitutes* the eigenvariable, so it
needs the eigenvariable-freshness facts `a ∉ FV(p)` / `a ∉ FV(Γ)` (Buchholz's eigenvariable condition,
O3 — supplied on the orbit by the embedding's fresh-eigenvariable choice). -/

/-- **I∀ reduct end-sequent = the `tpReduce`'d sequent.** Given the eigenvariable `a` is fresh in the
matrix `p` (`hpfresh`) and in the conclusion antecedent `Γ = seqAnt s` (`hΓfresh`), the I∀ reduct
`red (zIall s a p d0) = zsubst d0 a 0` has end-sequent `tpReduce (tp (zIall …)) s 0 = Γ→F(0)`. This is
the route-B conclusion-tracking fact for the ∀-principal cut (`red_zIneg_tpReduce` is its I¬ sibling). -/
lemma red_zIall_tpReduce {s a p d0 : V} (hZ : ZDerivation (zIall s a p d0))
    (hpfresh : fvSubst ℒₒᵣ a (Bootstrapping.Arithmetic.numeral 0) p = p)
    (hΓfresh : fvSubstSeq a (Bootstrapping.Arithmetic.numeral 0) (seqAnt s) = seqAnt s) :
    fstIdx (red (zIall s a p d0))
      = tpReduce (tp (zIall s a p d0)) (fstIdx (zIall s a p d0)) 0 := by
  obtain ⟨hd0, _, hwff⟩ := zDerivation_zIall_inv hZ
  have ht0 : IsSemiterm ℒₒᵣ 0 (Bootstrapping.Arithmetic.numeral 0 : V) := by simp
  have hfa : IsSemiterm ℒₒᵣ 0 (^&a : V) := by simp
  rw [red_zIall, tp_zIall, fstIdx_zIall, tpReduce_isymR_all, fstIdx_zsubst _ _ hd0]
  simp only [fvSubstSeqt, seqSetSucc, hwff.1, hwff.2.1, hΓfresh,
    fvSubst_substs1 ht0 hfa hwff.2.2, termFvSubst_fvar_self, hpfresh]

/-- **The ∀-inversion building block (general instance `t`).** Substituting the I∀ eigenvariable `a` by
ANY closed term `t` in the premise derivation `d0` yields a derivation whose succedent is the INSTANCE
`F(t) = substs1 t p`. Generalizes `red_zIall_tpReduce` (the `t = 0` case that `red` currently fixes).

⚠️ **This is the lap-114 crux finding.** The critical-cut SOUNDNESS inversion `ZDerivation_red_zK_crit`
(`Crux2Blueprint:100`) reduces, via `ZDerivation_iRcritG_of`, to two stripped half-derivations `haux0`
(`Γ → cutFormula d`) / `haux1`. The left half's threading (`isChainInf`) forces its R-redex premise to
derive exactly `cutFormula d = F(k)`, where `k` is the L-redex instance (`cutFormula_all`). But the reduct
`red` supplies there is `zAxReduct (red premise) = zsubst d0 a (numeral 0)` — instance **0**, NOT `k`. So
`haux0` is UNPROVABLE for `ρ = zAxReduct ∘ red`: `red`'s critical reduct is unsound (it substitutes the
wrong instance). Instance-0 is correct for the ordinal DESCENT (`iord (zsubst d0 a n)` is instance-
invariant) but wrong for SOUNDNESS, which needs Buchholz §3.2 case 5.1 re-principalization at `k`. The
fix: the critical reduct's R-redex premise must be `zsubst d0 a (numeral k)`. This lemma is its succedent
identity — with `k` the L-redex instance, `zsubst d0 a (numeral k)` derives `Γ → F(k) = Γ → cutFormula d`,
so `haux0`'s threading closes. The reduct is a `ZDerivation` by `ZDerivation_zsubst_zIall_premise`; the
matrix/Γ freshness `hpfresh` (a ∉ FV p, the eigenvariable condition, Buchholz O3) is supplied on the
⊥-orbit by the embedding's fresh-eigenvariable choice. See `PENDING_WORK` lap-114. -/
lemma seqSucc_zsubst_zIall_premise {s a p d0 t : V} (ht : IsSemiterm ℒₒᵣ 0 t)
    (hZ : ZDerivation (zIall s a p d0)) (hpfresh : fvSubst ℒₒᵣ a t p = p) :
    seqSucc (fstIdx (zsubst d0 a t)) = substs1 ℒₒᵣ t p := by
  obtain ⟨hd0, _, hwff⟩ := zDerivation_zIall_inv hZ
  have hfa : IsSemiterm ℒₒᵣ 0 (^&a : V) := by simp
  rw [fstIdx_zsubst _ _ hd0, seqSucc_fvSubstSeqt, hwff.2.1, fvSubst_substs1 ht hfa hwff.2.2]
  simp only [termFvSubst_fvar_self, hpfresh]

/-- **The corrected critical reduct's R-redex premise derives `cutFormula d` (second linchpin).** When the
redexI premise of a critical chain `d` is an I∀ node `zIall sᵢ a p d0` (R-principal for `∀p`), the
re-principalized reduct `zsubst d0 a (numeral k)` at the L-redex instance `k = π₁(π₂(tp (redexJ premise)))`
— the SAME `k` that `cutFormula` reads — derives succedent exactly `cutFormula d`. Combines
`seqSucc_zsubst_zIall_premise` (the instance-`k` succedent) with `cutFormula_all` (`cutFormula d = F(k)` in
the `∀`-branch). This is what makes the corrected `haux0`'s `isChainInf` j₀=redexI succedent clause hold —
the step `red`'s instance-0 reduct cannot provide (lap-114 finding). Modulo the eigenvariable freshness
`hpfresh` (Buchholz O3, supplied on the ⊥-orbit). -/
lemma seqSucc_corrected_redexI_eq_cutFormula {d sᵢ a p d0 : V}
    (hIall : znth (zKseq d) (redexI d) = zIall sᵢ a p d0)
    (hpremZ : ZDerivation (zIall sᵢ a p d0))
    (hpfresh : fvSubst ℒₒᵣ a
        (Bootstrapping.Arithmetic.numeral (π₁ (π₂ (tp (znth (zKseq d) (redexJ d)))))) p = p) :
    seqSucc (fstIdx (zsubst d0 a
        (Bootstrapping.Arithmetic.numeral (π₁ (π₂ (tp (znth (zKseq d) (redexJ d)))))))) = cutFormula d := by
  have hprincipal : chainAsucc (zKseq d) (redexI d) = (^∀ p : V) := by
    unfold chainAsucc; rw [hIall, fstIdx_zIall]; exact (zDerivation_zIall_inv hpremZ).2.1
  rw [seqSucc_zsubst_zIall_premise (by simp) hpremZ hpfresh, cutFormula_all hprincipal]

/-- **The corrected reduct's FULL end-sequent (general instance `t`).** Generalizes `red_zIall_tpReduce`
from the fixed `t = 0` to any closed term: the eigensubst premise `zsubst d0 a t` of a valid I∀ node has
end-sequent `Γ → F(t) = seqSetSucc s (substs1 t p)` (antecedent `Γ` kept by `hΓfresh`, succedent the
instance `F(t)`). The antecedent half is what `haux0`'s `hant`/`hX_ant` need; the succedent half is
linchpin #1. -/
lemma fstIdx_zsubst_zIall_premise {s a p d0 t : V} (ht : IsSemiterm ℒₒᵣ 0 t)
    (hZ : ZDerivation (zIall s a p d0)) (hpfresh : fvSubst ℒₒᵣ a t p = p)
    (hΓfresh : fvSubstSeq a t (seqAnt s) = seqAnt s) :
    fstIdx (zsubst d0 a t) = seqSetSucc s (substs1 ℒₒᵣ t p) := by
  obtain ⟨hd0, _, hwff⟩ := zDerivation_zIall_inv hZ
  have hfa : IsSemiterm ℒₒᵣ 0 (^&a : V) := by simp
  rw [fstIdx_zsubst _ _ hd0]
  simp only [fvSubstSeqt, seqSetSucc, hwff.1, hwff.2.1, hΓfresh,
    fvSubst_substs1 ht hfa hwff.2.2, termFvSubst_fvar_self, hpfresh]

/-- **5.2.2 replace branch — regularity preserved (unconditional).** `red (zK s r ds) = K^r(i/red dᵢ)`;
regular since every original premise is (`ZRegular_zK_premise`) and the swapped reduct `red dᵢ` is (IH). -/
lemma ZRegular_red_zK_replace {s r ds : V} (hds : Seq ds)
    (hreg : ZRegular (zK s r ds))
    (hred : ∀ i < lh ds, ZRegular (red (znth ds i)))
    (h1 : permIdx (zK s r ds) < lh ds)
    (h2 : permIdx (znth ds (permIdx (zK s r ds)))
        < lh (zKseq (znth ds (permIdx (zK s r ds))))) :
    ZRegular (red (zK s r ds)) := by
  rw [red_zK_rep h1 h2]
  exact ZRegular_zK_of_seqUpdate
    (fun m hm => ZRegular_zK_premise hds hreg hm) (hred _ h1)

/-- **5.1 critical branch — regularity preserved.** `red (zK s r ds) = iRcritG …` is a chain over
`iCritReductSeq d{0} d{1}`, each half a `seqUpdate` of `ds` swapping a redex premise for its tabulated
reduct `red (znth ds (redexI/J))`; regular when those two reducts are (supplied — they are IH instances
once the redex indices are in range). -/
lemma ZRegular_red_zK_crit {s r ds : V} (hds : Seq ds)
    (hreg : ZRegular (zK s r ds))
    (hI : ZRegular (red (znth ds (redexI (zK s r ds)))))
    (hJ : ZRegular (red (znth ds (redexJ (zK s r ds)))))
    (hcrit : ¬ permIdx (zK s r ds) < lh ds) :
    ZRegular (red (zK s r ds)) := by
  rw [red_zK_crit hcrit, iRcritG]
  simp only [fstIdx_zK, zKseq_zK, zKrank_zK, iCritReductG]
  refine ZRegular_zK_of_iCritReductSeq ?_ ?_
  · exact ZRegular_zK_of_seqUpdate
      (fun m hm => ZRegular_zK_premise hds hreg hm) (ZRegular_zAxReduct hI)
  · exact ZRegular_zK_of_seqUpdate
      (fun m hm => ZRegular_zK_premise hds hreg hm) (ZRegular_zAxReduct hJ)

/-- **Premise extraction from a critical reduct `iRcritG d ρ`.** Its premise sequence is the two-element
`iCritReductSeq`, so when the whole reduct is regular both halves `znth (zKseq (iRcritG d ρ)) {0,1}` are.
The extraction the 5.2.1 splice needs for the halves of `red dᵢ` once `dᵢ` is known to be a chain. -/
lemma ZRegular_iRcritG_premise {d ρk : V} {ρ : V → V} (h : ZRegular (iRcritG d ρ)) (hk : ρk < 2) :
    ZRegular (znth (zKseq (iRcritG d ρ)) ρk) := by
  rw [iRcritG, iCritReductG] at h ⊢
  rw [zKseq_zK]
  exact ZRegular_zK_premise (iCritReductSeq_seq _ _) h (by rw [iCritReductSeq_lh]; exact hk)

/-- **5.2.1 splice branch — regularity preserved, given the halves are regular.** `red (zK s r ds)`
splices the two halves `a,b = znth (zKseq (red dᵢ)) {0,1}` in place at `i`; regular when every original
premise is (`ZRegular_zK_premise`) and `a,b` are. The halves' regularity holds when `red dᵢ` is a chain
(`tag 4`), discharged inside `redSound` from the `zKValidF`-supplied tag (lap-93 finding) — here an
explicit hypothesis. -/
lemma ZRegular_red_zK_splice {s r ds : V} (hds : Seq ds)
    (hreg : ZRegular (zK s r ds))
    (h1 : permIdx (zK s r ds) < lh ds)
    (h2 : ¬ permIdx (znth ds (permIdx (zK s r ds)))
        < lh (zKseq (znth ds (permIdx (zK s r ds)))))
    (htag : zTag (znth ds (permIdx (zK s r ds))) = 4)
    (ha : ZRegular (znth (zKseq (red (znth ds (permIdx (zK s r ds))))) 0))
    (hb : ZRegular (znth (zKseq (red (znth ds (permIdx (zK s r ds))))) 1)) :
    ZRegular (red (zK s r ds)) := by
  rw [red_zK_splice h1 h2 htag]
  exact ZRegular_zK_of_seqInsert h1
    (fun m hm => ZRegular_zK_premise hds hreg hm) ha hb

/-- **5.2.1 splice branch — regularity preserved, from the selected premise being a CHAIN.** Strengthens
`ZRegular_red_zK_splice`: the two splice halves' regularity is *derived* from `zTag dᵢ = 4` (the selected
premise `dᵢ` is itself a chain) together with the IH `ZRegular (red dᵢ)`. Since the splice branch is taken
exactly when `dᵢ` is *critical* (`h2`), `red dᵢ = iRcritG dᵢ …` is a two-premise critical reduct, so its
halves are premises of a regular chain (`ZRegular_iRcritG_premise`). This is the interface `redSound`
consumes — the `zTag dᵢ = 4` fact comes from the `zKValidF` validity data threaded through the induction
(lap-93 finding). -/
lemma ZRegular_red_zK_splice_of_chain {s r ds : V} (hds : Seq ds)
    (hreg : ZRegular (zK s r ds))
    (hred : ∀ i < lh ds, ZRegular (red (znth ds i)))
    (h1 : permIdx (zK s r ds) < lh ds)
    (h2 : ¬ permIdx (znth ds (permIdx (zK s r ds)))
        < lh (zKseq (znth ds (permIdx (zK s r ds)))))
    (hchain : ZDerivation (znth ds (permIdx (zK s r ds))))
    (htag : zTag (znth ds (permIdx (zK s r ds))) = 4) :
    ZRegular (red (zK s r ds)) := by
  -- reconstruct the selected premise dᵢ as a chain `zK s' r' ds'`
  rcases zDerivation_iff.mp hchain with ⟨s', heq, _⟩ | ⟨s', a, p, d0, heq, _, _⟩ |
    ⟨s', p, d0, heq, _, _⟩ | ⟨s', at', p, d0, d1, heq, _, _⟩ |
    ⟨s', r', ds', heq, hds', _, _⟩ | ⟨s', p, k, heq, _, _⟩ | ⟨s', p, heq, _, _⟩ | ⟨s', C, heq, _⟩
  · rw [heq] at htag; simp at htag
  · rw [heq] at htag; simp at htag
  · rw [heq] at htag; simp at htag
  · rw [heq] at htag; simp at htag
  · -- the chain case: dᵢ = zK s' r' ds', so red dᵢ = iRcritG dᵢ … (critical by h2)
    have hcrit : ¬ permIdx (zK s' r' ds') < lh ds' := by
      rw [heq, zKseq_zK] at h2; exact h2
    have hregred : ZRegular (iRcritG (zK s' r' ds') (fun n => zAxReduct (red (znth ds' n)))) := by
      have h := hred (permIdx (zK s r ds)) h1
      rwa [heq, red_zK_crit hcrit] at h
    refine ZRegular_red_zK_splice hds hreg h1 h2 htag ?_ ?_
    · rw [heq, red_zK_crit hcrit]; exact ZRegular_iRcritG_premise hregred zero_lt_two
    · rw [heq, red_zK_crit hcrit]; exact ZRegular_iRcritG_premise hregred one_lt_two
  · rw [heq] at htag; simp at htag
  · rw [heq] at htag; simp at htag
  · rw [heq] at htag; simp at htag

/-- **`red` preserves `ZRegular` — the full `zK` chain case (lap-95: `hseltag` DISCHARGED).** Dispatches
on the GATED `iRK` (lap 95): `permIdx (zK s r ds) < lh ds` (chain non-critical) splits on whether the
selected premise `dᵢ` is a chain (`zTag dᵢ = 4`); a chain dispatches further on `dᵢ`'s own criticality
(non-critical → replace `ZRegular_red_zK_replace`, critical → splice `ZRegular_red_zK_splice_of_chain`
with `zTag dᵢ = 4` now supplied by the gate), while a NON-chain goes to the conclusion-replace
`red_zK_rep_nonchain` (the lap-94 obstruction's cure — the OLD `iRK` mis-spliced non-chains). The 5.1
critical branch's redex bounds are discharged INTERNALLY from the chain's own validity
(`zKValidF_of_ZDerivation_zK` + `zKCritical_of_not_permIdx_lt` + `redexI_redexJ_lt_of_zKValid`). The
former leaf `hseltag` is **GONE**: under the gated dispatch the splice branch IS the `zTag dᵢ = 4` case.
This is the regularity (O1) half of "red preserves valid+regular", now UNCONDITIONAL; the validity half
needs the `tpReduce` conclusion-reduction (lap-90). -/
lemma ZRegular_red_zK {s r ds : V} (hds : Seq ds)
    (hZ : ZDerivation (zK s r ds)) (hreg : ZRegular (zK s r ds))
    (hred : ∀ i < lh ds, ZRegular (red (znth ds i))) :
    ZRegular (red (zK s r ds)) := by
  by_cases h1 : permIdx (zK s r ds) < lh ds
  · by_cases htag : zTag (znth ds (permIdx (zK s r ds))) = 4
    · by_cases h2 : permIdx (znth ds (permIdx (zK s r ds)))
          < lh (zKseq (znth ds (permIdx (zK s r ds))))
      · -- chain selected premise, non-critical → replace
        exact ZRegular_red_zK_replace hds hreg hred h1 h2
      · -- chain selected premise, critical → splice (`htag` from the gate)
        exact ZRegular_red_zK_splice_of_chain hds hreg hred h1 h2
          ((zDerivation_zK_inv hZ).2 _ h1) htag
    · -- NON-chain selected premise → replace (the lap-94 obstruction's cure)
      rw [red_zK_rep_nonchain h1 htag]
      exact ZRegular_zK_of_seqUpdate
        (fun m hm => ZRegular_zK_premise hds hreg hm) (hred _ h1)
  · have hvalid : zKValid s r ds := zKValid_iff_zKValidF_and_zKCritical.mpr
      ⟨zKValidF_of_ZDerivation_zK hZ, zKCritical_of_not_permIdx_lt h1⟩
    obtain ⟨hI, hJ⟩ := redexI_redexJ_lt_of_zKValid hvalid
    exact ZRegular_red_zK_crit hds hreg (hred _ hI) (hred _ hJ) h1

/-- **`red` preserves `ZRegular` — the full structural theorem (O1, UNCONDITIONAL).** The eigenvariable
freshness (Buchholz's side-condition, tracked by `zReg`) is hereditarily preserved by the genuine reduct
`red`. Assembled by `zDerivation_induction`: every non-chain node delegates to `ZRegular_red_of_not_zK`
(structural / Ind / axiom cases, with the I-rule eigenvar-strip kept fresh by `zReg_zIall`/`zReg_zIneg`);
the chain (`zK`) node delegates to the unconditional `ZRegular_red_zK`, feeding the per-premise IH
`ZRegular (red dᵢ)` (each premise regular by `ZRegular_zK_premise`). This is the O1 half of "red preserves
valid + regular" — the validity half (`ZDerivation_red_zK`, Crux2Blueprint) is the remaining frontier. -/
theorem ZRegular_red : ∀ d : V, ZDerivation d → ZRegular d → ZRegular (red d) := by
  have key : ∀ d : V, ZDerivation d → (ZRegular d → ZRegular (red d)) := by
    apply zDerivation_induction (P := fun d => ZRegular d → ZRegular (red d))
    · definability
    · intro C hC d hphi hreg
      rcases hphi with ⟨s, rfl, hin⟩ | ⟨s, a, p, d0, rfl, hd0, hsc, hwff⟩ |
        ⟨s, p, d0, rfl, hd0, hsc, hwff⟩ | ⟨s, at', p, d0, d1, rfl, h0, h1, hwff⟩ |
        ⟨s, r, ds, rfl, hds, hmem, hvalid⟩ | ⟨s, p, k, rfl, hp, hin⟩ | ⟨s, p, rfl, hp, hin, hin2⟩ |
        ⟨s, C, rfl, hin⟩
      · exact ZRegular_red_of_not_zK
          (zDerivation_iff.mpr (Or.inl ⟨s, rfl, hin⟩)) hreg (by simp [zTag_zAtom])
      · exact ZRegular_red_of_not_zK
          (zDerivation_iff.mpr (Or.inr (Or.inl ⟨s, a, p, d0, rfl, (hC d0 hd0).1, hsc, hwff⟩)))
          hreg (by simp [zTag_zIall])
      · exact ZRegular_red_of_not_zK
          (zDerivation_iff.mpr (Or.inr (Or.inr (Or.inl ⟨s, p, d0, rfl, (hC d0 hd0).1, hsc, hwff⟩))))
          hreg (by simp [zTag_zIneg])
      · exact ZRegular_red_of_not_zK
          (zDerivation_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inl
            ⟨s, at', p, d0, d1, rfl, (hC d0 h0).1, (hC d1 h1).1, hwff⟩)))))
          hreg (by simp [zTag_zInd])
      · refine ZRegular_red_zK hds
          (zDerivation_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
            ⟨s, r, ds, rfl, hds, fun i hi => (hC (znth ds i) (hmem i hi)).1, hvalid⟩))))))
          hreg (fun i hi => (hC (znth ds i) (hmem i hi)).2 (ZRegular_zK_premise hds hreg hi))
      · exact ZRegular_red_of_not_zK
          (zDerivation_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
            (Or.inl ⟨s, p, k, rfl, hp, hin⟩))))))) hreg (by simp [zTag_zAxAll])
      · exact ZRegular_red_of_not_zK
          (zDerivation_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
            (Or.inr (Or.inl ⟨s, p, rfl, hp, hin, hin2⟩)))))))) hreg (by simp [zTag_zAxNeg])
      · exact ZRegular_red_of_not_zK
          (zDerivation_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
            (Or.inr (Or.inr ⟨s, C, rfl, hin⟩)))))))) hreg (by simp [zTag_zAx1])
  exact key

/-! ### ✅ The `hseltag` leaf — RESOLVED (lap 95) by the gated `iRK` dispatch

**Historical (lap 94 obstruction, now fixed).** The former `ZRegular_red_zK` leaf `hseltag` claimed the
splice-branch selected premise `dᵢ` is a chain (`zTag dᵢ = 4`). Under the OLD `iRK` this was FALSE: the
inner sentinel `permIdx dᵢ < lh (zKseq dᵢ)` routed to *replace* when true and *splice* when false, and for
a NON-chain `dᵢ` (atom/I-rule/axiom) `lh (zKseq dᵢ) = 0`, so `0 < 0 = false` fired the splice by default —
the splice did NOT imply `zTag dᵢ = 4`. **Lap-95 fix (`iRK`, `InternalZ.lean`):** the splice is now GATED
on `zTag dᵢ = 4 ∧ ¬ permIdx dᵢ < lh (zKseq dᵢ)` (= dᵢ a genuine *critical chain*); a non-chain selected
premise is routed to the replace `iRKr` (Buchholz Def 3.2 case 5.2.2, via `red_zK_rep_nonchain`). So the
splice branch now CONTAINS `zTag dᵢ = 4`, `hseltag` is derivable, and `ZRegular_red_zK` (above) is
UNCONDITIONAL. The witness `not_permIdx_lt_zKseq_zAtom` below stays as the in-kernel record of *why* the
gate is needed (the OLD dispatch mis-fired on atoms). The validity-half (`ZDerivation_red_zK`,
Crux2Blueprint) still needs the `tpReduce` conclusion-reduction for the non-`Rep` replace (lap-90). -/

/-- **`zKseq` of a non-chain atom node is the empty code** (`length 0`). -/
@[simp] lemma zKseq_zAtom (s : V) : zKseq (zAtom s) = 0 := by
  simp [zKseq, zRest, sndIdx, zAtom, pi₂_zero]

/-- The atom node's premise-sequence length is `0`. -/
@[simp] lemma lh_zKseq_zAtom (s : V) : lh (zKseq (zAtom s)) = 0 := by
  rw [zKseq_zAtom]
  conv_lhs => rw [← emptyset_def]
  exact lh_empty

/-- **⛔ Obstruction witness: an atom selected premise hits the 5.2.1 SPLICE branch.** `lh (zKseq (zAtom
s)) = 0`, so the replace-branch sentinel `permIdx (zAtom s) < lh (zKseq (zAtom s))` is `0 < 0 = false` and
`iRK` dispatches to the splice — refuting `hseltag` (the splice branch does NOT force `zTag dᵢ = 4`). The
in-kernel proof that the repo's `iRK` chain-criticality dispatch is Buchholz-unfaithful for non-chain
selected premises, so `ZRegular_red_zK`'s final leaf cannot be closed against the current `red`/`iRK`; the
route-B `tp`-driven dispatch is required. -/
lemma not_permIdx_lt_zKseq_zAtom (s : V) : ¬ permIdx (zAtom s) < lh (zKseq (zAtom s)) := by
  rw [lh_zKseq_zAtom]; simp

/-! ## `ZDerivation_zsubst` — eigenvariable substitution preserves Z-derivability (rung-1 step C)

Substituting the closed term `t` for the free variable `^&a` throughout a Z-derivation `d` whose every
eigenvariable index is `< a` (i.e. `maxEigen d < a`) yields a Z-derivation of the substituted end-sequent.
Proved by `zDerivation_induction` on `d`, dispatching the one-step `ZPhi` rule and rebuilding the same rule
on the substituted data; each rule's well-formedness transfers through the `fvSubst` commutation lemmas
(`fvSubst_all`/`fvSubst_substs1`/`fvSubst_substs1_fvar`/`fvSubst_inegF`/`inAnt_fvSubstSeq`) and the step-A
term helpers.

**Lap-93 reformulation (Path-X §3).** The hypothesis is now `maxEigen d < a` (the genuine *freshness*
bound) rather than the code bound `d ≤ a`. The two facts the proof needs from it — eigenvariable
freshness `e ≠ a` and the recursive premise bound — both follow from the `maxEigen` recursion equations:
each node's own eigenvariable and each premise's `maxEigen` are `≤ maxEigen d < a`. Critically, unlike
`d ≤ a`, this bound is **stable under `zsubst`** (`maxEigen_zsubst`), so it is maintainable through `red`. -/
theorem ZDerivation_zsubst {a t : V} (ht : IsSemiterm ℒₒᵣ 0 t) :
    ∀ d, ZDerivation d → maxEigen d < a → ZDerivation (zsubst d a t) := by
  apply zDerivation_induction (P := fun d => maxEigen d < a → ZDerivation (zsubst d a t))
  · definability
  · intro C hC d hphi
    rcases hphi with ⟨s, rfl, hatom⟩ | ⟨s, e, p, d0, rfl, hd0, hsc, hwff⟩ |
      ⟨s, p, d0, rfl, hd0, hsc, hwff⟩ | ⟨s, at', p, d0, d1, rfl, hd0, hd1, hwff⟩ |
      ⟨s, r, ds, rfl, hseq, hmem, hvalid⟩ | ⟨s, p, k, rfl, hp, hin⟩ | ⟨s, p, rfl, hp, hin, hin2⟩ |
      ⟨s, C, rfl, hin⟩
    -- atom
    · intro _
      rw [zsubst_zAtom]
      refine zDerivation_iff.mpr (Or.inl ⟨fvSubstSeqt a t s, rfl, ?_⟩)
      rw [seqSucc_fvSubstSeqt, seqAnt_fvSubstSeqt]
      exact inAnt_fvSubstSeq hatom
    -- zIall
    · intro hda
      rw [maxEigen_zIall] at hda
      have hd0Z : ZDerivation d0 := (hC d0 hd0).1
      have hp1 : IsSemiformula ℒₒᵣ 1 p := hwff.2.2
      have hea : e ≠ a := (lt_of_le_of_lt (le_max_left e (maxEigen d0)) hda).ne
      rw [zsubst_zIall]
      refine zDerivation_iff.mpr (Or.inr (Or.inl
        ⟨fvSubstSeqt a t s, e, fvSubst ℒₒᵣ a t p, zsubst d0 a t, rfl, ?_, ?_, ?_, ?_, ?_⟩))
      · exact (hC d0 hd0).2 (lt_of_le_of_lt (le_max_right e (maxEigen d0)) hda)
      · rw [seqSucc_fvSubstSeqt, hsc, fvSubst_all hp1.isUFormula]
      · rw [fstIdx_zsubst a t hd0Z, seqAnt_fvSubstSeqt, seqAnt_fvSubstSeqt, hwff.1]
      · rw [fstIdx_zsubst a t hd0Z, seqSucc_fvSubstSeqt, hwff.2.1,
          fvSubst_substs1_fvar ht hea hp1]
      · exact fvSubst_isSemiformula ht hp1
    -- zIneg
    · intro hda
      rw [maxEigen_zIneg] at hda
      have hd0Z : ZDerivation d0 := (hC d0 hd0).1
      have hpU : IsUFormula ℒₒᵣ p := hwff.2.2
      rw [zsubst_zIneg]
      refine zDerivation_iff.mpr (Or.inr (Or.inr (Or.inl
        ⟨fvSubstSeqt a t s, fvSubst ℒₒᵣ a t p, zsubst d0 a t, rfl, ?_, ?_, ?_, ?_, ?_⟩)))
      · exact (hC d0 hd0).2 hda
      · rw [seqSucc_fvSubstSeqt, hsc, fvSubst_inegF ht.isUTerm hpU]
      · rw [fstIdx_zsubst a t hd0Z, seqSucc_fvSubstSeqt, hwff.1, fvSubst_falsum (L := ℒₒᵣ)]
      · rw [fstIdx_zsubst a t hd0Z, seqAnt_fvSubstSeqt]
        exact inAnt_fvSubstSeq hwff.2.1
      · exact IsUFormula.fvSubst ht.isUTerm hpU
    -- zInd
    · intro hda
      rw [maxEigen_zInd] at hda
      have hd0Z : ZDerivation d0 := (hC d0 hd0).1
      have hd1Z : ZDerivation d1 := (hC d1 hd1).1
      -- derive freshness + premise bounds from `hda` BEFORE the `at' = ⟪…⟫` rewrite (which touches `hda`)
      have hea : π₁ at' ≠ a := (lt_of_le_of_lt (le_max_left _ _) hda).ne
      have hZ0 : ZDerivation (zsubst d0 a t) := (hC d0 hd0).2
        (lt_of_le_of_lt (le_trans (le_max_left (maxEigen d0) (maxEigen d1)) (le_max_right _ _)) hda)
      have hZ1 : ZDerivation (zsubst d1 a t) := (hC d1 hd1).2
        (lt_of_le_of_lt (le_trans (le_max_right (maxEigen d0) (maxEigen d1)) (le_max_right _ _)) hda)
      simp only [zIndWff, zIndEig_zInd, zIndTerm_zInd, zIndP_zInd, zIndPrem0_zInd, zIndPrem1_zInd,
        fstIdx_zInd] at hwff
      obtain ⟨⟨h1a, h1b⟩, ⟨h2a, h2b⟩, h3, h4, h5⟩ := hwff
      rw [show at' = ⟪π₁ at', π₂ at'⟫ from (pair_unpair at').symm, zsubst_zInd]
      refine zDerivation_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨fvSubstSeqt a t s, ⟪π₁ at', termFvSubst ℒₒᵣ a t (π₂ at')⟫, fvSubst ℒₒᵣ a t p,
          zsubst d0 a t, zsubst d1 a t, rfl, ?_, ?_, ?_⟩))))
      · exact hZ0
      · exact hZ1
      · simp only [zIndWff, zIndEig_zInd, zIndTerm_zInd, zIndP_zInd, zIndPrem0_zInd, zIndPrem1_zInd,
          fstIdx_zInd, pi₁_pair, pi₂_pair]
        refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
        · rw [fstIdx_zsubst a t hd0Z, seqAnt_fvSubstSeqt, seqAnt_fvSubstSeqt, h1a]
        · rw [fstIdx_zsubst a t hd0Z, seqSucc_fvSubstSeqt, h1b,
            fvSubst_substs1 ht (by simp) h4, termFvSubst_numeral]
        · rw [fstIdx_zsubst a t hd1Z, seqAnt_fvSubstSeqt, ← fvSubst_substs1_fvar ht hea h4]
          exact inAnt_fvSubstSeq h2a
        · rw [fstIdx_zsubst a t hd1Z, seqSucc_fvSubstSeqt, h2b,
            fvSubst_substs1 ht (isSemiterm_succVar _) h4, termFvSubst_succVar hea]
        · rw [seqSucc_fvSubstSeqt, h3, fvSubst_substs1 ht h5 h4]
        · exact fvSubst_isSemiformula ht h4
        · exact IsSemitermVec.termFvSubst ht h5
    -- zK: rebuild the chain on the substituted premises; validity transfers because every premise's
    -- eigenvariables are `< a` (freshness), so `isChainInf`/`iperm`/criticality all carry over.
    · intro hda
      rw [maxEigen_zK s r ds hseq] at hda
      obtain ⟨hci, hperm, hf1, hf2, hf5, hf6, hcf, hssf, hsaf⟩ := hvalid
      have hZpr : ∀ i < lh ds, ZDerivation (znth ds i) := fun i hi => (hC _ (hmem i hi)).1
      have hprle : ∀ i < lh ds, maxEigen (znth ds i) < a := fun i hi =>
        lt_of_le_of_lt (le_iseqMaxEigen hi) hda
      have hmap : ∀ i < lh ds,
          znth (tblMapSeq (zsubstTable a t (zK s r ds - 1)) ds) i = zsubst (znth ds i) a t := by
        intro i hi
        rw [znth_tblMapSeq hi, znth_zsubstTable_eq_zsubst a t _ (znth ds i)
          (le_pred_of_lt (lt_of_le_of_lt (znth_le_self ds i) (ds_lt_zK s r ds)))]
      have hlh : lh (tblMapSeq (zsubstTable a t (zK s r ds - 1)) ds) = lh ds := tblMapSeq_lh _ _
      rw [zsubst_zK]
      refine zDerivation_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨fvSubstSeqt a t s, r, tblMapSeq (zsubstTable a t (zK s r ds - 1)) ds, rfl, ?_, ?_, ?_⟩)))))
      · exact tblMapSeq_seq _ _
      · intro i hi
        rw [hlh] at hi
        rw [hmap i hi]
        exact (hC _ (hmem i hi)).2 (hprle i hi)
      · refine ⟨isChainInf_zsubst ht.isUTerm hlh hZpr hmap hcf hci, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro i hi
          rw [hlh] at hi
          rw [hmap i hi, fstIdx_zsubst a t (hZpr i hi)]
          exact iperm_tp_zsubst ht (hZpr i hi) (hperm i hi)
        · intro i hi htag
          rw [hlh] at hi
          rw [hmap i hi] at htag ⊢
          rw [zTag_zsubst (hZpr i hi)] at htag
          rw [zIallF_zsubst (hZpr i hi) htag]
          exact IsUFormula.fvSubst ht.isUTerm (hf1 i hi htag)
        · intro i hi htag
          rw [hlh] at hi
          rw [hmap i hi] at htag ⊢
          rw [zTag_zsubst (hZpr i hi)] at htag
          rw [zInegF_zsubst (hZpr i hi) htag]
          exact IsUFormula.fvSubst ht.isUTerm (hf2 i hi htag)
        · intro i hi htag
          rw [hlh] at hi
          rw [hmap i hi] at htag ⊢
          rw [zTag_zsubst (hZpr i hi)] at htag
          rw [zAxAllF_zsubst (hZpr i hi) htag]
          exact IsUFormula.fvSubst ht.isUTerm (hf5 i hi htag)
        · intro i hi htag
          rw [hlh] at hi
          rw [hmap i hi] at htag ⊢
          rw [zTag_zsubst (hZpr i hi)] at htag
          rw [zAxNegF_zsubst (hZpr i hi) htag]
          exact IsUFormula.fvSubst ht.isUTerm (hf6 i hi htag)
        · intro i hi
          rw [hlh] at hi
          simp only [chainAsucc, hmap i hi, fstIdx_zsubst a t (hZpr i hi), seqSucc_fvSubstSeqt]
          exact IsUFormula.fvSubst ht.isUTerm (hcf i hi)
        · rw [seqSucc_fvSubstSeqt]
          exact IsUFormula.fvSubst ht.isUTerm hssf
        · intro k hk
          rw [seqAnt_fvSubstSeqt] at hk ⊢
          rw [fvSubstSeq_lh] at hk
          rw [znth_fvSubstSeq hk]
          exact IsUFormula.fvSubst ht.isUTerm (hsaf k hk)
    -- zAxAll
    · intro _
      rw [zsubst_zAxAll]
      refine zDerivation_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨fvSubstSeqt a t s, fvSubst ℒₒᵣ a t p, k, rfl, ?_, ?_⟩))))))
      · exact IsUFormula.fvSubst ht.isUTerm hp
      · rw [seqAnt_fvSubstSeqt, ← fvSubst_all hp]
        exact inAnt_fvSubstSeq hin
    -- zAxNeg
    · intro _
      rw [zsubst_zAxNeg]
      refine zDerivation_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨fvSubstSeqt a t s, fvSubst ℒₒᵣ a t p, rfl, ?_, ?_, ?_⟩)))))))
      · exact IsUFormula.fvSubst ht.isUTerm hp
      · rw [seqAnt_fvSubstSeqt, ← fvSubst_inegF ht.isUTerm hp]
        exact inAnt_fvSubstSeq hin
      · rw [seqAnt_fvSubstSeqt]
        exact inAnt_fvSubstSeq hin2
    -- zAx1
    · intro _
      rw [zsubst_zAx1]
      refine zDerivation_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨fvSubstSeqt a t s, C, rfl, ?_⟩)))))))
      rw [seqSucc_fvSubstSeqt, seqAnt_fvSubstSeqt]
      exact inAnt_fvSubstSeq hin

/-! ## Route-B eigensubst reducts, discharged by `ZDerivation_zsubst` under a freshness bound

**Lap-92 corrected decomposition (`ANALYSIS-2026-06-25-lap92-criticality-wall-is-gone.md`).** Buchholz's
conclusion-reducing reduct (route B) needs, for the `I∀` rule, `red(zIall s a p d0) = d0(a/n)` deriving
`Γ→F(n)`, and for the `Ind` rule the step-premise substitutions `d1(a/i)`. The lap-91 handoff filed this
as **O2 = "the lap-78 substitution wall"**, but that is a misattribution: the lap-78 wall was the
*criticality* conjunct, which `ZPhi` no longer carries (it uses criticality-free `zKValidF`). The genuine
eigensubst — *preserving `zKValidF`* — is **already proven** by `ZDerivation_zsubst`; its only side
condition is the genuine freshness bound `maxEigen premise < eigenvariable` (every eigenvariable index of
the premise is `< a`, so it differs from `a`). These two corollaries make that explicit: **O2 is
discharged; the entire residual obligation is producing the bound (`maxEigen d0 < a` /
`maxEigen d1 < π₁ at'`) = O1, the eigenvariable-freshness tracking that `zIallWff`/`zIndWff` must add and
`red` must maintain** — now phrased on `maxEigen` (substitution-stable by `maxEigen_zsubst`, lap 93). -/

/-- **I∀ eigensubst reduct (route B), under the freshness bound.** The premise `d0` of a valid `zIall`
node, with the eigenvariable substituted by a closed term `t`, is a `ZDerivation` — *provided* the
freshness bound `maxEigen d0 < a` holds (O1: every eigenvariable index of `d0` is below the bound `a`).
The substitution itself (O2) is the existing `ZDerivation_zsubst`; no new "substitution preserves
validity" lemma is needed (the lap-78 obstruction was criticality, now absent from `zKValidF`). -/
theorem ZDerivation_zsubst_zIall_premise {s a p d0 t : V} (ht : IsSemiterm ℒₒᵣ 0 t)
    (hZ : ZDerivation (zIall s a p d0)) (hfresh : maxEigen d0 < a) :
    ZDerivation (zsubst d0 a t) :=
  ZDerivation_zsubst ht d0 (zDerivation_zIall_inv hZ).1 hfresh

/-- **Ind step-premise eigensubst reduct (route B), under the freshness bound.** The induction-step
premise `d1` of a valid `zInd` node, with the eigenvariable `π₁ at'` substituted by a closed term `t`
(Buchholz case 4: `d1(a/0)…d1(a/k-1)`), is a `ZDerivation` — provided `maxEigen d1 < π₁ at'` (O1). Same
decomposition as `ZDerivation_zsubst_zIall_premise`. -/
theorem ZDerivation_zsubst_zInd_premise1 {s at' p d0 d1 t : V} (ht : IsSemiterm ℒₒᵣ 0 t)
    (hZ : ZDerivation (zInd s at' p d0 d1)) (hfresh : maxEigen d1 < π₁ at') :
    ZDerivation (zsubst d1 (π₁ at') t) :=
  ZDerivation_zsubst ht d1 (zDerivation_zInd_inv hZ).2.1 hfresh

end GoodsteinPA.InternalZ
