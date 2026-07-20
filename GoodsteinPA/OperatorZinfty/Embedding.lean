module

public import GoodsteinPA.OperatorZinfty.Basic

@[expose] public section

namespace GoodsteinPA.OperatorZinfty

open LO LO.FirstOrder LO.FirstOrder.ArithmeticTerm ONote

/-! ### The PA-induction leaf's witness side condition

The unbounded `PXFc` induction-axiom construction in `EmbeddingBound.metaInduction_cong_bdd`
uses an `∃`-introduction with witness `n` at the `n`-th step of the cut tower.  In `Provable` that
move is legal only when the witness is bounded by `hardy e (k+d)`.

These lemmas isolate the decisive arithmetic.  A fixed numeric index cannot support all
witnesses, but the running `allω` index `max k n` can.  So the induction leaf is not blocked
at the witness side condition; any remaining difficulty is the structural port of the finite
EM/cut/value-substitution tower.
-/

/-- A fixed numeric index cannot bound the witnesses `n` needed by the induction cut tower. -/
lemma inductionLeaf_fixedIndex_witnessBound_impossible (e : ONote) (k d : ℕ) :
  ¬∀ n : ℕ, n ≤ hardy e (k + d) := by
  push Not;
  use (hardy e (k + d) + 1);
  omega

/-- The `n`-th `allω` premise runs at index `max k n`, which is large enough to pay for
the `∃`-witness `n`. -/
lemma inductionLeaf_runningIndex_witnessBound (e : ONote) (k d n : ℕ) : n ≤ hardy e (max k n + d) :=
  le_trans (by omega) (le_hardy e (max k n + d))

/-- The actual `Provable.exI` move needed in the induction-axiom leaf is legal at the running
index.  This is the local replacement for the unbounded proof's free `PXFc.exI` step. -/
lemma inductionLeaf_exI_runningIndex_probe {α β e} {k d c n} {Γ}
    {φ : ArithmeticSemiformula ℕ 1}
    (hβ : β < α) (hβNF : β.NF) (hαNF : α.NF) (hτ : norm β < max k n + d)
    (D : Provable β e (max k n) d c (insert (φ/[nm n]) Γ)) :
    Provable α e (max k n) d c (insert (∃⁰ φ) Γ) :=
  Provable.exI φ n hβ hβNF hαNF hτ (inductionLeaf_runningIndex_witnessBound e k d n) D

/-! #### Bounded embedding leaves: value-congruent atomic closure -/

/-- The standard value of a closed arithmetic term, in the evaluator used by `atomTrue`. -/
noncomputable abbrev stdClosedVal (t : ArithmeticTerm ℕ) : ℕ :=
  GoodsteinPA.Compat.gVal (Arithmetic.standardModel ℕ) (fun _ => 0) (fun _ => 0) t

/-- The standard value of the numeral term `nm m` is `m`. -/
@[simp] lemma stdClosedVal_nm (m : ℕ) : stdClosedVal (nm m) = m := by simp [stdClosedVal, nm]

/-- Substitution-composition for extending an assignment by a numeral in the freed variable. -/
lemma embedding_subst_q_cons {n : ℕ} (w : Fin n → ArithmeticTerm ℕ) (m : ℕ) :
    (Rew.subst ![nm m]).comp (Rew.subst w).q = Rew.subst (nm m :> w) := by
  ext x
  · cases x using Fin.cases with
    | zero => simp [Rew.comp_app]
    | succ i => simp [Rew.comp_app]
  · simp [Rew.comp_app]

/-- Formula form of `embedding_subst_q_cons`. -/
lemma embedding_subst_q_cons_app {n : ℕ} (w : Fin n → ArithmeticTerm ℕ) (m : ℕ)
    (ψ : ArithmeticSemiformula ℕ (n + 1)) :
    ((Rew.subst w).q ▹ ψ)/[nm m] = Rew.subst (nm m :> w) ▹ ψ := by
  show Rew.subst ![nm m] ▹ ((Rew.subst w).q ▹ ψ) = Rew.subst (nm m :> w) ▹ ψ
  rw [← TransitiveRewriting.comp_app, embedding_subst_q_cons]

/-- Standard-value congruence for renamed terms, ported to the `Provable` embedding probes. -/
lemma embedding_valm_subst_congr {n : ℕ} (w w' : Fin n → ArithmeticTerm ℕ)
    (hval : ∀ i, stdClosedVal (w i) = stdClosedVal (w' i))
    (t : ArithmeticSemiterm ℕ n) :
    stdClosedVal (Rew.subst w t) = stdClosedVal (Rew.subst w' t) := by
  simp only [stdClosedVal, Semiterm.val_substs]
  congr 1
  funext x; exact hval x

/-- Extending two value-equal assignments by the same numeral preserves pointwise value equality. -/
lemma embedding_valm_cons_nm_congr {n : ℕ} (w w' : Fin n → ArithmeticTerm ℕ) (m : ℕ)
    (hval : ∀ i, stdClosedVal (w i) = stdClosedVal (w' i)) :
    ∀ i, stdClosedVal ((nm m :> w) i) = stdClosedVal ((nm m :> w') i) := by
  intro i
  cases i using Fin.cases with
  | zero => simp
  | succ j => simpa using hval j

/-- Truth of a closed atomic relation only depends on the standard values of its terms. -/
lemma atomTrue_rel_congr {ar : ℕ} (r : (ℒₒᵣ).Rel ar)
    (v v' : Fin ar → ArithmeticTerm ℕ)
    (hval : ∀ i, stdClosedVal (v i) = stdClosedVal (v' i)) :
    atomTrue (Semiformula.rel r v) ↔ atomTrue (Semiformula.rel r v') := by
  have hv : (fun i => GoodsteinPA.Compat.gVal (Arithmetic.standardModel ℕ) (fun _ => 0) (fun _ => 0) (v i))
      = (fun i => GoodsteinPA.Compat.gVal (Arithmetic.standardModel ℕ) (fun _ => 0) (fun _ => 0) (v' i)) := by
    funext i; exact hval i
  simp only [atomTrue, Semiformula.eval_rel, hv, Function.comp_def]

/-- Truth of a closed negated atomic relation only depends on the standard values of its terms. -/
lemma atomTrue_nrel_congr {ar : ℕ} (r : (ℒₒᵣ).Rel ar)
    (v v' : Fin ar → ArithmeticTerm ℕ)
    (hval : ∀ i, stdClosedVal (v i) = stdClosedVal (v' i)) :
    atomTrue (Semiformula.nrel r v) ↔ atomTrue (Semiformula.nrel r v') := by
  have hv : (fun i => GoodsteinPA.Compat.gVal (Arithmetic.standardModel ℕ) (fun _ => 0) (fun _ => 0) (v i))
      = (fun i => GoodsteinPA.Compat.gVal (Arithmetic.standardModel ℕ) (fun _ => 0) (fun _ => 0) (v' i)) := by
    funext i; exact hval i
  simp only [atomTrue, Semiformula.eval_nrel, hv, Function.comp_def]

lemma atomTrue_nrel_iff_not_rel {ar : ℕ} (r : (ℒₒᵣ).Rel ar)
    (v : Fin ar → ArithmeticTerm ℕ) :
    atomTrue (Semiformula.nrel r v) ↔ ¬ atomTrue (Semiformula.rel r v) := by
  simp [atomTrue, Semiformula.eval_rel, Semiformula.eval_nrel, Function.comp_def]

lemma atomTrue_rel_iff_not_nrel {ar : ℕ} (r : (ℒₒᵣ).Rel ar)
    (v : Fin ar → ArithmeticTerm ℕ) :
    atomTrue (Semiformula.rel r v) ↔ ¬ atomTrue (Semiformula.nrel r v) := by
  simp [atomTrue, Semiformula.eval_rel, Semiformula.eval_nrel, Function.comp_def]

section ValueCongruentAtoms

variable {α e : ONote} {k d c : ℕ} {Γ : Finset (ArithmeticFormula ℕ)}

/--
Bounded value-congruent atomic closure, relation-positive side.

This is the `Provable` base leaf needed by assignment-carrying embedding: if the sequent contains
`R(v)` and `¬R(v')`, and the closed term vectors have equal standard values, a bounded truth leaf
closes the sequent at any normal ordinal whose norm fits the current budget.
-/
lemma embedding_valueCongruentRelAtom_probe {ar : ℕ}
    (r : (ℒₒᵣ).Rel ar) (v v' : Fin ar → ArithmeticTerm ℕ)
    (hval : ∀ i, stdClosedVal (v i) = stdClosedVal (v' i))
    (hαNF : α.NF) (hτ : norm α < k + d)
    (hp : Semiformula.rel r v ∈ Γ) (hn : Semiformula.nrel r v' ∈ Γ) :
    Provable α e k d c Γ := by
  by_cases hrel : atomTrue (Semiformula.rel r v)
  · exact Provable.trueRel r v hrel hτ hαNF hp
  · have hrel' : ¬ atomTrue (Semiformula.rel r v') := by
      intro hv'
      exact hrel ((atomTrue_rel_congr r v v' hval).mpr hv')
    exact Provable.trueNrel r v' ((atomTrue_nrel_iff_not_rel r v').mpr hrel') hτ hαNF hn

/--
Bounded value-congruent atomic closure, negated-relation-positive side.

This is the polarity twin of `embedding_valueCongruentRelAtom_probe`.
-/
lemma embedding_valueCongruentNrelAtom_probe {ar : ℕ}
    (r : (ℒₒᵣ).Rel ar) (v v' : Fin ar → ArithmeticTerm ℕ)
    (hval : ∀ i, stdClosedVal (v i) = stdClosedVal (v' i))
    (hαNF : α.NF) (hτ : norm α < k + d)
    (hp : Semiformula.nrel r v ∈ Γ) (hn : Semiformula.rel r v' ∈ Γ) :
    Provable α e k d c Γ := by
  by_cases hnrel : atomTrue (Semiformula.nrel r v)
  · exact Provable.trueNrel r v hnrel hτ hαNF hp
  · have hnrel' : ¬ atomTrue (Semiformula.nrel r v') := by
      intro hv'
      exact hnrel ((atomTrue_nrel_congr r v v' hval).mpr hv')
    exact Provable.trueRel r v' ((atomTrue_rel_iff_not_nrel r v').mpr hnrel') hτ hαNF hn

/-- Substituted-term form of the bounded value-congruent relation atom leaf. -/
lemma embedding_valueCongruentRelSubstAtom_probe {ar n : ℕ}
    (r : (ℒₒᵣ).Rel ar) (w w' : Fin n → ArithmeticTerm ℕ)
    (v : Fin ar → ArithmeticSemiterm ℕ n)
    (hval : ∀ i, stdClosedVal (w i) = stdClosedVal (w' i))
    (hαNF : α.NF) (hτ : norm α < k + d)
    (hp : Semiformula.rel r (fun i => Rew.subst w (v i)) ∈ Γ)
    (hn : Semiformula.nrel r (fun i => Rew.subst w' (v i)) ∈ Γ) :
    Provable α e k d c Γ :=
  embedding_valueCongruentRelAtom_probe r
    (fun i => Rew.subst w (v i)) (fun i => Rew.subst w' (v i))
    (fun i => embedding_valm_subst_congr w w' hval (v i)) hαNF hτ hp hn

/-- Substituted-term form of the bounded value-congruent negated-relation atom leaf. -/
lemma embedding_valueCongruentNrelSubstAtom_probe {ar n : ℕ}
    (r : (ℒₒᵣ).Rel ar) (w w' : Fin n → ArithmeticTerm ℕ)
    (v : Fin ar → ArithmeticSemiterm ℕ n)
    (hval : ∀ i, stdClosedVal (w i) = stdClosedVal (w' i))
    (hαNF : α.NF) (hτ : norm α < k + d)
    (hp : Semiformula.nrel r (fun i => Rew.subst w (v i)) ∈ Γ)
    (hn : Semiformula.rel r (fun i => Rew.subst w' (v i)) ∈ Γ) :
    Provable α e k d c Γ :=
  embedding_valueCongruentNrelAtom_probe r
    (fun i => Rew.subst w (v i)) (fun i => Rew.subst w' (v i))
    (fun i => embedding_valm_subst_congr w w' hval (v i)) hαNF hτ hp hn

/-- Closed-term specialization of the value-congruent relation atom leaf. -/
lemma embedding_valueCongruentRelClosedTermAtom_probe
    {ar : ℕ}
    (r : (ℒₒᵣ).Rel ar) (s s' : ArithmeticTerm ℕ)
    (v : Fin ar → ArithmeticSemiterm ℕ 1)
    (hval : stdClosedVal s = stdClosedVal s')
    (hαNF : α.NF) (hτ : norm α < k + d)
    (hp : (Semiformula.rel r v)/[s] ∈ Γ)
    (hn : (Semiformula.nrel r v)/[s'] ∈ Γ) :
    Provable α e k d c Γ := by
  refine embedding_valueCongruentRelSubstAtom_probe r ![s] ![s'] v ?_ hαNF hτ ?_ ?_
  · intro i
    cases i using Fin.cases with
    | zero => simpa using hval
    | succ j => exact Fin.elim0 j
  · simpa [Semiformula.rew_rel, Function.comp_def] using hp
  · simpa [Semiformula.rew_nrel, Function.comp_def] using hn

/-- Closed-term specialization of the value-congruent negated-relation atom leaf. -/
lemma embedding_valueCongruentNrelClosedTermAtom_probe
    {ar : ℕ}
    (r : (ℒₒᵣ).Rel ar) (s s' : ArithmeticTerm ℕ)
    (v : Fin ar → ArithmeticSemiterm ℕ 1)
    (hval : stdClosedVal s = stdClosedVal s')
    (hαNF : α.NF) (hτ : norm α < k + d)
    (hp : (Semiformula.nrel r v)/[s] ∈ Γ)
    (hn : (Semiformula.rel r v)/[s'] ∈ Γ) :
    Provable α e k d c Γ := by
  refine embedding_valueCongruentNrelSubstAtom_probe r ![s] ![s'] v ?_ hαNF hτ ?_ ?_
  · intro i
    cases i using Fin.cases with
    | zero => simpa using hval
    | succ j => exact Fin.elim0 j
  · simpa [Semiformula.rew_nrel, Function.comp_def] using hp
  · simpa [Semiformula.rew_rel, Function.comp_def] using hn

/-- Constant-true base case for the bounded value-congruent EM engine. -/
lemma embedding_valueCongruentVerum_probe {n : ℕ}
    (w : Fin n → ArithmeticTerm ℕ)
    (hp : (Rew.subst w ▹ (⊤ : ArithmeticSemiformula ℕ n)) ∈ Γ) :
    Provable α e k d c Γ :=
  Provable.verumR (by simpa using hp)

/-- Constant-false base case for the bounded value-congruent EM engine. -/
lemma embedding_valueCongruentFalsum_probe {n : ℕ}
    (w' : Fin n → ArithmeticTerm ℕ)
    (hn : (∼(Rew.subst w' ▹ (⊥ : ArithmeticSemiformula ℕ n))) ∈ Γ) :
    Provable α e k d c Γ :=
  Provable.verumR (by simpa using hn)

end ValueCongruentAtoms

section ValueCongruentChildren

variable {e : ONote} {k d c : ℕ} {Γ : Finset (ArithmeticFormula ℕ)}

/--
Bounded closed-term existential introduction, reduced to the genuine remaining EM/congruence premise.

This is the assignment-carrying embedding adapter for Foundation's `exs` rule: after an open witness term
has been closed by an assignment, its standard value `stdClosedVal s` is used as the numeral witness.
The only non-structural input is the value-congruent premise converting `ψ[s]` to `ψ[nm (stdClosedVal s)]`.
-/
lemma embedding_closedTermExI_of_valueCongruentEM_probe
    {βSrc βCong αCut αOut : ONote}
    {ψ : ArithmeticSemiformula ℕ 1} (s : ArithmeticTerm ℕ)
    (hψc : (ψ/[s]).complexity < c)
    (hSrcLt : βSrc < αCut) (hCongLt : βCong < αCut) (hCutLt : αCut < αOut)
    (hSrcNF : βSrc.NF) (hCongNF : βCong.NF) (hCutNF : αCut.NF) (hOutNF : αOut.NF)
    (hτSrc : norm βSrc < k + d) (hτCong : norm βCong < k + d)
    (hτCut : norm αCut < k + d)
    (hbound : stdClosedVal s ≤ hardy e (k + d))
    (dSrc : Provable βSrc e k d c (insert (ψ/[s]) Γ))
    (dCong : Provable βCong e k d c
      (insert (∼(ψ/[s])) (insert (ψ/[nm (stdClosedVal s)]) Γ))) :
    Provable αOut e k d c (insert (∃⁰ ψ) Γ) := by
  have dSrc' : Provable βSrc e k d c
      (insert (ψ/[s]) (insert (ψ/[nm (stdClosedVal s)]) Γ)) :=
    Provable.wk (Finset.insert_subset_insert _ (Finset.subset_insert _ _)) dSrc
  have dNumeral : Provable αCut e k d c (insert (ψ/[nm (stdClosedVal s)]) Γ) :=
    Provable.cut (ψ/[s]) hψc hSrcLt hCongLt hSrcNF hCongNF hCutNF hτSrc hτCong
      dSrc' dCong
  exact Provable.exI ψ (stdClosedVal s) hCutLt hCutNF hOutNF hτCut hbound dNumeral

/--
Conjunction step for the bounded value-congruent EM engine.

Given child derivations closing `a` against its value-congruent negation and `b` against its
value-congruent negation, this composes them into the parent sequent containing
`(a ∧ b)[w]` and `¬(a ∧ b)[w']`.  The theorem is intentionally phrased with explicit child
ordinals: the future recursive engine can choose any ordinal schedule and discharge these
side conditions separately.
-/
lemma embedding_valueCongruentAndFromChildren_probe
    {n : ℕ} {βA βB αAnd αOut : ONote}
    (w w' : Fin n → ArithmeticTerm ℕ) (a b : ArithmeticSemiformula ℕ n)
    (hA_lt : βA < αAnd) (hB_lt : βB < αAnd) (hAnd_lt : αAnd < αOut)
    (hANF : βA.NF) (hBNF : βB.NF) (hAndNF : αAnd.NF) (hOutNF : αOut.NF)
    (hτA : norm βA < k + d) (hτB : norm βB < k + d) (hτAnd : norm αAnd < k + d)
    (hp : (Rew.subst w ▹ (a ⋏ b)) ∈ Γ)
    (hn : (∼(Rew.subst w' ▹ (a ⋏ b))) ∈ Γ)
    (dA : Provable βA e k d c
      (insert (Rew.subst w ▹ a)
        (insert (∼(Rew.subst w' ▹ a)) (insert (∼(Rew.subst w' ▹ b)) Γ))))
    (dB : Provable βB e k d c
      (insert (Rew.subst w ▹ b)
        (insert (∼(Rew.subst w' ▹ a)) (insert (∼(Rew.subst w' ▹ b)) Γ)))) :
    Provable αOut e k d c Γ := by
  have hp' : ((Rew.subst w ▹ a) ⋏ (Rew.subst w ▹ b)) ∈ Γ := by
    simpa using hp
  have hn' : (∼(Rew.subst w' ▹ a) ⋎ ∼(Rew.subst w' ▹ b)) ∈ Γ := by
    simpa using hn
  have hand : Provable αAnd e k d c
      (insert (∼(Rew.subst w' ▹ a)) (insert (∼(Rew.subst w' ▹ b)) Γ)) := by
    have h := Provable.andI (Rew.subst w ▹ a) (Rew.subst w ▹ b)
      hA_lt hB_lt hANF hBNF hAndNF hτA hτB dA dB
    rw [Finset.insert_eq_self.mpr
      (show ((Rew.subst w ▹ a) ⋏ (Rew.subst w ▹ b))
          ∈ insert (∼(Rew.subst w' ▹ a)) (insert (∼(Rew.subst w' ▹ b)) Γ) by
        simp [hp'])] at h
    exact h
  have hor := Provable.orI (∼(Rew.subst w' ▹ a)) (∼(Rew.subst w' ▹ b))
    hAnd_lt hAndNF hOutNF hτAnd hand
  rwa [Finset.insert_eq_self.mpr hn'] at hor

/--
Disjunction step for the bounded value-congruent EM engine.

This is the polarity-dual parent constructor to
`embedding_valueCongruentAndFromChildren_probe`: child closures for `a` and `b` build
`¬a[w'] ∧ ¬b[w']`, then `Provable.orI` packages the positive `a[w] ∨ b[w]` parent.
-/
lemma embedding_valueCongruentOrFromChildren_probe
    {n : ℕ} {βA βB αAnd αOut : ONote}
    (w w' : Fin n → ArithmeticTerm ℕ) (a b : ArithmeticSemiformula ℕ n)
    (hA_lt : βA < αAnd) (hB_lt : βB < αAnd) (hAnd_lt : αAnd < αOut)
    (hANF : βA.NF) (hBNF : βB.NF) (hAndNF : αAnd.NF) (hOutNF : αOut.NF)
    (hτA : norm βA < k + d) (hτB : norm βB < k + d) (hτAnd : norm αAnd < k + d)
    (hp : (Rew.subst w ▹ (a ⋎ b)) ∈ Γ)
    (hn : (∼(Rew.subst w' ▹ (a ⋎ b))) ∈ Γ)
    (dA : Provable βA e k d c
      (insert (∼(Rew.subst w' ▹ a))
        (insert (Rew.subst w ▹ a) (insert (Rew.subst w ▹ b) Γ))))
    (dB : Provable βB e k d c
      (insert (∼(Rew.subst w' ▹ b))
        (insert (Rew.subst w ▹ a) (insert (Rew.subst w ▹ b) Γ)))) :
    Provable αOut e k d c Γ := by
  have hp' : ((Rew.subst w ▹ a) ⋎ (Rew.subst w ▹ b)) ∈ Γ := by
    simpa using hp
  have hn' : (∼(Rew.subst w' ▹ a) ⋏ ∼(Rew.subst w' ▹ b)) ∈ Γ := by
    simpa using hn
  have hand : Provable αAnd e k d c
      (insert (Rew.subst w ▹ a) (insert (Rew.subst w ▹ b) Γ)) := by
    have h := Provable.andI (∼(Rew.subst w' ▹ a)) (∼(Rew.subst w' ▹ b))
      hA_lt hB_lt hANF hBNF hAndNF hτA hτB dA dB
    rw [Finset.insert_eq_self.mpr
      (show (∼(Rew.subst w' ▹ a) ⋏ ∼(Rew.subst w' ▹ b))
          ∈ insert (Rew.subst w ▹ a) (insert (Rew.subst w ▹ b) Γ) by
        simp [hn'])] at h
    exact h
  have hor := Provable.orI (Rew.subst w ▹ a) (Rew.subst w ▹ b)
    hAnd_lt hAndNF hOutNF hτAnd hand
  rwa [Finset.insert_eq_self.mpr hp'] at hor

/-- Closed-term specialization of the conjunction parent constructor. -/
lemma embedding_valueCongruentAndClosedTermFromChildren_probe
    {βA βB αAnd αOut : ONote}
    (s s' : ArithmeticTerm ℕ) (a b : ArithmeticSemiformula ℕ 1)
    (hA_lt : βA < αAnd) (hB_lt : βB < αAnd) (hAnd_lt : αAnd < αOut)
    (hANF : βA.NF) (hBNF : βB.NF) (hAndNF : αAnd.NF) (hOutNF : αOut.NF)
    (hτA : norm βA < k + d) (hτB : norm βB < k + d) (hτAnd : norm αAnd < k + d)
    (hp : ((a ⋏ b)/[s]) ∈ Γ)
    (hn : (∼((a ⋏ b)/[s'])) ∈ Γ)
    (dA : Provable βA e k d c
      (insert (a/[s]) (insert (∼(a/[s'])) (insert (∼(b/[s'])) Γ))))
    (dB : Provable βB e k d c
      (insert (b/[s]) (insert (∼(a/[s'])) (insert (∼(b/[s'])) Γ)))) :
    Provable αOut e k d c Γ := by
  refine embedding_valueCongruentAndFromChildren_probe ![s] ![s'] a b
    hA_lt hB_lt hAnd_lt hANF hBNF hAndNF hOutNF hτA hτB hτAnd ?_ ?_ ?_ ?_
  · simpa using hp
  · simpa using hn
  · simpa using dA
  · simpa using dB

/-- Closed-term specialization of the disjunction parent constructor. -/
lemma embedding_valueCongruentOrClosedTermFromChildren_probe
    {βA βB αAnd αOut : ONote}
    (s s' : ArithmeticTerm ℕ) (a b : ArithmeticSemiformula ℕ 1)
    (hA_lt : βA < αAnd) (hB_lt : βB < αAnd) (hAnd_lt : αAnd < αOut)
    (hANF : βA.NF) (hBNF : βB.NF) (hAndNF : αAnd.NF) (hOutNF : αOut.NF)
    (hτA : norm βA < k + d) (hτB : norm βB < k + d) (hτAnd : norm αAnd < k + d)
    (hp : ((a ⋎ b)/[s]) ∈ Γ)
    (hn : (∼((a ⋎ b)/[s'])) ∈ Γ)
    (dA : Provable βA e k d c
      (insert (∼(a/[s'])) (insert (a/[s]) (insert (b/[s]) Γ))))
    (dB : Provable βB e k d c
      (insert (∼(b/[s'])) (insert (a/[s]) (insert (b/[s]) Γ)))) :
    Provable αOut e k d c Γ := by
  refine embedding_valueCongruentOrFromChildren_probe ![s] ![s'] a b
    hA_lt hB_lt hAnd_lt hANF hBNF hAndNF hOutNF hτA hτB hτAnd ?_ ?_ ?_ ?_
  · simpa using hp
  · simpa using hn
  · simpa using dA
  · simpa using dB

end ValueCongruentChildren

/-! #### A first recursive bounded value-congruence shell -/

/-- Quantifier-free arithmetic formulas.  This is the first bounded EM shell needed by the
embedding probes; the quantifier cases are handled separately by the `allω`/`exI` layer. -/
def QFreeForm {ξ n} : Semiformula ℒₒᵣ ξ n → Prop :=
  Semiformula.rec' (C := fun _ _ => Prop)
    True True
    (fun {_ _} _ _ => True)
    (fun {_ _} _ _ => True)
    (fun {_} _ _ p q => p ∧ q)
    (fun {_} _ _ p q => p ∧ q)
    (fun {_} _ _ => False)
    (fun {_} _ _ => False)

@[simp] lemma qFreeForm_verum {ξ n} : QFreeForm (⊤ : Semiformula ℒₒᵣ ξ n) := trivial
@[simp] lemma qFreeForm_falsum {ξ n} : QFreeForm (⊥ : Semiformula ℒₒᵣ ξ n) := trivial
@[simp] lemma qFreeForm_rel {ξ n ar} (r : (ℒₒᵣ).Rel ar) (v : Fin ar → Semiterm ℒₒᵣ ξ n) :
    QFreeForm (Semiformula.rel r v) := trivial
@[simp] lemma qFreeForm_nrel {ξ n ar} (r : (ℒₒᵣ).Rel ar) (v : Fin ar → Semiterm ℒₒᵣ ξ n) :
    QFreeForm (Semiformula.nrel r v) := trivial
@[simp] lemma qFreeForm_and {ξ n} (φ ψ : Semiformula ℒₒᵣ ξ n) :
    QFreeForm (φ ⋏ ψ) ↔ QFreeForm φ ∧ QFreeForm ψ := Iff.rfl
@[simp] lemma qFreeForm_or {ξ n} (φ ψ : Semiformula ℒₒᵣ ξ n) :
    QFreeForm (φ ⋎ ψ) ↔ QFreeForm φ ∧ QFreeForm ψ := Iff.rfl
@[simp] lemma qFreeForm_all {ξ n} (φ : Semiformula ℒₒᵣ ξ (n + 1)) :
    QFreeForm (∀⁰ φ) ↔ False := Iff.rfl
@[simp] lemma qFreeForm_exs {ξ n} (φ : Semiformula ℒₒᵣ ξ (n + 1)) :
    QFreeForm (∃⁰ φ) ↔ False := Iff.rfl

lemma embedding_ofNat_lt_of_lt {m n : ℕ} (h : m < n) : ONote.ofNat m < ONote.ofNat n := by
  rw [ONote.lt_def, ONote.repr_ofNat, ONote.repr_ofNat]
  exact_mod_cast h

@[simp] lemma embedding_norm_ofNat (n : ℕ) : norm (ONote.ofNat n) = n := by
  cases n with
  | zero => rfl
  | succ k => rw [ONote.ofNat_succ, norm_oadd, norm_zero]; simp

section ValueCongruentEM

variable {K d c : ℕ} {e : ONote} {Γ : Finset (ArithmeticFormula ℕ)}

/--
Quantifier-free closed-term value-congruent EM at explicit finite `ONote` height.

For a one-variable quantifier-free formula `ψ`, closed terms with the same standard value close any
sequent containing `ψ[s]` and `¬ψ[s']` at height `ofNat (2*q)`, provided that finite height fits the
current norm budget.
-/
lemma embedding_valueCongruentQFreeClosedTerm_probe (q : ℕ)
    (s s' : ArithmeticTerm ℕ) (ψ : ArithmeticSemiformula ℕ 1)
    (hψq : ψ.complexity ≤ q) (hqf : QFreeForm ψ) (hval : stdClosedVal s = stdClosedVal s')
    (hbudget : 2 * q < K + d) (hp : (ψ/[s]) ∈ Γ) (hn : (∼(ψ/[s'])) ∈ Γ) :
    Provable (ONote.ofNat (2 * q)) e K d c Γ := by
  induction q generalizing K d c e Γ s s' ψ hqf hval hp hn with
  | zero =>
      cases ψ using Semiformula.cases' with
      | hverum =>
          exact embedding_valueCongruentVerum_probe ![s] (by simpa using hp)
      | hfalsum =>
          exact embedding_valueCongruentFalsum_probe ![s'] (by simpa using hn)
      | hrel r v =>
          exact embedding_valueCongruentRelClosedTermAtom_probe r s s' v hval inferInstance
            (by rw [embedding_norm_ofNat]; omega) hp
            (by simpa [Semiformula.rew_rel, Semiformula.rew_nrel, Function.comp_def] using hn)
      | hnrel r v =>
          exact embedding_valueCongruentNrelClosedTermAtom_probe r s s' v hval inferInstance
            (by rw [embedding_norm_ofNat]; omega) hp
            (by simpa [Semiformula.rew_rel, Semiformula.rew_nrel, Function.comp_def] using hn)
      | hand a b =>
          simp only [Semiformula.complexity_and] at hψq
          omega
      | hor a b =>
          simp only [Semiformula.complexity_or] at hψq
          omega
      | hall a =>
          simp at hqf
      | hexs a =>
          simp at hqf
  | succ q ih =>
      cases ψ using Semiformula.cases' with
      | hverum =>
          exact embedding_valueCongruentVerum_probe ![s] (by simpa using hp)
      | hfalsum =>
          exact embedding_valueCongruentFalsum_probe ![s'] (by simpa using hn)
      | hrel r v =>
          exact embedding_valueCongruentRelClosedTermAtom_probe r s s' v hval inferInstance
            (by rw [embedding_norm_ofNat]; omega) hp
            (by simpa [Semiformula.rew_rel, Semiformula.rew_nrel, Function.comp_def] using hn)
      | hnrel r v =>
          exact embedding_valueCongruentNrelClosedTermAtom_probe r s s' v hval inferInstance
            (by rw [embedding_norm_ofNat]; omega) hp
            (by simpa [Semiformula.rew_rel, Semiformula.rew_nrel, Function.comp_def] using hn)
      | hand a b =>
          have haq : a.complexity ≤ q := by
            simp only [Semiformula.complexity_and] at hψq
            omega
          have hbq : b.complexity ≤ q := by
            simp only [Semiformula.complexity_and] at hψq
            omega
          obtain ⟨hqfa, hqfb⟩ : QFreeForm a ∧ QFreeForm b := by simpa using hqf
          have dA : Provable (ONote.ofNat (2 * q)) e K d c
              (insert (a/[s]) (insert (∼(a/[s'])) (insert (∼(b/[s'])) Γ))) :=
            ih (K := K) (d := d) (c := c) (e := e)
              (Γ := insert (a/[s]) (insert (∼(a/[s'])) (insert (∼(b/[s'])) Γ)))
              s s' a haq hqfa hval (by omega) (by simp) (by simp)
          have dB : Provable (ONote.ofNat (2 * q)) e K d c
              (insert (b/[s]) (insert (∼(a/[s'])) (insert (∼(b/[s'])) Γ))) :=
            ih (K := K) (d := d) (c := c) (e := e)
              (Γ := insert (b/[s]) (insert (∼(a/[s'])) (insert (∼(b/[s'])) Γ)))
              s s' b hbq hqfb hval (by omega) (by simp) (by simp)
          exact embedding_valueCongruentAndClosedTermFromChildren_probe
            (βA := ONote.ofNat (2 * q)) (βB := ONote.ofNat (2 * q))
            (αAnd := ONote.ofNat (2 * q + 1)) s s' a b
            (embedding_ofNat_lt_of_lt (by omega)) (embedding_ofNat_lt_of_lt (by omega))
            (embedding_ofNat_lt_of_lt (by omega))
            inferInstance inferInstance inferInstance inferInstance
            (by rw [embedding_norm_ofNat]; omega)
            (by rw [embedding_norm_ofNat]; omega)
            (by rw [embedding_norm_ofNat]; omega)
            hp hn dA dB
      | hor a b =>
          have haq : a.complexity ≤ q := by
            simp only [Semiformula.complexity_or] at hψq
            omega
          have hbq : b.complexity ≤ q := by
            simp only [Semiformula.complexity_or] at hψq
            omega
          obtain ⟨hqfa, hqfb⟩ : QFreeForm a ∧ QFreeForm b := by simpa using hqf
          have dA : Provable (ONote.ofNat (2 * q)) e K d c
              (insert (∼(a/[s'])) (insert (a/[s]) (insert (b/[s]) Γ))) :=
            ih (K := K) (d := d) (c := c) (e := e)
              (Γ := insert (∼(a/[s'])) (insert (a/[s]) (insert (b/[s]) Γ)))
              s s' a haq hqfa hval (by omega) (by simp) (by simp)
          have dB : Provable (ONote.ofNat (2 * q)) e K d c
              (insert (∼(b/[s'])) (insert (a/[s]) (insert (b/[s]) Γ))) :=
            ih (K := K) (d := d) (c := c) (e := e)
              (Γ := insert (∼(b/[s'])) (insert (a/[s]) (insert (b/[s]) Γ)))
              s s' b hbq hqfb hval (by omega) (by simp) (by simp)
          exact embedding_valueCongruentOrClosedTermFromChildren_probe
            (βA := ONote.ofNat (2 * q)) (βB := ONote.ofNat (2 * q))
            (αAnd := ONote.ofNat (2 * q + 1)) s s' a b
            (embedding_ofNat_lt_of_lt (by omega)) (embedding_ofNat_lt_of_lt (by omega))
            (embedding_ofNat_lt_of_lt (by omega))
            inferInstance inferInstance inferInstance inferInstance
            (by rw [embedding_norm_ofNat]; omega)
            (by rw [embedding_norm_ofNat]; omega)
            (by rw [embedding_norm_ofNat]; omega)
            hp hn dA dB
      | hall a =>
          simp at hqf
      | hexs a =>
          simp at hqf

/--
Bounded value-congruent EM for arbitrary formulas at explicit finite `ONote` height.

This is the arity-general recursive shell needed by the bounded embedding route.  The quantifier
cases are the decisive check: each `allω` premise runs at `max K m`, so the corresponding `exI`
witness `m` is paid by `inductionLeaf_runningIndex_witnessBound`.
-/
lemma embedding_valueCongruentEM_probe (q : ℕ) {n : ℕ} (w w' : Fin n → ArithmeticTerm ℕ)
    (ψ : ArithmeticSemiformula ℕ n) (hψq : ψ.complexity ≤ q)
    (hval : ∀ i, stdClosedVal (w i) = stdClosedVal (w' i)) (hbudget : 2 * q < K + d)
    (hp : (Rew.subst w ▹ ψ) ∈ Γ) (hn : (∼(Rew.subst w' ▹ ψ)) ∈ Γ) :
    Provable (ONote.ofNat (2 * q)) e K d c Γ := by
  induction q generalizing K d c e Γ n w w' ψ hval hp hn with
  | zero =>
      cases ψ using Semiformula.cases' with
      | hverum =>
          exact embedding_valueCongruentVerum_probe w (by simpa using hp)
      | hfalsum =>
          exact embedding_valueCongruentFalsum_probe w' (by simpa using hn)
      | hrel r v =>
          exact embedding_valueCongruentRelSubstAtom_probe r w w' v hval inferInstance
            (by rw [embedding_norm_ofNat]; omega)
            (by simpa [Semiformula.rew_rel, Function.comp_def] using hp)
            (by simpa [Semiformula.rew_rel, Semiformula.rew_nrel, Function.comp_def] using hn)
      | hnrel r v =>
          exact embedding_valueCongruentNrelSubstAtom_probe r w w' v hval inferInstance
            (by rw [embedding_norm_ofNat]; omega)
            (by simpa [Semiformula.rew_nrel, Function.comp_def] using hp)
            (by simpa [Semiformula.rew_rel, Semiformula.rew_nrel, Function.comp_def] using hn)
      | hand a b =>
          simp only [Semiformula.complexity_and] at hψq
          omega
      | hor a b =>
          simp only [Semiformula.complexity_or] at hψq
          omega
      | hall a =>
          simp only [Semiformula.complexity_all] at hψq
          omega
      | hexs a =>
          simp only [Semiformula.complexity_exs] at hψq
          omega
  | succ q ih =>
      cases ψ using Semiformula.cases' with
      | hverum =>
          exact embedding_valueCongruentVerum_probe w (by simpa using hp)
      | hfalsum =>
          exact embedding_valueCongruentFalsum_probe w' (by simpa using hn)
      | hrel r v =>
          exact embedding_valueCongruentRelSubstAtom_probe r w w' v hval inferInstance
            (by rw [embedding_norm_ofNat]; omega)
            (by simpa [Semiformula.rew_rel, Function.comp_def] using hp)
            (by simpa [Semiformula.rew_rel, Semiformula.rew_nrel, Function.comp_def] using hn)
      | hnrel r v =>
          exact embedding_valueCongruentNrelSubstAtom_probe r w w' v hval inferInstance
            (by rw [embedding_norm_ofNat]; omega)
            (by simpa [Semiformula.rew_nrel, Function.comp_def] using hp)
            (by simpa [Semiformula.rew_rel, Semiformula.rew_nrel, Function.comp_def] using hn)
      | hand a b =>
          have haq : a.complexity ≤ q := by
            simp only [Semiformula.complexity_and] at hψq
            omega
          have hbq : b.complexity ≤ q := by
            simp only [Semiformula.complexity_and] at hψq
            omega
          have dA : Provable (ONote.ofNat (2 * q)) e K d c
              (insert (Rew.subst w ▹ a)
                (insert (∼(Rew.subst w' ▹ a)) (insert (∼(Rew.subst w' ▹ b)) Γ))) :=
            ih (K := K) (d := d) (c := c) (e := e) (n := n) w w' a haq hval
              (by omega) (by simp) (by simp)
          have dB : Provable (ONote.ofNat (2 * q)) e K d c
              (insert (Rew.subst w ▹ b)
                (insert (∼(Rew.subst w' ▹ a)) (insert (∼(Rew.subst w' ▹ b)) Γ))) :=
            ih (K := K) (d := d) (c := c) (e := e) (n := n) w w' b hbq hval
              (by omega) (by simp) (by simp)
          exact embedding_valueCongruentAndFromChildren_probe
            (βA := ONote.ofNat (2 * q)) (βB := ONote.ofNat (2 * q))
            (αAnd := ONote.ofNat (2 * q + 1)) w w' a b
            (embedding_ofNat_lt_of_lt (by omega)) (embedding_ofNat_lt_of_lt (by omega))
            (embedding_ofNat_lt_of_lt (by omega))
            inferInstance inferInstance inferInstance inferInstance
            (by rw [embedding_norm_ofNat]; omega)
            (by rw [embedding_norm_ofNat]; omega)
            (by rw [embedding_norm_ofNat]; omega)
            hp hn dA dB
      | hor a b =>
          have haq : a.complexity ≤ q := by
            simp only [Semiformula.complexity_or] at hψq
            omega
          have hbq : b.complexity ≤ q := by
            simp only [Semiformula.complexity_or] at hψq
            omega
          have dA : Provable (ONote.ofNat (2 * q)) e K d c
              (insert (∼(Rew.subst w' ▹ a))
                (insert (Rew.subst w ▹ a) (insert (Rew.subst w ▹ b) Γ))) :=
            ih (K := K) (d := d) (c := c) (e := e) (n := n) w w' a haq hval
              (by omega) (by simp) (by simp)
          have dB : Provable (ONote.ofNat (2 * q)) e K d c
              (insert (∼(Rew.subst w' ▹ b))
                (insert (Rew.subst w ▹ a) (insert (Rew.subst w ▹ b) Γ))) :=
            ih (K := K) (d := d) (c := c) (e := e) (n := n) w w' b hbq hval
              (by omega) (by simp) (by simp)
          exact embedding_valueCongruentOrFromChildren_probe
            (βA := ONote.ofNat (2 * q)) (βB := ONote.ofNat (2 * q))
            (αAnd := ONote.ofNat (2 * q + 1)) w w' a b
            (embedding_ofNat_lt_of_lt (by omega)) (embedding_ofNat_lt_of_lt (by omega))
            (embedding_ofNat_lt_of_lt (by omega))
            inferInstance inferInstance inferInstance inferInstance
            (by rw [embedding_norm_ofNat]; omega)
            (by rw [embedding_norm_ofNat]; omega)
            (by rw [embedding_norm_ofNat]; omega)
            hp hn dA dB
      | hall a =>
          have haq : a.complexity ≤ q := by
            simp only [Semiformula.complexity_all] at hψq
            omega
          have hp' : (∀⁰ ((Rew.subst w).q ▹ a)) ∈ Γ := by simpa using hp
          have hn' : (∃⁰ ((Rew.subst w').q ▹ ∼a)) ∈ Γ := by simpa using hn
          have fam : ∀ m, Provable (ONote.ofNat (2 * q + 1)) e (max K m) d c
              (insert (((Rew.subst w).q ▹ a)/[nm m]) Γ) := by
            intro m
            have hvalm : ∀ i, stdClosedVal ((nm m :> w) i) = stdClosedVal ((nm m :> w') i) :=
              embedding_valm_cons_nm_congr w w' m hval
            have hx : Provable (ONote.ofNat (2 * q)) e (max K m) d c
                (insert (((Rew.subst w).q ▹ a)/[nm m])
                  (insert (∼(((Rew.subst w').q ▹ a)/[nm m])) Γ)) :=
              ih (K := max K m) (d := d) (c := c) (e := e) (n := n + 1)
                (nm m :> w) (nm m :> w') a haq hvalm (by omega)
                (by rw [← embedding_subst_q_cons_app]; simp)
                (by rw [← embedding_subst_q_cons_app]; simp)
            have hx' : Provable (ONote.ofNat (2 * q)) e (max K m) d c
                (insert ((((Rew.subst w').q ▹ ∼a)/[nm m])
                  ) (insert (((Rew.subst w).q ▹ a)/[nm m]) Γ)) := by
              have heq : (((Rew.subst w').q ▹ ∼a)/[nm m])
                  = ∼(((Rew.subst w').q ▹ a)/[nm m]) := by simp
              rw [heq, Finset.insert_comm]
              exact hx
            have hexI : Provable (ONote.ofNat (2 * q + 1)) e (max K m) d c
                (insert (∃⁰ ((Rew.subst w').q ▹ ∼a))
                  (insert (((Rew.subst w).q ▹ a)/[nm m]) Γ)) :=
              Provable.exI ((Rew.subst w').q ▹ ∼a) m
                (embedding_ofNat_lt_of_lt (by omega)) inferInstance inferInstance
                (by rw [embedding_norm_ofNat]; omega)
                (inductionLeaf_runningIndex_witnessBound e K d m) hx'
            rw [Finset.insert_eq_self.mpr (Finset.mem_insert_of_mem hn')] at hexI
            exact hexI
          have hallω : Provable (ONote.ofNat (2 * (q + 1))) e K d c
              (insert (∀⁰ ((Rew.subst w).q ▹ a)) Γ) :=
            Provable.allω ((Rew.subst w).q ▹ a) (fun _ => ONote.ofNat (2 * q + 1))
              (fun _ => embedding_ofNat_lt_of_lt (by omega))
              (fun _ => inferInstance) inferInstance
              (fun m => by rw [embedding_norm_ofNat]; omega) fam
          rwa [Finset.insert_eq_self.mpr hp'] at hallω
      | hexs a =>
          have haq : a.complexity ≤ q := by
            simp only [Semiformula.complexity_exs] at hψq
            omega
          have hp' : (∃⁰ ((Rew.subst w).q ▹ a)) ∈ Γ := by simpa using hp
          have hn' : (∀⁰ ((Rew.subst w').q ▹ ∼a)) ∈ Γ := by simpa using hn
          have fam : ∀ m, Provable (ONote.ofNat (2 * q + 1)) e (max K m) d c
              (insert (((Rew.subst w').q ▹ ∼a)/[nm m]) Γ) := by
            intro m
            have hvalm : ∀ i, stdClosedVal ((nm m :> w) i) = stdClosedVal ((nm m :> w') i) :=
              embedding_valm_cons_nm_congr w w' m hval
            have hx : Provable (ONote.ofNat (2 * q)) e (max K m) d c
                (insert (((Rew.subst w).q ▹ a)/[nm m])
                  (insert (∼(((Rew.subst w').q ▹ a)/[nm m])) Γ)) :=
              ih (K := max K m) (d := d) (c := c) (e := e) (n := n + 1)
                (nm m :> w) (nm m :> w') a haq hvalm (by omega)
                (by rw [← embedding_subst_q_cons_app]; simp)
                (by rw [← embedding_subst_q_cons_app]; simp)
            have hx' : Provable (ONote.ofNat (2 * q)) e (max K m) d c
                (insert (((Rew.subst w).q ▹ a)/[nm m])
                  (insert (((Rew.subst w').q ▹ ∼a)/[nm m]) Γ)) := by
              have heq : (((Rew.subst w').q ▹ ∼a)/[nm m])
                  = ∼(((Rew.subst w').q ▹ a)/[nm m]) := by simp
              rw [heq]
              exact hx
            have hexI : Provable (ONote.ofNat (2 * q + 1)) e (max K m) d c
                (insert (∃⁰ ((Rew.subst w).q ▹ a))
                  (insert (((Rew.subst w').q ▹ ∼a)/[nm m]) Γ)) :=
              Provable.exI ((Rew.subst w).q ▹ a) m
                (embedding_ofNat_lt_of_lt (by omega)) inferInstance inferInstance
                (by rw [embedding_norm_ofNat]; omega)
                (inductionLeaf_runningIndex_witnessBound e K d m) hx'
            rw [Finset.insert_eq_self.mpr (Finset.mem_insert_of_mem hp')] at hexI
            exact hexI
          have hallω : Provable (ONote.ofNat (2 * (q + 1))) e K d c
              (insert (∀⁰ ((Rew.subst w').q ▹ ∼a)) Γ) :=
            Provable.allω ((Rew.subst w').q ▹ ∼a) (fun _ => ONote.ofNat (2 * q + 1))
              (fun _ => embedding_ofNat_lt_of_lt (by omega))
              (fun _ => inferInstance) inferInstance
              (fun m => by rw [embedding_norm_ofNat]; omega) fam
          rwa [Finset.insert_eq_self.mpr hn'] at hallω

end ValueCongruentEM

end GoodsteinPA.OperatorZinfty
