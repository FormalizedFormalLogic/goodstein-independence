module

public import GoodsteinPA.OperatorZinfty.SomeK

@[expose] public section

namespace GoodsteinPA.OperatorZinfty

open LO LO.FirstOrder ONote

variable {e : ONote} {k d c : ℕ} {Γ Δ : Finset (ArithmeticFormula ℕ)}

/--
Existential-budget version of closed-term `exI`.

Given any bounded source derivation at some witness index, choose a larger finite index that also
pays all local norm side conditions and the closed witness value.  This is the shape needed for a
global finite-budget embedding pass: each rule may enlarge `K`, and the final theorem only exports
the resulting finite budget.
-/
lemma embedding_closedTermExI_someK_probe
    {βSrc αCut αOut : ONote} {q : ℕ}
    {ψ : ArithmeticSemiformula ℕ 1} (s : ArithmeticTerm ℕ)
    (hψq : ψ.complexity ≤ q) (hψc : (ψ/[s]).complexity < c)
    (hSrcLt : βSrc < αCut) (hCongLt : ONote.ofNat (2 * q) < αCut)
    (hCutLt : αCut < αOut)
    (hSrcNF : βSrc.NF) (hCutNF : αCut.NF) (hOutNF : αOut.NF)
    (dSrc : ProvableSomeK βSrc e d c (insert (ψ/[s]) Γ)) :
    ProvableSomeK αOut e d c (insert (∃⁰ ψ) Γ) := by
  rcases dSrc with ⟨K0, d0⟩
  let K1 :=
    max K0
      (max (stdClosedVal s)
        (max (norm βSrc + 1)
          (max (norm (ONote.ofNat (2 * q)) + 1)
            (max (norm αCut + 1) (2 * q + 1)))))
  refine ⟨K1, embedding_closedTermExI_probe (K := K1) s hψq hψc
    hSrcLt hCongLt hCutLt hSrcNF hCutNF hOutNF ?_ ?_ ?_ ?_ ?_ ?_⟩
  · dsimp [K1]; omega
  · dsimp [K1]; omega
  · dsimp [K1]; omega
  · dsimp [K1]; omega
  · exact closedTerm_witnessBound_of_budget e (by dsimp [K1]; omega)
  · exact d0.mono_k (by dsimp [K1]; omega)

/--
One bounded cut-tower step for the PA-induction leaf.

This is the structural kernel behind `EmbeddingBound.metaInduction_cong_bdd`, ported to `Provable`:
given the finite excluded-middle premises for `ψ(n)` and `ψ(n+1)`, combine them into the bad-step
formula, introduce `∃ badStep` using the running witness bound, then cut against the current
`ψ(n)` derivation to obtain `ψ(n+1)`.

The EM/value-substitution premises are still external to this probe.  The point of the theorem is
that the witness-bounded `andI`/`exI`/`cut` wiring itself is tractable at index `max k n`.
-/
lemma inductionLeaf_cutTowerStep_probe
    {βIH βA βB βAnd βEx α : ONote} {n : ℕ}
    {ψ step : ArithmeticSemiformula ℕ 1}
    (hstep : (∼step)/[nm n] = (ψ/[nm n]) ⋏ ∼(ψ/[nm (n + 1)]))
    (hmemEx : (∃⁰ ∼step) ∈ Δ)
    (hψc : (ψ/[nm n]).complexity < c)
    (hIHlt : βIH < α) (hExlt : βEx < α)
    (hAlt : βA < βAnd) (hBlt : βB < βAnd) (hAndlt : βAnd < βEx)
    (hIHNF : βIH.NF) (hANF : βA.NF) (hBNF : βB.NF)
    (hAndNF : βAnd.NF) (hExNF : βEx.NF) (hαNF : α.NF)
    (hτIH : norm βIH < max k n + d) (hτA : norm βA < max k n + d)
    (hτB : norm βB < max k n + d) (hτAnd : norm βAnd < max k n + d)
    (hτEx : norm βEx < max k n + d)
    (dIH : Provable βIH e (max k n) d c (insert (ψ/[nm n]) Δ))
    (dA : Provable βA e (max k n) d c
      (insert (ψ/[nm n]) (insert (∼(ψ/[nm n])) (insert (ψ/[nm (n + 1)]) Δ))))
    (dB : Provable βB e (max k n) d c
      (insert (∼(ψ/[nm (n + 1)])) (insert (∼(ψ/[nm n])) (insert (ψ/[nm (n + 1)]) Δ)))) :
    Provable α e (max k n) d c (insert (ψ/[nm (n + 1)]) Δ) := by
  have hAnd : Provable βAnd e (max k n) d c
      (insert ((ψ/[nm n]) ⋏ ∼(ψ/[nm (n + 1)]))
        (insert (∼(ψ/[nm n])) (insert (ψ/[nm (n + 1)]) Δ))) :=
    Provable.andI (ψ/[nm n]) (∼(ψ/[nm (n + 1)]))
      hAlt hBlt hANF hBNF hAndNF hτA hτB dA dB
  have hBadStep : Provable βAnd e (max k n) d c
      (insert ((∼step)/[nm n])
        (insert (∼(ψ/[nm n])) (insert (ψ/[nm (n + 1)]) Δ))) := by
    rw [hstep]
    exact hAnd
  have hEx : Provable βEx e (max k n) d c
      (insert (∃⁰ ∼step) (insert (∼(ψ/[nm n])) (insert (ψ/[nm (n + 1)]) Δ))) :=
    Provable.exI (∼step) n hAndlt hAndNF hExNF hτAnd
      (inductionLeaf_runningIndex_witnessBound e k d n) hBadStep
  have hEx' : Provable βEx e (max k n) d c
      (insert (∼(ψ/[nm n])) (insert (ψ/[nm (n + 1)]) Δ)) := by
    rw [Finset.insert_eq_self.mpr
      (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hmemEx))] at hEx
    exact hEx
  have hIH' : Provable βIH e (max k n) d c
      (insert (ψ/[nm n]) (insert (ψ/[nm (n + 1)]) Δ)) :=
    Provable.wk (Finset.insert_subset_insert _ (Finset.subset_insert _ _)) dIH
  exact Provable.cut (ψ/[nm n]) hψc hIHlt hExlt hIHNF hExNF hαNF hτIH hτEx hIH' hEx'

/-- Value-substitution by a cut against a value-congruent excluded-middle premise.

This is the `Provable` analogue of the cut used by
`EmbeddingBound.subst_value_subst_bdd`; the actual proof of the congruent EM premise is still
outside this probe, but the cut interface and budgets are now checked. -/
lemma inductionLeaf_valueSubst_cut_probe
    {βSrc βCong α : ONote}
    {ψ : ArithmeticSemiformula ℕ 1} {s t : ArithmeticTerm ℕ}
    (hψc : (ψ/[s]).complexity < c)
    (hSrcLt : βSrc < α) (hCongLt : βCong < α)
    (hSrcNF : βSrc.NF) (hCongNF : βCong.NF) (hαNF : α.NF)
    (hτSrc : norm βSrc < k + d) (hτCong : norm βCong < k + d)
    (dSrc : Provable βSrc e k d c (insert (ψ/[s]) Γ))
    (dCong : Provable βCong e k d c (insert (∼(ψ/[s])) (insert (ψ/[t]) Γ))) :
    Provable α e k d c (insert (ψ/[t]) Γ) :=
  Provable.cut (ψ/[s]) hψc hSrcLt hCongLt hSrcNF hCongNF hαNF hτSrc hτCong
    (Provable.wk (Finset.insert_subset_insert _ (Finset.subset_insert _ _)) dSrc) dCong

/--
The same cut-tower step, but with the successor occurrence still written as an arbitrary closed
term `succT`.  After the bad-step cut yields `ψ/[succT]`, a value-substitution cut turns it into
the numeral instance `ψ/[nm (n+1)]`.

This mirrors the real `succInd` leaf more closely than `inductionLeaf_cutTowerStep_probe`.
-/
lemma inductionLeaf_cutTowerStepWithTerm_probe
    {βIH βA βB βAnd βEx βCong αStep α : ONote} {n : ℕ}
    {ψ step : ArithmeticSemiformula ℕ 1} (succT : ArithmeticTerm ℕ)
    (hstep : (∼step)/[nm n] = (ψ/[nm n]) ⋏ ∼(ψ/[succT]))
    (hmemEx : (∃⁰ ∼step) ∈ Δ)
    (hψc : (ψ/[nm n]).complexity < c) (hsuccc : (ψ/[succT]).complexity < c)
    (hIHlt : βIH < αStep) (hExlt : βEx < αStep)
    (hAlt : βA < βAnd) (hBlt : βB < βAnd) (hAndlt : βAnd < βEx)
    (hStepLt : αStep < α) (hCongLt : βCong < α)
    (hIHNF : βIH.NF) (hANF : βA.NF) (hBNF : βB.NF)
    (hAndNF : βAnd.NF) (hExNF : βEx.NF) (hStepNF : αStep.NF)
    (hCongNF : βCong.NF) (hαNF : α.NF)
    (hτIH : norm βIH < max k n + d) (hτA : norm βA < max k n + d)
    (hτB : norm βB < max k n + d) (hτAnd : norm βAnd < max k n + d)
    (hτEx : norm βEx < max k n + d) (hτStep : norm αStep < max k n + d)
    (hτCong : norm βCong < max k n + d)
    (dIH : Provable βIH e (max k n) d c (insert (ψ/[nm n]) Δ))
    (dA : Provable βA e (max k n) d c
      (insert (ψ/[nm n]) (insert (∼(ψ/[nm n])) (insert (ψ/[succT]) Δ))))
    (dB : Provable βB e (max k n) d c
      (insert (∼(ψ/[succT])) (insert (∼(ψ/[nm n])) (insert (ψ/[succT]) Δ))))
    (dCong : Provable βCong e (max k n) d c
      (insert (∼(ψ/[succT])) (insert (ψ/[nm (n + 1)]) Δ))) :
    Provable α e (max k n) d c (insert (ψ/[nm (n + 1)]) Δ) := by
  have hAnd : Provable βAnd e (max k n) d c
      (insert ((ψ/[nm n]) ⋏ ∼(ψ/[succT]))
        (insert (∼(ψ/[nm n])) (insert (ψ/[succT]) Δ))) :=
    Provable.andI (ψ/[nm n]) (∼(ψ/[succT]))
      hAlt hBlt hANF hBNF hAndNF hτA hτB dA dB
  have hBadStep : Provable βAnd e (max k n) d c
      (insert ((∼step)/[nm n])
        (insert (∼(ψ/[nm n])) (insert (ψ/[succT]) Δ))) := by
    rw [hstep]
    exact hAnd
  have hEx : Provable βEx e (max k n) d c
      (insert (∃⁰ ∼step) (insert (∼(ψ/[nm n])) (insert (ψ/[succT]) Δ))) :=
    Provable.exI (∼step) n hAndlt hAndNF hExNF hτAnd
      (inductionLeaf_runningIndex_witnessBound e k d n) hBadStep
  have hEx' : Provable βEx e (max k n) d c
      (insert (∼(ψ/[nm n])) (insert (ψ/[succT]) Δ)) := by
    rw [Finset.insert_eq_self.mpr
      (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hmemEx))] at hEx
    exact hEx
  have hIH' : Provable βIH e (max k n) d c
      (insert (ψ/[nm n]) (insert (ψ/[succT]) Δ)) :=
    Provable.wk (Finset.insert_subset_insert _ (Finset.subset_insert _ _)) dIH
  have hStep : Provable αStep e (max k n) d c (insert (ψ/[succT]) Δ) :=
    Provable.cut (ψ/[nm n]) hψc hIHlt hExlt hIHNF hExNF hStepNF hτIH hτEx hIH' hEx'
  exact inductionLeaf_valueSubst_cut_probe hsuccc hStepLt hCongLt hStepNF hCongNF hαNF
    hτStep hτCong hStep dCong

/--
Existential-budget surface for one successor-induction cut-tower step with a closed successor term.

The exact `Provable` probe above requires all four premises at the same running index `max k n`.
This wrapper instead runs the same `andI`/`exI`/`cut` wiring in the `ProvableSomeK` calculus, letting
the existential-budget rules absorb the independently chosen finite premise budgets.
-/
lemma inductionLeaf_cutTowerStepWithTerm_someK_probe
    {βIH βA βB βAnd βEx βCong αStep α : ONote} {n : ℕ}
    {ψ step : ArithmeticSemiformula ℕ 1} (succT : ArithmeticTerm ℕ)
    (hstep : (∼step)/[nm n] = (ψ/[nm n]) ⋏ ∼(ψ/[succT]))
    (hmemEx : (∃⁰ ∼step) ∈ Δ)
    (hψc : (ψ/[nm n]).complexity < c) (hsuccc : (ψ/[succT]).complexity < c)
    (hIHlt : βIH < αStep) (hExlt : βEx < αStep)
    (hAlt : βA < βAnd) (hBlt : βB < βAnd) (hAndlt : βAnd < βEx)
    (hStepLt : αStep < α) (hCongLt : βCong < α)
    (hIHNF : βIH.NF) (hANF : βA.NF) (hBNF : βB.NF)
    (hAndNF : βAnd.NF) (hExNF : βEx.NF) (hStepNF : αStep.NF)
    (hCongNF : βCong.NF) (hαNF : α.NF)
    (dIH : ProvableSomeK βIH e d c (insert (ψ/[nm n]) Δ))
    (dA : ProvableSomeK βA e d c
      (insert (ψ/[nm n]) (insert (∼(ψ/[nm n])) (insert (ψ/[succT]) Δ))))
    (dB : ProvableSomeK βB e d c
      (insert (∼(ψ/[succT])) (insert (∼(ψ/[nm n])) (insert (ψ/[succT]) Δ))))
    (dCong : ProvableSomeK βCong e d c
      (insert (∼(ψ/[succT])) (insert (ψ/[nm (n + 1)]) Δ))) :
    ProvableSomeK α e d c (insert (ψ/[nm (n + 1)]) Δ) := by
  have hAnd : ProvableSomeK βAnd e d c
      (insert ((ψ/[nm n]) ⋏ ∼(ψ/[succT]))
        (insert (∼(ψ/[nm n])) (insert (ψ/[succT]) Δ))) :=
    ProvableSomeK.andI (ψ/[nm n]) (∼(ψ/[succT]))
      hAlt hBlt hANF hBNF hAndNF dA dB
  have hBadStep : ProvableSomeK βAnd e d c
      (insert ((∼step)/[nm n])
        (insert (∼(ψ/[nm n])) (insert (ψ/[succT]) Δ))) := by
    rw [hstep]
    exact hAnd
  have hEx : ProvableSomeK βEx e d c
      (insert (∃⁰ ∼step) (insert (∼(ψ/[nm n])) (insert (ψ/[succT]) Δ))) :=
    ProvableSomeK.exI (∼step) n hAndlt hAndNF hExNF hBadStep
  have hEx' : ProvableSomeK βEx e d c
      (insert (∼(ψ/[nm n])) (insert (ψ/[succT]) Δ)) := by
    rw [Finset.insert_eq_self.mpr
      (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hmemEx))] at hEx
    exact hEx
  have hIH' : ProvableSomeK βIH e d c
      (insert (ψ/[nm n]) (insert (ψ/[succT]) Δ)) :=
    ProvableSomeK.wk (Finset.insert_subset_insert _ (Finset.subset_insert _ _)) dIH
  have hStep : ProvableSomeK αStep e d c (insert (ψ/[succT]) Δ) :=
    ProvableSomeK.cut (ψ/[nm n]) hψc hIHlt hExlt hIHNF hExNF hStepNF hIH' hEx'
  have hStep' : ProvableSomeK αStep e d c
      (insert (ψ/[succT]) (insert (ψ/[nm (n + 1)]) Δ)) :=
    ProvableSomeK.wk (Finset.insert_subset_insert _ (Finset.subset_insert _ _)) hStep
  exact ProvableSomeK.cut (ψ/[succT]) hsuccc hStepLt hCongLt hStepNF hCongNF hαNF
    hStep' dCong

/--
Package a running finite induction chain into the `allω` rule.

This is the outer shape of `EmbeddingBound.metaInduction_cong_bdd` in the witness-bounded
`Provable` calculus: the successor step is allowed to run at the old index `max k n`; monotonicity
then raises it to the next `allω` premise index `max k (n+1)`.
-/
lemma inductionLeaf_allOmegaFromStep_probe
    {αAll : ONote}
    {ψ : ArithmeticSemiformula ℕ 1} (β : ℕ → ONote)
    (hβlt : ∀ n, β n < αAll) (hβNF : ∀ n, (β n).NF)
    (hαAllNF : αAll.NF) (hβτ : ∀ n, norm (β n) < max k n + d)
    (hbase : Provable (β 0) e k d c (insert (ψ/[nm 0]) Δ))
    (hnext : ∀ n,
      Provable (β n) e (max k n) d c (insert (ψ/[nm n]) Δ) →
      Provable (β (n + 1)) e (max k n) d c (insert (ψ/[nm (n + 1)]) Δ)) :
    Provable αAll e k d c (insert (∀⁰ ψ) Δ) := by
  have chain : ∀ n, Provable (β n) e (max k n) d c (insert (ψ/[nm n]) Δ) := by
    intro n
    induction n with
    | zero =>
        simpa using hbase
    | succ n ih =>
        exact (hnext n ih).mono_k (by omega)
  exact Provable.allω ψ β hβlt hβNF hαAllNF hβτ chain

/-- Existential-budget surface for a uniform running-index induction chain.

This packages the `allω` outer layer used by the bounded PA-induction leaf: once the chain data
has a single base index `k`, the exported conclusion only remembers that some finite index exists. -/
lemma inductionLeaf_allOmegaFromStep_someK_probe
    {αAll : ONote}
    {ψ : ArithmeticSemiformula ℕ 1} (β : ℕ → ONote)
    (hpack : ∃ k : ℕ,
      (∀ n, β n < αAll) ∧
      (∀ n, (β n).NF) ∧
      αAll.NF ∧
      (∀ n, norm (β n) < max k n + d) ∧
      Provable (β 0) e k d c (insert (ψ/[nm 0]) Δ) ∧
      (∀ n,
        Provable (β n) e (max k n) d c (insert (ψ/[nm n]) Δ) →
        Provable (β (n + 1)) e (max k n) d c (insert (ψ/[nm (n + 1)]) Δ))) :
    ProvableSomeK αAll e d c (insert (∀⁰ ψ) Δ) := by
  rcases hpack with ⟨k, hβlt, hβNF, hαAllNF, hβτ, hbase, hnext⟩
  exact ⟨k, inductionLeaf_allOmegaFromStep_probe β hβlt hβNF hαAllNF hβτ hbase hnext⟩

/--
The `allω` packaging for the numeral-successor cut tower.

This is the value-congruence-free core of the bounded PA-induction leaf: the local step already concludes
`ψ(n+1)`, so the outer finite induction and `allω` rule do not need any extra congruent-value premise.
-/
lemma inductionLeaf_allOmegaCutTowerNumeral_probe
    {αAll : ONote}
    {ψ step : ArithmeticSemiformula ℕ 1}
    (β βA βB βAnd βEx : ℕ → ONote)
    (hβAllLt : ∀ n, β n < αAll)
    (hIHlt : ∀ n, β n < β (n + 1)) (hExlt : ∀ n, βEx n < β (n + 1))
    (hAlt : ∀ n, βA n < βAnd n) (hBlt : ∀ n, βB n < βAnd n)
    (hAndlt : ∀ n, βAnd n < βEx n)
    (hβNF : ∀ n, (β n).NF) (hANF : ∀ n, (βA n).NF) (hBNF : ∀ n, (βB n).NF)
    (hAndNF : ∀ n, (βAnd n).NF) (hExNF : ∀ n, (βEx n).NF)
    (hαAllNF : αAll.NF)
    (hβτ : ∀ n, norm (β n) < max k n + d)
    (hAτ : ∀ n, norm (βA n) < max k n + d)
    (hBτ : ∀ n, norm (βB n) < max k n + d)
    (hAndτ : ∀ n, norm (βAnd n) < max k n + d)
    (hExτ : ∀ n, norm (βEx n) < max k n + d)
    (hstep : ∀ n, (∼step)/[nm n] = (ψ/[nm n]) ⋏ ∼(ψ/[nm (n + 1)]))
    (hmemEx : (∃⁰ ∼step) ∈ Δ)
    (hψc : ∀ n, (ψ/[nm n]).complexity < c)
    (hbase : Provable (β 0) e k d c (insert (ψ/[nm 0]) Δ))
    (dA : ∀ n, Provable (βA n) e (max k n) d c
      (insert (ψ/[nm n]) (insert (∼(ψ/[nm n])) (insert (ψ/[nm (n + 1)]) Δ))))
    (dB : ∀ n, Provable (βB n) e (max k n) d c
      (insert (∼(ψ/[nm (n + 1)])) (insert (∼(ψ/[nm n])) (insert (ψ/[nm (n + 1)]) Δ)))) :
    Provable αAll e k d c (insert (∀⁰ ψ) Δ) :=
  inductionLeaf_allOmegaFromStep_probe β hβAllLt hβNF hαAllNF hβτ hbase
    (fun n dIH =>
      inductionLeaf_cutTowerStep_probe (hstep n) hmemEx (hψc n)
        (hIHlt n) (hExlt n) (hAlt n) (hBlt n) (hAndlt n)
        (hβNF n) (hANF n) (hBNF n) (hAndNF n) (hExNF n) (hβNF (n + 1))
        (hβτ n) (hAτ n) (hBτ n) (hAndτ n) (hExτ n)
        dIH (dA n) (dB n))

/--
The `allω` packaging specialized to the bounded PA-induction cut tower.

All finite EM/congruence premises are still explicit hypotheses.  The theorem checks the important
interface: the local `andI`/`exI`/`cut`/value-substitution step composes through ordinary finite
induction and then through `Provable.allω` without losing the running witness index.
-/
lemma inductionLeaf_allOmegaCutTowerWithTerm_probe
    {αAll : ONote}
    {ψ step : ArithmeticSemiformula ℕ 1}
    (β βA βB βAnd βEx βStep βCong : ℕ → ONote)
    (succT : ℕ → ArithmeticTerm ℕ)
    (hβAllLt : ∀ n, β n < αAll)
    (hIHlt : ∀ n, β n < βStep n) (hExlt : ∀ n, βEx n < βStep n)
    (hAlt : ∀ n, βA n < βAnd n) (hBlt : ∀ n, βB n < βAnd n)
    (hAndlt : ∀ n, βAnd n < βEx n)
    (hStepLt : ∀ n, βStep n < β (n + 1)) (hCongLt : ∀ n, βCong n < β (n + 1))
    (hβNF : ∀ n, (β n).NF) (hANF : ∀ n, (βA n).NF) (hBNF : ∀ n, (βB n).NF)
    (hAndNF : ∀ n, (βAnd n).NF) (hExNF : ∀ n, (βEx n).NF)
    (hStepNF : ∀ n, (βStep n).NF) (hCongNF : ∀ n, (βCong n).NF)
    (hαAllNF : αAll.NF)
    (hβτ : ∀ n, norm (β n) < max k n + d)
    (hAτ : ∀ n, norm (βA n) < max k n + d)
    (hBτ : ∀ n, norm (βB n) < max k n + d)
    (hAndτ : ∀ n, norm (βAnd n) < max k n + d)
    (hExτ : ∀ n, norm (βEx n) < max k n + d)
    (hStepτ : ∀ n, norm (βStep n) < max k n + d)
    (hCongτ : ∀ n, norm (βCong n) < max k n + d)
    (hstep : ∀ n, (∼step)/[nm n] = (ψ/[nm n]) ⋏ ∼(ψ/[succT n]))
    (hmemEx : (∃⁰ ∼step) ∈ Δ)
    (hψc : ∀ n, (ψ/[nm n]).complexity < c)
    (hsuccc : ∀ n, (ψ/[succT n]).complexity < c)
    (hbase : Provable (β 0) e k d c (insert (ψ/[nm 0]) Δ))
    (dA : ∀ n, Provable (βA n) e (max k n) d c
      (insert (ψ/[nm n]) (insert (∼(ψ/[nm n])) (insert (ψ/[succT n]) Δ))))
    (dB : ∀ n, Provable (βB n) e (max k n) d c
      (insert (∼(ψ/[succT n])) (insert (∼(ψ/[nm n])) (insert (ψ/[succT n]) Δ))))
    (dCong : ∀ n, Provable (βCong n) e (max k n) d c
      (insert (∼(ψ/[succT n])) (insert (ψ/[nm (n + 1)]) Δ))) :
    Provable αAll e k d c (insert (∀⁰ ψ) Δ) :=
  inductionLeaf_allOmegaFromStep_probe β hβAllLt hβNF hαAllNF hβτ hbase
    (fun n dIH =>
      inductionLeaf_cutTowerStepWithTerm_probe (succT n) (hstep n) hmemEx (hψc n) (hsuccc n)
        (hIHlt n) (hExlt n) (hAlt n) (hBlt n) (hAndlt n)
        (hStepLt n) (hCongLt n)
        (hβNF n) (hANF n) (hBNF n) (hAndNF n) (hExNF n) (hStepNF n)
        (hCongNF n) (hβNF (n + 1))
        (hβτ n) (hAτ n) (hBτ n) (hAndτ n) (hExτ n) (hStepτ n) (hCongτ n)
        dIH (dA n) (dB n) (dCong n))


end GoodsteinPA.OperatorZinfty
