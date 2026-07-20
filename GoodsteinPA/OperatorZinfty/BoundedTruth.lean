module

public import GoodsteinPA.OperatorZinfty.Embedding

@[expose] public section

namespace GoodsteinPA.OperatorZinfty

open LO LO.FirstOrder ONote

/-! #### Bounded true axiom leaves -/

/--
Truth with the exact witness bounds needed by the `Zekd` rules after a closed substitution.

Unlike plain standard-model truth, the existential case records a witness already bounded by the
current control budget `hardy e (K + d)`, and the universal case switches to the running index
`max K m`.  This is the reusable target for the finite `𝗣𝗔⁻`/equality axiom-leaf discharge.
-/
noncomputable def ZekdBoundedTruth (e : ONote) (K d : ℕ) :
    {n : ℕ} → (Fin n → ArithmeticTerm ℕ) → ArithmeticSemiformula ℕ n → Prop
  | _, _, .verum => True
  | _, _, .falsum => False
  | _, w, .rel r v => atomTrue (Semiformula.rel r (fun i => Rew.subst w (v i)))
  | _, w, .nrel r v => atomTrue (Semiformula.nrel r (fun i => Rew.subst w (v i)))
  | _, w, .and a b => ZekdBoundedTruth e K d w a ∧ ZekdBoundedTruth e K d w b
  | _, w, .or a b => ZekdBoundedTruth e K d w a ∨ ZekdBoundedTruth e K d w b
  | _, w, .all a => ∀ m, ZekdBoundedTruth e (max K m) d (nm m :> w) a
  | _, w, .exs a => ∃ m, m ≤ hardy e (K + d) ∧ ZekdBoundedTruth e K d (nm m :> w) a

/--
Bounded truth gives an exact-index `Zekd` derivation.

The proof mirrors the old `provable_true` recursion, but the universal and existential cases are
indexed by `ZekdBoundedTruth`: universals run at `max K m`, and existential witnesses are already
within the control-ordinal Hardy budget.
-/
theorem zekdOfBoundedTruth_probe :
    ∀ (q : ℕ) {K d c : ℕ} {e : ONote} {Γ : Finset (ArithmeticFormula ℕ)} {n : ℕ}
      (w : Fin n → ArithmeticTerm ℕ) (ψ : ArithmeticSemiformula ℕ n),
      ψ.complexity ≤ q →
      ZekdBoundedTruth e K d w ψ →
      2 * q < K + d →
      (Rew.subst w ▹ ψ) ∈ Γ →
      Zekd (ONote.ofNat (2 * q)) e K d c Γ := by
  intro q
  induction q with
  | zero =>
      intro K d c e Γ n w ψ hψq hBT hbudget hmem
      cases ψ using Semiformula.cases' with
      | hverum =>
          exact embedding_valueCongruentVerum_probe w (by simpa using hmem)
      | hfalsum =>
          cases hBT
      | hrel r v =>
          exact Zekd.trueRel r (fun i => Rew.subst w (v i)) hBT
            (by rw [embedding_norm_ofNat]; omega) inferInstance
            (by simpa [Semiformula.rew_rel, Function.comp_def] using hmem)
      | hnrel r v =>
          exact Zekd.trueNrel r (fun i => Rew.subst w (v i)) hBT
            (by rw [embedding_norm_ofNat]; omega) inferInstance
            (by simpa [Semiformula.rew_nrel, Function.comp_def] using hmem)
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
      intro K d c e Γ n w ψ hψq hBT hbudget hmem
      cases ψ using Semiformula.cases' with
      | hverum =>
          exact embedding_valueCongruentVerum_probe w (by simpa using hmem)
      | hfalsum =>
          cases hBT
      | hrel r v =>
          exact Zekd.trueRel r (fun i => Rew.subst w (v i)) hBT
            (by rw [embedding_norm_ofNat]; omega) inferInstance
            (by simpa [Semiformula.rew_rel, Function.comp_def] using hmem)
      | hnrel r v =>
          exact Zekd.trueNrel r (fun i => Rew.subst w (v i)) hBT
            (by rw [embedding_norm_ofNat]; omega) inferInstance
            (by simpa [Semiformula.rew_nrel, Function.comp_def] using hmem)
      | hand a b =>
          have haq : a.complexity ≤ q := by
            simp only [Semiformula.complexity_and] at hψq
            omega
          have hbq : b.complexity ≤ q := by
            simp only [Semiformula.complexity_and] at hψq
            omega
          obtain ⟨hBTa, hBTb⟩ := hBT
          have dA : Zekd (ONote.ofNat (2 * q)) e K d c (insert (Rew.subst w ▹ a) Γ) :=
            ih (K := K) (d := d) (c := c) (e := e) (Γ := insert (Rew.subst w ▹ a) Γ)
              w a haq hBTa (by omega) (by simp)
          have dB : Zekd (ONote.ofNat (2 * q)) e K d c (insert (Rew.subst w ▹ b) Γ) :=
            ih (K := K) (d := d) (c := c) (e := e) (Γ := insert (Rew.subst w ▹ b) Γ)
              w b hbq hBTb (by omega) (by simp)
          have hp' : ((Rew.subst w ▹ a) ⋏ (Rew.subst w ▹ b)) ∈ Γ := by
            simpa using hmem
          have hand : Zekd (ONote.ofNat (2 * (q + 1))) e K d c
              (insert ((Rew.subst w ▹ a) ⋏ (Rew.subst w ▹ b)) Γ) :=
            Zekd.andI (Rew.subst w ▹ a) (Rew.subst w ▹ b)
              (embedding_ofNat_lt_of_lt (by omega)) (embedding_ofNat_lt_of_lt (by omega))
              inferInstance inferInstance inferInstance
              (by rw [embedding_norm_ofNat]; omega) (by rw [embedding_norm_ofNat]; omega)
              dA dB
          rwa [Finset.insert_eq_self.mpr hp'] at hand
      | hor a b =>
          have haq : a.complexity ≤ q := by
            simp only [Semiformula.complexity_or] at hψq
            omega
          have hbq : b.complexity ≤ q := by
            simp only [Semiformula.complexity_or] at hψq
            omega
          have hp' : ((Rew.subst w ▹ a) ⋎ (Rew.subst w ▹ b)) ∈ Γ := by
            simpa using hmem
          rcases hBT with hBTa | hBTb
          · have dA : Zekd (ONote.ofNat (2 * q)) e K d c
                (insert (Rew.subst w ▹ a) (insert (Rew.subst w ▹ b) Γ)) :=
              ih (K := K) (d := d) (c := c) (e := e)
                (Γ := insert (Rew.subst w ▹ a) (insert (Rew.subst w ▹ b) Γ))
                w a haq hBTa (by omega) (by simp)
            have hor : Zekd (ONote.ofNat (2 * (q + 1))) e K d c
                (insert ((Rew.subst w ▹ a) ⋎ (Rew.subst w ▹ b)) Γ) :=
              Zekd.orI (Rew.subst w ▹ a) (Rew.subst w ▹ b)
                (embedding_ofNat_lt_of_lt (by omega)) inferInstance inferInstance
                (by rw [embedding_norm_ofNat]; omega) dA
            rwa [Finset.insert_eq_self.mpr hp'] at hor
          · have dB0 : Zekd (ONote.ofNat (2 * q)) e K d c
                (insert (Rew.subst w ▹ b) (insert (Rew.subst w ▹ a) Γ)) :=
              ih (K := K) (d := d) (c := c) (e := e)
                (Γ := insert (Rew.subst w ▹ b) (insert (Rew.subst w ▹ a) Γ))
                w b hbq hBTb (by omega) (by simp)
            have dB : Zekd (ONote.ofNat (2 * q)) e K d c
                (insert (Rew.subst w ▹ a) (insert (Rew.subst w ▹ b) Γ)) :=
              Zekd.wk (by intro x hx; simp only [Finset.mem_insert] at hx ⊢; tauto) dB0
            have hor : Zekd (ONote.ofNat (2 * (q + 1))) e K d c
                (insert ((Rew.subst w ▹ a) ⋎ (Rew.subst w ▹ b)) Γ) :=
              Zekd.orI (Rew.subst w ▹ a) (Rew.subst w ▹ b)
                (embedding_ofNat_lt_of_lt (by omega)) inferInstance inferInstance
                (by rw [embedding_norm_ofNat]; omega) dB
            rwa [Finset.insert_eq_self.mpr hp'] at hor
      | hall a =>
          have haq : a.complexity ≤ q := by
            simp only [Semiformula.complexity_all] at hψq
            omega
          have hp' : (∀⁰ ((Rew.subst w).q ▹ a)) ∈ Γ := by
            simpa using hmem
          have fam : ∀ m, Zekd (ONote.ofNat (2 * q)) e (max K m) d c
              (insert (((Rew.subst w).q ▹ a)/[nm m]) Γ) := by
            intro m
            exact ih (K := max K m) (d := d) (c := c) (e := e)
              (Γ := insert (((Rew.subst w).q ▹ a)/[nm m]) Γ)
              (nm m :> w) a haq (hBT m) (by omega)
              (by rw [← embedding_subst_q_cons_app]; simp)
          have hallω : Zekd (ONote.ofNat (2 * (q + 1))) e K d c
              (insert (∀⁰ ((Rew.subst w).q ▹ a)) Γ) :=
            Zekd.allω ((Rew.subst w).q ▹ a) (fun _ => ONote.ofNat (2 * q))
              (fun _ => embedding_ofNat_lt_of_lt (by omega))
              (fun _ => inferInstance) inferInstance
              (fun m => by rw [embedding_norm_ofNat]; omega) fam
          rwa [Finset.insert_eq_self.mpr hp'] at hallω
      | hexs a =>
          have haq : a.complexity ≤ q := by
            simp only [Semiformula.complexity_exs] at hψq
            omega
          have hp' : (∃⁰ ((Rew.subst w).q ▹ a)) ∈ Γ := by
            simpa using hmem
          rcases hBT with ⟨m, hbound, hBTm⟩
          have dA : Zekd (ONote.ofNat (2 * q)) e K d c
              (insert (((Rew.subst w).q ▹ a)/[nm m]) Γ) :=
            ih (K := K) (d := d) (c := c) (e := e)
              (Γ := insert (((Rew.subst w).q ▹ a)/[nm m]) Γ)
              (nm m :> w) a haq hBTm (by omega)
              (by rw [← embedding_subst_q_cons_app]; simp)
          have hexI : Zekd (ONote.ofNat (2 * (q + 1))) e K d c
              (insert (∃⁰ ((Rew.subst w).q ▹ a)) Γ) :=
            Zekd.exI ((Rew.subst w).q ▹ a) m
              (embedding_ofNat_lt_of_lt (by omega)) inferInstance inferInstance
              (by rw [embedding_norm_ofNat]; omega) hbound dA
          rwa [Finset.insert_eq_self.mpr hp'] at hexI

/--
Closed-term existential introduction using the checked bounded value-congruence EM engine.

This is the direct `Zekd` adapter for the Foundation `exs` shape after an open witness term has been
closed by an assignment.  The only semantic side condition still exposed is the real witness bound
`stdClosedVal s ≤ hardy e (K+d)`.
-/
theorem embedding_closedTermExI_probe
    {βSrc αCut αOut e : ONote} {K d c q : ℕ} {Γ : Finset (ArithmeticFormula ℕ)}
    {ψ : ArithmeticSemiformula ℕ 1} (s : ArithmeticTerm ℕ)
    (hψq : ψ.complexity ≤ q) (hψc : (ψ/[s]).complexity < c)
    (hSrcLt : βSrc < αCut) (hCongLt : ONote.ofNat (2 * q) < αCut)
    (hCutLt : αCut < αOut)
    (hSrcNF : βSrc.NF) (hCutNF : αCut.NF) (hOutNF : αOut.NF)
    (hτSrc : norm βSrc < K + d) (hτCong : norm (ONote.ofNat (2 * q)) < K + d)
    (hτCut : norm αCut < K + d)
    (hbudget : 2 * q < K + d)
    (hbound : stdClosedVal s ≤ hardy e (K + d))
    (dSrc : Zekd βSrc e K d c (insert (ψ/[s]) Γ)) :
    Zekd αOut e K d c (insert (∃⁰ ψ) Γ) := by
  have hval : ∀ i, stdClosedVal ((![nm (stdClosedVal s)] : Fin 1 → ArithmeticTerm ℕ) i)
      = stdClosedVal ((![s] : Fin 1 → ArithmeticTerm ℕ) i) := by
    intro i
    cases i using Fin.cases with
    | zero => simp
    | succ j => exact Fin.elim0 j
  have dCong : Zekd (ONote.ofNat (2 * q)) e K d c
      (insert (∼(ψ/[s])) (insert (ψ/[nm (stdClosedVal s)]) Γ)) := by
    refine embedding_valueCongruentEM_probe q
      (![nm (stdClosedVal s)] : Fin 1 → ArithmeticTerm ℕ)
      (![s] : Fin 1 → ArithmeticTerm ℕ) ψ hψq hval hbudget ?_ ?_
    · simp
    · simp
  exact embedding_closedTermExI_of_valueCongruentEM_probe s hψc hSrcLt hCongLt hCutLt
    hSrcNF inferInstance hCutNF hOutNF hτSrc hτCong hτCut hbound dSrc dCong

/-- A finite numeric budget bound on a closed witness term is enough for the `Zekd.exI`
witness side condition, because every Hardy level is expansive. -/
theorem closedTerm_witnessBound_of_budget
    (e : ONote) {K d : ℕ} {s : ArithmeticTerm ℕ}
    (hterm : stdClosedVal s ≤ K + d) :
    stdClosedVal s ≤ hardy e (K + d) :=
  le_trans hterm (le_hardy e (K + d))

/--
Closed-term existential introduction with the witness bound paid by raising the `K` index.

This is the local `exs` budget adapter needed by the bounded embedding route: if a source derivation
is available at index `K`, then it can be used at `max K (stdClosedVal s)`, where the closed witness
term is automatically within the Hardy witness budget.  No extra logical premise is introduced.
-/
theorem embedding_closedTermExI_raiseK_probe
    {βSrc αCut αOut e : ONote} {K d c q : ℕ} {Γ : Finset (ArithmeticFormula ℕ)}
    {ψ : ArithmeticSemiformula ℕ 1} (s : ArithmeticTerm ℕ)
    (hψq : ψ.complexity ≤ q) (hψc : (ψ/[s]).complexity < c)
    (hSrcLt : βSrc < αCut) (hCongLt : ONote.ofNat (2 * q) < αCut)
    (hCutLt : αCut < αOut)
    (hSrcNF : βSrc.NF) (hCutNF : αCut.NF) (hOutNF : αOut.NF)
    (hτSrc : norm βSrc < K + d) (hτCong : norm (ONote.ofNat (2 * q)) < K + d)
    (hτCut : norm αCut < K + d)
    (hbudget : 2 * q < K + d)
    (dSrc : Zekd βSrc e K d c (insert (ψ/[s]) Γ)) :
    Zekd αOut e (max K (stdClosedVal s)) d c (insert (∃⁰ ψ) Γ) := by
  refine embedding_closedTermExI_probe (K := max K (stdClosedVal s)) s hψq hψc
    hSrcLt hCongLt hCutLt hSrcNF hCutNF hOutNF ?_ ?_ ?_ ?_ ?_ ?_
  · exact lt_of_lt_of_le hτSrc (by omega)
  · exact lt_of_lt_of_le hτCong (by omega)
  · exact lt_of_lt_of_le hτCut (by omega)
  · exact lt_of_lt_of_le hbudget (by omega)
  · exact closedTerm_witnessBound_of_budget e (by omega)
  · exact dSrc.mono_k (le_max_left K (stdClosedVal s))

end GoodsteinPA.OperatorZinfty
