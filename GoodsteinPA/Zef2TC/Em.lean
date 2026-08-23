module

public import GoodsteinPA.Zef2TC.Basic

@[expose] public section

namespace GoodsteinPA.E1EmbeddingGrind

open LO LO.FirstOrder LO.FirstOrder.ArithmeticTerm ONote Ordinal
open GoodsteinPA.OperatorZeh GoodsteinPA.OperatorZinfty

variable {e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {Γ : Finset (ArithmeticFormula ℕ)}

/-! ## Budgeted excluded middle -/

/-- A sequent containing `φ, ∼φ` is cut-free `Zef2TC`-derivable at the deterministic ordinal
rung `ofNat (2k+1)` (`k ≥ φ.complexity`), for any slot `f` monotone and inflationary with
`clog (2k+1) ≤ f 0`.  Mirrors `Provable.em_cong_gen` in `GoodsteinPA/Zinfty/Embedding.lean`.

- [EW12, Lemma 32] -/
theorem em_Zef2TC (k : ℕ) (φ : ArithmeticFormula ℕ) (hk : φ.complexity ≤ k)
    (hmono : Monotone f) (hinfl : ∀ m, m ≤ f m) (hgate : clog (2 * k + 1) ≤ f 0)
    (hp : φ ∈ Γ) (hn : ∼φ ∈ Γ) :
    Zef2TC (ONote.ofNat (2 * k + 1)) e H f 0 Γ := by
  induction k generalizing φ e H f Γ with
  | zero =>
    have hgate' : Nlog (ONote.ofNat 1) ≤ f 0 := le_trans (Nlog_ofNat_le 1) hgate
    cases φ using Semiformula.cases' with
    | hverum => exact Zef2TC.verumR hgate' hp
    | hfalsum => exact Zef2TC.verumR hgate' (by simpa using hn)
    | hrel r v => exact Zef2TC.axL hgate' r v hp (by simpa using hn)
    | hnrel r v => exact Zef2TC.axL hgate' r v (by simpa using hn) hp
    | hand φ ψ => simp at hk
    | hor φ ψ => simp at hk
    | hall φ => simp at hk
    | hexs φ => simp at hk
  | succ k ih =>
    -- rungs: IH at `ofNat (2k+1)`, connective/witness node at `ofNat (2k+2)`,
    -- root at `ofNat (2k+3) = ofNat (2·(k+1)+1)`
    rw [show 2 * (k + 1) + 1 = 2 * k + 3 by ring] at hgate ⊢
    have hNF : ∀ m : ℕ, (ONote.ofNat m).NF := fun m => ONote.nf_ofNat m
    have hlt12 : ONote.ofNat (2 * k + 1) < ONote.ofNat (2 * k + 2) := ofNat_lt_ofNat (by omega)
    have hlt23 : ONote.ofNat (2 * k + 2) < ONote.ofNat (2 * k + 3) := ofNat_lt_ofNat (by omega)
    have hlt13 : ONote.ofNat (2 * k + 1) < ONote.ofNat (2 * k + 3) := ofNat_lt_ofNat (by omega)
    have hroot : Nlog (ONote.ofNat (2 * k + 3)) ≤ f 0 := le_trans (Nlog_ofNat_le _) hgate
    have hg2 : Nlog (ONote.ofNat (2 * k + 2)) ≤ f 0 :=
      le_trans (Nlog_ofNat_le _) (le_trans (clog_mono (by omega)) hgate)
    have hg1 : clog (2 * k + 1) ≤ f 0 := le_trans (clog_mono (by omega)) hgate
    cases φ using Semiformula.cases' with
    | hverum => exact Zef2TC.verumR hroot hp
    | hfalsum => exact Zef2TC.verumR hroot (by simpa using hn)
    | hrel r v => exact Zef2TC.axL hroot r v hp (by simpa using hn)
    | hnrel r v => exact Zef2TC.axL hroot r v (by simpa using hn) hp
    | hand φ ψ =>
        have hφk : φ.complexity ≤ k := by simp only [Semiformula.complexity_and] at hk; omega
        have hψk : ψ.complexity ≤ k := by simp only [Semiformula.complexity_and] at hk; omega
        have h1 := ih φ hφk (e := e) (H := H) (f := f)
          (Γ := insert φ (insert (∼φ) (insert (∼ψ) Γ))) hmono hinfl hg1 (by simp) (by simp)
        have h2 := ih ψ hψk (e := e) (H := H) (f := f)
          (Γ := insert ψ (insert (∼φ) (insert (∼ψ) Γ))) hmono hinfl hg1 (by simp) (by simp)
        have hand := Zef2TC.andI (α := ONote.ofNat (2 * k + 2)) hg2 φ ψ hlt12 hlt12
          (hNF _) (hNF _) (hNF _) (Cl.ofNat _) (Cl.ofNat _) h1 h2
        rw [Finset.insert_eq_self.mpr
          (show (φ ⋏ ψ) ∈ insert (∼φ) (insert (∼ψ) Γ) by simp [hp])] at hand
        have hor := Zef2TC.orI (α := ONote.ofNat (2 * k + 3)) hroot (∼φ) (∼ψ) hlt23
          (hNF _) (hNF _) (Cl.ofNat _) hand
        rwa [Finset.insert_eq_self.mpr (show (∼φ ⋎ ∼ψ) ∈ Γ by simpa using hn)] at hor
    | hor φ ψ =>
        have hn' : (∼φ ⋏ ∼ψ) ∈ Γ := by simpa using hn
        have hφk : φ.complexity ≤ k := by simp only [Semiformula.complexity_or] at hk; omega
        have hψk : ψ.complexity ≤ k := by simp only [Semiformula.complexity_or] at hk; omega
        have h1 := ih φ hφk (e := e) (H := H) (f := f)
          (Γ := insert (∼φ) (insert φ (insert ψ Γ))) hmono hinfl hg1 (by simp) (by simp)
        have h2 := ih ψ hψk (e := e) (H := H) (f := f)
          (Γ := insert (∼ψ) (insert φ (insert ψ Γ))) hmono hinfl hg1 (by simp) (by simp)
        have hand := Zef2TC.andI (α := ONote.ofNat (2 * k + 2)) hg2 (∼φ) (∼ψ) hlt12 hlt12
          (hNF _) (hNF _) (hNF _) (Cl.ofNat _) (Cl.ofNat _) h1 h2
        rw [Finset.insert_eq_self.mpr
          (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hn'))] at hand
        have hor := Zef2TC.orI (α := ONote.ofNat (2 * k + 3)) hroot φ ψ hlt23
          (hNF _) (hNF _) (Cl.ofNat _) hand
        rwa [Finset.insert_eq_self.mpr (show (φ ⋎ ψ) ∈ Γ by simp [hp])] at hor
    | hall ψ =>
        have hψk : ψ.complexity ≤ k := by simp only [Semiformula.complexity_all] at hk; omega
        have hex : (∃⁰ ∼ψ) ∈ Γ := by simpa using hn
        have fam : ∀ n, Zef2TC (ONote.ofNat (2 * k + 2)) e (adjoin H n) (rel1 f n) 0
            (insert (ψ/[nm n]) Γ) := by
          intro n
          have hf0n : f 0 ≤ rel1 f n 0 := by
            simpa [rel1] using hmono (Nat.zero_le (max n 0))
          have hcomp : (ψ/[nm n]).complexity ≤ k := by
            simpa using hψk
          have h0 := ih (ψ/[nm n]) hcomp (e := e) (H := adjoin H n) (f := rel1 f n)
            (Γ := insert (∼(ψ/[nm n])) (insert (ψ/[nm n]) Γ))
            (rel1_monotone hmono n) (rel1_infl hinfl n)
            (le_trans hg1 hf0n) (by simp) (by simp)
          have hbound : n ≤ rel1 f n 0 := by
            simpa [rel1] using hinfl n
          have hexI := Zef2TC.exI (α := ONote.ofNat (2 * k + 2))
            (le_trans hg2 hf0n)
            (∼ψ) n hlt12 (hNF _) (hNF _) (Cl.ofNat _) hbound
            (by have heq : (∼ψ)/[nm n] = ∼(ψ/[nm n]) := by simp
                rw [heq]; exact h0)
          rwa [Finset.insert_eq_self.mpr (Finset.mem_insert_of_mem hex)] at hexI
        have hall := Zef2TC.allω (α := ONote.ofNat (2 * k + 3)) hroot ψ
          (fun _ => ONote.ofNat (2 * k + 2)) (fun _ => hlt23) (fun _ => hNF _) (hNF _)
          (fun _ => Cl.ofNat _) fam
        rwa [Finset.insert_eq_self.mpr hp] at hall
    | hexs ψ =>
        have hψk : ψ.complexity ≤ k := by simp only [Semiformula.complexity_exs] at hk; omega
        have hall' : (∀⁰ ∼ψ) ∈ Γ := by simpa using hn
        have fam : ∀ n, Zef2TC (ONote.ofNat (2 * k + 2)) e (adjoin H n) (rel1 f n) 0
            (insert ((∼ψ)/[nm n]) Γ) := by
          intro n
          have hf0n : f 0 ≤ rel1 f n 0 := by
            simpa [rel1] using hmono (Nat.zero_le (max n 0))
          have hcomp : (ψ/[nm n]).complexity ≤ k := by
            simpa using hψk
          have h0 := ih (ψ/[nm n]) hcomp (e := e) (H := adjoin H n) (f := rel1 f n)
            (Γ := insert (ψ/[nm n]) (insert (∼(ψ/[nm n])) Γ))
            (rel1_monotone hmono n) (rel1_infl hinfl n)
            (le_trans hg1 hf0n) (by simp) (by simp)
          have hbound : n ≤ rel1 f n 0 := by
            simpa [rel1] using hinfl n
          have hexI := Zef2TC.exI (α := ONote.ofNat (2 * k + 2))
            (le_trans hg2 hf0n)
            ψ n hlt12 (hNF _) (hNF _) (Cl.ofNat _) hbound h0
          rw [Finset.insert_eq_self.mpr
            (Finset.mem_insert_of_mem hp)] at hexI
          have heq : (∼ψ)/[nm n] = ∼(ψ/[nm n]) := by simp
          rw [heq]
          exact hexI
        have hall := Zef2TC.allω (α := ONote.ofNat (2 * k + 3)) hroot (∼ψ)
          (fun _ => ONote.ofNat (2 * k + 2)) (fun _ => hlt23) (fun _ => hNF _) (hNF _)
          (fun _ => Cl.ofNat _) fam
        rwa [Finset.insert_eq_self.mpr hall'] at hall

/-- Non-`k`-indexed corollary: EM at the formula's own complexity rung. -/
theorem em_Zef2TC' (φ : ArithmeticFormula ℕ)
    (hmono : Monotone f) (hinfl : ∀ m, m ≤ f m)
    (hgate : clog (2 * φ.complexity + 1) ≤ f 0)
    (hp : φ ∈ Γ) (hn : ∼φ ∈ Γ) :
    Zef2TC (ONote.ofNat (2 * φ.complexity + 1)) e H f 0 Γ :=
  em_Zef2TC φ.complexity φ le_rfl hmono hinfl hgate hp hn

private lemma em_cong_atomic_rel {n : ℕ} (w w' : Fin n → ArithmeticTerm ℕ)
    (hval : ∀ i, stdClosedVal (w i) = stdClosedVal (w' i))
    {ar : ℕ} (r : (ℒₒᵣ).Rel ar) (v : Fin ar → ArithmeticSemiterm ℕ n)
    {α : ONote} {c : ℕ}
    (hαN : Nlog α ≤ f 0)
    (hp : (Rew.subst w ▹ Semiformula.rel r v) ∈ Γ)
    (hn : (∼(Rew.subst w' ▹ Semiformula.rel r v)) ∈ Γ) :
    Zef2TC α e H f c Γ := by
  have hp' : Semiformula.rel r (fun i => Rew.subst w (v i)) ∈ Γ := by
    simpa [Semiformula.rew_rel, Function.comp_def] using hp
  have hn' : Semiformula.nrel r (fun i => Rew.subst w' (v i)) ∈ Γ := by
    simpa [Semiformula.rew_rel, Function.comp_def] using hn
  by_cases ht : atomTrue (Semiformula.rel r (fun i => Rew.subst w (v i)))
  · exact Zef2TC.trueRel hαN r _ ht hp'
  · have htn : atomTrue (Semiformula.nrel r (fun i => Rew.subst w (v i))) :=
      (atomTrue_nrel_iff_not_rel r _).mpr ht
    have htn' : atomTrue (Semiformula.nrel r (fun i => Rew.subst w' (v i))) :=
      (atomTrue_nrel_congr r _ _
        (fun i => embedding_valm_subst_congr w w' hval (v i))).mp htn
    exact Zef2TC.trueNrel hαN r _ htn' hn'

private lemma em_cong_atomic_nrel {n : ℕ} (w w' : Fin n → ArithmeticTerm ℕ)
    (hval : ∀ i, stdClosedVal (w i) = stdClosedVal (w' i))
    {ar : ℕ} (r : (ℒₒᵣ).Rel ar) (v : Fin ar → ArithmeticSemiterm ℕ n)
    {α : ONote} {c : ℕ}
    (hαN : Nlog α ≤ f 0)
    (hp : (Rew.subst w ▹ Semiformula.nrel r v) ∈ Γ)
    (hn : (∼(Rew.subst w' ▹ Semiformula.nrel r v)) ∈ Γ) :
    Zef2TC α e H f c Γ := by
  have hp' : Semiformula.nrel r (fun i => Rew.subst w (v i)) ∈ Γ := by
    simpa [Semiformula.rew_nrel, Function.comp_def] using hp
  have hn' : Semiformula.rel r (fun i => Rew.subst w' (v i)) ∈ Γ := by
    simpa [Semiformula.rew_nrel, Function.comp_def] using hn
  by_cases ht : atomTrue (Semiformula.nrel r (fun i => Rew.subst w (v i)))
  · exact Zef2TC.trueNrel hαN r _ ht hp'
  · have htn : atomTrue (Semiformula.rel r (fun i => Rew.subst w (v i))) := by
      by_contra hno
      exact ht ((atomTrue_nrel_iff_not_rel r _).mpr hno)
    have htn' : atomTrue (Semiformula.rel r (fun i => Rew.subst w' (v i))) :=
      (atomTrue_rel_congr r _ _
        (fun i => embedding_valm_subst_congr w w' hval (v i))).mp htn
    exact Zef2TC.trueRel hαN r _ htn' hn'

/-- **Value-congruent budgeted EM** (arity-general): for pointwise value-equal closed
substitutions `w, w'`, any sequent containing `Rew.subst w ▹ ψ` and `∼(Rew.subst w' ▹ ψ)` is
cut-free `Zef2TC`-derivable at the deterministic rung `ofNat (2k+1)`.

- [EW12, Lemma 32] -/
theorem em_cong_Zef2TC (k : ℕ) {n : ℕ} (w w' : Fin n → ArithmeticTerm ℕ)
    (ψ : ArithmeticSemiformula ℕ n) (hk : ψ.complexity ≤ k)
    (hval : ∀ i, stdClosedVal (w i) = stdClosedVal (w' i))
    (hmono : Monotone f) (hinfl : ∀ m, m ≤ f m) (hgate : clog (2 * k + 1) ≤ f 0)
    (hp : (Rew.subst w ▹ ψ) ∈ Γ) (hn : (∼(Rew.subst w' ▹ ψ)) ∈ Γ) :
    Zef2TC (ONote.ofNat (2 * k + 1)) e H f 0 Γ := by
  induction k generalizing n w w' ψ e H f Γ with
  | zero =>
    have hgate' : Nlog (ONote.ofNat 1) ≤ f 0 := le_trans (Nlog_ofNat_le 1) hgate
    cases ψ using Semiformula.cases' with
    | hverum => exact Zef2TC.verumR hgate' (by simpa using hp)
    | hfalsum => exact Zef2TC.verumR hgate' (by simpa using hn)
    | hrel r v => exact em_cong_atomic_rel w w' hval r v hgate' hp hn
    | hnrel r v => exact em_cong_atomic_nrel w w' hval r v hgate' hp hn
    | hand φ ψ => simp at hk
    | hor φ ψ => simp at hk
    | hall φ => simp at hk
    | hexs φ => simp at hk
  | succ k ih =>
    rw [show 2 * (k + 1) + 1 = 2 * k + 3 by ring] at hgate ⊢
    have hNF : ∀ m : ℕ, (ONote.ofNat m).NF := fun m => ONote.nf_ofNat m
    have hlt12 : ONote.ofNat (2 * k + 1) < ONote.ofNat (2 * k + 2) := ofNat_lt_ofNat (by omega)
    have hlt23 : ONote.ofNat (2 * k + 2) < ONote.ofNat (2 * k + 3) := ofNat_lt_ofNat (by omega)
    have hroot : Nlog (ONote.ofNat (2 * k + 3)) ≤ f 0 := le_trans (Nlog_ofNat_le _) hgate
    have hg2 : Nlog (ONote.ofNat (2 * k + 2)) ≤ f 0 :=
      le_trans (Nlog_ofNat_le _) (le_trans (clog_mono (by omega)) hgate)
    have hg1 : clog (2 * k + 1) ≤ f 0 := le_trans (clog_mono (by omega)) hgate
    cases ψ using Semiformula.cases' with
    | hverum => exact Zef2TC.verumR hroot (by simpa using hp)
    | hfalsum => exact Zef2TC.verumR hroot (by simpa using hn)
    | hrel r v => exact em_cong_atomic_rel w w' hval r v hroot hp hn
    | hnrel r v => exact em_cong_atomic_nrel w w' hval r v hroot hp hn
    | hand a b =>
        have hak : a.complexity ≤ k := by simp only [Semiformula.complexity_and] at hk; omega
        have hbk : b.complexity ≤ k := by simp only [Semiformula.complexity_and] at hk; omega
        have hp' : ((Rew.subst w ▹ a) ⋏ (Rew.subst w ▹ b)) ∈ Γ := by simpa using hp
        have hn' : (∼(Rew.subst w' ▹ a) ⋎ ∼(Rew.subst w' ▹ b)) ∈ Γ := by simpa using hn
        have h1 := ih (n := n) w w' a hak hval (e := e) (H := H) (f := f)
          (Γ := insert (Rew.subst w ▹ a)
            (insert (∼(Rew.subst w' ▹ a)) (insert (∼(Rew.subst w' ▹ b)) Γ)))
          hmono hinfl hg1 (by simp) (by simp)
        have h2 := ih (n := n) w w' b hbk hval (e := e) (H := H) (f := f)
          (Γ := insert (Rew.subst w ▹ b)
            (insert (∼(Rew.subst w' ▹ a)) (insert (∼(Rew.subst w' ▹ b)) Γ)))
          hmono hinfl hg1 (by simp) (by simp)
        have hand := Zef2TC.andI (α := ONote.ofNat (2 * k + 2)) hg2
          (Rew.subst w ▹ a) (Rew.subst w ▹ b) hlt12 hlt12
          (hNF _) (hNF _) (hNF _) (Cl.ofNat _) (Cl.ofNat _) h1 h2
        rw [Finset.insert_eq_self.mpr
          (show ((Rew.subst w ▹ a) ⋏ (Rew.subst w ▹ b))
            ∈ insert (∼(Rew.subst w' ▹ a)) (insert (∼(Rew.subst w' ▹ b)) Γ)
            by simp [hp'])] at hand
        have hor := Zef2TC.orI (α := ONote.ofNat (2 * k + 3)) hroot
          (∼(Rew.subst w' ▹ a)) (∼(Rew.subst w' ▹ b)) hlt23
          (hNF _) (hNF _) (Cl.ofNat _) hand
        rwa [Finset.insert_eq_self.mpr hn'] at hor
    | hor a b =>
        have hak : a.complexity ≤ k := by simp only [Semiformula.complexity_or] at hk; omega
        have hbk : b.complexity ≤ k := by simp only [Semiformula.complexity_or] at hk; omega
        have hp' : ((Rew.subst w ▹ a) ⋎ (Rew.subst w ▹ b)) ∈ Γ := by simpa using hp
        have hn' : (∼(Rew.subst w' ▹ a) ⋏ ∼(Rew.subst w' ▹ b)) ∈ Γ := by simpa using hn
        have h1 := ih (n := n) w w' a hak hval (e := e) (H := H) (f := f)
          (Γ := insert (∼(Rew.subst w' ▹ a))
            (insert (Rew.subst w ▹ a) (insert (Rew.subst w ▹ b) Γ)))
          hmono hinfl hg1 (by simp) (by simp)
        have h2 := ih (n := n) w w' b hbk hval (e := e) (H := H) (f := f)
          (Γ := insert (∼(Rew.subst w' ▹ b))
            (insert (Rew.subst w ▹ a) (insert (Rew.subst w ▹ b) Γ)))
          hmono hinfl hg1 (by simp) (by simp)
        have hand := Zef2TC.andI (α := ONote.ofNat (2 * k + 2)) hg2
          (∼(Rew.subst w' ▹ a)) (∼(Rew.subst w' ▹ b)) hlt12 hlt12
          (hNF _) (hNF _) (hNF _) (Cl.ofNat _) (Cl.ofNat _) h1 h2
        rw [Finset.insert_eq_self.mpr
          (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hn'))] at hand
        have hor := Zef2TC.orI (α := ONote.ofNat (2 * k + 3)) hroot
          (Rew.subst w ▹ a) (Rew.subst w ▹ b) hlt23
          (hNF _) (hNF _) (Cl.ofNat _) hand
        rwa [Finset.insert_eq_self.mpr (show ((Rew.subst w ▹ a) ⋎ (Rew.subst w ▹ b)) ∈ Γ
          by simp [hp'])] at hor
    | hall a =>
        have hak : a.complexity ≤ k := by simp only [Semiformula.complexity_all] at hk; omega
        have hp' : (∀⁰ ((Rew.subst w).q ▹ a)) ∈ Γ := by simpa using hp
        have hn' : (∃⁰ ((Rew.subst w').q ▹ ∼a)) ∈ Γ := by simpa using hn
        have fam : ∀ m, Zef2TC (ONote.ofNat (2 * k + 2)) e (adjoin H m) (rel1 f m) 0
            (insert ((((Rew.subst w).q ▹ a))/[nm m]) Γ) := by
          intro m
          have hf0m : f 0 ≤ rel1 f m 0 := by
            simpa [rel1] using hmono (Nat.zero_le (max m 0))
          have hvalm : ∀ i, stdClosedVal ((nm m :> w) i) = stdClosedVal ((nm m :> w') i) :=
            embedding_valm_cons_nm_congr w w' m hval
          have h0 := ih (n := n + 1) (nm m :> w) (nm m :> w') a hak hvalm
            (e := e) (H := adjoin H m) (f := rel1 f m)
            (Γ := insert (((Rew.subst w).q ▹ a)/[nm m])
              (insert (∼(((Rew.subst w').q ▹ a)/[nm m])) Γ))
            (rel1_monotone hmono m) (rel1_infl hinfl m) (le_trans hg1 hf0m)
            (by rw [← embedding_subst_q_cons_app]; simp)
            (by rw [← embedding_subst_q_cons_app]; simp)
          have hbound : m ≤ rel1 f m 0 := by
            simpa [rel1] using hinfl m
          have hexI := Zef2TC.exI (α := ONote.ofNat (2 * k + 2))
            (le_trans hg2 hf0m)
            ((Rew.subst w').q ▹ ∼a) m hlt12 (hNF _) (hNF _) (Cl.ofNat _) hbound
            (by
              have heq : (((Rew.subst w').q ▹ ∼a)/[nm m])
                  = ∼(((Rew.subst w').q ▹ a)/[nm m]) := by simp
              rw [heq, Finset.insert_comm]
              exact h0)
          rwa [Finset.insert_eq_self.mpr (Finset.mem_insert_of_mem hn')] at hexI
        have hall := Zef2TC.allω (α := ONote.ofNat (2 * k + 3)) hroot
          ((Rew.subst w).q ▹ a) (fun _ => ONote.ofNat (2 * k + 2)) (fun _ => hlt23)
          (fun _ => hNF _) (hNF _) (fun _ => Cl.ofNat _) fam
        rwa [Finset.insert_eq_self.mpr hp'] at hall
    | hexs a =>
        have hak : a.complexity ≤ k := by simp only [Semiformula.complexity_exs] at hk; omega
        have hp' : (∃⁰ ((Rew.subst w).q ▹ a)) ∈ Γ := by simpa using hp
        have hn' : (∀⁰ ((Rew.subst w').q ▹ ∼a)) ∈ Γ := by simpa using hn
        have fam : ∀ m, Zef2TC (ONote.ofNat (2 * k + 2)) e (adjoin H m) (rel1 f m) 0
            (insert ((((Rew.subst w').q ▹ ∼a))/[nm m]) Γ) := by
          intro m
          have hf0m : f 0 ≤ rel1 f m 0 := by
            simpa [rel1] using hmono (Nat.zero_le (max m 0))
          have hvalm : ∀ i, stdClosedVal ((nm m :> w) i) = stdClosedVal ((nm m :> w') i) :=
            embedding_valm_cons_nm_congr w w' m hval
          have h0 := ih (n := n + 1) (nm m :> w) (nm m :> w') a hak hvalm
            (e := e) (H := adjoin H m) (f := rel1 f m)
            (Γ := insert (((Rew.subst w).q ▹ a)/[nm m])
              (insert (∼(((Rew.subst w').q ▹ a)/[nm m])) Γ))
            (rel1_monotone hmono m) (rel1_infl hinfl m) (le_trans hg1 hf0m)
            (by rw [← embedding_subst_q_cons_app]; simp)
            (by rw [← embedding_subst_q_cons_app]; simp)
          have hbound : m ≤ rel1 f m 0 := by
            simpa [rel1] using hinfl m
          have hexI := Zef2TC.exI (α := ONote.ofNat (2 * k + 2))
            (le_trans hg2 hf0m)
            ((Rew.subst w).q ▹ a) m hlt12 (hNF _) (hNF _) (Cl.ofNat _) hbound h0
          rw [Finset.insert_eq_self.mpr
            (Finset.mem_insert_of_mem hp')] at hexI
          have heq : (((Rew.subst w').q ▹ ∼a)/[nm m])
              = ∼(((Rew.subst w').q ▹ a)/[nm m]) := by simp
          rw [heq]
          exact hexI
        have hall := Zef2TC.allω (α := ONote.ofNat (2 * k + 3)) hroot
          ((Rew.subst w').q ▹ ∼a) (fun _ => ONote.ofNat (2 * k + 2)) (fun _ => hlt23)
          (fun _ => hNF _) (hNF _) (fun _ => Cl.ofNat _) fam
        rwa [Finset.insert_eq_self.mpr hn'] at hall

/-- Single-term wrapper: closed terms `s, s'` of equal standard value. -/
theorem em_cong1_Zef2TC (s s' : ArithmeticTerm ℕ)
    (hval : stdClosedVal s = stdClosedVal s')
    (ψ : ArithmeticSemiformula ℕ 1)
    (hmono : Monotone f) (hinfl : ∀ m, m ≤ f m)
    (hgate : clog (2 * ψ.complexity + 1) ≤ f 0)
    (hp : (ψ/[s]) ∈ Γ) (hn : (∼(ψ/[s'])) ∈ Γ) :
    Zef2TC (ONote.ofNat (2 * ψ.complexity + 1)) e H f 0 Γ := by
  refine em_cong_Zef2TC ψ.complexity ![s] ![s'] ψ le_rfl ?_ hmono hinfl hgate hp hn
  intro i
  cases i using Fin.cases with
  | zero => simpa using hval
  | succ j => exact j.elim0

end GoodsteinPA.E1EmbeddingGrind
