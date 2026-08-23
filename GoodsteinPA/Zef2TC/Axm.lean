module

public import GoodsteinPA.Zef2TC.EmbedV3

@[expose] public section

namespace GoodsteinPA.E1EmbeddingGrind

open LO LO.FirstOrder LO.FirstOrder.ArithmeticTerm ONote
open GoodsteinPA.OperatorZeh GoodsteinPA.OperatorZinfty

/-! ### Bounded truth for ∃-free formulas (the `axm` engine)

All PA⁻/EQ axioms except `addEqOfLt` are (∀-closures of) ∃-free matrices; a TRUE closed
∃-free formula is cut-free `Zef2TC`-derivable at the deterministic rung `ofNat (2k+1)` —
no witness budget at all (`exI` never fires). `addEqOfLt` (witness `z = y - x ≤ y`, paid by
the branch slot) and the induction schema (cut-tower over `em_Zef2TC`) are the two bespoke
residues. -/

/-- No `∃⁰` anywhere (the Π-fragment over NNF).  Truth of such closed formulas needs no
witness data, so the bounded-truth derivation avoids `exI`'s slot gate entirely. -/
def ExFree : ∀ {n : ℕ}, ArithmeticSemiformula ℕ n → Prop
  | _, Semiformula.verum => True
  | _, Semiformula.falsum => True
  | _, Semiformula.rel _ _ => True
  | _, Semiformula.nrel _ _ => True
  | _, Semiformula.and φ ψ => ExFree φ ∧ ExFree ψ
  | _, Semiformula.or φ ψ => ExFree φ ∧ ExFree ψ
  | _, Semiformula.all φ => ExFree φ
  | _, Semiformula.exs _ => False

variable {n : ℕ}

@[simp, grind .] lemma exFree_verum : ExFree (⊤ : ArithmeticSemiformula ℕ n) := trivial
@[simp, grind .] lemma exFree_falsum : ExFree (⊥ : ArithmeticSemiformula ℕ n) := trivial
@[simp, grind .] lemma exFree_rel {k : ℕ} (r : (ℒₒᵣ).Rel k) (v) :
    ExFree (Semiformula.rel (n := n) r v) := trivial
@[simp, grind .] lemma exFree_nrel {k : ℕ} (r : (ℒₒᵣ).Rel k) (v) :
    ExFree (Semiformula.nrel (n := n) r v) := trivial
@[simp, grind =] lemma exFree_and {φ ψ : ArithmeticSemiformula ℕ n} :
    ExFree (φ ⋏ ψ) ↔ ExFree φ ∧ ExFree ψ := Iff.rfl
@[simp, grind =] lemma exFree_or {φ ψ : ArithmeticSemiformula ℕ n} :
    ExFree (φ ⋎ ψ) ↔ ExFree φ ∧ ExFree ψ := Iff.rfl
@[simp, grind =] lemma exFree_all {φ : ArithmeticSemiformula ℕ (n + 1)} :
    ExFree (∀⁰ φ) ↔ ExFree φ := Iff.rfl
@[simp, grind =] lemma exFree_exs {φ : ArithmeticSemiformula ℕ (n + 1)} :
    ExFree (∃⁰ φ) ↔ False := Iff.rfl

/-- `ExFree` is stable under every rewriting (rewriting preserves the connective tree). -/
lemma ExFree.rew {n₁ : ℕ} (ψ : ArithmeticSemiformula ℕ n₁) : ExFree ψ →
    ∀ {n₂ : ℕ} (ω : Rew ℒₒᵣ ℕ n₁ ℕ n₂), ExFree (ω ▹ ψ) := by
  induction ψ using Semiformula.rec' with
  | hverum => intro _ n₂ ω; simp
  | hfalsum => intro _ n₂ ω; simp
  | hrel r v => intro _ n₂ ω; simp [Function.comp_def]
  | hnrel r v => intro _ n₂ ω; simp [Function.comp_def]
  | hand φ ψ ihφ ihψ =>
      intro h n₂ ω
      simp only [LogicalConnective.HomClass.map_and, exFree_and]
      exact ⟨ihφ h.1 ω, ihψ h.2 ω⟩
  | hor φ ψ ihφ ihψ =>
      intro h n₂ ω
      simp only [LogicalConnective.HomClass.map_or, exFree_or]
      exact ⟨ihφ h.1 ω, ihψ h.2 ω⟩
  | hall φ ih =>
      intro h n₂ ω
      rw [Rewriting.app_all]
      exact ih h ω.q
  | hexs φ ih => intro h; exact absurd h (by simp)

/-- **Bounded ω-truth for the ∃-free fragment** (the W1 engine): a TRUE (zero-assignment)
∃-free formula in `Γ` is cut-free `Zef2TC`-derivable at the deterministic-complexity rung.
Same budget discipline as `em_Zef2TC` — all hypotheses `rel1`-stable, the `all` branches
relativize the slot, and no `exI` ever fires. -/
theorem truth_exFree_Zef2TC (k : ℕ) :
    ∀ (ψ : ArithmeticFormula ℕ), ψ.complexity ≤ k → ExFree ψ → atomTrue ψ →
    ∀ {e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {Γ : Finset (ArithmeticFormula ℕ)},
      Monotone f → (∀ m, m ≤ f m) → clog (2 * k + 1) ≤ f 0 → ψ ∈ Γ →
      Zef2TC (ONote.ofNat (2 * k + 1)) e H f 0 Γ := by
  induction k with
  | zero =>
    intro ψ hk hex htrue e H f Γ hmono hinfl hgate hmem
    have hgate' : Nlog (ONote.ofNat 1) ≤ f 0 := le_trans (Nlog_ofNat_le 1) hgate
    cases ψ using Semiformula.cases' with
    | hverum => exact Zef2TC.verumR hgate' hmem
    | hfalsum => exact htrue.elim
    | hrel r v => exact Zef2TC.trueRel hgate' r v htrue hmem
    | hnrel r v => exact Zef2TC.trueNrel hgate' r v htrue hmem
    | hand φ ψ => simp at hk
    | hor φ ψ => simp at hk
    | hall φ => simp at hk
    | hexs φ => simp at hk
  | succ k ih =>
    intro ψ hk hex htrue e H f Γ hmono hinfl hgate hmem
    rw [show 2 * (k + 1) + 1 = 2 * k + 3 by ring] at hgate ⊢
    have hNF : ∀ m : ℕ, (ONote.ofNat m).NF := fun m => ONote.nf_ofNat m
    have hlt13 : ONote.ofNat (2 * k + 1) < ONote.ofNat (2 * k + 3) := ofNat_lt_ofNat (by omega)
    have hroot : Nlog (ONote.ofNat (2 * k + 3)) ≤ f 0 := le_trans (Nlog_ofNat_le _) hgate
    have hg1 : clog (2 * k + 1) ≤ f 0 := le_trans (clog_mono (by omega)) hgate
    cases ψ using Semiformula.cases' with
    | hverum => exact Zef2TC.verumR hroot hmem
    | hfalsum => exact htrue.elim
    | hrel r v => exact Zef2TC.trueRel hroot r v htrue hmem
    | hnrel r v => exact Zef2TC.trueNrel hroot r v htrue hmem
    | hand a b =>
        have hak : a.complexity ≤ k := by simp only [Semiformula.complexity_and] at hk; omega
        have hbk : b.complexity ≤ k := by simp only [Semiformula.complexity_and] at hk; omega
        have hta : atomTrue a := htrue.1
        have htb : atomTrue b := htrue.2
        have h1 := ih a hak hex.1 hta (e := e) (H := H) (f := f)
          (Γ := insert a Γ) hmono hinfl hg1 (Finset.mem_insert_self _ _)
        have h2 := ih b hbk hex.2 htb (e := e) (H := H) (f := f)
          (Γ := insert b Γ) hmono hinfl hg1 (Finset.mem_insert_self _ _)
        have hand := Zef2TC.andI (α := ONote.ofNat (2 * k + 3)) hroot
          a b hlt13 hlt13 (hNF _) (hNF _) (hNF _) (Cl.ofNat _) (Cl.ofNat _) h1 h2
        rwa [Finset.insert_eq_self.mpr hmem] at hand
    | hor a b =>
        have hak : a.complexity ≤ k := by simp only [Semiformula.complexity_or] at hk; omega
        have hbk : b.complexity ≤ k := by simp only [Semiformula.complexity_or] at hk; omega
        have htab : atomTrue a ∨ atomTrue b := htrue
        have h1 : Zef2TC (ONote.ofNat (2 * k + 1)) e H f 0 (insert a (insert b Γ)) := by
          rcases htab with hta | htb
          · exact ih a hak hex.1 hta hmono hinfl hg1 (Finset.mem_insert_self _ _)
          · exact ih b hbk hex.2 htb hmono hinfl hg1
              (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
        have hor := Zef2TC.orI (α := ONote.ofNat (2 * k + 3)) hroot
          a b hlt13 (hNF _) (hNF _) (Cl.ofNat _) h1
        rwa [Finset.insert_eq_self.mpr hmem] at hor
    | hall a =>
        have hak : a.complexity ≤ k := by simp only [Semiformula.complexity_all] at hk; omega
        have fam : ∀ m, Zef2TC (ONote.ofNat (2 * k + 1)) e (adjoin H m) (rel1 f m) 0
            (insert (a/[nm m]) Γ) := by
          intro m
          have hf0m : f 0 ≤ rel1 f m 0 := by
            simpa [rel1] using hmono (Nat.zero_le (max m 0))
          have hsk : (a/[nm m]).complexity ≤ k := by
            have : (a/[nm m]).complexity = a.complexity := by simp
            omega
          have hsex : ExFree (a/[nm m]) := hex.rew a (Rew.subst ![nm m])
          have hstrue : atomTrue (a/[nm m]) := by
            have hall : ∀ x : ℕ, Semiformula.gEvalm ℕ ![x] (fun _ => 0) a := by
              simpa [atomTrue, Matrix.constant_eq_singleton, Matrix.empty_eq] using htrue
            simpa [atomTrue, Semiformula.eval_substs, ArithmeticTerm.valm_nm,
              Matrix.constant_eq_singleton, Matrix.empty_eq] using hall m
          exact ih (a/[nm m]) hsk hsex hstrue
            (rel1_monotone hmono m) (rel1_infl hinfl m) (le_trans hg1 hf0m)
            (Finset.mem_insert_self _ _)
        have hall := Zef2TC.allω (α := ONote.ofNat (2 * k + 3)) hroot
          a (fun _ => ONote.ofNat (2 * k + 1)) (fun _ => hlt13)
          (fun _ => hNF _) (hNF _) (fun _ => Cl.ofNat _) fam
        rwa [Finset.insert_eq_self.mpr hmem] at hall
    | hexs a => exact absurd hex (by simp)

@[simp, grind =] lemma exFree_allClosure : ∀ {φ : ArithmeticSemiformula ℕ n},
    ExFree (∀⁰* φ) ↔ ExFree φ := by
  induction n with
  | zero => intro φ; rfl
  | succ n ih => intro φ; rw [show (∀⁰* φ) = (∀⁰* (∀⁰ φ)) from rfl, ih]; exact exFree_all

/-- The closing assignment fixes embedded sentences (no fvars to rewrite). -/
lemma asg_emb_fix (env : ℕ → ℕ) (σ : ArithmeticSentence) :
    asg env ▹ (↑σ : ArithmeticFormula ℕ) = ↑σ := by
  have hc : (asg env).comp Rew.emb = (Rew.emb : Rew ℒₒᵣ Empty 0 ℕ 0) := by
    ext x
    · exact x.elim0
    · exact x.elim
  show asg env ▹ (Rew.emb ▹ σ) = Rew.emb ▹ σ
  rw [← TransitiveRewriting.comp_app, hc]

/-- Truth transfer: a sentence true in `ℕ` stays `atomTrue` after embedding + any closing
assignment (`asg env` fixes the fvar-free embed; mirrors `embedC`'s `axm` truth step). -/
lemma atomTrue_asg_emb {σ : ArithmeticSentence} (h : ℕ ⊧ₘ σ) (env : ℕ → ℕ) :
    atomTrue (asg env ▹ (↑σ : ArithmeticFormula ℕ)) := by
  simp only [atomTrue, asg, Semiformula.eval_rewrite, Semiformula.eval_emb]
  rw [models_iff] at h
  simpa [Matrix.empty_eq] using h

/-- **The ∃-free `axm` wrapper**: a TRUE ∃-free PA-axiom sentence in `Γ` is budgeted-embeddable
outright — `truth_exFree_Zef2TC` at the V3 structural budget of the `closed` case. -/
theorem budgetedEmbedsV3_of_exFree_true {Γ}
    (σ : ArithmeticSentence) (hex : ExFree (↑σ : ArithmeticFormula ℕ)) (htrue : ℕ ⊧ₘ σ)
    (hΓ : (↑σ : ArithmeticFormula ℕ) ∈ Γ) : BudgetedEmbedsV3 Γ := by
  set k : ℕ := (↑σ : ArithmeticFormula ℕ).complexity with hk
  refine ⟨clog (2 * k + 1), 0, 0, 0, ONote.ofNat (2 * k + 1),
    ONote.NF.zero, ONote.nf_ofNat _, Nlog_ofNat_le _, fun env => ?_⟩
  have hf1 := ewRootSlot_f1 (0 : ONote) (clog (2 * k + 1))
  have hmono : Monotone (rel1 (ewRootSlot 0 (clog (2 * k + 1))) (envSup env 0)) :=
    rel1_monotone hf1.1.monotone (envSup env 0)
  have hinfl : ∀ m, m ≤ rel1 (ewRootSlot 0 (clog (2 * k + 1))) (envSup env 0) m :=
    rel1_infl (fun m => by have := hf1.2 m; omega) (envSup env 0)
  have hgate : clog (2 * k + 1)
      ≤ rel1 (ewRootSlot 0 (clog (2 * k + 1))) (envSup env 0) 0 :=
    le_relSlot_zero 0 _ _
  have hcompl : (asg env ▹ (↑σ : ArithmeticFormula ℕ)).complexity ≤ k := by
    simp [hk]
  exact truth_exFree_Zef2TC k _ hcompl (hex.rew _ _) (atomTrue_asg_emb htrue env)
    hmono hinfl hgate (Finset.mem_image_of_mem _ hΓ)

/-! ### The PA⁻ `axm` sweep -/

/-- **`addEqOfLt`** — the SOLE ∃-carrying PA⁻ axiom (`∀ x y, x < y → ∃ z, x + z = y`).
The witness `z = y - x ≤ y` is dominated by the second ω-branch numeral, hence by the branch
slot's relativization (`rel1 · y`) — no structural tower needed. -/
theorem budgetedEmbedsV3_addEqOfLt {Γ}
    (hΓ : (↑(Arithmetic.PeanoMinus.Axiom.addEqOfLt) : ArithmeticFormula ℕ) ∈ Γ) :
    BudgetedEmbedsV3 Γ := by
  refine ⟨clog 11, 0, 0, 0, ONote.ofNat 5, ONote.NF.zero, ONote.nf_ofNat _,
    le_trans (Nlog_ofNat_le 5) (clog_mono (by omega)), fun env => ?_⟩
  set B : ℕ := clog 11 with hB
  set f : ℕ → ℕ := rel1 (ewRootSlot 0 B) (envSup env 0) with hf
  have hf1 := ewRootSlot_f1 (0 : ONote) B
  have hmono : Monotone f := rel1_monotone hf1.1.monotone (envSup env 0)
  have hinfl : ∀ m, m ≤ f m := rel1_infl (fun m => by have := hf1.2 m; omega) (envSup env 0)
  have hgate : clog 11 ≤ f 0 := le_relSlot_zero 0 B (envSup env 0)
  have hNF : ∀ m : ℕ, (ONote.ofNat m).NF := fun m => ONote.nf_ofNat m
  -- normalize the image formula to constructor form
  have himg : asg env ▹ (↑(Arithmetic.PeanoMinus.Axiom.addEqOfLt)
        : ArithmeticFormula ℕ)
      = ∀⁰ ∀⁰ ((∼(Semiformula.rel Language.LT.lt ![#1, #0]))
          ⋎ (∃⁰ (Semiformula.rel Language.Eq.eq ![‘(#2 + #0)’, #1]))) := by
    rw [asg_emb_fix]
    simp only [Arithmetic.PeanoMinus.Axiom.addEqOfLt, Semiformula.Operator.eq_def,
      Semiformula.Operator.lt_def, Semiformula.imp_eq]
    simp [Function.comp_def]
    constructor <;> simp [Matrix.comp_vecCons]
  have hmem := Finset.mem_image_of_mem (fun χ => asg env ▹ χ) hΓ
  rw [himg] at hmem
  set M : ArithmeticSemiformula ℕ 2 :=
    (∼(Semiformula.rel Language.LT.lt ![#1, #0]))
      ⋎ (∃⁰ (Semiformula.rel Language.Eq.eq ![‘(#2 + #0)’, #1])) with hM
  set Γ' : Finset (ArithmeticFormula ℕ) := Γ.image (fun χ => asg env ▹ χ) with hΓ'
  have hlt12 : ONote.ofNat 1 < ONote.ofNat 2 := ofNat_lt_ofNat (by omega)
  have hlt23 : ONote.ofNat 2 < ONote.ofNat 3 := ofNat_lt_ofNat (by omega)
  have hlt34 : ONote.ofNat 3 < ONote.ofNat 4 := ofNat_lt_ofNat (by omega)
  have hlt45 : ONote.ofNat 4 < ONote.ofNat 5 := ofNat_lt_ofNat (by omega)
  -- the OUTER ω-family
  have famA : ∀ a, Zef2TC (ONote.ofNat 4) 0 (adjoin (fun _ : ONote => True) a) (rel1 f a) 0
      (insert ((∀⁰ M)/[nm a]) Γ') := by
    intro a
    have hfa : f 0 ≤ rel1 f a 0 := by simpa [rel1] using hmono (Nat.zero_le (max a 0))
    have hmonoA : Monotone (rel1 f a) := rel1_monotone hmono a
    have hinflA : ∀ m, m ≤ rel1 f a m := rel1_infl hinfl a
    have hsubA : ((∀⁰ M)/[nm a]) = ∀⁰ ((Rew.subst ![nm a]).q ▹ M) := by
      simp
    rw [hsubA]
    -- the INNER ω-family
    have famB : ∀ b, Zef2TC (ONote.ofNat 3) 0 (adjoin (adjoin (fun _ : ONote => True) a) b)
        (rel1 (rel1 f a) b) 0
        (insert ((((Rew.subst ![nm a]).q ▹ M))/[nm b]) Γ') := by
      intro b
      have hfb : rel1 f a 0 ≤ rel1 (rel1 f a) b 0 := by
        simpa [rel1] using hmonoA (Nat.zero_le (max b 0))
      have hgb : ∀ k : ℕ, k ≤ 11 → Nlog (ONote.ofNat k) ≤ rel1 (rel1 f a) b 0 :=
        fun k hk => le_trans (Nlog_ofNat_le k)
          (le_trans (clog_mono hk) (le_trans hgate (le_trans hfa hfb)))
      -- collapse the composed substitution to the cons vector
      have hsubB : (((Rew.subst ![nm a]).q ▹ M))/[nm b]
          = (∼(Semiformula.rel Language.LT.lt ![nm a, nm b]))
            ⋎ (∃⁰ ((Rew.subst (nm b :> ![nm a])).q
                ▹ (Semiformula.rel Language.Eq.eq ![‘(#2 + #0)’, #1]))) := by
        rw [embedding_subst_q_cons_app]
        simp [hM, Matrix.comp_vecCons,
          Function.comp_def, Matrix.constant_eq_singleton]
      rw [hsubB]
      set A : ArithmeticFormula ℕ := ∼(Semiformula.rel Language.LT.lt ![nm a, nm b]) with hA
      set Eb : ArithmeticSemiformula ℕ 1 := (Rew.subst (nm b :> ![nm a])).q
        ▹ (Semiformula.rel Language.Eq.eq ![‘(#2 + #0)’, #1]) with hE
      set Δ : Finset (ArithmeticFormula ℕ) := insert A (insert (∃⁰ Eb) Γ') with hΔ
      have hD : Zef2TC (ONote.ofNat 2) 0 (adjoin (adjoin (fun _ : ONote => True) a) b)
          (rel1 (rel1 f a) b) 0 Δ := by
        by_cases hab : a < b
        · -- exI at witness b - a, trueRel leaf
          have hsubC : Eb/[nm (b - a)]
              = Semiformula.rel Language.Eq.eq
                  ![Semiterm.func Language.Add.add ![nm a, nm (b - a)], nm b] := by
            rw [hE, embedding_subst_q_cons_app]
            simp [Rew.func, Matrix.comp_vecCons,
              Semiterm.Operator.operator, Semiterm.Operator.Add.term_eq, Function.comp_def,
              Matrix.constant_eq_singleton]
          have htrue : atomTrue (Semiformula.rel Language.Eq.eq
              ![Semiterm.func Language.Add.add ![nm a, nm (b - a)], nm b]) := by
            simp [atomTrue, Semiformula.eval_rel, Semiterm.val_func, Matrix.empty_eq, Function.comp_def]
            omega
          have hleaf : Zef2TC (ONote.ofNat 1) 0 (adjoin (adjoin (fun _ : ONote => True) a) b)
              (rel1 (rel1 f a) b) 0 (insert (Eb/[nm (b - a)]) Δ) := by
            rw [hsubC]
            exact Zef2TC.trueRel (hgb 1 (by omega)) _ _ htrue (Finset.mem_insert_self _ _)
          have hwit : b - a ≤ rel1 (rel1 f a) b 0 := by
            have h1 : (b : ℕ) ≤ rel1 (rel1 f a) b 0 := by
              simpa [rel1] using hinflA (max b 0)
            omega
          have hexI := Zef2TC.exI (α := ONote.ofNat 2) (hgb 2 (by omega))
            Eb (b - a) hlt12 (ONote.nf_ofNat _) (ONote.nf_ofNat _) (Cl.ofNat _) hwit hleaf
          rwa [Finset.insert_eq_self.mpr
            (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))] at hexI
        · -- trueNrel leaf on ¬(a < b)
          have htrue : atomTrue (Semiformula.nrel Language.LT.lt ![nm a, nm b]) := by
            simp [atomTrue, Semiformula.eval_nrel, Matrix.empty_eq, Function.comp_def]
            omega
          exact Zef2TC.trueNrel (hgb 2 (by omega)) _ _ htrue
            (by
              show Semiformula.nrel Language.LT.lt ![nm a, nm b] ∈ Δ
              rw [hΔ, hA]
              exact Finset.mem_insert.mpr (Or.inl (by simp [Semiformula.neg_rel])))
      have horI := Zef2TC.orI (α := ONote.ofNat 3) (hgb 3 (by omega))
        A (∃⁰ Eb) hlt23 (ONote.nf_ofNat _) (ONote.nf_ofNat _) (Cl.ofNat _) hD
      exact horI
    have hallB := Zef2TC.allω (α := ONote.ofNat 4) (le_trans (Nlog_ofNat_le 4)
        (le_trans (clog_mono (by omega)) (le_trans hgate hfa)))
      ((Rew.subst ![nm a]).q ▹ M) (fun _ => ONote.ofNat 3) (fun _ => hlt34)
      (fun _ => ONote.nf_ofNat _) (ONote.nf_ofNat _) (fun _ => Cl.ofNat _)
      famB
    exact hallB
  -- assemble the OUTER allω
  have hallA := Zef2TC.allω (α := ONote.ofNat 5)
    (le_trans (Nlog_ofNat_le 5) (le_trans (clog_mono (by omega)) hgate))
    (∀⁰ M) (fun _ => ONote.ofNat 4) (fun _ => hlt45)
    (fun _ => ONote.nf_ofNat _) (ONote.nf_ofNat _) (fun _ => Cl.ofNat _) famA
  rwa [Finset.insert_eq_self.mpr hmem] at hallA

/-- **The PA⁻ `axm` dispatcher**: every PA⁻ axiom in `Γ` is budgeted-embeddable.  All cases
except `addEqOfLt` are TRUE ∃-free sentences — `budgetedEmbedsV3_of_exFree_true` (bounded
ω-truth), per-case `ExFree` by unfolding the concrete axiom.  -/
theorem budgetedEmbedsV3_axm_PAminus {Γ}
    (σ : ArithmeticSentence) (hσ : σ ∈ 𝗣𝗔⁻) (hΓ : (↑σ : ArithmeticFormula ℕ) ∈ Γ) :
    BudgetedEmbedsV3 Γ := by
  have hmod : ℕ ⊧ₘ σ := Semantics.modelsSet_iff.mp inferInstance hσ
  cases hσ with
  | equal φ hφ =>
      cases hφ with
      | refl => exact budgetedEmbedsV3_of_exFree_true _ (by
          simp [Theory.Eq.refl, Semiformula.Operator.eq_def]) hmod hΓ
      | symm => exact budgetedEmbedsV3_of_exFree_true _ (by
          simp [Theory.Eq.symm, Semiformula.Operator.eq_def, Semiformula.imp_eq]) hmod hΓ
      | trans => exact budgetedEmbedsV3_of_exFree_true _ (by
          simp [Theory.Eq.trans, Semiformula.Operator.eq_def, Semiformula.imp_eq]) hmod hΓ
      | funcExt f =>
          cases f with
          | zero => exact budgetedEmbedsV3_of_exFree_true _ (by
              simp [Theory.Eq.funcExt, Semiformula.Operator.eq_def,
                Semiformula.imp_eq, Matrix.conj,
                Matrix.comp_vecCons, Function.comp_def]) hmod hΓ
          | one => exact budgetedEmbedsV3_of_exFree_true _ (by
              simp [Theory.Eq.funcExt, Semiformula.Operator.eq_def,
                Semiformula.imp_eq, Matrix.conj,
                Matrix.comp_vecCons, Function.comp_def]) hmod hΓ
          | add => exact budgetedEmbedsV3_of_exFree_true _ (by
              simp [Theory.Eq.funcExt, Semiformula.Operator.eq_def,
                Semiformula.imp_eq, Matrix.conj,
                Matrix.vecTail,
                Matrix.comp_vecCons, Function.comp_def]) hmod hΓ
          | mul => exact budgetedEmbedsV3_of_exFree_true _ (by
              simp [Theory.Eq.funcExt, Semiformula.Operator.eq_def,
                Semiformula.imp_eq, Matrix.conj,
                Matrix.vecTail,
                Matrix.comp_vecCons, Function.comp_def]) hmod hΓ
      | relExt r =>
          cases r with
          | eq => exact budgetedEmbedsV3_of_exFree_true _ (by
              simp [Theory.Eq.relExt, Semiformula.Operator.eq_def, Semiformula.imp_eq, Matrix.conj,
                Matrix.vecTail,
                Matrix.comp_vecCons, Function.comp_def]) hmod hΓ
          | lt => exact budgetedEmbedsV3_of_exFree_true _ (by
              simp [Theory.Eq.relExt, Semiformula.Operator.eq_def,
                Semiformula.imp_eq, Matrix.conj,
                Matrix.vecTail,
                Matrix.comp_vecCons, Function.comp_def]) hmod hΓ
  | addZero => exact budgetedEmbedsV3_of_exFree_true _ (by
      simp [Arithmetic.PeanoMinus.Axiom.addZero, Semiformula.Operator.eq_def]) hmod hΓ
  | addAssoc => exact budgetedEmbedsV3_of_exFree_true _ (by
      simp [Arithmetic.PeanoMinus.Axiom.addAssoc, Semiformula.Operator.eq_def]) hmod hΓ
  | addComm => exact budgetedEmbedsV3_of_exFree_true _ (by
      simp [Arithmetic.PeanoMinus.Axiom.addComm, Semiformula.Operator.eq_def]) hmod hΓ
  | addEqOfLt => exact budgetedEmbedsV3_addEqOfLt hΓ
  | zeroLe => exact budgetedEmbedsV3_of_exFree_true _ (by
      simp [Arithmetic.PeanoMinus.Axiom.zeroLe, Semiformula.Operator.eq_def,
        Semiformula.Operator.lt_def, Semiformula.Operator.LE.def_of_Eq_of_LT]) hmod hΓ
  | zeroLtOne => exact budgetedEmbedsV3_of_exFree_true _ (by
      simp [Arithmetic.PeanoMinus.Axiom.zeroLtOne,
        Semiformula.Operator.lt_def]) hmod hΓ
  | oneLeOfZeroLt => exact budgetedEmbedsV3_of_exFree_true _ (by
      simp [Arithmetic.PeanoMinus.Axiom.oneLeOfZeroLt, Semiformula.Operator.eq_def,
        Semiformula.Operator.lt_def, Semiformula.Operator.LE.def_of_Eq_of_LT,
        Semiformula.imp_eq]) hmod hΓ
  | addLtAdd => exact budgetedEmbedsV3_of_exFree_true _ (by
      simp [Arithmetic.PeanoMinus.Axiom.addLtAdd,
        Semiformula.Operator.lt_def,
        Semiformula.imp_eq]) hmod hΓ
  | mulZero => exact budgetedEmbedsV3_of_exFree_true _ (by
      simp [Arithmetic.PeanoMinus.Axiom.mulZero, Semiformula.Operator.eq_def]) hmod hΓ
  | mulOne => exact budgetedEmbedsV3_of_exFree_true _ (by
      simp [Arithmetic.PeanoMinus.Axiom.mulOne, Semiformula.Operator.eq_def]) hmod hΓ
  | mulAssoc => exact budgetedEmbedsV3_of_exFree_true _ (by
      simp [Arithmetic.PeanoMinus.Axiom.mulAssoc, Semiformula.Operator.eq_def]) hmod hΓ
  | mulComm => exact budgetedEmbedsV3_of_exFree_true _ (by
      simp [Arithmetic.PeanoMinus.Axiom.mulComm, Semiformula.Operator.eq_def]) hmod hΓ
  | mulLtMul => exact budgetedEmbedsV3_of_exFree_true _ (by
      simp [Arithmetic.PeanoMinus.Axiom.mulLtMul,
        Semiformula.Operator.lt_def,
        Semiformula.imp_eq]) hmod hΓ
  | distr => exact budgetedEmbedsV3_of_exFree_true _ (by
      simp [Arithmetic.PeanoMinus.Axiom.distr, Semiformula.Operator.eq_def]) hmod hΓ
  | ltIrrefl => exact budgetedEmbedsV3_of_exFree_true _ (by
      simp [Arithmetic.PeanoMinus.Axiom.ltIrrefl,
        Semiformula.Operator.lt_def]) hmod hΓ
  | ltTrans => exact budgetedEmbedsV3_of_exFree_true _ (by
      simp [Arithmetic.PeanoMinus.Axiom.ltTrans,
        Semiformula.Operator.lt_def,
        Semiformula.imp_eq]) hmod hΓ
  | ltTri => exact budgetedEmbedsV3_of_exFree_true _ (by
      simp [Arithmetic.PeanoMinus.Axiom.ltTri, Semiformula.Operator.eq_def,
        Semiformula.Operator.lt_def]) hmod hΓ

end GoodsteinPA.E1EmbeddingGrind
