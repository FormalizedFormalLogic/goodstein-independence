module

public import GoodsteinPA.Zef2TC.Em
public import GoodsteinPA.Zef2TC.TermBound

@[expose] public section

namespace GoodsteinPA.E1EmbeddingGrind

open LO LO.FirstOrder LO.FirstOrder.ArithmeticTerm ONote
open GoodsteinPA.OperatorZeh GoodsteinPA.OperatorZinfty

/-! ### V3 — the structural-budget master predicate

`BudgetedEmbedsV3` refines `BudgetedEmbedsTC` (`GoodsteinPA/Zef2TC/EmbedTC.lean`) by choosing the
node ordinal `α` and the budgets `B, d, N, c` outside `∀ env` (uniform over assignments), with the
only env-dependence being the relativization index, fixed as the canonical assignment sup
`envSup env N`. -/
def BudgetedEmbedsV3 (Γ : Finset (ArithmeticFormula ℕ)) : Prop :=
  ∃ B d N : ℕ, ∃ e α : ONote, e.NF ∧ α.NF ∧ Nlog α ≤ B ∧
    ∀ env : ℕ → ℕ,
      Zef2TC α e (fun _ => True) (rel1 (ewRootSlot e B) (envSup env N)) d
        (Γ.image (fun φ => asg env ▹ φ))

variable {Γ : Finset (ArithmeticFormula ℕ)}

/-- `ewRootSlot` is monotone in the structural budget `B`. -/
@[grind =>]
lemma ewRootSlot_mono_B (e : ONote) {B B' : ℕ} (h : B ≤ B') (x : ℕ) :
    ewRootSlot e B x ≤ ewRootSlot e B' x := by
  simp only [ewRootSlot, rel1]
  have := hardy_monotone e (max_le_max h (le_refl x))
  omega

/-- The shifted-down assignment's sup is absorbed by one extra `N`. -/
@[grind .]
lemma envSup_shift_le (env : ℕ → ℕ) (N : ℕ) :
    envSup (fun x => env (x + 1)) N ≤ envSup env (N + 1) := by
  refine Finset.sup_le fun x hx => ?_
  simp only [Finset.mem_range] at hx
  exact le_envSup (by omega : x + 1 < N + 1)

/-- **V3 `closed`** — the deterministic-complexity EM leaf (structural `α = ofNat (2·complexity+1)`,
budget `clog`; `envSup env 0 = 0`). -/
lemma budgetedEmbedsV3_closed (φ : ArithmeticFormula ℕ) (hp : φ ∈ Γ) (hn : ∼φ ∈ Γ) :
    BudgetedEmbedsV3 Γ := by
  refine ⟨clog (2 * φ.complexity + 1), 0, 0, 0, ONote.ofNat (2 * φ.complexity + 1),
    ONote.NF.zero, ONote.nf_ofNat _, Nlog_ofNat_le _, ?_⟩
  intro env
  have hf1 := ewRootSlot_f1 (0 : ONote) (clog (2 * φ.complexity + 1))
  have hmono : Monotone (rel1 (ewRootSlot 0 (clog (2 * φ.complexity + 1))) (envSup env 0)) :=
    rel1_monotone hf1.1.monotone (envSup env 0)
  have hinfl : ∀ m, m ≤ rel1 (ewRootSlot 0 (clog (2 * φ.complexity + 1))) (envSup env 0) m :=
    rel1_infl (fun m => by have := hf1.2 m; omega) (envSup env 0)
  have hgate : clog (2 * (asg env ▹ φ).complexity + 1)
      ≤ rel1 (ewRootSlot 0 (clog (2 * φ.complexity + 1))) (envSup env 0) 0 := by
    simp only [Semiformula.complexity_rew]
    exact le_relSlot_zero 0 _ _
  have hem : Zef2TC (ONote.ofNat (2 * (asg env ▹ φ).complexity + 1)) (0 : ONote)
      (fun _ : ONote => True) (rel1 (ewRootSlot 0 (clog (2 * φ.complexity + 1))) (envSup env 0)) 0
      (Γ.image (fun ψ => asg env ▹ ψ)) :=
    em_Zef2TC' (asg env ▹ φ) hmono hinfl hgate
      (Finset.mem_image_of_mem _ hp)
      (by simpa using Finset.mem_image_of_mem (fun ψ => asg env ▹ ψ) hn)
  rwa [show (asg env ▹ φ).complexity = φ.complexity from by simp] at hem

/-- **V3 `verum`** — `verumR` at `α = 0`. -/
lemma budgetedEmbedsV3_verum (h : (⊤ : ArithmeticFormula ℕ) ∈ Γ) : BudgetedEmbedsV3 Γ := by
  refine ⟨0, 0, 0, 0, 0, ONote.NF.zero, ONote.NF.zero, by simp, ?_⟩
  intro env
  have hmem : (⊤ : ArithmeticFormula ℕ) ∈ Γ.image (fun ψ => asg env ▹ ψ) := by
    have := Finset.mem_image_of_mem (fun ψ => asg env ▹ ψ) h; simpa using this
  exact Zef2TC.verumR (by simp) hmem

/-- **V3 `wk`** — image weakening; all structural budgets carried. -/
lemma budgetedEmbedsV3_wk {Δ} (hsub : Δ ⊆ Γ) (ih : BudgetedEmbedsV3 Δ) : BudgetedEmbedsV3 Γ := by
  obtain ⟨B, d, N, e, α, he, hαNF, hNlogB, ih⟩ := ih
  refine ⟨B, d, N, e, α, he, hαNF, hNlogB, ?_⟩
  intro env
  exact (ih env).wk (ih env).gate (Finset.image_subset_image hsub)

/-- **V3 `or`** — closes `BudgetedEmbedsV3` under `⋎`-introduction from a single premise. -/
lemma budgetedEmbedsV3_or {φ ψ : ArithmeticFormula ℕ} (h : φ ⋎ ψ ∈ Γ)
    (ih : BudgetedEmbedsV3 (insert φ (insert ψ Γ))) : BudgetedEmbedsV3 Γ := by
  obtain ⟨B, d, N, e, α, he, hαNF, hNlogB, ih⟩ := ih
  -- `osucc` root, `B + 1` for the `Nlog`/gate slack
  refine ⟨B + 1, d, N, e, osucc α, he, osucc_NF hαNF, ?_, ?_⟩
  · have := Nlog_osucc_le hαNF; omega
  · intro env
    have D := ih env
    rw [Finset.image_insert, Finset.image_insert] at D
    have D' := D.mono_f (fun x => relSlot_mono (Nat.le_succ B) (le_refl (envSup env N)) x)
    have hg : Nlog (osucc α) ≤ rel1 (ewRootSlot e (B + 1)) (envSup env N) 0 := by
      have hs := Nlog_osucc_le hαNF
      have hb := le_relSlot_zero e (B + 1) (envSup env N)
      omega
    have hor := Zef2TC.orI (α := osucc α) hg
      (asg env ▹ φ) (asg env ▹ ψ)
      (lt_osucc hαNF) hαNF (osucc_NF hαNF) (clT α) D'
    have hmem : (asg env ▹ φ ⋎ asg env ▹ ψ)
        ∈ Γ.image (fun χ => asg env ▹ χ) := by
      have := Finset.mem_image_of_mem (fun χ => asg env ▹ χ) h; simpa using this
    rwa [Finset.insert_eq_self.mpr hmem] at hor

/-- **V3 `shift`** — closes `BudgetedEmbedsV3` under `Rewriting.shift`. -/
lemma budgetedEmbedsV3_shift (ih : BudgetedEmbedsV3 Γ) : BudgetedEmbedsV3 (Γ.image Rewriting.shift) := by
  obtain ⟨B, d, N, e, α, he, hαNF, hNlogB, ih⟩ := ih
  refine ⟨B, d, N + 1, e, α, he, hαNF, hNlogB, ?_⟩
  intro env
  -- the shifted assignment's index absorbs into `N + 1` via `envSup_shift_le`
  have D := ih (fun x => env (x + 1))
  have himg : (Γ.image (Rewriting.shift : ArithmeticFormula ℕ → ArithmeticFormula ℕ)).image
        (fun φ => asg env ▹ φ)
      = Γ.image (fun φ => asg (fun x => env (x + 1)) ▹ φ) := by
    have hcompB : (asg env).comp Rew.shift = asg (fun x => env (x + 1)) := by
      ext x
      · exact Fin.elim0 x
      · simp [asg, Rew.comp_app]
    rw [Finset.image_image]
    refine Finset.image_congr (fun ψ _ => ?_)
    show asg env ▹ (Rew.shift ▹ ψ) = asg (fun x => env (x + 1)) ▹ ψ
    rw [← TransitiveRewriting.comp_app, hcompB]
  rw [himg]
  exact D.mono_f (fun x => relSlot_mono (le_refl B) (envSup_shift_le env N) x)

/-- **V3 `all`** — closes `BudgetedEmbedsV3` under the ω-rule for `∀⁰ φ`. -/
lemma budgetedEmbedsV3_all {φ : ArithmeticSemiformula ℕ 1} (h : ∀⁰ φ ∈ Γ)
    (ih : BudgetedEmbedsV3 (insert (Rewriting.free φ) (Γ.image Rewriting.shift))) :
    BudgetedEmbedsV3 Γ := by
  obtain ⟨B, d, N, e, α, he, hαNF, hNlogB, ih⟩ := ih
  -- the node ordinal is uniform over branches (`β n := α`, root `osucc α`); the env-local budget
  -- index `envSup env N` is paid by the branch relativization `rel1 · n` via `envSup_cons_le`
  refine ⟨B + 1, d, N, e, osucc α, he, osucc_NF hαNF, ?_, ?_⟩
  · have := Nlog_osucc_le hαNF; omega
  · intro env
    -- the ω-family: each branch is the IH at `n :>ₙ env`, transported to the branch slot/operator
    have hfam : ∀ n, Zef2TC α e (adjoin (fun _ : ONote => True) n)
        (rel1 (rel1 (ewRootSlot e (B + 1)) (envSup env N)) n) d
        (insert (((asg env).q ▹ φ)/[nm n])
          (Γ.image (fun ψ => asg env ▹ ψ))) := by
      intro n
      have Dn := ih (n :>ₙ env)
      rw [Finset.image_insert] at Dn
      have hA : asg (n :>ₙ env) ▹ (Rewriting.free φ)
          = ((asg env).q ▹ φ)/[nm n] := by
        have hRew : (asg (n :>ₙ env)).comp Rew.free
            = (Rew.subst ![nm n]).comp (asg env).q := by
          ext x
          · refine Fin.cases ?_ (fun i => Fin.elim0 i) x
            simp [asg, Rew.comp_app, nm]
          · simp [asg, Rew.comp_app, nm]
        show asg (n :>ₙ env) ▹ (Rew.free ▹ φ)
            = Rew.subst ![nm n] ▹ ((asg env).q ▹ φ)
        rw [← TransitiveRewriting.comp_app, ← TransitiveRewriting.comp_app, hRew]
      have hB : (Γ.image Rewriting.shift).image (fun ψ => asg (n :>ₙ env) ▹ ψ)
          = Γ.image (fun ψ => asg env ▹ ψ) := by
        have hcompB : (asg (n :>ₙ env)).comp Rew.shift = asg env := by
          ext x
          · exact Fin.elim0 x
          · simp [asg, Rew.comp_app]
        rw [Finset.image_image]
        refine Finset.image_congr (fun ψ _ => ?_)
        show asg (n :>ₙ env) ▹ (Rew.shift ▹ ψ) = asg env ▹ ψ
        rw [← TransitiveRewriting.comp_app, hcompB]
      rw [hA, hB] at Dn
      have hK : envSup (n :>ₙ env) N ≤ max (envSup env N) n :=
        calc envSup (n :>ₙ env) N
            ≤ envSup (n :>ₙ env) (N + 1) := envSup_mono_N (n :>ₙ env) (Nat.le_succ N)
          _ ≤ max n (envSup env N) := envSup_cons_le env n N
          _ = max (envSup env N) n := Nat.max_comm _ _
      have hff : ∀ x, rel1 (ewRootSlot e B) (envSup (n :>ₙ env) N) x
          ≤ rel1 (rel1 (ewRootSlot e (B + 1)) (envSup env N)) n x := by
        intro x
        rw [rel1_rel1]
        exact relSlot_mono (Nat.le_succ B) hK x
      exact (Dn.change_H).mono_f hff
    have hgate : Nlog (osucc α)
        ≤ rel1 (ewRootSlot e (B + 1)) (envSup env N) 0 := by
      have h1 := Nlog_osucc_le hαNF
      have h2 : (B + 1 : ℕ) ≤ rel1 (ewRootSlot e (B + 1)) (envSup env N) 0 :=
        le_relSlot_zero e (B + 1) (envSup env N)
      omega
    have hrel : ∀ n, relOp (fun _ : ONote => True) n α :=
      fun n => Cl.base (Or.inl trivial)
    have hall := Zef2TC.allω (α := osucc α)
      (f := rel1 (ewRootSlot e (B + 1)) (envSup env N)) hgate
      ((asg env).q ▹ φ) (fun _ => α)
      (fun _ => lt_osucc hαNF) (fun _ => hαNF) (osucc_NF hαNF) hrel hfam
    have hmem : (asg env ▹ (∀⁰ φ))
        ∈ Γ.image (fun ψ => asg env ▹ ψ) := Finset.mem_image_of_mem _ h
    rw [show (asg env ▹ (∀⁰ φ)) = ∀⁰ ((asg env).q ▹ φ) by simp] at hmem
    rw [Finset.insert_eq_self.mpr hmem] at hall
    exact hall

/-- **V3 `and`** — closes `BudgetedEmbedsV3` under `⋏`-introduction from two premises. -/
lemma budgetedEmbedsV3_and {φ ψ : ArithmeticFormula ℕ} (h : φ ⋏ ψ ∈ Γ)
    (ihp : BudgetedEmbedsV3 (insert φ Γ)) (ihq : BudgetedEmbedsV3 (insert ψ Γ)) :
    BudgetedEmbedsV3 Γ := by
  obtain ⟨B₁, d₁, N₁, e₁, α₁, he₁, hα₁NF, hN₁, ih₁⟩ := ihp
  obtain ⟨B₂, d₂, N₂, e₂, α₂, he₂, hα₂NF, hN₂, ih₂⟩ := ihq
  have headdNF : (e₁ + e₂).NF := by haveI := he₁; haveI := he₂; exact ONote.add_nf e₁ e₂
  have heNF : (osucc (e₁ + e₂)).NF := osucc_NF headdNF
  have hlt₁ : e₁ < osucc (e₁ + e₂) :=
    lt_of_le_of_lt (le_add_right_NF he₁ he₂) (lt_osucc headdNF)
  have hlt₂ : e₂ < osucc (e₁ + e₂) :=
    lt_of_le_of_lt (le_add_left_NF he₁ he₂) (lt_osucc headdNF)
  have haddNF : (α₁ + α₂).NF := by haveI := hα₁NF; haveI := hα₂NF; exact ONote.add_nf α₁ α₂
  -- control `osucc (e₁ + e₂)`, root `osucc (α₁ + α₂)`; `B` covers both the `Nlog` invariant and
  -- the `relSlot_le` norm gates, so the root gate is free from the structural invariant
  set B := max B₁ B₂ + norm e₁ + norm e₂ + 2 with hB
  refine ⟨B, max d₁ d₂, max N₁ N₂, osucc (e₁ + e₂), osucc (α₁ + α₂),
    heNF, osucc_NF haddNF, ?_, ?_⟩
  · have hs := Nlog_osucc_le haddNF
    have ha := Nlog_add_le_max_succ α₁ hα₁NF α₂ hα₂NF
    omega
  · intro env
    have hff₁ : ∀ x, rel1 (ewRootSlot e₁ B₁) (envSup env N₁) x
        ≤ rel1 (ewRootSlot (osucc (e₁ + e₂)) B) (envSup env (max N₁ N₂)) x :=
      relSlot_le he₁ heNF hlt₁ (by omega)
        (envSup_mono_N env (le_max_left N₁ N₂)) (by omega)
    have hff₂ : ∀ x, rel1 (ewRootSlot e₂ B₂) (envSup env N₂) x
        ≤ rel1 (ewRootSlot (osucc (e₁ + e₂)) B) (envSup env (max N₁ N₂)) x :=
      relSlot_le he₂ heNF hlt₂ (by omega)
        (envSup_mono_N env (le_max_right N₁ N₂)) (by omega)
    have D₁ := ih₁ env
    have D₂ := ih₂ env
    rw [Finset.image_insert] at D₁ D₂
    have D₁' := ((D₁.change_e (osucc (e₁ + e₂))).mono_f hff₁).mono_c (le_max_left d₁ d₂)
    have D₂' := ((D₂.change_e (osucc (e₁ + e₂))).mono_f hff₂).mono_c (le_max_right d₁ d₂)
    have hg : Nlog (osucc (α₁ + α₂))
        ≤ rel1 (ewRootSlot (osucc (e₁ + e₂)) B) (envSup env (max N₁ N₂)) 0 := by
      have hs := Nlog_osucc_le haddNF
      have ha := Nlog_add_le_max_succ α₁ hα₁NF α₂ hα₂NF
      have hb := le_relSlot_zero (osucc (e₁ + e₂)) B (envSup env (max N₁ N₂))
      omega
    have hand := Zef2TC.andI (α := osucc (α₁ + α₂)) hg
      (asg env ▹ φ) (asg env ▹ ψ)
      (lt_of_le_of_lt (le_add_right_NF hα₁NF hα₂NF) (lt_osucc haddNF))
      (lt_of_le_of_lt (le_add_left_NF hα₁NF hα₂NF) (lt_osucc haddNF))
      hα₁NF hα₂NF (osucc_NF haddNF) (clT α₁) (clT α₂) D₁' D₂'
    have hmem : (asg env ▹ φ ⋏ asg env ▹ ψ)
        ∈ Γ.image (fun χ => asg env ▹ χ) := by
      have := Finset.mem_image_of_mem (fun χ => asg env ▹ χ) h
      simpa using this
    rwa [Finset.insert_eq_self.mpr hmem] at hand

/-- **V3 `cut`** — closes `BudgetedEmbedsV3` under the cut rule for `φ` and `∼φ`. -/
lemma budgetedEmbedsV3_cut {φ : ArithmeticFormula ℕ}
    (ihp : BudgetedEmbedsV3 (insert φ Γ)) (ihn : BudgetedEmbedsV3 (insert (∼φ) Γ)) :
    BudgetedEmbedsV3 Γ := by
  obtain ⟨B₁, d₁, N₁, e₁, α₁, he₁, hα₁NF, hN₁, ih₁⟩ := ihp
  obtain ⟨B₂, d₂, N₂, e₂, α₂, he₂, hα₂NF, hN₂, ih₂⟩ := ihn
  have headdNF : (e₁ + e₂).NF := by haveI := he₁; haveI := he₂; exact ONote.add_nf e₁ e₂
  have heNF : (osucc (e₁ + e₂)).NF := osucc_NF headdNF
  have hlt₁ : e₁ < osucc (e₁ + e₂) :=
    lt_of_le_of_lt (le_add_right_NF he₁ he₂) (lt_osucc headdNF)
  have hlt₂ : e₂ < osucc (e₁ + e₂) :=
    lt_of_le_of_lt (le_add_left_NF he₁ he₂) (lt_osucc headdNF)
  have haddNF : (α₁ + α₂).NF := by haveI := hα₁NF; haveI := hα₂NF; exact ONote.add_nf α₁ α₂
  -- the `and` join, with the cut rank `max`ed against `φ.complexity + 1` and the read gate paid
  -- by absorbing `φ.complexity` into `B` (rewriting preserves `complexity`)
  set B := max B₁ B₂ + norm e₁ + norm e₂ + φ.complexity + 2 with hB
  refine ⟨B, max (max d₁ d₂) (φ.complexity + 1), max N₁ N₂, osucc (e₁ + e₂),
    osucc (α₁ + α₂), heNF, osucc_NF haddNF, ?_, ?_⟩
  · have hs := Nlog_osucc_le haddNF
    have ha := Nlog_add_le_max_succ α₁ hα₁NF α₂ hα₂NF
    omega
  · intro env
    have hff₁ : ∀ x, rel1 (ewRootSlot e₁ B₁) (envSup env N₁) x
        ≤ rel1 (ewRootSlot (osucc (e₁ + e₂)) B) (envSup env (max N₁ N₂)) x :=
      relSlot_le he₁ heNF hlt₁ (by omega)
        (envSup_mono_N env (le_max_left N₁ N₂)) (by omega)
    have hff₂ : ∀ x, rel1 (ewRootSlot e₂ B₂) (envSup env N₂) x
        ≤ rel1 (ewRootSlot (osucc (e₁ + e₂)) B) (envSup env (max N₁ N₂)) x :=
      relSlot_le he₂ heNF hlt₂ (by omega)
        (envSup_mono_N env (le_max_right N₁ N₂)) (by omega)
    have D₁ := ih₁ env
    have D₂ := ih₂ env
    rw [Finset.image_insert] at D₁ D₂
    have D₁' := ((D₁.change_e (osucc (e₁ + e₂))).mono_f hff₁).mono_c
      (c' := max (max d₁ d₂) (φ.complexity + 1))
      (le_trans (le_max_left d₁ d₂) (le_max_left _ _))
    have D₂' := ((D₂.change_e (osucc (e₁ + e₂))).mono_f hff₂).mono_c
      (c' := max (max d₁ d₂) (φ.complexity + 1))
      (le_trans (le_max_right d₁ d₂) (le_max_left _ _))
    rw [show asg env ▹ (∼φ) = ∼(asg env ▹ φ) by simp] at D₂'
    have hb := le_relSlot_zero (osucc (e₁ + e₂)) B (envSup env (max N₁ N₂))
    have hg : Nlog (osucc (α₁ + α₂))
        ≤ rel1 (ewRootSlot (osucc (e₁ + e₂)) B) (envSup env (max N₁ N₂)) 0 := by
      have hs := Nlog_osucc_le haddNF
      have ha := Nlog_add_le_max_succ α₁ hα₁NF α₂ hα₂NF
      omega
    have hread : (asg env ▹ φ).complexity
        ≤ rel1 (ewRootSlot (osucc (e₁ + e₂)) B) (envSup env (max N₁ N₂)) 0 := by
      simp only [Semiformula.complexity_rew]
      omega
    have hcompl : (asg env ▹ φ).complexity
        < max (max d₁ d₂) (φ.complexity + 1) := by
      simp only [Semiformula.complexity_rew]
      omega
    exact Zef2TC.cut hg (asg env ▹ φ) hcompl hread
      (lt_of_le_of_lt (le_add_right_NF hα₁NF hα₂NF) (lt_osucc haddNF))
      (lt_of_le_of_lt (le_add_left_NF hα₁NF hα₂NF) (lt_osucc haddNF))
      hα₁NF hα₂NF (osucc_NF haddNF) (clT α₁) (clT α₂) D₁' D₂'

/-- **V3 `exs`** — closes `BudgetedEmbedsV3` under ∃-introduction for `∃⁰ φ` with a structural
witness budget. -/
lemma budgetedEmbedsV3_exs {φ : ArithmeticSemiformula ℕ 1} (h : ∃⁰ φ ∈ Γ) (t : ArithmeticTerm ℕ)
    (ih : BudgetedEmbedsV3 (insert (φ/[t]) Γ)) :
    BudgetedEmbedsV3 Γ := by
  obtain ⟨B₁, d₁, N₁, e₁, α₁, he₁, hα₁NF, hN₁, ih₁⟩ := ih
  obtain ⟨c, Nt, hdom⟩ := stdClosedVal_asg_le_Gexp_iter t
  -- the witness `m = stdClosedVal (asg env t)` is env-dependent, but bounded by
  -- `Gexp^[c] (envSup env Nt)` with structural `(c, Nt)`; the Gexp control tower `ω²·(c+1)` and
  -- the joined control `e` absorb the iterate into a single Hardy value dominated by the root slot
  set c' : ℕ+ := ⟨c + 1, Nat.succ_pos c⟩ with hc'
  set eG : ONote := ONote.oadd (ONote.ofNat 2) c' 0 with heG
  have heGNF : eG.NF := (ONote.nf_ofNat 2).oadd c' ONote.NFBelow.zero
  have headdNF : (e₁ + eG).NF := by haveI := he₁; haveI := heGNF; exact ONote.add_nf e₁ eG
  have heNF : (osucc (e₁ + eG)).NF := osucc_NF headdNF
  set e : ONote := osucc (e₁ + eG) with he
  have hlt₁ : e₁ < e :=
    lt_of_le_of_lt (le_add_right_NF he₁ heGNF) (lt_osucc headdNF)
  have hltG : eG < e :=
    lt_of_le_of_lt (le_add_left_NF he₁ heGNF) (lt_osucc headdNF)
  set B : ℕ := B₁ + φ.complexity + clog (2 * φ.complexity + 1)
    + norm e₁ + norm eG + 3 with hB
  set d : ℕ := max d₁ (φ.complexity + 1) with hd
  set N : ℕ := max N₁ Nt with hN
  have hofNF : (ONote.ofNat (2 * φ.complexity + 1)).NF := ONote.nf_ofNat _
  have haddNF : (α₁ + ONote.ofNat (2 * φ.complexity + 1)).NF := by
    haveI := hα₁NF; haveI := hofNF; exact ONote.add_nf _ _
  refine ⟨B, d, N, e, osucc (osucc (α₁ + ONote.ofNat (2 * φ.complexity + 1))),
    heNF, osucc_NF (osucc_NF haddNF), ?_, ?_⟩
  · -- the structural `Nlog` invariant at the doubled-osucc root
    have h1 := Nlog_osucc_le (osucc_NF haddNF)
    have h2 := Nlog_osucc_le haddNF
    have h3 := Nlog_add_le_max_succ α₁ hα₁NF _ hofNF
    have h4 := Nlog_ofNat_le (2 * φ.complexity + 1)
    omega
  · intro env
    set M : ℕ := envSup env N with hM
    set F : ℕ → ℕ := rel1 (ewRootSlot e B) M with hF
    set ψ' : ArithmeticSemiformula ℕ 1 := (asg env).q ▹ φ with hψ'
    set s : ArithmeticTerm ℕ := asg env t with hs
    set m : ℕ := stdClosedVal s with hm
    have hψc : ψ'.complexity = φ.complexity := by simp [hψ']
    have hf1 := ewRootSlot_f1 e B
    have hFmono : Monotone F := rel1_monotone hf1.1.monotone M
    have hFinfl : ∀ x, x ≤ F x := rel1_infl (fun x => by have := hf1.2 x; omega) M
    have hBF : B ≤ F 0 := le_relSlot_zero e B M
    -- the IH derivation, re-based to the joined control/budgets
    have D₁ := ih₁ env
    rw [Finset.image_insert, rew_subst_term (asg env) φ t] at D₁
    have hff : ∀ x, rel1 (ewRootSlot e₁ B₁) (envSup env N₁) x ≤ F x :=
      relSlot_le he₁ heNF hlt₁ (by omega)
        (envSup_mono_N env (le_max_left N₁ Nt)) (by omega)
    have D₁' := ((D₁.change_e e).mono_f hff).mono_c (c' := d) (le_max_left _ _)
    -- left cut premise: add ψ'/[nm m] to the context
    have Dsrc : Zef2TC α₁ e (fun _ => True) F d
        (insert (ψ'/[s]) (insert (ψ'/[nm m])
          (Γ.image (fun χ => asg env ▹ χ)))) :=
      D₁'.wk D₁'.gate (Finset.insert_subset_insert _ (Finset.subset_insert _ _))
    -- right cut premise: value-congruent EM at the pair (nm m, s)
    have hgateEM : clog (2 * ψ'.complexity + 1) ≤ F 0 := by rw [hψc]; omega
    have Dcong : Zef2TC (ONote.ofNat (2 * ψ'.complexity + 1)) e (fun _ => True) F 0
        (insert (∼(ψ'/[s])) (insert (ψ'/[nm m])
          (Γ.image (fun χ => asg env ▹ χ)))) := by
      refine em_cong1_Zef2TC (nm m) s (by simp [hm]) ψ' hFmono hFinfl hgateEM ?_ ?_
      · exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
      · exact Finset.mem_insert_self _ _
    have Dcong' := Dcong.mono_c (c' := d) (Nat.zero_le d)
    -- the cut, at root `osucc (α₁ + ofNat (2·complexity+1))`; gate free from `B`
    have hgcut : Nlog (osucc (α₁ + ONote.ofNat (2 * φ.complexity + 1))) ≤ F 0 := by
      have h2 := Nlog_osucc_le haddNF
      have h3 := Nlog_add_le_max_succ α₁ hα₁NF _ hofNF
      have h4 := Nlog_ofNat_le (2 * φ.complexity + 1)
      omega
    have hcompl : (ψ'/[s]).complexity < d := by
      have : (ψ'/[s]).complexity = φ.complexity := by simp [hψ']
      omega
    have hread : (ψ'/[s]).complexity ≤ F 0 := by
      have hc : (ψ'/[s]).complexity = φ.complexity := by simp [hψ']
      omega
    have hψof : ONote.ofNat (2 * ψ'.complexity + 1)
        = ONote.ofNat (2 * φ.complexity + 1) := by rw [hψc]
    rw [hψof] at Dcong'
    have Dnum : Zef2TC (osucc (α₁ + ONote.ofNat (2 * φ.complexity + 1))) e
        (fun _ => True) F d
        (insert (ψ'/[nm m]) (Γ.image (fun χ => asg env ▹ χ))) :=
      Zef2TC.cut hgcut (ψ'/[s]) hcompl hread
        (lt_of_le_of_lt (le_add_right_NF hα₁NF hofNF) (lt_osucc haddNF))
        (lt_of_le_of_lt (le_add_left_NF hα₁NF hofNF) (lt_osucc haddNF))
        hα₁NF hofNF (osucc_NF haddNF) (clT _) (clT _) Dsrc Dcong'
    -- THE structural witness bound: `m ≤ Gexp^[c] ≤ hardy eG ≤ hardy e ≤ F 0`
    have hwit : m ≤ F 0 := by
      have s1 : m ≤ Gexp^[c] (envSup env Nt) := hdom env
      have s2 : Gexp^[c] (envSup env Nt) ≤ Gexp^[c] M :=
        Gexp_iter_monotone c (envSup_mono_N env (le_max_right N₁ Nt))
      have s3 : Gexp^[c] M ≤ Gexp^[c + 1] M := Gexp_iter_le_iter (Nat.le_succ c) M
      have s4 : Gexp^[c + 1] M = hardy eG M := Gexp_iter_eq_hardy c' M
      have s5 : hardy eG M ≤ hardy eG (max B (max M 0)) :=
        hardy_monotone eG (le_trans (le_max_left M 0) (le_max_right B _))
      have s6 : hardy eG (max B (max M 0)) ≤ hardy e (max B (max M 0)) :=
        hardy_le_of_lt heGNF heNF hltG (le_trans (by omega) (le_max_left B _))
      have s7 : hardy e (max B (max M 0)) ≤ F 0 := by
        simp only [hF, rel1, ewRootSlot]
        omega
      omega
    -- the ∃-introduction at the numeral witness `m`
    have hgout : Nlog (osucc (osucc (α₁ + ONote.ofNat (2 * φ.complexity + 1)))) ≤ F 0 := by
      have h1 := Nlog_osucc_le (osucc_NF haddNF)
      have h2 := Nlog_osucc_le haddNF
      have h3 := Nlog_add_le_max_succ α₁ hα₁NF _ hofNF
      have h4 := Nlog_ofNat_le (2 * φ.complexity + 1)
      omega
    have hexI := Zef2TC.exI
      (α := osucc (osucc (α₁ + ONote.ofNat (2 * φ.complexity + 1))))
      hgout ψ' m
      (lt_osucc (osucc_NF haddNF)) (osucc_NF haddNF)
      (osucc_NF (osucc_NF haddNF)) (clT _) hwit Dnum
    have hmem : (∃⁰ ψ') ∈ Γ.image (fun χ => asg env ▹ χ) := by
      have := Finset.mem_image_of_mem (fun χ => asg env ▹ χ) h
      simpa [hψ'] using this
    rwa [Finset.insert_eq_self.mpr hmem] at hexI

end GoodsteinPA.E1EmbeddingGrind
