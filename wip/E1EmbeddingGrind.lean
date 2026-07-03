import GoodsteinPA.OperatorZef2
import GoodsteinPA.WainerRoute

/-!
# E-1 grind (Series-3) — `Zef2TC` (full E–W Def-23 rule set) + the budgeted EM lemma

Per the E-1 block-1 finding (`wip/E0Ax2NeedProbe.lean` § E-1 seam probe): `Zef2T` lacks the
connective rules the PA-proof embedding needs (`{⊤}` kernel-underivable even with (Ax2)).  This
file erects the AMENDED target calculus — **`Zef2TC` = `Zef2` + (Ax2) `trueRel`/`trueNrel` +
the finite `verumR`/`andI`/`orI`** (the `Zekd` shapes with the `Nlog` gate + `Cl`-operator
side conditions threaded, mirroring `weak`/`exI`) — and banks the first E–W Lemma-32 mechanism:

* `em_Zef2TC` — the **budgeted excluded middle** (the W3 `closed` case engine): any sequent
  containing `φ, ∼φ` is `Zef2TC`-derivable cut-free at the DETERMINISTIC ordinal
  `ofNat (2·complexity + 1)`, any slot `f` that is monotone + inflationary with
  `clog (2·complexity+1) ≤ f 0`.  Mirrors `Embedding.lean`'s `provable_em` with the full
  gate/ordinal bookkeeping; the ∀/∃ cases pair `allω` branches with `exI` at witness `n`
  (bound `n ≤ rel1 f n 0 = f n` — inflationarity), the finite cases ride `andI`/`orI`.

Everything here is wip-only ruling input (the `Zef2TC` amendment is flagged for the judge in
ledger block 6, NOT self-ratified); statements are new-machinery lemmas, not rung texts.  The
amended DRAFT `embedding_Zef2TC_DRAFT` re-bases the E-0 draft verbatim onto `Zef2TC`.
-/

namespace GoodsteinPA.E1EmbeddingGrind

open LO LO.FirstOrder ONote Ordinal
open GoodsteinPA.FastGrowing
open GoodsteinPA.OperatorZeh GoodsteinPA.OperatorZinfty

/-! ## `Zef2TC` — the full-rule-set target calculus -/

/-- **`Zef2TC`** — `Zef2` (verbatim, `Nlog` gates) + E–W (Ax2) (`trueRel`/`trueNrel`) + the
finite connective rules `verumR`/`andI`/`orI` (`Zekd` shapes; ordinal-descending premises with
the `weak`-style NF/`Cl` side conditions; slot UNCHANGED — E–W relativizes only the ω-rule). -/
inductive Zef2TC : ONote → ONote → (ONote → Prop) → (ℕ → ℕ) → ℕ → Seq → Prop
  | axL {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Seq} {ar : ℕ}
      (hαN : Nlog α ≤ f 0)
      (r : (ℒₒᵣ).Rel ar) (v) (hp : Semiformula.rel r v ∈ Γ)
      (hn : Semiformula.nrel r v ∈ Γ) : Zef2TC α e H f c Γ
  | trueRel {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Seq} {ar : ℕ}
      (hαN : Nlog α ≤ f 0)
      (r : (ℒₒᵣ).Rel ar) (v) (htrue : atomTrue (Semiformula.rel r v))
      (hmem : Semiformula.rel r v ∈ Γ) : Zef2TC α e H f c Γ
  | trueNrel {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Seq} {ar : ℕ}
      (hαN : Nlog α ≤ f 0)
      (r : (ℒₒᵣ).Rel ar) (v) (htrue : atomTrue (Semiformula.nrel r v))
      (hmem : Semiformula.nrel r v ∈ Γ) : Zef2TC α e H f c Γ
  | verumR {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Seq}
      (hαN : Nlog α ≤ f 0) (h : (⊤ : Form) ∈ Γ) : Zef2TC α e H f c Γ
  | wk {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Δ Γ : Seq}
      (hαN : Nlog α ≤ f 0) (hsub : Δ ⊆ Γ) (dd : Zef2TC α e H f c Δ) :
      Zef2TC α e H f c Γ
  | weak {α β e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Δ Γ : Seq}
      (hαN : Nlog α ≤ f 0)
      (hβ : β < α) (hβNF : β.NF) (hαNF : α.NF) (hβH : Cl H β)
      (hsub : Δ ⊆ Γ) (dd : Zef2TC β e H f c Δ) : Zef2TC α e H f c Γ
  | andI {α βφ βψ e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Seq}
      (hαN : Nlog α ≤ f 0)
      (φ ψ : Form) (hβφ : βφ < α) (hβψ : βψ < α)
      (hβφNF : βφ.NF) (hβψNF : βψ.NF) (hαNF : α.NF)
      (hβφH : Cl H βφ) (hβψH : Cl H βψ)
      (dφ : Zef2TC βφ e H f c (insert φ Γ)) (dψ : Zef2TC βψ e H f c (insert ψ Γ)) :
      Zef2TC α e H f c (insert (φ ⋏ ψ) Γ)
  | orI {α β e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Seq}
      (hαN : Nlog α ≤ f 0)
      (φ ψ : Form) (hβ : β < α) (hβNF : β.NF) (hαNF : α.NF) (hβH : Cl H β)
      (dd : Zef2TC β e H f c (insert φ (insert ψ Γ))) :
      Zef2TC α e H f c (insert (φ ⋎ ψ) Γ)
  | allω {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Seq}
      (hαN : Nlog α ≤ f 0)
      (φ : SyntacticSemiformula ℒₒᵣ 1) (β : ℕ → ONote)
      (hβ : ∀ n, β n < α) (hβNF : ∀ n, (β n).NF) (hαNF : α.NF)
      (hβH : ∀ n, relOp H n (β n))
      (dd : ∀ n, Zef2TC (β n) e (adjoin H n) (rel1 f n) c (insert (φ/[nm n]) Γ)) :
      Zef2TC α e H f c (insert (∀⁰ φ) Γ)
  | exI {α β e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Seq}
      (hαN : Nlog α ≤ f 0)
      (φ : SyntacticSemiformula ℒₒᵣ 1) (n : ℕ) (hβ : β < α)
      (hβNF : β.NF) (hαNF : α.NF) (hβH : Cl H β) (hbound : n ≤ f 0)
      (dd : Zef2TC β e H f c (insert (φ/[nm n]) Γ)) : Zef2TC α e H f c (insert (∃⁰ φ) Γ)
  | cut {α βφ βψ e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Seq}
      (hαN : Nlog α ≤ f 0)
      (φ : Form) (hcompl : φ.complexity < c) (hcutRead : φ.complexity ≤ f 0)
      (hβφ : βφ < α) (hβψ : βψ < α)
      (hβφNF : βφ.NF) (hβψNF : βψ.NF) (hαNF : α.NF)
      (hβφH : Cl H βφ) (hβψH : Cl H βψ)
      (d₁ : Zef2TC βφ e H f c (insert φ Γ)) (d₂ : Zef2TC βψ e H f c (insert (∼φ) Γ)) :
      Zef2TC α e H f c Γ

namespace Zef2TC

theorem gate {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Seq}
    (dd : Zef2TC α e H f c Γ) : Nlog α ≤ f 0 := by
  cases dd <;> assumption

/-- `Zef2 ⊆ Zef2TC`. -/
theorem ofZef2 : ∀ {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Seq},
    Zef2 α e H f c Γ → Zef2TC α e H f c Γ := by
  intro α e H f c Γ dd
  induction dd with
  | axL hαN r v hp hn => exact Zef2TC.axL hαN r v hp hn
  | wk hαN hsub _ ih => exact Zef2TC.wk hαN hsub ih
  | weak hαN hβ hβNF hαNF hβH hsub _ ih => exact Zef2TC.weak hαN hβ hβNF hαNF hβH hsub ih
  | allω hαN φ β hβ hβNF hαNF hβH _ ih => exact Zef2TC.allω hαN φ β hβ hβNF hαNF hβH ih
  | exI hαN φ n hβ hβNF hαNF hβH hbound _ ih =>
      exact Zef2TC.exI hαN φ n hβ hβNF hαNF hβH hbound ih
  | cut hαN φ hcompl hcutRead hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH _ _ ih₁ ih₂ =>
      exact Zef2TC.cut hαN φ hcompl hcutRead hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH ih₁ ih₂

end Zef2TC

/-! ## Ordinal-ladder toolkit (`ofNat` rungs) -/

theorem ofNat_lt_ofNat {a b : ℕ} (h : a < b) : ONote.ofNat a < ONote.ofNat b := by
  rw [ONote.lt_def, ONote.repr_ofNat, ONote.repr_ofNat]
  exact_mod_cast h

theorem Nlog_ofNat_le (m : ℕ) : Nlog (ONote.ofNat m) ≤ clog m := by
  cases m with
  | zero => simp
  | succ k =>
      rw [show ONote.ofNat (k + 1) = ONote.oadd 0 k.succPNat 0 from rfl]
      simp [Nat.succPNat]

theorem clog_mono {a b : ℕ} (h : a ≤ b) : clog a ≤ clog b :=
  Nat.log_mono_right (by omega)

/-! ## The budgeted excluded middle (E–W Lemma 32 / the W3 `closed`-case engine) -/

/-- **Budgeted EM**: a sequent containing `φ, ∼φ` is cut-free `Zef2TC`-derivable at the
deterministic ordinal rung `ofNat (2k+1)` (`k ≥ complexity φ`), for ANY slot `f` monotone +
inflationary with `clog (2k+1) ≤ f 0`.  All hypotheses are `rel1`-stable, so the ω-cases
recurse at the relativized slots.  Mirrors `provable_em` (`Embedding.lean:71`). -/
theorem em_Zef2TC (k : ℕ) :
    ∀ (φ : Form), φ.complexity ≤ k →
    ∀ {e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {Γ : Seq},
      Monotone f → (∀ m, m ≤ f m) → clog (2 * k + 1) ≤ f 0 →
      φ ∈ Γ → ∼φ ∈ Γ → Zef2TC (ONote.ofNat (2 * k + 1)) e H f 0 Γ := by
  induction k with
  | zero =>
    intro φ hk e H f Γ hmono hinfl hgate hp hn
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
    intro φ hk e H f Γ hmono hinfl hgate hp hn
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
theorem em_Zef2TC' (φ : Form) {e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {Γ : Seq}
    (hmono : Monotone f) (hinfl : ∀ m, m ≤ f m)
    (hgate : clog (2 * φ.complexity + 1) ≤ f 0)
    (hp : φ ∈ Γ) (hn : ∼φ ∈ Γ) :
    Zef2TC (ONote.ofNat (2 * φ.complexity + 1)) e H f 0 Γ :=
  em_Zef2TC φ.complexity φ le_rfl hmono hinfl hgate hp hn

/-! ## The AMENDED rung-E statement DRAFT (block-6 amendment applied) -/

/-- The goodstein Π₂ body (as in `wip/E0Ax2NeedProbe.lean`). -/
noncomputable def goodsteinBody : Semisentence ℒₒᵣ 1 :=
  “∃ N, !LO.FirstOrder.Arithmetic.igoodsteinDef 0 #1 N”

theorem goodsteinSentence_eq_all_body :
    GoodsteinPA.goodsteinSentence = ∀⁰ goodsteinBody := rfl

noncomputable def goodsteinBodyE : SyntacticSemiformula ℒₒᵣ 1 :=
  Rewriting.emb goodsteinBody

/-- **DRAFT (E-1 amendment of the E-0 draft; NOT ratified — DO NOT port to src).**  Identical
to `embedding_Zef2T_DRAFT` (`wip/E0Ax2NeedProbe.lean`) with the sole change `Zef2T → Zef2TC`
(the connective-rule amendment, forced by `zef2T_not_derives_verum`). -/
theorem embedding_Zef2TC_DRAFT :
    (𝗣𝗔 ⊢ ↑GoodsteinPA.goodsteinSentence) →
      ∃ B d : ℕ, ∃ e : ONote, e.NF ∧ ∀ m : ℕ, ∃ α : ONote, α.NF ∧ ∃ H : ONote → Prop,
        Cl H α ∧ Zef2TC α e H (ewRootSlot e B) d {(goodsteinBodyE/[nm m])} := by
  sorry

end GoodsteinPA.E1EmbeddingGrind
