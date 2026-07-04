import GoodsteinPA.OperatorZef2
import GoodsteinPA.WainerRoute
import GoodsteinPA.Embedding
import GoodsteinPA.InternalBridge
import GoodsteinPA.ReadoffValueGate
import GoodsteinPA.Compat

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

/- **DRAFT (E-1 amendment of the E-0 draft) — RETIRED (SERIES-5 Lane C).**  The fixed-root-slot
draft was superseded by the ratified `embedding_Zef2TC_V3` (env-local `∃ K` relativization); it had
no code consumers and its `sorry` was decorative judge-input only. Deleted to reach `src` sorry-free.
The ratified statement lives at `embedding_Zef2TC_V3` below. -/

/-! ## E-1 block 3 — monotonicity ports, the slot toolkit, and the case ladder

### The block-3 STATEMENT discovery (amendment input for the judge)

The E-0/E-1 DRAFT's **fixed root slot cannot pay the `exI` gate**: `Zef2TC.exI` demands the
witness numeral `n ≤ f 0`, and in the `Derivation2` `exs` case the witness value
`(asg env) t` is **env-dependent and unbounded** while `f = ewRootSlot e B` is structural
(chosen before `∀ env`).  Concretely, at the root the DRAFT's conclusion sequent
`{goodsteinBodyE/[nm m]}` is a Σ₁ instance whose only introduction rule is `exI` at the true
goodstein witness `N(m)` — unbounded in `m` — so the fixed-slot DRAFT is unprovable as stated
(and morally false).  This is exactly the seam the W3 verdict solved in `ZekdSomeK` with the
env-local `∃ K` witness budget; the fix here is the same discipline transplanted to the slot:
the master predicate carries an **env-local relativization index `K`** and runs the derivation
at slot `rel1 (ewRootSlot e B) K`.  `rel1`-slots compose with the ω-rule
(`rel1_rel1 : rel1 (rel1 f m) n = rel1 f (max m n)`) and keep `EwF1`/`EwF2` (`rel1_low`), so
the downstream pass/read-off pipeline is undisturbed.  `embedding_Zef2TC_DRAFT2` below is the
so-amended rung-E statement (the DRAFT above is retained verbatim as the flagged judge input).
-/

namespace Zef2TC

/-- Slot monotonicity (port of `Zef2.mono_f` over the full rule set). -/
theorem mono_f : ∀ {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Seq},
    Zef2TC α e H f c Γ → ∀ {f' : ℕ → ℕ}, (∀ x, f x ≤ f' x) → Zef2TC α e H f' c Γ := by
  intro α e H f c Γ dd
  induction dd with
  | axL hαN r v hp hn =>
      intro f' hff'; exact .axL (le_trans hαN (hff' 0)) r v hp hn
  | trueRel hαN r v htrue hmem =>
      intro f' hff'; exact .trueRel (le_trans hαN (hff' 0)) r v htrue hmem
  | trueNrel hαN r v htrue hmem =>
      intro f' hff'; exact .trueNrel (le_trans hαN (hff' 0)) r v htrue hmem
  | verumR hαN h => intro f' hff'; exact .verumR (le_trans hαN (hff' 0)) h
  | wk hαN hsub _ ih => intro f' hff'; exact .wk (le_trans hαN (hff' 0)) hsub (ih hff')
  | weak hαN hβ hβNF hαNF hβH hsub _ ih =>
      intro f' hff'; exact .weak (le_trans hαN (hff' 0)) hβ hβNF hαNF hβH hsub (ih hff')
  | andI hαN φ ψ hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH _ _ ih₁ ih₂ =>
      intro f' hff'
      exact .andI (le_trans hαN (hff' 0)) φ ψ hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH
        (ih₁ hff') (ih₂ hff')
  | orI hαN φ ψ hβ hβNF hαNF hβH _ ih =>
      intro f' hff'; exact .orI (le_trans hαN (hff' 0)) φ ψ hβ hβNF hαNF hβH (ih hff')
  | allω hαN φ β hβ hβNF hαNF hβH _ ih =>
      intro f' hff'
      exact .allω (le_trans hαN (hff' 0)) φ β hβ hβNF hαNF hβH
        (fun n => ih n (rel1_mono hff' n))
  | exI hαN φ n hβ hβNF hαNF hβH hbound _ ih =>
      intro f' hff'
      exact .exI (le_trans hαN (hff' 0)) φ n hβ hβNF hαNF hβH
        (le_trans hbound (hff' 0)) (ih hff')
  | cut hαN φ hcompl hcutRead hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH _ _ ih₁ ih₂ =>
      intro f' hff'
      exact .cut (le_trans hαN (hff' 0)) φ hcompl (le_trans hcutRead (hff' 0))
        hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH (ih₁ hff') (ih₂ hff')

/-- Cut-rank monotonicity (only `cut` mentions `c`). -/
theorem mono_c : ∀ {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Seq},
    Zef2TC α e H f c Γ → ∀ {c' : ℕ}, c ≤ c' → Zef2TC α e H f c' Γ := by
  intro α e H f c Γ dd
  induction dd with
  | axL hαN r v hp hn => intro c' _; exact .axL hαN r v hp hn
  | trueRel hαN r v htrue hmem => intro c' _; exact .trueRel hαN r v htrue hmem
  | trueNrel hαN r v htrue hmem => intro c' _; exact .trueNrel hαN r v htrue hmem
  | verumR hαN h => intro c' _; exact .verumR hαN h
  | wk hαN hsub _ ih => intro c' hcc; exact .wk hαN hsub (ih hcc)
  | weak hαN hβ hβNF hαNF hβH hsub _ ih =>
      intro c' hcc; exact .weak hαN hβ hβNF hαNF hβH hsub (ih hcc)
  | andI hαN φ ψ hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH _ _ ih₁ ih₂ =>
      intro c' hcc
      exact .andI hαN φ ψ hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH (ih₁ hcc) (ih₂ hcc)
  | orI hαN φ ψ hβ hβNF hαNF hβH _ ih =>
      intro c' hcc; exact .orI hαN φ ψ hβ hβNF hαNF hβH (ih hcc)
  | allω hαN φ β hβ hβNF hαNF hβH _ ih =>
      intro c' hcc; exact .allω hαN φ β hβ hβNF hαNF hβH (fun n => ih n hcc)
  | exI hαN φ n hβ hβNF hαNF hβH hbound _ ih =>
      intro c' hcc; exact .exI hαN φ n hβ hβNF hαNF hβH hbound (ih hcc)
  | cut hαN φ hcompl hcutRead hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH _ _ ih₁ ih₂ =>
      intro c' hcc
      exact .cut hαN φ (lt_of_lt_of_le hcompl hcc) hcutRead hβφ hβψ hβφNF hβψNF hαNF
        hβφH hβψH (ih₁ hcc) (ih₂ hcc)

/-- Operator swap (port of `Zef2.change_H`; `Cl_of_NF` supplies every `Cl` obligation). -/
theorem change_H : ∀ {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Seq},
    Zef2TC α e H f c Γ → ∀ {H' : ONote → Prop}, Zef2TC α e H' f c Γ := by
  intro α e H f c Γ dd
  induction dd with
  | axL hαN r v hp hn => intro H'; exact .axL hαN r v hp hn
  | trueRel hαN r v htrue hmem => intro H'; exact .trueRel hαN r v htrue hmem
  | trueNrel hαN r v htrue hmem => intro H'; exact .trueNrel hαN r v htrue hmem
  | verumR hαN h => intro H'; exact .verumR hαN h
  | wk hαN hsub _ ih => intro H'; exact .wk hαN hsub ih
  | weak hαN hβ hβNF hαNF _ hsub _ ih =>
      intro H'; exact .weak hαN hβ hβNF hαNF (Cl_of_NF hβNF) hsub ih
  | andI hαN φ ψ hβφ hβψ hβφNF hβψNF hαNF _ _ _ _ ih₁ ih₂ =>
      intro H'
      exact .andI hαN φ ψ hβφ hβψ hβφNF hβψNF hαNF (Cl_of_NF hβφNF) (Cl_of_NF hβψNF) ih₁ ih₂
  | orI hαN φ ψ hβ hβNF hαNF _ _ ih =>
      intro H'; exact .orI hαN φ ψ hβ hβNF hαNF (Cl_of_NF hβNF) ih
  | allω hαN φ β hβ hβNF hαNF _ _ ih =>
      intro H'
      exact .allω hαN φ β hβ hβNF hαNF (fun n => Cl_of_NF (hβNF n)) (fun n => ih n)
  | exI hαN φ n hβ hβNF hαNF _ hbound _ ih =>
      intro H'; exact .exI hαN φ n hβ hβNF hαNF (Cl_of_NF hβNF) hbound ih
  | cut hαN φ hcompl hcutRead hβφ hβψ hβφNF hβψNF hαNF _ _ _ _ ih₁ ih₂ =>
      intro H'
      exact .cut hαN φ hcompl hcutRead hβφ hβψ hβφNF hβψNF hαNF
        (Cl_of_NF hβφNF) (Cl_of_NF hβψNF) ih₁ ih₂

/-- Control-ordinal swap: `e` is a phantom index of the derivation relation (no rule inspects
it), so a derivation transports to ANY control ordinal.  (The control ordinal only acquires
meaning in the cut-elimination pass, where it drives the `ewIter`/`hardy` slot arithmetic.) -/
theorem change_e : ∀ {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Seq},
    Zef2TC α e H f c Γ → ∀ (e' : ONote), Zef2TC α e' H f c Γ := by
  intro α e H f c Γ dd
  induction dd with
  | axL hαN r v hp hn => intro e'; exact .axL hαN r v hp hn
  | trueRel hαN r v htrue hmem => intro e'; exact .trueRel hαN r v htrue hmem
  | trueNrel hαN r v htrue hmem => intro e'; exact .trueNrel hαN r v htrue hmem
  | verumR hαN h => intro e'; exact .verumR hαN h
  | wk hαN hsub _ ih => intro e'; exact .wk hαN hsub (ih e')
  | weak hαN hβ hβNF hαNF hβH hsub _ ih =>
      intro e'; exact .weak hαN hβ hβNF hαNF hβH hsub (ih e')
  | andI hαN φ ψ hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH _ _ ih₁ ih₂ =>
      intro e'
      exact .andI hαN φ ψ hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH (ih₁ e') (ih₂ e')
  | orI hαN φ ψ hβ hβNF hαNF hβH _ ih =>
      intro e'; exact .orI hαN φ ψ hβ hβNF hαNF hβH (ih e')
  | allω hαN φ β hβ hβNF hαNF hβH _ ih =>
      intro e'; exact .allω hαN φ β hβ hβNF hαNF hβH (fun n => ih n e')
  | exI hαN φ n hβ hβNF hαNF hβH hbound _ ih =>
      intro e'; exact .exI hαN φ n hβ hβNF hαNF hβH hbound (ih e')
  | cut hαN φ hcompl hcutRead hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH _ _ ih₁ ih₂ =>
      intro e'
      exact .cut hαN φ hcompl hcutRead hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH (ih₁ e') (ih₂ e')

end Zef2TC

/-! ### `Nlog`/slot toolkit for the ordinal joins -/

/-- `Nlog` is near-stable under `osucc` (mirror of `ewN_osucc_le`). -/
theorem Nlog_osucc_le : ∀ {o : ONote}, o.NF → Nlog (osucc o) ≤ Nlog o + 1
  | 0, _ => by
      show Nlog (oadd 0 1 0) ≤ Nlog 0 + 1
      simp only [Nlog_oadd, Nlog_zero, PNat.one_coe]
      have : clog 1 = 1 := by decide
      omega
  | oadd 0 n a, h => by
      have ha0 : a = 0 := by
        have hlt : a.repr < ω ^ (0 : ONote).repr := h.snd'.repr_lt
        rw [ONote.repr_zero, Ordinal.opow_zero] at hlt
        exact (@ONote.repr_inj a 0 h.snd ONote.NF.zero).1
          (by rw [ONote.repr_zero]; exact Order.lt_one_iff.1 hlt)
      subst ha0
      show Nlog (oadd 0 (n + 1) 0) ≤ Nlog (oadd 0 n 0) + 1
      have hadd := clog_add_le (n : ℕ) 1
      have hpos := clog_pos n
      have h1 : clog 1 = 1 := by decide
      simp only [Nlog_oadd, Nlog_zero, PNat.add_coe, PNat.one_coe, Nat.zero_add]
      omega
  | oadd (oadd e' n' a') m b, h => by
      show Nlog (oadd (oadd e' n' a') m (osucc b)) ≤ Nlog (oadd (oadd e' n' a') m b) + 1
      have hIH := Nlog_osucc_le h.snd
      simp only [Nlog_oadd] at hIH ⊢
      omega

/-- The `K`-relativized root slot dominates a smaller-budget one: `e₁ < e` (with
`norm e₁ ≤ B`), `B₁ ≤ B`, `K₁ ≤ K` give pointwise domination.  The `norm e₁ ≤ B`
side condition is exactly `hardy_le_of_lt`'s budget gate, absorbed into the structural `B`. -/
theorem relSlot_le {e₁ e : ONote} (he₁ : e₁.NF) (he : e.NF) (hlt : e₁ < e)
    {B₁ B K₁ K : ℕ} (hB : B₁ ≤ B) (hK : K₁ ≤ K) (hnorm : norm e₁ ≤ B) (x : ℕ) :
    rel1 (ewRootSlot e₁ B₁) K₁ x ≤ rel1 (ewRootSlot e B) K x := by
  simp only [rel1, ewRootSlot]
  have harg : max B₁ (max K₁ x) ≤ max B (max K x) :=
    max_le_max hB (max_le_max hK le_rfl)
  have h1 : hardy e₁ (max B₁ (max K₁ x)) ≤ hardy e₁ (max B (max K x)) :=
    hardy_monotone e₁ harg
  have h2 : hardy e₁ (max B (max K x)) ≤ hardy e (max B (max K x)) :=
    hardy_le_of_lt he₁ he hlt (le_trans hnorm (le_max_left _ _))
  have h3 : max K₁ x ≤ max K x := max_le_max hK le_rfl
  omega

/-- Same-`e` slot monotonicity in `(B, K)`. -/
theorem relSlot_mono {e : ONote} {B₁ B K₁ K : ℕ} (hB : B₁ ≤ B) (hK : K₁ ≤ K) (x : ℕ) :
    rel1 (ewRootSlot e B₁) K₁ x ≤ rel1 (ewRootSlot e B) K x := by
  simp only [rel1, ewRootSlot]
  have h1 : hardy e (max B₁ (max K₁ x)) ≤ hardy e (max B (max K x)) :=
    hardy_monotone e (max_le_max hB (max_le_max hK le_rfl))
  have h3 : max K₁ x ≤ max K x := max_le_max hK le_rfl
  omega

/-- One `K`-rung buys `+2` of root-gate slack (the `2·(x + …)` slot shape). -/
theorem relSlot_succ_gap (e : ONote) (B M : ℕ) :
    rel1 (ewRootSlot e B) M 0 + 2 ≤ rel1 (ewRootSlot e B) (M + 1) 0 := by
  simp only [rel1, ewRootSlot]
  have h1 : hardy e (max B (max M 0)) ≤ hardy e (max B (max (M + 1) 0)) :=
    hardy_monotone e (max_le_max le_rfl (max_le_max (Nat.le_succ M) le_rfl))
  have h2 : max M 0 + 1 ≤ max (M + 1) 0 := by omega
  omega

/-- The structural budget `B` is readable off the slot at `0`. -/
theorem le_relSlot_zero (e : ONote) (B K : ℕ) : B ≤ rel1 (ewRootSlot e B) K 0 := by
  simp only [rel1, ewRootSlot]
  have h1 := le_hardy e (max B (max K 0))
  have h2 : B ≤ max B (max K 0) := le_max_left _ _
  omega

/-! ### The master predicate and the `Derivation2` case ladder -/

/-- **The rung-E master predicate** (block-3 amendment of the W3 shape): structural budgets
`B` (slot), `d` (cut rank), `e` (control tower) OUTSIDE `∀ env`; per-assignment an env-local
relativization index `K` (the `SomeK` witness-budget discipline — see the block-3 discovery
note) and a node ordinal `α`; operator fixed at the full closure `Cl (⊤)` (every `Cl`
obligation is `Cl.base trivial`, and `∃ H, Cl H α ∧ …` follows). -/
def BudgetedEmbedsTC (Γ : Finset (SyntacticFormula ℒₒᵣ)) : Prop :=
  ∃ B d : ℕ, ∃ e : ONote, e.NF ∧ ∀ env : ℕ → ℕ, ∃ K : ℕ, ∃ α : ONote, α.NF ∧
    Zef2TC α e (fun _ => True) (rel1 (ewRootSlot e B) K) d
      (Γ.image (fun φ => Embedding.asg env ▹ φ))

/-- Every `Cl (⊤)` obligation is free. -/
theorem clT (β : ONote) : Cl (fun _ : ONote => True) β := Cl.base trivial

/-- **`closed`** — consume `em_Zef2TC'`; the ordinal is the deterministic complexity rung
(env-independent since rewriting preserves `complexity`), the budget is its `clog` gate. -/
theorem budgetedEmbedsTC_closed {Γ : Finset (SyntacticFormula ℒₒᵣ)}
    (φ : SyntacticFormula ℒₒᵣ) (hp : φ ∈ Γ) (hn : ∼φ ∈ Γ) :
    BudgetedEmbedsTC Γ := by
  refine ⟨clog (2 * φ.complexity + 1), 0, 0, ONote.NF.zero, fun env => ?_⟩
  refine ⟨0, ONote.ofNat (2 * (Embedding.asg env ▹ φ).complexity + 1), ONote.nf_ofNat _, ?_⟩
  have hf1 := ewRootSlot_f1 0 (clog (2 * φ.complexity + 1))
  have hmono : Monotone (rel1 (ewRootSlot 0 (clog (2 * φ.complexity + 1))) 0) :=
    rel1_monotone hf1.1.monotone 0
  have hinfl : ∀ m, m ≤ rel1 (ewRootSlot 0 (clog (2 * φ.complexity + 1))) 0 m :=
    rel1_infl (fun m => by have := hf1.2 m; omega) 0
  have hgate : clog (2 * (Embedding.asg env ▹ φ).complexity + 1)
      ≤ rel1 (ewRootSlot 0 (clog (2 * φ.complexity + 1))) 0 0 := by
    simp only [Semiformula.complexity_rew]
    exact le_relSlot_zero 0 _ 0
  exact em_Zef2TC' (Embedding.asg env ▹ φ) hmono hinfl hgate
    (Finset.mem_image_of_mem _ hp)
    (by simpa using Finset.mem_image_of_mem (fun ψ => Embedding.asg env ▹ ψ) hn)

/-- **`verum`** — `verumR` at ordinal `0`. -/
theorem budgetedEmbedsTC_verum {Γ : Finset (SyntacticFormula ℒₒᵣ)}
    (h : (⊤ : SyntacticFormula ℒₒᵣ) ∈ Γ) :
    BudgetedEmbedsTC Γ := by
  refine ⟨0, 0, 0, ONote.NF.zero, fun env => ⟨0, 0, ONote.NF.zero, ?_⟩⟩
  have hmem : (⊤ : SyntacticFormula ℒₒᵣ) ∈ Γ.image (fun ψ => Embedding.asg env ▹ ψ) := by
    have := Finset.mem_image_of_mem (fun ψ => Embedding.asg env ▹ ψ) h
    simpa using this
  exact Zef2TC.verumR (by simp) hmem

/-- **`wk`** — image weakening; all budgets carried. -/
theorem budgetedEmbedsTC_wk {Δ Γ : Finset (SyntacticFormula ℒₒᵣ)}
    (hsub : Δ ⊆ Γ) (ih : BudgetedEmbedsTC Δ) :
    BudgetedEmbedsTC Γ := by
  obtain ⟨B, d, e, he, ih⟩ := ih
  refine ⟨B, d, e, he, fun env => ?_⟩
  obtain ⟨K, α, hαNF, D⟩ := ih env
  exact ⟨K, α, hαNF, D.wk D.gate (Finset.image_subset_image hsub)⟩

/-- **`shift`** — the image collapses under the shifted assignment (`embedC`'s `hB`
computation, verbatim); budgets and derivation carried unchanged. -/
theorem budgetedEmbedsTC_shift {Γ : Finset (SyntacticFormula ℒₒᵣ)}
    (ih : BudgetedEmbedsTC Γ) :
    BudgetedEmbedsTC (Γ.image Rewriting.shift) := by
  obtain ⟨B, d, e, he, ih⟩ := ih
  refine ⟨B, d, e, he, fun env => ?_⟩
  obtain ⟨K, α, hαNF, D⟩ := ih (fun x => env (x + 1))
  refine ⟨K, α, hαNF, ?_⟩
  have himg : (Γ.image (Rewriting.shift : SyntacticFormula ℒₒᵣ → SyntacticFormula ℒₒᵣ)).image
        (fun φ => Embedding.asg env ▹ φ)
      = Γ.image (fun φ => Embedding.asg (fun x => env (x + 1)) ▹ φ) := by
    have hcompB : (Embedding.asg env).comp Rew.shift
        = Embedding.asg (fun x => env (x + 1)) := by
      ext x
      · exact Fin.elim0 x
      · simp [Embedding.asg, Rew.comp_app]
    rw [Finset.image_image]
    refine Finset.image_congr (fun ψ _ => ?_)
    show Embedding.asg env ▹ (Rew.shift ▹ ψ) = Embedding.asg (fun x => env (x + 1)) ▹ ψ
    rw [← TransitiveRewriting.comp_app, hcompB]
  rwa [himg]

/-- **`or`** — single premise; `osucc` root, one `K`-rung pays the `Nlog` gate. -/
theorem budgetedEmbedsTC_or {Γ : Finset (SyntacticFormula ℒₒᵣ)}
    {φ ψ : SyntacticFormula ℒₒᵣ} (h : φ ⋎ ψ ∈ Γ)
    (ih : BudgetedEmbedsTC (insert φ (insert ψ Γ))) :
    BudgetedEmbedsTC Γ := by
  obtain ⟨B, d, e, he, ih⟩ := ih
  refine ⟨B, d, e, he, fun env => ?_⟩
  obtain ⟨K, α, hαNF, D⟩ := ih env
  refine ⟨K + 1, osucc α, osucc_NF hαNF, ?_⟩
  have hgate := D.gate
  rw [Finset.image_insert, Finset.image_insert] at D
  have D' := D.mono_f (relSlot_mono (le_refl B) (Nat.le_succ K))
  have hg : Nlog (osucc α) ≤ rel1 (ewRootSlot e B) (K + 1) 0 := by
    have hs := Nlog_osucc_le hαNF
    have hgap := relSlot_succ_gap e B K
    omega
  have hor := Zef2TC.orI (α := osucc α) hg
    (Embedding.asg env ▹ φ) (Embedding.asg env ▹ ψ)
    (Zekd.lt_osucc hαNF) hαNF (osucc_NF hαNF) (clT α) D'
  have hmem : (Embedding.asg env ▹ φ ⋎ Embedding.asg env ▹ ψ)
      ∈ Γ.image (fun χ => Embedding.asg env ▹ χ) := by
    have := Finset.mem_image_of_mem (fun χ => Embedding.asg env ▹ χ) h
    simpa using this
  rwa [Finset.insert_eq_self.mpr hmem] at hor

/-- **`and`** — the two-premise join: control tower `osucc (e₁ + e₂)` (both strictly below,
`hardy_le_of_lt` fed by `norm eᵢ` absorbed into the structural `B`), root `osucc (α₁ + α₂)`
(`Nlog` absorbing + one `K`-rung of gate slack), budgets aligned by `max`/`mono`. -/
theorem budgetedEmbedsTC_and {Γ : Finset (SyntacticFormula ℒₒᵣ)}
    {φ ψ : SyntacticFormula ℒₒᵣ} (h : φ ⋏ ψ ∈ Γ)
    (ihp : BudgetedEmbedsTC (insert φ Γ)) (ihq : BudgetedEmbedsTC (insert ψ Γ)) :
    BudgetedEmbedsTC Γ := by
  obtain ⟨B₁, d₁, e₁, he₁, ih₁⟩ := ihp
  obtain ⟨B₂, d₂, e₂, he₂, ih₂⟩ := ihq
  have headdNF : (e₁ + e₂).NF := by haveI := he₁; haveI := he₂; exact ONote.add_nf e₁ e₂
  have heNF : (osucc (e₁ + e₂)).NF := osucc_NF headdNF
  have hlt₁ : e₁ < osucc (e₁ + e₂) :=
    lt_of_le_of_lt (Zekd.le_add_right_NF he₁ he₂) (Zekd.lt_osucc headdNF)
  have hlt₂ : e₂ < osucc (e₁ + e₂) :=
    lt_of_le_of_lt (Zekd.le_add_left_NF he₁ he₂) (Zekd.lt_osucc headdNF)
  refine ⟨B₁ + B₂ + norm e₁ + norm e₂, max d₁ d₂, osucc (e₁ + e₂), heNF, fun env => ?_⟩
  obtain ⟨K₁, α₁, hα₁NF, D₁⟩ := ih₁ env
  obtain ⟨K₂, α₂, hα₂NF, D₂⟩ := ih₂ env
  have haddNF : (α₁ + α₂).NF := by haveI := hα₁NF; haveI := hα₂NF; exact ONote.add_nf α₁ α₂
  refine ⟨max K₁ K₂ + 1, osucc (α₁ + α₂), osucc_NF haddNF, ?_⟩
  have hg₁ := D₁.gate
  have hg₂ := D₂.gate
  rw [Finset.image_insert] at D₁ D₂
  have hff₁ : ∀ x, rel1 (ewRootSlot e₁ B₁) K₁ x
      ≤ rel1 (ewRootSlot (osucc (e₁ + e₂)) (B₁ + B₂ + norm e₁ + norm e₂))
          (max K₁ K₂ + 1) x :=
    relSlot_le he₁ heNF hlt₁ (by omega) (by omega) (by omega)
  have hff₂ : ∀ x, rel1 (ewRootSlot e₂ B₂) K₂ x
      ≤ rel1 (ewRootSlot (osucc (e₁ + e₂)) (B₁ + B₂ + norm e₁ + norm e₂))
          (max K₁ K₂ + 1) x :=
    relSlot_le he₂ heNF hlt₂ (by omega) (by omega) (by omega)
  have D₁' := ((D₁.change_e (osucc (e₁ + e₂))).mono_f hff₁).mono_c (le_max_left d₁ d₂)
  have D₂' := ((D₂.change_e (osucc (e₁ + e₂))).mono_f hff₂).mono_c (le_max_right d₁ d₂)
  have hg : Nlog (osucc (α₁ + α₂))
      ≤ rel1 (ewRootSlot (osucc (e₁ + e₂)) (B₁ + B₂ + norm e₁ + norm e₂))
          (max K₁ K₂ + 1) 0 := by
    have hs := Nlog_osucc_le haddNF
    have ha := Nlog_add_le_max_succ α₁ hα₁NF α₂ hα₂NF
    have j₁ : rel1 (ewRootSlot e₁ B₁) K₁ 0
        ≤ rel1 (ewRootSlot (osucc (e₁ + e₂)) (B₁ + B₂ + norm e₁ + norm e₂)) (max K₁ K₂) 0 :=
      relSlot_le he₁ heNF hlt₁ (by omega) (le_max_left _ _) (by omega) 0
    have j₂ : rel1 (ewRootSlot e₂ B₂) K₂ 0
        ≤ rel1 (ewRootSlot (osucc (e₁ + e₂)) (B₁ + B₂ + norm e₁ + norm e₂)) (max K₁ K₂) 0 :=
      relSlot_le he₂ heNF hlt₂ (by omega) (le_max_right _ _) (by omega) 0
    have hgap := relSlot_succ_gap (osucc (e₁ + e₂)) (B₁ + B₂ + norm e₁ + norm e₂) (max K₁ K₂)
    omega
  have hand := Zef2TC.andI (α := osucc (α₁ + α₂)) hg
    (Embedding.asg env ▹ φ) (Embedding.asg env ▹ ψ)
    (lt_of_le_of_lt (Zekd.le_add_right_NF hα₁NF hα₂NF) (Zekd.lt_osucc haddNF))
    (lt_of_le_of_lt (Zekd.le_add_left_NF hα₁NF hα₂NF) (Zekd.lt_osucc haddNF))
    hα₁NF hα₂NF (osucc_NF haddNF) (clT α₁) (clT α₂) D₁' D₂'
  have hmem : (Embedding.asg env ▹ φ ⋏ Embedding.asg env ▹ ψ)
      ∈ Γ.image (fun χ => Embedding.asg env ▹ χ) := by
    have := Finset.mem_image_of_mem (fun χ => Embedding.asg env ▹ χ) h
    simpa using this
  rwa [Finset.insert_eq_self.mpr hmem] at hand

/-- **`cut`** — same two-premise join as `and`; the cut rank is `max`ed with
`φ.complexity + 1` (env-independent: rewriting preserves `complexity`) and the read gate
`complexity ≤ f 0` is paid by absorbing `φ.complexity` into the structural `B`. -/
theorem budgetedEmbedsTC_cut {Γ : Finset (SyntacticFormula ℒₒᵣ)}
    {φ : SyntacticFormula ℒₒᵣ}
    (ihp : BudgetedEmbedsTC (insert φ Γ)) (ihn : BudgetedEmbedsTC (insert (∼φ) Γ)) :
    BudgetedEmbedsTC Γ := by
  obtain ⟨B₁, d₁, e₁, he₁, ih₁⟩ := ihp
  obtain ⟨B₂, d₂, e₂, he₂, ih₂⟩ := ihn
  have headdNF : (e₁ + e₂).NF := by haveI := he₁; haveI := he₂; exact ONote.add_nf e₁ e₂
  have heNF : (osucc (e₁ + e₂)).NF := osucc_NF headdNF
  have hlt₁ : e₁ < osucc (e₁ + e₂) :=
    lt_of_le_of_lt (Zekd.le_add_right_NF he₁ he₂) (Zekd.lt_osucc headdNF)
  have hlt₂ : e₂ < osucc (e₁ + e₂) :=
    lt_of_le_of_lt (Zekd.le_add_left_NF he₁ he₂) (Zekd.lt_osucc headdNF)
  refine ⟨B₁ + B₂ + norm e₁ + norm e₂ + φ.complexity, max (max d₁ d₂) (φ.complexity + 1),
    osucc (e₁ + e₂), heNF, fun env => ?_⟩
  obtain ⟨K₁, α₁, hα₁NF, D₁⟩ := ih₁ env
  obtain ⟨K₂, α₂, hα₂NF, D₂⟩ := ih₂ env
  have haddNF : (α₁ + α₂).NF := by haveI := hα₁NF; haveI := hα₂NF; exact ONote.add_nf α₁ α₂
  refine ⟨max K₁ K₂ + 1, osucc (α₁ + α₂), osucc_NF haddNF, ?_⟩
  have hg₁ := D₁.gate
  have hg₂ := D₂.gate
  rw [Finset.image_insert] at D₁ D₂
  have hff₁ : ∀ x, rel1 (ewRootSlot e₁ B₁) K₁ x
      ≤ rel1 (ewRootSlot (osucc (e₁ + e₂)) (B₁ + B₂ + norm e₁ + norm e₂ + φ.complexity))
          (max K₁ K₂ + 1) x :=
    relSlot_le he₁ heNF hlt₁ (by omega) (by omega) (by omega)
  have hff₂ : ∀ x, rel1 (ewRootSlot e₂ B₂) K₂ x
      ≤ rel1 (ewRootSlot (osucc (e₁ + e₂)) (B₁ + B₂ + norm e₁ + norm e₂ + φ.complexity))
          (max K₁ K₂ + 1) x :=
    relSlot_le he₂ heNF hlt₂ (by omega) (by omega) (by omega)
  have D₁' := ((D₁.change_e (osucc (e₁ + e₂))).mono_f hff₁).mono_c
    (c' := max (max d₁ d₂) (φ.complexity + 1))
    (le_trans (le_max_left d₁ d₂) (le_max_left _ _))
  have D₂' := ((D₂.change_e (osucc (e₁ + e₂))).mono_f hff₂).mono_c
    (c' := max (max d₁ d₂) (φ.complexity + 1))
    (le_trans (le_max_right d₁ d₂) (le_max_left _ _))
  rw [show Embedding.asg env ▹ (∼φ) = ∼(Embedding.asg env ▹ φ) by simp] at D₂'
  have hg : Nlog (osucc (α₁ + α₂))
      ≤ rel1 (ewRootSlot (osucc (e₁ + e₂)) (B₁ + B₂ + norm e₁ + norm e₂ + φ.complexity))
          (max K₁ K₂ + 1) 0 := by
    have hs := Nlog_osucc_le haddNF
    have ha := Nlog_add_le_max_succ α₁ hα₁NF α₂ hα₂NF
    have j₁ : rel1 (ewRootSlot e₁ B₁) K₁ 0
        ≤ rel1 (ewRootSlot (osucc (e₁ + e₂))
            (B₁ + B₂ + norm e₁ + norm e₂ + φ.complexity)) (max K₁ K₂) 0 :=
      relSlot_le he₁ heNF hlt₁ (by omega) (le_max_left _ _) (by omega) 0
    have j₂ : rel1 (ewRootSlot e₂ B₂) K₂ 0
        ≤ rel1 (ewRootSlot (osucc (e₁ + e₂))
            (B₁ + B₂ + norm e₁ + norm e₂ + φ.complexity)) (max K₁ K₂) 0 :=
      relSlot_le he₂ heNF hlt₂ (by omega) (le_max_right _ _) (by omega) 0
    have hgap := relSlot_succ_gap (osucc (e₁ + e₂))
      (B₁ + B₂ + norm e₁ + norm e₂ + φ.complexity) (max K₁ K₂)
    omega
  have hread : (Embedding.asg env ▹ φ).complexity
      ≤ rel1 (ewRootSlot (osucc (e₁ + e₂)) (B₁ + B₂ + norm e₁ + norm e₂ + φ.complexity))
          (max K₁ K₂ + 1) 0 := by
    simp only [Semiformula.complexity_rew]
    exact le_trans (by omega) (le_relSlot_zero _ _ _)
  have hcompl : (Embedding.asg env ▹ φ).complexity < max (max d₁ d₂) (φ.complexity + 1) := by
    simp only [Semiformula.complexity_rew]
    omega
  exact Zef2TC.cut hg (Embedding.asg env ▹ φ) hcompl hread
    (lt_of_le_of_lt (Zekd.le_add_right_NF hα₁NF hα₂NF) (Zekd.lt_osucc haddNF))
    (lt_of_le_of_lt (Zekd.le_add_left_NF hα₁NF hα₂NF) (Zekd.lt_osucc haddNF))
    hα₁NF hα₂NF (osucc_NF haddNF) (clT α₁) (clT α₂) D₁' D₂'

/- **`axm` / `all` leaves of `budgetedEmbedding_Zef2TC` — RETIRED (SERIES-5 Lane C).**  These were
the two open hard leaves (W1/W2 content) of the `Derivation2`-induction TC master ladder
`budgetedEmbedding_Zef2TC`, which is itself superseded by the ratified `embedding_Zef2TC_V3`
(proved sorry-free via `budgetedEmbeddingV3`). The master and both leaves had no consumers on the
clean pipeline; deleted together (below) to reach `src` sorry-free. -/

/-! ### The value-congruent EM engine + the closed-term collapse (the `exs` kit)

Mirror of `provable_em_cong_gen`/`Provable.exI_closed` (`Embedding.lean`) with the `Zef2TC`
budget bookkeeping of `em_Zef2TC`; the atomic cases split on `atomTrue` and close by
`trueRel`/`trueNrel` — this is exactly where (Ax2) is load-bearing (in `Z∞` the split used
`axTrue`; `Zef2` alone has no true-literal leaf).  The congruence kit
(`stdClosedVal`/`atomTrue_rel_congr`/`embedding_subst_q_cons_app`) is banked in
`OperatorZinfty`. -/

private theorem em_cong_atomic_rel {n : ℕ} (w w' : Fin n → SyntacticTerm ℒₒᵣ)
    (hval : ∀ i, stdClosedVal (w i) = stdClosedVal (w' i))
    {ar : ℕ} (r : (ℒₒᵣ).Rel ar) (v : Fin ar → SyntacticSemiterm ℒₒᵣ n)
    {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Seq}
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

private theorem em_cong_atomic_nrel {n : ℕ} (w w' : Fin n → SyntacticTerm ℒₒᵣ)
    (hval : ∀ i, stdClosedVal (w i) = stdClosedVal (w' i))
    {ar : ℕ} (r : (ℒₒᵣ).Rel ar) (v : Fin ar → SyntacticSemiterm ℒₒᵣ n)
    {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Seq}
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

/-- **Value-congruent budgeted EM** (arity-general; the `exs`-case engine): for pointwise
value-equal closed substitutions `w, w'`, any sequent containing `Rew.subst w ▹ ψ` and
`∼(Rew.subst w' ▹ ψ)` is cut-free `Zef2TC`-derivable at the deterministic rung
`ofNat (2k+1)`.  Same budget discipline as `em_Zef2TC` (all hypotheses `rel1`-stable);
atomic cases via `trueRel`/`trueNrel` + `stdClosedVal` congruence — the (Ax2)-load-bearing
step. -/
theorem em_cong_Zef2TC (k : ℕ) :
    ∀ {n : ℕ} (w w' : Fin n → SyntacticTerm ℒₒᵣ) (ψ : SyntacticSemiformula ℒₒᵣ n),
      ψ.complexity ≤ k →
      (∀ i, stdClosedVal (w i) = stdClosedVal (w' i)) →
      ∀ {e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {Γ : Seq},
        Monotone f → (∀ m, m ≤ f m) → clog (2 * k + 1) ≤ f 0 →
        (Rew.subst w ▹ ψ) ∈ Γ → (∼(Rew.subst w' ▹ ψ)) ∈ Γ →
        Zef2TC (ONote.ofNat (2 * k + 1)) e H f 0 Γ := by
  induction k with
  | zero =>
    intro n w w' ψ hk hval e H f Γ hmono hinfl hgate hp hn
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
    intro n w w' ψ hk hval e H f Γ hmono hinfl hgate hp hn
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
theorem em_cong1_Zef2TC (s s' : SyntacticTerm ℒₒᵣ)
    (hval : stdClosedVal s = stdClosedVal s')
    (ψ : SyntacticSemiformula ℒₒᵣ 1) {e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {Γ : Seq}
    (hmono : Monotone f) (hinfl : ∀ m, m ≤ f m)
    (hgate : clog (2 * ψ.complexity + 1) ≤ f 0)
    (hp : (ψ/[s]) ∈ Γ) (hn : (∼(ψ/[s'])) ∈ Γ) :
    Zef2TC (ONote.ofNat (2 * ψ.complexity + 1)) e H f 0 Γ := by
  refine em_cong_Zef2TC ψ.complexity ![s] ![s'] ψ le_rfl ?_ hmono hinfl hgate hp hn
  intro i
  cases i using Fin.cases with
  | zero => simpa using hval
  | succ j => exact j.elim0

/-- The relativization index is readable off the slot at `0`. -/
theorem index_le_relSlot_zero (e : ONote) (B K : ℕ) : K ≤ rel1 (ewRootSlot e B) K 0 := by
  simp only [rel1, ewRootSlot]
  omega

/-- **`exs`** — the closed-term collapse, DISCHARGED.  `asg env t` is closed with standard
value `m`; the value-congruent EM (`em_cong1_Zef2TC`, at pair `(nm m, asg env t)`) + one
`cut` at rank `complexity+1` convert the IH's `ψ'/[asg env t]` into `ψ'/[nm m]`, and `exI`
fires at witness `m` — env-dependent, absorbed into the relativization index
`K := max K₁ m + 3` (the `∃ K` amendment's raison d'être; `n ≤ f 0` paid by
`index_le_relSlot_zero`, the two ordinal-join gates by `relSlot_succ_gap` rungs). -/
theorem budgetedEmbedsTC_exs {Γ : Finset (SyntacticFormula ℒₒᵣ)}
    {φ : SyntacticSemiformula ℒₒᵣ 1} (h : ∃⁰ φ ∈ Γ) (t : SyntacticTerm ℒₒᵣ)
    (ih : BudgetedEmbedsTC (insert (φ/[t]) Γ)) :
    BudgetedEmbedsTC Γ := by
  obtain ⟨B₁, d₁, e₁, he₁, ih₁⟩ := ih
  refine ⟨B₁ + φ.complexity + clog (2 * φ.complexity + 1), max d₁ (φ.complexity + 1), e₁,
    he₁, fun env => ?_⟩
  set B : ℕ := B₁ + φ.complexity + clog (2 * φ.complexity + 1) with hB
  set d : ℕ := max d₁ (φ.complexity + 1) with hd
  obtain ⟨K₁, α₁, hα₁NF, D₁⟩ := ih₁ env
  -- the closed witness and its standard value
  set ψ' : SyntacticSemiformula ℒₒᵣ 1 := (Embedding.asg env).q ▹ φ with hψ'
  set s : SyntacticTerm ℒₒᵣ := Embedding.asg env t with hs
  set m : ℕ := stdClosedVal s with hm
  set K : ℕ := max K₁ m + 3 with hK
  set F : ℕ → ℕ := rel1 (ewRootSlot e₁ B) K with hF
  have hψc : ψ'.complexity = φ.complexity := by simp [hψ']
  have hf1 := ewRootSlot_f1 e₁ B
  have hFmono : Monotone F := rel1_monotone hf1.1.monotone K
  have hFinfl : ∀ x, x ≤ F x := rel1_infl (fun x => by have := hf1.2 x; omega) K
  -- the IH derivation, re-based to the joined budget and rewritten to the substituted head
  have hg₁ := D₁.gate
  rw [Finset.image_insert, Embedding.rew_subst_term (Embedding.asg env) φ t] at D₁
  have D₁' := (D₁.mono_f (relSlot_mono (show B₁ ≤ B by omega) (show K₁ ≤ K by omega))).mono_c
    (c' := d) (le_max_left _ _)
  -- left cut premise: add ψ'/[nm m] to the context
  have Dsrc : Zef2TC α₁ e₁ (fun _ => True) F d
      (insert (ψ'/[s]) (insert (ψ'/[nm m])
        (Γ.image (fun χ => Embedding.asg env ▹ χ)))) :=
    D₁'.wk D₁'.gate (Finset.insert_subset_insert _ (Finset.subset_insert _ _))
  -- right cut premise: value-congruent EM at the pair (nm m, s)
  have hgateEM : clog (2 * ψ'.complexity + 1) ≤ F 0 := by
    rw [hψc]
    exact le_trans (by omega) (le_relSlot_zero e₁ B K)
  have Dcong : Zef2TC (ONote.ofNat (2 * ψ'.complexity + 1)) e₁ (fun _ => True) F 0
      (insert (∼(ψ'/[s])) (insert (ψ'/[nm m])
        (Γ.image (fun χ => Embedding.asg env ▹ χ)))) := by
    refine em_cong1_Zef2TC (nm m) s (by simp [hm]) ψ' hFmono hFinfl hgateEM ?_ ?_
    · exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    · exact Finset.mem_insert_self _ _
  have Dcong' := Dcong.mono_c (c' := d) (Nat.zero_le d)
  -- the cut, at root `osucc (α₁ + ofNat (2·complexity+1))`
  have hofNF : (ONote.ofNat (2 * ψ'.complexity + 1)).NF := ONote.nf_ofNat _
  have haddNF : (α₁ + ONote.ofNat (2 * ψ'.complexity + 1)).NF := by
    haveI := hα₁NF; haveI := hofNF; exact ONote.add_nf _ _
  have hslack : ∀ M, rel1 (ewRootSlot e₁ B) M 0 + 2
      ≤ rel1 (ewRootSlot e₁ B) (M + 2) 0 := by
    intro M
    have g1 := relSlot_succ_gap e₁ B M
    have g2 := relSlot_succ_gap e₁ B (M + 1)
    rw [show M + 1 + 1 = M + 2 from rfl] at g2
    omega
  have hgcut : Nlog (osucc (α₁ + ONote.ofNat (2 * ψ'.complexity + 1))) ≤ F 0 := by
    rw [hF, hK]
    have hs' := Nlog_osucc_le haddNF
    have ha := Nlog_add_le_max_succ α₁ hα₁NF _ hofNF
    have hα₁K : rel1 (ewRootSlot e₁ B₁) K₁ 0 ≤ rel1 (ewRootSlot e₁ B) (max K₁ m) 0 :=
      relSlot_mono (by omega) (le_max_left _ _) 0
    have hof : Nlog (ONote.ofNat (2 * ψ'.complexity + 1)) ≤ rel1 (ewRootSlot e₁ B) (max K₁ m) 0 :=
      le_trans (Nlog_ofNat_le _) (le_trans (by rw [hψc]; omega)
        (le_relSlot_zero e₁ B (max K₁ m)))
    have hgap := hslack (max K₁ m)
    have hlast := relSlot_succ_gap e₁ B (max K₁ m + 2)
    rw [show max K₁ m + 2 + 1 = max K₁ m + 3 from rfl] at hlast
    omega
  have hcompl : (ψ'/[s]).complexity < d := by
    have : (ψ'/[s]).complexity = φ.complexity := by simp [hψ']
    omega
  have hread : (ψ'/[s]).complexity ≤ F 0 := by
    have hc : (ψ'/[s]).complexity = φ.complexity := by simp [hψ']
    rw [hc]
    exact le_trans (by omega) (le_relSlot_zero e₁ B K)
  have Dnum : Zef2TC (osucc (α₁ + ONote.ofNat (2 * ψ'.complexity + 1))) e₁ (fun _ => True) F d
      (insert (ψ'/[nm m]) (Γ.image (fun χ => Embedding.asg env ▹ χ))) :=
    Zef2TC.cut hgcut (ψ'/[s]) hcompl hread
      (lt_of_le_of_lt (Zekd.le_add_right_NF hα₁NF hofNF) (Zekd.lt_osucc haddNF))
      (lt_of_le_of_lt (Zekd.le_add_left_NF hα₁NF hofNF) (Zekd.lt_osucc haddNF))
      hα₁NF hofNF (osucc_NF haddNF) (clT _) (clT _) Dsrc Dcong'
  -- the ∃-introduction at the numeral witness `m`
  refine ⟨K, osucc (osucc (α₁ + ONote.ofNat (2 * ψ'.complexity + 1))),
    osucc_NF (osucc_NF haddNF), ?_⟩
  have hgout : Nlog (osucc (osucc (α₁ + ONote.ofNat (2 * ψ'.complexity + 1)))) ≤ F 0 := by
    rw [hF, hK]
    have hs' := Nlog_osucc_le (osucc_NF haddNF)
    have hs'' := Nlog_osucc_le haddNF
    have ha := Nlog_add_le_max_succ α₁ hα₁NF _ hofNF
    have hα₁K : rel1 (ewRootSlot e₁ B₁) K₁ 0 ≤ rel1 (ewRootSlot e₁ B) (max K₁ m) 0 :=
      relSlot_mono (by omega) (le_max_left _ _) 0
    have hof : Nlog (ONote.ofNat (2 * ψ'.complexity + 1)) ≤ rel1 (ewRootSlot e₁ B) (max K₁ m) 0 :=
      le_trans (Nlog_ofNat_le _) (le_trans (by rw [hψc]; omega)
        (le_relSlot_zero e₁ B (max K₁ m)))
    have g1 := relSlot_succ_gap e₁ B (max K₁ m)
    have g2 := relSlot_succ_gap e₁ B (max K₁ m + 1)
    have g3 := relSlot_succ_gap e₁ B (max K₁ m + 2)
    rw [show max K₁ m + 1 + 1 = max K₁ m + 2 from rfl] at g2
    rw [show max K₁ m + 2 + 1 = max K₁ m + 3 from rfl] at g3
    omega
  have hwit : m ≤ F 0 := le_trans (by omega) (index_le_relSlot_zero e₁ B K)
  have hexI := Zef2TC.exI (α := osucc (osucc (α₁ + ONote.ofNat (2 * ψ'.complexity + 1))))
    hgout ψ' m
    (Zekd.lt_osucc (osucc_NF haddNF)) (osucc_NF haddNF)
    (osucc_NF (osucc_NF haddNF)) (clT _) hwit Dnum
  have hmem : (∃⁰ ψ') ∈ Γ.image (fun χ => Embedding.asg env ▹ χ) := by
    have := Finset.mem_image_of_mem (fun χ => Embedding.asg env ▹ χ) h
    simpa [hψ'] using this
  rwa [Finset.insert_eq_self.mpr hmem] at hexI

/- **`budgetedEmbedding_Zef2TC` (rung-E master ladder via `Derivation2` induction) — RETIRED
(SERIES-5 Lane C).**  Superseded by the ratified `embedding_Zef2TC_V3` (proved sorry-free via
`budgetedEmbeddingV3`); had no consumers on the clean pipeline. Deleted with its two open leaves
(`budgetedEmbedsTC_axm` / `_all`, above) to reach `src` sorry-free. The clean per-case helpers
(`budgetedEmbedsTC_closed/verum/and/or/exs/wk/shift/cut`) are retained. -/

/- **DRAFT2 (block-3 amendment) — RETIRED (SERIES-5 Lane C).**  The `∃ K`-relativized statement
was ratified and realized as `embedding_Zef2TC_V3` (proved sorry-free below); this draft placeholder
had no code consumers and its `sorry` was decorative. Deleted to reach `src` sorry-free. -/

end GoodsteinPA.E1EmbeddingGrind

-- Audit anchors.  The seven closed ladder cases are standard-triple
-- (`[propext, Classical.choice, Quot.sound]`, no sorryAx); the assembled master carries
-- `sorryAx` exactly through the three disclosed hard leaves (`axm`/`all`/`exs`).
#print axioms GoodsteinPA.E1EmbeddingGrind.budgetedEmbedsTC_closed
#print axioms GoodsteinPA.E1EmbeddingGrind.budgetedEmbedsTC_and
#print axioms GoodsteinPA.E1EmbeddingGrind.budgetedEmbedsTC_cut
#print axioms GoodsteinPA.E1EmbeddingGrind.em_cong_Zef2TC
#print axioms GoodsteinPA.E1EmbeddingGrind.budgetedEmbedsTC_exs

namespace GoodsteinPA.E1EmbeddingGrind

open LO LO.FirstOrder ONote
open GoodsteinPA.FastGrowing
open GoodsteinPA.OperatorZeh GoodsteinPA.OperatorZinfty

/-! ## E-1 block 5 — the GROWTH KIT: `Gexp = hardy (ω²)` dominates ℒₒᵣ term values

The `all` case's residue (and the coming V3 refinement of the master predicate): the env-local
witness budget must be BOUNDED BY A STRUCTURAL FUNCTION of the assignment, or the ω-rule cannot
uniformize the branches (`K_n` unbounded in `n` kills `rel1 f n` domination).  The mechanism
that pays every witness is the control tower: every closed-term value under `asg env` is
dominated by finitely many iterates of the single engine `Gexp := hardy (ω²)` applied to the
sup of the finitely many relevant `env` values. -/

/-- The growth engine: `H_{ω²}`. -/
noncomputable def Gexp : ℕ → ℕ := hardy (oadd (ONote.ofNat 2) 1 0)

theorem Gexp_eq (x : ℕ) : Gexp x = 2 ^ (x + 1) * (x + 1) - 1 := by
  have h := hardy_omega_pow_ofNat 2 x
  have h2 : fastGrowing (ONote.ofNat 2) (x + 1) = 2 ^ (x + 1) * (x + 1) := by
    rw [show ONote.ofNat 2 = 2 from rfl, ONote.fastGrowing_two]
  have hpos : 0 < 2 ^ (x + 1) * (x + 1) := Nat.mul_pos (Nat.two_pow_pos _) (Nat.succ_pos x)
  unfold Gexp
  omega

theorem Gexp_monotone : Monotone Gexp := hardy_monotone _

theorem le_Gexp (x : ℕ) : x ≤ Gexp x := le_hardy _ x

theorem succ_le_Gexp (x : ℕ) : x + 1 ≤ Gexp x := by
  rw [Gexp_eq]
  have h2 : 2 ≤ 2 ^ (x + 1) := by
    calc 2 = 2 ^ 1 := rfl
    _ ≤ 2 ^ (x + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have h3 : 2 * (x + 1) ≤ 2 ^ (x + 1) * (x + 1) := Nat.mul_le_mul_right _ h2
  omega

/-- The two closure facts term domination needs: `Gexp (max a b)` absorbs both `a + b`
and `a * b`. -/
theorem add_le_Gexp_max (a b : ℕ) : a + b ≤ Gexp (max a b) := by
  rw [Gexp_eq]
  have h2 : 2 ≤ 2 ^ (max a b + 1) := by
    calc 2 = 2 ^ 1 := rfl
    _ ≤ 2 ^ (max a b + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have h3 : 2 * (max a b + 1) ≤ 2 ^ (max a b + 1) * (max a b + 1) := Nat.mul_le_mul_right _ h2
  have hab : a + b ≤ 2 * max a b := by omega
  omega

theorem mul_le_Gexp_max (a b : ℕ) : a * b ≤ Gexp (max a b) := by
  rw [Gexp_eq]
  have hab : a * b ≤ max a b * max a b :=
    Nat.mul_le_mul (le_max_left a b) (le_max_right a b)
  have h1 : max a b + 1 ≤ 2 ^ (max a b + 1) := le_of_lt Nat.lt_two_pow_self
  have h2 : (max a b + 1) * (max a b + 1) = max a b * max a b + 2 * max a b + 1 := by ring
  have h3 : (max a b + 1) * (max a b + 1) ≤ 2 ^ (max a b + 1) * (max a b + 1) :=
    Nat.mul_le_mul_right _ h1
  omega

theorem Gexp_iter_monotone (c : ℕ) : Monotone (Gexp^[c]) :=
  Gexp_monotone.iterate c

theorem le_Gexp_iter (c x : ℕ) : x ≤ Gexp^[c] x := by
  induction c with
  | zero => simp
  | succ c ih =>
      rw [Function.iterate_succ_apply']
      exact le_trans ih (le_Gexp _)

theorem Gexp_iter_le_iter {c c' : ℕ} (h : c ≤ c') (x : ℕ) : Gexp^[c] x ≤ Gexp^[c'] x := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Function.iterate_add_apply]
  exact Gexp_iter_monotone c (le_Gexp_iter k x)

theorem iter_le_Gexp_iter (c x : ℕ) : c ≤ Gexp^[c] x := by
  induction c with
  | zero => exact Nat.zero_le _
  | succ c ih =>
      rw [Function.iterate_succ_apply']
      have h1 := succ_le_Gexp (Gexp^[c] x)
      omega

/-- Iterates as a single Hardy value: `Gexp^[c] = H_{ω²·c}` — the control tower absorbs the
iterate budget (`hardy_single_coeff`; exponent `ofNat 2 ≠ 0`). -/
theorem Gexp_iter_eq_hardy (c : ℕ+) (x : ℕ) :
    Gexp^[(c : ℕ)] x = hardy (oadd (ONote.ofNat 2) c 0) x :=
  (hardy_single_coeff (ONote.ofNat 2) (by decide) c x).symm

/-! ### `envSup` — the canonical assignment sup -/

/-- Sup of the first `N` values of the assignment (the canonical witness-budget seed; `N` is
the sequent's structural fv bound). -/
def envSup (env : ℕ → ℕ) (N : ℕ) : ℕ := (Finset.range N).sup env

theorem envSup_mono_N (env : ℕ → ℕ) {N N' : ℕ} (h : N ≤ N') :
    envSup env N ≤ envSup env N' :=
  Finset.sup_mono (fun x hx => by
    simp only [Finset.mem_range] at hx ⊢; omega)

theorem le_envSup {env : ℕ → ℕ} {N x : ℕ} (hx : x < N) : env x ≤ envSup env N :=
  Finset.le_sup (Finset.mem_range.mpr hx)

/-- The ω-rule cons law: the branch assignment's sup collapses to `max n` of the root's. -/
theorem envSup_cons_le (env : ℕ → ℕ) (n N : ℕ) :
    envSup (n :>ₙ env) (N + 1) ≤ max n (envSup env N) := by
  refine Finset.sup_le fun x hx => ?_
  rcases x with _ | y
  · simp
  · have hy : y < N := by simpa using hx
    exact le_trans (by simpa using le_envSup hy) (le_max_right _ _)

/-! ### Term domination -/

/-- **Term domination**: every ℒₒᵣ term value under any assignment is bounded by structurally
many `Gexp`-iterates of the env-sup over a structural fv bound.  Induction on the term; the
`add`/`mul` closure facts pay the function cases.  This is the mechanism the `exs`/`all`
witness budgets reduce to (E–W: the control tower pays for term growth). -/
theorem term_val_le_Gexp_iter (t : SyntacticTerm ℒₒᵣ) :
    ∃ c N : ℕ, ∀ env : ℕ → ℕ,
      GoodsteinPA.Compat.gValm ℕ ![] env t ≤ Gexp^[c] (envSup env N) := by
  induction t with
  | bvar x => exact x.elim0
  | fvar x =>
      exact ⟨0, x + 1, fun env => by
        simpa using le_envSup (Nat.lt_succ_self x)⟩
  | func f v ih =>
      match f, v with
      | LO.FirstOrder.Language.ORing.Func.zero, v =>
          refine ⟨0, 0, fun env => ?_⟩
          have hv : GoodsteinPA.Compat.gValm ℕ ![] env (Semiterm.func
              LO.FirstOrder.Language.ORing.Func.zero v) = 0 := by
            simp only [GoodsteinPA.Compat.gValm, Semiterm.val_func]; rfl
          simp [hv]
      | LO.FirstOrder.Language.ORing.Func.one, v =>
          refine ⟨1, 0, fun env => ?_⟩
          have h1 := iter_le_Gexp_iter 1 (envSup env 0)
          have hv : GoodsteinPA.Compat.gValm ℕ ![] env (Semiterm.func
              LO.FirstOrder.Language.ORing.Func.one v) = 1 := by
            simp only [GoodsteinPA.Compat.gValm, Semiterm.val_func]; rfl
          omega
      | LO.FirstOrder.Language.ORing.Func.add, v =>
          obtain ⟨c₀, N₀, h₀⟩ := ih 0
          obtain ⟨c₁, N₁, h₁⟩ := ih 1
          refine ⟨max c₀ c₁ + 1, max N₀ N₁, fun env => ?_⟩
          have hb₀ : GoodsteinPA.Compat.gValm ℕ ![] env (v 0)
              ≤ Gexp^[max c₀ c₁] (envSup env (max N₀ N₁)) :=
            le_trans (h₀ env) (le_trans
              (Gexp_iter_le_iter (le_max_left c₀ c₁) _)
              (Gexp_iter_monotone _ (envSup_mono_N env (le_max_left N₀ N₁))))
          have hb₁ : GoodsteinPA.Compat.gValm ℕ ![] env (v 1)
              ≤ Gexp^[max c₀ c₁] (envSup env (max N₀ N₁)) :=
            le_trans (h₁ env) (le_trans
              (Gexp_iter_le_iter (le_max_right c₀ c₁) _)
              (Gexp_iter_monotone _ (envSup_mono_N env (le_max_right N₀ N₁))))
          have hadd : GoodsteinPA.Compat.gValm ℕ ![] env (Semiterm.func
              LO.FirstOrder.Language.ORing.Func.add v)
              = GoodsteinPA.Compat.gValm ℕ ![] env (v 0) + GoodsteinPA.Compat.gValm ℕ ![] env (v 1) := by
            simp only [GoodsteinPA.Compat.gValm, Semiterm.val_func]; rfl
          rw [hadd, Function.iterate_succ_apply']
          refine le_trans (add_le_Gexp_max _ _) (Gexp_monotone ?_)
          exact max_le hb₀ hb₁
      | LO.FirstOrder.Language.ORing.Func.mul, v =>
          obtain ⟨c₀, N₀, h₀⟩ := ih 0
          obtain ⟨c₁, N₁, h₁⟩ := ih 1
          refine ⟨max c₀ c₁ + 1, max N₀ N₁, fun env => ?_⟩
          have hb₀ : GoodsteinPA.Compat.gValm ℕ ![] env (v 0)
              ≤ Gexp^[max c₀ c₁] (envSup env (max N₀ N₁)) :=
            le_trans (h₀ env) (le_trans
              (Gexp_iter_le_iter (le_max_left c₀ c₁) _)
              (Gexp_iter_monotone _ (envSup_mono_N env (le_max_left N₀ N₁))))
          have hb₁ : GoodsteinPA.Compat.gValm ℕ ![] env (v 1)
              ≤ Gexp^[max c₀ c₁] (envSup env (max N₀ N₁)) :=
            le_trans (h₁ env) (le_trans
              (Gexp_iter_le_iter (le_max_right c₀ c₁) _)
              (Gexp_iter_monotone _ (envSup_mono_N env (le_max_right N₀ N₁))))
          have hmul : GoodsteinPA.Compat.gValm ℕ ![] env (Semiterm.func
              LO.FirstOrder.Language.ORing.Func.mul v)
              = GoodsteinPA.Compat.gValm ℕ ![] env (v 0) * GoodsteinPA.Compat.gValm ℕ ![] env (v 1) := by
            simp only [GoodsteinPA.Compat.gValm, Semiterm.val_func]; rfl
          rw [hmul, Function.iterate_succ_apply']
          refine le_trans (mul_le_Gexp_max _ _) (Gexp_monotone ?_)
          exact max_le hb₀ hb₁

/-- Bridge: the `atomTrue`-evaluator value of the `asg`-closed term is the direct
`env`-valuation. -/
theorem stdClosedVal_asg (env : ℕ → ℕ) (t : SyntacticTerm ℒₒᵣ) :
    stdClosedVal (Embedding.asg env t) = GoodsteinPA.Compat.gValm ℕ ![] env t := by
  show GoodsteinPA.Compat.gVal _ (fun _ => 0) (fun _ => 0) (Rew.rewrite (fun x => nm (env x)) t) = _
  -- unfold the `gVal`/`gValm` shims so `rw` sees `Semiterm.val`; upstream's `val_rewrite` now emits
  -- the free-var assignment in `∘`-composition form, so normalize it back with `Function.comp_def`
  unfold GoodsteinPA.Compat.gVal GoodsteinPA.Compat.gValm
  rw [Semiterm.val_rewrite]
  simp only [Function.comp_def]
  have he : (fun _ => 0 : Fin 0 → ℕ) = ![] := funext (fun x => x.elim0)
  rw [he]
  congr 1
  funext x
  exact Embedding.valm_nm (env x) (fun _ => 0)

/-- **The `exs`/V3 witness gate**: the closed witness's standard value is dominated by
structurally many `Gexp`-iterates of the env-sup. -/
theorem stdClosedVal_asg_le_Gexp_iter (t : SyntacticTerm ℒₒᵣ) :
    ∃ c N : ℕ, ∀ env : ℕ → ℕ,
      stdClosedVal (Embedding.asg env t) ≤ Gexp^[c] (envSup env N) := by
  obtain ⟨c, N, h⟩ := term_val_le_Gexp_iter t
  exact ⟨c, N, fun env => by rw [stdClosedVal_asg]; exact h env⟩

/-! ### V3 — the structural-budget master predicate (block 6)

The block-8 predicate `BudgetedEmbedsTC` existentially bound the node ordinal `α` AND the
witness index `K` *per assignment*, which made the ω-rule `all` case demand a uniform root over
unbounded per-branch `(K_n, α_n)`.  **V3 dissolves both**: the node ordinal `α` and the budgets
`B,d,N,c` all live OUTSIDE `∀ env` (env-independent — as, in fact, every landed case builds them,
since rewriting preserves `complexity`), and the ONLY env-dependence is the slot's relativization
index, fixed as the canonical assignment sup `envSup env N`.  Then:
* **ordinal uniformization is free** — `β n := α` (structural, uniform over branches), root `osucc α`;
* **budget uniformization is `envSup_cons_le`** — the branch index `envSup (n:>ₙenv) N` is dominated
  by `max (envSup env N) n`, which is exactly the `allω` branch relativization `rel1 · n` (via
  `rel1_rel1`).  No unbounded `K_n`.
The absorbing-norm gate `Nlog α ≤ f 0` is maintained by the structural invariant `Nlog α ≤ B`
(`Nlog` absorbing under `osucc`/`+`), and the `Gexp`-domination field pays the `exs`/atomic witness
budgets (control tower absorbs term growth). -/
def BudgetedEmbedsV3 (Γ : Finset (SyntacticFormula ℒₒᵣ)) : Prop :=
  ∃ B d N : ℕ, ∃ e α : ONote, e.NF ∧ α.NF ∧ Nlog α ≤ B ∧
    ∀ env : ℕ → ℕ,
      Zef2TC α e (fun _ => True) (rel1 (ewRootSlot e B) (envSup env N)) d
        (Γ.image (fun φ => Embedding.asg env ▹ φ))

/-- `ewRootSlot` is monotone in the structural budget `B`. -/
theorem ewRootSlot_mono_B (e : ONote) {B B' : ℕ} (h : B ≤ B') (x : ℕ) :
    ewRootSlot e B x ≤ ewRootSlot e B' x := by
  simp only [ewRootSlot, rel1]
  have := hardy_monotone e (max_le_max h (le_refl x))
  omega

/-- The shifted-down assignment's sup is absorbed by one extra `N`. -/
theorem envSup_shift_le (env : ℕ → ℕ) (N : ℕ) :
    envSup (fun x => env (x + 1)) N ≤ envSup env (N + 1) := by
  refine Finset.sup_le fun x hx => ?_
  simp only [Finset.mem_range] at hx
  exact le_envSup (by omega : x + 1 < N + 1)

/-- **V3 `closed`** — the deterministic-complexity EM leaf (structural `α = ofNat (2·complexity+1)`,
budget `clog`; `envSup env 0 = 0`). -/
theorem budgetedEmbedsV3_closed {Γ : Finset (SyntacticFormula ℒₒᵣ)}
    (φ : SyntacticFormula ℒₒᵣ) (hp : φ ∈ Γ) (hn : ∼φ ∈ Γ) :
    BudgetedEmbedsV3 Γ := by
  refine ⟨clog (2 * φ.complexity + 1), 0, 0, 0, ONote.ofNat (2 * φ.complexity + 1),
    ONote.NF.zero, ONote.nf_ofNat _, Nlog_ofNat_le _, fun env => ?_⟩
  have hf1 := ewRootSlot_f1 (0 : ONote) (clog (2 * φ.complexity + 1))
  have hmono : Monotone (rel1 (ewRootSlot 0 (clog (2 * φ.complexity + 1))) (envSup env 0)) :=
    rel1_monotone hf1.1.monotone (envSup env 0)
  have hinfl : ∀ m, m ≤ rel1 (ewRootSlot 0 (clog (2 * φ.complexity + 1))) (envSup env 0) m :=
    rel1_infl (fun m => by have := hf1.2 m; omega) (envSup env 0)
  have hgate : clog (2 * (Embedding.asg env ▹ φ).complexity + 1)
      ≤ rel1 (ewRootSlot 0 (clog (2 * φ.complexity + 1))) (envSup env 0) 0 := by
    simp only [Semiformula.complexity_rew]
    exact le_relSlot_zero 0 _ _
  have hem : Zef2TC (ONote.ofNat (2 * (Embedding.asg env ▹ φ).complexity + 1)) (0 : ONote)
      (fun _ : ONote => True) (rel1 (ewRootSlot 0 (clog (2 * φ.complexity + 1))) (envSup env 0)) 0
      (Γ.image (fun ψ => Embedding.asg env ▹ ψ)) :=
    em_Zef2TC' (Embedding.asg env ▹ φ) hmono hinfl hgate
      (Finset.mem_image_of_mem _ hp)
      (by simpa using Finset.mem_image_of_mem (fun ψ => Embedding.asg env ▹ ψ) hn)
  rwa [show (Embedding.asg env ▹ φ).complexity = φ.complexity from by simp] at hem

/-- **V3 `verum`** — `verumR` at `α = 0`. -/
theorem budgetedEmbedsV3_verum {Γ : Finset (SyntacticFormula ℒₒᵣ)}
    (h : (⊤ : SyntacticFormula ℒₒᵣ) ∈ Γ) : BudgetedEmbedsV3 Γ := by
  refine ⟨0, 0, 0, 0, 0, ONote.NF.zero, ONote.NF.zero, by simp, fun env => ?_⟩
  have hmem : (⊤ : SyntacticFormula ℒₒᵣ) ∈ Γ.image (fun ψ => Embedding.asg env ▹ ψ) := by
    have := Finset.mem_image_of_mem (fun ψ => Embedding.asg env ▹ ψ) h; simpa using this
  exact Zef2TC.verumR (by simp) hmem

/-- **V3 `wk`** — image weakening; all structural budgets carried. -/
theorem budgetedEmbedsV3_wk {Δ Γ : Finset (SyntacticFormula ℒₒᵣ)}
    (hsub : Δ ⊆ Γ) (ih : BudgetedEmbedsV3 Δ) : BudgetedEmbedsV3 Γ := by
  obtain ⟨B, d, N, e, α, he, hαNF, hNlogB, ih⟩ := ih
  refine ⟨B, d, N, e, α, he, hαNF, hNlogB, fun env => ?_⟩
  exact (ih env).wk (ih env).gate (Finset.image_subset_image hsub)

/-- **V3 `or`** — single premise; `osucc` root, `B+1` for the `Nlog`/gate slack. -/
theorem budgetedEmbedsV3_or {Γ : Finset (SyntacticFormula ℒₒᵣ)}
    {φ ψ : SyntacticFormula ℒₒᵣ} (h : φ ⋎ ψ ∈ Γ)
    (ih : BudgetedEmbedsV3 (insert φ (insert ψ Γ))) : BudgetedEmbedsV3 Γ := by
  obtain ⟨B, d, N, e, α, he, hαNF, hNlogB, ih⟩ := ih
  refine ⟨B + 1, d, N, e, osucc α, he, osucc_NF hαNF, ?_, fun env => ?_⟩
  · have := Nlog_osucc_le hαNF; omega
  · have D := ih env
    rw [Finset.image_insert, Finset.image_insert] at D
    have D' := D.mono_f (fun x => relSlot_mono (Nat.le_succ B) (le_refl (envSup env N)) x)
    have hg : Nlog (osucc α) ≤ rel1 (ewRootSlot e (B + 1)) (envSup env N) 0 := by
      have hs := Nlog_osucc_le hαNF
      have hb := le_relSlot_zero e (B + 1) (envSup env N)
      omega
    have hor := Zef2TC.orI (α := osucc α) hg
      (Embedding.asg env ▹ φ) (Embedding.asg env ▹ ψ)
      (Zekd.lt_osucc hαNF) hαNF (osucc_NF hαNF) (clT α) D'
    have hmem : (Embedding.asg env ▹ φ ⋎ Embedding.asg env ▹ ψ)
        ∈ Γ.image (fun χ => Embedding.asg env ▹ χ) := by
      have := Finset.mem_image_of_mem (fun χ => Embedding.asg env ▹ χ) h; simpa using this
    rwa [Finset.insert_eq_self.mpr hmem] at hor

/-- **V3 `shift`** — the shifted assignment `fun x => env (x+1)`; the index absorbs into `N+1`
(`envSup_shift_le`).  Budgets and derivation carried. -/
theorem budgetedEmbedsV3_shift {Γ : Finset (SyntacticFormula ℒₒᵣ)}
    (ih : BudgetedEmbedsV3 Γ) : BudgetedEmbedsV3 (Γ.image Rewriting.shift) := by
  obtain ⟨B, d, N, e, α, he, hαNF, hNlogB, ih⟩ := ih
  refine ⟨B, d, N + 1, e, α, he, hαNF, hNlogB, fun env => ?_⟩
  have D := ih (fun x => env (x + 1))
  have himg : (Γ.image (Rewriting.shift : SyntacticFormula ℒₒᵣ → SyntacticFormula ℒₒᵣ)).image
        (fun φ => Embedding.asg env ▹ φ)
      = Γ.image (fun φ => Embedding.asg (fun x => env (x + 1)) ▹ φ) := by
    have hcompB : (Embedding.asg env).comp Rew.shift = Embedding.asg (fun x => env (x + 1)) := by
      ext x
      · exact Fin.elim0 x
      · simp [Embedding.asg, Rew.comp_app]
    rw [Finset.image_image]
    refine Finset.image_congr (fun ψ _ => ?_)
    show Embedding.asg env ▹ (Rew.shift ▹ ψ) = Embedding.asg (fun x => env (x + 1)) ▹ ψ
    rw [← TransitiveRewriting.comp_app, hcompB]
  rw [himg]
  exact D.mono_f (fun x => relSlot_mono (le_refl B) (envSup_shift_le env N) x)

/-- **V3 `all` — THE DECISIVE CASE (block-6 probe).**  The ω-rule closes under the structural-budget
predicate: the node ordinal is uniform (`β n := α`, root `osucc α`), and the env-local budget index
`envSup env N` is paid by the branch relativization `rel1 · n` via `envSup_cons_le`.  This validates
the V3 design — the block-8 `all` obstruction (unbounded per-branch `K_n, α_n`) is a predicate-shape
artifact, dissolved by moving `α`/budgets outside `∀ env`. -/
theorem budgetedEmbedsV3_all {Γ : Finset (SyntacticFormula ℒₒᵣ)}
    {φ : SyntacticSemiformula ℒₒᵣ 1} (h : ∀⁰ φ ∈ Γ)
    (ih : BudgetedEmbedsV3 (insert (Rewriting.free φ) (Γ.image Rewriting.shift))) :
    BudgetedEmbedsV3 Γ := by
  obtain ⟨B, d, N, e, α, he, hαNF, hNlogB, ih⟩ := ih
  refine ⟨B + 1, d, N, e, osucc α, he, osucc_NF hαNF, ?_, fun env => ?_⟩
  · have := Nlog_osucc_le hαNF; omega
  · -- the ω-family: each branch is the IH at `n :>ₙ env`, transported to the branch slot/operator
    have hfam : ∀ n, Zef2TC α e (adjoin (fun _ : ONote => True) n)
        (rel1 (rel1 (ewRootSlot e (B + 1)) (envSup env N)) n) d
        (insert (((Embedding.asg env).q ▹ φ)/[nm n])
          (Γ.image (fun ψ => Embedding.asg env ▹ ψ))) := by
      intro n
      have Dn := ih (n :>ₙ env)
      rw [Finset.image_insert] at Dn
      have hA : Embedding.asg (n :>ₙ env) ▹ (Rewriting.free φ)
          = ((Embedding.asg env).q ▹ φ)/[nm n] := by
        have hRew : (Embedding.asg (n :>ₙ env)).comp Rew.free
            = (Rew.subst ![nm n]).comp (Embedding.asg env).q := by
          ext x
          · refine Fin.cases ?_ (fun i => Fin.elim0 i) x
            simp [Embedding.asg, Rew.comp_app, ZinftyF.nm, GoodsteinPA.OperatorZinfty.nm]
          · simp [Embedding.asg, Rew.comp_app, ZinftyF.nm, GoodsteinPA.OperatorZinfty.nm]
        show Embedding.asg (n :>ₙ env) ▹ (Rew.free ▹ φ)
            = Rew.subst ![nm n] ▹ ((Embedding.asg env).q ▹ φ)
        rw [← TransitiveRewriting.comp_app, ← TransitiveRewriting.comp_app, hRew]
      have hB : (Γ.image Rewriting.shift).image (fun ψ => Embedding.asg (n :>ₙ env) ▹ ψ)
          = Γ.image (fun ψ => Embedding.asg env ▹ ψ) := by
        have hcompB : (Embedding.asg (n :>ₙ env)).comp Rew.shift = Embedding.asg env := by
          ext x
          · exact Fin.elim0 x
          · simp [Embedding.asg, Rew.comp_app]
        rw [Finset.image_image]
        refine Finset.image_congr (fun ψ _ => ?_)
        show Embedding.asg (n :>ₙ env) ▹ (Rew.shift ▹ ψ) = Embedding.asg env ▹ ψ
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
      ((Embedding.asg env).q ▹ φ) (fun _ => α)
      (fun _ => Zekd.lt_osucc hαNF) (fun _ => hαNF) (osucc_NF hαNF) hrel hfam
    have hmem : (Embedding.asg env ▹ (∀⁰ φ))
        ∈ Γ.image (fun ψ => Embedding.asg env ▹ ψ) := Finset.mem_image_of_mem _ h
    rw [show (Embedding.asg env ▹ (∀⁰ φ)) = ∀⁰ ((Embedding.asg env).q ▹ φ) by simp] at hmem
    rw [Finset.insert_eq_self.mpr hmem] at hall
    exact hall

/-- **V3 `and`** — two-premise join, all structural: control `osucc (e₁ + e₂)`, root
`osucc (α₁ + α₂)`, `B := max B₁ B₂ + norm e₁ + norm e₂ + 2` (covers the `Nlog` invariant AND
the `relSlot_le` norm gates), `N := max N₁ N₂`, `d := max d₁ d₂`.  Unlike block-8, the root
gate is FREE from the structural invariant (`Nlog root ≤ B ≤ slot 0`) — no succ-gap rung. -/
theorem budgetedEmbedsV3_and {Γ : Finset (SyntacticFormula ℒₒᵣ)}
    {φ ψ : SyntacticFormula ℒₒᵣ} (h : φ ⋏ ψ ∈ Γ)
    (ihp : BudgetedEmbedsV3 (insert φ Γ)) (ihq : BudgetedEmbedsV3 (insert ψ Γ)) :
    BudgetedEmbedsV3 Γ := by
  obtain ⟨B₁, d₁, N₁, e₁, α₁, he₁, hα₁NF, hN₁, ih₁⟩ := ihp
  obtain ⟨B₂, d₂, N₂, e₂, α₂, he₂, hα₂NF, hN₂, ih₂⟩ := ihq
  have headdNF : (e₁ + e₂).NF := by haveI := he₁; haveI := he₂; exact ONote.add_nf e₁ e₂
  have heNF : (osucc (e₁ + e₂)).NF := osucc_NF headdNF
  have hlt₁ : e₁ < osucc (e₁ + e₂) :=
    lt_of_le_of_lt (Zekd.le_add_right_NF he₁ he₂) (Zekd.lt_osucc headdNF)
  have hlt₂ : e₂ < osucc (e₁ + e₂) :=
    lt_of_le_of_lt (Zekd.le_add_left_NF he₁ he₂) (Zekd.lt_osucc headdNF)
  have haddNF : (α₁ + α₂).NF := by haveI := hα₁NF; haveI := hα₂NF; exact ONote.add_nf α₁ α₂
  set B := max B₁ B₂ + norm e₁ + norm e₂ + 2 with hB
  refine ⟨B, max d₁ d₂, max N₁ N₂, osucc (e₁ + e₂), osucc (α₁ + α₂),
    heNF, osucc_NF haddNF, ?_, fun env => ?_⟩
  · have hs := Nlog_osucc_le haddNF
    have ha := Nlog_add_le_max_succ α₁ hα₁NF α₂ hα₂NF
    omega
  · have hff₁ : ∀ x, rel1 (ewRootSlot e₁ B₁) (envSup env N₁) x
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
      (Embedding.asg env ▹ φ) (Embedding.asg env ▹ ψ)
      (lt_of_le_of_lt (Zekd.le_add_right_NF hα₁NF hα₂NF) (Zekd.lt_osucc haddNF))
      (lt_of_le_of_lt (Zekd.le_add_left_NF hα₁NF hα₂NF) (Zekd.lt_osucc haddNF))
      hα₁NF hα₂NF (osucc_NF haddNF) (clT α₁) (clT α₂) D₁' D₂'
    have hmem : (Embedding.asg env ▹ φ ⋏ Embedding.asg env ▹ ψ)
        ∈ Γ.image (fun χ => Embedding.asg env ▹ χ) := by
      have := Finset.mem_image_of_mem (fun χ => Embedding.asg env ▹ χ) h
      simpa using this
    rwa [Finset.insert_eq_self.mpr hmem] at hand

/-- **V3 `cut`** — the two-premise join of `and` with the cut rank `max`ed against
`φ.complexity + 1` and the read gate paid by absorbing `φ.complexity` into `B`
(rewriting preserves `complexity`, so this stays env-independent). -/
theorem budgetedEmbedsV3_cut {Γ : Finset (SyntacticFormula ℒₒᵣ)}
    {φ : SyntacticFormula ℒₒᵣ}
    (ihp : BudgetedEmbedsV3 (insert φ Γ)) (ihn : BudgetedEmbedsV3 (insert (∼φ) Γ)) :
    BudgetedEmbedsV3 Γ := by
  obtain ⟨B₁, d₁, N₁, e₁, α₁, he₁, hα₁NF, hN₁, ih₁⟩ := ihp
  obtain ⟨B₂, d₂, N₂, e₂, α₂, he₂, hα₂NF, hN₂, ih₂⟩ := ihn
  have headdNF : (e₁ + e₂).NF := by haveI := he₁; haveI := he₂; exact ONote.add_nf e₁ e₂
  have heNF : (osucc (e₁ + e₂)).NF := osucc_NF headdNF
  have hlt₁ : e₁ < osucc (e₁ + e₂) :=
    lt_of_le_of_lt (Zekd.le_add_right_NF he₁ he₂) (Zekd.lt_osucc headdNF)
  have hlt₂ : e₂ < osucc (e₁ + e₂) :=
    lt_of_le_of_lt (Zekd.le_add_left_NF he₁ he₂) (Zekd.lt_osucc headdNF)
  have haddNF : (α₁ + α₂).NF := by haveI := hα₁NF; haveI := hα₂NF; exact ONote.add_nf α₁ α₂
  set B := max B₁ B₂ + norm e₁ + norm e₂ + φ.complexity + 2 with hB
  refine ⟨B, max (max d₁ d₂) (φ.complexity + 1), max N₁ N₂, osucc (e₁ + e₂),
    osucc (α₁ + α₂), heNF, osucc_NF haddNF, ?_, fun env => ?_⟩
  · have hs := Nlog_osucc_le haddNF
    have ha := Nlog_add_le_max_succ α₁ hα₁NF α₂ hα₂NF
    omega
  · have hff₁ : ∀ x, rel1 (ewRootSlot e₁ B₁) (envSup env N₁) x
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
    rw [show Embedding.asg env ▹ (∼φ) = ∼(Embedding.asg env ▹ φ) by simp] at D₂'
    have hb := le_relSlot_zero (osucc (e₁ + e₂)) B (envSup env (max N₁ N₂))
    have hg : Nlog (osucc (α₁ + α₂))
        ≤ rel1 (ewRootSlot (osucc (e₁ + e₂)) B) (envSup env (max N₁ N₂)) 0 := by
      have hs := Nlog_osucc_le haddNF
      have ha := Nlog_add_le_max_succ α₁ hα₁NF α₂ hα₂NF
      omega
    have hread : (Embedding.asg env ▹ φ).complexity
        ≤ rel1 (ewRootSlot (osucc (e₁ + e₂)) B) (envSup env (max N₁ N₂)) 0 := by
      simp only [Semiformula.complexity_rew]
      omega
    have hcompl : (Embedding.asg env ▹ φ).complexity
        < max (max d₁ d₂) (φ.complexity + 1) := by
      simp only [Semiformula.complexity_rew]
      omega
    exact Zef2TC.cut hg (Embedding.asg env ▹ φ) hcompl hread
      (lt_of_le_of_lt (Zekd.le_add_right_NF hα₁NF hα₂NF) (Zekd.lt_osucc haddNF))
      (lt_of_le_of_lt (Zekd.le_add_left_NF hα₁NF hα₂NF) (Zekd.lt_osucc haddNF))
      hα₁NF hα₂NF (osucc_NF haddNF) (clT α₁) (clT α₂) D₁' D₂'

/-- **V3 `exs`** — the closed-term collapse with a STRUCTURAL witness budget.  The witness
`m = stdClosedVal (asg env t)` is env-dependent, but `stdClosedVal_asg_le_Gexp_iter` bounds it
by `Gexp^[c] (envSup env Nt)` with STRUCTURAL `(c, Nt)`; raising the control tower to
`e := osucc (e₁ + ω²·(c+1))` absorbs the iterate into a single Hardy value
(`Gexp_iter_eq_hardy`) dominated by the root slot (`hardy_le_of_lt`, `norm` gate paid by `B`).
The value-congruent EM + cut + `exI` assembly ports from block-8; the ordinal-join gates are
free from the structural `Nlog ≤ B` invariant. -/
theorem budgetedEmbedsV3_exs {Γ : Finset (SyntacticFormula ℒₒᵣ)}
    {φ : SyntacticSemiformula ℒₒᵣ 1} (h : ∃⁰ φ ∈ Γ) (t : SyntacticTerm ℒₒᵣ)
    (ih : BudgetedEmbedsV3 (insert (φ/[t]) Γ)) :
    BudgetedEmbedsV3 Γ := by
  obtain ⟨B₁, d₁, N₁, e₁, α₁, he₁, hα₁NF, hN₁, ih₁⟩ := ih
  obtain ⟨c, Nt, hdom⟩ := stdClosedVal_asg_le_Gexp_iter t
  -- the Gexp control tower `ω²·(c+1)` and the joined control `e`
  set c' : ℕ+ := ⟨c + 1, Nat.succ_pos c⟩ with hc'
  set eG : ONote := ONote.oadd (ONote.ofNat 2) c' 0 with heG
  have heGNF : eG.NF := (ONote.nf_ofNat 2).oadd c' ONote.NFBelow.zero
  have headdNF : (e₁ + eG).NF := by haveI := he₁; haveI := heGNF; exact ONote.add_nf e₁ eG
  have heNF : (osucc (e₁ + eG)).NF := osucc_NF headdNF
  set e : ONote := osucc (e₁ + eG) with he
  have hlt₁ : e₁ < e :=
    lt_of_le_of_lt (Zekd.le_add_right_NF he₁ heGNF) (Zekd.lt_osucc headdNF)
  have hltG : eG < e :=
    lt_of_le_of_lt (Zekd.le_add_left_NF he₁ heGNF) (Zekd.lt_osucc headdNF)
  set B : ℕ := B₁ + φ.complexity + clog (2 * φ.complexity + 1)
    + norm e₁ + norm eG + 3 with hB
  set d : ℕ := max d₁ (φ.complexity + 1) with hd
  set N : ℕ := max N₁ Nt with hN
  have hofNF : (ONote.ofNat (2 * φ.complexity + 1)).NF := ONote.nf_ofNat _
  have haddNF : (α₁ + ONote.ofNat (2 * φ.complexity + 1)).NF := by
    haveI := hα₁NF; haveI := hofNF; exact ONote.add_nf _ _
  refine ⟨B, d, N, e, osucc (osucc (α₁ + ONote.ofNat (2 * φ.complexity + 1))),
    heNF, osucc_NF (osucc_NF haddNF), ?_, fun env => ?_⟩
  · -- the structural `Nlog` invariant at the doubled-osucc root
    have h1 := Nlog_osucc_le (osucc_NF haddNF)
    have h2 := Nlog_osucc_le haddNF
    have h3 := Nlog_add_le_max_succ α₁ hα₁NF _ hofNF
    have h4 := Nlog_ofNat_le (2 * φ.complexity + 1)
    omega
  · set M : ℕ := envSup env N with hM
    set F : ℕ → ℕ := rel1 (ewRootSlot e B) M with hF
    set ψ' : SyntacticSemiformula ℒₒᵣ 1 := (Embedding.asg env).q ▹ φ with hψ'
    set s : SyntacticTerm ℒₒᵣ := Embedding.asg env t with hs
    set m : ℕ := stdClosedVal s with hm
    have hψc : ψ'.complexity = φ.complexity := by simp [hψ']
    have hf1 := ewRootSlot_f1 e B
    have hFmono : Monotone F := rel1_monotone hf1.1.monotone M
    have hFinfl : ∀ x, x ≤ F x := rel1_infl (fun x => by have := hf1.2 x; omega) M
    have hBF : B ≤ F 0 := le_relSlot_zero e B M
    -- the IH derivation, re-based to the joined control/budgets
    have D₁ := ih₁ env
    rw [Finset.image_insert, Embedding.rew_subst_term (Embedding.asg env) φ t] at D₁
    have hff : ∀ x, rel1 (ewRootSlot e₁ B₁) (envSup env N₁) x ≤ F x :=
      relSlot_le he₁ heNF hlt₁ (by omega)
        (envSup_mono_N env (le_max_left N₁ Nt)) (by omega)
    have D₁' := ((D₁.change_e e).mono_f hff).mono_c (c' := d) (le_max_left _ _)
    -- left cut premise: add ψ'/[nm m] to the context
    have Dsrc : Zef2TC α₁ e (fun _ => True) F d
        (insert (ψ'/[s]) (insert (ψ'/[nm m])
          (Γ.image (fun χ => Embedding.asg env ▹ χ)))) :=
      D₁'.wk D₁'.gate (Finset.insert_subset_insert _ (Finset.subset_insert _ _))
    -- right cut premise: value-congruent EM at the pair (nm m, s)
    have hgateEM : clog (2 * ψ'.complexity + 1) ≤ F 0 := by rw [hψc]; omega
    have Dcong : Zef2TC (ONote.ofNat (2 * ψ'.complexity + 1)) e (fun _ => True) F 0
        (insert (∼(ψ'/[s])) (insert (ψ'/[nm m])
          (Γ.image (fun χ => Embedding.asg env ▹ χ)))) := by
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
        (insert (ψ'/[nm m]) (Γ.image (fun χ => Embedding.asg env ▹ χ))) :=
      Zef2TC.cut hgcut (ψ'/[s]) hcompl hread
        (lt_of_le_of_lt (Zekd.le_add_right_NF hα₁NF hofNF) (Zekd.lt_osucc haddNF))
        (lt_of_le_of_lt (Zekd.le_add_left_NF hα₁NF hofNF) (Zekd.lt_osucc haddNF))
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
      (Zekd.lt_osucc (osucc_NF haddNF)) (osucc_NF haddNF)
      (osucc_NF (osucc_NF haddNF)) (clT _) hwit Dnum
    have hmem : (∃⁰ ψ') ∈ Γ.image (fun χ => Embedding.asg env ▹ χ) := by
      have := Finset.mem_image_of_mem (fun χ => Embedding.asg env ▹ χ) h
      simpa [hψ'] using this
    rwa [Finset.insert_eq_self.mpr hmem] at hexI

/-! ### The W1 kit — bounded truth for ∃-free formulas (the `axm` engine)

All PA⁻/EQ axioms except `addEqOfLt` are (∀-closures of) ∃-free matrices; a TRUE closed
∃-free formula is cut-free `Zef2TC`-derivable at the deterministic rung `ofNat (2k+1)` —
no witness budget at all (`exI` never fires).  `addEqOfLt` (witness `z = y - x ≤ y`, paid by
the branch slot) and the induction schema (cut-tower over `em_Zef2TC`) are the two bespoke
residues. -/

/-- No `∃⁰` anywhere (the Π-fragment over NNF).  Truth of such closed formulas needs no
witness data, so the bounded-truth derivation avoids `exI`'s slot gate entirely. -/
def ExFree : ∀ {n : ℕ}, SyntacticSemiformula ℒₒᵣ n → Prop
  | _, Semiformula.verum => True
  | _, Semiformula.falsum => True
  | _, Semiformula.rel _ _ => True
  | _, Semiformula.nrel _ _ => True
  | _, Semiformula.and φ ψ => ExFree φ ∧ ExFree ψ
  | _, Semiformula.or φ ψ => ExFree φ ∧ ExFree ψ
  | _, Semiformula.all φ => ExFree φ
  | _, Semiformula.exs _ => False

@[simp] theorem exFree_verum {n : ℕ} : ExFree (⊤ : SyntacticSemiformula ℒₒᵣ n) := trivial
@[simp] theorem exFree_falsum {n : ℕ} : ExFree (⊥ : SyntacticSemiformula ℒₒᵣ n) := trivial
@[simp] theorem exFree_rel {n k : ℕ} (r : (ℒₒᵣ).Rel k) (v) :
    ExFree (Semiformula.rel (n := n) r v) := trivial
@[simp] theorem exFree_nrel {n k : ℕ} (r : (ℒₒᵣ).Rel k) (v) :
    ExFree (Semiformula.nrel (n := n) r v) := trivial
@[simp] theorem exFree_and {n : ℕ} {φ ψ : SyntacticSemiformula ℒₒᵣ n} :
    ExFree (φ ⋏ ψ) ↔ ExFree φ ∧ ExFree ψ := Iff.rfl
@[simp] theorem exFree_or {n : ℕ} {φ ψ : SyntacticSemiformula ℒₒᵣ n} :
    ExFree (φ ⋎ ψ) ↔ ExFree φ ∧ ExFree ψ := Iff.rfl
@[simp] theorem exFree_all {n : ℕ} {φ : SyntacticSemiformula ℒₒᵣ (n + 1)} :
    ExFree (∀⁰ φ) ↔ ExFree φ := Iff.rfl
@[simp] theorem exFree_exs {n : ℕ} {φ : SyntacticSemiformula ℒₒᵣ (n + 1)} :
    ExFree (∃⁰ φ) ↔ False := Iff.rfl

/-- `ExFree` is stable under every rewriting (rewriting preserves the connective tree). -/
theorem ExFree.rew : ∀ {n₁ : ℕ} (ψ : SyntacticSemiformula ℒₒᵣ n₁), ExFree ψ →
    ∀ {n₂ : ℕ} (ω : Rew ℒₒᵣ ℕ n₁ ℕ n₂), ExFree (ω ▹ ψ) := by
  intro n₁ ψ
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
    ∀ (ψ : SyntacticFormula ℒₒᵣ), ψ.complexity ≤ k → ExFree ψ → atomTrue ψ →
    ∀ {e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {Γ : Seq},
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
            have hall : ∀ x : ℕ, GoodsteinPA.Compat.gEvalm ℕ ![x] (fun _ => 0) a := by
              simpa [atomTrue, Matrix.constant_eq_singleton, Matrix.empty_eq] using htrue
            simpa [atomTrue, Semiformula.eval_substs, Embedding.valm_nm,
              Matrix.constant_eq_singleton, Matrix.empty_eq] using hall m
          exact ih (a/[nm m]) hsk hsex hstrue
            (rel1_monotone hmono m) (rel1_infl hinfl m) (le_trans hg1 hf0m)
            (Finset.mem_insert_self _ _)
        have hall := Zef2TC.allω (α := ONote.ofNat (2 * k + 3)) hroot
          a (fun _ => ONote.ofNat (2 * k + 1)) (fun _ => hlt13)
          (fun _ => hNF _) (hNF _) (fun _ => Cl.ofNat _) fam
        rwa [Finset.insert_eq_self.mpr hmem] at hall
    | hexs a => exact absurd hex (by simp)

@[simp] theorem exFree_allClosure : ∀ {n : ℕ} {φ : SyntacticSemiformula ℒₒᵣ n},
    ExFree (∀⁰* φ) ↔ ExFree φ := by
  intro n
  induction n with
  | zero => intro φ; rfl
  | succ n ih => intro φ; rw [show (∀⁰* φ) = (∀⁰* (∀⁰ φ)) from rfl, ih]; exact exFree_all

/-- The closing assignment fixes embedded sentences (no fvars to rewrite). -/
theorem asg_emb_fix (env : ℕ → ℕ) (σ : Sentence ℒₒᵣ) :
    Embedding.asg env ▹ (↑σ : SyntacticFormula ℒₒᵣ) = ↑σ := by
  have hc : (Embedding.asg env).comp Rew.emb = (Rew.emb : Rew ℒₒᵣ Empty 0 ℕ 0) := by
    ext x
    · exact x.elim0
    · exact x.elim
  show Embedding.asg env ▹ (Rew.emb ▹ σ) = Rew.emb ▹ σ
  rw [← TransitiveRewriting.comp_app, hc]

/-- Truth transfer: a sentence true in `ℕ` stays `atomTrue` after embedding + any closing
assignment (`asg env` fixes the fvar-free embed; mirrors `embedC`'s `axm` truth step). -/
theorem atomTrue_asg_emb {σ : Sentence ℒₒᵣ} (h : ℕ ⊧ₘ σ) (env : ℕ → ℕ) :
    atomTrue (Embedding.asg env ▹ (↑σ : SyntacticFormula ℒₒᵣ)) := by
  simp only [atomTrue, Embedding.asg, Semiformula.eval_rewrite, Semiformula.eval_emb]
  rw [models_iff] at h
  simpa [Matrix.empty_eq] using h

/-- **The ∃-free `axm` wrapper**: a TRUE ∃-free PA-axiom sentence in `Γ` is budgeted-embeddable
outright — `truth_exFree_Zef2TC` at the V3 structural budget of the `closed` case. -/
theorem budgetedEmbedsV3_of_exFree_true {Γ : Finset (SyntacticFormula ℒₒᵣ)}
    (σ : Sentence ℒₒᵣ) (hex : ExFree (↑σ : SyntacticFormula ℒₒᵣ)) (htrue : ℕ ⊧ₘ σ)
    (hΓ : (↑σ : SyntacticFormula ℒₒᵣ) ∈ Γ) : BudgetedEmbedsV3 Γ := by
  set k : ℕ := (↑σ : SyntacticFormula ℒₒᵣ).complexity with hk
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
  have hcompl : (Embedding.asg env ▹ (↑σ : SyntacticFormula ℒₒᵣ)).complexity ≤ k := by
    simp [hk]
  exact truth_exFree_Zef2TC k _ hcompl (hex.rew _ _) (atomTrue_asg_emb htrue env)
    hmono hinfl hgate (Finset.mem_image_of_mem _ hΓ)


/-! ### The PA⁻ `axm` sweep -/

/-- **`addEqOfLt`** — the SOLE ∃-carrying PA⁻ axiom (`∀ x y, x < y → ∃ z, x + z = y`).
The witness `z = y - x ≤ y` is dominated by the second ω-branch numeral, hence by the branch
slot's relativization (`rel1 · y`) — no structural tower needed.  Bespoke `exI` assembly;
disclosed `sorry`, next E-1 block. -/
theorem budgetedEmbedsV3_addEqOfLt {Γ : Finset (SyntacticFormula ℒₒᵣ)}
    (hΓ : (↑(Arithmetic.PeanoMinus.Axiom.addEqOfLt) : SyntacticFormula ℒₒᵣ) ∈ Γ) :
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
  have himg : Embedding.asg env ▹ (↑(Arithmetic.PeanoMinus.Axiom.addEqOfLt)
        : SyntacticFormula ℒₒᵣ)
      = ∀⁰ ∀⁰ ((∼(Semiformula.rel Language.LT.lt ![#1, #0]))
          ⋎ (∃⁰ (Semiformula.rel Language.Eq.eq ![‘(#2 + #0)’, #1]))) := by
    rw [asg_emb_fix]
    simp only [Arithmetic.PeanoMinus.Axiom.addEqOfLt, Semiformula.Operator.eq_def,
      Semiformula.Operator.lt_def, Semiformula.imp_eq]
    simp [Function.comp_def]
    constructor <;> simp [Matrix.comp_vecCons]
  have hmem := Finset.mem_image_of_mem (fun χ => Embedding.asg env ▹ χ) hΓ
  rw [himg] at hmem
  set M : SyntacticSemiformula ℒₒᵣ 2 :=
    (∼(Semiformula.rel Language.LT.lt ![#1, #0]))
      ⋎ (∃⁰ (Semiformula.rel Language.Eq.eq ![‘(#2 + #0)’, #1])) with hM
  set Γ' : Seq := Γ.image (fun χ => Embedding.asg env ▹ χ) with hΓ'
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
      set A : SyntacticFormula ℒₒᵣ := ∼(Semiformula.rel Language.LT.lt ![nm a, nm b]) with hA
      set Eb : SyntacticSemiformula ℒₒᵣ 1 := (Rew.subst (nm b :> ![nm a])).q
        ▹ (Semiformula.rel Language.Eq.eq ![‘(#2 + #0)’, #1]) with hE
      set Δ : Seq := insert A (insert (∃⁰ Eb) Γ') with hΔ
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
theorem budgetedEmbedsV3_axm_PAminus {Γ : Finset (SyntacticFormula ℒₒᵣ)}
    (σ : Sentence ℒₒᵣ) (hσ : σ ∈ 𝗣𝗔⁻) (hΓ : (↑σ : SyntacticFormula ℒₒᵣ) ∈ Γ) :
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

/-! ### The induction-schema kit, part 1 — `osuccs` + the ∀-closure peel -/

/-- Iterated successor (the closure-peel ordinal ladder). -/
def osuccs (α : ONote) : ℕ → ONote
  | 0 => α
  | n + 1 => osucc (osuccs α n)

theorem osuccs_NF {α : ONote} (h : α.NF) : ∀ n, (osuccs α n).NF
  | 0 => h
  | n + 1 => osucc_NF (osuccs_NF h n)

theorem osuccs_succ_shift (α : ONote) : ∀ n, osuccs (osucc α) n = osucc (osuccs α n)
  | 0 => rfl
  | n + 1 => by simp only [osuccs, osuccs_succ_shift α n]

theorem Cl_osuccs {S : ONote → Prop} {α : ONote} (h : Cl S α) : ∀ n, Cl S (osuccs α n)
  | 0 => h
  | n + 1 => Cl.osucc (Cl_osuccs h n)

theorem Nlog_osuccs_le {α : ONote} (h : α.NF) : ∀ n, Nlog (osuccs α n) ≤ Nlog α + n
  | 0 => le_refl _
  | n + 1 => by
      have h1 := Nlog_osucc_le (osuccs_NF h n)
      have h2 := Nlog_osuccs_le h n
      simp only [osuccs]
      omega

/-- **∀-closure peel**: if every numeral instance of the `ℓ`-ary matrix is derivable at `α`
(uniformly in the operator/slot, `em_cong`-style stability), the universal closure is
derivable at `osuccs α ℓ`.  Instances feed through `embedding_subst_q_cons_app`; the
`Cl`-in-every-operator hypothesis pays every `relOp` side condition. -/
theorem allClosure_peel {e : ONote} {d : ℕ} {f₀ : ℕ → ℕ} :
    ∀ (ℓ : ℕ) (α : ONote), α.NF → (∀ S : ONote → Prop, Cl S α) →
      ∀ (χ : SyntacticSemiformula ℒₒᵣ ℓ) (Γ : Seq),
      (∀ (w : Fin ℓ → ℕ) (H : ONote → Prop) (f : ℕ → ℕ), Monotone f → (∀ m, m ≤ f m) →
          f₀ 0 ≤ f 0 →
          Zef2TC α e H f d (insert (Rew.subst (fun i => nm (w i)) ▹ χ) Γ)) →
      (∀ k, k ≤ ℓ → Nlog (osuccs α k) ≤ f₀ 0) →
      ∀ (H : ONote → Prop) (f : ℕ → ℕ), Monotone f → (∀ m, m ≤ f m) → f₀ 0 ≤ f 0 →
      Zef2TC (osuccs α ℓ) e H f d (insert (∀⁰* χ) Γ) := by
  intro ℓ
  induction ℓ with
  | zero =>
      intro α hNF hCl χ Γ hinst hg H f hmono hinfl hf0
      have h := hinst ![] H f hmono hinfl hf0
      have hs : Rew.subst (fun i => nm ((![] : Fin 0 → ℕ) i)) ▹ χ = χ := by
        have : (Rew.subst (fun i => nm ((![] : Fin 0 → ℕ) i)) : Rew ℒₒᵣ ℕ 0 ℕ 0)
            = Rew.subst ![] := by congr; funext i; exact i.elim0
        rw [this]
        simp
      rwa [hs] at h
  | succ n ih =>
      intro α hNF hCl χ Γ hinst hg H f hmono hinfl hf0
      have step : ∀ (w : Fin n → ℕ) (H' : ONote → Prop) (f' : ℕ → ℕ), Monotone f' →
          (∀ m, m ≤ f' m) → f₀ 0 ≤ f' 0 →
          Zef2TC (osucc α) e H' f' d
            (insert (Rew.subst (fun i => nm (w i)) ▹ (∀⁰ χ)) Γ) := by
        intro w H' f' hmono' hinfl' hf0'
        have hsub : Rew.subst (fun i => nm (w i)) ▹ (∀⁰ χ)
            = ∀⁰ ((Rew.subst (fun i => nm (w i))).q ▹ χ) := by simp
        rw [hsub]
        have fam : ∀ m, Zef2TC α e (adjoin H' m) (rel1 f' m) d
            (insert ((((Rew.subst (fun i => nm (w i))).q ▹ χ))/[nm m]) Γ) := by
          intro m
          have hf'm : f' 0 ≤ rel1 f' m 0 := by
            simpa [rel1] using hmono' (Nat.zero_le (max m 0))
          rw [embedding_subst_q_cons_app]
          have hv : (nm m :> fun i => nm (w i)) = (fun i => nm ((m :> w) i)) := by
            funext i
            refine Fin.cases ?_ (fun j => ?_) i <;> simp
          rw [hv]
          exact hinst (m :> w) (adjoin H' m) (rel1 f' m) (rel1_monotone hmono' m)
            (rel1_infl hinfl' m) (le_trans hf0' hf'm)
        have hgd : Nlog (osucc α) ≤ f' 0 := le_trans (hg 1 (by omega)) hf0'
        exact Zef2TC.allω hgd _ (fun _ => α) (fun _ => Zekd.lt_osucc hNF) (fun _ => hNF)
          (osucc_NF hNF) (fun m => hCl (adjoin H' m)) fam
      have h := ih (osucc α) (osucc_NF hNF) (fun S => Cl.osucc (hCl S)) (∀⁰ χ) Γ step
        (fun k hk => by
          rw [osuccs_succ_shift]
          exact hg (k + 1) (by omega))
        H f hmono hinfl hf0
      rw [osuccs_succ_shift] at h
      exact h


/-! ### The induction-schema kit, part 2 — `clog` gate arithmetic + the ω-root -/

/-- `2·⌈log⌉` is dominated by the argument (+3): `2·log₂(m+1) ≤ m+3`. -/
theorem two_mul_clog_le (m : ℕ) : 2 * clog m ≤ m + 3 := by
  have hkey : ∀ k : ℕ, 2 * k ≤ 2 ^ k + 2 := by
    intro k
    induction k with
    | zero => omega
    | succ k ih =>
        have h2 : 2 ^ k ≥ 1 := Nat.one_le_two_pow
        have : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by ring
        omega
  have hpow : 2 ^ Nat.log 2 (m + 1) ≤ m + 1 := Nat.pow_log_le_self 2 (by omega)
  have := hkey (Nat.log 2 (m + 1))
  simp only [clog]
  omega

/-- `clog` submultiplicativity: `clog (a·b) ≤ clog a + clog b + 1`. -/
theorem clog_mul_le (a b : ℕ) : clog (a * b) ≤ clog a + clog b + 1 := by
  rcases Nat.eq_zero_or_pos a with ha | ha
  · subst ha; simp
  rcases Nat.eq_zero_or_pos b with hb | hb
  · subst hb; simp
  have h1 : a + 1 < 2 ^ (clog a + 1) := by
    simpa [clog] using Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (a + 1)
  have h2 : b + 1 < 2 ^ (clog b + 1) := by
    simpa [clog] using Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (b + 1)
  have hle : a * b + 1 < 2 ^ (clog a + 1) * 2 ^ (clog b + 1) := by
    have hexp : (a + 1) * (b + 1) = a * b + a + b + 1 := by ring
    have : a * b + 1 ≤ (a + 1) * (b + 1) := by omega
    exact lt_of_le_of_lt this (Nat.mul_lt_mul'' h1 h2)
  rw [← pow_add] at hle
  have hfin : clog (a * b) < clog a + 1 + (clog b + 1) := by
    simpa [clog] using Nat.log_lt_of_lt_pow (by omega : a * b + 1 ≠ 0) hle
  omega

/-- **The tower-gate bound**: linear-in-`k` `ofNat` towers have `clog`-gates dominated by
`max n C` for the constant `C = 2·clog a + 12` — exactly what an arbitrary
monotone+inflationary slot pays at branch `n`. -/
theorem clog_tower_gate (a : ℕ) {k n : ℕ} (hk : k ≤ n) :
    clog (a * (k + 1)) ≤ max n (2 * clog a + 12) := by
  have h1 := clog_mul_le a (k + 1)
  have h2 : clog (k + 1) ≤ clog (n + 1) := clog_mono (by omega)
  have h3 := two_mul_clog_le (n + 1)
  omega

/-- The `ONote` `ω` is the closure element `expTower (ofNat 1)` — in every `Cl S`. -/
theorem omega_eq_expTower : (ONote.omega : ONote) = expTower (ONote.ofNat 1) := rfl

theorem omega_NF : (ONote.omega : ONote).NF := by
  rw [omega_eq_expTower]; exact expTower_NF (ONote.nf_ofNat 1)

theorem Cl_omega (S : ONote → Prop) : Cl S ONote.omega := by
  rw [omega_eq_expTower]; exact Cl.expTower (Cl.ofNat 1)

theorem ofNat_lt_omega (m : ℕ) : ONote.ofNat m < ONote.omega := by
  rw [ONote.lt_def, ONote.repr_ofNat,
    show ONote.omega.repr = Ordinal.omega0 from by simp [ONote.omega]]
  exact Ordinal.natCast_lt_omega0 m

theorem Nlog_omega : Nlog ONote.omega = 2 := by
  show Nlog (ONote.oadd 1 1 0) = 2
  have h2 : Nat.log 2 2 = 1 := by decide
  show max (Nlog (1 : ONote) + clog 1) (Nlog 0) = 2
  have h1 : Nlog (1 : ONote) = 1 := by
    show max (Nlog 0 + clog 1) (Nlog 0) = 1
    simp [clog, h2]
  simp [h1, clog, h2]

/-! ### The induction-schema kit, part 3 — `succInd` rewriting naturality over `ℒₒᵣ`
(ports of `EmbeddingX.subst1_comp_bShift` / `rew_subst1_comm_q` / `rew_succInd` /
`succInd_nnf` off `LX`). -/

/-- A degree-1 substitution fixes a `bShift`ed term. -/
theorem subst1_comp_bShift' (t : Semiterm ℒₒᵣ ℕ 1) :
    (Rew.subst ![t]).comp Rew.bShift = (Rew.bShift : Rew ℒₒᵣ ℕ 0 ℕ 1) := by
  ext y
  · exact Fin.elim0 y
  · simp [Rew.comp_app]

/-- `g.q` commutes with substituting a `g.q`-fixed term for the leading bvar. -/
theorem rew_subst1_comm_q' (g : SyntacticRew ℒₒᵣ 0 0) (φ : SyntacticSemiformula ℒₒᵣ 1)
    (t : Semiterm ℒₒᵣ ℕ 1) (ht : g.q t = t) :
    g.q ▹ (φ/[t]) = (g.q ▹ φ)/[t] := by
  show g.q ▹ (Rew.subst ![t] ▹ φ) = Rew.subst ![t] ▹ (g.q ▹ φ)
  have heq : (g.q).comp (Rew.subst ![t]) = (Rew.subst ![t]).comp g.q := by
    ext x
    · cases x using Fin.cases with
      | zero => simp [Rew.comp_app, ht]
      | succ i => exact Fin.elim0 i
    · rw [Rew.comp_app, Rew.comp_app, Rew.subst_fvar, Rew.q_fvar]
      show Rew.bShift (g &x) = ((Rew.subst ![t]).comp Rew.bShift) (g &x)
      rw [subst1_comp_bShift']
  rw [← TransitiveRewriting.comp_app, ← TransitiveRewriting.comp_app, heq]

/-- **`succInd` commutes with a closed rewriting** (`ℒₒᵣ` port of `EmbeddingX.rew_succInd`). -/
theorem rew_succInd' (g : SyntacticRew ℒₒᵣ 0 0) (ψ : Semiformula ℒₒᵣ ℕ 1) :
    g ▹ (Arithmetic.succInd ψ) = Arithmetic.succInd (g.q ▹ ψ) := by
  unfold Arithmetic.succInd
  simp only [Nat.reduceAdd, Fin.Fin1.eq_one, Fin.isValue, Rewriting.subst1_bvar0_eq,
    LogicalConnective.HomClass.map_imply, Rewriting.app_all, Semiformula.imp_inj,
    Semiformula.all_inj, true_and, and_true]
  refine ⟨?_, ?_⟩
  · rw [Embedding.rew_subst_term g ψ (↑(0 : ℕ))]
    congr 1
    simp
  · rw [rew_subst1_comm_q' g ψ (‘(#0 + 1)’ : Semiterm ℒₒᵣ ℕ 1) (by simp)]

/-- The NNF of `succInd ψ` — the three Tait components. -/
theorem succInd_nnf' (ψ : Semiformula ℒₒᵣ ℕ 1) :
    Arithmetic.succInd ψ = (∼ψ/[(↑(0 : ℕ) : Semiterm ℒₒᵣ ℕ 0)]) ⋎
      ((∃⁰ ∼((∼ψ/[(#0 : Semiterm ℒₒᵣ ℕ 1)]) ⋎ ψ/[(‘(#0 + 1)’ : Semiterm ℒₒᵣ ℕ 1)])) ⋎
        (∀⁰ ψ/[(#0 : Semiterm ℒₒᵣ ℕ 1)])) := by
  conv_lhs => unfold Arithmetic.succInd
  simp only [Semiformula.imp_eq, Semiformula.neg_all]

/-! ### The induction-schema kit, part 4 — the succInd cut-tower at root `ω`

Per numeral branch `n`, a `≤ n`-long chain of cuts `D_k ⊢ ψ(k), Δ` climbs the linear `ofNat`
ladder `a·(k+1)` (`a := 2·complexity+4`): `D_0` is the value-congruent EM at `(nm 0, t0)`,
`D_{k+1}` cuts `ψ(nm k)` against the fired step disjunct (`exI` at witness `k`, `andI`, EM +
value-congruent EM at `(nm (k+1), succT k)`).  The branch ordinals are UNBOUNDED but all
`< ω`, and their `Nlog ≈ clog(a·(k+1))` gates are paid by the branch slot `rel1 f n`
via `clog_tower_gate` (`max n C`-domination — log beats linear).  The `allω` root is `ω`. -/

set_option maxHeartbeats 1000000 in
theorem metaInduction_Zef2TC (ψ step : SyntacticSemiformula ℒₒᵣ 1)
    (t0 : SyntacticTerm ℒₒᵣ) (succT : ℕ → SyntacticTerm ℒₒᵣ)
    (hval0 : stdClosedVal t0 = 0)
    (hsval : ∀ n, stdClosedVal (succT n) = n + 1)
    (hstep : ∀ n, (∼step)/[nm n] = (ψ/[nm n]) ⋏ ∼(ψ/[succT n]))
    {e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {Γ : Seq}
    (hmono : Monotone f) (hinfl : ∀ m, m ≤ f m)
    (hg1 : 2 * clog (2 * ψ.complexity + 4) + 12 ≤ f 0)
    (hg2 : ψ.complexity ≤ f 0) :
    Zef2TC ONote.omega e H f (ψ.complexity + 1)
      (insert (∀⁰ ψ) (insert (∼(ψ/[t0])) (insert (∃⁰ (∼step)) Γ))) := by
  set c : ℕ := ψ.complexity + 1 with hc
  set a : ℕ := 2 * ψ.complexity + 4 with ha
  set Δ : Seq := insert (∼(ψ/[t0])) (insert (∃⁰ (∼step)) Γ) with hΔ
  have hNF : ∀ m : ℕ, (ONote.ofNat m).NF := fun m => ONote.nf_ofNat m
  have chain : ∀ n k, k ≤ n →
      Zef2TC (ONote.ofNat (a * (k + 1))) e (adjoin H n) (rel1 f n) c
        (insert (ψ/[nm k]) Δ) := by
    intro n
    have hFmono : Monotone (rel1 f n) := rel1_monotone hmono n
    have hFinfl : ∀ m, m ≤ rel1 f n m := rel1_infl hinfl n
    have hf0n : f 0 ≤ rel1 f n 0 := by simpa [rel1] using hmono (Nat.zero_le (max n 0))
    have hnF : n ≤ rel1 f n 0 := by
      have := hinfl (max n 0)
      simp only [rel1]
      omega
    have hconst : ∀ m, m ≤ 2 * a → clog m ≤ rel1 f n 0 := by
      intro m hm
      have h1 := clog_mono hm
      have h2 := clog_mul_le 2 a
      have h3 : clog 2 ≤ 2 := by decide
      omega
    have htower : ∀ k, k ≤ n → clog (a * (k + 1)) ≤ rel1 f n 0 := by
      intro k hk
      have h1 := clog_tower_gate a (n := n) hk
      have h2 : 2 * clog a + 12 ≤ rel1 f n 0 := le_trans hg1 hf0n
      omega
    have hcxk : ∀ (t : SyntacticTerm ℒₒᵣ), (ψ/[t]).complexity = ψ.complexity := by
      intro t; simp
    intro k
    induction k with
    | zero =>
        intro _
        have hgEM : clog (2 * ψ.complexity + 1) ≤ rel1 f n 0 :=
          hconst _ (by omega)
        have hem : Zef2TC (ONote.ofNat (2 * ψ.complexity + 1)) e (adjoin H n) (rel1 f n) c
            (insert (ψ/[nm 0]) Δ) :=
          (em_cong1_Zef2TC (nm 0) t0 (by simp [hval0]) ψ
            hFmono hFinfl hgEM
            (Finset.mem_insert_self _ _)
            (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))).mono_c
            (c' := c) (Nat.zero_le c)
        refine Zef2TC.weak ?_ (ofNat_lt_ofNat (by omega)) (hNF _) (hNF _)
          (Cl.ofNat _) (Finset.Subset.refl _) hem
        exact le_trans (Nlog_ofNat_le _) (htower 0 (Nat.zero_le n))
    | succ k ih =>
        intro hk1
        have hkn : k ≤ n := Nat.le_of_succ_le hk1
        have Dk := ih hkn
        set X : Seq := insert (∼(ψ/[nm k])) (insert (ψ/[nm (k + 1)]) Δ) with hX
        have hgEM : clog (2 * ψ.complexity + 1) ≤ rel1 f n 0 := hconst _ (by omega)
        -- left EM leaf: ψ(nm k) vs ∼ψ(nm k)
        have hL : Zef2TC (ONote.ofNat (2 * ψ.complexity + 1)) e (adjoin H n) (rel1 f n) c
            (insert (ψ/[nm k]) X) := by
          have h : Zef2TC (ONote.ofNat (2 * (ψ/[nm k]).complexity + 1)) e (adjoin H n)
              (rel1 f n) c (insert (ψ/[nm k]) X) :=
            (em_Zef2TC' (ψ/[nm k]) hFmono hFinfl
              (by rw [hcxk]; exact hgEM)
              (Finset.mem_insert_self _ _)
              (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))).mono_c
              (c' := c) (Nat.zero_le c)
          rwa [hcxk] at h
        -- right EM leaf: value-congruent pair (nm (k+1), succT k)
        have hR : Zef2TC (ONote.ofNat (2 * ψ.complexity + 1)) e (adjoin H n) (rel1 f n) c
            (insert (∼(ψ/[succT k])) X) :=
          (em_cong1_Zef2TC (nm (k + 1)) (succT k) (by simp [hsval]) ψ
            hFmono hFinfl hgEM
            (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
              (Finset.mem_insert_self _ _)))
            (Finset.mem_insert_self _ _)).mono_c (c' := c) (Nat.zero_le c)
        -- andI + exI: fire the step disjunct at witness k
        have hand := Zef2TC.andI (α := ONote.ofNat (2 * ψ.complexity + 2))
          (le_trans (Nlog_ofNat_le _) (hconst _ (by omega)))
          _ _ (ofNat_lt_ofNat (by omega)) (ofNat_lt_ofNat (by omega))
          (hNF _) (hNF _) (hNF _) (Cl.ofNat _) (Cl.ofNat _) hL hR
        rw [← hstep k] at hand
        have hex := Zef2TC.exI (α := ONote.ofNat (2 * ψ.complexity + 3))
          (le_trans (Nlog_ofNat_le _) (hconst _ (by omega)))
          (∼step) k (ofNat_lt_ofNat (by omega)) (hNF _) (hNF _) (Cl.ofNat _)
          (le_trans (le_trans hkn hnF) (le_refl _)) hand
        rw [Finset.insert_eq_self.mpr
          (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
            (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))))] at hex
        -- the cut on ψ(nm k), root a·(k+2)
        have hmul1 : a * (k + 1 + 1) = a * (k + 1) + a := by ring
        have hmul2 : a ≤ a * (k + 1) := Nat.le_mul_of_pos_right a (by omega)
        have d₁ : Zef2TC (ONote.ofNat (a * (k + 1))) e (adjoin H n) (rel1 f n) c
            (insert (ψ/[nm k]) (insert (ψ/[nm (k + 1)]) Δ)) :=
          Dk.wk Dk.gate (Finset.insert_subset_insert _ (Finset.subset_insert _ _))
        exact Zef2TC.cut
          (le_trans (Nlog_ofNat_le _) (htower (k + 1) hk1))
          (ψ/[nm k]) (by rw [hcxk]; omega) (by rw [hcxk]; exact le_trans hg2 hf0n)
          (ofNat_lt_ofNat (by omega)) (ofNat_lt_ofNat (by omega))
          (hNF _) (hNF _) (hNF _) (Cl.ofNat _) (Cl.ofNat _) d₁ hex
  have hroot : Nlog ONote.omega ≤ f 0 := by rw [Nlog_omega]; omega
  exact Zef2TC.allω hroot ψ (fun n => ONote.ofNat (a * (n + 1)))
    (fun n => ofNat_lt_omega _) (fun n => hNF _) omega_NF
    (fun n => Cl.ofNat _) (fun n => chain n n le_rfl)

/-! ### The induction-schema kit, part 5 — the per-instance succInd shape, and the V3 case -/

/-- The successor term of the induction step, at numeral `n`. -/
noncomputable def succTerm (n : ℕ) : SyntacticTerm ℒₒᵣ :=
  Rew.subst ![nm n] (‘(#0 + 1)’ : Semiterm ℒₒᵣ ℕ 1)

theorem stdClosedVal_succTerm (n : ℕ) : stdClosedVal (succTerm n) = n + 1 := by
  simp [succTerm, stdClosedVal, Matrix.empty_eq, nm]

/-- **The succInd instance shape**: any (rewritten) induction-axiom instance
`succInd ψw` is `Zef2TC`-derivable at the FIXED structural root `osucc² ω` — the ω-root
cut-tower `metaInduction_Zef2TC` plus the two `orI` peels of the NNF. -/
theorem succInd_shape_Zef2TC (ψw : SyntacticSemiformula ℒₒᵣ 1)
    {e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {Γ : Seq}
    (hmono : Monotone f) (hinfl : ∀ m, m ≤ f m)
    (hg1 : 2 * clog (2 * ψw.complexity + 4) + 12 ≤ f 0)
    (hg2 : ψw.complexity ≤ f 0) :
    Zef2TC (osucc (osucc ONote.omega)) e H f (ψw.complexity + 1)
      (insert (Arithmetic.succInd ψw) Γ) := by
  rw [succInd_nnf' ψw]
  set t0 : SyntacticTerm ℒₒᵣ := (↑(0 : ℕ) : Semiterm ℒₒᵣ ℕ 0) with ht0
  set stepw : SyntacticSemiformula ℒₒᵣ 1 :=
    (∼ψw/[(#0 : Semiterm ℒₒᵣ ℕ 1)]) ⋎ ψw/[(‘(#0 + 1)’ : Semiterm ℒₒᵣ ℕ 1)] with hstepw
  have hval0 : stdClosedVal t0 = 0 := by simp [ht0, stdClosedVal]
  have hstep : ∀ n, (∼stepw)/[nm n] = (ψw/[nm n]) ⋏ ∼(ψw/[succTerm n]) := by
    intro n
    simp only [hstepw, succTerm]
    simp [← TransitiveRewriting.comp_app, Rew.subst_comp_subst]
  have ht := metaInduction_Zef2TC ψw stepw t0 succTerm hval0 stdClosedVal_succTerm hstep
    (e := e) (H := H) (Γ := Γ) hmono hinfl hg1 hg2
  have hb : ψw/[(#0 : Semiterm ℒₒᵣ ℕ 1)] = ψw := by simp
  -- gates for the two orI peels
  have hNs : Nlog (osucc ONote.omega) ≤ 3 := by
    have := Nlog_osucc_le omega_NF; rw [Nlog_omega] at this; omega
  have hNss : Nlog (osucc (osucc ONote.omega)) ≤ 4 := by
    have := Nlog_osucc_le (osucc_NF omega_NF); omega
  -- reorder for the inner orI
  have hre : Zef2TC ONote.omega e H f (ψw.complexity + 1)
      (insert (∃⁰ (∼stepw)) (insert (∀⁰ ψw)
        (insert (∼(ψw/[t0])) Γ))) :=
    ht.wk ht.gate (by intro x hx; simp only [Finset.mem_insert] at hx ⊢; tauto)
  have horI₂ := Zef2TC.orI (α := osucc ONote.omega)
    (le_trans hNs (le_trans (by omega : (3:ℕ) ≤ 12) (le_trans (by omega) hg1)))
    (∃⁰ (∼stepw)) (∀⁰ ψw) (Zekd.lt_osucc omega_NF) omega_NF (osucc_NF omega_NF)
    (Cl_omega H) hre
  have hre₂ : Zef2TC (osucc ONote.omega) e H f (ψw.complexity + 1)
      (insert (∼(ψw/[t0])) (insert ((∃⁰ (∼stepw)) ⋎ (∀⁰ ψw)) Γ)) :=
    horI₂.wk horI₂.gate (by intro x hx; simp only [Finset.mem_insert] at hx ⊢; tauto)
  have horI₁ := Zef2TC.orI (α := osucc (osucc ONote.omega))
    (le_trans hNss (le_trans (by omega : (4:ℕ) ≤ 12) (le_trans (by omega) hg1)))
    (∼(ψw/[t0])) ((∃⁰ (∼stepw)) ⋎ (∀⁰ ψw)) (Zekd.lt_osucc (osucc_NF omega_NF))
    (osucc_NF omega_NF) (osucc_NF (osucc_NF omega_NF)) (Cl.osucc (Cl_omega H)) hre₂
  rw [hb]
  exact horI₁

/-- **V3 `axm`, the induction schema** — the LAST V3 ladder rung.  The `univCl (succInd φ)`
sentence is env-fixed (`asg_emb_fix`), coerces to `∀⁰* (fixitr ▹ succInd φ)`, and peels by
`allClosure_peel` into numeral instances `succInd ψw` handled by `succInd_shape_Zef2TC` at the
uniform root `osucc² ω` — total root `osuccs (osucc² ω) fvSup`, all budgets structural. -/
theorem budgetedEmbedsV3_succInd {Γ : Finset (SyntacticFormula ℒₒᵣ)}
    (φ : Semiformula ℒₒᵣ ℕ 1)
    (hΓ : (↑(Semiformula.univCl (Arithmetic.succInd φ)) : SyntacticFormula ℒₒᵣ) ∈ Γ) :
    BudgetedEmbedsV3 Γ := by
  set ℓ : ℕ := (Arithmetic.succInd φ).fvSup with hℓ
  set B : ℕ := 2 * clog (2 * φ.complexity + 4) + φ.complexity + ℓ + 20 with hB
  set α₀ : ONote := osucc (osucc ONote.omega) with hα₀
  have hα₀NF : α₀.NF := osucc_NF (osucc_NF omega_NF)
  have hα₀Cl : ∀ S : ONote → Prop, Cl S α₀ := fun S => Cl.osucc (Cl.osucc (Cl_omega S))
  have hNlogα₀ : Nlog α₀ ≤ 4 := by
    rw [hα₀]
    have h1 := Nlog_osucc_le omega_NF
    have h2 := Nlog_osucc_le (osucc_NF omega_NF)
    rw [Nlog_omega] at h1
    omega
  refine ⟨B, φ.complexity + 1, 0, 0, osuccs α₀ (0 + ℓ), ONote.NF.zero,
    osuccs_NF hα₀NF (0 + ℓ), ?_, fun env => ?_⟩
  · exact le_trans (Nlog_osuccs_le hα₀NF (0 + ℓ)) (by omega)
  · have hmem := Finset.mem_image_of_mem (fun χ => Embedding.asg env ▹ χ) hΓ
    rw [asg_emb_fix] at hmem
    have hcoe : (↑(Semiformula.univCl (Arithmetic.succInd φ)) : SyntacticFormula ℒₒᵣ)
        = ∀⁰* (Rew.fixitr 0 ℓ ▹ (Arithmetic.succInd φ)) := by
      rw [Semiformula.coe_univCl_eq_univCl']; rfl
    rw [hcoe] at hmem
    have hf1 := ewRootSlot_f1 (0 : ONote) B
    have hmono : Monotone (rel1 (ewRootSlot 0 B) (envSup env 0)) :=
      rel1_monotone hf1.1.monotone _
    have hinfl : ∀ m, m ≤ rel1 (ewRootSlot 0 B) (envSup env 0) m :=
      rel1_infl (fun m => by have := hf1.2 m; omega) _
    have hf0 : B ≤ rel1 (ewRootSlot 0 B) (envSup env 0) 0 := le_relSlot_zero 0 B _
    have hinst : ∀ (w : Fin (0 + ℓ) → ℕ) (H : ONote → Prop) (f : ℕ → ℕ), Monotone f →
        (∀ m, m ≤ f m) → (fun _ : ℕ => B) 0 ≤ f 0 →
        Zef2TC α₀ 0 H f (φ.complexity + 1)
          (insert (Rew.subst (fun i => nm (w i)) ▹ (Rew.fixitr 0 ℓ ▹ (Arithmetic.succInd φ)))
            (Γ.image (fun χ => Embedding.asg env ▹ χ))) := by
      intro w H f hmono' hinfl' hf0'
      rw [← TransitiveRewriting.comp_app, rew_succInd']
      set ψw : SyntacticSemiformula ℒₒᵣ 1 :=
        ((Rew.subst fun i => nm (w i)).comp (Rew.fixitr 0 ℓ)).q ▹ φ with hψw
      have hcx : ψw.complexity = φ.complexity := by simp [hψw]
      have hBle : B ≤ f 0 := hf0'
      have h := succInd_shape_Zef2TC ψw (e := 0) (H := H)
        (Γ := Γ.image (fun χ => Embedding.asg env ▹ χ)) hmono' hinfl'
        (by rw [hcx]; exact le_trans (by rw [hB]; omega) hBle)
        (by rw [hcx]; exact le_trans (by rw [hB]; omega) hBle)
      rwa [hcx] at h
    have hpeel := allClosure_peel (f₀ := fun _ => B) (0 + ℓ) α₀ hα₀NF hα₀Cl
      (Rew.fixitr 0 ℓ ▹ (Arithmetic.succInd φ))
      (Γ.image (fun χ => Embedding.asg env ▹ χ)) hinst
      (fun k hk => by
        have h1 := Nlog_osuccs_le hα₀NF k
        have h2 := hNlogα₀
        show Nlog (osuccs α₀ k) ≤ B
        rw [hB]
        omega)
      (fun _ => True) (rel1 (ewRootSlot 0 B) (envSup env 0)) hmono hinfl hf0
    rwa [Finset.insert_eq_self.mpr hmem] at hpeel

/-! ### The V3 `axm` dispatcher and the assembled V3 master ladder -/

/-- **V3 `axm`, complete**: every 𝗣𝗔 axiom in `Γ` is budgeted-embeddable — 𝗣𝗔 splits as
𝗣𝗔⁻ (`budgetedEmbedsV3_axm_PAminus`) + the universal induction scheme
(`budgetedEmbedsV3_succInd`). -/
theorem budgetedEmbedsV3_axm {Γ : Finset (SyntacticFormula ℒₒᵣ)}
    (σ : Sentence ℒₒᵣ) (hσ : σ ∈ (𝗣𝗔 : Theory ℒₒᵣ))
    (hΓ : (↑σ : SyntacticFormula ℒₒᵣ) ∈ Γ) : BudgetedEmbedsV3 Γ := by
  have hsplit : σ ∈ (𝗣𝗔⁻ : Theory ℒₒᵣ) ∨ σ ∈ Arithmetic.InductionScheme ℒₒᵣ Set.univ := by
    simpa [Arithmetic.Peano, Set.mem_union] using hσ
  rcases hsplit with h | h
  · exact budgetedEmbedsV3_axm_PAminus σ h hΓ
  · obtain ⟨φ, -, rfl⟩ := h
    exact budgetedEmbedsV3_succInd φ hΓ

/-- **The V3 master ladder, assembled — ALL TEN CASES SORRY-FREE**: every `Derivation2`
from 𝗣𝗔 is budgeted-embeddable into `Zef2TC` under the structural-budget predicate
`BudgetedEmbedsV3`.  This is the rung-E embedding content, complete (judge input;
NOT self-ratified into src per the directive). -/
theorem budgetedEmbeddingV3 {Γ : Finset (SyntacticFormula ℒₒᵣ)}
    (d : Derivation2 (𝗣𝗔 : Theory ℒₒᵣ) Γ) :
    BudgetedEmbedsV3 Γ := by
  induction d with
  | closed Γ φ hp hn => exact budgetedEmbedsV3_closed φ hp hn
  | axm φ hφ hΓ => exact budgetedEmbedsV3_axm φ hφ hΓ
  | verum h => exact budgetedEmbedsV3_verum h
  | @and Γ φ ψ h _dp _dq ihp ihq => exact budgetedEmbedsV3_and h ihp ihq
  | @or Γ φ ψ h _d ih => exact budgetedEmbedsV3_or h ih
  | @all Γ φ h _d ih => exact budgetedEmbedsV3_all h ih
  | @exs Γ φ h t _d ih => exact budgetedEmbedsV3_exs h t ih
  | @wk Δ Γ _d hsub ih => exact budgetedEmbedsV3_wk hsub ih
  | @shift Γ _d ih => exact budgetedEmbedsV3_shift ih
  | @cut Γ φ _dp _dn ihp ihn => exact budgetedEmbedsV3_cut ihp ihn

/-! ### allω INVERSION — the E→R/D seam converter

The rungs R/D consume per-instance SINGLETONS `{body/[nm m]}`, while the V3 master ladder
concludes at the ∀-sentence.  Inversion replays the derivation at branch slot `rel1 f m`,
replacing `∀⁰ φ` by its `m`-th numeral instance throughout.  Operators are phantoms in
`Zef2TC` (`change_H`), so only the slot/gate bookkeeping is live: every gate `≤ f 0` lifts
to `≤ rel1 f m 0` by monotonicity, and nested ω-branches commute via `rel1_rel1`+`max_comm`. -/

set_option maxHeartbeats 1600000 in
theorem allω_inversion {φ : SyntacticSemiformula ℒₒᵣ 1} (m : ℕ) :
    ∀ {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Seq},
      Zef2TC α e H f c Γ → Monotone f →
      Zef2TC α e H (rel1 f m) c (insert (φ/[nm m]) (Γ.erase (∀⁰ φ))) := by
  have hkey : ∀ (f : ℕ → ℕ), Monotone f → ∀ x, f x ≤ rel1 f m x := by
    intro f hmono x
    exact hmono (le_max_right m x)
  -- re-shape an inverted premise `insert inst ((insert χ Γ).erase ∀φ)` into the
  -- rebuilt rule's premise `insert χ (insert inst (Γ.erase ∀φ))`
  have hreshape : ∀ (χ : Form) (Γ : Seq),
      insert (φ/[nm m]) ((insert χ Γ).erase (∀⁰ φ))
        ⊆ insert χ (insert (φ/[nm m]) (Γ.erase (∀⁰ φ))) := by
    intro χ Γ x hx
    simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
    tauto
  -- targets: conclusion reshaping `insert χ (insert inst (Γ.erase ∀φ)) ⊇ goal` when χ ∈ Γ-form
  intro α e H F c Γ dd
  induction dd with
  | axL hαN r v hp hn =>
      intro hmono
      refine Zef2TC.axL (le_trans hαN (hkey _ hmono 0)) r v ?_ ?_
      · exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨by simp, hp⟩)
      · exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨by simp, hn⟩)
  | trueRel hαN r v htrue hmem =>
      intro hmono
      exact Zef2TC.trueRel (le_trans hαN (hkey _ hmono 0)) r v htrue
        (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨by simp, hmem⟩))
  | trueNrel hαN r v htrue hmem =>
      intro hmono
      exact Zef2TC.trueNrel (le_trans hαN (hkey _ hmono 0)) r v htrue
        (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨by simp, hmem⟩))
  | verumR hαN h =>
      intro hmono
      exact Zef2TC.verumR (le_trans hαN (hkey _ hmono 0))
        (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨by simp, h⟩))
  | wk hαN hsub _ ih =>
      intro hmono
      exact Zef2TC.wk (le_trans hαN (hkey _ hmono 0))
        (Finset.insert_subset_insert _ (Finset.erase_subset_erase _ hsub)) (ih hmono)
  | @weak α' β' e' H' F' c' Δ' Γ' hαN hβ hβNF hαNF hβH hsub _ ih =>
      intro hmono
      exact Zef2TC.weak (le_trans hαN (hkey _ hmono 0)) hβ hβNF hαNF hβH
        (Finset.insert_subset_insert _ (Finset.erase_subset_erase _ hsub)) (ih hmono)
  | @andI α' βφ' βψ' e' H' F' c' Γ' hαN χ₁ χ₂ hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH _ _ ih₁ ih₂ =>
      intro hmono
      have hne : χ₁ ⋏ χ₂ ≠ ∀⁰ φ := by simp
      rw [Finset.erase_insert_of_ne hne]
      rw [Finset.insert_comm]
      refine Zef2TC.andI (le_trans hαN (hkey _ hmono 0)) χ₁ χ₂ hβφ hβψ hβφNF hβψNF hαNF
        hβφH hβψH ?_ ?_
      · exact Zef2TC.wk (ih₁ hmono).gate (hreshape χ₁ Γ') (ih₁ hmono)
      · exact Zef2TC.wk (ih₂ hmono).gate (hreshape χ₂ Γ') (ih₂ hmono)
  | @orI α' β' e' H' F' c' Γ' hαN χ₁ χ₂ hβ hβNF hαNF hβH _ ih =>
      intro hmono
      have hne : χ₁ ⋎ χ₂ ≠ ∀⁰ φ := by simp
      rw [Finset.erase_insert_of_ne hne, Finset.insert_comm]
      refine Zef2TC.orI (le_trans hαN (hkey _ hmono 0)) χ₁ χ₂ hβ hβNF hαNF hβH ?_
      have h := ih hmono
      refine Zef2TC.wk h.gate ?_ h
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
      tauto
  | @allω α' e' H' F' c' Γ' hαN χ β hβ hβNF hαNF hβH dd ih =>
      intro hmono
      by_cases hchi : (∀⁰ χ : Form) = ∀⁰ φ
      · -- PRINCIPAL: take branch m, re-invert it, drop the duplicate instance
        have hφχ : χ = φ := by simpa using hchi
        subst hφχ
        have hbr := (ih m) (rel1_monotone hmono m)
        -- slot: rel1 (rel1 F m) m = rel1 F m
        rw [rel1_rel1, max_self] at hbr
        -- context: insert inst ((insert inst Γ').erase ∀χ) = insert inst (Γ'.erase ∀χ)
        have hctx : insert ((χ : SyntacticSemiformula ℒₒᵣ 1)/[nm m])
              ((insert (χ/[nm m]) Γ').erase (∀⁰ χ))
            = insert (χ/[nm m]) (Γ'.erase (∀⁰ χ)) := by
          rw [Finset.erase_insert_of_ne (by
            intro h
            have := congrArg Semiformula.complexity h
            simp at this)]
          exact Finset.insert_idem _ _
        rw [hctx] at hbr
        have hbr' := hbr.change_H (H' := H')
        refine Zef2TC.weak (le_trans hαN (hkey _ hmono 0)) (hβ m) (hβNF m) hαNF
          (Cl_of_NF (hβNF m)) ?_ hbr'
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
        tauto
      · -- NON-PRINCIPAL: rebuild the ω-rule over the inverted branches
        rw [Finset.erase_insert_of_ne hchi, Finset.insert_comm]
        refine Zef2TC.allω (le_trans hαN (hkey _ hmono 0)) χ β hβ hβNF hαNF
          (fun n => hβH n) ?_
        intro n
        have h := (ih n) (rel1_monotone hmono n)
        rw [rel1_rel1, max_comm n m, ← rel1_rel1] at h
        have h' := h.change_H (H' := adjoin H' n)
        refine Zef2TC.wk h'.gate ?_ h'
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
        tauto
  | @exI α' β' e' H' F' c' Γ' hαN χ n hβ hβNF hαNF hβH hbound _ ih =>
      intro hmono
      have hne : (∃⁰ χ : Form) ≠ ∀⁰ φ := by simp
      rw [Finset.erase_insert_of_ne hne, Finset.insert_comm]
      refine Zef2TC.exI (le_trans hαN (hkey _ hmono 0)) χ n hβ hβNF hαNF hβH
        (le_trans hbound (hkey _ hmono 0)) ?_
      have h := ih hmono
      refine Zef2TC.wk h.gate ?_ h
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
      tauto
  | @cut α' βφ' βψ' e' H' F' c' Γ' hαN χ hcompl hcutRead hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH _ _ ih₁ ih₂ =>
      intro hmono
      refine Zef2TC.cut (le_trans hαN (hkey _ hmono 0)) χ hcompl
        (le_trans hcutRead (hkey _ hmono 0)) hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH ?_ ?_
      · exact Zef2TC.wk (ih₁ hmono).gate (hreshape χ Γ') (ih₁ hmono)
      · exact Zef2TC.wk (ih₂ hmono).gate (hreshape (∼χ) Γ') (ih₂ hmono)

/-! ### The rung-E statement, REALIZED (V3 + inversion; judge input, NOT ratified) -/

/-- The embedded goodstein sentence is the ∀-closure of the embedded body. -/
theorem coe_goodsteinSentence_eq :
    (↑GoodsteinPA.goodsteinSentence : SyntacticFormula ℒₒᵣ) = ∀⁰ goodsteinBodyE := by
  rw [goodsteinSentence_eq_all_body]
  simp [goodsteinBodyE, Rewriting.emb]

/-- **Rung E, the V3 realization** (the DRAFT2 `∃ K` shape, STRENGTHENED: the node ordinal
`α` is also `m`-uniform).  From a PA proof of the goodstein sentence: uniform structural
budgets `B, d`, control `e`, node `α`, and per-instance derivations of the Σ₁ instance
singletons at slot `rel1 (ewRootSlot e B) K` — exactly the shape rungs R/D consume.
Proof = `toDerivation2` ∘ `budgetedEmbeddingV3` ∘ `allω_inversion`. -/
theorem embedding_Zef2TC_V3 :
    (𝗣𝗔 ⊢ ↑GoodsteinPA.goodsteinSentence) →
      ∃ B d : ℕ, ∃ e α : ONote, e.NF ∧ α.NF ∧ ∀ m : ℕ, ∃ K : ℕ,
        ∃ H : ONote → Prop, Cl H α ∧
          Zef2TC α e H (rel1 (ewRootSlot e B) K) d {(goodsteinBodyE/[nm m])} := by
  intro h
  -- upstream `𝗣𝗔 ⊢ σ` repackages as a `Derivation2 𝗣𝗔 {↑σ}` via `provable_iff_derivable2`
  have hV3 : BudgetedEmbedsV3 {(↑GoodsteinPA.goodsteinSentence : SyntacticFormula ℒₒᵣ)} := by
    obtain ⟨d2⟩ := (provable_iff_derivable2 (L := ℒₒᵣ)).mp h
    exact budgetedEmbeddingV3 d2
  obtain ⟨B, d, N, e, α, he, hαNF, hNlogB, hD⟩ := hV3
  refine ⟨B, d, e, α, he, hαNF, fun m => ?_⟩
  have hD0 := hD (fun _ => 0)
  have himg : ({(↑GoodsteinPA.goodsteinSentence : SyntacticFormula ℒₒᵣ)} :
        Finset (SyntacticFormula ℒₒᵣ)).image
        (fun φ => Embedding.asg (fun _ => 0) ▹ φ)
      = {(↑GoodsteinPA.goodsteinSentence : SyntacticFormula ℒₒᵣ)} := by
    rw [Finset.image_singleton, asg_emb_fix]
  rw [himg, coe_goodsteinSentence_eq] at hD0
  have hf1 := ewRootSlot_f1 e B
  have hmono : Monotone (rel1 (ewRootSlot e B) (envSup (fun _ => 0) N)) :=
    rel1_monotone hf1.1.monotone _
  have hinv := allω_inversion (φ := goodsteinBodyE) m hD0 hmono
  rw [rel1_rel1] at hinv
  refine ⟨max (envSup (fun _ => 0) N) m, fun _ => True, Cl_of_NF hαNF, ?_⟩
  have hctx : insert (goodsteinBodyE/[nm m])
        (({(∀⁰ goodsteinBodyE : SyntacticFormula ℒₒᵣ)} :
          Finset (SyntacticFormula ℒₒᵣ)).erase (∀⁰ goodsteinBodyE))
      = {(goodsteinBodyE/[nm m])} := by
    rw [Finset.erase_singleton]
    rfl
  rw [hctx] at hinv
  exact hinv.change_H

/-! ### The TC pass-port kit, part 1 — finite inversions + ⊥-erase

`passAux`'s inert-shape discharge (`Zef2.erase_inert`) breaks over `Zef2TC` (⋏/⋎/⊤ ARE
principal here).  The port needs: and/or-INVERSION (the finite mirrors of `allω_inversion` —
no slot change, no operator change), and ⊥-erase (⊥ is still never principal in TC). -/

/-- Left ⋏-inversion: replace `χ₁ ⋏ χ₂` by `χ₁` throughout.  Same ordinal, slot, rank. -/
theorem and_inversion_left {χ₁ χ₂ : Form} :
    ∀ {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Seq},
      Zef2TC α e H f c Γ →
      Zef2TC α e H f c (insert χ₁ (Γ.erase (χ₁ ⋏ χ₂))) := by
  have hreshape : ∀ (χ : Form) (Γ : Seq),
      insert χ₁ ((insert χ Γ).erase (χ₁ ⋏ χ₂))
        ⊆ insert χ (insert χ₁ (Γ.erase (χ₁ ⋏ χ₂))) := by
    intro χ Γ x hx
    simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
    tauto
  intro α e H f c Γ dd
  induction dd with
  | axL hαN r v hp hn =>
      exact Zef2TC.axL hαN r v
        (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨by simp, hp⟩))
        (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨by simp, hn⟩))
  | trueRel hαN r v htrue hmem =>
      exact Zef2TC.trueRel hαN r v htrue
        (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨by simp, hmem⟩))
  | trueNrel hαN r v htrue hmem =>
      exact Zef2TC.trueNrel hαN r v htrue
        (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨by simp, hmem⟩))
  | verumR hαN h =>
      exact Zef2TC.verumR hαN
        (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨by simp, h⟩))
  | wk hαN hsub _ ih =>
      exact Zef2TC.wk hαN
        (Finset.insert_subset_insert _ (Finset.erase_subset_erase _ hsub)) ih
  | weak hαN hβ hβNF hαNF hβH hsub _ ih =>
      exact Zef2TC.weak hαN hβ hβNF hαNF hβH
        (Finset.insert_subset_insert _ (Finset.erase_subset_erase _ hsub)) ih
  | @andI α' βφ' βψ' e' H' F' c' Γ' hαN φ ψ hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH d₁ _ ih₁ ih₂ =>
      by_cases hchi : (φ ⋏ ψ : Form) = χ₁ ⋏ χ₂
      · -- PRINCIPAL: use the LEFT premise, re-invert, drop the duplicate
        have hφ₁ : φ = χ₁ ∧ ψ = χ₂ := by simpa using hchi
        obtain ⟨rfl, rfl⟩ := hφ₁
        have hctx : insert (φ : Form) ((insert φ Γ').erase (φ ⋏ ψ))
            = insert φ (Γ'.erase (φ ⋏ ψ)) := by
          rw [Finset.erase_insert_of_ne (by
            intro h
            have := congrArg Semiformula.complexity h
            simp at this)]
          exact Finset.insert_idem _ _
        rw [hctx] at ih₁
        refine Zef2TC.weak hαN hβφ hβφNF hαNF hβφH ?_ ih₁
        rw [hchi]
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
        tauto
      · rw [Finset.erase_insert_of_ne hchi, Finset.insert_comm]
        refine Zef2TC.andI hαN φ ψ hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH ?_ ?_
        · exact Zef2TC.wk ih₁.gate (hreshape φ Γ') ih₁
        · exact Zef2TC.wk ih₂.gate (hreshape ψ Γ') ih₂
  | @orI α' β' e' H' F' c' Γ' hαN φ ψ hβ hβNF hαNF hβH _ ih =>
      have hne : (φ ⋎ ψ : Form) ≠ χ₁ ⋏ χ₂ := by simp
      rw [Finset.erase_insert_of_ne hne, Finset.insert_comm]
      refine Zef2TC.orI hαN φ ψ hβ hβNF hαNF hβH ?_
      refine Zef2TC.wk ih.gate ?_ ih
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
      tauto
  | @allω α' e' H' F' c' Γ' hαN φ β hβ hβNF hαNF hβH _ ih =>
      have hne : (∀⁰ φ : Form) ≠ χ₁ ⋏ χ₂ := by simp
      rw [Finset.erase_insert_of_ne hne, Finset.insert_comm]
      refine Zef2TC.allω hαN φ β hβ hβNF hαNF hβH ?_
      intro n
      refine Zef2TC.wk (ih n).gate ?_ (ih n)
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
      tauto
  | @exI α' β' e' H' F' c' Γ' hαN φ n hβ hβNF hαNF hβH hbound _ ih =>
      have hne : (∃⁰ φ : Form) ≠ χ₁ ⋏ χ₂ := by simp
      rw [Finset.erase_insert_of_ne hne, Finset.insert_comm]
      refine Zef2TC.exI hαN φ n hβ hβNF hαNF hβH hbound ?_
      refine Zef2TC.wk ih.gate ?_ ih
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
      tauto
  | @cut α' βφ' βψ' e' H' F' c' Γ' hαN φ hcompl hcutRead hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH _ _ ih₁ ih₂ =>
      refine Zef2TC.cut hαN φ hcompl hcutRead hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH ?_ ?_
      · exact Zef2TC.wk ih₁.gate (hreshape φ Γ') ih₁
      · exact Zef2TC.wk ih₂.gate (hreshape (∼φ) Γ') ih₂

/-- Right ⋏-inversion. -/
theorem and_inversion_right {χ₁ χ₂ : Form} :
    ∀ {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Seq},
      Zef2TC α e H f c Γ →
      Zef2TC α e H f c (insert χ₂ (Γ.erase (χ₁ ⋏ χ₂))) := by
  have hreshape : ∀ (χ : Form) (Γ : Seq),
      insert χ₂ ((insert χ Γ).erase (χ₁ ⋏ χ₂))
        ⊆ insert χ (insert χ₂ (Γ.erase (χ₁ ⋏ χ₂))) := by
    intro χ Γ x hx
    simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
    tauto
  intro α e H f c Γ dd
  induction dd with
  | axL hαN r v hp hn =>
      exact Zef2TC.axL hαN r v
        (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨by simp, hp⟩))
        (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨by simp, hn⟩))
  | trueRel hαN r v htrue hmem =>
      exact Zef2TC.trueRel hαN r v htrue
        (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨by simp, hmem⟩))
  | trueNrel hαN r v htrue hmem =>
      exact Zef2TC.trueNrel hαN r v htrue
        (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨by simp, hmem⟩))
  | verumR hαN h =>
      exact Zef2TC.verumR hαN
        (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨by simp, h⟩))
  | wk hαN hsub _ ih =>
      exact Zef2TC.wk hαN
        (Finset.insert_subset_insert _ (Finset.erase_subset_erase _ hsub)) ih
  | weak hαN hβ hβNF hαNF hβH hsub _ ih =>
      exact Zef2TC.weak hαN hβ hβNF hαNF hβH
        (Finset.insert_subset_insert _ (Finset.erase_subset_erase _ hsub)) ih
  | @andI α' βφ' βψ' e' H' F' c' Γ' hαN φ ψ hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH _ d₂ ih₁ ih₂ =>
      by_cases hchi : (φ ⋏ ψ : Form) = χ₁ ⋏ χ₂
      · have hφ₁ : φ = χ₁ ∧ ψ = χ₂ := by simpa using hchi
        obtain ⟨rfl, rfl⟩ := hφ₁
        have hctx : insert (ψ : Form) ((insert ψ Γ').erase (φ ⋏ ψ))
            = insert ψ (Γ'.erase (φ ⋏ ψ)) := by
          rw [Finset.erase_insert_of_ne (by
            intro h
            have := congrArg Semiformula.complexity h
            simp at this)]
          exact Finset.insert_idem _ _
        rw [hctx] at ih₂
        refine Zef2TC.weak hαN hβψ hβψNF hαNF hβψH ?_ ih₂
        rw [hchi]
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
        tauto
      · rw [Finset.erase_insert_of_ne hchi, Finset.insert_comm]
        refine Zef2TC.andI hαN φ ψ hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH ?_ ?_
        · exact Zef2TC.wk ih₁.gate (hreshape φ Γ') ih₁
        · exact Zef2TC.wk ih₂.gate (hreshape ψ Γ') ih₂
  | @orI α' β' e' H' F' c' Γ' hαN φ ψ hβ hβNF hαNF hβH _ ih =>
      have hne : (φ ⋎ ψ : Form) ≠ χ₁ ⋏ χ₂ := by simp
      rw [Finset.erase_insert_of_ne hne, Finset.insert_comm]
      refine Zef2TC.orI hαN φ ψ hβ hβNF hαNF hβH ?_
      refine Zef2TC.wk ih.gate ?_ ih
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
      tauto
  | @allω α' e' H' F' c' Γ' hαN φ β hβ hβNF hαNF hβH _ ih =>
      have hne : (∀⁰ φ : Form) ≠ χ₁ ⋏ χ₂ := by simp
      rw [Finset.erase_insert_of_ne hne, Finset.insert_comm]
      refine Zef2TC.allω hαN φ β hβ hβNF hαNF hβH ?_
      intro n
      refine Zef2TC.wk (ih n).gate ?_ (ih n)
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
      tauto
  | @exI α' β' e' H' F' c' Γ' hαN φ n hβ hβNF hαNF hβH hbound _ ih =>
      have hne : (∃⁰ φ : Form) ≠ χ₁ ⋏ χ₂ := by simp
      rw [Finset.erase_insert_of_ne hne, Finset.insert_comm]
      refine Zef2TC.exI hαN φ n hβ hβNF hαNF hβH hbound ?_
      refine Zef2TC.wk ih.gate ?_ ih
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
      tauto
  | @cut α' βφ' βψ' e' H' F' c' Γ' hαN φ hcompl hcutRead hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH _ _ ih₁ ih₂ =>
      refine Zef2TC.cut hαN φ hcompl hcutRead hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH ?_ ?_
      · exact Zef2TC.wk ih₁.gate (hreshape φ Γ') ih₁
      · exact Zef2TC.wk ih₂.gate (hreshape (∼φ) Γ') ih₂

/-- ⋎-inversion: replace `χ₁ ⋎ χ₂` by BOTH disjuncts. -/
theorem or_inversion {χ₁ χ₂ : Form} :
    ∀ {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Seq},
      Zef2TC α e H f c Γ →
      Zef2TC α e H f c (insert χ₁ (insert χ₂ (Γ.erase (χ₁ ⋎ χ₂)))) := by
  have hreshape : ∀ (χ : Form) (Γ : Seq),
      insert χ₁ (insert χ₂ ((insert χ Γ).erase (χ₁ ⋎ χ₂)))
        ⊆ insert χ (insert χ₁ (insert χ₂ (Γ.erase (χ₁ ⋎ χ₂)))) := by
    intro χ Γ x hx
    simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
    tauto
  intro α e H f c Γ dd
  induction dd with
  | axL hαN r v hp hn =>
      exact Zef2TC.axL hαN r v
        (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
          (Finset.mem_erase.mpr ⟨by simp, hp⟩)))
        (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
          (Finset.mem_erase.mpr ⟨by simp, hn⟩)))
  | trueRel hαN r v htrue hmem =>
      exact Zef2TC.trueRel hαN r v htrue
        (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
          (Finset.mem_erase.mpr ⟨by simp, hmem⟩)))
  | trueNrel hαN r v htrue hmem =>
      exact Zef2TC.trueNrel hαN r v htrue
        (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
          (Finset.mem_erase.mpr ⟨by simp, hmem⟩)))
  | verumR hαN h =>
      exact Zef2TC.verumR hαN
        (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
          (Finset.mem_erase.mpr ⟨by simp, h⟩)))
  | wk hαN hsub _ ih =>
      exact Zef2TC.wk hαN
        (Finset.insert_subset_insert _ (Finset.insert_subset_insert _
          (Finset.erase_subset_erase _ hsub))) ih
  | weak hαN hβ hβNF hαNF hβH hsub _ ih =>
      exact Zef2TC.weak hαN hβ hβNF hαNF hβH
        (Finset.insert_subset_insert _ (Finset.insert_subset_insert _
          (Finset.erase_subset_erase _ hsub))) ih
  | @andI α' βφ' βψ' e' H' F' c' Γ' hαN φ ψ hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH _ _ ih₁ ih₂ =>
      have hne : (φ ⋏ ψ : Form) ≠ χ₁ ⋎ χ₂ := by simp
      rw [Finset.erase_insert_of_ne hne]
      rw [show insert (χ₁ : Form) (insert χ₂ (insert (φ ⋏ ψ) (Γ'.erase (χ₁ ⋎ χ₂))))
          = insert (φ ⋏ ψ) (insert χ₁ (insert χ₂ (Γ'.erase (χ₁ ⋎ χ₂)))) from by
        rw [Finset.insert_comm χ₂, Finset.insert_comm χ₁]]
      refine Zef2TC.andI hαN φ ψ hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH ?_ ?_
      · exact Zef2TC.wk ih₁.gate (hreshape φ Γ') ih₁
      · exact Zef2TC.wk ih₂.gate (hreshape ψ Γ') ih₂
  | @orI α' β' e' H' F' c' Γ' hαN φ ψ hβ hβNF hαNF hβH d₁ ih =>
      by_cases hchi : (φ ⋎ ψ : Form) = χ₁ ⋎ χ₂
      · -- PRINCIPAL: the premise carries BOTH disjuncts; re-invert and clean up
        have hφ₁ : φ = χ₁ ∧ ψ = χ₂ := by simpa using hchi
        obtain ⟨rfl, rfl⟩ := hφ₁
        have hctx : insert (φ : Form) (insert ψ
              ((insert φ (insert ψ Γ')).erase (φ ⋎ ψ)))
            = insert φ (insert ψ (Γ'.erase (φ ⋎ ψ))) := by
          rw [Finset.erase_insert_of_ne (by
              intro h
              have := congrArg Semiformula.complexity h
              simp at this),
            Finset.erase_insert_of_ne (by
              intro h
              have := congrArg Semiformula.complexity h
              simp at this)]
          ext x
          simp only [Finset.mem_insert]
          tauto
        rw [hctx] at ih
        refine Zef2TC.weak hαN hβ hβNF hαNF hβH ?_ ih
        rw [hchi]
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
        tauto
      · rw [Finset.erase_insert_of_ne hchi]
        rw [show insert (χ₁ : Form) (insert χ₂ (insert (φ ⋎ ψ) (Γ'.erase (χ₁ ⋎ χ₂))))
            = insert (φ ⋎ ψ) (insert χ₁ (insert χ₂ (Γ'.erase (χ₁ ⋎ χ₂)))) from by
          rw [Finset.insert_comm χ₂, Finset.insert_comm χ₁]]
        refine Zef2TC.orI hαN φ ψ hβ hβNF hαNF hβH ?_
        refine Zef2TC.wk ih.gate ?_ ih
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
        tauto
  | @allω α' e' H' F' c' Γ' hαN φ β hβ hβNF hαNF hβH _ ih =>
      have hne : (∀⁰ φ : Form) ≠ χ₁ ⋎ χ₂ := by simp
      rw [Finset.erase_insert_of_ne hne]
      rw [show insert (χ₁ : Form) (insert χ₂ (insert (∀⁰ φ) (Γ'.erase (χ₁ ⋎ χ₂))))
          = insert (∀⁰ φ) (insert χ₁ (insert χ₂ (Γ'.erase (χ₁ ⋎ χ₂)))) from by
        rw [Finset.insert_comm χ₂, Finset.insert_comm χ₁]]
      refine Zef2TC.allω hαN φ β hβ hβNF hαNF hβH ?_
      intro n
      refine Zef2TC.wk (ih n).gate ?_ (ih n)
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
      tauto
  | @exI α' β' e' H' F' c' Γ' hαN φ n hβ hβNF hαNF hβH hbound _ ih =>
      have hne : (∃⁰ φ : Form) ≠ χ₁ ⋎ χ₂ := by simp
      rw [Finset.erase_insert_of_ne hne]
      rw [show insert (χ₁ : Form) (insert χ₂ (insert (∃⁰ φ) (Γ'.erase (χ₁ ⋎ χ₂))))
          = insert (∃⁰ φ) (insert χ₁ (insert χ₂ (Γ'.erase (χ₁ ⋎ χ₂)))) from by
        rw [Finset.insert_comm χ₂, Finset.insert_comm χ₁]]
      refine Zef2TC.exI hαN φ n hβ hβNF hαNF hβH hbound ?_
      refine Zef2TC.wk ih.gate ?_ ih
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
      tauto
  | @cut α' βφ' βψ' e' H' F' c' Γ' hαN φ hcompl hcutRead hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH _ _ ih₁ ih₂ =>
      refine Zef2TC.cut hαN φ hcompl hcutRead hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH ?_ ?_
      · exact Zef2TC.wk ih₁.gate (hreshape φ Γ') ih₁
      · exact Zef2TC.wk ih₂.gate (hreshape (∼φ) Γ') ih₂

/-- ⊥-erase: `⊥` is never principal in `Zef2TC` (no rule introduces `falsum`), so it can be
erased from any context. -/
theorem falsum_erase :
    ∀ {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Seq},
      Zef2TC α e H f c Γ →
      Zef2TC α e H f c (Γ.erase (⊥ : Form)) := by
  have hreshape : ∀ (χ : Form) (Γ : Seq),
      (insert χ Γ).erase (⊥ : Form) ⊆ insert χ (Γ.erase (⊥ : Form)) := by
    intro χ Γ x hx
    simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
    tauto
  intro α e H f c Γ dd
  induction dd with
  | axL hαN r v hp hn =>
      exact Zef2TC.axL hαN r v
        (Finset.mem_erase.mpr ⟨by simp, hp⟩) (Finset.mem_erase.mpr ⟨by simp, hn⟩)
  | trueRel hαN r v htrue hmem =>
      exact Zef2TC.trueRel hαN r v htrue (Finset.mem_erase.mpr ⟨by simp, hmem⟩)
  | trueNrel hαN r v htrue hmem =>
      exact Zef2TC.trueNrel hαN r v htrue (Finset.mem_erase.mpr ⟨by simp, hmem⟩)
  | verumR hαN h =>
      exact Zef2TC.verumR hαN (Finset.mem_erase.mpr ⟨by simp, h⟩)
  | wk hαN hsub _ ih =>
      exact Zef2TC.wk hαN (Finset.erase_subset_erase _ hsub) ih
  | weak hαN hβ hβNF hαNF hβH hsub _ ih =>
      exact Zef2TC.weak hαN hβ hβNF hαNF hβH (Finset.erase_subset_erase _ hsub) ih
  | @andI α' βφ' βψ' e' H' F' c' Γ' hαN φ ψ hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH _ _ ih₁ ih₂ =>
      rw [Finset.erase_insert_of_ne (by simp : (φ ⋏ ψ : Form) ≠ ⊥)]
      refine Zef2TC.andI hαN φ ψ hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH ?_ ?_
      · exact Zef2TC.wk ih₁.gate (hreshape φ Γ') ih₁
      · exact Zef2TC.wk ih₂.gate (hreshape ψ Γ') ih₂
  | @orI α' β' e' H' F' c' Γ' hαN φ ψ hβ hβNF hαNF hβH _ ih =>
      rw [Finset.erase_insert_of_ne (by simp : (φ ⋎ ψ : Form) ≠ ⊥)]
      refine Zef2TC.orI hαN φ ψ hβ hβNF hαNF hβH ?_
      refine Zef2TC.wk ih.gate ?_ ih
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
      tauto
  | @allω α' e' H' F' c' Γ' hαN φ β hβ hβNF hαNF hβH _ ih =>
      rw [Finset.erase_insert_of_ne (by simp : (∀⁰ φ : Form) ≠ ⊥)]
      refine Zef2TC.allω hαN φ β hβ hβNF hαNF hβH ?_
      intro n
      exact Zef2TC.wk (ih n).gate (hreshape _ Γ') (ih n)
  | @exI α' β' e' H' F' c' Γ' hαN φ n hβ hβNF hαNF hβH hbound _ ih =>
      rw [Finset.erase_insert_of_ne (by simp : (∃⁰ φ : Form) ≠ ⊥)]
      refine Zef2TC.exI hαN φ n hβ hβNF hαNF hβH hbound ?_
      exact Zef2TC.wk ih.gate (hreshape _ Γ') ih
  | @cut α' βφ' βψ' e' H' F' c' Γ' hαN φ hcompl hcutRead hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH _ _ ih₁ ih₂ =>
      refine Zef2TC.cut hαN φ hcompl hcutRead hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH ?_ ?_
      · exact Zef2TC.wk ih₁.gate (hreshape φ Γ') ih₁
      · exact Zef2TC.wk ih₂.gate (hreshape (∼φ) Γ') ih₂

/-! ### The TC pass-port kit, part 2 — the ⋏/⋎ principal cut-reduction + ⊤/⊥ principal cuts

Block 12b: the finite mirror of `stepAllω_Zf2_bnd`.  A top-rank cut on `φ ⋏ ψ` reduces to two
nested LOWER-complexity cuts (on `ψ`, then `φ`) via the block-12a inversions.  No slot change,
no operator change; ordinal cost = two successors above the ordinal SUM of the premises
(`osucc (osucc (βφ + βψ))`) — strictly under `collapse α` at the pass's call site via
`collapse_add_lt` + limit headroom.  The gate is paid by the single slack hypothesis
`Nlog (βφ + βψ) + 2 ≤ f 0` (both successor gates ride `Nlog_osucc_le`).

The ⋎-principal cut is the SAME lemma with the premises swapped (`∼(φ ⋎ ψ) = ∼φ ⋏ ∼ψ`, and
`φ ⋎ ψ = ∼(∼φ) ⋎ ∼(∼ψ)` after double-negation cleanup — exactly how `passAux`'s `exs` case
reuses `all`).  The ⊤/⊥ principal cuts are FREE: `∼⊤ = ⊥` and ⊥ is never principal
(`falsum_erase`), so the ⊥-side premise already derives `Γ`. -/

/-- **`stepAnd_Zef2TC`** — the ⋏-principal top-rank cut reduction (E–W/Buchholz finite
reduction).  From `⊢ φ⋏ψ, Γ` and `⊢ ∼φ⋎∼ψ, Γ` (same slot `f`, rank `c`), derive `Γ` at rank
`c` using two cuts on `ψ` and `φ` (both `complexity < c`), at root `osucc (osucc (βφ + βψ))`. -/
theorem stepAnd_Zef2TC {φ ψ : Form} {βφ βψ e : ONote} {H : ONote → Prop} {f : ℕ → ℕ}
    {c : ℕ} {Γ : Seq}
    (hβφNF : βφ.NF) (hβψNF : βψ.NF)
    (hφc : φ.complexity < c) (hψc : ψ.complexity < c)
    (hφRead : φ.complexity ≤ f 0) (hψRead : ψ.complexity ≤ f 0)
    (hgate : Nlog (βφ + βψ) + 2 ≤ f 0)
    (D₁ : Zef2TC βφ e H f c (insert (φ ⋏ ψ) Γ))
    (D₂ : Zef2TC βψ e H f c (insert (∼φ ⋎ ∼ψ) Γ)) :
    Zef2TC (osucc (osucc (βφ + βψ))) e H f c Γ := by
  have hσNF : (βφ + βψ).NF := ONote.add_nf βφ βψ
  have hα₁NF : (osucc (βφ + βψ)).NF := osucc_NF hσNF
  have hα₂NF : (osucc (osucc (βφ + βψ))).NF := osucc_NF hα₁NF
  have hβφ1 : βφ < osucc (βφ + βψ) :=
    lt_of_le_of_lt (Zekd.le_add_right_NF hβφNF hβψNF) (Zekd.lt_osucc hσNF)
  have hβψ1 : βψ < osucc (βφ + βψ) :=
    lt_of_le_of_lt (Zekd.le_add_left_NF hβφNF hβψNF) (Zekd.lt_osucc hσNF)
  have h12 : osucc (βφ + βψ) < osucc (osucc (βφ + βψ)) := Zekd.lt_osucc hα₁NF
  have hβφ2 : βφ < osucc (osucc (βφ + βψ)) := lt_trans hβφ1 h12
  have hα₁N : Nlog (osucc (βφ + βψ)) ≤ f 0 :=
    le_trans (Nlog_osucc_le hσNF) (by omega)
  have hα₂N : Nlog (osucc (osucc (βφ + βψ))) ≤ f 0 := by
    have h1 := Nlog_osucc_le hα₁NF
    have h2 := Nlog_osucc_le hσNF
    omega
  -- left ⋏-inversion → `⊢ φ, Γ` at `βφ`
  have PL : Zef2TC βφ e H f c (insert φ Γ) := by
    have A := and_inversion_left (χ₁ := φ) (χ₂ := ψ) D₁
    rw [Finset.erase_insert_eq_erase] at A
    exact Zef2TC.wk A.gate
      (Finset.insert_subset_insert _ (Finset.erase_subset _ _)) A
  -- right ⋏-inversion → `⊢ ψ, ∼φ, Γ` at `βφ`
  have PR : Zef2TC βφ e H f c (insert ψ (insert (∼φ) Γ)) := by
    have B := and_inversion_right (χ₁ := φ) (χ₂ := ψ) D₁
    rw [Finset.erase_insert_eq_erase] at B
    refine Zef2TC.wk B.gate ?_ B
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
    tauto
  -- ⋎-inversion → `⊢ ∼ψ, ∼φ, Γ` at `βψ`
  have PN : Zef2TC βψ e H f c (insert (∼ψ) (insert (∼φ) Γ)) := by
    have C := or_inversion (χ₁ := ∼φ) (χ₂ := ∼ψ) D₂
    rw [Finset.erase_insert_eq_erase] at C
    refine Zef2TC.wk C.gate ?_ C
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
    tauto
  -- inner cut on `ψ` → `⊢ ∼φ, Γ` at `osucc (βφ + βψ)`
  have cutψ : Zef2TC (osucc (βφ + βψ)) e H f c (insert (∼φ) Γ) :=
    Zef2TC.cut hα₁N ψ hψc hψRead hβφ1 hβψ1 hβφNF hβψNF hα₁NF
      (Cl_of_NF hβφNF) (Cl_of_NF hβψNF) PR PN
  -- outer cut on `φ` → `⊢ Γ`
  exact Zef2TC.cut hα₂N φ hφc hφRead hβφ2 h12 hβφNF hα₁NF hα₂NF
    (Cl_of_NF hβφNF) (Cl_of_NF hα₁NF) PL cutψ

/-! ### Block 12c — atomic truth-leaf surgery: the TC atomic cut needs NO splice

Over `Zef2TC`, exactly one of `rel rr vv` / `nrel rr vv` is `atomTrue`
(`atomTrue_nrel_iff_not_rel`), so the atomic top-rank cut dissolves WITHOUT `atomCutRun_Zf2`'s
axL-pair splice: erase the FALSE literal from its own premise.  The only rules where the false
literal could be "principal" are `axL` (the pair leaf — after erasing the false half, the TRUE
half remains in context and the leaf collapses to `trueRel`/`trueNrel`) and the matching
truth leaf itself (kernel-contradicted by exclusivity).  Same ordinal, same slot, no fresh
root, no composition. -/

/-- Erase a FALSE `nrel` literal (its `rel` is `atomTrue`): never honestly principal. -/
theorem false_nrel_erase {ar : ℕ} {rr : (ℒₒᵣ).Rel ar} {vv : Fin ar → Semiterm ℒₒᵣ ℕ 0}
    (htrue : atomTrue (Semiformula.rel rr vv)) :
    ∀ {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Seq},
      Zef2TC α e H f c Γ →
      Zef2TC α e H f c (Γ.erase (Semiformula.nrel rr vv)) := by
  have hreshape : ∀ (χ : Form) (Γ : Seq),
      (insert χ Γ).erase (Semiformula.nrel rr vv)
        ⊆ insert χ (Γ.erase (Semiformula.nrel rr vv)) := by
    intro χ Γ x hx
    simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
    tauto
  intro α e H f c Γ dd
  induction dd with
  | @axL α' e' H' F' c' Γ' ar' hαN r v hp hn =>
      by_cases h : (Semiformula.nrel r v : Form) = Semiformula.nrel rr vv
      · -- the pair leaf collapses to a `trueRel` leaf on the surviving TRUE half
        have hrel : (Semiformula.rel r v : Form) = Semiformula.rel rr vv := by
          have := congrArg (∼·) h
          simpa using this
        have htrue' : atomTrue (Semiformula.rel r v) := by rw [hrel]; exact htrue
        exact Zef2TC.trueRel hαN r v htrue' (Finset.mem_erase.mpr ⟨by simp, hp⟩)
      · exact Zef2TC.axL hαN r v
          (Finset.mem_erase.mpr ⟨by simp, hp⟩) (Finset.mem_erase.mpr ⟨h, hn⟩)
  | trueRel hαN r v htrue' hmem =>
      exact Zef2TC.trueRel hαN r v htrue' (Finset.mem_erase.mpr ⟨by simp, hmem⟩)
  | @trueNrel α' e' H' F' c' Γ' ar' hαN r v htrue' hmem =>
      by_cases h : (Semiformula.nrel r v : Form) = Semiformula.nrel rr vv
      · -- exclusivity: a TRUE `nrel` leaf on the FALSE literal is impossible
        rw [h] at htrue'
        exact absurd htrue ((atomTrue_nrel_iff_not_rel rr vv).mp htrue')
      · exact Zef2TC.trueNrel hαN r v htrue' (Finset.mem_erase.mpr ⟨h, hmem⟩)
  | verumR hαN h =>
      exact Zef2TC.verumR hαN (Finset.mem_erase.mpr ⟨by simp, h⟩)
  | wk hαN hsub _ ih =>
      exact Zef2TC.wk hαN (Finset.erase_subset_erase _ hsub) ih
  | weak hαN hβ hβNF hαNF hβH hsub _ ih =>
      exact Zef2TC.weak hαN hβ hβNF hαNF hβH (Finset.erase_subset_erase _ hsub) ih
  | @andI α' βφ' βψ' e' H' F' c' Γ' hαN φ ψ hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH _ _ ih₁ ih₂ =>
      rw [Finset.erase_insert_of_ne (by simp : (φ ⋏ ψ : Form) ≠ Semiformula.nrel rr vv)]
      refine Zef2TC.andI hαN φ ψ hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH ?_ ?_
      · exact Zef2TC.wk ih₁.gate (hreshape φ Γ') ih₁
      · exact Zef2TC.wk ih₂.gate (hreshape ψ Γ') ih₂
  | @orI α' β' e' H' F' c' Γ' hαN φ ψ hβ hβNF hαNF hβH _ ih =>
      rw [Finset.erase_insert_of_ne (by simp : (φ ⋎ ψ : Form) ≠ Semiformula.nrel rr vv)]
      refine Zef2TC.orI hαN φ ψ hβ hβNF hαNF hβH ?_
      refine Zef2TC.wk ih.gate ?_ ih
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
      tauto
  | @allω α' e' H' F' c' Γ' hαN φ β hβ hβNF hαNF hβH _ ih =>
      rw [Finset.erase_insert_of_ne (by simp : (∀⁰ φ : Form) ≠ Semiformula.nrel rr vv)]
      refine Zef2TC.allω hαN φ β hβ hβNF hαNF hβH ?_
      intro n
      exact Zef2TC.wk (ih n).gate (hreshape _ Γ') (ih n)
  | @exI α' β' e' H' F' c' Γ' hαN φ n hβ hβNF hαNF hβH hbound _ ih =>
      rw [Finset.erase_insert_of_ne (by simp : (∃⁰ φ : Form) ≠ Semiformula.nrel rr vv)]
      refine Zef2TC.exI hαN φ n hβ hβNF hαNF hβH hbound ?_
      exact Zef2TC.wk ih.gate (hreshape _ Γ') ih
  | @cut α' βφ' βψ' e' H' F' c' Γ' hαN φ hcompl hcutRead hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH _ _ ih₁ ih₂ =>
      refine Zef2TC.cut hαN φ hcompl hcutRead hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH ?_ ?_
      · exact Zef2TC.wk ih₁.gate (hreshape φ Γ') ih₁
      · exact Zef2TC.wk ih₂.gate (hreshape (∼φ) Γ') ih₂

/-- Erase a FALSE `rel` literal (its `nrel` is `atomTrue`): dual of `false_nrel_erase`. -/
theorem false_rel_erase {ar : ℕ} {rr : (ℒₒᵣ).Rel ar} {vv : Fin ar → Semiterm ℒₒᵣ ℕ 0}
    (htrue : atomTrue (Semiformula.nrel rr vv)) :
    ∀ {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Seq},
      Zef2TC α e H f c Γ →
      Zef2TC α e H f c (Γ.erase (Semiformula.rel rr vv)) := by
  have hreshape : ∀ (χ : Form) (Γ : Seq),
      (insert χ Γ).erase (Semiformula.rel rr vv)
        ⊆ insert χ (Γ.erase (Semiformula.rel rr vv)) := by
    intro χ Γ x hx
    simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
    tauto
  intro α e H f c Γ dd
  induction dd with
  | @axL α' e' H' F' c' Γ' ar' hαN r v hp hn =>
      by_cases h : (Semiformula.rel r v : Form) = Semiformula.rel rr vv
      · -- the pair leaf collapses to a `trueNrel` leaf on the surviving TRUE half
        have hnrel : (Semiformula.nrel r v : Form) = Semiformula.nrel rr vv := by
          have := congrArg (∼·) h
          simpa using this
        have htrue' : atomTrue (Semiformula.nrel r v) := by rw [hnrel]; exact htrue
        exact Zef2TC.trueNrel hαN r v htrue' (Finset.mem_erase.mpr ⟨by simp, hn⟩)
      · exact Zef2TC.axL hαN r v
          (Finset.mem_erase.mpr ⟨h, hp⟩) (Finset.mem_erase.mpr ⟨by simp, hn⟩)
  | @trueRel α' e' H' F' c' Γ' ar' hαN r v htrue' hmem =>
      by_cases h : (Semiformula.rel r v : Form) = Semiformula.rel rr vv
      · rw [h] at htrue'
        exact absurd htrue ((atomTrue_rel_iff_not_nrel rr vv).mp htrue')
      · exact Zef2TC.trueRel hαN r v htrue' (Finset.mem_erase.mpr ⟨h, hmem⟩)
  | trueNrel hαN r v htrue' hmem =>
      exact Zef2TC.trueNrel hαN r v htrue' (Finset.mem_erase.mpr ⟨by simp, hmem⟩)
  | verumR hαN h =>
      exact Zef2TC.verumR hαN (Finset.mem_erase.mpr ⟨by simp, h⟩)
  | wk hαN hsub _ ih =>
      exact Zef2TC.wk hαN (Finset.erase_subset_erase _ hsub) ih
  | weak hαN hβ hβNF hαNF hβH hsub _ ih =>
      exact Zef2TC.weak hαN hβ hβNF hαNF hβH (Finset.erase_subset_erase _ hsub) ih
  | @andI α' βφ' βψ' e' H' F' c' Γ' hαN φ ψ hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH _ _ ih₁ ih₂ =>
      rw [Finset.erase_insert_of_ne (by simp : (φ ⋏ ψ : Form) ≠ Semiformula.rel rr vv)]
      refine Zef2TC.andI hαN φ ψ hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH ?_ ?_
      · exact Zef2TC.wk ih₁.gate (hreshape φ Γ') ih₁
      · exact Zef2TC.wk ih₂.gate (hreshape ψ Γ') ih₂
  | @orI α' β' e' H' F' c' Γ' hαN φ ψ hβ hβNF hαNF hβH _ ih =>
      rw [Finset.erase_insert_of_ne (by simp : (φ ⋎ ψ : Form) ≠ Semiformula.rel rr vv)]
      refine Zef2TC.orI hαN φ ψ hβ hβNF hαNF hβH ?_
      refine Zef2TC.wk ih.gate ?_ ih
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
      tauto
  | @allω α' e' H' F' c' Γ' hαN φ β hβ hβNF hαNF hβH _ ih =>
      rw [Finset.erase_insert_of_ne (by simp : (∀⁰ φ : Form) ≠ Semiformula.rel rr vv)]
      refine Zef2TC.allω hαN φ β hβ hβNF hαNF hβH ?_
      intro n
      exact Zef2TC.wk (ih n).gate (hreshape _ Γ') (ih n)
  | @exI α' β' e' H' F' c' Γ' hαN φ n hβ hβNF hαNF hβH hbound _ ih =>
      rw [Finset.erase_insert_of_ne (by simp : (∃⁰ φ : Form) ≠ Semiformula.rel rr vv)]
      refine Zef2TC.exI hαN φ n hβ hβNF hαNF hβH hbound ?_
      exact Zef2TC.wk ih.gate (hreshape _ Γ') ih
  | @cut α' βφ' βψ' e' H' F' c' Γ' hαN φ hcompl hcutRead hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH _ _ ih₁ ih₂ =>
      refine Zef2TC.cut hαN φ hcompl hcutRead hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH ?_ ?_
      · exact Zef2TC.wk ih₁.gate (hreshape φ Γ') ih₁
      · exact Zef2TC.wk ih₂.gate (hreshape (∼φ) Γ') ih₂

/-- **`stepAtom_Zef2TC`** — the atomic top-rank cut over `Zef2TC`: splice-FREE.  Erase the
false literal from its premise; lift to the common root `osucc (βφ + βψ)` via `weak`. -/
theorem stepAtom_Zef2TC {ar : ℕ} {rr : (ℒₒᵣ).Rel ar} {vv : Fin ar → Semiterm ℒₒᵣ ℕ 0}
    {βφ βψ e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Seq}
    (hβφNF : βφ.NF) (hβψNF : βψ.NF)
    (hgate : Nlog (βφ + βψ) + 1 ≤ f 0)
    (D₁ : Zef2TC βφ e H f c (insert (Semiformula.rel rr vv) Γ))
    (D₂ : Zef2TC βψ e H f c (insert (Semiformula.nrel rr vv) Γ)) :
    Zef2TC (osucc (βφ + βψ)) e H f c Γ := by
  have hσNF : (βφ + βψ).NF := ONote.add_nf βφ βψ
  have hα₁NF : (osucc (βφ + βψ)).NF := osucc_NF hσNF
  have hα₁N : Nlog (osucc (βφ + βψ)) ≤ f 0 :=
    le_trans (Nlog_osucc_le hσNF) (by omega)
  by_cases htrue : atomTrue (Semiformula.rel rr vv)
  · -- `nrel` is FALSE: erase it from `D₂`
    have E := false_nrel_erase htrue D₂
    rw [Finset.erase_insert_eq_erase] at E
    have E' : Zef2TC βψ e H f c Γ := Zef2TC.wk E.gate (Finset.erase_subset _ _) E
    exact Zef2TC.weak hα₁N
      (lt_of_le_of_lt (Zekd.le_add_left_NF hβφNF hβψNF) (Zekd.lt_osucc hσNF))
      hβψNF hα₁NF (Cl_of_NF hβψNF) (Finset.Subset.refl _) E'
  · -- `rel` is FALSE: erase it from `D₁`
    have hntrue : atomTrue (Semiformula.nrel rr vv) :=
      (atomTrue_nrel_iff_not_rel rr vv).mpr htrue
    have E := false_rel_erase hntrue D₁
    rw [Finset.erase_insert_eq_erase] at E
    have E' : Zef2TC βφ e H f c Γ := Zef2TC.wk E.gate (Finset.erase_subset _ _) E
    exact Zef2TC.weak hα₁N
      (lt_of_le_of_lt (Zekd.le_add_right_NF hβφNF hβψNF) (Zekd.lt_osucc hσNF))
      hβφNF hα₁NF (Cl_of_NF hβφNF) (Finset.Subset.refl _) E'

/-- **`stepVerum_Zef2TC`** — the ⊤-principal top-rank cut is FREE: `∼⊤ = ⊥` and ⊥ is never
principal, so `falsum_erase` on the ⊥-side premise already derives `Γ` at ITS ordinal `βψ`. -/
theorem stepVerum_Zef2TC {βψ e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Seq}
    (D₂ : Zef2TC βψ e H f c (insert (⊥ : Form) Γ)) :
    Zef2TC βψ e H f c Γ := by
  have C := falsum_erase D₂
  rw [Finset.erase_insert_eq_erase] at C
  exact Zef2TC.wk C.gate (Finset.erase_subset _ _) C

/-! ### Block 12d — `Zef2TCProv` + the TC running-family ∀/∃ cut-reduction + `stepAllωTC_bnd`

The last reduction the TC pass needs: the port of `cutReduceAllAuxRunning_Zf2` (the Towsner
§19.6 running-family reduction, fresh root `α + γ`, output slot `g ∘ f`) to the full `Zef2TC`
rule set.  The five NEW rules are all head-inert for the erased `∃⁰ ∼φ` (truth leaves survive
the erasure; `andI`/`orI` rebuild at the fresh root exactly like `allω`), so the port is
mechanical; the live cases (`exI` principal, `cut`) are verbatim.  `stepAllωTC_bnd` then
mirrors `stepAllω_Zf2_bnd` via the banked `allω_inversion`. -/

/-- The `≤`-slack wrapper over `Zef2TC` (mirror of `Zef2Prov`). -/
def Zef2TCProv (α e : ONote) (H : ONote → Prop) (f : ℕ → ℕ) (c : ℕ) (Γ : Seq) : Prop :=
  ∃ α', α' ≤ α ∧ α'.NF ∧ Cl H α' ∧ Nlog α' ≤ f 0 ∧ Zef2TC α' e H f c Γ

namespace Zef2TCProv

theorem of {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Seq}
    (hNF : α.NF) (hH : Cl H α) (hN : Nlog α ≤ f 0) (D : Zef2TC α e H f c Γ) :
    Zef2TCProv α e H f c Γ :=
  ⟨α, le_refl _, hNF, hH, hN, D⟩

theorem mono {α β e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Seq}
    (hα : α ≤ β) : Zef2TCProv α e H f c Γ → Zef2TCProv β e H f c Γ := by
  rintro ⟨α', hα', hNF, hH, hN, D⟩
  exact ⟨α', le_trans hα' hα, hNF, hH, hN, D⟩

theorem weakening {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ Δ : Seq}
    (h : Γ ⊆ Δ) : Zef2TCProv α e H f c Γ → Zef2TCProv α e H f c Δ := by
  rintro ⟨α', hα', hNF, hH, hN, D⟩
  exact ⟨α', hα', hNF, hH, hN, Zef2TC.wk hN h D⟩

theorem mono_f {α e : ONote} {H : ONote → Prop} {f f' : ℕ → ℕ} {c : ℕ} {Γ : Seq}
    (h : ∀ x, f x ≤ f' x) : Zef2TCProv α e H f c Γ → Zef2TCProv α e H f' c Γ := by
  rintro ⟨α', hα', hNF, hH, hN, D⟩
  exact ⟨α', hα', hNF, hH, le_trans hN (h 0), D.mono_f h⟩

end Zef2TCProv

set_option maxHeartbeats 1000000 in
/-- **`cutReduceAllAuxRunning_TC`** — the running-family ∀/∃ cut-reduction over `Zef2TC`
(port of `cutReduceAllAuxRunning_Zf2`; fresh root `α + γ`, output slot `g ∘ f`). -/
theorem cutReduceAllAuxRunning_TC {φ : SyntacticSemiformula ℒₒᵣ 1} {c : ℕ} {α e : ONote}
    {Γ : Seq} {g : ℕ → ℕ} (hφc : φ.complexity < c) (hαNF : α.NF) (heNF : e.NF)
    (hg_mono : Monotone g) (hg_infl : ∀ x, x ≤ g x)
    (fam : ∀ n (H' : ONote → Prop), Zef2TC α e H' (rel1 g n) c (insert (φ/[nm n]) Γ)) :
    ∀ {γ : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {Δ : Seq}, Zef2TC γ e H f c Δ → γ.NF →
      Monotone f → (∀ x, x ≤ f x) → (∀ k, f 0 ≤ k → max (g 0) k + 1 ≤ g k) →
      φ.complexity ≤ f 0 → (∃⁰ ∼φ) ∈ Δ →
      Zef2TCProv (α + γ) e H (g ∘ f) c (Δ.erase (∃⁰ ∼φ) ∪ Γ) := by
  have hg0 : Nlog α ≤ g 0 := by
    have h := Zef2TC.gate (fam 0 (fun _ => True)); simpa [rel1] using h
  intro γ H f Δ D
  induction D with
  | @axL γ e H f c Δ ar hαN r v hp hn =>
      intro hγNF _ _ hsl _ hmem
      refine Zef2TCProv.of (ONote.add_nf α γ) (Cl_of_NF (ONote.add_nf α γ))
        (Nlog_add_le_comp hαNF hγNF hg0 hαN (hsl _ le_rfl)) ?_
      exact Zef2TC.axL (Nlog_add_le_comp hαNF hγNF hg0 hαN (hsl _ le_rfl)) r v
        (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), hp⟩))
        (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), hn⟩))
  | @trueRel γ e H f c Δ ar hαN r v htrue hmemr =>
      intro hγNF _ _ hsl _ hmem
      refine Zef2TCProv.of (ONote.add_nf α γ) (Cl_of_NF (ONote.add_nf α γ))
        (Nlog_add_le_comp hαNF hγNF hg0 hαN (hsl _ le_rfl)) ?_
      exact Zef2TC.trueRel (Nlog_add_le_comp hαNF hγNF hg0 hαN (hsl _ le_rfl)) r v htrue
        (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), hmemr⟩))
  | @trueNrel γ e H f c Δ ar hαN r v htrue hmemr =>
      intro hγNF _ _ hsl _ hmem
      refine Zef2TCProv.of (ONote.add_nf α γ) (Cl_of_NF (ONote.add_nf α γ))
        (Nlog_add_le_comp hαNF hγNF hg0 hαN (hsl _ le_rfl)) ?_
      exact Zef2TC.trueNrel (Nlog_add_le_comp hαNF hγNF hg0 hαN (hsl _ le_rfl)) r v htrue
        (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), hmemr⟩))
  | @verumR γ e H f c Δ hαN hmemv =>
      intro hγNF _ _ hsl _ hmem
      refine Zef2TCProv.of (ONote.add_nf α γ) (Cl_of_NF (ONote.add_nf α γ))
        (Nlog_add_le_comp hαNF hγNF hg0 hαN (hsl _ le_rfl)) ?_
      exact Zef2TC.verumR (Nlog_add_le_comp hαNF hγNF hg0 hαN (hsl _ le_rfl))
        (Finset.mem_union_left _ (Finset.mem_erase.mpr
          ⟨by intro h; simp [ExsQuantifier.exs] at h, hmemv⟩))
  | @wk γ e H f c Δsub Δsup hαN hsub D' ih =>
      intro hγNF hmono hinfl hsl hφread hmem
      by_cases hd : (∃⁰ ∼φ) ∈ Δsub
      · exact (ih hφc heNF fam hγNF hmono hinfl hsl hφread hd).weakening (by
          intro x hx; simp only [Finset.mem_union, Finset.mem_erase] at hx ⊢
          rcases hx with ⟨hne, hxs⟩ | hxΓ
          · exact Or.inl ⟨hne, hsub hxs⟩
          · exact Or.inr hxΓ)
      · exact ⟨γ, Zekd.le_add_left_NF hαNF hγNF, hγNF, Cl_of_NF hγNF,
          le_trans hαN (reslot_exside hg_infl 0),
          Zef2TC.wk (le_trans hαN (reslot_exside hg_infl 0)) (by
            intro x hx; simp only [Finset.mem_union, Finset.mem_erase]
            exact Or.inl ⟨fun e0 => hd (e0 ▸ hx), hsub hx⟩) (D'.mono_f (reslot_exside hg_infl))⟩
  | @weak γ β e H f c Δsub Δsup hαN hβ hβNF hγNF' hβH hsub D' ih =>
      intro hγNF hmono hinfl hsl hφread hmem
      by_cases hd : (∃⁰ ∼φ) ∈ Δsub
      · exact ((ih hφc heNF fam hβNF hmono hinfl hsl hφread hd).weakening (by
          intro x hx; simp only [Finset.mem_union, Finset.mem_erase] at hx ⊢
          rcases hx with ⟨hne, hxs⟩ | hxΓ
          · exact Or.inl ⟨hne, hsub hxs⟩
          · exact Or.inr hxΓ)).mono
          (le_of_lt (Zekd.add_lt_add_left_NF hαNF hβNF hγNF hβ))
      · exact ⟨β, le_of_lt (lt_of_lt_of_le hβ (Zekd.le_add_left_NF hαNF hγNF)), hβNF, Cl_of_NF hβNF,
          le_trans (Zef2TC.gate D') (reslot_exside hg_infl 0),
          Zef2TC.wk (le_trans (Zef2TC.gate D') (reslot_exside hg_infl 0)) (by
            intro x hx; simp only [Finset.mem_union, Finset.mem_erase]
            exact Or.inl ⟨fun e0 => hd (e0 ▸ hx), hsub hx⟩) (D'.mono_f (reslot_exside hg_infl))⟩
  | @andI γ βφ' βψ' e H f c Γ₀ hαN χ₁ χ₂ hβφ hβψ hβφNF hβψNF hγNF' hβφH hβψH d₁ d₂ ih₁ ih₂ =>
      intro hγNF hmono hinfl hsl hφread hmem
      have hhead : (χ₁ ⋏ χ₂ : Form) ≠ (∃⁰ ∼φ) := by
        intro h; simp [ExsQuantifier.exs] at h
      have hmem0 : (∃⁰ ∼φ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
      have haddNF : (α + γ).NF := ONote.add_nf α γ
      obtain ⟨a₁, ha₁le, ha₁NF, ha₁H, ha₁g, D₁⟩ := ih₁ hφc heNF fam hβφNF hmono hinfl hsl hφread
        (Finset.mem_insert_of_mem hmem0)
      obtain ⟨a₂, ha₂le, ha₂NF, ha₂H, ha₂g, D₂⟩ := ih₂ hφc heNF fam hβψNF hmono hinfl hsl hφread
        (Finset.mem_insert_of_mem hmem0)
      have D₁' : Zef2TC a₁ e H (g ∘ f) c (insert χ₁ (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) :=
        Zef2TC.wk ha₁g (by
          intro x hx
          simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢; tauto) D₁
      have D₂' : Zef2TC a₂ e H (g ∘ f) c (insert χ₂ (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) :=
        Zef2TC.wk ha₂g (by
          intro x hx
          simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢; tauto) D₂
      refine Zef2TCProv.of haddNF (Cl_of_NF haddNF)
        (Nlog_add_le_comp hαNF hγNF hg0 hαN (hsl _ le_rfl)) ?_
      have hAnd : Zef2TC (α + γ) e H (g ∘ f) c
          (insert (χ₁ ⋏ χ₂) (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) :=
        Zef2TC.andI (Nlog_add_le_comp hαNF hγNF hg0 hαN (hsl _ le_rfl)) χ₁ χ₂
          (lt_of_le_of_lt ha₁le (Zekd.add_lt_add_left_NF hαNF hβφNF hγNF hβφ))
          (lt_of_le_of_lt ha₂le (Zekd.add_lt_add_left_NF hαNF hβψNF hγNF hβψ))
          ha₁NF ha₂NF haddNF ha₁H ha₂H D₁' D₂'
      exact Zef2TC.wk (Nlog_add_le_comp hαNF hγNF hg0 hαN (hsl _ le_rfl)) (by
        intro x hx
        simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢
        rcases hx with rfl | hx
        · exact Or.inl ⟨hhead, Or.inl rfl⟩
        · tauto) hAnd
  | @orI γ β e H f c Γ₀ hαN χ₁ χ₂ hβ hβNF hγNF' hβH d₁ ih =>
      intro hγNF hmono hinfl hsl hφread hmem
      have hhead : (χ₁ ⋎ χ₂ : Form) ≠ (∃⁰ ∼φ) := by
        intro h; simp [ExsQuantifier.exs] at h
      have hmem0 : (∃⁰ ∼φ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
      have haddNF : (α + γ).NF := ONote.add_nf α γ
      obtain ⟨a, hale, haNF, haH, hag, Da⟩ := ih hφc heNF fam hβNF hmono hinfl hsl hφread
        (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hmem0))
      have Da' : Zef2TC a e H (g ∘ f) c
          (insert χ₁ (insert χ₂ (Γ₀.erase (∃⁰ ∼φ) ∪ Γ))) :=
        Zef2TC.wk hag (by
          intro x hx
          simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢; tauto) Da
      refine Zef2TCProv.of haddNF (Cl_of_NF haddNF)
        (Nlog_add_le_comp hαNF hγNF hg0 hαN (hsl _ le_rfl)) ?_
      have hOr : Zef2TC (α + γ) e H (g ∘ f) c
          (insert (χ₁ ⋎ χ₂) (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) :=
        Zef2TC.orI (Nlog_add_le_comp hαNF hγNF hg0 hαN (hsl _ le_rfl)) χ₁ χ₂
          (lt_of_le_of_lt hale (Zekd.add_lt_add_left_NF hαNF hβNF hγNF hβ))
          haNF haddNF haH Da'
      exact Zef2TC.wk (Nlog_add_le_comp hαNF hγNF hg0 hαN (hsl _ le_rfl)) (by
        intro x hx
        simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢
        rcases hx with rfl | hx
        · exact Or.inl ⟨hhead, Or.inl rfl⟩
        · tauto) hOr
  | @allω γ e H f c Γ₀ hαN χ β hβ hβNF hγNF' hβH dd ih =>
      intro hγNF hmono hinfl hsl hφread hmem
      have hhead : (∀⁰ χ) ≠ (∃⁰ ∼φ) := by intro h; simp [UnivQuantifier.all, ExsQuantifier.exs] at h
      have hmem0 : (∃⁰ ∼φ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
      have haddNF : (α + γ).NF := ONote.add_nf α γ
      have ihn : ∀ n, Zef2TCProv (α + β n) e (adjoin H n) (g ∘ rel1 f n) c
          (insert (χ/[nm n]) (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) := by
        intro n
        have hread : φ.complexity ≤ (rel1 f n) 0 := by
          simp only [rel1]; exact le_trans hφread (hmono (Nat.zero_le _))
        exact (ih n hφc heNF fam (hβNF n) (rel1_monotone hmono n) (rel1_infl hinfl n)
          (fun k hk => hsl k (le_trans (by
            simp only [rel1]; exact hmono (Nat.zero_le _)) hk))
          hread (Finset.mem_insert_of_mem hmem0)).weakening (by
            intro x hx
            simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢; tauto)
      refine Zef2TCProv.of haddNF (Cl_of_NF haddNF) (Nlog_add_le_comp hαNF hγNF hg0 hαN (hsl _ le_rfl)) ?_
      have hAll : Zef2TC (α + γ) e H (g ∘ f) c
          (insert (∀⁰ χ) (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) := by
        exact Zef2TC.allω (Nlog_add_le_comp hαNF hγNF hg0 hαN (hsl _ le_rfl)) χ (fun n => (ihn n).choose)
          (fun n => lt_of_le_of_lt (ihn n).choose_spec.1
            (Zekd.add_lt_add_left_NF hαNF (hβNF n) hγNF (hβ n)))
          (fun n => (ihn n).choose_spec.2.1) haddNF
          (fun n => Cl_of_NF (ihn n).choose_spec.2.1)
          (fun n => (ihn n).choose_spec.2.2.2.2)
      exact Zef2TC.wk (Nlog_add_le_comp hαNF hγNF hg0 hαN (hsl _ le_rfl)) (by
        intro x hx
        simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢
        rcases hx with rfl | hx
        · exact Or.inl ⟨hhead, Or.inl rfl⟩
        · tauto) hAll
  | @exI γ β e H f c Γ₀ hαN χ n hβ hβNF hγNF' hβH hbound dχ ih =>
      intro hγNF hmono hinfl hsl hφread hmem
      have haddNF : (α + γ).NF := ONote.add_nf α γ
      by_cases hhd : (∃⁰ χ) = (∃⁰ ∼φ)
      · have hχ : χ = ∼φ := by simpa [ExsQuantifier.exs] using hhd
        subst hχ
        rw [Finset.erase_insert_eq_erase]
        have hNeg : (∼φ)/[nm n] = ∼(φ/[nm n]) := by simp
        have hcompl : (φ/[nm n]).complexity < c := by simpa using hφc
        have hcutRead : (φ/[nm n]).complexity ≤ (g ∘ f) 0 := by
          have he : (φ/[nm n]).complexity = φ.complexity := by simp
          rw [he]; exact le_trans hφread (hg_infl (f 0))
        have hg0comp : Nlog α ≤ (g ∘ f) 0 := le_trans hg0 (hg_mono (Nat.zero_le _))
        have famn : Zef2TC α e H (g ∘ f) c (insert (φ/[nm n]) (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) :=
          Zef2TC.wk hg0comp (by
            intro x hx; simp only [Finset.mem_insert, Finset.mem_union] at hx ⊢; tauto)
            ((fam n H).mono_f (reslot_family hg_mono hinfl hmono hbound))
        have hαlt : α < α + γ := by
          haveI := hαNF; haveI := hγNF
          refine ONote.lt_def.mpr ?_
          rw [ONote.repr_add]
          have hγpos : (0 : Ordinal) < γ.repr := lt_of_le_of_lt (by simp) (ONote.lt_def.mp hβ)
          simpa using (add_lt_add_iff_left α.repr).mpr hγpos
        by_cases hd : (∃⁰ ∼φ) ∈ Γ₀
        · obtain ⟨a, hale, haNF, haH, hag, Da⟩ := ih hφc heNF fam hβNF hmono hinfl hsl hφread
            (Finset.mem_insert_of_mem hd)
          have Da' : Zef2TC a e H (g ∘ f) c
              (insert (∼(φ/[nm n])) (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) :=
            Zef2TC.wk hag (by
              intro x hx
              simp only [hNeg, Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢; tauto) Da
          refine Zef2TCProv.of haddNF (Cl_of_NF haddNF) (Nlog_add_le_comp hαNF hγNF hg0 hαN (hsl _ le_rfl)) ?_
          exact Zef2TC.cut (Nlog_add_le_comp hαNF hγNF hg0 hαN (hsl _ le_rfl)) (φ/[nm n]) hcompl hcutRead hαlt
            (lt_of_le_of_lt hale (Zekd.add_lt_add_left_NF hαNF hβNF hγNF hβ))
            hαNF haNF haddNF (Cl_of_NF hαNF) haH famn Da'
        · have Dβ' : Zef2TC β e H (g ∘ f) c
              (insert (∼(φ/[nm n])) (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) :=
            Zef2TC.wk (le_trans (Zef2TC.gate dχ) (reslot_exside hg_infl 0)) (by
              intro x hx
              simp only [hNeg, Finset.mem_insert] at hx
              simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_erase]
              rcases hx with rfl | hxΓ₀
              · exact Or.inl rfl
              · exact Or.inr (Or.inl ⟨fun e0 => hd (e0 ▸ hxΓ₀), hxΓ₀⟩))
              (dχ.mono_f (reslot_exside hg_infl))
          refine Zef2TCProv.of haddNF (Cl_of_NF haddNF) (Nlog_add_le_comp hαNF hγNF hg0 hαN (hsl _ le_rfl)) ?_
          exact Zef2TC.cut (Nlog_add_le_comp hαNF hγNF hg0 hαN (hsl _ le_rfl)) (φ/[nm n]) hcompl hcutRead hαlt
            (lt_of_lt_of_le hβ (Zekd.le_add_left_NF hαNF hγNF))
            hαNF hβNF haddNF (Cl_of_NF hαNF) (Cl_of_NF hβNF) famn Dβ'
      · have hmem0 : (∃⁰ ∼φ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhd e.symm
        obtain ⟨a, hale, haNF, haH, hag, Da⟩ := ih hφc heNF fam hβNF hmono hinfl hsl hφread
          (Finset.mem_insert_of_mem hmem0)
        have Da' : Zef2TC a e H (g ∘ f) c (insert (χ/[nm n]) (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) :=
          Zef2TC.wk hag (by
            intro x hx
            simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢; tauto) Da
        refine Zef2TCProv.of haddNF (Cl_of_NF haddNF) (Nlog_add_le_comp hαNF hγNF hg0 hαN (hsl _ le_rfl)) ?_
        have hbound' : n ≤ (g ∘ f) 0 := le_trans hbound (hg_infl (f 0))
        exact Zef2TC.wk (Nlog_add_le_comp hαNF hγNF hg0 hαN (hsl _ le_rfl)) (by
          intro x hx
          simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢
          rcases hx with rfl | hx
          · exact Or.inl ⟨hhd, Or.inl rfl⟩
          · tauto)
          (Zef2TC.exI (Nlog_add_le_comp hαNF hγNF hg0 hαN (hsl _ le_rfl)) χ n
            (lt_of_le_of_lt hale (Zekd.add_lt_add_left_NF hαNF hβNF hγNF hβ))
            haNF haddNF haH hbound' Da')
  | @cut γ βφ βψ e H f c Γ₀ hαN χ hχc hcutRead' hβφ hβψ hβφNF hβψNF hγNF' hβφH hβψH d₁ d₂ ih₁ ih₂ =>
      intro hγNF hmono hinfl hsl hφread hmem
      obtain ⟨a₁, ha₁le, ha₁NF, ha₁H, ha₁g, D₁⟩ := ih₁ hφc heNF fam hβφNF hmono hinfl hsl hφread
        (Finset.mem_insert_of_mem hmem)
      obtain ⟨a₂, ha₂le, ha₂NF, ha₂H, ha₂g, D₂⟩ := ih₂ hφc heNF fam hβψNF hmono hinfl hsl hφread
        (Finset.mem_insert_of_mem hmem)
      have haddNF : (α + γ).NF := ONote.add_nf α γ
      have D₁' : Zef2TC a₁ e H (g ∘ f) c (insert χ (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) :=
        Zef2TC.wk ha₁g (by
          intro x hx
          simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢; tauto) D₁
      have D₂' : Zef2TC a₂ e H (g ∘ f) c (insert (∼χ) (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) :=
        Zef2TC.wk ha₂g (by
          intro x hx
          simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢; tauto) D₂
      refine Zef2TCProv.of haddNF (Cl_of_NF haddNF) (Nlog_add_le_comp hαNF hγNF hg0 hαN (hsl _ le_rfl)) ?_
      exact Zef2TC.cut (Nlog_add_le_comp hαNF hγNF hg0 hαN (hsl _ le_rfl)) χ hχc
        (le_trans hcutRead' (hg_infl (f 0)))
        (lt_of_le_of_lt ha₁le (Zekd.add_lt_add_left_NF hαNF hβφNF hγNF hβφ))
        (lt_of_le_of_lt ha₂le (Zekd.add_lt_add_left_NF hαNF hβψNF hγNF hβψ))
        ha₁NF ha₂NF haddNF ha₁H ha₂H D₁' D₂'

/-- **`stepAllωTC_bnd`** — the bound-exposing principal ∀/∃ cut-reduction step over `Zef2TC`
(mirror of `stepAllω_Zf2_bnd`): invert the ∀-side via `allω_inversion`, feed the running
reduction; output witness ordinal bounded by `P₁ + P₂`. -/
theorem stepAllωTC_bnd {E : ONote} {H : ONote → Prop} {c : ℕ} {Γ : Seq}
    {χ : SyntacticSemiformula ℒₒᵣ 1} {P₁ P₂ : ONote} {f g : ℕ → ℕ}
    (hP₁ : P₁.NF) (hP₂ : P₂.NF)
    (hENF : E.NF) (hχc : χ.complexity < c)
    (hg_mono : Monotone g) (hg_infl : ∀ x, x ≤ g x)
    (hg_slack : ∀ k, f 0 ≤ k → max (g 0) k + 1 ≤ g k)
    (hf_mono : Monotone f) (hf_infl : ∀ x, x ≤ f x) (hχRead : χ.complexity ≤ f 0)
    (D₁ : Zef2TCProv P₁ E H g c (insert (∀⁰ χ) Γ))
    (D₂ : Zef2TCProv P₂ E H f c (insert (∃⁰ ∼χ) Γ)) :
    Zef2TCProv (P₁ + P₂) E H (g ∘ f) c Γ := by
  obtain ⟨α₁, hα₁le, hNF₁, _, _, d₁⟩ := D₁
  obtain ⟨γ₁, hγ₁le, hNF₂, _, _, d₂⟩ := D₂
  have fam : ∀ n (H' : ONote → Prop), Zef2TC α₁ E H' (rel1 g n) c (insert (χ/[nm n]) Γ) := by
    intro n H'
    have hinv := allω_inversion (φ := χ) n d₁ hg_mono
    rw [Finset.erase_insert_eq_erase] at hinv
    exact (Zef2TC.wk (Zef2TC.gate hinv)
      (Finset.insert_subset_insert _ (Finset.erase_subset _ _)) hinv).change_H
  have hred := cutReduceAllAuxRunning_TC hχc hNF₁ hENF hg_mono hg_infl fam
    d₂ hNF₂ hf_mono hf_infl hg_slack hχRead (Finset.mem_insert_self _ _)
  have hbnd : α₁ + γ₁ ≤ P₁ + P₂ := by
    haveI := hNF₁; haveI := hNF₂; haveI := hP₁; haveI := hP₂
    rw [ONote.le_def, ONote.repr_add, ONote.repr_add]
    exact add_le_add (ONote.le_def.mp hα₁le) (ONote.le_def.mp hγ₁le)
  exact ((hred.weakening
    (Finset.union_subset (Finset.erase_insert_subset _ _) (Finset.Subset.refl Γ))).mono hbnd)

/-! ### Block 12e — `passAuxTC`: the cut-elimination pass over `Zef2TC`

The port of `passAux` to the full rule set.  New leaves (`trueRel`/`trueNrel`/`verumR`) rebuild
at `collapse α` like `axL`; `andI`/`orI` rebuild like `exI` (two/one premises, slot-lifted).
The top-rank cut dispatches by cut-formula shape to the four banked reductions:
∀/∃ → `stepAllωTC_bnd`; ⋏/⋎ → `stepAnd_Zef2TC`; ⊤/⊥ → `stepVerum_Zef2TC`; atoms →
`stepAtom_Zef2TC`.  The finite steps' `osucc` roots sit under `collapse α = ω^α` by additive
principality + limit headroom (`osucc_lt_collapse`), and their `Nlog … + 2` gates are paid by
one extra threaded base-slack conjunct `3 ≤ f 0` (preserved by `rel1`, satisfied by every real
root slot: `ewRootSlot … 0 ≥ 3`). -/

/-- Successor headroom under the collapse: `collapse α = ω^α` is a limit for `α > 0`, so
`σ < collapse α → osucc σ < collapse α` (additive principality with `1 < ω^α`). -/
theorem osucc_lt_collapse {σ α : ONote} (hσNF : σ.NF) (_hαNF : α.NF)
    (hαpos : (0 : ONote) < α) (h : σ < collapse α) : osucc σ < collapse α := by
  haveI := hσNF; haveI := _hαNF
  refine ONote.lt_def.mpr ?_
  rw [repr_osucc hσNF, repr_collapse]
  have h1 : σ.repr < Ordinal.omega0 ^ α.repr := by
    have := ONote.lt_def.mp h
    rwa [repr_collapse] at this
  have h0 : (0 : Ordinal) < α.repr := by simpa using ONote.lt_def.mp hαpos
  have h2 : (1 : Ordinal) < Ordinal.omega0 ^ α.repr :=
    lt_of_lt_of_le Ordinal.one_lt_omega0 (Ordinal.left_le_opow _ h0)
  exact Ordinal.isPrincipal_add_omega0_opow α.repr h1 h2

set_option maxHeartbeats 3200000 in
/-- **`passAuxTC`** — one cut-elimination pass over `Zef2TC` (port of `passAux`): the ordinal
collapses (`collapse α`), the slot iterates (`ewIter f α`), the rank drops `c+1 → c`. -/
theorem passAuxTC (c : ℕ) {e : ONote} (heNF : e.NF) :
    ∀ {α : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {Γ : Seq} {r : ℕ},
      Zef2TC α e H f r Γ → r = c + 1 → Monotone f → (∀ x, x ≤ f x) → (∀ m, 2 * m + 1 ≤ f m) →
      3 ≤ f 0 → α.NF → Cl H α →
      Zef2TCProv (collapse α) e H (ewIter f α) c Γ := by
  intro α H f Γ r D
  induction D with
  | @axL α e H f r Γ ar hαN rel v hp hn =>
      intro hr hmono hinfl hlow hbase3 hαNF hαH
      have hg := Nlog_collapse_le hlow hαN
      exact Zef2TCProv.of (collapse_NF hαNF) (Cl_of_NF (collapse_NF hαNF)) hg
        (Zef2TC.axL hg rel v hp hn)
  | @trueRel α e H f r Γ ar hαN rel v htrue hmem =>
      intro hr hmono hinfl hlow hbase3 hαNF hαH
      have hg := Nlog_collapse_le hlow hαN
      exact Zef2TCProv.of (collapse_NF hαNF) (Cl_of_NF (collapse_NF hαNF)) hg
        (Zef2TC.trueRel hg rel v htrue hmem)
  | @trueNrel α e H f r Γ ar hαN rel v htrue hmem =>
      intro hr hmono hinfl hlow hbase3 hαNF hαH
      have hg := Nlog_collapse_le hlow hαN
      exact Zef2TCProv.of (collapse_NF hαNF) (Cl_of_NF (collapse_NF hαNF)) hg
        (Zef2TC.trueNrel hg rel v htrue hmem)
  | @verumR α e H f r Γ hαN hmem =>
      intro hr hmono hinfl hlow hbase3 hαNF hαH
      have hg := Nlog_collapse_le hlow hαN
      exact Zef2TCProv.of (collapse_NF hαNF) (Cl_of_NF (collapse_NF hαNF)) hg
        (Zef2TC.verumR hg hmem)
  | @wk α e H f r Δ Γ hαN hsub D' ih =>
      intro hr hmono hinfl hlow hbase3 hαNF hαH
      exact (ih heNF hr hmono hinfl hlow hbase3 hαNF hαH).weakening hsub
  | @weak α β e H f r Δ Γ hαN hβ hβNF hαNF' hβH hsub D' ih =>
      intro hr hmono hinfl hlow hbase3 hαNF hαH
      obtain ⟨a, hale, haNF, haH, hag, Da⟩ := ih heNF hr hmono hinfl hlow hbase3 hβNF (Cl_of_NF hβNF)
      have hslot := ewIter_slot_le hmono hinfl hβNF hβ (Zef2TC.gate D')
      exact ⟨a, le_trans hale (le_of_lt (collapse_strictMono hβNF hβ)), haNF, haH,
        le_trans hag (hslot 0), Zef2TC.wk (le_trans hag (hslot 0)) hsub (Da.mono_f hslot)⟩
  | @andI α βφ βψ e H f r Γ hαN φ ψ hβφ hβψ hβφNF hβψNF hαNF' hβφH hβψH dφ dψ ih₁ ih₂ =>
      intro hr hmono hinfl hlow hbase3 hαNF hαH
      have hg := Nlog_collapse_le hlow hαN
      obtain ⟨a₁, ha₁le, ha₁NF, ha₁H, ha₁g, D₁⟩ :=
        ih₁ heNF hr hmono hinfl hlow hbase3 hβφNF (Cl_of_NF hβφNF)
      obtain ⟨a₂, ha₂le, ha₂NF, ha₂H, ha₂g, D₂⟩ :=
        ih₂ heNF hr hmono hinfl hlow hbase3 hβψNF (Cl_of_NF hβψNF)
      have hsφ := ewIter_slot_le hmono hinfl hβφNF hβφ (Zef2TC.gate dφ)
      have hsψ := ewIter_slot_le hmono hinfl hβψNF hβψ (Zef2TC.gate dψ)
      refine Zef2TCProv.of (collapse_NF hαNF) (Cl_of_NF (collapse_NF hαNF)) hg ?_
      exact Zef2TC.andI hg φ ψ
        (lt_of_le_of_lt ha₁le (collapse_strictMono hβφNF hβφ))
        (lt_of_le_of_lt ha₂le (collapse_strictMono hβψNF hβψ))
        ha₁NF ha₂NF (collapse_NF hαNF) ha₁H ha₂H (D₁.mono_f hsφ) (D₂.mono_f hsψ)
  | @orI α β e H f r Γ hαN φ ψ hβ hβNF hαNF' hβH dd ih =>
      intro hr hmono hinfl hlow hbase3 hαNF hαH
      have hg := Nlog_collapse_le hlow hαN
      obtain ⟨a, hale, haNF, haH, hag, Da⟩ :=
        ih heNF hr hmono hinfl hlow hbase3 hβNF (Cl_of_NF hβNF)
      have hslot := ewIter_slot_le hmono hinfl hβNF hβ (Zef2TC.gate dd)
      refine Zef2TCProv.of (collapse_NF hαNF) (Cl_of_NF (collapse_NF hαNF)) hg ?_
      exact Zef2TC.orI hg φ ψ
        (lt_of_le_of_lt hale (collapse_strictMono hβNF hβ))
        haNF (collapse_NF hαNF) haH (Da.mono_f hslot)
  | @allω α e H f r Γ hαN χ β hβ hβNF hαNF' hβH dd ih =>
      intro hr hmono hinfl hlow hbase3 hαNF hαH
      have hg := Nlog_collapse_le hlow hαN
      have hbranch : ∀ n, Zef2TCProv (collapse (β n)) e (adjoin H n)
          (ewIter (rel1 f n) (β n)) c (insert (χ/[nm n]) Γ) := fun n =>
        ih n heNF hr (rel1_monotone hmono n) (rel1_infl hinfl n) (rel1_low hmono hlow n)
          (le_trans hbase3 (by simp only [rel1]; exact hmono (Nat.zero_le _)))
          (hβNF n) (Cl_of_NF (hβNF n))
      choose a hale haNF haH hagate Da using hbranch
      have hlift : ∀ n x, ewIter (rel1 f n) (β n) x ≤ rel1 (ewIter f α) n x := by
        intro n x
        refine le_trans (ewIter_rel1_le hmono hinfl (β n) n x) ?_
        have hgate : Nlog (β n) ≤ f (Nlog α + max n x) := by
          have hgn := Zef2TC.gate (dd n)
          simp only [rel1] at hgn
          refine le_trans hgn (hmono ?_)
          omega
        simpa [rel1] using ewIter_le_of_lt (f := f) hinfl (hβNF n) (hβ n) hgate
      have Da' : ∀ n, Zef2TC (a n) e (adjoin H n) (rel1 (ewIter f α) n) c
          (insert (χ/[nm n]) Γ) := fun n => (Da n).mono_f (hlift n)
      have haltcol : ∀ n, a n < collapse α :=
        fun n => lt_of_le_of_lt (hale n) (collapse_strictMono (hβNF n) (hβ n))
      refine Zef2TCProv.of (collapse_NF hαNF) (Cl_of_NF (collapse_NF hαNF)) hg ?_
      exact Zef2TC.allω hg χ a haltcol haNF (collapse_NF hαNF)
        (fun n => Cl_of_NF (haNF n)) Da'
  | @exI α β e H f r Γ hαN χ n hβ hβNF hαNF' hβH hbound dχ ih =>
      intro hr hmono hinfl hlow hbase3 hαNF hαH
      obtain ⟨a, hale, haNF, haH, hag, Da⟩ :=
        ih heNF hr hmono hinfl hlow hbase3 hβNF (Cl_of_NF hβNF)
      have hslot := ewIter_slot_le hmono hinfl hβNF hβ (Zef2TC.gate dχ)
      have haltcol : a < collapse α := lt_of_le_of_lt hale (collapse_strictMono hβNF hβ)
      have hg := Nlog_collapse_le hlow hαN
      have hbound' : n ≤ ewIter f α 0 := le_trans hbound (ewIter_base_le hinfl α)
      refine Zef2TCProv.of (collapse_NF hαNF) (Cl_of_NF (collapse_NF hαNF)) hg ?_
      exact Zef2TC.exI hg χ n haltcol haNF (collapse_NF hαNF) haH hbound'
        (Zef2TC.wk (le_trans hag (hslot 0)) (Finset.Subset.refl _) (Da.mono_f hslot))
  | @cut α βφ βψ e H f r Γ hαN χ hcompl hcutRead hβφ hβψ hβφNF hβψNF hαNF' hβφH hβψH d₁ d₂ ih₁ ih₂ =>
      intro hr hmono hinfl hlow hbase3 hαNF hαH
      have hg := Nlog_collapse_le hlow hαN
      have hf0 : f 0 ≤ ewIter f α 0 := ewIter_base_le hinfl α
      have hαpos : (0 : ONote) < α := by
        cases α with
        | zero => exact absurd (ONote.lt_def.mp hβφ) not_lt_zero
        | oadd e' n' a' => exact oadd_pos e' n' a'
      by_cases hc : χ.complexity < c
      · -- SUB-RANK cut: keep it, rebuild at rank `c`
        obtain ⟨aφ, haφle, haφNF, haφH, haφg, Dφ⟩ :=
          ih₁ heNF hr hmono hinfl hlow hbase3 hβφNF (Cl_of_NF hβφNF)
        obtain ⟨aψ, haψle, haψNF, haψH, haψg, Dψ⟩ :=
          ih₂ heNF hr hmono hinfl hlow hbase3 hβψNF (Cl_of_NF hβψNF)
        have hsφ := ewIter_slot_le hmono hinfl hβφNF hβφ (Zef2TC.gate d₁)
        have hsψ := ewIter_slot_le hmono hinfl hβψNF hβψ (Zef2TC.gate d₂)
        have haφcol : aφ < collapse α := lt_of_le_of_lt haφle (collapse_strictMono hβφNF hβφ)
        have haψcol : aψ < collapse α := lt_of_le_of_lt haψle (collapse_strictMono hβψNF hβψ)
        refine Zef2TCProv.of (collapse_NF hαNF) (Cl_of_NF (collapse_NF hαNF)) hg ?_
        exact Zef2TC.cut hg χ hc (le_trans hcutRead hf0) haφcol haψcol
          haφNF haψNF (collapse_NF hαNF) haφH haψH (Dφ.mono_f hsφ) (Dψ.mono_f hsψ)
      · -- TOP-RANK cut: eliminate by cut-formula shape
        have hgφ : Nlog βφ ≤ f 0 := Zef2TC.gate d₁
        have hgψ : Nlog βψ ≤ f 0 := Zef2TC.gate d₂
        have hcomp : ∀ m, ewIter f βφ (ewIter f βψ m) ≤ ewIter f α m :=
          ewIter_comp_le hmono hinfl hβφNF hβψNF hβφ hβψ hgφ hgψ
        have hcomp' : ∀ m, ewIter f βψ (ewIter f βφ m) ≤ ewIter f α m :=
          ewIter_comp_le hmono hinfl hβψNF hβφNF hβψ hβφ hgψ hgφ
        have hcollt : collapse βφ + collapse βψ < collapse α :=
          collapse_add_lt hβφNF hβψNF hαNF hβφ hβψ
        have hcollt' : collapse βψ + collapse βφ < collapse α :=
          collapse_add_lt hβψNF hβφNF hαNF hβψ hβφ
        have P₁ := ih₁ heNF hr hmono hinfl hlow hbase3 hβφNF (Cl_of_NF hβφNF)
        have P₂ := ih₂ heNF hr hmono hinfl hlow hbase3 hβψNF (Cl_of_NF hβψNF)
        have hsφ := ewIter_slot_le hmono hinfl hβφNF hβφ hgφ
        have hsψ := ewIter_slot_le hmono hinfl hβψNF hβψ hgψ
        -- the `Nlog … + 2` gate for the finite-step roots, paid by `hbase3` + `ewIter_low`
        have hFφ : 2 * ewIter f βφ 0 + 1 ≤ ewIter f α 0 :=
          le_trans (ewIter_low hinfl hlow βφ _)
            (ewIter_lower hβφNF hβφ (le_trans hgφ (hmono (Nat.zero_le _))))
        have hFψ : 2 * ewIter f βψ 0 + 1 ≤ ewIter f α 0 :=
          le_trans (ewIter_low hinfl hlow βψ _)
            (ewIter_lower hβψNF hβψ (le_trans hgψ (hmono (Nat.zero_le _))))
        have hxφ3 : 3 ≤ ewIter f βφ 0 := le_trans hbase3 (ewIter_base_le hinfl βφ)
        have hxψ3 : 3 ≤ ewIter f βψ 0 := le_trans hbase3 (ewIter_base_le hinfl βψ)
        cases χ with
        | verum =>
            obtain ⟨a₂, ha₂le, ha₂NF, ha₂H, ha₂g, Da₂⟩ := P₂
            have Da₂' : Zef2TC a₂ e H (ewIter f βψ) c (insert (⊥ : Form) Γ) := Da₂
            have hD := stepVerum_Zef2TC Da₂'
            exact ⟨a₂, le_trans ha₂le (le_of_lt (collapse_strictMono hβψNF hβψ)), ha₂NF, ha₂H,
              le_trans ha₂g (hsψ 0), hD.mono_f hsψ⟩
        | falsum =>
            obtain ⟨a₁, ha₁le, ha₁NF, ha₁H, ha₁g, Da₁⟩ := P₁
            have hD := stepVerum_Zef2TC Da₁
            exact ⟨a₁, le_trans ha₁le (le_of_lt (collapse_strictMono hβφNF hβφ)), ha₁NF, ha₁H,
              le_trans ha₁g (hsφ 0), hD.mono_f hsφ⟩
        | and φ₁ φ₂ =>
            have hcR := hcutRead
            have hcm := hcompl
            have hcn := hc
            simp only [Semiformula.complexity_and'] at hcR hcm hcn
            have hφ₁c : φ₁.complexity < c := by omega
            have hφ₂c : φ₂.complexity < c := by omega
            have hread₁ : φ₁.complexity ≤ ewIter f α 0 := by omega
            have hread₂ : φ₂.complexity ≤ ewIter f α 0 := by omega
            obtain ⟨a₁, ha₁le, ha₁NF, ha₁H, ha₁g, Da₁⟩ := P₁
            obtain ⟨a₂, ha₂le, ha₂NF, ha₂H, ha₂g, Da₂'⟩ := P₂
            have Da₂ : Zef2TC a₂ e H (ewIter f βψ) c (insert (∼φ₁ ⋎ ∼φ₂) Γ) := Da₂'
            have hb1 := Nlog_add_le_max_succ a₁ ha₁NF a₂ ha₂NF
            have hgate : Nlog (a₁ + a₂) + 2 ≤ ewIter f α 0 := by
              have h₁ := hsφ 0
              have h₂ := hsψ 0
              omega
            have hstep := stepAnd_Zef2TC ha₁NF ha₂NF hφ₁c hφ₂c hread₁ hread₂ hgate
              (Da₁.mono_f hsφ) (Da₂.mono_f hsψ)
            have hσNF : (a₁ + a₂).NF := ONote.add_nf a₁ a₂
            have hσlt : a₁ + a₂ < collapse α := by
              refine lt_of_le_of_lt ?_ hcollt
              haveI := ha₁NF; haveI := ha₂NF
              haveI := collapse_NF hβφNF; haveI := collapse_NF hβψNF
              haveI := ONote.add_nf a₁ a₂
              haveI := ONote.add_nf (collapse βφ) (collapse βψ)
              rw [ONote.le_def, ONote.repr_add, ONote.repr_add]
              exact add_le_add (ONote.le_def.mp ha₁le) (ONote.le_def.mp ha₂le)
            have h1 := osucc_lt_collapse hσNF hαNF hαpos hσlt
            have h2 := osucc_lt_collapse (osucc_NF hσNF) hαNF hαpos h1
            have hNg : Nlog (osucc (osucc (a₁ + a₂))) ≤ ewIter f α 0 := by
              have hs1 := Nlog_osucc_le hσNF
              have hs2 := Nlog_osucc_le (osucc_NF hσNF)
              omega
            exact ⟨osucc (osucc (a₁ + a₂)), le_of_lt h2, osucc_NF (osucc_NF hσNF),
              Cl_of_NF (osucc_NF (osucc_NF hσNF)), hNg, hstep⟩
        | or φ₁ φ₂ =>
            have hcR := hcutRead
            have hcm := hcompl
            have hcn := hc
            simp only [Semiformula.complexity_or'] at hcR hcm hcn
            have hn₁ : (∼φ₁ : Form).complexity = φ₁.complexity := Semiformula.complexity_neg φ₁
            have hn₂ : (∼φ₂ : Form).complexity = φ₂.complexity := Semiformula.complexity_neg φ₂
            have hφ₁c : (∼φ₁ : Form).complexity < c := by omega
            have hφ₂c : (∼φ₂ : Form).complexity < c := by omega
            have hread₁ : (∼φ₁ : Form).complexity ≤ ewIter f α 0 := by omega
            have hread₂ : (∼φ₂ : Form).complexity ≤ ewIter f α 0 := by omega
            obtain ⟨a₁, ha₁le, ha₁NF, ha₁H, ha₁g, Da₁⟩ := P₁
            obtain ⟨a₂, ha₂le, ha₂NF, ha₂H, ha₂g, Da₂'⟩ := P₂
            have Da₂ : Zef2TC a₂ e H (ewIter f βψ) c (insert (∼φ₁ ⋏ ∼φ₂) Γ) := Da₂'
            have hd₁ : Zef2TC a₁ e H (ewIter f α) c (insert (∼(∼φ₁) ⋎ ∼(∼φ₂)) Γ) := by
              rw [show (∼(∼φ₁) ⋎ ∼(∼φ₂) : Form) = φ₁ ⋎ φ₂ from by simp]
              exact Da₁.mono_f hsφ
            have hb1 := Nlog_add_le_max_succ a₂ ha₂NF a₁ ha₁NF
            have hgate : Nlog (a₂ + a₁) + 2 ≤ ewIter f α 0 := by
              have h₁ := hsφ 0
              have h₂ := hsψ 0
              omega
            have hstep := stepAnd_Zef2TC ha₂NF ha₁NF hφ₁c hφ₂c hread₁ hread₂ hgate
              (Da₂.mono_f hsψ) hd₁
            have hσNF : (a₂ + a₁).NF := ONote.add_nf a₂ a₁
            have hσlt : a₂ + a₁ < collapse α := by
              refine lt_of_le_of_lt ?_ hcollt'
              haveI := ha₁NF; haveI := ha₂NF
              haveI := collapse_NF hβφNF; haveI := collapse_NF hβψNF
              haveI := ONote.add_nf a₂ a₁
              haveI := ONote.add_nf (collapse βψ) (collapse βφ)
              rw [ONote.le_def, ONote.repr_add, ONote.repr_add]
              exact add_le_add (ONote.le_def.mp ha₂le) (ONote.le_def.mp ha₁le)
            have h1 := osucc_lt_collapse hσNF hαNF hαpos hσlt
            have h2 := osucc_lt_collapse (osucc_NF hσNF) hαNF hαpos h1
            have hNg : Nlog (osucc (osucc (a₂ + a₁))) ≤ ewIter f α 0 := by
              have hs1 := Nlog_osucc_le hσNF
              have hs2 := Nlog_osucc_le (osucc_NF hσNF)
              omega
            exact ⟨osucc (osucc (a₂ + a₁)), le_of_lt h2, osucc_NF (osucc_NF hσNF),
              Cl_of_NF (osucc_NF (osucc_NF hσNF)), hNg, hstep⟩
        | rel r' v' =>
            obtain ⟨a₁, ha₁le, ha₁NF, ha₁H, ha₁g, Da₁⟩ := P₁
            obtain ⟨a₂, ha₂le, ha₂NF, ha₂H, ha₂g, Da₂⟩ := P₂
            have Da₂n : Zef2TC a₂ e H (ewIter f βψ) c (insert (Semiformula.nrel r' v') Γ) := Da₂
            have hb1 := Nlog_add_le_max_succ a₁ ha₁NF a₂ ha₂NF
            have hgate : Nlog (a₁ + a₂) + 1 ≤ ewIter f α 0 := by
              have h₁ := hsφ 0
              have h₂ := hsψ 0
              omega
            have hstep := stepAtom_Zef2TC ha₁NF ha₂NF hgate
              (Da₁.mono_f hsφ) (Da₂n.mono_f hsψ)
            have hσNF : (a₁ + a₂).NF := ONote.add_nf a₁ a₂
            have hσlt : a₁ + a₂ < collapse α := by
              refine lt_of_le_of_lt ?_ hcollt
              haveI := ha₁NF; haveI := ha₂NF
              haveI := collapse_NF hβφNF; haveI := collapse_NF hβψNF
              haveI := ONote.add_nf a₁ a₂
              haveI := ONote.add_nf (collapse βφ) (collapse βψ)
              rw [ONote.le_def, ONote.repr_add, ONote.repr_add]
              exact add_le_add (ONote.le_def.mp ha₁le) (ONote.le_def.mp ha₂le)
            have h1 := osucc_lt_collapse hσNF hαNF hαpos hσlt
            have hNg : Nlog (osucc (a₁ + a₂)) ≤ ewIter f α 0 := by
              have hs1 := Nlog_osucc_le hσNF
              omega
            exact ⟨osucc (a₁ + a₂), le_of_lt h1, osucc_NF hσNF, Cl_of_NF (osucc_NF hσNF), hNg, hstep⟩
        | nrel r' v' =>
            obtain ⟨a₁, ha₁le, ha₁NF, ha₁H, ha₁g, Da₁⟩ := P₁
            obtain ⟨a₂, ha₂le, ha₂NF, ha₂H, ha₂g, Da₂⟩ := P₂
            have Da₂n : Zef2TC a₂ e H (ewIter f βψ) c (insert (Semiformula.rel r' v') Γ) := Da₂
            have hb1 := Nlog_add_le_max_succ a₂ ha₂NF a₁ ha₁NF
            have hgate : Nlog (a₂ + a₁) + 1 ≤ ewIter f α 0 := by
              have h₁ := hsφ 0
              have h₂ := hsψ 0
              omega
            have hstep := stepAtom_Zef2TC ha₂NF ha₁NF hgate
              (Da₂n.mono_f hsψ) (Da₁.mono_f hsφ)
            have hσNF : (a₂ + a₁).NF := ONote.add_nf a₂ a₁
            have hσlt : a₂ + a₁ < collapse α := by
              refine lt_of_le_of_lt ?_ hcollt'
              haveI := ha₁NF; haveI := ha₂NF
              haveI := collapse_NF hβφNF; haveI := collapse_NF hβψNF
              haveI := ONote.add_nf a₂ a₁
              haveI := ONote.add_nf (collapse βψ) (collapse βφ)
              rw [ONote.le_def, ONote.repr_add, ONote.repr_add]
              exact add_le_add (ONote.le_def.mp ha₂le) (ONote.le_def.mp ha₁le)
            have h1 := osucc_lt_collapse hσNF hαNF hαpos hσlt
            have hNg : Nlog (osucc (a₂ + a₁)) ≤ ewIter f α 0 := by
              have hs1 := Nlog_osucc_le hσNF
              omega
            exact ⟨osucc (a₂ + a₁), le_of_lt h1, osucc_NF hσNF, Cl_of_NF (osucc_NF hσNF), hNg, hstep⟩
        | all ψ =>
            have h : (Semiformula.all ψ : Form).complexity = ψ.complexity + 1 := rfl
            have hψc : ψ.complexity < c := by omega
            have hread : ψ.complexity ≤ ewIter f βψ 0 := by
              have h2 : ψ.complexity ≤ f 0 := by omega
              exact le_trans h2 (ewIter_base_le hinfl βψ)
            have hstep := stepAllωTC_bnd (collapse_NF hβφNF) (collapse_NF hβψNF) heNF hψc
              (ewIter_monotone hmono hinfl βφ) (ewIter_infl hinfl βφ)
              (hslack_kit_ge hmono hinfl hlow βφ βψ)
              (ewIter_monotone hmono hinfl βψ) (ewIter_infl hinfl βψ) hread P₁ P₂
            obtain ⟨w, hwle, hwNF, hwH, hwg, Dw⟩ := hstep
            exact ⟨w, le_trans hwle (le_of_lt hcollt), hwNF, hwH,
              le_trans hwg (hcomp 0), Dw.mono_f hcomp⟩
        | exs ψ =>
            have h : (Semiformula.exs ψ : Form).complexity = ψ.complexity + 1 := rfl
            have h2 : (∼ψ).complexity = ψ.complexity := Semiformula.complexity_neg ψ
            have hψc : (∼ψ).complexity < c := by omega
            have hread : (∼ψ).complexity ≤ ewIter f βφ 0 := by
              have h3 : (∼ψ).complexity ≤ f 0 := by omega
              exact le_trans h3 (ewIter_base_le hinfl βφ)
            have P₁' : Zef2TCProv (collapse βφ) e H (ewIter f βφ) c (insert (∃⁰ ∼(∼ψ)) Γ) := by
              have hnn : (∼(∼ψ)) = ψ := by simp
              rw [hnn]
              exact P₁
            have hstep := stepAllωTC_bnd (collapse_NF hβψNF) (collapse_NF hβφNF) heNF hψc
              (ewIter_monotone hmono hinfl βψ) (ewIter_infl hinfl βψ)
              (hslack_kit_ge hmono hinfl hlow βψ βφ)
              (ewIter_monotone hmono hinfl βφ) (ewIter_infl hinfl βφ) hread P₂ P₁'
            obtain ⟨w, hwle, hwNF, hwH, hwg, Dw⟩ := hstep
            exact ⟨w, le_trans hwle (le_of_lt hcollt'), hwNF, hwH,
              le_trans hwg (hcomp' 0), Dw.mono_f hcomp'⟩

/-! ### Block 12f — rank descent (`rankToZeroTC`) + the rank-0 truth core (`sound0_TC`)

`rankToZeroAuxTC` mirrors `rankToZeroAux` verbatim (the extra `3 ≤ f 0` conjunct survives the
tower: `ewIter f α 0 ≥ f 0`).  `sound0_TC` extends `sound0` to the full rule set: the truth
leaves ARE their own witnesses, `verumR` gives `⊤`, and `andI`/`orI` combine premise truths
through the connective evaluation. -/

/-- **`rankToZeroAuxTC`** — iterate `passAuxTC` down the cut rank `d → 0`. -/
theorem rankToZeroAuxTC (e : ONote) (heNF : e.NF) :
    ∀ (d : ℕ) {α : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {Γ : Seq},
      Zef2TC α e H f d Γ → Monotone f → (∀ x, x ≤ f x) → (∀ m, 2 * m + 1 ≤ f m) →
      3 ≤ f 0 → α.NF → Cl H α →
      Zef2TCProv (collapseIter d α) e H (ewIterTower f d α) 0 Γ := by
  intro d
  induction d with
  | zero =>
      intro α H f Γ D hmono hinfl hlow hbase3 hαNF hαH
      exact Zef2TCProv.of hαNF hαH (Zef2TC.gate D) D
  | succ d ih =>
      intro α H f Γ D hmono hinfl hlow hbase3 hαNF hαH
      obtain ⟨β, hβle, hβNF, hβH, hβgate, Dβ⟩ :=
        passAuxTC d heNF D rfl hmono hinfl hlow hbase3 hαNF hαH
      have hg := Nlog_collapse_le hlow (Zef2TC.gate D)
      have Dcol : Zef2TC (collapse α) e H (ewIter f α) d Γ := by
        rcases lt_or_eq_of_le (ONote.le_def.mp hβle) with hlt | heq
        · exact Zef2TC.weak hg (ONote.lt_def.mpr hlt) hβNF (collapse_NF hαNF) hβH
            (Finset.Subset.refl Γ) Dβ
        · have hβeq : β = collapse α := by
            haveI := hβNF; haveI := collapse_NF hαNF
            exact ONote.repr_inj.mp heq
          exact hβeq ▸ Dβ
      have hrec := ih Dcol (ewIter_monotone hmono hinfl α) (ewIter_infl hinfl α)
        (fun m => ewIter_low hinfl hlow α m)
        (le_trans hbase3 (ewIter_base_le hinfl α))
        (collapse_NF hαNF) (Cl_of_NF (collapse_NF hαNF))
      rw [collapseIter_collapse α d, ewIterTower_collapse f α d] at hrec
      exact hrec

/-- **`rankToZero_TC`** — the rung-R analog over `Zef2TC` (EwF1/EwF2 entry point; the extra
`3 ≤ f 0` is satisfied by every real root slot, e.g. `ewRootSlot e m 0 ≥ 3`). -/
theorem rankToZero_TC {α e : ONote} {H : ONote → Prop} {d : ℕ} {Γ : Seq} (f : ℕ → ℕ)
    (heNF : e.NF) (hαNF : α.NF) (hαH : Cl H α) (hf0 : 3 ≤ f 0)
    (D : Zef2TC α e H f d Γ) (hf1 : EwF1 f) (_hf2 : EwF2 f) :
    Zef2TCProv (collapseIter d α) e H (ewIterTower f d α) 0 Γ :=
  rankToZeroAuxTC e heNF d D hf1.monotone hf1.infl hf1.2 hf0 hαNF hαH

/-- **Rank-0 `Zef2TC` soundness** — the truth core over the FULL rule set: a cut-free (rank-0)
`Zef2TC` derivation has a standard-model-true member.  Truth leaves are their own witnesses;
`andI`/`orI` combine premise truths through the connective evaluation. -/
theorem sound0_TC : ∀ {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Seq},
    Zef2TC α e H f c Γ → c = 0 → ∃ ψ ∈ Γ, atomTrue ψ := by
  intro α e H f c Γ dd
  induction dd with
  | @axL α e H f c Γ ar hαN r v hp hn =>
      intro _
      by_cases htrue : atomTrue (Semiformula.rel r v)
      · exact ⟨_, hp, htrue⟩
      · refine ⟨_, hn, ?_⟩
        simpa [atomTrue, Semiformula.eval_nrel, Semiformula.eval_rel, Function.comp_def] using htrue
  | trueRel hαN r v htrue hmem =>
      intro _
      exact ⟨_, hmem, htrue⟩
  | trueNrel hαN r v htrue hmem =>
      intro _
      exact ⟨_, hmem, htrue⟩
  | verumR hαN h =>
      intro _
      exact ⟨⊤, h, by simp [atomTrue]⟩
  | @wk α e H f c Δ Γ hαN hsub _ ih =>
      intro hc
      obtain ⟨ψ, hψ, htrue⟩ := ih hc
      exact ⟨ψ, hsub hψ, htrue⟩
  | @weak α β e H f c Δ Γ hαN hβ hβNF hαNF hβH hsub _ ih =>
      intro hc
      obtain ⟨ψ, hψ, htrue⟩ := ih hc
      exact ⟨ψ, hsub hψ, htrue⟩
  | @andI α βφ βψ e H f c Γ hαN φ ψ hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH _ _ ih₁ ih₂ =>
      intro hc
      obtain ⟨ψ₁, hψ₁, htrue₁⟩ := ih₁ hc
      obtain ⟨ψ₂, hψ₂, htrue₂⟩ := ih₂ hc
      rcases Finset.mem_insert.mp hψ₁ with rfl | hΓ₁
      · rcases Finset.mem_insert.mp hψ₂ with rfl | hΓ₂
        · refine ⟨ψ₁ ⋏ ψ₂, Finset.mem_insert_self _ _, ?_⟩
          have h12 : atomTrue ψ₁ ∧ atomTrue ψ₂ := ⟨htrue₁, htrue₂⟩
          simpa [atomTrue] using h12
        · exact ⟨ψ₂, Finset.mem_insert_of_mem hΓ₂, htrue₂⟩
      · exact ⟨ψ₁, Finset.mem_insert_of_mem hΓ₁, htrue₁⟩
  | @orI α β e H f c Γ hαN φ ψ hβ hβNF hαNF hβH _ ih =>
      intro hc
      obtain ⟨ψ', hψ', htrue'⟩ := ih hc
      rcases Finset.mem_insert.mp hψ' with rfl | hψ'2
      · refine ⟨ψ' ⋎ ψ, Finset.mem_insert_self _ _, ?_⟩
        have h1 : atomTrue ψ' ∨ atomTrue ψ := Or.inl htrue'
        simpa [atomTrue] using h1
      · rcases Finset.mem_insert.mp hψ'2 with rfl | hΓ
        · refine ⟨φ ⋎ ψ', Finset.mem_insert_self _ _, ?_⟩
          have h1 : atomTrue φ ∨ atomTrue ψ' := Or.inr htrue'
          simpa [atomTrue] using h1
        · exact ⟨ψ', Finset.mem_insert_of_mem hΓ, htrue'⟩
  | @allω α e H f c Γ hαN φ β hβ hβNF hαNF hβH _ ih =>
      intro hc
      rcases Classical.em (∃ n : ℕ, ∃ ψ ∈ Γ, atomTrue ψ) with hctx | hctx
      · obtain ⟨n, ψ, hψ, htrue⟩ := hctx
        exact ⟨ψ, Finset.mem_insert_of_mem hψ, htrue⟩
      · refine ⟨∀⁰ φ, Finset.mem_insert_self _ _, ?_⟩
        have hall : ∀ n, atomTrue (φ/[nm n]) := by
          intro n
          obtain ⟨ψ, hψ, htrue⟩ := ih n hc
          rcases Finset.mem_insert.mp hψ with rfl | hψΓ
          · exact htrue
          · exact absurd ⟨n, ψ, hψΓ, htrue⟩ hctx
        exact (atomTrue_all_iff φ).mpr hall
  | @exI α β e H f c Γ hαN φ n hβ hβNF hαNF hβH hbound _ ih =>
      intro hc
      obtain ⟨ψ, hψ, htrue⟩ := ih hc
      rcases Finset.mem_insert.mp hψ with rfl | hψΓ
      · exact ⟨∃⁰ φ, Finset.mem_insert_self _ _, (atomTrue_ex_iff φ).mpr ⟨n, htrue⟩⟩
      · exact ⟨ψ, Finset.mem_insert_of_mem hψΓ, htrue⟩
  | @cut α βφ βψ e H f c Γ hαN φ hcompl hcutRead _ _ _ _ _ _ _ _ _ _ _ =>
      intro hc; subst hc
      exact absurd hcompl (by omega)

/-! ### E-seam piece (2) prerequisites: the root-slot EwLow facts + tower inflationarity

The composition `embedding_Zef2TC_V3 → rankToZeroAuxTC → readoff_delta0_Zef2TC` runs at the root
slot `rel1 (ewRootSlot e B) K`, which is NOT `EwF1` (the `rel1` plateau below `K` breaks
`StrictMono`) — so it feeds `rankToZeroAuxTC` (the EwLow entry: `Monotone ∧ infl ∧ 2m+1 ∧ 3≤·0`),
NOT the `rankToZero_TC` `EwF1` wrapper.  `readoff_delta0_Zef2TC` then needs the OUTPUT tower slot
`ewIterTower … d α` inflationary.  These two lemmas bank exactly those prerequisites. -/

/-- `3 ≤ (rel1 (ewRootSlot e B) K) 0` — the root slot pays `rankToZeroAuxTC`'s `3 ≤ f 0` gate
(`ewRootSlot _ _ x = 2·(…) + 3 ≥ 3`). -/
theorem three_le_rel1_rootSlot (e : ONote) (B K : ℕ) :
    3 ≤ (rel1 (ewRootSlot e B) K) 0 := by
  simp only [rel1, ewRootSlot]; omega

/-- **`ewIterTower_infl`** — the `d`-fold slot tower inherits inflationarity from its base slot
(each pass is `ewIter`, inflationary by `ewIter_infl`).  Feeds `readoff_delta0_Zef2TC`'s `hinfl`. -/
theorem ewIterTower_infl {f : ℕ → ℕ} (hinfl : ∀ m, m ≤ f m) (α : ONote) :
    ∀ (d : ℕ) (m : ℕ), m ≤ ewIterTower f d α m
  | 0, m => hinfl m
  | (d + 1), m => ewIter_infl (ewIterTower_infl hinfl α d) (collapseIter d α) m

/-! ### E-seam piece (1): the BOUNDED rank-0 `Zef2TC` read-off

`sound0_TC` gives the UNBOUNDED true member of a rank-0 sequent; the read-off needs the WITNESS
BOUND `n ≤ ewIter f α 0`.  Following **E–W's Witnessing Lemma 31** (diagnosis in
`wip/ReadoffDAuxRetired.lean`): extract the top `∃⁰ φ` witness via `exI` at slot `f` (`n ≤ f 0`,
`exI`/`weak`/`wk` all keep `f`) and verify the Δ₀ matrix instance SEMANTICALLY via `sound0_TC`,
WITHOUT structurally recursing into `allω`-decomposed matrix branches.  The invariant threaded is
`(∃⁰ φ) ∈ Γ ∧ (every OTHER member of Γ is standard-false)` — maintained by every rule at the
CONSTANT bound `f 0` (base rules are vacuous under the invariant; `weak`/`wk`/`exI`/`andI`/`orI`
recurse at the same slot; the `cut` rank is 0).  The SOLE residual is the `allω` non-monotone-matrix
trap — `∀⁰ χ` is standard-false yet its `0`-instance `χ/[nm 0]` is TRUE, so `rel1 f 0 = f`'s
sharp branch-0 recursion is unavailable and the semantic false-branch index overflows the budget.
That residual is EXACTLY the fragment `readoffD_trapped_of_mono` (`OperatorZef2.lean`) closes under
the goodstein downward-closed guard (`atomTrue (χ/[nm 0]) → atomTrue (∀⁰ χ)`), so it is a disclosed
`sorry` pending the guard-carrying statement the judge ratifies for rung D/E. -/

/-- Root weakening `f 0 ≤ ewIter f α 0` (needs only inflationarity). -/
theorem f0_le_ewIter {f : ℕ → ℕ} (hinfl : ∀ m, m ≤ f m) (α : ONote) : f 0 ≤ ewIter f α 0 := by
  by_cases hα : α = 0
  · subst hα; simp
  · have h0α : (0 : ONote) < α := by
      cases α with
      | zero => exact (hα rfl).elim
      | oadd e n a => exact oadd_pos e n a
    have hlow := ewIter_lower (f := f) (β := 0) (α := α) (m := 0) NF.zero h0α (Nat.zero_le _)
    have hff : f (f 0) ≤ ewIter f α 0 := by simpa [ewIter_zero] using hlow
    exact le_trans (hinfl (f 0)) hff

/- **`readoffTC_core` / `readoff_delta0_Zef2TC` (TC bounded rank-0 read-off) — RETIRED
(SERIES-5 Lane C).**  The invariant-form TC read-off and its singleton wrapper carried the single
`allω` non-monotone-matrix `sorry`; both are superseded by the V-threaded VALUE-BUDGET read-off
below (`readoffVTC_core` / `readoff_value_pipeline` / `readoff_value_goodstein'`), which carries the
clean route-B chain. Neither had a code consumer outside this dead pair. `f0_le_ewIter` is retained. -/

/-! ### Route-(c): the V-threaded VALUE-BUDGET read-off (DIRECTION lap-206 step (3))

The `allω`-trap dissolves against the master bound `BND V α := ewIter S α (S V)`,
`S x := max (f₀ x) (P x)`: the invariant requires every member `Gated P V` (the hereditary
semantic value gate, `wip/ReadoffValueGate.lean`), so a false `∀⁰ χ` member always admits a
false branch `k₀ ≤ P V`, and the T3 descent inequality absorbs the budget bump `V ↦ max V k₀`.
`Gated`/accessors/`Gated_mono` and the T-gadgets are COPIED from `wip/ReadoffValueGate.lean` /
`wip/ReadoffValueGadgetProbe.lean` (wip files are not importable); the ROOT discharge
`gated_of_sigma1` (`Hierarchy 𝚺 1` + guard-value bound ⟹ `Gated`) lives in the former. -/

-- SERIES-5 Lane A dedup: `Gated` and its accessors are now the single canonical copy in
-- `ReadoffValueGate`; E1's former duplicate is deleted so `wainer_bound_witness`'s `Hcert`
-- unifies with `gated_certificate_uniform` (both over `ReadoffValueGate.Gated`).
open GoodsteinPA.ReadoffValueGate (Gated Gated_and_iff Gated_or_iff Gated_all_iff Gated_exs_iff
  Gated_mono)

/-- The combined value-budget step `S x := max (f₀ x) (P x)`. -/
def Sslot (f₀ P : ℕ → ℕ) : ℕ → ℕ := fun x => max (f₀ x) (P x)

theorem Sslot_mono {f₀ P : ℕ → ℕ} (hf : Monotone f₀) (hP : Monotone P) :
    Monotone (Sslot f₀ P) := fun _ _ h => max_le_max (hf h) (hP h)

theorem Sslot_infl {f₀ P : ℕ → ℕ} (hf_infl : ∀ m, m ≤ f₀ m) :
    ∀ m, m ≤ Sslot f₀ P m := fun m => le_trans (hf_infl m) (le_max_left _ _)

/-- One-step absorption at a nonzero ordinal (copy of the probe's `SS_le_ewIter`). -/
theorem SS_le_ewIter' {S : ℕ → ℕ} {β : ONote} (hβ : β ≠ 0) (x : ℕ) :
    S (S x) ≤ ewIter S β x := by
  have h0β : (0 : ONote) < β := by
    cases β with
    | zero => exact (hβ rfl).elim
    | oadd e n a => exact oadd_pos e n a
  have h := ewIter_lower (f := S) (β := 0) (α := β) (m := x) NF.zero h0β (Nat.zero_le _)
  simpa [ewIter_zero] using h

/-- **T3 — the decisive descent inequality** (copy of the probe's `T3_descent`): a premise at
`β < α` with any bumped budget `V' ≤ S V` has its master bound absorbed by the node's. -/
theorem T3_descent' {S : ℕ → ℕ} (hS_mono : Monotone S) (hS_infl : ∀ m, m ≤ S m)
    {β α : ONote} (hβNF : β.NF) (hβα : β < α)
    {V V' : ℕ} (hV' : V' ≤ S V)
    (hgate : Nlog β ≤ S (S V)) :
    ewIter S β (S V') ≤ ewIter S α (S V) := by
  have ha : ewIter S β (S V') ≤ ewIter S β (S (S V)) :=
    ewIter_monotone hS_mono hS_infl β (hS_mono hV')
  have hb : S (S V) ≤ ewIter S β (S V) := by
    by_cases hβ0 : β = 0
    · subst hβ0
      simp [ewIter_zero]
    · exact le_trans (hS_infl (S (S V))) (SS_le_ewIter' hβ0 (S V))
  have hc : ewIter S β (S (S V)) ≤ ewIter S β (ewIter S β (S V)) :=
    ewIter_monotone hS_mono hS_infl β hb
  have hd : ewIter S β (ewIter S β (S V)) ≤ ewIter S α (S V) :=
    ewIter_lower hβNF hβα (le_trans hgate (hS_mono (by omega)))
  exact le_trans ha (le_trans hc hd)

/-- **`readoffVTC_core`** — the V-threaded value-budget read-off (route (c)).  Invariant: the
tracked `∃⁰ φ` is a member, every member is `Gated P V`, every non-tracked member is
standard-false; slot frame `g = rel1 f₀ j`, `j ≤ V`.  Conclusion bound: the master
`BND V α = ewIter S α (S V)`, `S = Sslot f₀ P`.  SORRY-FREE: the `allω` trap descends into the
`Gated` false branch `k₀ ≤ P V`; `T3_descent'` absorbs every budget bump. -/
theorem readoffVTC_core {φ : SyntacticSemiformula ℒₒᵣ 1} {f₀ P : ℕ → ℕ}
    (hf_mono : Monotone f₀) (hf_infl : ∀ m, m ≤ f₀ m) (hP_mono : Monotone P) :
    ∀ {α e : ONote} {H : ONote → Prop} {g : ℕ → ℕ} {c : ℕ} {Γ : Seq},
      Zef2TC α e H g c Γ → c = 0 →
      ∀ (V j : ℕ), g = rel1 f₀ j → j ≤ V →
      (∃⁰ φ) ∈ Γ →
      (∀ ψ ∈ Γ, Gated P V ψ ∧ (ψ = (∃⁰ φ) ∨ ¬ atomTrue ψ)) →
      ∃ n, n ≤ ewIter (Sslot f₀ P) α (Sslot f₀ P V) ∧ atomTrue (φ/[nm n]) := by
  have hS_mono : Monotone (Sslot f₀ P) := Sslot_mono hf_mono hP_mono
  have hS_infl : ∀ m, m ≤ Sslot f₀ P m := Sslot_infl hf_infl
  intro α e H g c Γ dd
  induction dd with
  | @axL α e H g c Γ ar hαN r v hp hn =>
      intro _ _ _ _ _ _ hinv
      have h1 : ¬ atomTrue (Semiformula.rel r v) :=
        (hinv _ hp).2.resolve_left (Semiformula.ne_of_ne_complexity (by simp))
      have h2 : ¬ atomTrue (Semiformula.nrel r v) :=
        (hinv _ hn).2.resolve_left (Semiformula.ne_of_ne_complexity (by simp))
      exact absurd ((atomTrue_nrel_iff_not_rel r v).mpr h1) h2
  | trueRel hαN r v htrue hmem =>
      intro _ _ _ _ _ _ hinv
      exact absurd htrue ((hinv _ hmem).2.resolve_left (Semiformula.ne_of_ne_complexity (by simp)))
  | trueNrel hαN r v htrue hmem =>
      intro _ _ _ _ _ _ hinv
      exact absurd htrue ((hinv _ hmem).2.resolve_left (Semiformula.ne_of_ne_complexity (by simp)))
  | verumR hαN h =>
      intro _ _ _ _ _ _ hinv
      have hf := (hinv _ h).2.resolve_left (Semiformula.ne_of_ne_complexity (by simp))
      exact absurd (show atomTrue (⊤ : Form) by simp [atomTrue]) hf
  | @wk α e H g c Δ Γ hαN hsub dpr ih =>
      intro hc V j hg hjV _ hinv
      obtain ⟨ψ, hψΔ, htψ⟩ := sound0_TC dpr hc
      have hφΔ : (∃⁰ φ) ∈ Δ := by
        rcases (hinv ψ (hsub hψΔ)).2 with rfl | hfalse
        · exact hψΔ
        · exact absurd htψ hfalse
      exact ih hc V j hg hjV hφΔ (fun ψ' hψ' => hinv ψ' (hsub hψ'))
  | @weak α β e H g c Δ Γ hαN hβ hβNF hαNF hβH hsub dpr ih =>
      intro hc V j hg hjV _ hinv
      obtain ⟨ψ, hψΔ, htψ⟩ := sound0_TC dpr hc
      have hφΔ : (∃⁰ φ) ∈ Δ := by
        rcases (hinv ψ (hsub hψΔ)).2 with rfl | hfalse
        · exact hψΔ
        · exact absurd htψ hfalse
      obtain ⟨n, hn, htn⟩ := ih hc V j hg hjV hφΔ (fun ψ' hψ' => hinv ψ' (hsub hψ'))
      refine ⟨n, le_trans hn ?_, htn⟩
      refine T3_descent' hS_mono hS_infl hβNF hβ (hS_infl V) ?_
      have hgpr : Nlog β ≤ g 0 := Zef2TC.gate dpr
      have hg0 : g 0 = f₀ j := by simp [hg, rel1]
      calc Nlog β ≤ f₀ j := hg0 ▸ hgpr
        _ ≤ Sslot f₀ P V := le_trans (hf_mono hjV) (le_max_left _ _)
        _ ≤ Sslot f₀ P (Sslot f₀ P V) := hS_infl _
  | @andI α βφ βψ e H g c Γ hαN χ₁ χ₂ hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH dφ dψ ih₁ ih₂ =>
      intro hc V j hg hjV hmem hinv
      have hφΓ : (∃⁰ φ) ∈ Γ :=
        (Finset.mem_insert.mp hmem).resolve_left
          (fun h => (by simp : (χ₁ ⋏ χ₂) ≠ (∃⁰ φ)) h.symm)
      obtain ⟨hgAnd, horAnd⟩ := hinv _ (Finset.mem_insert_self _ _)
      obtain ⟨hg1, hg2⟩ := Gated_and_iff.mp hgAnd
      have hfalse : ¬ (atomTrue χ₁ ∧ atomTrue χ₂) := by
        have hnand : ¬ atomTrue (χ₁ ⋏ χ₂) := horAnd.resolve_left (by simp)
        simpa [atomTrue] using hnand
      have hgate : Nlog βφ ≤ Sslot f₀ P (Sslot f₀ P V) ∧
          Nlog βψ ≤ Sslot f₀ P (Sslot f₀ P V) := by
        have hgφ : Nlog βφ ≤ g 0 := Zef2TC.gate dφ
        have hgψ : Nlog βψ ≤ g 0 := Zef2TC.gate dψ
        have hg0 : g 0 = f₀ j := by simp [hg, rel1]
        have hto : f₀ j ≤ Sslot f₀ P (Sslot f₀ P V) :=
          le_trans (le_trans (hf_mono hjV) (le_max_left _ _)) (hS_infl _)
        exact ⟨le_trans (hg0 ▸ hgφ) hto, le_trans (hg0 ▸ hgψ) hto⟩
      rcases not_and_or.mp hfalse with h1 | h2
      · obtain ⟨n, hn, htn⟩ := ih₁ hc V j hg hjV (Finset.mem_insert_of_mem hφΓ) (fun ψ hψ => by
          rcases Finset.mem_insert.mp hψ with rfl | hψΓ
          · exact ⟨hg1, Or.inr h1⟩
          · exact hinv ψ (Finset.mem_insert_of_mem hψΓ))
        exact ⟨n, le_trans hn
          (T3_descent' hS_mono hS_infl hβφNF hβφ (hS_infl V) hgate.1), htn⟩
      · obtain ⟨n, hn, htn⟩ := ih₂ hc V j hg hjV (Finset.mem_insert_of_mem hφΓ) (fun ψ hψ => by
          rcases Finset.mem_insert.mp hψ with rfl | hψΓ
          · exact ⟨hg2, Or.inr h2⟩
          · exact hinv ψ (Finset.mem_insert_of_mem hψΓ))
        exact ⟨n, le_trans hn
          (T3_descent' hS_mono hS_infl hβψNF hβψ (hS_infl V) hgate.2), htn⟩
  | @orI α β e H g c Γ hαN χ₁ χ₂ hβ hβNF hαNF hβH dpr ih =>
      intro hc V j hg hjV hmem hinv
      have hφΓ : (∃⁰ φ) ∈ Γ :=
        (Finset.mem_insert.mp hmem).resolve_left
          (fun h => (by simp : (χ₁ ⋎ χ₂) ≠ (∃⁰ φ)) h.symm)
      obtain ⟨hgOr, horOr⟩ := hinv _ (Finset.mem_insert_self _ _)
      obtain ⟨hg1, hg2⟩ := Gated_or_iff.mp hgOr
      have hfalse : ¬ (atomTrue χ₁ ∨ atomTrue χ₂) := by
        have hnor : ¬ atomTrue (χ₁ ⋎ χ₂) := horOr.resolve_left (by simp)
        simpa [atomTrue] using hnor
      obtain ⟨hf1, hf2⟩ := not_or.mp hfalse
      obtain ⟨n, hn, htn⟩ := ih hc V j hg hjV
        (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hφΓ)) (fun ψ hψ => by
          rcases Finset.mem_insert.mp hψ with rfl | hψ'
          · exact ⟨hg1, Or.inr hf1⟩
          · rcases Finset.mem_insert.mp hψ' with rfl | hψΓ
            · exact ⟨hg2, Or.inr hf2⟩
            · exact hinv ψ (Finset.mem_insert_of_mem hψΓ))
      refine ⟨n, le_trans hn (T3_descent' hS_mono hS_infl hβNF hβ (hS_infl V) ?_), htn⟩
      have hgpr : Nlog β ≤ g 0 := Zef2TC.gate dpr
      have hg0 : g 0 = f₀ j := by simp [hg, rel1]
      calc Nlog β ≤ f₀ j := hg0 ▸ hgpr
        _ ≤ Sslot f₀ P (Sslot f₀ P V) :=
          le_trans (le_trans (hf_mono hjV) (le_max_left _ _)) (hS_infl _)
  | @allω α e H g c Γ hαN χ β hβ hβNF hαNF hβH dpr ih =>
      intro hc V j hg hjV hmem hinv
      have hφΓ : (∃⁰ φ) ∈ Γ :=
        (Finset.mem_insert.mp hmem).resolve_left (by simp)
      obtain ⟨hgAll, horAll⟩ := hinv _ (Finset.mem_insert_self _ _)
      have hnall : ¬ atomTrue (∀⁰ χ) := horAll.resolve_left (by simp)
      rw [Gated_all_iff] at hgAll
      obtain ⟨k₀, hk₀P, hk₀f⟩ := hgAll.1 hnall
      -- descend into the GATED false branch k₀ at bumped budget max V k₀
      obtain ⟨n, hn, htn⟩ := ih k₀ hc (max V k₀) (max j k₀)
        (by rw [hg, rel1_rel1])
        (max_le_max hjV le_rfl)
        (Finset.mem_insert_of_mem hφΓ)
        (fun ψ hψ => by
          rcases Finset.mem_insert.mp hψ with rfl | hψΓ
          · exact ⟨hgAll.2 k₀, Or.inr hk₀f⟩
          · obtain ⟨hgψ, horψ⟩ := hinv ψ (Finset.mem_insert_of_mem hψΓ)
            exact ⟨Gated_mono hP_mono ψ V (max V k₀) (le_max_left _ _) hgψ, horψ⟩)
      refine ⟨n, le_trans hn (T3_descent' hS_mono hS_infl (hβNF k₀) (hβ k₀) ?_ ?_), htn⟩
      · -- V' = max V k₀ ≤ S V
        exact max_le (le_trans (hf_infl V) (le_max_left _ _))
          (le_trans hk₀P (le_max_right _ _))
      · -- gate: Nlog (β k₀) ≤ (rel1 g k₀) 0 = f₀ (max j k₀) ≤ S (S V)
        have hgpr : Nlog (β k₀) ≤ (rel1 g k₀) 0 := Zef2TC.gate (dpr k₀)
        have hg0 : (rel1 g k₀) 0 = f₀ (max j k₀) := by simp [hg, rel1]
        have harg : max j k₀ ≤ Sslot f₀ P V :=
          max_le (le_trans hjV (hS_infl V)) (le_trans hk₀P (le_max_right _ _))
        calc Nlog (β k₀) ≤ f₀ (max j k₀) := hg0 ▸ hgpr
          _ ≤ f₀ (Sslot f₀ P V) := hf_mono harg
          _ ≤ Sslot f₀ P (Sslot f₀ P V) := le_max_left _ _
  | @exI α β e H g c Γ hαN χ n hβ hβNF hαNF hβH hbound dpr ih =>
      intro hc V j hg hjV hmem hinv
      have hnfj : n ≤ f₀ j := by
        have := hbound
        rw [hg] at this
        simpa [rel1] using this
      have hnSV : n ≤ Sslot f₀ P V :=
        le_trans (le_trans hnfj (hf_mono hjV)) (le_max_left _ _)
      have hgate : Nlog β ≤ Sslot f₀ P (Sslot f₀ P V) := by
        have hgpr : Nlog β ≤ g 0 := Zef2TC.gate dpr
        have hg0 : g 0 = f₀ j := by simp [hg, rel1]
        calc Nlog β ≤ f₀ j := hg0 ▸ hgpr
          _ ≤ Sslot f₀ P (Sslot f₀ P V) :=
            le_trans (le_trans (hf_mono hjV) (le_max_left _ _)) (hS_infl _)
      have hVbump : max V n ≤ Sslot f₀ P V := max_le (hS_infl V) hnSV
      by_cases hχφ : (∃⁰ χ) = (∃⁰ φ)
      · have hχeq : χ = φ := by simpa using hχφ
        subst hχeq
        by_cases htn : atomTrue (χ/[nm n])
        · exact ⟨n, le_trans hnSV (ewIter_infl hS_infl α _), htn⟩
        · obtain ⟨hgEx, _⟩ := hinv _ hmem
          have hgInst : Gated P (max V n) (χ/[nm n]) := (Gated_exs_iff.mp hgEx) n
          have hInvP : ∀ ψ ∈ insert (χ/[nm n]) Γ,
              Gated P (max V n) ψ ∧ (ψ = (∃⁰ χ) ∨ ¬ atomTrue ψ) := by
            intro ψ hψ
            rcases Finset.mem_insert.mp hψ with rfl | hψΓ
            · exact ⟨hgInst, Or.inr htn⟩
            · obtain ⟨hgψ, horψ⟩ := hinv ψ (Finset.mem_insert_of_mem hψΓ)
              exact ⟨Gated_mono hP_mono ψ V (max V n) (le_max_left _ _) hgψ, horψ⟩
          by_cases hin : (∃⁰ χ) ∈ insert (χ/[nm n]) Γ
          · obtain ⟨n', hn', htn'⟩ := ih hc (max V n) j hg
              (le_trans hjV (le_max_left _ _)) hin hInvP
            exact ⟨n', le_trans hn'
              (T3_descent' hS_mono hS_infl hβNF hβ hVbump hgate), htn'⟩
          · obtain ⟨ψ, hψ, htψ⟩ := sound0_TC dpr hc
            rcases (hInvP ψ hψ).2 with rfl | hfψ
            · exact absurd hψ hin
            · exact absurd htψ hfψ
      · have hφΓ : (∃⁰ φ) ∈ Γ :=
          (Finset.mem_insert.mp hmem).resolve_left (fun h => hχφ h.symm)
        obtain ⟨hgEx, horEx⟩ := hinv _ (Finset.mem_insert_self _ _)
        have hexχ : ¬ atomTrue (∃⁰ χ) := horEx.resolve_left hχφ
        have hχn : ¬ atomTrue (χ/[nm n]) :=
          fun ht => hexχ ((atomTrue_ex_iff χ).mpr ⟨n, ht⟩)
        have hgInst : Gated P (max V n) (χ/[nm n]) := (Gated_exs_iff.mp hgEx) n
        obtain ⟨n', hn', htn'⟩ := ih hc (max V n) j hg
          (le_trans hjV (le_max_left _ _))
          (Finset.mem_insert_of_mem hφΓ)
          (fun ψ hψ => by
            rcases Finset.mem_insert.mp hψ with rfl | hψΓ
            · exact ⟨hgInst, Or.inr hχn⟩
            · obtain ⟨hgψ, horψ⟩ := hinv ψ (Finset.mem_insert_of_mem hψΓ)
              exact ⟨Gated_mono hP_mono ψ V (max V n) (le_max_left _ _) hgψ, horψ⟩)
        exact ⟨n', le_trans hn'
          (T3_descent' hS_mono hS_infl hβNF hβ hVbump hgate), htn'⟩
  | @cut α βφ βψ e H g c Γ hαN χ hcompl hcutRead _ _ _ _ _ _ _ _ _ _ _ =>
      intro hc _ _ _ _ _ _; subst hc
      exact absurd hcompl (by omega)

/-- **`readoff_value_Zef2TC`** — route (c) at the SINGLETON root `{∃⁰ φ}`: given the root
`Gated` certificate (discharged by `gated_of_sigma1`, `wip/ReadoffValueGate.lean`, from
`Hierarchy 𝚺 1 φ` + the guard-value bound `gvb`), the read-off closes SORRY-FREE at the master
bound `ewIter (Sslot f₀ P) α (Sslot f₀ P V)`. -/
theorem readoff_value_Zef2TC {φ : SyntacticSemiformula ℒₒᵣ 1} {f₀ P : ℕ → ℕ}
    (hf_mono : Monotone f₀) (hf_infl : ∀ m, m ≤ f₀ m) (hP_mono : Monotone P)
    {α e : ONote} {H : ONote → Prop}
    (dd : Zef2TC α e H f₀ 0 {(∃⁰ φ)}) (V : ℕ) (hroot : Gated P V (∃⁰ φ)) :
    ∃ n, n ≤ ewIter (Sslot f₀ P) α (Sslot f₀ P V) ∧ atomTrue (φ/[nm n]) :=
  readoffVTC_core hf_mono hf_infl hP_mono dd rfl V 0
    (by funext x; simp [rel1]) (Nat.zero_le V)
    (Finset.mem_singleton_self _)
    (fun ψ hψ => by
      rcases Finset.mem_singleton.mp hψ with rfl
      exact ⟨hroot, Or.inl rfl⟩)

/-- The tower slot preserves monotonicity (copy of `wip/NlogGateProbe.ewIterTower_monotone`). -/
theorem ewIterTower_monotone {f : ℕ → ℕ} (hmono : Monotone f) (hinfl : ∀ m, m ≤ f m)
    (α : ONote) : ∀ d, Monotone (ewIterTower f d α)
  | 0 => hmono
  | (d + 1) => ewIter_monotone (ewIterTower_monotone hmono hinfl α d)
      (ewIterTower_infl hinfl α d) _

/-- **Piece 2a — the STRUCTURAL PIPELINE** (bound-shape-independent): from a rank-`d` `Zef2TC`
derivation of a singleton `{∃⁰ φ}` at the embedding's root slot `rel1 (ewRootSlot e B) K`
(the `embedding_Zef2TC_V3` output shape) + the root `Gated` certificate, compose
`rankToZeroAuxTC` (the EwLow entry — the `rel1` plateau breaks `StrictMono`, so NOT the `EwF1`
wrapper) with `readoff_value_Zef2TC`: a TRUE numeral instance under the concrete
`ewIter (Sslot tower P)` bound at some NF ordinal `α' ≤ collapseIter d α`.  Step 2b converts
this bound into the ratified splice target (`∃ o, o.NF ∧ …` has total ordinal freedom). -/
theorem readoff_value_pipeline {φ : SyntacticSemiformula ℒₒᵣ 1} {P : ℕ → ℕ}
    (hP_mono : Monotone P)
    {α e : ONote} {H : ONote → Prop} {B K d : ℕ}
    (heNF : e.NF) (hαNF : α.NF) (hαH : Cl H α)
    (D : Zef2TC α e H (rel1 (ewRootSlot e B) K) d {(∃⁰ φ)})
    (V : ℕ) (hroot : Gated P V (∃⁰ φ)) :
    ∃ α', α' ≤ collapseIter d α ∧ α'.NF ∧
      ∃ n, n ≤ ewIter (Sslot (ewIterTower (rel1 (ewRootSlot e B) K) d α) P) α'
              (Sslot (ewIterTower (rel1 (ewRootSlot e B) K) d α) P V) ∧
        atomTrue (φ/[nm n]) := by
  have hf1 := ewRootSlot_f1 e B
  have hmono : Monotone (rel1 (ewRootSlot e B) K) := rel1_monotone hf1.monotone K
  have hinfl : ∀ x, x ≤ rel1 (ewRootSlot e B) K x := rel1_infl hf1.infl K
  have hlow : ∀ m, 2 * m + 1 ≤ rel1 (ewRootSlot e B) K m := rel1_low hf1.monotone hf1.2 K
  obtain ⟨α', hα'le, hα'NF, _hα'H, _hα'N, D0⟩ :=
    rankToZeroAuxTC e heNF d D hmono hinfl hlow (three_le_rel1_rootSlot e B K) hαNF hαH
  obtain ⟨n, hn, htn⟩ := readoff_value_Zef2TC
    (ewIterTower_monotone hmono hinfl α d) (ewIterTower_infl hinfl α d)
    hP_mono D0 V hroot
  exact ⟨α', hα'le, hα'NF, n, hn, htn⟩

/-- **The root shape + Σ₁ certificate input**: the pipeline instance `goodsteinBodyE/[nm m]`
IS an `∃⁰ χ` (definitionally — the two rewrites push through the `∃`), and it is
`Hierarchy 𝚺 1` (rew-invariance + `igoodsteinDef`'s own Σ₁-ness).  The `Gated` certificate
follows from Σ₁-ness by `gated_root_of_sigma1` (`wip/ReadoffValueGate.lean`) at assembly. -/
theorem goodsteinBodyE_inst_shape (m : ℕ) :
    ∃ χ : SyntacticSemiformula ℒₒᵣ 1,
      goodsteinBodyE/[nm m] = (∃⁰ χ) ∧ Arithmetic.Hierarchy 𝚺 1 (∃⁰ χ) := by
  refine ⟨_, rfl, ?_⟩
  show Arithmetic.Hierarchy 𝚺 1 (goodsteinBodyE/[nm m])
  apply Arithmetic.Hierarchy.rew
  apply Arithmetic.Hierarchy.rew
  simp [goodsteinBody]

/-- **The route-(c) rung-E chain, ASSEMBLED modulo the root `Gated` certificate**: from a PA
proof of the goodstein sentence — uniform budgets `B, d`, control `e`, node `α`, and per-`m` a
matrix `χ` (with the Σ₁ certificate input) and a slot stage `K` such that ANY `Gated`
certificate for `∃⁰ χ` yields a TRUE numeral instance under the concrete
`ewIter (Sslot tower P)` bound.  `embedding_Zef2TC_V3 → readoff_value_pipeline` composed at
`goodsteinBodyE`; the certificate is discharged from `Hierarchy 𝚺 1 (∃⁰ χ)` by
`gated_root_of_sigma1` at assembly (its `gvb` layer lives in `wip/ReadoffValueGate.lean`). -/
theorem readoff_value_goodstein
    (h : 𝗣𝗔 ⊢ ↑GoodsteinPA.goodsteinSentence) :
    ∃ B d : ℕ, ∃ e α : ONote, e.NF ∧ α.NF ∧ ∀ m : ℕ,
      ∃ (χ : SyntacticSemiformula ℒₒᵣ 1) (K : ℕ),
        goodsteinBodyE/[nm m] = (∃⁰ χ) ∧ Arithmetic.Hierarchy 𝚺 1 (∃⁰ χ) ∧
        ∀ (P : ℕ → ℕ) (V : ℕ), Monotone P → Gated P V (∃⁰ χ) →
          ∃ α', α' ≤ collapseIter d α ∧ α'.NF ∧
            ∃ n, n ≤ ewIter (Sslot (ewIterTower (rel1 (ewRootSlot e B) K) d α) P)
                    α' (Sslot (ewIterTower (rel1 (ewRootSlot e B) K) d α) P V) ∧
              atomTrue (χ/[nm n]) := by
  obtain ⟨B, d, e, α, heNF, hαNF, hall⟩ := embedding_Zef2TC_V3 h
  refine ⟨B, d, e, α, heNF, hαNF, fun m => ?_⟩
  obtain ⟨K, H, hαH, D⟩ := hall m
  obtain ⟨χ, hχeq, hchiS⟩ := goodsteinBodyE_inst_shape m
  rw [hχeq] at D
  refine ⟨χ, K, hχeq, hchiS, fun P V hP_mono hroot => ?_⟩
  exact readoff_value_pipeline hP_mono heNF hαNF hαH D V hroot

/-! ### 2b prep — m-uniformization of the pipeline bound

The read-off bound's `m`-dependence enters ONLY through (i) the slot stage `K_m` (a `rel1`
pre-max on the tower base) and (ii) the instance value bound `P_m` (a `gvb` numeral
contraction).  The two lemmas here collapse (i): `ewIter` is pointwise monotone in the SLOT
(bigger slot ⟹ bigger ball and bigger branches), hence the `rel1` pre-max commutes out of the
whole tower — `ewIterTower (rel1 f K) d α x ≤ ewIterTower f d α (max K x)` — leaving ONE fixed
tower with the `m`-dependence pushed into the argument. -/

/-- **Pointwise slot-domination of `ewIter`**: a pointwise-dominated slot yields a
pointwise-dominated iterate (the ball only grows, and each branch value is dominated by
IH + `ewIter_lower` on the dominating side). -/
theorem ewIter_mono_slot {f g : ℕ → ℕ} (hfg : ∀ x, f x ≤ g x)
    (hg_mono : Monotone g) (hg_infl : ∀ m, m ≤ g m) :
    ∀ (α : ONote) (m : ℕ), ewIter f α m ≤ ewIter g α m := by
  intro α m
  by_cases hα : α = 0
  · subst hα
    simpa [ewIter_zero] using hfg m
  · conv_lhs => rw [ewIter_unfold f α m]
    rw [ewStep]
    simp only [dif_neg hα]
    apply Finset.max'_le
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨δ, hδmem, rfl⟩
    have hδlt : (δ : ONote) < α := (Finset.mem_filter.mp δ.2).2.1
    have hδNF : (δ : ONote).NF := (mem_NlogBall.mp (Finset.mem_filter.mp δ.2).1).1
    have hδgate : Nlog (δ : ONote) ≤ f (Nlog α + m) := (Finset.mem_filter.mp δ.2).2.2
    have hδgate' : Nlog (δ : ONote) ≤ g (Nlog α + m) := le_trans hδgate (hfg _)
    have ih1 : ewIter f (δ : ONote) m ≤ ewIter g (δ : ONote) m :=
      ewIter_mono_slot hfg hg_mono hg_infl δ m
    have ih2 : ewIter f (δ : ONote) (ewIter f (δ : ONote) m)
        ≤ ewIter g (δ : ONote) (ewIter g (δ : ONote) m) :=
      le_trans (ewIter_mono_slot hfg hg_mono hg_infl δ _)
        (ewIter_monotone hg_mono hg_infl (δ : ONote) ih1)
    exact le_trans ih2 (ewIter_lower hδNF hδlt hδgate')
termination_by α _ => α
decreasing_by
  all_goals exact hδlt

/-- **The tower/`rel1` commutation** — the slot-stage pre-max `K` commutes out of the whole
`d`-fold tower into the argument: ONE fixed tower dominates all stages. -/
theorem ewIterTower_rel1_le {f : ℕ → ℕ} (hmono : Monotone f) (hinfl : ∀ m, m ≤ f m)
    (K : ℕ) (α : ONote) : ∀ (d : ℕ) (x : ℕ),
    ewIterTower (rel1 f K) d α x ≤ ewIterTower f d α (max K x)
  | 0, x => le_of_eq (by simp [ewIterTower, rel1])
  | (d + 1), x => by
      have hTmono : Monotone (ewIterTower f d α) := ewIterTower_monotone hmono hinfl α d
      have hTinfl : ∀ m, m ≤ ewIterTower f d α m := ewIterTower_infl hinfl α d
      have hpt : ∀ x', ewIterTower (rel1 f K) d α x' ≤ rel1 (ewIterTower f d α) K x' :=
        fun x' => ewIterTower_rel1_le hmono hinfl K α d x'
      calc ewIter (ewIterTower (rel1 f K) d α) (collapseIter d α) x
          ≤ ewIter (rel1 (ewIterTower f d α) K) (collapseIter d α) x :=
            ewIter_mono_slot hpt (rel1_monotone hTmono K) (rel1_infl hTinfl K)
              (collapseIter d α) x
        _ ≤ ewIter (ewIterTower f d α) (collapseIter d α) (max K x) :=
            ewIter_rel1_le hTmono hTinfl (collapseIter d α) K x

/-! ### 2b item (d) — the semantic link (igoodstein faithfulness)

A true numeral instance of the pipeline matrix at witness `n` bounds the REAL Goodstein
length: `atomTrue (χ/[nm n]) → goodsteinLength m ≤ n`.  The matrix is extracted from the
`∃⁰`-shape equality by constructor injectivity (whnf), then the Bridge-style eval recipe
(`igoodstein_defined.iff` + `igoodstein_nat`) lands on `goodsteinSeq m n = 0`. -/

theorem goodsteinBodyE_semantic_link {m n : ℕ} {χ : SyntacticSemiformula ℒₒᵣ 1}
    (hχ : goodsteinBodyE/[nm m] = (∃⁰ χ)) (h : atomTrue (χ/[nm n])) :
    GoodsteinPA.Dom.goodsteinLength m ≤ n := by
  have hbody := Semiformula.exs.inj hχ
  rw [← hbody] at h
  have h' : atomTrue ((((Rew.subst (L := ℒₒᵣ) ![nm m]).q ▹
      ((Rew.emb : Rew ℒₒᵣ Empty 1 ℕ 1).q ▹
        (((↑(LO.FirstOrder.Arithmetic.igoodsteinDef))/[(‘0’ : Semiterm ℒₒᵣ Empty 2), #1, #0])
          : Semisentence ℒₒᵣ 2))) : SyntacticSemiformula ℒₒᵣ 1)/[nm n]) := h
  apply GoodsteinPA.Dom.goodsteinLength_le (m := m) (N := n)
  rw [← GoodsteinPA.InternalPow.igoodstein_nat]
  simp only [atomTrue, Semiformula.eval_rew, Function.comp_def] at h'
  have hcast : ∀ (E : Fin 3 → ℕ) (ε₁ ε₂ : Empty → ℕ),
      GoodsteinPA.Compat.gEval (Arithmetic.standardModel ℕ) E ε₁
        (↑(LO.FirstOrder.Arithmetic.igoodsteinDef)) →
      GoodsteinPA.Compat.gEval (Arithmetic.standardModel ℕ) E ε₂
        (↑(LO.FirstOrder.Arithmetic.igoodsteinDef)) := by
    intro E ε₁ ε₂ hh
    rwa [show ε₂ = ε₁ from funext fun a => a.elim]
  have h'' := hcast _ _ Empty.elim h'
  have hkey := GoodsteinPA.InternalPow.igoodstein_defined.iff.mp h''
  have hq1 : ((Rew.subst (L := ℒₒᵣ) (ξ := ℕ) ![nm m]).q #1 : SyntacticSemiterm ℒₒᵣ 1)
      = Rew.bShift (nm m) := by
    show (Rew.subst (L := ℒₒᵣ) (ξ := ℕ) ![nm m]).q #(Fin.succ 0) = _
    rw [Rew.q_bvar_succ]
    simp
  -- `hkey` (post-`simp`) carries a bare `Semiterm.val`; state `hval` in the same form (the ℕ-model's
  -- `Structure ℒₒᵣ ℕ` instance IS `standardModel ℕ`) so the `rw` matches, not via the `gVal` shim.
  have hval : Semiterm.val (L := ℒₒᵣ) (ξ := ℕ) (fun _ => n) (fun _ => 0)
      ((Rew.subst (L := ℒₒᵣ) (ξ := ℕ) ![nm m]).q #1) = m := by
    rw [hq1]
    simp [Semiterm.val_bShift', Matrix.empty_eq, valm_nm]
  simp at hkey
  rw [hval] at hkey
  simpa using hkey.symm

/-! ### Lap 210 (SERIES-4 S-3) — the Nlog-PRIMED pipeline

`Zef2TCProv` carries `Nlog α' ≤ f 0`; `readoff_value_pipeline` discarded it, but the α'-uniform
Hardy conversion (`ewIter_dom_pad_levelcap`, `wip/HardyMajorization.lean`) needs it — `Nlog α'`
appears in the converted bound's ARGUMENT and must itself be bounded (it is: by the tower slot
at `0`, which the `S°`-uniformization makes Hardy-in-`m`).  Same proofs, keeping the conjunct. -/

/-- `readoff_value_pipeline` + the `Nlog α'` certificate. -/
theorem readoff_value_pipeline' {φ : SyntacticSemiformula ℒₒᵣ 1} {P : ℕ → ℕ}
    (hP_mono : Monotone P)
    {α e : ONote} {H : ONote → Prop} {B K d : ℕ}
    (heNF : e.NF) (hαNF : α.NF) (hαH : Cl H α)
    (D : Zef2TC α e H (rel1 (ewRootSlot e B) K) d {(∃⁰ φ)})
    (V : ℕ) (hroot : Gated P V (∃⁰ φ)) :
    ∃ α', α' ≤ collapseIter d α ∧ α'.NF ∧
      Nlog α' ≤ ewIterTower (rel1 (ewRootSlot e B) K) d α 0 ∧
      ∃ n, n ≤ ewIter (Sslot (ewIterTower (rel1 (ewRootSlot e B) K) d α) P) α'
              (Sslot (ewIterTower (rel1 (ewRootSlot e B) K) d α) P V) ∧
        atomTrue (φ/[nm n]) := by
  have hf1 := ewRootSlot_f1 e B
  have hmono : Monotone (rel1 (ewRootSlot e B) K) := rel1_monotone hf1.monotone K
  have hinfl : ∀ x, x ≤ rel1 (ewRootSlot e B) K x := rel1_infl hf1.infl K
  have hlow : ∀ m, 2 * m + 1 ≤ rel1 (ewRootSlot e B) K m := rel1_low hf1.monotone hf1.2 K
  obtain ⟨α', hα'le, hα'NF, _hα'H, hα'N, D0⟩ :=
    rankToZeroAuxTC e heNF d D hmono hinfl hlow (three_le_rel1_rootSlot e B K) hαNF hαH
  obtain ⟨n, hn, htn⟩ := readoff_value_Zef2TC
    (ewIterTower_monotone hmono hinfl α d) (ewIterTower_infl hinfl α d)
    hP_mono D0 V hroot
  exact ⟨α', hα'le, hα'NF, hα'N, n, hn, htn⟩

/-- The per-`m` stage `K_m` of `embedding_Zef2TC_V3` is `max K₀ m` for a UNIFORM `K₀` — the
m-uniformization's linear-stage certificate, extracted by re-running the embedding's own proof
(the stage is `max (envSup (fun _ => 0) N) m`). -/
theorem embedding_Zef2TC_V3_linearK :
    (𝗣𝗔 ⊢ ↑GoodsteinPA.goodsteinSentence) →
      ∃ B d K₀ : ℕ, ∃ e α : ONote, e.NF ∧ α.NF ∧ ∀ m : ℕ,
        ∃ H : ONote → Prop, Cl H α ∧
          Zef2TC α e H (rel1 (ewRootSlot e B) (max K₀ m)) d {(goodsteinBodyE/[nm m])} := by
  intro h
  -- upstream `𝗣𝗔 ⊢ σ` repackages as a `Derivation2 𝗣𝗔 {↑σ}` via `provable_iff_derivable2`
  have hV3 : BudgetedEmbedsV3 {(↑GoodsteinPA.goodsteinSentence : SyntacticFormula ℒₒᵣ)} := by
    obtain ⟨d2⟩ := (provable_iff_derivable2 (L := ℒₒᵣ)).mp h
    exact budgetedEmbeddingV3 d2
  obtain ⟨B, d, N, e, α, he, hαNF, hNlogB, hD⟩ := hV3
  refine ⟨B, d, envSup (fun _ => 0) N, e, α, he, hαNF, fun m => ?_⟩
  have hD0 := hD (fun _ => 0)
  have himg : ({(↑GoodsteinPA.goodsteinSentence : SyntacticFormula ℒₒᵣ)} :
        Finset (SyntacticFormula ℒₒᵣ)).image
        (fun φ => Embedding.asg (fun _ => 0) ▹ φ)
      = {(↑GoodsteinPA.goodsteinSentence : SyntacticFormula ℒₒᵣ)} := by
    rw [Finset.image_singleton, asg_emb_fix]
  rw [himg, coe_goodsteinSentence_eq] at hD0
  have hf1 := ewRootSlot_f1 e B
  have hmono : Monotone (rel1 (ewRootSlot e B) (envSup (fun _ => 0) N)) :=
    rel1_monotone hf1.1.monotone _
  have hinv := allω_inversion (φ := goodsteinBodyE) m hD0 hmono
  rw [rel1_rel1] at hinv
  refine ⟨fun _ => True, Cl_of_NF hαNF, ?_⟩
  have hctx : insert (goodsteinBodyE/[nm m])
        (({(∀⁰ goodsteinBodyE : SyntacticFormula ℒₒᵣ)} :
          Finset (SyntacticFormula ℒₒᵣ)).erase (∀⁰ goodsteinBodyE))
      = {(goodsteinBodyE/[nm m])} := by
    rw [Finset.erase_singleton]
    rfl
  rw [hctx] at hinv
  exact hinv.change_H

/-- `readoff_value_goodstein` + the `Nlog α'` certificate + the LINEAR stage `max K₀ m` —
the m-uniformization-ready read-off. -/
theorem readoff_value_goodstein'
    (h : 𝗣𝗔 ⊢ ↑GoodsteinPA.goodsteinSentence) :
    ∃ B d K₀ : ℕ, ∃ e α : ONote, e.NF ∧ α.NF ∧ ∀ m : ℕ,
      ∃ χ : SyntacticSemiformula ℒₒᵣ 1,
        goodsteinBodyE/[nm m] = (∃⁰ χ) ∧ Arithmetic.Hierarchy 𝚺 1 (∃⁰ χ) ∧
        ∀ (P : ℕ → ℕ) (V : ℕ), Monotone P → Gated P V (∃⁰ χ) →
          ∃ α', α' ≤ collapseIter d α ∧ α'.NF ∧
            Nlog α' ≤ ewIterTower (rel1 (ewRootSlot e B) (max K₀ m)) d α 0 ∧
            ∃ n, n ≤ ewIter (Sslot (ewIterTower (rel1 (ewRootSlot e B) (max K₀ m)) d α) P)
                    α' (Sslot (ewIterTower (rel1 (ewRootSlot e B) (max K₀ m)) d α) P V) ∧
              atomTrue (χ/[nm n]) := by
  obtain ⟨B, d, K₀, e, α, heNF, hαNF, hall⟩ := embedding_Zef2TC_V3_linearK h
  refine ⟨B, d, K₀, e, α, heNF, hαNF, fun m => ?_⟩
  obtain ⟨H, hαH, D⟩ := hall m
  obtain ⟨χ, hχeq, hchiS⟩ := goodsteinBodyE_inst_shape m
  rw [hχeq] at D
  refine ⟨χ, hχeq, hchiS, fun P V hP_mono hroot => ?_⟩
  exact readoff_value_pipeline' hP_mono heNF hαNF hαH D V hroot

/-! ### Lap 210 (SERIES-4 S-5) — the EventuallyLE package at the axiom's VERBATIM type

Hypothesis-passing across the sibling wip modules (they cannot import each other; each
hypothesis is the VERBATIM statement of a theorem proven kernel-clean in its module):
- `Hcert` = `GoodsteinPA.ReadoffValueGate.gated_certificate_uniform` (`Gated` is this file's
  duplicate of the same definition),
- `HSdom` = `GoodsteinPA.HardyMajorization.Scirc_dom_pad`,
- `Hconv` = `GoodsteinPA.HardyMajorization.master_conversion`.
The read-off (`readoff_value_goodstein'`), the m-uniformization, and the semantic link are
discharged HERE.  The conclusion is the exact type of the sole route axiom
`WainerRoute.wainer_bound_of_pa_proves_goodstein` (`src/GoodsteinPA/WainerRoute.lean:119`). -/
theorem wainer_bound_witness
    (Hcert : ∀ {G : ℕ → ℕ}, Monotone G → (∀ x, x + 1 ≤ G x) →
      (∀ a b, a + b ≤ G (max a b)) → (∀ a b, a * b ≤ G (max a b)) →
      ∀ (body : SyntacticSemiformula ℒₒᵣ 2), ∃ k : ℕ, ∀ (m V : ℕ)
        (χ : SyntacticSemiformula ℒₒᵣ 1),
        χ = (Rew.subst (L := ℒₒᵣ) (ξ := ℕ) ![nm m]).q ▹ body →
        Arithmetic.Hierarchy 𝚺 1 (∃⁰ χ) →
        ∃ P : ℕ → ℕ, Monotone P ∧ Gated P V (∃⁰ χ) ∧
          ∀ z, P z ≤ G^[k] (max (max V m) z))
    (HSdom : ∀ (e : ONote), e.NF → ∀ (Bb d k : ℕ) (α : ONote), α.NF →
      ∃ (E : ONote) (c : ℕ), E.NF ∧ E ≠ 0 ∧
        ∀ z, max (ewIterTower (ewRootSlot e Bb) d α z)
            ((hardy (oadd (ofNat 2) 1 0))^[k] z)
          ≤ hardy (oadd E 1 0) (z + c))
    (Hconv : ∀ {S : ℕ → ℕ} {E_S γ : ONote} {c_S : ℕ}, E_S.NF → E_S ≠ 0 → γ.NF →
      (∀ z, S z ≤ hardy (oadd E_S 1 0) (z + c_S)) → (∀ z, z ≤ S z) → ∀ K₀ : ℕ,
      ∃ o : ONote, o.NF ∧ ∃ N : ℕ, ∀ m, N ≤ m →
        ∀ α' : ONote, α'.NF → α' ≤ γ → ∀ n : ℕ,
          Nlog α' ≤ S (max K₀ m) →
          n ≤ ewIter S α' (S (max K₀ m)) →
          n ≤ fastGrowing o m)
    (h : 𝗣𝗔 ⊢ ↑GoodsteinPA.goodsteinSentence) :
    ∃ o : ONote, o.NF ∧
      GoodsteinPA.WainerRoute.EventuallyLE GoodsteinPA.Dom.goodsteinLength
        (fun n => fastGrowing o n) := by
  obtain ⟨B, d, K₀, e, α, heNF, hαNF, hall⟩ := readoff_value_goodstein' h
  -- ONE iterate count k for the whole numeral family, at the FIXED matrix B₀
  obtain ⟨k, hk⟩ := Hcert (G := Gexp) Gexp_monotone succ_le_Gexp add_le_Gexp_max
    mul_le_Gexp_max
    ((Rew.emb : Rew ℒₒᵣ Empty 1 ℕ 1).q ▹
      ((((↑(LO.FirstOrder.Arithmetic.igoodsteinDef))/[(‘0’ : Semiterm ℒₒᵣ Empty 2), #1, #0])
        : Semisentence ℒₒᵣ 2)))
  -- the fixed slot S° and its domination
  obtain ⟨E_S, c_S, hES, hES0, hSdom⟩ := HSdom e heNF B d k α hαNF
  have hf1 := ewRootSlot_f1 e B
  have hTmono : Monotone (ewIterTower (ewRootSlot e B) d α) :=
    ewIterTower_monotone hf1.monotone hf1.infl α d
  have hSmono : Monotone (fun x => max (ewIterTower (ewRootSlot e B) d α x)
      ((hardy (oadd (ofNat 2) 1 0))^[k] x)) :=
    fun a b hab => max_le_max (hTmono hab) ((Gexp_iter_monotone k) hab)
  have hSinfl : ∀ x, x ≤ max (ewIterTower (ewRootSlot e B) d α x)
      ((hardy (oadd (ofNat 2) 1 0))^[k] x) :=
    fun x => le_trans (le_Gexp_iter k x) (le_max_right _ _)
  have hγNF : (collapseIter d α).NF := collapseIter_NF hαNF d
  obtain ⟨o, hoNF, N, hN⟩ := Hconv hES hES0 hγNF hSdom hSinfl K₀
  refine ⟨o, hoNF, N, fun m hm => ?_⟩
  obtain ⟨χ, hχeq, hSig, hmain⟩ := hall m
  have hχB : χ = (Rew.subst (L := ℒₒᵣ) (ξ := ℕ) ![nm m]).q ▹
      ((Rew.emb : Rew ℒₒᵣ Empty 1 ℕ 1).q ▹
        ((((↑(LO.FirstOrder.Arithmetic.igoodsteinDef))/[(‘0’ : Semiterm ℒₒᵣ Empty 2), #1, #0])
          : Semisentence ℒₒᵣ 2))) :=
    (Semiformula.exs.inj hχeq).symm
  obtain ⟨P, hPmono, hPgated, hPle⟩ := hk m 0 χ hχB hSig
  obtain ⟨α', hle, hα'NF, hNcert, n, hn, htrue⟩ := hmain P 0 hPmono hPgated
  have hglen : GoodsteinPA.Dom.goodsteinLength m ≤ n :=
    goodsteinBodyE_semantic_link hχeq htrue
  -- m-uniformization: fold the rel1-staged tower and the per-m P into the fixed slot
  have hT_m : ∀ x, ewIterTower (rel1 (ewRootSlot e B) (max K₀ m)) d α x
      ≤ ewIterTower (ewRootSlot e B) d α (max (max K₀ m) x) :=
    ewIterTower_rel1_le hf1.monotone hf1.infl (max K₀ m) α d
  have hP' : ∀ x, P x ≤ (hardy (oadd (ofNat 2) 1 0))^[k] (max (max K₀ m) x) := by
    intro x
    refine le_trans (hPle x) ((Gexp_iter_monotone k) (by omega))
  have hSl : ∀ x, Sslot (ewIterTower (rel1 (ewRootSlot e B) (max K₀ m)) d α) P x
      ≤ rel1 (fun x => max (ewIterTower (ewRootSlot e B) d α x)
          ((hardy (oadd (ofNat 2) 1 0))^[k] x)) (max K₀ m) x :=
    fun x => max_le_max (hT_m x) (hP' x)
  have hrmono := rel1_monotone hSmono (max K₀ m)
  have hrinfl := rel1_infl hSinfl (max K₀ m)
  have hy : Sslot (ewIterTower (rel1 (ewRootSlot e B) (max K₀ m)) d α) P 0
      ≤ max (ewIterTower (ewRootSlot e B) d α (max K₀ m))
          ((hardy (oadd (ofNat 2) 1 0))^[k] (max K₀ m)) := by
    have := hSl 0
    rwa [show rel1 (fun x => max (ewIterTower (ewRootSlot e B) d α x)
        ((hardy (oadd (ofNat 2) 1 0))^[k] x)) (max K₀ m) 0
      = max (ewIterTower (ewRootSlot e B) d α (max K₀ m))
          ((hardy (oadd (ofNat 2) 1 0))^[k] (max K₀ m)) by
        show (fun x => max _ _) (max (max K₀ m) 0) = _
        rw [Nat.max_zero]] at this
  have h5 := ewIter_mono_slot hSl hrmono hrinfl α'
    (Sslot (ewIterTower (rel1 (ewRootSlot e B) (max K₀ m)) d α) P 0)
  have h6 := ewIter_monotone hrmono hrinfl α' hy
  have h7 := ewIter_rel1_le hSmono hSinfl α' (max K₀ m)
    (max (ewIterTower (ewRootSlot e B) d α (max K₀ m))
      ((hardy (oadd (ofNat 2) 1 0))^[k] (max K₀ m)))
  have h8 : max (max K₀ m) (max (ewIterTower (ewRootSlot e B) d α (max K₀ m))
      ((hardy (oadd (ofNat 2) 1 0))^[k] (max K₀ m)))
      = max (ewIterTower (ewRootSlot e B) d α (max K₀ m))
          ((hardy (oadd (ofNat 2) 1 0))^[k] (max K₀ m)) :=
    max_eq_right (hSinfl (max K₀ m))
  rw [h8] at h7
  have hNcert' : Nlog α' ≤ max (ewIterTower (ewRootSlot e B) d α (max K₀ m))
      ((hardy (oadd (ofNat 2) 1 0))^[k] (max K₀ m)) := by
    refine le_trans hNcert (le_trans ?_ (le_max_left _ _))
    have := hT_m 0
    rwa [Nat.max_zero] at this
  have hfinal : n ≤ ewIter (fun x => max (ewIterTower (ewRootSlot e B) d α x)
      ((hardy (oadd (ofNat 2) 1 0))^[k] x)) α'
      ((fun x => max (ewIterTower (ewRootSlot e B) d α x)
        ((hardy (oadd (ofNat 2) 1 0))^[k] x)) (max K₀ m)) :=
    le_trans hn (le_trans h5 (le_trans h6 h7))
  exact le_trans hglen (hN m hm α' hα'NF hle n hNcert' hfinal)

end GoodsteinPA.E1EmbeddingGrind

#print axioms GoodsteinPA.E1EmbeddingGrind.wainer_bound_witness
#print axioms GoodsteinPA.E1EmbeddingGrind.readoff_value_pipeline'
#print axioms GoodsteinPA.E1EmbeddingGrind.readoff_value_goodstein'
#print axioms GoodsteinPA.E1EmbeddingGrind.embedding_Zef2TC_V3_linearK
#print axioms GoodsteinPA.E1EmbeddingGrind.goodsteinBodyE_semantic_link
#print axioms GoodsteinPA.E1EmbeddingGrind.ewIter_mono_slot
#print axioms GoodsteinPA.E1EmbeddingGrind.ewIterTower_rel1_le
#print axioms GoodsteinPA.E1EmbeddingGrind.goodsteinBodyE_inst_shape
#print axioms GoodsteinPA.E1EmbeddingGrind.readoff_value_goodstein
#print axioms GoodsteinPA.E1EmbeddingGrind.readoff_value_pipeline
#print axioms GoodsteinPA.E1EmbeddingGrind.readoffVTC_core
#print axioms GoodsteinPA.E1EmbeddingGrind.readoff_value_Zef2TC

#print axioms GoodsteinPA.E1EmbeddingGrind.term_val_le_Gexp_iter
#print axioms GoodsteinPA.E1EmbeddingGrind.stdClosedVal_asg_le_Gexp_iter
#print axioms GoodsteinPA.E1EmbeddingGrind.budgetedEmbedsV3_closed
#print axioms GoodsteinPA.E1EmbeddingGrind.budgetedEmbedsV3_or
#print axioms GoodsteinPA.E1EmbeddingGrind.budgetedEmbedsV3_shift
#print axioms GoodsteinPA.E1EmbeddingGrind.budgetedEmbedsV3_all
#print axioms GoodsteinPA.E1EmbeddingGrind.budgetedEmbedsV3_and
#print axioms GoodsteinPA.E1EmbeddingGrind.budgetedEmbedsV3_cut
#print axioms GoodsteinPA.E1EmbeddingGrind.budgetedEmbedsV3_exs
#print axioms GoodsteinPA.E1EmbeddingGrind.truth_exFree_Zef2TC
#print axioms GoodsteinPA.E1EmbeddingGrind.budgetedEmbedsV3_addEqOfLt
#print axioms GoodsteinPA.E1EmbeddingGrind.budgetedEmbedsV3_axm_PAminus
#print axioms GoodsteinPA.E1EmbeddingGrind.allClosure_peel
#print axioms GoodsteinPA.E1EmbeddingGrind.clog_tower_gate
#print axioms GoodsteinPA.E1EmbeddingGrind.rew_succInd'
#print axioms GoodsteinPA.E1EmbeddingGrind.metaInduction_Zef2TC
#print axioms GoodsteinPA.E1EmbeddingGrind.succInd_shape_Zef2TC
#print axioms GoodsteinPA.E1EmbeddingGrind.budgetedEmbedsV3_succInd
#print axioms GoodsteinPA.E1EmbeddingGrind.budgetedEmbedsV3_axm
#print axioms GoodsteinPA.E1EmbeddingGrind.budgetedEmbeddingV3
#print axioms GoodsteinPA.E1EmbeddingGrind.allω_inversion
#print axioms GoodsteinPA.E1EmbeddingGrind.embedding_Zef2TC_V3
#print axioms GoodsteinPA.E1EmbeddingGrind.and_inversion_left
#print axioms GoodsteinPA.E1EmbeddingGrind.and_inversion_right
#print axioms GoodsteinPA.E1EmbeddingGrind.or_inversion
#print axioms GoodsteinPA.E1EmbeddingGrind.stepAnd_Zef2TC
#print axioms GoodsteinPA.E1EmbeddingGrind.stepVerum_Zef2TC
#print axioms GoodsteinPA.E1EmbeddingGrind.false_nrel_erase
#print axioms GoodsteinPA.E1EmbeddingGrind.false_rel_erase
#print axioms GoodsteinPA.E1EmbeddingGrind.stepAtom_Zef2TC
#print axioms GoodsteinPA.E1EmbeddingGrind.cutReduceAllAuxRunning_TC
#print axioms GoodsteinPA.E1EmbeddingGrind.stepAllωTC_bnd
#print axioms GoodsteinPA.E1EmbeddingGrind.osucc_lt_collapse
#print axioms GoodsteinPA.E1EmbeddingGrind.passAuxTC
#print axioms GoodsteinPA.E1EmbeddingGrind.rankToZero_TC
#print axioms GoodsteinPA.E1EmbeddingGrind.sound0_TC
#print axioms GoodsteinPA.E1EmbeddingGrind.falsum_erase
#print axioms GoodsteinPA.E1EmbeddingGrind.f0_le_ewIter
#print axioms GoodsteinPA.E1EmbeddingGrind.three_le_rel1_rootSlot
#print axioms GoodsteinPA.E1EmbeddingGrind.ewIterTower_infl
