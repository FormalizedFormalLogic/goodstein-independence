import GoodsteinPA.OperatorZef2
import GoodsteinPA.WainerRoute

/-!
# E-0 (Series-3) — the Ax2-need kernel probe + the rung-E statement DRAFT

Order item E-0 (`REBUILD-Z-SERIES-3-ORDER-2026-07-03.md`): (a) the rung-E statement DRAFT (the
W3-ratified K-hypothesis shape re-based onto the current calculus, source
`hpa : 𝗣𝗔 ⊢ ↑goodsteinSentence`, `Γ_G` bound to the concrete goodstein translation) — **text in
wip, marked DRAFT, NOT src**; (b) the **Ax2-need kernel probe**: embed one concrete
PA-axiom/true-Δ₀ leaf into `Zef2` vs `Zef2T` — does closure require the true-literal rule?

## (b) ANSWER: YES — kernel-proven, and STRONGER than the planned leaf probe

The lap-199 spine-head machinery (`zef2_rank0_uniform_spine_underivable`, src) already shows
`Zef2` rank-0 derives NO singleton whatsoever (`zef2_rank0_singleton_underivable` below — ANY
singleton is uniform-spine).  This probe adds the CONCRETE pair the order asked for, at the
current `Nlog` gates:

* `zef2T_derives_paRefl` — `Zef2T` (= `Zef2` + E–W (Ax2), cloned below at the post-swap `Nlog`
  gates) derives the PA equality-axiom-shaped leaf `{∀x (x = x)}` at rank 0, root ordinal `1`,
  slot `·+1`: one `allω` node, every branch a `trueRel` leaf on the true literal `n = n`.
* `zef2_not_derives_paRefl` — `Zef2` provably CANNOT derive it (any α, e, H, f).

So the rung-E embedding's true-Δ₀/PA-axiom leaves REQUIRE the (Ax2) rule: B(iii) confirmed at
the kernel, per-leaf AND globally.  (Ax2) adoption remains the judge's ruling; this file is
its evidence.

## (a) The rung-E statement DRAFT — see `embedding_Zef2T_DRAFT` at the bottom

Shape notes (all four W3/R-6 disciplines carried):
1. **Source** = `hpa : 𝗣𝗔 ⊢ ↑goodsteinSentence` (PA-proof-sourced pipeline; no `∀ Zeh`
   transport).
2. **Budgets EXISTENTIAL and uniform in the instance `m`**: the PA proof is one finite object;
   its embedding's cut-rank `d`, root budget `B`, and control tower `e` do not depend on `m`
   (W3's `∃ c d₀, ∀ env, …` discipline).  The per-instance ordinal `α` varies (numeral-sized
   nodes) — it stays inside the `∀ m`.
3. **Target calculus = `Zef2T`** (forced by (b); a `Zef2` target is kernel-false by
   `zef2_not_derives_goodstein_instance` below — the instance sequent is a singleton).
4. **`Γ_G` concrete**: the `m`-th instance singleton `{(goodsteinBodyE)/[nm m]}` where
   `goodsteinBodyE` is the syntactic embedding of the goodstein matrix
   `“∃ N, !igoodsteinDef 0 #0 N”` (so `∀⁰ goodsteinBodyE = ↑goodsteinSentence` — proven by
   `rfl`-grade lemma `goodsteinSentence_eq_all_body` below, keeping the binding faithful rather
   than improvised).

DRAFT ONLY — statement enters src after the rung-E ruling.  wip-only ruling input; src untouched.
-/

namespace GoodsteinPA.E0Ax2NeedProbe

open LO LO.FirstOrder ONote Ordinal
open GoodsteinPA.FastGrowing
open GoodsteinPA.OperatorZeh GoodsteinPA.OperatorZinfty

/-! ## The clone: `Zef2T` = `Zef2` + (Ax2), at the CURRENT (post-swap) `Nlog` gates -/

/-- **`Zef2T`** — `Zef2` (verbatim constructors, `Nlog` gates included) + E–W's (Ax2) as the two
true-literal leaves `trueRel`/`trueNrel`.  Post-swap re-clone of the frozen Stage-B probe
(`wip/Ax2AdequacyProbe.lean`, pre-swap `ewN` gates — left untouched as evidence). -/
inductive Zef2T : ONote → ONote → (ONote → Prop) → (ℕ → ℕ) → ℕ → Seq → Prop
  | axL {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Seq} {ar : ℕ}
      (hαN : Nlog α ≤ f 0)
      (r : (ℒₒᵣ).Rel ar) (v) (hp : Semiformula.rel r v ∈ Γ)
      (hn : Semiformula.nrel r v ∈ Γ) : Zef2T α e H f c Γ
  | trueRel {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Seq} {ar : ℕ}
      (hαN : Nlog α ≤ f 0)
      (r : (ℒₒᵣ).Rel ar) (v) (htrue : atomTrue (Semiformula.rel r v))
      (hmem : Semiformula.rel r v ∈ Γ) : Zef2T α e H f c Γ
  | trueNrel {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Seq} {ar : ℕ}
      (hαN : Nlog α ≤ f 0)
      (r : (ℒₒᵣ).Rel ar) (v) (htrue : atomTrue (Semiformula.nrel r v))
      (hmem : Semiformula.nrel r v ∈ Γ) : Zef2T α e H f c Γ
  | wk {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Δ Γ : Seq}
      (hαN : Nlog α ≤ f 0) (hsub : Δ ⊆ Γ) (dd : Zef2T α e H f c Δ) :
      Zef2T α e H f c Γ
  | weak {α β e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Δ Γ : Seq}
      (hαN : Nlog α ≤ f 0)
      (hβ : β < α) (hβNF : β.NF) (hαNF : α.NF) (hβH : Cl H β)
      (hsub : Δ ⊆ Γ) (dd : Zef2T β e H f c Δ) : Zef2T α e H f c Γ
  | allω {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Seq}
      (hαN : Nlog α ≤ f 0)
      (φ : SyntacticSemiformula ℒₒᵣ 1) (β : ℕ → ONote)
      (hβ : ∀ n, β n < α) (hβNF : ∀ n, (β n).NF) (hαNF : α.NF)
      (hβH : ∀ n, relOp H n (β n))
      (dd : ∀ n, Zef2T (β n) e (adjoin H n) (rel1 f n) c (insert (φ/[nm n]) Γ)) :
      Zef2T α e H f c (insert (∀⁰ φ) Γ)
  | exI {α β e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Seq}
      (hαN : Nlog α ≤ f 0)
      (φ : SyntacticSemiformula ℒₒᵣ 1) (n : ℕ) (hβ : β < α)
      (hβNF : β.NF) (hαNF : α.NF) (hβH : Cl H β) (hbound : n ≤ f 0)
      (dd : Zef2T β e H f c (insert (φ/[nm n]) Γ)) : Zef2T α e H f c (insert (∃⁰ φ) Γ)
  | cut {α βφ βψ e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Seq}
      (hαN : Nlog α ≤ f 0)
      (φ : Form) (hcompl : φ.complexity < c) (hcutRead : φ.complexity ≤ f 0)
      (hβφ : βφ < α) (hβψ : βψ < α)
      (hβφNF : βφ.NF) (hβψNF : βψ.NF) (hαNF : α.NF)
      (hβφH : Cl H βφ) (hβψH : Cl H βψ)
      (d₁ : Zef2T βφ e H f c (insert φ Γ)) (d₂ : Zef2T βψ e H f c (insert (∼φ) Γ)) :
      Zef2T α e H f c Γ

namespace Zef2T

theorem gate {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Seq}
    (dd : Zef2T α e H f c Γ) : Nlog α ≤ f 0 := by
  cases dd <;> assumption

/-- `Zef2 ⊆ Zef2T` (the inclusion; (Ax2) is an extension). -/
theorem ofZef2 : ∀ {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Seq},
    Zef2 α e H f c Γ → Zef2T α e H f c Γ := by
  intro α e H f c Γ dd
  induction dd with
  | axL hαN r v hp hn => exact Zef2T.axL hαN r v hp hn
  | wk hαN hsub _ ih => exact Zef2T.wk hαN hsub ih
  | weak hαN hβ hβNF hαNF hβH hsub _ ih => exact Zef2T.weak hαN hβ hβNF hαNF hβH hsub ih
  | allω hαN φ β hβ hβNF hαNF hβH _ ih => exact Zef2T.allω hαN φ β hβ hβNF hαNF hβH ih
  | exI hαN φ n hβ hβNF hαNF hβH hbound _ ih =>
      exact Zef2T.exI hαN φ n hβ hβNF hαNF hβH hbound ih
  | cut hαN φ hcompl hcutRead hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH _ _ ih₁ ih₂ =>
      exact Zef2T.cut hαN φ hcompl hcutRead hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH ih₁ ih₂

end Zef2T

/-! ## (b) The concrete leaf pair -/

/-- The PA equality-axiom-shaped matrix `#0 = #0` (reflexivity — the equality block's simplest
member; every instance `n = n` is a true closed literal). -/
noncomputable def eqReflMatrix : SyntacticSemiformula ℒₒᵣ 1 :=
  Semiformula.rel (Language.Eq.eq : (ℒₒᵣ).Rel 2) ![#0, #0]

theorem eqReflMatrix_inst (n : ℕ) : eqReflMatrix/[nm n] =
    Semiformula.rel (Language.Eq.eq : (ℒₒᵣ).Rel 2) ![nm n, nm n] := by
  simp [eqReflMatrix, Semiformula.rew_rel2]

theorem eqReflMatrix_inst_true (n : ℕ) : atomTrue (eqReflMatrix/[nm n]) := by
  rw [eqReflMatrix_inst]
  simp [atomTrue, nm]

/-- **`Zef2T` closes the PA-axiom leaf `{∀x (x = x)}` at rank 0** — root ordinal `1`, slot `id`:
one `allω` node (branch ordinals `0`), each branch a single `trueRel` (Ax2) leaf on the true
literal `n = n`. -/
theorem zef2T_derives_paRefl (e : ONote) (H : ONote → Prop) :
    Zef2T 1 e H (· + 1) 0 {(∀⁰ eqReflMatrix)} := by
  have h1 : ({(∀⁰ eqReflMatrix)} : Seq) = insert (∀⁰ eqReflMatrix) ∅ := rfl
  rw [h1]
  have hN1 : Nlog 1 ≤ 1 := by
    rw [show (1 : ONote) = ONote.oadd 0 1 0 from rfl]
    simp [clog]
    decide
  refine Zef2T.allω hN1 eqReflMatrix (fun _ => 0) (fun n => ?_) (fun n => NF.zero)
    ?_ (fun n => ?_) (fun n => ?_)
  · -- 0 < 1 in ONote
    rw [show (1 : ONote) = ONote.oadd 0 1 0 from rfl]
    exact ONote.oadd_pos _ _ _
  · -- NF 1
    exact NF.oadd NF.zero 1 NFBelow.zero
  · -- relOp H n 0 = Cl (adjoin H n) 0
    rw [show (0 : ONote) = ONote.ofNat 0 by simp]
    exact Cl.ofNat 0
  · -- branch n: one trueRel leaf on the true literal `n = n`
    have hlit := eqReflMatrix_inst (n := n)
    refine Zef2T.trueRel (by simp) (Language.Eq.eq : (ℒₒᵣ).Rel 2) ![nm n, nm n] ?_ ?_
    · simpa [hlit] using eqReflMatrix_inst_true n
    · rw [← hlit]
      exact Finset.mem_insert_self _ _

/-- **ANY singleton is rank-0 underivable in `Zef2`** (lap-199 corollary — a singleton is
trivially uniform-spine). -/
theorem zef2_rank0_singleton_underivable (ψ : Form)
    {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} :
    ¬ Zef2 α e H f 0 {ψ} := by
  intro dd
  refine zef2_rank0_uniform_spine_underivable (t := spineHead ψ) dd rfl ?_
  intro χ hχ
  rw [Finset.mem_singleton] at hχ
  rw [hχ]

/-- **`Zef2` canNOT close the PA-axiom leaf** — the concrete other half of the Ax2-need pair. -/
theorem zef2_not_derives_paRefl {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} :
    ¬ Zef2 α e H f 0 {(∀⁰ eqReflMatrix)} :=
  zef2_rank0_singleton_underivable _

/-! ## (a) The rung-E statement DRAFT -/

/-- The goodstein Π₂ body: `goodsteinSentence = ∀⁰ goodsteinBody` where
`goodsteinBody = “∃ N, !igoodsteinDef 0 #0 N”` — the concrete matrix binding (R-6). -/
noncomputable def goodsteinBody : Semisentence ℒₒᵣ 1 :=
  “∃ N, !LO.FirstOrder.Arithmetic.igoodsteinDef 0 #1 N”

/-- Faithfulness of the binding: the sentence IS `∀⁰` of the body (definitional). -/
theorem goodsteinSentence_eq_all_body :
    GoodsteinPA.goodsteinSentence = ∀⁰ goodsteinBody := rfl

/-- The syntactic (ℕ-variable) embedding of the body — the `Γ_G` instance matrix lives at the
`Seq` level (`SyntacticFormula`). -/
noncomputable def goodsteinBodyE : SyntacticSemiformula ℒₒᵣ 1 :=
  Rewriting.emb goodsteinBody

/-- **DRAFT (E-0; NOT ratified — DO NOT port to src).**  Rung E re-based onto `Zef2T` (forced
by the Ax2-need answer above): from a PA proof of the goodstein sentence, uniform existential
budgets `B` (root slot), `d` (cut rank), `e` (control tower, NF), and for every instance `m` a
per-instance NF node ordinal `α_m` closed under the operator, such that the `m`-th instance
singleton — the CONCRETE translation binding `{goodsteinBodyE/[nm m]}` — is `Zef2T`-derivable
at slot `ewRootSlot e B`.

Instance-uniformity of `B`/`d`/`e` follows the W3 `∃ c d₀, ∀ env` discipline (one finite PA
proof ⇒ one budget); `α` stays per-instance (numeral-sized ω-nodes).  ALTERNATIVE under judge
consideration: hoist `∃ α` uniform too (the instance derivations differ only by numeral
substitution; E–W Lemma 33 suggests uniform α works) — flagged, not chosen here.

The `∃⁰`-read-off compatibility: `goodsteinBodyE/[nm m]` is itself `∃⁰`-headed (the `N`
witness), with `𝚺₁`-matrix instances — the rank-0 exit feeds the (Ax2)-aware Δ₀ read-off,
which per the Stage-B/lap-199 findings must be RE-PROVEN over `Zef2T` (the `Zef2` rung D is
vacuous; the spine-head obstruction dissolves under (Ax2) by design). -/
theorem embedding_Zef2T_DRAFT :
    (𝗣𝗔 ⊢ ↑GoodsteinPA.goodsteinSentence) →
      ∃ B d : ℕ, ∃ e : ONote, e.NF ∧ ∀ m : ℕ, ∃ α : ONote, α.NF ∧ ∃ H : ONote → Prop,
        Cl H α ∧ Zef2T α e H (ewRootSlot e B) d {(goodsteinBodyE/[nm m])} := by
  sorry


/-! ## E-1 seam probe — `Zef2T` LACKS the connective rules the embedding needs

First E-1 grind block, and it fires at the STATEMENT level: the W3 case ladder (Derivation2
induction) has `verum`/`and`/`or` cases (PA proofs contain arbitrary connective formulas), and
`Zekd` — the calculus the W3 skeleton targeted — has `verumR`/`andI`/`orI` rules for them
(`OperatorZinfty.lean:50,58,62`).  `Zef2` deleted the connective rules (sound for the cut-elim
grind, where `⊤/⊥/⋏/⋎` cut formulas are never principal — `Zef2.erase_inert`), and the `Zef2T`
clone above inherits the deletion.

**Kernel fact: even WITH (Ax2), the `verum` case is underivable** —
`zef2T_not_derives_verum` below, via the none-spine invariant (every member inert-headed ⇒ no
leaf can fire: `axL`/`trueRel`/`trueNrel` need a literal head, `allω`/`exI` insert
spine-preserving instances, no rank-0 cut).  `{A ⋏ B}` singletons with inert-headed `A ⋏ B`
are covered by the same invariant, and the `and` case has no rule to split on regardless.

**Consequence for the rung-E DRAFT (judge input, statement-level):** `embedding_Zef2T_DRAFT`
is UNPROVABLE-AS-SHAPED unless the target calculus is extended to the FULL E–W Def-23 rule
set: `Zef2TC := Zef2T + verumR + andI + orI` (the `Zekd` shapes with `Nlog` gates threaded,
ordinal-descending premises).  E–W's (⋀)/(⋁) rules cover finite conjunction/disjunction
alongside the ω-rules; the `Zef2` port narrowed to the ω-fragment for the cut-elim grind, and
rung E forces the finite fragment back in.  Cost fallout to measure for the ruling: `passAux`
gains ⋏/⋎ PRINCIPAL cut shapes (the `erase_inert` dodge stops applying — genuine
inversion/reduction cases, E–W Lemma 25's finite arms), and each read-off gains two cases.
This is the honest Def-23-faithfulness cost deferred when `Zef2` dropped the connectives. -/

/-- **None-spine sequents are rank-0 underivable EVEN IN `Zef2T`** — (Ax2) only helps literal
heads.  Mirror of the src spine-head invariant with the two extra leaf cases. -/
theorem zef2T_rank0_noneSpine_underivable :
    ∀ {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Seq},
      Zef2T α e H f c Γ → c = 0 → (∀ ψ ∈ Γ, spineHead ψ = none) → False := by
  intro α e H f c Γ dd
  induction dd with
  | @axL α e H f c Γ ar hαN r v hp hn =>
      intro _ hyp
      have h1 := hyp _ hp
      rw [show spineHead (Semiformula.rel r v) = some (true, ⟨ar, r⟩) from rfl] at h1
      simp at h1
  | @trueRel α e H f c Γ ar hαN r v htrue hmem =>
      intro _ hyp
      have h1 := hyp _ hmem
      rw [show spineHead (Semiformula.rel r v) = some (true, ⟨ar, r⟩) from rfl] at h1
      simp at h1
  | @trueNrel α e H f c Γ ar hαN r v htrue hmem =>
      intro _ hyp
      have h1 := hyp _ hmem
      rw [show spineHead (Semiformula.nrel r v) = some (false, ⟨ar, r⟩) from rfl] at h1
      simp at h1
  | wk hαN hsub _ ih =>
      intro hc hyp
      exact ih hc (fun ψ hψ => hyp ψ (hsub hψ))
  | weak hαN hβ hβNF hαNF hβH hsub _ ih =>
      intro hc hyp
      exact ih hc (fun ψ hψ => hyp ψ (hsub hψ))
  | @allω α e H f c Γ hαN φ β hβ hβNF hαNF hβH dd ih =>
      intro hc hyp
      refine ih 0 hc ?_
      intro ψ hψ
      rcases Finset.mem_insert.mp hψ with rfl | hψΓ
      · rw [spineHead_substs]
        simpa using hyp (∀⁰ φ) (Finset.mem_insert_self _ _)
      · exact hyp ψ (Finset.mem_insert_of_mem hψΓ)
  | @exI α β e H f c Γ hαN φ n hβ hβNF hαNF hβH hbound dd ih =>
      intro hc hyp
      refine ih hc ?_
      intro ψ hψ
      rcases Finset.mem_insert.mp hψ with rfl | hψΓ
      · rw [spineHead_substs]
        simpa using hyp (∃⁰ φ) (Finset.mem_insert_self _ _)
      · exact hyp ψ (Finset.mem_insert_of_mem hψΓ)
  | cut hαN φ hcompl hcutRead hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH _ _ _ _ =>
      intro hc _
      omega

/-- **The embedding's `verum` case is UNDERIVABLE in `Zef2T`** — the connective-rule gap. -/
theorem zef2T_not_derives_verum {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} :
    ¬ Zef2T α e H f 0 {(⊤ : Form)} := by
  intro dd
  refine zef2T_rank0_noneSpine_underivable dd rfl ?_
  intro ψ hψ
  rw [Finset.mem_singleton] at hψ
  rw [hψ]
  rfl

end GoodsteinPA.E0Ax2NeedProbe
