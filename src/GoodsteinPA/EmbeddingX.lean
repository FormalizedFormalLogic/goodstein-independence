/-
# C₂ — the embedding `𝗣𝗔(LX) ⊢ φ ⟹ Z_∞ ⊢^{α}_c {φ}` over `LX`, `XFreeAx`-preserving

Port of `src/Embedding.lean`'s `embedC` from `ℒₒᵣ`/`Provable` to `LX`/`PXFc` (the `XFreeAx`-tracking,
cut-rank-carrying carrier of `XFreeCutElim.lean`). The structural cases mirror `embedC` verbatim
(swapping the builders for their `PXFc.*` twins, all `XFreeAx`-safe). The two non-structural cases:

- **`axm`** splits. **X-free axioms** (`𝗣𝗔⁻(LX)` image + induction over X-free formulas) are TRUE
  closed X-free formulas, discharged by `provable_true_x` (ω-completeness emitting only X-free
  `axTrue` leaves ⟹ `XFreeAx`-safe). **X-induction instances** go through `metaInduction` (a tower of
  `cut`s on `ψ(i)` bottoming out at `provable_em_x`, never a lone X-`axTrue`).
- **`exs`** (open witness `t`): `asgX e ▹ (φ/[t])` is `((asgX e).q ▹ φ)/[asgX e t]` with `asgX e t`
  closed; collapse to its numeral value via the value-congruent EM `provable_em_cong_gen_x` + a `cut`
  (`PXFc.exI_closed`), then numeral-`exI`.

This file delivers the `axm`-abstracted structural port `embedC_LX_gen`; the X-free / X-induction
discharge for the concrete `paLX` schema (`embedC_LX`) chains on top.
-/
import GoodsteinPA.XFreeCutElim
import Foundation.FirstOrder.Arithmetic.Schemata

namespace GoodsteinPA.EmbeddingX

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open GoodsteinPA.ZinftyGen GoodsteinPA.LangX GoodsteinPA.XFreeCutElim

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

/-! ## X-freeness of a formula (structural; every relation symbol is an `ℒₒᵣ`-relation `Sum.inl`) -/

/-- A `Semiformula LX` is **X-free** when every relation symbol occurring in it is an `ℒₒᵣ`-relation
(`Sum.isLeft = true`), i.e. none is the set variable `X`. Defined by structural recursion. -/
def XFreeForm {ξ n} : Semiformula LX ξ n → Prop :=
  Semiformula.rec' (C := fun _ _ => Prop)
    True True
    (fun {_ _} r _ => Sum.isLeft r = true)
    (fun {_ _} r _ => Sum.isLeft r = true)
    (fun {_} _ _ p q => p ∧ q)
    (fun {_} _ _ p q => p ∧ q)
    (fun {_} _ p => p)
    (fun {_} _ p => p)

@[simp] lemma xfreeForm_verum {ξ n} : XFreeForm (⊤ : Semiformula LX ξ n) := trivial
@[simp] lemma xfreeForm_falsum {ξ n} : XFreeForm (⊥ : Semiformula LX ξ n) := trivial
@[simp] lemma xfreeForm_rel {ξ n k} (r : LX.Rel k) (v : Fin k → Semiterm LX ξ n) :
    XFreeForm (Semiformula.rel r v) ↔ Sum.isLeft r = true := Iff.rfl
@[simp] lemma xfreeForm_nrel {ξ n k} (r : LX.Rel k) (v : Fin k → Semiterm LX ξ n) :
    XFreeForm (Semiformula.nrel r v) ↔ Sum.isLeft r = true := Iff.rfl
@[simp] lemma xfreeForm_and {ξ n} (φ ψ : Semiformula LX ξ n) :
    XFreeForm (φ ⋏ ψ) ↔ XFreeForm φ ∧ XFreeForm ψ := Iff.rfl
@[simp] lemma xfreeForm_or {ξ n} (φ ψ : Semiformula LX ξ n) :
    XFreeForm (φ ⋎ ψ) ↔ XFreeForm φ ∧ XFreeForm ψ := Iff.rfl
@[simp] lemma xfreeForm_all {ξ n} (φ : Semiformula LX ξ (n + 1)) :
    XFreeForm (∀⁰ φ) ↔ XFreeForm φ := Iff.rfl
@[simp] lemma xfreeForm_exs {ξ n} (φ : Semiformula LX ξ (n + 1)) :
    XFreeForm (∃⁰ φ) ↔ XFreeForm φ := Iff.rfl

@[simp] lemma xfreeForm_neg {ξ n} (φ : Semiformula LX ξ n) : XFreeForm (∼φ) ↔ XFreeForm φ := by
  induction φ using Semiformula.rec' <;> simp_all

/-- X-freeness only inspects relation symbols, which any rewriting `ω ▹ ·` preserves. -/
@[simp] lemma xfreeForm_rew {ξ ζ n m} (ω : Rew LX ξ n ζ m) (φ : Semiformula LX ξ n) :
    XFreeForm (ω ▹ φ) ↔ XFreeForm φ := by
  induction φ using Semiformula.rec' generalizing ζ m with
  | hverum => simp
  | hfalsum => simp
  | hrel r v => simp [Semiformula.rew_rel]
  | hnrel r v => simp [Semiformula.rew_nrel]
  | hand φ ψ ihφ ihψ => simp [ihφ, ihψ]
  | hor φ ψ ihφ ihψ => simp [ihφ, ihψ]
  | hall φ ih => simpa using ih _
  | hexs φ ih => simpa using ih _

/-- The numeral `nm n` evaluates to `n` under the ambient `Boundedness.ambient` instance (which is
`structLX ∅`, defeq), so `LitTrue` substitution instances simplify. -/
@[simp] lemma val_nm_ambient (n : ℕ) :
    Semiterm.val Boundedness.ambient ![] (id : ℕ → ℕ) (nm n) = n :=
  Boundedness.val_nm_structLX (fun _ => False) n

/-- The same fact phrased with `Semiterm.valm ℕ` (the ambient instance), so it `rw`s in `LitTrue`/EM
goals stated with `valm`. -/
@[simp] lemma valm_nm (n : ℕ) :
    Semiterm.valm ℕ ![] (id : ℕ → ℕ) (nm n : Semiterm LX ℕ 0) = n :=
  Boundedness.val_nm_structLX (fun _ => False) n

/-! ## ω-completeness for TRUE closed X-free formulas, `XFreeAx`-preserving. -/

/-- **ω-completeness, `XFreeAx` form.** Any closed `LX`-formula that is X-free and TRUE in the
standard model `ℕ` is `Z∞`-derivable cut-free with an X-free derivation. Mirrors
`Embedding.provable_true`; the atomic leaves use `PXFc.axTrue` with the X-freeness witness, so the
whole derivation is `XFreeAx`. -/
theorem provable_true_x : ∀ (k : ℕ) (φ : Form LX), φ.complexity ≤ k → XFreeForm φ → LitTrue φ →
    ∀ {Γ : Seq LX}, φ ∈ Γ → ∃ a, PXFc a 0 Γ := by
  intro k
  induction k with
  | zero =>
    intro φ hk hxf htrue Γ hmem
    cases φ using Semiformula.cases' with
    | hverum => exact ⟨0, PXFc.verumR hmem⟩
    | hfalsum => simp [LitTrue] at htrue
    | hrel r v => exact ⟨0, PXFc.axTrue true r v (by simpa using hxf) htrue hmem⟩
    | hnrel r v => exact ⟨0, PXFc.axTrue false r v (by simpa using hxf) htrue hmem⟩
    | hand φ ψ => simp at hk
    | hor φ ψ => simp at hk
    | hall φ => simp at hk
    | hexs φ => simp at hk
  | succ k ih =>
    intro φ hk hxf htrue Γ hmem
    cases φ using Semiformula.cases' with
    | hverum => exact ⟨0, PXFc.verumR hmem⟩
    | hfalsum => simp [LitTrue] at htrue
    | hrel r v => exact ⟨0, PXFc.axTrue true r v (by simpa using hxf) htrue hmem⟩
    | hnrel r v => exact ⟨0, PXFc.axTrue false r v (by simpa using hxf) htrue hmem⟩
    | hand a b =>
      have hak : a.complexity ≤ k := by simp only [Semiformula.complexity_and] at hk; omega
      have hbk : b.complexity ≤ k := by simp only [Semiformula.complexity_and] at hk; omega
      obtain ⟨hxa, hxb⟩ : XFreeForm a ∧ XFreeForm b := by simpa using hxf
      have htab : LitTrue a ∧ LitTrue b := by simpa [LitTrue] using htrue
      obtain ⟨hta, htb⟩ := htab
      obtain ⟨a1, h1⟩ := ih a hak hxa hta (Γ := insert a Γ) (by simp)
      obtain ⟨a2, h2⟩ := ih b hbk hxb htb (Γ := insert b Γ) (by simp)
      have hand := PXFc.andI a b h1 h2
      rw [Finset.insert_eq_self.mpr hmem] at hand
      exact ⟨_, hand⟩
    | hor a b =>
      have hak : a.complexity ≤ k := by simp only [Semiformula.complexity_or] at hk; omega
      have hbk : b.complexity ≤ k := by simp only [Semiformula.complexity_or] at hk; omega
      obtain ⟨hxa, hxb⟩ : XFreeForm a ∧ XFreeForm b := by simpa using hxf
      have htor : LitTrue a ∨ LitTrue b := by simpa [LitTrue] using htrue
      rcases htor with hta | htb
      · obtain ⟨a1, h1⟩ := ih a hak hxa hta (Γ := insert a (insert b Γ)) (by simp)
        have hor := PXFc.orI a b h1
        rw [Finset.insert_eq_self.mpr hmem] at hor
        exact ⟨_, hor⟩
      · obtain ⟨a1, h1⟩ := ih b hbk hxb htb (Γ := insert a (insert b Γ)) (by simp)
        have hor := PXFc.orI a b h1
        rw [Finset.insert_eq_self.mpr hmem] at hor
        exact ⟨_, hor⟩
    | hall a =>
      have hak : a.complexity ≤ k := by simp only [Semiformula.complexity_all] at hk; omega
      have hxa : XFreeForm a := by simpa using hxf
      have hfam : ∀ n, LitTrue (a/[nm n]) := by
        intro n
        have := htrue
        simp only [LitTrue, Semiformula.eval_all] at this
        simpa [LitTrue, Semiformula.eval_substs, val_nm_ambient, Matrix.constant_eq_singleton]
          using this n
      have fam : ∀ n, ∃ x, PXFc x 0 (insert (a/[nm n]) Γ) := by
        intro n
        have hcomp : (a/[nm n]).complexity ≤ k := by
          have : (a/[nm n]).complexity = a.complexity := by simp
          rw [this]; exact hak
        exact ih (a/[nm n]) hcomp (by simpa using hxa) (hfam n) (by simp)
      choose β hβ using fam
      have hallω := PXFc.allω a hβ
      rw [Finset.insert_eq_self.mpr hmem] at hallω
      exact ⟨_, hallω⟩
    | hexs a =>
      have hak : a.complexity ≤ k := by simp only [Semiformula.complexity_exs] at hk; omega
      have hxa : XFreeForm a := by simpa using hxf
      have hex : ∃ n, LitTrue (a/[nm n]) := by
        have := htrue
        simp only [LitTrue, Semiformula.eval_ex] at this
        obtain ⟨x, hx⟩ := this
        exact ⟨x, by simpa [LitTrue, Semiformula.eval_substs, Boundedness.val_nm_structLX,
          Matrix.constant_eq_singleton] using hx⟩
      obtain ⟨n, hn⟩ := hex
      have hcomp : (a/[nm n]).complexity ≤ k := by
        have : (a/[nm n]).complexity = a.complexity := by simp
        rw [this]; exact hak
      obtain ⟨x, hx⟩ := ih (a/[nm n]) hcomp (by simpa using hxa) hn (Γ := insert (a/[nm n]) Γ) (by simp)
      have hexI := PXFc.exI a n hx
      rw [Finset.insert_eq_self.mpr hmem] at hexI
      exact ⟨_, hexI⟩

/-! ## The closing assignment `asgX` + rewriting plumbing (LX ports of `Embedding.asg` & co.) -/

/-- The closing substitution over `LX`: free variable `&x ↦ nm (e x)`. Sends every
`SyntacticFormula LX` to a closed (sentence-image) formula. -/
noncomputable def asgX (e : ℕ → ℕ) : Rew LX ℕ 0 ℕ 0 := Rew.rewrite (fun x => nm (e x))

/-- Substitution–rewriting commutation for an arbitrary witness term `t`:
`ω ▹ (φ/[t]) = (ω.q ▹ φ)/[ω t]`. With `ω = asgX e`, `ω t` is closed. -/
lemma rew_subst_term (ω : Rew LX ℕ 0 ℕ 0) (φ : SyntacticSemiformula LX 1)
    (t : SyntacticTerm LX) : ω ▹ (φ/[t]) = (ω.q ▹ φ)/[ω t] := by
  show ω ▹ (Rew.subst ![t] ▹ φ) = Rew.subst ![ω t] ▹ (ω.q ▹ φ)
  have heq : ω.comp (Rew.subst ![t]) = (Rew.subst ![ω t]).comp ω.q := by
    ext x
    · cases x using Fin.cases with
      | zero => simp [Rew.comp_app]
      | succ i => exact Fin.elim0 i
    · simp [Rew.comp_app]
  rw [← TransitiveRewriting.comp_app, ← TransitiveRewriting.comp_app, heq]

/-! ## Value-congruent excluded middle over `LX` (the `exs` engine).

The `LX` port of `Embedding.provable_em_cong_gen`. Because the calculus now has the value-congruent
literal axiom `PXFc.axLv`, every atomic case closes **uniformly via `axLv`** (no `LitTrue` split, no
`axTrue`) — so the derivation is `XFreeAx`-safe for X-atoms too. Exactly what the `exs` collapse needs. -/

/-- Value of a renamed term depends only on the values of the substituted terms. -/
lemma valm_subst_congr {n} (w w' : Fin n → SyntacticTerm LX)
    (hval : ∀ i, Semiterm.valm ℕ ![] (id : ℕ → ℕ) (w i)
                = Semiterm.valm ℕ ![] (id : ℕ → ℕ) (w' i))
    (t : SyntacticSemiterm LX n) :
    Semiterm.valm ℕ ![] (id : ℕ → ℕ) (Rew.subst w t)
      = Semiterm.valm ℕ ![] (id : ℕ → ℕ) (Rew.subst w' t) := by
  simp only [Semiterm.valm, Semiterm.val_substs]
  congr 1; funext x; exact hval x

/-- Substitution-composition (LX port). -/
lemma subst_q_cons (w : Fin n → SyntacticTerm LX) (m : ℕ) :
    (Rew.subst ![nm m]).comp (Rew.subst w).q = Rew.subst (nm m :> w) := by
  ext x
  · cases x using Fin.cases with
    | zero => simp [Rew.comp_app]
    | succ i => simp [Rew.comp_app]
  · simp [Rew.comp_app]

lemma subst_q_cons_app (w : Fin n → SyntacticTerm LX) (m : ℕ)
    (ψ : SyntacticSemiformula LX (n + 1)) :
    ((Rew.subst w).q ▹ ψ)/[nm m] = Rew.subst (nm m :> w) ▹ ψ := by
  show Rew.subst ![nm m] ▹ ((Rew.subst w).q ▹ ψ) = Rew.subst (nm m :> w) ▹ ψ
  rw [← TransitiveRewriting.comp_app, subst_q_cons]

/-- **Value-congruent excluded middle (arity-general), `XFreeAx` form.** -/
theorem provable_em_cong_gen_x : ∀ (k : ℕ) {n : ℕ} (w w' : Fin n → SyntacticTerm LX)
    (ψ : SyntacticSemiformula LX n), ψ.complexity ≤ k →
    (∀ i, Semiterm.valm ℕ ![] (id : ℕ → ℕ) (w i)
        = Semiterm.valm ℕ ![] (id : ℕ → ℕ) (w' i)) →
    ∀ {Γ : Seq LX}, (Rew.subst w ▹ ψ) ∈ Γ → (∼(Rew.subst w' ▹ ψ)) ∈ Γ → ∃ a, PXFc a 0 Γ := by
  intro k
  induction k with
  | zero =>
    intro n w w' ψ hk hval Γ hp hn
    cases ψ using Semiformula.cases' with
    | hverum => exact ⟨0, PXFc.verumR (by simpa using hp)⟩
    | hfalsum => exact ⟨0, PXFc.verumR (by simpa using hn)⟩
    | hrel r v => exact atomic_close_x w w' hval r v hp hn
    | hnrel r v => exact atomic_close_neg_x w w' hval r v hp hn
    | hand φ ψ => simp at hk
    | hor φ ψ => simp at hk
    | hall φ => simp at hk
    | hexs φ => simp at hk
  | succ k ih =>
    intro n w w' ψ hk hval Γ hp hn
    cases ψ using Semiformula.cases' with
    | hverum => exact ⟨0, PXFc.verumR (by simpa using hp)⟩
    | hfalsum => exact ⟨0, PXFc.verumR (by simpa using hn)⟩
    | hrel r v => exact atomic_close_x w w' hval r v hp hn
    | hnrel r v => exact atomic_close_neg_x w w' hval r v hp hn
    | hand a b =>
      have hak : a.complexity ≤ k := by simp only [Semiformula.complexity_and] at hk; omega
      have hbk : b.complexity ≤ k := by simp only [Semiformula.complexity_and] at hk; omega
      have hp' : ((Rew.subst w ▹ a) ⋏ (Rew.subst w ▹ b)) ∈ Γ := by simpa using hp
      have hn' : (∼(Rew.subst w' ▹ a) ⋎ ∼(Rew.subst w' ▹ b)) ∈ Γ := by simpa using hn
      obtain ⟨a1, h1⟩ := ih (n := n) w w' a hak hval
        (Γ := insert (Rew.subst w ▹ a)
          (insert (∼(Rew.subst w' ▹ a)) (insert (∼(Rew.subst w' ▹ b)) Γ)))
        (by simp) (by simp)
      obtain ⟨a2, h2⟩ := ih (n := n) w w' b hbk hval
        (Γ := insert (Rew.subst w ▹ b)
          (insert (∼(Rew.subst w' ▹ a)) (insert (∼(Rew.subst w' ▹ b)) Γ)))
        (by simp) (by simp)
      have hand := PXFc.andI (Rew.subst w ▹ a) (Rew.subst w ▹ b) h1 h2
      rw [Finset.insert_eq_self.mpr (show ((Rew.subst w ▹ a) ⋏ (Rew.subst w ▹ b))
        ∈ insert (∼(Rew.subst w' ▹ a)) (insert (∼(Rew.subst w' ▹ b)) Γ) by simp [hp'])] at hand
      have hor := PXFc.orI (∼(Rew.subst w' ▹ a)) (∼(Rew.subst w' ▹ b)) hand
      rw [Finset.insert_eq_self.mpr hn'] at hor
      exact ⟨_, hor⟩
    | hor a b =>
      have hak : a.complexity ≤ k := by simp only [Semiformula.complexity_or] at hk; omega
      have hbk : b.complexity ≤ k := by simp only [Semiformula.complexity_or] at hk; omega
      have hp' : ((Rew.subst w ▹ a) ⋎ (Rew.subst w ▹ b)) ∈ Γ := by simpa using hp
      have hn' : (∼(Rew.subst w' ▹ a) ⋏ ∼(Rew.subst w' ▹ b)) ∈ Γ := by simpa using hn
      obtain ⟨a1, h1⟩ := ih (n := n) w w' a hak hval
        (Γ := insert (∼(Rew.subst w' ▹ a))
          (insert (Rew.subst w ▹ a) (insert (Rew.subst w ▹ b) Γ)))
        (by simp) (by simp)
      obtain ⟨a2, h2⟩ := ih (n := n) w w' b hbk hval
        (Γ := insert (∼(Rew.subst w' ▹ b))
          (insert (Rew.subst w ▹ a) (insert (Rew.subst w ▹ b) Γ)))
        (by simp) (by simp)
      have hand := PXFc.andI (∼(Rew.subst w' ▹ a)) (∼(Rew.subst w' ▹ b)) h1 h2
      rw [Finset.insert_eq_self.mpr (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hn'))]
        at hand
      have hor := PXFc.orI (Rew.subst w ▹ a) (Rew.subst w ▹ b) hand
      rw [Finset.insert_eq_self.mpr (show ((Rew.subst w ▹ a) ⋎ (Rew.subst w ▹ b)) ∈ Γ
        by simp [hp'])] at hor
      exact ⟨_, hor⟩
    | hall a =>
      have hak : a.complexity ≤ k := by simp only [Semiformula.complexity_all] at hk; omega
      have hp' : (∀⁰ ((Rew.subst w).q ▹ a)) ∈ Γ := by simpa using hp
      have hn' : (∃⁰ ((Rew.subst w').q ▹ ∼a)) ∈ Γ := by simpa using hn
      have fam : ∀ m, ∃ x, PXFc x 0 (insert (((Rew.subst w).q ▹ a)/[nm m]) Γ) := by
        intro m
        have hvalm : ∀ i, Semiterm.valm ℕ ![] (id : ℕ → ℕ) ((nm m :> w) i)
            = Semiterm.valm ℕ ![] (id : ℕ → ℕ) ((nm m :> w') i) := by
          intro i; cases i using Fin.cases with
          | zero => rfl
          | succ j => simpa using hval j
        obtain ⟨x, hx⟩ := ih (n := n + 1) (nm m :> w) (nm m :> w') a hak hvalm
          (Γ := insert (((Rew.subst w).q ▹ a)/[nm m])
            (insert (∼(((Rew.subst w').q ▹ a)/[nm m])) Γ))
          (by rw [← subst_q_cons_app]; simp)
          (by rw [← subst_q_cons_app]; simp)
        have hexI := PXFc.exI ((Rew.subst w').q ▹ ∼a) m
          (Γ := insert (((Rew.subst w).q ▹ a)/[nm m]) Γ)
          (by
            have heq : (((Rew.subst w').q ▹ ∼a)/[nm m])
                = ∼(((Rew.subst w').q ▹ a)/[nm m]) := by simp
            rw [heq, Finset.insert_comm]; exact hx)
        rw [Finset.insert_eq_self.mpr (Finset.mem_insert_of_mem hn')] at hexI
        exact ⟨_, hexI⟩
      choose β hβ using fam
      have hallω := PXFc.allω ((Rew.subst w).q ▹ a) hβ
      rw [Finset.insert_eq_self.mpr hp'] at hallω
      exact ⟨_, hallω⟩
    | hexs a =>
      have hak : a.complexity ≤ k := by simp only [Semiformula.complexity_exs] at hk; omega
      have hp' : (∃⁰ ((Rew.subst w).q ▹ a)) ∈ Γ := by simpa using hp
      have hn' : (∀⁰ ((Rew.subst w').q ▹ ∼a)) ∈ Γ := by simpa using hn
      have fam : ∀ m, ∃ x, PXFc x 0 (insert (((Rew.subst w').q ▹ ∼a)/[nm m]) Γ) := by
        intro m
        have hvalm : ∀ i, Semiterm.valm ℕ ![] (id : ℕ → ℕ) ((nm m :> w) i)
            = Semiterm.valm ℕ ![] (id : ℕ → ℕ) ((nm m :> w') i) := by
          intro i; cases i using Fin.cases with
          | zero => rfl
          | succ j => simpa using hval j
        obtain ⟨x, hx⟩ := ih (n := n + 1) (nm m :> w) (nm m :> w') a hak hvalm
          (Γ := insert (((Rew.subst w).q ▹ a)/[nm m])
            (insert (∼(((Rew.subst w').q ▹ a)/[nm m])) Γ))
          (by rw [← subst_q_cons_app]; simp)
          (by rw [← subst_q_cons_app]; simp)
        have hexI := PXFc.exI ((Rew.subst w).q ▹ a) m
          (Γ := insert (∼(((Rew.subst w').q ▹ a)/[nm m])) Γ) hx
        rw [Finset.insert_eq_self.mpr (Finset.mem_insert_of_mem hp')] at hexI
        have heq : (((Rew.subst w').q ▹ ∼a)/[nm m]) = ∼(((Rew.subst w').q ▹ a)/[nm m]) := by simp
        rw [heq]; exact ⟨_, hexI⟩
      choose β hβ using fam
      have hallω := PXFc.allω ((Rew.subst w').q ▹ ∼a) hβ
      rw [Finset.insert_eq_self.mpr hn'] at hallω
      exact ⟨_, hallω⟩
where
  atomic_close_x {n} (w w' : Fin n → SyntacticTerm LX)
      (hval : ∀ i, Semiterm.valm ℕ ![] (id : ℕ → ℕ) (w i)
                = Semiterm.valm ℕ ![] (id : ℕ → ℕ) (w' i))
      {k} (r : (LX).Rel k) (v : Fin k → SyntacticSemiterm LX n)
      {Γ : Seq LX} (hp : (Rew.subst w ▹ Semiformula.rel r v) ∈ Γ)
      (hn : (∼(Rew.subst w' ▹ Semiformula.rel r v)) ∈ Γ) : ∃ a, PXFc a 0 Γ := by
    have hp' : Semiformula.rel r (fun i => Rew.subst w (v i)) ∈ Γ := by
      simpa [Semiformula.rew_rel] using hp
    have hn' : Semiformula.nrel r (fun i => Rew.subst w' (v i)) ∈ Γ := by
      simpa [Semiformula.rew_rel] using hn
    exact ⟨0, PXFc.axLv r _ _ (fun i => valm_subst_congr w w' hval (v i)) hp' hn'⟩
  atomic_close_neg_x {n} (w w' : Fin n → SyntacticTerm LX)
      (hval : ∀ i, Semiterm.valm ℕ ![] (id : ℕ → ℕ) (w i)
                = Semiterm.valm ℕ ![] (id : ℕ → ℕ) (w' i))
      {k} (r : (LX).Rel k) (v : Fin k → SyntacticSemiterm LX n)
      {Γ : Seq LX} (hp : (Rew.subst w ▹ Semiformula.nrel r v) ∈ Γ)
      (hn : (∼(Rew.subst w' ▹ Semiformula.nrel r v)) ∈ Γ) : ∃ a, PXFc a 0 Γ := by
    have hp' : Semiformula.nrel r (fun i => Rew.subst w (v i)) ∈ Γ := by
      simpa [Semiformula.rew_nrel] using hp
    have hn' : Semiformula.rel r (fun i => Rew.subst w' (v i)) ∈ Γ := by
      simpa [Semiformula.rew_nrel] using hn
    exact ⟨0, PXFc.axLv r _ _ (fun i => (valm_subst_congr w w' hval (v i)).symm) hn' hp'⟩

/-- **Closed-term ∃-introduction, `XFreeAx` form.** From `⊢ ψ/[s], Γ` (any closed `s`) conclude
`⊢ ∃⁰ψ, Γ`: collapse `s` to its numeral value via `provable_em_cong_gen_x` + a `cut`, then numeral
`exI`. The cut raises the rank to `max c (ψ.complexity+1)`. -/
theorem PXFc.exI_closed {α : Ordinal.{0}} {c : ℕ} {Γ : Seq LX}
    (ψ : SyntacticSemiformula LX 1) (s : SyntacticTerm LX)
    (h : PXFc α c (insert (ψ/[s]) Γ)) :
    ∃ β, PXFc β (max c (ψ.complexity + 1)) (insert (∃⁰ ψ) Γ) := by
  set m : ℕ := Semiterm.valm ℕ ![] (id : ℕ → ℕ) s with hm
  set c' : ℕ := max c (ψ.complexity + 1) with hc'
  have hsval : Semiterm.valm ℕ ![] (id : ℕ → ℕ) (nm m : Semiterm LX ℕ 0)
             = Semiterm.valm ℕ ![] (id : ℕ → ℕ) s := by
    rw [valm_nm]
  have h₁ : PXFc α c' (insert (ψ/[s]) (insert (ψ/[nm m]) Γ)) :=
    (h.weakening (Finset.insert_subset_insert _ (Finset.subset_insert _ _))).mono le_rfl
      (le_max_left _ _)
  obtain ⟨b, h₂⟩ := provable_em_cong_gen_x ψ.complexity ![nm m] ![s] ψ le_rfl
    (by intro i; cases i using Fin.cases with
        | zero => simpa using hsval
        | succ j => exact j.elim0)
    (Γ := insert (∼(ψ/[s])) (insert (ψ/[nm m]) Γ))
    (by show (Rew.subst ![nm m] ▹ ψ) ∈ _; simp)
    (by show (∼(Rew.subst ![s] ▹ ψ)) ∈ _; simp)
  have hcc : (((ψ/[s]).complexity : ℕ) + 1 : ℕ∞) ≤ (c' : ℕ∞) := by
    have : (ψ/[s]).complexity = ψ.complexity := by simp
    rw [this]; exact_mod_cast le_max_right _ _
  have hcut := PXFc.cut (ψ/[s]) hcc h₁ (h₂.mono le_rfl (le_max_left _ _))
  exact ⟨_, PXFc.exI ψ m hcut⟩

/-! ## The structural embedding `embedC_LX_gen` (the `axm` discharge abstracted as `hax`).

Mirrors `Embedding.embedC` rule-by-rule, swapping the `ZinftyF.Provable.*` builders for their
`XFreeAx`-tracking `PXFc.*` twins. The `closed` case uses `provable_em_x` (`axL`-only, `XFreeAx`
automatic). All structural builders are `XFreeAx`-safe. The two non-structural cases:

- **`axm`** is abstracted into the hypothesis `hax` (discharged for the concrete `paLX` schema by
  `provable_true_x` on X-free axioms + `metaInduction` on X-induction instances).
- **`exs`** is the one genuinely-hard remaining case: collapsing the closed witness `asgX e t` to its
  numeral value needs a *value-congruent* excluded middle, and for an `X`-atom body that requires
  **Buchholz's value-congruent X-pair axiom** `{Xs, ¬Xt}` (sᴺ=tᴺ; `AX(Z∞)`, lecture notes p.27),
  which our calculus's same-atom `axL` does NOT provide. See `ANALYSIS-2026-06-22-lap16-exs-axLv.md`:
  the faithful fix is to generalise `axL` to value-congruent literal pairs (Boundedness case 1.2,
  p.29, already handles them). Held as a disclosed `sorry` pending that retrofit. -/
theorem embedC_LX_gen {𝓢 : Schema LX}
    (hax : ∀ {Γ : Seq LX} (φ : Form LX), φ ∈ 𝓢 → φ ∈ Γ →
      ∃ c : ℕ, ∀ e : ℕ → ℕ, ∃ α, PXFc α c (Γ.image (fun ψ => asgX e ▹ ψ)))
    {Γ : Seq LX} (d : Derivation2 𝓢 Γ) :
    ∃ c : ℕ, ∀ e : ℕ → ℕ, ∃ α, PXFc α c (Γ.image (fun φ => asgX e ▹ φ)) := by
  induction d with
  | closed Γ φ hp hn =>
    exact ⟨0, fun e => provable_em_x (asgX e ▹ φ) (Finset.mem_image_of_mem _ hp)
      (by have := Finset.mem_image_of_mem (fun φ => asgX e ▹ φ) hn; simpa using this)⟩
  | axm φ hφ hΓ => exact hax φ hφ hΓ
  | verum hΓ =>
    exact ⟨0, fun e => ⟨0, PXFc.verumR
      (by have := Finset.mem_image_of_mem (fun φ => asgX e ▹ φ) hΓ; simpa using this)⟩⟩
  | @and Γ φ ψ h _dp _dq ihp ihq =>
    obtain ⟨c1, ihp⟩ := ihp; obtain ⟨c2, ihq⟩ := ihq
    refine ⟨max c1 c2, fun e => ?_⟩
    obtain ⟨a1, h1⟩ := ihp e; obtain ⟨a2, h2⟩ := ihq e
    rw [Finset.image_insert] at h1 h2
    have h1' := h1.mono (le_refl a1) (le_max_left c1 c2)
    have h2' := h2.mono (le_refl a2) (le_max_right c1 c2)
    have hand := PXFc.andI (asgX e ▹ φ) (asgX e ▹ ψ) h1' h2'
    have hmem : (asgX e ▹ φ ⋏ asgX e ▹ ψ) ∈ Γ.image (fun φ => asgX e ▹ φ) := by
      have := Finset.mem_image_of_mem (fun φ => asgX e ▹ φ) h; simpa using this
    rw [Finset.insert_eq_self.mpr hmem] at hand
    exact ⟨_, hand⟩
  | @or Γ φ ψ h _d ih =>
    obtain ⟨c, ih⟩ := ih
    refine ⟨c, fun e => ?_⟩
    obtain ⟨a, hd⟩ := ih e
    rw [Finset.image_insert, Finset.image_insert] at hd
    have hor := PXFc.orI (asgX e ▹ φ) (asgX e ▹ ψ) hd
    have hmem : (asgX e ▹ φ ⋎ asgX e ▹ ψ) ∈ Γ.image (fun φ => asgX e ▹ φ) := by
      have := Finset.mem_image_of_mem (fun φ => asgX e ▹ φ) h; simpa using this
    rw [Finset.insert_eq_self.mpr hmem] at hor
    exact ⟨_, hor⟩
  | @all Γ φ h _d ih =>
    obtain ⟨c, ih⟩ := ih
    refine ⟨c, fun e => ?_⟩
    have hfam : ∀ n, ∃ a, PXFc a c
        (insert (((asgX e).q ▹ φ)/[nm n]) (Γ.image (fun ψ => asgX e ▹ ψ))) := by
      intro n
      obtain ⟨a, hd⟩ := ih (n :>ₙ e)
      rw [Finset.image_insert] at hd
      have hA : asgX (n :>ₙ e) ▹ (Rewriting.free φ) = ((asgX e).q ▹ φ)/[nm n] := by
        have hRew : (asgX (n :>ₙ e)).comp Rew.free = (Rew.subst ![nm n]).comp (asgX e).q := by
          ext x
          · refine Fin.cases ?_ (fun i => Fin.elim0 i) x
            simp [asgX, Rew.comp_app]
          · simp [asgX, Rew.comp_app]
        show asgX (n :>ₙ e) ▹ (Rew.free ▹ φ) = Rew.subst ![nm n] ▹ ((asgX e).q ▹ φ)
        rw [← TransitiveRewriting.comp_app, ← TransitiveRewriting.comp_app, hRew]
      have hB : (Γ.image Rewriting.shift).image (fun ψ => asgX (n :>ₙ e) ▹ ψ)
          = Γ.image (fun ψ => asgX e ▹ ψ) := by
        have hcompB : (asgX (n :>ₙ e)).comp Rew.shift = asgX e := by
          ext x
          · exact Fin.elim0 x
          · simp [asgX, Rew.comp_app]
        rw [Finset.image_image]
        refine Finset.image_congr (fun ψ _ => ?_)
        show asgX (n :>ₙ e) ▹ (Rew.shift ▹ ψ) = asgX e ▹ ψ
        rw [← TransitiveRewriting.comp_app, hcompB]
      rw [hA, hB] at hd
      exact ⟨a, hd⟩
    choose β hβ using hfam
    have hall := PXFc.allω ((asgX e).q ▹ φ) hβ
    have hmem : (asgX e ▹ (∀⁰ φ)) ∈ Γ.image (fun ψ => asgX e ▹ ψ) := Finset.mem_image_of_mem _ h
    rw [show (asgX e ▹ (∀⁰ φ)) = ∀⁰ ((asgX e).q ▹ φ) by simp] at hmem
    rw [Finset.insert_eq_self.mpr hmem] at hall
    exact ⟨_, hall⟩
  | @exs Γ φ h t _d ih =>
    -- `asgX e ▹ (φ/[t]) = ((asgX e).q ▹ φ)/[asgX e t]` with `asgX e t` closed; collapse to its numeral
    -- value via `PXFc.exI_closed` (value-congruent EM, X-atoms via the `axLv` axiom). The cut bumps the
    -- rank to `max c (φ.complexity + 1)`.
    obtain ⟨c, ih⟩ := ih
    refine ⟨max c (φ.complexity + 1), fun e => ?_⟩
    obtain ⟨a, hd⟩ := ih e
    rw [Finset.image_insert, rew_subst_term (asgX e) φ t] at hd
    obtain ⟨β, hβ⟩ := PXFc.exI_closed ((asgX e).q ▹ φ) (asgX e t) hd
    have hcomp : (((asgX e).q ▹ φ).complexity + 1) = (φ.complexity + 1) := by simp
    rw [hcomp] at hβ
    have hmem : (asgX e ▹ (∃⁰ φ)) ∈ Γ.image (fun ψ => asgX e ▹ ψ) := Finset.mem_image_of_mem _ h
    rw [show (asgX e ▹ (∃⁰ φ)) = ∃⁰ ((asgX e).q ▹ φ) by simp] at hmem
    rw [Finset.insert_eq_self.mpr hmem] at hβ
    exact ⟨_, hβ⟩
  | @wk Δ Γ _d h ih =>
    obtain ⟨c, ih⟩ := ih
    refine ⟨c, fun e => ?_⟩
    obtain ⟨α, hα⟩ := ih e
    exact ⟨α, hα.weakening (Finset.image_subset_image h)⟩
  | @shift Γ _d ih =>
    obtain ⟨c, ih⟩ := ih
    refine ⟨c, fun e => ?_⟩
    have hcomp : (asgX e).comp Rew.shift = asgX (e ∘ Nat.succ) := by
      ext x
      · exact Fin.elim0 x
      · simp [asgX, Rew.comp_app]
    have key : (Γ.image Rewriting.shift).image (fun φ => asgX e ▹ φ)
        = Γ.image (fun φ => asgX (e ∘ Nat.succ) ▹ φ) := by
      rw [Finset.image_image]
      refine Finset.image_congr (fun ψ _ => ?_)
      show asgX e ▹ (Rew.shift ▹ ψ) = asgX (e ∘ Nat.succ) ▹ ψ
      rw [← TransitiveRewriting.comp_app, hcomp]
    rw [key]; exact ih (e ∘ Nat.succ)
  | @cut Γ φ _d _dn ihd ihdn =>
    obtain ⟨c1, ihd⟩ := ihd; obtain ⟨c2, ihdn⟩ := ihdn
    refine ⟨max (φ.complexity + 1) (max c1 c2), fun e => ?_⟩
    obtain ⟨a1, h1⟩ := ihd e; obtain ⟨a2, h2⟩ := ihdn e
    rw [Finset.image_insert] at h1 h2
    rw [show (asgX e ▹ (∼φ)) = ∼(asgX e ▹ φ) by simp] at h2
    have h1' := h1.mono (le_refl a1)
      (show c1 ≤ max (φ.complexity + 1) (max c1 c2) from
        le_trans (le_max_left c1 c2) (le_max_right _ _))
    have h2' := h2.mono (le_refl a2)
      (show c2 ≤ max (φ.complexity + 1) (max c1 c2) from
        le_trans (le_max_right c1 c2) (le_max_right _ _))
    have hc : (((asgX e ▹ φ).complexity + 1 : ℕ) : ℕ∞)
        ≤ ((max (φ.complexity + 1) (max c1 c2) : ℕ) : ℕ∞) := by
      rw [Semiformula.complexity_rew]; exact_mod_cast Nat.le_max_left _ _
    exact ⟨_, PXFc.cut (asgX e ▹ φ) hc h1' h2'⟩

/-! ## The source theory `paLX` = `𝗣𝗔` over the language `LX` (resolves "what is `Z ⊢ TI(X)`?")

Buchholz's `Z = PA(X)`: Peano arithmetic in the language `ℒₒᵣ ∪ {X}` with induction extended to **all**
`LX`-formulas (incl. those mentioning the set variable `X`). Concretely: the `ORing`-embedding image
of the finite `𝗣𝗔⁻` axioms (X-free) together with the full `LX` induction scheme `InductionScheme LX
Set.univ`. A hypothetical proof `Z ⊢ TI_≺(X)` is then a `Derivation2 (↑paLX) {TI prec}`. -/
noncomputable def paLX : Theory LX :=
  Theory.lMap (Language.ORing.embedding LX) 𝗣𝗔⁻ + LO.FirstOrder.Arithmetic.InductionScheme LX Set.univ

/-! ### Discharging `hax` for `paLX` (C₂-axm): X-free base axioms + X-induction instances -/

/-- The `ℕ`-structure on `LX` (`Boundedness.ambient = structLX ∅`), pulled back along the `ORing`
embedding, is exactly the standard `ℒₒᵣ`-structure on `ℕ` (they agree on every ring/order symbol,
and there are no others in `ℒₒᵣ`). The bridge for transferring `ℕ ⊧ₘ τ` to `LitTrue (lMap τ)`. -/
lemma ambient_lMap_eq :
    (Boundedness.ambient.lMap (Language.ORing.embedding LX)) = (inferInstance : Structure ℒₒᵣ ℕ) := by
  apply Structure.ext <;> · funext k r v; rcases r with _|_ <;> rfl

/-- The `ORing`-embedding image of any `ℒₒᵣ`-formula is **X-free** (every relation symbol is an
`ℒₒᵣ`-relation `Sum.inl _`, none is the set variable `X`). -/
lemma xfreeForm_lMap {ξ n} (φ : Semiformula ℒₒᵣ ξ n) :
    XFreeForm (Semiformula.lMap (Language.ORing.embedding LX) φ) := by
  induction φ using Semiformula.rec' with
  | hverum => simp
  | hfalsum => simp
  | hrel r v => rw [Semiformula.lMap_rel]; rw [xfreeForm_rel]; rcases r with _|_ <;> rfl
  | hnrel r v => rw [Semiformula.lMap_nrel]; rw [xfreeForm_nrel]; rcases r with _|_ <;> rfl
  | hand φ ψ ihφ ihψ => simp_all [Semiformula.lMap]
  | hor φ ψ ihφ ihψ => simp_all [Semiformula.lMap]
  | hall φ ih => simp_all
  | hexs φ ih => simp_all

/-- A `𝗣𝗔⁻`-axiom `τ` (true in `ℕ`), embedded into `LX` and closed by `asgX e`, is a TRUE closed
literal under the ambient `ℕ`-model — `provable_true_x`'s side condition for the X-free `axm` case. -/
lemma litTrue_lMap_axiom (τ : Sentence ℒₒᵣ) (hτ : ℕ ⊧ₘ τ) (e : ℕ → ℕ) :
    LitTrue (asgX e ▹ (Rew.emb ▹ Semiformula.lMap (Language.ORing.embedding LX) τ)) := by
  simp only [LitTrue, asgX, Semiformula.eval_rewrite, Semiformula.eval_emb]
  rw [Semiformula.eval_lMap, ambient_lMap_eq]
  rw [models_iff] at hτ
  simpa using hτ

/-- **Value-congruent formula renaming.** A derivation containing the instance `ψ/[s]` yields one
with `ψ/[t]` for any value-equal `t` (`|s| = |t|`), at the same cut rank, `XFreeAx`-preserving — one
`cut` against the value-congruent EM `provable_em_cong_gen_x`. The compound-formula analogue of
`nrel_value_subst`; the bridge from `succInd`'s `nm n + 1` to `metaInduction`'s `nm (n+1)`. -/
theorem PXFc.subst_value_subst {α : Ordinal.{0}} {c : ℕ} {Γ : Seq LX}
    (ψ : SyntacticSemiformula LX 1) (s t : SyntacticTerm LX)
    (hval : Semiterm.valm ℕ ![] (id : ℕ → ℕ) s = Semiterm.valm ℕ ![] (id : ℕ → ℕ) t)
    (hc : (ψ.complexity + 1 : ℕ∞) ≤ (c : ℕ∞))
    (h : PXFc α c (insert (ψ/[s]) Γ)) :
    ∃ β, PXFc β c (insert (ψ/[t]) Γ) := by
  have h₁ : PXFc α c (insert (ψ/[s]) (insert (ψ/[t]) Γ)) :=
    h.weakening (Finset.insert_subset_insert _ (Finset.subset_insert _ _))
  obtain ⟨b, h₂⟩ := provable_em_cong_gen_x ψ.complexity ![t] ![s] ψ le_rfl
    (by intro i; cases i using Fin.cases with
        | zero => simpa using hval.symm
        | succ j => exact j.elim0)
    (Γ := insert (∼(ψ/[s])) (insert (ψ/[t]) Γ))
    (by show (Rew.subst ![t] ▹ ψ) ∈ _; simp)
    (by show (∼(Rew.subst ![s] ▹ ψ)) ∈ _; simp)
  have hcc : (((ψ/[s]).complexity : ℕ) + 1 : ℕ∞) ≤ (c : ℕ∞) := by
    have : (ψ/[s]).complexity = ψ.complexity := by simp
    rw [this]; exact hc
  exact ⟨_, PXFc.cut (ψ/[s]) hcc h₁ (h₂.mono le_rfl (Nat.zero_le c))⟩

/-- **Value-congruent meta-induction (Buchholz Thm 5.5).** Generalises `XFreeCutElim.metaInduction`
to a *value-congruent* successor: the step's `∃`-side `(∼step)/[nm n] = ψ(n) ⋏ ∼ψ(succT n)` may use
any term `succT n` with `|succT n| = n + 1` (e.g. `nm n + 1`, the form `succInd` produces) — not just
the numeral `nm (n+1)`. The chain's `ψ(succT n)` is bridged back to `ψ(nm (n+1))` by
`subst_value_subst`. This is what makes the embedding's X-induction case match Foundation's `succInd`
syntax (where the successor is `#0 + 1`, value- but not syntactically-equal to the next numeral). -/
theorem metaInduction_cong (ψ step : SyntacticSemiformula LX 1) {Γ : Seq LX}
    (succT : ℕ → SyntacticTerm LX)
    (hsval : ∀ n, Semiterm.valm ℕ ![] (id : ℕ → ℕ) (succT n) = n + 1)
    (hstep : ∀ n, (∼step)/[nm n] = (ψ/[nm n]) ⋏ ∼(ψ/[succT n])) :
    ∃ a, PXFc a (ψ.complexity + 1)
      (insert (∼(ψ/[nm 0])) (insert (∃⁰ (∼step)) (insert (∀⁰ ψ) Γ))) := by
  set c : ℕ := ψ.complexity + 1 with hc
  set Δ : Seq LX := insert (∼(ψ/[nm 0])) (insert (∃⁰ (∼step)) Γ) with hΔ
  have hcut : ∀ n, ((ψ/[nm n]).complexity + 1 : ℕ∞) ≤ (c : ℕ∞) := by
    intro n; rw [hc]; simp
  have hcc : (ψ.complexity + 1 : ℕ∞) ≤ (c : ℕ∞) := by rw [hc]; push_cast; exact le_rfl
  have hEx : ∀ n, (∃⁰ (∼step)) ∈ (insert (∼(ψ/[nm n])) (insert (ψ/[succT n]) Δ)) := by
    intro n; rw [hΔ]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_insert_self _ _)))
  have chain : ∀ n, ∃ a, PXFc a c (insert (ψ/[nm n]) Δ) := by
    intro n
    induction n with
    | zero =>
      obtain ⟨a, ha⟩ := provable_em_x (ψ/[nm 0]) (Γ := insert (ψ/[nm 0]) Δ)
        (Finset.mem_insert_self _ _)
        (Finset.mem_insert_of_mem (by rw [hΔ]; exact Finset.mem_insert_self _ _))
      exact ⟨a, ha.mono le_rfl (Nat.zero_le c)⟩
    | succ n ih =>
      obtain ⟨aL, hL0⟩ := ih
      have hL : PXFc aL c (insert (ψ/[nm n]) (insert (ψ/[succT n]) Δ)) :=
        hL0.weakening (Finset.insert_subset_insert _ (Finset.subset_insert _ _))
      obtain ⟨aA, hA0⟩ := provable_em_x (ψ/[nm n])
        (Γ := insert (ψ/[nm n]) (insert (∼(ψ/[nm n])) (insert (ψ/[succT n]) Δ)))
        (Finset.mem_insert_self _ _)
        (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
      obtain ⟨aB, hB0⟩ := provable_em_x (ψ/[succT n])
        (Γ := insert (∼(ψ/[succT n]))
          (insert (∼(ψ/[nm n])) (insert (ψ/[succT n]) Δ)))
        (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))
        (Finset.mem_insert_self _ _)
      have hand := PXFc.andI (c := c) (ψ/[nm n]) (∼(ψ/[succT n]))
        (hA0.mono le_rfl (Nat.zero_le c)) (hB0.mono le_rfl (Nat.zero_le c))
      rw [← hstep n] at hand
      have hexI := PXFc.exI (∼step) n hand
      rw [Finset.insert_eq_self.mpr (hEx n)] at hexI
      have hcutd : PXFc _ c (insert (ψ/[succT n]) Δ) :=
        PXFc.cut (ψ/[nm n]) (hcut n) hL hexI
      obtain ⟨γ, hγ⟩ := PXFc.subst_value_subst ψ (succT n) (nm (n+1))
        (by rw [hsval, valm_nm]) hcc hcutd
      exact ⟨γ, hγ⟩
  choose β hβ using chain
  have hall := PXFc.allω (β := β) ψ (Γ := Δ) hβ
  refine ⟨_, hall.weakening ?_⟩
  rw [hΔ]; intro x hx
  simp only [Finset.mem_insert] at hx ⊢
  tauto

/-- The NNF of Foundation's `succInd ψ` (`ψ(0) → (∀x, ψx → ψ(x+1)) → ∀x ψx`): a disjunction of the
induction-axiom's three Tait components, matching `metaInduction_cong`'s `{∼ψ(0), ∃(∼step), ∀ψ}`. -/
lemma succInd_nnf (ψ : Semiformula LX ℕ 1) :
    succInd ψ = (∼ψ/[(↑(0:ℕ) : Semiterm LX ℕ 0)]) ⋎
      ((∃⁰ ∼((∼ψ/[(#0 : Semiterm LX ℕ 1)]) ⋎ ψ/[(‘(#0 + 1)’ : Semiterm LX ℕ 1)])) ⋎
        (∀⁰ ψ/[(#0 : Semiterm LX ℕ 1)])) := by
  conv_lhs => unfold succInd
  simp only [Semiformula.imp_eq, Semiformula.neg_all]

/-- **C₂-axm: the `axm` discharge for `paLX`.** Each `paLX` axiom appearing in `Γ` yields a
cut-rank-bounded `XFreeAx` `Z∞`-derivation of the image sequent. **X-free base axioms** (`𝗣𝗔⁻` image)
are TRUE closed X-free formulas ⟹ `provable_true_x`. **X-induction instances** (`univCl (succInd ψ)`)
go through `metaInduction` (DISCLOSED `sorry`: the `succInd`/`univCl`/NNF DSL unfolding connecting
`↑(univCl (succInd ψ))` to `metaInduction`'s explicit `{∼ψ(0), ∃(∼step), ∀ψ}` shape). -/
theorem hax_paLX {Γ : Seq LX} (φ : Form LX) (hφ : φ ∈ (paLX : Schema LX)) (hΓ : φ ∈ Γ) :
    ∃ c : ℕ, ∀ e : ℕ → ℕ, ∃ α, PXFc α c (Γ.image (fun ψ => asgX e ▹ ψ)) := by
  obtain ⟨σ, hσ, rfl⟩ := hφ
  rcases hσ with hbase | hind
  · obtain ⟨τ, hτ, rfl⟩ := hbase
    refine ⟨0, fun e => ?_⟩
    have hmod : ℕ ⊧ₘ τ := ModelsTheory.models ℕ hτ
    have htrue := litTrue_lMap_axiom τ hmod e
    have hxf : XFreeForm (asgX e ▹ (Rew.emb ▹ Semiformula.lMap (Language.ORing.embedding LX) τ)) := by
      rw [xfreeForm_rew, xfreeForm_rew]; exact xfreeForm_lMap τ
    exact provable_true_x _ _ le_rfl hxf htrue (Finset.mem_image_of_mem _ hΓ)
  · -- DISCLOSED: X-induction instance `σ = univCl (succInd ψ)` → `metaInduction`. The DSL unfolding
    -- (NNF of `↑(univCl (succInd ψ))` ⟹ `∼ψ(0) ⋎ ∃(∼step) ⋎ ∀ψ`, break by `orI`, apply
    -- `metaInduction` with `step = ψ(x) → ψ(x+1)`) is the next chip.
    sorry

/-- **C₂, the target form.** The embedding of `𝗣𝗔(LX)`-derivations into the `XFreeAx` `Z∞` carrier
`PXFc` is just `embedC_LX_gen` specialised to `𝓢 := ↑paLX`, **once the `axm` discharge `hax` for
`paLX` is supplied** (X-free axioms — `𝗣𝗔⁻` image + X-free induction — via `provable_true_x`;
X-induction instances via `metaInduction`). The structural engine (`embedC_LX_gen`) is already
sorry-free + axiom-clean; only `hax` and the cut-elimination end (`atomCut_x` → `nrel_value_subst`)
remain to make the full `Z ⊢ TI ⟹ ‖≺‖ < ε₀` chain clean. -/
theorem embedC_LX
    (hax : ∀ {Γ : Seq LX} (φ : Form LX), φ ∈ (paLX : Schema LX) → φ ∈ Γ →
      ∃ c : ℕ, ∀ e : ℕ → ℕ, ∃ α, PXFc α c (Γ.image (fun ψ => asgX e ▹ ψ)))
    {Γ : Seq LX} (d : Derivation2 (paLX : Schema LX) Γ) :
    ∃ c : ℕ, ∀ e : ℕ → ℕ, ∃ α, PXFc α c (Γ.image (fun φ => asgX e ▹ φ)) :=
  embedC_LX_gen hax d

end GoodsteinPA.EmbeddingX
