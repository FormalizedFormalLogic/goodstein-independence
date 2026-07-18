/-
# `wip/TruthSem.lean` — Buchholz's X-positive truth semantics `⊨^γ` (lap-13, Boundedness step 1)

The light self-contained layer the Boundedness theorem (Buchholz Thm 5.4) sits on:
- `rk ≺ n = |n|_≺` (the ≺-rank), via mathlib `IsWellFounded.rank`;
- `orderType ≺ = ‖≺‖ = sup{|n|_≺ + 1}`;
- `levelSet ≺ γ = {n : |n|_≺ < γ}` (the `X`-interpretation `U^γ`);
- `models ≺ γ A = ⊨^γ A` and `Sat ≺ γ Γ` (the sequent reading), via the explicit `structLX` carrier
  (NOT an ambient instance — `γ` must vary in the Boundedness induction; see
  `ANALYSIS-2026-06-22-lap13-boundedness-design.md`);
- the **X-free invariance** bridge: an `ℒₒᵣ`-formula's truth is independent of the `X`-set, so a true
  X-free leaf of a derivation is `⊨^γ` for every `γ`. This is the reusable bridge from `axTrue` leaves
  to the truth semantics.
-/
import GoodsteinPA.ZinftyGen
import GoodsteinPA.LangX
import Mathlib.SetTheory.Ordinal.Rank
import GoodsteinPA.Compat

namespace GoodsteinPA.TruthSem

open LO LO.FirstOrder
open GoodsteinPA.ZinftyGen GoodsteinPA.LangX

variable (lt : ℕ → ℕ → Prop) [IsWellFounded ℕ lt]

/-- `|n|_≺` — the ≺-rank, `sup{|i|_≺ + 1 : i ≺ n}` (mathlib `IsWellFounded.rank`). -/
noncomputable def rk (n : ℕ) : Ordinal.{0} := IsWellFounded.rank lt n

theorem rk_lt_of_rel {a b : ℕ} (h : lt a b) : rk lt a < rk lt b :=
  IsWellFounded.rank_lt_of_rel h

/-- `|n|_≺ ≤ γ` whenever every `≺`-predecessor has rank `< γ` (the `Prog`/case-2 rank step:
`|n|_≺ = sup{|m|_≺+1 : m ≺ n}`). -/
theorem rk_le_of_forall {γ : Ordinal.{0}} {n : ℕ} (h : ∀ m, lt m n → rk lt m < γ) :
    rk lt n ≤ γ := by
  rw [rk, IsWellFounded.rank_eq]
  apply Ordinal.iSup_le
  rintro ⟨m, hm⟩
  exact Order.succ_le_of_lt (h m hm)

/-- `‖≺‖` — the order type, `sup{|n|_≺ + 1}`. -/
noncomputable def orderType : Ordinal.{0} := ⨆ n : ℕ, Order.succ (rk lt n)

/-- Every rank is `< ‖≺‖.succ`; more usefully, `|n|_≺ < γ` for all `n` forces `‖≺‖ ≤ γ`. -/
theorem orderType_le_of_forall {γ : Ordinal.{0}} (h : ∀ n, rk lt n < γ) : orderType lt ≤ γ := by
  refine Ordinal.iSup_le ?_
  intro n
  exact Order.succ_le_of_lt (h n)

/-- `U^γ = {n : |n|_≺ < γ}` — the level set interpreting `X` at level `γ`. -/
def levelSet (γ : Ordinal.{0}) : ℕ → Prop := fun n => rk lt n < γ

/-- `⊨^γ A :⟺ (ℕ, U^γ) ⊨ A` — truth in the `structLX (U^γ)` carrier (explicit structure). -/
noncomputable def models (γ : Ordinal.{0}) (A : Form LX) : Prop :=
  GoodsteinPA.Compat.gEval (structLX (levelSet lt γ)) ![] id A

/-- `⊨^γ {A₁,…,A_k} :⟺ ⊨^γ A₁ ∨ … ∨ ⊨^γ A_k` (the Tait sequent reads as a disjunction). -/
noncomputable def Sat (γ : Ordinal.{0}) (Γ : Seq LX) : Prop := ∃ A ∈ Γ, models lt γ A

theorem Sat.intro {γ : Ordinal.{0}} {Γ : Seq LX} {A : Form LX}
    (hA : A ∈ Γ) (h : models lt γ A) : Sat lt γ Γ := ⟨A, hA, h⟩

/-! ## `⊨^γ` on connectives

The Tait-formula recursion the Boundedness induction reads off: `⊨^γ` commutes with `⋏`/`⋎` and the
quantifiers turn into the numeral family (matching the ω-rule premise shape `φ/[nm n]`). -/

/-- The numeral `nm n` denotes `n` in `structLX S` (its `ℒₒᵣ`-fragment is the standard model). -/
theorem val_nm (S : ℕ → Prop) (n : ℕ) :
    GoodsteinPA.Compat.gVal (structLX S) ![] (id : ℕ → ℕ) (nm n) = n := by
  letI inst : Structure LX ℕ := structLX S
  haveI : Structure.Zero LX ℕ := ⟨rfl⟩
  haveI : Structure.One LX ℕ := ⟨rfl⟩
  haveI : Structure.Add LX ℕ := ⟨fun _ _ => rfl⟩
  simp [nm]

/-- The 1-ary substitution vector `![nm n]` evaluates to `![n]` in `structLX S`. -/
theorem subst_vec (S : ℕ → Prop) (n : ℕ) :
    (fun i => GoodsteinPA.Compat.gVal (structLX S) ![] id (![nm n] i)) = ![n] := by
  funext i; refine Fin.cases ?_ (fun j => j.elim0) i; simp [val_nm]

@[simp] theorem models_and (γ : Ordinal.{0}) (φ ψ : Form LX) :
    models lt γ (φ ⋏ ψ) ↔ models lt γ φ ∧ models lt γ ψ := by unfold models; simp

@[simp] theorem models_or (γ : Ordinal.{0}) (φ ψ : Form LX) :
    models lt γ (φ ⋎ ψ) ↔ models lt γ φ ∨ models lt γ ψ := by unfold models; simp

theorem models_all (γ : Ordinal.{0}) (φ : SyntacticSemiformula LX 1) :
    models lt γ (∀⁰ φ) ↔ ∀ n : ℕ, models lt γ (φ/[nm n]) := by
  unfold models; simp only [Semiformula.eval_all, Semiformula.eval_substs, subst_vec, Function.comp_def]

theorem models_ex (γ : Ordinal.{0}) (φ : SyntacticSemiformula LX 1) :
    models lt γ (∃⁰ φ) ↔ ∃ n : ℕ, models lt γ (φ/[nm n]) := by
  unfold models; simp only [Semiformula.eval_ex, Semiformula.eval_substs, subst_vec, Function.comp_def]

/-! ## X-free invariance

The `ℒₒᵣ`-reduct of `structLX S` is the standard ℕ-model, independent of `S` — because the `ORing`
embedding sends every `ℒₒᵣ` symbol to the `Sum.inl` side, which `structLX` interprets via the standard
model regardless of `S`. Hence a formula lifted from `ℒₒᵣ` has `S`-independent (so `γ`-independent)
truth: the bridge from a true X-free `axTrue` leaf to `⊨^γ`. -/

/-- The `ℒₒᵣ`-reduct of `structLX S` is the standard model, for every `S`. -/
theorem lMap_structLX (S : ℕ → Prop) :
    (structLX S).lMap (Language.ORing.embedding LX) = (inferInstance : Structure ℒₒᵣ ℕ) := by
  apply Structure.ext
  · funext k f v
    match k, f with
    | 0, Language.Zero.zero => rfl
    | 0, Language.One.one => rfl
    | 2, Language.Add.add => rfl
    | 2, Language.Mul.mul => rfl
  · funext k r v
    match k, r with
    | 2, Language.Eq.eq => rfl
    | 2, Language.LT.lt => rfl

/-- **X-free invariance.** A formula lifted from `ℒₒᵣ` is `⊨^γ`-true iff it is true in the standard
ℕ-model — independent of `γ`. -/
theorem models_lMap (γ : Ordinal.{0}) (φ₀ : SyntacticFormula ℒₒᵣ) :
    models lt γ (Semiformula.lMap (Language.ORing.embedding LX) φ₀)
      ↔ GoodsteinPA.Compat.gEvalm ℕ ![] (id : ℕ → ℕ) φ₀ := by
  unfold models
  rw [Semiformula.eval_lMap, lMap_structLX]

end GoodsteinPA.TruthSem
