module

public import GoodsteinPA.Zef2TC.Basic

@[expose] public section

namespace GoodsteinPA.E1EmbeddingGrind

open LO LO.FirstOrder LO.FirstOrder.ArithmeticTerm ONote
open GoodsteinPA.OperatorZeh GoodsteinPA.OperatorZinfty

/-! ## E-1 block 5 — the GROWTH KIT: `Gexp = hardy (ω²)` dominates ℒₒᵣ term values

The `all` case's residue (and the coming V3 refinement of the master predicate): the env-local
witness budget must be BOUNDED BY A STRUCTURAL FUNCTION of the assignment, or the ω-rule cannot
uniformize the branches (`K_n` unbounded in `n` kills `rel1 f n` domination).  The mechanism
that pays every witness is the control tower: every closed-term value under `asg env` is
dominated by finitely many iterates of the single engine `Gexp := hardy (ω²)` applied to the
sup of the finitely many relevant `env` values. -/

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
theorem term_val_le_Gexp_iter (t : ArithmeticTerm ℕ) :
    ∃ c N : ℕ, ∀ env : ℕ → ℕ,
      Semiterm.gValm ℕ ![] env t ≤ Gexp^[c] (envSup env N) := by
  induction t with
  | bvar x => exact x.elim0
  | fvar x =>
      exact ⟨0, x + 1, fun env => by
        simpa using le_envSup (Nat.lt_succ_self x)⟩
  | func f v ih =>
      match f, v with
      | LO.FirstOrder.Language.ORing.Func.zero, v =>
          refine ⟨0, 0, fun env => ?_⟩
          have hv : Semiterm.gValm ℕ ![] env (Semiterm.func
              LO.FirstOrder.Language.ORing.Func.zero v) = 0 := by
            simp only [Semiterm.gValm, Semiterm.val_func]; rfl
          simp [hv]
      | LO.FirstOrder.Language.ORing.Func.one, v =>
          refine ⟨1, 0, fun env => ?_⟩
          have h1 := iter_le_Gexp_iter 1 (envSup env 0)
          have hv : Semiterm.gValm ℕ ![] env (Semiterm.func
              LO.FirstOrder.Language.ORing.Func.one v) = 1 := by
            simp only [Semiterm.gValm, Semiterm.val_func]; rfl
          omega
      | LO.FirstOrder.Language.ORing.Func.add, v =>
          obtain ⟨c₀, N₀, h₀⟩ := ih 0
          obtain ⟨c₁, N₁, h₁⟩ := ih 1
          refine ⟨max c₀ c₁ + 1, max N₀ N₁, fun env => ?_⟩
          have hb₀ : Semiterm.gValm ℕ ![] env (v 0)
              ≤ Gexp^[max c₀ c₁] (envSup env (max N₀ N₁)) :=
            le_trans (h₀ env) (le_trans
              (Gexp_iter_le_iter (le_max_left c₀ c₁) _)
              (Gexp_iter_monotone _ (envSup_mono_N env (le_max_left N₀ N₁))))
          have hb₁ : Semiterm.gValm ℕ ![] env (v 1)
              ≤ Gexp^[max c₀ c₁] (envSup env (max N₀ N₁)) :=
            le_trans (h₁ env) (le_trans
              (Gexp_iter_le_iter (le_max_right c₀ c₁) _)
              (Gexp_iter_monotone _ (envSup_mono_N env (le_max_right N₀ N₁))))
          have hadd : Semiterm.gValm ℕ ![] env (Semiterm.func
              LO.FirstOrder.Language.ORing.Func.add v)
              = Semiterm.gValm ℕ ![] env (v 0) + Semiterm.gValm ℕ ![] env (v 1) := by
            simp only [Semiterm.gValm, Semiterm.val_func]; rfl
          rw [hadd, Function.iterate_succ_apply']
          refine le_trans (add_le_Gexp_max _ _) (Gexp_monotone ?_)
          exact max_le hb₀ hb₁
      | LO.FirstOrder.Language.ORing.Func.mul, v =>
          obtain ⟨c₀, N₀, h₀⟩ := ih 0
          obtain ⟨c₁, N₁, h₁⟩ := ih 1
          refine ⟨max c₀ c₁ + 1, max N₀ N₁, fun env => ?_⟩
          have hb₀ : Semiterm.gValm ℕ ![] env (v 0)
              ≤ Gexp^[max c₀ c₁] (envSup env (max N₀ N₁)) :=
            le_trans (h₀ env) (le_trans
              (Gexp_iter_le_iter (le_max_left c₀ c₁) _)
              (Gexp_iter_monotone _ (envSup_mono_N env (le_max_left N₀ N₁))))
          have hb₁ : Semiterm.gValm ℕ ![] env (v 1)
              ≤ Gexp^[max c₀ c₁] (envSup env (max N₀ N₁)) :=
            le_trans (h₁ env) (le_trans
              (Gexp_iter_le_iter (le_max_right c₀ c₁) _)
              (Gexp_iter_monotone _ (envSup_mono_N env (le_max_right N₀ N₁))))
          have hmul : Semiterm.gValm ℕ ![] env (Semiterm.func
              LO.FirstOrder.Language.ORing.Func.mul v)
              = Semiterm.gValm ℕ ![] env (v 0) * Semiterm.gValm ℕ ![] env (v 1) := by
            simp only [Semiterm.gValm, Semiterm.val_func]; rfl
          rw [hmul, Function.iterate_succ_apply']
          refine le_trans (mul_le_Gexp_max _ _) (Gexp_monotone ?_)
          exact max_le hb₀ hb₁

/-- Bridge: the `atomTrue`-evaluator value of the `asg`-closed term is the direct
`env`-valuation. -/
theorem stdClosedVal_asg (env : ℕ → ℕ) (t : ArithmeticTerm ℕ) :
    stdClosedVal (asg env t) = Semiterm.gValm ℕ ![] env t := by
  show Semiterm.gVal _ (fun _ => 0) (fun _ => 0) (Rew.rewrite (fun x => nm (env x)) t) = _
  -- unfold the `gVal`/`gValm` shims so `rw` sees `Semiterm.val`; upstream's `val_rewrite` now emits
  -- the free-var assignment in `∘`-composition form, so normalize it back with `Function.comp_def`
  unfold Semiterm.gVal Semiterm.gValm
  rw [Semiterm.val_rewrite]
  simp only [Function.comp_def]
  have he : (fun _ => 0 : Fin 0 → ℕ) = ![] := funext (fun x => x.elim0)
  rw [he]
  congr 1
  funext x
  exact ArithmeticTerm.valm_nm (env x) (fun _ => 0)

/-- **The `exs`/V3 witness gate**: the closed witness's standard value is dominated by
structurally many `Gexp`-iterates of the env-sup. -/
theorem stdClosedVal_asg_le_Gexp_iter (t : ArithmeticTerm ℕ) :
    ∃ c N : ℕ, ∀ env : ℕ → ℕ,
      stdClosedVal (asg env t) ≤ Gexp^[c] (envSup env N) := by
  obtain ⟨c, N, h⟩ := term_val_le_Gexp_iter t
  exact ⟨c, N, fun env => by rw [stdClosedVal_asg]; exact h env⟩

end GoodsteinPA.E1EmbeddingGrind
