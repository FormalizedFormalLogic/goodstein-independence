module

public import GoodsteinPA.Zef2TC.Basic

@[expose] public section

namespace GoodsteinPA.E1EmbeddingGrind

open LO LO.FirstOrder LO.FirstOrder.ArithmeticTerm ONote
open GoodsteinPA.OperatorZeh GoodsteinPA.OperatorZinfty

/-! ## `Gexp = hardy (ω²)` dominates ℒₒᵣ term values

Every closed-term value under `asg env` is dominated by finitely many iterates of `Gexp`
applied to the sup of the finitely many relevant `env` values. -/

/-! ### `envSup` — the canonical assignment sup -/

/-- Sup of the first `N` values of the assignment. -/
def envSup (env : ℕ → ℕ) (N : ℕ) : ℕ := (Finset.range N).sup env

@[grind .]
lemma envSup_mono_N (env : ℕ → ℕ) {N N' : ℕ} (h : N ≤ N') : envSup env N ≤ envSup env N' :=
  Finset.sup_mono (fun x hx => by simp only [Finset.mem_range] at hx ⊢; omega)

@[grind .]
lemma le_envSup {env : ℕ → ℕ} {N x : ℕ} (hx : x < N) : env x ≤ envSup env N :=
  Finset.le_sup (Finset.mem_range.mpr hx)

/-- Consing a value onto the assignment collapses the sup at `N + 1` to `max n` of the sup at `N`. -/
@[grind .]
lemma envSup_cons_le (env : ℕ → ℕ) (n N : ℕ) : envSup (n :>ₙ env) (N + 1) ≤ max n (envSup env N) := by
  refine Finset.sup_le fun x hx => ?_
  rcases x with _ | y
  · simp
  · have hy : y < N := by simpa using hx
    exact le_trans (by simpa using le_envSup hy) (le_max_right _ _)

/-! ### Term domination -/

/-- Raising a `Gexp`-iterate bound to a larger iterate count / env-sup bound. -/
private lemma raise_bound {c₀ N₀ c N m : ℕ} (env : ℕ → ℕ) (hc : c₀ ≤ c) (hN : N₀ ≤ N)
    (h : m ≤ Gexp^[c₀] (envSup env N₀)) : m ≤ Gexp^[c] (envSup env N) :=
  le_trans h (le_trans (Gexp_iter_le_iter hc _) (Gexp_iter_monotone _ (envSup_mono_N env hN)))

/-- Domination of a binary function value `op a b` (with `op` closed by a `Gexp`-bound such as
`add_le_Gexp_max`/`mul_le_Gexp_max`) given `Gexp`-iterate bounds on `a` and `b`. -/
private lemma func_bound {op : ℕ → ℕ → ℕ} (hop : ∀ a b, op a b ≤ Gexp (max a b))
    (env : ℕ → ℕ) {c₀ N₀ c₁ N₁ a b : ℕ}
    (h₀ : a ≤ Gexp^[c₀] (envSup env N₀)) (h₁ : b ≤ Gexp^[c₁] (envSup env N₁)) :
    op a b ≤ Gexp^[max c₀ c₁ + 1] (envSup env (max N₀ N₁)) := by
  rw [Function.iterate_succ_apply']
  refine le_trans (hop a b) (Gexp_monotone (max_le ?_ ?_))
  · exact raise_bound env (le_max_left c₀ c₁) (le_max_left N₀ N₁) h₀
  · exact raise_bound env (le_max_right c₀ c₁) (le_max_right N₀ N₁) h₁

/-- Every ℒₒᵣ term value under any assignment is bounded by finitely many `Gexp`-iterates of the
env-sup over some finite free-variable bound. -/
lemma term_val_le_Gexp_iter (t : ArithmeticTerm ℕ) :
    ∃ c N : ℕ, ∀ env : ℕ → ℕ,
      Semiterm.gValm ℕ ![] env t ≤ Gexp^[c] (envSup env N) := by
  induction t with
  | bvar x => exact x.elim0
  | fvar x => exact ⟨0, x + 1, fun env => by simpa using le_envSup (Nat.lt_succ_self x)⟩
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
          have hadd : Semiterm.gValm ℕ ![] env (Semiterm.func
              LO.FirstOrder.Language.ORing.Func.add v)
              = Semiterm.gValm ℕ ![] env (v 0) + Semiterm.gValm ℕ ![] env (v 1) := by
            simp only [Semiterm.gValm, Semiterm.val_func]; rfl
          rw [hadd]
          exact func_bound add_le_Gexp_max env (h₀ env) (h₁ env)
      | LO.FirstOrder.Language.ORing.Func.mul, v =>
          obtain ⟨c₀, N₀, h₀⟩ := ih 0
          obtain ⟨c₁, N₁, h₁⟩ := ih 1
          refine ⟨max c₀ c₁ + 1, max N₀ N₁, fun env => ?_⟩
          have hmul : Semiterm.gValm ℕ ![] env (Semiterm.func
              LO.FirstOrder.Language.ORing.Func.mul v)
              = Semiterm.gValm ℕ ![] env (v 0) * Semiterm.gValm ℕ ![] env (v 1) := by
            simp only [Semiterm.gValm, Semiterm.val_func]; rfl
          rw [hmul]
          exact func_bound mul_le_Gexp_max env (h₀ env) (h₁ env)

/-- The standard value of a term closed by `asg env` is its direct `env`-valuation. -/
@[grind =]
lemma stdClosedVal_asg (env : ℕ → ℕ) (t : ArithmeticTerm ℕ) :
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

/-- The standard value of any closed ℒₒᵣ term (closed via `asg env`) is dominated by finitely
many `Gexp`-iterates of the env-sup over some finite free-variable bound. -/
theorem stdClosedVal_asg_le_Gexp_iter (t : ArithmeticTerm ℕ) :
    ∃ c N : ℕ, ∀ env : ℕ → ℕ,
      stdClosedVal (asg env t) ≤ Gexp^[c] (envSup env N) := by
  obtain ⟨c, N, h⟩ := term_val_le_Gexp_iter t
  exact ⟨c, N, fun env => by rw [stdClosedVal_asg]; exact h env⟩

end GoodsteinPA.E1EmbeddingGrind
