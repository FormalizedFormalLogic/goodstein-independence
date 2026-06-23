/-
# `DescentConstruction.lean` — wall C: the M-internal `Mlt`-descent sequence (COMPLETE, axiom-clean)

The lone wall `DescentSemantic.no_min_descent_absurd_of_goodstein`'s `hCD` needs an `M`-internal,
`LX`-definable descending sequence built from `no_min`/`ha₀`. This file constructs it over `M`'s
`ℒₒᵣ`-reduct (`reductORing`, `⊧ 𝗜𝚺₁`) using Foundation's HFS `Seq` coding. **Sorry-free** (lap 35):

- `IsDescent f a₀ W` — `W` codes a finite `Mlt`-descending sequence through `¬MX` from `a₀`.
- `isDescent_iff_mem` — the membership (`Seq`-graph) form of `IsDescent`: the `X`-atom sits on a *bound
  variable*, not a `znth`-term — the key simplification for the definability.
- `descent_base` / `descent_extend` — the base (length 1) and the canonical one-step extension (via
  `DescentSemantic.descent_step`, the `lx_least_number` selector). Real math content.
- `lxDef_exists` / `lxDef2_and` — binary `LX`-definability combinators (`∃`-closure, conjunction).
- `skel_lxDef` / `descentMlt_lxDef` / `xclause_lxDef` — pieces A/B/C: the `LX`-definability of the
  `ℒₒᵣ`-skeleton (`Seq`/`∈`/`lh`), the `Mlt`-descent clause (`prec` atom), and the `¬MX` clause
  (`Xsym` atom). Built directly from Foundation's `memRelOpr`/`seqDef`/`lhDef` + `lMap Φ` to the reduct.
- `descent_seq_exists` — `∀ k, ∃ W, IsDescent W ∧ lh W = k+1`, by `lx_succ_induction`; its definability
  hypothesis `hDdef` (`D(k) := ∃ W, IsDescent W ∧ lh W = k+1` is `LX`-definable) is **DISCHARGED**
  (`∃ W, A∧B∧C`, `lxDef2_and` + `lxDef_exists`). This is wall C's descent-existence brick, ready to
  feed the βₖ slow-down (Rathjen §3 Thm 3.5) toward `hCD`.
-/
import GoodsteinPA.DescentSemantic
import Mathlib.Tactic.FinCases

namespace GoodsteinPA.DescentConstruction

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open GoodsteinPA GoodsteinPA.LangX GoodsteinPA.EmbeddingX GoodsteinPA.DescentSemantic
open GoodsteinPA.DescentLift (Φ)

variable {M : Type} [Nonempty M] [Structure LX M]

/-- `W` codes a finite `Mlt`-descending sequence through the `¬MX` set, starting at `a₀`. -/
def IsDescent [ORingStructure M] [M ⊧ₘ* 𝗜𝚺₁] (f : ℕ → M) (a₀ : M) (W : M) : Prop :=
  Seq W ∧ znth W 0 = a₀ ∧
    (∀ i, i + 1 < lh W → Mlt f (znth W (i + 1)) (znth W i)) ∧
    (∀ i, i < lh W → ¬ MX (znth W i))

/-- **Membership form of `IsDescent`** (the `Seq`-graph rendering of the `znth`-clauses). Over `M`'s
`ℒₒᵣ`-reduct, `IsDescent f a₀ W` is equivalent to the `∈`/pairing statement
`Seq W ∧ ⟪0,a₀⟫∈W ∧ (∀ i x x', ⟪i,x⟫∈W → ⟪i+1,x'⟫∈W → Mlt f x' x) ∧ (∀ i x, ⟪i,x⟫∈W → ¬MX x)`.
This is the key simplification for `hDdef`: the `X`-atom now sits on a *bound variable* `x` (not a
`znth`-function-term), so the `LX`-definability is a bounded `∀` over the reduct-definable `∈`-guard with
a primitive `Xsym`-atom — no function-graph plumbing. Requires `0 < lh W` (always true here: `lh W = k+1`). -/
theorem isDescent_iff_mem [ORingStructure M] [M ⊧ₘ* 𝗜𝚺₁] (f : ℕ → M) (a₀ W : M) (hpos : 0 < lh W) :
    IsDescent f a₀ W ↔
      (Seq W ∧ ⟪(0 : M), a₀⟫ ∈ W ∧
        (∀ i x x' : M, ⟪i, x⟫ ∈ W → ⟪i + 1, x'⟫ ∈ W → Mlt f x' x) ∧
        (∀ i x : M, ⟪i, x⟫ ∈ W → ¬ MX x)) := by
  constructor
  · rintro ⟨hSeq, hz0, hdesc, hnotMX⟩
    refine ⟨hSeq, ?_, ?_, ?_⟩
    · -- `⟪0,a₀⟫∈W` from `znth W 0 = a₀` and `0 < lh W`
      have := hSeq.znth hpos; rwa [hz0] at this
    · -- descent, membership form
      intro i x x' hix hix'
      have hi1 : i + 1 < lh W := hSeq.lt_lh_of_mem hix'
      rw [← hSeq.znth_eq_of_mem hix, ← hSeq.znth_eq_of_mem hix']
      exact hdesc i hi1
    · -- `¬MX`, membership form
      intro i x hix
      rw [← hSeq.znth_eq_of_mem hix]
      exact hnotMX i (hSeq.lt_lh_of_mem hix)
  · rintro ⟨hSeq, hz0, hdesc, hnotMX⟩
    refine ⟨hSeq, ?_, ?_, ?_⟩
    · exact hSeq.znth_eq_of_mem hz0
    · -- descent, `znth` form
      intro i hi1
      have hi : i < lh W := lt_of_le_of_lt (by simp) hi1
      exact hdesc i (znth W i) (znth W (i + 1)) (hSeq.znth hi) (hSeq.znth hi1)
    · -- `¬MX`, `znth` form
      intro i hi
      exact hnotMX i (znth W i) (hSeq.znth hi)

/-! ### Binary `LX`-definability combinators (for `hDdef`)

`hDdef` asks for the `LX`-definability of `D(k) := ∃ W, IsDescent f a₀ W ∧ lh W = k+1`. These generalize
the unary combinators in `DescentSemantic` to a *binary* predicate `R W k` plus an `∃`-closure on the
first variable, matching the `∃ W` shape. -/

/-- **`∃`-closure on the first variable.** From a binary `LX`-definable `R W k` (by `β : … ℕ 2`,
`#0 ↦ W`, `#1 ↦ k`), the predicate `fun k ↦ ∃ W, R W k` is `LX`-definable by `∃⁰ β`. -/
theorem lxDef_exists {R : M → M → Prop}
    (hR : ∃ e : ℕ → M, ∃ β : Semiformula LX ℕ 2, ∀ W k, R W k ↔ Semiformula.Evalm M ![W, k] e β) :
    ∃ e : ℕ → M, ∃ φ : Semiformula LX ℕ 1,
      ∀ k, (∃ W, R W k) ↔ Semiformula.Evalm M ![k] e φ := by
  rcases hR with ⟨e, β, hβ⟩
  refine ⟨e, ∃⁰ β, fun k => ?_⟩
  rw [Semiformula.eval_ex]
  exact exists_congr fun W => hβ W k

/-- **Binary `LX`-definability is closed under conjunction.** (Even/odd free-assignment merge, as in the
unary `lxDef_and`.) -/
theorem lxDef2_and {R S : M → M → Prop}
    (hR : ∃ e : ℕ → M, ∃ β : Semiformula LX ℕ 2, ∀ W k, R W k ↔ Semiformula.Evalm M ![W, k] e β)
    (hS : ∃ e : ℕ → M, ∃ β : Semiformula LX ℕ 2, ∀ W k, S W k ↔ Semiformula.Evalm M ![W, k] e β) :
    ∃ e : ℕ → M, ∃ β : Semiformula LX ℕ 2,
      ∀ W k, (R W k ∧ S W k) ↔ Semiformula.Evalm M ![W, k] e β := by
  rcases hR with ⟨eR, βR, hβR⟩
  rcases hS with ⟨eS, βS, hβS⟩
  refine ⟨fun n => if n % 2 = 0 then eR (n / 2) else eS (n / 2),
    (Rew.rewriteMap (fun n => 2 * n) ▹ βR) ⋏ (Rew.rewriteMap (fun n => 2 * n + 1) ▹ βS),
    fun W k => ?_⟩
  rw [LogicalConnective.HomClass.map_and, Semiformula.eval_rewriteMap, Semiformula.eval_rewriteMap]
  apply and_congr
  · have heqR : (fun z : ℕ => (fun n => if n % 2 = 0 then eR (n / 2) else eS (n / 2)) (2 * z)) = eR := by
      funext z; have h1 : (2 * z) % 2 = 0 := by omega
      have h2 : (2 * z) / 2 = z := by omega
      simp [h1, h2]
    rw [heqR]; exact hβR W k
  · have heqS : (fun z : ℕ => (fun n => if n % 2 = 0 then eR (n / 2) else eS (n / 2)) (2 * z + 1)) = eS := by
      funext z; have h1 : ¬ (2 * z + 1) % 2 = 0 := by omega
      have h2 : (2 * z + 1) / 2 = z := by omega
      simp [h1, h2]
    rw [heqS]; exact hβS W k

section
variable [Structure.Eq LX M] (hM : M ⊧ₘ* (paLX : Theory LX)) (f : ℕ → M)

/-- **Base case.** The length-1 sequence `⟨a₀⟩` is a descent (descent/`¬MX` clauses: only the seed). -/
theorem descent_base {a₀ : M} (ha₀ : ¬ MX a₀) :
    letI : ORingStructure M := ReductModel.reductORing
    haveI : M ⊧ₘ* (𝗜𝚺₁ : Theory ℒₒᵣ) := ReductModel.reduct_models_isigma1 hM
    IsDescent f a₀ ((∅ : M) ⁀' a₀) ∧ lh ((∅ : M) ⁀' a₀) = 1 := by
  letI : ORingStructure M := ReductModel.reductORing
  haveI : M ⊧ₘ* (𝗜𝚺₁ : Theory ℒₒᵣ) := ReductModel.reduct_models_isigma1 hM
  have hSeq : Seq ((∅ : M) ⁀' a₀) := (seq_empty).seqCons a₀
  have hlh : lh ((∅ : M) ⁀' a₀) = 1 := by
    rw [Seq.lh_seqCons a₀ seq_empty, lh_empty, zero_add]
  refine ⟨⟨hSeq, ?_, ?_, ?_⟩, hlh⟩
  · -- `znth W 0 = a₀`
    have : ⟪(0 : M), a₀⟫ ∈ (∅ : M) ⁀' a₀ := by
      have := Seq.mem_seqCons (∅ : M) a₀
      rwa [lh_empty] at this
    exact Seq.znth_eq_of_mem hSeq this
  · -- descent clause: `i + 1 < 1` is impossible
    intro i hi; rw [hlh] at hi
    exact absurd (lt_one_iff_eq_zero.mp hi) (lt_of_le_of_lt (by simp) (lt_add_one i)).ne'
  · -- `¬MX` clause: only `i = 0`
    intro i hi; rw [hlh] at hi
    have : i = 0 := lt_one_iff_eq_zero.mp hi
    subst this
    have : ⟪(0 : M), a₀⟫ ∈ (∅ : M) ⁀' a₀ := by
      have := Seq.mem_seqCons (∅ : M) a₀
      rwa [lh_empty] at this
    rwa [Seq.znth_eq_of_mem hSeq this]

/-- **One-step extension (the canonical descent step).** Given a descent `W` of length `k+1`, append the
`<`-least `¬MX` element `Mlt`-below its last entry (`DescentSemantic.descent_step`). -/
theorem descent_extend
    (no_min : ∀ x : M, ¬ MX x → ∃ y, Mlt f y x ∧ ¬ MX y)
    {a₀ : M} {W : M} {k : M}
    (hW : letI : ORingStructure M := ReductModel.reductORing
          haveI : M ⊧ₘ* (𝗜𝚺₁ : Theory ℒₒᵣ) := ReductModel.reduct_models_isigma1 hM
          IsDescent f a₀ W)
    (hk : letI : ORingStructure M := ReductModel.reductORing
          haveI : M ⊧ₘ* (𝗜𝚺₁ : Theory ℒₒᵣ) := ReductModel.reduct_models_isigma1 hM
          lh W = k + 1) :
    letI : ORingStructure M := ReductModel.reductORing
    haveI : M ⊧ₘ* (𝗜𝚺₁ : Theory ℒₒᵣ) := ReductModel.reduct_models_isigma1 hM
    ∃ W', IsDescent f a₀ W' ∧ lh W' = k + 2 := by
  letI : ORingStructure M := ReductModel.reductORing
  haveI hI : M ⊧ₘ* (𝗜𝚺₁ : Theory ℒₒᵣ) := ReductModel.reduct_models_isigma1 hM
  haveI hPA : M ⊧ₘ* (𝗣𝗔⁻ : Theory ℒₒᵣ) := models_of_subtheory (ReductModel.reduct_models_PA hM)
  obtain ⟨hSeq, hz0, hdesc, hnotMX⟩ := hW
  -- last entry `aₖ = znth W k`, with `¬MX aₖ`
  have hk_lt : k < lh W := by rw [hk]; exact lt_add_one k
  set aₖ := znth W k with haₖ
  have hnotMXk : ¬ MX aₖ := hnotMX k hk_lt
  -- canonical `Mlt`-smaller `¬MX` element below `aₖ`
  obtain ⟨y, ⟨hylt, hyMX⟩, _hleast⟩ := descent_step hM f no_min hnotMXk
  -- `znth` preservation: old entries survive the `seqCons`, and the new last entry is `y`.
  have hpreserve : ∀ i, i < lh W → znth (W ⁀' y) i = znth W i := fun i hi =>
    Seq.znth_eq_of_mem (hSeq.seqCons y) (Seq.subset_seqCons W y (hSeq.znth hi))
  have hlast : znth (W ⁀' y) (lh W) = y :=
    Seq.znth_eq_of_mem (hSeq.seqCons y) (Seq.mem_seqCons W y)
  have hlhW' : lh (W ⁀' y) = lh W + 1 := Seq.lh_seqCons y hSeq
  refine ⟨W ⁀' y, ⟨hSeq.seqCons y, ?_, ?_, ?_⟩, ?_⟩
  · -- `znth (W ⁀' y) 0 = a₀`
    have h0 : (0 : M) < lh W := lt_of_le_of_lt (by simp) (by rw [hk]; exact lt_add_one k)
    rw [hpreserve 0 h0, hz0]
  · -- descent clause: split `i + 1 < lh W` vs `i + 1 = lh W`
    intro i hi
    rw [hlhW'] at hi
    rcases (lt_succ_iff_le.mp hi).lt_or_eq with hlt | heq
    · -- both entries are old
      have hi' : i < lh W := lt_of_le_of_lt (le_of_lt (lt_add_one i)) hlt
      rw [hpreserve (i + 1) hlt, hpreserve i hi']
      exact hdesc i hlt
    · -- `i + 1 = lh W`, so `i = k` and the new entry `y` sits below `aₖ`
      have hi_lt : i < lh W := heq ▸ lt_add_one i
      have hieq : i = k := add_right_cancel (heq.trans hk)
      rw [heq, hlast, hpreserve i hi_lt, hieq]
      exact hylt
  · -- `¬MX` clause: split `i < lh W` vs `i = lh W`
    intro i hi
    rw [hlhW'] at hi
    rcases (lt_succ_iff_le.mp hi).lt_or_eq with hlt | heq
    · rw [hpreserve i hlt]; exact hnotMX i hlt
    · rw [heq, hlast]; exact hyMX
  · rw [hlhW', hk, add_assoc, one_add_one_eq_two]

/-- **Piece C of `hDdef`: the `X`-clause `∀ i x, ⟪i,x⟫∈W → ¬MX x` is binary-`LX`-definable.** The novel
content: the `∈`-guard is `ℒₒᵣ`-on-reduct (`memRelOpr`, `lMap Φ`), the consequent is the primitive
`Xsym`-atom on the bound `x`. Built directly: `β := ∀⁰ ∀⁰ (lMap Φ (memRelOpr ![#2,#1,#0]) 🡒 ∼Xsym ![#0])`
(bvars after wrapping: `#0=x, #1=i, #2=W, #3=k`). Eval: `eval_lMap` carries the guard to the reduct
`inst.lMap Φ = standardModel reductORing` where `eval_memRel` reads it as `⟪i,x⟫∈W`. -/
theorem xclause_lxDef :
    letI : ORingStructure M := ReductModel.reductORing
    haveI : M ⊧ₘ* (𝗜𝚺₁ : Theory ℒₒᵣ) := ReductModel.reduct_models_isigma1 hM
    ∃ e : ℕ → M, ∃ β : Semiformula LX ℕ 2,
      ∀ W k : M, (∀ i x : M, ⟪i, x⟫ ∈ W → ¬ MX x) ↔ Semiformula.Evalm M ![W, k] e β := by
  letI oM : ORingStructure M := ReductModel.reductORing
  haveI hI : M ⊧ₘ* (𝗜𝚺₁ : Theory ℒₒᵣ) := ReductModel.reduct_models_isigma1 hM
  have hred := ReductModel.reduct_eq_standardModel (M := M)
  set e : ℕ → M := fun _ => Classical.arbitrary M with he
  refine ⟨e, ∀⁰ ∀⁰ ((Semiformula.lMap Φ (memRelOpr.operator ![#2, #1, #0])) 🡒
      ∼(Semiformula.rel Xsym ![#0])), fun W k => ?_⟩
  -- guard-eval: the `ℒₒᵣ` membership operator (carried to the reduct) reads as `⟪i,x⟫∈W`.
  have hguard : ∀ x i : M,
      Semiformula.Evalm M ![x, i, W, k] e (Semiformula.lMap Φ (memRelOpr.operator ![#2, #1, #0]))
        ↔ ⟪i, x⟫ ∈ W := by
    intro x i
    rw [Semiformula.eval_lMap, hred, Semiformula.eval_operator]
    have hv : (fun j : Fin 3 =>
        Semiterm.val (@standardModel M oM) ![x, i, W, k] e (![(#2 : Semiterm ℒₒᵣ ℕ 4), #1, #0] j))
        = ![W, i, x] := by
      funext j; fin_cases j <;> simp [Semiterm.val_bvar]
    simp only [hv, eval_memRel]
  simp only [Semiformula.eval_all, LogicalConnective.HomClass.map_imply,
    LogicalConnective.HomClass.map_neg, Semiformula.eval_rel₁, Semiterm.val_bvar,
    Matrix.cons_val_zero]
  constructor
  · intro hC i x hg
    exact hC i x ((hguard x i).mp hg)
  · intro hR i x hmem
    exact hR i x ((hguard x i).mpr hmem)

/-- **Piece B of `hDdef`: the `Mlt`-descent clause `∀ i x x', ⟪i,x⟫∈W → ⟪i+1,x'⟫∈W → Mlt f x' x` is
binary-`LX`-definable.** Same `∀⁰`-over-`∈`-guards shape as piece C, but with the (X-free, fvar-free)
`prec` atom in place of `Xsym`. Built directly: two `ℒₒᵣ`-on-reduct membership guards (`memRelOpr`,
`lMap Φ`; the second on the successor term `‘#2+1’`) and `prec ⇜ ![#0,#1]` (`prec` is fvar-free, so the
free assignment is irrelevant — `eval_iff_of_funEqOn`). Bvars after wrapping: `#0=x', #1=x, #2=i, #3=W,
#4=k`. -/
theorem descentMlt_lxDef :
    letI : ORingStructure M := ReductModel.reductORing
    haveI : M ⊧ₘ* (𝗜𝚺₁ : Theory ℒₒᵣ) := ReductModel.reduct_models_isigma1 hM
    ∃ e : ℕ → M, ∃ β : Semiformula LX ℕ 2,
      ∀ W k : M, (∀ i x x' : M, ⟪i, x⟫ ∈ W → ⟪i + 1, x'⟫ ∈ W → Mlt f x' x)
        ↔ Semiformula.Evalm M ![W, k] e β := by
  letI oM : ORingStructure M := ReductModel.reductORing
  haveI hI : M ⊧ₘ* (𝗜𝚺₁ : Theory ℒₒᵣ) := ReductModel.reduct_models_isigma1 hM
  have hred := ReductModel.reduct_eq_standardModel (M := M)
  set e : ℕ → M := fun _ => Classical.arbitrary M with he
  refine ⟨e, ∀⁰ ∀⁰ ∀⁰ (
      (Semiformula.lMap Φ (memRelOpr.operator ![#3, #2, #1])) 🡒
      (Semiformula.lMap Φ (memRelOpr.operator ![#3, ‘(#2 + 1)’, #0])) 🡒
      (Thm56.prec ⇜ ![#0, #1])), fun W k => ?_⟩
  -- guard 1: `⟪i,x⟫∈W`
  have hg1 : ∀ x' x i : M,
      Semiformula.Evalm M ![x', x, i, W, k] e (Semiformula.lMap Φ (memRelOpr.operator ![#3, #2, #1]))
        ↔ ⟪i, x⟫ ∈ W := by
    intro x' x i
    rw [Semiformula.eval_lMap, hred, Semiformula.eval_operator]
    have hv : (fun j : Fin 3 =>
        Semiterm.val (@standardModel M oM) ![x', x, i, W, k] e (![(#3 : Semiterm ℒₒᵣ ℕ 5), #2, #1] j))
        = ![W, i, x] := by funext j; fin_cases j <;> simp [Semiterm.val_bvar]
    simp only [hv, eval_memRel]
  -- guard 2: `⟪i+1,x'⟫∈W`
  have hg2 : ∀ x' x i : M,
      Semiformula.Evalm M ![x', x, i, W, k] e
        (Semiformula.lMap Φ (memRelOpr.operator ![#3, ‘(#2 + 1)’, #0])) ↔ ⟪i + 1, x'⟫ ∈ W := by
    intro x' x i
    rw [Semiformula.eval_lMap, hred, Semiformula.eval_operator]
    have hv : (fun j : Fin 3 =>
        Semiterm.val (@standardModel M oM) ![x', x, i, W, k] e
          (![(#3 : Semiterm ℒₒᵣ ℕ 5), ‘(#2 + 1)’, #0] j)) = ![W, i + 1, x'] := by
      funext j; fin_cases j <;> simp [Semiterm.val_bvar]
    simp only [hv, eval_memRel]
  -- prec atom: `Mlt f x' x`
  have hp : ∀ x' x i : M,
      Semiformula.Evalm M ![x', x, i, W, k] e (Thm56.prec ⇜ ![(#0 : Semiterm LX ℕ 5), #1])
        ↔ Mlt f x' x := by
    intro x' x i
    rw [Semiformula.eval_substs]
    have hbv : (fun j : Fin 2 =>
        Semiterm.valm M ![x', x, i, W, k] e (![(#0 : Semiterm LX ℕ 5), #1] j)) = ![x', x] := by
      funext j; fin_cases j <;> simp [Semiterm.val_bvar]
    rw [hbv]
    show Semiformula.Eval _ ![x', x] e Thm56.prec ↔ Semiformula.Eval _ ![x', x] f Thm56.prec
    exact Semiformula.eval_iff_of_funEqOn Thm56.prec
      (fun z hz => absurd hz (by simp [Semiformula.FVar?, Thm56.freeVariables_prec]))
  simp only [Semiformula.eval_all, LogicalConnective.HomClass.map_imply]
  constructor
  · intro hB i x x' h1 h2
    exact (hp x' x i).mpr (hB i x x' ((hg1 x' x i).mp h1) ((hg2 x' x i).mp h2))
  · intro hR i x x' h1 h2
    exact (hp x' x i).mp (hR i x x' ((hg1 x' x i).mpr h1) ((hg2 x' x i).mpr h2))

/-- **Piece A of `hDdef`: the skeleton `Seq W ∧ ⟪0,a₀⟫∈W ∧ lh W = k+1` is binary-`LX`-definable** (with
`a₀` a parameter, carried by the free assignment `e 0 = a₀`). Pure `ℒₒᵣ`-on-reduct: `Seq` via `seqDef`,
membership via `memRelOpr`, `lh W = k+1` via `lhDef` (both `𝚺₀` Foundation `Defined` predicates, read off
the reduct by `Defined.iff`). -/
theorem skel_lxDef (a₀ : M) :
    letI : ORingStructure M := ReductModel.reductORing
    haveI : M ⊧ₘ* (𝗜𝚺₁ : Theory ℒₒᵣ) := ReductModel.reduct_models_isigma1 hM
    ∃ e : ℕ → M, ∃ β : Semiformula LX ℕ 2,
      ∀ W k : M, (Seq W ∧ ⟪(0 : M), a₀⟫ ∈ W ∧ lh W = k + 1)
        ↔ Semiformula.Evalm M ![W, k] e β := by
  letI oM : ORingStructure M := ReductModel.reductORing
  haveI hI : M ⊧ₘ* (𝗜𝚺₁ : Theory ℒₒᵣ) := ReductModel.reduct_models_isigma1 hM
  have hred := ReductModel.reduct_eq_standardModel (M := M)
  refine ⟨fun _ => a₀, Semiformula.lMap Φ (
      ((Rewriting.emb (seqDef.val)) ⇜ ![(#0 : Semiterm ℒₒᵣ ℕ 2)]) ⋏
      (memRelOpr.operator ![#0, ‘0’, &0]) ⋏
      ((Rewriting.emb (lhDef.val)) ⇜ ![‘(#1 + 1)’, (#0 : Semiterm ℒₒᵣ ℕ 2)])), fun W k => ?_⟩
  set e : ℕ → M := fun _ => a₀ with he
  rw [Semiformula.eval_lMap, hred, LogicalConnective.HomClass.map_and,
    LogicalConnective.HomClass.map_and]
  refine and_congr ?_ (and_congr ?_ ?_)
  · -- `Seq W`
    rw [Semiformula.eval_substs, Semiformula.eval_emb]
    have hv : (fun i : Fin 1 =>
        Semiterm.val (@standardModel M oM) ![W, k] e (![(#0 : Semiterm ℒₒᵣ ℕ 2)] i)) = ![W] := by
      funext j; fin_cases j <;> simp [Semiterm.val_bvar]
    rw [hv]
    simp
  · -- `⟪0,a₀⟫∈W`
    rw [Semiformula.eval_operator]
    have hv : (fun j : Fin 3 =>
        Semiterm.val (@standardModel M oM) ![W, k] e (![(#0 : Semiterm ℒₒᵣ ℕ 2), ‘0’, &0] j))
        = ![W, 0, a₀] := by funext j; fin_cases j <;> simp [Semiterm.val_bvar, he]
    rw [hv]; simp
  · -- `lh W = k+1`
    rw [Semiformula.eval_substs, Semiformula.eval_emb]
    have hv : (fun i : Fin 2 =>
        Semiterm.val (@standardModel M oM) ![W, k] e (![‘(#1 + 1)’, (#0 : Semiterm ℒₒᵣ ℕ 2)] i))
        = ![k + 1, W] := by funext j; fin_cases j <;> simp [Semiterm.val_bvar]
    rw [hv]
    rw [show (lh W = k + 1) ↔ (k + 1 = lh W) from eq_comm]
    simp

/-- **The descent sequence exists for every length.** By `lx_succ_induction` (`base`/`extend`). The lone
remaining obligation is the `LX`-definability of `D(k) := ∃ W, IsDescent W ∧ lh W = k+1` — see the file
header. Disclosed `sorry` (wall C's last sub-obligation; `wip/`, off the build). -/
theorem descent_seq_exists
    (no_min : ∀ x : M, ¬ MX x → ∃ y, Mlt f y x ∧ ¬ MX y)
    {a₀ : M} (ha₀ : ¬ MX a₀) :
    letI : ORingStructure M := ReductModel.reductORing
    haveI : M ⊧ₘ* (𝗜𝚺₁ : Theory ℒₒᵣ) := ReductModel.reduct_models_isigma1 hM
    ∀ k : M, ∃ W, IsDescent f a₀ W ∧ lh W = k + 1 := by
  letI : ORingStructure M := ReductModel.reductORing
  haveI : M ⊧ₘ* (𝗜𝚺₁ : Theory ℒₒᵣ) := ReductModel.reduct_models_isigma1 hM
  haveI hPA : M ⊧ₘ* (𝗣𝗔⁻ : Theory ℒₒᵣ) := models_of_subtheory (ReductModel.reduct_models_PA hM)
  -- `D(k) := ∃ W, IsDescent f a₀ W ∧ lh W = k+1` is LX-definable (header obligation), now DISCHARGED:
  -- it is `∃ W, A(W,k) ∧ B(W) ∧ C(W)` (pieces `skel_lxDef`/`descentMlt_lxDef`/`xclause_lxDef`),
  -- combined by `lxDef2_and` and `∃`-closed by `lxDef_exists`; the membership form is `isDescent_iff_mem`.
  have hDdef : ∃ e : ℕ → M, ∃ φ : Semiformula LX ℕ 1,
      ∀ k, (∃ W, IsDescent f a₀ W ∧ lh W = k + 1) ↔ Semiformula.Evalm M ![k] e φ := by
    obtain ⟨e, φ, hφ⟩ :=
      lxDef_exists (lxDef2_and (skel_lxDef hM a₀) (lxDef2_and (descentMlt_lxDef hM f) (xclause_lxDef hM)))
    refine ⟨e, φ, fun k => ?_⟩
    rw [← hφ k]
    refine exists_congr fun W => ?_
    have h0 : (0 : M) < k + 1 := lt_of_le_of_lt (by simp) (lt_add_one k)
    constructor
    · rintro ⟨hdesc, hlh⟩
      rw [isDescent_iff_mem f a₀ W (hlh ▸ h0)] at hdesc
      obtain ⟨hSeq, hmem, hdMlt, hnotMX⟩ := hdesc
      exact ⟨⟨hSeq, hmem, hlh⟩, hdMlt, hnotMX⟩
    · rintro ⟨⟨hSeq, hmem, hlh⟩, hdMlt, hnotMX⟩
      exact ⟨(isDescent_iff_mem f a₀ W (hlh ▸ h0)).mpr ⟨hSeq, hmem, hdMlt, hnotMX⟩, hlh⟩
  refine lx_succ_induction hM hDdef ?_ ?_
  · -- base: `k = 0`
    obtain ⟨hd, hl⟩ := descent_base hM f ha₀
    exact ⟨_, hd, by rw [hl]; exact (zero_add 1).symm⟩
  · -- step: extend
    rintro k ⟨W, hW, hk⟩
    obtain ⟨W', hW', hk'⟩ := descent_extend hM f no_min hW hk
    exact ⟨W', hW', by rw [hk', add_assoc, one_add_one_eq_two]⟩

end

end GoodsteinPA.DescentConstruction
