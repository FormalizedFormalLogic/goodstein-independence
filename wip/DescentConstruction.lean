/-
# `wip/DescentConstruction.lean` — wall C: the M-internal `Mlt`-descent sequence (SCAFFOLD)

The lone wall `DescentSemantic.no_min_descent_absurd_of_goodstein`'s `hCD` needs an `M`-internal,
`LX`-definable descending sequence built from `no_min`/`ha₀`. This file scaffolds that construction
over `M`'s `ℒₒᵣ`-reduct (`reductORing`, `⊧ 𝗜𝚺₁`) using Foundation's HFS `Seq` coding:

- `IsDescent f a₀ W` — `W` codes a finite `Mlt`-descending sequence through `¬MX` from `a₀`.
- `descent_base` / `descent_extend` — the base (length 1) and the canonical one-step extension (via
  `DescentSemantic.descent_step`, the `lx_least_number` selector). **PROVEN** (real math content).
- `descent_seq_exists` — `∀ k, ∃ W, IsDescent W ∧ lh W = k+1`, by `lx_succ_induction`. **Disclosed
  `sorry`** on the lone remaining obligation: the `LX`-definability of the predicate
  `D(k) := ∃ W, IsDescent W ∧ lh W = k+1` (an `LX`-formula with a `Seq`-existential + interleaved
  `Mlt`/`¬MX` atoms on `znth`-terms). The combinators in `DescentSemantic`
  (`lxDef_of_reduct`, `lxDef_and`, `MX_lxDef`) carry the `ℒₒᵣ` parts; the `znth`-term `X`-atoms are
  built directly (next lap).

This file is OUTSIDE the build target (`wip/`), so its disclosed `sorry`s do not block the self-stop
gate; `src/` stays sorry-free. Promote to `src/` once `descent_seq_exists` is sorry-free.
-/
import GoodsteinPA.DescentSemantic

namespace GoodsteinPA.DescentConstruction

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open GoodsteinPA GoodsteinPA.LangX GoodsteinPA.EmbeddingX GoodsteinPA.DescentSemantic

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
  -- `D(k) := ∃ W, IsDescent f a₀ W ∧ lh W = k+1` is LX-definable (header obligation).
  have hDdef : ∃ e : ℕ → M, ∃ φ : Semiformula LX ℕ 1,
      ∀ k, (∃ W, IsDescent f a₀ W ∧ lh W = k + 1) ↔ Semiformula.Evalm M ![k] e φ := by
    sorry
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
