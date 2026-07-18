/-
# `wip/StdCor34.lean` — Crux 1: the STANDARD-level internal Cor 3.4 global assembly

**Status: GREEN over an abstract bookkeeping/`ig`-tail interface (wip, off the build target).**

Lap-50's KEY insight (memory `crux1-headline-needs-only-standard-level`): for the headline,
`goodstein_implies_consistency = crux2 ∘ crux1` uses crux 1 (`γ → PRWO`) at the **single** concrete
primrec instance `gentzenDescentφ`, so Rathjen's Lemma 3.2 gives a **STANDARD** Grzegorczyk level —
the internal-Ackermann wall (laps 45–49) is OFF the headline path. Hence the slow-down only needs the
standard-level Cor 3.4.

This file builds the **global assembly** of Cor 3.4 — the step that turns a raw `≺`-descending sequence
`β` into the *slow* sequence `α j = ω^(l+1)·β_{blk j} + igt (blk j) (off j)` with
`iC(α j) ≤ K·(j+1)` — by composing the (already machine-checked, axiom-clean) `InternalCor34` bricks
`icorAlpha_within` / `icorAlpha_boundary` / `icorAlpha_C_le` / `isNF_icorAlpha`. The output `α` is
exactly the input `InternalThm35.bbeta` (Thm 3.5) consumes (`isNF` + `iC ≤ K(j+1)` + `icmp`-descent).

**What is REAL here (new, non-vacuous content):** the internal *global* Cor-3.4 assembly. The
ℕ-template `Grz.corAlpha_*` only proves the per-step descent (the global `∀ j, αⱼ₊₁ ≺ αⱼ` is *vacuous*
in ℕ — ε₀ is well-founded, no infinite input descent exists). Inside `V ⊧ 𝗜𝚺₁` the descent is a genuine
nonstandard infinite one, so the global assembly is content, not bookkeeping.

**What is still abstract (the remaining crux-1 obligations, disclosed as hypotheses):**
- the block bookkeeping `blk`/`off` (internal `iwsum`/`iwidx`/`iwoff` — partial sums + `findGreatest`
  over the width function `t ↦ iC(β(t+1))`), with the dichotomy `blk(j+1) ∈ {blk j, blk j + 1}` and the
  C-bookkeeping `blk j + off j ≤ j`;
- the slow-tail family `igt n m` = the internal Grzegorczyk `g` recursion (`Grz.g`), with NF / `≠0` /
  within-block descent / `iC ≤ Kg·(n+m+1)` / `iAbove (ocExp (igt n m)) (ω^(l+1)·…)` (the `g < ω^(l+1)`
  clean-append condition).
These are the next bricks to discharge (the bookkeeping is mechanical `𝚺₁` recursion; the `ig`
recursion is the deep `g`-padding, standard level). Discharging them turns this assembly into the real
internal Cor 3.4, feeding `bbeta` → `DescentArith.nonterminating_internal` (Lemma 3.6) → crux 1.
-/
import GoodsteinPA.InternalCor34
import GoodsteinPA.InternalThm35
import GoodsteinPA.InternalIg
import GoodsteinPA.DescentSlowdown
import GoodsteinPA.Compat

namespace GoodsteinPA.StdCor34

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open GoodsteinPA GoodsteinPA.InternalONote GoodsteinPA.IIter GoodsteinPA.InternalIg
open GoodsteinPA.InternalPow

set_option maxHeartbeats 400000

-- The code-arithmetic defs (`iVbigMul`/`iadd`/`icorAlpha`) never reduce on a variable level, so
-- leaving them semi-reducible sends `isDefEq` into a `whnf` loop even on syntactically identical
-- terms (lap-49 `iVbigMul` irreducibility note). Make them opaque to defeq in this file — every brick
-- we apply matches structurally on these heads, so no unfolding is ever needed.
attribute [local irreducible] iadd icorAlpha

variable {V : Type*} [ORingStructure V] [V ⊧ₘ* 𝗜𝚺₁]

/-- The (standard-level) Cor 3.4 slowed sequence:
`α j = ω^(l+1)·β_{blk j} + igt (blk j) (off j)` (= `icorAlpha (β (blk j)) (igt (blk j) (off j)) l`). -/
noncomputable def salpha (l : V) (β blk off : V → V) (igt : V → V → V) (j : V) : V :=
  icorAlpha (β (blk j)) (igt (blk j) (off j)) l

variable {l : V} {β blk off : V → V} {igt : V → V → V}

/-- **NF of the slowed sequence.** Each `α j` is a valid normal-form code (`isNF_icorAlpha`). -/
theorem salpha_isNF
    (hβNF : ∀ n, isNF (β n))
    (higtNF : ∀ n m, isNF (igt n m))
    (higt0 : ∀ n m, igt n m ≠ 0)
    (habove : ∀ n m a, iAbove (ocExp (igt n m)) (iVbigMul (β (blk a)) (l + 1)))
    (j : V) : isNF (salpha l β blk off igt j) :=
  isNF_icorAlpha (hβNF (blk j)) (higtNF (blk j) (off j)) (higt0 (blk j) (off j))
    (habove (blk j) (off j) j)

/-- **The global ≺-descent.** `α (j+1) ≺ α j` for every `j`, by the block dichotomy:
within a block (`blk(j+1) = blk j`) the lead is fixed and the `igt`-tail descends
(`icorAlpha_within`); at a block boundary (`blk(j+1) = blk j + 1`) the lead drops via the raw descent
`β_{blk j+1} ≺ β_{blk j}` and the tail is absorbed (`icorAlpha_boundary`). -/
theorem salpha_desc
    (hβNF : ∀ n, isNF (β n))
    (hβdesc : ∀ n, icmp (β (n + 1)) (β n) = 0)
    (higt0 : ∀ n m, igt n m ≠ 0)
    (habove : ∀ n m a, iAbove (ocExp (igt n m)) (iVbigMul (β (blk a)) (l + 1)))
    (hblk_dich : ∀ j, blk (j + 1) = blk j ∨ blk (j + 1) = blk j + 1)
    (higt_within : ∀ j, blk (j + 1) = blk j →
        icmp (igt (blk j) (off (j + 1))) (igt (blk j) (off j)) = 0)
    (j : V) :
    icmp (salpha l β blk off igt (j + 1)) (salpha l β blk off igt j) = 0 := by
  have ej : salpha l β blk off igt j
      = icorAlpha (β (blk j)) (igt (blk j) (off j)) l := rfl
  rcases hblk_dich j with hw | hb
  · -- within block: lead `ω^(l+1)·β_{blk j}` fixed, the `igt`-tail descends
    have e1 : salpha l β blk off igt (j + 1)
        = icorAlpha (β (blk j)) (igt (blk j) (off (j + 1))) l := by
      unfold salpha; rw [hw]
    rw [e1, ej]
    exact @icorAlpha_within V _ _ (β (blk j)) (igt (blk j) (off (j + 1)))
      (igt (blk j) (off j)) l (higt0 (blk j) (off (j + 1))) (higt0 (blk j) (off j))
      (habove (blk j) (off (j + 1)) j) (habove (blk j) (off j) j) (higt_within j hw)
  · -- block boundary: lead drops via the raw descent, the `igt`-tail `< ω^(l+1)` is absorbed.
    -- Keep `salpha (j+1)` as `β (blk (j+1))` (no `hb`-rewrite) so the `habove` leads `β (blk a)`
    -- match at `a = j+1`/`a = j`; the raw descent transports through `hb` (`blk(j+1) = blk j + 1`).
    have e1 : salpha l β blk off igt (j + 1)
        = icorAlpha (β (blk (j + 1))) (igt (blk (j + 1)) (off (j + 1))) l := rfl
    rw [e1, ej]
    refine icorAlpha_boundary (hβNF (blk (j + 1))) (hβNF (blk j))
      (higt0 (blk (j + 1)) (off (j + 1))) (higt0 (blk j) (off j))
      ?_ ?_ ?_ ?_ (hb.symm ▸ hβdesc (blk j))
    · exact habove (blk (j + 1)) (off (j + 1)) (j + 1)
    · exact habove (blk (j + 1)) (off (j + 1)) j
    · exact habove (blk j) (off j) (j + 1)
    · exact habove (blk j) (off j) j

/-- **The slowness bound (Cor 3.4 conclusion).** `iC(α j) ≤ K·(j+1)` with `K = max (Cβ+(l+1)) Kg`,
via the clean-append C-split (`icorAlpha_C_le`): the lead contributes `iC(β_{blk j})+(l+1) ≤ (Cβ+j)+(l+1)
= (Cβ+(l+1))+j ≤ K·(j+1)` (constant-absorption `iconst_add_le_mul`), the `igt`-tail contributes
`iC(igt) ≤ Kg·(blk j + off j + 1) ≤ Kg·(j+1) ≤ K·(j+1)` (since `blk j + off j ≤ j`). The output `K` and
its positivity feed `bbeta_C_le`/`bbeta_desc`. -/
theorem salpha_C_le
    {Cβ Kg : V}
    (hβC : ∀ j, iC (β (blk j)) ≤ Cβ + j)
    (higtC : ∀ j, iC (igt (blk j) (off j)) ≤ Kg * (blk j + off j + 1))
    (hnm : ∀ j, blk j + off j ≤ j)
    (higt0 : ∀ n m, igt n m ≠ 0)
    (habove : ∀ n m a, iAbove (ocExp (igt n m)) (iVbigMul (β (blk a)) (l + 1))) :
    ∃ K, 0 < K ∧ ∀ j, iC (salpha l β blk off igt j) ≤ K * (j + 1) := by
  have hl1 : (1 : V) ≤ l + 1 := le_add_self
  have hK1 : (1 : V) ≤ max (Cβ + (l + 1)) Kg :=
    le_trans (le_trans hl1 le_add_self) (le_max_left _ _)
  refine ⟨max (Cβ + (l + 1)) Kg, lt_of_lt_of_le _root_.zero_lt_one hK1, fun j => ?_⟩
  unfold salpha
  refine le_trans (icorAlpha_C_le (higt0 (blk j) (off j)) (habove (blk j) (off j) j)) (max_le ?_ ?_)
  · -- lead: `iC(β_{blk j}) + (l+1) ≤ (Cβ+(l+1)) + j ≤ K·(j+1)`
    calc iC (β (blk j)) + (l + 1)
        ≤ (Cβ + j) + (l + 1) := by gcongr; exact hβC j
      _ = (Cβ + (l + 1)) + j := add_right_comm Cβ j (l + 1)
      _ ≤ max (Cβ + (l + 1)) Kg + j := by gcongr; exact le_max_left _ _
      _ ≤ max (Cβ + (l + 1)) Kg * (j + 1) := iconst_add_le_mul hK1
  · -- tail: `iC(igt) ≤ Kg·(blk j+off j+1) ≤ Kg·(j+1) ≤ K·(j+1)`
    calc iC (igt (blk j) (off j))
        ≤ Kg * (blk j + off j + 1) := higtC j
      _ ≤ Kg * (j + 1) := by gcongr; exact hnm j
      _ ≤ max (Cβ + (l + 1)) Kg * (j + 1) := by gcongr; exact le_max_right _ _

/-- **Discharge the clean-append `habove` family from a per-`igt` top-exponent bound.** The 3-arg
`habove` hypothesis of `salpha_*` is exactly the statement that every `igt n m` is clean below every
lead `ω^(l+1)·β_{blk a}`, which holds iff `igt n m < ω^(l+1)` — i.e. its top exponent is either `0`
(a finite code) or a finite code `j ≤ l`. This is the defining property of Rathjen's `g` (Lemma 3.3:
`|g l n m| < ω^(l+1)`), so the real `ig` recursion supplies `higt_exp` directly; here we route it
through the existing `iAbove_ocExp_iVbigMul_fin`/`_inf`. -/
theorem habove_of_igt_exp (hl : 0 < l)
    (hβ0 : ∀ n, β n ≠ 0) (hβNF : ∀ n, isNF (β n))
    (higt_exp : ∀ n m, ocExp (igt n m) = 0 ∨ ∃ j, j ≤ l ∧ ocExp (igt n m) = ocOadd 0 j 0) :
    ∀ n m a, iAbove (ocExp (igt n m)) (iVbigMul (β (blk a)) (l + 1)) := by
  intro n m a
  rcases higt_exp n m with h0 | ⟨j, hjl, hj⟩
  · exact iAbove_ocExp_iVbigMul_fin (hβ0 (blk a)) l h0
  · exact iAbove_ocExp_iVbigMul_inf (hβNF (blk a)) (hβ0 (blk a)) hl hjl hj

/-! ## The concrete Cor 3.4 assembly with the real internal-Grzegorczyk tail `igtTot`

Instantiate `salpha` with the totalized internal Grzegorczyk tail `igtTot l₀` (`InternalIg`, axiom-clean)
at a STANDARD level `l₀ ≥ 1`. The four unconditional `igtTot` props (`isNF_igtTot`/`igtTot_ne_zero`/
`higt_exp_igtTot`→`habove_of_igt_exp`/`iC_igtTot_bound`) discharge `salpha_isNF` and `salpha_C_le`
outright; `salpha_desc` reduces to the **single domination input** `hdom` (the within-block offset stays
below `iF l₀ (blk j)`, Rathjen Lemma 3.2) routed through `igtTot_within`. The output is exactly the
NF + tight-`iC` + ≺-descent triple `InternalThm35.bbeta_isNF`/`bbeta_C_le`/`bbeta_desc_exists` consume. -/
theorem salpha_igtTot_spec (l₀ : ℕ) (hl₀ : 0 < l₀)
    {β blk off : V → V} {Cβ : V}
    (hβNF : ∀ n, isNF (β n)) (hβ0 : ∀ n, β n ≠ 0)
    (hβdesc : ∀ n, icmp (β (n + 1)) (β n) = 0)
    (hβC : ∀ j, iC (β (blk j)) ≤ Cβ + j)
    (hblk_dich : ∀ j, blk (j + 1) = blk j ∨ blk (j + 1) = blk j + 1)
    (hoff_adv : ∀ j, blk (j + 1) = blk j → off (j + 1) = off j + 1)
    (hnm : ∀ j, blk j + off j ≤ j)
    (hdom : ∀ j, blk (j + 1) = blk j → off j + 1 < iF l₀ (blk j)) :
    (∀ j, isNF (salpha (l₀ : V) β blk off (igtTot l₀) j)) ∧
    (∃ K, 0 < K ∧ ∀ j, iC (salpha (l₀ : V) β blk off (igtTot l₀) j) ≤ K * (j + 1)) ∧
    (∀ j, icmp (salpha (l₀ : V) β blk off (igtTot l₀) (j + 1))
            (salpha (l₀ : V) β blk off (igtTot l₀) j) = 0) := by
  have hlV : (0 : V) < (l₀ : V) := by exact_mod_cast hl₀
  have habove : ∀ n m a, iAbove (ocExp (igtTot l₀ n m)) (iVbigMul (β (blk a)) ((l₀ : V) + 1)) :=
    habove_of_igt_exp hlV hβ0 hβNF (higt_exp_igtTot l₀)
  obtain ⟨Kg, _, hKg⟩ := iC_igtTot_bound (V := V) l₀
  refine ⟨fun j => salpha_isNF hβNF (isNF_igtTot l₀) (igtTot_ne_zero l₀) habove j,
    salpha_C_le hβC (fun j => hKg (blk j) (off j)) hnm (igtTot_ne_zero l₀) habove,
    fun j => salpha_desc hβNF hβdesc (igtTot_ne_zero l₀) habove hblk_dich ?_ j⟩
  intro j hw
  rw [hoff_adv j hw]
  exact igtTot_within l₀ (blk j) (off j) (hdom j hw)

/-- **Cor 3.4 → Thm 3.5, end-to-end (internal, modulo the named hypotheses).** Feeding the
`salpha_igtTot_spec` triple into `InternalThm35.bbeta` produces the complete Thm 3.5 sequence
`β' = bbeta K s α` (ω-tower prefix + slow-down block-tail) with a height `s`, positive `K`, the NF
invariant, the **tight** slowness `iC(β'ᵣ) ≤ r+1`, and strict ≺-descent at every index — exactly the
input `DescentArith`/Lemma 3.6 consume. The remaining crux-1 frontier is then: (1) the `hdom`
domination (Lemma 3.2), (2) the `blk`/`off` bookkeeping from `BlkRec` + the raw input descent `β` from
the gentzen instance, (3) the reflection lift of the V-internal descent to `𝗣𝗔 ⊢ prwoInstance`. -/
theorem bbeta_of_igtTot (l₀ : ℕ) (hl₀ : 0 < l₀)
    {β blk off : V → V} {Cβ : V}
    (hβNF : ∀ n, isNF (β n)) (hβ0 : ∀ n, β n ≠ 0)
    (hβdesc : ∀ n, icmp (β (n + 1)) (β n) = 0)
    (hβC : ∀ j, iC (β (blk j)) ≤ Cβ + j)
    (hblk_dich : ∀ j, blk (j + 1) = blk j ∨ blk (j + 1) = blk j + 1)
    (hoff_adv : ∀ j, blk (j + 1) = blk j → off (j + 1) = off j + 1)
    (hnm : ∀ j, blk j + off j ≤ j)
    (hdom : ∀ j, blk (j + 1) = blk j → off j + 1 < iF l₀ (blk j)) :
    ∃ K s : V, 0 < K ∧
      (∀ r, isNF (bbeta K s (salpha (l₀ : V) β blk off (igtTot l₀)) r)) ∧
      (∀ r, iC (bbeta K s (salpha (l₀ : V) β blk off (igtTot l₀)) r) ≤ r + 1) ∧
      (∀ r, icmp (bbeta K s (salpha (l₀ : V) β blk off (igtTot l₀)) (r + 1))
              (bbeta K s (salpha (l₀ : V) β blk off (igtTot l₀)) r) = 0) := by
  obtain ⟨hNF, ⟨K, hKpos, hslow⟩, hdesc⟩ :=
    salpha_igtTot_spec l₀ hl₀ hβNF hβ0 hβdesc hβC hblk_dich hoff_adv hnm hdom
  obtain ⟨s, hs⟩ := bbeta_desc_exists hKpos hNF hdesc
  exact ⟨K, s, hKpos, bbeta_isNF hKpos hNF, bbeta_C_le hslow, hs⟩

/-- **Cor 3.4 → Thm 3.5 with the bookkeeping discharged by `BlkRec`.** The abstract `blk`/`off`
dichotomy/advance/`≤j` hypotheses of `bbeta_of_igtTot` are *exactly* the `BlkRec` block-state laws
(`blk_succ_dich`/`off_succ_of_blk_eq`/`blk_add_off_le`) for any width code `wseq`. So specializing
`blk := BlkRec.blk wseq`, `off := BlkRec.off wseq` discharges all the bookkeeping internally — the
crux-1 frontier collapses to just **(input ≺-descending NF `β`) + (domination `hdom`)**. -/
theorem bbeta_of_igtTot_blkRec (l₀ : ℕ) (hl₀ : 0 < l₀) (wseq : V)
    {β : V → V} {Cβ : V}
    (hβNF : ∀ n, isNF (β n)) (hβ0 : ∀ n, β n ≠ 0)
    (hβdesc : ∀ n, icmp (β (n + 1)) (β n) = 0)
    (hβC : ∀ j, iC (β (BlkRec.blk wseq j)) ≤ Cβ + j)
    (hdom : ∀ j, BlkRec.blk wseq (j + 1) = BlkRec.blk wseq j →
        BlkRec.off wseq j + 1 < iF l₀ (BlkRec.blk wseq j)) :
    ∃ K s : V, 0 < K ∧
      (∀ r, isNF (bbeta K s
        (salpha (l₀ : V) β (BlkRec.blk wseq) (BlkRec.off wseq) (igtTot l₀)) r)) ∧
      (∀ r, iC (bbeta K s
        (salpha (l₀ : V) β (BlkRec.blk wseq) (BlkRec.off wseq) (igtTot l₀)) r) ≤ r + 1) ∧
      (∀ r, icmp (bbeta K s
              (salpha (l₀ : V) β (BlkRec.blk wseq) (BlkRec.off wseq) (igtTot l₀)) (r + 1))
            (bbeta K s
              (salpha (l₀ : V) β (BlkRec.blk wseq) (BlkRec.off wseq) (igtTot l₀)) r) = 0) :=
  bbeta_of_igtTot l₀ hl₀ hβNF hβ0 hβdesc hβC
    (BlkRec.blk_succ_dich wseq) (BlkRec.off_succ_of_blk_eq wseq) (BlkRec.blk_add_off_le wseq) hdom

/-! ## Bridge to the non-terminating Goodstein run (Lemma 3.6 consumer seam)

The Thm-3.5 output `β'` (`isNF` + `iC(β'ᵣ) ≤ r+1` + ≺-descent) is *exactly* the data
`DescentSlowdown.nonterminating_of_slowdown` consumes (modulo `𝚺₁`-definability of `β'`): `iCanon (r+1)
(β'ᵣ)` is definitionally `iC(β'ᵣ) ≤ r+1`. So feeding `β'` through the Lemma-3.6 engine gives a seed `m₀`
whose internal Goodstein run never terminates — the contradiction with the lifted `goodsteinSentence`. -/

/-! ## `𝚺₁`-definability of the slowed sequence (`hdef` discharge)

The whole `bbeta ∘ salpha` construction is a fixed composition of `𝚺₁`-definable code-arithmetic
operations (`iadd`/`iVbigMul`/`iomul`/`ocOadd`/`iwtower`/`/`/`%`) applied to the definable inputs
`β`/`blk`/`off`/`igtTot`. So given the definability of those inputs the slowed sequence is
`𝚺₁`-definable — exactly the `hdef` hypothesis `crux1_internal_run` carries. -/

open LO.FirstOrder.Arithmetic.HierarchySymbol in
/-- `bbtail K α r = iadd (iomul (α ((r−K)/K))) (ω^0·(K − (r−K)%K))` is `𝚺₁`-definable in `r`. -/
lemma bbtail_definable (K : V) {α : V → V} (hα : 𝚺₁-Function₁ α) :
    𝚺₁-Function₁ (bbtail K α : V → V) := by
  have h : (fun v : Fin 1 → V => bbtail K α (v 0))
      = (fun v : Fin 1 → V =>
          iadd (iomul (α ((v 0 - K) / K))) (ocOadd 0 (K - (v 0 - K) % K) 0)) := by
    funext v; simp only [bbtail]
  show 𝚺₁.DefinableFunction (fun v : Fin 1 → V => bbtail K α (v 0))
  rw [h]
  exact DefinableFunction₂.comp (F := iadd) (hF := iadd_definable' 𝚺)
    (DefinableFunction₁.comp (hF := iomul_definable' 𝚺)
      (DefinableFunction₁.comp (hF := hα)
        (DefinableFunction₂.comp (F := (· / ·))
          (DefinableFunction₂.comp (F := (· - ·))
            (DefinableFunction.var 0) (DefinableFunction.const K))
          (DefinableFunction.const K))))
    (DefinableFunction₃.comp (F := ocOadd) (hF := ocOadd_definable.of_sigmaOne)
      (DefinableFunction.const 0)
      (DefinableFunction₂.comp (F := (· - ·)) (DefinableFunction.const K)
        (DefinableFunction₂.comp (F := (· % ·))
          (DefinableFunction₂.comp (F := (· - ·))
            (DefinableFunction.var 0) (DefinableFunction.const K))
          (DefinableFunction.const K)))
      (DefinableFunction.const 0))

open LO.FirstOrder.Arithmetic.HierarchySymbol in
/-- `bbeta K s α r = if r < K then iwtower (s + (K−1−r)) else bbtail K α r` is `𝚺₁`-definable in `r`. -/
lemma bbeta_definable (K s : V) {α : V → V} (hα : 𝚺₁-Function₁ α) :
    𝚺₁-Function₁ (bbeta K s α : V → V) := by
  have h : (fun v : Fin 1 → V => bbeta K s α (v 0))
      = (fun v : Fin 1 → V =>
          if v 0 < K then iwtower (s + (K - 1 - v 0)) else bbtail K α (v 0)) := by
    funext v; simp only [bbeta]
  show 𝚺₁.DefinableFunction (fun v : Fin 1 → V => bbeta K s α (v 0))
  rw [h]
  apply definableFunction_ite
  · exact Definable.comp₂ (P := (· < ·)) (DefinableFunction.var 0) (DefinableFunction.const K)
  · exact Definable.not
      (Definable.comp₂ (P := (· < ·)) (DefinableFunction.var 0) (DefinableFunction.const K))
  · exact DefinableFunction₁.comp (hF := iwtower_definable' 𝚺)
      (DefinableFunction₂.comp (F := (· + ·)) (DefinableFunction.const s)
        (DefinableFunction₂.comp (F := (· - ·))
          (DefinableFunction.const (K - 1)) (DefinableFunction.var 0)))
  · exact bbtail_definable K hα

open LO.FirstOrder.Arithmetic.HierarchySymbol in
/-- `salpha l β blk off igt j = iadd (iVbigMul (β (blk j)) (l+1)) (igt (blk j) (off j))` is
`𝚺₁`-definable in `j`, given the definability of `β`, `blk`, `off`, `igt`. -/
lemma salpha_definable (l : V) {β blk off : V → V} {igt : V → V → V}
    (hβ : 𝚺₁-Function₁ β) (hblk : 𝚺₁-Function₁ blk) (hoff : 𝚺₁-Function₁ off)
    (higt : 𝚺₁-Function₂ igt) :
    𝚺₁-Function₁ (salpha l β blk off igt : V → V) := by
  have h : (fun v : Fin 1 → V => salpha l β blk off igt (v 0))
      = (fun v : Fin 1 → V =>
          iadd (iVbigMul (β (blk (v 0))) (l + 1)) (igt (blk (v 0)) (off (v 0)))) := by
    funext v; simp only [salpha, icorAlpha]
  show 𝚺₁.DefinableFunction (fun v : Fin 1 → V => salpha l β blk off igt (v 0))
  rw [h]
  refine DefinableFunction₂.comp (F := iadd) (hF := iadd_definable' 𝚺) ?_ ?_
  · exact DefinableFunction₂.comp (F := iVbigMul) (hF := iVbigMul_definable' 𝚺)
      (DefinableFunction₁.comp (hF := hβ)
        (DefinableFunction₁.comp (hF := hblk) (DefinableFunction.var 0)))
      (DefinableFunction₂.comp (F := (· + ·)) (DefinableFunction.const l) (DefinableFunction.const 1))
  · exact DefinableFunction₂.comp (F := igt) (hF := higt)
      (DefinableFunction₁.comp (hF := hblk) (DefinableFunction.var 0))
      (DefinableFunction₁.comp (hF := hoff) (DefinableFunction.var 0))

/-- **Thm 3.5 facts → non-terminating internal Goodstein run.** Pure seam: repackage the `bbeta`
output triple as `nonterminating_of_slowdown`'s input (`iCanon` from the `iC`-bound). -/
theorem nonterminating_of_bbeta_facts {β' : V → V}
    (hdef : 𝚺₁-Function₁ β')
    (hNF : ∀ r, isNF (β' r))
    (hC : ∀ r, iC (β' r) ≤ r + 1)
    (hdesc : ∀ r, icmp (β' (r + 1)) (β' r) = 0) :
    ∃ m₀ : V, ∀ k : V, 0 < igoodstein m₀ k :=
  DescentSlowdown.nonterminating_of_slowdown hdef hNF
    (fun r => (iCanon_def (r + 1) (β' r)).mpr (hC r)) hdesc

/-- **Crux-1 internal run, end-to-end (modulo input `β`, domination, definability).** Chains the whole
internal-Grzegorczyk girder — `igtTot` tail → `salpha` (Cor 3.4) → `bbeta` (Thm 3.5) → the Lemma-3.6
engine — into a non-terminating internal Goodstein run. The three remaining gaps are exactly the named
hypotheses: the input ≺-descending NF `β` (gentzen ε₀-descent), the domination `hdom` (Lemma 3.2), and
the `𝚺₁`-definability of the slowed sequence (a uniform construction, so quantified over `K`,`s`). -/
theorem crux1_internal_run (l₀ : ℕ) (hl₀ : 0 < l₀) (wseq : V)
    {β : V → V} {Cβ : V}
    (hβNF : ∀ n, isNF (β n)) (hβ0 : ∀ n, β n ≠ 0)
    (hβdesc : ∀ n, icmp (β (n + 1)) (β n) = 0)
    (hβC : ∀ j, iC (β (BlkRec.blk wseq j)) ≤ Cβ + j)
    (hdom : ∀ j, BlkRec.blk wseq (j + 1) = BlkRec.blk wseq j →
        BlkRec.off wseq j + 1 < iF l₀ (BlkRec.blk wseq j))
    (hdef : ∀ K s : V, 𝚺₁-Function₁
        (bbeta K s (salpha (l₀ : V) β (BlkRec.blk wseq) (BlkRec.off wseq) (igtTot l₀)))) :
    ∃ m₀ : V, ∀ k : V, 0 < igoodstein m₀ k := by
  obtain ⟨K, s, _, hNF, hC, hdesc⟩ :=
    bbeta_of_igtTot_blkRec l₀ hl₀ wseq hβNF hβ0 hβdesc hβC hdom
  exact nonterminating_of_bbeta_facts (hdef K s) hNF hC hdesc

open LO.FirstOrder.Arithmetic.HierarchySymbol in
/-- **`hdef` discharged.** For any fixed `wseq` and `𝚺₁`-definable input `β`, the slowed sequence
`bbeta K s (salpha l₀ β (BlkRec.blk wseq) (BlkRec.off wseq) (igtTot l₀))` is `𝚺₁`-definable in `r`
for every `K`,`s`. Composes `bbeta_definable` over `salpha_definable` over the four definable inputs:
`β` (the hypothesis), the `BlkRec` block-state projections (`BlkRec.blk_definable`/`off_definable`,
specialized at the fixed `wseq`), and the totalized internal Grzegorczyk tail (`igtTot_definable`). -/
theorem hdef_of_beta_definable (l₀ : ℕ) (wseq : V) {β : V → V} (hβ : 𝚺₁-Function₁ β)
    (K s : V) :
    𝚺₁-Function₁
      (bbeta K s (salpha (l₀ : V) β (BlkRec.blk wseq) (BlkRec.off wseq) (igtTot l₀))) := by
  have hblk : 𝚺₁-Function₁ (BlkRec.blk wseq : V → V) :=
    DefinableFunction₂.comp (F := BlkRec.blk) (hF := BlkRec.blk_definable 𝚺)
      (DefinableFunction.const wseq) (DefinableFunction.var 0)
  have hoff : 𝚺₁-Function₁ (BlkRec.off wseq : V → V) :=
    DefinableFunction₂.comp (F := BlkRec.off) (hF := BlkRec.off_definable 𝚺)
      (DefinableFunction.const wseq) (DefinableFunction.var 0)
  exact bbeta_definable K s
    (salpha_definable (l₀ : V) hβ hblk hoff (igtTot_definable l₀ 𝚺))

/-- **Crux-1 internal run, definability discharged.** Same as `crux1_internal_run` but with the `hdef`
hypothesis replaced by the single definability premise on the input `β` (everything else in the
`bbeta ∘ salpha` tower is a fixed `𝚺₁`-definable construction). The crux-1 frontier is now exactly
**(input ≺-descending NF `β`, definable) + (domination `hdom`)**. -/
theorem crux1_internal_run_of_beta_def (l₀ : ℕ) (hl₀ : 0 < l₀) (wseq : V)
    {β : V → V} {Cβ : V}
    (hβNF : ∀ n, isNF (β n)) (hβ0 : ∀ n, β n ≠ 0)
    (hβdesc : ∀ n, icmp (β (n + 1)) (β n) = 0)
    (hβC : ∀ j, iC (β (BlkRec.blk wseq j)) ≤ Cβ + j)
    (hβdef : 𝚺₁-Function₁ β)
    (hdom : ∀ j, BlkRec.blk wseq (j + 1) = BlkRec.blk wseq j →
        BlkRec.off wseq j + 1 < iF l₀ (BlkRec.blk wseq j)) :
    ∃ m₀ : V, ∀ k : V, 0 < igoodstein m₀ k :=
  crux1_internal_run l₀ hl₀ wseq hβNF hβ0 hβdesc hβC hdom
    (fun K s => hdef_of_beta_definable l₀ wseq hβdef K s)

/-- **Domination `hdom` reduces to *width* domination.** The `hdom` hypothesis (within a block the
offset stays below `iF l₀ (blk j)`) follows from the single Rathjen-Lemma-3.2 input that every block
*width* is bounded by the standard Grzegorczyk level: `∀ n, znth wseq n ≤ iF l₀ n`. Within-block, the
offset already sits strictly below the width (`BlkRec.off_succ_lt_width_of_blk_eq`); transitivity with
the width bound gives the offset bound. This isolates the crux-1 domination wall to *exactly* the
Grzegorczyk-domination of the width sequence — the concrete instance of Rathjen 2014 Lemma 3.2. -/
theorem hdom_of_width_dom (l₀ : ℕ) (wseq : V)
    (hwdom : ∀ n, znth wseq n ≤ iF l₀ n) :
    ∀ j, BlkRec.blk wseq (j + 1) = BlkRec.blk wseq j →
        BlkRec.off wseq j + 1 < iF l₀ (BlkRec.blk wseq j) :=
  fun j hb => lt_of_lt_of_le
    (BlkRec.off_succ_lt_width_of_blk_eq wseq j hb) (hwdom (BlkRec.blk wseq j))

/-- **Crux-1 internal run, domination reduced to width domination.** Same as
`crux1_internal_run_of_beta_def` but the domination premise is the clean *width-domination* statement
`∀ n, znth wseq n ≤ iF l₀ n` (Rathjen 2014 Lemma 3.2 at the concrete width sequence). The crux-1
frontier is now: **(input ≺-descending NF `β`, definable) + (the block widths are Grzegorczyk-bounded)**. -/
theorem crux1_internal_run_of_width_dom (l₀ : ℕ) (hl₀ : 0 < l₀) (wseq : V)
    {β : V → V} {Cβ : V}
    (hβNF : ∀ n, isNF (β n)) (hβ0 : ∀ n, β n ≠ 0)
    (hβdesc : ∀ n, icmp (β (n + 1)) (β n) = 0)
    (hβC : ∀ j, iC (β (BlkRec.blk wseq j)) ≤ Cβ + j)
    (hβdef : 𝚺₁-Function₁ β)
    (hwdom : ∀ n, znth wseq n ≤ iF l₀ n) :
    ∃ m₀ : V, ∀ k : V, 0 < igoodstein m₀ k :=
  crux1_internal_run_of_beta_def l₀ hl₀ wseq hβNF hβ0 hβdesc hβC hβdef
    (hdom_of_width_dom l₀ wseq hwdom)

end GoodsteinPA.StdCor34
