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

namespace GoodsteinPA.StdCor34

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open GoodsteinPA GoodsteinPA.InternalONote GoodsteinPA.IIter GoodsteinPA.InternalIg

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

end GoodsteinPA.StdCor34
