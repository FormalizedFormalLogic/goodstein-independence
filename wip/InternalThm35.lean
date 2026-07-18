/-
# `InternalThm35.lean` — Rathjen 2014 Theorem 3.5, the M-internal block-tail (codes)

**Rathjen "Goodstein revisited" Theorem 3.5 (PA).** From a *slow* descending ε₀-sequence
`α₀ ≻ α₁ ≻ …` (slow: `C(αₙ) ≤ K·(n+1)`) one builds a descending sequence `β₀ ≻ β₁ ≻ …` with the
*tight* canonical-form bound `C(βᵣ) ≤ r+1`, by the reindex

  `β_{K·(n+1)+i} := ω·αₙ + (K−i)`     (`n < ω`, `0 ≤ i < K`).

This file builds the **block-tail** of that sequence — the indices `r ≥ K`, where the reindex
`r ↦ (n,i)` is `n = (r−K)/K`, `i = (r−K)%K` (internal division in `V ⊧ 𝗜𝚺₁`). It proves the three
load-bearing facts of Thm 3.5 for these indices, all from the existing single-step toolkit
(`icmp_betaTail_within`/`icmp_betaTail_boundary`/`isNF_iadd_finite`/`iC_betaTail_le`):

* `bbtail_isNF`    — every `βᵣ` is a valid NF code;
* `bbtail_C_le`    — the *tight* slowness `C(βᵣ) ≤ r+1` (Thm 3.5's headline bound, exact);
* `bbtail_desc`    — strict `≺`-descent `β_{r+1} ≺ βᵣ` (within-block and block-boundary cases).

It is **level-agnostic** (no Grzegorczyk `g`, no Ackermann) and so route-independent: it consumes a
slow descent and is reused by both the Con(PA) route (Rathjen Cor 3.7 / Thm 2.8) and any model-internal
descent argument. The deep crux that *produces* the slow input `α` is Cor 3.4 (the internal
Grzegorczyk `g`-padding, internal level `l : V`); the finite ω-tower **prefix** `r < K` (Rathjen's
`βⱼ = Σ_{i} ω_{s−i}`) — which fills indices `0..K−1` down to `β_K`, needing an internal ω-tower on
codes — is the one remaining piece toward a single sequence indexed from `0`. See
`route-resolved-prwo-gentzen` (memory) and `PENDING_WORK.md`.
-/
import GoodsteinPA.InternalCor34
import GoodsteinPA.Compat

namespace GoodsteinPA.InternalONote

open LO LO.FirstOrder LO.FirstOrder.Arithmetic

variable {V : Type*} [ORingStructure V] [V ⊧ₘ* 𝗜𝚺₁]

/-- **Thm 3.5 block-tail term** (codes, internal index `r ≥ K`). With `q = r − K`,
`n = q/K`, `i = q%K`, this is `βᵣ = ω·αₙ + (K − i)`. -/
noncomputable def bbtail (K : V) (α : V → V) (r : V) : V :=
  iadd (iomul (α ((r - K) / K))) (ocOadd 0 (K - (r - K) % K) 0)

/-- `(r−K)%K < K`, hence `K − (r−K)%K ≥ 1`, so the finite tail `K − (r−K)%K` is nonzero. -/
private lemma sub_mod_pos {K : V} (hK : 0 < K) (r : V) : 0 < K - (r - K) % K :=
  pos_sub_iff_lt.mpr (mod_lt _ hK)

/-- **Thm 3.5, NF invariant.** Every block-tail term is a valid normal-form code. -/
theorem bbtail_isNF {K : V} (hK : 0 < K) {α : V → V} (hNF : ∀ n, isNF (α n)) (r : V) :
    isNF (bbtail K α r) :=
  isNF_iadd_finite (hNF _) (sub_mod_pos hK r).ne'

/-- **Thm 3.5, tight slowness bound** `C(βᵣ) ≤ r + 1` for `r ≥ K`. The reindex makes the generic
`K·(n+1)+i+1` bound (`iC_betaTail_le`) collapse to exactly `r+1`, because `K·(q/K)+q%K = q = r−K`. -/
theorem bbtail_C_le {K : V} {α : V → V} (hslow : ∀ n, iC (α n) ≤ K * (n + 1)) {r : V} (hr : K ≤ r) :
    iC (bbtail K α r) ≤ r + 1 := by
  have hbound := iC_betaTail_le (c := α ((r - K) / K)) (K := K)
    (n := (r - K) / K) (i := (r - K) % K) (hslow _)
  refine le_trans hbound (le_of_eq ?_)
  -- `K·(q/K + 1) + q%K + 1 = q + K + 1 = r + 1`, using `K·(q/K) + q%K = q` and `(r−K)+K = r`.
  have hdm : K * ((r - K) / K) + (r - K) % K = r - K := div_add_mod (r - K) K
  have hrK : (r - K) + K = r := sub_add_self_of_le hr
  calc K * ((r - K) / K + 1) + (r - K) % K + 1
      = (K * ((r - K) / K) + (r - K) % K) + K + 1 := by
        rw [mul_add, mul_one, add_right_comm (K * ((r - K) / K)) K ((r - K) % K)]
    _ = (r - K) + K + 1 := by rw [hdm]
    _ = r + 1 := by rw [hrK]

/-- **Thm 3.5, strict descent** `β_{r+1} ≺ βᵣ` for `r ≥ K`. The reindex successor `r ↦ r+1` either
stays within a block (`i+1 < K`: same `ω·αₙ` head, the finite tail drops by one — `icmp_betaTail_within`)
or crosses a block boundary (`i+1 = K`: `α_{n+1} ≺ αₙ` drops the head — `icmp_betaTail_boundary`).
The whole case split is internal division: `(q+1)/K`, `(q+1)%K` from `q/K`, `q%K` (`q = r−K`). -/
theorem bbtail_desc {K : V} (hK : 0 < K) {α : V → V} (hNF : ∀ n, isNF (α n))
    (hdesc : ∀ n, icmp (α (n + 1)) (α n) = 0) {r : V} (hr : K ≤ r) :
    icmp (bbtail K α (r + 1)) (bbtail K α r) = 0 := by
  -- `(r+1) − K = (r−K) + 1`.
  have hq1 : (r + 1) - K = (r - K) + 1 := by
    have h1 : r + 1 = ((r - K) + 1) + K := by rw [add_right_comm, sub_add_self_of_le hr]
    rw [h1, add_sub_self]
  simp only [bbtail]
  rw [hq1]
  set q := r - K with hq
  set n := q / K with hn
  set i := q % K with hi
  have hi_lt : i < K := mod_lt q hK
  have hdm : K * n + i = q := div_add_mod q K
  -- `q + 1 = K·n + (i+1)`.
  have hexp : q + 1 = K * n + (i + 1) := by rw [← add_assoc, hdm]
  rcases lt_or_eq_of_le (show i + 1 ≤ K from succ_le_iff_lt.mpr hi_lt) with hcase | hcase
  · -- within-block: `i+1 < K`
    have hquot : (q + 1) / K = n := by rw [hexp]; exact div_mul_add' n K hcase
    have hmod : (q + 1) % K = i + 1 := by
      rw [hexp, mod_mul_add' n (i + 1) hK, mod_eq_self_of_lt hcase]
    have hKi : (K - (i + 1)) + 1 = K - i := by
      rw [← Arithmetic.sub_sub]
      exact sub_add_self_of_le (Arithmetic.one_le_of_zero_lt _ (pos_sub_iff_lt.mpr hi_lt))
    rw [hquot, hmod, ← hKi]
    exact icmp_betaTail_within (α n) (K - (i + 1))
  · -- block boundary: `i+1 = K`
    have hexpB : q + 1 = K * (n + 1) := by rw [hexp, hcase, mul_add, mul_one]
    have hquot : (q + 1) / K = n + 1 := by rw [hexpB]; exact div_mul' (n + 1) hK
    have hmod : (q + 1) % K = 0 := by rw [hexpB]; exact mod_mul_self_right (n + 1) K
    rw [hquot, hmod, Arithmetic.sub_zero]
    exact icmp_betaTail_boundary (hNF (n + 1)) (hNF n) (hdesc n) K (K - i)

/-! ## Internal ω-tower `ωₙ` on codes — toward the Thm 3.5 prefix (`r < K`)

Rathjen's prefix `βⱼ = Σ_{i} ω_{s−i}` (indices `0..K−1`) needs the ε₀ ω-tower `ω₀ = 1`,
`ω_{n+1} = ω^{ωₙ}` with an **internal** index (the slowness constant `K : V` is internal). On codes
`ω^c = ocOadd c 1 0`, so the tower is the structural recursion `iwtower (n+1) = ocOadd (iwtower n) 1 0`
— `𝚺₁`-definable and **IΣ₁-total** (the code has size linear in `n`, no Ackermann). Each tower is a
valid NF code with the single coefficient `1` (`iC = 1`). -/

/-- Blueprint for the ω-tower: `ω₀ = ocOadd 0 1 0 (= 1)`, `ω_{n+1} = ocOadd (ωₙ) 1 0 (= ω^{ωₙ})`. -/
def iwtower.blueprint : PR.Blueprint 0 where
  zero := .mkSigma “y. !ocOaddDef y 0 1 0”
  succ := .mkSigma “y ih n. !ocOaddDef y ih 1 0”

noncomputable def iwtower.construction : PR.Construction V iwtower.blueprint where
  zero := fun _ ↦ ocOadd 0 1 0
  succ := fun _ _ ih ↦ ocOadd ih 1 0
  zero_defined := .mk fun v ↦ by simp [iwtower.blueprint, ocOadd_defined.iff]
  succ_defined := .mk fun v ↦ by simp [iwtower.blueprint, ocOadd_defined.iff]

/-- **Internal ω-tower** `iwtower n = ωₙ` on codes inside `V ⊧ 𝗜𝚺₁`. -/
noncomputable def iwtower (n : V) : V := iwtower.construction.result ![] n

@[simp] lemma iwtower_zero : iwtower (0 : V) = ocOadd 0 1 0 := by
  simp [iwtower, iwtower.construction]

@[simp] lemma iwtower_succ (n : V) : iwtower (n + 1) = ocOadd (iwtower n) 1 0 := by
  simp [iwtower, iwtower.construction]

def _root_.LO.FirstOrder.Arithmetic.iwtowerDef : 𝚺₁.Semisentence 2 :=
  iwtower.blueprint.resultDef.rew (Rew.subst ![#0, #1])

instance iwtower_defined : 𝚺₁-Function₁ (iwtower : V → V) via iwtowerDef := .mk
  fun v ↦ by simp [iwtower.construction.result_defined_iff, iwtowerDef]; rfl

instance iwtower_definable : 𝚺₁-Function₁ (iwtower : V → V) := iwtower_defined.to_definable

instance iwtower_definable' (Γ) : Γ-[m + 1]-Function₁ (iwtower : V → V) :=
  iwtower_definable.of_sigmaOne

/-- **Every ω-tower is a valid NF code.** -/
lemma isNF_iwtower (n : V) : isNF (iwtower n) := by
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero =>
    rw [iwtower_zero, isNF_ocOadd]
    exact ⟨_root_.one_ne_zero, isNF_zero, isNF_zero, Or.inl rfl⟩
  case succ n ih =>
    rw [iwtower_succ, isNF_ocOadd]
    exact ⟨_root_.one_ne_zero, ih, isNF_zero, Or.inl rfl⟩

/-- **Each ω-tower has coefficient bound `1`** (`C(ωₙ) = 1`). -/
lemma iC_iwtower (n : V) : iC (iwtower n) = 1 := by
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero =>
    rw [iwtower_zero, iC_ocOadd, iC_zero]
    simp
  case succ n ih =>
    rw [iwtower_succ, iC_ocOadd, iC_zero, ih]
    simp

/-- **A strictly smaller leading exponent decides `≺` outright** (CNF lexicographic head):
`icmp e₁ e₂ = 0 ⟹ ocOadd e₁ n₁ r₁ ≺ ocOadd e₂ n₂ r₂`, since `thenV 0 _ = 0`. -/
lemma icmp_ocOadd_lt_exp {e1 n1 r1 e2 n2 r2 : V} (h : icmp e1 e2 = 0) :
    icmp (ocOadd e1 n1 r1) (ocOadd e2 n2 r2) = 0 := by
  rw [icmp_ocOadd, h]; simp [thenV]

/-- **The ω-tower strictly increases**: `ωₙ ≺ ω_{n+1}` (i.e. `icmp ωₙ ω_{n+1} = 0`). Each step is a
head-exponent drop (`ωₙ` is the exponent of `ω_{n+1} = ω^{ωₙ}`), so `icmp_ocOadd_lt_exp` applies with
the previous step's comparison. -/
lemma icmp_iwtower_succ (n : V) : icmp (iwtower n) (iwtower (n + 1)) = 0 := by
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero =>
    rw [iwtower_succ, iwtower_zero]
    exact icmp_ocOadd_lt_exp (icmp_zero_ocOadd 0 1 0)
  case succ n ih =>
    rw [iwtower_succ (n + 1)]
    nth_rewrite 1 [iwtower_succ n]
    exact icmp_ocOadd_lt_exp ih

/-- **ω-tower cofinality in ε₀.** Every code is dominated by some ω-tower:
`∀ c, ∃ s, c ≺ ωₛ` (`icmp c (iwtower s) = 0`). No NF hypothesis is needed — the comparison
`icmp_ocOadd_lt_exp` only reads the *leading exponent*, so a single `≺`-witness on the exponent
(supplied by the strong-induction hypothesis at `ocExp c < c`) decides the whole code. The witness
`s` is the iterated-exponent depth of `c`. This discharges the seam hypothesis `hbdry` of
`bbeta_desc` (memory `route-resolved-prwo-gentzen`; PENDING_WORK lap-46 §4). -/
theorem iwtower_cofinal (c : V) : ∃ s, icmp c (iwtower s) = 0 := by
  induction c using ISigma1.sigma1_order_induction
  · definability
  case ind c IH =>
    rcases eq_or_ne c 0 with rfl | hc
    · exact ⟨0, by rw [iwtower_zero]; exact icmp_zero_ocOadd 0 1 0⟩
    · obtain ⟨se, hse⟩ := IH (ocExp c) (ocExp_lt_of_pos (pos_iff_ne_zero.mpr hc))
      refine ⟨se + 1, ?_⟩
      rw [← ocOadd_destruct hc, iwtower_succ]
      exact icmp_ocOadd_lt_exp hse

/-! ## The full Thm 3.5 sequence `β` indexed from `0` (prefix + block-tail)

The finite prefix `r < K` is **simplified** from Rathjen's `Σ_i ω_{s−i}` to *single* ω-towers
`βⱼ = ω_{s+K−1−j}` — valid because `C` is the *max coefficient* (not the term count), so a single
tower already has `C = 1 ≤ j+1`. Consecutive towers strictly descend (`icmp_iwtower_succ`), the prefix
bottom `β_{K−1} = ωₛ` sits above the block top `β_K` (the boundary hypothesis `hbdry`, an instance of
ω-tower cofinality in ε₀), and the block-tail `r ≥ K` is `bbtail`. This is the complete Thm 3.5
output: a single sequence indexed from `0` with strict ≺-descent and the tight `C(βᵣ) ≤ r+1`, modulo
the one disclosed cofinality input `hbdry`. -/

/-- **Thm 3.5 full sequence** (codes, indexed from `0`): the ω-tower prefix for `r < K`, the
slow-down block-tail for `r ≥ K`. `s` is the tower height with `β_K ≺ ωₛ`. -/
noncomputable def bbeta (K s : V) (α : V → V) (r : V) : V :=
  if r < K then iwtower (s + (K - 1 - r)) else bbtail K α r

section
variable {K s : V} {α : V → V}

/-- **Thm 3.5 (full), NF invariant.** -/
theorem bbeta_isNF (hK : 0 < K) (hNF : ∀ n, isNF (α n)) (r : V) : isNF (bbeta K s α r) := by
  unfold bbeta
  split
  · exact isNF_iwtower _
  · exact bbtail_isNF hK hNF r

/-- **Thm 3.5 (full), tight slowness** `C(βᵣ) ≤ r+1` for all `r`. Prefix: `C = 1 ≤ r+1`. Block: `bbtail_C_le`. -/
theorem bbeta_C_le (hslow : ∀ n, iC (α n) ≤ K * (n + 1)) (r : V) : iC (bbeta K s α r) ≤ r + 1 := by
  unfold bbeta
  split
  · rw [iC_iwtower]; exact le_add_self
  · rename_i h; exact bbtail_C_le hslow (not_lt.mp h)

/-- **Thm 3.5 (full), strict descent** `β_{r+1} ≺ βᵣ` for all `r`. Three cases: prefix→prefix
(consecutive towers), prefix→block at the seam `r = K−1` (the boundary `hbdry`), block→block
(`bbtail_desc`). -/
theorem bbeta_desc (hK : 0 < K) (hNF : ∀ n, isNF (α n)) (hdesc : ∀ n, icmp (α (n + 1)) (α n) = 0)
    (hbdry : icmp (bbtail K α K) (iwtower s) = 0) (r : V) :
    icmp (bbeta K s α (r + 1)) (bbeta K s α r) = 0 := by
  unfold bbeta
  by_cases hrK : r + 1 < K
  · -- prefix → prefix: consecutive towers `ω_{s+K-1-(r+1)} ≺ ω_{s+K-1-r}`
    have hr : r < K := lt_trans (lt_add_one r) hrK
    rw [if_pos hrK, if_pos hr]
    -- `K-1-(r+1) = (K-1-r)-1` and `s+(K-1-r) = (s+(K-1-r)-1)+1`
    have hlt1 : r < K - 1 := lt_of_lt_of_le (lt_add_one r) (le_sub_one_of_lt hrK)
    have hpos : 0 < K - 1 - r := pos_sub_iff_lt.mpr hlt1
    have hsub : K - 1 - (r + 1) = K - 1 - r - 1 := (Arithmetic.sub_sub).symm
    have hsucc : (s + (K - 1 - r - 1)) + 1 = s + (K - 1 - r) := by
      rw [add_assoc, sub_add_self_of_le (Arithmetic.one_le_of_zero_lt _ hpos)]
    rw [hsub, ← hsucc]
    exact icmp_iwtower_succ (s + (K - 1 - r - 1))
  · by_cases hr : r < K
    · -- prefix → block at the seam `r = K-1`, so `r+1 = K`
      have heq : r + 1 = K := le_antisymm (succ_le_iff_lt.mpr hr) (not_lt.mp hrK)
      rw [if_neg hrK, if_pos hr, heq]
      -- `β_{K-1} = ω_{s + (K-1-(K-1))} = ω_s`
      have h0 : K - 1 - r = 0 := by
        have : K - 1 = r := by rw [← heq]; simp
        rw [this, Arithmetic.sub_self]
      rw [h0, add_zero]
      exact hbdry
    · -- block → block
      have hKr : K ≤ r := not_lt.mp hr
      rw [if_neg hrK, if_neg hr]
      exact bbtail_desc hK hNF hdesc hKr

/-- **Thm 3.5 (full), strict descent — boundary discharged.** The seam hypothesis `hbdry` of
`bbeta_desc` is exactly `β_K ≺ ω_s`, which ω-tower cofinality (`iwtower_cofinal`) supplies for a
suitable `s` applied to the block top `bbtail K α K`. So the complete descending Thm 3.5 sequence
exists *unconditionally* (a height `s` and `β = bbeta K s α` with strict ≺-descent at every index).
The NF and tight-slowness facts (`bbeta_isNF`, `bbeta_C_le`) hold for this same `s`. -/
theorem bbeta_desc_exists (hK : 0 < K) (hNF : ∀ n, isNF (α n))
    (hdesc : ∀ n, icmp (α (n + 1)) (α n) = 0) :
    ∃ s, ∀ r, icmp (bbeta K s α (r + 1)) (bbeta K s α r) = 0 := by
  obtain ⟨s, hs⟩ := iwtower_cofinal (bbtail K α K)
  exact ⟨s, fun r => bbeta_desc hK hNF hdesc hs r⟩
end

end GoodsteinPA.InternalONote
