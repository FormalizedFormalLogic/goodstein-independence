/-
# `Thm56.lean` — Gentzen 1943 sharpness: `𝗣𝗔 ⊬ TI_≺(X)` (Buchholz Thm 5.6), assembled

This file **assembles** the entire Buchholz §5 girder into the single headline-route theorem
`peano_not_proves_TI : IsEmpty (Derivation2 paLX {TI_≺(X)})` — Peano arithmetic (in the set-variable
language `LX`, with induction extended to all `LX`-formulas) does **not** prove transfinite induction
along the CNF-ε₀ order `≺`. It then reduces the headline `𝗣𝗔 ⊬ ↑goodsteinSentence` to the **one**
remaining wall **E** (the Goodstein-to-`TI(ε₀)` descent in PA).

## The chain (all pieces axiom-clean except the two disclosed walls)

A hypothetical `Derivation2 paLX {TI prec}` (a `Z ⊢ TI_≺(X)` proof) is pushed through:

1. **C₂** (`embedC_LX` + `hax_paLX`, lap 20, axiom-clean) — embed it into the cut-rank-carrying
   `XFreeAx` `Z∞` carrier `PXFc`. Since `prec` is the `lMap` of a *sentence* (`Seam.φ = emb precφ`,
   `precφ : Semisentence ℒₒᵣ 2`), `TI prec` is free-variable-free, so `asgX e` fixes it
   (`asgX_TI_fix`) and the assignment-indexed image collapses to `{TI prec}`.
2. **D'** (`embed_TI_bounded`, THIS FILE, the one new disclosed `sorry`) — the embedded ordinal is
   `< ε₀`. This is *the* content of Gentzen's theorem: a **finite** PA-proof embeds to a `Z∞`-proof of
   ordinal height `< ε₀` (the ε₀ "wall" is exactly that PA cannot certify heights up to ε₀ itself).
   `embedC_LX` currently forgets the bound (`∃ α` with no `< ε₀`); discharging D' = re-running the
   embedding with a *uniform* (assignment-independent) ordinal bound `∃ B < ε₀, ∀ e, ∃ α ≤ B, …` —
   the ω-rule case closes because the IH's bound sits outside `∀ e`. Pure ordinal bookkeeping, no
   literature. See `PENDING_WORK.md`.
3. **C₁ + D** (`orderType_le_of_TIprovable`, axiom-clean) — cut-eliminate, then Boundedness (Thm 5.4):
   `PXFc α c {TI prec} ⟹ ‖≺‖ ≤ 2^(ω_c^α)`.
4. **F** (`seam`, axiom-clean modulo the F-φ comparison axiom on Aristotle) — `ε₀ ≤ ‖≺‖`.

Combining: `ε₀ ≤ ‖≺‖ ≤ 2^(ω_c^α) < ε₀` (the last `<` because `α < ε₀` ⟹ `ω_c^α < ε₀` ⟹
`2^(ω_c^α) < ε₀`), a contradiction. Hence no such derivation exists.

`#print axioms peano_not_proves_TI` carries exactly: the trust base, `rePred_ltPull_natCode` (F-φ,
Aristotle), and `embed_TI_bounded`'s `sorryAx` (D'). NOT wired to the headline `sorry` (anti-fraud).
-/
import GoodsteinPA.XFreeCutElim
import GoodsteinPA.EmbeddingX
import GoodsteinPA.EmbeddingBound
import GoodsteinPA.SeamDefinability
import GoodsteinPA.Reduction

namespace GoodsteinPA.Thm56

open scoped Ordinal
open LO LO.FirstOrder
open GoodsteinPA.ZinftyGen GoodsteinPA.LangX GoodsteinPA.XFreeCutElim
open GoodsteinPA.Boundedness GoodsteinPA.EmbeddingX GoodsteinPA.EpsilonOrder GoodsteinPA.TruthSem

/-- The concrete CNF-ε₀ order formula `≺` of the seam, as a depth-2 `LX`-formula. -/
noncomputable def prec : Semiformula LX ℕ 2 := Seam.prec SeamDefinability.seam

/-- `prec` is free-variable-free: it is the `lMap` of `Rewriting.emb precφ`, and `precφ` is a
`Semisentence` (no free variables), a property both `lMap` and the rewrite-only-touches-fvars
machinery preserve. -/
@[simp] theorem freeVariables_prec : prec.freeVariables = ∅ := by
  simp only [prec, Seam.prec, SeamDefinability.seam, Semiformula.freeVariables_lMap,
    Semiformula.freeVariables_emb]

/-- `TI prec` is free-variable-free (built from `prec` under binders, which only shrink the bound
de Bruijn count and never introduce free `ℕ`-variables). -/
@[simp] theorem freeVariables_TI : (TI prec).freeVariables = ∅ := by
  simp [TI, Prog, hyp, Xat, Semiformula.imp_eq, Semiformula.freeVariables_rel,
    Semiformula.freeVariables_nrel, freeVariables_prec]

/-- **The assignment fixes `TI prec`.** `asgX e = Rew.rewrite (nm ∘ e)` only rewrites free
`ℕ`-variables, of which `TI prec` has none; so it acts as the identity. This is what collapses the
embedding's assignment-indexed image `{TI prec}.image (asgX e ▹ ·)` back to `{TI prec}`. -/
theorem asgX_TI_fix (e : ℕ → ℕ) : asgX e ▹ (TI prec) = TI prec := by
  apply Semiformula.rew_eq_self_of
  · intro x; exact x.elim0
  · intro x hx
    simp [Semiformula.FVar?, freeVariables_TI] at hx

/-- The seam order's wellfoundedness, as an instance for `orderType`/`rk` resolution. -/
instance : IsWellFounded ℕ SeamDefinability.seam.lt := SeamDefinability.seam.wf

/-- **C₂ collapsed to `{TI prec}`.** A `Z ⊢ TI_≺(X)` proof embeds (via `embedC_LX`/`hax_paLX`) to a
`PXFc`-derivation of the singleton `{TI prec}` itself (the assignment image collapses by
`asgX_TI_fix`). Existential in the ordinal — the `< ε₀` bound is the separate `embed_TI_bounded`. -/
theorem embed_TI (d : Derivation2 (paLX : Theory LX) {TI prec}) :
    ∃ (c : ℕ) (α : Ordinal.{0}), PXFc α c ({TI prec} : Seq LX) := by
  obtain ⟨c, hc⟩ := embedC_LX hax_paLX d
  obtain ⟨α, hα⟩ := hc id
  refine ⟨c, α, ?_⟩
  rwa [show ({TI prec} : Seq LX).image (fun ψ => asgX id ▹ ψ) = {TI prec} by
        rw [Finset.image_singleton, asgX_TI_fix]] at hα

/-- **D' — the embedded ordinal is `< ε₀` (DISCLOSED `sorry`; the next chip).** The finite PA-proof's
embedding lands at a `Z∞` ordinal `< ε₀`. This is the load-bearing Gentzen content the lap-20 handoff
omitted: `embedC_LX` forgets the bound. Discharge plan: strengthen `embedC_LX_gen` (and the axiom
discharge `hax_paLX` ⟵ `provable_em_x`, `metaInduction`) to the *uniform* conclusion
`∃ c, ∃ B < ε₀, ∀ e, ∃ α ≤ B, PXFc α c (…)`. Every builder bumps the bound by `+1`/`max+1`/`sup+1`, all
of which keep `B < ε₀` (ε₀ a limit); the ω-rule (`allω`) case closes precisely because the IH's `B`
sits *outside* `∀ e`, so the family `{α(n)}ₙ` is uniformly `≤ B`, hence `⨆ₙ α(n) + 1 ≤ B + 1 < ε₀`.
Pure ordinal bookkeeping, Foundation-light, no literature. -/
theorem embed_TI_bounded (d : Derivation2 (paLX : Theory LX) {TI prec}) :
    ∃ (c : ℕ) (α : Ordinal.{0}), α < ε₀ ∧ PXFc α c ({TI prec} : Seq LX) := by
  obtain ⟨c, B, hB, hpxfc⟩ := GoodsteinPA.EmbeddingBound.embedC_LX_bdd d
  refine ⟨c, B, hB, ?_⟩
  have h := hpxfc id
  rwa [show ({TI prec} : Seq LX).image (fun ψ => asgX id ▹ ψ) = {TI prec} by
        rw [Finset.image_singleton, asgX_TI_fix]] at h

/-- A small arithmetic helper: `2^β < ε₀` for `β < ε₀` (`2 ≤ ω`, then `ω^β < ε₀`). -/
theorem two_opow_lt_epsilon0 {β : Ordinal.{0}} (h : β < ε₀) : (2 : Ordinal) ^ β < ε₀ :=
  lt_of_le_of_lt
    (Ordinal.opow_le_opow_left β (by exact_mod_cast (Ordinal.natCast_lt_omega0 2).le))
    (Deriv.omega0_opow_lt_epsilon0 h)

/-- **Buchholz Thm 5.6 (Gentzen 1943 sharpness), assembled.** `𝗣𝗔` over `LX` (= Buchholz's `Z`) does
**not** prove transfinite induction `TI_≺(X)` along the CNF-ε₀ order. Modulo the two disclosed walls
(F-φ `rePred_ltPull_natCode`, Aristotle; D' `embed_TI_bounded`), this is axiom-clean and chains the
entire §5 girder: embedding (C₂) + cut-elimination (C₁) + Boundedness (D) + order-type ≥ ε₀ (F). -/
theorem peano_not_proves_TI : IsEmpty (Derivation2 (paLX : Theory LX) {TI prec}) := by
  refine ⟨fun d => ?_⟩
  obtain ⟨c, α, hα, hpxfc⟩ := embed_TI_bounded d
  have hbound : orderType SeamDefinability.seam.lt ≤ 2 ^ (Deriv.omegaTower c α) :=
    orderType_le_of_TIprovable SeamDefinability.seam.lt prec
      (SeamDefinability.seam.hprec) (SeamDefinability.seam.hprecXPos) hpxfc
  have hge : ε₀ ≤ orderType SeamDefinability.seam.lt := SeamDefinability.seam.ge
  have hlt : (2 : Ordinal) ^ (Deriv.omegaTower c α) < ε₀ :=
    two_opow_lt_epsilon0 (Deriv.omegaTower_lt_epsilon0 c hα)
  exact absurd (hge.trans hbound) (not_le.mpr hlt)

/-! ## G — reduce the headline to the descent wall E

`E` is the Goodstein-to-`TI(ε₀)` descent *inside* PA: from a PA-proof of the Goodstein sentence,
produce a `Z`-proof (`Derivation2 paLX`) of `TI_≺(X)` for the seam order. Given `E`, Thm 5.6 closes
the headline by contradiction. The headline `sorry` in `Statement.lean` stays put until `E` is real
(anti-fraud: discharge it only when `#print axioms` is clean). -/

/-- **The descent wall E (interface).** From a PA proof of the Goodstein sentence, a `Z`-derivation of
`TI_≺(X)` along the seam's CNF-ε₀ order. This is the sole remaining unstarted girder. -/
def DescentE : Prop :=
  𝗣𝗔 ⊢ ↑goodsteinSentence → Nonempty (Derivation2 (paLX : Theory LX) {TI prec})

/-- **G — the headline, reduced to E.** If the descent `E` holds, then `𝗣𝗔 ⊬ ↑goodsteinSentence`:
a proof of `γ` would yield (by `E`) a `Z`-proof of `TI_≺(X)`, contradicting Thm 5.6. This does NOT
discharge the headline `sorry` — it pins exactly what `E` must deliver. -/
theorem peano_not_proves_goodstein_of_descent (hE : DescentE) :
    𝗣𝗔 ⊬ ↑goodsteinSentence :=
  fun h => peano_not_proves_TI.false (hE h).some

end GoodsteinPA.Thm56
