/-
# `EmbeddingBound.lean` — D': the embedded ordinal is `< ε₀`

The headline-route theorem `Thm56.peano_not_proves_TI` is axiom-clean modulo F-φ **and** the disclosed
`Thm56.embed_TI_bounded` (D'): a **finite** PA-proof embeds to a `Z∞`-proof of ordinal height `< ε₀`.
This is *the* Gentzen content (PA cannot certify heights up to ε₀ itself); `embedC_LX` forgets the
bound (`∃ α` with no `< ε₀`). This file re-runs the embedding tracking a **uniform** ordinal bound.

## Strategy

The ω-rule (`PXFc.allω`) maps a family `{α(n)}ₙ` to `(⨆ₙ α(n)) + 1`. For the result to stay `< ε₀` the
family must be **uniformly** bounded below ε₀ — and a plain existential `∃ α(n) < ε₀` is NOT enough (the
α(n) could climb to ε₀). The fix everywhere: carry a bound determined by *complexity / structure*, not
by the instantiation, so the family is **constant** in `n`.

- **`provable_em_x_bdd`** (this file): the `Z∞` excluded middle for `φ` has ordinal `≤ 2·complexity φ`,
  a **finite** ordinal. Its own ω-rule case (nested quantifiers) closes because the sub-family is at the
  constant complexity-bound `2·(k-1)+1`, so `⨆ₙ const = const`.

Downstream chips (next laps): `provable_true_x_bdd`, `exI_closed_bdd`, `metaInduction_cong_bdd`,
`PXFc_allClosure_bdd`, then `embedC_LX_gen_bdd` (10 cases) + `hax_paLX_bdd`, then discharge
`embed_TI_bounded`.
-/
import GoodsteinPA.XFreeCutElim
import GoodsteinPA.EmbeddingX
import GoodsteinPA.Epsilon0Complete

namespace GoodsteinPA.EmbeddingBound

open scoped Ordinal
open LO LO.FirstOrder
open GoodsteinPA.ZinftyGen GoodsteinPA.LangX GoodsteinPA.XFreeCutElim GoodsteinPA.EmbeddingX

/-- `⨆ₙ c = c` over `ℕ` (constant family), specialised to `Ordinal`. -/
private theorem iSup_const_ord (c : Ordinal.{0}) : (⨆ _ : ℕ, c) = c := ciSup_const

/-! ## ε₀-closure helpers + the `PXFcFin` / `PXFcLt` bound-tracking layer

`PXFcFin c Γ` = "derivable with a **finite** (natural-number) ordinal height", closed under every
structural builder + the ω-rule **with a uniform finite family**. `PXFcLt c Γ` = "derivable with
height `< ε₀`". The single transfinite jump (the ω-rule over a *non*-constant finite family, as in
`metaInduction`) is `PXFcLt.allω_fin` : `⨆ₙ (↑N n) ≤ ω < ε₀`. -/

open GoodsteinPA.Epsilon0Complete (isSuccLimit_epsilon0)

/-- ε₀ is closed under successor (it is a limit ordinal). -/
theorem add_one_lt_epsilon0 {B : Ordinal.{0}} (h : B < ε₀) : B + 1 < ε₀ := by
  rw [← Order.succ_eq_add_one]; exact isSuccLimit_epsilon0.succ_lt h

/-- `ω < ε₀`. -/
theorem omega0_lt_epsilon0 : Ordinal.omega0 < ε₀ := Ordinal.omega0_lt_epsilon 0

/-- Naturals are `< ε₀`. -/
theorem natCast_lt_epsilon0 (n : ℕ) : (n : Ordinal.{0}) < ε₀ := Ordinal.natCast_lt_epsilon n 0

/-- `↑(max a b) = max ↑a ↑b` in `Ordinal`. -/
private theorem natCast_max (a b : ℕ) : ((max a b : ℕ) : Ordinal.{0}) = max (a : Ordinal) b :=
  Nat.mono_cast.map_max

/-- A finite-height `PXFc` derivation (natural-number ordinal). -/
def PXFcFin (c : ℕ) (Γ : Seq LX) : Prop := ∃ N : ℕ, PXFc (N : Ordinal) c Γ

/-- A `PXFc` derivation of height `< ε₀`. -/
def PXFcLt (c : ℕ) (Γ : Seq LX) : Prop := ∃ α : Ordinal.{0}, α < ε₀ ∧ PXFc α c Γ

theorem PXFcFin.toLt {c Γ} (h : PXFcFin c Γ) : PXFcLt c Γ := by
  obtain ⟨N, hN⟩ := h; exact ⟨_, natCast_lt_epsilon0 N, hN⟩

theorem PXFcFin.mono_c {c c' Γ} (hc : c ≤ c') (h : PXFcFin c Γ) : PXFcFin c' Γ := by
  obtain ⟨N, hN⟩ := h; exact ⟨N, hN.mono le_rfl hc⟩

theorem PXFcFin.weakening {c Γ Δ} (h : Γ ⊆ Δ) (hd : PXFcFin c Γ) : PXFcFin c Δ := by
  obtain ⟨N, hN⟩ := hd; exact ⟨N, hN.weakening h⟩

theorem PXFcFin.verumR {c Γ} (h : (⊤ : Form LX) ∈ Γ) : PXFcFin c Γ :=
  ⟨0, (PXFc.verumR h).mono (by simp) (Nat.zero_le c)⟩

theorem PXFcFin.axLv {c Γ k} (r : LX.Rel k) (v v' : Fin k → Semiterm LX ℕ 0)
    (hval : ∀ i, Semiterm.valm ℕ ![] (id : ℕ → ℕ) (v i)
              = Semiterm.valm ℕ ![] (id : ℕ → ℕ) (v' i))
    (hp : Semiformula.rel r v ∈ Γ) (hn : Semiformula.nrel r v' ∈ Γ) : PXFcFin c Γ :=
  ⟨0, (PXFc.axLv r v v' hval hp hn).mono (by simp) (Nat.zero_le c)⟩

theorem PXFcFin.axTrue {c Γ k} (b : Bool) (r : LX.Rel k) (v) (hxfree : Sum.isLeft r = true)
    (htrue : LitTrue (signedLit b r v)) (hmem : signedLit b r v ∈ Γ) : PXFcFin c Γ :=
  ⟨0, (PXFc.axTrue b r v hxfree htrue hmem).mono (by simp) (Nat.zero_le c)⟩

theorem PXFcFin.andI {c Γ} (φ ψ : Form LX) (hφ : PXFcFin c (insert φ Γ))
    (hψ : PXFcFin c (insert ψ Γ)) : PXFcFin c (insert (φ ⋏ ψ) Γ) := by
  obtain ⟨N1, h1⟩ := hφ; obtain ⟨N2, h2⟩ := hψ
  refine ⟨max N1 N2 + 1, ?_⟩
  have := PXFc.andI φ ψ h1 h2
  rwa [← natCast_max, ← Nat.cast_add_one] at this

theorem PXFcFin.orI {c Γ} (φ ψ : Form LX) (h : PXFcFin c (insert φ (insert ψ Γ))) :
    PXFcFin c (insert (φ ⋎ ψ) Γ) := by
  obtain ⟨N, hN⟩ := h
  exact ⟨N + 1, by rw [Nat.cast_add_one]; exact PXFc.orI φ ψ hN⟩

theorem PXFcFin.exI {c Γ} (φ : SyntacticSemiformula LX 1) (n : ℕ)
    (h : PXFcFin c (insert (φ/[nm n]) Γ)) : PXFcFin c (insert (∃⁰ φ) Γ) := by
  obtain ⟨N, hN⟩ := h
  exact ⟨N + 1, by rw [Nat.cast_add_one]; exact PXFc.exI φ n hN⟩

theorem PXFcFin.cut {c : ℕ} {Γ} (χ : Form LX) (hc : (χ.complexity + 1 : ℕ∞) ≤ (c : ℕ∞))
    (h₁ : PXFcFin c (insert χ Γ)) (h₂ : PXFcFin c (insert (∼χ) Γ)) : PXFcFin c Γ := by
  obtain ⟨N1, h1⟩ := h₁; obtain ⟨N2, h2⟩ := h₂
  refine ⟨max N1 N2 + 1, ?_⟩
  have := PXFc.cut χ hc h1 h2
  rwa [← natCast_max, ← Nat.cast_add_one] at this

/-- The ω-rule with a **uniform finite** family: every premise at the same finite height `N`. -/
theorem PXFcFin.allω_unif {c Γ} (φ : SyntacticSemiformula LX 1) (N : ℕ)
    (h : ∀ n, PXFc (N : Ordinal) c (insert (φ/[nm n]) Γ)) : PXFcFin c (insert (∀⁰ φ) Γ) := by
  refine ⟨N + 1, ?_⟩
  rw [Nat.cast_add_one]
  have := PXFc.allω (β := fun _ => (N : Ordinal)) φ (Γ := Γ) h
  rwa [iSup_const_ord] at this

/-- **The single transfinite jump**, explicit form: the ω-rule over a *non*-constant finite family
lands uniformly at height `ω + 1` (each premise `↑N n ≤ ω`). This explicit `ω + 1` is independent of
the family witnesses, so it survives being placed under further binders (`allClosure`). -/
theorem PXFc.allω_omega {c : ℕ} {Γ : Seq LX} (φ : SyntacticSemiformula LX 1)
    (h : ∀ n, PXFcFin c (insert (φ/[nm n]) Γ)) :
    PXFc (Ordinal.omega0 + 1) c (insert (∀⁰ φ) Γ) := by
  choose N hN using h
  refine (PXFc.allω (β := fun n => ((N n : ℕ) : Ordinal)) φ hN).mono ?_ le_rfl
  gcongr
  exact Ordinal.iSup_le (fun n => (Ordinal.natCast_lt_omega0 (N n)).le)

/-- `ω + 1 < ε₀`. -/
theorem omega0_add_one_lt_epsilon0 : (Ordinal.omega0 : Ordinal.{0}) + 1 < ε₀ :=
  add_one_lt_epsilon0 omega0_lt_epsilon0

/-- **Bounded `Z∞` excluded middle over `LX`.** The cut-free `XFreeAx` derivation of `{φ, ∼φ}` has
**finite** ordinal `≤ 2·complexity φ`. The bound is complexity-determined (not instantiation-determined),
so the ω-rule case's numeral-family is constant — `⨆ₙ const = const` — and the ordinal stays finite.
Strengthens `XFreeCutElim.provable_em_x` (which forgot the bound). -/
theorem provable_em_x_bdd : ∀ (k : ℕ) (φ : Form LX), φ.complexity ≤ k →
    ∀ {Γ : Seq LX}, φ ∈ Γ → ∼φ ∈ Γ → PXFc ((2 * k : ℕ) : Ordinal) 0 Γ := by
  intro k
  induction k with
  | zero =>
    intro φ hk Γ hp hn
    have h0 : ((2 * 0 : ℕ) : Ordinal) = 0 := by norm_num
    rw [h0]
    cases φ using Semiformula.cases' with
    | hverum => exact PXFc.verumR hp
    | hfalsum => exact PXFc.verumR (by simpa using hn)
    | hrel r v => exact PXFc.axL r v hp (by simpa using hn)
    | hnrel r v => exact PXFc.axL r v (by simpa using hn) hp
    | hand φ ψ => simp at hk
    | hor φ ψ => simp at hk
    | hall φ => simp at hk
    | hexs φ => simp at hk
  | succ k ih =>
    intro φ hk Γ hp hn
    -- target ordinal `↑(2*(k+1)) = ↑(2*k) + 1 + 1`
    have hk2 : (2 * (k + 1) : ℕ) = (2 * k + 1) + 1 := by omega
    have hcast : ((2 * (k + 1) : ℕ) : Ordinal) = ((2 * k : ℕ) : Ordinal) + 1 + 1 := by
      rw [hk2]; simp only [Nat.cast_add, Nat.cast_one]
    cases φ using Semiformula.cases' with
    | hverum => exact (PXFc.verumR hp).mono (by simp) (le_refl 0)
    | hfalsum => exact (PXFc.verumR (by simpa using hn)).mono (by simp) (le_refl 0)
    | hrel r v => exact (PXFc.axL r v hp (by simpa using hn)).mono (by simp) (le_refl 0)
    | hnrel r v => exact (PXFc.axL r v (by simpa using hn) hp).mono (by simp) (le_refl 0)
    | hand φ ψ =>
      have hφk : φ.complexity ≤ k := by simp only [Semiformula.complexity_and] at hk; omega
      have hψk : ψ.complexity ≤ k := by simp only [Semiformula.complexity_and] at hk; omega
      have h1 := ih φ hφk (Γ := insert φ (insert (∼φ) (insert (∼ψ) Γ))) (by simp) (by simp)
      have h2 := ih ψ hψk (Γ := insert ψ (insert (∼φ) (insert (∼ψ) Γ))) (by simp) (by simp)
      have hand := PXFc.andI φ ψ h1 h2
      rw [Finset.insert_eq_self.mpr
        (show (φ ⋏ ψ) ∈ insert (∼φ) (insert (∼ψ) Γ) by simp [hp])] at hand
      have hor := PXFc.orI (∼φ) (∼ψ) hand
      rw [Finset.insert_eq_self.mpr (show (∼φ ⋎ ∼ψ) ∈ Γ by simpa using hn)] at hor
      -- hor : PXFc (max (↑(2k)) (↑(2k)) + 1 + 1) 0 Γ ; max=↑(2k); target ↑(2k)+1+1
      rw [hcast]
      simpa only [max_self] using hor
    | hor φ ψ =>
      have hn' : (∼φ ⋏ ∼ψ) ∈ Γ := by simpa using hn
      have hφk : φ.complexity ≤ k := by simp only [Semiformula.complexity_or] at hk; omega
      have hψk : ψ.complexity ≤ k := by simp only [Semiformula.complexity_or] at hk; omega
      have h1 := ih φ hφk (Γ := insert (∼φ) (insert φ (insert ψ Γ))) (by simp) (by simp)
      have h2 := ih ψ hψk (Γ := insert (∼ψ) (insert φ (insert ψ Γ))) (by simp) (by simp)
      have hand := PXFc.andI (∼φ) (∼ψ) h1 h2
      rw [Finset.insert_eq_self.mpr
        (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hn'))] at hand
      have hor := PXFc.orI φ ψ hand
      rw [Finset.insert_eq_self.mpr (show (φ ⋎ ψ) ∈ Γ by simp [hp])] at hor
      rw [hcast]
      simpa only [max_self] using hor
    | hall ψ =>
      have hψk : ψ.complexity ≤ k := by simp only [Semiformula.complexity_all] at hk; omega
      have hex : (∃⁰ ∼ψ) ∈ Γ := by simpa using hn
      -- constant family: each member is `PXFc (↑(2k) + 1) 0 (insert (ψ/[nm n]) Γ)`
      have fam : ∀ n, PXFc (((2 * k : ℕ) : Ordinal) + 1) 0 (insert (ψ/[nm n]) Γ) := by
        intro n
        have hcomp : (ψ/[nm n]).complexity ≤ k := by
          have he : (ψ/[nm n]).complexity = ψ.complexity := by simp
          rw [he]; exact hψk
        have ha := ih (ψ/[nm n]) hcomp
          (Γ := insert (∼(ψ/[nm n])) (insert (ψ/[nm n]) Γ)) (by simp) (by simp)
        have hexI := PXFc.exI (∼ψ) n (Γ := insert (ψ/[nm n]) Γ)
          (by have heq : (∼ψ)/[nm n] = ∼(ψ/[nm n]) := by simp
              rw [heq]; exact ha)
        rwa [Finset.insert_eq_self.mpr (Finset.mem_insert_of_mem hex)] at hexI
      have hall := PXFc.allω (β := fun _ => ((2 * k : ℕ) : Ordinal) + 1) ψ (Γ := Γ) fam
      rw [Finset.insert_eq_self.mpr hp, iSup_const_ord] at hall
      rw [hcast]; exact hall
    | hexs ψ =>
      have hψk : ψ.complexity ≤ k := by simp only [Semiformula.complexity_exs] at hk; omega
      have hall' : (∀⁰ ∼ψ) ∈ Γ := by simpa using hn
      have fam : ∀ n, PXFc (((2 * k : ℕ) : Ordinal) + 1) 0 (insert ((∼ψ)/[nm n]) Γ) := by
        intro n
        have hcomp : (ψ/[nm n]).complexity ≤ k := by
          have he : (ψ/[nm n]).complexity = ψ.complexity := by simp
          rw [he]; exact hψk
        have ha := ih (ψ/[nm n]) hcomp
          (Γ := insert (ψ/[nm n]) (insert (∼(ψ/[nm n])) Γ)) (by simp) (by simp)
        have hexI := PXFc.exI ψ n (Γ := insert (∼(ψ/[nm n])) Γ) ha
        rw [Finset.insert_eq_self.mpr (Finset.mem_insert_of_mem hp)] at hexI
        have heq : (∼ψ)/[nm n] = ∼(ψ/[nm n]) := by simp
        rw [heq]; exact hexI
      have hall := PXFc.allω (β := fun _ => ((2 * k : ℕ) : Ordinal) + 1) (∼ψ) (Γ := Γ) fam
      rw [Finset.insert_eq_self.mpr hall', iSup_const_ord] at hall
      rw [hcast]; exact hall

/-! ## The complexity-driven leaf engines, with explicit uniform bounds

`provable_em_cong_gen_x` and `provable_true_x` re-proved returning the **explicit** ordinal `↑(2k)`
(resp. `↑k`) — uniform in every instantiation, so their ω-rule families are literally constant. -/

set_option maxHeartbeats 1000000 in
/-- Bounded value-congruent EM: explicit finite height `↑(2k)`. Mirrors
`EmbeddingX.provable_em_cong_gen_x`. -/
theorem provable_em_cong_gen_x_bdd : ∀ (k : ℕ) {n : ℕ} (w w' : Fin n → SyntacticTerm LX)
    (ψ : SyntacticSemiformula LX n), ψ.complexity ≤ k →
    (∀ i, Semiterm.valm ℕ ![] (id : ℕ → ℕ) (w i)
        = Semiterm.valm ℕ ![] (id : ℕ → ℕ) (w' i)) →
    ∀ {Γ : Seq LX}, (Rew.subst w ▹ ψ) ∈ Γ → (∼(Rew.subst w' ▹ ψ)) ∈ Γ →
      PXFc ((2 * k : ℕ) : Ordinal) 0 Γ := by
  intro k
  induction k with
  | zero =>
    intro n w w' ψ hk hval Γ hp hn
    have h0 : ((2 * 0 : ℕ) : Ordinal) = 0 := by norm_num
    rw [h0]
    cases ψ using Semiformula.cases' with
    | hverum => exact PXFc.verumR (by simpa using hp)
    | hfalsum => exact PXFc.verumR (by simpa using hn)
    | hrel r v =>
      have hp' : Semiformula.rel r (fun i => Rew.subst w (v i)) ∈ Γ := by
        simpa [Semiformula.rew_rel] using hp
      have hn' : Semiformula.nrel r (fun i => Rew.subst w' (v i)) ∈ Γ := by
        simpa [Semiformula.rew_rel] using hn
      exact PXFc.axLv r _ _ (fun i => valm_subst_congr w w' hval (v i)) hp' hn'
    | hnrel r v =>
      have hp' : Semiformula.nrel r (fun i => Rew.subst w (v i)) ∈ Γ := by
        simpa [Semiformula.rew_nrel] using hp
      have hn' : Semiformula.rel r (fun i => Rew.subst w' (v i)) ∈ Γ := by
        simpa [Semiformula.rew_nrel] using hn
      exact PXFc.axLv r _ _ (fun i => (valm_subst_congr w w' hval (v i)).symm) hn' hp'
    | hand φ ψ => simp at hk
    | hor φ ψ => simp at hk
    | hall φ => simp at hk
    | hexs φ => simp at hk
  | succ k ih =>
    intro n w w' ψ hk hval Γ hp hn
    have hcast : ((2 * (k + 1) : ℕ) : Ordinal) = ((2 * k : ℕ) : Ordinal) + 1 + 1 := by
      have : (2 * (k + 1) : ℕ) = (2 * k + 1) + 1 := by omega
      rw [this]; simp only [Nat.cast_add, Nat.cast_one]
    cases ψ using Semiformula.cases' with
    | hverum => exact (PXFc.verumR (by simpa using hp)).mono (by simp) (le_refl 0)
    | hfalsum => exact (PXFc.verumR (by simpa using hn)).mono (by simp) (le_refl 0)
    | hrel r v =>
      have hp' : Semiformula.rel r (fun i => Rew.subst w (v i)) ∈ Γ := by
        simpa [Semiformula.rew_rel] using hp
      have hn' : Semiformula.nrel r (fun i => Rew.subst w' (v i)) ∈ Γ := by
        simpa [Semiformula.rew_rel] using hn
      exact (PXFc.axLv r _ _ (fun i => valm_subst_congr w w' hval (v i)) hp' hn').mono
        (by simp) (le_refl 0)
    | hnrel r v =>
      have hp' : Semiformula.nrel r (fun i => Rew.subst w (v i)) ∈ Γ := by
        simpa [Semiformula.rew_nrel] using hp
      have hn' : Semiformula.rel r (fun i => Rew.subst w' (v i)) ∈ Γ := by
        simpa [Semiformula.rew_nrel] using hn
      exact (PXFc.axLv r _ _ (fun i => (valm_subst_congr w w' hval (v i)).symm) hn' hp').mono
        (by simp) (le_refl 0)
    | hand a b =>
      have hak : a.complexity ≤ k := by simp only [Semiformula.complexity_and] at hk; omega
      have hbk : b.complexity ≤ k := by simp only [Semiformula.complexity_and] at hk; omega
      have hp' : ((Rew.subst w ▹ a) ⋏ (Rew.subst w ▹ b)) ∈ Γ := by simpa using hp
      have hn' : (∼(Rew.subst w' ▹ a) ⋎ ∼(Rew.subst w' ▹ b)) ∈ Γ := by simpa using hn
      have h1 := ih (n := n) w w' a hak hval
        (Γ := insert (Rew.subst w ▹ a)
          (insert (∼(Rew.subst w' ▹ a)) (insert (∼(Rew.subst w' ▹ b)) Γ)))
        (by simp) (by simp)
      have h2 := ih (n := n) w w' b hbk hval
        (Γ := insert (Rew.subst w ▹ b)
          (insert (∼(Rew.subst w' ▹ a)) (insert (∼(Rew.subst w' ▹ b)) Γ)))
        (by simp) (by simp)
      have hand := PXFc.andI (Rew.subst w ▹ a) (Rew.subst w ▹ b) h1 h2
      rw [Finset.insert_eq_self.mpr (show ((Rew.subst w ▹ a) ⋏ (Rew.subst w ▹ b))
        ∈ insert (∼(Rew.subst w' ▹ a)) (insert (∼(Rew.subst w' ▹ b)) Γ) by simp [hp'])] at hand
      have hor := PXFc.orI (∼(Rew.subst w' ▹ a)) (∼(Rew.subst w' ▹ b)) hand
      rw [Finset.insert_eq_self.mpr hn'] at hor
      rw [hcast]; simpa only [max_self] using hor
    | hor a b =>
      have hak : a.complexity ≤ k := by simp only [Semiformula.complexity_or] at hk; omega
      have hbk : b.complexity ≤ k := by simp only [Semiformula.complexity_or] at hk; omega
      have hp' : ((Rew.subst w ▹ a) ⋎ (Rew.subst w ▹ b)) ∈ Γ := by simpa using hp
      have hn' : (∼(Rew.subst w' ▹ a) ⋏ ∼(Rew.subst w' ▹ b)) ∈ Γ := by simpa using hn
      have h1 := ih (n := n) w w' a hak hval
        (Γ := insert (∼(Rew.subst w' ▹ a))
          (insert (Rew.subst w ▹ a) (insert (Rew.subst w ▹ b) Γ)))
        (by simp) (by simp)
      have h2 := ih (n := n) w w' b hbk hval
        (Γ := insert (∼(Rew.subst w' ▹ b))
          (insert (Rew.subst w ▹ a) (insert (Rew.subst w ▹ b) Γ)))
        (by simp) (by simp)
      have hand := PXFc.andI (∼(Rew.subst w' ▹ a)) (∼(Rew.subst w' ▹ b)) h1 h2
      rw [Finset.insert_eq_self.mpr (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hn'))]
        at hand
      have hor := PXFc.orI (Rew.subst w ▹ a) (Rew.subst w ▹ b) hand
      rw [Finset.insert_eq_self.mpr (show ((Rew.subst w ▹ a) ⋎ (Rew.subst w ▹ b)) ∈ Γ
        by simp [hp'])] at hor
      rw [hcast]; simpa only [max_self] using hor
    | hall a =>
      have hak : a.complexity ≤ k := by simp only [Semiformula.complexity_all] at hk; omega
      have hp' : (∀⁰ ((Rew.subst w).q ▹ a)) ∈ Γ := by simpa using hp
      have hn' : (∃⁰ ((Rew.subst w').q ▹ ∼a)) ∈ Γ := by simpa using hn
      have fam : ∀ m, PXFc (((2 * k : ℕ) : Ordinal) + 1) 0
          (insert (((Rew.subst w).q ▹ a)/[nm m]) Γ) := by
        intro m
        have hvalm : ∀ i, Semiterm.valm ℕ ![] (id : ℕ → ℕ) ((nm m :> w) i)
            = Semiterm.valm ℕ ![] (id : ℕ → ℕ) ((nm m :> w') i) := by
          intro i; cases i using Fin.cases with
          | zero => rfl
          | succ j => simpa using hval j
        have hx := ih (n := n + 1) (nm m :> w) (nm m :> w') a hak hvalm
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
        exact hexI
      have hallω := PXFc.allω (β := fun _ => ((2 * k : ℕ) : Ordinal) + 1)
        ((Rew.subst w).q ▹ a) (Γ := Γ) fam
      rw [Finset.insert_eq_self.mpr hp', iSup_const_ord] at hallω
      rw [hcast]; exact hallω
    | hexs a =>
      have hak : a.complexity ≤ k := by simp only [Semiformula.complexity_exs] at hk; omega
      have hp' : (∃⁰ ((Rew.subst w).q ▹ a)) ∈ Γ := by simpa using hp
      have hn' : (∀⁰ ((Rew.subst w').q ▹ ∼a)) ∈ Γ := by simpa using hn
      have fam : ∀ m, PXFc (((2 * k : ℕ) : Ordinal) + 1) 0
          (insert (((Rew.subst w').q ▹ ∼a)/[nm m]) Γ) := by
        intro m
        have hvalm : ∀ i, Semiterm.valm ℕ ![] (id : ℕ → ℕ) ((nm m :> w) i)
            = Semiterm.valm ℕ ![] (id : ℕ → ℕ) ((nm m :> w') i) := by
          intro i; cases i using Fin.cases with
          | zero => rfl
          | succ j => simpa using hval j
        have hx := ih (n := n + 1) (nm m :> w) (nm m :> w') a hak hvalm
          (Γ := insert (((Rew.subst w).q ▹ a)/[nm m])
            (insert (∼(((Rew.subst w').q ▹ a)/[nm m])) Γ))
          (by rw [← subst_q_cons_app]; simp)
          (by rw [← subst_q_cons_app]; simp)
        have hexI := PXFc.exI ((Rew.subst w).q ▹ a) m
          (Γ := insert (∼(((Rew.subst w').q ▹ a)/[nm m])) Γ) hx
        rw [Finset.insert_eq_self.mpr (Finset.mem_insert_of_mem hp')] at hexI
        have heq : (((Rew.subst w').q ▹ ∼a)/[nm m]) = ∼(((Rew.subst w').q ▹ a)/[nm m]) := by simp
        rw [heq]; exact hexI
      have hallω := PXFc.allω (β := fun _ => ((2 * k : ℕ) : Ordinal) + 1)
        ((Rew.subst w').q ▹ ∼a) (Γ := Γ) fam
      rw [Finset.insert_eq_self.mpr hn', iSup_const_ord] at hallω
      rw [hcast]; exact hallω

set_option maxHeartbeats 1000000 in
/-- Bounded ω-completeness for true closed X-free formulas: explicit finite height `↑k`. Mirrors
`EmbeddingX.provable_true_x`. -/
theorem provable_true_x_bdd : ∀ (k : ℕ) (φ : Form LX), φ.complexity ≤ k → XFreeForm φ → LitTrue φ →
    ∀ {Γ : Seq LX}, φ ∈ Γ → PXFc ((k : ℕ) : Ordinal) 0 Γ := by
  intro k
  induction k with
  | zero =>
    intro φ hk hxf htrue Γ hmem
    have h0 : ((0 : ℕ) : Ordinal) = 0 := by norm_num
    rw [h0]
    cases φ using Semiformula.cases' with
    | hverum => exact PXFc.verumR hmem
    | hfalsum => simp [LitTrue] at htrue
    | hrel r v => exact PXFc.axTrue true r v (by simpa using hxf) htrue hmem
    | hnrel r v => exact PXFc.axTrue false r v (by simpa using hxf) htrue hmem
    | hand φ ψ => simp at hk
    | hor φ ψ => simp at hk
    | hall φ => simp at hk
    | hexs φ => simp at hk
  | succ k ih =>
    intro φ hk hxf htrue Γ hmem
    have hcast : (((k + 1 : ℕ)) : Ordinal) = ((k : ℕ) : Ordinal) + 1 := by
      simp only [Nat.cast_add, Nat.cast_one]
    cases φ using Semiformula.cases' with
    | hverum => exact (PXFc.verumR hmem).mono (by simp) (le_refl 0)
    | hfalsum => simp [LitTrue] at htrue
    | hrel r v => exact (PXFc.axTrue true r v (by simpa using hxf) htrue hmem).mono (by simp) (le_refl 0)
    | hnrel r v => exact (PXFc.axTrue false r v (by simpa using hxf) htrue hmem).mono (by simp) (le_refl 0)
    | hand a b =>
      have hak : a.complexity ≤ k := by simp only [Semiformula.complexity_and] at hk; omega
      have hbk : b.complexity ≤ k := by simp only [Semiformula.complexity_and] at hk; omega
      obtain ⟨hxa, hxb⟩ : XFreeForm a ∧ XFreeForm b := by simpa using hxf
      obtain ⟨hta, htb⟩ : LitTrue a ∧ LitTrue b := by simpa [LitTrue] using htrue
      have h1 := ih a hak hxa hta (Γ := insert a Γ) (by simp)
      have h2 := ih b hbk hxb htb (Γ := insert b Γ) (by simp)
      have hand := PXFc.andI a b h1 h2
      rw [Finset.insert_eq_self.mpr hmem] at hand
      rw [hcast]; simpa only [max_self] using hand
    | hor a b =>
      have hak : a.complexity ≤ k := by simp only [Semiformula.complexity_or] at hk; omega
      have hbk : b.complexity ≤ k := by simp only [Semiformula.complexity_or] at hk; omega
      obtain ⟨hxa, hxb⟩ : XFreeForm a ∧ XFreeForm b := by simpa using hxf
      have htor : LitTrue a ∨ LitTrue b := by simpa [LitTrue] using htrue
      rcases htor with hta | htb
      · have h1 := ih a hak hxa hta (Γ := insert a (insert b Γ)) (by simp)
        have hor := PXFc.orI a b h1
        rw [Finset.insert_eq_self.mpr hmem] at hor
        rw [hcast]; exact hor
      · have h1 := ih b hbk hxb htb (Γ := insert a (insert b Γ)) (by simp)
        have hor := PXFc.orI a b h1
        rw [Finset.insert_eq_self.mpr hmem] at hor
        rw [hcast]; exact hor
    | hall a =>
      have hak : a.complexity ≤ k := by simp only [Semiformula.complexity_all] at hk; omega
      have hxa : XFreeForm a := by simpa using hxf
      have hfam : ∀ n, LitTrue (a/[nm n]) := by
        intro n
        have := htrue
        simp only [LitTrue, Semiformula.eval_all] at this
        simpa [LitTrue, Semiformula.eval_substs, val_nm_ambient, Matrix.constant_eq_singleton]
          using this n
      have fam : ∀ n, PXFc ((k : ℕ) : Ordinal) 0 (insert (a/[nm n]) Γ) := by
        intro n
        have hcomp : (a/[nm n]).complexity ≤ k := by
          have : (a/[nm n]).complexity = a.complexity := by simp
          rw [this]; exact hak
        exact ih (a/[nm n]) hcomp (by simpa using hxa) (hfam n) (by simp)
      have hallω := PXFc.allω (β := fun _ => ((k : ℕ) : Ordinal)) a fam
      rw [Finset.insert_eq_self.mpr hmem, iSup_const_ord] at hallω
      rw [hcast]; exact hallω
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
      have hx := ih (a/[nm n]) hcomp (by simpa using hxa) hn (Γ := insert (a/[nm n]) Γ) (by simp)
      have hexI := PXFc.exI a n hx
      rw [Finset.insert_eq_self.mpr hmem] at hexI
      rw [hcast]; exact hexI

/-- Bounded `Z∞` excluded middle as a `PXFcFin` (finite height `2·complexity`). -/
theorem provable_em_x_fin {c : ℕ} {Γ : Seq LX} (φ : Form LX) (hp : φ ∈ Γ) (hn : ∼φ ∈ Γ) :
    PXFcFin c Γ :=
  ⟨2 * φ.complexity, (provable_em_x_bdd φ.complexity φ le_rfl hp hn).mono le_rfl (Nat.zero_le c)⟩

/-! ## Bounded value-substitution + closed ∃-introduction (finite-preserving) -/

/-- Bounded `PXFc.subst_value_subst`: value-congruent substitution preserves finite height. -/
theorem subst_value_subst_bdd {c : ℕ} {Γ : Seq LX}
    (ψ : SyntacticSemiformula LX 1) (s t : SyntacticTerm LX)
    (hval : Semiterm.valm ℕ ![] (id : ℕ → ℕ) s = Semiterm.valm ℕ ![] (id : ℕ → ℕ) t)
    (hc : (ψ.complexity + 1 : ℕ∞) ≤ (c : ℕ∞))
    (h : PXFcFin c (insert (ψ/[s]) Γ)) :
    PXFcFin c (insert (ψ/[t]) Γ) := by
  obtain ⟨N, hN⟩ := h
  have h₁ : PXFc (N : Ordinal) c (insert (ψ/[s]) (insert (ψ/[t]) Γ)) :=
    hN.weakening (Finset.insert_subset_insert _ (Finset.subset_insert _ _))
  have h₂ := provable_em_cong_gen_x_bdd ψ.complexity ![t] ![s] ψ le_rfl
    (by intro i; cases i using Fin.cases with
        | zero => simpa using hval.symm
        | succ j => exact j.elim0)
    (Γ := insert (∼(ψ/[s])) (insert (ψ/[t]) Γ))
    (by show (Rew.subst ![t] ▹ ψ) ∈ _; simp)
    (by show (∼(Rew.subst ![s] ▹ ψ)) ∈ _; simp)
  have hcc : (((ψ/[s]).complexity : ℕ) + 1 : ℕ∞) ≤ (c : ℕ∞) := by
    have : (ψ/[s]).complexity = ψ.complexity := by simp
    rw [this]; exact hc
  exact PXFcFin.cut (ψ/[s]) hcc ⟨N, h₁⟩ ⟨2 * ψ.complexity, h₂.mono le_rfl (Nat.zero_le c)⟩

/-- Bounded `PXFc.exI_closed`: closed-term ∃-introduction preserves finite height (the rank rises to
`max c (ψ.complexity + 1)`). -/
theorem exI_closed_bdd {c : ℕ} {Γ : Seq LX}
    (ψ : SyntacticSemiformula LX 1) (s : SyntacticTerm LX)
    (h : PXFcFin c (insert (ψ/[s]) Γ)) :
    PXFcFin (max c (ψ.complexity + 1)) (insert (∃⁰ ψ) Γ) := by
  obtain ⟨N, hN⟩ := h
  set m : ℕ := Semiterm.valm ℕ ![] (id : ℕ → ℕ) s with hm
  set c' : ℕ := max c (ψ.complexity + 1) with hc'
  have hsval : Semiterm.valm ℕ ![] (id : ℕ → ℕ) (nm m : Semiterm LX ℕ 0)
             = Semiterm.valm ℕ ![] (id : ℕ → ℕ) s := by rw [valm_nm]
  have h₁ : PXFc (N : Ordinal) c' (insert (ψ/[s]) (insert (ψ/[nm m]) Γ)) :=
    (hN.weakening (Finset.insert_subset_insert _ (Finset.subset_insert _ _))).mono le_rfl
      (le_max_left _ _)
  have h₂ := provable_em_cong_gen_x_bdd ψ.complexity ![nm m] ![s] ψ le_rfl
    (by intro i; cases i using Fin.cases with
        | zero => simpa using hsval
        | succ j => exact j.elim0)
    (Γ := insert (∼(ψ/[s])) (insert (ψ/[nm m]) Γ))
    (by show (Rew.subst ![nm m] ▹ ψ) ∈ _; simp)
    (by show (∼(Rew.subst ![s] ▹ ψ)) ∈ _; simp)
  have hcc : (((ψ/[s]).complexity : ℕ) + 1 : ℕ∞) ≤ (c' : ℕ∞) := by
    have : (ψ/[s]).complexity = ψ.complexity := by simp
    rw [this]; exact_mod_cast le_max_right _ _
  have hcut : PXFcFin c' (insert (ψ/[nm m]) Γ) :=
    PXFcFin.cut (ψ/[s]) hcc ⟨N, h₁⟩ ⟨2 * ψ.complexity, h₂.mono le_rfl (Nat.zero_le c')⟩
  exact PXFcFin.exI ψ m hcut

/-! ## The cut-tower: `metaInduction_cong_bdd` — height `< ε₀` (the single transfinite jump)

The chain `{ψ(n)}ₙ` of cuts is built at **finite** height per `n` (each step adds finitely-many
`provable_em_x_fin`/`andI`/`exI`/`cut`/`subst_value_subst_bdd` bumps). The ω-rule over this
*non*-constant finite family lands at `⨆ₙ (↑Nₙ) + 1 ≤ ω + 1 < ε₀` (`PXFcLt.allω_fin`). This is the
sole place the embedded ordinal goes transfinite — exactly Gentzen's content. -/
set_option maxHeartbeats 1000000 in
theorem metaInduction_cong_bdd (ψ step : SyntacticSemiformula LX 1) {Γ : Seq LX}
    (succT : ℕ → SyntacticTerm LX)
    (hsval : ∀ n, Semiterm.valm ℕ ![] (id : ℕ → ℕ) (succT n) = n + 1)
    (hstep : ∀ n, (∼step)/[nm n] = (ψ/[nm n]) ⋏ ∼(ψ/[succT n])) :
    PXFc (Ordinal.omega0 + 1) (ψ.complexity + 1)
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
  have chain : ∀ n, PXFcFin c (insert (ψ/[nm n]) Δ) := by
    intro n
    induction n with
    | zero =>
      exact provable_em_x_fin (ψ/[nm 0]) (Finset.mem_insert_self _ _)
        (Finset.mem_insert_of_mem (by rw [hΔ]; exact Finset.mem_insert_self _ _))
    | succ n ih =>
      have hL : PXFcFin c (insert (ψ/[nm n]) (insert (ψ/[succT n]) Δ)) :=
        ih.weakening (Finset.insert_subset_insert _ (Finset.subset_insert _ _))
      have hA : PXFcFin c (insert (ψ/[nm n])
          (insert (∼(ψ/[nm n])) (insert (ψ/[succT n]) Δ))) :=
        provable_em_x_fin (ψ/[nm n]) (Finset.mem_insert_self _ _)
          (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
      have hB : PXFcFin c (insert (∼(ψ/[succT n]))
          (insert (∼(ψ/[nm n])) (insert (ψ/[succT n]) Δ))) :=
        provable_em_x_fin (ψ/[succT n])
          (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))
          (Finset.mem_insert_self _ _)
      have hand := PXFcFin.andI (c := c) (ψ/[nm n]) (∼(ψ/[succT n])) hA hB
      rw [← hstep n] at hand
      have hexI := PXFcFin.exI (∼step) n hand
      rw [Finset.insert_eq_self.mpr (hEx n)] at hexI
      have hcutd : PXFcFin c (insert (ψ/[succT n]) Δ) :=
        PXFcFin.cut (ψ/[nm n]) (hcut n) hL hexI
      exact subst_value_subst_bdd ψ (succT n) (nm (n+1)) (by rw [hsval, valm_nm]) hcc hcutd
  refine (PXFc.allω_omega (c := c) (Γ := Δ) ψ chain).weakening ?_
  rw [hΔ]; intro x hx
  simp only [Finset.mem_insert] at hx ⊢
  tauto

/-! ## Bounded universal-closure stripping (explicit `B + n`) -/

set_option maxHeartbeats 1000000 in
/-- Bounded `EmbeddingX.PXFc_allClosure`: from a **uniform** bound `B` on every numeral
instantiation, derive `∀⁰* χ` at the explicit height `B + n` (one `+1` per closure variable, all the
ω-rule families constant at `B`). -/
theorem PXFc_allClosure_omega : ∀ {n} (χ : Semiformula LX ℕ n) {c : ℕ} {Γ : Seq LX} (B : Ordinal.{0}),
    (∀ (v : Fin n → ℕ), PXFc B c (insert (Rew.subst (fun i => nm (v i)) ▹ χ) Γ)) →
    PXFc (B + (n : ℕ)) c (insert (∀⁰* χ) Γ) := by
  intro n
  induction n with
  | zero =>
    intro χ c Γ B h
    have ha := h Fin.elim0
    rw [show (∀⁰* χ) = χ from rfl]
    have he : (Rew.subst (fun i : Fin 0 => nm (Fin.elim0 i)) ▹ χ) = χ := by simp [Matrix.empty_eq]
    rw [he] at ha
    simpa using ha
  | succ n ih =>
    intro χ c Γ B h
    rw [allClosure_succ]
    have key : ∀ v : Fin n → ℕ, PXFc (B + 1) c
        (insert (Rew.subst (fun i => nm (v i)) ▹ (∀⁰ χ)) Γ) := by
      intro v
      rw [Rewriting.app_all]
      have fam : ∀ m, PXFc B c
          (insert (((Rew.subst (fun i => nm (v i))).q ▹ χ)/[nm m]) Γ) := by
        intro m
        rw [subst_q_cons_app (fun i => nm (v i)) m χ]
        have hcons : ((nm m :> fun i => nm (v i)) : Fin (n+1) → Semiterm LX ℕ 0)
            = (fun i => nm ((m :> v) i)) := by
          funext i; cases i using Fin.cases with
          | zero => simp
          | succ j => simp
        rw [hcons]; exact h (m :> v)
      have hb := PXFc.allω (β := fun _ => B) ((Rew.subst (fun i => nm (v i))).q ▹ χ) fam
      rwa [iSup_const_ord] at hb
    have hres := ih (∀⁰ χ) (B + 1) key
    have hcast : (B + 1) + (n : ℕ) = B + ((n + 1 : ℕ) : Ordinal) := by
      rw [add_assoc]; congr 1
      rw [← Nat.cast_one, ← Nat.cast_add]; congr 1; omega
    rwa [hcast] at hres

end GoodsteinPA.EmbeddingBound
