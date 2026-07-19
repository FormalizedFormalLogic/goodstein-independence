/-
# `XFreeCutElim.lean` — C₁: `XFreeAx`-preserving cut-elimination over `LX`

The corollary `orderType_le_of_TIderiv` (Boundedness, lap 14) consumes a **cut-free** (`d.cr = 0`)
`XFreeAx` derivation of `{TI}`. The embedding (C₂) supplies a derivation of some finite cut rank `c`
with `XFreeAx`; this file reduces it to cut rank `0` **while preserving `XFreeAx`** — the missing
input to the corollary, hence to Thm 5.6 (`Z ⊢ TI_≺(X) ⟹ ‖≺‖ < ε₀`).

## Why a port (not a transport of `ZinftyGen.cutElim`)
`ZinftyGen.Provable.cutElim` already cut-eliminates generically over `{L}` — but it returns
`Provable` (`∃ d, …`), discarding the derivation, so the `XFreeAx` of its *output* is unrecoverable.
We therefore carry the leaf predicate through every reduction in a cut-rank-bearing twin
`PXFc α c Γ := ∃ d, d.o ≤ α ∧ d.cr ≤ c ∧ XFreeAx d` (generalising lap-14's `PXF = PXFc · 0`).

## The one faithfulness subtlety, resolved (lap-15 review)
Cut-elimination's only truth-layer steps are the **atomic** ones (`atomCut`/`removeFalseLit`), which
emit `axTrue` leaves on the cut atom. On an X-atom that would be a lone X-`axTrue` ⟹ break `XFreeAx`.
But it never happens: (i) our `Deriv.axL` is the **same-atom** EM axiom `{Xs,¬Xs}`, so an X-atomic
cut closes by **set idempotence** (the `axL` branch, truth-free); (ii) the truth-surgery branch fires
only on an `axTrue` leaf *equal to* the cut atom — i.e. an X-`axTrue` leaf — which `XFreeAx` forbids,
so it is **vacuous**. Hence `removeFalseLit` is only ever invoked on X-FREE cut atoms (emitting X-free
`axTrue`, fine for `XFreeAx`). The full chain therefore preserves `XFreeAx` at cut rank 0.
-/
import GoodsteinPA.Boundedness
import GoodsteinPA.Compat

namespace GoodsteinPA.XFreeCutElim

open LO LO.FirstOrder
open GoodsteinPA.ZinftyGen GoodsteinPA.LangX GoodsteinPA.TruthSem GoodsteinPA.XPositive
  GoodsteinPA.Boundedness

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

/-- **Cut-rank-carrying `XFreeAx` provability** over `LX`: a derivation of ordinal height `≤ α`, cut
rank `≤ c`, all of whose `axTrue` leaves are X-free. `PXFc α 0 ↔ PXF α` (cut-free case, lap 14). -/
def PXFc (α : Ordinal.{0}) (c : ℕ) (Γ : Seq LX) : Prop :=
  ∃ d : Deriv Γ, d.o ≤ α ∧ d.cr ≤ (c : ℕ∞) ∧ XFreeAx d

/-! ### Bridge to the lap-14 cut-free carrier `PXF` -/

theorem PXF.toPXFc {α : Ordinal.{0}} {Γ : Seq LX} : PXF α Γ → PXFc α 0 Γ
  | ⟨d, ho, hcr, hxf⟩ => ⟨d, ho, by simp [hcr], hxf⟩

theorem PXFc.toPXF {α : Ordinal.{0}} {Γ : Seq LX} : PXFc α 0 Γ → PXF α Γ
  | ⟨d, ho, hcr, hxf⟩ => ⟨d, ho, nonpos_iff_eq_zero.mp (by simpa using hcr), hxf⟩

/-! ### Smart builders (mirror `ZinftyGen.Provable.*`, carrying `XFreeAx`) -/

theorem PXFc.mono {α β : Ordinal.{0}} {c c' : ℕ} (hα : α ≤ β) (hc : c ≤ c') {Γ : Seq LX} :
    PXFc α c Γ → PXFc β c' Γ
  | ⟨d, ho, hcr, hxf⟩ => ⟨d, ho.trans hα, hcr.trans (by exact_mod_cast hc), hxf⟩

theorem PXFc.weakening {α : Ordinal.{0}} {c : ℕ} {Γ Δ : Seq LX} (h : Γ ⊆ Δ) :
    PXFc α c Γ → PXFc α c Δ
  | ⟨d, ho, hcr, hxf⟩ =>
    ⟨Deriv.weak d h, by simpa only [Deriv.o] using ho, by simpa only [Deriv.cr] using hcr, hxf⟩

theorem PXFc.cast {α : Ordinal.{0}} {c : ℕ} {Γ Δ : Seq LX} (e : Γ = Δ) :
    PXFc α c Γ → PXFc α c Δ := fun h => e ▸ h

theorem PXFc.axL {Γ : Seq LX} {k} (r : LX.Rel k) (v) (hp : Semiformula.rel r v ∈ Γ)
    (hn : Semiformula.nrel r v ∈ Γ) : PXFc 0 0 Γ :=
  ⟨Deriv.axL r v hp hn, by simp [Deriv.o], by simp [Deriv.cr], by simp [XFreeAx]⟩

/-- The value-congruent literal axiom, `XFreeAx`-safe (not an `axTrue`). -/
theorem PXFc.axLv {Γ : Seq LX} {k} (r : LX.Rel k) (v v' : Fin k → Semiterm LX ℕ 0)
    (hval : ∀ i, GoodsteinPA.Compat.gValm ℕ ![] (id : ℕ → ℕ) (v i)
               = GoodsteinPA.Compat.gValm ℕ ![] (id : ℕ → ℕ) (v' i))
    (hp : Semiformula.rel r v ∈ Γ) (hn : Semiformula.nrel r v' ∈ Γ) : PXFc 0 0 Γ :=
  ⟨Deriv.axLv r v v' hval hp hn, by simp [Deriv.o], by simp [Deriv.cr], by simp [XFreeAx]⟩

theorem PXFc.axTrue {Γ : Seq LX} {k} (b : Bool) (r : LX.Rel k) (v) (hxfree : Sum.isLeft r = true)
    (htrue : LitTrue (signedLit b r v)) (hmem : signedLit b r v ∈ Γ) : PXFc 0 0 Γ :=
  ⟨Deriv.axTrue b r v htrue hmem, by simp [Deriv.o], by simp [Deriv.cr], hxfree⟩

theorem PXFc.verumR {Γ : Seq LX} (h : (⊤ : Form LX) ∈ Γ) : PXFc 0 0 Γ :=
  ⟨Deriv.verumR h, by simp [Deriv.o], by simp [Deriv.cr], by simp [XFreeAx]⟩

theorem PXFc.andI {α β : Ordinal.{0}} {c : ℕ} {Γ : Seq LX} (φ ψ : Form LX)
    (hφ : PXFc α c (insert φ Γ)) (hψ : PXFc β c (insert ψ Γ)) :
    PXFc (max α β + 1) c (insert (φ ⋏ ψ) Γ) :=
  match hφ, hψ with
  | ⟨dφ, hoφ, hcφ, hxφ⟩, ⟨dψ, hoψ, hcψ, hxψ⟩ =>
    ⟨Deriv.andI φ ψ dφ dψ, by simp only [Deriv.o]; exact add_le_add (max_le_max hoφ hoψ) le_rfl,
      by simp only [Deriv.cr]; exact max_le hcφ hcψ, ⟨hxφ, hxψ⟩⟩

theorem PXFc.orI {α : Ordinal.{0}} {c : ℕ} {Γ : Seq LX} (φ ψ : Form LX)
    (h : PXFc α c (insert φ (insert ψ Γ))) : PXFc (α + 1) c (insert (φ ⋎ ψ) Γ) :=
  match h with
  | ⟨d, ho, hc, hx⟩ =>
    ⟨Deriv.orI φ ψ d, by simp only [Deriv.o]; gcongr, by simp only [Deriv.cr]; exact hc, hx⟩

theorem PXFc.exI {α : Ordinal.{0}} {c : ℕ} {Γ : Seq LX} (φ : SyntacticSemiformula LX 1) (n : ℕ)
    (h : PXFc α c (insert (φ/[nm n]) Γ)) : PXFc (α + 1) c (insert (∃⁰ φ) Γ) :=
  match h with
  | ⟨d, ho, hc, hx⟩ =>
    ⟨Deriv.exI φ n d, by simp only [Deriv.o]; gcongr, by simp only [Deriv.cr]; exact hc, hx⟩

theorem PXFc.allω {β : ℕ → Ordinal.{0}} {c : ℕ} {Γ : Seq LX} (φ : SyntacticSemiformula LX 1)
    (h : ∀ n, PXFc (β n) c (insert (φ/[nm n]) Γ)) : PXFc ((⨆ n, β n) + 1) c (insert (∀⁰ φ) Γ) := by
  choose d ho hc hx using h
  refine ⟨Deriv.allω φ d, ?_, ?_, hx⟩
  · simp only [Deriv.o]
    exact add_le_add (Ordinal.iSup_le fun n => (ho n).trans (Ordinal.le_iSup β n)) le_rfl
  · simp only [Deriv.cr]; exact iSup_le hc

theorem PXFc.cut {α β : Ordinal.{0}} {c : ℕ} {Γ : Seq LX} (χ : Form LX)
    (hc : (χ.complexity + 1 : ℕ∞) ≤ (c : ℕ∞))
    (h₁ : PXFc α c (insert χ Γ)) (h₂ : PXFc β c (insert (∼χ) Γ)) :
    PXFc (max α β + 1) c Γ :=
  match h₁, h₂ with
  | ⟨d₁, ho₁, hcr₁, hx₁⟩, ⟨d₂, ho₂, hcr₂, hx₂⟩ =>
    ⟨Deriv.cut χ d₁ d₂, by simp only [Deriv.o]; exact add_le_add (max_le_max ho₁ ho₂) le_rfl,
      by simp only [Deriv.cr]; exact max_le hc (max_le hcr₁ hcr₂), ⟨hx₁, hx₂⟩⟩

theorem PXFc.contr {α : Ordinal.{0}} {c : ℕ} {Γ : Seq LX} (φ : Form LX)
    (h : PXFc α c (insert φ (insert φ Γ))) : PXFc α c (insert φ Γ) := by
  simpa [Finset.insert_idem] using h

/-! ### Inversions at cut rank `≤ c`, preserving `XFreeAx` (port of `ZinftyGen.{orInvAux,andInvAux,
allInvAux}`). The `cut` case is now real (recurse on both premises, re-cut on the cut formula —
truth-free, `XFreeAx` threads); the lap-14 cr=0 inversions made it vacuous. -/

theorem orInvAux_x {φ ψ : Form LX} {c : ℕ} : ∀ {Γ : Seq LX} (d : Deriv Γ),
    XFreeAx d → d.cr ≤ (c : ℕ∞) → (φ ⋎ ψ) ∈ Γ →
    PXFc d.o c (insert φ (insert ψ (Γ.erase (φ ⋎ ψ)))) := by
  intro Γ d
  induction d with
  | @axL Γ k r v hp hn =>
    intro _ _ _
    have hr : Semiformula.rel r v ∈ Γ.erase (φ ⋎ ψ) :=
      Finset.mem_erase.mpr ⟨by intro h; simp [Vee.vee] at h, hp⟩
    have hn' : Semiformula.nrel r v ∈ Γ.erase (φ ⋎ ψ) :=
      Finset.mem_erase.mpr ⟨by intro h; simp [Vee.vee] at h, hn⟩
    simp only [Deriv.o]
    exact (PXFc.axL r v (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hr))
      (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hn'))).mono le_rfl (Nat.zero_le c)
  | @axLv Γ k r v v' hval hp hn =>
    intro _ _ _
    have hr : Semiformula.rel r v ∈ Γ.erase (φ ⋎ ψ) :=
      Finset.mem_erase.mpr ⟨by intro h; simp [Vee.vee] at h, hp⟩
    have hn' : Semiformula.nrel r v' ∈ Γ.erase (φ ⋎ ψ) :=
      Finset.mem_erase.mpr ⟨by intro h; simp [Vee.vee] at h, hn⟩
    simp only [Deriv.o]
    exact (PXFc.axLv r v v' hval (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hr))
      (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hn'))).mono le_rfl (Nat.zero_le c)
  | @axTrue Γ k b r v htrue hmem =>
    intro hxf _ _
    have hl : signedLit b r v ∈ Γ.erase (φ ⋎ ψ) :=
      Finset.mem_erase.mpr ⟨by cases b <;> simp [signedLit, Vee.vee], hmem⟩
    simp only [Deriv.o]
    exact (PXFc.axTrue b r v hxf htrue
      (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hl))).mono le_rfl (Nat.zero_le c)
  | @verumR Γ h =>
    intro _ _ _
    have ht : (⊤ : Form LX) ∈ Γ.erase (φ ⋎ ψ) :=
      Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), h⟩
    simp only [Deriv.o]
    exact (PXFc.verumR (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem ht))).mono
      le_rfl (Nat.zero_le c)
  | @weak Δ Γ d' hsub ih =>
    intro hxf hcr hmem
    simp only [Deriv.cr] at hcr
    simp only [Deriv.o]
    by_cases hd : (φ ⋎ ψ) ∈ Δ
    · exact (ih hxf hcr hd).weakening
        (Finset.insert_subset_insert _ (Finset.insert_subset_insert _
          (Finset.erase_subset_erase _ hsub)))
    · have base : PXFc d'.o c Δ := ⟨d', le_rfl, hcr, hxf⟩
      refine base.weakening ?_
      intro x hx
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_erase.mpr ⟨fun e => hd (e ▸ hx), hsub hx⟩))
  | @andI Γ₀ φ' ψ' dφ dψ ihφ ihψ =>
    intro hxf hcr hmem
    simp only [Deriv.cr] at hcr
    simp only [Deriv.o]
    have hhead : (φ' ⋏ ψ') ≠ (φ ⋎ ψ) := by intro h; simp [Wedge.wedge, Vee.vee] at h
    have hmem0 : (φ ⋎ ψ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
    have hcrφ : dφ.cr ≤ (c : ℕ∞) := le_trans (le_max_left _ _) hcr
    have hcrψ : dψ.cr ≤ (c : ℕ∞) := le_trans (le_max_right _ _) hcr
    have Pφ := (ihφ hxf.1 hcrφ (Finset.mem_insert_of_mem hmem0)).weakening (invPushOr φ ψ φ' Γ₀)
    have Pψ := (ihψ hxf.2 hcrψ (Finset.mem_insert_of_mem hmem0)).weakening (invPushOr φ ψ ψ' Γ₀)
    exact (PXFc.andI φ' ψ' Pφ Pψ).weakening (invPullOr φ ψ hhead Γ₀)
  | @orI Γ₀ φ' ψ' d' ih =>
    intro hxf hcr hmem
    simp only [Deriv.cr] at hcr
    simp only [Deriv.o]
    by_cases hhd : (φ' ⋎ ψ') = (φ ⋎ ψ)
    · obtain ⟨rfl, rfl⟩ := (Semiformula.or_inj _ _ _ _).mp hhd.symm
      by_cases hd : (φ ⋎ ψ) ∈ Γ₀
      · have P := ih hxf hcr (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hd))
        refine (P.weakening ?_).mono (le_of_lt (lt_add_of_pos_right _ one_pos)) le_rfl
        intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto
      · have base : PXFc d'.o c (insert φ (insert ψ Γ₀)) := ⟨d', le_rfl, hcr, hxf⟩
        refine (base.weakening ?_).mono (le_of_lt (lt_add_of_pos_right _ one_pos)) le_rfl
        intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
        rcases hx with rfl | rfl | hx
        · tauto
        · tauto
        · exact Or.inr (Or.inr ⟨fun e => hd (e ▸ hx), Or.inr hx⟩)
    · have hmem0 : (φ ⋎ ψ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhd e.symm
      have hsub : insert φ (insert ψ ((insert φ' (insert ψ' Γ₀)).erase (φ ⋎ ψ)))
            ⊆ insert φ' (insert ψ' (insert φ (insert ψ (Γ₀.erase (φ ⋎ ψ))))) := by
        intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto
      have P := (ih hxf hcr (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hmem0))).weakening hsub
      exact (PXFc.orI φ' ψ' P).weakening (invPullOr φ ψ hhd Γ₀)
  | @allω Γ₀ χ d ih =>
    intro hxf hcr hmem
    simp only [Deriv.cr] at hcr
    simp only [Deriv.o]
    have hhead : (∀⁰ χ) ≠ (φ ⋎ ψ) := by intro h; simp [Vee.vee] at h
    have hmem0 : (φ ⋎ ψ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
    have key : ∀ n, PXFc (d n).o c (insert (χ/[nm n]) (insert φ (insert ψ (Γ₀.erase (φ ⋎ ψ))))) :=
      fun n => (ih n (hxf n) (le_trans (le_iSup (fun m => (d m).cr) n) hcr)
        (Finset.mem_insert_of_mem hmem0)).weakening (invPushOr φ ψ (χ/[nm n]) Γ₀)
    exact (PXFc.allω χ key).weakening (invPullOr φ ψ hhead Γ₀)
  | @exI Γ₀ χ n d ih =>
    intro hxf hcr hmem
    simp only [Deriv.cr] at hcr
    simp only [Deriv.o]
    have hhead : (∃⁰ χ) ≠ (φ ⋎ ψ) := by intro h; simp [Vee.vee] at h
    have hmem0 : (φ ⋎ ψ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
    have P := (ih hxf hcr (Finset.mem_insert_of_mem hmem0)).weakening (invPushOr φ ψ (χ/[nm n]) Γ₀)
    exact (PXFc.exI χ n P).weakening (invPullOr φ ψ hhead Γ₀)
  | @cut Γ₀ χ d₁ d₂ ih₁ ih₂ =>
    intro hxf hcr hmem
    simp only [Deriv.cr] at hcr
    simp only [Deriv.o]
    have hcχ : (χ.complexity + 1 : ℕ∞) ≤ (c : ℕ∞) := (le_max_left _ _).trans hcr
    have hcr1 : d₁.cr ≤ (c : ℕ∞) := (le_max_left d₁.cr d₂.cr).trans ((le_max_right _ _).trans hcr)
    have hcr2 : d₂.cr ≤ (c : ℕ∞) := (le_max_right d₁.cr d₂.cr).trans ((le_max_right _ _).trans hcr)
    have P₁ := (ih₁ hxf.1 hcr1 (Finset.mem_insert_of_mem hmem)).weakening (invPushOr φ ψ χ Γ₀)
    have P₂ := (ih₂ hxf.2 hcr2 (Finset.mem_insert_of_mem hmem)).weakening (invPushOr φ ψ (∼χ) Γ₀)
    exact PXFc.cut χ hcχ P₁ P₂

/-- **∨-inversion at a relaxed bound**, `XFreeAx`-preserving. -/
theorem PXFc.orInv {α : Ordinal.{0}} {c : ℕ} {Γ : Seq LX} {φ ψ : Form LX} (hmem : (φ ⋎ ψ) ∈ Γ)
    (h : PXFc α c Γ) : PXFc α c (insert φ (insert ψ (Γ.erase (φ ⋎ ψ)))) := by
  rcases h with ⟨d, ho, hcr, hxf⟩
  exact (orInvAux_x d hxf hcr hmem).mono ho le_rfl

/-- **∧-inversion** (both conjuncts), cut rank `≤ c`, `XFreeAx`-preserving. -/
theorem andInvAux_x {φ ψ : Form LX} {c : ℕ} : ∀ {Γ : Seq LX} (d : Deriv Γ),
    XFreeAx d → d.cr ≤ (c : ℕ∞) → (φ ⋏ ψ) ∈ Γ →
    PXFc d.o c (insert φ (Γ.erase (φ ⋏ ψ))) ∧ PXFc d.o c (insert ψ (Γ.erase (φ ⋏ ψ))) := by
  intro Γ d
  induction d with
  | @axL Γ k r v hp hn =>
    intro _ _ _
    have hr : Semiformula.rel r v ∈ Γ.erase (φ ⋏ ψ) :=
      Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), hp⟩
    have hn' : Semiformula.nrel r v ∈ Γ.erase (φ ⋏ ψ) :=
      Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), hn⟩
    simp only [Deriv.o]
    exact ⟨(PXFc.axL r v (Finset.mem_insert_of_mem hr) (Finset.mem_insert_of_mem hn')).mono
        le_rfl (Nat.zero_le c),
      (PXFc.axL r v (Finset.mem_insert_of_mem hr) (Finset.mem_insert_of_mem hn')).mono
        le_rfl (Nat.zero_le c)⟩
  | @axLv Γ k r v v' hval hp hn =>
    intro _ _ _
    have hr : Semiformula.rel r v ∈ Γ.erase (φ ⋏ ψ) :=
      Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), hp⟩
    have hn' : Semiformula.nrel r v' ∈ Γ.erase (φ ⋏ ψ) :=
      Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), hn⟩
    simp only [Deriv.o]
    exact ⟨(PXFc.axLv r v v' hval (Finset.mem_insert_of_mem hr)
          (Finset.mem_insert_of_mem hn')).mono le_rfl (Nat.zero_le c),
      (PXFc.axLv r v v' hval (Finset.mem_insert_of_mem hr)
          (Finset.mem_insert_of_mem hn')).mono le_rfl (Nat.zero_le c)⟩
  | @axTrue Γ k b r v htrue hmem =>
    intro hxf _ _
    have hl : signedLit b r v ∈ Γ.erase (φ ⋏ ψ) :=
      Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by cases b <;> simp [signedLit]), hmem⟩
    simp only [Deriv.o]
    exact ⟨(PXFc.axTrue b r v hxf htrue (Finset.mem_insert_of_mem hl)).mono le_rfl (Nat.zero_le c),
      (PXFc.axTrue b r v hxf htrue (Finset.mem_insert_of_mem hl)).mono le_rfl (Nat.zero_le c)⟩
  | @verumR Γ h =>
    intro _ _ _
    have ht : (⊤ : Form LX) ∈ Γ.erase (φ ⋏ ψ) :=
      Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), h⟩
    simp only [Deriv.o]
    exact ⟨(PXFc.verumR (Finset.mem_insert_of_mem ht)).mono le_rfl (Nat.zero_le c),
      (PXFc.verumR (Finset.mem_insert_of_mem ht)).mono le_rfl (Nat.zero_le c)⟩
  | @weak Δ Γ d' hsub ih =>
    intro hxf hcr hmem
    simp only [Deriv.cr] at hcr
    simp only [Deriv.o]
    by_cases hd : (φ ⋏ ψ) ∈ Δ
    · exact ⟨(ih hxf hcr hd).1.weakening
          (Finset.insert_subset_insert _ (Finset.erase_subset_erase _ hsub)),
        (ih hxf hcr hd).2.weakening
          (Finset.insert_subset_insert _ (Finset.erase_subset_erase _ hsub))⟩
    · have base : PXFc d'.o c Δ := ⟨d', le_rfl, hcr, hxf⟩
      have hΔ : Δ ⊆ Γ.erase (φ ⋏ ψ) := fun x hx =>
        Finset.mem_erase.mpr ⟨fun e => hd (e ▸ hx), hsub hx⟩
      exact ⟨base.weakening (fun x hx => Finset.mem_insert_of_mem (hΔ hx)),
        base.weakening (fun x hx => Finset.mem_insert_of_mem (hΔ hx))⟩
  | @andI Γ₀ φ' ψ' dφ dψ ihφ ihψ =>
    intro hxf hcr hmem
    simp only [Deriv.cr] at hcr
    simp only [Deriv.o]
    have hcrφ : dφ.cr ≤ (c : ℕ∞) := le_trans (le_max_left _ _) hcr
    have hcrψ : dψ.cr ≤ (c : ℕ∞) := le_trans (le_max_right _ _) hcr
    have hbφ : dφ.o ≤ max dφ.o dψ.o + 1 :=
      le_trans (le_max_left _ _) (le_of_lt (lt_add_of_pos_right _ one_pos))
    have hbψ : dψ.o ≤ max dφ.o dψ.o + 1 :=
      le_trans (le_max_right _ _) (le_of_lt (lt_add_of_pos_right _ one_pos))
    by_cases hhd : (φ' ⋏ ψ') = (φ ⋏ ψ)
    · obtain ⟨rfl, rfl⟩ := (Semiformula.and_inj _ _ _ _).mp hhd.symm
      have hL : PXFc (max dφ.o dψ.o + 1) c (insert φ ((insert (φ ⋏ ψ) Γ₀).erase (φ ⋏ ψ))) := by
        by_cases hd : (φ ⋏ ψ) ∈ Γ₀
        · refine ((ihφ hxf.1 hcrφ (Finset.mem_insert_of_mem hd)).1.weakening ?_).mono hbφ le_rfl
          intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto
        · have base : PXFc dφ.o c (insert φ Γ₀) := ⟨dφ, le_rfl, hcrφ, hxf.1⟩
          refine (base.weakening ?_).mono hbφ le_rfl
          intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
          rcases hx with rfl | hx
          · tauto
          · exact Or.inr ⟨fun e => hd (e ▸ hx), Or.inr hx⟩
      have hR : PXFc (max dφ.o dψ.o + 1) c (insert ψ ((insert (φ ⋏ ψ) Γ₀).erase (φ ⋏ ψ))) := by
        by_cases hd : (φ ⋏ ψ) ∈ Γ₀
        · refine ((ihψ hxf.2 hcrψ (Finset.mem_insert_of_mem hd)).2.weakening ?_).mono hbψ le_rfl
          intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto
        · have base : PXFc dψ.o c (insert ψ Γ₀) := ⟨dψ, le_rfl, hcrψ, hxf.2⟩
          refine (base.weakening ?_).mono hbψ le_rfl
          intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
          rcases hx with rfl | hx
          · tauto
          · exact Or.inr ⟨fun e => hd (e ▸ hx), Or.inr hx⟩
      exact ⟨hL, hR⟩
    · have hmem0 : (φ ⋏ ψ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhd e.symm
      refine ⟨?_, ?_⟩
      · have Pφ := ((ihφ hxf.1 hcrφ (Finset.mem_insert_of_mem hmem0)).1).weakening
          (invPush1' φ φ' (φ ⋏ ψ) Γ₀)
        have Pψ := ((ihψ hxf.2 hcrψ (Finset.mem_insert_of_mem hmem0)).1).weakening
          (invPush1' φ ψ' (φ ⋏ ψ) Γ₀)
        exact (PXFc.andI φ' ψ' Pφ Pψ).weakening (invPull1' φ hhd Γ₀)
      · have Pφ := ((ihφ hxf.1 hcrφ (Finset.mem_insert_of_mem hmem0)).2).weakening
          (invPush1' ψ φ' (φ ⋏ ψ) Γ₀)
        have Pψ := ((ihψ hxf.2 hcrψ (Finset.mem_insert_of_mem hmem0)).2).weakening
          (invPush1' ψ ψ' (φ ⋏ ψ) Γ₀)
        exact (PXFc.andI φ' ψ' Pφ Pψ).weakening (invPull1' ψ hhd Γ₀)
  | @orI Γ₀ φ' ψ' d' ih =>
    intro hxf hcr hmem
    simp only [Deriv.cr] at hcr
    simp only [Deriv.o]
    have hhead : (φ' ⋎ ψ') ≠ (φ ⋏ ψ) := by intro h; simp [Vee.vee, Wedge.wedge] at h
    have hmem0 : (φ ⋏ ψ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
    have mk : ∀ b : Form LX,
        PXFc d'.o c (insert b ((insert φ' (insert ψ' Γ₀)).erase (φ ⋏ ψ))) →
        PXFc (d'.o + 1) c (insert b ((insert (φ' ⋎ ψ') Γ₀).erase (φ ⋏ ψ))) := by
      intro b P
      have hsub : insert b ((insert φ' (insert ψ' Γ₀)).erase (φ ⋏ ψ))
            ⊆ insert φ' (insert ψ' (insert b (Γ₀.erase (φ ⋏ ψ)))) := by
        intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto
      exact (PXFc.orI φ' ψ' (P.weakening hsub)).weakening (invPull1' b hhead Γ₀)
    exact ⟨mk φ ((ih hxf hcr (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hmem0))).1),
      mk ψ ((ih hxf hcr (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hmem0))).2)⟩
  | @allω Γ₀ χ' d' ih =>
    intro hxf hcr hmem
    simp only [Deriv.cr] at hcr
    simp only [Deriv.o]
    have hhead : (∀⁰ χ') ≠ (φ ⋏ ψ) := by intro h; simp [Wedge.wedge] at h
    have hmem0 : (φ ⋏ ψ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
    have mk : ∀ b : Form LX,
        (∀ m, PXFc (d' m).o c (insert b ((insert (χ'/[nm m]) Γ₀).erase (φ ⋏ ψ)))) →
        PXFc ((⨆ m, (d' m).o) + 1) c (insert b ((insert (∀⁰ χ') Γ₀).erase (φ ⋏ ψ))) := by
      intro b P
      have key : ∀ m, PXFc (d' m).o c (insert (χ'/[nm m]) (insert b (Γ₀.erase (φ ⋏ ψ)))) :=
        fun m => (P m).weakening (invPush1' b (χ'/[nm m]) (φ ⋏ ψ) Γ₀)
      exact (PXFc.allω χ' key).weakening (invPull1' b hhead Γ₀)
    refine ⟨mk φ (fun m => ?_), mk ψ (fun m => ?_)⟩
    · exact (ih m (hxf m) (le_trans (le_iSup (fun j => (d' j).cr) m) hcr)
        (Finset.mem_insert_of_mem hmem0)).1
    · exact (ih m (hxf m) (le_trans (le_iSup (fun j => (d' j).cr) m) hcr)
        (Finset.mem_insert_of_mem hmem0)).2
  | @exI Γ₀ χ' n d' ih =>
    intro hxf hcr hmem
    simp only [Deriv.cr] at hcr
    simp only [Deriv.o]
    have hhead : (∃⁰ χ') ≠ (φ ⋏ ψ) := by intro h; simp [ExsQuantifier.exs, Wedge.wedge] at h
    have hmem0 : (φ ⋏ ψ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
    refine ⟨?_, ?_⟩
    · have P := ((ih hxf hcr (Finset.mem_insert_of_mem hmem0)).1).weakening
        (invPush1' φ (χ'/[nm n]) (φ ⋏ ψ) Γ₀)
      exact (PXFc.exI χ' n P).weakening (invPull1' φ hhead Γ₀)
    · have P := ((ih hxf hcr (Finset.mem_insert_of_mem hmem0)).2).weakening
        (invPush1' ψ (χ'/[nm n]) (φ ⋏ ψ) Γ₀)
      exact (PXFc.exI χ' n P).weakening (invPull1' ψ hhead Γ₀)
  | @cut Γ₀ ξ d₁ d₂ ih₁ ih₂ =>
    intro hxf hcr hmem
    simp only [Deriv.cr] at hcr
    simp only [Deriv.o]
    have hcξ : (ξ.complexity + 1 : ℕ∞) ≤ (c : ℕ∞) := (le_max_left _ _).trans hcr
    have hcr1 : d₁.cr ≤ (c : ℕ∞) := (le_max_left d₁.cr d₂.cr).trans ((le_max_right _ _).trans hcr)
    have hcr2 : d₂.cr ≤ (c : ℕ∞) := (le_max_right d₁.cr d₂.cr).trans ((le_max_right _ _).trans hcr)
    refine ⟨?_, ?_⟩
    · have P₁ := ((ih₁ hxf.1 hcr1 (Finset.mem_insert_of_mem hmem)).1).weakening
        (invPush1' φ ξ (φ ⋏ ψ) Γ₀)
      have P₂ := ((ih₂ hxf.2 hcr2 (Finset.mem_insert_of_mem hmem)).1).weakening
        (invPush1' φ (∼ξ) (φ ⋏ ψ) Γ₀)
      exact PXFc.cut ξ hcξ P₁ P₂
    · have P₁ := ((ih₁ hxf.1 hcr1 (Finset.mem_insert_of_mem hmem)).2).weakening
        (invPush1' ψ ξ (φ ⋏ ψ) Γ₀)
      have P₂ := ((ih₂ hxf.2 hcr2 (Finset.mem_insert_of_mem hmem)).2).weakening
        (invPush1' ψ (∼ξ) (φ ⋏ ψ) Γ₀)
      exact PXFc.cut ξ hcξ P₁ P₂

/-- **∧-inversion, left conjunct, relaxed bound**, `XFreeAx`-preserving. -/
theorem PXFc.andInvL {α : Ordinal.{0}} {c : ℕ} {Γ : Seq LX} {φ ψ : Form LX} (hmem : (φ ⋏ ψ) ∈ Γ)
    (h : PXFc α c Γ) : PXFc α c (insert φ (Γ.erase (φ ⋏ ψ))) := by
  rcases h with ⟨d, ho, hcr, hxf⟩
  exact (andInvAux_x d hxf hcr hmem).1.mono ho le_rfl

/-- **∧-inversion, right conjunct, relaxed bound**, `XFreeAx`-preserving. -/
theorem PXFc.andInvR {α : Ordinal.{0}} {c : ℕ} {Γ : Seq LX} {φ ψ : Form LX} (hmem : (φ ⋏ ψ) ∈ Γ)
    (h : PXFc α c Γ) : PXFc α c (insert ψ (Γ.erase (φ ⋏ ψ))) := by
  rcases h with ⟨d, ho, hcr, hxf⟩
  exact (andInvAux_x d hxf hcr hmem).2.mono ho le_rfl

/-- **ω/∀-inversion** at cut rank `≤ c`, `XFreeAx`-preserving. For the universal instance `i`. -/
theorem allInvAux_x {χ : SyntacticSemiformula LX 1} {c : ℕ} (i : ℕ) : ∀ {Γ : Seq LX} (d : Deriv Γ),
    XFreeAx d → d.cr ≤ (c : ℕ∞) → (∀⁰ χ) ∈ Γ →
    PXFc d.o c (insert (χ/[nm i]) (Γ.erase (∀⁰ χ))) := by
  intro Γ d
  induction d with
  | @axL Γ k r v hp hn =>
    intro _ _ _
    have hr : Semiformula.rel r v ∈ Γ.erase (∀⁰ χ) :=
      Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), hp⟩
    have hn' : Semiformula.nrel r v ∈ Γ.erase (∀⁰ χ) :=
      Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), hn⟩
    simp only [Deriv.o]
    exact (PXFc.axL r v (Finset.mem_insert_of_mem hr)
      (Finset.mem_insert_of_mem hn')).mono le_rfl (Nat.zero_le c)
  | @axLv Γ k r v v' hval hp hn =>
    intro _ _ _
    have hr : Semiformula.rel r v ∈ Γ.erase (∀⁰ χ) :=
      Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), hp⟩
    have hn' : Semiformula.nrel r v' ∈ Γ.erase (∀⁰ χ) :=
      Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), hn⟩
    simp only [Deriv.o]
    exact (PXFc.axLv r v v' hval (Finset.mem_insert_of_mem hr)
      (Finset.mem_insert_of_mem hn')).mono le_rfl (Nat.zero_le c)
  | @axTrue Γ k b r v htrue hmem =>
    intro hxf _ _
    have hl : signedLit b r v ∈ Γ.erase (∀⁰ χ) :=
      Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by cases b <;> simp [signedLit]), hmem⟩
    simp only [Deriv.o]
    exact (PXFc.axTrue b r v hxf htrue (Finset.mem_insert_of_mem hl)).mono le_rfl (Nat.zero_le c)
  | @verumR Γ h =>
    intro _ _ _
    have ht : (⊤ : Form LX) ∈ Γ.erase (∀⁰ χ) :=
      Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), h⟩
    simp only [Deriv.o]
    exact (PXFc.verumR (Finset.mem_insert_of_mem ht)).mono le_rfl (Nat.zero_le c)
  | @weak Δ Γ d' hsub ih =>
    intro hxf hcr hmem
    simp only [Deriv.cr] at hcr
    simp only [Deriv.o]
    by_cases hd : (∀⁰ χ) ∈ Δ
    · exact (ih hxf hcr hd).weakening
        (Finset.insert_subset_insert _ (Finset.erase_subset_erase _ hsub))
    · have base : PXFc d'.o c Δ := ⟨d', le_rfl, hcr, hxf⟩
      refine base.weakening ?_
      intro x hx
      exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨fun e => hd (e ▸ hx), hsub hx⟩)
  | @andI Γ₀ φ' ψ' dφ dψ ihφ ihψ =>
    intro hxf hcr hmem
    simp only [Deriv.cr] at hcr
    simp only [Deriv.o]
    have hhead : (φ' ⋏ ψ') ≠ (∀⁰ χ) := by intro h; simp [Wedge.wedge] at h
    have hmem0 : (∀⁰ χ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
    have hcrφ : dφ.cr ≤ (c : ℕ∞) := le_trans (le_max_left _ _) hcr
    have hcrψ : dψ.cr ≤ (c : ℕ∞) := le_trans (le_max_right _ _) hcr
    have Pφ := (ihφ hxf.1 hcrφ (Finset.mem_insert_of_mem hmem0)).weakening
      (invPush1' (χ/[nm i]) φ' (∀⁰ χ) Γ₀)
    have Pψ := (ihψ hxf.2 hcrψ (Finset.mem_insert_of_mem hmem0)).weakening
      (invPush1' (χ/[nm i]) ψ' (∀⁰ χ) Γ₀)
    exact (PXFc.andI φ' ψ' Pφ Pψ).weakening (invPull1' (χ/[nm i]) hhead Γ₀)
  | @orI Γ₀ φ' ψ' d' ih =>
    intro hxf hcr hmem
    simp only [Deriv.cr] at hcr
    simp only [Deriv.o]
    have hhead : (φ' ⋎ ψ') ≠ (∀⁰ χ) := by intro h; simp [Vee.vee] at h
    have hmem0 : (∀⁰ χ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
    have hsub : insert (χ/[nm i]) ((insert φ' (insert ψ' Γ₀)).erase (∀⁰ χ))
          ⊆ insert φ' (insert ψ' (insert (χ/[nm i]) (Γ₀.erase (∀⁰ χ)))) := by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto
    have P := (ih hxf hcr (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hmem0))).weakening hsub
    exact (PXFc.orI φ' ψ' P).weakening (invPull1' (χ/[nm i]) hhead Γ₀)
  | @allω Γ₀ χ' d' ih =>
    intro hxf hcr hmem
    simp only [Deriv.cr] at hcr
    simp only [Deriv.o]
    by_cases hhd : (∀⁰ χ') = (∀⁰ χ)
    · obtain rfl := (Semiformula.all_inj _ _).mp hhd
      have hcrn : (d' i).cr ≤ (c : ℕ∞) := le_trans (le_iSup (fun m => (d' m).cr) i) hcr
      have hbound : (d' i).o ≤ (⨆ m, (d' m).o) + 1 :=
        le_trans (Ordinal.le_iSup (fun m => (d' m).o) i) (le_of_lt (lt_add_of_pos_right _ one_pos))
      by_cases hd : (∀⁰ χ') ∈ Γ₀
      · have P := ih i (hxf i) hcrn (Finset.mem_insert_of_mem hd)
        refine (P.weakening ?_).mono hbound le_rfl
        intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto
      · have base : PXFc (d' i).o c (insert (χ'/[nm i]) Γ₀) := ⟨d' i, le_rfl, hcrn, hxf i⟩
        refine (base.weakening ?_).mono hbound le_rfl
        intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
        rcases hx with rfl | hx
        · tauto
        · exact Or.inr ⟨fun e => hd (e ▸ hx), Or.inr hx⟩
    · have hmem0 : (∀⁰ χ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhd e.symm
      have key : ∀ m, PXFc (d' m).o c
          (insert (χ'/[nm m]) (insert (χ/[nm i]) (Γ₀.erase (∀⁰ χ)))) := fun m =>
        (ih m (hxf m) (le_trans (le_iSup (fun j => (d' j).cr) m) hcr)
          (Finset.mem_insert_of_mem hmem0)).weakening (invPush1' (χ/[nm i]) (χ'/[nm m]) (∀⁰ χ) Γ₀)
      exact (PXFc.allω χ' key).weakening (invPull1' (χ/[nm i]) hhd Γ₀)
  | @exI Γ₀ χ' n d' ih =>
    intro hxf hcr hmem
    simp only [Deriv.cr] at hcr
    simp only [Deriv.o]
    have hhead : (∃⁰ χ') ≠ (∀⁰ χ) := by intro h; simp [ExsQuantifier.exs, UnivQuantifier.all] at h
    have hmem0 : (∀⁰ χ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
    have P := (ih hxf hcr (Finset.mem_insert_of_mem hmem0)).weakening
      (invPush1' (χ/[nm i]) (χ'/[nm n]) (∀⁰ χ) Γ₀)
    exact (PXFc.exI χ' n P).weakening (invPull1' (χ/[nm i]) hhead Γ₀)
  | @cut Γ₀ ξ d₁ d₂ ih₁ ih₂ =>
    intro hxf hcr hmem
    simp only [Deriv.cr] at hcr
    simp only [Deriv.o]
    have hcξ : (ξ.complexity + 1 : ℕ∞) ≤ (c : ℕ∞) := (le_max_left _ _).trans hcr
    have hcr1 : d₁.cr ≤ (c : ℕ∞) := (le_max_left d₁.cr d₂.cr).trans ((le_max_right _ _).trans hcr)
    have hcr2 : d₂.cr ≤ (c : ℕ∞) := (le_max_right d₁.cr d₂.cr).trans ((le_max_right _ _).trans hcr)
    have P₁ := (ih₁ hxf.1 hcr1 (Finset.mem_insert_of_mem hmem)).weakening
      (invPush1' (χ/[nm i]) ξ (∀⁰ χ) Γ₀)
    have P₂ := (ih₂ hxf.2 hcr2 (Finset.mem_insert_of_mem hmem)).weakening
      (invPush1' (χ/[nm i]) (∼ξ) (∀⁰ χ) Γ₀)
    exact PXFc.cut ξ hcξ P₁ P₂

/-- **ω-inversion at a relaxed bound**, `XFreeAx`-preserving. -/
theorem PXFc.allInv {α : Ordinal.{0}} {c : ℕ} {Γ : Seq LX} {χ : SyntacticSemiformula LX 1}
    (hmem : (∀⁰ χ) ∈ Γ) (i : ℕ) (h : PXFc α c Γ) :
    PXFc α c (insert (χ/[nm i]) (Γ.erase (∀⁰ χ))) := by
  rcases h with ⟨d, ho, hcr, hxf⟩
  exact (allInvAux_x i d hxf hcr hmem).mono ho le_rfl

/-! ### Cut reductions (§19.5 ∧/∨, §19.6 ∀/∃) over `PXFc` (port of `ZinftyGen.cutReduce*`). -/

/-- ∧/∨ principal cut reduction (Towsner Thm 19.5), `XFreeAx`-preserving. -/
theorem PXFc.cutReduceConj {a b : Form LX} {c : ℕ} {α β : Ordinal.{0}} {Γ : Seq LX}
    (ha : (a.complexity + 1 : ℕ∞) ≤ c) (hb : (b.complexity + 1 : ℕ∞) ≤ c)
    (hC : PXFc α c (insert (a ⋏ b) Γ)) (hNC : PXFc β c (insert (∼a ⋎ ∼b) Γ)) :
    PXFc (max α β + 1 + 1) c Γ := by
  have hA : PXFc α c (insert a Γ) :=
    (hC.andInvL (Finset.mem_insert_self _ _)).weakening (by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto)
  have hB : PXFc α c (insert b Γ) :=
    (hC.andInvR (Finset.mem_insert_self _ _)).weakening (by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto)
  have hNab : PXFc β c (insert (∼a) (insert (∼b) Γ)) :=
    (hNC.orInv (Finset.mem_insert_self _ _)).weakening (by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto)
  have cutA : PXFc (max α β + 1) c (insert (∼b) Γ) :=
    PXFc.cut a ha (hA.weakening (by
      intro x hx; simp only [Finset.mem_insert] at hx ⊢; tauto)) hNab
  have cutB : PXFc (max α (max α β + 1) + 1) c Γ := PXFc.cut b hb hB cutA
  have he : max α (max α β + 1) + 1 = max α β + 1 + 1 := by
    congr 1
    exact max_eq_right (le_trans (le_max_left α β) (le_of_lt (lt_add_of_pos_right _ one_pos)))
  exact he ▸ cutB

/-- ∨/∧ principal cut reduction (dual; Towsner Thm 19.5), `XFreeAx`-preserving. -/
theorem PXFc.cutReduceDisj {a b : Form LX} {c : ℕ} {α β : Ordinal.{0}} {Γ : Seq LX}
    (ha : (a.complexity + 1 : ℕ∞) ≤ c) (hb : (b.complexity + 1 : ℕ∞) ≤ c)
    (hC : PXFc α c (insert (a ⋎ b) Γ)) (hNC : PXFc β c (insert (∼a ⋏ ∼b) Γ)) :
    PXFc (max α β + 1 + 1) c Γ := by
  have hAB : PXFc α c (insert a (insert b Γ)) :=
    (hC.orInv (Finset.mem_insert_self _ _)).weakening (by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto)
  have hNa : PXFc β c (insert (∼a) Γ) :=
    (hNC.andInvL (Finset.mem_insert_self _ _)).weakening (by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto)
  have hNb : PXFc β c (insert (∼b) Γ) :=
    (hNC.andInvR (Finset.mem_insert_self _ _)).weakening (by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto)
  have cutA : PXFc (max α β + 1) c (insert b Γ) :=
    PXFc.cut a ha hAB (hNa.weakening (by
      intro x hx; simp only [Finset.mem_insert] at hx ⊢; tauto))
  have cutB : PXFc (max (max α β + 1) β + 1) c Γ := PXFc.cut b hb cutA hNb
  have he : max (max α β + 1) β + 1 = max α β + 1 + 1 := by
    congr 1
    exact max_eq_left (le_trans (le_max_right α β) (le_of_lt (lt_add_of_pos_right _ one_pos)))
  exact he ▸ cutB

/-- Bound bookkeeping (binary commuting): `max (α+a+1) (α+b+1) + 1 ≤ α + (max a b + 1) + 1`. -/
private theorem cb_bnd (α a b : Ordinal.{0}) :
    max (α + a + 1) (α + b + 1) + 1 ≤ α + (max a b + 1) + 1 := by
  refine add_le_add_left (max_le ?_ ?_) 1
  · calc α + a + 1 = α + (a + 1) := add_assoc α a 1
      _ ≤ α + (max a b + 1) := (add_le_add_iff_left α).mpr (add_le_add_left (le_max_left a b) 1)
  · calc α + b + 1 = α + (b + 1) := add_assoc α b 1
      _ ≤ α + (max a b + 1) := (add_le_add_iff_left α).mpr (add_le_add_left (le_max_right a b) 1)

/-- Bound bookkeeping (unary commuting): `α + a + 1 + 1 = α + (a + 1) + 1`. -/
private theorem cb_bnd1 (α a : Ordinal.{0}) : α + a + 1 + 1 ≤ α + (a + 1) + 1 :=
  le_of_eq (by rw [add_assoc α a 1])

/-- Bound bookkeeping (ω-rule commuting). -/
private theorem cb_bnd_sup (α : Ordinal.{0}) (f : ℕ → Ordinal.{0}) :
    (⨆ n, (α + f n + 1)) + 1 ≤ α + ((⨆ n, f n) + 1) + 1 := by
  refine add_le_add_left ?_ 1
  apply Ordinal.iSup_le
  intro n
  calc α + f n + 1 = α + (f n + 1) := add_assoc α (f n) 1
    _ ≤ α + ((⨆ m, f m) + 1) := (add_le_add_iff_left α).mpr (add_le_add_left (Ordinal.le_iSup f n) 1)

/-- Frame subset: push an `insert` out of the `erase`/`∪`-framed context. -/
private theorem cb_frame_in (a e : Form LX) (s t : Seq LX) :
    (insert a s).erase e ∪ t ⊆ insert a (s.erase e ∪ t) := by
  intro x hx
  simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢
  rcases hx with ⟨hne, hxa | hxs⟩ | hxt
  · exact Or.inl hxa
  · exact Or.inr (Or.inl ⟨hne, hxs⟩)
  · exact Or.inr (Or.inr hxt)

/-- The induction core of the ∀/∃ reduction over `PXFc` (port of `cutReduceAllAux`), `XFreeAx`-
preserving. `fam` is the ∀-inversion family; induct on the ∃-side derivation `d`. -/
theorem PXFc.cutReduceAllAux {φ : SyntacticSemiformula LX 1} {c : ℕ} {α : Ordinal.{0}}
    {Γ : Seq LX} (hφc : (φ.complexity + 1 : ℕ∞) ≤ c)
    (fam : ∀ n, PXFc α c (insert (φ/[nm n]) Γ)) :
    ∀ {Δ : Seq LX} (d : Deriv Δ), XFreeAx d → d.cr ≤ (c : ℕ∞) → (∃⁰ ∼φ) ∈ Δ →
      PXFc (α + d.o + 1) c (Δ.erase (∃⁰ ∼φ) ∪ Γ) := by
  intro Δ d
  induction d with
  | @axL Δ k r v hp hn =>
    intro _ _ _
    simp only [Deriv.o]
    refine (PXFc.axL r v ?_ ?_).mono zero_le (Nat.zero_le c)
    · exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), hp⟩)
    · exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), hn⟩)
  | @axLv Δ k r v v' hval hp hn =>
    intro _ _ _
    simp only [Deriv.o]
    refine (PXFc.axLv r v v' hval ?_ ?_).mono zero_le (Nat.zero_le c)
    · exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), hp⟩)
    · exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), hn⟩)
  | @axTrue Δ k b r v htrue hmem =>
    intro hxf _ _
    simp only [Deriv.o]
    refine (PXFc.axTrue b r v hxf htrue ?_).mono zero_le (Nat.zero_le c)
    exact Finset.mem_union_left _ (Finset.mem_erase.mpr
      ⟨Semiformula.ne_of_ne_complexity (by cases b <;> simp [signedLit]), hmem⟩)
  | @verumR Δ h =>
    intro _ _ _
    simp only [Deriv.o]
    refine (PXFc.verumR ?_).mono zero_le (Nat.zero_le c)
    exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), h⟩)
  | @weak Δ' Δ d' hsub ih =>
    intro hxf hcr hmem
    simp only [Deriv.cr] at hcr
    simp only [Deriv.o]
    by_cases hd : (∃⁰ ∼φ) ∈ Δ'
    · exact (ih hxf hcr hd).weakening (by
        intro x hx; simp only [Finset.mem_union, Finset.mem_erase] at hx ⊢
        rcases hx with ⟨hne, hxΔ'⟩ | hxΓ
        · exact Or.inl ⟨hne, hsub hxΔ'⟩
        · exact Or.inr hxΓ)
    · refine (show PXFc d'.o c Δ' from ⟨d', le_rfl, hcr, hxf⟩).weakening ?_ |>.mono ?_ le_rfl
      · intro x hx
        exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨fun e => hd (e ▸ hx), hsub hx⟩)
      · exact le_trans (CanonicallyOrderedAdd.le_add_self d'.o α)
          (le_of_lt (lt_add_of_pos_right _ one_pos))
  | @andI Γ₀ χ₀ χ₁ d₀ d₁ ih₀ ih₁ =>
    intro hxf hcr hmem
    simp only [Deriv.cr] at hcr
    simp only [Deriv.o]
    have hhead : (χ₀ ⋏ χ₁) ≠ (∃⁰ ∼φ) := by intro h; simp [Wedge.wedge, ExsQuantifier.exs] at h
    have hmem0 : (∃⁰ ∼φ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
    have hcr0 : d₀.cr ≤ (c : ℕ∞) := le_trans (le_max_left _ _) hcr
    have hcr1 : d₁.cr ≤ (c : ℕ∞) := le_trans (le_max_right _ _) hcr
    have P0 : PXFc (α + d₀.o + 1) c (insert χ₀ (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) :=
      (ih₀ hxf.1 hcr0 (Finset.mem_insert_of_mem hmem0)).weakening (by
        intro x hx; simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢; tauto)
    have P1 : PXFc (α + d₁.o + 1) c (insert χ₁ (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) :=
      (ih₁ hxf.2 hcr1 (Finset.mem_insert_of_mem hmem0)).weakening (by
        intro x hx; simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢; tauto)
    refine ((PXFc.andI χ₀ χ₁ P0 P1).weakening (show
        insert (χ₀ ⋏ χ₁) (Γ₀.erase (∃⁰ ∼φ) ∪ Γ) ⊆ (insert (χ₀ ⋏ χ₁) Γ₀).erase (∃⁰ ∼φ) ∪ Γ from by
      intro x hx; simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢
      rcases hx with rfl | hx
      · exact Or.inl ⟨hhead, Or.inl rfl⟩
      · tauto)).mono (cb_bnd α d₀.o d₁.o) le_rfl
  | @orI Γ₀ χ₀ χ₁ d' ih =>
    intro hxf hcr hmem
    simp only [Deriv.cr] at hcr
    simp only [Deriv.o]
    have hhead : (χ₀ ⋎ χ₁) ≠ (∃⁰ ∼φ) := by intro h; simp [Vee.vee, ExsQuantifier.exs] at h
    have hmem0 : (∃⁰ ∼φ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
    have P : PXFc (α + d'.o + 1) c (insert χ₀ (insert χ₁ (Γ₀.erase (∃⁰ ∼φ) ∪ Γ))) :=
      (ih hxf hcr (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hmem0))).weakening (by
        intro x hx; simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢; tauto)
    refine ((PXFc.orI χ₀ χ₁ P).weakening (show
        insert (χ₀ ⋎ χ₁) (Γ₀.erase (∃⁰ ∼φ) ∪ Γ) ⊆ (insert (χ₀ ⋎ χ₁) Γ₀).erase (∃⁰ ∼φ) ∪ Γ from by
      intro x hx; simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢
      rcases hx with rfl | hx
      · exact Or.inl ⟨hhead, Or.inl rfl⟩
      · tauto)).mono (cb_bnd1 α d'.o) le_rfl
  | @allω Γ₀ χ' d' ih =>
    intro hxf hcr hmem
    simp only [Deriv.cr] at hcr
    simp only [Deriv.o]
    have hhead : (∀⁰ χ') ≠ (∃⁰ ∼φ) := by intro h; simp [UnivQuantifier.all, ExsQuantifier.exs] at h
    have hmem0 : (∃⁰ ∼φ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
    have key : ∀ n, PXFc (α + (d' n).o + 1) c (insert (χ'/[nm n]) (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) :=
      fun n => (ih n (hxf n) (le_trans (le_iSup (fun m => (d' m).cr) n) hcr)
        (Finset.mem_insert_of_mem hmem0)).weakening (by
          intro x hx; simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢; tauto)
    refine ((PXFc.allω χ' key).weakening (show
        insert (∀⁰ χ') (Γ₀.erase (∃⁰ ∼φ) ∪ Γ) ⊆ (insert (∀⁰ χ') Γ₀).erase (∃⁰ ∼φ) ∪ Γ from by
      intro x hx; simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢
      rcases hx with rfl | hx
      · exact Or.inl ⟨hhead, Or.inl rfl⟩
      · tauto)).mono (cb_bnd_sup α (fun n => (d' n).o)) le_rfl
  | @exI Γ₀ χ' n d' ih =>
    intro hxf hcr hmem
    simp only [Deriv.cr] at hcr
    simp only [Deriv.o]
    by_cases hhd : (∃⁰ χ') = (∃⁰ ∼φ)
    · have hχ : χ' = ∼φ := by have := hhd; simpa [ExsQuantifier.exs] using this
      subst hχ
      rw [Finset.erase_insert_eq_erase]
      have hcutfml : (((φ/[nm n]).complexity + 1 : ℕ∞)) ≤ c := by simpa using hφc
      have hNeg : (∼φ)/[nm n] = ∼(φ/[nm n]) := by simp
      have famn := (fam n).weakening (show insert (φ/[nm n]) Γ
          ⊆ insert (φ/[nm n]) (Γ₀.erase (∃⁰ ∼φ) ∪ Γ) from by
        intro x hx; simp only [Finset.mem_insert, Finset.mem_union] at hx ⊢; tauto)
      by_cases hd : (∃⁰ ∼φ) ∈ Γ₀
      · have Premise : PXFc (α + d'.o + 1) c (insert ((∼φ)/[nm n]) (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) :=
          (ih hxf hcr (Finset.mem_insert_of_mem hd)).weakening (by
            intro x hx; simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢; tauto)
        have hctx : insert ((∼φ)/[nm n]) (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)
            = insert (∼(φ/[nm n])) (Γ₀.erase (∃⁰ ∼φ) ∪ Γ) := by rw [hNeg]
        have hcut := PXFc.cut (φ/[nm n]) hcutfml famn (Premise.cast hctx)
        refine hcut.mono ?_ le_rfl
        refine add_le_add_left ?_ 1
        exact max_le le_self_add (le_of_eq (add_assoc α d'.o 1))
      · have base : PXFc d'.o c (insert (∼(φ/[nm n])) (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) := by
          refine (show PXFc d'.o c (insert ((∼φ)/[nm n]) Γ₀) from ⟨d', le_rfl, hcr, hxf⟩).weakening ?_
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_erase] at hx ⊢
          rcases hx with rfl | hxΓ₀
          · left; rw [hNeg]
          · exact Or.inr (Or.inl ⟨fun e => hd (e ▸ hxΓ₀), hxΓ₀⟩)
        have hcut := PXFc.cut (φ/[nm n]) hcutfml famn base
        refine hcut.mono ?_ le_rfl
        refine add_le_add_left ?_ 1
        exact max_le le_self_add
          (le_trans (le_of_lt (lt_add_of_pos_right _ one_pos))
            (CanonicallyOrderedAdd.le_add_self (d'.o + 1) α))
    · have hhead : (∃⁰ χ') ≠ (∃⁰ ∼φ) := hhd
      have hmem0 : (∃⁰ ∼φ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
      have P : PXFc (α + d'.o + 1) c (insert (χ'/[nm n]) (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) :=
        (ih hxf hcr (Finset.mem_insert_of_mem hmem0)).weakening (by
          intro x hx; simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢; tauto)
      refine ((PXFc.exI χ' n P).weakening (show
          insert (∃⁰ χ') (Γ₀.erase (∃⁰ ∼φ) ∪ Γ) ⊆ (insert (∃⁰ χ') Γ₀).erase (∃⁰ ∼φ) ∪ Γ from by
        intro x hx; simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢
        rcases hx with rfl | hx
        · exact Or.inl ⟨hhead, Or.inl rfl⟩
        · tauto)).mono (cb_bnd1 α d'.o) le_rfl
  | @cut Γ₀ ξ d₁ d₂ ih₁ ih₂ =>
    intro hxf hcr hmem
    simp only [Deriv.cr] at hcr
    simp only [Deriv.o]
    have hcξ : (ξ.complexity + 1 : ℕ∞) ≤ c := (le_max_left _ _).trans hcr
    have hcr1 : d₁.cr ≤ (c : ℕ∞) := (le_max_left d₁.cr d₂.cr).trans ((le_max_right _ _).trans hcr)
    have hcr2 : d₂.cr ≤ (c : ℕ∞) := (le_max_right d₁.cr d₂.cr).trans ((le_max_right _ _).trans hcr)
    have P1 := (ih₁ hxf.1 hcr1 (Finset.mem_insert_of_mem hmem)).weakening (cb_frame_in ξ (∃⁰ ∼φ) Γ₀ Γ)
    have P2 := (ih₂ hxf.2 hcr2 (Finset.mem_insert_of_mem hmem)).weakening (cb_frame_in (∼ξ) (∃⁰ ∼φ) Γ₀ Γ)
    exact (PXFc.cut ξ hcξ P1 P2).mono (cb_bnd α d₁.o d₂.o) le_rfl

/-- **Cut reduction, ∀/∃ principal** (Towsner Thm 19.6), `XFreeAx`-preserving. -/
theorem PXFc.cutReduceAll {φ : SyntacticSemiformula LX 1} {c : ℕ} {α β : Ordinal.{0}}
    {Γ : Seq LX} (hφc : (φ.complexity + 1 : ℕ∞) ≤ c)
    (hC : PXFc α c (insert (∀⁰ φ) Γ)) (hNC : PXFc β c (insert (∃⁰ ∼φ) Γ)) :
    PXFc (α + β + 1) c Γ := by
  have fam : ∀ n, PXFc α c (insert (φ/[nm n]) Γ) := fun n =>
    (hC.allInv (Finset.mem_insert_self _ _) n).weakening (by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto)
  rcases hNC with ⟨d, ho, hcr, hxf⟩
  have haux := PXFc.cutReduceAllAux hφc fam d hxf hcr (Finset.mem_insert_self _ _)
  refine (haux.weakening (show (insert (∃⁰ ∼φ) Γ).erase (∃⁰ ∼φ) ∪ Γ ⊆ Γ from by
    intro x hx; simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢; tauto)).mono ?_ le_rfl
  exact add_le_add_left ((add_le_add_iff_left α).mpr ho) 1

/-! ### Truth layer: removing false/⊥ literals + atomic cut, `XFreeAx`-preserving.

The ONLY `axTrue` leaves cut-elimination *introduces* are in `removeFalseLitAux`'s `axL` case, on the
**cut atom's** relation. We therefore require the removed literal to be **X-free** (`Sum.isLeft r₀`),
making those leaves X-free. `atomCut` supplies this: at an X-atom cut the truth branch is **vacuous**
(it needs an `axTrue` leaf equal to the cut atom = an X-`axTrue` leaf, forbidden by `XFreeAx`); the
helper `xfree_transport` extracts X-freeness of the cut atom from that very leaf. -/

/-- Head relation's `isLeft` (X-freeness) of an atomic literal; `false` on non-atoms. -/
def headIsLeft : Form LX → Bool
  | Semiformula.rel r _ => Sum.isLeft r
  | Semiformula.nrel r _ => Sum.isLeft r
  | _ => false

theorem headIsLeft_signedLit (b : Bool) {k} (r : LX.Rel k) (v) :
    headIsLeft (signedLit b r v) = Sum.isLeft r := by cases b <;> rfl

/-- If a known-X-free signed literal equals another signed literal, the latter's relation is X-free
too. (Used to discharge the `Sum.isLeft` side condition of `removeFalseLitAux` at atomic cuts.) -/
theorem xfree_transport {k₀} (b₀ : Bool) (r₀ : LX.Rel k₀) (v₀) (hxfree : Sum.isLeft r₀ = true)
    {k} (b : Bool) (r : LX.Rel k) (v) (h : signedLit b₀ r₀ v₀ = signedLit b r v) :
    Sum.isLeft r = true := by
  have hc := congrArg headIsLeft h
  rw [headIsLeft_signedLit, headIsLeft_signedLit] at hc
  rw [← hc]; exact hxfree

/-- Frame subset (dual of `cb_frame_in`), valid when the head `a` is not the erased formula. -/
private theorem cb_frame_out {a e : Form LX} (hne : a ≠ e) (s t : Seq LX) :
    insert a (s.erase e ∪ t) ⊆ (insert a s).erase e ∪ t := by
  intro x hx
  simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢
  rcases hx with rfl | (⟨hne', hxs⟩ | hxt)
  · exact Or.inl ⟨hne, Or.inl rfl⟩
  · exact Or.inl ⟨hne', Or.inr hxs⟩
  · exact Or.inr hxt

/-- **Removing a FALSE, X-free closed literal** from a cut-free `XFreeAx` derivation, bound- and
`XFreeAx`-preserving (Towsner Thm 19.2 truth layer). The emitted `axTrue` leaves are on the (X-free)
removed atom's relation. -/
theorem PXFc.removeFalseLitAux (b₀ : Bool) {k₀} (r₀ : (LX).Rel k₀) (v₀)
    (hxfree : Sum.isLeft r₀ = true) (hL : ¬ LitTrue (signedLit b₀ r₀ v₀)) :
    ∀ {Δ : Seq LX} (d : Deriv Δ), XFreeAx d → d.cr ≤ (0 : ℕ∞) →
      signedLit b₀ r₀ v₀ ∈ Δ → PXFc d.o 0 (Δ.erase (signedLit b₀ r₀ v₀)) := by
  set Lit : Form LX := signedLit b₀ r₀ v₀ with hLdef
  have hLne : ∀ (g : Form LX), g.complexity ≠ 0 → g ≠ Lit := by
    intro g hg; rw [hLdef]; exact Semiformula.ne_of_ne_complexity (by cases b₀ <;> simp [signedLit, hg])
  intro Δ d
  induction d with
  | @axL Δ k r v hp hn =>
    intro _ _ _; simp only [Deriv.o]
    by_cases h1 : Lit = Semiformula.rel r v
    · have htn : LitTrue (signedLit false r v) := by
        show LitTrue (Semiformula.nrel r v)
        rw [← Semiformula.neg_rel, litTrue_neg]; exact h1 ▸ hL
      have hxr : Sum.isLeft r = true :=
        xfree_transport b₀ r₀ v₀ hxfree true r v (hLdef ▸ h1)
      exact PXFc.axTrue false r v hxr htn (Finset.mem_erase.mpr ⟨by rw [h1]; simp [signedLit], hn⟩)
    · by_cases h2 : Lit = Semiformula.nrel r v
      · have htr : LitTrue (signedLit true r v) := by
          show LitTrue (Semiformula.rel r v)
          by_contra hc
          exact (h2 ▸ hL) (by rw [← Semiformula.neg_rel, litTrue_neg]; exact hc)
        have hxr : Sum.isLeft r = true :=
          xfree_transport b₀ r₀ v₀ hxfree false r v (hLdef ▸ h2)
        exact PXFc.axTrue true r v hxr htr (Finset.mem_erase.mpr ⟨by rw [h2]; simp [signedLit], hp⟩)
      · exact PXFc.axL r v (Finset.mem_erase.mpr ⟨fun e => h1 e.symm, hp⟩)
          (Finset.mem_erase.mpr ⟨fun e => h2 e.symm, hn⟩)
  | @axLv Δ k r va vb hval hp hn =>
    intro _ _ _; simp only [Deriv.o]
    by_cases h1 : Lit = Semiformula.rel r va
    · -- removed atom is the pair's positive; X-free (transported); the value-cong negative is true.
      have htn : LitTrue (signedLit false r vb) := by
        show LitTrue (Semiformula.nrel r vb)
        rw [← Semiformula.neg_rel, litTrue_neg]
        exact (litTrue_rel_congr r va vb hval).not.mp (h1 ▸ hL)
      have hxr : Sum.isLeft r = true := xfree_transport b₀ r₀ v₀ hxfree true r va (hLdef ▸ h1)
      exact PXFc.axTrue false r vb hxr htn (Finset.mem_erase.mpr ⟨by rw [h1]; simp [signedLit], hn⟩)
    · by_cases h2 : Lit = Semiformula.nrel r vb
      · have htr : LitTrue (signedLit true r va) := by
          show LitTrue (Semiformula.rel r va)
          refine (litTrue_rel_congr r va vb hval).mpr ?_
          by_contra hc
          exact (h2 ▸ hL) (by rw [← Semiformula.neg_rel, litTrue_neg]; exact hc)
        have hxr : Sum.isLeft r = true := xfree_transport b₀ r₀ v₀ hxfree false r vb (hLdef ▸ h2)
        exact PXFc.axTrue true r va hxr htr (Finset.mem_erase.mpr ⟨by rw [h2]; simp [signedLit], hp⟩)
      · exact PXFc.axLv r va vb hval (Finset.mem_erase.mpr ⟨fun e => h1 e.symm, hp⟩)
          (Finset.mem_erase.mpr ⟨fun e => h2 e.symm, hn⟩)
  | @axTrue Δ k b r v htrue hmem =>
    intro hxf _ _; simp only [Deriv.o]
    have hne : signedLit b r v ≠ Lit := fun e => hL (e ▸ htrue)
    exact PXFc.axTrue b r v hxf htrue (Finset.mem_erase.mpr ⟨hne, hmem⟩)
  | @verumR Δ h =>
    intro _ _ _; simp only [Deriv.o]
    exact PXFc.verumR (Finset.mem_erase.mpr ⟨by rw [hLdef]; exact (lit_ne_verum b₀ r₀ v₀).symm, h⟩)
  | @weak Δ' Δ d' hsub ih =>
    intro hxf hcr hmem; simp only [Deriv.cr] at hcr; simp only [Deriv.o]
    by_cases hd : Lit ∈ Δ'
    · exact (ih hxf hcr hd).weakening (Finset.erase_subset_erase _ hsub)
    · refine (show PXFc d'.o 0 Δ' from ⟨d', le_rfl, hcr, hxf⟩).weakening ?_
      intro x hx; exact Finset.mem_erase.mpr ⟨fun e => hd (e ▸ hx), hsub hx⟩
  | @andI Γ₀ χ₀ χ₁ d₀ d₁ ih₀ ih₁ =>
    intro hxf hcr hmem; simp only [Deriv.cr] at hcr; simp only [Deriv.o]
    have hhead : (χ₀ ⋏ χ₁) ≠ Lit := hLne _ (by simp)
    have hmem0 : Lit ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
    have P0 : PXFc d₀.o 0 (insert χ₀ (Γ₀.erase Lit)) :=
      (ih₀ hxf.1 (le_trans (le_max_left _ _) hcr) (Finset.mem_insert_of_mem hmem0)).weakening (by
        intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto)
    have P1 : PXFc d₁.o 0 (insert χ₁ (Γ₀.erase Lit)) :=
      (ih₁ hxf.2 (le_trans (le_max_right _ _) hcr) (Finset.mem_insert_of_mem hmem0)).weakening (by
        intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto)
    exact (PXFc.andI χ₀ χ₁ P0 P1).weakening (by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
      rcases hx with rfl | hx
      · exact ⟨hhead, Or.inl rfl⟩
      · tauto)
  | @orI Γ₀ χ₀ χ₁ d' ih =>
    intro hxf hcr hmem; simp only [Deriv.cr] at hcr; simp only [Deriv.o]
    have hhead : (χ₀ ⋎ χ₁) ≠ Lit := hLne _ (by simp)
    have hmem0 : Lit ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
    have P : PXFc d'.o 0 (insert χ₀ (insert χ₁ (Γ₀.erase Lit))) :=
      (ih hxf hcr (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hmem0))).weakening (by
        intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto)
    exact (PXFc.orI χ₀ χ₁ P).weakening (by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
      rcases hx with rfl | hx
      · exact ⟨hhead, Or.inl rfl⟩
      · tauto)
  | @allω Γ₀ χ' d' ih =>
    intro hxf hcr hmem; simp only [Deriv.cr] at hcr; simp only [Deriv.o]
    have hhead : (∀⁰ χ') ≠ Lit := hLne _ (by simp)
    have hmem0 : Lit ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
    have key : ∀ n, PXFc (d' n).o 0 (insert (χ'/[nm n]) (Γ₀.erase Lit)) := fun n =>
      (ih n (hxf n) (le_trans (le_iSup (fun m => (d' m).cr) n) hcr)
        (Finset.mem_insert_of_mem hmem0)).weakening (by
          intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto)
    exact (PXFc.allω χ' key).weakening (by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
      rcases hx with rfl | hx
      · exact ⟨hhead, Or.inl rfl⟩
      · tauto)
  | @exI Γ₀ χ' n d' ih =>
    intro hxf hcr hmem; simp only [Deriv.cr] at hcr; simp only [Deriv.o]
    have hhead : (∃⁰ χ') ≠ Lit := hLne _ (by simp)
    have hmem0 : Lit ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
    have P : PXFc d'.o 0 (insert (χ'/[nm n]) (Γ₀.erase Lit)) :=
      (ih hxf hcr (Finset.mem_insert_of_mem hmem0)).weakening (by
        intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto)
    exact (PXFc.exI χ' n P).weakening (by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
      rcases hx with rfl | hx
      · exact ⟨hhead, Or.inl rfl⟩
      · tauto)
  | @cut Γ₀ ξ d₁ d₂ ih₁ ih₂ =>
    intro _ hcr _; simp only [Deriv.cr] at hcr
    exact absurd ((le_max_left _ _).trans hcr) (by simp)

/-- Removing `⊥` from a cut-free `XFreeAx` derivation, bound- and `XFreeAx`-preserving (no truth
leaf is emitted — `⊥` is never an `axTrue` witness). -/
theorem PXFc.removeFalsumAux : ∀ {Δ : Seq LX} (d : Deriv Δ), XFreeAx d → d.cr ≤ (0 : ℕ∞) →
    (⊥ : Form LX) ∈ Δ → PXFc d.o 0 (Δ.erase ⊥) := by
  intro Δ d
  induction d with
  | @axL Δ k r v hp hn =>
    intro _ _ _; simp only [Deriv.o]
    exact PXFc.axL r v (Finset.mem_erase.mpr ⟨by simp, hp⟩)
      (Finset.mem_erase.mpr ⟨by simp, hn⟩)
  | @axLv Δ k r v v' hval hp hn =>
    intro _ _ _; simp only [Deriv.o]
    exact PXFc.axLv r v v' hval (Finset.mem_erase.mpr ⟨by simp, hp⟩)
      (Finset.mem_erase.mpr ⟨by simp, hn⟩)
  | @axTrue Δ k b r v htrue hmem =>
    intro hxf _ _; simp only [Deriv.o]
    exact PXFc.axTrue b r v hxf htrue (Finset.mem_erase.mpr ⟨by cases b <;> simp [signedLit], hmem⟩)
  | @verumR Δ h =>
    intro _ _ _; simp only [Deriv.o]
    exact PXFc.verumR (Finset.mem_erase.mpr ⟨by simp, h⟩)
  | @weak Δ' Δ d' hsub ih =>
    intro hxf hcr hmem; simp only [Deriv.cr] at hcr; simp only [Deriv.o]
    by_cases hd : (⊥ : Form LX) ∈ Δ'
    · exact (ih hxf hcr hd).weakening (Finset.erase_subset_erase _ hsub)
    · refine (show PXFc d'.o 0 Δ' from ⟨d', le_rfl, hcr, hxf⟩).weakening ?_
      intro x hx; exact Finset.mem_erase.mpr ⟨fun e => hd (e ▸ hx), hsub hx⟩
  | @andI Γ₀ χ₀ χ₁ d₀ d₁ ih₀ ih₁ =>
    intro hxf hcr hmem; simp only [Deriv.cr] at hcr; simp only [Deriv.o]
    have hhead : (χ₀ ⋏ χ₁) ≠ (⊥ : Form LX) := by simp [Wedge.wedge]
    have hmem0 : (⊥ : Form LX) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
    have P0 : PXFc d₀.o 0 (insert χ₀ (Γ₀.erase ⊥)) :=
      (ih₀ hxf.1 (le_trans (le_max_left _ _) hcr) (Finset.mem_insert_of_mem hmem0)).weakening (by
        intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto)
    have P1 : PXFc d₁.o 0 (insert χ₁ (Γ₀.erase ⊥)) :=
      (ih₁ hxf.2 (le_trans (le_max_right _ _) hcr) (Finset.mem_insert_of_mem hmem0)).weakening (by
        intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto)
    exact (PXFc.andI χ₀ χ₁ P0 P1).weakening (by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
      rcases hx with rfl | hx
      · exact ⟨hhead, Or.inl rfl⟩
      · tauto)
  | @orI Γ₀ χ₀ χ₁ d' ih =>
    intro hxf hcr hmem; simp only [Deriv.cr] at hcr; simp only [Deriv.o]
    have hhead : (χ₀ ⋎ χ₁) ≠ (⊥ : Form LX) := by simp [Vee.vee]
    have hmem0 : (⊥ : Form LX) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
    have P : PXFc d'.o 0 (insert χ₀ (insert χ₁ (Γ₀.erase ⊥))) :=
      (ih hxf hcr (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hmem0))).weakening (by
        intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto)
    exact (PXFc.orI χ₀ χ₁ P).weakening (by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
      rcases hx with rfl | hx
      · exact ⟨hhead, Or.inl rfl⟩
      · tauto)
  | @allω Γ₀ χ' d' ih =>
    intro hxf hcr hmem; simp only [Deriv.cr] at hcr; simp only [Deriv.o]
    have hhead : (∀⁰ χ') ≠ (⊥ : Form LX) := by simp [UnivQuantifier.all]
    have hmem0 : (⊥ : Form LX) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
    have key : ∀ n, PXFc (d' n).o 0 (insert (χ'/[nm n]) (Γ₀.erase ⊥)) := fun n =>
      (ih n (hxf n) (le_trans (le_iSup (fun m => (d' m).cr) n) hcr)
        (Finset.mem_insert_of_mem hmem0)).weakening (by
          intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto)
    exact (PXFc.allω χ' key).weakening (by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
      rcases hx with rfl | hx
      · exact ⟨hhead, Or.inl rfl⟩
      · tauto)
  | @exI Γ₀ χ' n d' ih =>
    intro hxf hcr hmem; simp only [Deriv.cr] at hcr; simp only [Deriv.o]
    have hhead : (∃⁰ χ') ≠ (⊥ : Form LX) := by simp [ExsQuantifier.exs]
    have hmem0 : (⊥ : Form LX) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
    have P : PXFc d'.o 0 (insert (χ'/[nm n]) (Γ₀.erase ⊥)) :=
      (ih hxf hcr (Finset.mem_insert_of_mem hmem0)).weakening (by
        intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto)
    exact (PXFc.exI χ' n P).weakening (by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
      rcases hx with rfl | hx
      · exact ⟨hhead, Or.inl rfl⟩
      · tauto)
  | @cut Γ₀ ξ d₁ d₂ ih₁ ih₂ =>
    intro _ hcr _; simp only [Deriv.cr] at hcr
    exact absurd ((le_max_left _ _).trans hcr) (by simp)

/-- Remove a `⊥` from a cut-free `XFreeAx` sequent. -/
theorem PXFc.removeFalsum {B : Ordinal.{0}} {Γ : Seq LX}
    (h : PXFc B 0 (insert (⊥ : Form LX) Γ)) : PXFc B 0 Γ := by
  rcases h with ⟨d, ho, hcr, hxf⟩
  refine (PXFc.removeFalsumAux d hxf hcr (Finset.mem_insert_self _ _)).weakening ?_ |>.mono ho le_rfl
  intro x hx; simp only [Finset.mem_erase, Finset.mem_insert] at hx; exact (hx.2).resolve_left hx.1

/-- **Value-congruent negative-literal renaming.** In a cut-free `XFreeAx` derivation of `Δ`
containing the negative literal `nrel r v`, replace it by a value-congruent `nrel r w`
(`|v| = |w|`), preserving height and `XFreeAx`. -/
theorem PXFc.nrel_value_subst {k} (r : (LX).Rel k) (v w : Fin k → Semiterm LX ℕ 0)
    (hvw : ∀ i, GoodsteinPA.Compat.gValm ℕ ![] (id : ℕ → ℕ) (v i)
              = GoodsteinPA.Compat.gValm ℕ ![] (id : ℕ → ℕ) (w i)) :
    ∀ {Δ : Seq LX} (d : Deriv Δ), XFreeAx d → d.cr ≤ (0 : ℕ∞) →
      (Semiformula.nrel r v) ∈ Δ →
      PXFc d.o 0 (insert (Semiformula.nrel r w) (Δ.erase (Semiformula.nrel r v))) := by
  intro Δ d
  induction d with
  | @axL Δ k' r' v' hp hn =>
    intro _ _ _; simp only [Deriv.o]
    by_cases h1 : (Semiformula.nrel r v : Form LX) = Semiformula.nrel r' v'
    · -- leaf's negative IS the renamed literal; pair leaf positive `rel r' v'` (= rel r v) with `nrel r w`
      have hpos : (Semiformula.rel r v : Form LX) = Semiformula.rel r' v' := by
        rw [← Semiformula.neg_nrel, h1, Semiformula.neg_nrel]
      refine PXFc.axLv r v w hvw ?_ (Finset.mem_insert_self _ _)
      refine Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨?_, hpos ▸ hp⟩)
      rw [hpos]; simp
    · refine (PXFc.axL r' v' ?_ ?_)
      · exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨by simp, hp⟩)
      · exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨fun e => h1 e.symm, hn⟩)
  | @axLv Δ k' r₀ va vb hval hp hn =>
    intro _ _ _; simp only [Deriv.o]
    by_cases h1 : (Semiformula.nrel r v : Form LX) = Semiformula.nrel r₀ vb
    · injection h1 with _ hk hr hvv
      subst hk; subst hr; subst hvv
      -- now r₀ = r, vb = v; pair leaf positive `rel r va` with `nrel r w`
      refine PXFc.axLv r va w (fun i => (hval i).trans (hvw i)) ?_ (Finset.mem_insert_self _ _)
      exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨by simp, hp⟩)
    · refine (PXFc.axLv r₀ va vb hval ?_ ?_)
      · exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨by simp, hp⟩)
      · exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨fun e => h1 e.symm, hn⟩)
  | @axTrue Δ k' b r' v' htrue hmem =>
    intro hxf _ _; simp only [Deriv.o]
    by_cases h1 : (signedLit b r' v' : Form LX) = Semiformula.nrel r v
    · -- the true literal IS the renamed atom (X-free, false-signed); re-emit on `nrel r w`
      have hb : b = false := by cases b <;> simp_all [signedLit]
      subst hb
      have hrr : (Semiformula.nrel r' v' : Form LX) = Semiformula.nrel r v := by
        simpa [signedLit] using h1
      have hxr : Sum.isLeft r = true :=
        xfree_transport false r' v' hxf false r v (by simpa [signedLit] using hrr)
      have htn : LitTrue (Semiformula.nrel r w) := by
        rw [← Semiformula.neg_rel, litTrue_neg]
        rw [← litTrue_rel_congr r v w hvw]
        rw [← litTrue_neg, Semiformula.neg_rel]
        exact hrr ▸ (by simpa [signedLit] using htrue)
      exact PXFc.axTrue false r w hxr htn (Finset.mem_insert_self _ _)
    · exact PXFc.axTrue b r' v' hxf htrue
        (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨h1, hmem⟩))
  | @verumR Δ h =>
    intro _ _ _; simp only [Deriv.o]
    exact PXFc.verumR (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨by simp, h⟩))
  | @weak Δ' Δ d' hsub ih =>
    intro hxf hcr hmem; simp only [Deriv.cr] at hcr; simp only [Deriv.o]
    by_cases hd : (Semiformula.nrel r v : Form LX) ∈ Δ'
    · refine (ih hxf hcr hd).weakening ?_
      intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
      rcases hx with rfl | ⟨hne, hxs⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨hne, hsub hxs⟩
    · refine (show PXFc d'.o 0 Δ' from ⟨d', le_rfl, hcr, hxf⟩).weakening ?_
      intro x hx
      refine Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨fun e => hd (e ▸ hx), hsub hx⟩)
  | @andI Γ₀ χ₀ χ₁ d₀ d₁ ih₀ ih₁ =>
    intro hxf hcr hmem; simp only [Deriv.cr] at hcr; simp only [Deriv.o]
    have hhead : (χ₀ ⋏ χ₁) ≠ (Semiformula.nrel r v : Form LX) := Semiformula.ne_of_ne_complexity (by simp)
    have hmem0 : (Semiformula.nrel r v : Form LX) ∈ Γ₀ :=
      (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
    have P0 : PXFc d₀.o 0 (insert χ₀ (insert (Semiformula.nrel r w) (Γ₀.erase (Semiformula.nrel r v)))) :=
      (ih₀ hxf.1 (le_trans (le_max_left _ _) hcr) (Finset.mem_insert_of_mem hmem0)).weakening (by
        intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto)
    have P1 : PXFc d₁.o 0 (insert χ₁ (insert (Semiformula.nrel r w) (Γ₀.erase (Semiformula.nrel r v)))) :=
      (ih₁ hxf.2 (le_trans (le_max_right _ _) hcr) (Finset.mem_insert_of_mem hmem0)).weakening (by
        intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto)
    exact (PXFc.andI χ₀ χ₁ P0 P1).weakening (by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
      rcases hx with rfl | rfl | ⟨hne, hxs⟩
      · exact Or.inr ⟨fun e => hhead e, Or.inl rfl⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨hne, Or.inr hxs⟩)
  | @orI Γ₀ χ₀ χ₁ d' ih =>
    intro hxf hcr hmem; simp only [Deriv.cr] at hcr; simp only [Deriv.o]
    have hhead : (χ₀ ⋎ χ₁) ≠ (Semiformula.nrel r v : Form LX) := Semiformula.ne_of_ne_complexity (by simp)
    have hmem0 : (Semiformula.nrel r v : Form LX) ∈ Γ₀ :=
      (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
    have P : PXFc d'.o 0 (insert χ₀ (insert χ₁ (insert (Semiformula.nrel r w) (Γ₀.erase (Semiformula.nrel r v))))) :=
      (ih hxf hcr (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hmem0))).weakening (by
        intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto)
    exact (PXFc.orI χ₀ χ₁ P).weakening (by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
      rcases hx with rfl | rfl | ⟨hne, hxs⟩
      · exact Or.inr ⟨fun e => hhead e, Or.inl rfl⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨hne, Or.inr hxs⟩)
  | @allω Γ₀ χ' d' ih =>
    intro hxf hcr hmem; simp only [Deriv.cr] at hcr; simp only [Deriv.o]
    have hhead : (∀⁰ χ') ≠ (Semiformula.nrel r v : Form LX) := Semiformula.ne_of_ne_complexity (by simp)
    have hmem0 : (Semiformula.nrel r v : Form LX) ∈ Γ₀ :=
      (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
    have key : ∀ n, PXFc (d' n).o 0 (insert (χ'/[nm n]) (insert (Semiformula.nrel r w) (Γ₀.erase (Semiformula.nrel r v)))) := fun n =>
      (ih n (hxf n) (le_trans (le_iSup (fun m => (d' m).cr) n) hcr)
        (Finset.mem_insert_of_mem hmem0)).weakening (by
          intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto)
    exact (PXFc.allω χ' key).weakening (by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
      rcases hx with rfl | rfl | ⟨hne, hxs⟩
      · exact Or.inr ⟨fun e => hhead e, Or.inl rfl⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨hne, Or.inr hxs⟩)
  | @exI Γ₀ χ' n d' ih =>
    intro hxf hcr hmem; simp only [Deriv.cr] at hcr; simp only [Deriv.o]
    have hhead : (∃⁰ χ') ≠ (Semiformula.nrel r v : Form LX) := Semiformula.ne_of_ne_complexity (by simp)
    have hmem0 : (Semiformula.nrel r v : Form LX) ∈ Γ₀ :=
      (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
    have P : PXFc d'.o 0 (insert (χ'/[nm n]) (insert (Semiformula.nrel r w) (Γ₀.erase (Semiformula.nrel r v)))) :=
      (ih hxf hcr (Finset.mem_insert_of_mem hmem0)).weakening (by
        intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto)
    exact (PXFc.exI χ' n P).weakening (by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
      rcases hx with rfl | rfl | ⟨hne, hxs⟩
      · exact Or.inr ⟨fun e => hhead e, Or.inl rfl⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨hne, Or.inr hxs⟩)
  | @cut Γ₀ ξ d₁ d₂ ih₁ ih₂ =>
    intro _ hcr _; simp only [Deriv.cr] at hcr
    exact absurd ((le_max_left _ _).trans hcr) (by simp)

/-- Induction core of atomic cut (Towsner Thm 19.2): cut a `rel r v` derivation `d` against a fixed
`nrel r v` derivation `hNC`, `XFreeAx`-preserving. The truth-layer (`removeFalseLit`) branch fires
only on an `axTrue` leaf equal to the cut atom; `XFreeAx` of that leaf forces the cut atom X-free
(`xfree_transport`), so `removeFalseLit`'s X-free side condition is met (and at an X-atom cut the
branch is vacuous). -/
theorem PXFc.atomCutAux {k} (r : (LX).Rel k) (v) {B : Ordinal.{0}} {Γ : Seq LX}
    (hNC : PXFc B 0 (insert (Semiformula.nrel r v) Γ)) :
    ∀ {Δ : Seq LX} (d : Deriv Δ), XFreeAx d → d.cr ≤ (0 : ℕ∞) → (Semiformula.rel r v) ∈ Δ →
      PXFc (B + d.o + 1) 0 (Δ.erase (Semiformula.rel r v) ∪ Γ) := by
  intro Δ d
  induction d with
  | @axL Δ k' r' v' hp hn =>
    intro _ _ _
    simp only [Deriv.o]
    have hnn : (Semiformula.nrel r' v' : Form LX) ∈ Δ.erase (Semiformula.rel r v) :=
      Finset.mem_erase.mpr ⟨by intro h; exact absurd h (by simp), hn⟩
    by_cases hrel : (Semiformula.rel r' v' : Form LX) = Semiformula.rel r v
    · have hnrv : (Semiformula.nrel r' v' : Form LX) = Semiformula.nrel r v := by
        rw [← Semiformula.neg_rel r' v', hrel, Semiformula.neg_rel]
      refine (hNC.weakening ?_).mono ?_ le_rfl
      · intro x hx
        simp only [Finset.mem_insert] at hx
        rcases hx with rfl | hxΓ
        · exact Finset.mem_union_left _ (hnrv ▸ hnn)
        · exact Finset.mem_union_right _ hxΓ
      · exact le_trans le_self_add (le_of_lt (lt_add_of_pos_right _ one_pos))
    · have hpp : (Semiformula.rel r' v' : Form LX) ∈ Δ.erase (Semiformula.rel r v) :=
        Finset.mem_erase.mpr ⟨hrel, hp⟩
      exact (PXFc.axL r' v' (Finset.mem_union_left _ hpp)
        (Finset.mem_union_left _ hnn)).mono zero_le le_rfl
  | @axLv Δ k' r₀ va vb hval hp hn =>
    intro _ _ _
    simp only [Deriv.o]
    have hnn : (Semiformula.nrel r₀ vb : Form LX) ∈ Δ.erase (Semiformula.rel r v) :=
      Finset.mem_erase.mpr ⟨by intro h; exact absurd h (by simp), hn⟩
    by_cases hrel : (Semiformula.rel r₀ va : Form LX) = Semiformula.rel r v
    · -- The value-congruent pair's positive member IS the cut atom (`r₀ = r`, `va = v`, `|vb| = |v|`).
      -- The leaf's value-congruent negative `nrel r vb` survives the erase (`hnn`); transport
      -- `hNC : ⊢ nrel r v, Γ` along the value congruence `|v| = |vb|` (`nrel_value_subst`), giving
      -- `⊢ nrel r vb, Γ`, which combines with `hnn`. No `axTrue` on an X-atom is emitted.
      injection hrel with _ hk hr hva
      subst hk
      have hr' : r = r₀ := (eq_of_heq hr).symm
      have hva' : v = va := (eq_of_heq hva).symm
      subst hr'; subst hva'
      rcases hNC with ⟨dN, hoN, hcrN, hxfN⟩
      have hrm := PXFc.nrel_value_subst r v vb hval dN hxfN hcrN
        (show (Semiformula.nrel r v : Form LX) ∈ insert (Semiformula.nrel r v) Γ by simp)
      refine (hrm.weakening ?_).mono ?_ le_rfl
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_erase] at hx
        rcases hx with rfl | ⟨hne, hx2⟩
        · exact Finset.mem_union_left _ hnn
        · rcases hx2 with rfl | hxΓ
          · exact absurd rfl hne
          · exact Finset.mem_union_right _ hxΓ
      · exact le_trans hoN (le_trans le_self_add (le_of_lt (lt_add_of_pos_right _ one_pos)))
    · have hpp : (Semiformula.rel r₀ va : Form LX) ∈ Δ.erase (Semiformula.rel r v) :=
        Finset.mem_erase.mpr ⟨hrel, hp⟩
      exact (PXFc.axLv r₀ va vb hval (Finset.mem_union_left _ hpp)
        (Finset.mem_union_left _ hnn)).mono zero_le le_rfl
  | @axTrue Δ k' b' r' v' htrue' hmem' =>
    intro hxf _ _
    simp only [Deriv.o]
    by_cases heq : (signedLit b' r' v' : Form LX) = Semiformula.rel r v
    · have htrue_rel : LitTrue (Semiformula.rel r v) := heq ▸ htrue'
      have hfalse : ¬ LitTrue (signedLit false r v) := by
        rw [← litTrue_flip false r v]; simpa [signedLit] using htrue_rel
      have hxr : Sum.isLeft r = true := xfree_transport b' r' v' hxf true r v heq
      rcases hNC with ⟨dN, hoN, hcrN, hxfN⟩
      have hrm := PXFc.removeFalseLitAux false r v hxr hfalse dN hxfN hcrN
        (show signedLit false r v ∈ insert (Semiformula.nrel r v) Γ by simp [signedLit])
      refine (hrm.weakening ?_).mono ?_ le_rfl
      · intro x hx
        have hxΓ : x ∈ Γ := by
          have h1 := Finset.mem_of_mem_erase hx
          have h2 := Finset.ne_of_mem_erase hx
          rcases Finset.mem_insert.mp h1 with rfl | h3
          · exact absurd (show (Semiformula.nrel r v : Form LX) = signedLit false r v by simp [signedLit]) h2
          · exact h3
        exact Finset.mem_union_right _ hxΓ
      · exact le_trans hoN (le_trans le_self_add (le_of_lt (lt_add_of_pos_right _ one_pos)))
    · have hll : (signedLit b' r' v' : Form LX) ∈ Δ.erase (Semiformula.rel r v) :=
        Finset.mem_erase.mpr ⟨heq, hmem'⟩
      exact (PXFc.axTrue b' r' v' hxf htrue' (Finset.mem_union_left _ hll)).mono zero_le le_rfl
  | @verumR Δ h =>
    intro _ _ _
    simp only [Deriv.o]
    have ht : (⊤ : Form LX) ∈ Δ.erase (Semiformula.rel r v) :=
      Finset.mem_erase.mpr ⟨by simp, h⟩
    exact (PXFc.verumR (Finset.mem_union_left _ ht)).mono zero_le le_rfl
  | @weak Δ' Δ d' hsub ih =>
    intro hxf hcr hmem
    simp only [Deriv.cr] at hcr
    simp only [Deriv.o]
    by_cases hd : (Semiformula.rel r v) ∈ Δ'
    · exact (ih hxf hcr hd).weakening (by
        intro x hx; simp only [Finset.mem_union, Finset.mem_erase] at hx ⊢
        rcases hx with ⟨hne, hxΔ'⟩ | hxΓ
        · exact Or.inl ⟨hne, hsub hxΔ'⟩
        · exact Or.inr hxΓ)
    · refine (show PXFc d'.o 0 Δ' from ⟨d', le_rfl, hcr, hxf⟩).weakening ?_ |>.mono ?_ le_rfl
      · intro x hx
        exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨fun e => hd (e ▸ hx), hsub hx⟩)
      · exact le_trans (CanonicallyOrderedAdd.le_add_self d'.o B)
          (le_of_lt (lt_add_of_pos_right _ one_pos))
  | @andI Γ₀ χ₀ χ₁ d₀ d₁ ih₀ ih₁ =>
    intro hxf hcr hmem
    simp only [Deriv.cr] at hcr
    simp only [Deriv.o]
    have hhead : (χ₀ ⋏ χ₁) ≠ (Semiformula.rel r v) := by intro h; simp [Wedge.wedge] at h
    have hmem0 : (Semiformula.rel r v) ∈ Γ₀ :=
      (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
    have hcr0 : d₀.cr ≤ (0 : ℕ∞) := le_trans (le_max_left _ _) hcr
    have hcr1 : d₁.cr ≤ (0 : ℕ∞) := le_trans (le_max_right _ _) hcr
    have P0 : PXFc (B + d₀.o + 1) 0 (insert χ₀ (Γ₀.erase (Semiformula.rel r v) ∪ Γ)) :=
      (ih₀ hxf.1 hcr0 (Finset.mem_insert_of_mem hmem0)).weakening (cb_frame_in χ₀ _ Γ₀ Γ)
    have P1 : PXFc (B + d₁.o + 1) 0 (insert χ₁ (Γ₀.erase (Semiformula.rel r v) ∪ Γ)) :=
      (ih₁ hxf.2 hcr1 (Finset.mem_insert_of_mem hmem0)).weakening (cb_frame_in χ₁ _ Γ₀ Γ)
    exact ((PXFc.andI χ₀ χ₁ P0 P1).weakening (cb_frame_out hhead Γ₀ Γ)).mono
      (cb_bnd B d₀.o d₁.o) le_rfl
  | @orI Γ₀ χ₀ χ₁ d' ih =>
    intro hxf hcr hmem
    simp only [Deriv.cr] at hcr
    simp only [Deriv.o]
    have hhead : (χ₀ ⋎ χ₁) ≠ (Semiformula.rel r v) := by intro h; simp [Vee.vee] at h
    have hmem0 : (Semiformula.rel r v) ∈ Γ₀ :=
      (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
    have P : PXFc (B + d'.o + 1) 0 (insert χ₀ (insert χ₁ (Γ₀.erase (Semiformula.rel r v) ∪ Γ))) :=
      (ih hxf hcr (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hmem0))).weakening (by
        intro x hx; simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢; tauto)
    exact ((PXFc.orI χ₀ χ₁ P).weakening (cb_frame_out hhead Γ₀ Γ)).mono (cb_bnd1 B d'.o) le_rfl
  | @allω Γ₀ χ' d' ih =>
    intro hxf hcr hmem
    simp only [Deriv.cr] at hcr
    simp only [Deriv.o]
    have hhead : (∀⁰ χ') ≠ (Semiformula.rel r v) := by intro h; simp [UnivQuantifier.all] at h
    have hmem0 : (Semiformula.rel r v) ∈ Γ₀ :=
      (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
    have key : ∀ n, PXFc (B + (d' n).o + 1) 0
        (insert (χ'/[nm n]) (Γ₀.erase (Semiformula.rel r v) ∪ Γ)) := fun n =>
      (ih n (hxf n) (le_trans (le_iSup (fun m => (d' m).cr) n) hcr)
        (Finset.mem_insert_of_mem hmem0)).weakening (cb_frame_in (χ'/[nm n]) _ Γ₀ Γ)
    exact ((PXFc.allω χ' key).weakening (cb_frame_out hhead Γ₀ Γ)).mono
      (cb_bnd_sup B (fun n => (d' n).o)) le_rfl
  | @exI Γ₀ χ' n d' ih =>
    intro hxf hcr hmem
    simp only [Deriv.cr] at hcr
    simp only [Deriv.o]
    have hhead : (∃⁰ χ') ≠ (Semiformula.rel r v) := by intro h; simp [ExsQuantifier.exs] at h
    have hmem0 : (Semiformula.rel r v) ∈ Γ₀ :=
      (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
    have P : PXFc (B + d'.o + 1) 0 (insert (χ'/[nm n]) (Γ₀.erase (Semiformula.rel r v) ∪ Γ)) :=
      (ih hxf hcr (Finset.mem_insert_of_mem hmem0)).weakening (cb_frame_in (χ'/[nm n]) _ Γ₀ Γ)
    exact ((PXFc.exI χ' n P).weakening (cb_frame_out hhead Γ₀ Γ)).mono (cb_bnd1 B d'.o) le_rfl
  | @cut Γ₀ ξ d₁ d₂ ih₁ ih₂ =>
    intro _ hcr _
    simp only [Deriv.cr] at hcr
    exact absurd ((le_max_left _ _).trans hcr) (by simp)

/-- **Atomic cut elimination** (Towsner Thm 19.2), `XFreeAx`-preserving. -/
theorem PXFc.atomCut {k} (r : (LX).Rel k) (v) {A B : Ordinal.{0}} {Γ : Seq LX}
    (hC : PXFc A 0 (insert (Semiformula.rel r v) Γ))
    (hNC : PXFc B 0 (insert (Semiformula.nrel r v) Γ)) :
    PXFc (B + A + 1) 0 Γ := by
  rcases hC with ⟨d, ho, hcr, hxf⟩
  refine ((PXFc.atomCutAux r v hNC d hxf hcr (Finset.mem_insert_self _ _)).weakening
    (show (insert (Semiformula.rel r v) Γ).erase (Semiformula.rel r v) ∪ Γ ⊆ Γ from by
      intro x hx; simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢;
      tauto)).mono ?_ le_rfl
  exact add_le_add_left ((add_le_add_iff_left B).mpr ho) 1

/-! ### Cut-rank elimination (§19.7/19.9) over `PXFc` — ordinal bookkeeping + assembly. -/

private theorem cb_one_lt_opow_succ (c : Ordinal.{0}) : (1 : Ordinal) < Ordinal.omega0 ^ (c + 1) := by
  calc (1 : Ordinal) < Ordinal.omega0 := Ordinal.one_lt_omega0
    _ = Ordinal.omega0 ^ (1 : Ordinal) := (Ordinal.opow_one _).symm
    _ ≤ Ordinal.omega0 ^ (c + 1) :=
        Ordinal.opow_le_opow_right Ordinal.omega0_pos (CanonicallyOrderedAdd.le_add_self 1 c)

private theorem cb_opow_lt_opow_succ_of_le_max {a b x : Ordinal.{0}}
    (hx : x ≤ max (Ordinal.omega0 ^ a) (Ordinal.omega0 ^ b)) :
    x < Ordinal.omega0 ^ (max a b + 1) := by
  refine lt_of_le_of_lt hx (max_lt ?_ ?_)
  · exact (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mpr
      (lt_of_le_of_lt (le_max_left a b) (lt_add_of_pos_right _ one_pos))
  · exact (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mpr
      (lt_of_le_of_lt (le_max_right a b) (lt_add_of_pos_right _ one_pos))

private theorem cb_max_opow_add_one_le (a b : Ordinal.{0}) :
    max (Ordinal.omega0 ^ a) (Ordinal.omega0 ^ b) + 1 ≤ Ordinal.omega0 ^ (max a b + 1) :=
  le_of_lt (Ordinal.isPrincipal_add_omega0_opow _ (cb_opow_lt_opow_succ_of_le_max le_rfl)
    (cb_one_lt_opow_succ _))

private theorem cb_max_opow_add_two_le (a b : Ordinal.{0}) :
    max (Ordinal.omega0 ^ a) (Ordinal.omega0 ^ b) + 1 + 1 ≤ Ordinal.omega0 ^ (max a b + 1) := by
  have hP := Ordinal.isPrincipal_add_omega0_opow (max a b + 1)
  exact le_of_lt (hP (hP (cb_opow_lt_opow_succ_of_le_max le_rfl) (cb_one_lt_opow_succ _))
    (cb_one_lt_opow_succ _))

private theorem cb_opow_add_opow_add_one_le (a b : Ordinal.{0}) :
    Ordinal.omega0 ^ a + Ordinal.omega0 ^ b + 1 ≤ Ordinal.omega0 ^ (max a b + 1) := by
  have hP := Ordinal.isPrincipal_add_omega0_opow (max a b + 1)
  exact le_of_lt (hP (hP (cb_opow_lt_opow_succ_of_le_max (le_max_left _ _))
    (cb_opow_lt_opow_succ_of_le_max (le_max_right _ _))) (cb_one_lt_opow_succ _))

private theorem cb_opow_add_one_le' (a : Ordinal.{0}) :
    Ordinal.omega0 ^ a + 1 ≤ Ordinal.omega0 ^ (a + 1) := by
  have hP := Ordinal.isPrincipal_add_omega0_opow (a + 1)
  exact le_of_lt (hP ((Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mpr
    (lt_add_of_pos_right _ one_pos)) (cb_one_lt_opow_succ _))

private theorem cb_sup_opow_add_one_le (f : ℕ → Ordinal.{0}) :
    (⨆ n, Ordinal.omega0 ^ (f n)) + 1 ≤ Ordinal.omega0 ^ ((⨆ n, f n) + 1) := by
  have hsup : (⨆ n, Ordinal.omega0 ^ (f n)) ≤ Ordinal.omega0 ^ (⨆ n, f n) :=
    Ordinal.iSup_le fun n => Ordinal.opow_le_opow_right Ordinal.omega0_pos (Ordinal.le_iSup f n)
  have hlt : Ordinal.omega0 ^ (⨆ n, f n) < Ordinal.omega0 ^ ((⨆ n, f n) + 1) :=
    (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mpr (lt_add_of_pos_right _ one_pos)
  exact le_of_lt (Ordinal.isPrincipal_add_omega0_opow _ (lt_of_le_of_lt hsup hlt)
    (cb_one_lt_opow_succ _))

/-- **Principal cut on a rank-`c` formula** (Towsner Thm 19.7 core), `XFreeAx`-preserving. -/
theorem PXFc.cutElimPrincipal {c : ℕ} {ξ : Form LX} {A B : Ordinal.{0}} {Γ : Seq LX}
    (hξeq : ξ.complexity = c)
    (hC : PXFc (Ordinal.omega0 ^ A) c (insert ξ Γ))
    (hNC : PXFc (Ordinal.omega0 ^ B) c (insert (∼ξ) Γ)) :
    PXFc (Ordinal.omega0 ^ (max A B + 1)) c Γ := by
  cases ξ with
  | verum =>
      have hc0 : c = 0 := hξeq.symm
      subst hc0
      have hNC' : PXFc (Ordinal.omega0 ^ B) 0 (insert (⊥ : Form LX) Γ) := hNC
      refine (PXFc.removeFalsum hNC').mono ?_ le_rfl
      exact Ordinal.opow_le_opow_right Ordinal.omega0_pos
        (le_trans (le_max_right A B) (le_of_lt (lt_add_of_pos_right _ one_pos)))
  | falsum =>
      have hc0 : c = 0 := hξeq.symm
      subst hc0
      refine (PXFc.removeFalsum hC).mono ?_ le_rfl
      exact Ordinal.opow_le_opow_right Ordinal.omega0_pos
        (le_trans (le_max_left A B) (le_of_lt (lt_add_of_pos_right _ one_pos)))
  | rel r v =>
      have hc0 : c = 0 := hξeq.symm
      subst hc0
      refine (PXFc.atomCut r v hC hNC).mono ?_ le_rfl
      rw [max_comm A B]; exact cb_opow_add_opow_add_one_le B A
  | nrel r v =>
      have hc0 : c = 0 := hξeq.symm
      subst hc0
      have hNC' : PXFc (Ordinal.omega0 ^ B) 0 (insert (Semiformula.rel r v) Γ) := hNC
      exact (PXFc.atomCut r v hNC' hC).mono (cb_opow_add_opow_add_one_le A B) le_rfl
  | and a b =>
      have hM : max a.complexity b.complexity + 1 = c := hξeq
      have han : a.complexity + 1 ≤ c := by have := le_max_left a.complexity b.complexity; omega
      have hbn : b.complexity + 1 ≤ c := by have := le_max_right a.complexity b.complexity; omega
      exact (PXFc.cutReduceConj (by exact_mod_cast han) (by exact_mod_cast hbn) hC hNC).mono
        (cb_max_opow_add_two_le A B) le_rfl
  | or a b =>
      have hM : max a.complexity b.complexity + 1 = c := hξeq
      have han : a.complexity + 1 ≤ c := by have := le_max_left a.complexity b.complexity; omega
      have hbn : b.complexity + 1 ≤ c := by have := le_max_right a.complexity b.complexity; omega
      exact (PXFc.cutReduceDisj (by exact_mod_cast han) (by exact_mod_cast hbn) hC hNC).mono
        (cb_max_opow_add_two_le A B) le_rfl
  | all φ' =>
      have hφn : φ'.complexity + 1 ≤ c := le_of_eq hξeq
      exact (PXFc.cutReduceAll (by exact_mod_cast hφn) hC hNC).mono
        (cb_opow_add_opow_add_one_le A B) le_rfl
  | exs φ' =>
      have hφn : (∼φ').complexity + 1 ≤ c := by
        rw [Semiformula.complexity_neg]; exact le_of_eq hξeq
      have hC' : PXFc (Ordinal.omega0 ^ A) c (insert (∃⁰ ∼(∼φ')) Γ) := by
        rw [DeMorgan.neg]; exact hC
      refine ((PXFc.cutReduceAll (by exact_mod_cast hφn) hNC hC').mono ?_ le_rfl)
      rw [max_comm A B]; exact cb_opow_add_opow_add_one_le B A

/-- One level of cut-rank reduction (Towsner Thm 19.7), `XFreeAx`-preserving. -/
theorem PXFc.cutElimStepAux {c : ℕ} : ∀ {Γ : Seq LX} (d : Deriv Γ), XFreeAx d →
    d.cr ≤ ((c + 1 : ℕ) : ℕ∞) → PXFc (Ordinal.omega0 ^ (d.o)) c Γ := by
  intro Γ d
  induction d with
  | @axL Γ k r v hp hn =>
    intro _ _; simp only [Deriv.o]
    exact (PXFc.axL r v hp hn).mono zero_le (Nat.zero_le c)
  | @axLv Γ k r v v' hval hp hn =>
    intro _ _; simp only [Deriv.o]
    exact (PXFc.axLv r v v' hval hp hn).mono zero_le (Nat.zero_le c)
  | @axTrue Γ k b r v htrue hmem =>
    intro hxf _; simp only [Deriv.o]
    exact (PXFc.axTrue b r v hxf htrue hmem).mono zero_le (Nat.zero_le c)
  | @verumR Γ h =>
    intro _ _; simp only [Deriv.o]
    exact (PXFc.verumR h).mono zero_le (Nat.zero_le c)
  | @weak Δ Γ d' hsub ih =>
    intro hxf hcr; simp only [Deriv.cr] at hcr; simp only [Deriv.o]
    exact (ih hxf hcr).weakening hsub
  | @andI Γ₀ χ₀ χ₁ d₀ d₁ ih₀ ih₁ =>
    intro hxf hcr; simp only [Deriv.cr] at hcr; simp only [Deriv.o]
    exact (PXFc.andI χ₀ χ₁ (ih₀ hxf.1 ((le_max_left _ _).trans hcr))
      (ih₁ hxf.2 ((le_max_right _ _).trans hcr))).mono (cb_max_opow_add_one_le d₀.o d₁.o) le_rfl
  | @orI Γ₀ χ₀ χ₁ d' ih =>
    intro hxf hcr; simp only [Deriv.cr] at hcr; simp only [Deriv.o]
    exact (PXFc.orI χ₀ χ₁ (ih hxf hcr)).mono (cb_opow_add_one_le' d'.o) le_rfl
  | @allω Γ₀ χ' d' ih =>
    intro hxf hcr; simp only [Deriv.cr] at hcr; simp only [Deriv.o]
    have IH : ∀ n, PXFc (Ordinal.omega0 ^ ((d' n).o)) c (insert (χ'/[nm n]) Γ₀) :=
      fun n => ih n (hxf n) ((le_iSup (fun m => (d' m).cr) n).trans hcr)
    exact (PXFc.allω χ' IH).mono (cb_sup_opow_add_one_le (fun n => (d' n).o)) le_rfl
  | @exI Γ₀ χ' n d' ih =>
    intro hxf hcr; simp only [Deriv.cr] at hcr; simp only [Deriv.o]
    exact (PXFc.exI χ' n (ih hxf hcr)).mono (cb_opow_add_one_le' d'.o) le_rfl
  | @cut Γ₀ ξ d₁ d₂ ih₁ ih₂ =>
    intro hxf hcr; simp only [Deriv.cr] at hcr
    have hcr1 : d₁.cr ≤ ((c + 1 : ℕ) : ℕ∞) :=
      (le_max_left d₁.cr d₂.cr).trans ((le_max_right _ _).trans hcr)
    have hcr2 : d₂.cr ≤ ((c + 1 : ℕ) : ℕ∞) :=
      (le_max_right d₁.cr d₂.cr).trans ((le_max_right _ _).trans hcr)
    have hξc : (ξ.complexity + 1 : ℕ∞) ≤ ((c + 1 : ℕ) : ℕ∞) := (le_max_left _ _).trans hcr
    have IH1 := ih₁ hxf.1 hcr1
    have IH2 := ih₂ hxf.2 hcr2
    simp only [Deriv.o]
    by_cases hkeep : ξ.complexity < c
    · exact (PXFc.cut ξ (by exact_mod_cast Nat.succ_le_of_lt hkeep) IH1 IH2).mono
        (cb_max_opow_add_one_le d₁.o d₂.o) le_rfl
    · have hξle : ξ.complexity ≤ c := Nat.le_of_succ_le_succ (by exact_mod_cast hξc)
      have hξeq : ξ.complexity = c := le_antisymm hξle (not_lt.mp hkeep)
      exact PXFc.cutElimPrincipal hξeq IH1 IH2

/-- One level of cut elimination (Towsner Thm 19.7), `XFreeAx`-preserving. -/
theorem PXFc.cutElimStep {α : Ordinal.{0}} {c : ℕ} {Γ : Seq LX}
    (h : PXFc α (c + 1) Γ) : PXFc (Ordinal.omega0 ^ α) c Γ := by
  rcases h with ⟨d, ho, hcr, hxf⟩
  exact (PXFc.cutElimStepAux d hxf hcr).mono
    (Ordinal.opow_le_opow_right Ordinal.omega0_pos ho) le_rfl

/-- **Full cut elimination** (Towsner Thm 19.9), `XFreeAx`-preserving: iterate `cutElimStep` `c`
times to a cut-free derivation at `ω_c^α`. **This is C₁** — the input to corollary B. -/
theorem PXFc.cutElim {α : Ordinal.{0}} {c : ℕ} {Γ : Seq LX}
    (h : PXFc α c Γ) : PXFc (Deriv.omegaTower c α) 0 Γ := by
  induction c generalizing α with
  | zero => simpa [Deriv.omegaTower] using h
  | succ c ih => exact ih (PXFc.cutElimStep h)

/-! ### D (Thm 5.6 tail): cut-eliminate the embedded `{TI}` derivation and feed corollary B.

Composing **C₁** (`PXFc.cutElim`) with the lap-14 **corollary B** (`orderType_le_of_TIderiv`): any
`XFreeAx` `Z∞`-derivation of `{TI_≺(X)}` (of *any* finite cut rank `c`, height `≤ α`) bounds the order
type by `2^(ω_c^α)`. This is everything downstream of the embedding; **C₂** (`embedC` over `LX`,
producing the `PXFc` hypothesis from a `Z ⊢ TI` proof) is the one remaining gap to Thm 5.6 proper. -/
theorem orderType_le_of_TIprovable (lt : ℕ → ℕ → Prop) [IsWellFounded ℕ lt]
    (prec : Semiformula LX ℕ 2)
    (hprec : ∀ (γ : Ordinal.{0}) (n : ℕ),
      models lt γ ((Boundedness.hyp prec)/[nm n]) ↔ ∀ m : ℕ, lt m n → rk lt m < γ)
    (hprecXPos : XPos (∼ prec)) {α : Ordinal.{0}} {c : ℕ}
    (h : PXFc α c ({Boundedness.TI prec} : Seq LX)) :
    orderType lt ≤ 2 ^ (Deriv.omegaTower c α) := by
  obtain ⟨d, hdo, hdc, hdx⟩ := PXFc.toPXF (PXFc.cutElim h)
  exact Boundedness.orderType_le_of_TIderiv lt prec _ hprec hprecXPos d hdo hdc hdx

/-! ### C₂ groundwork: `Z∞` excluded middle over `LX`, `XFreeAx`-preserving.

`provable_em φ` closes `{φ, ∼φ}` cut-free using ONLY `axL`/`verumR`/`andI`/`orI`/`allω`/`exI` — **never
`axTrue`** (atoms close via the same-atom EM axiom `axL`, *including X-atoms*). So `XFreeAx` holds for
the whole derivation automatically, and the output is a `PXFc · 0`. This is the base/step engine of the
embedding's X-induction meta-induction (Buchholz Thm 5.5) — the `XFreeAx`-safe route for X-formulas. -/
theorem provable_em_x (φ : Form LX) {Γ : Seq LX} (hp : φ ∈ Γ) (hn : ∼φ ∈ Γ) :
    ∃ a, PXFc a 0 Γ := by
  have key : ∀ (k : ℕ) (φ : Form LX), φ.complexity ≤ k →
      ∀ {Γ : Seq LX}, φ ∈ Γ → ∼φ ∈ Γ → ∃ a, PXFc a 0 Γ := by
    intro k
    induction k with
    | zero =>
      intro φ hk Γ hp hn
      cases φ using Semiformula.cases' with
      | hverum => exact ⟨0, PXFc.verumR hp⟩
      | hfalsum => exact ⟨0, PXFc.verumR (by simpa using hn)⟩
      | hrel r v => exact ⟨0, PXFc.axL r v hp (by simpa using hn)⟩
      | hnrel r v => exact ⟨0, PXFc.axL r v (by simpa using hn) hp⟩
      | hand φ ψ => simp at hk
      | hor φ ψ => simp at hk
      | hall φ => simp at hk
      | hexs φ => simp at hk
    | succ k ih =>
      intro φ hk Γ hp hn
      cases φ using Semiformula.cases' with
      | hverum => exact ⟨0, PXFc.verumR hp⟩
      | hfalsum => exact ⟨0, PXFc.verumR (by simpa using hn)⟩
      | hrel r v => exact ⟨0, PXFc.axL r v hp (by simpa using hn)⟩
      | hnrel r v => exact ⟨0, PXFc.axL r v (by simpa using hn) hp⟩
      | hand φ ψ =>
        have hφk : φ.complexity ≤ k := by simp only [Semiformula.complexity_and] at hk; omega
        have hψk : ψ.complexity ≤ k := by simp only [Semiformula.complexity_and] at hk; omega
        obtain ⟨a1, h1⟩ := ih φ hφk (Γ := insert φ (insert (∼φ) (insert (∼ψ) Γ)))
          (by simp) (by simp)
        obtain ⟨a2, h2⟩ := ih ψ hψk (Γ := insert ψ (insert (∼φ) (insert (∼ψ) Γ)))
          (by simp) (by simp)
        have hand := PXFc.andI φ ψ h1 h2
        rw [Finset.insert_eq_self.mpr
          (show (φ ⋏ ψ) ∈ insert (∼φ) (insert (∼ψ) Γ) by simp [hp])] at hand
        have hor := PXFc.orI (∼φ) (∼ψ) hand
        rw [Finset.insert_eq_self.mpr (show (∼φ ⋎ ∼ψ) ∈ Γ by simpa using hn)] at hor
        exact ⟨_, hor⟩
      | hor φ ψ =>
        have hn' : (∼φ ⋏ ∼ψ) ∈ Γ := by simpa using hn
        have hφk : φ.complexity ≤ k := by simp only [Semiformula.complexity_or] at hk; omega
        have hψk : ψ.complexity ≤ k := by simp only [Semiformula.complexity_or] at hk; omega
        obtain ⟨a1, h1⟩ := ih φ hφk (Γ := insert (∼φ) (insert φ (insert ψ Γ)))
          (by simp) (by simp)
        obtain ⟨a2, h2⟩ := ih ψ hψk (Γ := insert (∼ψ) (insert φ (insert ψ Γ)))
          (by simp) (by simp)
        have hand := PXFc.andI (∼φ) (∼ψ) h1 h2
        rw [Finset.insert_eq_self.mpr
          (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hn'))] at hand
        have hor := PXFc.orI φ ψ hand
        rw [Finset.insert_eq_self.mpr (show (φ ⋎ ψ) ∈ Γ by simp [hp])] at hor
        exact ⟨_, hor⟩
      | hall ψ =>
        have hψk : ψ.complexity ≤ k := by simp only [Semiformula.complexity_all] at hk; omega
        have hex : (∃⁰ ∼ψ) ∈ Γ := by simpa using hn
        have fam : ∀ n, ∃ a, PXFc a 0 (insert (ψ/[nm n]) Γ) := by
          intro n
          have hcomp : (ψ/[nm n]).complexity ≤ k := by
            have he : (ψ/[nm n]).complexity = ψ.complexity := by simp
            rw [he]; exact hψk
          obtain ⟨a, ha⟩ := ih (ψ/[nm n]) hcomp
            (Γ := insert (∼(ψ/[nm n])) (insert (ψ/[nm n]) Γ)) (by simp) (by simp)
          have hexI := PXFc.exI (∼ψ) n (Γ := insert (ψ/[nm n]) Γ)
            (by have heq : (∼ψ)/[nm n] = ∼(ψ/[nm n]) := by simp
                rw [heq]; exact ha)
          rw [Finset.insert_eq_self.mpr (Finset.mem_insert_of_mem hex)] at hexI
          exact ⟨a + 1, hexI⟩
        choose β hβ using fam
        have hall := PXFc.allω ψ (Γ := Γ) hβ
        rw [Finset.insert_eq_self.mpr hp] at hall
        exact ⟨_, hall⟩
      | hexs ψ =>
        have hψk : ψ.complexity ≤ k := by simp only [Semiformula.complexity_exs] at hk; omega
        have hall' : (∀⁰ ∼ψ) ∈ Γ := by simpa using hn
        have fam : ∀ n, ∃ a, PXFc a 0 (insert ((∼ψ)/[nm n]) Γ) := by
          intro n
          have hcomp : (ψ/[nm n]).complexity ≤ k := by
            have he : (ψ/[nm n]).complexity = ψ.complexity := by simp
            rw [he]; exact hψk
          obtain ⟨a, ha⟩ := ih (ψ/[nm n]) hcomp
            (Γ := insert (ψ/[nm n]) (insert (∼(ψ/[nm n])) Γ)) (by simp) (by simp)
          have hexI := PXFc.exI ψ n (Γ := insert (∼(ψ/[nm n])) Γ) ha
          rw [Finset.insert_eq_self.mpr (Finset.mem_insert_of_mem hp)] at hexI
          have heq : (∼ψ)/[nm n] = ∼(ψ/[nm n]) := by simp
          rw [heq]; exact ⟨a + 1, hexI⟩
        choose β hβ using fam
        have hall := PXFc.allω (∼ψ) (Γ := Γ) hβ
        rw [Finset.insert_eq_self.mpr hall'] at hall
        exact ⟨_, hall⟩
  exact key φ.complexity φ le_rfl hp hn

/-! ### C₂ crux: the X-induction **meta-induction** (Buchholz Thm 5.5), `XFreeAx`-preserving.

The faithfulness-critical case of the embedding. The PA induction axiom for an X-formula `ψ` is NOT
derived by `provable_true` (ω-completeness) — that would `axTrue` a lone X-atom and break `XFreeAx`.
Instead, after stripping `univCl` + the two `🡒`, the sequent `{∼ψ(0), ∼∀x(ψ(x)→ψ(x+1)), ∀x ψ(x)}` is
built by a **tower of `cut`s on `ψ(i)`** (the ω-rule absorbing the metatheoretic induction), bottoming
out at `provable_em` (`XFreeAx`-safe). Stated abstractly in the instantiated families `ψ/[nm n]`, with
the step's `∃`-side `(∼step)/[nm n] = ψ(n) ⋏ ∼ψ(n+1)` as a hypothesis (the Foundation-DSL that produces
`step` from `ψ` by the successor substitution is deferred to the `embedC` port). -/
theorem metaInduction (ψ step : SyntacticSemiformula LX 1) {Γ : Seq LX}
    (hstep : ∀ n, (∼step)/[nm n] = (ψ/[nm n]) ⋏ ∼(ψ/[nm (n + 1)])) :
    ∃ a, PXFc a (ψ.complexity + 1)
      (insert (∼(ψ/[nm 0])) (insert (∃⁰ (∼step)) (insert (∀⁰ ψ) Γ))) := by
  set c : ℕ := ψ.complexity + 1 with hc
  set Δ : Seq LX := insert (∼(ψ/[nm 0])) (insert (∃⁰ (∼step)) Γ) with hΔ
  have hcut : ∀ n, ((ψ/[nm n]).complexity + 1 : ℕ∞) ≤ (c : ℕ∞) := by
    intro n; rw [hc]; simp
  have hEx : ∀ n, (∃⁰ (∼step)) ∈ (insert (∼(ψ/[nm n])) (insert (ψ/[nm (n + 1)]) Δ)) := by
    intro n; rw [hΔ]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_insert_self _ _)))
  -- the chain `∀ n, ⊢ ψ(n), Δ` by meta-induction on n
  have chain : ∀ n, ∃ a, PXFc a c (insert (ψ/[nm n]) Δ) := by
    intro n
    induction n with
    | zero =>
      obtain ⟨a, ha⟩ := provable_em_x (ψ/[nm 0]) (Γ := insert (ψ/[nm 0]) Δ)
        (Finset.mem_insert_self _ _)
        (Finset.mem_insert_of_mem (by rw [hΔ]; exact Finset.mem_insert_self _ _))
      exact ⟨a, ha.mono le_rfl (Nat.zero_le c)⟩
    | succ n ih =>
      obtain ⟨aL, hL0⟩ := ih
      -- left premise of the cut: weaken `ψ(n), Δ` to `ψ(n), ψ(n+1), Δ`
      have hL : PXFc aL c (insert (ψ/[nm n]) (insert (ψ/[nm (n + 1)]) Δ)) :=
        hL0.weakening (Finset.insert_subset_insert _ (Finset.subset_insert _ _))
      -- right premise `R = ∼ψ(n), ψ(n+1), Δ`, via exI on the step + two `em`s under `andI`
      obtain ⟨aA, hA0⟩ := provable_em_x (ψ/[nm n])
        (Γ := insert (ψ/[nm n]) (insert (∼(ψ/[nm n])) (insert (ψ/[nm (n + 1)]) Δ)))
        (Finset.mem_insert_self _ _)
        (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
      obtain ⟨aB, hB0⟩ := provable_em_x (ψ/[nm (n + 1)])
        (Γ := insert (∼(ψ/[nm (n + 1)]))
          (insert (∼(ψ/[nm n])) (insert (ψ/[nm (n + 1)]) Δ)))
        (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))
        (Finset.mem_insert_self _ _)
      have hand := PXFc.andI (c := c) (ψ/[nm n]) (∼(ψ/[nm (n + 1)]))
        (hA0.mono le_rfl (Nat.zero_le c)) (hB0.mono le_rfl (Nat.zero_le c))
      rw [← hstep n] at hand
      have hexI := PXFc.exI (∼step) n hand
      rw [Finset.insert_eq_self.mpr (hEx n)] at hexI
      -- cut `ψ(n)`: left `ψ(n),ψ(n+1),Δ` × right `∼ψ(n),ψ(n+1),Δ` ⟹ `ψ(n+1),Δ`
      exact ⟨_, PXFc.cut (ψ/[nm n]) (hcut n) hL hexI⟩
  choose β hβ using chain
  have hall := PXFc.allω (β := β) ψ (Γ := Δ) hβ
  refine ⟨_, hall.weakening ?_⟩
  rw [hΔ]; intro x hx
  simp only [Finset.mem_insert] at hx ⊢
  tauto

end GoodsteinPA.XFreeCutElim
