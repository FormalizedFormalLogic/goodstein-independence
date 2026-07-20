module

public import GoodsteinPA.OperatorZeh.Zef
public import GoodsteinPA.BlueprintAttr
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

namespace GoodsteinPA.OperatorZeh

open LO LO.FirstOrder ONote Ordinal
open GoodsteinPA.OperatorZinfty

variable {α e : ONote} {H : ONote → Prop} {m c : ℕ} {f : ℕ → ℕ} {Γ : Finset (ArithmeticFormula ℕ)}

/-! ## The inversion suite

`allInv_Zeh` is the six-case induction mirroring `Provable.allInv` (`OperatorZinfty.lean`), with the
numeric `max k n₀` bookkeeping re-keyed to the stage axis `max m n₀` and the relativization axis
`adjoin H n₀`.  Since the minimal `Zeh` core has only the six mandated constructors (no
`andI`/`orI`/`verumR`/`trueRel`/`trueNrel`), the induction is strictly shorter than `Provable`'s —
the only genuinely new bookkeeping is that inverting under an `allω`/`exI` sub-derivation
adjoins `n₀` on top of the branch relativization, which the `adjoin` reassociation lemmas below
absorb (they are the operator-side analog of `Provable`'s `max`-reshuffle
`max (max k n₀) n = max (max k n) n₀`). -/

/-! ### Finset push/pull helpers for the inversion (re-derivations of the `private`
`OperatorZinfty` copies — calculus-independent). -/

theorem inv1Push (A e b : ArithmeticFormula ℕ) (s : Finset (ArithmeticFormula ℕ)) :
    insert e ((insert b s).erase A) ⊆ insert b (insert e (s.erase A)) := by
  intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto

theorem inv1Pull (A e : ArithmeticFormula ℕ) {b : ArithmeticFormula ℕ} (h : b ≠ A) (s : Finset (ArithmeticFormula ℕ)) :
    insert b (insert e (s.erase A)) ⊆ insert e ((insert b s).erase A) := by
  intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
  rcases hx with rfl | rfl | hx
  · exact Or.inr ⟨h, Or.inl rfl⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨hx.1, Or.inr hx.2⟩

theorem princAllSub (A e : ArithmeticFormula ℕ) (s : Finset (ArithmeticFormula ℕ)) :
    insert e ((insert e s).erase A) ⊆ insert e (s.erase A) := by
  intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto

/-- **∀-inversion, `Zeh` form.**  The extracted instance runs at the relativization
`adjoin H n₀` and the raised stage `max m n₀`.

- [Tow20, Theorem 19.4]
-/
theorem allInv_Zeh {φ₀ : ArithmeticSemiformula ℕ 1} (n₀ : ℕ)
    (dd : Zeh α e H m c Γ) (hmem : (∀⁰ φ₀) ∈ Γ) :
    Zeh α e (adjoin H n₀) (max m n₀) c (insert (φ₀/[nm n₀]) (Γ.erase (∀⁰ φ₀))) := by
  induction dd with
  | @axL α e H m c Γ ar r v hp hn =>
      refine Zeh.axL r v ?_ ?_ <;>
        exact Finset.mem_insert_of_mem
          (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), by assumption⟩)
  | @wk α e H m c Δ Γ hsub dd ih =>
      by_cases hh : (∀⁰ φ₀) ∈ Δ
      · exact Zeh.wk (Finset.insert_subset_insert _ (Finset.erase_subset_erase _ hsub)) (ih hh)
      · refine Zeh.wk ?_ (Zeh.mono_H dd (adjoin_le H n₀) (le_max_left m n₀))
        intro x hx
        exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨fun e => hh (e ▸ hx), hsub hx⟩)
  | @weak α β e H m c Δ Γ hβ hβNF hαNF hβH hsub dd ih =>
      by_cases hh : (∀⁰ φ₀) ∈ Δ
      · exact Zeh.weak hβ hβNF hαNF (Cl_mono (adjoin_le H n₀) hβH)
          (Finset.insert_subset_insert _ (Finset.erase_subset_erase _ hsub)) (ih hh)
      · refine Zeh.weak hβ hβNF hαNF (Cl_mono (adjoin_le H n₀) hβH) ?_
          (Zeh.mono_H dd (adjoin_le H n₀) (le_max_left m n₀))
        intro x hx
        exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨fun e => hh (e ▸ hx), hsub hx⟩)
  | @allω α e H m c Γ₀ χ β hβ hβNF hαNF hβH dd ih =>
      by_cases hhd : (∀⁰ χ) = (∀⁰ φ₀)
      · -- PRINCIPAL: specialize branch n₀ (already at `adjoin H n₀`, `max m n₀`)
        obtain rfl := (Semiformula.all_inj _ _).mp hhd
        rw [Finset.erase_insert_eq_erase]
        by_cases hh : (∀⁰ χ) ∈ Γ₀
        · -- the tail still carries a ∀⁰χ: invert it out of branch n₀ recursively
          have h := ih n₀ (Finset.mem_insert_of_mem hh)
          have h2 : Zeh (β n₀) e (adjoin H n₀) (max m n₀) c
              (insert (χ/[nm n₀]) ((insert (χ/[nm n₀]) Γ₀).erase (∀⁰ χ))) :=
            Zeh.mono_H h (adjoin_idem H n₀) (le_of_eq (by omega))
          exact Zeh.weak (hβ n₀) (hβNF n₀) hαNF (hβH n₀) (princAllSub (∀⁰ χ) _ Γ₀) h2
        · rw [Finset.erase_eq_of_notMem hh]
          exact Zeh.weak (hβ n₀) (hβNF n₀) hαNF (hβH n₀) (Finset.Subset.refl _) (dd n₀)
      · -- NON-PRINCIPAL: rebuild the `allω`, adjoining `n₀` on top of each branch relativization
        have hmem0 : (∀⁰ φ₀) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhd e.symm
        have key : ∀ n, Zeh (β n) e (adjoin (adjoin H n₀) n) (max (max m n₀) n) c
            (insert (χ/[nm n]) (insert (φ₀/[nm n₀]) (Γ₀.erase (∀⁰ φ₀)))) := by
          intro n
          have h := ih n (Finset.mem_insert_of_mem hmem0)
          exact Zeh.wk (inv1Push (∀⁰ φ₀) _ (χ/[nm n]) Γ₀)
            (Zeh.mono_H h (adjoin_swap H n n₀) (le_of_eq (by omega)))
        exact Zeh.wk (inv1Pull (∀⁰ φ₀) _ hhd Γ₀)
          (Zeh.allω χ β hβ hβNF hαNF
            (fun n => Cl_mono (adjoin_base_mono n (adjoin_le H n₀)) (hβH n)) key)
  | @exI α β e H m c Γ₀ χ n hβ hβNF hαNF hβH hbound dd ih =>
      have hhead : (∃⁰ χ) ≠ (∀⁰ φ₀) := by intro h; simp [ExsQuantifier.exs, UnivQuantifier.all] at h
      have hmem0 : (∀⁰ φ₀) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
      have P := Zeh.wk (inv1Push (∀⁰ φ₀) _ (χ/[nm n]) Γ₀) (ih (Finset.mem_insert_of_mem hmem0))
      exact Zeh.wk (inv1Pull (∀⁰ φ₀) _ hhead Γ₀)
        (Zeh.exI χ n hβ hβNF hαNF (Cl_mono (adjoin_le H n₀) hβH)
          (le_trans hbound (hardy_monotone _ (le_max_left m n₀))) P)
  | @cut α βφ βψ e H m c Γ₀ χ hcompl hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH d₁ d₂ ih₁ ih₂ =>
      have P₁ := Zeh.wk (inv1Push (∀⁰ φ₀) _ χ Γ₀) (ih₁ (Finset.mem_insert_of_mem hmem))
      have P₂ := Zeh.wk (inv1Push (∀⁰ φ₀) _ (∼χ) Γ₀) (ih₂ (Finset.mem_insert_of_mem hmem))
      exact Zeh.cut χ hcompl hβφ hβψ hβφNF hβψNF hαNF
        (Cl_mono (adjoin_le H n₀) hβφH) (Cl_mono (adjoin_le H n₀) hβψH) P₁ P₂

/-! ## Kernel-footprint attributes

Only nodes with a real (sorry-free) proof carry a kernel-footprint attribute; `cutElimPass_Zf`
is still `sorryAx`-bearing and is not eligible. -/

attribute [goodstein_blueprint 10 clean "zeh_inversion_suite" "0" 100 allInv_Zeh
  []
  ["∀-inversion, mirrors the banked Provable.allInv; [Tow20, Theorem 19.4]",
   "GoodsteinPA.OperatorZeh.orInv_Zeh / andInvL_Zeh / andInvR_Zeh: complete propositional companions, axiom-clean",
   "Suite completeness: the minimal core admits no fifth inversion"]
  "The Zeh inversion suite: control-preserving inversions (∀ at the relativization + running stage) feeding the fixed-control reduction and the cut-elimination assembly."]
  allInv_Zeh

/-! ## Companion inversions

`orInv_Zeh`, `andInvL_Zeh`, `andInvR_Zeh` — the propositional inversions mirroring the `Provable`
suite (`OperatorZinfty.lean:221/326/404`).  They keep the same `(α, e, H, m, c)` (unlike
`allInv_Zeh`, which raises the stage/relativization), so no `mono_H`/`Cl_mono` re-keying is
needed — the side-condition memberships thread through unchanged.  Since the minimal `Zeh` core
has no `andI`/`orI` introduction rule, `φ ⋏ ψ` / `φ ⋎ ψ` is never principal: every case just
threads the inversion past a passive side formula, so these ports are strictly shorter than
`Provable`'s (which each carry a principal `andI`/`orI` sub-case).  They do not consume the f-slot
statements — reused by a cut-elimination assembly for cuts on propositional formulas.
`∧`-inversion is [Tow20, Theorem 19.3]; `∨`-inversion is standard and has no dedicated
theorem number in [Tow20] (`∨` is symmetric/trivial there).

- [Tow20, §19]
-/

/-- Double-insert reshuffle helpers (∨-inversion inserts both `φ` and `ψ`; re-derivations of
the `private` `OperatorZinfty` copies). -/
theorem invPush (A b : ArithmeticFormula ℕ) (s : Finset (ArithmeticFormula ℕ)) {φ ψ : ArithmeticFormula ℕ} :
    insert φ (insert ψ ((insert b s).erase A)) ⊆ insert b (insert φ (insert ψ (s.erase A))) := by
  intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto

theorem invPull (A : ArithmeticFormula ℕ) {b : ArithmeticFormula ℕ} (h : b ≠ A) (s : Finset (ArithmeticFormula ℕ)) {φ ψ : ArithmeticFormula ℕ} :
    insert b (insert φ (insert ψ (s.erase A))) ⊆ insert φ (insert ψ ((insert b s).erase A)) := by
  intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
  rcases hx with rfl | rfl | rfl | hx
  · exact Or.inr (Or.inr ⟨h, Or.inl rfl⟩)
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr ⟨hx.1, Or.inr hx.2⟩)

/-- **∨-inversion, `Zeh` form**: replace `φ ⋎ ψ` by `φ, ψ`, same `(α, e, H, m, c)`. Standard
∨-inversion; cf. [Tow20, §19]. -/
theorem orInv_Zeh {φ ψ : ArithmeticFormula ℕ}
    (dd : Zeh α e H m c Γ) (hmem : (φ ⋎ ψ) ∈ Γ) :
    Zeh α e H m c (insert φ (insert ψ (Γ.erase (φ ⋎ ψ)))) := by
  induction dd with
  | @axL α e H m c Γ ar r v hp hn =>
      refine Zeh.axL r v ?_ ?_ <;>
        exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
          (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), by assumption⟩))
  | @wk α e H m c Δ Γ hsub dd ih =>
      by_cases hd : (φ ⋎ ψ) ∈ Δ
      · exact Zeh.wk (Finset.insert_subset_insert _ (Finset.insert_subset_insert _
          (Finset.erase_subset_erase _ hsub))) (ih hd)
      · refine Zeh.wk ?_ dd
        intro x hx
        exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
          (Finset.mem_erase.mpr ⟨fun e => hd (e ▸ hx), hsub hx⟩))
  | @weak α β e H m c Δ Γ hβ hβNF hαNF hβH hsub dd ih =>
      by_cases hd : (φ ⋎ ψ) ∈ Δ
      · exact Zeh.weak hβ hβNF hαNF hβH (Finset.insert_subset_insert _
          (Finset.insert_subset_insert _ (Finset.erase_subset_erase _ hsub))) (ih hd)
      · refine Zeh.weak hβ hβNF hαNF hβH ?_ dd
        intro x hx
        exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
          (Finset.mem_erase.mpr ⟨fun e => hd (e ▸ hx), hsub hx⟩))
  | @allω α e H m c Γ₀ χ β hβ hβNF hαNF hβH dd ih =>
      have hhead : (∀⁰ χ) ≠ (φ ⋎ ψ) := by intro h; simp [UnivQuantifier.all, Vee.vee] at h
      have hmem0 : (φ ⋎ ψ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
      have key : ∀ n, Zeh (β n) e (adjoin H n) (max m n) c
          (insert (χ/[nm n]) (insert φ (insert ψ (Γ₀.erase (φ ⋎ ψ))))) := fun n =>
        Zeh.wk (invPush (φ ⋎ ψ) (χ/[nm n]) Γ₀) (ih n (Finset.mem_insert_of_mem hmem0))
      exact Zeh.wk (invPull (φ ⋎ ψ) hhead Γ₀) (Zeh.allω χ β hβ hβNF hαNF hβH key)
  | @exI α β e H m c Γ₀ χ n hβ hβNF hαNF hβH hbound dd ih =>
      have hhead : (∃⁰ χ) ≠ (φ ⋎ ψ) := by intro h; simp [ExsQuantifier.exs, Vee.vee] at h
      have hmem0 : (φ ⋎ ψ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
      have P := Zeh.wk (invPush (φ ⋎ ψ) (χ/[nm n]) Γ₀) (ih (Finset.mem_insert_of_mem hmem0))
      exact Zeh.wk (invPull (φ ⋎ ψ) hhead Γ₀) (Zeh.exI χ n hβ hβNF hαNF hβH hbound P)
  | @cut α βφ βψ e H m c Γ₀ χ hcompl hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH d₁ d₂ ih₁ ih₂ =>
      have P₁ := Zeh.wk (invPush (φ ⋎ ψ) χ Γ₀) (ih₁ (Finset.mem_insert_of_mem hmem))
      have P₂ := Zeh.wk (invPush (φ ⋎ ψ) (∼χ) Γ₀) (ih₂ (Finset.mem_insert_of_mem hmem))
      exact Zeh.cut χ hcompl hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH P₁ P₂

/-- **∧-inversion, left, `Zeh` form**: replace `φ ⋏ ψ` by `φ`, same `(α, e, H, m, c)`.

- [Tow20, Theorem 19.3]
-/
theorem andInvL_Zeh {φ ψ : ArithmeticFormula ℕ}
    (dd : Zeh α e H m c Γ) (hmem : (φ ⋏ ψ) ∈ Γ) :
    Zeh α e H m c (insert φ (Γ.erase (φ ⋏ ψ))) := by
  induction dd with
  | @axL α e H m c Γ ar r v hp hn =>
      refine Zeh.axL r v ?_ ?_ <;>
        exact Finset.mem_insert_of_mem
          (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), by assumption⟩)
  | @wk α e H m c Δ Γ hsub dd ih =>
      by_cases hh : (φ ⋏ ψ) ∈ Δ
      · exact Zeh.wk (Finset.insert_subset_insert _ (Finset.erase_subset_erase _ hsub)) (ih hh)
      · refine Zeh.wk ?_ dd
        intro x hx
        exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨fun e => hh (e ▸ hx), hsub hx⟩)
  | @weak α β e H m c Δ Γ hβ hβNF hαNF hβH hsub dd ih =>
      by_cases hh : (φ ⋏ ψ) ∈ Δ
      · exact Zeh.weak hβ hβNF hαNF hβH
          (Finset.insert_subset_insert _ (Finset.erase_subset_erase _ hsub)) (ih hh)
      · refine Zeh.weak hβ hβNF hαNF hβH ?_ dd
        intro x hx
        exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨fun e => hh (e ▸ hx), hsub hx⟩)
  | @allω α e H m c Γ₀ χ β hβ hβNF hαNF hβH dd ih =>
      have hhead : (∀⁰ χ) ≠ (φ ⋏ ψ) := by intro h; simp [UnivQuantifier.all, Wedge.wedge] at h
      have hmem0 : (φ ⋏ ψ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
      have key : ∀ n, Zeh (β n) e (adjoin H n) (max m n) c
          (insert (χ/[nm n]) (insert φ (Γ₀.erase (φ ⋏ ψ)))) := fun n =>
        Zeh.wk (inv1Push (φ ⋏ ψ) _ (χ/[nm n]) Γ₀) (ih n (Finset.mem_insert_of_mem hmem0))
      exact Zeh.wk (inv1Pull (φ ⋏ ψ) _ hhead Γ₀) (Zeh.allω χ β hβ hβNF hαNF hβH key)
  | @exI α β e H m c Γ₀ χ n hβ hβNF hαNF hβH hbound dd ih =>
      have hhead : (∃⁰ χ) ≠ (φ ⋏ ψ) := by intro h; simp [ExsQuantifier.exs, Wedge.wedge] at h
      have hmem0 : (φ ⋏ ψ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
      have P := Zeh.wk (inv1Push (φ ⋏ ψ) _ (χ/[nm n]) Γ₀) (ih (Finset.mem_insert_of_mem hmem0))
      exact Zeh.wk (inv1Pull (φ ⋏ ψ) _ hhead Γ₀) (Zeh.exI χ n hβ hβNF hαNF hβH hbound P)
  | @cut α βφ βψ e H m c Γ₀ χ hcompl hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH d₁ d₂ ih₁ ih₂ =>
      have P₁ := Zeh.wk (inv1Push (φ ⋏ ψ) _ χ Γ₀) (ih₁ (Finset.mem_insert_of_mem hmem))
      have P₂ := Zeh.wk (inv1Push (φ ⋏ ψ) _ (∼χ) Γ₀) (ih₂ (Finset.mem_insert_of_mem hmem))
      exact Zeh.cut χ hcompl hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH P₁ P₂

/-- **∧-inversion, right, `Zeh` form**: replace `φ ⋏ ψ` by `ψ`, same `(α, e, H, m, c)`.

- [Tow20, Theorem 19.3]
-/
theorem andInvR_Zeh {φ ψ : ArithmeticFormula ℕ}
    (dd : Zeh α e H m c Γ) (hmem : (φ ⋏ ψ) ∈ Γ) :
    Zeh α e H m c (insert ψ (Γ.erase (φ ⋏ ψ))) := by
  induction dd with
  | @axL α e H m c Γ ar r v hp hn =>
      refine Zeh.axL r v ?_ ?_ <;>
        exact Finset.mem_insert_of_mem
          (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), by assumption⟩)
  | @wk α e H m c Δ Γ hsub dd ih =>
      by_cases hh : (φ ⋏ ψ) ∈ Δ
      · exact Zeh.wk (Finset.insert_subset_insert _ (Finset.erase_subset_erase _ hsub)) (ih hh)
      · refine Zeh.wk ?_ dd
        intro x hx
        exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨fun e => hh (e ▸ hx), hsub hx⟩)
  | @weak α β e H m c Δ Γ hβ hβNF hαNF hβH hsub dd ih =>
      by_cases hh : (φ ⋏ ψ) ∈ Δ
      · exact Zeh.weak hβ hβNF hαNF hβH
          (Finset.insert_subset_insert _ (Finset.erase_subset_erase _ hsub)) (ih hh)
      · refine Zeh.weak hβ hβNF hαNF hβH ?_ dd
        intro x hx
        exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨fun e => hh (e ▸ hx), hsub hx⟩)
  | @allω α e H m c Γ₀ χ β hβ hβNF hαNF hβH dd ih =>
      have hhead : (∀⁰ χ) ≠ (φ ⋏ ψ) := by intro h; simp [UnivQuantifier.all, Wedge.wedge] at h
      have hmem0 : (φ ⋏ ψ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
      have key : ∀ n, Zeh (β n) e (adjoin H n) (max m n) c
          (insert (χ/[nm n]) (insert ψ (Γ₀.erase (φ ⋏ ψ)))) := fun n =>
        Zeh.wk (inv1Push (φ ⋏ ψ) _ (χ/[nm n]) Γ₀) (ih n (Finset.mem_insert_of_mem hmem0))
      exact Zeh.wk (inv1Pull (φ ⋏ ψ) _ hhead Γ₀) (Zeh.allω χ β hβ hβNF hαNF hβH key)
  | @exI α β e H m c Γ₀ χ n hβ hβNF hαNF hβH hbound dd ih =>
      have hhead : (∃⁰ χ) ≠ (φ ⋏ ψ) := by intro h; simp [ExsQuantifier.exs, Wedge.wedge] at h
      have hmem0 : (φ ⋏ ψ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
      have P := Zeh.wk (inv1Push (φ ⋏ ψ) _ (χ/[nm n]) Γ₀) (ih (Finset.mem_insert_of_mem hmem0))
      exact Zeh.wk (inv1Pull (φ ⋏ ψ) _ hhead Γ₀) (Zeh.exI χ n hβ hβNF hαNF hβH hbound P)
  | @cut α βφ βψ e H m c Γ₀ χ hcompl hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH d₁ d₂ ih₁ ih₂ =>
      have P₁ := Zeh.wk (inv1Push (φ ⋏ ψ) _ χ Γ₀) (ih₁ (Finset.mem_insert_of_mem hmem))
      have P₂ := Zeh.wk (inv1Push (φ ⋏ ψ) _ (∼χ) Γ₀) (ih₂ (Finset.mem_insert_of_mem hmem))
      exact Zeh.cut χ hcompl hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH P₁ P₂

/-! ## ∀-inversion in the slot calculus (feeds the reduction from a ∀-side derivation) -/

/-- `f ≤ rel1 f n₀` for monotone `f` (`f x ≤ f (max n₀ x)`). -/
private theorem f_le_rel1 (hf : Monotone f) (n₀ x : ℕ) :
    f x ≤ rel1 f n₀ x := hf (le_max_right n₀ x)

/-- **`allInv_Zef`** — ∀-inversion, slot form: port of `allInv_Zeh` with `max m n₀ ⤳ rel1 f n₀`.
The extracted instance runs at the relativization `adjoin H n₀` and the relativized slot
`rel1 f n₀`.  Needs `f` monotone (to raise `exI` bounds `n ≤ f 0 ≤ (rel1 f n₀) 0 = f n₀`).  The
operator threading is FREE (`mono_Hf`/`change_H`, R1). -/
theorem allInv_Zef {φ₀ : ArithmeticSemiformula ℕ 1} (n₀ : ℕ) (dd : Zef α e H f c Γ)
    (hmono : Monotone f) (hmem : (∀⁰ φ₀) ∈ Γ) :
    Zef α e (adjoin H n₀) (rel1 f n₀) c (insert (φ₀/[nm n₀]) (Γ.erase (∀⁰ φ₀))) := by
  induction dd with
  | @axL α e H f c Γ ar r v hp hn =>
      refine Zef.axL r v ?_ ?_ <;>
        exact Finset.mem_insert_of_mem
          (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), by assumption⟩)
  | @wk α e H f c Δ Γ hsub dd ih =>
      by_cases hh : (∀⁰ φ₀) ∈ Δ
      · exact Zef.wk (Finset.insert_subset_insert _ (Finset.erase_subset_erase _ hsub)) (ih hmono hh)
      · refine Zef.wk ?_ (dd.mono_Hf (f_le_rel1 hmono n₀))
        intro x hx
        exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨fun e => hh (e ▸ hx), hsub hx⟩)
  | @weak α β e H f c Δ Γ hβ hβNF hαNF hβH hsub dd ih =>
      by_cases hh : (∀⁰ φ₀) ∈ Δ
      · exact Zef.weak hβ hβNF hαNF (Cl_of_NF hβNF)
          (Finset.insert_subset_insert _ (Finset.erase_subset_erase _ hsub)) (ih hmono hh)
      · refine Zef.weak hβ hβNF hαNF (Cl_of_NF hβNF) ?_ (dd.mono_Hf (f_le_rel1 hmono n₀))
        intro x hx
        exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨fun e => hh (e ▸ hx), hsub hx⟩)
  | @allω α e H f c Γ₀ χ β hβ hβNF hαNF hβH dd ih =>
      by_cases hhd : (∀⁰ χ) = (∀⁰ φ₀)
      · obtain rfl := (Semiformula.all_inj _ _).mp hhd
        rw [Finset.erase_insert_eq_erase]
        by_cases hh : (∀⁰ χ) ∈ Γ₀
        · have h := ih n₀ (rel1_monotone hmono n₀) (Finset.mem_insert_of_mem hh)
          have h2 : Zef (β n₀) e (adjoin H n₀) (rel1 f n₀) c
              (insert (χ/[nm n₀]) ((insert (χ/[nm n₀]) Γ₀).erase (∀⁰ χ))) :=
            h.mono_Hf (fun x => le_of_eq (by simp only [rel1]; congr 1; omega))
          exact Zef.weak (hβ n₀) (hβNF n₀) hαNF (Cl_of_NF (hβNF n₀)) (princAllSub (∀⁰ χ) _ Γ₀) h2
        · rw [Finset.erase_eq_of_notMem hh]
          exact Zef.weak (hβ n₀) (hβNF n₀) hαNF (Cl_of_NF (hβNF n₀)) (Finset.Subset.refl _) (dd n₀)
      · have hmem0 : (∀⁰ φ₀) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhd e.symm
        have key : ∀ n, Zef (β n) e (adjoin (adjoin H n₀) n) (rel1 (rel1 f n₀) n) c
            (insert (χ/[nm n]) (insert (φ₀/[nm n₀]) (Γ₀.erase (∀⁰ φ₀)))) := by
          intro n
          have h := ih n (rel1_monotone hmono n) (Finset.mem_insert_of_mem hmem0)
          exact Zef.wk (inv1Push (∀⁰ φ₀) _ (χ/[nm n]) Γ₀)
            (h.mono_Hf (fun x => le_of_eq (by simp only [rel1]; congr 1; omega)))
        exact Zef.wk (inv1Pull (∀⁰ φ₀) _ hhd Γ₀)
          (Zef.allω χ β hβ hβNF hαNF (fun n => Cl_of_NF (hβNF n)) key)
  | @exI α β e H f c Γ₀ χ n hβ hβNF hαNF hβH hbound dd ih =>
      have hhead : (∃⁰ χ) ≠ (∀⁰ φ₀) := by intro h; simp [ExsQuantifier.exs, UnivQuantifier.all] at h
      have hmem0 : (∀⁰ φ₀) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
      have P := Zef.wk (inv1Push (∀⁰ φ₀) _ (χ/[nm n]) Γ₀) (ih hmono (Finset.mem_insert_of_mem hmem0))
      exact Zef.wk (inv1Pull (∀⁰ φ₀) _ hhead Γ₀)
        (Zef.exI χ n hβ hβNF hαNF (Cl_of_NF hβNF)
          (le_trans hbound (hmono (Nat.zero_le _))) P)
  | @cut α βφ βψ e H f c Γ₀ χ hcompl hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH d₁ d₂ ih₁ ih₂ =>
      have P₁ := Zef.wk (inv1Push (∀⁰ φ₀) _ χ Γ₀) (ih₁ hmono (Finset.mem_insert_of_mem hmem))
      have P₂ := Zef.wk (inv1Push (∀⁰ φ₀) _ (∼χ) Γ₀) (ih₂ hmono (Finset.mem_insert_of_mem hmem))
      exact Zef.cut χ hcompl hβφ hβψ hβφNF hβψNF hαNF
        (Cl_of_NF hβφNF) (Cl_of_NF hβψNF) P₁ P₂

/-! ## Propositional inversions in the slot judgment `Zef`

Slot-form ports of `orInv_Zeh`/`andInvL_Zeh`/`andInvR_Zeh` — the propositional inversions a
cut-elimination assembly would reuse for cuts on `⋏`/`⋎` formulas.  Control-preserving (same
`(α, e, H, f, c)`); since the minimal core has no `andI`/`orI` intro rule, `φ ⋏ ψ` / `φ ⋎ ψ` is
never principal, so every case threads the inversion past a passive side formula.  Completes the
`Zef` inversion suite (`allInv_Zef` + these three), mirroring the `Zeh` suite. -/

/-- **∨-inversion, `Zef` form**: replace `φ ⋎ ψ` by `φ, ψ`, same `(α, e, H, f, c)`. Standard
∨-inversion; cf. [Tow20, §19]. -/
theorem orInv_Zef {φ ψ : ArithmeticFormula ℕ}
    (dd : Zef α e H f c Γ) (hmem : (φ ⋎ ψ) ∈ Γ) :
    Zef α e H f c (insert φ (insert ψ (Γ.erase (φ ⋎ ψ)))) := by
  induction dd with
  | @axL α e H f c Γ ar r v hp hn =>
      refine Zef.axL r v ?_ ?_ <;>
        exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
          (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), by assumption⟩))
  | @wk α e H f c Δ Γ hsub dd ih =>
      by_cases hd : (φ ⋎ ψ) ∈ Δ
      · exact Zef.wk (Finset.insert_subset_insert _ (Finset.insert_subset_insert _
          (Finset.erase_subset_erase _ hsub))) (ih hd)
      · refine Zef.wk ?_ dd
        intro x hx
        exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
          (Finset.mem_erase.mpr ⟨fun e => hd (e ▸ hx), hsub hx⟩))
  | @weak α β e H f c Δ Γ hβ hβNF hαNF hβH hsub dd ih =>
      by_cases hd : (φ ⋎ ψ) ∈ Δ
      · exact Zef.weak hβ hβNF hαNF hβH (Finset.insert_subset_insert _
          (Finset.insert_subset_insert _ (Finset.erase_subset_erase _ hsub))) (ih hd)
      · refine Zef.weak hβ hβNF hαNF hβH ?_ dd
        intro x hx
        exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
          (Finset.mem_erase.mpr ⟨fun e => hd (e ▸ hx), hsub hx⟩))
  | @allω α e H f c Γ₀ χ β hβ hβNF hαNF hβH dd ih =>
      have hhead : (∀⁰ χ) ≠ (φ ⋎ ψ) := by intro h; simp [UnivQuantifier.all, Vee.vee] at h
      have hmem0 : (φ ⋎ ψ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
      have key : ∀ n, Zef (β n) e (adjoin H n) (rel1 f n) c
          (insert (χ/[nm n]) (insert φ (insert ψ (Γ₀.erase (φ ⋎ ψ))))) := fun n =>
        Zef.wk (invPush (φ ⋎ ψ) (χ/[nm n]) Γ₀) (ih n (Finset.mem_insert_of_mem hmem0))
      exact Zef.wk (invPull (φ ⋎ ψ) hhead Γ₀) (Zef.allω χ β hβ hβNF hαNF hβH key)
  | @exI α β e H f c Γ₀ χ n hβ hβNF hαNF hβH hbound dd ih =>
      have hhead : (∃⁰ χ) ≠ (φ ⋎ ψ) := by intro h; simp [ExsQuantifier.exs, Vee.vee] at h
      have hmem0 : (φ ⋎ ψ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
      have P := Zef.wk (invPush (φ ⋎ ψ) (χ/[nm n]) Γ₀) (ih (Finset.mem_insert_of_mem hmem0))
      exact Zef.wk (invPull (φ ⋎ ψ) hhead Γ₀) (Zef.exI χ n hβ hβNF hαNF hβH hbound P)
  | @cut α βφ βψ e H f c Γ₀ χ hcompl hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH d₁ d₂ ih₁ ih₂ =>
      have P₁ := Zef.wk (invPush (φ ⋎ ψ) χ Γ₀) (ih₁ (Finset.mem_insert_of_mem hmem))
      have P₂ := Zef.wk (invPush (φ ⋎ ψ) (∼χ) Γ₀) (ih₂ (Finset.mem_insert_of_mem hmem))
      exact Zef.cut χ hcompl hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH P₁ P₂

/-- **∧-inversion, left, `Zef` form**: replace `φ ⋏ ψ` by `φ`, same `(α, e, H, f, c)`.

- [Tow20, Theorem 19.3]
-/
theorem andInvL_Zef {φ ψ : ArithmeticFormula ℕ}
    (dd : Zef α e H f c Γ) (hmem : (φ ⋏ ψ) ∈ Γ) :
    Zef α e H f c (insert φ (Γ.erase (φ ⋏ ψ))) := by
  induction dd with
  | @axL α e H f c Γ ar r v hp hn =>
      refine Zef.axL r v ?_ ?_ <;>
        exact Finset.mem_insert_of_mem
          (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), by assumption⟩)
  | @wk α e H f c Δ Γ hsub dd ih =>
      by_cases hh : (φ ⋏ ψ) ∈ Δ
      · exact Zef.wk (Finset.insert_subset_insert _ (Finset.erase_subset_erase _ hsub)) (ih hh)
      · refine Zef.wk ?_ dd
        intro x hx
        exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨fun e => hh (e ▸ hx), hsub hx⟩)
  | @weak α β e H f c Δ Γ hβ hβNF hαNF hβH hsub dd ih =>
      by_cases hh : (φ ⋏ ψ) ∈ Δ
      · exact Zef.weak hβ hβNF hαNF hβH
          (Finset.insert_subset_insert _ (Finset.erase_subset_erase _ hsub)) (ih hh)
      · refine Zef.weak hβ hβNF hαNF hβH ?_ dd
        intro x hx
        exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨fun e => hh (e ▸ hx), hsub hx⟩)
  | @allω α e H f c Γ₀ χ β hβ hβNF hαNF hβH dd ih =>
      have hhead : (∀⁰ χ) ≠ (φ ⋏ ψ) := by intro h; simp [UnivQuantifier.all, Wedge.wedge] at h
      have hmem0 : (φ ⋏ ψ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
      have key : ∀ n, Zef (β n) e (adjoin H n) (rel1 f n) c
          (insert (χ/[nm n]) (insert φ (Γ₀.erase (φ ⋏ ψ)))) := fun n =>
        Zef.wk (inv1Push (φ ⋏ ψ) _ (χ/[nm n]) Γ₀) (ih n (Finset.mem_insert_of_mem hmem0))
      exact Zef.wk (inv1Pull (φ ⋏ ψ) _ hhead Γ₀) (Zef.allω χ β hβ hβNF hαNF hβH key)
  | @exI α β e H f c Γ₀ χ n hβ hβNF hαNF hβH hbound dd ih =>
      have hhead : (∃⁰ χ) ≠ (φ ⋏ ψ) := by intro h; simp [ExsQuantifier.exs, Wedge.wedge] at h
      have hmem0 : (φ ⋏ ψ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
      have P := Zef.wk (inv1Push (φ ⋏ ψ) _ (χ/[nm n]) Γ₀) (ih (Finset.mem_insert_of_mem hmem0))
      exact Zef.wk (inv1Pull (φ ⋏ ψ) _ hhead Γ₀) (Zef.exI χ n hβ hβNF hαNF hβH hbound P)
  | @cut α βφ βψ e H f c Γ₀ χ hcompl hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH d₁ d₂ ih₁ ih₂ =>
      have P₁ := Zef.wk (inv1Push (φ ⋏ ψ) _ χ Γ₀) (ih₁ (Finset.mem_insert_of_mem hmem))
      have P₂ := Zef.wk (inv1Push (φ ⋏ ψ) _ (∼χ) Γ₀) (ih₂ (Finset.mem_insert_of_mem hmem))
      exact Zef.cut χ hcompl hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH P₁ P₂

/-- **∧-inversion, right, `Zef` form**: replace `φ ⋏ ψ` by `ψ`, same `(α, e, H, f, c)`.

- [Tow20, Theorem 19.3]
-/
theorem andInvR_Zef {φ ψ : ArithmeticFormula ℕ}
    (dd : Zef α e H f c Γ) (hmem : (φ ⋏ ψ) ∈ Γ) :
    Zef α e H f c (insert ψ (Γ.erase (φ ⋏ ψ))) := by
  induction dd with
  | @axL α e H f c Γ ar r v hp hn =>
      refine Zef.axL r v ?_ ?_ <;>
        exact Finset.mem_insert_of_mem
          (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), by assumption⟩)
  | @wk α e H f c Δ Γ hsub dd ih =>
      by_cases hh : (φ ⋏ ψ) ∈ Δ
      · exact Zef.wk (Finset.insert_subset_insert _ (Finset.erase_subset_erase _ hsub)) (ih hh)
      · refine Zef.wk ?_ dd
        intro x hx
        exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨fun e => hh (e ▸ hx), hsub hx⟩)
  | @weak α β e H f c Δ Γ hβ hβNF hαNF hβH hsub dd ih =>
      by_cases hh : (φ ⋏ ψ) ∈ Δ
      · exact Zef.weak hβ hβNF hαNF hβH
          (Finset.insert_subset_insert _ (Finset.erase_subset_erase _ hsub)) (ih hh)
      · refine Zef.weak hβ hβNF hαNF hβH ?_ dd
        intro x hx
        exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨fun e => hh (e ▸ hx), hsub hx⟩)
  | @allω α e H f c Γ₀ χ β hβ hβNF hαNF hβH dd ih =>
      have hhead : (∀⁰ χ) ≠ (φ ⋏ ψ) := by intro h; simp [UnivQuantifier.all, Wedge.wedge] at h
      have hmem0 : (φ ⋏ ψ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
      have key : ∀ n, Zef (β n) e (adjoin H n) (rel1 f n) c
          (insert (χ/[nm n]) (insert ψ (Γ₀.erase (φ ⋏ ψ)))) := fun n =>
        Zef.wk (inv1Push (φ ⋏ ψ) _ (χ/[nm n]) Γ₀) (ih n (Finset.mem_insert_of_mem hmem0))
      exact Zef.wk (inv1Pull (φ ⋏ ψ) _ hhead Γ₀) (Zef.allω χ β hβ hβNF hαNF hβH key)
  | @exI α β e H f c Γ₀ χ n hβ hβNF hαNF hβH hbound dd ih =>
      have hhead : (∃⁰ χ) ≠ (φ ⋏ ψ) := by intro h; simp [ExsQuantifier.exs, Wedge.wedge] at h
      have hmem0 : (φ ⋏ ψ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
      have P := Zef.wk (inv1Push (φ ⋏ ψ) _ (χ/[nm n]) Γ₀) (ih (Finset.mem_insert_of_mem hmem0))
      exact Zef.wk (inv1Pull (φ ⋏ ψ) _ hhead Γ₀) (Zef.exI χ n hβ hβNF hαNF hβH hbound P)
  | @cut α βφ βψ e H f c Γ₀ χ hcompl hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH d₁ d₂ ih₁ ih₂ =>
      have P₁ := Zef.wk (inv1Push (φ ⋏ ψ) _ χ Γ₀) (ih₁ (Finset.mem_insert_of_mem hmem))
      have P₂ := Zef.wk (inv1Push (φ ⋏ ψ) _ (∼χ) Γ₀) (ih₂ (Finset.mem_insert_of_mem hmem))
      exact Zef.cut χ hcompl hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH P₁ P₂

end GoodsteinPA.OperatorZeh
