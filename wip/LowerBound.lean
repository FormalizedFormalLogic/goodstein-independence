/-
# The witness-bounded cut-free lower bound, over the **concrete** Hardy hierarchy (M6)

`wip/WitnessBound.lean` proved the ∃-fragment lower bound (`lowerBound_existential`) *modulo* an
abstract Hardy monotonicity hypothesis `Hmono : β < α → τ β < k → h β k ≤ h α k`.  This file
**discharges that hypothesis concretely**: it re-states the witness-bounded calculus over `ONote`
(Towsner's ordinals `< ε₀` ARE the notation system), instantiates the Hardy data with the real
`hardy`/`norm` from `src/GoodsteinPA/Hardy.lean` (ported Track-1), and supplies `Hmono` from
`hardy_le_of_lt` — the index-monotonicity lemma whose budget side condition `norm α ≤ x` is exactly
Towsner's `τ β < k`.  The Goodstein atom-truth + `G` are the real ones (from `Defs.lean`).

**Results (all axiom-clean):**
* `lowerBound_existential_hardy` — the ∀-free Goodstein-fragment lower bound, **zero abstract
  hypotheses**, over the genuine Hardy hierarchy and genuine Goodstein function.
* `B.mono_k`, `B.allInv` — `k`-monotonicity and **∀-inversion** (the universal is inverted away,
  not accumulated — the resolution of the lap-4 `bounding` frontier; see
  `ANALYSIS-2026-06-22-bounding-resolution.md`).
* `lowerBound_hardy` — the **full** Goodstein lower bound (Towsner Thm 17.1): no witness-bounded
  cut-free derivation of `gAll = ∀x∃y g_y(x)=0` at `(α,k)`, **modulo Goodstein domination `Hdom`**
  (`∃ x, hardy α (max k x) < G x`).  The `gAll`/`I∀` accumulation worry of the lap-4 handoff is
  resolved here, machine-checked.

**`Hdom` is now discharged** (lap 6): `Hdom_of_NF` supplies `∃ x, hardy α (max k x) < G x` from the
ported Goodstein-dominates-fastGrowing chain (`GoodsteinPA.Dom`, `src/Domination.lean`) bridged via
`hardy_le_fastGrowing` + `G = goodsteinLength` + the `+2`→strict iterate split (`add_le_iterate_of_lt`).
So `lowerBound_hardy_selfcontained` is the **full Towsner Thm 17.1 with no hypotheses beyond `α.NF`**.
Promoted to `src/` — terminal asset (M6 lower-bound half complete). `#print axioms` carries the
documented `native_decide` Goodstein base-case artifacts (🟢 finite witnesses) via the domination path.
-/
import Mathlib.SetTheory.Ordinal.Notation
import Mathlib.Order.Lattice.Nat
import Mathlib.Order.Iterate
import GoodsteinPA.Defs
import GoodsteinPA.Hardy
import GoodsteinPA.Domination

namespace GoodsteinPA.LowerBoundHardy

open ONote Ordinal GoodsteinPA.FastGrowing

/-! ## Goodstein fragment formulas + the real `G` (mirrors `wip/WitnessBound.lean`) -/

inductive GForm
  | atom (m n : ℕ)   -- `g_m(n) = 0`
  | gEx (n : ℕ)      -- `∃y g_y(n) = 0`
  | gAll             -- `∀x ∃y g_y(x) = 0`
  deriving DecidableEq

abbrev Seq := Finset GForm
open GForm

/-- `g_m(n)=0` true in ℕ. -/
def atomTrue (m n : ℕ) : Prop := goodsteinSeq n m = 0
instance (m n : ℕ) : Decidable (atomTrue m n) := by unfold atomTrue; infer_instance

/-- The Goodstein function: least zero step (Towsner Def 7.1). -/
noncomputable def G (n : ℕ) : ℕ := sInf {m | goodsteinSeq n m = 0}

/-- `HG`, concretely: a true atom forces `m ≥ G n`. -/
theorem G_le_of_atomTrue {m n : ℕ} (h : atomTrue m n) : G n ≤ m := Nat.sInf_le h

/-! ## The witness-bounded cut-free calculus over `ONote`

Identical rule shape to `wip/WitnessBound.lean : B`, but the height index is an `ONote` (so
`h := hardy`, `τ := norm` are *concrete*).  `NF` hypotheses are carried where `hardy_le_of_lt`
needs them; the well-founded descent uses only `ONote.lt_def` (`β < α ↔ repr β < repr α`). -/
inductive B : ONote → ℕ → Seq → Prop
  | trueR {α : ONote} {k : ℕ} {Γ : Seq} {m n : ℕ}
      (hmem : atom m n ∈ Γ) (htrue : atomTrue m n) (hτ : norm α < k) : B α k Γ
  | weak {α β : ONote} {k : ℕ} {Δ Γ : Seq}
      (hβ : β < α) (hβNF : β.NF) (hαNF : α.NF) (hτ : norm β < k)
      (hsub : Δ ⊆ Γ) (d : B β k Δ) : B α k Γ
  | exI {α β : ONote} {k : ℕ} {Γ : Seq} {n v : ℕ}
      (hβ : β < α) (hβNF : β.NF) (hαNF : α.NF) (hτ : norm β < k) (hbound : v ≤ hardy α k)
      (hmem : gEx n ∈ Γ) (d : B β k (insert (atom v n) Γ)) : B α k Γ
  | allI {α : ONote} {k : ℕ} {Γ : Seq} (β : ℕ → ONote)
      (hmem : gAll ∈ Γ) (hβ : ∀ n, β n < α) (hβNF : ∀ n, (β n).NF) (hαNF : α.NF)
      (hτ : ∀ n, norm (β n) < max k n)
      (d : ∀ n, B (β n) (max k n) (insert (gEx n) Γ)) : B α k Γ

/-- **Hardy index monotonicity = `Hmono`, concretely.**  For NF notations `β < α` with the budget
`norm β < k`, `hardy β k ≤ hardy α k`.  This is `hardy_le_of_lt` with `x := k` and the strict
budget weakened to `≤`. -/
theorem hardy_mono_of_lt {β α : ONote} {k : ℕ} (hβNF : β.NF) (hαNF : α.NF)
    (hβα : β < α) (hτ : norm β < k) : hardy β k ≤ hardy α k :=
  hardy_le_of_lt hβNF hαNF hβα (Nat.le_of_lt hτ)

/-- **The ∃-fragment lower bound, fully concrete (Towsner Thm 17.1, ∀-free part).**

Over the real Hardy hierarchy (`hardy`) and the real Goodstein function (`G`), the witness-bounded
cut-free calculus cannot derive a sequent of pending existentials + false atoms all of which are
"out of reach": every `gEx n` with `hardy α k < G n`, every `atom m n` with `m < G n`.  No abstract
hypotheses — `Hmono` is `hardy_le_of_lt`, `HG` is `G_le_of_atomTrue`. -/
theorem lowerBound_existential_hardy :
    ∀ (α : ONote) (k : ℕ) (Γ : Seq),
      (∀ f ∈ Γ, (∃ n, f = gEx n ∧ hardy α k < G n) ∨ (∃ m n, f = atom m n ∧ m < G n)) →
      ¬ B α k Γ := by
  suffices H : ∀ (g : Ordinal.{0}) (α : ONote), α.repr = g →
      ∀ (k : ℕ) (Γ : Seq),
        (∀ f ∈ Γ, (∃ n, f = gEx n ∧ hardy α k < G n) ∨ (∃ m n, f = atom m n ∧ m < G n)) →
        ¬ B α k Γ from
    fun α k Γ h => H α.repr α rfl k Γ h
  intro g
  induction g using WellFoundedLT.induction with
  | _ g IH =>
    intro α ho k Γ hcond hB
    cases hB with
    | trueR hmem htrue hτ =>
      rename_i m n
      rcases hcond _ hmem with ⟨n', hf, _⟩ | ⟨m', n', hf, hlt⟩
      · exact absurd hf (by simp)
      · obtain ⟨rfl, rfl⟩ : m = m' ∧ n = n' := by simpa [GForm.atom.injEq] using hf
        exact absurd (G_le_of_atomTrue htrue) (by omega)
    | weak hβ hβNF hαNF hτ hsub d =>
      rename_i β Δ
      have hrβ : β.repr < g := by rw [← ho]; exact lt_def.mp hβ
      refine IH β.repr hrβ β rfl k Δ (fun f hf => ?_) d
      rcases hcond f (hsub hf) with ⟨n, hfn, hgt⟩ | ⟨m, n, hfm, hlt⟩
      · exact Or.inl ⟨n, hfn, lt_of_le_of_lt (hardy_mono_of_lt hβNF hαNF hβ hτ) hgt⟩
      · exact Or.inr ⟨m, n, hfm, hlt⟩
    | exI hβ hβNF hαNF hτ hbound hmem d =>
      rename_i β n v
      have hrβ : β.repr < g := by rw [← ho]; exact lt_def.mp hβ
      have hgtn : hardy α k < G n := by
        rcases hcond _ hmem with ⟨n', hfn, hgt⟩ | ⟨_, _, hf, _⟩
        · obtain rfl : n = n' := by simpa [GForm.gEx.injEq] using hfn
          exact hgt
        · exact absurd hf (by simp)
      refine IH β.repr hrβ β rfl k (insert (atom v n) Γ) (fun f hf => ?_) d
      rcases Finset.mem_insert.mp hf with rfl | hfΓ
      · exact Or.inr ⟨v, n, rfl, lt_of_le_of_lt hbound hgtn⟩
      · rcases hcond f hfΓ with ⟨n', hfn, hgt⟩ | ⟨m, n', hfm, hlt⟩
        · exact Or.inl ⟨n', hfn, lt_of_le_of_lt (hardy_mono_of_lt hβNF hαNF hβ hτ) hgt⟩
        · exact Or.inr ⟨m, n', hfm, hlt⟩
    | allI β hmem _ _ _ _ =>
      rcases hcond _ hmem with ⟨_, hf, _⟩ | ⟨_, _, hf, _⟩ <;> exact absurd hf (by simp)

/-! ## `k`-monotonicity and ∀-inversion (toward the full Thm 17.1)

The numeric bound `k` is a *weaker* constraint as it grows (`τ α < k` easier, witness bound
`hardy α k` larger by `hardy_monotone`).  And the universal `gAll` can be **inverted away**: a
derivation of a sequent containing `gAll` yields a derivation of the instance sequent with `gAll`
replaced by `gEx n₀`.  Together with `lowerBound_existential_hardy` (the gAll-free fragment) and
Goodstein domination, these give the full lower bound — see `ANALYSIS-2026-06-22-bounding-resolution.md`. -/

/-- **`k`-monotonicity.**  Raising the numeric bound only relaxes every side condition. -/
theorem B.mono_k : ∀ {α : ONote} {k : ℕ} {Γ : Seq}, B α k Γ → ∀ {k' : ℕ}, k ≤ k' → B α k' Γ := by
  intro α k Γ d
  induction d with
  | trueR hmem htrue hτ => intro k' hk; exact B.trueR hmem htrue (lt_of_lt_of_le hτ hk)
  | weak hβ hβNF hαNF hτ hsub _ ih =>
      intro k' hk; exact B.weak hβ hβNF hαNF (lt_of_lt_of_le hτ hk) hsub (ih hk)
  | exI hβ hβNF hαNF hτ hbound hmem _ ih =>
      intro k' hk
      exact B.exI hβ hβNF hαNF (lt_of_lt_of_le hτ hk)
        (le_trans hbound (hardy_monotone _ hk)) hmem (ih hk)
  | allI β hmem hβ hβNF hαNF hτ _ ih =>
      intro k' hk
      exact B.allI β hmem hβ hβNF hαNF
        (fun n => lt_of_lt_of_le (hτ n) (max_le_max hk le_rfl))
        (fun n => ih n (max_le_max hk le_rfl))

/-- **∀-inversion for `B`.**  A derivation of `Γ ∋ gAll` yields a derivation of the instance sequent
`{gEx n₀} ∪ (Γ \ gAll)` at the (possibly raised) numeric bound `max k n₀` and the same ordinal `α`.
The principal `allI` case hands over the premise `B (β n₀) (max k n₀) (insert (gEx n₀) Γ)` and lifts
the ordinal back to `α` via `weak`; the other cases commute with the inversion (k-weakened up). -/
theorem B.allInv (n₀ : ℕ) :
    ∀ {α : ONote} {k : ℕ} {Γ : Seq}, B α k Γ → gAll ∈ Γ →
      B α (max k n₀) (insert (gEx n₀) (Γ.erase gAll)) := by
  intro α k Γ d
  induction d with
  | @trueR α k Γ m n hmem htrue hτ =>
      intro _
      -- the true atom survives erasing `gAll` and the new `gEx n₀`
      refine B.trueR (m := m) (n := n) ?_ htrue (lt_of_lt_of_le hτ (le_max_left _ _))
      exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨by simp, hmem⟩)
  | @weak α β k Δ Γ hβ hβNF hαNF hτ hsub dd ih =>
      intro _
      by_cases hΔ : gAll ∈ Δ
      · exact B.weak hβ hβNF hαNF (lt_of_lt_of_le hτ (le_max_left _ _))
          (Finset.insert_subset_insert _ (Finset.erase_subset_erase _ hsub)) (ih hΔ)
      · -- `gAll ∉ Δ` ⇒ `Δ ⊆ Γ.erase gAll`; weaken the unchanged subderivation (k raised)
        refine B.weak hβ hβNF hαNF (lt_of_lt_of_le hτ (le_max_left _ _)) ?_
          (B.mono_k dd (le_max_left _ _))
        intro x hx
        exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨fun h => hΔ (h ▸ hx), hsub hx⟩)
  | @exI α β k Γ n v hβ hβNF hαNF hτ hbound hmem _ ih =>
      intro hgAll
      have key : B β (max k n₀) (insert (gEx n₀) (insert (atom v n) (Γ.erase gAll))) := by
        have := ih (Finset.mem_insert_of_mem hgAll)
        rwa [Finset.erase_insert_of_ne (by simp)] at this
      refine B.exI hβ hβNF hαNF (lt_of_lt_of_le hτ (le_max_left _ _))
        (le_trans hbound (hardy_monotone _ (le_max_left _ _)))
        (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨by simp, hmem⟩)) ?_
      -- reorder the inserts to match `exI`'s premise shape
      rwa [Finset.insert_comm] at key
  | @allI α k Γ β hmem hβ hβNF hαNF hτ d ih =>
      intro _
      -- principal case: use the premise at index `n₀`, invert away the lingering `gAll`, lift via `weak`
      have hprem : B (β n₀) (max k n₀) (insert (gEx n₀) (Γ.erase gAll)) := by
        have h := ih n₀ (Finset.mem_insert_of_mem hmem)
        rw [Finset.erase_insert_of_ne (by simp), Finset.insert_idem] at h
        rwa [max_eq_left (le_max_right k n₀)] at h
      exact B.weak (hβ n₀) (hβNF n₀) hαNF (hτ n₀) (fun _ h => h) hprem

/-- **The full Goodstein lower bound (Towsner Thm 17.1), over the concrete Hardy hierarchy.**

If Goodstein length dominates the Hardy level `α` at some argument (`∃ x, hardy α (max k x) < G x` —
Towsner Thm 7.2/9.8, `Hdom`), then the witness-bounded cut-free calculus **cannot** derive the
Goodstein sentence `gAll = ∀x∃y g_y(x)=0` at bound `(α,k)`.

Proof: invert `gAll` at the dominating index `x` (`B.allInv`) to a gAll-free single-existential
sequent `{gEx x}` at bound `(α, max k x)`; domination makes `gEx x` out of reach; the proven
∃-fragment `lowerBound_existential_hardy` finishes.  **No abstract hypotheses except `Hdom`** — the
`gAll`/`I∀` accumulation frontier of `wip/WitnessBound.lean : bounding` is resolved (invert, don't
accumulate; see `ANALYSIS-2026-06-22-bounding-resolution.md`). -/
theorem lowerBound_hardy {α : ONote} {k : ℕ} (Hdom : ∃ x, hardy α (max k x) < G x) :
    ¬ B α k ({gAll} : Seq) := by
  intro hB
  obtain ⟨x, hx⟩ := Hdom
  have hinv := B.allInv x hB (by simp)
  rw [Finset.erase_singleton] at hinv
  refine lowerBound_existential_hardy α (max k x) (insert (gEx x) ∅) (fun f hf => ?_) hinv
  rw [Finset.mem_insert] at hf
  rcases hf with rfl | h
  · exact Or.inl ⟨x, rfl, hx⟩
  · exact absurd h (Finset.notMem_empty _)

/-! ## Discharging `Hdom` from the ported Goodstein domination → self-contained Thm 17.1

The domination input `Hdom` is supplied by Track-1's `goodsteinLength_dominates_fastGrowing` (ported
to `GoodsteinPA.Dom`), bridged to `hardy`/`G` via `hardy_le_fastGrowing` and `G = goodsteinLength`.
The `+2`→strict gap is closed by domination at `osucc α` (the fastGrowing-over-hardy gap swallows the
`+2`). Result: `lowerBound_hardy_selfcontained` — no hypotheses beyond `α.NF`. -/

/-- `G` = Track-1's `goodsteinLength`: both the least zero step (set nonempty by termination). -/
theorem G_eq_goodsteinLength (n : ℕ) : G n = GoodsteinPA.Dom.goodsteinLength n := by
  apply le_antisymm
  · exact Nat.sInf_le (GoodsteinPA.Dom.goodsteinSeq_goodsteinLength n)
  · exact Nat.find_le (Nat.sInf_mem (GoodsteinPA.Dom.goodstein_terminates n))

/-- Iterating a strictly-inflationary map adds ≥ the iteration count. -/
theorem add_le_iterate_of_lt {g : ℕ → ℕ}
    (hstep : ∀ y, 1 ≤ y → y + 1 ≤ g y) (hpos : ∀ y, 1 ≤ y → 1 ≤ g y) :
    ∀ (j : ℕ) {y : ℕ}, 1 ≤ y → y + j ≤ g^[j] y := by
  intro j
  induction j with
  | zero => intro y hy; simp
  | succ j ih =>
    intro y hy
    rw [Function.iterate_succ_apply]
    have h1 : 1 ≤ g y := hpos y hy
    have hstepy : y + 1 ≤ g y := hstep y hy
    have := ih (y := g y) h1
    omega

/-- **`Hdom`, strict.** For NF `α`, Goodstein length eventually strictly exceeds `hardy α`. -/
theorem hardy_lt_goodsteinLength {α : ONote} (hα : α.NF) :
    ∃ N, ∀ m, N ≤ m → hardy α m < GoodsteinPA.Dom.goodsteinLength m := by
  obtain ⟨N, hN⟩ := GoodsteinPA.Dom.goodsteinLength_dominates_fastGrowing (osucc_NF hα)
  refine ⟨max N 4, fun m hm => ?_⟩
  have hm4 : 4 ≤ m := le_trans (le_max_right _ _) hm
  have hmN : N ≤ m := le_trans (le_max_left _ _) hm
  have hfs : fastGrowing (osucc α) m = (fastGrowing α)^[m] m := by
    rw [fastGrowing_succ (osucc α) (fundamentalSequence_osucc hα)]
  have hstep : ∀ y, 1 ≤ y → y + 1 ≤ fastGrowing α y := fun y hy => lt_fastGrowing α hy
  have hpos : ∀ y, 1 ≤ y → 1 ≤ fastGrowing α y := fun y hy => le_trans hy (le_fastGrowing α y)
  have hsplit : (fastGrowing α)^[m] m = (fastGrowing α)^[m-1] (fastGrowing α m) := by
    obtain ⟨n, hn⟩ : ∃ n, m = n + 1 := ⟨m-1, by omega⟩
    rw [hn]; simp [Function.iterate_succ_apply]
  have hiter : fastGrowing α m + (m - 1) ≤ (fastGrowing α)^[m - 1] (fastGrowing α m) :=
    add_le_iterate_of_lt hstep hpos (m - 1) (hpos m (by omega))
  have hHF : hardy α m ≤ fastGrowing α m := hardy_le_fastGrowing α m (by omega)
  have hdom := hN m hmN
  rw [hfs, hsplit] at hdom
  omega

/-- **`Hdom` in the shape `lowerBound_hardy` consumes.** -/
theorem Hdom_of_NF {α : ONote} (hα : α.NF) (k : ℕ) : ∃ x, hardy α (max k x) < G x := by
  obtain ⟨N, hN⟩ := hardy_lt_goodsteinLength hα
  refine ⟨max N k, ?_⟩
  have hxk : k ≤ max N k := le_max_right _ _
  have hxN : N ≤ max N k := le_max_left _ _
  rw [max_eq_right hxk, G_eq_goodsteinLength]
  exact hN _ hxN

/-- **Controlled-index domination** (the §19.6-option-2 lower-bound ingredient). For a *linearly
shifted* Hardy argument `x ↦ x + c`, Goodstein length still eventually dominates: `hardy α (x+c) <
G x` for all large `x`. Proof: `hardy α (x+c) = hardy (α + ofNat c) x` (`hardy_add_ofNat`, finite-tail
additivity), then `hardy_lt_goodsteinLength` on the NF ordinal `α + ofNat c`. This is exactly what a
controlled ω-rule (premise index `≤ x + c`, as cut-elimination's commuting case produces) needs so the
witness-bound lower bound survives the reindexing. -/
theorem hardy_shift_lt_goodsteinLength {α : ONote} (hα : α.NF) (c : ℕ) :
    ∃ N, ∀ x, N ≤ x → hardy α (x + c) < G x := by
  haveI := hα
  have hNF : (α + ONote.ofNat c).NF := ONote.add_nf α (ONote.ofNat c)
  obtain ⟨N, hN⟩ := hardy_lt_goodsteinLength hNF
  refine ⟨N, fun x hx => ?_⟩
  rw [← hardy_add_ofNat hα c, G_eq_goodsteinLength]
  exact hN x hx

/-- **Wrong-order composition domination** (the §19.6 control-ordinal operator-calculus
lower-bound ingredient). For NF `α`, `e`, the nested composition `H_α(H_e(m))` — the small
cut-formula bound `α` applied *outside* a large control value `H_e(m)` — is eventually
strictly below Goodstein length. Unlike the control-side collapse `hardy_add_collapse`
(`H_e∘H_α = H_{e+α}`, big ordinal outside), this order is NOT a single Hardy level
(concatenation always puts the larger ordinal outside); instead it is dominated by
`H_{ω^Q·2}` with `Q = osucc(lead α + lead e)` exceeding both `α` and `e`
(`H_α(H_e(m)) ≤ H_{ω^Q}(H_{ω^Q}(m)) = H_{ω^Q·2}(m)` via index monotonicity + the coefficient
law `hardy_oadd_coeff`), and `ω^Q·2 < ε₀` is Goodstein-dominated by `hardy_lt_goodsteinLength`.
This is what the operator-calculus lower bound needs to absorb the nested control index
`hardy α (hardy e (·) + d)` (the finite `+d` reduces first via `hardy_add_ofNat`). -/
theorem hardy_comp_lt_goodsteinLength {α e : ONote} (hα : α.NF) (he : e.NF) :
    ∃ N, ∀ m, N ≤ m → hardy α (hardy e m) < GoodsteinPA.Dom.goodsteinLength m := by
  haveI : (lead α).NF := lead_NF hα
  haveI : (lead e).NF := lead_NF he
  have hSnf : (lead α + lead e).NF := ONote.add_nf (lead α) (lead e)
  set S : ONote := lead α + lead e with hSdef
  have hQnf : (osucc S).NF := osucc_NF hSnf
  set Q : ONote := osucc S with hQdef
  have hPnf : (oadd Q 1 0).NF := NF.oadd hQnf 1 NFBelow.zero
  set P : ONote := oadd Q 1 0 with hPdef
  have hβnf : (oadd Q (Nat.succPNat 1) 0).NF := NF.oadd hQnf _ NFBelow.zero
  have hSrepr : S.repr = (lead α).repr + (lead e).repr := by rw [hSdef]; exact repr_add _ _
  have hQrepr : Q.repr = S.repr + 1 := by rw [hQdef]; exact repr_osucc hSnf
  have hPrepr : P.repr = ω ^ Q.repr := by rw [hPdef]; simp [ONote.repr]
  have hαP : α < P := by
    rw [lt_def, hPrepr, hQrepr]
    apply repr_lt_omega_opow_succ hα
    rw [hSrepr]; exact le_self_add
  have heP : e < P := by
    rw [lt_def, hPrepr, hQrepr]
    apply repr_lt_omega_opow_succ he
    rw [hSrepr]; exact le_add_self
  have hQ0 : Q ≠ 0 := by
    intro h
    have h0 : Q.repr = 0 := by rw [h, repr_zero]
    rw [hQrepr] at h0
    exact (lt_of_lt_of_le zero_lt_one le_add_self).ne' h0
  have hβP2 : ∀ m, hardy (oadd Q (Nat.succPNat 1) 0) m = hardy P (hardy P m) := by
    intro m
    rw [hardy_oadd_coeff Q hQ0 1 m]
    show (hardy P)^[1 + 1] m = hardy P (hardy P m)
    rfl
  obtain ⟨N₀, hN₀⟩ := hardy_lt_goodsteinLength hβnf
  refine ⟨max N₀ (max (norm α) (norm e)), fun m hm => ?_⟩
  have hmN₀ : N₀ ≤ m := le_trans (le_max_left _ _) hm
  have hmα : norm α ≤ m := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hm
  have hme : norm e ≤ m := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hm
  have hem : hardy e m ≤ hardy P m := hardy_le_of_lt he hPnf heP hme
  have hαnorm : norm α ≤ hardy e m := le_trans hmα (le_hardy e m)
  calc hardy α (hardy e m)
      ≤ hardy P (hardy e m) := hardy_le_of_lt hα hPnf hαP hαnorm
    _ ≤ hardy P (hardy P m) := hardy_monotone P hem
    _ = hardy (oadd Q (Nat.succPNat 1) 0) m := (hβP2 m).symm
    _ < GoodsteinPA.Dom.goodsteinLength m := hN₀ m hmN₀

/-- **The fully self-contained Goodstein lower bound (Towsner Thm 17.1).**  For every `α.NF` and `k`,
the witness-bounded cut-free calculus cannot derive the Goodstein sentence `gAll` at `(α,k)` — no
hypotheses beyond normal-formhood.  `Hdom` is discharged from the ported Goodstein-dominates-Hardy
chain (carries documented `native_decide` Goodstein base-case axioms). -/
theorem lowerBound_hardy_selfcontained {α : ONote} (hα : α.NF) (k : ℕ) :
    ¬ B α k ({gAll} : Seq) :=
  lowerBound_hardy (Hdom_of_NF hα k)

end GoodsteinPA.LowerBoundHardy
