import GoodsteinPA.OperatorZef2

/-!
# SERIES-3 N-0 — T-S3 ENTRY GATE: the cut-node slack over the absorbing norm `Nlog`

**Question (the HARD gate; no src swap until this passes).**  Ruling (1) adopts the absorbing
norm `Nlog` in place of `ewN` as `Zef2`'s gate norm; `absorbing_closes_gate` then closes the
reduction's fresh-root node `N (α+γ) ≤ g (f 0)` from the two premise gates PROVIDED the slack

    hslack : max (g 0) (f 0) + c ≤ g (f 0)      (c = 1 for `Nlog`)

holds at the actual cut node, where `g = ewIter s βφ`, `f = ewIter s βψ` and `s` is the pass's
threaded slot (`Monotone` + inflationary + EwLow `2m+1 ≤ s m`).  The judge flagged the edges
`βφ, βψ ∈ {0, 1}`: "`βψ = 0` gives `f 0 = 0` and hslack degenerates to `g 0 + c ≤ g 0` (false)"
— a real worry for a GENERIC `f`, and plateau slots stress the `g`-arm the same way the refuted
`hg_base` did (`ewIter` is NOT strictly monotone, trap-8).

**This probe DISCHARGES hslack uniformly — all `βφ, βψ`, edges included, NO case split.**
Two structural facts do it:

1. `f 0 = ewIter s βψ 0 ≥ s 0 ≥ 1` — the EwLow floor makes the flagged `f 0 = 0` edge
   VACUOUS (`βψ = 0` gives `f 0 = s 0 ≥ 2·0+1 = 1`; `βψ ≠ 0` gives `f 0 ≥ s (s 0)`, more).
2. **The swap lemma** (`ewIter_swap`, the new structural insight):

       s (ewIter s α x) ≤ ewIter s α (s x)

   for every Monotone + inflationary `s` and EVERY `α` — proved by well-founded recursion on
   `α` through the max-attainment of `ewStep` (`ewIter_attained`).  It converts the `g`-arm's
   needed strict gain into low-bound arithmetic WITHOUT strict monotonicity:
   `g (f 0) ≥ g (s 0) ≥ s (g 0) ≥ 2·(g 0) + 1 > g 0` — the plateau obstruction dissolves
   because the argument bump `0 → f 0 ≥ s 0` is itself a slot application, and `ewIter`
   commutes (one-sidedly) with its own slot.

Deliverables (all kernel-checked, no `native_decide`, no new axioms):
  * `ewIter_attained` — the `ewStep` max is attained on a gated branch (reusable for N-1);
  * `ewIter_swap` — the swap lemma;
  * `ewIter_base_le`, `kit_f0_pos` — the edge-vacuity floors;
  * `hslack_kit` — **T-S3 PASSES**: `max (g 0) (f 0) + 1 ≤ g (f 0)` for the threaded kit,
    unconditional in `βφ, βψ` (explicit edge corollaries `hslack_kit_edge_*`);
  * `Nlog` kit (copied verbatim from `wip/AbsorbingNormProbe.lean`, the D-1 probe — wip files
    are standalone, so the promoted-to-src copy in N-1 is the deduplication point):
    `clog_add_le`, `Nlog_add_le_max_succ` (the absorbing theorem, NF);
  * `Nlog_collapse`, `Nlog_collapse_le` — the per-node gate analogs of
    `ewN_collapse`/`ewN_collapse_le` (the pass's node gates over `Nlog`);
  * `ewIterTower_monotone/_infl/_low` + `Nlog_collapseIter_le` — the Def-16 iterate/tower gate
    (rung R's per-pass node gate over `Nlog`);
  * `Nlog_add_le_comp_kit` — the pins-1–2 fresh-root gate at the ACTUAL kit slots, closed by
    the absorbing arithmetic alone (NO `hg_base`);
  * `MiniZ` + `mini_axL` + `mini_axL_fresh_root` — the pins-1–2 miniature: an `Nlog`-gated axL
    node and its rebuilt fresh root `α + γ` at slot `g ∘ f`.

This is **wip-only gate evidence** (SERIES-3 order N-0).  Nothing here touches `src`.
-/

namespace GoodsteinPA.NlogGateProbe

open ONote
open scoped Ordinal
open GoodsteinPA.OperatorZeh

/-! ## Part 1 — the swap lemma and the slack

### Attainment: the `ewStep` max is realized on a gated branch -/

/-- **Max-attainment for `ewIter`** (`α ≠ 0`): the iterate's value is realized by some branch
`β < α` inside the ball gate.  Extracted from `ewStep`'s `Finset.max'` via `Finset.max'_mem`.
This is the primitive the swap lemma recurses through (and is reusable for any future
lower-bound analysis of `ewIter`). -/
theorem ewIter_attained {f : ℕ → ℕ} {α : ONote} (hα : α ≠ 0) (x : ℕ) :
    ∃ β : ONote, β < α ∧ ewN β ≤ f (ewN α + x) ∧
      ewIter f α x = ewIter f β (ewIter f β x) := by
  have hunf := ewIter_unfold f α x
  rw [ewStep] at hunf
  simp only [dif_neg hα] at hunf
  set S := ((ewBall (f (ewN α + x))).filter
    (fun β => β < α ∧ ewN β ≤ f (ewN α + x))) with hS
  set vals := S.attach.image
    (fun β => ewIter f β.1 (ewIter f β.1 x)) with hvals
  have hne : vals.Nonempty := by
    apply Finset.image_nonempty.mpr
    refine ⟨⟨0, ?_⟩, Finset.mem_attach _ _⟩
    simp only [hS, Finset.mem_filter]
    refine ⟨mem_ewBall_of_ewN_le 0 (Nat.zero_le _), ?_, Nat.zero_le _⟩
    cases α with
    | zero => exact (hα rfl).elim
    | oadd e n a => exact oadd_pos e n a
  have hmem : vals.max' hne ∈ vals := Finset.max'_mem vals hne
  rcases Finset.mem_image.mp hmem with ⟨δ, _, hδval⟩
  have hδfilter := Finset.mem_filter.mp δ.2
  refine ⟨δ.1, hδfilter.2.1, hδfilter.2.2, ?_⟩
  rw [hunf, ← hδval]

/-- **THE SWAP LEMMA** — `ewIter` commutes one-sidedly with its own slot:
`s (ewIter s α x) ≤ ewIter s α (s x)` for every Monotone + inflationary `s` and EVERY `α`
(including `α = 0`, where it is equality `s (s x) = s (s x)`).

This is the structural fact that replaces strict monotonicity in the cut-node slack: an
argument bump BY A SLOT APPLICATION always gains at least a slot application on the value —
even across `ewIter`'s plateaus.  Proof: well-founded recursion on `α` through the attained
maximizing branch `β < α`: `s (ewIter s β (ewIter s β x)) ≤ ewIter s β (s (ewIter s β x))
≤ ewIter s β (ewIter s β (s x)) ≤ ewIter s α (s x)` (IH twice, then `ewIter_lower` with the
gate transported by `x ≤ s x`). -/
theorem ewIter_swap {s : ℕ → ℕ} (hmono : Monotone s) (hinfl : ∀ m, m ≤ s m)
    (α : ONote) (x : ℕ) : s (ewIter s α x) ≤ ewIter s α (s x) := by
  by_cases hα : α = 0
  · subst hα; simp [ewIter_zero]
  · obtain ⟨β, hβlt, hβgate, heq⟩ := ewIter_attained hα x
    rw [heq]
    have ih1 : s (ewIter s β (ewIter s β x)) ≤ ewIter s β (s (ewIter s β x)) :=
      ewIter_swap hmono hinfl β (ewIter s β x)
    have ih2 : s (ewIter s β x) ≤ ewIter s β (s x) :=
      ewIter_swap hmono hinfl β x
    have hmβ : Monotone (ewIter s β) := ewIter_monotone hmono hinfl β
    have hgate' : ewN β ≤ s (ewN α + s x) :=
      le_trans hβgate (hmono (by have := hinfl x; omega))
    exact le_trans ih1 (le_trans (hmβ ih2) (ewIter_lower hβlt hgate'))
termination_by α
decreasing_by all_goals exact hβlt

/-! ### The edge floors: `ewIter s β 0 ≥ s 0 ≥ 1` -/

/-- The base floor `s 0 ≤ ewIter s β 0`, ALL `β` (at `β = 0` it is equality). -/
theorem ewIter_base_le {s : ℕ → ℕ} (hinfl : ∀ m, m ≤ s m) (β : ONote) :
    s 0 ≤ ewIter s β 0 := by
  by_cases hβ : β = 0
  · subst hβ; simp [ewIter_zero]
  · have h0β : (0 : ONote) < β := by
      cases β with
      | zero => exact (hβ rfl).elim
      | oadd e n a => exact oadd_pos e n a
    have hlow := ewIter_lower (f := s) (β := 0) (α := β) (m := 0) h0β (Nat.zero_le _)
    have hss : s (s 0) ≤ ewIter s β 0 := by simpa [ewIter_zero] using hlow
    exact le_trans (hinfl (s 0)) hss

/-- **The judge's flagged edge is VACUOUS**: `f 0 = ewIter s βψ 0 ≥ 1` for every `βψ`
(including `βψ = 0`) once the pass's EwLow floor is threaded — `f 0 = 0` never occurs. -/
theorem kit_f0_pos {s : ℕ → ℕ} (hinfl : ∀ m, m ≤ s m) (hlow : ∀ m, 2 * m + 1 ≤ s m)
    (βψ : ONote) : 1 ≤ ewIter s βψ 0 :=
  le_trans (by have := hlow 0; omega) (ewIter_base_le hinfl βψ)

/-! ### T-S3: the slack — uniform in `βφ, βψ`, no case split -/

/-- **T-S3 ENTRY GATE — PASSES (direct form).**  For the threaded kit (`s` Monotone +
inflationary + EwLow) and ARBITRARY `βφ, βψ` (edges `0, 1` included):

    max (g 0) (f 0) + 1 ≤ g (f 0),   g = ewIter s βφ,  f = ewIter s βψ.

`f`-arm: `g (f 0) ≥ 2·(f 0) + 1` (`ewIter_low`).  `g`-arm: `g (f 0) ≥ g (s 0)` (monotone,
`f 0 ≥ s 0` by `ewIter_base_le`) `≥ s (g 0)` (**swap lemma**) `≥ 2·(g 0) + 1` (EwLow). -/
theorem hslack_kit {s : ℕ → ℕ} (hmono : Monotone s) (hinfl : ∀ m, m ≤ s m)
    (hlow : ∀ m, 2 * m + 1 ≤ s m) (βφ βψ : ONote) :
    max (ewIter s βφ 0) (ewIter s βψ 0) + 1
      ≤ ewIter s βφ (ewIter s βψ 0) := by
  have hfarm : 2 * ewIter s βψ 0 + 1 ≤ ewIter s βφ (ewIter s βψ 0) :=
    ewIter_low hinfl hlow βφ (ewIter s βψ 0)
  have hs0f : s 0 ≤ ewIter s βψ 0 := ewIter_base_le hinfl βψ
  have hgmono : Monotone (ewIter s βφ) := ewIter_monotone hmono hinfl βφ
  have hswap : s (ewIter s βφ 0) ≤ ewIter s βφ (s 0) := ewIter_swap hmono hinfl βφ 0
  have hgarm : 2 * ewIter s βφ 0 + 1 ≤ ewIter s βφ (ewIter s βψ 0) :=
    le_trans (hlow (ewIter s βφ 0)) (le_trans hswap (hgmono hs0f))
  omega

/-- Edge `βφ = 0, βψ = 0`: `hslack` at the doubly-degenerate corner (`g = f = s`),
`max (s 0) (s 0) + 1 ≤ s (s 0)` — explicit corollary documenting the judge's edge. -/
theorem hslack_kit_edge_00 {s : ℕ → ℕ} (hmono : Monotone s) (hinfl : ∀ m, m ≤ s m)
    (hlow : ∀ m, 2 * m + 1 ≤ s m) :
    max (ewIter s 0 0) (ewIter s 0 0) + 1 ≤ ewIter s 0 (ewIter s 0 0) :=
  hslack_kit hmono hinfl hlow 0 0

/-- Edge `βψ = 0` (the flagged one), arbitrary `βφ`. -/
theorem hslack_kit_edge_psi0 {s : ℕ → ℕ} (hmono : Monotone s) (hinfl : ∀ m, m ≤ s m)
    (hlow : ∀ m, 2 * m + 1 ≤ s m) (βφ : ONote) :
    max (ewIter s βφ 0) (ewIter s 0 0) + 1 ≤ ewIter s βφ (ewIter s 0 0) :=
  hslack_kit hmono hinfl hlow βφ 0

/-- Edge `βφ = 1, βψ = 1`. -/
theorem hslack_kit_edge_11 {s : ℕ → ℕ} (hmono : Monotone s) (hinfl : ∀ m, m ≤ s m)
    (hlow : ∀ m, 2 * m + 1 ≤ s m) :
    max (ewIter s 1 0) (ewIter s 1 0) + 1 ≤ ewIter s 1 (ewIter s 1 0) :=
  hslack_kit hmono hinfl hlow 1 1

/-! ## Part 2 — the `Nlog` kit (verbatim copy of the D-1 probe's ratified-by-construction
definitions; N-1 promotes these to src, which is the deduplication point) -/

/-- Logarithmic coefficient charge: `clog n = ⌊log₂ (n+1)⌋`. -/
def clog (n : ℕ) : ℕ := Nat.log 2 (n + 1)

@[simp] theorem clog_zero : clog 0 = 0 := rfl

/-- The merge lemma: `clog (a + b) ≤ max (clog a) (clog b) + 1`. -/
theorem clog_add_le (a b : ℕ) : clog (a + b) ≤ max (clog a) (clog b) + 1 := by
  unfold clog
  have hmono : Nat.log 2 (a + b + 1) ≤ Nat.log 2 ((max a b + 1) * 2) := by
    apply Nat.log_mono_right
    have ha : a ≤ max a b := le_max_left _ _
    have hb : b ≤ max a b := le_max_right _ _
    omega
  have hstep : Nat.log 2 ((max a b + 1) * 2) = Nat.log 2 (max a b + 1) + 1 :=
    Nat.log_mul_base Nat.one_lt_two (by omega)
  have hmax : Nat.log 2 (max a b + 1) ≤ max (Nat.log 2 (a + 1)) (Nat.log 2 (b + 1)) := by
    rcases le_total a b with h | h
    · rw [Nat.max_eq_right h]; exact le_max_right _ _
    · rw [Nat.max_eq_left h]; exact le_max_left _ _
  omega

/-- `clog n ≥ 1` for positive `n`. -/
theorem clog_pos (n : ℕ+) : 1 ≤ clog (n : ℕ) :=
  Nat.log_pos Nat.one_lt_two (by have := n.pos; omega)

/-- The absorbing norm: max-over-terms with logarithmic coefficient charge. -/
def Nlog : ONote → ℕ
  | 0 => 0
  | oadd e n a => max (Nlog e + clog (n : ℕ)) (Nlog a)

@[simp] theorem Nlog_zero : Nlog 0 = 0 := rfl

@[simp] theorem Nlog_oadd (e : ONote) (n : ℕ+) (a : ONote) :
    Nlog (oadd e n a) = max (Nlog e + clog (n : ℕ)) (Nlog a) := rfl

/-- Absorption on `ONote`, packaged (copy of the D-1 probe helper). -/
theorem add_eq_right_of_repr {x γ : ONote} [NF x] [NF γ]
    (h : ONote.repr x + ONote.repr γ = ONote.repr γ) : x + γ = γ := by
  haveI : NF (x + γ) := inferInstance
  exact repr_inj.1 (by rw [repr_add]; exact h)

/-- **The general absorbing theorem** (verbatim from the D-1 probe, kernel-clean there):
`Nlog (α+γ) ≤ max (Nlog α) (Nlog γ) + 1` for all NF `α, γ`. -/
theorem Nlog_add_le_max_succ : ∀ (α : ONote), NF α → ∀ (γ : ONote), NF γ →
    Nlog (α + γ) ≤ max (Nlog α) (Nlog γ) + 1 := by
  intro α
  induction α with
  | zero =>
      intro _ γ _
      show Nlog γ ≤ max (Nlog ONote.zero) (Nlog γ) + 1
      have : Nlog γ ≤ max (Nlog ONote.zero) (Nlog γ) := le_max_right _ _
      omega
  | oadd e n a _ihe iha =>
      intro hα γ hγ
      haveI := hα
      haveI := hγ
      haveI hNFe : NF e := hα.fst
      haveI hNFa : NF a := hα.snd
      have hab : NFBelow a (ONote.repr e) := hα.snd'
      cases γ with
      | zero =>
          have hz : oadd e n a + ONote.zero = oadd e n a := by
            apply repr_inj.1
            rw [repr_add]; simp
          rw [hz]
          have : Nlog (oadd e n a) ≤ max (Nlog (oadd e n a)) (Nlog ONote.zero) :=
            le_max_left _ _
          omega
      | oadd eg ng ag =>
          haveI hNFeg : NF eg := hγ.fst
          haveI hNFag : NF ag := hγ.snd
          have hagb : NFBelow ag (ONote.repr eg) := hγ.snd'
          rcases lt_trichotomy (ONote.repr e) (ONote.repr eg) with hlt | heq | hgt
          · have hαbelow : NFBelow (oadd e n a) (ONote.repr eg) := NF.below_of_lt hlt hα
            have hform : oadd e n a + oadd eg ng ag = oadd eg ng ag :=
              add_eq_right_of_repr
                (Ordinal.add_of_omega0_opow_le hαbelow.repr_lt (omega0_le_oadd eg ng ag))
            rw [hform]
            have : Nlog (oadd eg ng ag) ≤ max (Nlog (oadd e n a)) (Nlog (oadd eg ng ag)) :=
              le_max_right _ _
            omega
          · have hee : e = eg := repr_inj.1 heq
            subst hee
            haveI : NF (oadd e (n + ng) ag) := NF.oadd hNFe (n + ng) hagb
            have hform : oadd e n a + oadd e ng ag = oadd e (n + ng) ag := by
              apply repr_inj.1
              rw [repr_add]
              simp only [ONote.repr, PNat.add_coe, Nat.cast_add, mul_add]
              have hng : (0 : Ordinal) < ((ng : ℕ) : Ordinal) := by exact_mod_cast ng.pos
              have habsorb : ONote.repr a + ω ^ ONote.repr e * ((ng : ℕ) : Ordinal)
                  = ω ^ ONote.repr e * ((ng : ℕ) : Ordinal) :=
                Ordinal.add_of_omega0_opow_le hab.repr_lt (Ordinal.le_mul_left _ hng)
              rw [add_assoc, ← add_assoc (ONote.repr a), habsorb, ← add_assoc]
            rw [hform, Nlog_oadd, Nlog_oadd, Nlog_oadd]
            have hcoeN : (((n + ng : ℕ+) : ℕ)) = ((n : ℕ)) + ((ng : ℕ)) := by
              push_cast; ring
            rw [hcoeN]
            have hcl := clog_add_le (n : ℕ) (ng : ℕ)
            have e1 : Nlog e + clog (n : ℕ) ≤ max (Nlog e + clog (n : ℕ)) (Nlog a) :=
              le_max_left _ _
            have e2 : Nlog e + clog (ng : ℕ) ≤ max (Nlog e + clog (ng : ℕ)) (Nlog ag) :=
              le_max_left _ _
            have e3 : Nlog ag ≤ max (Nlog e + clog (ng : ℕ)) (Nlog ag) := le_max_right _ _
            apply max_le
            · have b1 : Nlog e + clog (n : ℕ)
                  ≤ max (max (Nlog e + clog (n:ℕ)) (Nlog a))
                      (max (Nlog e + clog (ng:ℕ)) (Nlog ag)) :=
                le_trans e1 (le_max_left _ _)
              have b2 : Nlog e + clog (ng : ℕ)
                  ≤ max (max (Nlog e + clog (n:ℕ)) (Nlog a))
                      (max (Nlog e + clog (ng:ℕ)) (Nlog ag)) :=
                le_trans e2 (le_max_right _ _)
              omega
            · have b3 : Nlog ag
                  ≤ max (max (Nlog e + clog (n:ℕ)) (Nlog a))
                      (max (Nlog e + clog (ng:ℕ)) (Nlog ag)) :=
                le_trans e3 (le_max_right _ _)
              omega
          · have hγbelow : NFBelow (oadd eg ng ag) (ONote.repr e) := NF.below_of_lt hgt hγ
            haveI hNFaγ : NF (a + oadd eg ng ag) := inferInstance
            have haγ_below : NFBelow (a + oadd eg ng ag) (ONote.repr e) := by
              apply NF.below_of_lt' _ hNFaγ
              rw [repr_add]
              exact Ordinal.isPrincipal_add_omega0_opow (ONote.repr e) hab.repr_lt
                hγbelow.repr_lt
            haveI : NF (oadd e n (a + oadd eg ng ag)) := NF.oadd hNFe n haγ_below
            have hform : oadd e n a + oadd eg ng ag = oadd e n (a + oadd eg ng ag) := by
              apply repr_inj.1
              simp only [repr_add, ONote.repr]
              exact add_assoc _ _ _
            rw [hform, Nlog_oadd, Nlog_oadd]
            have hIH : Nlog (a + oadd eg ng ag) ≤ max (Nlog a) (Nlog (oadd eg ng ag)) + 1 :=
              iha hNFa (oadd eg ng ag) hγ
            have hA : Nlog e + clog (n : ℕ) ≤ max (Nlog e + clog (n:ℕ)) (Nlog a) :=
              le_max_left _ _
            have hAa : Nlog a ≤ max (Nlog e + clog (n:ℕ)) (Nlog a) := le_max_right _ _
            apply max_le
            · have : Nlog e + clog (n:ℕ)
                  ≤ max (max (Nlog e + clog (n:ℕ)) (Nlog a)) (Nlog (oadd eg ng ag)) :=
                le_trans hA (le_max_left _ _)
              omega
            · have hb1 : Nlog a
                  ≤ max (max (Nlog e + clog (n:ℕ)) (Nlog a)) (Nlog (oadd eg ng ag)) :=
                le_trans hAa (le_max_left _ _)
              have hb2 : Nlog (oadd eg ng ag)
                  ≤ max (max (Nlog e + clog (n:ℕ)) (Nlog a)) (Nlog (oadd eg ng ag)) :=
                le_max_right _ _
              omega

/-! ### The per-node gates over `Nlog` (analogs of `ewN_collapse`/`ewN_collapse_le`) -/

/-- `Nlog (collapse α) = Nlog α + 1` (`collapse α = oadd α 1 0`, `clog 1 = 1`) — the exact
analog of `ewN_collapse`. -/
theorem Nlog_collapse (α : ONote) : Nlog (collapse α) = Nlog α + 1 := by
  show Nlog (oadd α 1 0) = Nlog α + 1
  have hc : clog 1 = 1 := by decide
  simp [Nlog_oadd, hc]

/-- **Per-node gate for the pass over `Nlog`** — the analog of `ewN_collapse_le`: the rebuilt
node at `collapse α` with slot `ewIter f α` closes its `Nlog` gate from the derivation's base
gate `Nlog α ≤ f 0` + the EwLow floor.  Same `f (f 0)` mechanism; only `hlow`, no strictness,
so it survives the `allω` branches' `rel1 f n` slots. -/
theorem Nlog_collapse_le {f : ℕ → ℕ} (hlow : ∀ m, 2 * m + 1 ≤ f m) {α : ONote}
    (hgate : Nlog α ≤ f 0) : Nlog (collapse α) ≤ ewIter f α 0 := by
  rw [Nlog_collapse]
  by_cases hα : α = 0
  · subst hα
    simp only [Nlog_zero, ewIter_zero]
    have := hlow 0; omega
  · have h0α : (0 : ONote) < α := by
      cases α with
      | zero => exact (hα rfl).elim
      | oadd e n a => exact oadd_pos e n a
    have hlow' := ewIter_lower (f := f) (β := 0) (α := α) (m := 0) h0α (Nat.zero_le _)
    have hff : f (f 0) ≤ ewIter f α 0 := by simpa [ewIter_zero] using hlow'
    have hb : 2 * f 0 + 1 ≤ f (f 0) := hlow (f 0)
    omega

/-! ### The Def-16 iterate/tower gate over `Nlog` (rung R's per-pass node gates) -/

/-- The tower slot preserves inflationarity. -/
theorem ewIterTower_infl {f : ℕ → ℕ} (hmono : Monotone f) (hinfl : ∀ m, m ≤ f m)
    (α : ONote) : ∀ d, ∀ m, m ≤ ewIterTower f d α m
  | 0 => hinfl
  | (d + 1) => ewIter_infl (ewIterTower_infl hmono hinfl α d) _

/-- The tower slot preserves monotonicity. -/
theorem ewIterTower_monotone {f : ℕ → ℕ} (hmono : Monotone f) (hinfl : ∀ m, m ≤ f m)
    (α : ONote) : ∀ d, Monotone (ewIterTower f d α)
  | 0 => hmono
  | (d + 1) => ewIter_monotone (ewIterTower_monotone hmono hinfl α d)
      (ewIterTower_infl hmono hinfl α d) _

/-- The tower slot preserves the EwLow floor. -/
theorem ewIterTower_low {f : ℕ → ℕ} (hmono : Monotone f) (hinfl : ∀ m, m ≤ f m)
    (hlow : ∀ m, 2 * m + 1 ≤ f m) (α : ONote) :
    ∀ d, ∀ m, 2 * m + 1 ≤ ewIterTower f d α m
  | 0 => hlow
  | (d + 1) => ewIter_low (ewIterTower_infl hmono hinfl α d)
      (ewIterTower_low hmono hinfl hlow α d) _

/-- **The Def-16 tower gate over `Nlog`** — rung R's per-pass node gate iterates: `d` passes
carry the base gate `Nlog α ≤ f 0` to `Nlog (collapseIter d α) ≤ ewIterTower f d α 0`
(each step is one `Nlog_collapse_le` at the current tower slot). -/
theorem Nlog_collapseIter_le {f : ℕ → ℕ} (hmono : Monotone f) (hinfl : ∀ m, m ≤ f m)
    (hlow : ∀ m, 2 * m + 1 ≤ f m) {α : ONote} (hgate : Nlog α ≤ f 0) :
    ∀ d, Nlog (collapseIter d α) ≤ ewIterTower f d α 0
  | 0 => hgate
  | (d + 1) =>
      Nlog_collapse_le (ewIterTower_low hmono hinfl hlow α d)
        (Nlog_collapseIter_le hmono hinfl hlow hgate d)

/-! ## Part 3 — the pins-1–2 miniature over `Nlog`: the fresh-root gate closes with the
absorbing arithmetic alone (NO `hg_base`) -/

/-- **The fresh-root gate at the ACTUAL kit slots** — the `Nlog` replacement of
`ewN_add_le_comp`: premise gates `Nlog α ≤ g 0`, `Nlog γ ≤ f 0` (with `g = ewIter s βφ`,
`f = ewIter s βψ`) close the fresh root `Nlog (α + γ) ≤ g (f 0)` via the absorbing theorem +
`hslack_kit`.  This is `absorbing_closes_gate` instantiated end-to-end: the node gate the
top-rank cut synthesizes, with NO base-additivity hypothesis anywhere. -/
theorem Nlog_add_le_comp_kit {s : ℕ → ℕ} (hmono : Monotone s) (hinfl : ∀ m, m ≤ s m)
    (hlow : ∀ m, 2 * m + 1 ≤ s m) {βφ βψ α γ : ONote} (hαNF : α.NF) (hγNF : γ.NF)
    (hα : Nlog α ≤ ewIter s βφ 0) (hγ : Nlog γ ≤ ewIter s βψ 0) :
    Nlog (α + γ) ≤ ewIter s βφ (ewIter s βψ 0) := by
  have habs := Nlog_add_le_max_succ α hαNF γ hγNF
  have hsl := hslack_kit hmono hinfl hlow βφ βψ
  have hmm : max (Nlog α) (Nlog γ) ≤ max (ewIter s βφ 0) (ewIter s βψ 0) :=
    max_le_max hα hγ
  omega

/-- The pins-1–2 miniature calculus: a single `Nlog`-gated axL node (the gate discipline of
`Zef2.axL`, norm swapped). -/
inductive MiniZ : ONote → (ℕ → ℕ) → GoodsteinPA.OperatorZinfty.Seq → Prop
  | axL {α : ONote} {f : ℕ → ℕ} {Γ : GoodsteinPA.OperatorZinfty.Seq} {ar : ℕ}
      (hαN : Nlog α ≤ f 0)
      (r : (LO.FirstOrder.Language.oRing).Rel ar) (v)
      (hp : LO.FirstOrder.Semiformula.rel r v ∈ Γ)
      (hn : LO.FirstOrder.Semiformula.nrel r v ∈ Γ) : MiniZ α f Γ

/-- Miniature axL case: an `Nlog`-gated leaf builds exactly as in `Zef2` (the gate is the only
obligation and it is the hypothesis). -/
theorem mini_axL {α : ONote} {f : ℕ → ℕ} {Γ : GoodsteinPA.OperatorZinfty.Seq} {ar : ℕ}
    (hαN : Nlog α ≤ f 0)
    (r : (LO.FirstOrder.Language.oRing).Rel ar) (v)
    (hp : LO.FirstOrder.Semiformula.rel r v ∈ Γ)
    (hn : LO.FirstOrder.Semiformula.nrel r v ∈ Γ) : MiniZ α f Γ :=
  MiniZ.axL hαN r v hp hn

/-- **Miniature fresh-root case** — the reduction's synthesized root `α + γ` at the composed
slot `g ∘ f` (`g = ewIter s βφ`, `f = ewIter s βψ`) rebuilds an axL leaf with its `Nlog` gate
closed by `Nlog_add_le_comp_kit`: the pins-1–2 arithmetic over the absorbing norm, end-to-end,
with no `hg_base`. -/
theorem mini_axL_fresh_root {s : ℕ → ℕ} (hmono : Monotone s) (hinfl : ∀ m, m ≤ s m)
    (hlow : ∀ m, 2 * m + 1 ≤ s m) {βφ βψ α γ : ONote} (hαNF : α.NF) (hγNF : γ.NF)
    (hα : Nlog α ≤ ewIter s βφ 0) (hγ : Nlog γ ≤ ewIter s βψ 0)
    {Γ : GoodsteinPA.OperatorZinfty.Seq} {ar : ℕ}
    (r : (LO.FirstOrder.Language.oRing).Rel ar) (v)
    (hp : LO.FirstOrder.Semiformula.rel r v ∈ Γ)
    (hn : LO.FirstOrder.Semiformula.nrel r v ∈ Γ) :
    MiniZ (α + γ) (ewIter s βφ ∘ ewIter s βψ) Γ :=
  MiniZ.axL (Nlog_add_le_comp_kit hmono hinfl hlow hαNF hγNF hα hγ) r v hp hn

end GoodsteinPA.NlogGateProbe
