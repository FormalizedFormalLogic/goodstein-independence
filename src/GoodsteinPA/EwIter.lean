import GoodsteinPA.OperatorZeh
import GoodsteinPA.Domination

set_option linter.unnecessarySimpa false

namespace GoodsteinPA.OperatorZeh

open ONote
open GoodsteinPA.FastGrowing

/-!
# The Eguchi–Weiermann controlled iterate (`ewIter`), ported to `src` (lap 8)

Port of the ratified lap-7 wip layer (`wip/EwIter.lean`, freeze reference).  The source `norm`
is the CNF max-coefficient norm, whose fibers are infinite on the tower spine, so the gated max
below uses `ewN`, a constructor norm with finite fibers.

The P2/P3 native-decide instance probes stay in `wip/EwIter.lean` (evidence artifacts); `src`
stays anchor-free.  Everything below is the reusable iterate machinery + the P1 lift lemma.
-/

/-- Constructor norm for finite E-W gates on `ONote`.  Numerals keep their usual size, while
every nonzero CNF constructor contributes the sizes of its components. -/
def ewN : ONote → ℕ
  | 0 => 0
  | oadd e n a => ewN e + (n : ℕ) + ewN a

@[simp] theorem ewN_zero : ewN 0 = 0 := rfl

@[simp] theorem ewN_oadd (e : ONote) (n : ℕ+) (a : ONote) :
    ewN (oadd e n a) = ewN e + (n : ℕ) + ewN a := rfl

/-- All `ONote`s with constructor norm at most `K`. -/
def ewBall : ℕ → Finset ONote
  | 0 => {0}
  | K + 1 =>
      ewBall K ∪
        ((ewBall K).product ((Finset.range (K + 1)).product (ewBall K))).image
          (fun p => oadd p.1 ⟨p.2.1 + 1, Nat.succ_pos _⟩ p.2.2)

theorem mem_ewBall_of_ewN_le : ∀ {K : ℕ} (o : ONote), ewN o ≤ K → o ∈ ewBall K := by
  intro K
  induction K with
  | zero =>
      intro o ho
      cases o with
      | zero => simp [ewBall]
      | oadd e n a =>
          simp only [ewN_oadd] at ho
          have hn : 1 ≤ (n : ℕ) := n.pos
          omega
  | succ K ih =>
      intro o ho
      by_cases hprev : ewN o ≤ K
      · exact Finset.mem_union_left _ (ih o hprev)
      · cases o with
        | zero =>
            exact (hprev (by simp [ewN])).elim
        | oadd e n a =>
            apply Finset.mem_union_right
            apply Finset.mem_image.mpr
            refine ⟨(e, (n.natPred, a)), ?_, ?_⟩
            · simp [Finset.mem_product]
              have hsum : ewN e + (n : ℕ) + ewN a ≤ K + 1 := by
                simpa only [ewN_oadd] using ho
              have hn : 1 ≤ (n : ℕ) := n.pos
              constructor
              · exact ih e (by omega)
              constructor
              · have hn_eq : (n : ℕ) = n.natPred + 1 := by
                  simpa using congrArg (fun q : ℕ+ => (q : ℕ)) (PNat.succPNat_natPred n).symm
                omega
              · exact ih a (by omega)
            · congr 1
              apply PNat.coe_injective
              simpa using congrArg (fun q : ℕ+ => (q : ℕ)) (PNat.succPNat_natPred n).symm

def EwF1 (f : ℕ → ℕ) : Prop :=
  StrictMono f ∧ ∀ m, 2 * m + 1 ≤ f m

def EwF2 (f : ℕ → ℕ) : Prop :=
  ∀ m, 2 * f m ≤ f (f m)

theorem EwF1.monotone {f : ℕ → ℕ} (hf : EwF1 f) : Monotone f :=
  hf.1.monotone

theorem EwF1.infl {f : ℕ → ℕ} (hf : EwF1 f) : ∀ m, m ≤ f m :=
  fun m => le_trans (by omega) (hf.2 m)

/-- **Base-additive composite** (lap-10 SERIES-1 R-0(ii), the `noOsucc_closes` pattern).  With the
judge's `α + γ` reduction output (no successor `+1`), a per-step growth floor `g 0 + k ≤ g k` on the
`∀`-side slot converts the two additive input gates into the composed-slot base gate: any
`a ≤ g 0`, `b ≤ f 0` give `a + b ≤ g (f 0)`.  Kernel-checked in `wip/Lap10SeamProbe.lean`; the
`ewN`-level composite `ewN (α+γ) ≤ g (f 0)` (via `ewN_add_le`) is `OperatorZef2.ewN_add_le_comp`. -/
theorem base_add_le_comp {f g : ℕ → ℕ} (hg_base : ∀ k, g 0 + k ≤ g k) {a b : ℕ}
    (ha : a ≤ g 0) (hb : b ≤ f 0) : a + b ≤ g (f 0) := by
  have := hg_base (f 0); omega

noncomputable def ewStep (f : ℕ → ℕ) (α : ONote) (rec : (β : ONote) → β < α → ℕ → ℕ)
    (m : ℕ) : ℕ :=
  if hα : α = 0 then
    f m
  else
    let K := f (ewN α + m)
    let vals : Finset ℕ :=
      ((ewBall K).filter (fun β => β < α ∧ ewN β ≤ K)).attach.image
        (fun β => rec β.1 (by
            exact (Finset.mem_filter.mp β.2).2.1)
          (rec β.1 (by
            exact (Finset.mem_filter.mp β.2).2.1) m))
    vals.max' (by
      apply Finset.image_nonempty.mpr
      refine ⟨⟨0, ?_⟩, by simp⟩
      simp only [Finset.mem_filter]
      constructor
      · exact mem_ewBall_of_ewN_le 0 (Nat.zero_le _)
      · constructor
        · cases α with
          | zero => exact (hα rfl).elim
          | oadd e n a => exact oadd_pos e n a
        · exact Nat.zero_le _)

noncomputable def ewIter (f : ℕ → ℕ) : ONote → ℕ → ℕ
  | α => fun m => ewStep f α (fun β _ => ewIter f β) m
termination_by α => α
decreasing_by
  exact ‹_›

theorem ewIter_unfold (f : ℕ → ℕ) (α : ONote) (m : ℕ) :
    ewIter f α m = ewStep f α (fun β _ => ewIter f β) m := by
  rw [ewIter]

@[simp] theorem ewIter_zero (f : ℕ → ℕ) : ewIter f 0 = f := by
  funext m
  rw [ewIter_unfold, ewStep]
  simp

theorem ewIter_lower {f : ℕ → ℕ} {β α : ONote} {m : ℕ}
    (hβα : β < α) (hgate : ewN β ≤ f (ewN α + m)) :
    ewIter f β (ewIter f β m) ≤ ewIter f α m := by
  have hαne : α ≠ 0 := by
    intro h
    subst h
    have hrepr := lt_def.1 hβα
    rw [repr_zero] at hrepr
    exact (not_lt_of_ge (show (0 : Ordinal) ≤ β.repr from zero_le) hrepr).elim
  conv_rhs => rw [ewIter_unfold f α m]
  rw [ewStep]
  simp only [dif_neg hαne]
  apply Finset.le_max'
  apply Finset.mem_image.mpr
  refine ⟨⟨β, ?_⟩, by simp, rfl⟩
  simp only [Finset.mem_filter]
  exact ⟨mem_ewBall_of_ewN_le β hgate, hβα, hgate⟩

theorem ewIter_infl {f : ℕ → ℕ} (hf_infl : ∀ m, m ≤ f m) (α : ONote) (m : ℕ) :
    m ≤ ewIter f α m := by
  by_cases hα : α = 0
  · subst hα
    simp [ewIter_zero, hf_infl]
  · have h0α : (0 : ONote) < α := by
      cases α with
      | zero => exact (hα rfl).elim
      | oadd e n a => exact oadd_pos e n a
    have hgate : ewN (0 : ONote) ≤ f (ewN α + m) := Nat.zero_le _
    have hlow := ewIter_lower (f := f) (β := 0) (α := α) (m := m) h0α hgate
    have hlow' : f (f m) ≤ ewIter f α m := by
      simpa [ewIter_zero] using hlow
    exact le_trans (hf_infl m) (le_trans (hf_infl (f m)) hlow')

theorem ewIter_monotone {f : ℕ → ℕ} (hf_mono : Monotone f) (hf_infl : ∀ m, m ≤ f m)
    (α : ONote) : Monotone (ewIter f α) := by
  intro m m' hmm'
  by_cases hα : α = 0
  · subst hα
    simpa [ewIter_zero] using hf_mono hmm'
  · conv_lhs => rw [ewIter_unfold f α m]
    rw [ewStep]
    simp only [dif_neg hα]
    apply Finset.max'_le
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨δ, hδmem, rfl⟩
    have hδlt : (δ : ONote) < α := (Finset.mem_filter.mp δ.2).2.1
    have hδgate : ewN (δ : ONote) ≤ f (ewN α + m) := (Finset.mem_filter.mp δ.2).2.2
    have hδgate' : ewN (δ : ONote) ≤ f (ewN α + m') :=
      le_trans hδgate (hf_mono (by omega))
    have ihδ : Monotone (ewIter f (δ : ONote)) := ewIter_monotone hf_mono hf_infl δ
    exact le_trans (ihδ (ihδ hmm')) (ewIter_lower (f := f) hδlt hδgate')
termination_by α
decreasing_by
  exact hδlt

/-- **Gated ordinal-monotonicity of `ewIter`** (lap-10 SERIES-1 Stage-3 pass prep).  The property
trap-8 refuted for the bare `iterSlot` but which the ewN GATE restores for `ewIter`: for `β < α`
with the ball gate `ewN β ≤ f (ewN α + m)`, the smaller-ordinal iterate is dominated by the larger,
`ewIter f β m ≤ ewIter f α m` (inflate once, then `ewIter_lower`).  This is what un-walls the pass's
slot side — the cut-elimination step composes iterates at DIFFERENT ordinals `< α`, and this lemma
lifts each to the common `α`.  Kernel-checked in `wip/Lap10PassProbe.lean`. -/
theorem ewIter_le_of_lt {f : ℕ → ℕ} (hf_infl : ∀ m, m ≤ f m) {β α : ONote} {m : ℕ}
    (hβα : β < α) (hgate : ewN β ≤ f (ewN α + m)) :
    ewIter f β m ≤ ewIter f α m :=
  le_trans (ewIter_infl hf_infl β (ewIter f β m)) (ewIter_lower hβα hgate)

/-- **Slot-composition containment** (lap-10 SERIES-3 pass prep) — the cut-elimination step merges
two IH-reduced premises' slots `ewIter f α₀ ∘ ewIter f α₁` (`α₀,α₁ < α`) and must fit under the
declared output `ewIter f α`.  Pick δ = the larger of α₀,α₁ (< α); lift both iterates to δ by gated
ordinal-monotonicity (`ewIter_le_of_lt`), giving the two-fold `ewIter f δ (ewIter f δ m)`; then
`ewIter_lower` at δ < α collapses it to the one-fold `ewIter f α m`.  All ball gates follow from the
base gates `ewN αᵢ ≤ f 0` + monotonicity.  CLOSES the slot side of the cut step — no
`EwF1`-of-`rel1` escalation needed.  Kernel-checked in `wip/Lap10PassProbe.lean`. -/
theorem ewIter_comp_le {f : ℕ → ℕ} (hf_mono : Monotone f) (hf_infl : ∀ m, m ≤ f m)
    {α₀ α₁ α : ONote} (hα₀ : α₀.NF) (hα₁ : α₁.NF)
    (h0 : α₀ < α) (h1 : α₁ < α) (g0 : ewN α₀ ≤ f 0) (g1 : ewN α₁ ≤ f 0) (m : ℕ) :
    ewIter f α₀ (ewIter f α₁ m) ≤ ewIter f α m := by
  haveI := hα₀; haveI := hα₁
  have gate0 : ∀ k, ewN α₀ ≤ f (ewN α + k) := fun k => le_trans g0 (hf_mono (Nat.zero_le _))
  have gate1 : ∀ k, ewN α₁ ≤ f (ewN α + k) := fun k => le_trans g1 (hf_mono (Nat.zero_le _))
  rcases lt_trichotomy α₀.repr α₁.repr with hlt | heq | hgt
  · have hα₀α₁ : α₀ < α₁ := lt_def.mpr hlt
    have g01 : ewN α₀ ≤ f (ewN α₁ + (ewIter f α₁ m)) := le_trans g0 (hf_mono (Nat.zero_le _))
    exact le_trans (ewIter_le_of_lt hf_infl hα₀α₁ g01) (ewIter_lower h1 (gate1 m))
  · have hαeq : α₀ = α₁ := repr_inj.mp heq
    subst hαeq
    exact ewIter_lower h0 (gate0 m)
  · have hα₁α₀ : α₁ < α₀ := lt_def.mpr hgt
    have g10 : ewN α₁ ≤ f (ewN α₀ + m) := le_trans g1 (hf_mono (Nat.zero_le _))
    have hinner : ewIter f α₁ m ≤ ewIter f α₀ m := ewIter_le_of_lt hf_infl hα₁α₀ g10
    exact le_trans (ewIter_monotone hf_mono hf_infl α₀ hinner) (ewIter_lower h0 (gate0 m))

theorem ewIter_rel1_le {f : ℕ → ℕ} (hf_mono : Monotone f) (hf_infl : ∀ m, m ≤ f m)
    (β : ONote) (n x : ℕ) :
    ewIter (rel1 f n) β x ≤ ewIter f β (max n x) := by
  by_cases hβ : β = 0
  · subst hβ
    simp [ewIter_zero, rel1]
  · conv_lhs => rw [ewIter_unfold (rel1 f n) β x]
    rw [ewStep]
    simp only [dif_neg hβ]
    apply Finset.max'_le
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨δ, hδmem, rfl⟩
    have hδlt : (δ : ONote) < β := (Finset.mem_filter.mp δ.2).2.1
    have hδgate_branch :
        ewN (δ : ONote) ≤ rel1 f n (ewN β + x) := (Finset.mem_filter.mp δ.2).2.2
    have hδgate_parent : ewN (δ : ONote) ≤ f (ewN β + max n x) := by
      refine le_trans hδgate_branch (hf_mono ?_)
      omega
    have ih_arg :
        ewIter (rel1 f n) (δ : ONote) (ewIter (rel1 f n) (δ : ONote) x) ≤
          ewIter f (δ : ONote) (max n (ewIter (rel1 f n) (δ : ONote) x)) :=
      ewIter_rel1_le hf_mono hf_infl (δ : ONote) n (ewIter (rel1 f n) (δ : ONote) x)
    have ih_x :
        ewIter (rel1 f n) (δ : ONote) x ≤ ewIter f (δ : ONote) (max n x) :=
      ewIter_rel1_le hf_mono hf_infl (δ : ONote) n x
    have harg :
        max n (ewIter (rel1 f n) (δ : ONote) x) ≤ ewIter f (δ : ONote) (max n x) := by
      have hn : n ≤ ewIter f (δ : ONote) (max n x) :=
        le_trans (le_max_left n x) (ewIter_infl hf_infl (δ : ONote) (max n x))
      exact max_le hn ih_x
    have hmonoδ := ewIter_monotone hf_mono hf_infl (δ : ONote)
    exact le_trans ih_arg
      (le_trans (hmonoδ harg) (ewIter_lower (f := f) hδlt hδgate_parent))
termination_by β
decreasing_by
  all_goals exact hδlt

theorem ewIter_lift_of_mono_infl {f : ℕ → ℕ} (hf_mono : Monotone f)
    (hf_infl : ∀ m, m ≤ f m) {β α : ONote}
    (hβα : β < α) (hβN : ewN β ≤ f 0) :
    ∀ x, ewIter f β x ≤ ewIter f α x := by
  intro x
  have hgate : ewN β ≤ f (ewN α + x) :=
    le_trans hβN (hf_mono (Nat.zero_le _))
  exact le_trans (ewIter_infl hf_infl β (ewIter f β x)) (ewIter_lower (f := f) hβα hgate)

theorem ewIter_lift {f : ℕ → ℕ} (hf : EwF1 f) {β α : ONote}
    (hβα : β < α) (hβN : ewN β ≤ f 0) :
    ∀ x, ewIter f β x ≤ ewIter f α x :=
  ewIter_lift_of_mono_infl (EwF1.monotone hf) (EwF1.infl hf) hβα hβN

/-- P1, named as the lap-7 pre-probe. -/
theorem P1_ewIter_lift {f : ℕ → ℕ} (hf : EwF1 f) {β α : ONote}
    (hβα : β < α) (hβN : ewN β ≤ f 0) :
    ∀ x, ewIter f β x ≤ ewIter f α x :=
  ewIter_lift hf hβα hβN

end GoodsteinPA.OperatorZeh
