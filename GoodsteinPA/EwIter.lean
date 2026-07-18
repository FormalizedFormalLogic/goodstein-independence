import GoodsteinPA.OperatorZeh
import GoodsteinPA.Domination

set_option linter.unnecessarySimpa false

namespace GoodsteinPA.OperatorZeh

open ONote
open scoped Ordinal
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

/-! ## The absorbing norm `Nlog` (SERIES-3 N-1 promotion; ruling (1) `ewN → Nlog`)

Promoted from `wip/AbsorbingNormProbe.lean` (Stage D-1, kernel-clean there) +
`wip/NlogGateProbe.lean` (N-0 gate, T-S3 PASS).  `Nlog` is max-over-terms with a logarithmic
coefficient charge: finite-fibered on NF notations (`Nlog_finite_fiber`) AND absorbing
(`Nlog_add_le_max_succ`), which is what dissolves the top-rank-cut node gate
(`absorbing_closes_gate`) without the kernel-refuted base-additivity `hg_base`. -/

/-- Logarithmic coefficient charge: `clog n = ⌊log₂ (n+1)⌋`.  `clog 0 = 0`, `clog 1 = 1`;
finite fibers and sub-max-additive. -/
def clog (n : ℕ) : ℕ := Nat.log 2 (n + 1)

@[simp] theorem clog_zero : clog 0 = 0 := rfl

/-- The merge lemma: `clog (a + b) ≤ max (clog a) (clog b) + 1` — what tames the CNF
coefficient merge `ω^β·a + ω^β·b = ω^β·(a+b)` that makes `ewN` non-absorbing. -/
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

/-- `clog n ≥ 1` for positive `n` — every CNF term charges at least `1`. -/
theorem clog_pos (n : ℕ+) : 1 ≤ clog (n : ℕ) :=
  Nat.log_pos Nat.one_lt_two (by have := n.pos; omega)

/-- Coefficient bound from the log charge: `clog n ≤ K → n < 2^(K+1)`. -/
theorem coe_lt_of_clog_le {n : ℕ+} {K : ℕ} (h : clog (n : ℕ) ≤ K) : (n : ℕ) < 2 ^ (K + 1) := by
  have h1 : (n : ℕ) + 1 < 2 ^ (Nat.log 2 ((n : ℕ) + 1) + 1) :=
    Nat.lt_pow_succ_log_self Nat.one_lt_two _
  have h2 : 2 ^ (Nat.log 2 ((n : ℕ) + 1) + 1) ≤ 2 ^ (K + 1) :=
    Nat.pow_le_pow_right (by norm_num) (by unfold clog at h; omega)
  omega

/-- **The absorbing norm**: max-over-terms with logarithmic coefficient charge.  Contrast
`ewN`, which SUMS the leading charge and the tail. -/
def Nlog : ONote → ℕ
  | 0 => 0
  | oadd e n a => max (Nlog e + clog (n : ℕ)) (Nlog a)

@[simp] theorem Nlog_zero : Nlog 0 = 0 := rfl

@[simp] theorem Nlog_oadd (e : ONote) (n : ℕ+) (a : ONote) :
    Nlog (oadd e n a) = max (Nlog e + clog (n : ℕ)) (Nlog a) := rfl

/-- `{n : ℕ+ | n < B}` is finite. -/
theorem finite_pnat_coe_lt (B : ℕ) : {n : ℕ+ | (n : ℕ) < B}.Finite := by
  have h : {n : ℕ+ | (n : ℕ) < B} = ((↑) : ℕ+ → ℕ) ⁻¹' Set.Iio B := rfl
  rw [h]
  exact (Set.finite_Iio B).preimage PNat.coe_injective.injOn

/-- **Finite fibers of `Nlog` on NF notations** (ruling (1) property (i); the NF restriction is
forced — non-NF flat chains give an infinite `Nlog ≤ 1` ball, see the D-1 probe).  Induction on
`K` with an inner well-founded induction on the `NFBelow` bound ordinal; NF's strict exponent
descent is exactly what the inner induction consumes. -/
theorem Nlog_finite_fiber : ∀ K : ℕ, {α : ONote | NF α ∧ Nlog α ≤ K}.Finite := by
  intro K
  induction K with
  | zero =>
      apply Set.Finite.subset (Set.finite_singleton (0 : ONote))
      rintro α ⟨_, hle⟩
      cases α with
      | zero => exact Set.mem_singleton _
      | oadd e n a =>
          exfalso
          have h1 := clog_pos n
          simp only [Nlog_oadd] at hle
          omega
  | succ K ihK =>
      have inner : ∀ b : Ordinal, {α : ONote | NFBelow α b ∧ Nlog α ≤ K + 1}.Finite := by
        intro b
        induction b using WellFoundedLT.induction with
        | _ b ihb =>
          have hcov : {α : ONote | NFBelow α b ∧ Nlog α ≤ K + 1} ⊆
              insert 0 (⋃ e ∈ {e : ONote | (NF e ∧ Nlog e ≤ K) ∧ ONote.repr e < b},
                ⋃ n ∈ {n : ℕ+ | (n : ℕ) < 2 ^ (K + 2)},
                  (fun a => oadd e n a) ''
                    {a : ONote | NFBelow a (ONote.repr e) ∧ Nlog a ≤ K + 1}) := by
            rintro α ⟨hbel, hle⟩
            cases α with
            | zero => exact Set.mem_insert _ _
            | oadd e n a =>
                refine Set.mem_insert_iff.2 (Or.inr ?_)
                simp only [Nlog_oadd] at hle
                have hc1 := clog_pos n
                simp only [Set.mem_iUnion, Set.mem_image, Set.mem_setOf_eq]
                exact ⟨e, ⟨⟨hbel.fst, by omega⟩, hbel.lt⟩,
                  n, coe_lt_of_clog_le (by omega),
                  a, ⟨hbel.snd, by omega⟩, rfl⟩
          apply Set.Finite.subset _ hcov
          refine Set.Finite.insert 0 ?_
          refine Set.Finite.biUnion (ihK.subset (fun e he => he.1)) ?_
          rintro e ⟨⟨_, _⟩, hlt⟩
          refine Set.Finite.biUnion (finite_pnat_coe_lt _) ?_
          intro n _
          exact (ihb (ONote.repr e) hlt).image _
      apply Set.Finite.subset
        (Set.Finite.insert 0 (Set.Finite.biUnion ihK
          (fun e _ => inner (Order.succ (ONote.repr e)))))
      rintro α ⟨hNF, hle⟩
      cases α with
      | zero => exact Set.mem_insert _ _
      | oadd e n a =>
          refine Set.mem_insert_iff.2 (Or.inr ?_)
          simp only [Nlog_oadd] at hle
          have hc1 := clog_pos n
          simp only [Set.mem_iUnion, Set.mem_setOf_eq]
          exact ⟨e, ⟨hNF.fst, by omega⟩,
            hNF.below_of_lt (Order.lt_succ _), by simp only [Nlog_oadd]; omega⟩

/-- The NF `Nlog`-ball as a `Finset` (the iterate's branch-enumeration domain post-swap). -/
noncomputable def NlogBall (K : ℕ) : Finset ONote := (Nlog_finite_fiber K).toFinset

@[simp] theorem mem_NlogBall {K : ℕ} {o : ONote} :
    o ∈ NlogBall K ↔ NF o ∧ Nlog o ≤ K := Set.Finite.mem_toFinset _

/-- Absorption on `ONote`, packaged: `x + γ = γ` when the reprs absorb. -/
theorem add_eq_right_of_repr {x γ : ONote} [NF x] [NF γ]
    (h : ONote.repr x + ONote.repr γ = ONote.repr γ) : x + γ = γ := by
  haveI : NF (x + γ) := inferInstance
  exact repr_inj.1 (by rw [repr_add]; exact h)

/-- **The general absorbing theorem** (ruling (1) property (ii)):
`Nlog (α+γ) ≤ max (Nlog α) (Nlog γ) + 1` for all NF `α, γ`.  Induct on `α`, trichotomy on the
two leading exponents; the merge case's two `+1`s never compound because `a + γ = γ` absorbs
(`a`'s exponents sit strictly below the shared head). -/
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

/-- **The absorbing node gate** (ruling (1)'s `absorbing_closes_gate`, promoted verbatim from
the D-1 probe): with an absorbing norm the fresh-root gate `N (α+γ) ≤ g (f 0)` closes from the
two premise gates and the weak slack `max (g 0) (f 0) + c ≤ g (f 0)` — NO base-additivity
`hg_base`. -/
theorem absorbing_closes_gate {N : ONote → ℕ} {g f : ℕ → ℕ} (c : ℕ)
    (habs : ∀ α γ, N (α + γ) ≤ max (N α) (N γ) + c)
    (hslack : max (g 0) (f 0) + c ≤ g (f 0))
    {α γ : ONote} (hα : N α ≤ g 0) (hγ : N γ ≤ f 0) :
    N (α + γ) ≤ g (f 0) := by
  have h1 : N (α + γ) ≤ max (N α) (N γ) + c := habs α γ
  have h2 : max (N α) (N γ) ≤ max (g 0) (f 0) := by
    apply max_le
    · exact le_trans hα (le_max_left _ _)
    · exact le_trans hγ (le_max_right _ _)
  omega

/-- The instance form actually consumed at fresh roots: `Nlog`'s absorbing inequality + the
slack close the composed gate. -/
theorem Nlog_add_le_comp {α γ : ONote} {f g : ℕ → ℕ}
    (hαNF : α.NF) (hγNF : γ.NF)
    (hα : Nlog α ≤ g 0) (hγ : Nlog γ ≤ f 0)
    (hslack : max (g 0) (f 0) + 1 ≤ g (f 0)) :
    Nlog (α + γ) ≤ g (f 0) := by
  have habs := Nlog_add_le_max_succ α hαNF γ hγNF
  have hmm : max (Nlog α) (Nlog γ) ≤ max (g 0) (f 0) := max_le_max hα hγ
  omega

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

/-- **The controlled step, post-swap (N-1)**: the branch ball is the NF `Nlog`-ball (the
`ewN → Nlog` substitution image of the ratified `ewStep`; the ball's NF restriction is forced
by `Nlog`'s fiber structure and is the population the calculus feeds anyway). -/
noncomputable def ewStep (f : ℕ → ℕ) (α : ONote) (rec : (β : ONote) → β < α → ℕ → ℕ)
    (m : ℕ) : ℕ :=
  if hα : α = 0 then
    f m
  else
    let K := f (Nlog α + m)
    let vals : Finset ℕ :=
      ((NlogBall K).filter (fun β => β < α ∧ Nlog β ≤ K)).attach.image
        (fun β => rec β.1 (by
            exact (Finset.mem_filter.mp β.2).2.1)
          (rec β.1 (by
            exact (Finset.mem_filter.mp β.2).2.1) m))
    vals.max' (by
      apply Finset.image_nonempty.mpr
      refine ⟨⟨0, ?_⟩, by simp⟩
      simp only [Finset.mem_filter]
      constructor
      · exact mem_NlogBall.mpr ⟨NF.zero, Nat.zero_le _⟩
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

theorem ewIter_lower {f : ℕ → ℕ} {β α : ONote} {m : ℕ} (hβNF : β.NF)
    (hβα : β < α) (hgate : Nlog β ≤ f (Nlog α + m)) :
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
  exact ⟨mem_NlogBall.mpr ⟨hβNF, hgate⟩, hβα, hgate⟩

theorem ewIter_infl {f : ℕ → ℕ} (hf_infl : ∀ m, m ≤ f m) (α : ONote) (m : ℕ) :
    m ≤ ewIter f α m := by
  by_cases hα : α = 0
  · subst hα
    simp [ewIter_zero, hf_infl]
  · have h0α : (0 : ONote) < α := by
      cases α with
      | zero => exact (hα rfl).elim
      | oadd e n a => exact oadd_pos e n a
    have hgate : Nlog (0 : ONote) ≤ f (Nlog α + m) := Nat.zero_le _
    have hlow := ewIter_lower (f := f) (β := 0) (α := α) (m := m) NF.zero h0α hgate
    have hlow' : f (f m) ≤ ewIter f α m := by
      simpa [ewIter_zero] using hlow
    exact le_trans (hf_infl m) (le_trans (hf_infl (f m)) hlow')

/-- **`ewIter` inherits the `2m+1` lower bound** (lap-11 SERIES-1 Stage-4 rung-R prep).  The pass
threads `Monotone ∧ inflationary ∧ (2m+1 ≤ f m)` (`EwLow`, all `rel1`-stable); rung R ITERATES the
pass, so the output slot `ewIter f α` must ITSELF satisfy the same invariant to feed the next pass.
Monotonicity/inflationarity are `ewIter_monotone`/`ewIter_infl`; here is the `2m+1` component —
unlike `EwF1`'s STRICT monotonicity (which `ewIter` does NOT inherit, cf. the trap-8/plateau seam),
the lower-bound floor DOES carry: for `α ≠ 0`, `ewIter f α m ≥ f (f m) ≥ 2·f m + 1 ≥ 2m+1`. -/
theorem ewIter_low {f : ℕ → ℕ} (hf_infl : ∀ m, m ≤ f m) (hf_low : ∀ m, 2 * m + 1 ≤ f m)
    (α : ONote) (m : ℕ) : 2 * m + 1 ≤ ewIter f α m := by
  by_cases hα : α = 0
  · subst hα; simpa [ewIter_zero] using hf_low m
  · have h0α : (0 : ONote) < α := by
      cases α with
      | zero => exact (hα rfl).elim
      | oadd e n a => exact oadd_pos e n a
    have hlow := ewIter_lower (f := f) (β := 0) (α := α) (m := m) NF.zero h0α (Nat.zero_le _)
    have hff : f (f m) ≤ ewIter f α m := by simpa [ewIter_zero] using hlow
    have hfm : m ≤ f m := hf_infl m
    have hlf : 2 * f m + 1 ≤ f (f m) := hf_low (f m)
    omega

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
    have hδNF : (δ : ONote).NF := (mem_NlogBall.mp (Finset.mem_filter.mp δ.2).1).1
    have hδgate : Nlog (δ : ONote) ≤ f (Nlog α + m) := (Finset.mem_filter.mp δ.2).2.2
    have hδgate' : Nlog (δ : ONote) ≤ f (Nlog α + m') :=
      le_trans hδgate (hf_mono (by omega))
    have ihδ : Monotone (ewIter f (δ : ONote)) := ewIter_monotone hf_mono hf_infl δ
    exact le_trans (ihδ (ihδ hmm')) (ewIter_lower (f := f) hδNF hδlt hδgate')
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
    (hβNF : β.NF) (hβα : β < α) (hgate : Nlog β ≤ f (Nlog α + m)) :
    ewIter f β m ≤ ewIter f α m :=
  le_trans (ewIter_infl hf_infl β (ewIter f β m)) (ewIter_lower hβNF hβα hgate)

/-- **Pointwise slot-lift** (lap-10 SERIES-3 pass prep) — at internal pass nodes the IH slot
`ewIter f β` (`β < α`) must be raised to the node slot `ewIter f α` via `Zef2.mono_f`; gated
ordinal-monotonicity gives it pointwise from the base gate `ewN β ≤ f 0`. -/
theorem ewIter_slot_le {f : ℕ → ℕ} (hf_mono : Monotone f) (hf_infl : ∀ m, m ≤ f m)
    {β α : ONote} (hβNF : β.NF) (hβα : β < α) (g : Nlog β ≤ f 0) :
    ∀ x, ewIter f β x ≤ ewIter f α x :=
  fun x => ewIter_le_of_lt (m := x) hf_infl hβNF hβα
    (le_trans g (hf_mono (Nat.zero_le _)))

/-- **Slot-composition containment** (lap-10 SERIES-3 pass prep) — the cut-elimination step merges
two IH-reduced premises' slots `ewIter f α₀ ∘ ewIter f α₁` (`α₀,α₁ < α`) and must fit under the
declared output `ewIter f α`.  Pick δ = the larger of α₀,α₁ (< α); lift both iterates to δ by gated
ordinal-monotonicity (`ewIter_le_of_lt`), giving the two-fold `ewIter f δ (ewIter f δ m)`; then
`ewIter_lower` at δ < α collapses it to the one-fold `ewIter f α m`.  All ball gates follow from the
base gates `ewN αᵢ ≤ f 0` + monotonicity.  CLOSES the slot side of the cut step — no
`EwF1`-of-`rel1` escalation needed.  Kernel-checked in `wip/Lap10PassProbe.lean`. -/
theorem ewIter_comp_le {f : ℕ → ℕ} (hf_mono : Monotone f) (hf_infl : ∀ m, m ≤ f m)
    {α₀ α₁ α : ONote} (hα₀ : α₀.NF) (hα₁ : α₁.NF)
    (h0 : α₀ < α) (h1 : α₁ < α) (g0 : Nlog α₀ ≤ f 0) (g1 : Nlog α₁ ≤ f 0) (m : ℕ) :
    ewIter f α₀ (ewIter f α₁ m) ≤ ewIter f α m := by
  haveI := hα₀; haveI := hα₁
  have gate0 : ∀ k, Nlog α₀ ≤ f (Nlog α + k) := fun k => le_trans g0 (hf_mono (Nat.zero_le _))
  have gate1 : ∀ k, Nlog α₁ ≤ f (Nlog α + k) := fun k => le_trans g1 (hf_mono (Nat.zero_le _))
  rcases lt_trichotomy α₀.repr α₁.repr with hlt | heq | hgt
  · have hα₀α₁ : α₀ < α₁ := lt_def.mpr hlt
    have g01 : Nlog α₀ ≤ f (Nlog α₁ + (ewIter f α₁ m)) := le_trans g0 (hf_mono (Nat.zero_le _))
    exact le_trans (ewIter_le_of_lt hf_infl hα₀ hα₀α₁ g01) (ewIter_lower hα₁ h1 (gate1 m))
  · have hαeq : α₀ = α₁ := repr_inj.mp heq
    subst hαeq
    exact ewIter_lower hα₀ h0 (gate0 m)
  · have hα₁α₀ : α₁ < α₀ := lt_def.mpr hgt
    have g10 : Nlog α₁ ≤ f (Nlog α₀ + m) := le_trans g1 (hf_mono (Nat.zero_le _))
    have hinner : ewIter f α₁ m ≤ ewIter f α₀ m := ewIter_le_of_lt hf_infl hα₁ hα₁α₀ g10
    exact le_trans (ewIter_monotone hf_mono hf_infl α₀ hinner) (ewIter_lower hα₀ h0 (gate0 m))

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
    have hδNF : (δ : ONote).NF := (mem_NlogBall.mp (Finset.mem_filter.mp δ.2).1).1
    have hδgate_branch :
        Nlog (δ : ONote) ≤ rel1 f n (Nlog β + x) := (Finset.mem_filter.mp δ.2).2.2
    have hδgate_parent : Nlog (δ : ONote) ≤ f (Nlog β + max n x) := by
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
      (le_trans (hmonoδ harg) (ewIter_lower (f := f) hδNF hδlt hδgate_parent))
termination_by β
decreasing_by
  all_goals exact hδlt

theorem ewIter_lift_of_mono_infl {f : ℕ → ℕ} (hf_mono : Monotone f)
    (hf_infl : ∀ m, m ≤ f m) {β α : ONote} (hβNF : β.NF)
    (hβα : β < α) (hβN : Nlog β ≤ f 0) :
    ∀ x, ewIter f β x ≤ ewIter f α x := by
  intro x
  have hgate : Nlog β ≤ f (Nlog α + x) :=
    le_trans hβN (hf_mono (Nat.zero_le _))
  exact le_trans (ewIter_infl hf_infl β (ewIter f β x))
    (ewIter_lower (f := f) hβNF hβα hgate)

theorem ewIter_lift {f : ℕ → ℕ} (hf : EwF1 f) {β α : ONote} (hβNF : β.NF)
    (hβα : β < α) (hβN : Nlog β ≤ f 0) :
    ∀ x, ewIter f β x ≤ ewIter f α x :=
  ewIter_lift_of_mono_infl (EwF1.monotone hf) (EwF1.infl hf) hβNF hβα hβN

/-- P1, named as the lap-7 pre-probe. -/
theorem P1_ewIter_lift {f : ℕ → ℕ} (hf : EwF1 f) {β α : ONote} (hβNF : β.NF)
    (hβα : β < α) (hβN : Nlog β ≤ f 0) :
    ∀ x, ewIter f β x ≤ ewIter f α x :=
  ewIter_lift hf hβNF hβα hβN

/-! ## The N-0 kit promoted (attainment, swap lemma, base floor, T-S3 slack)

Promoted from `wip/NlogGateProbe.lean` (kernel-clean there); statements are the probe texts
under the in-place `ewN → Nlog` iterate (the ball gate is now `Nlog`-native). -/

/-- **Max-attainment for `ewIter`** (`α ≠ 0`): the iterate's value is realized by some NF
branch `β < α` inside the ball gate. -/
theorem ewIter_attained {f : ℕ → ℕ} {α : ONote} (hα : α ≠ 0) (x : ℕ) :
    ∃ β : ONote, β.NF ∧ β < α ∧ Nlog β ≤ f (Nlog α + x) ∧
      ewIter f α x = ewIter f β (ewIter f β x) := by
  have hunf := ewIter_unfold f α x
  rw [ewStep] at hunf
  simp only [dif_neg hα] at hunf
  set S := ((NlogBall (f (Nlog α + x))).filter
    (fun β => β < α ∧ Nlog β ≤ f (Nlog α + x))) with hS
  set vals := S.attach.image
    (fun β => ewIter f β.1 (ewIter f β.1 x)) with hvals
  have hne : vals.Nonempty := by
    apply Finset.image_nonempty.mpr
    refine ⟨⟨0, ?_⟩, Finset.mem_attach _ _⟩
    simp only [hS, Finset.mem_filter]
    refine ⟨mem_NlogBall.mpr ⟨NF.zero, Nat.zero_le _⟩, ?_, Nat.zero_le _⟩
    cases α with
    | zero => exact (hα rfl).elim
    | oadd e n a => exact oadd_pos e n a
  have hmem : vals.max' hne ∈ vals := Finset.max'_mem vals hne
  rcases Finset.mem_image.mp hmem with ⟨δ, _, hδval⟩
  have hδfilter := Finset.mem_filter.mp δ.2
  refine ⟨δ.1, (mem_NlogBall.mp hδfilter.1).1, hδfilter.2.1, hδfilter.2.2, ?_⟩
  rw [hunf, ← hδval]

/-- **THE SWAP LEMMA** (N-0's structural insight): `ewIter` commutes one-sidedly with its own
slot, `s (ewIter s α x) ≤ ewIter s α (s x)`, for every Monotone + inflationary `s` and EVERY
`α`.  An argument bump BY A SLOT APPLICATION always gains a slot application on the value —
even across `ewIter`'s plateaus (this is what replaces the kernel-refuted `hg_base`). -/
theorem ewIter_swap {s : ℕ → ℕ} (hmono : Monotone s) (hinfl : ∀ m, m ≤ s m)
    (α : ONote) (x : ℕ) : s (ewIter s α x) ≤ ewIter s α (s x) := by
  by_cases hα : α = 0
  · subst hα; simp [ewIter_zero]
  · obtain ⟨β, hβNF, hβlt, hβgate, heq⟩ := ewIter_attained hα x
    rw [heq]
    have ih1 : s (ewIter s β (ewIter s β x)) ≤ ewIter s β (s (ewIter s β x)) :=
      ewIter_swap hmono hinfl β (ewIter s β x)
    have ih2 : s (ewIter s β x) ≤ ewIter s β (s x) :=
      ewIter_swap hmono hinfl β x
    have hmβ : Monotone (ewIter s β) := ewIter_monotone hmono hinfl β
    have hgate' : Nlog β ≤ s (Nlog α + s x) :=
      le_trans hβgate (hmono (by have := hinfl x; omega))
    exact le_trans ih1 (le_trans (hmβ ih2) (ewIter_lower hβNF hβlt hgate'))
termination_by α
decreasing_by all_goals exact hβlt

/-- The base floor `s 0 ≤ ewIter s β 0`, ALL `β`. -/
theorem ewIter_base_le {s : ℕ → ℕ} (hinfl : ∀ m, m ≤ s m) (β : ONote) :
    s 0 ≤ ewIter s β 0 := by
  by_cases hβ : β = 0
  · subst hβ; simp [ewIter_zero]
  · have h0β : (0 : ONote) < β := by
      cases β with
      | zero => exact (hβ rfl).elim
      | oadd e n a => exact oadd_pos e n a
    have hlow := ewIter_lower (f := s) (β := 0) (α := β) (m := 0) NF.zero h0β (Nat.zero_le _)
    have hss : s (s 0) ≤ ewIter s β 0 := by simpa [ewIter_zero] using hlow
    exact le_trans (hinfl (s 0)) hss

/-- **T-S3 (N-0, PASSED): the cut-node slack** — for the threaded kit and ARBITRARY
`βφ, βψ` (edges included): `max (g 0) (f 0) + 1 ≤ g (f 0)` with `g = ewIter s βφ`,
`f = ewIter s βψ`.  `f`-arm by `ewIter_low`; `g`-arm by monotone + swap + EwLow. -/
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

/-- **The slot-threaded slack** (the reduction's replacement for the kernel-refuted
`hg_base`): the T-S3 slack holds not just at `f 0` but at every `k ≥ f 0` — this is the
form the running-family reduction threads down its `rel1` re-entries (slot bases only grow).
Same three ingredients: `ewIter_low` for the `k`-arm, monotone + swap + EwLow for the
`g`-arm. -/
theorem hslack_kit_ge {s : ℕ → ℕ} (hmono : Monotone s) (hinfl : ∀ m, m ≤ s m)
    (hlow : ∀ m, 2 * m + 1 ≤ s m) (βφ βψ : ONote) :
    ∀ k, ewIter s βψ 0 ≤ k →
      max (ewIter s βφ 0) k + 1 ≤ ewIter s βφ k := by
  intro k hk
  have hkarm : 2 * k + 1 ≤ ewIter s βφ k := ewIter_low hinfl hlow βφ k
  have hs0f : s 0 ≤ k := le_trans (ewIter_base_le hinfl βψ) hk
  have hgmono : Monotone (ewIter s βφ) := ewIter_monotone hmono hinfl βφ
  have hswap : s (ewIter s βφ 0) ≤ ewIter s βφ (s 0) := ewIter_swap hmono hinfl βφ 0
  have hgarm : 2 * ewIter s βφ 0 + 1 ≤ ewIter s βφ k :=
    le_trans (hlow (ewIter s βφ 0)) (le_trans hswap (hgmono hs0f))
  omega

end GoodsteinPA.OperatorZeh
