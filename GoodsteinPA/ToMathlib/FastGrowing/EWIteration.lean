/-
# Eguchi–Weiermann iteration on `ONote`

The max-relativization `rel1`, the exponential collapse `expTower`/`collapse`, the controlled
iteration `ewIter`, and the `d`-fold collapse/slot towers (`collapseIter`/`ewIterTower`).
-/
module

public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Tactic.Ring
public import GoodsteinPA.ToMathlib.Hardy

@[expose] public section

namespace ONote

open Ordinal

/-- A nonzero `ONote` is positive. -/
lemma pos_of_ne_zero {α : ONote} (h : α ≠ 0) : (0 : ONote) < α := by
  cases α with
  | zero => exact (h rfl).elim
  | oadd e n a => exact oadd_pos e n a

/-- `ω^α` as an explicit `ONote` (`oadd α 1 0`). -/
def expTower (α : ONote) : ONote := oadd α 1 0

lemma expTower_NF {α : ONote} (hα : α.NF) : (expTower α).NF :=
  hα.oadd 1 NFBelow.zero

lemma expTower_lt_expTower {β α : ONote} (hβ : β.NF) (h : β < α) :
    expTower β < expTower α :=
  oadd_lt_oadd_1 (expTower_NF hβ) h

/-- The Eguchi–Weiermann max-relativization of a number-theoretic operator. -/
def rel1 (f : ℕ → ℕ) (n : ℕ) : ℕ → ℕ := fun x => f (max n x)

/-- **The reassembly algebra:** `rel1 (f ∘ g) n = f ∘ rel1 g n` (definitionally). -/
lemma rel1_comp (f g : ℕ → ℕ) (n : ℕ) : rel1 (f ∘ g) n = f ∘ rel1 g n := rfl

/-- `rel1` is monotone in the slot (feeds `NormControlled.mono` at ω-nodes). -/
lemma rel1_mono {f f' : ℕ → ℕ} (hff' : ∀ x, f x ≤ f' x) (n : ℕ) :
    ∀ x, rel1 f n x ≤ rel1 f' n x := fun x => hff' (max n x)

/-- `rel1 f n` inherits monotonicity from `f`. -/
lemma rel1_monotone {f : ℕ → ℕ} (hf : Monotone f) (n : ℕ) : Monotone (rel1 f n) :=
  fun _ _ h => hf (max_le_max (le_refl n) h)

/-- `rel1 f n` inherits inflationarity from `f` (`x ≤ rel1 f n x`). -/
lemma rel1_infl {f : ℕ → ℕ} (hf : ∀ x, x ≤ f x) (n : ℕ) : ∀ x, x ≤ rel1 f n x :=
  fun x => le_trans (le_max_right n x) (hf (max n x))

/-- **`rel1` preserves the `2m+1` lower bound:** `2·m + 1 ≤ rel1 f n m` whenever
`2·m + 1 ≤ f m`. -/
lemma rel1_low {f : ℕ → ℕ} (hmono : Monotone f) (hlow : ∀ m, 2 * m + 1 ≤ f m) (n : ℕ) :
    ∀ m, 2 * m + 1 ≤ rel1 f n m :=
  fun m => le_trans (hlow m) (hmono (le_max_right n m))

/-- **Max-associativity:** `rel1 (rel1 f m) n = rel1 f (max m n)`. -/
lemma rel1_rel1 (f : ℕ → ℕ) (m n : ℕ) : rel1 (rel1 f m) n = rel1 f (max m n) := by
  funext x
  simp only [rel1]
  rw [max_assoc]

/-- **`collapse`:** the single-rank height map `α ↦ ω^α`. -/
def collapse (α : ONote) : ONote := expTower α

/-- `collapse` is NF-preserving (so the assembly can splice at NF ordinals). -/
lemma collapse_NF {α : ONote} (hα : α.NF) : (collapse α).NF := expTower_NF hα

/-- **`collapse` is strictly monotone:** `β < α → collapse β < collapse α`. -/
lemma collapse_strictMono {β α : ONote} (hβ : β.NF) (h : β < α) : collapse β < collapse α :=
  expTower_lt_expTower hβ h

/-!
# The Eguchi–Weiermann controlled iterate `ewIter`

The gated iteration uses `ewN` (constructor norm with finite fibers) since the CNF norm has
infinite fibers on the tower spine.
-/

/-- **Constructor norm with finite fibers:** numerals keep their usual size,
nonzero CNF constructors contribute the sizes of their components. -/
def ewN : ONote → ℕ
  | 0 => 0
  | oadd e n a => ewN e + (n : ℕ) + ewN a

@[simp] theorem ewN_zero : ewN 0 = 0 := rfl

@[simp] theorem ewN_oadd (e : ONote) (n : ℕ+) (a : ONote) :
    ewN (oadd e n a) = ewN e + (n : ℕ) + ewN a := rfl

/-! ## The absorbing norm `Nlog`

Max-over-terms with logarithmic coefficient charge: finite-fibered and absorbing
(dissolves the top-rank-cut node gate without base-additivity).
-/

/-- **Logarithmic coefficient charge:** `clog n = ⌊log₂ (n+1)⌋`. -/
def clog (n : ℕ) : ℕ := Nat.log 2 (n + 1)

@[simp] theorem clog_zero : clog 0 = 0 := rfl

/-- **The merge lemma:** `clog (a + b) ≤ max (clog a) (clog b) + 1`. -/
lemma clog_add_le (a b : ℕ) : clog (a + b) ≤ max (clog a) (clog b) + 1 := by
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
lemma clog_pos (n : ℕ+) : 1 ≤ clog (n : ℕ) :=
  Nat.log_pos Nat.one_lt_two (by have := n.pos; omega)

/-- Coefficient bound from the log charge: `clog n ≤ K → n < 2^(K+1)`. -/
lemma coe_lt_of_clog_le {n : ℕ+} {K : ℕ} (h : clog (n : ℕ) ≤ K) : (n : ℕ) < 2 ^ (K + 1) := by
  have h1 : (n : ℕ) + 1 < 2 ^ (Nat.log 2 ((n : ℕ) + 1) + 1) :=
    Nat.lt_pow_succ_log_self Nat.one_lt_two _
  have h2 : 2 ^ (Nat.log 2 ((n : ℕ) + 1) + 1) ≤ 2 ^ (K + 1) :=
    Nat.pow_le_pow_right (by norm_num) (by unfold clog at h; omega)
  omega

/-- `2·⌈log⌉` is dominated by the argument (+3): `2·log₂(m+1) ≤ m+3`. -/
lemma two_mul_clog_le (m : ℕ) : 2 * clog m ≤ m + 3 := by
  have hkey : ∀ k : ℕ, 2 * k ≤ 2 ^ k + 2 := by
    intro k
    induction k with
    | zero => omega
    | succ k ih =>
        have h2 : 2 ^ k ≥ 1 := Nat.one_le_two_pow
        have : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by ring
        omega
  have hpow : 2 ^ Nat.log 2 (m + 1) ≤ m + 1 := Nat.pow_log_le_self 2 (by omega)
  have := hkey (Nat.log 2 (m + 1))
  simp only [clog]
  omega

/-- **`clog` submultiplicativity:** `clog (a·b) ≤ clog a + clog b + 1`. -/
lemma clog_mul_le (a b : ℕ) : clog (a * b) ≤ clog a + clog b + 1 := by
  rcases Nat.eq_zero_or_pos a with ha | ha
  · subst ha; simp
  rcases Nat.eq_zero_or_pos b with hb | hb
  · subst hb; simp
  have h1 : a + 1 < 2 ^ (clog a + 1) := by
    simpa [clog] using Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (a + 1)
  have h2 : b + 1 < 2 ^ (clog b + 1) := by
    simpa [clog] using Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (b + 1)
  have hle : a * b + 1 < 2 ^ (clog a + 1) * 2 ^ (clog b + 1) := by
    have hexp : (a + 1) * (b + 1) = a * b + a + b + 1 := by ring
    have : a * b + 1 ≤ (a + 1) * (b + 1) := by omega
    exact lt_of_le_of_lt this (Nat.mul_lt_mul'' h1 h2)
  rw [← pow_add] at hle
  have hfin : clog (a * b) < clog a + 1 + (clog b + 1) := by
    simpa [clog] using Nat.log_lt_of_lt_pow (by omega : a * b + 1 ≠ 0) hle
  omega

/-- **The absorbing norm:** max-over-terms with logarithmic coefficient charge. -/
def Nlog : ONote → ℕ
  | 0 => 0
  | oadd e n a => max (Nlog e + clog (n : ℕ)) (Nlog a)

@[simp] theorem Nlog_zero : Nlog 0 = 0 := rfl

@[simp] theorem Nlog_oadd (e : ONote) (n : ℕ+) (a : ONote) :
    Nlog (oadd e n a) = max (Nlog e + clog (n : ℕ)) (Nlog a) := rfl

/-- `{n : ℕ+ | n < B}` is finite. -/
lemma finite_pnat_coe_lt (B : ℕ) : {n : ℕ+ | (n : ℕ) < B}.Finite := by
  have h : {n : ℕ+ | (n : ℕ) < B} = ((↑) : ℕ+ → ℕ) ⁻¹' Set.Iio B := rfl
  rw [h]
  exact (Set.finite_Iio B).preimage PNat.coe_injective.injOn

/-- **Finite fibers of `Nlog` on NF notations** (NF restriction is forced). -/
theorem Nlog_finite_fiber (K : ℕ) : {α : ONote | NF α ∧ Nlog α ≤ K}.Finite := by
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
lemma add_eq_right_of_repr {x γ : ONote} [NF x] [NF γ]
    (h : ONote.repr x + ONote.repr γ = ONote.repr γ) : x + γ = γ := by
  haveI : NF (x + γ) := inferInstance
  exact repr_inj.1 (by rw [repr_add]; exact h)

/-- **The general absorbing theorem:** `Nlog (α+γ) ≤ max (Nlog α) (Nlog γ) + 1` for NF `α, γ`. -/
theorem Nlog_add_le_max_succ (α : ONote) (hα : NF α) (γ : ONote) (hγ : NF γ) :
    Nlog (α + γ) ≤ max (Nlog α) (Nlog γ) + 1 := by
  induction α generalizing γ with
  | zero =>
      show Nlog γ ≤ max (Nlog ONote.zero) (Nlog γ) + 1
      have : Nlog γ ≤ max (Nlog ONote.zero) (Nlog γ) := le_max_right _ _
      omega
  | oadd e n a _ihe iha =>
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

/-- **The absorbing node gate:** with an absorbing norm, `N (α+γ) ≤ g (f 0)` closes
from the two premise gates and the slack condition without base-additivity. -/
lemma absorbing_closes_gate {N : ONote → ℕ} {g f : ℕ → ℕ} (c : ℕ)
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

/-- **Instance for fresh roots:** `Nlog`'s absorbing inequality and the slack close
the composed gate. -/
lemma Nlog_add_le_comp {α γ : ONote} {f g : ℕ → ℕ}
    (hαNF : α.NF) (hγNF : γ.NF)
    (hα : Nlog α ≤ g 0) (hγ : Nlog γ ≤ f 0)
    (hslack : max (g 0) (f 0) + 1 ≤ g (f 0)) :
    Nlog (α + γ) ≤ g (f 0) := by
  have habs := Nlog_add_le_max_succ α hαNF γ hγNF
  have hmm : max (Nlog α) (Nlog γ) ≤ max (g 0) (f 0) := max_le_max hα hγ
  omega

/-! ## `ω` as an `ONote` -/

/-- `ω` (`ONote.omega`) is the closure element `expTower (ofNat 1)`. -/
lemma omega_eq_expTower : (ONote.omega : ONote) = expTower (ONote.ofNat 1) := rfl

lemma omega_NF : (ONote.omega : ONote).NF := by
  rw [omega_eq_expTower]; exact expTower_NF (ONote.nf_ofNat 1)

/-- Every numeral `ONote.ofNat m` lies strictly below `ω`. -/
lemma ofNat_lt_omega (m : ℕ) : ONote.ofNat m < ONote.omega := by
  rw [ONote.lt_def, ONote.repr_ofNat,
    show ONote.omega.repr = Ordinal.omega0 from by simp [ONote.omega]]
  exact Ordinal.natCast_lt_omega0 m

lemma Nlog_omega : Nlog ONote.omega = 2 := by
  show Nlog (ONote.oadd 1 1 0) = 2
  have h2 : Nat.log 2 2 = 1 := by decide
  show max (Nlog (1 : ONote) + clog 1) (Nlog 0) = 2
  have h1 : Nlog (1 : ONote) = 1 := by
    show max (Nlog 0 + clog 1) (Nlog 0) = 1
    simp [clog, h2]
  simp [h1, clog, h2]

/-! ## `osucc` interaction with `Nlog` and `collapse` -/

/-- `Nlog` is near-stable under `osucc` (mirror of `ewN_osucc_le`). -/
lemma Nlog_osucc_le : ∀ {o : ONote}, o.NF → Nlog (osucc o) ≤ Nlog o + 1
  | 0, _ => by
      show Nlog (oadd 0 1 0) ≤ Nlog 0 + 1
      simp only [Nlog_oadd, Nlog_zero, PNat.one_coe]
      have : clog 1 = 1 := by decide
      omega
  | oadd 0 n a, h => by
      have ha0 : a = 0 := by
        have hlt : a.repr < ω ^ (0 : ONote).repr := h.snd'.repr_lt
        rw [ONote.repr_zero, Ordinal.opow_zero] at hlt
        exact (@ONote.repr_inj a 0 h.snd ONote.NF.zero).1
          (by rw [ONote.repr_zero]; exact Order.lt_one_iff.1 hlt)
      subst ha0
      show Nlog (oadd 0 (n + 1) 0) ≤ Nlog (oadd 0 n 0) + 1
      have hadd := clog_add_le (n : ℕ) 1
      have hpos := clog_pos n
      have h1 : clog 1 = 1 := by decide
      simp only [Nlog_oadd, Nlog_zero, PNat.add_coe, PNat.one_coe, Nat.zero_add]
      omega
  | oadd (oadd e' n' a') m b, h => by
      show Nlog (oadd (oadd e' n' a') m (osucc b)) ≤ Nlog (oadd (oadd e' n' a') m b) + 1
      have hIH := Nlog_osucc_le h.snd
      simp only [Nlog_oadd] at hIH ⊢
      omega

/-- `osuccs α n` is the `n`-fold iterate of `osucc` applied to `α`. -/
def osuccs (α : ONote) : ℕ → ONote
  | 0 => α
  | n + 1 => osucc (osuccs α n)

lemma osuccs_NF {α : ONote} (h : α.NF) : ∀ n, (osuccs α n).NF
  | 0 => h
  | n + 1 => osucc_NF (osuccs_NF h n)

lemma osuccs_succ_shift (α : ONote) : ∀ n, osuccs (osucc α) n = osucc (osuccs α n)
  | 0 => rfl
  | n + 1 => by simp only [osuccs, osuccs_succ_shift α n]

lemma Nlog_osuccs_le {α : ONote} (h : α.NF) : ∀ n, Nlog (osuccs α n) ≤ Nlog α + n
  | 0 => le_refl _
  | n + 1 => by
      have h1 := Nlog_osucc_le (osuccs_NF h n)
      have h2 := Nlog_osuccs_le h n
      simp only [osuccs]
      omega

/-- Successor headroom under the collapse: `collapse α = ω^α` is a limit for `α > 0`, so
`σ < collapse α → osucc σ < collapse α` (additive principality with `1 < ω^α`). -/
lemma osucc_lt_collapse {σ α : ONote} (hσNF : σ.NF) (_hαNF : α.NF)
    (hαpos : (0 : ONote) < α) (h : σ < collapse α) : osucc σ < collapse α := by
  haveI := hσNF; haveI := _hαNF
  have hrepr_collapse : ∀ x : ONote, (collapse x).repr = ω ^ x.repr := fun x => by
    simp [collapse, expTower, ONote.repr]
  refine ONote.lt_def.mpr ?_
  rw [repr_osucc hσNF, hrepr_collapse]
  have h1 : σ.repr < Ordinal.omega0 ^ α.repr := by
    have := ONote.lt_def.mp h
    rwa [hrepr_collapse] at this
  have h0 : (0 : Ordinal) < α.repr := by simpa using ONote.lt_def.mp hαpos
  have h2 : (1 : Ordinal) < Ordinal.omega0 ^ α.repr :=
    lt_of_lt_of_le Ordinal.one_lt_omega0 (Ordinal.left_le_opow _ h0)
  exact Ordinal.isPrincipal_add_omega0_opow α.repr h1 h2

def EwF1 (f : ℕ → ℕ) : Prop :=
  StrictMono f ∧ ∀ m, 2 * m + 1 ≤ f m

def EwF2 (f : ℕ → ℕ) : Prop :=
  ∀ m, 2 * f m ≤ f (f m)

lemma EwF1.monotone {f : ℕ → ℕ} (hf : EwF1 f) : Monotone f :=
  hf.1.monotone

lemma EwF1.infl {f : ℕ → ℕ} (hf : EwF1 f) : ∀ m, m ≤ f m :=
  fun m => le_trans (by omega) (hf.2 m)

/-- **Base-additive composite.** A per-step growth floor `g 0 + k ≤ g k` on the `∀`-side
slot converts the two additive input gates into the composed-slot base gate: any
`a ≤ g 0`, `b ≤ f 0` give `a + b ≤ g (f 0)`. The `ewN`-level composite
`ewN (α+γ) ≤ g (f 0)` (via `ewN_add_le`) is `OperatorZef2.ewN_add_le_comp`. -/
lemma base_add_le_comp {f g : ℕ → ℕ} (hg_base : ∀ k, g 0 + k ≤ g k) {a b : ℕ}
    (ha : a ≤ g 0) (hb : b ≤ f 0) : a + b ≤ g (f 0) := by
  have := hg_base (f 0); omega

/-- **The controlled step**: the branch ball is the NF `Nlog`-ball, whose NF restriction is
forced by `Nlog`'s fiber structure and is the population the calculus feeds anyway. -/
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
      and_intros
      · exact mem_NlogBall.mpr ⟨NF.zero, Nat.zero_le _⟩
      · exact pos_of_ne_zero hα
      · exact Nat.zero_le _)

noncomputable def ewIter (f : ℕ → ℕ) : ONote → ℕ → ℕ
  | α => fun m => ewStep f α (fun β _ => ewIter f β) m
termination_by α => α
decreasing_by
  exact ‹_›

lemma ewIter_unfold (f : ℕ → ℕ) (α : ONote) (m : ℕ) :
    ewIter f α m = ewStep f α (fun β _ => ewIter f β) m := by
  rw [ewIter]

@[simp] theorem ewIter_zero (f : ℕ → ℕ) : ewIter f 0 = f := by
  funext m
  rw [ewIter_unfold, ewStep]
  simp

variable {f : ℕ → ℕ} {α β : ONote} {m x : ℕ}

lemma ewIter_lower (hβNF : β.NF)
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

lemma ewIter_infl {f : ℕ → ℕ} (hf_infl : ∀ m, m ≤ f m) (α : ONote) (m : ℕ) :
    m ≤ ewIter f α m := by
  by_cases hα : α = 0
  · subst hα
    simp [ewIter_zero, hf_infl]
  · have h0α : (0 : ONote) < α := pos_of_ne_zero hα
    have hgate : Nlog (0 : ONote) ≤ f (Nlog α + m) := Nat.zero_le _
    have hlow := ewIter_lower (f := f) (β := 0) (α := α) (m := m) NF.zero h0α hgate
    have hlow' : f (f m) ≤ ewIter f α m := by
      simpa [ewIter_zero] using hlow
    exact le_trans (hf_infl m) (le_trans (hf_infl (f m)) hlow')

/-- **`ewIter` inherits the `2m+1` lower bound:** `2·m + 1 ≤ ewIter f α m` when
`2·m + 1 ≤ f m`. -/
lemma ewIter_low {f : ℕ → ℕ} (hf_infl : ∀ m, m ≤ f m) (hf_low : ∀ m, 2 * m + 1 ≤ f m)
    (α : ONote) (m : ℕ) : 2 * m + 1 ≤ ewIter f α m := by
  by_cases hα : α = 0
  · subst hα; simpa [ewIter_zero] using hf_low m
  · have h0α : (0 : ONote) < α := pos_of_ne_zero hα
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
    obtain ⟨δ, hδmem, rfl⟩ := Finset.mem_image.mp hy
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

/-- **Gated ordinal-monotonicity of `ewIter`:** for `β < α` with the gate `Nlog β ≤ f (Nlog α + m)`,
`ewIter f β m ≤ ewIter f α m`. -/
lemma ewIter_le_of_lt (hf_infl : ∀ m, m ≤ f m)
    (hβNF : β.NF) (hβα : β < α) (hgate : Nlog β ≤ f (Nlog α + m)) :
    ewIter f β m ≤ ewIter f α m :=
  le_trans (ewIter_infl hf_infl β (ewIter f β m)) (ewIter_lower hβNF hβα hgate)

/-- **Pointwise slot-lift:** at internal pass nodes, raise the IH slot `ewIter f β` to `ewIter f α`
via gated ordinal-monotonicity from the base gate. -/
lemma ewIter_slot_le (hf_mono : Monotone f) (hf_infl : ∀ m, m ≤ f m)
    (hβNF : β.NF) (hβα : β < α) (g : Nlog β ≤ f 0) :
    ∀ x, ewIter f β x ≤ ewIter f α x :=
  fun x => ewIter_le_of_lt (m := x) hf_infl hβNF hβα
    (le_trans g (hf_mono (Nat.zero_le _)))

/-- **Slot-composition containment:** merging two IH-reduced premises' slots to fit under
the declared output slot via gated ordinal-monotonicity and the lower bound. -/
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

lemma ewIter_rel1_le {f : ℕ → ℕ} (hf_mono : Monotone f) (hf_infl : ∀ m, m ≤ f m)
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
    obtain ⟨δ, hδmem, rfl⟩ := Finset.mem_image.mp hy
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

lemma ewIter_lift_of_mono_infl (hf_mono : Monotone f)
    (hf_infl : ∀ m, m ≤ f m) (hβNF : β.NF)
    (hβα : β < α) (hβN : Nlog β ≤ f 0) :
    ∀ x, ewIter f β x ≤ ewIter f α x := by
  intro x
  have hgate : Nlog β ≤ f (Nlog α + x) :=
    le_trans hβN (hf_mono (Nat.zero_le _))
  exact le_trans (ewIter_infl hf_infl β (ewIter f β x))
    (ewIter_lower (f := f) hβNF hβα hgate)

lemma ewIter_lift (hf : EwF1 f) (hβNF : β.NF)
    (hβα : β < α) (hβN : Nlog β ≤ f 0) :
    ∀ x, ewIter f β x ≤ ewIter f α x :=
  ewIter_lift_of_mono_infl (EwF1.monotone hf) (EwF1.infl hf) hβNF hβα hβN

/-! ## Attainment, swap lemma, base floor, cut-node slack -/

/-- **Max-attainment for `ewIter`:** the iterate's value is realized by some NF branch `β < α`. -/
lemma ewIter_attained {f : ℕ → ℕ} {α : ONote} (hα : α ≠ 0) (x : ℕ) :
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
    exact ⟨mem_NlogBall.mpr ⟨NF.zero, Nat.zero_le _⟩, pos_of_ne_zero hα, Nat.zero_le _⟩
  have hmem : vals.max' hne ∈ vals := Finset.max'_mem vals hne
  obtain ⟨δ, _, hδval⟩ := Finset.mem_image.mp hmem
  have hδfilter := Finset.mem_filter.mp δ.2
  refine ⟨δ.1, (mem_NlogBall.mp hδfilter.1).1, hδfilter.2.1, hδfilter.2.2, ?_⟩
  rw [hunf, ← hδval]

/-- **The swap lemma:** `s (ewIter s α x) ≤ ewIter s α (s x)` for monotone, inflationary `s`. -/
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

/-- **Base floor:** `s 0 ≤ ewIter s β 0` for all `β`. -/
lemma ewIter_base_le {s : ℕ → ℕ} (hinfl : ∀ m, m ≤ s m) (β : ONote) :
    s 0 ≤ ewIter s β 0 := by
  by_cases hβ : β = 0
  · subst hβ; simp [ewIter_zero]
  · have h0β : (0 : ONote) < β := pos_of_ne_zero hβ
    have hlow := ewIter_lower (f := s) (β := 0) (α := β) (m := 0) NF.zero h0β (Nat.zero_le _)
    have hss : s (s 0) ≤ ewIter s β 0 := by simpa [ewIter_zero] using hlow
    exact le_trans (hinfl (s 0)) hss

/-- **The slot-threaded slack:** the cut-node slack holds at every `k ≥ f 0`. -/
lemma hslack_kit_ge {s : ℕ → ℕ} (hmono : Monotone s) (hinfl : ∀ m, m ≤ s m)
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

/-- **The E–W root slot:** a concrete `EwF1`/`EwF2` witness slot. -/
def ewRootSlot (e : ONote) (m : ℕ) : ℕ → ℕ :=
  fun x => 2 * (x + rel1 (hardy e) m x) + 3

lemma ewRootSlot_f1 (e : ONote) (m : ℕ) : EwF1 (ewRootSlot e m) := by
  constructor
  · intro a b hab
    have hr : hardy e (max m a) ≤ hardy e (max m b) :=
      hardy_monotone e (max_le_max (le_refl m) hab.le)
    simp [ewRootSlot, rel1]
    omega
  · intro x
    simp [ewRootSlot]
    omega

lemma ewRootSlot_f2 (e : ONote) (m : ℕ) : EwF2 (ewRootSlot e m) := by
  intro x
  simp [ewRootSlot]
  omega

/-- The `d`-fold ordinal collapse (rung R's ordinal tower).  `collapse = expTower`. -/
def collapseIter : ℕ → ONote → ONote
  | 0, α => α
  | (d + 1), α => collapse (collapseIter d α)

/-- NF preservation for the collapse tower (real content, not a pin). -/
lemma collapseIter_NF {α : ONote} (hα : α.NF) : ∀ d, (collapseIter d α).NF
  | 0 => hα
  | (d + 1) => expTower_NF (collapseIter_NF hα d)

/-- The `d`-fold slot tower (rung R's iterate composite): each pass iterates the current slot at
the current collapsed ordinal. -/
noncomputable def ewIterTower : (ℕ → ℕ) → ℕ → ONote → (ℕ → ℕ)
  | f, 0, _ => f
  | f, (d + 1), α => ewIter (ewIterTower f d α) (collapseIter d α)

/-- **Collapse-tower shift** — `collapseIter d (collapse α) = collapse (collapseIter d α)`
(`= collapseIter (d+1) α`).  Lets the rung-R induction stay on EXACT ordinals: one pass promotes
`α → collapse α`, and the remaining `d` passes commute the outer `collapse` through. -/
lemma collapseIter_collapse (α : ONote) :
    ∀ d, collapseIter d (collapse α) = collapse (collapseIter d α)
  | 0 => rfl
  | (d + 1) => by
      show collapse (collapseIter d (collapse α)) = collapse (collapse (collapseIter d α))
      rw [collapseIter_collapse α d]

/-- **Slot-tower shift** — `ewIterTower (ewIter f α) d (collapse α) = ewIterTower f (d+1) α`.  The
companion of `collapseIter_collapse` for the slot side: `d` passes starting from the once-passed
`(ewIter f α, collapse α)` equal `d+1` passes from `(f, α)`. -/
lemma ewIterTower_collapse (f : ℕ → ℕ) (α : ONote) :
    ∀ d, ewIterTower (ewIter f α) d (collapse α) = ewIterTower f (d + 1) α
  | 0 => rfl
  | (d + 1) => by
      show ewIter (ewIterTower (ewIter f α) d (collapse α)) (collapseIter d (collapse α))
         = ewIter (ewIterTower f (d + 1) α) (collapse (collapseIter d α))
      rw [ewIterTower_collapse f α d, collapseIter_collapse α d]

/-- The `d`-fold slot tower inherits inflationarity from its base slot (each pass is `ewIter`,
inflationary by `ewIter_infl`). -/
lemma ewIterTower_infl {f : ℕ → ℕ} (hinfl : ∀ m, m ≤ f m) (α : ONote) :
    ∀ (d : ℕ) (m : ℕ), m ≤ ewIterTower f d α m
  | 0, m => hinfl m
  | (d + 1), m => ewIter_infl (ewIterTower_infl hinfl α d) (collapseIter d α) m

/-- The tower slot `ewIterTower f d α` preserves monotonicity. -/
lemma ewIterTower_monotone {f : ℕ → ℕ} (hmono : Monotone f) (hinfl : ∀ m, m ≤ f m)
    (α : ONote) : ∀ d, Monotone (ewIterTower f d α)
  | 0 => hmono
  | (d + 1) => ewIter_monotone (ewIterTower_monotone hmono hinfl α d)
      (ewIterTower_infl hinfl α d) _

/-- A pointwise-dominated slot yields a pointwise-dominated `ewIter`: if `f x ≤ g x` for all `x`
(with `g` monotone and inflationary), then `ewIter f α m ≤ ewIter g α m`. -/
lemma ewIter_mono_slot {f g : ℕ → ℕ} (hfg : ∀ x, f x ≤ g x)
    (hg_mono : Monotone g) (hg_infl : ∀ m, m ≤ g m) :
    ∀ (α : ONote) (m : ℕ), ewIter f α m ≤ ewIter g α m := by
  intro α m
  by_cases hα : α = 0
  · subst hα
    simpa [ewIter_zero] using hfg m
  · conv_lhs => rw [ewIter_unfold f α m]
    rw [ewStep]
    simp only [dif_neg hα]
    apply Finset.max'_le
    intro y hy
    obtain ⟨δ, hδmem, rfl⟩ := Finset.mem_image.mp hy
    have hδlt : (δ : ONote) < α := (Finset.mem_filter.mp δ.2).2.1
    have hδNF : (δ : ONote).NF := (mem_NlogBall.mp (Finset.mem_filter.mp δ.2).1).1
    have hδgate : Nlog (δ : ONote) ≤ f (Nlog α + m) := (Finset.mem_filter.mp δ.2).2.2
    have hδgate' : Nlog (δ : ONote) ≤ g (Nlog α + m) := le_trans hδgate (hfg _)
    have ih1 : ewIter f (δ : ONote) m ≤ ewIter g (δ : ONote) m :=
      ewIter_mono_slot hfg hg_mono hg_infl δ m
    have ih2 : ewIter f (δ : ONote) (ewIter f (δ : ONote) m)
        ≤ ewIter g (δ : ONote) (ewIter g (δ : ONote) m) :=
      le_trans (ewIter_mono_slot hfg hg_mono hg_infl δ _)
        (ewIter_monotone hg_mono hg_infl (δ : ONote) ih1)
    exact le_trans ih2 (ewIter_lower hδNF hδlt hδgate')
termination_by α _ => α
decreasing_by
  all_goals exact hδlt

/-- The slot-stage pre-max `K` commutes out of the whole `d`-fold tower into the argument: one
fixed tower dominates all stages. -/
theorem ewIterTower_rel1_le {f : ℕ → ℕ} (hmono : Monotone f) (hinfl : ∀ m, m ≤ f m)
    (K : ℕ) (α : ONote) : ∀ (d : ℕ) (x : ℕ),
    ewIterTower (rel1 f K) d α x ≤ ewIterTower f d α (max K x)
  | 0, x => le_of_eq (by simp [ewIterTower, rel1])
  | (d + 1), x => by
      have hTmono : Monotone (ewIterTower f d α) := ewIterTower_monotone hmono hinfl α d
      have hTinfl : ∀ m, m ≤ ewIterTower f d α m := ewIterTower_infl hinfl α d
      have hpt : ∀ x', ewIterTower (rel1 f K) d α x' ≤ rel1 (ewIterTower f d α) K x' :=
        fun x' => ewIterTower_rel1_le hmono hinfl K α d x'
      calc ewIter (ewIterTower (rel1 f K) d α) (collapseIter d α) x
          ≤ ewIter (rel1 (ewIterTower f d α) K) (collapseIter d α) x :=
            ewIter_mono_slot hpt (rel1_monotone hTmono K) (rel1_infl hTinfl K)
              (collapseIter d α) x
        _ ≤ ewIter (ewIterTower f d α) (collapseIter d α) (max K x) :=
            ewIter_rel1_le hTmono hTinfl (collapseIter d α) K x

/-- One-step absorption at a nonzero ordinal: `S (S x) ≤ ewIter S β x` for `β ≠ 0`. -/
lemma SS_le_ewIter' {S : ℕ → ℕ} {β : ONote} (hβ : β ≠ 0) (x : ℕ) :
    S (S x) ≤ ewIter S β x := by
  have h0β : (0 : ONote) < β := pos_of_ne_zero hβ
  have h := ewIter_lower (f := S) (β := 0) (α := β) (m := x) NF.zero h0β (Nat.zero_le _)
  simpa [ewIter_zero] using h

/-- **Descent inequality**: a premise at `β < α` with any bumped budget `V' ≤ S V` has its
master bound absorbed by the node's `ewIter S α (S V)`. -/
lemma T3_descent' {S : ℕ → ℕ} (hS_mono : Monotone S) (hS_infl : ∀ m, m ≤ S m)
    {β α : ONote} (hβNF : β.NF) (hβα : β < α)
    {V V' : ℕ} (hV' : V' ≤ S V)
    (hgate : Nlog β ≤ S (S V)) :
    ewIter S β (S V') ≤ ewIter S α (S V) := by
  have ha : ewIter S β (S V') ≤ ewIter S β (S (S V)) :=
    ewIter_monotone hS_mono hS_infl β (hS_mono hV')
  have hb : S (S V) ≤ ewIter S β (S V) := by
    by_cases hβ0 : β = 0
    · subst hβ0
      simp [ewIter_zero]
    · exact le_trans (hS_infl (S (S V))) (SS_le_ewIter' hβ0 (S V))
  have hc : ewIter S β (S (S V)) ≤ ewIter S β (ewIter S β (S V)) :=
    ewIter_monotone hS_mono hS_infl β hb
  have hd : ewIter S β (ewIter S β (S V)) ≤ ewIter S α (S V) :=
    ewIter_lower hβNF hβα (le_trans hgate (hS_mono (by omega)))
  exact le_trans ha (le_trans hc hd)

/-! ## Ordinal-ladder toolkit (`ofNat` rungs) -/

lemma ofNat_lt_ofNat {a b : ℕ} (h : a < b) : ONote.ofNat a < ONote.ofNat b := by
  rw [ONote.lt_def, ONote.repr_ofNat, ONote.repr_ofNat]
  exact_mod_cast h

lemma Nlog_ofNat_le (m : ℕ) : Nlog (ONote.ofNat m) ≤ clog m := by
  cases m with
  | zero => simp
  | succ k =>
      rw [show ONote.ofNat (k + 1) = ONote.oadd 0 k.succPNat 0 from rfl]
      simp [Nat.succPNat]

lemma clog_mono {a b : ℕ} (h : a ≤ b) : clog a ≤ clog b :=
  Nat.log_mono_right (by omega)

end ONote
