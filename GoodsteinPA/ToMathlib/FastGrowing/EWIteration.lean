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
public import GoodsteinPA.ToMathlib.Hardy.Comparison

@[expose] public section

namespace ONote

open Ordinal

/-- A nonzero `ONote` is positive. -/
lemma pos_of_ne_zero {o : ONote} (h : o ≠ 0) : (0 : ONote) < o := by
  cases o with
  | zero => exact (h rfl).elim
  | oadd e n a => exact oadd_pos e n a

/-- `ω^a` as an explicit `ONote` (`oadd a 1 0`). -/
def expTower (a : ONote) : ONote := oadd a 1 0

@[grind →]
lemma expTower_NF {a : ONote} (ha : a.NF) : (expTower a).NF :=
  ha.oadd 1 NFBelow.zero

lemma expTower_lt_expTower {b a : ONote} (hb : b.NF) (h : b < a) :
    expTower b < expTower a :=
  oadd_lt_oadd_1 (expTower_NF hb) h

/-- The Eguchi–Weiermann max-relativization of a number-theoretic operator. -/
def rel1 (f : ℕ → ℕ) (n : ℕ) : ℕ → ℕ := fun x => f (max n x)

/-- **The reassembly algebra:** `rel1 (f ∘ g) n = f ∘ rel1 g n` (definitionally). -/
@[grind =]
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

/-- **`collapse`:** the single-rank height map `a ↦ ω^a`. -/
def collapse (a : ONote) : ONote := expTower a

/-- `collapse` is NF-preserving (so the assembly can splice at NF ordinals). -/
@[grind →]
lemma collapse_NF {a : ONote} (ha : a.NF) : (collapse a).NF := expTower_NF ha

/-- **`collapse` is strictly monotone:** `b < a → collapse b < collapse a`. -/
lemma collapse_strictMono {b a : ONote} (hb : b.NF) (h : b < a) : collapse b < collapse a :=
  expTower_lt_expTower hb h

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

@[simp, grind =] theorem ewN_zero : ewN 0 = 0 := rfl

@[simp, grind =] theorem ewN_oadd (e : ONote) (n : ℕ+) (a : ONote) :
    ewN (oadd e n a) = ewN e + (n : ℕ) + ewN a := rfl

/-! ## The absorbing norm `Nlog`

Max-over-terms with logarithmic coefficient charge: finite-fibered and absorbing
(dissolves the top-rank-cut node gate without base-additivity).
-/

/-- **Logarithmic coefficient charge:** `clog n = ⌊log₂ (n+1)⌋`. -/
def clog (n : ℕ) : ℕ := Nat.log 2 (n + 1)

@[simp, grind =] theorem clog_zero : clog 0 = 0 := rfl

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

@[simp, grind =] theorem Nlog_zero : Nlog 0 = 0 := rfl

@[simp, grind =] theorem Nlog_oadd (e : ONote) (n : ℕ+) (a : ONote) :
    Nlog (oadd e n a) = max (Nlog e + clog (n : ℕ)) (Nlog a) := rfl

/-- `{n : ℕ+ | n < B}` is finite. -/
lemma finite_pnat_coe_lt (B : ℕ) : {n : ℕ+ | (n : ℕ) < B}.Finite := by
  have h : {n : ℕ+ | (n : ℕ) < B} = ((↑) : ℕ+ → ℕ) ⁻¹' Set.Iio B := rfl
  rw [h]
  exact (Set.finite_Iio B).preimage PNat.coe_injective.injOn

/-- **Finite fibers of `Nlog` on NF notations** (NF restriction is forced). -/
theorem Nlog_finite_fiber (K : ℕ) : {o : ONote | NF o ∧ Nlog o ≤ K}.Finite := by
  induction K with
  | zero =>
      apply Set.Finite.subset (Set.finite_singleton (0 : ONote))
      rintro o ⟨_, hle⟩
      cases o with
      | zero => exact Set.mem_singleton _
      | oadd e n a =>
          exfalso
          have h1 := clog_pos n
          simp only [Nlog_oadd] at hle
          omega
  | succ K ihK =>
      have inner : ∀ b : Ordinal, {o : ONote | NFBelow o b ∧ Nlog o ≤ K + 1}.Finite := by
        intro b
        induction b using WellFoundedLT.induction with
        | _ b ihb =>
          have hcov : {o : ONote | NFBelow o b ∧ Nlog o ≤ K + 1} ⊆
              insert 0 (⋃ e ∈ {e : ONote | (NF e ∧ Nlog e ≤ K) ∧ ONote.repr e < b},
                ⋃ n ∈ {n : ℕ+ | (n : ℕ) < 2 ^ (K + 2)},
                  (fun a => oadd e n a) ''
                    {a : ONote | NFBelow a (ONote.repr e) ∧ Nlog a ≤ K + 1}) := by
            rintro o ⟨hbel, hle⟩
            cases o with
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
      rintro o ⟨hNF, hle⟩
      cases o with
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

@[simp, grind =] theorem mem_NlogBall {K : ℕ} {o : ONote} :
    o ∈ NlogBall K ↔ NF o ∧ Nlog o ≤ K := Set.Finite.mem_toFinset _

/-- Absorption on `ONote`, packaged: `x + c = c` when the reprs absorb. -/
lemma add_eq_right_of_repr {x c : ONote} [NF x] [NF c]
    (h : ONote.repr x + ONote.repr c = ONote.repr c) : x + c = c := by
  haveI : NF (x + c) := inferInstance
  exact repr_inj.1 (by rw [repr_add]; exact h)

/-- **The general absorbing theorem:** `Nlog (o+c) ≤ max (Nlog o) (Nlog c) + 1` for NF `o, c`. -/
theorem Nlog_add_le_max_succ (o : ONote) (ho : NF o) (c : ONote) (hc : NF c) :
    Nlog (o + c) ≤ max (Nlog o) (Nlog c) + 1 := by
  induction o generalizing c with
  | zero =>
      show Nlog c ≤ max (Nlog ONote.zero) (Nlog c) + 1
      have : Nlog c ≤ max (Nlog ONote.zero) (Nlog c) := le_max_right _ _
      omega
  | oadd e n a _ihe iha =>
      haveI := ho
      haveI := hc
      haveI hNFe : NF e := ho.fst
      haveI hNFa : NF a := ho.snd
      have hab : NFBelow a (ONote.repr e) := ho.snd'
      cases c with
      | zero =>
          have hz : oadd e n a + ONote.zero = oadd e n a := by
            apply repr_inj.1
            rw [repr_add]; simp
          rw [hz]
          have : Nlog (oadd e n a) ≤ max (Nlog (oadd e n a)) (Nlog ONote.zero) :=
            le_max_left _ _
          omega
      | oadd eg ng ag =>
          haveI hNFeg : NF eg := hc.fst
          haveI hNFag : NF ag := hc.snd
          have hagb : NFBelow ag (ONote.repr eg) := hc.snd'
          rcases lt_trichotomy (ONote.repr e) (ONote.repr eg) with hlt | heq | hgt
          · have hobelow : NFBelow (oadd e n a) (ONote.repr eg) := NF.below_of_lt hlt ho
            have hform : oadd e n a + oadd eg ng ag = oadd eg ng ag :=
              add_eq_right_of_repr
                (Ordinal.add_of_omega0_opow_le hobelow.repr_lt (omega0_le_oadd eg ng ag))
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
          · have hcbelow : NFBelow (oadd eg ng ag) (ONote.repr e) := NF.below_of_lt hgt hc
            haveI hNFac : NF (a + oadd eg ng ag) := inferInstance
            have hac_below : NFBelow (a + oadd eg ng ag) (ONote.repr e) := by
              apply NF.below_of_lt' _ hNFac
              rw [repr_add]
              exact Ordinal.isPrincipal_add_omega0_opow (ONote.repr e) hab.repr_lt
                hcbelow.repr_lt
            haveI : NF (oadd e n (a + oadd eg ng ag)) := NF.oadd hNFe n hac_below
            have hform : oadd e n a + oadd eg ng ag = oadd e n (a + oadd eg ng ag) := by
              apply repr_inj.1
              simp only [repr_add, ONote.repr]
              exact add_assoc _ _ _
            rw [hform, Nlog_oadd, Nlog_oadd]
            have hIH : Nlog (a + oadd eg ng ag) ≤ max (Nlog a) (Nlog (oadd eg ng ag)) + 1 :=
              iha hNFa (oadd eg ng ag) hc
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

/-- **The absorbing node gate:** with an absorbing norm, `N (a+d) ≤ g (f 0)` closes
from the two premise gates and the slack condition without base-additivity. -/
lemma absorbing_closes_gate {N : ONote → ℕ} {g f : ℕ → ℕ} (c : ℕ)
    (habs : ∀ a d, N (a + d) ≤ max (N a) (N d) + c)
    (hslack : max (g 0) (f 0) + c ≤ g (f 0))
    {a d : ONote} (ha : N a ≤ g 0) (hd : N d ≤ f 0) :
    N (a + d) ≤ g (f 0) := by
  have h1 : N (a + d) ≤ max (N a) (N d) + c := habs a d
  have h2 : max (N a) (N d) ≤ max (g 0) (f 0) := by
    apply max_le
    · exact le_trans ha (le_max_left _ _)
    · exact le_trans hd (le_max_right _ _)
  omega

/-- **Instance for fresh roots:** `Nlog`'s absorbing inequality and the slack close
the composed gate. -/
lemma Nlog_add_le_comp {a c : ONote} {f g : ℕ → ℕ}
    (haNF : a.NF) (hcNF : c.NF)
    (ha : Nlog a ≤ g 0) (hc : Nlog c ≤ f 0)
    (hslack : max (g 0) (f 0) + 1 ≤ g (f 0)) :
    Nlog (a + c) ≤ g (f 0) := by
  have habs := Nlog_add_le_max_succ a haNF c hcNF
  have hmm : max (Nlog a) (Nlog c) ≤ max (g 0) (f 0) := max_le_max ha hc
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

/-- `osuccs a n` is the `n`-fold iterate of `osucc` applied to `a`. -/
def osuccs (a : ONote) : ℕ → ONote
  | 0 => a
  | n + 1 => osucc (osuccs a n)

lemma osuccs_NF {a : ONote} (h : a.NF) : ∀ n, (osuccs a n).NF
  | 0 => h
  | n + 1 => osucc_NF (osuccs_NF h n)

@[simp, grind =]
lemma osuccs_succ_shift (a : ONote) : ∀ n, osuccs (osucc a) n = osucc (osuccs a n)
  | 0 => rfl
  | n + 1 => by simp only [osuccs, osuccs_succ_shift a n]

lemma Nlog_osuccs_le {a : ONote} (h : a.NF) : ∀ n, Nlog (osuccs a n) ≤ Nlog a + n
  | 0 => le_refl _
  | n + 1 => by
      have h1 := Nlog_osucc_le (osuccs_NF h n)
      have h2 := Nlog_osuccs_le h n
      simp only [osuccs]
      omega

/-- Successor headroom under the collapse: `collapse a = ω^a` is a limit for `a > 0`, so
`s < collapse a → osucc s < collapse a` (additive principality with `1 < ω^a`). -/
lemma osucc_lt_collapse {s a : ONote} (hsNF : s.NF) (_haNF : a.NF)
    (hapos : (0 : ONote) < a) (h : s < collapse a) : osucc s < collapse a := by
  haveI := hsNF; haveI := _haNF
  have hrepr_collapse : ∀ x : ONote, (collapse x).repr = ω ^ x.repr := fun x => by
    simp [collapse, expTower, ONote.repr]
  refine ONote.lt_def.mpr ?_
  rw [repr_osucc hsNF, hrepr_collapse]
  have h1 : s.repr < Ordinal.omega0 ^ a.repr := by
    have := ONote.lt_def.mp h
    rwa [hrepr_collapse] at this
  have h0 : (0 : Ordinal) < a.repr := by simpa using ONote.lt_def.mp hapos
  have h2 : (1 : Ordinal) < Ordinal.omega0 ^ a.repr :=
    lt_of_lt_of_le Ordinal.one_lt_omega0 (Ordinal.left_le_opow _ h0)
  exact Ordinal.isPrincipal_add_omega0_opow a.repr h1 h2

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
`ewN (a+c) ≤ g (f 0)` (via `ewN_add_le`) is `OperatorZef2.ewN_add_le_comp`. -/
lemma base_add_le_comp {f g : ℕ → ℕ} (hg_base : ∀ k, g 0 + k ≤ g k) {a b : ℕ}
    (ha : a ≤ g 0) (hb : b ≤ f 0) : a + b ≤ g (f 0) := by
  have := hg_base (f 0); omega

/-- **The controlled step**: the branch ball is the NF `Nlog`-ball, whose NF restriction is
forced by `Nlog`'s fiber structure and is the population the calculus feeds anyway. -/
noncomputable def ewStep (f : ℕ → ℕ) (a : ONote) (rec : (b : ONote) → b < a → ℕ → ℕ)
    (m : ℕ) : ℕ :=
  if ha : a = 0 then
    f m
  else
    let K := f (Nlog a + m)
    let vals : Finset ℕ :=
      ((NlogBall K).filter (fun b => b < a ∧ Nlog b ≤ K)).attach.image
        (fun b => rec b.1 (by
            exact (Finset.mem_filter.mp b.2).2.1)
          (rec b.1 (by
            exact (Finset.mem_filter.mp b.2).2.1) m))
    vals.max' (by
      apply Finset.image_nonempty.mpr
      refine ⟨⟨0, ?_⟩, by simp⟩
      simp only [Finset.mem_filter]
      and_intros
      · exact mem_NlogBall.mpr ⟨NF.zero, Nat.zero_le _⟩
      · exact pos_of_ne_zero ha
      · exact Nat.zero_le _)

noncomputable def ewIter (f : ℕ → ℕ) : ONote → ℕ → ℕ
  | a => fun m => ewStep f a (fun b _ => ewIter f b) m
termination_by a => a
decreasing_by
  exact ‹_›

lemma ewIter_unfold (f : ℕ → ℕ) (a : ONote) (m : ℕ) :
    ewIter f a m = ewStep f a (fun b _ => ewIter f b) m := by
  rw [ewIter]

@[simp, grind =] theorem ewIter_zero (f : ℕ → ℕ) : ewIter f 0 = f := by
  funext m
  rw [ewIter_unfold, ewStep]
  simp

variable {f : ℕ → ℕ} {a b : ONote} {m x : ℕ}

lemma ewIter_lower (hbNF : b.NF)
    (hba : b < a) (hgate : Nlog b ≤ f (Nlog a + m)) :
    ewIter f b (ewIter f b m) ≤ ewIter f a m := by
  have hane : a ≠ 0 := by
    intro h
    subst h
    have hrepr := lt_def.1 hba
    rw [repr_zero] at hrepr
    exact (not_lt_of_ge (show (0 : Ordinal) ≤ b.repr from zero_le) hrepr).elim
  conv_rhs => rw [ewIter_unfold f a m]
  rw [ewStep]
  simp only [dif_neg hane]
  apply Finset.le_max'
  apply Finset.mem_image.mpr
  refine ⟨⟨b, ?_⟩, by simp, rfl⟩
  simp only [Finset.mem_filter]
  exact ⟨mem_NlogBall.mpr ⟨hbNF, hgate⟩, hba, hgate⟩

lemma ewIter_infl {f : ℕ → ℕ} (hf_infl : ∀ m, m ≤ f m) (a : ONote) (m : ℕ) :
    m ≤ ewIter f a m := by
  by_cases ha : a = 0
  · subst ha
    simp [ewIter_zero, hf_infl]
  · have h0a : (0 : ONote) < a := pos_of_ne_zero ha
    have hgate : Nlog (0 : ONote) ≤ f (Nlog a + m) := Nat.zero_le _
    have hlow := ewIter_lower (f := f) (b := 0) (a := a) (m := m) NF.zero h0a hgate
    have hlow' : f (f m) ≤ ewIter f a m := by
      simpa [ewIter_zero] using hlow
    exact le_trans (hf_infl m) (le_trans (hf_infl (f m)) hlow')

/-- **`ewIter` inherits the `2m+1` lower bound:** `2·m + 1 ≤ ewIter f a m` when
`2·m + 1 ≤ f m`. -/
lemma ewIter_low {f : ℕ → ℕ} (hf_infl : ∀ m, m ≤ f m) (hf_low : ∀ m, 2 * m + 1 ≤ f m)
    (a : ONote) (m : ℕ) : 2 * m + 1 ≤ ewIter f a m := by
  by_cases ha : a = 0
  · subst ha; simpa [ewIter_zero] using hf_low m
  · have h0a : (0 : ONote) < a := pos_of_ne_zero ha
    have hlow := ewIter_lower (f := f) (b := 0) (a := a) (m := m) NF.zero h0a (Nat.zero_le _)
    have hff : f (f m) ≤ ewIter f a m := by simpa [ewIter_zero] using hlow
    have hfm : m ≤ f m := hf_infl m
    have hlf : 2 * f m + 1 ≤ f (f m) := hf_low (f m)
    omega

theorem ewIter_monotone {f : ℕ → ℕ} (hf_mono : Monotone f) (hf_infl : ∀ m, m ≤ f m)
    (a : ONote) : Monotone (ewIter f a) := by
  intro m m' hmm'
  by_cases ha : a = 0
  · subst ha
    simpa [ewIter_zero] using hf_mono hmm'
  · conv_lhs => rw [ewIter_unfold f a m]
    rw [ewStep]
    simp only [dif_neg ha]
    apply Finset.max'_le
    intro y hy
    obtain ⟨d, hdmem, rfl⟩ := Finset.mem_image.mp hy
    have hdlt : (d : ONote) < a := (Finset.mem_filter.mp d.2).2.1
    have hdNF : (d : ONote).NF := (mem_NlogBall.mp (Finset.mem_filter.mp d.2).1).1
    have hdgate : Nlog (d : ONote) ≤ f (Nlog a + m) := (Finset.mem_filter.mp d.2).2.2
    have hdgate' : Nlog (d : ONote) ≤ f (Nlog a + m') :=
      le_trans hdgate (hf_mono (by omega))
    have ihd : Monotone (ewIter f (d : ONote)) := ewIter_monotone hf_mono hf_infl d
    exact le_trans (ihd (ihd hmm')) (ewIter_lower (f := f) hdNF hdlt hdgate')
termination_by a
decreasing_by
  exact hdlt

/-- **Gated ordinal-monotonicity of `ewIter`:** for `b < a` with the gate `Nlog b ≤ f (Nlog a + m)`,
`ewIter f b m ≤ ewIter f a m`. -/
lemma ewIter_le_of_lt (hf_infl : ∀ m, m ≤ f m)
    (hbNF : b.NF) (hba : b < a) (hgate : Nlog b ≤ f (Nlog a + m)) :
    ewIter f b m ≤ ewIter f a m :=
  le_trans (ewIter_infl hf_infl b (ewIter f b m)) (ewIter_lower hbNF hba hgate)

/-- **Pointwise slot-lift:** at internal pass nodes, raise the IH slot `ewIter f b` to `ewIter f a`
via gated ordinal-monotonicity from the base gate. -/
lemma ewIter_slot_le (hf_mono : Monotone f) (hf_infl : ∀ m, m ≤ f m)
    (hbNF : b.NF) (hba : b < a) (g : Nlog b ≤ f 0) :
    ∀ x, ewIter f b x ≤ ewIter f a x :=
  fun x => ewIter_le_of_lt (m := x) hf_infl hbNF hba
    (le_trans g (hf_mono (Nat.zero_le _)))

/-- **Slot-composition containment:** merging two IH-reduced premises' slots to fit under
the declared output slot via gated ordinal-monotonicity and the lower bound. -/
theorem ewIter_comp_le {f : ℕ → ℕ} (hf_mono : Monotone f) (hf_infl : ∀ m, m ≤ f m)
    {a₀ a₁ a : ONote} (ha₀ : a₀.NF) (ha₁ : a₁.NF)
    (h0 : a₀ < a) (h1 : a₁ < a) (g0 : Nlog a₀ ≤ f 0) (g1 : Nlog a₁ ≤ f 0) (m : ℕ) :
    ewIter f a₀ (ewIter f a₁ m) ≤ ewIter f a m := by
  haveI := ha₀; haveI := ha₁
  have gate0 : ∀ k, Nlog a₀ ≤ f (Nlog a + k) := fun k => le_trans g0 (hf_mono (Nat.zero_le _))
  have gate1 : ∀ k, Nlog a₁ ≤ f (Nlog a + k) := fun k => le_trans g1 (hf_mono (Nat.zero_le _))
  rcases lt_trichotomy a₀.repr a₁.repr with hlt | heq | hgt
  · have ha₀a₁ : a₀ < a₁ := lt_def.mpr hlt
    have g01 : Nlog a₀ ≤ f (Nlog a₁ + (ewIter f a₁ m)) := le_trans g0 (hf_mono (Nat.zero_le _))
    exact le_trans (ewIter_le_of_lt hf_infl ha₀ ha₀a₁ g01) (ewIter_lower ha₁ h1 (gate1 m))
  · have haeq : a₀ = a₁ := repr_inj.mp heq
    subst haeq
    exact ewIter_lower ha₀ h0 (gate0 m)
  · have ha₁a₀ : a₁ < a₀ := lt_def.mpr hgt
    have g10 : Nlog a₁ ≤ f (Nlog a₀ + m) := le_trans g1 (hf_mono (Nat.zero_le _))
    have hinner : ewIter f a₁ m ≤ ewIter f a₀ m := ewIter_le_of_lt hf_infl ha₁ ha₁a₀ g10
    exact le_trans (ewIter_monotone hf_mono hf_infl a₀ hinner) (ewIter_lower ha₀ h0 (gate0 m))

lemma ewIter_rel1_le {f : ℕ → ℕ} (hf_mono : Monotone f) (hf_infl : ∀ m, m ≤ f m)
    (b : ONote) (n x : ℕ) :
    ewIter (rel1 f n) b x ≤ ewIter f b (max n x) := by
  by_cases hb : b = 0
  · subst hb
    simp [ewIter_zero, rel1]
  · conv_lhs => rw [ewIter_unfold (rel1 f n) b x]
    rw [ewStep]
    simp only [dif_neg hb]
    apply Finset.max'_le
    intro y hy
    obtain ⟨d, hdmem, rfl⟩ := Finset.mem_image.mp hy
    have hdlt : (d : ONote) < b := (Finset.mem_filter.mp d.2).2.1
    have hdNF : (d : ONote).NF := (mem_NlogBall.mp (Finset.mem_filter.mp d.2).1).1
    have hdgate_branch :
        Nlog (d : ONote) ≤ rel1 f n (Nlog b + x) := (Finset.mem_filter.mp d.2).2.2
    have hdgate_parent : Nlog (d : ONote) ≤ f (Nlog b + max n x) := by
      refine le_trans hdgate_branch (hf_mono ?_)
      omega
    have ih_arg :
        ewIter (rel1 f n) (d : ONote) (ewIter (rel1 f n) (d : ONote) x) ≤
          ewIter f (d : ONote) (max n (ewIter (rel1 f n) (d : ONote) x)) :=
      ewIter_rel1_le hf_mono hf_infl (d : ONote) n (ewIter (rel1 f n) (d : ONote) x)
    have ih_x :
        ewIter (rel1 f n) (d : ONote) x ≤ ewIter f (d : ONote) (max n x) :=
      ewIter_rel1_le hf_mono hf_infl (d : ONote) n x
    have harg :
        max n (ewIter (rel1 f n) (d : ONote) x) ≤ ewIter f (d : ONote) (max n x) := by
      have hn : n ≤ ewIter f (d : ONote) (max n x) :=
        le_trans (le_max_left n x) (ewIter_infl hf_infl (d : ONote) (max n x))
      exact max_le hn ih_x
    have hmonod := ewIter_monotone hf_mono hf_infl (d : ONote)
    exact le_trans ih_arg
      (le_trans (hmonod harg) (ewIter_lower (f := f) hdNF hdlt hdgate_parent))
termination_by b
decreasing_by
  all_goals exact hdlt

lemma ewIter_lift_of_mono_infl (hf_mono : Monotone f)
    (hf_infl : ∀ m, m ≤ f m) (hbNF : b.NF)
    (hba : b < a) (hbN : Nlog b ≤ f 0) :
    ∀ x, ewIter f b x ≤ ewIter f a x := by
  intro x
  have hgate : Nlog b ≤ f (Nlog a + x) :=
    le_trans hbN (hf_mono (Nat.zero_le _))
  exact le_trans (ewIter_infl hf_infl b (ewIter f b x))
    (ewIter_lower (f := f) hbNF hba hgate)

lemma ewIter_lift (hf : EwF1 f) (hbNF : b.NF)
    (hba : b < a) (hbN : Nlog b ≤ f 0) :
    ∀ x, ewIter f b x ≤ ewIter f a x :=
  ewIter_lift_of_mono_infl (EwF1.monotone hf) (EwF1.infl hf) hbNF hba hbN

/-! ## Attainment, swap lemma, base floor, cut-node slack -/

/-- **Max-attainment for `ewIter`:** the iterate's value is realized by some NF branch `b < a`. -/
lemma ewIter_attained {f : ℕ → ℕ} {a : ONote} (ha : a ≠ 0) (x : ℕ) :
    ∃ b : ONote, b.NF ∧ b < a ∧ Nlog b ≤ f (Nlog a + x) ∧
      ewIter f a x = ewIter f b (ewIter f b x) := by
  have hunf := ewIter_unfold f a x
  rw [ewStep] at hunf
  simp only [dif_neg ha] at hunf
  set S := ((NlogBall (f (Nlog a + x))).filter
    (fun b => b < a ∧ Nlog b ≤ f (Nlog a + x))) with hS
  set vals := S.attach.image
    (fun b => ewIter f b.1 (ewIter f b.1 x)) with hvals
  have hne : vals.Nonempty := by
    apply Finset.image_nonempty.mpr
    refine ⟨⟨0, ?_⟩, Finset.mem_attach _ _⟩
    simp only [hS, Finset.mem_filter]
    exact ⟨mem_NlogBall.mpr ⟨NF.zero, Nat.zero_le _⟩, pos_of_ne_zero ha, Nat.zero_le _⟩
  have hmem : vals.max' hne ∈ vals := Finset.max'_mem vals hne
  obtain ⟨d, _, hdval⟩ := Finset.mem_image.mp hmem
  have hdfilter := Finset.mem_filter.mp d.2
  refine ⟨d.1, (mem_NlogBall.mp hdfilter.1).1, hdfilter.2.1, hdfilter.2.2, ?_⟩
  rw [hunf, ← hdval]

/-- **The swap lemma:** `s (ewIter s a x) ≤ ewIter s a (s x)` for monotone, inflationary `s`. -/
theorem ewIter_swap {s : ℕ → ℕ} (hmono : Monotone s) (hinfl : ∀ m, m ≤ s m)
    (a : ONote) (x : ℕ) : s (ewIter s a x) ≤ ewIter s a (s x) := by
  by_cases ha : a = 0
  · subst ha; simp [ewIter_zero]
  · obtain ⟨b, hbNF, hblt, hbgate, heq⟩ := ewIter_attained ha x
    rw [heq]
    have ih1 : s (ewIter s b (ewIter s b x)) ≤ ewIter s b (s (ewIter s b x)) :=
      ewIter_swap hmono hinfl b (ewIter s b x)
    have ih2 : s (ewIter s b x) ≤ ewIter s b (s x) :=
      ewIter_swap hmono hinfl b x
    have hmb : Monotone (ewIter s b) := ewIter_monotone hmono hinfl b
    have hgate' : Nlog b ≤ s (Nlog a + s x) :=
      le_trans hbgate (hmono (by have := hinfl x; omega))
    exact le_trans ih1 (le_trans (hmb ih2) (ewIter_lower hbNF hblt hgate'))
termination_by a
decreasing_by all_goals exact hblt

/-- **Base floor:** `s 0 ≤ ewIter s b 0` for all `b`. -/
lemma ewIter_base_le {s : ℕ → ℕ} (hinfl : ∀ m, m ≤ s m) (b : ONote) :
    s 0 ≤ ewIter s b 0 := by
  by_cases hb : b = 0
  · subst hb; simp [ewIter_zero]
  · have h0b : (0 : ONote) < b := pos_of_ne_zero hb
    have hlow := ewIter_lower (f := s) (b := 0) (a := b) (m := 0) NF.zero h0b (Nat.zero_le _)
    have hss : s (s 0) ≤ ewIter s b 0 := by simpa [ewIter_zero] using hlow
    exact le_trans (hinfl (s 0)) hss

/-- **The slot-threaded slack:** the cut-node slack holds at every `k ≥ f 0`. -/
lemma hslack_kit_ge {s : ℕ → ℕ} (hmono : Monotone s) (hinfl : ∀ m, m ≤ s m)
    (hlow : ∀ m, 2 * m + 1 ≤ s m) (b₁ b₂ : ONote) :
    ∀ k, ewIter s b₂ 0 ≤ k →
      max (ewIter s b₁ 0) k + 1 ≤ ewIter s b₁ k := by
  intro k hk
  have hkarm : 2 * k + 1 ≤ ewIter s b₁ k := ewIter_low hinfl hlow b₁ k
  have hs0f : s 0 ≤ k := le_trans (ewIter_base_le hinfl b₂) hk
  have hgmono : Monotone (ewIter s b₁) := ewIter_monotone hmono hinfl b₁
  have hswap : s (ewIter s b₁ 0) ≤ ewIter s b₁ (s 0) := ewIter_swap hmono hinfl b₁ 0
  have hgarm : 2 * ewIter s b₁ 0 + 1 ≤ ewIter s b₁ k :=
    le_trans (hlow (ewIter s b₁ 0)) (le_trans hswap (hgmono hs0f))
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
  | 0, a => a
  | (d + 1), a => collapse (collapseIter d a)

/-- NF preservation for the collapse tower (real content, not a pin). -/
lemma collapseIter_NF {a : ONote} (ha : a.NF) : ∀ d, (collapseIter d a).NF
  | 0 => ha
  | (d + 1) => expTower_NF (collapseIter_NF ha d)

/-- The `d`-fold slot tower (rung R's iterate composite): each pass iterates the current slot at
the current collapsed ordinal. -/
noncomputable def ewIterTower : (ℕ → ℕ) → ℕ → ONote → (ℕ → ℕ)
  | f, 0, _ => f
  | f, (d + 1), a => ewIter (ewIterTower f d a) (collapseIter d a)

/-- **Collapse-tower shift** — `collapseIter d (collapse a) = collapse (collapseIter d a)`
(`= collapseIter (d+1) a`).  Lets the rung-R induction stay on EXACT ordinals: one pass promotes
`a → collapse a`, and the remaining `d` passes commute the outer `collapse` through. -/
lemma collapseIter_collapse (a : ONote) :
    ∀ d, collapseIter d (collapse a) = collapse (collapseIter d a)
  | 0 => rfl
  | (d + 1) => by
      show collapse (collapseIter d (collapse a)) = collapse (collapse (collapseIter d a))
      rw [collapseIter_collapse a d]

/-- **Slot-tower shift** — `ewIterTower (ewIter f a) d (collapse a) = ewIterTower f (d+1) a`.  The
companion of `collapseIter_collapse` for the slot side: `d` passes starting from the once-passed
`(ewIter f a, collapse a)` equal `d+1` passes from `(f, a)`. -/
lemma ewIterTower_collapse (f : ℕ → ℕ) (a : ONote) :
    ∀ d, ewIterTower (ewIter f a) d (collapse a) = ewIterTower f (d + 1) a
  | 0 => rfl
  | (d + 1) => by
      show ewIter (ewIterTower (ewIter f a) d (collapse a)) (collapseIter d (collapse a))
         = ewIter (ewIterTower f (d + 1) a) (collapse (collapseIter d a))
      rw [ewIterTower_collapse f a d, collapseIter_collapse a d]

/-- The `d`-fold slot tower inherits inflationarity from its base slot (each pass is `ewIter`,
inflationary by `ewIter_infl`). -/
lemma ewIterTower_infl {f : ℕ → ℕ} (hinfl : ∀ m, m ≤ f m) (a : ONote) :
    ∀ (d : ℕ) (m : ℕ), m ≤ ewIterTower f d a m
  | 0, m => hinfl m
  | (d + 1), m => ewIter_infl (ewIterTower_infl hinfl a d) (collapseIter d a) m

/-- The tower slot `ewIterTower f d a` preserves monotonicity. -/
lemma ewIterTower_monotone {f : ℕ → ℕ} (hmono : Monotone f) (hinfl : ∀ m, m ≤ f m)
    (a : ONote) : ∀ d, Monotone (ewIterTower f d a)
  | 0 => hmono
  | (d + 1) => ewIter_monotone (ewIterTower_monotone hmono hinfl a d)
      (ewIterTower_infl hinfl a d) _

/-- A pointwise-dominated slot yields a pointwise-dominated `ewIter`: if `f x ≤ g x` for all `x`
(with `g` monotone and inflationary), then `ewIter f a m ≤ ewIter g a m`. -/
lemma ewIter_mono_slot {f g : ℕ → ℕ} (hfg : ∀ x, f x ≤ g x)
    (hg_mono : Monotone g) (hg_infl : ∀ m, m ≤ g m) :
    ∀ (a : ONote) (m : ℕ), ewIter f a m ≤ ewIter g a m := by
  intro a m
  by_cases ha : a = 0
  · subst ha
    simpa [ewIter_zero] using hfg m
  · conv_lhs => rw [ewIter_unfold f a m]
    rw [ewStep]
    simp only [dif_neg ha]
    apply Finset.max'_le
    intro y hy
    obtain ⟨d, hdmem, rfl⟩ := Finset.mem_image.mp hy
    have hdlt : (d : ONote) < a := (Finset.mem_filter.mp d.2).2.1
    have hdNF : (d : ONote).NF := (mem_NlogBall.mp (Finset.mem_filter.mp d.2).1).1
    have hdgate : Nlog (d : ONote) ≤ f (Nlog a + m) := (Finset.mem_filter.mp d.2).2.2
    have hdgate' : Nlog (d : ONote) ≤ g (Nlog a + m) := le_trans hdgate (hfg _)
    have ih1 : ewIter f (d : ONote) m ≤ ewIter g (d : ONote) m :=
      ewIter_mono_slot hfg hg_mono hg_infl d m
    have ih2 : ewIter f (d : ONote) (ewIter f (d : ONote) m)
        ≤ ewIter g (d : ONote) (ewIter g (d : ONote) m) :=
      le_trans (ewIter_mono_slot hfg hg_mono hg_infl d _)
        (ewIter_monotone hg_mono hg_infl (d : ONote) ih1)
    exact le_trans ih2 (ewIter_lower hdNF hdlt hdgate')
termination_by a _ => a
decreasing_by
  all_goals exact hdlt

/-- The slot-stage pre-max `K` commutes out of the whole `d`-fold tower into the argument: one
fixed tower dominates all stages. -/
theorem ewIterTower_rel1_le {f : ℕ → ℕ} (hmono : Monotone f) (hinfl : ∀ m, m ≤ f m)
    (K : ℕ) (a : ONote) : ∀ (d : ℕ) (x : ℕ),
    ewIterTower (rel1 f K) d a x ≤ ewIterTower f d a (max K x)
  | 0, x => le_of_eq (by simp [ewIterTower, rel1])
  | (d + 1), x => by
      have hTmono : Monotone (ewIterTower f d a) := ewIterTower_monotone hmono hinfl a d
      have hTinfl : ∀ m, m ≤ ewIterTower f d a m := ewIterTower_infl hinfl a d
      have hpt : ∀ x', ewIterTower (rel1 f K) d a x' ≤ rel1 (ewIterTower f d a) K x' :=
        fun x' => ewIterTower_rel1_le hmono hinfl K a d x'
      calc ewIter (ewIterTower (rel1 f K) d a) (collapseIter d a) x
          ≤ ewIter (rel1 (ewIterTower f d a) K) (collapseIter d a) x :=
            ewIter_mono_slot hpt (rel1_monotone hTmono K) (rel1_infl hTinfl K)
              (collapseIter d a) x
        _ ≤ ewIter (ewIterTower f d a) (collapseIter d a) (max K x) :=
            ewIter_rel1_le hTmono hTinfl (collapseIter d a) K x

/-- One-step absorption at a nonzero ordinal: `S (S x) ≤ ewIter S b x` for `b ≠ 0`. -/
lemma SS_le_ewIter' {S : ℕ → ℕ} {b : ONote} (hb : b ≠ 0) (x : ℕ) :
    S (S x) ≤ ewIter S b x := by
  have h0b : (0 : ONote) < b := pos_of_ne_zero hb
  have h := ewIter_lower (f := S) (b := 0) (a := b) (m := x) NF.zero h0b (Nat.zero_le _)
  simpa [ewIter_zero] using h

/-- **Descent inequality**: a premise at `b < a` with any bumped budget `V' ≤ S V` has its
master bound absorbed by the node's `ewIter S a (S V)`. -/
lemma T3_descent' {S : ℕ → ℕ} (hS_mono : Monotone S) (hS_infl : ∀ m, m ≤ S m)
    {b a : ONote} (hbNF : b.NF) (hba : b < a)
    {V V' : ℕ} (hV' : V' ≤ S V)
    (hgate : Nlog b ≤ S (S V)) :
    ewIter S b (S V') ≤ ewIter S a (S V) := by
  have ha : ewIter S b (S V') ≤ ewIter S b (S (S V)) :=
    ewIter_monotone hS_mono hS_infl b (hS_mono hV')
  have hb : S (S V) ≤ ewIter S b (S V) := by
    by_cases hb0 : b = 0
    · subst hb0
      simp [ewIter_zero]
    · exact le_trans (hS_infl (S (S V))) (SS_le_ewIter' hb0 (S V))
  have hc : ewIter S b (S (S V)) ≤ ewIter S b (ewIter S b (S V)) :=
    ewIter_monotone hS_mono hS_infl b hb
  have hd : ewIter S b (ewIter S b (S V)) ≤ ewIter S a (S V) :=
    ewIter_lower hbNF hba (le_trans hgate (hS_mono (by omega)))
  exact le_trans ha (le_trans hc hd)

/-! ## Ordinal-ladder toolkit (`ofNat` rungs) -/

@[grind →]
lemma ofNat_lt_ofNat {a b : ℕ} (h : a < b) : ONote.ofNat a < ONote.ofNat b := by
  rw [ONote.lt_def, ONote.repr_ofNat, ONote.repr_ofNat]
  exact_mod_cast h

lemma Nlog_ofNat_le (m : ℕ) : Nlog (ONote.ofNat m) ≤ clog m := by
  cases m with
  | zero => simp
  | succ k =>
      rw [show ONote.ofNat (k + 1) = ONote.oadd 0 k.succPNat 0 from rfl]
      simp [Nat.succPNat]

@[grind →]
lemma clog_mono {a b : ℕ} (h : a ≤ b) : clog a ≤ clog b :=
  Nat.log_mono_right (by omega)

end ONote
