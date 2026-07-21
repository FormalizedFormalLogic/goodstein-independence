module

public import GoodsteinPA.ToMathlib.FastGrowing.EWIteration

@[expose] public section

/-!
# `ewIter` → `hardy` majorization

Dominate `ewIter S γ (S (max m C))` by `fastGrowing o` at one fixed normal-form `o`, eventually.
-/

namespace ONote

open Ordinal

/-- **The norm/Nlog bridge:** `norm b < 2^(Nlog b + 1)`. -/
lemma norm_lt_two_pow_Nlog : ∀ (b : ONote), norm b < 2 ^ (Nlog b + 1)
  | 0 => by simp [norm]
  | oadd e n a => by
      have he := norm_lt_two_pow_Nlog e
      have ha := norm_lt_two_pow_Nlog a
      have hn : (n : ℕ) < 2 ^ (clog (n : ℕ) + 1) := by
        have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) ((n : ℕ) + 1)
        unfold clog
        omega
      simp only [norm_oadd, Nlog_oadd]
      have hpow_mono : ∀ {i j : ℕ}, i ≤ j → (2:ℕ) ^ i ≤ 2 ^ j :=
        fun h => Nat.pow_le_pow_right (by norm_num) h
      apply max_lt
      · exact lt_of_lt_of_le he
          (hpow_mono (by have := Nat.zero_le (clog (n : ℕ)); omega))
      apply max_lt
      · exact lt_of_lt_of_le hn
          (hpow_mono (by have := Nat.zero_le (Nlog e); omega))
      · exact lt_of_lt_of_le ha (hpow_mono (by omega))

/-- A branch ordinal passing the `Nlog b ≤ K` gate has linear norm `< 2^(K+1)`. -/
@[grind →]
lemma norm_lt_of_Nlog_le {b : ONote} {K : ℕ} (h : Nlog b ≤ K) :
    norm b < 2 ^ (K + 1) :=
  lt_of_lt_of_le (norm_lt_two_pow_Nlog b)
    (Nat.pow_le_pow_right (by norm_num) (by omega))


/-! ## The single-step composition and raise (master induction engine)

The branch shape `H_{ω^b'}³(H_{ω^e'}(z))` composes to `H_{ω^b'·2 + ω^e'}(z)` then raises to `H_{ω^a'}(z)`.
-/

/-- `ω^x` as a notation. -/
def Wpow (x : ONote) : ONote := oadd x 1 0

@[grind →]
lemma Wpow_NF {x : ONote} (hx : x.NF) : (Wpow x).NF :=
  NF.oadd hx 1 NFBelow.zero

/-- `Wpow`'s repr is a genuine `ω`-power. -/
@[simp, grind =]
lemma repr_Wpow (x : ONote) : (Wpow x).repr = ω ^ x.repr := by
  show ω ^ x.repr * (1 : ℕ) + 0 = ω ^ x.repr; simp

/-- Adding a finite `1` shifts the repr by exactly `1`. -/
@[grind =]
lemma repr_add_one {b : ONote} (hb : b.NF) : (b + 1).repr = b.repr + 1 := by
  haveI := hb
  rw [ONote.repr_add, ONote.repr_one]; norm_num

/-- Every NF notation is strictly below its successor `b + 1`. -/
@[grind →]
lemma lt_add_one_self {b : ONote} (hb : b.NF) : b < b + 1 := by
  rw [lt_def, repr_add_one hb]; exact lt_add_one _

/-- `b + 1` is never `0`. -/
@[grind →]
lemma add_one_ne_zero {b : ONote} (hb : b.NF) : b + 1 ≠ 0 := by
  intro h
  have hh := congrArg ONote.repr h
  rw [repr_add_one hb, repr_zero] at hh
  exact (lt_of_lt_of_le zero_lt_one le_add_self).ne' hh

/-- General `ω^A + ω^B < ω^{A+1}` for `B < A` (the tower-collapse raise, generalizing a single
`ω`-power step to arbitrary ordered exponents). -/
lemma Wpow_add_lt_Wpow_succ {A B : ONote} (hA : A.NF) (hB : B.NF) (hBA : B < A) :
    Wpow A + Wpow B < Wpow (A + 1) := by
  haveI : (Wpow A).NF := Wpow_NF hA
  haveI : (Wpow B).NF := Wpow_NF hB
  rw [lt_def, ONote.repr_add]
  show (Wpow A).repr + (Wpow B).repr < ω ^ (A + 1).repr * (1 : ℕ) + 0
  rw [repr_Wpow, repr_Wpow, repr_add_one hA]
  have hBltA : B.repr < A.repr := by rw [lt_def] at hBA; exact hBA
  have hstep : ω ^ B.repr < ω ^ A.repr :=
    (Ordinal.opow_lt_opow_iff_right (by norm_num : (1 : Ordinal) < ω)).mpr hBltA
  calc ω ^ A.repr + ω ^ B.repr
      < ω ^ A.repr + ω ^ A.repr := (add_lt_add_iff_left _).2 hstep
    _ = ω ^ A.repr * 2 := by rw [show (2 : Ordinal) = 1 + 1 by norm_num, mul_add, mul_one]
    _ < ω ^ A.repr * ω := mul_lt_mul_of_pos_left (by simpa using Ordinal.natCast_lt_omega0 2)
        (Ordinal.opow_pos _ omega0_pos)
    _ = ω ^ (A.repr + 1) := by
        have h := (Ordinal.opow_add ω A.repr 1).symm
        rw [Ordinal.opow_one] at h; exact h
    _ ≤ ω ^ (A.repr + 1) * (1 : ℕ) + 0 := by simp

/-- **Double-Hardy collapse:** `H_{ω^A}(H_{ω^B}(y)) = H_{ω^A+ω^B}(y)` when `B < A`. -/
lemma hardy_double_collapse {A B : ONote} (hA : A.NF) (hB : B.NF) (hBA : B < A) (y : ℕ) :
    hardy (Wpow A) (hardy (Wpow B) y) = hardy (Wpow A + Wpow B) y := by
  refine (hardy_add_comp _ (Wpow_NF hA) _ (Wpow_NF hB) (Or.inr ?_) y).symm
  show (Wpow B).repr < ω ^ (lastExp (Wpow A)).repr
  have hlast : lastExp (Wpow A) = A := rfl
  rw [hlast, repr_Wpow]
  have hBltA : B.repr < A.repr := by rw [lt_def] at hBA; exact hBA
  exact (Ordinal.opow_lt_opow_iff_right (by norm_num : (1 : Ordinal) < ω)).mpr hBltA

/-- The ONote sum `ω^b'·2 + ω^e'` in normal form. -/
def stepOrd (b' e' : ONote) : ONote := oadd b' 2 (Wpow e')

lemma stepOrd_NF {b' e' : ONote} (hb' : b'.NF) (he' : e'.NF) (hlt : e' < b') :
    (stepOrd b' e').NF :=
  NF.oadd hb' 2 (NFBelow.oadd he' NFBelow.zero (lt_def.mp hlt))

/-- **The chain identity:** Two same-level principals over one engine compose exactly. -/
lemma hardy_chain_eq {b' e' : ONote} (hb' : b'.NF) (he' : e'.NF)
    (hb0 : b' ≠ 0) (hlt : e' < b') (z : ℕ) :
    hardy (Wpow b') (hardy (Wpow b') (hardy (Wpow e') z))
      = hardy (stepOrd b' e') z := by
  have hsum : (oadd b' 2 0 : ONote) + Wpow e' = stepOrd b' e' := by
    haveI h1 : NF (oadd b' 2 0) := NF.oadd hb' 2 NFBelow.zero
    haveI h2 : NF (Wpow e') := Wpow_NF he'
    haveI h3 : NF (stepOrd b' e') := stepOrd_NF hb' he' hlt
    apply repr_inj.mp
    rw [repr_add]
    show ω ^ b'.repr * (2:ℕ) + 0 + (ω ^ e'.repr * (1:ℕ) + 0)
      = ω ^ b'.repr * (2:ℕ) + (ω ^ e'.repr * (1:ℕ) + 0)
    rw [add_zero]
  have hcomp : hardy ((oadd b' 2 0 : ONote) + Wpow e') z
      = hardy (oadd b' 2 0) (hardy (Wpow e') z) := by
    apply hardy_add_comp _ (NF.oadd hb' 2 NFBelow.zero) _ (Wpow_NF he')
    · right
      show ω ^ e'.repr * (1:ℕ) + 0 < ω ^ (lastExp (oadd b' 2 0)).repr
      have hle : lastExp (oadd b' 2 0) = b' := rfl
      rw [hle]
      simpa using (Ordinal.opow_lt_opow_iff_right (by norm_num : (1:Ordinal) < ω)).mpr
        (lt_def.mp hlt)
  have hcoeff : hardy (oadd b' 2 0) (hardy (Wpow e') z)
      = hardy (Wpow b') (hardy (Wpow b') (hardy (Wpow e') z)) := by
    have h2 : (2 : ℕ+) = 1 + 1 := rfl
    rw [show (oadd b' 2 0 : ONote) = oadd b' (1 + 1) 0 from rfl,
      hardy_coeff_add b' hb0 1 1]
    rfl
  rw [← hsum, hcomp, hcoeff]

/-- **The raise:** The composed step ordinal fits under the next `ω`-power. -/
lemma hardy_step_raise {b' e' a' : ONote} (hb' : b'.NF) (he' : e'.NF) (ha' : a'.NF)
    (hlt : e' < b') (hba' : b' < a') {z : ℕ}
    (hnorm : max (norm b') (max 2 (max (norm e') 1)) ≤ z) :
    hardy (stepOrd b' e') z ≤ hardy (Wpow a') z := by
  apply hardy_le_of_lt (stepOrd_NF hb' he' hlt) (Wpow_NF ha')
  · show oadd b' 2 (Wpow e') < oadd a' 1 0
    rw [lt_def]
    calc (oadd b' 2 (Wpow e')).repr
        < ω ^ a'.repr := by
          have h1 : (oadd b' 2 (Wpow e')).NF := stepOrd_NF hb' he' hlt
          exact (NF.below_of_lt (lt_def.mp hba') h1).repr_lt
      _ ≤ (oadd a' 1 0).repr := by
          show ω ^ a'.repr ≤ ω ^ a'.repr * (1:ℕ) + 0
          simp
  · show norm (oadd b' 2 (Wpow e')) ≤ z
    simpa [norm, Wpow] using hnorm

/-- **The step engine assembled:** The master induction's branch case. -/
lemma hardy_step {b' e' a' : ONote} (hb' : b'.NF) (he' : e'.NF) (ha' : a'.NF)
    (hb0 : b' ≠ 0) (hlt : e' < b') (hba' : b' < a') {z : ℕ}
    (hnorm : max (norm b') (max 2 (max (norm e') 1)) ≤ z) :
    hardy (Wpow b') (hardy (Wpow b') (hardy (Wpow e') z)) ≤ hardy (Wpow a') z := by
  rw [hardy_chain_eq hb' he' hb0 hlt z]
  exact hardy_step_raise hb' he' ha' hlt hba' hnorm


/-! ## Argument super-additivity of `hardy`

`H_o(n) + c ≤ H_o(n + c)`.
-/

lemma hardy_succ_ge (o : ONote) (n : ℕ) : hardy o n + 1 ≤ hardy o (n + 1) := by
  rcases e : fundamentalSequence o with (_ | a) | f
  · rw [hardy_zero' o e]; simp
  · have hlt : a < o := by
      have hp := fundamentalSequence_has_prop o; rw [e] at hp
      rw [lt_def, hp.1]; exact Order.lt_succ _
    rw [hardy_succ o e]
    exact hardy_succ_ge a (n + 1)
  · have hlt : f n < o := by
      have hp := fundamentalSequence_has_prop o; rw [e] at hp
      exact (hp.2.1 n).2.1
    rw [hardy_limit o e]
    exact le_trans (hardy_succ_ge (f n) n) (hardy_fundSeq_step e n)
termination_by o
decreasing_by
  · exact hlt
  · exact hlt

lemma hardy_arg_add (o : ONote) (n c : ℕ) : hardy o n + c ≤ hardy o (n + c) := by
  induction c with
  | zero => simp
  | succ c ih =>
      calc hardy o n + (c + 1) = (hardy o n + c) + 1 := by ring
        _ ≤ hardy o (n + c) + 1 := by omega
        _ ≤ hardy o (n + c + 1) := hardy_succ_ge o (n + c)
        _ = hardy o (n + (c + 1)) := by ring_nf

/-- Exponent-strict-monotonicity of `Wpow` (repr-level). -/
@[grind →]
lemma Wpow_lt {x y : ONote} (h : x < y) : Wpow x < Wpow y := by
  rw [lt_def]
  show ω ^ x.repr * (1 : ℕ) + 0 < ω ^ y.repr * (1 : ℕ) + 0
  simpa using (Ordinal.opow_lt_opow_iff_right (by norm_num : (1 : Ordinal) < ω)).mpr
    (lt_def.mp h)

/-! ## Linear-norm control of ONote addition

`norm (x + y) ≤ normSum x + norm y`.
-/

/-- Summed per-term charge of a notation (an upper-bound companion to `norm`). -/
@[grind =]
def normSum : ONote → ℕ
  | 0 => 0
  | oadd e n a => max (norm e) (n : ℕ) + normSum a

lemma norm_addAux_le (e : ONote) (n : ℕ+) (o : ONote) :
    norm (addAux e n o) ≤ max (norm e) (n : ℕ) + norm o := by
  cases o with
  | zero =>
      show norm (oadd e n 0) ≤ _
      simp only [norm_oadd, norm_zero]
      omega
  | oadd e' n' a' =>
      show norm (match ONote.cmp e e' with
        | Ordering.lt => oadd e' n' a'
        | Ordering.eq => oadd e (n + n') a'
        | Ordering.gt => oadd e n (oadd e' n' a')) ≤ _
      cases ONote.cmp e e' with
      | lt => simp only [norm_oadd]; omega
      | eq =>
          simp only [norm_oadd, PNat.add_coe]
          have h1 := le_max_left (norm e) (n : ℕ)
          have h2 := le_max_right (norm e) (n : ℕ)
          have h3 := le_max_left (norm e') ((n' : ℕ) ⊔ norm a')
          have h4 := le_max_left (n' : ℕ) (norm a')
          have h5 := le_max_right (n' : ℕ) (norm a')
          have h6 := le_max_right (norm e') ((n' : ℕ) ⊔ norm a')
          omega
      | gt => simp only [norm_oadd]; omega

lemma norm_add_le : ∀ (x y : ONote), norm (x + y) ≤ normSum x + norm y
  | 0, y => by simp [normSum]
  | oadd e n a, y => by
      rw [oadd_add]
      have h1 := norm_addAux_le e n (a + y)
      have h2 := norm_add_le a y
      simp only [normSum]
      omega


/-! ## The coefficient-3 chain (master induction's branch shape)

`H_{ω^b'}³(H_{ω^e'}(z)) = H_{ω^b'·3 + ω^e'}(z)`.
-/

/-- `ω^b'·3 + ω^e'` in normal form. -/
def stepOrd3 (b' e' : ONote) : ONote := oadd b' 3 (Wpow e')

lemma stepOrd3_NF {b' e' : ONote} (hb' : b'.NF) (he' : e'.NF) (hlt : e' < b') :
    (stepOrd3 b' e').NF :=
  NF.oadd hb' 3 (NFBelow.oadd he' NFBelow.zero (lt_def.mp hlt))

/-- Three same-level principals over one engine compose exactly. -/
lemma hardy_chain3_eq {b' e' : ONote} (hb0 : b' ≠ 0) (z : ℕ) :
    hardy (Wpow b') (hardy (Wpow b') (hardy (Wpow b') (hardy (Wpow e') z)))
      = hardy (stepOrd3 b' e') z := by
  rw [show stepOrd3 b' e' = oadd b' 3 (Wpow e') from rfl,
    hardy_oadd_tail b' 3 (Wpow e') z,
    show (3 : ℕ+) = 1 + 2 from rfl, hardy_coeff_add b' hb0 1 2,
    show (2 : ℕ+) = 1 + 1 from rfl, hardy_coeff_add b' hb0 1 1]
  rfl

/-- The composed branch ordinal sits strictly below the next `ω`-power. -/
lemma stepOrd3_lt_Wpow {b' e' a' : ONote} (hb' : b'.NF) (he' : e'.NF)
    (hlt : e' < b') (hba' : b' < a') : stepOrd3 b' e' < Wpow a' := by
  rw [lt_def]
  calc (stepOrd3 b' e').repr
      < ω ^ a'.repr :=
        (NF.below_of_lt (lt_def.mp hba') (stepOrd3_NF hb' he' hlt)).repr_lt
    _ ≤ (Wpow a').repr := by
        show ω ^ a'.repr ≤ ω ^ a'.repr * (1 : ℕ) + 0
        simp


/-! ## The master majorization

`ewIter f α m ≤ H_{ω^{e'+1+α}}(H_{ω^{e'}}(Nlog α + m + p))` with assignment exponent `g α := e' + 1 + α`, under the engine hypothesis `hEng`.
-/

theorem ewIter_hardy_le {f : ℕ → ℕ} {e' : ONote} {p : ℕ}
    (he' : e'.NF) (hp : norm e' + 1 ≤ p)
    (hEng : ∀ x, x + 2 * f x + 2 ^ (f x + 1) + normSum (e' + 1) + norm e' + 2 * p + 4
        ≤ hardy (Wpow e') (x + p))
    (α : ONote) (hα : α.NF) (m : ℕ) :
    ewIter f α m ≤ hardy (Wpow (e' + 1 + α)) (hardy (Wpow e') (Nlog α + m + p)) := by
  haveI := he'
  haveI hNF1 : (1 : ONote).NF := NF.oadd NF.zero 1 NFBelow.zero
  haveI hNFe1 : (e' + 1).NF := ONote.add_nf e' 1
  have hrepr_e1 : (e' + 1).repr = e'.repr + 1 := by
    rw [ONote.repr_add, ONote.repr_one]; norm_num
  by_cases h0 : α = 0
  · subst h0
    have hbase : f m ≤ hardy (Wpow e') (m + p) := by
      refine le_trans ?_ (hEng m)
      calc f m ≤ m + 2 * f m := by omega
        _ ≤ m + 2 * f m + 2 ^ (f m + 1) := Nat.le_add_right _ _
        _ ≤ m + 2 * f m + 2 ^ (f m + 1) + normSum (e' + 1) := Nat.le_add_right _ _
        _ ≤ m + 2 * f m + 2 ^ (f m + 1) + normSum (e' + 1) + norm e' :=
            Nat.le_add_right _ _
        _ ≤ m + 2 * f m + 2 ^ (f m + 1) + normSum (e' + 1) + norm e' + 2 * p :=
            Nat.le_add_right _ _
        _ ≤ m + 2 * f m + 2 ^ (f m + 1) + normSum (e' + 1) + norm e' + 2 * p + 4 :=
            Nat.le_add_right _ _
    simp only [ewIter_zero, Nlog_zero, Nat.zero_add]
    exact le_trans hbase (le_hardy _ _)
  · haveI := hα
    haveI hgαNF : (e' + 1 + α).NF := ONote.add_nf (e' + 1) α
    conv_lhs => rw [ewIter_unfold f α m]
    rw [ewStep]
    simp only [dif_neg h0]
    apply Finset.max'_le
    intro v hv
    obtain ⟨δ, hδmem, rfl⟩ := Finset.mem_image.mp hv
    have hδlt : (δ : ONote) < α := (Finset.mem_filter.mp δ.2).2.1
    have hδNF : (δ : ONote).NF := (mem_NlogBall.mp (Finset.mem_filter.mp δ.2).1).1
    have hδgate : Nlog (δ : ONote) ≤ f (Nlog α + m) := (Finset.mem_filter.mp δ.2).2.2
    haveI := hδNF
    haveI hgδNF : (e' + 1 + (δ : ONote)).NF := ONote.add_nf (e' + 1) δ
    have hreprδ : (e' + 1 + (δ : ONote)).repr = e'.repr + 1 + (δ : ONote).repr := by
      rw [ONote.repr_add, hrepr_e1]
    have hreprα : (e' + 1 + α).repr = e'.repr + 1 + α.repr := by
      rw [ONote.repr_add, hrepr_e1]
    -- ordinal facts about the assignment
    have hegδ : e' < e' + 1 + (δ : ONote) := by
      rw [lt_def, hreprδ]
      calc e'.repr < e'.repr + 1 := lt_add_of_pos_right _ zero_lt_one
        _ ≤ e'.repr + 1 + (δ : ONote).repr := le_self_add
    have hgδα : e' + 1 + (δ : ONote) < e' + 1 + α := by
      rw [lt_def, hreprδ, hreprα]
      exact (add_lt_add_iff_left _).2 (lt_def.mp hδlt)
    have hgδ0 : e' + 1 + (δ : ONote) ≠ 0 := by
      intro h
      have := lt_def.mp (h ▸ hegδ)
      simp at this
    -- step 1+2: the two IH layers
    have ih_inner : ewIter f (δ : ONote) m
        ≤ hardy (Wpow (e' + 1 + (δ : ONote)))
            (hardy (Wpow e') (Nlog (δ : ONote) + m + p)) :=
      ewIter_hardy_le he' hp hEng (δ : ONote) hδNF m
    have ih_outer : ewIter f (δ : ONote) (ewIter f (δ : ONote) m)
        ≤ hardy (Wpow (e' + 1 + (δ : ONote)))
            (hardy (Wpow e') (Nlog (δ : ONote) + ewIter f (δ : ONote) m + p)) :=
      ewIter_hardy_le he' hp hEng (δ : ONote) hδNF (ewIter f (δ : ONote) m)
    -- step 3+4: monotone lift of the outer seed, then push the additive cost innermost
    have hpush : Nlog (δ : ONote) + ewIter f (δ : ONote) m + p
        ≤ hardy (Wpow (e' + 1 + (δ : ONote)))
            (hardy (Wpow e') (Nlog (δ : ONote) + m + p + (Nlog (δ : ONote) + p))) := by
      have h1 : Nlog (δ : ONote) + ewIter f (δ : ONote) m + p
          ≤ hardy (Wpow (e' + 1 + (δ : ONote)))
              (hardy (Wpow e') (Nlog (δ : ONote) + m + p)) + (Nlog (δ : ONote) + p) := by
        have := ih_inner; omega
      have h2 := hardy_arg_add (Wpow (e' + 1 + (δ : ONote)))
        (hardy (Wpow e') (Nlog (δ : ONote) + m + p)) (Nlog (δ : ONote) + p)
      have h3 := hardy_arg_add (Wpow e') (Nlog (δ : ONote) + m + p) (Nlog (δ : ONote) + p)
      exact le_trans h1 (le_trans h2 (hardy_monotone _ h3))
    -- assemble the four-layer stack
    have hY2 : ewIter f (δ : ONote) (ewIter f (δ : ONote) m)
        ≤ hardy (Wpow (e' + 1 + (δ : ONote))) (hardy (Wpow e')
            (hardy (Wpow (e' + 1 + (δ : ONote)))
              (hardy (Wpow e') (Nlog (δ : ONote) + m + p + (Nlog (δ : ONote) + p))))) :=
      le_trans ih_outer (hardy_monotone _ (hardy_monotone _ hpush))
    -- step 5: raise the middle engine to the branch level
    have hmid : hardy (Wpow e')
          (hardy (Wpow (e' + 1 + (δ : ONote)))
            (hardy (Wpow e') (Nlog (δ : ONote) + m + p + (Nlog (δ : ONote) + p))))
        ≤ hardy (Wpow (e' + 1 + (δ : ONote)))
          (hardy (Wpow (e' + 1 + (δ : ONote)))
            (hardy (Wpow e') (Nlog (δ : ONote) + m + p + (Nlog (δ : ONote) + p)))) := by
      apply hardy_le_of_lt (Wpow_NF he') (Wpow_NF hgδNF) (Wpow_lt hegδ)
      have hnw : norm (Wpow e') ≤ p := by
        simp only [Wpow, norm_oadd, norm_zero, PNat.one_coe]
        omega
      calc norm (Wpow e') ≤ p := hnw
        _ ≤ Nlog (δ : ONote) + m + p + (Nlog (δ : ONote) + p) := by omega
        _ ≤ hardy (Wpow e') (Nlog (δ : ONote) + m + p + (Nlog (δ : ONote) + p)) :=
            le_hardy _ _
        _ ≤ hardy (Wpow (e' + 1 + (δ : ONote)))
              (hardy (Wpow e') (Nlog (δ : ONote) + m + p + (Nlog (δ : ONote) + p))) :=
            le_hardy _ _
    -- step 6: collapse via the coefficient-3 chain identity
    have hchain : ewIter f (δ : ONote) (ewIter f (δ : ONote) m)
        ≤ hardy (stepOrd3 (e' + 1 + (δ : ONote)) e')
            (Nlog (δ : ONote) + m + p + (Nlog (δ : ONote) + p)) := by
      rw [← hardy_chain3_eq hgδ0]
      exact le_trans hY2 (hardy_monotone _ hmid)
    -- step 7: the collapsed argument fits under the engine-inflated seed
    have hsc_z : Nlog (δ : ONote) + m + p + (Nlog (δ : ONote) + p)
        ≤ hardy (Wpow e') (Nlog α + m + p) := by
      have hE := hEng (Nlog α + m)
      generalize 2 ^ (f (Nlog α + m) + 1) = Q at hE
      omega
    -- step 8: final raise, norm gate paid by the bridge + hEng
    have hraise : hardy (stepOrd3 (e' + 1 + (δ : ONote)) e')
          (hardy (Wpow e') (Nlog α + m + p))
        ≤ hardy (Wpow (e' + 1 + α)) (hardy (Wpow e') (Nlog α + m + p)) := by
      apply hardy_le_of_lt (stepOrd3_NF hgδNF he' hegδ) (Wpow_NF hgαNF)
        (stepOrd3_lt_Wpow hgδNF he' hegδ hgδα)
      have hnormδ : norm (δ : ONote) < 2 ^ (f (Nlog α + m) + 1) :=
        norm_lt_of_Nlog_le hδgate
      have hnormgδ : norm (e' + 1 + (δ : ONote)) ≤ normSum (e' + 1) + norm (δ : ONote) :=
        norm_add_le (e' + 1) (δ : ONote)
      have hE := hEng (Nlog α + m)
      simp only [Wpow] at hE
      simp only [stepOrd3, Wpow, norm_oadd, norm_zero, PNat.one_coe]
      have h3 : ((3 : ℕ+) : ℕ) = 3 := rfl
      rw [h3]
      generalize 2 ^ (f (Nlog α + m) + 1) = Q at hE hnormδ
      have hm1 := le_max_left (norm e') (max 1 0)
      omega
    exact le_trans hchain (le_trans (hardy_monotone _ hsc_z) hraise)
termination_by α
decreasing_by
  · exact hδlt
  · exact hδlt


/-! ## Concrete engine instantiation

`e' := e₀ + 2` discharges `hEng` from plain Hardy domination `f ≤ H_{ω^{e₀}}`.
-/

/-- Closed form at `ω²`: `H_{ω²}(y) + 1 = 2^{y+1}·(y+1)`. -/
lemma hardy_omega_sq (y : ℕ) :
    hardy (oadd (ofNat 2) 1 0) y + 1 = 2 ^ (y + 1) * (y + 1) := by
  rw [hardy_omega_pow_ofNat 2 y, show (ofNat 2 : ONote) = 2 from rfl, fastGrowing_two]

/-- The engine arithmetic: anything below `5y + 2^{y+1}` fits under `H_{ω²}(y)` (`y ≥ 2`). -/
lemma engine_arith {L y : ℕ} (h2 : 2 ≤ y) (hL : L ≤ 5 * y + 2 ^ (y + 1)) :
    L ≤ hardy (oadd (ofNat 2) 1 0) y := by
  have hcf := hardy_omega_sq y
  have hP : 8 ≤ 2 ^ (y + 1) := by
    calc (8 : ℕ) = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (y + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hexp : 2 ^ (y + 1) * (y + 1) = 2 ^ (y + 1) * y + 2 ^ (y + 1) := by ring
  rw [hexp] at hcf
  have hmul : 8 * y ≤ 2 ^ (y + 1) * y := Nat.mul_le_mul_right y hP
  generalize 2 ^ (y + 1) * y = R at hcf hmul
  generalize 2 ^ (y + 1) = Q at hcf hL
  omega

/-- **Abstract engine core**, parameterized by the raised-argument domination `hfxp`. -/
theorem hEng_of_fx {f : ℕ → ℕ} {e₀ : ONote} {p : ℕ}
    (he₀ : e₀.NF) (he₀0 : e₀ ≠ 0)
    (hfxp : ∀ x, f x ≤ hardy (Wpow e₀) (x + p))
    (hp : norm (e₀ + 1) + norm e₀ + normSum (e₀ + 2 + 1) + norm (e₀ + 2) + 8 ≤ p) :
    ∀ x, x + 2 * f x + 2 ^ (f x + 1) + normSum (e₀ + 2 + 1) + norm (e₀ + 2) + 2 * p + 4
        ≤ hardy (Wpow (e₀ + 2)) (x + p) := by
  intro x
  haveI := he₀
  haveI hNF1 : (1 : ONote).NF := NF.oadd NF.zero 1 NFBelow.zero
  haveI hNF2 : (2 : ONote).NF := nf_ofNat 2
  haveI hNFe1 : (e₀ + 1).NF := ONote.add_nf e₀ 1
  haveI hNFe2 : (e₀ + 2).NF := ONote.add_nf e₀ 2
  have hrepr1 : (e₀ + 1).repr = e₀.repr + 1 := repr_add_one he₀
  have hrepr2 : (e₀ + 2).repr = e₀.repr + 2 := by
    rw [ONote.repr_add, show ((2 : ONote)).repr = ((2 : ℕ) : Ordinal) from repr_ofNat 2]
    norm_num
  haveI hWe1 : (Wpow (e₀ + 1)).NF := Wpow_NF hNFe1
  haveI hWe0 : (Wpow e₀).NF := Wpow_NF he₀
  have he₀pos : (1 : Ordinal) ≤ e₀.repr :=
    Order.one_le_iff_ne_zero.mpr
      (fun h0 => he₀0 (repr_inj.mp (by rw [h0, repr_zero])))
  -- the inflated engine argument
  have hy1 : x + p ≤ hardy (Wpow e₀) (x + p) := le_hardy _ _
  have hy2 : 2 * (x + p) ≤ hardy (Wpow e₀) (x + p) :=
    two_mul_le_hardy_pow he₀0 he₀ (by omega)
  have hfx : f x ≤ hardy (Wpow e₀) (x + p) := hfxp x
  have hpow : 2 ^ (f x + 1) ≤ 2 ^ (hardy (Wpow e₀) (x + p) + 1) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  -- step A: everything fits under H_{ω²} at the inflated argument
  have hA : x + 2 * f x + 2 ^ (f x + 1) + normSum (e₀ + 2 + 1) + norm (e₀ + 2) + 2 * p + 4
      ≤ hardy (oadd (ofNat 2) 1 0) (hardy (Wpow e₀) (x + p)) := by
    apply engine_arith (by omega)
    generalize hQ : 2 ^ (hardy (Wpow e₀) (x + p) + 1) = Q at hpow
    generalize 2 ^ (f x + 1) = A at hpow ⊢
    omega
  -- step B: raise ω² to ω^{e₀+1} (equality possible at e₀ = 1)
  have hB : hardy (oadd (ofNat 2) 1 0) (hardy (Wpow e₀) (x + p))
      ≤ hardy (Wpow (e₀ + 1)) (hardy (Wpow e₀) (x + p)) := by
    have hle : ((ofNat 2 : ONote)).repr ≤ (e₀ + 1).repr := by
      rw [repr_ofNat, hrepr1]
      have : ((2 : ℕ) : Ordinal) = 1 + 1 := by norm_num
      rw [this]
      exact add_le_add he₀pos le_rfl
    rcases eq_or_lt_of_le hle with heq | hlt
    · rw [show (oadd (ofNat 2) 1 0 : ONote) = Wpow (e₀ + 1) by
        show Wpow (ofNat 2) = Wpow (e₀ + 1)
        rw [repr_inj.mp heq]]
    · apply hardy_le_of_lt (Wpow_NF (nf_ofNat 2)) (Wpow_NF hNFe1)
        (Wpow_lt (lt_def.mpr hlt))
      have hn2 : norm (Wpow (ofNat 2)) = 2 := by
        simp [Wpow, ofNat_succ, norm_oadd]
      show norm (Wpow (ofNat 2)) ≤ _
      rw [hn2]
      omega
  -- step C: exact composition H_{ω^{e₀+1}} ∘ H_{ω^{e₀}} = H_{ω^{e₀+1}+ω^{e₀}}
  have hC : hardy (Wpow (e₀ + 1)) (hardy (Wpow e₀) (x + p))
      = hardy (Wpow (e₀ + 1) + Wpow e₀) (x + p) :=
    hardy_double_collapse hNFe1 he₀ (lt_add_one_self he₀) (x + p)
  -- step D: final raise under ω^{e₀+2}
  haveI hDNF : (Wpow (e₀ + 1) + Wpow e₀).NF := ONote.add_nf _ _
  have hDlt : Wpow (e₀ + 1) + Wpow e₀ < Wpow (e₀ + 2) := by
    haveI : (e₀ + 1 + 1).NF := ONote.add_nf (e₀ + 1) 1
    have heq : (e₀ + 1 + 1 : ONote) = e₀ + 2 :=
      repr_inj.mp (by rw [repr_add_one hNFe1, repr_add_one he₀, hrepr2, add_assoc, one_add_one_eq_two])
    rw [← heq]
    exact Wpow_add_lt_Wpow_succ hNFe1 he₀ (lt_add_one_self he₀)
  have hDnorm : norm (Wpow (e₀ + 1) + Wpow e₀) ≤ x + p := by
    have h := norm_add_le (Wpow (e₀ + 1)) (Wpow e₀)
    have h1 : normSum (Wpow (e₀ + 1)) = max (norm (e₀ + 1)) 1 := by
      show max (norm (e₀ + 1)) ((1 : ℕ+) : ℕ) + normSum 0 = max (norm (e₀ + 1)) 1
      simp [normSum]
    have h2 : norm (Wpow e₀) = max (norm e₀) (max 1 0) := rfl
    rw [h1, h2] at h
    have hm1 := le_max_left (norm (e₀ + 1)) 1
    have hm2 := le_max_left (norm e₀) (max 1 0)
    have hmm1 : max (norm (e₀ + 1)) 1 ≤ norm (e₀ + 1) + 1 := by omega
    have hmm2 : max (norm e₀) (max 1 0) ≤ norm e₀ + 1 := by omega
    omega
  calc x + 2 * f x + 2 ^ (f x + 1) + normSum (e₀ + 2 + 1) + norm (e₀ + 2) + 2 * p + 4
      ≤ hardy (oadd (ofNat 2) 1 0) (hardy (Wpow e₀) (x + p)) := hA
    _ ≤ hardy (Wpow (e₀ + 1)) (hardy (Wpow e₀) (x + p)) := hB
    _ = hardy (Wpow (e₀ + 1) + Wpow e₀) (x + p) := hC
    _ ≤ hardy (Wpow (e₀ + 2)) (x + p) :=
        hardy_le_of_lt hDNF (Wpow_NF hNFe2) hDlt hDnorm

/-- **The concrete engine:** `e' := e₀ + 2` discharges `ewIter_hardy_le`'s `hEng` from plain domination. -/
theorem hEng_of_dom {f : ℕ → ℕ} {e₀ : ONote} {p : ℕ}
    (he₀ : e₀.NF) (he₀0 : e₀ ≠ 0)
    (hdom : ∀ z, f z ≤ hardy (Wpow e₀) z)
    (hp : norm (e₀ + 1) + norm e₀ + normSum (e₀ + 2 + 1) + norm (e₀ + 2) + 8 ≤ p) :
    ∀ x, x + 2 * f x + 2 ^ (f x + 1) + normSum (e₀ + 2 + 1) + norm (e₀ + 2) + 2 * p + 4
        ≤ hardy (Wpow (e₀ + 2)) (x + p) :=
  hEng_of_fx he₀ he₀0 (fun x => le_trans (hdom x) (hardy_monotone _ (by omega))) hp

/-- **The end-to-end majorization at a concrete engine:** From `f ≤ H_{ω^{e₀}}` with explicit pad. -/
theorem ewIter_hardy_le_of_dom {f : ℕ → ℕ} {e₀ : ONote}
    (he₀ : e₀.NF) (he₀0 : e₀ ≠ 0)
    (hdom : ∀ z, f z ≤ hardy (Wpow e₀) z)
    (α : ONote) (hα : α.NF) (m : ℕ) :
    ewIter f α m ≤ hardy (Wpow (e₀ + 2 + 1 + α))
      (hardy (Wpow (e₀ + 2))
        (Nlog α + m + (norm (e₀ + 1) + norm e₀ + normSum (e₀ + 2 + 1) + norm (e₀ + 2) + 8))) := by
  haveI := he₀
  haveI hNF2 : (2 : ONote).NF := nf_ofNat 2
  haveI hNFe2 : (e₀ + 2).NF := ONote.add_nf e₀ 2
  exact ewIter_hardy_le hNFe2 (by omega)
    (hEng_of_dom he₀ he₀0 hdom le_rfl) α hα m

/-- **The engine at a padded pointwise domination:** `f z ≤ H_{ω^{e₀}}(z + c)`, absorbing constant floor. -/
theorem hEng_of_dom_pad {f : ℕ → ℕ} {e₀ : ONote} {p c : ℕ}
    (he₀ : e₀.NF) (he₀0 : e₀ ≠ 0)
    (hdom : ∀ z, f z ≤ hardy (Wpow e₀) (z + c))
    (hp : norm (e₀ + 1) + norm e₀ + normSum (e₀ + 2 + 1) + norm (e₀ + 2) + 8 + c ≤ p) :
    ∀ x, x + 2 * f x + 2 ^ (f x + 1) + normSum (e₀ + 2 + 1) + norm (e₀ + 2) + 2 * p + 4
        ≤ hardy (Wpow (e₀ + 2)) (x + p) :=
  hEng_of_fx he₀ he₀0
    (fun x => le_trans (hdom x) (hardy_monotone _ (by omega))) (by omega)

/-- **The padded end-to-end majorization:** From `f ≤ H_{ω^{e₀}}(· + c)`. -/
theorem ewIter_hardy_le_of_dom_pad {f : ℕ → ℕ} {e₀ : ONote} {c : ℕ}
    (he₀ : e₀.NF) (he₀0 : e₀ ≠ 0)
    (hdom : ∀ z, f z ≤ hardy (Wpow e₀) (z + c))
    (α : ONote) (hα : α.NF) (m : ℕ) :
    ewIter f α m ≤ hardy (Wpow (e₀ + 2 + 1 + α))
      (hardy (Wpow (e₀ + 2))
        (Nlog α + m + (norm (e₀ + 1) + norm e₀ + normSum (e₀ + 2 + 1) + norm (e₀ + 2) + 8 + c))) := by
  haveI := he₀
  haveI hNF2 : (2 : ONote).NF := nf_ofNat 2
  haveI hNFe2 : (e₀ + 2).NF := ONote.add_nf e₀ 2
  exact ewIter_hardy_le hNFe2 (by omega)
    (hEng_of_dom_pad he₀ he₀0 hdom le_rfl) α hα m

/-! ## `S*`-domination bricks

The concrete pipeline slot is padded-Hardy-dominable: bricks build from `ewRootSlot` → tower → `Sslot`.
-/

/-- Any normal-form `e` sits strictly below `ω^{e+1}`. -/
@[grind →]
lemma e_lt_Wpow_succ (e : ONote) (he : e.NF) : e < Wpow (e + 1) := by
  rw [lt_def]
  show e.repr < (Wpow (e + 1)).repr
  rw [repr_Wpow, repr_add_one he]
  calc e.repr ≤ ω ^ e.repr := Ordinal.right_le_opow _ (by exact_mod_cast Ordinal.one_lt_omega0)
    _ < ω ^ (e.repr + 1) :=
        (Ordinal.opow_lt_opow_iff_right (by norm_num : (1 : Ordinal) < ω)).mpr (lt_add_one _)

/-- **`hardy e` at a `max`-shifted argument is padded-dominated by `H_{ω^{e+1}}`** uniformly in `z`. -/
lemma hardy_maxpad (e : ONote) (he : e.NF) (m z : ℕ) :
    hardy e (max m z) ≤ hardy (Wpow (e + 1)) (z + (m + norm e)) := by
  have he1 : (e + 1).NF := ONote.add_nf e 1
  have hlt : e < Wpow (e + 1) := e_lt_Wpow_succ e he
  have hmono : hardy e (max m z) ≤ hardy e (z + (m + norm e)) :=
    hardy_monotone e (by omega)
  have hgate : hardy e (z + (m + norm e)) ≤ hardy (Wpow (e + 1)) (z + (m + norm e)) :=
    hardy_le_of_lt he (Wpow_NF he1) hlt (by omega)
  exact le_trans hmono hgate

/-- **The base root slot is padded-Hardy-dominated** at `H_{ω^{(e+1)+2}}`. -/
theorem ewRootSlot_dom_pad (e : ONote) (he : e.NF) (m x : ℕ) :
    ewRootSlot e m x
        ≤ hardy (Wpow ((e + 1) + 2))
            (x + (norm ((e + 1) + 1) + norm (e + 1) + normSum ((e + 1) + 2 + 1)
                    + norm ((e + 1) + 2) + 8 + (m + norm e))) := by
  have he₀ : (e + 1).NF := ONote.add_nf e 1
  have he₀0 : e + 1 ≠ 0 := add_one_ne_zero he
  have hfdom : ∀ z, hardy e (max m z) ≤ hardy (Wpow (e + 1)) (z + (m + norm e)) :=
    hardy_maxpad e he m
  have hEng := hEng_of_dom_pad (f := fun z => hardy e (max m z)) (c := m + norm e)
    he₀ he₀0 hfdom le_rfl
  have hEngx := hEng x
  have hfge : x ≤ hardy e (max m x) := le_trans (le_max_right m x) (le_hardy e (max m x))
  have hpowge : hardy e (max m x) + 1 ≤ 2 ^ (hardy e (max m x) + 1) :=
    Nat.le_of_lt Nat.lt_two_pow_self
  have hunfold : ewRootSlot e m x = 2 * (x + hardy e (max m x)) + 3 := by
    simp only [ewRootSlot, rel1]
  rw [hunfold]
  refine le_trans ?_ hEngx
  omega

/-- `rel1` shift preserves padded domination. -/
lemma rel1_dom_pad {g : ℕ → ℕ} {E : ONote} {c : ℕ}
    (hg : ∀ x, g x ≤ hardy (Wpow E) (x + c)) (K z : ℕ) :
    rel1 g K z ≤ hardy (Wpow E) (z + (K + c)) := by
  show g (max K z) ≤ hardy (Wpow E) (z + (K + c))
  exact le_trans (hg (max K z)) (hardy_monotone _ (by omega))


/-- **The tower is padded-Hardy-dominated:** Each `ewIter` pass raises to a double Hardy, which collapses and raises back to a single `ω`-power level. -/
theorem ewIterTower_dom_pad {g : ℕ → ℕ} {E : ONote} {c : ℕ} (hE : E.NF) (hE0 : E ≠ 0)
    (hg : ∀ x, g x ≤ hardy (Wpow E) (x + c)) (α : ONote) (hα : α.NF) (d : ℕ) :
    ∃ (E' : ONote) (c' : ℕ), E'.NF ∧ E' ≠ 0 ∧
      ∀ x, ewIterTower g d α x ≤ hardy (Wpow E') (x + c') := by
  induction d with
  | zero => exact ⟨E, c, hE, hE0, hg⟩
  | succ d ih =>
    obtain ⟨Ed, cd, hEd, hEd0, hdom⟩ := ih
    have hγ : (collapseIter d α).NF := collapseIter_NF hα d
    haveI := hEd
    haveI : (2 : ONote).NF := nf_ofNat 2
    haveI hB : (Ed + 2).NF := ONote.add_nf Ed 2
    haveI hB1 : (Ed + 2 + 1).NF := ONote.add_nf (Ed + 2) 1
    haveI := hγ
    haveI hA : (Ed + 2 + 1 + collapseIter d α).NF :=
      ONote.add_nf (Ed + 2 + 1) (collapseIter d α)
    have hBA : Ed + 2 < Ed + 2 + 1 + collapseIter d α := by
      have h1 : (Ed + 2 + 1 + collapseIter d α).repr
          = (Ed + 2).repr + 1 + (collapseIter d α).repr := by
        rw [ONote.repr_add (Ed + 2 + 1) (collapseIter d α),
          ONote.repr_add (Ed + 2) 1, ONote.repr_one]
        push_cast
        rfl
      rw [lt_def, h1]
      calc (Ed + 2).repr < (Ed + 2).repr + 1 := lt_add_one _
        _ ≤ (Ed + 2).repr + 1 + (collapseIter d α).repr := le_self_add
    haveI hWA : (Wpow (Ed + 2 + 1 + collapseIter d α)).NF := Wpow_NF hA
    haveI hWB : (Wpow (Ed + 2)).NF := Wpow_NF hB
    haveI hA1 : (Ed + 2 + 1 + collapseIter d α + 1).NF :=
      ONote.add_nf (Ed + 2 + 1 + collapseIter d α) 1
    have hA10 : Ed + 2 + 1 + collapseIter d α + 1 ≠ 0 := add_one_ne_zero hA
    refine ⟨Ed + 2 + 1 + collapseIter d α + 1,
      Nlog (collapseIter d α)
        + (norm (Ed + 1) + norm Ed + normSum (Ed + 2 + 1) + norm (Ed + 2) + 8 + cd)
        + norm (Wpow (Ed + 2 + 1 + collapseIter d α) + Wpow (Ed + 2)),
      hA1, hA10, ?_⟩
    intro x
    have hpass := ewIter_hardy_le_of_dom_pad hEd hEd0 hdom (collapseIter d α) hγ x
    have hstep : ewIterTower g (d + 1) α x
        = ewIter (ewIterTower g d α) (collapseIter d α) x := rfl
    rw [hstep]
    refine le_trans hpass ?_
    rw [hardy_double_collapse hA hB hBA]
    have harg : Nlog (collapseIter d α) + x
          + (norm (Ed + 1) + norm Ed + normSum (Ed + 2 + 1) + norm (Ed + 2) + 8 + cd)
        ≤ x + (Nlog (collapseIter d α)
          + (norm (Ed + 1) + norm Ed + normSum (Ed + 2 + 1) + norm (Ed + 2) + 8 + cd)
          + norm (Wpow (Ed + 2 + 1 + collapseIter d α) + Wpow (Ed + 2))) := by omega
    refine le_trans (hardy_monotone _ harg) ?_
    haveI hsum : (Wpow (Ed + 2 + 1 + collapseIter d α) + Wpow (Ed + 2)).NF :=
      ONote.add_nf _ _
    have hgate : norm (Wpow (Ed + 2 + 1 + collapseIter d α) + Wpow (Ed + 2))
        ≤ x + (Nlog (collapseIter d α)
          + (norm (Ed + 1) + norm Ed + normSum (Ed + 2 + 1) + norm (Ed + 2) + 8 + cd)
          + norm (Wpow (Ed + 2 + 1 + collapseIter d α) + Wpow (Ed + 2))) := by omega
    exact hardy_le_of_lt hsum (Wpow_NF hA1) (Wpow_add_lt_Wpow_succ hA hB hBA) hgate

/-- **Iterates of a fixed `ω`-power Hardy level are padded-Hardy-dominated** with existential level and pad. -/
theorem hardy_Wpow_iter_dom_pad (E₀ : ONote) (hE₀ : E₀.NF) (k : ℕ) :
    ∃ (E : ONote) (c : ℕ), E.NF ∧ E ≠ 0 ∧ E₀ < E ∧
      ∀ z, (hardy (Wpow E₀))^[k] z ≤ hardy (Wpow E) (z + c) := by
  haveI := hE₀
  induction k with
  | zero =>
      refine ⟨E₀ + 1, 0, ONote.add_nf E₀ 1, add_one_ne_zero hE₀, lt_add_one_self hE₀, ?_⟩
      intro z
      simpa using le_hardy (Wpow (E₀ + 1)) z
  | succ k ih =>
      obtain ⟨Ek, ck, hEk, hEk0, hE₀Ek, hdom⟩ := ih
      haveI := hEk
      haveI hWEk : (Wpow Ek).NF := Wpow_NF hEk
      haveI hWE₀ : (Wpow E₀).NF := Wpow_NF hE₀
      haveI hsum : (Wpow Ek + Wpow E₀).NF := ONote.add_nf _ _
      refine ⟨Ek + 1, ck + norm (Wpow Ek + Wpow E₀), ONote.add_nf Ek 1, add_one_ne_zero hEk,
        lt_trans hE₀Ek (lt_add_one_self hEk), ?_⟩
      intro z
      have h1 : (hardy (Wpow E₀))^[k + 1] z = (hardy (Wpow E₀))^[k] (hardy (Wpow E₀) z) :=
        Function.iterate_succ_apply _ _ _
      rw [h1]
      have h2 : (hardy (Wpow E₀))^[k] (hardy (Wpow E₀) z)
          ≤ hardy (Wpow Ek) (hardy (Wpow E₀) z + ck) := hdom _
      have h3 : hardy (Wpow E₀) z + ck ≤ hardy (Wpow E₀) (z + ck) := hardy_arg_add _ _ _
      have h4 : hardy (Wpow Ek) (hardy (Wpow E₀) (z + ck))
          = hardy (Wpow Ek + Wpow E₀) (z + ck) := hardy_double_collapse hEk hE₀ hE₀Ek _
      have harg : z + ck ≤ z + (ck + norm (Wpow Ek + Wpow E₀)) := by omega
      have hgate : norm (Wpow Ek + Wpow E₀) ≤ z + (ck + norm (Wpow Ek + Wpow E₀)) := by omega
      calc (hardy (Wpow E₀))^[k] (hardy (Wpow E₀) z)
          ≤ hardy (Wpow Ek) (hardy (Wpow E₀) z + ck) := h2
        _ ≤ hardy (Wpow Ek) (hardy (Wpow E₀) (z + ck)) := hardy_monotone _ h3
        _ = hardy (Wpow Ek + Wpow E₀) (z + ck) := h4
        _ ≤ hardy (Wpow Ek + Wpow E₀) (z + (ck + norm (Wpow Ek + Wpow E₀))) :=
            hardy_monotone _ harg
        _ ≤ hardy (Wpow (Ek + 1)) (z + (ck + norm (Wpow Ek + Wpow E₀))) :=
            hardy_le_of_lt hsum (Wpow_NF (ONote.add_nf Ek 1))
              (Wpow_add_lt_Wpow_succ hEk hE₀ hE₀Ek) hgate

/-- **Padded-domination max-combiner:** Two padded Hardy bounds combine at joint level `E₁+E₂+1`. -/
theorem dom_pad_max {f g : ℕ → ℕ} {E₁ E₂ : ONote} {c₁ c₂ : ℕ}
    (hE₁ : E₁.NF) (hE₂ : E₂.NF)
    (hf : ∀ z, f z ≤ hardy (Wpow E₁) (z + c₁))
    (hg : ∀ z, g z ≤ hardy (Wpow E₂) (z + c₂)) :
    ∃ (E : ONote) (c : ℕ), E.NF ∧ E ≠ 0 ∧ E₁ < E ∧ E₂ < E ∧
      ∀ z, max (f z) (g z) ≤ hardy (Wpow E) (z + c) := by
  haveI := hE₁
  haveI := hE₂
  haveI h12 : (E₁ + E₂).NF := ONote.add_nf E₁ E₂
  haveI hE : (E₁ + E₂ + 1).NF := ONote.add_nf (E₁ + E₂) 1
  have hrepr : (E₁ + E₂ + 1).repr = E₁.repr + E₂.repr + 1 := by
    rw [repr_add_one h12, ONote.repr_add E₁ E₂]
  have hlt₁ : E₁ < E₁ + E₂ + 1 := by
    rw [lt_def, hrepr]
    calc E₁.repr ≤ E₁.repr + E₂.repr := le_self_add
      _ < E₁.repr + E₂.repr + 1 := lt_add_one _
  have hlt₂ : E₂ < E₁ + E₂ + 1 := by
    rw [lt_def, hrepr]
    calc E₂.repr ≤ E₁.repr + E₂.repr := le_add_self
      _ < E₁.repr + E₂.repr + 1 := lt_add_one _
  have hne : E₁ + E₂ + 1 ≠ 0 := add_one_ne_zero h12
  refine ⟨E₁ + E₂ + 1, max c₁ c₂ + norm (Wpow E₁) + norm (Wpow E₂), hE, hne, hlt₁, hlt₂, ?_⟩
  intro z
  have harg₁ : z + c₁ ≤ z + (max c₁ c₂ + norm (Wpow E₁) + norm (Wpow E₂)) := by omega
  have harg₂ : z + c₂ ≤ z + (max c₁ c₂ + norm (Wpow E₁) + norm (Wpow E₂)) := by omega
  have hgate₁ : norm (Wpow E₁)
      ≤ z + (max c₁ c₂ + norm (Wpow E₁) + norm (Wpow E₂)) := by omega
  have hgate₂ : norm (Wpow E₂)
      ≤ z + (max c₁ c₂ + norm (Wpow E₁) + norm (Wpow E₂)) := by omega
  have hb₁ : f z ≤ hardy (Wpow (E₁ + E₂ + 1))
      (z + (max c₁ c₂ + norm (Wpow E₁) + norm (Wpow E₂))) :=
    le_trans (hf z) (le_trans (hardy_monotone _ harg₁)
      (hardy_le_of_lt (Wpow_NF hE₁) (Wpow_NF hE) (Wpow_lt hlt₁) hgate₁))
  have hb₂ : g z ≤ hardy (Wpow (E₁ + E₂ + 1))
      (z + (max c₁ c₂ + norm (Wpow E₁) + norm (Wpow E₂))) :=
    le_trans (hg z) (le_trans (hardy_monotone _ harg₂)
      (hardy_le_of_lt (Wpow_NF hE₂) (Wpow_NF hE) (Wpow_lt hlt₂) hgate₂))
  exact max_le hb₁ hb₂

/-- **The `S*`-domination:** The concrete pipeline slot is padded-Hardy-dominated at one fixed level. -/
theorem Sstar_dom_pad (e : ONote) (he : e.NF) (m K d : ℕ) (α : ONote) (hα : α.NF)
    {P : ℕ → ℕ} {E₀ : ONote} (hE₀ : E₀.NF) {k V : ℕ}
    (hP : ∀ z, P z ≤ (hardy (Wpow E₀))^[k] (max V z)) :
    ∃ (E : ONote) (c : ℕ), E.NF ∧ E ≠ 0 ∧
      ∀ z, max (ewIterTower (rel1 (ewRootSlot e m) K) d α z) (P z)
        ≤ hardy (Wpow E) (z + c) := by
  haveI := he
  haveI h1 : (e + 1).NF := ONote.add_nf e 1
  haveI : (2 : ONote).NF := nf_ofNat 2
  haveI hL : ((e + 1) + 2).NF := ONote.add_nf (e + 1) 2
  have hL0 : (e + 1) + 2 ≠ 0 := by
    intro h
    have hh := congrArg ONote.repr h
    rw [ONote.repr_add (e + 1) 2,
      show ((2 : ONote)).repr = ((2 : ℕ) : Ordinal) from repr_ofNat 2, repr_zero] at hh
    push_cast at hh
    exact (lt_of_lt_of_le zero_lt_two le_add_self).ne' hh
  have hrel1 := rel1_dom_pad (ewRootSlot_dom_pad e he m) K
  obtain ⟨E₁, c₁, hE₁, hE₁0, htower⟩ := ewIterTower_dom_pad hL hL0 hrel1 α hα d
  obtain ⟨E₂, c₂, hE₂, hE₂0, _hlt, hiter⟩ := hardy_Wpow_iter_dom_pad E₀ hE₀ k
  have hPdom : ∀ z, P z ≤ hardy (Wpow E₂) (z + (V + c₂)) := by
    intro z
    have hz : P z ≤ (hardy (Wpow E₀))^[k] (z + V) :=
      le_trans (hP z) ((hardy_monotone (Wpow E₀)).iterate k (by omega))
    exact le_trans hz (le_trans (hiter (z + V)) (hardy_monotone _ (by omega)))
  obtain ⟨E, c, hE, hE0, _, _, hmax⟩ := dom_pad_max hE₁ hE₂ htower hPdom
  exact ⟨E, c, hE, hE0, hmax⟩

/-- **Padded-domination composition:** Padded-Hardy-dominated functions compose at level `E₁+E₂+1+1`. -/
theorem dom_pad_comp {f g : ℕ → ℕ} {E₁ E₂ : ONote} {c₁ c₂ : ℕ}
    (hE₁ : E₁.NF) (hE₂ : E₂.NF)
    (hf : ∀ z, f z ≤ hardy (Wpow E₁) (z + c₁))
    (hg : ∀ z, g z ≤ hardy (Wpow E₂) (z + c₂)) :
    ∃ (E : ONote) (c : ℕ), E.NF ∧ E ≠ 0 ∧
      ∀ z, f (g z) ≤ hardy (Wpow E) (z + c) := by
  haveI := hE₁
  haveI := hE₂
  haveI h12 : (E₁ + E₂).NF := ONote.add_nf E₁ E₂
  haveI hA : (E₁ + E₂ + 1).NF := ONote.add_nf (E₁ + E₂) 1
  haveI hE : (E₁ + E₂ + 1 + 1).NF := ONote.add_nf (E₁ + E₂ + 1) 1
  haveI hWA : (Wpow (E₁ + E₂ + 1)).NF := Wpow_NF hA
  haveI hWE₂ : (Wpow E₂).NF := Wpow_NF hE₂
  haveI hsum : (Wpow (E₁ + E₂ + 1) + Wpow E₂).NF := ONote.add_nf _ _
  have hrepr : (E₁ + E₂ + 1).repr = E₁.repr + E₂.repr + 1 := by
    rw [repr_add_one h12, ONote.repr_add E₁ E₂]
  have hlt₁ : E₁ < E₁ + E₂ + 1 := by
    rw [lt_def, hrepr]
    calc E₁.repr ≤ E₁.repr + E₂.repr := le_self_add
      _ < E₁.repr + E₂.repr + 1 := lt_add_one _
  have hlt₂ : E₂ < E₁ + E₂ + 1 := by
    rw [lt_def, hrepr]
    calc E₂.repr ≤ E₁.repr + E₂.repr := le_add_self
      _ < E₁.repr + E₂.repr + 1 := lt_add_one _
  have hne : E₁ + E₂ + 1 + 1 ≠ 0 := add_one_ne_zero hA
  refine ⟨E₁ + E₂ + 1 + 1,
    c₁ + c₂ + norm (Wpow E₁) + norm (Wpow (E₁ + E₂ + 1) + Wpow E₂),
    hE, hne, ?_⟩
  intro z
  have h1 : f (g z) ≤ hardy (Wpow E₁) (g z + c₁) := hf (g z)
  have h2 : g z + c₁ ≤ hardy (Wpow E₂) (z + c₂) + c₁ := by
    have := hg z
    omega
  have h3 : hardy (Wpow E₂) (z + c₂) + c₁ ≤ hardy (Wpow E₂) (z + c₂ + c₁) :=
    hardy_arg_add _ _ _
  have h4 : hardy (Wpow E₂) (z + c₂ + c₁) ≤ hardy (Wpow E₂)
      (z + (c₁ + c₂ + norm (Wpow E₁) + norm (Wpow (E₁ + E₂ + 1) + Wpow E₂))) :=
    hardy_monotone _ (by omega)
  have hY : f (g z) ≤ hardy (Wpow E₁) (hardy (Wpow E₂)
      (z + (c₁ + c₂ + norm (Wpow E₁) + norm (Wpow (E₁ + E₂ + 1) + Wpow E₂)))) :=
    le_trans h1 (hardy_monotone _ (le_trans h2 (le_trans h3 h4)))
  have hgate₁ : norm (Wpow E₁) ≤ hardy (Wpow E₂)
      (z + (c₁ + c₂ + norm (Wpow E₁) + norm (Wpow (E₁ + E₂ + 1) + Wpow E₂))) := by
    have := le_hardy (Wpow E₂)
      (z + (c₁ + c₂ + norm (Wpow E₁) + norm (Wpow (E₁ + E₂ + 1) + Wpow E₂)))
    omega
  have hraise : hardy (Wpow E₁) (hardy (Wpow E₂)
        (z + (c₁ + c₂ + norm (Wpow E₁) + norm (Wpow (E₁ + E₂ + 1) + Wpow E₂))))
      ≤ hardy (Wpow (E₁ + E₂ + 1)) (hardy (Wpow E₂)
        (z + (c₁ + c₂ + norm (Wpow E₁) + norm (Wpow (E₁ + E₂ + 1) + Wpow E₂)))) :=
    hardy_le_of_lt (Wpow_NF hE₁) (Wpow_NF hA) (Wpow_lt hlt₁) hgate₁
  have hcol := hardy_double_collapse hA hE₂ hlt₂
      (z + (c₁ + c₂ + norm (Wpow E₁) + norm (Wpow (E₁ + E₂ + 1) + Wpow E₂)))
  have hfin : hardy (Wpow (E₁ + E₂ + 1) + Wpow E₂)
        (z + (c₁ + c₂ + norm (Wpow E₁) + norm (Wpow (E₁ + E₂ + 1) + Wpow E₂)))
      ≤ hardy (Wpow (E₁ + E₂ + 1 + 1))
        (z + (c₁ + c₂ + norm (Wpow E₁) + norm (Wpow (E₁ + E₂ + 1) + Wpow E₂))) :=
    hardy_le_of_lt hsum (Wpow_NF hE) (Wpow_add_lt_Wpow_succ hA hE₂ hlt₂) (by omega)
  calc f (g z) ≤ _ := hY
    _ ≤ _ := hraise
    _ = _ := hcol
    _ ≤ _ := hfin

/-- `2^x` sits under `H_{ω²}` — the floor fact connecting `Nlog` certificate to `norm` gate. -/
lemma two_pow_le_hardy_Wpow2 (x : ℕ) : 2 ^ x ≤ hardy (Wpow (ofNat 2)) x := by
  have h := hardy_omega_pow_ofNat 2 x
  have h2 : fastGrowing (ofNat 2) (x + 1) = 2 ^ (x + 1) * (x + 1) := by
    rw [show (ofNat 2 : ONote) = 2 from rfl, ONote.fastGrowing_two]
  rw [h2] at h
  show 2 ^ x ≤ hardy (oadd (ofNat 2) 1 0) x
  have hexp : 2 ^ (x + 1) = 2 * 2 ^ x := by rw [pow_succ]; ring
  have hone : 1 ≤ 2 ^ x := Nat.one_le_two_pow
  have hmul : 2 * 2 ^ x * 1 ≤ 2 * 2 ^ x * (x + 1) :=
    Nat.mul_le_mul_left _ (by omega)
  rw [hexp] at h
  omega

/-- **The `a'`-uniform level cap:** The bound caps at fixed level `ω^{e₀+2+1+γ+1}` uniformly in `a' ≤ γ`. -/
theorem ewIter_dom_pad_levelcap {f : ℕ → ℕ} {e₀ γ : ONote} {c : ℕ}
    (he₀ : e₀.NF) (he₀0 : e₀ ≠ 0) (hγ : γ.NF)
    (hdom : ∀ z, f z ≤ hardy (Wpow e₀) (z + c)) :
    ∃ q : ℕ, ∀ (a' : ONote), a'.NF → a' ≤ γ → ∀ x,
      ewIter f a' x
        ≤ hardy (Wpow (e₀ + 2 + 1 + γ + 1))
            (hardy (Wpow (e₀ + 2)) (Nlog a' + x + q)) := by
  haveI := he₀
  haveI : (2 : ONote).NF := nf_ofNat 2
  haveI hNFe2 : (e₀ + 2).NF := ONote.add_nf e₀ 2
  haveI hNFe21 : (e₀ + 2 + 1).NF := ONote.add_nf (e₀ + 2) 1
  haveI := hγ
  haveI hNFg : (e₀ + 2 + 1 + γ).NF := ONote.add_nf (e₀ + 2 + 1) γ
  haveI hNFL : (e₀ + 2 + 1 + γ + 1).NF := ONote.add_nf (e₀ + 2 + 1 + γ) 1
  have he₀pos : (1 : Ordinal) ≤ e₀.repr :=
    Order.one_le_iff_ne_zero.mpr
      (fun h0 => he₀0 (repr_inj.mp (by rw [h0, repr_zero])))
  refine ⟨(norm (e₀ + 1) + norm e₀ + normSum (e₀ + 2 + 1) + norm (e₀ + 2) + 8 + c)
      + (normSum (e₀ + 2 + 1) + 1) + 2, ?_⟩
  intro a' ha' hle x
  haveI := ha'
  haveI hNFA : (e₀ + 2 + 1 + a').NF := ONote.add_nf (e₀ + 2 + 1) a'
  have h0 := ewIter_hardy_le_of_dom_pad he₀ he₀0 hdom a' ha' x
  have h1 : ewIter f a' x
      ≤ hardy (Wpow (e₀ + 2 + 1 + a'))
          (hardy (Wpow (e₀ + 2))
            (Nlog a' + x + ((norm (e₀ + 1) + norm e₀ + normSum (e₀ + 2 + 1)
              + norm (e₀ + 2) + 8 + c) + (normSum (e₀ + 2 + 1) + 1) + 2))) :=
    le_trans h0 (hardy_monotone _ (hardy_monotone _ (by omega)))
  -- the inner Hardy value pays the outer norm gate
  have hY2 : 2 ^ (Nlog a' + x + ((norm (e₀ + 1) + norm e₀ + normSum (e₀ + 2 + 1)
        + norm (e₀ + 2) + 8 + c) + (normSum (e₀ + 2 + 1) + 1) + 2))
      ≤ hardy (Wpow (e₀ + 2)) (Nlog a' + x + ((norm (e₀ + 1) + norm e₀
        + normSum (e₀ + 2 + 1) + norm (e₀ + 2) + 8 + c)
        + (normSum (e₀ + 2 + 1) + 1) + 2)) := by
    refine le_trans (two_pow_le_hardy_Wpow2 _) ?_
    have hlt2 : (ofNat 2 : ONote) < e₀ + 2 := by
      rw [lt_def, ONote.repr_add e₀ 2, repr_ofNat,
        show ((2 : ONote)).repr = ((2 : ℕ) : Ordinal) from repr_ofNat 2]
      have h1lt : (1 : Ordinal) < e₀.repr + 1 := lt_of_le_of_lt he₀pos (lt_add_one _)
      have hsucc : (1 : Ordinal) + 1 < (e₀.repr + 1) + 1 := by
        rw [← Order.succ_eq_add_one, ← Order.succ_eq_add_one]
        exact Order.succ_lt_succ h1lt
      calc ((2 : ℕ) : Ordinal) = 1 + 1 := by push_cast; exact one_add_one_eq_two.symm
        _ < (e₀.repr + 1) + 1 := hsucc
        _ = e₀.repr + ((2 : ℕ) : Ordinal) := by
            rw [add_assoc, one_add_one_eq_two]; push_cast; rfl
    have hn2 : norm (Wpow (ofNat 2)) = 2 := by
      simp [Wpow, ofNat_succ, norm_oadd]
    exact hardy_le_of_lt (Wpow_NF (nf_ofNat 2)) (Wpow_NF hNFe2) (Wpow_lt hlt2)
      (by rw [hn2]; omega)
  have hnormW : norm (Wpow (e₀ + 2 + 1 + a'))
      ≤ normSum (e₀ + 2 + 1) + norm a' + 1 := by
    show norm (oadd (e₀ + 2 + 1 + a') 1 0) ≤ _
    rw [norm_oadd]
    have hna := norm_add_le (e₀ + 2 + 1) a'
    simp only [norm_zero, PNat.one_coe]
    omega
  have hnorm_a : norm a' < 2 ^ (Nlog a' + 1) := norm_lt_two_pow_Nlog a'
  -- 2-power arithmetic: P·q pays K₀ + P
  have hgate : norm (Wpow (e₀ + 2 + 1 + a'))
      ≤ hardy (Wpow (e₀ + 2)) (Nlog a' + x + ((norm (e₀ + 1) + norm e₀
        + normSum (e₀ + 2 + 1) + norm (e₀ + 2) + 8 + c)
        + (normSum (e₀ + 2 + 1) + 1) + 2)) := by
    refine le_trans hnormW (le_trans ?_ hY2)
    · -- normSum(e₀+2+1) + norm a' + 1 ≤ 2^(Nlog a' + x + q)
      have hsplit : 2 ^ ((Nlog a' + 1) + ((norm (e₀ + 1) + norm e₀
            + normSum (e₀ + 2 + 1) + norm (e₀ + 2) + 8 + c)
            + (normSum (e₀ + 2 + 1) + 1) + 1))
          ≤ 2 ^ (Nlog a' + x + ((norm (e₀ + 1) + norm e₀
            + normSum (e₀ + 2 + 1) + norm (e₀ + 2) + 8 + c)
            + (normSum (e₀ + 2 + 1) + 1) + 2)) :=
        Nat.pow_le_pow_right (by omega) (by omega)
      have hpow_add : 2 ^ ((Nlog a' + 1) + ((norm (e₀ + 1) + norm e₀
            + normSum (e₀ + 2 + 1) + norm (e₀ + 2) + 8 + c)
            + (normSum (e₀ + 2 + 1) + 1) + 1))
          = 2 ^ (Nlog a' + 1) * 2 ^ ((norm (e₀ + 1) + norm e₀
            + normSum (e₀ + 2 + 1) + norm (e₀ + 2) + 8 + c)
            + (normSum (e₀ + 2 + 1) + 1) + 1) := pow_add 2 _ _
      have hP2 : 2 ≤ 2 ^ (Nlog a' + 1) := by
        calc 2 = 2 ^ 1 := rfl
          _ ≤ 2 ^ (Nlog a' + 1) := Nat.pow_le_pow_right (by omega) (by omega)
      have hQq : (norm (e₀ + 1) + norm e₀ + normSum (e₀ + 2 + 1) + norm (e₀ + 2) + 8 + c)
            + (normSum (e₀ + 2 + 1) + 1) + 1
          ≤ 2 ^ ((norm (e₀ + 1) + norm e₀ + normSum (e₀ + 2 + 1) + norm (e₀ + 2) + 8 + c)
            + (normSum (e₀ + 2 + 1) + 1) + 1) :=
        Nat.le_of_lt Nat.lt_two_pow_self
      have hmul : 2 ^ (Nlog a' + 1) * ((norm (e₀ + 1) + norm e₀
            + normSum (e₀ + 2 + 1) + norm (e₀ + 2) + 8 + c)
            + (normSum (e₀ + 2 + 1) + 1) + 1)
          ≤ 2 ^ (Nlog a' + 1) * 2 ^ ((norm (e₀ + 1) + norm e₀
            + normSum (e₀ + 2 + 1) + norm (e₀ + 2) + 8 + c)
            + (normSum (e₀ + 2 + 1) + 1) + 1) :=
        Nat.mul_le_mul_left _ hQq
      have hexpand : 2 ^ (Nlog a' + 1) * ((norm (e₀ + 1) + norm e₀
            + normSum (e₀ + 2 + 1) + norm (e₀ + 2) + 8 + c)
            + (normSum (e₀ + 2 + 1) + 1) + 1)
          = 2 ^ (Nlog a' + 1) * (norm (e₀ + 1) + norm e₀
            + normSum (e₀ + 2 + 1) + norm (e₀ + 2) + 8 + c)
            + 2 ^ (Nlog a' + 1) * (normSum (e₀ + 2 + 1) + 1)
            + 2 ^ (Nlog a' + 1) := by ring
      have hK : normSum (e₀ + 2 + 1) + 1
          ≤ 2 ^ (Nlog a' + 1) * (normSum (e₀ + 2 + 1) + 1) :=
        Nat.le_mul_of_pos_left _ (by omega)
      omega
  exact le_trans h1 (hardy_le_of_lt (Wpow_NF hNFA) (Wpow_NF hNFL)
    (Wpow_lt (by
      rw [lt_def, ONote.repr_add (e₀ + 2 + 1) a',
        show (e₀ + 2 + 1 + γ + 1).repr = (e₀ + 2 + 1).repr + γ.repr + 1 by
          rw [ONote.repr_add (e₀ + 2 + 1 + γ) 1, ONote.repr_add (e₀ + 2 + 1) γ,
            ONote.repr_one]
          push_cast
          rfl]
      calc (e₀ + 2 + 1).repr + a'.repr
          ≤ (e₀ + 2 + 1).repr + γ.repr := (add_le_add_iff_left _).mpr (repr_le_repr hle)
        _ < (e₀ + 2 + 1).repr + γ.repr + 1 := lt_add_one _))
    hgate)

/-- **Padded Hardy eventually under one fastGrowing level:** `H_{ω^L}(m+C) < f_{osucc L}(m)` for `m ≥ C+3`. -/
theorem hardy_pad_lt_fastGrowing_osucc (L : ONote) (hL : L.NF) (C m : ℕ) (hm : C + 3 ≤ m) :
    hardy (Wpow L) (m + C) < fastGrowing (osucc L) m := by
  have h1 : hardy (Wpow L) (m + C) < fastGrowing L (m + C + 1) :=
    hardy_omega_pow_lt_fastGrowing L (m + C)
  have hA : ∀ j, m + j ≤ (fastGrowing L)^[j] m := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
        rw [Function.iterate_succ_apply']
        have hge1 : 1 ≤ (fastGrowing L)^[j] m := by omega
        have := lt_fastGrowing L hge1
        omega
  have hB : fastGrowing L (m + C + 1) ≤ (fastGrowing L)^[C + 2] m := by
    rw [Function.iterate_succ_apply']
    exact fastGrowing_monotone L (hA (C + 1))
  have hC : (fastGrowing L)^[C + 2] m ≤ (fastGrowing L)^[m] m :=
    Function.monotone_iterate_of_id_le (fun x => le_fastGrowing L x) (by omega) m
  have hD : fastGrowing (osucc L) m = (fastGrowing L)^[m] m := by
    rw [fastGrowing_succ _ (fundamentalSequence_osucc hL)]
  omega

/-- The eventual-domination package: a padded-Hardy-dominated function sits eventually under one fixed `fastGrowing` level. -/
theorem dom_pad_eventuallyLE {f : ℕ → ℕ} {L : ONote} {C : ℕ} (hL : L.NF)
    (hdom : ∀ m, f m ≤ hardy (Wpow L) (m + C)) :
    ∃ o : ONote, o.NF ∧ ∃ N, ∀ m, N ≤ m → f m ≤ fastGrowing o m :=
  ⟨osucc L, osucc_NF hL, C + 3, fun m hm =>
    le_trans (hdom m) (le_of_lt (hardy_pad_lt_fastGrowing_osucc L hL C m hm))⟩

/-- **The fixed pipeline slot `S°` is padded-Hardy-dominated** with concrete `P = Gexp^[k]`. -/
theorem Scirc_dom_pad (e : ONote) (he : e.NF) (Bb d k : ℕ) (α : ONote) (hα : α.NF) :
    ∃ (E : ONote) (c : ℕ), E.NF ∧ E ≠ 0 ∧
      ∀ z, max (ewIterTower (ewRootSlot e Bb) d α z)
          ((hardy (oadd (ofNat 2) 1 0))^[k] z)
        ≤ hardy (oadd E 1 0) (z + c) := by
  haveI := he
  haveI : (2 : ONote).NF := nf_ofNat 2
  haveI h1 : (e + 1).NF := ONote.add_nf e 1
  haveI hL : ((e + 1) + 2).NF := ONote.add_nf (e + 1) 2
  have hL0 : (e + 1) + 2 ≠ 0 := by
    intro h
    have hh := congrArg ONote.repr h
    rw [ONote.repr_add (e + 1) 2,
      show ((2 : ONote)).repr = ((2 : ℕ) : Ordinal) from repr_ofNat 2, repr_zero] at hh
    push_cast at hh
    exact (lt_of_lt_of_le zero_lt_two le_add_self).ne' hh
  obtain ⟨E₁, c₁, hE₁, hE₁0, htower⟩ :=
    ewIterTower_dom_pad hL hL0 (ewRootSlot_dom_pad e he Bb) α hα d
  obtain ⟨E₂, c₂, hE₂, hE₂0, _, hiter⟩ := hardy_Wpow_iter_dom_pad (ofNat 2) (nf_ofNat 2) k
  have hiter' : ∀ z, (hardy (oadd (ofNat 2) 1 0))^[k] z ≤ hardy (Wpow E₂) (z + c₂) := hiter
  obtain ⟨E, c, hE, hE0, _, _, hmax⟩ := dom_pad_max hE₁ hE₂ htower hiter'
  exact ⟨E, c, hE, hE0, hmax⟩

/-- `2y + q` sits under `H_{ω²}(y)` once `y ≥ max(q,1)` (the Hardy value is `≥ 4y+3`). -/
lemma two_mul_add_le_hardy_omega_sq {y q : ℕ} (hq : q ≤ y) (hy : 1 ≤ y) :
    2 * y + q ≤ hardy (oadd (ofNat 2) 1 0) y := by
  have h := hardy_omega_pow_ofNat 2 y
  have h2 : fastGrowing (ofNat 2) (y + 1) = 2 ^ (y + 1) * (y + 1) := by
    rw [show (ofNat 2 : ONote) = 2 from rfl, ONote.fastGrowing_two]
  rw [h2] at h
  have h4 : 4 ≤ 2 ^ (y + 1) := by
    calc 4 = 2 ^ 2 := rfl
      _ ≤ 2 ^ (y + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have hmul : 4 * (y + 1) ≤ 2 ^ (y + 1) * (y + 1) := Nat.mul_le_mul_right _ h4
  omega

/-- **The master conversion:** Given any slot `S` padded-Hardy-dominated and inflationary, one fixed `fastGrowing o` eventually dominates the read-off. -/
theorem master_conversion {S : ℕ → ℕ} {E_S γ : ONote} {c_S : ℕ}
    (hES : E_S.NF) (hES0 : E_S ≠ 0) (hγ : γ.NF)
    (hSdom : ∀ z, S z ≤ hardy (oadd E_S 1 0) (z + c_S))
    (hSinfl : ∀ z, z ≤ S z) (K₀ : ℕ) :
    ∃ o : ONote, o.NF ∧ ∃ N : ℕ, ∀ m, N ≤ m →
      ∀ a' : ONote, a'.NF → a' ≤ γ → ∀ n : ℕ,
        Nlog a' ≤ S (max K₀ m) →
        n ≤ ewIter S a' (S (max K₀ m)) →
        n ≤ fastGrowing o m := by
  haveI := hES
  haveI : (2 : ONote).NF := nf_ofNat 2
  haveI hNF2 : (E_S + 2).NF := ONote.add_nf E_S 2
  haveI hNF21 : (E_S + 2 + 1).NF := ONote.add_nf (E_S + 2) 1
  haveI := hγ
  haveI hNFg : (E_S + 2 + 1 + γ).NF := ONote.add_nf (E_S + 2 + 1) γ
  haveI hNFL : (E_S + 2 + 1 + γ + 1).NF := ONote.add_nf (E_S + 2 + 1 + γ) 1
  have hSdom' : ∀ z, S z ≤ hardy (Wpow E_S) (z + c_S) := hSdom
  obtain ⟨q, hq⟩ := ewIter_dom_pad_levelcap hES hES0 hγ hSdom'
  -- composition chain: Gexp ∘ (H_{E_S}(·+K₀+c_S)) → E₃; H_{E_S+2} ∘ E₃ → E₄; H_LL ∘ E₄ → E₅
  obtain ⟨E₃, c₃, hE₃, hE₃0, hcomp₁⟩ :=
    dom_pad_comp (f := hardy (Wpow (ofNat 2))) (g := fun z => hardy (Wpow E_S) (z + (K₀ + c_S)))
      (c₁ := 0) (c₂ := K₀ + c_S)
      (nf_ofNat 2) hES (fun z => by simp) (fun z => le_rfl)
  obtain ⟨E₄, c₄, hE₄, hE₄0, hcomp₂⟩ :=
    dom_pad_comp (f := hardy (Wpow (E_S + 2))) (g := fun z => hardy (Wpow E₃) (z + c₃))
      (c₁ := 0) (c₂ := c₃)
      hNF2 hE₃ (fun z => by simp) (fun z => le_rfl)
  obtain ⟨E₅, c₅, hE₅, hE₅0, hcomp₃⟩ :=
    dom_pad_comp (f := hardy (Wpow (E_S + 2 + 1 + γ + 1))) (g := fun z => hardy (Wpow E₄) (z + c₄))
      (c₁ := 0) (c₂ := c₄)
      hNFL hE₄ (fun z => by simp) (fun z => le_rfl)
  refine ⟨osucc E₅, osucc_NF hE₅, q + c₅ + 3, ?_⟩
  intro m hm a' ha' hle n hNcert hn
  -- the m-side value x := S (max K₀ m)
  have hx_ge : max K₀ m ≤ S (max K₀ m) := hSinfl _
  have hx_ge_m : m ≤ S (max K₀ m) := le_trans (le_max_right _ _) hx_ge
  have hx_ge_q : q ≤ S (max K₀ m) := le_trans (by omega) hx_ge_m
  have hx_ge_1 : 1 ≤ S (max K₀ m) := le_trans (by omega) hx_ge_m
  -- inner argument absorbed into Gexp x
  have hinner : Nlog a' + S (max K₀ m) + q ≤ 2 * S (max K₀ m) + q := by omega
  have hinner₂ : 2 * S (max K₀ m) + q ≤ hardy (oadd (ofNat 2) 1 0) (S (max K₀ m)) :=
    two_mul_add_le_hardy_omega_sq hx_ge_q hx_ge_1
  -- x ≤ H_{E_S}(m + (K₀ + c_S))
  have hx_dom : S (max K₀ m) ≤ hardy (Wpow E_S) (m + (K₀ + c_S)) :=
    le_trans (hSdom' _) (hardy_monotone _ (by omega))
  have hGx : hardy (oadd (ofNat 2) 1 0) (S (max K₀ m))
      ≤ hardy (Wpow (ofNat 2)) (hardy (Wpow E_S) (m + (K₀ + c_S))) :=
    hardy_monotone _ hx_dom
  have hE₃b : hardy (Wpow (ofNat 2)) (hardy (Wpow E_S) (m + (K₀ + c_S)))
      ≤ hardy (Wpow E₃) (m + c₃) := hcomp₁ m
  -- assemble
  have hmain := hq a' ha' hle (S (max K₀ m))
  have hstep1 : hardy (Wpow (E_S + 2)) (Nlog a' + S (max K₀ m) + q)
      ≤ hardy (Wpow (E_S + 2)) (hardy (Wpow E₃) (m + c₃)) :=
    hardy_monotone _ (le_trans hinner (le_trans hinner₂ (le_trans hGx hE₃b)))
  have hstep2 : hardy (Wpow (E_S + 2)) (hardy (Wpow E₃) (m + c₃))
      ≤ hardy (Wpow E₄) (m + c₄) := hcomp₂ m
  have hstep3 : hardy (Wpow (E_S + 2 + 1 + γ + 1)) (hardy (Wpow E₄) (m + c₄))
      ≤ hardy (Wpow E₅) (m + c₅) := hcomp₃ m
  have hchain : ewIter S a' (S (max K₀ m)) ≤ hardy (Wpow E₅) (m + c₅) :=
    le_trans hmain (le_trans (hardy_monotone _ (le_trans hstep1 hstep2)) hstep3)
  have hfin : hardy (Wpow E₅) (m + c₅) < fastGrowing (osucc E₅) m :=
    hardy_pad_lt_fastGrowing_osucc E₅ hE₅ c₅ m (by omega)
  omega


end ONote
