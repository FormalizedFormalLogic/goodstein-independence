import GoodsteinPA.InternalONote

namespace GoodsteinPA.InternalONote
open Classical
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.HierarchySymbol
open GoodsteinPA.InternalPow
variable {V : Type*} [ORingStructure V] [V ⊧ₘ* 𝗜𝚺₁]

/-- **Destructor**: a positive code is the `ocOadd` of its decoded parts. -/
lemma ocOadd_destruct {c : V} (hc : c ≠ 0) :
    ocOadd (ocExp c) (ocCoeff c) (ocTail c) = c := by
  have hpos : 0 < c := pos_iff_ne_zero.mpr hc
  unfold ocOadd ocExp ocCoeff ocTail fstIdx sndIdx
  rw [pair_unpair, pair_unpair]
  exact sub_add_self_of_le (pos_iff_one_le.mp hpos)

/-! ### `thenV` / `cmpV` value lemmas -/

lemma thenV_eq_one {a b : V} : thenV a b = 1 ↔ a = 1 ∧ b = 1 := by
  unfold thenV; by_cases h : a = 1 <;> simp [h]

lemma thenV_eq_zero {a b : V} : thenV a b = 0 ↔ a = 0 ∨ (a = 1 ∧ b = 0) := by
  unfold thenV; by_cases h : a = 1 <;> simp [h]

lemma cmpV_eq_zero {a b : V} : cmpV a b = 0 ↔ a < b := by
  unfold cmpV
  by_cases h : a < b
  · simp [h]
  · simp only [h, if_false]; by_cases h2 : a = b <;> simp [h, h2]

lemma cmpV_eq_one {a b : V} : cmpV a b = 1 ↔ a = b := by
  unfold cmpV
  by_cases h : a < b
  · simp only [if_pos h]
    constructor
    · intro h0; simp at h0
    · rintro rfl; exact absurd h (_root_.lt_irrefl a)
  · by_cases h2 : a = b
    · subst h2; simp
    · simp [h, h2]

/-! ### Positivity & the tail-bound ⟹ whole-bound step -/

/-- A nonzero NF code has positive value. -/
lemma ievalNat_pos {b c : V} (hnf : isNF c) (hc : c ≠ 0) : 0 < ievalNat b c := by
  obtain ⟨e, n, r, rfl⟩ : ∃ e n r, c = ocOadd e n r :=
    ⟨ocExp c, ocCoeff c, ocTail c, (ocOadd_destruct hc).symm⟩
  rw [ievalNat_ocOadd]
  have hn : n ≠ 0 := ((isNF_ocOadd e n r).1 hnf).1
  have hnp : 0 < n := pos_iff_ne_zero.mpr hn
  have hp : 0 < ipow (b + 1) (ievalNat b e) := ipow_pos (by simp) _
  calc (0 : V) < n * ipow (b + 1) (ievalNat b e) := mul_pos hnp hp
    _ ≤ n * ipow (b + 1) (ievalNat b e) + ievalNat b r := le_self_add

/-- **Tail-bound ⟹ whole-bound.** If the tail value is below `(b+1)^E` (`E = ievalNat b (ocExp c)`)
then the whole code value is below `(b+1)^(E+1)`. Uses `n ≤ b` (`iCanon`). -/
lemma tb_imp_bd {b c : V} (hnf : isNF c) (hcanon : iCanon b c) (hc : c ≠ 0)
    (htb : ievalNat b (ocTail c) < ipow (b + 1) (ievalNat b (ocExp c))) :
    ievalNat b c < ipow (b + 1) (ievalNat b (ocExp c) + 1) := by
  obtain ⟨e, n, r, rfl⟩ : ∃ e n r, c = ocOadd e n r :=
    ⟨ocExp c, ocCoeff c, ocTail c, (ocOadd_destruct hc).symm⟩
  rw [ievalNat_ocOadd, ocExp_ocOadd] at *
  rw [ocTail_ocOadd] at htb
  set E := ievalNat b e with hE
  have hn : n ≤ b := ((iCanon_ocOadd b e n r).1 hcanon).1
  have hpe : 0 < ipow (b + 1) E := ipow_pos (by simp) _
  rw [ipow_succ]
  calc n * ipow (b + 1) E + ievalNat b r
      < n * ipow (b + 1) E + ipow (b + 1) E := by gcongr
    _ = (n + 1) * ipow (b + 1) E := by rw [add_mul, one_mul]
    _ ≤ (b + 1) * ipow (b + 1) E := by gcongr
    _ = ipow (b + 1) E * (b + 1) := by rw [mul_comm]

/-! ### Subterm NF/Canon projections -/

private lemma isNF_ocExp {c : V} (h : isNF c) (hc : c ≠ 0) : isNF (ocExp c) := by
  have := (isNF_ocOadd (ocExp c) (ocCoeff c) (ocTail c)).1 (by rw [ocOadd_destruct hc]; exact h)
  exact this.2.1

private lemma isNF_ocTail {c : V} (h : isNF c) (hc : c ≠ 0) : isNF (ocTail c) := by
  have := (isNF_ocOadd (ocExp c) (ocCoeff c) (ocTail c)).1 (by rw [ocOadd_destruct hc]; exact h)
  exact this.2.2.1

private lemma coeff_ne_zero {c : V} (h : isNF c) (hc : c ≠ 0) : ocCoeff c ≠ 0 := by
  have := (isNF_ocOadd (ocExp c) (ocCoeff c) (ocTail c)).1 (by rw [ocOadd_destruct hc]; exact h)
  exact this.1

private lemma tailExp_cond {c : V} (h : isNF c) (hc : c ≠ 0) :
    ocTail c = 0 ∨ icmp (ocExp (ocTail c)) (ocExp c) = 0 := by
  have := (isNF_ocOadd (ocExp c) (ocCoeff c) (ocTail c)).1 (by rw [ocOadd_destruct hc]; exact h)
  exact this.2.2.2

private lemma iCanon_ocExp {b c : V} (h : iCanon b c) (hc : c ≠ 0) : iCanon b (ocExp c) := by
  have := (iCanon_ocOadd b (ocExp c) (ocCoeff c) (ocTail c)).1 (by rw [ocOadd_destruct hc]; exact h)
  exact this.2.1

private lemma iCanon_ocTail {b c : V} (h : iCanon b c) (hc : c ≠ 0) : iCanon b (ocTail c) := by
  have := (iCanon_ocOadd b (ocExp c) (ocCoeff c) (ocTail c)).1 (by rw [ocOadd_destruct hc]; exact h)
  exact this.2.2

private lemma coeff_le {b c : V} (h : iCanon b c) (hc : c ≠ 0) : ocCoeff c ≤ b := by
  have := (iCanon_ocOadd b (ocExp c) (ocCoeff c) (ocTail c)).1 (by rw [ocOadd_destruct hc]; exact h)
  exact this.1

/-! ### `icmp` reflects equality -/

private lemma code_lt_of_exp {e n r w : V} (h : ocOadd e n r ≤ w) : e < w := by
  have : e < ocOadd e n r := by have := ocExp_lt e n r; rwa [ocExp_ocOadd] at this
  exact lt_of_lt_of_le this h

private lemma code_lt_of_tail {e n r w : V} (h : ocOadd e n r ≤ w) : r < w := by
  have : r < ocOadd e n r := by have := ocTail_lt e n r; rwa [ocTail_ocOadd] at this
  exact lt_of_lt_of_le this h

theorem icmp_eq_imp_eq : ∀ w : V, ∀ a ≤ w, ∀ c ≤ w, icmp a c = 1 → a = c := by
  intro w
  induction w using ISigma1.sigma1_order_induction
  · definability
  case ind w ih =>
    intro a haw c hcw hcmp
    rcases eq_or_ne a 0 with rfl | ha
    · rcases eq_or_ne c 0 with rfl | hc
      · rfl
      · obtain ⟨e, n, r, rfl⟩ : ∃ e n r, c = ocOadd e n r :=
          ⟨ocExp c, ocCoeff c, ocTail c, (ocOadd_destruct hc).symm⟩
        rw [icmp_zero_ocOadd] at hcmp; exact absurd hcmp (zero_ne_one)
    · rcases eq_or_ne c 0 with rfl | hc
      · obtain ⟨e, n, r, rfl⟩ : ∃ e n r, a = ocOadd e n r :=
          ⟨ocExp a, ocCoeff a, ocTail a, (ocOadd_destruct ha).symm⟩
        rw [icmp_ocOadd_zero] at hcmp; exact absurd hcmp (one_lt_two).ne'
      · obtain ⟨e1, n1, r1, rfl⟩ : ∃ e n r, a = ocOadd e n r :=
          ⟨ocExp a, ocCoeff a, ocTail a, (ocOadd_destruct ha).symm⟩
        obtain ⟨e2, n2, r2, rfl⟩ : ∃ e n r, c = ocOadd e n r :=
          ⟨ocExp c, ocCoeff c, ocTail c, (ocOadd_destruct hc).symm⟩
        rw [icmp_ocOadd, thenV_eq_one, thenV_eq_one] at hcmp
        obtain ⟨he, hn, hr⟩ := hcmp
        have he1w : e1 < w := code_lt_of_exp haw
        have he2w : e2 < w := code_lt_of_exp hcw
        have hr1w : r1 < w := code_lt_of_tail haw
        have hr2w : r2 < w := code_lt_of_tail hcw
        have hee : e1 = e2 :=
          ih (max e1 e2) (max_lt he1w he2w) e1 (le_max_left _ _) e2 (le_max_right _ _) he
        have hnn : n1 = n2 := cmpV_eq_one.mp hn
        have hrr : r1 = r2 :=
          ih (max r1 r2) (max_lt hr1w hr2w) r1 (le_max_left _ _) r2 (le_max_right _ _) hr
        rw [hee, hnn, hrr]

/-! ### The combined tail-bound + monotonicity induction -/

private def TBstmt (b c : V) : Prop :=
  isNF c → iCanon b c → c ≠ 0 →
    ievalNat b (ocTail c) < ipow (b + 1) (ievalNat b (ocExp c))

private def MONOstmt (b o p : V) : Prop :=
  isNF o → isNF p → iCanon b o → iCanon b p → icmp o p = 0 →
    ievalNat b o < ievalNat b p

private def Combined (b w : V) : Prop :=
  (∀ c ≤ w, TBstmt b c) ∧ (∀ o ≤ w, ∀ p ≤ w, MONOstmt b o p)

theorem evalNat_reflect_combined {b : V} (hb : 1 ≤ b) : ∀ w, Combined b w := by
  have hB1 : (1 : V) ≤ b + 1 := by simp
  intro w
  induction w using ISigma1.sigma1_order_induction
  · unfold Combined TBstmt MONOstmt; definability
  case ind w ih =>
    refine ⟨?tb, ?mono⟩
    case tb =>
      intro c hcw hnf hcanon hc0
      rcases eq_or_ne (ocTail c) 0 with hr0 | hr0
      · rw [hr0, ievalNat_zero]; exact ipow_pos (by simp) _
      · have hicmp : icmp (ocExp (ocTail c)) (ocExp c) = 0 := (tailExp_cond hnf hc0).resolve_left hr0
        have hnfr : isNF (ocTail c) := isNF_ocTail hnf hc0
        have hcanonr : iCanon b (ocTail c) := iCanon_ocTail hcanon hc0
        have htail_lt : ocTail c < c := ocTail_lt_of_pos (pos_iff_ne_zero.mpr hc0)
        have hrw : ocTail c < w := lt_of_lt_of_le htail_lt hcw
        have htbr : TBstmt b (ocTail c) := (ih (ocTail c) hrw).1 (ocTail c) le_rfl
        have hbdr : ievalNat b (ocTail c) < ipow (b + 1) (ievalNat b (ocExp (ocTail c)) + 1) :=
          tb_imp_bd hnfr hcanonr hr0 (htbr hnfr hcanonr hr0)
        -- E(ocExp (ocTail c)) < E(ocExp c) via MONO at smaller codes
        have hexpr_lt : ocExp (ocTail c) < w :=
          lt_of_lt_of_le (lt_trans (ocExp_lt_of_pos (pos_iff_ne_zero.mpr hr0)) htail_lt) hcw
        have hexpc_lt : ocExp c < w := lt_of_lt_of_le (ocExp_lt_of_pos (pos_iff_ne_zero.mpr hc0)) hcw
        have hmono : ievalNat b (ocExp (ocTail c)) < ievalNat b (ocExp c) :=
          (ih (max (ocExp (ocTail c)) (ocExp c)) (max_lt hexpr_lt hexpc_lt)).2
            (ocExp (ocTail c)) (le_max_left _ _) (ocExp c) (le_max_right _ _)
            (isNF_ocExp hnfr hr0) (isNF_ocExp hnf hc0) (iCanon_ocExp hcanonr hr0)
            (iCanon_ocExp hcanon hc0) hicmp
        calc ievalNat b (ocTail c)
            < ipow (b + 1) (ievalNat b (ocExp (ocTail c)) + 1) := hbdr
          _ ≤ ipow (b + 1) (ievalNat b (ocExp c)) :=
              ipow_le_ipow_right hB1 (lt_iff_succ_le.mp hmono)
    case mono =>
      -- TB component, available for codes ≤ w (proved above; re-derive as a local fact)
      have hTB : ∀ c ≤ w, TBstmt b c := by
        intro c hcw hnf hcanon hc0
        rcases eq_or_ne (ocTail c) 0 with hr0 | hr0
        · rw [hr0, ievalNat_zero]; exact ipow_pos (by simp) _
        · have hicmp : icmp (ocExp (ocTail c)) (ocExp c) = 0 :=
            (tailExp_cond hnf hc0).resolve_left hr0
          have hnfr : isNF (ocTail c) := isNF_ocTail hnf hc0
          have hcanonr : iCanon b (ocTail c) := iCanon_ocTail hcanon hc0
          have htail_lt : ocTail c < c := ocTail_lt_of_pos (pos_iff_ne_zero.mpr hc0)
          have hrw : ocTail c < w := lt_of_lt_of_le htail_lt hcw
          have htbr : TBstmt b (ocTail c) := (ih (ocTail c) hrw).1 (ocTail c) le_rfl
          have hbdr : ievalNat b (ocTail c) < ipow (b + 1) (ievalNat b (ocExp (ocTail c)) + 1) :=
            tb_imp_bd hnfr hcanonr hr0 (htbr hnfr hcanonr hr0)
          have hexpr_lt : ocExp (ocTail c) < w :=
            lt_of_lt_of_le (lt_trans (ocExp_lt_of_pos (pos_iff_ne_zero.mpr hr0)) htail_lt) hcw
          have hexpc_lt : ocExp c < w :=
            lt_of_lt_of_le (ocExp_lt_of_pos (pos_iff_ne_zero.mpr hc0)) hcw
          have hmono : ievalNat b (ocExp (ocTail c)) < ievalNat b (ocExp c) :=
            (ih (max (ocExp (ocTail c)) (ocExp c)) (max_lt hexpr_lt hexpc_lt)).2
              (ocExp (ocTail c)) (le_max_left _ _) (ocExp c) (le_max_right _ _)
              (isNF_ocExp hnfr hr0) (isNF_ocExp hnf hc0) (iCanon_ocExp hcanonr hr0)
              (iCanon_ocExp hcanon hc0) hicmp
          calc ievalNat b (ocTail c)
              < ipow (b + 1) (ievalNat b (ocExp (ocTail c)) + 1) := hbdr
            _ ≤ ipow (b + 1) (ievalNat b (ocExp c)) :=
                ipow_le_ipow_right hB1 (lt_iff_succ_le.mp hmono)
      intro o how p hpw hno hnp hco hcp hcmp
      rcases eq_or_ne o 0 with rfl | ho0
      · rcases eq_or_ne p 0 with rfl | hp0
        · rw [icmp_zero_zero] at hcmp; exact absurd hcmp _root_.one_ne_zero
        · rw [ievalNat_zero]; exact ievalNat_pos hnp hp0
      · rcases eq_or_ne p 0 with rfl | hp0
        · obtain ⟨e, n, r, rfl⟩ : ∃ e n r, o = ocOadd e n r :=
            ⟨ocExp o, ocCoeff o, ocTail o, (ocOadd_destruct ho0).symm⟩
          rw [icmp_ocOadd_zero] at hcmp; exact absurd hcmp (_root_.two_ne_zero)
        · obtain ⟨e1, n1, r1, rfl⟩ : ∃ e n r, o = ocOadd e n r :=
            ⟨ocExp o, ocCoeff o, ocTail o, (ocOadd_destruct ho0).symm⟩
          obtain ⟨e2, n2, r2, rfl⟩ : ∃ e n r, p = ocOadd e n r :=
            ⟨ocExp p, ocCoeff p, ocTail p, (ocOadd_destruct hp0).symm⟩
          obtain ⟨hn1, hne1, hnr1, _⟩ := (isNF_ocOadd e1 n1 r1).1 hno
          obtain ⟨hn2, hne2, hnr2, _⟩ := (isNF_ocOadd e2 n2 r2).1 hnp
          obtain ⟨hb1le, hbe1, hbr1⟩ := (iCanon_ocOadd b e1 n1 r1).1 hco
          obtain ⟨hb2le, hbe2, hbr2⟩ := (iCanon_ocOadd b e2 n2 r2).1 hcp
          have hn2pos : 1 ≤ n2 := pos_iff_one_le.mp (pos_iff_ne_zero.mpr hn2)
          -- tail bounds
          have htr1 : ievalNat b r1 < ipow (b + 1) (ievalNat b e1) := by
            have := hTB (ocOadd e1 n1 r1) how hno hco (ocOadd_ne_zero _ _ _)
            rwa [ocTail_ocOadd, ocExp_ocOadd] at this
          have htr2 : ievalNat b r2 < ipow (b + 1) (ievalNat b e2) := by
            have := hTB (ocOadd e2 n2 r2) hpw hnp hcp (ocOadd_ne_zero _ _ _)
            rwa [ocTail_ocOadd, ocExp_ocOadd] at this
          rw [icmp_ocOadd, thenV_eq_zero] at hcmp
          rw [ievalNat_ocOadd, ievalNat_ocOadd]
          set E1 := ievalNat b e1 with hE1
          set E2 := ievalNat b e2 with hE2
          have hpe1 : 0 < ipow (b + 1) E1 := ipow_pos (by simp) _
          have hpe2 : 0 < ipow (b + 1) E2 := ipow_pos (by simp) _
          rcases hcmp with he | ⟨he1, hinner⟩
          · -- icmp e1 e2 = 0 : E1 < E2, leading term of p dominates o
            have he1w : e1 < w := lt_of_lt_of_le (by have := ocExp_lt e1 n1 r1; rwa [ocExp_ocOadd] at this) how
            have he2w : e2 < w := lt_of_lt_of_le (by have := ocExp_lt e2 n2 r2; rwa [ocExp_ocOadd] at this) hpw
            have hElt : E1 < E2 :=
              (ih (max e1 e2) (max_lt he1w he2w)).2 e1 (le_max_left _ _) e2 (le_max_right _ _)
                hne1 hne2 hbe1 hbe2 he
            calc n1 * ipow (b + 1) E1 + ievalNat b r1
                < n1 * ipow (b + 1) E1 + ipow (b + 1) E1 := by gcongr
              _ = (n1 + 1) * ipow (b + 1) E1 := by rw [add_mul, one_mul]
              _ ≤ (b + 1) * ipow (b + 1) E1 := by gcongr
              _ = ipow (b + 1) (E1 + 1) := by rw [ipow_succ, mul_comm]
              _ ≤ ipow (b + 1) E2 := ipow_le_ipow_right hB1 (lt_iff_succ_le.mp hElt)
              _ = 1 * ipow (b + 1) E2 := (one_mul _).symm
              _ ≤ n2 * ipow (b + 1) E2 := by gcongr
              _ ≤ n2 * ipow (b + 1) E2 + ievalNat b r2 := le_self_add
          · -- icmp e1 e2 = 1 : e1 = e2, so E1 = E2; compare coefficients then tails
            have heq : e1 = e2 := by
              have he1w : e1 ≤ w := le_of_lt (lt_of_lt_of_le (by have := ocExp_lt e1 n1 r1; rwa [ocExp_ocOadd] at this) how)
              have he2w : e2 ≤ w := le_of_lt (lt_of_lt_of_le (by have := ocExp_lt e2 n2 r2; rwa [ocExp_ocOadd] at this) hpw)
              exact icmp_eq_imp_eq w e1 he1w e2 he2w he1
            have hEeq : E1 = E2 := by rw [hE1, hE2, heq]
            rw [thenV_eq_zero] at hinner
            rcases hinner with hcn | ⟨hcn, hri⟩
            · -- n1 < n2
              have hnlt : n1 < n2 := cmpV_eq_zero.mp hcn
              calc n1 * ipow (b + 1) E1 + ievalNat b r1
                  < n1 * ipow (b + 1) E1 + ipow (b + 1) E1 := by gcongr
                _ = (n1 + 1) * ipow (b + 1) E1 := by rw [add_mul, one_mul]
                _ ≤ n2 * ipow (b + 1) E1 := by gcongr; exact lt_iff_succ_le.mp hnlt
                _ = n2 * ipow (b + 1) E2 := by rw [hEeq]
                _ ≤ n2 * ipow (b + 1) E2 + ievalNat b r2 := le_self_add
            · -- n1 = n2, r1 ≺ r2
              have hneq : n1 = n2 := cmpV_eq_one.mp hcn
              have hr1w : r1 < w := lt_of_lt_of_le (by have := ocTail_lt e1 n1 r1; rwa [ocTail_ocOadd] at this) how
              have hr2w : r2 < w := lt_of_lt_of_le (by have := ocTail_lt e2 n2 r2; rwa [ocTail_ocOadd] at this) hpw
              have hrlt : ievalNat b r1 < ievalNat b r2 :=
                (ih (max r1 r2) (max_lt hr1w hr2w)).2 r1 (le_max_left _ _) r2 (le_max_right _ _)
                  hnr1 hnr2 hbr1 hbr2 hri
              calc n1 * ipow (b + 1) E1 + ievalNat b r1
                  < n1 * ipow (b + 1) E1 + ievalNat b r2 := by gcongr
                _ = n2 * ipow (b + 1) E2 + ievalNat b r2 := by rw [hneq, hEeq]

/-- **Internal order-reflection (forward direction)**: on the `isNF`/`iCanon b` domain, `≺` (i.e.
`icmp = 0`) implies the strict `ievalNat b` order. This is the Rathjen 2.3(iii) half the descent's
`ineq6_step` consumes. -/
theorem ievalNat_lt_of_icmp_eq_zero {b : V} (hb : 1 ≤ b) {o p : V}
    (hno : isNF o) (hnp : isNF p) (hco : iCanon b o) (hcp : iCanon b p)
    (h : icmp o p = 0) : ievalNat b o < ievalNat b p :=
  (evalNat_reflect_combined hb (max o p)).2 o (le_max_left _ _) p (le_max_right _ _)
    hno hnp hco hcp h

end GoodsteinPA.InternalONote
