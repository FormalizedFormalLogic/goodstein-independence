import GoodsteinPA.OperatorZef2

/-!
# 2b growth conversion — `ewIter` → `hardy` majorization (lap 207 start)

The route-(c) splice's LAST piece: dominate the read-off's master bound
`ewIter S γ (S (max m C))` by `fastGrowing o` at ONE fixed NF `o`, eventually.  Design
(PENDING_WORK lap-207 2b analysis):

* the naive Nlog-gated hardy ordinal-monotonicity is FALSE (coefficient `2^x` vs argument `x`);
  the banked `hardy_le_of_lt` gates on the LINEAR `norm`;
* so the majorization must pay the norm/log mismatch EXPLICITLY: the ball bound
  `Nlog β ≤ K` converts to `norm β < 2^(K+1)` (the bridge below), and the master induction
  keeps the argument pre-inflated past that;
* per level the two-fold branch composes by `hardy_add_comp` (EXACT when no absorption) and
  the ordinal assignment `g α ≈ h·ω^(1+α)` leaves room: `g β · 2 + corrections < g α`.

This file banks the majorization prerequisites, starting with THE bridge.
-/

namespace GoodsteinPA.HardyMajorization

open ONote Ordinal GoodsteinPA.FastGrowing GoodsteinPA.OperatorZeh

/-- **The norm/Nlog bridge**: the linear norm is at most one binary order above the log-norm.
(Sharp shape: `norm ≤ 2^Nlog` FAILS at coefficient 5 — `clog 5 = 2`, `2^2 = 4 < 5`.) -/
theorem norm_lt_two_pow_Nlog : ∀ (β : ONote), norm β < 2 ^ (Nlog β + 1)
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

/-- The ball-membership corollary the master induction consumes: a branch ordinal passing the
`Nlog β ≤ K` gate has linear norm `< 2^(K+1)`. -/
theorem norm_lt_of_Nlog_le {β : ONote} {K : ℕ} (h : Nlog β ≤ K) :
    norm β < 2 ^ (K + 1) :=
  lt_of_lt_of_le (norm_lt_two_pow_Nlog β)
    (Nat.pow_le_pow_right (by norm_num) (by omega))

#print axioms GoodsteinPA.HardyMajorization.norm_lt_two_pow_Nlog
#print axioms GoodsteinPA.HardyMajorization.norm_lt_of_Nlog_le

/-! ## The single-step composition + raise (the master induction's engine)

The branch shape `H_{ω^β'}(H_{ω^β'}(H_{ω^e'}(z)))` composes EXACTLY into
`H_{ω^β'·2 + ω^e'}(z)` (coefficient additivity + `hardy_add_comp`, association from the right),
then raises to `H_{ω^α'}(z)` by the LINEAR-norm-gated `hardy_le_of_lt` — the norm gate is paid
by the pre-inflated seed via the bridge above. -/

/-- `ω^x` as a notation. -/
noncomputable def Wpow (x : ONote) : ONote := oadd x 1 0

theorem Wpow_NF {x : ONote} (hx : x.NF) : (Wpow x).NF :=
  NF.oadd hx 1 NFBelow.zero

/-- The ONote sum `ω^β'·2 + ω^e'` in normal form. -/
noncomputable def stepOrd (β' e' : ONote) : ONote := oadd β' 2 (Wpow e')

theorem stepOrd_NF {β' e' : ONote} (hβ' : β'.NF) (he' : e'.NF) (hlt : e' < β') :
    (stepOrd β' e').NF :=
  NF.oadd hβ' 2 (NFBelow.oadd he' NFBelow.zero (lt_def.mp hlt))

/-- **The chain identity**: two same-level principal applications over one engine application
compose exactly. -/
theorem hardy_chain_eq {β' e' : ONote} (hβ' : β'.NF) (he' : e'.NF)
    (hβ0 : β' ≠ 0) (hlt : e' < β') (z : ℕ) :
    hardy (Wpow β') (hardy (Wpow β') (hardy (Wpow e') z))
      = hardy (stepOrd β' e') z := by
  have hsum : (oadd β' 2 0 : ONote) + Wpow e' = stepOrd β' e' := by
    haveI h1 : NF (oadd β' 2 0) := NF.oadd hβ' 2 NFBelow.zero
    haveI h2 : NF (Wpow e') := Wpow_NF he'
    haveI h3 : NF (stepOrd β' e') := stepOrd_NF hβ' he' hlt
    apply repr_inj.mp
    rw [repr_add]
    show ω ^ β'.repr * (2:ℕ) + 0 + (ω ^ e'.repr * (1:ℕ) + 0)
      = ω ^ β'.repr * (2:ℕ) + (ω ^ e'.repr * (1:ℕ) + 0)
    rw [add_zero]
  have hcomp : hardy ((oadd β' 2 0 : ONote) + Wpow e') z
      = hardy (oadd β' 2 0) (hardy (Wpow e') z) := by
    apply hardy_add_comp _ (NF.oadd hβ' 2 NFBelow.zero) _ (Wpow_NF he')
    · right
      show ω ^ e'.repr * (1:ℕ) + 0 < ω ^ (lastExp (oadd β' 2 0)).repr
      have hle : lastExp (oadd β' 2 0) = β' := rfl
      rw [hle]
      simpa using (Ordinal.opow_lt_opow_iff_right (by norm_num : (1:Ordinal) < ω)).mpr
        (lt_def.mp hlt)
  have hcoeff : hardy (oadd β' 2 0) (hardy (Wpow e') z)
      = hardy (Wpow β') (hardy (Wpow β') (hardy (Wpow e') z)) := by
    have h2 : (2 : ℕ+) = 1 + 1 := rfl
    rw [show (oadd β' 2 0 : ONote) = oadd β' (1 + 1) 0 from rfl,
      hardy_coeff_add β' hβ0 1 1]
    rfl
  rw [← hsum, hcomp, hcoeff]

/-- **The raise**: the composed step ordinal fits under the next `ω`-power, gated on the
linear norm of the BRANCH data only. -/
theorem hardy_step_raise {β' e' α' : ONote} (hβ' : β'.NF) (he' : e'.NF) (hα' : α'.NF)
    (hlt : e' < β') (hβα : β' < α') {z : ℕ}
    (hnorm : max (norm β') (max 2 (max (norm e') 1)) ≤ z) :
    hardy (stepOrd β' e') z ≤ hardy (Wpow α') z := by
  apply hardy_le_of_lt (stepOrd_NF hβ' he' hlt) (Wpow_NF hα')
  · show oadd β' 2 (Wpow e') < oadd α' 1 0
    rw [lt_def]
    calc (oadd β' 2 (Wpow e')).repr
        < ω ^ α'.repr := by
          have h1 : (oadd β' 2 (Wpow e')).NF := stepOrd_NF hβ' he' hlt
          exact (NF.below_of_lt (lt_def.mp hβα) h1).repr_lt
      _ ≤ (oadd α' 1 0).repr := by
          show ω ^ α'.repr ≤ ω ^ α'.repr * (1:ℕ) + 0
          simp
  · show norm (oadd β' 2 (Wpow e')) ≤ z
    simpa [norm, Wpow] using hnorm

/-- **The step engine, assembled**: the master induction's branch case in one move. -/
theorem hardy_step {β' e' α' : ONote} (hβ' : β'.NF) (he' : e'.NF) (hα' : α'.NF)
    (hβ0 : β' ≠ 0) (hlt : e' < β') (hβα : β' < α') {z : ℕ}
    (hnorm : max (norm β') (max 2 (max (norm e') 1)) ≤ z) :
    hardy (Wpow β') (hardy (Wpow β') (hardy (Wpow e') z)) ≤ hardy (Wpow α') z := by
  rw [hardy_chain_eq hβ' he' hβ0 hlt z]
  exact hardy_step_raise hβ' he' hα' hlt hβα hnorm

#print axioms GoodsteinPA.HardyMajorization.hardy_chain_eq
#print axioms GoodsteinPA.HardyMajorization.hardy_step

end GoodsteinPA.HardyMajorization
