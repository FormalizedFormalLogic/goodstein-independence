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

/-! ## Argument super-additivity of `hardy` (lap 208)

`H_o(n) + c ≤ H_o(n + c)` — the commuting engine that pushes the branch's additive
`Nlog β + ·` costs INSIDE the composed Hardy stack (so all principal applications
compose exactly, engines innermost).  Successor form mirrors `hardy_monotone`'s
WF recursion; limit case pays one `hardy_fundSeq_step`. -/

theorem hardy_succ_ge (o : ONote) (n : ℕ) : hardy o n + 1 ≤ hardy o (n + 1) := by
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

theorem hardy_arg_add (o : ONote) (n c : ℕ) : hardy o n + c ≤ hardy o (n + c) := by
  induction c with
  | zero => simp
  | succ c ih =>
      calc hardy o n + (c + 1) = (hardy o n + c) + 1 := by ring
        _ ≤ hardy o (n + c) + 1 := by omega
        _ ≤ hardy o (n + c + 1) := hardy_succ_ge o (n + c)
        _ = hardy o (n + (c + 1)) := by ring_nf

/-- Exponent-strict-monotonicity of `Wpow` (repr-level). -/
theorem Wpow_lt {x y : ONote} (h : x < y) : Wpow x < Wpow y := by
  rw [lt_def]
  show ω ^ x.repr * (1 : ℕ) + 0 < ω ^ y.repr * (1 : ℕ) + 0
  simpa using (Ordinal.opow_lt_opow_iff_right (by norm_num : (1 : Ordinal) < ω)).mpr
    (lt_def.mp h)

/-! ## Linear-norm control of ONote addition

`norm (x + y) ≤ normSum x + norm y` where `normSum` charges the SUM of per-term maxima
of `x` (a fixed constant when `x` is fixed, e.g. the assignment prefix `e' + 1`).  This is
what bounds `norm (e' + 1 + β)` by `C(e') + norm β`, feeding the raise's norm gate through
the `Nlog → norm` bridge. -/

/-- Summed per-term charge of a notation (an upper-bound companion to `norm`). -/
def normSum : ONote → ℕ
  | 0 => 0
  | oadd e n a => max (norm e) (n : ℕ) + normSum a

theorem norm_addAux_le (e : ONote) (n : ℕ+) (o : ONote) :
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

theorem norm_add_le : ∀ (x y : ONote), norm (x + y) ≤ normSum x + norm y
  | 0, y => by simp [normSum]
  | oadd e n a, y => by
      rw [oadd_add]
      have h1 := norm_addAux_le e n (a + y)
      have h2 := norm_add_le a y
      simp only [normSum]
      omega

#print axioms GoodsteinPA.HardyMajorization.hardy_arg_add
#print axioms GoodsteinPA.HardyMajorization.norm_add_le

/-! ## The coefficient-3 chain (the master induction's actual branch shape)

The branch pays THREE same-level principal applications (outer IH + inner IH + the raised
middle engine) over one innermost engine: `H_{ω^β'}³(H_{ω^e'}(z)) = H_{ω^β'·3 + ω^e'}(z)`,
then the composed ordinal raises under `ω^α'` exactly as in `hardy_step_raise`. -/

/-- `ω^β'·3 + ω^e'` in normal form. -/
noncomputable def stepOrd3 (β' e' : ONote) : ONote := oadd β' 3 (Wpow e')

theorem stepOrd3_NF {β' e' : ONote} (hβ' : β'.NF) (he' : e'.NF) (hlt : e' < β') :
    (stepOrd3 β' e').NF :=
  NF.oadd hβ' 3 (NFBelow.oadd he' NFBelow.zero (lt_def.mp hlt))

/-- Three same-level principals over one engine compose exactly (tail-peel + coefficient
additivity — no repr arithmetic needed). -/
theorem hardy_chain3_eq {β' e' : ONote} (hβ0 : β' ≠ 0) (z : ℕ) :
    hardy (Wpow β') (hardy (Wpow β') (hardy (Wpow β') (hardy (Wpow e') z)))
      = hardy (stepOrd3 β' e') z := by
  rw [show stepOrd3 β' e' = oadd β' 3 (Wpow e') from rfl,
    hardy_oadd_tail β' 3 (Wpow e') z,
    show (3 : ℕ+) = 1 + 2 from rfl, hardy_coeff_add β' hβ0 1 2,
    show (2 : ℕ+) = 1 + 1 from rfl, hardy_coeff_add β' hβ0 1 1]
  rfl

/-- The composed branch ordinal sits strictly below the next `ω`-power. -/
theorem stepOrd3_lt_Wpow {β' e' α' : ONote} (hβ' : β'.NF) (he' : e'.NF)
    (hlt : e' < β') (hβα : β' < α') : stepOrd3 β' e' < Wpow α' := by
  rw [lt_def]
  calc (stepOrd3 β' e').repr
      < ω ^ α'.repr :=
        (NF.below_of_lt (lt_def.mp hβα) (stepOrd3_NF hβ' he' hlt)).repr_lt
    _ ≤ (Wpow α').repr := by
        show ω ^ α'.repr ≤ ω ^ α'.repr * (1 : ℕ) + 0
        simp

#print axioms GoodsteinPA.HardyMajorization.hardy_chain3_eq
#print axioms GoodsteinPA.HardyMajorization.stepOrd3_lt_Wpow

/-! ## THE MASTER MAJORIZATION (lap 208) — `ewIter f α m ≤ H_{ω^{e'+1+α}}(H_{ω^{e'}}(Nlog α + m + p))`

The 2b growth-conversion crux.  Assignment exponent `g α := e' + 1 + α` (ONote add — strictly
monotone, always above the engine `e'`).  WF induction on `α`; the branch (a ball member
`δ < α`, `Nlog δ ≤ K := f (Nlog α + m)`) pays:

1. outer IH + inner IH (two `H_{ω^{gδ}}∘H_{ω^{e'}}` layers with additive `Nlog δ` costs in
   between);
2. `hardy_arg_add` pushes the additive costs innermost;
3. the middle engine raises to the branch level (`Wpow_lt` + `hardy_le_of_lt`, gate `≤ p`);
4. `hardy_chain3_eq` collapses the three same-level principals + engine into
   `H_{ω^{gδ}·3 + ω^{e'}}`;
5. the final raise to `ω^{gα}` happens at the engine-inflated argument
   `z = H_{ω^{e'}}(Nlog α + m + p)`, whose size pays the `2^{K+1}` norm gate
   (`norm_add_le` + the `Nlog→norm` bridge) via the single engine hypothesis `hEng`.

`hEng` is the ONLY growth assumption: the engine level `e'` absorbs one `f`-application,
the exponential of one `f`-application, and fixed constants.  Instantiating it at a concrete
`e'` (from `f ≤ H_{ω^{e₀}}`-form domination, `e' ≈ e₀ + 2`) is separate downstream work. -/

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

#print axioms GoodsteinPA.HardyMajorization.ewIter_hardy_le

end GoodsteinPA.HardyMajorization
