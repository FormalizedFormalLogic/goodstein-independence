module

public import GoodsteinPA.Zef2TC.Axm

@[expose] public section

namespace GoodsteinPA.E1EmbeddingGrind

open LO LO.FirstOrder LO.FirstOrder.ArithmeticTerm ONote
open GoodsteinPA.OperatorZeh GoodsteinPA.OperatorZinfty

/-! ### The induction-schema kit, part 1 — `osuccs` + the ∀-closure peel -/

theorem Cl_osuccs {S : ONote → Prop} {α} (h : Cl S α) : ∀ n, Cl S (osuccs α n)
  | 0 => h
  | n + 1 => Cl.osucc (Cl_osuccs h n)

/-- **∀-closure peel**: if every numeral instance of the `ℓ`-ary matrix is derivable at `α`
(uniformly in the operator/slot, `em_cong`-style stability), the universal closure is
derivable at `osuccs α ℓ`.  Instances feed through `embedding_subst_q_cons_app`; the
`Cl`-in-every-operator hypothesis pays every `relOp` side condition. -/
theorem allClosure_peel {e} {d} {f₀ : ℕ → ℕ} :
    ∀ (ℓ : ℕ) (α : ONote), α.NF → (∀ S : ONote → Prop, Cl S α) →
      ∀ (χ : ArithmeticSemiformula ℕ ℓ) (Γ : Finset (ArithmeticFormula ℕ)),
      (∀ (w : Fin ℓ → ℕ) (H : ONote → Prop) (f : ℕ → ℕ), Monotone f → (∀ m, m ≤ f m) →
          f₀ 0 ≤ f 0 →
          Zef2TC α e H f d (insert (Rew.subst (fun i => nm (w i)) ▹ χ) Γ)) →
      (∀ k, k ≤ ℓ → Nlog (osuccs α k) ≤ f₀ 0) →
      ∀ (H : ONote → Prop) (f : ℕ → ℕ), Monotone f → (∀ m, m ≤ f m) → f₀ 0 ≤ f 0 →
      Zef2TC (osuccs α ℓ) e H f d (insert (∀⁰* χ) Γ) := by
  intro ℓ
  induction ℓ with
  | zero =>
      intro α hNF hCl χ Γ hinst hg H f hmono hinfl hf0
      have h := hinst ![] H f hmono hinfl hf0
      have hs : Rew.subst (fun i => nm ((![] : Fin 0 → ℕ) i)) ▹ χ = χ := by
        have : (Rew.subst (fun i => nm ((![] : Fin 0 → ℕ) i)) : Rew ℒₒᵣ ℕ 0 ℕ 0)
            = Rew.subst ![] := by congr; funext i; exact i.elim0
        rw [this]
        simp
      rwa [hs] at h
  | succ n ih =>
      intro α hNF hCl χ Γ hinst hg H f hmono hinfl hf0
      have step : ∀ (w : Fin n → ℕ) (H' : ONote → Prop) (f' : ℕ → ℕ), Monotone f' →
          (∀ m, m ≤ f' m) → f₀ 0 ≤ f' 0 →
          Zef2TC (osucc α) e H' f' d
            (insert (Rew.subst (fun i => nm (w i)) ▹ (∀⁰ χ)) Γ) := by
        intro w H' f' hmono' hinfl' hf0'
        have hsub : Rew.subst (fun i => nm (w i)) ▹ (∀⁰ χ)
            = ∀⁰ ((Rew.subst (fun i => nm (w i))).q ▹ χ) := by simp
        rw [hsub]
        have fam : ∀ m, Zef2TC α e (adjoin H' m) (rel1 f' m) d
            (insert ((((Rew.subst (fun i => nm (w i))).q ▹ χ))/[nm m]) Γ) := by
          intro m
          have hf'm : f' 0 ≤ rel1 f' m 0 := by
            simpa [rel1] using hmono' (Nat.zero_le (max m 0))
          rw [embedding_subst_q_cons_app]
          have hv : (nm m :> fun i => nm (w i)) = (fun i => nm ((m :> w) i)) := by
            funext i
            refine Fin.cases ?_ (fun j => ?_) i <;> simp
          rw [hv]
          exact hinst (m :> w) (adjoin H' m) (rel1 f' m) (rel1_monotone hmono' m)
            (rel1_infl hinfl' m) (le_trans hf0' hf'm)
        have hgd : Nlog (osucc α) ≤ f' 0 := le_trans (hg 1 (by omega)) hf0'
        exact Zef2TC.allω hgd _ (fun _ => α) (fun _ => lt_osucc hNF) (fun _ => hNF)
          (osucc_NF hNF) (fun m => hCl (adjoin H' m)) fam
      have h := ih (osucc α) (osucc_NF hNF) (fun S => Cl.osucc (hCl S)) (∀⁰ χ) Γ step
        (fun k hk => by
          rw [osuccs_succ_shift]
          exact hg (k + 1) (by omega))
        H f hmono hinfl hf0
      rw [osuccs_succ_shift] at h
      exact h


/-! ### The induction-schema kit, part 2 — `clog` gate arithmetic + the ω-root -/

/-- **The tower-gate bound**: linear-in-`k` `ofNat` towers have `clog`-gates dominated by
`max n C` for the constant `C = 2·clog a + 12` — exactly what an arbitrary
monotone+inflationary slot pays at branch `n`. -/
theorem clog_tower_gate (a : ℕ) {k n : ℕ} (hk : k ≤ n) :
    clog (a * (k + 1)) ≤ max n (2 * clog a + 12) := by
  have h1 := clog_mul_le a (k + 1)
  have h2 : clog (k + 1) ≤ clog (n + 1) := clog_mono (by omega)
  have h3 := two_mul_clog_le (n + 1)
  omega

/-- `ω` is in the closure of any generating set `S`. -/
theorem Cl_omega (S : ONote → Prop) : Cl S ONote.omega := by
  rw [omega_eq_expTower]; exact Cl.expTower (Cl.ofNat 1)

/-! ### The induction-schema kit, part 3 — `succInd` rewriting naturality over `ℒₒᵣ`
(ports of `EmbeddingX.subst1_comp_bShift` / `rew_subst1_comm_q` / `rew_succInd` /
`succInd_nnf` off `LX`). -/

/-- A degree-1 substitution fixes a `bShift`ed term. -/
theorem subst1_comp_bShift' (t : Semiterm ℒₒᵣ ℕ 1) :
    (Rew.subst ![t]).comp Rew.bShift = (Rew.bShift : Rew ℒₒᵣ ℕ 0 ℕ 1) := by
  ext y
  · exact Fin.elim0 y
  · simp [Rew.comp_app]

/-- `g.q` commutes with substituting a `g.q`-fixed term for the leading bvar. -/
theorem rew_subst1_comm_q' (g : SyntacticRew ℒₒᵣ 0 0) (φ : ArithmeticSemiformula ℕ 1)
    (t : Semiterm ℒₒᵣ ℕ 1) (ht : g.q t = t) :
    g.q ▹ (φ/[t]) = (g.q ▹ φ)/[t] := by
  show g.q ▹ (Rew.subst ![t] ▹ φ) = Rew.subst ![t] ▹ (g.q ▹ φ)
  have heq : (g.q).comp (Rew.subst ![t]) = (Rew.subst ![t]).comp g.q := by
    ext x
    · cases x using Fin.cases with
      | zero => simp [Rew.comp_app, ht]
      | succ i => exact Fin.elim0 i
    · rw [Rew.comp_app, Rew.comp_app, Rew.subst_fvar, Rew.q_fvar]
      show Rew.bShift (g &x) = ((Rew.subst ![t]).comp Rew.bShift) (g &x)
      rw [subst1_comp_bShift']
  rw [← TransitiveRewriting.comp_app, ← TransitiveRewriting.comp_app, heq]

/-- **`succInd` commutes with a closed rewriting** (`ℒₒᵣ` port of `EmbeddingX.rew_succInd`). -/
theorem rew_succInd' (g : SyntacticRew ℒₒᵣ 0 0) (ψ : Semiformula ℒₒᵣ ℕ 1) :
    g ▹ (Arithmetic.succInd ψ) = Arithmetic.succInd (g.q ▹ ψ) := by
  unfold Arithmetic.succInd
  simp only [Nat.reduceAdd, Fin.Fin1.eq_one, Fin.isValue, Rewriting.subst1_bvar0_eq,
    LogicalConnective.HomClass.map_imply, Rewriting.app_all, Semiformula.imp_inj,
    Semiformula.all_inj, true_and, and_true]
  refine ⟨?_, ?_⟩
  · rw [rew_subst_term g ψ (↑(0 : ℕ))]
    congr 1
    simp
  · rw [rew_subst1_comm_q' g ψ (‘(#0 + 1)’ : Semiterm ℒₒᵣ ℕ 1) (by simp)]

/-- The NNF of `succInd ψ` — the three Tait components. -/
theorem succInd_nnf' (ψ : Semiformula ℒₒᵣ ℕ 1) :
    Arithmetic.succInd ψ = (∼ψ/[(↑(0 : ℕ) : Semiterm ℒₒᵣ ℕ 0)]) ⋎
      ((∃⁰ ∼((∼ψ/[(#0 : Semiterm ℒₒᵣ ℕ 1)]) ⋎ ψ/[(‘(#0 + 1)’ : Semiterm ℒₒᵣ ℕ 1)])) ⋎
        (∀⁰ ψ/[(#0 : Semiterm ℒₒᵣ ℕ 1)])) := by
  conv_lhs => unfold Arithmetic.succInd
  simp only [Semiformula.imp_eq, Semiformula.neg_all]

/-! ### The induction-schema kit, part 4 — the succInd cut-tower at root `ω`

Per numeral branch `n`, a `≤ n`-long chain of cuts `D_k ⊢ ψ(k), Δ` climbs the linear `ofNat`
ladder `a·(k+1)` (`a := 2·complexity+4`): `D_0` is the value-congruent EM at `(nm 0, t0)`,
`D_{k+1}` cuts `ψ(nm k)` against the fired step disjunct (`exI` at witness `k`, `andI`, EM +
value-congruent EM at `(nm (k+1), succT k)`).  The branch ordinals are UNBOUNDED but all
`< ω`, and their `Nlog ≈ clog(a·(k+1))` gates are paid by the branch slot `rel1 f n`
via `clog_tower_gate` (`max n C`-domination — log beats linear).  The `allω` root is `ω`. -/

set_option maxHeartbeats 1000000 in
theorem metaInduction_Zef2TC (ψ step : ArithmeticSemiformula ℕ 1)
    (t0 : ArithmeticTerm ℕ) (succT : ℕ → ArithmeticTerm ℕ)
    (hval0 : stdClosedVal t0 = 0)
    (hsval : ∀ n, stdClosedVal (succT n) = n + 1)
    (hstep : ∀ n, (∼step)/[nm n] = (ψ/[nm n]) ⋏ ∼(ψ/[succT n]))
    {e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {Γ : Finset (ArithmeticFormula ℕ)}
    (hmono : Monotone f) (hinfl : ∀ m, m ≤ f m)
    (hg1 : 2 * clog (2 * ψ.complexity + 4) + 12 ≤ f 0)
    (hg2 : ψ.complexity ≤ f 0) :
    Zef2TC ONote.omega e H f (ψ.complexity + 1)
      (insert (∀⁰ ψ) (insert (∼(ψ/[t0])) (insert (∃⁰ (∼step)) Γ))) := by
  set c : ℕ := ψ.complexity + 1 with hc
  set a : ℕ := 2 * ψ.complexity + 4 with ha
  set Δ : Finset (ArithmeticFormula ℕ) := insert (∼(ψ/[t0])) (insert (∃⁰ (∼step)) Γ) with hΔ
  have hNF : ∀ m : ℕ, (ONote.ofNat m).NF := fun m => ONote.nf_ofNat m
  have chain : ∀ n k, k ≤ n →
      Zef2TC (ONote.ofNat (a * (k + 1))) e (adjoin H n) (rel1 f n) c
        (insert (ψ/[nm k]) Δ) := by
    intro n
    have hFmono : Monotone (rel1 f n) := rel1_monotone hmono n
    have hFinfl : ∀ m, m ≤ rel1 f n m := rel1_infl hinfl n
    have hf0n : f 0 ≤ rel1 f n 0 := by simpa [rel1] using hmono (Nat.zero_le (max n 0))
    have hnF : n ≤ rel1 f n 0 := by
      have := hinfl (max n 0)
      simp only [rel1]
      omega
    have hconst : ∀ m, m ≤ 2 * a → clog m ≤ rel1 f n 0 := by
      intro m hm
      have h1 := clog_mono hm
      have h2 := clog_mul_le 2 a
      have h3 : clog 2 ≤ 2 := by decide
      omega
    have htower : ∀ k, k ≤ n → clog (a * (k + 1)) ≤ rel1 f n 0 := by
      intro k hk
      have h1 := clog_tower_gate a (n := n) hk
      have h2 : 2 * clog a + 12 ≤ rel1 f n 0 := le_trans hg1 hf0n
      omega
    have hcxk : ∀ (t : ArithmeticTerm ℕ), (ψ/[t]).complexity = ψ.complexity := by
      intro t; simp
    intro k
    induction k with
    | zero =>
        intro _
        have hgEM : clog (2 * ψ.complexity + 1) ≤ rel1 f n 0 :=
          hconst _ (by omega)
        have hem : Zef2TC (ONote.ofNat (2 * ψ.complexity + 1)) e (adjoin H n) (rel1 f n) c
            (insert (ψ/[nm 0]) Δ) :=
          (em_cong1_Zef2TC (nm 0) t0 (by simp [hval0]) ψ
            hFmono hFinfl hgEM
            (Finset.mem_insert_self _ _)
            (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))).mono_c
            (c' := c) (Nat.zero_le c)
        refine Zef2TC.weak ?_ (ofNat_lt_ofNat (by omega)) (hNF _) (hNF _)
          (Cl.ofNat _) (Finset.Subset.refl _) hem
        exact le_trans (Nlog_ofNat_le _) (htower 0 (Nat.zero_le n))
    | succ k ih =>
        intro hk1
        have hkn : k ≤ n := Nat.le_of_succ_le hk1
        have Dk := ih hkn
        set X : Finset (ArithmeticFormula ℕ) := insert (∼(ψ/[nm k])) (insert (ψ/[nm (k + 1)]) Δ) with hX
        have hgEM : clog (2 * ψ.complexity + 1) ≤ rel1 f n 0 := hconst _ (by omega)
        -- left EM leaf: ψ(nm k) vs ∼ψ(nm k)
        have hL : Zef2TC (ONote.ofNat (2 * ψ.complexity + 1)) e (adjoin H n) (rel1 f n) c
            (insert (ψ/[nm k]) X) := by
          have h : Zef2TC (ONote.ofNat (2 * (ψ/[nm k]).complexity + 1)) e (adjoin H n)
              (rel1 f n) c (insert (ψ/[nm k]) X) :=
            (em_Zef2TC' (ψ/[nm k]) hFmono hFinfl
              (by rw [hcxk]; exact hgEM)
              (Finset.mem_insert_self _ _)
              (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))).mono_c
              (c' := c) (Nat.zero_le c)
          rwa [hcxk] at h
        -- right EM leaf: value-congruent pair (nm (k+1), succT k)
        have hR : Zef2TC (ONote.ofNat (2 * ψ.complexity + 1)) e (adjoin H n) (rel1 f n) c
            (insert (∼(ψ/[succT k])) X) :=
          (em_cong1_Zef2TC (nm (k + 1)) (succT k) (by simp [hsval]) ψ
            hFmono hFinfl hgEM
            (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
              (Finset.mem_insert_self _ _)))
            (Finset.mem_insert_self _ _)).mono_c (c' := c) (Nat.zero_le c)
        -- andI + exI: fire the step disjunct at witness k
        have hand := Zef2TC.andI (α := ONote.ofNat (2 * ψ.complexity + 2))
          (le_trans (Nlog_ofNat_le _) (hconst _ (by omega)))
          _ _ (ofNat_lt_ofNat (by omega)) (ofNat_lt_ofNat (by omega))
          (hNF _) (hNF _) (hNF _) (Cl.ofNat _) (Cl.ofNat _) hL hR
        rw [← hstep k] at hand
        have hex := Zef2TC.exI (α := ONote.ofNat (2 * ψ.complexity + 3))
          (le_trans (Nlog_ofNat_le _) (hconst _ (by omega)))
          (∼step) k (ofNat_lt_ofNat (by omega)) (hNF _) (hNF _) (Cl.ofNat _)
          (le_trans (le_trans hkn hnF) (le_refl _)) hand
        rw [Finset.insert_eq_self.mpr
          (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
            (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))))] at hex
        -- the cut on ψ(nm k), root a·(k+2)
        have hmul1 : a * (k + 1 + 1) = a * (k + 1) + a := by ring
        have hmul2 : a ≤ a * (k + 1) := Nat.le_mul_of_pos_right a (by omega)
        have d₁ : Zef2TC (ONote.ofNat (a * (k + 1))) e (adjoin H n) (rel1 f n) c
            (insert (ψ/[nm k]) (insert (ψ/[nm (k + 1)]) Δ)) :=
          Dk.wk Dk.gate (Finset.insert_subset_insert _ (Finset.subset_insert _ _))
        exact Zef2TC.cut
          (le_trans (Nlog_ofNat_le _) (htower (k + 1) hk1))
          (ψ/[nm k]) (by rw [hcxk]; omega) (by rw [hcxk]; exact le_trans hg2 hf0n)
          (ofNat_lt_ofNat (by omega)) (ofNat_lt_ofNat (by omega))
          (hNF _) (hNF _) (hNF _) (Cl.ofNat _) (Cl.ofNat _) d₁ hex
  have hroot : Nlog ONote.omega ≤ f 0 := by rw [Nlog_omega]; omega
  exact Zef2TC.allω hroot ψ (fun n => ONote.ofNat (a * (n + 1)))
    (fun n => ofNat_lt_omega _) (fun n => hNF _) omega_NF
    (fun n => Cl.ofNat _) (fun n => chain n n le_rfl)

/-! ### The induction-schema kit, part 5 — the per-instance succInd shape, and the V3 case -/

/-- The successor term of the induction step, at numeral `n`. -/
noncomputable def succTerm (n : ℕ) : ArithmeticTerm ℕ :=
  Rew.subst ![nm n] (‘(#0 + 1)’ : Semiterm ℒₒᵣ ℕ 1)

theorem stdClosedVal_succTerm (n : ℕ) : stdClosedVal (succTerm n) = n + 1 := by
  simp [succTerm, stdClosedVal, Matrix.empty_eq, nm]

/-- **The succInd instance shape**: any (rewritten) induction-axiom instance
`succInd ψw` is `Zef2TC`-derivable at the FIXED structural root `osucc² ω` — the ω-root
cut-tower `metaInduction_Zef2TC` plus the two `orI` peels of the NNF. -/
theorem succInd_shape_Zef2TC (ψw : ArithmeticSemiformula ℕ 1)
    {e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {Γ : Finset (ArithmeticFormula ℕ)}
    (hmono : Monotone f) (hinfl : ∀ m, m ≤ f m)
    (hg1 : 2 * clog (2 * ψw.complexity + 4) + 12 ≤ f 0)
    (hg2 : ψw.complexity ≤ f 0) :
    Zef2TC (osucc (osucc ONote.omega)) e H f (ψw.complexity + 1)
      (insert (Arithmetic.succInd ψw) Γ) := by
  rw [succInd_nnf' ψw]
  set t0 : ArithmeticTerm ℕ := (↑(0 : ℕ) : Semiterm ℒₒᵣ ℕ 0) with ht0
  set stepw : ArithmeticSemiformula ℕ 1 :=
    (∼ψw/[(#0 : Semiterm ℒₒᵣ ℕ 1)]) ⋎ ψw/[(‘(#0 + 1)’ : Semiterm ℒₒᵣ ℕ 1)] with hstepw
  have hval0 : stdClosedVal t0 = 0 := by simp [ht0, stdClosedVal]
  have hstep : ∀ n, (∼stepw)/[nm n] = (ψw/[nm n]) ⋏ ∼(ψw/[succTerm n]) := by
    intro n
    simp only [hstepw, succTerm]
    simp [← TransitiveRewriting.comp_app, Rew.subst_comp_subst]
  have ht := metaInduction_Zef2TC ψw stepw t0 succTerm hval0 stdClosedVal_succTerm hstep
    (e := e) (H := H) (Γ := Γ) hmono hinfl hg1 hg2
  have hb : ψw/[(#0 : Semiterm ℒₒᵣ ℕ 1)] = ψw := by simp
  -- gates for the two orI peels
  have hNs : Nlog (osucc ONote.omega) ≤ 3 := by
    have := Nlog_osucc_le omega_NF; rw [Nlog_omega] at this; omega
  have hNss : Nlog (osucc (osucc ONote.omega)) ≤ 4 := by
    have := Nlog_osucc_le (osucc_NF omega_NF); omega
  -- reorder for the inner orI
  have hre : Zef2TC ONote.omega e H f (ψw.complexity + 1)
      (insert (∃⁰ (∼stepw)) (insert (∀⁰ ψw)
        (insert (∼(ψw/[t0])) Γ))) :=
    ht.wk ht.gate (by intro x hx; simp only [Finset.mem_insert] at hx ⊢; tauto)
  have horI₂ := Zef2TC.orI (α := osucc ONote.omega)
    (le_trans hNs (le_trans (by omega : (3:ℕ) ≤ 12) (le_trans (by omega) hg1)))
    (∃⁰ (∼stepw)) (∀⁰ ψw) (lt_osucc omega_NF) omega_NF (osucc_NF omega_NF)
    (Cl_omega H) hre
  have hre₂ : Zef2TC (osucc ONote.omega) e H f (ψw.complexity + 1)
      (insert (∼(ψw/[t0])) (insert ((∃⁰ (∼stepw)) ⋎ (∀⁰ ψw)) Γ)) :=
    horI₂.wk horI₂.gate (by intro x hx; simp only [Finset.mem_insert] at hx ⊢; tauto)
  have horI₁ := Zef2TC.orI (α := osucc (osucc ONote.omega))
    (le_trans hNss (le_trans (by omega : (4:ℕ) ≤ 12) (le_trans (by omega) hg1)))
    (∼(ψw/[t0])) ((∃⁰ (∼stepw)) ⋎ (∀⁰ ψw)) (lt_osucc (osucc_NF omega_NF))
    (osucc_NF omega_NF) (osucc_NF (osucc_NF omega_NF)) (Cl.osucc (Cl_omega H)) hre₂
  rw [hb]
  exact horI₁

/-- **V3 `axm`, the induction schema** — the LAST V3 ladder rung.  The `univCl (succInd φ)`
sentence is env-fixed (`asg_emb_fix`), coerces to `∀⁰* (fixitr ▹ succInd φ)`, and peels by
`allClosure_peel` into numeral instances `succInd ψw` handled by `succInd_shape_Zef2TC` at the
uniform root `osucc² ω` — total root `osuccs (osucc² ω) fvSup`, all budgets structural. -/
theorem budgetedEmbedsV3_succInd {Γ}
    (φ : Semiformula ℒₒᵣ ℕ 1)
    (hΓ : (↑(Semiformula.univCl (Arithmetic.succInd φ)) : ArithmeticFormula ℕ) ∈ Γ) :
    BudgetedEmbedsV3 Γ := by
  set ℓ : ℕ := (Arithmetic.succInd φ).fvSup with hℓ
  set B : ℕ := 2 * clog (2 * φ.complexity + 4) + φ.complexity + ℓ + 20 with hB
  set α₀ : ONote := osucc (osucc ONote.omega) with hα₀
  have hα₀NF : α₀.NF := osucc_NF (osucc_NF omega_NF)
  have hα₀Cl : ∀ S : ONote → Prop, Cl S α₀ := fun S => Cl.osucc (Cl.osucc (Cl_omega S))
  have hNlogα₀ : Nlog α₀ ≤ 4 := by
    rw [hα₀]
    have h1 := Nlog_osucc_le omega_NF
    have h2 := Nlog_osucc_le (osucc_NF omega_NF)
    rw [Nlog_omega] at h1
    omega
  refine ⟨B, φ.complexity + 1, 0, 0, osuccs α₀ (0 + ℓ), ONote.NF.zero,
    osuccs_NF hα₀NF (0 + ℓ), ?_, fun env => ?_⟩
  · exact le_trans (Nlog_osuccs_le hα₀NF (0 + ℓ)) (by omega)
  · have hmem := Finset.mem_image_of_mem (fun χ => asg env ▹ χ) hΓ
    rw [asg_emb_fix] at hmem
    have hcoe : (↑(Semiformula.univCl (Arithmetic.succInd φ)) : ArithmeticFormula ℕ)
        = ∀⁰* (Rew.fixitr 0 ℓ ▹ (Arithmetic.succInd φ)) := by
      rw [Semiformula.coe_univCl_eq_univCl']; rfl
    rw [hcoe] at hmem
    have hf1 := ewRootSlot_f1 (0 : ONote) B
    have hmono : Monotone (rel1 (ewRootSlot 0 B) (envSup env 0)) :=
      rel1_monotone hf1.1.monotone _
    have hinfl : ∀ m, m ≤ rel1 (ewRootSlot 0 B) (envSup env 0) m :=
      rel1_infl (fun m => by have := hf1.2 m; omega) _
    have hf0 : B ≤ rel1 (ewRootSlot 0 B) (envSup env 0) 0 := le_relSlot_zero 0 B _
    have hinst : ∀ (w : Fin (0 + ℓ) → ℕ) (H : ONote → Prop) (f : ℕ → ℕ), Monotone f →
        (∀ m, m ≤ f m) → (fun _ : ℕ => B) 0 ≤ f 0 →
        Zef2TC α₀ 0 H f (φ.complexity + 1)
          (insert (Rew.subst (fun i => nm (w i)) ▹ (Rew.fixitr 0 ℓ ▹ (Arithmetic.succInd φ)))
            (Γ.image (fun χ => asg env ▹ χ))) := by
      intro w H f hmono' hinfl' hf0'
      rw [← TransitiveRewriting.comp_app, rew_succInd']
      set ψw : ArithmeticSemiformula ℕ 1 :=
        ((Rew.subst fun i => nm (w i)).comp (Rew.fixitr 0 ℓ)).q ▹ φ with hψw
      have hcx : ψw.complexity = φ.complexity := by simp [hψw]
      have hBle : B ≤ f 0 := hf0'
      have h := succInd_shape_Zef2TC ψw (e := 0) (H := H)
        (Γ := Γ.image (fun χ => asg env ▹ χ)) hmono' hinfl'
        (by rw [hcx]; exact le_trans (by rw [hB]; omega) hBle)
        (by rw [hcx]; exact le_trans (by rw [hB]; omega) hBle)
      rwa [hcx] at h
    have hpeel := allClosure_peel (f₀ := fun _ => B) (0 + ℓ) α₀ hα₀NF hα₀Cl
      (Rew.fixitr 0 ℓ ▹ (Arithmetic.succInd φ))
      (Γ.image (fun χ => asg env ▹ χ)) hinst
      (fun k hk => by
        have h1 := Nlog_osuccs_le hα₀NF k
        have h2 := hNlogα₀
        show Nlog (osuccs α₀ k) ≤ B
        rw [hB]
        omega)
      (fun _ => True) (rel1 (ewRootSlot 0 B) (envSup env 0)) hmono hinfl hf0
    rwa [Finset.insert_eq_self.mpr hmem] at hpeel

end GoodsteinPA.E1EmbeddingGrind
