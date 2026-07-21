/-
# Hardy hierarchy — additive/structural laws

`hstep`, `lastExp`, `lead`, and the additive composition laws for `hardy` on CNF notations.
-/
module

public import GoodsteinPA.ToMathlib.Hardy.Basic

@[expose] public section

namespace ONote

open ONote Ordinal

/-- **First super-linear Hardy lower bound:** `2n ≤ H_{ω^e}(n)` for every nonzero exponent `e` and `n ≥ 1`. -/
theorem two_mul_le_hardy_pow {e : ONote} (he : e ≠ 0) (hNFe : e.NF) {n : ℕ} (hn : 1 ≤ n) :
    2 * n ≤ hardy (oadd e 1 0) n := by
  have hNF1 : (1 : ONote).NF := NF.oadd NF.zero 1 NFBelow.zero
  have hNFω : (oadd 1 1 0).NF := NF.oadd hNF1 1 NFBelow.zero
  have hNFe1 : (oadd e 1 0).NF := NF.oadd hNFe 1 NFBelow.zero
  have he_pos : 0 < e.repr := by
    rcases eq_zero_or_pos e.repr with h | h
    · exact absurd ((@repr_inj e 0 hNFe NF.zero).1 (by rw [h, repr_zero])) he
    · exact h
  -- `ω = ω^1 ≤ ω^(repr e)` since `1 ≤ repr e`
  have hle : (oadd 1 1 0).repr ≤ (oadd e 1 0).repr := by
    have hr1 : (oadd 1 1 0).repr = ω ^ (1 : Ordinal) := by simp [ONote.repr]
    have hre : (oadd e 1 0).repr = ω ^ e.repr := by simp [ONote.repr]
    rw [hr1, hre]
    exact opow_le_opow_right omega0_pos (Order.one_le_iff_pos.2 he_pos)
  rcases eq_or_lt_of_le hle with heq | hlt
  · have heqo : oadd 1 1 0 = oadd e 1 0 := (@repr_inj (oadd 1 1 0) (oadd e 1 0) hNFω hNFe1).1 heq
    rw [← heqo, hardy_omega]; omega
  · have hbudget : norm (oadd 1 1 0) ≤ n := by
      have hn1 : norm (oadd 1 1 0) = 1 := by decide
      omega
    have h := hardy_le_of_lt hNFω hNFe1 (lt_def.2 hlt) hbudget
    rw [hardy_omega] at h; omega

/-! ### The Hardy step `hstep` and the step invariant

`H_o(n) = H_{hstep o n}(n+1)` for nonzero `o`, where `hstep` performs one budget-incrementing step of ordinal descent.
-/

/-- The fundamental sequence of a limit notation is everywhere nonzero: every branch of
`ONote.fundamentalSequence` for a limit returns `fun i => oadd …`, and `oadd` is positive.
Needed so the limit recursion of `hstep`/`hardy_hstep` never collapses to `0` prematurely. -/
lemma fundamentalSequence_inr_ne_zero {o : ONote} {f : ℕ → ONote}
    (h : fundamentalSequence o = Sum.inr f) (i : ℕ) : f i ≠ 0 := by
  induction o with
  | zero => simp [fundamentalSequence] at h
  | oadd a m b iha ihb =>
    rw [fundamentalSequence] at h
    split at h
    · injection h with h'; subst h'; exact (oadd_pos _ _ _).ne'
    · exact (Sum.inl_ne_inr h).elim
    · split at h <;>
        first
          | exact (Sum.inl_ne_inr h).elim
          | (injection h with h'; subst h'; simp only []; exact (oadd_pos _ _ _).ne')

/-- One budget-incrementing Hardy step: descend through limit stages until passing exactly one successor. -/
def hstep : ONote → ℕ → ONote
  | o =>
    match fundamentalSequence o, fundamentalSequence_has_prop o with
    | Sum.inl none, _ => fun _ => 0
    | Sum.inl (some a), _ => fun _ => a
    | Sum.inr f, h => fun n =>
      have : f n < o := (h.2.1 n).2.1
      hstep (f n) n
  termination_by o => o

/-- Unfolding lemma for `hstep`, mirroring `hardy_def`. -/
lemma hstep_def {o : ONote} {x} (e : fundamentalSequence o = x) :
    hstep o =
      match
        (motive := (x : Option ONote ⊕ (ℕ → ONote)) → FundamentalSequenceProp o x → ℕ → ONote)
        x, e ▸ fundamentalSequence_has_prop o with
      | Sum.inl none, _ => fun _ => 0
      | Sum.inl (some a), _ => fun _ => a
      | Sum.inr f, _ => fun n => hstep (f n) n := by
  subst x; rw [hstep]

/-- `hstep o = fun _ => a` when `o` is the successor of `a`. -/
lemma hstep_succ (o) {a} (h : fundamentalSequence o = Sum.inl (some a)) :
    hstep o = fun _ => a := by rw [hstep_def h]

/-- `hstep o = fun n => hstep (o[n]) n` when `o` is a limit with fundamental sequence `f`. -/
lemma hstep_limit (o) {f} (h : fundamentalSequence o = Sum.inr f) :
    hstep o = fun n => hstep (f n) n := by rw [hstep_def h]

/-- **Intrinsic Hardy step invariant:** For a nonzero notation, `H_o(n) = H_{hstep o n}(n+1)`. -/
theorem hardy_hstep (o : ONote) (n : ℕ) (h : o ≠ 0) : hardy o n = hardy (hstep o n) (n + 1) := by
  rcases e : fundamentalSequence o with (_ | a) | f
  · exact absurd (eq_zero_of_fundamentalSequence_inl_none e) h
  · rw [hardy_succ o e, hstep_succ o e]
  · have hlt : f n < o := fundamentalSequence_inr_lt e n
    rw [hardy_limit o e, hstep_limit o e]
    exact hardy_hstep (f n) n (fundamentalSequence_inr_ne_zero e n)
termination_by o
decreasing_by exact hlt

/-- **Peeling the leading term of a Hardy step:** When `R ≠ 0`, `hstep (oadd E C R) b = oadd E C (hstep R b)`. -/
lemma hstep_oadd_tail (E : ONote) (C : ℕ+) (b : ℕ) (R : ONote) (hR : R ≠ 0) :
    hstep (oadd E C R) b = oadd E C (hstep R b) := by
  induction R using (InvImage.wf repr Ordinal.lt_wf).induction with
  | _ R ih =>
    rcases e : fundamentalSequence R with (_ | R') | g
    · exact absurd (eq_zero_of_fundamentalSequence_inl_none e) hR
    · rw [hstep_succ _ (fundamentalSequence_oadd_succ e), hstep_succ _ e]
    · rw [hstep_limit _ (fundamentalSequence_oadd_limit e), hstep_limit _ e]
      have hgb : g b ≠ 0 := fundamentalSequence_inr_ne_zero e b
      have hglt : g b < R := fundamentalSequence_inr_lt e b
      exact ih (g b) (lt_def.1 hglt) hgb

/-- **Hardy tail-peeling — the additive law:** `hardy (oadd a m b) n = hardy (oadd a m 0) (hardy b n)`. -/
theorem hardy_oadd_tail (a : ONote) (m : ℕ+) (b : ONote) (n : ℕ) :
    hardy (oadd a m b) n = hardy (oadd a m 0) (hardy b n) := by
  rcases e : fundamentalSequence b with (_ | b') | f
  · have hb0 : b = 0 := eq_zero_of_fundamentalSequence_inl_none e
    rw [hardy_zero' b e, hb0]; rfl
  · have hlt : b' < b := lt_of_fundamentalSequence_inl_some e
    have hfs : fundamentalSequence (oadd a m b) = Sum.inl (some (oadd a m b')) := by
      conv_lhs => rw [fundamentalSequence]; rw [e]
    rw [hardy_succ _ hfs, hardy_succ b e]
    exact hardy_oadd_tail a m b' (n + 1)
  · have hlt : f n < b := fundamentalSequence_inr_lt e n
    have hfs : fundamentalSequence (oadd a m b) = Sum.inr (fun i => oadd a m (f i)) := by
      conv_lhs => rw [fundamentalSequence]; rw [e]
    rw [hardy_limit _ hfs, hardy_limit b e]
    exact hardy_oadd_tail a m (f n) n
termination_by b
decreasing_by all_goals exact hlt

/-- Anti-vacuity for `hardy_oadd_tail`: `H_{ω·2 + 1}(2) = H_{ω·2}(H_1(2)) = H_{ω·2}(3)`. -/
example : hardy (oadd 1 2 1) 2 = hardy (oadd 1 2 0) (hardy 1 2) := hardy_oadd_tail 1 2 1 2

/-- **Coefficient step:** `H_{ω^b·(j+1)}(x) = H_{ω^b·j}(H_{ω^b}(x))` for `b ≠ 0`. -/
theorem hardy_oadd_coeff_step (b : ONote) (hb : b ≠ 0) (k x : ℕ) :
    hardy (oadd b (k + 1).succPNat 0) x
      = hardy (oadd b k.succPNat 0) (hardy (oadd b 1 0) x) := by
  rcases e : fundamentalSequence b with (_ | b') | f
  · exact absurd (eq_zero_of_fundamentalSequence_inl_none e) hb
  · have hfs : fundamentalSequence (oadd b (k + 1).succPNat 0)
        = Sum.inr (fun i => oadd b k.succPNat (oadd b' i.succPNat 0)) := by
      conv_lhs => rw [fundamentalSequence]
      rw [e]; rfl
    rw [hardy_limit _ hfs]
    show hardy (oadd b k.succPNat (oadd b' x.succPNat 0)) x
        = hardy (oadd b k.succPNat 0) (hardy (oadd b 1 0) x)
    rw [hardy_oadd_tail b k.succPNat (oadd b' x.succPNat 0) x,
        hardy_limit (oadd b 1 0) (fundamentalSequence_omega_pow_succ e)]
  · have hfs : fundamentalSequence (oadd b (k + 1).succPNat 0)
        = Sum.inr (fun i => oadd b k.succPNat (oadd (f i) 1 0)) := by
      conv_lhs => rw [fundamentalSequence]
      rw [e]; rfl
    rw [hardy_limit _ hfs]
    show hardy (oadd b k.succPNat (oadd (f x) 1 0)) x
        = hardy (oadd b k.succPNat 0) (hardy (oadd b 1 0) x)
    rw [hardy_oadd_tail b k.succPNat (oadd (f x) 1 0) x,
        hardy_limit (oadd b 1 0) (fundamentalSequence_omega_pow_limit e)]

/-- **The coefficient lemma:** `hardy (oadd b (k+1) 0) x = (hardy (oadd b 1 0))^[k+1] x` for `b ≠ 0`. -/
theorem hardy_oadd_coeff (b : ONote) (hb : b ≠ 0) (k x : ℕ) :
    hardy (oadd b k.succPNat 0) x = (hardy (oadd b 1 0))^[k + 1] x := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    rw [hardy_oadd_coeff_step b hb k x, ih (hardy (oadd b 1 0) x), ← Function.iterate_succ_apply]

/-! ### The general non-absorbing Hardy additive composition law

`H_{c+d}(x) = H_c(H_d(x))` when `d` lies strictly below `c`'s least exponent (non-absorbing CNF concatenation).
-/

/-- The least (trailing) exponent of a notation's Cantor normal form (`0` for `0`). -/
def lastExp : ONote → ONote
  | 0 => 0
  | oadd e _ a => match a with
    | 0 => e
    | oadd _ _ _ => lastExp a

@[simp] theorem lastExp_zero : lastExp 0 = 0 := rfl
@[simp] theorem lastExp_oadd_zero (e n) : lastExp (oadd e n 0) = e := rfl

@[grind =]
lemma lastExp_oadd_ne {e : ONote} {n : ℕ+} {a : ONote} (h : a ≠ 0) : lastExp (oadd e n a) = lastExp a := by
  cases a with
  | zero => exact absurd rfl h
  | oadd e' n' a' => rfl

/-- `addAux` concatenates (no merge/absorb) when the right operand's leading exponent is strictly below `e`. -/
lemma addAux_concat {e : ONote} (he : e.NF) {n : ℕ+} {o : ONote} (ho : o.NF)
    (h : o = 0 ∨ ∀ e' n' a', o = oadd e' n' a' → e'.repr < e.repr) :
    addAux e n o = oadd e n o := by
  match o, ho, h with
  | 0, _, _ => rfl
  | oadd e' n' a', ho', h' =>
    have hlt : e'.repr < e.repr := by
      rcases h' with h0 | hf
      · exact absurd h0 (by simp)
      · exact hf e' n' a' rfl
    have hee' : ONote.cmp e e' = Ordering.gt :=
      (@ONote.cmp_compares e e' he ho'.fst).eq_gt.2 hlt
    simp only [addAux, hee']

/-- The least exponent of a nonzero notation lies below any bound it is `NFBelow`. -/
lemma lastExp_repr_lt {o : ONote} {b : Ordinal} (hb : NFBelow o b) (h : o ≠ 0) : (lastExp o).repr < b := by
  induction o generalizing b with
  | zero => exact absurd rfl h
  | oadd e n a _ iha =>
    rcases eq_or_ne a 0 with ha | ha
    · subst ha; rw [lastExp_oadd_zero]; exact hb.lt
    · rw [lastExp_oadd_ne ha]
      exact lt_trans (iha hb.snd ha) hb.lt

/-- Convert an `NFBelow` fact into the leading-exponent bound `addAux_concat` consumes. -/
lemma nfBelow_concat {o : ONote} {b : Ordinal} (h : NFBelow o b) :
    o = 0 ∨ ∀ e' n' a', o = oadd e' n' a' → e'.repr < b := by
  cases o with
  | zero => left; rfl
  | oadd e' n' a' => right; intro e'' n'' a'' heq; cases heq; exact h.lt

/-- **The general non-absorbing Hardy additive composition law:** For normal-form `c`, `d` with `d` strictly below `c`'s least exponent, `H_{c+d}(x) = H_c(H_d(x))`. -/
theorem hardy_add_comp (c : ONote) (hc : c.NF) (d : ONote) (hd : d.NF)
    (hcond : d = 0 ∨ d.repr < ω ^ (lastExp c).repr) (x : ℕ) :
    hardy (c + d) x = hardy c (hardy d x) := by
  induction c generalizing d x with
  | zero =>
    show hardy ((0 : ONote) + d) x = hardy (0 : ONote) (hardy d x)
    rw [ONote.zero_add, hardy_zero]; rfl
  | oadd e n a _ iha =>
    haveI := hc
    rcases eq_or_ne d 0 with hd0 | hd0
    · subst hd0
      have hadd : oadd e n a + 0 = oadd e n a :=
        repr_inj.mp (by rw [repr_add, repr_zero, add_zero])
      rw [hadd, hardy_zero]; rfl
    have he : e.NF := hc.fst
    have hba : NFBelow a e.repr := hc.snd'
    have ha : a.NF := ⟨⟨e.repr, hba⟩⟩
    have hle : (lastExp (oadd e n a)).repr ≤ e.repr := by
      rcases eq_or_ne a 0 with ha0 | ha0
      · subst ha0; rw [lastExp_oadd_zero]
      · rw [lastExp_oadd_ne ha0]; exact le_of_lt (lastExp_repr_lt hba ha0)
    have hdlt_e : d.repr < ω ^ e.repr := by
      rcases hcond with h0 | hlt
      · exact absurd h0 hd0
      · exact lt_of_lt_of_le hlt (opow_le_opow_right omega0_pos hle)
    have hbd : NFBelow d e.repr := NF.below_of_lt' hdlt_e hd
    have hbad : NFBelow (a + d) e.repr := add_nfBelow hba hbd
    have hcc : addAux e n (a + d) = oadd e n (a + d) :=
      addAux_concat he (⟨⟨_, hbad⟩⟩) (nfBelow_concat hbad)
    rw [oadd_add, hcc, hardy_oadd_tail e n (a + d) x]
    rcases eq_or_ne a 0 with ha0 | ha0
    · subst ha0; rw [ONote.zero_add]
    · have ihcond : d = 0 ∨ d.repr < ω ^ (lastExp a).repr := by
        right
        rcases hcond with h0 | hlt
        · exact absurd h0 hd0
        · rwa [lastExp_oadd_ne ha0] at hlt
      rw [iha ha d hd ihcond x, hardy_oadd_tail e n a (hardy d x)]

/-- **Control-ordinal collapse:** When cut-formula bound `a` lies below control ordinal `e`'s least exponent, `H_e(H_a(x)) = H_{e+a}(x)`. -/
theorem hardy_add_collapse {e a : ONote} (he : e.NF) (ha : a.NF)
    (hbelow : a = 0 ∨ a.repr < ω ^ (lastExp e).repr) (x : ℕ) :
    hardy (e + a) x = hardy e (hardy a x) :=
  hardy_add_comp e he a ha hbelow x

/-! ### The additive-Hardy inequality

`H_{e+b}(x) ≤ H_e(H_b(x))` for every normal-form `e, b` (survives absorption, unlike the equality).
-/

/-- Single finite term: `H_{ω^0·p}(y) = y + p` (via `oadd 0 p 0 = ofNat p`). -/
@[simp, grind =]
lemma hardy_oadd0 (p : ℕ+) (y : ℕ) : hardy (oadd 0 p 0) y = y + (p : ℕ) := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, p = k.succPNat := ⟨p.natPred, (PNat.succPNat_natPred p).symm⟩
  rw [show oadd 0 k.succPNat 0 = ofNat (k + 1) from (ofNat_succ k).symm, hardy_ofNat,
    Nat.succPNat_coe]

/-- Coefficient-as-iterate, restated for a `ℕ+` coefficient (`e ≠ 0`): `H_{ω^e·p}(x) = (H_{ω^e})^[p](x)`. -/
lemma hardy_single_coeff (e : ONote) (he : e ≠ 0) (p : ℕ+) (x : ℕ) :
    hardy (oadd e p 0) x = (hardy (oadd e 1 0))^[(p : ℕ)] x := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, p = k.succPNat := ⟨p.natPred, (PNat.succPNat_natPred p).symm⟩
  rw [hardy_oadd_coeff e he k x, Nat.succPNat_coe]

/-- Coefficient additivity at a single term (`e ≠ 0`): `H_{ω^e·(m+n)}(x) = H_{ω^e·m}(H_{ω^e·n}(x))`. -/
lemma hardy_coeff_add (e : ONote) (he : e ≠ 0) (m n : ℕ+) (x : ℕ) :
    hardy (oadd e (m + n) 0) x = hardy (oadd e m 0) (hardy (oadd e n 0) x) := by
  rw [hardy_single_coeff e he (m + n) x, hardy_single_coeff e he m,
    hardy_single_coeff e he n x, PNat.add_coe, Function.iterate_add_apply]

/-- **The additive-Hardy inequality:** For normal-form `e, b`, `H_{e+b}(x) ≤ H_e(H_b(x))`. -/
theorem hardy_add_le_comp (e : ONote) (he : e.NF) (b : ONote) (hb : b.NF) (x : ℕ) :
    hardy (e + b) x ≤ hardy e (hardy b x) := by
  induction e generalizing b x with
  | zero =>
    simp [ONote.zero_add, hardy_zero]
  | oadd e₁ n₁ a₁ _ihe₁ iha₁ =>
    rcases eq_or_ne b 0 with rfl | hb0
    · rw [show oadd e₁ n₁ a₁ + 0 = oadd e₁ n₁ a₁ from
          repr_inj.mp (by rw [repr_add, repr_zero, add_zero])]
      simp [hardy_zero]
    have he₁ : e₁.NF := he.fst
    have hba₁ : NFBelow a₁ e₁.repr := he.snd'
    have ha₁ : a₁.NF := ⟨⟨e₁.repr, hba₁⟩⟩
    obtain ⟨bo, hbo⟩ := hb.out
    have hsNF : (a₁ + b).NF :=
      ⟨⟨max e₁.repr bo,
        add_nfBelow (hba₁.mono (le_max_left _ _)) (hbo.mono (le_max_right _ _))⟩⟩
    have hs0 : a₁ + b ≠ 0 := by
      intro h
      apply hb0
      have : ONote.repr (a₁ + b) = 0 := by rw [h, repr_zero]
      rw [repr_add] at this
      exact repr_inj.mp (by rw [(Ordinal.add_eq_zero_iff.mp this).2, repr_zero])
    rw [oadd_add]
    cases hh : a₁ + b with
    | zero => exact absurd hh hs0
    | oadd e' n' a' =>
      have he'NF : e'.NF := (hh ▸ hsNF).fst
      cases hcmpc : e₁.cmp e' with
      | lt =>
        simp only [addAux, hcmpc]
        rw [← hh]
        calc hardy (a₁ + b) x
            ≤ hardy a₁ (hardy b x) := iha₁ ha₁ b hb x
          _ ≤ hardy (oadd e₁ n₁ a₁) (hardy b x) := by
              rw [hardy_oadd_tail e₁ n₁ a₁ (hardy b x)]
              exact le_hardy (oadd e₁ n₁ 0) (hardy a₁ (hardy b x))
      | gt =>
        simp only [addAux, hcmpc]
        rw [← hh]
        calc hardy (oadd e₁ n₁ (a₁ + b)) x
            = hardy (oadd e₁ n₁ 0) (hardy (a₁ + b) x) := hardy_oadd_tail e₁ n₁ (a₁ + b) x
          _ ≤ hardy (oadd e₁ n₁ 0) (hardy a₁ (hardy b x)) := hardy_monotone _ (iha₁ ha₁ b hb x)
          _ = hardy (oadd e₁ n₁ a₁) (hardy b x) := (hardy_oadd_tail e₁ n₁ a₁ (hardy b x)).symm
      | eq =>
        have hee : e₁ = e' := by
          have := @cmp_compares e₁ e' he₁ he'NF; rw [hcmpc] at this; exact this
        subst hee
        simp only [addAux, hcmpc]
        rcases eq_or_ne e₁ 0 with he₁0 | he₁0
        · subst he₁0
          have ha1z : a₁ = 0 := by
            cases a₁ with
            | zero => rfl
            | oadd e'' n'' a'' =>
                have hlt := NFBelow.lt hba₁; rw [repr_zero] at hlt
                exact absurd hlt not_lt_zero
          have ha'z : a' = 0 := by
            cases a' with
            | zero => rfl
            | oadd e'' n'' a'' =>
                have hlt := NFBelow.lt (hh ▸ hsNF).snd'; rw [repr_zero] at hlt
                exact absurd hlt not_lt_zero
          subst ha1z; subst ha'z
          have hbeq : b = oadd 0 n' 0 := by rw [← ONote.zero_add b]; exact hh
          rw [hbeq]
          rw [hardy_oadd0 (n₁ + n') x, hardy_oadd0 n₁, hardy_oadd0 n' x, PNat.add_coe]
          omega
        · have hcoeff : ∀ z, hardy (oadd e₁ (n₁ + n') a') z
              = hardy (oadd e₁ n₁ 0) (hardy (oadd e₁ n' a') z) := by
            intro z
            rw [hardy_oadd_tail e₁ (n₁ + n') a' z, hardy_oadd_tail e₁ n' a' z,
              hardy_coeff_add e₁ he₁0 n₁ n' (hardy a' z)]
          calc hardy (oadd e₁ (n₁ + n') a') x
              = hardy (oadd e₁ n₁ 0) (hardy (oadd e₁ n' a') x) := hcoeff x
            _ = hardy (oadd e₁ n₁ 0) (hardy (a₁ + b) x) := by rw [hh]
            _ ≤ hardy (oadd e₁ n₁ 0) (hardy a₁ (hardy b x)) := hardy_monotone _ (iha₁ ha₁ b hb x)
            _ = hardy (oadd e₁ n₁ a₁) (hardy b x) := (hardy_oadd_tail e₁ n₁ a₁ (hardy b x)).symm

/-- **The additive-Hardy inequality at a principal raise:** `H_{e + ω^a}(x) ≤ H_e(H_{ω^a}(x))`. -/
theorem hardy_add_omega_pow_le {e a : ONote} (he : e.NF) (ha : a.NF) (x : ℕ) :
    hardy (e + oadd a 1 0) x ≤ hardy e (hardy (oadd a 1 0) x) :=
  hardy_add_le_comp e he (oadd a 1 0) (NF.oadd ha 1 NFBelow.zero) x

end ONote
