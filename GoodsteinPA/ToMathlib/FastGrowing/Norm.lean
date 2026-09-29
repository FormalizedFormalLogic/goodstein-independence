/-
# `ONote` norm, successor, and tower helpers

`norm`, `osucc`, `tower` and the norm-based domination lemmas for `fastGrowing`.
-/
module

public import GoodsteinPA.ToMathlib.FastGrowing.Basic

@[expose] public section

namespace ONote

open ONote Ordinal

variable {x : ℕ} {o a b c : ONote}

/-- **No `ω`-fixed points below `ε₀`, elementarily:** for every normal-form notation, `repr o < ω ^ repr o`. -/
lemma repr_lt_opow_repr (o : ONote) (h : o.NF) : o.repr < ω ^ o.repr :=
  match o, h with
  | 0, _ => by simp
  | oadd e n a, h => by
      have hIH : e.repr < ω ^ e.repr := repr_lt_opow_repr e h.fst
      have hle : ω ^ e.repr ≤ (oadd e n a).repr := omega0_le_oadd e n a
      have helt : e.repr < (oadd e n a).repr := lt_of_lt_of_le hIH hle
      have hbelow : NFBelow (oadd e n a) (e.repr + 1) :=
        NFBelow.oadd h.fst h.snd' (Order.lt_succ _)
      have h1 : (oadd e n a).repr < ω ^ (e.repr + 1) := hbelow.repr_lt
      have h2 : ω ^ (e.repr + 1) ≤ ω ^ (oadd e n a).repr :=
        opow_le_opow_right omega0_pos (Order.succ_le_of_lt helt)
      exact lt_of_lt_of_le h1 h2

/-! ### The CNF norm and structural comparison helpers (toward general Bachmann reachability)

The general index-domination needs a **budget condition**: the diagonal argument `x` must be
large enough that the fundamental-sequence descent of `o` actually passes through `d`. The
right "size of `d`" is its **CNF norm**: the largest finite number (coefficient or finite
tail) appearing anywhere in `d`'s Cantor normal form. -/

/-- **CNF norm** of a notation: the maximum finite coefficient appearing anywhere in its
Cantor normal form (recursively through exponents and tails). `norm 0 = 0`,
`norm (ω^e·n + a) = max (norm e) (max n (norm a))`. This is the budget threshold: if
`norm d ≤ x` then the standard fundamental-sequence descent of any `o > d` reaches `d` with
budget `x` (`reaches_of_lt`). -/
def norm : ONote → ℕ
  | 0 => 0
  | oadd e n a => max (norm e) (max (n : ℕ) (norm a))

@[simp] theorem norm_zero : norm 0 = 0 := rfl

@[simp] theorem norm_oadd (e : ONote) (n : ℕ+) (a : ONote) :
    norm (oadd e n a) = max (norm e) (max (n : ℕ) (norm a)) := rfl

/-- **Trichotomy decomposition of `<` on `oadd`.** For normal-form notations,
`oadd ea na ba < oadd e m b` splits into the three lexicographic cases on
(exponent, coefficient, tail). -/
lemma lt_oadd_cases {ea : ONote} {na : ℕ+} {ba e : ONote} {m : ℕ+} {b : ONote}
    (h1 : NF (oadd ea na ba)) (h2 : NF (oadd e m b)) (h : oadd ea na ba < oadd e m b) :
    ea < e ∨ (ea = e ∧ (na : ℕ) < (m : ℕ)) ∨ (ea = e ∧ na = m ∧ ba < b) := by
  rcases lt_trichotomy ea.repr e.repr with he | he | he
  · exact Or.inl (lt_def.2 he)
  · have heq : ea = e := (@repr_inj ea e h1.fst h2.fst).1 he
    subst heq
    rcases lt_trichotomy (na : ℕ) (m : ℕ) with hn | hn | hn
    · exact Or.inr (Or.inl ⟨rfl, hn⟩)
    · have hnm : na = m := PNat.coe_injective hn
      subst hnm
      rcases lt_trichotomy ba.repr b.repr with hb | hb | hb
      · exact Or.inr (Or.inr ⟨rfl, rfl, lt_def.2 hb⟩)
      · have hbeq : ba = b := (@repr_inj ba b h1.snd h2.snd).1 hb
        subst hbeq; exact absurd h (lt_irrefl _)
      · exact absurd (oadd_lt_oadd_3 (lt_def.2 hb)) (lt_asymm h)
    · exact absurd (oadd_lt_oadd_2 h2 hn) (lt_asymm h)
  · exact absurd (oadd_lt_oadd_1 h2 (lt_def.2 he)) (lt_asymm h)

/-- **Norm bound on a single CNF level:** if a normal-form `d` has leading exponent `≤ c`
and norm `≤ x`, then `d < ω^c·(x+1)`. -/
lemma lt_oadd_of_lead_le (hc : c.NF) {d : ONote} (hd : d.NF)
    (hlead : d.repr < ω ^ c.repr * ω) (hnorm : norm d ≤ x) :
    d < oadd c x.succPNat 0 := by
  cases d with
  | zero => exact oadd_pos _ _ _
  | oadd ed nd bd =>
    have hpow : ω ^ ed.repr ≤ (oadd ed nd bd).repr := omega0_le_oadd ed nd bd
    have h2 : (ω : Ordinal) ^ ed.repr < ω ^ c.repr * ω := lt_of_le_of_lt hpow hlead
    rw [← opow_succ] at h2
    have hed_le : ed.repr ≤ c.repr :=
      Order.lt_succ_iff.1 ((opow_lt_opow_iff_right one_lt_omega0).1 h2)
    rcases lt_or_eq_of_le hed_le with hlt | heq
    · exact oadd_lt_oadd_1 hd (lt_def.2 hlt)
    · have hedc : ed = c := (@repr_inj ed c hd.fst hc).1 heq
      subst hedc
      rw [norm_oadd] at hnorm
      have hnd : (nd : ℕ) ≤ x := (le_max_of_le_right (le_max_left _ _)).trans hnorm
      refine oadd_lt_oadd_2 hd ?_
      simpa [Nat.succPNat] using Nat.lt_succ_of_le hnd

/-- **The key cofinality bound (general Bachmann reachability core):** for a normal-form limit `o`
with fundamental sequence `g`, every `d < o` with norm `≤ x` sits below the `x`-th rung `g x`. -/
theorem lt_fundamentalSequence_of_norm_le (o : ONote) (ho : o.NF) (g : ℕ → ONote)
    (hg : fundamentalSequence o = Sum.inr g) (d : ONote) (hd : d.NF) (hdo : d < o)
    (hnorm : norm d ≤ x) : d < g x := by
  induction o generalizing g d with
  | zero => exact (Sum.inl_ne_inr hg).elim
  | oadd a m b iha ihb =>
    rcases hb : fundamentalSequence b with (_ | b') | hbf
    · -- b = 0 : leading-term cases
      rcases ha : fundamentalSequence a with (_ | a') | p
      · -- a = 0 : `oadd 0 m 0` is a successor → contradicts the limit `hg`
        rcases hm : m.natPred with _ | k
        · rw [fundamentalSequence, hb, ha, hm] at hg; exact (Sum.inl_ne_inr hg).elim
        · rw [fundamentalSequence, hb, ha, hm] at hg; exact (Sum.inl_ne_inr hg).elim
      · -- a a successor (predecessor `a'`)
        have hpa := fundamentalSequence_has_prop a; rw [ha] at hpa
        have ha'NF : a'.NF := hpa.2 ho.fst
        have harepr : a.repr = Order.succ a'.repr := hpa.1
        have hb0 : b = 0 := by have hpb := fundamentalSequence_has_prop b; rwa [hb] at hpb
        rcases hm : m.natPred with _ | k
        · -- L2 : `g = fun i => ω^a'·(i+1)`, `m = 1`
          have hg' : g = fun i => oadd a' i.succPNat 0 := by
            rw [fundamentalSequence, hb, ha, hm] at hg; exact (Sum.inr.inj hg).symm
          have hm1 : m = 1 := by rw [← PNat.succPNat_natPred m, hm]; rfl
          rw [hg']
          refine lt_oadd_of_lead_le ha'NF hd ?_ hnorm
          have hlt : d.repr < (oadd a m b).repr := lt_def.1 hdo
          rw [hb0, hm1] at hlt
          rw [show (oadd a 1 0).repr = ω ^ a.repr from by
            simp only [ONote.repr, PNat.one_coe, Nat.cast_one, mul_one, add_zero]] at hlt
          rw [harepr, opow_succ] at hlt
          exact hlt
        · -- L3 : `g = fun i => ω^a·(k+1) + ω^a'·(i+1)`, `m = k+2`
          have hg' : g = fun i => oadd a k.succPNat (oadd a' i.succPNat 0) := by
            rw [fundamentalSequence, hb, ha, hm] at hg; exact (Sum.inr.inj hg).symm
          have hmval : (m : ℕ) = k + 2 := by rw [← PNat.succPNat_natPred m, hm]; rfl
          rw [hg']
          cases d with
          | zero => exact oadd_pos _ _ _
          | oadd ea na ba =>
            rw [hb0] at hdo
            rcases lt_oadd_cases hd (hb0 ▸ ho) hdo with hlt | ⟨heq, hnlt⟩ | ⟨_, _, hbalt⟩
            · exact oadd_lt_oadd_1 hd hlt
            · rw [heq] at hd hnorm ⊢
              rw [hmval] at hnlt
              rcases Nat.lt_or_ge (na : ℕ) (k + 1) with hna | hna
              · exact oadd_lt_oadd_2 hd (by simpa [Nat.succPNat] using hna)
              · have hnak : (na : ℕ) = k + 1 := le_antisymm (by omega) hna
                have hnaP : na = k.succPNat := PNat.coe_injective (by simpa [Nat.succPNat] using hnak)
                subst hnaP
                refine oadd_lt_oadd_3 ?_
                refine lt_oadd_of_lead_le ha'NF hd.snd ?_ ?_
                · have hba : ba.repr < ω ^ a.repr := hd.snd'.repr_lt
                  rw [harepr, opow_succ] at hba; exact hba
                · rw [norm_oadd] at hnorm
                  exact (le_max_of_le_right (le_max_right _ _)).trans hnorm
            · have hr := lt_def.1 hbalt; rw [repr_zero] at hr
              exact absurd hr not_lt_zero
      · -- a a limit (fundamental sequence `p`)
        have hb0 : b = 0 := by have hpb := fundamentalSequence_has_prop b; rwa [hb] at hpb
        rcases hm : m.natPred with _ | k
        · -- L4 : `g = fun i => ω^(a[i])`, `m = 1`
          have hg' : g = fun i => oadd (p i) 1 0 := by
            rw [fundamentalSequence, hb, ha, hm] at hg; exact (Sum.inr.inj hg).symm
          have hm1 : m = 1 := by rw [← PNat.succPNat_natPred m, hm]; rfl
          rw [hg']
          cases d with
          | zero => exact oadd_pos _ _ _
          | oadd ea na ba =>
            rw [hb0, hm1] at hdo
            rcases lt_oadd_cases hd ((hb0 ▸ hm1 ▸ ho : NF (oadd a 1 0))) hdo
              with hlt | ⟨rfl, hnlt⟩ | ⟨rfl, _, hbalt⟩
            · have hnorm_ea : norm ea ≤ x := by
                rw [norm_oadd] at hnorm; exact (le_max_left _ _).trans hnorm
              have hep : ea < p x := iha ho.fst p ha ea hd.fst hlt hnorm_ea
              exact oadd_lt_oadd_1 hd hep
            · simp only [PNat.one_coe] at hnlt; exact absurd hnlt (by have := na.pos; omega)
            · have hr := lt_def.1 hbalt; rw [repr_zero] at hr
              exact absurd hr not_lt_zero
        · -- L5 : `g = fun i => ω^a·(k+1) + ω^(a[i])`, `m = k+2`
          have hg' : g = fun i => oadd a k.succPNat (oadd (p i) 1 0) := by
            rw [fundamentalSequence, hb, ha, hm] at hg; exact (Sum.inr.inj hg).symm
          have hmval : (m : ℕ) = k + 2 := by rw [← PNat.succPNat_natPred m, hm]; rfl
          rw [hg']
          cases d with
          | zero => exact oadd_pos _ _ _
          | oadd ea na ba =>
            rw [hb0] at hdo
            rcases lt_oadd_cases hd (hb0 ▸ ho) hdo with hlt | ⟨heq, hnlt⟩ | ⟨_, _, hbalt⟩
            · exact oadd_lt_oadd_1 hd hlt
            · rw [heq] at hd hnorm ⊢
              rw [hmval] at hnlt
              rcases Nat.lt_or_ge (na : ℕ) (k + 1) with hna | hna
              · exact oadd_lt_oadd_2 hd (by simpa [Nat.succPNat] using hna)
              · have hnak : (na : ℕ) = k + 1 := le_antisymm (by omega) hna
                have hnaP : na = k.succPNat := PNat.coe_injective (by simpa [Nat.succPNat] using hnak)
                subst hnaP
                refine oadd_lt_oadd_3 ?_
                cases ba with
                | zero => exact oadd_pos _ _ _
                | oadd eb nb bb =>
                  have heb : eb.repr < a.repr := by
                    have hbb : (oadd eb nb bb).repr < ω ^ a.repr := hd.snd'.repr_lt
                    have hle : ω ^ eb.repr ≤ (oadd eb nb bb).repr := omega0_le_oadd eb nb bb
                    exact (opow_lt_opow_iff_right one_lt_omega0).1 (lt_of_le_of_lt hle hbb)
                  have hnorm_eb : norm eb ≤ x := by
                    rw [norm_oadd, norm_oadd] at hnorm
                    exact (le_max_of_le_right (le_max_of_le_right (le_max_left _ _))).trans hnorm
                  have hep : eb < p x := iha ho.fst p ha eb hd.snd.fst (lt_def.2 heb) hnorm_eb
                  exact oadd_lt_oadd_1 hd.snd hep
            · have hr := lt_def.1 hbalt; rw [repr_zero] at hr
              exact absurd hr not_lt_zero
    · -- b a successor ⟹ `oadd a m b` is a successor → contradicts the limit `hg`
      rw [fundamentalSequence_oadd_succ hb] at hg; exact (Sum.inl_ne_inr hg).elim
    · -- L1 : b a limit, `g = fun i => oadd a m (b[i])` ; descend the tail
      have hg' : g = fun i => oadd a m (hbf i) := by
        rw [fundamentalSequence_oadd_limit hb] at hg; exact (Sum.inr.inj hg).symm
      rw [hg']
      cases d with
      | zero => exact oadd_pos _ _ _
      | oadd ea na ba =>
        rcases lt_oadd_cases hd ho hdo with hlt | ⟨rfl, hnlt⟩ | ⟨rfl, hnm, hbalt⟩
        · exact oadd_lt_oadd_1 hd hlt
        · exact oadd_lt_oadd_2 hd hnlt
        · subst hnm
          have hnorm_ba : norm ba ≤ x := by
            rw [norm_oadd] at hnorm; exact (le_max_of_le_right (le_max_right _ _)).trans hnorm
          exact oadd_lt_oadd_3 (ihb ho.snd hbf hb ba hd.snd hbalt hnorm_ba)

/-- **General Bachmann reachability:** for normal-form `d < o` with budget `x ≥ norm d`,
the standard fundamental-sequence descent of `o` reaches `d`. -/
theorem reaches_of_lt (o : ONote) (ho : o.NF) (d : ONote) (hd : d.NF) (hdo : d < o) (hnorm : norm d ≤ x) :
    Reaches x o d := by
  rcases e : fundamentalSequence o with (_ | c) | g
  · exfalso
    have ho0 : o = 0 := by have hp := fundamentalSequence_has_prop o; rwa [e] at hp
    rw [ho0] at hdo
    have hr : d.repr < 0 := by rw [← repr_zero]; exact lt_def.1 hdo
    exact absurd hr not_lt_zero
  · have hp := fundamentalSequence_has_prop o; rw [e] at hp
    have hcNF : c.NF := hp.2 ho
    have hco : c < o := lt_def.2 (by rw [hp.1]; exact Order.lt_succ _)
    have hdr : d.repr ≤ c.repr := Order.lt_succ_iff.1 (by rw [← hp.1]; exact lt_def.1 hdo)
    rcases eq_or_lt_of_le hdr with heq | hlt
    · have hdc : d = c := (@repr_inj d c hd hcNF).1 heq
      subst hdc; exact Reaches.succ e (Reaches.refl _)
    · exact Reaches.succ e (reaches_of_lt c hcNF d hd (lt_def.2 hlt) hnorm)
  · have hp := fundamentalSequence_has_prop o; rw [e] at hp
    have hgxNF : (g x).NF := (hp.2.1 x).2.2 ho
    have hgxlt : g x < o := (hp.2.1 x).2.1
    have hdgx : d < g x := lt_fundamentalSequence_of_norm_le o ho g e d hd hdo hnorm
    exact Reaches.limit e (reaches_of_lt (g x) hgxNF d hd hdgx hnorm)
termination_by o
decreasing_by all_goals assumption

/-- **Strict successor index step:** at a notation-successor `o` (predecessor `a`), for `n ≥ 2`, `f_a(n) < f_o(n)`. -/
lemma fastGrowing_lt_succ_index (h : fundamentalSequence o = Sum.inl (some a)) {n : ℕ} (hn : 2 ≤ n) :
    fastGrowing a n < fastGrowing o n := by
  rw [fastGrowing_succ o h]
  have hexp : (id : ℕ → ℕ) ≤ fastGrowing a := fun m => le_fastGrowing a m
  have h1n : 1 ≤ n := le_trans one_le_two hn
  have hge : n ≤ fastGrowing a n := le_fastGrowing a n
  have hlt2 : fastGrowing a n < fastGrowing a (fastGrowing a n) :=
    lt_fastGrowing a (le_trans h1n hge)
  have hstep2 : (fastGrowing a)^[2] n ≤ (fastGrowing a)^[n] n :=
    Function.monotone_iterate_of_id_le hexp hn n
  have h2eq : (fastGrowing a)^[2] n = fastGrowing a (fastGrowing a n) := by
    rw [Function.iterate_succ_apply', Function.iterate_one]
  calc fastGrowing a n < fastGrowing a (fastGrowing a n) := hlt2
    _ = (fastGrowing a)^[2] n := h2eq.symm
    _ ≤ (fastGrowing a)^[n] n := hstep2

/-- **General index monotonicity of the fast-growing hierarchy:** for normal-form `d < o`
with `1 ≤ x ≥ norm d`, `f_d(x) ≤ f_o(x)`. -/
theorem fastGrowing_le_of_lt (hx : 1 ≤ x) (hd : d.NF) (ho : o.NF) (hdo : d < o) (hnorm : norm d ≤ x) :
    fastGrowing d x ≤ fastGrowing o x :=
  fastGrowing_le_of_reaches hx (reaches_of_lt o ho d hd hdo hnorm)

/-- A normal-form `oadd 0 n a` (leading exponent `0`) has a zero tail: `NF` forces `a.repr < ω^0 = 1`, hence `a = 0`. -/
lemma tail_eq_zero_of_zero_exponent {n : ℕ+} {a : ONote} (h : (oadd 0 n a).NF) : a = 0 := by
  have hlt : a.repr < ω ^ (0 : ONote).repr := h.snd'.repr_lt
  rw [repr_zero, opow_zero] at hlt
  exact (@repr_inj a 0 h.snd NF.zero).1 (by rw [repr_zero]; exact Order.lt_one_iff.1 hlt)

/-! ### The notation successor `osucc` (for strict index domination)

Uses structural fundamental-sequence descent to achieve `Reaches n (tower n) (osucc o)`.
-/

/-- The **notation successor** `osucc o`: a structural definition giving `repr (osucc o) = repr o + 1`
and `fundamentalSequence (osucc o) = inl (some o)` on normal forms. -/
def osucc : ONote → ONote
  | 0 => oadd 0 1 0
  | oadd 0 n _ => oadd 0 (n + 1) 0
  | oadd (oadd e' n' a') m b => oadd (oadd e' n' a') m (osucc b)

@[grind =]
lemma repr_osucc {o : ONote} (h : o.NF) : (osucc o).repr = o.repr + 1 :=
  match o, h with
  | 0, _ => by simp [osucc]
  | oadd 0 n a, h => by
      have ha0 := tail_eq_zero_of_zero_exponent h
      subst ha0
      show (oadd 0 (n + 1) 0).repr = (oadd 0 n 0).repr + 1
      simp only [ONote.repr, opow_zero, one_mul, add_zero, PNat.add_coe,
        PNat.one_coe, Nat.cast_add, Nat.cast_one]
  | oadd (oadd e' n' a') m b, h => by
      show (oadd (oadd e' n' a') m (osucc b)).repr = (oadd (oadd e' n' a') m b).repr + 1
      simp only [ONote.repr]
      rw [repr_osucc h.snd, ← add_assoc]

@[grind →]
lemma osucc_NF {o : ONote} (h : o.NF) : (osucc o).NF :=
  match o, h with
  | 0, _ => NF.oadd_zero 0 1
  | oadd 0 n _, _ => NF.oadd_zero 0 (n + 1)
  | oadd (oadd e' n' a') m b, h => by
      refine NF.oadd h.fst m (NF.below_of_lt' ?_ (osucc_NF h.snd))
      rw [repr_osucc h.snd, ← Order.succ_eq_add_one]
      have hElim : Order.IsSuccLimit (ω ^ (oadd e' n' a').repr) := by
        refine isSuccLimit_opow_left isSuccLimit_omega0 ?_
        have hpos : (0 : Ordinal) < (oadd e' n' a').repr := by
          rw [← repr_zero]; exact lt_def.1 (oadd_pos e' n' a')
        exact hpos.ne'
      exact hElim.succ_lt h.snd'.repr_lt

@[grind =]
lemma fundamentalSequence_osucc {o : ONote} (h : o.NF) : fundamentalSequence (osucc o) = Sum.inl (some o) :=
  match o, h with
  | 0, _ => rfl
  | oadd 0 n a, h => by
      have ha0 := tail_eq_zero_of_zero_exponent h
      subst ha0
      obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k.succPNat := ⟨n.natPred, (PNat.succPNat_natPred n).symm⟩
      rfl
  | oadd (oadd e' n' a') m b, h =>
      fundamentalSequence_oadd_succ (fundamentalSequence_osucc h.snd)

-- No `grind` attribute: `@[grind →]` needs a propositional hypothesis (there is none here),
-- and `@[grind =]` needs an equality conclusion (this is a `≤`).
lemma norm_osucc_le {o : ONote} : norm (osucc o) ≤ norm o + 1 :=
  match o with
  | 0 => by simp [osucc, norm]
  | oadd 0 n _ => by
      simp only [osucc, norm_oadd, norm_zero, PNat.add_coe, PNat.one_coe]; omega
  | oadd (oadd e' n' a') m b => by
      have ih : norm (osucc b) ≤ norm b + 1 := norm_osucc_le
      simp only [osucc, norm_oadd]; omega

/-- The **diagonal tower** `0, 1, ω, ω^ω, …` underlying `fastGrowingε₀`. -/
def tower (i : ℕ) : ONote := (fun a => oadd a 1 0)^[i] 0

@[simp] theorem tower_zero : tower 0 = 0 := rfl

/-- `tower (i+1) = ω^{tower i}`. -/
lemma tower_succ (i : ℕ) : tower (i + 1) = oadd (tower i) 1 0 := by
  rw [tower, tower, Function.iterate_succ_apply']

/-- Every tower level is a normal-form notation. -/
lemma tower_NF (i : ℕ) : (tower i).NF :=
  match i with
  | 0 => by rw [tower_zero]; exact NF.zero
  | i + 1 => by rw [tower_succ]; haveI := tower_NF i; exact NF.oadd_zero _ _

/-- The tower is **strictly increasing:** `tower i < tower (i+1) = ω^{tower i}`. -/
lemma tower_lt_succ (i : ℕ) : tower i < tower (i + 1) := by
  rw [tower_succ, lt_def]
  have hrepr : ((tower i).oadd 1 0).repr = ω ^ (tower i).repr := by
    simp only [ONote.repr, PNat.one_coe, Nat.cast_one, mul_one, add_zero]
  rw [hrepr]
  exact repr_lt_opow_repr _ (tower_NF i)

/-- The tower is monotone in its index. -/
lemma tower_strictMono : StrictMono tower :=
  strictMono_nat_of_lt_succ tower_lt_succ

/-- `repr (tower (i+1)) = ω ^ repr (tower i)`. -/
lemma repr_tower_succ (i : ℕ) : (tower (i + 1)).repr = ω ^ (tower i).repr := by
  rw [tower_succ]
  simp only [ONote.repr, PNat.one_coe, Nat.cast_one, mul_one, add_zero]

/-- **Cofinality of the tower in `ε₀`:** every normal-form notation is below some tower level. -/
theorem tower_cofinal (o : ONote) (h : o.NF) : ∃ k, o < tower k :=
  match o, h with
  | 0, _ => ⟨1, by rw [lt_def]; simp [tower_succ]⟩
  | oadd e n a, h => by
      obtain ⟨j, hj⟩ := tower_cofinal e h.fst
      refine ⟨j + 1, ?_⟩
      rw [lt_def, repr_tower_succ]
      have hej : e.repr < (tower j).repr := (lt_def).mp hj
      have hbelow : NFBelow (oadd e n a) (e.repr + 1) :=
        NFBelow.oadd h.fst h.snd' (Order.lt_succ _)
      have h1 : (oadd e n a).repr < ω ^ (e.repr + 1) := hbelow.repr_lt
      have h2 : ω ^ (e.repr + 1) ≤ ω ^ (tower j).repr :=
        opow_le_opow_right omega0_pos (Order.succ_le_of_lt hej)
      exact lt_of_lt_of_le h1 h2

/-! ### `osucc` strict order facts -/

lemma lt_osucc (h : o.NF) : o < osucc o :=
  lt_def.mpr (by rw [repr_osucc h]; exact lt_add_one _)

/-- `osucc` is strictly monotone on normal-form notations. -/
lemma osucc_lt_osucc {x y : ONote} (hx : x.NF) (hy : y.NF) (h : x < y) : osucc x < osucc y := by
  refine lt_def.mpr ?_
  rw [repr_osucc hx, repr_osucc hy, ← Order.succ_eq_add_one, ← Order.succ_eq_add_one]
  exact Order.succ_lt_succ (lt_def.mp h)

/-- `x < y ⟹ x < osucc y` (NF). -/
lemma lt_osucc_of_lt {x y : ONote} (hy : y.NF) (h : x < y) : x < osucc y :=
  lt_trans h (lt_osucc hy)

/-! ### Ordinal addition and `norm` bookkeeping on normal forms -/

/-- Strict monotonicity of `+` in the right summand, on normal-form notations. -/
lemma add_lt_add_left_NF (haNF : a.NF) (hc'NF : c'.NF) (hcNF : c.NF) (h : c' < c) : a + c' < a + c := by
  haveI := haNF; haveI := hc'NF; haveI := hcNF
  exact lt_def.mpr (by rw [repr_add, repr_add]; exact (add_lt_add_iff_left _).mpr (lt_def.mp h))

lemma le_add_left_NF (haNF : a.NF) (hcNF : c.NF) : c ≤ a + c := by
  haveI := haNF; haveI := hcNF
  exact le_def.mpr (by rw [repr_add]; exact le_add_self)

lemma le_add_right_NF (haNF : a.NF) (hcNF : c.NF) : a ≤ a + c := by
  haveI := haNF; haveI := hcNF
  exact le_def.mpr (by rw [repr_add]; exact le_self_add)

/-- Combines `add_lt_add_left_NF` and `osucc_lt_osucc`: `osucc (a + c') < osucc (a + c)` whenever `c' < c`. -/
lemma add_osucc_descent (haNF : a.NF) (hc'NF : c'.NF) (hcNF : c.NF) (h : c' < c) : osucc (a + c') < osucc (a + c) :=
  osucc_lt_osucc (ONote.add_nf a c') (ONote.add_nf a c) (add_lt_add_left_NF haNF hc'NF hcNF h)

@[simp] theorem norm_omegaPow {a : ONote} : norm (oadd a 1 0) = max (norm a) 1 := by
  simp [norm_oadd]

/-- **Additive bound for `norm` under `+` on normal-form arguments:**
`norm (b + c) ≤ norm b + norm c` when both are NF. -/
lemma norm_add_le_of_nf (hb : b.NF) (hc : c.NF) : norm (b + c) ≤ norm b + norm c := by
  induction b generalizing c with
  | zero => simp
  | oadd e n a ihe iha =>
    have ha : a.NF := hb.snd
    haveI := ha; haveI := hc
    have iha' : norm (a + c) ≤ norm a + norm c := iha ha hc
    rw [oadd_add]
    rcases hr : a + c with _ | ⟨e', n', a'⟩
    · simp only [addAux, norm_oadd, norm_zero]; omega
    · rw [hr] at iha'
      simp only [norm_oadd] at iha'
      simp only [addAux]
      rcases hcmp : ONote.cmp e e' with _ | _ | _
      · simp only [norm_oadd]; omega
      · have hee : e = e' := eq_of_cmp_eq hcmp
        have hge : Ordinal.omega0 ^ ONote.repr e ≤ ONote.repr (a + c) := by
          rw [hr, hee]; exact omega0_le_oadd e' n' a'
        have hra : ONote.repr a < Ordinal.omega0 ^ ONote.repr e := hb.snd'.repr_lt
        have hgc : Ordinal.omega0 ^ ONote.repr e ≤ ONote.repr c := by
          by_contra hlt
          push Not at hlt
          have : ONote.repr a + ONote.repr c < Ordinal.omega0 ^ ONote.repr e :=
            (Ordinal.isPrincipal_add_omega0_opow (ONote.repr e)) hra hlt
          rw [repr_add] at hge
          exact absurd (lt_of_le_of_lt hge this) (lt_irrefl _)
        have habs : a + c = c := by
          have : ONote.repr (a + c) = ONote.repr c := by
            rw [repr_add]; exact Ordinal.add_of_omega0_opow_le hra hgc
          exact repr_inj.mp this
        have hnc : norm c = max (norm e') (max (n':ℕ) (norm a')) := by
          rw [← habs, hr]; simp [norm_oadd]
        simp only [norm_oadd, PNat.add_coe]; omega
      · simp only [norm_oadd]; omega

/-! ### Clean-append refinement: a `max`-bound for `norm` under `+` -/

/-- Every leading exponent of `a` dominates `b`'s value (`b.repr < ω^(repr e)`, recursively
through `a`'s tail). The clean-append condition under which `a + b` grafts `b` on as a tail
without merging any coefficients. -/
def AllExpAbove (b : ONote) : ONote → Prop
  | 0 => True
  | oadd e _ a' => b.repr < ω ^ e.repr ∧ AllExpAbove b a'

/-- **Clean-append refinement of `norm_add_le_of_nf`:** if every exponent of `a` dominates `b`
(`AllExpAbove b a`), addition appends `b` as a tail without merging coefficients, so
`norm (a + b) ≤ max (norm a) (norm b)`. -/
@[grind →]
lemma norm_add_clean {b : ONote} (hb : b.NF) :
    ∀ {a : ONote}, a.NF → AllExpAbove b a → norm (a + b) ≤ max (norm a) (norm b)
  | 0, _, _ => by rw [zero_add]; exact le_max_right _ _
  | oadd e n a', hNF, hab => by
      obtain ⟨hbe, hab'⟩ := hab
      have hNFe : e.NF := hNF.fst
      have hNFa' : a'.NF := hNF.snd
      have ih := norm_add_clean hb hNFa' hab'
      have hbelow : NFBelow (a' + b) e.repr := add_nfBelow hNF.snd' (NF.below_of_lt' hbe hb)
      have hadd : oadd e n a' + b = oadd e n (a' + b) := by
        rw [oadd_add]
        cases h : a' + b with
        | zero => simp [addAux]
        | oadd e'' n'' a'' =>
            have hbXo := h ▸ hbelow
            have hNFe'' : e''.NF := hbXo.fst
            have hlt : e''.repr < e.repr := hbXo.lt
            have hcmp : cmp e e'' = Ordering.gt := by
              have hc := @cmp_compares e e'' hNFe hNFe''
              rcases hco : cmp e e'' with _ | _ | _
              · rw [hco] at hc; exact absurd (lt_def.1 hc) (not_lt.2 hlt.le)
              · rw [hco] at hc; exact absurd (congrArg repr hc) (ne_of_gt hlt)
              · rfl
            simp [addAux, hcmp]
      rw [hadd, norm_oadd, norm_oadd]
      omega

end ONote
