/-
Goal: prove `ibump_mono` — monotonicity of the hereditary base-bump.

`ibump b n` = the natural number obtained from `n` by writing `n` in hereditary base-`b`
notation and replacing every `b` by `b+1`. It satisfies the peeling recursion below.
We axiomatize `ibump`, `ipow` (b^x), `ilog` (base-b log) as opaque functions with their
true defining properties, and ask for MONOTONICITY in the second argument.

Use ONLY the provided axioms + standard Nat arithmetic (Nat.div_add_mod, Nat.mod_lt, etc.).
Do NOT introduce ordinals or any other characterization of `ibump`.
-/
import Mathlib

namespace IBumpMono

axiom ipow : ℕ → ℕ → ℕ
axiom ilog : ℕ → ℕ → ℕ
axiom ibump : ℕ → ℕ → ℕ

-- power laws
axiom ipow_succ (b x : ℕ) : ipow b (x + 1) = ipow b x * b
axiom ipow_pos {b : ℕ} (hb : 0 < b) (x : ℕ) : 0 < ipow b x
axiom ipow_le_ipow_right {b : ℕ} (hb : 1 ≤ b) {x y : ℕ} (h : x ≤ y) : ipow b x ≤ ipow b y
axiom ipow_lt_ipow_right {b : ℕ} (hb : 1 < b) {x y : ℕ} (h : x < y) : ipow b x < ipow b y
axiom self_lt_ipow {b : ℕ} (hb : 2 ≤ b) (x : ℕ) : x < ipow b x

-- log laws
axiom ipow_ilog_le {b n : ℕ} (hb : 2 ≤ b) (hn : 0 < n) : ipow b (ilog b n) ≤ n
axiom lt_ipow_ilog_succ {b n : ℕ} (hb : 2 ≤ b) (hn : 0 < n) : n < ipow b (ilog b n + 1)
axiom ilog_mono {b n n' : ℕ} (hb : 2 ≤ b) (hn : 0 < n) (hle : n ≤ n') : ilog b n ≤ ilog b n'

-- bump laws
axiom ibump_zero (b : ℕ) : ibump b 0 = 0
axiom le_ibump {b : ℕ} (hb : 2 ≤ b) (n : ℕ) : n ≤ ibump b n
/-- the peel recursion at any positive argument: `e = ilog b n`, leading power `b^e`. -/
axiom ibump_pos {b : ℕ} (hb : 2 ≤ b) {n : ℕ} (hn : 0 < n) :
    ibump b n
      = n / ipow b (ilog b n) * ipow (b + 1) (ibump b (ilog b n))
        + ibump b (n % ipow b (ilog b n))

set_option maxHeartbeats 2000000 in
/-- Parametric version of the combined invariant: all the `ipow`/`ilog`/`ibump`
laws are taken as ordinary hypotheses, so the argument is purely about `ℕ`
arithmetic and uses no axioms of its own. -/
lemma ibump_combined_param
    (ipow ilog ibump : ℕ → ℕ → ℕ)
    (hpow_succ : ∀ b x, ipow b (x + 1) = ipow b x * b)
    (hpow_pos : ∀ b, 0 < b → ∀ x, 0 < ipow b x)
    (hpow_le : ∀ b, 1 ≤ b → ∀ x y, x ≤ y → ipow b x ≤ ipow b y)
    (hself_lt : ∀ b, 2 ≤ b → ∀ x, x < ipow b x)
    (hilog_le : ∀ b n, 2 ≤ b → 0 < n → ipow b (ilog b n) ≤ n)
    (hlt_ilog_succ : ∀ b n, 2 ≤ b → 0 < n → n < ipow b (ilog b n + 1))
    (hilog_mono : ∀ b n n', 2 ≤ b → 0 < n → n ≤ n' → ilog b n ≤ ilog b n')
    (hbump_zero : ∀ b, ibump b 0 = 0)
    (hle_bump : ∀ b, 2 ≤ b → ∀ n, n ≤ ibump b n)
    (hbump_pos : ∀ b, 2 ≤ b → ∀ n, 0 < n →
        ibump b n = n / ipow b (ilog b n) * ipow (b + 1) (ibump b (ilog b n))
          + ibump b (n % ipow b (ilog b n)))
    {b : ℕ} (hb : 2 ≤ b) :
    ∀ N : ℕ,
      (∀ n, 0 < n → n ≤ N →
          ibump b n < ipow (b + 1) (ibump b (ilog b n) + 1)) ∧
      (∀ n n', n' ≤ N → n < n' → ibump b n < ibump b n') := by
  intro N
  induction' N using Nat.strong_induction_on with N ih;
  refine' ⟨ fun n hn hn' => _, fun n n' hn' hn => _ ⟩;
  · set q := n / ipow b (ilog b n)
    set r := n % ipow b (ilog b n)
    have hq : q < b := by
      exact Nat.div_lt_of_lt_mul <| by nlinarith [ hlt_ilog_succ b n hb hn, hpow_succ b ( ilog b n ) ] ;
    have hr : r < ipow b (ilog b n) := by
      exact Nat.mod_lt _ ( hpow_pos _ ( by linarith ) _ )
    have hibump : ibump b n = q * ipow (b + 1) (ibump b (ilog b n)) + ibump b r := by
      exact hbump_pos b hb n hn;
    by_cases hr_pos : 0 < r;
    · have hibump_r : ibump b r < ipow (b + 1) (ibump b (ilog b r) + 1) := by
        apply (ih r (by
        exact lt_of_lt_of_le hr ( le_trans ( hilog_le b n hb hn ) hn' ))).left r hr_pos (by
        linarith);
      have hibump_log : ibump b (ilog b r) < ibump b (ilog b n) := by
        apply ih (ilog b n) (by
        grind) |>.2;
        · norm_num;
        · contrapose! hr;
          exact le_trans ( hpow_le b ( by linarith ) _ _ hr ) ( hilog_le b r hb hr_pos );
      rw [ hibump, hpow_succ ];
      nlinarith [ hpow_le ( b + 1 ) ( by linarith ) ( ibump b ( ilog b r ) + 1 ) ( ibump b ( ilog b n ) ) ( by linarith ) ];
    · simp_all +decide;
      nlinarith [ hpow_pos ( b + 1 ) ( by linarith ) ( ibump b ( ilog b n ) ) ];
  · by_cases hn_pos : 0 < n;
    · set e := ilog b n
      set e' := ilog b n'
      have he_le_e' : e ≤ e' := by
        exact hilog_mono b n n' hb hn_pos hn.le
      have he'_lt_N : e' < N := by
        grind +suggestions;
      by_cases he_eq_e' : e = e';
      · have hr_lt_P : ibump b (n % ipow b e) < ipow (b + 1) (ibump b e) := by
          by_cases hr_pos : 0 < n % ipow b e;
          · have hr_lt_P : ilog b (n % ipow b e) < e := by
              contrapose! hlt_ilog_succ;
              exact absurd ( hilog_le b ( n % ipow b e ) hb hr_pos ) ( by nlinarith [ Nat.mod_lt n ( hpow_pos b ( by linarith ) e ), hpow_le b ( by linarith ) e ( ilog b ( n % ipow b e ) ) hlt_ilog_succ ] );
            have hr_lt_P : ibump b (n % ipow b e) < ipow (b + 1) (ibump b (ilog b (n % ipow b e)) + 1) := by
              grind;
            refine lt_of_lt_of_le hr_lt_P ?_;
            apply hpow_le;
            · linarith;
            · grind +suggestions;
          · simp_all +decide;
        have hq_lt_q' : n / ipow b e < n' / ipow b e ∨ (n / ipow b e = n' / ipow b e ∧ n % ipow b e < n' % ipow b e) := by
          have hq_lt_q' : n = (n / ipow b e) * ipow b e + (n % ipow b e) ∧ n' = (n' / ipow b e) * ipow b e + (n' % ipow b e) := by
            exact ⟨ by rw [ Nat.div_add_mod' ], by rw [ Nat.div_add_mod' ] ⟩;
          exact Classical.or_iff_not_imp_left.2 fun h => ⟨ by nlinarith [ Nat.zero_le ( n % ipow b e ), Nat.zero_le ( n' % ipow b e ), Nat.mod_lt n ( hpow_pos b ( by linarith ) e ), Nat.mod_lt n' ( hpow_pos b ( by linarith ) e ) ], by nlinarith [ Nat.zero_le ( n % ipow b e ), Nat.zero_le ( n' % ipow b e ), Nat.mod_lt n ( hpow_pos b ( by linarith ) e ), Nat.mod_lt n' ( hpow_pos b ( by linarith ) e ) ] ⟩;
        rw [ hbump_pos b hb n hn_pos, hbump_pos b hb n' ( by linarith ) ];
        cases hq_lt_q' <;> simp_all +decide;
        · simp +zetaDelta at *;
          rw [ he_eq_e' ];
          nlinarith [ hpow_pos ( b + 1 ) ( by linarith ) ( ibump b ( ilog b n' ) ) ];
        · simp +zetaDelta at *;
          rw [ he_eq_e' ];
          rw [ ‹n / ipow b ( ilog b n' ) = n' / ipow b ( ilog b n' ) ∧ n % ipow b ( ilog b n' ) < n' % ipow b ( ilog b n' ) ›.1 ];
          have := ih ( n' % ipow b ( ilog b n' ) ) ( by
            exact lt_of_lt_of_le ( Nat.mod_lt _ ( hpow_pos _ ( by linarith ) _ ) ) ( by linarith [ hilog_le _ _ hb ( by linarith : 0 < n' ) ] ) );
          grind;
      · have h_ibump_n_lt_ipow : ibump b n < ipow (b + 1) (ibump b e + 1) := by
          grind;
        have h_ibump_e_plus_one_le_ibump_e' : ibump b e + 1 ≤ ibump b e' := by
          exact ih e' he'_lt_N |>.2 _ _ ( by linarith ) ( lt_of_le_of_ne he_le_e' he_eq_e' );
        have h_ipow_le_ipow : ipow (b + 1) (ibump b e + 1) ≤ ipow (b + 1) (ibump b e') := by
          exact hpow_le _ ( by linarith ) _ _ h_ibump_e_plus_one_le_ibump_e';
        rw [ hbump_pos b hb n' ( by linarith ) ];
        refine' lt_of_lt_of_le h_ibump_n_lt_ipow ( le_trans h_ipow_le_ipow _ );
        refine' le_add_of_le_of_nonneg _ _;
        · refine' Nat.le_mul_of_pos_left _ _;
          exact Nat.div_pos ( hilog_le b n' hb ( by linarith ) ) ( hpow_pos b ( by linarith ) _ );
        · exact Nat.zero_le _;
    · grind +splitIndPred

/-- Combined strong-induction invariant: an upper bound on `ibump` together with
strict monotonicity, both indexed by the maximal argument `N`. -/
lemma ibump_combined {b : ℕ} (hb : 2 ≤ b) :
    ∀ N : ℕ,
      (∀ n, 0 < n → n ≤ N →
          ibump b n < ipow (b + 1) (ibump b (ilog b n) + 1)) ∧
      (∀ n n', n' ≤ N → n < n' → ibump b n < ibump b n') :=
  ibump_combined_param ipow ilog ibump
    ipow_succ
    (fun _ hbp x => ipow_pos hbp x)
    (fun _ hbp _ _ h => ipow_le_ipow_right hbp h)
    (fun _ hbp x => self_lt_ipow hbp x)
    (fun _ _ hbp hn => ipow_ilog_le hbp hn)
    (fun _ _ hbp hn => lt_ipow_ilog_succ hbp hn)
    (fun _ _ _ hbp hn hle => ilog_mono hbp hn hle)
    ibump_zero
    (fun _ hbp n => le_ibump hbp n)
    (fun _ hbp _ hn => ibump_pos hbp hn)
    hb

/-- **The target.** The hereditary base-bump is monotone in its argument. -/
theorem ibump_mono {b : ℕ} (hb : 2 ≤ b) : ∀ {n n' : ℕ}, n ≤ n' → ibump b n ≤ ibump b n' := by
  intro n n' h
  rcases lt_or_eq_of_le h with h | h
  · exact le_of_lt ((ibump_combined hb n').2 n n' le_rfl h)
  · subst h; exact le_rfl

end IBumpMono
