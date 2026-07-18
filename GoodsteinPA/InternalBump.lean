/-
# `InternalBump.lean` — E-core(b) brick 4: the hereditary base-change `bump` inside `V`

Brick 4 (`DESCENT-PLAN.md §3`). `Defs.bump b n` is course-of-values recursion (it recurses at
`e = log_b n` and `r = n mod b^e`, both `< n`). To realize it inside `V ⊧ₘ* 𝗜𝚺₁` we use the standard
table reduction of strong recursion to primitive recursion (`HFS/PRF.lean`'s `PR.Construction`):

* `bumpNext b M s` — the value `bump b M` computed from the **table** `s = ⟨bump b 0,…,bump b (M-1)⟩`
  (length `M`): peel the top base-`b` power of `M` and read the two recursive sub-results out of `s`.

This file establishes `bumpNext` and its `𝚺₁`-definability (the artifact the table's `PR.Blueprint`
references). Brick 4b will assemble the table itself via `PR.Construction`, brick 4c will read off
`ibump b n := (table b n).[n]` and prove it satisfies `Defs.bump`'s recursion.
-/
import GoodsteinPA.InternalLog
import GoodsteinPA.Compat

namespace GoodsteinPA.InternalPow

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.HierarchySymbol

variable {V : Type*} [ORingStructure V] [V ⊧ₘ* 𝗜𝚺₁]

/-- **Table step of `bump`.** Given the table `s = ⟨bump b 0,…,bump b (M-1)⟩`, compute `bump b M` by
peeling the top base-`b` power: `e = ilog b M`, top coefficient `M / b^e`, exponent result `s.[e]`,
remainder result `s.[M % b^e]`. (For `M ≥ 1` with a correct table this equals `Defs.bump b M`.) -/
noncomputable def bumpNext (b M s : V) : V :=
  M / ipow b (ilog b M) * ipow (b + 1) (znth s (ilog b M)) + znth s (M % ipow b (ilog b M))

/-- The `𝚺₁` graph-definition of `bumpNext`, composing `ilog`, `ipow`, `znth`, `div`, `rem`. -/
def _root_.LO.FirstOrder.Arithmetic.bumpNextDef : 𝚺₁.Semisentence 4 := .mkSigma
  “y b M s.
    ∃ e, !ilogDef e b M ∧ ∃ pe, !ipowDef pe b e ∧ ∃ te, !znthDef te s e ∧
      ∃ pte, !ipowDef pte (b + 1) te ∧ ∃ q, !divDef q M pe ∧ ∃ r, !remDef r M pe ∧
        ∃ tr, !znthDef tr s r ∧ y = q * pte + tr”

instance bumpNext_defined : 𝚺₁-Function₃ (bumpNext : V → V → V → V) via bumpNextDef := .mk fun v ↦ by
  simp [bumpNextDef, bumpNext, ilog_defined.iff, ipow_defined.iff, znth_defined.iff,
    div_defined.iff, rem_defined.iff]

instance bumpNext_definable : 𝚺₁-Function₃ (bumpNext : V → V → V → V) := bumpNext_defined.to_definable

/-! ### The `bump` table via primitive recursion -/

/-- Blueprint for the `bump` table: `bumpTable b 0 = ⟨0⟩`, `bumpTable b (n+1)` appends
`bumpNext b (n+1) (bumpTable b n)`. -/
def bumpTable.blueprint : PR.Blueprint 1 where
  zero := .mkSigma “y x. !mkSeq₁Def y 0”
  succ := .mkSigma “y ih n x. ∃ v, !bumpNextDef v x (n + 1) ih ∧ !seqConsDef y ih v”

noncomputable def bumpTable.construction : PR.Construction V bumpTable.blueprint where
  zero := fun _ ↦ !⟦0⟧
  succ := fun x n ih ↦ seqCons ih (bumpNext (x 0) (n + 1) ih)
  zero_defined := .mk fun v ↦ by
    simp [bumpTable.blueprint, mkSeq₁Def, seqCons_defined.iff, emptyset_def]
  succ_defined := .mk fun v ↦ by
    simp [bumpTable.blueprint, bumpNext_defined.iff, seqCons_defined.iff]

/-- **The `bump` table** inside `V`: `ibumpTable b n = ⟨bump b 0,…,bump b n⟩` (length `n+1`). -/
noncomputable def ibumpTable (b n : V) : V := bumpTable.construction.result ![b] n

@[simp] lemma ibumpTable_zero (b : V) : ibumpTable b 0 = !⟦0⟧ := by
  simp [ibumpTable, bumpTable.construction]

@[simp] lemma ibumpTable_succ (b n : V) :
    ibumpTable b (n + 1) = seqCons (ibumpTable b n) (bumpNext b (n + 1) (ibumpTable b n)) := by
  simp [ibumpTable, bumpTable.construction]

/-- **Internalized hereditary base-change** `bump b n` in `V`: the `n`-th entry of the table. -/
noncomputable def ibump (b n : V) : V := znth (ibumpTable b n) n

section

def _root_.LO.FirstOrder.Arithmetic.ibumpTableDef : 𝚺₁.Semisentence 3 :=
  bumpTable.blueprint.resultDef.rew (Rew.subst ![#0, #2, #1])

instance ibumpTable_defined : 𝚺₁-Function₂ (ibumpTable : V → V → V) via ibumpTableDef := .mk
  fun v ↦ by simp [bumpTable.construction.result_defined_iff, ibumpTableDef]; rfl

instance ibumpTable_definable : 𝚺₁-Function₂ (ibumpTable : V → V → V) := ibumpTable_defined.to_definable

instance ibumpTable_definable' (Γ) : Γ-[m + 1]-Function₂ (ibumpTable : V → V → V) :=
  ibumpTable_definable.of_sigmaOne

def _root_.LO.FirstOrder.Arithmetic.ibumpDef : 𝚺₁.Semisentence 3 := .mkSigma
  “y b n. ∃ t, !ibumpTableDef t b n ∧ !znthDef y t n”

instance ibump_defined : 𝚺₁-Function₂ (ibump : V → V → V) via ibumpDef := .mk fun v ↦ by
  simp [ibumpDef, ibump, ibumpTable_defined.iff, znth_defined.iff]

instance ibump_definable : 𝚺₁-Function₂ (ibump : V → V → V) := ibump_defined.to_definable

instance ibump_definable' (Γ) : Γ-[m + 1]-Function₂ (ibump : V → V → V) :=
  ibump_definable.of_sigmaOne

end

/-! ### Structural correctness of the table

`definability`/aesop cannot discharge predicates over `ibumpTable` (its `PR.result` definability
leaf makes the `isDefEq` search blow up), so the `𝚺₁`-predicate side conditions of the inductions
below are supplied as **explicit composition terms** via the helpers here. -/

/-- `fun v ↦ ibumpTable b (v i)` is `𝚺₁`-definable (explicit composition, no search). -/
private lemma def_ibumpTable {k} (b : V) (i : Fin k) :
    𝚺-[1].DefinableFunction (fun v : Fin k → V ↦ ibumpTable b (v i)) :=
  DefinableFunction₂.comp (F := ibumpTable) (DefinableFunction.const b) (DefinableFunction.var i)

private lemma def_ibump {k} (b : V) (i : Fin k) :
    𝚺-[1].DefinableFunction (fun v : Fin k → V ↦ ibump b (v i)) :=
  DefinableFunction₂.comp (F := ibump) (DefinableFunction.const b) (DefinableFunction.var i)

@[simp] lemma ibumpTable_seq (b n : V) : Seq (ibumpTable b n) := by
  induction n using ISigma1.sigma1_succ_induction
  · exact Definable.comp₁ (def_ibumpTable b 0)
  case zero => simp
  case succ n ih => rw [ibumpTable_succ]; exact ih.seqCons _

@[simp] lemma ibumpTable_lh (b n : V) : lh (ibumpTable b n) = n + 1 := by
  induction n using ISigma1.sigma1_succ_induction
  · exact Definable.comp₂ (DefinableFunction₁.comp (F := lh) (def_ibumpTable b 0))
      (by definability)
  case zero => simp
  case succ n ih => rw [ibumpTable_succ, Seq.lh_seqCons _ (ibumpTable_seq b n), ih]

/-- Earlier entries of a `seqCons` are preserved. -/
lemma znth_seqCons_of_lt {s : V} (h : Seq s) (x : V) {i} (hi : i < lh s) :
    znth (seqCons s x) i = znth s i :=
  (h.seqCons x).znth_eq_of_mem (Seq.subset_seqCons s x (h.znth hi))

lemma znth_ibumpTable_succ {b n k : V} (hk : k < n + 1) :
    znth (ibumpTable b (n + 1)) k = znth (ibumpTable b n) k := by
  rw [ibumpTable_succ]
  exact znth_seqCons_of_lt (ibumpTable_seq b n) _ (by rw [ibumpTable_lh]; exact hk)

@[simp] lemma ibump_zero (b : V) : ibump b 0 = 0 := by
  simp only [ibump, ibumpTable_zero]
  exact (singleton_seq 0).znth_eq_of_mem ((mem_singleton_seq_iff 0 0).mpr rfl)

/-- **Table stability.** Every entry of the length-`(N+1)` table is the genuine `ibump` value. -/
lemma znth_ibumpTable_eq_ibump (b : V) : ∀ N, ∀ k ≤ N, znth (ibumpTable b N) k = ibump b k := by
  intro N
  induction N using ISigma1.sigma1_succ_induction
  · refine Definable.ball_le (by definability) ?_
    exact Definable.comp₂
      (DefinableFunction₂.comp (F := znth) (def_ibumpTable b 1) (DefinableFunction.var 0))
      (def_ibump b 0)
  case zero =>
    intro k hk
    rcases (nonpos_iff_eq_zero.mp hk) with rfl
    rfl
  case succ N ih =>
    intro k hk
    rcases eq_or_lt_of_le hk with rfl | hlt
    · rfl
    · rw [znth_ibumpTable_succ hlt]
      exact ih k (le_iff_lt_succ.mpr hlt)

/-! ### The `bump` recursion equation -/

/-- `x < b^x` for `2 ≤ b`: makes the top exponent of `n+1` land `≤ n`. -/
lemma self_lt_ipow {b : V} (hb : 2 ≤ b) (x : V) : x < ipow b x := by
  have hb0 : (0 : V) < b := lt_of_lt_of_le (by simp) hb
  induction x using ISigma1.sigma1_succ_induction
  · definability
  case zero => exact ipow_pos hb0 0
  case succ x ih =>
    rw [ipow_succ]
    calc x + 1 ≤ ipow b x := lt_iff_succ_le.mp ih
      _ < ipow b x + ipow b x := lt_add_of_pos_right _ (ipow_pos hb0 x)
      _ = ipow b x * 2 := (mul_two _).symm
      _ ≤ ipow b x * b := mul_le_mul_right hb _

lemma znth_seqCons_self {s : V} (h : Seq s) (x : V) : znth (seqCons s x) (lh s) = x :=
  (h.seqCons x).znth_eq_of_mem (lh_mem_seqCons s x)

/-- **The internal `bump` recursion** — `ibump` satisfies the peel recursion of `Defs.bump`:
`bump b (n+1) = (n+1)/b^e · (b+1)^(bump b e) + bump b r`, with `e = ilog b (n+1)`, `r = (n+1) mod b^e`.
This is the machine-checked statement that the table truly computes the hereditary base-change. -/
lemma ibump_succ {b : V} (hb : 2 ≤ b) (n : V) :
    ibump b (n + 1)
      = (n + 1) / ipow b (ilog b (n + 1)) * ipow (b + 1) (ibump b (ilog b (n + 1)))
        + ibump b ((n + 1) % ipow b (ilog b (n + 1))) := by
  have hb0 : (0 : V) < b := lt_of_lt_of_le (by simp) hb
  have hpos : (0 : V) < n + 1 := by simp
  have hpe : 0 < ipow b (ilog b (n + 1)) := ipow_pos hb0 _
  have hen : ilog b (n + 1) ≤ n :=
    le_iff_lt_succ.mpr (lt_of_lt_of_le (self_lt_ipow hb _) (ipow_ilog_le hb hpos))
  have hrn : (n + 1) % ipow b (ilog b (n + 1)) ≤ n :=
    le_iff_lt_succ.mpr (lt_of_lt_of_le (mod_lt _ hpe) (ipow_ilog_le hb hpos))
  have key : znth (ibumpTable b (n + 1)) (n + 1) = bumpNext b (n + 1) (ibumpTable b n) := by
    rw [ibumpTable_succ]
    have := znth_seqCons_self (ibumpTable_seq b n) (bumpNext b (n + 1) (ibumpTable b n))
    rwa [ibumpTable_lh] at this
  rw [ibump, key, bumpNext,
    znth_ibumpTable_eq_ibump b n (ilog b (n + 1)) hen,
    znth_ibumpTable_eq_ibump b n ((n + 1) % ipow b (ilog b (n + 1))) hrn]

/-- **The internal `bump` recursion at any positive argument** (general form of `ibump_succ`):
`ibump b n = n/b^e · (b+1)^(ibump b e) + ibump b (n mod b^e)` with `e = ilog b n`, for `0 < n`. The
workhorse equation behind the strong-induction internal `bump` lemmas (the `Δ₀`-numeral analogues of
`Domination`'s `ℕ` facts). -/
lemma ibump_pos {b : V} (hb : 2 ≤ b) {n : V} (hn : 0 < n) :
    ibump b n
      = n / ipow b (ilog b n) * ipow (b + 1) (ibump b (ilog b n))
        + ibump b (n % ipow b (ilog b n)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 :=
    ⟨n - 1, (sub_add_self_of_le (pos_iff_one_le.mp hn)).symm⟩
  exact ibump_succ hb m

/-- **`n ≤ ibump b n`** (internal analogue of `Domination.le_bump`). The hereditary base-change never
shrinks its argument: each digit-block grows (`b^e ≤ (b+1)^(ibump b e)`) and the remainder dominates
its own bump by the strong IH. Proved by `𝚺₁` order-induction on `n`, peeling via `ibump_pos`. -/
theorem le_ibump {b : V} (hb : 2 ≤ b) : ∀ n, n ≤ ibump b n := by
  have hb0 : (0 : V) < b := lt_of_lt_of_le (by simp) hb
  intro n
  induction n using ISigma1.sigma1_order_induction
  · exact Definable.comp₂ (DefinableFunction.var 0) (def_ibump b 0)
  case ind n ih =>
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · have hnpos : 0 < n := pos_iff_ne_zero.mpr hn
      set e := ilog b n with he
      have hpe : 0 < ipow b e := ipow_pos hb0 e
      have hen : e < n :=
        lt_of_lt_of_le (self_lt_ipow hb e) (ipow_ilog_le hb hnpos)
      have hrn : n % ipow b e < n :=
        lt_of_lt_of_le (mod_lt _ hpe) (ipow_ilog_le hb hnpos)
      rw [ibump_pos hb hnpos, ← he]
      -- leading block: b^e ≤ (b+1)^(ibump b e)
      have h1 : ipow b e ≤ ipow (b + 1) (ibump b e) :=
        le_trans (ipow_le_ipow_left (by simp) e) (ipow_le_ipow_right (by simp) (ih e hen))
      have h2 : n % ipow b e ≤ ibump b (n % ipow b e) := ih _ hrn
      have hdm : n / ipow b e * ipow b e + n % ipow b e = n := by
        rw [mul_comm]; exact div_add_mod n (ipow b e)
      calc n = n / ipow b e * ipow b e + n % ipow b e := hdm.symm
        _ ≤ n / ipow b e * ipow (b + 1) (ibump b e) + ibump b (n % ipow b e) := by
            gcongr
        _ = _ := rfl

/-- **Strict growth above the base** (internal analogue of `Domination.bump_gt`): for `b ≤ n`, one
hereditary base-change strictly increases the value, `n + 1 ≤ ibump b n`. The leading power `b^L`
(`L = ilog b n ≥ 1`) is sent to `(b+1)^(ibump b L) > b^L`, so the leading term alone already exceeds
`n`. Digit-direct (no ordinals), so it internalizes; the `ℕ` proof's ordinal route does not. -/
theorem ibump_gt {b : V} (hb : 2 ≤ b) {n : V} (hn : b ≤ n) : n + 1 ≤ ibump b n := by
  have hb0 : (0 : V) < b := lt_of_lt_of_le (by simp) hb
  have hnpos : (0 : V) < n := lt_of_lt_of_le hb0 hn
  set L := ilog b n with hL
  have hL1 : 1 ≤ L := ilog_pos hb hn
  have hbe_pos : 0 < ipow b L := ipow_pos hb0 L
  have hbe_le : ipow b L ≤ n := ipow_ilog_le hb hnpos
  have hq1 : 1 ≤ n / ipow b L := by
    rcases eq_or_ne (n / ipow b L) 0 with h0 | h0
    · exfalso
      have hlt := lt_mul_div n hbe_pos
      rw [h0] at hlt; simp at hlt
      exact absurd hlt (not_lt.mpr hbe_le)
    · exact pos_iff_one_le.mp (pos_iff_ne_zero.mpr h0)
  have hpow_lt : ipow b L < ipow (b + 1) L :=
    ipow_lt_ipow_left (by simp) (pos_iff_one_le.mpr hL1)
  have hpow_le : ipow (b + 1) L ≤ ipow (b + 1) (ibump b L) :=
    ipow_le_ipow_right (by simp) (le_ibump hb L)
  have hP : ipow b L + 1 ≤ ipow (b + 1) (ibump b L) :=
    lt_iff_succ_le.mp (lt_of_lt_of_le hpow_lt hpow_le)
  have hr_le : n % ipow b L ≤ ibump b (n % ipow b L) := le_ibump hb _
  have hbump := ibump_pos hb hnpos
  have hn_eq : n / ipow b L * ipow b L + n % ipow b L = n := by
    rw [mul_comm]; exact div_add_mod n (ipow b L)
  rw [← hL] at hbump
  set q := n / ipow b L with hq
  set BL := ipow b L with hBL
  set P := ipow (b + 1) (ibump b L) with hPdef
  have hmul : q * (BL + 1) ≤ q * P := by gcongr
  have hexp : q * (BL + 1) = q * BL + q := by rw [mul_add, mul_one]
  have hkey : q * BL + q ≤ q * P := hexp ▸ hmul
  rw [hbump]
  have hge : q * BL + q + n % BL ≤ q * P + ibump b (n % BL) := add_le_add hkey hr_le
  have heq : n + 1 ≤ q * BL + q + n % BL := by
    have e1 : q * BL + q + n % BL = q * BL + n % BL + q := add_right_comm _ _ _
    rw [e1, hn_eq]
    exact add_le_add (le_refl n) hq1
  exact le_trans heq hge

/-! ### Strict monotonicity of `ibump` (combined upper-bound + monotonicity induction)

The hereditary base-change is strictly monotone in its argument. As with `evalNat_reflect_combined`
(`InternalONote`), the value-bound `ibump b n < (b+1)^(ibump b (ilog b n) + 1)` and the strict
monotonicity are mutually recursive — increasing the leading coefficient dominates the whole tail iff
the tail is bounded by the leading power — so both are carried in one strong induction on the value.
Digit-direct (no ordinals), so it internalizes. (Port of the Aristotle `ibump_mono` blueprint into
clean `IΣ₁` arithmetic, replacing its `nlinarith`/`grind` with manual ordered-semiring steps.) -/

private def IBcombined (b w : V) : Prop :=
  (∀ n ≤ w, 0 < n → ibump b n < ipow (b + 1) (ibump b (ilog b n) + 1)) ∧
  (∀ n ≤ w, ∀ n' ≤ w, n < n' → ibump b n < ibump b n')

private theorem ibump_combined {b : V} (hb : 2 ≤ b) : ∀ w, IBcombined b w := by
  have hb0 : (0 : V) < b := lt_of_lt_of_le (by simp) hb
  have hb1 : (1 : V) ≤ b := le_trans (by simp) hb
  have hb0' : (0 : V) < b + 1 := lt_of_lt_of_le (by simp) (le_trans hb (by simp))
  have hb1' : (1 : V) ≤ b + 1 := le_trans hb1 (by simp)
  intro w
  induction w using ISigma1.sigma1_order_induction
  · unfold IBcombined; definability
  case ind w ih =>
    -- The upper-bound component, established once (used by MONO too).
    have hUB : ∀ n ≤ w, 0 < n → ibump b n < ipow (b + 1) (ibump b (ilog b n) + 1) := by
      intro n hnw hnpos
      have hDpos : 0 < ipow b (ilog b n) := ipow_pos hb0 _
      have hDle : ipow b (ilog b n) ≤ n := ipow_ilog_le hb hnpos
      have hq_lt : n / ipow b (ilog b n) < b := by
        apply div_lt_of_lt_mul
        have := lt_ipow_ilog_succ hb hnpos
        rwa [ipow_succ, mul_comm] at this
      have hr_lt : n % ipow b (ilog b n) < ipow b (ilog b n) := mod_lt _ hDpos
      have hr_w : n % ipow b (ilog b n) < w :=
        lt_of_lt_of_le (lt_of_lt_of_le hr_lt hDle) hnw
      -- tail block bound: ibump b (n % D) < (b+1)^(ibump b (ilog b n))
      have htail : ibump b (n % ipow b (ilog b n)) < ipow (b + 1) (ibump b (ilog b n)) := by
        rcases eq_or_ne (n % ipow b (ilog b n)) 0 with h0 | h0
        · rw [h0, ibump_zero]; exact ipow_pos hb0' _
        · have hr_pos : 0 < n % ipow b (ilog b n) := pos_iff_ne_zero.mpr h0
          have hlog_lt : ilog b (n % ipow b (ilog b n)) < ilog b n := by
            by_contra hc
            have h1 : ipow b (ilog b n) ≤ ipow b (ilog b (n % ipow b (ilog b n))) :=
              ipow_le_ipow_right hb1 (not_lt.mp hc)
            have h2 := ipow_ilog_le hb hr_pos
            exact absurd (lt_of_lt_of_le hr_lt (le_trans h1 h2)) (_root_.lt_irrefl _)
          have he_w : ilog b n < w := lt_of_lt_of_le (lt_of_lt_of_le (self_lt_ipow hb _) hDle) hnw
          have hlog_w : ilog b (n % ipow b (ilog b n)) < w := lt_trans hlog_lt he_w
          have hUBr := (ih _ hr_w).1 _ le_rfl hr_pos
          have hmono_exp : ibump b (ilog b (n % ipow b (ilog b n))) < ibump b (ilog b n) :=
            (ih _ (max_lt hlog_w he_w)).2 _ (le_max_left _ _) _ (le_max_right _ _) hlog_lt
          exact lt_of_lt_of_le hUBr (ipow_le_ipow_right hb1' (lt_iff_succ_le.mp hmono_exp))
      rw [ibump_pos hb hnpos]
      calc n / ipow b (ilog b n) * ipow (b + 1) (ibump b (ilog b n))
              + ibump b (n % ipow b (ilog b n))
          < n / ipow b (ilog b n) * ipow (b + 1) (ibump b (ilog b n))
              + ipow (b + 1) (ibump b (ilog b n)) := by gcongr
        _ = (n / ipow b (ilog b n) + 1) * ipow (b + 1) (ibump b (ilog b n)) := by
            rw [add_mul, one_mul]
        _ ≤ b * ipow (b + 1) (ibump b (ilog b n)) := by gcongr; exact lt_iff_succ_le.mp hq_lt
        _ < b * ipow (b + 1) (ibump b (ilog b n)) + ipow (b + 1) (ibump b (ilog b n)) :=
            lt_add_of_pos_right _ (ipow_pos hb0' _)
        _ = (b + 1) * ipow (b + 1) (ibump b (ilog b n)) := by rw [add_mul, one_mul]
        _ = ipow (b + 1) (ibump b (ilog b n) + 1) := by rw [ipow_succ, mul_comm]
    refine ⟨hUB, ?_⟩
    -- MONO component.
    intro n hnw n' hn'w hnn'
    rcases eq_or_ne n 0 with rfl | hn0
    · rw [ibump_zero]
      exact lt_of_lt_of_le hnn' (le_ibump hb n')
    · have hnpos : 0 < n := pos_iff_ne_zero.mpr hn0
      have hn'pos : 0 < n' := lt_trans hnpos hnn'
      have hee' : ilog b n ≤ ilog b n' := ilog_mono hb hnpos hnn'.le
      have hD'pos : 0 < ipow b (ilog b n') := ipow_pos hb0 _
      have hD'le : ipow b (ilog b n') ≤ n' := ipow_ilog_le hb hn'pos
      have he_w : ilog b n < w :=
        lt_of_lt_of_le (lt_of_lt_of_le (self_lt_ipow hb _) (ipow_ilog_le hb hnpos)) hnw
      have he'_w : ilog b n' < w :=
        lt_of_lt_of_le (lt_of_lt_of_le (self_lt_ipow hb _) hD'le) hn'w
      -- leading coefficient of n' is ≥ 1
      have hq'1 : 1 ≤ n' / ipow b (ilog b n') := by
        rcases eq_or_ne (n' / ipow b (ilog b n')) 0 with h0 | h0
        · exfalso
          have hdm := div_add_mod n' (ipow b (ilog b n'))
          rw [h0, mul_zero, zero_add] at hdm
          have hlt : n' % ipow b (ilog b n') < ipow b (ilog b n') := mod_lt n' hD'pos
          rw [hdm] at hlt
          exact absurd hD'le (not_le.mpr hlt)
        · exact pos_iff_one_le.mp (pos_iff_ne_zero.mpr h0)
      -- the leading term of `ibump b n'` dominates `(b+1)^(ibump b (ilog b n'))`
      have hlead : ipow (b + 1) (ibump b (ilog b n')) ≤ ibump b n' := by
        rw [ibump_pos hb hn'pos]
        calc ipow (b + 1) (ibump b (ilog b n'))
            = 1 * ipow (b + 1) (ibump b (ilog b n')) := (one_mul _).symm
          _ ≤ n' / ipow b (ilog b n') * ipow (b + 1) (ibump b (ilog b n')) := by gcongr
          _ ≤ n' / ipow b (ilog b n') * ipow (b + 1) (ibump b (ilog b n'))
              + ibump b (n' % ipow b (ilog b n')) := le_self_add
      rcases lt_or_eq_of_le hee' with hlt | heq
      · -- distinct leading exponents
        have hmono_exp : ibump b (ilog b n) < ibump b (ilog b n') :=
          (ih _ (max_lt he_w he'_w)).2 _ (le_max_left _ _) _ (le_max_right _ _) hlt
        calc ibump b n < ipow (b + 1) (ibump b (ilog b n) + 1) := hUB n hnw hnpos
          _ ≤ ipow (b + 1) (ibump b (ilog b n')) :=
              ipow_le_ipow_right hb1' (lt_iff_succ_le.mp hmono_exp)
          _ ≤ ibump b n' := hlead
      · -- equal leading exponents: compare leading coefficients, then remainders
        have hDpos : 0 < ipow b (ilog b n) := ipow_pos hb0 _
        have hr_lt : n % ipow b (ilog b n) < ipow b (ilog b n) := mod_lt _ hDpos
        have hr'_lt : n' % ipow b (ilog b n') < ipow b (ilog b n') := mod_lt _ hD'pos
        have hr_w : n % ipow b (ilog b n) < w :=
          lt_of_lt_of_le (lt_of_lt_of_le hr_lt (ipow_ilog_le hb hnpos)) hnw
        -- the tail block of `n` is bounded by the leading power (same UB argument as above)
        have htail_n : ibump b (n % ipow b (ilog b n)) < ipow (b + 1) (ibump b (ilog b n)) := by
          rcases eq_or_ne (n % ipow b (ilog b n)) 0 with h0 | h0
          · rw [h0, ibump_zero]; exact ipow_pos hb0' _
          · have hr_pos : 0 < n % ipow b (ilog b n) := pos_iff_ne_zero.mpr h0
            have hlog_lt : ilog b (n % ipow b (ilog b n)) < ilog b n := by
              by_contra hc
              have h1 : ipow b (ilog b n) ≤ ipow b (ilog b (n % ipow b (ilog b n))) :=
                ipow_le_ipow_right hb1 (not_lt.mp hc)
              exact absurd (lt_of_lt_of_le hr_lt (le_trans h1 (ipow_ilog_le hb hr_pos)))
                (_root_.lt_irrefl _)
            have hlog_w : ilog b (n % ipow b (ilog b n)) < w := lt_trans hlog_lt he_w
            have hmono_exp : ibump b (ilog b (n % ipow b (ilog b n))) < ibump b (ilog b n) :=
              (ih _ (max_lt hlog_w he_w)).2 _ (le_max_left _ _) _ (le_max_right _ _) hlog_lt
            exact lt_of_lt_of_le ((ih _ hr_w).1 _ le_rfl hr_pos)
              (ipow_le_ipow_right hb1' (lt_iff_succ_le.mp hmono_exp))
        rw [ibump_pos hb hnpos, ibump_pos hb hn'pos, heq]
        rw [heq] at htail_n
        rcases lt_trichotomy (n / ipow b (ilog b n')) (n' / ipow b (ilog b n')) with hq | hq | hq
        · -- leading coefficients separate
          calc n / ipow b (ilog b n') * ipow (b + 1) (ibump b (ilog b n'))
                  + ibump b (n % ipow b (ilog b n'))
              < n / ipow b (ilog b n') * ipow (b + 1) (ibump b (ilog b n'))
                  + ipow (b + 1) (ibump b (ilog b n')) := by gcongr
            _ = (n / ipow b (ilog b n') + 1) * ipow (b + 1) (ibump b (ilog b n')) := by
                rw [add_mul, one_mul]
            _ ≤ n' / ipow b (ilog b n') * ipow (b + 1) (ibump b (ilog b n')) := by
                gcongr; exact lt_iff_succ_le.mp hq
            _ ≤ n' / ipow b (ilog b n') * ipow (b + 1) (ibump b (ilog b n'))
                + ibump b (n' % ipow b (ilog b n')) := le_self_add
        · -- equal leading coefficients ⟹ remainders strictly ordered
          have hr'_w : n' % ipow b (ilog b n') < w :=
            lt_of_lt_of_le (lt_of_lt_of_le hr'_lt hD'le) hn'w
          have hrr : n % ipow b (ilog b n') < n' % ipow b (ilog b n') := by
            have hdn := div_add_mod n (ipow b (ilog b n'))
            have hdn' := div_add_mod n' (ipow b (ilog b n'))
            rw [← hq] at hdn'
            have hkey : ipow b (ilog b n') * (n / ipow b (ilog b n')) + n % ipow b (ilog b n')
                < ipow b (ilog b n') * (n / ipow b (ilog b n')) + n' % ipow b (ilog b n') := by
              rw [hdn, hdn']; exact hnn'
            exact lt_of_add_lt_add_left hkey
          have hmono_r : ibump b (n % ipow b (ilog b n')) < ibump b (n' % ipow b (ilog b n')) :=
            (ih _ hr'_w).2 _ (le_of_lt hrr) _ le_rfl hrr
          rw [hq]; gcongr
        · -- n'/D < n/D contradicts n < n'
          refine absurd ?_ (lt_asymm hnn')
          calc n' = ipow b (ilog b n') * (n' / ipow b (ilog b n')) + n' % ipow b (ilog b n') :=
                (div_add_mod n' (ipow b (ilog b n'))).symm
            _ < ipow b (ilog b n') * (n' / ipow b (ilog b n')) + ipow b (ilog b n') := by gcongr
            _ = ipow b (ilog b n') * (n' / ipow b (ilog b n') + 1) := by rw [mul_add, mul_one]
            _ ≤ ipow b (ilog b n') * (n / ipow b (ilog b n')) := by
                gcongr; exact lt_iff_succ_le.mp hq
            _ ≤ ipow b (ilog b n') * (n / ipow b (ilog b n')) + n % ipow b (ilog b n') := le_self_add
            _ = n := div_add_mod n (ipow b (ilog b n'))

/-- **`ibump b` is strictly monotone** in its argument (`2 ≤ b`). -/
theorem ibump_strictMono {b : V} (hb : 2 ≤ b) {n n' : V} (h : n < n') :
    ibump b n < ibump b n' :=
  (ibump_combined hb (max n n')).2 n (le_max_left _ _) n' (le_max_right _ _) h

/-- **`ibump b` is monotone** in its argument (`2 ≤ b`) — the weak form the descent's `ineq6_step`
consumes: a larger Goodstein value bumps to a larger value. -/
theorem ibump_mono {b : V} (hb : 2 ≤ b) {n n' : V} (h : n ≤ n') :
    ibump b n ≤ ibump b n' := by
  rcases eq_or_lt_of_le h with rfl | h
  · exact le_rfl
  · exact le_of_lt (ibump_strictMono hb h)

end GoodsteinPA.InternalPow
