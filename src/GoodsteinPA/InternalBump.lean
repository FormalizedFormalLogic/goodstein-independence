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

end GoodsteinPA.InternalPow
