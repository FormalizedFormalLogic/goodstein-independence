import GoodsteinPA.OperatorZef2

/-!
# RETIRED (Series-3 D-3): the `readoffD_aux` falsity-invariant route to rung D

Moved verbatim from `src/GoodsteinPA/OperatorZef2.lean` when D-3 landed `readoff_delta0_Zef2`
(R-4′ conclusion `∃ n ≤ ewIter f α 0`) via the singleton-vacuity route
(`zef2_rank0_singleton_ex_underivable` — the spine-head invariant shows `Zef2` without E–W's
(Ax2) cannot derive ANY `{∃⁰ φ}` at rank 0, so the ratified statement holds vacuously; this
was exactly lap-195's flagged "residue vacuous" alternative, globalized).

The falsity-invariant scaffold below is the ABANDONED structural route: its `allω` trapped
case (`readoffD_trapped`, the disclosed `sorry` here) is NOT closable even at the amended
`ewIter f α 0` bound — the false-branch index `k₀` is semantic (least false matrix instance),
uncontrolled by any gate, so `ewIter (rel1 f k₀) (β k₀) 0 ≰ ewIter f α 0` for adversarially
large `k₀` (e.g. matrix `x < N`, `Γ₀ ∋ ∼(φ/[nm N])`, slot `·+1`, `α = 2`, `N` large: the
aux-invariant-at-`ewIter`-bound is FALSE, though from a singleton root such Γ₀ never arises —
which is the vacuity observation).  Kept compiling as frozen evidence; the `sorry` is
designated-retired, NOT open work.
-/

namespace GoodsteinPA.OperatorZeh

open LO LO.FirstOrder ONote Ordinal
open GoodsteinPA.FastGrowing
open GoodsteinPA.OperatorZinfty

/-- **RESIDUE (trapped contraction) — the SOLE open sub-case of `readoffD_aux`.**

At an `allω` node deriving `insert (∀⁰ χ) Γ₀`, the branches run at the *relativized* slot
`rel1 f n` (`rel1 f n 0 = f n`, NOT `f 0`).  When the shared context `Γ₀` still carries the goal
existential `∃⁰ φ` (kept by a *contraction* on a lower `exI`), the branch's inductive witness bound
is `≤ f n`, so `readoffD_aux`'s outer bound `≤ f 0` is NOT inductively maintained here.

**NARROWED (lap-195) — the residue is now the non-monotone-matrix case only.**  The KEY structural
fact `rel1 f 0 = f` (because `max 0 x = x`) means **branch `0` runs at the un-relativized slot `f`**:
if `χ/[nm 0]` is FALSE, `readoffD_aux` recurses into branch 0 and closes at the SHARP bound
`rel1 f 0 0 = f 0` with NO residue (proven in `readoffD_aux`'s `allω`/trapped case).  So the trap
survives ONLY when `χ/[nm 0]` is TRUE while `∀⁰ χ` is false — i.e. the Δ₀ matrix `χ` is
*non-monotone* in its numeral instances, all false branches sitting at index `≥ 1`.  This is exactly
the case E–W's (Ax2) closes semantically; the added hypothesis `h0 : atomTrue (χ/[nm 0])` records
the narrowing.  (A sufficient condition making the residue never fire: whenever `∀⁰ χ` is false its
`0`-instance `χ/[nm 0]` is already false — e.g. `χ` a bounded-`∀` guard `y < t → ψ` with `ψ`
downward-closed in `y` — since then the branch-0 recursion discharges it at bound `f 0`.)

**Decisive diagnosis (lap-194c, grounded in the E–W Lemma 31 PROOF).**  The trap is a
formulation artifact: it comes from `readoffD_aux` STRUCTURALLY descending the Δ₀ matrix via `allω`
(which relativizes `f → rel1 f n`).  **E–W's Witnessing Lemma 31 AVOIDS this.**  In E–W Def 23:
  • `∃` is `⋁`-type — witnessed by their `(⋁)` rule with the operator `f` **UNCHANGED** and the
    witness norm `N(t) ≤ f(0)`; `∀` is `⋀`-type — decomposed by `(⋀)` with the operator RELATIVIZED
    `f → f[N(ι)]`.  (Exactly our `exI` keeps `f`, our `allω` = `rel1 f ·`.)
  • They also have **(Ax2): a true closed PA-literal `Γ ∩ TRUE₀ ≠ ∅` closes the sequent** — which
    THIS `Zef2` LACKS (only `axL` = a complementary literal *pair*).
  Lemma 31's induction extracts the l TOP-LEVEL `∃`-witnesses via `(⋁)` at operator `f` (all bounds
  `≤ f(0)`), and verifies the Δ₀ matrix instances `B_j(t)` **SEMANTICALLY** — its proof says "`B(t)`
  must be true (in ℕ)" via soundness, and NEVER structurally re-derives the matrix.  So the `(⋀)`/
  `allω` relativization is confined to *deriving* Δ₀ instances and never touches the top-`∃` witness
  budget.  Our structural descent breaks exactly this separation.

**Fix (calculus-gated) = mirror E–W.**  Prove the read-off by extracting the top-`∃⁰ φ` witness via
`exI` at slot `f` (`n ≤ f 0`) and verifying `φ/[nm n]` truth via `sound0` (semantic), WITHOUT
structurally recursing into `allω`-decomposed matrix branches — and add the E–W **(Ax2)** true-literal
rule to `Zef2` so true Δ₀ leaves close without forcing the trapped `∃⁰ φ`.  Adding (Ax2) is the
**architect-gated Ax2-adequacy** already flagged for rung E (`Zekd` has `trueRel`/`trueNrel`, `Zef2`
has none, E–W Def 23 has (Ax2)) — so this residue and rung E share ONE calculus-faithfulness
decision.  Open pure-proof alternative: show trap-derivations do not EXIST in `Zef2`-without-(Ax2)
(fewer leaves ⇒ the false branch may be underivable), which would make the residue vacuous.

The non-trapped (`∃⁰ φ ∉ Γ₀`) sub-case is closed inside `readoffD_aux` via `sound0`; `exI`/`wk`/
`weak`/`axL`/`cut` are fully proven.  See `PENDING_WORK.md` (lap-194c) + the ledger. -/
theorem readoffD_trapped_RETIRED {φ χ : SyntacticSemiformula ℒₒᵣ 1}
    {e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {Γ₀ : Seq} {β : ℕ → ONote}
    (hbranch : ∀ n, Zef2 (β n) e (adjoin H n) (rel1 f n) 0 (insert (χ/[nm n]) Γ₀))
    (htrap : (∃⁰ φ) ∈ Γ₀)
    (hfalse : ¬ atomTrue (∀⁰ χ))
    (hΓ₀ : ∀ ψ ∈ Γ₀, ψ = (∃⁰ φ) ∨ ¬ atomTrue ψ)
    (h0 : atomTrue (χ/[nm 0])) :
    ∃ n ≤ f 0, atomTrue (φ/[nm n]) := by
  sorry

/-- **`readoffD_aux` — the strengthened read-off invariant** (falsity form).  From a rank-0 `Zef2`
derivation of any `Γ` all of whose members are either the goal existential `∃⁰ φ` or standard-model
FALSE, extract the bounded witness `n ≤ f 0` with `φ/[nm n]` true.  Proven by induction on the
derivation for all rules; the `allω` node splits on whether `∃⁰ φ` is trapped in the shared context
(the `readoffD_trapped` residue) vs. absent (closed by `sound0`).  `exI`/`wk`/`weak` keep the slot
`f`; `axL`/`cut` are vacuous at rank 0. -/
theorem readoffD_aux_RETIRED {φ : SyntacticSemiformula ℒₒᵣ 1} :
    ∀ {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Seq},
      Zef2 α e H f c Γ → c = 0 → (∀ ψ ∈ Γ, ψ = (∃⁰ φ) ∨ ¬ atomTrue ψ) →
      ∃ n ≤ f 0, atomTrue (φ/[nm n]) := by
  intro α e H f c Γ dd
  induction dd with
  | @axL α e H f c Γ ar hαN r v hp hn =>
      intro _ hyp
      -- one of the complementary literals is true, contradicting `hyp` (literals ≠ `∃⁰ φ`)
      by_cases htrue : atomTrue (Semiformula.rel r v)
      · rcases hyp _ hp with h | h
        · exact absurd h (by simp [ExsQuantifier.exs])
        · exact absurd htrue h
      · have hntrue : atomTrue (Semiformula.nrel r v) := by
          simpa [atomTrue, Semiformula.eval_nrel, Semiformula.eval_rel] using htrue
        rcases hyp _ hn with h | h
        · exact absurd h (by simp [ExsQuantifier.exs])
        · exact absurd hntrue h
  | @wk α e H f c Δ Γ hαN hsub _ ih =>
      intro hc hyp
      exact ih hc (fun ψ hψ => hyp ψ (hsub hψ))
  | @weak α β e H f c Δ Γ hαN hβ hβNF hαNF hβH hsub _ ih =>
      intro hc hyp
      exact ih hc (fun ψ hψ => hyp ψ (hsub hψ))
  | @allω α e H f c Γ₀ hαN χ β hβ hβNF hαNF hβH dd ih =>
      intro hc hyp
      -- `∀⁰ χ ≠ ∃⁰ φ`, so by `hyp` it is FALSE ⇒ some branch instance `χ/[nm k₀]` is false
      have hχfalse : ¬ atomTrue (∀⁰ χ) := by
        rcases hyp (∀⁰ χ) (Finset.mem_insert_self _ _) with h | h
        · exact absurd h (by simp [UnivQuantifier.all, ExsQuantifier.exs])
        · exact h
      obtain ⟨k₀, hk₀⟩ : ∃ k, ¬ atomTrue (χ/[nm k]) := by
        by_contra hcon
        push_neg at hcon
        exact hχfalse ((atomTrue_all_iff χ).mpr hcon)
      -- the shared context `Γ₀` inherits the falsity/`∃⁰ φ` dichotomy
      have hΓ₀ : ∀ ψ ∈ Γ₀, ψ = (∃⁰ φ) ∨ ¬ atomTrue ψ :=
        fun ψ hψ => hyp ψ (Finset.mem_insert_of_mem hψ)
      by_cases htrap : (∃⁰ φ) ∈ Γ₀
      · -- TRAPPED contraction.  KEY: branch `0` runs at slot `rel1 f 0 = f` (since `max 0 x = x`),
        -- so if `χ/[nm 0]` is FALSE the recursion into branch 0 closes at the SHARP bound `f 0`
        -- (no relativization).  Only when `χ/[nm 0]` is TRUE (non-monotone matrix, all false
        -- branches at index ≥ 1) does the genuine slot-growth residue remain.
        subst hc
        by_cases h0 : atomTrue (χ/[nm 0])
        · exact readoffD_trapped_RETIRED dd htrap hχfalse hΓ₀ h0
        · -- branch 0 at slot `rel1 f 0 = f`: recurse, landing the bound at `rel1 f 0 0 = f 0`
          have hyp0 : ∀ ψ ∈ insert (χ/[nm 0]) Γ₀, ψ = (∃⁰ φ) ∨ ¬ atomTrue ψ := by
            intro ψ hψ
            rcases Finset.mem_insert.mp hψ with rfl | hψΓ
            · exact Or.inr h0
            · exact hΓ₀ ψ hψΓ
          have hb0 := ih 0 rfl hyp0
          rwa [show (rel1 f 0) 0 = f 0 from by simp [rel1]] at hb0
      · -- NOT trapped: branch `k₀` has all members false ⇒ `sound0` contradiction
        exfalso
        have hbranch := dd k₀
        obtain ⟨ψ, hψ, htrueψ⟩ := sound0 hbranch hc
        rcases Finset.mem_insert.mp hψ with rfl | hψΓ
        · exact hk₀ htrueψ
        · rcases hΓ₀ ψ hψΓ with rfl | hfψ
          · exact htrap hψΓ
          · exact hfψ htrueψ
  | @exI α β e H f c Γ₀ hαN χ n hβ hβNF hαNF hβH hbound dd ih =>
      intro hc hyp
      by_cases hχφ : χ = φ
      · subst hχφ
        -- `subst` eliminated `φ` (replacing it by `χ`); the goal now reads off `χ`
        -- the introduced witness `n ≤ f 0`; either `χ/[nm n]` is already true, or recurse
        by_cases hinst : atomTrue (χ/[nm n])
        · exact ⟨n, hbound, hinst⟩
        · refine ih hc ?_
          intro ψ hψ
          rcases Finset.mem_insert.mp hψ with rfl | hψΓ
          · exact Or.inr hinst
          · exact hyp ψ (Finset.mem_insert_of_mem hψΓ)
      · -- `∃⁰ χ ≠ ∃⁰ φ` ⇒ `∃⁰ χ` false ⇒ `χ/[nm n]` false; recurse at slot `f`
        have hexχfalse : ¬ atomTrue (∃⁰ χ) := by
          rcases hyp (∃⁰ χ) (Finset.mem_insert_self _ _) with h | h
          · exact absurd ((Semiformula.exs_inj _ _).mp h) hχφ
          · exact h
        have hχn : ¬ atomTrue (χ/[nm n]) := fun ht =>
          hexχfalse ((atomTrue_ex_iff χ).mpr ⟨n, ht⟩)
        refine ih hc ?_
        intro ψ hψ
        rcases Finset.mem_insert.mp hψ with rfl | hψΓ
        · exact Or.inr hχn
        · exact hyp ψ (Finset.mem_insert_of_mem hψΓ)
  | @cut α βφ βψ e H f c Γ hαN φ' hcompl hcutRead _ _ _ _ _ _ _ _ _ _ _ =>
      intro hc _; subst hc
      exact absurd hcompl (by omega)

end GoodsteinPA.OperatorZeh
