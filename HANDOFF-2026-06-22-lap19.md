# HANDOFF — 2026-06-22 (lap 19, F SEAM FULLY ASSEMBLED)

> **Branch** `plan` · HEAD `8d011e4` · build **green** (`lake build GoodsteinPA`, **1269 jobs**) ·
> headline `peano_not_proves_goodstein` = honest `sorry` (anti-fraud intact). Working tree clean.
> Deliverable: **girder F (the arithmetization seam) is FULLY ASSEMBLED** —
> `SeamDefinability.seam : EpsilonOrder.Seam` is built; `#print axioms seam =
> [propext, choice, Quot.sound, rePred_ltPull_natCode]` (ONE disclosed axiom). Both the dominant-risk
> order-type half AND the definability half are discharged this lap.

## ✅ Lap-19 headline deliverable — F SEAM ASSEMBLED (`src/GoodsteinPA/SeamDefinability.lean`)
- `codeOfREPred₂` + `codeOfREPred₂_spec` — binary `ℒₒᵣ` representability (port of Foundation's unary
  `codeOfREPred`), axiom-clean.
- `precφ := codeOfREPred₂ (natCode order)` + `precφ_spec : ℕ ⊧/![m,n] precφ ↔ natCode m < natCode n`.
- `seam : EpsilonOrder.Seam` — `φ := emb precφ`, `hφ` via `eval_emb`+`precφ_spec`, `ge :=
  epsilon0_le_orderType_natCode`; `hprec`/`hprecXPos` from `EpsilonOrder` (lap 18).
- **ONE disclosed axiom** `rePred_ltPull_natCode` (CNF order is r.e.) = the **F-φ discharge target**:
  true (decidable `NONote.cmp` + computable `natCode`), gap = mathlib's missing `Computable`/`Primrec`
  for `ONote.cmp`. Bounded, Foundation-free, Aristotle-eligible. **`ON-LINE-REQUEST.md` filed.** NOT on
  any headline-clean claim (F not yet wired to headline).

## ✅ Lap-19 proof deliverable — `src/GoodsteinPA/Epsilon0Complete.lean` (NEW, all `#print axioms` clean)
The order-type half of girder **F** (`ε₀ ≤ orderType ≺`), end-to-end:
1. **`exists_NF_repr_eq`** `: ∀ o<ε₀, ∃ x:ONote, x.NF ∧ x.repr=o` — ε₀-completeness of CNF notations
   (the surjectivity mathlib LACKS). CNF recursion via `WellFoundedLT.induction`; crux `log_omega0_lt_self`
   (`log ω o < o` for `o<ε₀`, = no `ω^·` fixed point below ε₀).
2. **`repr_lt_epsilon0`** (NF ⟹ `repr<ε₀`) + **`range_NONote_repr`** (`= Iio ε₀`).
3. **`rk_ltPull_eq_repr`** (= seam-advice `note_rank_eq_repr`) + **`epsilon0_le_orderType_ltPull (e : ℕ≃NONote)`**
   `: ε₀ ≤ orderType (ltPull e)` (= the `Seam.ge` field, for ANY coding `e`).
4. **`encodeONote`/`decodeONote`** (COMPUTABLE structural `Encodable ONote`) + `Infinite`/`Denumerable NONote`
   ⟹ **`natCode : ℕ ≃ NONote`** + **`epsilon0_le_orderType_natCode`** (concrete, hypothesis-free `Seam.ge`).

**Two non-obvious points (carry forward):**
- Proved `ε₀ ≤ orderType` by **naming `orderType`/`rk` itself as some `repr (e n₀)` via surjectivity** —
  dodges the `NONote ≃o Iio ε₀` iso (which bumps universes: `Iio ε₀ : Type 1` ⟹ `Ordinal.{1}` ≠ the
  project's `Ordinal.{0}` `orderType`). Stay in ℕ.
- The coding MUST be **computable** (concurrent-session footgun): `ofCountable`/`Countable.toEncodable` use
  choice and would pass `Seam.ge` but silently wall Worker B (`codeOfREPred₂` needs `REPred (ltPull natCode)`).
  Verified `#eval (natCode 5)` and `ONote.cmp (natCode 3).1 (natCode 7).1` both compute.

## 🎯 Open obligations (priority order)
1. **Discharge `rePred_ltPull_natCode`** (`SeamDefinability.lean`) ⟹ F entirely axiom-clean. Needs
   computable `ONote.cmp` (`Computable₂`/`Primrec`). Plan: `Primcodable NONote` is free
   (`Primcodable.ofDenumerable`); `Computable natCode = Computable.ofNat NONote` (verified rfl); then
   `Computable (fun q : NONote×NONote => decide (q.1 < q.2))` via relating `NONote.cmp`→`ONote.cmp` to a
   `Primrec`/`Nat.rec` form (the recursion-framework lemma mathlib lacks). `ON-LINE-REQUEST.md` filed.
   Aristotle-eligible (pure mathlib/computability, ZERO Foundation dep).
2. **C₂ glue `hax_paLX`** X-induction case (`EmbeddingX.lean:705`) — closes **Thm 5.6 (`PA ⊬ TI(ε₀)`)**
   axiom-clean modulo E+F. Recipe inlined (steps 1-7), all 4 helpers proven; friction = Foundation-DSL
   Rew-pushing through `succInd`/`univCl`/`fixitr`. ALL-OR-NOTHING (can't partial-commit a sorry) ⟹ extract
   step-4 `rew_succInd : g ▹ succInd ψ = succInd (g.q ▹ ψ)` as a standalone helper first.
3. **E** Goodstein⟹TI_≺(`natCode` order) in PA — the last unstarted wall. Per seam-advice Reviewer-2 §3:
   ONE order (`natCode`'s CNF order) for both F and E; E uses `Domination.toONote` as a descent MAP into it
   (E's order need not be type ε₀, only a PA-provable `≺`-decreasing descent). Needs `papers/` reading.

## ⚠️ Locked / notes
- **LOCKED untouched:** `Defs.lean`, `Bridge.lean` RHS, `goodsteinTerminates`, headline `sorry`.
- **src/ sorries (3):** `Statement.lean:22` (headline, locked), `Reduction.lean:50` (Route-A, off-path),
  `EmbeddingX.lean:705` (`hax_paLX` glue). `Epsilon0Complete.lean` + `EpsilonOrder.lean` are sorry-free.
- Coordination: `ARITHMETIZATION-SEAM-ADVICE-2026-06-22.md` comment log is current (Codex + me).

## 📊 Lap estimate to headline (updated)
F-φ ~1-2 · C₂ glue ~1 · Thm 5.6 wiring ~0.5 · **E ~2-4 (now the dominant remaining risk)** · G ~1.
**Total ~5-9 laps.** Everything from D back + F's order-type half is axiom-clean machine-checked.
