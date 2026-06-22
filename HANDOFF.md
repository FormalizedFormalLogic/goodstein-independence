# HANDOFF — 2026-06-22 (lap 20, C₂ GLUE DISCHARGED — Thm 5.6 axiom-clean modulo E+F)

> **Branch** `plan` · HEAD `24144a3` · build **green** (`lake build GoodsteinPA`, **1269 jobs**) ·
> headline `peano_not_proves_goodstein` = honest `sorry` (anti-fraud intact). Working tree clean.
> Deliverable: **C₂ glue `hax_paLX` X-induction case is DISCHARGED** (`src/GoodsteinPA/EmbeddingX.lean`).
> `#print axioms hax_paLX = #print axioms embedC_LX = [propext, choice, Quot.sound]`. ⟹ the
> **entire Buchholz §5 girder from D back through C₂ is now machine-checked + axiom-clean**, so
> **Thm 5.6 (`PA ⊬ TI(ε₀)`) is axiom-clean modulo the two remaining campaign walls E + F-φ**.

## ✅ Lap-20 deliverable — C₂ glue `hax_paLX` (`src/GoodsteinPA/EmbeddingX.lean`)
The X-induction case (was the lone open `sorry` below the headline, besides off-path Route-A) is closed:
- **`subst1_comp_bShift`** : `(Rew.subst ![t]).comp Rew.bShift = Rew.bShift` (degree-1 subst fixes a bShifted term).
- **`rew_subst1_comm_q`** : `g.q ▹ (φ/[t]) = (g.q ▹ φ)/[t]` for `g.q`-fixed `t` (the under-one-binder
  analogue of the file's `rew_subst_term`).
- **`rew_succInd`** : `g ▹ succInd ψ = succInd (g.q ▹ ψ)` (naturality of `succInd` under closed rewriting).
- **assembly**: `asgX e ▹ ↑(univCl (succInd ψ))` = `∀⁰* (fixitr ▹ succInd ψ)` (via Foundation's
  `coe_univCl_eq_univCl'` + `rew_univCl'`); `PXFc_allClosure` strips `∀⁰*` to per-`v` numeral instances;
  each reduces (`← comp_app` + `rew_succInd`) to `succInd ψ_v` (`ψ_v := g_v.q ▹ ψ`, `g_v := subst(nm∘v)∘fixitr`);
  `succInd_nnf` + `PXFc.orI`×2 break it into `metaInduction_cong`'s `{∼ψ_v(0), ∃(∼step_v), ∀ψ_v}` shape.
  `succT_v n := Rew.subst ![nm n] ‘#0+1’` (value `n+1`; `hsval` via `Structure.One/Add` `haveI`s + `congr 1`;
  `hstep` via `Rew.subst_comp_subst`). Complexity bridged by `complexity_rew` (`ψ_v.complexity = ψ.complexity`).

## 🎯 Open obligations (priority order) — TWO campaign walls left + the F-φ Aristotle job
1. **E** — `PA ⊢ Goodstein → PA ⊢ TI_≺(natCode order)` (the bridge). **The dominant remaining wall, now
   the top priority** (C₂ is done). Per seam-advice Reviewer-2 §3: ONE order (`natCode`'s CNF order) for
   both F and E; E uses `Domination.toONote` as a descent MAP into it (E's order need not be type ε₀, only
   a PA-provable strictly-`≺`-decreasing descent). **Needs `papers/` reading** (Cichoń/Rathjen/Agboola —
   Goodstein↔ε₀-descent). Not yet started; map the wall, state it in Lean, formalize the first prerequisite.
2. **F-φ** `rePred_ltPull_natCode` (`SeamDefinability.lean`, 1 disclosed axiom) ⟹ F entirely axiom-clean.
   **SUBMITTED TO ARISTOTLE lap 20** (UUID `16c9fc79-ae8b-4b04-8b83-2e8e9e5f38db`, status RUNNING; project
   `/tmp/aris_onotecmp/ONoteComp.lean` = self-contained mathlib-only port: structural `Encodable ONote` +
   `Denumerable NONote` + `natCode`, goal `REPred (natCode · < natCode ·)`). On return: VERIFY in our kernel
   + `#print axioms`, then port to discharge the axiom. Crux = `Primcodable ONote` from the STRUCTURAL
   encoding (not `ofDenumerable`) + `Primrec₂ ONote.cmp`. Foundation-free, bounded.
3. **G / assembly** — once Thm 5.6 + E + F land: `PA ⊢ Goodstein ⟹ (E) PA ⊢ TI_≺ ⟹ (Thm 5.6) False`,
   discharge headline. Only if `#print axioms peano_not_proves_goodstein` is clean.

## ⚠️ Locked / notes
- **LOCKED untouched:** `Defs.lean`, `Bridge.lean` RHS, `goodsteinTerminates`, headline `sorry`.
- **src/ sorries (2):** `Statement.lean:22` (headline, locked, designated open target), `Reduction.lean:52`
  (Route-A, off-path). EmbeddingX/Epsilon0Complete/EpsilonOrder are all sorry-free.
- M1 (`goodsteinTerminates_re`) verified axiom-clean this lap (`[propext, choice, Quot.sound]`).

## 📊 Lap estimate to headline (updated)
**E ~2-4 (the dominant remaining risk)** · F-φ ~0-1 (Aristotle in flight) · G assembly ~1. Everything from
D back + C₂ (Thm 5.6) + F's order-type half is axiom-clean machine-checked. **Total ~3-6 laps.**
