# DESCENT-PLAN — the E wall (`Thm56.DescentE`), grounded + API-verified (lap 23, 2026-06-23)

Companion to `PENDING_WORK.md`. This lap I read **Rathjen 2014 "Goodstein revisited" §2–3 + Appendix**
end-to-end (`papers/rathjen-2014-goodsteins-theorem-revisited.pdf`) and **located/probed the exact
Foundation bricks** for the proof-translation half of E. This file is the executable map.

```
DescentE := 𝗣𝗔 ⊢ ↑goodsteinSentence → Nonempty (Derivation2 paLX {TI prec})
```

Given `peano_not_proves_TI : IsEmpty (Derivation2 paLX {TI prec})` (already axiom-clean modulo F-φ),
`DescentE` closes the headline by contradiction (`peano_not_proves_goodstein_of_descent`, proved).
`goodsteinSentence` is the **special** Goodstein sequence (`goodsteinSeq`, shift-function base-bumps),
so E is the Kirby–Paris sharp form, which needs Rathjen §3 ("slowing down"), not just §2.

---

## 1. The math (Rathjen, mapped to repo defs)

Rathjen's reduction `special-Goodstein-termination ⟹ PRWO(ε₀)`, all inside PA (Cor 3.7):

| Rathjen | statement | repo status |
|---|---|---|
| `T^b_ω(n)` | base-`b` rep → CNF ordinal | **have** `Domination.toOrdinal b n` / `toONote b n`, `repr_toONote` |
| `T̂^b_ω(α)` | CNF ordinal → base-`b` integer (replace ω by b) | **have** `Domination.evalNat (b-1)` (`evalNat b o` reads CNF at ω↦b+1) |
| Lemma 2.2/2.3 | `α<β ⇔ T̂^b_ω(α)<T̂^b_ω(β)` when `C(α),C(β)<b` | **PARTIAL** — `toOrdinal_mono_and_bound` is the `T` half; the **`evalNat` (T̂) order-monotonicity under a coefficient bound is the missing brick** (needs a `C`/max-coefficient notion on `ONote`) |
| eq. (4) / Thm 2.5 | special Goodstein ordinal strictly decreases | **have** `Domination.seqOrd_step` (= Rathjen eq. 4), `goodstein_terminates` |
| Lemma 3.2 (Grzegorczyk domination) | every primrec `h` is `≤ f_n(max 2 ⃗x)` | **mathlib** `Computability/Ackermann.lean : exists_lt_ack_of_nat_primrec` (`∃ m, ∀ n, f n < ack m n`) — ack ≈ Grzegorczyk fₙ, interchangeable for domination |
| Lemma 4.1 | properties of fₗ-iteration | subsumed by mathlib `ack` monotonicity lemmas (`ack_strictMono_*`, `ack_le_ack`, …) |
| Lemma 3.3 / Cor 3.4 | make a primrec descending ε₀-seq **slow** (`|αᵢ| ≤ K·(i+1)`) | **TODO** — ordinal construction `g : ℕ²→ω^ω`; uses Lemma 3.2 |
| Thm 3.5 | slow ⟹ a primrec seq with `C(βᵣ) ≤ r+1` | **TODO** — explicit `βⱼ` construction |
| Lemma 3.6 | `C(βₙ)≤n+1` descending seq ⟹ the special Goodstein seq at `T̂²_ω(β₀)` never terminates | **TODO** — this is the contrapositive of the repo's `seqOrd_step` backbone via `evalNat`; inequality (6) `mₖ ≥ T̂^{k+2}_ω(βₖ)` |

**The X-essential subtlety (why E ≠ just lMap).** `TI prec = Prog prec 🡒 ∀⁰ Xat #0` mentions the
**set variable `X`** (`Boundedness.Xat`, the `Xsym` relation), which is **not** in `ℒₒᵣ`, hence **not in
the image of `Semiformula.lMap (ORing.embedding LX)`**. So no PA-sentence's lMap equals `TI prec`; the
derivation must genuinely *use* the X-induction axioms of `paLX`. Correct logic:

- `PRWO(ε₀)` in *schema* form ("no formula-definable ≺-descending sequence") **is** the `TI(≺)` schema.
- The instance of that schema for the LX-formula `X` (the free predicate) is exactly `paLX ⊢ TI prec`:
  from `Prog(X)` and a putative `¬X a`, progressivity gives `∃ b≺a, ¬X b`; the least such `b`
  (least-number principle, an `X`-formula instance available in `paLX = lMap 𝗣𝗔⁻ + InductionScheme LX univ`)
  defines an `X`-definable infinite ≺-descent, contradicting PRWO. So the real content of "PRWO ⟹ TI(prec)"
  is one application of the **LX least-number / induction scheme to an `X`-formula** — `paLX` has it.

So **E factors as** `E-core ∘ E-lift`:

```
𝗣𝗔 ⊢ goodsteinSentence
  ──[E-core, §3 inside PA]──▶  𝗣𝗔 ⊢ ⌜PRWO(ε₀)⌝            (X-free, ℒₒᵣ schema)
  ──[E-lift, proof translation + X-induction instance]──▶  Derivation2 paLX {TI prec}
```

### ⚠️ CORRECTION (lap 24) — the back-end is subtler than "one X-instance"; `Goodstein ⟹ PRWO` is SHARED

Grounding the above against Rathjen §2 (Thm 2.6/2.8, Cor 2.7/3.7) and Buchholz revealed two things the
first sketch glossed:

1. **Rathjen's `PRWO(ε₀)` is the *primitive-recursive* well-ordering statement** ("no descending **primrec**
   ε₀-sequence", Thm 2.8 / Cor 2.7), and his §3 slow-down is explicitly primrec (Lemma 3.2 = Grzegorczyk/
   `ack`). His actual headline route is **Route A**: `Goodstein ⟹ PRWO(ε₀)` (§3) + `PRWO ⟹ Con(PA)`
   (Gentzen, Thm 2.8(i)) + Gödel II. He does **not** use Buchholz's `TI_≺(X)`.

2. **`PRWO(ε₀) ⟹ paLX ⊢ TI prec` is NOT "one X-instance".** `TI prec` carries the **free** predicate `X`;
   a counterexample to it yields an `X`-*definable* descending sequence, which is **not primrec**, so
   primrec-`PRWO` cannot refute it. The honest Route-B bridge must carry out Rathjen §3 **inside paLX with
   the free-X descent** (define the descent from `¬X` via the LX least-number/induction scheme; slow it
   down; run inequality (6); contradict the *lifted, X-free* `goodsteinSentence` instantiated at the
   X-definable seed `m₀ = T̂²_ω(β₀)`). I.e. E-core(b) for Route B is an *integrated* paLX derivation, not
   "PA proves PRWO, then a one-line lift". (E-lift is still used — but only to import the X-free Goodstein
   hypothesis into paLX, `σ = goodsteinSentence`.)

**The de-risking consequence (route-independent focus).** The hard mathematical content —
**`Goodstein ⟹ PRWO(ε₀)` = Rathjen §3 (slow-down + inequality (6))** — is needed by **both** back-ends and
is therefore **never wasted**. So:

> **Plan:** focus E-core on the **shared** `Goodstein ⟹ PRWO(ε₀)` (§3); inequality (6)'s step is done
> (`Dom.ineq6_step`, lap 24). **Defer the back-end choice** — Route A (`Reduction.goodstein_implies_consistency`
> via `PRWO ⟹ Con(PA)` + Gödel II; costs the 🟡 `PA_delta1Definable` axiom) vs Route B (the integrated
> paLX construction; axiom-clean but heavier) — until §3 is formalized. See `ON-LINE-REQUEST.md` (lap 24)
> for the literature question that pins which back-end is cheaper to land.

---

## 2. E-lift — proof translation (Foundation bricks VERIFIED this lap)

All present in `Foundation/FirstOrder/Basic/Calculus{,2}.lean`:

- `Derivation.lMap (Φ : L₁ →ᵥ L₂) : 𝓢₁ ⟹ Γ → 𝓢₁.lMap Φ ⟹ Γ.map (.lMap Φ)`  — derivation functoriality.
- `provable_def {T : Theory L} : T ⊢ σ ↔ (T : Schema L) ⊢ ↑σ` and `𝓢 ⊢ φ = Nonempty (𝓢 ⟹. φ)` (`⟹. φ = ⟹ [φ]`).
- `Derivation.toDerivation2 (𝓢) : 𝓢 ⟹ Γ → 𝓢 ⟹₂ Γ.toFinset` and `provable_iff_derivable2 : 𝓢 ⊢ φ ↔ 𝓢 ⊢!₂! φ`.

**X-free lift lemma (next concrete target, lands in `src/`):**
```
𝗣𝗔 ⊢ σ  →  Nonempty (Derivation2 paLX {Rew.emb ▹ Semiformula.lMap (ORing.embedding LX) σ})
```
chain: `provable_def` → extract `𝗣𝗔:Schema ⟹ [↑σ]` → `Derivation.lMap Φ` → weaken schema → `toDerivation2`.
The schema weakening needs **`(𝗣𝗔 : Schema ℒₒᵣ).lMap Φ ⊆ (paLX : Schema LX)`**, i.e. (since `+`=∪ and
`Theory.lMap`=image):
```
Theory.lMap Φ (InductionScheme ℒₒᵣ Set.univ) ⊆ InductionScheme LX Set.univ
```
which reduces (membership unfold, `Schemata.lean : InductionScheme = {univCl (succInd φ) | Γ φ}`) to two
commutation lemmas:
- `Semiformula.lMap Φ (univCl χ) = univCl (Semiformula.lMap Φ χ)`  (lMap ∘ univCl' ∘ toEmpty).
- `Semiformula.lMap Φ (succInd φ) = succInd (Semiformula.lMap Φ φ)`.

**Probed this lap:** `unfold succInd; simp [Semiformula.lMap_subst]` reduces the second to two *term*
equalities `Semiterm.lMap Φ (0) = 0` and `Semiterm.lMap Φ ‘(#0+1)’ = ‘(#0+1)’`. These hold for
`Φ = ORing.embedding LX` (it fixes `Zero/One/Add/Mul`, see `Language.ORing.embedding`,
`add₁_zero/one/add/mul`) **but there is no ready-made `Semiterm.lMap_operator` lemma** — the DSL term
desugars to `(Rew.subst v) (Rew.emb op(+).term)`, so the brick to build first is a small tower:
`Semiterm.lMap` commuting with `Rew.emb`/`Rew.subst` (have: `Semiformula.lMap_subst`, `Semiterm.lMap_bind`)
plus `Semiterm.lMap Φ (op.term) = op'.term` for each ORing operator. **Build `wip/DescentLift.lean`
with these operator-lMap lemmas, then promote the X-free lift lemma to `src/` once green.**

---

## 3. E-core — §3 inside PA (the deep half, multi-lap)

Target: `𝗣𝗔 ⊢ goodsteinSentence → 𝗣𝗔 ⊢ ⌜PRWO(ε₀)⌝`. Two layers:

(a) **Semantic backbone** (mathlib + repo, no Foundation): formalize Lemma 3.3/Cor 3.4/Thm 3.5/Lemma 3.6
as ℕ/ONote facts on top of `toOrdinal`/`evalNat`. First brick: a max-coefficient `C : ONote → ℕ` and
`evalNat` order-monotonicity under `C < b` (Rathjen Lemma 2.3(iii) in `evalNat` form) — the workhorse of
Lemma 3.6's inequality (6). These are self-contained, axiom-clean, **Aristotle-eligible**.

(b) **Arithmetization** (Foundation, the genuine wall): re-express (a) as `𝗣𝗔`-derivations. `PRWO(ε₀)`
needs an ℒₒᵣ formula — reuse the seam's `precφ : Semisentence ℒₒᵣ 2` (the arithmetic ε₀-order, X-free)
and state `PRWO` as `∀ primrec-coded sequences …` / the `TI(precφ)` schema. This is where most laps go.

### 3a. The Σ₁-completeness reframe — name the kernel (lap 24, cross-session strategic note)

**Most of the arithmetization (b) is FREE, the same way F-φ is free.** Rathjen's slow-down (3.3/3.4/3.5)
builds **primitive recursive** witnesses `g`, `βⱼ` by *explicit* formulas. Every *computational* claim
about them — "the slowed value at step `k` is `v`", "`C(βₖ) ≤ k+1`", "this `g` strictly descends while
`m < f(n)`" — is **Σ₁/Δ₀**, and **true Σ₁ facts are PA-provable for free** via Foundation's
`sigma_one_completeness` / `re_complete` (the very engine F-φ rides). So the bulk of (b) is Σ₁ glue, not
hand-built induction.

**The irreducible content is a single `Π₁` PA-induction: Rathjen inequality (6)**
`∀ k, mₖ ≥ T̂^{k+2}_ω(βₖ)` (the special Goodstein run from `T̂²_ω(β₀)` never reaches 0). Its semantic core
— the **inductive step** — is now a clean axiom-clean ℕ/ONote lemma **`Dom.ineq6_step`** (`DescentCore.lean`,
lap 24): one `evalNat (k+2)` order-reflection per Goodstein step, no well-foundedness. The PA induction
that iterates it is the analog of **Boundedness on the other side of the proof** — the one genuine multi-lap
girder of E-core(b). Everything else around it is Σ₁ reflection.

> **Attack order (refined):** (1) E-lift X-induction instance (`PRWO ⟹ TI prec`, the X-essential glue;
> the X-free proof-translation half is already done). (2) Semantic backbone bricks, Aristotle-eligible:
> `ineq6_step` ✅ done; the slow-down constructions 3.3/3.4/3.5 as plain ℕ/ONote facts (Lemma 3.2 =
> mathlib `exists_lt_ack_of_nat_primrec`). (3) Arithmetize: computational facts → Σ₁-completeness (free);
> the **one** real lift = inequality (6)'s `∀ k` as a genuine PA-induction. (4) Assemble `E = E-lift ∘
> E-core`, discharge headline, then `#print axioms`.

**Anti-vacuity (E-core is the highest fraud-risk step in the project).** Two guards: (i) keep the
headline `sorry` until `#print axioms peano_not_proves_goodstein` is clean (doctrine); (ii) the `prec`/ε₀-
order E-core builds `PRWO` over **must be the same `prec`** `peano_not_proves_TI` refutes — `Thm56`
already quantifies over a single `prec`, which enforces the coupling that makes the contradiction real.
Treat the `PRWO`/`TI prec` statement as a designated audit surface alongside `TI prec`. Also note: the
`∀ k`/non-termination *Lean* statements (`lemma36_ineq6`, `lemma36_nonterminating`) have **semantically
unsatisfiable** hypotheses (ε₀ is well-founded in ZFC) — they carry **zero** independence force on their
own; only their PA-internal (arithmetized) form does. The reusable non-vacuous content is `ineq6_step`.

**ALT escape hatch** (`Reduction.goodstein_implies_consistency`, Route A): Rathjen Thm 2.8 says
`PRA ⊢ PRWO(ε₀) → Con(PA)`, then Gödel II. Avoids E-lift but **reintroduces `PA_delta1Definable`** (a
Foundation-side axiom) — keep B (the `peano_not_proves_TI` route) as primary; A only if B stalls.

---

## 4. Priority for next laps

1. **`wip/DescentLift.lean`**: operator-`lMap` tower → `succInd`/`univCl` lMap-commutation → schema
   inclusion → the **X-free lift lemma**. Promote to `src/` when green + axiom-clean. (Mechanical, ~1–2 laps.)
2. **`C : ONote → ℕ` + `evalNat`-monotonicity-under-`C<b`** (Lemma 2.3(iii), `src/`, Aristotle-eligible).
3. **Lemma 3.6 inequality (6)** semantic (`src/`), on the `evalNat` backbone.
4. **Lemma 3.3 / Cor 3.4 / Thm 3.5** semantic ordinal constructions (`src/`).
5. **Arithmetization** of 2–4 + the `PRWO ⟹ TI prec` X-induction instance — the dominant wall.
