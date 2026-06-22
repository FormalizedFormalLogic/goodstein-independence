# Pending work — open obligations & attack paths

## ⏭️ LAP-15 (2026-06-22) — review validated lap-14 design; EXECUTE C₁ then C₂. Read this FIRST.

**Direction CONFIRMED sound** (fresh-mind review). Lap 14 finished the crux (Boundedness Thm 5.4 +
corollary B, axiom-clean). The remaining work to **Thm 5.6 (`PA ⊬ TI(ε₀)`)** is C₁+C₂ (connective
tissue), then E (Goodstein⟹TI bridge) + F (arithmetization seam). **Key validated fact (lap 15):** the
cr=0 design is feasible — `atomCut` on an X-atom, applied to `XFreeAx` inputs, preserves `XFreeAx`, because
(i) our `Provable.axL` is the *same-atom* EM axiom `{Xs,¬Xs}` so X-atomic cuts close by **set idempotence**
(the `axL` branch of `atomCutAux`, no truth), and (ii) the truth-surgery branch (`removeFalseLitAux`) fires
only on an `axTrue` leaf *equal to the cut atom* = an X-`axTrue` leaf, which `XFreeAx` forbids ⟹ **vacuous**.
So `removeFalseLitAux` is only ever invoked on X-FREE cut atoms (emitting X-free `axTrue`, fine).

### C₁ — XFreeAx-preserving cutElim → cr=0 (THE next target; the big port). Plan:
Introduce in `Boundedness.lean` (or a new `src/GoodsteinPA/XFreeCutElim.lean`) the cut-rank-carrying carrier
`PXFc α c Γ := ∃ d : Deriv Γ, d.o ≤ α ∧ d.cr ≤ c ∧ XFreeAx d` (generalises lap-14's `PXF` = `PXFc α 0`).
Port, each tracking `XFreeAx` (the `Deriv` constructors used are exactly axL / X-free-axTrue / verumR / weak
/ andI / orI / allω / exI / cut — none add an X-`axTrue` except the vacuous `removeFalseLit` branch above):
1. **Smart builders** `PXFc.{mono,weakening,axL,axTrue(Xfree),verumR,andI,orI,exI,allω,cut,contr}` —
   mirror `ZinftyGen.Provable.*` (lines 179–265) but carry the third `XFreeAx` component. Most are trivial
   (`XFreeAx` of a built node = conjunction/∀ of the parts' `XFreeAx`, by the `def XFreeAx` clauses).
2. **`removeFalseLitAux` / `removeFalsumAux`** preserve `XFreeAx`: port `ZinftyGen` 1087/1334 threading the
   property. KEY: `removeFalseLitAux` is stated for a FALSE literal `signedLit b₀ r₀ v₀`; on the X-route it
   is only ever called with `r₀` X-FREE (from the vacuous-branch argument), so its emitted `axTrue` leaves
   are X-free ⟹ `XFreeAx`. State it with an added hyp `Sum.isLeft r₀ = true` (X-free cut atom) to make this
   explicit, OR thread `XFreeAx d` and show the X-axTrue case can't arise.
3. **`atomCutAux` / `atomCut`** (ZinftyGen 1191/1320) preserve `XFreeAx`: the `axTrue`/`heq` branch needs the
   leaf = cut atom; for X-free cut atoms it's an X-free leaf (fine); the cut atom is X-free anyway on the
   route. To be safe handle generic atoms: if the cut atom is an X-atom, the `axTrue`/heq branch is vacuous
   by `XFreeAx`, and the `axL` branch + structural cases are truth-free.
4. **`cutReduceConj/Disj/AllAux/All`** (ZinftyGen 796/826/862/1017) preserve `XFreeAx`: they compose the
   `XFreeAx`-preserving inversions (lap-14 `andInv_xfree`/`orInv_xfree`/`allInv_xfree` — already built! but
   at cr=0; **generalise them to cr ≤ c** since inversions don't change cut rank) + builders + `cut`.
5. **`cutElimPrincipal` / `cutElimStepAux` / `cutElimStep` / `cutElim`** (1422/1479/1529/1537): structural
   port; `cutElim : PXFc α c Γ → PXFc (omegaTower c α) 0 Γ`. This is the deliverable feeding corollary B.
**Aristotle target:** a self-contained "`removeFalseLitAux` preserves `XFreeAx` for X-free `r₀`" or a
`PXFc` builder lemma (inline the `Deriv`/`XFreeAx`/`o`/`cr` defs). Bounded + mechanical.

### C₂ — `embedC` over generic LX (parallel/after C₁). Plan in lap-14 HANDOFF §C₂ (CRITICAL: X-induction
axioms via the meta-induction tower of `cut`s on `φ(i)` + `provable_em` base/step — NOT `provable_true`,
which would lone-X-`axTrue`. `𝗣𝗔⁻` X-free axioms can still go via `provable_true`. Port the lap-10 worked
meta-induction). Produces the `XFreeAx` derivation of `{TI}` that C₁ then reduces to cr=0.

## ⏭️ LAP-13 (2026-06-22) — Buchholz route EXECUTING; read this FIRST

**Read `ANALYSIS-2026-06-22-lap13-boundedness-design.md`** (full Buchholz §5 pp.26–31 read + the design).
Lap 13 built ALL the Boundedness prerequisites — green, axiom-clean, in `src/`:
- `LangX.lean` — `structLX (S:ℕ→Prop) : Structure LX ℕ` (the `⊨^S` carrier) + DecidableEq instances +
  `eval_Xatom`. **The `⊨^α` carrier.**
- `ZinftyGen.lean` — **M5 cut-elim generalised over `{L}[ORing L][Structure L ℕ][DecEq…]`**,
  `Provable.cutElim` axiom-clean. Reused wholesale (no cut-elim re-proof on the X-route).
- `TruthSem.lean` — `rk`/`orderType`/`levelSet`/`models (⊨^γ)`/`Sat` + **`models_lMap` (X-free
  invariance)** + `orderType_le_of_forall`.
- `XPositive.lean` — `XPos` + **`models_mono` (⊨^γ monotone in γ on X-positive formulas)** (Buchholz
  cases 2/3/4) + `val_structLX_eq` + `eval_mono`.
- `wip/BoundednessProbe.lean` — `Xatom_axiom`: the Buchholz X-atom axiom `{Xs,¬Xt}` (sᴺ=tᴺ) is
  derivable in generic Z∞ at `(LX,structLX S)` for ANY S. (Validation probe; stays in wip.)

**THE crux still open = Boundedness Thm 5.4 (the 8-case induction) + its formula scaffolding.** Next:
1. **Construct `Prog_≺(X)` / `TI_≺(X)` as `LX`-formulas.** Parametrise by `prec : Semiformula LX ℕ 2`
   (the order, with its ℕ-interpretation = the wellfounded `lt`; for the app `prec` is ℒₒᵣ-definable OT
   order). `Prog := ∀x(∀y(y≺x → Xy) → Xx)`, `¬Prog ≃ ∃x(∀y≺x Xy ∧ ¬Xx)`. Use Foundation DSL/`∀⁰`/`∃⁰`
   + `Xatom`. Pin the inversion shape (`exI`/`allω`/`orI` on `¬Prog`) the induction needs.
2. **Boundedness (Thm 5.4):** induction on the cut-free `Provable β 0` `Deriv` over `LX` (cases =
   our constructors axL/axTrue/verumR/weak/andI/orI/allω/exI/cut ↔ Buchholz's 8). Ingredients ALL
   built: Ax→`Xatom_axiom` (X-pair) / `models_lMap` (TRUE₀); ⋀/⋁/Rep→IH + `models_mono`; ¬Prog `exI`
   inversion = case 2; `cut` on X-atom = case 8. Conclude `Sat lt (α+2^β) Γ`. THE new theorem.
3. **Corollary** `‖≺‖ ≤ 2^β` via `orderType_le_of_forall` (invert TI → ⊢^β_1 ¬Prog,Xn → 5.4 → ⊨^{2^β}Xn
   → rk n < 2^β ∀n).
4. **M4 `embedC` over LX** (mechanical `{L}` generalisation like M5; PA(X) axioms true in structLX S
   for any S since first-order induction holds for any fixed predicate) + assemble **Thm 5.6**
   (`Z⊢TI(X) ⟹ ‖≺‖<ε₀`).
5. **Goodstein⟹TI_≺(X)** bridge (VERIFY-(b)) + arithmetization seam (OT↔ε₀, `‖≺‖=ε₀`) ⟹ headline.

**Banked off-path (do NOT resume):** witness-bounded `wip/` calculi (Towsner/operator-H). The ℒₒᵣ-only
`src/Zinfty.lean`/`src/Embedding.lean` stay for now (existing users); the live chain uses the LX versions.

## ⏭️ LAP-12 PIVOT (2026-06-22) — superseded by lap-13 above (kept for the Buchholz-route rationale)

**Read `ANALYSIS-2026-06-22-lap12-buchholz-pivot.md`.** The lap-11 "build the witness-bounded `Zᵏ`" plan
below is **retired**: lap 12 proved its §19.6 cut-elim needs the Buchholz operator `H` (ADDENDUM 7 in
`ANALYSIS-…-cutelim-k-threading.md`) — a multi-lap wall — while Buchholz §5's **witness-FREE** route reuses
the done-and-axiom-clean **M4 `embedC`** + **M5 `cutElim`** and needs only a **Boundedness** theorem. The
lap-11 "embedC is the wrong object" verdict was a conflation of order-type-boundedness (valid, Buchholz
Thm 5.4) with witness-boundedness (walled, Towsner). **`embedC` is the RIGHT object** (Buchholz Thm 5.5).

**New critical path (Buchholz §5 — `Z ⊢ TI_≺(X) ⟹ ‖≺‖ < ε₀`, then Goodstein⟹TI(ε₀)):**
- **0. VERIFY-FIRST (do before deep work):** (a) M5/M4 take the set variable `X` (extend `ℒₒᵣ`→`ℒₒᵣ∪{X}`
  or add `X` as a fixed relation symbol; `embedC.axm`/`provable_true` only need the `X`-free PA axioms);
  (b) the Goodstein⟹TI_≺(X) bridge is provable in PA via the Phase-0 CNF-ε₀ encoding. Neither is a known
  wall; confirm before sinking laps.
- **1.** Truth semantics `⊨^α Γ` (`X := {n : |n|_≺<α}`), `Prog_≺`, ≺-norm `|n|_≺`, order type `‖≺‖`,
  X-positivity — light self-contained defs.
- **2.** **Boundedness (Thm 5.4)** — `Z∞ ⊢^β_1 ¬Prog_≺(X),¬Xs₁,…,¬Xsₖ,Γ & |sᵢ|_≺≤α ⟹ ⊨^{α+2^β} Γ`
  (Γ X-positive), by induction on the cut-free `Provable β 0`-derivation (8 cases, Buchholz p.29).
  Corollary: `Z∞ ⊢^β_1 TI_≺(X) ⟹ ‖≺‖ ≤ 2^β`. THE new theorem; no Hardy, no witness bound.
- **3.** Goodstein ⟹ TI_≺(X) for the ε₀-order (bridge; Kirby–Paris/Cichoń; reuse Phase-0 encoding).
- **4.** Assembly: PA⊢Goodstein ⟹ (M4) ⟹ (M5 cut-free `β<ε₀`) ⟹ (Boundedness) `‖≺‖≤2^β<ε₀`, but the
  ε₀-order has `‖≺‖=ε₀` ⟹ `False` ⟹ discharge headline, `#print axioms` clean.

**Banked off-path (do NOT resume on this route):** the witness-bounded `wip/` calculi. Lap-12 PROVED the
norm-budget half of Towsner §19.6 (`cutReduceAllAux` in `wip/OperatorZinfty.lean`, axiom-clean, via the
norm-carrying `ZekdProv` wrapper — see ADDENDUM 6); the witness-budget half needs operator `H` (ADDENDUM
7). Kept as reference IF the Buchholz route ever stalls. M6 (Hardy) is off-path too.

---

## ⏭️ LAP-11 FINAL STATE (2026-06-22) — SUPERSEDED by the lap-12 pivot above (kept for history)

**M4 — the embedding `embedC` — is COMPLETE, axiom-clean, promoted to `src/GoodsteinPA/Embedding.lean`,
in the default build.** `embedC : Derivation2 (𝗣𝗔:Schema) Γ → ∃ c, ∀ e, ∃ α, Provable α c (Γ.image
(asg e ▹))`. The two hard cases fell to two reusable lemmas: `Provable.exI_closed` (closed-witness
∃-intro, from value-congruent EM `provable_em_cong_gen` + cut) for `exs`; `provable_true`
(ω-completeness) for `axm`. See HANDOFF lap-11.

**⚠️ COURSE CORRECTION (lap 11, grounded in Towsner §13–17) — read
`ANALYSIS-2026-06-22-witness-bound-gap.md`.** The headline needs the **witness-bounded calculus
`Zᵏ`**, NOT a bound on M5's `Provable`. M5 tracks cut-rank `c` but drops Towsner's I∃ witness bound
`k` (`value(t) ≤ h_α(k)`) — and without it the lower bound (Thm 17.1) does not bite (`provable_true`
gives a cut-free `< ε₀` derivation of `{↑gs}`; bounded quantifiers cost `allω`=`ω`, `exI` costs `+1`
regardless of witness value). So `embedC` = the *unbounded* embedding (Towsner Thm 14.2), reusable but
not the headline object; the lap-11 `wip/Bounding.lean` bridge `cutfree_lt_eps0_absurd` is FALSE as
stated. The lap-9 "bound directly on unbounded `Deriv`" reframe is retracted.

**Corrected critical path (= lap-5 plan steps 1–4, now confirmed):**
1. **`Zᵏ`** = M5 `Deriv` + `(α,k)` witness bound on `exI`. Revive banked `wip/` Zekd/OperatorZinfty
   (lap-8 worked §19.2–19.5 + control axis). Carrier: `ZekdProv` wrapper `∃ α'≤α, α'.NF ∧ Zᵏ …`.
2. **Bounded embedding (Towsner Thm 16.1/16.5/16.7)** into `Zᵏ`. `axm`: 16.1 (universal axioms, via
   `provable_true` on the bounded matrix) + 16.5 (induction, bounded meta-induction ordinal
   `ω·4#2^{rk}#2`, via `provable_em` + `Provable.exI_closed`). Structural: port `embedC` cases.
3. **`(α,k)`-cut-elim (Thm 19.9)** — `wip/` Zekd §19 grind (`ANALYSIS-…-cutelim-k-threading.md`).
4. **Subformula bridge to `B`** (M6) + Σ₁-arithmetization seam (M7a: `codeOfREPred` ↔ `atomTrue`,
   anchor `codeOfREPred_spec`) + ONote↔Ordinal<ε₀ seam ⟹ contradiction with
   `lowerBound_hardy_selfcontained`.

**BANKED reusable (src/Embedding.lean, axiom-clean):** `provable_true`, `provable_em`,
`provable_em_cong_gen`, `Provable.exI_closed`, `embedC` structural cases. Do NOT discard.
**Aristotle candidates:** a `Zᵏ` mono/inversion lemma; the ONote↔Ordinal<ε₀ bridge; a `norm_add_le`/
NF ordinal fact from the §19 bookkeeping.

---

## ⏭️ LAP-10 FINAL STATE (2026-06-22) — superseded by lap-11 above; kept for context

**Headline result: the M5 `axTrue` truth-layer surgery is DONE (axiom-clean) and the assignment-
carrying embedding `embedC` is 8/10.** Full status in `HANDOFF.md`. The TWO remaining `embedC` cases
(`axm`, `exs`) both reduce to ONE shared deep lemma — build it next:

**`provable_subst_congr` (closed-term substitution congruence — THE next chip).** For closed terms
`s s'` of equal ℕ-value and any `ψ : SyntacticSemiformula ℒₒᵣ 1`: the sequent `{∼(ψ/[s]), ψ/[s']}` is
Z∞-derivable (`∃ a, Provable a 0 {...}`). Proof = induction on `ψ.complexity` (the `provable_em`
template), tracking the two terms:
- **atomic** `ψ = rel/nrel R v` (v mentions `#0`): `ψ/[s]` and `ψ/[s']` have EQUAL truth (`Evalm`
  depends on a term only via its value — `Semiterm.val_substs` (Semantics.lean:123) + `eval_substs`
  (l.391)). So `∼(ψ/[s])` and `ψ/[s']` can't both be false ⟹ one is a true literal ⟹ `Provable.axTrue`.
  (Needs the value-equality `hval` and that `(ψ/[s]).LitTrue ↔ (ψ/[s']).LitTrue`.)
- **and/or/all/exs**: recurse structurally, exactly mirroring `provable_em`'s compound cases (the ∀/∃
  cases use the `nm`-family + `exI`/`allω`, with the substituted term threaded through `/[·]`).
Then derive:
- **`Provable.exI_closed (s closed, value m)`: `Provable α c (insert (ψ/[s]) Γ) → ∃ β, Provable β c
  (insert (∃⁰ψ) Γ)`** — cut `provable_subst_congr s (nm m)` (weakened into Γ) against the hypothesis to
  swap `ψ/[s] ⤳ ψ/[nm m]`, then `Provable.exI ψ m`. Finishes `embedC.exs` (the `rew_subst_term` setup
  is already in place — see `wip/Embedding.lean`).
- **`embedC.axm`**: `𝗣𝗔⁻` instances → strip `∀` (`allω`), decompose connectives, bottom at `axTrue`;
  `univCl(succInd ψ)` → the worked meta-induction below, with `nm n+1 = nm(n+1)` via the same congruence.

API notes: term value = `Semiterm.valm ℕ ![] id s`; numeral value `valm ℕ … (nm m) = m` (find/derive
`val_numeral`); `nm`/`signedLit`/`LitTrue` live in `src/GoodsteinPA/Zinfty.lean` now.

---

## ⏭️ LAP-10 PROGRESS (earlier in lap)

**Done lap 10 (all committed, green):**
- `rew_subst_nm` PROVED ⟹ `provable_rew`/`ZProvable.rew` fully axiom-clean (`[propext, choice,
  Quot.sound]`). The M4 renaming enabler is DONE.
- `embed` `shift` + `all` PROVED ⟹ **8/10 cases** (only `axm`, `exs` remain). `all` is the ω-rule
  case: `provable_rew` substitutes the freed var by each `nm n` (undoing the `shift` on `Γ` via
  `rewrite_comp_shift_eq_id`), then `Provable.allω`.

**Remaining M4 cases — both deep:**

### `axm` (THE crux — Z∞-derive each PA axiom). `φ ∈ (𝗣𝗔:Schema)` = `↑σ`, `σ ∈ 𝗣𝗔⁻ ∪ InductionScheme`.
`axm` does NOT need the assignment reformulation (φ=↑σ is CLOSED). By `ZProvable.weakening` (`{↑σ} ⊆ Γ`
since `↑σ ∈ Γ`) reduces to `ZProvable {↑σ}` per axiom.
- **(a) `σ ∈ 𝗣𝗔⁻` (PeanoMinus, finite):** each a true closed ∀-sentence (semiring/order axioms). Z∞-
  derivable at finite ordinal. Bounded grind (enumerate Foundation's `PeanoMinus` axiom set).
- **(b) `σ = univCl(succInd ψ)` — induction via ω-rule. FULL PAPER PROOF WORKED OUT (lap 10):**
  `succInd ψ = ψ(0) → (∀x, ψ(x)→ψ(x+1)) → ∀x, ψ(x)`. After stripping `univCl` (iterated `allω` over the
  free-var numeral assignments) and two `orI` (Tait `A→B ≡ ∼A⋎B`), reduce to the sequent
  `S := {∼ψ(0), ∼(∀x,ψ(x)→ψ(x+1)), ∀x,ψ(x)}`. Introduce `∀x,ψ(x)` by `allω`: ∀n need `{∼ψ(0), ∼∀step, ψ(n)}`.
  **Meta-induction on n** (the heart — ω-rule absorbs PA-induction):
  - n=0: `{∼ψ(0), …, ψ(0)}` has `ψ(0)` and `∼ψ(0)` ⟹ `provable_em`. ✓
  - n→n+1: want `{∼ψ0, ∼∀step, ψ(n+1)}`. **`cut` on `ψ(n)`** (cut rank = `complexity ψ + 1`, uniform):
    - left `{∼ψ0, ∼∀step, ψ(n)}` = IH `D_n`. ✓
    - right `{∼ψ0, ∼∀step, ψ(n+1), ∼ψ(n)}`: `∼∀step = ∃y∼step(y)`; `exI` witness `n` reduces to
      `{∼ψ0, ∼step(n), ψ(n+1), ∼ψ(n)}` where `∼step(n) = ψ(n) ⋏ ∼ψ(n+1)`; `andI` splits into
      `{ψ(n),…,∼ψ(n)}` (em ✓) and `{∼ψ(n+1),…,ψ(n+1)}` (em ✓).
  Cut rank uniform `complexity ψ + 1`; ordinal O(n) per instance ⟹ `allω` gives ~ω. **Uses ONLY M5's
  existing constructors** (`provable_em`/`cut`/`exI`/`andI`/`allω`/`orI`) — no new smart constructors.
  Lean friction = Foundation-syntax wrangling: unfold `↑(univCl(succInd ψ))` `“…”`-DSL into the nested
  `⋎/∼/∀/∃` structure + the numeral substitutions `step(n)`, `ψ(x+1)`. Mechanical but intricate; multi-step.

### `exs` (needs the assignment reformulation). Open witness term `t` ⟹ naive statement can't close it.
Reformulate `embed : ∀ e:ℕ→ℕ, ZProvable (Γ.image (ρe ▹))`, `ρe := Rew.rewrite (nm∘e)`. ALSO needs a Z∞
closed-term→numeral collapse (`ρe▹t = nm m` is arithmetic, built from PeanoMinus eqns ⟹ intertwined with
`axm`(a)). Restructure re-proves the 8 done cases (mechanical, ρe distributes) — do AFTER `axm`.

---

## 🧭 LAP-9 DEEP-REFLECTION COURSE-CORRECTION (2026-06-22)
Full synthesis: `REFLECTION-2026-06-22.md`. STATUS refreshed. **The priority order below (A/B/…) is
SUPERSEDED.** New order, hardest-first = **unavoidable-first**:

1. **M4 — embedding `𝗣𝗔 ⊢ φ ⟹ Z_∞ ⊢^{α}_c {φ}` = THE next target.** The *universal bottleneck*:
   needed on Route A, two-phase Route B, AND the abandoned Zekd route — there is no headline path that
   skips it. **LAP-9 FEASIBILITY PROBE (done this lap) — the machinery EXISTS; here is the mapped path:**
   - **Foundation's finitary calculus** (`.lake/.../Foundation/FirstOrder/Basic/Calculus.lean`):
     `Derivation 𝓢 : Sequent L → Type` (List sequents), constructors
     `axm (φ∈𝓢) | axL | verum | or | and | all (φ.free :: Γ⁺) | exs t | wk | cut` — maps almost 1-1
     onto M5's `ZinftyF.Deriv`. A **Finset** variant `Derivation2` exists (`Calculus2.lean:13`, same
     constructors) + `provable_iff_derivable2 : 𝓢 ⊢ φ ↔ 𝓢 ⊢!₂! φ` (`Calculus2.lean:94`) — matches M5's
     Finset substrate (use it to skip the List→Finset bridge).
   - **The lap-6 "derivation-substitution" deep case is ALREADY PROVIDED:**
     `Derivation.rewrite : 𝓢 ⟹ Γ → ∀ (f:ℕ→SyntacticTerm L), 𝓢 ⟹ Γ.map (Rew.rewrite f ▹ ·)`
     (`Calculus.lean:255`). So the **finitary `all` (`φ.free :: Γ⁺`) → M5 ω-rule `allω`** conversion is:
     for each numeral `n`, `rewrite` the free var by `n` to get `𝓢 ⟹ φ/[n] :: Γ`, embed each, assemble
     via `Provable.allω` (`src/Zinfty.lean:183`). **No missing machinery.**
   - **The `axm` case** splits cleanly because `𝗣𝗔 = 𝗣𝗔⁻ + InductionScheme ℒₒᵣ Set.univ`
     (`Foundation/FirstOrder/Arithmetic/Schemata.lean:52`): (a) `φ ∈ 𝗣𝗔⁻` (PeanoMinus, **finite**) —
     each a true ∀-sentence, Z∞-derivable at a finite ordinal (bounded grind); (b) `φ = univCl(succInd ψ)`
     (`mem_InductionScheme_of_mem`, Schemata.lean:85) — derive in Z∞ **via the ω-rule** (`ψ(n)` for each
     `n` by `n`-fold step, then `allω`), ordinal ~`ω·k`. **This is the one genuine deep case** (Buchholz
     §5.5 / Towsner §16) — but it's standard textbook content and `Provable.allω` is already built.
   - **LAP-9 DID THIS: `wip/Embedding.lean` COMPILES** (`lake env lean wip/Embedding.lean`).
     `embed : Derivation2 (𝗣𝗔:Schema) Γ → ∃ α c, Provable α c Γ` over the SAME `Finset (SyntacticFormula
     ℒₒᵣ)` substrate (no language translation). **6/10 cases DONE** (verum/and/or/wk/cut/closed).
     **`provable_em` FULLY PROVED + axiom-clean** (`[propext,choice,Quot.sound]`): the Z∞ excluded-middle
     `∀ φ Γ, φ∈Γ → ∼φ∈Γ → ∃ a, Provable a 0 Γ`, incl. the ∀/∃ numeral ω-family. Promotable to `src/`.
   - **4 disclosed `sorry`s remain = the genuine deep content, ALL needing free-var/subst machinery
     for M5's `Deriv` (interdependent). Build the shared enabler FIRST:**
     - **(0, enabler) M5 renaming/subst lemma** = analogue of Foundation `Derivation.rewrite`
       (`Calculus.lean:255`): `Provable α c Γ → Provable α c (Γ.image (Rew…▹·))`, induction on `Deriv`
       (8 cases; `allω` case = the care point). Unlocks `shift`/`all`/`exs` together.
     - **`shift`** — corollary of the enabler. **`all`** — free var `&0` → each numeral via enabler →
       `allω`. **`exs`** — witness term → numeral value → `exI`. **`axm`** (deepest) — PeanoMinus finite +
       `univCl(succInd ψ)` via ω-rule. Buchholz §5.5.
2. **M7a — transparent arithmetization** = parallel/fallback (shovel-ready, faithfulness-gated):
   `gAllReal = ∀x∃y[g_y(x)=0]` + `𝗣𝗔 ⊢ goodsteinSentence ↔ gAllReal`, gated by `Bridge.lean`.
3. **Bounding bridge (small, downstream):** prove on M5's **real cut-free `Deriv`** directly
   (`allInv` ∀ away, read `exI` numeral off, witness `≤ hardy(toONote α)N`), combine with M6's
   `hardy_lt_goodsteinLength` (`src/LowerBound.lean:258`). **Reuse M6's ℕ-domination fact, NOT the
   abstract `B` transport** — the `B` lower bound is the template, banked. Ordinal seam = one `toONote`
   (check mathlib `ONote.repr` surjectivity onto `[0,ε₀)`).

**DO NOT RESUME** the witness-bounded cut-elim thread: `cutReduceAllAux`, `Zekd`, any 4th index
calculus. Proven off-critical-path (lap-8 findings: single-index Hardy inequality is FALSE; landscape
memory: the Hardy `k` index was never needed for cut-elim). `wip/{BoundedZinfty,SplitZinfty,
OperatorZinfty}.lean` = reference only. Everything below this block (the lap-7/8 A/B/Zekd plans) is
**historical context**, not the live plan.

---

## 🗺️ OPEN-OBLIGATION INVENTORY (lap-7 end) — full list + 3 attack paths each
### ⚠️ SUPERSEDED by the lap-9 block above — kept for history/attack-path detail only.
The headline `Statement.peano_not_proves_goodstein` is the only `src/` sorry (the designated open
target; anti-fraud — do NOT fill until the chain genuinely closes axiom-clean). It is reached via the
connecting spine. Open spine pieces, with attack paths:

## 🧭 LAP-8 STRATEGIC PIVOT (ON-LINE-FINDINGS 2026-06-22) — TWO-PHASE architecture is the headline path
The findings doc (`archive/findings/…omega-rule-commuting-bound.md`) **proves the §19.6 commuting bound
cannot close in any single-numeric-`k`/`(k,d)`/`(k,d,e)` system** (the Hardy inequality is FALSE; Towsner
hand-waves it). The lap-8 `Zekd cutReduceAllAux` commuting cases hit exactly this wall (norm-boundary
strictness). **Resolution (literature-standard, Buchholz §5 / Schwichtenberg–Wainer Ch.4): NEVER thread
the witness index through cut-elim. Two phases:**
  1. **Cut-elimination on the WITNESS-INDEX-FREE calculus** — pure ordinal + cut-rank. **This is M5,
     `src/Zinfty.lean`, ALREADY DONE + axiom-clean** (`Deriv.Provable.cutElim`). Commuting cases there are
     one-liners (`α#βₙ < α#β`) — no `k`/`d`/`e` to thread.
  2. **Hardy-bound the CUT-FREE result** — on a cut-free derivation there is NO `+α` growth, so the
     `max{k,n}`-vs-`+α` clash cannot arise. **This is M6, `lowerBound_hardy_selfcontained`, ALREADY DONE**
     (applied at `c=0`).
**The remaining work is the BRIDGE connecting them** (was "step 4 subformula bridge", now the critical
path): a cut-free `Z∞ ⊢^{α}_0 {gAll}` (from M4-embed + M5-cutElim) ⟹ a witness-bounded `B`-derivation
(subformula property: cut-free `{gAll}` uses only `GForm` subformulas; + a Hardy **bounding lemma** reading
off `∃`-witnesses ≤ `H_α(N)` on the cut-free structure) ⟹ contradicts `lowerBound_hardy_selfcontained`.
**Next lap: build this bridge.** The `Zekd`/`SplitZinfty` witness-bounded-cut-elim effort is a banked
alternative (NOT on the critical path anymore); its inversions/§19.5/`mono_e`/structural-`cutReduceAllAux`
cases stand for reference. Faithfulness corrections from the findings (carry into write-ups): Lemma 16.10
is `α<β ∧ τα<k ⟹ h_α(k)<h_β(k)` (strict); cut-elim base is `ω^α` (Towsner)/`3^α` (Buchholz), not `2^α`;
`h_{β#ω}(k)=h_β(2k)` is NOT a Towsner lemma (heuristic only); the operator `H[X]` is Buchholz-1992, not
the on-disk notes (which are pure-ordinal for PA).

---

**LAP-8 UPDATE — (A)/(B) substantially advanced.** Hardy-infra layer BANKED (axiom-clean, `src/`):
`hardy_add_comp`/`hardy_add_collapse` (control collapse) + `hardy_comp_lt_goodsteinLength` (lower-bound
nested-index domination). Control-ordinal operator calculus `Zekd α e k d c Γ` built in
`wip/OperatorZinfty.lean`, sorry-free through §19.5, with the NEW `mono_e` control axis. Design validated
(ADDENDUM 5): single control ordinal `e` closes the ADDENDUM-4 witness-index obstruction (no set-valued
`H` needed). **ONE remaining girder for step-1 cut-elim: §19.6 `cutReduceAll` on `Zekd`.**
  - **[LAP-8 NEXT] Port `Zinfty.lean:785 cutReduceAllAux` to `Zekd`.** Invert ∀-side → `fam`; induct on
    ∃-side; principal `exI` cuts `fam(witness)`; commuting cases reapply at `osucc(α+γ)`
    (`add_osucc_descent` banked), `d ↦ d + norm α` (norm-budget), `e` raised at the top cut via `mono_e`.
    **FIRST**: NF-ify the `Zekd` leaf rules (`trueRel`/`trueNrel` need `hαNF`) — leaf cases need
    `norm(α+γ) ≤ norm α + norm γ` (`norm_add_le`, NF-essential). ADDENDUM 5 has the subtlety + 3 fixes
    (option (b)/NF-ify-leaves cleanest). Budget arithmetic: issue leaf at the node's own `γ` then `weak`
    up to `osucc(α+γ)` (avoids the `osucc` `+1`-vs-strict-`<` boundary).

**(A) §19.6 `cutReduceAll` — the critical-path crux** (calculus + Hardy infra now in place — see LAP-8).
  1. **Control-ordinal operator calculus (RECOMMENDED).** Replace `Zkd`'s `(k,d)` with an index
     `(e, k, d)` where `e : ONote` is a *control ordinal* and the ω-premise / witness bound use
     `hardy e (n + k) + …` (a `hardy`-closed index). Cut-elim raises `e` to dominate cut-formula bounds;
     the principal cut's witness `w ≤ hardy γ (max k n + d) ≤ hardy e (n + k + d)` (γ<e, hardy mono in
     both args) stays controlled. Lower bound survives via **general Hardy additivity** `hardy α (hardy e m)
     ~ hardy (e (#)+ α) m` (e+α<ε₀ ⟹ G dominates). Port §19.2–19.5 from `SplitZinfty` (`max k ·` ⤳
     `hardy e ·`). **Lap-7 de-risk:** the cut-elim *control* side needs NO new lemma — the witness
     control `hardy γ (idx) ≤ hardy e (idx)` (γ<e) is the **existing** `hardy_le_of_lt` (`src/Hardy.lean`,
     `+ hardy_monotone` for the argument). Only the *lower-bound* side needs general Hardy additivity (B).
  2. **Buchholz set-valued operator `H`** (Buchholz §9 / 1992) — fully general; heavier. Fallback if the
     single control-ordinal `e` can't express some closure. `ON-LINE-REQUEST` filed for the PA spec.
  3. **Restrict the calculus to the `GForm` fragment** (the headline only needs cut-elim for derivations
     of `{gAll}` and its subformulas). The ∃-side may then have bounded structure making the witness
     index controllable without a full operator. Investigate whether the subformula property pre-bounds it.

**(B) General Hardy additivity** `hardy (e (#)+ α) m = hardy α (hardy e m)` (infra for A.1; generalizes
  the proved finite-tail `hardy_add_ofNat`).
  1. Induct on α through the fundamental-sequence structure (successor + limit), using the banked
     `fundamentalSequence`/`Reaches`/`hardy_le_of_reaches` machinery in `src/Hardy.lean`.
  2. Prove only the *inequality* `hardy α (hardy e m) ≤ hardy (e + α) m` (ordinary `+`) — weaker but may
     suffice for domination; likely easier than the exact `#`-additive identity.
  3. Aristotle target: self-contained ONote/Hardy statement (feed once A.1's exact form is pinned).

**(C) §19.7 `cutElimStep` + §19.9 `cutElim`** (depend on A). Ordinal `ω^α` (`norm_omegaPow` banked);
  iterate. Paths: port `src/Zinfty.lean` structure / the `SplitZinfty` helpers / existential-index.

**(D) Subformula bridge** (cut-free operator-derivation of `{gAll}` ⟹ `B`-derivation ⟹ lower bound).
  Paths: structural subformula-closure induction / `GForm ↪ ℒₒᵣ` identification / reuse M6 as-is.

**(E) M4 embedding `PA ⊢ φ ⟹ (calculus) ⊢ φ`** — INDEPENDENT of A (parallel thread). Recon done lap 6.
  Paths: induct on Foundation `Derivation` (axm = Lemma 16.1 + Cor 16.6 induction instances; `all`→ω-rule
  via derivation-substitution; `exs`→witness bound) / list→finset bridge / scope `axm` first.

**(F) M7a language gap** `𝗣𝗔 ⊢ goodsteinSentence ↔ gAllReal` — INDEPENDENT (parallel thread). Paths:
  arithmetize `goodsteinSeq` as a real Π₂ `ℒₒᵣ` formula (Foundation Σ₁ tools) / gate by `Bridge.lean` /
  prove one direction first.

**Lap-7 acted on (A): conceptual crux resolved, 4 lemmas proved, `(k,d)` calculus through §19.5 built,
the two §19.6 obstructions precisely characterized (norm-budget CLOSED, witness-index ⟹ needs operator).**

---

## ✅ LAP-7 — cut-elim `k`/`τ` crux RESOLVED (offline read of Towsner §15–§20). See `ANALYSIS-2026-06-22-cutelim-k-threading.md`.
The lap-6 "norm grows under addition ⟹ cut-elim might break `norm<k`" worry was a **misframing**.
Resolved facts (the design for ALL of §19): (a) `k` is **not** fixed — it grows (§19.5 `k↦2k`; §19.6
`k↦h_{β#ω}(k)`; §19.7 `k↦h_{ω^α}(k)`). (b) `lowerBound_hardy_selfcontained` is already `∀k` ⟹ growth
harmless. (c) every `ONote` is `<ε₀` by construction ⟹ ε₀ side-condition **free**. ⟹ **state the whole
cut-elim chain existentially in `k`**: `CutFree α Γ := ∃k, Zk α k 0 Γ`; endgame
`(∃k c, Zk α k c Γ) → α.NF → ∃ α' k', α'.NF ∧ Zk α' k' 0 Γ`, then subformula-bridge + lower bound.
Route decision recorded in `STATUS.md`: **STAY ROUTE B**. `ON-LINE-REQUEST` closed.

### Refined §19.6 plan (`cutReduceAll` for `Zk`) — the next girder, now unblocked
Port `src/Zinfty.lean:785 cutReduceAllAux` (the lap-3 ∀/∃ reduction over the unbounded `(α,c)`
calculus, fully proved) to `Zk`, adding the `(k,NF,norm)` bookkeeping:
- **Structure (unchanged from lap 3):** invert the ∀-side once (`allInv` → numeral family
  `fam : ∀n, Zk α k c (insert (φ/[nm n]) Γ)`), then **induct on the ∃-side `Zk γ k c Δ`** with
  `(∃∼φ)∈Δ`; principal `exI` case = cut `fam n` at the witness numeral; commuting cases re-apply the
  rule over `Δ.erase(∃∼φ) ∪ Γ`. `Zk` is `Prop`-valued, so induct directly (no height fn `o d`); the
  running ordinal is the constructor bound `γ` itself (sub-bounds `<γ` come from the descent premises).
- **Bound:** ordinal `α + γ` (`ONote.+`, `add_lt_add_left_NF`/`le_add_left_NF` banked); slack via
  `osucc` at cuts (`lt_osucc`, `osucc_NF` banked).
- **`k`-growth (the new content vs lap 3):** the conclusion's `k` is **`h_{β#ω}(k)`** (a Hardy value),
  NOT the input `k` — Towsner §19.6 exactly. ⚠️ **LAP-7 FINDING — the `allω`-commuting case is a REAL
  obstruction, not mechanical.** Reconstructing the ω-rule after adding `α` to the bound needs
  `norm(α+βₙ) < max K n`, but `norm(α+βₙ) ~ norm α + n` exceeds `max K n ~ n` for large `n`, for ANY
  fixed `K` (norm is not `<`-monotone, so `βₙ<β` doesn't bound `norm βₙ`; natural sum + `τα<k` don't
  save it). Towsner's "follows from IH" glosses this. **The numeric `(α,k)` form may genuinely need
  either (1) Buchholz operator-controlled derivations, (2) a generalized `Zk.allω` with a controlled
  premise-index `f n` (re-verify M6 lower bound survives — tension: cut-elim wants `f` to GROW to fit
  `+α`, the lower bound wants witnesses `≤ h(f n) < G(n)` BOUNDED), or (3) re-derived Towsner 16.8–16.10
  Hardy inequalities (likely insufficient per the `+α` analysis).** Full derivation +
  attack options in `ANALYSIS-2026-06-22-cutelim-k-threading.md` ADDENDUM. `ON-LINE-REQUEST` re-filed.
  ⚠️ **LAP-7 UPDATE — option (2) (global numeric index swap) is ELIMINATED.** Tried `max k n → k + n`:
  it fixes §19.6-commuting (`(k+n)+norm α = (k+norm α)+n`) but **breaks `allInv`**, whose principal case
  relies on `max`'s idempotence (`max(max k n₀)n₀ = max k n₀`); under `+` the lingering-duplicate subcase
  produces index `k + 2n₀` (slope 2), forcing the lower bound to need `hardy α (2n) < G n` — a
  *multiplicative* rescaling the additivity lemma does NOT give. So **no single numeric `idx(k,n)` serves
  both** `allInv` (wants idempotence) and §19.6-commuting (wants additive shift). Full analysis:
  `ANALYSIS-…-cutelim-k-threading.md` **ADDENDUM 2**. The `k+n` experiment was reverted (wip stays
  sorry-free). **REVISED RECOMMENDATION = option (1): function/operator-valued `allω` index** (Buchholz
  operator-controlled derivations specialized to PA): each `allω` carries a controlled index *function*
  `g : ℕ → ℕ` (`g n ≤ n + const`), rules compose `g`s (idempotently for `allInv`, post-composing `+norm α`
  for cut-elim). Keeps slope 1, so the proved domination lemmas (`hardy_add_ofNat`,
  `hardy_shift_lt_goodsteinLength`) still apply. Larger refactor of `wip/BoundedZinfty.lean` + `B`/lower
  bound, but it's the only design closing BOTH obstructions. Start fresh-headed; don't half-break wip.
  Lap-7 investigation confirmed M6 domination is STRONG (`hardy_lt_goodsteinLength {α NF} : ∃ N, ∀ m ≥ N,
  hardy α m < G m` — beats `hardy α` at *every* large `m`), so the controlled-`g` lower bound is viable.
  **This is now the hardest-first crux of step 1 — the principal `exI` case is clean; the commuting
  `allω` bounding is the live frontier.** Use `hardy` (`src/Hardy.lean`; `Reaches`/`fundamentalSequence`/
  `hardy_le_of_reaches`/`hardy_monotone` already banked).
- **`norm` ingredient (lap 7): BOTH PROVED + banked, axiom-clean** in `wip/BoundedZinfty.lean`:
  `norm_addAux_le` (head-merge bound) and `norm_add_le {α γ NF} : norm(α+γ) ≤ norm α + norm γ` (the
  `τ(α#β)≤τα+τβ` budget fact). NF is essential — the NF-free version is machine-checked FALSE; the
  eq-merge case is discharged by additive-principality **absorption** (`a + γ = γ` when `repr a <
  ω^(repr e) ≤ repr γ`, via `Ordinal.add_of_omega0_opow_le`). `wip/BoundedZinfty.lean` is **sorry-free**.

---

State after lap 6 (2026-06-22). Build green (`lake build GoodsteinPA`, 1257 jobs). Phase 0 + Phase 1
clean; **M5 (cut-elim) and M6 (Hardy lower bound) both DONE**. Headline stays a literal `sorry`
(anti-fraud). See `PHASE2-DECOMPOSITION.md` for the girder ladder; `ANALYSIS-…-bounding-resolution.md`
§"M4 scoping" for the 5-step connecting spine.

## ✅ LAP-6 — M6 DONE (lower bound self-contained); TOP PRIORITY now = step 1, the `Zᵏ` calculus
`src/GoodsteinPA/LowerBound.lean` (`lowerBound_hardy_selfcontained`) is the full Towsner Thm 17.1 with
no hypotheses beyond `α.NF`, axiom-clean modulo the 🟢 `native_decide` Goodstein base-cases. M5 + M6
are now both complete but **disconnected** (M5 = unbounded `(α,c)` over real `ℒₒᵣ`; M6 = bounded
`(α,k)` over the `GForm` fragment). The connecting spine (hardest-first):

### Step 1 — `Zᵏ`: witness-bounded ω-calculus over real `SyntacticFormula ℒₒᵣ` (Towsner §15)
**DEFINED + §19.2–19.5 DONE** (`wip/BoundedZinfty.lean`, lap 6, all axiom-clean). Chosen design:
**ONote-indexed, B-style (bound-as-parameter, no `⨆`-suprema)** over real `ℒₒᵣ` formulas, with both
`(α,k)` side conditions the lower bound needs (lap-4 finding — cannot be dropped): truth-atom rules
`trueRel`/`trueNrel` (`norm α < k`) + `∃`-witness bound (`exI` carries `n ≤ hardy α k`). Plus a
height-preserving `wk`, a β<α `weak` (raises ordinals in principal inversion cases), `∧`/`∨`/`cut`.
Built: `mono_k`, `mono_c`, `wk`/`weakening`; the **full inversion suite** `orInv`/`andInvL`/`andInvR`/
`allInv` (reshuffle helpers `invPush`/`invPull`/`invPush2`/`inv1Push`/… kept standalone so
`DecidableEq Form` doesn't blow the heartbeat limit inside the big inductions); the **§19.5** ∧/∨
cut-reductions `cutReduceConj`/`cutReduceDisj` (`lt_osucc` + caller-supplied NF upper bound `δ`, result
at `osucc δ` — no natural sum needed).

**NEXT — §19.6 ∀/∃ cut-reduction `cutReduceAllAux`** (the hard, non-invertible one; the witness-bound
survival crux). Port `src/Zinfty.lean`'s measure-style version to parameter-style:
- **Bound framing:** the family `fam : ∀ n, Zk α k c (insert (φ/[nm n]) Γ)`; induct on the ∃-side
  `d : Zk γ k c Δ` with running conclusion bound **`α + γ`** (`ONote.add`; `add_nf` instance gives NF,
  `repr_add` + `Ordinal.add_lt_add_left` give strict monotonicity in `γ` for the premise-`<` conditions).
- **Principal `exI` case** (∃-side introduces `∃⁰∼φ` at witness `n`): cut `fam n` (∀-instance) against
  the ∃-premise on `φ/[nm n]` (complexity `< c`). This is the witness cut.
- The non-principal cases mirror the inversions (reuse the union-reshuffle pattern; src frames the
  running sequent as `Δ.erase (∃⁰∼φ) ∪ Γ`).

**Then `cutElimStep` (§19.7, `c+1→c`, bound `ω^α = oadd α 1 0`) + `cutElim` (§19.9).**

⚠️ **KEY FINDING (lap 6) — the `norm<k` budget does NOT survive ordinal addition; it grows.** `norm`
is `max` over CNF coefficients (`Hardy.lean:637`), and addition MERGES coefficients when leading
exponents coincide: machine-checked `norm ω = 1` but `norm (ω+ω) = norm (ω·2) = 2`. So the naive
"`norm(α+γ) ≤ max`" is **false**; the true bound is additive (`norm(α+γ) ≤ norm α + norm γ`, to verify).
Consequences for the cut-elim design:
- **§19.7 `ω^α` blow-up is SAFE:** `norm (oadd α 1 0) = max (norm α) 1` (machine-checked, `norm_omegaPow`),
  coefficient stays `1` — a pure ω-tower never bumps `norm` beyond `max(norm α, 1)`. So iterating the
  rank-reduction keeps the budget (for `k ≥ 2`).
- **§19.6 within-rank addition is where `norm` grows.** The ω-rule combines premises by *supremum*
  (bound-as-parameter, no sum), NOT addition — so it doesn't bump `norm`. Only the §19.6 cut-combination
  (∀-family `α` + ∃-side `γ`) is an addition, and cut-elim performs finitely many such reductions (cut
  rank `c` finite), so `norm` grows by a *bounded* amount ⇒ choosing `k` large enough at embedding (M4)
  absorbs it. **The precise bookkeeping (how Towsner threads `τ`/`k` through §19; the exact growth bound)
  needs the paper — see `ON-LINE-REQUEST.md`.** Do NOT claim cut-elim closed until this is pinned down.
- Helpers banked this lap: `lt_osucc`, `add_lt_add_left_NF`, `le_add_left_NF`, `norm_omegaPow`. Still
  need (build with §19.6): `norm (α+γ) ≤ norm α + norm γ`, `norm (osucc δ) ≤ norm δ + 1`.
(`Ordinal.nadd`/`♯` absent in mathlib v4.31.0; ordinary `+`/`osucc` with slack, as `src/Zinfty.lean` did
— note natural sum would NOT help here, it merges coefficients the same way.)

### Step 2 — M4 embedding `PA ⊢ φ ⟹ Zᵏ ⊢^{α,k}_c φ`  (UNBLOCKED — independent of the §19.6 τ/k question)
α<ε₀, finite c (Towsner §16/§18). **Reconnaissance done (lap 6).** Foundation's proof object is
`Derivation (𝓢 : Schema L) : Sequent L → Type` in `Foundation/FirstOrder/Basic/Calculus.lean:20`
(`Sequent L = List (SyntacticFormula L)`, one-sided/Tait). Constructors + their `Zᵏ` image (the
embedding inducts on this `Derivation`):
- `axm : φ ∈ 𝓢` — **the PA-axiom case, the crux.** `Zᵏ` must derive each PA axiom at a bounded `(α,k)`:
  Lemma 16.1 (true Δ₀/atomic axioms via the `trueRel`/`trueNrel` rules, low bound) + Cor 16.6 (the
  **induction-scheme** instances at bound `ω·4 # 2rk(φ) # 8` — the real work; `∀`-closure via the
  ω-rule). This is the bulk of M4.
- `axL r v`→`Zk.axL`; `verum`→`Zk.verumR`; `or`→`Zk.orI`; `and`→`Zk.andI`; `wk`→`Zk.wk`;
  `cut`→`Zk.cut` (finitely many cut formulas of bounded complexity ⇒ finite cut rank `c`).
- `all` (eigenvariable `φ.free`) → **`Zk.allω`** (finitary ∀ becomes the ω-rule: derive `φ/[nm n]` for
  every `n`). 2nd deep case: needs **derivation-substitution** — specialize the single eigenvariable
  premise (`φ.free :: Γ⁺`, fresh free var) to each numeral `n` (Foundation `Rew`/free-var substitution
  on a whole `Derivation`). The uniform eigenvariable proof instantiates to all `ℕ`-many ω-rule premises.
- `exs t` (witness *term* `t`) → **`Zk.exI`** with numeral `⟦t⟧ℕ`, needing the **witness bound**
  `⟦t⟧ℕ ≤ hardy α k` (Towsner picks `k` large enough — where the bound is established).
Two wrinkles: (a) Foundation sequents are **`List`**, `Zᵏ` uses **`Finset`** — need a list→finset bridge.
(b) Confirm how `𝗣𝗔 ⊢ ↑goodsteinSentence` (the headline's `LO.Entailment`) connects to `Derivation
𝗣𝗔-schema` (the `OneSided` instance at `Calculus.lean:31` is `Derivation`). The structural map is
clean — the depth is all in `axm`. Foundation-heavy; not Aristotle-friendly.

### Step 3 — cut-elim with `k`
Redo `src/Zinfty.lean` §19 tracking the witness bound. The inversions/reductions *strategy* ports; the
new content is threading `h_{ω^α}(k)` through §19.6 (∀/∃ reduction) and confirming `ω^α < ε₀` keeps the
final cut-free bound `< ε₀` (so domination still bites). No deep math doubt (literature-standard,
host-verified) — formalization labor.

### Step 4 — subformula bridge (the clean small connector)
A cut-free `Zᵏ`-derivation of `{gAll}` contains only subformulas of `gAll` closed under numeral
substitution = exactly `{gAll, gEx n, atom m n}` = the `GForm` fragment, so it **is** a `B`-derivation
⇒ `lowerBound_hardy_selfcontained` refutes it. Needs: a subformula-closure lemma for the ω-calculus
(structural induction over `Deriv`, ω-rule = closure under numeral substitution) + the `GForm ↪ ℒₒᵣ`
encoding identification. Reuses M6 as-is.

### M7a — the language gap (the other hard girder; Towsner Remark 10.3)
`goodsteinSentence = ∀⁰ (codeOfREPred goodsteinTerminates)` is an **opaque Σ₁ blob**, NOT the
transparent `∀x∃y g_y(x)=0` that step 4 needs. Build a transparent Π₂ `gAllReal` (arithmetize
`goodsteinSeq` as a real `ℒₒᵣ` formula — Foundation's Σ₁/representability tools) and prove
`𝗣𝗔 ⊢ goodsteinSentence ↔ gAllReal`, gated by `Bridge.lean`'s spec so faithfulness can't regress.
Then the subformula bridge runs on `gAllReal`.

## ✅ LAP-5 — O0 done + the I∀ frontier RESOLVED; TOP PRIORITY is now O0′ (port `Hdom`)
The witness-bounded calculus `B` is now built over `ONote` with the **concrete** Hardy hierarchy
(`src/GoodsteinPA/Hardy.lean`, ported from Track-1). `wip/LowerBoundHardy.lean` proves, axiom-clean:
the ∃-fragment lower bound (`lowerBound_existential_hardy`, zero abstract hyps), `k`-monotonicity,
**∀-inversion** (`B.allInv`), and the **full Thm 17.1 modulo domination** (`lowerBound_hardy`). The
lap-4 "accumulating existentials" wall is resolved by inverting `gAll` away rather than carrying it
(see `ANALYSIS-2026-06-22-bounding-resolution.md`).

### O0′ (TOP) — discharge `Hdom : ∃ x, hardy α (max k x) < G x`
`G = goodsteinLength`; Goodstein defs (`bump`/`base`/`goodsteinSeq`) are **byte-identical** to Track-1.
Port `~/src/lean-formalizations Logic/Goodstein/{Length,Domination,DominationOmega,TowerDomination,
GrowthStatement,DominationCorollary,GoodsteinLike,DominationBaseCases}.lean` →
`goodsteinLength_dominates_fastGrowing {o}(ho:o.NF) : ∃ N, ∀ m≥N, fastGrowing o m ≤ goodsteinLength m+2`.
Chain `hardy α m ≤ fastGrowing α m` (`hardy_le_fastGrowing`) + identify `G = goodsteinLength`. **Bridge
the `+2` to strict `<`** (the one genuinely-open bit; fastGrowing's gap over hardy swallows +2 for
large m — good Aristotle target). Then `lowerBound_hardy` becomes a self-contained Thm 17.1. NB the
port carries documented `native_decide` finite-base-case axioms.

<details><summary>Superseded lap-4 O0 (re-architect on the witness-bounded calculus) — DONE</summary>

## ⚠️ TOP PRIORITY (lap 4) — O0: re-architect on the witness-bounded calculus
**Finding (machine-checked, axiom-clean, `wip/WitnessBound.lean`):** the completed M5 cut-elimination
in `src/Zinfty.lean` is for a calculus with an **unbounded `∃`-witness** and **no numeric index `k`**.
That calculus cannot reach the headline — `unbounded_proves_goodstein` derives the Goodstein sentence
cut-free at ordinal 2, so Towsner's lower bound (17.1) is FALSE for it. The headline needs the
**witness-bounded, Hardy-indexed `(α,k)` calculus** (Towsner §15), where `∃` carries `v ≤ h α k`,
`True` carries `τ α < k`, and `∀`'s premises use `max k n`. See `STATUS.md` lap-4 finding.

Attack paths (hardest-first; the crux is now the lower bound + the `k`-tracking cut-elim):
1. **Finish the lower bound (M6 / Thm 17.1).** `wip/WitnessBound.lean` has the calculus `B` and the
   `∀`-free fragment proved (`lowerBound_existential`). The remaining frontier is the `gAll`/`I∀`
   case with *accumulating* existentials — Towsner's stated invariant looks insufficient there
   (see `ON-LINE-REQUEST.md`). Either crack the refined invariant (likely a single-ordinal
   `H`-controlled measure, Buchholz style) or get it from the literature, then discharge the abstract
   Hardy hypotheses `Hmono`/`Hdom`/`HG` from a real `h_α`/`τ`/`G` (mathlib `ONote.fastGrowing`?).
2. **Retrofit `k` into cut-elimination.** Redo `src/Zinfty.lean`'s inversions/reductions tracking the
   numeric bound `k` (the *strategy* ports; only the bookkeeping changes). Needed so the cut-free
   output of M5 still carries the `(α,k)` bound that 17.1 refutes.
3. **Decide architecture:** Towsner two-index `(α,k)` vs. Buchholz single-ordinal `H`-controlled
   derivations. The latter may formalize more cleanly (one well-founded measure, standard boundedness
   theorem). Resolve via `ON-LINE-REQUEST.md` before sinking the cut-elim redo.

Plus the **PA↔PA⁺ language gap**: our headline is real-`ℒₒᵣ` PA with an opaque Σ₁ `goodsteinSentence`,
not Towsner's extended-language `∀x∃y g_y(x)=0`; the arithmetization bridge Towsner skips (Remark
10.3) is a separate deep girder (M7-adjacent). Route A (via `Con(PA)`, O1) stays entirely in real PA
and sidesteps this — re-evaluate Route A vs Route B in light of the language gap.
</details>

## Open obligations (toward a clean headline)

### O1 — `Reduction.goodstein_implies_consistency` (Route A girder) — `sorry`
`𝗣𝗔 ⊢ γ → 𝗣𝗔 ⊢ Con(𝗣𝗔)`. The deep ordinal-analysis content via Con(PA).
Attack paths:
1. **Gentzen `TI(ε₀) ⊢ Con(𝗣𝗔)` + `γ ⟹ TI(ε₀)`** — the classic route; needs `PA_∞`
   cut-elimination (same `Z_∞` machinery as Route B) plus the Con(PA) lower bound. Reuses
   Foundation's Gödel II downstream. (Buchholz `on-gentzens-first-consistency-proof`.)
2. **Drop Route A entirely for Route B** (recommended) — Towsner shows `𝗣𝗔 ⊬ γ` directly without
   Con(PA); then `goodstein_implies_consistency` becomes unnecessary (leave it as a documented,
   never-used alternative). The headline is discharged via O2's chain instead.
3. Partial: keep the lemma but prove the *easier* converse direction / a weaker reflection
   principle first as warmup, to exercise Foundation's provability API (`⊢`, `Con`, D1–D3).

### O2 — the Phase-2 girder (Route B, Towsner) — milestones M3…M7 in `PHASE2-DECOMPOSITION.md`

**✅ M3 (Z_∞ calculus) + M5 (cut-elimination) COMPLETE & axiom-clean** in
`src/GoodsteinPA/Zinfty.lean` (promoted from `wip/`, 0 sorries, `#print axioms` = trust base only,
2026-06-22 lap 3). The whole Towsner §19 is machine-checked: inversions 19.2–19.4, cut reductions
19.5 (`cutReduceConj/Disj`) + 19.6 (`cutReduceAll`), atomic/⊥ cuts (`atomCut`/`removeFalsum`, **no
truth layer needed** — set sequents dissolve them), `cutElimStep` (19.7), `cutElim` (19.9). Key
findings: `Ordinal.nadd` ABSENT in mathlib v4.31.0 → ordinary `+` with `+1` slack (bounded below
`ω^(·+1)` by additive principality); the Hardy `k` index was NOT needed for cut-elim (pure Schütte
`(α,c)` suffices — it's a §17 device); `exI` restricted to numeral witnesses.

**NEXT (hardest-first): M4 — the embedding `PA⁺ ↪ Z_∞`** (Towsner §16 Thm 16.7 / §18 Thm 18.1). A
`PA⁺` proof of `φ` yields `∃ α<ε₀, ∃ k c, Z_∞ ⊢^{α}_c φ`, finite `c` (finitely many induction
instances ⇒ finitely many finite-rank cuts — the hinge of the whole argument). Sub-targets:
M4.1 (Lemma 16.1, true universal sentences derivable at finite bound), M4.2 (Lemma 16.5/Cor 16.6,
induction axioms at bound `ω·4 # 2rk(φ) # 8`), M4.3 (Thm 16.7, induct over a Hilbert-style proof;
reuse Foundation's finitary `Derivation`, map `∀`→ω-rule). M6 (Hardy lower bound, §17) is
**independent and parallelizable** (M6.1–M6.3 overlap Track 1 `Logic/FastGrowing`; M6.4 = Thm 17.1
is new and likely DOES need the Hardy `k` threaded through a cut-free `Provable₀`).

<details><summary>Superseded lap-2 status (M5 was one open leaf `cutElimStep`)</summary>
Done and **machine-checked** (`lake env lean wip/ZinftyF.lean`, only `cutElimStep` sorry):
- The `Z_∞` calculus `inductive Deriv` over `SyntacticFormula ℒₒᵣ`, **Finset sequents** (set-based,
  per Towsner ⇒ contraction is FREE, no `contr` rule), ω-rule `allω`, ordinal bound `o`, `ℕ∞`
  cut rank `cr`. The `ℕ∞/⊤` blocker is **gone**: `complexity : Form → ℕ` is finite.
- Full predicate-level inference API: `axL/verumR/andI/orI/exI/allω/cut/mono/weakening/cast`,
  contraction free.
- **All three inversion lemmas PROVED** (the syntactic content of cut-elimination):
  `orInvAux`/`Provable.orInv` (§19.2 ∨), `andInvAux`/`Provable.andInvL`/`.andInvR` (§19.3 ∧),
  `allInvAux`/`Provable.allInv` (§19.4 ω/∀). Each by structural induction on `Deriv`, all 8 cases,
  preserving ordinal bound and cut rank.
- `cutElim` (Thm 19.9) reduced to the single open leaf `cutElimStep` (Thm 19.7).

**NEXT (hardest-first): the cut-REDUCTION lemma (Towsner §19.5–19.7), the ordinal-arithmetic
heart of `cutElimStep`.** With all inversions in hand, the reduction lemma is: a top-level cut on a
formula of complexity `= c` between two `Provable _ c` derivations can be replaced by a cut-free-at-
rank-`c` derivation with the ordinal bounds *added* (not `max+1`). The principal-formula reduction
uses the inversions to push the cut to the immediate subformulas (∨/∧ → smaller-complexity cut;
ω/∀ → instantiate at the ∃-witness numeral). Then `cutElimStep` does the transfinite induction over
the derivation eliminating all rank-`c` cuts, raising `α ↦ ω^α`. Likely needs a numeric/Hardy `k`
parameter re-added to `Provable` (Towsner threads `h_{ω^α}(k)` through 19.6/19.7) — assess whether
the `(α,c)` indexing suffices first.

Attack paths:
1. **Continue the `wip/Zinfty.lean` prototype** (E2 encoding — *compiles*). Next: (a) connect
   `AForm` to a faithful arithmetic formula with a real free-variable/substitution layer (replace
   the `ℕ → AForm` family with a single body + numeral substitution), so `rk` is genuinely
   finite; (b) state M3.3 bound-monotonicity lemmas; (c) state M4 embedding + M5 cut-elimination
   theorems as disclosed `sorry`s. Bank each as it typechecks; promote to `src/` when green.
2. **Develop M6 (Hardy domination) via Track 1.** `~/src/lean-formalizations` `Logic/FastGrowing`
   is building `h_α`, monotonicity, and Goodstein-length domination on mathlib's
   `ONote.fastGrowing`. Reuse those for M6.1–M6.3; only M6.4 (Thm 17.1, the cut-free lower bound)
   is new here. (Does NOT block M3–M5 — parallelizable.)
3. **Tackle cut-elimination (M5) on the prototype first**, before the embedding — it is the
   self-contained heart (Towsner §19). **STATUS: M5 is now structured down to ONE leaf.**
   `wip/Zinfty.lean` has `Provable.cutElim` (Thm 19.9, full elimination) *proved* by induction on
   cut rank, reducing entirely to the single open lemma **`Provable.cutElimStep`** (Thm 19.7, one
   level). So the next concrete target is exactly `cutElimStep` = §19 inversions 19.2–19.4 +
   reductions 19.5–19.6 + the principal-`Cut`-on-rank-`c` case. Proving it makes the whole
   cut-elimination machine-checked (mod the embedding M4 and lower bound M6.4). NOTE: `cutElimStep`
   likely needs the numeric/Hardy `k` bound that `Provable` currently elides — re-add a `k : ℕ`
   index to `Provable`/`Deriv.o` first (it threads the `h_{ω^α}(k)` bound through 19.6/19.7).
   *(Resolved lap 3: the `k` index turned out NOT to be needed for cut-elimination.)*
</details>

### O2′ — M4 DESIGN DECISION (scouted lap 3, execute lap 4) ⭐
The embedding needs Z_∞ to derive PA's **true defining axioms** (e.g. `n+(m+1)=(n+m)+1`), which the
current calculus CANNOT: `axL` is the clash-based identity (`rel r v ∧ nrel r v ∈ Γ`) and `verumR`
is only `⊤`. Towsner's "True" rule is a **truth-based atomic axiom**. So M4 requires extending the
calculus. Concrete plan:
1. **Atomic truth predicate** — reuse Foundation `Semiformula.Evalm ℕ` (the `standardModel`
   instance for `ℒₒᵣ` over `ℕ`; `=`/`<` decidable). For embedding-substituted formulas (free vars
   replaced by numerals) truth is assignment-independent. **VALIDATED (lap 3)** — this typechecks
   (imports `Foundation.FirstOrder.Arithmetic.Basic.Model`):
   ```
   noncomputable def atomTrue (φ : SyntacticFormula ℒₒᵣ) : Prop :=
     Semiformula.Evalm ℕ (fun _ => 0) (fun _ => 0) φ
   ```
   (`Foundation/.../Semantics/Semantics.lean:241`, `Arithmetic/Basic/Model.lean:25`.)
2. **Add `trueAtom` constructor** to `Deriv`: `(φ : Form) → (φ atomic) → Evalm ℕ … φ → φ ∈ Γ →
   Deriv Γ`, with `o = 0`, `cr = 0`. ⚠️ **This touches the completed cut-elimination**: every
   induction (`orInvAux`, `allInvAux`, `andInvAux`, `cutReduceAllAux`, `atomCutAux`,
   `removeFalsumAux`, `cutElimStepAux`) gains one new leaf case — mostly trivial (like `verumR`),
   EXCEPT `atomCutAux`: a `trueAtom` on the cut atom `rel r v` means `rel r v` is true ⇒ `nrel r v`
   is false ⇒ must remove it from the other premise. So `atomCut` needs a **truth-based false-atomic
   removal** (the genuine §19.2 content, now unavoidable, but only for atomics — decidable ℕ
   arithmetic). Do this extension on a `wip/` copy first; re-green; re-promote.
3. **ε₀** is `ε_ 0` in `Mathlib.SetTheory.Ordinal.Veblen` (first fixed point of `ω^·`); `omegaTower
   c α < ε₀` for `α < ε₀` is the closure fact M5.4/M7 need (ε₀ closed under `ω^·`).
4. Then M4.1 (Lemma 16.1) → M4.2 (Cor 16.6) → M4.3 (Thm 16.7), inducting over a `Peano`-proof
   (`𝗣𝗔⁻ + InductionScheme ℒₒᵣ Set.univ`), reusing Foundation's finitary `Derivation`.

**Caveat on the clean state:** cut-elimination is currently truth-free and axiom-clean precisely
because of clash-`axL`. Adding `trueAtom` re-introduces a (decidable, atomic-only) truth layer.
This is the standard Schütte setup and is correct; just do it carefully so the §19 proofs stay green.

### O3 — `PA_delta1Definable : 𝗣𝗔.Δ₁` (Foundation axiom) — only on Route A
Needed to *state* Gödel II for `𝗣𝗔`; Foundation axiomatizes it (TODO in
`Incompleteness/Examples.lean`). Route B avoids it. Attack paths:
1. **Avoid** — go Route B (O1 path 2); the axiom never enters the headline profile.
2. Discharge it: construct the Δ₁-definition of PA's axiom set (PA⁻ + induction scheme) in
   Foundation's `Theory.Δ₁` framework and prove `isDelta1`. Deep arithmetization; multi-lap.
3. Upstream: check whether a newer Foundation rev proves it (the TODO may get filled upstream);
   file an `ON-LINE-REQUEST.md` to check the latest Foundation `Incompleteness/Examples.lean`.

**UPDATE (lap 6, cross-session news):** a separate session (`~/src/Foundation-delta1-burndown`,
branch `feat/induction-scheme-delta1`) is **actively discharging** both `PA_delta1Definable` and
`ISigma1_delta1Definable` (proving them in `InductionSchemeDelta1.lean`; reduced `PA.Δ₁` to 3 isolated
obligations, build green, ~1–2 laps to PA-complete per that session). So path 3 is in progress
**upstream** — do NOT duplicate it here. When it lands and our Foundation pin bumps to include it,
Route A's `not_proves_of_implies_consistency` becomes axiom-clean (no `PA_delta1Definable`). This is a
**fallback de-risk only**: our headline stays on **Route B** (Towsner direct, avoids `Con(PA)` and this
axiom). `goodstein_implies_consistency` (the `TI(ε₀)⊢Con(PA)`-inside-PA girder of Route A) remains
deeply blocked regardless, so the Δ₁ news doesn't make Route A the preferred path.

## Done — lap 4 (2026-06-22)
- **Witness-bound architectural finding** (machine-checked, axiom-clean, `wip/WitnessBound.lean`):
  the `src/Zinfty.lean` `(α,c)` cut-elimination is OFF the headline path (its unbounded `∃` makes the
  lower bound false). Built the corrected witness-bounded calculus `B`; proved the existential-fragment
  lower bound (`lowerBound_existential[_real]`) grounded against the real `G`; decomposed the full
  Thm 17.1 to the single `bounding` frontier (`True`/`W`/`I∃` cases machine-verified via `sat_mono_ord`,
  `I∀` case the literature-gated frontier; `lowerBound` contradiction-extraction real). Goodstein-side
  grounded: `G`, `goodstein_zero_succ`/`_mono`, `atomTrue_iff_G_le`. Filed `ON-LINE-REQUEST.md` for the
  rigorous `bounding` invariant + architecture (Towsner `(α,k)` vs Buchholz `H`-controlled).
- Next deep brick (architecture-independent, but gated on the notation/architecture decision):
  the **Hardy / fast-growing hierarchy + τ-controlled monotonicity** to discharge `Hmono`/`Hmono_n`,
  and **Goodstein domination** (Towsner §5–§9) to discharge `Hdom`. mathlib `ONote.fastGrowing`
  exists but has NO growth lemmas (deliberately minimal).
  - **STARTED** (`wip/FastGrowing.lean`, axiom-clean): `fastGrowing_id_le` — `n ≤ fastGrowing o n`
    (the inflationary half, which IS separable from ordinal-monotonicity: successor case via
    iterating a `≥id` map, limit case via the smaller-ordinal IH).
  - **Confirmed entangled:** *numeric* monotonicity (`Hmono_n` analogue) of `fastGrowing` — its
    limit case `fastGrowing (f m) m ≤ fastGrowing (f m') m` needs *ordinal* monotonicity at fixed `n`,
    which is the τ-subtle one (false for small `n` without the coefficient control — Towsner §8). So
    `Hmono`/`Hmono_n` for the real hierarchy genuinely need the τ machinery; not a quick brick.

## Done — lap 1
- M1: `Encoding.goodsteinTerminates_re` proved (`Computability.lean`: `primrec_natLog`,
  `primrec_bump`, `primrec_goodsteinSeq`). Phase 0 axiom-clean.
- M2: `Reduction.lean` — Gödel II hook + meta-reduction (axiom-clean mod `PA_delta1Definable`).
- Phase 2: `PHASE2-DECOMPOSITION.md` (Towsner-grounded ladder) + `wip/Zinfty.lean` (E2 encoding
  prototype — compiles: ω-rule inductive, ordinal/cut-rank measures, bound-domination lemma,
  `Provable.mono`/`.weakening`, and the **proved predicate-level inference API** `Provable.orI`,
  `.exI`, `.allI` — the ω-rule with the supremum ordinal bound, machine-checked against the
  `Deriv` measures via `Classical.choice`).

## ⭐ KEY FINDING (2026-06-22, end of lap) — build `Z_∞` ON Foundation's Tait calculus
Foundation **already has a finitary Tait one-sided FO sequent calculus**:
`FirstOrder/Basic/Calculus.lean` — `inductive Derivation (𝓢 : Schema L) : Sequent L → Type`
with constructors `axL, verum, or, and, all, exs, wk, cut` and a `height` measure, over the *real*
`SyntacticFormula ℒₒᵣ` (which already carries free variables, substitution, negation, rank).
Plus `FirstOrder/Hauptsatz.lean` (finitary cut-elimination). **There is NO infinitary calculus /
ω-rule / `PA_∞`** (confirmed by grep — only finitary Tait + Hauptsatz).

**Consequence — revise M3.1:** do NOT continue the standalone `wip/Zinfty.lean` `AForm`. Instead
define `Z_∞` as a new inductive **over Foundation's `SyntacticFormula ℒₒᵣ`/`Sequent`**, replacing
the finitary `all` (eigenvariable, one premise, `ℕ` height) with the **ω-rule** (`all` taking an
`ℕ`-indexed family `n ↦ φ[x ↦ numeral n]`, `Ordinal` height). This:
- **kills the `AForm` substitution-layer prerequisite** — Foundation's formula substitution +
  `rk` are reused, so `rk φ` is already finite and `cut`/`cutElimStep` become directly stateable;
- **shrinks M4 (embedding):** a PA proof already yields a Foundation *finitary* `Derivation`
  (via Hauptsatz machinery); M4 becomes "finitary `Derivation` ↪ `Z_∞`" (map each rule across,
  ∀→ω-rule) instead of re-deriving from `True`/`Lemma 16.1` by hand;
- **makes M7 natural:** everything is over real `ℒₒᵣ` formulas, so connecting to our
  `goodsteinSentence` is a formula-level statement, not a re-encoding.
The `wip/Zinfty.lean` prototype keeps its value as the *proof that the ordinal/ω-rule measures
work* (the encoding-feasibility result) — port its `o`/`cr`/`allI`/`cutElim` skeleton onto
Foundation's `Derivation`-shaped inductive. **This is the recommended first action next lap**
(read `FirstOrder/Basic/Calculus.lean` + `Hauptsatz.lean` first).

## Design note — `Provable.cut` + the `ℕ∞` cut-rank (next lap, read before refactoring)
`cr : Deriv Γ → ℕ∞` (cut rank can be `⊤` for pathological infinite families). A predicate-level
`Provable.cut` is the one rule still missing: from `Provable α c (φ ::ₘ Γ)` and
`Provable β c (φ.neg ::ₘ Γ)` it should give `Provable (max α β + 1) c' (Γ)` where
`c' ≥ rk φ + 1`. But `rk φ : ℕ∞` may be `⊤`, so you can't pick a finite `c' : ℕ` in general —
`Provable`'s `c : ℕ`. **Fix:** when `AForm` gets the real free-variable + numeral-substitution
layer (the M3.1 refinement), `rk φ` becomes provably finite (`rk φ ≠ ⊤`) for genuine formulas, so
`Provable.cut` and the Hardy-bounded `cutElimStep` both become stateable with finite `c`. So the
substitution-layer refactor is a prerequisite for *both* `cut` and `cutElimStep` — do it first.

## Gotcha noted (for the corpus)
For `Ordinal`, `add_le_add_right h c` elaborates to `c + a ≤ c + b` (adds on the *left*) — use
`add_le_add h le_rfl` to get `a + 1 ≤ b + 1` from `a ≤ b`. `gcongr` on `⨆`-bounds spawns a
`BddAbove (Set.range …)` side-goal (discharge with `Ordinal.bddAbove_range`).
