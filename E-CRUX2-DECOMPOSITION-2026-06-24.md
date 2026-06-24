# E — Crux-2 decomposition: turning eq-(5) into a punch-list (judge, 2026-06-24)

> **VALIDATE, don't trust.** Source-grounded (Buchholz [6] §§3–5 read in full from the PDF). Goal per the
> operator: break the one genuinely-hard remaining piece (crux-2, the Gentzen reduction descent) into
> ordered, citation-backed, Lean-shaped sub-lemmas — most of them low-hanging — so the forward-grinder can
> plow. **The single most useful thing in this doc:** the difficulty is NOT spread across "step 2 (iR) +
> step 4 (C3)". It is concentrated in **ONE reduction case (5.1, the critical/cut-elimination case)**, and
> that case is **gated behind two prerequisites (Lemma 3.1 + Theorem 3.4) the current plan omits.**
> Everything else is õ-bookkeeping the box already has the algebra for.

Maps onto the box's own objects (`idg`/`iõ`/`iord` = Buchholz `dg`/`õ`/`o`; `ZDerivation`/`z*` codes;
`iR` = `d↦d[0]`) and its extraction `CRUX2-ORD-ASSIGNMENT-2026-06-24.md`. Citations are to
`papers/buchholz-on-gentzens-first-consistency-proof.pdf` unless noted.

## 0. The one insight that reorders the whole attack
Buchholz `o(d) = ω_{dg(d)}(õ(d))`, a tower of height `dg(d)` over pre-ordinal `õ(d)`. The descent
`o(d[n]) < o(d)` (Thm 4.2) splits, via Lemma 4.1, into two regimes:
- **Non-critical / structural cases** (atomic, I∀, I¬, Ind, chain-non-critical): `dg` does **not rise** and
  `õ` **strictly drops** — pure natural-sum (`#`) order bookkeeping. The box's F1–F4 + tower lemmas already
  discharge these. **LOW-HANGING.**
- **The ONE critical case (5.1)** — a `R_A`/`L^k_A` redex is eliminated: here `õ` may *jump up* to `< ω^{õ(d)}`,
  and the descent survives **only because `dg` strictly drops by 1**. This degree-drop IS cut-elimination,
  and it is the only place the tower height falls. **THE NUT.** It needs `rk(A(d)) < dg(d)` — which is *not*
  free; it comes from Theorem 3.4, which needs Lemma 3.1.

⟹ **Reordered plan:** build objects → plow the LOW-HANGING descent cases first (they validate the engine and
are cheap) → then the two prerequisites → then the nut → then Thm 4.2 (a 3-line tower combine) → bridge.

## 1. Dependency tree (hardest isolated)
```
C0   ZDerivation : V→Prop            (Fixpoint over z* codes)         ← box step 1, START
C0'  iR : V→V  (= d↦d[0]) SKELETON   (Def 3.2 dispatch on zTag)       ← box step 2, but see §3
 ├─ L3.1  critical-pair existence    (Lemma 3.1)            ◄ PREREQ, currently UNLISTED
 ├─ T3.4  rk(A(d)) < r + d{0}/d{1}   (Theorem 3.4)          ◄ PREREQ, currently UNLISTED
C3a  Lemma 4.1 — LOW-HANGING cases   (atomic,I∀,I¬,Ind,5.2) ← do FIRST, cheap, validates engine
C3b  Lemma 4.1(b)(ii) — case 5.1     (the cut-elim nut)     ← THE NUT, needs L3.1+T3.4
C3c  Theorem 4.2                     (tower combine)         ← ~3 lines given C3a+C3b + tower mono
C0.5 Foundation→Z bridge             (PA-⊥-proof → Z-⊥-deriv)← parallel; Bryce–Goré Peano.v blueprint
C4   isNF/≠0 of iord on ⊥-derivs     (feeds gentzenDescentφ_realized)
C5   assembly: gentzenDescentφ, d₀    (least ⊥-proof via C0.5)
```

## 2. The LOW-HANGING punch-list (plow these right after objects exist)
Each is a one-case fragment of Lemma 4.1; state it as `idg (iR d) ≤ idg d ∧ icmp (iõ (iR d)) (iõ d) = 0`
for the relevant `zTag d`, then `iord`-combine via the tower. Order of increasing effort:

| # | Buchholz case | `d[n]` is | Descent obligation | Discharged by | Effort |
|---|---|---|---|---|---|
| LH1 | **case 3 (I¬)** `d=I_{¬A}d₀` | `d[0]=d₀` | `õ(d₀) < õ(d₀)+1`, `dg` eq | `self_lt_iadd_one` | trivial |
| LH2 | **case 2 (I∀)** `d=I^a_{∀xF}d₀` | `d[n]=d₀(a/n)` | same; uses `õ(d(a/t))=õ(d)` (Remark p.10) | + the substitution-invariance remark | trivial |
| LH3 | **case 5.2.2** (chain, `dᵢ` non-crit) | `d[n]=K^r(i/dᵢ[n])` | one summand `ω^{õ(dᵢ)}↦ω^{õ(dᵢ[n])}` drops, `#` rest fixed | **F1** (left-cancel/mono) + IH(a) | low |
| LH4 | **case 4 (Ind)** `d=Ind^{a,k}_F d₀d₁` | `d[0]=K^r d₀ d₁(0)…d₁(k−1)` | `õ(d[0]) = ω^{õ(d₀)} # (k copies of ω^{õ(d₁)}) < ω^{õ(d₀)} # ω^{õ(d₁)+1} = õ(d)` | **F3** (`ω^β·k ≺ ω^{β+1}`) | low-med |
| LH5 | **case 5.2.1** (chain, `dᵢ` crit) | `d[0]=K^{r'}(i/dᵢ{0},dᵢ{1})` | descent by IH(b)(i) on `dᵢ{0}`,`dᵢ{1}`; `#` two summands below one | **F1+F2** + IH(b)(i) | med |

LH1–LH3 should each be ~one lap. **Doing these first is high-value:** they exercise `ZDerivation`/`iR` end-to-end
on the easy rules, so when you hit the nut the machinery is already debugged. (This is the box's own
"objects-first" instinct, pushed one level further: *easy-descent-cases* before the hard one.)

## 3. PREREQUISITES the current plan omits (build before the nut)
The plan jumps `iR` → "per-rule C3". But the critical case's descent (`rk(A(d)) < dg(d)`) is **not provable
from the assignment alone** — it is a theorem about the reduction:

- **L3.1 — Lemma 3.1 (critical-pair existence), p.8.** In a chain inference whose succedent is false-minimal,
  among the premises' inference symbols there exist `i<j` with `Iᵢ = R_{Aᵢ}`, `I_j = L^k_{Aᵢ}`, `0 < rk(Aᵢ)`.
  This is what makes `tp(d)` well-defined in the critical branch and identifies the redex `iR` eliminates.
  *Lean shape:* a `Σ₁` search over the (coded) premise list returning the least such `(i,j,k)`; pure
  combinatorics on `zTag`/inference-symbol codes, **no ordinals**. Order-induction on the premise index.
  *Effort:* medium, self-contained. **This is genuinely low-hanging and unblocks the nut — do it early.**
- **T3.4 — Theorem 3.4(a), p.9.** For critical `d = K^r…`: the auxiliary derivations satisfy
  `d{0} ⊢ Π·A(d)`, `d{1} ⊢ A(d),Π`, **and `rk(A(d)) < r`.** The rank bound is the linchpin of the degree-drop.
  *Lean shape:* `ZDerivation d → critical d → ... ∧ rk (zCutFormula d) < zRank d`. Proof is structural
  (the redex formula's rank is bounded by the chain-rule rank). *Effort:* medium; depends on L3.1.

**Add L3.1 and T3.4 as explicit milestones between `iR` and the critical-case C3.** Without them, C3b cannot
even be *stated* truthfully (it would have to assume `rk(A(d)) < dg(d)` as a hypothesis — a hidden gap).

## 4. THE NUT — Lemma 4.1(b)(ii), case 5.1 (cut-elimination), p.11
`d = K^r_Π d₀…d_l` critical, redex `(i,j,k)` from L3.1; `d[0] = K^{r−1}_Π d{0} d{1}` where `d{0}`,`d{1}` are
the auxiliary derivations from T3.4. Three obligations:
1. **`dg(d[0]) < dg(d)`** — the degree strictly drops. Buchholz: `dg(d[0]) = max{dg(d{0})−1, dg(d{1})−1, r−1}`,
   and by IH(b)(i) `dg(d{ν}) ≤ dg(d)`, plus `rk(A(d)) < r ≤ dg(d)` (T3.4) ⟹ each component `< dg(d)`.
   **This is the cut-elimination heart — the only degree-drop in the whole proof.**
2. **`õ(d[0]) < ω^{õ(d)}`** — pre-ordinal stays below one ω-power of `õ(d)`. From IH(b)(i)
   `õ(d{ν}) < õ(d)` and `õ(d[0]) = ω^{õ(d{0})} # ω^{õ(d{1})} < ω^{õ(d)}` via **F2** (two powers below one).
3. **`rk(A(d)) < dg(d)`** — directly T3.4 + `r ≤ dg(d)`.
Then Thm 4.2: `o(d[0]) = ω_{dg(d[0])}(õ(d[0])) < ω_{dg(d[0])}(ω^{õ(d)}) ≤ ω_{dg(d)}(õ(d)) = o(d)` — the
*degree-drop* (1) absorbs the *pre-ordinal jump* (2) through the tower (`ω_{m}(ω^α) = ω_{m+1}(α) ≤ ω_{m+1+…}`).
**The order-fact `ω_m(ω^α) ≤ ω_{m+1}(α)` is the one tower lemma to confirm exists** (`icmp_iotower_lt_succ_of_le`
looks like it — VALIDATE it gives exactly this).

The genuine work in the nut is **constructing `d{0}`/`d{1}` as `ZDerivation`s** (nested chain rules, Buchholz
14.253 / 3.2(5.1)) and the IH plumbing — *not* the ordinal inequality, which is two F-lemmas + a tower step.
So even the nut is mostly the **object construction** `iR`-critical-branch, which is C0'/T3.4 work, with a
short ordinal tail.

## 5. C0.5 bridge — sub-decomposition (Foundation-PA-⊥ → Z-⊥), parallelizable
`Z ⊇ PA` on closed sequents: discharge each PA axiom in Z + simulate each Foundation rule, composing to
`𝗣𝗔.DerivationOf d ⊥ → ∃ z, ZDerivesEmpty z` (M-internal). Independent of §§3–4 — run in a worktree.

**Bryce–Goré `Peano.v` skeleton (the worked PA→infinitary analogue, extracted from the Coq source):** their
bridge `PA_Base_closed_PA_omega` is `PA_Base → (annotate degree+ordinal) PA_Implication → (per-constructor)
PA_ω`, where — logical/equality/arithmetic axioms → short target derivations (easy); **MP → a cut** (the
cut-formula's complexity *becomes* the new cut-degree — this is *why* a reduction is then needed);
**generalization → the quantifier/ω rule**; the bridge carries a structurally-computed `(degree, ordinal<ε₀)`,
no closed-form bound.

**⭐ JUDGE REFINEMENT — the bridge is CHEAPER for Buchholz-Z than my earlier ~1215-line flag.** Bryce–Goré's
`Peano.v` is *dominated by one sub-tower: unfolding PA's induction axiom into the ω-rule* (`inductive_chain` →
`induction_iterate_general` → `induction_terminate` → `induction_final` — roughly half the file). **You do not
pay that.** Buchholz-Z has a *native* complete-induction rule (`Ind`, §2/§3), so PA's induction axiom maps to
Z's `Ind` rule **directly** — the most expensive part of their bridge is *free* in yours. Net: revise C0.5
**down to well under 1k lines.**
- **B1** PA logical+equality+arithmetic axioms → Z atomic axioms `Ax(Z)` (Buchholz §5). Easy.
- **B2** Foundation Tait+cut rules → Z: `cutRule` → Z chain rule `K^r`; `∀`/generalization → Z `I^a_∀`;
  **the PA-induction `axm` schema → Z's native `Ind` rule (direct — NOT an ω-unfolding).** This is the whole
  payoff of choosing Z over PA_ω (lap-58 call, now cost-quantified).
- **B3** compose, M-internally (Σ₁ / per-model): `𝗣𝗔.DerivationOf d ⊥ → ∃ z, ZDerivesEmpty z`.

**Do NOT port Bryce–Goré's `cut_elim.v`.** Their consistency core is *infinitary transfinite recursion* over
ε₀ (`transfinite_induction` on `nf` ordinals) + a "dangerous-disjunct" argument → META-level Con(PA) — **not**
the *primrec* reduction your PRWO route needs. Only `Peano.v` (the bridge) transfers; the descent stays
Buchholz §§3–4 (this doc §§2–4), the finitary primrec `R`. (Independently re-confirms the lap-58 Z-over-PA_ω
call: their core diverges exactly where the primrec requirement bites.)

## 6. Literature map (which paper in `papers/` decomposes each piece further)
The box is offline but `papers/` is in-repo — point each hard node at its richest secondary source:
- **The nut (5.1) / cut-elim:** `buchholz-beweistheorie-lecture-notes.pdf` (Buchholz's own longer course
  treatment of the same Z system — more steps shown than [6]); `buss-handbook-ch2-first-order-proof-theory-arithmetic.pdf`
  (standard cut-elimination, the canonical reference); `arai-lectures-on-ordinal-analysis.pdf` (alternative
  ordinal-assignment exposition — cross-check the degree-drop).
- **L3.1 / T3.4:** `buchholz-on-gentzens-first-consistency-proof.pdf` pp.8–9 (primary, complete proofs);
  `siders-gentzen-consistency-proofs-arithmetic.pdf` (the cited eq-5 companion).
- **Bridge (C0.5):** Bryce–Goré `Peano.v` (Coq, the direct analogue); `buchholz-beweistheorie` (PA→PA_ω
  embedding, § embedding); Rathjen `rathjen-2006-art-of-ordinal-analysis.pdf` for context.
- **Tower / `o(d)` reindex:** [6] §4 + `arai-lectures` (the `ω_n` hierarchy conventions).

## 7. How this could be wrong / validation checklist
- I read [6]'s §§3–5 but mapped cases to the box's `zTag`/`iR` from the handoffs, not from `InternalZ.lean`
  source — **confirm `iR`'s critical branch actually constructs `d{0}`/`d{1}` per 3.2(5.1)**, not a
  shortcut that silently changes the ordinal bound.
- **Confirm `icmp_iotower_lt_succ_of_le` proves `ω_m(ω^α) ≤ ω_{m+1}(α)`** (the exact step the nut's Thm-4.2
  combine needs). If it proves something weaker, that's a missing tower lemma — flag it.
- The "LOW-HANGING first" ordering assumes `ZDerivation` + a minimal `iR` exist for the easy rules before the
  hard one — true if `iR` is built rule-by-rule (it should be).
- If `iR`'s degree drop in case 5.1 turns out NOT to need T3.4 (e.g. the box encodes ranks so `rk<r` is
  definitional), then T3.4 collapses to a definitional unfolding — *check before building it as a theorem*.
- Credit: the box's F1–F4 isolation and the `icmp_insTerm_congr` nut-identification (lap 59) are exactly
  right and feed LH3/LH5 + nut-step 2. This doc reorders and gates; it does not relitigate the algebra.

## 8. Atomic breakdown of the hard part (leaf-level grind-list)
The nut (case 5.1) and its two prereqs, taken down to bite-sized Lean obligations against Buchholz pp.8–11.
**Punchline: no leaf is a monolith; only four leaves are genuinely-new content.** Tags: 🆓 free (structural
IH) · ➕ ℕ-arithmetic/definitional · ✅ algebra you have · 🔨 algebra you're building (F1/F2) · 🆕 new but
small · 📐 one tower lemma.

### 8.1 — Lemma 3.1, the redex finder (p.8). A `Σ₁` search, NO ordinals.
- **L1** the last inference symbol `I_{j₀}` is an L-symbol (`L^k_B`), forced by the false-minimal succedent. [🆕 a `zTag`-of-last-premise case-check]
- **L2** `j :=` least index with `I_j ∈ L`; its cut-formula `B ∈ Γ_j\Γ`, so `B = A_i` for some `i<j`. [🆕 minimality search + antecedent-membership]
- **L3** by minimality `I_i ∉ L`; permissibility `I_i ◁ Π_i` forces `I_i = R_{A_i}`. [🆕 "permissible non-L symbol on `Γ→A_i` ⟹ `R_{A_i}`" case-lemma]
- **L4** `rk(A_i) > 0` (else `R_{A_i}` & `L^k_{A_i}` both permissible ⟹ `A_i ≈ ⊤` and `≈ ⊥`, impossible). [➕ rank/truth-value check]
⟹ a `Σ₁`-definable least pair `(i,j,k)`. All four leaves are finite code-combinatorics — the box's `zTag`/recognizer wheelhouse.

### 8.2 — Theorem 3.4(a), the rank bound (p.9).
- **T1** IH(b) on the redex premises: `d_i[k] ⊢ Π_i·F(k)`, `d_j[0] ⊢ F(k),Π_j`. [🆓 structural IH]
- **T2/T3** `d{0}:=K^r_{Π·A(d)}(i/d_i[k])`, `d{1}:=K^r_{A(d),Π}(j/d_j[0])` are valid `K^r` chains with the stated endsequents. [🆕 ONE reusable lemma: "replace a premise of a valid `K^r`-chain by a same-endsequent reduct ⟹ still valid `K^r`"]
- **T4** `rk(A(d)) < r`, since `rk(A(d)) = rk(F(k)) = rk(F) < rk(F)+1 = rk(∀xF) = rk(A_i) ≤ r`. Three facts: **(a)** `rk` substitution-invariant `rk(F(k))=rk(F)` [🆕 small structural lemma — the ONE new rank fact]; **(b)** `rk(∀xF)=rk(F)+1` [➕ definitional]; **(c)** `rk(A_i) ≤ r` [➕ the `K^r` chain-rank invariant, read off well-formedness].

### 8.3 — The nut, Lemma 4.1(b)(ii) case 5.1 (p.11). Given L3.1's redex + T3.4's `d{0}/d{1}`:
- **N1** IH on the immediate subderivations: `dg(d_i[k]) ≤ dg(d_i)`, `õ(d_i[k]) < õ(d_i)` (and `d_j[0]`). [🆓 structural IH = Lemma 4.1 on `d_i`,`d_j`]
- **N2** lift to the auxiliaries: `dg(d{ν}) ≤ dg(d)` and `õ(d{ν}) < õ(d)`. [dg: ➕ `dg(K^r…)=max{dg(prem)−1,r}` + N1. õ: 🔨 **F1** — replacing one `#`-summand `ω^{õ(d_i)}` by the smaller `ω^{õ(d_i[k])}` lowers the sum = your `icmp_insTerm_congr`/left-cancel]
- **N3a** `dg(d[0]) < dg(d)`: `dg(d[0])=max{dg(d{0})−1,dg(d{1})−1,r−1}`, each term `< dg(d)` from N2 + `r ≤ dg(d)`. [➕ pure ℕ-max arithmetic] **← the cut-elim degree-drop is just arithmetic, once `iR` builds `d{0}/d{1}`**
- **N3b** `õ(d[0]) < ω^{õ(d)}`: `õ(d[0]) = ω^{õ(d{0})} # ω^{õ(d{1})}`, both `< õ(d)` (N2) ⟹ via **F2** (`ω^{α0}#ω^{α1} ≺ ω^α`). [🔨/✅ **F2**]
- **N3c** `rk(A(d)) < dg(d)`: T3.4 `rk(A(d)) < r ≤ dg(d)`. [➕ arithmetic]
- **N4** Thm 4.2 combine: `o(d[0]) = ω_{dg(d[0])}(õ(d[0])) <_{N3b} ω_{dg(d[0])}(ω^{õ(d)}) = ω_{dg(d[0])+1}(õ(d)) ≤_{N3a} ω_{dg(d)}(õ(d)) = o(d)`. Uses **(i)** `ω_m(ω^α)=ω_{m+1}(α)` [➕ definitional tower identity], **(ii)** `ω_m` base-monotone [✅ `icmp_iotower_mono`], **(iii)** tower height-monotone `ω_m(β) ≤ ω_{m'}(β)` for `m ≤ m'` [📐 — **VALIDATE `icmp_iotower_lt_succ_of_le` delivers exactly (iii)**]

### Tally — the ENTIRE hard part's genuinely-new content is 4 small leaves:
1. **L1–L4** the redex finder (finite `zTag` combinatorics).
2. **T2/T3** the "replace-a-premise stays a valid `K^r`-chain" lemma (one reusable fact).
3. **T4(a)** rank-substitution-invariance `rk(F(k))=rk(F)` (one structural lemma).
4. **the `d{0}/d{1}` object construction** = `iR`'s critical branch (the only sizeable build, and it's bounded).
Everything else is 🆓 IH, ➕ arithmetic, 🔨 F1/F2 (in flight), ✅/📐 one tower lemma. **No monolithic step remains in crux-2.** The "wall" was a staircase.

### 8.4 — Validation (this section specifically)
- I read Buchholz pp.8–11 directly, but mapped `d{0}/d{1}`/`dg(K^r)`/`õ(K^r)` to the box's `iR`/`idg`/`iõ` from the handoffs — **confirm the `iR` critical branch builds `d{0}=K^r(i/d_i[k])`, `d{1}=K^r(j/d_j[0])`, `d[0]=K^{r-1}d{0}d{1}` verbatim** (3.2 case 5.1); a different reduct changes N2–N3.
- N4(iii): if `icmp_iotower_lt_succ_of_le` proves only `ω_m(α) ≼ ω_{m+1}(β)` under `α ≼ β` (same form as its name), confirm that instantiates to height-monotonicity at fixed base; else it's a 1-lemma gap.
- T4(c) assumes `iR`/`ZDerivation` carries the chain-rank `r` and the `rk(cut formula) ≤ r` well-formedness invariant. If ranks aren't stored, T4(c) needs the invariant proved from the `K^r` constructor first.
