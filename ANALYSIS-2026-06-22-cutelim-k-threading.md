# ANALYSIS — how `k`/`τ` thread through Towsner's cut-elimination (§17–§19)

**Filed:** 2026-06-22 (lap 7). **Resolves:** the open `ON-LINE-REQUEST.md` ("how does the numeric
index `k` / norm `τ` thread through cut-elimination"). Answered **offline** by a careful read of the
on-disk PDF `papers/towsner-goodstein-epsilon0-unprovability.pdf` §15–§20 (the request itself noted
this was possible). This is the design crux for the `Zᵏ` cut-elimination port (`wip/BoundedZinfty.lean`).

## TL;DR — the supposed wall was a misframing. Three facts collapse it.

The lap-6 worry was: "cut-elimination grows the ordinal bound, `norm`/`τ` is not preserved by ordinal
addition (`norm(ω+ω)=2`), so the cut-free output might violate `norm < k` and break the subformula
bridge." This rests on the false premise that **`k` is fixed**. It is not.

1. **`k` GROWS through cut-elimination — it is never held fixed.** Towsner's exact bounds:
   - **§19.5 (∧/∨ cut-reduction):** `⊢^{α,k}_c Γ,φ`  &  `⊢^{α,k}_c Γ,ψ`  &  `⊢^{β,k}_c ∆,(∼φ∨∼ψ)^m`
     ⟹  `⊢^{α#β, 2k}_c Γ,∆`.  **k ↦ 2k.**  τ(α#β) < 2k holds *because* τ(α),τ(β) < k and
     τ is sub-additive under natural sum (`τ(α#β) ≤ τ(α)+τ(β)`). The doubling is engineered to
     absorb exactly the additive growth of `τ`.
   - **§19.6 (∀/∃ cut-reduction):** `⊢^{α,max{k,n}}_c Γ,φ[n]` (∀n)  &  `⊢^{β,k}_c ∆,(∃x∼φ)^m`
     ⟹  `⊢^{α#β, h_{β#ω}(k)}_c Γ,∆`.  **k ↦ h_{β#ω}(k)** (a Hardy value). Towsner: "Adding ω
     ensures `h_{β#ω}(k) > 2k > τ(α#β')`."
   - **§19.7 (rank reduction `c+1 ↦ c`):** `⊢^{α,k}_{c+1} Γ` ⟹ `⊢^{ω^α, h_{ω^α}(k)}_c Γ`.
     **k ↦ h_{ω^α}(k).**  Ordinal blows up `α ↦ ω^α` (CNF norm: `norm(ω^α)=max(norm α,1)`, safe).
   - **§19.9 (full cut-elim):** apply §19.7 `c` times ⟹ `⊢^{ω_c^α, m}_0 Γ` for **some** `m`
     (`ω_c^α` = the `c`-fold `ω^·` tower over α).

2. **The lower bound (Thm 17.1) holds for EVERY `k`.** Our `lowerBound_hardy_selfcontained
   {α} (hα : α.NF) (k : ℕ) : ¬ B α k {gAll}` is already `∀ α NF, ∀ k`. Towsner's 17.1 likewise:
   "It is not the case that `Z∞ ⊢^{α,k} ∀x∃y g_y(x)=0` cut-free for any α < ε₀" — **for all k**.
   So whatever `m` cut-elim produces, `lowerBound … m` refutes it. **The growth of `k` is harmless.**

3. **Every `ONote` is automatically `< ε₀`.** `ONote` is the Cantor-normal-form notation system for
   ordinals `< ε₀`; `ONote.repr o < ε₀` for every `o` by construction. The "`ω_c^α < ε₀`" side
   condition Towsner must check is **free** in the Lean port — there is nothing to track. ε₀-closure
   under `ω^·` is built into the type.

## Consequence for the Lean design — make k EXISTENTIAL

Because (2) says the only thing the lower bound needs is "cut-free (`c=0`) at *some* `(α', k')` with
α' a NF ONote", and (3) says α'<ε₀ is automatic, the entire cut-elimination chain should be stated
**existentially in `k`**:

- Cut-free predicate: `CutFree α Γ := ∃ k, Zk α k 0 Γ`.
- Endgame target (`cutElim`): `(∃ k c, Zk α k c Γ) → α.NF → ∃ (α' : ONote) (k' : ℕ), α'.NF ∧ Zk α' k' 0 Γ`.
- Final contradiction (§20): from `Zk α k c {gAll}` (α NF) get `Zk α' k' 0 {gAll}`; subformula-bridge
  it to `B α' k' {gAll}`; `lowerBound_hardy_selfcontained (α' NF) k'` refutes. ∎

With `k` existential, `mono_k` (already proved) lets every combination step raise `k` to whatever
finite value makes the `norm β < k` side conditions hold at the *finitely many* nodes a single
reduction touches. **The one place this is NOT free is the ω-rule** (`allω`): it has ℕ-many premises
with `norm(β n) < max k n` and `norm(β n)` unbounded in `n` — a single finite `k` cannot bound them.
That is exactly why Towsner's `max{k,n}` design exists and why `allInv` (already ported) threads
`max{k,n}`. The ω-rule's bound is preserved structurally; only the *combination* steps (∧/∨/∃ cuts at
a single node) grow `k`, finitely, absorbed by the existential.

## Natural sum `#` vs ordinary `+` (mathlib v4.31.0 has no `Ordinal.nadd`)

Towsner combines premise ordinals with **natural (Hessenberg) sum** `α#β`. mathlib v4.31.0 exposes no
`nadd` on `Ordinal` and `ONote` has only ordinary `+` (`ONote.add`, `repr_add`). Two viable routes,
both already de-risked:
- **Ordinary `+` with slack** (what `src/Zinfty.lean` lap-3 did for the `(α,c)` calculus): `α+β ≥ α`,
  `α+β ≥ β`, and `norm(α+β) ≤ norm α + norm β` (ONote.add merges equal leading exponents, absorbs
  lower α-terms — never exceeds the sum of norms). With existential `k`, the `2k`/`norm α+norm β` slack
  is absorbed for free. The `cutReduceConj/Disj` already in `wip/BoundedZinfty.lean` use a **`δ`-trick**
  (caller supplies NF `δ > α,β` with `norm δ < k`, result at `osucc δ`, **same `k`**) — equivalent
  once `k` is existential (pick `δ` = the combined ordinal, `k` large enough).
- **Define `ONote`-level natural sum** (merge-sort CNF exponent multisets) if a faithful `#` is wanted;
  then `norm(a ⊕ b) = norm a + norm b` is a clean structural lemma. Not required for the headline.

**Recommendation:** ordinary `+`, existential `k`. Matches lap-3, needs no new ordinal infrastructure.

## What this unblocks / next concrete steps (see PENDING_WORK step 1)
- **§19.6 ∀/∃ cut-reduction** (`cutReduceAll`): invert the ∀-side once via `allInv` (→ numeral family
  `φ[n]`), induct on the ∃-side derivation, cut at the witness numeral in the principal `exI` case.
  Bound: ordinal `α+β` (ordinary `+`); `k` existential. **The next girder.**
- **§19.7 `cutElimStep`** (`c+1 ↦ c`, ordinal `α ↦ ω^α = oadd α 1 0`, `norm_omegaPow` banked) +
  **§19.9 `cutElim`** (iterate `c` times). All existential in `k`.
- **Step 4 subformula bridge** then consumes `CutFree α' {gAll}` ⟹ `B α' k' {gAll}` ⟹ contradiction.

No literature gap remains for the cut-elimination `k`/`τ` bookkeeping itself (the original request is
answered). **But see the ADDENDUM below** — the §19.6 *commuting* cases surfaced a deeper obstruction;
`ON-LINE-REQUEST.md` is re-filed for that one layer down.

---

## ADDENDUM (lap 7, continued) — the §19.6 **I∀-commuting** obstruction (deeper than the headline crux)

Starting the `cutReduceAll` port for `Zk` surfaced a genuine obstruction that Towsner's §19.6 ("the
other cases follow immediately from the IH") glosses over. Recording it precisely so the next lap does
not rediscover it.

**Setup.** §19.6 inverts the ∀-side (`allInv` → family `fam : ∀n, Zk α (max k n) c (Γ,φ[n])`) and
**inducts on the ∃-side** `Zk β k c (∆, ∃∼φ)`, framing the running conclusion over `α + βᵢ` (ordinal)
at a grown `k`. The **principal `exI`** case is clean (cut `fam n` at witness `n ≤ hardy β k`, which is
why Towsner's bound uses `β#ω`: `h_{β#ω}(k) > 2k ≥` the witness). The trouble is the **commuting `allω`
case**: the ∃-side's last rule is an ω-rule introducing some `∀χ ∈ ∆`, premises
`Zk βₙ (max k n) c (∆', χ[n], ∃∼φ)` with `norm βₙ < max k n`.

**The obstruction (machine-analytic, not yet machine-checked).** Reconstructing the ω-rule on `χ` at
the conclusion's grown index `K` requires the `n`-th premise to satisfy the `Zk.allω` side condition
`norm(α + βₙ) < max K n`. But `norm(α+βₙ) ≤ norm α + norm βₙ` (our `norm_add_le`) and `norm βₙ` can be
`~ n` (e.g. `βₙ = ofNat n < β = ω^ω`, `norm βₙ = n`, since `norm` is **not** monotone in `<`). So
`norm(α+βₙ) ~ norm α + n`, which for large `n` **exceeds** `max K n ~ n` — for ANY fixed `K`, even with
the existential-`k` design, even with natural sum (`τ(α#βₙ) = τα + τβₙ`), even using `τα < k` (the cut's
own side condition). The additive constant `norm α` cannot fit under the ω-rule's `max{k,n} ~ n` budget
for large `n`. **Adding `α` to the bound breaks the ω-rule norm budget in the commuting case.**

**Why this isn't fatal — but needs the right machinery.** The standard rigorous fix is **Buchholz
operator-controlled derivations** (`H` an operator on ordinal sets, written `H ⊢^α_c Γ`) instead of a
numeric `k`: the ω-rule's premises are controlled by `H[{n}]` (the operator augmented by `n`), and the
embedding/cut-elimination thread the *operator* (closed under the relevant ordinal functions), which
absorbs a `+α` shift where a numeric `max{k,n}` cannot. Towsner's numeric `(α,k)` is a stripped-down
presentation that works for the *principal* lower-bound argument (§17) but is too rigid for the
*general* §19.6 commuting cases unless one re-derives the Hardy fundamental-sequence inequalities
(Towsner 16.8–16.10) carefully — and even then the `max{k,n}`-vs-`+α` mismatch above suggests the
numeric form genuinely needs either (i) the operator reformulation, or (ii) a per-`n` index on the
reconstructed ω-rule that the `Zk.allω` shape would have to be generalized to permit.

**Decision / next-lap options (hardest-first):**
1. **Reformulate `Zk` operator-controlled** (Buchholz `beweistheorie` §9 "Boundedness", on disk;
   Hardy-hierarchy §, on disk). Most robust; larger refactor of `wip/BoundedZinfty.lean`.
2. **Generalize `Zk.allω`** to allow the `n`-th premise at index `f n` for a controlled `f` (not just
   `max k n`), re-checking the lower bound (M6) still refutes — the lower bound is `∀k`, may extend to
   `∀ controlled f`. Smaller change; verify §17 survives.
3. **Re-derive Towsner 16.8–16.10** (Hardy fundamental-sequence bounds; partial machinery already in
   `src/Hardy.lean`: `Reaches`, `fundamentalSequence`, `hardy_le_of_reaches`, `hardy_monotone`) and
   prove the commuting-case inequality `h_{βₙ#ω}(max{k,n}) ≤ max{h_{β#ω}(k), n}` IF it holds — but the
   `+α` analysis above suggests it does NOT hold in the naive form, so (1)/(2) are more promising.

This is the true remaining depth of step 1. The conceptual `k`-crux (top of this doc) and the
`norm`-subadditivity ingredient (`norm_add_le`, proved) are done; the §19.6 commuting-case bounding is
the live frontier. `ON-LINE-REQUEST.md` re-filed for the operator-controlled / S-W bounding-lemma
detail.

---

## ADDENDUM 2 (lap 7, continued) — option 2 (global index swap) is ELIMINATED; operator index needed

Attempted the recommended lightweight fix (option 2: swap the ω-rule index `max k n → k + n` globally in
`wip/BoundedZinfty.lean`). It does **not** work — a second, opposite obstruction appears, so the two
naive global indices each break a different half:

- **`max k n` (current)** — good for `allInv` (the principal case relies on **idempotence**
  `max (max k n₀) n₀ = max k n₀` to keep a single result index), but **breaks §19.6-commuting**
  (`norm(α+βₙ) ~ norm α + n > max K n ~ n`, ADDENDUM 1).
- **`k + n`** — good for §19.6-commuting (`(k+n)+norm α = (k+norm α)+n`, additive shift absorbs `+α`),
  but **breaks `allInv`**: the principal case (when the inverted `∀⁰φ₀` *also lingers in* `Γ₀`, a set-
  sequent duplicate) must re-invert via the IH, producing index `(k+n₀)+n₀ = k + 2n₀` — there is no
  idempotent collapse under `+`. Declaring `allInv`'s result at `k + 2·n₀` is internally consistent
  (clean cases `mono_k` up), but then the §19.6 family `fam n` lands at index `k + 2n` — **slope 2** —
  and the lower bound's I∀ case now needs `hardy α (2n+k) < G(n)`, a *multiplicative* rescaling that
  `hardy_shift_lt_goodsteinLength` (additivity, slope 1) does NOT cover. (A slope-2 Hardy bound needs a
  rescaling lemma `hardy α (2n) ≤ hardy α' n`, strictly harder than finite-tail additivity.)

**Conclusion: no single numeric index `idx(k,n)` serves both `allInv` (wants idempotence) and
§19.6-commuting (wants additive-shift absorption).** The principled fix is a **function/operator-valued
index**: each `allω` node carries an index *function* `g : ℕ → ℕ` (with `g` controlled, e.g.
`g n ≤ n + const`), and the rules compose `g`s — `allInv` composes idempotently, cut-elim's commuting
case post-composes the `+norm α` shift. This is exactly **Buchholz operator-controlled derivations**
(`H ⊢^α_c Γ`) specialized to PA. It subsumes both naive indices and keeps the controlled-index
domination (`hardy_shift_lt_goodsteinLength`, proved) applicable at the slope-1 level.

**Revised recommendation: option 1 (operator/function-valued `allω` index), NOT option 2.** It is the
larger refactor of `wip/BoundedZinfty.lean` + `B`/lower-bound, but it is the only one that closes both
obstructions. The two Hardy lemmas proved this lap (`hardy_add_ofNat`, `hardy_shift_lt_goodsteinLength`)
remain the right domination ingredients for it (the controlled `g` keeps the slope at 1). The `+α`/`max`
analysis here is the precise spec the operator index must satisfy. `wip/BoundedZinfty.lean` left
sorry-free (the `k+n` experiment reverted); no half-broken state committed.

---

## ADDENDUM 3 (lap 7) — THE FIX: a split index `(k, d)` (concrete, lighter than full operators)

ADDENDUM 2 concluded "operator-valued index needed". Working it out gives a **concrete minimal form**:
add ONE numeric parameter `d` (a cut-shift budget) alongside `k`. The two obstructions want opposite
things from the index — `allInv` wants idempotence (use `max`), §19.6-commuting wants additive-shift
absorption (use `+`). **Give each its own component:**

- Calculus index becomes `(k, d) : ℕ × ℕ`. Effective norm budget for a node is `k + d`; the **ω-rule's
  `n`-th premise** sits at index `(max k n, d)` (so its budget is `max(k,n) + d` — the `+d` is OUTSIDE
  the `max`, shifting the whole thing uniformly).
- **`allInv` (and all inversions) transform only `k`** (via `max`, leaving `d` fixed): the principal
  lingering-duplicate subcase re-inverts at `n₀`, giving `(max (max k n₀) n₀, d) = (max k n₀, d)` —
  **idempotent** (max), `d` untouched. ✓ The numeric juggling stays exactly as the current `max`-based
  proofs, just carrying an inert `d`.
- **§19.6 cut-elim transforms only `d`** (additive, leaving `k` fixed): the commuting `allω` case bumps
  `d ↦ d + norm α`. Reconstructed premise `n` budget `max(k,n) + (d + norm α) = (max(k,n)+d) + norm α >
  norm α + norm βₙ ≥ norm(α+βₙ)`. ✓ exactly absorbs the `+α` shift.
- **Slope stays 1:** every node budget `max(k,n) + d ≤ n + (k + d)` — linear in `n` with constant
  `k+d`. So the lower bound's I∀ case needs `hardy α (max(k,n)+d) < G n`, discharged by
  `hardy α (max(k,n)+d) ≤ hardy α (n + (k+d))` (`hardy_monotone`) `< G n`
  (`hardy_shift_lt_goodsteinLength` with `c = k+d`). ✓ **Both proved lemmas apply directly — no
  multiplicative rescaling needed.**

This is the operator control of Buchholz §9 in its **minimal PA form** (`d` is the additive part of the
"operator"; `max(k,·)` is the cofinal part). **It is the recommended implementation** — lighter than a
general `g : ℕ → ℕ` or set-valued `H`, and every existing `max`-based proof in `wip/BoundedZinfty.lean`
ports by threading an inert `d`.

**Refactor plan (next lap):** add `d : ℕ` to `Zk` (and `B`); rule norm conditions `< k` become `< k + d`
(ω-premise `< max k n + d`); witness bound `≤ hardy α (k+d)` (or `(max k n + d)` in ω); re-prove the
inversion suite (`d` inert, `k`-juggling unchanged), the ∧/∨ cut-reductions (`d` inert), then
`cutReduceAll` (the commuting `allω` case bumps `d ↦ d + norm α`, the §19.6 payoff), `cutElimStep`,
`cutElim`; re-prove `lowerBound_hardy_selfcontained` (I∀ case via `hardy_shift_lt_goodsteinLength`).
`hardy_add_ofNat` + `hardy_shift_lt_goodsteinLength` are the banked domination ingredients. Sanity-check
the principal `exI` case threads the witness bound under `(k,d)`.

---

## ADDENDUM 4 (lap 7) — the `(k,d)` split solves §19.2–19.5 but NOT §19.6 (a SECOND, witness-index obstruction)

Implementing `wip/SplitZinfty.lean` (calculus + §19.2–19.5 on the `(k,d)` split, all sorry-free) and then
setting up `cutReduceAll` exposed that §19.6 has **two independent** obstructions, and the `(k,d)` split
only closes one:

1. **Norm-budget obstruction (ADDENDUM 1):** reconstructed commuting-`allω` premise `n` needs
   `norm(α+βₙ) < (premise budget)`. **CLOSED by the `d`-bump** (`d ↦ d + norm α`): budget
   `max(k,n)+(d+norm α)` absorbs the `+norm α`. ✓ (This part of ADDENDUM 3 is correct.)

2. **Witness-index obstruction (NEW, ADDENDUM 4):** `cutReduceAllAux`'s **principal `exI` cut** cuts the
   ∀-family `fam w` (at index `(max k' w, d)`, from `allInv` at the witness `w`) against the ∃-side. The
   witness `w ≤ hardy γ (k'+d)`, so the cut pulls the **k-part up to `~ w ~ hardy γ (k'+d)`**. At the
   *top level* `k' = k` is fixed, so this is a constant — fine. But in the **commuting `allω` case** the
   IH is invoked at `k' = max k n` (the ω-premise's k, which grows with `n`), so the IH's output k-part
   grows like `hardy(·)(n)` — **super-linearly in `n`**. Reconstructing the ω-rule then needs premise `n`
   at `max k_c n` (linear in `n`), which **cannot absorb** a `hardy(·)(n)` index (`mono_k` only raises,
   and `max k_c n ~ n < hardy(·)(n)` for large `n`). **The `max k n` ω-premise shape is fundamentally
   incompatible with a Hardy-growing witness index passing through it.**

This is exactly why Towsner's conclusion index is the **Hardy value `h_{β#ω}(k)`** and the ω-rule premise
is `max{conclusion-k, n}` — and why even that needs the **full Buchholz operator `H`** (a SET closed
under the Hardy/ordinal functions) rather than any numeric or `(k,d)` index: only a function-closed
operator can satisfy `h_{βₙ#ω}(max{k,n}) ∈ H[{n}]` uniformly. A single numeric k-part (even `max k n`)
or the `(k,d)` split cannot.

**Honest status:** `(k,d)` is a **correct and reusable stepping stone** — it carries §19.2–19.5 and the
§19.6 norm-budget, and the operator `H` generalizes its `max(k,·)`-part to a function-closed `H`-part
(keeping the additive `d`). The inversions/§19.5 proofs in `SplitZinfty.lean` will largely port to the
operator calculus. But **§19.6 `cutReduceAll` is NOT completable on `(k,d)`**; it needs the operator.

**Revised next step:** implement the **Buchholz operator-controlled calculus** `H ⊢^α_{d,c} Γ` (operator
`H : Set ℕ → Set ℕ` or a concrete "closed-under-`hardy`" predicate on the witness index), ω-premise `n`
controlled by `H[{n}]`, the True/∃ side conditions by `H`. Port §19.2–19.5 from `SplitZinfty.lean`
(mechanical: `max k ·` ⤳ `H`), then §19.6 with the witness index living in `H[{n}]` (closed under
`hardy`, so the principal cut's `hardy(·)(·)` witness stays in `H`). The `d`-bump (norm budget) rides
alongside. `ON-LINE-REQUEST` (PA operator-control spec) remains the literature ask.

---

## ADDENDUM 5 (lap 8) — the **control-ordinal `e`** form: obstruction 2 CLOSES, Hardy infra BANKED

Lap 8 implemented the operator as a **single control ordinal `e : ONote`** (the numeric-`e` Buchholz
form), not the full set-valued `H`. The witness bound is decoupled from the derivation ordinal `α`:

> `exI` bound: `n ≤ hardy e (k + d)`  (was `hardy α (k + d)`).

This is `wip/OperatorZinfty.lean` (`Zekd α e k d c Γ`), built sorry-free through §19.5 + the new
control-axis monotonicity `mono_e`.

### Why `e` closes the witness-index obstruction (the ADDENDUM-4 wall)

ADDENDUM 4's wall was: under cut-elim `α ↦ α + γ`, a witness bound `hardy α (·)` GROWS, and through a
commuting ω-rule the witness index becomes Hardy-super-linear, which `max k n` cannot pass. The fix:

1. **Commuting cases keep `e` inert.** The witness bound `hardy e (k+d)` does not move when `α` grows;
   the commuting ω-rule reconstructs with the *same* `e`, so no Hardy-super-linear index is ever forced
   through `max k n`. The only index motion in commuting cases is the `d`-bump (`d ↦ d + norm α`,
   norm-budget, already closed by `(k,d)`).
2. **`e` is raised only at the top-level cut**, via `mono_e` (banked): combining the ∀-side (control
   `e₁`) and ∃-side (control `e₂`) needs a common control `e = ` an NF ordinal `> e₁,e₂`; `mono_e` lifts
   both via the banked index-monotonicity `hardy_le_of_lt` (budget side condition `norm eᵢ ≤ k+d`). The
   witnesses then all sit under `hardy e`.
3. **The lower bound survives.** In a cut-free `Zekd`-derivation of `{gAll}`, `e` is a FIXED `ONote`
   `< ε₀`; witnesses `≤ hardy e (k+d)` and the I∀ inversion index is controlled. The nested-control
   index `hardy α (hardy e (·))` that the bridge-to-`B` produces is Goodstein-dominated by the banked
   **`hardy_comp_lt_goodsteinLength`** (lap 8). The control-side collapse `hardy (e+α) = hardy e ∘ hardy α`
   is the banked **`hardy_add_collapse`** (lap 8).

So the single control ordinal `e` suffices — the full set-valued `H` is NOT needed for PA/`ε₀`. The
Hardy-closure that `H` was meant to provide is exactly `hardy_le_of_lt` (raise `e`) + the two
composition lemmas (lower bound). **All three are banked and axiom-clean.**

### Banked this lap (the Hardy layer of the design, both directions)
- `hardy_add_comp` / `hardy_add_collapse` (`src/Hardy.lean`): `H_{γ+δ}=H_γ∘H_δ` for non-absorbing
  `γ+δ` (δ below γ's least exponent). Control-side cut-elim collapse.
- `hardy_comp_lt_goodsteinLength` (`src/LowerBound.lean`): `H_α(H_e(m)) < G(m)` eventually, ANY NF
  `α,e`. Lower-bound side: the nested control index is still Goodstein-dominated (via `ω^Q·2`
  exceeding both `α,e` + the coefficient law). Both axiom-clean (trust base + the documented Goodstein
  `native_decide` base-cases).
- `Zekd` calculus (`wip/OperatorZinfty.lean`): inductive + `mono_k/d/c/e` + full inversion suite
  (orInv, andInvL/R, allInv) + §19.5 cutReduceConj/Disj + all §19.6/19.7 ordinal/norm helpers.
  Sorry-free. Full §19.2–19.5 parity with `SplitZinfty` PLUS the control axis.

### The remaining girder: §19.6 `cutReduceAll` on `Zekd` — and a NEWLY-SURFACED subtlety

Structure (port `src/Zinfty.lean:785 cutReduceAllAux` + bounded bookkeeping): invert ∀-side → `fam`;
induct on ∃-side; principal `exI` cuts `fam(witness)`; commuting cases reapply the rule at `α + γ`
(`add_osucc_descent` banked); ordinal `osucc(α+γ)`, `d ↦ d + norm α`, `e` raised at the top cut.

**NF-threading subtlety (surfaced lap 8, attempting the trueRel leaf):** the **leaf** rules
(`axL`/`verumR`/`trueRel`/`trueNrel`) carry NO `hαNF` on the node ordinal `γ`, so in `cutReduceAll`'s
leaf cases `γ` may be non-NF — and then `norm (α+γ) ≤ norm α + norm γ` (`norm_add_le`, **NF-essential**;
NF-free version is machine-checked FALSE) does NOT apply, so the conclusion ordinal `osucc(α+γ)`'s norm
budget can't be discharged directly. **Fix options for next lap:** (a) re-issue leaf conclusions at the
node's own `γ` (norm `< k+d` already) via `weak` up to `osucc(α+γ)` — but `weak`/`γ ≤ α+γ` themselves
need NF (`le_add_left_NF`); (b) add an `α.NF` invariant to the leaf rules of `Zekd` (cheap — the leaves
are issued by the embedding M4 / the calculus's own rules, which always have NF α in practice); (c)
carry an `NF γ` side-hypothesis through `cutReduceAllAux` (the ∃-side derivation's ordinal). Option (b)
(NF-ify the leaves) is the cleanest and matches Towsner (every `Z_∞` node is `<ε₀` ⟹ NF). This is the
concrete first task of the cut-elim grind, ahead of the commuting/principal bound bookkeeping.

### Lap-8 cont. — NF-threading runs deeper than the leaves; use a `Provable`-style wrapper

NF-ifying the leaves (`trueRel`/`trueNrel`, done — commit `c8cd83d`) is necessary but NOT sufficient
for `cutReduceAll`: the **`wk` case** also needs `γ` NF. There, when `(∃∼φ)∉Δ'`, the sub-derivation
sits at ordinal `γ` over `Δ.erase(∃∼φ)∪Γ`, but the conclusion is demanded at `osucc(α+γ)` — raising `γ
→ osucc(α+γ)` uses `Zekd.weak`, whose `hβNF` needs `γ.NF`. Raw `Zekd` carries an *exact* ordinal (no
built-in "≤" slack), so every ordinal-raise needs NF of the source.

**Cleanest fix (matches the unbounded `Zinfty.lean` template) — a `Provable`-style wrapper:**
```
def ZekdProv (α e : ONote) (k d c : ℕ) (Γ : Seq) : Prop :=
  ∃ α', α' ≤ α ∧ α'.NF ∧ Zekd α' e k d c Γ
```
State `cutReduceAll` over `ZekdProv` (bound `α` as an UPPER bound, like `Provable α c`). The wrapper's
`α'.NF` supplies NF wherever an ordinal-raise is needed, and the `α' ≤ α` slack absorbs the `osucc`/`+1`
bookkeeping uniformly (no per-case boundary fights). The unbounded `Provable.cutReduceAllAux` is then a
near-line-by-line template (it already threads exactly this `∃ d, o d ≤ α ∧ cr ≤ c` wrapper); the
bounded port adds the `(k, d, e)` carry: `mono_k`/`mono_d`/`mono_e` for the index, `norm_add_le` for the
`d`-bump, `hardy_comp_lt_goodsteinLength`/`hardy_add_collapse` for the witness control. **This is the
recommended first construction of the next lap, ahead of writing `cutReduceAllAux` itself.**

---

## ADDENDUM 6 (lap 12) — the FIX for §19.6 `cutReduceAllAux` norm budget: norm-carrying wrapper + `+1` d-bump

Lap 11 retracted the two-phase escape (the strategic note atop `cutReduceAll` in `OperatorZinfty.lean`
is now STALE): the unbounded cut-free `Z∞` of `{gAll}` has UNbounded witnesses (lap-11 disproof:
witness `G(5)` at ordinal 1), so the witness bound must live in the calculus and survive cut-elim ⟹
§19.6 `cutReduceAllAux` on `Zekd` is back on the critical path. Lap 12 found WHY the lap-8 `ZekdProv`
wrapper stalled and the concrete fix.

**The obstruction (lap-12 diagnosis).** Reassembling the commuting `allω` in `cutReduceAllAux` needs the
premise ordinal's NORM bounded (`norm(premise) < max k n + d'`). The premise comes from the IH as a
`ZekdProv (osucc(α+βn)) …` = `∃ α', α' ≤ osucc(α+βn) ∧ …`. But **`norm` is NOT monotone under `≤`**
(`hardy-index-monotone-fails-small-arg`; `ofNat n < ω` yet `norm(ofNat n)=n`), so `α' ≤ osucc(α+βn)`
gives NO norm bound. The `≤`-wrapper THREW AWAY exactly the norm info the `allω` reassembly needs.

**The fix (three coupled moves; all with ordinary `+`, NO natural sum needed):**
1. **Norm-carrying wrapper:** `ZekdProv α e k d c Γ := ∃ α', α' ≤ α ∧ α'.NF ∧ norm α' < k+d ∧ Zekd α' …`.
   The IH now EXPOSES `norm α' < (its k)+(its d)`, which is exactly the `allω` premise budget.
2. **Thread `hγb : norm γ < k+dd`** through `cutReduceAllAux` (the ∃-side ordinal's norm). In EVERY
   case the child's required `hγb` is supplied by that rule's own `hτ` side-condition (`andI`→`hτφ/hτψ`,
   `allω`→`hτ n` at `max k n+dd`, `weak/exI/cut`→`hτ…`). The threaded `hγb` is used only at the RESULT,
   to bound `norm(osucc(α+γ))`.
3. **d-bump `dd ↦ dd + norm α + 1`** (the `+1` absorbs the `osucc`). Then for every node:
   `norm(osucc(α+γ)) ≤ norm α + norm γ + 1 < norm α + (k+dd) + 1 = k + (dd+norm α+1)` (STRICT, via
   `hγb`), and the `allω` premise `norm(osucc(α+βn)) ≤ norm α+norm βn+1 < max k n+(dd+norm α+1)` (via
   `hτ n`). Leaves at ordinal `0`: `norm 0 = 0 < k+(dd+norm α+1)` — the `+1` kills the `k+dd=0` edge.
   Ingredients all banked: `norm_osucc_le` (Hardy), `norm_add_le`, `hardy_monotone`, `le_add_left_NF`,
   `add_osucc_descent`.

**Why this closes BOTH historical obstructions.** Norm-budget (ADDENDUM 1): closed by `+1` d-bump +
`hγb`. Witness-index (ADDENDUM 4): closed because the control ordinal `e` stays INERT in `cutReduceAllAux`
(`fam` and the ∃-side share the fixed outer `e`; witnesses stay `≤ hardy e (·)`, never Hardy-super-linear
through `max k n`). `e` is raised only at the top-level cut in `cutReduceAll` (via `mono_e`). The
lap-8 `e`-design was RIGHT; it just lacked the norm-carrying wrapper + `+1`, hitting the
norm-not-≤-monotone wall. Implementation: `wip/OperatorZinfty.lean` (lap 12).

---

## ADDENDUM 7 (lap 12) — the WITNESS-budget half is NOT closable numerically; operator `H` required (corrects ADDENDUM 5)

ADDENDUM 6 (norm half) is **done & committed** (`cutReduceAllAux`, axiom-clean). Trying to *feed* it from
`cutReduceAll` exposed that §19.6 has TWO independent budgets and the lap-12 proof only closes one:

**The witness-budget gap (the `fam`-index).** `cutReduceAllAux` is stated with `fam : ∀ n, Zekd α e k₀
dd₀ c (insert (φ/[nm n]) Γ)` at a **FIXED** `k₀`. But `allInv n` (the only way to build `fam`) yields the
n-th ∀-premise at index **`max k₀ n`** — necessarily, since that premise's witnesses range up to
`hardy e (max k₀ n + dd₀)`, which a derivation at the smaller index `k₀` cannot host. So `fam`-at-fixed-`k₀`
is **unprovable** in general; `cutReduceAllAux` as written is a true-but-unfeedable lemma (it compiled only
because fixed-`k₀` + inert-`e` trivially bounds witnesses). Empirically: `cutReduceAll(k₀:=k) … fam …` with
`fam` from `allInv` fails to unify `k` against `max k n`.

**Why no numeric index works (definitive — this CORRECTS the lap-8 ADDENDUM-5 "single control ordinal `e`
suffices" optimism).** Take `fam` at the honest `max k₀ n` and let the result index grow to Towsner's
`h_{β#ω}(k)`. The commuting `allω` case (∃-side ends in ω-rule on `χ`) needs, for the reassembled ω-premise
`n`, the IH-result index `≤` the premise budget — i.e. Towsner's
  `h_{βₙ#ω}(max{k,n}) ≤ max{h_{β#ω}(k), n}`.
For `n` large (`> k`, `> h_{β#ω}(k)`): LHS `= h_{βₙ#ω}(n) ≥ h_ω(n) = h_n(n) > n =` RHS. **FALSE.** Towsner
"follows immediately from the IH"-hand-waves exactly this. The obstruction is structural: a numeric index
must simultaneously (a) GROW with the ∀-branch `n` to host the witness `hardy e (max k n)` and (b) stay
`≤ max{K,n}` to be a legal ω-premise — incompatible. The split `(k,d)` (ADD. 3), and the single control
ordinal `e` (ADD. 5), are all numeric ⟹ all fail here. `e`-inert (my lap-12 proof) sidesteps it only by
assuming the unprovable fixed-`k₀`.

**The fix = Buchholz operator-controlled derivations** (`papers/buchholz-beweistheorie-skriptum.pdf`,
"operatorkontrollierte Ableitungen"; also Buss Handbook ch.II). The witness "budget" is **set membership
`n ∈ H`**, not a numeric `≤`. `H` (a set/function on ordinals, closed under the relevant `hardy`/`+`/`ω^·`
functions) grows monotonically under cut-elim; the ω-rule premise `n` is controlled by `H[{n}]`. Because
the budget is set-membership, the nested-`hardy` witness blow-up STAYS in the (closed) `H` — there is no
numeric inequality to violate. The lap-8 banked Hardy lemmas (`hardy_add_collapse : H_{e+α}=H_e∘H_α`,
`hardy_comp_lt_goodsteinLength`) ARE the closure facts an `H` needs (they let the control absorb the
double-`hardy`); lap-8 had the right ingredients but wired them as a single numeric `e` rather than a set.

**What ports (do NOT rebuild):** the entire lap-12 `cutReduceAllAux` structural skeleton + norm-carrying
`ZekdProv` wrapper + `+1` d-bump port **verbatim** to the `H`-calculus — only the `exI`/`allω` witness
side-condition changes (`n ≤ hardy e (k+d)` ⤳ `n ∈ H[node]`). The norm budget (ADD. 6) is orthogonal and
stays. So lap-12 is the reusable half; next lap builds `Zekd^H` (witness control `H`) and re-does §19.2–19.6
threading `H` (mechanical for §19.2–19.5; §19.6 is where `H`'s closure finally makes the commuting ω legal).

**Decision: STOP trying numeric witness controls (single `k`, `(k,d)`, single `e`) — all three are now
PROVED insufficient for §19.6-commuting. Build the operator `H`.** Read Buchholz's operator definition +
its ω-rule + its cut-elim Boundedness lemma; that is the precise spec the `Zekd^H` calculus must implement.
