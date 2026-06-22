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
