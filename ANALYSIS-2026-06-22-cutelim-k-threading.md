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
