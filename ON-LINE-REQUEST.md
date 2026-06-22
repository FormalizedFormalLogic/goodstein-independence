# ON-LINE-REQUEST — Towsner §19.6 commuting cases: the ω-rule cut-elimination bounding detail

**Filed:** 2026-06-22 (lap 7). **Asker:** box (offline). **Unblocks:** the §19.6 ∀/∃ cut-reduction
(`cutReduceAll`) for the witness-bounded `Zᵏ` calculus — the one genuinely-deep step left in step 1 of
the connecting spine. (The numeric `k`/`τ` threading itself is RESOLVED offline — see
`ANALYSIS-2026-06-22-cutelim-k-threading.md`. This request is the *next layer down*.)

## The precise obstruction (machine-analytic; full derivation in the ANALYSIS addendum)
§19.6 inducts on the ∃-side derivation. The **principal `exI`** case is clean. The **commuting `allω`
case** (∃-side's last rule is an ω-rule introducing `∀χ`, premises `Zk βₙ (max k n) c (…)` with
`norm βₙ < max k n`) requires reconstructing the ω-rule at the grown conclusion index `K`, whose `n`-th
premise must satisfy `norm(α + βₙ) < max K n`. But `norm(α+βₙ) ≤ norm α + norm βₙ ~ norm α + n` (norm is
NOT `<`-monotone, so `βₙ < β` does not bound `norm βₙ`), which **exceeds** `max K n ~ n` for large `n`,
for ANY fixed `K`, even with natural sum and `τα < k`. **Adding the ∀-family bound `α` to the ordinal
breaks the ω-rule's `max{k,n}` norm budget in the commuting case.** Towsner §19.6 dismisses these as
"follow immediately from the IH" — but the numeric `(α,k)` presentation does not obviously survive here.

## What would unblock (any one)
1. **The detailed §19.6 commuting-`allω` case** worked out in the `(α,k)` numeric presentation: how is
   the reconstructed ω-rule's `n`-th premise kept under budget when the ordinal grows by `α`? Is there a
   Hardy fundamental-sequence inequality (à la Towsner 16.8–16.10) of the form
   `h_{βₙ#ω}(max{k,n}) ≤ max{h_{β#ω}(k), n}` that actually holds? (My `+α` analysis suggests the naive
   form fails — please confirm or correct.)
2. **Buchholz operator-controlled derivations for PA** (`H ⊢^α_c Γ`, the `H`-operator replacing the
   numeric `k`): the precise embedding + predicative cut-elimination + boundedness statements for the
   PA / `ε₀` case (not the `ID₁`/`KP` collapsing version, which is what the on-disk
   `buchholz-beweistheorie-lecture-notes.pdf` and `arai-lectures-on-ordinal-analysis.pdf` mostly cover).
   Buchholz's "operator controlled derivations" original (Arch. Math. Logic 1992) or the PA chapter of
   any text that does it numerically-free. Goal: see how the operator absorbs the `+α` shift that the
   numeric `max{k,n}` cannot.
3. **Schwichtenberg–Wainer, *Proofs and Computations*, Ch. 4** — the "Bounding Lemma" / the `H_α`-bound
   threading through `PA_∞` cut-elimination, stated precisely enough to see the commuting ω-rule case.
   (Not on disk.)

A few paragraphs on how the ω-rule commuting case is bounded under the cut-elimination ordinal growth
(numeric or operator) would let me pick between: re-deriving the Hardy inequalities, generalizing
`Zk.allω` to a controlled index function (and re-checking the M6 lower bound survives), or refactoring
`Zk` to operator-controlled form. **Not blocking the lap** — continuing on other open work meanwhile.

## Why it matters
Without the correct commuting-case bound, `cutReduceAll` cannot be completed faithfully, and step 1
(cut-elimination for `Zᵏ`) cannot close — the headline path stalls at the M5↔M6 connection. The
`norm`-subadditivity ingredient (`norm_add_le`) and the conceptual `k`-crux are already done; this is
the last deep piece of the cut-elimination girder.
