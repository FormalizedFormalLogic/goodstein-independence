# ON-LINE-REQUEST — literature gaps for the box (offline)

A networked host session fulfils these: commit `ON-LINE-FINDINGS-<date>-<topic>.md`, delete the
answered item here, and remove this file once nothing is left open.

---

## 2026-06-22 (lap 4) — the *rigorous* invariant for the bounded cut-free lower bound (Towsner Thm 17.1)

**Context.** We are formalising Kirby–Paris (`PA ⊬ Goodstein`) via Towsner's Route B
(`towsner-goodstein-epsilon0-unprovability.pdf`, on disk in `papers/`). Towsner Theorem 17.1 is the
lower bound: *no cut-free, ordinal-`<ε₀`, numeric-bound-`k` deduction `Z_∞ ⊢^{α,k}_0 ∀x∃y g_y(x)=0`.*
We have machine-checked the **∃-only fragment** of this (no `∀x` present) cleanly — see
`wip/WitnessBound.lean : lowerBound_existential`. The full theorem with the Goodstein **sentence**
present (hence the `I∀` ω-rule) is the open frontier.

**The precise difficulty.** Towsner's induction (PDF p. 29–30, the `I∀` case) applies the inductive
hypothesis to `Γ₀ ∪ {∃y g_y(n)=0}` at bound `(βₙ, n)` after "choosing `n ≥ k` large enough that
`G(n) > hα(n) > hβₙ(n)`." His stated invariant requires every other existential `∃y g_y(m)=0 ∈ Γ₀`
(with `m ≤ k`, `G(m) > hα(k)`) to **still** satisfy the invariant at the *new, larger* numeric bound
`n`, i.e. `G(m) > hβₙ(n)`. But `hβₙ(n)` is astronomically large for the large `n` forced by
domination, while `G(m)` is a fixed finite number — so the condition `G(m) > hβₙ(n)` **fails**. The
exposition appears to gloss the case where the `I∀` ω-rule is applied while *other* existentials are
still pending in the sequent (which a cut-free derivation of `{∀x∃y g_y(x)=0}` genuinely can do, by
re-applying `I∀` to the universal before discharging an earlier `∃`).

**What we need (any one suffices):**
1. The *exact* induction invariant used in a rigorous proof of the bounded cut-free lower bound —
   one that is provably preserved by the `I∀` rule in the presence of accumulated existentials.
   Likely sources: **Schwichtenberg & Wainer, _Proofs and Computations_** (the `≺`-/H-controlled
   "bounding/boundedness lemma" for `PA_∞`); **Buchholz, _Beweistheorie_** (`papers/`, German — the
   `H`-controlled-derivation boundedness theorem `Bᵃ`); **Buss, Handbook ch. II** (`papers/`,
   the Gentzen consistency / ordinal-bound argument). Please quote the precise statement + the
   invariant/measure, and how the universal-rule case closes with side existentials present.
2. Equivalently: confirmation that the *cleanest formalization-friendly* route is the
   **operator/`H`-controlled derivation** with a **single** ordinal bound (Buchholz style), where the
   "boundedness theorem" replaces Towsner's `(α,k)` pair — and the precise statement of that
   boundedness theorem and its lower-bound corollary for `∀x∃y g_y(x)=0`. If so, that may be a better
   target architecture than Towsner's two-index `(α,k)` system; advice welcome.
3. The Hardy-hierarchy facts the lower bound consumes, stated precisely over a CNF/`ONote`-style
   notation system (so we can discharge our abstract hypotheses `Hmono`, `Hdom`, `HG`):
   - monotonicity `β < α ∧ τ(β) < k ⟹ h_β(k) ≤ h_α(k)` (Towsner Lemma 16.10),
   - Goodstein domination `∀ α<ε₀, ∃ n≥k, G(n) > h_α(n)` (Towsner Thm 7.2 / 9.8),
   and whether mathlib's `ONote.fundamentalSequence` / `ONote.fastGrowing`
   (`Mathlib/SetTheory/Ordinal/Notation.lean`) can supply `h_α` and these facts directly, or whether
   a bespoke Hardy hierarchy + `τ` over `ONote` is needed (and if a Lean/Isabelle/Coq formalization of
   the Hardy hierarchy with these monotonicity/domination lemmas already exists to port).

This unblocks the headline girder M6 (lower bound). Not urgent for *this* lap (we are proceeding on
the calculus design and the gAll-free core), but it is the gating reference for the full Thm 17.1.
