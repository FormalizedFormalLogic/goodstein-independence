# ON-LINE-FINDINGS — Thm 17.1 resolution: independent verification + Hardy-port pointers

**Fulfils:** `ON-LINE-REQUEST.md` lap-4 (the rigorous invariant for the bounded cut-free lower
bound, Towsner Thm 17.1, `I∀` case) — which **lap 5 self-resolved** (commits `a453766`,
`95a4caf`) while this host session was researching it. Per the online-request protocol, the right
move on a self-resolved live lap is to record the research as **independent verification** of the
just-landed proof, plus anything useful for the next step.

**Host session, 2026-06-22.** Sources read: Towsner `papers/towsner-…pdf` §16–§19 (pp. 26–33,
verbatim against the Lean); the box's `ANALYSIS-2026-06-22-bounding-resolution.md` + commit
`a453766`; mathlib `Mathlib/SetTheory/Ordinal/Notation.lean` @ master `2026-06-21`; web (Buchholz–
Wainer 1987, Schwichtenberg–Wainer *Proofs and Computations* Ch. 4, Coq `hydra-battles`, arXiv).

---

## 1. Verdict: the lap-5 resolution is CORRECT ✅ (independent verification)

I reconstructed the fix from scratch (before reading the box's lap-5 work) and arrived at the
**identical architecture**: **∀-inversion removes the universal, then the already-proven gAll-free
Σ₁ fragment bites; domination supplies "out of reach".** The box's `B.allInv` + `lowerBound_hardy`
(axiom-clean) is the standard, correct route. High confidence (~90%). Specific confirmations:

- **The lap-4 gap in Towsner is real**, verified against his p.30 proof of Thm 17.1. His `I∀` case
  picks one large `n ≥ k` and applies the IH at `(β_n, n)`, which requires *every accumulated*
  existential `∃y g_y(m) ∈ Γ'` (with small index `m ≤ k`) to satisfy `G(m) > h_{β_n}(n)`. Since
  `h_{β_n}(n)` is astronomically large for the large `n` forced by domination while `G(m)` is a
  fixed finite number, that condition **fails**. Towsner's exposition glosses this. The box's lap-4
  diagnosis is exactly right — and sharper than my own framing: in a *set* sequent a true atom
  closes the **whole** sequent, so re-expanding `gAll` at a small reachable index and discharging it
  via `trueR` would make `{gAll}` *derivable* under the naive "all out of reach" invariant. So the
  invariant is genuinely not `allI`-preserved.

- **Why inversion dissolves it (the crux):** the obstruction is the **τ-controlled monotonicity**,
  Towsner Lemma 16.10 (`β < α ∧ τ(β) < k ⟹ h_β(k) ≤ h_α(k)`). The hypothesis `τ(β) < k` forces the
  numeric argument to exceed the ordinal-complexity `τ`. The `I∀` rule inflates the numeric bound
  `k → max k n`, and **a witness bound at a larger numeric argument can never be brought back down
  to a smaller one** (monotonicity only goes the wrong way). A small-index accumulated existential
  therefore cannot have its ordinal lifted after the inflation. Carrying the universal through the
  bounding induction is a genuine **dead end** — confirmed from two independent directions. Removing
  the universal first (inversion) means the bounding induction runs on universal-free sequents where
  the Goodstein `I∀` rule **cannot occur** (sub-formula property), so nothing accumulates.

- **The route is the literature-standard one.** "Read numeric bounds off cut-free proofs of Σ₁
  statements, after collapsing/inverting" is **Buchholz–Wainer 1987** (the foundational reference,
  per the Stanford Encyclopedia *Provably Recursive Functions* appendix) and **Schwichtenberg–
  Wainer, *Proofs and Computations*, Ch. 4** (the bounding lemma; the *slow-growing* hierarchy bounds
  existential-truth witnesses in the cut-free system, the *fast-growing* hierarchy once Cut is added).
  The **disjunctive** reading the box used — "*some* formula of Γ is witnessed below `H_α(N)`", not
  *every* existential simultaneously — is exactly the standard form, and is what
  `lowerBound_existential_hardy` already encodes in contrapositive form.

**Bottom line:** the box did not paper over the gap — it found the principled fix. The proof is
sound modulo the one honest remaining obligation, `Hdom` (domination), which is what Part 3 serves.

## 2. One citation correction (faithfulness)

- **arXiv:2003.13207 = Toshiyasu Arai, "Two remarks on proof theory of first-order arithmetic"**
  (MSC 03F30). The box cited this correctly ✓. Verified at arxiv.org/abs/2003.13207. Its Thm 1.1 +
  the Σ₁-witness derivability relation is indeed the cleanest single statement of the bound; PDF now
  on disk (Part 4).
- **arXiv:2109.06258 is by Anton Freund, NOT Pakhomov.** `ON-LINE-REQUEST.md` (lap-5 note) and one
  line of the analysis attributed *"Unprovability in Mathematics: A First Course on Ordinal Analysis"*
  to "Pakhomov" — that's wrong; it is **Freund**, *"Unprovability in mathematics: a first course on
  ordinal analysis"* (matches `papers/SOURCES.md` and the on-disk `freund-unprovability-first-course-
  ordinal-analysis.pdf`). Minor, but worth fixing in any write-up that ships. (Fedor Pakhomov works
  in this area too, which is the likely source of the slip.)

## 3. Pointers for the remaining obligation `Hdom` (Goodstein dominates Hardy) — the genuinely new value

The box's next step is `Hdom : ∃ x, hardy α (max k x) < G x`, noted as "largely a port" from Track-1.
Here is the survey to de-risk that port. **All verified against the actual mathlib source this session.**

### 3a. mathlib has the fast-growing hierarchy `F_α`, NOT the Hardy hierarchy `h_α`
In `Mathlib/SetTheory/Ordinal/Notation.lean` (master `2026-06-21`, = your v4.31.0 pin):
- ✅ `ONote.fundamentalSequence : ONote → (Option ONote) ⊕ (ℕ → ONote)` + `FundamentalSequenceProp`
  + `fundamentalSequence_has_prop` — **the raw material you need is present.**
- ✅ `ONote.fastGrowing : ONote → ℕ → ℕ` with `fastGrowing_zero` (= `Nat.succ`), `fastGrowing_one`
  (= `2*n`), `fastGrowing_two` (= `2^n * n`), `fastGrowing_succ`, `fastGrowing_limit`, and
  `fastGrowingε₀`. **This is the fast-growing `F_α`, which is NOT Towsner's `h_α`.**
- ❌ **No monotonicity / growth lemmas at all** (no `fastGrowing_mono`, no `…_le`, no inflationary
  lemma). `grep "Hardy"` over all of `Mathlib/` returns only `ContinuedFractions` (unrelated). So
  **mathlib has no Hardy hierarchy and no growth facts** — the box's lap-4 note ("`ONote.fastGrowing`
  exists but has NO growth lemmas") is exactly right.

### 3b. Towsner's `h_α` IS the Hardy hierarchy — build it on `fundamentalSequence`, don't reuse `fastGrowing`
Towsner's `h_α(k)` (Def 6.3; the Lemma 16.10 proof computes it as the `m` with
`α[k][k+1]···[k+m] = 0`) is the **Hardy function** `H_α` — the *descent length* along fundamental
sequences. It is distinct from `fastGrowing` (`F_α`). They are related by the standard Wainer identity
`H_{ω^α} = F_α`, so `fastGrowing` is the wrong index unless you compose with `ω^·`. **Recommendation:**
define `hardy` directly over `ONote.fundamentalSequence`, matching Def 6.3:
`H_0(n)=n`, `H_{α+1}(n)=H_α(n+1)`, `H_λ(n)=H_{λ[n]}(n)` — this is the function whose monotonicity is
Lemma 16.10 and whose domination is Thm 7.2/9.8, and it's a much closer fit to your `B`-rule bound
`v ≤ h α k` than `fastGrowing` is. (Mathlib already gives you the `fundamentalSequence` + its prop, so
the well-founded recursion is set up for you.)

### 3c. `τ` (ordinal complexity, Towsner Def 8.1) = the Ketonen–Solovay norm over `ONote`
`τ(α)` is the "norm" controlling when fundamental sequences are monotone (Lemma 16.8:
`β > α ∧ τ(α) < k ⟹ β[k] ≥ α`). Over `ONote` in CNF, `τ` is the bound on the numeric
coefficients/parameters appearing in `α` (the `N(α)` of Ketonen–Solovay). The Lemma 16.10
monotonicity is **false** without this `τ`-control at small arguments — which is precisely the wall
that defeated the lap-4 invariant. Define `τ` recursively on `ONote`'s CNF; the Coq port below has
the canonical version.

### 3d. Existing formalizations to port from (hardest-first, ranked by fit)
1. **Coq `rocq-community/hydra-battles` (Castéran et al.) — the prime reference.** On disk:
   `papers/casteran-hydra-battles-in-coq.pdf`; repo: github.com/rocq-community/hydra-battles. It
   formalizes **both the Hardy and Wainer hierarchies**, the **Ketonen–Solovay machinery** on ε₀
   (the canonical/`{n}`-refined `≤`), and the headline that **ε₀ is the "largest accessible
   ordinal"** (no variant maps every hydra below `µ` for `µ < ε₀`). That largest-accessible result
   **is** the monotonicity-`τ` + domination content you need for `Hmono` and `Hdom`, machine-checked.
   Port the *intuition and lemma shapes* (can't lift Coq → Lean directly, but the def/lemma ladder
   transfers cleanly).
2. **Isabelle AFP `Nested_Multisets_Ordinals` (Felgenhauer et al., FSCD 2017).** On disk:
   `papers/nested-multisets-…pdf`. ε₀ as hereditary multisets + machine-checked **Goodstein
   termination** — but **not** the Hardy hierarchy/growth functions. Good for the ordinal-notation
   layer, *not* for `Hdom`.
3. **New math (not a formalization): arXiv:2604.00771, "Goodstein at the Second Threshold" (2026).**
   Builds a Goodstein process *on the Hardy hierarchy* via two-step collapsing (ID₂ independence).
   Confirms the Hardy-hierarchy framing of Goodstein is current best practice; useful as a modern,
   clean exposition of `H_α`-vs-Goodstein domination to cross-check your bookkeeping.

### 3e. The domination port itself
`Hdom` = "Goodstein length `G` dominates every Hardy `h_α`, `α < ε₀`" (Towsner Thm 7.2 / 9.8). Your
Track-1 (`~/src/lean-formalizations Logic/Goodstein/Domination*.lean`) reportedly has
`goodsteinLength`-domination of `fastGrowing_*`. Two bridges remain, both mechanical-ish:
(a) **`fastGrowing` → `hardy`**: if Track-1 dominates `F_α`, lift to `H_α` via `H_{ω^α} = F_α`
   (so dominating `F_α` gives `H_{ω^α}`; you need it for all `H_β`, `β < ε₀`, but `ε₀` is closed under
   `ω^·`, so `{ω^α : α<ε₀}` is cofinal and this suffices) — **or** redo domination directly against
   the `hardy` you build in 3b (cleaner, avoids the identity).
(b) **`goodsteinLength` → `G`**: relate Track-1's length to this repo's `G` (`= sInf` least-zero
   step, `wip/WitnessBound.lean`). These should be defeq-or-one-lemma apart.

## 4. The optional ask is done
`papers/arai-two-remarks-proof-theory-arithmetic.pdf` (arXiv:2003.13207, Arai; 8 pp, 152 KB,
`%PDF-1.4`, verified) is now on disk for cross-checking the exact Σ₁-witness bound bookkeeping. It is
**gitignored** (`papers/**/*.pdf`), so it won't be committed — add a one-line entry to
`papers/SOURCES.md` on the next lap to catalog it (provenance: open arXiv, downloaded 2026-06-22).

---

### Net
Nothing was open; the lower-bound frontier is correctly resolved. This file is **independent
verification** of `lowerBound_hardy` + a de-risking survey for the `Hdom` port (Part 3) + a citation
fix (Freund ≠ Pakhomov) + the requested Arai PDF. No host git was run during the live lap; the box's
next lap can `git add` this file if it wants it tracked.
