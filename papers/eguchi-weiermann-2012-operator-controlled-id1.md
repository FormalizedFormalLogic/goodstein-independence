# Eguchi & Weiermann (2012) — A Simplified Characterisation of Provably Computable Functions of ID₁ (operator-controlled derivations)

## Provenance

- **File**: `eguchi-weiermann-2012-operator-controlled-id1.pdf` (gitignored; local/bind-mount only)
- **Title**: *A Simplified Characterisation of Provably Computable Functions of the System ID₁ of Inductive Definitions (Technical Report)*
- **Authors**: Naohi Eguchi (Tohoku) & Andreas Weiermann (Ghent)
- **Source**: arXiv:1205.2879v1 [math.LO], 13 May 2012. 27 pp. (Technical report; self-contained with full proofs.)
- **Citation**: N. Eguchi & A. Weiermann, "A simplified characterisation of provably computable functions of the system ID₁ of inductive definitions," arXiv:1205.2879, 2012.
- **Phase**: **fast-growing** (Σ₁-witness read-off machinery) + method template for the **Zᵉ operator-controlled redesign**.

---

## Why this paper matters here (BLUF)

This is the **fullest exposition on disk of a *doubly* operator-controlled derivation calculus** — sequents
`f, F ⊢^α_ρ Γ` controlled by a **pair** of operators:

- **F : Ord → Ord** (ordinal operator, Buchholz-style) — controls *which ordinals may enter* the
  derivation, via coefficient sets `K_Ω`. This is the side that does collapsing / handles the
  Π¹₁-structure.
- **f : ℕ → ℕ** (number-theoretic operator, Weiermann-style) — controls *how large the numeric
  content may grow*, via the norm `N(·)`. This is the side that makes the final Σ₁/Π⁰₂ read-off
  **quantitative**: the Witnessing Lemma bounds every existential witness by `f(0)`.

The authors' own summary of the design (Conclusion, p. 25): *"Ordinal operators contain information
enough to analyse Π¹₁-consequences of the controlled derivations. In contrast, number-theoretic
operators contain information enough to analyse the Π⁰₂-consequences."*

**Why the box should care (three reasons):**

1. **It is the detailed template for the Wainer/Σ₁ read-off (W5).** Weiermann's PA classification
   ([19] = *Classifying the Provably Total Functions of PA*, BSL 12(2):177–190, 2006 — **not on
   disk**) uses exactly this f-side machinery, with no Ω and no F-side, to prove "PA ⊢ Π⁰₂-sentence
   ⟹ witness bounded by a `< ε₀`-iterate of a base function." This TR spells the mechanics out in
   complete proofs (BSL 2006 is terser); for the PA case, *delete everything mentioning Ω, F, K_Ω,
   Cl_Ω, and the impredicative collapse* and what remains is the PA analysis. The remaining axiom
   `wainer_bound_of_pa_proves_goodstein` is precisely a statement of this shape.
2. **The control algebra is structurally non-affine — the exact alternative to the (k,d) budget
   that SPIKE-W4B killed.** In the Zekd calculus every rule was affine (slope 1) in the branch
   index while cut-reduction demanded slope 2; here there is no numeric budget to overflow, because
   the controls are *function-valued* and the elimination lemmas **compose and iterate** them:
   cut-reduction returns `f ∘ g` (Lemma 25), one rank-step of collapse returns `f^{F^α(0)+1}`
   (Lemma 26), full collapse returns `f^{F^α(0)+1}, F^{α+1}` (Lemma 30). Super-affine demand is
   absorbed by moving up a function hierarchy, not by adding to a counter.
3. **The ω-premise conditioning matches the pinned Zᵉ shape.** The (⋀)-rule's premises are
   controlled by the *relativized* pair `f[N(ι)], F[ord(ι)]` — both controls conditioned uniformly
   on the branch index `ι` (`f[n](m) := f(n+m)`, `F[K](ξ) := F(max(K ∪ {ξ}))`). That is the same
   discipline as `Zeh`'s "ω-premises at `H[n]`", and it is family-uniform in the branch index (the
   SPIKE-W4 "never branch-indexed" uniformization requirement, realized here as the official rule
   format).

**Scope caveat**: the paper's target is **ID₁** (one non-iterated inductive definition), so its `Ω`
is impredicative — interpreted as `ω₁^CK`, with a *non-recursive* notation system `OT(F)` that is
only cut back to a recursive `O(Ω)` at the very end (§6). For the g-i target (PA, ε₀) the
impredicative half is machinery we do NOT need; read it as "what the method scales to," and mine the
f-side + the lemma-engine shapes.

---

## What the paper proves

**Corollary 42 (main result)**: a function is provably computable in **ID₁** ⟺ it is elementary in
`{s^α | α ∈ O(Ω)↾Ω}`, where `s` is the successor `m ↦ m+1`, `s^α` is norm-gated transfinite
iteration (below), and `O(Ω)` is a recursive ordinal notation system whose collapsing is done by
iterated *successor*-collapses `S^α(ξ)`. ("Elementary in g" = definable from `s`, projections, 0,
`+`, `·`, cut-off subtraction, and `g` by composition, bounded sums and bounded products.)

En route (§4–5): embedding of ID₁ into an infinitary system **ID₁^∞**, cut-reduction, predicative
cut-elimination, impredicative collapse, boundedness, and a witnessing lemma — all with explicit
operator bookkeeping at every step. ID₁ is PA in the language with new predicates `P_A` (one per
positive operator form `A`), plus (ID1) closure `∀x(A(P_A,x) → P_A(x))` and (ID2) the leastness
schema `∀x(A(F,x) → F(x)) → ∀x(P_A x → F(x))`.

---

## The technical apparatus (extracted for offline use)

### 1. Ordinal terms `OT(F)` and collapsing operators (§3)

Terms built from `0, Ω, +, φ` (binary Veblen), `Ω^α·ξ`, `S(α)` (successor), `E(α)` (least ε-number
above), and function symbols: if `F ∈ F` and `α ∈ OT(F)`, `ξ ∈ OT(F)↾Ω`, then `F^α(ξ) ∈ SC`
(strongly critical) and `F^α ∈ F`. Base symbols `S, E ∈ F`. `Ω` is interpreted as `Ω₁ = ω₁^CK`, so
`OT(F)` is deliberately **non-recursive**.

**Coefficient sets** (Def 2.1): for `α =_NF Ω₁^{α₁}·β₁ + ⋯ + Ω₁^{α_l}·β_l < ε_{Ω₁+1}`,

```
K_Ω α = {β₁, …, β_l} ∪ K_Ω α₁ ∪ ⋯ ∪ K_Ω α_l        (so K_Ω α ⊆ Ord↾Ω, finite)
```

**Collapsing hierarchy** (Def 2.2): for an ordinal function `F : Ord → Ord`,

```
F⁰(ξ) = F(ξ)
F^α(ξ) = min{ γ | ω^γ = γ,  K_Ωα ∪ {ξ} < γ,  and
              (∀η<γ)(∀β<α)(K_Ωβ < γ ⟹ F^β(η) < γ) }
```

Prop 4: if `F` is Σ₁-definable in `L_{Ω₁}` and maps below `Ω₁`, so is each `F^α` (this is where
`Ω₁ = ω₁^CK`'s admissibility is used). Cor 8: `F^α(ξ) < Ω` for `ξ < Ω`.

**Monotonicity hypothesis** used throughout, `(HYP(F))`: `η < F(ξ) ⟹ F(η) ≤ F(ξ)` (a "flatness"
condition; survives relativization `F[K]`).

**Norm** (Def 13.3) — the number-theoretic size of an ordinal term:

```
N(0)=0   N(Ω)=1   N(S α)=N(E α)=N(α)+1   N(α+β)=N(α)+N(β)
N(φαβ)=N(α)+N(β)+1   N(Ω^α·ξ)=N(α)+N(ξ)+1   N(F^α(ξ)) = N(F(ξ)) + N(α)
```

extended to closed PA-terms by `N(t) := val(t)`. So `N(ω^0·m) = m`: numerals and their ordinal
codes have the same size. **The norm is what replaces fundamental sequences everywhere.**

### 2. Norm-gated transfinite iteration `f^α` (Def 16) — fundamental-sequence-free

For `f : ℕ → ℕ` satisfying `(f.1)` `f` strictly increasing with `2m+1 ≤ f(m)` (hence
`n + f(m) ≤ f(n+m)`) and `(f.2)` `2·f(m) ≤ f(f(m))`:

```
f⁰(m) = f(m)
f^α(m) = max{ f^β(f^β(m)) | β < α  and  N(β) ≤ f[N(α)](m) }     (α > 0)
```

Which `β < α` may be used is gated by the **norm bound** `N(β) ≤ f(N(α)+m)` — no fundamental
sequences needed, and the definition works for the non-recursive `OT(F)` too. Key facts:
`s^n(m) = m + 2^n`, `s^ω(m) = m + 2^{m+3}` (Example 18); `N(α) ≤ f^{F^α(0)}(0)` (Lemma 19);
`(f^α)^β(m) ≤ f^{F^{Ω·α+β}(0)}(m)` (Lemma 20 — folds nested iteration back into one level);
`(f[n])^α(m) ≤ f^{α+2}(m)` for `n ≤ m` (Cor 22).

### 3. The infinitary system ID₁^∞ (§4)

Language `L*`: PA plus stage-predicates `P_A^{<α}, ¬P_A^{<α}` for `α ∈ (OT(F)↾Ω) ∪ {Ω}` (write
`P_A^{<Ω} = P_A`). Negation by de Morgan; each sentence is `⋀`-type or `⋁`-type via `≃` (Def 14):

```
¬P_A^{<α}t ≃ ⋀_{ξ<α} ¬A(P_A^{<ξ}, t)        P_A^{<α}t ≃ ⋁_{ξ<α} A(P_A^{<ξ}, t)
∀xA ≃ ⋀_{t closed} A(t)                      ∃xA ≃ ⋁_{t closed} A(t)
```

Complexity measures: rank `rk(P_A^{<α}t) = ω·α`, `rk(A∧B)=max+1`, `rk(∀xA)=rk(A)+1`; Π/Σ-coefficient
sets `k^Π(A), k^Σ(A)` (the stage ordinals occurring positively/negatively), `k_Ω = k↾Ω`; `ord(ι)` =
the stage ordinal of a branch index (0 for closed terms); `N` extended to indices via `val`.

### 4. **Definition 23 — the controlled derivability relation** (the paper's core)

`f, F ⊢^α_ρ Γ` for `α < ε_{Ω+1}`, `ρ < Ω·ω`, `Γ` a finite sequent, **provided the side condition**

```
(HYP(f;F;α)):   max{N(F(0)), N(α)} ≤ f(0)   and   K_Ω α < F(0)
```

holds and one of the following rules applies (notation: `f[n](m) := f(n+m)`,
`F[K](ξ) := F(max(K∪{ξ}))`, `F[μ] := F[{μ}]`; `TRUE₀` = true closed PA-literals):

- **(Ax1)** some PA-literal pair `{¬A(s), A(t)} ⊆ Γ` with `val(s) = val(t)`.
- **(Ax2)** `Γ ∩ TRUE₀ ≠ ∅`.
- **(⋁)** some `A ≃ ⋁_{ι∈J} A_ι ∈ Γ`, some `α₀ < α`, `ι₀ ∈ J` with **`N(ι₀) ≤ f(0)`** and
  **`ord(ι₀) < min{α, F(0)}`**, and `f, F ⊢^{α₀}_ρ Γ, A_{ι₀}`.
- **(⋀)** some `A ≃ ⋀_{ι∈J} A_ι ∈ Γ` with `N(max k_Ω^Π(A)) ≤ f(0)`, `k_Ω^Π(A) < F(0)`, and for
  every `ι ∈ J` some `α_ι < α` with **`f[N(ι)], F[ord(ι)] ⊢^{α_ι}_ρ Γ, A_ι`**.
- **(Cl_Ω)** (closure) some closed `t`, `α₀ < α`, with `P_A^{<Ω}t ∈ Γ`, `Ω < α`, and
  `f, F ⊢^{α₀}_ρ Γ, A(P_A^{<Ω}, t)`.
- **(Cut)** some `⋁`-type `C`, `α₀ < α`, with `max{lh(C), N(max k_Ω^Π(C)), N(max k_Ω^Σ(C))} ≤ f(0)`,
  `k_Ω(C) < F(0)`, `rk(C) < ρ`, and both `f, F ⊢^{α₀}_ρ Γ, C` and `f, F ⊢^{α₀}_ρ Γ, ¬C`.

Read the division of labor off the side conditions: **every ordinal parameter must have its
`K_Ω`-coefficients below `F(0)` (F-side) and its norm below `f(0)` (f-side)**. The pair `(f,F)` is
called the operators *controlling* the derivation.

### 5. The lemma engine (§4) — with the operator updates, the part worth copying

| Lemma | Statement shape | **Control update** |
|---|---|---|
| 24 Inversion | `A ≃ ⋀A_ι`, `f,F ⊢^α_ρ Γ,A` ⟹ `⊢^α_ρ Γ,A_ι` | `f[N(ι)], F[ord(ι)]` |
| 25 Cut-reduction | `C ≃ ⋁`, `rk(C)=ρ≠Ω`: `f,F ⊢^α_ρ Γ,¬C` & `g,F ⊢^β_ρ Γ,C` ⟹ `⊢^{α+β}_ρ Γ` | **`f ∘ g`** |
| 26 one rank-step above Ω | `f,F ⊢^α_{Ω+k+2} Γ` ⟹ `⊢^{Ω^α}_{Ω+k+1} Γ` | **`f^{F^α(0)+1}`** |
| 27 Predicative cut-elim | `{α,β,γ}<Ω`, `f^γ,F ⊢^β_{ρ+ω^α} Γ` ⟹ `⊢^{φαβ}_ρ Γ` | **`f^{F^{Ω·α+γ+β}(0)+1}`** |
| 29 Boundedness | `f,F ⊢^α_ρ Γ,A` ⟹ `⊢^α_ρ Γ,A^ξ` (replace `P^{<Ω}` by `P^{<ξ}`), any `α ≤ ξ ≤ F(0)` with `N(ξ) ≤ f(0)`, `K_Ωξ < F(0)` | unchanged |
| 30 **Impredicative cut-elim (collapse)** | `f,F ⊢^α_{Ω+1} Γ` ⟹ `⊢^{F^α(0)}_{F^α(0)} Γ` | **`f^{F^α(0)+1}, F^{α+1}`** |
| 31 **Witnessing** | `Γ = ∃x₀B₀,…,∃x_{l-1}B_{l-1}` (`B_j` Δ⁰₀), `f,F ⊢^α_0 Γ` ⟹ witnesses exist with **`max{m_j} ≤ f(0)`** | terminal read-off |

Lemma 30 is the collapsing theorem: derivation bound *and* cut rank both drop to `F^α(0) < Ω`, at
the price of raising the ordinal operator to `F^{α+1}` and iterating the numeric operator
`F^α(0)+1`-fold. Lemma 31's proof is a bare induction on the cut-free derivation: at each (⋁) the
witnessing term `t` satisfies `val(t) = N(t) ≤ f(0)` — **the numeric content of the whole
derivation is carried in `f(0)` the entire way down**. This is the mechanism that turns
cut-elimination into an explicit subrecursive bound.

### 6. Embedding ID₁ → ID₁^∞ (§5) and the read-off chain

With base ordinal operator `E` (least-ε-number-above; `HYP(E)` holds):

- **Lemma 32 (Tautology)**: `f[n], E[k_Ω(A)] ⊢^{rk(A)·2}_0 Γ, ¬A(s), A(t)` for `val(s)=val(t)`,
  `n := max{N(rk(A)), N(max k_Ω^Π(A)), N(max k_Ω^Σ(A))}`.
- **Lemma 33**: a cut-free G3m predicate-logic proof of height `h` embeds with `f[m+k]`,
  bound `Ω·2+k`, cut-rank 0 (induction on `h`, `k` from `h`).
- **Lemma 34 (induction axioms)**: `f[N(rk(A))+m+1], E ⊢^{(rk(A)+m+1)·2}_0 Γ, ¬A(0), ¬∀x(A→A(Sx)), A(t)`
  for `val(t)=m` — the numeral's value enters the *f-relativization*, not the ordinal bound.
- **Lemma 35 / 36 ((ID2) axioms)**: main induction on stage `ξ ≤ Ω`, side induction on
  `rk(B(P_A^{<ξ}))`; conclusion for the universal closures at bound `Ω·2+ω`, cut-rank 0.
- **Theorem 37 (the pipeline)**: `ID₁ ⊢ A`, `A ≡ ∀x∃y B(x,y)` Π⁰₂ ⟹ embed
  (`f[c], E ⊢^{Ω·3}_{Ω+d+1} A`) → `d`-fold Lemma 26 (rank down to `Ω+1`; ordinals `γ_{n+1} = E^{γ_n}(0)+1`,
  bounds tower `Ω_{n+1}(α) = Ω^{Ω_n(α)}`) → Lemma 30 (collapse below `Ω`) → Lemma 27 (cut-rank → 0
  at bound `φβ β`-shape) → set `f = s^ω` → Lemma 20 (flatten nested iterates) → `l`-fold Inversion
  (plug in the numerals `m`) → Lemma 31: `∃n ≤ s^α(m₀+⋯+m_{l-1})` with `B(m,n)` true, for a
  **φ-free** `α ∈ OT(F)↾Ω`.
- **Cor 38**: every ID₁-provably-computable function is elementary in `{s^α | α ∈ OT(F)↾Ω}`.
- **§6**: recursive notation system `O(Ω)` (collapsing only via iterated successor-collapses
  `S^α(ξ)`); Lemmas 40–41 majorize every φ-free `OT(F)`-term by an `O(Ω)`-term (using `E(α) ≤ S¹(α)`
  + Lemma 11 `(F^α)^β(ξ) ≤ F^{α+β}(ξ)`); **Cor 42** (the ⟺, above). The "if" direction is quoted
  from the standard fact that ID₁ proves well-ordering of each initial segment of `O(Ω)` (Pohlers,
  Handbook §29) — not re-proved here.

---

## Mapping to the Zᵉ redesign (`Zeh α e H c Γ`)

- **`H` (set-valued Buchholz operator, cf. Freund's Def 5.4 / Buchholz's `H_γ`) vs this paper's `F`
  (ordinal-valued function)**: interconvertible control disciplines. `H`-style says "all parameters
  of the derivation lie in the closed set `H[Θ]`"; `F`-style says "`K_Ω`-coefficients of all
  parameters lie below `F(0)`," with closure properties packaged in `HYP(F)` + the relativization
  `F[K]`. Freund/Buchholz's `H_γ(X) ∩ Ω ⊆ ψ`-style capture ↔ this paper's `F^α(0)`-collapse. If
  `Zeh` keeps a set-operator `H`, this paper still transfers: read `K_Ωα < F(0)` as `α ∈ H` and
  `F[ord(ι)]` as `H[ord(ι)]`.
- **What `Zeh` may be missing that this paper supplies: the second (numeric) coordinate.** The g-i
  someK/Σ₁ lane needs a quantitative exit (`∃K` witness bounds, Hardy/Wainer read-off). The (k,d)
  pair tried to carry that numerically and died affine (SPIKE-W4B). Here the numeric coordinate is
  a *function* `f` with composition/iteration as the update algebra, and the witness bound falls
  out as `f(0)` at the end (Lemma 31). For the M2-bridge/Σ₁-definability worry: `f` ranges over a
  concrete subrecursive class (`s^α` iterates, Def 16 is arithmetically definable given the notation
  system), which is exactly what a Σ₁ read-off wants.
- **PA specialization** (what the Wainer-debt discharge actually needs): drop `Ω, F, K_Ω, Cl_Ω`,
  Lemmas 26/29/30; keep the norm `N`, the `f`-control with `(f.1)/(f.2)`, `f^α` (Def 16), rules
  (Ax1/Ax2/⋁/⋀/Cut) with the `N(ι₀) ≤ f(0)` / `f[N(ι)]` discipline, and the chain
  Tautology → induction-embedding → Cut-reduction (`f∘g`) → predicative cut-elimination
  (Lemma 27's `Ω`-free shadow: `f^γ ⊢^β_{ρ+ω^α} ⟹ f^{…} ⊢^{φαβ}_ρ`; for PA one only needs the
  `α = 1` instances iterated, i.e. the usual `ω^β`-tower staying below ε₀) → Witnessing.
  That is Weiermann [19] (BSL 2006). The bound comes out as: PA ⊢ `∀x∃yB` ⟹ witnesses `≤ s^α(m)`
  for some `α < ε₀`-notation — the `wainer_bound` statement, with `s^α` a Hardy-class function
  (compare the repo's Hardy bank; `s^α ≈ H_α` up to the norm-gating details).
- **The uniformization lesson W4 already learned, confirmed as official rule format**: premises of
  the ω-rule are controlled by `f[N(ι)], F[ord(ι)]` — conditioned on the branch index through a
  *fixed* family-uniform recipe, never through per-branch ad-hoc budgets.

## Pointers into the rest of the on-disk corpus

- **Buchholz–Wainer 1987** (`buchholz-wainer-1987-…pdf`) — proves the PA classification both
  directions but with classical (non-operator) ω-logic bookkeeping; this TR is the operator-
  controlled modernization of the same pipeline (for a stronger system).
- **Freund, second course** (`freund-second-course-ordinal-analysis.pdf`) — §5 has the set-operator
  (`H : P → P`) presentation and Buchholz's `H_γ`; use it side-by-side with this paper's
  function-operator presentation.
- **Not on disk, referenced here**: [19] Weiermann BSL 12(2):177–190 (2006) *Classifying the
  Provably Total Functions of PA* (the PA case of this machinery — the single most relevant
  paywalled item for W5); [7] Buchholz MLQ 47(3):363–396 (2001) *Finitary Treatment of Operator
  Controlled Derivations* — **finitary** operator-controlled derivations, i.e. the shape a Lean
  in-kernel formalization actually wants (no genuinely infinite ω-branching); [8]
  Buchholz–Cichon–Weiermann MLQ 40:273–286 (1994) uniform fundamental sequences/hierarchies (the
  norm-vs-fundamental-sequence trade); [20] Weiermann 2011 draft *A Quick Proof-theoretic Analysis
  of ID₁* (7 pp., source of the `OT(F)` system).

## Faithfulness caveats

- This is the **arXiv v1 technical report**; lemma/def numbers cited above are v1's. Cite as arXiv.
- The paper's `Ω` is `ω₁^CK` and `OT(F)` is non-recursive **by design** (Prop 4 leans on
  admissibility of `L_{Ω₁}`); only §6's `O(Ω)` is recursive. Don't import `OT(F)` wholesale into a
  formalization — for PA/ε₀ none of that is needed.
- The `(f.1)/(f.2)` conditions on `f` are load-bearing in *every* norm computation (Lemmas 19–22,
  and inside each elimination lemma's arithmetic). `s^ω` satisfies them; an arbitrary base function
  does not.
- Lemma 27 as stated has the `f^γ` premise shape (the input operator is already an iterate);
  applying it needs the Lemma 20/Cor 22 flattening arithmetic, which is where most of the
  side-condition sweat lives (pp. 14–17).
