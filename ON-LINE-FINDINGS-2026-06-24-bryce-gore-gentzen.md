# ON-LINE-FINDINGS — Bryce–Goré Coq Gentzen `Con(PA)` formalization (for the C0.5 Foundation→Z bridge)

**Fulfils:** `ON-LINE-REQUEST.md` (lap 62) — the Bryce–Goré machine-checked `Con(PA)` via ordinal
cut-elimination (arXiv:2603.00487, repo `aarondroidbryce/Gentzen`). Three priority asks + a Foundation
`PA_delta1Definable` check.

**Host session, 2026-06-24.** Sources: the **whole repo cloned to `~/src/Gentzen`** (box-readable per
operator note — read it directly; commit `f34542a`, 2023-09-01, 18,074 lines Coq) + the arXiv HTML
(faithful prose, not LaTeX) + the live Foundation pin source. Everything below is read off the actual
`.v` files; file:line pointers are into `~/src/Gentzen/theories/…`. Faithfulness over fluency: the Coq
text **is** the ground truth (more faithful than any paper paraphrase), so I quote declarations verbatim.

> ⚠️ **The repo has NO LICENSE file** — so I did **not** vendor its source into this (Apache-licensed)
> repo. The full source is at `~/src/Gentzen` for you to read directly; `papers/bryce-gore-gentzen/` holds
> only a provenance stub. Excerpts below are short fair-use quotes for the blueprint.

---

## TL;DR — verdicts

1. **The bridge blueprint is real and directly portable.** Their PA→PA_ω simulation is **not** a monolithic
   admissibility proof. It is a **three-layer split**: (a) a typed intermediate calculus that is
   syntactically PA but *annotated with the target ordinal+degree*, (b) a cheap `Base → Annotated`
   existence lemma, (c) the real work `Annotated → PA_ω` by induction-on-derivation, **one case per axiom /
   rule**. Port that *shape* for C0.5, not the infinitary internals. (§1)
2. **Per-rule ordinal arithmetic confirmed** and tabulated for cross-checking your `iord`/`iR`. Their
   ω-rule premises carry a **uniform** ordinal across all witnesses (pure-Gentzen, no `max{k,n}` —
   consistent with the earlier `omega-rule-commuting-bound` findings). Their cut-elim per-round base is
   **`2^α`** (`ord_2_exp`), *not* Towsner's `ω^α` or Buchholz's `3^α`. (§2)
3. **Main theorem = `PA_Consistent`** (`gentzen.v:290`); ordinal library = **Pierre Castéran & Evelyne
   Contejean's** Cantor/ε₀ Coq library, with their own CNF `ord` type. **Route caveat confirmed:** they use
   infinitary **PA_ω** (a real ω-rule over all closed terms); you use finitary **Z**. Port the bridge
   shape, not the line counts. (§3)
4. **Lower priority — `PA_delta1Definable` is STILL an `axiom`.** Identical in the pinned `gotrevor/
   Foundation` *and* upstream `FormalizedFormalLogic/Foundation` main: `Examples.lean:17`, with a standing
   `TODO`. No later version proved it. (§4)

---

## §1 — Item 1: the `PA_closed_PA_omega` bridge (the C0.5 blueprint)

The bridge lives entirely in **`theories/Logic/Peano.v`** (1215 lines — request's "~1,215" was exact). It
is a **three-layer** structure, not one lemma:

### Layer A — `Peano_Theorems_Base` (`Peano.v:21`): the *real* finitary PA
A Hilbert-style system, **no ordinals**: `FOL1`–`FOL5`, `MP`, `UG`, the equality axioms (`equ_trans`,
`equ_succ`, `non_zero`, `succ_equ`), `pl0/plS/ml0/mlS`, and `induct` (the induction schema). This is the
analogue of Foundation's `(𝗣𝗔).DerivationOf` — the thing you start from.

### Layer B — `Peano_Theorems_Implication` (`Peano.v:67`): PA **annotated with `(degree, ordinal)`**
```coq
Inductive Peano_Theorems_Implication : formula -> nat -> ord -> Type :=
| I_FOL1 : ... 0 (ord_succ (ord_succ (nat_ord (num_conn A + num_conn A))))
| I_MP   : Peano_Theorems_Implication (A ~> B) d1 alpha ->
           Peano_Theorems_Implication A d2 beta ->
           Peano_Theorems_Implication B (max (max d2 d1) (num_conn (neg A)))
                                         (ord_succ (ord_succ (ord_max beta alpha)))
| I_UG   : ... -> Peano_Theorems_Implication (univ n A) d (ord_succ alpha)
| I_induct : ... (num_conn A + 1) (ord_succ (ord_succ (cons (nat_ord 1) 0 Zero))). (* = ω·1 = ω *)
```
**This is the load-bearing idea.** Every PA axiom/rule is given an *explicit* `(d, α)`. All axioms get
**finite** ordinals (`nat_ord k`) **except `I_induct`**, which is the only one that reaches `ω`
(`cons (nat_ord 1) 0 Zero`). `MP`/`UG` propagate via `ord_max`/`ord_succ`. This layer is "PA, but every
derivation already knows the ordinal it will cost in the infinitary system."

### Layer C — three lemmas wire it together
- **`PA_Base_equiv_PA_Implication`** (`Peano.v:1070`): `Peano_Theorems_Base A → {d & {α & Peano_Theorems_Implication A d α}}`.
  Just `induction` on the Base derivation, emitting the `(d,α)` from Layer B per case. **Cheap.**
- **`PA_closed_PA_omega`** (`Peano.v:489`): **the real work.**
  ```coq
  Lemma PA_closed_PA_omega : forall (A : formula) (d : nat) (alpha : ord),
    Peano_Theorems_Implication A d alpha ->
      (forall (c : c_term), PA_omega_theorem (closure A c) d alpha).
  ```
  `induction T1` over the **16** `Implication` constructors; each case discharged by an explicit sequence
  of PA_ω rule applications (`exchange*/contraction*/weakening/LEM/cut3/demorgan2/quantification*/w_rule`).
  Note it proves the **universal closure** `closure A c` (free variables universally closed over a
  `c_term`), and **preserves both `d` and `α` exactly**.
- **`PA_Base_closed_PA_omega`** (`Peano.v:1206`): the composite `Base A → ∀c, {d & {α & PA_omega_theorem (closure A c) d α}}`. **= paper's Theorem 11.**

### What to copy for C0.5 (`(𝗣𝗔).DerivationOf d ⊥ → ∃ z, ZDerivesEmpty z`)
The precedent says: **don't** prove the bridge as one giant admissibility lemma. Instead
1. define an **intermediate inductive** that mirrors Foundation-PA's derivation constructors but is
   *annotated with the Z-side data* you need downstream (the Z-ordinal / degree / whatever `ZDerivesEmpty`
   consumes) — their Layer B;
2. a **cheap** `Foundation-PA-derivation → annotated` existence lemma (induction on the Foundation
   derivation) — their Layer A→B;
3. the **real** `annotated → Z` map by induction-on-derivation, **one case per PA axiom/rule**, each
   emitting the explicit Z construction — their Layer C `PA_closed_PA_omega`.

Their 16-case `I_*` ordinal table is your per-axiom Z-arithmetic template. The "only induction reaches `ω`,
the rest are finite" structure is likely to recur on the Z side too (the induction schema is where the
transfinite content enters). **This is exactly the "one unplanned load-bearing seam" the lap-61 judge
flagged — and they have a worked precedent for it.**

---

## §2 — Item 2: ordinal assignment (`proof_trees.v`) + cut-elim reduction `R` (`cut_elim.v`)

### Ordinal/degree assignment — `theories/Logic/proof_trees.v`
- `ptree` (`:13`) — the proof-tree datatype, one constructor per PA_ω rule (`weakening_ad`, `cut_ca`,
  `cut_ad`, `cut_cad`, `w_rule_a`, `w_rule_ad`, …).
- `ptree_ord : ptree -> ord` (`:160`) — the **ordinal-height read-off**. Verbatim key cases:
  ```
  weakening_ad …            => ord_succ alpha
  demorgan_ab/abd …         => ord_succ (ord_max alpha1 alpha2)
  negation_a/ad …           => ord_succ alpha
  quantification_a/ad …     => ord_succ alpha
  w_rule_a/ad …             => ord_succ alpha          (* the ω-rule *)
  cut_ca  …                 => ord_succ (ord_max alpha1 alpha2)
  cut_ad  …                 => ord_succ (ord_succ (ord_max alpha1 alpha2))
  cut_cad …                 => ord_succ (ord_max alpha1 alpha2)
  node A / exchange / contraction / ord_up => Zero / alpha / alpha
  ```
- `ptree_deg : ptree -> nat` (`:115`) — cut-degree read-off.
- `valid : ptree -> Type` (`:205`) — the well-formedness invariant tying every node's `(formula,deg,ord)`
  to its premises; crucially `ord_up` requires **`nf alpha`** (normal-form / `< ε₀`), and `ptree_ord_nf`
  (`:441`) proves every valid tree's ordinal is `nf`. (Your `iord` should likewise carry an NF invariant.)
- `P_proves` (`:301`) / `provable A d α := {P & P_proves P A d α}` (`:305`).

### Per-rule arithmetic — `PA_omega.v:24` (matches `ptree_ord` exactly). Cross-check anchors for `iord`/`iR`:
| PA_ω rule | ordinal out | degree out |
|---|---|---|
| `axiom` | `Zero` | `0` |
| `weakening` | `ord_succ α` | `d` |
| `negation1/2`, `quantification1/2` | `ord_succ α` | `d` |
| `demorgan1/2` | `ord_succ (ord_max α1 α2)` | `max d1 d2` |
| **`w_rule1/2` (ω-rule)** | `ord_succ α` | `d` |
| `cut1`/`cut3` | `ord_succ (ord_max α1 α2)` | `max (max d1 d2) (num_conn (neg A))` |
| `cut2` | `ord_succ (ord_succ (ord_max α1 α2))` | `max (max d1 d2) (num_conn (neg A))` |
| `ord_incr` | any `nf β > α` | `d` |
| `deg_incr` | `α` | any `d' > d` |

⚠️ **The ω-rule is `uniform`:** `w_rule1` (`PA_omega.v:100`) takes
`g : forall (c : c_term), PA_omega_theorem (substitution A n (projT1 c)) d alpha` — **the same `(d,α)` for
every closed witness `c`**, concluding `(d, ord_succ α)`. There is **no per-premise `max{k,n}` index** (this
is pure-ordinal Gentzen/Buchholz `Z∞`, exactly the structure the prior `omega-rule-commuting-bound`
findings said makes the commuting case "one line"). If your `Z` ω-rule threads a numeric witness index, this
is the divergence point.

### Cut-elimination reduction `R` — `theories/Logic/cut_elim.v`
- **`cut_elimination : ptree -> ptree`** (`:231`) — **one round** of cut-elimination. Dispatches on the cut
  formula's shape into the three principal-formula reduction families
  `cut_elimination_atom` (`:22`) / `cut_elimination_neg` (`:65`) / `cut_elimination_lor` (`:175`). **This is
  their "`R`".** (Helpers: `contraction_help :156`, `associativity_1'/2' :100/:112`.)
- Three correctness theorems about one round:
  - `cut_elimination_formula` (`:259`): `ptree_formula (cut_elimination P) = ptree_formula P` (end-sequent
    preserved).
  - **`cut_elimination_ord`** (`:317`): `ord_ltb (ord_2_exp (ptree_ord P)) (ptree_ord (cut_elimination P)) = false`
    — i.e. **one round costs at most `α ↦ 2^α`**. ⚠️ base **`2^α`** (`ord_2_exp`, `ordinals.v:524`), NOT
    `ω^α`/`3^α`. Cite the right base when cross-checking `iR`.
  - `cut_elimination_valid` (`:387`): the reduct is `valid`.
- Heavy lifting (commuting + principal cases): `cut_elim_aux0` (`:753`, ~420 lines), via `cut_remove`
  (`:748`), `cut_elim_ord_Zero` (`:486`), `cut_elim_ord_one` (`:601`).
- **Top theorem `cut_elim`** (`:1198`):
  ```coq
  Theorem cut_elim : forall (A : formula) (d : nat) (alpha : ord),
    provable A d alpha -> {beta : ord & provable A 0 beta}.
  ```
  Full elimination to **degree 0** (cut-free). NB the resulting `beta` is **existential** — they never
  need a closed-form bound, only its existence + `nf` (`< ε₀`). That is enough for consistency. (If your Z
  route also only needs "some `< ε₀` ordinal exists cut-free", you can mirror this and skip a tight
  closed-form bound.)

---

## §3 — Item 3: main theorem, ε₀-library, route caveat

### Main theorem — `theories/gentzen.v:290`
```coq
Lemma PA_Consistent : forall A, Peano_Theorems_Base A -> Peano_Theorems_Base (neg A) -> False.
```
Proof architecture (all in `gentzen.v`, 296 lines):
- `danger := atom (equ zero (succ zero))` (`:34`) — the formula **`0 = S0`**; `dangerous_disjunct A`
  (`:36`) = "`A` is a disjunction containing `0=S0`".
- `danger_not_deg_0` (`:121`): a dangerous disjunct **cannot** be proved at **degree 0** (cut-free) — by
  induction on the cut-free tree (atomic axioms are *correct*, so a false atom can't appear).
- `provable_not_danger` (`:219`): any `provable A` → `cut_elim` to degree 0 → `danger_not_deg_0` → ⊥. So no
  dangerous disjunct is provable.
- `inconsistent_danger` (`:273`): `⊢ A` and `⊢ ¬A` in PA_ω → `cut2` them (+ weakening) → `⊢ 0=S0` → not
  dangerous-provable → ⊥.
- `PA_Consistent` (`:290`): embed both via `PA_Base_closed_PA_omega` (`closure_neg` aligns the negation),
  then `inconsistent_danger`.

So the spine is exactly: **real PA → (ordinal-annotated) PA → PA_ω → cut-elimination → no cut-free proof of
`0=S0` → consistency.**

### Ordinal-notation library
- **Pierre Castéran & Evelyne Contejean's** Coq ordinal library (the `Cantor`/`Epsilon0` development;
  README: `http://www.labri.fr/~casteran/Cantor/Kantor.tar.gz`). Imported under `theories/Casteran/`
  (`rpo.v` = the **recursive path ordering** giving well-foundedness; `term.v`, `dickson.v`, `closure.v`,
  `AccP.v`, …). **The "reportedly Castéran" claim is CONFIRMED.**
- Their own ε₀ representation (`theories/Maths/ordinals.v:12`):
  ```coq
  Inductive ord : Set := Zero : ord | cons : ord -> nat -> ord -> ord.
  ```
  `cons a n b` = `ω^a · (n+1) + b` (Cantor normal form). `nf : ord -> Prop` (`:163`) = the CNF/descending
  predicate; ops `ord_lt`(`:18`)/`ord_ltb`(`:206`), `ord_succ`(`:569`), `ord_max`, `ord_add`(`:504`),
  `ord_mult`(`:519`), `ord_2_exp`(`:524`), `nat_ord`(`:174`). Well-foundedness of `ord_lt` on `nf` ordinals
  (via the Castéran RPO) is the meta-engine that makes the cut-elim recursion terminate.

### ⚠️ Route caveat (CONFIRMED — this is finitary-Z vs infinitary-PA_ω)
Their target is the **infinitary PA_ω**: the ω-rule `w_rule1/2` literally takes a Coq function
`forall c : c_term, …` over **all closed terms** (an actual infinitary premise), and proofs are infinitely-
branching `ptree`s. Your route is **finitary Z** (Buchholz-Z, no infinitary branching). **Port the bridge
*shape* (§1) — the typed-intermediate-calculus + induction-on-derivation — NOT the infinitary specifics or
their line counts.** Their `closure A c` device (universally closing free vars before entering PA_ω) is
specific to the infinitary side; Z handles free variables differently.

### Paper / authors (arXiv:2603.00487, Feb-2026 DRAFT)
"*A Formally Verified Constructive Proof of the Consistency of Peano Arithmetic Using Ordinal Assignments*",
**Aaron Bryce** (Mathematical Sciences Institute, ANU) & **Rajeev Goré** (FIT, Monash). It is a
constructive Coq redo of Gentzen 1936 (Gödel's reformulation). Headline meta-claim relevant to you: the
ordinal assignments to the Peano axioms **must stay `< ε₀`**, and the whole argument needs no more than
**PRA + transfinite induction up to ε₀** — the explicit ordinal bookkeeping (Layer B) is the paper's named
contribution over Morgan Sinclaire's earlier (incomplete-on-this-point) formalization, which "gave no
guarantee that the PA-axiom ordinal assignments lie within the cut-elimination bound."

---

## §4 — Lower priority: is `PA_delta1Definable` still an axiom?

**YES — still an `axiom`, both in your pin and upstream.** In the live Foundation pin
(`gotrevor/Foundation` rev `a5eda23`) at
`.lake/packages/Foundation/Foundation/FirstOrder/Incompleteness/Examples.lean`:
```coq
/-! *TODO: Prove `𝗜𝚺₁` and `𝗣𝗔` are Δ₁-definable.* -/    -- line 10
axiom ISigma1_delta1Definable : 𝗜𝚺₁.Δ₁                  -- line 15
axiom PA_delta1Definable : 𝗣𝗔.Δ₁                         -- line 17
attribute [instance] ISigma1_delta1Definable PA_delta1Definable   -- line 19
```
I fetched upstream `FormalizedFormalLogic/Foundation` **main** (`Examples.lean`) live — **byte-identical**
on these lines (axiom at :17, same TODO at :10). So **no later Foundation version has proved it**;
scoping the induction-scheme-Δ₁ arithmetization is genuinely open work upstream, not something a bump
would hand you. Both `𝗜𝚺₁.Δ₁` and `𝗣𝗔.Δ₁` are axiom-instances; the Goodstein chain inherits both
transitively through whatever uses `𝗣𝗔.Δ₁` as an instance.

---

## Sources
- **`~/src/Gentzen`** — full clone (commit `f34542a`, 2023-09-01), read directly. Key files:
  `theories/gentzen.v` (main thm), `theories/Logic/Peano.v` (bridge), `theories/Logic/PA_omega.v` (system),
  `theories/Logic/proof_trees.v` (ord/deg/valid), `theories/Logic/cut_elim.v` (reduction `R`),
  `theories/Maths/ordinals.v` (ε₀ type), `theories/Casteran/` (Castéran RPO ordinal library).
- arXiv:2603.00487, Bryce & Goré — abstract/intro (prose) for the main-thm meta-claim, ε₀-bound, authors.
  https://arxiv.org/html/2603.00487
- Predecessor: Morgan Sinclaire, "Formally Verifying Peano Arithmetic" (Boise State thesis) — the repo's
  acknowledged inspiration. https://scholarworks.boisestate.edu/cgi/viewcontent.cgi?article=2662&context=td
- Foundation `Examples.lean` — live pin (`gotrevor/Foundation` a5eda23) + upstream
  `FormalizedFormalLogic/Foundation` main (fetched via GitHub API this session). `PA_delta1Definable` axiom.

---

### Net
The Bryce–Goré development gives you a **worked, machine-checked precedent for the C0.5 seam**: a
three-layer PA→infinitary-calculus bridge (real PA → ordinal-annotated PA → PA_ω, by induction-on-
derivation with an explicit per-axiom ordinal table). Copy the *shape* (§1); cross-check your `iord`/`iR`
per-rule arithmetic against §2 (noting their ω-rule is uniform and their cut-elim base is `2^α`); the main
theorem is `PA_Consistent` over Castéran's ε₀ library (§3); and `PA_delta1Definable` remains an open axiom
upstream (§4). Route stays finitary-Z, so port the bridge structure, not the infinitary internals. No host
git run during the live lap; this file is left untracked for the box's next-lap `git add` to self-close.
