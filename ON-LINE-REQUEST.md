# ON-LINE-REQUEST — 2026-06-22 (lap 19)

## Computable / Primrec comparison of Cantor normal forms (`ONote.cmp`) — the F-φ discharge target

**Theorem/source needed.** A `Computable` (ideally `Primrec`) proof that comparison of mathlib's
`ONote`/`NONote` Cantor normal forms is computable — concretely enough to discharge:

```lean
-- src/GoodsteinPA/SeamDefinability.lean  (currently a DISCLOSED axiom)
axiom rePred_ltPull_natCode :
    REPred fun v : List.Vector ℕ 2 ↦ natCode (v.get 0) < natCode (v.get 1)
-- where natCode : ℕ ≃ NONote := (Denumerable.eqv NONote).symm  (= Denumerable.ofNat NONote, computable)
--       and `<` on NONote is `repr a < repr b`, decidable via `NONote.cmp` (linearOrderOfCompares).
```

**Exactly what I need (any one suffices):**
1. A mathlib/known lemma giving `Primcodable ONote` with `Primrec`-grade `ONote.cmp`, OR `Computable₂
   (fun a b : NONote => decide (a < b))` / `Computable (fun a b : ONote => ONote.cmp a b)`. Then
   `rePred_ltPull_natCode` falls out by `ComputablePred → REPred` (`computable_iff_re_compl_re'`) +
   `REPred.comp` with `Computable natCode` (already have `Computable.ofNat NONote`).
2. A pointer to a reference (Lean Zulip / mathlib PR / paper) that has formalized computable ordinal-
   notation comparison, so I can port it.

**Why it unblocks me.** F (the arithmetization seam) is fully assembled — `seam : EpsilonOrder.Seam`
is built and `#print axioms seam = [propext, choice, Quot.sound, rePred_ltPull_natCode]`. Discharging
this single axiom makes the *entire F girder* axiom-clean. It is pure mathlib/computability (ZERO
Foundation dependency), bounded, and Aristotle-feedable.

**Context I already verified (no need to recheck):**
- mathlib's `Ordinal/Notation.lean` has `NONote.cmp` (decidable order) but NO `Computable`/`Primrec`
  for it; `repr` is `noncomputable`.
- `Primcodable NONote` is free via `Primcodable.ofDenumerable` (I have `Denumerable NONote`).
- The order-type half (`exists_NF_repr_eq`, `epsilon0_le_orderType_natCode`) is DONE + axiom-clean in
  `src/GoodsteinPA/Epsilon0Complete.lean` — does NOT need this.

If `--no-aristotle`/offline this lap, no action; I will attempt the recursion-framework proof locally
next lap (relate `ONote.cmp` to a `Nat.rec`/`Primrec` form via the `Primcodable.ofDenumerable` encoding).

---

## 2026-06-23 (lap 24) — the E back-end: how does `PRWO(ε₀)` connect to Buchholz's `paLX ⊬ TI_≺(X)`?

**Context.** The repo's headline refutation is **Buchholz Thm 5.6** (`peano_not_proves_TI :
IsEmpty (Derivation2 paLX {TI prec})`, Gentzen-1943 sharpness, `paLX ⊬ TI_≺(X)` for the **free** set
predicate `X`), now axiom-clean modulo F-φ. The descent wall **E** needs
`𝗣𝗔 ⊢ goodsteinSentence → Nonempty (Derivation2 paLX {TI prec})`. Rathjen 2014 §3 (on disk) gives the
shared core `𝗣𝗔 ⊢ Goodstein → 𝗣𝗔 ⊢ PRWO(ε₀)` where **`PRWO(ε₀)` = "no descending *primitive recursive*
ε₀-sequence"** (Rathjen Thm 2.8 / Cor 2.7). Rathjen's OWN route is **Route A** (`PRWO ⟹ Con(PA)` + Gödel
II), NOT Buchholz's `TI_≺(X)`.

**The precise question (any one helps).**
1. **Route-B bridge.** Is there a standard reference (Buchholz's Beweistheorie notes §5? Schütte? Takeuti?
   Pohlers?) that derives the **lower bound** `Goodstein ⟹ paLX ⊢ TI_≺(X)` (free `X`) directly — i.e.
   carries out the descent *inside* the calculus with the free predicate — rather than via primrec-`PRWO`
   + Con(PA)? Concretely: how is `paLX ⊢ TI_≺(X)` obtained from a (lifted, X-free) proof of Goodstein
   termination, given that the descent extracted from `¬X` is `X`-definable, **not** primrec? A precise
   statement of the calculus-internal "well-foundedness ⟹ transfinite-induction-for-free-X" step (and
   which induction instances it uses) would let me formalize the Route-B back-end.
2. **Route-A cost.** Confirm the cleanest formalized path for `𝗣𝗔 ⊢ PRWO(ε₀) → 𝗣𝗔 ⊢ Con(PA)` (Gentzen,
   Rathjen Thm 2.8(i)) reusing the repo's existing embedding/cut-elim/boundedness girder, and whether the
   `PA_delta1Definable` Foundation axiom is the only extra cost (the repo's `Reduction.lean` already has
   the Gödel II hook `not_proves_of_implies_consistency`, axiom-clean modulo that one axiom).

**Why it unblocks me.** Both back-ends reuse the *shared* `Goodstein ⟹ PRWO` (Rathjen §3), which I am
formalizing regardless. Knowing the precise Route-B bridge (or confirming Route A is the standard/cheaper
landing) decides where the §3 output plugs in and avoids a wrong-target arithmetization. Not blocking —
I continue on §3 (inequality (6)'s step is done; next = the slow-down constructions 3.3/3.4/3.5).
