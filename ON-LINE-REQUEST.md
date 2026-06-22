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
