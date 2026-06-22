# DIRECTION — GoodsteinPA (treadmill charter + current state)

Companion to `EXPEDITION-PLAN.md` (the math). This file is the **operational charter**: what a
treadmill lap should do, what it must NOT touch, and when to stop. Read both.

## Where we are (Phase 0.2 — 2026-06-22)

The γ encoding route is **found, build-verified, and banked**:

```
goodsteinSentence := ∀⁰ (codeOfREPred (fun m => ∃ N, goodsteinSeq m N = 0))
```

- `goodsteinSentence` (`Encoding.lean`) is a **real** `Sentence ℒₒᵣ`, axiom-clean
  (`#print axioms` = `[propext, Classical.choice, Quot.sound]`).
- `goodsteinSentence_faithful` (`Bridge.lean`) is **PROVED**:
  `(ℕ ⊧ₘ goodsteinSentence) ↔ ∀ m, ∃ N, goodsteinSeq m N = 0`, via Foundation's
  `Semiformula.eval_all` ∘ `codeOfREPred_spec`. Its only `sorryAx` flows from the single
  residual below.

Why this route: Foundation's `R0/Representation.lean` already does the hard work — it turns any
**r.e. predicate** into a faithful Σ₁ sentence (`codeOfREPred` + `codeOfREPred_spec`). We do not
hand-build the arithmetic formula for the recursive Goodstein step.

## THE residual (the treadmill objective) 🎯

One sorry stands between us and an axiom-clean faithful Phase 0:

```
Encoding.goodsteinTerminates_re : REPred goodsteinTerminates
```

`goodsteinTerminates m := ∃ N, goodsteinSeq m N = 0` is r.e. (search `N`). The only non-trivial
input is **computability of the Goodstein function**, which bottoms out at **`Computable bump`**.
`bump` (`Defs.lean`) is defined by well-founded recursion on `Nat.log b n`, so mathlib does not
derive its `Computable` witness automatically. This is bounded, compiler-checkable, and carries
**zero faithfulness risk** (a computability proof typechecks or it doesn't — it cannot fake
faithfulness). Ideal treadmill fuel.

Sketch of the attack (any working route is fine):
- `Computable bump` — the wall. Options: derive it for the WF recursion directly; or give a
  manifestly-computable structural reformulation (e.g. fuel-bounded `bumpFuel`), prove it equals
  `bump`, transfer computability. Then `Computable₂ goodsteinSeq` by recursion on the step index.
- `ComputablePred (fun p : ℕ × ℕ => goodsteinSeq p.1 p.2 = 0)` via `Computable` + decidable `= 0`.
- `REPred` via `ComputablePred.to_re` then `REPred.projection` to existentially quantify `N`.
  (See `REPred.projection`, `REPred.and`, `ComputablePred.to_re` in Foundation `Vorspiel/Computability`.)

## LOCK — the audit surface (do NOT edit) 🔒

Faithfulness is enforced by the compiler against fixed anchors. A lap may ADD computability
lemmas and discharge `goodsteinTerminates_re`, but must NOT change:
- `Defs.lean` — the audited `goodsteinSeq` / `bump` / `base` (the faithful process).
- `Bridge.lean`'s theorem **RHS** `∀ m, ∃ N, goodsteinSeq m N = 0` (the faithful spec).
- `goodsteinTerminates`'s definition in `Encoding.lean`.
Weakening any of these would smuggle vacuity. They are the trust base; leave them be.

## Self-stop criterion (bounded — not an open grind) 🛑

Stop when **all** hold (host-verify, don't trust a lap's self-report):
1. `lake build GoodsteinPA` GREEN.
2. `Encoding.lean` has **no** `sorry` (i.e. `goodsteinTerminates_re` is proved).
3. `#print axioms goodsteinSentence_faithful` = `[propext, Classical.choice, Quot.sound]`
   (the `sorryAx` is gone).

Do **NOT** touch `Statement.peano_not_proves_goodstein` — that is the **designated open target**
(the heroic Kirby–Paris girder, Phase 2+, multi-month, human-led). A lap that "closes" it is
almost certainly smuggling; leave its `sorry` in place. The treadmill's whole job is the
computability residual, nothing downstream.

## Execution prerequisite (verify before launching) ⚙️

The lean-yolo box is network-isolated. It must build this repo **offline**: the CoW'd Foundation
v4.31 + mathlib oleans in `.lake/packages` (placed by `lake-base link … --require Foundation`) +
the box's v4.31.0 Linux toolchain. A lap must never run `lake update` / fetch. Confirm a clean
offline `lake build GoodsteinPA` in the box before turning the treadmill loose.
