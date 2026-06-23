# Summary of changes for run 6ab1345b-e478-406e-ba19-fc0f1cb804fe
Proved `ONoteComp.rePred_ltPull_natCode` in `ONoteComp.lean` (replacing its `sorry`), with no `sorry` remaining anywhere in the file and no new axioms. `#print axioms` for the target shows only `propext`, `Classical.choice`, `Quot.sound`, `Lean.ofReduceBool`, `Lean.trustCompiler`. The file builds cleanly (only a couple of benign `unusedSimpArgs` style lint notes remain, inside `<;> simp [...]` combinators where the argument is load-bearing in some branches). No statements of the pre-existing scaffolding `def`s/instances were changed.

The result establishes that comparison of Cantor-normal-form ordinal notations is computable, packaged as the requested recursively-enumerable predicate. The development follows the intended structure:

1. Structural `Primcodable ONote` — built from the given structural `encodeONote`/`decodeONote` (not from the opaque `Primcodable.ofDenumerable`), via the bijection fact `encodeONote (decodeONote n) = n`, which makes the `prim` field reduce to `Nat.succ`.

2. Computability of `ONote.cmp` — encoded as a ℕ-level function `Cnat` (Ordering codes lt/eq/gt = 0/1/2) and proved `Computable` by structural strong recursion (`Nat.strong_rec`) over the pairing encoding, with a step function whose recursive lookups land at strictly smaller paired codes.

3. Computability of the `NF` predicate — needed to enumerate `NONote`. Mirrors the `cmp` development: a ℕ-level `Nfb` with `Nfb (encodeONote x) = decide x.NF`, proved `Computable` by strong recursion using the `NF (oadd …) ↔ NF e ∧ NF a ∧ TopBelow e a` characterization (the `TopBelow` check reusing `Cnat`).

4. Computability of the coding `natCode` — the subtle point is that the given `Denumerable NONote` enumerates in structural-encode order but its own encoding is opaque, so the naive identity `(natCode a).1 = decodeONote a` is false (this was checked and the false intermediate claim was replaced). Instead, `enc a := encodeONote (natCode a).1` is shown (via the `Denumerable.ofEncodableOfInfinite`/`equivRangeEncode` chain) to be the strictly monotone enumeration of the NF-codes; it is then identified with a search `nthNF a = μ n. a < countNF (n+1)` and proved `Computable` by `Nat.rfind`.

5. Final assembly — `natCode a < natCode b ↔ Cnat (Nat.pair (enc a) (enc b)) = 0`, giving a decidable, `Computable` predicate, from which `REPred` follows by `ComputablePred.to_re`.