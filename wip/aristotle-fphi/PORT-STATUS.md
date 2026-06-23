# F-φ port status — v4.28 → v4.31 (lap 27)

**Goal:** port Aristotle's verified proof of `rePred_ltPull_natCode` (`ONoteComp.lean`, proved on Lean
`v4.28.0`) into our `v4.31.0` repo, then replace the `axiom rePred_ltPull_natCode` in
`src/GoodsteinPA/SeamDefinability.lean` with it — making `Thm56.peano_not_proves_TI` fully axiom-clean.

**Faithfulness (verified lap 27):** the target statement is *verbatim* ours and uses **our**
`Epsilon0Complete.natCode := (Denumerable.eqv NONote).symm`. Our `Epsilon0Complete` scaffolding
(`encodeONote`/`decodeONote`/`Encodable ONote`/`Denumerable NONote`/`natCode`) is **definitionally
identical** to Aristotle's, so the ported file REUSES it (imports `GoodsteinPA.Epsilon0Complete`,
`open GoodsteinPA.Epsilon0Complete`) rather than redefining — no re-basing of the order-type half
(`Seam.ge`) needed.

## Files
- `ONoteComp.lean` — Aristotle's ORIGINAL v4.28 proof (untouched reference).
- `ONoteComp.v431-port-wip.lean` — the in-progress port (namespace `GoodsteinPA.ONoteComp`, imports
  our scaffolding). **Has ~12 compile errors remaining** (see below). NOT in the build.
- `ARISTOTLE_SUMMARY.md` — Aristotle's own description of the proof structure.

## DONE this lap (in the wip port)
- Removed Aristotle's duplicated scaffolding (encode/decode/instances/natCode) → reuse `Epsilon0Complete`.
- Deleted 3 DEAD lemmas (`primrec_thenNat`, `primrec_cmpNat`, `primrec_cmpNV`) — unused (`computable_cmpStep`
  inlines those facts).
- Rewrote `primrec_cmpIdxA` cleanly (combinator proof, no `convert`). ✅
- Rewrote `ordCode_cmp` — **still broken** (see below).
- Replaced both `native_decide +revert` (the v4.31 hang: `+revert` reverts the strong-rec IH `∀m, ...`,
  non-decidable) → `simp`/plain `native_decide`. ✅ (was causing >10min hangs.)

## COMPILE-TIME REALITY (the real blocker)
At full `maxHeartbeats` the single file takes **>10 min** (`lake env lean`, no caching) — aggregate
heavy-tactic cost (~10 `grind`/`aesop`/`simp +decide`/`nlinarith`/`native_decide` proofs), NOT a kernel
hang (confirmed: `-DmaxHeartbeats=15000` finishes in ~7 min). **Iterate with the low-heartbeat
diagnostic** (`lake env lean -DmaxHeartbeats=15000 …`) to see structural errors fast; only the 2
genuinely-heavy proofs (`computable_cmpStep` L~199, the `enc_strictMono`/`countNF` chain L~176) time out
there and need a full build to confirm. **First green build → wire into the lib + cache.**

## REMAINING ERRORS (low-heartbeat diagnostic, line numbers in the wip file ~)
Root causes are systematic v4.28→v4.31 drift:

1. **`ordCode_cmp` (L107)** — `LT.lt.not_lt` field is GONE (`error: Invalid field not_lt`). Use
   `asymm h` / `Nat.not_lt.mpr h.le` / `ne_of_gt h` instead, or rewrite via `cmp_eq_lt_iff` /
   `cmp_eq_gt_iff` / `cmp_eq_eq_iff` (verify these exist in `Mathlib/Order/Compare.lean`).
2. **Syntax `)[ ` (L166, L350)** — the `exact fun L => …( L[cmpIdxE L.length]? ).bind…` restatements in
   `computable_cmpStep`/`computable_nfStep` fail to parse under v4.31 (`unexpected token ')['`). The
   getElem `L[i]?` notation inside the explicit lambda. Fix: reformulate without the inline `(L[i]?)` or
   add spacing/parens; likely cleanest to **rewrite these two `Computable` proofs** directly.
3. **`convert … using 1` metavar explosion** — the big convert-based `Computable` proofs
   (`computable_cmpStep`, `computable_nfTB`, `computable_nfStep`, the final `rePred_ltPull_natCode`,
   `computable_countNF` partly, `computable_nthNF`) create `?convert_N` metavars + `grind`/`aesop`
   can't close them (v4.31 `convert` is stricter — see corpus `lean-v431-convert-bang-using-bang`). Try
   `convert!`/`using!` FIRST; if that fails, **rewrite each as a direct combinator term** (the functions
   are explicit unpair/pair/ite/bind/map compositions — all combinators verified present in v4.31:
   `Computable.{option_bind,option_map,cond,nat_casesOn,nat_rec,list_getElem?,list_length,to₂,pair}`,
   `Primrec.{vector_get,list_getElem?,nat_sub,unpair,fst,snd,ite}`, `Computable.nat_strong_rec`,
   `Partrec.rfind`; `Primrec.nat_lt`/`Primrec.eq` are now `PrimrecRel` — use directly as the
   `PrimrecPred` for `Primrec.ite`, but `.comp` on them may need `(· : Primrec₂ _).comp`).
4. **`of_eq` `id`-goals (L234/265/268/387)** — `refine' X.of_eq _ _` leaves `fun n => f n = fun a => f (id a)`;
   v4.31 doesn't auto-close. Add `· funext _; rfl` (or `· ext; simp`) for these.
5. **`enc_strictMono` (L426)** — the 7-`simp [Denumerable.eqv]`/`Encodable.decode₂`/`Nat.Subtype.ofNat`
   chain hits an `instances`-transparency type mismatch (`Encodable.decode₂` unfold). Needs a v4.31-aware
   reproof of the NF-enumeration strict monotonicity.
6. **`lt_countNF_succ_enc` (L485) / `enc_eq_nthNF` (L487) / `countNF_enc`-area (L496)** — `linarith`/`unknown
   tactic` fallout; small arithmetic, fixable with `omega`.

## Recommended resume strategy
- This is a **mechanical multi-lap port** of a verified proof. Keep the disclosed `axiom` in
  `SeamDefinability.lean` (it is TRUE + PROVEN — honest 🟡) until the port is green.
- Fix in this order (cheap→expensive), using the **low-heartbeat diagnostic** for fast iteration:
  ordCode_cmp (1) → of_eq id-goals (4) → arithmetic (6) → enc_strictMono (5) → then the convert-heavy
  `Computable` rewrites (2,3). Many of (2,3) are best **rewritten as direct combinator terms** rather
  than salvaging the auto-generated convert chains.
- When green at low-heartbeat: do ONE full `lake build` (wire into lib root + SeamDefinability), confirm
  `#print axioms peano_not_proves_TI` = `[propext, choice, Quot.sound]` (+ ≤2 `native_decide` 🟢
  `ofReduceBool`/`trustCompiler`), then the F wall is fully discharged.
- ALTERNATIVE if the port stays painful: this is not the crux (E-core is). The axiom is honest and
  proven; deprioritize the port and drive E-core(b) Route-B instead.
</content>
