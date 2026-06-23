# STATUS — GoodsteinPA 📊

**Kirby–Paris: `𝗣𝗔 ⊬ Goodstein`, via Gentzen/Buchholz ordinal analysis — witness-FREE `Z_∞` (embedding
[M4 `embedC`, done] + ε₀ cut-elim [M5, done]) + **Boundedness** (Thm 5.4, DONE lap 14, axiom-clean) ⟹
`𝗣𝗔 ⊬ TI(ε₀)` (= `peano_not_proves_TI`, FULLY axiom-clean — F-φ DISCHARGED lap 28), then
Goodstein⟹TI(ε₀) [= the E wall].** · **Build**: 🟢 green (1308 jobs, `lake build GoodsteinPA`) ·
**Updated**: lap 42 (review — `IterPrefix_lxDef` DISCHARGED → descent exists unconditionally; crux now = Rathjen §3 SLOW-DOWN) · 2026-06-23 · `16552e3`

## ⭐ Lap-42 (REVIEW) — the lap-41 "lone wall" `IterPrefix_lxDef` DISCHARGED; descent sequence is unconditional
**Done:** `IterPrefix_lxDef` + `minClause_lxDef` (`DescentConstruction.lean`, axiom-clean, green 1308).
The **membership-form trick** (`isDescent_iff_mem` — the `X`-atom on a *bound* variable, not a `znth`-term)
that lap 35 used for the `Mlt`-descent applies verbatim to lap-41's **`descentR`** route, so all four
`IterPrefix` clauses are binary-`LX`-definable (only the `descentR` minimality `∀ z<x', ¬(Mlt f z x ∧ ¬MX z)`,
via Foundation `ballLT`, was new). ⟹ **`descent_iterate_seq_total : ∀ k:M, IterPrefix hM f a₀ k` is
UNCONDITIONAL** (the canonical `Mlt`-descent prefix exists at every length, hypothesis-free). Lap 41
over-rated this as "genuine multi-lap infra"; it was one membership-form clause.
**Fresh-mind course-correction (recorded in `PENDING_WORK` lap-42):** the prior `hbound` decomposition
**under-specified slowness** — it assumed the extracted descent `α` already has `iC(αₖ)≤K(k+1)`, but a
`descentR`-least step has uncontrolled `C`. Rathjen gets the bound only via **Cor 3.4** (Grzegorczyk
`g`-padding, Lemma 3.3), which is **NOT started** and is now the genuine remaining crux; the lap-41
`InternalONote` toolkit is the *Thm 3.5* reindex arithmetic, downstream of Cor 3.4. Also flagged: the
`hbound` `sorry` still carries the unachievable `𝚺₁-Function₁ b` shape (b is `X`-dependent) — refactor
`hCD` through lap-41's `nonterminating_of_xDescent` when β lands.

## ⭐ Lap-36 (DEEP REFLECTION + WALL B DISSOLVED) — `goodsteinSentence` refactored transparent; `hB` discharged
**Done after the synthesis:** refactored `goodsteinSentence` to the transparent `“∀ m, ∃ N, !igoodsteinDef
0 m N”` (`Encoding.lean`), re-proved `Bridge.goodsteinSentence_faithful` axiom-**clean** with the IDENTICAL
locked RHS, and **closed `hB`** (`DescentSemantic.lean:419`) — `hgood` lifts to `M`'s reduct
(`reduct_eq_standardModel`), evals to `∀ m ∃ N, igoodstein m N = 0`, instantiate at `m₀`. Real `#print
axioms`: `goodsteinSentence_faithful` = `[propext, choice, Quot.sound]`; the chain's lone `sorryAx` is now
**only `hCD`**. `ON-LINE-REQUEST` archived (wall B moot). **Two walls → one; the only literature gate is
gone, the remaining path is entirely offline.** The synthesis that motivated this:

Altitude pass on the stronger model. Real `#print axioms` reconfirmed: the **entire ordinal-analysis girder
is done and axiom-clean** (`Thm56.peano_not_proves_TI` = trust-base + 1 🟢 native_decide), the headline is
an honest `sorry` (0 math axioms), and the would-be-headline `…_modulo_semantic` carries exactly **one**
`sorryAx` from `no_min_descent_absurd_of_goodstein` — which splits into `hCD` (wall C+D, descent⟹run-never-
dies) and `hB` (wall B, the opaque code↔run bridge). **Finding:** wall B exists ONLY because
`goodsteinSentence = ∀⁰ (codeOfREPred goodsteinTerminates)` is Foundation's **opaque** `Classical.epsilon`
r.e. blob — and every lap since 24 treated that blob as a *fixed* target and tried to *bridge to it*
(literature-gated `ON-LINE-REQUEST`). But `goodsteinSentence` is **not** in the LOCK list, and
`Encoding.lean`'s own docstring (lines 35–39) **explicitly sanctions** refactoring it to a transparent form,
"gated by matching this bridge's spec, so faithfulness can never silently regress." **The course change:
redefine `goodsteinSentence` as the transparent Π₂ sentence built from the repo's own
`igoodsteinDef : 𝚺₁.Semisentence 3`** (`InternalGoodstein`), re-prove `goodsteinSentence_faithful` (identical
locked RHS) via `igoodstein_nat`+`igoodstein_defined` — then `hB` falls out of `hgood` directly and wall B
**dissolves into a mechanical Foundation eval**, removing the project's only literature gate. De-risked this
lap: `igoodsteinDef`/`igoodstein_defined`/`igoodstein_nat` all exist; the `Internal*` chain is `Encoding`-free
(no import cycle); `models_lMap_goodstein` is form-independent; complexity (Π₂) unchanged. After the refactor
the lone genuine wall is **C+D (`hCD`)** — Rathjen §3 slow-down internalized in `M`; its ONote kernel
(`DescentCore`) is built, fully offline. See `REFLECTION-2026-06-23-lap36.md`. Build green 1306 jobs.

## ✅ Lap-30 (review) — STRATEGIC REDIRECT: the E wall collapses to ONE semantic lemma via completeness
Fresh-mind pass found the lap-27 "Route B = hand-build a `paLX` sequent-calculus derivation of `TI_≺(X)`"
plan (literature-gated, `ON-LINE-REQUEST.md`) is **not the cleanest route**. Foundation's **first-order
completeness theorem** (`Derivation.completeness_of_encodable`, general FO, on disk) produces
`(paLX : Schema) ⟹ [TI prec]` from a single *semantic* premise. So `Thm56.DescentE` — and hence the whole
headline — **reduces to ONE model-theoretic lemma** `paLX_models_TI_of_PA_provable` (`src/DescentSemantic.lean`,
NEW): *under `𝗣𝗔 ⊢ goodsteinSentence`, every model `M ⊧ paLX` satisfies `TI prec`*. This is Rathjen §3
carried out **inside `M`** (the free predicate `X` is `M`'s interpretation; inequality (6)'s induction is
`M ⊧ InductionScheme LX`). Three wins: (i) **resolves the free-`X` obstruction** (work in models of `paLX`,
not `𝗜𝚺₁` — `X` present throughout; completeness does the syntactic lift), (ii) **no literature gate**
(standard model theory, not a bespoke sequent shape), (iii) **reuses the lap-26 substrate**
(`igoodstein`/`ibump` live in `M`'s `ℒₒᵣ`-reduct; `DescentCore.ineq6_step` is the kernel). `descentE :
Thm56.DescentE` and `peano_not_proves_goodstein_modulo_semantic : 𝗣𝗔 ⊬ goodsteinSentence` are **proved
modulo the one disclosed `sorry`**; **real `#print axioms` on both = `[propext, sorryAx, choice, Quot.sound,
ONoteComp…native_decide.ax_1_5]`** — the moment the semantic lemma is real, the headline is axiom-clean
(NO `PA_delta1Definable`, NO custom axiom). `Statement.lean` headline `sorry` untouched (anti-fraud). Built
`LX.Encodable`. The remaining wall is now a single, decomposable semantic obligation — see `DESCENT-PLAN §5`.

## ✅ Lap-28 — F-φ DISCHARGED: Thm 5.6 is now FULLY axiom-clean; ONE wall left (E-core)
Completed the v4.28→v4.31 port of Aristotle's `rePred_ltPull_natCode` (CNF comparison is r.e./computable)
and **wired it into the headline route**, turning the lone F-φ math axiom into a machine-checked theorem.
`src/GoodsteinPA/ONoteComp.lean` (promoted from `wip/`, green, sorry-free) supplies the `Computable`
proof of CNF comparison via a structural strong recursion. `SeamDefinability.rePred_ltPull_natCode` is
now a `theorem` (chains ONoteComp), not an `axiom`. **Real `#print axioms peano_not_proves_TI` =
`[propext, Classical.choice, Quot.sound, ONoteComp.cmpStep_spec._native.native_decide.ax_1_5]`** — the
F-φ math axiom is GONE; only one 🟢 `native_decide` finite base-case witness remains (acceptable per
doctrine). Port fixes over the lap-27 wip: rewrote the convert-heavy `Computable` proofs
(`computable_cmpStep`/`_nfTB`/`_nthNF`) as direct combinator terms (added `primrec_thenNat`/`_cmpNat`/
`_cmpNV`); reproved `enc_strictMono` structurally via the `Nat.Subtype.ofNat` enumeration + `ofEquiv_ofNat`
(the v4.31-drift item); replaced the slow `nlinarith` index bound in `cmpStep_spec` with `pair_lt_pair`+
`omega`; `import Mathlib.Tactic.Linarith`. **The project now has exactly ONE wall: E-core (Route-B
form).** Headline `peano_not_proves_goodstein` still an honest `sorry` (anti-fraud intact). Port detail:
`wip/aristotle-fphi/PORT-STATUS.md`.

## ✅ Lap-27 (DEEP REFLECTION) — F-φ SOLVED on Aristotle; back-end choice DECIDED (Route B); one wall left
Altitude pass. **Two state changes.** (1) **F-φ is SOLVED:** the Aristotle job `aris_onotecmp` returned
COMPLETE — `rePred_ltPull_natCode` proved (622-line `ONoteComp.lean`, no `sorry`, no new axioms beyond
2 `native_decide`). Verified faithful here: its final statement is *verbatim* ours and it uses **our**
`natCode := (Denumerable.eqv NONote).symm`. Caveat: proved on `v4.28.0` vs our `v4.31.0` ⟹ a mechanical
cross-version **port** is pending (stashed `wip/aristotle-fphi/`). F-φ is now "proof in hand," not "open."
(2) **COURSE CORRECTION — commit to Route B; stop deferring the back-end.** The lap 25–26 internal-V
machinery (`DescentArith.ineq6_internal` via `sigma1_pos_succ_induction`) builds **Route A's** front-half
(`𝗣𝗔 ⊢ goodstein → 𝗣𝗔 ⊢ PRWO(ε₀)`, X-free), which **cannot** feed the built, axiom-clean **Route B**
back-end `peano_not_proves_TI` (the free-`X` obstruction the team itself flagged in the lap-24
correction: `𝗣𝗔 ⊢ PRWO`/primrec can't refute the X-definable counterexample to `TI prec`; E-lift can't
make the free `X` either). Route A carries `PA_delta1Definable` (🟡), which the anti-fraud rule forbids
on the headline — so Route A can never finish cleanly. **Decision: Route B is primary and committed.**
The lap-26 *arithmetic substrate* (`InternalPow/Digits/Log/Bump/Goodstein`+`InternalBridge`) is **kept**
(reused as `LX`-formula builders for the Route-B paLX construction, ~70% transfers); only the
`DescentArith` `sigma1_pos_succ_induction` *induction wrapper* is Route-A-flavored and off the
clean-headline path. **Highest-value next = port F-φ** (proof in hand ⟹ discharges a whole wall),
collapsing the project to a **single** wall: **E-core(b), Route-B form** (inequality (6) as an
`InductionScheme LX` step on the X-definable descent inside paLX). Faithfulness audit of the headline
reduction (`Thm56`/`Seam`) clean — no transcription drift. Headline still honest `sorry`. See
`REFLECTION-2026-06-23.md`.

## ✅ Lap-24 (review) — direction re-validated against the real kernel; **two walls left: E-core + F-φ**
Fresh-mind pass. Confirmed via real `#print axioms` (not the stale lap-21 ledger): **D' is fully
discharged** (lap 22, `embed_TI_bounded` now chains `EmbeddingBound.embedC_LX_bdd`, no `sorryAx`), and
**`peano_not_proves_TI` carries exactly `[propext, choice, Quot.sound, rePred_ltPull_natCode]`** — the
ONE remaining math axiom on the entire Thm 5.6 route is **F-φ** (on Aristotle, `aris_onotecmp`,
RUNNING). The X-free **E-lift** is done (lap 23, axiom-clean) and the first **E-core** semantic brick
(`evalNat` order-reflection, Rathjen 2.3(iii)) is clean. The single remaining girder to the headline
is **E** = `DescentE` (Goodstein ⟹ `TI(ε₀)` inside PA); its deep content is **E-core** (Rathjen §3
"slowing-down" + arithmetization), since E-lift alone does not reach the X-mentioning `TI prec`. Walls
are now **E-core + F-φ** (was E + F-φ + D'). Direction (Buchholz Boundedness route, attack E-core)
**reaffirmed**. `aris_emcong` job was CANCELED (its target `provable_em_cong_gen` is already proved —
nothing to harvest). Headline `peano_not_proves_goodstein` still an honest `sorry` (anti-fraud intact).

## ✅ Lap-21 (review) — Thm 5.6 ASSEMBLED into one theorem + a hidden gap (D') surfaced
`src/GoodsteinPA/Thm56.lean` (NEW) **assembles the entire Buchholz §5 girder** into the single
headline-route theorem **`peano_not_proves_TI : IsEmpty (Derivation2 paLX {TI prec})`** (Gentzen 1943
sharpness, `𝗣𝗔 ⊬ TI_≺(X)`), and reduces the headline to ONE wall **E** via
`peano_not_proves_goodstein_of_descent (hE : DescentE) : 𝗣𝗔 ⊬ ↑goodsteinSentence`. The chain (all
machine-checked): C₂ `embedC_LX`+`hax_paLX` → collapse the assignment image via `asgX_TI_fix` (`TI prec`
is fvar-free, `prec = lMap (emb precφ)`, `precφ` a `Semisentence`) → C₁+D `orderType_le_of_TIprovable` →
F `seam.ge`; the contradiction is `ε₀ ≤ ‖≺‖ ≤ 2^(ω_c^α) < ε₀`. `#print axioms peano_not_proves_TI =
[propext, choice, Quot.sound, sorryAx, rePred_ltPull_natCode]`. Headline untouched (anti-fraud intact).

**⚠️ Fresh-mind review finding — D' is a real, previously-unflagged gap.** The lap-20 handoff claimed
"Thm 5.6 axiom-clean modulo E+F". That is **incomplete**: the contradiction needs the embedded ordinal
`α < ε₀`, but `embedC_LX` only gives `∃ α` (no bound). `α < ε₀` is *the* Gentzen content — a **finite**
PA-proof embeds to a `Z∞`-proof of height `< ε₀` (PA cannot certify heights up to ε₀ itself). Isolated
as the disclosed `sorry` **`embed_TI_bounded`** (D'). It is **tractable, Foundation-light, no literature**:
strengthen `embedC_LX_gen`/`hax_paLX` to the *uniform* conclusion `∃ c, ∃ B<ε₀, ∀ e, ∃ α≤B, PXFc α c …`
(every builder bumps `B` by `+1`/`max+1`/`sup+1`, all `<ε₀`; the ω-rule closes because the IH's `B` is
*outside* `∀ e`, so the family is uniformly `≤B`). **The walls are now E + F-φ + D'** (was E + F-φ).

## ✅ Lap-19 — F's ORDER-TYPE WALL CLOSED (axiom-clean) — the dominant campaign risk is down
The order-type half of **F** (`src/GoodsteinPA/Epsilon0Complete.lean`, all `#print axioms`-clean) is now
machine-checked end-to-end — this is the piece flagged across laps 12-19 as "the dominant risk / the real
F girder mathlib LACKS":
- **`exists_NF_repr_eq`** : `∀ o<ε₀, ∃ x:ONote, x.NF ∧ x.repr=o` — ε₀-completeness of CNF notations (the
  surjectivity mathlib omits), via the standard CNF recursion (`WellFoundedLT.induction`).
- **`repr_lt_epsilon0`** / **`range_NONote_repr`** : the embedding direction + `range NONote.repr = Iio ε₀`.
- **`rk_ltPull_eq_repr`** (= the seam-advice `note_rank_eq_repr`) + **`epsilon0_le_orderType_ltPull`** :
  `ε₀ ≤ orderType (ltPull e)` for ANY coding `e : ℕ ≃ NONote` (no Iio-sup / universe bump — straight to ℕ).
- **`natCode`** (`Encodable ONote` + `Infinite`/`Denumerable NONote`) + **`epsilon0_le_orderType_natCode`** :
  a fully concrete, hypothesis-free `ε₀ ≤ orderType` witness = the `Seam.ge` field.
**F now reduces to one Foundation-side wire-up:** the `ℒₒᵣ` formula `φ` (`codeOfREPred₂`) defining `natCode`'s
order, then `Seam` instantiates (`Seam.ge := epsilon0_le_orderType_natCode`). The order-type *math* is done.

## ⏭️ Open obligations (lap 19 end) — Thm 5.6 is ONE glue lemma from axiom-clean; remaining walls E + F-φ
The **entire machine from D back is now machine-checked + `#print axioms`-clean** (lap 17): Boundedness
(Thm 5.4) + corollary B, **C₁** `PXFc.cutElim`→cr0, **D** `orderType_le_of_TIprovable`, **C₂-structural**
`embedC_LX_gen`, M4 `embedC`, M5 `cutElim`. The single open sorry below the headline (besides the locked
headline + off-path Route-A) is **C₂ glue** `hax_paLX`'s X-induction case (`EmbeddingX.lean:705`, "pure
integration", recipe inlined) — closing it makes **Thm 5.6 (`PA ⊬ TI(ε₀)`)** axiom-clean modulo E+F.
The remaining campaign walls are **E** (Goodstein⟹TI_≺(X)) and **F** (arithmetization seam, `‖≺‖=ε₀` +
discharge `hprec`/`hprecXPos`). **Reflection finding (lap 18, see PENDING_WORK top):** F's order-type half =
**ε₀-completeness of CNF notations** (`∀ o<ε₀, ∃ x:ONote, NF x ∧ repr x=o`), which **mathlib LACKS** (it has
only the order-*embedding* `NONote↪ε₀`, not surjectivity) — it is the real F girder, ~1–3 laps, and being
pure mathlib ordinal arithmetic it is **Aristotle-eligible** (the one piece with no Foundation dependency).
E **pins which `≺` F may use** (co-design). See newest `HANDOFF`.

## Where it stands
**(lap-39 review — current read.)** The ordinal-analysis girder is **done and axiom-clean** (real `#print
axioms peano_not_proves_TI` = trust-base + 1 🟢 native_decide); the headline `peano_not_proves_goodstein` is
an honest `sorry` (0 math axioms, anti-fraud intact); the faithfulness anchor `goodsteinSentence_faithful` is
axiom-clean. The ENTIRE project now reduces to **one obligation**: `hbound` (`DescentSemantic.lean:416`),
inside `no_min_descent_absurd_of_goodstein`. Laps 37–38 built the **internal ε₀-notation arithmetic**
(`InternalONote.lean`, sorry-free, axiom-clean): codes + `iC` + `ievalNat` (T̂) + `iCanon` + `icmp` + `isNF` +
**order-reflection** `ievalNat_lt_of_icmp_eq_zero` (Rathjen 2.3(iii)). This is the deep substrate `hbound`'s
`step` consumes. **Decomposition of `hbound` (the live attack, hardest-first):** (1) internal
`evalNat_succ_base` `ievalNat (b+1) c = ibump (b+1) (ievalNat b c)` (structural induction; needs the tail
bound — already in `evalNat_reflect_combined`'s TB — + 3 digit-peel lemmas `ilog`/`div`/`mod` of a leading
term, `ibump_pos` recursion in hand); (2) internal `ineq6_step` (port `DescentCore.ineq6_step` digit-direct
onto codes, consuming order-reflection + (1)); (3) seam/F re-wire to transparent `natCodeT` (route (b), the
risky girder touch — re-`#print axioms peano_not_proves_TI` after every change); (4) βₖ slow-down (Rathjen
Thm 3.5) + assemble `hbound` (`base`/`step`/`hpos`+`𝚺₁`-def). Fully offline. See `HANDOFF-2026-06-23-lap38.md`.

**(lap-36 reflection + wall B dissolved — historical read.)** The ordinal-analysis girder is **done and
axiom-clean**; the headline is **one theorem** away (`DescentSemantic.no_min_descent_absurd_of_goodstein`).
Lap 36 found wall B was self-inflicted by the opaque `codeOfREPred` blob, **refactored `goodsteinSentence`
transparent** (`“∀ m ∃ N, !igoodsteinDef 0 m N”`, faithful bridge re-proved clean), and **discharged `hB`**.
The project's only literature gate is gone (`ON-LINE-REQUEST` archived). **The lone genuine remaining wall
is `hCD`** (wall C+D): Rathjen §3 slow-down internalized in `M` — extract a coherent descent function from
`descent_seq_exists` (lap 35), construct `βₖ` + internalize the `DescentCore` ONote/`C` kernel into `M`'s
reduct as `LX`-definable functions, wire the run side (`DescentArith.nonterminating_internal`). Fully
offline. See `REFLECTION-2026-06-23-lap36.md`.

**(lap-33 review — historical read.)** ONE wall stands between the disclosed-`sorry` headline and a fully
axiom-clean Kirby–Paris: **`DescentSemantic.no_min_descent_absurd_of_goodstein`** (Rathjen §3 *inside a
model `M ⊧ paLX`*). Real `#print axioms` this lap: `Thm56.peano_not_proves_TI` (the whole Buchholz Thm 5.6
girder) = `[propext, choice, Quot.sound, ONoteComp…native_decide]` — **clean**; the would-be-headline chain
`peano_not_proves_goodstein_modulo_semantic` adds **exactly one `sorryAx`**, from that lemma. Laps 31–32
built the **equality plumbing** the lemma's substrate needs: X-congruence (`relExt Xsym`) is now an axiom of
`paLX` (lap 32 `a0c611f`, `peano_not_proves_TI` re-validated clean), and `𝗘𝗤 ⪯ paLX` is proved (lap 32
`32d0b0e`) — so models of `paLX` carry genuine equality. **Immediate gate (A2 part 2):** re-route `descentE`
through `Structure.consequence_iff_eq` + `complete` so `no_min_descent_absurd_of_goodstein` may assume
`[Structure.Eq LX M]` — required to install `M`'s `ℒₒᵣ`-reduct as a real `[M ⊧ₘ* 𝗜𝚺₁]` (the substrate
lemmas `ReductModel.reduct_models_isigma1` already demand it). **Then the deep content (walls B/C/D):**
B (opaque `codeOfREPred goodsteinTerminates` ↔ `∃N, igoodstein m N=0`, IΣ₁-internal), C (M-internal
`Mlt`-descent via LX least-number), D (slow-down `βₖ` + `DescentCore.ineq6_step` iterated by `M ⊧
InductionScheme LX`). Substrate is built (laps 26–32); this is the genuine remaining mathematics.

**(lap-30 read.)** The project has **one wall left, and it is now a single semantic lemma**:
`DescentSemantic.paLX_models_TI_of_PA_provable` — "if `𝗣𝗔 ⊢ goodsteinSentence`, every model `M ⊧ paLX`
satisfies `TI prec`." Everything else is machine-checked: `peano_not_proves_TI` (Thm 5.6) is axiom-clean
(lap 28, F-φ discharged), and `DescentSemantic.descentE : Thm56.DescentE` derives the whole `Derivation2
paLX {TI prec}` from that one lemma via Foundation's completeness theorem. `#print axioms` on the full
chain (`peano_not_proves_goodstein_modulo_semantic`) = trust-base + 1 🟢 `native_decide` + 1 `sorryAx`;
discharging the semantic lemma makes the headline clean. **Attack (`DESCENT-PLAN §5`):** decompose
`paLX_models_TI_of_PA_provable` model-internally — (1) E-lift+soundness ⟹ `M ⊧ lMap goodsteinSentence`
(easy, next); (2) the `¬TI prec` ⟹ X-definable `≺`-descent in `M` via `M`'s LX least-number principle;
(3) Rathjen §3 slow-down + inequality (6) in `M` (the lap-26 substrate run + `DescentCore.ineq6_step`,
iterated by `M ⊧ InductionScheme LX`); (4) contradiction with (1). The lap-26 internal substrate transfers
directly; the `sigma1_pos_succ_induction`/`DescentInternal` lemmas are true and green but now superseded
(they were the `V ⊧ 𝗜𝚺₁`, X-free framing — the model `M ⊧ paLX` framing here is the one that closes).

**(historical lap-27 read.)** The project has effectively **one wall left: E-core (Route-B form)**. F-φ —
the lone math axiom under `peano_not_proves_TI` — was **SOLVED on Aristotle** (`rePred_ltPull_natCode`,
verified-faithful, `wip/aristotle-fphi/`); only a mechanical `v4.28→v4.31` port stands between it and
discharge. The **back-end is decided: Route B** (the built, axiom-clean Buchholz monument), reversing the
"deferred" framing — the lap 25–26 internal-V `sigma1_pos_succ_induction` route lands X-free
`𝗣𝗔 ⊢ PRWO`, which is **Route A's** antecedent and cannot feed `peano_not_proves_TI` (free-`X`
obstruction). E-core(b) must be re-targeted to the **integrated paLX construction** (X-definable descent
+ `InductionScheme LX`), reusing the lap-26 arithmetic substrate. Real `#print axioms` (lap 27, build
1280 jobs): headline `[propext, sorryAx, choice, Quot.sound]` (honest `sorry`, 0 math axioms);
`peano_not_proves_TI` = `[propext, choice, Quot.sound, rePred_ltPull_natCode]` (exactly 1 math axiom,
F-φ, now proof-in-hand).

**(historical lap-24 read.)** `peano_not_proves_TI` (Buchholz Thm 5.6, `𝗣𝗔 ⊬ TI_≺(X)`) is **assembled and
axiom-clean modulo the single F-φ axiom** `rePred_ltPull_natCode` (on Aristotle): the full §5 chain
C₂→C₁→D→F + D' (`embed_TI_bounded`, discharged lap 22 via `EmbeddingBound.embedC_LX_bdd`). The headline
reduces to it through `peano_not_proves_goodstein_of_descent` modulo **E** = `DescentE`
(`𝗣𝗔 ⊢ goodsteinSentence → Nonempty (Derivation2 paLX {TI prec})`). E factors as **E-lift** (proof
translation, X-free, DONE lap 23: `paLX_derivable2_lMap_of_PA_provable`) **∘ E-core** (Rathjen §3
"slowing-down" inside PA: `𝗣𝗔 ⊢ goodstein → 𝗣𝗔 ⊢ PRWO(ε₀)`, plus the `PRWO ⟹ TI prec` X-induction
instance). E-core is the **last deep wall**; lap 23 landed its first semantic brick (`evalNat`
order-reflection, `src/DescentCore.lean`). Below the headline only **2 honest `sorry`s** remain in
`src/`: the locked headline (`Statement.lean:22`) and off-path Route-A (`Reduction.lean:52`).

**Historical (the machine from D back, machine-checked + `#print axioms`-clean, lap 18):** the
**embedding** M4 `embedC` (Thm 5.5, `src/Embedding.lean`), the **ε₀ cut-elimination** M5
`cutElim` (Thms 5.1–5.3, `src/Zinfty.lean` + generic `src/ZinftyGen.lean`), **lap 14's Boundedness** Thm
5.4 + corollary `Z∞⊢^β_1 TI ⟹ ‖≺‖≤2^β` (`src/Boundedness.lean`), **lap 15/17's C₁** `PXFc.cutElim`→cr0 +
**D** `orderType_le_of_TIprovable` (`src/XFreeCutElim.lean`, made axiom-clean lap 17 via `nrel_value_subst`),
and **lap 16/17's C₂-structural** `embedC_LX_gen` (`src/EmbeddingX.lean`). Phase 0 (M1,
`goodsteinTerminates_re` clean) + Phase 1 (Gödel II hook) landed. The **only `sorry` below the headline**
(besides the locked headline + off-path Route-A `Reduction.lean:50`) is **C₂ glue** `hax_paLX`'s
X-induction assembly (`EmbeddingX.lean:705`, base done, recipe inlined). The headline
`Statement.peano_not_proves_goodstein` is **still a literal `sorry`** (anti-fraud — correct; `#print axioms`
= `[propext, sorryAx, choice, Quot.sound]`, 0 math axioms). Closing `hax_paLX` makes **Thm 5.6 =
`PA ⊬ TI(ε₀)`** axiom-clean modulo the two remaining campaign girders: the bridge (E, Goodstein⟹TI) +
arithmetization seam (F, `‖≺‖=ε₀`; order-type half = ε₀-completeness, mathlib-lacking — see lap-18 focus).
**Lap-12 pivot** (see route decision):
the project drifted (laps 4–11) into Towsner's witness-bounded variant and hit a genuine wall (§19.6
witness-budget needs the operator `H`). Buchholz §5 shows the witness-FREE route — M4+M5 (done) +
**Boundedness (Thm 5.4)** + Goodstein⟹TI(ε₀) — is the standard, shorter path. Next target = the truth
semantics `⊨^α` + Boundedness. M6 (Hardy lower bound) and the `wip/` witness-bounded calculi are banked
off-path. See `ANALYSIS-2026-06-22-lap12-buchholz-pivot.md` and Outstanding.

## Route decision (lap 12) — PIVOT to Buchholz's Boundedness route (RETRACTS the lap-7 Route-B choice)
**Decision: the Gentzen/Buchholz `TI(ε₀)` route, via Boundedness (Thm 5.4) on the witness-FREE `Z∞`.**
The lap-7 "stay on Towsner Route B" rested on a claim that **lap 12 falsified**: the `(α,k)` cut-elim was
NOT a resolved bookkeeping detail — its §19.6 commuting-ω case is provably unclosable with any numeric
control (ADDENDUM 7), needing the Buchholz operator `H` (multi-lap). Meanwhile Buchholz §5 shows the
witness-FREE route reuses **M5 cut-elim (done) + M4 `embedC` (done)** and needs only **Boundedness +
Goodstein⟹TI(ε₀)** — strictly less unproven surface than Towsner's `Zᵏ` + bounded-cut-elim + bridge, and
the textbook-standard analysis. M6 (Hardy lower bound) was the main "Route B asset" justifying the lap-7
choice, but it is Towsner-specific and now OFF the critical path (banked, not deleted). See
`ANALYSIS-2026-06-22-lap12-buchholz-pivot.md`. (Route A via `Con(PA)`+Gödel-II stays the documented
escape hatch; it re-introduces the `PA_delta1Definable` Foundation axiom 🟡.)

## What's happened (newest first)
- **2026-06-23 (lap 39 — review):** Fresh-mind pass. Real `#print axioms` reconfirmed: headline =
  `[propext, sorryAx, choice, Quot.sound]` (0 math axioms), girder `peano_not_proves_TI` clean, faithful
  bridge clean; the lone `sorryAx` traces to `hbound` (`DescentSemantic:416`). Direction **re-validated**:
  the lap-38 decomposition (internal `evalNat_succ_base` → `ineq6_step` → seam rewire → βₖ) is the correct,
  highest-value attack on `hbound`. Fixed stale `HANDOFF.md` symlink (→ lap38). Began grinding internal
  `evalNat_succ_base` (digit-peel lemmas + structural induction on the substrate). Aristotle available, idle.
- **2026-06-23 (laps 37–38 — internal-ONote substrate COMPLETE):** Built the ε₀-notation arithmetic *inside
  `IΣ₁`* in `InternalONote.lean` (sorry-free, axiom-clean): `icmp` (CNF comparison via pair-indexed CofV
  table), `isNF` (CNF well-formedness as a 0/1 product flag — no negated existentials), and **the crux**
  `ievalNat_lt_of_icmp_eq_zero` (Rathjen 2.3(iii) order-reflection), proved **digit-direct** (no ordinals, so
  it internalizes) via a combined tail-bound + monotonicity strong induction (`evalNat_reflect_combined`).
  Substrate inventory: codes/`iC`/`ievalNat`/`iCanon`/`icmp`/`isNF`/order-reflection. Aristotle `ibump_mono`
  COMPLETE (downloaded, not yet ported to V — order-reflection didn't need it). Build green 1307 jobs.
- **2026-06-23 (lap 36 — DEEP REFLECTION + WALL B DISSOLVED):** Found wall B (the opaque
  `codeOfREPred`↔`igoodstein` bridge, `ON-LINE-REQUEST`) was self-inflicted by keeping the opaque blob as
  `goodsteinSentence`; `Encoding.lean`'s docstring sanctions a transparent refactor gated on the bridge
  spec. **Executed it:** redefined `goodsteinSentence := “∀ m, ∃ N, !igoodsteinDef 0 m N”`, re-proved
  `goodsteinSentence_faithful` axiom-clean (identical locked RHS), and **discharged `hB`**. Real `#print
  axioms`: faithful bridge clean; the chain's lone `sorryAx` is now only `hCD`. Two walls → one; the only
  literature gate removed (`ON-LINE-REQUEST` archived). See `REFLECTION-2026-06-23-lap36.md`. Build green 1306.
- **2026-06-23 (laps 34–35 — wall-C descent-existence brick + `hDdef` DISCHARGED):** Built the M-internal
  descent scaffold and discharged its lone `sorry`: `DescentConstruction.descent_seq_exists`
  (`∀k, ∃W, IsDescent f a₀ W ∧ lh W=k+1`) is sorry-free + axiom-clean, promoted to `src/`. `D(k)` shown
  `LX`-definable via the binary-definability combinators (`lxDef_exists`/`lxDef2_and`) + the membership/
  `Seq`-graph form `isDescent_iff_mem` (key move: the `X`-atom sits on a bound var, not a `znth`-term).
  GOTCHA: mixed `ℒₒᵣ`-guard + `X`-atom `LX` formulas — write the guard in `ℒₒᵣ`, `lMap Φ` it, conjoin the
  `Xsym`/`prec` atom in `LX`. The remaining wall-C content is the βₖ slow-down + the run (now folded into `hCD`).
- **2026-06-23 (lap 33 — review: direction re-validated; equality plumbing complete, A2-part-2 is the
  gate):** Real `#print axioms` reconfirmed: `peano_not_proves_TI` clean, `…_modulo_semantic` = trust-base
  + 1 🟢 native_decide + exactly **one** `sorryAx` (`no_min_descent_absurd_of_goodstein`). Single wall.
  Validated that the substrate (`ReductModel.reduct_models_isigma1`, `DescentCore.lemma36_nonterminating`/
  `ineq6_step`) is built but gated on `[Structure.Eq LX M]` — so the lap-31/32 equality work (X-cong into
  `paLX`; `𝗘𝗤 ⪯ paLX`) is the correct enabler, and A2-part-2 (thread `Structure.Eq` via `consequence_iff_eq`)
  is the immediate gate before walls B/C/D. STATUS/ledger refreshed. Build green 1304 jobs.
- **2026-06-23 (laps 31–32 — equality plumbing for the model-internal descent):** Proved the
  X-congruence matrix in `PXFc` (lap 31 `3ba2727`) and **wired `relExt Xsym` (`∀x y, x=y→X x→X y`) into
  `paLX`** as a genuine axiom (lap 32 `a0c611f`) — `peano_not_proves_TI` re-validated axiom-clean after the
  3-summand `paLX` change. Then proved **`𝗘𝗤 ⪯ paLX`** (lap 32 `32d0b0e`, `DescentLift.eqLX_subset_paLX` +
  `WeakerThan.ofSubset`): every `𝗘𝗤(LX)` axiom is an `lMap Φ`-image of a `𝗣𝗔⁻` axiom or `relExt Xsym`, so
  models of `paLX` carry real equality. GOTCHA banked: prove `lMap`-over-`Matrix.conj` by **casing the
  concrete ℒₒᵣ symbol** (`cases r`/`cases f`), not a general-`k` higher-order rewrite.
- **2026-06-23 (lap 30 — review: E wall → ONE semantic lemma via first-order completeness):** Found
  that `Thm56.DescentE` need not be a hand-built `paLX` sequent derivation. Foundation's
  `Derivation.completeness_of_encodable` turns the semantic premise "every `M ⊧ paLX` models `TI prec`"
  into `paLX ⟹ [TI prec]`. New `src/DescentSemantic.lean`: built `LX.Encodable`, proved `descentE :
  Thm56.DescentE` and `peano_not_proves_goodstein_modulo_semantic` **modulo one disclosed `sorry`**
  (`paLX_models_TI_of_PA_provable`). Real `#print axioms` on the full chain = `[propext, sorryAx, choice,
  Quot.sound, native_decide.ax_1_5]` — no `PA_delta1Definable`, no custom axiom; discharging the lemma
  ⟹ clean headline. Resolves the free-`X` obstruction (models of `paLX` carry `X`) and drops the
  literature gate. Build green 1302 jobs; `Statement.lean` headline `sorry` intact.
- **2026-06-23 (lap 27 — DEEP REFLECTION: F-φ solved on Aristotle; back-end DECIDED = Route B):**
  Altitude pass; faithfulness audit clean (no transcription drift in `Thm56`/`Seam`). **F-φ
  (`rePred_ltPull_natCode`) returned COMPLETE from Aristotle** — verified its statement is verbatim ours
  and uses our `natCode`; proved on `v4.28.0`, so a mechanical `v4.31` port is pending (`wip/aristotle-fphi/`).
  **Reversed the deferred back-end framing: committed to Route B.** Found that the lap 25–26 internal-V
  `sigma1_pos_succ_induction` assembly produces X-free `𝗣𝗔 ⊢ PRWO` = **Route A's** antecedent, which
  cannot feed the built `peano_not_proves_TI` (free-`X` obstruction, per the lap-24 correction) and whose
  back-end carries the forbidden `PA_delta1Definable`. Kept the lap-26 arithmetic substrate (reusable for
  Route B's paLX construction); recognized `DescentArith.ineq6_internal` as off the clean-headline path.
  Next = port F-φ (collapses to one wall), then E-core(b) the Route-B way. Build 1280 jobs; headline
  `sorry` intact. See `REFLECTION-2026-06-23.md`.
- **2026-06-22 (lap 21 — REVIEW: Thm 5.6 assembled; D' gap surfaced):** Validated the lap-20 handoff
  direction (E next, F-φ on Aristotle) against the real kernel. Assembled the §5 girder into one theorem
  `peano_not_proves_TI` (`src/GoodsteinPA/Thm56.lean`) + headline reduction to E
  (`peano_not_proves_goodstein_of_descent`). **Caught a real gap the handoff missed: D'** (embedded
  ordinal `< ε₀`), now isolated as the disclosed `embed_TI_bounded` `sorry`. Build green 1270 jobs;
  headline still `sorry` (anti-fraud). F-φ Aristotle job `aris_onotecmp` still RUNNING. Walls: E + F-φ + D'.
- **2026-06-22 (lap 18 — DEEP REFLECTION: F seam grounded vs an outside attack plan; STATUS refreshed
  through lap 17):** Took altitude. Confirmed (real `#print axioms`) that the *entire machine from D back
  is axiom-clean* — only `hax_paLX` (C₂ glue), the locked headline, and off-path Route-A carry `sorry`.
  **Evaluated an external (GPT-5.5) attack plan for F** (arithmetization seam) against the real repo +
  mathlib. Verdict: seam-abstraction + `hprec`-as-definability + `codeOfREPred₂` are sound (all verified
  against `Boundedness.lean:699`, `TruthSem.lean:120`, `Foundation/.../Representation.lean:233`), but the
  plan **under-scopes the order-type half**: `rank o = repr o` ⟺ **ε₀-completeness of CNF notations**,
  which **mathlib does NOT have** (`Notation.lean` proves only the order-embedding `NONote↪ε₀`, not
  surjectivity). That completeness lemma is the real F girder (~1–3 laps, mathlib-only ⟹ **Aristotle-
  eligible**). Also: the plan's order-choice ignores that **E pins which `≺` F may use** (co-design), and
  the Goodstein base-2 coding (`toONote 2·`/`seqONote`) is the WRONG order (pullback order type ω, not ε₀).
  Full corrected F attack-plan in `PENDING_WORK.md` top. Direction (Buchholz Boundedness route) reaffirmed.
- **2026-06-22 (lap 17 — C₁/D made AXIOM-CLEAN; the X-induction crux SOLVED):** Cleared the lap-16
  `atomCut_x` disclosed `sorry` via **`PXFc.nrel_value_subst`** (value-congruent negative-literal
  renaming; matched-`axLv`-leaf `r₀=r` extraction by `injection` on the nrel eq + oriented `subst`) ⟹
  **`XFreeCutElim.lean` sorry-free; C₁ `cutElim` + D `orderType_le_of_TIprovable` now
  `[propext,choice,Quot.sound]`**. Discharged the **`hax_paLX` base case** (X-free `𝗣𝗔⁻`-image axioms via
  `provable_true_x`). **Solved the X-induction crux conceptually + proved its 4 structural lemmas**
  (`subst_value_subst`, `metaInduction_cong`, `succInd_nnf`, `PXFc_allClosure`): Foundation's `succInd`
  successor `#0+1` substitutes to `nm n+1`, value-equal but NOT syntactically the numeral `nm(n+1)`
  `metaInduction` demanded — no syntactic `step'` can satisfy the old `hstep`; resolved by the
  value-congruent reformulation. Only the `hax_paLX` induction *assembly* (integration glue, recipe
  inlined at the sorry) remains for full C₂. Headline still an honest `sorry`.
- **2026-06-22 (lap 16 — C₂ STRUCTURAL PORT landed; the `exs` case mapped to a calculus retrofit):**
  Built `src/GoodsteinPA/EmbeddingX.lean` (green, one disclosed `sorry`): **`embedC_LX_gen`** — the
  `axm`-abstracted structural embedding of `Derivation2 𝓢 Γ` into `PXFc` over `LX`, all 9 structural
  cases (`closed` via `provable_em_x`; `verum/and/or/all/wk/shift/cut`; `axm` as hypothesis `hax`),
  every builder `XFreeAx`-safe — plus **`provable_true_x`** (ω-completeness for true closed **X-free**
  formulas, the X-free `axm` engine) and **`XFreeForm`** (structural X-freeness + rewriting-invariance).
  **Then ground-truthed the `exs` case against Buchholz §5 (PDF pp.26–30) and found the lap-15
  "mechanical" claim was wrong:** faithfully embedding Foundation's `exs` (arbitrary-term ∃-intro) over
  X-atom bodies needs Buchholz's **value-congruent X-pair axiom** `{Xs,¬Xt}` (`sᴺ=tᴺ`, `AX(Z∞)`, p.27),
  which our same-atom `Deriv.axL` lacks. The faithful fix is a calculus retrofit (generalise the literal
  axiom to value-congruent pairs `Deriv.axLv`); Boundedness case 1.2 (p.29) + cut-elim's literal-cut
  (Remark p.27) already handle them in Buchholz. **Probed the retrofit** (added `axLv` + threaded the
  ZinftyGen leaf branches): 5/8 sites mechanical, `atomCutAux` is the one hard spot, and the XFreeAx
  interaction is benign (reverted as an uncommittable mid-big-bang; it's a single-lap effort with no
  intermediate green). Headline still an honest `sorry`. See `ANALYSIS-2026-06-22-lap16-exs-axLv.md`.
- **2026-06-22 (lap 15 — FRESH-MIND REVIEW: validated the lap-14 cr=0 design against a feared
  obstruction; direction confirmed sound):** Took altitude. Re-derived the full Buchholz §5 chain and
  stress-tested the lap-14 architecture. **Nearly flagged a wall:** Boundedness is implemented at
  `d.cr = 0` (fully cut-free), whereas Buchholz states it at `⊢^β_1` (cut-rank ≤ 1, atomic cuts allowed,
  his case 8 = the X-atomic cut). The worry: getting a cr=0 `XFreeAx` derivation of `{TI}` needs cutElim
  to *eliminate X-atomic cuts*, and the truth-layer surgery (`removeFalseLit`) would emit `axTrue false
  Xsym` leaves — breaking `XFreeAx`. **Resolved by reading `atomCutAux`:** our `Provable.axL` is the
  *same-atom* EM axiom `{Xs,¬Xs}` (not Buchholz's value-matched `{Xs,¬Xt}`), so an X-atomic cut closes by
  **set idempotence** (the `axL` branch, no truth), and the truth-surgery branch is **vacuous under
  `XFreeAx`** (it fires only on an `axTrue` leaf *equal to* the cut atom — i.e. an X-`axTrue` leaf, which
  `XFreeAx` forbids). So `atomCut` preserves `XFreeAx` when cutting X-atoms on `XFreeAx` inputs, and the
  lap-14 C₁ plan (port cutElim to a `cr`-carrying `PXFc` twin, all the way to cr=0) is **feasible as
  written**. **Then GROUND IT OUT (same lap):** built `src/GoodsteinPA/XFreeCutElim.lean` (1456 lines,
  all `[propext,choice,Quot.sound]`) — **C₁ DONE** (the full §19 cut-elim ported to the `XFreeAx`-tracking
  `PXFc` carrier: builders + inversions-at-cr≤c + cut reductions + truth layer + `cutElim`), **D DONE**
  (`orderType_le_of_TIprovable` = Thm 5.6 tail), and the **C₂ crux** (`metaInduction`, the X-induction
  embedding via a cut-tower — the lap-14-flagged faithfulness case — + `provable_em_x`, LX excluded
  middle). Headline still an honest `sorry`. **Remaining to Thm 5.6: the C₂ structural `embedC` port.**
- **2026-06-22 (lap 14 — CRUX CRACKED: Boundedness Thm 5.4 + the full corollary B, axiom-clean):**
  Proved **`boundedness`** (Thm 5.4) — the 9-`Deriv`-case nested induction (outer strong-induction on the
  ordinal height `o d`, inner structural), hardest **case 2** (`¬Prog` `∃⁰`-inversion + the `α→α+2^{β₀}`
  rank bump) machine-checked — and **`orderType_le_of_TIderiv`**, the FULL corollary `Z∞ ⊢^β_1 TI_≺(X)
  ⟹ ‖≺‖ ≤ 2^β` (invert TI's `🡒`/`∀` via the new `XFreeAx`-preserving inversion suite `andInv_xfree`/
  `orInv_xfree`/`allInv_xfree`, feed Boundedness). Built the **`PXF`** carrier (cut-free `XFreeAx`-tracking
  provability + smart constructors). All 17 deliverables `[propext,choice,Quot.sound]`, no math axioms,
  modulo the two legitimate seam hypotheses `hprec`/`hprecXPos` (discharged at arithmetization, step F).
  This is Buchholz's crux done. Remaining to Thm 5.6: C₁ (XFreeAx cutElim→cr=0) + C₂ (`embedC` over LX).
- **2026-06-22 (lap 13 — Boundedness prerequisites; generic Z∞ over LX):** Read Buchholz §5 pp.26–31
  end-to-end. Shipped (green, axiom-clean, `src/`): **`LangX`** (`structLX (S:ℕ→Prop) : Structure LX ℕ`,
  the `⊨^S` carrier), **`ZinftyGen`** (M5 cut-elim **generalised over `{L}[ORing L][Structure L ℕ][DecEq…]`**,
  `Provable.cutElim` axiom-clean — reused wholesale on the X-route, no cut-elim re-proof), **`TruthSem`**
  (`rk`/`orderType`/`models (⊨^γ)`/`Sat` + X-free invariance `models_lMap`), **`XPositive`** (`XPos` +
  `models_mono`, the Buchholz cases 2/3/4 monotonicity). Confirmed VERIFY-(a): the set variable `X` is
  plumbing, not math. See `ANALYSIS-2026-06-22-lap13-boundedness-design.md`.
- **2026-06-22 (lap 12 — §19.6 norm-machinery PROVED + PIVOT to Buchholz's Boundedness route):** Reviewed
  the whole spine fresh. **(a)** Cracked the **norm-budget** half of the 5-lap §19.6 wall: proved
  `cutReduceAllAux` (Towsner's ∀/∃ cut-reduction) on the witness-bounded `Zekd` calculus, axiom-clean
  (`wip/OperatorZinfty.lean`) — via a self-derived **norm-carrying `ZekdProv` wrapper** + threaded
  `norm γ<k+dd` + `+1` d-bump (the plain `≤`-wrapper threw away the norm bound the `allω` reassembly
  needs, since `norm` isn't `≤`-monotone — the actual 5-lap blocker). **(b)** But feeding it from
  `cutReduceAll` exposed the **witness-budget** obstruction is REAL and numeric-unclosable (ADDENDUM 7;
  `allInv` gives the ∀-family at `max k₀ n`, Towsner's commuting-ω bound is false for large `n`) — needs
  the operator `H`. **(c) ⟹ Read Buchholz §5 and PIVOTED:** the witness-FREE `Z∞` + **Boundedness**
  (Thm 5.4) is the standard route and reuses **M4 `embedC` + M5 `cutElim` (both done, axiom-clean)**;
  lap-11's "need witness-bounded `Zᵏ`" was a conflation of order-type-boundedness (valid) with
  witness-boundedness (walled). New critical path = Boundedness + Goodstein⟹TI(ε₀); M6 (Hardy) drops off
  it. See `ANALYSIS-2026-06-22-lap12-buchholz-pivot.md` + ADDENDA 6/7. Build green; headline `sorry` intact.
- **2026-06-22 (lap 9 — DEEP REFLECTION: course-correct off the witness-bounded detour, name M4 as the
  universal bottleneck):** Took altitude. Read DIRECTION/STATUS/HANDOFF/PENDING + the lap-6→8 history +
  the cross-lap landscape memory + all three findings docs. **Findings:** (1) The destination
  (`peano_not_proves_goodstein` axiom-clean) is still right and worth it — net-new in Lean. (2) The
  **two-phase pivot (lap-8) is correct** and well-supported (Buchholz §5 / Schwichtenberg–Wainer Ch.4:
  never thread the witness index through cut-elim). (3) **But laps 6–8 fixated** on building/rebuilding
  witness-bounded cut-elim calculi (`BoundedZinfty→SplitZinfty→OperatorZinfty/Zekd`, ~3 laps), which the
  findings + landscape memory both show was **never on the critical path** — M5 (witness-free cut-elim)
  has been done & clean since lap 3. (4) The **real, universal, untouched bottleneck is M4** (embedding
  `PA ⊢ φ ⟹ Z_∞ ⊢ φ`): it is required on *every* route to the headline (A, two-phase B, Zekd), and has
  sat at "recon done lap 6" for 8 laps while the easier-but-off-path cut-elim thread absorbed effort.
  (5) **Architecture seam named:** M5 is over mathlib `Ordinal.{0}`+real `ℒₒᵣ`; M6 is over `ONote`+abstract
  `GForm` — the bridge must cross an ordinal-type seam + a language seam. **Reframe:** prove the bounding
  lemma *directly* on M5's real cut-free `Deriv` (reusing M6's `hardy_lt_goodsteinLength` ℕ-domination
  fact — the reusable core of M6 — not transporting into the abstract `B` calculus). **Decision:** STOP
  the `cutReduceAllAux`/Zekd thread (bank `wip/` as reference); next target = **M4 feasibility probe**,
  with **M7a (transparent arithmetization)** as the parallel shovel-ready / fallback thread. Refreshed
  STATUS + wrote `REFLECTION-2026-06-22.md` + rewrote HANDOFF to inherit the course change. **Then
  started the M4 grind (post-synthesis):** `wip/Embedding.lean` — `embed : Derivation2 (𝗣𝗔:Schema) Γ →
  ∃ α c, Provable α c Γ` over the SAME `Finset (SyntacticFormula ℒₒᵣ)` substrate (no language
  translation). **6/10 cases proved** (verum/and/or/wk/cut/closed); **`provable_em` (Z∞ excluded-middle)
  FULLY PROVED + axiom-clean.** 4 deep cases remain (`axm`/`all`/`exs`/`shift`), all needing a shared M5
  renaming/subst lemma (the `Derivation.rewrite` analogue) = the next target. Build green (1257),
  headline `sorry` intact, ledger re-confirmed by real `#print axioms`.
- **2026-06-22 (lap 8 — control-ordinal operator calculus built through §19.5; Hardy infra BANKED):**
  Resolved the **Hardy-infrastructure layer** of the §19.6 crux (both directions, axiom-clean, in
  `src/`): `hardy_add_comp`/`hardy_add_collapse` (`H_{γ+δ}=H_γ∘H_δ` for non-absorbing `γ+δ` — the
  cut-elim control collapse) and `hardy_comp_lt_goodsteinLength` (`H_α(H_e(m)) < G(m)` eventually, any
  NF `α,e` — the lower-bound nested-index domination, via `ω^Q·2` exceeding both + the coefficient law).
  Then built `wip/OperatorZinfty.lean`: the **control-ordinal operator calculus `Zekd α e k d c Γ`**
  (witness bound `hardy e (k+d)` decoupled from the derivation ordinal `α`), sorry-free through §19.5 —
  inductive + `mono_k/d/c` + the NEW **`mono_e`** (control-axis monotonicity, via the banked
  `hardy_le_of_lt`) + full inversion suite (orInv/andInvL/R/allInv) + §19.5 cutReduceConj/Disj + all
  §19.6/19.7 ordinal/norm helpers. **Design validated (`ANALYSIS-…-cutelim-k-threading.md` ADDENDUM 5):**
  the single control ordinal `e` (numeric Buchholz form, NOT the set-valued `H`) closes the ADDENDUM-4
  witness-index obstruction — commuting cases keep `e` inert, `e` rises only at the top cut via `mono_e`,
  the lower bound survives via `hardy_comp_lt_goodsteinLength`. **Remaining girder = §19.6 `cutReduceAll`
  on `Zekd`** (port `Zinfty.lean:785` + bounded bookkeeping); a NF-threading subtlety in the leaf cases
  surfaced (norm_add_le is NF-essential) — fix + 3 options recorded in ADDENDUM 5.
  **STRATEGIC PIVOT (ON-LINE-FINDINGS, end of lap 8):** the §19.6 commuting bound is **provably
  unclosable in any single-numeric-index system** (the Hardy inequality is FALSE; Towsner hand-waves it;
  `cutReduceAllAux`'s commuting cases hit exactly this). The literature-standard fix is **two-phase**:
  cut-eliminate on the witness-index-FREE calculus (**= M5, `src/Zinfty.lean`, DONE**) then Hardy-bound
  the CUT-FREE result (**= M6, DONE**). **The remaining critical-path work is the BRIDGE** (cut-free
  `Z∞ {gAll}` → `B`-derivation via subformula property + a Hardy bounding lemma → contradiction), NOT the
  witness-bounded cut-elim. `Zekd`/`SplitZinfty` are now banked alternatives. See `PENDING_WORK.md` top.
- **2026-06-22 (lap 3):** Proved the ENTIRE Z_∞ cut-elimination (Towsner §19), zero sorries,
  axiom-clean: inversions + cut reductions §19.5 (∧/∨) & §19.6 (∀/∃) + `cutElimStep` §19.7 + `cutElim`
  §19.9. `Ordinal.nadd` ABSENT in mathlib v4.31.0 → ordinary `+` with `+1` slack (additive principality
  of `ω^c`). Promoted `wip/ZinftyF.lean → src/GoodsteinPA/Zinfty.lean`. (M5 ✅)  *(laps 1–2 trimmed —
  M1/M2/Phase-0-1 landed + the real `Z_∞` calculus & inversions built; see git history.)*

## Outstanding
**New route (Buchholz §5, lap-12 pivot).** M4 `embedC` (Embedding, Thm 5.5) and M5 `cutElim` (Thms
5.1/5.2/5.3) are **done & axiom-clean** and ARE the two hard pieces. Remaining = Boundedness + the
Goodstein⟹TI bridge. Priorities (see `ANALYSIS-2026-06-22-lap12-buchholz-pivot.md`):

### Short-term — `hbound` is the LONE wall (laps 37–38: deep substrate COMPLETE)
The headline bottoms out at `DescentSemantic.no_min_descent_absurd_of_goodstein`, now a single `sorry`
`hbound` (`:416`) — `hB` discharged lap 36, `hCD` reduced to its sole input `hbound` (the run side
`DescentArith.nonterminating_internal` is proved). `hbound` = `∃ m₀ b, 𝚺₁-Function₁ b ∧ b 0 ≤ igoodstein m₀ 0
∧ (∀k, b k ≤ igoodstein m₀ k → b(k+1) ≤ igoodstein m₀ (k+1)) ∧ ∀k, 0<b k`. Decomposition (hardest-first):
1. ✅ **Internal ε₀-notation substrate — DONE (laps 37–38).** `InternalONote.lean`: `ievalNat` (T̂), `icmp`,
   `isNF`, `iCanon`, `iC`, and `ievalNat_lt_of_icmp_eq_zero` (Rathjen 2.3(iii) order-reflection) — all
   sorry-free, axiom-clean, digit-direct.
2. **Internal `evalNat_succ_base`** `ievalNat (b+1) c = ibump (b+1) (ievalNat b c)` (isNF/iCanon) — structural
   induction; tail bound from `evalNat_reflect_combined`'s TB (extract `ievalNat_tail_lt`); 3 digit-peel
   lemmas (`ilog`/`/`/`%` of `n·β^E+tail`); `ibump_pos` in hand. **← current target.**
3. **Internal `ineq6_step`** — port `DescentCore.ineq6_step` digit-direct onto codes in `M`, consuming
   order-reflection (1) + (2). This is `hbound`'s `step`.
4. **Seam/F re-wire to transparent `natCodeT`** (route (b), the risky girder touch) — make `Mlt`/`precφ`
   decode to `icmp` on codes. Re-`#print axioms peano_not_proves_TI` after EVERY change (must stay clean).
5. **βₖ slow-down** (Rathjen Thm 3.5) from the descent + `iC` ⟹ assemble `hbound` and feed
   `DescentArith.nonterminating_internal`. Several laps, fully offline. See `HANDOFF-2026-06-23-lap38.md`.

**(superseded gate, kept for record) A2 part 2 — Thread `[Structure.Eq LX M]`.** `𝗘𝗤 ⪯ paLX` is proved, so
`descentE` routes through `Structure.consequence_iff_eq` + `complete` (already done in `descentE`/the wall's
signature carries `[Structure.Eq LX M]`). Required so `ReductModel.reduct_models_isigma1` installs the reduct
   as `[M ⊧ₘ* 𝗜𝚺₁]`.
1. **(wall B) Connect the opaque blob to `igoodstein`.** `hgood : M ⊧ lMap Φ goodsteinSentence` mentions the
   r.e.-code `codeOfREPred goodsteinTerminates`; bridge it IΣ₁-internally to the transparent
   `∃N, igoodstein m N = 0` (lap-26 substrate, in `M`'s reduct).
2. **(wall C) M-internal `Mlt`-descent.** From `no_min` build a *definable* descending `G : M → M` via `M`'s
   LX least-number principle (`reduct_models_isigma1`/`InductionScheme LX`). Must be M-internal, not `choice`.
3. **(wall D) Slow-down + inequality (6) in `M`.** Slow `(G k)` ⟹ `(βₖ)` with `C(βₖ) ≤ k+1`; run the special
   Goodstein seq from `m₀ = T̂²(β₀)`; iterate `DescentCore.ineq6_step` by `M`'s LX-induction ⟹ `M ⊧ ∀k mₖ>0`;
   contradict `hgood`. `DescentCore.lemma36_nonterminating` is the route-neutral ONote/ℕ kernel.

### Long-term / banked
- **BANKED, OFF the critical path (do NOT resume on the Buchholz route):** the witness-bounded cut-elim
  thread — `wip/{BoundedZinfty,SplitZinfty,OperatorZinfty}.lean`. Lap-12 `cutReduceAllAux` (norm-machinery,
  axiom-clean) is the furthest it got; closing it fully needs the operator `H` (ADDENDUM 7). Kept as
  reference for the operator-`H` build IF the Buchholz route ever stalls. **M6 (Hardy lower bound,
  `lowerBound_hardy_selfcontained`)** — Towsner-specific, a correct theorem, now OFF the critical path.
- **Route A** (`goodstein_implies_consistency` in `Reduction.lean`, via `Con(PA)` + Gödel II) stays as
  the documented escape hatch; it re-introduces the `PA_delta1Definable` Foundation axiom (🟡) and also
  needs M4. Revisit only if M4 + M7a prove intractable after sustained effort.

### To completion
Headline discharged ⟺ **Boundedness (Thm 5.4) + truth semantics + Goodstein⟹TI(ε₀) bridge + assembly**
land on top of the done M4 `embedC` + M5 `cutElim`, AND `#print axioms peano_not_proves_goodstein` is
`[propext, Classical.choice, Quot.sound]` (+ any documented `native_decide` Goodstein base-cases — 🟢
finite witnesses; no `PA_delta1Definable` on this route). M6 (Hardy) is no longer required.

## Axiom ledger (per headline / landmark theorem — the fidelity spine)
| theorem | paper claim | `#print axioms` shows | status |
|---|---|---|---|
| `peano_not_proves_goodstein` (headline, `Statement.lean`) | uncond. (Kirby–Paris) | `propext, sorryAx, choice, Quot.sound` (lap-30 real) | 🔓 open `sorry` (LOCKED, anti-fraud) — now reduced to **ONE semantic lemma** `paLX_models_TI_of_PA_provable` via `descentE`+completeness. **0** real math axioms; the would-be-headline chain (`…_modulo_semantic`) carries only `sorryAx`+native_decide. |
| `…_modulo_semantic` (lap 30, `src/DescentSemantic`) | the headline, modulo the disclosed semantic `sorry` | `propext, sorryAx, choice, Quot.sound, ONoteComp…native_decide.ax_1_5` (lap-30 real) | 🔓 **= `peano_not_proves_goodstein_of_descent descentE`**. Proves the FULL chain is axiom-clean save `sorryAx` (one lemma) + 1 🟢 `native_decide` — **no `PA_delta1Definable`, no custom axiom**. NOT wired to `Statement.lean`. |
| `descentE` (lap 30, `src/DescentSemantic`) | `Thm56.DescentE` (`𝗣𝗔⊢γ ⟹ Derivation2 paLX {TI prec}`) | `propext, sorryAx, choice, Quot.sound, native_decide.ax_1_5` | 🔓 **via FO completeness** (`Derivation.completeness_of_encodable`) — reduces `DescentE` to the one semantic premise `paLX_models_TI_of_PA_provable`. Built `LX.Encodable`. |
| `no_min_descent_absurd_of_goodstein` (laps 30–38, `src/DescentSemantic`, **THE wall**) | Rathjen §3 in-model: `no_min` + Goodstein-in-`M` ⟹ ⊥ | `sorryAx` (disclosed, **1** sub-`sorry`: `hbound`@416) | 🔴→🎯 the **single open obligation**. `hB` **DISCHARGED lap 36**; `hCD` reduced to its sole input `hbound` (∃ `m₀,b` with `𝚺₁`-def, `base`/`step`/`hpos` — the run side `DescentArith.nonterminating_internal` is proved/baked-in). Laps 37–38 built the deep substrate (`InternalONote`: `ievalNat`/`icmp`/`isNF`/`iCanon`/order-reflection, all axiom-clean) that `hbound`'s `step` (internal `ineq6_step`) consumes. Remaining: internal `evalNat_succ_base` → `ineq6_step` → seam rewire → βₖ slow-down. |
| `paLX_models_TI_of_PA_provable` (lap 30, `src/DescentSemantic`) | Rathjen §3 in-model: `𝗣𝗔⊢γ ⟹ ∀ M⊧paLX, M⊧TI prec` | `sorryAx` (via the wall) | 🟢 PROVED modulo the one named `sorry` above — steps 1–2 + progressivity-contrapositive machine-checked; bottoms out at `no_min_descent_absurd_of_goodstein`. |
| `eqLX_subset_paLX` / `eqAxiom_weakerThan_paLX` (lap 32, `src/DescentLift`) | `𝗘𝗤(LX) ⊆ paLX`, hence `𝗘𝗤 ⪯ paLX` | `propext, choice, Quot.sound` | 🟢 clean — every `𝗘𝗤(LX)` axiom is an `lMap Φ`-image of a `𝗣𝗔⁻` axiom or `relExt Xsym`; gives models of `paLX` genuine equality (enables the A2-pt2 `consequence_iff_eq` route). |
| `peano_not_proves_TI` (Thm 5.6, lap 21, **F-φ DISCHARGED lap 28**, `src/Thm56`) | Gentzen 1943: `𝗣𝗔 ⊬ TI_≺(X)` | `propext, choice, Quot.sound, ONoteComp…native_decide.ax_1_5` (lap-30 real) | 🟢 **CLEAN** — full §5 chain C₂→C₁→D→F + D'; F-φ now a theorem (`ONoteComp`). Only 1 🟢 `native_decide` finite artifact. No `sorryAx`, no math axiom. |
| `embed_TI_bounded` (D', **discharged lap 22**, `src/Thm56`) | finite PA-proof ⟹ `Z∞`-proof height `<ε₀` | `propext, choice, Quot.sound, rePred_ltPull_natCode` | 🟢 **CLEAN** — chains `EmbeddingBound.embedC_LX_bdd` (the uniform `∃B<ε₀,∀e,∃α≤B` bound). The lap-21 disclosed `sorry` is gone. |
| `paLX_derivable2_lMap_of_PA_provable` (E-lift, **lap 23**, `src/DescentLift`) | `𝗣𝗔 ⊢ σ ⟹ Derivation2 paLX {lMap σ}` | `propext, choice, Quot.sound` | 🟢 clean — X-free proof translation (`lMap` commutes with `succInd`/`univCl`; schema inclusion `(𝗣𝗔:Schema).lMap Φ ⊆ paLX`). Does NOT reach `TI prec` (X-essential); feeds E-core's X-induction instance. |
| `evalNat_lt_iff`/`evalNat_lt_of_lt` (E-core brick, **lap 23**, `src/DescentCore`) | Rathjen 2.3(iii): `T̂^b_ω` order-reflects on `Canon` | `propext, choice, Quot.sound` | 🟢 clean — `evalNat b o < evalNat b p ↔ o.repr < p.repr` on the `Canon`/`NF` domain, from `canon_repr` + `toOrdinal` strict mono. The workhorse Lemma 3.6 inequality (6) runs on. |
| `peano_not_proves_goodstein_of_descent` (G, **lap 21**, `src/Thm56`) | `DescentE ⟹ 𝗣𝗔 ⊬ γ` | same as Thm 5.6 | 🟢 reduction — pins E's interface (`𝗣𝗔 ⊢ γ → Nonempty (Derivation2 paLX {TI prec})`); headline `sorry` stays until E real |
| `hax_paLX` (C₂ glue, `src/EmbeddingX`) | `paLX`-image axioms embed to `PXFc` | `propext, choice, Quot.sound` | 🟢 **CLEAN (lap 20)** — X-induction assembly discharged via `PXFc_allClosure` + new `rew_succInd`/`rew_subst1_comm_q`/`subst1_comp_bShift` + `metaInduction_cong`. ⟹ `embedC_LX` clean. |
| `goodsteinSentence_faithful` (bridge) | encoding correctness `(ℕ⊧γ) ↔ ∀m∃N goodsteinSeq m N=0` | `propext, choice, Quot.sound` | 🟢 clean (trust base) — **lap 36:** re-proved for the transparent `γ := “∀ m ∃ N, !igoodsteinDef 0 m N”` via `igoodstein_defined.iff`+`igoodstein_nat`; **identical locked RHS**, faithfulness preserved. |
| `goodsteinTerminates_re` (M1) | r.e. of termination | `propext, choice, Quot.sound` | 🟢 clean |
| `Deriv.Provable.cutElim` (M5, §19.9, `src/Zinfty`) | ε₀ cut-elimination (ℒₒᵣ) | `propext, choice, Quot.sound` | 🟢 clean — witness-FREE `(α,c)` |
| `ZinftyGen.…Provable.cutElim` (M5-generic, lap 13) | ε₀ cut-elim over `{L}` | `propext, choice, Quot.sound` | 🟢 clean — the X-route carrier (`L=LX`); reused wholesale, no re-proof |
| `Boundedness.boundedness` (Thm 5.4, **lap 14**) | order-type Boundedness | `propext, choice, Quot.sound` | 🟢 clean — modulo seam hyps `hprec`/`hprecXPos` (discharged at F) |
| `Boundedness.orderType_le_of_TIderiv` (Cor B, **lap 14**) | `Z∞⊢^β_1 TI ⟹ ‖≺‖≤2^β` | `propext, choice, Quot.sound` | 🟢 clean — modulo `hprec`/`hprecXPos`; consumes a cr=0 `XFreeAx` `⊢{TI}` (C₁+C₂ supply it) |
| `embedC` (M4, `src/Embedding`) | PA⊢φ ⟹ Z∞⊢φ (ℒₒᵣ) | `propext, choice, Quot.sound` | 🟢 clean — needs C₂ generic-LX port for the X-route |
| `PXFc.cutElim` (C₁, lap 15, **clean lap 17**, `src/XFreeCutElim`) | `XFreeAx` cut-elim → cr=0 | `propext, choice, Quot.sound` | 🟢 clean — value-congruent literal calculus (`Deriv.axLv`); the lap-16 `atomCut_x` disclosed `sorry` was discharged lap 17 by **`PXFc.nrel_value_subst`** (value-cong negative-literal renaming). |
| `orderType_le_of_TIprovable` (D, **lap 15**) | Thm 5.6 tail `PXFc {TI} ⟹ ‖≺‖≤2^(ω_c^α)` | `propext, choice, Quot.sound` | 🟢 clean — C₁ ∘ corollary B; modulo seam hyps `hprec`/`hprecXPos` (F) |
| `provable_em_x` (C₂, **lap 15**) | `Z∞` excluded middle over LX | `propext, choice, Quot.sound` | 🟢 clean — `XFreeAx`-automatic (never `axTrue`) |
| `metaInduction` (C₂ crux, **lap 15**) | X-induction via cut-tower (Buchholz 5.5) | `propext, choice, Quot.sound` | 🟢 clean — the faithfulness-critical embedding step; abstract in `step` (Foundation-DSL glue ⟹ later) |
| `provable_true_x` (C₂, **lap 16**, `src/EmbeddingX`) | ω-completeness, true closed X-free ⟹ `XFreeAx` | `propext, choice, Quot.sound` | 🟢 clean — the X-free `axm` engine |
| `embedC_LX_gen` (C₂-struct, **lap 16**) | structural embedding `Derivation2 𝓢 Γ ⟹ PXFc` over LX | `propext, choice, Quot.sound` | 🟢 **clean** — all 10 cases (`exs` discharged via `axLv`-based `provable_em_cong_gen_x` + `PXFc.exI_closed`); `axm` abstracted as `hax` |
| `provable_em_cong_gen_x` (C₂, **lap 16**) | value-cong EM over LX (atoms via `axLv`) | `propext, choice, Quot.sound` | 🟢 clean — the `exs` engine, X-atoms safe |
| `hardy_le_of_lt` (M6, `src/Hardy`) | Hardy index monotonicity (Hmono) | `propext, choice, Quot.sound` | 🟢 clean |
| `lowerBound_existential_hardy` (M6) | ∃-fragment 17.1, concrete Hardy/`G` | `propext, choice, Quot.sound` | 🟢 clean — zero abstract hyps |
| `B.allInv` (M6) | ∀-inversion (I∀-frontier resolution) | `propext, choice, Quot.sound` | 🟢 clean |
| `lowerBound_hardy` (M6) | full Thm 17.1 mod `Hdom` | `propext, choice, Quot.sound` | 🟢 clean |
| `lowerBound_hardy_selfcontained` (M6, **lap 6**) | **full Thm 17.1, only `α.NF`** | `propext, choice, Quot.sound` + 12 `native_decide` base-case `ax_*` | 🟢 clean — the `ax_*` are 🟢 finite Goodstein base-case witnesses (acceptable indefinitely) |
| `hardy_add_comp`/`_collapse` (lap 8, `src/Hardy`) | `H_{γ+δ}=H_γ∘H_δ` (non-absorbing) | `propext, choice, Quot.sound` | 🟢 clean — banked Hardy infra (was for the dead Zekd thread; still a usable composition law) |
| `hardy_comp_lt_goodsteinLength` (lap 8, `src/LowerBound`) | `H_α(H_e(m)) < G(m)` eventually | `propext, choice, Quot.sound` + the M6 `native_decide` base-cases | 🟢 clean — banked nested-index domination (reusable if a bridge ever needs a nested control index) |
| `not_proves_of_implies_consistency` (Route A) | meta-reduction | `…, PA_delta1Definable` | 🟡 Foundation axiom; **Route A — REJECTED lap 27** (anti-fraud forbids it on the headline; back-end is Route B) |

Math-axiom count: **`peano_not_proves_TI`** (Thm 5.6) carries **0** math axioms — F-φ
`rePred_ltPull_natCode` was **DISCHARGED lap 28** (ported `ONoteComp.lean` into `src/`); its `#print axioms`
is now `[propext, choice, Quot.sound, ONoteComp…native_decide.ax_1_5]` (trust base + 1 🟢 finite
`native_decide` witness). The **headline** target is still `sorry` (the one semantic wall unbuilt); the
would-be-headline chain `…_modulo_semantic` carries only that trust base + **1 `sorryAx`**
(`no_min_descent_absurd_of_goodstein`). On discharge, headline `#print axioms` must be `[propext,
Classical.choice, Quot.sound]` (+ documented 🟢 `native_decide` artifacts) with no `PA_delta1Definable` —
**back-end is Route B** (lap-27 decision; the 🟡 `PA_delta1Definable` sits only under the rejected Route-A hook).

## Pointers
ROADMAP/plan: `EXPEDITION-PLAN.md`, `PHASE2-DECOMPOSITION.md` · **lap-27 reflection (back-end decided
= Route B; F-φ solved): `REFLECTION-2026-06-23.md`** · lap-9 reflection: `REFLECTION-2026-06-22.md` ·
E map: `DESCENT-PLAN.md` · architecture: `ANALYSIS-2026-06-22-bounding-resolution.md` · newest
baton: `HANDOFF.md` · open-items: `PENDING_WORK.md` · charter: `DIRECTION.md`
