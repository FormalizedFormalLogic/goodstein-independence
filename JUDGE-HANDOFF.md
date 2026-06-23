# JUDGE HANDOFF — Goodstein-independence expedition (external-reviewer role)

> **For a fresh Ren session.** You are the **outside judge** of `~/src/goodstein-independence`, *not* a
> worker on it. An autonomous prover ("the box") + a second agent ("Codex") do the grinding. Your job is
> to read their progress, go to the **source**, find what they miss, calibrate honestly, and relay
> high-value findings. Written 2026-06-23 (~lap 50). Re-run the catch-up recipe first — the box moves
> ~1 lap every few minutes, so this WILL be stale.

## Your role (and why it works)
- **Outside judge / adversarial reviewer**, not a co-grinder. You don't write the proof.
- The division that makes this productive:
  - **The box** is a forward-grinder: it builds confidently and fast, and will build *right up to a gap*
    and then stall or (worse) close it vacuously. It does not naturally take altitude.
  - **Codex** is a competent *code-level* reviewer (file:line, interface hygiene) but can read a stale
    HEAD and stays close to the code.
  - **You** are the *source-grounded* check that catches **architecture-level** and **seam-level** errors
    neither of them sees — by reading the actual papers and reasoning about whether the pieces *connect*.
- **Faithfulness > fluency** (this is the load-bearing principle). In deep proof theory you can spin a
  confident, wrong story undetectably. When a claim is load-bearing, **go to the paper / the compiler**,
  state your confidence as a number, and write a "how this could be wrong" section. The single biggest win
  of the last session came from *reading Rathjen 2014 in full* instead of trusting anyone's summary.

## The cast & channels
- **The box**: autonomous treadmill. Commits per lap; writes `HANDOFF-<date>-lapN.md`, `STATUS.md`,
  `PENDING_WORK.md`, `DESCENT-PLAN.md`, `REFLECTION-*.md`. It respects untracked external files
  ("NOT mine, leave alone"), so docs you drop are safe.
- **Codex**: second agent. Leaves `E-ARCHITECTURE-RESPONSE-*.md` and Comment-Log entries in shared docs.
  Read them; engage fairly (it's usually right, just sometimes a lap behind).
- **Trevor**: relays your findings to the box as **pastes** — that's the live channel (the in-repo
  "coordination doc" negotiation is dead). For bigger findings, write a repo doc *and* hand Trevor a paste
  pointer. Keep status check-ins **short**; he wants the headline, not a deep read every time.

## Catch-up recipe (run FIRST, every session)
```
cd ~/src/goodstein-independence
git log --oneline -20
grep -n ":= sorry" src/GoodsteinPA/Statement.lean src/GoodsteinPA/Reduction.lean
ls -t HANDOFF*.md | head -1     # newest box baton — read it + STATUS.md
```
Don't trust this doc's "where it stands" — verify against HEAD.

## The proof, in one breath (lead with THIS clarity — it's what made it click)
Goodstein: write n in hereditary base 2, then forever {bump the base, subtract 1}. The integers explode
(G(4) dwarfs the atom count) yet always crash to 0. **Why:** replace the base with ω → you get an ordinal
< ε₀; bumping the base is invisible to the ordinal, subtracting 1 strictly lowers it, and ordinals can't
fall forever → it terminates. **Why PA can't prove it:** ε₀ is exactly PA's proof-theoretic strength
(à la Galois — one invariant pins down the whole system's reach); Goodstein needs induction *up to* ε₀,
one notch past PA.

## Where it stands (~lap 50, 2026-06-23 — VERIFY)
- Headline `peano_not_proves_goodstein` = honest `sorry` (anti-fraud guard; stays until `#print axioms`
  is clean). `goodsteinSentence_faithful` is clean (the statement genuinely means Kirby–Paris).
- **Route DECIDED = Route A (Rathjen 2014, Cor 3.7):**
  `PA ⊢ γ →(§3 reduction, PRIMREC) PA ⊢ PRWO(ε₀) →(Gentzen Thm 2.8) PA ⊢ Con(PA)`, then **Gödel II**.
- **Two halves being built:**
  - **crux-1** = internal Cor 3.4 slow-down (`Goodstein → PRWO`): ~assembled; remaining = `ig` f-recursion
    + X-definable block bookkeeping. The `Grzegorczyk.lean` ℕ-template is done.
  - **crux-2** = Gentzen `PRWO(ε₀) → Con(PA)` (`wip/GentzenCon`): just started, PRWO formulation built +
    faithfulness-certified. This is the substantial piece (Gentzen's consistency proof, finitary primrec
    `ord` + reduction `R` with `ord(R D) < ord D`).
- **Banked, OFF the headline path:** `Thm56.peano_not_proves_TI` (the free-X Buchholz §5 boundedness /
  cut-elim machine) — a real, axiom-clean achievement, but the *wrong direction* for chaining (see below).
  Don't let anyone resume it as the headline back-end or delete it.
- **Accepted cost:** `PA_delta1Definable` (🟡 Foundation axiom) rides Gödel II on Route A. It must end up
  the *only* non-trust-base axiom on the headline.

## How we got here (the arc — so you don't re-litigate)
F (the ε₀-order arithmetization seam) got solved fast (`codeOfREPred` from Foundation + a clean
order-type girder). E (Goodstein⟹the unprovable thing) was the deep wall. The box tried **Route B**:
prove `Goodstein → TI_≺(X)` for a *free predicate X* to feed the free-X boundedness result. **Reading
Rathjen showed Route B is blocked, not just hard:** §3 (Grzegorczyk domination, Lemma 3.2) is
**primrec-only**, and an X-definable descent isn't dominated — `free-X-TI ⊢ PRWO`, so
`PA⊬PRWO ⟹ PA⊬free-X-TI` (WRONG direction). The box *machine-checked* the obstruction
(`Grz.not_dominated_of_diag_le`) and switched to Route A, keeping the §3 work (a PRWO descent *is*
internally primrec, so domination holds). Full finding: `E-ARCHITECTURE-REVIEW-2026-06-23.md`.

## Watch-items (this project's bugs live in SEAMS — where two halves must join)
1. **One shared `PRWO(ε₀)` def.** crux-1 *outputs* `PA ⊢ PRWO`; crux-2 *consumes* `PA ⊢ PRWO → Con`.
   They must reference the **identical** Lean def. "Both faithful to Rathjen" ≠ "same object." Enforce via
   a single shared def + final-assembly typecheck.
2. **crux-2's `Con(PA)` must be Foundation's `Con[𝗣𝗔]`** — the exact object Gödel II (`Second.lean`) is
   proven about, not a hand-rolled lookalike. Verify at the statement level before proving the body.
3. **Internal Lemma 3.2 is the lynchpin.** Route A works *only* if Grzegorczyk domination internalizes
   inside PA for the primrec descent (the same domination that was false for free-X, now true). Validate
   it early; everything rests on it.
4. **Meta vs internal.** The banked §5 infra is meta-level/infinitary (Lean about Z∞, mathlib ordinals);
   crux-2 is finitary/internal/primrec. They're different beasts — don't let anyone try to "reuse" §5 for
   crux-2.
5. **Anti-fraud.** Headline stays `sorry` until `#print axioms peano_not_proves_goodstein` is the trust
   base (`propext, Classical.choice, Quot.sound`) + at most `PA_delta1Definable`. No new math axioms; no
   vacuous PRWO/Con.

## The playbook (how to deliver a finding)
- **Catch up from HEAD, not memory.** Then read the source for anything load-bearing (`papers/` has
  Rathjen-2014, Kirby–Paris-1982, Cichon-1983, Towsner, Caicedo, Agboola, Rathjen-2006). `Read` the PDF
  directly.
- **Write findings the box can VALIDATE, not obey:** a cited claim, an explicit confidence %, a
  **validation checklist** (concrete things to check against the code), and a **"how this could be wrong"
  section** so the box can refute cleanly. Put a "VALIDATE, don't trust" banner on big ones.
- **Hand Trevor a tight paste** for the live channel. Reserve a repo doc for architecture-level findings
  (the box reads them on reflection laps; name them distinctively).
- **Add value beyond the workers** — the wins are library discoveries (what's already in Foundation/
  mathlib), simplifications (only the lower bound was needed; Σ₁-completeness gives the computational facts
  free), footguns (computable `Encodable`, not `ofCountable`), and **architecture/seam** calls.
- **Credit the workers** when they're right; **converge, don't compete.** Codex's "validation gate" was
  the right cautious move; the box machine-checking the obstruction was exactly right.

## Pointers
- Finding of record: `E-ARCHITECTURE-REVIEW-2026-06-23.md` (architecture + validation checklist §E).
- Codex: `E-ARCHITECTURE-RESPONSE-2026-06-23.md`.
- Source of truth: `papers/rathjen-2014-goodsteins-theorem-revisited.pdf` (the route), `[9]`
  Kirby–Paris-1982 (the *free-X* model-theoretic proof — different technique; relevant only if free-X ever
  comes back).
- Box state: newest `HANDOFF-*.md`, `STATUS.md`, `PENDING_WORK.md`, `DESCENT-PLAN.md`.

— start by running the catch-up recipe, reading the newest box HANDOFF, and asking "what's the next seam
that has to join, and has anyone checked it joins?"
