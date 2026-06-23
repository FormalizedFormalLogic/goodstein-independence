# ON-LINE-REQUEST — 2026-06-23 (lap 33)

> ⚠️ **SUPERSEDED as of lap 36 (2026-06-23) — do NOT fulfil.** The lap-36 deep reflection found wall B is
> **self-inflicted**: it exists only because `goodsteinSentence` is kept as the opaque `codeOfREPred` blob.
> The fix is to refactor `goodsteinSentence` to a transparent `igoodstein`-based Π₂ sentence (sanctioned by
> `Encoding.lean`'s docstring, gated on the bridge spec) — then the opaque-code↔run bridge below is **moot**
> and `hB` falls out directly. See `REFLECTION-2026-06-23-lap36.md` + `PENDING_WORK.md` top. This file will
> be retired once the refactor lands; no online research is needed. The original request is kept below for
> record only.

---

> Previous requests (lap 27 Route-B sequent shape; lap 19 F-φ) are **all resolved/moot** and have been
> removed. ONE open request below: **Wall B — the opaque-code↔transparent-run bridge inside 𝗜𝚺₁.**

## Wall B: bridging `codeOfREPred goodsteinTerminates` to the transparent `igoodstein` run, provably in 𝗜𝚺₁

**Context.** The headline `goodsteinSentence : Sentence ℒₒᵣ := ∀⁰ (codeOfREPred goodsteinTerminates)` is
LOCKED (anti-fraud) and uses Foundation's r.e.-predicate arithmetization
`LO.FirstOrder.Arithmetic.codeOfREPred` (`R0/Representation.lean:245`), built via `codeOfPartrec'` +
`Classical.epsilon` over the Kleene normal form — so it is an **opaque** Σ₁ `Semisentence`.

The descent contradiction (`DescentSemantic.no_min_descent_absurd_of_goodstein`, now decomposed into walls
B and C+D) needs, inside an **arbitrary** model `M ⊧ 𝗜𝚺₁` (M's `ℒₒᵣ`-reduct, possibly nonstandard):

```
hgood : M ⊧ ∀ m, codeOfREPred goodsteinTerminates (m)
  ⟹   ∀ m₀ : M, ∃ k : M, igoodstein m₀ k = 0          -- (the transparent run reaches 0)
```

where `igoodstein` (`InternalGoodstein.lean`) is the repo's `PR.Construction`-built, 𝗜𝚺₁-Σ₁-definable
Goodstein run (`igoodstein_nat`: it computes the audited `Defs.goodsteinSeq` on ℕ). Equivalently we need
`𝗜𝚺₁ ⊢ ∀ m, codeOfREPred goodsteinTerminates (m) ↔ ∃ N, igoodstein m N = 0`.

**The obstruction.** Foundation's only spec for `codeOfREPred` is the **ℕ-only** `codeOfREPred_spec`
(`ℕ ⊧/![x] codeOfREPred A ↔ A x`) and the provability `re_complete` (for *standard* `x`). There is
(apparently) NO model-internal / 𝗜𝚺₁-provable correctness lemma, and the underlying code is picked by
`Classical.epsilon`, so one cannot reason about its internal behaviour on nonstandard inputs. This is the
`PA_delta1Definable`-flavoured gap (DESCENT-PLAN §3b anticipated it), but the anti-fraud rule forbids
axiomatizing it on the headline, so it must be **proven** for this concrete primitive-recursive function.

**The precise questions (any one helps).**
1. **Foundation API:** Does Foundation (e.g. `Arithmetization` / `ISigma1.Metamath` — the library used for
   Gödel II's provability arithmetization) provide a **model-internal** correctness statement for
   `codeOfREPred` / `codeOfPartrec'` / `code` — something like `V ⊧ codeOfREPred A (a) ↔ <internal Σ₁
   formula>` for `V ⊧ 𝗜𝚺₁`, or a 𝗜𝚺₁-provable graph-correctness for the Kleene code? Pointer to the exact
   lemma name + file if so.
2. **Standard technique:** For a 𝗜𝚺₁-provably-total **primitive recursive** function `f` (here
   `goodsteinSeq`, with a hand-built 𝗜𝚺₁-Σ₁ definition `igoodstein` carrying its provable recursion
   equations), what is the textbook route to `𝗜𝚺₁ ⊢ ∀x, codeOfREPred {y | f-halts}(x) ↔ <my Σ₁ def>`?
   (Hájek–Pudlák *Metamathematics of First-Order Arithmetic* Chap. I/V on Σ₁-definability and the
   provable equivalence of Σ₁ definitions of the same 𝗜𝚺₁-provably-recursive function; the "every two Σ₁
   definitions provably-equivalent if both 𝗜𝚺₁-prove the defining recursion" lemma — exact statement?)
3. **Foundation primitive to bypass the epsilon:** Is there a way in Foundation to obtain a Σ₁ sentence
   *from a `PR.Construction`/`𝚺₁`-definable function* together with a `𝗜𝚺₁`-provable equivalence to
   `codeOfREPred` of the same ℕ-predicate — i.e. a constructive (non-`Classical.epsilon`) `codeOf…`
   variant whose correctness is internalizable? Or a `Defined`/`Definable`-class bridge that yields it?

**Why it unblocks.** Wall B is now the project's dominant remaining wall (wall C+D, the descent
construction, is independent and being attacked in parallel — see PENDING_WORK). Getting the precise
technique/lemma pins how `igoodstein` connects to the locked `codeOfREPred` headline form. **Not
blocking** — I proceed on wall C+D and on probing Foundation's `Arithmetization` library meanwhile.
