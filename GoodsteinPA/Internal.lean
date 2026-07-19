/-
# The IΣ₁-internal Goodstein apparatus

Arithmetization of the Goodstein machinery inside models of `𝗜𝚺₁`: internal
exponentiation/digits/log (`ipow`/`idigits`/`ilog`), the internal base-bump
(`ibump`), the internal Goodstein step/sequence (`igoodstein`), and the bridge
tying the internal sequence to the external `Goodstein.goodsteinSeq`.

Formerly the file chain `InternalPow → InternalDigits → InternalLog →
InternalBump → InternalGoodstein → InternalBridge`, consolidated; each former
file is one section below.
-/
module

public import GoodsteinPA.Compat
public import GoodsteinPA.ToMathlib.Goodstein.Domination

@[expose] public section

namespace GoodsteinPA.InternalPow

/-! ## InternalPow -/
/-
# `InternalPow.lean` — E-core(b) brick 1: internalized base-`b` power as a `𝚺₁`-function in `V`

The deep wall of the descent **E** is **E-core(b)** (`DESCENT-PLAN.md §3`): re-expressing Rathjen §3
*inside* PA. Its kernel — inequality (6) — is arithmetized over **base-`b` numerals** (the digit /
hereditary-base-change view), so the very first prerequisite is a `𝚺₁`-definable variable-base power
`b ^ x` inside an arbitrary `V ⊧ₘ* 𝗜𝚺₁`.

Foundation's `Exponential`/`exp`/`bexp` machinery is **base-2 only** (`Arithmetic/Exponential/`); there
is no general variable-base power. We build one here from the generic primitive-recursion engine
`PR.Blueprint`/`PR.Construction` (`HFS/PRF.lean`), exactly the way `repeatVec` (`HFS/Vec.lean`) is built:

* `ipow b 0     = 1`
* `ipow b (x+1) = ipow b x * b`

and the engine certifies `ipow` is a genuine **`𝚺₁`-function** of `(b, x)` — the form the inequality-(6)
internal induction (`DescentArith.ineq6_internal`) consumes. This is brick 1 of the multi-lap wall;
brick 2 will be base-`b` digit extraction, brick 3 the hereditary base-change `bump`.
-/
section

open LO LO.FirstOrder LO.FirstOrder.Arithmetic

variable {V : Type*} [ORingStructure V] [V ⊧ₘ* 𝗜𝚺₁]

/-- Primitive-recursion blueprint for variable-base power: one parameter (the base `x = b`),
`zero ↦ 1`, `succ : ih ↦ ih * b`. -/
def pow.blueprint : PR.Blueprint 1 where
  zero := .mkSigma “y x. y = 1”
  succ := .mkSigma “y ih n x. y = ih * x”

/-- The model-side construction realizing `pow.blueprint`: `zero v = 1`, `succ v i ih = ih * b`. Both
component functions are `𝚺₀` (hence `𝚺₁`) so the engine yields a `𝚺₁`-definable result. -/
noncomputable def pow.construction : PR.Construction V pow.blueprint where
  zero := fun _ ↦ 1
  succ := fun x _ ih ↦ ih * x 0
  zero_defined := .mk fun v ↦ by simp [pow.blueprint]
  succ_defined := .mk fun v ↦ by simp [pow.blueprint]

/-- **Internalized variable-base power** `b ^ x` inside `V`, via primitive recursion on `x`. -/
noncomputable def ipow (b x : V) : V := pow.construction.result ![b] x

@[simp] lemma ipow_zero (b : V) : ipow b 0 = 1 := by simp [ipow, pow.construction]

@[simp] lemma ipow_succ (b x : V) : ipow b (x + 1) = ipow b x * b := by simp [ipow, pow.construction]

section

/-- `𝚺₁`-definition of `ipow`, with the argument order `(output, b, x)`. -/
def _root_.LO.FirstOrder.Arithmetic.ipowDef : 𝚺₁.Semisentence 3 :=
  pow.blueprint.resultDef.rew (Rew.subst ![#0, #2, #1])

instance ipow_defined : 𝚺₁-Function₂ (ipow : V → V → V) via ipowDef := .mk
  fun v ↦ by simp [pow.construction.result_defined_iff, ipowDef]; rfl

instance ipow_definable : 𝚺₁-Function₂ (ipow : V → V → V) := ipow_defined.to_definable

instance ipow_definable' (Γ) : Γ-[m + 1]-Function₂ (ipow : V → V → V) := ipow_definable.of_sigmaOne

end

/-! ### Power laws (internal induction in `𝗜𝚺₁`) -/

@[simp] lemma ipow_one (b : V) : ipow b 1 = b := by
  have : (1 : V) = 0 + 1 := by simp
  rw [this, ipow_succ, ipow_zero, one_mul]

lemma one_le_ipow {b : V} (hb : 1 ≤ b) (x : V) : 1 ≤ ipow b x := by
  induction x using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ x ih =>
    rw [ipow_succ]
    calc (1 : V) = 1 * 1 := by simp
      _ ≤ ipow b x * b := mul_le_mul' ih hb

lemma ipow_pos {b : V} (hb : 0 < b) (x : V) : 0 < ipow b x := by
  induction x using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ x ih => rw [ipow_succ]; exact mul_pos ih hb

lemma ipow_add (b x y : V) : ipow b (x + y) = ipow b x * ipow b y := by
  induction y using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ y ih =>
    rw [show x + (y + 1) = (x + y) + 1 from (add_assoc x y 1).symm,
      ipow_succ, ipow_succ, ih, mul_assoc]

lemma ipow_le_ipow_right {b : V} (hb : 1 ≤ b) {x y : V} (h : x ≤ y) :
    ipow b x ≤ ipow b y := by
  obtain ⟨d, rfl⟩ := le_iff_exists_add.mp h
  rw [ipow_add]
  calc ipow b x = ipow b x * 1 := by simp
    _ ≤ ipow b x * ipow b d := mul_le_mul_right (one_le_ipow hb d) _

lemma ipow_lt_ipow_right {b : V} (hb : 1 < b) {x y : V} (h : x < y) :
    ipow b x < ipow b y := by
  have hb0 : (0 : V) < b := lt_trans (by simp) hb
  have hb1 : (1 : V) ≤ b := le_of_lt hb
  obtain ⟨d, rfl⟩ := le_iff_exists_add.mp (le_of_lt h)
  have hd : 0 < d := by
    by_contra hd0
    have : d = 0 := by simpa using (nonpos_iff_eq_zero.mp (not_lt.mp hd0))
    rw [this] at h; simp at h
  rw [ipow_add]
  calc ipow b x = ipow b x * 1 := by simp
    _ < ipow b x * b := mul_lt_mul_of_pos_left hb (ipow_pos hb0 x)
    _ ≤ ipow b x * ipow b d := by
        apply _root_.mul_le_mul_right
        calc b = ipow b 1 := (ipow_one b).symm
          _ ≤ ipow b d := ipow_le_ipow_right hb1 (pos_iff_one_le.mp hd)

/-- `ipow` is monotone in the **base**: `b ≤ c → ipow b x ≤ ipow c x`. -/
lemma ipow_le_ipow_left {b c : V} (h : b ≤ c) (x : V) : ipow b x ≤ ipow c x := by
  induction x using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ x ih =>
    rw [ipow_succ, ipow_succ]
    exact mul_le_mul ih h (Arithmetic.zero_le b) (Arithmetic.zero_le (ipow c x))

/-- `ipow` is **strictly** monotone in the base at a positive exponent:
`b < c → 0 < x → ipow b x < ipow c x`. -/
lemma ipow_lt_ipow_left {b c : V} (hbc : b < c) {x : V} (hx : 0 < x) :
    ipow b x < ipow c x := by
  have hc0 : 0 < c := lt_of_le_of_lt (Arithmetic.zero_le b) hbc
  obtain ⟨m, rfl⟩ : ∃ m, x = m + 1 :=
    ⟨x - 1, (sub_add_self_of_le (pos_iff_one_le.mp hx)).symm⟩
  rw [ipow_succ, ipow_succ]
  exact mul_lt_mul' (ipow_le_ipow_left (le_of_lt hbc) m) hbc (Arithmetic.zero_le b) (ipow_pos hc0 m)

end

/-! ## InternalDigits -/
/-
# `InternalDigits.lean` — E-core(b) brick 2: base-`b` digits inside `V`

Brick 2 of the arithmetization wall (`DESCENT-PLAN.md §3`, after `InternalPow.ipow`). The PA-side
proof of Rathjen's inequality (6) is phrased over **base-`b` numerals**: the order comparison and the
hereditary base-change `bump` (`S^b_{b+1}`) are operations on the base-`b` digits of a number. This
file gives the digit accessor and its basic laws inside an arbitrary `V ⊧ₘ* 𝗜𝚺₁`:

* `idigit b n i = (n / b^i) % b` — the `i`-th base-`b` digit of `n`.

with `idigit b n i < b` (for `0 < b`) and the `𝚺₁`-definability needed for internal induction. Brick 3
will assemble these into the base-`b` hereditary base-change.
-/
section

open LO LO.FirstOrder LO.FirstOrder.Arithmetic

variable {V : Type*} [ORingStructure V] [V ⊧ₘ* 𝗜𝚺₁]

/-- **`i`-th base-`b` digit of `n`**: `(n / b^i) % b`. -/
noncomputable def idigit (b n i : V) : V := (n / ipow b i) % b

/-- Every base-`b` digit is `< b` (for a positive base). -/
@[simp] lemma idigit_lt {b : V} (hb : 0 < b) (n i : V) : idigit b n i < b :=
  mod_lt _ hb

lemma idigit_zero_exp (b n : V) : idigit b n 0 = n % b := by simp [idigit]

/-- **Digit shift.** The `(i+1)`-th base-`b` digit of `n` is the `i`-th digit of `n / b`. This is the
recursion that lets digit facts be proved by induction on the position. -/
lemma idigit_succ_exp (b n i : V) : idigit b n (i + 1) = idigit b (n / b) i := by
  unfold idigit
  rw [ipow_succ, mul_comm, LO.FirstOrder.Arithmetic.div_mul]

instance idigit_definable : 𝚺₁-Function₃ (idigit : V → V → V → V) := by
  unfold idigit; definability

end

/-! ## InternalLog -/
/-
# `InternalLog.lean` — E-core(b) brick 3: base-`b` logarithm inside `V`

Brick 3 of the arithmetization wall (`DESCENT-PLAN.md §3`). Rathjen's hereditary base-change `bump`
(`Defs.bump`) peels the **top** base-`b` power off `n`, i.e. it needs the top exponent
`e = log_b n` (`Nat.log b n`). Foundation ships base-2 `log` only, so we build the variable-base
`ilog b n` inside an arbitrary `V ⊧ₘ* 𝗜𝚺₁`, characterized (for `2 ≤ b`, `0 < n`) by

  `b ^ (ilog b n) ≤ n < b ^ (ilog b n + 1)`.

Built by the least-number principle exactly as Foundation builds base-2 `log` (least `e` with
`n < b^e`, predecessor is the logarithm). This is the last numeric prerequisite before the
hereditary base-change `bump` itself (brick 4).
-/
section

open LO LO.FirstOrder LO.FirstOrder.Arithmetic

variable {V : Type*} [ORingStructure V] [V ⊧ₘ* 𝗜𝚺₁]

/-- `x + 1 ≤ b ^ (x+1)` for `2 ≤ b`: the base bound that makes the log search terminate. -/
lemma succ_le_ipow_succ {b : V} (hb : 2 ≤ b) (x : V) : x + 1 ≤ ipow b (x + 1) := by
  have hb1 : (1 : V) ≤ b := le_trans (by simp) hb
  induction x using ISigma1.sigma1_succ_induction
  · definability
  case zero => simpa [ipow_one] using hb1
  case succ x ih =>
    rw [ipow_succ]
    have h1 : (1 : V) ≤ ipow b (x + 1) := one_le_ipow hb1 (x + 1)
    calc x + 1 + 1 ≤ ipow b (x + 1) + ipow b (x + 1) := add_le_add ih h1
      _ = ipow b (x + 1) * 2 := (mul_two _).symm
      _ ≤ ipow b (x + 1) * b := mul_le_mul_right hb _

lemma lt_ipow_succ {b : V} (hb : 2 ≤ b) (x : V) : x < ipow b (x + 1) :=
  lt_of_lt_of_le (by simp) (succ_le_ipow_succ hb x)

/-- The defining graph of `ilog`, stated unconditionally (so `ilog` is total): the characterizing
inequality `b^e ≤ n < b^(e+1)` when `2 ≤ b ∧ 0 < n`, and `e = 0` otherwise. -/
lemma ilog_exists_unique (b n : V) :
    ∃! e, ((2 ≤ b ∧ 0 < n) → ipow b e ≤ n ∧ n < ipow b (e + 1))
        ∧ (¬(2 ≤ b ∧ 0 < n) → e = 0) := by
  by_cases hmain : 2 ≤ b ∧ 0 < n
  · obtain ⟨hb, hpos⟩ := hmain
    have hb1 : (1 : V) ≤ b := le_trans (by simp) hb
    -- least `y` with `n < b^y`; the logarithm is its predecessor.
    have hP : 𝚺₁-Predicate (fun e => n < ipow b e) := by definability
    have hex : n < ipow b (n + 1) := lt_ipow_succ hb n
    obtain ⟨y, hy, hmin⟩ := InductionOnHierarchy.least_number 𝚺 1 hP hex
    have hy0 : y ≠ 0 := by
      rintro rfl; simp only [ipow_zero] at hy
      exact absurd (lt_one_iff_eq_zero.mp hy) (pos_iff_ne_zero.mp hpos)
    obtain ⟨e, rfl⟩ := (zero_or_succ y).resolve_left hy0
    have hle : ipow b e ≤ n := not_lt.mp (hmin e (by simp))
    refine ExistsUnique.intro e ⟨fun _ => ⟨hle, hy⟩, fun h => absurd ⟨hb, hpos⟩ h⟩ ?_
    rintro e' ⟨he', _⟩
    obtain ⟨hle', hlt'⟩ := he' ⟨hb, hpos⟩
    -- both satisfy `b^· ≤ n < b^(·+1)`; strict monotonicity forces equality.
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have : ipow b (e' + 1) ≤ ipow b e :=
        ipow_le_ipow_right hb1 (by simpa [lt_iff_succ_le] using h)
      exact absurd (lt_of_lt_of_le hlt' (le_trans this hle)) (by simp)
    · have : ipow b (e + 1) ≤ ipow b e' :=
        ipow_le_ipow_right hb1 (by simpa [lt_iff_succ_le] using h)
      exact absurd (lt_of_lt_of_le hy (le_trans this hle')) (by simp)
  · refine ExistsUnique.intro 0 ⟨fun h => absurd h hmain, fun _ => rfl⟩ ?_
    rintro e ⟨_, he⟩; exact he hmain

/-- **Base-`b` logarithm** in `V`: the top exponent of `n` in base `b` (`0` for `n = 0` or `b < 2`). -/
noncomputable def ilog (b n : V) : V := Classical.choose! (ilog_exists_unique b n)

/-- **Defining inequality of `ilog`**: for `2 ≤ b` and `0 < n`, `b^(ilog b n) ≤ n < b^(ilog b n + 1)`. -/
lemma ilog_spec {b n : V} (hb : 2 ≤ b) (hn : 0 < n) :
    ipow b (ilog b n) ≤ n ∧ n < ipow b (ilog b n + 1) :=
  (Classical.choose!_spec (ilog_exists_unique b n)).1 ⟨hb, hn⟩

lemma ipow_ilog_le {b n : V} (hb : 2 ≤ b) (hn : 0 < n) : ipow b (ilog b n) ≤ n :=
  (ilog_spec hb hn).1

lemma lt_ipow_ilog_succ {b n : V} (hb : 2 ≤ b) (hn : 0 < n) : n < ipow b (ilog b n + 1) :=
  (ilog_spec hb hn).2

/-- `1 ≤ ilog b n` once `b ≤ n` (the leading exponent is at least 1). If `ilog b n = 0` then
`n < ipow b 1 = b`, contradicting `b ≤ n`. -/
lemma ilog_pos {b n : V} (hb : 2 ≤ b) (hn : b ≤ n) : 1 ≤ ilog b n := by
  have hnpos : 0 < n := lt_of_lt_of_le (lt_of_lt_of_le (by simp) hb) hn
  by_contra h
  have h0 : ilog b n = 0 := nonpos_iff_eq_zero.mp (le_iff_lt_succ.mpr (by simpa using not_le.mp h))
  have hlt := lt_ipow_ilog_succ hb hnpos
  rw [h0, zero_add, ipow_one] at hlt
  exact absurd hlt (not_lt.mpr hn)

/-- **Monotonicity of `ilog`.** For `2 ≤ b` and `0 < n ≤ n'`, the leading exponent does not decrease:
`ilog b n ≤ ilog b n'`. (If it did, `b^(ilog b n) ≤ n ≤ n' < b^(ilog b n' + 1) ≤ b^(ilog b n)` — a
strict contradiction.) -/
lemma ilog_mono {b n n' : V} (hb : 2 ≤ b) (hn : 0 < n) (hle : n ≤ n') : ilog b n ≤ ilog b n' := by
  have hb1 : (1 : V) ≤ b := le_trans (by simp) hb
  have hn' : 0 < n' := lt_of_lt_of_le hn hle
  by_contra h
  -- `ilog b n' < ilog b n`, i.e. `ilog b n' + 1 ≤ ilog b n`.
  have hstep : ilog b n' + 1 ≤ ilog b n := lt_iff_succ_le.mp (not_le.mp h)
  have h1 : n' < ipow b (ilog b n' + 1) := lt_ipow_ilog_succ hb hn'
  have h2 : ipow b (ilog b n' + 1) ≤ ipow b (ilog b n) := ipow_le_ipow_right hb1 hstep
  have h3 : ipow b (ilog b n) ≤ n := ipow_ilog_le hb hn
  exact absurd (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_le_of_lt hle h1) h2) h3) (_root_.lt_irrefl n)

/-- Graph of `ilog`, for the `𝚺₁`-definability instance below. -/
lemma ilog_graph {e b n : V} :
    e = ilog b n ↔ ((2 ≤ b ∧ 0 < n) → ipow b e ≤ n ∧ n < ipow b (e + 1))
        ∧ (¬(2 ≤ b ∧ 0 < n) → e = 0) :=
  Classical.choose!_eq_iff_right _

def _root_.LO.FirstOrder.Arithmetic.ilogDef : 𝚺₁.Semisentence 3 := .mkSigma
  “e b n. (2 ≤ b ∧ 0 < n → (∃ pe, !ipowDef pe b e ∧ pe ≤ n) ∧ (∃ pf, !ipowDef pf b (e + 1) ∧ n < pf))
        ∧ (¬(2 ≤ b ∧ 0 < n) → e = 0)”

instance ilog_defined : 𝚺₁-Function₂ (ilog : V → V → V) via ilogDef := .mk fun v ↦ by
  simp [ilogDef, ilog_graph, ipow_defined.iff]
  refine fun _ => ⟨fun h hyp => h ?_, fun h hyp => h (fun h2 => hyp.resolve_left (not_lt.mpr h2))⟩
  by_cases h2 : 2 ≤ v 1
  · exact Or.inr (hyp h2)
  · exact Or.inl (not_le.mp h2)

instance ilog_definable : 𝚺₁-Function₂ (ilog : V → V → V) := ilog_defined.to_definable

instance ilog_definable' (Γ) : Γ-[m + 1]-Function₂ (ilog : V → V → V) := ilog_definable.of_sigmaOne

end

/-! ## InternalBump -/
/-
# `InternalBump.lean` — E-core(b) brick 4: the hereditary base-change `bump` inside `V`

Brick 4 (`DESCENT-PLAN.md §3`). `Defs.bump b n` is course-of-values recursion (it recurses at
`e = log_b n` and `r = n mod b^e`, both `< n`). To realize it inside `V ⊧ₘ* 𝗜𝚺₁` we use the standard
table reduction of strong recursion to primitive recursion (`HFS/PRF.lean`'s `PR.Construction`):

* `bumpNext b M s` — the value `bump b M` computed from the **table** `s = ⟨bump b 0,…,bump b (M-1)⟩`
  (length `M`): peel the top base-`b` power of `M` and read the two recursive sub-results out of `s`.

This file establishes `bumpNext` and its `𝚺₁`-definability (the artifact the table's `PR.Blueprint`
references). Brick 4b will assemble the table itself via `PR.Construction`, brick 4c will read off
`ibump b n := (table b n).[n]` and prove it satisfies `Defs.bump`'s recursion.
-/
section

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.HierarchySymbol

variable {V : Type*} [ORingStructure V] [V ⊧ₘ* 𝗜𝚺₁]

/-- **Table step of `bump`.** Given the table `s = ⟨bump b 0,…,bump b (M-1)⟩`, compute `bump b M` by
peeling the top base-`b` power: `e = ilog b M`, top coefficient `M / b^e`, exponent result `s.[e]`,
remainder result `s.[M % b^e]`. (For `M ≥ 1` with a correct table this equals `Defs.bump b M`.) -/
noncomputable def bumpNext (b M s : V) : V :=
  M / ipow b (ilog b M) * ipow (b + 1) (znth s (ilog b M)) + znth s (M % ipow b (ilog b M))

/-- The `𝚺₁` graph-definition of `bumpNext`, composing `ilog`, `ipow`, `znth`, `div`, `rem`. -/
def _root_.LO.FirstOrder.Arithmetic.bumpNextDef : 𝚺₁.Semisentence 4 := .mkSigma
  “y b M s.
    ∃ e, !ilogDef e b M ∧ ∃ pe, !ipowDef pe b e ∧ ∃ te, !znthDef te s e ∧
      ∃ pte, !ipowDef pte (b + 1) te ∧ ∃ q, !divDef q M pe ∧ ∃ r, !remDef r M pe ∧
        ∃ tr, !znthDef tr s r ∧ y = q * pte + tr”

instance bumpNext_defined : 𝚺₁-Function₃ (bumpNext : V → V → V → V) via bumpNextDef := .mk fun v ↦ by
  simp [bumpNextDef, bumpNext, ilog_defined.iff, ipow_defined.iff, znth_defined.iff,
    div_defined.iff, rem_defined.iff]

instance bumpNext_definable : 𝚺₁-Function₃ (bumpNext : V → V → V → V) := bumpNext_defined.to_definable

/-! ### The `bump` table via primitive recursion -/

/-- Blueprint for the `bump` table: `bumpTable b 0 = ⟨0⟩`, `bumpTable b (n+1)` appends
`bumpNext b (n+1) (bumpTable b n)`. -/
def bumpTable.blueprint : PR.Blueprint 1 where
  zero := .mkSigma “y x. !mkSeq₁Def y 0”
  succ := .mkSigma “y ih n x. ∃ v, !bumpNextDef v x (n + 1) ih ∧ !seqConsDef y ih v”

noncomputable def bumpTable.construction : PR.Construction V bumpTable.blueprint where
  zero := fun _ ↦ !⟦0⟧
  succ := fun x n ih ↦ seqCons ih (bumpNext (x 0) (n + 1) ih)
  zero_defined := .mk fun v ↦ by
    simp [bumpTable.blueprint, mkSeq₁Def, seqCons_defined.iff, emptyset_def]
  succ_defined := .mk fun v ↦ by
    simp [bumpTable.blueprint, bumpNext_defined.iff, seqCons_defined.iff]

/-- **The `bump` table** inside `V`: `ibumpTable b n = ⟨bump b 0,…,bump b n⟩` (length `n+1`). -/
noncomputable def ibumpTable (b n : V) : V := bumpTable.construction.result ![b] n

@[simp] lemma ibumpTable_zero (b : V) : ibumpTable b 0 = !⟦0⟧ := by
  simp [ibumpTable, bumpTable.construction]

@[simp] lemma ibumpTable_succ (b n : V) :
    ibumpTable b (n + 1) = seqCons (ibumpTable b n) (bumpNext b (n + 1) (ibumpTable b n)) := by
  simp [ibumpTable, bumpTable.construction]

/-- **Internalized hereditary base-change** `bump b n` in `V`: the `n`-th entry of the table. -/
noncomputable def ibump (b n : V) : V := znth (ibumpTable b n) n

section

def _root_.LO.FirstOrder.Arithmetic.ibumpTableDef : 𝚺₁.Semisentence 3 :=
  bumpTable.blueprint.resultDef.rew (Rew.subst ![#0, #2, #1])

instance ibumpTable_defined : 𝚺₁-Function₂ (ibumpTable : V → V → V) via ibumpTableDef := .mk
  fun v ↦ by simp [bumpTable.construction.result_defined_iff, ibumpTableDef]; rfl

instance ibumpTable_definable : 𝚺₁-Function₂ (ibumpTable : V → V → V) := ibumpTable_defined.to_definable

instance ibumpTable_definable' (Γ) : Γ-[m + 1]-Function₂ (ibumpTable : V → V → V) :=
  ibumpTable_definable.of_sigmaOne

def _root_.LO.FirstOrder.Arithmetic.ibumpDef : 𝚺₁.Semisentence 3 := .mkSigma
  “y b n. ∃ t, !ibumpTableDef t b n ∧ !znthDef y t n”

instance ibump_defined : 𝚺₁-Function₂ (ibump : V → V → V) via ibumpDef := .mk fun v ↦ by
  simp [ibumpDef, ibump, ibumpTable_defined.iff, znth_defined.iff]

instance ibump_definable : 𝚺₁-Function₂ (ibump : V → V → V) := ibump_defined.to_definable

instance ibump_definable' (Γ) : Γ-[m + 1]-Function₂ (ibump : V → V → V) :=
  ibump_definable.of_sigmaOne

end

/-! ### Structural correctness of the table

`definability`/aesop cannot discharge predicates over `ibumpTable` (its `PR.result` definability
leaf makes the `isDefEq` search blow up), so the `𝚺₁`-predicate side conditions of the inductions
below are supplied as **explicit composition terms** via the helpers here. -/

/-- `fun v ↦ ibumpTable b (v i)` is `𝚺₁`-definable (explicit composition, no search). -/
private lemma def_ibumpTable {k} (b : V) (i : Fin k) :
    𝚺-[1].DefinableFunction (fun v : Fin k → V ↦ ibumpTable b (v i)) :=
  DefinableFunction₂.comp (F := ibumpTable) (DefinableFunction.const b) (DefinableFunction.var i)

private lemma def_ibump {k} (b : V) (i : Fin k) :
    𝚺-[1].DefinableFunction (fun v : Fin k → V ↦ ibump b (v i)) :=
  DefinableFunction₂.comp (F := ibump) (DefinableFunction.const b) (DefinableFunction.var i)

@[simp] lemma ibumpTable_seq (b n : V) : Seq (ibumpTable b n) := by
  induction n using ISigma1.sigma1_succ_induction
  · exact Definable.comp₁ (def_ibumpTable b 0)
  case zero => simp
  case succ n ih => rw [ibumpTable_succ]; exact ih.seqCons _

@[simp] lemma ibumpTable_lh (b n : V) : lh (ibumpTable b n) = n + 1 := by
  induction n using ISigma1.sigma1_succ_induction
  · exact Definable.comp₂ (DefinableFunction₁.comp (F := lh) (def_ibumpTable b 0))
      (by definability)
  case zero => simp
  case succ n ih => rw [ibumpTable_succ, Seq.lh_seqCons _ (ibumpTable_seq b n), ih]

/-- Earlier entries of a `seqCons` are preserved. -/
lemma znth_seqCons_of_lt {s : V} (h : Seq s) (x : V) {i} (hi : i < lh s) :
    znth (seqCons s x) i = znth s i :=
  (h.seqCons x).znth_eq_of_mem (Seq.subset_seqCons s x (h.znth hi))

lemma znth_ibumpTable_succ {b n k : V} (hk : k < n + 1) :
    znth (ibumpTable b (n + 1)) k = znth (ibumpTable b n) k := by
  rw [ibumpTable_succ]
  exact znth_seqCons_of_lt (ibumpTable_seq b n) _ (by rw [ibumpTable_lh]; exact hk)

@[simp] lemma ibump_zero (b : V) : ibump b 0 = 0 := by
  simp only [ibump, ibumpTable_zero]
  exact (singleton_seq 0).znth_eq_of_mem ((mem_singleton_seq_iff 0 0).mpr rfl)

/-- **Table stability.** Every entry of the length-`(N+1)` table is the genuine `ibump` value. -/
lemma znth_ibumpTable_eq_ibump (b : V) : ∀ N, ∀ k ≤ N, znth (ibumpTable b N) k = ibump b k := by
  intro N
  induction N using ISigma1.sigma1_succ_induction
  · refine Definable.ball_le (by definability) ?_
    exact Definable.comp₂
      (DefinableFunction₂.comp (F := znth) (def_ibumpTable b 1) (DefinableFunction.var 0))
      (def_ibump b 0)
  case zero =>
    intro k hk
    rcases (nonpos_iff_eq_zero.mp hk) with rfl
    rfl
  case succ N ih =>
    intro k hk
    rcases eq_or_lt_of_le hk with rfl | hlt
    · rfl
    · rw [znth_ibumpTable_succ hlt]
      exact ih k (le_iff_lt_succ.mpr hlt)

/-! ### The `bump` recursion equation -/

/-- `x < b^x` for `2 ≤ b`: makes the top exponent of `n+1` land `≤ n`. -/
lemma self_lt_ipow {b : V} (hb : 2 ≤ b) (x : V) : x < ipow b x := by
  have hb0 : (0 : V) < b := lt_of_lt_of_le (by simp) hb
  induction x using ISigma1.sigma1_succ_induction
  · definability
  case zero => exact ipow_pos hb0 0
  case succ x ih =>
    rw [ipow_succ]
    calc x + 1 ≤ ipow b x := lt_iff_succ_le.mp ih
      _ < ipow b x + ipow b x := lt_add_of_pos_right _ (ipow_pos hb0 x)
      _ = ipow b x * 2 := (mul_two _).symm
      _ ≤ ipow b x * b := mul_le_mul_right hb _

lemma znth_seqCons_self {s : V} (h : Seq s) (x : V) : znth (seqCons s x) (lh s) = x :=
  (h.seqCons x).znth_eq_of_mem (lh_mem_seqCons s x)

/-- **The internal `bump` recursion** — `ibump` satisfies the peel recursion of `Defs.bump`:
`bump b (n+1) = (n+1)/b^e · (b+1)^(bump b e) + bump b r`, with `e = ilog b (n+1)`, `r = (n+1) mod b^e`.
This is the machine-checked statement that the table truly computes the hereditary base-change. -/
lemma ibump_succ {b : V} (hb : 2 ≤ b) (n : V) :
    ibump b (n + 1)
      = (n + 1) / ipow b (ilog b (n + 1)) * ipow (b + 1) (ibump b (ilog b (n + 1)))
        + ibump b ((n + 1) % ipow b (ilog b (n + 1))) := by
  have hb0 : (0 : V) < b := lt_of_lt_of_le (by simp) hb
  have hpos : (0 : V) < n + 1 := by simp
  have hpe : 0 < ipow b (ilog b (n + 1)) := ipow_pos hb0 _
  have hen : ilog b (n + 1) ≤ n :=
    le_iff_lt_succ.mpr (lt_of_lt_of_le (self_lt_ipow hb _) (ipow_ilog_le hb hpos))
  have hrn : (n + 1) % ipow b (ilog b (n + 1)) ≤ n :=
    le_iff_lt_succ.mpr (lt_of_lt_of_le (mod_lt _ hpe) (ipow_ilog_le hb hpos))
  have key : znth (ibumpTable b (n + 1)) (n + 1) = bumpNext b (n + 1) (ibumpTable b n) := by
    rw [ibumpTable_succ]
    have := znth_seqCons_self (ibumpTable_seq b n) (bumpNext b (n + 1) (ibumpTable b n))
    rwa [ibumpTable_lh] at this
  rw [ibump, key, bumpNext,
    znth_ibumpTable_eq_ibump b n (ilog b (n + 1)) hen,
    znth_ibumpTable_eq_ibump b n ((n + 1) % ipow b (ilog b (n + 1))) hrn]

/-- **The internal `bump` recursion at any positive argument** (general form of `ibump_succ`):
`ibump b n = n/b^e · (b+1)^(ibump b e) + ibump b (n mod b^e)` with `e = ilog b n`, for `0 < n`. The
workhorse equation behind the strong-induction internal `bump` lemmas (the `Δ₀`-numeral analogues of
`Domination`'s `ℕ` facts). -/
lemma ibump_pos {b : V} (hb : 2 ≤ b) {n : V} (hn : 0 < n) :
    ibump b n
      = n / ipow b (ilog b n) * ipow (b + 1) (ibump b (ilog b n))
        + ibump b (n % ipow b (ilog b n)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 :=
    ⟨n - 1, (sub_add_self_of_le (pos_iff_one_le.mp hn)).symm⟩
  exact ibump_succ hb m

/-- **`n ≤ ibump b n`** (internal analogue of `Domination.le_bump`). The hereditary base-change never
shrinks its argument: each digit-block grows (`b^e ≤ (b+1)^(ibump b e)`) and the remainder dominates
its own bump by the strong IH. Proved by `𝚺₁` order-induction on `n`, peeling via `ibump_pos`. -/
theorem le_ibump {b : V} (hb : 2 ≤ b) : ∀ n, n ≤ ibump b n := by
  have hb0 : (0 : V) < b := lt_of_lt_of_le (by simp) hb
  intro n
  induction n using ISigma1.sigma1_order_induction
  · exact Definable.comp₂ (DefinableFunction.var 0) (def_ibump b 0)
  case ind n ih =>
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · have hnpos : 0 < n := pos_iff_ne_zero.mpr hn
      set e := ilog b n with he
      have hpe : 0 < ipow b e := ipow_pos hb0 e
      have hen : e < n :=
        lt_of_lt_of_le (self_lt_ipow hb e) (ipow_ilog_le hb hnpos)
      have hrn : n % ipow b e < n :=
        lt_of_lt_of_le (mod_lt _ hpe) (ipow_ilog_le hb hnpos)
      rw [ibump_pos hb hnpos, ← he]
      -- leading block: b^e ≤ (b+1)^(ibump b e)
      have h1 : ipow b e ≤ ipow (b + 1) (ibump b e) :=
        le_trans (ipow_le_ipow_left (by simp) e) (ipow_le_ipow_right (by simp) (ih e hen))
      have h2 : n % ipow b e ≤ ibump b (n % ipow b e) := ih _ hrn
      have hdm : n / ipow b e * ipow b e + n % ipow b e = n := by
        rw [mul_comm]; exact div_add_mod n (ipow b e)
      calc n = n / ipow b e * ipow b e + n % ipow b e := hdm.symm
        _ ≤ n / ipow b e * ipow (b + 1) (ibump b e) + ibump b (n % ipow b e) := by
            gcongr
        _ = _ := rfl

/-- **Strict growth above the base** (internal analogue of `Domination.bump_gt`): for `b ≤ n`, one
hereditary base-change strictly increases the value, `n + 1 ≤ ibump b n`. The leading power `b^L`
(`L = ilog b n ≥ 1`) is sent to `(b+1)^(ibump b L) > b^L`, so the leading term alone already exceeds
`n`. Digit-direct (no ordinals), so it internalizes; the `ℕ` proof's ordinal route does not. -/
theorem ibump_gt {b : V} (hb : 2 ≤ b) {n : V} (hn : b ≤ n) : n + 1 ≤ ibump b n := by
  have hb0 : (0 : V) < b := lt_of_lt_of_le (by simp) hb
  have hnpos : (0 : V) < n := lt_of_lt_of_le hb0 hn
  set L := ilog b n with hL
  have hL1 : 1 ≤ L := ilog_pos hb hn
  have hbe_pos : 0 < ipow b L := ipow_pos hb0 L
  have hbe_le : ipow b L ≤ n := ipow_ilog_le hb hnpos
  have hq1 : 1 ≤ n / ipow b L := by
    rcases eq_or_ne (n / ipow b L) 0 with h0 | h0
    · exfalso
      have hlt := lt_mul_div n hbe_pos
      rw [h0] at hlt; simp at hlt
      exact absurd hlt (not_lt.mpr hbe_le)
    · exact pos_iff_one_le.mp (pos_iff_ne_zero.mpr h0)
  have hpow_lt : ipow b L < ipow (b + 1) L :=
    ipow_lt_ipow_left (by simp) (pos_iff_one_le.mpr hL1)
  have hpow_le : ipow (b + 1) L ≤ ipow (b + 1) (ibump b L) :=
    ipow_le_ipow_right (by simp) (le_ibump hb L)
  have hP : ipow b L + 1 ≤ ipow (b + 1) (ibump b L) :=
    lt_iff_succ_le.mp (lt_of_lt_of_le hpow_lt hpow_le)
  have hr_le : n % ipow b L ≤ ibump b (n % ipow b L) := le_ibump hb _
  have hbump := ibump_pos hb hnpos
  have hn_eq : n / ipow b L * ipow b L + n % ipow b L = n := by
    rw [mul_comm]; exact div_add_mod n (ipow b L)
  rw [← hL] at hbump
  set q := n / ipow b L with hq
  set BL := ipow b L with hBL
  set P := ipow (b + 1) (ibump b L) with hPdef
  have hmul : q * (BL + 1) ≤ q * P := by gcongr
  have hexp : q * (BL + 1) = q * BL + q := by rw [mul_add, mul_one]
  have hkey : q * BL + q ≤ q * P := hexp ▸ hmul
  rw [hbump]
  have hge : q * BL + q + n % BL ≤ q * P + ibump b (n % BL) := add_le_add hkey hr_le
  have heq : n + 1 ≤ q * BL + q + n % BL := by
    have e1 : q * BL + q + n % BL = q * BL + n % BL + q := add_right_comm _ _ _
    rw [e1, hn_eq]
    exact add_le_add (le_refl n) hq1
  exact le_trans heq hge

/-! ### Strict monotonicity of `ibump` (combined upper-bound + monotonicity induction)

The hereditary base-change is strictly monotone in its argument. As with `evalNat_reflect_combined`
(`InternalONote`), the value-bound `ibump b n < (b+1)^(ibump b (ilog b n) + 1)` and the strict
monotonicity are mutually recursive — increasing the leading coefficient dominates the whole tail iff
the tail is bounded by the leading power — so both are carried in one strong induction on the value.
Digit-direct (no ordinals), so it internalizes. (Port of the Aristotle `ibump_mono` blueprint into
clean `IΣ₁` arithmetic, replacing its `nlinarith`/`grind` with manual ordered-semiring steps.) -/

private def IBcombined (b w : V) : Prop :=
  (∀ n ≤ w, 0 < n → ibump b n < ipow (b + 1) (ibump b (ilog b n) + 1)) ∧
  (∀ n ≤ w, ∀ n' ≤ w, n < n' → ibump b n < ibump b n')

private theorem ibump_combined {b : V} (hb : 2 ≤ b) : ∀ w, IBcombined b w := by
  have hb0 : (0 : V) < b := lt_of_lt_of_le (by simp) hb
  have hb1 : (1 : V) ≤ b := le_trans (by simp) hb
  have hb0' : (0 : V) < b + 1 := lt_of_lt_of_le (by simp) (le_trans hb (by simp))
  have hb1' : (1 : V) ≤ b + 1 := le_trans hb1 (by simp)
  intro w
  induction w using ISigma1.sigma1_order_induction
  · unfold IBcombined; definability
  case ind w ih =>
    -- The upper-bound component, established once (used by MONO too).
    have hUB : ∀ n ≤ w, 0 < n → ibump b n < ipow (b + 1) (ibump b (ilog b n) + 1) := by
      intro n hnw hnpos
      have hDpos : 0 < ipow b (ilog b n) := ipow_pos hb0 _
      have hDle : ipow b (ilog b n) ≤ n := ipow_ilog_le hb hnpos
      have hq_lt : n / ipow b (ilog b n) < b := by
        apply div_lt_of_lt_mul
        have := lt_ipow_ilog_succ hb hnpos
        rwa [ipow_succ, mul_comm] at this
      have hr_lt : n % ipow b (ilog b n) < ipow b (ilog b n) := mod_lt _ hDpos
      have hr_w : n % ipow b (ilog b n) < w :=
        lt_of_lt_of_le (lt_of_lt_of_le hr_lt hDle) hnw
      -- tail block bound: ibump b (n % D) < (b+1)^(ibump b (ilog b n))
      have htail : ibump b (n % ipow b (ilog b n)) < ipow (b + 1) (ibump b (ilog b n)) := by
        rcases eq_or_ne (n % ipow b (ilog b n)) 0 with h0 | h0
        · rw [h0, ibump_zero]; exact ipow_pos hb0' _
        · have hr_pos : 0 < n % ipow b (ilog b n) := pos_iff_ne_zero.mpr h0
          have hlog_lt : ilog b (n % ipow b (ilog b n)) < ilog b n := by
            by_contra hc
            have h1 : ipow b (ilog b n) ≤ ipow b (ilog b (n % ipow b (ilog b n))) :=
              ipow_le_ipow_right hb1 (not_lt.mp hc)
            have h2 := ipow_ilog_le hb hr_pos
            exact absurd (lt_of_lt_of_le hr_lt (le_trans h1 h2)) (_root_.lt_irrefl _)
          have he_w : ilog b n < w := lt_of_lt_of_le (lt_of_lt_of_le (self_lt_ipow hb _) hDle) hnw
          have hlog_w : ilog b (n % ipow b (ilog b n)) < w := lt_trans hlog_lt he_w
          have hUBr := (ih _ hr_w).1 _ le_rfl hr_pos
          have hmono_exp : ibump b (ilog b (n % ipow b (ilog b n))) < ibump b (ilog b n) :=
            (ih _ (max_lt hlog_w he_w)).2 _ (le_max_left _ _) _ (le_max_right _ _) hlog_lt
          exact lt_of_lt_of_le hUBr (ipow_le_ipow_right hb1' (lt_iff_succ_le.mp hmono_exp))
      rw [ibump_pos hb hnpos]
      calc n / ipow b (ilog b n) * ipow (b + 1) (ibump b (ilog b n))
              + ibump b (n % ipow b (ilog b n))
          < n / ipow b (ilog b n) * ipow (b + 1) (ibump b (ilog b n))
              + ipow (b + 1) (ibump b (ilog b n)) := by gcongr
        _ = (n / ipow b (ilog b n) + 1) * ipow (b + 1) (ibump b (ilog b n)) := by
            rw [add_mul, one_mul]
        _ ≤ b * ipow (b + 1) (ibump b (ilog b n)) := by gcongr; exact lt_iff_succ_le.mp hq_lt
        _ < b * ipow (b + 1) (ibump b (ilog b n)) + ipow (b + 1) (ibump b (ilog b n)) :=
            lt_add_of_pos_right _ (ipow_pos hb0' _)
        _ = (b + 1) * ipow (b + 1) (ibump b (ilog b n)) := by rw [add_mul, one_mul]
        _ = ipow (b + 1) (ibump b (ilog b n) + 1) := by rw [ipow_succ, mul_comm]
    refine ⟨hUB, ?_⟩
    -- MONO component.
    intro n hnw n' hn'w hnn'
    rcases eq_or_ne n 0 with rfl | hn0
    · rw [ibump_zero]
      exact lt_of_lt_of_le hnn' (le_ibump hb n')
    · have hnpos : 0 < n := pos_iff_ne_zero.mpr hn0
      have hn'pos : 0 < n' := lt_trans hnpos hnn'
      have hee' : ilog b n ≤ ilog b n' := ilog_mono hb hnpos hnn'.le
      have hD'pos : 0 < ipow b (ilog b n') := ipow_pos hb0 _
      have hD'le : ipow b (ilog b n') ≤ n' := ipow_ilog_le hb hn'pos
      have he_w : ilog b n < w :=
        lt_of_lt_of_le (lt_of_lt_of_le (self_lt_ipow hb _) (ipow_ilog_le hb hnpos)) hnw
      have he'_w : ilog b n' < w :=
        lt_of_lt_of_le (lt_of_lt_of_le (self_lt_ipow hb _) hD'le) hn'w
      -- leading coefficient of n' is ≥ 1
      have hq'1 : 1 ≤ n' / ipow b (ilog b n') := by
        rcases eq_or_ne (n' / ipow b (ilog b n')) 0 with h0 | h0
        · exfalso
          have hdm := div_add_mod n' (ipow b (ilog b n'))
          rw [h0, mul_zero, zero_add] at hdm
          have hlt : n' % ipow b (ilog b n') < ipow b (ilog b n') := mod_lt n' hD'pos
          rw [hdm] at hlt
          exact absurd hD'le (not_le.mpr hlt)
        · exact pos_iff_one_le.mp (pos_iff_ne_zero.mpr h0)
      -- the leading term of `ibump b n'` dominates `(b+1)^(ibump b (ilog b n'))`
      have hlead : ipow (b + 1) (ibump b (ilog b n')) ≤ ibump b n' := by
        rw [ibump_pos hb hn'pos]
        calc ipow (b + 1) (ibump b (ilog b n'))
            = 1 * ipow (b + 1) (ibump b (ilog b n')) := (one_mul _).symm
          _ ≤ n' / ipow b (ilog b n') * ipow (b + 1) (ibump b (ilog b n')) := by gcongr
          _ ≤ n' / ipow b (ilog b n') * ipow (b + 1) (ibump b (ilog b n'))
              + ibump b (n' % ipow b (ilog b n')) := le_self_add
      rcases lt_or_eq_of_le hee' with hlt | heq
      · -- distinct leading exponents
        have hmono_exp : ibump b (ilog b n) < ibump b (ilog b n') :=
          (ih _ (max_lt he_w he'_w)).2 _ (le_max_left _ _) _ (le_max_right _ _) hlt
        calc ibump b n < ipow (b + 1) (ibump b (ilog b n) + 1) := hUB n hnw hnpos
          _ ≤ ipow (b + 1) (ibump b (ilog b n')) :=
              ipow_le_ipow_right hb1' (lt_iff_succ_le.mp hmono_exp)
          _ ≤ ibump b n' := hlead
      · -- equal leading exponents: compare leading coefficients, then remainders
        have hDpos : 0 < ipow b (ilog b n) := ipow_pos hb0 _
        have hr_lt : n % ipow b (ilog b n) < ipow b (ilog b n) := mod_lt _ hDpos
        have hr'_lt : n' % ipow b (ilog b n') < ipow b (ilog b n') := mod_lt _ hD'pos
        have hr_w : n % ipow b (ilog b n) < w :=
          lt_of_lt_of_le (lt_of_lt_of_le hr_lt (ipow_ilog_le hb hnpos)) hnw
        -- the tail block of `n` is bounded by the leading power (same UB argument as above)
        have htail_n : ibump b (n % ipow b (ilog b n)) < ipow (b + 1) (ibump b (ilog b n)) := by
          rcases eq_or_ne (n % ipow b (ilog b n)) 0 with h0 | h0
          · rw [h0, ibump_zero]; exact ipow_pos hb0' _
          · have hr_pos : 0 < n % ipow b (ilog b n) := pos_iff_ne_zero.mpr h0
            have hlog_lt : ilog b (n % ipow b (ilog b n)) < ilog b n := by
              by_contra hc
              have h1 : ipow b (ilog b n) ≤ ipow b (ilog b (n % ipow b (ilog b n))) :=
                ipow_le_ipow_right hb1 (not_lt.mp hc)
              exact absurd (lt_of_lt_of_le hr_lt (le_trans h1 (ipow_ilog_le hb hr_pos)))
                (_root_.lt_irrefl _)
            have hlog_w : ilog b (n % ipow b (ilog b n)) < w := lt_trans hlog_lt he_w
            have hmono_exp : ibump b (ilog b (n % ipow b (ilog b n))) < ibump b (ilog b n) :=
              (ih _ (max_lt hlog_w he_w)).2 _ (le_max_left _ _) _ (le_max_right _ _) hlog_lt
            exact lt_of_lt_of_le ((ih _ hr_w).1 _ le_rfl hr_pos)
              (ipow_le_ipow_right hb1' (lt_iff_succ_le.mp hmono_exp))
        rw [ibump_pos hb hnpos, ibump_pos hb hn'pos, heq]
        rw [heq] at htail_n
        rcases lt_trichotomy (n / ipow b (ilog b n')) (n' / ipow b (ilog b n')) with hq | hq | hq
        · -- leading coefficients separate
          calc n / ipow b (ilog b n') * ipow (b + 1) (ibump b (ilog b n'))
                  + ibump b (n % ipow b (ilog b n'))
              < n / ipow b (ilog b n') * ipow (b + 1) (ibump b (ilog b n'))
                  + ipow (b + 1) (ibump b (ilog b n')) := by gcongr
            _ = (n / ipow b (ilog b n') + 1) * ipow (b + 1) (ibump b (ilog b n')) := by
                rw [add_mul, one_mul]
            _ ≤ n' / ipow b (ilog b n') * ipow (b + 1) (ibump b (ilog b n')) := by
                gcongr; exact lt_iff_succ_le.mp hq
            _ ≤ n' / ipow b (ilog b n') * ipow (b + 1) (ibump b (ilog b n'))
                + ibump b (n' % ipow b (ilog b n')) := le_self_add
        · -- equal leading coefficients ⟹ remainders strictly ordered
          have hr'_w : n' % ipow b (ilog b n') < w :=
            lt_of_lt_of_le (lt_of_lt_of_le hr'_lt hD'le) hn'w
          have hrr : n % ipow b (ilog b n') < n' % ipow b (ilog b n') := by
            have hdn := div_add_mod n (ipow b (ilog b n'))
            have hdn' := div_add_mod n' (ipow b (ilog b n'))
            rw [← hq] at hdn'
            have hkey : ipow b (ilog b n') * (n / ipow b (ilog b n')) + n % ipow b (ilog b n')
                < ipow b (ilog b n') * (n / ipow b (ilog b n')) + n' % ipow b (ilog b n') := by
              rw [hdn, hdn']; exact hnn'
            exact lt_of_add_lt_add_left hkey
          have hmono_r : ibump b (n % ipow b (ilog b n')) < ibump b (n' % ipow b (ilog b n')) :=
            (ih _ hr'_w).2 _ (le_of_lt hrr) _ le_rfl hrr
          rw [hq]; gcongr
        · -- n'/D < n/D contradicts n < n'
          refine absurd ?_ (lt_asymm hnn')
          calc n' = ipow b (ilog b n') * (n' / ipow b (ilog b n')) + n' % ipow b (ilog b n') :=
                (div_add_mod n' (ipow b (ilog b n'))).symm
            _ < ipow b (ilog b n') * (n' / ipow b (ilog b n')) + ipow b (ilog b n') := by gcongr
            _ = ipow b (ilog b n') * (n' / ipow b (ilog b n') + 1) := by rw [mul_add, mul_one]
            _ ≤ ipow b (ilog b n') * (n / ipow b (ilog b n')) := by
                gcongr; exact lt_iff_succ_le.mp hq
            _ ≤ ipow b (ilog b n') * (n / ipow b (ilog b n')) + n % ipow b (ilog b n') := le_self_add
            _ = n := div_add_mod n (ipow b (ilog b n'))

/-- **`ibump b` is strictly monotone** in its argument (`2 ≤ b`). -/
theorem ibump_strictMono {b : V} (hb : 2 ≤ b) {n n' : V} (h : n < n') :
    ibump b n < ibump b n' :=
  (ibump_combined hb (max n n')).2 n (le_max_left _ _) n' (le_max_right _ _) h

/-- **`ibump b` is monotone** in its argument (`2 ≤ b`) — the weak form the descent's `ineq6_step`
consumes: a larger Goodstein value bumps to a larger value. -/
theorem ibump_mono {b : V} (hb : 2 ≤ b) {n n' : V} (h : n ≤ n') :
    ibump b n ≤ ibump b n' := by
  rcases eq_or_lt_of_le h with rfl | h
  · exact le_rfl
  · exact le_of_lt (ibump_strictMono hb h)

end

/-! ## InternalGoodstein -/
/-
# `InternalGoodstein.lean` — E-core(b) brick 5: the internal Goodstein sequence in `V`

Brick 5 (`DESCENT-PLAN.md §3`). With the hereditary base-change `ibump` built and proven correct
(`InternalBump`), the Goodstein run itself is **structural** recursion on the step index (single
predecessor), so it goes straight through `PR.Construction`:

  `Defs.goodsteinSeq m 0 = m`,   `Defs.goodsteinSeq m (k+1) = bump (k+2) (goodsteinSeq m k) - 1`.

`igoodstein m₀ k` is the `𝚺₁`-definable run `k ↦ mₖ` inside an arbitrary `V ⊧ₘ* 𝗜𝚺₁` — the concrete
`m : V → V` that `DescentArith.ineq6_internal` abstracts over. Brick 6 will be the `b`-side bound
`T̂^{k+2}∘β` and the internal `ineq6_step`.
-/
section

open LO LO.FirstOrder LO.FirstOrder.Arithmetic

variable {V : Type*} [ORingStructure V] [V ⊧ₘ* 𝗜𝚺₁]

/-- Blueprint for the Goodstein run: `zero ↦ m₀`, `succ : (k, v) ↦ ibump (k+2) v - 1`. -/
def goodstein.blueprint : PR.Blueprint 1 where
  zero := .mkSigma “y x. y = x”
  succ := .mkSigma “y ih n x. ∃ w, !ibumpDef w (n + 2) ih ∧ !subDef y w 1”

noncomputable def goodstein.construction : PR.Construction V goodstein.blueprint where
  zero := fun x ↦ x 0
  succ := fun _ n ih ↦ ibump (n + 2) ih - 1
  zero_defined := .mk fun v ↦ by simp [goodstein.blueprint]
  succ_defined := .mk fun v ↦ by
    simp [goodstein.blueprint, ibump_defined.iff, sub_defined.iff]

/-- **Internal Goodstein sequence** `igoodstein m₀ k = mₖ` in `V` (over the audited base `k+2`). -/
noncomputable def igoodstein (m₀ k : V) : V := goodstein.construction.result ![m₀] k

@[simp] lemma igoodstein_zero (m₀ : V) : igoodstein m₀ 0 = m₀ := by
  simp [igoodstein, goodstein.construction]

@[simp] lemma igoodstein_succ (m₀ k : V) :
    igoodstein m₀ (k + 1) = ibump (k + 2) (igoodstein m₀ k) - 1 := by
  simp [igoodstein, goodstein.construction]

section

def _root_.LO.FirstOrder.Arithmetic.igoodsteinDef : 𝚺₁.Semisentence 3 :=
  goodstein.blueprint.resultDef.rew (Rew.subst ![#0, #2, #1])

instance igoodstein_defined : 𝚺₁-Function₂ (igoodstein : V → V → V) via igoodsteinDef := .mk
  fun v ↦ by simp [goodstein.construction.result_defined_iff, igoodsteinDef]; rfl

instance igoodstein_definable : 𝚺₁-Function₂ (igoodstein : V → V → V) := igoodstein_defined.to_definable

instance igoodstein_definable' (Γ) : Γ-[m + 1]-Function₂ (igoodstein : V → V → V) :=
  igoodstein_definable.of_sigmaOne

end

end

/-! ## InternalBridge -/
/-
# `InternalBridge.lean` — E-core(b) brick 6: the standard-model bridge (faithfulness)

The internal `ipow`/`ilog`/`ibump`/`igoodstein` were built inside an arbitrary `V ⊧ₘ* 𝗜𝚺₁`. For the
expedition's **anti-fraud** guarantee they must agree with the *audited* `Defs.bump`/`Defs.goodsteinSeq`
on the standard model `ℕ` (itself a model of `𝗜𝚺₁`). This file establishes that absoluteness:

* `ipow b n = b ^ n`              (over `ℕ`)
* `ilog b n = Nat.log b n`        (over `ℕ`)
* `ibump b n = Defs.bump b n`     (over `ℕ`, base `2 ≤ b` — the only case Goodstein uses)
* `igoodstein m k = goodsteinSeq m k`

so the `𝚺₁`-definable internal run is the genuine Goodstein process, not a look-alike.
-/
section

open LO LO.FirstOrder LO.FirstOrder.Arithmetic

/-- Over `ℕ`, the internal power is `Nat.pow`. -/
@[simp] lemma ipow_nat (b n : ℕ) : ipow b n = b ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [ipow_succ, ih, pow_succ]

/-- Over `ℕ`, the internal logarithm is `Nat.log`. (Foundation's scoped `≤` on `ℕ` is `=∨<`, so we
convert it to `Nat.le` via `LO.FirstOrder.Arithmetic.le_def`; the `<` underneath is already `Nat.lt`.) -/
@[simp] lemma ilog_nat (b n : ℕ) : ilog b n = Nat.log b n := by
  symm
  rw [ilog_graph]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨hb, hn⟩ := h
    rw [LO.FirstOrder.Arithmetic.le_def] at hb
    rw [ipow_nat, ipow_nat, LO.FirstOrder.Arithmetic.le_def]
    exact ⟨Nat.eq_or_lt_of_le (Nat.pow_log_le_self b hn.ne'),
      Nat.lt_pow_succ_log_self (by omega) n⟩
  · rcases not_and_or.mp h with h1 | h1
    · rw [LO.FirstOrder.Arithmetic.le_def] at h1
      push Not at h1
      exact Nat.log_of_left_le_one (by omega) n
    · have : n = 0 := by omega
      subst this; simp

/-! ### Foundation `/`,`%` over `ℕ` agree with `Nat.div`/`Nat.mod`

Over `V = ℕ` the scoped Foundation `Div`/`Mod` instances are `Classical.choose!`-built and so are NOT
defeq to `Nat.instDiv`/`Nat.instMod`; the `ibump` peel recursion (`ibump_succ`) exposes the raw
Foundation `/`,`%`. These two bridges convert them to `Nat.div`/`Nat.mod` (`*`,`+`,`-` over `ℕ` ARE
already defeq, so only `/`,`%` need bridging), feeding the standard-model `ibump_nat`. -/

/-- Foundation division over `ℕ` is `Nat.div`. (Stated via `div_eq_of`, whose conclusion carries the
Foundation `Div` instance; the RHS `x / d` is `Nat`'s.) -/
lemma fdiv_nat (x d : ℕ) (hd : 0 < d) :
    @HDiv.hDiv ℕ ℕ ℕ (@instHDiv ℕ (@LO.FirstOrder.Arithmetic.instDiv_foundation ℕ _ _)) x d
      = x / d := by
  have hdm := Nat.div_add_mod x d
  have hml : x % d < d := Nat.mod_lt x hd
  refine div_eq_of (b := d) (c := x / d) ?_ ?_
  · rw [LO.FirstOrder.Arithmetic.le_def]
    rcases (show d * (x / d) ≤ x from by omega).lt_or_eq with h | h
    · exact Or.inr h
    · exact Or.inl h
  · show x < d * (x / d + 1)
    rw [Nat.mul_succ]; omega

/-- Foundation truncated subtraction over `ℕ` is `Nat.sub`. -/
lemma fsub_nat (x y : ℕ) :
    @HSub.hSub ℕ ℕ ℕ (@instHSub ℕ (@LO.FirstOrder.Arithmetic.instSub_foundation ℕ _ _)) x y
      = x - y := by
  by_cases h : y ≤ x
  · have hle : @LE.le ℕ (@LO.FirstOrder.Arithmetic.instLE_foundation ℕ _) y x :=
      LO.FirstOrder.Arithmetic.le_def.mpr (Or.symm h.lt_or_eq)
    have hf := LO.FirstOrder.Arithmetic.sub_spec_of_ge hle
    omega
  · have h' : x ≤ y := le_of_lt (Nat.lt_of_not_le h)
    have hle : @LE.le ℕ (@LO.FirstOrder.Arithmetic.instLE_foundation ℕ _) x y :=
      LO.FirstOrder.Arithmetic.le_def.mpr (Or.symm h'.lt_or_eq)
    rw [LO.FirstOrder.Arithmetic.sub_spec_of_le hle]
    omega

/-- Foundation remainder over `ℕ` is `Nat.mod`. -/
lemma fmod_nat (x d : ℕ) (hd : 0 < d) :
    @HMod.hMod ℕ ℕ ℕ (@instHMod ℕ (@LO.FirstOrder.Arithmetic.instMod_foundation ℕ _ _)) x d
      = x % d := by
  have hdm := Nat.div_add_mod x d
  rw [LO.FirstOrder.Arithmetic.mod_def, fdiv_nat x d hd, fsub_nat]
  omega

/-! ### The internal `bump`/`goodsteinSeq` are the audited ones over `ℕ` -/

/-- Over `ℕ` (base `2 ≤ b`), the internal hereditary base-change is `Defs.bump`. -/
theorem ibump_nat (b : ℕ) (hb : 2 ≤ b) (n : ℕ) : ibump b n = Goodstein.bump b n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
      show ibump b (m + 1) = Goodstein.bump b (m + 1)
      have hbF : @LE.le ℕ (@LO.FirstOrder.Arithmetic.instLE_foundation ℕ _) 2 b :=
        LO.FirstOrder.Arithmetic.le_def.mpr (Or.symm hb.lt_or_eq)
      have hb0 : 0 < b := by omega
      set e := Nat.log b (m + 1) with he
      have hpe : 0 < b ^ e := Nat.pow_pos hb0
      have hen : e < m + 1 := Nat.log_lt_self b (Nat.succ_ne_zero m)
      have hrn : (m + 1) % b ^ e < m + 1 :=
        lt_of_lt_of_le (Nat.mod_lt (m + 1) hpe) (Nat.pow_log_le_self b (Nat.succ_ne_zero m))
      rw [ibump_succ hbF m]
      simp only [ipow_nat, ilog_nat, ← he]
      rw [fdiv_nat (m + 1) (b ^ e) hpe, fmod_nat (m + 1) (b ^ e) hpe,
        ih e hen, ih ((m + 1) % b ^ e) hrn,
        Goodstein.Dom.bump_pos b (m + 1) (Nat.succ_ne_zero m), ← he]

/-- Over `ℕ`, the internal Goodstein run is `Defs.goodsteinSeq`. -/
theorem igoodstein_nat (m₀ : ℕ) (k : ℕ) : igoodstein m₀ k = Goodstein.goodsteinSeq m₀ k := by
  induction k with
  | zero => simp only [igoodstein_zero]; rfl
  | succ k ih =>
    -- `igoodstein_succ` produces `ibump (k+2) _` with the generic `AtLeastTwo` numeral and Foundation
    -- truncated subtraction; `fsub_nat` Natifies the `- 1` and `show` re-casts `k+2` to `Nat`'s literal
    -- so `ibump_nat` matches syntactically.
    rw [igoodstein_succ, ih, fsub_nat]
    show ibump (k + 2) (Goodstein.goodsteinSeq m₀ k) - 1 = Goodstein.goodsteinSeq m₀ (k + 1)
    rw [ibump_nat (k + 2) (by omega)]
    rfl

end

end GoodsteinPA.InternalPow
