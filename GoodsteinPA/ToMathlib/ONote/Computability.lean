/-
# Computability of `ONote` comparison

Mathlib's `Mathlib/SetTheory/Ordinal/Notation.lean` proves that `ONote.cmp` computes the linear
order on Cantor normal forms (`NONote.cmp_compares`), but supplies no `Primcodable`/`Computable`
packaging of that fact. This file builds one, structurally, and uses it to show that the order
pulled back to `ℕ` along the structural coding `ONote.natCode` (from `GoodsteinPA.ToMathlib.Ordinal.Epsilon0`)
is not just well-founded but recursively enumerable — in fact computable:

  `rePred_ltPull_natCode : REPred fun v : List.Vector ℕ 2 ↦ natCode (v.get 0) < natCode (v.get 1)`.

The route is a structural strong recursion on the pairing codes used by `ONote.encodeONote`:

* `Cnat` computes `ordCode ∘ ONote.cmp` on decoded pairs via `Computable.nat_strong_rec`, using
  `cmpStep`/`cmpStep_spec` to unfold one `oadd` layer at a time (`computable_Cnat`).
* `Nfb` computes the `ONote.NF` predicate the same way, via `nfStep`/`nfStep_spec`
  (`computable_Nfb`), which is needed because `NONote` (the `enc`/`countNF`/`nthNF` maps below)
  enumerates only the normal-form codes.
* `enc` (equivalently `nthNF`, found by unbounded search) enumerates the normal-form codes in
  increasing order (`computable_enc`), matching the actual `NONote` numbering induced by
  `ONote.natCode`.

Carries one `native_decide` (in `cmpStep_spec`'s base case: a finite, decidable computation on the
zero-length pairing case). -/
module

public import Mathlib.Computability.RE
public import Mathlib.Tactic.Cases
public import Mathlib.Tactic.Linarith
public import GoodsteinPA.ToMathlib.Ordinal.Epsilon0
public meta import GoodsteinPA.ToMathlib.Ordinal.Epsilon0 -- shake: keep

@[expose] public section

namespace ONote

/-! ### Structural `Primcodable ONote` and computability of `ONote.cmp`

`encodeONote`/`decodeONote`/`natCode` and the `Encodable ONote`/`Denumerable NONote` instances come
from `GoodsteinPA.ToMathlib.Ordinal.Epsilon0`. -/

/-- `encodeONote` and `decodeONote` are mutually inverse: `encode` is a bijection `ONote ≃ ℕ`. -/
lemma encodeONote_decodeONote (n : ℕ) : encodeONote (decodeONote n) = n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
  rcases n with (_ | m);
  · simp [decodeONote, encodeONote];
  · unfold decodeONote;
    simp +arith +decide [encodeONote, ih _ (Nat.lt_succ_of_le (Nat.unpair_left_le _)),
      ih _ (Nat.lt_succ_of_le (Nat.unpair_right_le _ |> le_trans <| Nat.unpair_right_le _))]

/-- The structural `Encodable ONote` decodes via `decodeONote` (never failing). -/
lemma decode_eq (n : ℕ) : (Encodable.decode n : Option ONote) = some (decodeONote n) := by
  rfl

/-- The structural `Encodable ONote` encodes via `encodeONote`. -/
lemma encode_eq (x : ONote) : Encodable.encode x = encodeONote x := by
  rfl

lemma encode_decode_eq (n : ℕ) :
    Encodable.encode (Encodable.decode n : Option ONote) = n + 1 := by
  rw [decode_eq];
  simp +decide [Encodable.encode, encodeONote_decodeONote]

/-- `encode ∘ decode` is `Nat.succ` up to the `+ 1` shift, so it is primitive recursive. -/
lemma primrec_encode_decode :
    Nat.Primrec (fun n => Encodable.encode (Encodable.decode n : Option ONote)) := by
  convert Nat.Primrec.succ using 1;
  exact funext fun n => by simpa using encode_decode_eq n;

/-- **Structural `Primcodable ONote`.** Built from the structural `Encodable ONote` above. -/
instance instPrimcodableONote : Primcodable ONote :=
  { (inferInstance : Encodable ONote) with
    prim := primrec_encode_decode }

lemma computable_decodeONote : Computable decodeONote := by
  have h_decodeONote_computable : Computable (fun n => (Encodable.decode n : Option ONote)) :=
    Computable.decode (α := ONote)
  exact Computable.option_getD h_decodeONote_computable (Computable.const ONote.zero)

/-! ### Ordering encoded as `ℕ` (lt = 0, eq = 1, gt = 2) -/

/-- Encode an `Ordering` as a natural number. -/
def ordCode : Ordering → ℕ
  | Ordering.lt => 0
  | Ordering.eq => 1
  | Ordering.gt => 2

/-- `ℕ`-level version of `Ordering.then`. -/
def thenNat (a b : ℕ) : ℕ := if a = 1 then b else a

/-- `ℕ`-level version of `_root_.cmp` on `ℕ`, returning an `ordCode`. -/
def cmpNat (a b : ℕ) : ℕ := if a < b then 0 else if a = b then 1 else 2

lemma ordCode_then (o p : Ordering) : ordCode (o.then p) = thenNat (ordCode o) (ordCode p) := by
  cases o <;> cases p <;> rfl

lemma ordCode_cmp (a b : ℕ) : ordCode (_root_.cmp a b) = cmpNat a b := by
  unfold _root_.cmp cmpUsing ordCode cmpNat
  split_ifs <;> simp_all
  omega

/-- Index (paired code) of the `e`-subterms, given the paired code `m = pair cx cy`. -/
def cmpIdxE (m : ℕ) : ℕ :=
  Nat.pair (Nat.unpair ((Nat.unpair m).1 - 1)).1 (Nat.unpair ((Nat.unpair m).2 - 1)).1

/-- Index (paired code) of the `a`-subterms, given the paired code `m = pair cx cy`. -/
def cmpIdxA (m : ℕ) : ℕ :=
  Nat.pair (Nat.unpair (Nat.unpair ((Nat.unpair m).1 - 1)).2).2
           (Nat.unpair (Nat.unpair ((Nat.unpair m).2 - 1)).2).2

/-- The `ordCode` of the comparison of the leading coefficients, given `m = pair cx cy`.
(`computable_cmpStep` inlines its primitive recursiveness; no standalone `Primrec cmpNV` lemma.) -/
def cmpNV (m : ℕ) : ℕ :=
  cmpNat ((Nat.unpair (Nat.unpair ((Nat.unpair m).1 - 1)).2).1 + 1)
         ((Nat.unpair (Nat.unpair ((Nat.unpair m).2 - 1)).2).1 + 1)

lemma primrec_cmpIdxE : Primrec cmpIdxE := by
  have h_fst : Primrec (fun x : ℕ => (Nat.unpair x).1) := Primrec.fst.comp Primrec.unpair
  have h_snd : Primrec (fun x : ℕ => (Nat.unpair x).2) := Primrec.snd.comp Primrec.unpair
  have h_sub : Primrec (fun x : ℕ => x - 1) := Primrec.nat_sub.comp Primrec.id (Primrec.const 1)
  exact Primrec₂.natPair.comp (h_fst.comp (h_sub.comp h_fst)) (h_fst.comp (h_sub.comp h_snd))

lemma primrec_cmpIdxA : Primrec cmpIdxA := by
  have h_fst : Primrec (fun x : ℕ => (Nat.unpair x).1) := Primrec.fst.comp Primrec.unpair
  have h_snd : Primrec (fun x : ℕ => (Nat.unpair x).2) := Primrec.snd.comp Primrec.unpair
  have h_sub : Primrec (fun x : ℕ => x - 1) := Primrec.nat_sub.comp Primrec.id (Primrec.const 1)
  exact Primrec₂.natPair.comp
    (h_snd.comp (h_snd.comp (h_sub.comp h_fst)))
    (h_snd.comp (h_snd.comp (h_sub.comp h_snd)))

lemma primrec_thenNat : Primrec₂ thenNat := by
  unfold thenNat
  exact Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 1)) Primrec.snd Primrec.fst

lemma primrec_cmpNat : Primrec₂ cmpNat := by
  unfold cmpNat
  exact Primrec.ite (Primrec.nat_lt.comp Primrec.fst Primrec.snd) (Primrec.const 0)
    (Primrec.ite (Primrec.eq.comp Primrec.fst Primrec.snd) (Primrec.const 1) (Primrec.const 2))

lemma primrec_cmpNV : Primrec cmpNV := by
  have hfst : Primrec (fun m : ℕ => (Nat.unpair m).1) := Primrec.fst.comp Primrec.unpair
  have hsnd : Primrec (fun m : ℕ => (Nat.unpair m).2) := Primrec.snd.comp Primrec.unpair
  have hsub : Primrec (fun x : ℕ => x - 1) := Primrec.nat_sub.comp Primrec.id (Primrec.const 1)
  -- inner_lhs m = (unpair (unpair ((unpair m).1 - 1)).2).1
  have hlhs : Primrec (fun m : ℕ =>
      (Nat.unpair (Nat.unpair ((Nat.unpair m).1 - 1)).2).1 + 1) :=
    Primrec.succ.comp (hfst.comp (hsnd.comp (hsub.comp hfst)))
  have hrhs : Primrec (fun m : ℕ =>
      (Nat.unpair (Nat.unpair ((Nat.unpair m).2 - 1)).2).1 + 1) :=
    Primrec.succ.comp (hfst.comp (hsnd.comp (hsub.comp hsnd)))
  exact primrec_cmpNat.comp hlhs hrhs

/-- The step function for the strong recursion computing `ordCode ∘ cmp` on paired codes. -/
def cmpStep (L : List ℕ) : Option ℕ :=
  let m := L.length
  if (Nat.unpair m).1 = 0 then (if (Nat.unpair m).2 = 0 then some 1 else some 0)
  else if (Nat.unpair m).2 = 0 then some 2
  else
    (L[cmpIdxE m]?).bind fun re =>
      (L[cmpIdxA m]?).map fun ra =>
        thenNat re (thenNat (cmpNV m) ra)

/-- The function computed by the strong recursion: `ordCode` of the comparison of the two
notations whose codes are the components of `m`. -/
def Cnat (m : ℕ) : ℕ :=
  ordCode (ONote.cmp (decodeONote (Nat.unpair m).1) (decodeONote (Nat.unpair m).2))

lemma Cnat_pair (cx cy : ℕ) :
    Cnat (Nat.pair cx cy) = ordCode (ONote.cmp (decodeONote cx) (decodeONote cy)) := by
  simp [Cnat, Nat.unpair_pair]

lemma pair_lt_pair {a₁ a₂ b₁ b₂ : ℕ} (ha : a₁ < a₂) (hb : b₁ < b₂) :
    Nat.pair a₁ b₁ < Nat.pair a₂ b₂ :=
  lt_trans (Nat.pair_lt_pair_left b₁ ha) (Nat.pair_lt_pair_right a₂ hb)

lemma computable_cmpStep : Computable cmpStep := by
  apply Primrec.to_comp
  have c1 : PrimrecPred (fun L : List ℕ => (Nat.unpair L.length).1 = 0) :=
    Primrec.eq.comp (Primrec.fst.comp (Primrec.unpair.comp Primrec.list_length)) (Primrec.const 0)
  have c2 : PrimrecPred (fun L : List ℕ => (Nat.unpair L.length).2 = 0) :=
    Primrec.eq.comp (Primrec.snd.comp (Primrec.unpair.comp Primrec.list_length)) (Primrec.const 0)
  have f1 : Primrec (fun L : List ℕ => L[cmpIdxE L.length]?) :=
    Primrec.list_getElem?.comp Primrec.id (primrec_cmpIdxE.comp Primrec.list_length)
  have g2 : Primrec₂ (fun (p : List ℕ × ℕ) (ra : ℕ) =>
      thenNat p.2 (thenNat (cmpNV p.1.length) ra)) :=
    primrec_thenNat.comp (Primrec.snd.comp Primrec.fst)
      (primrec_thenNat.comp
        (primrec_cmpNV.comp (Primrec.list_length.comp (Primrec.fst.comp Primrec.fst)))
        Primrec.snd)
  have f2 : Primrec (fun p : List ℕ × ℕ => p.1[cmpIdxA p.1.length]?) :=
    Primrec.list_getElem?.comp Primrec.fst
      (primrec_cmpIdxA.comp (Primrec.list_length.comp Primrec.fst))
  have g1 : Primrec₂ (fun (L : List ℕ) (re : ℕ) =>
      (L[cmpIdxA L.length]?).map fun ra => thenNat re (thenNat (cmpNV L.length) ra)) :=
    Primrec.option_map f2 g2
  have helse : Primrec (fun L : List ℕ =>
      (L[cmpIdxE L.length]?).bind fun re =>
        (L[cmpIdxA L.length]?).map fun ra => thenNat re (thenNat (cmpNV L.length) ra)) :=
    Primrec.option_bind f1 g1
  exact Primrec.ite c1
    (Primrec.ite c2 (Primrec.const (some 1)) (Primrec.const (some 0)))
    (Primrec.ite c2 (Primrec.const (some 2)) helse)

lemma cmpStep_spec (m : ℕ) : cmpStep ((List.range m).map Cnat) = some (Cnat m) := by
  unfold cmpStep;
  simp +decide [cmpIdxE, cmpIdxA, cmpNV];
  rcases n : Nat.unpair m with ⟨x, y⟩; rcases x with (_ | x) <;> rcases y with (_ | y) <;> simp +decide;
  · rw [show m = 0 by rw [← Nat.pair_unpair m, n]; rfl]; simp +decide [Cnat];
    native_decide;
  · unfold Cnat; simp +decide [n];
    unfold decodeONote; simp +decide [ONote.cmp];
  · unfold Cnat; simp +decide [n];
    unfold decodeONote; simp +decide [ONote.cmp];
  · rw [List.getElem?_range, List.getElem?_range] <;> norm_num [n];
    · unfold Cnat;
      rw [n];
      rw [decodeONote, decodeONote];
      simp +decide [ONote.cmp, ordCode_then, ordCode_cmp];
      unfold cmpNat; aesop;
    · rw [← Nat.pair_unpair m, n]
      have e1 := Nat.unpair_left_le x
      have e2 := Nat.unpair_right_le x
      have e3 := Nat.unpair_left_le y
      have e4 := Nat.unpair_right_le y
      have e5 := Nat.unpair_right_le (Nat.unpair x).2
      have e6 := Nat.unpair_right_le (Nat.unpair y).2
      exact pair_lt_pair (by omega) (by omega)
    · rw [← Nat.pair_unpair m, n];
      exact pair_lt_pair (Nat.unpair_left_le _ |> Nat.lt_succ_of_le) (Nat.unpair_left_le _ |> Nat.lt_succ_of_le)

theorem computable_Cnat : Computable Cnat := by
  have h_step_spec : ∀ n, cmpStep ((List.range n).map Cnat) = some (Cnat n) := cmpStep_spec
  exact (Computable.nat_strong_rec (fun (_ : Unit) n => Cnat n)
    (computable_cmpStep.comp Computable.snd |> Computable.to₂)
    (fun _ n => h_step_spec n)).comp (Computable.const ()) Computable.id

/-! ### Computability of the `NF` predicate (needed to enumerate `NONote`) -/

/-- The `ordCode` is `0` exactly for `Ordering.lt`. -/
lemma ordCode_eq_zero {o : Ordering} : ordCode o = 0 ↔ o = Ordering.lt := by
  cases o <;> simp [ordCode]

/-- `Cnat (pair cx cy) = 0` iff `cmp (decode cx) (decode cy) = lt`. -/
lemma Cnat_pair_eq_zero (cx cy : ℕ) :
    Cnat (Nat.pair cx cy) = 0 ↔ ONote.cmp (decodeONote cx) (decodeONote cy) = Ordering.lt := by
  rw [Cnat_pair, ordCode_eq_zero]

/-- The `ℕ`-level normal-form predicate (intended: `Nfb (encodeONote x) = decide x.NF`). -/
def Nfb (n : ℕ) : Bool := decide (decodeONote n).NF

/-- Index of the leading exponent code, given a notation code `c`. -/
def nfIdxE (c : ℕ) : ℕ := (Nat.unpair (c - 1)).1

/-- Index of the tail code, given a notation code `c`. -/
def nfIdxA (c : ℕ) : ℕ := (Nat.unpair (Nat.unpair (c - 1)).2).2

/-- The `TopBelow` check at code `c`. -/
def nfTB (c : ℕ) : Bool :=
  if nfIdxA c = 0 then true
  else decide (Cnat (Nat.pair (Nat.unpair (nfIdxA c - 1)).1 (nfIdxE c)) = 0)

lemma primrec_nfIdxE : Primrec nfIdxE :=
  Primrec.fst.comp (Primrec.unpair.comp (Primrec.nat_sub.comp Primrec.id (Primrec.const 1)))

lemma primrec_nfIdxA : Primrec nfIdxA :=
  Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp
    (Primrec.unpair.comp (Primrec.nat_sub.comp Primrec.id (Primrec.const 1)))))

lemma computable_nfTB : Computable nfTB := by
  have hidx : Primrec (fun c : ℕ => Nat.pair (Nat.unpair (nfIdxA c - 1)).1 (nfIdxE c)) :=
    Primrec₂.natPair.comp
      (Primrec.fst.comp (Primrec.unpair.comp
        (Primrec.nat_sub.comp primrec_nfIdxA (Primrec.const 1))))
      primrec_nfIdxE
  have hCnat : Computable
      (fun c : ℕ => Cnat (Nat.pair (Nat.unpair (nfIdxA c - 1)).1 (nfIdxE c))) :=
    computable_Cnat.comp hidx.to_comp
  have hA : Computable (fun c : ℕ => decide (nfIdxA c = 0)) :=
    (Primrec.eq.comp primrec_nfIdxA (Primrec.const 0)).decide.to_comp
  have hB : Computable (fun c : ℕ =>
      decide (Cnat (Nat.pair (Nat.unpair (nfIdxA c - 1)).1 (nfIdxE c)) = 0)) :=
    ((Primrec.eq.comp Primrec.id (Primrec.const 0)).decide.to_comp).comp hCnat
  refine (Computable.cond hA (Computable.const true) hB).of_eq (fun c => ?_)
  by_cases h : nfIdxA c = 0 <;> simp [nfTB, h]

/-- Step function for the strong recursion computing `Nfb`. -/
def nfStep (L : List Bool) : Option Bool :=
  let c := L.length
  if c = 0 then some true
  else
    (L[nfIdxE c]?).bind fun be =>
      (L[nfIdxA c]?).map fun ba =>
        be && ba && nfTB c

lemma computable_nfStep : Computable nfStep := by
  have c0 : Computable (fun L : List Bool => decide (L.length = 0)) :=
    (Primrec.eq.comp Primrec.list_length (Primrec.const 0)).decide.to_comp
  have f1 : Computable (fun L : List Bool => L[nfIdxE L.length]?) :=
    (Primrec.list_getElem?.comp Primrec.id (primrec_nfIdxE.comp Primrec.list_length)).to_comp
  have f2 : Computable (fun p : List Bool × Bool => p.1[nfIdxA p.1.length]?) :=
    (Primrec.list_getElem?.comp Primrec.fst
      (primrec_nfIdxA.comp (Primrec.list_length.comp Primrec.fst))).to_comp
  have g2 : Computable₂ (fun (p : List Bool × Bool) (ba : Bool) => p.2 && ba && nfTB p.1.length) := by
    have h1 : Computable (fun q : (List Bool × Bool) × Bool => q.1.2 && q.2) :=
      Computable₂.comp Primrec.and.to_comp (Computable.snd.comp Computable.fst) Computable.snd
    have h2 : Computable (fun q : (List Bool × Bool) × Bool => nfTB q.1.1.length) :=
      computable_nfTB.comp (Primrec.list_length.comp (Primrec.fst.comp Primrec.fst)).to_comp
    exact Computable₂.comp Primrec.and.to_comp h1 h2
  have g1 : Computable₂ (fun (L : List Bool) (be : Bool) =>
      (L[nfIdxA L.length]?).map fun ba => be && ba && nfTB L.length) :=
    Computable.option_map f2 g2
  have helse : Computable (fun L : List Bool =>
      (L[nfIdxE L.length]?).bind fun be =>
        (L[nfIdxA L.length]?).map fun ba => be && ba && nfTB L.length) :=
    Computable.option_bind f1 g1
  refine (Computable.cond c0 (Computable.const (some true)) helse).of_eq (fun L => ?_)
  unfold nfStep
  by_cases h : L.length = 0 <;> simp [h]

/-- Characterization of `NF` on `oadd` (from mathlib's `decidableNF` argument). -/
lemma NF_oadd_iff {e : ONote} {n : ℕ+} {a : ONote} :
    (ONote.oadd e n a).NF ↔ ONote.NF e ∧ ONote.NF a ∧ ONote.TopBelow e a := by
  by_cases h : e.NF
  · haveI := h
    rw [show (ONote.oadd e n a).NF ↔ ONote.NFBelow a (ONote.repr e) from
      ⟨fun h' => h'.snd', fun h' => ONote.NF.oadd h n h'⟩, ONote.nfBelow_iff_topBelow]
    tauto
  · exact ⟨fun h' => absurd h'.fst h, fun h' => absurd h'.1 h⟩

lemma nfStep_spec (n : ℕ) : nfStep ((List.range n).map Nfb) = some (Nfb n) := by
  unfold nfStep Nfb;
  by_cases hn : n = 0;
  · rw [hn]; simp +decide [decodeONote];
  · rw [show decodeONote n = ONote.oadd (decodeONote (Nat.unpair (n - 1) |>.1))
      ⟨(Nat.unpair (Nat.unpair (n - 1) |>.2) |>.1) + 1, Nat.succ_pos _⟩
      (decodeONote (Nat.unpair (Nat.unpair (n - 1) |>.2) |>.2)) from ?_];
    · have h_nfTB : nfTB n = decide (ONote.TopBelow (decodeONote (nfIdxE n)) (decodeONote (nfIdxA n))) := by
        unfold nfTB ONote.TopBelow;
        rcases k : nfIdxA n with (_ | k) <;> simp_all +decide [Cnat_pair_eq_zero];
        · unfold decodeONote; simp +decide;
        · rw [decodeONote];
      simp_all +decide [NF_oadd_iff];
      rw [List.getElem?_range, List.getElem?_range];
      · simp +decide [nfIdxE, nfIdxA];
        grind;
      · exact lt_of_le_of_lt (Nat.unpair_right_le _) (lt_of_le_of_lt (Nat.unpair_right_le _) (Nat.pred_lt hn));
      · exact Nat.lt_of_le_of_lt (Nat.unpair_left_le _) (Nat.pred_lt hn);
    · cases n <;> simp_all +decide [decodeONote]

theorem computable_Nfb : Computable Nfb :=
  (Computable.nat_strong_rec (fun (_ : Unit) n => Nfb n)
    (computable_nfStep.comp Computable.snd |> Computable.to₂)
    (fun _ n => nfStep_spec n)).comp (Computable.const ()) Computable.id

/-! ### Enumeration of normal-form codes -/

/-- The structural NF-code of the `a`-th notation `natCode a`. -/
def enc (a : ℕ) : ℕ := encodeONote (natCode a).1

lemma decodeONote_enc (a : ℕ) : decodeONote (enc a) = (natCode a).1 := by
  rw [enc, decodeONote_encodeONote]

lemma nf_decode_enc (a : ℕ) : (decodeONote (enc a)).NF := by
  rw [decodeONote_enc]; exact (natCode a).2

lemma enc_injective : Function.Injective enc := by
  intro a b hab;
  apply_fun decodeONote at hab;
  have h_eq : (natCode a).1 = (natCode b).1 := by
    grind +suggestions;
  exact natCode.injective (Subtype.ext h_eq)

lemma enc_surjOn {n : ℕ} (h : (decodeONote n).NF) : ∃ a, enc a = n := by
  obtain ⟨a, ha⟩ := natCode.surjective ⟨decodeONote n, h⟩
  use a
  unfold enc
  simp [ha, encodeONote_decodeONote]

lemma enc_strictMono : StrictMono enc := by
  -- `enc a` is the underlying ℕ-value of the `a`-th element of `range encode`, enumerated by
  -- `Nat.Subtype.ofNat` in increasing order; hence strictly monotone.
  letI hdec : DecidablePred (· ∈ Set.range (Encodable.encode : NONote → ℕ)) :=
    Encodable.decidableRangeEncode NONote
  letI hinf : Infinite (Set.range (Encodable.encode : NONote → ℕ)) :=
    Infinite.of_injective _ (Equiv.ofInjective _ Encodable.encode_injective).injective
  have key : ∀ a, enc a =
      ((Nat.Subtype.ofNat (Set.range (Encodable.encode : NONote → ℕ)) a :
          Set.range (Encodable.encode : NONote → ℕ)) : ℕ) := by
    intro a
    have h2 : (natCode a) = (Encodable.equivRangeEncode NONote).symm
        (Nat.Subtype.ofNat (Set.range (Encodable.encode : NONote → ℕ)) a) := by
      show Denumerable.ofNat NONote a = _
      simp only [Denumerable.ofEquiv_ofNat, Denumerable.ofNat_nat, Equiv.coe_fn_symm_mk]
    unfold enc
    rw [h2]
    exact congrArg Subtype.val
      (Equiv.apply_symm_apply (Encodable.equivRangeEncode NONote)
        (Nat.Subtype.ofNat (Set.range (Encodable.encode : NONote → ℕ)) a))
  rw [show enc = fun a => ((Nat.Subtype.ofNat (Set.range (Encodable.encode : NONote → ℕ)) a :
        Set.range (Encodable.encode : NONote → ℕ)) : ℕ) from funext key]
  apply strictMono_nat_of_lt_succ
  intro n
  exact Subtype.coe_lt_coe.mpr (Nat.Subtype.lt_succ_self _)

/-- Number of NF-codes strictly below `n`. -/
def countNF (n : ℕ) : ℕ := ((List.range n).filter (fun k => Nfb k)).length

lemma computable_countNF : Computable countNF := by
  have h_countNF_eq : countNF = fun n => Nat.recOn n 0 (fun n count => count + if Nfb n then 1 else 0) := by
    funext n; induction' n with n ih <;> simp_all +decide [countNF];
    rw [List.range_succ, List.filter_append]; aesop;
  rw [h_countNF_eq];
  convert Computable.nat_rec _ _ _ using 1;
  rotate_left;
  exact fun n => n;
  exact fun n => 0;
  exact fun n p => p.2 + if Nfb p.1 then 1 else 0;
  · exact Computable.id;
  · exact Computable.const 0;
  · have h_countNF_eq : Computable (fun (p : ℕ × ℕ) => p.2 + (if Nfb p.1 then 1 else 0)) := by
      have h_cond : Computable (fun (p : ℕ × ℕ) => if Nfb p.1 then 1 else 0) := by
        have h_cond : Computable (fun (p : ℕ) => if Nfb p then 1 else 0) := by
          convert Computable.cond computable_Nfb (Computable.const 1) (Computable.const 0) using 1;
          grind;
        exact h_cond.comp Computable.fst
      have h_add : Computable (fun (p : ℕ × ℕ) => p.1 + p.2) := by
        exact Primrec.to_comp (Primrec.nat_add.comp Primrec.fst Primrec.snd);
      convert h_add.comp (Computable.snd.pair h_cond) using 1;
    exact h_countNF_eq.comp Computable.snd;
  · rfl

lemma Nfb_enc (a : ℕ) : Nfb (enc a) = true := by
  simp [Nfb, nf_decode_enc]

lemma countNF_eq (n : ℕ) :
    countNF n = ((Finset.range n).filter (fun k => (decodeONote k).NF)).card := by
  congr

lemma countNF_enc (a : ℕ) : countNF (enc a) = a := by
  have h_card : ((Finset.range (enc a)).filter (fun k => (decodeONote k).NF)).card = ((Finset.range a).image enc).card := by
    congr 1 with x; simp +decide [Finset.mem_image, Finset.mem_range];
    constructor;
    · intro hx;
      obtain ⟨b, hb⟩ := enc_surjOn hx.2;
      exact ⟨b, by simpa [hb] using enc_strictMono.lt_iff_lt.mp (by aesop), hb⟩;
    · rintro ⟨b, hb, rfl⟩; exact ⟨enc_strictMono hb, nf_decode_enc _⟩;
  rw [Finset.card_image_of_injective _ enc_injective] at h_card; aesop

lemma countNF_succ (n : ℕ) : countNF (n + 1) = countNF n + (if Nfb n then 1 else 0) := by
  have h_filter : List.filter (fun k => Nfb k) (List.range (n + 1)) = List.filter (fun k => Nfb k) (List.range n) ++ if Nfb n then [n] else [] := by
    simp +decide [List.range_succ];
    grind;
  unfold countNF; aesop;

lemma countNF_mono : Monotone countNF :=
  monotone_nat_of_le_succ (by simp +decide [countNF_succ])

lemma lt_countNF_succ_enc (a : ℕ) : a < countNF (enc a + 1) := by
  rw [countNF_succ];
  rw [countNF_enc, if_pos (Nfb_enc a)]; linarith

lemma exists_count (a : ℕ) : ∃ n, a < countNF (n + 1) := ⟨enc a, lt_countNF_succ_enc a⟩

/-- The `a`-th NF-code, defined by an (always-terminating) search. -/
noncomputable def nthNF (a : ℕ) : ℕ := Nat.find (exists_count a)

lemma enc_eq_nthNF (a : ℕ) : enc a = nthNF a :=
  Eq.symm <| (Nat.find_eq_iff _).2
    ⟨lt_countNF_succ_enc a, fun n hn => not_lt_of_ge <| by
      linarith [countNF_mono <| Nat.succ_le_of_lt hn, countNF_enc a]⟩

lemma rfind_nthNF (a : ℕ) :
    Nat.rfind (fun n => (Part.some (decide (a < countNF (n + 1))) : Part Bool)) =
      Part.some (nthNF a) := by
  convert Part.eq_some_iff.mpr _ using 1;
  simp +zetaDelta at *;
  exact ⟨Nat.find_spec (exists_count a), fun {m} hm => not_lt.1 fun contra => hm.not_ge <| Nat.find_min' _ contra⟩

lemma computable_nthNF : Computable nthNF := by
  have hp : Partrec₂ (fun (a m : ℕ) =>
      (Part.some (decide (a < countNF (m + 1))) : Part Bool)) :=
    (Primrec.nat_lt.decide.to_comp).comp Computable.fst
      (computable_countNF.comp (Computable.succ.comp Computable.snd))
  exact (Partrec.rfind hp).of_eq rfind_nthNF

theorem computable_enc : Computable enc :=
  computable_nthNF.of_eq (fun a => (enc_eq_nthNF a).symm)

/-! ### Assembling the final result -/

lemma cmp_eq_lt_iff_lt (x y : NONote) : x.cmp y = Ordering.lt ↔ x < y := by
  have h_compares : (x.cmp y).Compares x y := NONote.cmp_compares x y
  rcases h : x.cmp y with (_ | _ | _) <;> simp_all +decide [Ordering.Compares];
  exact le_of_lt h_compares

lemma lt_iff_Cnat (a b : ℕ) :
    natCode a < natCode b ↔ Cnat (Nat.pair (enc a) (enc b)) = 0 := by
  rw [Cnat_pair_eq_zero, decodeONote_enc, decodeONote_enc]
  exact (cmp_eq_lt_iff_lt (natCode a) (natCode b)).symm

/-- **Recursive enumerability (in fact computability) of the pulled-back CNF order.** The order
`natCode a < natCode b` on ℕ-codes is `REPred`. -/
theorem rePred_ltPull_natCode :
    REPred fun v : List.Vector ℕ 2 ↦ natCode (v.get 0) < natCode (v.get 1) := by
  apply ComputablePred.to_re
  refine ⟨inferInstance, ?_⟩
  have hidx0 : Computable (fun v : List.Vector ℕ 2 => v.get (0 : Fin 2)) :=
    (Primrec.vector_get.comp Primrec.id (Primrec.const (0 : Fin 2))).to_comp
  have hidx1 : Computable (fun v : List.Vector ℕ 2 => v.get (1 : Fin 2)) :=
    (Primrec.vector_get.comp Primrec.id (Primrec.const (1 : Fin 2))).to_comp
  have hpair : Computable (fun v : List.Vector ℕ 2 =>
      Nat.pair (enc (v.get 0)) (enc (v.get 1))) :=
    Primrec₂.natPair.to_comp.comp (computable_enc.comp hidx0) (computable_enc.comp hidx1)
  have hmain : Computable (fun v : List.Vector ℕ 2 =>
      decide (Cnat (Nat.pair (enc (v.get 0)) (enc (v.get 1))) = 0)) :=
    ((Primrec.eq.comp Primrec.id (Primrec.const 0)).decide.to_comp).comp
      (computable_Cnat.comp hpair)
  exact hmain.of_eq (fun v => decide_eq_decide.mpr (lt_iff_Cnat (v.get 0) (v.get 1)).symm)

end ONote
