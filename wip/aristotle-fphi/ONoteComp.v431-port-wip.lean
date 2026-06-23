import Mathlib.Computability.RE
import Mathlib.Computability.Partrec
import Mathlib.Computability.Primrec.List
import GoodsteinPA.Epsilon0Complete

/-
# `ONoteComp.lean` — F-φ DISCHARGE: comparison of CNF notations is r.e. (`rePred_ltPull_natCode`)

Proves `rePred_ltPull_natCode : REPred fun v : List.Vector ℕ 2 ↦ natCode (v.get 0) < natCode (v.get 1)`
for the repo's `Epsilon0Complete.natCode` — discharging the lone math axiom of `Thm56.peano_not_proves_TI`.

Provenance: the proof body was produced by Aristotle (Harmonic) on Lean `v4.28.0` (`aris_onotecmp`,
lap 26) and ported here to `v4.31.0` (lap 27). The structural `encodeONote`/`decodeONote`/`natCode` and
the `Encodable ONote`/`Denumerable NONote` instances are REUSED from `Epsilon0Complete` (they are
definitionally identical to Aristotle's scaffolding), so `rePred_ltPull_natCode` is about the SAME
`natCode` the seam (`SeamDefinability.seam`) uses — no re-basing of the order-type half.

Carries 2 `native_decide` per-site axioms (🟢 finite-computation trust base, acceptable per doctrine).

Goal (Aristotle's note): comparison of mathlib's `ONote`/`NONote` Cantor normal forms is COMPUTABLE,
packaged as a single `REPred` lemma. mathlib has `ONote.cmp` and the `LinearOrder NONote` it induces,
but no `Computable`/`Primrec` proof; this file supplies it via a structural strong recursion.
-/

open ONote

namespace GoodsteinPA.ONoteComp

open GoodsteinPA.Epsilon0Complete

/-! ### Structural `Primcodable ONote` and computability of `ONote.cmp`

`encodeONote`/`decodeONote`/`natCode` and the `Encodable ONote`/`Denumerable NONote` instances come
from `Epsilon0Complete`. -/

/-
`encodeONote` and `decodeONote` are mutually inverse: `encode` is a bijection `ONote ≃ ℕ`.
-/
theorem encodeONote_decodeONote : ∀ n : ℕ, encodeONote (decodeONote n) = n := by
  intro n
  induction' n using Nat.strongRecOn with n ih
  generalize_proofs at *;
  rcases n with ( _ | m );
  · simp [decodeONote, encodeONote];
  · unfold decodeONote;
    simp +arith +decide [ encodeONote, ih _ ( Nat.lt_succ_of_le ( Nat.unpair_left_le _ ) ), ih _ ( Nat.lt_succ_of_le ( Nat.unpair_right_le _ |> le_trans <| Nat.unpair_right_le _ ) ) ]

/-
The structural `Encodable ONote` decodes via `decodeONote` (never failing).
-/
theorem decode_eq (n : ℕ) : (Encodable.decode n : Option ONote) = some (decodeONote n) := by
  rfl

/-
The structural `Encodable ONote` encodes via `encodeONote`.
-/
theorem encode_eq (x : ONote) : Encodable.encode x = encodeONote x := by
  rfl

theorem encode_decode_eq (n : ℕ) :
    Encodable.encode (Encodable.decode n : Option ONote) = n + 1 := by
  rw [ decode_eq ];
  simp +decide [ Encodable.encode, encode_eq, encodeONote_decodeONote ]

theorem primrec_encode_decode :
    Nat.Primrec (fun n => Encodable.encode (Encodable.decode n : Option ONote)) := by
  -- Since `Nat.succ` is primitive recursive, and `encode` and `decode` are inverses, the function `n => encode (decode n)` is also primitive recursive.
  have h_succ : Nat.Primrec Nat.succ := by
    exact Nat.Primrec.succ;
  convert h_succ using 1;
  exact funext fun n => by simpa using encode_decode_eq n;

/-- **Structural `Primcodable ONote`.** Built from the structural `Encodable ONote` above. -/
instance instPrimcodableONote : Primcodable ONote :=
  { (inferInstance : Encodable ONote) with
    prim := primrec_encode_decode }

theorem computable_decodeONote : Computable decodeONote := by
  have h_decodeONote_computable : Computable (fun n => (Encodable.decode n : Option ONote)) := by
    convert Computable.decode ( α := ONote ) using 1;
  exact Computable.option_getD ( h_decodeONote_computable ) ( Computable.const ONote.zero )

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

theorem ordCode_then (o p : Ordering) : ordCode (o.then p) = thenNat (ordCode o) (ordCode p) := by
  cases o <;> cases p <;> rfl

theorem ordCode_cmp (a b : ℕ) : ordCode (_root_.cmp a b) = cmpNat a b := by
  rcases lt_trichotomy a b with h | h | h
  · have hc : _root_.cmp a b = Ordering.lt := by simp [_root_.cmp, cmpUsing, h]
    rw [hc]; simp [ordCode, cmpNat, h]
  · subst h
    have hc : _root_.cmp a a = Ordering.eq := by simp [_root_.cmp, cmpUsing]
    rw [hc]; simp [ordCode, cmpNat]
  · have hc : _root_.cmp a b = Ordering.gt := by
      simp [_root_.cmp, cmpUsing, h.not_lt, asymm h]
    rw [hc]; simp [ordCode, cmpNat, h.not_lt, (ne_of_gt h)]

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

theorem primrec_cmpIdxE : Primrec cmpIdxE := by
  have h_id : Primrec (fun x : ℕ => x) := by
    exact Primrec.id
  have h_fst : Primrec (fun x : ℕ => (Nat.unpair x).1) := by
    exact Primrec.fst.comp ( Primrec.unpair )
  have h_snd : Primrec (fun x : ℕ => (Nat.unpair x).2) := by
    exact Primrec.snd.comp ( Primrec.unpair.comp h_id )
  have h_sub : Primrec (fun x : ℕ => x - 1) := by
    exact Primrec.nat_sub.comp ( h_id ) ( Primrec.const 1 )
  have h_pair : Primrec₂ (fun x y : ℕ => Nat.pair x y) := Primrec₂.natPair
  exact h_pair.comp ( h_fst.comp ( h_sub.comp h_fst ) ) ( h_fst.comp ( h_sub.comp h_snd ) )

theorem primrec_cmpIdxA : Primrec cmpIdxA := by
  have h_fst : Primrec (fun x : ℕ => (Nat.unpair x).1) := Primrec.fst.comp Primrec.unpair
  have h_snd : Primrec (fun x : ℕ => (Nat.unpair x).2) := Primrec.snd.comp Primrec.unpair
  have h_sub : Primrec (fun x : ℕ => x - 1) := Primrec.nat_sub.comp Primrec.id (Primrec.const 1)
  exact Primrec₂.natPair.comp
    (h_snd.comp (h_snd.comp (h_sub.comp h_fst)))
    (h_snd.comp (h_snd.comp (h_sub.comp h_snd)))

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

theorem Cnat_pair (cx cy : ℕ) :
    Cnat (Nat.pair cx cy) = ordCode (ONote.cmp (decodeONote cx) (decodeONote cy)) := by
  simp [Cnat, Nat.unpair_pair]

theorem getElem?_range_map (m i : ℕ) :
    ((List.range m).map Cnat)[i]? = if i < m then some (Cnat i) else none := by
  rw [List.getElem?_map]
  rcases lt_or_ge i m with h | h
  · rw [List.getElem?_range h]; simp [h]
  · rw [List.getElem?_eq_none (by simpa using h)]; simp [Nat.not_lt.2 h]

theorem pair_lt_pair {a₁ a₂ b₁ b₂ : ℕ} (ha : a₁ < a₂) (hb : b₁ < b₂) :
    Nat.pair a₁ b₁ < Nat.pair a₂ b₂ :=
  lt_trans (Nat.pair_lt_pair_left b₁ ha) (Nat.pair_lt_pair_right a₂ hb)

theorem computable_cmpStep : Computable cmpStep := by
  refine' Primrec.to_comp _;
  refine' Primrec.of_eq _ _;
  exact fun L => if ( Nat.unpair L.length ).1 = 0 then if ( Nat.unpair L.length ).2 = 0 then some 1 else some 0 else if ( Nat.unpair L.length ).2 = 0 then some 2 else ( L[cmpIdxE L.length]? ).bind fun re => ( L[cmpIdxA L.length]? ).map fun ra => thenNat re ( thenNat ( cmpNV L.length ) ra );
  · convert Primrec.ite _ _ _ using 1;
    · exact Primrec.eq.comp ( Primrec.fst.comp ( Primrec.unpair.comp ( Primrec.list_length ) ) ) ( Primrec.const 0 );
    · convert Primrec.ite _ _ _ using 1;
      · exact Primrec.eq.comp ( Primrec.snd.comp ( Primrec.unpair.comp ( Primrec.list_length ) ) ) ( Primrec.const 0 );
      · exact Primrec.const ( some 1 );
      · exact Primrec.const ( some 0 );
    · convert Primrec.ite _ _ _ using 1;
      · exact Primrec.eq.comp ( Primrec.snd.comp ( Primrec.unpair.comp ( Primrec.list_length ) ) ) ( Primrec.const 0 );
      · exact Primrec.const ( some 2 );
      · refine' Primrec.option_bind _ _;
        · have h_primrec : Primrec₂ (fun (L : List ℕ) (i : ℕ) => L[i]?) := by
            convert Primrec.list_getElem? using 1;
          exact h_primrec.comp ( Primrec.id ) ( primrec_cmpIdxE.comp ( Primrec.list_length ) );
        · refine' Primrec.option_map _ _;
          · exact Primrec.list_getElem?.comp ( Primrec.fst ) ( Primrec.comp ( primrec_cmpIdxA ) ( Primrec.list_length.comp ( Primrec.fst ) ) );
          · convert Primrec₂.comp _ _ _ using 1;
            all_goals try infer_instance;
            · grind +suggestions;
            · exact Primrec.snd.comp ( Primrec.fst );
            · convert Primrec₂.comp _ _ _ using 1;
              all_goals try infer_instance;
              · grind +suggestions;
              · convert Primrec₂.comp _ _ _ using 1;
                all_goals try infer_instance;
                · grind +suggestions;
                · convert Primrec.nat_add.comp _ _ using 1;
                  · convert Primrec.fst.comp ( Primrec.unpair.comp ( Primrec.snd.comp ( Primrec.unpair.comp ( Primrec.nat_sub.comp ( Primrec.fst.comp ( Primrec.unpair.comp ( Primrec.list_length.comp ( Primrec.fst.comp ( Primrec.fst ) ) ) ) ) ( Primrec.const 1 ) ) ) ) ) using 1;
                  · exact Primrec.const 1;
                · convert Primrec.nat_add.comp ( Primrec.fst.comp ( Primrec.unpair.comp ( Primrec.snd.comp ( Primrec.unpair.comp ( Primrec.nat_sub.comp ( Primrec.snd.comp ( Primrec.unpair.comp ( Primrec.list_length.comp ( Primrec.fst.comp ( Primrec.fst ) ) ) ) ) ( Primrec.const 1 ) ) ) ) ) ) ( Primrec.const 1 ) using 1;
              · exact Primrec.snd;
  · unfold cmpStep; aesop;

theorem cmpStep_spec (m : ℕ) : cmpStep ((List.range m).map Cnat) = some (Cnat m) := by
  unfold cmpStep;
  simp +decide [ cmpIdxE, cmpIdxA, cmpNV ];
  rcases n : Nat.unpair m with ⟨ x, y ⟩ ; rcases x with ( _ | x ) <;> rcases y with ( _ | y ) <;> simp +decide [ n ];
  · rw [ show m = 0 by rw [ ← Nat.pair_unpair m, n ] ; rfl ] ; simp +decide [ Cnat ] ;
    native_decide;
  · unfold Cnat; simp +decide [ n ] ;
    unfold decodeONote; simp +decide [ ONote.cmp ] ;
  · unfold Cnat; simp +decide [ n ] ;
    unfold decodeONote; simp +decide [ ONote.cmp ] ;
  · rw [ List.getElem?_range, List.getElem?_range ] <;> norm_num [ n ];
    · unfold Cnat;
      rw [ n ];
      rw [ decodeONote, decodeONote ];
      simp +decide [ ONote.cmp, ordCode_then, ordCode_cmp ];
      unfold cmpNat; aesop;
    · rw [ ← Nat.pair_unpair m, n ] ; simp +arith +decide [ Nat.pair ];
      split_ifs <;> nlinarith [ Nat.unpair_left_le x, Nat.unpair_right_le x, Nat.unpair_left_le y, Nat.unpair_right_le y, Nat.unpair_left_le ( Nat.unpair x |>.2 ), Nat.unpair_right_le ( Nat.unpair x |>.2 ), Nat.unpair_left_le ( Nat.unpair y |>.2 ), Nat.unpair_right_le ( Nat.unpair y |>.2 ) ];
    · rw [ ← Nat.pair_unpair m, n ];
      exact pair_lt_pair ( Nat.unpair_left_le _ |> Nat.lt_succ_of_le ) ( Nat.unpair_left_le _ |> Nat.lt_succ_of_le )

theorem computable_Cnat : Computable Cnat := by
  have h_rec_comp : Computable (fun n => Cnat n) := by
    have h_step : Computable (fun (L : List ℕ) => cmpStep L) := computable_cmpStep
    have h_step_spec : ∀ n, cmpStep ((List.range n).map Cnat) = some (Cnat n) := cmpStep_spec
    convert Computable.nat_strong_rec ( fun ( _ : Unit ) n => Cnat n ) ( h_step.comp Computable.snd |> Computable.to₂ ) ( fun _ n => h_step_spec n ) |> fun h => h.comp ( Computable.const () ) Computable.id using 1;
  exact h_rec_comp

/-! ### Computability of the `NF` predicate (needed to enumerate `NONote`) -/

/-- The `ordCode` is `0` exactly for `Ordering.lt`. -/
theorem ordCode_eq_zero {o : Ordering} : ordCode o = 0 ↔ o = Ordering.lt := by
  cases o <;> simp [ordCode]

/-- `Cnat (pair cx cy) = 0` iff `cmp (decode cx) (decode cy) = lt`. -/
theorem Cnat_pair_eq_zero (cx cy : ℕ) :
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

theorem primrec_nfIdxE : Primrec nfIdxE := by
  convert Primrec.fst.comp ( Primrec.unpair.comp ( Primrec.nat_sub.comp ( Primrec.id ) ( Primrec.const 1 ) ) ) using 1

theorem primrec_nfIdxA : Primrec nfIdxA := by
  convert Primrec.snd.comp ( Primrec.unpair.comp ( Primrec.snd.comp ( Primrec.unpair.comp ( Primrec.nat_sub.comp ( Primrec.id ) ( Primrec.const 1 ) ) ) ) ) using 1

theorem computable_nfTB : Computable nfTB := by
  convert Computable.cond _ _ _ using 1;
  rotate_left;
  exact fun n => n = 0 ∨ nfIdxA n = 0;
  exact fun _ => Bool.true;
  exact fun n => decide ( Cnat ( Nat.pair ( Nat.unpair ( nfIdxA n - 1 ) |>.1 ) ( nfIdxE n ) ) = 0 );
  · convert Computable.of_eq _ _ using 1;
    exact fun n => decide ( n = 0 ) || decide ( nfIdxA n = 0 );
    · convert Computable.cond _ _ _ using 1;
      · convert Computable.of_eq _ _ using 1;
        exact fun n => n == 0;
        · convert Computable.of_eq _ _ using 1;
          exact fun n => Nat.recOn n Bool.true fun _ _ => Bool.false;
          · exact Computable.nat_casesOn ( Computable.id ) ( Computable.const true ) ( Computable.const false );
          · exact fun n => by cases n <;> rfl;
        · grind;
      · exact Computable.const Bool.true;
      · convert Computable.of_eq _ _ using 1;
        exact fun n => decide ( nfIdxA n = 0 );
        · convert Computable.of_eq _ _ using 1;
          exact fun n => decide ( nfIdxA n = 0 );
          · convert Primrec.to_comp _ using 1;
            convert Primrec.eq.comp ( primrec_nfIdxA ) ( Primrec.const 0 ) using 1;
            exact Iff.symm primrecPred_iff_primrec_decide;
          · exact fun _ => rfl;
        · exact fun _ => rfl;
    · grind;
  · exact Computable.const true;
  · have h_nfTB : Computable (fun n => Cnat (Nat.pair (Nat.unpair (nfIdxA n - 1)).1 (nfIdxE n))) := by
      convert computable_Cnat.comp _ using 1;
      convert Primrec.to_comp _ using 1;
      convert Primrec₂.natPair.comp _ _ using 1;
      · exact Primrec.fst.comp ( Primrec.unpair.comp ( Primrec.nat_sub.comp ( primrec_nfIdxA ) ( Primrec.const 1 ) ) );
      · exact primrec_nfIdxE;
    convert Computable.of_eq _ _ using 1;
    exact fun n => Nat.recOn ( Cnat ( Nat.pair ( Nat.unpair ( nfIdxA n - 1 ) |>.1 ) ( nfIdxE n ) ) ) Bool.true fun _ _ => Bool.false;
    · exact Computable.nat_casesOn h_nfTB ( Computable.const true ) ( Computable.const false );
    · intro n; cases h : Cnat ( Nat.pair ( Nat.unpair ( nfIdxA n - 1 ) |>.1 ) ( nfIdxE n ) ) <;> aesop;
  · ext; simp [nfTB];
    by_cases h : ‹_› = 0 <;> simp +decide [ h ]

/-- Step function for the strong recursion computing `Nfb`. -/
def nfStep (L : List Bool) : Option Bool :=
  let c := L.length
  if c = 0 then some true
  else
    (L[nfIdxE c]?).bind fun be =>
      (L[nfIdxA c]?).map fun ba =>
        be && ba && nfTB c

theorem computable_nfStep : Computable nfStep := by
  refine' Computable.of_eq _ _;
  exact fun L => if L.length = 0 then some true else ( L[nfIdxE L.length]? ).bind fun be => ( L[nfIdxA L.length]? ).map fun ba => be && ba && nfTB L.length;
  · convert Computable.cond _ _ _ using 1;
    rotate_left;
    exact fun L => L.length = 0;
    exact fun _ => some true;
    exact fun L => L[nfIdxE L.length]?.bind fun be => Option.map ( fun ba => be && ba && nfTB L.length ) L[nfIdxA L.length]?;
    · convert Computable.of_eq _ _ using 1;
      exact fun L => Nat.recOn L.length Bool.true fun _ _ => Bool.false;
      · exact Computable.nat_casesOn ( Computable.list_length ) ( Computable.const true ) ( Computable.const false );
      · intro n; cases n <;> simp +decide ;
    · exact Computable.const ( some true );
    · refine' Computable.option_bind _ _;
      · exact Computable.list_getElem?.comp ( Computable.id ) ( ( primrec_nfIdxE.comp ( Primrec.list_length ) ).to_comp );
      · refine' Computable.option_map _ _;
        · exact Computable.list_getElem?.comp ( Computable.fst ) ( Primrec.to_comp ( primrec_nfIdxA.comp ( Primrec.list_length.comp ( Primrec.fst ) ) ) );
        · refine' Computable₂.comp _ _ _;
          · exact Computable.of_eq ( Computable.cond ( Computable.fst ) ( Computable.snd ) ( Computable.const false ) ) fun p => by cases p.1 <;> cases p.2 <;> rfl;
          · convert Computable₂.comp _ _ _ using 1;
            all_goals try infer_instance;
            · exact Computable.of_eq ( Computable.cond ( Computable.fst ) ( Computable.snd ) ( Computable.const false ) ) fun p => by cases p.1 <;> cases p.2 <;> rfl;
            · exact Computable.snd.comp ( Computable.fst );
            · exact Computable.snd;
          · convert computable_nfTB.comp ( Computable.list_length.comp ( Computable.fst.comp ( Computable.fst ) ) ) using 1;
    · grind;
  · unfold nfStep; aesop;

theorem getElem?_range_mapNfb (m i : ℕ) :
    ((List.range m).map Nfb)[i]? = if i < m then some (Nfb i) else none := by
  rw [List.getElem?_map]
  rcases lt_or_ge i m with h | h
  · rw [List.getElem?_range h]; simp [h]
  · rw [List.getElem?_eq_none (by simpa using h)]; simp [Nat.not_lt.2 h]

/-
Characterization of `NF` on `oadd` (from mathlib's `decidableNF` argument).
-/
theorem NF_oadd_iff {e : ONote} {n : ℕ+} {a : ONote} :
    (ONote.oadd e n a).NF ↔ ONote.NF e ∧ ONote.NF a ∧ ONote.TopBelow e a := by
  by_cases h : e.NF <;> simp_all +decide;
  · convert ONote.nfBelow_iff_topBelow ( b := e ) |> Iff.trans <| ?_ using 1;
    rotate_left;
    exact a;
    · rfl;
    · exact ⟨ fun h' => h'.snd', fun h' => ONote.NF.oadd h n h' ⟩;
  · exact fun h' => h <| h'.fst

theorem nfStep_spec (n : ℕ) : nfStep ((List.range n).map Nfb) = some (Nfb n) := by
  unfold nfStep Nfb;
  by_cases hn : n = 0;
  · rw [ hn ] ; simp +decide [ decodeONote ] ;
  · rw [ show decodeONote n = ONote.oadd ( decodeONote ( Nat.unpair ( n - 1 ) |>.1 ) ) ⟨ ( Nat.unpair ( Nat.unpair ( n - 1 ) |>.2 ) |>.1 ) + 1, Nat.succ_pos _ ⟩ ( decodeONote ( Nat.unpair ( Nat.unpair ( n - 1 ) |>.2 ) |>.2 ) ) from ?_ ];
    · have h_nfTB : nfTB n = decide (ONote.TopBelow (decodeONote (nfIdxE n)) (decodeONote (nfIdxA n))) := by
        unfold nfTB ONote.TopBelow;
        rcases k : nfIdxA n with ( _ | k ) <;> simp_all +decide [ Cnat_pair_eq_zero ];
        · unfold decodeONote; simp +decide ;
        · rw [ decodeONote ];
      simp_all +decide [ NF_oadd_iff ];
      rw [ List.getElem?_range, List.getElem?_range ];
      · simp +decide [ nfIdxE, nfIdxA ];
        grind;
      · exact lt_of_le_of_lt ( Nat.unpair_right_le _ ) ( lt_of_le_of_lt ( Nat.unpair_right_le _ ) ( Nat.pred_lt hn ) );
      · exact Nat.lt_of_le_of_lt ( Nat.unpair_left_le _ ) ( Nat.pred_lt hn );
    · cases n <;> simp_all +decide [ decodeONote ]

theorem computable_Nfb : Computable Nfb := by
  convert Computable.nat_strong_rec ( fun ( _ : Unit ) n => Nfb n ) ( computable_nfStep.comp Computable.snd |> Computable.to₂ ) ( fun _ n => nfStep_spec n ) |> fun h => h.comp ( Computable.const () ) Computable.id using 1

/-! ### Enumeration of normal-form codes -/

/-- The structural NF-code of the `a`-th notation `natCode a`. -/
def enc (a : ℕ) : ℕ := encodeONote (natCode a).1

theorem decodeONote_enc (a : ℕ) : decodeONote (enc a) = (natCode a).1 := by
  rw [enc, decodeONote_encodeONote]

theorem nf_decode_enc (a : ℕ) : (decodeONote (enc a)).NF := by
  rw [decodeONote_enc]; exact (natCode a).2

theorem enc_injective : Function.Injective enc := by
  intro a b hab;
  apply_fun decodeONote at hab;
  -- Since `decodeONote (enc a) = (natCode a).1` and `decodeONote (enc b) = (natCode b).1`, we have `(natCode a).1 = (natCode b).1`.
  have h_eq : (natCode a).1 = (natCode b).1 := by
    grind +suggestions;
  exact natCode.injective ( Subtype.ext h_eq )

theorem enc_surjOn {n : ℕ} (h : (decodeONote n).NF) : ∃ a, enc a = n := by
  -- Since `natCode` is a bijection, there exists `a` such that `natCode a = ⟨decodeONote n, h⟩`.
  obtain ⟨a, ha⟩ : ∃ a, natCode a = ⟨decodeONote n, h⟩ := by
    exact natCode.surjective _;
  use a
  unfold enc
  simp [ha, encodeONote_decodeONote]

theorem enc_strictMono : StrictMono enc := by
  refine' strictMono_nat_of_lt_succ _;
  intro n
  unfold enc;
  unfold natCode;
  simp +decide [ Denumerable.eqv ];
  simp +decide [ Encodable.equivRangeEncode ];
  simp +decide [ Encodable.decode₂ ];
  simp +decide [ Encodable.decode ];
  simp +decide [ Encodable.decodeSubtype ];
  simp +decide [ Nat.Subtype.ofNat ];
  simp +decide [ Nat.Subtype.succ ];
  grind +suggestions

/-- Number of NF-codes strictly below `n`. -/
def countNF (n : ℕ) : ℕ := ((List.range n).filter (fun k => Nfb k)).length

theorem computable_countNF : Computable countNF := by
  have h_countNF_eq : countNF = fun n => Nat.recOn n 0 (fun n count => count + if Nfb n then 1 else 0) := by
    funext n; induction' n with n ih <;> simp_all +decide [ countNF ] ;
    rw [ List.range_succ, List.filter_append ] ; aesop;
  rw [ h_countNF_eq ];
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
          convert Computable.cond ( computable_Nfb ) ( Computable.const 1 ) ( Computable.const 0 ) using 1;
          grind;
        exact h_cond.comp ( Computable.fst )
      have h_add : Computable (fun (p : ℕ × ℕ) => p.1 + p.2) := by
        exact Primrec.to_comp ( Primrec.nat_add.comp ( Primrec.fst ) ( Primrec.snd ) );
      convert h_add.comp ( Computable.snd.pair h_cond ) using 1;
    exact h_countNF_eq.comp ( Computable.snd );
  · rfl

theorem Nfb_enc (a : ℕ) : Nfb (enc a) = true := by
  simp [Nfb, nf_decode_enc]

theorem countNF_eq (n : ℕ) :
    countNF n = ((Finset.range n).filter (fun k => (decodeONote k).NF)).card := by
  congr

theorem countNF_enc (a : ℕ) : countNF (enc a) = a := by
  have h_card : ((Finset.range (enc a)).filter (fun k => (decodeONote k).NF)).card = ((Finset.range a).image enc).card := by
    congr 1 with x ; simp +decide [ Finset.mem_image, Finset.mem_range ];
    constructor;
    · intro hx;
      obtain ⟨ b, hb ⟩ := enc_surjOn hx.2;
      exact ⟨ b, by simpa [ hb ] using enc_strictMono.lt_iff_lt.mp ( by aesop ), hb ⟩;
    · rintro ⟨ b, hb, rfl ⟩ ; exact ⟨ enc_strictMono hb, nf_decode_enc _ ⟩;
  rw [ Finset.card_image_of_injective _ enc_injective ] at h_card ; aesop

theorem countNF_succ (n : ℕ) : countNF (n + 1) = countNF n + (if Nfb n then 1 else 0) := by
  have h_filter : List.filter (fun k => Nfb k) (List.range (n + 1)) = List.filter (fun k => Nfb k) (List.range n) ++ if Nfb n then [n] else [] := by
    simp +decide [ List.range_succ ];
    grind;
  unfold countNF; aesop;

theorem countNF_mono : Monotone countNF := by
  refine' monotone_nat_of_le_succ _;
  simp +decide [ countNF_succ ]

theorem lt_countNF_succ_enc (a : ℕ) : a < countNF (enc a + 1) := by
  rw [ countNF_succ ];
  rw [ countNF_enc, if_pos ( Nfb_enc a ) ] ; linarith

theorem exists_count (a : ℕ) : ∃ n, a < countNF (n + 1) := ⟨enc a, lt_countNF_succ_enc a⟩

/-- The `a`-th NF-code, defined by an (always-terminating) search. -/
noncomputable def nthNF (a : ℕ) : ℕ := Nat.find (exists_count a)

theorem enc_eq_nthNF (a : ℕ) : enc a = nthNF a := by
  refine' Eq.symm ( Nat.find_eq_iff _ |>.2 _ );
  exact ⟨ lt_countNF_succ_enc a, fun n hn => not_lt_of_ge <| by linarith [ countNF_mono <| Nat.succ_le_of_lt hn, countNF_enc a ] ⟩

theorem rfind_nthNF (a : ℕ) :
    Nat.rfind (fun n => (Part.some (decide (a < countNF (n + 1))) : Part Bool)) =
      Part.some (nthNF a) := by
  convert Part.eq_some_iff.mpr _ using 1;
  simp +zetaDelta at *;
  exact ⟨ Nat.find_spec ( exists_count a ), fun { m } hm => not_lt.1 fun contra => hm.not_ge <| Nat.find_min' _ contra ⟩

theorem computable_nthNF : Computable nthNF := by
  convert Computable.of_eq _ _ using 1;
  exact fun n => Nat.find ( exists_count n );
  · convert Partrec.rfind _ |> Partrec.of_eq <| _ using 1;
    exact fun n m => Part.some ( decide ( n < countNF ( m + 1 ) ) );
    · have h_countNF : Computable₂ (fun (n m : ℕ) => countNF (m + 1)) := by
        convert Computable.comp ( computable_countNF ) ( Computable.succ.comp ( Computable.snd ) ) using 1;
      have h_lt : Computable₂ (fun (n m : ℕ) => decide (n < m)) := by
        convert Primrec.to_comp _ using 1;
        convert Primrec.nat_lt.comp ( Primrec.fst ) ( Primrec.snd ) using 1;
        exact Iff.symm primrecPred_iff_primrec_decide;
      convert h_lt.comp ( Computable.fst ) ( h_countNF.comp ( Computable.fst ) ( Computable.snd ) ) using 1;
    · convert rfind_nthNF using 1;
  · aesop

theorem computable_enc : Computable enc :=
  computable_nthNF.of_eq (fun a => (enc_eq_nthNF a).symm)

/-! ### Assembling the final result -/

theorem lt_iff_Cnat (a b : ℕ) :
    natCode a < natCode b ↔ Cnat (Nat.pair (enc a) (enc b)) = 0 := by
  rw [Cnat_pair_eq_zero];
  have h_dec : (natCode a).1.cmp (natCode b).1 = Ordering.lt ↔ natCode a < natCode b := by
    have h_linear_order : ∀ x y : NONote, (x.cmp y = Ordering.lt ↔ x < y) := by
      have h_linear_order : ∀ x y : NONote, (x.cmp y).Compares x y :=
        fun x y => NONote.cmp_compares x y
      intro x y; specialize h_linear_order x y; rcases h : x.cmp y with ( _ | _ | _ ) <;> simp_all +decide [ Ordering.Compares ] ;
      exact le_of_lt h_linear_order;
    exact h_linear_order _ _;
  rw [ decodeONote_enc, decodeONote_enc, h_dec ]

/-- **The F-φ target.** The order `natCode a < natCode b` on ℕ-codes is recursively enumerable
(in fact computable). Discharges `SeamDefinability.rePred_ltPull_natCode`. -/
theorem rePred_ltPull_natCode :
    REPred fun v : List.Vector ℕ 2 ↦ natCode (v.get 0) < natCode (v.get 1) := by
  apply ComputablePred.to_re
  generalize_proofs at *; (
  refine' ⟨ _, _ ⟩;
  infer_instance;
  convert Computable.of_eq _ _ using 1;
  exact fun v => decide ( Cnat ( Nat.pair ( enc ( v.get 0 ) ) ( enc ( v.get 1 ) ) ) = 0 );
  · have h_nfTB : Computable (fun v : List.Vector ℕ 2 => Cnat (Nat.pair (enc (v.get 0)) (enc (v.get 1)))) := by
      -- The function `Cnat` is computable by definition.
      have h_Cnat : Computable Cnat := by
        exact computable_Cnat
      generalize_proofs at *; (
      -- The function `enc` is computable by definition.
      have h_enc : Computable enc := by
        exact computable_enc
      generalize_proofs at *; (
      refine' h_Cnat.comp _;
      convert Computable.pair ( h_enc.comp ( Primrec.to_comp ( Primrec.vector_get.comp ( Primrec.id ) ( Primrec.const 0 ) ) ) ) ( h_enc.comp ( Primrec.to_comp ( Primrec.vector_get.comp ( Primrec.id ) ( Primrec.const 1 ) ) ) ) using 1));
    convert Computable.of_eq _ _ using 1;
    exact fun v => Nat.recOn ( Cnat ( Nat.pair ( enc ( v.get 0 ) ) ( enc ( v.get 1 ) ) ) ) Bool.true fun _ _ => Bool.false;
    · exact Computable.nat_casesOn h_nfTB ( Computable.const true ) ( Computable.const false );
    · intro n; cases h : Cnat ( Nat.pair ( enc ( n.get 0 ) ) ( enc ( n.get 1 ) ) ) <;> aesop;
  · exact fun v => by rw [ decide_eq_decide.mpr ( lt_iff_Cnat _ _ |> Iff.symm ) ] ;)

end GoodsteinPA.ONoteComp
