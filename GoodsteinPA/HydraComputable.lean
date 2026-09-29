/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
module

public import GoodsteinPA.ToMathlib.ONote.Computability
public import GoodsteinPA.HydraEscape

@[expose] public section

/-!
# The canonical hydra battle is computable on codes (stage 2, part B)

Target: `Computable₂ (fun m N => toCode (battle (ofCode m) N))`, from which
`exists_sigma1_battle_def` follows by Foundation's `codeOfPartrec'`.

Everything runs on codes.  A hydra code `c` lists its children's codes (`childC`, inverse `nodeC`,
Cantor pairing as in `ofCode`/`toCode`), and every child code is `< c`, so each hydra function is a
`Computable.nat_strong_rec` on codes — the `ONoteComp.computable_Cnat` pattern.
-/

namespace GoodsteinPA.Hydra

open ONote LeanGallery.Logic.Hydra LeanGallery.Logic.Hydra.Hydra


/-! ### (a) Child-code lists -/

/-- The codes of the children of the hydra with code `c`. -/
def childC : ℕ → List ℕ
  | 0 => []
  | n + 1 =>
    have := Nat.unpair_right_le n
    (Nat.unpair n).1 :: childC (Nat.unpair n).2
termination_by c => c
decreasing_by omega

/-- The code of the hydra whose children have the given codes. -/
def nodeC : List ℕ → ℕ
  | [] => 0
  | a :: l => Nat.pair a (nodeC l) + 1

theorem toCode_node (cs : List Hydra) : toCode (node cs) = nodeC (cs.map toCode) := by
  induction cs with
  | nil => rw [toCode]; rfl
  | cons c cs ih => rw [toCode, ih]; rfl

theorem childC_nodeC : ∀ l : List ℕ, childC (nodeC l) = l
  | [] => by rw [nodeC, childC]
  | a :: l => by rw [nodeC, childC]; simp [Nat.unpair_pair, childC_nodeC l]

theorem ofCode_eq (c : ℕ) : ofCode c = node ((childC c).map ofCode) := by
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    rcases c with _ | n
    · rw [childC, ofCode]; rfl
    · rw [ofCode, childC]
      have := Nat.unpair_right_le n
      rw [ih _ (by omega)]
      simp

theorem childC_toCode_node (cs : List Hydra) : childC (toCode (node cs)) = cs.map toCode := by
  rw [toCode_node, childC_nodeC]

theorem lt_of_mem_childC : ∀ {c a : ℕ}, a ∈ childC c → a < c
  | 0, _, h => by rw [childC] at h; simp at h
  | n + 1, a, h => by
    rw [childC] at h
    have h1 := Nat.unpair_left_le n
    have h2 := Nat.unpair_right_le n
    rcases List.mem_cons.mp h with rfl | h'
    · omega
    · have := lt_of_mem_childC h'; omega

theorem primrec_nodeC : Primrec nodeC := by
  have : nodeC = fun l => l.foldr (fun a acc => Nat.pair a acc + 1) 0 := by
    funext l; induction l with
    | nil => rfl
    | cons a l ih => simp [nodeC, ih]
  rw [this]
  exact Primrec.list_foldr Primrec.id (Primrec.const 0)
    (Primrec.succ.comp (Primrec₂.natPair.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd))).to₂

/-! ### A three-way selector on comparison codes (`lt = 0`, `eq = 1`, `gt = 2`) -/

def sel3 (r x0 x1 x2 : ℕ) : ℕ := if r = 0 then x0 else if r = 1 then x1 else x2

theorem primrec_sel3 : Primrec (fun q : ℕ × ℕ × ℕ × ℕ => sel3 q.1 q.2.1 q.2.2.1 q.2.2.2) := by
  unfold sel3
  exact Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 0)) (Primrec.fst.comp Primrec.snd)
    (Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 1))
      (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))

theorem primrec_sel3' {α : Type*} [Primcodable α] {r x0 x1 x2 : α → ℕ} (hr : Primrec r)
    (h0 : Primrec x0) (h1 : Primrec x1) (h2 : Primrec x2) :
    Primrec fun a => sel3 (r a) (x0 a) (x1 a) (x2 a) :=
  primrec_sel3.comp (hr.pair (h0.pair (h1.pair h2)))

theorem sel3_ordCode (o : Ordering) (x0 x1 x2 : ℕ) :
    sel3 (ordCode o) x0 x1 x2 = match o with | .lt => x0 | .eq => x1 | .gt => x2 := by
  cases o <;> rfl

/-! ### (b) `insertTerm` on ONote codes -/

/-- `insertTerm` transported to ONote codes. -/
def insC (e c : ℕ) : ℕ := encodeONote (insertTerm (decodeONote e) (decodeONote c))

/-- One step of the strong recursion for `insC e`, reading the table of values at codes `< c`. -/
def insStep (e : ℕ) (L : List ℕ) : Option ℕ :=
  if L.length = 0 then some (Nat.pair e (Nat.pair 0 0) + 1)
  else some (sel3 (Cnat (Nat.pair e (Nat.unpair (L.length - 1)).1))
    (Nat.pair (Nat.unpair (L.length - 1)).1
      (Nat.pair (Nat.unpair (Nat.unpair (L.length - 1)).2).1
        ((L[(Nat.unpair (Nat.unpair (L.length - 1)).2).2]?).getD 0)) + 1)
    (Nat.pair (Nat.unpair (L.length - 1)).1
      (Nat.pair ((Nat.unpair (Nat.unpair (L.length - 1)).2).1 + 1)
        (Nat.unpair (Nat.unpair (L.length - 1)).2).2) + 1)
    (Nat.pair e (Nat.pair 0 L.length) + 1))

theorem insStep_spec (e c : ℕ) : insStep e ((List.range c).map (insC e)) = some (insC e c) := by
  simp only [insStep, List.length_map, List.length_range]
  rcases c with _ | m
  · simp only [if_true]
    simp [insC, decodeONote, insertTerm, encodeONote, encodeONote_decodeONote]
  · simp only [Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
    congr 1
    have hb : (Nat.unpair (Nat.unpair m).2).2 < m + 1 := by
      have := Nat.unpair_right_le m
      have := Nat.unpair_right_le (Nat.unpair m).2
      omega
    rw [List.getElem?_map, List.getElem?_range hb, Option.map_some, Option.getD_some,
      Cnat_pair]
    have hdec : decodeONote (m + 1) = oadd (decodeONote (Nat.unpair m).1)
        ⟨(Nat.unpair (Nat.unpair m).2).1 + 1, Nat.succ_pos _⟩
        (decodeONote (Nat.unpair (Nat.unpair m).2).2) := by rw [decodeONote]
    unfold insC
    rw [hdec]
    rw [sel3_ordCode]
    cases hcmp : ONote.cmp (decodeONote e) (decodeONote (Nat.unpair m).1) <;>
      simp only [insertTerm, hcmp, encodeONote, encodeONote_decodeONote] <;>
      first | rfl | simp [Nat.pair_unpair]

theorem primrec_insStep : Primrec₂ insStep := by
  have hlen : Primrec fun p : ℕ × List ℕ => p.2.length := Primrec.list_length.comp Primrec.snd
  have hm : Primrec fun p : ℕ × List ℕ => Nat.unpair (p.2.length - 1) :=
    Primrec.unpair.comp (Primrec.nat_sub.comp hlen (Primrec.const 1))
  have ha : Primrec fun p : ℕ × List ℕ => (Nat.unpair (p.2.length - 1)).1 := Primrec.fst.comp hm
  have hmm : Primrec fun p : ℕ × List ℕ => Nat.unpair (Nat.unpair (p.2.length - 1)).2 :=
    Primrec.unpair.comp (Primrec.snd.comp hm)
  have hk : Primrec fun p : ℕ × List ℕ => (Nat.unpair (Nat.unpair (p.2.length - 1)).2).1 :=
    Primrec.fst.comp hmm
  have hb : Primrec fun p : ℕ × List ℕ => (Nat.unpair (Nat.unpair (p.2.length - 1)).2).2 :=
    Primrec.snd.comp hmm
  have hpair : Primrec₂ Nat.pair := Primrec₂.natPair
  have hr : Primrec fun p : ℕ × List ℕ => Cnat (Nat.pair p.1 (Nat.unpair (p.2.length - 1)).1) :=
    primrec_Cnat.comp (hpair.comp Primrec.fst ha)
  have hL : Primrec fun p : ℕ × List ℕ =>
      (p.2[(Nat.unpair (Nat.unpair (p.2.length - 1)).2).2]?).getD 0 :=
    Primrec.option_getD.comp (Primrec.list_getElem?.comp Primrec.snd hb) (Primrec.const 0)
  have x0 : Primrec fun p : ℕ × List ℕ =>
      Nat.pair (Nat.unpair (p.2.length - 1)).1
        (Nat.pair (Nat.unpair (Nat.unpair (p.2.length - 1)).2).1
          ((p.2[(Nat.unpair (Nat.unpair (p.2.length - 1)).2).2]?).getD 0)) + 1 :=
    Primrec.succ.comp (hpair.comp ha (hpair.comp hk hL))
  have x1 : Primrec fun p : ℕ × List ℕ =>
      Nat.pair (Nat.unpair (p.2.length - 1)).1
        (Nat.pair ((Nat.unpair (Nat.unpair (p.2.length - 1)).2).1 + 1)
          (Nat.unpair (Nat.unpair (p.2.length - 1)).2).2) + 1 :=
    Primrec.succ.comp (hpair.comp ha (hpair.comp (Primrec.succ.comp hk) hb))
  have x2 : Primrec fun p : ℕ × List ℕ => Nat.pair p.1 (Nat.pair 0 p.2.length) + 1 :=
    Primrec.succ.comp (hpair.comp Primrec.fst (hpair.comp (Primrec.const 0) hlen))
  have hmain : Primrec fun p : ℕ × List ℕ => insStep p.1 p.2 :=
    (Primrec.option_some.comp (Primrec.ite (Primrec.eq.comp hlen (Primrec.const 0))
      (Primrec.succ.comp (hpair.comp Primrec.fst (Primrec.const (Nat.pair 0 0))))
      (primrec_sel3' hr x0 x1 x2))).of_eq fun p => by
        simp only [insStep]
        by_cases h0 : p.2.length = 0 <;> simp [h0]
  exact hmain.to₂

/-- **`insertTerm` is primitive recursive on ONote codes.** -/
theorem primrec_insC : Primrec₂ insC :=
  Primrec.nat_strong_rec insC primrec_insStep insStep_spec

/-! ### (c) The ordinal of a hydra, on codes -/

/-- The ONote code of `ord (ofCode c)`. -/
def ordC (c : ℕ) : ℕ := encodeONote (ord (ofCode c))

theorem ord_ofCode_succ (n : ℕ) :
    ord (ofCode (n + 1)) = insertTerm (ord (ofCode (Nat.unpair n).1)) (ord (ofCode (Nat.unpair n).2)) := by
  rw [ofCode]
  split
  rename_i cs hcs
  rw [ord_node, List.map_cons, hcs, ord_node]
  rfl

def ordStep (L : List ℕ) : Option ℕ :=
  if L.length = 0 then some 0
  else some (insC ((L[(Nat.unpair (L.length - 1)).1]?).getD 0)
    ((L[(Nat.unpair (L.length - 1)).2]?).getD 0))

theorem ordStep_spec (c : ℕ) : ordStep ((List.range c).map ordC) = some (ordC c) := by
  simp only [ordStep, List.length_map, List.length_range]
  rcases c with _ | n
  · simp only [ordC, ofCode, if_true]
    rw [show ord leaf = 0 from ord_leaf]
    rfl
  · simp only [Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
    have h1 : (Nat.unpair n).1 < n + 1 := Nat.lt_succ_of_le (Nat.unpair_left_le n)
    have h2 : (Nat.unpair n).2 < n + 1 := Nat.lt_succ_of_le (Nat.unpair_right_le n)
    rw [List.getElem?_map, List.getElem?_range h1, List.getElem?_map, List.getElem?_range h2]
    simp only [Option.map_some, Option.getD_some]
    simp [insC, ordC, ord_ofCode_succ, decodeONote_encodeONote]

theorem primrec_ordStep : Primrec ordStep := by
  have hlen : Primrec fun L : List ℕ => L.length := Primrec.list_length
  have hm : Primrec fun L : List ℕ => Nat.unpair (L.length - 1) :=
    Primrec.unpair.comp (Primrec.nat_sub.comp hlen (Primrec.const 1))
  have hA : Primrec fun L : List ℕ => (L[(Nat.unpair (L.length - 1)).1]?).getD 0 :=
    Primrec.option_getD.comp (Primrec.list_getElem?.comp Primrec.id (Primrec.fst.comp hm))
      (Primrec.const 0)
  have hB : Primrec fun L : List ℕ => (L[(Nat.unpair (L.length - 1)).2]?).getD 0 :=
    Primrec.option_getD.comp (Primrec.list_getElem?.comp Primrec.id (Primrec.snd.comp hm))
      (Primrec.const 0)
  exact (Primrec.option_some.comp (Primrec.ite (Primrec.eq.comp hlen (Primrec.const 0))
    (Primrec.const 0) (primrec_insC.comp hA hB))).of_eq fun L => by
      simp only [ordStep]
      by_cases h0 : L.length = 0 <;> simp [h0]

/-- **The Kirby–Paris ordinal is primitive recursive on hydra codes.** -/
theorem primrec_ordC : Primrec ordC := by
  have := Primrec.nat_strong_rec (fun (_ : Unit) c => ordC c)
    (primrec_ordStep.comp Primrec.snd).to₂ (fun _ c => ordStep_spec c)
  exact this.comp (Primrec.const ()) Primrec.id

/-! ### (d) The canonical child, on codes -/

theorem ordC_toCode (h : Hydra) : ordC (toCode h) = encodeONote (ord h) := by
  rw [ordC, ofCode_toCode]

/-- `ord x < ord c`, decided on codes. -/
theorem cmp_lt_iff_Cnat (e c : Hydra) :
    (ONote.cmp (ord e) (ord c) == .lt) = decide (Cnat (Nat.pair (ordC (toCode e)) (ordC (toCode c))) = 0) := by
  rw [ordC_toCode, ordC_toCode, Cnat_pair, decodeONote_encodeONote, decodeONote_encodeONote]
  cases ONote.cmp (ord e) (ord c) <;> rfl

/-- The fold step: extend the (index, tail) state by a new head `c`. -/
def pickStep (c : ℕ) (st : ℕ × List ℕ) : ℕ × List ℕ :=
  (if st.2.length = 0 then 0 else
    Option.casesOn (st.2[st.1]?) 0 fun e =>
      if Cnat (Nat.pair (ordC e) (ordC c)) = 0 then st.1 + 1 else 0,
   c :: st.2)

/-- Index of the canonical child, on a list of child codes. -/
def pickIdxC (l : List ℕ) : ℕ := (l.foldr pickStep (0, [])).1

theorem pick_branch (L : List Hydra) (j : ℕ) (c : Hydra) :
    (Option.casesOn (Option.map toCode L[j]?) 0
        (fun e => if Cnat (Nat.pair (ordC e) (ordC (toCode c))) = 0 then j + 1 else 0) : ℕ) =
      (match L[j]? with
        | some e => if (ONote.cmp (ord e) (ord c) == Ordering.lt) = true then j + 1 else 0
        | none => 0 : ℕ) := by
  cases h : L[j]? with
  | none => rfl
  | some e =>
    simp only [Option.map_some]
    rw [cmp_lt_iff_Cnat]
    by_cases hlt : Cnat (Nat.pair (ordC (toCode e)) (ordC (toCode c))) = 0 <;> simp [hlt]

theorem foldr_pickStep (cs : List Hydra) :
    (cs.map toCode).foldr pickStep (0, []) = (pickIdx cs, cs.map toCode) := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    rw [List.map_cons, List.foldr_cons, ih]
    simp only [pickStep, Prod.mk.injEq, and_true]
    rcases cs with _ | ⟨d, cs⟩
    · simp [pickIdx]
    · simp only [List.map_cons, List.length_cons, Nat.add_one_ne_zero, if_false]
      rw [pickIdx, ← List.map_cons, List.getElem?_map]
      exact pick_branch _ _ c

theorem pickIdxC_map (cs : List Hydra) : pickIdxC (cs.map toCode) = pickIdx cs := by
  rw [pickIdxC, foldr_pickStep]

theorem primrec_pickIdxC : Primrec pickIdxC := by
  have hC : Primrec₂ fun (e c : ℕ) => decide (Cnat (Nat.pair (ordC e) (ordC c)) = 0) :=
    (Primrec.eq.decide.comp (primrec_Cnat.comp (Primrec₂.natPair.comp
      (primrec_ordC.comp Primrec.fst) (primrec_ordC.comp Primrec.snd))) (Primrec.const 0)).to₂
  have hstep : Primrec₂ pickStep := by
    have h1 : Primrec fun q : ℕ × (ℕ × List ℕ) => q.2.2.length := Primrec.list_length.comp
      (Primrec.snd.comp Primrec.snd)
    have hget : Primrec fun q : ℕ × (ℕ × List ℕ) => q.2.2[q.2.1]? :=
      Primrec.list_getElem?.comp (Primrec.snd.comp Primrec.snd) (Primrec.fst.comp Primrec.snd)
    have hbranch : Primrec₂ fun (q : ℕ × (ℕ × List ℕ)) (e : ℕ) =>
        if Cnat (Nat.pair (ordC e) (ordC q.1)) = 0 then q.2.1 + 1 else 0 :=
      (Primrec.ite (PrimrecPred.of_eq (Primrec.eq.comp (primrec_Cnat.comp (Primrec₂.natPair.comp
          (primrec_ordC.comp Primrec.snd) (primrec_ordC.comp (Primrec.fst.comp Primrec.fst))))
          (Primrec.const 0)) fun _ => Iff.rfl)
        (Primrec.succ.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)))
        (Primrec.const 0)).to₂
    have hidx : Primrec fun q : ℕ × (ℕ × List ℕ) => (if q.2.2.length = 0 then 0 else
        Option.casesOn (q.2.2[q.2.1]?) 0 fun e =>
          if Cnat (Nat.pair (ordC e) (ordC q.1)) = 0 then q.2.1 + 1 else 0) :=
      Primrec.ite (Primrec.eq.comp h1 (Primrec.const 0)) (Primrec.const 0)
        (Primrec.option_casesOn hget (Primrec.const 0) hbranch)
    exact (hidx.pair (Primrec.list_cons.comp Primrec.fst (Primrec.snd.comp Primrec.snd))).to₂
  exact Primrec.fst.comp (Primrec.list_foldr Primrec.id (Primrec.const (0, []))
    (hstep.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂)

/-! ### (e) The regrowing chop, on codes -/

theorem nodeC_childC (c : ℕ) : nodeC (childC c) = c := by
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    rcases c with _ | n
    · rw [childC]; rfl
    · rw [childC, nodeC]
      have := Nat.unpair_right_le n
      rw [ih _ (by omega)]
      simp [Nat.pair_unpair]

theorem toCode_ofCode (c : ℕ) : toCode (ofCode c) = c := by
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    rw [ofCode_eq, toCode_node, List.map_map]
    conv_rhs => rw [← nodeC_childC c]
    congr 1
    conv_rhs => rw [← List.map_id (childC c)]
    exact List.map_congr_left fun a ha => ih a (lt_of_mem_childC ha)

def childStep (L : List (List ℕ)) : Option (List ℕ) :=
  if L.length = 0 then some []
  else some ((Nat.unpair (L.length - 1)).1 :: (L[(Nat.unpair (L.length - 1)).2]?).getD [])

theorem childStep_spec (c : ℕ) : childStep ((List.range c).map childC) = some (childC c) := by
  simp only [childStep, List.length_map, List.length_range]
  rcases c with _ | n
  · simp [childC]
  · simp only [Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
    have h2 : (Nat.unpair n).2 < n + 1 := Nat.lt_succ_of_le (Nat.unpair_right_le n)
    rw [List.getElem?_map, List.getElem?_range h2, Option.map_some, Option.getD_some, childC]

theorem primrec_childC : Primrec childC := by
  have hlen : Primrec fun L : List (List ℕ) => L.length := Primrec.list_length
  have hm : Primrec fun L : List (List ℕ) => Nat.unpair (L.length - 1) :=
    Primrec.unpair.comp (Primrec.nat_sub.comp hlen (Primrec.const 1))
  have hstep : Primrec childStep :=
    (Primrec.option_some.comp (Primrec.ite (Primrec.eq.comp hlen (Primrec.const 0))
      (Primrec.const []) (Primrec.list_cons.comp (Primrec.fst.comp hm)
        (Primrec.option_getD.comp (Primrec.list_getElem?.comp Primrec.id (Primrec.snd.comp hm))
          (Primrec.const []))))).of_eq fun L => by
      simp only [childStep]
      by_cases h0 : L.length = 0 <;> simp [h0]
  have := Primrec.nat_strong_rec (fun (_ : Unit) c => childC c)
    (hstep.comp Primrec.snd).to₂ (fun _ c => childStep_spec c)
  exact this.comp (Primrec.const ()) Primrec.id

theorem primrec_eraseIdx : Primrec₂ (fun (l : List ℕ) (i : ℕ) => l.eraseIdx i) :=
  (Primrec.list_append.comp (Primrec.list_take.comp Primrec.snd Primrec.fst)
    (Primrec.list_drop.comp (Primrec.succ.comp Primrec.snd) Primrec.fst)).to₂.of_eq
    fun l i => (List.eraseIdx_eq_take_drop_succ l i).symm

theorem primrec_replicate : Primrec₂ (fun (k x : ℕ) => List.replicate k x) :=
  (Primrec.list_map (Primrec.list_range.comp Primrec.fst) (Primrec.snd.comp Primrec.fst).to₂).to₂.of_eq
    fun k x => by simp

/-- `chopC` transported to hydra codes. -/
def chopCC (n c : ℕ) : ℕ := toCode (chopC n (ofCode c))

/-- `l[i]?` under a name (the `)[` token is claimed by imported notation). -/
def idx? (l : List ℕ) (i : ℕ) : Option ℕ := l[i]?

/-- One strong-recursion step for `chopCC n`, reading the table at codes `< c`. -/
def chopStep (n : ℕ) (L : List ℕ) : Option ℕ :=
  some (Option.casesOn (idx? (childC L.length) (pickIdxC (childC L.length))) L.length fun ec =>
    Option.casesOn (idx? (childC ec) (pickIdxC (childC ec))) L.length fun f =>
      if f = 0 then
        nodeC ((childC L.length).eraseIdx (pickIdxC (childC L.length)) ++
          List.replicate (n + 1) (nodeC ((childC ec).eraseIdx (pickIdxC (childC ec)))))
      else nodeC ((L[ec]?).getD 0 :: (childC L.length).eraseIdx (pickIdxC (childC L.length))))

theorem map_toCode_childC (c : ℕ) : ((childC c).map ofCode).map toCode = childC c := by
  rw [List.map_map]
  conv_rhs => rw [← List.map_id (childC c)]
  exact List.map_congr_left fun a _ => toCode_ofCode a

theorem toCode_eq_zero {g : Hydra} : toCode g = 0 ↔ g = leaf := by
  constructor
  · intro h; rw [← ofCode_toCode g, h, ofCode]
  · rintro rfl; rw [leaf, toCode]

theorem chopStep_spec (n c : ℕ) :
    chopStep n ((List.range c).map (chopCC n)) = some (chopCC n c) := by
  simp only [chopStep, idx?, List.length_map, List.length_range]
  congr 1
  set ds := (childC c).map ofCode with hdsdef
  have hc : ofCode c = node ds := ofCode_eq c
  have hds : ds.map toCode = childC c := map_toCode_childC c
  rw [← hds, pickIdxC_map, List.getElem?_map]
  unfold chopCC
  rw [hc, chopC.eq_1]
  split
  · rename_i hd
    conv_lhs => rw [hd]
    simp only [Option.map_none]
    rw [← hc, toCode_ofCode]
  · rename_i es hd
    conv_lhs => rw [hd]
    simp only [Option.map_some]
    rw [childC_toCode_node, pickIdxC_map]
    have hes : idx? (es.map toCode) (pickIdx es) = (es[pickIdx es]?).map toCode :=
      List.getElem?_map ..
    simp only [idx?] at hes
    conv_lhs => rw [hes]
    split
    · rename_i he
      conv_lhs => rw [he]
      simp only [Option.map_none]
      rw [← hc, toCode_ofCode]
    · rename_i he
      conv_lhs => rw [he]
      simp only [Option.map_some, show toCode (node []) = 0 from toCode_eq_zero.mpr rfl, if_true]
      rw [toCode_node, List.map_append, List.map_replicate, toCode_node, ← List.eraseIdx_map,
        ← List.eraseIdx_map]
    · rename_i g _ _
      have he : es[pickIdx es]? = some g := ‹_›
      have hg : g = node [] → False := ‹_›
      conv_lhs => rw [he]
      have hg0 : toCode g ≠ 0 := fun h => hg (toCode_eq_zero.mp h)
      simp only [Option.map_some, hg0, if_false]
      have hmem : node es ∈ ds := List.mem_of_getElem? hd
      have hlt : toCode (node es) < c := by
        apply lt_of_mem_childC
        rw [← hds]; exact List.mem_map_of_mem hmem
      rw [List.getElem?_map, List.getElem?_range hlt, Option.map_some, Option.getD_some,
        ofCode_toCode, toCode_node (chopC n (node es) :: _), List.map_cons, ← List.eraseIdx_map]

theorem primrec_idx? : Primrec₂ idx? := Primrec.list_getElem?

theorem primrec_chopStep : Primrec₂ chopStep := by
  -- `p = (n, L)`
  have hc : Primrec fun p : ℕ × List ℕ => p.2.length := Primrec.list_length.comp Primrec.snd
  have hD : Primrec fun p : ℕ × List ℕ => childC p.2.length := primrec_childC.comp hc
  have hI : Primrec fun p : ℕ × List ℕ => pickIdxC (childC p.2.length) := primrec_pickIdxC.comp hD
  have hrest : Primrec fun p : ℕ × List ℕ =>
      (childC p.2.length).eraseIdx (pickIdxC (childC p.2.length)) := primrec_eraseIdx.comp hD hI
  -- `q = (p, ec)`
  have hE : Primrec fun q : (ℕ × List ℕ) × ℕ => childC q.2 := primrec_childC.comp Primrec.snd
  have hK : Primrec fun q : (ℕ × List ℕ) × ℕ => pickIdxC (childC q.2) := primrec_pickIdxC.comp hE
  have hA : Primrec fun q : (ℕ × List ℕ) × ℕ =>
      nodeC ((childC q.1.2.length).eraseIdx (pickIdxC (childC q.1.2.length)) ++
        List.replicate (q.1.1 + 1) (nodeC ((childC q.2).eraseIdx (pickIdxC (childC q.2))))) :=
    primrec_nodeC.comp (Primrec.list_append.comp (hrest.comp Primrec.fst)
      (primrec_replicate.comp (Primrec.succ.comp (Primrec.fst.comp Primrec.fst))
        (primrec_nodeC.comp (primrec_eraseIdx.comp hE hK))))
  have hB : Primrec fun q : (ℕ × List ℕ) × ℕ =>
      nodeC ((q.1.2[q.2]?).getD 0 :: (childC q.1.2.length).eraseIdx (pickIdxC (childC q.1.2.length))) :=
    primrec_nodeC.comp (Primrec.list_cons.comp
      (Primrec.option_getD.comp (Primrec.list_getElem?.comp (Primrec.snd.comp Primrec.fst)
        Primrec.snd) (Primrec.const 0)) (hrest.comp Primrec.fst))
  have hg2 : Primrec₂ fun (q : (ℕ × List ℕ) × ℕ) (f : ℕ) =>
      if f = 0 then
        nodeC ((childC q.1.2.length).eraseIdx (pickIdxC (childC q.1.2.length)) ++
          List.replicate (q.1.1 + 1) (nodeC ((childC q.2).eraseIdx (pickIdxC (childC q.2)))))
      else nodeC ((q.1.2[q.2]?).getD 0 ::
        (childC q.1.2.length).eraseIdx (pickIdxC (childC q.1.2.length))) :=
    (Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 0)) (hA.comp Primrec.fst)
      (hB.comp Primrec.fst)).to₂
  have hinner : Primrec₂ fun (p : ℕ × List ℕ) (ec : ℕ) =>
      (Option.casesOn (idx? (childC ec) (pickIdxC (childC ec))) p.2.length fun f =>
        if f = 0 then
          nodeC ((childC p.2.length).eraseIdx (pickIdxC (childC p.2.length)) ++
            List.replicate (p.1 + 1) (nodeC ((childC ec).eraseIdx (pickIdxC (childC ec)))))
        else nodeC ((p.2[ec]?).getD 0 ::
          (childC p.2.length).eraseIdx (pickIdxC (childC p.2.length))) : ℕ) :=
    (Primrec.option_casesOn (primrec_idx?.comp hE hK) (hc.comp Primrec.fst) hg2).to₂
  have hmain : Primrec fun p : ℕ × List ℕ => chopStep p.1 p.2 :=
    Primrec.option_some.comp (Primrec.option_casesOn (primrec_idx?.comp hD hI) hc hinner)
  exact hmain.to₂

/-- **The regrowing chop is primitive recursive on codes.** -/
theorem primrec_chopCC : Primrec₂ chopCC :=
  Primrec.nat_strong_rec chopCC primrec_chopStep chopStep_spec

/-! ### (f) The canonical move, and (g) the battle, on codes -/

/-- `canonStep` on hydra codes. -/
def canonC (n c : ℕ) : ℕ :=
  Option.casesOn (idx? (childC c) (pickIdxC (childC c))) 0 fun f =>
    if f = 0 then nodeC ((childC c).eraseIdx (pickIdxC (childC c))) else chopCC n c

theorem canonC_spec (n c : ℕ) : canonC n c = toCode (canonStep n (ofCode c)) := by
  set ds := (childC c).map ofCode
  have hc : ofCode c = node ds := ofCode_eq c
  have hds : ds.map toCode = childC c := map_toCode_childC c
  unfold canonC chopCC
  rw [← hds, pickIdxC_map]
  simp only [idx?]
  rw [List.getElem?_map, hc, canonStep.eq_1]
  split
  · rename_i hd
    conv_lhs => rw [hd]
    simp only [Option.map_none]
    exact (toCode_eq_zero.mpr rfl).symm
  · rename_i hd
    conv_lhs => rw [hd]
    simp only [Option.map_some, show toCode (node []) = 0 from toCode_eq_zero.mpr rfl, if_true]
    rw [toCode_node, List.eraseIdx_map]
  · rename_i g _ _
    have hd : ds[pickIdx ds]? = some g := ‹_›
    have hg : g = node [] → False := ‹_›
    conv_lhs => rw [hd]
    have hg0 : toCode g ≠ 0 := fun h => hg (toCode_eq_zero.mp h)
    simp only [Option.map_some, hg0, if_false]

theorem primrec_canonC : Primrec₂ canonC := by
  have hD : Primrec fun p : ℕ × ℕ => childC p.2 := primrec_childC.comp Primrec.snd
  have hI : Primrec fun p : ℕ × ℕ => pickIdxC (childC p.2) := primrec_pickIdxC.comp hD
  have hg : Primrec₂ fun (p : ℕ × ℕ) (f : ℕ) =>
      if f = 0 then nodeC ((childC p.2).eraseIdx (pickIdxC (childC p.2))) else chopCC p.1 p.2 :=
    (Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 0))
      (primrec_nodeC.comp (primrec_eraseIdx.comp (hD.comp Primrec.fst) (hI.comp Primrec.fst)))
      (primrec_chopCC.comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.fst))).to₂
  exact (Primrec.option_casesOn (primrec_idx?.comp hD hI) (Primrec.const 0) hg).to₂

/-- The battle on codes: iterate `canonC`, move `k` at turn `k`. -/
def battleC (m N : ℕ) : ℕ := Nat.rec (motive := fun _ => ℕ) m (fun k acc => canonC k acc) N

theorem battleC_spec (m : ℕ) : ∀ N, battleC m N = toCode (battle (ofCode m) N)
  | 0 => (toCode_ofCode m).symm
  | N + 1 => by
    show canonC N (battleC m N) = _
    rw [battleC_spec m N, canonC_spec, ofCode_toCode]
    rfl

theorem primrec_battleC : Primrec₂ battleC :=
  Primrec.nat_rec Primrec.id (primrec_canonC.comp (Primrec.fst.comp Primrec.snd)
    (Primrec.snd.comp Primrec.snd)).to₂

/-- **The canonical battle is computable on codes** (Astra's sufficient target). -/
theorem computable_battle : Computable₂ fun m N => toCode (battle (ofCode m) N) :=
  (primrec_battleC.to_comp).of_eq fun p => battleC_spec p.1 p.2

/-! ### (h) A Σ₁ definition of the battle exists -/

section Existence
open FFL FFL.FirstOrder

/-- The battle's final-code function on argument vectors `![N, m]`. -/
def battleVec (v : List.Vector ℕ 2) : Part ℕ := Part.some (battleC (v.get 1) (v.get 0))

theorem partrec_battleVec : Nat.Partrec' battleVec := by
  apply Nat.Partrec'.of_part
  exact (primrec_battleC.to_comp.comp
    (Primrec.vector_get.to_comp.comp Computable.id (Computable.const 1))
    (Primrec.vector_get.to_comp.comp Computable.id (Computable.const 0))).partrec

/-- **Anti-vacuity for the headline**: some Σ₁ formula defines the canonical battle
pointwise in ℕ, so `pa_not_proves_hydra`'s hypothesis class is inhabited. -/
theorem exists_sigma1_battle_def :
    ∃ φ : Semisentence ℒₒᵣ 2, ℬ[<, ℒₒᵣ].Hierarchy 𝚺 1 φ ∧
      ∀ m N : ℕ, (ℕ ⊧/![N, m] φ) ↔ battle (ofCode m) N = Hydra.leaf := by
  refine ⟨(Arithmetic.codeOfPartrec' battleVec)/[‘0’, #0, #1], ?_, fun m N => ?_⟩
  · exact Bounding.Hierarchy.rew _ (by simp [Arithmetic.codeOfPartrec'])
  · have hspec := Arithmetic.codeOfPartrec'_spec partrec_battleVec (y := 0) (v := ![N, m])
    rw [← toCode_eq_zero, ← battleC_spec]
    simpa [Semiformula.eval_substs, Matrix.comp_vecCons', battleVec, eq_comm] using hspec

end Existence

end GoodsteinPA.Hydra

end
