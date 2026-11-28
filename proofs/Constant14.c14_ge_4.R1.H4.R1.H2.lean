import OMAReductions.R_Constant14_c14_ge_4_R1_H4_R1
import Mathlib.Computability.Halting
import Mathlib.Computability.TuringMachine.ToPartrec
import Mathlib.Tactic

/-!
# Proof of `Constant14.c14_ge_4.R1.H4.R1.H2`

Proves productivity of non-halting for binary Busy Beaver Turing machines under the base-`B`
decoder of `Constant14.c14_ge_4.R1.H4.R1`: no partial recursive function `f : ℕ →. ℕ` whose domain
consists solely of codes of non-halting decoded machines can accept all of them.

Architecture (fixed universal machine + primitive recursive input-prepend compiler):
1. Fix a single `ToPartrec.Code` universal diagonal program `U` computing
   `diag n = (Nat.Partrec.Code.ofNatCode n).eval n`.
2. Compile this single fixed `U` through Mathlib's `PartrecToTM2` -> `TM2to1` -> `TM1to1` ->
   `TM1to0` stack, reindex its finite support to `Fin (K_st + 1)`, and convert `TM0` over `Bool`
   into a single fixed binary Busy Beaver machine `BB_univ : Machine (Fin 2) (Fin (M_st + 1))`.
3. Show that the encoded input tape `inputBits n : List Bool` is primitive recursive, using only
   three fixed bit-block constants and the binary expansion `natBits n`.
4. For any input bitstring `lbs`, prepend `lbs.length + 1` setup states to `BB_univ` to obtain a
   zero-input Busy Beaver machine `prependBB` that halts on the blank tape iff `BB_univ` halts on
   `lbs.map b2f`, iff `(diag n).Dom`.
5. Compute the base-`B` code `compile n` of `prependBB (inputBits n) BB_univ` primitive recursively
   using a single fixed constant table `univTable : List ℕ` for `BB_univ`, prove `dec (compile n)`
   recovers `prependBB`, and finish by Kleene diagonalization at `n₀ = e.encodeCode`.

Credits: Built by `@Narden91`.
-/

namespace C14Ge4H4R1H2

open Turing Turing.BusyBeaver

/- ## Section 1: Fixed Universal Diagonal Program in `ToPartrec.Code` -/

private def diag (n : ℕ) : Part ℕ :=
  (Nat.Partrec.Code.ofNatCode n).eval n

private lemma partrec_diag : Partrec diag :=
  Nat.Partrec.Code.eval_part.comp (Computable.ofNat Nat.Partrec.Code) Computable.id

private lemma exists_univCode :
    ∃ c : Turing.ToPartrec.Code, ∀ n : ℕ, (c.eval [n]).Dom ↔ (diag n).Dom := by
  have h1 : Nat.Partrec' (fun v : List.Vector ℕ 1 => diag v.head) :=
    Nat.Partrec'.part_iff₁.mpr partrec_diag
  obtain ⟨c, hc⟩ := Turing.ToPartrec.Code.exists_code h1
  refine ⟨c, fun n => ?_⟩
  have hn := hc ⟨[n], rfl⟩
  change c.eval [n] = pure <$> diag n at hn
  rw [hn]
  rfl

private noncomputable def univCode : Turing.ToPartrec.Code :=
  exists_univCode.choose

private lemma univCode_dom (n : ℕ) :
    (univCode.eval [n]).Dom ↔ (diag n).Dom :=
  exists_univCode.choose_spec n

/- ## Section 2: Compile Fixed `univCode` to a Finite `TM0` Machine over `Bool` -/

private instance instFintypeK' : Fintype Turing.PartrecToTM2.K' :=
  ⟨{.main, .rev, .aux, .stack}, fun x => by cases x <;> simp⟩

/-- Wrapper around `PartrecToTM2.Λ'` whose `Inhabited` instance points to the initial state of
`univCode`, avoiding typeclass diamonds with `PartrecToTM2.Λ'.instInhabited`. -/
private def Λ2 : Type := Turing.PartrecToTM2.Λ'

private noncomputable instance instInhabitedΛ2 : Inhabited Λ2 :=
  ⟨Turing.PartrecToTM2.trNormal univCode .halt⟩

private abbrev Γ2 (_ : Turing.PartrecToTM2.K') : Type := Turing.PartrecToTM2.Γ'

private def M2 : Λ2 → Turing.TM2.Stmt Γ2 Λ2 (Option Turing.PartrecToTM2.Γ') :=
  Turing.PartrecToTM2.tr

private noncomputable def S2 : Finset Λ2 :=
  Turing.PartrecToTM2.codeSupp univCode .halt

private lemma hS2 : Turing.TM2.Supports M2 S2 :=
  Turing.PartrecToTM2.tr_supports univCode .halt

private lemma M2_init_eq (n : ℕ) :
    (Turing.TM2.init (Γ := Γ2) (Λ := Λ2) (σ := Option Turing.PartrecToTM2.Γ')
      .main (Turing.PartrecToTM2.trList [n])) =
    Turing.PartrecToTM2.init univCode [n] := by
  simp only [Turing.TM2.init, Turing.PartrecToTM2.init]
  congr 1
  funext k
  cases k <;> rfl

private lemma M2_eval_dom (n : ℕ) :
    (Turing.TM2.eval M2 .main (Turing.PartrecToTM2.trList [n])).Dom ↔ (diag n).Dom := by
  have h1 : (Turing.TM2.eval M2 .main (Turing.PartrecToTM2.trList [n])).Dom ↔
      (StateTransition.eval (Turing.TM2.step Turing.PartrecToTM2.tr)
        (Turing.PartrecToTM2.init univCode [n])).Dom := by
    unfold Turing.TM2.eval
    rw [M2_init_eq n]
    rfl
  rw [h1, Turing.PartrecToTM2.tr_eval univCode [n]]
  exact univCode_dom n

private abbrev Γ1 : Type := Turing.TM2to1.Γ' Turing.PartrecToTM2.K' Γ2
private abbrev Λ1 : Type :=
  Turing.TM2to1.Λ' Turing.PartrecToTM2.K' Γ2 Λ2 (Option Turing.PartrecToTM2.Γ')

private def M1 : Λ1 → Turing.TM1.Stmt Γ1 Λ1 (Option Turing.PartrecToTM2.Γ') :=
  Turing.TM2to1.tr M2

private noncomputable def S1 : Finset Λ1 :=
  Turing.TM2to1.trSupp M2 S2

private lemma hS1 : Turing.TM1.Supports M1 S1 :=
  Turing.TM2to1.tr_supports M2 hS2

private lemma M1_eval_dom (n : ℕ) :
    (Turing.TM1.eval M1
      (Turing.TM2to1.trInit .main (Turing.PartrecToTM2.trList [n]))).Dom ↔ (diag n).Dom :=
  (Turing.TM2to1.tr_eval_dom M2 .main (Turing.PartrecToTM2.trList [n])).trans (M2_eval_dom n)

private lemma exists_enc1 :
    ∃ (d : ℕ) (enc : Γ1 → List.Vector Bool d) (dec₁ : List.Vector Bool d → Γ1),
      enc default = List.Vector.replicate d false ∧ ∀ a, dec₁ (enc a) = a :=
  Turing.TM1to1.exists_enc_dec

private noncomputable def d1 : ℕ := exists_enc1.choose
private noncomputable def enc1 : Γ1 → List.Vector Bool d1 := exists_enc1.choose_spec.choose
private noncomputable def dec1 : List.Vector Bool d1 → Γ1 :=
  exists_enc1.choose_spec.choose_spec.choose
private lemma enc1_zero : enc1 default = List.Vector.replicate d1 false :=
  exists_enc1.choose_spec.choose_spec.choose_spec.1
private lemma enc1_dec1 : ∀ a : Γ1, dec1 (enc1 a) = a :=
  exists_enc1.choose_spec.choose_spec.choose_spec.2

private abbrev Λ1b : Type := Turing.TM1to1.Λ' Γ1 Λ1 (Option Turing.PartrecToTM2.Γ')

private noncomputable def M1b : Λ1b → Turing.TM1.Stmt Bool Λ1b (Option Turing.PartrecToTM2.Γ') :=
  Turing.TM1to1.tr enc1 dec1 M1

private noncomputable def S1b : Finset Λ1b :=
  Turing.TM1to1.trSupp M1 S1

private lemma hS1b : Turing.TM1.Supports M1b S1b :=
  Turing.TM1to1.tr_supports enc1 dec1 M1 hS1

private lemma M1b_eval_dom (L : List Γ1) :
    (Turing.TM1.eval M1b (L.flatMap fun x => (enc1 x).toList)).Dom ↔
    (Turing.TM1.eval M1 L).Dom := by
  have hinit : Turing.TM1to1.trCfg enc1 enc1_zero
      (Turing.TM1.init (Γ := Γ1) (Λ := Λ1) (σ := Option Turing.PartrecToTM2.Γ') L) =
      Turing.TM1.init (Γ := Bool) (Λ := Λ1b) (σ := Option Turing.PartrecToTM2.Γ')
        (L.flatMap fun x => (enc1 x).toList) := by
    simp only [Turing.TM1to1.trCfg, Turing.TM1.init, Option.map_some]
    congr 1
    simp only [Turing.Tape.mk₁, Turing.Tape.mk₂, Turing.TM1to1.trTape_mk', Turing.TM1to1.trTape',
      Turing.ListBlank.flatMap_mk, List.flatMap_nil]
  have hresp := Turing.TM1to1.tr_respects dec1 M1 (enc0 := enc1_zero) enc1_dec1
  exact StateTransition.tr_eval_dom hresp hinit

private abbrev Λ0 : Type := Turing.TM1to0.Λ' M1b

private noncomputable def M0 : Turing.TM0.Machine Bool Λ0 :=
  Turing.TM1to0.tr M1b

private noncomputable def S0 : Finset Λ0 :=
  Turing.TM1to0.trStmts M1b S1b

private lemma hS0 : Turing.TM0.Supports M0 (S0 : Set Λ0) :=
  Turing.TM1to0.tr_supports M1b hS1b

private lemma M0_eval_dom (L : List Bool) :
    (Turing.TM0.eval M0 L).Dom ↔ (Turing.TM1.eval M1b L).Dom := by
  unfold M0
  rw [Turing.TM1to0.tr_eval M1b L]

private noncomputable def K_st : ℕ := S0.card - 1

private lemma S0_card_eq : S0.card = K_st + 1 := by
  have hpos : 0 < S0.card := Finset.card_pos.mpr ⟨default, hS0.1⟩
  dsimp only [K_st]
  omega

private noncomputable def eS0 : {x : Λ0 // x ∈ S0} ≃ Fin (K_st + 1) :=
  let e1 : {x : Λ0 // x ∈ S0} ≃ Fin (K_st + 1) := S0.equivFin.trans (finCongr S0_card_eq)
  e1.trans (Equiv.swap (e1 ⟨default, hS0.1⟩) 0)

private lemma eS0_default : eS0 ⟨default, hS0.1⟩ = 0 := by
  dsimp only [eS0, Equiv.trans_apply]
  exact Equiv.swap_apply_left _ _

open scoped Classical in
private noncomputable def g1S0 : Turing.PointedMap Λ0 (Fin (K_st + 1)) :=
  ⟨fun q => if h : q ∈ S0 then eS0 ⟨q, h⟩ else 0, by
    change (if h : default ∈ S0 then eS0 ⟨default, h⟩ else 0) = 0
    rw [dif_pos (Finset.mem_coe.mp hS0.1), eS0_default]⟩

private noncomputable def g2S0 : Fin (K_st + 1) → Λ0 :=
  fun i => (eS0.symm i).val

private def idPM : Turing.PointedMap Bool Bool := ⟨id, rfl⟩

private noncomputable def M_fin : Turing.TM0.Machine Bool (Fin (K_st + 1)) :=
  M0.map idPM idPM g1S0 g2S0

open scoped Classical in
private lemma M_fin_eval_dom (L : List Bool) :
    (Turing.TM0.eval M_fin L).Dom ↔ (Turing.TM0.eval M0 L).Dom := by
  have hg21 : ∀ q ∈ (S0 : Set Λ0), g2S0 (g1S0 q) = q := by
    intro q hq
    change (eS0.symm (if h : q ∈ S0 then eS0 ⟨q, h⟩ else 0)).val = q
    rw [dif_pos (Finset.mem_coe.mp hq), Equiv.symm_apply_apply]
  have hresp := M0.map_respects idPM idPM g1S0 g2S0 hS0 (fun _ => rfl) hg21
  have hinit : (Turing.TM0.init (Γ := Bool) (Λ := Λ0) L).q ∈ (S0 : Set Λ0) ∧
      Turing.TM0.Cfg.map idPM g1S0 (Turing.TM0.init L) = Turing.TM0.init L := by
    refine ⟨hS0.1, ?_⟩
    rw [Turing.TM0.map_init idPM g1S0 L]
    simp [idPM]
  exact StateTransition.tr_eval_dom hresp hinit

/- ## Section 3: Primitive Recursive Encoded Input Tape `inputBits` -/

private def natBits (n : ℕ) : List Bool :=
  if h : n = 0 then [] else (n % 2 == 1) :: natBits (n / 2)

private lemma natBits_zero : natBits 0 = [] := by
  rw [natBits]; simp

private lemma natBits_pos {n : ℕ} (hn : n ≠ 0) :
    natBits n = (n % 2 == 1) :: natBits (n / 2) := by
  rw [natBits, dif_neg hn]

private lemma primrec_natBits : Primrec natBits := by
  let g : Unit → List (List Bool) → Option (List Bool) := fun _ L =>
    let n := L.length
    if n = 0 then some []
    else (L[n / 2]?).map fun tl => (n % 2 == 1) :: tl
  have hg : Primrec₂ g := by
    dsimp only [g]
    have hlen : Primrec (fun p : Unit × List (List Bool) => p.2.length) :=
      Primrec.list_length.comp Primrec.snd
    refine Primrec.ite (Primrec.eq.comp hlen (Primrec.const 0)) (Primrec.const (some [])) ?_
    have hget : Primrec (fun p : Unit × List (List Bool) => p.2[p.2.length / 2]?) :=
      Primrec.list_getElem?.comp Primrec.snd (Primrec.nat_div.comp hlen (Primrec.const 2))
    have hbit : Primrec (fun p : Unit × List (List Bool) => p.2.length % 2 == 1) :=
      Primrec.beq.comp (Primrec.nat_mod.comp hlen (Primrec.const 2)) (Primrec.const 1)
    exact Primrec.option_map hget (Primrec.list_cons.comp (hbit.comp Primrec.fst) Primrec.snd).to₂
  have hrec : Primrec₂ (fun (_ : Unit) (n : ℕ) => natBits n) :=
    Primrec.nat_strong_rec (fun _ n => natBits n) hg fun _ n => by
      dsimp only [g]
      rw [List.length_map, List.length_range]
      by_cases hn : n = 0
      · subst hn; simp [natBits_zero]
      · rw [if_neg hn, natBits_pos hn]
        have hlt : n / 2 < n := Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by decide)
        simp [hlt]
  exact hrec.comp (Primrec.const ()) Primrec.id

private lemma trPosNum_eq (p : PosNum) :
    Turing.PartrecToTM2.trPosNum p =
      (natBits (p : ℕ)).map (fun b => bif b then .bit1 else .bit0) := by
  induction p with
  | one =>
    have h1 : (PosNum.one : ℕ) = 1 := rfl
    rw [h1, natBits_pos (by decide), natBits_zero]
    rfl
  | bit0 p ih =>
    have hp : 0 < (p : ℕ) := PosNum.cast_pos p
    have hval : (p.bit0 : ℕ) = 2 * (p : ℕ) := by simp [two_mul]
    rw [hval, natBits_pos (by omega)]
    have hmod : (2 * (p : ℕ)) % 2 = 0 := by omega
    have hdiv : (2 * (p : ℕ)) / 2 = (p : ℕ) := by omega
    rw [hmod, hdiv]
    simp [Turing.PartrecToTM2.trPosNum, ih]
  | bit1 p ih =>
    have hval : (p.bit1 : ℕ) = 2 * (p : ℕ) + 1 := by simp [two_mul]
    rw [hval, natBits_pos (by omega)]
    have hmod : (2 * (p : ℕ) + 1) % 2 = 1 := by omega
    have hdiv : (2 * (p : ℕ) + 1) / 2 = (p : ℕ) := by omega
    rw [hmod, hdiv]
    simp [Turing.PartrecToTM2.trPosNum, ih]

private lemma trNat_eq (n : ℕ) :
    Turing.PartrecToTM2.trNat n =
      (natBits n).map (fun b => bif b then .bit1 else .bit0) := by
  unfold Turing.PartrecToTM2.trNat
  have hcast : ((n : Num) : ℕ) = n := by simp
  conv_rhs => rw [← hcast]
  cases m : (n : Num) with
  | zero =>
    change Turing.PartrecToTM2.trNum .zero =
      (natBits 0).map (fun b => bif b then .bit1 else .bit0)
    rw [natBits_zero]
    rfl
  | pos p =>
    exact trPosNum_eq p

private def cHead : Γ1 := (true, Function.update (fun _ => none) .main (some .cons))
private def cBit0 : Γ1 := (false, Function.update (fun _ => none) .main (some .bit0))
private def cBit1 : Γ1 := (false, Function.update (fun _ => none) .main (some .bit1))

private noncomputable def headBits : List Bool := (enc1 cHead).toList
private noncomputable def bit0Bits : List Bool := (enc1 cBit0).toList
private noncomputable def bit1Bits : List Bool := (enc1 cBit1).toList

private noncomputable def inputBits (n : ℕ) : List Bool :=
  headBits ++ (natBits n).reverse.flatMap (fun b => bif b then bit1Bits else bit0Bits)

private def mkCell (a : Turing.PartrecToTM2.Γ') : Γ1 :=
  (false, Function.update (fun _ => none) .main (some a))

private lemma trInit_append_cons (L : List Turing.PartrecToTM2.Γ') :
    Turing.TM2to1.trInit (Γ := Γ2) .main (L ++ [.cons]) =
      cHead :: L.reverse.map mkCell := by
  unfold Turing.TM2to1.trInit cHead mkCell
  rw [List.reverse_append, List.reverse_singleton, List.singleton_append]
  rfl

private lemma inputBits_eq (n : ℕ) :
    inputBits n =
      (Turing.TM2to1.trInit .main (Turing.PartrecToTM2.trList [n])).flatMap
        (fun x => (enc1 x).toList) := by
  have hlist : Turing.PartrecToTM2.trList [n] =
      Turing.PartrecToTM2.trNat n ++ [.cons] := by
    simp [Turing.PartrecToTM2.trList]
  rw [hlist, trInit_append_cons, List.flatMap_cons, trNat_eq n, List.map_reverse,
    List.map_map, ← List.map_reverse, List.flatMap_map]
  simp only [inputBits, headBits, bit0Bits, bit1Bits, cBit0, cBit1]
  congr 1
  refine List.flatMap_congr fun b _ => ?_
  cases b <;> rfl

private lemma primrec_inputBits : Primrec inputBits :=
  Primrec.list_append.comp (Primrec.const headBits)
    (Primrec.list_flatMap (Primrec.list_reverse.comp primrec_natBits)
      ((Primrec.cond Primrec.id (Primrec.const bit1Bits) (Primrec.const bit0Bits)).comp
        Primrec.snd).to₂)

private lemma M_fin_inputBits_dom (n : ℕ) :
    (Turing.TM0.eval M_fin (inputBits n)).Dom ↔ (diag n).Dom := by
  rw [M_fin_eval_dom, M0_eval_dom, inputBits_eq, M1b_eval_dom, M1_eval_dom]

/- ## Section 4: Convert `TM0` over `Bool` to Busy Beaver Machine over `Fin 2` -/

private def b2f : Turing.PointedMap Bool (Fin 2) :=
  ⟨fun b => if b then 1 else 0, rfl⟩

private def f2b : Turing.PointedMap (Fin 2) Bool :=
  ⟨fun a => a.val == 1, rfl⟩

private lemma f2b_b2f (b : Bool) : f2b (b2f b) = b := by
  cases b <;> rfl

private noncomputable def M_st : ℕ := 2 * K_st + 1

private def tm0ToBB {K : ℕ} (M : Turing.TM0.Machine Bool (Fin (K + 1))) :
    BusyBeaver.Machine (Fin 2) (Fin (2 * K + 1 + 1)) :=
  fun q a =>
    if hq : q.val < K + 1 then
      match M ⟨q.val, hq⟩ (f2b a) with
      | none => none
      | some (q', .move d) =>
        some (some ⟨q'.val, by omega⟩, Stmt.write a d)
      | some (q', .write c) =>
        some (some ⟨(K + 1) + q'.val, by omega⟩, Stmt.write (b2f c) .right)
    else
      some (some ⟨q.val - (K + 1), by omega⟩, Stmt.write a .left)

private def trCfgBB {K : ℕ} :
    Turing.TM0.Cfg Bool (Fin (K + 1)) → BusyBeaver.Cfg (Fin 2) (Fin (2 * K + 1 + 1))
  | ⟨q, T⟩ => ⟨some ⟨q.val, by omega⟩, T.map b2f⟩

private lemma tm0ToBB_respects {K : ℕ} (M : Turing.TM0.Machine Bool (Fin (K + 1))) :
    StateTransition.Respects (Turing.TM0.step M) (BusyBeaver.Machine.step (tm0ToBB M))
      (fun c₁ c₂ => trCfgBB c₁ = c₂) := by
  rw [StateTransition.fun_respects]
  rintro ⟨q, T⟩
  simp only [Turing.TM0.step, trCfgBB]
  have hhead : f2b (T.map b2f).head = T.head := by
    rw [Turing.Tape.map_fst, f2b_b2f]
  cases hM : M q T.head with
  | none =>
    simp only [StateTransition.FRespects, Option.map_none, BusyBeaver.Machine.step, tm0ToBB,
      dif_pos q.isLt, hhead, hM]
  | some out =>
    rcases out with ⟨q', st⟩
    cases st with
    | move d =>
      simp only [StateTransition.FRespects, Option.map_some]
      refine Relation.TransGen.single ?_
      change BusyBeaver.Machine.step (tm0ToBB M) ⟨some ⟨q.val, _⟩, T.map b2f⟩ =
        some ⟨some ⟨q'.val, _⟩, (T.move d).map b2f⟩
      simp only [BusyBeaver.Machine.step, tm0ToBB, dif_pos q.isLt, hhead, hM, Option.map_some]
      rw [Turing.Tape.write_self, Turing.Tape.map_move]
    | write c =>
      simp only [StateTransition.FRespects, Option.map_some]
      let mid : BusyBeaver.Cfg (Fin 2) (Fin (2 * K + 1 + 1)) :=
        ⟨some ⟨(K + 1) + q'.val, by omega⟩, ((T.map b2f).write (b2f c)).move .right⟩
      have h1 : mid ∈ BusyBeaver.Machine.step (tm0ToBB M) ⟨some ⟨q.val, by omega⟩, T.map b2f⟩ := by
        change BusyBeaver.Machine.step (tm0ToBB M) ⟨some ⟨q.val, _⟩, T.map b2f⟩ = some mid
        simp only [BusyBeaver.Machine.step, tm0ToBB, dif_pos q.isLt, hhead, hM, Option.map_some, mid]
      have hnotlt : ¬ ((K + 1) + q'.val < K + 1) := by omega
      have hsub : (K + 1) + q'.val - (K + 1) = q'.val := by omega
      have h2 : trCfgBB ⟨q', T.write c⟩ ∈ BusyBeaver.Machine.step (tm0ToBB M) mid := by
        change BusyBeaver.Machine.step (tm0ToBB M) mid = some ⟨some ⟨q'.val, _⟩, (T.write c).map b2f⟩
        simp only [BusyBeaver.Machine.step, tm0ToBB, mid, dif_neg hnotlt, Option.map_some]
        congr 1
        refine BusyBeaver.Cfg.ext ?_ ?_
        · simp [hsub]
        · rw [Turing.Tape.write_self, Turing.Tape.move_right_left, Turing.Tape.map_write]
      exact Relation.TransGen.head h1 (Relation.TransGen.single h2)

private lemma tm0ToBB_eval_dom {K : ℕ} (M : Turing.TM0.Machine Bool (Fin (K + 1)))
    (L : List Bool) :
    ((tm0ToBB M).eval (L.map b2f)).Dom ↔ (Turing.TM0.eval M L).Dom := by
  have hinit : trCfgBB (Turing.TM0.init (Γ := Bool) (Λ := Fin (K + 1)) L) =
      BusyBeaver.Machine.init (L.map b2f) := by
    simp only [trCfgBB, Turing.TM0.init, BusyBeaver.Machine.init, Turing.Tape.map_mk₁]
    rfl
  exact StateTransition.tr_eval_dom (tm0ToBB_respects M) hinit

private noncomputable def BB_univ : BusyBeaver.Machine (Fin 2) (Fin (M_st + 1)) :=
  tm0ToBB M_fin

private lemma BB_univ_inputBits_dom (n : ℕ) :
    (BB_univ.eval ((inputBits n).map b2f)).Dom ↔ (diag n).Dom :=
  (tm0ToBB_eval_dom M_fin (inputBits n)).trans (M_fin_inputBits_dom n)

/- ## Section 5: Prepend Input Bitstring `lbs` to a Busy Beaver Machine -/

private def prependBB {m : ℕ} (lbs : List Bool) (B : BusyBeaver.Machine (Fin 2) (Fin (m + 1))) :
    BusyBeaver.Machine (Fin 2) (Fin (lbs.length + m + 1 + 1)) :=
  fun q a =>
    if h1 : q.val < lbs.length then
      some (some ⟨q.val + 1, by omega⟩, Stmt.write (b2f (lbs.getD (lbs.length - 1 - q.val) false)) .left)
    else if h2 : q.val = lbs.length then
      some (some ⟨lbs.length + 1, by omega⟩, Stmt.write 0 .right)
    else
      match B ⟨q.val - (lbs.length + 1), by omega⟩ a with
      | none => none
      | some (qOpt, st) =>
        some (qOpt.map (fun q' => ⟨lbs.length + 1 + q'.val, by omega⟩), st)

private lemma listBlank_cons_zero_default :
    (Turing.ListBlank.cons (0 : Fin 2) default) = default := by
  refine Turing.ListBlank.ext fun i => ?_
  cases i <;> rfl

private lemma listBlank_mk_zero :
    Turing.ListBlank.mk [(0 : Fin 2)] = default := by
  change Turing.ListBlank.cons (0 : Fin 2) (Turing.ListBlank.mk []) = default
  exact listBlank_cons_zero_default

private lemma prependBB_reaches_stage {m : ℕ} (lbs : List Bool)
    (B : BusyBeaver.Machine (Fin 2) (Fin (m + 1))) :
    ∀ i (hi : i ≤ lbs.length),
      StateTransition.Reaches (prependBB lbs B).step (BusyBeaver.Machine.init [])
        ⟨some ⟨i, by omega⟩,
          Turing.Tape.mk' default
            (Turing.ListBlank.mk (0 :: (lbs.drop (lbs.length - i)).map b2f))⟩ := by
  intro i hi
  induction i with
  | zero =>
    have hdrop : lbs.drop (lbs.length - 0) = [] := by simp
    have hcfg : (⟨some ⟨0, by omega⟩,
        Turing.Tape.mk' default
          (Turing.ListBlank.mk (0 :: (lbs.drop (lbs.length - 0)).map b2f))⟩ :
        BusyBeaver.Cfg (Fin 2) (Fin (lbs.length + m + 1 + 1))) =
        BusyBeaver.Machine.init [] := by
      refine BusyBeaver.Cfg.ext rfl ?_
      rw [hdrop, List.map_nil, listBlank_mk_zero]
      rfl
    rw [hcfg]
    exact Relation.ReflTransGen.refl
  | succ i ih =>
    have hi_lt : i < lbs.length := by omega
    have hprev := ih (by omega)
    refine hprev.tail ?_
    change (prependBB lbs B).step
        ⟨some ⟨i, by omega⟩,
          Turing.Tape.mk' default
            (Turing.ListBlank.mk (0 :: (lbs.drop (lbs.length - i)).map b2f))⟩ =
      some ⟨some ⟨i + 1, by omega⟩,
        Turing.Tape.mk' default
          (Turing.ListBlank.mk (0 :: (lbs.drop (lbs.length - (i + 1))).map b2f))⟩
    simp only [BusyBeaver.Machine.step, prependBB, dif_pos hi_lt, Option.map_some]
    congr 1
    refine BusyBeaver.Cfg.ext rfl ?_
    have hidx : lbs.length - 1 - i < lbs.length := by omega
    have hget : lbs.getD (lbs.length - 1 - i) false = lbs[lbs.length - 1 - i] := by
      simp [List.getD_eq_getElem?_getD, hidx]
    have hdrop_eq : lbs[lbs.length - 1 - i] :: lbs.drop (lbs.length - i) =
        lbs.drop (lbs.length - (i + 1)) := by
      have hsucc : lbs.length - 1 - i + 1 = lbs.length - i := by omega
      have hsub : lbs.length - (i + 1) = lbs.length - 1 - i := by omega
      rw [hsub, ← hsucc, List.cons_getElem_drop_succ]
    have htail_def : (default : Turing.ListBlank (Fin 2)).tail = default := rfl
    have hhead_def : (default : Turing.ListBlank (Fin 2)).head = 0 := rfl
    rw [hget, Turing.Tape.write_mk', Turing.Tape.move_left_mk', htail_def, hhead_def,
      ← Turing.ListBlank.cons_mk, Turing.ListBlank.tail_cons,
      Turing.ListBlank.cons_mk, Turing.ListBlank.cons_mk, ← List.map_cons, hdrop_eq]

private def shiftCfg {m : ℕ} (lbs : List Bool) :
    BusyBeaver.Cfg (Fin 2) (Fin (m + 1)) →
      BusyBeaver.Cfg (Fin 2) (Fin (lbs.length + m + 1 + 1))
  | ⟨qOpt, T⟩ => ⟨qOpt.map (fun q => ⟨lbs.length + 1 + q.val, by omega⟩), T⟩

private lemma prependBB_reaches_start {m : ℕ} (lbs : List Bool)
    (B : BusyBeaver.Machine (Fin 2) (Fin (m + 1))) :
    StateTransition.Reaches (prependBB lbs B).step (BusyBeaver.Machine.init [])
      (shiftCfg lbs (BusyBeaver.Machine.init (lbs.map b2f))) := by
  have hstage := prependBB_reaches_stage lbs B lbs.length (le_refl _)
  refine hstage.tail ?_
  change (prependBB lbs B).step
      ⟨some ⟨lbs.length, by omega⟩,
        Turing.Tape.mk' default
          (Turing.ListBlank.mk (0 :: (lbs.drop (lbs.length - lbs.length)).map b2f))⟩ =
    some (shiftCfg lbs (BusyBeaver.Machine.init (lbs.map b2f)))
  have hnotlt : ¬ (lbs.length < lbs.length) := by omega
  simp only [BusyBeaver.Machine.step, prependBB, dif_neg hnotlt, dite_true, Option.map_some,
    shiftCfg, BusyBeaver.Machine.init]
  congr 1
  refine BusyBeaver.Cfg.ext ?_ ?_
  · simp
  · rw [Nat.sub_self, List.drop_zero, Turing.Tape.write_mk', Turing.Tape.move_right_mk',
      ← Turing.ListBlank.cons_mk, Turing.ListBlank.tail_cons, Turing.ListBlank.head_cons,
      Turing.ListBlank.tail_cons, listBlank_cons_zero_default]
    rfl

private lemma prependBB_respects_shift {m : ℕ} (lbs : List Bool)
    (B : BusyBeaver.Machine (Fin 2) (Fin (m + 1))) :
    StateTransition.Respects B.step (prependBB lbs B).step
      (fun c₁ c₂ => shiftCfg lbs c₁ = c₂) := by
  rw [StateTransition.fun_respects]
  rintro ⟨qOpt, T⟩
  cases qOpt with
  | none => rfl
  | some q =>
    simp only [BusyBeaver.Machine.step, shiftCfg, Option.map_some]
    have hnot1 : ¬ (lbs.length + 1 + q.val < lbs.length) := by omega
    have hnot2 : ¬ (lbs.length + 1 + q.val = lbs.length) := by omega
    have hsub : (⟨lbs.length + 1 + q.val - (lbs.length + 1), by omega⟩ : Fin (m + 1)) = q := by
      ext; dsimp only; omega
    cases hB : B q T.head with
    | none =>
      simp only [StateTransition.FRespects, Option.map_none, BusyBeaver.Machine.step, prependBB,
        dif_neg hnot1, dif_neg hnot2, hsub, hB]
    | some out =>
      rcases out with ⟨qNext, ⟨sym, d⟩⟩
      simp only [StateTransition.FRespects, Option.map_some]
      refine Relation.TransGen.single ?_
      change (prependBB lbs B).step ⟨some ⟨lbs.length + 1 + q.val, _⟩, T⟩ =
        some ⟨qNext.map (fun q' => ⟨lbs.length + 1 + q'.val, _⟩), (T.write sym).move d⟩
      simp only [BusyBeaver.Machine.step, prependBB, dif_neg hnot1, dif_neg hnot2, hsub, hB,
        Option.map_some]

private lemma prependBB_isHalting_iff {m : ℕ} (lbs : List Bool)
    (B : BusyBeaver.Machine (Fin 2) (Fin (m + 1))) :
    (prependBB lbs B).IsHalting ↔ (B.eval (lbs.map b2f)).Dom := by
  constructor
  · rintro ⟨h⟩
    have h1 : (StateTransition.eval (prependBB lbs B).step (BusyBeaver.Machine.init [])).Dom := h
    rw [StateTransition.reaches_eval (prependBB_reaches_start lbs B)] at h1
    exact (StateTransition.tr_eval_dom (prependBB_respects_shift lbs B) rfl).mp h1
  · intro h
    refine ⟨?_⟩
    change (StateTransition.eval (prependBB lbs B).step (BusyBeaver.Machine.init [])).Dom
    rw [StateTransition.reaches_eval (prependBB_reaches_start lbs B)]
    exact (StateTransition.tr_eval_dom (prependBB_respects_shift lbs B) rfl).mpr h

/- ## Section 6: Base-`B` Table Encoder `compile` and `Primrec compile` -/

private def decAux (m t : ℕ) : BusyBeaver.Machine (Fin 2) (Fin (m + 1)) :=
  let B := 4 * (m + 2) + 1
  fun q a =>
    let v := (t / B ^ (2 * q.val + a.val)) % B
    if v = 0 then none
    else
      let w := v - 1
      let s := w / 4
      let b : Fin 2 := ⟨(w / 2) % 2, Nat.mod_lt _ (by decide)⟩
      let d : Dir := if w % 2 = 0 then .left else .right
      some (if h : s < m + 1 then some ⟨s, h⟩ else none, Stmt.write b d)

private def dec (c : ℕ) : (m : ℕ) × BusyBeaver.Machine (Fin 2) (Fin (m + 1)) :=
  ⟨(Nat.unpair c).1, decAux (Nat.unpair c).1 (Nat.unpair c).2⟩

private lemma isHalting_of_sigma_eq
    {p q : (m : ℕ) × BusyBeaver.Machine (Fin 2) (Fin (m + 1))} (h : p = q) :
    p.2.IsHalting ↔ q.2.IsHalting := by
  subst h; rfl

private def polySum (B : ℕ) (d : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => polySum B d k + d k * B ^ k

private lemma polySum_lt {B : ℕ} (d : ℕ → ℕ) :
    ∀ k, (∀ j < k, d j < B) → polySum B d k < B ^ k := by
  intro k
  induction k with
  | zero =>
    intro _; simp [polySum]
  | succ k ih =>
    intro hd
    have h1 : polySum B d k < B ^ k := ih (fun j hj => hd j (by omega))
    have h2 : d k < B := hd k (Nat.lt_succ_self k)
    have h3 : (d k + 1) * B ^ k ≤ B * B ^ k := Nat.mul_le_mul_right (B ^ k) h2
    calc
      polySum B d (k + 1) = polySum B d k + d k * B ^ k := rfl
      _ < B ^ k + d k * B ^ k := Nat.add_lt_add_right h1 _
      _ = (d k + 1) * B ^ k := by ring
      _ ≤ B * B ^ k := h3
      _ = B ^ (k + 1) := by rw [Nat.pow_succ, mul_comm]

private lemma polySum_div_mod {B : ℕ} (hB : 0 < B) (d : ℕ → ℕ) :
    ∀ k, (∀ j < k, d j < B) → ∀ i < k, (polySum B d k / B ^ i) % B = d i := by
  intro k
  induction k with
  | zero =>
    intro _ i hi; omega
  | succ k ih =>
    intro hd i hi
    have hlt_k : ∀ j < k, d j < B := fun j hj => hd j (by omega)
    have hdk : d k < B := hd k (Nat.lt_succ_self k)
    by_cases hik : i = k
    · subst hik
      have hpos : 0 < B ^ i := Nat.pow_pos hB
      have hsum_lt : polySum B d i < B ^ i := polySum_lt d i hlt_k
      change ((polySum B d i + d i * B ^ i) / B ^ i) % B = d i
      rw [Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt hsum_lt, zero_add, Nat.mod_eq_of_lt hdk]
    · have hi_lt : i < k := by omega
      have hpos : 0 < B ^ i := Nat.pow_pos hB
      have hpow : B ^ k = (B * B ^ (k - i - 1)) * B ^ i := by
        have hexp : 1 + (k - i - 1) + i = k := by omega
        calc
          B ^ k = B ^ (1 + (k - i - 1) + i) := by rw [hexp]
          _ = B ^ (1 + (k - i - 1)) * B ^ i := by rw [Nat.pow_add]
          _ = (B * B ^ (k - i - 1)) * B ^ i := by rw [Nat.pow_add, Nat.pow_one]
      change ((polySum B d k + d k * B ^ k) / B ^ i) % B = d i
      rw [hpow, ← mul_assoc, Nat.add_mul_div_right _ _ hpos]
      have hmulB : d k * (B * B ^ (k - i - 1)) = (d k * B ^ (k - i - 1)) * B := by ring
      rw [hmulB, Nat.add_mul_mod_self_right]
      exact ih hlt_k i hi_lt

private noncomputable def univBaseDigit (j : ℕ) : ℕ :=
  if hq : j / 2 < M_st + 1 then
    match BB_univ ⟨j / 2, hq⟩ ⟨j % 2, Nat.mod_lt _ (by decide)⟩ with
    | none => 0
    | some (qOpt, ⟨b, d⟩) =>
      let s0 := match qOpt with
        | some q' => 1 + q'.val
        | none => M_st + 2
      let dBit := match d with
        | .left => 0
        | .right => 1
      1 + 4 * s0 + 2 * b.val + dBit
  else 0

private noncomputable def univTable : List ℕ :=
  (List.range (2 * (M_st + 1))).map univBaseDigit

private noncomputable def digitOf (lbs : List Bool) (idx : ℕ) : ℕ :=
  let r := lbs.length
  let q := idx / 2
  if q < r then
    let b := if lbs.getD (r - 1 - q) false then 1 else 0
    1 + 4 * (q + 1) + 2 * b
  else if q = r then
    4 * (r + 1) + 2
  else
    let base := univTable.getD (idx - 2 * (r + 1)) 0
    if base = 0 then 0 else base + 4 * r

private noncomputable def compileList (lbs : List Bool) : ℕ :=
  let r := lbs.length
  let m := r + M_st + 1
  let B := 4 * (m + 2) + 1
  Nat.pair m (polySum B (digitOf lbs) (2 * (m + 1)))

private noncomputable def compile (n : ℕ) : ℕ :=
  compileList (inputBits n)

private lemma digitOf_lt (lbs : List Bool) {idx : ℕ}
    (hidx : idx < 2 * (lbs.length + M_st + 1 + 1)) :
    digitOf lbs idx < 4 * (lbs.length + M_st + 1 + 2) + 1 := by
  dsimp only [digitOf]
  by_cases h1 : idx / 2 < lbs.length
  · rw [if_pos h1]
    cases lbs.getD (lbs.length - 1 - idx / 2) false <;> simp <;> omega
  · rw [if_neg h1]
    by_cases h2 : idx / 2 = lbs.length
    · rw [if_pos h2]; omega
    · rw [if_neg h2]
      by_cases h3 : univTable.getD (idx - 2 * (lbs.length + 1)) 0 = 0
      · rw [if_pos h3]; omega
      · rw [if_neg h3]
        have hj : idx - 2 * (lbs.length + 1) < 2 * (M_st + 1) := by omega
        have hget : univTable.getD (idx - 2 * (lbs.length + 1)) 0 =
            univBaseDigit (idx - 2 * (lbs.length + 1)) := by
          simp [univTable, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj]
        rw [hget]
        unfold univBaseDigit
        have hq : (idx - 2 * (lbs.length + 1)) / 2 < M_st + 1 := by omega
        rw [dif_pos hq]
        cases htr : BB_univ ⟨(idx - 2 * (lbs.length + 1)) / 2, hq⟩
            ⟨(idx - 2 * (lbs.length + 1)) % 2, Nat.mod_lt _ (by decide)⟩ with
        | none => dsimp only; omega
        | some out =>
          rcases out with ⟨qOpt, ⟨b, d⟩⟩
          have hb : b.val < 2 := b.isLt
          cases qOpt with
          | none => cases d <;> dsimp only <;> omega
          | some q' =>
            have hq' : q'.val < M_st + 1 := q'.isLt
            cases d <;> dsimp only <;> omega

private def decodeDigit (m v : ℕ) : Option (Option (Fin (m + 1)) × BusyBeaver.Stmt (Fin 2)) :=
  if v = 0 then none
  else
    let w := v - 1
    let s := w / 4
    let b : Fin 2 := ⟨(w / 2) % 2, Nat.mod_lt _ (by decide)⟩
    let d : Dir := if w % 2 = 0 then .left else .right
    some (if h : s < m + 1 then some ⟨s, h⟩ else none, Stmt.write b d)

private lemma decodeDigit_eq {m : ℕ} {qOpt : Option (Fin (m + 1))} {b : Fin 2} {d : Dir} :
    let s := match qOpt with | some q' => q'.val | none => m + 1
    let dBit := match d with | .left => 0 | .right => 1
    decodeDigit m (1 + 4 * s + 2 * b.val + dBit) = some (qOpt, Stmt.write b d) := by
  intro s dBit
  let v := 1 + 4 * s + 2 * b.val + dBit
  have hb : b.val < 2 := b.isLt
  have hdBit : dBit < 2 := by dsimp only [dBit]; cases d <;> decide
  have hv_ne : v ≠ 0 := by dsimp only [v]; omega
  have hs_div : (v - 1) / 4 = s := by dsimp only [v]; omega
  have hb_eq : (⟨((v - 1) / 2) % 2, Nat.mod_lt _ (by decide)⟩ : Fin 2) = b := by
    ext; dsimp only [v]; omega
  have hd_eq : (if (v - 1) % 2 = 0 then Dir.left else Dir.right) = d := by
    cases d
    · have h0 : (v - 1) % 2 = 0 := by dsimp only [v, dBit]; omega
      rw [if_pos h0]
    · have h1 : (v - 1) % 2 ≠ 0 := by dsimp only [v, dBit]; omega
      rw [if_neg h1]
  have hq_eq : (if h : (v - 1) / 4 < m + 1 then some ⟨(v - 1) / 4, h⟩ else none) = qOpt := by
    cases qOpt with
    | none =>
      have hnot : ¬ ((v - 1) / 4 < m + 1) := by rw [hs_div]; dsimp only [s]; omega
      rw [dif_neg hnot]
    | some q' =>
      have hlt : (v - 1) / 4 < m + 1 := by rw [hs_div]; exact q'.isLt
      rw [dif_pos hlt]
      congr 1
      ext
      exact hs_div
  change decodeDigit m v = some (qOpt, Stmt.write b d)
  unfold decodeDigit
  rw [if_neg hv_ne]
  dsimp only
  rw [hq_eq, hb_eq, hd_eq]

private lemma decAux_compileList (lbs : List Bool) :
    decAux (lbs.length + M_st + 1)
      (polySum (4 * (lbs.length + M_st + 1 + 2) + 1) (digitOf lbs)
        (2 * (lbs.length + M_st + 1 + 1))) =
    prependBB lbs BB_univ := by
  funext q a
  let r := lbs.length
  let m := r + M_st + 1
  let B := 4 * (m + 2) + 1
  have hB : 0 < B := by dsimp only [B]; omega
  have hidx : 2 * q.val + a.val < 2 * (m + 1) := by
    have hq := q.isLt; have ha := a.isLt; dsimp only [m, r]; omega
  have hv :
      (polySum B (digitOf lbs) (2 * (m + 1)) / B ^ (2 * q.val + a.val)) % B =
      digitOf lbs (2 * q.val + a.val) :=
    polySum_div_mod hB (digitOf lbs) (2 * (m + 1)) (fun j hj => digitOf_lt lbs hj) _ hidx
  have hqdiv : (2 * q.val + a.val) / 2 = q.val := by have ha := a.isLt; omega
  change decodeDigit m
      ((polySum B (digitOf lbs) (2 * (m + 1)) / B ^ (2 * q.val + a.val)) % B) =
    prependBB lbs BB_univ q a
  rw [hv]
  dsimp only [digitOf, prependBB]
  rw [hqdiv]
  by_cases h1 : q.val < r
  · rw [if_pos h1, dif_pos h1]
    have hb : (if lbs.getD (r - 1 - q.val) false then 1 else 0) =
        (b2f (lbs.getD (r - 1 - q.val) false)).val := by
      cases lbs.getD (r - 1 - q.val) false <;> rfl
    rw [hb]
    simpa only [add_zero] using
      (@decodeDigit_eq m (some ⟨q.val + 1, by omega⟩)
        (b2f (lbs.getD (r - 1 - q.val) false)) .left)
  · rw [if_neg h1, dif_neg h1]
    by_cases h2 : q.val = r
    · rw [if_pos h2, dif_pos h2]
      have h42 : 4 * (r + 1) + 2 = 1 + 4 * (r + 1) + 2 * (0 : Fin 2).val + 1 := by
        simp only [Fin.val_zero]; omega
      rw [h42]
      exact @decodeDigit_eq m (some ⟨r + 1, by omega⟩) 0 .right
    · rw [if_neg h2, dif_neg h2]
      have hj_lt : 2 * q.val + a.val - 2 * (r + 1) < 2 * (M_st + 1) := by
        have hq := q.isLt; have ha := a.isLt; dsimp only [r] at *; omega
      have hget : univTable.getD (2 * q.val + a.val - 2 * (r + 1)) 0 =
          univBaseDigit (2 * q.val + a.val - 2 * (r + 1)) := by
        simp [univTable, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj_lt]
      have hq_sub : (2 * q.val + a.val - 2 * (r + 1)) / 2 = q.val - (r + 1) := by
        have ha := a.isLt; omega
      have ha_sub : (2 * q.val + a.val - 2 * (r + 1)) % 2 = a.val := by
        have ha := a.isLt; omega
      have hq_lt : (2 * q.val + a.val - 2 * (r + 1)) / 2 < M_st + 1 := by omega
      have hfin_q : (⟨(2 * q.val + a.val - 2 * (r + 1)) / 2, hq_lt⟩ : Fin (M_st + 1)) =
          ⟨q.val - (r + 1), by omega⟩ := by ext; exact hq_sub
      have hfin_a : (⟨(2 * q.val + a.val - 2 * (r + 1)) % 2, Nat.mod_lt _ (by decide)⟩ : Fin 2) =
          a := by ext; exact ha_sub
      rw [hget]
      unfold univBaseDigit
      rw [dif_pos hq_lt, hfin_q, hfin_a]
      cases htr : BB_univ ⟨q.val - (r + 1), by omega⟩ a with
      | none => simp [decodeDigit]
      | some out =>
        rcases out with ⟨qOpt, ⟨b, d⟩⟩
        cases qOpt with
        | none =>
          cases d <;> dsimp only
          · rw [if_neg (by omega)]
            have heq : 1 + 4 * (M_st + 2) + 2 * b.val + 0 + 4 * r =
                1 + 4 * (m + 1) + 2 * b.val + 0 := by dsimp only [m, r]; omega
            rw [heq]
            exact @decodeDigit_eq m none b .left
          · rw [if_neg (by omega)]
            have heq : 1 + 4 * (M_st + 2) + 2 * b.val + 1 + 4 * r =
                1 + 4 * (m + 1) + 2 * b.val + 1 := by dsimp only [m, r]; omega
            rw [heq]
            exact @decodeDigit_eq m none b .right
        | some q' =>
          cases d <;> dsimp only
          · rw [if_neg (by omega)]
            have heq : 1 + 4 * (1 + q'.val) + 2 * b.val + 0 + 4 * r =
                1 + 4 * (r + 1 + q'.val) + 2 * b.val + 0 := by omega
            rw [heq]
            exact @decodeDigit_eq m (some ⟨r + 1 + q'.val, by omega⟩) b .left
          · rw [if_neg (by omega)]
            have heq : 1 + 4 * (1 + q'.val) + 2 * b.val + 1 + 4 * r =
                1 + 4 * (r + 1 + q'.val) + 2 * b.val + 1 := by omega
            rw [heq]
            exact @decodeDigit_eq m (some ⟨r + 1 + q'.val, by omega⟩) b .right

private lemma dec_compileList_eq (lbs : List Bool) :
    dec (compileList lbs) = ⟨lbs.length + M_st + 1, prependBB lbs BB_univ⟩ := by
  dsimp only [dec, compileList]
  rw [Nat.unpair_pair, decAux_compileList lbs]

private lemma dec_compile_isHalting_iff (n : ℕ) :
    (dec (compile n)).2.IsHalting ↔ (diag n).Dom := by
  rw [compile, isHalting_of_sigma_eq (dec_compileList_eq (inputBits n)),
    prependBB_isHalting_iff, BB_univ_inputBits_dom]

private lemma primrec_pow : Primrec₂ ((· ^ ·) : ℕ → ℕ → ℕ) :=
  (Primrec.nat_rec (Primrec.const 1)
    (Primrec.nat_mul.comp (Primrec.snd.comp Primrec.snd) Primrec.fst).to₂).of_eq
    fun b k => by
      dsimp only
      induction k with
      | zero => rfl
      | succ k ih => rw [Nat.pow_succ, ← ih]

private lemma primrec_digitOf : Primrec₂ digitOf := by
  have hr : Primrec (fun p : List Bool × ℕ => p.1.length) :=
    Primrec.list_length.comp Primrec.fst
  have hq : Primrec (fun p : List Bool × ℕ => p.2 / 2) :=
    Primrec.nat_div.comp Primrec.snd (Primrec.const 2)
  have hb : Primrec (fun p : List Bool × ℕ =>
      if p.1.getD (p.1.length - 1 - p.2 / 2) false then 1 else 0) :=
    Primrec.ite
      (Primrec.eq.comp
        ((Primrec.list_getD false).comp Primrec.fst
          (Primrec.nat_sub.comp (Primrec.nat_sub.comp hr (Primrec.const 1)) hq))
        (Primrec.const true))
      (Primrec.const 1) (Primrec.const 0)
  have hbr1 : Primrec (fun p : List Bool × ℕ =>
      1 + 4 * (p.2 / 2 + 1) + 2 * (if p.1.getD (p.1.length - 1 - p.2 / 2) false then 1 else 0)) :=
    Primrec.nat_add.comp
      (Primrec.nat_add.comp (Primrec.const 1)
        (Primrec.nat_mul.comp (Primrec.const 4) (Primrec.nat_add.comp hq (Primrec.const 1))))
      (Primrec.nat_mul.comp (Primrec.const 2) hb)
  have hbr2 : Primrec (fun p : List Bool × ℕ => 4 * (p.1.length + 1) + 2) :=
    Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.const 4) (Primrec.nat_add.comp hr (Primrec.const 1)))
      (Primrec.const 2)
  have hbase : Primrec (fun p : List Bool × ℕ =>
      univTable.getD (p.2 - 2 * (p.1.length + 1)) 0) :=
    (Primrec.list_getD 0).comp (Primrec.const univTable)
      (Primrec.nat_sub.comp Primrec.snd
        (Primrec.nat_mul.comp (Primrec.const 2) (Primrec.nat_add.comp hr (Primrec.const 1))))
  have hbr3 : Primrec (fun p : List Bool × ℕ =>
      let base := univTable.getD (p.2 - 2 * (p.1.length + 1)) 0
      if base = 0 then 0 else base + 4 * p.1.length) :=
    Primrec.ite (Primrec.eq.comp hbase (Primrec.const 0)) (Primrec.const 0)
      (Primrec.nat_add.comp hbase (Primrec.nat_mul.comp (Primrec.const 4) hr))
  refine (Primrec.ite (Primrec.nat_lt.comp hq hr) hbr1
    (Primrec.ite (Primrec.eq.comp hq hr) hbr2 hbr3)).of_eq ?_
  rintro ⟨lbs, idx⟩
  rfl

private lemma primrec_compileList : Primrec compileList := by
  have hr : Primrec (fun lbs : List Bool => lbs.length) := Primrec.list_length
  have hm : Primrec (fun lbs : List Bool => lbs.length + M_st + 1) :=
    Primrec.nat_add.comp (Primrec.nat_add.comp hr (Primrec.const M_st)) (Primrec.const 1)
  have hB : Primrec (fun lbs : List Bool => 4 * (lbs.length + M_st + 1 + 2) + 1) :=
    Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.const 4) (Primrec.nat_add.comp hm (Primrec.const 2)))
      (Primrec.const 1)
  have hK : Primrec (fun lbs : List Bool => 2 * (lbs.length + M_st + 1 + 1)) :=
    Primrec.nat_mul.comp (Primrec.const 2) (Primrec.nat_add.comp hm (Primrec.const 1))
  have hstep : Primrec₂ (fun (lbs : List Bool) (p : ℕ × ℕ) =>
      p.2 + digitOf lbs p.1 * (4 * (lbs.length + M_st + 1 + 2) + 1) ^ p.1) :=
    Primrec.nat_add.comp (Primrec.snd.comp Primrec.snd)
      (Primrec.nat_mul.comp
        (primrec_digitOf.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
        (primrec_pow.comp (hB.comp Primrec.fst) (Primrec.fst.comp Primrec.snd)))
  have hpoly : Primrec (fun lbs : List Bool =>
      polySum (4 * (lbs.length + M_st + 1 + 2) + 1) (digitOf lbs)
        (2 * (lbs.length + M_st + 1 + 1))) :=
    (Primrec.nat_rec' hK (Primrec.const 0) hstep).of_eq fun lbs => by
      dsimp only
      generalize 2 * (lbs.length + M_st + 1 + 1) = k
      induction k with
      | zero => rfl
      | succ k ih =>
        dsimp only [polySum]
        rw [← ih]
  exact Primrec₂.natPair.comp hm hpoly

private lemma primrec_compile : Primrec compile :=
  primrec_compileList.comp primrec_inputBits

/- ## Section 7: Diagonal Contradiction -/

theorem main_proof : OMA.R_Constant14_c14_ge_4_R1_H4_R1.H2 := by
  intro f hf hsound
  by_contra hnone
  push Not at hnone
  have hiff : ∀ c : ℕ, (f c).Dom ↔ ¬ (dec c).2.IsHalting :=
    fun c => ⟨hsound c, hnone c⟩
  let g : ℕ →. ℕ := fun n => f (compile n)
  have hg : Nat.Partrec g :=
    Partrec.nat_iff.mp ((Partrec.nat_iff.mpr hf).comp primrec_compile.to_comp)
  obtain ⟨e, he⟩ := Nat.Partrec.Code.exists_code.1 hg
  let n0 : ℕ := e.encodeCode
  have hdiag : diag n0 = g n0 := by
    dsimp only [diag, n0]
    have hof : Nat.Partrec.Code.ofNatCode e.encodeCode = e :=
      Denumerable.ofNat_encode e
    rw [hof, he]
  have h1 : (g n0).Dom ↔ (f (compile n0)).Dom := Iff.rfl
  have h2 : (f (compile n0)).Dom ↔ ¬ (dec (compile n0)).2.IsHalting := hiff (compile n0)
  have h3 : (dec (compile n0)).2.IsHalting ↔ (diag n0).Dom := dec_compile_isHalting_iff n0
  have h4 : (diag n0).Dom ↔ (g n0).Dom := by rw [hdiag]
  exact iff_not_self (h1.trans (h2.trans (not_congr (h3.trans h4))))

end C14Ge4H4R1H2

theorem OMA.solution : OMA.R_Constant14_c14_ge_4_R1_H4_R1.H2 :=
  C14Ge4H4R1H2.main_proof
