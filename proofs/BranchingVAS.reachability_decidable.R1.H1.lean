import OMAReductions.R_BranchingVAS_reachability_decidable_R1
import Mathlib

/-!
# Proof of `BranchingVAS.reachability_decidable.R1.H1`

We prove that checking a separating semilinear inductive invariant for a Branching Vector
Addition System (BVAS) is uniformly computable, by implementing a primitive-recursive
Cooper quantifier elimination procedure over flat positive DNF formulas in Presburger
arithmetic `Th(ℤ, +, 0, 1, <, (m ∣ ·))` and compiling the four invariant clauses into
closed DNF queries.
-/

namespace BVASH1

open BranchingVAS
open scoped BigOperators

private abbrev Input := Σ d : ℕ, Bvas d × (Fin d → ℤ)
private abbrev RawInput := ℕ × List (List ℤ) × List (List ℤ) × List (List ℤ) × List ℤ
private abbrev SemilinearCode := List (List ℕ × List (List ℕ))

/- ### Section 1: Primitive-Recursive `ℤ` and `List` Primitives -/

private lemma encode_int_ofNat (m : ℕ) : Encodable.encode (Int.ofNat m) = 2 * m := rfl

private lemma encode_int_negSucc (n : ℕ) : Encodable.encode (Int.negSucc n) = 2 * n + 1 := rfl

private lemma bodd_two_mul (k : ℕ) : (2 * k).bodd = false := by
  rw [Nat.bodd_mul]; rfl

private lemma bodd_two_mul_add_one (k : ℕ) : (2 * k + 1).bodd = true := by
  rw [Nat.bodd_succ, bodd_two_mul]; rfl

private lemma div2_two_mul (k : ℕ) : (2 * k).div2 = k := by
  rw [Nat.div2_val]; omega

private lemma div2_two_mul_add_one (k : ℕ) : (2 * k + 1).div2 = k := by
  rw [Nat.div2_val]; omega

private lemma primrec_int_ofNat : Primrec (fun n : ℕ => (n : ℤ)) :=
  Primrec.encode_iff.mp Primrec.nat_double

private lemma primrec_int_natAbs : Primrec Int.natAbs := by
  have h : Primrec fun z : ℤ =>
      cond (Encodable.encode z).bodd ((Encodable.encode z).div2 + 1) (Encodable.encode z).div2 :=
    Primrec.cond (Primrec.nat_bodd.comp Primrec.encode)
      (Primrec.succ.comp (Primrec.nat_div2.comp Primrec.encode))
      (Primrec.nat_div2.comp Primrec.encode)
  refine h.of_eq fun z => ?_
  cases z with
  | ofNat m =>
    simp only [encode_int_ofNat, bodd_two_mul, div2_two_mul, Bool.cond_false]
    rfl
  | negSucc n =>
    simp only [encode_int_negSucc, bodd_two_mul_add_one, div2_two_mul_add_one, Bool.cond_true,
      Int.natAbs_negSucc]

private lemma primrec_int_neg : Primrec (Neg.neg : ℤ → ℤ) := by
  rw [← Primrec.encode_iff]
  let e : ℤ → ℕ := Encodable.encode
  let b : ℤ → Bool := fun z => (e z).bodd
  let k : ℤ → ℕ := fun z => (e z).div2
  have he : Primrec e := Primrec.encode
  have hb : Primrec b := Primrec.nat_bodd.comp he
  have hk : Primrec k := Primrec.nat_div2.comp he
  have hpos : Primrec fun z : ℤ =>
      if k z = 0 then 0 else 2 * (k z - 1) + 1 :=
    Primrec.ite (Primrec.eq.comp hk (Primrec.const 0))
      (Primrec.const 0)
      (Primrec.nat_double_succ.comp (Primrec.nat_sub.comp hk (Primrec.const 1)))
  have hcomb : Primrec fun z : ℤ =>
      cond (b z) (2 * (k z + 1)) (if k z = 0 then 0 else 2 * (k z - 1) + 1) :=
    Primrec.cond hb (Primrec.nat_double.comp (Primrec.succ.comp hk)) hpos
  refine hcomb.of_eq fun z => ?_
  cases z with
  | ofNat m =>
    cases m with
    | zero =>
      simp only [b, k, e, encode_int_ofNat, bodd_two_mul, div2_two_mul, Bool.cond_false,
        ↓reduceIte]
      rfl
    | succ m =>
      simp only [b, k, e, encode_int_ofNat, bodd_two_mul, div2_two_mul, Bool.cond_false,
        Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
      have hneg : -Int.ofNat (m + 1) = Int.negSucc m := rfl
      rw [hneg, encode_int_negSucc]
  | negSucc n =>
    simp only [b, k, e, encode_int_negSucc, bodd_two_mul_add_one, div2_two_mul_add_one,
      Bool.cond_true]
    have hneg : -Int.negSucc n = Int.ofNat (n + 1) := rfl
    rw [hneg, encode_int_ofNat]

private lemma primrec_int_nonneg : Primrec (fun z : ℤ => decide ((0 : ℤ) ≤ z)) := by
  have h : ∀ z : ℤ, decide ((0 : ℤ) ≤ z) = !(Encodable.encode z).bodd := by
    rintro (m | n)
    · rw [encode_int_ofNat, bodd_two_mul]
      simp [Int.ofNat_eq_natCast]
    · rw [encode_int_negSucc, bodd_two_mul_add_one]
      simp [show ¬ ((0 : ℤ) ≤ Int.negSucc n) by omega]
  exact (Primrec.not.comp (Primrec.nat_bodd.comp Primrec.encode)).of_eq fun z => (h z).symm

private lemma primrec_int_pos : Primrec (fun z : ℤ => decide ((0 : ℤ) < z)) := by
  have h : ∀ z : ℤ, decide ((0 : ℤ) < z) = (decide (0 < Encodable.encode z) && !(Encodable.encode z).bodd) := by
    rintro (m | n)
    · rw [encode_int_ofNat, bodd_two_mul]
      cases m with
      | zero => simp
      | succ m => simp [Int.ofNat_eq_natCast]
    · rw [encode_int_negSucc, bodd_two_mul_add_one]
      simp [show ¬ ((0 : ℤ) < Int.negSucc n) by omega]
  have hp : Primrec fun z : ℤ => decide (0 < Encodable.encode z) && !(Encodable.encode z).bodd :=
    Primrec.and.comp
      ((Primrec.nat_lt.comp (Primrec.const 0) Primrec.encode).decide)
      (Primrec.not.comp (Primrec.nat_bodd.comp Primrec.encode))
  exact hp.of_eq fun z => (h z).symm

private lemma primrec_int_add : Primrec₂ ((· + ·) : ℤ → ℤ → ℤ) := by
  rw [Primrec₂, ← Primrec.encode_iff]
  let e1 : ℤ × ℤ → ℕ := fun p => Encodable.encode p.1
  let e2 : ℤ × ℤ → ℕ := fun p => Encodable.encode p.2
  let b1 : ℤ × ℤ → Bool := fun p => (e1 p).bodd
  let b2 : ℤ × ℤ → Bool := fun p => (e2 p).bodd
  let x1 : ℤ × ℤ → ℕ := fun p => (e1 p).div2
  let x2 : ℤ × ℤ → ℕ := fun p => (e2 p).div2
  have he1 : Primrec e1 := Primrec.encode.comp Primrec.fst
  have he2 : Primrec e2 := Primrec.encode.comp Primrec.snd
  have hb1 : Primrec b1 := Primrec.nat_bodd.comp he1
  have hb2 : Primrec b2 := Primrec.nat_bodd.comp he2
  have hx1 : Primrec x1 := Primrec.nat_div2.comp he1
  have hx2 : Primrec x2 := Primrec.nat_div2.comp he2
  have hff : Primrec fun p => 2 * (x1 p + x2 p) :=
    Primrec.nat_double.comp (Primrec.nat_add.comp hx1 hx2)
  have htt : Primrec fun p => 2 * (x1 p + x2 p + 1) + 1 :=
    Primrec.nat_double_succ.comp (Primrec.succ.comp (Primrec.nat_add.comp hx1 hx2))
  have hft : Primrec fun p =>
      if x2 p < x1 p then 2 * (x1 p - (x2 p + 1)) else 2 * (x2 p - x1 p) + 1 :=
    Primrec.ite (Primrec.nat_lt.comp hx2 hx1)
      (Primrec.nat_double.comp (Primrec.nat_sub.comp hx1 (Primrec.succ.comp hx2)))
      (Primrec.nat_double_succ.comp (Primrec.nat_sub.comp hx2 hx1))
  have htf : Primrec fun p =>
      if x1 p < x2 p then 2 * (x2 p - (x1 p + 1)) else 2 * (x1 p - x2 p) + 1 :=
    Primrec.ite (Primrec.nat_lt.comp hx1 hx2)
      (Primrec.nat_double.comp (Primrec.nat_sub.comp hx2 (Primrec.succ.comp hx1)))
      (Primrec.nat_double_succ.comp (Primrec.nat_sub.comp hx1 hx2))
  have hcomb : Primrec fun p : ℤ × ℤ =>
      cond (b1 p)
        (cond (b2 p) (2 * (x1 p + x2 p + 1) + 1)
          (if x1 p < x2 p then 2 * (x2 p - (x1 p + 1)) else 2 * (x1 p - x2 p) + 1))
        (cond (b2 p)
          (if x2 p < x1 p then 2 * (x1 p - (x2 p + 1)) else 2 * (x2 p - x1 p) + 1)
          (2 * (x1 p + x2 p))) :=
    Primrec.cond hb1 (Primrec.cond hb2 htt htf) (Primrec.cond hb2 hft hff)
  refine hcomb.of_eq fun ⟨z1, z2⟩ => ?_
  cases z1 with
  | ofNat m1 =>
    cases z2 with
    | ofNat m2 =>
      have heq : Int.ofNat m1 + Int.ofNat m2 = Int.ofNat (m1 + m2) := rfl
      rw [heq]
      simp only [b1, b2, x1, x2, e1, e2, encode_int_ofNat, bodd_two_mul, div2_two_mul,
        Bool.cond_false]
    | negSucc n2 =>
      simp only [b1, b2, x1, x2, e1, e2, encode_int_ofNat, encode_int_negSucc,
        bodd_two_mul, bodd_two_mul_add_one, div2_two_mul, div2_two_mul_add_one,
        Bool.cond_false, Bool.cond_true]
      split_ifs with h
      · have heq : Int.ofNat m1 + Int.negSucc n2 = Int.ofNat (m1 - (n2 + 1)) := by
          simp only [Int.ofNat_eq_natCast]; omega
        rw [heq, encode_int_ofNat]
      · have heq : Int.ofNat m1 + Int.negSucc n2 = Int.negSucc (n2 - m1) := by
          simp only [Int.ofNat_eq_natCast]; omega
        rw [heq, encode_int_negSucc]
  | negSucc n1 =>
    cases z2 with
    | ofNat m2 =>
      simp only [b1, b2, x1, x2, e1, e2, encode_int_ofNat, encode_int_negSucc,
        bodd_two_mul, bodd_two_mul_add_one, div2_two_mul, div2_two_mul_add_one,
        Bool.cond_false, Bool.cond_true]
      split_ifs with h
      · have heq : Int.negSucc n1 + Int.ofNat m2 = Int.ofNat (m2 - (n1 + 1)) := by
          simp only [Int.ofNat_eq_natCast]; omega
        rw [heq, encode_int_ofNat]
      · have heq : Int.negSucc n1 + Int.ofNat m2 = Int.negSucc (n1 - m2) := by
          simp only [Int.ofNat_eq_natCast]; omega
        rw [heq, encode_int_negSucc]
    | negSucc n2 =>
      have heq : Int.negSucc n1 + Int.negSucc n2 = Int.negSucc (n1 + n2 + 1) := by omega
      rw [heq]
      simp only [b1, b2, x1, x2, e1, e2, encode_int_negSucc,
        bodd_two_mul_add_one, div2_two_mul_add_one, Bool.cond_true]

private lemma primrec_int_sub : Primrec₂ ((· - ·) : ℤ → ℤ → ℤ) :=
  (primrec_int_add.comp Primrec.fst (primrec_int_neg.comp Primrec.snd)).to₂.of_eq fun a b =>
    (sub_eq_add_neg a b).symm

private lemma primrec_int_mul : Primrec₂ ((· * ·) : ℤ → ℤ → ℤ) := by
  rw [Primrec₂, ← Primrec.encode_iff]
  let mag : ℤ × ℤ → ℕ := fun p => p.1.natAbs * p.2.natAbs
  let diffSign : ℤ × ℤ → Bool := fun p =>
    decide ((Encodable.encode p.1).bodd ≠ (Encodable.encode p.2).bodd)
  have hmag : Primrec mag :=
    Primrec.nat_mul.comp (primrec_int_natAbs.comp Primrec.fst) (primrec_int_natAbs.comp Primrec.snd)
  have hdiff : Primrec diffSign :=
    (Primrec.eq.comp (Primrec.nat_bodd.comp (Primrec.encode.comp Primrec.fst))
      (Primrec.nat_bodd.comp (Primrec.encode.comp Primrec.snd))).not.decide
  have hcomb : Primrec fun p : ℤ × ℤ =>
      if mag p = 0 then 0
      else cond (diffSign p) (2 * (mag p - 1) + 1) (2 * mag p) :=
    Primrec.ite (Primrec.eq.comp hmag (Primrec.const 0))
      (Primrec.const 0)
      (Primrec.cond hdiff
        (Primrec.nat_double_succ.comp (Primrec.nat_sub.comp hmag (Primrec.const 1)))
        (Primrec.nat_double.comp hmag))
  refine hcomb.of_eq fun ⟨z1, z2⟩ => ?_
  have hna : ∀ m : ℕ, (Int.ofNat m).natAbs = m := fun _ => rfl
  cases z1 with
  | ofNat m1 =>
    cases z2 with
    | ofNat m2 =>
      have heq : Int.ofNat m1 * Int.ofNat m2 = Int.ofNat (m1 * m2) := rfl
      rw [heq]
      simp only [mag, diffSign, hna, encode_int_ofNat, bodd_two_mul, ne_eq,
        not_true_eq_false, decide_false, Bool.cond_false]
      split_ifs with h
      · rw [h]
      · rfl
    | negSucc n2 =>
      simp only [mag, diffSign, hna, Int.natAbs_negSucc, encode_int_ofNat,
        encode_int_negSucc, bodd_two_mul, bodd_two_mul_add_one, ne_eq, Bool.false_eq_true,
        not_false_eq_true, decide_true, Bool.cond_true]
      split_ifs with h
      · have hm1 : m1 = 0 := by nlinarith
        subst hm1
        have hz : Int.ofNat 0 * Int.negSucc n2 = Int.ofNat 0 := by simp
        rw [hz, encode_int_ofNat]
      · have heq : Int.ofNat m1 * Int.negSucc n2 = Int.negSucc (m1 * (n2 + 1) - 1) := by
          have hpos : 1 ≤ m1 * (n2 + 1) := Nat.pos_of_ne_zero h
          have : Int.ofNat m1 * Int.negSucc n2 = -((m1 * (n2 + 1) : ℕ) : ℤ) := by
            simp only [Int.ofNat_eq_natCast, Int.negSucc_eq]
            push_cast
            ring
          rw [this, Int.negSucc_eq]
          omega
        rw [heq, encode_int_negSucc]
  | negSucc n1 =>
    cases z2 with
    | ofNat m2 =>
      simp only [mag, diffSign, hna, Int.natAbs_negSucc, encode_int_ofNat,
        encode_int_negSucc, bodd_two_mul, bodd_two_mul_add_one, ne_eq, Bool.true_eq_false,
        not_false_eq_true, decide_true, Bool.cond_true]
      split_ifs with h
      · have hm2 : m2 = 0 := by nlinarith
        subst hm2
        have hz : Int.negSucc n1 * Int.ofNat 0 = Int.ofNat 0 := by simp
        rw [hz, encode_int_ofNat]
      · have heq : Int.negSucc n1 * Int.ofNat m2 = Int.negSucc ((n1 + 1) * m2 - 1) := by
          have hpos : 1 ≤ (n1 + 1) * m2 := Nat.pos_of_ne_zero h
          have : Int.negSucc n1 * Int.ofNat m2 = -(((n1 + 1) * m2 : ℕ) : ℤ) := by
            simp only [Int.ofNat_eq_natCast, Int.negSucc_eq]
            push_cast
            ring
          rw [this, Int.negSucc_eq]
          omega
        rw [heq, encode_int_negSucc]
    | negSucc n2 =>
      simp only [mag, diffSign, Int.natAbs_negSucc, encode_int_negSucc, bodd_two_mul_add_one,
        ne_eq, not_true_eq_false, decide_false, Bool.cond_false]
      have hne : (n1 + 1) * (n2 + 1) ≠ 0 := by positivity
      simp only [hne, ↓reduceIte]
      have heq : Int.negSucc n1 * Int.negSucc n2 = Int.ofNat ((n1 + 1) * (n2 + 1)) := by
        simp only [Int.negSucc_eq, Int.ofNat_eq_natCast]
        push_cast
        ring
      rw [heq, encode_int_ofNat]

private lemma primrec_int_dvd_nat : Primrec₂ (fun (m : ℕ) (z : ℤ) => decide ((m : ℤ) ∣ z)) := by
  have h : Primrec fun p : ℕ × ℤ => decide (p.2.natAbs % p.1 = 0) :=
    (Primrec.eq.comp (Primrec.nat_mod.comp (primrec_int_natAbs.comp Primrec.snd) Primrec.fst)
      (Primrec.const 0)).decide
  refine h.to₂.of_eq fun m z => ?_
  apply decide_eq_decide.mpr
  rw [← Nat.dvd_iff_mod_eq_zero, Int.natCast_dvd]

private lemma primrec_list_isEmpty {α : Type*} [Primcodable α] :
    Primrec (fun l : List α => l.isEmpty) :=
  (Primrec.list_casesOn Primrec.id (Primrec.const true) (Primrec.const false).to₂).of_eq fun l => by
    cases l <;> rfl

private lemma list_filter_eq_foldr {α : Type*} (p : α → Bool) (l : List α) :
    l.filter p = l.foldr (fun x acc => cond (p x) (x :: acc) acc) [] := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.filter_cons, List.foldr_cons, ih]
    cases p x <;> rfl

private lemma primrec_list_filter_bool {α β : Type*} [Primcodable α] [Primcodable β]
    {f : α → List β} {p : α → β → Bool} (hf : Primrec f) (hp : Primrec₂ p) :
    Primrec fun a => (f a).filter (p a) := by
  have h := Primrec.list_foldr hf (Primrec.const ([] : List β))
    (Primrec.cond (hp.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
      (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂
  exact h.of_eq fun a => (list_filter_eq_foldr (p a) (f a)).symm

private lemma list_all_eq_foldr {α : Type*} (p : α → Bool) (l : List α) :
    l.all p = l.foldr (fun x acc => p x && acc) true := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [List.all_cons, ih]

private lemma list_any_eq_foldr {α : Type*} (p : α → Bool) (l : List α) :
    l.any p = l.foldr (fun x acc => p x || acc) false := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [List.any_cons, ih]

private lemma primrec_list_all {α β : Type*} [Primcodable α] [Primcodable β]
    {f : α → List β} {p : α → β → Bool} (hf : Primrec f) (hp : Primrec₂ p) :
    Primrec fun a => (f a).all (p a) := by
  have h := Primrec.list_foldr hf (Primrec.const true)
    (Primrec.and.comp (hp.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂
  exact h.of_eq fun a => (list_all_eq_foldr (p a) (f a)).symm

private lemma primrec_list_any {α β : Type*} [Primcodable α] [Primcodable β]
    {f : α → List β} {p : α → β → Bool} (hf : Primrec f) (hp : Primrec₂ p) :
    Primrec fun a => (f a).any (p a) := by
  have h := Primrec.list_foldr hf (Primrec.const false)
    (Primrec.or.comp (hp.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂
  exact h.of_eq fun a => (list_any_eq_foldr (p a) (f a)).symm

private def vecAdd (a b : List ℤ) : List ℤ :=
  (List.range (max a.length b.length)).map fun i => a.getD i 0 + b.getD i 0

private lemma primrec_vecAdd : Primrec₂ vecAdd :=
  (Primrec.list_map
    (Primrec.list_range.comp
      (Primrec.nat_max.comp (Primrec.list_length.comp Primrec.fst)
        (Primrec.list_length.comp Primrec.snd)))
    (primrec_int_add.comp
      ((Primrec.list_getD (0 : ℤ)).comp (Primrec.fst.comp Primrec.fst) Primrec.snd)
      ((Primrec.list_getD (0 : ℤ)).comp (Primrec.snd.comp Primrec.fst) Primrec.snd)).to₂).to₂

private lemma primrec_vecNeg : Primrec (fun a : List ℤ => a.map (- ·)) :=
  Primrec.list_map Primrec.id (primrec_int_neg.comp Primrec.snd).to₂

private lemma primrec_vecScale : Primrec₂ (fun (k : ℤ) (a : List ℤ) => a.map (k * ·)) :=
  (Primrec.list_map Primrec.snd
    (primrec_int_mul.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂).to₂

private def nonnegList (l : List ℤ) : Bool :=
  l.all fun z => decide ((0 : ℤ) ≤ z)

private lemma primrec_nonnegList : Primrec nonnegList :=
  primrec_list_all Primrec.id (primrec_int_nonneg.comp Primrec.snd).to₂

private lemma nonnegList_ofFn_iff {d : ℕ} (v : Fin d → ℤ) :
    nonnegList (List.ofFn v) = true ↔ 0 ≤ v := by
  simp only [nonnegList, List.all_eq_true, decide_eq_true_eq]
  constructor
  · intro h i
    exact h (v i) (by simp)
  · intro h z hz
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hz
    exact h i

/- ### Section 2: Flat Positive DNF Formulas over `ℤ` -/

private abbrev Atom := ℕ × ℤ × List ℤ
private abbrev Conj := List Atom
private abbrev DNF := List Conj

private def dot : List ℤ → (ℕ → ℤ) → ℤ
  | [], _ => 0
  | a :: as, env => a * env 0 + dot as (fun i => env (i + 1))

private def consEnv (x : ℤ) (env : ℕ → ℤ) : ℕ → ℤ
  | 0 => x
  | i + 1 => env i

private def prependFin {n : ℕ} (xs : Fin n → ℤ) (env : ℕ → ℤ) (i : ℕ) : ℤ :=
  if h : i < n then xs ⟨i, h⟩ else env (i - n)

private lemma dot_zero_env (a : List ℤ) : dot a (fun _ => 0) = 0 := by
  induction a with
  | nil => rfl
  | cons x xs ih => simp [dot, ih]

private lemma dot_eq_sum_range_length (a : List ℤ) (env : ℕ → ℤ) :
    dot a env = ∑ i ∈ Finset.range a.length, a.getD i 0 * env i := by
  induction a generalizing env with
  | nil => simp [dot]
  | cons x xs ih =>
    simp only [dot, List.length_cons, Finset.sum_range_succ', List.getD_cons_zero,
      List.getD_cons_succ, ih]
    ring

private lemma dot_eq_sum_range (a : List ℤ) (env : ℕ → ℤ) {n : ℕ} (hn : a.length ≤ n) :
    dot a env = ∑ i ∈ Finset.range n, a.getD i 0 * env i := by
  rw [dot_eq_sum_range_length]
  refine Finset.sum_subset (Finset.range_mono hn) fun i _ hi => ?_
  have hge : a.length ≤ i := by simpa [Finset.mem_range] using hi
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge]

private lemma dot_consEnv (a : List ℤ) (x : ℤ) (env : ℕ → ℤ) :
    dot a (consEnv x env) = a.getD 0 0 * x + dot a.tail env := by
  cases a with
  | nil => simp [dot]
  | cons a0 as => simp [dot, consEnv]

private lemma dot_vecNeg (a : List ℤ) (env : ℕ → ℤ) :
    dot (a.map (- ·)) env = - dot a env := by
  induction a generalizing env with
  | nil => simp [dot]
  | cons x xs ih =>
    simp only [List.map_cons, dot, ih]
    ring

private lemma dot_vecScale (k : ℤ) (a : List ℤ) (env : ℕ → ℤ) :
    dot (a.map (k * ·)) env = k * dot a env := by
  induction a generalizing env with
  | nil => simp [dot]
  | cons x xs ih =>
    simp only [List.map_cons, dot, ih]
    ring

private lemma dot_vecAdd (a b : List ℤ) (env : ℕ → ℤ) :
    dot (vecAdd a b) env = dot a env + dot b env := by
  let n := max a.length b.length
  have hlen : (vecAdd a b).length = n := by simp [vecAdd, n]
  rw [dot_eq_sum_range_length (vecAdd a b) env, hlen,
    dot_eq_sum_range a env (le_max_left _ _),
    dot_eq_sum_range b env (le_max_right _ _), ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hin : i < n := Finset.mem_range.mp hi
  have hget : (vecAdd a b).getD i 0 = a.getD i 0 + b.getD i 0 := by
    simp [vecAdd, n, List.getD_eq_getElem?_getD, hin]
  rw [hget]
  ring

private lemma dot_append (a b : List ℤ) (env : ℕ → ℤ) :
    dot (a ++ b) env = dot a env + dot b (fun i => env (i + a.length)) := by
  induction a generalizing env with
  | nil => simp [dot]
  | cons x xs ih =>
    simp only [List.cons_append, dot, List.length_cons, ih]
    have hshift : (fun i => env (i + xs.length + 1)) = (fun i => env (i + (xs.length + 1))) := rfl
    rw [hshift]
    ring

private lemma consEnv_prependFin {n : ℕ} (x : ℤ) (xs : Fin n → ℤ) (env : ℕ → ℤ) :
    consEnv x (prependFin xs env) = prependFin (Fin.cons x xs) env := by
  funext i
  cases i with
  | zero => simp [consEnv, prependFin]
  | succ k =>
    simp only [consEnv, prependFin]
    split_ifs with h1 h2 h2
    · rfl
    · omega
    · omega
    · congr 1; omega

private lemma prependFin_zero (xs : Fin 0 → ℤ) (env : ℕ → ℤ) :
    prependFin xs env = env := by
  funext i
  simp [prependFin]

private lemma prependFin_shift {n : ℕ} (xs : Fin n → ℤ) (env : ℕ → ℤ) :
    (fun i => prependFin xs env (i + n)) = env := by
  funext i
  have hnot : ¬ (i + n < n) := by omega
  simp only [prependFin, hnot, ↓reduceDIte, Nat.add_sub_cancel]

private lemma dot_prependFin_eq_sum {n : ℕ} (a : List ℤ) (ha : a.length = n)
    (xs : Fin n → ℤ) (env : ℕ → ℤ) :
    dot a (prependFin xs env) = ∑ j : Fin n, xs j * a.getD j.1 0 := by
  rw [dot_eq_sum_range_length, ha]
  let f : ℕ → ℤ := fun i => if h : i < n then xs ⟨i, h⟩ * a.getD i 0 else 0
  have hR : ∑ j : Fin n, xs j * a.getD j.1 0 = ∑ j : Fin n, f j.1 :=
    Finset.sum_congr rfl fun j _ => by simp [f, j.2]
  rw [hR, Fin.sum_univ_eq_sum_range f n]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hin : i < n := Finset.mem_range.mp hi
  simp only [f, prependFin, hin, ↓reduceDIte]
  ring

private def evalAtom (env : ℕ → ℤ) : Atom → Prop
  | (0, c, a) => (0 : ℤ) < c + dot a env
  | (m + 1, c, a) => ((m + 1 : ℕ) : ℤ) ∣ c + dot a env

private lemma evalAtom_of_pos {k : ℕ} (hk : 0 < k) (env : ℕ → ℤ) (c : ℤ) (a : List ℤ) :
    evalAtom env (k, c, a) ↔ ((k : ℕ) : ℤ) ∣ c + dot a env := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  rfl

private def evalConj (env : ℕ → ℤ) (C : Conj) : Prop :=
  ∀ A ∈ C, evalAtom env A

private def evalDNF (env : ℕ → ℤ) (D : DNF) : Prop :=
  ∃ C ∈ D, evalConj env C

private def evalClosedAtom (A : Atom) : Bool :=
  if A.1 = 0 then decide ((0 : ℤ) < A.2.1)
  else decide ((A.1 : ℤ) ∣ A.2.1)

private def evalClosedConj (C : Conj) : Bool :=
  C.all evalClosedAtom

private def evalClosedDNF (D : DNF) : Bool :=
  D.any evalClosedConj

private lemma primrec_evalClosedAtom : Primrec evalClosedAtom :=
  Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 0))
    (primrec_int_pos.comp (Primrec.fst.comp Primrec.snd))
    (primrec_int_dvd_nat.comp Primrec.fst (Primrec.fst.comp Primrec.snd))

private lemma primrec_evalClosedConj : Primrec evalClosedConj :=
  primrec_list_all Primrec.id (primrec_evalClosedAtom.comp Primrec.snd).to₂

private lemma primrec_evalClosedDNF : Primrec evalClosedDNF :=
  primrec_list_any Primrec.id (primrec_evalClosedConj.comp Primrec.snd).to₂

private lemma evalClosedAtom_eq_true_iff (A : Atom) :
    evalClosedAtom A = true ↔ evalAtom (fun _ => 0) A := by
  rcases A with ⟨tag, c, a⟩
  cases tag with
  | zero =>
    simp [evalClosedAtom, evalAtom, dot_zero_env]
  | succ m =>
    simp [evalClosedAtom, evalAtom, dot_zero_env]

private lemma evalClosedConj_eq_true_iff (C : Conj) :
    evalClosedConj C = true ↔ evalConj (fun _ => 0) C := by
  simp only [evalClosedConj, List.all_eq_true, evalConj, evalClosedAtom_eq_true_iff]

private lemma evalClosedDNF_eq_true_iff (D : DNF) :
    evalClosedDNF D = true ↔ evalDNF (fun _ => 0) D := by
  simp only [evalClosedDNF, List.any_eq_true, evalDNF, evalClosedConj_eq_true_iff]

private def andDNF (D1 D2 : DNF) : DNF :=
  D1.flatMap fun C1 => D2.map fun C2 => C1 ++ C2

private lemma primrec_andDNF : Primrec₂ andDNF :=
  (Primrec.list_flatMap Primrec.fst
    (Primrec.list_map (Primrec.snd.comp Primrec.fst)
      (Primrec.list_append.comp (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂).to₂).to₂

private lemma evalDNF_singleton (env : ℕ → ℤ) (C : Conj) :
    evalDNF env [C] ↔ evalConj env C := by
  simp [evalDNF]

private lemma evalDNF_andDNF (env : ℕ → ℤ) (D1 D2 : DNF) :
    evalDNF env (andDNF D1 D2) ↔ evalDNF env D1 ∧ evalDNF env D2 := by
  simp only [evalDNF, andDNF, List.mem_flatMap, List.mem_map, evalConj]
  constructor
  · rintro ⟨_, ⟨C1, hC1, C2, hC2, rfl⟩, h⟩
    exact ⟨⟨C1, hC1, fun A hA => h A (List.mem_append_left C2 hA)⟩,
      ⟨C2, hC2, fun A hA => h A (List.mem_append_right C1 hA)⟩⟩
  · rintro ⟨⟨C1, hC1, h1⟩, ⟨C2, hC2, h2⟩⟩
    refine ⟨C1 ++ C2, ⟨C1, hC1, C2, hC2, rfl⟩, fun A hA => ?_⟩
    rcases List.mem_append.mp hA with hA1 | hA2
    · exact h1 A hA1
    · exact h2 A hA2

private def negAtom (A : Atom) : DNF :=
  match A.1 with
  | 0 => [[(0, 1 - A.2.1, A.2.2.map (- ·))]]
  | m + 1 => (List.range m).map fun r => [(m + 1, A.2.1 + ((r + 1 : ℕ) : ℤ), A.2.2)]

private def negConj (C : Conj) : DNF :=
  C.flatMap negAtom

private def negDNF (D : DNF) : DNF :=
  D.foldr (fun C acc => andDNF (negConj C) acc) [[]]

private lemma primrec_negAtom : Primrec negAtom := by
  have hzero : Primrec fun A : Atom =>
      [[((0 : ℕ), 1 - A.2.1, A.2.2.map (- ·))]] :=
    Primrec.list_cons.comp
      (Primrec.list_cons.comp
        (Primrec.pair (Primrec.const 0)
          (Primrec.pair (primrec_int_sub.comp (Primrec.const 1) (Primrec.fst.comp Primrec.snd))
            (primrec_vecNeg.comp (Primrec.snd.comp Primrec.snd))))
        (Primrec.const []))
      (Primrec.const [])
  have hsucc : Primrec₂ fun (A : Atom) (m : ℕ) =>
      (List.range m).map fun r => [((m + 1 : ℕ), A.2.1 + ((r + 1 : ℕ) : ℤ), A.2.2)] :=
    (Primrec.list_map (Primrec.list_range.comp Primrec.snd)
      (Primrec.list_cons.comp
        (Primrec.pair (Primrec.succ.comp (Primrec.snd.comp Primrec.fst))
          (Primrec.pair
            (primrec_int_add.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
              (primrec_int_ofNat.comp (Primrec.succ.comp Primrec.snd)))
            (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))))
        (Primrec.const [])).to₂).to₂
  exact (Primrec.nat_casesOn Primrec.fst hzero hsucc).of_eq fun ⟨tag, c, a⟩ => by
    cases tag <;> rfl

private lemma primrec_negConj : Primrec negConj :=
  Primrec.list_flatMap Primrec.id (primrec_negAtom.comp Primrec.snd).to₂

private lemma primrec_negDNF : Primrec negDNF :=
  Primrec.list_foldr Primrec.id (Primrec.const ([[]] : DNF))
    (primrec_andDNF.comp (primrec_negConj.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂

private lemma not_dvd_iff_exists_add_succ (m : ℕ) (t : ℤ) :
    ¬ (((m + 1 : ℕ) : ℤ) ∣ t) ↔ ∃ r < m, ((m + 1 : ℕ) : ℤ) ∣ t + ((r + 1 : ℕ) : ℤ) := by
  let k : ℤ := ((m + 1 : ℕ) : ℤ)
  have hk_pos : (0 : ℤ) < k := by positivity
  constructor
  · intro hndvd
    have hrem_nn : 0 ≤ t % k := Int.emod_nonneg t (ne_of_gt hk_pos)
    have hrem_lt : t % k < k := Int.emod_lt_of_pos t hk_pos
    have hrem_ne : t % k ≠ 0 := fun h0 => hndvd (Int.dvd_of_emod_eq_zero h0)
    let r : ℕ := (k - t % k - 1).toNat
    have hr_lt : r < m := by
      have : (k - t % k - 1 : ℤ) < m := by omega
      omega
    have hr_eq : ((r + 1 : ℕ) : ℤ) = k - t % k := by omega
    refine ⟨r, hr_lt, ?_⟩
    rw [hr_eq]
    refine ⟨t / k + 1, ?_⟩
    have hdm := Int.mul_ediv_add_emod t k
    linarith
  · rintro ⟨r, hr_lt, hdvd⟩ ht
    have h1 : k ∣ (t + ((r + 1 : ℕ) : ℤ)) - t := dvd_sub hdvd ht
    rw [add_sub_cancel_left] at h1
    have hle : k ≤ ((r + 1 : ℕ) : ℤ) := Int.le_of_dvd (by positivity) h1
    omega

private lemma evalDNF_negAtom (env : ℕ → ℤ) (A : Atom) :
    evalDNF env (negAtom A) ↔ ¬ evalAtom env A := by
  rcases A with ⟨tag, c, a⟩
  cases tag with
  | zero =>
    simp only [negAtom, evalDNF, evalConj, evalAtom, List.mem_singleton, exists_eq_left,
      forall_eq, dot_vecNeg]
    omega
  | succ m =>
    simp only [negAtom, evalDNF, evalConj, evalAtom, List.mem_map, List.mem_range,
      exists_exists_and_eq_and, List.mem_singleton, forall_eq]
    rw [not_dvd_iff_exists_add_succ]
    refine exists_congr fun r => and_congr_right fun _ => ?_
    have heq : c + ((r + 1 : ℕ) : ℤ) + dot a env = c + dot a env + ((r + 1 : ℕ) : ℤ) := by ring
    rw [heq]

private lemma evalDNF_negConj (env : ℕ → ℤ) (C : Conj) :
    evalDNF env (negConj C) ↔ ¬ evalConj env C := by
  simp only [negConj, evalDNF, List.mem_flatMap, evalConj]
  constructor
  · rintro ⟨C', ⟨A, hA, hC'⟩, hC'_eval⟩ hC
    exact (evalDNF_negAtom env A).mp ⟨C', hC', hC'_eval⟩ (hC A hA)
  · intro hnot
    rw [not_forall] at hnot
    obtain ⟨A, hA⟩ := hnot
    rw [Classical.not_imp] at hA
    obtain ⟨hAmem, hAn⟩ := hA
    obtain ⟨C', hC', hC'_eval⟩ := (evalDNF_negAtom env A).mpr hAn
    exact ⟨C', ⟨A, hAmem, hC'⟩, hC'_eval⟩

private lemma evalDNF_negDNF (env : ℕ → ℤ) (D : DNF) :
    evalDNF env (negDNF D) ↔ ¬ evalDNF env D := by
  induction D with
  | nil =>
    simp [negDNF, evalDNF, evalConj]
  | cons C Ds ih =>
    change evalDNF env (andDNF (negConj C) (negDNF Ds)) ↔ ¬ evalDNF env (C :: Ds)
    rw [evalDNF_andDNF, evalDNF_negConj, ih]
    simp only [evalDNF, List.mem_cons, exists_eq_or_imp, not_or]

/- ### Section 3: One-Variable Cooper Quantifier Elimination -/

private def prodL (C : Conj) : ℕ :=
  C.foldr (fun A acc =>
    let k := (A.2.2.getD 0 0).natAbs
    if k = 0 then acc else k * acc) 1

private lemma primrec_prodL : Primrec prodL := by
  have hk : Primrec fun p : Conj × Atom × ℕ => (p.2.1.2.2.getD 0 0).natAbs :=
    primrec_int_natAbs.comp
      ((Primrec.list_getD (0 : ℤ)).comp
        (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)))
        (Primrec.const 0))
  exact Primrec.list_foldr Primrec.id (Primrec.const 1)
    (Primrec.ite (Primrec.eq.comp hk (Primrec.const 0))
      (Primrec.snd.comp Primrec.snd)
      (Primrec.nat_mul.comp hk (Primrec.snd.comp Primrec.snd))).to₂

private lemma prodL_pos (C : Conj) : 0 < prodL C := by
  induction C with
  | nil => simp [prodL]
  | cons A Cs ih =>
    simp only [prodL, List.foldr_cons]
    split_ifs with h
    · exact ih
    · exact Nat.mul_pos (Nat.pos_of_ne_zero h) ih

private lemma dvd_prodL {C : Conj} {A : Atom} (hA : A ∈ C) (hne : A.2.2.getD 0 0 ≠ 0) :
    (A.2.2.getD 0 0).natAbs ∣ prodL C := by
  induction C with
  | nil => cases hA
  | cons B Bs ih =>
    simp only [prodL, List.foldr_cons]
    rcases List.mem_cons.mp hA with rfl | hmem
    · have hk : (A.2.2.getD 0 0).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hne
      simp only [hk, ↓reduceIte]
      exact dvd_mul_right _ _
    · split_ifs
      · exact ih hmem
      · exact dvd_mul_of_dvd_right (ih hmem) _

private def normAtom (L : ℕ) (A : Atom) : Atom :=
  let tag := A.1
  let c := A.2.1
  let a := A.2.2
  let a0 := a.getD 0 0
  if a0 = 0 then A
  else
    let q : ℕ := L / a0.natAbs
    if tag = 0 then
      (0, (q : ℤ) * c, (if 0 < a0 then (1 : ℤ) else -1) :: a.tail.map ((q : ℤ) * ·))
    else
      if 0 < a0 then
        (q * tag, (q : ℤ) * c, (1 : ℤ) :: a.tail.map ((q : ℤ) * ·))
      else
        (q * tag, -((q : ℤ) * c), (1 : ℤ) :: a.tail.map ((-(q : ℤ)) * ·))

private lemma primrec_normAtom : Primrec₂ normAtom := by
  let tag : ℕ × Atom → ℕ := fun p => p.2.1
  let c : ℕ × Atom → ℤ := fun p => p.2.2.1
  let a : ℕ × Atom → List ℤ := fun p => p.2.2.2
  let a0 : ℕ × Atom → ℤ := fun p => (a p).getD 0 0
  let q : ℕ × Atom → ℕ := fun p => p.1 / (a0 p).natAbs
  let qz : ℕ × Atom → ℤ := fun p => (q p : ℤ)
  let tail : ℕ × Atom → List ℤ := fun p => (a p).tail
  have htag : Primrec tag := Primrec.fst.comp Primrec.snd
  have hc : Primrec c := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have ha : Primrec a := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have ha0 : Primrec a0 := (Primrec.list_getD (0 : ℤ)).comp ha (Primrec.const 0)
  have hq : Primrec q := Primrec.nat_div.comp Primrec.fst (primrec_int_natAbs.comp ha0)
  have hqz : Primrec qz := primrec_int_ofNat.comp hq
  have htail : Primrec tail := Primrec.list_tail.comp ha
  have hposA0 : PrimrecPred fun p : ℕ × Atom => (0 : ℤ) < a0 p :=
    (primrec_int_pos.comp ha0).primrecPred
  have hqc : Primrec fun p => qz p * c p := primrec_int_mul.comp hqz hc
  have hscaled : Primrec fun p => (tail p).map (qz p * ·) := primrec_vecScale.comp hqz htail
  have hnegScaled : Primrec fun p => (tail p).map ((-qz p) * ·) :=
    primrec_vecScale.comp (primrec_int_neg.comp hqz) htail
  have hltBranch : Primrec fun p : ℕ × Atom =>
      ((0 : ℕ), qz p * c p, (if 0 < a0 p then (1 : ℤ) else -1) :: (tail p).map (qz p * ·)) :=
    Primrec.pair (Primrec.const 0)
      (Primrec.pair hqc
        (Primrec.list_cons.comp (Primrec.ite hposA0 (Primrec.const 1) (Primrec.const (-1)))
          hscaled))
  have hdvdPos : Primrec fun p : ℕ × Atom =>
      (q p * tag p, qz p * c p, (1 : ℤ) :: (tail p).map (qz p * ·)) :=
    Primrec.pair (Primrec.nat_mul.comp hq htag)
      (Primrec.pair hqc (Primrec.list_cons.comp (Primrec.const 1) hscaled))
  have hdvdNeg : Primrec fun p : ℕ × Atom =>
      (q p * tag p, -(qz p * c p), (1 : ℤ) :: (tail p).map ((-qz p) * ·)) :=
    Primrec.pair (Primrec.nat_mul.comp hq htag)
      (Primrec.pair (primrec_int_neg.comp hqc)
        (Primrec.list_cons.comp (Primrec.const 1) hnegScaled))
  have hbody := Primrec.ite (Primrec.eq.comp ha0 (Primrec.const (0 : ℤ)))
    Primrec.snd
    (Primrec.ite (Primrec.eq.comp htag (Primrec.const 0))
      hltBranch
      (Primrec.ite hposA0 hdvdPos hdvdNeg))
  exact hbody.to₂

private def IsUnitHead (A : Atom) : Prop :=
  A.2.2.getD 0 0 = 0 ∨ A.2.2.getD 0 0 = 1 ∨ (A.1 = 0 ∧ A.2.2.getD 0 0 = -1)

private lemma isUnitHead_normAtom (L : ℕ) (A : Atom) : IsUnitHead (normAtom L A) := by
  unfold normAtom IsUnitHead
  dsimp only
  split_ifs with h0 htag hpos
  · exact Or.inl h0
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inl rfl)

private lemma evalAtom_normAtom_iff {L : ℕ} {A : Atom} (hL : 0 < L)
    (hdvd : A.2.2.getD 0 0 ≠ 0 → (A.2.2.getD 0 0).natAbs ∣ L)
    (x : ℤ) (env : ℕ → ℤ) :
    evalAtom (consEnv ((L : ℤ) * x) env) (normAtom L A) ↔ evalAtom (consEnv x env) A := by
  rcases A with ⟨tag, c, a⟩
  set a0 : ℤ := a.getD 0 0
  unfold normAtom
  dsimp only
  change evalAtom (consEnv ((L : ℤ) * x) env)
    (if a0 = 0 then (tag, c, a)
     else
       let q : ℕ := L / a0.natAbs
       if tag = 0 then
         (0, (q : ℤ) * c, (if 0 < a0 then (1 : ℤ) else -1) :: a.tail.map ((q : ℤ) * ·))
       else
         if 0 < a0 then
           (q * tag, (q : ℤ) * c, (1 : ℤ) :: a.tail.map ((q : ℤ) * ·))
         else
           (q * tag, -((q : ℤ) * c), (1 : ℤ) :: a.tail.map ((-(q : ℤ)) * ·))) ↔
    evalAtom (consEnv x env) (tag, c, a)
  by_cases ha0 : a0 = 0
  · simp only [ha0, ↓reduceIte]
    have hdot : dot a (consEnv ((L : ℤ) * x) env) = dot a (consEnv x env) := by
      rw [dot_consEnv, dot_consEnv]
      change a0 * ((L : ℤ) * x) + dot a.tail env = a0 * x + dot a.tail env
      simp [ha0]
    cases tag <;> simp [evalAtom, hdot]
  · simp only [ha0, ↓reduceIte]
    have hdiv : a0.natAbs ∣ L := hdvd ha0
    set q : ℕ := L / a0.natAbs
    have hmul : a0.natAbs * q = L := Nat.mul_div_cancel' hdiv
    have hq_pos : 0 < q := by
      rcases Nat.eq_zero_or_pos q with h0 | hp
      · rw [h0, mul_zero] at hmul; omega
      · exact hp
    have hqz_pos : (0 : ℤ) < (q : ℤ) := by exact_mod_cast hq_pos
    have hqz_ne : (q : ℤ) ≠ 0 := ne_of_gt hqz_pos
    by_cases htag : tag = 0
    · subst htag
      simp only [↓reduceIte, evalAtom, dot, consEnv, dot_vecScale, dot_consEnv]
      change (0 : ℤ) < (q : ℤ) * c + ((if 0 < a0 then (1 : ℤ) else -1) * ((L : ℤ) * x) +
        (q : ℤ) * dot a.tail env) ↔ (0 : ℤ) < c + (a0 * x + dot a.tail env)
      by_cases hpos : 0 < a0
      · simp only [hpos, ↓reduceIte]
        have hqa0 : (q : ℤ) * a0 = (L : ℤ) := by
          have habs : (a0.natAbs : ℤ) = a0 := Int.natAbs_of_nonneg (le_of_lt hpos)
          have hcast : ((a0.natAbs : ℤ) * (q : ℤ)) = (L : ℤ) := by exact_mod_cast hmul
          rw [← hcast, habs]; ring
        have hlin : (q : ℤ) * c + (1 * ((L : ℤ) * x) + (q : ℤ) * dot a.tail env) =
            (q : ℤ) * (c + (a0 * x + dot a.tail env)) := by
          rw [← hqa0]; ring
        rw [hlin]
        exact mul_pos_iff_of_pos_left hqz_pos
      · simp only [hpos, ↓reduceIte]
        have hneg : a0 < 0 := lt_of_le_of_ne (not_lt.mp hpos) ha0
        have hqa0 : (q : ℤ) * a0 = -(L : ℤ) := by
          have habs : (a0.natAbs : ℤ) = -a0 := Int.ofNat_natAbs_of_nonpos (le_of_lt hneg)
          have hcast : ((a0.natAbs : ℤ) * (q : ℤ)) = (L : ℤ) := by exact_mod_cast hmul
          rw [← hcast, habs]; ring
        have hlin : (q : ℤ) * c + (-1 * ((L : ℤ) * x) + (q : ℤ) * dot a.tail env) =
            (q : ℤ) * (c + (a0 * x + dot a.tail env)) := by
          have : -(L : ℤ) = (q : ℤ) * a0 := hqa0.symm
          calc (q : ℤ) * c + (-1 * ((L : ℤ) * x) + (q : ℤ) * dot a.tail env)
              = (q : ℤ) * c + (-(L : ℤ)) * x + (q : ℤ) * dot a.tail env := by ring
            _ = (q : ℤ) * c + ((q : ℤ) * a0) * x + (q : ℤ) * dot a.tail env := by rw [this]
            _ = (q : ℤ) * (c + (a0 * x + dot a.tail env)) := by ring
        rw [hlin]
        exact mul_pos_iff_of_pos_left hqz_pos
    · have htag_pos : 0 < tag := Nat.pos_of_ne_zero htag
      have hqt_pos : 0 < q * tag := Nat.mul_pos hq_pos htag_pos
      simp only [htag, ↓reduceIte]
      by_cases hpos : 0 < a0
      · simp only [hpos, ↓reduceIte]
        rw [evalAtom_of_pos hqt_pos, evalAtom_of_pos htag_pos]
        simp only [dot, consEnv, dot_vecScale, dot_consEnv, Nat.cast_mul]
        have hqa0 : (q : ℤ) * a0 = (L : ℤ) := by
          have habs : (a0.natAbs : ℤ) = a0 := Int.natAbs_of_nonneg (le_of_lt hpos)
          have hcast : ((a0.natAbs : ℤ) * (q : ℤ)) = (L : ℤ) := by exact_mod_cast hmul
          rw [← hcast, habs]; ring
        have hlin : (q : ℤ) * c + (1 * ((L : ℤ) * x) + (q : ℤ) * dot a.tail env) =
            (q : ℤ) * (c + (a0 * x + dot a.tail env)) := by
          rw [← hqa0]; ring
        change (q : ℤ) * (tag : ℤ) ∣ (q : ℤ) * c + (1 * ((L : ℤ) * x) + (q : ℤ) * dot a.tail env) ↔
          (tag : ℤ) ∣ c + (a0 * x + dot a.tail env)
        rw [hlin, mul_dvd_mul_iff_left hqz_ne]
      · simp only [hpos, ↓reduceIte]
        rw [evalAtom_of_pos hqt_pos, evalAtom_of_pos htag_pos]
        simp only [dot, consEnv, dot_vecScale, dot_consEnv, Nat.cast_mul]
        have hneg : a0 < 0 := lt_of_le_of_ne (not_lt.mp hpos) ha0
        have hqa0 : (q : ℤ) * a0 = -(L : ℤ) := by
          have habs : (a0.natAbs : ℤ) = -a0 := Int.ofNat_natAbs_of_nonpos (le_of_lt hneg)
          have hcast : ((a0.natAbs : ℤ) * (q : ℤ)) = (L : ℤ) := by exact_mod_cast hmul
          rw [← hcast, habs]; ring
        have hlin : -((q : ℤ) * c) + (1 * ((L : ℤ) * x) + -(q : ℤ) * dot a.tail env) =
            -((q : ℤ) * (c + (a0 * x + dot a.tail env))) := by
          have hL_eq : (L : ℤ) = -((q : ℤ) * a0) := by linarith
          rw [hL_eq]; ring
        change (q : ℤ) * (tag : ℤ) ∣
          -((q : ℤ) * c) + (1 * ((L : ℤ) * x) + -(q : ℤ) * dot a.tail env) ↔
          (tag : ℤ) ∣ c + (a0 * x + dot a.tail env)
        rw [hlin, dvd_neg, mul_dvd_mul_iff_left hqz_ne]

private def divMod (C : Conj) : ℕ :=
  C.foldr (fun A acc => if A.1 = 0 then acc else A.1 * acc) 1

private lemma primrec_divMod : Primrec divMod :=
  Primrec.list_foldr Primrec.id (Primrec.const 1)
    (Primrec.ite (Primrec.eq.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.snd)) (Primrec.const 0))
      (Primrec.snd.comp Primrec.snd)
      (Primrec.nat_mul.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
        (Primrec.snd.comp Primrec.snd))).to₂

private lemma divMod_pos (C : Conj) : 0 < divMod C := by
  induction C with
  | nil => simp [divMod]
  | cons A Cs ih =>
    simp only [divMod, List.foldr_cons]
    split_ifs with h
    · exact ih
    · exact Nat.mul_pos (Nat.pos_of_ne_zero h) ih

private lemma dvd_divMod {C : Conj} {A : Atom} (hA : A ∈ C) (hne : A.1 ≠ 0) :
    A.1 ∣ divMod C := by
  induction C with
  | nil => cases hA
  | cons B Bs ih =>
    simp only [divMod, List.foldr_cons]
    rcases List.mem_cons.mp hA with rfl | hmem
    · simp only [hne, ↓reduceIte]
      exact dvd_mul_right _ _
    · split_ifs
      · exact ih hmem
      · exact dvd_mul_of_dvd_right (ih hmem) _

private def isLo (A : Atom) : Bool :=
  decide (A.1 = 0) && decide (A.2.2.getD 0 0 = 1)

private def isNotHi (A : Atom) : Bool :=
  !(decide (A.1 = 0) && decide (A.2.2.getD 0 0 = -1))

private lemma primrec_isLo : Primrec isLo :=
  Primrec.and.comp
    (Primrec.eq.comp Primrec.fst (Primrec.const 0)).decide
    (Primrec.eq.comp ((Primrec.list_getD (0 : ℤ)).comp (Primrec.snd.comp Primrec.snd) (Primrec.const 0))
      (Primrec.const (1 : ℤ))).decide

private lemma primrec_isNotHi : Primrec isNotHi :=
  Primrec.not.comp
    (Primrec.and.comp
      (Primrec.eq.comp Primrec.fst (Primrec.const 0)).decide
      (Primrec.eq.comp ((Primrec.list_getD (0 : ℤ)).comp (Primrec.snd.comp Primrec.snd) (Primrec.const 0))
        (Primrec.const (-1 : ℤ))).decide)

private def substY (cb : ℤ) (vb : List ℤ) (A : Atom) : Atom :=
  let a0 := A.2.2.getD 0 0
  (A.1, A.2.1 + a0 * cb, vecAdd A.2.2.tail (vb.map (a0 * ·)))

private lemma primrec_substY : Primrec (fun p : (ℤ × List ℤ) × Atom => substY p.1.1 p.1.2 p.2) := by
  let cb : (ℤ × List ℤ) × Atom → ℤ := fun p => p.1.1
  let vb : (ℤ × List ℤ) × Atom → List ℤ := fun p => p.1.2
  let A : (ℤ × List ℤ) × Atom → Atom := fun p => p.2
  let a0 : (ℤ × List ℤ) × Atom → ℤ := fun p => (A p).2.2.getD 0 0
  have hcb : Primrec cb := Primrec.fst.comp Primrec.fst
  have hvb : Primrec vb := Primrec.snd.comp Primrec.fst
  have hA : Primrec A := Primrec.snd
  have ha0 : Primrec a0 := (Primrec.list_getD (0 : ℤ)).comp (Primrec.snd.comp (Primrec.snd.comp hA))
    (Primrec.const 0)
  exact Primrec.pair (Primrec.fst.comp hA)
    (Primrec.pair
      (primrec_int_add.comp (Primrec.fst.comp (Primrec.snd.comp hA)) (primrec_int_mul.comp ha0 hcb))
      (primrec_vecAdd.comp
        (Primrec.list_tail.comp (Primrec.snd.comp (Primrec.snd.comp hA)))
        (primrec_vecScale.comp ha0 hvb)))

private lemma evalAtom_substY (cb : ℤ) (vb : List ℤ) (A : Atom) (env : ℕ → ℤ) :
    evalAtom env (substY cb vb A) ↔ evalAtom (consEnv (cb + dot vb env) env) A := by
  rcases A with ⟨tag, c, a⟩
  have hlin :
      (c + a.getD 0 0 * cb) + dot (vecAdd a.tail (vb.map (a.getD 0 0 * ·))) env =
      c + dot a (consEnv (cb + dot vb env) env) := by
    rw [dot_vecAdd, dot_vecScale, dot_consEnv]
    ring
  cases tag with
  | zero => simp only [substY, evalAtom, hlin]
  | succ m => simp only [substY, evalAtom, hlin]

private lemma evalConj_map_substY (cb : ℤ) (vb : List ℤ) (C : Conj) (env : ℕ → ℤ) :
    evalConj env (C.map (substY cb vb)) ↔ evalConj (consEnv (cb + dot vb env) env) C := by
  simp only [evalConj, List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
    evalAtom_substY]

private def elimUnit (C : Conj) : DNF :=
  let M := divMod C
  let Lo := C.filter isLo
  if Lo.isEmpty then
    let NoHi := C.filter isNotHi
    (List.range M).map fun r => NoHi.map (substY ((r + 1 : ℕ) : ℤ) [])
  else
    Lo.flatMap fun A =>
      (List.range M).map fun r =>
        C.map (substY (-A.2.1 + ((r + 1 : ℕ) : ℤ)) (A.2.2.tail.map (- ·)))

private def elimOneConj (C : Conj) : DNF :=
  let L := prodL C
  elimUnit ((L, 0, [1]) :: C.map (normAtom L))

private def elimOne (D : DNF) : DNF :=
  D.flatMap elimOneConj

private def elimN (n : ℕ) (D : DNF) : DNF :=
  elimOne^[n] D

private lemma primrec_elimUnit : Primrec elimUnit := by
  have hLo : Primrec fun C : Conj => C.filter isLo :=
    primrec_list_filter_bool Primrec.id (primrec_isLo.comp Primrec.snd).to₂
  have hNoHi : Primrec fun C : Conj => C.filter isNotHi :=
    primrec_list_filter_bool Primrec.id (primrec_isNotHi.comp Primrec.snd).to₂
  have hEmptyPred : PrimrecPred fun C : Conj => (C.filter isLo).isEmpty = true :=
    Primrec.eq.comp (primrec_list_isEmpty.comp hLo) (Primrec.const true)
  have hBranch1 : Primrec fun C : Conj =>
      (List.range (divMod C)).map fun r =>
        (C.filter isNotHi).map (substY ((r + 1 : ℕ) : ℤ) []) :=
    Primrec.list_map (Primrec.list_range.comp primrec_divMod)
      (Primrec.list_map (hNoHi.comp Primrec.fst)
        (primrec_substY.comp
          (Primrec.pair
            (Primrec.pair (primrec_int_ofNat.comp (Primrec.succ.comp (Primrec.snd.comp Primrec.fst)))
              (Primrec.const ([] : List ℤ)))
            Primrec.snd)).to₂).to₂
  have hBranch2 : Primrec fun C : Conj =>
      (C.filter isLo).flatMap fun A =>
        (List.range (divMod C)).map fun r =>
          C.map (substY (-A.2.1 + ((r + 1 : ℕ) : ℤ)) (A.2.2.tail.map (- ·))) :=
    Primrec.list_flatMap hLo
      (Primrec.list_map (Primrec.list_range.comp (primrec_divMod.comp Primrec.fst))
        (Primrec.list_map (Primrec.fst.comp Primrec.fst)
          (primrec_substY.comp
            (Primrec.pair
              (Primrec.pair
                (primrec_int_add.comp
                  (primrec_int_neg.comp
                    (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))))
                  (primrec_int_ofNat.comp (Primrec.succ.comp (Primrec.snd.comp Primrec.fst))))
                (primrec_vecNeg.comp
                  (Primrec.list_tail.comp
                    (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))))))
              Primrec.snd)).to₂).to₂).to₂
  exact Primrec.ite hEmptyPred hBranch1 hBranch2

private lemma primrec_elimOneConj : Primrec elimOneConj :=
  primrec_elimUnit.comp
    (Primrec.list_cons.comp
      (Primrec.pair primrec_prodL (Primrec.const ((0 : ℤ), [(1 : ℤ)])))
      (Primrec.list_map Primrec.id
        (primrec_normAtom.comp (primrec_prodL.comp Primrec.fst) Primrec.snd).to₂))

private lemma primrec_elimOne : Primrec elimOne :=
  Primrec.list_flatMap Primrec.id (primrec_elimOneConj.comp Primrec.snd).to₂

private lemma primrec_elimN : Primrec₂ elimN :=
  (Primrec.nat_iterate Primrec.fst Primrec.snd (primrec_elimOne.comp Primrec.snd).to₂).to₂

private lemma exists_least_int {P : ℤ → Prop} (lb : ℤ) (hlb : ∀ y, P y → lb ≤ y)
    (hex : ∃ y, P y) : ∃ y0, P y0 ∧ ∀ y, P y → y0 ≤ y := by
  classical
  have hnat : ∃ n : ℕ, P (lb + n) := by
    obtain ⟨y, hy⟩ := hex
    refine ⟨(y - lb).toNat, ?_⟩
    have hle := hlb y hy
    have heq : lb + ((y - lb).toNat : ℤ) = y := by omega
    rwa [heq]
  refine ⟨lb + Nat.find hnat, Nat.find_spec hnat, fun y hy => ?_⟩
  have hle := hlb y hy
  have hmin : Nat.find hnat ≤ (y - lb).toNat := by
    apply Nat.find_min'
    have heq : lb + ((y - lb).toNat : ℤ) = y := by omega
    rwa [heq]
  omega

private lemma evalAtom_shift_of_dvd {M : ℕ} {A : Atom} (hunit : IsUnitHead A)
    (hdiv : A.1 ≠ 0 → A.1 ∣ M) (hnoLt : A.1 = 0 → A.2.2.getD 0 0 = 0)
    (y1 y2 : ℤ) (hcong : ((M : ℕ) : ℤ) ∣ y1 - y2) (env : ℕ → ℤ) :
    evalAtom (consEnv y1 env) A ↔ evalAtom (consEnv y2 env) A := by
  rcases A with ⟨tag, c, a⟩
  dsimp only [IsUnitHead] at hunit hdiv hnoLt
  cases tag with
  | zero =>
    have ha0 : a.getD 0 0 = 0 := hnoLt rfl
    simp only [evalAtom, dot_consEnv, ha0, zero_mul, zero_add]
  | succ m =>
    have hdvdM : (m + 1 : ℕ) ∣ M := hdiv (Nat.succ_ne_zero m)
    have hdvdZ : (((m + 1 : ℕ) : ℤ)) ∣ ((M : ℕ) : ℤ) := by exact_mod_cast hdvdM
    have hdvdDiff : (((m + 1 : ℕ) : ℤ)) ∣ y1 - y2 := dvd_trans hdvdZ hcong
    rcases hunit with ha0 | ha1 | ⟨h0, _⟩
    · simp only [evalAtom, dot_consEnv, ha0, zero_mul, zero_add]
    · simp only [evalAtom, dot_consEnv, ha1, one_mul]
      have hdiff : (c + (y1 + dot a.tail env)) - (c + (y2 + dot a.tail env)) = y1 - y2 := by ring
      constructor
      · intro h1
        have hsub := dvd_sub h1 hdvdDiff
        have heq : c + (y1 + dot a.tail env) - (y1 - y2) = c + (y2 + dot a.tail env) := by ring
        rwa [heq] at hsub
      · intro h2
        have hadd := dvd_add h2 hdvdDiff
        have heq : c + (y2 + dot a.tail env) + (y1 - y2) = c + (y1 + dot a.tail env) := by ring
        rwa [heq] at hadd
    · exact absurd h0 (Nat.succ_ne_zero m)

private lemma evalDNF_elimUnit_iff {C : Conj} (hunit : ∀ A ∈ C, IsUnitHead A) (env : ℕ → ℤ) :
    evalDNF env (elimUnit C) ↔ ∃ y : ℤ, evalConj (consEnv y env) C := by
  set M := divMod C
  have hM_pos : 0 < M := divMod_pos C
  set Lo := C.filter isLo
  unfold elimUnit
  dsimp only
  change evalDNF env (if Lo.isEmpty then
      (List.range M).map fun r => (C.filter isNotHi).map (substY ((r + 1 : ℕ) : ℤ) [])
    else
      Lo.flatMap fun A =>
        (List.range M).map fun r =>
          C.map (substY (-A.2.1 + ((r + 1 : ℕ) : ℤ)) (A.2.2.tail.map (- ·)))) ↔
    ∃ y : ℤ, evalConj (consEnv y env) C
  by_cases hLo : Lo.isEmpty = true
  · simp only [hLo, ↓reduceIte]
    have hLo_nil : Lo = [] := List.isEmpty_iff.mp hLo
    have hnoLo : ∀ A ∈ C, ¬ (A.1 = 0 ∧ A.2.2.getD 0 0 = 1) := by
      intro A hA ⟨h1, h2⟩
      have hmem : A ∈ Lo := List.mem_filter.mpr ⟨hA, by simp only [isLo, h1, h2, decide_true, Bool.and_self]⟩
      rw [hLo_nil] at hmem
      cases hmem
    simp only [evalDNF, List.mem_map, List.mem_range, exists_exists_and_eq_and,
      evalConj_map_substY, dot, add_zero]
    constructor
    · rintro ⟨r, _, hr⟩
      let yBase : ℤ := ((r + 1 : ℕ) : ℤ)
      let B : ℤ := C.foldr (fun A acc => min acc (A.2.1 + dot A.2.2.tail env)) 0
      have hB : ∀ A ∈ C, B ≤ A.2.1 + dot A.2.2.tail env := by
        intro A hA
        have hfold : ∀ (L : Conj), ∀ A ∈ L,
            L.foldr (fun X acc => min acc (X.2.1 + dot X.2.2.tail env)) 0 ≤
              A.2.1 + dot A.2.2.tail env := by
          intro L
          induction L with
          | nil => intro _ h; cases h
          | cons X Xs ih =>
            intro Y hY
            simp only [List.foldr_cons]
            rcases List.mem_cons.mp hY with rfl | hmem
            · exact min_le_right _ _
            · exact le_trans (min_le_left _ _) (ih Y hmem)
        exact hfold C A hA
      let k : ℕ := (yBase - B + 1).toNat
      let y : ℤ := yBase - (k : ℤ) * (M : ℤ)
      refine ⟨y, fun A hA => ?_⟩
      by_cases hHi : A.1 = 0 ∧ A.2.2.getD 0 0 = -1
      · rcases A with ⟨tag, c, a⟩
        dsimp only at hHi
        rcases hHi with ⟨rfl, ha0⟩
        simp only [evalAtom, dot_consEnv, ha0]
        have hBA : B ≤ c + dot a.tail env := hB (0, c, a) hA
        have hk_ge : yBase - B + 1 ≤ (k : ℤ) := by omega
        have hM_ge : (1 : ℤ) ≤ (M : ℤ) := by exact_mod_cast hM_pos
        have hmul_ge : (k : ℤ) ≤ (k : ℤ) * (M : ℤ) := by nlinarith
        have hy_lt : y < B := by dsimp [y]; linarith
        linarith
      · have hnotHi : A ∈ C.filter isNotHi := by
          refine List.mem_filter.mpr ⟨hA, ?_⟩
          simp only [isNotHi, Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not]
          by_cases h1 : A.1 = 0
          · right; intro h2; exact hHi ⟨h1, h2⟩
          · left; exact h1
        have hbaseA : evalAtom (consEnv yBase env) A := hr A hnotHi
        have hnoLt : A.1 = 0 → A.2.2.getD 0 0 = 0 := by
          intro h1
          rcases hunit A hA with h0 | hpos1 | ⟨_, hneg1⟩
          · exact h0
          · exact absurd ⟨h1, hpos1⟩ (hnoLo A hA)
          · exact absurd ⟨h1, hneg1⟩ hHi
        have hcong : ((M : ℕ) : ℤ) ∣ y - yBase := ⟨-(k : ℤ), by dsimp [y]; ring⟩
        exact (evalAtom_shift_of_dvd (hunit A hA) (dvd_divMod hA) hnoLt y yBase hcong env).mpr hbaseA
    · rintro ⟨y, hy⟩
      have hMz_pos : (0 : ℤ) < (M : ℤ) := by exact_mod_cast hM_pos
      let r : ℕ := ((y - 1) % (M : ℤ)).toNat
      have hrem_nn : 0 ≤ (y - 1) % (M : ℤ) := Int.emod_nonneg (y - 1) (ne_of_gt hMz_pos)
      have hrem_lt : (y - 1) % (M : ℤ) < (M : ℤ) := Int.emod_lt_of_pos (y - 1) hMz_pos
      have hr_lt : r < M := by omega
      have hr_eq : ((r + 1 : ℕ) : ℤ) = (y - 1) % (M : ℤ) + 1 := by omega
      refine ⟨r, hr_lt, fun A hA => ?_⟩
      obtain ⟨hAC, hNotHiB⟩ := List.mem_filter.mp hA
      have hNotHi : ¬ (A.1 = 0 ∧ A.2.2.getD 0 0 = -1) := by
        intro ⟨h1, h2⟩
        simp only [isNotHi, h1, h2, decide_true, Bool.and_self, Bool.not_true, Bool.false_eq_true] at hNotHiB
      have hnoLt : A.1 = 0 → A.2.2.getD 0 0 = 0 := by
        intro h1
        rcases hunit A hAC with h0 | hpos1 | ⟨_, hneg1⟩
        · exact h0
        · exact absurd ⟨h1, hpos1⟩ (hnoLo A hAC)
        · exact absurd ⟨h1, hneg1⟩ hNotHi
      have hcong : ((M : ℕ) : ℤ) ∣ ((r + 1 : ℕ) : ℤ) - y := by
        rw [hr_eq]
        refine ⟨-((y - 1) / (M : ℤ)), ?_⟩
        have hdm := Int.mul_ediv_add_emod (y - 1) (M : ℤ)
        linarith
      exact (evalAtom_shift_of_dvd (hunit A hAC) (dvd_divMod hAC) hnoLt
        ((r + 1 : ℕ) : ℤ) y hcong env).mpr (hy A hAC)
  · have hLo_f : Lo.isEmpty = false := Bool.eq_false_iff.mpr hLo
    simp only [hLo_f, Bool.false_eq_true, ↓reduceIte, evalDNF, List.mem_flatMap, List.mem_map,
      List.mem_range]
    constructor
    · rintro ⟨C', ⟨A, _, r, _, rfl⟩, hC'⟩
      rw [evalConj_map_substY] at hC'
      exact ⟨(-A.2.1 + ((r + 1 : ℕ) : ℤ)) + dot (A.2.2.tail.map (- ·)) env, hC'⟩
    · rintro ⟨yInit, hyInit⟩
      have hLo_ne : Lo ≠ [] := fun hnil => hLo (by simp [hnil])
      obtain ⟨A0, hA0_mem⟩ : ∃ A0, A0 ∈ Lo := List.exists_mem_of_ne_nil Lo hLo_ne
      obtain ⟨hA0_C, hA0_lo⟩ := List.mem_filter.mp hA0_mem
      have hA0_tag : A0.1 = 0 := by
        simp only [isLo, Bool.and_eq_true, decide_eq_true_eq] at hA0_lo
        exact hA0_lo.1
      have hA0_head : A0.2.2.getD 0 0 = 1 := by
        simp only [isLo, Bool.and_eq_true, decide_eq_true_eq] at hA0_lo
        exact hA0_lo.2
      have hlb : ∀ y : ℤ, evalConj (consEnv y env) C → -A0.2.1 - dot A0.2.2.tail env ≤ y := by
        intro y hy
        have h := hy A0 hA0_C
        rcases A0 with ⟨tag0, c0, a0⟩
        dsimp only at hA0_tag hA0_head ⊢
        subst hA0_tag
        simp only [evalAtom, dot_consEnv, hA0_head, one_mul] at h
        omega
      obtain ⟨y0, hy0, hleast⟩ := exists_least_int (-A0.2.1 - dot A0.2.2.tail env) hlb ⟨yInit, hyInit⟩
      have hy1_not : ¬ evalConj (consEnv (y0 - (M : ℤ)) env) C := by
        intro h1
        have hle := hleast (y0 - (M : ℤ)) h1
        omega
      rw [evalConj, not_forall] at hy1_not
      obtain ⟨A, hA⟩ := hy1_not
      rw [Classical.not_imp] at hA
      obtain ⟨hAC, hA_fail⟩ := hA
      have hA_hold : evalAtom (consEnv y0 env) A := hy0 A hAC
      have hA_lo_props : A.1 = 0 ∧ A.2.2.getD 0 0 = 1 := by
        rcases hunit A hAC with ha0 | ha1 | ⟨htag0, ham1⟩
        · exfalso
          apply hA_fail
          rcases A with ⟨tag, c, a⟩
          dsimp only at ha0
          cases tag <;> simp only [evalAtom, dot_consEnv, ha0, zero_mul, zero_add] at hA_hold ⊢ <;>
            exact hA_hold
        · by_cases htag0 : A.1 = 0
          · exact ⟨htag0, ha1⟩
          · exfalso
            apply hA_fail
            have hcong : ((M : ℕ) : ℤ) ∣ (y0 - (M : ℤ)) - y0 := ⟨-1, by ring⟩
            exact (evalAtom_shift_of_dvd (hunit A hAC) (dvd_divMod hAC)
              (fun h0 => absurd h0 htag0) (y0 - (M : ℤ)) y0 hcong env).mpr hA_hold
        · exfalso
          apply hA_fail
          rcases A with ⟨tag, c, a⟩
          dsimp only at htag0 ham1
          subst htag0
          simp only [evalAtom, dot_consEnv, ham1] at hA_hold ⊢
          omega
      have hA_in_Lo : A ∈ Lo :=
        List.mem_filter.mpr ⟨hAC, by simp only [isLo, hA_lo_props.1, hA_lo_props.2, decide_true, Bool.and_self]⟩
      let b : ℤ := -A.2.1 - dot A.2.2.tail env
      have hb_lt : b < y0 := by
        dsimp only [b]
        rcases A with ⟨tag, c, a⟩
        dsimp only at hA_lo_props ⊢
        rcases hA_lo_props with ⟨rfl, ha1⟩
        simp only [evalAtom, dot_consEnv, ha1, one_mul] at hA_hold
        omega
      have hy0_le : y0 - (M : ℤ) ≤ b := by
        dsimp only [b]
        rcases A with ⟨tag, c, a⟩
        dsimp only at hA_lo_props ⊢
        rcases hA_lo_props with ⟨rfl, ha1⟩
        simp only [evalAtom, dot_consEnv, ha1, one_mul] at hA_fail
        omega
      let r : ℕ := (y0 - b - 1).toNat
      have hr_lt : r < M := by omega
      have hr_eq : (-A.2.1 + ((r + 1 : ℕ) : ℤ)) + dot (A.2.2.tail.map (- ·)) env = y0 := by
        rw [dot_vecNeg]
        dsimp only [b, r]
        omega
      refine ⟨C.map (substY (-A.2.1 + ((r + 1 : ℕ) : ℤ)) (A.2.2.tail.map (- ·))),
        ⟨A, hA_in_Lo, r, hr_lt, rfl⟩, ?_⟩
      rw [evalConj_map_substY, hr_eq]
      exact hy0

private lemma evalDNF_elimOneConj_iff (C : Conj) (env : ℕ → ℤ) :
    evalDNF env (elimOneConj C) ↔ ∃ x : ℤ, evalConj (consEnv x env) C := by
  unfold elimOneConj
  set L := prodL C
  have hL_pos : 0 < L := prodL_pos C
  have hunit : ∀ A ∈ ((L, 0, [1]) :: C.map (normAtom L)), IsUnitHead A := by
    intro A hA
    rcases List.mem_cons.mp hA with rfl | hmem
    · exact Or.inr (Or.inl rfl)
    · obtain ⟨B, _, rfl⟩ := List.mem_map.mp hmem
      exact isUnitHead_normAtom L B
  rw [evalDNF_elimUnit_iff hunit]
  constructor
  · rintro ⟨y, hy⟩
    have hdvdL : ((L : ℕ) : ℤ) ∣ y := by
      have h0 := hy (L, 0, [1]) (List.mem_cons_self ..)
      rw [evalAtom_of_pos hL_pos] at h0
      simpa [dot, consEnv] using h0
    obtain ⟨x, rfl⟩ := hdvdL
    refine ⟨x, fun A hA => ?_⟩
    have hnorm := hy (normAtom L A) (List.mem_cons_of_mem _ (List.mem_map_of_mem hA))
    exact (evalAtom_normAtom_iff hL_pos (dvd_prodL hA) x env).mp hnorm
  · rintro ⟨x, hx⟩
    refine ⟨(L : ℤ) * x, fun A hA => ?_⟩
    rcases List.mem_cons.mp hA with rfl | hmem
    · rw [evalAtom_of_pos hL_pos]
      simp [dot, consEnv]
    · obtain ⟨B, hBC, rfl⟩ := List.mem_map.mp hmem
      exact (evalAtom_normAtom_iff hL_pos (dvd_prodL hBC) x env).mpr (hx B hBC)

private lemma evalDNF_elimOne_iff (D : DNF) (env : ℕ → ℤ) :
    evalDNF env (elimOne D) ↔ ∃ x : ℤ, evalDNF (consEnv x env) D := by
  simp only [elimOne, evalDNF, List.mem_flatMap]
  constructor
  · rintro ⟨C', ⟨C, hCD, hC'⟩, hC'_eval⟩
    obtain ⟨x, hx⟩ := (evalDNF_elimOneConj_iff C env).mp ⟨C', hC', hC'_eval⟩
    exact ⟨x, C, hCD, hx⟩
  · rintro ⟨x, C, hCD, hx⟩
    obtain ⟨C', hC', hC'_eval⟩ := (evalDNF_elimOneConj_iff C env).mpr ⟨x, hx⟩
    exact ⟨C', ⟨C, hCD, hC'⟩, hC'_eval⟩

private lemma evalDNF_elimN_iff (n : ℕ) (D : DNF) (env : ℕ → ℤ) :
    evalDNF env (elimN n D) ↔ ∃ xs : Fin n → ℤ, evalDNF (prependFin xs env) D := by
  induction n generalizing D env with
  | zero =>
    simp only [elimN, Function.iterate_zero_apply]
    constructor
    · intro h
      refine ⟨Fin.elim0, ?_⟩
      rwa [prependFin_zero]
    · rintro ⟨xs, h⟩
      rwa [prependFin_zero] at h
  | succ n ih =>
    have hstep : elimN (n + 1) D = elimN n (elimOne D) := by
      simp [elimN, Function.iterate_succ_apply]
    rw [hstep, ih]
    constructor
    · rintro ⟨ys, hys⟩
      obtain ⟨x, hx⟩ := (evalDNF_elimOne_iff D (prependFin ys env)).mp hys
      rw [consEnv_prependFin] at hx
      exact ⟨Fin.cons x ys, hx⟩
    · rintro ⟨xs, hxs⟩
      refine ⟨Fin.tail xs, (evalDNF_elimOne_iff D _).mpr ⟨xs 0, ?_⟩⟩
      rw [consEnv_prependFin, Fin.cons_self_tail]
      exact hxs

/- ### Section 4: BVAS Semilinear Invariant Compiler -/

private def basisVec (k : ℕ) : List ℤ :=
  (List.range (k + 1)).map fun j => if j = k then (1 : ℤ) else 0

private def nonnegVars (m : ℕ) : Conj :=
  (List.range m).map fun k => (0, 1, basisVec k)

private def periodRow (periods : List (List ℕ)) (i : ℕ) : List ℤ :=
  periods.map fun p => ((p.getD i 0 : ℕ) : ℤ)

private def mkEqZero (c : ℤ) (a : List ℤ) : Conj :=
  [(0, c + 1, a), (0, 1 - c, a.map (- ·))]

private lemma dot_basisVec (k : ℕ) (env : ℕ → ℤ) : dot (basisVec k) env = env k := by
  rw [dot_eq_sum_range_length]
  have hlen : (basisVec k).length = k + 1 := by simp [basisVec]
  rw [hlen, Finset.sum_eq_single k]
  · simp [basisVec, List.getD_eq_getElem?_getD]
  · intro j hj hjk
    have hjlt : j < k + 1 := Finset.mem_range.mp hj
    simp [basisVec, List.getD_eq_getElem?_getD, hjlt, hjk]
  · intro hk
    exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self k)) hk

private lemma evalConj_nonnegVars (m : ℕ) (env : ℕ → ℤ) :
    evalConj env (nonnegVars m) ↔ ∀ k < m, (0 : ℤ) ≤ env k := by
  simp only [evalConj, nonnegVars, List.mem_map, List.mem_range, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, evalAtom, dot_basisVec]
  refine forall_congr' fun k => imp_congr_right fun _ => ?_
  omega

private lemma evalConj_nonnegVars_prependFin {m : ℕ} (xs : Fin m → ℤ) (env : ℕ → ℤ) :
    evalConj (prependFin xs env) (nonnegVars m) ↔ ∀ j : Fin m, (0 : ℤ) ≤ xs j := by
  rw [evalConj_nonnegVars]
  constructor
  · intro h j
    simpa [prependFin, j.2] using h j.1 j.2
  · intro h k hk
    simpa [prependFin, hk] using h ⟨k, hk⟩

private lemma evalConj_nonnegVars_prependFin2 {m1 m2 : ℕ} (x1 : Fin m1 → ℤ) (x2 : Fin m2 → ℤ)
    (env : ℕ → ℤ) :
    evalConj (prependFin x1 (prependFin x2 env)) (nonnegVars (m1 + m2)) ↔
      (∀ j1 : Fin m1, (0 : ℤ) ≤ x1 j1) ∧ (∀ j2 : Fin m2, (0 : ℤ) ≤ x2 j2) := by
  rw [evalConj_nonnegVars]
  constructor
  · intro h
    refine ⟨fun j1 => ?_, fun j2 => ?_⟩
    · have hlt : j1.1 < m1 + m2 := Nat.lt_of_lt_of_le j1.2 (Nat.le_add_right m1 m2)
      simpa [prependFin, j1.2] using h j1.1 hlt
    · have hlt : m1 + j2.1 < m1 + m2 := Nat.add_lt_add_left j2.2 m1
      have hnot : ¬ (m1 + j2.1 < m1) := by omega
      have hsub : m1 + j2.1 - m1 = j2.1 := Nat.add_sub_cancel_left m1 j2.1
      have h2 := h (m1 + j2.1) hlt
      simp only [prependFin, hnot, ↓reduceDIte, hsub, j2.2] at h2
      exact h2
  · rintro ⟨h1, h2⟩ k hk
    by_cases hk1 : k < m1
    · simpa [prependFin, hk1] using h1 ⟨k, hk1⟩
    · have hk2 : k - m1 < m2 := by omega
      simpa [prependFin, hk1, hk2] using h2 ⟨k - m1, hk2⟩

private lemma evalConj_mkEqZero (c : ℤ) (a : List ℤ) (env : ℕ → ℤ) :
    evalConj env (mkEqZero c a) ↔ c + dot a env = 0 := by
  simp only [evalConj, mkEqZero, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, evalAtom, dot_vecNeg]
  omega

private lemma dot_periodRow (periods : List (List ℕ)) (i : ℕ) (c : Fin periods.length → ℤ)
    (env : ℕ → ℤ) :
    dot (periodRow periods i) (prependFin c env) =
      ∑ j : Fin periods.length, c j * (((periods[j]).getD i 0 : ℕ) : ℤ) := by
  rw [dot_prependFin_eq_sum (periodRow periods i) (by simp [periodRow]) c env]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [periodRow, List.getD_eq_getElem?_getD, j.2]

private lemma dot_periodRow_neg (periods : List (List ℕ)) (i : ℕ) (c : Fin periods.length → ℤ)
    (env : ℕ → ℤ) :
    dot ((periodRow periods i).map (- ·)) (prependFin c env) =
      -(∑ j : Fin periods.length, c j * (((periods[j]).getD i 0 : ℕ) : ℤ)) := by
  rw [dot_vecNeg, dot_periodRow]

private def memBpConj (d : ℕ) (bp : List ℕ × List (List ℕ)) (v : List ℤ) : Conj :=
  nonnegVars bp.2.length ++
  (List.range d).flatMap fun i =>
    mkEqZero ((bp.1.getD i 0 : ℤ) - v.getD i 0) (periodRow bp.2 i)

private def checkMemBp (d : ℕ) (bp : List ℕ × List (List ℕ)) (v : List ℤ) : Bool :=
  evalClosedDNF (elimN bp.2.length [memBpConj d bp v])

private def checkMem (d : ℕ) (S : SemilinearCode) (v : List ℤ) : Bool :=
  S.any fun bp => checkMemBp d bp v

private def checkBases (d : ℕ) (S : SemilinearCode) (baseList : List (List ℤ)) : Bool :=
  baseList.all fun v => !nonnegList v || checkMem d S v

private def unaryMatchConj (d : ℕ) (bp bp' : List ℕ × List (List ℕ)) (r : List ℤ) : Conj :=
  nonnegVars bp'.2.length ++
  (List.range d).flatMap fun i =>
    mkEqZero ((bp'.1.getD i 0 : ℤ) - (bp.1.getD i 0 : ℤ) - r.getD i 0)
      (periodRow bp'.2 i ++ (periodRow bp.2 i).map (- ·))

private def unaryHitDNF (d : ℕ) (S : SemilinearCode) (bp : List ℕ × List (List ℕ))
    (r : List ℤ) : DNF :=
  S.flatMap fun bp' => elimN bp'.2.length [unaryMatchConj d bp bp' r]

private def unaryDomConj (d : ℕ) (bp : List ℕ × List (List ℕ)) (r : List ℤ) : Conj :=
  nonnegVars bp.2.length ++
  (List.range d).map fun i =>
    (0, (bp.1.getD i 0 : ℤ) + r.getD i 0 + 1, periodRow bp.2 i)

private def checkUnaryPair (d : ℕ) (S : SemilinearCode) (bp : List ℕ × List (List ℕ))
    (r : List ℤ) : Bool :=
  !evalClosedDNF (elimN bp.2.length (andDNF [unaryDomConj d bp r] (negDNF (unaryHitDNF d S bp r))))

private def checkUnary (d : ℕ) (S : SemilinearCode) (uList : List (List ℤ)) : Bool :=
  S.all fun bp => uList.all fun r => checkUnaryPair d S bp r

private def binaryMatchConj (d : ℕ) (bp1 bp2 bp' : List ℕ × List (List ℕ)) (r : List ℤ) : Conj :=
  nonnegVars bp'.2.length ++
  (List.range d).flatMap fun i =>
    mkEqZero ((bp'.1.getD i 0 : ℤ) - (bp1.1.getD i 0 : ℤ) - (bp2.1.getD i 0 : ℤ) - r.getD i 0)
      (periodRow bp'.2 i ++ ((periodRow bp1.2 i).map (- ·) ++ (periodRow bp2.2 i).map (- ·)))

private def binaryHitDNF (d : ℕ) (S : SemilinearCode) (bp1 bp2 : List ℕ × List (List ℕ))
    (r : List ℤ) : DNF :=
  S.flatMap fun bp' => elimN bp'.2.length [binaryMatchConj d bp1 bp2 bp' r]

private def binaryDomConj (d : ℕ) (bp1 bp2 : List ℕ × List (List ℕ)) (r : List ℤ) : Conj :=
  nonnegVars (bp1.2.length + bp2.2.length) ++
  (List.range d).map fun i =>
    (0, (bp1.1.getD i 0 : ℤ) + (bp2.1.getD i 0 : ℤ) + r.getD i 0 + 1,
      periodRow bp1.2 i ++ periodRow bp2.2 i)

private def checkBinaryTriple (d : ℕ) (S : SemilinearCode)
    (bp1 bp2 : List ℕ × List (List ℕ)) (r : List ℤ) : Bool :=
  !evalClosedDNF (elimN bp2.2.length (elimN bp1.2.length
    (andDNF [binaryDomConj d bp1 bp2 r] (negDNF (binaryHitDNF d S bp1 bp2 r)))))

private def checkBinary (d : ℕ) (S : SemilinearCode) (bList : List (List ℤ)) : Bool :=
  S.all fun bp1 => S.all fun bp2 => bList.all fun r => checkBinaryTriple d S bp1 bp2 r

private def decideInv (raw : RawInput) (S : SemilinearCode) : Bool :=
  let d := raw.1
  let baseList := raw.2.1
  let uList := raw.2.2.1
  let bList := raw.2.2.2.1
  let tVec := raw.2.2.2.2
  checkBases d S baseList &&
  checkUnary d S uList &&
  checkBinary d S bList &&
  !checkMem d S tVec

/- ### Section 5: Primrec Proofs for the Compiler -/

private lemma primrec_basisVec : Primrec basisVec :=
  Primrec.list_map (Primrec.list_range.comp Primrec.succ)
    (Primrec.ite (Primrec.eq.comp Primrec.snd Primrec.fst)
      (Primrec.const (1 : ℤ)) (Primrec.const (0 : ℤ))).to₂

private lemma primrec_nonnegVars : Primrec nonnegVars :=
  Primrec.list_map Primrec.list_range
    (Primrec.pair (Primrec.const (0 : ℕ))
      (Primrec.pair (Primrec.const (1 : ℤ)) (primrec_basisVec.comp Primrec.snd))).to₂

private lemma primrec_periodRow : Primrec₂ periodRow :=
  (Primrec.list_map Primrec.fst
    (primrec_int_ofNat.comp
      ((Primrec.list_getD (0 : ℕ)).comp Primrec.snd (Primrec.snd.comp Primrec.fst))).to₂).to₂

private lemma primrec_mkEqZero : Primrec₂ mkEqZero :=
  (Primrec.list_cons.comp
    (Primrec.pair (Primrec.const (0 : ℕ))
      (Primrec.pair (primrec_int_add.comp Primrec.fst (Primrec.const (1 : ℤ))) Primrec.snd))
    (Primrec.list_cons.comp
      (Primrec.pair (Primrec.const (0 : ℕ))
        (Primrec.pair (primrec_int_sub.comp (Primrec.const (1 : ℤ)) Primrec.fst)
          (primrec_vecNeg.comp Primrec.snd)))
      (Primrec.const []))).to₂

private lemma primrec_memBpConj :
    Primrec (fun p : (ℕ × (List ℕ × List (List ℕ))) × List ℤ => memBpConj p.1.1 p.1.2 p.2) := by
  let d : (ℕ × (List ℕ × List (List ℕ))) × List ℤ → ℕ := fun p => p.1.1
  let bp : (ℕ × (List ℕ × List (List ℕ))) × List ℤ → List ℕ × List (List ℕ) := fun p => p.1.2
  let v : (ℕ × (List ℕ × List (List ℕ))) × List ℤ → List ℤ := fun p => p.2
  have hd : Primrec d := Primrec.fst.comp Primrec.fst
  have hbp : Primrec bp := Primrec.snd.comp Primrec.fst
  have hv : Primrec v := Primrec.snd
  have hnonneg : Primrec fun p => nonnegVars (bp p).2.length :=
    primrec_nonnegVars.comp (Primrec.list_length.comp (Primrec.snd.comp hbp))
  have heqs : Primrec fun p =>
      (List.range (d p)).flatMap fun i =>
        mkEqZero (((bp p).1.getD i 0 : ℤ) - (v p).getD i 0) (periodRow (bp p).2 i) :=
    Primrec.list_flatMap (Primrec.list_range.comp hd)
      (primrec_mkEqZero.comp
        (primrec_int_sub.comp
          (primrec_int_ofNat.comp
            ((Primrec.list_getD (0 : ℕ)).comp
              (Primrec.fst.comp (hbp.comp Primrec.fst)) Primrec.snd))
          ((Primrec.list_getD (0 : ℤ)).comp (hv.comp Primrec.fst) Primrec.snd))
        (primrec_periodRow.comp (Primrec.snd.comp (hbp.comp Primrec.fst)) Primrec.snd)).to₂
  exact Primrec.list_append.comp hnonneg heqs

private lemma primrec_checkMemBp :
    Primrec (fun p : (ℕ × (List ℕ × List (List ℕ))) × List ℤ => checkMemBp p.1.1 p.1.2 p.2) :=
  primrec_evalClosedDNF.comp
    (primrec_elimN.comp
      (Primrec.list_length.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
      (Primrec.list_cons.comp primrec_memBpConj (Primrec.const [])))

private lemma primrec_checkMem :
    Primrec (fun p : (ℕ × SemilinearCode) × List ℤ => checkMem p.1.1 p.1.2 p.2) :=
  primrec_list_any (Primrec.snd.comp Primrec.fst)
    (primrec_checkMemBp.comp
      (Primrec.pair (Primrec.pair (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd)
        (Primrec.snd.comp Primrec.fst))).to₂

private lemma primrec_checkBases :
    Primrec (fun p : (ℕ × SemilinearCode) × List (List ℤ) => checkBases p.1.1 p.1.2 p.2) :=
  primrec_list_all Primrec.snd
    (Primrec.or.comp
      (Primrec.not.comp (primrec_nonnegList.comp Primrec.snd))
      (primrec_checkMem.comp (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd))).to₂

private lemma primrec_unaryMatchConj :
    Primrec (fun p : ((ℕ × (List ℕ × List (List ℕ))) × List ℤ) × (List ℕ × List (List ℕ)) =>
      unaryMatchConj p.1.1.1 p.1.1.2 p.2 p.1.2) := by
  let d := fun p : ((ℕ × (List ℕ × List (List ℕ))) × List ℤ) × (List ℕ × List (List ℕ)) => p.1.1.1
  let bp := fun p : ((ℕ × (List ℕ × List (List ℕ))) × List ℤ) × (List ℕ × List (List ℕ)) => p.1.1.2
  let r := fun p : ((ℕ × (List ℕ × List (List ℕ))) × List ℤ) × (List ℕ × List (List ℕ)) => p.1.2
  let bp' := fun p : ((ℕ × (List ℕ × List (List ℕ))) × List ℤ) × (List ℕ × List (List ℕ)) => p.2
  have hd : Primrec d := Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have hbp : Primrec bp := Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have hr : Primrec r := Primrec.snd.comp Primrec.fst
  have hbp' : Primrec bp' := Primrec.snd
  have hnonneg : Primrec fun p => nonnegVars (bp' p).2.length :=
    primrec_nonnegVars.comp (Primrec.list_length.comp (Primrec.snd.comp hbp'))
  have heqs : Primrec fun p =>
      (List.range (d p)).flatMap fun i =>
        mkEqZero (((bp' p).1.getD i 0 : ℤ) - ((bp p).1.getD i 0 : ℤ) - (r p).getD i 0)
          (periodRow (bp' p).2 i ++ (periodRow (bp p).2 i).map (- ·)) :=
    Primrec.list_flatMap (Primrec.list_range.comp hd)
      (primrec_mkEqZero.comp
        (primrec_int_sub.comp
          (primrec_int_sub.comp
            (primrec_int_ofNat.comp
              ((Primrec.list_getD (0 : ℕ)).comp (Primrec.fst.comp (hbp'.comp Primrec.fst)) Primrec.snd))
            (primrec_int_ofNat.comp
              ((Primrec.list_getD (0 : ℕ)).comp (Primrec.fst.comp (hbp.comp Primrec.fst)) Primrec.snd)))
          ((Primrec.list_getD (0 : ℤ)).comp (hr.comp Primrec.fst) Primrec.snd))
        (Primrec.list_append.comp
          (primrec_periodRow.comp (Primrec.snd.comp (hbp'.comp Primrec.fst)) Primrec.snd)
          (primrec_vecNeg.comp
            (primrec_periodRow.comp (Primrec.snd.comp (hbp.comp Primrec.fst)) Primrec.snd)))).to₂
  exact Primrec.list_append.comp hnonneg heqs

private lemma primrec_unaryHitDNF :
    Primrec (fun p : ((ℕ × SemilinearCode) × (List ℕ × List (List ℕ))) × List ℤ =>
      unaryHitDNF p.1.1.1 p.1.1.2 p.1.2 p.2) :=
  Primrec.list_flatMap (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
    (primrec_elimN.comp
      (Primrec.list_length.comp (Primrec.snd.comp Primrec.snd))
      (Primrec.list_cons.comp
        (primrec_unaryMatchConj.comp
          (Primrec.pair
            (Primrec.pair
              (Primrec.pair (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
                (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
              (Primrec.snd.comp Primrec.fst))
            Primrec.snd))
        (Primrec.const []))).to₂

private lemma primrec_unaryDomConj :
    Primrec (fun p : (ℕ × (List ℕ × List (List ℕ))) × List ℤ => unaryDomConj p.1.1 p.1.2 p.2) := by
  let d : (ℕ × (List ℕ × List (List ℕ))) × List ℤ → ℕ := fun p => p.1.1
  let bp : (ℕ × (List ℕ × List (List ℕ))) × List ℤ → List ℕ × List (List ℕ) := fun p => p.1.2
  let r : (ℕ × (List ℕ × List (List ℕ))) × List ℤ → List ℤ := fun p => p.2
  have hd : Primrec d := Primrec.fst.comp Primrec.fst
  have hbp : Primrec bp := Primrec.snd.comp Primrec.fst
  have hr : Primrec r := Primrec.snd
  have hnonneg : Primrec fun p => nonnegVars (bp p).2.length :=
    primrec_nonnegVars.comp (Primrec.list_length.comp (Primrec.snd.comp hbp))
  have hineqs : Primrec fun p =>
      (List.range (d p)).map fun i =>
        ((0 : ℕ), ((bp p).1.getD i 0 : ℤ) + (r p).getD i 0 + 1, periodRow (bp p).2 i) :=
    Primrec.list_map (Primrec.list_range.comp hd)
      (Primrec.pair (Primrec.const (0 : ℕ))
        (Primrec.pair
          (primrec_int_add.comp
            (primrec_int_add.comp
              (primrec_int_ofNat.comp
                ((Primrec.list_getD (0 : ℕ)).comp (Primrec.fst.comp (hbp.comp Primrec.fst)) Primrec.snd))
              ((Primrec.list_getD (0 : ℤ)).comp (hr.comp Primrec.fst) Primrec.snd))
            (Primrec.const (1 : ℤ)))
          (primrec_periodRow.comp (Primrec.snd.comp (hbp.comp Primrec.fst)) Primrec.snd))).to₂
  exact Primrec.list_append.comp hnonneg hineqs

private lemma primrec_checkUnaryPair :
    Primrec (fun p : ((ℕ × SemilinearCode) × (List ℕ × List (List ℕ))) × List ℤ =>
      checkUnaryPair p.1.1.1 p.1.1.2 p.1.2 p.2) :=
  Primrec.not.comp
    (primrec_evalClosedDNF.comp
      (primrec_elimN.comp
        (Primrec.list_length.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
        (primrec_andDNF.comp
          (Primrec.list_cons.comp
            (primrec_unaryDomConj.comp
              (Primrec.pair
                (Primrec.pair (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
                  (Primrec.snd.comp Primrec.fst))
                Primrec.snd))
            (Primrec.const []))
          (primrec_negDNF.comp primrec_unaryHitDNF))))

private lemma primrec_checkUnary :
    Primrec (fun p : (ℕ × SemilinearCode) × List (List ℤ) => checkUnary p.1.1 p.1.2 p.2) :=
  primrec_list_all (Primrec.snd.comp Primrec.fst)
    (primrec_list_all (Primrec.snd.comp Primrec.fst)
      (primrec_checkUnaryPair.comp
        (Primrec.pair
          (Primrec.pair (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
            (Primrec.snd.comp Primrec.fst))
          Primrec.snd)).to₂).to₂

private lemma primrec_binaryMatchConj :
    Primrec (fun p : (((ℕ × (List ℕ × List (List ℕ))) × (List ℕ × List (List ℕ))) × List ℤ) ×
        (List ℕ × List (List ℕ)) =>
      binaryMatchConj p.1.1.1.1 p.1.1.1.2 p.1.1.2 p.2 p.1.2) := by
  let P := (((ℕ × (List ℕ × List (List ℕ))) × (List ℕ × List (List ℕ))) × List ℤ) ×
    (List ℕ × List (List ℕ))
  let d : P → ℕ := fun p => p.1.1.1.1
  let bp1 : P → List ℕ × List (List ℕ) := fun p => p.1.1.1.2
  let bp2 : P → List ℕ × List (List ℕ) := fun p => p.1.1.2
  let r : P → List ℤ := fun p => p.1.2
  let bp' : P → List ℕ × List (List ℕ) := fun p => p.2
  have hd : Primrec d := Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
  have hbp1 : Primrec bp1 := Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
  have hbp2 : Primrec bp2 := Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have hr : Primrec r := Primrec.snd.comp Primrec.fst
  have hbp' : Primrec bp' := Primrec.snd
  have hnonneg : Primrec fun p => nonnegVars (bp' p).2.length :=
    primrec_nonnegVars.comp (Primrec.list_length.comp (Primrec.snd.comp hbp'))
  have heqs : Primrec fun p =>
      (List.range (d p)).flatMap fun i =>
        mkEqZero (((bp' p).1.getD i 0 : ℤ) - ((bp1 p).1.getD i 0 : ℤ) -
            ((bp2 p).1.getD i 0 : ℤ) - (r p).getD i 0)
          (periodRow (bp' p).2 i ++
            ((periodRow (bp1 p).2 i).map (- ·) ++ (periodRow (bp2 p).2 i).map (- ·))) :=
    Primrec.list_flatMap (Primrec.list_range.comp hd)
      (primrec_mkEqZero.comp
        (primrec_int_sub.comp
          (primrec_int_sub.comp
            (primrec_int_sub.comp
              (primrec_int_ofNat.comp
                ((Primrec.list_getD (0 : ℕ)).comp (Primrec.fst.comp (hbp'.comp Primrec.fst)) Primrec.snd))
              (primrec_int_ofNat.comp
                ((Primrec.list_getD (0 : ℕ)).comp (Primrec.fst.comp (hbp1.comp Primrec.fst)) Primrec.snd)))
            (primrec_int_ofNat.comp
              ((Primrec.list_getD (0 : ℕ)).comp (Primrec.fst.comp (hbp2.comp Primrec.fst)) Primrec.snd)))
          ((Primrec.list_getD (0 : ℤ)).comp (hr.comp Primrec.fst) Primrec.snd))
        (Primrec.list_append.comp
          (primrec_periodRow.comp (Primrec.snd.comp (hbp'.comp Primrec.fst)) Primrec.snd)
          (Primrec.list_append.comp
            (primrec_vecNeg.comp
              (primrec_periodRow.comp (Primrec.snd.comp (hbp1.comp Primrec.fst)) Primrec.snd))
            (primrec_vecNeg.comp
              (primrec_periodRow.comp (Primrec.snd.comp (hbp2.comp Primrec.fst)) Primrec.snd))))).to₂
  exact Primrec.list_append.comp hnonneg heqs

private lemma primrec_binaryHitDNF :
    Primrec (fun p : (((ℕ × SemilinearCode) × (List ℕ × List (List ℕ))) ×
        (List ℕ × List (List ℕ))) × List ℤ =>
      binaryHitDNF p.1.1.1.1 p.1.1.1.2 p.1.1.2 p.1.2 p.2) :=
  Primrec.list_flatMap (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
    (primrec_elimN.comp
      (Primrec.list_length.comp (Primrec.snd.comp Primrec.snd))
      (Primrec.list_cons.comp
        (primrec_binaryMatchConj.comp
          (Primrec.pair
            (Primrec.pair
              (Primrec.pair
                (Primrec.pair
                  (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))))
                  (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))))
                (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
              (Primrec.snd.comp Primrec.fst))
            Primrec.snd))
        (Primrec.const []))).to₂

private lemma primrec_binaryDomConj :
    Primrec (fun p : ((ℕ × (List ℕ × List (List ℕ))) × (List ℕ × List (List ℕ))) × List ℤ =>
      binaryDomConj p.1.1.1 p.1.1.2 p.1.2 p.2) := by
  let P := ((ℕ × (List ℕ × List (List ℕ))) × (List ℕ × List (List ℕ))) × List ℤ
  let d : P → ℕ := fun p => p.1.1.1
  let bp1 : P → List ℕ × List (List ℕ) := fun p => p.1.1.2
  let bp2 : P → List ℕ × List (List ℕ) := fun p => p.1.2
  let r : P → List ℤ := fun p => p.2
  have hd : Primrec d := Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have hbp1 : Primrec bp1 := Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have hbp2 : Primrec bp2 := Primrec.snd.comp Primrec.fst
  have hr : Primrec r := Primrec.snd
  have hnonneg : Primrec fun p => nonnegVars ((bp1 p).2.length + (bp2 p).2.length) :=
    primrec_nonnegVars.comp
      (Primrec.nat_add.comp
        (Primrec.list_length.comp (Primrec.snd.comp hbp1))
        (Primrec.list_length.comp (Primrec.snd.comp hbp2)))
  have hineqs : Primrec fun p =>
      (List.range (d p)).map fun i =>
        ((0 : ℕ), ((bp1 p).1.getD i 0 : ℤ) + ((bp2 p).1.getD i 0 : ℤ) + (r p).getD i 0 + 1,
          periodRow (bp1 p).2 i ++ periodRow (bp2 p).2 i) :=
    Primrec.list_map (Primrec.list_range.comp hd)
      (Primrec.pair (Primrec.const (0 : ℕ))
        (Primrec.pair
          (primrec_int_add.comp
            (primrec_int_add.comp
              (primrec_int_add.comp
                (primrec_int_ofNat.comp
                  ((Primrec.list_getD (0 : ℕ)).comp (Primrec.fst.comp (hbp1.comp Primrec.fst)) Primrec.snd))
                (primrec_int_ofNat.comp
                  ((Primrec.list_getD (0 : ℕ)).comp (Primrec.fst.comp (hbp2.comp Primrec.fst)) Primrec.snd)))
              ((Primrec.list_getD (0 : ℤ)).comp (hr.comp Primrec.fst) Primrec.snd))
            (Primrec.const (1 : ℤ)))
          (Primrec.list_append.comp
            (primrec_periodRow.comp (Primrec.snd.comp (hbp1.comp Primrec.fst)) Primrec.snd)
            (primrec_periodRow.comp (Primrec.snd.comp (hbp2.comp Primrec.fst)) Primrec.snd)))).to₂
  exact Primrec.list_append.comp hnonneg hineqs

private lemma primrec_checkBinaryTriple :
    Primrec (fun p : (((ℕ × SemilinearCode) × (List ℕ × List (List ℕ))) ×
        (List ℕ × List (List ℕ))) × List ℤ =>
      checkBinaryTriple p.1.1.1.1 p.1.1.1.2 p.1.1.2 p.1.2 p.2) :=
  Primrec.not.comp
    (primrec_evalClosedDNF.comp
      (primrec_elimN.comp
        (Primrec.list_length.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
        (primrec_elimN.comp
          (Primrec.list_length.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))))
          (primrec_andDNF.comp
            (Primrec.list_cons.comp
              (primrec_binaryDomConj.comp
                (Primrec.pair
                  (Primrec.pair
                    (Primrec.pair (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
                      (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
                    (Primrec.snd.comp Primrec.fst))
                  Primrec.snd))
              (Primrec.const []))
            (primrec_negDNF.comp primrec_binaryHitDNF)))))

private lemma primrec_checkBinary :
    Primrec (fun p : (ℕ × SemilinearCode) × List (List ℤ) => checkBinary p.1.1 p.1.2 p.2) :=
  primrec_list_all (Primrec.snd.comp Primrec.fst)
    (primrec_list_all (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
      (primrec_list_all (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
        (primrec_checkBinaryTriple.comp
          (Primrec.pair
            (Primrec.pair
              (Primrec.pair (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
                (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
              (Primrec.snd.comp Primrec.fst))
            Primrec.snd)).to₂).to₂).to₂

private lemma primrec_decideInv : Primrec₂ decideInv := by
  let d : RawInput × SemilinearCode → ℕ := fun p => p.1.1
  let baseList : RawInput × SemilinearCode → List (List ℤ) := fun p => p.1.2.1
  let uList : RawInput × SemilinearCode → List (List ℤ) := fun p => p.1.2.2.1
  let bList : RawInput × SemilinearCode → List (List ℤ) := fun p => p.1.2.2.2.1
  let tVec : RawInput × SemilinearCode → List ℤ := fun p => p.1.2.2.2.2
  let S : RawInput × SemilinearCode → SemilinearCode := fun p => p.2
  have hd : Primrec d := Primrec.fst.comp Primrec.fst
  have hbase : Primrec baseList := Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hu : Primrec uList := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have hb : Primrec bList :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
  have ht : Primrec tVec :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
  have hS : Primrec S := Primrec.snd
  have hdS : Primrec fun p => (d p, S p) := Primrec.pair hd hS
  have h1 : Primrec fun p => checkBases (d p) (S p) (baseList p) :=
    primrec_checkBases.comp (Primrec.pair hdS hbase)
  have h2 : Primrec fun p => checkUnary (d p) (S p) (uList p) :=
    primrec_checkUnary.comp (Primrec.pair hdS hu)
  have h3 : Primrec fun p => checkBinary (d p) (S p) (bList p) :=
    primrec_checkBinary.comp (Primrec.pair hdS hb)
  have h4 : Primrec fun p => !checkMem (d p) (S p) (tVec p) :=
    Primrec.not.comp (primrec_checkMem.comp (Primrec.pair hdS ht))
  exact (Primrec.and.comp (Primrec.and.comp (Primrec.and.comp h1 h2) h3) h4).to₂

/- ### Section 6: Semantic Correctness and `OMA.solution` -/

private def bpVec (d : ℕ) (bp : List ℕ × List (List ℕ)) (c : Fin bp.2.length → ℕ) : Fin d → ℤ :=
  fun i => (bp.1.getD i.1 0 : ℤ) +
    ∑ j : Fin bp.2.length, (c j : ℤ) * (((bp.2[j]).getD i.1 0 : ℕ) : ℤ)

private def memSL (d : ℕ) (S : SemilinearCode) (v : Fin d → ℤ) : Prop :=
  ∃ bp ∈ S, ∃ c : Fin bp.2.length → ℕ, ∀ i : Fin d, v i = bpVec d bp c i

private lemma exists_nat_iff_exists_nonneg_int {m : ℕ} (P : (Fin m → ℤ) → Prop) :
    (∃ c : Fin m → ℕ, P (fun j => (c j : ℤ))) ↔
      (∃ c : Fin m → ℤ, (∀ j : Fin m, (0 : ℤ) ≤ c j) ∧ P c) := by
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨fun j => (c j : ℤ), fun j => Int.natCast_nonneg _, hc⟩
  · rintro ⟨c, hnn, hc⟩
    refine ⟨fun j => (c j).toNat, ?_⟩
    have heq : (fun j => (((c j).toNat : ℕ) : ℤ)) = c := by
      funext j
      exact Int.toNat_of_nonneg (hnn j)
    rwa [heq]

private lemma checkMemBp_ofFn_iff {d : ℕ} (bp : List ℕ × List (List ℕ)) (v : Fin d → ℤ) :
    checkMemBp d bp (List.ofFn v) = true ↔
      ∃ c : Fin bp.2.length → ℕ, ∀ i : Fin d, v i = bpVec d bp c i := by
  rw [checkMemBp, evalClosedDNF_eq_true_iff, evalDNF_elimN_iff]
  simp only [evalDNF_singleton]
  dsimp only [bpVec]
  rw [exists_nat_iff_exists_nonneg_int (fun c => ∀ i : Fin d,
    v i = (bp.1.getD i.1 0 : ℤ) + ∑ j : Fin bp.2.length, c j * (((bp.2[j]).getD i.1 0 : ℕ) : ℤ))]
  refine exists_congr fun c => ?_
  simp only [memBpConj, evalConj, List.mem_append, List.mem_flatMap, List.mem_range]
  have hsplit : (∀ A, A ∈ nonnegVars bp.2.length ∨
      (∃ i < d, A ∈ mkEqZero ((bp.1.getD i 0 : ℤ) - (List.ofFn v).getD i 0) (periodRow bp.2 i)) →
        evalAtom (prependFin c (fun _ => 0)) A) ↔
      evalConj (prependFin c (fun _ => 0)) (nonnegVars bp.2.length) ∧
      ∀ i < d, evalConj (prependFin c (fun _ => 0))
        (mkEqZero ((bp.1.getD i 0 : ℤ) - (List.ofFn v).getD i 0) (periodRow bp.2 i)) := by
    constructor
    · intro h
      exact ⟨fun A hA => h A (Or.inl hA), fun i hi A hA => h A (Or.inr ⟨i, hi, hA⟩)⟩
    · rintro ⟨h1, h2⟩ A (hA | ⟨i, hi, hA⟩)
      · exact h1 A hA
      · exact h2 i hi A hA
  rw [hsplit, evalConj_nonnegVars_prependFin]
  refine and_congr_right fun _ => ?_
  constructor
  · intro h i
    have hi := (evalConj_mkEqZero _ _ _).mp (h i.1 i.2)
    rw [dot_periodRow] at hi
    have hv : (List.ofFn v).getD i.1 0 = v i := by simp [List.getD_eq_getElem?_getD, i.2]
    rw [hv] at hi
    linarith
  · intro h i hi
    rw [evalConj_mkEqZero, dot_periodRow]
    have hv : (List.ofFn v).getD i 0 = v ⟨i, hi⟩ := by simp [List.getD_eq_getElem?_getD, hi]
    rw [hv, h ⟨i, hi⟩]
    ring

private lemma checkMem_ofFn_iff {d : ℕ} (S : SemilinearCode) (v : Fin d → ℤ) :
    checkMem d S (List.ofFn v) = true ↔ memSL d S v := by
  simp only [checkMem, List.any_eq_true, checkMemBp_ofFn_iff, memSL]

private lemma checkBases_ofFn_iff {d : ℕ} (S : SemilinearCode) (bs : List (Fin d → ℤ)) :
    checkBases d S (bs.map List.ofFn) = true ↔ ∀ v ∈ bs, 0 ≤ v → memSL d S v := by
  simp only [checkBases, List.all_eq_true, List.mem_map, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, Bool.or_eq_true, Bool.not_eq_true', checkMem_ofFn_iff]
  refine forall_congr' fun v => imp_congr_right fun _ => ?_
  rw [← nonnegList_ofFn_iff]
  cases nonnegList (List.ofFn v) <;> simp

private lemma unaryHitDNF_iff {d : ℕ} (S : SemilinearCode) (bp : List ℕ × List (List ℕ))
    (r : Fin d → ℤ) (c : Fin bp.2.length → ℤ) :
    evalDNF (prependFin c (fun _ => 0)) (unaryHitDNF d S bp (List.ofFn r)) ↔
      memSL d S (fun i => (bp.1.getD i.1 0 : ℤ) +
        (∑ j : Fin bp.2.length, c j * (((bp.2[j]).getD i.1 0 : ℕ) : ℤ)) + r i) := by
  simp only [unaryHitDNF, evalDNF, List.mem_flatMap]
  constructor
  · rintro ⟨C', ⟨bp', hbp'S, hC'⟩, hC'_eval⟩
    have helim : evalDNF (prependFin c (fun _ => 0))
        (elimN bp'.2.length [unaryMatchConj d bp bp' (List.ofFn r)]) := ⟨C', hC', hC'_eval⟩
    rw [evalDNF_elimN_iff] at helim
    obtain ⟨c', hc'⟩ := helim
    simp only [evalDNF, List.mem_singleton, exists_eq_left] at hc'
    have hnn : ∀ l : Fin bp'.2.length, (0 : ℤ) ≤ c' l := by
      rw [← evalConj_nonnegVars_prependFin (env := prependFin c (fun _ => 0))]
      intro A hA
      exact hc' A (List.mem_append_left _ hA)
    refine ⟨bp', hbp'S, fun l => (c' l).toNat, fun i => ?_⟩
    have heq_at := (evalConj_mkEqZero _ _ _).mp fun A hA =>
      hc' A (List.mem_append_right _ (List.mem_flatMap.mpr ⟨i.1, List.mem_range.mpr i.2, hA⟩))
    rw [dot_append, dot_periodRow] at heq_at
    have hlen' : (periodRow bp'.2 i.1).length = bp'.2.length := by simp [periodRow]
    rw [hlen', prependFin_shift, dot_periodRow_neg] at heq_at
    have hr : (List.ofFn r).getD i.1 0 = r i := by simp [List.getD_eq_getElem?_getD, i.2]
    rw [hr] at heq_at
    have hsum_eq :
        ∑ l : Fin bp'.2.length, (((c' l).toNat : ℕ) : ℤ) * (((bp'.2[l]).getD i.1 0 : ℕ) : ℤ) =
        ∑ l : Fin bp'.2.length, c' l * (((bp'.2[l]).getD i.1 0 : ℕ) : ℤ) := by
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [Int.toNat_of_nonneg (hnn l)]
    dsimp only [bpVec]
    rw [hsum_eq]
    linarith
  · rintro ⟨bp', hbp'S, c', hc'⟩
    suffices helim : evalDNF (prependFin c (fun _ => 0))
        (elimN bp'.2.length [unaryMatchConj d bp bp' (List.ofFn r)]) by
      obtain ⟨C', hC', hC'_eval⟩ := helim
      exact ⟨C', ⟨bp', hbp'S, hC'⟩, hC'_eval⟩
    rw [evalDNF_elimN_iff]
    refine ⟨fun l => (c' l : ℤ), ?_⟩
    simp only [evalDNF, List.mem_singleton, exists_eq_left]
    intro A hA
    rcases List.mem_append.mp hA with hnn | heq
    · exact (evalConj_nonnegVars_prependFin (fun l => (c' l : ℤ)) _).mpr
        (fun l => Int.natCast_nonneg _) A hnn
    · obtain ⟨i, hi_mem, hA_eq⟩ := List.mem_flatMap.mp heq
      have hi : i < d := List.mem_range.mp hi_mem
      refine (evalConj_mkEqZero _ _ _).mpr ?_ A hA_eq
      rw [dot_append, dot_periodRow]
      have hlen' : (periodRow bp'.2 i).length = bp'.2.length := by simp [periodRow]
      rw [hlen', prependFin_shift, dot_periodRow_neg]
      have hr : (List.ofFn r).getD i 0 = r ⟨i, hi⟩ := by simp [List.getD_eq_getElem?_getD, hi]
      rw [hr]
      have hi_eq := hc' ⟨i, hi⟩
      dsimp only [bpVec] at hi_eq
      linarith

private lemma checkUnaryPair_ofFn_iff {d : ℕ} (S : SemilinearCode) (bp : List ℕ × List (List ℕ))
    (r : Fin d → ℤ) :
    checkUnaryPair d S bp (List.ofFn r) = true ↔
      ∀ c : Fin bp.2.length → ℕ, 0 ≤ bpVec d bp c + r → memSL d S (bpVec d bp c + r) := by
  simp only [checkUnaryPair, Bool.not_eq_true', Bool.eq_false_iff, ne_eq,
    evalClosedDNF_eq_true_iff, evalDNF_elimN_iff, evalDNF_andDNF, evalDNF_negDNF,
    evalDNF_singleton, not_exists, not_and, not_not]
  constructor
  · intro h c hcfg
    have hc_dom : evalConj (prependFin (fun j => (c j : ℤ)) (fun _ => 0))
        (unaryDomConj d bp (List.ofFn r)) := by
      intro A hA
      rcases List.mem_append.mp hA with hnn | hineq
      · exact (evalConj_nonnegVars_prependFin (fun j => (c j : ℤ)) _).mpr
          (fun j => Int.natCast_nonneg _) A hnn
      · obtain ⟨i, hi_mem, rfl⟩ := List.mem_map.mp hineq
        have hi : i < d := List.mem_range.mp hi_mem
        simp only [evalAtom, dot_periodRow]
        have hr : (List.ofFn r).getD i 0 = r ⟨i, hi⟩ := by simp [List.getD_eq_getElem?_getD, hi]
        rw [hr]
        have h0 : (0 : ℤ) ≤ (bpVec d bp c + r) ⟨i, hi⟩ := hcfg ⟨i, hi⟩
        simp only [Pi.add_apply, bpVec] at h0
        linarith
    have hhit := h (fun j => (c j : ℤ)) hc_dom
    exact (unaryHitDNF_iff S bp r (fun j => (c j : ℤ))).mp hhit
  · intro h c hc_dom
    have hnn : ∀ j : Fin bp.2.length, (0 : ℤ) ≤ c j := by
      rw [← evalConj_nonnegVars_prependFin (env := fun _ => 0)]
      intro A hA
      exact hc_dom A (List.mem_append_left _ hA)
    let cn : Fin bp.2.length → ℕ := fun j => (c j).toNat
    have hcn_eq : ∀ j : Fin bp.2.length, (cn j : ℤ) = c j := fun j => Int.toNat_of_nonneg (hnn j)
    have hcfg : 0 ≤ bpVec d bp cn + r := by
      intro i
      have hat := hc_dom _ (List.mem_append_right _
        (List.mem_map.mpr ⟨i.1, List.mem_range.mpr i.2, rfl⟩))
      simp only [evalAtom, dot_periodRow] at hat
      have hr : (List.ofFn r).getD i.1 0 = r i := by simp [List.getD_eq_getElem?_getD, i.2]
      rw [hr] at hat
      simp only [Pi.zero_apply, Pi.add_apply, bpVec, hcn_eq]
      linarith
    have hmem := h cn hcfg
    refine (unaryHitDNF_iff S bp r c).mpr ?_
    have hvec_eq : (fun i : Fin d => (bp.1.getD i.1 0 : ℤ) +
        (∑ j : Fin bp.2.length, c j * (((bp.2[j]).getD i.1 0 : ℕ) : ℤ)) + r i) =
        bpVec d bp cn + r := by
      funext i
      simp only [Pi.add_apply, bpVec, hcn_eq]
    rw [hvec_eq]
    exact hmem

private lemma checkUnary_ofFn_iff {d : ℕ} (S : SemilinearCode) (us : List (Fin d → ℤ)) :
    checkUnary d S (us.map List.ofFn) = true ↔
      ∀ v r, memSL d S v → r ∈ us → 0 ≤ v + r → memSL d S (v + r) := by
  simp only [checkUnary, List.all_eq_true, List.mem_map, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, checkUnaryPair_ofFn_iff]
  constructor
  · intro h v r ⟨bp, hbpS, c, hv⟩ hr hcfg
    have hveq : v = bpVec d bp c := funext hv
    subst hveq
    exact h bp hbpS r hr c hcfg
  · intro h bp hbpS r hr c hcfg
    exact h (bpVec d bp c) r ⟨bp, hbpS, c, fun _ => rfl⟩ hr hcfg

private lemma binaryHitDNF_iff {d : ℕ} (S : SemilinearCode)
    (bp1 bp2 : List ℕ × List (List ℕ)) (r : Fin d → ℤ)
    (c1 : Fin bp1.2.length → ℤ) (c2 : Fin bp2.2.length → ℤ) :
    evalDNF (prependFin c1 (prependFin c2 (fun _ => 0))) (binaryHitDNF d S bp1 bp2 (List.ofFn r)) ↔
      memSL d S (fun i =>
        ((bp1.1.getD i.1 0 : ℤ) + ∑ j : Fin bp1.2.length, c1 j * (((bp1.2[j]).getD i.1 0 : ℕ) : ℤ)) +
        ((bp2.1.getD i.1 0 : ℤ) + ∑ j : Fin bp2.2.length, c2 j * (((bp2.2[j]).getD i.1 0 : ℕ) : ℤ)) +
        r i) := by
  simp only [binaryHitDNF, evalDNF, List.mem_flatMap]
  constructor
  · rintro ⟨C', ⟨bp', hbp'S, hC'⟩, hC'_eval⟩
    have helim : evalDNF (prependFin c1 (prependFin c2 (fun _ => 0)))
        (elimN bp'.2.length [binaryMatchConj d bp1 bp2 bp' (List.ofFn r)]) := ⟨C', hC', hC'_eval⟩
    rw [evalDNF_elimN_iff] at helim
    obtain ⟨c', hc'⟩ := helim
    simp only [evalDNF, List.mem_singleton, exists_eq_left] at hc'
    have hnn : ∀ l : Fin bp'.2.length, (0 : ℤ) ≤ c' l := by
      rw [← evalConj_nonnegVars_prependFin (env := prependFin c1 (prependFin c2 (fun _ => 0)))]
      intro A hA
      exact hc' A (List.mem_append_left _ hA)
    refine ⟨bp', hbp'S, fun l => (c' l).toNat, fun i => ?_⟩
    have heq_at := (evalConj_mkEqZero _ _ _).mp fun A hA =>
      hc' A (List.mem_append_right _ (List.mem_flatMap.mpr ⟨i.1, List.mem_range.mpr i.2, hA⟩))
    rw [dot_append, dot_periodRow] at heq_at
    have hlen' : (periodRow bp'.2 i.1).length = bp'.2.length := by simp [periodRow]
    rw [hlen', prependFin_shift, dot_append, dot_periodRow_neg] at heq_at
    have hlen1 : ((periodRow bp1.2 i.1).map (- ·)).length = bp1.2.length := by simp [periodRow]
    rw [hlen1, prependFin_shift, dot_periodRow_neg] at heq_at
    have hr : (List.ofFn r).getD i.1 0 = r i := by simp [List.getD_eq_getElem?_getD, i.2]
    rw [hr] at heq_at
    have hsum_eq :
        ∑ l : Fin bp'.2.length, (((c' l).toNat : ℕ) : ℤ) * (((bp'.2[l]).getD i.1 0 : ℕ) : ℤ) =
        ∑ l : Fin bp'.2.length, c' l * (((bp'.2[l]).getD i.1 0 : ℕ) : ℤ) := by
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [Int.toNat_of_nonneg (hnn l)]
    dsimp only [bpVec]
    rw [hsum_eq]
    linarith
  · rintro ⟨bp', hbp'S, c', hc'⟩
    suffices helim : evalDNF (prependFin c1 (prependFin c2 (fun _ => 0)))
        (elimN bp'.2.length [binaryMatchConj d bp1 bp2 bp' (List.ofFn r)]) by
      obtain ⟨C', hC', hC'_eval⟩ := helim
      exact ⟨C', ⟨bp', hbp'S, hC'⟩, hC'_eval⟩
    rw [evalDNF_elimN_iff]
    refine ⟨fun l => (c' l : ℤ), ?_⟩
    simp only [evalDNF, List.mem_singleton, exists_eq_left]
    intro A hA
    rcases List.mem_append.mp hA with hnn | heq
    · exact (evalConj_nonnegVars_prependFin (fun l => (c' l : ℤ)) _).mpr
        (fun l => Int.natCast_nonneg _) A hnn
    · obtain ⟨i, hi_mem, hA_eq⟩ := List.mem_flatMap.mp heq
      have hi : i < d := List.mem_range.mp hi_mem
      refine (evalConj_mkEqZero _ _ _).mpr ?_ A hA_eq
      rw [dot_append, dot_periodRow]
      have hlen' : (periodRow bp'.2 i).length = bp'.2.length := by simp [periodRow]
      rw [hlen', prependFin_shift, dot_append, dot_periodRow_neg]
      have hlen1 : ((periodRow bp1.2 i).map (- ·)).length = bp1.2.length := by simp [periodRow]
      rw [hlen1, prependFin_shift, dot_periodRow_neg]
      have hr : (List.ofFn r).getD i 0 = r ⟨i, hi⟩ := by simp [List.getD_eq_getElem?_getD, hi]
      rw [hr]
      have hi_eq := hc' ⟨i, hi⟩
      dsimp only [bpVec] at hi_eq
      linarith

private lemma checkBinaryTriple_ofFn_iff {d : ℕ} (S : SemilinearCode)
    (bp1 bp2 : List ℕ × List (List ℕ)) (r : Fin d → ℤ) :
    checkBinaryTriple d S bp1 bp2 (List.ofFn r) = true ↔
      ∀ c1 : Fin bp1.2.length → ℕ, ∀ c2 : Fin bp2.2.length → ℕ,
        0 ≤ bpVec d bp1 c1 + bpVec d bp2 c2 + r →
        memSL d S (bpVec d bp1 c1 + bpVec d bp2 c2 + r) := by
  simp only [checkBinaryTriple, Bool.not_eq_true', Bool.eq_false_iff, ne_eq,
    evalClosedDNF_eq_true_iff, evalDNF_elimN_iff, evalDNF_andDNF, evalDNF_negDNF,
    evalDNF_singleton, not_exists, not_and, not_not]
  constructor
  · intro h c1 c2 hcfg
    have hc_dom : evalConj (prependFin (fun j => (c1 j : ℤ)) (prependFin (fun j => (c2 j : ℤ)) (fun _ => 0)))
        (binaryDomConj d bp1 bp2 (List.ofFn r)) := by
      intro A hA
      rcases List.mem_append.mp hA with hnn | hineq
      · exact (evalConj_nonnegVars_prependFin2 (fun j => (c1 j : ℤ)) (fun j => (c2 j : ℤ)) _).mpr
          ⟨fun j => Int.natCast_nonneg _, fun j => Int.natCast_nonneg _⟩ A hnn
      · obtain ⟨i, hi_mem, rfl⟩ := List.mem_map.mp hineq
        have hi : i < d := List.mem_range.mp hi_mem
        simp only [evalAtom, dot_append, dot_periodRow]
        have hlen1 : (periodRow bp1.2 i).length = bp1.2.length := by simp [periodRow]
        rw [hlen1, prependFin_shift, dot_periodRow]
        have hr : (List.ofFn r).getD i 0 = r ⟨i, hi⟩ := by simp [List.getD_eq_getElem?_getD, hi]
        rw [hr]
        have h0 : (0 : ℤ) ≤ (bpVec d bp1 c1 + bpVec d bp2 c2 + r) ⟨i, hi⟩ := hcfg ⟨i, hi⟩
        simp only [Pi.add_apply, bpVec] at h0
        linarith
    have hhit := h (fun j => (c2 j : ℤ)) (fun j => (c1 j : ℤ)) hc_dom
    exact (binaryHitDNF_iff S bp1 bp2 r (fun j => (c1 j : ℤ)) (fun j => (c2 j : ℤ))).mp hhit
  · intro h c2 c1 hc_dom
    have hnn : (∀ j1 : Fin bp1.2.length, (0 : ℤ) ≤ c1 j1) ∧
        (∀ j2 : Fin bp2.2.length, (0 : ℤ) ≤ c2 j2) := by
      rw [← evalConj_nonnegVars_prependFin2 (env := fun _ => 0)]
      intro A hA
      exact hc_dom A (List.mem_append_left _ hA)
    let cn1 : Fin bp1.2.length → ℕ := fun j => (c1 j).toNat
    let cn2 : Fin bp2.2.length → ℕ := fun j => (c2 j).toNat
    have hcn1 : ∀ j, (cn1 j : ℤ) = c1 j := fun j => Int.toNat_of_nonneg (hnn.1 j)
    have hcn2 : ∀ j, (cn2 j : ℤ) = c2 j := fun j => Int.toNat_of_nonneg (hnn.2 j)
    have hcfg : 0 ≤ bpVec d bp1 cn1 + bpVec d bp2 cn2 + r := by
      intro i
      have hat := hc_dom _ (List.mem_append_right _
        (List.mem_map.mpr ⟨i.1, List.mem_range.mpr i.2, rfl⟩))
      simp only [evalAtom, dot_append, dot_periodRow] at hat
      have hlen1 : (periodRow bp1.2 i.1).length = bp1.2.length := by simp [periodRow]
      rw [hlen1, prependFin_shift, dot_periodRow] at hat
      have hr : (List.ofFn r).getD i.1 0 = r i := by simp [List.getD_eq_getElem?_getD, i.2]
      rw [hr] at hat
      simp only [Pi.zero_apply, Pi.add_apply, bpVec, hcn1, hcn2]
      linarith
    have hmem := h cn1 cn2 hcfg
    refine (binaryHitDNF_iff S bp1 bp2 r c1 c2).mpr ?_
    have hvec_eq : (fun i : Fin d =>
        ((bp1.1.getD i.1 0 : ℤ) + ∑ j : Fin bp1.2.length, c1 j * (((bp1.2[j]).getD i.1 0 : ℕ) : ℤ)) +
        ((bp2.1.getD i.1 0 : ℤ) + ∑ j : Fin bp2.2.length, c2 j * (((bp2.2[j]).getD i.1 0 : ℕ) : ℤ)) +
        r i) = bpVec d bp1 cn1 + bpVec d bp2 cn2 + r := by
      funext i
      simp only [Pi.add_apply, bpVec, hcn1, hcn2]
    rw [hvec_eq]
    exact hmem

private lemma checkBinary_ofFn_iff {d : ℕ} (S : SemilinearCode) (bs : List (Fin d → ℤ)) :
    checkBinary d S (bs.map List.ofFn) = true ↔
      ∀ v1 v2 r, memSL d S v1 → memSL d S v2 → r ∈ bs → 0 ≤ v1 + v2 + r → memSL d S (v1 + v2 + r) := by
  simp only [checkBinary, List.all_eq_true, List.mem_map, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, checkBinaryTriple_ofFn_iff]
  constructor
  · intro h v1 v2 r ⟨bp1, hbp1S, c1, hv1⟩ ⟨bp2, hbp2S, c2, hv2⟩ hr hcfg
    have h1 : v1 = bpVec d bp1 c1 := funext hv1
    have h2 : v2 = bpVec d bp2 c2 := funext hv2
    subst h1; subst h2
    exact h bp1 hbp1S bp2 hbp2S r hr c1 c2 hcfg
  · intro h bp1 hbp1S bp2 hbp2S r hr c1 c2 hcfg
    exact h (bpVec d bp1 c1) (bpVec d bp2 c2) r
      ⟨bp1, hbp1S, c1, fun _ => rfl⟩ ⟨bp2, hbp2S, c2, fun _ => rfl⟩ hr hcfg

private def encodeInput (p : Input) : RawInput :=
  (p.1, p.2.1.1.map List.ofFn, p.2.1.unaryRules.map List.ofFn,
    p.2.1.binaryRules.map List.ofFn, List.ofFn p.2.2)

private lemma primrec_encodeInput : Primrec encodeInput :=
  Primrec.encode_iff.mp Primrec.encode

private lemma decideInv_encodeInput_iff (x : Input × SemilinearCode) :
    decideInv (encodeInput x.1) x.2 = true ↔
      let d := x.1.1
      let b := x.1.2.1
      let t := x.1.2.2
      let mem : (Fin d → ℤ) → Prop := fun v =>
        ∃ bp ∈ x.2, ∃ c : Fin bp.2.length → ℕ,
          ∀ i : Fin d, v i = (bp.1.getD i.1 0 : ℤ) +
            ∑ j : Fin bp.2.length, (c j : ℤ) * (((bp.2[j]).getD i.1 0 : ℕ) : ℤ)
      (∀ v ∈ b.1, 0 ≤ v → mem v) ∧
      (∀ v r, mem v → r ∈ b.unaryRules → 0 ≤ v + r → mem (v + r)) ∧
      (∀ v₁ v₂ r, mem v₁ → mem v₂ → r ∈ b.binaryRules → 0 ≤ v₁ + v₂ + r → mem (v₁ + v₂ + r)) ∧
      ¬ mem t := by
  rcases x with ⟨⟨d, b, t⟩, S⟩
  simp only [decideInv, encodeInput, Bool.and_eq_true, Bool.not_eq_true', Bool.eq_false_iff, ne_eq,
    checkBases_ofFn_iff, checkUnary_ofFn_iff, checkBinary_ofFn_iff, checkMem_ofFn_iff,
    and_assoc]
  rfl

private theorem h1_proof : OMA.R_BranchingVAS_reachability_decidable_R1.H1 := by
  rw [OMA.R_BranchingVAS_reachability_decidable_R1.H1, ComputablePred.computable_iff]
  refine ⟨fun x => decideInv (encodeInput x.1) x.2, ?_, ?_⟩
  · exact (primrec_decideInv.comp (primrec_encodeInput.comp Primrec.fst) Primrec.snd).to_comp
  · funext x
    exact propext (decideInv_encodeInput_iff x).symm

end BVASH1

theorem OMA.solution : OMA.R_BranchingVAS_reachability_decidable_R1.H1 :=
  BVASH1.h1_proof
