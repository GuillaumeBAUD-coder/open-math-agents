import OMAReductions.R_BranchingVAS_reachability_decidable_R1
import Mathlib.Computability.RE
import Mathlib.Computability.Primrec.List
import Mathlib.Tactic

/-!
# Uniform Computability of Separating Semilinear Inductive Invariants (`BranchingVAS.R1.H1`)

We prove `OMA.R_BranchingVAS_reachability_decidable_R1.H1` by implementing a fully
primitive-recursive (`Primrec`) quantifier-elimination decision procedure for Presburger
arithmetic over `ℤ` (Cooper's algorithm) and applying it uniformly to all four clauses of
a BVAS separating semilinear inductive invariant:

1. **Primitive-recursive `ℤ` and `List` arithmetic:** `ofNat`, `natAbs`, `nonneg`, `pos`,
   `neg`, `add`, `sub`, `mul`, natural divisibility `(d : ℤ) ∣ z`, plus `List.all`/`List.any`.
2. **Flat positive DNF Presburger formulas:** Using existing `Primcodable` types directly:
   - `Lin := ℤ × List ℤ` representing `c + ∑ i, cs[i] * env[i]`
   - `Atom := ℕ × Lin` where `(0, e)` denotes `0 ≤ e` and `(d + 1, e)` denotes `(d + 1) ∣ e`
   - `Conj := List Atom` and `DNF := List Conj`
   with `Primrec` negation (`¬(0 ≤ t) ↔ 0 ≤ -t - 1`; `¬((d+1) ∣ t) ↔ ∨_{r=1..d} (d+1) ∣ (t+r)`),
   conjunction (`andDNF`), and closed evaluation (`evalDNF0`).
3. **Cooper single-variable quantifier elimination:** On each conjunction, scale nonzero
   leading coefficients to their exact product `L ≥ 1` (no `gcd`/`lcm`), split into
   `freeAtoms`, `lowerBounds`, `upperBounds`, and `divBounds` (including `L ∣ y`), take
   modulus product `M ≥ 1`, and replace `∃ y` by testing `j ∈ 0..M-1` (when `lowers = []`,
   dropping `uppers`) or `b₀ + j` for `b₀ ∈ lowers, j ∈ 0..M-1` (when `lowers ≠ []`).
   Iterate via `Primrec.nat_iterate`.
4. **Unified BVAS invariant check:** All four clauses (base inclusion, unary closure, binary
   closure, target exclusion — using that `mem_S t → 0 ≤ t`) reduce to one `Primrec`
   universal-existential inclusion predicate `checkIncludedBool d base₀ P₀ S`.

Credit: @yhay81
-/

namespace BranchingVASR1H1

open BranchingVAS
open scoped BigOperators

/- ### Part 1: Primitive-recursive integer and list combinators -/

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
  Primrec.encode_iff.mp (Primrec.nat_double.of_eq fun _ => rfl)

private lemma natAbs_ofNat (m : ℕ) : (Int.ofNat m).natAbs = m := rfl

private lemma primrec_int_natAbs : Primrec Int.natAbs := by
  let h := Primrec.cond (Primrec.nat_bodd.comp (Primrec.encode (α := ℤ)))
    (Primrec.succ.comp (Primrec.nat_div2.comp (Primrec.encode (α := ℤ))))
    (Primrec.nat_div2.comp (Primrec.encode (α := ℤ)))
  refine h.of_eq fun z => ?_
  cases z with
  | ofNat m =>
    simp only [encode_int_ofNat, bodd_two_mul, div2_two_mul, Bool.cond_false, natAbs_ofNat]
  | negSucc n =>
    simp only [encode_int_negSucc, bodd_two_mul_add_one, div2_two_mul_add_one, Bool.cond_true,
      Int.natAbs_negSucc, Nat.succ_eq_add_one]

private lemma primrec_int_nonneg : Primrec (fun z : ℤ => decide ((0 : ℤ) ≤ z)) := by
  have h : ∀ z : ℤ, (!(Encodable.encode z).bodd) = decide ((0 : ℤ) ≤ z) := by
    rintro (m | n)
    · rw [encode_int_ofNat, bodd_two_mul]
      simp [Int.ofNat_eq_natCast]
    · rw [encode_int_negSucc, bodd_two_mul_add_one]
      simp [show ¬ ((0 : ℤ) ≤ Int.negSucc n) by omega]
  exact (Primrec.not.comp (Primrec.nat_bodd.comp Primrec.encode)).of_eq h

private lemma primrec_int_pos : Primrec (fun z : ℤ => decide ((0 : ℤ) < z)) := by
  have h : Primrec (fun z : ℤ => decide ((0 : ℤ) ≤ z) && !(z == (0 : ℤ))) :=
    Primrec.and.comp primrec_int_nonneg
      (Primrec.not.comp (Primrec.beq.comp Primrec.id (Primrec.const (0 : ℤ))))
  refine h.of_eq fun z => ?_
  by_cases hz : 0 < z
  · have h1 : (0 : ℤ) ≤ z := le_of_lt hz
    have h2 : z ≠ 0 := ne_of_gt hz
    simp [hz, h1, h2]
  · by_cases h0 : z = 0
    · subst h0; simp
    · have h1 : ¬ ((0 : ℤ) ≤ z) := by omega
      simp [hz, h1]

private lemma primrec_int_neg : Primrec (Neg.neg : ℤ → ℤ) := by
  rw [← Primrec.encode_iff]
  let e : ℤ → ℕ := Encodable.encode
  let b : ℤ → Bool := fun z => (e z).bodd
  let x : ℤ → ℕ := fun z => (e z).div2
  have he : Primrec e := Primrec.encode
  have hb : Primrec b := Primrec.nat_bodd.comp he
  have hx : Primrec x := Primrec.nat_div2.comp he
  have hpos : Primrec (fun z : ℤ => cond (x z == 0) 0 (2 * (x z - 1) + 1)) :=
    Primrec.cond (Primrec.beq.comp hx (Primrec.const 0)) (Primrec.const 0)
      (Primrec.nat_double_succ.comp (Primrec.pred.comp hx))
  have hneg : Primrec (fun z : ℤ => 2 * (x z + 1)) :=
    Primrec.nat_double.comp (Primrec.succ.comp hx)
  refine (Primrec.cond hb hneg hpos).of_eq fun z => ?_
  cases z with
  | ofNat m =>
    cases m with
    | zero =>
      have heq : -(Int.ofNat 0) = Int.ofNat 0 := rfl
      rw [heq]
      simp only [b, x, e, encode_int_ofNat, bodd_two_mul, div2_two_mul, Bool.cond_false,
        beq_self_eq_true, Bool.cond_true]
    | succ k =>
      have heq : -(Int.ofNat (k + 1)) = Int.negSucc k := rfl
      rw [heq]
      simp only [b, x, e, encode_int_ofNat, encode_int_negSucc, bodd_two_mul, div2_two_mul,
        Bool.cond_false, Nat.add_sub_cancel]
      rw [show (k + 1 == 0) = false from beq_false_of_ne (Nat.succ_ne_zero k), Bool.cond_false]
  | negSucc n =>
    have heq : -(Int.negSucc n) = Int.ofNat (n + 1) := rfl
    rw [heq]
    simp only [b, x, e, encode_int_ofNat, encode_int_negSucc, bodd_two_mul_add_one,
      div2_two_mul_add_one, Bool.cond_true]

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
  have hff : Primrec (fun p => 2 * (x1 p + x2 p)) :=
    Primrec.nat_double.comp (Primrec.nat_add.comp hx1 hx2)
  have htt : Primrec (fun p => 2 * (x1 p + x2 p + 1) + 1) :=
    Primrec.nat_double_succ.comp (Primrec.succ.comp (Primrec.nat_add.comp hx1 hx2))
  have hft : Primrec (fun p => if x2 p < x1 p then 2 * (x1 p - (x2 p + 1)) else 2 * (x2 p - x1 p) + 1) :=
    Primrec.ite (Primrec.nat_lt.comp hx2 hx1)
      (Primrec.nat_double.comp (Primrec.nat_sub.comp hx1 (Primrec.succ.comp hx2)))
      (Primrec.nat_double_succ.comp (Primrec.nat_sub.comp hx2 hx1))
  have htf : Primrec (fun p => if x1 p < x2 p then 2 * (x2 p - (x1 p + 1)) else 2 * (x1 p - x2 p) + 1) :=
    Primrec.ite (Primrec.nat_lt.comp hx1 hx2)
      (Primrec.nat_double.comp (Primrec.nat_sub.comp hx2 (Primrec.succ.comp hx1)))
      (Primrec.nat_double_succ.comp (Primrec.nat_sub.comp hx1 hx2))
  have hcomb : Primrec (fun p : ℤ × ℤ =>
      cond (b1 p) (cond (b2 p) (2 * (x1 p + x2 p + 1) + 1)
                               (if x1 p < x2 p then 2 * (x2 p - (x1 p + 1)) else 2 * (x1 p - x2 p) + 1))
                  (cond (b2 p) (if x2 p < x1 p then 2 * (x1 p - (x2 p + 1)) else 2 * (x2 p - x1 p) + 1)
                               (2 * (x1 p + x2 p)))) :=
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
  (primrec_int_add.comp₂ Primrec₂.left (primrec_int_neg.comp₂ Primrec₂.right)).of_eq fun a b =>
    (sub_eq_add_neg a b).symm

private lemma primrec_int_mul : Primrec₂ ((· * ·) : ℤ → ℤ → ℤ) := by
  rw [Primrec₂, ← Primrec.encode_iff]
  let prodAbs : ℤ × ℤ → ℕ := fun p => p.1.natAbs * p.2.natAbs
  let sameSign : ℤ × ℤ → Bool := fun p => (Encodable.encode p.1).bodd == (Encodable.encode p.2).bodd
  have hp : Primrec prodAbs :=
    Primrec.nat_mul.comp (primrec_int_natAbs.comp Primrec.fst) (primrec_int_natAbs.comp Primrec.snd)
  have hs : Primrec sameSign :=
    Primrec.beq.comp (Primrec.nat_bodd.comp (Primrec.encode.comp Primrec.fst))
      (Primrec.nat_bodd.comp (Primrec.encode.comp Primrec.snd))
  have hcomb : Primrec (fun p : ℤ × ℤ =>
      cond (prodAbs p == 0) 0
        (cond (sameSign p) (2 * prodAbs p) (2 * (prodAbs p - 1) + 1))) :=
    Primrec.cond (Primrec.beq.comp hp (Primrec.const 0)) (Primrec.const 0)
      (Primrec.cond hs (Primrec.nat_double.comp hp)
        (Primrec.nat_double_succ.comp (Primrec.pred.comp hp)))
  refine hcomb.of_eq fun ⟨z1, z2⟩ => ?_
  cases z1 with
  | ofNat m1 =>
    cases z2 with
    | ofNat m2 =>
      have heq : Int.ofNat m1 * Int.ofNat m2 = Int.ofNat (m1 * m2) := rfl
      rw [heq]
      by_cases hm : m1 * m2 = 0
      · simp only [prodAbs, sameSign, natAbs_ofNat, encode_int_ofNat, bodd_two_mul, hm,
          beq_self_eq_true, Bool.cond_true, Nat.mul_zero]
      · simp only [prodAbs, sameSign, natAbs_ofNat, encode_int_ofNat, bodd_two_mul,
          beq_self_eq_true, Bool.cond_true]
        rw [show (m1 * m2 == 0) = false from beq_false_of_ne hm, Bool.cond_false]
    | negSucc n2 =>
      by_cases hm : m1 = 0
      · subst hm
        have heq : Int.ofNat 0 * Int.negSucc n2 = Int.ofNat 0 := by
          rw [Int.ofNat_eq_natCast, Nat.cast_zero, zero_mul]
        rw [heq]
        simp only [prodAbs, natAbs_ofNat, Int.natAbs_negSucc, Nat.zero_mul, beq_self_eq_true,
          Bool.cond_true, encode_int_ofNat, Nat.mul_zero]
      · have hpos : m1 * (n2 + 1) ≠ 0 := Nat.mul_ne_zero hm (Nat.succ_ne_zero n2)
        have heq : Int.ofNat m1 * Int.negSucc n2 = Int.negSucc (m1 * (n2 + 1) - 1) := by
          have h1 : 1 ≤ m1 * (n2 + 1) := Nat.pos_of_ne_zero hpos
          rw [Int.ofNat_eq_natCast, Int.negSucc_eq, Int.negSucc_eq]
          have : ((m1 * (n2 + 1) - 1 : ℕ) : ℤ) + 1 = (m1 : ℤ) * ((n2 : ℤ) + 1) := by
            rw [Nat.cast_sub h1]; push_cast; ring
          linarith
        rw [heq]
        simp only [prodAbs, sameSign, natAbs_ofNat, Int.natAbs_negSucc, encode_int_ofNat,
          encode_int_negSucc, bodd_two_mul, bodd_two_mul_add_one, Nat.succ_eq_add_one]
        rw [show (m1 * (n2 + 1) == 0) = false from beq_false_of_ne hpos, Bool.cond_false]
        rfl
  | negSucc n1 =>
    cases z2 with
    | ofNat m2 =>
      by_cases hm : m2 = 0
      · subst hm
        have heq : Int.negSucc n1 * Int.ofNat 0 = Int.ofNat 0 := by
          rw [Int.ofNat_eq_natCast, Nat.cast_zero, mul_zero]
        rw [heq]
        simp only [prodAbs, natAbs_ofNat, Int.natAbs_negSucc, Nat.mul_zero, beq_self_eq_true,
          Bool.cond_true, encode_int_ofNat]
      · have hpos : (n1 + 1) * m2 ≠ 0 := Nat.mul_ne_zero (Nat.succ_ne_zero n1) hm
        have heq : Int.negSucc n1 * Int.ofNat m2 = Int.negSucc ((n1 + 1) * m2 - 1) := by
          have h1 : 1 ≤ (n1 + 1) * m2 := Nat.pos_of_ne_zero hpos
          rw [Int.ofNat_eq_natCast, Int.negSucc_eq, Int.negSucc_eq]
          have : (((n1 + 1) * m2 - 1 : ℕ) : ℤ) + 1 = ((n1 : ℤ) + 1) * (m2 : ℤ) := by
            rw [Nat.cast_sub h1]; push_cast; ring
          linarith
        rw [heq]
        simp only [prodAbs, sameSign, natAbs_ofNat, Int.natAbs_negSucc, encode_int_ofNat,
          encode_int_negSucc, bodd_two_mul, bodd_two_mul_add_one, Nat.succ_eq_add_one]
        rw [show ((n1 + 1) * m2 == 0) = false from beq_false_of_ne hpos, Bool.cond_false]
        rfl
    | negSucc n2 =>
      have hpos : (n1 + 1) * (n2 + 1) ≠ 0 :=
        Nat.mul_ne_zero (Nat.succ_ne_zero n1) (Nat.succ_ne_zero n2)
      have heq : Int.negSucc n1 * Int.negSucc n2 = Int.ofNat ((n1 + 1) * (n2 + 1)) := by
        rw [Int.ofNat_eq_natCast, Int.negSucc_eq, Int.negSucc_eq]
        push_cast; ring
      rw [heq]
      simp only [prodAbs, sameSign, Int.natAbs_negSucc, encode_int_ofNat, encode_int_negSucc,
        bodd_two_mul_add_one, beq_self_eq_true, Bool.cond_true, Nat.succ_eq_add_one]
      rw [show ((n1 + 1) * (n2 + 1) == 0) = false from beq_false_of_ne hpos, Bool.cond_false]

private lemma primrec_int_dvd_nat : Primrec₂ (fun (d : ℕ) (z : ℤ) => decide ((d : ℤ) ∣ z)) := by
  have h : Primrec₂ (fun (d : ℕ) (z : ℤ) => z.natAbs % d == 0) :=
    Primrec.beq.comp₂ (Primrec.nat_mod.comp₂ (primrec_int_natAbs.comp₂ Primrec₂.right) Primrec₂.left)
      (Primrec.const 0).to₂
  refine h.of_eq fun d z => ?_
  rw [Bool.eq_iff_iff]
  simp only [beq_iff_eq, decide_eq_true_eq]
  rw [← Int.natAbs_dvd_natAbs, Int.natAbs_natCast, Nat.dvd_iff_mod_eq_zero]

private lemma primrec_int_lt : Primrec₂ (fun (a b : ℤ) => decide (a < b)) :=
  (primrec_int_pos.comp₂ (primrec_int_sub.comp₂ Primrec₂.right Primrec₂.left)).of_eq fun a b => by
    simp only [decide_eq_decide]; omega

private lemma primrec_list_all {α β : Type*} [Primcodable α] [Primcodable β]
    {f : α → List β} {p : α → β → Bool} (hf : Primrec f) (hp : Primrec₂ p) :
    Primrec fun a => (f a).all (p a) := by
  have hstep : Primrec₂ (fun (a : α) (bs : β × Bool) => p a bs.1 && bs.2) :=
    (Primrec.and.comp (hp.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂
  refine (Primrec.list_foldr hf (Primrec.const true) hstep).of_eq fun a => ?_
  induction f a with
  | nil => rfl
  | cons b tl ih => simp [List.foldr_cons, List.all_cons, ih]

private lemma primrec_list_any {α β : Type*} [Primcodable α] [Primcodable β]
    {f : α → List β} {p : α → β → Bool} (hf : Primrec f) (hp : Primrec₂ p) :
    Primrec fun a => (f a).any (p a) := by
  have hstep : Primrec₂ (fun (a : α) (bs : β × Bool) => p a bs.1 || bs.2) :=
    (Primrec.or.comp (hp.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂
  refine (Primrec.list_foldr hf (Primrec.const false) hstep).of_eq fun a => ?_
  induction f a with
  | nil => rfl
  | cons b tl ih => simp [List.foldr_cons, List.any_cons, ih]

private lemma primrec_list_isEmpty {α : Type*} [Primcodable α] :
    Primrec (@List.isEmpty α) :=
  (Primrec.list_casesOn Primrec.id (Primrec.const true) (Primrec.const false).to₂).of_eq fun l => by
    cases l <;> rfl

/- ### Part 2: Linear expressions `Lin := ℤ × List ℤ` and `dotList` -/

private abbrev Lin := ℤ × List ℤ

private def dotList : List ℤ → List ℤ → ℤ
  | [], _ => 0
  | a :: as, env => a * env.getD 0 0 + dotList as env.tail

private def evalLin (e : Lin) (env : List ℤ) : ℤ :=
  e.1 + dotList e.2 env

private lemma getD_tail (l : List ℤ) (i : ℕ) : l.tail.getD i 0 = l.getD (i + 1) 0 := by
  cases l <;> simp

private lemma dotList_cons_cons (a : ℤ) (as : List ℤ) (x : ℤ) (env : List ℤ) :
    dotList (a :: as) (x :: env) = a * x + dotList as env := rfl

private lemma dotList_cons_right (cs : List ℤ) (x : ℤ) (env : List ℤ) :
    dotList cs (x :: env) = cs.getD 0 0 * x + dotList cs.tail env := by
  cases cs with
  | nil => simp [dotList]
  | cons a as => rfl

private lemma dotList_nil_right (cs : List ℤ) : dotList cs [] = 0 := by
  induction cs with
  | nil => rfl
  | cons a as ih => simp [dotList, ih]

private lemma dotList_eq_sum_range :
    ∀ (N : ℕ) (cs env : List ℤ), cs.length ≤ N →
      dotList cs env = ∑ i ∈ Finset.range N, cs.getD i 0 * env.getD i 0
  | 0, cs, env, hN => by
    have hcs : cs = [] := List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero hN)
    subst hcs; simp [dotList]
  | N + 1, cs, env, hN => by
    rw [Finset.sum_range_succ']
    cases cs with
    | nil => simp [dotList]
    | cons a as =>
      simp only [List.length_cons, Nat.add_le_add_iff_right] at hN
      simp only [dotList, List.getD_cons_zero, List.getD_cons_succ]
      rw [dotList_eq_sum_range N as env.tail hN, add_comm]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [getD_tail]

private lemma dotList_append :
    ∀ (cs₁ cs₂ xs ys : List ℤ), cs₁.length = xs.length →
      dotList (cs₁ ++ cs₂) (xs ++ ys) = dotList cs₁ xs + dotList cs₂ ys
  | [], cs₂, xs, ys, h => by
    have hxs : xs = [] := List.eq_nil_of_length_eq_zero h.symm
    subst hxs; simp [dotList]
  | a :: as, cs₂, [], ys, h => by simp at h
  | a :: as, cs₂, x :: xs, ys, h => by
    simp only [List.length_cons, Nat.succ.injEq] at h
    simp only [List.cons_append, dotList_cons_cons, dotList_append as cs₂ xs ys h]
    ring

private lemma dotList_map_mul (k : ℤ) :
    ∀ (cs env : List ℤ), dotList (cs.map fun a => k * a) env = k * dotList cs env
  | [], _ => by simp [dotList]
  | a :: as, env => by
    simp only [List.map_cons, dotList, dotList_map_mul k as env.tail]
    ring

private def unitVec (k : ℕ) : List ℤ :=
  ((List.range k).map fun _ => (0 : ℤ)) ++ [1]

private lemma unitVec_succ (k : ℕ) : unitVec (k + 1) = 0 :: unitVec k := by
  unfold unitVec
  have h : ((List.range (k + 1)).map fun _ => (0 : ℤ)) =
      0 :: ((List.range k).map fun _ => (0 : ℤ)) := by
    refine List.ext_getElem (by simp) fun i hi _ => ?_
    cases i <;> simp
  rw [h, List.cons_append]

private lemma dotList_unitVec : ∀ (k : ℕ) (env : List ℤ), dotList (unitVec k) env = env.getD k 0
  | 0, env => by simp [unitVec, dotList]
  | k + 1, env => by
    rw [unitVec_succ, dotList, zero_mul, zero_add, dotList_unitVec k env.tail, getD_tail]

private lemma primrec_unitVec : Primrec unitVec := by
  unfold unitVec
  exact Primrec.list_append.comp
    (Primrec.list_map Primrec.list_range (Primrec.const (0 : ℤ)).to₂)
    (Primrec.const [(1 : ℤ)])

private def addListInt (l₁ l₂ : List ℤ) : List ℤ :=
  (List.range (max l₁.length l₂.length)).map fun i => l₁.getD i 0 + l₂.getD i 0

private lemma dotList_addListInt (l₁ l₂ env : List ℤ) :
    dotList (addListInt l₁ l₂) env = dotList l₁ env + dotList l₂ env := by
  set N := max l₁.length l₂.length
  have hlen : (addListInt l₁ l₂).length = N := by simp [addListInt, N]
  rw [dotList_eq_sum_range N (addListInt l₁ l₂) env hlen.le,
    dotList_eq_sum_range N l₁ env (le_max_left _ _),
    dotList_eq_sum_range N l₂ env (le_max_right _ _), ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hiN : i < N := Finset.mem_range.mp hi
  have hget : (addListInt l₁ l₂).getD i 0 = l₁.getD i 0 + l₂.getD i 0 := by
    simp [addListInt, List.getD_eq_getElem?_getD, N, hiN]
  rw [hget]; ring

private lemma primrec_addListInt : Primrec₂ addListInt := by
  change Primrec (fun p : List ℤ × List ℤ => addListInt p.1 p.2)
  unfold addListInt
  refine Primrec.list_map
    (Primrec.list_range.comp
      (Primrec.nat_max.comp (Primrec.list_length.comp Primrec.fst)
        (Primrec.list_length.comp Primrec.snd))) ?_
  have h1 : Primrec₂ (fun (p : List ℤ × List ℤ) (i : ℕ) => p.1.getD i 0) :=
    (Primrec.list_getD (0 : ℤ)).comp₂ (Primrec.fst.comp₂ Primrec₂.left) Primrec₂.right
  have h2 : Primrec₂ (fun (p : List ℤ × List ℤ) (i : ℕ) => p.2.getD i 0) :=
    (Primrec.list_getD (0 : ℤ)).comp₂ (Primrec.snd.comp₂ Primrec₂.left) Primrec₂.right
  exact primrec_int_add.comp₂ h1 h2

private def scaleLin (k : ℤ) (e : Lin) : Lin :=
  (k * e.1, e.2.map fun a => k * a)

private def addLin (e₁ e₂ : Lin) : Lin :=
  (e₁.1 + e₂.1, addListInt e₁.2 e₂.2)

private def subLin (e₁ e₂ : Lin) : Lin :=
  addLin e₁ (scaleLin (-1) e₂)

private def shiftLin (j : ℤ) (e : Lin) : Lin :=
  (e.1 + j, e.2)

private lemma evalLin_scaleLin (k : ℤ) (e : Lin) (env : List ℤ) :
    evalLin (scaleLin k e) env = k * evalLin e env := by
  simp only [evalLin, scaleLin, dotList_map_mul]; ring

private lemma evalLin_addLin (e₁ e₂ : Lin) (env : List ℤ) :
    evalLin (addLin e₁ e₂) env = evalLin e₁ env + evalLin e₂ env := by
  simp only [evalLin, addLin, dotList_addListInt]; ring

private lemma evalLin_subLin (e₁ e₂ : Lin) (env : List ℤ) :
    evalLin (subLin e₁ e₂) env = evalLin e₁ env - evalLin e₂ env := by
  simp only [subLin, evalLin_addLin, evalLin_scaleLin]; ring

private lemma evalLin_shiftLin (j : ℤ) (e : Lin) (env : List ℤ) :
    evalLin (shiftLin j e) env = evalLin e env + j := by
  simp only [evalLin, shiftLin]; ring

private lemma evalLin_nil (e : Lin) : evalLin e [] = e.1 := by
  simp [evalLin, dotList_nil_right]

private lemma evalLin_cons (e : Lin) (x : ℤ) (env : List ℤ) :
    evalLin e (x :: env) = e.2.getD 0 0 * x + evalLin (e.1, e.2.tail) env := by
  simp only [evalLin, dotList_cons_right]; ring

private lemma primrec_scaleLin : Primrec₂ scaleLin := by
  change Primrec (fun p : ℤ × Lin => scaleLin p.1 p.2)
  unfold scaleLin
  refine Primrec.pair
    (primrec_int_mul.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
    (Primrec.list_map (Primrec.snd.comp Primrec.snd)
      (primrec_int_mul.comp₂ (Primrec.fst.comp₂ Primrec₂.left) Primrec₂.right))

private lemma primrec_addLin : Primrec₂ addLin := by
  change Primrec (fun p : Lin × Lin => addLin p.1 p.2)
  unfold addLin
  exact Primrec.pair
    (primrec_int_add.comp (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd))
    (primrec_addListInt.comp (Primrec.snd.comp Primrec.fst) (Primrec.snd.comp Primrec.snd))

private lemma primrec_subLin : Primrec₂ subLin :=
  primrec_addLin.comp₂ Primrec₂.left (primrec_scaleLin.comp₂ (Primrec.const (-1 : ℤ)).to₂ Primrec₂.right)

private lemma primrec_shiftLin : Primrec₂ shiftLin := by
  change Primrec (fun p : ℤ × Lin => shiftLin p.1 p.2)
  unfold shiftLin
  exact Primrec.pair
    (primrec_int_add.comp (Primrec.fst.comp Primrec.snd) Primrec.fst)
    (Primrec.snd.comp Primrec.snd)

/- ### Part 3: Flat positive DNF Presburger formulas -/

private abbrev Atom := ℕ × Lin
private abbrev Conj := List Atom
private abbrev DNF := List Conj

private def evalAtom (a : Atom) (env : List ℤ) : Prop :=
  match a.1 with
  | 0 => 0 ≤ evalLin a.2 env
  | d + 1 => ((d + 1 : ℕ) : ℤ) ∣ evalLin a.2 env

private lemma evalAtom_zero (e : Lin) (env : List ℤ) :
    evalAtom (0, e) env ↔ 0 ≤ evalLin e env := Iff.rfl

private lemma evalAtom_of_pos {d : ℕ} (hd : 0 < d) (e : Lin) (env : List ℤ) :
    evalAtom (d, e) env ↔ ((d : ℕ) : ℤ) ∣ evalLin e env := by
  cases d with
  | zero => omega
  | succ d' => rfl

private def evalConj (C : Conj) (env : List ℤ) : Prop :=
  ∀ a ∈ C, evalAtom a env

private def evalDNF (φ : DNF) (env : List ℤ) : Prop :=
  ∃ C ∈ φ, evalConj C env

private def negAtom (a : Atom) : DNF :=
  match a.1 with
  | 0 => [[(0, shiftLin (-1) (scaleLin (-1) a.2))]]
  | d + 1 => (List.range d).map fun r => [(d + 1, shiftLin ((r + 1 : ℕ) : ℤ) a.2)]

private def negConj (C : Conj) : DNF := C.flatMap negAtom

private def andDNF (φ ψ : DNF) : DNF :=
  φ.flatMap fun C₁ => ψ.map fun C₂ => C₁ ++ C₂

private def negDNF (φ : DNF) : DNF :=
  φ.foldr (fun C acc => andDNF (negConj C) acc) [[]]

private lemma evalDNF_negAtom (a : Atom) (env : List ℤ) :
    evalDNF (negAtom a) env ↔ ¬ evalAtom a env := by
  rcases a with ⟨d, e⟩
  cases d with
  | zero =>
    simp only [negAtom, evalDNF, evalConj, evalAtom, List.mem_singleton, exists_eq_left,
      forall_eq, evalLin_shiftLin, evalLin_scaleLin]
    omega
  | succ d =>
    simp only [negAtom, evalDNF, evalConj, evalAtom, List.mem_map, List.mem_range,
      exists_exists_and_eq_and, List.mem_singleton, forall_eq, evalLin_shiftLin]
    set t := evalLin e env
    constructor
    · rintro ⟨r, hr, hdiv⟩ hdt
      have hrdiv : ((d + 1 : ℕ) : ℤ) ∣ ((r + 1 : ℕ) : ℤ) := by
        have hsub := Int.dvd_sub hdiv hdt
        simpa using hsub
      have hnat : (d + 1) ∣ (r + 1) := Int.ofNat_dvd.mp hrdiv
      have hle := Nat.le_of_dvd (Nat.succ_pos r) hnat
      omega
    · intro hndiv
      have hdpos : (0 : ℤ) < ((d + 1 : ℕ) : ℤ) := by positivity
      have hrem_nn : 0 ≤ t % ((d + 1 : ℕ) : ℤ) := Int.emod_nonneg t hdpos.ne'
      have hrem_lt : t % ((d + 1 : ℕ) : ℤ) < ((d + 1 : ℕ) : ℤ) := Int.emod_lt_of_pos t hdpos
      have hrem_ne : t % ((d + 1 : ℕ) : ℤ) ≠ 0 := by
        intro h0
        exact hndiv (Int.dvd_of_emod_eq_zero h0)
      let rem : ℕ := (t % ((d + 1 : ℕ) : ℤ)).toNat
      have hrem_cast : (rem : ℤ) = t % ((d + 1 : ℕ) : ℤ) := Int.toNat_of_nonneg hrem_nn
      have hrem_pos : 0 < rem := by omega
      have hrem_le : rem ≤ d := by omega
      refine ⟨d - rem, by omega, ?_⟩
      refine ⟨t / ((d + 1 : ℕ) : ℤ) + 1, ?_⟩
      have hdiv_eq := Int.mul_ediv_add_emod t ((d + 1 : ℕ) : ℤ)
      have hcast : ((d - rem + 1 : ℕ) : ℤ) = ((d + 1 : ℕ) : ℤ) - (rem : ℤ) := by omega
      rw [hcast, hrem_cast]
      linarith

private lemma evalDNF_negConj (C : Conj) (env : List ℤ) :
    evalDNF (negConj C) env ↔ ¬ evalConj C env := by
  simp only [negConj, evalDNF, List.mem_flatMap, evalConj]
  constructor
  · rintro ⟨C', ⟨a, ha, hC'⟩, hsat⟩ hall
    exact (evalDNF_negAtom a env).mp ⟨C', hC', hsat⟩ (hall a ha)
  · intro hnot
    push Not at hnot
    obtain ⟨a, ha, hna⟩ := hnot
    obtain ⟨C', hC', hsat⟩ := (evalDNF_negAtom a env).mpr hna
    exact ⟨C', ⟨a, ha, hC'⟩, hsat⟩

private lemma evalDNF_andDNF (φ ψ : DNF) (env : List ℤ) :
    evalDNF (andDNF φ ψ) env ↔ evalDNF φ env ∧ evalDNF ψ env := by
  simp only [andDNF, evalDNF, evalConj, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨C, ⟨C₁, hC₁, C₂, hC₂, rfl⟩, hsat⟩
    exact ⟨⟨C₁, hC₁, fun a ha => hsat a (List.mem_append_left C₂ ha)⟩,
      ⟨C₂, hC₂, fun a ha => hsat a (List.mem_append_right C₁ ha)⟩⟩
  · rintro ⟨⟨C₁, hC₁, hsat₁⟩, ⟨C₂, hC₂, hsat₂⟩⟩
    refine ⟨C₁ ++ C₂, ⟨C₁, hC₁, C₂, hC₂, rfl⟩, fun a ha => ?_⟩
    rcases List.mem_append.mp ha with h1 | h2
    · exact hsat₁ a h1
    · exact hsat₂ a h2

private lemma negDNF_cons (C : Conj) (tl : DNF) :
    negDNF (C :: tl) = andDNF (negConj C) (negDNF tl) := rfl

private lemma evalDNF_negDNF (φ : DNF) (env : List ℤ) :
    evalDNF (negDNF φ) env ↔ ¬ evalDNF φ env := by
  induction φ with
  | nil =>
    simp [negDNF, evalDNF, evalConj]
  | cons C tl ih =>
    rw [negDNF_cons, evalDNF_andDNF, evalDNF_negConj, ih]
    simp only [evalDNF, List.mem_cons, exists_eq_or_imp, not_or]

private lemma primrec_negAtom : Primrec negAtom := by
  have hzero : Primrec (fun a : Atom => [[((0 : ℕ), shiftLin (-1) (scaleLin (-1) a.2))]]) :=
    Primrec.list_cons.comp
      (Primrec.list_cons.comp
        (Primrec.pair (Primrec.const (0 : ℕ))
          (primrec_shiftLin.comp (Primrec.const (-1 : ℤ))
            (primrec_scaleLin.comp (Primrec.const (-1 : ℤ)) Primrec.snd)))
        (Primrec.const ([] : Conj)))
      (Primrec.const ([] : DNF))
  have hsucc : Primrec₂ (fun (a : Atom) (d : ℕ) =>
      (List.range d).map fun r => [(d + 1, shiftLin ((r + 1 : ℕ) : ℤ) a.2)]) := by
    change Primrec (fun p : Atom × ℕ =>
      (List.range p.2).map fun r => [(p.2 + 1, shiftLin ((r + 1 : ℕ) : ℤ) p.1.2)])
    refine Primrec.list_map (Primrec.list_range.comp Primrec.snd) ?_
    have hd1 : Primrec (fun p : (Atom × ℕ) × ℕ => p.1.2 + 1) :=
      Primrec.succ.comp (Primrec.snd.comp Primrec.fst)
    have hr1 : Primrec (fun p : (Atom × ℕ) × ℕ => ((p.2 + 1 : ℕ) : ℤ)) :=
      primrec_int_ofNat.comp (Primrec.succ.comp Primrec.snd)
    have he : Primrec (fun p : (Atom × ℕ) × ℕ => p.1.1.2) :=
      Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
    exact (Primrec.list_cons.comp
      (Primrec.pair hd1 (primrec_shiftLin.comp hr1 he))
      (Primrec.const ([] : Conj))).to₂
  refine (Primrec.nat_casesOn Primrec.fst hzero hsucc).of_eq fun ⟨d, e⟩ => ?_
  cases d <;> rfl

private lemma primrec_negConj : Primrec negConj :=
  Primrec.list_flatMap (Primrec.id (α := Conj)) (primrec_negAtom.comp₂ Primrec₂.right)

private lemma primrec_andDNF : Primrec₂ andDNF := by
  change Primrec (fun p : DNF × DNF => andDNF p.1 p.2)
  unfold andDNF
  refine Primrec.list_flatMap Primrec.fst ?_
  change Primrec (fun q : (DNF × DNF) × Conj => q.1.2.map fun C₂ => q.2 ++ C₂)
  refine Primrec.list_map (Primrec.snd.comp Primrec.fst) ?_
  exact (Primrec.list_append.comp (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂

private lemma primrec_negDNF : Primrec negDNF := by
  unfold negDNF
  have hstep : Primrec₂ (fun (_ : DNF) (bs : Conj × DNF) => andDNF (negConj bs.1) bs.2) :=
    (primrec_andDNF.comp (primrec_negConj.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂
  exact Primrec.list_foldr (Primrec.id (α := DNF)) (Primrec.const ([[]] : DNF)) hstep

private def evalAtom0 (a : Atom) : Bool :=
  match a.1 with
  | 0 => decide (0 ≤ a.2.1)
  | d + 1 => decide (((d + 1 : ℕ) : ℤ) ∣ a.2.1)

private def evalConj0 (C : Conj) : Bool := C.all evalAtom0

private def evalDNF0 (φ : DNF) : Bool := φ.any evalConj0

private lemma evalAtom0_eq_true (a : Atom) : evalAtom0 a = true ↔ evalAtom a [] := by
  rcases a with ⟨d, e⟩
  cases d with
  | zero => simp [evalAtom0, evalAtom, evalLin_nil]
  | succ d => simp [evalAtom0, evalAtom, evalLin_nil]

private lemma evalConj0_eq_true (C : Conj) : evalConj0 C = true ↔ evalConj C [] := by
  simp [evalConj0, evalConj, evalAtom0_eq_true]

private lemma evalDNF0_eq_true (φ : DNF) : evalDNF0 φ = true ↔ evalDNF φ [] := by
  simp [evalDNF0, evalDNF, evalConj0_eq_true]

private lemma primrec_evalAtom0 : Primrec evalAtom0 := by
  have hzero : Primrec (fun a : Atom => decide ((0 : ℤ) ≤ a.2.1)) :=
    primrec_int_nonneg.comp (Primrec.fst.comp Primrec.snd)
  have hsucc : Primrec₂ (fun (a : Atom) (d : ℕ) => decide (((d + 1 : ℕ) : ℤ) ∣ a.2.1)) :=
    primrec_int_dvd_nat.comp₂ (Primrec.succ.comp₂ Primrec₂.right)
      ((Primrec.fst.comp Primrec.snd).comp₂ Primrec₂.left)
  refine (Primrec.nat_casesOn Primrec.fst hzero hsucc).of_eq fun ⟨d, e⟩ => ?_
  cases d <;> rfl

private lemma primrec_evalConj0 : Primrec evalConj0 :=
  primrec_list_all Primrec.id (primrec_evalAtom0.comp₂ Primrec₂.right)

private lemma primrec_evalDNF0 : Primrec evalDNF0 :=
  primrec_list_any Primrec.id (primrec_evalConj0.comp₂ Primrec₂.right)

/- ### Part 4: Cooper single-variable quantifier elimination -/

private def leadProd (C : Conj) : ℕ :=
  C.foldr (fun a acc =>
    let k := a.2.2.getD 0 0
    cond (k == 0) acc (k.natAbs * acc)) 1

private def freeAtoms (C : Conj) : Conj :=
  C.foldr (fun a acc =>
    cond (a.2.2.getD 0 0 == 0) ((a.1, (a.2.1, a.2.2.tail)) :: acc) acc) []

private def lowerBounds (L : ℕ) (C : Conj) : List Lin :=
  C.foldr (fun a acc =>
    let k := a.2.2.getD 0 0
    cond ((a.1 == 0) && decide (0 < k))
      (scaleLin (-((L / k.natAbs : ℕ) : ℤ)) (a.2.1, a.2.2.tail) :: acc) acc) []

private def upperBounds (L : ℕ) (C : Conj) : List Lin :=
  C.foldr (fun a acc =>
    let k := a.2.2.getD 0 0
    cond ((a.1 == 0) && decide (k < 0))
      (scaleLin (((L / k.natAbs : ℕ) : ℤ)) (a.2.1, a.2.2.tail) :: acc) acc) []

private def divBounds (L : ℕ) (C : Conj) : List (ℕ × Lin) :=
  (L, (0, [])) :: C.foldr (fun a acc =>
    let k := a.2.2.getD 0 0
    cond (!(a.1 == 0) && !(k == 0))
      (let m := L / k.natAbs
       let s : ℤ := cond (decide (0 < k)) (m : ℤ) (-(m : ℤ))
       (m * a.1, scaleLin s (a.2.1, a.2.2.tail)) :: acc) acc) []

private def modProd (Ds : List (ℕ × Lin)) : ℕ :=
  Ds.foldr (fun de acc => de.1 * acc) 1

private def elimConj (C : Conj) : DNF :=
  let L := leadProd C
  let F := freeAtoms C
  let Ls := lowerBounds L C
  let Us := upperBounds L C
  let Ds := divBounds L C
  let M := modProd Ds
  cond Ls.isEmpty
    ((List.range M).map fun j : ℕ =>
      F ++ Ds.map fun de => (de.1, shiftLin (j : ℤ) de.2))
    (Ls.flatMap fun b₀ =>
      (List.range M).map fun j : ℕ =>
        let y := shiftLin (j : ℤ) b₀
        F ++
        (Ls.map fun b => (0, subLin y b)) ++
        (Us.map fun u => (0, subLin u y)) ++
        (Ds.map fun de => (de.1, addLin y de.2)))

private def elimDNF (φ : DNF) : DNF := φ.flatMap elimConj

private def elimMany (n : ℕ) (φ : DNF) : DNF := elimDNF^[n] φ

private lemma leadProd_cons (a : Atom) (tl : Conj) :
    leadProd (a :: tl) = cond (a.2.2.getD 0 0 == 0) (leadProd tl) ((a.2.2.getD 0 0).natAbs * leadProd tl) := rfl

private lemma freeAtoms_cons (a : Atom) (tl : Conj) :
    freeAtoms (a :: tl) = cond (a.2.2.getD 0 0 == 0) ((a.1, (a.2.1, a.2.2.tail)) :: freeAtoms tl) (freeAtoms tl) := rfl

private lemma lowerBounds_cons (L : ℕ) (a : Atom) (tl : Conj) :
    lowerBounds L (a :: tl) =
      cond ((a.1 == 0) && decide (0 < a.2.2.getD 0 0))
        (scaleLin (-((L / (a.2.2.getD 0 0).natAbs : ℕ) : ℤ)) (a.2.1, a.2.2.tail) :: lowerBounds L tl)
        (lowerBounds L tl) := rfl

private lemma upperBounds_cons (L : ℕ) (a : Atom) (tl : Conj) :
    upperBounds L (a :: tl) =
      cond ((a.1 == 0) && decide (a.2.2.getD 0 0 < 0))
        (scaleLin (((L / (a.2.2.getD 0 0).natAbs : ℕ) : ℤ)) (a.2.1, a.2.2.tail) :: upperBounds L tl)
        (upperBounds L tl) := rfl

private lemma leadProd_pos (C : Conj) : 0 < leadProd C := by
  induction C with
  | nil => decide
  | cons a tl ih =>
    rw [leadProd_cons]
    by_cases hk : a.2.2.getD 0 0 = 0
    · rw [show (a.2.2.getD 0 0 == 0) = true from beq_iff_eq.mpr hk, Bool.cond_true]
      exact ih
    · have hpos : 0 < (a.2.2.getD 0 0).natAbs := Int.natAbs_pos.mpr hk
      rw [show (a.2.2.getD 0 0 == 0) = false from beq_false_of_ne hk, Bool.cond_false]
      exact Nat.mul_pos hpos ih

private lemma natAbs_dvd_leadProd {C : Conj} {a : Atom} (ha : a ∈ C)
    (hk : a.2.2.getD 0 0 ≠ 0) : (a.2.2.getD 0 0).natAbs ∣ leadProd C := by
  induction C with
  | nil => cases ha
  | cons b tl ih =>
    rw [leadProd_cons]
    rcases List.mem_cons.mp ha with rfl | htl
    · rw [show (a.2.2.getD 0 0 == 0) = false from beq_false_of_ne hk, Bool.cond_false]
      exact dvd_mul_right _ _
    · by_cases hkb : b.2.2.getD 0 0 = 0
      · rw [show (b.2.2.getD 0 0 == 0) = true from beq_iff_eq.mpr hkb, Bool.cond_true]
        exact ih htl
      · rw [show (b.2.2.getD 0 0 == 0) = false from beq_false_of_ne hkb, Bool.cond_false]
        exact dvd_mul_of_dvd_right (ih htl) _

private lemma mem_freeAtoms_iff (C : Conj) (f : Atom) :
    f ∈ freeAtoms C ↔ ∃ a ∈ C, a.2.2.getD 0 0 = 0 ∧ f = (a.1, (a.2.1, a.2.2.tail)) := by
  induction C with
  | nil => simp [freeAtoms]
  | cons a tl ih =>
    rw [freeAtoms_cons]
    by_cases hk : a.2.2.getD 0 0 = 0
    · rw [show (a.2.2.getD 0 0 == 0) = true from beq_iff_eq.mpr hk, Bool.cond_true,
        List.mem_cons, ih]
      constructor
      · rintro (rfl | ⟨b, hb, hkb, rfl⟩)
        · exact ⟨a, List.mem_cons_self .., hk, rfl⟩
        · exact ⟨b, List.mem_cons_of_mem a hb, hkb, rfl⟩
      · rintro ⟨b, hb, hkb, rfl⟩
        rcases List.mem_cons.mp hb with rfl | htl
        · exact Or.inl rfl
        · exact Or.inr ⟨b, htl, hkb, rfl⟩
    · rw [show (a.2.2.getD 0 0 == 0) = false from beq_false_of_ne hk, Bool.cond_false, ih]
      constructor
      · rintro ⟨b, hb, hkb, rfl⟩; exact ⟨b, List.mem_cons_of_mem a hb, hkb, rfl⟩
      · rintro ⟨b, hb, hkb, rfl⟩
        rcases List.mem_cons.mp hb with rfl | htl
        · exact (hk hkb).elim
        · exact ⟨b, htl, hkb, rfl⟩

private lemma mem_lowerBounds_iff (L : ℕ) (C : Conj) (b : Lin) :
    b ∈ lowerBounds L C ↔
      ∃ a ∈ C, a.1 = 0 ∧ 0 < a.2.2.getD 0 0 ∧
        b = scaleLin (-((L / (a.2.2.getD 0 0).natAbs : ℕ) : ℤ)) (a.2.1, a.2.2.tail) := by
  induction C with
  | nil => simp [lowerBounds]
  | cons a tl ih =>
    rw [lowerBounds_cons]
    by_cases hcond : a.1 = 0 ∧ 0 < a.2.2.getD 0 0
    · have hb_true : ((a.1 == 0) && decide (0 < a.2.2.getD 0 0)) = true := by
        rw [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]; exact hcond
      rw [hb_true, Bool.cond_true, List.mem_cons, ih]
      constructor
      · rintro (rfl | ⟨x, hx, h1, h2, rfl⟩)
        · exact ⟨a, List.mem_cons_self .., hcond.1, hcond.2, rfl⟩
        · exact ⟨x, List.mem_cons_of_mem a hx, h1, h2, rfl⟩
      · rintro ⟨x, hx, h1, h2, rfl⟩
        rcases List.mem_cons.mp hx with rfl | htl
        · exact Or.inl rfl
        · exact Or.inr ⟨x, htl, h1, h2, rfl⟩
    · have hb_false : ((a.1 == 0) && decide (0 < a.2.2.getD 0 0)) = false := by
        rw [Bool.eq_false_iff]; intro ht
        rw [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at ht
        exact hcond ht
      rw [hb_false, Bool.cond_false, ih]
      constructor
      · rintro ⟨x, hx, h1, h2, rfl⟩; exact ⟨x, List.mem_cons_of_mem a hx, h1, h2, rfl⟩
      · rintro ⟨x, hx, h1, h2, rfl⟩
        rcases List.mem_cons.mp hx with rfl | htl
        · exact (hcond ⟨h1, h2⟩).elim
        · exact ⟨x, htl, h1, h2, rfl⟩

private lemma mem_upperBounds_iff (L : ℕ) (C : Conj) (u : Lin) :
    u ∈ upperBounds L C ↔
      ∃ a ∈ C, a.1 = 0 ∧ a.2.2.getD 0 0 < 0 ∧
        u = scaleLin (((L / (a.2.2.getD 0 0).natAbs : ℕ) : ℤ)) (a.2.1, a.2.2.tail) := by
  induction C with
  | nil => simp [upperBounds]
  | cons a tl ih =>
    rw [upperBounds_cons]
    by_cases hcond : a.1 = 0 ∧ a.2.2.getD 0 0 < 0
    · have hb_true : ((a.1 == 0) && decide (a.2.2.getD 0 0 < 0)) = true := by
        rw [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]; exact hcond
      rw [hb_true, Bool.cond_true, List.mem_cons, ih]
      constructor
      · rintro (rfl | ⟨x, hx, h1, h2, rfl⟩)
        · exact ⟨a, List.mem_cons_self .., hcond.1, hcond.2, rfl⟩
        · exact ⟨x, List.mem_cons_of_mem a hx, h1, h2, rfl⟩
      · rintro ⟨x, hx, h1, h2, rfl⟩
        rcases List.mem_cons.mp hx with rfl | htl
        · exact Or.inl rfl
        · exact Or.inr ⟨x, htl, h1, h2, rfl⟩
    · have hb_false : ((a.1 == 0) && decide (a.2.2.getD 0 0 < 0)) = false := by
        rw [Bool.eq_false_iff]; intro ht
        rw [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at ht
        exact hcond ht
      rw [hb_false, Bool.cond_false, ih]
      constructor
      · rintro ⟨x, hx, h1, h2, rfl⟩; exact ⟨x, List.mem_cons_of_mem a hx, h1, h2, rfl⟩
      · rintro ⟨x, hx, h1, h2, rfl⟩
        rcases List.mem_cons.mp hx with rfl | htl
        · exact (hcond ⟨h1, h2⟩).elim
        · exact ⟨x, htl, h1, h2, rfl⟩

private lemma mem_divBounds_iff (L : ℕ) (C : Conj) (de : ℕ × Lin) :
    de ∈ divBounds L C ↔
      de = (L, (0, [])) ∨
      ∃ a ∈ C, a.1 ≠ 0 ∧ a.2.2.getD 0 0 ≠ 0 ∧
        de = ((L / (a.2.2.getD 0 0).natAbs) * a.1,
          scaleLin (cond (decide (0 < a.2.2.getD 0 0))
            ((L / (a.2.2.getD 0 0).natAbs : ℕ) : ℤ)
            (-((L / (a.2.2.getD 0 0).natAbs : ℕ) : ℤ)))
            (a.2.1, a.2.2.tail)) := by
  unfold divBounds
  rw [List.mem_cons]
  refine or_congr_right ?_
  induction C with
  | nil => simp
  | cons a tl ih =>
    rw [List.foldr_cons]
    by_cases hcond : a.1 ≠ 0 ∧ a.2.2.getD 0 0 ≠ 0
    · have hb_true : (!(a.1 == 0) && !(a.2.2.getD 0 0 == 0)) = true := by
        rw [Bool.and_eq_true, Bool.not_eq_true', Bool.not_eq_true',
          beq_false_of_ne hcond.1, beq_false_of_ne hcond.2]; exact ⟨rfl, rfl⟩
      dsimp only
      rw [hb_true, Bool.cond_true, List.mem_cons, ih]
      constructor
      · rintro (rfl | ⟨x, hx, h1, h2, rfl⟩)
        · exact ⟨a, List.mem_cons_self .., hcond.1, hcond.2, rfl⟩
        · exact ⟨x, List.mem_cons_of_mem a hx, h1, h2, rfl⟩
      · rintro ⟨x, hx, h1, h2, rfl⟩
        rcases List.mem_cons.mp hx with rfl | htl
        · exact Or.inl rfl
        · exact Or.inr ⟨x, htl, h1, h2, rfl⟩
    · have hb_false : (!(a.1 == 0) && !(a.2.2.getD 0 0 == 0)) = false := by
        rw [Bool.eq_false_iff]; intro ht
        rw [Bool.and_eq_true, Bool.not_eq_true', Bool.not_eq_true',
          Bool.eq_false_iff, Bool.eq_false_iff, ne_eq, ne_eq, beq_iff_eq, beq_iff_eq] at ht
        exact hcond ht
      dsimp only
      rw [hb_false, Bool.cond_false, ih]
      constructor
      · rintro ⟨x, hx, h1, h2, rfl⟩; exact ⟨x, List.mem_cons_of_mem a hx, h1, h2, rfl⟩
      · rintro ⟨x, hx, h1, h2, rfl⟩
        rcases List.mem_cons.mp hx with rfl | htl
        · exact (hcond ⟨h1, h2⟩).elim
        · exact ⟨x, htl, h1, h2, rfl⟩

private lemma divBounds_pos (C : Conj) :
    ∀ de ∈ divBounds (leadProd C) C, 0 < de.1 := by
  intro de hde
  have hL : 0 < leadProd C := leadProd_pos C
  rcases (mem_divBounds_iff (leadProd C) C de).mp hde with rfl | ⟨a, ha, ha1, hk, rfl⟩
  · exact hL
  · have hdvd := natAbs_dvd_leadProd ha hk
    have hka : 0 < (a.2.2.getD 0 0).natAbs := Int.natAbs_pos.mpr hk
    have hm : 0 < leadProd C / (a.2.2.getD 0 0).natAbs :=
      Nat.div_pos (Nat.le_of_dvd hL hdvd) hka
    exact Nat.mul_pos hm (Nat.pos_of_ne_zero ha1)

private lemma modProd_pos {Ds : List (ℕ × Lin)} (hDs : ∀ de ∈ Ds, 0 < de.1) :
    0 < modProd Ds := by
  induction Ds with
  | nil => decide
  | cons de tl ih =>
    simp only [modProd, List.foldr_cons]
    exact Nat.mul_pos (hDs de (List.mem_cons_self ..))
      (ih fun x hx => hDs x (List.mem_cons_of_mem _ hx))

private lemma dvd_modProd {Ds : List (ℕ × Lin)} {de : ℕ × Lin} (hde : de ∈ Ds) :
    de.1 ∣ modProd Ds := by
  induction Ds with
  | nil => cases hde
  | cons x tl ih =>
    simp only [modProd, List.foldr_cons]
    rcases List.mem_cons.mp hde with rfl | htl
    · exact dvd_mul_right _ _
    · exact dvd_mul_of_dvd_right (ih htl) _

private lemma exists_max_mem {α : Type*} (f : α → ℤ) :
    ∀ l : List α, l ≠ [] → ∃ a ∈ l, ∀ x ∈ l, f x ≤ f a
  | [], h => (h rfl).elim
  | [a], _ => ⟨a, List.mem_singleton_self a, fun x hx => by
      rw [List.mem_singleton.mp hx]⟩
  | a :: b :: tl, _ => by
    obtain ⟨m, hm, hmax⟩ := exists_max_mem f (b :: tl) (List.cons_ne_nil b tl)
    by_cases h : f a ≤ f m
    · refine ⟨m, List.mem_cons_of_mem a hm, fun x hx => ?_⟩
      rcases List.mem_cons.mp hx with rfl | hxtl
      · exact h
      · exact hmax x hxtl
    · refine ⟨a, List.mem_cons_self .., fun x hx => ?_⟩
      rcases List.mem_cons.mp hx with rfl | hxtl
      · exact le_rfl
      · exact (hmax x hxtl).trans (le_of_not_ge h)

private lemma exists_le_all (f : Lin → ℤ) (Us : List Lin) :
    ∃ B : ℤ, ∀ u ∈ Us, B ≤ f u := by
  induction Us with
  | nil => exact ⟨0, fun _ h => (List.not_mem_nil h).elim⟩
  | cons u tl ih =>
    obtain ⟨B, hB⟩ := ih
    refine ⟨min (f u) B, fun x hx => ?_⟩
    rcases List.mem_cons.mp hx with rfl | htl
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (hB x htl)

private lemma cooper_scale_iff (C : Conj) (env : List ℤ) :
    (∃ x : ℤ, evalConj C (x :: env)) ↔
    (evalConj (freeAtoms C) env ∧
      ∃ y : ℤ,
        (∀ b ∈ lowerBounds (leadProd C) C, evalLin b env ≤ y) ∧
        (∀ u ∈ upperBounds (leadProd C) C, y ≤ evalLin u env) ∧
        (∀ de ∈ divBounds (leadProd C) C, ((de.1 : ℕ) : ℤ) ∣ (y + evalLin de.2 env))) := by
  set L := leadProd C
  have hL_pos : 0 < L := leadProd_pos C
  have hmul_pos : ∀ {a : Atom}, a ∈ C → 0 < a.2.2.getD 0 0 →
      ((L / (a.2.2.getD 0 0).natAbs : ℕ) : ℤ) * a.2.2.getD 0 0 = (L : ℤ) := by
    intro a ha hk
    have hdvd := natAbs_dvd_leadProd ha (ne_of_gt hk)
    have hnat : (L / (a.2.2.getD 0 0).natAbs) * (a.2.2.getD 0 0).natAbs = L :=
      Nat.div_mul_cancel hdvd
    have hka : ((a.2.2.getD 0 0).natAbs : ℤ) = a.2.2.getD 0 0 := Int.natAbs_of_nonneg (le_of_lt hk)
    rw [← hka]; exact_mod_cast hnat
  have hmul_neg : ∀ {a : Atom}, a ∈ C → a.2.2.getD 0 0 < 0 →
      ((L / (a.2.2.getD 0 0).natAbs : ℕ) : ℤ) * a.2.2.getD 0 0 = -(L : ℤ) := by
    intro a ha hk
    have hdvd := natAbs_dvd_leadProd ha (ne_of_lt hk)
    have hnat : (L / (a.2.2.getD 0 0).natAbs) * (a.2.2.getD 0 0).natAbs = L :=
      Nat.div_mul_cancel hdvd
    have hka : ((a.2.2.getD 0 0).natAbs : ℤ) = -(a.2.2.getD 0 0) := by omega
    have hcast : ((L / (a.2.2.getD 0 0).natAbs : ℕ) : ℤ) * ((a.2.2.getD 0 0).natAbs : ℤ) = (L : ℤ) := by
      exact_mod_cast hnat
    rw [hka] at hcast
    linarith
  have hm_pos : ∀ {a : Atom}, a ∈ C → a.2.2.getD 0 0 ≠ 0 →
      0 < L / (a.2.2.getD 0 0).natAbs := fun ha hk =>
    Nat.div_pos (Nat.le_of_dvd hL_pos (natAbs_dvd_leadProd ha hk)) (Int.natAbs_pos.mpr hk)
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨?_, (L : ℤ) * x, ?_, ?_, ?_⟩
    · intro f hf
      obtain ⟨a, ha, hk0, rfl⟩ := (mem_freeAtoms_iff C f).mp hf
      have hsat := hx a ha
      have hev : evalLin a.2 (x :: env) = evalLin (a.2.1, a.2.2.tail) env := by
        rw [evalLin_cons, hk0, zero_mul, zero_add]
      cases hd : a.1 with
      | zero =>
        rw [evalAtom, hd] at hsat
        rw [evalAtom]
        simpa [hev] using hsat
      | succ d' =>
        rw [evalAtom, hd] at hsat
        rw [evalAtom]
        simpa [hev] using hsat
    · intro b hb
      obtain ⟨a, ha, ha1, hkpos, rfl⟩ := (mem_lowerBounds_iff L C b).mp hb
      have hsat := hx a ha
      rw [evalAtom, ha1] at hsat
      rw [evalLin_cons] at hsat
      rw [evalLin_scaleLin]
      have hm0 : (0 : ℤ) ≤ ((L / (a.2.2.getD 0 0).natAbs : ℕ) : ℤ) := Nat.cast_nonneg _
      have hmul := mul_nonneg hm0 hsat
      have hprod := hmul_pos ha hkpos
      have hEq : ((L / (a.2.2.getD 0 0).natAbs : ℕ) : ℤ) *
          (a.2.2.getD 0 0 * x + evalLin (a.2.1, a.2.2.tail) env) =
          (L : ℤ) * x + ((L / (a.2.2.getD 0 0).natAbs : ℕ) : ℤ) * evalLin (a.2.1, a.2.2.tail) env := by
        calc _ = (((L / (a.2.2.getD 0 0).natAbs : ℕ) : ℤ) * a.2.2.getD 0 0) * x +
              ((L / (a.2.2.getD 0 0).natAbs : ℕ) : ℤ) * evalLin (a.2.1, a.2.2.tail) env := by ring
          _ = _ := by rw [hprod]
      linarith
    · intro u hu
      obtain ⟨a, ha, ha1, hkneg, rfl⟩ := (mem_upperBounds_iff L C u).mp hu
      have hsat := hx a ha
      rw [evalAtom, ha1] at hsat
      rw [evalLin_cons] at hsat
      rw [evalLin_scaleLin]
      have hm0 : (0 : ℤ) ≤ ((L / (a.2.2.getD 0 0).natAbs : ℕ) : ℤ) := Nat.cast_nonneg _
      have hmul := mul_nonneg hm0 hsat
      have hprod := hmul_neg ha hkneg
      have hEq : ((L / (a.2.2.getD 0 0).natAbs : ℕ) : ℤ) *
          (a.2.2.getD 0 0 * x + evalLin (a.2.1, a.2.2.tail) env) =
          -(L : ℤ) * x + ((L / (a.2.2.getD 0 0).natAbs : ℕ) : ℤ) * evalLin (a.2.1, a.2.2.tail) env := by
        calc _ = (((L / (a.2.2.getD 0 0).natAbs : ℕ) : ℤ) * a.2.2.getD 0 0) * x +
              ((L / (a.2.2.getD 0 0).natAbs : ℕ) : ℤ) * evalLin (a.2.1, a.2.2.tail) env := by ring
          _ = _ := by rw [hprod]
      linarith
    · intro de hde
      rcases (mem_divBounds_iff L C de).mp hde with rfl | ⟨a, ha, ha1, hkne, rfl⟩
      · simp [evalLin, dotList]
      · have hsat := hx a ha
        rw [evalAtom_of_pos (Nat.pos_of_ne_zero ha1)] at hsat
        rw [evalLin_cons] at hsat
        rw [evalLin_scaleLin, Nat.cast_mul]
        set m := L / (a.2.2.getD 0 0).natAbs
        by_cases hkpos : 0 < a.2.2.getD 0 0
        · simp only [hkpos, decide_true, Bool.cond_true]
          have hdiv := mul_dvd_mul_left (m : ℤ) hsat
          have hprod := hmul_pos ha hkpos
          have hEq : (m : ℤ) * (a.2.2.getD 0 0 * x + evalLin (a.2.1, a.2.2.tail) env) =
              (L : ℤ) * x + (m : ℤ) * evalLin (a.2.1, a.2.2.tail) env := by
            calc _ = ((m : ℤ) * a.2.2.getD 0 0) * x + (m : ℤ) * evalLin (a.2.1, a.2.2.tail) env := by ring
              _ = _ := by rw [hprod]
          rw [hEq] at hdiv
          exact hdiv
        · have hkneg : a.2.2.getD 0 0 < 0 := by omega
          simp only [hkpos, decide_false, Bool.cond_false]
          have hdiv := mul_dvd_mul_left (m : ℤ) (dvd_neg.mpr hsat)
          have hprod := hmul_neg ha hkneg
          have hEq : (m : ℤ) * -(a.2.2.getD 0 0 * x + evalLin (a.2.1, a.2.2.tail) env) =
              (L : ℤ) * x + -(m : ℤ) * evalLin (a.2.1, a.2.2.tail) env := by
            calc _ = -(((m : ℤ) * a.2.2.getD 0 0) * x) + -(m : ℤ) * evalLin (a.2.1, a.2.2.tail) env := by ring
              _ = _ := by rw [hprod]; ring
          rw [hEq] at hdiv
          exact hdiv
  · rintro ⟨hfree, y, hlow, hup, hdiv⟩
    have hLy : (L : ℤ) ∣ y := by
      have h0 := hdiv (L, (0, [])) ((mem_divBounds_iff L C _).mpr (Or.inl rfl))
      simpa [evalLin, dotList] using h0
    obtain ⟨x, rfl⟩ := hLy
    refine ⟨x, fun a ha => ?_⟩
    by_cases hk0 : a.2.2.getD 0 0 = 0
    · have hf := hfree (a.1, (a.2.1, a.2.2.tail))
        ((mem_freeAtoms_iff C _).mpr ⟨a, ha, hk0, rfl⟩)
      have hev : evalLin a.2 (x :: env) = evalLin (a.2.1, a.2.2.tail) env := by
        rw [evalLin_cons, hk0, zero_mul, zero_add]
      cases hd : a.1 with
      | zero => rw [evalAtom, hd] at hf ⊢; simpa [hev] using hf
      | succ d' => rw [evalAtom, hd] at hf ⊢; simpa [hev] using hf
    · set m := L / (a.2.2.getD 0 0).natAbs
      have hmpos : (0 : ℤ) < (m : ℤ) := by exact_mod_cast hm_pos ha hk0
      cases hd : a.1 with
      | zero =>
        rw [evalAtom, hd, evalLin_cons]
        by_cases hkpos : 0 < a.2.2.getD 0 0
        · have hb := hlow _ ((mem_lowerBounds_iff L C _).mpr ⟨a, ha, hd, hkpos, rfl⟩)
          rw [evalLin_scaleLin] at hb
          have hprod := hmul_pos ha hkpos
          have hmul : 0 ≤ (m : ℤ) * (a.2.2.getD 0 0 * x + evalLin (a.2.1, a.2.2.tail) env) := by
            have hEq : (m : ℤ) * (a.2.2.getD 0 0 * x + evalLin (a.2.1, a.2.2.tail) env) =
                (L : ℤ) * x + (m : ℤ) * evalLin (a.2.1, a.2.2.tail) env := by
              calc _ = ((m : ℤ) * a.2.2.getD 0 0) * x + (m : ℤ) * evalLin (a.2.1, a.2.2.tail) env := by ring
                _ = _ := by rw [hprod]
            linarith
          exact nonneg_of_mul_nonneg_right hmul hmpos
        · have hkneg : a.2.2.getD 0 0 < 0 := by omega
          have hu := hup _ ((mem_upperBounds_iff L C _).mpr ⟨a, ha, hd, hkneg, rfl⟩)
          rw [evalLin_scaleLin] at hu
          have hprod := hmul_neg ha hkneg
          have hmul : 0 ≤ (m : ℤ) * (a.2.2.getD 0 0 * x + evalLin (a.2.1, a.2.2.tail) env) := by
            have hEq : (m : ℤ) * (a.2.2.getD 0 0 * x + evalLin (a.2.1, a.2.2.tail) env) =
                -(L : ℤ) * x + (m : ℤ) * evalLin (a.2.1, a.2.2.tail) env := by
              calc _ = ((m : ℤ) * a.2.2.getD 0 0) * x + (m : ℤ) * evalLin (a.2.1, a.2.2.tail) env := by ring
                _ = _ := by rw [hprod]
            linarith
          exact nonneg_of_mul_nonneg_right hmul hmpos
      | succ d' =>
        have ha1 : a.1 ≠ 0 := by omega
        have hd_mem := hdiv _ ((mem_divBounds_iff L C _).mpr (Or.inr ⟨a, ha, ha1, hk0, rfl⟩))
        rw [evalAtom, hd, evalLin_cons]
        rw [hd, Nat.cast_mul, evalLin_scaleLin] at hd_mem
        by_cases hkpos : 0 < a.2.2.getD 0 0
        · simp only [hkpos, decide_true, Bool.cond_true] at hd_mem
          have hprod := hmul_pos ha hkpos
          have hEq : (L : ℤ) * x + (m : ℤ) * evalLin (a.2.1, a.2.2.tail) env =
              (m : ℤ) * (a.2.2.getD 0 0 * x + evalLin (a.2.1, a.2.2.tail) env) := by
            calc _ = ((m : ℤ) * a.2.2.getD 0 0) * x + (m : ℤ) * evalLin (a.2.1, a.2.2.tail) env := by rw [hprod]
              _ = _ := by ring
          rw [hEq] at hd_mem
          exact (mul_dvd_mul_iff_left hmpos.ne').mp hd_mem
        · have hkneg : a.2.2.getD 0 0 < 0 := by omega
          simp only [hkpos, decide_false, Bool.cond_false] at hd_mem
          have hprod := hmul_neg ha hkneg
          have hEq : (L : ℤ) * x + -(m : ℤ) * evalLin (a.2.1, a.2.2.tail) env =
              (m : ℤ) * -(a.2.2.getD 0 0 * x + evalLin (a.2.1, a.2.2.tail) env) := by
            calc _ = -(((m : ℤ) * a.2.2.getD 0 0) * x) + -(m : ℤ) * evalLin (a.2.1, a.2.2.tail) env := by rw [hprod]; ring
              _ = _ := by ring
          rw [hEq] at hd_mem
          exact dvd_neg.mp ((mul_dvd_mul_iff_left hmpos.ne').mp hd_mem)

private lemma cooper_elim_y_nil {Us : List Lin} {Ds : List (ℕ × Lin)}
    (hDs : ∀ de ∈ Ds, 0 < de.1) (env : List ℤ) :
    (∃ y : ℤ,
      (∀ u ∈ Us, y ≤ evalLin u env) ∧
      (∀ de ∈ Ds, ((de.1 : ℕ) : ℤ) ∣ (y + evalLin de.2 env))) ↔
    (∃ j < modProd Ds, ∀ de ∈ Ds, ((de.1 : ℕ) : ℤ) ∣ ((j : ℤ) + evalLin de.2 env)) := by
  set M := modProd Ds
  have hM_pos : 0 < M := modProd_pos hDs
  have hM_posZ : (0 : ℤ) < (M : ℤ) := by exact_mod_cast hM_pos
  constructor
  · rintro ⟨y, -, hdiv⟩
    let j : ℕ := (y % (M : ℤ)).toNat
    have hj_cast : (j : ℤ) = y % (M : ℤ) := Int.toNat_of_nonneg (Int.emod_nonneg y hM_posZ.ne')
    have hj_lt : j < M := by
      have := Int.emod_lt_of_pos y hM_posZ
      omega
    refine ⟨j, hj_lt, fun de hde => ?_⟩
    have hdm : ((de.1 : ℕ) : ℤ) ∣ (M : ℤ) := Int.ofNat_dvd.mpr (dvd_modProd hde)
    have hsplit := Int.mul_ediv_add_emod y (M : ℤ)
    have hsub : (j : ℤ) + evalLin de.2 env = (y + evalLin de.2 env) - (M : ℤ) * (y / (M : ℤ)) := by
      linarith
    rw [hsub]
    exact dvd_sub (hdiv de hde) (dvd_mul_of_dvd_left hdm _)
  · rintro ⟨j, -, hdiv⟩
    obtain ⟨B, hB⟩ := exists_le_all (fun u => evalLin u env) Us
    let K : ℕ := ((j : ℤ) - B).toNat
    let y : ℤ := (j : ℤ) - (K : ℤ) * (M : ℤ)
    refine ⟨y, ?_, ?_⟩
    · intro u hu
      have hle_B : B ≤ evalLin u env := hB u hu
      have hK_ge : (j : ℤ) - B ≤ (K : ℤ) := by
        dsimp only [K]; omega
      have hK_nn : (0 : ℤ) ≤ (K : ℤ) := Nat.cast_nonneg K
      have hM_ge1 : (1 : ℤ) ≤ (M : ℤ) := by omega
      have hKM : (K : ℤ) ≤ (K : ℤ) * (M : ℤ) := by nlinarith
      dsimp only [y]; linarith
    · intro de hde
      have hdm : ((de.1 : ℕ) : ℤ) ∣ (M : ℤ) := Int.ofNat_dvd.mpr (dvd_modProd hde)
      have hEq : y + evalLin de.2 env = ((j : ℤ) + evalLin de.2 env) - (K : ℤ) * (M : ℤ) := by
        dsimp only [y]; ring
      rw [hEq]
      exact dvd_sub (hdiv de hde) (dvd_mul_of_dvd_right hdm _)

private lemma cooper_elim_y_nonempty {Ls Us : List Lin} {Ds : List (ℕ × Lin)}
    (hLs : Ls ≠ []) (hDs : ∀ de ∈ Ds, 0 < de.1) (env : List ℤ) :
    (∃ y : ℤ,
      (∀ b ∈ Ls, evalLin b env ≤ y) ∧
      (∀ u ∈ Us, y ≤ evalLin u env) ∧
      (∀ de ∈ Ds, ((de.1 : ℕ) : ℤ) ∣ (y + evalLin de.2 env))) ↔
    (∃ b₀ ∈ Ls, ∃ j < modProd Ds,
      (∀ b ∈ Ls, evalLin b env ≤ evalLin b₀ env + (j : ℤ)) ∧
      (∀ u ∈ Us, evalLin b₀ env + (j : ℤ) ≤ evalLin u env) ∧
      (∀ de ∈ Ds, ((de.1 : ℕ) : ℤ) ∣ (evalLin b₀ env + (j : ℤ) + evalLin de.2 env))) := by
  set M := modProd Ds
  have hM_pos : 0 < M := modProd_pos hDs
  have hM_posZ : (0 : ℤ) < (M : ℤ) := by exact_mod_cast hM_pos
  constructor
  · rintro ⟨y, hlow, hup, hdiv⟩
    obtain ⟨b₀, hb₀, hmax⟩ := exists_max_mem (fun b => evalLin b env) Ls hLs
    have hdiff_nn : 0 ≤ y - evalLin b₀ env := sub_nonneg.mpr (hlow b₀ hb₀)
    let j : ℕ := ((y - evalLin b₀ env) % (M : ℤ)).toNat
    have hj_cast : (j : ℤ) = (y - evalLin b₀ env) % (M : ℤ) :=
      Int.toNat_of_nonneg (Int.emod_nonneg _ hM_posZ.ne')
    have hj_lt : j < M := by
      have := Int.emod_lt_of_pos (y - evalLin b₀ env) hM_posZ
      omega
    have hq_nn : 0 ≤ (y - evalLin b₀ env) / (M : ℤ) := Int.ediv_nonneg hdiff_nn hM_posZ.le
    have hsplit := Int.mul_ediv_add_emod (y - evalLin b₀ env) (M : ℤ)
    have hy'_eq : evalLin b₀ env + (j : ℤ) = y - (M : ℤ) * ((y - evalLin b₀ env) / (M : ℤ)) := by
      linarith
    refine ⟨b₀, hb₀, j, hj_lt, ?_, ?_, ?_⟩
    · intro b hb
      have := hmax b hb
      have : (0 : ℤ) ≤ (j : ℤ) := Nat.cast_nonneg j
      linarith
    · intro u hu
      have := hup u hu
      have hMq : 0 ≤ (M : ℤ) * ((y - evalLin b₀ env) / (M : ℤ)) := mul_nonneg hM_posZ.le hq_nn
      linarith
    · intro de hde
      have hdm : ((de.1 : ℕ) : ℤ) ∣ (M : ℤ) := Int.ofNat_dvd.mpr (dvd_modProd hde)
      have hEq : evalLin b₀ env + (j : ℤ) + evalLin de.2 env =
          (y + evalLin de.2 env) - (M : ℤ) * ((y - evalLin b₀ env) / (M : ℤ)) := by linarith
      rw [hEq]
      exact dvd_sub (hdiv de hde) (dvd_mul_of_dvd_left hdm _)
  · rintro ⟨b₀, _, j, _, hlow, hup, hdiv⟩
    exact ⟨evalLin b₀ env + (j : ℤ), hlow, hup, hdiv⟩

private lemma evalDNF_elimConj (C : Conj) (env : List ℤ) :
    evalDNF (elimConj C) env ↔ ∃ x : ℤ, evalConj C (x :: env) := by
  rw [cooper_scale_iff C env]
  unfold elimConj
  dsimp only
  set L := leadProd C
  set F := freeAtoms C
  set Ls := lowerBounds L C
  set Us := upperBounds L C
  set Ds := divBounds L C
  set M := modProd Ds
  have hDs_pos : ∀ de ∈ Ds, 0 < de.1 := divBounds_pos C
  have hM_pos : 0 < M := modProd_pos hDs_pos
  cases hLs : Ls with
  | nil =>
    rw [List.isEmpty_nil, Bool.cond_true]
    rw [show (∃ y : ℤ,
        (∀ b ∈ ([] : List Lin), evalLin b env ≤ y) ∧
        (∀ u ∈ Us, y ≤ evalLin u env) ∧
        (∀ de ∈ Ds, ((de.1 : ℕ) : ℤ) ∣ (y + evalLin de.2 env))) ↔
      (∃ j < M, ∀ de ∈ Ds, ((de.1 : ℕ) : ℤ) ∣ ((j : ℤ) + evalLin de.2 env)) by
        simpa using cooper_elim_y_nil hDs_pos env]
    simp only [evalDNF, evalConj, List.mem_map, List.mem_range, exists_exists_and_eq_and,
      List.mem_append]
    constructor
    · rintro ⟨j, hj, hsat⟩
      refine ⟨fun a ha => hsat a (Or.inl ha), j, hj, fun de hde => ?_⟩
      have h := hsat (de.1, shiftLin (j : ℤ) de.2) (Or.inr ⟨de, hde, rfl⟩)
      rw [evalAtom_of_pos (hDs_pos de hde), evalLin_shiftLin, add_comm] at h
      exact h
    · rintro ⟨hF, j, hj, hdiv⟩
      refine ⟨j, hj, fun a ha => ?_⟩
      rcases ha with h1 | ⟨de, hde, rfl⟩
      · exact hF a h1
      · rw [evalAtom_of_pos (hDs_pos de hde), evalLin_shiftLin, add_comm]
        exact hdiv de hde
  | cons b₁ tl =>
    have hLs_ne : b₁ :: tl ≠ [] := List.cons_ne_nil b₁ tl
    rw [List.isEmpty_cons, Bool.cond_false]
    rw [cooper_elim_y_nonempty hLs_ne hDs_pos env]
    simp only [evalDNF, evalConj, List.mem_flatMap, List.mem_map, List.mem_range]
    constructor
    · rintro ⟨C', ⟨b₀, hb₀, j, hj, rfl⟩, hsat⟩
      simp only [List.mem_append, List.mem_map] at hsat
      refine ⟨fun a ha => hsat a (Or.inl (Or.inl (Or.inl ha))), b₀, hb₀, j, hj, ?_, ?_, ?_⟩
      · intro b hb
        have h := hsat (0, subLin (shiftLin (j : ℤ) b₀) b)
          (Or.inl (Or.inl (Or.inr ⟨b, hb, rfl⟩)))
        rw [evalAtom_zero, evalLin_subLin, evalLin_shiftLin] at h
        linarith
      · intro u hu
        have h := hsat (0, subLin u (shiftLin (j : ℤ) b₀))
          (Or.inl (Or.inr ⟨u, hu, rfl⟩))
        rw [evalAtom_zero, evalLin_subLin, evalLin_shiftLin] at h
        linarith
      · intro de hde
        have h := hsat (de.1, addLin (shiftLin (j : ℤ) b₀) de.2)
          (Or.inr ⟨de, hde, rfl⟩)
        rw [evalAtom_of_pos (hDs_pos de hde), evalLin_addLin, evalLin_shiftLin] at h
        exact h
    · rintro ⟨hF, b₀, hb₀, j, hj, hlow, hup, hdiv⟩
      refine ⟨_, ⟨b₀, hb₀, j, hj, rfl⟩, fun a ha => ?_⟩
      simp only [List.mem_append, List.mem_map] at ha
      rcases ha with ((h1 | ⟨b, hb, rfl⟩) | ⟨u, hu, rfl⟩) | ⟨de, hde, rfl⟩
      · exact hF a h1
      · rw [evalAtom_zero, evalLin_subLin, evalLin_shiftLin]
        linarith [hlow b hb]
      · rw [evalAtom_zero, evalLin_subLin, evalLin_shiftLin]
        linarith [hup u hu]
      · rw [evalAtom_of_pos (hDs_pos de hde), evalLin_addLin, evalLin_shiftLin]
        exact hdiv de hde

private lemma evalDNF_elimDNF (φ : DNF) (env : List ℤ) :
    evalDNF (elimDNF φ) env ↔ ∃ x : ℤ, evalDNF φ (x :: env) := by
  simp only [elimDNF, evalDNF, List.mem_flatMap]
  constructor
  · rintro ⟨C', ⟨C, hC, hC'⟩, hsat⟩
    obtain ⟨x, hx⟩ := (evalDNF_elimConj C env).mp ⟨C', hC', hsat⟩
    exact ⟨x, C, hC, hx⟩
  · rintro ⟨x, C, hC, hx⟩
    obtain ⟨C', hC', hsat⟩ := (evalDNF_elimConj C env).mpr ⟨x, hx⟩
    exact ⟨C', ⟨C, hC, hC'⟩, hsat⟩

private lemma evalDNF_elimMany (n : ℕ) (φ : DNF) (env : List ℤ) :
    evalDNF (elimMany n φ) env ↔ ∃ xs : List ℤ, xs.length = n ∧ evalDNF φ (xs ++ env) := by
  induction n generalizing env with
  | zero =>
    simp only [elimMany, Function.iterate_zero, id_eq]
    constructor
    · intro h; exact ⟨[], rfl, h⟩
    · rintro ⟨xs, hlen, h⟩
      have hnil : xs = [] := List.eq_nil_of_length_eq_zero hlen
      subst hnil; exact h
  | succ n ih =>
    have hsucc : elimMany (n + 1) φ = elimDNF (elimMany n φ) :=
      Function.iterate_succ_apply' elimDNF n φ
    rw [hsucc, evalDNF_elimDNF]
    simp_rw [ih]
    constructor
    · rintro ⟨x, xs, hlen, hsat⟩
      refine ⟨xs ++ [x], by simp [hlen], ?_⟩
      simpa [List.append_assoc] using hsat
    · rintro ⟨ys, hlen, hsat⟩
      have hne : ys ≠ [] := by intro h; subst h; simp at hlen
      let xs := ys.dropLast
      let x := ys.getLast hne
      have hys : xs ++ [x] = ys := List.dropLast_append_getLast hne
      refine ⟨x, xs, by dsimp only [xs]; rw [List.length_dropLast, hlen]; omega, ?_⟩
      have hcat : xs ++ x :: env = ys ++ env := by
        rw [← hys, List.append_assoc]; rfl
      rw [hcat]; exact hsat

private lemma primrec_leadProd : Primrec leadProd := by
  unfold leadProd
  let k : Conj × (Atom × ℕ) → ℤ := fun p => p.2.1.2.2.getD 0 0
  have hk : Primrec k :=
    (Primrec.list_getD (0 : ℤ)).comp
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)))
      (Primrec.const 0)
  have hacc : Primrec (fun p : Conj × (Atom × ℕ) => p.2.2) :=
    Primrec.snd.comp Primrec.snd
  have hstep : Primrec₂ (fun (_ : Conj) (bs : Atom × ℕ) =>
      let k := bs.1.2.2.getD 0 0
      cond (k == 0) bs.2 (k.natAbs * bs.2)) :=
    (Primrec.cond (Primrec.beq.comp hk (Primrec.const (0 : ℤ))) hacc
      (Primrec.nat_mul.comp (primrec_int_natAbs.comp hk) hacc)).to₂
  exact Primrec.list_foldr (Primrec.id (α := Conj)) (Primrec.const 1) hstep

private lemma primrec_freeAtoms : Primrec freeAtoms := by
  unfold freeAtoms
  let a : Conj × (Atom × Conj) → Atom := fun p => p.2.1
  let acc : Conj × (Atom × Conj) → Conj := fun p => p.2.2
  have ha : Primrec a := Primrec.fst.comp Primrec.snd
  have hacc : Primrec acc := Primrec.snd.comp Primrec.snd
  have hk : Primrec (fun p : Conj × (Atom × Conj) => (a p).2.2.getD 0 0) :=
    (Primrec.list_getD (0 : ℤ)).comp (Primrec.snd.comp (Primrec.snd.comp ha)) (Primrec.const 0)
  have hatom : Primrec (fun p : Conj × (Atom × Conj) => ((a p).1, ((a p).2.1, (a p).2.2.tail))) :=
    Primrec.pair (Primrec.fst.comp ha)
      (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp ha))
        (Primrec.list_tail.comp (Primrec.snd.comp (Primrec.snd.comp ha))))
  have hstep : Primrec₂ (fun (_ : Conj) (bs : Atom × Conj) =>
      cond (bs.1.2.2.getD 0 0 == 0) ((bs.1.1, (bs.1.2.1, bs.1.2.2.tail)) :: bs.2) bs.2) :=
    (Primrec.cond (Primrec.beq.comp hk (Primrec.const (0 : ℤ)))
      (Primrec.list_cons.comp hatom hacc) hacc).to₂
  exact Primrec.list_foldr (Primrec.id (α := Conj)) (Primrec.const ([] : Conj)) hstep

private lemma primrec_lowerBounds : Primrec₂ lowerBounds := by
  change Primrec (fun p : ℕ × Conj => lowerBounds p.1 p.2)
  unfold lowerBounds
  let L : (ℕ × Conj) × (Atom × List Lin) → ℕ := fun p => p.1.1
  let a : (ℕ × Conj) × (Atom × List Lin) → Atom := fun p => p.2.1
  let acc : (ℕ × Conj) × (Atom × List Lin) → List Lin := fun p => p.2.2
  have hL : Primrec L := Primrec.fst.comp Primrec.fst
  have ha : Primrec a := Primrec.fst.comp Primrec.snd
  have hacc : Primrec acc := Primrec.snd.comp Primrec.snd
  have hk : Primrec (fun p => (a p).2.2.getD 0 0) :=
    (Primrec.list_getD (0 : ℤ)).comp (Primrec.snd.comp (Primrec.snd.comp ha)) (Primrec.const 0)
  have hcond : Primrec (fun p => ((a p).1 == 0) && decide (0 < (a p).2.2.getD 0 0)) :=
    Primrec.and.comp (Primrec.beq.comp (Primrec.fst.comp ha) (Primrec.const 0))
      (primrec_int_pos.comp hk)
  have hm : Primrec (fun p => -((L p / ((a p).2.2.getD 0 0).natAbs : ℕ) : ℤ)) :=
    primrec_int_neg.comp (primrec_int_ofNat.comp (Primrec.nat_div.comp hL (primrec_int_natAbs.comp hk)))
  have hlin : Primrec (fun p => ((a p).2.1, (a p).2.2.tail)) :=
    Primrec.pair (Primrec.fst.comp (Primrec.snd.comp ha))
      (Primrec.list_tail.comp (Primrec.snd.comp (Primrec.snd.comp ha)))
  have hstep : Primrec₂ (fun (p : ℕ × Conj) (bs : Atom × List Lin) =>
      let k := bs.1.2.2.getD 0 0
      cond ((bs.1.1 == 0) && decide (0 < k))
        (scaleLin (-((p.1 / k.natAbs : ℕ) : ℤ)) (bs.1.2.1, bs.1.2.2.tail) :: bs.2) bs.2) :=
    (Primrec.cond hcond (Primrec.list_cons.comp (primrec_scaleLin.comp hm hlin) hacc) hacc).to₂
  exact Primrec.list_foldr (Primrec.snd (α := ℕ) (β := Conj)) (Primrec.const ([] : List Lin)) hstep

private lemma primrec_upperBounds : Primrec₂ upperBounds := by
  change Primrec (fun p : ℕ × Conj => upperBounds p.1 p.2)
  unfold upperBounds
  let L : (ℕ × Conj) × (Atom × List Lin) → ℕ := fun p => p.1.1
  let a : (ℕ × Conj) × (Atom × List Lin) → Atom := fun p => p.2.1
  let acc : (ℕ × Conj) × (Atom × List Lin) → List Lin := fun p => p.2.2
  have hL : Primrec L := Primrec.fst.comp Primrec.fst
  have ha : Primrec a := Primrec.fst.comp Primrec.snd
  have hacc : Primrec acc := Primrec.snd.comp Primrec.snd
  have hk : Primrec (fun p => (a p).2.2.getD 0 0) :=
    (Primrec.list_getD (0 : ℤ)).comp (Primrec.snd.comp (Primrec.snd.comp ha)) (Primrec.const 0)
  have hcond : Primrec (fun p => ((a p).1 == 0) && decide ((a p).2.2.getD 0 0 < 0)) :=
    Primrec.and.comp (Primrec.beq.comp (Primrec.fst.comp ha) (Primrec.const 0))
      (primrec_int_lt.comp hk (Primrec.const (0 : ℤ)))
  have hm : Primrec (fun p => ((L p / ((a p).2.2.getD 0 0).natAbs : ℕ) : ℤ)) :=
    primrec_int_ofNat.comp (Primrec.nat_div.comp hL (primrec_int_natAbs.comp hk))
  have hlin : Primrec (fun p => ((a p).2.1, (a p).2.2.tail)) :=
    Primrec.pair (Primrec.fst.comp (Primrec.snd.comp ha))
      (Primrec.list_tail.comp (Primrec.snd.comp (Primrec.snd.comp ha)))
  have hstep : Primrec₂ (fun (p : ℕ × Conj) (bs : Atom × List Lin) =>
      let k := bs.1.2.2.getD 0 0
      cond ((bs.1.1 == 0) && decide (k < 0))
        (scaleLin (((p.1 / k.natAbs : ℕ) : ℤ)) (bs.1.2.1, bs.1.2.2.tail) :: bs.2) bs.2) :=
    (Primrec.cond hcond (Primrec.list_cons.comp (primrec_scaleLin.comp hm hlin) hacc) hacc).to₂
  exact Primrec.list_foldr (Primrec.snd (α := ℕ) (β := Conj)) (Primrec.const ([] : List Lin)) hstep

private lemma primrec_divBounds : Primrec₂ divBounds := by
  change Primrec (fun p : ℕ × Conj => divBounds p.1 p.2)
  unfold divBounds
  let L : (ℕ × Conj) × (Atom × List (ℕ × Lin)) → ℕ := fun p => p.1.1
  let a : (ℕ × Conj) × (Atom × List (ℕ × Lin)) → Atom := fun p => p.2.1
  let acc : (ℕ × Conj) × (Atom × List (ℕ × Lin)) → List (ℕ × Lin) := fun p => p.2.2
  have hL : Primrec L := Primrec.fst.comp Primrec.fst
  have ha : Primrec a := Primrec.fst.comp Primrec.snd
  have hacc : Primrec acc := Primrec.snd.comp Primrec.snd
  have hk : Primrec (fun p => (a p).2.2.getD 0 0) :=
    (Primrec.list_getD (0 : ℤ)).comp (Primrec.snd.comp (Primrec.snd.comp ha)) (Primrec.const 0)
  have hcond : Primrec (fun p => !((a p).1 == 0) && !((a p).2.2.getD 0 0 == 0)) :=
    Primrec.and.comp (Primrec.not.comp (Primrec.beq.comp (Primrec.fst.comp ha) (Primrec.const 0)))
      (Primrec.not.comp (Primrec.beq.comp hk (Primrec.const (0 : ℤ))))
  have hm : Primrec (fun p => L p / ((a p).2.2.getD 0 0).natAbs) :=
    Primrec.nat_div.comp hL (primrec_int_natAbs.comp hk)
  have hs : Primrec (fun p => cond (decide (0 < (a p).2.2.getD 0 0))
      ((L p / ((a p).2.2.getD 0 0).natAbs : ℕ) : ℤ)
      (-((L p / ((a p).2.2.getD 0 0).natAbs : ℕ) : ℤ))) :=
    Primrec.cond (primrec_int_pos.comp hk) (primrec_int_ofNat.comp hm)
      (primrec_int_neg.comp (primrec_int_ofNat.comp hm))
  have hlin : Primrec (fun p => ((a p).2.1, (a p).2.2.tail)) :=
    Primrec.pair (Primrec.fst.comp (Primrec.snd.comp ha))
      (Primrec.list_tail.comp (Primrec.snd.comp (Primrec.snd.comp ha)))
  have hitem : Primrec (fun p => (L p / ((a p).2.2.getD 0 0).natAbs * (a p).1,
      scaleLin (cond (decide (0 < (a p).2.2.getD 0 0))
        ((L p / ((a p).2.2.getD 0 0).natAbs : ℕ) : ℤ)
        (-((L p / ((a p).2.2.getD 0 0).natAbs : ℕ) : ℤ))) ((a p).2.1, (a p).2.2.tail))) :=
    Primrec.pair (Primrec.nat_mul.comp hm (Primrec.fst.comp ha))
      (primrec_scaleLin.comp hs hlin)
  have hstep : Primrec₂ (fun (p : ℕ × Conj) (bs : Atom × List (ℕ × Lin)) =>
      let k := bs.1.2.2.getD 0 0
      cond (!(bs.1.1 == 0) && !(k == 0))
        (let m := p.1 / k.natAbs
         let s : ℤ := cond (decide (0 < k)) (m : ℤ) (-(m : ℤ))
         (m * bs.1.1, scaleLin s (bs.1.2.1, bs.1.2.2.tail)) :: bs.2) bs.2) :=
    (Primrec.cond hcond (Primrec.list_cons.comp hitem hacc) hacc).to₂
  exact Primrec.list_cons.comp
    (Primrec.pair Primrec.fst (Primrec.const ((0 : ℤ), ([] : List ℤ))))
    (Primrec.list_foldr (Primrec.snd (α := ℕ) (β := Conj))
      (Primrec.const ([] : List (ℕ × Lin))) hstep)

private lemma primrec_modProd : Primrec modProd := by
  unfold modProd
  have hstep : Primrec₂ (fun (_ : List (ℕ × Lin)) (bs : (ℕ × Lin) × ℕ) => bs.1.1 * bs.2) :=
    (Primrec.nat_mul.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂
  exact Primrec.list_foldr (Primrec.id (α := List (ℕ × Lin))) (Primrec.const 1) hstep

private lemma primrec_elimConj : Primrec elimConj := by
  unfold elimConj
  have hL : Primrec leadProd := primrec_leadProd
  have hF : Primrec freeAtoms := primrec_freeAtoms
  have hLs : Primrec (fun C : Conj => lowerBounds (leadProd C) C) :=
    primrec_lowerBounds.comp hL Primrec.id
  have hUs : Primrec (fun C : Conj => upperBounds (leadProd C) C) :=
    primrec_upperBounds.comp hL Primrec.id
  have hDs : Primrec (fun C : Conj => divBounds (leadProd C) C) :=
    primrec_divBounds.comp hL Primrec.id
  have hM : Primrec (fun C : Conj => modProd (divBounds (leadProd C) C)) :=
    primrec_modProd.comp hDs
  have hbranch1 : Primrec (fun C : Conj =>
      (List.range (modProd (divBounds (leadProd C) C))).map fun j : ℕ =>
        freeAtoms C ++ (divBounds (leadProd C) C).map fun de => (de.1, shiftLin (j : ℤ) de.2)) := by
    refine Primrec.list_map (Primrec.list_range.comp hM) ?_
    change Primrec (fun p : Conj × ℕ =>
      freeAtoms p.1 ++ (divBounds (leadProd p.1) p.1).map fun de => (de.1, shiftLin (p.2 : ℤ) de.2))
    refine Primrec.list_append.comp (hF.comp Primrec.fst) ?_
    refine Primrec.list_map (hDs.comp Primrec.fst) ?_
    change Primrec (fun q : (Conj × ℕ) × (ℕ × Lin) => (q.2.1, shiftLin (q.1.2 : ℤ) q.2.2))
    exact Primrec.pair (Primrec.fst.comp Primrec.snd)
      (primrec_shiftLin.comp (primrec_int_ofNat.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.snd.comp Primrec.snd))
  have hbranch2 : Primrec (fun C : Conj =>
      (lowerBounds (leadProd C) C).flatMap fun b₀ =>
        (List.range (modProd (divBounds (leadProd C) C))).map fun j : ℕ =>
          let y := shiftLin (j : ℤ) b₀
          freeAtoms C ++
          ((lowerBounds (leadProd C) C).map fun b => (0, subLin y b)) ++
          ((upperBounds (leadProd C) C).map fun u => (0, subLin u y)) ++
          ((divBounds (leadProd C) C).map fun de => (de.1, addLin y de.2))) := by
    refine Primrec.list_flatMap hLs ?_
    change Primrec (fun q : Conj × Lin =>
      (List.range (modProd (divBounds (leadProd q.1) q.1))).map fun j : ℕ =>
        let y := shiftLin (j : ℤ) q.2
        freeAtoms q.1 ++
        ((lowerBounds (leadProd q.1) q.1).map fun b => (0, subLin y b)) ++
        ((upperBounds (leadProd q.1) q.1).map fun u => (0, subLin u y)) ++
        ((divBounds (leadProd q.1) q.1).map fun de => (de.1, addLin y de.2)))
    refine Primrec.list_map (Primrec.list_range.comp (hM.comp Primrec.fst)) ?_
    change Primrec (fun p : (Conj × Lin) × ℕ =>
      let y := shiftLin (p.2 : ℤ) p.1.2
      freeAtoms p.1.1 ++
      ((lowerBounds (leadProd p.1.1) p.1.1).map fun b => (0, subLin y b)) ++
      ((upperBounds (leadProd p.1.1) p.1.1).map fun u => (0, subLin u y)) ++
      ((divBounds (leadProd p.1.1) p.1.1).map fun de => (de.1, addLin y de.2)))
    let C' : (Conj × Lin) × ℕ → Conj := fun p => p.1.1
    let y : (Conj × Lin) × ℕ → Lin := fun p => shiftLin (p.2 : ℤ) p.1.2
    have hC' : Primrec C' := Primrec.fst.comp Primrec.fst
    have hy : Primrec y :=
      primrec_shiftLin.comp (primrec_int_ofNat.comp Primrec.snd) (Primrec.snd.comp Primrec.fst)
    have hp1 : Primrec (fun p : (Conj × Lin) × ℕ =>
        (lowerBounds (leadProd (C' p)) (C' p)).map fun b => (0, subLin (y p) b)) :=
      Primrec.list_map (hLs.comp hC')
        ((Primrec.pair (Primrec.const 0)
          (primrec_subLin.comp (hy.comp Primrec.fst) Primrec.snd)).to₂)
    have hp2 : Primrec (fun p : (Conj × Lin) × ℕ =>
        (upperBounds (leadProd (C' p)) (C' p)).map fun u => (0, subLin u (y p))) :=
      Primrec.list_map (hUs.comp hC')
        ((Primrec.pair (Primrec.const 0)
          (primrec_subLin.comp Primrec.snd (hy.comp Primrec.fst))).to₂)
    have hp3 : Primrec (fun p : (Conj × Lin) × ℕ =>
        (divBounds (leadProd (C' p)) (C' p)).map fun de => (de.1, addLin (y p) de.2)) :=
      Primrec.list_map (hDs.comp hC')
        ((Primrec.pair (Primrec.fst.comp Primrec.snd)
          (primrec_addLin.comp (hy.comp Primrec.fst) (Primrec.snd.comp Primrec.snd))).to₂)
    exact Primrec.list_append.comp
      (Primrec.list_append.comp
        (Primrec.list_append.comp (hF.comp hC') hp1) hp2) hp3
  exact Primrec.cond (primrec_list_isEmpty.comp hLs) hbranch1 hbranch2

private lemma primrec_elimDNF : Primrec elimDNF :=
  Primrec.list_flatMap Primrec.id (primrec_elimConj.comp₂ Primrec₂.right)

private lemma primrec_elimMany : Primrec₂ elimMany :=
  Primrec.to₂ (Primrec.nat_iterate Primrec.fst Primrec.snd (primrec_elimDNF.comp₂ Primrec₂.right))

/- ### Part 5: Translating `CheckIncluded` and BVAS invariant clauses into DNF -/

private abbrev Input := Σ d : ℕ, Bvas d × (Fin d → ℤ)
private abbrev RawInput := ℕ × List (List ℤ) × List (List ℤ) × List (List ℤ) × List ℤ
private abbrev SemilinearCode := List (List ℕ × List (List ℕ))

private def innerConj (d : ℕ) (base₀ : List ℤ) (P₀ : List (List ℕ))
    (bp : List ℕ × List (List ℕ)) : Conj :=
  ((List.range bp.2.length).map fun j => (0, ((0 : ℤ), unitVec j))) ++
  ((List.range d).flatMap fun i =>
    let diff : Lin :=
      (base₀.getD i 0 - (bp.1.getD i 0 : ℤ),
        (bp.2.map fun p => -((p.getD i 0 : ℕ) : ℤ)) ++
        (P₀.map fun p => ((p.getD i 0 : ℕ) : ℤ)))
    [(0, diff), (0, scaleLin (-1) diff)])

private def guardConj (d : ℕ) (base₀ : List ℤ) (P₀ : List (List ℕ)) : Conj :=
  ((List.range P₀.length).map fun k => (0, ((0 : ℤ), unitVec k))) ++
  ((List.range d).map fun i =>
    (0, (base₀.getD i 0, P₀.map fun p => ((p.getD i 0 : ℕ) : ℤ))))

private def memSDNF (d : ℕ) (base₀ : List ℤ) (P₀ : List (List ℕ)) (S : SemilinearCode) : DNF :=
  S.flatMap fun bp => elimMany bp.2.length [innerConj d base₀ P₀ bp]

private def checkIncludedBool (d : ℕ) (base₀ : List ℤ) (P₀ : List (List ℕ))
    (S : SemilinearCode) : Bool :=
  !(evalDNF0 (elimMany P₀.length (andDNF [guardConj d base₀ P₀] (negDNF (memSDNF d base₀ P₀ S)))))

private lemma dotList_map_nat_periods (P : List (List ℕ)) (i : ℕ) (c : Fin P.length → ℕ) :
    dotList (P.map fun p => ((p.getD i 0 : ℕ) : ℤ)) (List.ofFn fun k : Fin P.length => (c k : ℤ)) =
      ∑ k : Fin P.length, (c k : ℤ) * ((P[k].getD i 0 : ℕ) : ℤ) := by
  rw [dotList_eq_sum_range P.length _ _ (by simp)]
  rw [← Fin.sum_univ_eq_sum_range (fun k =>
    (P.map fun p => ((p.getD i 0 : ℕ) : ℤ)).getD k 0 *
    (List.ofFn fun k : Fin P.length => (c k : ℤ)).getD k 0) P.length]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h1 : (P.map fun p => ((p.getD i 0 : ℕ) : ℤ)).getD k.1 0 = ((P[k].getD i 0 : ℕ) : ℤ) := by
    simp [List.getD_eq_getElem?_getD, k.2]
  have h2 : (List.ofFn fun j : Fin P.length => (c j : ℤ)).getD k.1 0 = (c k : ℤ) := by
    simp [List.getD_eq_getElem?_getD, k.2]
  rw [h1, h2, mul_comm]

private lemma dotList_map_neg_nat_periods (P : List (List ℕ)) (i : ℕ) (c : Fin P.length → ℕ) :
    dotList (P.map fun p => -((p.getD i 0 : ℕ) : ℤ)) (List.ofFn fun k : Fin P.length => (c k : ℤ)) =
      -(∑ k : Fin P.length, (c k : ℤ) * ((P[k].getD i 0 : ℕ) : ℤ)) := by
  have hmap : (P.map fun p => -((p.getD i 0 : ℕ) : ℤ)) =
      (P.map fun p => ((p.getD i 0 : ℕ) : ℤ)).map fun a => (-1 : ℤ) * a := by
    rw [List.map_map]; refine List.map_congr_left fun p _ => by simp
  rw [hmap, dotList_map_mul, dotList_map_nat_periods]
  ring

private lemma evalConj_guardConj_iff (d : ℕ) (base₀ : List ℤ) (P₀ : List (List ℕ))
    (cs : List ℤ) (hlen : cs.length = P₀.length) :
    evalConj (guardConj d base₀ P₀) cs ↔
      (∀ k : Fin P₀.length, 0 ≤ cs.getD k.1 0) ∧
      ∃ c : Fin P₀.length → ℕ,
        cs = List.ofFn (fun k => (c k : ℤ)) ∧
        ∀ i : Fin d, 0 ≤ base₀.getD i.1 0 +
          ∑ k : Fin P₀.length, (c k : ℤ) * ((P₀[k].getD i.1 0 : ℕ) : ℤ) := by
  simp only [guardConj, evalConj, List.mem_append, List.mem_map, List.mem_range]
  constructor
  · intro h
    have hnn : ∀ k : Fin P₀.length, 0 ≤ cs.getD k.1 0 := by
      intro k
      have hk := h (0, ((0 : ℤ), unitVec k.1)) (Or.inl ⟨k.1, k.2, rfl⟩)
      rw [evalAtom_zero, evalLin, zero_add, dotList_unitVec] at hk
      exact hk
    let c : Fin P₀.length → ℕ := fun k => (cs.getD k.1 0).toNat
    have hcs_eq : cs = List.ofFn (fun k => (c k : ℤ)) := by
      refine List.ext_getElem (by simp [hlen]) fun k hk _ => ?_
      have hk' : k < P₀.length := hlen ▸ hk
      have hcast : ((cs.getD k 0).toNat : ℤ) = cs.getD k 0 := Int.toNat_of_nonneg (hnn ⟨k, hk'⟩)
      rw [List.getElem_ofFn]
      dsimp only [c]
      rw [hcast, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
    refine ⟨hnn, c, hcs_eq, fun i => ?_⟩
    have hi := h (0, (base₀.getD i.1 0, P₀.map fun p => ((p.getD i.1 0 : ℕ) : ℤ)))
      (Or.inr ⟨i.1, i.2, rfl⟩)
    rw [evalAtom_zero, evalLin, hcs_eq, dotList_map_nat_periods] at hi
    exact hi
  · rintro ⟨hnn, c, rfl, hvec⟩ a ha
    rcases ha with ⟨k, hk, rfl⟩ | ⟨i, hi, rfl⟩
    · rw [evalAtom_zero, evalLin, zero_add, dotList_unitVec]
      exact hnn ⟨k, hk⟩
    · rw [evalAtom_zero, evalLin, dotList_map_nat_periods]
      exact hvec ⟨i, hi⟩

private lemma evalDNF_memSDNF_iff (d : ℕ) (base₀ : List ℤ) (P₀ : List (List ℕ))
    (S : SemilinearCode) (c : Fin P₀.length → ℕ) :
    let cs : List ℤ := List.ofFn fun k => (c k : ℤ)
    evalDNF (memSDNF d base₀ P₀ S) cs ↔
      ∃ bp ∈ S, ∃ c' : Fin bp.2.length → ℕ,
        ∀ i : Fin d,
          base₀.getD i.1 0 + ∑ k : Fin P₀.length, (c k : ℤ) * ((P₀[k].getD i.1 0 : ℕ) : ℤ) =
          (bp.1.getD i.1 0 : ℤ) +
            ∑ j : Fin bp.2.length, (c' j : ℤ) * ((bp.2[j].getD i.1 0 : ℕ) : ℤ) := by
  intro cs
  simp only [memSDNF, evalDNF, List.mem_flatMap]
  have hstep : ∀ bp : List ℕ × List (List ℕ),
      (∃ C ∈ elimMany bp.2.length [innerConj d base₀ P₀ bp], evalConj C cs) ↔
      ∃ c' : Fin bp.2.length → ℕ,
        ∀ i : Fin d,
          base₀.getD i.1 0 + ∑ k : Fin P₀.length, (c k : ℤ) * ((P₀[k].getD i.1 0 : ℕ) : ℤ) =
          (bp.1.getD i.1 0 : ℤ) +
            ∑ j : Fin bp.2.length, (c' j : ℤ) * ((bp.2[j].getD i.1 0 : ℕ) : ℤ) := by
    intro bp
    change evalDNF (elimMany bp.2.length [innerConj d base₀ P₀ bp]) cs ↔ _
    rw [evalDNF_elimMany]
    simp only [evalDNF, List.mem_singleton, exists_eq_left]
    constructor
    · rintro ⟨cs', hlen', hsat⟩
      simp only [innerConj, evalConj, List.mem_append, List.mem_map, List.mem_range,
        List.mem_flatMap] at hsat
      have hnn' : ∀ j : Fin bp.2.length, 0 ≤ cs'.getD j.1 0 := by
        intro j
        have hj := hsat (0, ((0 : ℤ), unitVec j.1)) (Or.inl ⟨j.1, j.2, rfl⟩)
        rw [evalAtom_zero, evalLin, zero_add, dotList_unitVec] at hj
        have hget : (cs' ++ cs).getD j.1 0 = cs'.getD j.1 0 := by
          have hj' : j.1 < cs'.length := hlen'.symm ▸ j.2
          simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hj']
        rwa [hget] at hj
      let c' : Fin bp.2.length → ℕ := fun j => (cs'.getD j.1 0).toNat
      have hcs'_eq : cs' = List.ofFn (fun j => (c' j : ℤ)) := by
        refine List.ext_getElem (by simp [hlen']) fun j hj _ => ?_
        have hj' : j < bp.2.length := hlen' ▸ hj
        have hcast : ((cs'.getD j 0).toNat : ℤ) = cs'.getD j 0 := Int.toNat_of_nonneg (hnn' ⟨j, hj'⟩)
        rw [List.getElem_ofFn]
        dsimp only [c']
        rw [hcast, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
      refine ⟨c', fun i => ?_⟩
      let diff : Lin :=
        (base₀.getD i.1 0 - (bp.1.getD i.1 0 : ℤ),
          (bp.2.map fun p => -((p.getD i.1 0 : ℕ) : ℤ)) ++
          (P₀.map fun p => ((p.getD i.1 0 : ℕ) : ℤ)))
      have hpos := hsat (0, diff) (Or.inr ⟨i.1, i.2, by simp [diff]⟩)
      have hneg := hsat (0, scaleLin (-1) diff) (Or.inr ⟨i.1, i.2, by simp [diff]⟩)
      rw [evalAtom_zero] at hpos hneg
      rw [evalLin_scaleLin] at hneg
      have hzero : evalLin diff (cs' ++ cs) = 0 := by linarith
      have hev : evalLin diff (cs' ++ cs) =
          (base₀.getD i.1 0 + ∑ k : Fin P₀.length, (c k : ℤ) * ((P₀[k].getD i.1 0 : ℕ) : ℤ)) -
          ((bp.1.getD i.1 0 : ℤ) +
            ∑ j : Fin bp.2.length, (c' j : ℤ) * ((bp.2[j].getD i.1 0 : ℕ) : ℤ)) := by
        dsimp only [diff, evalLin]
        rw [hcs'_eq, dotList_append _ _ _ _ (by simp), dotList_map_neg_nat_periods,
          dotList_map_nat_periods]
        ring
      linarith
    · rintro ⟨c', heq⟩
      let cs' : List ℤ := List.ofFn fun j => (c' j : ℤ)
      refine ⟨cs', by simp [cs'], ?_⟩
      simp only [innerConj, evalConj, List.mem_append, List.mem_map, List.mem_range,
        List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]
      intro a ha
      rcases ha with ⟨j, hj, rfl⟩ | ⟨i, hi, rfl | rfl⟩
      · rw [evalAtom_zero, evalLin, zero_add, dotList_unitVec]
        have hj' : j < cs'.length := by simp [cs', hj]
        simp [cs', List.getD_eq_getElem?_getD, List.getElem?_append_left hj', hj]
      · rw [evalAtom_zero, evalLin, dotList_append _ _ _ _ (by simp [cs']),
          dotList_map_neg_nat_periods, dotList_map_nat_periods]
        linarith [heq ⟨i, hi⟩]
      · rw [evalAtom_zero, evalLin_scaleLin, evalLin, dotList_append _ _ _ _ (by simp [cs']),
          dotList_map_neg_nat_periods, dotList_map_nat_periods]
        linarith [heq ⟨i, hi⟩]
  constructor
  · rintro ⟨C, ⟨bp, hbp, hC⟩, hsat⟩
    exact ⟨bp, hbp, (hstep bp).mp ⟨C, hC, hsat⟩⟩
  · rintro ⟨bp, hbp, hc'⟩
    obtain ⟨C, hC, hsat⟩ := (hstep bp).mpr hc'
    exact ⟨C, ⟨bp, hbp, hC⟩, hsat⟩

private lemma evalDNF_singleton (C : Conj) (env : List ℤ) :
    evalDNF [C] env ↔ evalConj C env := by
  simp [evalDNF]

private lemma checkIncludedBool_eq_true_iff (d : ℕ) (base₀ : List ℤ) (P₀ : List (List ℕ))
    (S : SemilinearCode) :
    checkIncludedBool d base₀ P₀ S = true ↔
      ∀ c : Fin P₀.length → ℕ,
        (0 ≤ fun i : Fin d =>
          base₀.getD i.1 0 + ∑ k : Fin P₀.length, (c k : ℤ) * ((P₀[k].getD i.1 0 : ℕ) : ℤ)) →
        ∃ bp ∈ S, ∃ c' : Fin bp.2.length → ℕ,
          ∀ i : Fin d,
            base₀.getD i.1 0 + ∑ k : Fin P₀.length, (c k : ℤ) * ((P₀[k].getD i.1 0 : ℕ) : ℤ) =
            (bp.1.getD i.1 0 : ℤ) +
              ∑ j : Fin bp.2.length, (c' j : ℤ) * ((bp.2[j].getD i.1 0 : ℕ) : ℤ) := by
  unfold checkIncludedBool
  rw [Bool.not_eq_true', Bool.eq_false_iff, ne_eq, evalDNF0_eq_true, evalDNF_elimMany]
  simp_rw [List.append_nil, evalDNF_andDNF, evalDNF_singleton, evalDNF_negDNF]
  simp only [not_exists, not_and, not_not]
  constructor
  · intro h c hw
    let cs : List ℤ := List.ofFn fun k => (c k : ℤ)
    have hguard : evalConj (guardConj d base₀ P₀) cs :=
      (evalConj_guardConj_iff d base₀ P₀ cs (by simp [cs])).mpr
        ⟨fun k => by simp [cs, List.getD_eq_getElem?_getD, k.2], c, rfl, hw⟩
    exact (evalDNF_memSDNF_iff d base₀ P₀ S c).mp (h cs (by simp [cs]) hguard)
  · intro h cs hlen hguard
    obtain ⟨-, c, rfl, hw⟩ := (evalConj_guardConj_iff d base₀ P₀ cs hlen).mp hguard
    exact (evalDNF_memSDNF_iff d base₀ P₀ S c).mpr (h c hw)

private lemma primrec_innerConj :
    Primrec (fun p : (ℕ × List ℤ × List (List ℕ)) × (List ℕ × List (List ℕ)) =>
      innerConj p.1.1 p.1.2.1 p.1.2.2 p.2) := by
  unfold innerConj
  let d := fun p : (ℕ × List ℤ × List (List ℕ)) × (List ℕ × List (List ℕ)) => p.1.1
  let base₀ := fun p : (ℕ × List ℤ × List (List ℕ)) × (List ℕ × List (List ℕ)) => p.1.2.1
  let P₀ := fun p : (ℕ × List ℤ × List (List ℕ)) × (List ℕ × List (List ℕ)) => p.1.2.2
  let bp := fun p : (ℕ × List ℤ × List (List ℕ)) × (List ℕ × List (List ℕ)) => p.2
  have hd : Primrec d := Primrec.fst.comp Primrec.fst
  have hbase : Primrec base₀ := Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hP₀ : Primrec P₀ := Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have hbp : Primrec bp := Primrec.snd
  have hpart1 : Primrec (fun p => (List.range (bp p).2.length).map fun j => (0, ((0 : ℤ), unitVec j))) :=
    Primrec.list_map (Primrec.list_range.comp (Primrec.list_length.comp (Primrec.snd.comp hbp)))
      ((Primrec.pair (Primrec.const 0)
        (Primrec.pair (Primrec.const (0 : ℤ)) (primrec_unitVec.comp Primrec.snd))).to₂)
  have hpart2 : Primrec (fun p => (List.range (d p)).flatMap fun i =>
      let diff : Lin :=
        ((base₀ p).getD i 0 - (((bp p).1.getD i 0 : ℕ) : ℤ),
          ((bp p).2.map fun q => -((q.getD i 0 : ℕ) : ℤ)) ++
          ((P₀ p).map fun q => ((q.getD i 0 : ℕ) : ℤ)))
      [(0, diff), (0, scaleLin (-1) diff)]) := by
    refine Primrec.list_flatMap (Primrec.list_range.comp hd) ?_
    change Primrec (fun q : ((ℕ × List ℤ × List (List ℕ)) × (List ℕ × List (List ℕ))) × ℕ =>
      let diff : Lin :=
        ((base₀ q.1).getD q.2 0 - (((bp q.1).1.getD q.2 0 : ℕ) : ℤ),
          ((bp q.1).2.map fun v => -((v.getD q.2 0 : ℕ) : ℤ)) ++
          ((P₀ q.1).map fun v => ((v.getD q.2 0 : ℕ) : ℤ)))
      [(0, diff), (0, scaleLin (-1) diff)])
    let c0 : ((ℕ × List ℤ × List (List ℕ)) × (List ℕ × List (List ℕ))) × ℕ → ℤ :=
      fun q => (base₀ q.1).getD q.2 0 - (((bp q.1).1.getD q.2 0 : ℕ) : ℤ)
    have hc0 : Primrec c0 :=
      primrec_int_sub.comp
        ((Primrec.list_getD (0 : ℤ)).comp (hbase.comp Primrec.fst) Primrec.snd)
        (primrec_int_ofNat.comp
          ((Primrec.list_getD (0 : ℕ)).comp (Primrec.fst.comp (hbp.comp Primrec.fst)) Primrec.snd))
    have hcs1 : Primrec (fun q : ((ℕ × List ℤ × List (List ℕ)) × (List ℕ × List (List ℕ))) × ℕ =>
        (bp q.1).2.map fun v => -((v.getD q.2 0 : ℕ) : ℤ)) :=
      Primrec.list_map (Primrec.snd.comp (hbp.comp Primrec.fst))
        ((primrec_int_neg.comp (primrec_int_ofNat.comp
          ((Primrec.list_getD (0 : ℕ)).comp Primrec.snd (Primrec.snd.comp Primrec.fst)))).to₂)
    have hcs2 : Primrec (fun q : ((ℕ × List ℤ × List (List ℕ)) × (List ℕ × List (List ℕ))) × ℕ =>
        (P₀ q.1).map fun v => ((v.getD q.2 0 : ℕ) : ℤ)) :=
      Primrec.list_map (hP₀.comp Primrec.fst)
        ((primrec_int_ofNat.comp
          ((Primrec.list_getD (0 : ℕ)).comp Primrec.snd (Primrec.snd.comp Primrec.fst))).to₂)
    have hdiff : Primrec (fun q : ((ℕ × List ℤ × List (List ℕ)) × (List ℕ × List (List ℕ))) × ℕ =>
        (c0 q, ((bp q.1).2.map fun v => -((v.getD q.2 0 : ℕ) : ℤ)) ++
          ((P₀ q.1).map fun v => ((v.getD q.2 0 : ℕ) : ℤ)))) :=
      Primrec.pair hc0 (Primrec.list_append.comp hcs1 hcs2)
    exact Primrec.list_cons.comp
      (Primrec.pair (Primrec.const 0) hdiff)
      (Primrec.list_cons.comp
        (Primrec.pair (Primrec.const 0) (primrec_scaleLin.comp (Primrec.const (-1 : ℤ)) hdiff))
        (Primrec.const ([] : Conj)))
  exact Primrec.list_append.comp hpart1 hpart2

private lemma primrec_guardConj :
    Primrec (fun p : ℕ × List ℤ × List (List ℕ) => guardConj p.1 p.2.1 p.2.2) := by
  unfold guardConj
  have hd : Primrec (fun p : ℕ × List ℤ × List (List ℕ) => p.1) := Primrec.fst
  have hbase : Primrec (fun p : ℕ × List ℤ × List (List ℕ) => p.2.1) := Primrec.fst.comp Primrec.snd
  have hP₀ : Primrec (fun p : ℕ × List ℤ × List (List ℕ) => p.2.2) := Primrec.snd.comp Primrec.snd
  have hpart1 : Primrec (fun p : ℕ × List ℤ × List (List ℕ) =>
      (List.range p.2.2.length).map fun k => (0, ((0 : ℤ), unitVec k))) :=
    Primrec.list_map (Primrec.list_range.comp (Primrec.list_length.comp hP₀))
      ((Primrec.pair (Primrec.const 0)
        (Primrec.pair (Primrec.const (0 : ℤ)) (primrec_unitVec.comp Primrec.snd))).to₂)
  have hpart2 : Primrec (fun p : ℕ × List ℤ × List (List ℕ) =>
      (List.range p.1).map fun i => (0, (p.2.1.getD i 0, p.2.2.map fun v => ((v.getD i 0 : ℕ) : ℤ)))) := by
    refine Primrec.list_map (Primrec.list_range.comp hd) ?_
    change Primrec (fun q : (ℕ × List ℤ × List (List ℕ)) × ℕ =>
      (0, (q.1.2.1.getD q.2 0, q.1.2.2.map fun v => ((v.getD q.2 0 : ℕ) : ℤ))))
    refine Primrec.pair (Primrec.const 0)
      (Primrec.pair
        ((Primrec.list_getD (0 : ℤ)).comp (hbase.comp Primrec.fst) Primrec.snd)
        (Primrec.list_map (hP₀.comp Primrec.fst)
          ((primrec_int_ofNat.comp
            ((Primrec.list_getD (0 : ℕ)).comp Primrec.snd (Primrec.snd.comp Primrec.fst))).to₂)))
  exact Primrec.list_append.comp hpart1 hpart2

private lemma primrec_memSDNF :
    Primrec (fun p : (ℕ × List ℤ × List (List ℕ)) × SemilinearCode =>
      memSDNF p.1.1 p.1.2.1 p.1.2.2 p.2) := by
  unfold memSDNF
  refine Primrec.list_flatMap Primrec.snd ?_
  change Primrec (fun q : ((ℕ × List ℤ × List (List ℕ)) × SemilinearCode) × (List ℕ × List (List ℕ)) =>
    elimMany q.2.2.length [innerConj q.1.1.1 q.1.1.2.1 q.1.1.2.2 q.2])
  have hbp : Primrec (fun q : ((ℕ × List ℤ × List (List ℕ)) × SemilinearCode) × (List ℕ × List (List ℕ)) =>
      q.2) := Primrec.snd
  have hinner : Primrec (fun q : ((ℕ × List ℤ × List (List ℕ)) × SemilinearCode) × (List ℕ × List (List ℕ)) =>
      [innerConj q.1.1.1 q.1.1.2.1 q.1.1.2.2 q.2]) :=
    Primrec.list_cons.comp
      (primrec_innerConj.comp (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd))
      (Primrec.const ([] : DNF))
  exact primrec_elimMany.comp (Primrec.list_length.comp (Primrec.snd.comp hbp)) hinner

private lemma primrec_checkIncludedBool :
    Primrec (fun p : (ℕ × List ℤ × List (List ℕ)) × SemilinearCode =>
      checkIncludedBool p.1.1 p.1.2.1 p.1.2.2 p.2) := by
  unfold checkIncludedBool
  have hguard : Primrec (fun p : (ℕ × List ℤ × List (List ℕ)) × SemilinearCode =>
      [guardConj p.1.1 p.1.2.1 p.1.2.2]) :=
    Primrec.list_cons.comp (primrec_guardConj.comp Primrec.fst) (Primrec.const ([] : DNF))
  have hneg : Primrec (fun p : (ℕ × List ℤ × List (List ℕ)) × SemilinearCode =>
      negDNF (memSDNF p.1.1 p.1.2.1 p.1.2.2 p.2)) :=
    primrec_negDNF.comp primrec_memSDNF
  have hand := primrec_andDNF.comp hguard hneg
  have helim := primrec_elimMany.comp
    (Primrec.list_length.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))) hand
  exact Primrec.not.comp (primrec_evalDNF0.comp helim)

/- ### Part 6: Top-level BVAS invariant checker and `OMA.solution` -/

private def natVecToInt (v : List ℕ) : List ℤ := v.map fun n : ℕ => (n : ℤ)

private def addVecInt (d : ℕ) (v w : List ℤ) : List ℤ :=
  (List.range d).map fun i => v.getD i 0 + w.getD i 0

private def nonnegList (l : List ℤ) : Bool := l.all fun z => decide (0 ≤ z)

private def checkInvRaw (raw : RawInput) (S : SemilinearCode) : Bool :=
  let d := raw.1
  let baseVecs := raw.2.1
  let unary := raw.2.2.1
  let binary := raw.2.2.2.1
  let t := raw.2.2.2.2
  let c1 := baseVecs.all fun v => checkIncludedBool d v [] S
  let c2 := S.all fun bp =>
    unary.all fun r => checkIncludedBool d (addVecInt d (natVecToInt bp.1) r) bp.2 S
  let c3 := S.all fun bp₁ =>
    S.all fun bp₂ =>
      binary.all fun r =>
        checkIncludedBool d (addVecInt d (addVecInt d (natVecToInt bp₁.1) (natVecToInt bp₂.1)) r)
          (bp₁.2 ++ bp₂.2) S
  let c4 := !(nonnegList t && checkIncludedBool d t [] S)
  c1 && c2 && c3 && c4

private lemma primrec_natVecToInt : Primrec natVecToInt := by
  unfold natVecToInt
  exact Primrec.list_map (Primrec.id (α := List ℕ)) (primrec_int_ofNat.comp₂ Primrec₂.right)

private lemma primrec_addVecInt :
    Primrec (fun t : ℕ × List ℤ × List ℤ => addVecInt t.1 t.2.1 t.2.2) := by
  unfold addVecInt
  refine Primrec.list_map (Primrec.list_range.comp Primrec.fst) ?_
  have h1 : Primrec₂ (fun (t : ℕ × List ℤ × List ℤ) (i : ℕ) => t.2.1.getD i 0) :=
    (Primrec.list_getD (0 : ℤ)).comp₂ (Primrec.fst.comp₂ (Primrec.snd.comp₂ Primrec₂.left))
      Primrec₂.right
  have h2 : Primrec₂ (fun (t : ℕ × List ℤ × List ℤ) (i : ℕ) => t.2.2.getD i 0) :=
    (Primrec.list_getD (0 : ℤ)).comp₂ (Primrec.snd.comp₂ (Primrec.snd.comp₂ Primrec₂.left))
      Primrec₂.right
  exact primrec_int_add.comp₂ h1 h2

private lemma primrec_nonnegList : Primrec nonnegList :=
  primrec_list_all (Primrec.id (α := List ℤ)) (primrec_int_nonneg.comp₂ Primrec₂.right)

private lemma primrec_checkUnaryBody :
    Primrec (fun q : (ℕ × List (List ℤ) × SemilinearCode) × (List ℕ × List (List ℕ)) =>
      q.1.2.1.all fun r =>
        checkIncludedBool q.1.1 (addVecInt q.1.1 (natVecToInt q.2.1) r) q.2.2 q.1.2.2) := by
  have h1 : Primrec (fun q : (ℕ × List (List ℤ) × SemilinearCode) × (List ℕ × List (List ℕ)) =>
      q.1.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have h2 : Primrec (fun q : ((ℕ × List (List ℤ) × SemilinearCode) ×
      (List ℕ × List (List ℕ))) × List ℤ =>
    checkIncludedBool q.1.1.1 (addVecInt q.1.1.1 (natVecToInt q.1.2.1) q.2) q.1.2.2 q.1.1.2.2) := by
    let Q := ((ℕ × List (List ℤ) × SemilinearCode) × (List ℕ × List (List ℕ))) × List ℤ
    have hctx : Primrec (fun q : Q => q.1.1) := Primrec.fst.comp Primrec.fst
    have hbp : Primrec (fun q : Q => q.1.2) := Primrec.snd.comp Primrec.fst
    have hr : Primrec (fun q : Q => q.2) := Primrec.snd
    have hd' : Primrec (fun q : Q => q.1.1.1) := Primrec.fst.comp hctx
    have hS' : Primrec (fun q : Q => q.1.1.2.2) := Primrec.snd.comp (Primrec.snd.comp hctx)
    have hbp1 : Primrec (fun q : Q => q.1.2.1) := Primrec.fst.comp hbp
    have hbp2 : Primrec (fun q : Q => q.1.2.2) := Primrec.snd.comp hbp
    have hbase' : Primrec (fun q : Q => addVecInt q.1.1.1 (natVecToInt q.1.2.1) q.2) :=
      (primrec_addVecInt.comp
        (Primrec.pair hd' (Primrec.pair (primrec_natVecToInt.comp hbp1) hr))).of_eq fun _ => rfl
    exact (primrec_checkIncludedBool.comp
      (Primrec.pair (Primrec.pair hd' (Primrec.pair hbase' hbp2)) hS')).of_eq fun _ => rfl
  exact primrec_list_all h1 h2.to₂

private lemma primrec_checkBinaryBody :
    Primrec (fun q : ((ℕ × List (List ℤ) × SemilinearCode) ×
      (List ℕ × List (List ℕ))) × (List ℕ × List (List ℕ)) =>
      q.1.1.2.1.all fun r =>
        checkIncludedBool q.1.1.1
          (addVecInt q.1.1.1 (addVecInt q.1.1.1 (natVecToInt q.1.2.1) (natVecToInt q.2.1)) r)
          (q.1.2.2 ++ q.2.2) q.1.1.2.2) := by
  have h1 : Primrec (fun q : ((ℕ × List (List ℤ) × SemilinearCode) ×
      (List ℕ × List (List ℕ))) × (List ℕ × List (List ℕ)) => q.1.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
  have h2 : Primrec (fun q : (((ℕ × List (List ℤ) × SemilinearCode) ×
      (List ℕ × List (List ℕ))) × (List ℕ × List (List ℕ))) × List ℤ =>
    checkIncludedBool q.1.1.1.1
      (addVecInt q.1.1.1.1 (addVecInt q.1.1.1.1 (natVecToInt q.1.1.2.1) (natVecToInt q.1.2.1)) q.2)
      (q.1.1.2.2 ++ q.1.2.2) q.1.1.1.2.2) := by
    let Q := (((ℕ × List (List ℤ) × SemilinearCode) ×
      (List ℕ × List (List ℕ))) × (List ℕ × List (List ℕ))) × List ℤ
    have hctx : Primrec (fun q : Q => q.1.1.1) := Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
    have hbp1 : Primrec (fun q : Q => q.1.1.2) := Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
    have hbp2 : Primrec (fun q : Q => q.1.2) := Primrec.snd.comp Primrec.fst
    have hr : Primrec (fun q : Q => q.2) := Primrec.snd
    have hd' : Primrec (fun q : Q => q.1.1.1.1) := Primrec.fst.comp hctx
    have hS' : Primrec (fun q : Q => q.1.1.1.2.2) := Primrec.snd.comp (Primrec.snd.comp hctx)
    have hsum12 : Primrec (fun q : Q => addVecInt q.1.1.1.1 (natVecToInt q.1.1.2.1) (natVecToInt q.1.2.1)) :=
      (primrec_addVecInt.comp
        (Primrec.pair hd'
          (Primrec.pair (primrec_natVecToInt.comp (Primrec.fst.comp hbp1))
            (primrec_natVecToInt.comp (Primrec.fst.comp hbp2))))).of_eq fun _ => rfl
    have hbase' : Primrec (fun q : Q =>
        addVecInt q.1.1.1.1 (addVecInt q.1.1.1.1 (natVecToInt q.1.1.2.1) (natVecToInt q.1.2.1)) q.2) :=
      (primrec_addVecInt.comp (Primrec.pair hd' (Primrec.pair hsum12 hr))).of_eq fun _ => rfl
    have hP' : Primrec (fun q : Q => q.1.1.2.2 ++ q.1.2.2) :=
      (Primrec.list_append.comp (Primrec.snd.comp hbp1) (Primrec.snd.comp hbp2)).of_eq fun _ => rfl
    exact (primrec_checkIncludedBool.comp
      (Primrec.pair (Primrec.pair hd' (Primrec.pair hbase' hP')) hS')).of_eq fun _ => rfl
  exact primrec_list_all h1 h2.to₂

private lemma primrec_checkInv_c1 :
    Primrec (fun p : RawInput × SemilinearCode =>
      p.1.2.1.all fun v => checkIncludedBool p.1.1 v [] p.2) :=
  primrec_list_all (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
    ((primrec_checkIncludedBool.comp
      (Primrec.pair
        (Primrec.pair (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
          (Primrec.pair Primrec.snd (Primrec.const ([] : List (List ℕ)))))
        (Primrec.snd.comp Primrec.fst))).to₂)

private lemma primrec_checkInv_c2 :
    Primrec (fun p : RawInput × SemilinearCode =>
      p.2.all fun bp =>
        p.1.2.2.1.all fun r => checkIncludedBool p.1.1 (addVecInt p.1.1 (natVecToInt bp.1) r) bp.2 p.2) := by
  have hctxU : Primrec (fun p : RawInput × SemilinearCode => (p.1.1, p.1.2.2.1, p.2)) :=
    Primrec.pair (Primrec.fst.comp Primrec.fst)
      (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))) Primrec.snd)
  have h2 : Primrec (fun q : (RawInput × SemilinearCode) × (List ℕ × List (List ℕ)) =>
      q.1.1.2.2.1.all fun r =>
        checkIncludedBool q.1.1.1 (addVecInt q.1.1.1 (natVecToInt q.2.1) r) q.2.2 q.1.2) :=
    (primrec_checkUnaryBody.comp (Primrec.pair (hctxU.comp Primrec.fst) Primrec.snd)).of_eq fun _ => rfl
  exact primrec_list_all Primrec.snd h2.to₂

private lemma primrec_checkInv_c3 :
    Primrec (fun p : RawInput × SemilinearCode =>
      p.2.all fun bp₁ =>
        p.2.all fun bp₂ =>
          p.1.2.2.2.1.all fun r =>
            checkIncludedBool p.1.1
              (addVecInt p.1.1 (addVecInt p.1.1 (natVecToInt bp₁.1) (natVecToInt bp₂.1)) r)
              (bp₁.2 ++ bp₂.2) p.2) := by
  have hctxB : Primrec (fun p : RawInput × SemilinearCode => (p.1.1, p.1.2.2.2.1, p.2)) :=
    Primrec.pair (Primrec.fst.comp Primrec.fst)
      (Primrec.pair
        (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))))
        Primrec.snd)
  have h3 : Primrec (fun q : ((RawInput × SemilinearCode) × (List ℕ × List (List ℕ))) ×
      (List ℕ × List (List ℕ)) =>
      q.1.1.1.2.2.2.1.all fun r =>
        checkIncludedBool q.1.1.1.1
          (addVecInt q.1.1.1.1 (addVecInt q.1.1.1.1 (natVecToInt q.1.2.1) (natVecToInt q.2.1)) r)
          (q.1.2.2 ++ q.2.2) q.1.1.2) :=
    (primrec_checkBinaryBody.comp
      (Primrec.pair
        (Primrec.pair (hctxB.comp (Primrec.fst.comp Primrec.fst)) (Primrec.snd.comp Primrec.fst))
        Primrec.snd)).of_eq fun _ => rfl
  have h2 : Primrec (fun q : (RawInput × SemilinearCode) × (List ℕ × List (List ℕ)) =>
      q.1.2.all fun bp₂ =>
        q.1.1.2.2.2.1.all fun r =>
          checkIncludedBool q.1.1.1
            (addVecInt q.1.1.1 (addVecInt q.1.1.1 (natVecToInt q.2.1) (natVecToInt bp₂.1)) r)
            (q.2.2 ++ bp₂.2) q.1.2) :=
    primrec_list_all (Primrec.snd.comp Primrec.fst) h3.to₂
  exact primrec_list_all Primrec.snd h2.to₂

private lemma primrec_checkInv_c4 :
    Primrec (fun p : RawInput × SemilinearCode =>
      !(nonnegList p.1.2.2.2.2 && checkIncludedBool p.1.1 p.1.2.2.2.2 [] p.2)) := by
  have hd : Primrec (fun p : RawInput × SemilinearCode => p.1.1) := Primrec.fst.comp Primrec.fst
  have ht : Primrec (fun p : RawInput × SemilinearCode => p.1.2.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
  exact Primrec.not.comp
    (Primrec.and.comp (primrec_nonnegList.comp ht)
      (primrec_checkIncludedBool.comp
        (Primrec.pair (Primrec.pair hd (Primrec.pair ht (Primrec.const ([] : List (List ℕ)))))
          Primrec.snd)))

private lemma primrec_checkInvRaw : Primrec₂ checkInvRaw := by
  change Primrec (fun p : RawInput × SemilinearCode => checkInvRaw p.1 p.2)
  unfold checkInvRaw
  exact Primrec.and.comp
    (Primrec.and.comp (Primrec.and.comp primrec_checkInv_c1 primrec_checkInv_c2) primrec_checkInv_c3)
    primrec_checkInv_c4

private def encodeInput (p : Input) : RawInput :=
  (p.1, p.2.1.1.map List.ofFn, p.2.1.unaryRules.map List.ofFn,
    p.2.1.binaryRules.map List.ofFn, List.ofFn p.2.2)

private lemma primrec_encodeInput : Primrec encodeInput :=
  Primrec.encode_iff.mp Primrec.encode

private lemma nonnegList_ofFn_iff {d : ℕ} (v : Fin d → ℤ) :
    nonnegList (List.ofFn v) = true ↔ 0 ≤ v := by
  simp only [nonnegList, List.all_eq_true, List.mem_ofFn, decide_eq_true_eq]
  constructor
  · intro h i; exact h (v i) ⟨i, rfl⟩
  · rintro h z ⟨i, rfl⟩; exact h i

private lemma addVecInt_getD {d : ℕ} (v w : List ℤ) (i : Fin d) :
    (addVecInt d v w).getD i.1 0 = v.getD i.1 0 + w.getD i.1 0 := by
  simp [addVecInt, List.getD_eq_getElem?_getD, i.2]

private lemma natVecToInt_getD (v : List ℕ) (i : ℕ) :
    (natVecToInt v).getD i 0 = (v.getD i 0 : ℤ) := by
  rw [natVecToInt, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases v[i]? <;> rfl

private lemma ofFn_getD {d : ℕ} (v : Fin d → ℤ) (i : Fin d) :
    (List.ofFn v).getD i.1 0 = v i := by
  simp [List.getD_eq_getElem?_getD, i.2]

private lemma checkInvRaw_eq_true_iff (x : Input × SemilinearCode) :
    checkInvRaw (encodeInput x.1) x.2 = true ↔
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
  dsimp only [checkInvRaw, encodeInput]
  let mem : (Fin d → ℤ) → Prop := fun v =>
    ∃ bp ∈ S, ∃ c : Fin bp.2.length → ℕ,
      ∀ i : Fin d, v i = (bp.1.getD i.1 0 : ℤ) +
        ∑ j : Fin bp.2.length, (c j : ℤ) * (((bp.2[j]).getD i.1 0 : ℕ) : ℤ)
  have hnil : ∀ v : Fin d → ℤ,
      checkIncludedBool d (List.ofFn v) [] S = true ↔ (0 ≤ v → mem v) := by
    intro v
    rw [checkIncludedBool_eq_true_iff]
    have hv_eq : ∀ (c : Fin ([] : List (List ℕ)).length → ℕ) (i : Fin d),
        (List.ofFn v).getD i.1 0 +
          ∑ k : Fin ([] : List (List ℕ)).length, (c k : ℤ) * ((([] : List (List ℕ))[k].getD i.1 0 : ℕ) : ℤ) =
        v i := fun _ i => by simp
    constructor
    · intro h hv
      have h0 := h (fun k => Fin.elim0 k) fun i => by dsimp only; rw [hv_eq]; exact hv i
      rcases h0 with ⟨bp, hbp, c', hc'⟩
      exact ⟨bp, hbp, c', fun i => by rw [← hv_eq (fun k => Fin.elim0 k) i]; exact hc' i⟩
    · intro h c hw
      have hv : 0 ≤ v := fun i => by rw [← hv_eq c i]; exact hw i
      rcases h hv with ⟨bp, hbp, c', hc'⟩
      exact ⟨bp, hbp, c', fun i => by rw [hv_eq]; exact hc' i⟩
  have h1 : ((b.1.map List.ofFn).all fun v => checkIncludedBool d v [] S) = true ↔
      (∀ v ∈ b.1, 0 ≤ v → mem v) := by
    simp only [List.all_eq_true, List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
      hnil]
  have h2 : (S.all fun bp => (b.unaryRules.map List.ofFn).all fun r =>
        checkIncludedBool d (addVecInt d (natVecToInt bp.1) r) bp.2 S) = true ↔
      (∀ v r, mem v → r ∈ b.unaryRules → 0 ≤ v + r → mem (v + r)) := by
    simp only [List.all_eq_true, List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
      checkIncludedBool_eq_true_iff]
    constructor
    · intro h v r ⟨bp, hbp, c, hv⟩ hr hvr
      have hw_i : ∀ i : Fin d,
          (addVecInt d (natVecToInt bp.1) (List.ofFn r)).getD i.1 0 +
            ∑ k : Fin bp.2.length, (c k : ℤ) * ((bp.2[k].getD i.1 0 : ℕ) : ℤ) = (v + r) i := by
        intro i
        rw [addVecInt_getD, natVecToInt_getD, ofFn_getD, Pi.add_apply, hv i]
        ring
      have hres := h bp hbp r hr c fun i => by dsimp only; rw [hw_i i]; exact hvr i
      rcases hres with ⟨bp', hbp', c', hc'⟩
      exact ⟨bp', hbp', c', fun i => by rw [← hw_i i]; exact hc' i⟩
    · intro h bp hbp r hr c hw
      let v : Fin d → ℤ := fun i =>
        (bp.1.getD i.1 0 : ℤ) + ∑ k : Fin bp.2.length, (c k : ℤ) * ((bp.2[k].getD i.1 0 : ℕ) : ℤ)
      have hw_i : ∀ i : Fin d,
          (addVecInt d (natVecToInt bp.1) (List.ofFn r)).getD i.1 0 +
            ∑ k : Fin bp.2.length, (c k : ℤ) * ((bp.2[k].getD i.1 0 : ℕ) : ℤ) = (v + r) i := by
        intro i
        rw [addVecInt_getD, natVecToInt_getD, ofFn_getD, Pi.add_apply]
        dsimp only [v]; ring
      have hres := h v r ⟨bp, hbp, c, fun _ => rfl⟩ hr fun i => by rw [← hw_i i]; exact hw i
      rcases hres with ⟨bp', hbp', c', hc'⟩
      exact ⟨bp', hbp', c', fun i => by rw [hw_i i]; exact hc' i⟩
  have h3 : (S.all fun bp₁ => S.all fun bp₂ => (b.binaryRules.map List.ofFn).all fun r =>
        checkIncludedBool d (addVecInt d (addVecInt d (natVecToInt bp₁.1) (natVecToInt bp₂.1)) r)
          (bp₁.2 ++ bp₂.2) S) = true ↔
      (∀ v₁ v₂ r, mem v₁ → mem v₂ → r ∈ b.binaryRules → 0 ≤ v₁ + v₂ + r → mem (v₁ + v₂ + r)) := by
    simp only [List.all_eq_true, List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
      checkIncludedBool_eq_true_iff]
    have hsplit_sum : ∀ (P₁ P₂ : List (List ℕ)) (c : Fin (P₁ ++ P₂).length → ℕ) (i : Fin d),
        ∑ k : Fin (P₁ ++ P₂).length, (c k : ℤ) * (((P₁ ++ P₂)[k].getD i.1 0 : ℕ) : ℤ) =
          (∑ k₁ : Fin P₁.length,
            (c ⟨k₁.1, by rw [List.length_append]; omega⟩ : ℤ) * ((P₁[k₁].getD i.1 0 : ℕ) : ℤ)) +
          (∑ k₂ : Fin P₂.length,
            (c ⟨P₁.length + k₂.1, by rw [List.length_append]; omega⟩ : ℤ) * ((P₂[k₂].getD i.1 0 : ℕ) : ℤ)) := by
      intro P₁ P₂ c i
      let e : Fin P₁.length ⊕ Fin P₂.length ≃ Fin (P₁ ++ P₂).length :=
        finSumFinEquiv.trans (finCongr (List.length_append.symm))
      rw [← Equiv.sum_comp e, Fintype.sum_sum_type]
      congr 1
      · refine Finset.sum_congr rfl fun k₁ _ => ?_
        have hidx : (e (Sum.inl k₁)).1 = k₁.1 := by simp [e, finSumFinEquiv]
        have hget : (P₁ ++ P₂)[e (Sum.inl k₁)] = P₁[k₁] := by
          simp [List.getElem_append_left, hidx]
        have hfin : e (Sum.inl k₁) = ⟨k₁.1, by rw [List.length_append]; omega⟩ := Fin.ext hidx
        rw [hget, hfin]
      · refine Finset.sum_congr rfl fun k₂ _ => ?_
        have hidx : (e (Sum.inr k₂)).1 = P₁.length + k₂.1 := by simp [e, finSumFinEquiv]
        have hget : (P₁ ++ P₂)[e (Sum.inr k₂)] = P₂[k₂] := by
          simp [List.getElem_append_right, hidx]
        have hfin : e (Sum.inr k₂) = ⟨P₁.length + k₂.1, by rw [List.length_append]; omega⟩ := Fin.ext hidx
        rw [hget, hfin]
    constructor
    · intro h v₁ v₂ r ⟨bp₁, hbp₁, c₁, hv₁⟩ ⟨bp₂, hbp₂, c₂, hv₂⟩ hr hv12r
      let c : Fin (bp₁.2 ++ bp₂.2).length → ℕ := fun k =>
        if hk : k.1 < bp₁.2.length then c₁ ⟨k.1, hk⟩
        else c₂ ⟨k.1 - bp₁.2.length, by
          have hlen : (bp₁.2 ++ bp₂.2).length = bp₁.2.length + bp₂.2.length := List.length_append
          have hk2 : k.1 < (bp₁.2 ++ bp₂.2).length := k.2
          omega⟩
      have hw_i : ∀ i : Fin d,
          (addVecInt d (addVecInt d (natVecToInt bp₁.1) (natVecToInt bp₂.1)) (List.ofFn r)).getD i.1 0 +
            ∑ k : Fin (bp₁.2 ++ bp₂.2).length, (c k : ℤ) * (((bp₁.2 ++ bp₂.2)[k].getD i.1 0 : ℕ) : ℤ) =
          (v₁ + v₂ + r) i := by
        intro i
        rw [addVecInt_getD, addVecInt_getD, natVecToInt_getD, natVecToInt_getD, ofFn_getD,
          hsplit_sum, Pi.add_apply, Pi.add_apply, hv₁ i, hv₂ i]
        have hc1 : ∀ k₁ : Fin bp₁.2.length,
            c ⟨k₁.1, by rw [List.length_append]; omega⟩ = c₁ k₁ := fun k₁ => by
          simp [c, k₁.2]
        have hc2 : ∀ k₂ : Fin bp₂.2.length,
            c ⟨bp₁.2.length + k₂.1, by rw [List.length_append]; omega⟩ = c₂ k₂ := fun k₂ => by
          simp [c]
        simp_rw [hc1, hc2]
        ring
      have hres := h bp₁ hbp₁ bp₂ hbp₂ r hr c fun i => by dsimp only; rw [hw_i i]; exact hv12r i
      rcases hres with ⟨bp', hbp', c', hc'⟩
      exact ⟨bp', hbp', c', fun i => by rw [← hw_i i]; exact hc' i⟩
    · intro h bp₁ hbp₁ bp₂ hbp₂ r hr c hw
      let c₁ : Fin bp₁.2.length → ℕ := fun k₁ => c ⟨k₁.1, by rw [List.length_append]; omega⟩
      let c₂ : Fin bp₂.2.length → ℕ := fun k₂ => c ⟨bp₁.2.length + k₂.1, by rw [List.length_append]; omega⟩
      let v₁ : Fin d → ℤ := fun i =>
        (bp₁.1.getD i.1 0 : ℤ) + ∑ k₁ : Fin bp₁.2.length, (c₁ k₁ : ℤ) * ((bp₁.2[k₁].getD i.1 0 : ℕ) : ℤ)
      let v₂ : Fin d → ℤ := fun i =>
        (bp₂.1.getD i.1 0 : ℤ) + ∑ k₂ : Fin bp₂.2.length, (c₂ k₂ : ℤ) * ((bp₂.2[k₂].getD i.1 0 : ℕ) : ℤ)
      have hw_i : ∀ i : Fin d,
          (addVecInt d (addVecInt d (natVecToInt bp₁.1) (natVecToInt bp₂.1)) (List.ofFn r)).getD i.1 0 +
            ∑ k : Fin (bp₁.2 ++ bp₂.2).length, (c k : ℤ) * (((bp₁.2 ++ bp₂.2)[k].getD i.1 0 : ℕ) : ℤ) =
          (v₁ + v₂ + r) i := by
        intro i
        rw [addVecInt_getD, addVecInt_getD, natVecToInt_getD, natVecToInt_getD, ofFn_getD,
          hsplit_sum, Pi.add_apply, Pi.add_apply]
        dsimp only [v₁, v₂, c₁, c₂]; ring
      have hres := h v₁ v₂ r ⟨bp₁, hbp₁, c₁, fun _ => rfl⟩ ⟨bp₂, hbp₂, c₂, fun _ => rfl⟩ hr
        fun i => by rw [← hw_i i]; exact hw i
      rcases hres with ⟨bp', hbp', c', hc'⟩
      exact ⟨bp', hbp', c', fun i => by rw [hw_i i]; exact hc' i⟩
  have h4 : (!(nonnegList (List.ofFn t) && checkIncludedBool d (List.ofFn t) [] S)) = true ↔
      ¬ mem t := by
    rw [Bool.not_eq_true', Bool.and_eq_false_iff, Bool.eq_false_iff, Bool.eq_false_iff,
      ne_eq, ne_eq, nonnegList_ofFn_iff, hnil]
    have hmem_nn : mem t → 0 ≤ t := by
      rintro ⟨bp, _, c, ht⟩ i
      rw [ht i]
      refine add_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg fun j _ => ?_)
      exact mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    by_cases h0 : 0 ≤ t
    · simp [h0]
    · simp only [h0, not_false_eq_true, true_or, true_iff]
      exact fun hm => h0 (hmem_nn hm)
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, h1, h2, h3, h4, and_assoc, and_assoc]

end BranchingVASR1H1

theorem OMA.solution : OMA.R_BranchingVAS_reachability_decidable_R1.H1 := by
  let f : ((Σ d : ℕ, BranchingVAS.Bvas d × (Fin d → ℤ)) × List (List ℕ × List (List ℕ))) → Bool :=
    fun x => BranchingVASR1H1.checkInvRaw (BranchingVASR1H1.encodeInput x.1) x.2
  have hf : Primrec f :=
    BranchingVASR1H1.primrec_checkInvRaw.comp
      (BranchingVASR1H1.primrec_encodeInput.comp Primrec.fst) Primrec.snd
  refine ComputablePred.computable_iff.mpr ⟨f, hf.to_comp, funext fun x => propext ?_⟩
  simpa only [Bool.coe_true, f] using (BranchingVASR1H1.checkInvRaw_eq_true_iff x).symm
