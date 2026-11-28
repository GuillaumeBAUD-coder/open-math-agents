import OMAStatements.S_oeis_a085588
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace A085588Proof

open OMA.S_oeis_a085588 Polynomial

lemma xor_two_mul_add (x y r1 r2 : ℕ) (h1 : r1 < 2) (h2 : r2 < 2) :
    (2 * x + r1) ^^^ (2 * y + r2) = 2 * (x ^^^ y) + (r1 ^^^ r2) := by
  have hr12 : r1 ^^^ r2 < 2 := by
    rcases (by omega : r1 = 0 ∨ r1 = 1) with rfl | rfl <;>
      rcases (by omega : r2 = 0 ∨ r2 = 1) with rfl | rfl <;> decide
  apply Nat.eq_of_testBit_eq
  intro i
  cases i with
  | zero =>
    rw [Nat.testBit_xor, Nat.testBit_zero, Nat.testBit_zero, Nat.testBit_zero]
    have p1 : (2 * x + r1) % 2 = r1 := by omega
    have p2 : (2 * y + r2) % 2 = r2 := by omega
    have p3 : (2 * (x ^^^ y) + (r1 ^^^ r2)) % 2 = r1 ^^^ r2 := by omega
    rw [p1, p2, p3]
    rcases (by omega : r1 = 0 ∨ r1 = 1) with rfl | rfl <;>
      rcases (by omega : r2 = 0 ∨ r2 = 1) with rfl | rfl <;> decide
  | succ i =>
    rw [Nat.testBit_xor, Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_succ]
    have d1 : (2 * x + r1) / 2 = x := by omega
    have d2 : (2 * y + r2) / 2 = y := by omega
    have d3 : (2 * (x ^^^ y) + (r1 ^^^ r2)) / 2 = x ^^^ y := by omega
    rw [d1, d2, d3, Nat.testBit_xor]

lemma xor_two_mul (x y : ℕ) : (2 * x) ^^^ (2 * y) = 2 * (x ^^^ y) := by
  simpa using xor_two_mul_add x y 0 0 (by omega) (by omega)

lemma xor_eight_mul_add (x y r1 r2 : ℕ) (h1 : r1 < 8) (h2 : r2 < 8) :
    (8 * x + r1) ^^^ (8 * y + r2) = 8 * (x ^^^ y) + (r1 ^^^ r2) := by
  have hsplit : ∀ z r : ℕ, r < 8 →
      8 * z + r = 2 * (2 * (2 * z + r / 4) + (r / 2) % 2) + r % 2 := by
    intro z r hr
    omega
  have hr_lt : r1 ^^^ r2 < 8 := by
    have hb : ∀ i ≥ 3, (r1 ^^^ r2).testBit i = false := by
      intro i hi
      obtain ⟨j, rfl⟩ : ∃ j, i = j + 3 := ⟨i - 3, by omega⟩
      rw [Nat.testBit_xor, Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_succ,
        Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_succ]
      have z1 : r1 / 2 / 2 / 2 = 0 := by omega
      have z2 : r2 / 2 / 2 / 2 = 0 := by omega
      simp [z1, z2]
    by_contra hge
    push Not at hge
    set m := r1 ^^^ r2
    have hlog : 3 ≤ Nat.log2 m := by
      rw [Nat.le_log2 (by omega)]
      exact hge
    have htb : m.testBit (Nat.log2 m) = true := Nat.testBit_log2 (by omega)
    rw [hb (Nat.log2 m) hlog] at htb
    contradiction
  rw [hsplit x r1 h1, hsplit y r2 h2,
    xor_two_mul_add _ _ _ _ (by omega) (by omega),
    xor_two_mul_add _ _ _ _ (by omega) (by omega),
    xor_two_mul_add _ _ _ _ (by omega) (by omega)]
  have h_r : 2 * (2 * ((r1 / 4) ^^^ (r2 / 4)) + (((r1 / 2) % 2) ^^^ ((r2 / 2) % 2))) +
      ((r1 % 2) ^^^ (r2 % 2)) = r1 ^^^ r2 := by
    have e1 := xor_two_mul_add (r1 / 4) (r2 / 4) ((r1 / 2) % 2) ((r2 / 2) % 2) (by omega) (by omega)
    have e2 := xor_two_mul_add (2 * (r1 / 4) + (r1 / 2) % 2) (2 * (r2 / 4) + (r2 / 2) % 2)
      (r1 % 2) (r2 % 2) (by omega) (by omega)
    have r1_eq : 2 * (2 * (r1 / 4) + (r1 / 2) % 2) + r1 % 2 = r1 := by omega
    have r2_eq : 2 * (2 * (r2 / 4) + (r2 / 2) % 2) + r2 % 2 = r2 := by omega
    rw [r1_eq, r2_eq] at e2
    omega
  omega

def Bseq : ℕ → ℕ
  | 0 => 6
  | d + 1 => 2 * Bseq d + 1

lemma seven_mul_mersenne (d : ℕ) : 7 * (2 ^ (d + 3) - 1) = 8 * Bseq d + 1 := by
  induction d with
  | zero => decide
  | succ d ih =>
    unfold Bseq
    have hp : 2 ^ (d + 1 + 3) - 1 = 2 * (2 ^ (d + 3) - 1) + 1 := by
      have h1 : 2 ^ (d + 1 + 3) = 2 * 2 ^ (d + 3) := by ring
      have h2 : 1 ≤ 2 ^ (d + 3) := Nat.one_le_pow _ _ (by decide)
      omega
    omega

def Cseq (d : ℕ) : ℕ :=
  (2 ^ d - 1) ^^^ (2 * (2 ^ d - 1) + 1) ^^^ (8 * (2 ^ d - 1) + 7)

lemma Cseq_eq_Bseq (d : ℕ) : Cseq d = Bseq d := by
  induction d with
  | zero => decide
  | succ d ih =>
    unfold Cseq Bseq
    have h0 : 1 ≤ 2 ^ d := Nat.one_le_pow d 2 (by decide)
    have hpow : 2 ^ (d + 1) - 1 = 2 * (2 ^ d - 1) + 1 := by
      have : 2 ^ (d + 1) = 2 * 2 ^ d := by ring
      omega
    have hmul2 : 2 * (2 ^ (d + 1) - 1) + 1 = 2 * (2 * (2 ^ d - 1) + 1) + 1 := by omega
    have hmul8 : 8 * (2 ^ (d + 1) - 1) + 7 = 2 * (8 * (2 ^ d - 1) + 7) + 1 := by omega
    rw [hmul8, hmul2, hpow,
      xor_two_mul_add _ _ 1 1 (by omega) (by omega),
      xor_two_mul_add _ _ (1 ^^^ 1) 1 (by decide) (by omega)]
    have hc : (1 ^^^ 1) ^^^ 1 = 1 := by decide
    rw [hc]
    unfold Cseq at ih
    rw [ih]

lemma inA115770_mersenne {k : ℕ} (hk : 3 ≤ k) : InA115770 (2 ^ k - 1) := by
  obtain ⟨d, rfl⟩ : ∃ d, k = d + 3 := ⟨k - 3, by omega⟩
  unfold InA115770
  have h1 : 1 ≤ 2 ^ d := Nat.one_le_pow d 2 (by decide)
  have hm1 : 2 ^ (d + 3) - 1 = 8 * (2 ^ d - 1) + 7 := by
    have : 2 ^ (d + 3) = 8 * 2 ^ d := by ring
    omega
  have hm2 : 2 * (2 ^ (d + 3) - 1) = 8 * (2 * (2 ^ d - 1) + 1) + 6 := by omega
  have hm8 : 8 * (2 ^ (d + 3) - 1) = 8 * (8 * (2 ^ d - 1) + 7) + 0 := by omega
  rw [seven_mul_mersenne d]
  conv_rhs => rw [hm8, hm2, hm1]
  rw [xor_eight_mul_add _ _ 7 6 (by omega) (by omega),
    xor_eight_mul_add _ _ (7 ^^^ 6) 0 (by decide) (by omega)]
  have hc : (7 ^^^ 6) ^^^ 0 = 1 := by decide
  rw [hc, ← Cseq, Cseq_eq_Bseq]

lemma inA115770_two_pow_mul {m : ℕ} (hm : InA115770 m) (v : ℕ) : InA115770 (2 ^ v * m) := by
  induction v with
  | zero => simpa using hm
  | succ v ih =>
    unfold InA115770 at ih ⊢
    have hmul : 2 ^ (v + 1) * m = 2 * (2 ^ v * m) := by ring
    rw [hmul]
    set x := 2 ^ v * m
    have h8 : 8 * (2 * x) = 2 * (8 * x) := by ring
    rw [h8, xor_two_mul x (2 * x), xor_two_mul (x ^^^ (2 * x)) (8 * x)]
    omega

def bitBool {n : ℕ} (w : BitVec n) (z : ℤ) : Bool :=
  w.getLsbD (z % (n : ℤ)).toNat

def bitInt {n : ℕ} (w : BitVec n) (z : ℤ) : ℤ :=
  if bitBool w z then 1 else 0

lemma rotateLeft_one_bitBool {n : ℕ} (hn : 2 ≤ n) (w : BitVec n) (z : ℤ) :
    bitBool (w.rotateLeft 1) z = bitBool w (z - 1) := by
  unfold bitBool
  rw [BitVec.getLsbD_rotateLeft]
  have h1n : 1 % n = 1 := Nat.mod_eq_of_lt (by omega)
  rw [h1n]
  set r := z % (n : ℤ)
  have hr0 : 0 ≤ r := Int.emod_nonneg z (by omega)
  have hrlt : r < (n : ℤ) := Int.emod_lt_of_pos z (by omega)
  set i := r.toNat
  have hi_eq : (i : ℤ) = r := Int.toNat_of_nonneg hr0
  have hi_lt : i < n := by omega
  by_cases hi0 : i = 0
  · have hr_zero : r = 0 := by omega
    have hzm1 : (z - 1) % (n : ℤ) = (n : ℤ) - 1 := by
      have hz_eq : z = (n : ℤ) * (z / (n : ℤ)) := by
        have h := Int.emod_add_mul_ediv z (n : ℤ)
        change r + (n : ℤ) * (z / (n : ℤ)) = z at h
        linarith
      have hrew : z - 1 = ((n : ℤ) - 1) + (n : ℤ) * (z / (n : ℤ) - 1) := by
        linear_combination hz_eq
      rw [hrew, Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by omega) (by omega)]
    have hto : ((z - 1) % (n : ℤ)).toNat = n - 1 := by
      rw [hzm1]
      omega
    simp [hi0, hto]
  · have hi1 : ¬ (i < 1) := by omega
    have hzm1 : (z - 1) % (n : ℤ) = r - 1 := by
      have hz_eq : z - 1 = (r - 1) + (n : ℤ) * (z / (n : ℤ)) := by
        have h := Int.emod_add_mul_ediv z (n : ℤ)
        change r + (n : ℤ) * (z / (n : ℤ)) = z at h
        linarith
      rw [hz_eq, Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by omega) (by omega)]
    have hto : ((z - 1) % (n : ℤ)).toNat = i - 1 := by
      rw [hzm1]
      omega
    simp [hi1, hi_lt, hto]

lemma rotateRight_one_bitBool {n : ℕ} (hn : 2 ≤ n) (w : BitVec n) (z : ℤ) :
    bitBool (w.rotateRight 1) z = bitBool w (z + 1) := by
  unfold bitBool
  rw [BitVec.getLsbD_rotateRight]
  have h1n : 1 % n = 1 := Nat.mod_eq_of_lt (by omega)
  rw [h1n]
  set r := z % (n : ℤ)
  have hr0 : 0 ≤ r := Int.emod_nonneg z (by omega)
  have hrlt : r < (n : ℤ) := Int.emod_lt_of_pos z (by omega)
  set i := r.toNat
  have hi_eq : (i : ℤ) = r := Int.toNat_of_nonneg hr0
  have hi_lt : i < n := by omega
  by_cases hin : i < n - 1
  · have hzp1 : (z + 1) % (n : ℤ) = r + 1 := by
      have hz_eq : z + 1 = (r + 1) + (n : ℤ) * (z / (n : ℤ)) := by
        have h := Int.emod_add_mul_ediv z (n : ℤ)
        change r + (n : ℤ) * (z / (n : ℤ)) = z at h
        linarith
      rw [hz_eq, Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by omega) (by omega)]
    have hto : ((z + 1) % (n : ℤ)).toNat = 1 + i := by
      rw [hzp1]
      omega
    simp [hin, hto]
  · have hi_last : i = n - 1 := by omega
    have hzp1 : (z + 1) % (n : ℤ) = 0 := by
      have hr_last : r = (n : ℤ) - 1 := by omega
      have hz_eq : z + 1 = 0 + (n : ℤ) * (z / (n : ℤ) + 1) := by
        have h := Int.emod_add_mul_ediv z (n : ℤ)
        change r + (n : ℤ) * (z / (n : ℤ)) = z at h
        linear_combination -h + hr_last
      rw [hz_eq, Int.add_mul_emod_self_left]
      simp
    have hn0 : 0 < n := by omega
    simp [hi_last, hzp1, hn0]

lemma step_bitInt_mod2 {n : ℕ} (hn : 2 ≤ n) (w : BitVec n) (z : ℤ) :
    2 ∣ bitInt (step w) z - (bitInt w (z - 1) + bitInt w z + bitInt w (z + 1)) := by
  unfold bitInt step
  have hxor : bitBool (w.rotateLeft 1 ^^^ w ^^^ w.rotateRight 1) z =
      ((bitBool (w.rotateLeft 1) z ^^ bitBool w z) ^^ bitBool (w.rotateRight 1) z) := by
    unfold bitBool
    rw [BitVec.getLsbD_xor, BitVec.getLsbD_xor]
  rw [hxor, rotateLeft_one_bitBool hn, rotateRight_one_bitBool hn]
  generalize bitBool w (z - 1) = b1
  generalize bitBool w z = b2
  generalize bitBool w (z + 1) = b3
  cases b1 <;> cases b2 <;> cases b3 <;> decide

noncomputable def Tpoly : Polynomial ℤ := 1 + Polynomial.X + Polynomial.X ^ 2

noncomputable def wrap (n : ℕ) (P : Polynomial ℤ) (z : ℤ) : ℤ :=
  P.sum fun j a => if (j : ℤ) % (n : ℤ) = z % (n : ℤ) then a else 0

lemma wrap_zero (n : ℕ) (z : ℤ) : wrap n 0 z = 0 :=
  Polynomial.sum_zero_index _

lemma wrap_add (n : ℕ) (P Q : Polynomial ℤ) (z : ℤ) :
    wrap n (P + Q) z = wrap n P z + wrap n Q z :=
  Polynomial.sum_add_index P Q _ (fun _ => by simp) (fun _ a1 a2 => by split_ifs <;> ring)

lemma wrap_neg (n : ℕ) (P : Polynomial ℤ) (z : ℤ) :
    wrap n (-P) z = -wrap n P z := by
  have h := wrap_add n P (-P) z
  rw [add_neg_cancel, wrap_zero] at h
  linarith

lemma wrap_sub (n : ℕ) (P Q : Polynomial ℤ) (z : ℤ) :
    wrap n (P - Q) z = wrap n P z - wrap n Q z := by
  rw [sub_eq_add_neg, wrap_add, wrap_neg, sub_eq_add_neg]

lemma wrap_monomial (n d : ℕ) (c : ℤ) (z : ℤ) :
    wrap n (Polynomial.monomial d c) z =
      if (d : ℤ) % (n : ℤ) = z % (n : ℤ) then c else 0 :=
  Polynomial.sum_monomial_index c _ (by simp)

lemma wrap_two_mul (n : ℕ) (P : Polynomial ℤ) (z : ℤ) :
    wrap n (2 * P) z = 2 * wrap n P z := by
  have h2 : (2 : Polynomial ℤ) * P = P + P := two_mul P
  rw [h2, wrap_add]
  ring

lemma emod_eq_iff_dvd_sub {m : ℤ} (_hm : 0 < m) (a b : ℤ) :
    a % m = b % m ↔ m ∣ a - b := by
  constructor
  · intro h
    refine ⟨a / m - b / m, ?_⟩
    have h1 := Int.emod_add_mul_ediv a m
    have h2 := Int.emod_add_mul_ediv b m
    linear_combination -h1 + h2 + h
  · rintro ⟨q, hq⟩
    have hrew : a = b + q * m := by linarith
    rw [hrew, mul_comm q m, Int.add_mul_emod_self_left]

lemma wrap_X_pow_mul {n : ℕ} (hn : 1 ≤ n) (k : ℕ) (P : Polynomial ℤ) (z : ℤ) :
    wrap n (Polynomial.X ^ k * P) z = wrap n P (z - (k : ℤ)) := by
  induction P using Polynomial.induction_on' with
  | add P1 P2 ih1 ih2 =>
    rw [mul_add, wrap_add, wrap_add, ih1, ih2]
  | monomial d c =>
    rw [Polynomial.X_pow_eq_monomial, Polynomial.monomial_mul_monomial, one_mul,
      wrap_monomial, wrap_monomial]
    have hiff : ((k + d : ℕ) : ℤ) % (n : ℤ) = z % (n : ℤ) ↔
        (d : ℤ) % (n : ℤ) = (z - (k : ℤ)) % (n : ℤ) := by
      rw [emod_eq_iff_dvd_sub (by omega), emod_eq_iff_dvd_sub (by omega)]
      have hsub : ((k + d : ℕ) : ℤ) - z = (d : ℤ) - (z - (k : ℤ)) := by push_cast; ring
      rw [hsub]
    by_cases hc : ((k + d : ℕ) : ℤ) % (n : ℤ) = z % (n : ℤ)
    · rw [if_pos hc, if_pos (hiff.mp hc)]
    · rw [if_neg hc, if_neg (fun h => hc (hiff.mpr h))]

lemma wrap_mod_period {n : ℕ} (P : Polynomial ℤ) (z k : ℤ) :
    wrap n P (z + k * (n : ℤ)) = wrap n P z := by
  unfold wrap
  have hm : (z + k * (n : ℤ)) % (n : ℤ) = z % (n : ℤ) := by
    rw [mul_comm k (n : ℤ), Int.add_mul_emod_self_left]
  simp_rw [hm]

lemma row_bitInt_wrap {n : ℕ} (hn : 2 ≤ n) :
    ∀ (t : ℕ) (z : ℤ), 2 ∣ bitInt (row n t) z - wrap n (Tpoly ^ t) (z + (t : ℤ))
  | 0, z => by
    have hr0_eq : row n 0 = (1 : BitVec n) := rfl
    rw [hr0_eq]
    unfold bitInt bitBool
    simp only [pow_zero, Int.natCast_zero, add_zero]
    have h1 : (1 : Polynomial ℤ) = Polynomial.monomial 0 1 := by
      simp
    have hbv : (1 : BitVec n) = 1#n := rfl
    rw [h1, wrap_monomial, hbv, BitVec.getLsbD_one]
    have hn0 : 0 < n := by omega
    have hr0 : 0 ≤ z % (n : ℤ) := Int.emod_nonneg z (by omega)
    have hiff : (z % (n : ℤ)).toNat = 0 ↔ z % (n : ℤ) = 0 := by omega
    simp only [Nat.cast_zero, Int.zero_emod]
    by_cases hz : z % (n : ℤ) = 0
    · simp [hn0, hz]
    · have ht : (z % (n : ℤ)).toNat ≠ 0 := fun h => hz (hiff.mp h)
      have hz' : 0 ≠ z % (n : ℤ) := fun h => hz h.symm
      simp [hn0, hz', ht]
  | t + 1, z => by
    have hrow : row n (t + 1) = step (row n t) := by
      unfold row
      rw [Function.iterate_succ_apply']
    rw [hrow]
    have hst := step_bitInt_mod2 hn (row n t) z
    have ih1 := row_bitInt_wrap hn t (z - 1)
    have ih2 := row_bitInt_wrap hn t z
    have ih3 := row_bitInt_wrap hn t (z + 1)
    have hT : Tpoly ^ (t + 1) =
        Tpoly ^ t + Polynomial.X ^ 1 * Tpoly ^ t + Polynomial.X ^ 2 * Tpoly ^ t := by
      unfold Tpoly
      rw [pow_succ']
      ring
    have hw : wrap n (Tpoly ^ (t + 1)) (z + ((t + 1 : ℕ) : ℤ)) =
        wrap n (Tpoly ^ t) (z - 1 + (t : ℤ)) +
        wrap n (Tpoly ^ t) (z + (t : ℤ)) +
        wrap n (Tpoly ^ t) (z + 1 + (t : ℤ)) := by
      rw [hT, wrap_add, wrap_add, wrap_X_pow_mul (by omega), wrap_X_pow_mul (by omega)]
      have a1 : z + ((t + 1 : ℕ) : ℤ) = z + 1 + (t : ℤ) := by push_cast; ring
      have a2 : z + ((t + 1 : ℕ) : ℤ) - ((1 : ℕ) : ℤ) = z + (t : ℤ) := by push_cast; ring
      have a3 : z + ((t + 1 : ℕ) : ℤ) - ((2 : ℕ) : ℤ) = z - 1 + (t : ℤ) := by push_cast; ring
      rw [a2, a3, a1]
      ring
    rw [hw]
    have hlin : bitInt (step (row n t)) z -
        (wrap n (Tpoly ^ t) (z - 1 + (t : ℤ)) +
          wrap n (Tpoly ^ t) (z + (t : ℤ)) +
          wrap n (Tpoly ^ t) (z + 1 + (t : ℤ))) =
        (bitInt (step (row n t)) z -
          (bitInt (row n t) (z - 1) + bitInt (row n t) z + bitInt (row n t) (z + 1))) +
        (bitInt (row n t) (z - 1) - wrap n (Tpoly ^ t) (z - 1 + (t : ℤ))) +
        (bitInt (row n t) z - wrap n (Tpoly ^ t) (z + (t : ℤ))) +
        (bitInt (row n t) (z + 1) - wrap n (Tpoly ^ t) (z + 1 + (t : ℤ))) := by ring
    rw [hlin]
    exact dvd_add (dvd_add (dvd_add hst ih1) ih2) ih3

def ModCyc (n : ℕ) (P : Polynomial ℤ) : Prop :=
  ∃ Q W : Polynomial ℤ, P = (Polynomial.X ^ n - 1) * Q + 2 * W

lemma geom_sum_mul_sub_one (Y : Polynomial ℤ) (k : ℕ) :
    (∑ i ∈ Finset.range k, Y ^ i) * (Y - 1) = Y ^ k - 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, add_mul, ih]
    ring

lemma poly_div_X_pow_sub_one {n : ℕ} (hn : 1 ≤ n) (P : Polynomial ℤ) :
    ∃ Q : Polynomial ℤ,
      P - ∑ r ∈ Finset.range n, Polynomial.C (wrap n P (r : ℤ)) * Polynomial.X ^ r =
        (Polynomial.X ^ n - 1) * Q := by
  induction P using Polynomial.induction_on' with
  | add P1 P2 ih1 ih2 =>
    rcases ih1 with ⟨Q1, hQ1⟩
    rcases ih2 with ⟨Q2, hQ2⟩
    refine ⟨Q1 + Q2, ?_⟩
    have hsum : (∑ r ∈ Finset.range n, Polynomial.C (wrap n (P1 + P2) (r : ℤ)) * Polynomial.X ^ r) =
        (∑ r ∈ Finset.range n, Polynomial.C (wrap n P1 (r : ℤ)) * Polynomial.X ^ r) +
        (∑ r ∈ Finset.range n, Polynomial.C (wrap n P2 (r : ℤ)) * Polynomial.X ^ r) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [wrap_add, map_add, add_mul]
    rw [hsum]
    linear_combination hQ1 + hQ2
  | monomial d c =>
    set r0 := d % n
    set q0 := d / n
    have hr0_lt : r0 < n := Nat.mod_lt d (by omega)
    have hsum : (∑ r ∈ Finset.range n,
          Polynomial.C (wrap n (Polynomial.monomial d c) (r : ℤ)) * Polynomial.X ^ r) =
        Polynomial.C c * Polynomial.X ^ r0 := by
      rw [Finset.sum_eq_single r0]
      · rw [wrap_monomial]
        have hm : (d : ℤ) % (n : ℤ) = (r0 : ℤ) % (n : ℤ) := by
          dsimp [r0]
          exact Int.emod_emod_of_dvd (d : ℤ) (dvd_refl (n : ℤ)) |> fun _ => by
            rw [← Int.natCast_emod]
            exact (Int.emod_eq_of_lt (by omega) (by omega)).symm
        rw [if_pos hm]
      · intro r hr hne
        rw [Finset.mem_range] at hr
        rw [wrap_monomial]
        have hne_mod : (d : ℤ) % (n : ℤ) ≠ (r : ℤ) % (n : ℤ) := by
          rw [← Int.natCast_emod, Int.emod_eq_of_lt (by omega : 0 ≤ (r : ℤ)) (by omega)]
          intro heq
          apply hne
          exact_mod_cast heq.symm
        rw [if_neg hne_mod, map_zero, zero_mul]
      · intro hnot
        exact False.elim (hnot (Finset.mem_range.mpr hr0_lt))
    rw [hsum]
    have hmon : Polynomial.monomial d c = Polynomial.C c * Polynomial.X ^ d := by
      rw [Polynomial.X_pow_eq_monomial]
      have hC : Polynomial.C c = Polynomial.monomial 0 c := by
        ext i; cases i <;> simp
      rw [hC, Polynomial.monomial_mul_monomial, zero_add, mul_one]
    have hd : d = n * q0 + r0 := (Nat.div_add_mod d n).symm
    refine ⟨Polynomial.C c * Polynomial.X ^ r0 * ∑ i ∈ Finset.range q0, (Polynomial.X ^ n) ^ i, ?_⟩
    have hgeom := geom_sum_mul_sub_one (Polynomial.X ^ n : Polynomial ℤ) q0
    rw [hmon, hd, pow_add, pow_mul]
    linear_combination -Polynomial.C c * Polynomial.X ^ r0 * hgeom

lemma ModCyc_iff_wrap {n : ℕ} (hn : 1 ≤ n) (P : Polynomial ℤ) :
    ModCyc n P ↔ ∀ z : ℤ, 2 ∣ wrap n P z := by
  constructor
  · rintro ⟨Q, W, rfl⟩ z
    rw [wrap_add, sub_mul, one_mul, wrap_sub, wrap_X_pow_mul hn, wrap_two_mul]
    have hper : wrap n Q (z - (n : ℤ)) = wrap n Q z := by
      have := wrap_mod_period (n := n) Q z (-1)
      simpa [sub_eq_add_neg] using this
    rw [hper, sub_self, zero_add]
    exact dvd_mul_right 2 _
  · intro h
    rcases poly_div_X_pow_sub_one hn P with ⟨Q, hQ⟩
    have hrem : ∃ W : Polynomial ℤ,
        (∑ r ∈ Finset.range n, Polynomial.C (wrap n P (r : ℤ)) * Polynomial.X ^ r) = 2 * W := by
      refine ⟨∑ r ∈ Finset.range n, Polynomial.C (wrap n P (r : ℤ) / 2) * Polynomial.X ^ r, ?_⟩
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun r _ => ?_
      rcases h (r : ℤ) with ⟨q, hq⟩
      have hdiv : wrap n P (r : ℤ) / 2 = q := by omega
      rw [hdiv, hq]
      have hc2 : (2 : Polynomial ℤ) = Polynomial.C 2 := by simp
      rw [hc2, ← mul_assoc, ← map_mul]
    rcases hrem with ⟨W, hW⟩
    refine ⟨Q, W, ?_⟩
    linear_combination hQ + hW

lemma row_eq_iff_ModCyc {n : ℕ} (hn : 2 ≤ n) (t p : ℕ) :
    row n (t + p) = row n t ↔
      ModCyc n (Tpoly ^ (t + p) - Polynomial.X ^ p * Tpoly ^ t) := by
  rw [ModCyc_iff_wrap (by omega)]
  constructor
  · intro heq z
    have h1 := row_bitInt_wrap hn (t + p) (z - ((t + p : ℕ) : ℤ))
    have h2 := row_bitInt_wrap hn t (z - ((t + p : ℕ) : ℤ))
    rw [heq] at h1
    rw [wrap_sub, wrap_X_pow_mul (by omega)]
    have a1 : z - ((t + p : ℕ) : ℤ) + ((t + p : ℕ) : ℤ) = z := by ring
    have a2 : z - ((t + p : ℕ) : ℤ) + (t : ℤ) = z - (p : ℤ) := by push_cast; ring
    rw [a1] at h1
    rw [a2] at h2
    have hdiff : wrap n (Tpoly ^ (t + p)) z - wrap n (Tpoly ^ t) (z - (p : ℤ)) =
        (bitInt (row n t) (z - ((t + p : ℕ) : ℤ)) - wrap n (Tpoly ^ t) (z - (p : ℤ))) -
        (bitInt (row n t) (z - ((t + p : ℕ) : ℤ)) - wrap n (Tpoly ^ (t + p)) z) := by ring
    rw [hdiff]
    exact dvd_sub h2 h1
  · intro hdvd
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have h1 := row_bitInt_wrap hn (t + p) (i : ℤ)
    have h2 := row_bitInt_wrap hn t (i : ℤ)
    have h3 := hdvd ((i : ℤ) + ((t + p : ℕ) : ℤ))
    rw [wrap_sub, wrap_X_pow_mul (by omega)] at h3
    have a2 : (i : ℤ) + ((t + p : ℕ) : ℤ) - (p : ℤ) = (i : ℤ) + (t : ℤ) := by push_cast; ring
    rw [a2] at h3
    have hb_dvd : 2 ∣ bitInt (row n (t + p)) (i : ℤ) - bitInt (row n t) (i : ℤ) := by
      have hlin : bitInt (row n (t + p)) (i : ℤ) - bitInt (row n t) (i : ℤ) =
          (bitInt (row n (t + p)) (i : ℤ) - wrap n (Tpoly ^ (t + p)) ((i : ℤ) + ((t + p : ℕ) : ℤ))) -
          (bitInt (row n t) (i : ℤ) - wrap n (Tpoly ^ t) ((i : ℤ) + (t : ℤ))) +
          (wrap n (Tpoly ^ (t + p)) ((i : ℤ) + ((t + p : ℕ) : ℤ)) -
            wrap n (Tpoly ^ t) ((i : ℤ) + (t : ℤ))) := by ring
      rw [hlin]
      exact dvd_add (dvd_sub h1 h2) h3
    unfold bitInt bitBool at hb_dvd
    have hmod : ((i : ℤ) % (n : ℤ)).toNat = i := by
      rw [Int.emod_eq_of_lt (by omega) (by omega)]
      omega
    rw [hmod] at hb_dvd
    generalize (row n (t + p)).getLsbD i = b1 at hb_dvd ⊢
    generalize (row n t).getLsbD i = b2 at hb_dvd ⊢
    cases b1 <;> cases b2
    · rfl
    · exfalso; revert hb_dvd; decide
    · exfalso; revert hb_dvd; decide
    · rfl

def PolyMod2 (A B : Polynomial ℤ) : Prop :=
  ∃ W : Polynomial ℤ, A - B = 2 * W

lemma PolyMod2_refl (A : Polynomial ℤ) : PolyMod2 A A := ⟨0, by simp⟩

lemma PolyMod2_symm {A B : Polynomial ℤ} (h : PolyMod2 A B) : PolyMod2 B A := by
  rcases h with ⟨W, hW⟩
  exact ⟨-W, by linear_combination -hW⟩

lemma PolyMod2_trans {A B G : Polynomial ℤ}
    (h1 : PolyMod2 A B) (h2 : PolyMod2 B G) : PolyMod2 A G := by
  rcases h1 with ⟨W1, hW1⟩
  rcases h2 with ⟨W2, hW2⟩
  exact ⟨W1 + W2, by linear_combination hW1 + hW2⟩

lemma PolyMod2_add {A1 B1 A2 B2 : Polynomial ℤ}
    (h1 : PolyMod2 A1 B1) (h2 : PolyMod2 A2 B2) : PolyMod2 (A1 + A2) (B1 + B2) := by
  rcases h1 with ⟨W1, hW1⟩
  rcases h2 with ⟨W2, hW2⟩
  exact ⟨W1 + W2, by linear_combination hW1 + hW2⟩

lemma PolyMod2_mul {A1 B1 A2 B2 : Polynomial ℤ}
    (h1 : PolyMod2 A1 B1) (h2 : PolyMod2 A2 B2) : PolyMod2 (A1 * A2) (B1 * B2) := by
  rcases h1 with ⟨W1, hW1⟩
  rcases h2 with ⟨W2, hW2⟩
  exact ⟨W1 * A2 + B1 * W2, by linear_combination A2 * hW1 + B1 * hW2⟩

lemma PolyMod2_pow {A B : Polynomial ℤ} (h : PolyMod2 A B) (k : ℕ) :
    PolyMod2 (A ^ k) (B ^ k) := by
  induction k with
  | zero => simp [PolyMod2_refl]
  | succ k ih =>
    rw [pow_succ, pow_succ]
    exact PolyMod2_mul ih h

lemma PolyMod2_sub_two_pow (A B : Polynomial ℤ) (v : ℕ) :
    PolyMod2 ((A - B) ^ (2 ^ v)) (A ^ (2 ^ v) - B ^ (2 ^ v)) := by
  induction v with
  | zero => simp [PolyMod2_refl]
  | succ v ih =>
    rw [pow_succ, pow_mul]
    have h1 := PolyMod2_pow ih 2
    have h2 : PolyMod2 ((A ^ (2 ^ v) - B ^ (2 ^ v)) ^ 2)
        ((A ^ (2 ^ v)) ^ 2 - (B ^ (2 ^ v)) ^ 2) :=
      ⟨(B ^ (2 ^ v)) ^ 2 - A ^ (2 ^ v) * B ^ (2 ^ v), by ring⟩
    rw [← pow_mul, ← pow_mul] at h2
    exact PolyMod2_trans h1 h2

lemma Tpoly_two_pow (v : ℕ) :
    PolyMod2 (Tpoly ^ (2 ^ v)) (1 + Polynomial.X ^ (2 ^ v) + Polynomial.X ^ (2 * 2 ^ v)) := by
  induction v with
  | zero =>
    unfold Tpoly
    simp [PolyMod2_refl]
  | succ v ih =>
    rw [pow_succ, pow_mul]
    have h1 := PolyMod2_pow ih 2
    set Y : Polynomial ℤ := Polynomial.X ^ (2 ^ v)
    have hsq : PolyMod2 ((1 + Y + Polynomial.X ^ (2 * 2 ^ v)) ^ 2)
        (1 + Polynomial.X ^ (2 ^ (v + 1)) + Polynomial.X ^ (2 * 2 ^ (v + 1))) := by
      have hy2 : (Polynomial.X : Polynomial ℤ) ^ (2 * 2 ^ v) = Y ^ 2 := by
        dsimp [Y]; rw [← pow_mul, mul_comm 2 (2 ^ v)]
      have hy_next : (Polynomial.X : Polynomial ℤ) ^ (2 ^ (v + 1)) = Y ^ 2 := by
        dsimp [Y]; rw [pow_succ, pow_mul]
      have hy_next2 : (Polynomial.X : Polynomial ℤ) ^ (2 * 2 ^ (v + 1)) = Y ^ 4 := by
        dsimp [Y]; rw [← pow_mul]; congr 1; ring
      rw [hy2, hy_next, hy_next2]
      exact ⟨Y + Y ^ 2 + Y ^ 3, by ring⟩
    exact PolyMod2_trans h1 hsq

lemma ModCyc_add {n : ℕ} {P Q : Polynomial ℤ} (hP : ModCyc n P) (hQ : ModCyc n Q) :
    ModCyc n (P + Q) := by
  rcases hP with ⟨Q1, W1, rfl⟩
  rcases hQ with ⟨Q2, W2, rfl⟩
  exact ⟨Q1 + Q2, W1 + W2, by ring⟩

lemma ModCyc_sub {n : ℕ} {P Q : Polynomial ℤ} (hP : ModCyc n P) (hQ : ModCyc n Q) :
    ModCyc n (P - Q) := by
  rcases hP with ⟨Q1, W1, rfl⟩
  rcases hQ with ⟨Q2, W2, rfl⟩
  exact ⟨Q1 - Q2, W1 - W2, by ring⟩

lemma ModCyc_mul_right {n : ℕ} {P : Polynomial ℤ} (hP : ModCyc n P) (R : Polynomial ℤ) :
    ModCyc n (P * R) := by
  rcases hP with ⟨Q, W, rfl⟩
  exact ⟨Q * R, W * R, by ring⟩

lemma ModCyc_of_PolyMod2 (n : ℕ) {A B : Polynomial ℤ} (h : PolyMod2 A B) :
    ModCyc n (A - B) := by
  rcases h with ⟨W, hW⟩
  exact ⟨0, W, by linear_combination hW⟩

lemma ModCyc_of_dvd {m n : ℕ} (hdvd : m ∣ n) {P : Polynomial ℤ} (h : ModCyc n P) :
    ModCyc m P := by
  rcases hdvd with ⟨k, rfl⟩
  rcases h with ⟨Q, W, rfl⟩
  refine ⟨(∑ i ∈ Finset.range k, (Polynomial.X ^ m) ^ i) * Q, W, ?_⟩
  have hgeom := geom_sum_mul_sub_one (Polynomial.X ^ m : Polynomial ℤ) k
  rw [pow_mul]
  linear_combination -Q * hgeom

lemma not_period_two_pow {v : ℕ} (hv : 2 ≤ v) : period (2 ^ v) ≠ 2 ^ v := by
  set n := 2 ^ v
  set p := 2 ^ (v - 1)
  have hp_pos : 0 < p := Nat.pos_of_ne_zero (by positivity)
  have hn_eq : n = 2 * p := by
    dsimp [n, p]
    conv_lhs => rw [show v = (v - 1) + 1 by omega, pow_succ']
  have hn2 : 2 ≤ n := by omega
  have hmod : ModCyc n (Tpoly ^ (0 + p) - Polynomial.X ^ p * Tpoly ^ 0) := by
    rw [zero_add, pow_zero, mul_one]
    have ht := Tpoly_two_pow (v - 1)
    change PolyMod2 (Tpoly ^ p) (1 + Polynomial.X ^ p + Polynomial.X ^ (2 * p)) at ht
    rw [← hn_eq] at ht
    rcases ht with ⟨W, hW⟩
    refine ⟨1, W + 1, ?_⟩
    linear_combination hW
  have hrow := (row_eq_iff_ModCyc hn2 0 p).mpr hmod
  have hmem : p ∈ {q : ℕ | 0 < q ∧ ∃ t : ℕ, row n (t + q) = row n t} :=
    ⟨hp_pos, 0, hrow⟩
  have hle : period n ≤ p := Nat.sInf_le hmem
  omega

lemma not_period_three_mul_two_pow (v : ℕ) : period (3 * 2 ^ v) ≠ 3 * 2 ^ v := by
  set p := 2 ^ v
  set n := 3 * p
  have hp_pos : 0 < p := Nat.pos_of_ne_zero (by positivity)
  have hn2 : 2 ≤ n := by omega
  have hmod : ModCyc n (Tpoly ^ (p + p) - Polynomial.X ^ p * Tpoly ^ p) := by
    have ht1 := Tpoly_two_pow v
    have ht2 := Tpoly_two_pow (v + 1)
    have hp2 : 2 ^ (v + 1) = p + p := by dsimp [p]; ring
    have hp4 : 2 * (p + p) = 4 * p := by ring
    rw [hp2, hp4] at ht2
    change PolyMod2 (Tpoly ^ p) (1 + Polynomial.X ^ p + Polynomial.X ^ (2 * p)) at ht1
    have hx1 : PolyMod2 (Polynomial.X ^ p * Tpoly ^ p)
        (Polynomial.X ^ p + Polynomial.X ^ (2 * p) + Polynomial.X ^ (3 * p)) := by
      rcases ht1 with ⟨W1, hW1⟩
      refine ⟨Polynomial.X ^ p * W1, ?_⟩
      have e1 : (Polynomial.X : Polynomial ℤ) ^ p * Polynomial.X ^ p = Polynomial.X ^ (2 * p) := by
        rw [← pow_add]; congr 1; omega
      have e2 : (Polynomial.X : Polynomial ℤ) ^ p * Polynomial.X ^ (2 * p) = Polynomial.X ^ (3 * p) := by
        rw [← pow_add]; congr 1; omega
      calc
        Polynomial.X ^ p * Tpoly ^ p -
            (Polynomial.X ^ p + Polynomial.X ^ (2 * p) + Polynomial.X ^ (3 * p))
          = Polynomial.X ^ p * (Tpoly ^ p - (1 + Polynomial.X ^ p + Polynomial.X ^ (2 * p))) +
            (Polynomial.X ^ p * Polynomial.X ^ p - Polynomial.X ^ (2 * p)) +
            (Polynomial.X ^ p * Polynomial.X ^ (2 * p) - Polynomial.X ^ (3 * p)) := by ring
        _ = 2 * (Polynomial.X ^ p * W1) := by rw [hW1, e1, e2]; ring
    rcases ht2 with ⟨W2, hW2⟩
    rcases hx1 with ⟨W1, hW1⟩
    refine ⟨Polynomial.X ^ p - 1, W2 - W1, ?_⟩
    have h4p : (Polynomial.X : Polynomial ℤ) ^ (4 * p) = Polynomial.X ^ n * Polynomial.X ^ p := by
      dsimp [n]; rw [← pow_add]; congr 1; omega
    have h3p : (Polynomial.X : Polynomial ℤ) ^ (3 * p) = Polynomial.X ^ n := rfl
    rw [h4p] at hW2
    rw [h3p] at hW1
    linear_combination hW2 - hW1
  have hrow := (row_eq_iff_ModCyc hn2 p p).mpr hmod
  have hmem : p ∈ {q : ℕ | 0 < q ∧ ∃ t : ℕ, row n (t + q) = row n t} :=
    ⟨hp_pos, p, hrow⟩
  have hle : period n ≤ p := Nat.sInf_le hmem
  omega

lemma exists_vonNeumann_Tpoly {m : ℕ} (hm : 1 ≤ m) (hodd : Odd m) :
    ∃ U : Polynomial ℤ, ModCyc m (Tpoly ^ 2 * U - Tpoly) := by
  have h1X_T : PolyMod2 ((1 + Polynomial.X) * Tpoly) (Polynomial.X ^ 3 - 1) := by
    unfold Tpoly
    exact ⟨1 + Polynomial.X + Polynomial.X ^ 2, by ring⟩
  have h3q_mod : ∀ q : ℕ, ∃ A : Polynomial ℤ, PolyMod2 (Polynomial.X ^ (3 * q) - 1) (A * Tpoly) := by
    intro q
    have hgeom := geom_sum_mul_sub_one (Polynomial.X ^ 3 : Polynomial ℤ) q
    rw [← pow_mul] at hgeom
    rcases h1X_T with ⟨W0, hW0⟩
    refine ⟨(∑ i ∈ Finset.range q, (Polynomial.X ^ 3) ^ i) * (1 + Polynomial.X),
      -(∑ i ∈ Finset.range q, (Polynomial.X ^ 3) ^ i) * W0, ?_⟩
    linear_combination -hgeom - (∑ i ∈ Finset.range q, (Polynomial.X ^ 3) ^ i) * hW0
  have hm3 : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 := by omega
  rcases hm3 with h0 | h1 | h2
  · obtain ⟨d, rfl⟩ : ∃ d, m = 3 * d := ⟨m / 3, by omega⟩
    have hd_odd : Odd d := by
      rcases hodd with ⟨k, hk⟩
      exact Nat.odd_iff.mpr (by omega)
    set S : Polynomial ℤ := ∑ j ∈ Finset.range d, Polynomial.X ^ (3 * j)
    have hS_ann : ModCyc (3 * d) ((1 + Polynomial.X) * Tpoly * S) := by
      have hgeom := geom_sum_mul_sub_one (Polynomial.X ^ 3 : Polynomial ℤ) d
      have hsum_eq : (∑ i ∈ Finset.range d, (Polynomial.X ^ 3 : Polynomial ℤ) ^ i) = S := by
        dsimp [S]
        refine Finset.sum_congr rfl fun j _ => (pow_mul Polynomial.X 3 j).symm
      rw [hsum_eq, ← pow_mul] at hgeom
      rcases h1X_T with ⟨W0, hW0⟩
      refine ⟨1, S * W0, ?_⟩
      linear_combination S * hW0 + hgeom
    have hS_mod : ∃ B : Polynomial ℤ, PolyMod2 S (1 + B * Tpoly) := by
      have h_each : ∀ j : ℕ, ∃ A : Polynomial ℤ,
          PolyMod2 (Polynomial.X ^ (3 * j) - 1) (A * Tpoly) := h3q_mod
      have h_ind : ∀ k : ℕ, ∃ B : Polynomial ℤ,
          PolyMod2 (∑ j ∈ Finset.range k, (Polynomial.X ^ (3 * j) - 1)) (B * Tpoly) := by
        intro k
        induction k with
        | zero => exact ⟨0, by simp [PolyMod2_refl]⟩
        | succ k ih =>
          rcases ih with ⟨B1, hB1⟩
          rcases h_each k with ⟨A1, hA1⟩
          rw [Finset.sum_range_succ]
          have hadd := PolyMod2_add hB1 hA1
          rw [← add_mul] at hadd
          exact ⟨B1 + A1, hadd⟩
      rcases h_ind d with ⟨B, hB⟩
      rcases hd_odd with ⟨r, hr⟩
      rcases hB with ⟨W1, hW1⟩
      refine ⟨B, W1 + (r : Polynomial ℤ), ?_⟩
      have hsum_split : (∑ j ∈ Finset.range d, ((Polynomial.X : Polynomial ℤ) ^ (3 * j) - 1)) =
          S - (d : Polynomial ℤ) := by
        rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range]
        dsimp [S]
        simp
      rw [hsum_split, hr] at hW1
      push_cast at hW1
      linear_combination hW1
    rcases hS_mod with ⟨B, hSB⟩
    have h1T : PolyMod2 (1 - Tpoly) (Polynomial.X * (1 + Polynomial.X)) := by
      unfold Tpoly
      exact ⟨-Polynomial.X - Polynomial.X ^ 2, by ring⟩
    have hprod : PolyMod2 (Tpoly * (1 - Tpoly) * (1 + B * Tpoly))
        (Polynomial.X * ((1 + Polynomial.X) * Tpoly * S)) := by
      have p1 := PolyMod2_mul (PolyMod2_refl Tpoly) h1T
      have p2 := PolyMod2_mul p1 (PolyMod2_symm hSB)
      rcases p2 with ⟨W, hW⟩
      exact ⟨W, by linear_combination hW⟩
    have hcyc1 : ModCyc (3 * d) (Polynomial.X * ((1 + Polynomial.X) * Tpoly * S)) := by
      rw [mul_comm Polynomial.X]
      exact ModCyc_mul_right hS_ann Polynomial.X
    have hcyc2 := ModCyc_add (ModCyc_of_PolyMod2 (3 * d) hprod) hcyc1
    have hcancel : Tpoly * (1 - Tpoly) * (1 + B * Tpoly) -
        Polynomial.X * ((1 + Polynomial.X) * Tpoly * S) +
        Polynomial.X * ((1 + Polynomial.X) * Tpoly * S) =
        -(Tpoly ^ 2 * (1 - B + B * Tpoly) - Tpoly) := by ring
    rw [hcancel] at hcyc2
    rcases hcyc2 with ⟨Q, W, hQW⟩
    exact ⟨1 - B + B * Tpoly, -Q, -W, by linear_combination -hQW⟩
  · obtain ⟨q, rfl⟩ : ∃ q, m = 3 * q + 1 := ⟨m / 3, by omega⟩
    rcases h3q_mod q with ⟨A, W1, hW1⟩
    refine ⟨1 + Polynomial.X ^ 2 * A, Polynomial.X * Tpoly,
      Tpoly * (Polynomial.X - Polynomial.X ^ 2 * W1), ?_⟩
    have hpow : (Polynomial.X : Polynomial ℤ) ^ (3 * q + 1) =
        Polynomial.X * Polynomial.X ^ (3 * q) := by rw [pow_add, pow_one, mul_comm]
    have hT_def : Tpoly = 1 + Polynomial.X + Polynomial.X ^ 2 := rfl
    rw [hpow]
    linear_combination Tpoly * hT_def - Tpoly * Polynomial.X ^ 2 * hW1
  · obtain ⟨q, rfl⟩ : ∃ q, m = 3 * q + 2 := ⟨m / 3, by omega⟩
    rcases h3q_mod q with ⟨A, hA⟩
    set M := 3 * q + 2
    have hcyc1 : ModCyc M (Polynomial.X ^ 2 * (Polynomial.X ^ (3 * q) - 1) + (Polynomial.X ^ 2 - 1)) := by
      refine ⟨1, 0, ?_⟩
      have hpow : (Polynomial.X : Polynomial ℤ) ^ M = Polynomial.X ^ 2 * Polynomial.X ^ (3 * q) := by
        dsimp [M]; rw [pow_add, mul_comm]
      rw [hpow]
      ring
    have hcyc2 : ModCyc M (Polynomial.X ^ 2 * A * Tpoly + (Polynomial.X ^ 2 - 1)) := by
      have hd := ModCyc_of_PolyMod2 M (PolyMod2_mul (PolyMod2_refl (Polynomial.X ^ 2)) (PolyMod2_symm hA))
      have hs := ModCyc_add hd hcyc1
      have heq : Polynomial.X ^ 2 * (A * Tpoly) - Polynomial.X ^ 2 * (Polynomial.X ^ (3 * q) - 1) +
          (Polynomial.X ^ 2 * (Polynomial.X ^ (3 * q) - 1) + (Polynomial.X ^ 2 - 1)) =
          Polynomial.X ^ 2 * A * Tpoly + (Polynomial.X ^ 2 - 1) := by ring
      rwa [heq] at hs
    have hTX : PolyMod2 (Tpoly - Polynomial.X - (Polynomial.X ^ 2 - 1)) 0 := by
      unfold Tpoly; exact ⟨1, by ring⟩
    have hcyc3 : ModCyc M (Tpoly * (1 + Polynomial.X ^ 2 * A) - Polynomial.X) := by
      rcases hTX with ⟨W0, hW0⟩
      have hd : ModCyc M (Tpoly - Polynomial.X - (Polynomial.X ^ 2 - 1)) := ⟨0, W0, by linear_combination hW0⟩
      have hs := ModCyc_add hd hcyc2
      have heq : Tpoly - Polynomial.X - (Polynomial.X ^ 2 - 1) +
          (Polynomial.X ^ 2 * A * Tpoly + (Polynomial.X ^ 2 - 1)) =
          Tpoly * (1 + Polynomial.X ^ 2 * A) - Polynomial.X := by ring
      rwa [heq] at hs
    have hcyc4 := ModCyc_mul_right hcyc3 (Tpoly * Polynomial.X ^ (M - 1))
    have hcyc5 : ModCyc M ((Polynomial.X ^ M - 1) * Tpoly) := ⟨Tpoly, 0, by ring⟩
    have hcyc6 := ModCyc_add hcyc4 hcyc5
    have hM1 : Polynomial.X * Polynomial.X ^ (M - 1) = (Polynomial.X : Polynomial ℤ) ^ M := by
      rw [← pow_succ', show M - 1 + 1 = M by omega]
    have heq6 : (Tpoly * (1 + Polynomial.X ^ 2 * A) - Polynomial.X) * (Tpoly * Polynomial.X ^ (M - 1)) +
        (Polynomial.X ^ M - 1) * Tpoly =
        Tpoly ^ 2 * (Polynomial.X ^ (M - 1) * (1 + Polynomial.X ^ 2 * A)) - Tpoly := by
      calc
        (Tpoly * (1 + Polynomial.X ^ 2 * A) - Polynomial.X) * (Tpoly * Polynomial.X ^ (M - 1)) +
            (Polynomial.X ^ M - 1) * Tpoly
          = Tpoly ^ 2 * (Polynomial.X ^ (M - 1) * (1 + Polynomial.X ^ 2 * A)) -
            (Polynomial.X * Polynomial.X ^ (M - 1)) * Tpoly + (Polynomial.X ^ M - 1) * Tpoly := by ring
        _ = Tpoly ^ 2 * (Polynomial.X ^ (M - 1) * (1 + Polynomial.X ^ 2 * A)) - Tpoly := by
          rw [hM1]; ring
    rw [heq6] at hcyc6
    exact ⟨Polynomial.X ^ (M - 1) * (1 + Polynomial.X ^ 2 * A), hcyc6⟩

lemma reduce_transient_ModCyc {m : ℕ} (hm : 1 ≤ m) (hodd : Odd m) :
    ∀ (k b : ℕ) (R : Polynomial ℤ), 1 ≤ b →
      ModCyc m (Tpoly ^ (b + k) * R) → ModCyc m (Tpoly ^ b * R) := by
  intro k
  induction k with
  | zero => intro b R _ h; simpa using h
  | succ k ih =>
    intro b R hb h
    rcases exists_vonNeumann_Tpoly hm hodd with ⟨U, hU⟩
    have hmul := ModCyc_mul_right h U
    have hstep : ModCyc m ((Tpoly ^ 2 * U - Tpoly) * (Tpoly ^ (b + k - 1) * R)) :=
      ModCyc_mul_right hU _
    have hdiff := ModCyc_sub hmul hstep
    have heq : Tpoly ^ (b + (k + 1)) * R * U -
        (Tpoly ^ 2 * U - Tpoly) * (Tpoly ^ (b + k - 1) * R) =
        Tpoly ^ (b + k) * R := by
      have hb1 : b + (k + 1) = 2 + (b + k - 1) := by omega
      have hb2 : b + k = 1 + (b + k - 1) := by omega
      rw [hb1, pow_add]
      conv_rhs => rw [hb2, pow_add, pow_one]
      ring
    rw [heq] at hdiff
    exact ih b R hb hdiff

noncomputable def expandPoly (k : ℕ) (P : Polynomial ℤ) : Polynomial ℤ :=
  P.sum fun i a => Polynomial.monomial (k * i) a

lemma expandPoly_zero (k : ℕ) : expandPoly k 0 = 0 :=
  Polynomial.sum_zero_index _

lemma expandPoly_add (k : ℕ) (P Q : Polynomial ℤ) :
    expandPoly k (P + Q) = expandPoly k P + expandPoly k Q :=
  Polynomial.sum_add_index P Q _ (fun _ => by simp) (fun _ _ _ => map_add (Polynomial.monomial _) _ _)

lemma expandPoly_monomial (k d : ℕ) (c : ℤ) :
    expandPoly k (Polynomial.monomial d c) = Polynomial.monomial (k * d) c :=
  Polynomial.sum_monomial_index c _ (by simp)

lemma expandPoly_mul (k : ℕ) (P Q : Polynomial ℤ) :
    expandPoly k (P * Q) = expandPoly k P * expandPoly k Q := by
  induction P using Polynomial.induction_on' with
  | add P1 P2 ih1 ih2 =>
    rw [add_mul, expandPoly_add, expandPoly_add, ih1, ih2, add_mul]
  | monomial d1 c1 =>
    rw [expandPoly_monomial]
    induction Q using Polynomial.induction_on' with
    | add Q1 Q2 ihQ1 ihQ2 =>
      rw [mul_add, expandPoly_add, expandPoly_add, mul_add, ihQ1, ihQ2]
    | monomial d2 c2 =>
      rw [Polynomial.monomial_mul_monomial, expandPoly_monomial, expandPoly_monomial,
        Polynomial.monomial_mul_monomial, mul_add]

lemma expandPoly_pow (k : ℕ) (P : Polynomial ℤ) (d : ℕ) :
    expandPoly k (P ^ d) = (expandPoly k P) ^ d := by
  induction d with
  | zero =>
    change expandPoly k (Polynomial.monomial 0 1) = 1
    rw [expandPoly_monomial, mul_zero]
    rfl
  | succ d ih =>
    rw [pow_succ, expandPoly_mul, ih, pow_succ]

lemma sq_PolyMod2_expand2 (P : Polynomial ℤ) :
    PolyMod2 (P ^ 2) (expandPoly 2 P) := by
  induction P using Polynomial.induction_on' with
  | add P1 P2 ih1 ih2 =>
    rw [expandPoly_add]
    have hsq : PolyMod2 ((P1 + P2) ^ 2) (P1 ^ 2 + P2 ^ 2) := ⟨P1 * P2, by ring⟩
    exact PolyMod2_trans hsq (PolyMod2_add ih1 ih2)
  | monomial d c =>
    rw [sq, Polynomial.monomial_mul_monomial, expandPoly_monomial]
    have hd : d + d = 2 * d := by omega
    rw [hd]
    have hc : ∃ q : ℤ, c * c - c = 2 * q := by
      rcases Int.even_or_odd c with ⟨k, rfl⟩ | ⟨k, rfl⟩
      · exact ⟨2 * k ^ 2 - k, by ring⟩
      · exact ⟨2 * k ^ 2 + k, by ring⟩
    rcases hc with ⟨q, hq⟩
    refine ⟨Polynomial.monomial (2 * d) q, ?_⟩
    have hsub : Polynomial.monomial (2 * d) (c * c) - Polynomial.monomial (2 * d) c =
        Polynomial.monomial (2 * d) (c * c - c) := by
      ext i; simp [Polynomial.coeff_monomial]
    have h2m : (2 : Polynomial ℤ) * Polynomial.monomial (2 * d) q =
        Polynomial.monomial (2 * d) (2 * q) :=
      calc
        (2 : Polynomial ℤ) * Polynomial.monomial (2 * d) q
          = Polynomial.monomial (2 * d) q + Polynomial.monomial (2 * d) q := two_mul _
        _ = Polynomial.monomial (2 * d) (q + q) := (map_add (Polynomial.monomial (2 * d)) q q).symm
        _ = Polynomial.monomial (2 * d) (2 * q) := by congr 1; ring
    rw [hsub, hq, h2m]

lemma wrap_expand2_odd {m : ℕ} (hodd : Odd m) (P : Polynomial ℤ) (z : ℤ) :
    wrap m (expandPoly 2 P) (2 * z) = wrap m P z := by
  induction P using Polynomial.induction_on' with
  | add P1 P2 ih1 ih2 =>
    rw [expandPoly_add, wrap_add, wrap_add, ih1, ih2]
  | monomial d c =>
    rw [expandPoly_monomial, wrap_monomial, wrap_monomial]
    rcases hodd with ⟨k, hk⟩
    have hm_pos : 0 < (m : ℤ) := by omega
    have hiff : ((2 * d : ℕ) : ℤ) % (m : ℤ) = (2 * z) % (m : ℤ) ↔
        (d : ℤ) % (m : ℤ) = z % (m : ℤ) := by
      rw [emod_eq_iff_dvd_sub hm_pos, emod_eq_iff_dvd_sub hm_pos]
      constructor
      · rintro ⟨q, hq⟩
        refine ⟨((d : ℤ) - z) - (k : ℤ) * q, ?_⟩
        have hm_eq : (m : ℤ) = 2 * (k : ℤ) + 1 := by omega
        have hd_cast : ((2 * d : ℕ) : ℤ) = 2 * (d : ℤ) := by push_cast; ring
        rw [hd_cast] at hq
        linear_combination -(k : ℤ) * hq - ((d : ℤ) - z) * hm_eq
      · rintro ⟨q, hq⟩
        refine ⟨2 * q, ?_⟩
        push_cast
        linear_combination 2 * hq
    by_cases hc : ((2 * d : ℕ) : ℤ) % (m : ℤ) = (2 * z) % (m : ℤ)
    · rw [if_pos hc, if_pos (hiff.mp hc)]
    · rw [if_neg hc, if_neg (fun h => hc (hiff.mpr h))]

lemma ModCyc_of_sq_odd {m : ℕ} (hm : 1 ≤ m) (hodd : Odd m) {P : Polynomial ℤ}
    (h : ModCyc m (P ^ 2)) : ModCyc m P := by
  have hexp : ModCyc m (expandPoly 2 P) := by
    have hdiff := ModCyc_of_PolyMod2 m (PolyMod2_symm (sq_PolyMod2_expand2 P))
    have hsum := ModCyc_add hdiff h
    simpa using hsum
  rw [ModCyc_iff_wrap hm] at hexp ⊢
  intro z
  rw [← wrap_expand2_odd hodd P z]
  exact hexp (2 * z)

lemma ModCyc_of_two_pow_odd {m : ℕ} (hm : 1 ≤ m) (hodd : Odd m) :
    ∀ (v : ℕ) {P : Polynomial ℤ}, ModCyc m (P ^ (2 ^ v)) → ModCyc m P
  | 0, P, h => by simpa using h
  | v + 1, P, h => by
    rw [pow_succ, pow_mul] at h
    exact ModCyc_of_two_pow_odd hm hodd v (ModCyc_of_sq_odd hm hodd h)

inductive MidSupp (B : ℕ) : Polynomial ℤ → Prop
  | zero : MidSupp B 0
  | add {P Q} : MidSupp B P → MidSupp B Q → MidSupp B (P + Q)
  | mono (i : ℕ) (c : ℤ) (h1 : 1 ≤ i) (h2 : i < B) : MidSupp B (Polynomial.monomial i c)

lemma MidSupp_mono {B1 B2 : ℕ} (hle : B1 ≤ B2) {P : Polynomial ℤ} (h : MidSupp B1 P) :
    MidSupp B2 P := by
  induction h with
  | zero => exact MidSupp.zero
  | add _ _ ih1 ih2 => exact MidSupp.add ih1 ih2
  | mono i c h1 h2 => exact MidSupp.mono i c h1 (lt_of_lt_of_le h2 hle)

lemma MidSupp_mul_monomial {B d : ℕ} (c : ℤ) {P : Polynomial ℤ} (h : MidSupp B P) :
    MidSupp (B + d) (P * Polynomial.monomial d c) := by
  induction h with
  | zero => rw [zero_mul]; exact MidSupp.zero
  | add _ _ ih1 ih2 => rw [add_mul]; exact MidSupp.add ih1 ih2
  | mono i a h1 h2 =>
    rw [Polynomial.monomial_mul_monomial]
    exact MidSupp.mono (i + d) (a * c) (by omega) (by omega)

lemma X_eq_mono1 : (Polynomial.X : Polynomial ℤ) = Polynomial.monomial 1 1 := by
  simpa using Polynomial.X_pow_eq_monomial 1

lemma Tpoly_pow_decomp {K : ℕ} (hK : 1 ≤ K) :
    ∃ R : Polynomial ℤ, MidSupp (2 * K) R ∧
      Tpoly ^ K = 1 + R + Polynomial.monomial (2 * K) 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, K = k + 1 := ⟨K - 1, by omega⟩
  clear hK
  induction k with
  | zero =>
    refine ⟨Polynomial.monomial 1 1, MidSupp.mono 1 1 (by omega) (by omega), ?_⟩
    unfold Tpoly
    rw [pow_one, Polynomial.X_pow_eq_monomial, X_eq_mono1]
  | succ k ih =>
    rcases ih with ⟨R, hR, hpow⟩
    set B := 2 * (k + 1)
    have hT : Tpoly = 1 + Polynomial.monomial 1 1 + Polynomial.monomial 2 1 := by
      unfold Tpoly
      rw [Polynomial.X_pow_eq_monomial, X_eq_mono1]
    set R' := Polynomial.monomial 1 1 + Polynomial.monomial 2 1 +
      R + R * Polynomial.monomial 1 1 + R * Polynomial.monomial 2 1 +
      Polynomial.monomial B 1 + Polynomial.monomial (B + 1) 1
    refine ⟨R', ?_, ?_⟩
    · have hB : 2 * (k + 1 + 1) = B + 2 := by dsimp [B]; omega
      rw [hB]
      have m1 : MidSupp (B + 2) (Polynomial.monomial 1 1) := MidSupp.mono 1 1 (by omega) (by dsimp [B]; omega)
      have m2 : MidSupp (B + 2) (Polynomial.monomial 2 1) := MidSupp.mono 2 1 (by omega) (by dsimp [B]; omega)
      have m3 : MidSupp (B + 2) R := MidSupp_mono (by omega) hR
      have m4 : MidSupp (B + 2) (R * Polynomial.monomial 1 1) :=
        MidSupp_mono (by omega) (MidSupp_mul_monomial 1 hR)
      have m5 : MidSupp (B + 2) (R * Polynomial.monomial 2 1) :=
        MidSupp_mul_monomial 1 hR
      have m6 : MidSupp (B + 2) (Polynomial.monomial B 1) :=
        MidSupp.mono B 1 (by dsimp [B]; omega) (by omega)
      have m7 : MidSupp (B + 2) (Polynomial.monomial (B + 1) 1) :=
        MidSupp.mono (B + 1) 1 (by dsimp [B]; omega) (by omega)
      exact MidSupp.add (MidSupp.add (MidSupp.add (MidSupp.add (MidSupp.add (MidSupp.add m1 m2) m3) m4) m5) m6) m7
    · rw [pow_succ, hpow, hT]
      have hmB1 : Polynomial.monomial B (1 : ℤ) * Polynomial.monomial 1 1 =
          Polynomial.monomial (B + 1) 1 := by rw [Polynomial.monomial_mul_monomial, mul_one]
      have hmB2 : Polynomial.monomial B (1 : ℤ) * Polynomial.monomial 2 1 =
          Polynomial.monomial (2 * (k + 1 + 1)) 1 := by
        rw [Polynomial.monomial_mul_monomial, mul_one]; rfl
      dsimp [R']
      rw [← hmB1, ← hmB2]
      ring

lemma wrap_mid_vanish {m s K : ℕ} (c : ℕ) (hs : 1 ≤ s) (hK : 1 ≤ K)
    (hm : m + 1 = 2 ^ s + 2 ^ (s + 1) * K) (hc : c ≤ 2)
    {R : Polynomial ℤ} (hR : MidSupp (2 * K) R) :
    wrap m (Polynomial.monomial (c * 2 ^ s) 1 * expandPoly (2 ^ (s + 1)) R) ((2 ^ s : ℕ) : ℤ) = 0 := by
  induction hR with
  | zero => rw [expandPoly_zero, mul_zero, wrap_zero]
  | add _ _ ih1 ih2 => rw [expandPoly_add, mul_add, wrap_add, ih1, ih2, add_zero]
  | mono i a hi1 hi2 =>
    rw [expandPoly_monomial, Polynomial.monomial_mul_monomial, one_mul, wrap_monomial]
    rw [if_neg]
    intro hmod
    set d := c * 2 ^ s + 2 ^ (s + 1) * i
    have hs_ge2 : 2 ≤ 2 ^ s := le_trans (by decide : 2 ≤ 2 ^ 1) (Nat.pow_le_pow_right (by decide) hs)
    have hpow_next : 2 ^ (s + 1) = 2 * 2 ^ s := by ring
    have hd_gt : 2 ^ s < d := by dsimp [d]; nlinarith
    have hd_lt : d < 2 * m + 2 ^ s := by
      dsimp [d]
      have hi_le : i ≤ 2 * K - 1 := by omega
      nlinarith
    have hm_pos : 0 < (m : ℤ) := by omega
    rcases (emod_eq_iff_dvd_sub hm_pos _ _).mp hmod with ⟨q, hq⟩
    have hpos : 0 < (d : ℤ) - ((2 ^ s : ℕ) : ℤ) := by omega
    have hlt2 : (d : ℤ) - ((2 ^ s : ℕ) : ℤ) < 2 * (m : ℤ) := by omega
    have hq1 : q = 1 := by nlinarith
    rw [hq1, mul_one] at hq
    have hd_eq : d = m + 2 ^ s := by omega
    have hdvd_lhs : 2 ^ s ∣ d := by
      dsimp [d]
      rw [hpow_next]
      exact ⟨c + 2 * i, by ring⟩
    have hrem_rhs : (m + 2 ^ s) % 2 ^ s = 2 ^ s - 1 := by
      have hmul : 2 ^ (s + 1) * K = 2 ^ s * (2 * K) := by rw [hpow_next]; ring
      have hrew : m + 2 ^ s = (2 ^ s - 1) + 2 ^ s * (2 * K + 1) := by
        rw [Nat.mul_add, mul_one]
        omega
      rw [hrew, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
    rcases hdvd_lhs with ⟨u, hu⟩
    have h0 : d % 2 ^ s = 0 := by rw [hu, Nat.mul_mod_right]
    rw [hd_eq, hrem_rhs] at h0
    omega

lemma odd_mersenne_of_ModCyc {m : ℕ} (hm1 : 1 ≤ m) (hodd : Odd m)
    (hcyc : ModCyc m (Tpoly ^ (m + 1) - Tpoly)) :
    ∃ k : ℕ, 1 ≤ k ∧ m = 2 ^ k - 1 := by
  by_contra hnot
  have hex : ∃ s K : ℕ, 1 ≤ s ∧ 1 ≤ K ∧ m + 1 = 2 ^ s + 2 ^ (s + 1) * K := by
    have hstrip : ∀ x : ℕ, 0 < x → ∃ s u : ℕ, 2 ^ s * u = x ∧ Odd u := by
      intro x
      induction x using Nat.strong_induction_on with
      | h x ih =>
        intro hx
        by_cases hev : 2 ∣ x
        · rcases hev with ⟨y, rfl⟩
          rcases ih y (by omega) (by omega) with ⟨s, u, heq, hu⟩
          exact ⟨s + 1, u, by rw [pow_succ', mul_assoc, heq], hu⟩
        · exact ⟨0, x, by simp, Nat.odd_iff.mpr (by omega)⟩
    rcases hstrip (m + 1) (by omega) with ⟨s, u, hsu, hu_odd⟩
    have hs1 : 1 ≤ s := by
      by_contra hs0
      have hsz : s = 0 := by omega
      subst hsz
      simp at hsu
      rcases hodd with ⟨k1, hk1⟩
      rcases hu_odd with ⟨k2, hk2⟩
      omega
    have hu_ne1 : u ≠ 1 := by
      intro hu1
      subst hu1
      apply hnot
      exact ⟨s, hs1, by omega⟩
    rcases hu_odd with ⟨K, rfl⟩
    have hK1 : 1 ≤ K := by omega
    refine ⟨s, K, hs1, hK1, ?_⟩
    rw [← hsu, pow_succ]
    ring
  rcases hex with ⟨s, K, hs1, hK1, hm_eq⟩
  have hs_ge2 : 2 ≤ 2 ^ s := le_trans (by decide : 2 ≤ 2 ^ 1) (Nat.pow_le_pow_right (by decide) hs1)
  have hpow_next : 2 ^ (s + 1) = 2 * 2 ^ s := by ring
  have hm_ge5 : 5 ≤ m := by nlinarith
  have hT_m1 : PolyMod2 (Tpoly ^ (m + 1))
      ((1 + Polynomial.X ^ (2 ^ s) + Polynomial.X ^ (2 * 2 ^ s)) *
        expandPoly (2 ^ (s + 1)) (Tpoly ^ K)) := by
    rw [hm_eq, pow_add]
    have p1 := Tpoly_two_pow s
    have p2 : PolyMod2 (Tpoly ^ (2 ^ (s + 1) * K)) (expandPoly (2 ^ (s + 1)) (Tpoly ^ K)) := by
      rw [pow_mul, expandPoly_pow]
      have hexpT : expandPoly (2 ^ (s + 1)) Tpoly =
          1 + Polynomial.X ^ (2 ^ (s + 1)) + Polynomial.X ^ (2 * 2 ^ (s + 1)) := by
        have hT_m : Tpoly = Polynomial.monomial 0 1 + Polynomial.monomial 1 1 + Polynomial.monomial 2 1 := by
          unfold Tpoly
          rw [show (1 : Polynomial ℤ) = Polynomial.monomial 0 1 by simp,
            Polynomial.X_pow_eq_monomial, X_eq_mono1]
        rw [hT_m, expandPoly_add, expandPoly_add,
          expandPoly_monomial, expandPoly_monomial, expandPoly_monomial,
          mul_zero, mul_one, mul_comm (2 ^ (s + 1)) 2,
          ← Polynomial.X_pow_eq_monomial, ← Polynomial.X_pow_eq_monomial]
        simp [← Polynomial.X_pow_eq_monomial]
      rw [hexpT]
      exact PolyMod2_pow (Tpoly_two_pow (s + 1)) K
    exact PolyMod2_mul p1 p2
  have hcyc_prod : ModCyc m
      ((1 + Polynomial.X ^ (2 ^ s) + Polynomial.X ^ (2 * 2 ^ s)) *
        expandPoly (2 ^ (s + 1)) (Tpoly ^ K) - Tpoly) := by
    have hd := ModCyc_of_PolyMod2 m (PolyMod2_symm hT_m1)
    have hsum := ModCyc_add hd hcyc
    simpa using hsum
  have hdvd2 := (ModCyc_iff_wrap hm1 _).mp hcyc_prod ((2 ^ s : ℕ) : ℤ)
  rw [wrap_sub] at hdvd2
  rcases Tpoly_pow_decomp hK1 with ⟨R, hR, hTK⟩
  rw [hTK, expandPoly_add, expandPoly_add, expandPoly_monomial] at hdvd2
  have hexp1 : expandPoly (2 ^ (s + 1)) 1 = 1 := by
    change expandPoly (2 ^ (s + 1)) (Polynomial.monomial 0 1) = 1
    rw [expandPoly_monomial, mul_zero]; rfl
  rw [hexp1] at hdvd2
  set L0 := 1 + (Polynomial.X : Polynomial ℤ) ^ (2 ^ s) + Polynomial.X ^ (2 * 2 ^ s)
  have hL0 : L0 = Polynomial.monomial (0 * 2 ^ s) 1 + Polynomial.monomial (1 * 2 ^ s) 1 +
      Polynomial.monomial (2 * 2 ^ s) 1 := by
    dsimp [L0]
    simp only [zero_mul, one_mul, Polynomial.X_pow_eq_monomial]
    rfl
  rw [mul_add, mul_add, mul_one, wrap_add, wrap_add] at hdvd2
  have hw_mid : wrap m (L0 * expandPoly (2 ^ (s + 1)) R) ((2 ^ s : ℕ) : ℤ) = 0 := by
    rw [hL0, add_mul, add_mul, wrap_add, wrap_add,
      wrap_mid_vanish 0 hs1 hK1 hm_eq (by omega) hR,
      wrap_mid_vanish 1 hs1 hK1 hm_eq (by omega) hR,
      wrap_mid_vanish 2 hs1 hK1 hm_eq (by omega) hR]
    simp
  rw [hw_mid, add_zero] at hdvd2
  have hw_low : wrap m L0 ((2 ^ s : ℕ) : ℤ) = 1 := by
    rw [hL0, wrap_add, wrap_add, wrap_monomial, wrap_monomial, wrap_monomial]
    simp only [zero_mul, one_mul]
    have h2s_lt : 2 ^ s < m := by nlinarith
    have e0 : ((0 : ℕ) : ℤ) % (m : ℤ) ≠ ((2 ^ s : ℕ) : ℤ) % (m : ℤ) := by
      rw [Nat.cast_zero, Int.zero_emod, Int.emod_eq_of_lt (by omega) (by omega)]
      omega
    have e2 : ((2 * 2 ^ s : ℕ) : ℤ) % (m : ℤ) ≠ ((2 ^ s : ℕ) : ℤ) % (m : ℤ) := by
      intro heq
      rcases (emod_eq_iff_dvd_sub (by omega) _ _).mp heq with ⟨q, hq⟩
      have hdiff : ((2 * 2 ^ s : ℕ) : ℤ) - ((2 ^ s : ℕ) : ℤ) = ((2 ^ s : ℕ) : ℤ) := by
        push_cast; ring
      rw [hdiff] at hq
      have hpos : 0 < ((2 ^ s : ℕ) : ℤ) := by omega
      have hlt : ((2 ^ s : ℕ) : ℤ) < (m : ℤ) := by omega
      by_cases hq0 : q ≤ 0
      · nlinarith
      · nlinarith
    rw [if_neg e0, if_neg e2]
    simp
  have hw_high_split : wrap m (L0 * Polynomial.monomial (2 ^ (s + 1) * (2 * K)) 1) ((2 ^ s : ℕ) : ℤ) =
      wrap m (Polynomial.monomial (2 ^ (s + 1) * (2 * K)) 1) ((2 ^ s : ℕ) : ℤ) +
      wrap m (Polynomial.monomial (2 ^ s + 2 ^ (s + 1) * (2 * K)) 1) ((2 ^ s : ℕ) : ℤ) +
      wrap m (Polynomial.monomial (2 * 2 ^ s + 2 ^ (s + 1) * (2 * K)) 1) ((2 ^ s : ℕ) : ℤ) := by
    rw [hL0, add_mul, add_mul, wrap_add, wrap_add,
      Polynomial.monomial_mul_monomial, Polynomial.monomial_mul_monomial, Polynomial.monomial_mul_monomial]
    simp only [zero_mul, zero_add, one_mul]
  have hw_h0 : wrap m (Polynomial.monomial (2 ^ (s + 1) * (2 * K)) 1) ((2 ^ s : ℕ) : ℤ) = 0 := by
    rw [wrap_monomial, if_neg]
    intro hmod
    set d := 2 ^ (s + 1) * (2 * K)
    have hd_gt : 2 ^ s < d := by dsimp [d]; nlinarith
    have hd_lt : d < 2 * m + 2 ^ s := by dsimp [d]; nlinarith
    rcases (emod_eq_iff_dvd_sub (by omega) _ _).mp hmod with ⟨q, hq⟩
    have hpos : 0 < (d : ℤ) - ((2 ^ s : ℕ) : ℤ) := by omega
    have hlt2 : (d : ℤ) - ((2 ^ s : ℕ) : ℤ) < 2 * (m : ℤ) := by omega
    have hm_pos : 0 < (m : ℤ) := by omega
    have hq1 : q = 1 := by nlinarith
    rw [hq1, mul_one] at hq
    have hd_eq : d = m + 2 ^ s := by omega
    have hdvd_d : 2 ^ s ∣ d := by dsimp [d]; rw [hpow_next]; exact ⟨4 * K, by ring⟩
    rcases hdvd_d with ⟨u, hu⟩
    have hrem : (m + 2 ^ s) % 2 ^ s = 2 ^ s - 1 := by
      have hmul : 2 ^ (s + 1) * K = 2 ^ s * (2 * K) := by rw [hpow_next]; ring
      have hrew : m + 2 ^ s = (2 ^ s - 1) + 2 ^ s * (2 * K + 1) := by
        rw [Nat.mul_add, mul_one]; omega
      rw [hrew, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
    have h0 : d % 2 ^ s = 0 := by rw [hu, Nat.mul_mod_right]
    rw [hd_eq, hrem] at h0
    omega
  have hw_h1 : wrap m (Polynomial.monomial (2 ^ s + 2 ^ (s + 1) * (2 * K)) 1) ((2 ^ s : ℕ) : ℤ) = 0 := by
    rw [wrap_monomial, if_neg]
    intro hmod
    set d := 2 ^ s + 2 ^ (s + 1) * (2 * K)
    have hd_gt : 2 ^ s < d := by dsimp [d]; nlinarith
    have hd_lt : d < 2 * m + 2 ^ s := by dsimp [d]; nlinarith
    rcases (emod_eq_iff_dvd_sub (by omega) _ _).mp hmod with ⟨q, hq⟩
    have hpos : 0 < (d : ℤ) - ((2 ^ s : ℕ) : ℤ) := by omega
    have hlt2 : (d : ℤ) - ((2 ^ s : ℕ) : ℤ) < 2 * (m : ℤ) := by omega
    have hm_pos : 0 < (m : ℤ) := by omega
    have hq1 : q = 1 := by nlinarith
    rw [hq1, mul_one] at hq
    have hd_eq : d = m + 2 ^ s := by omega
    have hdvd_d : 2 ^ s ∣ d := by dsimp [d]; rw [hpow_next]; exact ⟨1 + 4 * K, by ring⟩
    rcases hdvd_d with ⟨u, hu⟩
    have hrem : (m + 2 ^ s) % 2 ^ s = 2 ^ s - 1 := by
      have hmul : 2 ^ (s + 1) * K = 2 ^ s * (2 * K) := by rw [hpow_next]; ring
      have hrew : m + 2 ^ s = (2 ^ s - 1) + 2 ^ s * (2 * K + 1) := by
        rw [Nat.mul_add, mul_one]; omega
      rw [hrew, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
    have h0 : d % 2 ^ s = 0 := by rw [hu, Nat.mul_mod_right]
    rw [hd_eq, hrem] at h0
    omega
  have hd2_eq : 2 * 2 ^ s + 2 ^ (s + 1) * (2 * K) = 2 * m + 2 := by nlinarith
  rw [hw_low, hw_high_split, hw_h0, hw_h1, zero_add, zero_add, hd2_eq] at hdvd2
  have hw_T : wrap m Tpoly ((2 ^ s : ℕ) : ℤ) = if s = 1 then 1 else 0 := by
    unfold Tpoly
    have h1 : (1 : Polynomial ℤ) = Polynomial.monomial 0 1 := by
      simp
    rw [h1, Polynomial.X_pow_eq_monomial, X_eq_mono1,
      wrap_add, wrap_add, wrap_monomial, wrap_monomial, wrap_monomial]
    have h2s_lt : 2 ^ s < m := by nlinarith
    have m0 : ((0 : ℕ) : ℤ) % (m : ℤ) ≠ ((2 ^ s : ℕ) : ℤ) % (m : ℤ) := by
      rw [Nat.cast_zero, Int.zero_emod, Int.emod_eq_of_lt (by omega) (by omega)]; omega
    have m1 : ((1 : ℕ) : ℤ) % (m : ℤ) ≠ ((2 ^ s : ℕ) : ℤ) % (m : ℤ) := by
      rw [Int.emod_eq_of_lt (by omega) (by omega), Int.emod_eq_of_lt (by omega) (by omega)]; omega
    rw [if_neg m0, if_neg m1, zero_add, zero_add]
    by_cases hs_one : s = 1
    · subst hs_one
      norm_num
    · have hs2 : 2 ≤ s := by omega
      have h4 : 4 ≤ 2 ^ s := le_trans (by decide : 4 ≤ 2 ^ 2) (Nat.pow_le_pow_right (by decide) hs2)
      have m2 : ((2 : ℕ) : ℤ) % (m : ℤ) ≠ ((2 ^ s : ℕ) : ℤ) % (m : ℤ) := by
        rw [Int.emod_eq_of_lt (by omega) (by omega), Int.emod_eq_of_lt (by omega) (by omega)]; omega
      rw [if_neg m2, if_neg hs_one]
  rw [hw_T, wrap_monomial] at hdvd2
  have h2m2_mod : ((2 * m + 2 : ℕ) : ℤ) % (m : ℤ) = 2 := by
    have hrew : ((2 * m + 2 : ℕ) : ℤ) = 2 + (m : ℤ) * 2 := by push_cast; ring
    rw [hrew, Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by omega) (by omega)]
  rw [h2m2_mod] at hdvd2
  by_cases hs_one : s = 1
  · subst hs_one
    have h2mod : ((2 ^ 1 : ℕ) : ℤ) % (m : ℤ) = 2 := by
      change (2 : ℤ) % (m : ℤ) = 2
      exact Int.emod_eq_of_lt (by omega) (by omega)
    rw [h2mod] at hdvd2
    simp at hdvd2
  · have hs2 : 2 ≤ s := by omega
    have h4 : 4 ≤ 2 ^ s := le_trans (by decide : 4 ≤ 2 ^ 2) (Nat.pow_le_pow_right (by decide) hs2)
    have h2s_lt : 2 ^ s < m := by nlinarith
    have hne : (2 : ℤ) ≠ ((2 ^ s : ℕ) : ℤ) % (m : ℤ) := by
      rw [Int.emod_eq_of_lt (by omega) (by omega)]; omega
    rw [if_neg hne, if_neg hs_one] at hdvd2
    norm_num at hdvd2

lemma strip_two : ∀ n : ℕ, 0 < n → ∃ v m : ℕ, 2 ^ v * m = n ∧ Odd m := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    by_cases hev : 2 ∣ n
    · rcases hev with ⟨y, rfl⟩
      rcases ih y (by omega) (by omega) with ⟨v, m, heq, hm⟩
      exact ⟨v + 1, m, by rw [pow_succ', mul_assoc, heq], hm⟩
    · exact ⟨0, n, by simp, Nat.odd_iff.mpr (by omega)⟩

lemma main_proof (n : ℕ) (hn : 3 ≤ n) (hper : period n = n) : InA115770 n := by
  have hne : {p : ℕ | 0 < p ∧ ∃ t : ℕ, row n (t + p) = row n t}.Nonempty := by
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty] at hempty
    unfold period at hper
    rw [hempty, Nat.sInf_empty] at hper
    omega
  have hn_mem : n ∈ {p : ℕ | 0 < p ∧ ∃ t : ℕ, row n (t + p) = row n t} := by
    have hs := Nat.sInf_mem hne
    change period n ∈ _ at hs
    rwa [hper] at hs
  rcases hn_mem.2 with ⟨t0, ht0⟩
  rcases strip_two n (by omega) with ⟨v, m, hvm, hodd_m⟩
  have hm1 : 1 ≤ m := by
    by_contra hm0
    have hmz : m = 0 := by omega
    subst hmz
    simp at hvm
    omega
  set t1 := max t0 (2 ^ v)
  have ht1_row : row n (t1 + n) = row n t1 := by
    obtain ⟨d, hd⟩ : ∃ d, t1 = t0 + d := ⟨t1 - t0, by omega⟩
    rw [hd]
    have ha : t0 + d + n = d + (t0 + n) := by omega
    have hb : t0 + d = d + t0 := by omega
    rw [ha, hb]
    unfold row at ht0 ⊢
    rw [Function.iterate_add_apply, ht0, ← Function.iterate_add_apply]
  have hcyc_n : ModCyc n (Tpoly ^ (t1 + n) - Polynomial.X ^ n * Tpoly ^ t1) :=
    (row_eq_iff_ModCyc (by omega) t1 n).mp ht1_row
  have hdvd_mn : m ∣ n := ⟨2 ^ v, by rw [mul_comm, hvm]⟩
  have hcyc_m0 : ModCyc m (Tpoly ^ (t1 + n) - Polynomial.X ^ n * Tpoly ^ t1) :=
    ModCyc_of_dvd hdvd_mn hcyc_n
  have hfactor : Tpoly ^ (t1 + n) - Polynomial.X ^ n * Tpoly ^ t1 =
      Tpoly ^ (2 ^ v + (t1 - 2 ^ v)) * (Tpoly ^ n - Polynomial.X ^ n) := by
    have ht1_eq : t1 = 2 ^ v + (t1 - 2 ^ v) := by
      have : 2 ^ v ≤ t1 := le_max_right _ _
      omega
    conv_lhs => rw [pow_add, ht1_eq]
    ring
  rw [hfactor] at hcyc_m0
  have h2v_pos : 1 ≤ 2 ^ v := Nat.one_le_pow v 2 (by decide)
  have hcyc_red := reduce_transient_ModCyc hm1 hodd_m (t1 - 2 ^ v) (2 ^ v)
    (Tpoly ^ n - Polynomial.X ^ n) h2v_pos hcyc_m0
  have hfresh : PolyMod2 ((Tpoly * (Tpoly ^ m - Polynomial.X ^ m)) ^ (2 ^ v))
      (Tpoly ^ (2 ^ v) * (Tpoly ^ n - Polynomial.X ^ n)) := by
    rw [mul_pow]
    have hp := PolyMod2_sub_two_pow (Tpoly ^ m) (Polynomial.X ^ m) v
    rw [← pow_mul, ← pow_mul, mul_comm m (2 ^ v), hvm] at hp
    exact PolyMod2_mul (PolyMod2_refl _) hp
  have hcyc_pow : ModCyc m ((Tpoly * (Tpoly ^ m - Polynomial.X ^ m)) ^ (2 ^ v)) := by
    have hd := ModCyc_of_PolyMod2 m hfresh
    have hs := ModCyc_add hd hcyc_red
    simpa using hs
  have hcyc_base := ModCyc_of_two_pow_odd hm1 hodd_m v hcyc_pow
  have hcyc_Tm : ModCyc m (Tpoly ^ (m + 1) - Tpoly) := by
    have hXm : ModCyc m ((Polynomial.X ^ m - 1) * Tpoly) := ⟨Tpoly, 0, by ring⟩
    have hsum := ModCyc_add hcyc_base hXm
    have heq : Tpoly * (Tpoly ^ m - Polynomial.X ^ m) + (Polynomial.X ^ m - 1) * Tpoly =
        Tpoly ^ (m + 1) - Tpoly := by
      rw [pow_succ']
      ring
    rwa [heq] at hsum
  rcases odd_mersenne_of_ModCyc hm1 hodd_m hcyc_Tm with ⟨k, hk1, hmk⟩
  by_cases hk3 : 3 ≤ k
  · rw [← hvm, hmk]
    exact inA115770_two_pow_mul (inA115770_mersenne hk3) v
  · exfalso
    have hk_cases : k = 1 ∨ k = 2 := by omega
    rcases hk_cases with rfl | rfl
    · norm_num at hmk
      subst hmk
      rw [mul_one] at hvm
      subst hvm
      have hv2 : 2 ≤ v := by
        by_contra hv1
        have : v = 0 ∨ v = 1 := by omega
        rcases this with rfl | rfl <;> omega
      exact not_period_two_pow hv2 hper
    · norm_num at hmk
      subst hmk
      rw [mul_comm] at hvm
      subst hvm
      exact not_period_three_mul_two_pow v hper

end A085588Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a085588.main :=
  A085588Proof.main_proof
