import OMAReductions.R_Erdos1109_erdos_1109_variants_konyagin_upper_R1_H1_R1_H2_R1_H1_R1_H1_R1
import Mathlib

namespace OMA.DivBound

open Finset

def W (k n : ℕ) : ℕ := ∏ p ∈ n.primeFactors, (if p < 2 ^ k then k ^ k else 1)

lemma pow_le (k : ℕ) (hk : 0 < k) (a : ℕ) : (a + 1) ^ k ≤ k ^ k * 2 ^ a := by
  have h1 : a + 1 ≤ k * (a / k + 1) := Nat.lt_mul_div_succ a hk
  have h2 : a / k + 1 ≤ 2 ^ (a / k) := Nat.lt_two_pow_self
  calc (a + 1) ^ k ≤ (k * 2 ^ (a / k)) ^ k :=
        Nat.pow_le_pow_left (h1.trans (Nat.mul_le_mul_left k h2)) k
    _ = k ^ k * 2 ^ (a / k * k) := by rw [mul_pow, ← pow_mul]
    _ ≤ k ^ k * 2 ^ a :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (Nat.div_mul_le_self a k))

lemma key (k : ℕ) (hk : 0 < k) (n : ℕ) : n.divisors.card ^ k ≤ W k n * n := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | zero => simp [hk.ne']
  | one => simp [W]
  | prime_pow p a hp ha =>
    have hw : W k (p ^ a) = if p < 2 ^ k then k ^ k else 1 := by
      simp [W, Nat.primeFactors_prime_pow ha.ne' hp]
    rw [hw, Nat.divisors_prime_pow hp, Finset.card_map, Finset.card_range]
    split_ifs with h8
    · calc (a + 1) ^ k ≤ k ^ k * 2 ^ a := pow_le k hk a
        _ ≤ k ^ k * p ^ a := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hp.two_le a)
    · have h8' : 2 ^ k ≤ p := by omega
      have h1 : a + 1 ≤ 2 ^ a := Nat.lt_two_pow_self
      calc (a + 1) ^ k ≤ (2 ^ a) ^ k := Nat.pow_le_pow_left h1 k
        _ = (2 ^ k) ^ a := by rw [← pow_mul, mul_comm, pow_mul]
        _ ≤ p ^ a := Nat.pow_le_pow_left h8' a
        _ = 1 * p ^ a := (one_mul _).symm
  | coprime m n hm hn hmn ihm ihn =>
    have hw : W k (m * n) = W k m * W k n := by
      unfold W
      rw [hmn.primeFactors_mul, Finset.prod_union hmn.disjoint_primeFactors]
    rw [hw, hmn.card_divisors_mul, mul_pow]
    calc m.divisors.card ^ k * n.divisors.card ^ k ≤ (W k m * m) * (W k n * n) :=
          Nat.mul_le_mul ihm ihn
      _ = W k m * W k n * (m * n) := by ring

lemma W_le (k : ℕ) (hk : 0 < k) (n : ℕ) : W k n ≤ (k ^ k) ^ (2 ^ k) := by
  unfold W
  rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
  apply Nat.pow_le_pow_right (Nat.pow_pos hk)
  calc (n.primeFactors.filter (fun p => p < 2 ^ k)).card ≤ (Finset.range (2 ^ k)).card := by
        apply Finset.card_le_card
        intro p hp
        simp only [Finset.mem_filter] at hp
        exact Finset.mem_range.mpr hp.2
    _ = 2 ^ k := Finset.card_range _

end OMA.DivBound

open OMA.DivBound in
theorem OMA.solution : OMA.R_Erdos1109_erdos_1109_variants_konyagin_upper_R1_H1_R1_H2_R1_H1_R1_H1_R1.H2 := by
  intro ε hε
  set k : ℕ := ⌈18 / ε⌉₊ + 1 with hkdef
  have hk : 0 < k := Nat.succ_pos _
  have hkε : (3 : ℝ) ≤ ε / 6 * k := by
    have h1 : 18 / ε ≤ (⌈18 / ε⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (k : ℝ) = (⌈18 / ε⌉₊ : ℝ) + 1 := by rw [hkdef]; push_cast; ring
    have h3 : 18 / ε ≤ (k : ℝ) := by linarith
    have h4 : 18 ≤ (k : ℝ) * ε := by
      rw [div_le_iff₀ hε] at h3
      exact h3
    nlinarith [h4]
  filter_upwards [Filter.eventually_ge_atTop ((k ^ k) ^ (2 ^ k) + 1)] with N hN m hm
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have h1 : m.divisors.card ^ k ≤ N ^ 3 := by
    calc m.divisors.card ^ k ≤ W k m * m := key k hk m
      _ ≤ N * N ^ 2 := Nat.mul_le_mul ((W_le k hk m).trans (by omega)) hm
      _ = N ^ 3 := by ring
  have h2 : ((m.divisors.card : ℝ)) ^ k ≤ (N : ℝ) ^ (3 : ℝ) := by
    have : ((m.divisors.card : ℝ)) ^ k ≤ (N : ℝ) ^ (3 : ℕ) := by exact_mod_cast h1
    rwa [← Real.rpow_natCast (N : ℝ) 3] at this
  have h3 : (N : ℝ) ^ (3 : ℝ) ≤ (N : ℝ) ^ (ε / 6 * k) :=
    Real.rpow_le_rpow_of_exponent_le hN1 hkε
  have h4 : (N : ℝ) ^ (ε / 6 * k) = ((N : ℝ) ^ (ε / 6)) ^ k := by
    rw [Real.rpow_mul (by linarith), Real.rpow_natCast]
  have h5 : ((m.divisors.card : ℝ)) ^ k ≤ ((N : ℝ) ^ (ε / 6)) ^ k := by
    rw [← h4]; exact h2.trans h3
  exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) hk.ne').mp h5
