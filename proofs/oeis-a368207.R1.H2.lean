import OMAReductions.R_oeis_a368207_R1
import Mathlib

namespace OMA.A368207H2

open Finset

def w (n : ℕ) : ℕ := ∏ p ∈ n.primeFactors, (if p < 8 then 8 else 1)

lemma cube_le (a : ℕ) : (a + 1) ^ 3 ≤ 8 * 2 ^ a := by
  have h : ∀ b : ℕ, (b + 4) ^ 3 ≤ 8 * 2 ^ (b + 3) := by
    intro b
    induction b with
    | zero => norm_num
    | succ b ih =>
      have : (b + 1 + 4) ^ 3 ≤ 2 * (b + 4) ^ 3 := by
        nlinarith [sq_nonneg b, Nat.zero_le b, Nat.zero_le (b ^ 3), Nat.zero_le (b ^ 2)]
      calc (b + 1 + 4) ^ 3 ≤ 2 * (b + 4) ^ 3 := this
        _ ≤ 2 * (8 * 2 ^ (b + 3)) := by omega
        _ = 8 * 2 ^ (b + 1 + 3) := by ring
  rcases a with _ | _ | _ | a
  · norm_num
  · norm_num
  · norm_num
  · exact h a

lemma key (n : ℕ) : n.divisors.card ^ 3 ≤ w n * n := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | zero => simp
  | one => simp [w]
  | prime_pow p a hp ha =>
    have hw : w (p ^ a) = if p < 8 then 8 else 1 := by
      simp [w, Nat.primeFactors_prime_pow ha.ne' hp]
    rw [hw, Nat.divisors_prime_pow hp, Finset.card_map, Finset.card_range]
    split_ifs with h8
    · calc (a + 1) ^ 3 ≤ 8 * 2 ^ a := cube_le a
        _ ≤ 8 * p ^ a := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hp.two_le a)
    · have h8' : 8 ≤ p := by omega
      have h1 : a + 1 ≤ 2 ^ a := Nat.lt_two_pow_self
      calc (a + 1) ^ 3 ≤ (2 ^ a) ^ 3 := Nat.pow_le_pow_left h1 3
        _ = 8 ^ a := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
        _ ≤ p ^ a := Nat.pow_le_pow_left h8' a
        _ = 1 * p ^ a := (one_mul _).symm
  | coprime m n hm hn hmn ihm ihn =>
    have hw : w (m * n) = w m * w n := by
      unfold w
      rw [hmn.primeFactors_mul, Finset.prod_union hmn.disjoint_primeFactors]
    rw [hw, hmn.card_divisors_mul, mul_pow]
    calc m.divisors.card ^ 3 * n.divisors.card ^ 3 ≤ (w m * m) * (w n * n) :=
          Nat.mul_le_mul ihm ihn
      _ = w m * w n * (m * n) := by ring

lemma w_le (n : ℕ) : w n ≤ 8 ^ 8 := by
  unfold w
  rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
  apply Nat.pow_le_pow_right (by norm_num)
  calc (n.primeFactors.filter (fun p => p < 8)).card ≤ (Finset.range 8).card := by
        apply Finset.card_le_card
        intro p hp
        simp only [Finset.mem_filter] at hp
        exact Finset.mem_range.mpr hp.2
    _ = 8 := Finset.card_range 8

end OMA.A368207H2

open OMA.A368207H2 in
theorem OMA.solution : OMA.R_oeis_a368207_R1.H2 := by
  unfold OMA.R_oeis_a368207_R1.H2
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt ((8 : ℝ) ^ 16 / ε ^ 6)
  refine ⟨N + 1, fun n hn => ?_⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hnN : (N : ℝ) < n := by exact_mod_cast (by omega : N < n)
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)]
  by_contra hcon
  push_neg at hcon
  have hd : ((n.divisors.card : ℝ)) ^ 3 ≤ 8 ^ 8 * n := by
    have h1 := key n
    have h2 := Nat.mul_le_mul_right n (w_le n)
    exact_mod_cast h1.trans h2
  have hd0 : (0 : ℝ) ≤ (n.divisors.card : ℝ) ^ 3 := by positivity
  have h6 : ((n.divisors.card : ℝ)) ^ 6 ≤ 8 ^ 16 * (n : ℝ) ^ 2 := by
    have := mul_le_mul hd hd hd0 (by positivity)
    nlinarith [this]
  have hsq : Real.sqrt n ^ 6 = (n : ℝ) ^ 3 := by
    have := Real.sq_sqrt hn0.le
    calc Real.sqrt n ^ 6 = (Real.sqrt n ^ 2) ^ 3 := by ring
      _ = (n : ℝ) ^ 3 := by rw [this]
  have h7 : ε ^ 6 ≤ ((n.divisors.card : ℝ) / Real.sqrt n) ^ 6 := pow_le_pow_left₀ hε.le hcon 6
  rw [div_pow, hsq, le_div_iff₀ (by positivity)] at h7
  have h8 : ε ^ 6 * (n : ℝ) ≤ 8 ^ 16 := by
    have h9 : ε ^ 6 * (n : ℝ) ^ 3 ≤ 8 ^ 16 * (n : ℝ) ^ 2 := h7.trans h6
    have h10 : (ε ^ 6 * (n : ℝ)) * (n : ℝ) ^ 2 ≤ 8 ^ 16 * (n : ℝ) ^ 2 := by nlinarith [h9]
    exact le_of_mul_le_mul_right h10 (by positivity)
  have h11 : (8 : ℝ) ^ 16 / ε ^ 6 < n := hN.trans hnN
  rw [div_lt_iff₀ (by positivity)] at h11
  nlinarith [h11, h8]
