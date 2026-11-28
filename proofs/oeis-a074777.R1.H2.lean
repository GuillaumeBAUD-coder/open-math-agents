import OMAReductions.R_oeis_a074777_R1
import Mathlib

-- Step oeis-a074777.R1.H2: hypothesis H2 of reduction oeis-a074777.R1
-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Sketch: phi(n) = 2^k via Nat.totient_mul on coprime factors 30*17*257*65537 and
-- Nat.totient_prime for the Fermat primes; sigma 1 (2^k) = 2^(k+1) - 1 by the geometric sum;
-- then 2 * (2^(k+1) - 1) = n by norm_num. Small cases by decide.

namespace A074777H2
open ArithmeticFunction

lemma sigma_two_pow (k : ℕ) : sigma 1 (2 ^ k) = 2 ^ (k + 1) - 1 := by
  rw [sigma_one_apply_prime_pow Nat.prime_two, Nat.geomSum_eq (le_refl 2)]
  simp

lemma p257 : Nat.Prime 257 := by norm_num
lemma p65537 : Nat.Prime 65537 := by norm_num

lemma t257 : Nat.totient 257 = 2 ^ 8 := by rw [Nat.totient_prime p257]; norm_num
lemma t65537 : Nat.totient 65537 = 2 ^ 16 := by rw [Nat.totient_prime p65537]; norm_num
lemma t17 : Nat.totient 17 = 2 ^ 4 := by rw [Nat.totient_prime (by norm_num)]; norm_num
lemma t30 : Nat.totient 30 = 2 ^ 3 := by decide

lemma t510 : Nat.totient 510 = 2 ^ 7 := by
  rw [show (510 : ℕ) = 30 * 17 by norm_num, Nat.totient_mul (by norm_num), t30, t17]
  norm_num
lemma t131070 : Nat.totient 131070 = 2 ^ 15 := by
  rw [show (131070 : ℕ) = 510 * 257 by norm_num, Nat.totient_mul (by norm_num), t510, t257]
  norm_num
lemma t8589934590 : Nat.totient 8589934590 = 2 ^ 31 := by
  rw [show (8589934590 : ℕ) = 131070 * 65537 by norm_num, Nat.totient_mul (by norm_num),
    t131070, t65537]
  norm_num

theorem H2_proof : OMA.R_oeis_a074777_R1.H2 := by
  intro n hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl
  · decide
  · decide
  · decide
  · rw [t510, sigma_two_pow]; norm_num
  · rw [t131070, sigma_two_pow]; norm_num
  · rw [t8589934590, sigma_two_pow]; norm_num

end A074777H2

theorem OMA.solution : OMA.R_oeis_a074777_R1.H2 := A074777H2.H2_proof
