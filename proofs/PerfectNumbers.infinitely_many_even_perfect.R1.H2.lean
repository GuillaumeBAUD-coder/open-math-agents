import OMAReductions.R_PerfectNumbers_infinitely_many_even_perfect_R1
import Mathlib

-- Step PerfectNumbers.infinitely_many_even_perfect.R1.H2: hypothesis H2 of reduction PerfectNumbers.infinitely_many_even_perfect.R1
-- Credit: @ivillar; the proof of Euclid's theorem is taken from the Mathlib Archive, Archive/Wiedijk100Theorems/PerfectNumbers.lean (author Aaron Anderson, Apache 2.0): `sigma_two_pow_eq_mersenne_succ` and `perfect_two_pow_mul_mersenne_of_prime`.

/-!
Euclid's theorem on even perfect numbers. The proof is taken from the Mathlib Archive,
`Archive/Wiedijk100Theorems/PerfectNumbers.lean` (author: Aaron Anderson, Apache 2.0):
`sigma_two_pow_eq_mersenne_succ` and `perfect_two_pow_mul_mersenne_of_prime`.
-/
namespace F2Perf

open ArithmeticFunction Finset
open scoped sigma

theorem sigma_two_pow_eq_mersenne_succ (k : ℕ) : σ 1 (2 ^ k) = mersenne (k + 1) := by
  simp_rw [sigma_one_apply, mersenne, ← one_add_one_eq_two, ← geom_sum_mul_add 1 (k + 1)]
  norm_num

theorem euclid : ∀ k : ℕ, (mersenne (k + 1)).Prime → Nat.Perfect (2 ^ k * mersenne (k + 1)) := by
  intro k pr
  rw [Nat.perfect_iff_sum_divisors_eq_two_mul, ← mul_assoc, ← pow_succ', ← sigma_one_apply,
    mul_comm,
    isMultiplicative_sigma.map_mul_of_coprime ((Odd.coprime_two_right (by simp)).pow_right _),
    sigma_two_pow_eq_mersenne_succ]
  · simp [pr, sigma_one_apply]
  · positivity

end F2Perf

theorem OMA.solution : OMA.R_PerfectNumbers_infinitely_many_even_perfect_R1.H2 :=
  F2Perf.euclid
