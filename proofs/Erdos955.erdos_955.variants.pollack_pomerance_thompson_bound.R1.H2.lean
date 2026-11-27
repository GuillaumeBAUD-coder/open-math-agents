import OMAReductions.R_Erdos955_erdos_955_variants_pollack_pomerance_thompson_bound_R1
import Mathlib

/-! The elementary bound sigma(n) <= n (1 + log n). Pairing each divisor d with n / d gives
sigma(n) = sum of n / d over the divisors d of n, which is at most n times the harmonic number
H_n, and H_n <= 1 + log n. -/

theorem OMA.solution :
    OMA.R_Erdos955_erdos_955_variants_pollack_pomerance_thompson_bound_R1.H2 := by
  unfold OMA.R_Erdos955_erdos_955_variants_pollack_pomerance_thompson_bound_R1.H2
  intro n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have h1 : (ArithmeticFunction.sigma 1 n : ℝ) = ∑ d ∈ n.divisors, (n : ℝ) / d := by
    rw [ArithmeticFunction.sigma_one_apply, Nat.cast_sum,
      ← Nat.sum_div_divisors n (fun d => (d : ℝ))]
    apply Finset.sum_congr rfl
    intro d hd
    rw [Nat.cast_div (Nat.dvd_of_mem_divisors hd)
      (Nat.cast_ne_zero.mpr (Nat.pos_of_mem_divisors hd).ne')]
  have h2 : ∑ d ∈ n.divisors, (n : ℝ) / d ≤ ∑ d ∈ Finset.Icc 1 n, (n : ℝ) / d := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro d hd
      rw [Finset.mem_Icc]
      exact ⟨Nat.pos_of_mem_divisors hd, Nat.divisor_le hd⟩
    · intro d _ _
      positivity
  have h3 : ∑ d ∈ Finset.Icc 1 n, (n : ℝ) / d = n * ((harmonic n : ℚ) : ℝ) := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d _
    rw [div_eq_mul_inv]
  have h4 : ((harmonic n : ℚ) : ℝ) ≤ 1 + Real.log n := harmonic_le_one_add_log n
  rw [h1]
  exact (h2.trans_eq h3).trans (mul_le_mul_of_nonneg_left h4 hnpos.le)
