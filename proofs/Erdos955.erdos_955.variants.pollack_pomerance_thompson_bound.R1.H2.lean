import OMAReductions.R_Erdos955_erdos_955_variants_pollack_pomerance_thompson_bound_R1
import Mathlib

/-! sigma(n) = sum over d | n of n/d <= n * H_n <= n (1 + log n) (harmonic_le_one_add_log). -/

theorem OMA.solution : OMA.R_Erdos955_erdos_955_variants_pollack_pomerance_thompson_bound_R1.H2 := by
  intro n hn
  have hσ : (ArithmeticFunction.sigma 1 n : ℝ) = ∑ d ∈ n.divisors, ((n : ℝ) / d) := by
    rw [ArithmeticFunction.sigma_one_apply, ← Nat.sum_div_divisors n (fun d => d)]
    push_cast
    refine Finset.sum_congr rfl fun d hd => ?_
    have hd0 : (d : ℝ) ≠ 0 := by
      have := Nat.pos_of_mem_divisors hd
      positivity
    rw [Nat.cast_div (Nat.dvd_of_mem_divisors hd) hd0]
  have hsub : ∑ d ∈ n.divisors, ((n : ℝ) / d) ≤ ∑ d ∈ Finset.Icc 1 n, ((n : ℝ) / d) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro d hd
      rw [Finset.mem_Icc]
      exact ⟨Nat.pos_of_mem_divisors hd, Nat.divisor_le hd⟩
    · intro i _ _
      positivity
  have hharm : ∑ d ∈ Finset.Icc 1 n, ((n : ℝ) / d) = n * (harmonic n : ℝ) := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [div_eq_mul_inv]
  have hlog := harmonic_le_one_add_log n
  have hn0 : (0 : ℝ) ≤ n := by positivity
  rw [hσ]
  calc ∑ d ∈ n.divisors, ((n : ℝ) / d) ≤ n * (harmonic n : ℝ) := hsub.trans hharm.le
    _ ≤ n * (1 + Real.log n) := mul_le_mul_of_nonneg_left hlog hn0
