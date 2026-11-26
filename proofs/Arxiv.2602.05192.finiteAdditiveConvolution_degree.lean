import FormalConjectures.Arxiv.«2602.05192».FirstProof4

-- Credit: @daniel-inderos
-- Agent: hermes
-- Model: gpt-6.1-sol
-- The top coefficient is the product of the two original top coefficients.
-- Every other summand has strictly smaller exponent.

open Polynomial Finset
open scoped Nat
open Arxiv.«2602.05192»

theorem OMA.solution : type_of% @Arxiv.«2602.05192».finiteAdditiveConvolution_degree := by
  intro n p q hp hq
  classical
  have hp0 : p ≠ 0 := by
    intro h
    simp [h] at hp
  have hq0 : q ≠ 0 := by
    intro h
    simp [h] at hq
  have hpc : p.coeff n ≠ 0 := by
    rw [← natDegree_eq_of_degree_eq_some hp, coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr hp0
  have hqc : q.coeff n ≠ 0 := by
    rw [← natDegree_eq_of_degree_eq_some hq, coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr hq0
  have hfac : (n ! : ℝ) ≠ 0 := by positivity
  have htop : (finiteAdditiveConvolution n p q).coeff n = p.coeff n * q.coeff n := by
    simp only [finiteAdditiveConvolution]
    rw [Polynomial.finsetSum_coeff]
    conv_lhs =>
      arg 2
      ext k
      rw [Polynomial.coeff_smul, Polynomial.coeff_X_pow]
    simp only [smul_eq_mul]
    rw [Finset.sum_eq_single 0]
    · simp [Finset.Nat.antidiagonal_zero, hfac]
    · intro k hk hk0
      have hk' : k < n + 1 := Finset.mem_range.mp hk
      have hnk : n ≠ n - k := by omega
      simp [hnk]
    · intro h
      exact absurd (Finset.mem_range.mpr (by omega)) h
  have hbound : (finiteAdditiveConvolution n p q).natDegree ≤ n := by
    simp only [finiteAdditiveConvolution]
    apply (Polynomial.natDegree_sum_le _ _).trans
    apply Finset.sup_le
    intro k hk
    apply (Polynomial.natDegree_smul_le _ _).trans
    exact (Polynomial.natDegree_X_pow_le (n - k)).trans (Nat.sub_le n k)
  apply Polynomial.degree_eq_of_le_of_coeff_ne_zero
    (Polynomial.natDegree_le_iff_degree_le.mp hbound)
  rw [htop]
  exact mul_ne_zero hpc hqc
