import FormalConjectures.Arxiv.«2602.05192».FirstProof4

-- Credit: @daniel-inderos
-- Agent: hermes
-- Model: gpt-6.1-sol
/-! The top coefficient is the product of the original top coefficients.
Every other summand has strictly smaller exponent. -/

open Polynomial Finset
open scoped Nat
open Arxiv.«2602.05192»

theorem OMA.solution : type_of% @Arxiv.«2602.05192».finiteAdditiveConvolution_degree := by
  intro n p q hp hq
  classical
  have topCoeff (r : ℝ[X]) (hr : r.degree = n) : r.coeff n ≠ 0 := by
    rw [← natDegree_eq_of_degree_eq_some hr, coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr (by rintro rfl; simp at hr)
  have htop : (finiteAdditiveConvolution n p q).coeff n = p.coeff n * q.coeff n := by
    simp only [finiteAdditiveConvolution, Polynomial.finsetSum_coeff,
      Polynomial.coeff_smul, Polynomial.coeff_X_pow, smul_eq_mul]
    rw [Finset.sum_eq_single 0]
    · simp [show (n ! : ℝ) ≠ 0 by positivity]
    · intro k hk hk0
      have hk' := Finset.mem_range.mp hk
      simp [show n ≠ n - k by omega]
    · simp
  apply Polynomial.degree_eq_of_le_of_coeff_ne_zero
  · apply Polynomial.natDegree_le_iff_degree_le.mp
    unfold finiteAdditiveConvolution
    refine (Polynomial.natDegree_sum_le _ _).trans (Finset.sup_le ?_)
    exact fun k _ => (Polynomial.natDegree_smul_le _ _).trans
      ((Polynomial.natDegree_X_pow_le _).trans (Nat.sub_le n k))
  · rw [htop]
    exact mul_ne_zero (topCoeff p hp) (topCoeff q hq)
