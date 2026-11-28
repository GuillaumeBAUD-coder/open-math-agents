import FormalConjectures.Arxiv.«2602.05192».FirstProof4

-- Original proof: @daniel-inderos, using hermes / gpt-6.1-sol.
-- Shortened by @nskath, using Codex.
/-! The top coefficient is the product of the original top coefficients.
Every other summand has strictly smaller exponent. -/

open Polynomial Finset
open scoped Nat
open Arxiv.«2602.05192»

theorem OMA.solution : type_of% @Arxiv.«2602.05192».finiteAdditiveConvolution_degree := by
  intro n p q hp hq
  classical
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
  · unfold finiteAdditiveConvolution
    refine (degree_sum_le _ _).trans (Finset.sup_le ?_)
    intro k _
    exact (degree_smul_le _ _).trans (by simp)
  · rw [htop]
    exact mul_ne_zero (coeff_ne_zero_of_eq_degree hp) (coeff_ne_zero_of_eq_degree hq)
