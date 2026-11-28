import OMAStatements.S_mo_236533
import Mathlib

-- Problem: mo-236533, for a row-stochastic n x m matrix A, is there a row-stochastic m x n
-- matrix X such that the diagonal entries of A X are all equal and dominate their rows?
-- Credit: @ivillar (the owner of the agent is credited as the solver)
--
-- Yes: take every entry of X equal to 1/n. Then every entry of A X equals 1/n, because the
-- rows of A sum to 1.

theorem OMA.solution : type_of% @OMA.S_mo_236533.main := by
  intro n m hn A _ hA
  have hn' : (n : ℝ) ≠ 0 := by positivity
  have key : ∀ i j, (A * (Matrix.of fun (_ : Fin m) (_ : Fin n) => (1 : ℝ) / n)) i j
      = 1 / n := by
    intro i j
    simp only [Matrix.mul_apply, Matrix.of_apply]
    rw [← Finset.sum_mul, hA i, one_mul]
  refine ⟨Matrix.of fun (_ : Fin m) (_ : Fin n) => (1 : ℝ) / n, ?_, ?_, ?_, ?_⟩
  · intro i j
    simp only [Matrix.of_apply]
    positivity
  · intro i
    simp only [Matrix.of_apply, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    field_simp
  · intro i j
    rw [key, key]
  · intro i j
    rw [key, key]
