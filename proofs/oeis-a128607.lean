import OMAStatements.S_oeis_a128607
import Mathlib.Tactic.NormNum.Prime

/-! Two further perfect powers whose divisor sums are perfect powers. -/
-- Credit: @STARDUSTLC666

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace DivisorSumWitnesses

private lemma sigma_square {p : ℕ} (hp : p.Prime) :
    σ 1 (p ^ 2) = 1 + p + p ^ 2 := by
  rw [sigma_one_apply_prime_pow hp]
  simp [Finset.sum_range_succ]

private lemma sigma_cube {p : ℕ} (hp : p.Prime) :
    σ 1 (p ^ 3) = 1 + p + p ^ 2 + p ^ 3 := by
  rw [sigma_one_apply_prime_pow hp]
  simp [Finset.sum_range_succ]

private lemma split_power (a p e : ℕ) (h : a.Coprime p) :
    σ 1 ((a * p) ^ e) = σ 1 (a ^ e) * σ 1 (p ^ e) := by
  rw [mul_pow]
  exact isMultiplicative_sigma.map_mul_of_coprime ((h.pow_left e).pow_right e)

private lemma cube_to_square :
    σ 1 ((17 * 31 * 47 * 191) ^ 3) = 10927088640 ^ 2 := by
  rw [split_power (17 * 31 * 47) 191 3 (by decide),
    split_power (17 * 31) 47 3 (by decide), split_power 17 31 3 (by decide),
    sigma_cube (p := 17) (by norm_num), sigma_cube (p := 31) (by norm_num),
    sigma_cube (p := 47) (by norm_num), sigma_cube (p := 191) (by norm_num)]
  decide

private lemma square_to_cube :
    σ 1 ((3 * 5 * 37 * 163 * 439 * 653) ^ 2) = 10773399 ^ 3 := by
  rw [split_power (3 * 5 * 37 * 163 * 439) 653 2 (by decide),
    split_power (3 * 5 * 37 * 163) 439 2 (by decide),
    split_power (3 * 5 * 37) 163 2 (by decide), split_power (3 * 5) 37 2 (by decide),
    split_power 3 5 2 (by decide), sigma_square (p := 3) (by norm_num),
    sigma_square (p := 5) (by norm_num), sigma_square (p := 37) (by norm_num),
    sigma_square (p := 163) (by norm_num), sigma_square (p := 439) (by norm_num),
    sigma_square (p := 653) (by norm_num)]
  decide

end DivisorSumWitnesses

open DivisorSumWitnesses

theorem OMA.solution : type_of% @OMA.S_oeis_a128607.main := by
  constructor
  · refine ⟨(17 * 31 * 47 * 191) ^ 3, by decide, by decide,
      ⟨17 * 31 * 47 * 191, 3, by decide, by decide, rfl⟩, ?_⟩
    exact ⟨10927088640, 2, by decide, by decide, cube_to_square.symm⟩
  · refine ⟨(3 * 5 * 37 * 163 * 439 * 653) ^ 2, by decide,
      ⟨3 * 5 * 37 * 163 * 439 * 653, 2, by decide, by decide, rfl⟩, ?_⟩
    exact ⟨10773399, 3, by decide, by decide, square_to_cube.symm⟩
