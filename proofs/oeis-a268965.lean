import OMAStatements.S_oeis_a268965
import Mathlib

/-!
# A268965 via the count for any number of complementary edges

For a fixed previous color and a fixed set of complementary positions,
each prescribed complementary successor has one choice and each other
successor has two choices. The proof below gives this binomial count for
every suffix length and every number of complementary edges. The last
part extracts the generating function coefficientwise.

Source: https://oeis.org/A268965
The proof of A268898 in PR #18518 (@dk8827) supplied the analogous
coefficientwise verification of its generating function.
-/

open PowerSeries
open OMA.S_oeis_a268965

private theorem count_formula (k : ℕ) (x : Color) (j : ℕ) :
    count k x j = k.choose j * 2 ^ (k - j) := by
  induction k generalizing x j with
  | zero => cases j <;> simp [count]
  | succ k ih =>
    cases j with
    | zero =>
      fin_cases x <;> rw [count] <;> norm_num [colors, ih, pow_succ] <;> omega
    | succ j =>
      have hshift : k.choose (j + 1) * 2 ^ (k - (j + 1)) * 2 =
          k.choose (j + 1) * 2 ^ (k - j) := by
        by_cases hj : j < k
        · have he : k - j = k - (j + 1) + 1 := by omega
          rw [he, pow_succ, Nat.mul_assoc]
        · rw [Nat.choose_eq_zero_of_lt (by omega : k < j + 1)]
          simp
      have hstep :
          k.choose j * 2 ^ (k - j) + 2 * (k.choose (j + 1) * 2 ^ (k - (j + 1))) =
            (k + 1).choose (j + 1) * 2 ^ ((k + 1) - (j + 1)) := by
        rw [Nat.choose_succ_succ, show k + 1 - (j + 1) = k - j by omega, Nat.add_mul]
        rw [← hshift]
        ring
      have he : k + 1 - (j + 1) = k - j := by omega
      rw [he] at hstep
      fin_cases x <;> rw [count] <;> norm_num [colors, ih]
      all_goals
        change _ = (k + 1).choose (j + 1) * 2 ^ (k - j)
        omega

private theorem closed (n : ℕ) : a (n + 1) = 4 ^ n * (6 * n + 9) := by
  rw [a]
  simp [colors, count_formula, pow_succ, pow_mul, show (2 : ℕ) ^ 2 = 4 by decide]
  ring

private theorem recurrence (n : ℕ) : a (n + 3) + 16 * a (n + 1) = 8 * a (n + 2) := by
  rw [show n + 3 = (n + 2) + 1 by omega, closed, closed, closed]
  simp only [pow_add]
  norm_num
  ring

theorem OMA.solution : type_of% @OMA.S_oeis_a268965.main := by
  refine ⟨recurrence, ?_, closed⟩
  let F : ℚ⟦X⟧ := PowerSeries.mk (fun n => (a n : ℚ))
  change (1 - 4 * X) ^ 2 * F = 3 * X * (3 - 4 * X)
  have h₁ : (1 - 4 * X) ^ 2 * F = F - C (8 : ℚ) * (X * F) +
      C (16 : ℚ) * (X * (X * F)) := by
    simp only [map_ofNat]
    ring
  have h₂ : (3 : ℚ⟦X⟧) * X * (3 - 4 * X) = C (9 : ℚ) * X - C (12 : ℚ) * X ^ 2 := by
    simp only [map_ofNat]
    ring
  rw [h₁, h₂]
  ext n
  have hC (c : ℚ) (S : ℚ⟦X⟧) (k : ℕ) := coeff_C_mul k S c
  rcases n with _ | _ | _ | n
  · norm_num [F, a, hC, coeff_X, coeff_X_pow]
  · norm_num [F, closed, show a 0 = 0 by rfl, hC, coeff_X, coeff_X_pow, coeff_succ_X_mul]
  · norm_num [F, closed, show a 0 = 0 by rfl, hC, coeff_X, coeff_X_pow, coeff_succ_X_mul]
  · change coeff (n + 3) _ = coeff (n + 3) _
    simp only [map_add, map_sub, hC, coeff_succ_X_mul, F, coeff_mk, coeff_X,
      coeff_X_pow, if_neg (show n + 3 ≠ 1 by omega), if_neg (show n + 3 ≠ 2 by omega),
      mul_zero, sub_zero]
    have hr := congrArg (fun k : ℕ => (k : ℚ)) (recurrence n)
    push_cast at hr
    linarith
