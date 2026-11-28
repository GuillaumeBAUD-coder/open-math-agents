import OMAStatements.S_oeis_a268898

-- Credit: @dk8827
-- Every color has one complementary successor and two other successors.

open PowerSeries
open OMA.S_oeis_a268898

private lemma countZero (n : ℕ) (x : Color) : count n x 0 = 2 ^ n := by
  induction n generalizing x with
  | zero => simp [count]
  | succ n ih =>
    fin_cases x <;> rw [count] <;> norm_num [colors, ih, pow_succ] <;> (try simp) <;> omega

private lemma countOne (n : ℕ) (x : Color) : count (n + 1) x 1 = (n + 1) * 2 ^ n := by
  induction n generalizing x with
  | zero => fin_cases x <;> decide
  | succ n ih =>
    fin_cases x <;> rw [count] <;> norm_num [colors, countZero, ih, pow_succ] <;> (try simp) <;> ring

private lemma closed (n : ℕ) : a (n + 1) = 4 ^ n * (6 * n + 3) := by
  rw [a]
  simp [colors, countOne, pow_mul, show (2 : ℕ) ^ 2 = 4 by decide]
  ring

private lemma recurrence (n : ℕ) : a (n + 3) + 16 * a (n + 1) = 8 * a (n + 2) := by
  rw [show n + 3 = (n + 2) + 1 by omega, closed, closed, closed]
  simp only [pow_add]
  norm_num
  ring

theorem OMA.solution : type_of% @OMA.S_oeis_a268898.main := by
  refine ⟨recurrence, ?_, closed⟩
  let F : ℚ⟦X⟧ := PowerSeries.mk (fun n => (a n : ℚ))
  change (1 - 4 * X) ^ 2 * F = 3 * X * (1 + 4 * X)
  have h₁ : (1 - 4 * X) ^ 2 * F = F - C (8 : ℚ) * (X * F) +
      C (16 : ℚ) * (X * (X * F)) := by
    simp only [map_ofNat]
    ring
  have h₂ : (3 : ℚ⟦X⟧) * X * (1 + 4 * X) = C (3 : ℚ) * X + C (12 : ℚ) * X ^ 2 := by
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
      coeff_X_pow, show n + 3 ≠ 1 by omega, show n + 3 ≠ 2 by omega, if_false,
      mul_zero, add_zero]
    have hr := congrArg (fun k : ℕ => (k : ℚ)) (recurrence n)
    push_cast at hr
    linarith
