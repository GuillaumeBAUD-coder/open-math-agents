import OMAStatements.S_oeis_a013302

namespace OMA.A013302

open PowerSeries OMA.S_oeis_a013302

private noncomputable def c (n : ℕ) : ℚ := coeff n invSqrt

private lemma c_eq_choose (n : ℕ) : c n = (-1 : ℚ) ^ n * Ring.choose (-1 / 2 : ℚ) n := by
  rw [c, invSqrt, coeff_rescale, binomialSeries_coeff, smul_eq_mul, mul_one]

private lemma c_zero : c 0 = 1 := by
  simp [c_eq_choose]

private lemma c_succ (n : ℕ) :
    2 * ((n : ℚ) + 1) * c (n + 1) = (2 * (n : ℚ) + 1) * c n := by
  have h := Ring.choose_smul_choose (-1 / 2 : ℚ) (Nat.le_succ n)
  rw [Nat.choose_succ_self_right, show n.succ - n = 1 by omega,
    Ring.choose_one_right, nsmul_eq_mul] at h
  push_cast at h
  rw [c_eq_choose, c_eq_choose, pow_succ]
  linear_combination (-2 * (-1 : ℚ) ^ n) * h

private noncomputable def oddFactorial (n : ℕ) : ℚ := (Nat.doubleFactorial (2 * n - 1) : ℚ)

private lemma oddFactorial_succ (n : ℕ) :
    oddFactorial (n + 1) = (2 * (n : ℚ) + 1) * oddFactorial n := by
  unfold oddFactorial
  rw [show 2 * (n + 1) - 1 = 2 * n + 1 by omega, Nat.doubleFactorial_add_one]
  push_cast
  rfl

private lemma even_factorial_succ (n : ℕ) :
    ((2 * (n + 1)).factorial : ℚ) =
      (2 * ((n : ℚ) + 1)) * (2 * (n : ℚ) + 1) * ((2 * n).factorial : ℚ) := by
  rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega, Nat.factorial_succ, Nat.factorial_succ]
  push_cast
  ring

private lemma factorial_mul_c (n : ℕ) : ((2 * n).factorial : ℚ) * c n = oddFactorial n ^ 2 := by
  induction n with
  | zero => norm_num [c_zero, oddFactorial, Nat.doubleFactorial]
  | succ n ih =>
    rw [even_factorial_succ, oddFactorial_succ, mul_pow, ← ih]
    linear_combination ((2 * (n : ℚ) + 1) * ((2 * n).factorial : ℚ)) * c_succ n

private lemma a_zero : a 0 = 1 := by
  simp only [a, sub_mul, one_mul, mul_assoc, map_sub, coeff_C_mul, coeff_zero_X_mul,
    mul_zero, sub_zero]
  change ((2 * 0).factorial : ℚ) * c 0 = 1
  norm_num [c_zero]

private lemma a_succ (n : ℕ) : a (n + 1) = (n : ℚ) * (2 * (n : ℚ) + 1) * oddFactorial n ^ 2 := by
  simp only [a, sub_mul, one_mul, mul_assoc, map_sub, coeff_C_mul, coeff_succ_X_mul]
  change ((2 * (n + 1)).factorial : ℚ) * (c (n + 1) - (1 / 2) * c n) = _
  rw [even_factorial_succ, ← factorial_mul_c]
  linear_combination ((2 * (n : ℚ) + 1) * ((2 * n).factorial : ℚ)) * c_succ n

private lemma first (n : ℕ) (hn : 2 ≤ n) :
    a n + 2 * (-2 * (n : ℚ)^2 + 2 * (n : ℚ) - 3) * a (n - 1)
      + 3 * (2 * (n : ℚ) - 3) * (2 * (n : ℚ) - 5) * a (n - 2) = 0 := by
  obtain rfl | hn := eq_or_lt_of_le hn
  · have h₁ := a_succ 0
    have h₂ := a_succ 1
    norm_num [a_zero, h₁, h₂, oddFactorial, Nat.doubleFactorial]
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k + 3 := ⟨n - 3, by omega⟩
  rw [show k + 3 - 1 = k + 2 by omega, show k + 3 - 2 = k + 1 by omega]
  rw [a_succ (k + 2), a_succ (k + 1), a_succ k, oddFactorial_succ (k + 1), oddFactorial_succ k]
  push_cast
  ring

private lemma second (n : ℕ) (hn : 1 ≤ n) :
    a n = (4 * (n : ℚ) - 5) * (Nat.doubleFactorial (2 * n - 3) : ℚ)^2
      + (2 * (n : ℚ) - 3)^2 * a (n - 1) := by
  obtain rfl | hn := eq_or_lt_of_le hn
  · have h₁ := a_succ 0
    norm_num [a_zero, h₁, Nat.doubleFactorial]
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k + 2 := ⟨n - 2, by omega⟩
  rw [show k + 2 - 1 = k + 1 by omega, show 2 * (k + 2) - 3 = 2 * (k + 1) - 1 by omega]
  rw [a_succ (k + 1), a_succ k]
  change _ = (4 * ((k + 2 : ℕ) : ℚ) - 5) * oddFactorial (k + 1)^2 + _
  rw [oddFactorial_succ k]
  push_cast
  ring

end OMA.A013302

theorem OMA.solution : type_of% @OMA.S_oeis_a013302.main :=
  ⟨OMA.A013302.first, OMA.A013302.second⟩
