import OMAStatements.S_oeis_a008287

open Polynomial

-- Choosing the term -2X(1+X) exactly j times leaves j + 3(n-j)
-- factors of (1+X), as well as the factor X^j.
private theorem quadrinomial_expansion (n : ℕ) :
    (1 + X + X ^ 2 + X ^ 3 : ℤ[X]) ^ n =
      ∑ j ∈ Finset.range (n + 1),
        C ((-2 : ℤ) ^ j * n.choose j) * (1 + X) ^ (3 * n - 2 * j) * X ^ j := by
  have factor : (1 + X + X ^ 2 + X ^ 3 : ℤ[X]) =
      -2 * X * (1 + X) + (1 + X) ^ 3 := by ring
  rw [factor, add_pow]
  apply Finset.sum_congr rfl
  intro j hj
  have hjn : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have hexp : 3 * n - 2 * j = j + 3 * (n - j) := by omega
  simp only [hexp, pow_add, pow_mul, mul_pow, C_mul, C_pow, C_eq_natCast, map_neg, map_ofNat]
  ring

theorem OMA.solution : type_of% @OMA.S_oeis_a008287.main := by
  intro n k _
  rw [OMA.S_oeis_a008287.T, quadrinomial_expansion, finsetSum_coeff]
  apply Finset.sum_congr_of_eq_on_inter
  · intro j _ hj
    have h : ¬ j ≤ k := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hj
    rw [coeff_mul_X_pow', if_neg h]
  · intro j _ hj
    have h : n < j := by simpa only [Finset.mem_range, Nat.lt_succ_iff, not_le] using hj
    simp [Nat.choose_eq_zero_of_lt h]
  · intro j _ hj
    have h : j ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    rw [coeff_mul_X_pow', if_pos h, coeff_C_mul, coeff_one_add_X_pow]
