import OMAStatements.S_oeis_a147817

-- Problem: A147817
-- Upstream: formal-conjectures statements/oeis-a147817.lean:0 (declaration OMA.S_oeis_a147817.main)
-- Credit: @nigelcarreiro-blip (the owner of the agent is credited as the solver)

/-! 24 a(n) = n (n-1) (n-2) (n-3) (n^4 + 2n^3 - 5n^2 - 22n - 30) is a polynomial of degree 8, so its
ninth differences vanish, which is the recurrence. Multiplying the g.f. by (1 - x)^9 takes ninth
differences, so only the coefficients of degree below 9 remain; they are computed directly. -/

namespace A147817Aux

open OMA.S_oeis_a147817 PowerSeries

theorem c2 (n : ℕ) : 2 * (n.choose 2 : ℤ) = n * (n - 1) := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Nat.choose_succ_succ', Nat.choose_one_right]
    push_cast
    linear_combination ih

theorem c3 (n : ℕ) : 6 * (n.choose 3 : ℤ) = n * (n - 1) * (n - 2) := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Nat.choose_succ_succ']
    push_cast
    linear_combination ih + 3 * c2 k

theorem c4 (n : ℕ) : 24 * (n.choose 4 : ℤ) = n * (n - 1) * (n - 2) * (n - 3) := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Nat.choose_succ_succ']
    push_cast
    linear_combination ih + 4 * c3 k

theorem a24 (n : ℕ) : 24 * a n =
    n * (n - 1) * (n - 2) * (n - 3) * (n ^ 4 + 2 * n ^ 3 - 5 * n ^ 2 - 22 * n - 30) := by
  simp only [a]
  linear_combination ((n : ℤ) ^ 4 + 2 * n ^ 3 - 5 * n ^ 2 - 22 * n - 30) * c4 n

theorem rec9 (m : ℕ) : a (m + 9) = 9 * a (m + 8) - 36 * a (m + 7) + 84 * a (m + 6)
    - 126 * a (m + 5) + 126 * a (m + 4) - 84 * a (m + 3) + 36 * a (m + 2) - 9 * a (m + 1)
    + a m := by
  apply mul_left_cancel₀ (show (24 : ℤ) ≠ 0 by norm_num)
  have h9 := a24 (m + 9)
  have h8 := a24 (m + 8)
  have h7 := a24 (m + 7)
  have h6 := a24 (m + 6)
  have h5 := a24 (m + 5)
  have h4 := a24 (m + 4)
  have h3 := a24 (m + 3)
  have h2 := a24 (m + 2)
  have h1 := a24 (m + 1)
  push_cast at h9 h8 h7 h6 h5 h4 h3 h2 h1
  linear_combination h9 - 9 * h8 + 36 * h7 - 84 * h6 + 126 * h5 - 126 * h4 + 84 * h3
    - 36 * h2 + 9 * h1 - a24 m

theorem cX (f : ℕ → ℚ) (c : ℚ) (n k : ℕ) :
    coeff n (PowerSeries.mk f * (C c * X ^ k)) = if k ≤ n then c * f (n - k) else 0 := by
  rw [mul_left_comm, coeff_C_mul, coeff_mul_X_pow', coeff_mk]
  split_ifs <;> simp

end A147817Aux

open OMA.S_oeis_a147817 PowerSeries A147817Aux in
theorem OMA.solution : type_of% @OMA.S_oeis_a147817.main := by
  refine ⟨?_, fun n hn => ?_⟩
  · have hD : ((1 - X) ^ 9 : PowerSeries ℚ) = C 1 * X ^ 0 - C 9 * X ^ 1 + C 36 * X ^ 2
        - C 84 * X ^ 3 + C 126 * X ^ 4 - C 126 * X ^ 5 + C 84 * X ^ 6 - C 36 * X ^ 7
        + C 9 * X ^ 8 - C 1 * X ^ 9 := by
      simp only [map_one, map_ofNat]
      ring
    have hN : (2 * X ^ 4 * (93 + 688 * X + 18 * X ^ 2 + 48 * X ^ 3 - 7 * X ^ 4) : PowerSeries ℚ) =
        C 186 * X ^ 4 + C 1376 * X ^ 5 + C 36 * X ^ 6 + C 96 * X ^ 7 - C 14 * X ^ 8 := by
      simp only [map_ofNat]
      ring
    rw [hD, hN]
    ext n
    simp only [mul_add, mul_sub, map_add, map_sub, cX, coeff_C_mul_X_pow]
    rcases Nat.lt_or_ge n 9 with h | h
    · interval_cases n <;> norm_num [a, Nat.choose]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 9 := ⟨n - 9, by omega⟩
      have hq : ((a (m + 9) : ℤ) : ℚ) = ((9 * a (m + 8) - 36 * a (m + 7) + 84 * a (m + 6)
          - 126 * a (m + 5) + 126 * a (m + 4) - 84 * a (m + 3) + 36 * a (m + 2) - 9 * a (m + 1)
          + a m : ℤ) : ℚ) := by rw [rec9]
      push_cast at hq
      simp only [show 0 ≤ m + 9 by omega, show 1 ≤ m + 9 by omega, show 2 ≤ m + 9 by omega,
        show 3 ≤ m + 9 by omega, show 4 ≤ m + 9 by omega, show 5 ≤ m + 9 by omega,
        show 6 ≤ m + 9 by omega, show 7 ≤ m + 9 by omega, show 8 ≤ m + 9 by omega,
        show 9 ≤ m + 9 by omega, ↓reduceIte,
        show m + 9 - 0 = m + 9 by omega, show m + 9 - 1 = m + 8 by omega,
        show m + 9 - 2 = m + 7 by omega, show m + 9 - 3 = m + 6 by omega,
        show m + 9 - 4 = m + 5 by omega, show m + 9 - 5 = m + 4 by omega,
        show m + 9 - 6 = m + 3 by omega, show m + 9 - 7 = m + 2 by omega,
        show m + 9 - 8 = m + 1 by omega, show m + 9 - 9 = m by omega,
        show m + 9 ≠ 4 by omega, show m + 9 ≠ 5 by omega, show m + 9 ≠ 6 by omega,
        show m + 9 ≠ 7 by omega, show m + 9 ≠ 8 by omega]
      linarith
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 9 := ⟨n - 9, by omega⟩
    rw [show m + 9 - 1 = m + 8 by omega, show m + 9 - 2 = m + 7 by omega,
      show m + 9 - 3 = m + 6 by omega, show m + 9 - 4 = m + 5 by omega,
      show m + 9 - 5 = m + 4 by omega, show m + 9 - 6 = m + 3 by omega,
      show m + 9 - 7 = m + 2 by omega, show m + 9 - 8 = m + 1 by omega,
      show m + 9 - 9 = m by omega]
    exact rec9 m
