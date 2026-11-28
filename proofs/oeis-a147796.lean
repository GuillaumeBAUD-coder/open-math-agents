import OMAStatements.S_oeis_a147796

-- Problem: A147796: Number of consistent sets of 3 irreflexive binary order relationships over n objects.
-- Upstream: formal-conjectures statements/oeis-a147796.lean:0 (declaration OMA.S_oeis_a147796.main)
-- Credit: @nigelcarreiro-blip (the owner of the agent is credited as the solver)

/-! 6 a(n) = n (n-1) (n-2) (n^3 - 5n - 6) is a polynomial of degree 6, so its seventh differences
vanish, which is the recurrence. Multiplying the g.f. by (1 - x)^7 takes seventh differences, so
only the coefficients of degree below 7 remain; they are computed directly. -/

namespace A147796Aux

open OMA.S_oeis_a147796 PowerSeries

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

theorem a6 (n : ℕ) : 6 * a n = n * (n - 1) * (n - 2) * (n ^ 3 - 5 * n - 6) := by
  simp only [a]
  linear_combination ((n : ℤ) ^ 3 - 5 * n - 6) * c3 n

theorem rec7 (m : ℕ) : a (m + 7) = 7 * a (m + 6) - 21 * a (m + 5) + 35 * a (m + 4)
    - 35 * a (m + 3) + 21 * a (m + 2) - 7 * a (m + 1) + a m := by
  apply mul_left_cancel₀ (show (6 : ℤ) ≠ 0 by norm_num)
  have h7 := a6 (m + 7)
  have h6 := a6 (m + 6)
  have h5 := a6 (m + 5)
  have h4 := a6 (m + 4)
  have h3 := a6 (m + 3)
  have h2 := a6 (m + 2)
  have h1 := a6 (m + 1)
  push_cast at h7 h6 h5 h4 h3 h2 h1
  linear_combination h7 - 7 * h6 + 21 * h5 - 35 * h4 + 35 * h3 - 21 * h2 + 7 * h1 - a6 m

theorem cX (f : ℕ → ℚ) (c : ℚ) (n k : ℕ) :
    coeff n (PowerSeries.mk f * (C c * X ^ k)) = if k ≤ n then c * f (n - k) else 0 := by
  rw [mul_left_comm, coeff_C_mul, coeff_mul_X_pow', coeff_mk]
  split_ifs <;> simp

end A147796Aux

open OMA.S_oeis_a147796 PowerSeries A147796Aux in
theorem OMA.solution : type_of% @OMA.S_oeis_a147796.main := by
  refine ⟨?_, fun n hn => ?_⟩
  · have hD : ((1 - X) ^ 7 : PowerSeries ℚ) = C 1 * X ^ 0 - C 7 * X ^ 1 + C 21 * X ^ 2
        - C 35 * X ^ 3 + C 35 * X ^ 4 - C 21 * X ^ 5 + C 7 * X ^ 6 - C 1 * X ^ 7 := by
      simp only [map_one, map_ofNat]
      ring
    have hN : (2 * X ^ 3 * (3 + 55 * X + X ^ 2 + X ^ 3) : PowerSeries ℚ) =
        C 6 * X ^ 3 + C 110 * X ^ 4 + C 2 * X ^ 5 + C 2 * X ^ 6 := by
      simp only [map_ofNat]
      ring
    rw [hD, hN]
    ext n
    simp only [mul_add, mul_sub, map_add, map_sub, cX, coeff_C_mul_X_pow]
    rcases Nat.lt_or_ge n 7 with h | h
    · interval_cases n <;> norm_num [a, Nat.choose]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 7 := ⟨n - 7, by omega⟩
      have hq : ((a (m + 7) : ℤ) : ℚ) = ((7 * a (m + 6) - 21 * a (m + 5) + 35 * a (m + 4)
          - 35 * a (m + 3) + 21 * a (m + 2) - 7 * a (m + 1) + a m : ℤ) : ℚ) := by rw [rec7]
      push_cast at hq
      simp only [show 0 ≤ m + 7 by omega, show 1 ≤ m + 7 by omega, show 2 ≤ m + 7 by omega,
        show 3 ≤ m + 7 by omega, show 4 ≤ m + 7 by omega, show 5 ≤ m + 7 by omega,
        show 6 ≤ m + 7 by omega, show 7 ≤ m + 7 by omega, ↓reduceIte,
        show m + 7 - 0 = m + 7 by omega, show m + 7 - 1 = m + 6 by omega,
        show m + 7 - 2 = m + 5 by omega, show m + 7 - 3 = m + 4 by omega,
        show m + 7 - 4 = m + 3 by omega, show m + 7 - 5 = m + 2 by omega,
        show m + 7 - 6 = m + 1 by omega, show m + 7 - 7 = m by omega,
        show m + 7 ≠ 3 by omega, show m + 7 ≠ 4 by omega, show m + 7 ≠ 5 by omega,
        show m + 7 ≠ 6 by omega]
      linarith
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 7 := ⟨n - 7, by omega⟩
    rw [show m + 7 - 1 = m + 6 by omega, show m + 7 - 2 = m + 5 by omega,
      show m + 7 - 3 = m + 4 by omega, show m + 7 - 4 = m + 3 by omega,
      show m + 7 - 5 = m + 2 by omega, show m + 7 - 6 = m + 1 by omega,
      show m + 7 - 7 = m by omega]
    exact rec7 m
