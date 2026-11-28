import OMAStatements.S_oeis_a335756
import Mathlib

theorem OMA.solution : type_of% @OMA.S_oeis_a335756.main := by
  open PowerSeries OMA.S_oeis_a335756 in
  have hr : ∀ n : ℕ, a (n + 6) - 2 * a (n + 3) + a n = 0 := by
    intro n
    simp only [a]
    split_ifs <;> push_cast <;> omega
  refine ⟨?_, ?_⟩
  · have e : ((1 - X) ^ 2 * (1 + X + X ^ 2) ^ 2 : PowerSeries ℚ) = 1 - X ^ 3 * C (2:ℚ) + X ^ 6 := by
      simp only [map_ofNat]; ring
    have e2 : (2 * (1 + X ^ 2 + 4 * X ^ 3 + 3 * X ^ 4 + 2 * X ^ 5) : PowerSeries ℚ) =
        C (2:ℚ) + C (2:ℚ) * X ^ 2 + C (8:ℚ) * X ^ 3 + C (6:ℚ) * X ^ 4 + C (4:ℚ) * X ^ 5 := by
      simp only [map_ofNat]; ring
    rw [e, e2]
    ext n
    simp only [mul_add, mul_sub, mul_one, map_add, map_sub, ← mul_assoc, coeff_mul_X_pow', coeff_mul_C,
      coeff_C_mul_X_pow, coeff_C, coeff_C_mul, coeff_mk]
    rcases n with _ | _ | _ | _ | _ | _ | n
    all_goals first
      | (simp [a]; done)
      | (simp [a]; norm_num; done)
      | skip
    all_goals
      have h := hr n
      have h' : ((a (n + 6) : ℤ) : ℚ) - 2 * (a (n + 3) : ℚ) + (a n : ℚ) = 0 := by exact_mod_cast h
      simp
      linarith
  · intro n hn
    obtain ⟨j, rfl⟩ : ∃ j, n = j + 6 := ⟨n - 6, by omega⟩
    have := hr j
    simp only [Nat.add_sub_cancel, show j + 6 - 3 = j + 3 by omega]
    linarith
