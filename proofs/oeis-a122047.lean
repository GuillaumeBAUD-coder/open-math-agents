import OMAStatements.S_oeis_a122047
import Mathlib

open OMA.S_oeis_a122047 PowerSeries

namespace P122047

theorem step (n : ℕ) : a (n + 5) = a n + ((n : ℤ) + 4) * ((n : ℤ) + 5) / 2 := by
  unfold a
  have hev : (2 : ℤ) ∣ ((n : ℤ) + 4) * ((n : ℤ) + 5) := by
    have := Int.even_mul_succ_self ((n : ℤ) + 4)
    rw [show (n : ℤ) + 4 + 1 = (n : ℤ) + 5 by ring] at this
    exact even_iff_two_dvd.mp this
  obtain ⟨c, hc⟩ := hev
  rw [hc, Int.mul_ediv_cancel_left _ (by norm_num)]
  push_cast
  have : ((n : ℤ) + 5) ^ 3 + 6 * ((n : ℤ) + 5) ^ 2 + 5 * ((n : ℤ) + 5) =
      ((n : ℤ) ^ 3 + 6 * (n : ℤ) ^ 2 + 5 * (n : ℤ)) + c * 30 := by
    linear_combination 15 * hc
  rw [this, Int.add_mul_ediv_right _ _ (by norm_num)]

theorem g2 (n : ℕ) : 2 * (((n : ℤ) + 4) * ((n : ℤ) + 5) / 2) = ((n : ℤ) + 4) * ((n : ℤ) + 5) := by
  have := Int.even_mul_succ_self ((n : ℤ) + 4)
  rw [show (n : ℤ) + 4 + 1 = (n : ℤ) + 5 by ring] at this
  exact Int.mul_ediv_cancel' (even_iff_two_dvd.mp this)

theorem rec8 (m : ℕ) : a (m + 8) = 3 * a (m + 7) - 3 * a (m + 6) + a (m + 5) + a (m + 3) -
    3 * a (m + 2) + 3 * a (m + 1) - a m := by
  have h8 := step (m + 3)
  have h7 := step (m + 2)
  have h6 := step (m + 1)
  have h5 := step m
  have e1 := g2 (m + 3)
  have e2 := g2 (m + 2)
  have e3 := g2 (m + 1)
  have e4 := g2 m
  push_cast at h8 h7 h6 h5 e1 e2 e3 e4
  rw [show m + 3 + 5 = m + 8 by ring] at h8
  rw [show m + 2 + 5 = m + 7 by ring] at h7
  rw [show m + 1 + 5 = m + 6 by ring] at h6
  linarith

end P122047

open P122047 in
theorem OMA.solution : type_of% @OMA.S_oeis_a122047.main := by
  refine ⟨?_, ?_⟩
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 8 := ⟨n - 8, by omega⟩
    rw [show m + 8 - 1 = m + 7 by omega, show m + 8 - 2 = m + 6 by omega,
      show m + 8 - 3 = m + 5 by omega, show m + 8 - 5 = m + 3 by omega,
      show m + 8 - 6 = m + 2 by omega, show m + 8 - 7 = m + 1 by omega,
      show m + 8 - 8 = m by omega, rec8 m]
  · have hp : ∀ F : PowerSeries ℚ, F * (1 + X + X ^ 2 + X ^ 3 + X ^ 4) * (1 - X) ^ 4 =
        F - 3 * (F * X ^ 1) + 3 * (F * X ^ 2) - F * X ^ 3 - F * X ^ 5 + 3 * (F * X ^ 6) -
          3 * (F * X ^ 7) + F * X ^ 8 := fun F => by ring
    rw [hp]
    ext n
    have h3 : ∀ F : PowerSeries ℚ, coeff n (3 * F) = 3 * coeff n F := fun F => by
      rw [← map_ofNat C 3, coeff_C_mul]
    simp only [map_sub, map_add, h3, coeff_mul_X_pow', coeff_mk, coeff_X_pow]
    rcases Nat.lt_or_ge n 8 with hn | hn
    · interval_cases n <;> norm_num [a]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 8 := ⟨n - 8, by omega⟩
      simp only [show 1 ≤ m + 8 by omega, show 2 ≤ m + 8 by omega, show 3 ≤ m + 8 by omega,
        show 5 ≤ m + 8 by omega, show 6 ≤ m + 8 by omega, show 7 ≤ m + 8 by omega,
        show 8 ≤ m + 8 by omega, if_true, show m + 8 ≠ 2 by omega, if_false,
        show m + 8 - 1 = m + 7 by omega, show m + 8 - 2 = m + 6 by omega,
        show m + 8 - 3 = m + 5 by omega, show m + 8 - 5 = m + 3 by omega,
        show m + 8 - 6 = m + 2 by omega, show m + 8 - 7 = m + 1 by omega,
        show m + 8 - 8 = m by omega]
      rw [rec8 m]
      push_cast
      ring
