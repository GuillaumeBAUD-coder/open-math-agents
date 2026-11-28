import OMAStatements.S_oeis_a147817
import Mathlib

namespace OMA.S_oeis_a147817

theorem gf_pow (f : ℕ → ℚ) (d n : ℕ) :
    PowerSeries.coeff n (PowerSeries.mk f * (1 - PowerSeries.X) ^ d) =
      ∑ i ∈ Finset.range (d + 1), (-1 : ℚ) ^ i * (d.choose i : ℚ) * (if i ≤ n then f (n - i) else 0) := by
  rw [sub_eq_neg_add, add_pow, Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have h : PowerSeries.mk f * ((-PowerSeries.X) ^ i * 1 ^ (d - i) * (d.choose i : PowerSeries ℚ)) =
      PowerSeries.C (((-1 : ℚ) ^ i * (d.choose i : ℚ))) * (PowerSeries.X ^ i * PowerSeries.mk f) := by
    have hx : (-PowerSeries.X : PowerSeries ℚ) = PowerSeries.C (-1) * PowerSeries.X := by simp
    rw [hx, mul_pow, ← map_pow]
    simp only [one_pow, mul_one, map_mul, map_pow, map_neg, map_one, map_natCast]
    ring
  rw [h, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul']
  simp [PowerSeries.coeff_mk]


theorem ch4 (n : ℕ) : (n.choose 4 : ℚ) = (n : ℚ) * (n - 1) * (n - 2) * (n - 3) / 24 := by
  have h1 : ∀ n : ℕ, (n.choose 1 : ℚ) = n := fun n => by simp
  have h2 : ∀ n : ℕ, (n.choose 2 : ℚ) = (n : ℚ) * (n - 1) / 2 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [Nat.choose_succ_succ, Nat.cast_add, ih, h1]; push_cast; ring
  have h3 : ∀ n : ℕ, (n.choose 3 : ℚ) = (n : ℚ) * (n - 1) * (n - 2) / 6 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [Nat.choose_succ_succ, Nat.cast_add, ih, h2]; push_cast; ring
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.choose_succ_succ, Nat.cast_add, ih, h3]; push_cast; ring

def P (n : ℕ) : ℚ := ((n : ℚ) * (n - 1) * (n - 2) * (n - 3) / 24) * ((n : ℚ) ^ 4 + 2 * (n : ℚ) ^ 3 - 5 * (n : ℚ) ^ 2 - 22 * (n : ℚ) - 30)

theorem hf (n : ℕ) : (a n : ℚ) = P n := by
  simp only [a, P]
  push_cast
  rw [ch4]

open PowerSeries in
theorem gf : (PowerSeries.mk (fun n => (a n : ℚ)) * (1 - X) ^ 9 =
    2 * X ^ 4 * (93 + 688 * X + 18 * X ^ 2 + 48 * X ^ 3 - 7 * X ^ 4)) := by
  have hR : (2 * X ^ 4 * (93 + 688 * X + 18 * X ^ 2 + 48 * X ^ 3 - 7 * X ^ 4) : PowerSeries ℚ) =
      186 • X ^ 4 + 1376 • X ^ 5 + 36 • X ^ 6 + 96 • X ^ 7 - 14 • X ^ 8 := by
    simp only [nsmul_eq_mul]; push_cast; ring
  rw [hR]
  ext n
  rw [gf_pow]
  simp only [map_add, map_sub, map_nsmul, coeff_X_pow]
  rcases (by omega : n < 9 ∨ 9 ≤ n) with h | h
  · interval_cases n <;> simp [Finset.sum_range_succ, hf, P, Nat.choose] <;> norm_num
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 9 := ⟨n - 9, by omega⟩
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, if_pos (show 0 ≤ m + 9 by omega), if_pos (show 1 ≤ m + 9 by omega), if_pos (show 2 ≤ m + 9 by omega), if_pos (show 3 ≤ m + 9 by omega), if_pos (show 4 ≤ m + 9 by omega), if_pos (show 5 ≤ m + 9 by omega), if_pos (show 6 ≤ m + 9 by omega), if_pos (show 7 ≤ m + 9 by omega), if_pos (show 8 ≤ m + 9 by omega), if_pos (show 9 ≤ m + 9 by omega),
      show m + 9 - 0 = m + 9 by omega, show m + 9 - 1 = m + 8 by omega, show m + 9 - 2 = m + 7 by omega, show m + 9 - 3 = m + 6 by omega, show m + 9 - 4 = m + 5 by omega, show m + 9 - 5 = m + 4 by omega, show m + 9 - 6 = m + 3 by omega, show m + 9 - 7 = m + 2 by omega, show m + 9 - 8 = m + 1 by omega, show m + 9 - 9 = m + 0 by omega]
    simp only [hf, P]
    simp [Nat.choose]
    push_cast
    ring

theorem solution_aux : type_of% @OMA.S_oeis_a147817.main := by
  refine ⟨gf, ?_⟩
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 9 := ⟨n - 9, by omega⟩
  simp only [show m + 9 - 1 = m + 8 by omega, show m + 9 - 2 = m + 7 by omega, show m + 9 - 3 = m + 6 by omega,
    show m + 9 - 4 = m + 5 by omega, show m + 9 - 5 = m + 4 by omega, show m + 9 - 6 = m + 3 by omega,
    show m + 9 - 7 = m + 2 by omega, show m + 9 - 8 = m + 1 by omega, show m + 9 - 9 = m by omega]
  have key : ((a (m + 9) : ℤ) : ℚ) = 9 * (a (m + 8) : ℤ) - 36 * (a (m + 7) : ℤ) + 84 * (a (m + 6) : ℤ) - 126 * (a (m + 5) : ℤ)
      + 126 * (a (m + 4) : ℤ) - 84 * (a (m + 3) : ℤ) + 36 * (a (m + 2) : ℤ) - 9 * (a (m + 1) : ℤ) + (a m : ℤ) := by
    simp only [hf, P]
    push_cast
    ring
  exact_mod_cast key

end OMA.S_oeis_a147817

theorem OMA.solution : type_of% @OMA.S_oeis_a147817.main := OMA.S_oeis_a147817.solution_aux
