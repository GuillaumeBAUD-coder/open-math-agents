import OMAStatements.S_oeis_a005313
import Mathlib

namespace OMA.S_oeis_a005313
open PowerSeries

lemma rec5 (n : ℕ) : a (n + 5) = 4 * a (n + 4) - 3 * a (n + 3) - 3 * a (n + 2) + 4 * a (n + 1) - a n := by
  unfold a
  have e : ∀ k, (Nat.fib (n + k + 2) : ℤ) = Nat.fib (n + k) + Nat.fib (n + k + 1) := by
    intro k; rw [Nat.fib_add_two]; push_cast; ring
  rw [show n + 5 = n + 4 + 1 from rfl, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
  have h2 := e 0; have h3 := e 1; have h4 := e 2; have h5 := e 3
  simp only [Nat.add_zero, show n + 1 + 2 = n + 3 from rfl, show n + 2 + 2 = n + 4 from rfl,
    show n + 3 + 2 = n + 5 from rfl, show n + 1 + 1 = n + 2 from rfl,
    show n + 2 + 1 = n + 3 from rfl, show n + 3 + 1 = n + 4 from rfl] at h2 h3 h4 h5
  have h6 : (Nat.fib (n + 4 + 1) : ℤ) = Nat.fib (n + 4) + Nat.fib (n + 3) := by
    rw [show n + 4 + 1 = n + 3 + 2 from rfl, Nat.fib_add_two]; push_cast; ring
  simp only [show n + 4 = n + 3 + 1 from rfl, show n + 3 = n + 2 + 1 from rfl,
    show n + 2 = n + 1 + 1 from rfl] at *
  push_cast
  simp only [Nat.fib_add_two] at *
  push_cast at *
  nlinarith [h2]


lemma coeffD (f : PowerSeries ℚ) (n : ℕ) :
    coeff (n + 5) (f * ((1 - 3 * X + X ^ 2) * (1 + X) * (1 - X) ^ 2)) =
      coeff (n + 5) f - 4 * coeff (n + 4) f + 3 * coeff (n + 3) f + 3 * coeff (n + 2) f
        - 4 * coeff (n + 1) f + coeff n f := by
  have : ((1 - 3 * X + X ^ 2) * (1 + X) * (1 - X) ^ 2 : PowerSeries ℚ) =
      1 - 4 * X + 3 * X ^ 2 + 3 * X ^ 3 - 4 * X ^ 4 + X ^ 5 := by ring
  rw [this]
  have h2 : f * (1 - 4 * X + 3 * X ^ 2 + 3 * X ^ 3 - 4 * X ^ 4 + X ^ 5) =
      f - C (4:ℚ) * (f * X ^ 1) + C (3:ℚ) * (f * X ^ 2) + C (3:ℚ) * (f * X ^ 3)
        - C (4:ℚ) * (f * X ^ 4) + f * X ^ 5 := by
    simp only [map_ofNat]; ring
  rw [h2]
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_X_pow']
  simp


lemma coeffD' (f : PowerSeries ℚ) (n : ℕ) :
    coeff n (f * ((1 - 3 * X + X ^ 2) * (1 + X) * (1 - X) ^ 2)) =
      coeff n f - 4 * (if 1 ≤ n then coeff (n - 1) f else 0)
        + 3 * (if 2 ≤ n then coeff (n - 2) f else 0) + 3 * (if 3 ≤ n then coeff (n - 3) f else 0)
        - 4 * (if 4 ≤ n then coeff (n - 4) f else 0) + (if 5 ≤ n then coeff (n - 5) f else 0) := by
  have : ((1 - 3 * X + X ^ 2) * (1 + X) * (1 - X) ^ 2 : PowerSeries ℚ) =
      1 - 4 * X + 3 * X ^ 2 + 3 * X ^ 3 - 4 * X ^ 4 + X ^ 5 := by ring
  rw [this]
  have h2 : f * (1 - 4 * X + 3 * X ^ 2 + 3 * X ^ 3 - 4 * X ^ 4 + X ^ 5) =
      f - C (4:ℚ) * (f * X ^ 1) + C (3:ℚ) * (f * X ^ 2) + C (3:ℚ) * (f * X ^ 3)
        - C (4:ℚ) * (f * X ^ 4) + f * X ^ 5 := by
    simp only [map_ofNat]; ring
  rw [h2]
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_X_pow']

end OMA.S_oeis_a005313

open OMA.S_oeis_a005313 PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a005313.main := by
  ext n
  rw [coeffD']
  have hR : (X * (1 - X - 3 * X ^ 2 + X ^ 3) : PowerSeries ℚ) =
      X - X ^ 2 - C (3:ℚ) * X ^ 3 + X ^ 4 := by simp only [map_ofNat]; ring
  rw [hR]
  simp only [map_add, map_sub, coeff_C_mul, coeff_X_pow, coeff_X, coeff_mk]
  by_cases hn : 5 ≤ n
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
    have := rec5 m
    have e : ((a (5 + m) : ℤ) : ℚ) = 4 * (a (4 + m) : ℚ) - 3 * a (3 + m) - 3 * a (2 + m) + 4 * a (1 + m) - a m := by
      rw [add_comm 5 m, this]; push_cast; rw [add_comm m 4, add_comm m 3, add_comm m 2, add_comm m 1]
    simp only [if_pos (show 1 ≤ 5 + m by omega), if_pos (show 2 ≤ 5 + m by omega),
      if_pos (show 3 ≤ 5 + m by omega), if_pos (show 4 ≤ 5 + m by omega), if_pos hn]
    simp only [show 5 + m - 1 = 4 + m by omega, show 5 + m - 2 = 3 + m by omega,
      show 5 + m - 3 = 2 + m by omega, show 5 + m - 4 = 1 + m by omega, show 5 + m - 5 = m by omega]
    rw [e]
    have h0 : ¬ (5 + m = 1) := by omega
    have h1 : ¬ (5 + m = 2) := by omega
    have h3 : ¬ (5 + m = 3) := by omega
    have h4 : ¬ (5 + m = 4) := by omega
    simp [h0, h1, h3, h4]; ring
  · interval_cases n <;> simp [a, Finset.sum_range_succ, Nat.fib_add_two] <;> norm_num
