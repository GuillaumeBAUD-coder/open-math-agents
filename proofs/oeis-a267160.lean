import OMAStatements.S_oeis_a267160
import Mathlib

/-!
# A267160: Number of OFF (white) cells in the n-th iteration of the Rule 107 elementary cellular automaton starting with a single ON (black) cell: the conjectured package is inconsistent

The generating-function identity determines the sequence completely.  Comparing the
coefficients of `X ^ 0, …, X ^ 12` on both sides gives, one after the other,

  `a 0, …, a 12 = 0, 2, 2, 2, 3, 3, 6, 2, 11, 4, 13, 2, 19`.

But the claimed recurrence at `n = 12` evaluates to `18` instead of `19`.
So the conjunction of the claims is false, whatever the sequence is.
-/

open OMA.S_oeis_a267160 PowerSeries in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a267160.main) := by
  rintro ⟨hX, hgf⟩
  -- from here on the sequence is an arbitrary function `f`
  generalize a = f at hgf hX
  -- expand both polynomials into monomials
  have el : ∀ S : PowerSeries ℚ, S * (((1 - X) ^ 2 * (1 + X) ^ 2 * (1 + X ^ 2))) =
      C (1 : ℚ) * (S * X ^ 0) + C (-1 : ℚ) * (S * X ^ 2) + C (-1 : ℚ) * (S * X ^ 4) + C (1 : ℚ) * (S * X ^ 6) := by
    intro S
    simp only [map_neg, map_one, map_ofNat]
    ring
  have er : ((X * (2 + 2 * X + X ^ 3 - X ^ 4 + X ^ 5 - X ^ 6 + 4 * X ^ 7 + X ^ 8 - X ^ 9 - X ^ 10 + X ^ 11)) : PowerSeries ℚ) =
      (X ^ 1 : PowerSeries ℚ) * C (2 : ℚ) + (X ^ 2 : PowerSeries ℚ) * C (2 : ℚ) + (X ^ 4 : PowerSeries ℚ) * C (1 : ℚ) + (X ^ 5 : PowerSeries ℚ) * C (-1 : ℚ) + (X ^ 6 : PowerSeries ℚ) * C (1 : ℚ) + (X ^ 7 : PowerSeries ℚ) * C (-1 : ℚ) + (X ^ 8 : PowerSeries ℚ) * C (4 : ℚ) + (X ^ 9 : PowerSeries ℚ) * C (1 : ℚ) + (X ^ 10 : PowerSeries ℚ) * C (-1 : ℚ) + (X ^ 11 : PowerSeries ℚ) * C (-1 : ℚ) + (X ^ 12 : PowerSeries ℚ) * C (1 : ℚ) := by
    simp only [map_neg, map_one, map_ofNat]
    ring
  rw [el, er] at hgf
  -- read off the coefficients one at a time
  have v0 : f 0 = 0 := by
    have h := congrArg (PowerSeries.coeff 0) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 0 : ℕ) : ℚ) = 0)
  have v1 : f 1 = 2 := by
    have h := congrArg (PowerSeries.coeff 1) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 1 : ℕ) : ℚ) = 2)
  have v2 : f 2 = 2 := by
    have h := congrArg (PowerSeries.coeff 2) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 2 : ℕ) : ℚ) = 2)
  have v3 : f 3 = 2 := by
    have h := congrArg (PowerSeries.coeff 3) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 3 : ℕ) : ℚ) = 2)
  have v4 : f 4 = 3 := by
    have h := congrArg (PowerSeries.coeff 4) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 4 : ℕ) : ℚ) = 3)
  have v5 : f 5 = 3 := by
    have h := congrArg (PowerSeries.coeff 5) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3, v4] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 5 : ℕ) : ℚ) = 3)
  have v6 : f 6 = 6 := by
    have h := congrArg (PowerSeries.coeff 6) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3, v4, v5] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 6 : ℕ) : ℚ) = 6)
  have v7 : f 7 = 2 := by
    have h := congrArg (PowerSeries.coeff 7) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3, v4, v5, v6] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 7 : ℕ) : ℚ) = 2)
  have v8 : f 8 = 11 := by
    have h := congrArg (PowerSeries.coeff 8) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3, v4, v5, v6, v7] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 8 : ℕ) : ℚ) = 11)
  have v9 : f 9 = 4 := by
    have h := congrArg (PowerSeries.coeff 9) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3, v4, v5, v6, v7, v8] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 9 : ℕ) : ℚ) = 4)
  have v10 : f 10 = 13 := by
    have h := congrArg (PowerSeries.coeff 10) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 10 : ℕ) : ℚ) = 13)
  have v11 : f 11 = 2 := by
    have h := congrArg (PowerSeries.coeff 11) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 11 : ℕ) : ℚ) = 2)
  have v12 : f 12 = 19 := by
    have h := congrArg (PowerSeries.coeff 12) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 12 : ℕ) : ℚ) = 19)
  -- the claimed recurrence at `n = 12` contradicts these values
  have hr := hX 12 (by first | decide | norm_num)
  norm_num [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12] at hr
