import OMAStatements.S_oeis_a270079
import Mathlib

/-!
# A270079: Number of active (ON, black) cells in n-th stage of growth of two-dimensional cellular automaton defined by Rule 62, based on the 5-celled von Neumann neighborhood.: the conjectured package is inconsistent

The generating-function identity determines the sequence completely.  Comparing the
coefficients of `X ^ 0, …, X ^ 12` on both sides gives, one after the other,

  `a 0, …, a 12 = 1, 5, 12, 20, 32, 44, 68, 72, 100, 112, 156, 160, 204`.

But the claimed recurrence at `n = 12` evaluates to `208` instead of `204`.
So the conjunction of the claims is false, whatever the sequence is.
-/

open OMA.S_oeis_a270079 PowerSeries in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a270079.main) := by
  rintro ⟨hX, hgf⟩
  -- expand both polynomials into monomials
  have el : ∀ S : PowerSeries ℤ, S * (((1 - X) ^ 3 * (1 + X) ^ 2 * (1 + X ^ 2))) =
      C (1 : ℤ) * (S * X ^ 0) + C (-1 : ℤ) * (S * X ^ 1) + C (-1 : ℤ) * (S * X ^ 2) + C (1 : ℤ) * (S * X ^ 3) + C (-1 : ℤ) * (S * X ^ 4) + C (1 : ℤ) * (S * X ^ 5) + C (1 : ℤ) * (S * X ^ 6) + C (-1 : ℤ) * (S * X ^ 7) := by
    intro S
    simp only [map_neg, map_one, map_ofNat]
    ring
  have er : (((1 + 4 * X + 6 * X ^ 2 + 4 * X ^ 3 + 4 * X ^ 4 + 6 * X ^ 6 - 12 * X ^ 7 - X ^ 8 + 4 * X ^ 9 + 4 * X ^ 10 - 4 * X ^ 12 : PowerSeries ℤ)) : PowerSeries ℤ) =
      (X ^ 0 : PowerSeries ℤ) * C (1 : ℤ) + (X ^ 1 : PowerSeries ℤ) * C (4 : ℤ) + (X ^ 2 : PowerSeries ℤ) * C (6 : ℤ) + (X ^ 3 : PowerSeries ℤ) * C (4 : ℤ) + (X ^ 4 : PowerSeries ℤ) * C (4 : ℤ) + (X ^ 6 : PowerSeries ℤ) * C (6 : ℤ) + (X ^ 7 : PowerSeries ℤ) * C (-12 : ℤ) + (X ^ 8 : PowerSeries ℤ) * C (-1 : ℤ) + (X ^ 9 : PowerSeries ℤ) * C (4 : ℤ) + (X ^ 10 : PowerSeries ℤ) * C (4 : ℤ) + (X ^ 12 : PowerSeries ℤ) * C (-4 : ℤ) := by
    simp only [map_neg, map_one, map_ofNat]
    ring
  rw [el, er] at hgf
  -- read off the coefficients one at a time
  have v0 : a 0 = 1 := by
    have h := congrArg (PowerSeries.coeff 0) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp at h
    first | omega | linarith | exact_mod_cast (by linarith : ((a 0 : ℤ) : ℤ) = 1)
  have v1 : a 1 = 5 := by
    have h := congrArg (PowerSeries.coeff 1) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((a 1 : ℤ) : ℤ) = 5)
  have v2 : a 2 = 12 := by
    have h := congrArg (PowerSeries.coeff 2) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((a 2 : ℤ) : ℤ) = 12)
  have v3 : a 3 = 20 := by
    have h := congrArg (PowerSeries.coeff 3) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((a 3 : ℤ) : ℤ) = 20)
  have v4 : a 4 = 32 := by
    have h := congrArg (PowerSeries.coeff 4) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((a 4 : ℤ) : ℤ) = 32)
  have v5 : a 5 = 44 := by
    have h := congrArg (PowerSeries.coeff 5) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3, v4] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((a 5 : ℤ) : ℤ) = 44)
  have v6 : a 6 = 68 := by
    have h := congrArg (PowerSeries.coeff 6) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3, v4, v5] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((a 6 : ℤ) : ℤ) = 68)
  have v7 : a 7 = 72 := by
    have h := congrArg (PowerSeries.coeff 7) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3, v4, v5, v6] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((a 7 : ℤ) : ℤ) = 72)
  have v8 : a 8 = 100 := by
    have h := congrArg (PowerSeries.coeff 8) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3, v4, v5, v6, v7] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((a 8 : ℤ) : ℤ) = 100)
  have v9 : a 9 = 112 := by
    have h := congrArg (PowerSeries.coeff 9) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3, v4, v5, v6, v7, v8] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((a 9 : ℤ) : ℤ) = 112)
  have v10 : a 10 = 156 := by
    have h := congrArg (PowerSeries.coeff 10) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((a 10 : ℤ) : ℤ) = 156)
  have v11 : a 11 = 160 := by
    have h := congrArg (PowerSeries.coeff 11) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((a 11 : ℤ) : ℤ) = 160)
  have v12 : a 12 = 204 := by
    have h := congrArg (PowerSeries.coeff 12) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((a 12 : ℤ) : ℤ) = 204)
  -- the claimed recurrence at `n = 12` contradicts these values
  have hr := hX 12 (by first | decide | norm_num)
  norm_num [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12] at hr
