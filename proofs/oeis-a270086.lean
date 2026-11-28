import OMAStatements.S_oeis_a270086
import Mathlib

/-!
# OEIS A270086: the conjectured package is inconsistent

The generating-function identity determines the sequence completely.  Comparing the
coefficients of `X ^ 0, …, X ^ 9` on both sides gives, one after the other,

  `a 0, …, a 9 = 3, 1, 31, -27, 87, -79, 171, -167, 291, -287`.

But the claimed recurrence at `n = 9` evaluates to `-291` instead of `-287`.
So the conjunction of the claims is false, whatever the sequence is.
-/

open OMA.S_oeis_a270086 PowerSeries in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a270086.main) := by
  rintro ⟨-, -, -, hX, hgf⟩
  -- expand both polynomials into monomials
  have el : ∀ S : PowerSeries ℤ, S * (((1 - X) ^ 2 * (1 + X) ^ 3)) =
      C (1 : ℤ) * (S * X ^ 0) + C (1 : ℤ) * (S * X ^ 1) + C (-2 : ℤ) * (S * X ^ 2) + C (-2 : ℤ) * (S * X ^ 3) + C (1 : ℤ) * (S * X ^ 4) + C (1 : ℤ) * (S * X ^ 5) := by
    intro S
    simp only [map_neg, map_one, map_ofNat]
    ring
  have er : ((3 + 4 * X + 26 * X ^ 2 - 4 * X ^ 3 - X ^ 4 + 4 * X ^ 5 + 4 * X ^ 6 - 8 * X ^ 7 + 4 * X ^ 9) : PowerSeries ℤ) =
      (X ^ 0 : PowerSeries ℤ) * C (3 : ℤ) + (X ^ 1 : PowerSeries ℤ) * C (4 : ℤ) + (X ^ 2 : PowerSeries ℤ) * C (26 : ℤ) + (X ^ 3 : PowerSeries ℤ) * C (-4 : ℤ) + (X ^ 4 : PowerSeries ℤ) * C (-1 : ℤ) + (X ^ 5 : PowerSeries ℤ) * C (4 : ℤ) + (X ^ 6 : PowerSeries ℤ) * C (4 : ℤ) + (X ^ 7 : PowerSeries ℤ) * C (-8 : ℤ) + (X ^ 9 : PowerSeries ℤ) * C (4 : ℤ) := by
    simp only [map_neg, map_one, map_ofNat]
    ring
  rw [el, er] at hgf
  -- read off the coefficients one at a time
  have v0 : a 0 = 3 := by
    have h := congrArg (PowerSeries.coeff 0) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp at h
    first | omega | linarith | exact_mod_cast (by linarith : ((a 0 : ℤ) : ℤ) = 3)
  have v1 : a 1 = 1 := by
    have h := congrArg (PowerSeries.coeff 1) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((a 1 : ℤ) : ℤ) = 1)
  have v2 : a 2 = 31 := by
    have h := congrArg (PowerSeries.coeff 2) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((a 2 : ℤ) : ℤ) = 31)
  have v3 : a 3 = -27 := by
    have h := congrArg (PowerSeries.coeff 3) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((a 3 : ℤ) : ℤ) = -27)
  have v4 : a 4 = 87 := by
    have h := congrArg (PowerSeries.coeff 4) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((a 4 : ℤ) : ℤ) = 87)
  have v5 : a 5 = -79 := by
    have h := congrArg (PowerSeries.coeff 5) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3, v4] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((a 5 : ℤ) : ℤ) = -79)
  have v6 : a 6 = 171 := by
    have h := congrArg (PowerSeries.coeff 6) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3, v4, v5] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((a 6 : ℤ) : ℤ) = 171)
  have v7 : a 7 = -167 := by
    have h := congrArg (PowerSeries.coeff 7) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3, v4, v5, v6] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((a 7 : ℤ) : ℤ) = -167)
  have v8 : a 8 = 291 := by
    have h := congrArg (PowerSeries.coeff 8) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3, v4, v5, v6, v7] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((a 8 : ℤ) : ℤ) = 291)
  have v9 : a 9 = -287 := by
    have h := congrArg (PowerSeries.coeff 9) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3, v4, v5, v6, v7, v8] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((a 9 : ℤ) : ℤ) = -287)
  -- the claimed recurrence at `n = 9` contradicts these values
  have hr := hX 9 (by first | decide | norm_num)
  norm_num [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9] at hr
