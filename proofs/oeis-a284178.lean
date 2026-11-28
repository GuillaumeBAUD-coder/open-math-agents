import OMAStatements.S_oeis_a284178
import Mathlib

/-!
# A284178: Decimal representation of the x-axis, from the origin to the right edge, of the n-th stage of growth of the two-dimensional cellular automaton defined by Rule 809, based on the 5-celled von Neumann neighborhood.: the conjectured package is inconsistent

The generating-function identity determines the sequence completely.  Comparing the
coefficients of `X ^ 0, …, X ^ 17` on both sides gives, one after the other,

  `a 0, …, a 17 = 1, 0, 4, 0, 20, 0, 84, 16, 292, 64, 1172, 272, 4644, 1344, 19092, 5392, 76324, 21824`.

But the claimed recurrence at `n = 17` evaluates to `21568` instead of `21824`.
So the conjunction of the claims is false, whatever the sequence is.
-/

open OMA.S_oeis_a284178 PowerSeries in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a284178.main) := by
  rintro ⟨hgf, hX⟩
  -- from here on the sequence is an arbitrary function `f`
  generalize a = f at hgf hX
  -- expand both polynomials into monomials
  have el : ∀ S : PowerSeries ℤ, S * (((1 - X) * (1 + X) * (1 - 2 * X) * (1 + 2 * X) * (1 + X ^ 2) * (1 + X ^ 4))) =
      C (1 : ℤ) * (S * X ^ 0) + C (-4 : ℤ) * (S * X ^ 2) + C (-1 : ℤ) * (S * X ^ 8) + C (4 : ℤ) * (S * X ^ 10) := by
    intro S
    simp only [map_neg, map_one, map_ofNat]
    ring
  have er : (((1 + 4 * X ^ 4 + 4 * X ^ 6 + 16 * X ^ 7 - 45 * X ^ 8 + 4 * X ^ 10 + 16 * X ^ 11 - 48 * X ^ 12 + 256 * X ^ 13 + 512 * X ^ 14 + 256 * X ^ 17 : PowerSeries ℤ)) : PowerSeries ℤ) =
      (X ^ 0 : PowerSeries ℤ) * C (1 : ℤ) + (X ^ 4 : PowerSeries ℤ) * C (4 : ℤ) + (X ^ 6 : PowerSeries ℤ) * C (4 : ℤ) + (X ^ 7 : PowerSeries ℤ) * C (16 : ℤ) + (X ^ 8 : PowerSeries ℤ) * C (-45 : ℤ) + (X ^ 10 : PowerSeries ℤ) * C (4 : ℤ) + (X ^ 11 : PowerSeries ℤ) * C (16 : ℤ) + (X ^ 12 : PowerSeries ℤ) * C (-48 : ℤ) + (X ^ 13 : PowerSeries ℤ) * C (256 : ℤ) + (X ^ 14 : PowerSeries ℤ) * C (512 : ℤ) + (X ^ 17 : PowerSeries ℤ) * C (256 : ℤ) := by
    simp only [map_neg, map_one, map_ofNat]
    ring
  rw [el, er] at hgf
  -- read off the coefficients one at a time
  have v0 : f 0 = 1 := by
    have h := congrArg (PowerSeries.coeff 0) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 0 : ℤ) : ℤ) = 1)
  have v1 : f 1 = 0 := by
    have h := congrArg (PowerSeries.coeff 1) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 1 : ℤ) : ℤ) = 0)
  have v2 : f 2 = 4 := by
    have h := congrArg (PowerSeries.coeff 2) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 2 : ℤ) : ℤ) = 4)
  have v3 : f 3 = 0 := by
    have h := congrArg (PowerSeries.coeff 3) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 3 : ℤ) : ℤ) = 0)
  have v4 : f 4 = 20 := by
    have h := congrArg (PowerSeries.coeff 4) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 4 : ℤ) : ℤ) = 20)
  have v5 : f 5 = 0 := by
    have h := congrArg (PowerSeries.coeff 5) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3, v4] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 5 : ℤ) : ℤ) = 0)
  have v6 : f 6 = 84 := by
    have h := congrArg (PowerSeries.coeff 6) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3, v4, v5] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 6 : ℤ) : ℤ) = 84)
  have v7 : f 7 = 16 := by
    have h := congrArg (PowerSeries.coeff 7) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3, v4, v5, v6] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 7 : ℤ) : ℤ) = 16)
  have v8 : f 8 = 292 := by
    have h := congrArg (PowerSeries.coeff 8) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3, v4, v5, v6, v7] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 8 : ℤ) : ℤ) = 292)
  have v9 : f 9 = 64 := by
    have h := congrArg (PowerSeries.coeff 9) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3, v4, v5, v6, v7, v8] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 9 : ℤ) : ℤ) = 64)
  have v10 : f 10 = 1172 := by
    have h := congrArg (PowerSeries.coeff 10) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 10 : ℤ) : ℤ) = 1172)
  have v11 : f 11 = 272 := by
    have h := congrArg (PowerSeries.coeff 11) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 11 : ℤ) : ℤ) = 272)
  have v12 : f 12 = 4644 := by
    have h := congrArg (PowerSeries.coeff 12) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 12 : ℤ) : ℤ) = 4644)
  have v13 : f 13 = 1344 := by
    have h := congrArg (PowerSeries.coeff 13) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 13 : ℤ) : ℤ) = 1344)
  have v14 : f 14 = 19092 := by
    have h := congrArg (PowerSeries.coeff 14) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 14 : ℤ) : ℤ) = 19092)
  have v15 : f 15 = 5392 := by
    have h := congrArg (PowerSeries.coeff 15) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 15 : ℤ) : ℤ) = 5392)
  have v16 : f 16 = 76324 := by
    have h := congrArg (PowerSeries.coeff 16) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 16 : ℤ) : ℤ) = 76324)
  have v17 : f 17 = 21824 := by
    have h := congrArg (PowerSeries.coeff 17) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 17 : ℤ) : ℤ) = 21824)
  -- the claimed recurrence at `n = 17` contradicts these values
  have hr := hX 17 (by first | decide | norm_num)
  norm_num [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17] at hr
