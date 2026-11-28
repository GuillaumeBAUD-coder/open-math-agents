import OMAStatements.S_oeis_a282828
import Mathlib

/-!
# A282828: Decimal representation of the x-axis, from the left edge to the origin, of the n-th stage of growth of the two-dimensional cellular automaton defined by Rule 521, based on the 5-celled von Neumann neighborhood.: the conjectured package is inconsistent

The generating-function identity determines the sequence completely.  Comparing the
coefficients of `X ^ 0, …, X ^ 17` on both sides gives, one after the other,

  `a 0, …, a 17 = 1, 0, 1, 0, 7, 7, 21, 0, 125, 124, 341, 0, 2029, 1964, 5517, 428, 32141, 32140`.

But the claimed recurrence at `n = 17` evaluates to `32172` instead of `32140`.
So the conjunction of the claims is false, whatever the sequence is.
-/

open OMA.S_oeis_a282828 PowerSeries in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a282828.main) := by
  rintro ⟨hX, hgf⟩
  -- from here on the sequence is an arbitrary function `f`
  generalize a = f at hgf hX
  -- expand both polynomials into monomials
  have el : ∀ S : PowerSeries ℤ, S * (((1 - X) * (1 + X) * (1 - 2 * X) * (1 + 2 * X) * (1 + 4 * X ^ 2) * (1 + 16 * X ^ 4))) =
      C (1 : ℤ) * (S * X ^ 0) + C (-1 : ℤ) * (S * X ^ 2) + C (-256 : ℤ) * (S * X ^ 8) + C (256 : ℤ) * (S * X ^ 10) := by
    intro S
    simp only [map_neg, map_one, map_ofNat]
    ring
  have er : (((1 + 6 * X ^ 4 + 7 * X ^ 5 + 14 * X ^ 6 - 7 * X ^ 7 - 152 * X ^ 8 + 124 * X ^ 9 + 216 * X ^ 10 - 124 * X ^ 11 + 152 * X ^ 12 + 172 * X ^ 13 - 96 * X ^ 14 + 256 * X ^ 15 - 32 * X ^ 17 : PowerSeries ℤ)) : PowerSeries ℤ) =
      (X ^ 0 : PowerSeries ℤ) * C (1 : ℤ) + (X ^ 4 : PowerSeries ℤ) * C (6 : ℤ) + (X ^ 5 : PowerSeries ℤ) * C (7 : ℤ) + (X ^ 6 : PowerSeries ℤ) * C (14 : ℤ) + (X ^ 7 : PowerSeries ℤ) * C (-7 : ℤ) + (X ^ 8 : PowerSeries ℤ) * C (-152 : ℤ) + (X ^ 9 : PowerSeries ℤ) * C (124 : ℤ) + (X ^ 10 : PowerSeries ℤ) * C (216 : ℤ) + (X ^ 11 : PowerSeries ℤ) * C (-124 : ℤ) + (X ^ 12 : PowerSeries ℤ) * C (152 : ℤ) + (X ^ 13 : PowerSeries ℤ) * C (172 : ℤ) + (X ^ 14 : PowerSeries ℤ) * C (-96 : ℤ) + (X ^ 15 : PowerSeries ℤ) * C (256 : ℤ) + (X ^ 17 : PowerSeries ℤ) * C (-32 : ℤ) := by
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
  have v2 : f 2 = 1 := by
    have h := congrArg (PowerSeries.coeff 2) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 2 : ℤ) : ℤ) = 1)
  have v3 : f 3 = 0 := by
    have h := congrArg (PowerSeries.coeff 3) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 3 : ℤ) : ℤ) = 0)
  have v4 : f 4 = 7 := by
    have h := congrArg (PowerSeries.coeff 4) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 4 : ℤ) : ℤ) = 7)
  have v5 : f 5 = 7 := by
    have h := congrArg (PowerSeries.coeff 5) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3, v4] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 5 : ℤ) : ℤ) = 7)
  have v6 : f 6 = 21 := by
    have h := congrArg (PowerSeries.coeff 6) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3, v4, v5] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 6 : ℤ) : ℤ) = 21)
  have v7 : f 7 = 0 := by
    have h := congrArg (PowerSeries.coeff 7) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3, v4, v5, v6] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 7 : ℤ) : ℤ) = 0)
  have v8 : f 8 = 125 := by
    have h := congrArg (PowerSeries.coeff 8) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3, v4, v5, v6, v7] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 8 : ℤ) : ℤ) = 125)
  have v9 : f 9 = 124 := by
    have h := congrArg (PowerSeries.coeff 9) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3, v4, v5, v6, v7, v8] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 9 : ℤ) : ℤ) = 124)
  have v10 : f 10 = 341 := by
    have h := congrArg (PowerSeries.coeff 10) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 10 : ℤ) : ℤ) = 341)
  have v11 : f 11 = 0 := by
    have h := congrArg (PowerSeries.coeff 11) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 11 : ℤ) : ℤ) = 0)
  have v12 : f 12 = 2029 := by
    have h := congrArg (PowerSeries.coeff 12) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 12 : ℤ) : ℤ) = 2029)
  have v13 : f 13 = 1964 := by
    have h := congrArg (PowerSeries.coeff 13) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 13 : ℤ) : ℤ) = 1964)
  have v14 : f 14 = 5517 := by
    have h := congrArg (PowerSeries.coeff 14) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 14 : ℤ) : ℤ) = 5517)
  have v15 : f 15 = 428 := by
    have h := congrArg (PowerSeries.coeff 15) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 15 : ℤ) : ℤ) = 428)
  have v16 : f 16 = 32141 := by
    have h := congrArg (PowerSeries.coeff 16) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 16 : ℤ) : ℤ) = 32141)
  have v17 : f 17 = 32140 := by
    have h := congrArg (PowerSeries.coeff 17) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 17 : ℤ) : ℤ) = 32140)
  -- the claimed recurrence at `n = 17` contradicts these values
  have hr := hX 17 (by first | decide | norm_num)
  norm_num [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17] at hr
