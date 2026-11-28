import OMAStatements.S_oeis_a270082
import Mathlib

/-!
# A270082: First differences of number of active (ON, black) cells in n-th stage of growth of two-dimensional cellular automaton defined by Rule 62, based on the 5-celled von Neumann neighborhood.: the conjectured package is inconsistent

The generating-function identity determines the sequence completely.  Comparing the
coefficients of `X ^ 0, …, X ^ 11` on both sides gives, one after the other,

  `a 0, …, a 11 = 4, 7, 8, 12, 12, 24, 4, 28, 12, 44, 4, 44`.

But the claimed recurrence at `n = 11` evaluates to `48` instead of `44`.
So the conjunction of the claims is false, whatever the sequence is.
-/

open OMA.S_oeis_a270082 PowerSeries in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a270082.main) := by
  rintro ⟨hX, hgf⟩
  -- from here on the sequence is an arbitrary function `f`
  generalize a = f at hgf hX
  -- expand both polynomials into monomials
  have el : ∀ S : PowerSeries ℤ, S * (((1 - X) ^ 2 * (1 + X) ^ 2 * (1 + X ^ 2))) =
      C (1 : ℤ) * (S * X ^ 0) + C (-1 : ℤ) * (S * X ^ 2) + C (-1 : ℤ) * (S * X ^ 4) + C (1 : ℤ) * (S * X ^ 6) := by
    intro S
    simp only [map_neg, map_one, map_ofNat]
    ring
  have er : (((4 + 7 * X + 4 * X ^ 2 + 5 * X ^ 3 + 5 * X ^ 5 - 12 * X ^ 6 - X ^ 7 + 4 * X ^ 8 + 4 * X ^ 9 - 4 * X ^ 11 : PowerSeries ℤ)) : PowerSeries ℤ) =
      (X ^ 0 : PowerSeries ℤ) * C (4 : ℤ) + (X ^ 1 : PowerSeries ℤ) * C (7 : ℤ) + (X ^ 2 : PowerSeries ℤ) * C (4 : ℤ) + (X ^ 3 : PowerSeries ℤ) * C (5 : ℤ) + (X ^ 5 : PowerSeries ℤ) * C (5 : ℤ) + (X ^ 6 : PowerSeries ℤ) * C (-12 : ℤ) + (X ^ 7 : PowerSeries ℤ) * C (-1 : ℤ) + (X ^ 8 : PowerSeries ℤ) * C (4 : ℤ) + (X ^ 9 : PowerSeries ℤ) * C (4 : ℤ) + (X ^ 11 : PowerSeries ℤ) * C (-4 : ℤ) := by
    simp only [map_neg, map_one, map_ofNat]
    ring
  rw [el, er] at hgf
  -- read off the coefficients one at a time
  have v0 : f 0 = 4 := by
    have h := congrArg (PowerSeries.coeff 0) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 0 : ℤ) : ℤ) = 4)
  have v1 : f 1 = 7 := by
    have h := congrArg (PowerSeries.coeff 1) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 1 : ℤ) : ℤ) = 7)
  have v2 : f 2 = 8 := by
    have h := congrArg (PowerSeries.coeff 2) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 2 : ℤ) : ℤ) = 8)
  have v3 : f 3 = 12 := by
    have h := congrArg (PowerSeries.coeff 3) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 3 : ℤ) : ℤ) = 12)
  have v4 : f 4 = 12 := by
    have h := congrArg (PowerSeries.coeff 4) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 4 : ℤ) : ℤ) = 12)
  have v5 : f 5 = 24 := by
    have h := congrArg (PowerSeries.coeff 5) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3, v4] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 5 : ℤ) : ℤ) = 24)
  have v6 : f 6 = 4 := by
    have h := congrArg (PowerSeries.coeff 6) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3, v4, v5] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 6 : ℤ) : ℤ) = 4)
  have v7 : f 7 = 28 := by
    have h := congrArg (PowerSeries.coeff 7) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3, v4, v5, v6] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 7 : ℤ) : ℤ) = 28)
  have v8 : f 8 = 12 := by
    have h := congrArg (PowerSeries.coeff 8) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3, v4, v5, v6, v7] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 8 : ℤ) : ℤ) = 12)
  have v9 : f 9 = 44 := by
    have h := congrArg (PowerSeries.coeff 9) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3, v4, v5, v6, v7, v8] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 9 : ℤ) : ℤ) = 44)
  have v10 : f 10 = 4 := by
    have h := congrArg (PowerSeries.coeff 10) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 10 : ℤ) : ℤ) = 4)
  have v11 : f 11 = 44 := by
    have h := congrArg (PowerSeries.coeff 11) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 11 : ℤ) : ℤ) = 44)
  -- the claimed recurrence at `n = 11` contradicts these values
  have hr := hX 11 (by first | decide | norm_num)
  norm_num [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11] at hr
