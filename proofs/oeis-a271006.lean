import OMAStatements.S_oeis_a271006
import Mathlib

/-!
# A271006: Partial sums of the number of active (ON, black) cells in n-th stage of growth of two-dimensional cellular automaton defined by Rule 245, based on the 5-celled von Neumann neighborhood.: the conjectured package is inconsistent

The generating-function identity determines the sequence completely.  Comparing the
coefficients of `X ^ 0, …, X ^ 11` on both sides gives, one after the other,

  `a 0, …, a 11 = 1, 9, 13, 57, 70, 182, 207, 415, 452, 792, 841, 1345`.

But the claimed recurrence at `n = 11` evaluates to `1349` instead of `1345`.
So the conjunction of the claims is false, whatever the sequence is.
-/

open OMA.S_oeis_a271006 PowerSeries in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a271006.main) := by
  rintro ⟨-, -, -, hX, hgf⟩
  -- from here on the sequence is an arbitrary function `f`
  generalize a = f at hgf hX
  -- expand both polynomials into monomials
  have el : ∀ S : PowerSeries ℤ, S * (((1 - X) ^ 4 * (1 + X) ^ 3)) =
      C (1 : ℤ) * (S * X ^ 0) + C (-1 : ℤ) * (S * X ^ 1) + C (-3 : ℤ) * (S * X ^ 2) + C (3 : ℤ) * (S * X ^ 3) + C (3 : ℤ) * (S * X ^ 4) + C (-3 : ℤ) * (S * X ^ 5) + C (-1 : ℤ) * (S * X ^ 6) + C (1 : ℤ) * (S * X ^ 7) := by
    intro S
    simp only [map_neg, map_one, map_ofNat]
    ring
  have er : (((1 + 8 * X + X ^ 2 + 20 * X ^ 3 + 4 * X ^ 4 + 4 * X ^ 5 - 3 * X ^ 6 - 4 * X ^ 7 - 3 * X ^ 8 + 8 * X ^ 9 - 4 * X ^ 11 : PowerSeries ℤ)) : PowerSeries ℤ) =
      (X ^ 0 : PowerSeries ℤ) * C (1 : ℤ) + (X ^ 1 : PowerSeries ℤ) * C (8 : ℤ) + (X ^ 2 : PowerSeries ℤ) * C (1 : ℤ) + (X ^ 3 : PowerSeries ℤ) * C (20 : ℤ) + (X ^ 4 : PowerSeries ℤ) * C (4 : ℤ) + (X ^ 5 : PowerSeries ℤ) * C (4 : ℤ) + (X ^ 6 : PowerSeries ℤ) * C (-3 : ℤ) + (X ^ 7 : PowerSeries ℤ) * C (-4 : ℤ) + (X ^ 8 : PowerSeries ℤ) * C (-3 : ℤ) + (X ^ 9 : PowerSeries ℤ) * C (8 : ℤ) + (X ^ 11 : PowerSeries ℤ) * C (-4 : ℤ) := by
    simp only [map_neg, map_one, map_ofNat]
    ring
  rw [el, er] at hgf
  -- read off the coefficients one at a time
  have v0 : f 0 = 1 := by
    have h := congrArg (PowerSeries.coeff 0) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 0 : ℤ) : ℤ) = 1)
  have v1 : f 1 = 9 := by
    have h := congrArg (PowerSeries.coeff 1) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 1 : ℤ) : ℤ) = 9)
  have v2 : f 2 = 13 := by
    have h := congrArg (PowerSeries.coeff 2) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 2 : ℤ) : ℤ) = 13)
  have v3 : f 3 = 57 := by
    have h := congrArg (PowerSeries.coeff 3) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 3 : ℤ) : ℤ) = 57)
  have v4 : f 4 = 70 := by
    have h := congrArg (PowerSeries.coeff 4) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 4 : ℤ) : ℤ) = 70)
  have v5 : f 5 = 182 := by
    have h := congrArg (PowerSeries.coeff 5) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3, v4] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 5 : ℤ) : ℤ) = 182)
  have v6 : f 6 = 207 := by
    have h := congrArg (PowerSeries.coeff 6) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3, v4, v5] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 6 : ℤ) : ℤ) = 207)
  have v7 : f 7 = 415 := by
    have h := congrArg (PowerSeries.coeff 7) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3, v4, v5, v6] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 7 : ℤ) : ℤ) = 415)
  have v8 : f 8 = 452 := by
    have h := congrArg (PowerSeries.coeff 8) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3, v4, v5, v6, v7] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 8 : ℤ) : ℤ) = 452)
  have v9 : f 9 = 792 := by
    have h := congrArg (PowerSeries.coeff 9) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3, v4, v5, v6, v7, v8] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 9 : ℤ) : ℤ) = 792)
  have v10 : f 10 = 841 := by
    have h := congrArg (PowerSeries.coeff 10) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 10 : ℤ) : ℤ) = 841)
  have v11 : f 11 = 1345 := by
    have h := congrArg (PowerSeries.coeff 11) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 11 : ℤ) : ℤ) = 1345)
  -- the claimed recurrence at `n = 11` contradicts these values
  have hr := hX 11 (by first | decide | norm_num)
  norm_num [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11] at hr
