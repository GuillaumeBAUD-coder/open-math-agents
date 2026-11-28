import OMAStatements.S_oeis_a285833
import Mathlib

/-!
# OEIS A285833: Barker's conjectures for the diagonal (origin to corner, base 10) of Rule 107: the conjectured package is inconsistent

The generating-function identity determines the sequence completely.  Comparing the
coefficients of `X ^ 0, …, X ^ 8` on both sides gives, one after the other,

  `a 0, …, a 8 = 1, 11, 110, 1111, 1100, 111111, 11000, 11111111, 11110000`.

But the claimed recurrence at `n = 8` evaluates to `110000` instead of `11110000`.
So the conjunction of the claims is false, whatever the sequence is.
-/

open OMA.S_oeis_a285833 PowerSeries in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a285833.main) := by
  rintro ⟨hgf, hX⟩
  -- from here on the sequence is an arbitrary function `f`
  generalize a = f at hgf hX
  -- expand both polynomials into monomials
  have el : ∀ S : PowerSeries ℤ, S * (((1 - X) * (1 + X) * (1 - 10 * X) * (1 + 10 * X) * (1 - 10 * X ^ 2))) =
      C (1 : ℤ) * (S * X ^ 0) + C (-111 : ℤ) * (S * X ^ 2) + C (1110 : ℤ) * (S * X ^ 4) + C (-1000 : ℤ) * (S * X ^ 6) := by
    intro S
    simp only [map_neg, map_one, map_ofNat]
    ring
  have er : ((1 + 11 * X - X ^ 2 - 110 * X ^ 3 - 10000 * X ^ 4 + 10000 * X ^ 6 + 11000000 * X ^ 8 - 111000000 * X ^ 10 + 100000000 * X ^ 12) : PowerSeries ℤ) =
      (X ^ 0 : PowerSeries ℤ) * C (1 : ℤ) + (X ^ 1 : PowerSeries ℤ) * C (11 : ℤ) + (X ^ 2 : PowerSeries ℤ) * C (-1 : ℤ) + (X ^ 3 : PowerSeries ℤ) * C (-110 : ℤ) + (X ^ 4 : PowerSeries ℤ) * C (-10000 : ℤ) + (X ^ 6 : PowerSeries ℤ) * C (10000 : ℤ) + (X ^ 8 : PowerSeries ℤ) * C (11000000 : ℤ) + (X ^ 10 : PowerSeries ℤ) * C (-111000000 : ℤ) + (X ^ 12 : PowerSeries ℤ) * C (100000000 : ℤ) := by
    simp only [map_neg, map_one, map_ofNat]
    ring
  rw [el, er] at hgf
  -- read off the coefficients one at a time
  have v0 : f 0 = 1 := by
    have h := congrArg (PowerSeries.coeff 0) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 0 : ℕ) : ℤ) = 1)
  have v1 : f 1 = 11 := by
    have h := congrArg (PowerSeries.coeff 1) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 1 : ℕ) : ℤ) = 11)
  have v2 : f 2 = 110 := by
    have h := congrArg (PowerSeries.coeff 2) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 2 : ℕ) : ℤ) = 110)
  have v3 : f 3 = 1111 := by
    have h := congrArg (PowerSeries.coeff 3) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 3 : ℕ) : ℤ) = 1111)
  have v4 : f 4 = 1100 := by
    have h := congrArg (PowerSeries.coeff 4) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 4 : ℕ) : ℤ) = 1100)
  have v5 : f 5 = 111111 := by
    have h := congrArg (PowerSeries.coeff 5) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3, v4] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 5 : ℕ) : ℤ) = 111111)
  have v6 : f 6 = 11000 := by
    have h := congrArg (PowerSeries.coeff 6) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3, v4, v5] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 6 : ℕ) : ℤ) = 11000)
  have v7 : f 7 = 11111111 := by
    have h := congrArg (PowerSeries.coeff 7) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3, v4, v5, v6] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 7 : ℕ) : ℤ) = 11111111)
  have v8 : f 8 = 11110000 := by
    have h := congrArg (PowerSeries.coeff 8) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3, v4, v5, v6, v7] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 8 : ℕ) : ℤ) = 11110000)
  -- the claimed recurrence at `n = 8` contradicts these values
  have hr := hX 8 (by first | decide | norm_num)
  norm_num [v0, v1, v2, v3, v4, v5, v6, v7, v8] at hr
