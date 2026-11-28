import OMAStatements.S_oeis_a290527
import Mathlib

/-!
# OEIS A290527: Barker's conjectures for the diagonal (corner to origin, base 2) of Rule 833: the conjectured package is inconsistent

The generating-function identity determines the sequence completely.  Comparing the
coefficients of `X ^ 0, …, X ^ 6` on both sides gives, one after the other,

  `a 0, …, a 6 = 1, 2, 5, 15, 24, 63, 112`.

But the claimed recurrence at `n = 6` evaluates to `106` instead of `112`.
So the conjunction of the claims is false, whatever the sequence is.
-/

open OMA.S_oeis_a290527 PowerSeries in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a290527.main) := by
  rintro ⟨hgf, -, -, hX⟩
  -- from here on the sequence is an arbitrary function `f`
  generalize a = f at hgf hX
  -- expand both polynomials into monomials
  have el : ∀ S : PowerSeries ℤ, S * (((1 - X) * (1 + X) * (1 - 2 * X) * (1 - 2 * X ^ 2))) =
      C (1 : ℤ) * (S * X ^ 0) + C (-2 : ℤ) * (S * X ^ 1) + C (-3 : ℤ) * (S * X ^ 2) + C (6 : ℤ) * (S * X ^ 3) + C (2 : ℤ) * (S * X ^ 4) + C (-4 : ℤ) * (S * X ^ 5) := by
    intro S
    simp only [map_neg, map_one, map_ofNat]
    ring
  have er : ((1 - 2 * X ^ 2 + 5 * X ^ 3 - 7 * X ^ 4 + 6 * X ^ 6 - 4 * X ^ 7) : PowerSeries ℤ) =
      (X ^ 0 : PowerSeries ℤ) * C (1 : ℤ) + (X ^ 2 : PowerSeries ℤ) * C (-2 : ℤ) + (X ^ 3 : PowerSeries ℤ) * C (5 : ℤ) + (X ^ 4 : PowerSeries ℤ) * C (-7 : ℤ) + (X ^ 6 : PowerSeries ℤ) * C (6 : ℤ) + (X ^ 7 : PowerSeries ℤ) * C (-4 : ℤ) := by
    simp only [map_neg, map_one, map_ofNat]
    ring
  rw [el, er] at hgf
  -- read off the coefficients one at a time
  have v0 : f 0 = 1 := by
    have h := congrArg (PowerSeries.coeff 0) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 0 : ℕ) : ℤ) = 1)
  have v1 : f 1 = 2 := by
    have h := congrArg (PowerSeries.coeff 1) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 1 : ℕ) : ℤ) = 2)
  have v2 : f 2 = 5 := by
    have h := congrArg (PowerSeries.coeff 2) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 2 : ℕ) : ℤ) = 5)
  have v3 : f 3 = 15 := by
    have h := congrArg (PowerSeries.coeff 3) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 3 : ℕ) : ℤ) = 15)
  have v4 : f 4 = 24 := by
    have h := congrArg (PowerSeries.coeff 4) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 4 : ℕ) : ℤ) = 24)
  have v5 : f 5 = 63 := by
    have h := congrArg (PowerSeries.coeff 5) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3, v4] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 5 : ℕ) : ℤ) = 63)
  have v6 : f 6 = 112 := by
    have h := congrArg (PowerSeries.coeff 6) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3, v4, v5] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 6 : ℕ) : ℤ) = 112)
  -- the claimed recurrence at `n = 6` contradicts these values
  have hr := hX 6 (by first | decide | norm_num)
  norm_num [v0, v1, v2, v3, v4, v5, v6] at hr
