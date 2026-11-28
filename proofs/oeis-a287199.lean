import OMAStatements.S_oeis_a287199
import Mathlib

/-!
# OEIS A287199: Decimal representation of the diagonal from the origin to the corner of Rule 259: the conjectured package is inconsistent

The generating-function identity determines the sequence completely.  Comparing the
coefficients of `X ^ 0, …, X ^ 1` on both sides gives, one after the other,

  `a 0, …, a 1 = 1, 3`.

But the claimed closed form at `n = 1` evaluates to `0` instead of `3`.
So the conjunction of the claims is false, whatever the sequence is.
-/

open OMA.S_oeis_a287199 PowerSeries in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a287199.main) := by
  rintro ⟨hgf, -, hX, -⟩
  -- from here on the sequence is an arbitrary function `f`
  generalize a = f at hgf hX
  -- expand both polynomials into monomials
  have el : ∀ S : PowerSeries ℤ, S * (((1 - X) * (1 + X) * (1 - 2 * X) * (1 + 2 * X))) =
      C (1 : ℤ) * (S * X ^ 0) + C (-5 : ℤ) * (S * X ^ 2) + C (4 : ℤ) * (S * X ^ 4) := by
    intro S
    simp only [map_neg, map_one, map_ofNat]
    ring
  have er : ((1 + 3 * X - X ^ 2 - 12 * X ^ 3 + 12 * X ^ 5) : PowerSeries ℤ) =
      (X ^ 0 : PowerSeries ℤ) * C (1 : ℤ) + (X ^ 1 : PowerSeries ℤ) * C (3 : ℤ) + (X ^ 2 : PowerSeries ℤ) * C (-1 : ℤ) + (X ^ 3 : PowerSeries ℤ) * C (-12 : ℤ) + (X ^ 5 : PowerSeries ℤ) * C (12 : ℤ) := by
    simp only [map_neg, map_one, map_ofNat]
    ring
  rw [el, er] at hgf
  -- read off the coefficients one at a time
  have v0 : f 0 = 1 := by
    have h := congrArg (PowerSeries.coeff 0) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 0 : ℕ) : ℤ) = 1)
  have v1 : f 1 = 3 := by
    have h := congrArg (PowerSeries.coeff 1) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 1 : ℕ) : ℤ) = 3)
  -- the claimed closed form at `n = 1` contradicts these values
  have hr := hX 1 (by first | decide | norm_num)
  norm_num [v0, v1] at hr
