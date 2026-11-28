import OMAStatements.S_oeis_a002414

-- Problem: A002414, octagonal pyramidal numbers, generating function x*(1+5x)/(1-x)^4.
-- Expanding (1 - x)^4, the coefficient of x^(n+4) on the left is the fourth difference of the
-- cubic a, which is zero; the coefficients of x^0 .. x^3 are 0, 1, 5, 0.

namespace OMA.A002414

open PowerSeries OMA.S_oeis_a002414

lemma diff4 (n : ℕ) :
    a (n + 4) - 4 * a (n + 3) + 6 * a (n + 2) - 4 * a (n + 1) + a n = 0 := by
  simp only [a]
  push_cast
  ring

lemma gf :
    PowerSeries.mk a * (1 - PowerSeries.X) ^ 4 =
      (PowerSeries.X : PowerSeries ℚ) * (1 + 5 * PowerSeries.X) := by
  set A := PowerSeries.mk a with hA
  have hl : A * (1 - PowerSeries.X) ^ 4 =
      A - (A * X ^ 1 + A * X ^ 1 + A * X ^ 1 + A * X ^ 1) +
        (A * X ^ 2 + A * X ^ 2 + A * X ^ 2 + A * X ^ 2 + A * X ^ 2 + A * X ^ 2) -
        (A * X ^ 3 + A * X ^ 3 + A * X ^ 3 + A * X ^ 3) + A * X ^ 4 := by ring
  have hr : (PowerSeries.X : PowerSeries ℚ) * (1 + 5 * PowerSeries.X) =
      X ^ 1 + (X ^ 2 + X ^ 2 + X ^ 2 + X ^ 2 + X ^ 2) := by ring
  rw [hl, hr, hA]
  ext n
  simp only [map_add, map_sub, coeff_mul_X_pow', coeff_mk, coeff_X_pow]
  rcases n with _ | _ | _ | _ | n
  · simp [a]
  · simp [a] <;> norm_num
  · simp [a] <;> norm_num
  · simp [a] <;> norm_num
  · have h := diff4 n
    have e1 : n + 1 + 1 + 1 + 1 - 1 = n + 3 := by omega
    have e2 : n + 1 + 1 + 1 + 1 - 2 = n + 2 := by omega
    have e3 : n + 1 + 1 + 1 + 1 - 3 = n + 1 := by omega
    have e4 : n + 1 + 1 + 1 + 1 - 4 = n := by omega
    simp only [e1, e2, e3, e4, show 1 ≤ n + 1 + 1 + 1 + 1 by omega,
      show 2 ≤ n + 1 + 1 + 1 + 1 by omega, show 3 ≤ n + 1 + 1 + 1 + 1 by omega,
      show 4 ≤ n + 1 + 1 + 1 + 1 by omega, if_true,
      show n + 1 + 1 + 1 + 1 ≠ 1 by omega, show n + 1 + 1 + 1 + 1 ≠ 2 by omega, if_false]
    have e : n + 1 + 1 + 1 + 1 = n + 4 := by omega
    rw [e]
    linarith

end OMA.A002414

theorem OMA.solution : type_of% @OMA.S_oeis_a002414.main := OMA.A002414.gf
