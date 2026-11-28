import Mathlib

namespace OMA.S_mse_3241568

/-- The unnormalized sinc function `sinc(x) = sin(x) / x` (with `sinc(0) = 1`). -/
noncomputable def sinc (x : ℝ) : ℝ :=
  if x = 0 then 1 else Real.sin x / x

/-- Conjectured asymptotic expansion from Math Stack Exchange #3241568:
`∏_{k=n}^∞ sinc(2^{-k} π) = 1 - (2π^2/9) 4^{-n} + (38π^4/2025) 4^{-2n} - (2332π^6/2679075) 4^{-3n} + (265618π^8/10247461875) 4^{-4n} + O(4^{-5n})`
as `n → ∞`. -/
theorem main :
    (fun n : ℕ =>
      (∏' k : ℕ, sinc ((2 : ℝ) ^ (-(n + k : ℤ)) * Real.pi)) -
        (1 - (2 * Real.pi ^ 2 / 9) * (4 : ℝ) ^ (-(n : ℤ)) +
          (38 * Real.pi ^ 4 / 2025) * (4 : ℝ) ^ (-(2 * n : ℤ)) -
          (2332 * Real.pi ^ 6 / 2679075) * (4 : ℝ) ^ (-(3 * n : ℤ)) +
          (265618 * Real.pi ^ 8 / 10247461875) * (4 : ℝ) ^ (-(4 * n : ℤ))))
      =O[Filter.atTop] (fun n : ℕ => (4 : ℝ) ^ (-(5 * n : ℤ))) := by sorry

end OMA.S_mse_3241568
