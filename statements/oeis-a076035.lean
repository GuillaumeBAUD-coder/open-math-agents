import Mathlib

/-!
# The relation between OEIS A076035 and A076025

Source: https://oeis.org/A076035
Source data: https://raw.githubusercontent.com/oeis/oeisdata/main/seq/A076/A076035.seq
Reference sequence: https://oeis.org/A076025
Credit: @Heart-galaxy

A076035 and A076025 are the coefficients of the two formal power series
specified in the OEIS entries, with C the ordinary Catalan series. The
claim is for positive indices because both constant terms are 1.

R. J. Mathar proposed the identity in 2022. Sela Fried noted in the OEIS
entry in 2025 that it follows from the two generating functions.
-/

namespace OMA.S_oeis_a076035

open PowerSeries

noncomputable def catalanGF : PowerSeries ℚ := map (Nat.castRingHom ℚ) catalanSeries

noncomputable def denominator : PowerSeries ℚ := 1 - 4 * X * catalanGF

noncomputable def a (n : ℕ) : ℚ := coeff n (denominator⁻¹)

noncomputable def b (n : ℕ) : ℚ :=
  coeff n ((1 - 3 * X * catalanGF) * denominator⁻¹)

theorem main : ∀ n : ℕ, 0 < n → a n = 4 * b n := by
  sorry

end OMA.S_oeis_a076035
