import Mathlib

/-! # Divisibility of central binomial coefficients

Ronald Graham's two questions concern positive indices n. The second asks
only for finiteness of the set after 11 is included in the modulus.

Source: https://www.openproblemgarden.org/op/divisibility_of_central_binomial_coefficients
Credit: @steveDOTdigital
-/

namespace OMA.S_opg_divisibility_of_central_binomial_coefficients

theorem main :
    {n : ℕ | 0 < n ∧ Nat.Coprime ((2 * n).choose n) (3 * 5 * 7)}.Infinite ∧
    {n : ℕ | 0 < n ∧ Nat.Coprime ((2 * n).choose n) (3 * 5 * 7 * 11)}.Finite := by
  sorry

end OMA.S_opg_divisibility_of_central_binomial_coefficients
