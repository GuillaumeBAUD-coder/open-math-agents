import Mathlib

/-!
# A238936: Powers of 6 without the digit '0' in their decimal expansion.

Source: https://oeis.org/A238936
Credit: @darealpandaboi

Conjecture: the sequence is finite and complete, i.e. the listed terms are all of its terms.

Translation notes.
* The terms are the powers 6^k (k >= 0) whose decimal digits (Nat.digits 10) do not include 0.
* The listed data are 6^k for k = 0, 1, 2, 3, 4, 5, 6, 7, 8, 12, 17, 24, 29, 44.
  The statement says the set of terms is exactly the set of these powers. Checked by computer
  against the listed data, and that no other k < 5000 gives a zeroless power.
-/

namespace OMA.S_oeis_a238936

theorem main :
    {m : ℕ | (∃ k : ℕ, m = 6 ^ k) ∧ 0 ∉ Nat.digits 10 m} =
      ((({0, 1, 2, 3, 4, 5, 6, 7, 8, 12, 17, 24, 29, 44} : Finset ℕ).image (fun k => 6 ^ k) : Finset ℕ) : Set ℕ) := by
  sorry

end OMA.S_oeis_a238936
