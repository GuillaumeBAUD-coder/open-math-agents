import Mathlib

/-!
# A227781: Least number of squares which add to -1 mod n.

Source: https://oeis.org/A227781
Credit: @laurilehtinen

OEIS Foundation, CC BY-SA 4.0. The sequence starts at modulus one.
-/

namespace OMA.S_oeis_a227781

/-- The least number of squares whose sum is minus one modulo `n`. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {k : ℕ | ∃ x : Fin k → ZMod n, ∑ i, (x i) ^ 2 = -1}

theorem main : ∀ n : ℕ, 0 < n →
    (a n = 4 ↔ 8 ∣ n) ∧ (a n = 3 ↔ n % 8 = 4) := by
  sorry

end OMA.S_oeis_a227781

