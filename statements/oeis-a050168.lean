import Mathlib

/-!
OEIS A050168, by Clark Kimberling. The sequence starts at index zero.
R. J. Mathar proposed the recurrence on November 26, 2012.
The first index with all four terms defined is three.

Source: https://oeis.org/A050168 (OEIS Foundation, CC BY-SA 4.0).
-/
namespace OMA.S_oeis_a050168

def a (n : ℕ) : ℕ :=
  if n = 0 then 1 else n.choose (n / 2) + (n - 1).choose (n / 2)

theorem main : ∀ n : ℕ, 3 ≤ n →
    ((n : ℤ) + 1) * a n + ((n : ℤ) - 3) * a (n - 1) +
      2 * (-2 * (n : ℤ) + 1) * a (n - 2) +
      4 * (-(n : ℤ) + 3) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a050168
