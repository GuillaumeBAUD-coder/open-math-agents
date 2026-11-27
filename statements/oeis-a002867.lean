import Mathlib

/-!
# A002867: a(n) = binomial(n,floor(n/2))*(n+1)!.

Source: https://oeis.org/A002867
Credit: @Nealanio

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.
-/

namespace OMA.S_oeis_a002867

/-- The OEIS sequence `a(n) = binomial(n, floor(n/2)) * (n+1)!`. -/
def a (n : ℕ) : ℕ :=
  Nat.choose n (n / 2) * Nat.factorial (n + 1)

/-- R. J. Mathar's conjectured recurrence. The equation is cast to the integers
because it is written with subtraction. -/
theorem main :
    ∀ n : ℕ, 2 ≤ n →
      (a n : ℤ) - 2 * (a (n - 1) : ℤ) -
        4 * (n : ℤ) * ((n : ℤ) - 1) * (a (n - 2) : ℤ) = 0 := by
  sorry

end OMA.S_oeis_a002867
