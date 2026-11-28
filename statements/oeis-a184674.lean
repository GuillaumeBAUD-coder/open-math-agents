import Mathlib

/-!
# The floor identity recorded in OEIS A184674

Source: https://oeis.org/A184674
Comparison sequence: https://oeis.org/A014616
Credit: @Heart-galaxy

A184674 defines a(n)=n+floor((n/2-1/(2*n))^2), with offset 1.
Mathar conjectured that a(n)=A014616(n-1) on January 29, 2011;
Spezia confirmed this on April 4, 2023. A014616 has offset 1 and the
formula b(m)=floor((m^2+6*m+1)/4). Their common domain is therefore n>=2.
At n=1 the comparison index 0 is outside the original domain of A014616;
we make no assertion there. The rational expressions and their integer
floors below are exact, without floating-point approximation.
-/

namespace OMA.S_oeis_a184674

def a (n : ℕ) : ℤ := (n : ℤ) + ⌊((n : ℚ)/2 - 1/(2*(n : ℚ)))^2⌋
def b (n : ℕ) : ℤ := ⌊((n : ℚ)^2 + 6*(n : ℚ) + 1)/4⌋

theorem main : ∀ n : ℕ, 2 ≤ n → a n = b (n-1) := by
  sorry

end OMA.S_oeis_a184674
