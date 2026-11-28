import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Choose.Basic

/-!
# Mathar's recurrence for OEIS A127363

The sum uses integer powers of -4 and the natural quotient k/2.
The sequence starts at zero, so the four-term recurrence is stated from n = 3.
Source: https://oeis.org/A127363 (OEIS Foundation, CC BY-SA 4.0).
Credit: @yukimiyazaki
-/

namespace OMA.S_oeis_a127363

def a (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n+1), (n.choose (k/2) : ℤ) * (-4 : ℤ)^(n-k)

theorem main : ∀ n : ℕ, 3 ≤ n →
    4*(n : ℤ)*a n + (17*(n : ℤ)-8)*a (n-1) +
      2*(-8*(n : ℤ)-1)*a (n-2) + 68*(-(n : ℤ)+2)*a (n-3) = 0 := by
  sorry

end OMA.S_oeis_a127363
