import Mathlib

/-!
# A007531: a(n) = n*(n-1)*(n-2) (or n!/(n-3)!)

Source: https://oeis.org/A007531
Credit: @niclorusso

Conjecture (Ed Pegg Jr, in the comments of A007531): n^3 - n = k! has a solution if and only if n
is 2, 3, 5 or 9 (when k is 3, 4, 5 and 6).

Conventions:
* n and k are natural numbers. For an integer n <= 1, n^3 - n = (n - 1) n (n + 1) <= 0 < k!, so
  restricting n to the natural numbers loses nothing; in particular n^3 - n never truncates here
  (n <= n^3 for every natural n).
* "has a solution" means: there is a natural number k with n^3 - n = k!.
-/

namespace OMA.S_oeis_a007531

/-- Pegg's conjecture on A007531: `n^3 - n` is a factorial exactly when `n` is 2, 3, 5 or 9. -/
theorem main : {n : ℕ | ∃ k : ℕ, n ^ 3 - n = k.factorial} = {2, 3, 5, 9} := by
  sorry

end OMA.S_oeis_a007531
