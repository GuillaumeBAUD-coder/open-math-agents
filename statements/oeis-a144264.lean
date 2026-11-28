import Mathlib

/-!
# OEIS A144264: Numbers k such that A014085(k) = A014085(k+1).

Source: https://oeis.org/A144264
Credit: @unserus

OEIS: "Conjecture: the sequence is infinite."
A014085(n) is the number of primes between `n^2` and `(n+1)^2` (squares are not prime, so the
open interval is the same as the closed one). A144264 lists the `k` for which the counts for
`k` and `k + 1` agree: the number of primes between `k^2` and `(k+1)^2` equals the number of
primes between `(k+1)^2` and `(k+2)^2` (first term `1`: `{2, 3}` and `{5, 7}`).
-/

namespace OMA.S_oeis_a144264

/-- A014085: the number of primes `p` with `n^2 < p < (n+1)^2`. -/
def a014085 (n : ℕ) : ℕ := ((Finset.Ioo (n ^ 2) ((n + 1) ^ 2)).filter Nat.Prime).card

/-- The terms of A144264: `k` with `A014085(k) = A014085(k+1)`. -/
def a144264Set : Set ℕ := {k : ℕ | a014085 k = a014085 (k + 1)}

/-- A144264 is infinite. -/
theorem main : a144264Set.Infinite := by
  sorry

end OMA.S_oeis_a144264
