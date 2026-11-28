import Mathlib

/-!
# A081739: a(n) = (-1/2^n)*(A000367(2^n)+1).

Source: https://oeis.org/A081739
Credit: @xor2k

R. J. Mathar (Apr 22 2007), in the formula section of A081739:
  a(n) = A076547(n)-1 (Conjecture).

Conventions:
* A000367(k) is the numerator of the Bernoulli number B_{2k} (offset 0), so A000367(2^n) is the
  numerator of B_{2^(n+1)}, in agreement with the Mathematica and PARI programs of A081739 and
  with the name of A076547. `N n` is this numerator, taken with `Rat.num` (lowest terms, positive
  denominator) of Mathlib's `bernoulli (2 ^ (n + 1))`. The index 2^(n+1) is even and at least 2,
  where the two conventions `bernoulli` and `bernoulli'` (they differ only at index 1) agree.
* A081739 (offset 1) is defined by its name: a(n) = (-1/2^n)*(A000367(2^n)+1).
* A076547 (offset 1) is defined by its name: b(n) = (2^n-1-numerator(B(2^(n+1))))/2^n.
* Both are quotients by 2^n. The entries list integer values (A076547 says: appears to always be
  an integer), but integrality is not part of Mathar's conjecture, so both sequences are defined
  as rational numbers by the exact quotient, and the identity is stated in ℚ for every n ≥ 1
  (the offset of both entries).

Numerical check: a Python copy of the definitions (fractions module) gives for n = 1..6
  a: 0, 0, 452, 481832565076, 3336994692120829058949545155598207748188, 4183667308477313795108662587270037418426429056133620947343416969739965511482242658521291610836247844507748569589344
  b: 1, 1, 453, 481832565077, 3336994692120829058949545155598207748189, 4183667308477313795108662587270037418426429056133620947343416969739965511482242658521291610836247844507748569589345
compared with DATA of A081739 and of A076547: identical for the first 6 terms (all terms of both
DATA fields).
-/

namespace OMA.S_oeis_a081739

/-- A000367(2^n): the numerator of the Bernoulli number B_{2^(n+1)}. -/
def N (n : ℕ) : ℤ := (bernoulli (2 ^ (n + 1))).num

/-- A081739 (offset 1): a(n) = (-1/2^n)*(A000367(2^n)+1), as a rational number. -/
def a (n : ℕ) : ℚ := (-1 / 2 ^ n) * ((N n : ℚ) + 1)

/-- A076547 (offset 1): (2^n-1-numerator(B(2^(n+1))))/2^n, as a rational number. -/
def b (n : ℕ) : ℚ := (2 ^ n - 1 - (N n : ℚ)) / 2 ^ n

/-- Mathar's conjecture: a(n) = A076547(n) - 1 for every n ≥ 1. -/
theorem main : ∀ n : ℕ, 1 ≤ n → a n = b n - 1 := by
  sorry

end OMA.S_oeis_a081739
