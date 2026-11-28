import Mathlib

/-!
# A004018: Theta series of square lattice (or number of ways of writing n as a sum of 2 squares). Often denoted by r(n) or r_2(n).

Source: https://oeis.org/A004018
Credit: @azmiozgen

Conjecture (Simon Plouffe), from the entry: Sum_{k>=0} a(k) / exp(k*Pi) = Pi^(1/2)/Gamma(3/4)^2
(= A175574). The entry notes that it is true (see the Fried link).

Formalization notes:
* a(n) is the number of ordered pairs (x, y) of integers, signs and order counted, with
  x^2 + y^2 = n (offset 0, a(0) = 1). Both coordinates lie in [-n, n]; the count runs over
  x = i - n, y = j - n for i, j in [0, 2n].
* The infinite sum is stated as `HasSum` of a(k) / exp(k * Pi) over k >= 0 in the reals.
* Controls: the definition gives a(0..10) = 1, 4, 4, 0, 4, 8, 0, 0, 4, 4, 8, as in the entry.
-/

namespace OMA.S_oeis_a004018

/-- A004018(n): the number of pairs `(x, y) ∈ ℤ²` with `x ^ 2 + y ^ 2 = n`. -/
def a (n : ℕ) : ℕ :=
  ((Finset.range (2 * n + 1) ×ˢ Finset.range (2 * n + 1)).filter
    (fun p : ℕ × ℕ => ((p.1 : ℤ) - n) ^ 2 + ((p.2 : ℤ) - n) ^ 2 = n)).card

/-- Plouffe's identity: `∑_{k ≥ 0} a(k) e^{-kπ} = √π / Γ(3/4)²`. -/
theorem main :
    HasSum (fun k : ℕ => (a k : ℝ) / Real.exp (k * Real.pi))
      (Real.sqrt Real.pi / Real.Gamma (3 / 4) ^ 2) := by
  sorry

end OMA.S_oeis_a004018
