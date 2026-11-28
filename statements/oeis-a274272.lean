import Mathlib

/-!
# A274272: closed form and recurrence

Source: https://oeis.org/A274272
Credit: @ivillar

The number of partitions of 5^n into at most four parts, i.e. the coefficient of x^(5^n) in
1/((1-x)*(1-x^2)*(1-x^3)*(1-x^4)) (offset 0; data 1, 6, 185, 15246, 1736385, ...). The entry
conjectures a(n) = (57 + 8*(-1)^n + 63*5^n + 3*5^(1+2*n) + 125^n)/144 and
a(n) = 155*a(n-1) - 3874*a(n-2) + 15470*a(n-3) + 3875*a(n-4) - 15625*a(n-5) for n > 4.

Status: conjectures recorded in the entry.

Formalization notes:
* A partition of N into at most four parts is written N = a + b + c + d with a >= b >= c >= d >= 0
  (padding with zero parts); it is determined by d in [0, floor(N/4)], c in [d, floor((N - d)/3)]
  and b in [c, floor((N - c - d)/2)], and `a` counts these triples for N = 5^n.
* The closed form is stated multiplied out and over ℤ (it involves (-1)^n):
  144 * a(n) = 57 + 8*(-1)^n + 63*5^n + 3*5^(1+2*n) + 125^n. The recurrence is stated over ℤ.
* The conjectured generating function (1-149*x+3129*x^2-5655*x^3-6750*x^4) /
  ((1-x)*(1+x)*(1-5*x)*(1-25*x)*(1-125*x)) is the rational function determined by the recurrence and
  the initial terms; it is not restated.
-/

namespace OMA.S_oeis_a274272

/-- A274272: the number of partitions `5^n = a + b + c + d` with `a ≥ b ≥ c ≥ d ≥ 0`. -/
def a (n : ℕ) : ℕ :=
  ∑ d ∈ Finset.range (5 ^ n / 4 + 1), ∑ c ∈ Finset.Icc d ((5 ^ n - d) / 3),
    ∑ _b ∈ Finset.Icc c ((5 ^ n - c - d) / 2), 1

/-- The conjectured closed form and recurrence (for `n > 4`) of A274272. -/
theorem main :
    (∀ n : ℕ,
      144 * (a n : ℤ) = 57 + 8 * (-1) ^ n + 63 * 5 ^ n + 3 * 5 ^ (1 + 2 * n) + 125 ^ n) ∧
    (∀ n : ℕ, 4 < n →
      (a n : ℤ) = 155 * a (n - 1) - 3874 * a (n - 2) + 15470 * a (n - 3) + 3875 * a (n - 4) -
        15625 * a (n - 5)) := by
  sorry

end OMA.S_oeis_a274272
