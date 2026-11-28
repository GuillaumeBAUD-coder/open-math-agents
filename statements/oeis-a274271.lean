import Mathlib

/-!
# A274271: closed form and recurrence

Source: https://oeis.org/A274271
Credit: @ivillar

The number of partitions of 3^n into at most four parts, i.e. the coefficient of x^(3^n) in
1/((1-x)*(1-x^2)*(1-x^3)*(1-x^4)) (offset 0; data 1, 3, 18, 225, 4410, 105903, ...). The entry
conjectures a(n) = ((3+3^n)^2*(9+3^n))/144 for n > 1 and
a(n) = 40*a(n-1) - 390*a(n-2) + 1080*a(n-3) - 729*a(n-4) for n > 4.

Status: conjectures recorded in the entry.

Formalization notes:
* A partition of N into at most four parts is written N = a + b + c + d with a >= b >= c >= d >= 0
  (padding with zero parts); it is determined by d in [0, floor(N/4)], c in [d, floor((N - d)/3)]
  and b in [c, floor((N - c - d)/2)], and `a` counts these triples for N = 3^n.
* The closed form is stated multiplied out: 144 * a(n) = (3 + 3^n)^2 * (9 + 3^n). The recurrence is
  stated over ℤ.
* The conjectured generating function (1-37*x+288*x^2-405*x^3-81*x^4) /
  ((1-x)*(1-3*x)*(1-9*x)*(1-27*x)) is the rational function determined by the recurrence and the
  initial terms; it is not restated.
-/

namespace OMA.S_oeis_a274271

/-- A274271: the number of partitions `3^n = a + b + c + d` with `a ≥ b ≥ c ≥ d ≥ 0`. -/
def a (n : ℕ) : ℕ :=
  ∑ d ∈ Finset.range (3 ^ n / 4 + 1), ∑ c ∈ Finset.Icc d ((3 ^ n - d) / 3),
    ∑ _b ∈ Finset.Icc c ((3 ^ n - c - d) / 2), 1

/-- The conjectured closed form (for `n > 1`) and recurrence (for `n > 4`) of A274271. -/
theorem main :
    (∀ n : ℕ, 1 < n → 144 * a n = (3 + 3 ^ n) ^ 2 * (9 + 3 ^ n)) ∧
    (∀ n : ℕ, 4 < n →
      (a n : ℤ) = 40 * a (n - 1) - 390 * a (n - 2) + 1080 * a (n - 3) - 729 * a (n - 4)) := by
  sorry

end OMA.S_oeis_a274271
