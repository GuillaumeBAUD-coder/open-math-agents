import Mathlib

/-!
# OEIS A308158: Barker's conjectures for the sum of the smallest sides of the isosceles triangles

Source: https://oeis.org/A308158 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A308158 (Wesley Ivan Hurt, May 14 2019), offset 1: Sum of the smallest side lengths of all
integer-sided isosceles triangles with perimeter n.
Formula section:
a(n) = Sum_{k=1..floor(n/3)} Sum_{i=k..floor((n-k)/2)} sign(floor((i+k)/(n-i-k+1))) *
([i=k] + [i=n-i-k] - [k=n-i-k]) * k, where [] is the Iverson bracket.
Conjectures from Colin Barker, May 15 2019:
G.f.: x^3*(1 + x^2 + x^3 + x^4 + x^5) / ((1 - x)^3*(1 + x)^2*(1 + x^2)^2*(1 + x + x^2)).
a(n) = a(n-3) + 2*a(n-4) - 2*a(n-7) - a(n-8) + a(n-11) for n>11.

Formalization notes:
* The definition follows the entry's formula line: the triangles are k <= i <= n - k - i, the
  factor sign(floor((i+k)/(n-i-k+1))) is 1 exactly when k + i > n - k - i (the triangle
  inequality) and 0 otherwise, the Iverson brackets select the isosceles triangles (each counted
  once, equilateral ones included), and k is the smallest side. The floor of the quotient of two
  natural numbers is natural-number division (the denominator n - i - k + 1 is at least 1 in the
  range of summation), sign is Int.sign, and [P] is if P then 1 else 0.
* The formula gives a(0) = 0 (empty sum), so A(x) = Sum_{n >= 0} a(n) x^n is the entry's
  generating function Sum_{n >= 1} a(n) x^n; it is stated as A * D = N in the formal power series
  ring over the integers, which is equivalent because D has constant term 1. The recurrence is
  stated in the integers.
* Controls from the entry, proved in the proof file: a(1..24) = 0, 0, 1, 0, 1, 2, 3, 2, 4, 5, 7,
  6, 8, 10, 13, 11, 14, 17, 20, 18, 22, 25, 29, 27.
-/

namespace OMA.S_oeis_a308158

open PowerSeries

/-- A308158(n), by the entry's formula (the empty sum gives a(0) = 0). -/
def a (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.Icc 1 (n / 3), ∑ i ∈ Finset.Icc k ((n - k) / 2),
    Int.sign (((i + k) / (n - i - k + 1) : ℕ) : ℤ) *
      ((if i = k then 1 else 0) + (if i = n - i - k then 1 else 0) -
        (if k = n - i - k then 1 else 0)) * (k : ℤ)

/-- Barker's generating function and recurrence. -/
theorem main :
    mk a * ((1 - X) ^ 3 * (1 + X) ^ 2 * (1 + X ^ 2) ^ 2 * (1 + X + X ^ 2)) =
      X ^ 3 * (1 + X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5) ∧
    (∀ n : ℕ, 11 < n → a n = a (n - 3) + 2 * a (n - 4) - 2 * a (n - 7) - a (n - 8) + a (n - 11)) := by
  sorry

end OMA.S_oeis_a308158
