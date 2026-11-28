import Mathlib

/-!
# A259714: a(n) = Sum_{k=1..n-1}((k mod 5)*a(n-k)), a(1) = 1.

Source: https://oeis.org/A259714
Credit: @marcelopierry

Conjectures from Colin Barker, Jul 04 2015 (in the formulas of A259714):
a(n) = a(n-1)+2*a(n-2)+3*a(n-3)+4*a(n-4)+a(n-5) for n>6.
G.f.: x*(x-1)*(x^4+x^3+x^2+x+1) / ((x+1)*(x^4+3*x^3+2*x-1)).

Conventions:
* The sequence has offset 1 (data 1, 1, 3, 8, 21, 50, 129, ...). In the definition a(m+1) for
  m >= 1 is written as Sum_{j=0..m-1} ((j+1) mod 5)*a(m-j), i.e. k = j + 1; a(0) = 0 is a
  placeholder outside the sequence, which is also the zero constant term of the g.f.
* The g.f. is stated over the rationals after multiplying by its denominator (whose constant
  term is -1, so the power series is determined): the series Sum_{n>=0} a(n) x^n times
  (x+1)*(x^4+3*x^3+2*x-1) equals x*(x-1)*(x^4+x^3+x^2+x+1).
-/

namespace OMA.S_oeis_a259714

/-- A259714 (offset 1; a 0 = 0 is a placeholder). -/
def a : ℕ → ℕ
  | 0 => 0
  | n + 1 => if n = 0 then 1 else ∑ j ∈ Finset.range n, ((j + 1) % 5) * a (n - j)
decreasing_by omega

open PowerSeries in
/-- Barker's conjectures: the recurrence for n > 6 and the generating function. -/
theorem main : (∀ n : ℕ, 6 < n →
    a n = a (n - 1) + 2 * a (n - 2) + 3 * a (n - 3) + 4 * a (n - 4) + a (n - 5)) ∧
    PowerSeries.mk (fun n => (a n : ℚ)) * ((X + 1) * (X ^ 4 + 3 * X ^ 3 + 2 * X - 1)) =
      X * (X - 1) * (X ^ 4 + X ^ 3 + X ^ 2 + X + 1) := by
  sorry

end OMA.S_oeis_a259714
