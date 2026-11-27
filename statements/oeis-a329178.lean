import Mathlib

/-!
# OEIS A329178: Barker's generating function and recurrence for sums of Padovan products

Source: https://oeis.org/A329178 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A329178 (David Nacin, Nov 08 2019), offset 0: Sum of the products of pairs of Padovan
numbers which are two apart, starting from A000931(5). Formula: a(n) = Sum_{i=5..n+5}
A000931(i)*A000931(i+2).
Conjectures from Colin Barker, Nov 09 2019:
G.f.: (1 + x - x^2 + x^3 - x^4) / ((1 - x)*(1 - 2*x + x^2 - x^3)*(1 + x - x^3)).
a(n) = 2*a(n-1) - 2*a(n-4) + 2*a(n-5) - 2*a(n-6) + a(n-7) for n>6.
A000931 is the Padovan sequence: a(n) = a(n-2) + a(n-3) with a(0) = 1, a(1) = a(2) = 0.

Formalization notes:
* `P` is A000931 and a(n) is the entry's formula Sum_{i=5..n+5} P(i)*P(i+2).
* The statement is the conjunction of the two conjectures. Since the denominator of the
  generating function has constant term 1, the identity A(x) = N/D for A(x) = Sum_{n >= 0} a(n)
  x^n is stated as A * D = N in the formal power series ring over the integers.
* Controls from the entry: the definition gives 1, 3, 5, 11, 19, 34, 62, 107 for n = 0..7.
-/

namespace OMA.S_oeis_a329178

open PowerSeries

/-- A000931, the Padovan sequence. -/
def P : ℕ → ℤ
  | 0 => 1
  | 1 => 0
  | 2 => 0
  | n + 3 => P (n + 1) + P n

/-- A329178(n) = Sum_{i=5..n+5} P(i)*P(i+2). -/
def a (n : ℕ) : ℤ := ∑ i ∈ Finset.Icc 5 (n + 5), P i * P (i + 2)

/-- Barker's generating function and recurrence. -/
theorem main :
    mk a * ((1 - X) * (1 - 2 * X + X ^ 2 - X ^ 3) * (1 + X - X ^ 3)) =
      (1 + X - X ^ 2 + X ^ 3 - X ^ 4 : PowerSeries ℤ) ∧
    (∀ n : ℕ, 6 < n →
      a n = 2 * a (n - 1) - 2 * a (n - 4) + 2 * a (n - 5) - 2 * a (n - 6) + a (n - 7)) := by
  sorry

end OMA.S_oeis_a329178
