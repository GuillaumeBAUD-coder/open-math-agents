import Mathlib.Algebra.Order.Group.Nat
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# A304490: a(1) = a(2) = a(3) = 1, a(4) = 5, a(5) = 6, a(6) = 4; a(n) = a(n-a(n-2)) + a(n-a(n-4)) for n > 6.

Source: https://oeis.org/A304490
Credit: @SPatel2133

Conjectures of Colin Barker, 14 May 2018:
G.f.: x*(1 - x + 2*x^2 + 2*x^3 + 2*x^5 - x^6 + 4*x^7 - 3*x^8 + x^9 - x^10 - 2*x^11 + 2*x^12
- x^13 + x^14 + x^15 - x^16) / ((1 - x)^2*(1 - x + x^2)^2*(1 + x + x^2)^2), and
a(n) = 2*a(n-1) - 3*a(n-2) + 4*a(n-3) - 5*a(n-4) + 6*a(n-5) - 5*a(n-6) + 4*a(n-7) - 3*a(n-8)
+ 2*a(n-9) - a(n-10) for n > 17.

The nested recurrence is not structurally recursive, so the statement quantifies over every
sequence that satisfies the initial values and the recurrence. The sequence has offset one.
It is padded with a(0) = 0, the constant coefficient of the conjectured generating function.
The generating function is stated with its denominator cleared.
-/

namespace OMA.S_oeis_a304490

open PowerSeries

theorem main :
    ∀ a : ℕ → ℕ, a 0 = 0 → a 1 = 1 → a 2 = 1 → a 3 = 1 → a 4 = 5 → a 5 = 6 → a 6 = 4 →
    (∀ n : ℕ, 6 < n → a n = a (n - a (n - 2)) + a (n - a (n - 4))) →
    (∀ n : ℕ, 17 < n → (a n : ℤ) = 2 * (a (n - 1) : ℤ) - 3 * a (n - 2) + 4 * a (n - 3) - 5 * a (n - 4) + 6 * a (n - 5) - 5 * a (n - 6) + 4 * a (n - 7) - 3 * a (n - 8) + 2 * a (n - 9) - a (n - 10)) ∧
    ((1 - X) ^ 2 * (1 - X + X ^ 2) ^ 2 * (1 + X + X ^ 2) ^ 2 * PowerSeries.mk (fun n => (a n : ℤ)) =
      (X * (1 - X + 2 * X ^ 2 + 2 * X ^ 3 + 2 * X ^ 5 - X ^ 6 + 4 * X ^ 7 - 3 * X ^ 8 + X ^ 9 -
        X ^ 10 - 2 * X ^ 11 + 2 * X ^ 12 - X ^ 13 + X ^ 14 + X ^ 15 - X ^ 16) : PowerSeries ℤ)) := by
  sorry

end OMA.S_oeis_a304490
