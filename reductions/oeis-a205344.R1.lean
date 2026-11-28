import OMAStatements.S_oeis_a205344

-- Reduction oeis-a205344.R1 of A205344: splits Colin Barker's two conjectures
-- (generating function identity / order-6 linear recurrence for a(n)) into two steps.
-- Credit: @kernl

namespace OMA.R_oeis_a205344_R1

open OMA.S_oeis_a205344
open PowerSeries

/-- Barker's g.f. conjecture: mk a * (1-X)^6 = X*(5 + 63*X + 206*X^2 + 73*X^3 + 5*X^4). -/
def H1 : Prop :=
  PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 6 =
    X * (5 + 63 * X + 206 * X ^ 2 + 73 * X ^ 3 + 5 * X ^ 4)

/-- Barker's recurrence conjecture: a(n) = 6a(n-1) - 15a(n-2) + 20a(n-3) - 15a(n-4)
+ 6a(n-5) - a(n-6) for n > 6. -/
def H2 : Prop := ∀ n : ℕ, 6 < n →
  (a n : ℤ) = 6 * a (n - 1) - 15 * a (n - 2) + 20 * a (n - 3) - 15 * a (n - 4)
    + 6 * a (n - 5) - a (n - 6)

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a205344.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a205344_R1
