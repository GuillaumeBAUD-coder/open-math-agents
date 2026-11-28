import Mathlib

/-!
# The recurrence and generating function for OEIS A111093

Source: https://oeis.org/A111093 and the digit string in https://oeis.org/A111072.
Credit: Giorgio Balzarotti and Paolo P. Lava (sequence), Chai Wah Wu (conjectures,
January 28, 2024), Robert Leshner (@rleshner, formalization).

Starting at position zero in the repeated digit string 0123456789, jump to the
right by 1², 2², 3², … . Sum the digits reached, including the initial zero.
Alois P. Heinz gives the generating function for the related linear jumps in A111072.
-/

namespace OMA.S_oeis_a111093

/-- Position reached after the first n square jumps. -/
def position : ℕ → ℕ
  | 0 => 0
  | n+1 => position n + (n+1)^2

/-- The digit at position p of the repeated decimal string is p modulo ten. -/
def a : ℕ → ℤ
  | 0 => 0
  | n+1 => a n + ((position (n+1) % 10 : ℕ) : ℤ)

/-- Both of Wu's conjectures. The denominator of the formal series has constant term 1. -/
theorem main :
    (∀ n : ℕ, 15 < n →
      a n = a (n-1)+a (n-5)-a (n-6)-a (n-10)+a (n-11)+a (n-15)-a (n-16)) ∧
    (let X : PowerSeries ℤ := PowerSeries.X
     (X^16-X^15-X^11+X^10+X^6-X^5-X+1)*PowerSeries.mk a =
       X*(9*X^12+5*X^11+6*X^10+5*X^8-5*X^6+5*X^4+4*X^2+5*X+1)) := by
  sorry

end OMA.S_oeis_a111093
