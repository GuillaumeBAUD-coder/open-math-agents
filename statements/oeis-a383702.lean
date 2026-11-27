import Mathlib.Algebra.Polynomial.Coeff

/-!
# The order-three recurrence of A383702

The product starts at n = 0 with the empty polynomial product 1. Writing the
index of the recurrence as n+3 covers every index with three predecessors.
A polynomial-coefficient linear recurrence also proves D-finiteness.

Source: https://oeis.org/A383702
Credit: @CubeJerry
-/

namespace OMA.S_oeis_a383702

open Polynomial

noncomputable def product : ℕ → Polynomial ℤ
  | 0 => 1
  | n+1 => (X + C (4*(n:ℤ)+3)) * product n

noncomputable def a (n : ℕ) := (product n).coeff 2

theorem main : ∀ n : ℕ, a (n+3) + 3*(-4*((n:ℤ)+3)+5)*a (n+2) +
    (48*((n:ℤ)+3)^2 - 168*((n:ℤ)+3) + 151)*a (n+1) -
    (4*((n:ℤ)+3)-9)^3*a n = 0 := by
  sorry

end OMA.S_oeis_a383702
