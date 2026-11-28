import Mathlib

/-!
# A183624: Number of (n+1) X 2 0..2 arrays with every 2 x 2 subblock summing to 4.

Source: https://oeis.org/A183624
Credit: @physbuzz

The conjectures listed in the entry, all stated below as one conjunction:
* G.f.: x*(19 - 69*x + 54*x^2) / ((1 - x)*(1 - 2*x)*(1 - 3*x)) (Colin Barker).
* a(n) = 2 + 2^(2+n) + 3^(1+n) (Colin Barker), stated for n >= 1.
* The recurrence a(n) = 6*a(n-1) - 11*a(n-2) + 6*a(n-3) for n > 3, equivalent to the generating
  function.

Conventions:
* An (n+1) X 2 array is the list of its n + 1 rows from top to bottom; a row is a function
  `Fin 2 → Fin 3` giving its two entries, each in `0..2`.
* Every 2 X 2 subblock sums to 4: for any two consecutive rows, the four entries sum to 4.
* Offset 1 as in the OEIS; the generating function is written after dividing by `x`, i.e. as the
  series `Sum_{n>=0} a(n+1) x^n`.
-/

namespace OMA.S_oeis_a183624

open PowerSeries

/-- The conditions on an array, given as the list of its rows from top to bottom. -/
def IsSolution (l : List (Fin 2 → Fin 3)) : Prop :=
  l.IsChain (fun r s => (r 0 : ℕ) + r 1 + s 0 + s 1 = 4)

/-- A183624(n): the number of such (n+1) X 2 arrays. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {l : List (Fin 2 → Fin 3) // l.length = n + 1 ∧ IsSolution l}

theorem main :
    (∀ n > 3, (a n : ℤ) = 6 * a (n - 1) - 11 * a (n - 2) + 6 * a (n - 3)) ∧
    (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * ((1 - X) * (1 - 2 * X) * (1 - 3 * X)) =
      19 - 69 * X + 54 * X ^ 2) ∧
    (∀ n ≥ 1, (a n : ℚ) = 2 + 2 ^ (2 + n) + 3 ^ (1 + n)) := by
  sorry

end OMA.S_oeis_a183624
