import Mathlib

/-!
# A251328: Number of (n+1) X (1+1) 0..2 arrays with every 2 X 2 subblock summing to 2 4 or 6.

Source: https://oeis.org/A251328
Credit: @physbuzz

The conjectures listed in the entry, all stated below as one conjunction:
* Empirical (R. H. Hardin): a(n) = 8*a(n-1) - 13*a(n-2) - 12*a(n-3), stated for n > 3.
* G.f.: 3*x*(13 - 47*x - 36*x^2) / ((1 - 4*x)*(1 - 4*x - 3*x^2)) (Colin Barker).
* a(n) = (7*2^(3+2*n) + (35-13*sqrt(7))*(2-sqrt(7))^n + (2+sqrt(7))^n*(35+13*sqrt(7))) / 14
  (Colin Barker), stated for n >= 1.

Conventions:
* An (n+1) X 2 array is the list of its n + 1 rows from top to bottom; a row is a function
  `Fin 2 → Fin 3` giving its two entries from left to right, each in `0..2`.
* Every 2 X 2 subblock sums to 2, 4 or 6: for any two consecutive rows, the four entries sum to 2,
  4 or 6.
* Offset 1 as in the OEIS; the generating function is written after dividing by `x`, i.e. as the
  series `Sum_{n>=0} a(n+1) x^n`.
-/

namespace OMA.S_oeis_a251328

open PowerSeries Real

/-- The conditions on an array, given as the list of its rows from top to bottom. -/
def IsSolution (l : List (Fin 2 → Fin 3)) : Prop :=
  l.IsChain (fun r s => (r 0 : ℕ) + r 1 + s 0 + s 1 ∈ ({2, 4, 6} : Finset ℕ))

/-- A251328(n): the number of such (n+1) X 2 arrays. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {l : List (Fin 2 → Fin 3) // l.length = n + 1 ∧ IsSolution l}

theorem main :
    (∀ n > 3, (a n : ℤ) = 8 * a (n - 1) - 13 * a (n - 2) - 12 * a (n - 3)) ∧
    (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * ((1 - 4 * X) * (1 - 4 * X - 3 * X ^ 2)) =
      3 * (13 - 47 * X - 36 * X ^ 2)) ∧
    (∀ n ≥ 1, (a n : ℝ) = (7 * 2 ^ (3 + 2 * n) + (35 - 13 * √7) * (2 - √7) ^ n +
      (2 + √7) ^ n * (35 + 13 * √7)) / 14) := by
  sorry

end OMA.S_oeis_a251328
