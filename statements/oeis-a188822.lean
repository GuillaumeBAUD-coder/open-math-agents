import Mathlib

/-!
# A188822: Number of n X 7 binary arrays without the pattern 0 1 diagonally or antidiagonally.

Source: https://oeis.org/A188822
Credit: @physbuzz

The conjectures listed in the entry, all stated below as one conjunction:
* G.f.: 4*x*(32 + 225*x + 394*x^2 + 329*x^3 + 72*x^4 + 8*x^5 - 36*x^6) / ((1 - x)^3*(1 + x))
  (Colin Barker).
* a(n) = 2*(578 - 1088*n + 512*n^2) for n>3 and even (Colin Barker).
* a(n) = 2*(528 - 1088*n + 512*n^2) for n>3 and odd (Colin Barker).

Conventions:
* An n X 7 array is the list of its n rows from top to bottom; a row is a function
  `Fin 7 → Fin 2` giving its entries from left to right (entry `j` lies in column `j`).
* The pattern 0 1 in a direction is a 0 immediately followed, in that direction, by a 1:
  diagonally (a 1 one row down and one column to the right of a 0) and antidiagonally (a 1 one
  row down and one column to the left of a 0). Both only involve two consecutive rows. This
  reading reproduces the OEIS data.
* Offset 1 as in the OEIS; the generating function is written after dividing by `x`, i.e. as the
  series `Sum_{n>=0} a(n+1) x^n`.
-/

namespace OMA.S_oeis_a188822

open PowerSeries

/-- The conditions on an array, given as the list of its rows from top to bottom. -/
def IsSolution (l : List (Fin 7 → Fin 2)) : Prop :=
  l.IsChain (fun r s =>
    ∀ j : Fin 6, ¬ (r j.castSucc = 0 ∧ s j.succ = 1) ∧ ¬ (r j.succ = 0 ∧ s j.castSucc = 1))

/-- A188822(n): the number of such n X 7 arrays. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {l : List (Fin 7 → Fin 2) // l.length = n ∧ IsSolution l}

theorem main :
    (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * ((1 - X) ^ 3 * (1 + X)) =
      4 * (32 + 225 * X + 394 * X ^ 2 + 329 * X ^ 3 + 72 * X ^ 4 + 8 * X ^ 5 - 36 * X ^ 6)) ∧
    (∀ n > 3, Even n → (a n : ℤ) = 2 * (578 - 1088 * n + 512 * n ^ 2)) ∧
    (∀ n > 3, Odd n → (a n : ℤ) = 2 * (528 - 1088 * n + 512 * n ^ 2)) := by
  sorry

end OMA.S_oeis_a188822
