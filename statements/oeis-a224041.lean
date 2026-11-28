import Mathlib

/-!
# A224041: Number of 5 X n 0..1 arrays with antidiagonals unimodal and rows and diagonals nondecreasing.

Source: https://oeis.org/A224041
Credit: @physbuzz

The conjectures listed in the entry, all stated below as one conjunction:
* G.f.: x*(32 - 48*x - 86*x^2 + 220*x^3 - 124*x^4 - 12*x^5 + 9*x^6 + 17*x^7 - 7*x^8) / (1 - x)^6 (Colin Barker, Aug 26 2018).
* a(n) = 6*a(n-1) - 15*a(n-2) + 20*a(n-3) - 15*a(n-4) + 6*a(n-5) - 1*a(n-6) for n>9 (Colin Barker, Aug 26 2018).

Conventions:
* A 5 X n array is the list of its n columns from left to right; a column is a function
  `Fin 5 → Fin 2` giving its entries from top to bottom (entry `i` lies in row `i`).
* A finite sequence is unimodal when it is weakly increasing up to some position and weakly
  decreasing from that position on (`Unimodal`, on the list of its terms).
* Every row, read from left to right, is nondecreasing: x(i, j) <= x(i, j+1).
* Every diagonal, read from top left to bottom right, is nondecreasing: x(i, j) <= x(i+1, j+1).
* Every antidiagonal is unimodal; the antidiagonals are the ones starting in the first column
  (`adiagFrom l i`) and the ones starting in the bottom row (`adiagFrom (l.drop j) 4`),
  each read from left to right (unimodality does not depend on the direction).
* This reading reproduces the OEIS data.
* Offset 1 as in the OEIS; the generating function is written after dividing by `x`, i.e. as the
  series `Sum_{n>=0} a(n+1) x^n`.
-/

namespace OMA.S_oeis_a224041

open PowerSeries

/-- A list is unimodal: weakly increasing up to some position `m`, weakly decreasing from `m` on. -/
def Unimodal (s : List ℕ) : Prop :=
  ∃ m, (s.take m).Pairwise (· ≤ ·) ∧ (s.drop m).Pairwise (· ≥ ·)

/-- The antidiagonal through the cell in row `i` of the first column of a list of columns, read
from left to right: x(i, 0), x(i - 1, 1), ..., x(0, i) (shorter when the columns run out). -/
def adiagFrom : List (Fin 5 → Fin 2) → ℕ → List ℕ
  | [], _ => []
  | c :: l, i => if h : i < 5 then (c ⟨i, h⟩ : ℕ) :: (if i = 0 then [] else adiagFrom l (i - 1)) else []

/-- The conditions on an array, given as the list of its columns from left to right. -/
def IsSolution (l : List (Fin 5 → Fin 2)) : Prop :=
  l.IsChain (fun u v => (∀ i : Fin 5, u i ≤ v i) ∧ (∀ i : Fin 4, u i.castSucc ≤ v i.succ)) ∧
  (∀ i < 5, Unimodal (adiagFrom l i)) ∧
  (∀ j, Unimodal (adiagFrom (l.drop j) 4))

/-- A224041(n): the number of such 5 X n arrays. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {l : List (Fin 5 → Fin 2) // l.length = n ∧ IsSolution l}

theorem main :
    (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * (1 - X) ^ 6 =
      32 - 48 * X - 86 * X ^ 2 + 220 * X ^ 3 - 124 * X ^ 4 - 12 * X ^ 5 + 9 * X ^ 6 + 17 * X ^ 7 - 7 * X ^ 8) ∧
    (∀ n > 9, (a n : ℤ) = 6 * a (n - 1) - 15 * a (n - 2) + 20 * a (n - 3) - 15 * a (n - 4) + 6 * a (n - 5) - 1 * a (n - 6)) := by
  sorry

end OMA.S_oeis_a224041
