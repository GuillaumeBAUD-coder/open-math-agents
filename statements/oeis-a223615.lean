import Mathlib

/-!
# A223615: Number of n X 3 0..1 arrays with rows and columns unimodal.

Source: https://oeis.org/A223615
Credit: @physbuzz

The conjectures listed in the entry, all stated below as one conjunction:
* G.f.: x*(7 + 44*x^2 - 20*x^3 + 20*x^4 - 6*x^5 + x^6) / (1 - x)^7 (Colin Barker, Aug 21 2018).
* a(n) = 7*a(n-1) - 21*a(n-2) + 35*a(n-3) - 35*a(n-4) + 21*a(n-5) - 7*a(n-6) + a(n-7) for n>7 (Colin Barker, Aug 21 2018).

Conventions:
* An n X 3 array is the list of its n rows from top to bottom; a row is a function
  `Fin 3 → Fin 2` giving its entries from left to right.
* A finite sequence is unimodal when it is weakly increasing up to some position and weakly
  decreasing from that position on (`Unimodal`, on the list of its terms). Every row, read from
  left to right, and every column, read from top to bottom, is unimodal. This reading reproduces
  the OEIS data.
* Offset 1 as in the OEIS; the generating function is written after dividing by `x`, i.e. as the
  series `Sum_{n>=0} a(n+1) x^n`.
-/

namespace OMA.S_oeis_a223615

open PowerSeries

/-- A list is unimodal: weakly increasing up to some position `m`, weakly decreasing from `m` on. -/
def Unimodal (s : List ℕ) : Prop :=
  ∃ m, (s.take m).Pairwise (· ≤ ·) ∧ (s.drop m).Pairwise (· ≥ ·)

/-- The conditions on an array, given as the list of its rows from top to bottom. -/
def IsSolution (l : List (Fin 3 → Fin 2)) : Prop :=
  (∀ r ∈ l, Unimodal (List.ofFn fun j => (r j : ℕ))) ∧
  ∀ j : Fin 3, Unimodal (l.map fun r => (r j : ℕ))

/-- A223615(n): the number of such n X 3 arrays. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {l : List (Fin 3 → Fin 2) // l.length = n ∧ IsSolution l}

theorem main :
    (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * (1 - X) ^ 7 =
      7 + 44 * X ^ 2 - 20 * X ^ 3 + 20 * X ^ 4 - 6 * X ^ 5 + X ^ 6) ∧
    (∀ n > 7, (a n : ℤ) = 7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) - 35 * a (n - 4) + 21 * a (n - 5) - 7 * a (n - 6) + a (n - 7)) := by
  sorry

end OMA.S_oeis_a223615
