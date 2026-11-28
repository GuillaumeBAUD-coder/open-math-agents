import Mathlib

/-!
# OEIS A279897: Barker's g.f. and closed form for n X 3 0..2 arrays with exactly one element unequal to a strict majority of its king-move neighbors

Source: https://oeis.org/A279897 (OEIS Foundation, CC BY-SA 4.0).

Entry A279897 (R. H. Hardin, Dec 22 2016), offset 1: Number of n X 3 0..2 arrays with no element
unequal to a strict majority of its king-move neighbors, with the exception of exactly one element,
and with new values introduced in order 0 sequentially upwards. Column 3 of A279902.
Data: 2, 6, 9, 20, 43, 94, 213, 456, 1003, 2146, ...
Formula section: Conjectures from Colin Barker, Feb 12 2019:
G.f.: x*(2 + 2*x - 9*x^2 - 8*x^3 + 8*x^4 + 8*x^5 + 12*x^6) / ((1 + x)^2*(1 - 2*x)^2).
a(n) = (1280*(-1)^n + 31*2^(2+n) - 264*(-1)^n*n + 33*2^n*n) / 216 for n>3.

Formalization notes:
* An array is a function x : Fin n -> Fin 3 -> Fin 3, x i j being the entry in row i and column j.
* The king-move neighbors of the cell (i,j) are the other cells (i',j') of the array with
  |i' - i| <= 1 and |j' - j| <= 1 (`KingAdj`). A cell is exceptional (`Exceptional`) when it is
  unequal to a strict majority of its king-move neighbors: twice the number of neighbors with a
  value different from x(i,j) exceeds the number of neighbors. The array is counted when exactly
  one cell is exceptional.
* New values introduced in order 0 sequentially upwards (`RowMajorNew`): reading the array row by
  row, each row from left to right, every value smaller than an entry occurs before that entry.
* The statement is the conjunction of Barker's two conjectures: the g.f. as the identity
  A(x) ((1 + x)^2 (1 - 2x)^2) = x (2 + 2x - 9x^2 - 8x^3 + 8x^4 + 8x^5 + 12x^6) in the formal power
  series ring over the rationals, with A(x) = Sum_{n >= 1} a(n) x^n (offset 1, so the constant
  term is 0), and the closed form over the rationals for every n > 3.
* A direct enumeration of this definition gives 2, 6, 9, 20, 43 for n = 1..5, the entry's data.
-/

namespace OMA.S_oeis_a279897

open PowerSeries Finset

/-- The cells p and q of an n X 3 array are king-move neighbors: they are different and their
rows and their columns differ by at most one. -/
def KingAdj {n : ℕ} (p q : Fin n × Fin 3) : Prop :=
  p ≠ q ∧ p.1.val ≤ q.1.val + 1 ∧ q.1.val ≤ p.1.val + 1 ∧ p.2.val ≤ q.2.val + 1 ∧
    q.2.val ≤ p.2.val + 1

instance {n : ℕ} (p q : Fin n × Fin 3) : Decidable (KingAdj p q) := by
  unfold KingAdj; infer_instance

/-- The cell (i,j) of x is unequal to a strict majority of its king-move neighbors. -/
def Exceptional {n : ℕ} (x : Fin n → Fin 3 → Fin 3) (q : Fin n × Fin 3) : Prop :=
  ((univ : Finset (Fin n × Fin 3)).filter (fun p => KingAdj p q)).card <
    2 * ((univ : Finset (Fin n × Fin 3)).filter (fun p => KingAdj p q ∧ x p.1 p.2 ≠ x q.1 q.2)).card

instance {n : ℕ} (x : Fin n → Fin 3 → Fin 3) (q : Fin n × Fin 3) : Decidable (Exceptional x q) := by
  unfold Exceptional; infer_instance

/-- The values of the array x are introduced in row major order: every value below x(i,j) already
occurs at an earlier position in row major order, in a row i' < i or in row i at a column j' < j. -/
def RowMajorNew {R C K : ℕ} (x : Fin R → Fin C → Fin K) : Prop :=
  ∀ i j, ∀ u : Fin K, u < x i j → ∃ i' j', (i' < i ∨ (i' = i ∧ j' < j)) ∧ x i' j' = u

instance {R C K : ℕ} : DecidablePred (@RowMajorNew R C K) := fun x => by
  unfold RowMajorNew; infer_instance

/-- A279897(n): the number of n X 3 arrays with entries 0..2 with exactly one exceptional cell and
the values introduced in row major order. -/
def a (n : ℕ) : ℕ :=
  ((univ : Finset (Fin n → Fin 3 → Fin 3)).filter (fun x =>
    ((univ : Finset (Fin n × Fin 3)).filter (fun q => Exceptional x q)).card = 1 ∧
      RowMajorNew x)).card

/-- Barker's conjectures: the g.f. and the closed form for n > 3. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * ((1 + X) ^ 2 * (1 - 2 * X) ^ 2) =
      X * (2 + 2 * X - 9 * X ^ 2 - 8 * X ^ 3 + 8 * X ^ 4 + 8 * X ^ 5 + 12 * X ^ 6) ∧
    ∀ n : ℕ, 3 < n → (a n : ℚ) =
      (1280 * (-1) ^ n + 31 * 2 ^ (2 + n) - 264 * (-1) ^ n * n + 33 * 2 ^ n * n) / 216 := by
  sorry

end OMA.S_oeis_a279897
