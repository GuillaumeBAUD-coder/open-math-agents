import Mathlib

/-!
# OEIS A239359: Barker's conjectures for n X 6 0..2 arrays with no element equal to one plus the sum of elements to its left or one plus the sum of elements above it or one plus the sum of the elements diagonally to its northwest, modulo 3

Source: https://oeis.org/A239359 (OEIS Foundation, CC BY-SA 4.0).

Entry A239359 (R. H. Hardin), offset 1: Number of n X 6 0..2 arrays with no element equal to one plus the sum of elements to its left or one plus the sum of elements above it or one plus the sum of the elements diagonally to its northwest, modulo 3.
Formula section:
Conjectures from Colin Barker, Oct 26 2018: (Start)
G.f.: x*(7 - 9*x + 5*x^2 + 7*x^3 + 13*x^4 - 33*x^5 + 12*x^6 + 12*x^7 + 2*x^8 + 7*x^9 - 4*x^10 + 10*x^11 - 10*x^12 - 10*x^13 + 9*x^14 - 3*x^15 + x^16) / (1 - x)^4.
a(n) = 4*a(n-1) - 6*a(n-2) + 4*a(n-3) - a(n-4) for n>17.
(End)

Formalization notes:
* An n X 6 array with entries 0..2 is a map x : Fin n -> Fin 6 -> Fin 3, with x i j the entry in
  row i and column j (row 0 at the top, column 0 at the left).
* The elements to the left of (i, j) are x i j' with j' < j, the elements above it are x i' j with
  i' < i, and the elements diagonally to its northwest are x (i - k) (j - k) for k >= 1,
  that is the cells (i', j') with i' < i and i - i' = j - j'.
  Empty sums are 0. "Equal to one plus the sum ... modulo 3" means x i j = (1 + sum) mod 3, the entry
  being read as a number in 0..2.
* a(n) is defined for every n; the entry starts at n = 1, so the g.f. is stated with
  A(x) = Sum_{n >= 1} a(n) x^n, as the identity A(x) * (denominator) = (numerator) in the formal
  power series ring over the rationals; the recurrence is stated for every n > 17 as an identity
  of integers. The statement is the conjunction of the two conjectures.
* The definition reproduces every listed term of the entry (7, 19, 39, 77, 156, 266, ... from
  n = 1), checked by direct enumeration for small n and by a transfer-matrix count for all 40 terms.
-/

namespace OMA.S_oeis_a239359

open PowerSeries Finset

/-- The sum of the elements to the left of (i, j) in its row. -/
def leftSum {n : ℕ} (x : Fin n → Fin 6 → Fin 3) (i : Fin n) (j : Fin 6) : ℕ :=
  ∑ j' ∈ univ.filter (· < j), (x i j' : ℕ)

/-- The sum of the elements above (i, j) in its column. -/
def aboveSum {n : ℕ} (x : Fin n → Fin 6 → Fin 3) (i : Fin n) (j : Fin 6) : ℕ :=
  ∑ i' ∈ univ.filter (· < i), (x i' j : ℕ)

/-- The sum of the elements diagonally to the northwest of (i, j): the cells (i', j') with i' < i and
i - i' = j - j'. -/
def nwSum {n : ℕ} (x : Fin n → Fin 6 → Fin 3) (i : Fin n) (j : Fin 6) : ℕ :=
  ∑ p ∈ univ.filter (fun p : Fin n × Fin 6 => p.1 < i ∧ (p.1 : ℕ) + j = p.2 + i), (x p.1 p.2 : ℕ)

/-- No element equals one plus any of these sums, modulo 3. -/
def good {n : ℕ} (x : Fin n → Fin 6 → Fin 3) : Prop :=
  ∀ i j, (x i j : ℕ) ≠ (1 + leftSum x i j) % 3 ∧ (x i j : ℕ) ≠ (1 + aboveSum x i j) % 3 ∧
    (x i j : ℕ) ≠ (1 + nwSum x i j) % 3

instance {n : ℕ} : DecidablePred (@good n) := fun x => by unfold good; infer_instance

/-- A239359: number of n X 6 0..2 arrays with no element equal to one plus the sum of elements to its left or one plus the sum of elements above it or one plus the sum of the elements diagonally to its northwest, modulo 3. -/
def a (n : ℕ) : ℕ := ((univ : Finset (Fin n → Fin 6 → Fin 3)).filter good).card

/-- Barker's conjectures. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 4 =
      X * (7 - 9 * X + 5 * X ^ 2 + 7 * X ^ 3 + 13 * X ^ 4 - 33 * X ^ 5 + 12 * X ^ 6 + 12 * X ^ 7 + 2 * X ^ 8 + 7 * X ^ 9 - 4 * X ^ 10 + 10 * X ^ 11 - 10 * X ^ 12 - 10 * X ^ 13 + 9 * X ^ 14 - 3 * X ^ 15 + X ^ 16) ∧
    ∀ n : ℕ, 17 < n → (a n : ℤ) = 4 * a (n - 1) - 6 * a (n - 2) + 4 * a (n - 3) - a (n - 4) := by
  sorry

end OMA.S_oeis_a239359
