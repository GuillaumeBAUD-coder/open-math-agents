import Mathlib

/-!
# OEIS A219500: Hardin's empirical quintic and Barker's conjectured g.f. and recurrence for the number of n X 6 neighbourhood-minimum arrays of sorted 0..1 arrays

Source: https://oeis.org/A219500 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with claude-code (model claude-fable-5-2), submitted by @VestigeClub.

Entry: A219500: Number of n X 6 arrays of the minimum value of corresponding elements and their
horizontal or vertical neighbors in a random, but sorted with lexicographically nondecreasing
rows and nonincreasing columns, 0..1 n X 6 array. Offset 1; data 6, 11, 35, 88, 179, 325, 550,
885, 1369, 2050, ...

The conjectures, as the entry gives them:
  R. H. Hardin (author of the entry, Nov 20 2012):
    Empirical: a(n) = (1/120)*n^5 + (1/24)*n^4 + (13/24)*n^3 + (59/24)*n^2 + (59/20)*n - 17
    for n>3.
  Conjectures from Colin Barker, Jul 26 2018:
    G.f.: x*(6 - 25*x + 59*x^2 - 77*x^3 + 46*x^4 - 10*x^6 + x^7 + x^8) / (1 - x)^6.
    a(n) = 6*a(n-1) - 15*a(n-2) + 20*a(n-3) - 15*a(n-4) + 6*a(n-5) - a(n-6) for n>9.

Formalization notes:
* Offset 1, as in the entry. `a 0` (the empty array, counted once) is never used: the two
  formulas are stated for the ranges the entry gives (n > 3 and n > 9), and the g.f. has
  coefficient 0 at x^0.
* A 0..1 n X 6 array is a function `A : Fin n → Fin 6 → Fin 2`: `A i j` is the entry in row `i`
  (counted from the top) and column `j` (counted from the left), and `Fin 2` carries the order
  0 < 1. Arrays are counted as they stand, not up to any symmetry.
* "Sorted with lexicographically nondecreasing rows and nonincreasing columns" is read as: the
  rows, each a word read left to right, are in lexicographically nondecreasing order from top to
  bottom (`Monotone (fun i => toLex (A i))`), and the columns, each a word read top to bottom,
  are in lexicographically nonincreasing order from left to right
  (`Antitone (fun j => toLex (fun i => A i j))`). `toLex` puts Mathlib's lexicographic order
  `Pi.Lex` on words: the first position where two words differ decides. The term a(1) = 6 needs
  the column condition to be this one: for n = 1 the row condition is empty, the columns are
  single entries, and exactly the seven rows 000000, 100000, ..., 111111 are sorted; they give
  the six arrays 000000 (twice), 100000, 110000, 111000, 111100, 111111.
* "The minimum value of corresponding elements and their horizontal or vertical neighbors": the
  new array has, at `(i, j)`, the minimum of `A i j` and of the entries of `A` in the cells
  `(i, j - 1)`, `(i, j + 1)`, `(i - 1, j)`, `(i + 1, j)` that exist in the array. Border cells
  have fewer neighbours; there is no wrap-around and no diagonal neighbour. In Lean this is the
  infimum (`Finset.inf` in `Fin 2`) of `A` over the cells `p` with `Near i j p`; this set of
  cells contains `(i, j)`, so the infimum is the minimum of the entries named.
* "A random ... array" is read as "some array": `a n` is the number of distinct n X 6 arrays `B`
  for which a sorted 0..1 n X 6 array `A` with neighbourhood-minimum array `B` exists.
* Check of this reading against the entry: enumerating all 2^(6n) arrays `A` for n = 1, 2, 3, 4
  and applying these definitions literally gives 6, 11, 35, 88, the entry's first four terms.
* Hardin's formula is stated over `ℚ` for all n > 3, Barker's recurrence over `ℤ` for all
  n > 9, both with the entry's ranges.
* The g.f. is the ordinary generating function Sum_{n>=1} a(n)*x^n. It is stated as an identity
  of formal power series over `ℚ` after multiplying both sides by `(1 - x)^6`, which is
  invertible as a power series (constant coefficient 1), so nothing is lost. The numerator has
  no x^5 term inside the bracket, as in the entry.
* Controls proved in the proof file from the definition `a`: a(1) = 6, a(2) = 11, a(3) = 35,
  a(4) = 88, a(5) = 179, a(6) = 325, a(7) = 550, a(8) = 885, a(9) = 1369, a(10) = 2050.
-/

namespace OMA.S_oeis_a219500

/-- The rows of `A`, read left to right, are in lexicographically nondecreasing order from top
to bottom, and the columns of `A`, read top to bottom, are in lexicographically nonincreasing
order from left to right. -/
def Sorted {n : ℕ} (A : Fin n → Fin 6 → Fin 2) : Prop :=
  Monotone (fun i => toLex (A i)) ∧ Antitone (fun j => toLex (fun i => A i j))

/-- The cell `p` is the cell `(i, j)` itself, or its left or right neighbour in row `i`, or its
upper or lower neighbour in column `j`. -/
def Near {n : ℕ} (i : Fin n) (j : Fin 6) (p : Fin n × Fin 6) : Prop :=
  (p.1 = i ∧ p.2 = j) ∨
    (p.1 = i ∧ (p.2.val + 1 = j.val ∨ j.val + 1 = p.2.val)) ∨
    (p.2 = j ∧ (p.1.val + 1 = i.val ∨ i.val + 1 = p.1.val))

/-- The minimum of the entry of `A` at `(i, j)` and of the entries of `A` at the horizontal and
vertical neighbours of `(i, j)` that lie in the array. -/
noncomputable def nbhdMin {n : ℕ} (A : Fin n → Fin 6 → Fin 2) (i : Fin n) (j : Fin 6) :
    Fin 2 := by
  classical
  exact (Finset.univ.filter (fun p : Fin n × Fin 6 => Near i j p)).inf (fun p => A p.1 p.2)

/-- A219500(n): the number of n X 6 arrays `B` that are the neighbourhood-minimum array of some
sorted 0..1 n X 6 array `A`. -/
noncomputable def a (n : ℕ) : ℕ := by
  classical
  exact Fintype.card
    {B : Fin n → Fin 6 → Fin 2 // ∃ A : Fin n → Fin 6 → Fin 2, Sorted A ∧ nbhdMin A = B}

open PowerSeries in
/-- Hardin's empirical formula (n > 3), Barker's g.f., and Barker's recurrence (n > 9). -/
theorem main :
    (∀ n : ℕ, 3 < n →
      (a n : ℚ) = (1 / 120) * (n : ℚ) ^ 5 + (1 / 24) * (n : ℚ) ^ 4 + (13 / 24) * (n : ℚ) ^ 3 +
        (59 / 24) * (n : ℚ) ^ 2 + (59 / 20) * (n : ℚ) - 17) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 6 =
        X * (6 - 25 * X + 59 * X ^ 2 - 77 * X ^ 3 + 46 * X ^ 4 - 10 * X ^ 6 + X ^ 7 +
          X ^ 8) ∧
    (∀ n : ℕ, 9 < n →
      (a n : ℤ) = 6 * a (n - 1) - 15 * a (n - 2) + 20 * a (n - 3) - 15 * a (n - 4) +
        6 * a (n - 5) - a (n - 6)) := by
  sorry

end OMA.S_oeis_a219500
