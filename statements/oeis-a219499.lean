import Mathlib

/-!
# OEIS A219499: Hardin's empirical quartic and Barker's conjectured g.f. and recurrence for the number of n X 5 neighbourhood-minimum arrays of sorted 0..1 arrays

Source: https://oeis.org/A219499 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with claude-code (model claude-fable-5-2), submitted by @VestigeClub.

Entry: A219499: Number of n X 5 arrays of the minimum value of corresponding elements and their
horizontal or vertical neighbors in a random, but sorted with lexicographically nondecreasing
rows and nonincreasing columns, 0..1 n X 5 array. Offset 1; data 5, 9, 26, 58, 107, 179, 281,
421, 608, 852, ...

The conjectures, as the entry gives them:
  R. H. Hardin (author of the entry, Nov 20 2012):
    Empirical: a(n) = (1/24)*n^4 + (1/4)*n^3 + (35/24)*n^2 + (21/4)*n - 13 for n>2.
  Conjectures from Colin Barker, Jul 26 2018:
    G.f.: x*(5 - 16*x + 31*x^2 - 32*x^3 + 12*x^4 + 4*x^5 - 3*x^6) / (1 - x)^5.
    a(n) = 5*a(n-1) - 10*a(n-2) + 10*a(n-3) - 5*a(n-4) + a(n-5) for n>7.

Formalization notes:
* Offset 1, as in the entry. `a 0` (the empty array, counted once) is never used: the two
  formulas are stated for the ranges the entry gives (n > 2 and n > 7), and the g.f. has
  coefficient 0 at x^0.
* A 0..1 n X 5 array is a function `A : Fin n → Fin 5 → Fin 2`: `A i j` is the entry in row `i`
  (counted from the top) and column `j` (counted from the left), and `Fin 2` carries the order
  0 < 1. Arrays are counted as they stand, not up to any symmetry.
* "Sorted with lexicographically nondecreasing rows and nonincreasing columns" is read as: the
  rows, each a word read left to right, are in lexicographically nondecreasing order from top to
  bottom (`Monotone (fun i => toLex (A i))`), and the columns, each a word read top to bottom,
  are in lexicographically nonincreasing order from left to right
  (`Antitone (fun j => toLex (fun i => A i j))`). `toLex` puts Mathlib's lexicographic order
  `Pi.Lex` on words: the first position where two words differ decides. The term a(1) = 5 needs
  the column condition to be this one: for n = 1 the row condition is empty, the columns are
  single entries, and exactly the six rows 00000, 10000, ..., 11111 are sorted; they give the
  five arrays 00000 (twice), 10000, 11000, 11100, 11111.
* "The minimum value of corresponding elements and their horizontal or vertical neighbors": the
  new array has, at `(i, j)`, the minimum of `A i j` and of the entries of `A` in the cells
  `(i, j - 1)`, `(i, j + 1)`, `(i - 1, j)`, `(i + 1, j)` that exist in the array. Border cells
  have fewer neighbours; there is no wrap-around and no diagonal neighbour. In Lean this is the
  infimum (`Finset.inf` in `Fin 2`) of `A` over the cells `p` with `Near i j p`; this set of
  cells contains `(i, j)`, so the infimum is the minimum of the entries named.
* "A random ... array" is read as "some array": `a n` is the number of distinct n X 5 arrays `B`
  for which a sorted 0..1 n X 5 array `A` with neighbourhood-minimum array `B` exists.
* Check of this reading against the entry: enumerating all 2^(5n) arrays `A` for n = 1, 2, 3, 4
  and applying these definitions literally gives 5, 9, 26, 58, the entry's first four terms.
* Hardin's formula is stated over `ℚ` for all n > 2, Barker's recurrence over `ℤ` for all
  n > 7, both with the entry's ranges.
* The g.f. is the ordinary generating function Sum_{n>=1} a(n)*x^n. It is stated as an identity
  of formal power series over `ℚ` after multiplying both sides by `(1 - x)^5`, which is
  invertible as a power series (constant coefficient 1), so nothing is lost.
* Controls proved in the proof file from the definition `a`: a(1) = 5, a(2) = 9, a(3) = 26,
  a(4) = 58, a(5) = 107, a(6) = 179, a(7) = 281, a(8) = 421.
-/

namespace OMA.S_oeis_a219499

/-- The rows of `A`, read left to right, are in lexicographically nondecreasing order from top
to bottom, and the columns of `A`, read top to bottom, are in lexicographically nonincreasing
order from left to right. -/
def Sorted {n : ℕ} (A : Fin n → Fin 5 → Fin 2) : Prop :=
  Monotone (fun i => toLex (A i)) ∧ Antitone (fun j => toLex (fun i => A i j))

/-- The cell `p` is the cell `(i, j)` itself, or its left or right neighbour in row `i`, or its
upper or lower neighbour in column `j`. -/
def Near {n : ℕ} (i : Fin n) (j : Fin 5) (p : Fin n × Fin 5) : Prop :=
  (p.1 = i ∧ p.2 = j) ∨
    (p.1 = i ∧ (p.2.val + 1 = j.val ∨ j.val + 1 = p.2.val)) ∨
    (p.2 = j ∧ (p.1.val + 1 = i.val ∨ i.val + 1 = p.1.val))

/-- The minimum of the entry of `A` at `(i, j)` and of the entries of `A` at the horizontal and
vertical neighbours of `(i, j)` that lie in the array. -/
noncomputable def nbhdMin {n : ℕ} (A : Fin n → Fin 5 → Fin 2) (i : Fin n) (j : Fin 5) :
    Fin 2 := by
  classical
  exact (Finset.univ.filter (fun p : Fin n × Fin 5 => Near i j p)).inf (fun p => A p.1 p.2)

/-- A219499(n): the number of n X 5 arrays `B` that are the neighbourhood-minimum array of some
sorted 0..1 n X 5 array `A`. -/
noncomputable def a (n : ℕ) : ℕ := by
  classical
  exact Fintype.card
    {B : Fin n → Fin 5 → Fin 2 // ∃ A : Fin n → Fin 5 → Fin 2, Sorted A ∧ nbhdMin A = B}

open PowerSeries in
/-- Hardin's empirical formula (n > 2), Barker's g.f., and Barker's recurrence (n > 7). -/
theorem main :
    (∀ n : ℕ, 2 < n →
      (a n : ℚ) = (1 / 24) * (n : ℚ) ^ 4 + (1 / 4) * (n : ℚ) ^ 3 + (35 / 24) * (n : ℚ) ^ 2 +
        (21 / 4) * (n : ℚ) - 13) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 5 =
        X * (5 - 16 * X + 31 * X ^ 2 - 32 * X ^ 3 + 12 * X ^ 4 + 4 * X ^ 5 - 3 * X ^ 6) ∧
    (∀ n : ℕ, 7 < n →
      (a n : ℤ) = 5 * a (n - 1) - 10 * a (n - 2) + 10 * a (n - 3) - 5 * a (n - 4) +
        a (n - 5)) := by
  sorry

end OMA.S_oeis_a219499
