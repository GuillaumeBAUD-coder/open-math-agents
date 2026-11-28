import Mathlib

/-!
# OEIS A219350: Barker's conjectures for n X 4 arrays of neighbourhood minima of sorted 0..1 arrays

Source: https://oeis.org/A219350 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @marcusbuffett.

Entry A219350 (R. H. Hardin, Nov 18 2012), offset 1: Number of n X 4 arrays of the minimum value of corresponding elements and their horizontal, vertical, diagonal or antidiagonal neighbors in a random, but sorted with lexicographically nondecreasing rows and columns, 0..1 n X 4 array.
Formula section:
Empirical: a(n) = (1/40320)*n^8 - (1/1120)*n^7 + (5/192)*n^6 - (2/5)*n^5 + (7429/1920)*n^4 - (3037/160)*n^3 + (34483/2016)*n^2 + (71507/280)*n - 791 for n>7.
Conjectures from _Colin Barker_, Jul 26 2018: (Start)
G.f.: x*(4 - 32*x + 123*x^2 - 292*x^3 + 474*x^4 - 555*x^5 + 496*x^6 - 364*x^7 + 235*x^8 - 139*x^9 + 82*x^10 - 48*x^11 + 22*x^12 - 7*x^13 + 3*x^14 - x^15) / (1 - x)^9.
a(n) = 9*a(n-1) - 36*a(n-2) + 84*a(n-3) - 126*a(n-4) + 126*a(n-5) - 84*a(n-6) + 36*a(n-7) - 9*a(n-8) + a(n-9) for n>16.
(End)

Formalization notes:
* An n X 4 array with entries in 0..1 is a map A : Fin n → Fin 4 → Fin 2, row index first. Entries are compared as natural numbers.
* Sorted with lexicographically nondecreasing rows and nondecreasing columns: the rows, each read
  left to right as a list, are nondecreasing in lexicographic order from top to bottom, and the
  columns, each read top to bottom as a list, are nondecreasing in lexicographic order from left to
  right (`IsSorted`).
* The derived array holds at each position the minimum of the element there and of its
  horizontal, vertical, diagonal or antidiagonal neighbours that lie inside the array (`minNb`). The relation
  `nb i j i' j'` says that position (i', j') is (i, j) itself or such a neighbour; the diagonal
  neighbours of (i, j) are (i - 1, j - 1) and (i + 1, j + 1), the antidiagonal ones
  (i - 1, j + 1) and (i + 1, j - 1).
* Counting the arrays of minima of a random sorted array means counting the distinct derived
  arrays as the source ranges over all sorted arrays: a(n) is the cardinality of the image of
  `minNb` on the sorted arrays. This reading reproduces the first terms by direct enumeration
  and every listed term of the entry by an exact transfer-matrix count.
* The statement is the conjunction of Barker's two conjectures: the g.f., as the identity
  A(x) (1 - x)^9 = (the entry's numerator) in the formal power series ring over the rationals with
  A(x) = Sum_{n >= 1} a(n) x^n; and the recurrence, for every n > 16, as an identity of integers.
-/

namespace OMA.S_oeis_a219350

open PowerSeries Finset

/-- Position (i', j') is (i, j) itself or one of its horizontal, vertical, diagonal or antidiagonal neighbours. -/
def nb (i j i' j' : ℕ) : Prop :=
  (i' = i ∧ j' = j) ∨
    (i' = i ∧ (j' + 1 = j ∨ j' = j + 1)) ∨
    (j' = j ∧ (i' + 1 = i ∨ i' = i + 1)) ∨
    ((i' + 1 = i ∧ j' + 1 = j) ∨ (i' = i + 1 ∧ j' = j + 1)) ∨
    ((i' + 1 = i ∧ j' = j + 1) ∨ (i' = i + 1 ∧ j' + 1 = j))

instance (i j i' j' : ℕ) : Decidable (nb i j i' j') := by unfold nb; infer_instance

/-- Rows lexicographically nondecreasing from top to bottom, columns lexicographically
nondecreasing from left to right. -/
def IsSorted {r c : ℕ} (A : Fin r → Fin c → Fin 2) : Prop :=
  Monotone (fun i => List.ofFn (A i)) ∧ Monotone (fun j => List.ofFn (fun i => A i j))

instance {r c : ℕ} (A : Fin r → Fin c → Fin 2) : Decidable (IsSorted A) := by
  unfold IsSorted; infer_instance

/-- The array of minima of each element and its neighbours inside the array. -/
def minNb {r c : ℕ} (A : Fin r → Fin c → Fin 2) : Fin r → Fin c → Fin 2 := fun i j =>
  ((univ : Finset (Fin r × Fin c)).filter (fun p => nb i j p.1 p.2)).inf (fun p => A p.1 p.2)

/-- A219350: the number of distinct arrays of neighbourhood minima of sorted n X 4 0..1 arrays. -/
def a (n : ℕ) : ℕ := ((univ.filter (fun A : Fin n → Fin 4 → Fin 2 => IsSorted A)).image minNb).card

/-- Barker's conjectures. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 9 =
      X * (4 - 32 * X + 123 * X ^ 2 - 292 * X ^ 3 + 474 * X ^ 4 - 555 * X ^ 5 + 496 * X ^ 6 - 364 * X ^ 7 + 235 * X ^ 8 - 139 * X ^ 9 + 82 * X ^ 10 - 48 * X ^ 11 + 22 * X ^ 12 - 7 * X ^ 13 + 3 * X ^ 14 - X ^ 15) ∧
    ∀ n : ℕ, 16 < n → (a n : ℤ) = 9 * a (n - 1) - 36 * a (n - 2) + 84 * a (n - 3) - 126 * a (n - 4) + 126 * a (n - 5) - 84 * a (n - 6) + 36 * a (n - 7) - 9 * a (n - 8) + a (n - 9) := by
  sorry

end OMA.S_oeis_a219350
