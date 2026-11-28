import Mathlib

/-!
# OEIS A219472: Barker's conjectures for 2 X n arrays of neighbourhood minima of sorted 0..3 arrays

Source: https://oeis.org/A219472 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @marcusbuffett.

Entry A219472 (R. H. Hardin, Nov 20 2012), offset 1: Number of 2 X n arrays of the minimum value of corresponding elements and their horizontal or antidiagonal neighbors in a random, but sorted with lexicographically nondecreasing rows and columns, 0..3 2 X n array.
Formula section:
Empirical: a(n) = (1/13440)*n^8 + (1/10080)*n^7 + (1/576)*n^6 + (119/720)*n^5 - (9659/5760)*n^4 + (18247/1440)*n^3 - (50047/2016)*n^2 + (6437/840)*n + 13 for n>3.
Conjectures from _Colin Barker_, Jul 26 2018: (Start)
G.f.: x*(10 - 67*x + 221*x^2 - 413*x^3 + 424*x^4 - 153*x^5 - 91*x^6 + 35*x^7 + 124*x^8 - 129*x^9 + 49*x^10 - 7*x^11) / (1 - x)^9.
a(n) = 9*a(n-1) - 36*a(n-2) + 84*a(n-3) - 126*a(n-4) + 126*a(n-5) - 84*a(n-6) + 36*a(n-7) - 9*a(n-8) + a(n-9) for n>12.
(End)

Formalization notes:
* A 2 X n array with entries in 0..3 is a map A : Fin 2 → Fin n → Fin 4, row index first. Entries are compared as natural numbers.
* Sorted with lexicographically nondecreasing rows and nondecreasing columns: the rows, each read
  left to right as a list, are nondecreasing in lexicographic order from top to bottom, and the
  columns, each read top to bottom as a list, are nondecreasing in lexicographic order from left to
  right (`IsSorted`).
* The derived array holds at each position the minimum of the element there and of its
  horizontal or antidiagonal neighbours that lie inside the array (`minNb`). The relation
  `nb i j i' j'` says that position (i', j') is (i, j) itself or such a neighbour; the diagonal
  neighbours of (i, j) are (i - 1, j - 1) and (i + 1, j + 1), the antidiagonal ones
  (i - 1, j + 1) and (i + 1, j - 1).
* Counting the arrays of minima of a random sorted array means counting the distinct derived
  arrays as the source ranges over all sorted arrays: a(n) is the cardinality of the image of
  `minNb` on the sorted arrays. This reading reproduces the first terms by direct enumeration
  and every listed term of the entry by an exact transfer-matrix count.
* The statement is the conjunction of Barker's two conjectures: the g.f., as the identity
  A(x) (1 - x)^9 = (the entry's numerator) in the formal power series ring over the rationals with
  A(x) = Sum_{n >= 1} a(n) x^n; and the recurrence, for every n > 12, as an identity of integers.
-/

namespace OMA.S_oeis_a219472

open PowerSeries Finset

/-- Position (i', j') is (i, j) itself or one of its horizontal or antidiagonal neighbours. -/
def nb (i j i' j' : ℕ) : Prop :=
  (i' = i ∧ j' = j) ∨
    (i' = i ∧ (j' + 1 = j ∨ j' = j + 1)) ∨
    ((i' + 1 = i ∧ j' = j + 1) ∨ (i' = i + 1 ∧ j' + 1 = j))

instance (i j i' j' : ℕ) : Decidable (nb i j i' j') := by unfold nb; infer_instance

/-- Rows lexicographically nondecreasing from top to bottom, columns lexicographically
nondecreasing from left to right. -/
def IsSorted {r c : ℕ} (A : Fin r → Fin c → Fin 4) : Prop :=
  Monotone (fun i => List.ofFn (A i)) ∧ Monotone (fun j => List.ofFn (fun i => A i j))

instance {r c : ℕ} (A : Fin r → Fin c → Fin 4) : Decidable (IsSorted A) := by
  unfold IsSorted; infer_instance

/-- The array of minima of each element and its neighbours inside the array. -/
def minNb {r c : ℕ} (A : Fin r → Fin c → Fin 4) : Fin r → Fin c → Fin 4 := fun i j =>
  ((univ : Finset (Fin r × Fin c)).filter (fun p => nb i j p.1 p.2)).inf (fun p => A p.1 p.2)

/-- A219472: the number of distinct arrays of neighbourhood minima of sorted 2 X n 0..3 arrays. -/
def a (n : ℕ) : ℕ := ((univ.filter (fun A : Fin 2 → Fin n → Fin 4 => IsSorted A)).image minNb).card

/-- Barker's conjectures. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 9 =
      X * (10 - 67 * X + 221 * X ^ 2 - 413 * X ^ 3 + 424 * X ^ 4 - 153 * X ^ 5 - 91 * X ^ 6 + 35 * X ^ 7 + 124 * X ^ 8 - 129 * X ^ 9 + 49 * X ^ 10 - 7 * X ^ 11) ∧
    ∀ n : ℕ, 12 < n → (a n : ℤ) = 9 * a (n - 1) - 36 * a (n - 2) + 84 * a (n - 3) - 126 * a (n - 4) + 126 * a (n - 5) - 84 * a (n - 6) + 36 * a (n - 7) - 9 * a (n - 8) + a (n - 9) := by
  sorry

end OMA.S_oeis_a219472
