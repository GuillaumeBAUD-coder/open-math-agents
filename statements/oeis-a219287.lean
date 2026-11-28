import Mathlib

/-!
# OEIS A219287: Barker's conjectures for n X 4 arrays of neighbourhood minima of sorted 0..1 arrays

Source: https://oeis.org/A219287 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @marcusbuffett.

Entry A219287 (R. H. Hardin, Nov 17 2012), offset 1: Number of n X 4 arrays of the minimum value of corresponding elements and their horizontal or vertical neighbors in a random, but sorted with lexicographically nondecreasing rows and columns, 0..1 n X 4 array.
Formula section:
Empirical: a(n) = (1/2240)*n^8 - (1/90)*n^7 + (17/96)*n^6 - (373/360)*n^5 - (4459/960)*n^4 + (49529/360)*n^3 - (348947/336)*n^2 + (55477/15)*n - 5259 for n>6.
Conjectures from _Colin Barker_, Jul 25 2018: (Start)
G.f.: x*(4 - 27*x + 105*x^2 - 241*x^3 + 342*x^4 - 249*x^5 + x^6 + 204*x^7 - 240*x^8 + 223*x^9 - 206*x^10 + 161*x^11 - 76*x^12 + 22*x^13 - 5*x^14) / (1 - x)^9.
a(n) = 9*a(n-1) - 36*a(n-2) + 84*a(n-3) - 126*a(n-4) + 126*a(n-5) - 84*a(n-6) + 36*a(n-7) - 9*a(n-8) + a(n-9) for n>15.
(End)

Formalization notes:
* An n X 4 array with entries in 0..1 is a map A : Fin n → Fin 4 → Fin 2, row index first. Entries are compared as natural numbers.
* Sorted with lexicographically nondecreasing rows and nondecreasing columns: the rows, each read
  left to right as a list, are nondecreasing in lexicographic order from top to bottom, and the
  columns, each read top to bottom as a list, are nondecreasing in lexicographic order from left to
  right (`IsSorted`).
* The derived array holds at each position the minimum of the element there and of its
  horizontal or vertical neighbours that lie inside the array (`minNb`). The relation
  `nb i j i' j'` says that position (i', j') is (i, j) itself or such a neighbour; the diagonal
  neighbours of (i, j) are (i - 1, j - 1) and (i + 1, j + 1), the antidiagonal ones
  (i - 1, j + 1) and (i + 1, j - 1).
* Counting the arrays of minima of a random sorted array means counting the distinct derived
  arrays as the source ranges over all sorted arrays: a(n) is the cardinality of the image of
  `minNb` on the sorted arrays. This reading reproduces the first terms by direct enumeration
  and every listed term of the entry by an exact transfer-matrix count.
* The statement is the conjunction of Barker's two conjectures: the g.f., as the identity
  A(x) (1 - x)^9 = (the entry's numerator) in the formal power series ring over the rationals with
  A(x) = Sum_{n >= 1} a(n) x^n; and the recurrence, for every n > 15, as an identity of integers.
-/

namespace OMA.S_oeis_a219287

open PowerSeries Finset

/-- Position (i', j') is (i, j) itself or one of its horizontal or vertical neighbours. -/
def nb (i j i' j' : ℕ) : Prop :=
  (i' = i ∧ j' = j) ∨
    (i' = i ∧ (j' + 1 = j ∨ j' = j + 1)) ∨
    (j' = j ∧ (i' + 1 = i ∨ i' = i + 1))

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

/-- A219287: the number of distinct arrays of neighbourhood minima of sorted n X 4 0..1 arrays. -/
def a (n : ℕ) : ℕ := ((univ.filter (fun A : Fin n → Fin 4 → Fin 2 => IsSorted A)).image minNb).card

/-- Barker's conjectures. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 9 =
      X * (4 - 27 * X + 105 * X ^ 2 - 241 * X ^ 3 + 342 * X ^ 4 - 249 * X ^ 5 + X ^ 6 + 204 * X ^ 7 - 240 * X ^ 8 + 223 * X ^ 9 - 206 * X ^ 10 + 161 * X ^ 11 - 76 * X ^ 12 + 22 * X ^ 13 - 5 * X ^ 14) ∧
    ∀ n : ℕ, 15 < n → (a n : ℤ) = 9 * a (n - 1) - 36 * a (n - 2) + 84 * a (n - 3) - 126 * a (n - 4) + 126 * a (n - 5) - 84 * a (n - 6) + 36 * a (n - 7) - 9 * a (n - 8) + a (n - 9) := by
  sorry

end OMA.S_oeis_a219287
