import Mathlib

/-!
# OEIS A219715: Barker's conjectures for 2 X n arrays of neighbourhood minima of sorted 0..3 arrays

Source: https://oeis.org/A219715 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @marcusbuffett.

Entry A219715 (R. H. Hardin, Nov 26 2012), offset 1: Number of 2 X n arrays of the minimum value of corresponding elements and their horizontal or antidiagonal neighbors in a random, but sorted with lexicographically nondecreasing rows and nonincreasing columns, 0..3 2 X n array.
Formula section:
Empirical: a(n) = (1/10)*n^5 - (53/24)*n^4 + (117/4)*n^3 - (4099/24)*n^2 + (10233/20)*n - 594 for n>4.
Conjectures from _Colin Barker_, Jul 27 2018: (Start)
G.f.: x*(10 - 47*x + 117*x^2 - 150*x^3 + 98*x^4 - 27*x^5 + 16*x^6 - 31*x^7 + 30*x^8 - 4*x^9) / (1 - x)^6.
a(n) = 6*a(n-1) - 15*a(n-2) + 20*a(n-3) - 15*a(n-4) + 6*a(n-5) - a(n-6) for n>10.
(End)

Formalization notes:
* A 2 X n array with entries in 0..3 is a map A : Fin 2 → Fin n → Fin 4, row index first. Entries are compared as natural numbers.
* Sorted with lexicographically nondecreasing rows and nonincreasing columns: the rows, each read
  left to right as a list, are nondecreasing in lexicographic order from top to bottom, and the
  columns, each read top to bottom as a list, are nonincreasing in lexicographic order from left to
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
  A(x) (1 - x)^6 = (the entry's numerator) in the formal power series ring over the rationals with
  A(x) = Sum_{n >= 1} a(n) x^n; and the recurrence, for every n > 10, as an identity of integers.
-/

namespace OMA.S_oeis_a219715

open PowerSeries Finset

/-- Position (i', j') is (i, j) itself or one of its horizontal or antidiagonal neighbours. -/
def nb (i j i' j' : ℕ) : Prop :=
  (i' = i ∧ j' = j) ∨
    (i' = i ∧ (j' + 1 = j ∨ j' = j + 1)) ∨
    ((i' + 1 = i ∧ j' = j + 1) ∨ (i' = i + 1 ∧ j' + 1 = j))

instance (i j i' j' : ℕ) : Decidable (nb i j i' j') := by unfold nb; infer_instance

/-- Rows lexicographically nondecreasing from top to bottom, columns lexicographically
nonincreasing from left to right. -/
def IsSorted {r c : ℕ} (A : Fin r → Fin c → Fin 4) : Prop :=
  Monotone (fun i => List.ofFn (A i)) ∧ Antitone (fun j => List.ofFn (fun i => A i j))

instance {r c : ℕ} (A : Fin r → Fin c → Fin 4) : Decidable (IsSorted A) := by
  unfold IsSorted; infer_instance

/-- The array of minima of each element and its neighbours inside the array. -/
def minNb {r c : ℕ} (A : Fin r → Fin c → Fin 4) : Fin r → Fin c → Fin 4 := fun i j =>
  ((univ : Finset (Fin r × Fin c)).filter (fun p => nb i j p.1 p.2)).inf (fun p => A p.1 p.2)

/-- A219715: the number of distinct arrays of neighbourhood minima of sorted 2 X n 0..3 arrays. -/
def a (n : ℕ) : ℕ := ((univ.filter (fun A : Fin 2 → Fin n → Fin 4 => IsSorted A)).image minNb).card

/-- Barker's conjectures. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 6 =
      X * (10 - 47 * X + 117 * X ^ 2 - 150 * X ^ 3 + 98 * X ^ 4 - 27 * X ^ 5 + 16 * X ^ 6 - 31 * X ^ 7 + 30 * X ^ 8 - 4 * X ^ 9) ∧
    ∀ n : ℕ, 10 < n → (a n : ℤ) = 6 * a (n - 1) - 15 * a (n - 2) + 20 * a (n - 3) - 15 * a (n - 4) + 6 * a (n - 5) - a (n - 6) := by
  sorry

end OMA.S_oeis_a219715
