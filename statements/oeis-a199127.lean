import Mathlib

/-!
# A199127: Number of n X 2 0..2 arrays with values 0..2 introduced in row major order, the number of instances of each value within one of each other, and no element equal to any horizontal or vertical neighbor.

Source: https://oeis.org/A199127 (OEIS Foundation, CC BY-SA 4.0)
Credit: @EmadY

Entry (R. H. Hardin), offset 1. Data: 1, 2, 2, 12, 30, 30, 210, 560, 560, 4200, 11550, ...
R. J. Mathar (Nov 01 2015), in the formula section of A199127:
  Conjecture: a(3n+2) = a(3n+3) = A208881(n+1).
  Conjecture: -(458*n-1205) *(n+2) *(n+1)*a(n) +(-208*n^3+2578*n^2-4613*n-2410) *a(n-1)
    +9*(-339*n-638) *a(n-2) +27*(n-2) *(458*n^2-289*n-1146) *a(n-3)
    +54*(n-2) *(n-3) *(104*n-1081) *a(n-4)=0.
  Conjecture: (n+2)*(n+1)*a(n) +(5*n^2-2)*a(n-1) +3*(5*n^2-15*n+3) *a(n-2)
    +3*(n^2 -60*n +81)*a(n-3) +135*(-n^2+3*n-1)*a(n-4) -405*(n-2)*(n-4) *a(n-5)
    -810*(n-4) *(n-5) *a(n-6)=0.

Formalization notes:
* An n X 2 array over 0..2 is `A : Fin n → Fin 2 → Fin 3`, with `A i j` the entry in row `i`,
  column `j`. Row major order puts cell `(i', j')` before `(i, j)` when `i' < i`, or `i' = i`
  and `j' < j`.
* Values introduced in row major order: every value smaller than the entry of a cell already
  occurs at an earlier cell (so the top left entry is 0, and each new value is one more than
  the largest earlier value). This is the convention of the sibling statement A199126.
* The number of instances of a value is the number of cells holding it; the numbers of
  instances of 0, 1 and 2 are within one of each other (a value that does not occur has 0
  instances).
* Horizontal neighbours are `(i, 0)` and `(i, 1)`; vertical neighbours are `(i, j)` and
  `(i + 1, j)`. No entry equals any of its neighbours.
* This reading reproduces the data terms of the entry (brute force for n <= 8).
* A208881 (offset 0) is the number of words, either empty or beginning with the first letter
  of the ternary alphabet, in which each letter occurs n times. The letters are written
  0, 1, 2, so these are the words w of length 3n over 0..2 with each value occurring n times
  and, when the word is not empty, w 0 = 0.
* A199127 has offset 1 and A208881 offset 0, so the first conjecture is stated for all n >= 0
  (every term then has its index in range). The two recurrences are stated for the n at which
  every term a(n-k) they use has index n - k >= 1: n >= 5 for the first and n >= 7 for the
  second. They are stated over the integers, with the polynomial coefficients as written.
* `main` is the conjunction of Mathar's three conjectures.
-/

namespace OMA.S_oeis_a199127

/-- The number of cells of the n X 2 array `A` that hold the value `v`. -/
def numOcc {n : ℕ} (A : Fin n → Fin 2 → Fin 3) (v : Fin 3) : ℕ :=
  (Finset.univ.filter (fun p : Fin n × Fin 2 => A p.1 p.2 = v)).card

/-- The array is counted by A199127: values introduced in row major order, the numbers of
instances of the values within one of each other, and no entry equal to a horizontal or
vertical neighbour. -/
def Valid {n : ℕ} (A : Fin n → Fin 2 → Fin 3) : Prop :=
  (∀ i : Fin n, ∀ j : Fin 2, ∀ v : Fin 3, v < A i j →
    ∃ i' : Fin n, ∃ j' : Fin 2, (i' < i ∨ (i' = i ∧ j' < j)) ∧ A i' j' = v) ∧
  (∀ u v : Fin 3, numOcc A u ≤ numOcc A v + 1) ∧
  (∀ i : Fin n, A i 0 ≠ A i 1) ∧
  (∀ i i' : Fin n, i.val + 1 = i'.val → ∀ j : Fin 2, A i j ≠ A i' j)

instance {n : ℕ} (A : Fin n → Fin 2 → Fin 3) : Decidable (Valid A) := by
  unfold Valid; infer_instance

/-- A199127(n): the number of valid n X 2 arrays over 0..2. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun A : Fin n → Fin 2 → Fin 3 => Valid A)).card

/-- The number of positions at which the word `w` has the value `v`. -/
def wordOcc {m : ℕ} (w : Fin m → Fin 3) (v : Fin 3) : ℕ :=
  (Finset.univ.filter (fun k : Fin m => w k = v)).card

/-- A208881(n): words of length 3n over 0..2 in which each value occurs n times and which are
empty or begin with 0. -/
def A208881 (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun w : Fin (3 * n) → Fin 3 =>
    (∀ v : Fin 3, wordOcc w v = n) ∧ ∀ h : 0 < 3 * n, w ⟨0, h⟩ = 0)).card

/-- Mathar's three conjectures for A199127. -/
theorem main :
    (∀ n : ℕ, a (3 * n + 2) = A208881 (n + 1) ∧ a (3 * n + 3) = A208881 (n + 1)) ∧
    (∀ n : ℕ, 5 ≤ n →
      -(458 * (n : ℤ) - 1205) * ((n : ℤ) + 2) * ((n : ℤ) + 1) * (a n : ℤ)
        + (-208 * (n : ℤ) ^ 3 + 2578 * (n : ℤ) ^ 2 - 4613 * (n : ℤ) - 2410) * (a (n - 1) : ℤ)
        + 9 * (-339 * (n : ℤ) - 638) * (a (n - 2) : ℤ)
        + 27 * ((n : ℤ) - 2) * (458 * (n : ℤ) ^ 2 - 289 * (n : ℤ) - 1146) * (a (n - 3) : ℤ)
        + 54 * ((n : ℤ) - 2) * ((n : ℤ) - 3) * (104 * (n : ℤ) - 1081) * (a (n - 4) : ℤ) = 0) ∧
    (∀ n : ℕ, 7 ≤ n →
      ((n : ℤ) + 2) * ((n : ℤ) + 1) * (a n : ℤ)
        + (5 * (n : ℤ) ^ 2 - 2) * (a (n - 1) : ℤ)
        + 3 * (5 * (n : ℤ) ^ 2 - 15 * (n : ℤ) + 3) * (a (n - 2) : ℤ)
        + 3 * ((n : ℤ) ^ 2 - 60 * (n : ℤ) + 81) * (a (n - 3) : ℤ)
        + 135 * (-(n : ℤ) ^ 2 + 3 * (n : ℤ) - 1) * (a (n - 4) : ℤ)
        - 405 * ((n : ℤ) - 2) * ((n : ℤ) - 4) * (a (n - 5) : ℤ)
        - 810 * ((n : ℤ) - 4) * ((n : ℤ) - 5) * (a (n - 6) : ℤ) = 0) := by
  sorry

end OMA.S_oeis_a199127
