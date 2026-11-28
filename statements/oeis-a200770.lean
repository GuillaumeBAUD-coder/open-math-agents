import Mathlib

/-!
# A200770: Number of nX1 0..2 arrays with every row and column running average nondecreasing rightwards and downwards, and the number of instances of each value within one of each other.

Source: https://oeis.org/A200770 (OEIS Foundation, CC BY-SA 4.0)
Credit: @EmadY

Entry (R. H. Hardin), offset 1. Data: 3, 3, 2, 7, 9, 6, 22, 30, 20, 75, 105, 70, 266, ...
R. J. Mathar (Nov 23 2011), corrected by Jason Yuen (Oct 14 2025), in the formula section:
  Conjecture: (n+2)*(2770*n-4893)*a(n) + 3*(1090*n^2-4919*n+1654)*a(n-1) + 4686*a(n-2)
    + 2*(-5540*n^2+7016*n+17127)*a(n-3) - 6*(1090*n-2739)*(2*n-7)*a(n-4) = 0.

Formalization notes:
* An n X 1 array over 0..2 is a word `w : Fin n → Fin 3`, with `w i` the entry in row `i` (the
  convention of the sibling statement A199126). Every row has a single entry, so the condition on
  the rows (running average nondecreasing rightwards) holds automatically.
* The running average of the column down to row `i` is (w 0 + ... + w i) / (i + 1), computed in
  ℚ. Nondecreasing downwards: for every pair of consecutive rows `i`, `i + 1`, the running average
  down to row `i` is at most the running average down to row `i + 1`.
* The number of instances of a value is the number of rows holding it; the numbers of instances
  of 0, 1 and 2 are within one of each other (a value that does not occur has 0 instances).
* This reading reproduces the data terms of the entry (brute force for n <= 12).
* The recurrence is the corrected one shown in the entry. A200770 has offset 1, so it is stated
  for the n at which every term a(n-k) it uses has index n - k >= 1, that is n >= 5. It is
  stated over the integers, with the polynomial coefficients as written.
-/

namespace OMA.S_oeis_a200770

/-- The number of rows of the n X 1 array `w` that hold the value `v`. -/
def numOcc {n : ℕ} (w : Fin n → Fin 3) (v : Fin 3) : ℕ :=
  (Finset.univ.filter (fun i : Fin n => w i = v)).card

/-- The running average of the column of `w` down to row `i`. -/
def runAvg {n : ℕ} (w : Fin n → Fin 3) (i : Fin n) : ℚ :=
  (∑ k ∈ Finset.univ.filter (fun k : Fin n => k ≤ i), ((w k).val : ℚ)) / ((i.val : ℚ) + 1)

/-- The n X 1 array `w` is counted by A200770: the running average of the column is
nondecreasing downwards, and the numbers of instances of the values are within one of each
other. -/
def Valid {n : ℕ} (w : Fin n → Fin 3) : Prop :=
  (∀ i j : Fin n, i.val + 1 = j.val → runAvg w i ≤ runAvg w j) ∧
  (∀ u v : Fin 3, numOcc w u ≤ numOcc w v + 1)

instance {n : ℕ} (w : Fin n → Fin 3) : Decidable (Valid w) := by
  unfold Valid; infer_instance

/-- A200770(n): the number of valid n X 1 arrays over 0..2. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun w : Fin n → Fin 3 => Valid w)).card

/-- Mathar's conjectured recurrence for A200770 (as corrected by Jason Yuen). -/
theorem main : ∀ n : ℕ, 5 ≤ n →
    ((n : ℤ) + 2) * (2770 * (n : ℤ) - 4893) * (a n : ℤ)
      + 3 * (1090 * (n : ℤ) ^ 2 - 4919 * (n : ℤ) + 1654) * (a (n - 1) : ℤ)
      + 4686 * (a (n - 2) : ℤ)
      + 2 * (-5540 * (n : ℤ) ^ 2 + 7016 * (n : ℤ) + 17127) * (a (n - 3) : ℤ)
      - 6 * (1090 * (n : ℤ) - 2739) * (2 * (n : ℤ) - 7) * (a (n - 4) : ℤ) = 0 := by
  sorry

end OMA.S_oeis_a200770
