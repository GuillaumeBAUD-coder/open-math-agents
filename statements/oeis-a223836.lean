import Mathlib

/-!
# A223836: Number of n X 6 0..1 arrays with rows, diagonals and antidiagonals unimodal and columns nondecreasing.

Source: https://oeis.org/A223836
Credit: @prathameshnium (agent: Claude Code, model claude-opus-5-5)

The entry (R. H. Hardin, Mar 27 2013; column 6 of A223838; DATA 22, 148, 503, 1286, 2884, ...) records in its FORMULA section:

  Empirical: a(n) = (2/45)*n^6 + (55/36)*n^4 + (14/3)*n^3 + (3767/180)*n^2 + (293/6)*n - 116 for n>3.
  Conjectures from Colin Barker, Aug 23 2018:
  G.f.: x*(22 - 6*x - 71*x^2 + 103*x^3 + 35*x^4 - 77*x^5 + 10*x^6 + 22*x^7 - 4*x^8 - 2*x^9) / (1 - x)^7.
  a(n) = 7*a(n-1) - 21*a(n-2) + 35*a(n-3) - 35*a(n-4) + 21*a(n-5) - 7*a(n-6) + a(n-7) for n>10.

Conventions:
* Offset 1. An `n X 6` array with entries 0..1 is `x : Fin n → Fin 6 → Fin 2`, where `x i j` is
  the entry in row `i` and column `j`. `a n` counts such arrays for every `n`; the conjectures concern `n ≥ 1`.
* A finite sequence is unimodal when it is weakly increasing and then weakly decreasing. Equivalently, no
  entry is strictly smaller than both an earlier and a later entry of the sequence; the definitions below
  use this second form. Rows are read left to right and columns top to bottom.
* Columns are nondecreasing: entries do not decrease going down a column.
* A diagonal is the set of cells with `j - i` constant, an antidiagonal the set with `i + j` constant;
  both are read in order of increasing `i` (the direction does not matter for unimodality).
* Empirical formula: stated over ℚ for `n > 3`. G.f.: an identity of formal power series over ℚ,
  with coefficient 0 at `x^0` (offset 1). Recurrence: stated in ℤ for `n > 10`.

Numerical check: a Python copy of these definitions gives the DATA of the entry (22, 148, 503, 1286, ...) by
brute force over all arrays for small `n`.
-/

namespace OMA.S_oeis_a223836

open PowerSeries

/-- Every row is unimodal. -/
def RowsUnimodal {n : ℕ} (x : Fin n → Fin 6 → Fin 2) : Prop :=
  ∀ i : Fin n, ∀ j1 j2 j3 : Fin 6, j1 < j2 → j2 < j3 → ¬ (x i j2 < x i j1 ∧ x i j2 < x i j3)

instance {n : ℕ} (x : Fin n → Fin 6 → Fin 2) : Decidable (RowsUnimodal x) := by
  unfold RowsUnimodal; infer_instance

/-- Every column is nondecreasing downwards. -/
def ColumnsNondecreasing {n : ℕ} (x : Fin n → Fin 6 → Fin 2) : Prop :=
  ∀ i1 i2 : Fin n, ∀ j : Fin 6, i1 ≤ i2 → x i1 j ≤ x i2 j

instance {n : ℕ} (x : Fin n → Fin 6 → Fin 2) : Decidable (ColumnsNondecreasing x) := by
  unfold ColumnsNondecreasing; infer_instance

/-- Every diagonal (cells with `j - i` constant, read by increasing `i`) is unimodal. -/
def DiagonalsUnimodal {n : ℕ} (x : Fin n → Fin 6 → Fin 2) : Prop :=
  ∀ i1 i2 i3 : Fin n, ∀ j1 j2 j3 : Fin 6, i1 < i2 → i2 < i3 → (j1 : ℕ) + i2 = j2 + i1 →
    (j2 : ℕ) + i3 = j3 + i2 → ¬ (x i2 j2 < x i1 j1 ∧ x i2 j2 < x i3 j3)

instance {n : ℕ} (x : Fin n → Fin 6 → Fin 2) : Decidable (DiagonalsUnimodal x) := by
  unfold DiagonalsUnimodal; infer_instance

/-- Every antidiagonal (cells with `i + j` constant, read by increasing `i`) is unimodal. -/
def AntidiagonalsUnimodal {n : ℕ} (x : Fin n → Fin 6 → Fin 2) : Prop :=
  ∀ i1 i2 i3 : Fin n, ∀ j1 j2 j3 : Fin 6, i1 < i2 → i2 < i3 → (i1 : ℕ) + j1 = i2 + j2 →
    (i2 : ℕ) + j2 = i3 + j3 → ¬ (x i2 j2 < x i1 j1 ∧ x i2 j2 < x i3 j3)

instance {n : ℕ} (x : Fin n → Fin 6 → Fin 2) : Decidable (AntidiagonalsUnimodal x) := by
  unfold AntidiagonalsUnimodal; infer_instance

/-- A223836(n): the number of `n X 6` arrays with entries 0..1 whose rows, diagonals and antidiagonals are unimodal and whose columns are nondecreasing. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun x : Fin n → Fin 6 → Fin 2 => RowsUnimodal x ∧ ColumnsNondecreasing x ∧ DiagonalsUnimodal x ∧ AntidiagonalsUnimodal x)).card

/-- Hardin's empirical formula and Barker's conjectured g.f. and recurrence. -/
theorem main :
    (∀ n : ℕ, 3 < n → (a n : ℚ) = 2/45 * (n : ℚ) ^ 6 + 55/36 * (n : ℚ) ^ 4 + 14/3 * (n : ℚ) ^ 3 + 3767/180 * (n : ℚ) ^ 2 + 293/6 * (n : ℚ) - 116) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 7 =
      X * (22 - 6 * X - 71 * X ^ 2 + 103 * X ^ 3 + 35 * X ^ 4 - 77 * X ^ 5 + 10 * X ^ 6 + 22 * X ^ 7 - 4 * X ^ 8 - 2 * X ^ 9) ∧
    ∀ n : ℕ, 10 < n → (a n : ℤ) = 7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) - 35 * a (n - 4) + 21 * a (n - 5) - 7 * a (n - 6) + a (n - 7) := by
  sorry

end OMA.S_oeis_a223836
