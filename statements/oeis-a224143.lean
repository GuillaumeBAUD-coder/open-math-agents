import Mathlib

/-!
# A224143: Number of n X 5 0..1 arrays with rows and antidiagonals unimodal and columns nondecreasing.

Source: https://oeis.org/A224143
Credit: @prathameshnium (agent: Claude Code, model claude-opus-5-5)

The entry (R. H. Hardin, Mar 31 2013; column 5 of A224146; DATA 16, 86, 275, 691, 1509, ...) records in its FORMULA section:

  Empirical: a(n) = (2/15)*n^5 + (2/3)*n^4 + (10/3)*n^3 + (25/3)*n^2 + (203/15)*n - 17 for n>2.
  Conjectures from Colin Barker, Aug 27 2018:
  G.f.: x*(16 - 10*x - x^2 + 11*x^3 + 8*x^4 - 10*x^5 + x^6 + x^7) / (1 - x)^6.
  a(n) = 6*a(n-1) - 15*a(n-2) + 20*a(n-3) - 15*a(n-4) + 6*a(n-5) - a(n-6) for n>8.

Conventions:
* Offset 1. An `n X 5` array with entries 0..1 is `x : Fin n → Fin 5 → Fin 2`, where `x i j` is
  the entry in row `i` and column `j`. `a n` counts such arrays for every `n`; the conjectures concern `n ≥ 1`.
* A finite sequence is unimodal when it is weakly increasing and then weakly decreasing. Equivalently, no
  entry is strictly smaller than both an earlier and a later entry of the sequence; the definitions below
  use this second form. Rows are read left to right and columns top to bottom.
* Columns are nondecreasing: entries do not decrease going down a column.
* A diagonal is the set of cells with `j - i` constant, an antidiagonal the set with `i + j` constant;
  both are read in order of increasing `i` (the direction does not matter for unimodality).
* Empirical formula: stated over ℚ for `n > 2`. G.f.: an identity of formal power series over ℚ,
  with coefficient 0 at `x^0` (offset 1). Recurrence: stated in ℤ for `n > 8`.

Numerical check: a Python copy of these definitions gives the DATA of the entry (16, 86, 275, 691, ...) by
brute force over all arrays for small `n`.
-/

namespace OMA.S_oeis_a224143

open PowerSeries

/-- Every row is unimodal. -/
def RowsUnimodal {n : ℕ} (x : Fin n → Fin 5 → Fin 2) : Prop :=
  ∀ i : Fin n, ∀ j1 j2 j3 : Fin 5, j1 < j2 → j2 < j3 → ¬ (x i j2 < x i j1 ∧ x i j2 < x i j3)

instance {n : ℕ} (x : Fin n → Fin 5 → Fin 2) : Decidable (RowsUnimodal x) := by
  unfold RowsUnimodal; infer_instance

/-- Every column is nondecreasing downwards. -/
def ColumnsNondecreasing {n : ℕ} (x : Fin n → Fin 5 → Fin 2) : Prop :=
  ∀ i1 i2 : Fin n, ∀ j : Fin 5, i1 ≤ i2 → x i1 j ≤ x i2 j

instance {n : ℕ} (x : Fin n → Fin 5 → Fin 2) : Decidable (ColumnsNondecreasing x) := by
  unfold ColumnsNondecreasing; infer_instance

/-- Every antidiagonal (cells with `i + j` constant, read by increasing `i`) is unimodal. -/
def AntidiagonalsUnimodal {n : ℕ} (x : Fin n → Fin 5 → Fin 2) : Prop :=
  ∀ i1 i2 i3 : Fin n, ∀ j1 j2 j3 : Fin 5, i1 < i2 → i2 < i3 → (i1 : ℕ) + j1 = i2 + j2 →
    (i2 : ℕ) + j2 = i3 + j3 → ¬ (x i2 j2 < x i1 j1 ∧ x i2 j2 < x i3 j3)

instance {n : ℕ} (x : Fin n → Fin 5 → Fin 2) : Decidable (AntidiagonalsUnimodal x) := by
  unfold AntidiagonalsUnimodal; infer_instance

/-- A224143(n): the number of `n X 5` arrays with entries 0..1 whose rows and antidiagonals are unimodal and whose columns are nondecreasing. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun x : Fin n → Fin 5 → Fin 2 => RowsUnimodal x ∧ ColumnsNondecreasing x ∧ AntidiagonalsUnimodal x)).card

/-- Hardin's empirical formula and Barker's conjectured g.f. and recurrence. -/
theorem main :
    (∀ n : ℕ, 2 < n → (a n : ℚ) = 2/15 * (n : ℚ) ^ 5 + 2/3 * (n : ℚ) ^ 4 + 10/3 * (n : ℚ) ^ 3 + 25/3 * (n : ℚ) ^ 2 + 203/15 * (n : ℚ) - 17) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 6 =
      X * (16 - 10 * X - X ^ 2 + 11 * X ^ 3 + 8 * X ^ 4 - 10 * X ^ 5 + X ^ 6 + X ^ 7) ∧
    ∀ n : ℕ, 8 < n → (a n : ℤ) = 6 * a (n - 1) - 15 * a (n - 2) + 20 * a (n - 3) - 15 * a (n - 4) + 6 * a (n - 5) - a (n - 6) := by
  sorry

end OMA.S_oeis_a224143
