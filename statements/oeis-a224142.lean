import Mathlib

/-!
# A224142: Number of n X 4 0..1 arrays with rows and antidiagonals unimodal and columns nondecreasing.

Source: https://oeis.org/A224142
Credit: @prathameshnium (agent: Claude Code, model claude-opus-5-5)

The entry (R. H. Hardin, Mar 31 2013; column 4 of A224146; DATA 11, 46, 124, 272, 526, ...) records in its FORMULA section:

  Empirical: a(n) = (1/3)*n^4 + (4/3)*n^3 + (14/3)*n^2 + (23/3)*n - 4 for n>1.
  Conjectures from Colin Barker, Aug 27 2018:
  G.f.: x*(11 - 9*x + 4*x^2 + 2*x^3 + x^4 - x^5) / (1 - x)^5.
  a(n) = 5*a(n-1) - 10*a(n-2) + 10*a(n-3) - 5*a(n-4) + a(n-5) for n>6.

Conventions:
* Offset 1. An `n X 4` array with entries 0..1 is `x : Fin n → Fin 4 → Fin 2`, where `x i j` is
  the entry in row `i` and column `j`. `a n` counts such arrays for every `n`; the conjectures concern `n ≥ 1`.
* A finite sequence is unimodal when it is weakly increasing and then weakly decreasing. Equivalently, no
  entry is strictly smaller than both an earlier and a later entry of the sequence; the definitions below
  use this second form. Rows are read left to right and columns top to bottom.
* Columns are nondecreasing: entries do not decrease going down a column.
* A diagonal is the set of cells with `j - i` constant, an antidiagonal the set with `i + j` constant;
  both are read in order of increasing `i` (the direction does not matter for unimodality).
* Empirical formula: stated over ℚ for `n > 1`. G.f.: an identity of formal power series over ℚ,
  with coefficient 0 at `x^0` (offset 1). Recurrence: stated in ℤ for `n > 6`.

Numerical check: a Python copy of these definitions gives the DATA of the entry (11, 46, 124, 272, ...) by
brute force over all arrays for small `n`.
-/

namespace OMA.S_oeis_a224142

open PowerSeries

/-- Every row is unimodal. -/
def RowsUnimodal {n : ℕ} (x : Fin n → Fin 4 → Fin 2) : Prop :=
  ∀ i : Fin n, ∀ j1 j2 j3 : Fin 4, j1 < j2 → j2 < j3 → ¬ (x i j2 < x i j1 ∧ x i j2 < x i j3)

instance {n : ℕ} (x : Fin n → Fin 4 → Fin 2) : Decidable (RowsUnimodal x) := by
  unfold RowsUnimodal; infer_instance

/-- Every column is nondecreasing downwards. -/
def ColumnsNondecreasing {n : ℕ} (x : Fin n → Fin 4 → Fin 2) : Prop :=
  ∀ i1 i2 : Fin n, ∀ j : Fin 4, i1 ≤ i2 → x i1 j ≤ x i2 j

instance {n : ℕ} (x : Fin n → Fin 4 → Fin 2) : Decidable (ColumnsNondecreasing x) := by
  unfold ColumnsNondecreasing; infer_instance

/-- Every antidiagonal (cells with `i + j` constant, read by increasing `i`) is unimodal. -/
def AntidiagonalsUnimodal {n : ℕ} (x : Fin n → Fin 4 → Fin 2) : Prop :=
  ∀ i1 i2 i3 : Fin n, ∀ j1 j2 j3 : Fin 4, i1 < i2 → i2 < i3 → (i1 : ℕ) + j1 = i2 + j2 →
    (i2 : ℕ) + j2 = i3 + j3 → ¬ (x i2 j2 < x i1 j1 ∧ x i2 j2 < x i3 j3)

instance {n : ℕ} (x : Fin n → Fin 4 → Fin 2) : Decidable (AntidiagonalsUnimodal x) := by
  unfold AntidiagonalsUnimodal; infer_instance

/-- A224142(n): the number of `n X 4` arrays with entries 0..1 whose rows and antidiagonals are unimodal and whose columns are nondecreasing. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun x : Fin n → Fin 4 → Fin 2 => RowsUnimodal x ∧ ColumnsNondecreasing x ∧ AntidiagonalsUnimodal x)).card

/-- Hardin's empirical formula and Barker's conjectured g.f. and recurrence. -/
theorem main :
    (∀ n : ℕ, 1 < n → (a n : ℚ) = 1/3 * (n : ℚ) ^ 4 + 4/3 * (n : ℚ) ^ 3 + 14/3 * (n : ℚ) ^ 2 + 23/3 * (n : ℚ) - 4) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 5 =
      X * (11 - 9 * X + 4 * X ^ 2 + 2 * X ^ 3 + X ^ 4 - X ^ 5) ∧
    ∀ n : ℕ, 6 < n → (a n : ℤ) = 5 * a (n - 1) - 10 * a (n - 2) + 10 * a (n - 3) - 5 * a (n - 4) + a (n - 5) := by
  sorry

end OMA.S_oeis_a224142
