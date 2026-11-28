import Mathlib

/-!
# A223632: Number of n X 3 0..1 arrays with rows, antidiagonals and columns unimodal.

Source: https://oeis.org/A223632
Credit: @prathameshnium (agent: Claude Code, model claude-opus-5-5)

The entry (R. H. Hardin, Mar 24 2013; column 3 of A223637; DATA 7, 49, 229, 801, 2297, ...) records in its FORMULA section:

  Empirical: a(n) = (23/360)*n^6 + (11/120)*n^5 + (91/72)*n^4 + (11/8)*n^3 + (301/180)*n^2 + (23/15)*n + 1.
  Conjectures from Colin Barker, Aug 21 2018:
  G.f.: x*(7 + 33*x^2 - 18*x^3 + 29*x^4 - 6*x^5 + x^6) / (1 - x)^7.
  a(n) = 7*a(n-1) - 21*a(n-2) + 35*a(n-3) - 35*a(n-4) + 21*a(n-5) - 7*a(n-6) + a(n-7) for n>7.

Conventions:
* Offset 1. An `n X 3` array with entries 0..1 is `x : Fin n → Fin 3 → Fin 2`, where `x i j` is
  the entry in row `i` and column `j`. `a n` counts such arrays for every `n`; the conjectures concern `n ≥ 1`.
* A finite sequence is unimodal when it is weakly increasing and then weakly decreasing. Equivalently, no
  entry is strictly smaller than both an earlier and a later entry of the sequence; the definitions below
  use this second form. Rows are read left to right and columns top to bottom.
* A diagonal is the set of cells with `j - i` constant, an antidiagonal the set with `i + j` constant;
  both are read in order of increasing `i` (the direction does not matter for unimodality).
* Empirical formula: stated over ℚ for `n > 0` (all `n ≥ 1`). G.f.: an identity of formal power series over ℚ,
  with coefficient 0 at `x^0` (offset 1). Recurrence: stated in ℤ for `n > 7`.

Numerical check: a Python copy of these definitions gives the DATA of the entry (7, 49, 229, 801, ...) by
brute force over all arrays for small `n`.
-/

namespace OMA.S_oeis_a223632

open PowerSeries

/-- Every row is unimodal. -/
def RowsUnimodal {n : ℕ} (x : Fin n → Fin 3 → Fin 2) : Prop :=
  ∀ i : Fin n, ∀ j1 j2 j3 : Fin 3, j1 < j2 → j2 < j3 → ¬ (x i j2 < x i j1 ∧ x i j2 < x i j3)

instance {n : ℕ} (x : Fin n → Fin 3 → Fin 2) : Decidable (RowsUnimodal x) := by
  unfold RowsUnimodal; infer_instance

/-- Every column is unimodal. -/
def ColumnsUnimodal {n : ℕ} (x : Fin n → Fin 3 → Fin 2) : Prop :=
  ∀ i1 i2 i3 : Fin n, ∀ j : Fin 3, i1 < i2 → i2 < i3 → ¬ (x i2 j < x i1 j ∧ x i2 j < x i3 j)

instance {n : ℕ} (x : Fin n → Fin 3 → Fin 2) : Decidable (ColumnsUnimodal x) := by
  unfold ColumnsUnimodal; infer_instance

/-- Every antidiagonal (cells with `i + j` constant, read by increasing `i`) is unimodal. -/
def AntidiagonalsUnimodal {n : ℕ} (x : Fin n → Fin 3 → Fin 2) : Prop :=
  ∀ i1 i2 i3 : Fin n, ∀ j1 j2 j3 : Fin 3, i1 < i2 → i2 < i3 → (i1 : ℕ) + j1 = i2 + j2 →
    (i2 : ℕ) + j2 = i3 + j3 → ¬ (x i2 j2 < x i1 j1 ∧ x i2 j2 < x i3 j3)

instance {n : ℕ} (x : Fin n → Fin 3 → Fin 2) : Decidable (AntidiagonalsUnimodal x) := by
  unfold AntidiagonalsUnimodal; infer_instance

/-- A223632(n): the number of `n X 3` arrays with entries 0..1 whose rows, columns and antidiagonals are unimodal. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun x : Fin n → Fin 3 → Fin 2 => RowsUnimodal x ∧ ColumnsUnimodal x ∧ AntidiagonalsUnimodal x)).card

/-- Hardin's empirical formula and Barker's conjectured g.f. and recurrence. -/
theorem main :
    (∀ n : ℕ, 0 < n → (a n : ℚ) = 23/360 * (n : ℚ) ^ 6 + 11/120 * (n : ℚ) ^ 5 + 91/72 * (n : ℚ) ^ 4 + 11/8 * (n : ℚ) ^ 3 + 301/180 * (n : ℚ) ^ 2 + 23/15 * (n : ℚ) + 1) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 7 =
      X * (7 + 33 * X ^ 2 - 18 * X ^ 3 + 29 * X ^ 4 - 6 * X ^ 5 + X ^ 6) ∧
    ∀ n : ℕ, 7 < n → (a n : ℤ) = 7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) - 35 * a (n - 4) + 21 * a (n - 5) - 7 * a (n - 6) + a (n - 7) := by
  sorry

end OMA.S_oeis_a223632
