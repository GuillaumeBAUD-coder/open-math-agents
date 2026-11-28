import Mathlib

/-!
# A223633: Number of n X 4 0..1 arrays with rows, antidiagonals and columns unimodal.

Source: https://oeis.org/A223633
Credit: @prathameshnium (agent: Claude Code, model claude-opus-5-5)

The entry (R. H. Hardin, Mar 24 2013; column 4 of A223637; DATA 11, 121, 801, 3712, 13599, ...) records in its FORMULA section:

  Empirical: a(n) = (1/112)*n^8 - (1/72)*n^7 + (203/360)*n^6 + (37/360)*n^5 + (41/144)*n^4 + (901/36)*n^3 - (168481/2520)*n^2 + (5693/60)*n - 45 for n>2.
  Conjectures from Colin Barker, Aug 21 2018:
  G.f.: x*(11 + 22*x + 108*x^2 - 65*x^3 + 249*x^4 - 74*x^5 + 92*x^6 + 18*x^7 + 9*x^8 - 11*x^9 + x^10) / (1 - x)^9.
  a(n) = 9*a(n-1) - 36*a(n-2) + 84*a(n-3) - 126*a(n-4) + 126*a(n-5) - 84*a(n-6) + 36*a(n-7) - 9*a(n-8) + a(n-9) for n>11.

Conventions:
* Offset 1. An `n X 4` array with entries 0..1 is `x : Fin n → Fin 4 → Fin 2`, where `x i j` is
  the entry in row `i` and column `j`. `a n` counts such arrays for every `n`; the conjectures concern `n ≥ 1`.
* A finite sequence is unimodal when it is weakly increasing and then weakly decreasing. Equivalently, no
  entry is strictly smaller than both an earlier and a later entry of the sequence; the definitions below
  use this second form. Rows are read left to right and columns top to bottom.
* A diagonal is the set of cells with `j - i` constant, an antidiagonal the set with `i + j` constant;
  both are read in order of increasing `i` (the direction does not matter for unimodality).
* Empirical formula: stated over ℚ for `n > 2`. G.f.: an identity of formal power series over ℚ,
  with coefficient 0 at `x^0` (offset 1). Recurrence: stated in ℤ for `n > 11`.

Numerical check: a Python copy of these definitions gives the DATA of the entry (11, 121, 801, 3712, ...) by
brute force over all arrays for small `n`.
-/

namespace OMA.S_oeis_a223633

open PowerSeries

/-- Every row is unimodal. -/
def RowsUnimodal {n : ℕ} (x : Fin n → Fin 4 → Fin 2) : Prop :=
  ∀ i : Fin n, ∀ j1 j2 j3 : Fin 4, j1 < j2 → j2 < j3 → ¬ (x i j2 < x i j1 ∧ x i j2 < x i j3)

instance {n : ℕ} (x : Fin n → Fin 4 → Fin 2) : Decidable (RowsUnimodal x) := by
  unfold RowsUnimodal; infer_instance

/-- Every column is unimodal. -/
def ColumnsUnimodal {n : ℕ} (x : Fin n → Fin 4 → Fin 2) : Prop :=
  ∀ i1 i2 i3 : Fin n, ∀ j : Fin 4, i1 < i2 → i2 < i3 → ¬ (x i2 j < x i1 j ∧ x i2 j < x i3 j)

instance {n : ℕ} (x : Fin n → Fin 4 → Fin 2) : Decidable (ColumnsUnimodal x) := by
  unfold ColumnsUnimodal; infer_instance

/-- Every antidiagonal (cells with `i + j` constant, read by increasing `i`) is unimodal. -/
def AntidiagonalsUnimodal {n : ℕ} (x : Fin n → Fin 4 → Fin 2) : Prop :=
  ∀ i1 i2 i3 : Fin n, ∀ j1 j2 j3 : Fin 4, i1 < i2 → i2 < i3 → (i1 : ℕ) + j1 = i2 + j2 →
    (i2 : ℕ) + j2 = i3 + j3 → ¬ (x i2 j2 < x i1 j1 ∧ x i2 j2 < x i3 j3)

instance {n : ℕ} (x : Fin n → Fin 4 → Fin 2) : Decidable (AntidiagonalsUnimodal x) := by
  unfold AntidiagonalsUnimodal; infer_instance

/-- A223633(n): the number of `n X 4` arrays with entries 0..1 whose rows, columns and antidiagonals are unimodal. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun x : Fin n → Fin 4 → Fin 2 => RowsUnimodal x ∧ ColumnsUnimodal x ∧ AntidiagonalsUnimodal x)).card

/-- Hardin's empirical formula and Barker's conjectured g.f. and recurrence. -/
theorem main :
    (∀ n : ℕ, 2 < n → (a n : ℚ) = 1/112 * (n : ℚ) ^ 8 - 1/72 * (n : ℚ) ^ 7 + 203/360 * (n : ℚ) ^ 6 + 37/360 * (n : ℚ) ^ 5 + 41/144 * (n : ℚ) ^ 4 + 901/36 * (n : ℚ) ^ 3 - 168481/2520 * (n : ℚ) ^ 2 + 5693/60 * (n : ℚ) - 45) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 9 =
      X * (11 + 22 * X + 108 * X ^ 2 - 65 * X ^ 3 + 249 * X ^ 4 - 74 * X ^ 5 + 92 * X ^ 6 + 18 * X ^ 7 + 9 * X ^ 8 - 11 * X ^ 9 + X ^ 10) ∧
    ∀ n : ℕ, 11 < n → (a n : ℤ) = 9 * a (n - 1) - 36 * a (n - 2) + 84 * a (n - 3) - 126 * a (n - 4) + 126 * a (n - 5) - 84 * a (n - 6) + 36 * a (n - 7) - 9 * a (n - 8) + a (n - 9) := by
  sorry

end OMA.S_oeis_a223633
