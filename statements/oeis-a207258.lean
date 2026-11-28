import Mathlib

/-!
# A207258: Number of 7 X n 0..1 arrays avoiding 0 0 1 and 1 0 1 horizontally and 0 1 0 and 1 0 1 vertically.

Source: https://oeis.org/A207258
Credit: @clementtrecourt

The conjectures listed in the entry, all stated below as one conjunction:
* G.f.: 42*x*(1 + 34*x + 35*x^2 - 96*x^3 + 15*x^4 + 14*x^5 - x^6) / (1 - x)^8.
* a(n) = 8*a(n-1) - 28*a(n-2) + 56*a(n-3) - 70*a(n-4) + 56*a(n-5) - 28*a(n-6) + 8*a(n-7) - a(n-8) for n>8.

Conventions: patterns are read left to right along rows and top to bottom along columns (this reading reproduces the OEIS data).
Offset 1: a(n) is the number of arrays with 7 rows and n columns, entries in 0..1, in which no three consecutive entries of a row (left to right) form 0 0 1 or 1 0 1 and no three consecutive entries of a column (top to bottom) form 0 1 0 or 1 0 1.
An independent transfer-matrix count reproduces the first 24 listed terms, and each formula was checked against every listed term (n up to 24).
-/

namespace OMA.S_oeis_a207258

/-- The entry of `x` in row `i`, column `j` (`0` outside the array). -/
def get {r c : ℕ} (x : Fin r → Fin c → Fin 2) (i j : ℕ) : ℕ :=
  if h : i < r ∧ j < c then (x ⟨i, h.1⟩ ⟨j, h.2⟩ : ℕ) else 0

/-- `x` avoids the two patterns horizontally (three consecutive entries of a row, read left to
right) and the two patterns vertically (three consecutive entries of a column, read top to
bottom). -/
def avoids {r c : ℕ} (x : Fin r → Fin c → Fin 2) : Bool :=
  decide ((∀ i < r, ∀ j < c - 2, (get x i j, get x i (j + 1), get x i (j + 2)) ≠ (0, 0, 1) ∧ (get x i j, get x i (j + 1), get x i (j + 2)) ≠ (1, 0, 1)) ∧
    (∀ i < r - 2, ∀ j < c, (get x i j, get x (i + 1) j, get x (i + 2) j) ≠ (0, 1, 0) ∧ (get x i j, get x (i + 1) j, get x (i + 2) j) ≠ (1, 0, 1)))

/-- The number of 7 × n arrays with entries in `0..1` (`7` rows, `n` columns) avoiding the patterns. -/
def a (n : ℕ) : ℤ :=
  ((Finset.univ : Finset (Fin 7 → Fin n → Fin 2)).filter (fun x => avoids x)).card

open PowerSeries in
theorem main :
    (PowerSeries.mk (fun n => if n < 1 then 0 else (a n : ℚ)) * ((1 - X) ^ 8 : PowerSeries ℚ) = 42 * X * (1 + 34 * X + 35 * X ^ 2 - 96 * X ^ 3 + 15 * X ^ 4 + 14 * X ^ 5 - X ^ 6)) ∧
    (∀ n : ℕ, 9 ≤ n → (a n : ℚ) = 8 * a (n - 1) - 28 * a (n - 2) + 56 * a (n - 3) - 70 * a (n - 4) + 56 * a (n - 5) - 28 * a (n - 6) + 8 * a (n - 7) - a (n - 8)) := by
  sorry

end OMA.S_oeis_a207258
