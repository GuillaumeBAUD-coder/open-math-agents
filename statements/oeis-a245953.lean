import Mathlib

/-!
# A245953: Number of length 3+3 0..n arrays with some pair in every consecutive four terms totalling exactly n.

Source: https://oeis.org/A245953
Credit: @clementtrecourt

The conjectures listed in the entry, all stated below as one conjunction:
* G.f.: x*(48 + 401*x + 669*x^2 + 1241*x^3 - 851*x^4 - 557*x^5 + 7*x^6 + 3*x^7 - x^8) / ((1 - x)^6*(1 + x)^3).
* a(n) = 1 + 26*n - 17*n^2 + 24*n^3 + 21*n^4 + n^5 for n even.
* a(n) = 39 - n - 36*n^2 + 24*n^3 + 21*n^4 + n^5 for n odd.

Conventions: length P+Q in the name is the array length P + Q; windows are runs of consecutive positions; this reading reproduces the OEIS data.
Offset 1: a(n) is the number of arrays (x_0, ..., x_5) of length 6 with entries in 0..n such that every 4 consecutive entries contain two (at different positions) summing to exactly n.
A brute-force count reproduces the listed terms for small n, and each formula was checked against every listed term (n up to 29).
-/

namespace OMA.S_oeis_a245953

/-- The entry of `x` at position `k` (`0` past the end). -/
def get {n : ℕ} (x : Fin 6 → Fin (n + 1)) (k : ℕ) : ℕ :=
  if h : k < 6 then (x ⟨k, h⟩ : ℕ) else 0

/-- The window condition: every 4 consecutive entries contain two (at different positions) summing to exactly n. -/
def good {n : ℕ} (x : Fin 6 → Fin (n + 1)) : Bool :=
  decide (∀ i < (3 : ℕ), ∃ s < (4 : ℕ), ∃ t < (4 : ℕ), s < t ∧ get x (i + s) + get x (i + t) = n)

/-- The number of arrays of length 6 with entries in `0..n` satisfying the window condition. -/
def a (n : ℕ) : ℤ :=
  ((Finset.univ : Finset (Fin 6 → Fin (n + 1))).filter (fun x => good x)).card

open PowerSeries in
theorem main :
    (PowerSeries.mk (fun n => if n < 1 then 0 else (a n : ℚ)) * ((1 - X) ^ 6 * (1 + X) ^ 3 : PowerSeries ℚ) = X * (48 + 401 * X + 669 * X ^ 2 + 1241 * X ^ 3 - 851 * X ^ 4 - 557 * X ^ 5 + 7 * X ^ 6 + 3 * X ^ 7 - X ^ 8)) ∧
    (∀ n : ℕ, 1 ≤ n → Even n → (a n : ℚ) = 1 + 26 * (n : ℚ) - 17 * (n : ℚ) ^ 2 + 24 * (n : ℚ) ^ 3 + 21 * (n : ℚ) ^ 4 + (n : ℚ) ^ 5) ∧
    (∀ n : ℕ, 1 ≤ n → Odd n → (a n : ℚ) = 39 - (n : ℚ) - 36 * (n : ℚ) ^ 2 + 24 * (n : ℚ) ^ 3 + 21 * (n : ℚ) ^ 4 + (n : ℚ) ^ 5) := by
  sorry

end OMA.S_oeis_a245953
