import Mathlib

/-!
# A245873: Number of length 4+2 0..n arrays with some pair in every consecutive three terms totalling exactly n.

Source: https://oeis.org/A245873
Credit: @clementtrecourt

The conjectures listed in the entry, all stated below as one conjunction:
* G.f.: x*(26 + 161*x - 15*x^2 - 30*x^3 - 44*x^4 - 3*x^5 + x^6) / ((1 - x)^5*(1 + x)^2).
* a(n) = 1 + 7*n + 20*n^2 + 16*n^3 + n^4 for n even.
* a(n) = -8 - 3*n + 20*n^2 + 16*n^3 + n^4 for n odd.

Conventions: length P+Q in the name is the array length P + Q; windows are runs of consecutive positions; this reading reproduces the OEIS data.
Offset 1: a(n) is the number of arrays (x_0, ..., x_5) of length 6 with entries in 0..n such that every 3 consecutive entries contain two (at different positions) summing to exactly n.
A brute-force count reproduces the listed terms for small n, and each formula was checked against every listed term (n up to 32).
-/

namespace OMA.S_oeis_a245873

/-- The entry of `x` at position `k` (`0` past the end). -/
def get {n : ℕ} (x : Fin 6 → Fin (n + 1)) (k : ℕ) : ℕ :=
  if h : k < 6 then (x ⟨k, h⟩ : ℕ) else 0

/-- The window condition: every 3 consecutive entries contain two (at different positions) summing to exactly n. -/
def good {n : ℕ} (x : Fin 6 → Fin (n + 1)) : Bool :=
  decide (∀ i < (4 : ℕ), ∃ s < (3 : ℕ), ∃ t < (3 : ℕ), s < t ∧ get x (i + s) + get x (i + t) = n)

/-- The number of arrays of length 6 with entries in `0..n` satisfying the window condition. -/
def a (n : ℕ) : ℤ :=
  ((Finset.univ : Finset (Fin 6 → Fin (n + 1))).filter (fun x => good x)).card

open PowerSeries in
theorem main :
    (PowerSeries.mk (fun n => if n < 1 then 0 else (a n : ℚ)) * ((1 - X) ^ 5 * (1 + X) ^ 2 : PowerSeries ℚ) = X * (26 + 161 * X - 15 * X ^ 2 - 30 * X ^ 3 - 44 * X ^ 4 - 3 * X ^ 5 + X ^ 6)) ∧
    (∀ n : ℕ, 1 ≤ n → Even n → (a n : ℚ) = 1 + 7 * (n : ℚ) + 20 * (n : ℚ) ^ 2 + 16 * (n : ℚ) ^ 3 + (n : ℚ) ^ 4) ∧
    (∀ n : ℕ, 1 ≤ n → Odd n → (a n : ℚ) = -8 - 3 * (n : ℚ) + 20 * (n : ℚ) ^ 2 + 16 * (n : ℚ) ^ 3 + (n : ℚ) ^ 4) := by
  sorry

end OMA.S_oeis_a245873
