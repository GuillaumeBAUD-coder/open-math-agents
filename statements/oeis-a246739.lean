import Mathlib

/-!
# A246739: Number of length 2+4 0..n arrays with no pair in any consecutive five terms totalling exactly n.

Source: https://oeis.org/A246739
Credit: @clementtrecourt

The conjectures listed in the entry, all stated below as one conjunction:
* G.f.: 2*x*(1 + 5*x + 105*x^2 + 161*x^3 + 1023*x^4 + 655*x^5 + 2211*x^6 + 523*x^7 + 1076*x^8) / ((1 - x)^7*(1 + x)^4).
* a(n) = -58*n + 111*n^2 - 87*n^3 + 36*n^4 - 8*n^5 + n^6 for n even.
* a(n) = -70 + 80*n + 34*n^2 - 71*n^3 + 36*n^4 - 8*n^5 + n^6 for n odd.

Conventions: length P+Q in the name is the array length P + Q; windows are runs of consecutive positions; this reading reproduces the OEIS data.
Offset 1: a(n) is the number of arrays (x_0, ..., x_5) of length 6 with entries in 0..n such that no 5 consecutive entries contain two (at different positions) summing to exactly n.
A brute-force count reproduces the listed terms for small n, and each formula was checked against every listed term (n up to 27).
-/

namespace OMA.S_oeis_a246739

/-- The entry of `x` at position `k` (`0` past the end). -/
def get {n : ℕ} (x : Fin 6 → Fin (n + 1)) (k : ℕ) : ℕ :=
  if h : k < 6 then (x ⟨k, h⟩ : ℕ) else 0

/-- The window condition: no 5 consecutive entries contain two (at different positions) summing to exactly n. -/
def good {n : ℕ} (x : Fin 6 → Fin (n + 1)) : Bool :=
  decide (∀ i < (2 : ℕ), ∀ s < (5 : ℕ), ∀ t < (5 : ℕ), s < t → get x (i + s) + get x (i + t) ≠ n)

/-- The number of arrays of length 6 with entries in `0..n` satisfying the window condition. -/
def a (n : ℕ) : ℤ :=
  ((Finset.univ : Finset (Fin 6 → Fin (n + 1))).filter (fun x => good x)).card

open PowerSeries in
theorem main :
    (PowerSeries.mk (fun n => if n < 1 then 0 else (a n : ℚ)) * ((1 - X) ^ 7 * (1 + X) ^ 4 : PowerSeries ℚ) = 2 * X * (1 + 5 * X + 105 * X ^ 2 + 161 * X ^ 3 + 1023 * X ^ 4 + 655 * X ^ 5 + 2211 * X ^ 6 + 523 * X ^ 7 + 1076 * X ^ 8)) ∧
    (∀ n : ℕ, 1 ≤ n → Even n → (a n : ℚ) = -58 * (n : ℚ) + 111 * (n : ℚ) ^ 2 - 87 * (n : ℚ) ^ 3 + 36 * (n : ℚ) ^ 4 - 8 * (n : ℚ) ^ 5 + (n : ℚ) ^ 6) ∧
    (∀ n : ℕ, 1 ≤ n → Odd n → (a n : ℚ) = -70 + 80 * (n : ℚ) + 34 * (n : ℚ) ^ 2 - 71 * (n : ℚ) ^ 3 + 36 * (n : ℚ) ^ 4 - 8 * (n : ℚ) ^ 5 + (n : ℚ) ^ 6) := by
  sorry

end OMA.S_oeis_a246739
