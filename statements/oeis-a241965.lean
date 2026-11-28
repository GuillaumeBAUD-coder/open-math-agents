import Mathlib

/-!
# A241965: Number of length 2+3 0..n arrays with no consecutive four elements summing to more than 2*n.

Source: https://oeis.org/A241965
Credit: @clementtrecourt

The conjectures listed in the entry, all stated below as one conjunction:
* G.f.: x*(19 + 10*x + 27*x^2 - 15*x^3 + 6*x^4 - x^5) / (1 - x)^6.
* a(n) = 6*a(n-1) - 15*a(n-2) + 20*a(n-3) - 15*a(n-4) + 6*a(n-5) - a(n-6) for n>6.

Conventions: length P+Q in the name is the array length P + Q; windows are runs of consecutive positions; this reading reproduces the OEIS data.
Offset 1: a(n) is the number of arrays (x_0, ..., x_4) of length 5 with entries in 0..n such that every 4 consecutive entries sum to at most 2 * n.
A brute-force count reproduces the listed terms for small n, and each formula was checked against every listed term (n up to 30).
-/

namespace OMA.S_oeis_a241965

/-- The entry of `x` at position `k` (`0` past the end). -/
def get {n : ℕ} (x : Fin 5 → Fin (n + 1)) (k : ℕ) : ℕ :=
  if h : k < 5 then (x ⟨k, h⟩ : ℕ) else 0

/-- The window condition: every 4 consecutive entries sum to at most 2 * n. -/
def good {n : ℕ} (x : Fin 5 → Fin (n + 1)) : Bool :=
  decide (∀ i < (2 : ℕ), (∑ t ∈ Finset.range 4, get x (i + t)) ≤ 2 * n)

/-- The number of arrays of length 5 with entries in `0..n` satisfying the window condition. -/
def a (n : ℕ) : ℤ :=
  ((Finset.univ : Finset (Fin 5 → Fin (n + 1))).filter (fun x => good x)).card

open PowerSeries in
theorem main :
    (PowerSeries.mk (fun n => if n < 1 then 0 else (a n : ℚ)) * ((1 - X) ^ 6 : PowerSeries ℚ) = X * (19 + 10 * X + 27 * X ^ 2 - 15 * X ^ 3 + 6 * X ^ 4 - X ^ 5)) ∧
    (∀ n : ℕ, 7 ≤ n → (a n : ℚ) = 6 * a (n - 1) - 15 * a (n - 2) + 20 * a (n - 3) - 15 * a (n - 4) + 6 * a (n - 5) - a (n - 6)) := by
  sorry

end OMA.S_oeis_a241965
