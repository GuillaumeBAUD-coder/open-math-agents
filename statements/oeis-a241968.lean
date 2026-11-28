import Mathlib

/-!
# A241968: Number of length 5+3 0..n arrays with no consecutive four elements summing to more than 2*n.

Source: https://oeis.org/A241968
Credit: @clementtrecourt

The conjectures listed in the entry, all stated below as one conjunction:
* G.f.: x*(97 + 1022*x + 3086*x^2 + 2268*x^3 + 632*x^4 - 65*x^5 + 36*x^6 - 9*x^7 + x^8) / (1 - x)^9.
* a(n) = 9*a(n-1) - 36*a(n-2) + 84*a(n-3) - 126*a(n-4) + 126*a(n-5) - 84*a(n-6) + 36*a(n-7) - 9*a(n-8) + a(n-9) for n>9.

Conventions: length P+Q in the name is the array length P + Q; windows are runs of consecutive positions; this reading reproduces the OEIS data.
Offset 1: a(n) is the number of arrays (x_0, ..., x_7) of length 8 with entries in 0..n such that every 4 consecutive entries sum to at most 2 * n.
A brute-force count reproduces the listed terms for small n, and each formula was checked against every listed term (n up to 23).
-/

namespace OMA.S_oeis_a241968

/-- The entry of `x` at position `k` (`0` past the end). -/
def get {n : ℕ} (x : Fin 8 → Fin (n + 1)) (k : ℕ) : ℕ :=
  if h : k < 8 then (x ⟨k, h⟩ : ℕ) else 0

/-- The window condition: every 4 consecutive entries sum to at most 2 * n. -/
def good {n : ℕ} (x : Fin 8 → Fin (n + 1)) : Bool :=
  decide (∀ i < (5 : ℕ), (∑ t ∈ Finset.range 4, get x (i + t)) ≤ 2 * n)

/-- The number of arrays of length 8 with entries in `0..n` satisfying the window condition. -/
def a (n : ℕ) : ℤ :=
  ((Finset.univ : Finset (Fin 8 → Fin (n + 1))).filter (fun x => good x)).card

open PowerSeries in
theorem main :
    (PowerSeries.mk (fun n => if n < 1 then 0 else (a n : ℚ)) * ((1 - X) ^ 9 : PowerSeries ℚ) = X * (97 + 1022 * X + 3086 * X ^ 2 + 2268 * X ^ 3 + 632 * X ^ 4 - 65 * X ^ 5 + 36 * X ^ 6 - 9 * X ^ 7 + X ^ 8)) ∧
    (∀ n : ℕ, 10 ≤ n → (a n : ℚ) = 9 * a (n - 1) - 36 * a (n - 2) + 84 * a (n - 3) - 126 * a (n - 4) + 126 * a (n - 5) - 84 * a (n - 6) + 36 * a (n - 7) - 9 * a (n - 8) + a (n - 9)) := by
  sorry

end OMA.S_oeis_a241968
