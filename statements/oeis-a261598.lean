import Mathlib

/-!
# Zero digits in sexagesimal Fibonacci numbers

Source: https://oeis.org/A261598
The sequence starts with the Fibonacci number F₀ = 0.
-/

namespace OMA.S_oeis_a261598

/-- The product of the base-60 digits of the nth Fibonacci number. -/
def digitProduct (n : ℕ) : ℕ :=
  let value := Nat.fib n
  if value = 0 then 0 else (Nat.digits 60 value).prod

theorem main : ∀ n : ℕ, 3329 < n → digitProduct n = 0 := by
  sorry

end OMA.S_oeis_a261598
