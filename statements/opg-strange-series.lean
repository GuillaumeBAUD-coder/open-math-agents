import Mathlib

/-!
# The 3n+1 conjecture

Source: https://www.openproblemgarden.org/op/strange_series

Conjecture. Let f(n) = 3n + 1 if n is odd and n/2 if n is even. Let f(1) = 1. Assume we
start with some number n and repeatedly take the f of the current number. Prove that no
matter what the initial number is we eventually reach 1.

(Also called the Collatz conjecture, Ulam conjecture or Syracuse problem.)

Conventions:
* `f` is the map of the page on ℕ, with the special value f(1) = 1 (so 1 is a fixed
  point); n / 2 is exact division since it is only used for even n.
* The initial number ranges over the positive integers n ≥ 1. For n = 0 the map gives
  f(0) = 0 forever, so 0 is not a starting number in the intended sense.
* eventually reach 1: some iterate `f^[k] n` equals 1 (k = 0 allowed, covering n = 1).
-/

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

namespace OMA.S_opg_strange_series

/-- The map of the page: f(1) = 1, f(n) = 3n + 1 for odd n, f(n) = n / 2 for even n. -/
def f (n : ℕ) : ℕ :=
  if n = 1 then 1 else if n % 2 = 1 then 3 * n + 1 else n / 2

theorem main : ∀ n : ℕ, 1 ≤ n → ∃ k : ℕ, f^[k] n = 1 := by
  sorry

end OMA.S_opg_strange_series
