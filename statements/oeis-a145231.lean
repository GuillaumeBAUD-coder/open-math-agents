import Mathlib

/-!
# A145231: a(n) = Fibonacci(4^n)

Source: https://oeis.org/A145231
Credit: @niclorusso

Conjecture (in the comments of A145231): each prime divisor can occur only once (i.e., all terms
are squarefree).

Conventions:
* The sequence has offset 0: a(n) = Fibonacci(4^n) for n >= 0, with Fibonacci(m) = `Nat.fib m`
  (Fibonacci(1) = 1, so a(0) = 1).
* Squarefree is Mathlib's `Squarefree` on the natural numbers.
-/

namespace OMA.S_oeis_a145231

/-- The conjecture on A145231: `Fibonacci(4^n)` is squarefree for every `n >= 0`. -/
theorem main : ∀ n : ℕ, Squarefree (Nat.fib (4 ^ n)) := by
  sorry

end OMA.S_oeis_a145231
