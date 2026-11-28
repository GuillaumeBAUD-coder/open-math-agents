import Mathlib

/-!
# A145231: a(n) = Fibonacci(4^n).

Source: https://oeis.org/A145231
Credit: @divmxnd0x

Conjecture (Artur Jasinski, Oct 05 2008, stated in A145231): each prime divisor can occur only
once, i.e. all terms are squarefree.

Formalization notes:
* `a n = Nat.fib (4^n)` (offset 0: `a 0, a 1, ... = 1, 3, 987, 10610209857723, ...`).
-/

namespace OMA.S_oeis_a145231

/-- Jasinski's conjecture: `Fibonacci(4^n)` is squarefree for every `n ≥ 0`. -/
theorem main : ∀ n : ℕ, Squarefree (Nat.fib (4 ^ n)) := by
  sorry

end OMA.S_oeis_a145231
