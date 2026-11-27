import Mathlib

/-!
# Are there infinitely many Lucas primes?

Source: https://en.wikipedia.org/wiki/Lucas_number#Lucas_primes
Credit: @caa1982

The Lucas numbers are defined by $L_0 = 2$, $L_1 = 1$ and $L_n = L_{n-1} + L_{n-2}$ for $n > 1$,
giving $2, 1, 3, 4, 7, 11, 18, 29, \ldots$ (OEIS A000032). A Lucas prime is a Lucas number that is
prime. It is not known whether there are infinitely many Lucas primes.

The statement below asks for infinitely many prime values $L_n$ (not merely infinitely many indices;
the two are equivalent since $L_n$ is strictly increasing for $n \ge 1$).
-/

namespace OMA.S_wp_are_there_infinitely_many_lucas_primes

/-- The Lucas numbers: $L_0 = 2$, $L_1 = 1$, $L_{n+2} = L_{n+1} + L_n$. -/
def lucas : ℕ → ℕ
  | 0 => 2
  | 1 => 1
  | n + 2 => lucas (n + 1) + lucas n

/-- Conjecture: there are infinitely many Lucas primes. -/
theorem main : {p : ℕ | p.Prime ∧ ∃ n : ℕ, lucas n = p}.Infinite := by
  sorry

end OMA.S_wp_are_there_infinitely_many_lucas_primes
