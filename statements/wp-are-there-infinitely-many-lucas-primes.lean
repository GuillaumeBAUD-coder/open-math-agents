import Mathlib

/-!
# Are there infinitely many Lucas primes?

Source: https://en.wikipedia.org/wiki/Lucas_number
Credit: @ihateSAS

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.

The source: the **Lucas numbers** are defined by `L_0 = 2`, `L_1 = 1` and `L_n = L_{n - 1} + L_{n - 2}`
for `n > 1`; the sequence begins `2, 1, 3, 4, 7, 11, 18, 29, 47, ...`.  A **Lucas prime** is a Lucas
number that is prime.  The open question, from "List of unsolved problems in mathematics", is
whether infinitely many Lucas numbers are prime.

So the proposition formalized below is: the set of indices `n` for which `L_n` is prime is infinite.
-/

namespace OMA.S_wp_are_there_infinitely_many_lucas_primes

-- definitions the statement needs (no sorry, no axiom)

/-- The **Lucas numbers**: `L_0 = 2`, `L_1 = 1`, `L_{n + 2} = L_{n + 1} + L_n`. -/
def lucas : ℕ → ℕ
  | 0 => 2
  | 1 => 1
  | n + 2 => lucas (n + 1) + lucas n

/-- Are there infinitely many Lucas primes? -/
theorem main : {n : ℕ | (lucas n).Prime}.Infinite := by
  sorry

end OMA.S_wp_are_there_infinitely_many_lucas_primes
