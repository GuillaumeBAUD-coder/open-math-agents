import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Set.Finite.Basic

/-!
# Primes whose cube minus one has eight positive divisors

OEIS A341659, contributed by Jon E. Schoenfield, conjectures that infinitely
many primes have this property. Source: https://oeis.org/A341659
(OEIS Foundation, CC BY-SA 4.0). Formalization: @ZedingZhang.
-/

namespace OMA.S_oeis_a341659

theorem main : Set.Infinite {p : ℕ | p.Prime ∧ (p ^ 3 - 1).divisors.card = 8} := by
  sorry

end OMA.S_oeis_a341659
