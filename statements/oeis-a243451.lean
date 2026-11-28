import Mathlib

/-!
# A243451: Primes of the form n^2 + 16

Source: https://oeis.org/A243451
Credit: @gblacher2

The entry lists the primes `p` such that `p = n ^ 2 + 16` for some natural number `n`, and records
the conjecture (Reinhard Zumkeller, 2015) that the sequence is infinite.
-/

namespace OMA.S_oeis_a243451

/-- There are infinitely many primes of the form `n ^ 2 + 16`. -/
theorem main : {p : ℕ | p.Prime ∧ ∃ n : ℕ, p = n ^ 2 + 16}.Infinite := by
  sorry

end OMA.S_oeis_a243451
