import Mathlib

/-!
# OEIS A185657: Numbers n such that (n^2 + n + 41) / 43 is prime.

Source: https://oeis.org/A185657
Credit: @unserus

OEIS (R. Israel): "All terms == 1 or 41 (mod 43). Bunyakovsky's conjecture implies there are
infinitely many terms in both these classes." (Another comment: "It's highly probable that a(n)
is infinite.")
The open statement is that both residue classes contain infinitely many terms (which implies
the sequence is infinite). "(n^2 + n + 41) / 43 is prime" is read as exact division:
`n^2 + n + 41 = 43 * p` with `p` prime (first term `41`: `41^2 + 41 + 41 = 43 * 41`).
-/

namespace OMA.S_oeis_a185657

/-- The terms of A185657: `n` such that `(n^2 + n + 41) / 43` is a prime. -/
def a185657Set : Set ℕ := {n : ℕ | ∃ p : ℕ, p.Prime ∧ n ^ 2 + n + 41 = 43 * p}

/-- Infinitely many terms are `≡ 1 (mod 43)` and infinitely many are `≡ 41 (mod 43)`. -/
theorem main :
    {n : ℕ | n ∈ a185657Set ∧ n % 43 = 1}.Infinite ∧
      {n : ℕ | n ∈ a185657Set ∧ n % 43 = 41}.Infinite := by
  sorry

end OMA.S_oeis_a185657
