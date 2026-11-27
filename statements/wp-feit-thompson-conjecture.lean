import Mathlib

/-!
# Feit–Thompson conjecture

Source: https://en.wikipedia.org/wiki/Feit%E2%80%93Thompson_conjecture
Credit: @ihateSAS

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.

The source: the Feit–Thompson conjecture states that for all distinct prime numbers `p` and `q`,
the number `(p ^ q - 1) / (p - 1)` does not divide `(q ^ p - 1) / (q - 1)`.

So the proposition formalized below is: for distinct primes `p` and `q`, the integer
`(p ^ q - 1) / (p - 1)` never divides `(q ^ p - 1) / (q - 1)`.
-/

namespace OMA.S_wp_feit_thompson_conjecture

-- definitions the statement needs (no sorry, no axiom)

/-- The Feit–Thompson conjecture. -/
theorem main : ∀ p q : ℕ, p.Prime → q.Prime → p ≠ q →
    ¬ ((p ^ q - 1) / (p - 1)) ∣ ((q ^ p - 1) / (q - 1)) := by
  sorry

end OMA.S_wp_feit_thompson_conjecture
