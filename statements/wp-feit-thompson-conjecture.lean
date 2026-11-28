import Mathlib

/-!
# Feit–Thompson conjecture

Source: https://en.wikipedia.org/wiki/Feit–Thompson_conjecture
Credit: @joshuadc11

For all distinct prime numbers `p` and `q`, `(p^q - 1) / (p - 1)` does not divide
`(q^p - 1) / (q - 1)`.

Formalization notes:
- For any prime `p`, `p - 1` divides `p ^ q - 1`, so natural number division `(p ^ q - 1) / (p - 1)`
  is exact.
-/

namespace OMA.S_wp_feit_thompson_conjecture

theorem main :
    ∀ p q : ℕ, p.Prime → q.Prime → p ≠ q →
      ¬ ((p ^ q - 1) / (p - 1) ∣ (q ^ p - 1) / (q - 1)) := by
  sorry

end OMA.S_wp_feit_thompson_conjecture
