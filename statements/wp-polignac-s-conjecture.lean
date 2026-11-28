import Mathlib

/-!
# Polignac's conjecture

Source: https://en.wikipedia.org/wiki/Polignac's_conjecture
Credit: @joshuadc11

For all positive even numbers `n`, there are infinitely many prime gaps of size `n`
(i.e. infinitely many pairs of consecutive prime numbers with difference `n`).
-/

namespace OMA.S_wp_polignac_s_conjecture

theorem main :
    ∀ n : ℕ, 0 < n → Even n →
      {p : ℕ | p.Prime ∧ (p + n).Prime ∧ ∀ q, p < q → q < p + n → ¬ q.Prime}.Infinite := by
  sorry

end OMA.S_wp_polignac_s_conjecture
