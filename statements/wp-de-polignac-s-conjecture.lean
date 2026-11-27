import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Set.Finite.Basic

/-!
# De Polignac's conjecture

Source: https://en.wikipedia.org/wiki/De_Polignac's_conjecture

For every positive integer `k`, there are infinitely many pairs of consecutive primes differing
by `2 * k`.
-/

namespace OMA.S_wp_de_polignac_s_conjecture

theorem main : ∀ k : ℕ, 0 < k →
    { p : ℕ | p.Prime ∧ (p + 2 * k).Prime ∧
      ∀ q : ℕ, p < q → q < p + 2 * k → ¬ q.Prime }.Infinite := by
  sorry

end OMA.S_wp_de_polignac_s_conjecture
