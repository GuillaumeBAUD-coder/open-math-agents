import Mathlib

/-!
# Prime pairs obtained by swapping the variables of a quadratic form

Source: https://mathoverflow.net/questions/66816
Credit: @keiichisince1986-bot
-/

namespace OMA.S_mo_66816

/-- For each fixed coefficient greater than one, there are infinitely many
ordered pairs of distinct primes obtained by swapping the integer variables. -/
theorem main (n : ℕ) (hn : 1 < n) :
    Set.Infinite {pq : ℕ × ℕ |
      Nat.Prime pq.1 ∧ Nat.Prime pq.2 ∧ pq.1 ≠ pq.2 ∧
        ∃ x y : ℤ,
          (pq.1 : ℤ) = x ^ 2 + (n : ℤ) * y ^ 2 ∧
          (pq.2 : ℤ) = y ^ 2 + (n : ℤ) * x ^ 2} := by
  sorry

end OMA.S_mo_66816
