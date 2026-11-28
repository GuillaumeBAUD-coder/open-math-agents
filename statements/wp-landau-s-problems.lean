import Mathlib

/-!
# Landau's problems

Source: https://en.wikipedia.org/wiki/Landau's_problems
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Source statement: at the 1912 ICM, Landau listed four basic problems about prime numbers:
1. Goldbach's conjecture: can every even integer greater than 2 be written as the sum of two
   primes?
2. Twin prime conjecture: are there infinitely many primes `p` such that `p + 2` is prime?
3. Legendre's conjecture: does there always exist at least one prime between consecutive
   perfect squares?
4. Are there infinitely many primes `p` such that `p - 1` is a perfect square, i.e. infinitely
   many primes of the form `n ^ 2 + 1`?
The source says all four are unresolved (as of 2026).

`main` is the conjunction of the four conjectured (affirmative) answers, in the source's order.

Conventions:
* integers in (1) are natural numbers `n` with `2 < n` and `Even n`; the two primes need not be
  distinct;
* in (3) the consecutive squares are `n ^ 2` and `(n + 1) ^ 2` for `n ≥ 1` (for `n = 0` there is
  no integer strictly between `0` and `1`), and between means strictly between;
* in (4) `p - 1` a perfect square is written `p = n ^ 2 + 1` for some `n : ℕ`, avoiding natural
  subtraction;
* infinitely many is `Set.Infinite`.
-/

namespace OMA.S_wp_landau_s_problems

theorem main :
    (∀ n : ℕ, 2 < n → Even n → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n = p + q) ∧
    {p : ℕ | p.Prime ∧ (p + 2).Prime}.Infinite ∧
    (∀ n : ℕ, 1 ≤ n → ∃ p : ℕ, p.Prime ∧ n ^ 2 < p ∧ p < (n + 1) ^ 2) ∧
    {p : ℕ | p.Prime ∧ ∃ n : ℕ, p = n ^ 2 + 1}.Infinite := by
  sorry

end OMA.S_wp_landau_s_problems
