import Mathlib

/-!
# The set of numbers a + b such that m a² + n b² is prime

Source: https://mathoverflow.net/questions/280123
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Conjecture: if `m, n` are coprime there is a natural number `N_{mn}` such that
`{a + b > N_{mn} | a, b ∈ ℕ⁺, m a² + n b² ∈ ℙ_{>2}} = {k > N_{mn} | gcd(k, m + n) = 1}`.
This file states that claim.

Formalized: `m, n` are positive coprime integers (the source's table indexes `m, n ≥ 1`); the
set equality is stated pointwise for every `k > N`.
-/

namespace OMA.S_mo_280123

theorem main :
    ∀ m n : ℕ, 0 < m → 0 < n → Nat.Coprime m n → ∃ N : ℕ, ∀ k : ℕ, N < k →
      ((∃ a b : ℕ, 0 < a ∧ 0 < b ∧ a + b = k ∧ (m * a ^ 2 + n * b ^ 2).Prime ∧
          2 < m * a ^ 2 + n * b ^ 2) ↔ Nat.Coprime k (m + n)) := by
  sorry

end OMA.S_mo_280123
