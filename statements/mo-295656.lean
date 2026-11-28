import Mathlib

/-!
# Positive integers `n` with `n + τ(n) = 2 φ(n)`

Source: https://mathoverflow.net/questions/295656/find-all-positive-integers-n-such-that-ntaun-2-varphin
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Conjecture (asker): the only positive integers `n` with `n + τ(n) = 2 φ(n)` are `n = 1` and
`n = 9`. Here `τ(n)` is the number of divisors of `n` and `φ` is Euler's totient function.
-/

namespace OMA.S_mo_295656

theorem main :
    {n : ℕ | 0 < n ∧ n + n.divisors.card = 2 * Nat.totient n} = {1, 9} := by
  sorry

end OMA.S_mo_295656
