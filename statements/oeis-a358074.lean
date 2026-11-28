import Mathlib

/-!
# A358074: a(n) is the number of distinct ways n can be written as the sum of a perfect square and factorial.

Source: https://oeis.org/A358074
Credit: @ceejcake

Conjecture (Robert Israel, OEIS A358074, Nov 10 2026): `a(n) ≤ 3` for all `n`.

Formalization notes:
* The sequence has offset `1`, so the conjecture is stated for `n ≥ 1`
  (with the definition below one also has `a 0 = 0`, since `k! ≥ 1`).
* Following the OEIS comment, `x ^ 2` and `(-x) ^ 2` are not counted separately, and `0!` and `1!`
  are not counted separately. So `a n` counts pairs `(x, k)` of natural numbers with `k ≥ 1` and
  `x ^ 2 + k ! = n`: the base `x` of the square is taken nonnegative, and the factorial `1 = 0! = 1!`
  is represented only by `k = 1`. Distinct pairs give distinct ways, since `k ↦ k !` is injective
  on `k ≥ 1`.
* The search bounds are lossless: any solution has `x ^ 2 ≤ n`, hence `x ≤ n.sqrt`, and
  `k ≤ k ! ≤ n` (`Nat.self_le_factorial`).
* Initial values for `n = 1, ..., 20`:
  `a(n) = 1, 2, 1, 0, 1, 2, 1, 0, 0, 2, 1, 0, 0, 0, 1, 0, 1, 1, 0, 0`.
  For example `2 = 0 ^ 2 + 2! = 1 ^ 2 + 1!`, so `a 2 = 2`, and `a 145 = 3`
  (`145 = 12 ^ 2 + 1! = 11 ^ 2 + 4! = 5 ^ 2 + 5!`).
-/

namespace OMA.S_oeis_a358074

/-- `a n` is the number of pairs `(x, k)` of natural numbers with `k ≥ 1` and `x ^ 2 + k ! = n`,
i.e. the number of ways to write `n` as a perfect square plus a factorial, counting `x ^ 2` and
`(-x) ^ 2` once and `0!`, `1!` once. -/
def a (n : ℕ) : ℕ :=
  ((Finset.range (n.sqrt + 1) ×ˢ Finset.Icc 1 n).filter
    fun p => p.1 ^ 2 + p.2.factorial = n).card

/-- OEIS A358074 conjecture (Robert Israel): `a n ≤ 3` for every `n ≥ 1`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → a n ≤ 3 := by
  sorry

end OMA.S_oeis_a358074
