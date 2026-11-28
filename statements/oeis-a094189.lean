import Mathlib

/-!
# A094189: Number of primes between n^2-n and n^2 (inclusive)

Source: https://oeis.org/A094189
Credit: @gblacher2

`a(n)` (offset 1) is the number of primes `p` with `n^2 - n ≤ p ≤ n^2`. The entry records two
conjectures:
1. for `n > 11`, `a(n) > 1`;
2. (Oppermann, 1882) for `n > 1`, `a(n) > 0`.

`main` is the conjunction of the two. For `n ≥ 1` the natural-number subtraction `n ^ 2 - n` is
exact, and both conjectures only concern `n > 1`.
-/

namespace OMA.S_oeis_a094189

/-- `a n`: the number of primes in the closed interval `[n^2 - n, n^2]` (OEIS A094189). -/
def a (n : ℕ) : ℕ := ((Finset.Icc (n ^ 2 - n) (n ^ 2)).filter Nat.Prime).card

/-- The two conjectures of OEIS A094189: `a(n) > 1` for `n > 11`, and `a(n) > 0` for `n > 1`. -/
theorem main : (∀ n : ℕ, 11 < n → 1 < a n) ∧ (∀ n : ℕ, 1 < n → 0 < a n) := by
  sorry

end OMA.S_oeis_a094189
