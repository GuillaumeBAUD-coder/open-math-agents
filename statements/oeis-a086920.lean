import Mathlib

/-!
# A086920: a prime obtained by repeating `k` `n` times and appending a 1

Source: https://oeis.org/A086920
Credit: @R-Dson

`a(n)` is the smallest `k` such that `n` times the concatenation of `k` with itself, followed by
a `1`, is a prime, or `0` if no such number exists. Conjecture: no term is zero.

Conventions.
- `repeated k n` is the number whose decimal representation is that of `k`, written `n` times:
  with `d` the number of decimal digits of `k`, it is `k * (1 + 10 ^ d + ... + 10 ^ (d * (n - 1)))`.
- `followedByOne k n` is that number with a final digit `1` appended: `10 * repeated k n + 1`.
- `a(n)` is the infimum in `ℕ` of the set of positive such `k`, so it is `0` exactly when the set
  is empty.
- The offset of the entry is `1`.
- Examples of the entry: `a(3) = 2` as `2221` is a prime; `a(4) = 3` as `33331` is a prime but
  `11111` and `22221` are not; `a(8) = 30` and the prime arising is `30303030303030301`.
-/

namespace OMA.S_oeis_a086920

/-- The number whose decimal representation is that of `k`, written `n` times. -/
def repeated (k n : ℕ) : ℕ := k * ∑ i ∈ Finset.range n, 10 ^ ((Nat.digits 10 k).length * i)

/-- That number with a final digit `1` appended. -/
def followedByOne (k n : ℕ) : ℕ := 10 * repeated k n + 1

/-- Smallest `k` such that `followedByOne k n` is a prime, or `0`. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {k : ℕ | 0 < k ∧ (followedByOne k n).Prime}

theorem main : ∀ n : ℕ, 0 < n → 0 < a n := by
  sorry

end OMA.S_oeis_a086920
