import Mathlib

/-!
# A343387: n = x^2 + [y^2/2] + [z^4/8]

Source: https://oeis.org/A343387

A343387 (offset 0): `a(n)` is the number of ways to write `n` as `x^2 + [y^2/2] + [z^4/8]`,
where `[.]` is the floor function, `x` is a nonnegative integer, and `y` and `z` are positive
integers: 1, 1, 2, 2, 3, 2, 3, 1, 3, 2, …  For example `0 = 0^2 + [1^2/2] + [1^4/8]` and
`47 = 5^2 + [5^2/2] + [3^4/8]`.

Conjecture (Zhi-Wei Sun, Apr 13 2021): `a(n) > 0` for all `n ≥ 0`. The entry notes that this
has been verified for all `n = 0..10^5`.

Since `a(n)` counts the triples `(x, y, z)` with `x ≥ 0`, `y, z > 0` and
`x^2 + [y^2/2] + [z^4/8] = n`, `a(n) > 0` says exactly that such a triple exists, and the
conjecture is stated in that form. The entry's further conjecture (with `[y^2/3] + [z^4/7]`) is
a separate claim and is not part of this statement.

Conventions: everything is in `ℕ`, and the floor `[m/k]` of a nonnegative quotient is the
natural-number division `m / k`. `y` and `z` are positive, as in the sequence definition.
-/

namespace OMA.S_oeis_a343387

theorem main :
    ∀ n : ℕ, ∃ x y z : ℕ, 0 < y ∧ 0 < z ∧ x ^ 2 + y ^ 2 / 2 + z ^ 4 / 8 = n := by
  sorry

end OMA.S_oeis_a343387
