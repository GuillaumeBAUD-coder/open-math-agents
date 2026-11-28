import Mathlib

/-!
# A101208: Smallest odd prime p such that n = (p - 1) / ord_p(2).

Source: https://oeis.org/A101208
Credit: @mscheuern

Conjecture (OEIS A101208, comments): `a(n)` is defined for all `n`, i.e. for every `n ≥ 1`
there is an odd prime `p` whose index `(p - 1) / ord_p(2)` (the index of the subgroup generated
by `2` in `(ℤ/pℤ)ˣ`) equals `n`. The sequence begins `a(1) = 3`, `a(2) = 7`, `a(3) = 43`,
`a(4) = 113`, `a(5) = 251`, `a(6) = 31`.

Formalization notes:
* `ord_p(2)` is `orderOf (2 : ZMod p)`, the multiplicative order of `2` modulo `p`. For an odd
  prime `p` the element `2` is a unit of `ZMod p`, so this order is positive and divides
  `p - 1` (Fermat). Hence `(p - 1) / ord_p(2) = n` holds exactly when
  `p - 1 = n * ord_p(2)`, and the statement uses this division-free form.
* "Odd prime" is `p.Prime ∧ p ≠ 2`: for `p = 2`, `2 = 0` in `ZMod 2` and has order `0`.
* `n` ranges over the offset of the sequence, `n ≥ 1`. The statement asserts only that `a(n)`
  exists; it does not compute it.
* Examples: `p = 3` has `ord_3(2) = 2`, index `1`; `p = 7` has `ord_7(2) = 3`, index `2`;
  `p = 43` has `ord_43(2) = 14`, index `3`.
-/

namespace OMA.S_oeis_a101208

/-- For every `n ≥ 1` there is an odd prime `p` with `p - 1 = n * ord_p(2)`. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p - 1 = n * orderOf (2 : ZMod p) := by
  sorry

end OMA.S_oeis_a101208
