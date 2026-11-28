import Mathlib

/-!
# A239800: First appearance of n in A016014, or 0 if n never occurs

Source: https://oeis.org/A239800

Conjecture (OEIS A239800):
Let `A016014(m)` be the least positive integer `k` such that `2 * m * k + 1` is prime
(for `m ≥ 1`). Then every positive integer `n` occurs in `A016014`; that is,
`A239800(n) > 0` for all `n ≥ 1`.

Conventions:
- Offset: `1` (`n ≥ 1`).
- First terms of A016014 (`m ≥ 1`): `1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, ...`.
- First terms of A239800 (`n ≥ 1`): `1, 4, 12, 42, 19, 59, 92, 196, 184, 159, ...`.
-/

namespace OMA.S_oeis_a239800

/-- Predicate stating that `k` is the least positive integer such that `2 * m * k + 1`
is prime (OEIS A016014). -/
def IsA016014 (m k : ℕ) : Prop :=
  IsLeast {j : ℕ | 1 ≤ j ∧ Nat.Prime (2 * m * j + 1)} k

/-- Conjecture: every positive integer `n` occurs as `A016014(m)` for some `m ≥ 1`. -/
theorem main :
    ∀ n : ℕ, 1 ≤ n → ∃ m : ℕ, 1 ≤ m ∧ IsA016014 m n := by
  sorry

end OMA.S_oeis_a239800
