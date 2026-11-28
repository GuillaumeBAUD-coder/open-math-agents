import Mathlib

/-!
# A004001: two conjectures on the Hofstadter–Conway $10000 sequence

Source: https://oeis.org/A004001
Credit: @jagraj28

A004001 is the sequence with `a(1) = a(2) = 1` and `a(n) = a(a(n-1)) + a(n - a(n-1))` for
`n ≥ 3`. The entry records two conjectures (Daniel Forgues, 2019):
1. `a(n) = n/2` if and only if `n = 2^k` with `k ≥ 1`;
2. `a(n) = 2^(k-1)` for `n = 2^k - (k-1)` to `2^k`, for every `k ≥ 1`.

`main` states both for every function `a : ℕ → ℕ` that satisfies the defining recurrence on
`n ≥ 1`. The recurrence determines `a(n)` for every `n ≥ 1` (by induction, using
`1 ≤ a(n-1) ≤ n - 1`), so this is the same as stating them for A004001 itself; `a 0` is not part
of the sequence and is left free.

Conventions: the sequence is indexed from `n = 1`, so conjecture 1 is stated for `n ≥ 1`.
`a(n) = n/2` is written `2 * a(n) = n`, which is the same equation and avoids division.
-/

namespace OMA.S_oeis_a004001

/-- `a` satisfies the defining recurrence of OEIS A004001 on `n ≥ 1`. -/
def IsHofstadterConway (a : ℕ → ℕ) : Prop :=
  a 1 = 1 ∧ a 2 = 1 ∧ ∀ n, 3 ≤ n → a n = a (a (n - 1)) + a (n - a (n - 1))

/-- Conjectures 1 and 2 of OEIS A004001 (Forgues). -/
theorem main : ∀ a : ℕ → ℕ, IsHofstadterConway a →
    (∀ n, 1 ≤ n → (2 * a n = n ↔ ∃ k, 1 ≤ k ∧ n = 2 ^ k)) ∧
    (∀ k, 1 ≤ k → ∀ n, 2 ^ k - (k - 1) ≤ n → n ≤ 2 ^ k → a n = 2 ^ (k - 1)) := by
  sorry

end OMA.S_oeis_a004001
