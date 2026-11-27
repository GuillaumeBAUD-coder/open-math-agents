import Mathlib

/-!
# A074987: a(n) is the least m not equal to n such that phi(m) = phi(n).

Source: https://oeis.org/A074987
Credit: @gblacher2

The source comment (T. D. Noe): "I conjecture that a(n) <= 2n."
The sequence has offset 1, so `n` ranges over positive integers.

Reading: `a(n)` is the least `m ≠ n` with `φ(m) = φ(n)`, so `a(n) ≤ 2n` holds exactly when some
`m ≠ n` with `φ(m) = φ(n)` satisfies `m ≤ 2n` (in particular such an `m` exists, so `a(n)` is
defined). We state it in that form. Since `φ(n) ≥ 1` for `n ≥ 1` while `φ(0) = 0`, the witness `m`
is automatically positive.
-/

namespace OMA.S_oeis_a074987

theorem main :
    ∀ n : ℕ, 1 ≤ n → ∃ m : ℕ, m ≠ n ∧ Nat.totient m = Nat.totient n ∧ m ≤ 2 * n := by
  sorry

end OMA.S_oeis_a074987
