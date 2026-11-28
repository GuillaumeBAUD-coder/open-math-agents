import Mathlib

/-!
# A259712: Least positive integer k such that prime(k) + prime(k*n) is a square.

Source: https://oeis.org/A259712
Credit: @divmxnd0x

Conjecture (Zhi-Wei Sun, stated in A259712): every positive rational number `r` can be written as `m/n`, where `m` and `n` are positive integers with `prime(m) + prime(n)` a square. (The existence of `a(n)` for every `n > 0` is
the case `r = n`.)

Formalization notes:
* `prime(m)` is the `m`-th prime with `prime(1) = 2`, i.e. `Nat.nth Nat.Prime (m - 1)`.
* `S` is the set of pairs `(m, n)` of positive integers with m, n > 0 with `prime m + prime n` a square; the conjecture says every
  positive rational is `m/n` for some `(m, n) ∈ S`.
-/

namespace OMA.S_oeis_a259712

/-- The `m`-th prime, `prime 1 = 2`. -/
noncomputable def prime (m : ℕ) : ℕ :=
  Nat.nth Nat.Prime (m - 1)

/-- The pairs `(m, n)` in Sun's conjecture. -/
def Good (m n : ℕ) : Prop := 0 < m ∧ 0 < n ∧ IsSquare (prime m + prime n)

/-- Sun's conjecture: every positive rational is `m/n` with `Good m n`. -/
theorem main : ∀ r : ℚ, 0 < r → ∃ m n : ℕ, Good m n ∧ r = (m : ℚ) / n := by
  sorry

end OMA.S_oeis_a259712
