import Mathlib

/-!
# A235383: the Saha–Karthik conjecture on Pisano periods

Source: https://oeis.org/A235383
Credit: @jagraj28

A235383 lists the Fibonacci numbers that are the product of other Fibonacci numbers (8, 144).
The entry records a conjecture of Saha and Karthik: the only positive integers `k` for which
`A001175(k^2) = A001175(k)` are 6 and 12, where `A001175(k)` is the Pisano period, the period of
the Fibonacci numbers modulo `k`.

`main` states it for `k ≥ 2`. For `k = 1` the equality holds trivially, because `1^2 = 1`; the
source plainly means the integers for which `k^2` is a different modulus, so `k = 1` is set
aside. A check for `2 ≤ k ≤ 600` finds exactly `k = 6` and `k = 12`.

Conventions: the Pisano period `π(k)` is the least `t > 0` with `F(t) ≡ 0` and
`F(t + 1) ≡ 1 (mod k)` (Mathlib's `Nat.fib`, `F(0) = 0`, `F(1) = 1`); this gives
`π(1) = 1`, `π(2) = 3`, `π(3) = 8`, as in A001175.
-/

namespace OMA.S_oeis_a235383

/-- The Pisano period `π(k)`, OEIS A001175: the least `t > 0` such that `F(t) ≡ 0` and
`F(t + 1) ≡ 1` modulo `k`. -/
noncomputable def pisano (k : ℕ) : ℕ :=
  sInf {t : ℕ | 0 < t ∧ Nat.fib t % k = 0 ∧ Nat.fib (t + 1) % k = 1 % k}

/-- The Saha–Karthik conjecture in OEIS A235383. -/
theorem main : ∀ k : ℕ, 2 ≤ k → (pisano (k ^ 2) = pisano k ↔ k = 6 ∨ k = 12) := by
  sorry

end OMA.S_oeis_a235383
