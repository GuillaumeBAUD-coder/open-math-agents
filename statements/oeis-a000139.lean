import Mathlib

/-!
# A000139: a(n) = 2*(3*n)! / ((2*n+1)! * (n+1)!).

Source: https://oeis.org/A000139
Credit: @rabdelaal

OEIS A000139 records the conjecture (Peter Bala, 2025) that `a(n)` is odd iff `n` is a
term of A022341, the odd Fibbinary numbers: odd `k` whose binary expansion has no two
consecutive `1` bits, i.e. `k % 2 = 1` and `k` bitwise-and `k / 2` is `0`.
-/

namespace OMA.S_oeis_a000139

/-- The OEIS A000139 entry `a n = 2*(3*n)! / ((2*n+1)! * (n+1)!)`. -/
def a (n : ℕ) : ℕ :=
  2 * Nat.factorial (3 * n) / (Nat.factorial (2 * n + 1) * Nat.factorial (n + 1))

/-- `k` is an odd Fibbinary number (A022341): odd, with no two adjacent `1` bits. -/
def IsOddFibbinary (k : ℕ) : Prop :=
  k % 2 = 1 ∧ Nat.land k (k / 2) = 0

/-- The conjecture recorded in OEIS A000139: `a n` is odd iff `n` is an odd Fibbinary
number. -/
theorem main : ∀ n : ℕ, a n % 2 = 1 ↔ IsOddFibbinary n := by
  sorry

end OMA.S_oeis_a000139
