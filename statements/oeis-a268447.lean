import Mathlib

/-!
Source: https://oeis.org/A268447
Source text: https://github.com/oeis/oeisdata/blob/main/seq/A268/A268447.seq
Credit: @Heart-galaxy

Mathar's recurrence is recorded as proved by Robert Israel (May 15, 2025).
The sequence is defined by Kotesovec's exact factorial quotient from that date.
The OEIS offset is 8, so both a(n) and a(n-1) are in its domain for n >= 9.
-/

namespace OMA.S_oeis_a268447

def a (n : ℕ) : ℚ :=
  18 * (Nat.factorial (2*n+1) : ℚ) /
    ((Nat.factorial (n-8) : ℚ) * (Nat.factorial (n+10) : ℚ))

theorem main : ∀ n : ℕ, 9 ≤ n →
    -((n:ℚ)+10)*((n:ℚ)-8)*a n + 2*(n:ℚ)*(2*(n:ℚ)+1)*a (n-1) = 0 := by
  sorry

end OMA.S_oeis_a268447
