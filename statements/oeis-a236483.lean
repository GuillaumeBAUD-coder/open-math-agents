import Mathlib

/-!
# A236483: a(n) = |{0 < k < n-2: p(k) + 2^(phi(n-k)/2) is prime}|

Source: https://oeis.org/A236483
Credit: @LordMike

a(n) = |{0 < k < n-2: p(k) + 2^(phi(n-k)/2) is prime}|, where p(.) is the partition function (A000041) and phi(.) is Euler's totient function.
Conjecture: (i) a(n) > 0 for all n > 3.

Reading used here: offset 1, so n ranges over positive integers; k runs over 1..n-3 (`Finset.Ioo 0 (n - 2)`,
empty for n ≤ 3 even with truncated subtraction). For k < n-2, n-k ≥ 3 so phi(n-k) is even and the natural
division by 2 is exact. Only part (i) of the conjecture is stated (parts (ii), (iii) are separate claims).
-/

namespace OMA.S_oeis_a236483

/-- A236483 (offset 1). -/
def a (n : ℕ) : ℕ :=
  ((Finset.Ioo 0 (n - 2)).filter fun k =>
    (Fintype.card (Nat.Partition k) + 2 ^ (Nat.totient (n - k) / 2)).Prime).card

theorem main : ∀ n > 3, 0 < a n := by
  sorry

end OMA.S_oeis_a236483
