import Mathlib

/-!
# OEIS A236389: a(n) > 0 for all n > 56

Source: https://oeis.org/A236389
Credit: @LordMike

a(n) = |{0 < k < n: m = phi(k)/2 + phi(n-k)/12 is an integer with 2^m*p(m) + 1 prime}|,
where p(.) is the partition function (A000041).
Conjecture: a(n) > 0 for all n > 56.

Reading used here: a(n) > 0 means some k with 0 < k < n has m = phi(k)/2 + phi(n-k)/12 equal to a
natural number (checked in ℚ, so no truncating division), with 2^m * p(m) + 1 prime, where p(m) is
the number of partitions of m (`Nat.Partition m`).
-/

namespace OMA.S_oeis_a236389

theorem main : ∀ n : ℕ, 56 < n → ∃ k ∈ Finset.Ioo 0 n, ∃ m : ℕ,
    (m : ℚ) = (Nat.totient k : ℚ) / 2 + (Nat.totient (n - k) : ℚ) / 12 ∧
    (2 ^ m * Fintype.card (Nat.Partition m) + 1).Prime := by
  sorry

end OMA.S_oeis_a236389
