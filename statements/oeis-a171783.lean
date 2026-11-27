import Mathlib

/-!
# A171783: Third smallest divisor of smallest number having exactly n divisors.

Source: https://oeis.org/A171783
Credit: @ShoQo

Conjecture: "a(n) = 4 for all prime numbers >= 3 and 3 for all composites." (Jianing Song,
Aug 28 2026: "The conjecture is true since the prime factors of each term in A005179 are
consecutive primes starting from 2.")

Formalization notes:
* A005179(n), the smallest number with exactly n divisors, is `sInf {m | #m.divisors = n}`.
  The set is nonempty for n ≥ 1 (2^(n-1) has n divisors), so this is the least element.
* The third smallest divisor of m is `Nat.nth (· ∣ m) 2` (`Nat.nth` counts from 0; for m ≠ 0
  the divisors of m are exactly the k with k ∣ m, and 0 ∤ m).
* Offset 3, as in the entry (data: a(3) = 4, a(4) = 3, a(5) = 4, ...); every n ≥ 3 is either
  prime or composite.
-/

namespace OMA.S_oeis_a171783

/-- A005179: the smallest number with exactly `n` divisors. -/
noncomputable def A005179 (n : ℕ) : ℕ := sInf {m : ℕ | m.divisors.card = n}

/-- The third smallest divisor of A005179(n). -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth (· ∣ A005179 n) 2

theorem main : ∀ n : ℕ, 3 ≤ n → a n = if n.Prime then 4 else 3 := by
  sorry

end OMA.S_oeis_a171783
