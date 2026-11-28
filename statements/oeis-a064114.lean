import Mathlib

/-!
# A064114: Unitary weird numbers: unitary abundant (A034683) but not unitary pseudoperfect (A293188).

Source: https://oeis.org/A064114
Credit: @gblacher2

Conjecture (Amiram Eldar, comment in A064114): "All the terms are divisible by 10 (tested on
the first 10^6 terms)", that is, every unitary weird number is a multiple of 10.

Conventions, following the OEIS entries cited in the name:
* a divisor `d` of `n` is unitary when `gcd(d, n / d) = 1`;
* `n` is unitary abundant (A034683) when `usigma(n) > 2 n`, where `usigma(n)` is the sum of all
  unitary divisors of `n`;
* `n` is unitary pseudoperfect (A293188) when `n` equals the sum of a subset of its aliquot
  (that is, proper: `d < n`) unitary divisors;
* the terms are positive integers.

With these definitions the terms below 14000 are 70, 4030, 5390, 5830, 10430, 10570, 10990,
11410, 11690, 11830, 12110, 12530, 12670, 13370, 13510, 13790, 13930, as in the OEIS data.
-/

namespace OMA.S_oeis_a064114

/-- The unitary divisors of `n`: divisors `d` with `gcd(d, n / d) = 1`. -/
def unitaryDivisors (n : ℕ) : Finset ℕ :=
  n.divisors.filter (fun d => Nat.Coprime d (n / d))

/-- `usigma(n)`, the sum of the unitary divisors of `n`. -/
def usigma (n : ℕ) : ℕ :=
  ∑ d ∈ unitaryDivisors n, d

/-- A034683: `n` is unitary abundant when `usigma(n) > 2 n`. -/
def IsUnitaryAbundant (n : ℕ) : Prop :=
  2 * n < usigma n

/-- A293188: `n` equals the sum of a subset of its aliquot unitary divisors. -/
def IsUnitaryPseudoperfect (n : ℕ) : Prop :=
  ∃ s ⊆ (unitaryDivisors n).filter (· < n), ∑ d ∈ s, d = n

/-- A064114: unitary weird numbers, unitary abundant but not unitary pseudoperfect. -/
def IsUnitaryWeird (n : ℕ) : Prop :=
  0 < n ∧ IsUnitaryAbundant n ∧ ¬ IsUnitaryPseudoperfect n

/-- Eldar's conjecture: every unitary weird number is divisible by 10. -/
theorem main : ∀ n : ℕ, IsUnitaryWeird n → 10 ∣ n := by
  sorry

end OMA.S_oeis_a064114
