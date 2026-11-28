import Mathlib

/-!
# A261513: Least positive integer k with p(prime(k))+p(prime(k*n)) prime, where p(.) is the partition function given by A000041.

Source: https://oeis.org/A261513
Credit: @divmxnd0x

Conjecture (Zhi-Wei Sun, stated in A261513): Any positive rational number `r` not equal to one can
be written as `m/n`, where `m` and `n` are positive integers with `p(prime(m)) + p(prime(n))` prime.
(This implies that there are infinitely many primes of the form `p(q) + p(r)` with `q` and `r` both
prime; the existence of `a(n)` for `n ≥ 2` is the case `r = n`.)

Formalization notes:
* `p(m)` is the number of partitions of `m`, `Fintype.card (Nat.Partition m)` (A000041);
  `prime(m)` is the `m`-th prime with `prime(1) = 2`, i.e. `Nat.nth Nat.Prime (m - 1)`.
* With this definition `a(2) = a(4) = a(6) = 1`, matching the data of A261513.
-/

namespace OMA.S_oeis_a261513

/-- The partition function `p(m)`. -/
def partitionCount (m : ℕ) : ℕ :=
  Fintype.card (Nat.Partition m)

/-- Sun's conjecture of A261513. -/
theorem main : ∀ r : ℚ, 0 < r → r ≠ 1 → ∃ m n : ℕ, 0 < m ∧ 0 < n ∧ r = (m : ℚ) / n ∧
    (partitionCount (Nat.nth Nat.Prime (m - 1)) + partitionCount (Nat.nth Nat.Prime (n - 1))).Prime := by
  sorry

end OMA.S_oeis_a261513
