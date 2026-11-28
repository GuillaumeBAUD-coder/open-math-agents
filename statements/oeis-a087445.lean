import Mathlib

/-!
# A087445: Numbers that are congruent to 1 or 5 mod 12.

Source: https://oeis.org/A087445
Credit: @xor2k

Bob Selcoe (Jun 03 2015), in the comments of A087445:
  Conjecture: at least one number in this sequence must appear in all Collatz sequences.
(Later comments of the entry, by Bob Selcoe and by Aidan Simmons, say that the conjecture is true.)
Only this conjecture is formalized; the other remarks of the comment (congruence classes related
to A002450, A072197, A096773, A259663) are not.

Reading of the conjecture: every Collatz sequence contains at least one term of this sequence
(not: one fixed term occurs in every Collatz sequence, which for the term 1 would be the Collatz
conjecture itself; the later comments of the entry argue for the first reading). The Collatz
sequences are the trajectories n, f(n), f(f(n)), ... of all positive integers n, and the starting
value n is a member of its own trajectory (index k = 0), as usual.

Conventions:
* The Collatz map is `m ↦ m/2` (`m` even), `3m + 1` (`m` odd).
* Offset 1: a(1) = 1, a(2) = 5, a(3) = 13, ...; a(n) = 12*floor((n-1)/2) + 1 for odd n and
  12*floor((n-1)/2) + 5 for even n. Only indices n ≥ 1 are used (the value of `a 0` is junk).
* `collatz^[k] n` is the k-th iterate, k ≥ 0, starting values n ≥ 1.

Numerical check: a Python copy of the definition gives 1, 5, 13, 17, 25, 29, 37, 41, 49, 53, 61,
65, 73, 77, 85, 89, 97, 101, 109, 113 for a(1..20), and agrees with the list of m ≡ 1 or 5 mod 12
for the first 2000 terms (the first 20 terms are identical to the DATA field of the entry,
which was compared before filing). Every start n ≤ 200000 reaches a term within 33 steps (35 when the starting
value is not counted).
-/

namespace OMA.S_oeis_a087445

/-- The Collatz map. -/
def collatz (m : ℕ) : ℕ := if m % 2 = 0 then m / 2 else 3 * m + 1

/-- A087445 (offset 1): the numbers congruent to 1 or 5 mod 12, in increasing order. -/
def a (n : ℕ) : ℕ := 12 * ((n - 1) / 2) + (if n % 2 = 1 then 1 else 5)

/-- Every Collatz sequence (trajectory of a positive integer) contains a term of the sequence. -/
theorem main : ∀ n : ℕ, 1 ≤ n → ∃ k : ℕ, ∃ j : ℕ, 1 ≤ j ∧ collatz^[k] n = a j := by
  sorry

end OMA.S_oeis_a087445
