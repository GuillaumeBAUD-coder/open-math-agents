import Mathlib

/-!
# A238516: primes (p(k)+1) p(n) + 1 with p the partition function (Sun's conjectures)

Source: https://oeis.org/A238516 (OEIS Foundation, CC BY-SA 4.0)
Credit: @trador01 (agent: Claude Code, model claude-opus-5-5)

A238516 (offset 1): a(n) = |{0 < k < n: (p(k)+1)*p(n) + 1 is prime}|, where p(.) is the partition
function (A000041); data 0, 1, 1, 1, 2, 3, 3, 3, 4, 5, ...
(a(4) = 1 since (p(1)+1)*p(4) + 1 = 2*5 + 1 = 11 is prime.)

The entry records (Zhi-Wei Sun):

  Conjecture: (i) a(n) > 0 for all n > 1. Also, for any integer n > 4 there is a positive
  integer k < n with (p(k)-1)*p(n) - 1 prime.
  (ii) Let q(.) be the strict partition function (A000009). If n > 5, then p(n)*q(k) + 1 is
  prime for some 3 < k < n. If n > 6, then p(n)*q(k) - 1 is prime for some 0 < k < n. If n > 1,
  then q(n)*q(k) + 1 is prime for some 0 < k < n. If n > 3, then q(n)*q(k) - 1 is prime for
  some 0 < k < n.

All six claims are stated here, as a conjunction.

Reading of the source:
* `p n` is the number of partitions of `n` (`Fintype.card (Nat.Partition n)`), and `q n` the
  number of partitions of `n` into distinct parts.
* `a(n) > 0` is the existence of `k` with `0 < k < n` and `(p(k)+1) p(n) + 1` prime.
* `(p(k) - 1) p(n) - 1` is negative when `p(k) = 1` (k = 1), and a negative number is not prime;
  so that claim is stated with `2 ≤ p k`, where the value is a natural number and the natural
  subtraction is exact. In the other claims all values are at least 1, so `p(n) q(k) - 1` and
  `q(n) q(k) - 1` are exact natural-number differences.
-/

namespace OMA.S_oeis_a238516

/-- The partition function `p(n)` (A000041). -/
def p (n : ℕ) : ℕ := Fintype.card (Nat.Partition n)

/-- The strict partition function `q(n)` (A000009): partitions of `n` into distinct parts. -/
def q (n : ℕ) : ℕ := (Finset.univ.filter (fun π : Nat.Partition n => π.parts.Nodup)).card

/-- Sun's conjectures (i) and (ii). -/
theorem main :
    (∀ n : ℕ, 1 < n → ∃ k, 0 < k ∧ k < n ∧ ((p k + 1) * p n + 1).Prime) ∧
    (∀ n : ℕ, 4 < n → ∃ k, 0 < k ∧ k < n ∧ 2 ≤ p k ∧ ((p k - 1) * p n - 1).Prime) ∧
    (∀ n : ℕ, 5 < n → ∃ k, 3 < k ∧ k < n ∧ (p n * q k + 1).Prime) ∧
    (∀ n : ℕ, 6 < n → ∃ k, 0 < k ∧ k < n ∧ (p n * q k - 1).Prime) ∧
    (∀ n : ℕ, 1 < n → ∃ k, 0 < k ∧ k < n ∧ (q n * q k + 1).Prime) ∧
    (∀ n : ℕ, 3 < n → ∃ k, 0 < k ∧ k < n ∧ (q n * q k - 1).Prime) := by
  sorry

end OMA.S_oeis_a238516
