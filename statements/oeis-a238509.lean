import Mathlib

/-!
# A238509: primes p(n) + p(k) - 1 with p the partition function (Sun's conjectures)

Source: https://oeis.org/A238509 (OEIS Foundation, CC BY-SA 4.0)
Credit: @trador01 (agent: Claude Code, model claude-opus-5-5)

A238509 (offset 1): a(n) = |{0 < k < n: p(n) + p(k) - 1 is prime}|, where p(.) is the partition
function (A000041); data 0, 1, 1, 2, 2, 3, 2, 1, 1, 2, 1, ...
(a(11) = 1 since p(11) + p(10) - 1 = 56 + 42 - 1 = 97 is prime.)

The entry records (Zhi-Wei Sun):

  Conjecture: (i) a(n) > 0 for all n > 1. Also, if n > 2 is different from 8 and 25, then
  p(n) + p(k) + 1 is prime for some 0 < k < n.
  (ii) If n > 7, then n + p(k) is prime for some 0 < k < n.
  (iii) If n > 1, then p(k) + q(n) is prime for some 0 < k < n, where q(.) is the strict
  partition function given by A000009. If n > 2, then p(k) + q(n) - 1 is prime for some
  0 < k < n. If n > 1 is not equal to 8, then p(k) + q(n) + 1 is prime for some 0 < k < n.

All six claims are stated here, as a conjunction.

Reading of the source:
* `p n` is the number of partitions of `n` (`Fintype.card (Nat.Partition n)`), and `q n` the
  number of partitions of `n` into distinct parts (those whose parts have no repetition).
* `a(n) > 0` is the existence of `k` with `0 < k < n` and `p(n) + p(k) - 1` prime.
* All values involved are at least 1, so the subtractions `- 1` are exact in `ℕ`.
-/

namespace OMA.S_oeis_a238509

/-- The partition function `p(n)` (A000041). -/
def p (n : ℕ) : ℕ := Fintype.card (Nat.Partition n)

/-- The strict partition function `q(n)` (A000009): partitions of `n` into distinct parts. -/
def q (n : ℕ) : ℕ := (Finset.univ.filter (fun π : Nat.Partition n => π.parts.Nodup)).card

/-- Sun's conjectures (i), (ii), (iii). -/
theorem main :
    (∀ n : ℕ, 1 < n → ∃ k, 0 < k ∧ k < n ∧ (p n + p k - 1).Prime) ∧
    (∀ n : ℕ, 2 < n → n ≠ 8 → n ≠ 25 → ∃ k, 0 < k ∧ k < n ∧ (p n + p k + 1).Prime) ∧
    (∀ n : ℕ, 7 < n → ∃ k, 0 < k ∧ k < n ∧ (n + p k).Prime) ∧
    (∀ n : ℕ, 1 < n → ∃ k, 0 < k ∧ k < n ∧ (p k + q n).Prime) ∧
    (∀ n : ℕ, 2 < n → ∃ k, 0 < k ∧ k < n ∧ (p k + q n - 1).Prime) ∧
    (∀ n : ℕ, 1 < n → n ≠ 8 → ∃ k, 0 < k ∧ k < n ∧ (p k + q n + 1).Prime) := by
  sorry

end OMA.S_oeis_a238509
