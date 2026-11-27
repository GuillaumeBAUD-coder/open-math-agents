import Mathlib

/-!
# A005117: Squarefree numbers: numbers that are not divisible by a square greater than 1.

Source: https://oeis.org/A005117
Credit: @diegopluna

Conjecture (Zhi-Wei Sun, Mar 26 2013). For each n = 2, 3, ... there are infinitely many integers
b > a(n) such that Sum_{k=1..n} a(k) * b^(k-1) is prime, and the smallest such an integer b does
not exceed (n+3)*(n+4).

Reading of the source:
* `a n` is the n-th squarefree number with the entry's offset 1, so a(1) = 1, a(2) = 2,
  a(3) = 3, a(4) = 5, ...; it is `Nat.nth Squarefree (n - 1)`.
* b ranges over integers b > a(n) >= 1, hence over positive integers, so natural numbers are used.
* "The smallest such b does not exceed (n+3)(n+4)" is stated as: some b with a(n) < b and
  b <= (n+3)(n+4) makes the sum prime. Given the first part (the set of such b is infinite, so it
  has a least element), this is equivalent to its least element being at most (n+3)(n+4).
* The entry's other "it appears" comment (Bouayoun, Detlefs: a characterization through products
  of primes modulo j) is followed in the entry by Antti Karttunen's argument that it holds, and
  the site lists only Sun's conjecture for this entry, so only Sun's conjecture is stated here.
-/

namespace OMA.S_oeis_a005117

/-- A005117(n): the n-th squarefree number, offset 1 (a(1) = 1). -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth Squarefree (n - 1)

/-- Sum_{k=1..n} a(k) * b^(k-1). -/
noncomputable def poly (n b : ℕ) : ℕ := ∑ k ∈ Finset.Icc 1 n, a k * b ^ (k - 1)

theorem main :
    ∀ n : ℕ, 2 ≤ n →
      {b : ℕ | a n < b ∧ (poly n b).Prime}.Infinite ∧
      ∃ b : ℕ, a n < b ∧ b ≤ (n + 3) * (n + 4) ∧ (poly n b).Prime := by
  sorry

end OMA.S_oeis_a005117
