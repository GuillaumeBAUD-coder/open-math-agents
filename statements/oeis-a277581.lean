import Mathlib

/-!
# OEIS A277581: Goldbach with squared prime differences is bounded

Source: https://oeis.org/A277581
Credit: @LordMike

A277581(n) is the "smallest integer >= ((A112823(n) - A234345(n))^2)/n for n >= 2", where
A112823(n) + A234345(n) = 2n are primes p <= q (offset 2). Comment: "Conjecture: 1 <= a(n) <= m for all n,
where m is largest value of a(n), i.e., the sequence of records in a(n) {1, 5, 15, 20, ..., m} is finite."

Reading used here: the sequence is bounded (m exists). a(n) is the minimum of the ceiling over all prime
pairs p <= q with p + q = 2n, so a(n) <= m says some such pair has ceiling <= m; this includes Goldbach
for 2n, as the sequence presupposes. The lower bound 1 <= a(n) is omitted: it fails at primes
("If n is prime, then a(n) = 0") and for composite n it is immediate (p = q would force p = n).
-/

namespace OMA.S_oeis_a277581

theorem main : ∃ m : ℕ, ∀ n ≥ 2, ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = 2 * n ∧ p ≤ q ∧
    ⌈((q - p : ℕ) ^ 2 : ℚ) / n⌉₊ ≤ m := by
  sorry

end OMA.S_oeis_a277581
