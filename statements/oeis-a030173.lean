import Mathlib

/-!
# A030173: Differences p(i)-p(j) between primes, sorted in numerical order.

Source: https://oeis.org/A030173
Credit: @eitanteperman

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.
-/

namespace OMA.S_oeis_a030173


/-- Polignac's conjecture (1849), as recorded in A030173: the set of (positive) differences `p - q`
of two primes `q < p` is the union of the positive even numbers and the numbers `p - 2` with `p` an odd
prime. (The inclusion "⊇ evens" is the open part: every even number is a difference of two primes.) -/
theorem main :
    {d : ℕ | ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ q < p ∧ d = p - q} =
      {d : ℕ | 0 < d ∧ Even d} ∪ {d : ℕ | ∃ p : ℕ, p.Prime ∧ Odd p ∧ d + 2 = p} := by
  sorry

end OMA.S_oeis_a030173
