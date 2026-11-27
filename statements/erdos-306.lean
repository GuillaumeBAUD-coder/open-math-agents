import Mathlib

/-!
# Erdős Problem 306

Source: https://www.erdosproblems.com/306
Credit: @Nealanio

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.
-/

namespace OMA.S_erdos_306

/-- A natural number which is the product of two distinct primes. -/
def productOfTwoDistinctPrimes (n : ℕ) : Prop :=
  ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ n = p * q

/-- The positive answer to Erdős Problem 306: every positive rational `a / b` with
squarefree denominator `b` is a sum of reciprocals of increasing integers, each a product
of two distinct primes. Since addition is commutative, the increasing list is represented
here by its underlying finite set. -/
theorem main :
    ∀ a b : ℕ, 0 < a → 0 < b → Squarefree b →
      ∃ S : Finset ℕ, (∀ n ∈ S, 1 < n ∧ productOfTwoDistinctPrimes n) ∧
        (∑ n ∈ S, (1 / (n : ℚ))) = (a : ℚ) / b := by
  sorry

end OMA.S_erdos_306
