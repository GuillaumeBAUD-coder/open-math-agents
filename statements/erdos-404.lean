import Mathlib

/-!
# Erdős Problem 404

Source: https://www.erdosproblems.com/404
Credit: @SudharsanAnimations

For which integers `a ≥ 1` and primes `p` is there a finite upper bound on those `k` such that
there are `a = a_1 < ⋯ < a_n` with `p^k ∣ a_1! + ⋯ + a_n!`? If `f(a, p)` is the greatest such `k`,
how does `f(a, p)` behave?

Is there a prime `p` and an infinite sequence `a_1 < a_2 < ⋯` such that, if `p^{m_k}` is the
highest power of `p` dividing `∑_{i ≤ k} a_i!`, then `m_k → ∞`?

We formalize the second question, in its affirmative form: such a prime and sequence exist.
The problem is open; a disproof is the negation of `main`. (The first question asks for a
classification and a growth rate, and is not formalized here.)

Conventions:
- The sequence is indexed from `0`: `a 0 < a 1 < ⋯`, and `m_k` is the `p`-adic valuation of
  `∑_{i ≤ k} (a i)!`, i.e. of `∑ i ∈ Finset.range (k + 1), (a i)!`. Shifting the index does not
  change whether `m_k → ∞`.
- The terms are positive integers, as in the first question (`a ≥ 1`). Every partial sum is
  then positive, so its `p`-adic valuation is the exponent of the highest power of `p` dividing it.
- `m_k → ∞` means `Tendsto m atTop atTop`.
-/

namespace OMA.S_erdos_404

open Filter

/-- Erdős Problem 404, second question, affirmative form. -/
theorem main : ∃ p : ℕ, p.Prime ∧ ∃ a : ℕ → ℕ, StrictMono a ∧ 0 < a 0 ∧
    Tendsto (fun k : ℕ => padicValNat p (∑ i ∈ Finset.range (k + 1), (a i).factorial))
      atTop atTop := by
  sorry

end OMA.S_erdos_404
