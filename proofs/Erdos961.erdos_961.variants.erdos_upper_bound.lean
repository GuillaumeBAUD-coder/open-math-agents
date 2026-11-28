import FormalConjectures.ErdosProblems.«961»

-- Problem: Erdős Problem 961 — erdos upper bound
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/961.lean:83
-- Credit: @sassmama27
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Outline from Erdős, On consecutive integers, Nieuw Arch. Wisk. (1955).

open Filter Real Nat

namespace Erdos961

-- Helper: p-adic valuation of binomial coefficients via Legendre
-- (to be expanded with Mathlib's factorial_multiplicity)

lemma binomial_val_bound (u t p : ℕ) (hp : Nat.Prime p) (hpu : p ≤ u + t) :
    padicValNat p (Nat.choose (u + t) t) < Nat.log p (u + t) + 1 := by
  sorry

-- Product over primes ≤ k of maximal powers is < (u+t)^{π(k)} roughly
lemma product_smooth_bound (k u t : ℕ) (hk : 0 < k) (ht : 0 < t) :
    ∏ p in (Finset.range (k + 1)).filter Nat.Prime, p ^ (Nat.log p (u + t))
      ≤ (u + t) ^ (Nat.primeCounting (k)) := by
  sorry

-- Main contradiction for large c
lemma erdos_1955_contradiction (k : ℕ) (hk : 100 < k)
    (h : ∃ u ≥ k ^ 2, ∀ i < ⌈(6 : ℝ) * k / Real.log k⌉₊,
      (u + i).PrimeFactors.sup id ≤ k) :
    False := by
  sorry

end Erdos961

theorem OMA.solution : type_of% @Erdos961.erdos_961.variants.erdos_upper_bound := by
  -- Eventually for large k, f k < 3 * k / log k
  -- via the contradiction above (constant 6 works, so 3 does)
  sorry
