import Mathlib

/-!
# OEIS A305080: connected strict partitions with indivisible squarefree parts

Source: https://oeis.org/A305080
Credit: @LordMike

A305080: Number of connected strict integer partitions of n with pairwise indivisible and squarefree parts.
Conjecture: This sequence is "eventually increasing," meaning that for all k >= 0 there exists an m >= 0
such that a(n) > k for all n > m.

Reading used here: a(n) counts finite sets S of positive integers with sum n, all squarefree, no part dividing
another, and the graph on S (edge iff gcd > 1) connected. This reproduces the OEIS data (a(1) = 1 from {1},
a(21) = 2 from {21} and {6,15}).
-/

namespace OMA.S_oeis_a305080

/-- `a n`: number of such partitions of `n` (strict partitions as finite sets). -/
noncomputable def a (n : ℕ) : ℕ := Set.ncard {S : Finset ℕ | S.sum id = n ∧ (∀ p ∈ S, Squarefree p) ∧
  (∀ p ∈ S, ∀ q ∈ S, p ∣ q → p = q) ∧ ((SimpleGraph.fromRel (fun x y : ℕ => 1 < Nat.gcd x y)).induce (S : Set ℕ)).Connected}

theorem main : ∀ k : ℕ, ∃ m : ℕ, ∀ n > m, k < a n := by
  sorry

end OMA.S_oeis_a305080
