import Mathlib

/-!
# A124197: Number of subsets S of {1,2,3,...,n}, including the empty subset, such that if x and y are in S with x<y and x+y even, then (x+y)/2 is also in S.

Source: https://oeis.org/A124197

Data (offset 0): 1, 2, 4, 7, 12, 18, 26, 36, 48, 61, ...

Conjecture (OEIS comment): the second differences of this sequence give A001227, the number of
odd divisors of n. With offset 0 this reads a(n+2) - 2*a(n+1) + a(n) = A001227(n+1) for n >= 0
(the second differences 1, 1, 2, 1, 2, 2, 2, 1, ... start at A001227(1)).
Noam D. Elkies (2009) sketched a proof in the entry (the core is Putnam 2009 B3).
-/

namespace OMA.S_oeis_a124197

/-- The closure condition: if x < y are in S and x + y is even, then (x + y)/2 is in S. -/
def Good (S : Finset ℕ) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, x < y → Even (x + y) → (x + y) / 2 ∈ S

instance (S : Finset ℕ) : Decidable (Good S) := by
  unfold Good; infer_instance

/-- A124197(n): the number of good subsets of {1, ..., n} (the empty subset included). -/
def a (n : ℕ) : ℕ := ((Finset.Icc 1 n).powerset.filter Good).card

/-- A001227(n): the number of odd divisors of n. -/
def a001227 (n : ℕ) : ℕ := (n.divisors.filter Odd).card

theorem main :
    ∀ n : ℕ, (a (n + 2) : ℤ) - 2 * a (n + 1) + a n = a001227 (n + 1) := by
  sorry

end OMA.S_oeis_a124197
