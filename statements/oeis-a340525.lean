import Mathlib

/-!
# A340525: Triangle read by rows: T(n,k) = A006218(n-k+1)*A002865(k-1), 1 <= k <= n.

Source: https://oeis.org/A340525
Credit: @esracummings31-blip

Conjecture (Omar E. Pol): the sum of row n equals A006128(n), the total number of parts in all
partitions of n.

Conventions.
* A002865(j) is the number of partitions of j that contain no part 1 (so A002865(0) = 1).
* A006218(m) = Sum_{i=1..m} d(i), where d(i) is the number of divisors of i.
* A006128(n) is the total number of parts in all partitions of n.
-/

namespace OMA.S_oeis_a340525

/-- A002865: the number of partitions of j with no part equal to 1. -/
def A002865 (j : ℕ) : ℕ :=
  ((Finset.univ : Finset (Nat.Partition j)).filter (fun p => 1 ∉ p.parts)).card

/-- A006218: Sum_{i=1..m} d(i). -/
def A006218 (m : ℕ) : ℕ := ∑ i ∈ Finset.Icc 1 m, (Nat.divisors i).card

/-- A006128: the total number of parts in all partitions of n. -/
def A006128 (n : ℕ) : ℕ := ∑ p : Nat.Partition n, Multiset.card p.parts

/-- T(n,k) = A006218(n-k+1) * A002865(k-1). -/
def T (n k : ℕ) : ℕ := A006218 (n - k + 1) * A002865 (k - 1)

theorem main : ∀ n : ℕ, 1 ≤ n → ∑ k ∈ Finset.Icc 1 n, T n k = A006128 n := by
  sorry

end OMA.S_oeis_a340525
