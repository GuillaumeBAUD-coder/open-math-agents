import Mathlib

/-!
# A299807: Rectangular array read by antidiagonals: T(n,k) is the number of distinct sums of k complex n-th roots of 1, n >= 1, k >= 0.

Source: https://oeis.org/A299807
Credit: @xor2k

Chai Wah Wu (May 28 2018), in A299807:
  The following are all conjectures. [...] For p prime, the n=p row corresponds to
  binomial(k+p-1,p-1) for k = 0,1,2,3,..., which is the maximum possible (i.e., the number of
  combinations with repetitions of k choices from p categories) with g.f.: 1/(1-x)^p.

Only this prime-row conjecture is formalized here. The other conjecture of the same comment (the
2^(m+1)-th rows are figurate numbers of the 2^m-dimensional regular convex polytopes) is not
part of this statement.

Conventions:
* A sum of k complex n-th roots of 1 is the sum of a multiset of size k (repetitions allowed,
  order irrelevant) of complex numbers x with x^n = 1. `T n k` is the number of distinct complex
  numbers obtained in this way (`Set.ncard`; the set is finite for n ≥ 1). For k = 0 the only
  sum is the empty sum 0, so T(n,0) = 1.
* The claim is stated for every prime p and every k ≥ 0: T(p,k) = binomial(k+p-1, p-1).
* The g.f. of row p is stated as an identity of formal power series over ℚ:
  (∑_{k ≥ 0} T(p,k) X^k) * (1 - X)^p = 1.
* The remark that binomial(k+p-1,p-1) is the maximum possible is the trivial bound by the number
  of multisets of size k on p elements; it is an explanation and is not stated separately.

Numerical check: a Python copy of the definition (floating point with rounding) gives the rows
n = 1: 1, 1, 1, 1, 1, 1, 1;  n = 2: 1, 2, 3, 4, 5, 6, 7;  n = 3: 1, 3, 6, 10, 15, 21, 28;
n = 4: 1, 4, 9, 16, 25, 36;  n = 5: 1, 5, 15, 35, 70, 126, 210;  n = 6: 1, 6, 19, 37, 61;
n = 7: 1, 7, 28, 84, 210, 462, 924 (k = 0, 1, 2, ...), in agreement with binomial(k+p-1,p-1)
for p = 2, 3, 5, 7. Read by antidiagonals this gives
1, 1, 1, 1, 2, 1, 1, 3, 3, 1, 1, 4, 6, 4, 1, 1, 5, 10, 9, 5, 1, ... when each antidiagonal is
read from T(1,d) to T(d+1,0) (the other direction swaps 10 and 9). The DATA field of the entry
was not available offline for comparison.
-/

namespace OMA.S_oeis_a299807

/-- A299807: T(n,k) is the number of distinct sums of k complex n-th roots of 1. -/
noncomputable def T (n k : ℕ) : ℕ :=
  Set.ncard {z : ℂ | ∃ s : Multiset ℂ, Multiset.card s = k ∧ (∀ x ∈ s, x ^ n = 1) ∧ s.sum = z}

/-- Wu's conjecture: for p prime, row p is binomial(k+p-1,p-1), with g.f. 1/(1-x)^p. -/
theorem main : ∀ p : ℕ, p.Prime →
    (∀ k : ℕ, T p k = Nat.choose (k + p - 1) (p - 1)) ∧
    PowerSeries.mk (fun k => (T p k : ℚ)) * (1 - PowerSeries.X) ^ p = 1 := by
  sorry

end OMA.S_oeis_a299807
