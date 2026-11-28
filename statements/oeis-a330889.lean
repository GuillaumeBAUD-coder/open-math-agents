import Mathlib

/-!
# A330889: a(n) is the total number of parts in all partitions of n into consecutive parts that differ by 3.

Source: https://oeis.org/A330889
Credit: @xor2k

Formalizes the conjecture in the formula section of the OEIS entry (the row does not name its
author):
  Conjecture: G.f.: Sum_{n>=1} n*x^(n*(3*n-1)/2)/(1-x^n).

Conventions:
* A partition of n into k consecutive parts that differ by 3 is a list of parts
  m, m+3, ..., m+3(k-1) with k >= 1, m >= 1 (all parts positive) and sum n; one part alone
  (k = 1, m = n) counts. Such a partition has k <= n and m <= n, so k and m range over `1..n`.
  a(n) is the sum, over all such partitions, of the number k of parts. Offset 1; the
  definition also gives a(0) = 0, the constant term of the g.f. (which has none).
* The g.f. is an infinite sum of formal power series over ℚ, with 1/(1-x^k) the inverse of
  1 - X^k in ℚ⟦X⟧ and k*(3*k-1)/2 an exact division. The summand of index k has order
  k*(3*k-1)/2 >= k, so the coefficient of x^n of the infinite sum is the coefficient of x^n of
  every partial sum over k = 1..N with N >= n. The statement is: for every n and every N >= n,
  a(n) is the coefficient of x^n of the partial sum over k = 1..N.

Numerical check: a Python copy of the definition gives 1, 1, 1, 1, 3, 1, 3, 1, 3, 1, 3, 4, 3, 1,
6, 1, 3, 4, 3, 1, 6, 5, 3, 4, 3, 5, 6, 1, 3, 8 for n = 1..30 (identical to the first 30 terms of the
DATA field of the entry, which was compared before filing).
-/

namespace OMA.S_oeis_a330889

/-- The `k` parts `m, m+3, ..., m+3(k-1)`. -/
def parts (m k : ℕ) : List ℕ := (List.range k).map (fun i => m + 3 * i)

/-- A330889: the total number of parts in all partitions of `n` into consecutive parts that
differ by 3. -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.Icc 1 n, ∑ m ∈ Finset.Icc 1 n, (if (parts m k).sum = n then k else 0)

/-- The conjectured g.f. Sum_{k>=1} k*x^(k*(3*k-1)/2)/(1-x^k), coefficient by coefficient. -/
theorem main : ∀ n N : ℕ, n ≤ N →
    (a n : ℚ) = PowerSeries.coeff n (∑ k ∈ Finset.Icc 1 N,
      (k : PowerSeries ℚ) * PowerSeries.X ^ (k * (3 * k - 1) / 2)
        * (1 - PowerSeries.X ^ k)⁻¹) := by
  sorry

end OMA.S_oeis_a330889
