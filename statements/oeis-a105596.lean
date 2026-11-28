import Mathlib

/-!
# A105596: a(n) = Sum_{k=0..n} A105595(k)*(-1)^k*A105595(n-k) (interpolated zeros suppressed).

Source: https://oeis.org/A105596
Credit: @Harsha0912

Conjecture (in the entry): a(2n) = 1 mod 4 for all n, a(2n+1) = 0 for all n.

Conventions:
* A105594 is the triangle `T(n, k) = (Sum_{j=0..n} |mu(binomial(n, j))| * (binomial(j, k) mod 2)) mod 2`
  (the formula in the entry), for `0 <= k <= n`; `|mu|` is `(ArithmeticFunction.moebius m).natAbs`.
* A105595 is its row sum `b(n) = Sum_{k=0..n} T(n, k)`.
* The conjecture indexes the convolution before the zeros are suppressed, so `c m` below is
  `Sum_{k=0..m} b(k) * (-1)^k * b(m-k)` for every `m`, computed in the integers; the listed terms
  of A105596 are `c (2n)`.
-/

namespace OMA.S_oeis_a105596

/-- A105594: `T(n, k) = (Sum_{j=0..n} |mu(C(n, j))| * (C(j, k) mod 2)) mod 2`. -/
def T (n k : ℕ) : ℕ :=
  (∑ j ∈ Finset.range (n + 1),
    (ArithmeticFunction.moebius (n.choose j)).natAbs * (j.choose k % 2)) % 2

/-- A105595: the row sums of A105594. -/
def b (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), T n k

/-- The convolution `Sum_{k=0..m} b(k) * (-1)^k * b(m-k)`, with the zeros not suppressed. -/
def c (m : ℕ) : ℤ := ∑ k ∈ Finset.range (m + 1), (b k : ℤ) * (-1) ^ k * (b (m - k) : ℤ)

/-- `c (2n) = 1 (mod 4)` and `c (2n+1) = 0` for every `n`. -/
theorem main : ∀ n : ℕ, c (2 * n) % 4 = 1 ∧ c (2 * n + 1) = 0 := by
  sorry

end OMA.S_oeis_a105596

