import Mathlib

/-!
# A195673: Triangle T(n,k) read by rows: T(0,0)=-2, T(1,0)=3, T(1,1)=0 and T(n,k) = T(n-1,k)-T(n-2,k-2) otherwise.

Source: https://oeis.org/A195673
Credit: @xor2k

Conjecture in the entry (as quoted in the row; no author is given there):
  The polynomials p(n,x) = sum_{k=0..n} T(n,k)*x^(n-k) based on this simple recurrence for other
  initial constant values of T(0,0)=p and T(1,0)=q are related to the S-polynomials of A053119:
  p(n,x,p+1,q+1)-p(n,x,p,q) = S(n,x).

Conventions:
* `T p q n k` is the triangle with the initial values T(0,0) = p, T(1,0) = q, T(1,1) = 0 and
  T(n,k) = T(n-1,k) - T(n-2,k-2) for n ≥ 2, where entries outside 0 ≤ k ≤ n are read as 0 (the
  term T(n-2,k-2) is dropped for k < 2, and T(n-1,n) = 0). The definition is given for all natural
  n, k; it is 0 for k > n, and only 0 ≤ k ≤ n enters the polynomial. Rows and columns have offset 0.
* `poly p q n` is p(n,x) = sum_{k=0..n} T(n,k)*x^(n-k) as an element of ℤ[X].
* S(n,x) are the Chebyshev S-polynomials S(n,x) = U(n,x/2), S(0) = 1, S(1) = x,
  S(n) = x*S(n-1) - S(n-2) (A053119 is their coefficient triangle); this is Mathlib's
  `Polynomial.Chebyshev.S ℤ n` (indexed by integers there, used here at natural n).
* The claim is stated for all integers p, q and all n ≥ 0 as an identity in ℤ[X].

Numerical check: a Python copy of the definition with p = -2, q = 3 gives the rows
  -2;  3, 0;  3, 0, 2;  3, 0, -1, 0;  3, 0, -4, 0, -2;  3, 0, -7, 0, -1, 0;  3, 0, -10, 0, 3, 0, 2;
  3, 0, -13, 0, 10, 0, 3, 0;  3, 0, -16, 0, 20, 0, 0, 0, -2
(to be compared with the DATA of the entry, which was not available offline), and the identity
holds for all -4 ≤ p, q ≤ 4 and n ≤ 15.
-/

namespace OMA.S_oeis_a195673

/-- The triangle with initial values T(0,0) = p, T(1,0) = q, T(1,1) = 0 and
T(n,k) = T(n-1,k) - T(n-2,k-2), entries outside 0 ≤ k ≤ n being 0. -/
def T (p q : ℤ) : ℕ → ℕ → ℤ
  | 0, k => if k = 0 then p else 0
  | 1, k => if k = 0 then q else 0
  | n + 2, k => T p q (n + 1) k - (if 2 ≤ k then T p q n (k - 2) else 0)

/-- p(n,x) = sum_{k=0..n} T(n,k)*x^(n-k). -/
noncomputable def poly (p q : ℤ) (n : ℕ) : Polynomial ℤ :=
  ∑ k ∈ Finset.range (n + 1), Polynomial.C (T p q n k) * Polynomial.X ^ (n - k)

/-- p(n,x,p+1,q+1) - p(n,x,p,q) = S(n,x). -/
theorem main : ∀ (p q : ℤ) (n : ℕ),
    poly (p + 1) (q + 1) n - poly p q n = Polynomial.Chebyshev.S ℤ (n : ℤ) := by
  sorry

end OMA.S_oeis_a195673
