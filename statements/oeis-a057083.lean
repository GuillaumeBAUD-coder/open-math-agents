import Mathlib

/-!
# A057083: Scaled Chebyshev U-polynomials evaluated at sqrt(3)/2; expansion of 1/(1 - 3*x + 3*x^2).

Source: https://oeis.org/A057083
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A057083 (Stanislav Sykora, Jun 10 2012): Let M be any
endomorphism on any vector space, such that M^3 = 1 (identity). Then
(1-M)^n = A057681(n) - A057682(n)*M + z(n)*M^2, where z(0) = z(1) = 0 and, apparently,
z(n+2) = a(n).

Conventions:
* `a` is A057083 (offset 0), the coefficients of 1/(1 - 3*x + 3*x^2): a(0) = 1, a(1) = 3 and
  a(n) = 3*a(n-1) - 3*a(n-2), i.e. 1, 3, 6, 9, 9, 0, -27, -81, ... (integers).
* `A057681 n = Sum_{j=0..floor(n/3)} (-1)^j*binomial(n,3*j)` and
  `A057682 n = Sum_{j=0..floor(n/3)} (-1)^j*binomial(n,3*j+1)`, the definitions (names) of
  those two entries, both with offset 0.
* `z` is the sequence named in the conjecture: z(0) = z(1) = 0 and z(n+2) = a(n).
* A vector space is a module `V` over a field `K`; an endomorphism is a `K`-linear map
  `M : Module.End K V`, where the product is composition and `1` is the identity. The integer
  coefficients act by the integer scalar multiplication `•` on `Module.End K V`, so that
  `A057681 n • 1` is the scalar endomorphism A057681(n) times the identity. The identity is
  asserted for every `n : ℕ`.
-/

namespace OMA.S_oeis_a057083

/-- A057083: a(0) = 1, a(1) = 3, a(n) = 3*a(n-1) - 3*a(n-2); expansion of 1/(1 - 3x + 3x^2). -/
def a : ℕ → ℤ
  | 0 => 1
  | 1 => 3
  | n + 2 => 3 * a (n + 1) - 3 * a n

/-- A057681: a(n) = Sum_{j=0..floor(n/3)} (-1)^j*binomial(n,3*j). -/
def A057681 (n : ℕ) : ℤ := ∑ j ∈ Finset.range (n / 3 + 1), (-1) ^ j * (n.choose (3 * j) : ℤ)

/-- A057682: a(n) = Sum_{j=0..floor(n/3)} (-1)^j*binomial(n,3*j+1). -/
def A057682 (n : ℕ) : ℤ := ∑ j ∈ Finset.range (n / 3 + 1), (-1) ^ j * (n.choose (3 * j + 1) : ℤ)

/-- The sequence `z` of the conjecture: z(0) = z(1) = 0 and z(n+2) = A057083(n). -/
def z : ℕ → ℤ
  | 0 => 0
  | 1 => 0
  | n + 2 => a n

/-- Sykora's conjecture: if `M ^ 3 = 1` then
`(1 - M)^n = A057681(n) - A057682(n)*M + z(n)*M^2` for every `n`. -/
theorem main : ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (M : Module.End K V),
    M ^ 3 = 1 → ∀ n : ℕ,
      (1 - M) ^ n = A057681 n • (1 : Module.End K V) - A057682 n • M + z n • M ^ 2 := by
  sorry

end OMA.S_oeis_a057083
