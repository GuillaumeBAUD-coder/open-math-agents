import Mathlib

/-!
# A045406: A diagonal of A008296

Source: https://oeis.org/A045406
Credit: @ivillar

Offset 2, data 1, 3, -1, 0, 4, -28, 188, -1368, ... The entry identifies a(n) = A008296(n,2) and gives
the formula of Benoit Cloitre a(n) = Sum_{i=1..n-1} i^2*Stirling1(n-1, i), which we take as the
definition. Stirling1 is the signed Stirling number of the first kind, s(n,m) = (-1)^(n+m) * c(n,m)
with c(n,m) = Nat.stirlingFirst n m the unsigned one; the formula reproduces the listed terms.

Conjecture (R. J. Mathar, Sep 15 2021): D-finite with recurrence
a(n) +(2*n-7)*a(n-1) +(n-4)^2*a(n-2)=0.
At n = 4 the left side is a(4) + a(3) = 2, so the recurrence is read from n = 5 on (n ≥ 5); it is
stated over the integers.
-/

namespace OMA.S_oeis_a045406

/-- The signed Stirling number of the first kind s(n,m). -/
def s (n m : ℕ) : ℤ := (-1) ^ (n + m) * (Nat.stirlingFirst n m : ℤ)

/-- Cloitre's formula a(n) = Sum_{i=1..n-1} i^2*Stirling1(n-1, i) (offset 2). -/
def a (n : ℕ) : ℤ := ∑ i ∈ Finset.Icc 1 (n - 1), (i : ℤ) ^ 2 * s (n - 1) i

/-- Mathar's conjectured recurrence, from n = 5 on. -/
theorem main : ∀ n : ℕ, 5 ≤ n →
    a n + (2 * (n : ℤ) - 7) * a (n - 1) + ((n : ℤ) - 4) ^ 2 * a (n - 2) = 0 := by
  sorry

end OMA.S_oeis_a045406
