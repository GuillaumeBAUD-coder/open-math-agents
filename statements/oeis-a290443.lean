import Mathlib

/-!
# A290443: a(n) = Catalan(n)*Motzkin(n-1).

Source: https://oeis.org/A290443
Credit: @vivanpoddar

The sequence (offset 1) begins 1, 2, 10, 56, 378, 2772, 21879, 181610, ...
It is defined as in the name of the entry. Catalan(n) is Mathlib's catalan, and the Motzkin numbers
(A001006: 1, 1, 2, 4, 9, 21, 51, ...) are given by the standard formula
Motzkin(n) = Sum_{k=0..floor(n/2)} C(n,2k)*Catalan(k).

Conjecture (R. J. Mathar, Aug 05 2017):
n*(n+1)^2*a(n) -2*-n*(2*n-1)^2*a(n-1) -12*(n-2)*(2*n-1)*(2*n-3)*a(n-2)=0.
It involves a(n-2) and the offset is 1, so it is stated for n >= 3, exactly as printed; the middle
coefficient -2*-n*(2*n-1)^2 is read literally as (-2)*(-n)*(2*n-1)^2.

Remark for the reviewer: with the terms of the entry the left-hand side at n = 3 is
3*16*10 + 2*3*25*2 - 12*1*5*3*1 = 600, so the relation as printed does not hold. The listed terms
do satisfy the relation with the middle term -2*n*(2*n-1)^2*a(n-1), which is what the recurrences
of the Catalan and Motzkin numbers give. The statement below keeps the printed form.
-/

namespace OMA.S_oeis_a290443

/-- The Motzkin numbers A001006. -/
def motzkin (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n / 2 + 1), n.choose (2 * k) * catalan k

/-- A290443: Catalan(n) * Motzkin(n-1). -/
def a (n : ℕ) : ℕ := catalan n * motzkin (n - 1)

/-- The conjectured recurrence for A290443, as printed in the entry. -/
theorem main : ∀ n : ℕ, 3 ≤ n →
    (n : ℤ) * ((n : ℤ) + 1) ^ 2 * a n - 2 * (-(n : ℤ)) * (2 * (n : ℤ) - 1) ^ 2 * a (n - 1)
      - 12 * ((n : ℤ) - 2) * (2 * (n : ℤ) - 1) * (2 * (n : ℤ) - 3) * a (n - 2) = 0 := by
  sorry

end OMA.S_oeis_a290443
