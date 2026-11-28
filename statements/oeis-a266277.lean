import Mathlib

/-!
# A266277: every integer is x^3 + y^5 - z^2 in infinitely many ways (Sun's conjecture, case {2,3,5})

Source: https://oeis.org/A266277
Credit: @LordMike

Conjecture: If {a,b,c} is among the multisets {2,2,p} (p is an odd prime or a product of primes
congruent to 1 modulo 4) and {2,3,k} (k = 3,4,5), then for any integer m there are (infinitely many)
triples (x,y,z) of positive integers such that m = x^a + y^b - z^c.

This implies that a(n) > 0 for all n.

Reading used here: the instance {2,3,k} with k = 5, exponents (a,b,c) = (3,5,2), which is the case behind
A266277 (n + x^2 = y^3 + z^5, offset 0, a(0)=3, a(1)=1, a(2)=83); the claim is for every integer m, and
infinitely many positive triples. Taking m = n >= 0 gives a(n) > 0.
-/

namespace OMA.S_oeis_a266277

theorem main : ∀ m : ℤ, {t : ℕ × ℕ × ℕ | 0 < t.1 ∧ 0 < t.2.1 ∧ 0 < t.2.2 ∧
    m = (t.1 : ℤ) ^ 3 + (t.2.1 : ℤ) ^ 5 - (t.2.2 : ℤ) ^ 2}.Infinite := by
  sorry

end OMA.S_oeis_a266277
