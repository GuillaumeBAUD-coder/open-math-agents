import Mathlib

/-!
# A357508: a(n) = binomial(4*n,2*n) - 2*binomial(4*n,n)

Source: https://oeis.org/A357508

Offset 0. The entry defines, for an integer m and a positive integer k,
u(n) = binomial((m+2)*n,(k+1)*n) - binomial(m,k)*binomial((m+2)*n,n)
(A357508 is the case m = 2, k = 1). The congruence u(n) == u(1) (mod p^5) for primes
p >= 7 is noted in the entry as proved (Helou and Terjanian), so it is not part of the target.
Open conjecture (Peter Bala, Oct 13 2022): for r >= 2,
u(p^r) == u(p^(r-1)) (mod p^(3*r+3)) for all primes p >= 5.

Formalized: binomial coefficients with integer top are `Ring.choose` over ℤ (the generalized
binomial, which agrees with `Nat.choose` for nonnegative top), so negative m is allowed as in
the entry. The congruence is `Int.ModEq` in ℤ, quantified over all integers m, all k >= 1,
all primes p >= 5 and all r >= 2.
-/

namespace OMA.S_oeis_a357508

/-- The sequence A357508: binomial(4n,2n) - 2 binomial(4n,n). -/
def a (n : ℕ) : ℤ := (Nat.choose (4 * n) (2 * n) : ℤ) - 2 * (Nat.choose (4 * n) n : ℤ)

/-- The generalization u(n) = binomial((m+2)n,(k+1)n) - binomial(m,k) binomial((m+2)n,n). -/
def u (m : ℤ) (k : ℕ) (n : ℕ) : ℤ :=
  Ring.choose ((m + 2) * (n : ℤ)) ((k + 1) * n) - Ring.choose m k * Ring.choose ((m + 2) * (n : ℤ)) n

theorem main :
    ∀ (m : ℤ) (k : ℕ), 1 ≤ k → ∀ (p : ℕ), p.Prime → 5 ≤ p → ∀ (r : ℕ), 2 ≤ r →
      u m k (p ^ r) ≡ u m k (p ^ (r - 1)) [ZMOD ((p : ℤ) ^ (3 * r + 3))] := by
  sorry

end OMA.S_oeis_a357508
