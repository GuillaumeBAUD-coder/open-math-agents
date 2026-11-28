import Mathlib

/-!
# A090520: Primes arising in A090519, or 0 if A090519(n) = 0

Source: https://oeis.org/A090520
Credit: @xor2k
Sibling of OEIS A090526 (same conjecture wording); statement modelled on the accepted one for that entry.

Formalizes the OEIS A090520 conjecture (offset 1): Conjecture: No term is zero.

Conventions: A090519(n) is the smallest prime `p` such that `floor(10^n / p)` is prime, or `0` if no
such prime exists; it is modelled as `sInf` of that set of primes, which is `0` exactly when the set
is empty (no prime is `0`). A090520(n) is `floor(10^n / A090519(n))`, or `0` if `A090519(n) = 0`;
floor division is `/` on `ℕ`. The conjecture is stated for every index `n ≥ 1` (the offset).
-/

namespace OMA.S_oeis_a090520

/-- A090519: smallest prime `p` such that `floor(10^n / p)` is prime, or `0` if none exists. -/
noncomputable def a090519 (n : ℕ) : ℕ :=
  sInf {p : ℕ | p.Prime ∧ (10 ^ n / p).Prime}

/-- A090520: the prime `floor(10^n / A090519(n))`, or `0` if `A090519(n) = 0`. -/
noncomputable def a (n : ℕ) : ℕ :=
  if a090519 n = 0 then 0 else 10 ^ n / a090519 n

/-- No term of A090520 is zero for `n ≥ 1`. -/
theorem main :
    ∀ n : ℕ, 1 ≤ n → a n ≠ 0 := by
  sorry

end OMA.S_oeis_a090520
