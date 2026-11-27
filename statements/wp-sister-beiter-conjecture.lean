import Mathlib

/-!
# Sister Beiter conjecture

Source: https://en.wikipedia.org/wiki/Sister_Beiter_conjecture
Credit: @ihateSAS

For `n > 0` let `A(n)` be the maximal coefficient in absolute value of the
cyclotomic polynomial `Φ_n`. For primes `3 ≤ p ≤ q ≤ r` the polynomial
`Φ_{pqr}` is called ternary, and `M(p) = max_{p ≤ q ≤ r prime} A(pqr)`.

Sister Beiter conjectured in 1968 that `M(p) ≤ (p + 1) / 2`; this was
disproved, and the corrected Sister Beiter conjecture states `M(p) ≤ (2 / 3) p`.
The statement below is the corrected conjecture, phrased directly over the
prime triples `p ≤ q ≤ r` that occur in the definition of `M(p)`.
-/

namespace OMA.S_wp_sister_beiter_conjecture

/-- The maximal coefficient in absolute value of the `n`-th cyclotomic
polynomial, denoted `A(n)` in the source. -/
noncomputable def maxCoeffAbs (n : ℕ) : ℕ :=
  (Finset.range (n + 1)).sup fun k => ((Polynomial.cyclotomic n ℤ).coeff k).natAbs

theorem main :
    ∀ p : ℕ, p.Prime → 3 ≤ p →
      ∀ q r : ℕ, q.Prime → r.Prime → p ≤ q → q ≤ r →
        maxCoeffAbs (p * q * r) ≤ 2 * p / 3 := by
  sorry

end OMA.S_wp_sister_beiter_conjecture
