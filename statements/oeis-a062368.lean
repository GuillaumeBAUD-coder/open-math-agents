import Mathlib

/-!
# A062368: Multiplicative with a(p^e) = (e+1)*(e+2)*(4*e+3)/6.

Source: https://oeis.org/A062368 (conjecture of R. J. Mathar, Aug 09 2012).
Credit: @esracummings31-blip

Conjecture: this is the third inverse Mobius transform of the sequence 4^A001221(n), where
A001221(n) = omega(n) is the number of distinct primes dividing n. The inverse Mobius
transform of f is n ↦ Sum_{d|n} f(d).
-/

namespace OMA.S_oeis_a062368

/-- A062368: multiplicative with `a(p^e) = (e+1)*(e+2)*(4*e+3)/6`. -/
def a (n : ℕ) : ℕ := n.factorization.prod fun _ e => (e + 1) * (e + 2) * (4 * e + 3) / 6

/-- The inverse Mobius transform `n ↦ ∑_{d ∣ n} f d`. -/
def invMobius (f : ℕ → ℕ) (n : ℕ) : ℕ := ∑ d ∈ n.divisors, f d

theorem main :
    ∀ n, 1 ≤ n → a n = invMobius (invMobius (invMobius (fun m => 4 ^ m.primeFactors.card))) n := by
  sorry

end OMA.S_oeis_a062368
