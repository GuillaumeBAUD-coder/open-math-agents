import Mathlib

/-!
# A054979: e-perfect numbers: numbers k such that the sum of the e-divisors (exponential divisors) of k equals 2*k.

Source: https://oeis.org/A054979
Credit: @azmiozgen

Conjecture (Jon Perry, Nov 13 2012): every e-perfect number is divisible by 36.

Formalization notes:
* The e-divisors of x = Product p(i)^r(i) are the numbers Product p(i)^s(i) with s(i) dividing
  r(i) for all i (entry comment). Since s(i) divides r(i) ≥ 1 forces s(i) ≥ 1, these are the
  divisors d of x with the same prime factors as x and with the exponent of each prime in d
  dividing its exponent in x. For x = 1 the only e-divisor is 1.
* e-perfect: k ≥ 1 with the sum of its e-divisors equal to 2k.
* Controls: the definition gives the e-perfect numbers below 1700 as 36, 180, 252, 396, 468, 612,
  684, 828, 1044, 1116, 1260, 1332, 1476, 1548, 1692, as in the entry.
-/

namespace OMA.S_oeis_a054979

/-- `d` is an exponential divisor of `n`. -/
def IsEDivisor (n d : ℕ) : Prop :=
  d ∣ n ∧ d.primeFactors = n.primeFactors ∧
    ∀ p ∈ n.primeFactors, d.factorization p ∣ n.factorization p

instance (n d : ℕ) : Decidable (IsEDivisor n d) := by unfold IsEDivisor; infer_instance

/-- The sum of the exponential divisors of `n`. -/
def sigmaE (n : ℕ) : ℕ := ∑ d ∈ n.divisors.filter (IsEDivisor n), d

/-- Perry's conjecture: every e-perfect number is divisible by 36. -/
theorem main : ∀ k : ℕ, 1 ≤ k → sigmaE k = 2 * k → 36 ∣ k := by
  sorry

end OMA.S_oeis_a054979
