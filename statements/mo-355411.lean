import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Data.Nat.GCD.BigOperators

namespace OMA.S_mo_355411

def smallerPrimes (p : ℕ) : Finset ℕ :=
  (Finset.range p).filter Nat.Prime

def primeProduct (p : ℕ) : ℕ :=
  ∏ q ∈ smallerPrimes p, q

/-- The number of positive integers at most `M` whose least prime factor is `p`. -/
def count (M p : ℕ) : ℕ :=
  ((Finset.range (M+1)).filter fun x =>
    x ≠ 0 ∧ p ∣ x ∧ ∀ q ∈ smallerPrimes p, ¬ q ∣ x).card

def closedForm (M p : ℕ) : ℤ :=
  ∑ d ∈ (primeProduct p).divisors,
    ArithmeticFunction.moebius d * ((M / (p*d) : ℕ) : ℤ)

/-- Exact count for any prime `p`, so in particular for the `n`th prime. -/
theorem main :
    ∀ M p : ℕ, p.Prime → (count M p : ℤ) = closedForm M p := by
  sorry

end OMA.S_mo_355411
