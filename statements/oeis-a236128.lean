import Mathlib

/-!
# A236128: Primes p such that gpf(gpf(2^p-1)-1) = p.

Source: https://oeis.org/A236128
Credit: @darealpandaboi

Conjectures: gpf(gpf(2^p-1)-1) = p for finitely many p; and gpf(lpf(2^p-1)-1) = p for
infinitely many p.

Translation notes.
* p ranges over primes (the sequence lists primes). gpf(m) is the greatest prime factor of m and
  lpf(m) the least, Nat.minFac m. For p prime, 2^p - 1 >= 3, so both factors are odd primes q >= 3
  and q - 1 >= 2 has a greatest prime factor.
* gpf is the maximum of Nat.primeFactors m (0 for m = 1, never used here).
* Checked by computer for primes p < 72: the first condition holds exactly for
  2, 3, 5, 7, 11, 13, 29, 53 (the listed data), and the second for 2, 3, 5, 7, 11, 13, 23, 29,
  37, 43, 47, 53 (as in Michael B. Porter's comment).
-/

namespace OMA.S_oeis_a236128

/-- The greatest prime factor of m (0 when m has none). -/
def gpf (m : ℕ) : ℕ := m.primeFactors.sup id

theorem main :
    {p : ℕ | p.Prime ∧ gpf (gpf (2 ^ p - 1) - 1) = p}.Finite ∧
    {p : ℕ | p.Prime ∧ gpf ((2 ^ p - 1).minFac - 1) = p}.Infinite := by
  sorry

end OMA.S_oeis_a236128
