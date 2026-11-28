import Mathlib

/-!
# A237659: Primes p with pi(p) and pi(p^2) both prime, where pi(.) is given by A000720.

Source: https://oeis.org/A237659
Credit: @darealpandaboi

Conjecture (Zhi-Wei Sun): The sequence has infinitely many terms.

Translation notes.
* pi is the prime-counting function Nat.primeCounting (number of primes <= x).
* This reading reproduces the listed data: 17, 41, 59, 109, 127, 157, 353, 367, ...
  (checked by computer).
-/

namespace OMA.S_oeis_a237659

theorem main :
    {p : ℕ | p.Prime ∧ (Nat.primeCounting p).Prime ∧ (Nat.primeCounting (p ^ 2)).Prime}.Infinite := by
  sorry

end OMA.S_oeis_a237659
