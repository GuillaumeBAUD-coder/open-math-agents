import Mathlib.Data.Nat.Squarefree

/-!
# A sufficient condition for a product of three primes to be Lucas–Carmichael

Davide Rotondo, December 23, 2020, in OEIS A006972.
Source: https://oeis.org/A006972 (OEIS Foundation, CC BY-SA 4.0).
-/

namespace OMA.S_oeis_a006972

/-- A squarefree composite whose prime divisors satisfy the Lucas–Carmichael condition. -/
def IsLucasCarmichael (k : ℕ) : Prop :=
  1 < k ∧ ¬ k.Prime ∧ Squarefree k ∧
    ∀ s : ℕ, s.Prime → s ∣ k → s + 1 ∣ k + 1

/-- The equations for the successors express the source's parametrization
without truncated subtraction on natural numbers. -/
theorem main : ∀ k p q r a b c d : ℕ,
    k = p * q * r →
    p.Prime → q.Prime → r.Prime → Odd p → Odd q → Odd r →
    p ≠ q → p ≠ r → q ≠ r →
    d = Nat.gcd (Nat.gcd (p + 1) (q + 1)) (r + 1) →
    p + 1 = a * d → q + 1 = b * d → r + 1 = c * d →
    a * b * c * d ∣ k + 1 → IsLucasCarmichael k := by
  sorry

end OMA.S_oeis_a006972
