import Mathlib.Combinatorics.Enumerative.Bell
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Order.Bounds.Defs

/-!
# Minimum period of Bell numbers modulo a prime (OEIS A054767)

Source: https://oeis.org/A054767 (OEIS Foundation, CC BY-SA 4.0).
Formalization: @sturdy4days.

The conjecture is that for each prime p, the least positive period of the
Bell sequence modulo p is (p^p - 1)/(p - 1). The Bell sequence starts with
B(0) = 1. The cited work of Wagstaff verifies cases of this minimum-period
conjecture.
Reference: https://doi.org/10.1090/S0025-5718-96-00683-7.
-/

namespace OMA.S_oeis_a054767

def positiveBellPeriods (modulus : ℕ) : Set ℕ :=
  {period | 0 < period ∧ ∀ n : ℕ, (n + period).bell % modulus = n.bell % modulus}

theorem main : ∀ p : ℕ, p.Prime → IsLeast (positiveBellPeriods p) ((p ^ p - 1) / (p - 1)) := by
  sorry

end OMA.S_oeis_a054767
