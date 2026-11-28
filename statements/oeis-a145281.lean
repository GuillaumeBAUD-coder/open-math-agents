import Mathlib

/-!
Sources: OEIS A145281 and A145236. The nearest-prime claim needs two
exceptions. At the underlying primes 3 and 5, the lower threshold is 1,
but the candidate 2 does not pass the square test. The least eligible
odd prime gives the corrected rule.
-/

namespace OMA.S_oeis_a145281

/-- The ceiling of the square root for positive inputs (and zero at zero). -/
def ceilSqrt (n : ℕ) : ℕ := if n = 0 then 0 else Nat.sqrt (n - 1) + 1

/-- The defining test in A145281 and A145236. -/
def passes (p q : ℕ) : Prop :=
  IsSquare (ceilSqrt (p * q) ^ 2 - p * q)

/-- The least positive integer that passes, as given in A145236. -/
def threshold (p : ℕ) : ℕ :=
  if p = 2 then 2 else p + 2 - 2 * Nat.sqrt (2 * p)

theorem main :
    ∀ p : ℕ, p.Prime →
      IsLeast {q : ℕ | 0 < q ∧ passes p q} (threshold p) ∧
      (∃ q : ℕ, IsLeast {r : ℕ | r.Prime ∧ passes p r} q ∧
        IsLeast {r : ℕ | r.Prime ∧ threshold p ≤ r ∧ (p = 2 ∨ 2 < r)} q) ∧
      ((∃ q : ℕ, IsLeast {r : ℕ | r.Prime ∧ passes p r} q ∧
        IsLeast {r : ℕ | r.Prime ∧ threshold p ≤ r} q) ↔ p ≠ 3 ∧ p ≠ 5) := by
  sorry

end OMA.S_oeis_a145281
