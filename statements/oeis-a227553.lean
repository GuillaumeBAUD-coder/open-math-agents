import Mathlib.Data.ZMod.Defs
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Nat.Prime.Defs

namespace OMA.S_oeis_a227553

/-- OEIS A227553: number of solutions `(x, y, z) ∈ (ZMod n)^3` to `x^2 - y^2 - z^2 = 1`. -/
noncomputable def a227553 (n : ℕ) : ℕ :=
  Nat.card {t : ZMod n × ZMod n × ZMod n // t.1 ^ 2 - t.2.1 ^ 2 - t.2.2 ^ 2 = 1}

/-- OEIS A227553 conjecture:
1. `a(2) = 4`;
2. for `s > 1`, `a(2^s) = 2^(2*s - 1)`;
3. for prime `p ≡ 1 (mod 4)` and `s ≥ 1`, `a(p^s) = (p + 1) * p^(2*s - 1)`;
4. for prime `p ≡ 3 (mod 4)` and `s ≥ 1`, `a(p^s) = (p - 1) * p^(2*s - 1)`. -/
theorem main :
    a227553 2 = 4 ∧
    (∀ s : ℕ, 1 < s → a227553 (2 ^ s) = 2 ^ (2 * s - 1)) ∧
    (∀ p s : ℕ, p.Prime → 1 ≤ s → p % 4 = 1 → a227553 (p ^ s) = (p + 1) * p ^ (2 * s - 1)) ∧
    (∀ p s : ℕ, p.Prime → 1 ≤ s → p % 4 = 3 → a227553 (p ^ s) = (p - 1) * p ^ (2 * s - 1)) := by
  sorry

end OMA.S_oeis_a227553
