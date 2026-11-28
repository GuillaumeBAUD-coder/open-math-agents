import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Set.Finite.Basic

/-!
# Prime progressions starting with an odd prime

Source: https://oeis.org/A210505
Credit: @luciusacarr
-/

namespace OMA.S_oeis_a210505

theorem main : ∀ p : ℕ, p.Prime → p % 2 = 1 →
    Set.Infinite {k : ℕ | ∀ i : ℕ, 0 < i → i < p → (2 * i * k + p).Prime} := by
  sorry

end OMA.S_oeis_a210505
