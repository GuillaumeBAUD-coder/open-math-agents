import Mathlib.Algebra.IsPrimePow
import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.NumberTheory.Fermat

/-!
# OEIS A328202

Source: https://oeis.org/A328202

The formula is due to Jon Maiga (8 October 2019). Robert Israel
conjectured the criterion for exceeding the index (16 October 2019).
The offset is four, so a Fermat prime in the criterion is greater than three.
In the second case, `n - 1 = 2^k - 1` is a Mersenne prime.
-/

namespace OMA.S_oeis_a328202

/-- Gcd of the coefficients after omitting the first and last two in row `n`. -/
def truncatedGcd (n : ℕ) : ℕ := (Finset.Icc 2 (n - 2)).gcd n.choose

/-- A014963: the prime base of a prime power, or one for any other index. -/
noncomputable def primePowerBase (n : ℕ) : ℕ :=
  open Classical in if IsPrimePow n then n.minFac else 1

theorem main : ∀ n : ℕ, 4 ≤ n →
    (truncatedGcd n = primePowerBase n * primePowerBase (n - 1)) ∧
    (n < truncatedGcd n ↔
      (∃ k : ℕ, n.Prime ∧ n = Nat.fermatNumber k) ∨
        (∃ k : ℕ, (n - 1).Prime ∧ n = 2 ^ k)) := by
  sorry

end OMA.S_oeis_a328202
